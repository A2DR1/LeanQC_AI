import subprocess
import threading
import queue
import json
import os
import time

class LeanServer:
    def __init__(self, project_path="."):
        self.project_path = os.path.abspath(project_path)
        
        # Ensure we are in a valid Lean project
        if not os.path.exists(os.path.join(self.project_path, "lakefile.toml")):
            raise FileNotFoundError(f"No lakefile.toml found in {self.project_path}")

        print(f"🚀 Starting Lean Server in: {self.project_path}")

        self.proc = subprocess.Popen(
            ["lake", "env", "lean", "--server"],
            cwd=self.project_path,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=False, 
            bufsize=0
        )

        self.response_queue = queue.Queue()
        self.running = True
        self.request_id = 0

        threading.Thread(target=self._read_stdout, daemon=True).start()
        threading.Thread(target=self._read_stderr, daemon=True).start()

        self._initialize_protocol()

    def _initialize_protocol(self):
        self._send({
            "id": 0,
            "jsonrpc": "2.0",
            "method": "initialize",
            "params": {
                "processId": None,
                "rootUri": f"file://{self.project_path}",
                "capabilities": {}
            }
        })
        
        # Wait for initialize response
        while True:
            msg = self.response_queue.get()
            if msg.get("id") == 0:
                break
        
        self._send({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })

    def _read_stdout(self):
        while self.running:
            try:
                header = b""
                while True:
                    ch = self.proc.stdout.read(1)
                    if not ch:
                        self.running = False
                        return
                    header += ch
                    if header.endswith(b"\r\n\r\n"):
                        break
                
                header_str = header.decode("ascii")
                content_length = 0
                for line in header_str.split("\r\n"):
                    if line.lower().startswith("content-length:"):
                        content_length = int(line.split(":")[1].strip())

                if content_length > 0:
                    body = self.proc.stdout.read(content_length)
                    msg = json.loads(body.decode("utf-8"))
                    self.response_queue.put(msg)
            except Exception as e:
                if self.running:
                    print("⚠️ Reader error:", e)
                break

    def _read_stderr(self):
        while self.running:
            line = self.proc.stderr.readline()
            if not line: return
            # Uncomment to debug raw server output
            # print(f"🔴 {line.decode(errors='replace').strip()}")

    def _send(self, req: dict):
        content_bytes = json.dumps(req).encode("utf-8")
        header = f"Content-Length: {len(content_bytes)}\r\n\r\n".encode("utf-8")
        try:
            self.proc.stdin.write(header)
            self.proc.stdin.write(content_bytes)
            self.proc.stdin.flush()
        except BrokenPipeError:
            self.running = False

    # ----------------------------------------------------------
    # CHECK CODE (FIXED)
    # ----------------------------------------------------------
    def check(self, code: str, filename="TmpCheck.lean", timeout=15):
        # We must use an absolute path for the URI
        file_path = os.path.join(self.project_path, filename)
        uri = f"file://{file_path}"
        
        # Clear queue of old messages to avoid processing stale diagnostics
        with self.response_queue.mutex:
            self.response_queue.queue.clear()

        # 1. Open the document
        self._send({
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": {
                    "uri": uri,
                    "languageId": "lean",
                    "version": 1,
                    "text": code
                }
            }
        })

        current_errors = []
        start_time = time.time()
        
        # State tracking for Lean's processing status
        # We need to wait for Lean to SAY it started, and then SAY it finished.
        has_started_processing = False

        # 2. Wait for diagnostics and "processing complete" signal
        while time.time() - start_time < timeout:
            try:
                # 0.5s timeout allows the loop to check the overall timeout condition
                msg = self.response_queue.get(timeout=0.1)
            except queue.Empty:
                continue

            method = msg.get("method")
            params = msg.get("params", {})

            # A. Collect Diagnostics
            if method == "textDocument/publishDiagnostics":
                if params.get("uri") == uri:
                    current_errors = [] # Reset errors on new publish (LSP standard)
                    for d in params.get("diagnostics", []):
                        # severity 1 = Error
                        if d.get("severity") == 1:
                            range_start = d['range']['start']
                            current_errors.append(
                                f"Line {range_start['line'] + 1}: {d['message']}"
                            )

            # B. Monitor Processing Status
            if method == "$/lean/fileProgress":
                records = params.get("processing", [])
                is_our_file_processing = any(r.get("uri") == uri for r in records)
                
                if is_our_file_processing:
                    has_started_processing = True
                
                # If we saw it start, and now it says it's NOT processing our file, we are done.
                if has_started_processing and not is_our_file_processing:
                    # Small buffer to ensure queue is drained of any immediately following diagnostics
                    time.sleep(0.1)
                    break
        
        # Drain any remaining diagnostics in the queue (rare but possible race condition)
        while not self.response_queue.empty():
            try:
                msg = self.response_queue.get_nowait()
                if msg.get("method") == "textDocument/publishDiagnostics":
                    if msg["params"]["uri"] == uri:
                        current_errors = []
                        for d in msg["params"]["diagnostics"]:
                            if d.get("severity") == 1:
                                current_errors.append(f"Line {d['range']['start']['line']+1}: {d['message']}")
            except queue.Empty:
                break

        # 3. Close Document
        self._send({
            "jsonrpc": "2.0",
            "method": "textDocument/didClose",
            "params": {"textDocument": {"uri": uri}}
        })

        if current_errors:
            return False, "\n".join(current_errors)
        return True, "OK"

    def close(self):
        self.running = False
        try:
            self.proc.terminate()
        except:
            pass

if __name__ == "__main__":
    # UPDATE THIS PATH TO YOUR ACTUAL PROJECT PATH
    PROJECT_PATH = os.getcwd() 
    
    # If checking external folder, hardcode it:
    # PROJECT_PATH = "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/AutoEvaluation"

    try:
        server = LeanServer(PROJECT_PATH)

        print("\n--- Checking Bad Code ---")
        ok, log = server.check("""
            import Mathlib
            theorem bad : 1 = 2 := by rfl
        """)
        print(f"Valid: {ok}")
        print(f"Log: {log}")

        print("\n--- Checking Good Code ---")
        ok, log = server.check("""
            import Mathlib
            theorem good : 1 = 1 := by rfl
        """)
        print(f"Valid: {ok}")
        print(f"Log: {log}")

        print("\n--- Checking Wrong Code (Syntax) ---")
        ok, log = server.check("""
            import Mathlib
            theor good : 1 = 1 := by rfl
        """)
        print(f"Valid: {ok}")
        print(f"Log: {log}")

        server.close()
    except Exception as e:
        print(f"Error: {e}")