import subprocess
import threading
import queue
import json
import os

class LeanServer:
    def __init__(self, project_path="."):
        # Start the Lean 4 Language Server via Lake
        self.proc = subprocess.Popen(
            ["lake", "env", "lean", "--server"],
            cwd=project_path,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,  # Capture stderr
            text=False,              # Binary mode is safer for LSP byte-counting
            bufsize=0                # Unbuffered I/O
        )
        
        self.response_queue = queue.Queue()
        self.running = True
        
        # Thread to read stdout (LSP messages)
        self.stdout_thread = threading.Thread(target=self._reader_loop, daemon=True)
        self.stdout_thread.start()

        # Thread to consume stderr (to prevent blocking)
        self.stderr_thread = threading.Thread(target=self._stderr_consumer, daemon=True)
        self.stderr_thread.start()

    def _stderr_consumer(self):
        """Consumes stderr to prevent buffer filling and blocking."""
        while self.running and self.proc.poll() is None:
            try:
                line = self.proc.stderr.readline()
                if not line:
                    break
                # Optional: print stderr for debugging (comment out if too noisy)
                # print(f"[Lean Stderr] {line.decode('utf-8', errors='replace').strip()}")
            except Exception:
                break

    def _reader_loop(self):
        """Reads LSP messages (Header + Content) correctly."""
        while self.running:
            try:
                if self.proc.poll() is not None:
                    break # Process died

                # 1. Read headers until \r\n\r\n
                header_bytes = b""
                while True:
                    char = self.proc.stdout.read(1)
                    if not char: # EOF
                        self.running = False
                        return
                    header_bytes += char
                    if header_bytes.endswith(b"\r\n\r\n"):
                        break
                
                # 2. Parse Content-Length
                header_str = header_bytes.decode("utf-8")
                content_length = 0
                for line in header_str.split("\r\n"):
                    if line.startswith("Content-Length:"):
                        content_length = int(line.split(":")[1].strip())
                
                # 3. Read the exact JSON payload
                if content_length > 0:
                    content_bytes = self.proc.stdout.read(content_length)
                    message = json.loads(content_bytes.decode("utf-8"))
                    self.response_queue.put(message)

            except Exception as e:
                if self.running:
                    print(f"Reader Error: {e}")
                break

    def send_request(self, method, params):
        """Sends a JSON-RPC request with the correct LSP headers."""
        if self.proc.poll() is not None:
             raise BrokenPipeError("Lean server process has terminated.")

        request = {
            "jsonrpc": "2.0",
            "method": method,
            "params": params
        }
        json_str = json.dumps(request)
        # LSP Framing: Content-Length header + \r\n\r\n + JSON
        message = f"Content-Length: {len(json_str)}\r\n\r\n{json_str}"
        try:
            self.proc.stdin.write(message.encode("utf-8"))
            self.proc.stdin.flush()
        except BrokenPipeError:
            self.running = False
            raise

    def check(self, lean_code: str, filename="test.lean"):
        """
        Sends code to the server and waits for diagnostics (errors).
        Returns: (is_valid, error_log)
        """
        # 1. Open the file (in memory)
        try:
            self.send_request("textDocument/didOpen", {
                "textDocument": {
                    "uri": f"file://{os.path.abspath(filename)}",
                    "languageId": "lean",
                    "version": 1,
                    "text": lean_code
                }
            })
        except BrokenPipeError:
            return False, "Error: Lean server crashed before request."

        # 2. Wait for diagnostics
        errors = []
        start_time = 0
        timeout = 10 # Increased timeout for imports
        
        import time
        start = time.time()

        try:
            while (time.time() - start) < timeout:
                try:
                    msg = self.response_queue.get(timeout=0.1) # Short poll
                except queue.Empty:
                    if self.proc.poll() is not None:
                        return False, "Error: Lean server process died."
                    continue
                
                if msg.get("method") == "textDocument/publishDiagnostics":
                    if msg["params"]["uri"].endswith(filename):
                        diagnostics = msg["params"]["diagnostics"]
                        for d in diagnostics:
                            if d.get("severity") == 1: # 1 = Error
                                errors.append(f"Line {d['range']['start']['line']}: {d['message']}")
                        
                        # We got the diagnostics for OUR file, so we can return.
                        # Note: In a persistent server, we might get empty diagnostics first (clearing errors)
                        # or processing diagnostics. If we assume sync processing, this is okay.
                        break
                        
        except Exception as e:
            return False, f"Error during check: {e}"

        # 3. Close the file to free memory
        try:
            self.send_request("textDocument/didClose", {
                "textDocument": {"uri": f"file://{os.path.abspath(filename)}"}
            })
        except:
            pass

        if not errors:
            return True, "OK"
        else:
            return False, "\n".join(errors)

    def close(self):
        self.running = False
        if self.proc:
            self.proc.terminate()
            try:
                self.proc.wait(timeout=2)
            except subprocess.TimeoutExpired:
                self.proc.kill()

if __name__ == "__main__":
    # Make sure you are in a folder with lakefile.toml!
    print("Initializing Lean Server...")
    server = LeanServer(".")

    # Give it a second to warm up imports if needed
    import time
    time.sleep(2)

    print("Checking code...")
    
    # Example 1: Bad Code
    bad_code = """
    import Mathlib
    theorem bad : 1 = 2 := by rfl
    """
    is_valid, log = server.check(bad_code, "bad.lean")
    print(f"\n--- Bad Code Results ---\nValid: {is_valid}\nLog: {log}")

    # Example 2: Good Code
    good_code = """
    import Mathlib
    theorem good : 1 = 1 := by rfl
    """
    is_valid, log = server.check(good_code, "good.lean")
    print(f"\n--- Good Code Results ---\nValid: {is_valid}\nLog: {log}")

    # Example 3: random Code
    bad_code = """
    import Mathlib
    theorem bad : 1 = 2 := by
    """
    is_valid, log = server.check(bad_code, "random.lean")
    print(f"\n--- Random Code Results ---\nValid: {is_valid}\nLog: {log}")

    server.close()