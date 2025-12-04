#!/usr/bin/env python3
import json
import subprocess
import threading
import queue
import uuid
import textwrap


def debug(*args):
    """Debug print helper."""
    print("[DEBUG]", *args)


class LeanLSP:
    def __init__(self, project_root="."):
        debug("Starting Lean server...")
        self.proc = subprocess.Popen(
            ["lake", "env", "lean", "--server"],
            cwd=project_root,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )

        self.responses = queue.Queue()

        thread = threading.Thread(target=self._reader, daemon=True)
        thread.start()
        debug("Reader thread started.")

        self._initialize()

    def _reader(self):
        while True:
            header = self.proc.stdout.readline()
            if not header:
                continue

            header = header.strip()
            debug("RECV HEADER:", header)

            if not header.startswith("Content-Length:"):
                continue

            length = int(header.split(":")[1].strip())
            blank = self.proc.stdout.readline()
            payload = self.proc.stdout.read(length)

            debug("RECV PAYLOAD:", payload.replace("\n", " "))

            try:
                msg = json.loads(payload)
                self.responses.put(msg)
            except Exception as e:
                debug("JSON decode failed:", e)

    def _send(self, payload):
        body = json.dumps(payload)
        header = f"Content-Length: {len(body)}\r\n\r\n"

        debug("SEND:", body)
        self.proc.stdin.write(header + body)
        self.proc.stdin.flush()

    def _initialize(self):
        debug("Sending initialize request...")

        init_id = str(uuid.uuid4())

        self._send({
            "jsonrpc": "2.0",
            "id": init_id,
            "method": "initialize",
            "params": {"rootUri": None, "capabilities": {}}
        })

        while True:
            msg = self.responses.get()
            debug("INIT RESPONSE:", msg)
            if msg.get("id") == init_id:
                break

        debug("Sending initialized notification...")
        self._send({
            "jsonrpc": "2.0",
            "method": "initialized",
            "params": {}
        })

    def check(self, code: str):
        module_name = f"TmpFile{uuid.uuid4().hex}"
        prefix = f"module {module_name}\n"
        
        # FORCE elaboration by referencing last definition
        code = textwrap.dedent(code).strip()
        lines = code.splitlines()
        
        # Try to extract the last identifier defined
        last_name = None
        for line in reversed(lines):
            line = line.strip()
            if line.startswith("def "):
                # def foo : ...
                parts = line.split()
                if len(parts) >= 2:
                    last_name = parts[1]
                    break
            if line.startswith("theorem "):
                parts = line.split()
                if len(parts) >= 2:
                    last_name = parts[1]
                    break
        
        # Now force elaboration
        force_eval = ""
        if last_name:
            force_eval = f"\n#check {last_name}\n"
        
        code = prefix + code + force_eval + "\n"
        
        uri = f"file:///{module_name}.lean"

        # OPEN THE DOC
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

        diagnostics = None

        # WAIT FOR FIRST diagnostics
        while True:
            msg = self.responses.get()

            if msg.get("method") == "textDocument/publishDiagnostics":
                uri2 = msg["params"]["uri"]
                if uri2 == uri:
                    diagnostics = msg["params"]["diagnostics"]
                    break

        # CLOSE DOC
        self._send({
            "jsonrpc": "2.0",
            "method": "textDocument/didClose",
            "params": {"textDocument": {"uri": uri}}
        })

        return diagnostics or []




if __name__ == "__main__":
    import time
    t0 = time.time()
    server = LeanLSP(project_root="/Users/austinshen/Documents/Umich/Research/LeanQC_AI/AutoEvaluation")

    tests = [
        r"""
        import Mathlib
        theorem good1 : True := by trivial
        """,

        # syntax error
        r"""
        import Mathlib
        def x : Nat :=
            5 + -- <-- broken token
        """,

        # unknown constant
        r"""
        import Mathlib
        def y := nonsenseIdentifier + 3
        """,

        # wrong number of arguments
        r"""
        import Mathlib
        theorem junk : True := Nat.succ
        """,

        # type mismatch in definition annotation
        r"""
        import Mathlib
        def z : Nat := fun x => x
        """,
    ]

    for i, snippet in enumerate(tests):
        print(f"\n===== TEST {i+1} =====")
        res = server.check(snippet)
        if res:
            print("❌ ERRORS:")
            for d in res:
                print("   →", d["message"])
        else:
            print("✔ OK")

    print("\nTime:", time.time() - t0)
