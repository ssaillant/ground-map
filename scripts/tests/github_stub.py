# Minimal stand-in for the GitHub REST API, for scripts/tests/publish_results_test.sh.
# Usage: github_stub.py PORT {ok|open|expired}
import http.server, json, os, sys
MODE = sys.argv[2] if len(sys.argv) > 2 else "ok"
LOG = os.environ.get("STUB_LOG", "requests.log")
class H(http.server.BaseHTTPRequestHandler):
    def log_message(self, *a): pass
    def send(self, code, obj, hdr={}):
        b = json.dumps(obj).encode(); self.send_response(code)
        for k, v in hdr.items(): self.send_header(k, v)
        self.send_header("Content-Length", str(len(b))); self.end_headers(); self.wfile.write(b)
    def do_GET(self):
        open(LOG, "a").write(f"GET {self.path} auth={self.headers.get('Authorization')}\n")
        if MODE == "expired": return self.send(401, {"message": "Bad credentials"})
        if "/pulls" in self.path:
            return self.send(200, [{"html_url": "https://example/pull/99"}] if MODE == "open" and "head=" in self.path else [])
        self.send(200, {"full_name": "o/r"}, {"github-authentication-token-expiration": "2026-12-05 10:00:00 UTC"})
    def do_POST(self):
        body = self.rfile.read(int(self.headers["Content-Length"]))
        open(LOG, "a").write(f"POST {self.path}\n{body.decode()}\n")
        self.send(201, {"html_url": "https://example/pull/42"})
http.server.HTTPServer(("127.0.0.1", int(sys.argv[1])), H).serve_forever()
