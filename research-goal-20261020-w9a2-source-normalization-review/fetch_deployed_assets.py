"""Anonymous GET-only capture of the current deployed submit page and its JS.

Never creates a browser session, executes fetched code, or submits a request.
"""
from concurrent.futures import ThreadPoolExecutor
from html.parser import HTMLParser
import hashlib
import json
from pathlib import Path
from urllib.parse import urljoin, urlsplit
from fetch_public_source import fetch, save


class Scripts(HTMLParser):
    def __init__(self):
        super().__init__()
        self.paths = set()

    def handle_starttag(self, tag, attrs):
        values = dict(attrs)
        if tag == "script" and values.get("src"):
            self.paths.add(values["src"])


def main():
    base = "https://www.riemannzeta.fun"
    raw, receipt = fetch(base + "/submit", "deployed/submit.html")
    parser = Scripts()
    parser.feed(raw.decode("utf-8"))
    paths = sorted(parser.paths)
    assert 0 < len(paths) < 80
    def one(path):
        url = urljoin(base, path)
        assert urlsplit(url).scheme == "https"
        assert urlsplit(url).netloc == urlsplit(base).netloc
        assert urlsplit(url).path.startswith("/_next/")
        filename = hashlib.sha256(url.encode()).hexdigest() + ".js"
        _, record = fetch(url, "deployed/assets/" + filename)
        return {"path": path, "file": "deployed/assets/" + filename, **record}
    with ThreadPoolExecutor(max_workers=4) as pool:
        assets = list(pool.map(one, paths))
    report = {"scope": "Current anonymous deployment GET-only; no script execution, session access, or submission",
        "page": receipt, "assets": assets, "HTTP_methods": ["GET"],
        "proof_or_website_write_calls": 0}
    save("deployed/capture.json", (json.dumps(report, indent=2) + "\n").encode())
    print(json.dumps({"assets": len(assets), "page_sha256": receipt["sha256"],
        "proof_or_website_write_calls": 0}), flush=True)


if __name__ == "__main__":
    main()
