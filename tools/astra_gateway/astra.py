"""Call GPT models (Astra) through the SSS gateway, an OpenAI-compatible API.

Reads SSS_BASE_URL and SSS_GPT_KEY from the environment (cloud environment "Default").
The key is never printed or written to a file.

  python astra.py models                       # list the models the gateway offers
  python astra.py probe [-m MODEL]             # one tiny call; prints the model the gateway reports + usage
  python astra.py ask [-m MODEL] [-e EFFORT] [-o OUT] < prompt.md
        # one Responses API call, no tools. Writes OUT.txt (answer) and OUT.meta.json
        # (requested and reported model, response id, usage, seconds).

For audits that let Astra read files, use codex_astra.sh (Codex CLI with the gateway as provider).
Standard library only. HTTPS goes through HTTPS_PROXY when it is set.
"""
import argparse, json, os, sys, time, urllib.error, urllib.request

DEFAULT_MODEL = "gpt-6.2-astra"


def base():
    b = os.environ.get("SSS_BASE_URL", "").rstrip("/")
    if not b or not os.environ.get("SSS_GPT_KEY"):
        sys.exit("SSS_BASE_URL or SSS_GPT_KEY is not set (select the cloud environment 'Default').")
    return b if b.endswith("/v1") else b + "/v1"


def call(path, body=None, timeout=1800):
    req = urllib.request.Request(base() + path, data=None if body is None else json.dumps(body).encode("utf-8"),
                                 headers={"Authorization": "Bearer " + os.environ["SSS_GPT_KEY"], "Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        sys.exit("HTTP %d from gateway: %s" % (e.code, e.read().decode("utf-8", "replace")[:500]))


def text_of(resp):
    out = []
    for item in resp.get("output", []):
        for c in item.get("content") or []:
            if c.get("type") == "output_text":
                out.append(c.get("text", ""))
    return "".join(out)


def usage_of(resp):
    u = dict(resp.get("usage") or {})
    u.pop("attribution", None)  # per-item breakdown; large and not needed in the ledger
    return u


def respond(model, prompt, effort=None):
    body = {"model": model, "input": prompt}
    if effort:
        body["reasoning"] = {"effort": effort}
    t0 = time.time()
    r = call("/responses", body)
    meta = {"requested_model": model, "reported_model": r.get("model"), "response_id": r.get("id"), "status": r.get("status"),
            "usage": usage_of(r), "seconds": round(time.time() - t0, 1), "gateway": base().split("/")[2],
            "utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    return text_of(r), meta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["models", "probe", "ask"])
    ap.add_argument("-m", "--model", default=DEFAULT_MODEL)
    ap.add_argument("-e", "--effort", default=None, help="reasoning effort, e.g. high")
    ap.add_argument("-o", "--out", default=None, help="output prefix for ask")
    a = ap.parse_args()
    if a.cmd == "models":
        print("\n".join(sorted(m["id"] for m in call("/models").get("data", []))))
    elif a.cmd == "probe":
        txt, meta = respond(a.model, "Reply with exactly: OK")
        meta["answer"] = txt.strip()[:50]
        print(json.dumps(meta))
    else:
        txt, meta = respond(a.model, sys.stdin.read(), a.effort)
        if a.out:
            open(a.out + ".txt", "w", encoding="utf-8").write(txt)
            json.dump(meta, open(a.out + ".meta.json", "w", encoding="utf-8"), indent=1)
            print(json.dumps(meta))
        else:
            print(txt)
            print(json.dumps(meta), file=sys.stderr)
        if meta["reported_model"] != a.model:
            print("WARNING: gateway reported model %r, requested %r" % (meta["reported_model"], a.model), file=sys.stderr)


if __name__ == "__main__":
    main()
