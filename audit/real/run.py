"""Run one arm step on one unit.  python run.py <step> <unit> ; steps: S1 S3a S3b S4 S6
Outputs runs/<unit>/<step>.{raw,json,meta}. Skips finished steps. No spending cap (owner, 24 Nov)."""
import io, json, os, re, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__)).replace("\\", "/") + "/"
step, unit = sys.argv[1:3]
W = "E:/auditreal/" + unit
key = {k["unit"]: k for k in json.load(io.open(HERE + "key.json", encoding="utf-8"))}[unit]
out = HERE + "runs/" + unit + "/"
os.makedirs(out, exist_ok=True)
if os.path.exists(out + step + ".json"):
    sys.exit(0)


def rd(p):
    return io.open(p, encoding="utf-8").read()


def parse(t):
    for m in reversed(list(re.finditer(r"\{", t))):
        pass
    i, j = t.find("{"), t.rfind("}")
    return json.loads(t[i:j + 1]) if i >= 0 else None


brief = rd(HERE + "BRIEF_audit.md").replace("@MODULE@", key["module"])
src = {"S4": "S1", "S6": "S3a"}.get(step)
if src:
    f = json.load(io.open(out + src + ".json", encoding="utf-8"))["findings"]
    if not f:
        json.dump({"verdicts": []}, open(out + step + ".json", "w"))
        sys.exit(0)
    prompt = rd(HERE + "REVIEW.md").replace("@MODULE@", key["module"]) + json.dumps(
        [{k: x.get(k) for k in ("id", "declaration", "lean", "hol4", "class", "explanation", "repair")} for x in f], ensure_ascii=False, indent=1)
else:
    prompt = brief
env = dict(os.environ)
env.pop("CLAUDECODE", None)
env["CLAUDE_CODE_GIT_BASH_PATH"] = "D:\\Git\\bin\\bash.exe"
if step == "S1":
    feats = "memories plugins apps browser_use computer_use multi_agent image_generation skill_search goals in_app_browser tool_suggest".split()
    cmd = [shutil.which("codex"), "exec", "-m", "gpt-6.2-astra", "-s", "read-only", "--skip-git-repo-check", "--ephemeral", "-c", "project_doc_max_bytes=0",
           "-c", "web_search=disabled", "-c", "model_reasoning_effort=high", "--json", "-o", out + step + ".last"]
    for x in feats:
        cmd += ["--disable", x]
    cmd.append("-")
    stdin = prompt
elif step == "S4":
    prompt += chr(10) * 2 + "Use only the file viewing, listing and text search tools. Shell commands are not available in this run; do not request them." + chr(10)  # added 24 Nov 13:05 UTC after headless denials
    cmd = [shutil.which("agy"), "-p", prompt, "--model", "gemini-4-neon-high", "--sandbox", "--mode", "plan", "--output-format", "stream-json", "--new-project"]
    stdin = ""
else:
    cmd = [shutil.which("claude"), "-p", "--model", "claude-opus-5-5", "--effort", "high", "--settings", HERE + "settings_audit.json", "--setting-sources", "",
           "--strict-mcp-config", "--disable-slash-commands", "--tools", "Read,Glob,Grep", "--permission-mode", "dontAsk", "--output-format", "stream-json", "--verbose"]
    stdin = prompt
t0 = time.time()
r = subprocess.run(cmd, input=stdin.encode("utf-8"), stdout=open(out + step + ".raw", "wb"), stderr=open(out + step + ".err", "wb"), cwd=W, env=env)
dt = time.time() - t0
raw = rd(out + step + ".raw")
meta = {"step": step, "unit": unit, "seconds": round(dt), "rc": r.returncode}
final = ""
for l in raw.split("\n"):
    try:
        o = json.loads(l)
    except Exception:
        continue
    if o.get("type") == "turn.completed":
        meta["usage"] = o["usage"]
    if o.get("type") == "result":
        final = o.get("result") or o.get("response") or ""
        for k in ("total_cost_usd", "num_turns", "usage", "modelUsage", "is_error", "subtype", "stats"):
            if k in o:
                meta[k] = o[k]
if step == "S1":
    final = rd(out + step + ".last")
elif step == "S4":
    for l in raw.splitlines():
        if l.startswith('{"event":"result"'):
            rr = json.loads(l)["result"]
            final = rr["response"]
            meta["usage"], meta["status"] = rr.get("usage"), rr.get("status")
json.dump(meta, io.open(out + step + ".meta", "w", encoding="utf-8"), indent=1)
try:
    d = parse(final)
except Exception:
    d = None
if not (d and ("findings" in d or "verdicts" in d)):
    sys.exit(3)
json.dump(d, io.open(out + step + ".json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
print(step, unit, round(dt), "s", len(d.get("findings", d.get("verdicts"))))
