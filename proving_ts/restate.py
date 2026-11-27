"""For the two theorems whose type hash changed: restate the original text and prove it with the final theorem."""
# Paths: set STUDY_ROOT (this repository), WORK_ROOT (folder holding ts_ws/, auditreal/, ...)
# and DISS_ROOT to override. Defaults: the repo root; E:/ on Windows, ~/work/ elsewhere; parent of the repo.
import os as _os
def _repo_root():
    d = _os.path.dirname(_os.path.abspath(__file__))
    while not _os.path.exists(_os.path.join(d, "CLOUD.md")) and _os.path.dirname(d) != d:
        d = _os.path.dirname(d)
    return d
_STUDY = _os.environ.get("STUDY_ROOT", _repo_root()).replace("\\", "/").rstrip("/")
_WR = _os.environ.get("WORK_ROOT", "E:/" if _os.name == "nt" else _os.path.expanduser("~/work")).replace("\\", "/").rstrip("/") + "/"
_DISS = _os.environ.get("DISS_ROOT", _os.path.dirname(_STUDY)).replace("\\", "/").rstrip("/") + "/"
import io, re
B = _WR + "ts_ws/prove_ts/base_copy/"
t = io.open(B + "TypeSound.lean", encoding="utf-8").read()
f = io.open(_WR + "ts_ws/prove_ts/ws/lean/CmlTS/TypeSound.lean", encoding="utf-8").read()
head = t[:t.index("theorem ")] if False else ""
out = "import CmlTS\nopen CmlTS\nnamespace CmlTS\n"
for n in ["decs_type_sound_no_check", "op_type_sound"]:
    m = re.search(r"theorem %s\s*(.*?):= by\s+sorry" % n, t, re.S)
    s = m.group(1)
    print(n, "statement text present in final file:", re.sub(r"\s+", " ", s).strip() in re.sub(r"\s+", " ", f))
    out += "theorem restated_%s %s:= @%s\n" % (n, s, n)
out += "#print axioms restated_op_type_sound\n#print axioms restated_decs_type_sound_no_check\nend CmlTS\n"
pre = "\n".join(l for l in t.split("\n") if l.startswith("open ") or l.startswith("universe") or l.startswith("set_option") or l.startswith("variable"))
io.open(_WR + "ts_ws/prove_ts/ws/lean/Restate.lean", "w", encoding="utf-8", newline="\n").write(out.replace("open CmlTS\n", "open CmlTS\n" + pre + "\n", 1))
