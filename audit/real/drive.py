"""Run the arms over all units, resumable.  python drive.py astra|opus_a|opus_b
astra: S1 then S4 ; opus_a: S3a then S6 ; opus_b: S3b.  A failed call (usage limit, no JSON) waits and is retried, at most 30 times per step."""
import io, json, os, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__)).replace("\\", "/") + "/"
STEPS = {"astra": ["S1"], "neon": ["S4"], "opus_a": ["S3a", "S6"], "opus_b": ["S3b"]}[sys.argv[1]]
for k in json.load(io.open(HERE + "key.json", encoding="utf-8")):
    for s in STEPS:
        while s == "S4" and not os.path.exists(HERE + "runs/%s/S1.json" % k["unit"]):
            time.sleep(30)
        for attempt in range(6 if s == "S4" else 30):
            t = time.time()
            r = subprocess.run([sys.executable, HERE + "run.py", s, k["unit"]], capture_output=True, timeout=2400)
            print(time.strftime("%H:%M:%S", time.gmtime()), s, k["unit"], r.returncode, r.stdout.decode("utf-8", "replace").strip(), flush=True)
            if r.returncode == 0:
                break
            err = r.stderr.decode("utf-8", "replace")[-300:]
            if err:
                print(err, flush=True)
            time.sleep(60 if s in ("S1", "S4") else 600)
