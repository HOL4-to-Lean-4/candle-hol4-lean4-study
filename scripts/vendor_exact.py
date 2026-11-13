"""Write an upstream git tree into <repo>/<prefix> byte-for-byte and make the
repo's index entries for it identical (mode + blob hash) to the upstream tree.
Usage: vendor_exact.py UPSTREAM_REPO COMMIT TARGET_REPO PREFIX"""
import os, shutil, subprocess, sys
from pathlib import Path

up, commit, repo, prefix = sys.argv[1], sys.argv[2], Path(sys.argv[3]), sys.argv[4].rstrip("/")
ls = subprocess.check_output(["git", "-C", up, "ls-tree", "-r", "-z", commit]).split(b"\0")
entries = []
for e in ls:
    if not e:
        continue
    meta, path = e.split(b"\t", 1)
    mode, typ, sha = meta.split()
    if typ != b"blob":
        raise SystemExit(f"unsupported entry {e!r}")
    entries.append((mode.decode(), sha.decode(), path.decode("utf-8")))

dest = repo / prefix
if dest.exists():
    shutil.rmtree(dest)
cat = subprocess.Popen(["git", "-C", up, "cat-file", "--batch"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
for mode, sha, path in entries:
    cat.stdin.write(sha.encode() + b"\n"); cat.stdin.flush()
    hdr = cat.stdout.readline().split()
    size = int(hdr[2])
    data = cat.stdout.read(size); cat.stdout.read(1)
    out = dest / path
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(data)  # symlinks are written as a file holding the target, as Git does with core.symlinks=false
cat.stdin.close(); cat.wait()

# store the exact blobs in the target repo and point the index at them
paths = "\n".join(str((dest / p).resolve()) for _, _, p in entries) + "\n"
hashes = subprocess.run(["git", "-C", str(repo), "hash-object", "-w", "--no-filters", "--stdin-paths"],
                        input=paths.encode(), capture_output=True, check=True).stdout.decode().split()
bad = [(p, s, h) for (_, s, p), h in zip(entries, hashes) if s != h]
if bad:
    raise SystemExit(f"{len(bad)} blobs differ, e.g. {bad[:3]}")
subprocess.run(["git", "-C", str(repo), "rm", "-r", "-q", "-f", "--cached", "--ignore-unmatch", prefix], check=True)
info = "".join(f"{m} {s}\t{prefix}/{p}\n" for m, s, p in entries)
subprocess.run(["git", "-C", str(repo), "update-index", "--add", "--index-info"], input=info.encode(), check=True)
print(f"{prefix}: {len(entries)} entries, all blobs identical, modes copied "
      f"({sum(m == '100755' for m, _, _ in entries)} executable, {sum(m == '120000' for m, _, _ in entries)} symlinks)")
