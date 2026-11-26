"""Run an SML file in a HOL4 context in WSL and print the output.  python run_sml.py candle|ts FILE.sml"""
import os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from vcheck import CTX, ENV

ctx, f = sys.argv[1], sys.argv[2]
wp = subprocess.run(["wsl.exe", "-e", "wslpath", "-a", os.path.abspath(f).replace("\\", "/")], capture_output=True).stdout.decode().replace("\0", "").strip()
d, loads = CTX[ctx]
pre = "val _ = List.app load [" + ",".join('"%s"' % l for l in loads) + "];\n"
sh = ENV + 'cd %s; { printf %%s \'%s\'; cat "%s"; } > _probe.sml; timeout 1800 hol run _probe.sml; echo "exit=$?"; rm -f _probe.sml' % (d, pre.replace("'", ""), wp)
r = subprocess.run(["wsl.exe", "-e", "sh", "-c", sh], capture_output=True)
sys.stdout.buffer.write((r.stdout + r.stderr).replace(b"\0", b""))
