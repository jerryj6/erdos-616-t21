#!/usr/bin/env python3
# rss.py OUTFILE cmd... : run cmd (stdout+stderr -> OUTFILE), append "exit E time Ts MAXRSS M MB"
import sys, subprocess, resource, time
out = sys.argv[1]; cmd = sys.argv[2:]
t = time.time()
with open(out, 'w') as f:
    r = subprocess.call(cmd, stdout=f, stderr=subprocess.STDOUT)
m = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss // 1024
with open(out, 'a') as f:
    f.write(f"exit {r} time {int(time.time()-t)}s MAXRSS {m} MB\n")
