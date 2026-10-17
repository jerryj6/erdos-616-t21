"""Re-derive and independently verify a T1-T3 trace system on 10 points containing a non-uniform seed (a=3)."""
import itertools, subprocess, ast
out = subprocess.run(['python3', 'tracefam.py', '10', '3'], capture_output=True, text=True).stdout.splitlines()
# rerun printing full family
import sys
sys.argv = ['x', '10', '3']
src = open('tracefam.py').read().replace("print(len(fam), fam[:60])", "print(len(fam)); print(fam)")
ns = {}; exec(compile(src, 'tf', 'exec'), ns)
