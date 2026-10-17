import sys, ast, subprocess
tt, name = sys.argv[1], sys.argv[2]
out = subprocess.run(['python3','k4enum1.py',tt,name],capture_output=True,text=True).stdout.splitlines()
sols = [ast.literal_eval(l) for l in out if l.startswith('{')]
keys = ['v','w','al','ga','m3','a3','a4','c3','c4','O0','O1','O2','O3','out']
print(name, len(sols))
for k in keys:
    vals = [s.get(k,0) for s in sols]; print(f'  {k}: {min(vals)}..{max(vals)}', end='')
print()
