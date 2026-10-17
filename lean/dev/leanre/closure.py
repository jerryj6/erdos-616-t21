import os,re,sys
P='lean/erdos/.lake/packages'
roots=sys.argv[1:]
pk={'Mathlib':'mathlib','Batteries':'batteries','Aesop':'aesop','Qq':'Qq','ProofWidgets':'proofwidgets','Plausible':'plausible','ImportGraph':'importGraph','LeanSearchClient':'LeanSearchClient'}
seen=set();st=list(roots);files=[]
while st:
  m=st.pop()
  if m in seen: continue
  seen.add(m)
  top=m.split('.')[0]
  if top not in pk: continue
  src=os.path.join(P,pk[top],*m.split('.'))+'.lean'
  if not os.path.exists(src): print('MISSING',m,file=sys.stderr); continue
  files.append((pk[top],m))
  for line in open(src,encoding='utf8'):
    mm=re.match(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)',line.strip())
    if mm: st.append(mm.group(1))
for p,m in files: print(p,m)
