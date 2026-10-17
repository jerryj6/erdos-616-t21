"""Insert stdin text at the end of the 'Wave 13 N-K4 compute' section (before the next '## ' header) of the t21 write-up."""
import sys
f='candidates/erdos-616-t21-upper.md'
L=open(f).read().split('\n'); t=sys.stdin.read().rstrip('\n').split('\n')
s=next(i for i,l in enumerate(L) if l.startswith('## Wave 13 N-K4 compute'))
e=next((i for i in range(s+1,len(L)) if L[i].startswith('## ')), len(L))
while e>s and L[e-1]=='': e-=1
L[e:e]=t; open(f,'w').write('\n'.join(L)); print('inserted', len(t), 'lines at', e)
