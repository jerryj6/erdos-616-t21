import time, numpy as np, itertools
import orbitsat as o
n=21; G=o.make_group('pgaml34',n)
t=time.time(); reps=o.orbit_reps(G,n,9,17); print('reps',len(reps),time.time()-t,flush=True)
t=time.time(); ok=o.self_ok(G,reps,n,5); print('selfok',ok.sum(),time.time()-t,flush=True)
t=time.time(); imgs=o.all_images(G,reps,n); print('imgs',time.time()-t,flush=True)
t=time.time(); S,oid=o.expand(G,reps,[int(np.nonzero(ok)[0][0])],n); print('expand',len(S),time.time()-t,flush=True)
t=time.time(); print(o.pair_triple_viol(S,oid,5,10)[1], time.time()-t,flush=True)
t=time.time(); print(o.incompat(0,reps,imgs,ok,5), time.time()-t,flush=True)
