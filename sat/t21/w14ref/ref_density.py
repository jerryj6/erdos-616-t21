"""REFEREE control: on random trace pairs my checker must find non-conflicts (density near the authors' 0.226), and
must agree with the authors' full matrix w14_conf.npz (data) on those pairs."""
import numpy as np, random
from pairref import load_states, check_pairs, P, OS
first, cnt, B, O = load_states('ref_states.npz')
z = np.load('../w14/w14_conf.npz'); C = z['C']; NT = len(z['T'])
random.seed(7); pa = []; pb = []
for _ in range(20000):
    i, j = random.sample(range(NT), 2); pa.append(i + 1); pb.append(j + 1)
pa = np.array(pa); pb = np.array(pb)
res = check_pairs(pa, pb, first, cnt, B, O, P, OS)
mine = res == 0
theirs = np.array([bool(np.unpackbits(C[i - 1])[j - 1]) for i, j in zip(pa, pb)])
print('random pairs', len(pa), 'my conflict density', mine.mean(), 'authors', theirs.mean(),
      'mine&~theirs', int((mine & ~theirs).sum()), 'theirs&~mine (UNSOUND if >0)', int((theirs & ~mine).sum()))
