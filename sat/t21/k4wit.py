import itertools
from k4model import base_sizes, reg
def single_patterns(tt):
    bs = base_sizes(tt); out = {}
    for i, j in itertools.combinations(range(4), 2):
        I = (1 << i) | (1 << j)
        Ms = [b for b in bs if b & I == I and bs[b] > 0]
        for R in Ms:
            pat = {b: bs[b] - (1 if b == R else 0) for b in Ms}
            pat = {b: v for b, v in pat.items() if v > 0}
            out[f'S{i}{j}_{R}'] = pat
    return out
def topat(d):
    return [(reg(b), mu) for b, mu in d.items()]
