import json
from w13_enum import NAMES, W8
from w13_tau import orbit
from w13_enum import nm, n
I={s:a for a,s in enumerate(NAMES)}; W=dict(zip(NAMES,W8))
R={r['B']:r for r in json.load(open('w13_rigid.json'))}
tried={'J1':'v,w,al0,al1','JB1':'w,al0,m0,m2','JB2':'v,al0,al1,g1','JB3':'w,g0,g1,m0','JM1':'v,al0,al1,m0','JN2':'v,w,g0,g2','JN3':'v,al1,g0,c3','JN4':'v,w,m0,a3_0',
       'JP1a':'v,g0,g1,g2','JP1b':'al0,g1,g2,m2','JP1c':'al0,g1,g2,m1','JP2a':'w,al0,al1,m0','JP2b':'w,al0,g0,m2','JP2c':'al1,g0,g1,m0','JP3a':'w,g1,m1,m2','JP3b':'w,g0,g1,g2','JP3c':'w,g0,g1,m2'}
tset={frozenset(v.split(',')):k for k,v in tried.items()}
def bm(s): return sum(1<<I[x] for x in s.split(','))
def entry(rep, tier, why):
    B=bm(rep); orb=sorted(orbit(B)); r=R.get(nm(B)) or R.get(nm(min(orb,key=lambda x:x)))
    rr=None
    for X in orb:
        if nm(X) in R: rr=R[nm(X)]
    imgs=[]
    for X in orb:
        names=[NAMES[a] for a in range(n) if X>>a&1]
        imgs.append(dict(avoid=[W[x] for x in names], short='{'+','.join(names)+'}', tried_as=tset.get(frozenset(names))))
    return dict(tier=tier, rep='{'+rep+'}', orbit_size=len(orb), rigidity_nsig=rr['nsig'] if rr else None,
                avoider_states=rr['states'] if rr else None, avoider_never_firstgen_states=rr['nonfirstgen'] if rr else None,
                why=why, images=imgs)
C=[]
C.append(entry('v,w,al0,al1','A1 (G-invariant; most rigid of all 145 base-transversal orbits)',
 'B = T012∪T013∪T023 = every point of P0 lying in a triple intersection. Lemma JA (S13.4): the avoider J has |J∩γ|≥2+o0+o1, '
 'a3,a4,m3 each hit, and Σ|J∩P_i|∈{20,21}: J meets ≥3 base edges in exactly 5 (all four in 72/109 local states), i.e. J is a FIFTH '
 'vertex of a clique of 5-pairs and spawns new K4s {P0,P1,P2,J} (triples 1,m\',a3\',g\'+c3\'), {P0,P1,P3,J}, {P0,P2,P3,J}. '
 'In 106/109 local states J is itself a first-gen single of (0,1)/(0,2)/(0,3) in a RARE shape (e.g. a (0,1)-single with A-part a3∪a4: one '
 'region signature), so it forces a single type into an extreme state. In the 10-single realization M10 (and w12m1) EVERY edge contains {v,w} or α (min transversals {v|w}×{al0|al1}); J_A is exactly the edge that breaks this. '
 'Tried ONLY in chain B (7 γ-singles, no m3-singles), where it was REALIZED (w10x_w12b1/Br1/Br2_real.json contain J1) — so it is not a killer by itself; '
 'never tried together with the m3-singles (chains M/N/P).'))
C.append(entry('v,w,c3,c4','A2 (G-invariant)',
 'Avoids both 1-point triples (all six apex inequalities S13.2 + two L3) and c3,c4 so J∩N12 = J∩N13 = J∩γ: J is a (1,2)- and (1,3)-single '
 'of the SAME γ-type, or a multi with |J∩γ|≥2. Covers the realized min transversals {w,c3},{v,c4} of M10. Untried.'))
C.append(entry('al0,al1,c3,c4','A3 (G-invariant; weakest of the three)',
 'Avoids T023 (L3: |J∩(P0∪P2∪P3)|≤10) and c3,c4; J∩N23 ⊆ γ. Untried.'))
C.append(entry('v,w,g0,g1','B1 (orbit 3; 2nd most rigid, nsig 21)',
 'Non-single avoiders (64/106 local states) contain c3,c4 and the third γ point; otherwise J is a (1,2)/(1,3)-single of type g2 or a (0,1)-single. '
 'JN2={v,w,g0,g2} is one image; add the other two images for the symmetric closure.'))
C.append(entry('v,w,al0,g0','B2 (orbit 6, nsig 33)','Two 1-point triples avoided + one point of each of α, γ. Untried.'))
C.append(entry('v,al0,al1,g0','B3 (orbit 6, nsig 46)','T012∪T023 avoided (two L3, three apex inequalities) + one γ point; JB2={v,al0,al1,g1} is an image (chain B only). Untried with m3-singles.'))
C.append(entry('v,al0,al1,c3','B4 (orbit 2, nsig 57)','T012∪T023 + c3: J∩N12 ⊆ γ, J∩N02 ⊆ a3. Untried.'))
C.append(entry('v,w,g0,c3','B5 (orbit 6, nsig 58)','Both 1-point triples + g0 + c3: J∩N12 ⊆ {g1,g2}. Untried.'))
redundant=[dict(set='{'+s+'}', note='avoider is ALWAYS a first-generation single (w13_rigid: always_firstgen) — equivalent to adding that gen-1 single slot')
           for s in ['v,g0,g1,g2','w,g0,g1,g2','v,w,m0,m1','al0,al1,g0,g1','al0,g0,g1,g2']]
out=dict(created='2026-10-16 Wave 13 N-K4 structure (hand/structural agent)', names='w8/w10x point names; v=T012_0 w=T013_0 alpha=T023_* gamma=T123_* m3=p01_* a3=p02_* a4=p03_* c3=p12_0 c4=p13_0',
 soundness='Every entry is a slot "an edge avoiding this 4-set of named points": exists in every counterexample by tau>=5, so adding any of them is sound regardless of this ranking. The ranking is heuristic.',
 ranking_metric='rigidity_nsig = number of region signatures (counts per region v,w,alpha,gamma,m3,a3,a4,c3,c4 + o-vector) of avoider states feasible against the base under all one-new-edge lemmas (w13_enum.check; o_i<=L_i+2). Lower = more forced. Computed over all 145 symmetry orbits of base-transversal core 4-sets (group order 576), w13_rigid.json.',
 caveat='No 4-set is provably forced-hit by the first-generation singles at the one- or two-edge level (S13.3); the list is principled by symmetry + local rigidity, not by a joint proof.',
 candidates=C, redundant_as_tau_edges=redundant)
json.dump(out,open('w13_tau_candidates.json','w'),indent=1,ensure_ascii=False)
for c in C: print(c['tier'], c['rep'], c['orbit_size'], c['rigidity_nsig'], [i['tried_as'] for i in c['images']])
