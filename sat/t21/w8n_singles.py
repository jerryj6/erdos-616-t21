"""Five singles (one per type) at a 5-pair under NK: how many distinct (A,C) parts can occur?
Exact model (singles live entirely in model points)."""
import sys; sys.path.insert(0,'.')
import w8n_model as W
from ortools.sat.python import cp_model
import itertools
for cls in [(2,4),(3,3),(3,4)]:
  for mode in ['F2 differs from F0 and F1', 'three distinct incl F2,F3']:
    md,Wl,nf,nk = W.build(cls=cls, wit=(), fam_max=5)
    m=md.m
    def differ(x,y):
        d=[]
        for p in W.A+W.C:
            b=m.NewBoolVar(''); m.Add(md.E[x][p]!=md.E[y][p]).OnlyEnforceIf(b); d.append(b)
        m.AddBoolOr(d)
    differ('F2','F0'); differ('F2','F1')
    if mode.startswith('three'):
        differ('F3','F0'); differ('F3','F1'); differ('F3','F2')
    s=cp_model.CpSolver(); s.parameters.max_time_in_seconds=40; s.parameters.num_workers=2
    st=s.Solve(m); print(cls, mode, s.StatusName(st), flush=True)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        for y in range(5):
            print('  F%d'%y,[p-5 for p in W.A if s.Value(md.E['F%d'%y][p]) if not isinstance(md.E['F%d'%y][p],int)] or [p-5 for p in W.A if md.E['F%d'%y][p] is 1],
                  [p-21 for p in W.C if (md.E['F%d'%y][p] if isinstance(md.E['F%d'%y][p],int) else s.Value(md.E['F%d'%y][p]))])
