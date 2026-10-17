import sys
from k4model import build, base_sizes
from k4wit import single_patterns, topat
from ortools.sat.python import cp_model
tt = tuple(int(x) for x in sys.argv[1].split(',')); name = sys.argv[2]
sp = single_patterns(tt)
import ast
pat = sp[name] if name in sp else ast.literal_eval(name)
m, c, regs = build(5, tt, {4: topat(pat)})
names = {7:'v',11:'w',13:'al',14:'ga',3:'m3',5:'a3',9:'a4',6:'c3',10:'c4',12:'p23',1:'O0',2:'O1',4:'O2',8:'O3',0:'out'}
X = [T for T in regs if T >> 4 & 1]
class CB(cp_model.CpSolverSolutionCallback):
    def __init__(s): super().__init__(); s.n = 0
    def on_solution_callback(s):
        s.n += 1
        print({names[T & 15]: s.Value(c[T]) for T in X if s.Value(c[T])})
s = cp_model.CpSolver(); s.parameters.enumerate_all_solutions = True; s.parameters.num_workers = 1
cb = CB(); s.Solve(m, cb); print('total', cb.n)
