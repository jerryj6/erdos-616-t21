#!/usr/bin/env python3
"""Lake-free build of the Lean development (fallback for environments where `lake build` is unavailable).

It does what `lake build` does for this project, with plain `lean` / `leanc` calls:

  1. compiles the core-Lean checker modules `Erdos616Checkers.*` to .olean and to C, and links the C code into one
     shared library `libErdos616Checkers.so` (this is what makes `native_decide` run compiled code);
  2. elaborates every module needed for the target, in import order, with `--load-dynlib` pointing at that library.

Usage (from anywhere):

    python3 scripts/build_direct.py [TARGET_MODULE ...] [--mathlib-lib DIR ...] [--neg]

TARGET_MODULE defaults to `Erdos616.Final`. Mathlib and its dependencies must already be built; by default their
`.lake/build/lib/lean` directories are taken from `lean/.lake/packages/*/` (as populated by `lake exe cache get`).
Use `--mathlib-lib` to point elsewhere. `--neg` additionally runs the negative control `lean/test/Neg.lean`, which
must FAIL to elaborate.

The build is resumable: a module whose .olean is newer than its source and its imports is skipped.
Output goes to `lean/.lake/direct/` (oleans, C files, logs) and needs `data/` populated (scripts/fetch_certs.sh).
"""
import os, re, sys, subprocess, time, glob

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEANDIR = os.path.join(ROOT, 'lean')
OUT = os.path.join(LEANDIR, '.lake', 'direct')
LIB, CDIR, LOGS = (os.path.join(OUT, d) for d in ('lib', 'c', 'logs'))
CHECKERS = ['Erdos616Checkers.LratCheck', 'Erdos616Checkers.LratChunk', 'Erdos616Checkers.TrCheck',
            'Erdos616Checkers.G14Check']
SO = os.path.join(OUT, 'libErdos616Checkers.so')


def src_of(mod):
    return os.path.join(LEANDIR, *mod.split('.')) + '.lean'


def olean_of(mod):
    return os.path.join(LIB, *mod.split('.')) + '.olean'


def local_imports(mod):
    out = []
    for line in open(src_of(mod)):
        m = re.match(r'^import\s+(\S+)', line)
        if m and os.path.exists(src_of(m.group(1))):
            out.append(m.group(1))
    return out


def closure(targets):
    order, seen = [], set()
    def visit(m):
        if m in seen: return
        seen.add(m)
        for d in local_imports(m): visit(d)
        order.append(m)
    for t in targets: visit(t)
    return order


def stale(mod):
    o = olean_of(mod)
    if not os.path.exists(o): return True
    t = os.path.getmtime(o)
    if os.path.getmtime(src_of(mod)) > t: return True
    return any(os.path.getmtime(olean_of(d)) > t for d in local_imports(mod))


def run(cmd, log):
    t0 = time.time()
    with open(log, 'w') as f:
        rc = subprocess.call(cmd, cwd=LEANDIR, stdout=f, stderr=subprocess.STDOUT)
    return rc, time.time() - t0


def main():
    args = sys.argv[1:]
    neg = '--neg' in args
    extra, targets, i = [], [], 0
    while i < len(args):
        if args[i] == '--mathlib-lib': extra.append(os.path.abspath(args[i + 1])); i += 2; continue
        if args[i] != '--neg': targets.append(args[i])
        i += 1
    targets = targets or ['Erdos616.Final']
    if not extra:
        extra = sorted(glob.glob(os.path.join(LEANDIR, '.lake', 'packages', '*', '.lake', 'build', 'lib', 'lean')))
    prefix = subprocess.check_output(['lean', '--print-prefix'], text=True).strip()
    tclib = os.path.join(prefix, 'lib', 'lean')
    env_path = ':'.join([LIB] + extra + [tclib])
    os.environ['LEAN_PATH'] = env_path
    for d in (LIB, CDIR, LOGS, os.path.join(ROOT, 'data', 'out')): os.makedirs(d, exist_ok=True)
    report = open(os.path.join(OUT, 'build.log'), 'a')
    def note(s):
        print(s, flush=True); report.write(s + '\n'); report.flush()
    note(f'== build_direct {time.ctime()} targets={targets}')

    mods = closure(targets)
    # 1. checkers -> olean + C -> shared library
    rebuilt = False
    for m in [c for c in CHECKERS if c in mods or True]:
        if not stale(m) and os.path.exists(os.path.join(CDIR, m + '.c')): continue
        os.makedirs(os.path.dirname(olean_of(m)), exist_ok=True)
        rc, dt = run(['lean', '-R', LEANDIR, '-o', olean_of(m), '-c', os.path.join(CDIR, m + '.c'), src_of(m)],
                     os.path.join(LOGS, m + '.out'))
        note(f'{m} exit {rc} {dt:.0f}s'); rebuilt = True
        if rc: sys.exit(f'FAILED {m}: see {LOGS}/{m}.out')
    if rebuilt or not os.path.exists(SO):
        objs = []
        for m in CHECKERS:
            o = os.path.join(CDIR, m + '.o'); objs.append(o)
            subprocess.check_call(['leanc', '-O3', '-DLEAN_EXPORTING', '-fPIC', '-c', '-o', o,
                                   os.path.join(CDIR, m + '.c')])
        subprocess.check_call(['leanc', '-shared', '-o', SO] + objs + ['-L' + tclib, '-lleanshared'])
        note(f'linked {SO}')
    # 2. everything else, in import order
    for m in mods:
        if m in CHECKERS or not stale(m): continue
        os.makedirs(os.path.dirname(olean_of(m)), exist_ok=True)
        rc, dt = run(['lean', '-R', LEANDIR, '--load-dynlib=' + SO, '-o', olean_of(m), src_of(m)],
                     os.path.join(LOGS, m + '.out'))
        note(f'{m} exit {rc} {dt:.0f}s')
        if rc: sys.exit(f'FAILED {m}: see {LOGS}/{m}.out')
    note('BUILD OK')
    if neg:
        rc, dt = run(['lean', '-R', LEANDIR, '--load-dynlib=' + SO, os.path.join(LEANDIR, 'test', 'Neg.lean')],
                     os.path.join(LOGS, 'test.Neg.out'))
        note(f'negative control test/Neg.lean exit {rc} ({"FAILS as required" if rc else "UNEXPECTEDLY SUCCEEDED"})')
        if rc == 0: sys.exit(1)


if __name__ == '__main__':
    main()
