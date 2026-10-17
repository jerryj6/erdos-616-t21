import sys, json, glob, random
sys.path.insert(0, '.'); sys.path.insert(0, '../pylib')
import w11e_sym as SY
from w11e_recheck import check, check_gd1
from w11b_recheck import check_generic
rng = random.Random(1); ok = bad = 0
fs = sorted(glob.glob('w11e_certs/c*.json')); rng.shuffle(fs)
for p in fs[:60]:
    rec = json.load(open(p))
    for g in SY.G:
        im = SY.image(rec, g)
        try:
            if im.get('generic') and im['generic']['kind'].startswith('GD1'): check_gd1(im)
            elif im.get('generic'): check_generic(im, rng)
            else: check(im)
            ok += 1
        except AssertionError as e:
            bad += 1
            if bad < 4: print('FAIL', p, e)
print('images', ok, 'ok', bad, 'failed', 'group size', len(SY.G) + 1)
