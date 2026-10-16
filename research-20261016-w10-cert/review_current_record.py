"""Compare the current primary-source kernel to the frozen W10 kernel."""
from pathlib import Path
import datetime, hashlib, json, re

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
OLD = ROOT / 'GramDefect20261015/Core.lean'
NEW = OUT / 'current-record-source.txt'

def sha(x):
    return hashlib.sha256(x).hexdigest()

def declaration(source, name):
    # For these named definitions a line starting a declaration ends the body.
    hit = re.search(r'^def ' + re.escape(name) + r'\b', source, re.M)
    assert hit, name
    rest = source[hit.start():]
    end = re.search(r'\n(?:def |theorem |lemma |end(?:\s|$)|namespace )', rest)
    return rest[:end.start() if end else len(rest)].rstrip()

def main():
    if not __debug__: raise RuntimeError('Assertions must remain enabled for this verifier')
    raw = NEW.read_bytes()
    blob_sha1 = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    assert blob_sha1 == 'fe197ef0eeb3109b74d38e6d635b72169a59cc47'
    a, b = OLD.read_text(encoding='utf8'), NEW.read_text(encoding='utf8')
    names = ['cAMn', 'cAM', 'ωAM', 'vAM', 'KfunAM', 'kfunAM', 'wfunAM',
             'K1AM', 'K2AM', 'k1AM', 'k2AM', 'w1AM', 'w2AM', 'RHOC', 'SIGC',
             'Kfun', 'kfun', 'wfun']
    checks = []
    for name in names:
        x, y = declaration(a, name), declaration(b, name)
        checks.append({'declaration': name, 'byte_identical': x == y,
                       'frozen_sha256': sha(x.encode()), 'record_sha256': sha(y.encode())})
    assert all(v['byte_identical'] for v in checks)
    from fractions import Fraction as Q
    parameter = json.loads((ROOT/'research-20261016/spectral-w10-refined-rational.json').read_text())
    kp = Q(parameter['conditional_kappa_exact'])
    kr = Q(34191001116882886388531117129201664, 50760020691785094633026544189453125)
    assert kp > kr
    from decimal import Decimal, localcontext
    with localcontext() as c:
        c.prec = 80
        pct = str(Decimal(kp.numerator) / Decimal(kp.denominator) * 100)
        gain = str(Decimal((kp-kr).numerator) / Decimal((kp-kr).denominator) * 100)
    result = {
        'scope': 'Primary-source identity and exact rational arithmetic only; no analytic W10 floor is certified.',
        'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_commit': '9e6ca6615b9dbfec4a1d722995cff0ffe3abf9bb',
        'source_github_blob_sha1': 'fe197ef0eeb3109b74d38e6d635b72169a59cc47',
        'source_github_blob_verified': True,
        'source_url': 'https://github.com/josusanmartin/riemann/blob/9e6ca6615b9dbfec4a1d722995cff0ffe3abf9bb/submissions/attempt-024/proof/Solution.lean',
        'record_page_url': 'https://www.riemannzeta.fun/submissions/attempt-024',
        'current_record_exact': str(kr), 'conditional_w10_exact': str(kp),
        'conditional_w10_percent': pct, 'conditional_gain_percentage_points': gain,
        'current_record_method': 'Nine-point frame-optimum weights, per-cell anchor variance and range-end tangent anchors.',
        'same_kernel': True, 'kernel_definition_checks': checks,
        'frozen_core_sha256': sha(OLD.read_bytes()), 'record_source_sha256': sha(NEW.read_bytes()),
        'reuse_boundary': 'Analytic values refer to the identical kernel; imported tables and generic proofs still require their own Lean replay under distinct namespaces.',
    }
    (OUT/'current-record-review.json').write_text(json.dumps(result, indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:result[k] for k in ['same_kernel','current_record_exact','conditional_w10_percent','conditional_gain_percentage_points']}))

if __name__ == '__main__': main()
