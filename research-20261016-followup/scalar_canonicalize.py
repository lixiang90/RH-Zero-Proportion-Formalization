"""Postprocess generated basin algebra into explicit canonical nine-term sums.

Run after scalar_generate.py. This avoids relying on vector-lookup simprocs
inside ring normalization. It changes no coefficients or interval hypotheses.
"""
from pathlib import Path
import argparse, hashlib, json, re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--basin', type=int, default=7)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    k = args.basin
    source = ROOT/f'StructuralW10Followup20261016/scalar_FwBasin{k}.lean'
    polynomial = ROOT/'StructuralW10Unconditional20261016/BasinPolynomials.lean'
    text, polytext = source.read_text(encoding='utf8'), polynomial.read_text(encoding='utf8')
    def vector(t, name):
        return re.search(r'^def '+name+r'[^\n]*:= !\[([^\n]*)\]', t, re.M)[1].split(', ')
    bs, ds, anchor = vector(polytext, f'b{k}'), vector(polytext, f'd{k}'), vector(text, f'anchor{k}')
    assert len(bs) == len(ds) == len(anchor) == 9
    nested = '0'
    for i in reversed(range(9)):
        y = f'(g {i}-({anchor[i]}))'
        term = f'(({bs[i]})*{y}+({ds[i]})*{y}^2)'
        nested = f'{term}+({nested})'
    begin = text.index('  rw [sum9]\n', text.index(f'theorem qsum_identity{k}'))
    end = text.index(f'\ntheorem actual_Fw_basin{k}', begin)
    body = f'  rw [sum9]\n  change qsum{k} g = BasinPolynomials.C{k}+({nested})+rest{k} g\n'
    body += f'  norm_num [qsum{k}, rest{k}, evalR,'+','.join(f'q{k}_{i}' for i in range(39))+f',BasinPolynomials.C{k}]\n  ring\n'
    result = text[:begin]+body+text[end:]
    if args.check:
        assert result == text, 'Generated identity is not in canonical form'
    else:
        source.write_text(result, encoding='utf8')
    receipt = {'scope': __doc__, 'basin': k, 'script_sha256': sha(Path(__file__)),
               'source': str(source.relative_to(ROOT)).replace('\\', '/'),
               'source_sha256': sha(source), 'polynomial_sha256': sha(polynomial),
               'unchanged_coefficients': True, 'canonical_identity_check_passed': True,
               'does_not_assert_Lean_verification': True}
    (HERE/f'scalar-canonical-{k}.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'canonical_identity_check_passed': True, 'source_sha256': sha(source)}))


if __name__ == '__main__':
    main()
