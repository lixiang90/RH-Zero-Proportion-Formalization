"""Recompute the sharpened window inputs and final record with exact integers."""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from math import factorial, isqrt

COEFFS = [12310798, -15041681, 3867664, 6489926, -992327, 5580097,
          -6846472, 3781297, -5670353, 3355089, -450523, -218483]

def main():
    d = 10**30
    rn = isqrt(d*d//2)
    r, ru = Q(rn,d), Q(rn+1,d)
    assert 2*r*r <= 1 <= 2*ru*ru
    p = sum(Q((-1)**j, factorial(2*j))*r**(2*j) for j in range(10)) + r**20/Q(2317049531596800000)
    cn = -((-p.numerator*d)//p.denominator)
    cosine = Q(cn,d)
    q = (1-cosine*cosine)*d*d
    sn = isqrt(q.numerator//q.denominator)
    sine = Q(sn,d)
    assert p <= cosine and sine*sine <= 1-cosine*cosine
    assert rn == 707106781186547524400844362104
    assert cn == 760244597075630151253567702555
    assert sn == 649636939080062444129454621098
    pi_upper = Q(314159265358979323847, 10**20)
    pam = sum(Q(c,10**9)**2*(Q(1,2)-1/(4*pi_upper*pi_upper*(j+1)**2)) for j,c in enumerate(COEFFS))
    expression = Q(3,2)-cosine/(2*r*sine)-pam/(2*sine*sine)
    h = Q(672168410564118874775945444401,d)
    assert h <= expression < h+Q(1,d)
    c, b = Q(85638285989,10**13), Q(436674,10**8)
    score = (h-b)/(1-c)
    assert score == Q(39282451209654051457408555553,58319774788300000000000000000)
    old = Q(667801670564118872522651,991436171500000000000000)
    assert score > old
    margin = 1000*331924437510001200-989*335544320000000000
    assert margin == 71105030001200000 and margin > 0
    with localcontext() as ctx:
        ctx.prec = 70
        decimal = lambda f: Decimal(f.numerator)/Decimal(f.denominator)
        print("Exact fraction:", score)
        print("Percent:", 100*decimal(score))
        print("Proportion gain:", decimal(score-old))
    print("Exact arithmetic passed. Analytic and finite premises are proved by Lean.")

if __name__ == "__main__":
    main()
