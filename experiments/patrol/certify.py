"""Certify dominance on the closed interval by exact cubic Bernstein coefficients."""
from patrol import F, cycles, evaluate

for rates, reference in [((3,6,9,9),'ACBD'), ((3,6,90,9),'ACBCDC')]:
    rates = [F(r,60) for r in rates]
    ref = tuple('ABCD'.index(c) for c in reference)
    ties = []
    for p in cycles:
        values = []
        for k in range(4):
            # x = inverse speed. Duration is affine and exposure is quadratic in x.
            x = F(2,3) + F(k,3)*(F(5,4)-F(2,3))
            a,t,_ = evaluate(p,1/x,rates)
            b,u,_ = evaluate(ref,1/x,rates)
            values.append((a-b)*t*u)
        lo,y,z,hi = values
        v = 27*y-8*lo-hi
        w = 27*z-lo-8*hi
        coefficients = (lo,(2*v-w)/18,(2*w-v)/18,hi)
        if all(c == 0 for c in coefficients):
            ties.append(p)
        else:
            assert min(coefficients)>0, (p,coefficients)
    print(reference, 'whole-interval ties:', ties)
