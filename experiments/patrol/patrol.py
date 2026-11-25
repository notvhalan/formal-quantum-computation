"""Exact completion-gap scoring and independent event-by-event integration."""
from fractions import Fraction as F
from itertools import product
from random import Random

travel = ((0,2,3,3),(2,0,2,2),(3,2,0,4),(3,2,4,0))
clean = (1,2,1,1)
cycles = [p for n in range(4,7) for p in product(range(4), repeat=n)
          if len(set(p)) == 4 and all(p <= p[i:]+p[:i] for i in range(1,n))]

def evaluate(p, speed, rates):
    gaps = []
    legs = [travel[p[i-1]][x]/speed + clean[x] for i,x in enumerate(p)]
    duration = sum(legs)
    ages = []
    for x in range(4):
        gap = 0
        while p[-1-gap] != x:
            gap += 1
        ages.append(sum(legs[len(p)-gap:]))
    area = 0
    for x, dt in zip(p, legs):
        area += sum(r*(a*dt+dt**2/2) for r,a in zip(rates, ages))
        ages = [a+dt for a in ages]
        gaps.append((x,ages[x]))
        ages[x] = 0
    score = sum(rates[x]*g*g/2 for x,g in gaps)/duration
    assert score == area/duration
    return score, duration, [max(g for y,g in gaps if y==x) for x in range(4)]

def exact_failure(scores):
    from collections import Counter
    counts = sorted(Counter(scores).items())
    n = 1 << (len(scores)-1).bit_length()
    denominator = n**3
    failure = [int(i != 0) for i in range(len(counts))]
    for _ in range(512):
        previous_sum = m = 0
        updated = []
        for value, (_, count) in zip(failure, counts):
            weight = (3*n-4*m)**2
            updated.append((denominator-m*weight)*value + weight*previous_sum)
            previous_sum += count*value
            m += count
        failure = updated
    index = next(i for i,(score,_) in enumerate(counts) if score == scores[0])
    return F(failure[index], denominator**512)

def search(scores, rng):
    """One Grover iteration per fresh shot, with exact integer Born weights."""
    n = 1 << (len(scores)-1).bit_length()
    incumbent = 0
    for _ in range(512):
        marked = [i for i,s in enumerate(scores) if s < scores[incumbent]]
        m = len(marked)
        # Each marked amplitude is (3-4m/n)/sqrt(n).
        if rng.randrange(n**3) < m*(3*n-4*m)**2:
            incumbent = rng.choice(marked)
    return incumbent

if __name__ == '__main__':
    print('classes',len(cycles))
    rng = Random(2026)
    for hourly in ((3,6,9,9),(3,6,90,9)):
        for speed in map(F, ('4/5','1','5/4','3/2')):
            rows = [evaluate(p,speed,[F(r,60) for r in hourly]) for p in cycles]
            scores = [row[0] for row in rows]
            best = min(scores)
            result = search(scores,rng)
            print(hourly,speed,'sample optimal',scores[result]==best,'exact-model failure',float(exact_failure(scores)))
            for p,(s,t,g) in zip(cycles,rows):
                if s == best:
                    print(''.join('ABCD'[i] for i in p), t, [p.count(i) for i in range(4)], [g[i] for i,r in enumerate(hourly) if r==max(hourly)], s)
