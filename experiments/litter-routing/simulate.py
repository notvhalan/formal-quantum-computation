"""Independent enumeration and exact-weight simulation of the 64-round experiment."""

from bisect import bisect_right
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import accumulate, pairwise, permutations
from random import Random
from statistics import mean


SHIFT = 14
TRAVEL = (
    (0, 2, 3, 4, 4),
    (2, 0, 2, 3, 3),
    (3, 2, 0, 2, 2),
    (4, 3, 2, 0, 4),
    (4, 3, 2, 4, 0),
)
CLEAN = (1, 2, 1, 1)
LITTER = (3, 6, 9, 9)
N = 2**7
ROUNDS = 64
TRIALS = 10_000
SEED = 2026
DENOMINATOR = N**3


@dataclass(frozen=True)
class Tour:
    route: tuple[int, ...]
    finishes: tuple[int, ...]
    returned: int
    score: tuple[int, int]


def evaluate(route):
    nodes = (0, *(site + 1 for site in route), 0)
    legs = tuple(TRAVEL[a][b] for a, b in pairwise(nodes))
    finishes = tuple(accumulate(leg + CLEAN[site] for site, leg in zip(route, legs)))
    finish_by_site = dict(zip(route, finishes))
    piece_minutes = sum(
        count * finish_by_site.get(site, SHIFT) for site, count in enumerate(LITTER)
    )
    returned = (finishes[-1] if finishes else 0) + legs[-1]
    return Tour(route, finishes, returned, (piece_minutes, sum(legs)))


@dataclass(frozen=True)
class Kernel:
    cumulative: list[int]
    retained_labels: list[int]
    transition_weights: dict[int, int]
    marks: int
    zero_controls: int


def compile_round(scores, incumbent):
    cutoff = scores[incumbent]
    assert cutoff is not None
    controls = [x for x, score in enumerate(scores) if score is not None and score < cutoff]

    # Work in units of the initial uniform amplitude. Compute the flag, apply Z,
    # then undo the full-pattern NOTs. Each flag amplitude at one must vanish.
    flag_zero, flag_one = [1] * N, [0] * N
    for x in controls:
        flag_zero[x], flag_one[x] = flag_one[x], flag_zero[x]
    flag_one = [-amplitude for amplitude in flag_one]
    for x in reversed(controls):
        flag_zero[x], flag_one[x] = flag_one[x], flag_zero[x]
    assert not any(flag_one)

    # The diffuser reflects amplitudes about their mean. Multiply by N before
    # squaring to avoid floating-point arithmetic in the Born probabilities.
    twice_sum = 2 * sum(flag_zero)
    weights = [(twice_sum - N * amplitude) ** 2 for amplitude in flag_zero]
    assert sum(weights) == DENOMINATOR

    marked = set(controls)
    retained = [x if x in marked else incumbent for x in range(N)]
    transitions = Counter()
    for label, weight in zip(retained, weights):
        transitions[label] += weight
    return Kernel(
        list(accumulate(weights)), retained, dict(transitions), len(controls),
        sum(7 - x.bit_count() for x in controls),
    )


def exact_success(kernels, optima):
    # After r rounds, each entry is a numerator over DENOMINATOR**r.
    numerators = {x: int(x in optima) for x in kernels}
    for _ in range(ROUNDS):
        numerators = {
            x: sum(weight * numerators[y] for y, weight in kernel.transition_weights.items())
            for x, kernel in kernels.items()
        }
    return Fraction(numerators[0], DENOMINATOR**ROUNDS)


def sample(kernels):
    rng = Random(SEED)
    results, marks_per_run, zeros_per_run = Counter(), [], []
    for _ in range(TRIALS):
        incumbent, marks, zeros = 0, 0, 0
        for _ in range(ROUNDS):
            kernel = kernels[incumbent]
            measured = bisect_right(kernel.cumulative, rng.randrange(DENOMINATOR))
            incumbent = kernel.retained_labels[measured]
            marks += kernel.marks
            zeros += kernel.zero_controls
        results[incumbent] += 1
        marks_per_run.append(marks)
        zeros_per_run.append(zeros)
    return results, marks_per_run, zeros_per_run


def main():
    tours = [
        evaluate(route)
        for length in range(len(LITTER) + 1)
        for route in permutations(range(len(LITTER)), length)
    ]
    feasible = [x for x, tour in enumerate(tours) if tour.returned <= SHIFT]
    optimum = min(tours[x].score for x in feasible)
    optima = tuple(x for x in feasible if tours[x].score == optimum)

    # Cross-check the results certified in Example.lean.
    assert len(tours) == 65 and len(feasible) == 25
    assert max(len(tours[x].route) for x in feasible) == 3
    assert optima == (31, 37) and optimum == (261, 10)
    assert tours[31] == Tour((2, 1, 0), (5, 9, 12), 14, (261, 10))
    assert tours[37] == Tour((3, 1, 0), (5, 9, 12), 14, (261, 10))

    eligible = set(feasible)
    scores = [tour.score if x in eligible else None for x, tour in enumerate(tours)]
    scores.extend([None] * (N - len(scores)))
    # Cache each kernel for simulation. Every simulated round still samples its
    # measured outcome and contributes its own query and gate counts.
    kernels = {x: compile_round(scores, x) for x in feasible}
    results, marks, zeros = sample(kernels)
    successes = sum(results[x] for x in optima)
    guarantee = 1 - Fraction(15, 16) ** ROUNDS
    exact = exact_success(kernels, optima)
    assert exact >= guarantee

    print(f"Measured enumeration: {len(tours)} candidates, {len(feasible)} feasible")
    for label in optima:
        print(f"Optimal label {label}: {tours[label]}")
    print(f"Measured simulation (seed {SEED}): {successes}/{TRIALS} optimal "
          f"({successes / TRIALS:.2%}), counts {[results[x] for x in optima]}")
    print(f"Derived exact-model success: {float(exact):.10%}")
    print(f"Lean success lower bound: {float(guarantee):.10%}")
    print(f"Derived phase queries per trial: {ROUNDS}")
    print(f"Measured compiler marks per trial (min / mean / max): "
          f"{min(marks)} / {mean(marks):.4f} / {max(marks)}")
    print(f"Derived mean oracle gates from simulated runs: "
          f"{2 * mean(marks):.4f} pattern-controlled NOT, {ROUNDS} Z")
    print(f"Derived mean oracle gates with positive controls and clean ladder: "
          f"{22 * mean(marks):.4f} Toffoli, {4 * mean(zeros):.4f} X, {ROUNDS} Z")


if __name__ == "__main__":
    main()
