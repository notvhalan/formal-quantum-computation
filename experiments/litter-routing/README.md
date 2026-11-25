# Litter routing with one picker

## Assumptions and data

One picker starts at the depot at minute zero and must return by minute 14. The
matrix gives the full walking time of a leg. A visit means a cleaning stop.
The picker can pass through a site during a leg and starts cleaning on arrival
at each selected stop. This gives the earliest finish times for a fixed route.
Initial litter stays on the ground until that site's single clean finishes.
Assume sufficient carrying capacity and fixed litter counts until removal.

All times and litter counts are nonnegative integers. The synthetic walking
times in minutes are symmetric, with positive times between distinct nodes.

| From / to | Depot | A | B | C | D |
| --- | ---: | ---: | ---: | ---: | ---: |
| Depot | 0 | 2 | 3 | 4 | 4 |
| A | 2 | 0 | 2 | 3 | 3 |
| B | 3 | 2 | 0 | 2 | 2 |
| C | 4 | 3 | 2 | 0 | 4 |
| D | 4 | 3 | 2 | 4 | 0 |

| Site | Cleaning minutes | Initial pieces |
| --- | ---: | ---: |
| A | 1 | 3 |
| B | 2 | 6 |
| C | 1 | 9 |
| D | 1 | 9 |

Each quantum round assumes a fresh ideal logical register, exact state evolution,
and computational-basis readout. The reversible circuit uses full-pattern
controlled NOT on seven index bits and a clean flag. For the gate estimates
below, the assumed logical gate set is Toffoli, X, H, and Z. A conjunction ladder
uses five reusable clean ancillas to lower a seven-control NOT.

## Route quality

The classical solver checks all 65 ordered subsets, including the empty route.
The objective compares total piece-minutes first, then walking minutes including
the return. A cleaned site contributes its litter count times its finish minute.
An unvisited site contributes its count times 14.

Lean certifies 25 feasible routes and rules out all four-stop routes. It selects
**Depot → C → B → A → Depot**. The cleaning finishes at minutes 5, 9, and 12,
and the picker returns at minute 14. The score is **(261 piece-minutes,
10 walking minutes)**. The contributions are `9 × 5 + 6 × 9 + 3 × 12 + 9 × 14`.
Starting at D instead of C ties on both costs. The C → D route also has 261
piece-minutes and takes 12 walking minutes. Labels 31 and 37 are exactly the
optimal labels. The Python enumeration independently agrees on both routes,
their timings and costs, and the feasible count.

## Quantum search and probability

Labels 0 through 64 encode the ordered subsets by length and then
lexicographically. Lean proves coverage, uniqueness, and the cutoff at 65.
The 63 unused labels and all infeasible routes receive a score above every
feasible score. The controller starts at label 0, which encodes the empty route.
Each of the 64 rounds prepares the uniform state, calls the threshold phase
oracle once, applies the repository's verified Grover diffuser, measures, and
retains a strict improvement if one was measured. The controller returns the
incumbent at the budget limit.

The threshold compiler tests the current score cutoff for every label and
emits one flag toggle per improvement. The oracle runs this sequence, applies
Z to the flag, then uncomputes. The Lean proof shows the intended phase on
every index amplitude and a clean flag after the sequence. The formal gate
semantics treat the seven-control pattern NOT as a primitive. Its Toffoli/X
lowering and the diffuser's gate decomposition remain at the resource-model level.

For `m` marked labels, the oracle and diffuser produce amplitudes
`(3 − m/32)/√128` on marked labels and `(1 − m/32)/√128` on the others.
Lean derives these amplitudes from the Hadamard preparation, the clean oracle,
and the repository's diffuser formula. It checks the resulting Born weights
sum to one and uses those weights in the adaptive search recurrence.

While the incumbent is nonoptimal, both optimal labels are marked and at most
32 labels are marked. Each optimum therefore has measurement probability at
least 1/32. The probability of reaching either one in that round is at least
1/16, and an optimal incumbent is retained in every later round. The verified
64-round success bound is `1 − (15/16)^64`, about **98.3925%**.

The independent simulator propagates integer-scaled amplitudes, samples the
exact Born weights, and counts either optimal label as success. With seed
2026 it measured **9,997 / 10,000 optimal returns (99.97%)**, split 4,992
and 5,005 across the two labels. Its exact rational transition calculation
gives **99.9889249265%** after rounding. All rates refer to the returned
incumbent after the full budget.

## Computational effort

| Quantity | Value | Basis |
| --- | ---: | --- |
| Candidates examined by the classical solver | 65 | Measured by independent enumeration and verified in Lean |
| Phase-oracle calls per quantum run | 64 | Derived from the fixed budget |
| Label tests to construct the 64 threshold oracles | 8,192 | Derived as 64 scans of 128 labels |
| Candidate records assessed during construction | 4,160 + 64 incumbent assessments | Derived as 65 decoded routes and one incumbent per scan |
| Classical measured-outcome checks | 64 | Derived as one per round |
| Logical index qubits | 7 | Derived from the 128 labels |
| Workspace at the full-pattern gate level | 1 flag | Derived from the reversible circuit |
| Workspace with the clean Toffoli ladder | 1 flag + 5 ancillas | Derived under the assumed gate lowering |
| Mean emitted mark patterns per run | 60.0175 | Measured across the 10,000 simulated runs |
| Mean phase-oracle gates per run | 120.035 pattern NOTs and 64 Z | Derived from the simulated patterns and compute/uncompute |
| Mean phase-oracle gates with lowering | 1,320.385 Toffoli, 999.220 X, and 64 Z | Derived under the assumed gate lowering |

Construction scans the label table at the current incumbent and generates the
pattern gates from the exact scores. The simulator caches the compiled
measurement kernels for speed and records the work associated with each
visited threshold. The construction counts above include rebuilding the
threshold circuit each round. The 64 query calls alone omit that cost.

A seven-control NOT lowers to eleven Toffolis using five conjunction
computations, the target toggle, and five uncomputations. Each negative
control adds two X gates per pattern NOT. Using the same workspace, the
diffuser can use Hadamards around a zero-index phase flip, up to a global
phase. With fresh preparation, this adds 21 H, 28 X, 22 Toffoli, and one Z per
round under that lowering. These are derived logical counts.

## Reproduce

Run from the repository root with elan and Python 3.10 or later. The
`lean-toolchain` file pins Lean 4.35.0.

~~~sh
lake exe cache get
lake build --wfail
scripts/check_all_imported.sh
lake env lean experiments/litter-routing/Check.lean
python3 experiments/litter-routing/simulate.py
~~~

`Check.lean` prints the certified optimum, timings, and ties, then checks
the axiom dependencies of the solver, encoding, oracle, Born probabilities,
and fixed-budget theorem. The checked theorems report the standard Lean
axioms `propext`, `Classical.choice`, and `Quot.sound`.

The multi-target challenge specifications document the marking-oracle
convention. This experiment uses the proved preparation and diffuser in
`QuantumComputation/Algorithms/Grover/Amplitude.lean`.
