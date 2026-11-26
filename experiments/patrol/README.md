# Continuous litter patrol

Travel takes baseline minutes divided by positive speed. Cleaning takes the
original site duration and removes everything at completion, including arrivals
during the clean. Litter accumulates continuously at the hourly rates below
divided by 60. Every cycle visits all four sites, has four to six stops, and
connects its last stop directly to its first. Lexicographically least rotations
represent cycles. Reversals remain eligible.

An age interval of length Δ contributes the area of a triangle of base Δ and
height λΔ. The sum over completions includes the wraparound interval. Dividing
by lap duration gives the steady-period average. Startup contributes a finite
transient because every site is cleaned within a lap. In ABACD at baseline
speed, A has gaps 7 and 13 minutes. Lean checks those values and checks rotation
agreement at baseline with unit rates. A general Lean proof of the age-integral
identity and rotation invariance remains open.

Python independently integrates the litter age across each leg and checks
agreement with the completion-gap formula. The results file lists every tied
winner, duration, visit counts in ABCD order, longest gap at each busiest site,
and exact average. The two hourly profiles are (3,6,9,9) and (3,6,90,9).

The exact Python interval certificate compares every score with the winning
reference after multiplying by both positive lap durations. With inverse
speed as the variable, each difference is a cubic because lap durations are
affine and gap exposures are quadratic. Four rational evaluations determine
its Bernstein coefficients on [2/3, 5/4]. Positive coefficients certify strict
dominance throughout. All-zero coefficients certify a tie. The only winners
throughout are ACBD and ADBC in the first profile and ACBCDC and ACDCBC in
the second. This certificate is outside Lean.

The simulator starts at a feasible label and runs 512 fresh one-iteration
Grover shots, accepting only strict improvements. It requires no optimum
input. With N = 512 and m improvements, phase inversion and reflection about
the mean give each marked label amplitude (3 − 4m/N)/√N. The simulator samples
the aggregate marked probability and then draws a uniform marked label.
All other outcomes retain the incumbent. The exact failure recurrence groups
equal scores and sums the transition weights to all strictly lower groups.
Its terminal indicator counts every minimum as success. The probability
recurrence is checked by exact arithmetic in Python. A Lean proof connecting
it to the nine-qubit diffuser and stopping rule remains open.

There are 314 usable labels and 198 unused labels, so the index needs nine
qubits. The modeled oracle uses one clean flag and two pattern-controlled
toggles per marked label plus a flag Z per call. Native lowering remains
abstract. The fixed budget makes 512 oracle calls. The simulator precomputes
all 314 scores, then scans 160,768 cached scores across the budget. A direct
rebuild of the Lean compiler scans 512 labels per call and scores the 314
patrols at each rebuild plus the incumbent. Classical enumeration requires
314 patrol scores.

Run from the repository root.

```sh
lake build --wfail
lake env lean experiments/patrol/Patrol.lean
python3 -B experiments/patrol/patrol.py
python3 -B experiments/patrol/certify.py
lake env lean experiments/qsat2/QSAT2.lean
```
