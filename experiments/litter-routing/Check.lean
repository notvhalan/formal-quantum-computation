import QuantumComputation.Algorithms.LitterRouting.Example

open LitterRouting LitterRouting.Example

#eval candidates.length
#eval (validLabels synthetic).card
#eval solve synthetic
#eval completionTimes synthetic (solve synthetic)
#eval elapsed synthetic (solve synthetic)
#eval ofLex (objective synthetic (solve synthetic))
#eval ((List.finRange (2 ^ 7)).filter fun label ↦ decide (label ∈ optima)).map fun label ↦
  (label, decode label)

#print axioms solve_optimal
#print axioms decode_covers
#print axioms invalid_worse
#print axioms threshold_marks_iff
#print axioms thresholdOracle_clean
#print axioms outcomeProbability_born
#print axioms optimal_labels
#print axioms success_at_least
