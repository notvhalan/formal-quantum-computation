/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import QuantumComputation.Algorithms.LitterRouting.Search

/-!
# A fourteen-minute synthetic shift

The travel matrix uses the order depot, A, B, C, D. The two optimum routes
visit C or D, then B, then A. Each returns at minute 14 with 10 minutes of
walking and 261 piece-minutes of litter exposure.
-/

@[expose] public section

open scoped Matrix

namespace LitterRouting.Example

def travelMinutes : Node → Node → ℕ :=
  !![0, 2, 3, 4, 4;
     2, 0, 2, 3, 3;
     3, 2, 0, 2, 2;
     4, 3, 2, 0, 4;
     4, 3, 2, 4, 0]

def synthetic : Instance where
  shift := 14
  travel := travelMinutes
  cleaning := ![1, 2, 1, 1]
  litter := ![3, 6, 9, 9]
  travel_symm := by decide
  travel_diagonal := by decide
  travel_pos := by decide

-- Keep finite table certificates kernel-checked with enough depth for list reduction.
set_option maxRecDepth 8192 in
theorem selected_route : solve synthetic = [2, 1, 0] := by decide

set_option maxRecDepth 8192 in
theorem selected_route_details :
    completionTimes synthetic (solve synthetic) = [(2, 5), (1, 9), (0, 12)] ∧
    elapsed synthetic (solve synthetic) = 14 ∧
    objective synthetic (solve synthetic) = toLex (261, 10) := by decide

theorem longer_walk_details :
    Feasible synthetic [2, 3] ∧ objective synthetic [2, 3] = toLex (261, 12) := by decide

set_option maxRecDepth 8192 in
theorem feasible_label_count : (validLabels synthetic).card = 25 := by decide

set_option maxRecDepth 8192 in
theorem feasible_route_length {route : Route} (hfeasible : Feasible synthetic route) :
    route.length < 4 := by
  have hshort : ∀ label ∈ validLabels synthetic,
      (decode label).any (fun candidate ↦ decide (candidate.length < 4)) = true := by decide
  obtain ⟨label, hdecode⟩ := decode_covers hfeasible.1
  have hvalid := (validLabel_iff synthetic label).mpr ⟨route, hdecode, hfeasible⟩
  have hmember : label ∈ validLabels synthetic :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvalid⟩
  simpa [hdecode] using hshort label hmember

def optima : Finset Label := {31, 37}

theorem optimal_label_31 : OptimalLabel synthetic 31 := by
  refine ⟨solve synthetic, ?_, solve_optimal synthetic⟩
  simpa only [selected_route] using (show decode (31 : Label) = some [2, 1, 0] by decide)

set_option maxRecDepth 8192 in
theorem optimal_labels (label : Label) : OptimalLabel synthetic label ↔ label ∈ optima := by
  have htable :
      ((List.finRange (2 ^ 7)).filter fun other ↦
        decide (encodedScore synthetic other = encodedScore synthetic 31)) = [31, 37] := by
    decide
  calc
    OptimalLabel synthetic label ↔ encodedScore synthetic label = encodedScore synthetic 31 :=
      optimalLabel_iff_score_eq optimal_label_31
    _ ↔ label ∈ (List.finRange (2 ^ 7)).filter
        (fun other ↦ decide (encodedScore synthetic other = encodedScore synthetic 31)) := by
      simp [List.mem_finRange]
    _ ↔ label ∈ optima := by
      rw [htable]
      simp [optima]

def budget : ℕ := 64

theorem initial_label : decode (0 : Label) = some [] := rfl

/-- The probability that the returned label decodes to an optimal route after 64 rounds. -/
theorem success_at_least :
    1 - (15 / 16 : ℝ) ^ budget ≤ successProbability synthetic budget 0 := by
  apply success_bound synthetic optima (by decide) (fun label h ↦ (optimal_labels label).mpr h)
  · rw [feasible_label_count]
    decide
  · exact (validLabel_iff synthetic 0).mpr ⟨[], initial_label, feasible_empty synthetic⟩

end LitterRouting.Example
