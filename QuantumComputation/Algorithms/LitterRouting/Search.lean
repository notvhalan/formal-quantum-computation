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

public import QuantumComputation.Algorithms.Grover.Amplitude
public import QuantumComputation.Algorithms.LitterRouting.Oracle

/-!
# Fixed-budget Grover minimum finding

In each round, prepare the uniform index state with a clean flag, run the current
threshold oracle and the Grover diffuser, and measure the index. Keep the measured
label if it improves the incumbent. The returned label is the incumbent when the
budget expires. The register is prepared afresh after every measurement.
-/

@[expose] public section

open scoped BigOperators Matrix Real

namespace LitterRouting

def validLabels (data : Instance) : Finset Label :=
  Finset.univ.filter (ValidLabel data)

def markedLabels (data : Instance) (incumbent : Label) : Finset Label :=
  Finset.univ.filter (fun label ↦ threshold data incumbent label = true)

@[simp]
theorem mem_markedLabels {data : Instance} {incumbent label : Label} :
    label ∈ markedLabels data incumbent ↔ threshold data incumbent label = true := by
  simp [markedLabels]

private theorem marked_valid {data : Instance} {incumbent label : Label}
    (marked : threshold data incumbent label = true) : ValidLabel data label :=
  ne_top_of_lt (show encodedScore data label < encodedScore data incumbent from
    of_decide_eq_true marked)

theorem markedLabels_subset_validLabels (data : Instance) (incumbent : Label) :
    markedLabels data incumbent ⊆ validLabels data := by
  intro label hmark
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, marked_valid (mem_markedLabels.mp hmark)⟩

private theorem sum_by_membership {R : Type*} [AddCommMonoid R] (marked : Finset Label)
    (yes no : R) :
    (∑ label : Label, if label ∈ marked then yes else no) =
      marked.card • yes + markedᶜ.card • no := by
  simp [Finset.sum_ite, Finset.filter_notMem_eq_sdiff, Finset.compl_eq_univ_sdiff]

noncomputable def uniformIndex : Label → ℂ :=
  fun label ↦ hadamardMatrix 7 label 0

theorem uniformIndex_apply (label : Label) :
    uniformIndex label = ((1 / √(128 : ℝ) : ℝ) : ℂ) := by
  change Grover.groverMatrix (n := 7) 0 0 label 0 = _
  rw [Grover.groverMatrix_apply_zero]
  norm_num [Grover.groverState]

/-- One measured round, before measuring the index and after the flag has been cleared. -/
noncomputable def roundState (data : Instance) (incumbent : Label) : Label → ℂ :=
  Grover.diffuserMatrix (n := 7) *ᵥ
    fun label ↦ thresholdOracle data incumbent (withCleanFlag uniformIndex) (label, false)

/-- The index amplitude divided by its initial amplitude. -/
noncomputable def amplitudeFactor (marked : Finset Label) (label : Label) : ℝ :=
  if label ∈ marked then 3 - (marked.card : ℝ) / 32 else 1 - (marked.card : ℝ) / 32

theorem roundState_amplitude (data : Instance) (incumbent label : Label) :
    roundState data incumbent label =
      (amplitudeFactor (markedLabels data incumbent) label : ℂ) * uniformIndex label := by
  have hphase :
      (fun x ↦ thresholdOracle data incumbent (withCleanFlag uniformIndex) (x, false)) =
      (fun x ↦ if x ∈ markedLabels data incumbent then -uniformIndex x else uniformIndex x) := by
    rw [thresholdOracle_clean]
    funext x
    simp [withCleanFlag, markPhase]
  rw [roundState, hphase, Grover.diffuserMatrix_mulVec]
  simp only [uniformIndex_apply]
  rw [sum_by_membership, Finset.card_compl]
  have capacity : (markedLabels data incumbent).card ≤ 2 ^ 7 := by
    simpa only [Fintype.card_fin] using (markedLabels data incumbent).card_le_univ
  simp only [nsmul_eq_mul, Fintype.card_fin, amplitudeFactor]
  rw [Nat.cast_sub capacity]
  split_ifs <;> push_cast <;> ring

/-- Exact probability of measuring the label after one Grover iteration. -/
noncomputable def outcomeProbability (marked : Finset Label) (label : Label) : ℝ :=
  amplitudeFactor marked label ^ 2 / 128

theorem outcomeProbability_born (data : Instance) (incumbent label : Label) :
    Complex.normSq (roundState data incumbent label) =
      outcomeProbability (markedLabels data incumbent) label := by
  rw [roundState_amplitude, Complex.normSq_mul]
  simp only [uniformIndex_apply, Complex.normSq_ofReal, outcomeProbability]
  rw [← pow_two (1 / √(128 : ℝ)), div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  ring

theorem outcomeProbability_nonneg (marked : Finset Label) (label : Label) :
    0 ≤ outcomeProbability marked label := by
  unfold outcomeProbability
  positivity

theorem outcomeProbability_sum (marked : Finset Label) :
    ∑ label : Label, outcomeProbability marked label = 1 := by
  have hfactor :
      (fun x ↦ outcomeProbability marked x) =
      (fun x ↦ if x ∈ marked then (3 - (marked.card : ℝ) / 32) ^ 2 / 128
        else (1 - (marked.card : ℝ) / 32) ^ 2 / 128) := by
    funext x
    by_cases hx : x ∈ marked <;> simp [outcomeProbability, amplitudeFactor, hx]
  rw [hfactor, sum_by_membership, Finset.card_compl]
  have capacity : marked.card ≤ 2 ^ 7 := by
    simpa only [Fintype.card_fin] using marked.card_le_univ
  simp only [nsmul_eq_mul, Fintype.card_fin]
  rw [Nat.cast_sub capacity]
  ring

theorem marked_outcome_probability {marked : Finset Label} (bound : marked.card ≤ 32)
    {label : Label} (hlabel : label ∈ marked) : 1 / 32 ≤ outcomeProbability marked label := by
  have hcard : (marked.card : ℝ) ≤ 32 := by exact_mod_cast bound
  unfold outcomeProbability amplitudeFactor
  rw [ite_eq_left hlabel]
  nlinarith [sq_nonneg ((3 - (marked.card : ℝ) / 32) - 2)]

def OptimalLabel (data : Instance) (label : Label) : Prop :=
  ∃ route, decode label = some route ∧ IsOptimal data route

theorem optimalLabel_iff (data : Instance) (label : Label) :
    OptimalLabel data label ↔
      ValidLabel data label ∧ ∀ other, encodedScore data label ≤ encodedScore data other := by
  constructor
  · rintro ⟨route, hdecode, hopt⟩
    have hvalid := (validLabel_iff data label).mpr ⟨route, hdecode, hopt.1⟩
    refine ⟨hvalid, fun other ↦ ?_⟩
    by_cases hother : ValidLabel data other
    · obtain ⟨alt, hdecode', hfeasible⟩ := (validLabel_iff data other).mp hother
      rw [encodedScore_of_feasible hdecode hopt.1, encodedScore_of_feasible hdecode' hfeasible,
        WithTop.coe_le_coe]
      exact hopt.2 alt hfeasible
    · exact (invalid_worse hvalid hother).le
  · rintro ⟨hvalid, hmin⟩
    obtain ⟨route, hdecode, hfeasible⟩ := (validLabel_iff data label).mp hvalid
    refine ⟨route, hdecode, hfeasible, fun alt hAlt ↦ ?_⟩
    obtain ⟨other, hdecode'⟩ := decode_covers hAlt.1
    have h := hmin other
    rwa [encodedScore_of_feasible hdecode hfeasible, encodedScore_of_feasible hdecode' hAlt,
      WithTop.coe_le_coe] at h

theorem optimalLabel_iff_score_eq {data : Instance} {known label : Label}
    (optimal : OptimalLabel data known) :
    OptimalLabel data label ↔ encodedScore data label = encodedScore data known := by
  obtain ⟨hvalid, hmin⟩ := (optimalLabel_iff data known).mp optimal
  constructor
  · intro h
    exact le_antisymm (((optimalLabel_iff data label).mp h).2 known) (hmin label)
  · intro h
    refine (optimalLabel_iff data label).mpr ⟨?_, ?_⟩
    · simpa only [ValidLabel, h] using hvalid
    · intro other
      rw [h]
      exact hmin other

/-- Apply the classical incumbent update after a measured outcome. -/
def advance (data : Instance) (incumbent measured : Label) : Label :=
  if threshold data incumbent measured then measured else incumbent

theorem valid_advance {data : Instance} {incumbent : Label} (measured : Label)
    (hvalid : ValidLabel data incumbent) : ValidLabel data (advance data incumbent measured) := by
  unfold advance
  split
  · rename_i mark
    exact marked_valid mark
  · exact hvalid

theorem advance_optimal {data : Instance} {incumbent : Label} (measured : Label)
    (hopt : OptimalLabel data incumbent) : advance data incumbent measured = incumbent := by
  have hmin := ((optimalLabel_iff data incumbent).mp hopt).2 measured
  simp [advance, threshold, not_lt_of_ge hmin]

theorem optimum_marked {data : Instance} {incumbent optimum : Label}
    (hopt : OptimalLabel data optimum) (hvalid : ValidLabel data incumbent)
    (hnonopt : ¬ OptimalLabel data incumbent) : optimum ∈ markedLabels data incumbent := by
  have hmin := ((optimalLabel_iff data optimum).mp hopt).2
  have hlt : encodedScore data optimum < encodedScore data incumbent := by
    apply lt_of_not_ge
    intro hle
    exact hnonopt ((optimalLabel_iff data incumbent).mpr
      ⟨hvalid, fun other ↦ hle.trans (hmin other)⟩)
  simp [threshold, hlt]

open Classical in
/-- Probability of returning a nonoptimal incumbent after the remaining rounds. -/
noncomputable def failureProbability (data : Instance) : ℕ → Label → ℝ
  | 0, incumbent => if OptimalLabel data incumbent then 0 else 1
  | rounds + 1, incumbent =>
    ∑ measured : Label, Complex.normSq (roundState data incumbent measured) *
      failureProbability data rounds (advance data incumbent measured)

noncomputable def successProbability (data : Instance) (rounds : ℕ) (incumbent : Label) : ℝ :=
  1 - failureProbability data rounds incumbent

theorem failure_of_optimal {data : Instance} {incumbent : Label} (rounds : ℕ)
    (hopt : OptimalLabel data incumbent) : failureProbability data rounds incumbent = 0 := by
  induction rounds with
  | zero => simp [failureProbability, hopt]
  | succ rounds ih => simp [failureProbability, advance_optimal _ hopt, ih]

/-- For at most 32 feasible labels and two certified optimum labels, every round at a
nonoptimal incumbent has at least a one-in-sixteen chance of measuring an optimum. -/
theorem failure_bound (data : Instance) (optima : Finset Label) (two : optima.card = 2)
    (sound : ∀ label ∈ optima, OptimalLabel data label) (small : (validLabels data).card ≤ 32)
    (rounds : ℕ) (incumbent : Label) (hvalid : ValidLabel data incumbent) :
    failureProbability data rounds incumbent ≤ (15 / 16 : ℝ) ^ rounds := by
  induction rounds generalizing incumbent with
  | zero =>
    simp only [failureProbability, pow_zero]
    split <;> norm_num
  | succ rounds ih =>
    by_cases hopt : OptimalLabel data incumbent
    · rw [failure_of_optimal (rounds + 1) hopt]
      positivity
    let marked := markedLabels data incumbent
    let weight := outcomeProbability marked
    let tail := fun label ↦ failureProbability data rounds (advance data incumbent label)
    have hsize : marked.card ≤ 32 :=
      (Finset.card_le_card (markedLabels_subset_validLabels data incumbent)).trans small
    have hmarked : ∀ label ∈ optima, label ∈ marked :=
      fun label h ↦ optimum_marked (sound label h) hvalid hopt
    have hhit : (1 / 16 : ℝ) ≤ ∑ label ∈ optima, weight label := by
      calc
        (1 / 16 : ℝ) = ∑ _label ∈ optima, (1 / 32 : ℝ) := by norm_num [two]
        _ ≤ _ := Finset.sum_le_sum
          (fun label h ↦ marked_outcome_probability hsize (hmarked label h))
    have hzero : ∑ label ∈ optima, weight label * tail label = 0 := by
      apply Finset.sum_eq_zero
      intro label h
      have hmark := mem_markedLabels.mp (hmarked label h)
      simp [tail, advance, hmark, failure_of_optimal rounds (sound label h)]
    have hrest : ∑ label ∈ optimaᶜ, weight label ≤ 15 / 16 := by
      have hsum := Finset.sum_compl_add_sum optima weight
      have htotal : ∑ label : Label, weight label = 1 := outcomeProbability_sum marked
      linarith
    calc
      failureProbability data (rounds + 1) incumbent =
          ∑ label ∈ optimaᶜ, weight label * tail label := by
        have hsplit := Finset.sum_compl_add_sum optima (fun label ↦ weight label * tail label)
        rw [hzero, add_zero] at hsplit
        simp only [failureProbability, outcomeProbability_born]
        exact hsplit.symm
      _ ≤ ∑ label ∈ optimaᶜ, weight label * (15 / 16 : ℝ) ^ rounds :=
        Finset.sum_le_sum (fun label _ ↦ mul_le_mul_of_nonneg_left
          (ih _ (valid_advance label hvalid)) (outcomeProbability_nonneg _ _))
      _ = (∑ label ∈ optimaᶜ, weight label) * (15 / 16 : ℝ) ^ rounds := by
        rw [Finset.sum_mul]
      _ ≤ (15 / 16 : ℝ) ^ (rounds + 1) := by
        rw [pow_succ' (15 / 16 : ℝ) rounds]
        exact mul_le_mul_of_nonneg_right hrest (by positivity)

theorem success_bound (data : Instance) (optima : Finset Label) (two : optima.card = 2)
    (sound : ∀ label ∈ optima, OptimalLabel data label) (small : (validLabels data).card ≤ 32)
    (rounds : ℕ) (incumbent : Label) (hvalid : ValidLabel data incumbent) :
    1 - (15 / 16 : ℝ) ^ rounds ≤ successProbability data rounds incumbent :=
  sub_le_sub_left (failure_bound data optima two sound small rounds incumbent hvalid) 1

end LitterRouting
