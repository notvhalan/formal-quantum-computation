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

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.WithBot
public import QuantumComputation.Algorithms.LitterRouting.Model

/-!
# A reversible threshold oracle

The compiler emits one controlled NOT per improving label. Each NOT targets the flag
and is controlled on the full seven-bit label pattern. The oracle computes the flag,
applies a Z to it, and reverses the compute sequence. Controlled NOT with a seven-bit
pattern is the primitive gate of this model.
-/

@[expose] public section

namespace LitterRouting

/-- The index register consists of seven logical qubits. -/
abbrev Label := Fin (2 ^ 7)

/-- Labels 0 through 64 code the ordered subsets. The other labels are unused. -/
def decode (label : Label) : Option Route :=
  candidates[label.val]?

theorem decode_covers {route : Route} (distinct : route.Nodup) :
    ∃ label, decode label = some route := by
  obtain ⟨index, bound, hget⟩ := List.getElem_of_mem (mem_candidates distinct)
  have fits : index < 2 ^ 7 := lt_trans bound (by rw [candidates_length]; decide)
  exact ⟨⟨index, fits⟩, by rw [decode, List.getElem?_eq_getElem bound, hget]⟩

theorem decode_unused (label : Label) : decode label = none ↔ 65 ≤ label.val := by
  simp [decode, candidates_length]

/-- Unused and infeasible labels have a score strictly above any feasible score. -/
def encodedScore (data : Instance) (label : Label) : WithTop Score :=
  match decode label with
  | none => ⊤
  | some route => if Feasible data route then ↑(objective data route) else ⊤

def ValidLabel (data : Instance) (label : Label) : Prop :=
  encodedScore data label ≠ ⊤

instance (data : Instance) (label : Label) : Decidable (ValidLabel data label) := by
  unfold ValidLabel
  infer_instance

theorem validLabel_iff (data : Instance) (label : Label) :
    ValidLabel data label ↔ ∃ route, decode label = some route ∧ Feasible data route := by
  cases h : decode label with
  | none => simp [ValidLabel, encodedScore, h]
  | some route =>
    by_cases hf : Feasible data route <;> simp [ValidLabel, encodedScore, h, hf]

theorem encodedScore_of_feasible {data : Instance} {label : Label} {route : Route}
    (hdecode : decode label = some route) (hf : Feasible data route) :
    encodedScore data label = (objective data route : WithTop Score) := by
  simp [encodedScore, hdecode, hf]

theorem invalid_worse {data : Instance} {valid invalid : Label}
    (hvalid : ValidLabel data valid) (hinvalid : ¬ ValidLabel data invalid) :
    encodedScore data valid < encodedScore data invalid := by
  have hinvalid' : encodedScore data invalid = ⊤ := not_ne_iff.mp hinvalid
  rwa [hinvalid', lt_top_iff_ne_top]

def threshold (data : Instance) (incumbent label : Label) : Bool :=
  decide (encodedScore data label < encodedScore data incumbent)

theorem threshold_marks_iff {data : Instance} {incumbent label : Label} {best : Route}
    (hdecode : decode incumbent = some best) (hf : Feasible data best) :
    threshold data incumbent label = true ↔
      ∃ route, decode label = some route ∧ Feasible data route ∧
        objective data route < objective data best := by
  cases h : decode label with
  | none => simp [threshold, encodedScore, h, hdecode, hf]
  | some route =>
    by_cases hr : Feasible data route <;> simp [threshold, encodedScore, h, hdecode, hf, hr]

/-- The targets of the full-pattern controlled NOT gates in the compute sequence. -/
def thresholdControls (data : Instance) (incumbent : Label) : List Label :=
  let cutoff := encodedScore data incumbent
  (List.finRange (2 ^ 7)).filter fun label ↦ decide (encodedScore data label < cutoff)

abbrev Register := Label × Bool

/-- Toggle the flag exactly on the given index basis state. -/
def patternNot (pattern : Label) : Equiv.Perm Register where
  toFun reg := (reg.1, if reg.1 = pattern then !reg.2 else reg.2)
  invFun reg := (reg.1, if reg.1 = pattern then !reg.2 else reg.2)
  left_inv := by
    rintro ⟨label, flag⟩
    by_cases h : label = pattern <;> simp [h]
  right_inv := by
    rintro ⟨label, flag⟩
    by_cases h : label = pattern <;> simp [h]

def toggleSequence : List Label → Equiv.Perm Register
  | [] => Equiv.refl _
  | pattern :: rest => (patternNot pattern).trans (toggleSequence rest)

private theorem toggleSequence_apply (controls : List Label) (distinct : controls.Nodup)
    (label : Label) (flag : Bool) :
    toggleSequence controls (label, flag) =
      (label, if label ∈ controls then !flag else flag) := by
  induction controls generalizing flag with
  | nil => simp [toggleSequence]
  | cons pattern rest ih =>
    rw [toggleSequence, Equiv.trans_apply]
    change toggleSequence rest (label, if label = pattern then !flag else flag) = _
    rw [ih distinct.of_cons]
    by_cases h : label = pattern
    · subst pattern
      simp [(List.nodup_cons.mp distinct).1]
    · simp [h]

def computeThreshold (data : Instance) (incumbent : Label) : Equiv.Perm Register :=
  toggleSequence (thresholdControls data incumbent)

theorem computeThreshold_apply (data : Instance) (incumbent label : Label) (flag : Bool) :
    computeThreshold data incumbent (label, flag) =
      (label, if threshold data incumbent label then !flag else flag) := by
  have distinct : (thresholdControls data incumbent).Nodup :=
    (List.nodup_finRange _).filter _
  rw [computeThreshold, toggleSequence_apply _ distinct]
  simp [thresholdControls, threshold]

def permute (gate : Equiv.Perm Register) (state : Register → ℂ) :
    Register → ℂ :=
  fun reg ↦ state (gate.symm reg)

def flagZ (state : Register → ℂ) : Register → ℂ :=
  fun reg ↦ if reg.2 then -state reg else state reg

/-- Compute, apply Z to the flag, and uncompute on the joint amplitude vector. -/
def thresholdOracle (data : Instance) (incumbent : Label) (state : Register → ℂ) :
    Register → ℂ :=
  let compute := computeThreshold data incumbent
  permute compute.symm (flagZ (permute compute state))

def withCleanFlag (state : Label → ℂ) : Register → ℂ :=
  fun reg ↦ if reg.2 then 0 else state reg.1

def markPhase (data : Instance) (incumbent : Label) (state : Label → ℂ) : Label → ℂ :=
  fun label ↦ if threshold data incumbent label then -state label else state label

/-- Every index amplitude receives the intended phase and the flag returns to zero. -/
theorem thresholdOracle_clean (data : Instance) (incumbent : Label) (state : Label → ℂ) :
    thresholdOracle data incumbent (withCleanFlag state) =
      withCleanFlag (markPhase data incumbent state) := by
  funext register
  rcases register with ⟨label, flag⟩
  simp only [thresholdOracle, permute, flagZ, Equiv.symm_symm, Equiv.symm_apply_apply]
  rw [computeThreshold_apply]
  cases flag <;> cases h : threshold data incumbent label <;> simp [withCleanFlag, markPhase, h]

end LitterRouting
