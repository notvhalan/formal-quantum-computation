import QuantumComputation.Algorithms.LitterRouting.Example

namespace Patrol
open LitterRouting

def words : ℕ → List Route
  | 0 => [[]]
  | n+1 => (words n).flatMap fun tail => (List.finRange 4).map (· :: tail)

def rotations (p : Route) := (List.range p.length).map (fun i => p.rotateLeft i)

def candidates := [4,5,6].flatMap fun n => (words n).filter fun p =>
  (List.finRange 4).all (fun x => p.contains x) &&
    (rotations p).all (fun q => decide (p ≤ q))

theorem mem_words (p : Route) : p ∈ words p.length := by
  induction p with
  | nil => simp [words]
  | cons a t ih =>
    exact List.mem_flatMap.mpr ⟨t, ih, List.mem_map.mpr ⟨a, List.mem_finRange a, rfl⟩⟩

def eligible (p : Route) := (List.finRange 4).all (fun x => p.contains x) &&
  (rotations p).all (fun q => decide (p ≤ q))

theorem family_coverage (p : Route) (n : p.length ∈ [4,5,6]) (h : eligible p) :
    p ∈ candidates :=
  List.mem_flatMap.mpr ⟨p.length, n, List.mem_filter.mpr ⟨mem_words p,h⟩⟩

def leg (s : ℚ) (a b : Site) : ℚ :=
  (Example.synthetic.travel a.succ b.succ : ℚ) / s + Example.synthetic.cleaning b

/-- Start immediately after each completion and walk to the next completion at that site. -/
def gap (s : ℚ) (p : Route) (i : ℕ) : ℚ := Id.run do
  let q := p.rotateLeft i
  let mut previous := (q.headD 0)
  let mut time := 0
  for x in q.tail ++ [(q.headD 0)] do
    time := time + leg s previous x
    if x == (q.headD 0) then break
    previous := x
  return time

def duration (s : ℚ) (p : Route) : ℚ :=
  ((List.range p.length).map fun i => leg s p[i]! p[(i+1)%p.length]!).sum

def score (s : ℚ) (rate : Site → ℚ) (p : Route) : ℚ :=
  ((List.range p.length).map fun i => rate p[i]! * gap s p i ^ 2 / 2).sum / duration s p

-- A B A C D has two distinct A-to-A gaps at baseline speed.
#guard gap 1 [0,1,0,2,3] 0 == 7 && gap 1 [0,1,0,2,3] 2 == 13

def solve (cost : Route → ℚ) : Route :=
  candidates.foldl (fun a b => if cost b < cost a then b else a) [0,1,2,3]

theorem fold_min (cost : Route → ℚ) (xs : List Route) (a : Route) :
    let best := xs.foldl (fun a b => if cost b < cost a then b else a) a
    (best = a ∨ best ∈ xs) ∧ cost best ≤ cost a ∧ ∀ x ∈ xs, cost best ≤ cost x := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    split <;> rename_i h
    · obtain ⟨hm, ha, ht⟩ := ih b
      exact ⟨by tauto, ha.trans h.le, fun x hx => hx.elim (fun e => e ▸ ha) (ht x)⟩
    · obtain ⟨hm, ha, ht⟩ := ih a
      exact ⟨by tauto, ha, fun x hx => hx.elim (fun e => e ▸ ha.trans (le_of_not_gt h)) (ht x)⟩

theorem solve_min (cost : Route → ℚ) (x : Route) (hx : x ∈ candidates) :
    cost (solve cost) ≤ cost x := (fold_min cost candidates _).2.2 x hx

theorem solve_feasible (cost : Route → ℚ) : solve cost ∈ candidates := by
  have seed : ([0,1,2,3] : Route) ∈ candidates :=
    family_coverage _ (by decide) (by decide +kernel)
  rcases (fold_min cost candidates [0,1,2,3]).1 with h | h
  · simpa only [solve, h] using seed
  · exact h

abbrev Label := Fin (2 ^ 9)
def decode (label : Label) := candidates[label.val]?
def encodedScore (cost : Route → ℚ) (label : Label) : WithTop ℚ :=
  match decode label with
  | none => ⊤
  | some p => ↑(cost p)
def threshold (cost : Route → ℚ) (inc label : Label) :=
  decide (encodedScore cost label < encodedScore cost inc)

theorem unused_rejected (c : Route → ℚ) (inc x : Label) (h : decode x = none) :
    threshold c inc x = false := by simp [threshold, encodedScore, h]

theorem marking (c : Route → ℚ) (inc x : Label) (p q : Route)
    (hp : decode inc = some p) (hq : decode x = some q) :
    threshold c inc x = true ↔ c q < c p := by simp [threshold, encodedScore, hp, hq]

#guard candidates.length == 314
#guard candidates.all (fun p => (rotations p).all (fun q =>
  score 1 (fun _ => 1) p == score 1 (fun _ => 1) q))

theorem coverage {p : Route} (h : p ∈ candidates) (fits : candidates.length ≤ 512) :
    ∃ x : Label, decode x = some p := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem h
  exact ⟨⟨i, lt_of_lt_of_le hi fits⟩, by simp [decode, List.getElem?_eq_getElem hi, he]⟩

def thresholdControls (data : (Route → ℚ)) (incumbent : Label) : List Label :=
  let cutoff := encodedScore data incumbent
  (List.finRange (2 ^ 9)).filter fun label ↦ decide (encodedScore data label < cutoff)

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

def computeThreshold (data : (Route → ℚ)) (incumbent : Label) : Equiv.Perm Register :=
  toggleSequence (thresholdControls data incumbent)

theorem computeThreshold_apply (data : (Route → ℚ)) (incumbent label : Label) (flag : Bool) :
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
def thresholdOracle (data : (Route → ℚ)) (incumbent : Label) (state : Register → ℂ) :
    Register → ℂ :=
  let compute := computeThreshold data incumbent
  permute compute.symm (flagZ (permute compute state))

def withCleanFlag (state : Label → ℂ) : Register → ℂ :=
  fun reg ↦ if reg.2 then 0 else state reg.1

def markPhase (data : (Route → ℚ)) (incumbent : Label) (state : Label → ℂ) : Label → ℂ :=
  fun label ↦ if threshold data incumbent label then -state label else state label

/-- Every index amplitude receives the intended phase and the flag returns to zero. -/
theorem thresholdOracle_clean (data : (Route → ℚ)) (incumbent : Label) (state : Label → ℂ) :
    thresholdOracle data incumbent (withCleanFlag state) =
      withCleanFlag (markPhase data incumbent state) := by
  funext register
  rcases register with ⟨label, flag⟩
  simp only [thresholdOracle, permute, flagZ, Equiv.symm_symm, Equiv.symm_apply_apply]
  rw [computeThreshold_apply]
  cases flag <;> cases h : threshold data incumbent label <;> simp [withCleanFlag, markPhase, h]


def hourlyRate (hourly : Site → ℚ) (x : Site) : ℚ := hourly x / 60

#guard [((4 : ℚ)/5), 1, 5/4, 3/2].zip [63/16, 27/8, 117/40, 21/8] |>.all
  (fun (speed, expected) =>
    let cost := score speed (hourlyRate ![3,6,9,9])
    cost (solve cost) == expected)

#guard [((4 : ℚ)/5), 1, 5/4, 3/2].zip [14169/1180, 507/50, 46281/5350, 4367/570] |>.all
  (fun (speed, expected) =>
    let cost := score speed (hourlyRate ![3,6,90,9])
    cost (solve cost) == expected)

#print axioms coverage
#print axioms solve_feasible
#print axioms thresholdOracle_clean
#print axioms solve_min
end Patrol
