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

public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Litter routing during one shift

One picker starts at the depot at minute zero, travels along the prescribed legs, and
cleans each selected site on arrival. Walking includes the return leg. Litter at a site
remains until cleaning finishes or until the shift ends.
-/

@[expose] public section

namespace LitterRouting

/-- The four cleanable sites. -/
abbrev Site := Fin 4

/-- Node zero is the depot. Sites are numbered one through four as travel nodes. -/
abbrev Node := Fin 5

/-- A route lists the sites in cleaning order. -/
abbrev Route := List Site

/-- The ordered pair of piece-minutes and walking minutes, compared lexicographically. -/
abbrev Score := ℕ ×ₗ ℕ

def depot : Node := 0

def travelNode (site : Site) : Node := site.succ

/-- Times are whole minutes. Travel times specify complete legs between the given nodes. -/
structure Instance where
  shift : ℕ
  travel : Node → Node → ℕ
  cleaning : Site → ℕ
  litter : Site → ℕ
  travel_symm : ∀ a b, travel a b = travel b a
  travel_diagonal : ∀ a, travel a a = 0
  travel_pos : ∀ a b, a ≠ b → 0 < travel a b

def completionsFrom (data : Instance) (atNode : Node) (minute : ℕ) :
    Route → List (Site × ℕ)
  | [] => []
  | site :: rest =>
    let finish := minute + data.travel atNode (travelNode site) + data.cleaning site
    (site, finish) :: completionsFrom data (travelNode site) finish rest

/-- The visited sites and their cleaning completion minutes. -/
def completionTimes (data : Instance) (route : Route) : List (Site × ℕ) :=
  completionsFrom data depot 0 route

def walkFrom (data : Instance) (atNode : Node) : Route → ℕ
  | [] => data.travel atNode depot
  | site :: rest =>
    data.travel atNode (travelNode site) + walkFrom data (travelNode site) rest

/-- The time spent walking, including the return to the depot. -/
def walkingTime (data : Instance) (route : Route) : ℕ :=
  walkFrom data depot route

/-- The time at which the picker is back at the depot. -/
def elapsed (data : Instance) (route : Route) : ℕ :=
  walkingTime data route + (route.map data.cleaning).sum

/-- Feasibility requires distinct sites and completion of the return within the shift. -/
def Feasible (data : Instance) (route : Route) : Prop :=
  route.Nodup ∧ elapsed data route ≤ data.shift

instance (data : Instance) (route : Route) : Decidable (Feasible data route) := by
  unfold Feasible
  infer_instance

/-- Total piece-minutes, charging unvisited sites for the full shift. -/
def litterCost (data : Instance) (route : Route) : ℕ :=
  let times := completionTimes data route
  ((List.finRange 4).map fun site ↦
    let finish := ((times.find? fun visit ↦ visit.1 == site).map Prod.snd).getD data.shift
    data.litter site * finish).sum

def objective (data : Instance) (route : Route) : Score :=
  toLex (litterCost data route, walkingTime data route)

/-- Optimal routes are feasible and have a lexicographically minimal score, allowing ties. -/
def IsOptimal (data : Instance) (route : Route) : Prop :=
  Feasible data route ∧ ∀ other, Feasible data other → objective data route ≤ objective data other

theorem feasible_empty (data : Instance) : Feasible data [] := by
  simp [Feasible, elapsed, walkingTime, walkFrom, data.travel_diagonal]

def routesOfLength : ℕ → List Site → List Route
  | 0, _ => [[]]
  | length + 1, sites =>
    sites.flatMap fun site ↦ (routesOfLength length (sites.erase site)).map (site :: ·)

/-- Ordered subsets, first by length and then lexicographically by site number. -/
def candidates : List Route :=
  (List.range 5).flatMap fun length ↦ routesOfLength length (List.finRange 4)

private theorem mem_routesOfLength {route : Route} {sites : List Site} (distinct : route.Nodup)
    (inSites : ∀ site ∈ route, site ∈ sites) :
    route ∈ routesOfLength route.length sites := by
  induction route generalizing sites with
  | nil => simp [routesOfLength]
  | cons site rest ih =>
    simp only [List.length_cons, routesOfLength, List.mem_flatMap, List.mem_map]
    refine ⟨site, inSites site (by simp), rest, ih distinct.of_cons ?_, rfl⟩
    intro other hmem
    have hne : other ≠ site := fun h ↦ (List.nodup_cons.mp distinct).1 (h ▸ hmem)
    exact (List.mem_erase_of_ne hne).mpr (inSites other (List.mem_cons_of_mem _ hmem))

theorem mem_candidates {route : Route} (distinct : route.Nodup) : route ∈ candidates := by
  have lengthBound : route.length < 5 := by
    simpa only [Fintype.card_fin] using Nat.lt_succ_of_le distinct.length_le_card
  exact List.mem_flatMap.mpr
    ⟨route.length, List.mem_range.mpr lengthBound,
      mem_routesOfLength distinct (fun site _ ↦ List.mem_finRange site)⟩

theorem candidates_length : candidates.length = 65 := rfl

theorem candidates_nodup : candidates.Nodup := by decide

theorem mem_candidates_iff {route : Route} : route ∈ candidates ↔ route.Nodup := by
  have h : candidates.all (fun candidate ↦ decide candidate.Nodup) = true := by decide
  exact ⟨fun hmem ↦ of_decide_eq_true (List.all_eq_true.mp h route hmem), mem_candidates⟩

def prefer (data : Instance) (incumbent candidate : Route) : Route :=
  if Feasible data candidate ∧ objective data candidate < objective data incumbent
  then candidate else incumbent

private theorem prefer_spec (data : Instance) (incumbent candidate : Route)
    (hi : Feasible data incumbent) :
    Feasible data (prefer data incumbent candidate) ∧
      objective data (prefer data incumbent candidate) ≤ objective data incumbent ∧
      (Feasible data candidate →
        objective data (prefer data incumbent candidate) ≤ objective data candidate) := by
  unfold prefer
  split
  · rename_i h
    exact ⟨h.1, h.2.le, fun _ ↦ le_rfl⟩
  · rename_i h
    exact ⟨hi, le_rfl, fun hc ↦ le_of_not_gt (fun hlt ↦ h ⟨hc, hlt⟩)⟩

private theorem foldl_prefer_spec (data : Instance) (routes : List Route) (incumbent : Route)
    (hi : Feasible data incumbent) :
    let best := routes.foldl (prefer data) incumbent
    Feasible data best ∧ objective data best ≤ objective data incumbent ∧
      ∀ route ∈ routes, Feasible data route → objective data best ≤ objective data route := by
  induction routes generalizing incumbent with
  | nil => simp [hi]
  | cons candidate rest ih =>
    obtain ⟨hf, hprev, hcandidate⟩ := prefer_spec data incumbent candidate hi
    obtain ⟨hbest, hstep, hrest⟩ := ih (prefer data incumbent candidate) hf
    refine ⟨hbest, hstep.trans hprev, ?_⟩
    intro route hmem hfeasible
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hstep.trans (hcandidate hfeasible)
    · exact hrest route hmem hfeasible

/-- Examine every ordered subset with the empty route as the initial incumbent. -/
def solve (data : Instance) : Route :=
  candidates.foldl (prefer data) []

theorem solve_optimal (data : Instance) : IsOptimal data (solve data) := by
  obtain ⟨hf, _, hcost⟩ := foldl_prefer_spec data candidates [] (feasible_empty data)
  exact ⟨hf, fun route hroute ↦ hcost route (mem_candidates hroute.1) hroute⟩

end LitterRouting
