import Mathlib.Data.Fintype.Pi

inductive QFormula (m n : Nat) where
  | exVar : Fin m → QFormula m n
  | allVar : Fin n → QFormula m n
  | neg : QFormula m n → QFormula m n
  | conj : QFormula m n → QFormula m n → QFormula m n
  | disj : QFormula m n → QFormula m n → QFormula m n

def QFormula.eval {m n : Nat}
    (φ : QFormula m n)
    (x : Fin m → Bool)
    (y : Fin n → Bool) : Bool :=
  match φ with
  | .exVar i => x i
  | .allVar i => y i
  | .neg a => !(a.eval x y)
  | .conj a b => a.eval x y && b.eval x y
  | .disj a b => a.eval x y || b.eval x y

def QSAT2 {m n : Nat}
    (φ : QFormula m n) : Prop :=
  ∃ x : Fin m → Bool,
    ∀ y : Fin n → Bool,
      φ.eval x y = true

def exampleFormula : QFormula 1 1 :=
  .conj
    (.disj (.exVar 0) (.allVar 0))
    (.disj (.exVar 0) (.neg (.allVar 0)))

theorem example_satisfiable :
    QSAT2 exampleFormula := by
  refine ⟨fun _ => true, ?_⟩
  intro y
  rfl

#print axioms example_satisfiable

/-- Exhaustive decision procedure over the finite assignment spaces. -/
def solveQSAT2 {m n : Nat} (φ : QFormula m n) : Bool :=
  decide (∃ x : Fin m → Bool, ∀ y : Fin n → Bool, φ.eval x y = true)

theorem solveQSAT2_correct {m n : Nat} (φ : QFormula m n) :
    solveQSAT2 φ = true ↔ QSAT2 φ := by
  simp [solveQSAT2, QSAT2]

#guard solveQSAT2 exampleFormula
#guard !(solveQSAT2 (.allVar 0 : QFormula 0 1))
#print axioms solveQSAT2_correct
