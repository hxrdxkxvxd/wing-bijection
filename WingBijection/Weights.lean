import WingBijection.Involutions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace WingBijection

def bitCost (x a p : Bool) : ℕ :=
  (if a ≠ x then 1 else 0) + (if a = p then 1 else 0)

theorem bitCost_toggle (x a p : Bool) (h : p = x) :
    bitCost x (!a) p = bitCost x a p := by
  cases x <;> cases a <;> cases p <;> simp_all [bitCost]

theorem bitCost_good (x a p : Bool) (h : p = x → a = x) :
    bitCost x a p = (if p = x then 1 else 0) + 2 * (if a ≠ x then 1 else 0) := by
  cases x <;> cases a <;> cases p <;> simp_all [bitCost]

section Finite

variable {X I : Type*} [Fintype X]

def agreement (bits : X → I → Bool) (p : X → X) (j : I) : ℕ :=
  ∑ x, if bits (p x) j = bits x j then 1 else 0

def displacement (bits : X → I → Bool) (a : X → X) (j : I) : ℕ :=
  ∑ x, if bits (a x) j ≠ bits x j then 1 else 0

def pairWeight (bits : X → I → Bool) (a p : X → X) (j : I) : ℕ :=
  ∑ x, bitCost (bits x j) (bits (a x) j) (bits (p x) j)

theorem output_weight_identity (bits : X → I → Bool)
    (A : X → Set I) (a p : X → X)
    (ha : ∀ x j, j ∉ A x → bits (a x) j = bits x j)
    (hp : ∀ x j, j ∈ A x → bits (p x) j ≠ bits x j) (j : I) :
    pairWeight bits a p j = agreement bits p j + 2 * displacement bits a j := by
  unfold pairWeight agreement displacement
  calc
    _ = ∑ x, ((if bits (p x) j = bits x j then 1 else 0) +
        2 * (if bits (a x) j ≠ bits x j then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply bitCost_good
      intro h
      by_cases hx : j ∈ A x
      · exact False.elim (hp x j hx h)
      · exact ha x j hx
    _ = _ := by
      have htwo (t : ℕ) : 2 * t = t + t := by omega
      simp only [htwo, Finset.sum_add_distrib]

/-- At an R-fixed state the actual coordinate bound follows from the invariant. -/
theorem output_bound (bits : X → I → Bool) (A : X → Set I)
    (a p : X → X) (budget extra : I → ℕ)
    (ha : ∀ x j, j ∉ A x → bits (a x) j = bits x j)
    (hp : ∀ x j, j ∈ A x → bits (p x) j ≠ bits x j)
    (hw : ∀ j, pairWeight bits a p j + extra j = budget j) :
    ∀ j, agreement bits p j ≤ budget j := by
  intro j
  have h := hw j
  rw [output_weight_identity bits A a p ha hp j] at h
  omega

end Finite

end WingBijection
