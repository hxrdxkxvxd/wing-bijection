import WingBijection.Main
import Mathlib.Data.Fintype.Powerset

namespace WingBijection

/-- Validate the finite wing condition, then run the proved constructor. -/
def checkedConstruct (n : ℕ) (O : Finset (Cube n)) (A : Cube n → Finset (Fin n)) :
    Option (Equiv.Perm {x // x ∈ O}) :=
  if hA : ∀ x ∈ O, ∀ S ⊆ A x, flipSet x S ∈ O then
    some (construct n O A hA)
  else none

theorem checkedConstruct_of_valid (n : ℕ) (O : Finset (Cube n))
    (A : Cube n → Finset (Fin n)) (hA : ∀ x ∈ O, ∀ S ⊆ A x, flipSet x S ∈ O) :
    checkedConstruct n O A = some (construct n O A hA) := by
  simp only [checkedConstruct, dif_pos hA]

theorem checkedConstruct_none_iff (n : ℕ) (O : Finset (Cube n))
    (A : Cube n → Finset (Fin n)) :
    checkedConstruct n O A = none ↔ ¬ (∀ x ∈ O, ∀ S ⊆ A x, flipSet x S ∈ O) := by
  unfold checkedConstruct
  split <;> simp_all

theorem checkedConstruct_correct (n : ℕ) (O : Finset (Cube n))
    (A : Cube n → Finset (Fin n)) (τ : Equiv.Perm {x // x ∈ O})
    (hτ : checkedConstruct n O A = some τ) :
    (∀ x : {x // x ∈ O}, ∀ i ∈ A x.val, (τ x).val i ≠ x.val i) ∧
    ∀ j : Fin n, (Finset.univ.filter fun x : {x // x ∈ O} =>
      (τ x).val j = x.val j).card ≤
      (O.filter fun x => Function.update x j (!x j) ∉ O).card := by
  unfold checkedConstruct at hτ
  split at hτ
  · cases hτ
    exact construct_correct n O A ‹_›
  · cases hτ

end WingBijection
