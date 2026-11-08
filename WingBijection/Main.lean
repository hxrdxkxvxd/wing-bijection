import WingBijection.Runner

/-!
# The wing bijection theorem, proved without determinants

Statement in plain cube language (Theorem 3.1 of the PSI Aaronson–Ambainis paper):
for a finite set `O` of cube points and wings `A x` (every flip of a subset of `A x` stays in `O`),
there is a bijection `τ` of `O` such that
* (a) `τ x` differs from `x` in every coordinate of `A x`;
* (b) for each coordinate `j`, the number of `x` with `(τ x) j = x j` is at most the number of
  `j`-boundary points of `O`.

The proof is the alternating-involution construction of `FullState.lean`: no determinants,
no linear algebra, and no appeal to the existence of the bijection.
-/

namespace WingBijection

open Finset

/-- Flip the coordinates in `S`. -/
def flipSet {n : ℕ} (x : Cube n) (S : Finset (Fin n)) : Cube n :=
  fun i => if i ∈ S then !x i else x i

/-- The input wing system, with explicit cube and point enumerations. -/
def ofFinset (n : ℕ) (O : Finset (Cube n)) (A : Cube n → Finset (Fin n))
    (hA : ∀ x ∈ O, ∀ S ⊆ A x, flipSet x S ∈ O) : WingSystem n :=
    { O := {x | x ∈ O}
      decO := fun x => inferInstanceAs (Decidable (x ∈ O))
      A := fun x => {i | i ∈ A x.val}
      decA := fun x i => inferInstanceAs (Decidable (i ∈ A x.val))
      points := pointList n O
      points_complete := pointList_complete n O
      closed := by
        intro x y hy
        have hS : (univ.filter fun i => y i ≠ x.val i) ⊆ A x.val := by
          intro i hi
          by_contra h
          exact (mem_filter.mp hi).2 (hy i h)
        have hxy : flipSet x.val (univ.filter fun i => y i ≠ x.val i) = y := by
          funext i
          unfold flipSet
          by_cases h : y i = x.val i
          · simp [h]
          · simp only [mem_filter, mem_univ, true_and]
            revert h; cases y i <;> cases x.val i <;> simp
        have := hA x.val x.property _ hS
        rw [hxy] at this
        exact this }

/-- A total executable construction on every valid input. -/
def construct (n : ℕ) (O : Finset (Cube n)) (A : Cube n → Finset (Fin n))
    (hA : ∀ x ∈ O, ∀ S ⊆ A x, flipSet x S ∈ O) : Equiv.Perm {x // x ∈ O} :=
  let D := ofFinset n O A hA
  let _ : Fintype D.Point := (inferInstance : Fintype {x // x ∈ O})
  D.constructPerm

/-- Both conditions of Theorem 3.1 hold for the permutation computed by `construct`. -/
theorem construct_correct (n : ℕ) (O : Finset (Cube n)) (A : Cube n → Finset (Fin n))
    (hA : ∀ x ∈ O, ∀ S ⊆ A x, flipSet x S ∈ O) :
    (∀ x : {x // x ∈ O}, ∀ i ∈ A x.val, (construct n O A hA x).val i ≠ x.val i) ∧
      ∀ j : Fin n, (univ.filter fun x : {x // x ∈ O} =>
        (construct n O A hA x).val j = x.val j).card ≤
        (O.filter fun x => Function.update x j (!x j) ∉ O).card := by
  let D := ofFinset n O A hA
  let _ : Fintype D.Point := (inferInstance : Fintype {x // x ∈ O})
  obtain ⟨ha, hb⟩ := D.constructPerm_correct
  refine ⟨fun x i hi => ha x i hi, fun j => ?_⟩
  have h1 := hb j
  have e1 : agreement D.bits D.constructPerm j =
      (univ.filter fun x : {x // x ∈ O} => (construct n O A hA x).val j = x.val j).card := by
    unfold agreement
    rw [card_filter]
    exact sum_congr rfl fun x _ => by congr
  have e2 : D.bnd j = (O.filter fun x => Function.update x j (!x j) ∉ O).card := by
    unfold WingSystem.bnd WingSystem.Int
    rw [card_filter, ← sum_coe_sort O]
    apply sum_congr rfl
    intro x _
    simp only [flip1]
    by_cases h : Function.update x.val j (!x.val j) ∈ O
    · have h' : Function.update x.val j (!x.val j) ∈ D.O := h
      simp [h, h']
    · have h' : Function.update x.val j (!x.val j) ∉ D.O := h
      simp [h, h']
  rw [e1, e2] at h1
  exact h1

/-- The existential formulation in the paper is an immediate corollary of the
executable construction's universal correctness theorem. -/
theorem wing_bijection (n : ℕ) (O : Finset (Cube n)) (A : Cube n → Finset (Fin n))
    (hA : ∀ x ∈ O, ∀ S ⊆ A x, flipSet x S ∈ O) :
    ∃ τ : Equiv.Perm {x // x ∈ O},
      (∀ x : {x // x ∈ O}, ∀ i ∈ A x.val, (τ x).val i ≠ x.val i) ∧
      ∀ j : Fin n, (univ.filter fun x : {x // x ∈ O} => (τ x).val j = x.val j).card ≤
        (O.filter fun x => Function.update x j (!x j) ∉ O).card :=
  ⟨construct n O A hA, construct_correct n O A hA⟩

end WingBijection
