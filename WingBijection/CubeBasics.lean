import WingBijection.WingRepair
import WingBijection.Finiteness
import WingBijection.Normalization
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Concrete cube facts: interior edges, edge switches, agreement counts, boundary counts. -/

namespace WingBijection

open Finset

/-- Two functions that agree away from two distinct points. -/
theorem sum_two {X : Type*} [Fintype X] [DecidableEq X] (f g : X → ℕ) (x y : X)
    (hxy : x ≠ y) (h : ∀ z, z ≠ x → z ≠ y → f z = g z) :
    (∑ z, f z) + (g x + g y) = (∑ z, g z) + (f x + f y) := by
  have hy : y ∈ (univ : Finset X).erase x := mem_erase.mpr ⟨hxy.symm, mem_univ y⟩
  rw [← add_sum_erase _ f (mem_univ x), ← add_sum_erase _ g (mem_univ x),
    ← add_sum_erase _ f hy, ← add_sum_erase _ g hy]
  have hr : ∑ z ∈ ((univ : Finset X).erase x).erase y, f z =
      ∑ z ∈ ((univ : Finset X).erase x).erase y, g z := by
    apply sum_congr rfl
    intro z hz
    have hz1 := ne_of_mem_erase hz
    have hz2 := ne_of_mem_erase (mem_of_mem_erase hz)
    exact h z hz2 hz1
  rw [hr]
  omega

theorem sum_one {X : Type*} [Fintype X] [DecidableEq X] (f g : X → ℕ) (x : X)
    (h : ∀ z, z ≠ x → f z = g z) :
    (∑ z, f z) + g x = (∑ z, g z) + f x := by
  rw [← add_sum_erase _ f (mem_univ x), ← add_sum_erase _ g (mem_univ x)]
  have hr : ∑ z ∈ (univ : Finset X).erase x, f z = ∑ z ∈ (univ : Finset X).erase x, g z :=
    sum_congr rfl fun z hz => h z (ne_of_mem_erase hz)
  rw [hr]
  omega

def flip1 {n : ℕ} (y : Cube n) (j : Fin n) : Cube n := Function.update y j (!y j)

@[simp] theorem flip1_self {n : ℕ} (y : Cube n) (j : Fin n) : flip1 y j j = !y j := by
  simp [flip1]

theorem flip1_ne {n : ℕ} (y : Cube n) {i j : Fin n} (h : i ≠ j) : flip1 y j i = y i := by
  simp [flip1, h]

@[simp] theorem flip1_flip1 {n : ℕ} (y : Cube n) (j : Fin n) : flip1 (flip1 y j) j = y := by
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [flip1_ne _ h]

namespace WingSystem

variable {n : ℕ} (D : WingSystem n)

/-- `x` lies on an interior `j`-edge. -/
def Int (j : Fin n) (x : D.Point) : Prop := flip1 x.val j ∈ D.O

instance decInt (j : Fin n) : DecidablePred (D.Int j) := by
  intro x
  unfold Int
  infer_instance

def LowerInt (j : Fin n) (x : D.Point) : Prop := x.val j = false ∧ D.Int j x

instance decLowerInt (j : Fin n) : DecidablePred (D.LowerInt j) := by
  intro x
  unfold LowerInt
  infer_instance

def sw (j : Fin n) (x : D.Point) : D.Point := by
  exact if h : D.Int j x then ⟨flip1 x.val j, h⟩ else x

theorem sw_val_of_int {j : Fin n} {x : D.Point} (h : D.Int j x) :
    (D.sw j x).val = flip1 x.val j := by
  classical
  simp [sw, h]

theorem sw_of_not_int {j : Fin n} {x : D.Point} (h : ¬ D.Int j x) : D.sw j x = x := by
  classical
  simp [sw, h]

theorem sw_involutive (j : Fin n) : Function.Involutive (D.sw j) := by
  classical
  intro x
  by_cases h : D.Int j x
  · have h2 : D.Int j (D.sw j x) := by
      unfold Int
      rw [D.sw_val_of_int h, flip1_flip1]
      exact x.property
    apply Subtype.ext
    rw [D.sw_val_of_int h2, D.sw_val_of_int h, flip1_flip1]
  · rw [D.sw_of_not_int h, D.sw_of_not_int h]

/-- The switch along all interior `j`-edges. -/
def sigma (j : Fin n) : Equiv.Perm D.Point :=
  Function.Involutive.toPerm _ (D.sw_involutive j)

theorem sigma_apply (j : Fin n) (x : D.Point) : D.sigma j x = D.sw j x := rfl

theorem sigma_sigma (j : Fin n) (x : D.Point) : D.sigma j (D.sigma j x) = x :=
  D.sw_involutive j x

theorem sigma_mul_self (j : Fin n) : D.sigma j * D.sigma j = 1 := by
  ext x
  simp [Equiv.Perm.mul_apply, sigma_sigma]

theorem sigma_bit_ne (j : Fin n) (x : D.Point) {i : Fin n} (h : i ≠ j) :
    (D.sigma j x).val i = x.val i := by
  classical
  rw [sigma_apply]
  by_cases hx : D.Int j x
  · rw [D.sw_val_of_int hx, flip1_ne _ h]
  · rw [D.sw_of_not_int hx]

theorem sigma_bit_int (j : Fin n) (x : D.Point) (h : D.Int j x) :
    (D.sigma j x).val j = !x.val j := by
  rw [sigma_apply, D.sw_val_of_int h, flip1_self]

theorem sigma_of_not_int (j : Fin n) (x : D.Point) (h : ¬ D.Int j x) : D.sigma j x = x := by
  rw [sigma_apply, D.sw_of_not_int h]

theorem int_sigma (j : Fin n) (x : D.Point) (h : D.Int j x) : D.Int j (D.sigma j x) := by
  unfold Int
  rw [sigma_apply, D.sw_val_of_int h, flip1_flip1]
  exact x.property

theorem sigma_ne_of_int (j : Fin n) (x : D.Point) (h : D.Int j x) : D.sigma j x ≠ x := by
  intro he
  have := congrArg (fun z : D.Point => z.val j) he
  simp only [D.sigma_bit_int j x h] at this
  cases hx : x.val j <;> simp [hx] at this

/-- Bits of `σ_j x` agree with `x` exactly at boundary points. -/
theorem sigma_bit_eq_iff (j : Fin n) (x : D.Point) :
    (D.sigma j x).val j = x.val j ↔ ¬ D.Int j x := by
  by_cases h : D.Int j x
  · rw [D.sigma_bit_int j x h]
    cases x.val j <;> simp [h]
  · rw [D.sigma_of_not_int j x h]
    simp [h]

/-- The number of `j`-boundary points. -/
def bnd [Fintype D.Point] (j : Fin n) : ℕ := by
  exact ∑ x : D.Point, if D.Int j x then 0 else 1

abbrev bits : D.Point → Fin n → Bool := fun x => x.val

theorem bits_injective : Function.Injective D.bits := fun _ _ h => Subtype.ext h

section Fin

variable [Fintype D.Point]

def agr (p : Equiv.Perm D.Point) (j : Fin n) : ℕ :=
  agreement D.bits p j

theorem agr_mul_of_preserve (p s : Equiv.Perm D.Point) (j : Fin n)
    (hs : ∀ z, (s z).val j = z.val j) : D.agr (p * s) j = D.agr p j := by
  classical
  unfold agr agreement
  have : ∀ x, (if D.bits ((p * s) x) j = D.bits x j then 1 else 0) =
      (fun y => if D.bits (p y) j = D.bits y j then 1 else 0) (s x) := by
    intro x
    have hx := hs x
    simp only [Equiv.Perm.mul_apply, bits, hx]
    congr
  simp_rw [this]
  exact Equiv.sum_comp s (fun y => if D.bits (p y) j = D.bits y j then 1 else 0)

/-- If a permutation preserves coordinate `j`, its `j`-agreement after `σ_j` is the boundary
count. -/
theorem agr_mul_sigma_of_preserve (r : Equiv.Perm D.Point) (j : Fin n)
    (hr : ∀ z, (r z).val j = z.val j) : D.agr (r * D.sigma j) j = D.bnd j := by
  classical
  unfold agr agreement bnd
  apply sum_congr rfl
  intro x _
  simp only [Equiv.Perm.mul_apply, bits, hr]
  by_cases h : D.Int j x
  · have := (D.sigma_bit_eq_iff j x).not.mpr (not_not.mpr h)
    simp [this, h]
  · have := (D.sigma_bit_eq_iff j x).mpr h
    simp [this, h]

/-- If every interior point changes coordinate `j` and the agreement equals the boundary count,
then every boundary point keeps coordinate `j`. -/
theorem boundary_keeps (p : Equiv.Perm D.Point) (j : Fin n)
    (hint : ∀ z, D.Int j z → (p z).val j ≠ z.val j) (hagr : D.agr p j = D.bnd j)
    (z : D.Point) (hz : ¬ D.Int j z) : (p z).val j = z.val j := by
  classical
  unfold agr agreement bnd at hagr
  have hle : ∀ x ∈ (univ : Finset D.Point),
      (if D.bits (p x) j = D.bits x j then 1 else 0) ≤ (if D.Int j x then 0 else 1) := by
    intro x _
    by_cases h : D.Int j x
    · simp [bits, hint x h, h]
    · split_ifs <;> simp
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hagr z (mem_univ z)
  simp only [hz, if_false, bits] at heq
  by_contra hne
  simp [hne] at heq

end Fin

end WingSystem

end WingBijection
