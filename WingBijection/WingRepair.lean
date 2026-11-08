import WingBijection.Weights
import WingBijection.EffectiveCube

/-! The actual wing toggle, for every dimension, on an arbitrary valid wing system. -/

namespace WingBijection

structure WingSystem (n : ℕ) where
  O : Set (Cube n)
  decO : DecidablePred O
  A : {x : Cube n // x ∈ O} → Set (Fin n)
  decA : ∀ x, DecidablePred (A x)
  points : List {x : Cube n // x ∈ O}
  points_complete : ∀ x, x ∈ points
  closed : ∀ x : {x : Cube n // x ∈ O}, ∀ y : Cube n,
    (∀ j, j ∉ A x → y j = x.val j) → y ∈ O

namespace WingSystem

variable {n : ℕ} (D : WingSystem n)

abbrev Point := {x : Cube n // x ∈ D.O}

instance (priority := 2000) pointDecEq : DecidableEq D.Point := Subtype.instDecidableEq

instance decMember (x : Cube n) : Decidable (x ∈ D.O) := D.decO x
instance decWing (x : D.Point) (j : Fin n) : Decidable (j ∈ D.A x) := D.decA x j
instance pointEnumeration : Enumeration D.Point := ⟨D.points, D.points_complete⟩
instance pointFintype : Fintype D.Point :=
  ⟨D.points.toFinset, by intro x; simpa using D.points_complete x⟩
abbrev LocalMap := {a : D.Point → D.Point //
  ∀ x j, j ∉ D.A x → (a x).val j = x.val j}

def toggleImage (a : D.LocalMap) (x : D.Point) (j : Fin n)
    (hj : j ∈ D.A x) : D.Point := by
  refine ⟨Function.update (a.val x).val j (!(a.val x).val j), D.closed x _ ?_⟩
  intro k hk
  have hkj : k ≠ j := by
    intro h
    subst k
    exact hk hj
  rw [Function.update_of_ne hkj]
  exact a.property x k hk

def toggle (a : D.LocalMap) (x : D.Point) (j : Fin n)
    (hj : j ∈ D.A x) : D.LocalMap := by
  refine ⟨fun y => if y = x then D.toggleImage a x j hj else a.val y, ?_⟩
  intro y k hk
  by_cases hy : y = x
  · subst y
    have hkj : k ≠ j := by
      intro h
      subst k
      exact hk hj
    simpa [toggleImage, hkj]
      using a.property x k hk
  · simp only [if_neg hy]
    exact a.property y k hk

theorem toggle_involutive (x : D.Point) (j : Fin n) (hj : j ∈ D.A x) :
    Function.Involutive (fun a : D.LocalMap => D.toggle a x j hj) := by
  classical
  intro a
  apply Subtype.ext
  funext y
  apply Subtype.ext
  funext k
  by_cases hy : y = x
  · subst y
    by_cases hk : k = j
    · subst k
      simp [toggle, toggleImage]
    · simp [toggle, toggleImage]
  · simp [toggle, hy]

theorem toggle_ne (a : D.LocalMap) (x : D.Point) (j : Fin n) (hj : j ∈ D.A x) :
    D.toggle a x j hj ≠ a := by
  classical
  intro h
  have hh := congrArg (fun b : D.LocalMap => (b.val x).val j) h
  simp [toggle, toggleImage] at hh

abbrev Bad (p : D.Point → D.Point) (q : D.Point × Fin n) : Prop :=
  q.2 ∈ D.A q.1 ∧ (p q.1).val q.2 = q.1.val q.2

instance decBad (p : D.Point → D.Point) : DecidablePred (D.Bad p) := by
  intro q
  unfold Bad
  infer_instance

def repair (p : D.Point → D.Point) (a : D.LocalMap) : D.LocalMap :=
  if h : ∃ q, D.Bad p q then
    let q := chooseFinite (D.Bad p) h
    D.toggle a q.val.1 q.val.2 q.property.1
  else a

theorem repair_involutive (p : D.Point → D.Point) :
    Function.Involutive (D.repair p) := by
  intro a
  by_cases h : ∃ q, D.Bad p q
  · simp only [repair, dif_pos h]
    exact D.toggle_involutive _ _ _ a
  · simp only [repair, dif_neg h]

theorem repair_fixed_iff (p : D.Point → D.Point) (a : D.LocalMap) :
    D.repair p a = a ↔ ∀ x j, j ∈ D.A x → (p x).val j ≠ x.val j := by
  by_cases h : ∃ q, D.Bad p q
  · simp only [repair, dif_pos h]
    let q := chooseFinite (D.Bad p) h
    constructor
    · intro he
      exact False.elim (D.toggle_ne a _ _ q.property.1 he)
    · intro hf
      exact False.elim (hf q.val.1 q.val.2 q.property.1 q.property.2)
  · simp only [repair, dif_neg h]
    constructor
    · intro _ x j hj heq
      exact h ⟨(x,j), hj, heq⟩
    · intro _; trivial

theorem toggle_cost (a : D.LocalMap) (p : D.Point → D.Point)
    (x : D.Point) (j : Fin n) (hj : j ∈ D.A x)
    (hp : (p x).val j = x.val j) (y : D.Point) (k : Fin n) :
    bitCost (y.val k) (((D.toggle a x j hj).val y).val k) ((p y).val k) =
      bitCost (y.val k) ((a.val y).val k) ((p y).val k) := by
  classical
  by_cases hy : y = x
  · subst y
    by_cases hk : k = j
    · subst k
      simpa [toggle, toggleImage] using
        bitCost_toggle (x.val j) ((a.val x).val j) ((p x).val j) hp
    · simp [toggle, toggleImage, hk]
  · simp [toggle, hy]

theorem repair_weight [Fintype D.Point] (p : D.Point → D.Point)
    (a : D.LocalMap) (k : Fin n) :
    pairWeight (fun x : D.Point => x.val) (D.repair p a).val p k =
      pairWeight (fun x : D.Point => x.val) a.val p k := by
  by_cases h : ∃ q, D.Bad p q
  · simp only [repair, dif_pos h]
    unfold pairWeight
    apply Finset.sum_congr rfl
    intro y _
    exact D.toggle_cost a p _ _ (chooseFinite (D.Bad p) h).property.1
      (chooseFinite (D.Bad p) h).property.2 y k
  · simp only [repair, dif_neg h]

/-- The actual R operation implies both output conditions whenever it stops. -/
theorem stopped_output [Fintype D.Point] (p : Equiv.Perm D.Point)
    (a : D.LocalMap) (budget extra : Fin n → ℕ)
    (hstop : D.repair p a = a)
    (hw : ∀ j, pairWeight (fun x : D.Point => x.val) a.val p j + extra j = budget j) :
    (∀ x j, j ∈ D.A x → (p x).val j ≠ x.val j) ∧
    (∀ j, agreement (fun x : D.Point => x.val) p j ≤ budget j) := by
  have hp := (D.repair_fixed_iff p a).mp hstop
  exact ⟨hp, output_bound (fun x : D.Point => x.val) D.A a.val p budget extra
    a.property hp hw⟩

end WingSystem

end WingBijection
