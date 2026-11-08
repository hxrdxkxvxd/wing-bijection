import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Fintype.Perm

namespace WingBijection

/-- An explicit ordered enumeration, not a choice of a list representative of a finset. -/
class Enumeration (X : Type*) where
  elems : List X
  complete : ∀ x, x ∈ elems

instance (n : ℕ) : Enumeration (Fin n) :=
  ⟨List.finRange n, by intro x; simp⟩

instance {X Y : Type*} [Enumeration X] [Enumeration Y] : Enumeration (X × Y) :=
  ⟨Enumeration.elems.product Enumeration.elems, by
    intro p
    exact List.mem_product.mpr ⟨Enumeration.complete p.1, Enumeration.complete p.2⟩⟩

/-- Deterministically select the first satisfying element of the supplied list. -/
def pick {X : Type*} [Enumeration X] (P : X → Prop) [DecidablePred P] : Option X :=
  Enumeration.elems.find? (fun x => decide (P x))

theorem pick_some {X : Type*} [Enumeration X] {P : X → Prop} [DecidablePred P]
    {x : X} (h : pick P = some x) : P x := by
  have hh := List.find?_some h
  simpa only [decide_eq_true_eq] using hh

theorem pick_none {X : Type*} [Enumeration X] {P : X → Prop} [DecidablePred P]
    (h : pick P = none) : ∀ x, ¬P x := by
  intro x
  have hh := List.find?_eq_none.mp h x (Enumeration.complete x)
  simpa only [decide_eq_true_eq] using hh

theorem pick_none_of {X : Type*} [Enumeration X] {P : X → Prop} [DecidablePred P]
    (h : ∀ x, ¬P x) : pick P = none := by
  apply List.find?_eq_none.mpr
  intro x _
  simpa only [decide_eq_true_eq] using h x

/-- The deterministic choice depends on truth values, not on decision-procedure proofs. -/
theorem pick_congr {X : Type*} [Enumeration X] {P Q : X → Prop}
    [DecidablePred P] [DecidablePred Q] (h : ∀ x, P x ↔ Q x) : pick P = pick Q := by
  unfold pick
  have he : (fun x => decide (P x)) = (fun x => decide (Q x)) := by
    funext x
    by_cases hp : P x
    · have hq := (h x).mp hp
      simp only [decide_eq_true hp, decide_eq_true hq]
    · have hq : ¬ Q x := fun hq => hp ((h x).mpr hq)
      simp only [decide_eq_false hp, decide_eq_false hq]
  rw [he]

/-- A finite witness search; the existence proof is erased from execution. -/
def chooseFinite {X : Type*} [Enumeration X] (P : X → Prop) [DecidablePred P]
    (h : ∃ x, P x) : {x // P x} :=
  match hp : pick P with
  | some x => ⟨x, pick_some hp⟩
  | none => False.elim (by obtain ⟨x, hx⟩ := h; exact pick_none hp x hx)

/-- Construct a permutation inverse by a finite lookup rather than classical choice. -/
def permOfInj {X : Type*} [Enumeration X] [Fintype X] [DecidableEq X]
    (f : X → X) (h : Function.Injective f) : Equiv.Perm X where
  toFun := f
  invFun y := (chooseFinite (fun x => f x = y) (h.bijective_of_finite.2 y)).val
  left_inv x := h (chooseFinite (fun y => f y = f x) (h.bijective_of_finite.2 (f x))).property
  right_inv y := (chooseFinite (fun x => f x = y) (h.bijective_of_finite.2 y)).property

@[simp] theorem permOfInj_apply {X : Type*} [Enumeration X] [Fintype X] [DecidableEq X]
    (f : X → X) (h : Function.Injective f) (x : X) : permOfInj f h x = f x := rfl

/-- Compare permutations by their forward functions, without enumerating permutations. -/
instance (priority := 2000) effectivePermEq {X : Type*} [Fintype X] [DecidableEq X] :
    DecidableEq (Equiv.Perm X) := fun p q =>
  if h : (p : X → X) = (q : X → X) then
    isTrue (Equiv.ext (congrFun h))
  else isFalse (fun hq => h (congrArg Equiv.toFun hq))

end WingBijection
