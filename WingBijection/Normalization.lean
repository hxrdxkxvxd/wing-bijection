import WingBijection.Involutions

namespace WingBijection

universe u v

/-- An involution together with its unique fixed point. -/
structure RootedInvolution (X : Type u) where
  map : X → X
  involutive : Function.Involutive map
  root : X
  fixed_iff : ∀ x, map x = x ↔ x = root

namespace RootedInvolution

variable {X : Type u} {Y : Type v} [DecidableEq X]

abbrev Fixed (t : X → X) := {x : X // t x = x}

def extendMap (t : X → X) (g : Fixed t → Fixed t) (x : X) : X := by
  exact if hx : t x = x then (g ⟨x, hx⟩).val else t x

theorem extendMap_involutive (t : X → X) (ht : Function.Involutive t)
    (g : Fixed t → Fixed t) (hg : Function.Involutive g) :
    Function.Involutive (extendMap t g) := by
  classical
  intro x
  by_cases hx : t x = x
  · have hfix := (g ⟨x, hx⟩).property
    have hh := congrArg Subtype.val (hg ⟨x, hx⟩)
    simpa only [extendMap, dif_pos hx, dif_pos hfix] using hh
  · have hn : t (t x) ≠ t x := by
      intro h
      exact hx ((ht x).symm.trans h).symm
    simp only [extendMap, dif_neg hx, dif_neg hn]
    exact ht x

def lift (t : X → X) (ht : Function.Involutive t)
    (e : Fixed t ≃ Y) (J : RootedInvolution Y) : RootedInvolution X := by
  let g : Fixed t → Fixed t := fun z => e.symm (J.map (e z))
  have hg : Function.Involutive g := by
    intro z
    simp only [g, e.apply_symm_apply]
    rw [J.involutive (e z), e.symm_apply_apply]
  let r : Fixed t := e.symm J.root
  have hgf : ∀ z, g z = z ↔ z = r := by
    intro z
    constructor
    · intro h
      have hh := congrArg e h
      simp only [g, e.apply_symm_apply] at hh
      have hz := (J.fixed_iff (e z)).mp hh
      simpa [r] using congrArg e.symm hz
    · intro h
      subst z
      have hroot : J.map J.root = J.root := (J.fixed_iff J.root).mpr rfl
      simp [g, r, hroot]
  refine ⟨extendMap t g, extendMap_involutive t ht g hg, r.val, ?_⟩
  intro x
  by_cases hx : t x = x
  · have he : extendMap t g x = x ↔ g ⟨x, hx⟩ = ⟨x, hx⟩ := by
      simp only [extendMap, dif_pos hx]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [he, hgf]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · have hxr : x ≠ r.val := by
      intro h
      exact hx (by simpa only [h] using r.property)
    have hm : extendMap t g x = t x := by
      unfold extendMap
      rw [dif_neg hx]
    rw [hm]
    exact iff_of_false hx hxr

/-- The terminal singleton supplies the unique fixed point at the final level. -/
def terminal (X : Type u) [Unique X] : RootedInvolution X where
  map := id
  involutive := fun _ => rfl
  root := default
  fixed_iff := fun _x => ⟨fun _ => Subsingleton.elim _ _, fun _ => rfl⟩

end RootedInvolution

end WingBijection
