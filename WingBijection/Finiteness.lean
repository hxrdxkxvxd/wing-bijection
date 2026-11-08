import WingBijection.Weights
import Mathlib.Data.Set.Finite.List
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace WingBijection

/-- Every nonidentity permutation moves at least one coordinate somewhere.
This weaker-than-two lower bound is already sufficient to bound stack length. -/
theorem total_displacement_pos {X I : Type*} [Fintype X] [Fintype I]
    (bits : X → I → Bool) (hinj : Function.Injective bits)
    (p : Equiv.Perm X) (hp : p ≠ Equiv.refl X) :
    0 < ∑ j, displacement bits p j := by
  classical
  have hx : ∃ x, p x ≠ x := by
    by_contra hn
    apply hp
    apply Equiv.ext
    intro x
    by_contra h
    exact hn ⟨x, h⟩
  obtain ⟨x, hx⟩ := hx
  have hj : ∃ j, bits (p x) j ≠ bits x j := by
    by_contra hn
    apply hx
    apply hinj
    funext j
    by_contra h
    exact hn ⟨j, h⟩
  obtain ⟨j, hj⟩ := hj
  have h1 : 1 ≤ displacement bits p j := by
    unfold displacement
    have h := Finset.single_le_sum
      (s := Finset.univ) (f := fun y => if bits (p y) j ≠ bits y j then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    simpa only [if_pos hj] using h
  have h2 : displacement bits p j ≤ ∑ k, displacement bits p k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  omega

theorem length_le_weight_sum {G : Type*} (w : G → ℕ)
    (hw : ∀ g, 0 < w g) (l : List G) : l.length ≤ (l.map w).sum := by
  induction l with
  | nil => simp
  | cons g rest ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have h := hw g
    omega

@[ext] structure RawAux (A P G E : Type*) where
  alpha : A
  perm : P
  stack : List G
  counters : E → ℕ

/-- State equality compares its finite functions and stack directly. -/
instance {A P G E : Type*} [DecidableEq A] [DecidableEq P] [DecidableEq G]
    [Fintype E] : DecidableEq (RawAux A P G E) := fun s t =>
  if h : s.alpha = t.alpha ∧ s.perm = t.perm ∧ s.stack = t.stack ∧
      s.counters = t.counters then
    isTrue (RawAux.ext h.1 h.2.1 h.2.2.1 h.2.2.2)
  else isFalse (fun he => h (by cases he; exact ⟨rfl, rfl, rfl, rfl⟩))

/-- A generic finiteness result for weighted stacks and bounded counters.
The cube application must still derive this budget inequality from its invariant. -/
theorem finite_weighted_aux
    {A P G E : Type*} [Finite A] [Finite P] [Finite G] [Fintype E]
    (w : G → ℕ) (hw : ∀ g, 0 < w g) (B : ℕ) :
    Finite {s : RawAux A P G E //
      (s.stack.map w).sum + (∑ e, s.counters e) ≤ B} := by
  classical
  let S := {s : RawAux A P G E //
    (s.stack.map w).sum + (∑ e, s.counters e) ≤ B}
  let BoundedList := {l : List G // l.length ≤ B}
  have : Finite BoundedList := (List.finite_length_le G B).to_subtype
  let T := A × P × BoundedList × (E → Fin (B + 1))
  let encode : S → T := fun s =>
    (s.val.alpha, s.val.perm,
      ⟨s.val.stack, by
        have h := length_le_weight_sum w hw s.val.stack
        have hb := s.property
        omega⟩,
      fun e => ⟨s.val.counters e, by
        have h : s.val.counters e ≤ ∑ t, s.val.counters t :=
          Finset.single_le_sum (fun t _ => Nat.zero_le (s.val.counters t))
            (Finset.mem_univ e)
        have hb := s.property
        omega⟩)
  apply Finite.of_injective encode
  intro s t h
  apply Subtype.ext
  apply RawAux.ext
  · exact congrArg (fun z : T => z.1) h
  · exact congrArg (fun z : T => z.2.1) h
  · exact congrArg (fun z : T => z.2.2.1.val) h
  · funext e
    exact congrArg (fun z : T => (z.2.2.2 e).val) h

end WingBijection
