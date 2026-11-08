import WingBijection.Canonical
import Mathlib.Data.Nat.Find

namespace WingBijection

/-- A tail-recursive, unbounded walk with a proved stopping condition. The termination
measure and the reachability certificate are propositions and are erased at runtime. -/
def finiteWalk {X : Type*} (step : X → X) (done : X → Prop) [DecidablePred done]
    (s : X) (h : ∃ k, done (step^[k] s)) :
    {t : X // done t ∧ ∃ k, t = step^[k] s} :=
  if hs : done s then ⟨s, hs, 0, rfl⟩
  else
    have htail : ∃ k, done (step^[k] (step s)) := by
      obtain ⟨k, hk⟩ := h
      cases k with
      | zero => exact False.elim (hs hk)
      | succ k => exact ⟨k, by simpa only [Function.iterate_succ_apply] using hk⟩
    let t := finiteWalk step done (step s) htail
    ⟨t.val, t.property.1, by
      obtain ⟨k, hk⟩ := t.property.2
      exact ⟨k + 1, hk.trans (Function.iterate_succ_apply step k s).symm⟩⟩
termination_by Nat.find h
decreasing_by
  have hn : Nat.find h ≠ 0 := by
    intro hz
    have hh := Nat.find_spec h
    rw [hz] at hh
    exact hs hh
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have ht : done (step^[k] (step s)) := by
    rw [← Function.iterate_succ_apply, ← hk]
    exact Nat.find_spec h
  have hle := Nat.find_min' htail ht
  omega

namespace WingSystem

variable {n : ℕ} (D : WingSystem n) [Fintype D.Point]

/-- The stopping test reads only the actual wing violations. -/
abbrev Finished (s : D.St) : Prop :=
  ∀ x j, j ∈ D.A x → (s.1.perm x).val j ≠ x.val j

instance decFinished : DecidablePred D.Finished := by
  intro s
  unfold Finished
  infer_instance

theorem finished_iff (s : D.St) : D.Finished s ↔ D.Rmap s = s := by
  constructor
  · intro hs
    apply Subtype.ext
    apply RawAux.ext
    · exact (D.repair_fixed_iff s.1.perm s.1.alpha).mpr hs
    · rfl
    · rfl
    · rfl
  · intro hs
    apply (D.repair_fixed_iff s.1.perm s.1.alpha).mp
    exact congrArg (fun t : D.St => t.1.alpha) hs

/-- Execute the alternating two-involution path from its explicit anchor. -/
def run : {s : D.St // D.Rmap s = s ∧
    ∃ k, s = (D.Lmap ∘ D.Rmap)^[k] D.anchor} :=
  let h := alternating_terminates D.Lmap D.Rmap D.Lmap_involutive D.Rmap_involutive
    D.anchor D.Lmap_fixed_iff
  let h' : ∃ k, D.Finished (D.canonicalAdvance^[k] D.anchor) := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, (D.finished_iff _).mpr (by simpa only [D.canonicalAdvance_eq] using hk)⟩
  let result := finiteWalk D.canonicalAdvance D.Finished D.anchor h'
  ⟨result.val, (D.finished_iff result.val).mp result.property.1,
    by simpa only [D.canonicalAdvance_eq] using result.property.2⟩

/-- The returned permutation is the endpoint's permutation, with no search over
candidate permutations. -/
def constructPerm : Equiv.Perm D.Point := D.run.val.val.perm

theorem constructPerm_correct :
    (∀ x j, j ∈ D.A x → (D.constructPerm x).val j ≠ x.val j) ∧
    ∀ j, agreement D.bits D.constructPerm j ≤ D.bnd j := by
  let s := D.run.val
  have hstop : D.repair s.1.perm s.1.alpha = s.1.alpha :=
    congrArg (fun t : D.St => t.1.alpha) D.run.property.1
  exact D.stopped_output s.1.perm s.1.alpha D.bnd
    (fun j => D.stackW s.1.stack j + 2 * ∑ x, s.1.counters (j, x)) hstop
    (fun j => by rw [← Nat.add_assoc]; exact s.2.2.2 j)

end WingSystem
end WingBijection
