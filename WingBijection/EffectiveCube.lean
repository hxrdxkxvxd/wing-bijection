import WingBijection.Effective
import Mathlib.Data.Fin.Tuple.Basic

namespace WingBijection

abbrev Cube (n : ℕ) := Fin n → Bool

instance (priority := 2000) cubeDecEq (n : ℕ) : DecidableEq (Cube n) :=
  Fintype.decidablePiFintype

def cubeList : (n : ℕ) → List (Cube n)
  | 0 => [fun i => Fin.elim0 i]
  | n + 1 => (cubeList n).flatMap fun tail =>
      [Fin.cons false tail, Fin.cons true tail]

theorem cubeList_complete (n : ℕ) (x : Cube n) : x ∈ cubeList n := by
  induction n with
  | zero =>
    have hx : x = (fun i : Fin 0 => Fin.elim0 i) := Subsingleton.elim _ _
    simp [cubeList, hx]
  | succ n ih =>
    let tail : Cube n := fun i => x i.succ
    have hx : Fin.cons (x 0) tail = x := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [← hx]
    apply List.mem_flatMap.mpr
    refine ⟨tail, ih tail, ?_⟩
    cases x 0 <;> simp

def pointList (n : ℕ) (O : Finset (Cube n)) : List {x // x ∈ O} :=
  (cubeList n).filterMap fun x => if h : x ∈ O then some ⟨x, h⟩ else none

theorem pointList_complete (n : ℕ) (O : Finset (Cube n)) (x : {x // x ∈ O}) :
    x ∈ pointList n O := by
  apply List.mem_filterMap.mpr
  exact ⟨x.val, cubeList_complete n x.val, by simp [x.property]⟩

end WingBijection
