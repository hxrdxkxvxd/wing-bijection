import WingBijection.Memo

namespace WingBijection.WingSystem

variable {n : ℕ} (D : WingSystem n)

/-- Evaluate an explicit table of point bit tables. -/
def tableCube (t : MemoTable D.Point (MemoTable (Fin n) Bool)) (x : D.Point) : Cube n :=
  (t.apply (fun x => tabulate x.val) x).apply (fun _ => false)

/-- The table carries the assertion that every returned cube point stays in O. -/
abbrev MapTable := {t : MemoTable D.Point (MemoTable (Fin n) Bool) //
  ∀ x, D.tableCube t x ∈ D.O}

/-- Store actual Boolean bit data, rather than closures producing cube points. -/
@[noinline] def bakeMap (f : D.Point → D.Point) : D.MapTable :=
  ⟨tabulate (fun x => tabulate (f x).val), by
    intro x
    simpa only [tableCube, tabulate_apply] using (f x).property⟩

def applyMap (t : D.MapTable) (x : D.Point) : D.Point :=
  ⟨D.tableCube t.val x, t.property x⟩

@[simp] theorem apply_bake (f : D.Point → D.Point) : D.applyMap (D.bakeMap f) = f := by
  funext x
  apply Subtype.ext
  change ((tabulate (fun x => tabulate (f x).val)).apply
    (fun x => tabulate x.val) x).apply (fun _ => false) = (f x).val
  simp only [tabulate_apply]

/-- Cache both permutation directions as explicit Boolean data. -/
def cachePointPerm (p : Equiv.Perm D.Point) : Equiv.Perm D.Point :=
  let forward := D.bakeMap (p : D.Point → D.Point)
  let backward := D.bakeMap (p.symm : D.Point → D.Point)
  { toFun := D.applyMap forward
    invFun := D.applyMap backward
    left_inv x := by
      simpa only [forward, backward, apply_bake] using p.symm_apply_apply x
    right_inv x := by
      simpa only [forward, backward, apply_bake] using p.apply_symm_apply x }

@[simp] theorem cachePointPerm_eq (p : Equiv.Perm D.Point) : D.cachePointPerm p = p := by
  apply Equiv.ext
  exact congrFun (D.apply_bake p)

variable [Fintype D.Point]

/-- Flatten both maps and their point values, as well as the counters. -/
def canonicalFreeze (s : D.St) : D.St :=
  let active := D.bakeMap s.1.alpha.val
  let counters := tabulate s.1.counters
  ⟨⟨⟨D.applyMap active, by
        simpa only [active, apply_bake] using s.1.alpha.property⟩,
      D.cachePointPerm s.1.perm, s.1.stack, counters.apply (fun _ => 0)⟩,
    by simpa only [active, counters, apply_bake, tabulate_apply, cachePointPerm_eq] using s.2⟩

@[simp] theorem canonicalFreeze_eq (s : D.St) : D.canonicalFreeze s = s := by
  apply Subtype.ext
  apply RawAux.ext
  · exact Subtype.ext (D.apply_bake _)
  · exact D.cachePointPerm_eq _
  · rfl
  · exact tabulate_apply _ _

/-- The optimized step is proved equal to one mathematical alternating step. -/
def canonicalAdvance (s : D.St) : D.St := D.canonicalFreeze (D.Lmap (D.Rmap s))

theorem canonicalAdvance_eq : D.canonicalAdvance = D.Lmap ∘ D.Rmap :=
  funext fun _ => D.canonicalFreeze_eq _

end WingBijection.WingSystem
