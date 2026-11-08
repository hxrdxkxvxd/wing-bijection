import WingBijection.Main

/-!
# Reimer's Butterfly Lemma from the wing bijection

Smyth's formulation (Lemma 2.4 of Smyth), on the whole cube, as recalled in Remark 3.10 of the
PSI paper. A butterfly is a pair `(a, b)` of cube points with body `a` and tip `b`:

* `Red (a, b) = {b^S : S ⊆ Δ(a, b)}`;
* `Yellow (a, b) = {y : y i ≠ b i for all i ∈ Δ(a, b)}`.

For a family of butterflies with distinct tips, the family's size is at most the size of the
intersection of the union of the red sets with the union of the yellow sets.

The proof applies part (a) of `wing_bijection` with `O` the union of the red sets, the wing
`Δ(a, b)` at each tip `b`, and empty wings elsewhere, and then uses injectivity.
-/

namespace WingBijection

open Finset

/-- The coordinates where `a` and `b` differ. -/
def diffSet {n : ℕ} (a b : Cube n) : Finset (Fin n) := univ.filter fun i => a i ≠ b i

def red {n : ℕ} (B : Cube n × Cube n) : Finset (Cube n) :=
  (diffSet B.1 B.2).powerset.image (flipSet B.2)

def yellow {n : ℕ} (B : Cube n × Cube n) : Finset (Cube n) :=
  univ.filter fun y => ∀ i ∈ diffSet B.1 B.2, y i ≠ B.2 i

theorem flipSet_empty {n : ℕ} (x : Cube n) : flipSet x ∅ = x := by
  funext i; simp [flipSet]

theorem butterfly_lemma (n : ℕ) (F : Finset (Cube n × Cube n))
    (htips : ∀ B ∈ F, ∀ B' ∈ F, B.2 = B'.2 → B = B') :
    F.card ≤ (F.biUnion red ∩ F.biUnion yellow).card := by
  classical
  set O := F.biUnion red
  -- the wing at a tip is the difference set of its (unique) butterfly; empty elsewhere
  let A : Cube n → Finset (Fin n) := fun x =>
    (F.filter fun B => B.2 = x).biUnion fun B => diffSet B.1 B.2
  have hA_tip : ∀ B ∈ F, A B.2 = diffSet B.1 B.2 := by
    intro B hB
    have hf : F.filter (fun B' => B'.2 = B.2) = {B} := by
      ext B'
      simp only [mem_filter, mem_singleton]
      exact ⟨fun h => htips B' h.1 B hB h.2, fun h => by subst h; exact ⟨hB, rfl⟩⟩
    simp only [A, hf, singleton_biUnion]
  have hA_none : ∀ x, (∀ B ∈ F, B.2 ≠ x) → A x = ∅ := by
    intro x hx
    have hf : F.filter (fun B => B.2 = x) = ∅ :=
      filter_eq_empty_iff.mpr fun B hB => hx B hB
    simp [A, hf]
  have hwing : ∀ x ∈ O, ∀ S ⊆ A x, flipSet x S ∈ O := by
    intro x hx S hS
    by_cases ht : ∃ B ∈ F, B.2 = x
    · obtain ⟨B, hB, rfl⟩ := ht
      rw [hA_tip B hB] at hS
      exact mem_biUnion.mpr ⟨B, hB, mem_image.mpr ⟨S, mem_powerset.mpr hS, rfl⟩⟩
    · simp only [not_exists, not_and] at ht
      rw [hA_none x ht, subset_empty] at hS
      subst hS
      rw [flipSet_empty]
      exact hx
  obtain ⟨τ, ha, -⟩ := wing_bijection n O A hwing
  have htipO : ∀ B ∈ F, B.2 ∈ O := fun B hB =>
    mem_biUnion.mpr ⟨B, hB, mem_image.mpr ⟨∅, empty_mem_powerset _, flipSet_empty _⟩⟩
  let f : Cube n × Cube n → Cube n := fun B =>
    if h : B.2 ∈ O then (τ ⟨B.2, h⟩).val else B.2
  have hf : ∀ B (hB : B ∈ F), f B = (τ ⟨B.2, htipO B hB⟩).val := fun B hB => by
    simp only [f, dif_pos (htipO B hB)]
  apply card_le_card_of_injOn f
  · intro B hB
    rw [hf B hB]
    refine mem_inter.mpr ⟨(τ _).property, mem_biUnion.mpr ⟨B, hB, ?_⟩⟩
    refine mem_filter.mpr ⟨mem_univ _, fun i hi => ?_⟩
    have hiA : i ∈ A B.2 := by rw [hA_tip B hB]; exact hi
    exact ha ⟨B.2, htipO B hB⟩ i hiA
  · intro B hB B' hB' h
    simp only [Finset.mem_coe] at hB hB'
    rw [hf B hB, hf B' hB'] at h
    have h2 := τ.injective (Subtype.ext h)
    exact htips B hB B' hB' (congrArg Subtype.val h2)

end WingBijection
