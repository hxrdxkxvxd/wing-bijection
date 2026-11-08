import WingBijection.Normalize
import Mathlib.Data.Fintype.BigOperators

/-! Full auxiliary state space, the involutions `R` and `L`, and the unconditional assembly. -/

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace WingBijection

open Finset

namespace WingSystem

variable {n : ℕ} (D : WingSystem n) [Fintype D.Point]

abbrev Raw := RawAux D.LocalMap (Equiv.Perm D.Point) (Equiv.Perm D.Point) (Fin n × D.Point)

def IsLocalPerm (γ : Equiv.Perm D.Point) : Prop :=
  ∀ x j, j ∉ D.A x → (γ x).val j = x.val j

def stackW (l : List (Equiv.Perm D.Point)) (j : Fin n) : ℕ :=
  (l.map fun γ => displacement D.bits γ j).sum

def Good (s : D.Raw) : Prop :=
  (∀ γ ∈ s.stack, γ ≠ 1 ∧ D.IsLocalPerm γ) ∧
  (∀ e, s.counters e ≠ 0 → D.LowerInt e.1 e.2) ∧
  (∀ j, pairWeight D.bits s.alpha.val s.perm j + D.stackW s.stack j +
      2 * ∑ x, s.counters (j, x) = D.bnd j)

abbrev St := {s : D.Raw // D.Good s}

def idL : D.LocalMap := ⟨id, fun _ _ _ => rfl⟩

/-! ### Weight identities -/

section weights

variable {D}

theorem bitCost_self (a c : Bool) : bitCost a a c = if c = a then 1 else 0 := by
  cases a <;> cases c <;> rfl

theorem bitCost_eq (a b c : Bool) :
    bitCost a b c = (if b ≠ a then 1 else 0) + (if c = b then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem pw_id (q : Equiv.Perm D.Point) (j : Fin n) :
    pairWeight D.bits (id : D.Point → D.Point) q j = D.agr q j := by
  unfold pairWeight agr agreement
  apply sum_congr rfl
  intro x _
  exact bitCost_self _ _

theorem pw_split (γ q : Equiv.Perm D.Point) (j : Fin n) :
    pairWeight D.bits γ q j = displacement D.bits γ j + D.agr (q * γ⁻¹) j := by
  classical
  unfold pairWeight displacement agr agreement
  have h2 : ∑ y, (if D.bits ((q * γ⁻¹) y) j = D.bits y j then 1 else 0) =
      ∑ x, (if D.bits (q x) j = D.bits (γ x) j then 1 else 0) := by
    rw [← Equiv.sum_comp γ]
    apply sum_congr rfl
    intro x _
    simp [Equiv.Perm.mul_apply]
  rw [h2, ← sum_add_distrib]
  apply sum_congr rfl
  intro x _
  exact bitCost_eq _ _ _

theorem stackW_cons (γ : Equiv.Perm D.Point) (l : List (Equiv.Perm D.Point)) (j : Fin n) :
    D.stackW (γ :: l) j = displacement D.bits γ j + D.stackW l j := by
  simp [stackW]

theorem stackW_nil (j : Fin n) : D.stackW [] j = 0 := by simp [stackW]

theorem bitCost_swap (x y c p q : Bool) :
    bitCost x c q + bitCost y c p = bitCost x c p + bitCost y c q := by
  cases x <;> cases y <;> cases c <;> cases p <;> cases q <;> rfl

end weights

/-! ### Finiteness -/

def wt (γ : Equiv.Perm D.Point) : ℕ := by
  exact (∑ j, displacement D.bits γ j) + if γ = 1 then 1 else 0

theorem wt_pos (γ : Equiv.Perm D.Point) : 0 < D.wt γ := by
  classical
  unfold wt
  by_cases h : γ = 1
  · simp [h]
  · have := total_displacement_pos D.bits D.bits_injective γ h
    omega

theorem wt_sum (l : List (Equiv.Perm D.Point)) (hl : ∀ γ ∈ l, γ ≠ 1) :
    (l.map D.wt).sum = ∑ j, D.stackW l j := by
  classical
  induction l with
  | nil => simp [stackW]
  | cons γ rest ih =>
    simp only [List.map_cons, List.sum_cons, stackW_cons, sum_add_distrib]
    rw [ih (fun g hg => hl g (List.mem_cons_of_mem _ hg))]
    unfold wt
    simp [hl γ List.mem_cons_self]

theorem good_bound (s : D.Raw) (hs : D.Good s) :
    (s.stack.map D.wt).sum + (∑ e, s.counters e) ≤ ∑ j, D.bnd j := by
  classical
  have h3 := hs.2.2
  have hsum : ∑ j, (pairWeight D.bits s.alpha.val s.perm j + D.stackW s.stack j +
      2 * ∑ x, s.counters (j, x)) = ∑ j, D.bnd j := sum_congr rfl fun j _ => h3 j
  rw [sum_add_distrib, sum_add_distrib] at hsum
  have hle : ∑ j, ∑ x, s.counters (j, x) ≤ ∑ j, 2 * ∑ x, s.counters (j, x) :=
    sum_le_sum fun j _ => by omega
  rw [D.wt_sum s.stack (fun g hg => (hs.1 g hg).1), Fintype.sum_prod_type]
  omega

instance finite_St : Finite D.St := by
  classical
  have hfin := finite_weighted_aux (A := D.LocalMap) (P := Equiv.Perm D.Point)
    (G := Equiv.Perm D.Point) (E := Fin n × D.Point) D.wt D.wt_pos (∑ j, D.bnd j)
  exact Finite.of_injective (fun s : D.St => (⟨s.1, D.good_bound s.1 s.2⟩ :
      {s : D.Raw // (s.stack.map D.wt).sum + (∑ e, s.counters e) ≤ ∑ j, D.bnd j}))
    (fun a b h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext h')

noncomputable instance fintype_St : Fintype D.St := Fintype.ofFinite _

/-! ### The wing involution `R` -/

def Rmap (s : D.St) : D.St :=
  ⟨{ s.1 with alpha := D.repair s.1.perm s.1.alpha },
    ⟨s.2.1, s.2.2.1, fun j => by
      have h := D.repair_weight s.1.perm s.1.alpha j
      have h3 := s.2.2.2 j
      simp only at h ⊢
      rw [h]
      exact h3⟩⟩

theorem Rmap_involutive : Function.Involutive D.Rmap := by
  intro s
  apply Subtype.ext
  show RawAux.mk _ _ _ _ = s.1
  congr 1
  exact D.repair_involutive s.1.perm s.1.alpha

/-! ### The left involution `L` -/

def Coll (a : D.Point → D.Point) (xy : D.Point × D.Point) : Prop :=
  xy.1 ≠ xy.2 ∧ a xy.1 = a xy.2

instance decColl (a : D.Point → D.Point) : DecidablePred (D.Coll a) := by
  intro xy
  unfold Coll
  infer_instance

def collide (s : D.St) (xy : D.Point × D.Point) : D.St := by
  exact if h : D.Coll s.1.alpha.val xy then
    ⟨{ s.1 with perm := s.1.perm * Equiv.swap xy.1 xy.2 },
      ⟨s.2.1, s.2.2.1, fun j => by
        have h3 := s.2.2.2 j
        have hpw : pairWeight D.bits s.1.alpha.val (s.1.perm * Equiv.swap xy.1 xy.2) j =
            pairWeight D.bits s.1.alpha.val s.1.perm j := by
          unfold pairWeight
          have hs := sum_two
            (fun z => bitCost (D.bits z j) (D.bits (s.1.alpha.val z) j)
              (D.bits ((s.1.perm * Equiv.swap xy.1 xy.2) z) j))
            (fun z => bitCost (D.bits z j) (D.bits (s.1.alpha.val z) j)
              (D.bits (s.1.perm z) j)) xy.1 xy.2 h.1
            (fun z h1 h2 => by
              simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2])
          have e1 : (s.1.perm * Equiv.swap xy.1 xy.2) xy.1 = s.1.perm xy.2 := by
            simp [Equiv.Perm.mul_apply]
          have e2 : (s.1.perm * Equiv.swap xy.1 xy.2) xy.2 = s.1.perm xy.1 := by
            simp [Equiv.Perm.mul_apply]
          beta_reduce at hs
          rw [e1, e2, h.2] at hs
          have hb := bitCost_swap (D.bits xy.1 j) (D.bits xy.2 j) (D.bits (s.1.alpha.val xy.2) j)
            (D.bits (s.1.perm xy.1) j) (D.bits (s.1.perm xy.2) j)
          omega
        simp only
        rw [hpw]
        exact h3⟩⟩
    else s

def push (s : D.St) : D.St := by
  exact if h : Function.Injective s.1.alpha.val ∧ s.1.alpha.val ≠ id then
    let γ : Equiv.Perm D.Point := permOfInj _ h.1
    ⟨⟨D.idL, s.1.perm * γ⁻¹, γ :: s.1.stack, s.1.counters⟩,
      ⟨by
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · refine ⟨fun h1 => h.2 ?_, s.1.alpha.property⟩
          funext x
          have := congrArg (fun e : Equiv.Perm D.Point => e x) h1
          simpa [γ] using this
        · exact s.2.1 g hg,
       s.2.2.1, fun j => by
        have h3 := s.2.2.2 j
        have hs := pw_split γ s.1.perm j
        simp only [idL]
        rw [pw_id, stackW_cons]
        have : pairWeight D.bits s.1.alpha.val s.1.perm j =
            pairWeight D.bits (γ : D.Point → D.Point) s.1.perm j := rfl
        omega⟩⟩
    else s

def pop (s : D.St) : D.St := by
  exact if h : s.1.alpha.val = id ∧ s.1.stack ≠ [] then
    let γ := s.1.stack.head h.2
    have hγ : γ ∈ s.1.stack := List.head_mem h.2
    ⟨⟨⟨γ, (s.2.1 γ hγ).2⟩, s.1.perm * γ, s.1.stack.tail, s.1.counters⟩,
      ⟨fun g hg => s.2.1 g (List.mem_of_mem_tail hg), s.2.2.1, fun j => by
        have h3 := s.2.2.2 j
        have hs := pw_split γ (s.1.perm * γ) j
        rw [mul_inv_cancel_right] at hs
        have hst : s.1.stack = γ :: s.1.stack.tail := (List.cons_head_tail h.2).symm
        rw [hst, stackW_cons, h.1, pw_id] at h3
        simp only
        omega⟩⟩
    else s

theorem inC0_of (s : D.St) (h : s.1.alpha.val = id ∧ s.1.stack = []) :
    D.InC 0 (s.1.perm, s.1.counters) := by
  refine ⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun j _ => ?_,
    fun j x hx => ⟨Nat.zero_le _, s.2.2.1 (j, x) hx⟩⟩
  have h3 := s.2.2.2 j
  rw [h.1, h.2, pw_id, stackW_nil] at h3
  simpa using h3

def ofC0 (s : D.St) (h : s.1.alpha.val = id ∧ s.1.stack = []) (c : D.C 0) :
    D.St :=
  ⟨⟨s.1.alpha, c.1.1, s.1.stack, c.1.2⟩,
    ⟨(by intro g hg; rw [h.2] at hg; cases hg),
     fun e he => (c.2.2.2 e.1 e.2 he).2,
     fun j => by
      have h2 := c.2.2.1 j (Nat.zero_le _)
      simp only
      rw [h.1, h.2, pw_id, stackW_nil]
      simpa using h2⟩⟩

def norm (s : D.St) : D.St := by
  exact if h : s.1.alpha.val = id ∧ s.1.stack = [] then
    D.ofC0 s h (D.J0.map ⟨(s.1.perm, s.1.counters), D.inC0_of s h⟩)
    else s

def Lmap (s : D.St) : D.St :=
  match pick (D.Coll s.1.alpha.val) with
  | some xy => D.collide s xy
  | none => if s.1.alpha.val = id then (if s.1.stack = [] then D.norm s else D.pop s)
      else D.push s

/-! ### Properties of the pieces -/

section props

variable {D}

theorem collide_alpha (s : D.St) (xy : D.Point × D.Point) :
    (D.collide s xy).1.alpha = s.1.alpha := by
  unfold collide; split <;> rfl

theorem collide_spec (s : D.St) (xy : D.Point × D.Point) (h : D.Coll s.1.alpha.val xy) :
    (D.collide s xy).1 = ⟨s.1.alpha, s.1.perm * Equiv.swap xy.1 xy.2, s.1.stack, s.1.counters⟩ := by
  unfold collide; rw [dif_pos h]

theorem collide_collide (s : D.St) (xy : D.Point × D.Point) (h : D.Coll s.1.alpha.val xy) :
    D.collide (D.collide s xy) xy = s := by
  have h' : D.Coll (D.collide s xy).1.alpha.val xy := by rw [collide_alpha]; exact h
  apply Subtype.ext
  rw [collide_spec _ _ h', collide_spec _ _ h]
  simp only [mul_assoc, Equiv.swap_mul_self, mul_one]

theorem collide_ne (s : D.St) (xy : D.Point × D.Point) (h : D.Coll s.1.alpha.val xy) :
    D.collide s xy ≠ s := by
  intro he
  have e1 := congrArg (fun t : D.St => t.1.perm xy.1) he
  unfold collide at e1
  rw [dif_pos h] at e1
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at e1
  exact h.1 (s.1.perm.injective e1).symm

theorem noColl_iff (a : D.Point → D.Point) : (∀ xy, ¬ D.Coll a xy) ↔ Function.Injective a := by
  constructor
  · intro h x y hxy
    by_contra hne
    exact h (x, y) ⟨hne, hxy⟩
  · rintro h ⟨x, y⟩ ⟨hne, hxy⟩
    exact hne (h hxy)

theorem push_spec (s : D.St) (h : Function.Injective s.1.alpha.val ∧ s.1.alpha.val ≠ id) :
    (D.push s).1 = ⟨D.idL, s.1.perm * (permOfInj _ h.1)⁻¹,
      (permOfInj _ h.1) :: s.1.stack, s.1.counters⟩ := by
  unfold push; rw [dif_pos h]

theorem pop_spec (s : D.St) (h : s.1.alpha.val = id ∧ s.1.stack ≠ []) :
    (D.pop s).1.alpha.val = s.1.stack.head h.2 ∧
    (D.pop s).1.perm = s.1.perm * s.1.stack.head h.2 ∧
    (D.pop s).1.stack = s.1.stack.tail ∧ (D.pop s).1.counters = s.1.counters := by
  unfold pop; rw [dif_pos h]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem norm_spec (s : D.St) (h : s.1.alpha.val = id ∧ s.1.stack = []) :
    D.norm s = D.ofC0 s h (D.J0.map ⟨(s.1.perm, s.1.counters), D.inC0_of s h⟩) := by
  unfold norm; rw [dif_pos h]

theorem Lmap_some (s : D.St) (xy : D.Point × D.Point) (hp : pick (D.Coll s.1.alpha.val) = some xy) :
    D.Lmap s = D.collide s xy := by
  unfold Lmap; rw [hp]

theorem Lmap_none (s : D.St) (hp : pick (D.Coll s.1.alpha.val) = none) :
    D.Lmap s = if s.1.alpha.val = id then (if s.1.stack = [] then D.norm s else D.pop s)
      else D.push s := by
  unfold Lmap; rw [hp]

theorem pick_none_of_inj (s : D.St) (h : Function.Injective s.1.alpha.val) :
    pick (D.Coll s.1.alpha.val) = none :=
  pick_none_of ((noColl_iff _).mpr h)

theorem pop_push (s : D.St) (h : Function.Injective s.1.alpha.val ∧ s.1.alpha.val ≠ id) :
    D.pop (D.push s) = s := by
  have hp := push_spec s h
  have h' : (D.push s).1.alpha.val = id ∧ (D.push s).1.stack ≠ [] := by
    rw [hp]; exact ⟨rfl, by simp⟩
  obtain ⟨e1, e2, e3, e4⟩ := pop_spec (D.push s) h'
  apply Subtype.ext
  apply RawAux.ext
  · apply Subtype.ext
    rw [e1]; simp only [hp, List.head_cons]; rfl
  · rw [e2]; simp only [hp, List.head_cons, inv_mul_cancel_right]
  · rw [e3, hp]; rfl
  · rw [e4, hp]

theorem push_pop (s : D.St) (h : s.1.alpha.val = id ∧ s.1.stack ≠ []) :
    D.push (D.pop s) = s := by
  obtain ⟨e1, e2, e3, e4⟩ := pop_spec s h
  have hγ := (s.2.1 _ (List.head_mem h.2)).1
  have h' : Function.Injective (D.pop s).1.alpha.val ∧ (D.pop s).1.alpha.val ≠ id := by
    rw [e1]
    refine ⟨(s.1.stack.head h.2).injective, fun h2 => hγ ?_⟩
    ext x; simp [show ((s.1.stack.head h.2 : Equiv.Perm D.Point) x) = x from congrFun h2 x]
  have hp := push_spec (D.pop s) h'
  have hg : permOfInj _ h'.1 = s.1.stack.head h.2 := by
    ext x; simp [e1]
  apply Subtype.ext
  rw [hp, hg]
  apply RawAux.ext
  · apply Subtype.ext; exact h.1.symm
  · simp [e2]
  · simp only [e3]; exact List.cons_head_tail h.2
  · exact e4

end props

theorem Lmap_involutive : Function.Involutive D.Lmap := by
  intro s
  cases hp : pick (D.Coll s.1.alpha.val) with
  | some xy =>
    have hc := pick_some hp
    rw [D.Lmap_some s xy hp]
    have hp' : pick (D.Coll (D.collide s xy).1.alpha.val) = some xy := by
      rw [collide_alpha]; exact hp
    rw [D.Lmap_some _ xy hp', collide_collide s xy hc]
  | none =>
    have hinj := (noColl_iff _).mp (pick_none hp)
    rw [D.Lmap_none s hp]
    by_cases ha : s.1.alpha.val = id
    · rw [if_pos ha]
      by_cases hst : s.1.stack = []
      · rw [if_pos hst]
        have hn := norm_spec s ⟨ha, hst⟩
        have ha' : (D.norm s).1.alpha.val = id := by rw [hn]; exact ha
        have hst' : (D.norm s).1.stack = [] := by rw [hn]; exact hst
        rw [D.Lmap_none _ (D.pick_none_of_inj _ (by rw [ha']; exact Function.injective_id)),
          if_pos ha', if_pos hst', norm_spec _ ⟨ha', hst'⟩]
        have hc : (⟨((D.norm s).1.perm, (D.norm s).1.counters), D.inC0_of _ ⟨ha', hst'⟩⟩ : D.C 0)
            = D.J0.map ⟨(s.1.perm, s.1.counters), D.inC0_of s ⟨ha, hst⟩⟩ :=
          Subtype.ext (by show ((D.norm s).1.perm, (D.norm s).1.counters) = _; rw [hn]; rfl)
        rw [hc, D.J0.involutive]
        apply Subtype.ext
        apply RawAux.ext
        · show (D.norm s).1.alpha = s.1.alpha
          rw [hn]; rfl
        · rfl
        · show (D.norm s).1.stack = s.1.stack
          rw [hn]; rfl
        · rfl
      · rw [if_neg hst]
        obtain ⟨e1, _, _, _⟩ := pop_spec s ⟨ha, hst⟩
        have hinj' : Function.Injective (D.pop s).1.alpha.val := by
          rw [e1]; exact (s.1.stack.head hst).injective
        have hne : (D.pop s).1.alpha.val ≠ id := by
          rw [e1]; intro h2
          apply (s.2.1 _ (List.head_mem hst)).1
          ext x; simp [show ((s.1.stack.head hst : Equiv.Perm D.Point) x) = x from congrFun h2 x]
        rw [D.Lmap_none _ (D.pick_none_of_inj _ hinj'), if_neg hne]
        exact push_pop s ⟨ha, hst⟩
    · rw [if_neg ha]
      have hps := push_spec s ⟨hinj, ha⟩
      have ha' : (D.push s).1.alpha.val = id := by rw [hps]; rfl
      have hst' : (D.push s).1.stack ≠ [] := by rw [hps]; simp
      rw [D.Lmap_none _ (D.pick_none_of_inj _ (by rw [ha']; exact Function.injective_id)),
        if_pos ha', if_neg hst']
      exact pop_push s ⟨hinj, ha⟩

/-- The unique `L`-fixed anchor. -/
def anchor : D.St :=
  ⟨⟨D.idL, D.J0.root.1.1, [], D.J0.root.1.2⟩,
    ⟨(by intro g hg; cases hg),
     fun e he => (D.J0.root.2.2.2 e.1 e.2 he).2,
     fun j => by
      have h2 := D.J0.root.2.2.1 j (Nat.zero_le _)
      simp only [idL]
      rw [pw_id, stackW_nil]
      simpa using h2⟩⟩

theorem Lmap_fixed_iff (s : D.St) : D.Lmap s = s ↔ s = D.anchor := by
  constructor
  · intro hf
    cases hp : pick (D.Coll s.1.alpha.val) with
    | some xy =>
      rw [D.Lmap_some s xy hp] at hf
      exact absurd hf (collide_ne s xy (pick_some hp))
    | none =>
      have hinj := (noColl_iff _).mp (pick_none hp)
      rw [D.Lmap_none s hp] at hf
      by_cases ha : s.1.alpha.val = id
      · rw [if_pos ha] at hf
        by_cases hst : s.1.stack = []
        · rw [if_pos hst, norm_spec s ⟨ha, hst⟩] at hf
          set c : D.C 0 := ⟨(s.1.perm, s.1.counters), D.inC0_of s ⟨ha, hst⟩⟩
          have hc : D.J0.map c = c := by
            apply Subtype.ext
            have e1 := congrArg (fun t : D.St => t.1.perm) hf
            have e2 := congrArg (fun t : D.St => t.1.counters) hf
            exact Prod.ext e1 e2
          have hr := (D.J0.fixed_iff c).mp hc
          apply Subtype.ext
          apply RawAux.ext
          · exact Subtype.ext ha
          · show s.1.perm = D.J0.root.1.1; rw [← hr]
          · exact hst
          · show s.1.counters = D.J0.root.1.2; rw [← hr]
        · rw [if_neg hst] at hf
          obtain ⟨_, _, e3, _⟩ := pop_spec s ⟨ha, hst⟩
          have := congrArg (fun t : D.St => t.1.stack.length) hf
          simp only [e3, List.length_tail] at this
          have hpos := List.length_pos_iff.mpr hst
          omega
      · rw [if_neg ha] at hf
        have hps := push_spec s ⟨hinj, ha⟩
        have := congrArg (fun t : D.St => t.1.stack.length) hf
        simp only [hps, List.length_cons] at this
        omega
  · rintro rfl
    have hid : D.anchor.1.alpha.val = id := rfl
    rw [D.Lmap_none _ (D.pick_none_of_inj _ (by rw [hid]; exact Function.injective_id)),
      if_pos hid, if_pos (show D.anchor.1.stack = [] from rfl), norm_spec _ ⟨hid, rfl⟩]
    have hroot : D.J0.map D.J0.root = D.J0.root := (D.J0.fixed_iff _).mpr rfl
    apply Subtype.ext
    apply RawAux.ext
    · rfl
    · show (D.J0.map ⟨(D.J0.root.1.1, D.J0.root.1.2), _⟩).1.1 = D.J0.root.1.1
      rw [show (⟨(D.J0.root.1.1, D.J0.root.1.2), _⟩ : D.C 0) = D.J0.root from rfl, hroot]
    · rfl
    · show (D.J0.map ⟨(D.J0.root.1.1, D.J0.root.1.2), _⟩).1.2 = D.J0.root.1.2
      rw [show (⟨(D.J0.root.1.1, D.J0.root.1.2), _⟩ : D.C 0) = D.J0.root from rfl, hroot]

end WingSystem

end WingBijection
