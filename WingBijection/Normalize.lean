import WingBijection.CubeBasics

/-! The nested edge-counter normalization `J` with a unique fixed point. -/

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option warn.classDefReducibility false

namespace WingBijection

open Finset

namespace WingSystem

variable {n : ℕ} (D : WingSystem n) [Fintype D.Point]

abbrev Ctr := Fin n × D.Point → ℕ

/-- Level `i`: permutations preserving coordinates `< i`, with edge counters on coordinates
`≥ i` and the coordinatewise budget identity. -/
def InC (i : ℕ) (q : Equiv.Perm D.Point × D.Ctr) : Prop :=
  (∀ j : Fin n, j.val < i → ∀ x, (q.1 x).val j = x.val j) ∧
  (∀ j : Fin n, i ≤ j.val → D.agr q.1 j + 2 * ∑ x, q.2 (j, x) = D.bnd j) ∧
  (∀ j x, q.2 (j, x) ≠ 0 → i ≤ j.val ∧ D.LowerInt j x)

abbrev C (i : ℕ) := {q : Equiv.Perm D.Point × D.Ctr // D.InC i q}

/-- An edge (named by its lower endpoint) that is not yet normal. -/
def EBad (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr) (x : D.Point) : Prop :=
  D.LowerInt j x ∧
    ¬ ((q.1 x).val j = true ∧ (q.1 (D.sigma j x)).val j = false ∧ q.2 (j, x) = 0)

instance decEBad (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr) :
    DecidablePred (D.EBad j q) := by
  intro x
  unfold EBad
  infer_instance

def newk (a c : Bool) (k : ℕ) : ℕ :=
  if a = false ∧ c = true then k + 1 else if a = true ∧ c = false then k - 1 else k

def step (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr) (x : D.Point) :
    Equiv.Perm D.Point × D.Ctr := by
  exact (q.1 * Equiv.swap x (D.sigma j x),
    Function.update q.2 (j, x) (newk ((q.1 x).val j) ((q.1 (D.sigma j x)).val j) (q.2 (j, x))))

def Tq (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr) :
    Equiv.Perm D.Point × D.Ctr :=
  match pick (D.EBad j q) with
  | some x => D.step j q x
  | none => q

section lemmas

variable {D}

theorem lower_ne_sigma {j : Fin n} {x : D.Point} (h : D.LowerInt j x) : x ≠ D.sigma j x :=
  (D.sigma_ne_of_int j x h.2).symm

theorem sigma_bit_lower {j : Fin n} {x : D.Point} (h : D.LowerInt j x) :
    (D.sigma j x).val j = true := by
  rw [D.sigma_bit_int j x h.2, h.1]; rfl

theorem step_perm_x (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr) (x : D.Point) :
    (D.step j q x).1 x = q.1 (D.sigma j x) := by
  classical
  simp [step, Equiv.Perm.mul_apply]

theorem step_perm_sx (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr) (x : D.Point) :
    (D.step j q x).1 (D.sigma j x) = q.1 x := by
  classical
  simp [step, Equiv.Perm.mul_apply]

theorem step_perm_other (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr) (x y : D.Point)
    (h1 : y ≠ x) (h2 : y ≠ D.sigma j x) : (D.step j q x).1 y = q.1 y := by
  classical
  simp [step, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem step_ctr_x (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr) (x : D.Point) :
    (D.step j q x).2 (j, x) = newk ((q.1 x).val j) ((q.1 (D.sigma j x)).val j) (q.2 (j, x)) := by
  classical
  simp [step]

theorem step_ctr_other (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr) (x : D.Point)
    (e : Fin n × D.Point) (he : e ≠ (j, x)) : (D.step j q x).2 e = q.2 e := by
  classical
  simp [step, Function.update_of_ne he]

theorem swap_bit (j : Fin n) (x z : D.Point) {i : Fin n} (hi : i ≠ j) :
    (Equiv.swap x (D.sigma j x) z).val i = z.val i := by
  classical
  rcases eq_or_ne z x with rfl | h1
  · rw [Equiv.swap_apply_left, D.sigma_bit_ne j z hi]
  rcases eq_or_ne z (D.sigma j x) with rfl | h2
  · rw [Equiv.swap_apply_right, D.sigma_bit_ne j x hi]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem newk_newk (a c : Bool) (k : ℕ) (hbad : ¬ (a = true ∧ c = false ∧ k = 0)) :
    newk c a (newk a c k) = k := by
  cases a <;> cases c <;> simp_all [newk] <;> omega

theorem bad_step_iff (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr) (x : D.Point)
    (hx : D.EBad j q x) (y : D.Point) : D.EBad j (D.step j q x) y ↔ D.EBad j q y := by
  classical
  unfold EBad
  rcases eq_or_ne y x with rfl | hyx
  · rw [step_perm_x, step_perm_sx, step_ctr_x]
    refine ⟨fun _ => hx, fun _ => ⟨hx.1, ?_⟩⟩
    rintro ⟨h1, h2, h3⟩
    rw [h1, h2] at h3
    simp [newk] at h3
  · by_cases hy : D.LowerInt j y
    · have hy1 : y ≠ D.sigma j x := by
        intro h
        have := congrArg (fun z : D.Point => z.val j) h
        simp only [sigma_bit_lower hx.1, hy.1] at this
        exact Bool.false_ne_true this
      have hy2 : D.sigma j y ≠ x := by
        intro h
        have := congrArg (fun z : D.Point => z.val j) h
        simp only [sigma_bit_lower hy, hx.1.1] at this
        exact Bool.false_ne_true this.symm
      have hy3 : D.sigma j y ≠ D.sigma j x := by
        intro h
        exact hyx ((D.sigma j).injective h)
      rw [step_perm_other j q x y hyx hy1, step_perm_other j q x _ hy2 hy3,
        step_ctr_other j q x (j, y) (by simp [hyx])]
    · simp [hy]

theorem step_step (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr) (x : D.Point)
    (hx : D.EBad j q x) : D.step j (D.step j q x) x = q := by
  classical
  have hn : newk ((q.1 (D.sigma j x)).val j) ((q.1 x).val j)
      (newk ((q.1 x).val j) ((q.1 (D.sigma j x)).val j) (q.2 (j, x))) = q.2 (j, x) :=
    newk_newk _ _ _ hx.2
  ext1
  · show (q.1 * Equiv.swap x (D.sigma j x)) * Equiv.swap x (D.sigma j x) = q.1
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  · funext e
    by_cases he : e = (j, x)
    · subst he
      rw [step_ctr_x, step_perm_x, step_perm_sx, step_ctr_x]
      exact hn
    · rw [step_ctr_other j _ x e he, step_ctr_other j _ x e he]

theorem step_ne (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr) (x : D.Point)
    (hx : D.EBad j q x) : D.step j q x ≠ q := by
  intro h
  have := congrArg (fun r : Equiv.Perm D.Point × D.Ctr => r.1 x) h
  simp only [step_perm_x] at this
  exact lower_ne_sigma hx.1 (q.1.injective this).symm

theorem Tq_involutive (j : Fin n) : Function.Involutive (D.Tq j) := by
  intro q
  unfold Tq
  cases hp : pick (D.EBad j q) with
  | none => simp only [hp]
  | some x =>
    have hx := pick_some hp
    simp only
    rw [pick_congr (bad_step_iff j q x hx), hp]
    exact step_step j q x hx

theorem Tq_fixed_iff (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr) :
    D.Tq j q = q ↔ ∀ x, ¬ D.EBad j q x := by
  unfold Tq
  cases hp : pick (D.EBad j q) with
  | none => exact ⟨fun _ => pick_none hp, fun _ => rfl⟩
  | some x =>
    simp only
    have hx := pick_some hp
    exact ⟨fun h => absurd h (step_ne j q x hx), fun h => absurd hx (h x)⟩

/-- `step` keeps the level-`i` invariant when `j = i`. -/
theorem step_inC (i : ℕ) (j : Fin n) (hj : j.val = i) (q : Equiv.Perm D.Point × D.Ctr)
    (hq : D.InC i q) (x : D.Point) (hx : D.EBad j q x) : D.InC i (D.step j q x) := by
  classical
  obtain ⟨hP1, hP2, hP3⟩ := hq
  have hxs := lower_ne_sigma hx.1
  refine ⟨?_, ?_, ?_⟩
  · intro j' hj' z
    have hne : j' ≠ j := by intro h; subst h; omega
    show (q.1 (Equiv.swap x (D.sigma j x) z)).val j' = z.val j'
    rw [hP1 j' hj', swap_bit j x z hne]
  · intro j' hj'
    by_cases hjj : j' = j
    · subst hjj
      have hA := sum_two (fun z => if ((D.step j' q x).1 z).val j' = z.val j' then 1 else 0)
        (fun z => if (q.1 z).val j' = z.val j' then 1 else 0) x (D.sigma j' x) hxs
        (fun z h1 h2 => by simp only [step_perm_other j' q x z h1 h2])
      have hB := sum_one (fun z => (D.step j' q x).2 (j', z)) (fun z => q.2 (j', z)) x
        (fun z hz => step_ctr_other j' q x (j', z) (by simp [hz]))
      simp only [step_perm_x, step_perm_sx, step_ctr_x] at hA hB
      have hP := hP2 j' hj'
      unfold agr agreement at hP ⊢
      simp only [bits] at hP ⊢
      have hxb := hx.1.1
      have hsb := sigma_bit_lower hx.1
      have hbad := hx.2
      rw [hxb, hsb] at hA
      revert hA hB hP hbad
      generalize (q.1 x).val j' = a
      generalize (q.1 (D.sigma j' x)).val j' = c
      intro hA hB hP hbad
      cases a <;> cases c <;> simp_all [newk] <;> omega
    · have h1 : D.agr (D.step j q x).1 j' = D.agr q.1 j' :=
        D.agr_mul_of_preserve q.1 _ j' (fun z => swap_bit j x z hjj)
      have h2 : ∑ z, (D.step j q x).2 (j', z) = ∑ z, q.2 (j', z) :=
        sum_congr rfl fun z _ => step_ctr_other j q x (j', z) (by simp [hjj])
      rw [h1, h2]
      exact hP2 j' hj'
  · intro j' z hz
    by_cases he : (j', z) = (j, x)
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨hj.ge, hx.1⟩
    · rw [step_ctr_other j q x _ he] at hz
      exact hP3 j' z hz

end lemmas

def TC (i : ℕ) (hi : i < n) (q : D.C i) : D.C i :=
  ⟨D.Tq ⟨i, hi⟩ q.1, by
    unfold Tq
    cases hp : pick (D.EBad ⟨i, hi⟩ q.1) with
    | none => exact q.2
    | some x => exact step_inC i ⟨i, hi⟩ rfl q.1 q.2 x (pick_some hp)⟩

theorem TC_involutive (i : ℕ) (hi : i < n) : Function.Involutive (D.TC i hi) := by
  intro q
  apply Subtype.ext
  exact Tq_involutive ⟨i, hi⟩ q.1

section fixedEquiv

variable {D}

/-- In a fixed state of `T_i`, every interior point changes coordinate `i`. -/
theorem fixed_int_flips (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr)
    (hnb : ∀ x, ¬ D.EBad j q x) (z : D.Point) (hz : D.Int j z) :
    (q.1 z).val j ≠ z.val j := by
  cases hzb : z.val j with
  | false =>
    have hl : D.LowerInt j z := ⟨hzb, hz⟩
    have h := not_not.mp (fun h => hnb z ⟨hl, h⟩)
    rw [h.1]; simp
  | true =>
    have hl : D.LowerInt j (D.sigma j z) := by
      refine ⟨?_, D.int_sigma j z hz⟩
      rw [D.sigma_bit_int j z hz, hzb]; rfl
    have h := not_not.mp (fun h => hnb _ ⟨hl, h⟩)
    rw [D.sigma_sigma] at h
    rw [h.2.1]; simp

theorem fixed_ctr_zero (i : ℕ) (j : Fin n) (q : Equiv.Perm D.Point × D.Ctr) (hq : D.InC i q)
    (hnb : ∀ x, ¬ D.EBad j q x) (x : D.Point) : q.2 (j, x) = 0 := by
  by_contra h
  have hl := (hq.2.2 j x h).2
  have hn := not_not.mp (fun h' => hnb x ⟨hl, h'⟩)
  exact h hn.2.2

theorem toNext_inC (i : ℕ) (hi : i < n) (q : Equiv.Perm D.Point × D.Ctr) (hq : D.InC i q)
    (hnb : ∀ x, ¬ D.EBad ⟨i, hi⟩ q x) : D.InC (i + 1) (q.1 * D.sigma ⟨i, hi⟩, q.2) := by
  classical
  set j : Fin n := ⟨i, hi⟩
  obtain ⟨hP1, hP2, hP3⟩ := hq
  have hz0 := fixed_ctr_zero i j q ⟨hP1, hP2, hP3⟩ hnb
  have hagr : D.agr q.1 j = D.bnd j := by
    have := hP2 j le_rfl
    simp only [hz0, sum_const_zero, Nat.mul_zero, Nat.add_zero] at this
    exact this
  have hbd := D.boundary_keeps q.1 j (fixed_int_flips j q hnb) hagr
  refine ⟨?_, ?_, ?_⟩
  · intro j' hj' z
    show (q.1 (D.sigma j z)).val j' = z.val j'
    by_cases hjj : j' = j
    · subst hjj
      by_cases hz : D.Int j z
      · have h1 := fixed_int_flips j q hnb _ (D.int_sigma j z hz)
        rw [D.sigma_bit_int j z hz] at h1
        revert h1
        cases (q.1 (D.sigma j z)).val j <;> cases z.val j <;> simp
      · rw [D.sigma_of_not_int j z hz]
        exact hbd z hz
    · have hlt : j'.val < i := by
        have : j'.val ≠ i := fun h => hjj (Fin.ext h)
        omega
      rw [hP1 j' hlt, D.sigma_bit_ne j z hjj]
  · intro j' hj'
    have hjj : j' ≠ j := by intro h; subst h; simp [j] at hj'
    rw [D.agr_mul_of_preserve q.1 _ j' (fun z => D.sigma_bit_ne j z hjj)]
    exact hP2 j' (by omega)
  · intro j' z hz
    have h := hP3 j' z hz
    refine ⟨?_, h.2⟩
    have hjj : j' ≠ j := by
      intro he; subst he; exact hz (hz0 z)
    have : j'.val ≠ i := fun h => hjj (Fin.ext h)
    omega

theorem fromNext_inC (i : ℕ) (hi : i < n) (r : Equiv.Perm D.Point × D.Ctr)
    (hr : D.InC (i + 1) r) : D.InC i (r.1 * D.sigma ⟨i, hi⟩, r.2) := by
  classical
  set j : Fin n := ⟨i, hi⟩
  obtain ⟨hP1, hP2, hP3⟩ := hr
  have hz0 : ∀ x, r.2 (j, x) = 0 := by
    intro x; by_contra h; have := (hP3 j x h).1; simp [j] at this
  refine ⟨?_, ?_, ?_⟩
  · intro j' hj' z
    have hjj : j' ≠ j := by intro h; subst h; simp [j] at hj'
    show (r.1 (D.sigma j z)).val j' = z.val j'
    rw [hP1 j' (by omega), D.sigma_bit_ne j z hjj]
  · intro j' hj'
    by_cases hjj : j' = j
    · subst hjj
      rw [D.agr_mul_sigma_of_preserve r.1 j (hP1 j (by simp [j]))]
      simp [hz0]
    · have hlt : i + 1 ≤ j'.val := by
        have : j'.val ≠ i := fun h => hjj (Fin.ext h)
        omega
      rw [D.agr_mul_of_preserve r.1 _ j' (fun z => D.sigma_bit_ne j z hjj)]
      exact hP2 j' hlt
  · intro j' z hz
    have h := hP3 j' z hz
    exact ⟨by omega, h.2⟩

theorem fromNext_noBad (i : ℕ) (hi : i < n) (r : Equiv.Perm D.Point × D.Ctr)
    (hr : D.InC (i + 1) r) (x : D.Point) : ¬ D.EBad ⟨i, hi⟩ (r.1 * D.sigma ⟨i, hi⟩, r.2) x := by
  set j : Fin n := ⟨i, hi⟩
  rintro ⟨hl, hn⟩
  apply hn
  have hpres : ∀ z, (r.1 z).val j = z.val j := hr.1 j (by simp [j])
  refine ⟨?_, ?_, ?_⟩
  · show (r.1 (D.sigma j x)).val j = true
    rw [hpres, sigma_bit_lower hl]
  · show (r.1 (D.sigma j (D.sigma j x))).val j = false
    rw [D.sigma_sigma, hpres, hl.1]
  · by_contra h
    have := (hr.2.2 j x h).1
    simp [j] at this

end fixedEquiv

def fixedEquiv (i : ℕ) (hi : i < n) :
    RootedInvolution.Fixed (D.TC i hi) ≃ D.C (i + 1) where
  toFun q := ⟨(q.1.1.1 * D.sigma ⟨i, hi⟩, q.1.1.2),
    toNext_inC i hi q.1.1 q.1.2 ((Tq_fixed_iff _ _).mp (congrArg Subtype.val q.2))⟩
  invFun r := ⟨⟨(r.1.1 * D.sigma ⟨i, hi⟩, r.1.2), fromNext_inC i hi r.1 r.2⟩, by
    apply Subtype.ext
    exact (Tq_fixed_iff _ _).mpr (fromNext_noBad i hi r.1 r.2)⟩
  left_inv q := by
    apply Subtype.ext; apply Subtype.ext
    show (q.1.1.1 * D.sigma ⟨i, hi⟩ * D.sigma ⟨i, hi⟩, q.1.1.2) = q.1.1
    rw [mul_assoc, D.sigma_mul_self, mul_one]
  right_inv r := by
    apply Subtype.ext
    show (r.1.1 * D.sigma ⟨i, hi⟩ * D.sigma ⟨i, hi⟩, r.1.2) = r.1
    rw [mul_assoc, D.sigma_mul_self, mul_one]

/-- Beyond the last coordinate the level is a singleton. -/
def uniqueC (i : ℕ) (hi : n ≤ i) : Unique (D.C i) where
  default := ⟨(1, 0), by
    refine ⟨fun _ _ _ => rfl, fun j hj => absurd hj (by omega), fun _ _ h => absurd rfl h⟩⟩
  uniq q := by
    apply Subtype.ext
    obtain ⟨⟨p, k⟩, hP1, _, hP3⟩ := q
    ext1
    · ext z j
      exact congrArg (fun b => b) (by simpa using hP1 j (by omega) z)
    · funext e
      by_contra h
      have := (hP3 e.1 e.2 h).1
      omega

def Jfrom (i : ℕ) : RootedInvolution (D.C i) :=
  if hi : i < n then
    RootedInvolution.lift (D.TC i hi) (D.TC_involutive i hi) (D.fixedEquiv i hi) (Jfrom (i + 1))
  else
    @RootedInvolution.terminal _ (D.uniqueC i (by omega))
termination_by n - i

/-- The normalization involution on the level-0 states. -/
def J0 : RootedInvolution (D.C 0) := D.Jfrom 0

end WingSystem

end WingBijection
