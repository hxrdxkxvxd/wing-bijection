import WingBijection
import Lean.Util.FoldConsts
import Lean.Compiler.NoncomputableAttr

#print axioms WingBijection.construct_correct
#print axioms WingBijection.checkedConstruct_correct
#print axioms WingBijection.wing_bijection
#print axioms WingBijection.butterfly_lemma
#print axioms WingBijection.WingSystem.Lmap_involutive
#print axioms WingBijection.WingSystem.Jfrom
#check @WingBijection.construct
#check @WingBijection.construct_correct
#check @WingBijection.wing_bijection
#check @WingBijection.butterfly_lemma

-- Reimer's Butterfly Lemma (Smyth's formulation, Remark 3.10 of the paper) in plain cube terms.
example (n : ℕ) (F : Finset ((Fin n → Bool) × (Fin n → Bool)))
    (htips : ∀ B ∈ F, ∀ B' ∈ F, B.2 = B'.2 → B = B') :
    F.card ≤ (F.biUnion (fun B => (Finset.univ.filter fun i => B.1 i ≠ B.2 i).powerset.image
        (fun S i => if i ∈ S then !B.2 i else B.2 i)) ∩
      F.biUnion (fun B => Finset.univ.filter fun y =>
        ∀ i ∈ Finset.univ.filter (fun i => B.1 i ≠ B.2 i), y i ≠ B.2 i)).card :=
  WingBijection.butterfly_lemma n F htips

-- Non-vacuity: two butterflies spanning the square with opposite tips; the red sets cover the
-- square, the yellow sets are the two antipodes, and the intersection has exactly two points.
example :
    let F : Finset (WingBijection.Cube 2 × WingBijection.Cube 2) :=
      {(fun _ => true, fun _ => false), (fun _ => false, fun _ => true)}
    (F.biUnion WingBijection.red).card = 4 ∧
      (F.biUnion WingBijection.red ∩ F.biUnion WingBijection.yellow).card = 2 := by
  decide

-- Restate the theorem in plain finite Boolean cube terms, with no WingSystem input,
-- normalization certificate, rooted involution, or determinant assumption.
example (n : ℕ) (O : Finset (Fin n → Bool))
    (A : (Fin n → Bool) → Finset (Fin n))
    (hA : ∀ x ∈ O, ∀ S ⊆ A x,
      (fun i => if i ∈ S then !x i else x i) ∈ O) :
    ∃ τ : Equiv.Perm {x // x ∈ O},
      (∀ x : {x // x ∈ O}, ∀ i ∈ A x.val, (τ x).val i ≠ x.val i) ∧
      ∀ j : Fin n,
        (Finset.univ.filter fun x : {x // x ∈ O} => (τ x).val j = x.val j).card ≤
        (O.filter fun x => Function.update x j (!x j) ∉ O).card :=
  WingBijection.wing_bijection n O A hA

open Lean Elab Command

-- Audit the transitive mathematical dependencies and fail on an unexpected axiom
-- or a dependency on the old conditional scaffolding or determinant machinery.
run_cmd do
  let env ← getEnv
  let mut pending := [`WingBijection.construct_correct, `WingBijection.checkedConstruct_correct,
    `WingBijection.butterfly_lemma]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if !seen.contains name then
      seen := seen.insert name
      if let some info := env.find? name then
        for dep in info.getUsedConstantsAsSet do
          if !seen.contains dep then pending := dep :: pending
  let mut axioms : Array String := #[]
  let mut flagged : Array String := #[]
  for name in seen do
    let s := name.toString
    if let some (.axiomInfo _) := env.find? name then
      axioms := axioms.push s
      unless name == `propext || name == `Classical.choice || name == `Quot.sound do
        throwError "Unexpected axiom: {name}"
    if s.startsWith "Matrix.det" || s.startsWith "AaronsonAmbainis." ||
        s.startsWith "MvPolynomial." || s == "sorryAx" ||
        s.startsWith "Lean.ofReduceBool" || s.startsWith "Lean.trustCompiler" then
      flagged := flagged.push s
  unless flagged.isEmpty do throwError "Flagged dependencies: {flagged}"
  if seen.contains `WingBijection.conditional_scheme_correct then
    throwError "The final theorem uses conditional scaffolding"
  unless seen.contains `WingBijection.WingSystem.Lmap_involutive &&
      seen.contains `WingBijection.WingSystem.Jfrom do
    throwError "The concrete involution construction is missing"
  let runtimeNames := #[`WingBijection.pick, `WingBijection.chooseFinite,
    `WingBijection.permOfInj, `WingBijection.cubeList,
    `WingBijection.WingSystem.repair, `WingBijection.WingSystem.Jfrom,
    `WingBijection.WingSystem.Lmap, `WingBijection.WingSystem.anchor,
    `WingBijection.WingSystem.bakeMap, `WingBijection.WingSystem.canonicalFreeze,
    `WingBijection.WingSystem.canonicalAdvance,
    `WingBijection.finiteWalk, `WingBijection.WingSystem.run,
    `WingBijection.construct, `WingBijection.checkedConstruct]
  for name in runtimeNames do
    if isNoncomputable env name then throwError "Noncomputable runtime entry point: {name}"
  let foreign := env.header.moduleNames.filter fun name =>
    name.toString.startsWith "AaronsonAmbainis" || name.toString.startsWith "PSI"
  unless foreign.isEmpty do throwError "Unexpected PSI imports: {foreign}"
  let matrices := env.header.moduleNames.filter fun name =>
    name.toString.startsWith "Mathlib.LinearAlgebra" ||
    name.toString.startsWith "Mathlib.Data.Matrix"
  logInfo m!"DEPENDENCY AXIOMS: {axioms}"
  logInfo m!"FLAGGED DEPENDENCIES: {flagged}"
  logInfo m!"CONDITIONAL SCHEME USED: false"
  logInfo m!"CONCRETE INVOLUTIONS USED: true"
  logInfo m!"COMPUTABLE RUNTIME ENTRY POINTS: {runtimeNames.size}"
  logInfo m!"PSI IMPORT MODULES: {foreign}"
  logInfo m!"MATRIX OR LINEAR-ALGEBRA IMPORT MODULES: {matrices}"
