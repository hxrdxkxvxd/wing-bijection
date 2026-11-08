# A two-involution construction of wing bijections

This project constructs a permutation of a finite subset of the Boolean cube, given a valid wing
at each point. The permutation changes every required wing coordinate, while keeping each
coordinate unchanged at no more points than its boundary count permits.

The algorithm alternates two explicit involutions on a finite state space. Its termination and
correctness are proved in Lean 4, and the construction compiles to an executable program.
The project also proves Reimer's Butterfly Lemma in the whole-cube formulation stated below.
The proofs use no determinants or linear algebra.

**Manuscript draft:** [PDF](paper/paper.pdf).

## Start here

- **Understand the mathematics:** read [PROOF.md](PROOF.md).
- **Inspect the formal statements:** see [Main.lean](WingBijection/Main.lean) for the wing
  bijection and [Butterfly.lean](WingBijection/Butterfly.lean) for its Butterfly Lemma corollary.
- **Follow the algorithm:** start with [Runner.lean](WingBijection/Runner.lean), then
  [FullState.lean](WingBijection/FullState.lean) and [Normalize.lean](WingBijection/Normalize.lean).
- **Reproduce the checks:** follow [Reproduce](#reproduce), run [Audit.lean](Audit.lean),
  and run [verify_outputs.py](verify_outputs.py). The remaining modules contain supporting
  definitions and proofs; the [Layout](#layout) table maps them.

## The theorem

For a finite set `O` of points of the Boolean cube and wings `A x` (flipping any subset of `A x` stays in
`O`), `construct` returns a permutation `τ` of `O` such that

* (a) `τ x` differs from `x` in every coordinate of `A x`;
* (b) for every coordinate `j`, the number of `x` with `(τ x) j = x j` is at most the number of
  `j`-boundary points of `O`.

```lean
theorem construct_correct (n : ℕ) (O : Finset (Cube n)) (A : Cube n → Finset (Fin n))
    (hA : ∀ x ∈ O, ∀ S ⊆ A x, flipSet x S ∈ O) :
    (∀ x : {x // x ∈ O}, ∀ i ∈ A x.val, (construct n O A hA x).val i ≠ x.val i) ∧
    ∀ j : Fin n, (univ.filter fun x : {x // x ∈ O} =>
        (construct n O A hA x).val j = x.val j).card ≤
      (O.filter fun x => Function.update x j (!x j) ∉ O).card
```

`wing_bijection` is the existential corollary of `construct_correct`. The final theorems depend only on
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). There is no `sorry`, no custom
axiom and no import from the PSI project. `Audit.lean` checks all of this mechanically.

## Corollary: Reimer's Butterfly Lemma

In the whole-cube formulation discussed by Smyth and recalled in Turturean's Remark 3.10: a butterfly `B = (a, b)` has body
`a` and tip `b`, with `Red B = {b^S : S ⊆ Δ(a, b)}` and `Yellow B = {y : y i ≠ b i for all i ∈ Δ(a, b)}`.

```lean
theorem butterfly_lemma (n : ℕ) (F : Finset (Cube n × Cube n))
    (htips : ∀ B ∈ F, ∀ B' ∈ F, B.2 = B'.2 → B = B') :
    F.card ≤ (F.biUnion red ∩ F.biUnion yellow).card
```

The proof applies part (a) with `O` the union of the red sets, the wing `Δ(a, b)` at each tip and
empty wings elsewhere, and then uses injectivity. Hall's theorem is not needed in this direction.

The mathematical argument for the construction is written out in [PROOF.md](PROOF.md)
and in the [manuscript draft](paper/paper.pdf).

## Reproduce

Requires [elan](https://github.com/leanprover/elan) (Lean 4.33.0 and mathlib are pinned) and Python 3.

```sh
lake exe cache get          # mathlib build cache
lake build                  # check all proofs
lake env lean Audit.lean    # axioms, signatures, dependency audit
lake build wingDemo
lake exe wingDemo           # nine-point example
python3 verify_outputs.py   # independent check of program outputs
```

Custom input: `lake exe wingDemo n points wing_masks`. Points and wing masks are comma-separated
integers, with coordinate 0 as the least significant bit and one mask per point. For example:
`lake exe wingDemo 3 0,1,2,5,6,7 2,0,2,2,4,2`.
Exit codes: 0 success, 1 invalid wings, 2 malformed input, 3 failed output check.

## Relation to previous work

David Turturean proved the existence of a wing bijection in his
[Aaronson–Ambainis paper](https://psi.inc/research/aaronson-ambainis/), using a determinant
argument (his Theorem 3.1); his Section 9.5 asks for a direct combinatorial construction. This
project's contribution is the explicit two-involution construction and its correctness proof.

Turturean's Remark 3.10 explains the relation to Reimer's Butterfly Lemma and discusses
linear-algebraic proofs. This project formalizes the implication from wing compatibility to the
Butterfly Lemma. The converse uses Hall's theorem and is not needed or formalized here.

## Scope

- The general guarantees are termination and the two output conditions for every valid wing
  assignment, together with the stated whole-cube Butterfly Lemma corollary.
- No polynomial running-time bound or formal complexity theorem is established. The implementation
  enumerates all `2^n` cube points at start-up. The state-count estimate in `PROOF.md` is informal.
- The manuscript identifies the normalization root with an explicit product of edge switches.
  Lean uses the recursively constructed root directly and does not separately formalize that identity.
- The complete Aaronson–Ambainis proof with this construction substituted is not formalized here.

## Layout

| Path | Contents |
| --- | --- |
| `WingBijection/Involutions.lean`, `Normalization.lean` | Alternating-involution termination; lifting a rooted involution |
| `WingBijection/Weights.lean`, `WingRepair.lean`, `Finiteness.lean` | Weight invariant, wing-repair involution `R`, finiteness of states |
| `WingBijection/CubeBasics.lean`, `Normalize.lean` | Cube edges and switches; edge-counter involutions and the normalization `J` |
| `WingBijection/FullState.lean` | State space, left involution `L`, unique anchor |
| `WingBijection/Effective.lean`, `EffectiveCube.lean`, `Memo.lean`, `Canonical.lean`, `Runner.lean` | Executable choices, enumeration and the verified walk |
| `WingBijection/Main.lean`, `Checked.lean` | `construct`, `construct_correct`, `wing_bijection`, input validation |
| `WingBijection/Butterfly.lean` | `butterfly_lemma`, the corollary |
| `Demo.lean` | Command-line program |
| `Audit.lean` | Machine audit of axioms and dependencies |
| `verify_outputs.py` | Independent checker of the program's outputs |

## License

Apache-2.0.
