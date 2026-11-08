# A two-involution construction of wing bijections

This note describes the algorithm and its mathematical proof. The problem is to permute a finite
set of cube points while satisfying the prescribed wings and coordinatewise boundary bounds.
The construction uses finite involutions, permutations and integer counters, without determinants
or linear algebra.

The existence statement was proved by David Turturean in Theorem 3.1 of his
[Aaronson–Ambainis paper](https://github.com/physical-superintelligence/aaronson-ambainis).
His Section 9.5 asks for a direct combinatorial construction. The contribution described here is the
explicit construction and its correctness argument.

Let O be a finite subset of {0,1}^n, N = |O|. For each x in O, let A_x be a wing: x XOR S is in O for every S subset of A_x. Let E_j be the set of interior coordinate-j edges of O, e_j = |E_j|, and b_j = N - 2e_j. We construct a permutation tau of O with:

    tau(x)_j != x_j for every j in A_x;
    a_j(tau) := #{x : tau(x)_j = x_j} <= b_j for every j.

All orders below are fixed in advance: coordinates, vertices, and edges. Thus every move is deterministic.

For a permutation gamma of O write d_j(gamma) = #{x : gamma(x)_j != x_j}. Let sigma_j swap the two endpoints of every edge in E_j and fix the other points. It changes only coordinate j. Define

    pi_* = sigma_(n-1) o ... o sigma_1 o sigma_0.

Then a_j(pi_*) = b_j. Before sigma_j is applied, all preceding swaps preserve coordinate j, so each token still has its original j-bit. Sigma_j changes that bit at precisely 2e_j token positions. Subsequent swaps preserve that bit.

The algorithm's states consist of:

* a subset S_x of A_x for each x; put alpha(x) = x XOR S_x;
* a permutation pi of O;
* an ordered stack L of nonidentity permutations gamma of O satisfying gamma(x) = x XOR T_x with T_x subset of A_x;
* one nonnegative integer k_e for each interior edge e.

The map alpha need not be a permutation. Wing validity ensures it is a map from O to O.

In Lean, `LocalMap` stores `alpha` directly; the corresponding subset is uniquely recovered as `S_x = Δ(x, alpha(x))`.

Only states satisfying the following coordinatewise invariant are admitted:

    w_j := sum_x [j in S_x]
         + sum_x [alpha(x)_j = pi(x)_j]
         + sum_(gamma in L) d_j(gamma)
         + 2 sum_(e in E_j) k_e
         = b_j.                                                   (1)

Every term is nonnegative. The state space is finite: the subsets and permutations have finitely many choices; the counters are bounded by (1); and every nonidentity permutation in the stack has total displacement at least two. Hence the stack length is at most floor(sum_j b_j / 2).

The initial state c_* has all S_x empty, pi = pi_*, empty stack, and zero counters. It satisfies (1).

We construct two involutions, R and L, on this finite state space. The letter L for the involution is distinguished from the stack L by context.

The wing involution R is simple. If there is an x and j in A_x with pi(x)_j = x_j, choose the first such pair and toggle j in S_x. Otherwise leave the state fixed.

R is an involution because its choice depends only on pi. It preserves (1): in the toggled coordinate, the two relevant summands are either 0 + 1 or 1 + 0. The new alpha(x) is still in O by the wing assumption.

At an R-fixed state, pi changes every wing coordinate. For such a state,

    sum_x [j in S_x] + sum_x [alpha(x)_j = pi(x)_j]
      = a_j(pi) + 2 sum_x [j in S_x].                              (2)

Indeed, outside A_x the subset bit is zero and alpha(x)_j = x_j. Inside A_x, pi(x)_j is opposite x_j: an absent subset bit contributes zero, while a present bit contributes two. Equations (1) and (2) imply a_j(pi) <= b_j. Thus every R-fixed state gives the required output.

We next construct the normalization involution J on the special states

    a_j(pi) + 2 sum_(e in E_j) k_e = b_j,                          (3)

with no subsets or stack. J will have exactly one fixed state: (pi_*, all counters zero).

For i = 0,...,n, define C_i to consist of a permutation rho preserving all coordinates less than i, counters for edges in E_j with j >= i, and the constraints

    a_j(rho) + 2 sum_(e in E_j) k_e = b_j  for j >= i.

C_0 is precisely (3), and C_n consists of the identity permutation alone.

Define an involution T_i on C_i, for i < n. Write an edge in E_i as {u,v}, with u_i = 0 and v_i = 1. Call the edge normal if

    rho(u)_i = 1, rho(v)_i = 0, and k_e = 0.

Choose the first edge that is not normal. Swap rho(u) and rho(v), using this counter update:

| Bits (rho(u)_i, rho(v)_i) before the swap | Counter update |
| --- | --- |
| (0,1) | k_e <- k_e + 1 |
| (1,0), necessarily with k_e > 0 | k_e <- k_e - 1 |
| (0,0) or (1,1) | no change |

If every edge is normal, T_i fixes the state.

Each nonfixed move preserves C_i. In the first case a_i decreases by two, offset by the counter increase. The second is the inverse. The third changes no agreement count. For j != i, the sources u and v have the same j-bit, so swapping their targets preserves a_j. Previously preserved coordinates remain preserved as well. The same edge remains the first nonnormal edge after a move: the edges in E_i have disjoint endpoints. Thus T_i is an involution.

Suppose a state is T_i-fixed. All its E_i counters vanish, and all 2e_i interior vertices change coordinate i. By the constraint a_i = b_i = N - 2e_i, no other vertex changes coordinate i. Consequently

    rho' = rho o sigma_i

preserves coordinate i and all preceding coordinates. For j > i this relabeling preserves the total agreement count, since sigma_i changes only i. Deleting the zero E_i counters therefore gives a bijection

    f_i : Fix(T_i) -> C_(i+1).

Its inverse sends rho' to rho' o sigma_i and reinstates zero counters. This inverse changes i precisely at the interior vertices, so it satisfies the deleted constraint and normality conditions.

Here is J explicitly. Start with (pi,k) in C_0 and scan coordinates in order. At level i, apply T_i. If it changes the state, lift its mate back to C_0 through f_(i-1)^(-1),...,f_0^(-1), and return that mate. If T_i fixes the state, pass through f_i and continue. If every T_i fixes, return the original state unchanged.

This is an involution: for a nonfixed input, the lifted mate passes through the same earlier fixed levels and encounters the same first nonfixed T_i. A second application reverses that move and all relabelings. There is precisely one fixed input, because C_n is a singleton and every f_i is a bijection on the preceding fixed set. Lifting the identity back gives pi_* and zero counters. This proves the claimed property of J without using a counting identity or a determinant.

The full left involution L has four cases, in priority order.

1. If alpha is not injective, choose the first collision alpha(x) = alpha(y), x != y, and swap pi(x), pi(y). Leave everything else unchanged. This preserves (1), because the two alpha images are identical. The collision choice is unchanged, so the move is an involution.
2. If alpha is a nonidentity permutation, push alpha onto the front of the stack, replace pi by beta = pi o alpha^(-1), and make every S_x empty. This preserves (1), because

       sum_x [alpha(x)_j = pi(x)_j] = a_j(beta),
       sum_x [j in S_x] = d_j(alpha).

3. If alpha is the identity and the stack is nonempty, pop its first permutation gamma, set S_x = difference(x,gamma(x)), and replace pi by pi o gamma. The stack's defining wing condition makes these S_x valid. This is exactly the inverse of case 2, and preserves (1).
4. If alpha is the identity and the stack is empty, use J on (pi,k). Its input constraints are exactly (3), so the preceding lemma applies.

Case 1 stays in the noninjective-alpha class. Cases 2 and 3 pair each other. Case 4 stays in the identity-alpha, empty-stack class. Hence these rules together define an involution on the whole state space. Its only fixed state is c_*, by the unique-fixed-point property of J.

The construction is now:

    c <- c_*
    repeat:
        r <- R(c)
        if r = c:
            return c.pi
        c <- L(r)

To prove termination, form a finite undirected multigraph on the states. Join each state to its nontrivial L-mate and to its nontrivial R-mate, with different edge colors. Each vertex has at most one edge of each color. The initial state is the unique L-fixed vertex. If it is R-fixed too, the algorithm returns immediately. Otherwise it is an endpoint of a path.

The algorithm follows that path, alternating its edge colors. A finite path from an endpoint cannot enter a cycle or revisit a vertex. Its other endpoint must be fixed by an involution. There is no second L-fixed state, so that endpoint is R-fixed. Equation (2) then proves both required output conditions. This establishes termination and correctness for every dimension and every valid wing assignment.

The following state bound is an informal estimate, in terms of n and N = |O|, for an explicit table representation of states; it is not part of the Lean-verified statement. Put B = sum_j b_j and H = sum_x |A_x|. There are at most

    2^H N!
    * sum_(r=0)^floor(B/2) (N! - 1)^r
    * product_j (floor(b_j/2) + 1)^e_j

states, with the empty-stack term equal to one. The algorithm takes fewer than this many nontrivial moves. Informally, each move can be computed from the current state in time polynomial in n and N, and the current state alone fits in space polynomial in n and N. These are not formally verified complexity guarantees; in particular, the Lean implementation enumerates the whole cube {0,1}^n during initialization. No polynomial-time guarantee is asserted.

The Lean development in `WingBijection/` proves termination and both output conditions, and derives the whole-cube Butterfly Lemma. It uses the recursively defined normalization root directly; it does not separately identify that root with pi_* or formalize the complexity estimates above. See README.md and the accompanying manuscript for the formalization boundary.
