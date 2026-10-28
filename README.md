# QuadraticFloor

Lean 4 / Mathlib formalization of the floor-sum results in J. S. Farland, *Quadratic Floor Sums,
Class Numbers, and the Trace of a Quartic Bernoulli Number* (manuscript, 2026).

For an odd prime `p` and integers `A, B, C` put

  `𝒮_{A,B,C}(p) = ∑_{n=0}^{p-1} (-1)^⌊(A n² + B n + C)/p⌋`.

The main results are:

- **Root count (Lemma 2.1).** If `A + B` is even and `p ∤ A`, then
  `𝒮_{A,B,C}(p) = (-1)^C (1 + 2 ∑_{j=0}^{(p-1)/2} ((D + 8Aj)/p))` with `D = B² - 4AC`.
- **Square-class decomposition (Theorem 3.2).** For a positive odd `A`, an odd prime `p ∤ A` and
  an admissible pair (`B` odd, `gcd(B, A) = 1`, `1 ≤ B² - 4AC < 4A`),
  `𝒮_{A,B,C}(p) = (-1)^C - (1/φ(A)) ∑_{ψ mod A} conj(ψ(B))² B_{1,ϑ_{p,ψ}}^{(8Ap)}`,
  where `ϑ_{p,ψ} = η_p χ_{-4}^{δ_ψ} ψ`, `η_p = χ_{-8p}` and `ψ(-1) = (-1)^{δ_ψ}`. So the sum depends
  only on the square class of `B` modulo `A` (Corollary 3.4).
- **The quartic split (Corollary 4.5).** For `p ≠ 2, 5`,
  `Re B_{1,Θ_p} = 𝒮_{5,3,0}(p) - 𝒮_{5,1,0}(p)`, where `Θ_p = η_p χ_{-4} ξ` has conductor `40p` and
  `ξ` is the quartic character modulo `5` with `ξ(2) = i`. The real part of a quartic Bernoulli
  number is a difference of two floor sums. It is an even integer, and
  `Re B_{1,Θ_p} ≡ 2(z_1 - z_3) (mod 4)` (Proposition 4.6).
- **The coefficients one and three (Theorems 4.1, 4.2)** in Bernoulli form, for example
  `𝒮_{1,1,0}(p) = 1 - B_{1,η_p}^{(8p)}`, which is `1 + h(-8p)` by Dirichlet's formula.
- **Monic shifts (Theorem 7.1).** For odd `a` the sum `𝒮_{1,a,b}(p)` is `𝒮_{1,1,0}(p) - 1` plus an
  explicit oriented sum of Legendre symbols; for even `a` it is an explicit finite expression,
  bounded by `1 + 2|a/2|` and eventually constant in `p`.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

```
lake exe cache get
lake build
```

No `sorry`, no `native_decide`. Every result depends only on `propext`, `Classical.choice` and
`Quot.sound`.

## Scope, hypotheses and limitations

- **No class numbers.** Mathlib does not connect Bernoulli numbers of quadratic characters to class
  numbers, so the class-number statements of the paper are formalized in Bernoulli form. The
  identities `B_{1,χ_D} = -h(D)` (Dirichlet's class number formula) and the Euler-factor
  relations that turn them into `h(-8p)`, `h(-24p)` and `h(-40p)` are quoted, not proved.
- **Definitions of the characters.** `η_p` is defined as the Jacobi symbol `(-8p / x)` for odd `x`
  and `0` for even `x`, which is the Kronecker character `χ_{-8p}`. The paper's formula
  `η_p(x) = κ_p(x) (x/p)` is proved from it by quadratic reciprocity (`eta_eq`). Bernoulli numbers
  `B_{1,f}^{(q)} = (1/q) ∑_{x=1}^{q} x f(x)` are defined for any function `f`, and the paper's
  `χ_{-4}^0` is taken as `χ_{-4}²`, the principal character modulo 4. In the cases `A = 3` and
  `A = 5` the characters are written as explicit functions: `η_p` times the indicator of numbers
  prime to 3 (or 5), `η_p χ_{-4} (·/3)` for `χ_{-24p}`, and `η_p (·/5)` for `χ_{-40p}`.
- **Theorem 4.4** is formalized as its two linear combinations: the difference of the cases
  `B = 1, 3` (Corollary 4.5) and their sum (`quadratic_half`).
- **Proposition 4.6.** `z_B` records whether some `0 ≤ j ≤ (p-1)/2` has `p ∣ B² + 40 j`, which is
  equivalent to the paper's description through the unique solution `j_B`.
- **Theorem 7.1.** The odd case is stated with `𝒮_{1,1,0}(p) - 1` in place of `h(-8p)`.
  Eventual constancy is stated as the existence of `N` and `c` with `𝒮_{1,2t,b}(p) = c` for every
  prime `p > N`.
- **Not formalized:**
  - the fibre and trace corollaries (3.5, 3.6) and Corollary 4.3;
  - the quartic field `K_p` and `h(K_p) = |B_{1,Θ_p}|²/2` (Proposition 4.7, Corollary 4.8);
  - the conductor `8ℓp` theorem (5.1);
  - Section 6 (the collision theorem and the determinant certificates), which rests on class
    numbers of discriminants near `1.3 × 10^7` and on large determinants.

## Sources and novelty

The class-number content of the cases `A = 1` and `A = 3` is classical: Dirichlet-type formulas of
Hudson and Williams (1982) and of Godin and Williams (2005). The mechanism of Theorem 3.2 is the
coset averaging of Szmidt, Urbanowicz and Zagier (1995) together with character orthogonality.
The author found neither the floor-sum form of these identities nor the quartic split in the
sources searched (the Dirichlet-type literature, Berndt's survey, and Chamberland and Dilcher's
floor-sum papers). Novelty is claimed only relative to that search.

## Authorship, AI assistance and licence

The mathematics, the statements and the paper are by Joseph S. Farland. The Lean code was drafted
and repaired by Claude (Anthropic) against the paper's statements and proofs; the author chose the
scope and compared every statement in `Challenge.lean` with the paper. No external referee has
reviewed the paper or the formalization. The code is released under the Apache License 2.0
(`LICENSE`).

## Layout for the Palomar registry

- `Challenge.lean` is the statement surface a reader should audit. It restates the definitions
  exactly as the development has them and states the nineteen results with `sorry`.
- `Solution.lean` proves the same declarations from the development in `QuadraticFloor/`.
- `comparator.json` lists the compared theorems and definitions and the permitted axioms.
- `formalization.yaml` records authorship, sources, AI assistance, scope and fidelity.
- `scripts/` holds Palomar's checks, copied from the
  [Palomar starter template](https://github.com/PalomarRegistry/PalomarTemplate).

```
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh      # needs bubblewrap (bwrap)
```

| Paper | Challenge declaration |
|---|---|
| Lemma 2.1 (root count) | `root_count` |
| Equation (2.2) | `eta_eq` |
| Lemma 2.3 (window form) | `window_form` |
| Lemma 3.1 | `half_sum_zero_of_periodic`, `half_sum_zero_of_even`, `bern_antiperiodic` |
| **Theorem 3.2 (square-class decomposition)** | `square_class_decomposition` |
| Corollary 3.3 | `floorSum_universal` |
| Corollary 3.4 | `floorSum_eq_of_sq_modEq`, `exists_admissible` |
| Theorem 4.1 (Bernoulli form) | `floorSum_one` |
| Theorem 4.2 (Bernoulli form) | `floorSum_three` |
| Theorem 4.4 (sum of the two cases) | `quadratic_half` |
| **Corollary 4.5 (quartic split)** | `quartic_split` |
| Proposition 4.6 | `quartic_mod_four` |
| Theorem 7.1 | `monic_odd`, `monic_even`, `monic_even_bound`, `monic_even_eventually_const` |

## Files

| File | Contents |
|---|---|
| `Defs.lean` | `floorSum`, `Admissible`, `eta`, `bern`, `vartheta`, `xi`, `Theta`, `zB`, `osum` |
| `RootCount.lean` | the parity of the quotient, counting roots of a quadratic, Lemma 2.1 |
| `Eta.lean` | `κ_p`, equation (2.2), and the symmetries of `η_p` |
| `HalfPeriod.lean` | Lemma 3.1 and the vanishing of periodic Legendre-weighted sums |
| `SquareClass.lean` | the window form, orthogonality modulo `A` and `8`, Theorem 3.2 |
| `Corollaries.lean` | Corollaries 3.3 and 3.4, Theorems 4.1 and 4.2 |
| `CoefficientFive.lean` | the characters modulo 5, Theorem 4.4, Corollary 4.5, Proposition 4.6 |
| `Monic.lean` | oriented sums and Theorem 7.1 |
