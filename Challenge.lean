module

public import Mathlib

@[expose] public section

/-!
# Quadratic floor sums: statements

This file is the statement surface for the Palomar registry. It restates, with their exact
library definitions, the objects the results are about, and states each result with `sorry`.
`Solution.lean` proves every statement below with the same name and type, using the development
in `QuadraticFloor/`.

Throughout `p` is an odd prime (`[Fact p.Prime]` and `p ≠ 2`). Lemma 2.1 holds for all integers
`A`, `B` with `A + B` even; from Lemma 2.3 on, `A` is a positive odd integer.

## Definitions

* `floorSum A B C p = 𝒮_{A,B,C}(p) = ∑_{n=0}^{p-1} (-1)^{⌊(A n² + B n + C)/p⌋}` (integer division by
  the positive integer `p` rounds down).
* `Admissible A B C`: `B` odd, `gcd(B, A) = 1`, `1 ≤ B² - 4AC < 4A` (Definition 2.2).
* `eta p x = η_p(x) = χ_{-8p}(x)`: the Jacobi symbol `(-8p / x)` for odd `x`, `0` for even `x`.
* `bern q f = B_{1,f}^{(q)} = (1/q) ∑_{x=1}^{q} x f(x)`.
* `vartheta p ψ = ϑ_{p,ψ} = η_p χ_{-4}^{δ_ψ} ψ` for a Dirichlet character `ψ` modulo `A`, where
  `ψ(-1) = (-1)^{δ_ψ}` and `χ_{-4}^0 = χ_{-4}²` is the principal character modulo `4`.
* `xi` is the quartic character modulo `5` with `ξ(2) = i` (`lg5`, `xiFun` give its values), and
  `Theta p = Θ_p = η_p χ_{-4} ξ`.
* `zB B p ∈ {0, 1}`: whether some `0 ≤ j ≤ (p-1)/2` has `p ∣ B² + 40 j`.
* `osum t g = ∑*_{j=0}^{t-1} g(j)`, the oriented sum.
* `kap p = κ_p`, the component of `η_p` modulo `8`: `χ_{-8}` (Mathlib's `χ₈'`) if `p ≡ 1 (mod 4)`,
  and `χ_8` otherwise.

## Results (numbering of the paper)

* `root_count` (Lemma 2.1), `eta_eq` (equation (8), Section 2), `window_form` (Lemma 2.3).
* `half_sum_zero_of_periodic`, `half_sum_zero_of_even`, `bern_antiperiodic` (Lemma 3.1).
* `square_class_decomposition` (**Theorem 3.2**), `floorSum_universal` (Corollary 3.3),
  `floorSum_eq_of_sq_modEq`, `exists_admissible` (Corollary 3.4).
* `floorSum_one` (Theorem 4.1, Bernoulli form), `floorSum_three` (Theorem 4.2, Bernoulli form).
* `quartic_split` (**Corollary 4.5**: `Re B_{1,Θ_p} = 𝒮_{5,3,0}(p) - 𝒮_{5,1,0}(p)`),
  `quadratic_half` (Theorem 4.4, the quadratic half in Bernoulli form), `quartic_mod_four`
  (Proposition 4.6).
* `monic_odd`, `monic_even`, `monic_even_bound`, `monic_even_eventually_const` (Theorem 7.1).

Class numbers do not appear: the identities `B_{1,χ_D} = -h(D)` of Dirichlet's class number
formula, which turn the Bernoulli forms into the class-number statements of the paper, are not
formalized.
-/

namespace QuadraticFloor

open Finset

/-! ### Definitions -/

/-- **The quadratic floor sum** `𝒮_{A,B,C}(p) = ∑_{n=0}^{p-1} (-1)^{⌊(A n² + B n + C)/p⌋}`.
Integer division `/` by the positive integer `p` rounds down. -/
def floorSum (A B C : ℤ) (p : ℕ) : ℤ :=
  ∑ n ∈ range p, (((A * n ^ 2 + B * n + C) / (p : ℤ)).negOnePow : ℤ)

/-- **Admissibility** (Definition 2.2): `B` is odd, `gcd(B, A) = 1`, and
`1 ≤ B² - 4AC < 4A`. -/
def Admissible (A : ℕ) (B C : ℤ) : Prop :=
  Odd B ∧ Int.gcd B A = 1 ∧ 1 ≤ B ^ 2 - 4 * A * C ∧ B ^ 2 - 4 * A * C < 4 * A

/-- `η_p = χ_{-8p}`: the Jacobi symbol `(-8p / x)` for odd `x`, and `0` for even `x`. -/
def eta (p x : ℕ) : ℤ := if Even x then 0 else jacobiSym (-8 * p) x

/-- The first Bernoulli number `B_{1,f}^{(q)} = (1/q) ∑_{x=1}^{q} x f(x)`. -/
noncomputable def bern (q : ℕ) (f : ℕ → ℂ) : ℂ :=
  (1 / (q : ℂ)) * ∑ x ∈ Icc 1 q, (x : ℂ) * f x

open Classical in
/-- `ϑ_{p,ψ} = η_p χ_{-4}^{δ_ψ} ψ`, where `ψ(-1) = (-1)^{δ_ψ}`; here `χ_{-4}^1 = χ_{-4}` and
`χ_{-4}^0 = χ_{-4}²` is the principal character modulo `4`. -/
noncomputable def vartheta {A : ℕ} (p : ℕ) (ψ : DirichletCharacter ℂ A) (x : ℕ) : ℂ :=
  (eta p x : ℂ) *
    (if ψ (-1) = -1 then (ZMod.χ₄ (x : ZMod 4) : ℂ) else (ZMod.χ₄ (x : ZMod 4) : ℂ) ^ 2) *
    ψ (x : ZMod A)

/-- The index of a nonzero residue modulo `5` to the base `2`: `2^{lg x} = x`. -/
def lg5 (x : ZMod 5) : ℕ := if x = 2 then 1 else if x = 4 then 2 else if x = 3 then 3 else 0

/-- The values of the quartic character modulo `5` with `ξ(2) = i`: `ξ(x) = i^{lg x}` for
`x ≠ 0`. -/
noncomputable def xiFun (x : ZMod 5) : ℂ := if x = 0 then 0 else Complex.I ^ lg5 x

/-- **The quartic character `ξ` modulo `5` with `ξ(2) = i`**: `ξ(1) = 1`, `ξ(2) = i`,
`ξ(4) = -1`, `ξ(3) = -i`. -/
noncomputable def xi : DirichletCharacter ℂ 5 where
  toFun := xiFun
  map_one' := by
    simp only [xiFun, show (1 : ZMod 5) ≠ 0 by decide, ite_false, show lg5 1 = 0 by decide,
      pow_zero]
  map_mul' := by
    intro a b
    by_cases ha : a = 0
    · simp [xiFun, ha]
    by_cases hb : b = 0
    · simp [xiFun, hb]
    have hab : a * b ≠ 0 := by revert a b; decide
    have hlg : lg5 (a * b) % 4 = (lg5 a + lg5 b) % 4 := by revert a b; decide
    simp only [xiFun, ha, hb, hab, ite_false, ← pow_add]
    rw [← Nat.mod_add_div (lg5 (a * b)) 4, ← Nat.mod_add_div (lg5 a + lg5 b) 4, hlg, pow_add,
      pow_add, pow_mul, pow_mul, Complex.I_pow_four, one_pow, one_pow]
  map_nonunit' := by
    intro a ha
    by_cases h0 : a = 0
    · simp [xiFun, h0]
    · exfalso
      apply ha
      obtain ⟨b, hb⟩ : ∃ b : ZMod 5, a * b = 1 := by revert a; decide
      exact IsUnit.of_mul_eq_one b hb

/-- `Θ_p = η_p χ_{-4} ξ`, the quartic character of conductor `40p`. -/
noncomputable def Theta (p x : ℕ) : ℂ :=
  (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) * xi (x : ZMod 5)

/-- `z_B = 1` if some `j` with `0 ≤ j ≤ (p-1)/2` has `p ∣ B² + 40 j`, and `0` otherwise. -/
def zB (B : ℤ) (p : ℕ) : ℤ :=
  if ∃ j ∈ range ((p + 1) / 2), (p : ℤ) ∣ B ^ 2 + 40 * j then 1 else 0

/-- The oriented sum `∑*_{j=0}^{t-1} g(j)`: `∑_{j=0}^{t-1} g(j)` for `t ≥ 0`, and
`-∑_{j=t}^{-1} g(j)` for `t < 0`. -/
def osum (t : ℤ) (g : ℤ → ℤ) : ℤ :=
  if 0 ≤ t then ∑ j ∈ Ico 0 t, g j else -∑ j ∈ Ico t 0, g j

/-- `κ_p`, the component of `η_p` modulo `8`. -/
def kap (p : ℕ) : MulChar (ZMod 8) ℤ := if p % 4 = 1 then ZMod.χ₈' else ZMod.χ₈

/-! ### Section 2: parity and reduction -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Lemma 2.1 (root count).** If `A + B` is even and `p ∤ A`, then
`𝒮_{A,B,C}(p) = (-1)^C (1 + 2 ∑_{j=0}^{(p-1)/2} ((B² - 4AC + 8Aj)/p))`. -/
theorem root_count (hp2 : p ≠ 2) {A B : ℤ} (C : ℤ) (hAB : Even (A + B)) (hpA : ¬ (p : ℤ) ∣ A) :
    floorSum A B C p = (C.negOnePow : ℤ) *
      (1 + 2 * ∑ j ∈ range ((p + 1) / 2), legendreSym p (B ^ 2 - 4 * A * C + 8 * A * j)) := sorry

/-- **Equation (8) of Section 2.** `η_p(x) = κ_p(x) (x/p)`. -/
theorem eta_eq (hp2 : p ≠ 2) (x : ℕ) : eta p x = kap p x * legendreSym p x := sorry

/-- **Lemma 2.3 (window form).** For an admissible pair, `𝒮_{A,B,C}(p) - (-1)^C` is twice the sum
of `η_p(x)` over the `x ∈ [1, 4Ap]` with `x ≡ B² - 4AC (mod 8A)`. -/
theorem window_form (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A) {B C : ℤ}
    (hBC : Admissible A B C) :
    floorSum A B C p - (C.negOnePow : ℤ) =
      2 * ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = (B ^ 2 - 4 * A * C).toNat),
        eta p x := sorry

/-! ### Section 3: the square-class decomposition -/

/-- **Lemma 3.1(1).** A function with `f(x + h) = f(x)` and zero sum over `[1, 2h]` has zero sum
over `[1, h]`. This is the paper's argument with `q = 2h`: periodicity makes the full sum twice
the half sum, and for a nonprincipal character modulo `q` the full sum is zero. Here the vanishing
of the full sum is a hypothesis, so the statement itself is immediate from periodicity. -/
theorem half_sum_zero_of_periodic (f : ℕ → ℂ) {h : ℕ} (hf : ∀ x, f (x + h) = f x)
    (hfull : ∑ x ∈ Icc 1 (2 * h), f x = 0) : ∑ x ∈ Icc 1 h, f x = 0 := sorry

/-- **Lemma 3.1(2).** A function with `f(x + h) = -f(x)`, `f(0) = 0` and `f(2h - x) = f(x)` has
zero sum over `[1, h]`. For an even character modulo `q = 2h` with `4 ∣ q`, the last two
hypotheses are `ϑ(0) = 0` and `ϑ(-x) = ϑ(x)`. -/
theorem half_sum_zero_of_even (f : ℕ → ℂ) {h : ℕ} (hf : ∀ x, f (x + h) = -f x) (h0 : f 0 = 0)
    (hrefl : ∀ x ≤ 2 * h, f (2 * h - x) = f x) : ∑ x ∈ Icc 1 h, f x = 0 := sorry

/-- **Lemma 3.1(3).** If `f(x + h) = -f(x)`, then `B_{1,f}^{(2h)} = -(1/2) ∑_{x=1}^{h} f(x)`. -/
theorem bern_antiperiodic (f : ℕ → ℂ) {h : ℕ} (hh : 0 < h) (hf : ∀ x, f (x + h) = -f x) :
    bern (2 * h) f = -(1 / 2) * ∑ x ∈ Icc 1 h, f x := sorry

/-- **Theorem 3.2 (square-class decomposition).** For an admissible pair `(B, C)`,
`𝒮_{A,B,C}(p) = (-1)^C - (1/φ(A)) ∑_{ψ mod A} conj(ψ(B))² B_{1,ϑ_{p,ψ}}^{(8Ap)}`.
The instance argument `[NeZero A]`, needed to form `DirichletCharacter ℂ A`, is implied by
`Odd A`. -/
theorem square_class_decomposition (hp2 : p ≠ 2) {A : ℕ} [NeZero A] (hA : Odd A)
    (hpA : ¬ p ∣ A) {B C : ℤ} (hBC : Admissible A B C) :
    (floorSum A B C p : ℂ) = (C.negOnePow : ℤ) - (1 / (A.totient : ℂ)) *
      ∑ ψ : DirichletCharacter ℂ A, (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 *
        bern (8 * A * p) (vartheta p ψ) := sorry

/-- **Corollary 3.3.** `𝒮_{A,1,0}(p) = 1 - (1/φ(A)) ∑_ψ B_{1,ϑ_{p,ψ}}^{(8Ap)}`
(`[NeZero A]` is implied by `Odd A`). -/
theorem floorSum_universal (hp2 : p ≠ 2) {A : ℕ} [NeZero A] (hA : Odd A) (hpA : ¬ p ∣ A) :
    (floorSum A 1 0 p : ℂ) = 1 - (1 / (A.totient : ℂ)) *
      ∑ ψ : DirichletCharacter ℂ A, bern (8 * A * p) (vartheta p ψ) := sorry

/-- **Corollary 3.4.** Admissible pairs with the same square class `B² mod A` give the same floor
sum and the same sign `(-1)^C`. -/
theorem floorSum_eq_of_sq_modEq (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A)
    {B C B' C' : ℤ} (h : Admissible A B C) (h' : Admissible A B' C')
    (hBB : B ^ 2 ≡ B' ^ 2 [ZMOD A]) :
    floorSum A B C p = floorSum A B' C' p ∧ C.negOnePow = C'.negOnePow := sorry

/-- **Corollary 3.4, every square class arises.** Every unit residue class `B₀` modulo `A`, hence
every square class `B₀² mod A`, has an admissible representative `B ≡ B₀ (mod A)`. -/
theorem exists_admissible {A : ℕ} (hA : Odd A) {B₀ : ℤ} (hB₀ : Int.gcd B₀ A = 1) :
    ∃ B C : ℤ, Admissible A B C ∧ B ≡ B₀ [ZMOD A] := sorry

/-! ### Section 4: the first odd coefficients -/

/-- **Theorem 4.1, Bernoulli form.** `𝒮_1(p) = ∑_{n<p} (-1)^{⌊n(n+1)/p⌋} = 1 - B_{1,η_p}^{(8p)}`
(which is `1 + h(-8p)` by Dirichlet's class number formula). -/
theorem floorSum_one (hp2 : p ≠ 2) :
    (floorSum 1 1 0 p : ℂ) = 1 - bern (8 * p) (fun x => (eta p x : ℂ)) := sorry

/-- **Theorem 4.2, Bernoulli form.** `𝒮_3(p) = 1 - (B_{1,η_p}^{(24p)} + B_{1,χ_{-24p}}^{(24p)})/2`,
with `η_p` induced to modulus `24p` and `χ_{-24p} = η_p χ_{-4} (·/3)`. -/
theorem floorSum_three (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (floorSum 3 1 0 p : ℂ) = 1 - (1 / 2) *
      (bern (24 * p) (fun x => (eta p x : ℂ) * (if 3 ∣ x then 0 else 1)) +
        bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
          (legendreSym 3 x : ℂ))) := sorry

/-- **Theorem 4.4, the quadratic half, Bernoulli form.**
`𝒮_{5,1,0}(p) + 𝒮_{5,3,0}(p) - 2 = -(B_{1,η_p}^{(40p)} + B_{1,χ_{-40p}}^{(40p)})/2`, with `η_p`
induced to modulus `40p` and `χ_{-40p} = η_p (·/5)`. -/
theorem quadratic_half (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((floorSum 5 1 0 p + floorSum 5 3 0 p - 2 : ℤ) : ℂ) = -(1 / 2) *
      (bern (40 * p) (fun x => (eta p x : ℂ) * (if 5 ∣ x then 0 else 1)) +
        bern (40 * p) (fun x => (eta p x : ℂ) * (jacobiSym x 5 : ℂ))) := sorry

/-- **Corollary 4.5 (the quartic split), equation (23).**
`Re B_{1,Θ_p} = 𝒮_{5,3,0}(p) - 𝒮_{5,1,0}(p)`. Together with `quadratic_half` this is Theorem 4.4
in Bernoulli form. The real part does not depend on the choice `ξ(2) = i`: replacing `ξ` by `ξ̄`
replaces `B_{1,Θ_p}` by its complex conjugate. -/
theorem quartic_split (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((floorSum 5 3 0 p - floorSum 5 1 0 p : ℤ) : ℝ) = (bern (40 * p) (Theta p)).re := sorry

/-- **Proposition 4.6.** `Re B_{1,Θ_p}` is an integer congruent to `2 (z_1 - z_3)` modulo `4`. -/
theorem quartic_mod_four (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ∃ m : ℤ, (bern (40 * p) (Theta p)).re = m ∧ m ≡ 2 * (zB 1 p - zB 3 p) [ZMOD 4] := sorry

/-! ### Section 7: monic shifts -/

/-- **Theorem 7.1(1).** For `a = 2t + 1` and `b' = b - t(t+1)`,
`𝒮_{1,a,b}(p) = (𝒮_1(p) - 1) + (-1)^{b'} - 2 ∑*_{j=0}^{b'-1} (-1)^j ((-4j-3)/p)`. -/
theorem monic_odd (hp2 : p ≠ 2) (t b : ℤ) :
    floorSum 1 (2 * t + 1) b p = (floorSum 1 1 0 p - 1) + ((b - t * (t + 1)).negOnePow : ℤ) -
      2 * osum (b - t * (t + 1)) (fun j => (j.negOnePow : ℤ) * legendreSym p (-4 * j - 3)) :=
  sorry

/-- **Theorem 7.1(2).** For `a = 2t` and `b' = b - t²`,
`𝒮_{1,a,b}(p) = (-1)^{⌊b'/p⌋} - 2 ∑*_{m=0}^{t-1} (-1)^{⌊(m² + b')/p⌋}`. -/
theorem monic_even (hp2 : p ≠ 2) (t b : ℤ) :
    floorSum 1 (2 * t) b p = (((b - t ^ 2) / (p : ℤ)).negOnePow : ℤ) -
      2 * osum t (fun m => (((m ^ 2 + (b - t ^ 2)) / (p : ℤ)).negOnePow : ℤ)) := sorry

/-- **Theorem 7.1(2), the bound.** `|𝒮_{1,2t,b}(p)| ≤ 1 + 2|t|`. -/
theorem monic_even_bound (hp2 : p ≠ 2) (t b : ℤ) :
    |floorSum 1 (2 * t) b p| ≤ 1 + 2 * |t| := sorry

/-- **Theorem 7.1(2), eventual constancy.** For fixed `t` and `b`, `𝒮_{1,2t,b}(p)` takes one
value for all sufficiently large primes `p`. -/
theorem monic_even_eventually_const (t b : ℤ) :
    ∃ N : ℕ, ∃ c : ℤ, ∀ p : ℕ, p.Prime → N < p → floorSum 1 (2 * t) b p = c := sorry

end QuadraticFloor
