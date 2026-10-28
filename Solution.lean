module

public import QuadraticFloor

public section

/-!
# Proved solution

Each declaration below has exactly the statement of its counterpart in `Challenge.lean` and is
proved from the development in `QuadraticFloor/`. The definitions used in the statements are those
of `QuadraticFloor/Defs.lean` and `QuadraticFloor/Eta.lean`, and are compared with the copies in
`Challenge.lean`.
-/

namespace QuadraticFloor

open Finset

/-! ### Section 2: parity and reduction -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Lemma 2.1 (root count).** If `A + B` is even and `p ∤ A`, then
`𝒮_{A,B,C}(p) = (-1)^C (1 + 2 ∑_{j=0}^{(p-1)/2} ((B² - 4AC + 8Aj)/p))`. -/
theorem root_count (hp2 : p ≠ 2) {A B : ℤ} (C : ℤ) (hAB : Even (A + B)) (hpA : ¬ (p : ℤ) ∣ A) :
    floorSum A B C p = (C.negOnePow : ℤ) *
      (1 + 2 * ∑ j ∈ range ((p + 1) / 2), legendreSym p (B ^ 2 - 4 * A * C + 8 * A * j)) :=
  root_count' hp2 C hAB hpA

/-- **Equation (2.2).** `η_p(x) = κ_p(x) (x/p)`. -/
theorem eta_eq (hp2 : p ≠ 2) (x : ℕ) : eta p x = kap p x * legendreSym p x :=
  eta_eq' hp2 x

/-- **Lemma 2.3 (window form).** For an admissible pair, `𝒮_{A,B,C}(p) - (-1)^C` is twice the sum
of `η_p(x)` over the `x ∈ [1, 4Ap]` with `x ≡ B² - 4AC (mod 8A)`. -/
theorem window_form (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A) {B C : ℤ}
    (hBC : Admissible A B C) :
    floorSum A B C p - (C.negOnePow : ℤ) =
      2 * ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = (B ^ 2 - 4 * A * C).toNat),
        eta p x :=
  window_form' hp2 hA hpA hBC

/-! ### Section 3: the square-class decomposition -/

/-- **Lemma 3.1(1).** A function with `f(x + h) = f(x)` and zero sum over `[1, 2h]` has zero sum
over `[1, h]`. -/
theorem half_sum_zero_of_periodic (f : ℕ → ℂ) {h : ℕ} (hf : ∀ x, f (x + h) = f x)
    (hfull : ∑ x ∈ Icc 1 (2 * h), f x = 0) : ∑ x ∈ Icc 1 h, f x = 0 :=
  half_sum_zero_of_periodic' f hf hfull

/-- **Lemma 3.1(2).** A function with `f(x + h) = -f(x)`, `f(0) = 0` and `f(2h - x) = f(x)` has
zero sum over `[1, h]`. -/
theorem half_sum_zero_of_even (f : ℕ → ℂ) {h : ℕ} (hf : ∀ x, f (x + h) = -f x) (h0 : f 0 = 0)
    (hrefl : ∀ x ≤ 2 * h, f (2 * h - x) = f x) : ∑ x ∈ Icc 1 h, f x = 0 :=
  half_sum_zero_of_even' f hf h0 hrefl

/-- **Lemma 3.1(3).** If `f(x + h) = -f(x)`, then `B_{1,f}^{(2h)} = -(1/2) ∑_{x=1}^{h} f(x)`. -/
theorem bern_antiperiodic (f : ℕ → ℂ) {h : ℕ} (hh : 0 < h) (hf : ∀ x, f (x + h) = -f x) :
    bern (2 * h) f = -(1 / 2) * ∑ x ∈ Icc 1 h, f x :=
  bern_antiperiodic' f hh hf

/-- **Theorem 3.2 (square-class decomposition).** For an admissible pair `(B, C)`,
`𝒮_{A,B,C}(p) = (-1)^C - (1/φ(A)) ∑_{ψ mod A} conj(ψ(B))² B_{1,ϑ_{p,ψ}}^{(8Ap)}`. -/
theorem square_class_decomposition (hp2 : p ≠ 2) {A : ℕ} [NeZero A] (hA : Odd A)
    (hpA : ¬ p ∣ A) {B C : ℤ} (hBC : Admissible A B C) :
    (floorSum A B C p : ℂ) = (C.negOnePow : ℤ) - (1 / (A.totient : ℂ)) *
      ∑ ψ : DirichletCharacter ℂ A, (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 *
        bern (8 * A * p) (vartheta p ψ) :=
  square_class_decomposition' hp2 hA hpA hBC

/-- **Corollary 3.3.** `𝒮_{A,1,0}(p) = 1 - (1/φ(A)) ∑_ψ B_{1,ϑ_{p,ψ}}^{(8Ap)}`. -/
theorem floorSum_universal (hp2 : p ≠ 2) {A : ℕ} [NeZero A] (hA : Odd A) (hpA : ¬ p ∣ A) :
    (floorSum A 1 0 p : ℂ) = 1 - (1 / (A.totient : ℂ)) *
      ∑ ψ : DirichletCharacter ℂ A, bern (8 * A * p) (vartheta p ψ) :=
  floorSum_universal' hp2 hA hpA

/-- **Corollary 3.4.** Admissible pairs with the same square class `B² mod A` give the same floor
sum and the same sign `(-1)^C`. -/
theorem floorSum_eq_of_sq_modEq (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A)
    {B C B' C' : ℤ} (h : Admissible A B C) (h' : Admissible A B' C')
    (hBB : B ^ 2 ≡ B' ^ 2 [ZMOD A]) :
    floorSum A B C p = floorSum A B' C' p ∧ C.negOnePow = C'.negOnePow :=
  floorSum_eq_of_sq_modEq' hp2 hA hpA h h' hBB

/-- **Corollary 3.4, every square class arises.** -/
theorem exists_admissible {A : ℕ} (hA : Odd A) {B₀ : ℤ} (hB₀ : Int.gcd B₀ A = 1) :
    ∃ B C : ℤ, Admissible A B C ∧ B ≡ B₀ [ZMOD A] :=
  exists_admissible' hA hB₀

/-! ### Section 4: the first odd coefficients -/

/-- **Theorem 4.1, Bernoulli form.** `𝒮_1(p) = ∑_{n<p} (-1)^{⌊n(n+1)/p⌋} = 1 - B_{1,η_p}^{(8p)}`
(which is `1 + h(-8p)` by Dirichlet's class number formula). -/
theorem floorSum_one (hp2 : p ≠ 2) :
    (floorSum 1 1 0 p : ℂ) = 1 - bern (8 * p) (fun x => (eta p x : ℂ)) :=
  floorSum_one' hp2

/-- **Theorem 4.2, Bernoulli form.** `𝒮_3(p) = 1 - (B_{1,η_p}^{(24p)} + B_{1,χ_{-24p}}^{(24p)})/2`,
with `η_p` induced to modulus `24p` and `χ_{-24p} = η_p χ_{-4} (·/3)`. -/
theorem floorSum_three (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (floorSum 3 1 0 p : ℂ) = 1 - (1 / 2) *
      (bern (24 * p) (fun x => (eta p x : ℂ) * (if 3 ∣ x then 0 else 1)) +
        bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
          (legendreSym 3 x : ℂ))) :=
  floorSum_three' hp2 hp3

/-- **Theorem 4.4, the quadratic half, Bernoulli form.**
`𝒮_{5,1,0}(p) + 𝒮_{5,3,0}(p) - 2 = -(B_{1,η_p}^{(40p)} + B_{1,χ_{-40p}}^{(40p)})/2`, with `η_p`
induced to modulus `40p` and `χ_{-40p} = η_p (·/5)`. -/
theorem quadratic_half (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((floorSum 5 1 0 p + floorSum 5 3 0 p - 2 : ℤ) : ℂ) = -(1 / 2) *
      (bern (40 * p) (fun x => (eta p x : ℂ) * (if 5 ∣ x then 0 else 1)) +
        bern (40 * p) (fun x => (eta p x : ℂ) * (jacobiSym x 5 : ℂ))) :=
  quadratic_half' hp2 hp5

/-- **Corollary 4.5 (the quartic split).** `Re B_{1,Θ_p} = 𝒮_{5,3,0}(p) - 𝒮_{5,1,0}(p)`. -/
theorem quartic_split (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((floorSum 5 3 0 p - floorSum 5 1 0 p : ℤ) : ℝ) = (bern (40 * p) (Theta p)).re :=
  quartic_split' hp2 hp5

/-- **Proposition 4.6.** `Re B_{1,Θ_p}` is an integer congruent to `2 (z_1 - z_3)` modulo `4`. -/
theorem quartic_mod_four (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ∃ m : ℤ, (bern (40 * p) (Theta p)).re = m ∧ m ≡ 2 * (zB 1 p - zB 3 p) [ZMOD 4] :=
  quartic_mod_four' hp2 hp5

/-! ### Section 7: monic shifts -/

/-- **Theorem 7.1(1).** For `a = 2t + 1` and `b' = b - t(t+1)`,
`𝒮_{1,a,b}(p) = (𝒮_1(p) - 1) + (-1)^{b'} - 2 ∑*_{j=0}^{b'-1} (-1)^j ((-4j-3)/p)`. -/
theorem monic_odd (hp2 : p ≠ 2) (t b : ℤ) :
    floorSum 1 (2 * t + 1) b p = (floorSum 1 1 0 p - 1) + ((b - t * (t + 1)).negOnePow : ℤ) -
      2 * osum (b - t * (t + 1)) (fun j => (j.negOnePow : ℤ) * legendreSym p (-4 * j - 3)) :=
  monic_odd' hp2 t b

/-- **Theorem 7.1(2).** For `a = 2t` and `b' = b - t²`,
`𝒮_{1,a,b}(p) = (-1)^{⌊b'/p⌋} - 2 ∑*_{m=0}^{t-1} (-1)^{⌊(m² + b')/p⌋}`. -/
theorem monic_even (hp2 : p ≠ 2) (t b : ℤ) :
    floorSum 1 (2 * t) b p = (((b - t ^ 2) / (p : ℤ)).negOnePow : ℤ) -
      2 * osum t (fun m => (((m ^ 2 + (b - t ^ 2)) / (p : ℤ)).negOnePow : ℤ)) :=
  monic_even' hp2 t b

/-- **Theorem 7.1(2), the bound.** `|𝒮_{1,2t,b}(p)| ≤ 1 + 2|t|`. -/
theorem monic_even_bound (hp2 : p ≠ 2) (t b : ℤ) :
    |floorSum 1 (2 * t) b p| ≤ 1 + 2 * |t| :=
  monic_even_bound' hp2 t b

/-- **Theorem 7.1(2), eventual constancy.** For fixed `t` and `b`, `𝒮_{1,2t,b}(p)` takes one
value for all sufficiently large primes `p`. -/
theorem monic_even_eventually_const (t b : ℤ) :
    ∃ N : ℕ, ∃ c : ℤ, ∀ p : ℕ, p.Prime → N < p → floorSum 1 (2 * t) b p = c :=
  monic_even_eventually_const' t b

end QuadraticFloor
