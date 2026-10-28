module

public import Mathlib

@[expose] public section

/-!
# Definitions

Throughout `p` is an odd prime and `A` a positive odd integer.

* `floorSum A B C p = 𝒮_{A,B,C}(p) = ∑_{n=0}^{p-1} (-1)^{⌊(A n² + B n + C)/p⌋}`. Integer division
  by the positive integer `p` is floor division.
* `Admissible A B C`: `B` odd, `gcd(B, A) = 1` and `1 ≤ B² - 4AC < 4A`.
* `eta p = η_p = χ_{-8p}`, the Kronecker character of discriminant `-8p`: on odd `x > 0` it is the
  Jacobi symbol `(-8p / x)`, and it vanishes on even `x`.
* `bern q f = B_{1,f}^{(q)} = (1/q) ∑_{x=1}^{q} x f(x)`, the first Bernoulli number of a function
  of period `q`, with the modulus recorded.
* `vartheta p ψ = ϑ_{p,ψ} = η_p χ_{-4}^{δ_ψ} ψ` for a Dirichlet character `ψ` modulo `A`, where
  `ψ(-1) = (-1)^{δ_ψ}` and `χ_{-4}^0 = χ_{-4}²` is the principal character modulo `4`.
* `xi` is the quartic character modulo `5` with `ξ(2) = i`, and `Theta p = Θ_p = η_p χ_{-4} ξ`.
* `zB B p ∈ {0, 1}` records whether the progression `B² + 40 j`, `0 ≤ j ≤ (p-1)/2`, meets a
  multiple of `p`.
* `osum t g` is the oriented sum `∑*_{j=0}^{t-1} g(j)`: the usual sum for `t ≥ 0` and
  `-∑_{j=t}^{-1} g(j)` for `t < 0`.
-/

namespace QuadraticFloor

open Finset

theorem ite_of_pos {α : Sort*} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_of_neg {α : Sort*} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

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

end QuadraticFloor
