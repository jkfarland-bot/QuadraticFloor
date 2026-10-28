module

public import QuadraticFloor.RootCount

@[expose] public section

/-!
# The character `η_p = χ_{-8p}`

For odd `x`, quadratic reciprocity gives `η_p(x) = κ_p(x) (x/p)` (equation (2.2)), where `κ_p` is the
component of `η_p` modulo `8`: `κ_p = χ_{-8}` (Mathlib's `χ₈'`) if `p ≡ 1 (mod 4)` and `κ_p = χ_8`
if `p ≡ 3 (mod 4)`. From this: `η_p` vanishes on even numbers and on multiples of `p`, changes sign
under `x ↦ x + 4Ap` (`A` odd), and is odd: `η_p(q - x) = -η_p(x)` when `8p ∣ q`.
-/

namespace QuadraticFloor

open Finset

/-- `κ_p`, the component of `η_p` modulo `8`. -/
def kap (p : ℕ) : MulChar (ZMod 8) ℤ := if p % 4 = 1 then ZMod.χ₈' else ZMod.χ₈

lemma kap_add_four (p : ℕ) (y : ZMod 8) : kap p (y + 4) = -kap p y := by
  unfold kap
  split_ifs
  · revert y; decide
  · revert y; decide

lemma kap_one (p : ℕ) : kap p 1 = 1 := by unfold kap; split_ifs <;> decide

lemma kap_five (p : ℕ) : kap p 5 = -1 := by unfold kap; split_ifs <;> decide

lemma kap_neg (p : ℕ) (y : ZMod 8) : kap p (-y) = kap p (-1) * kap p y := by
  rw [← map_mul, neg_one_mul]

variable {p : ℕ} [hp : Fact p.Prime]

/-- `κ_p(-1) (-1/p) = -1`: `η_p` is odd. -/
lemma kap_neg_one_mul_legendre (hp2 : p ≠ 2) : kap p (-1) * legendreSym p (-1) = -1 := by
  rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_eq_if_mod_four]
  have hodd := odd_of_ne_two hp2
  have h2 : p % 2 = 1 := Nat.odd_iff.1 hodd
  unfold kap
  rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with h | h
  · simp only [h, ite_true, show p % 2 ≠ 0 by omega, ite_false]; decide
  · simp only [h, show (3 : ℕ) ≠ 1 by decide, ite_false, show p % 2 ≠ 0 by omega]; decide

/-- **Equation (2.2)**: `η_p(x) = κ_p(x) (x/p)`. -/
theorem eta_eq' (hp2 : p ≠ 2) (x : ℕ) : eta p x = kap p x * legendreSym p x := by
  have hpodd := odd_of_ne_two hp2
  unfold eta
  by_cases hx : Even x
  · simp only [hx, ite_true]
    have : kap p (x : ZMod 8) = 0 := by
      unfold kap
      have : x % 2 = 0 := Nat.even_iff.1 hx
      split_ifs
      · rw [ZMod.χ₈'_nat_eq_if_mod_eight]; simp [this]
      · rw [ZMod.χ₈_nat_eq_if_mod_eight]; simp [this]
    rw [this, zero_mul]
  simp only [hx, ite_false]
  have hxodd : Odd x := Nat.not_even_iff_odd.1 hx
  have hsplit : (-8 * p : ℤ) = (-1) * 2 * 2 * 2 * (p : ℤ) := by ring
  rw [hsplit, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left,
    jacobiSym.at_neg_one hxodd, jacobiSym.at_two hxodd,
    jacobiSym.quadratic_reciprocity hpodd hxodd, ← jacobiSym.legendreSym.to_jacobiSym]
  have hx2 : x % 2 = 1 := Nat.odd_iff.1 hxodd
  have hp2' : p % 2 = 1 := Nat.odd_iff.1 hpodd
  -- parity of `(p/2)(x/2)`
  have hsign : ((-1 : ℤ) ^ (p / 2 * (x / 2))) =
      if p % 4 = 1 then 1 else (if x % 4 = 1 then 1 else -1) := by
    split_ifs with h1 h2
    · apply Even.neg_one_pow
      apply Even.mul_right
      rw [Nat.even_div]; omega
    · apply Even.neg_one_pow
      apply Even.mul_left
      rw [Nat.even_div]; omega
    · apply Odd.neg_one_pow
      apply Nat.odd_mul.2
      constructor <;> rw [← Nat.not_even_iff_odd, Nat.even_div] <;> omega
  rw [hsign]
  unfold kap
  rw [ZMod.χ₄_nat_eq_if_mod_four, ZMod.χ₈_nat_eq_if_mod_eight]
  have h8 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  have h4 : x % 4 = x % 8 % 4 := (Nat.mod_mod_of_dvd x (by norm_num)).symm
  split_ifs with hp4 <;>
    simp only [ZMod.χ₈'_nat_eq_if_mod_eight, ZMod.χ₈_nat_eq_if_mod_eight] <;>
    rcases h8 with h | h | h | h <;> simp [h, hx2] <;> omega

omit hp in
lemma eta_of_even {x : ℕ} (hx : Even x) : eta p x = 0 := by simp [eta, hx]

lemma eta_of_dvd (hp2 : p ≠ 2) {x : ℕ} (hx : p ∣ x) : eta p x = 0 := by
  rw [eta_eq' hp2, (legendreSym.eq_zero_iff p _).2, mul_zero]
  exact_mod_cast (ZMod.natCast_eq_zero_iff x p).2 hx

/-- `η_p(x + 4Ap) = -η_p(x)` for odd `A`. -/
lemma eta_add_half (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (x : ℕ) :
    eta p (x + 4 * A * p) = -eta p x := by
  rw [eta_eq' hp2, eta_eq' hp2]
  have hAp : (A * p) % 2 = 1 := Nat.odd_iff.1 (hA.mul (odd_of_ne_two hp2))
  have hm : (4 * A * p) % 8 = 4 % 8 := by rw [show 4 * A * p = 4 * (A * p) by ring]; omega
  have h4 : ((4 * A * p : ℕ) : ZMod 8) = 4 := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ 8).2 hm
    rw [Nat.cast_ofNat] at this
    exact this
  have h8 : ((x + 4 * A * p : ℕ) : ZMod 8) = (x : ZMod 8) + 4 := by
    rw [Nat.cast_add, h4]
  have hL : legendreSym p ((x + 4 * A * p : ℕ) : ℤ) = legendreSym p x := by
    rw [legendreSym.mod, legendreSym.mod p (x : ℤ)]
    congr 1
    push_cast
    rw [show (x : ℤ) + 4 * A * p = x + (4 * A) * p by ring, Int.add_mul_emod_self_right]
  rw [h8, hL, kap_add_four]
  ring

/-- `η_p(q - x) = -η_p(x)` when `8p ∣ q` and `x ≤ q`. -/
lemma eta_reflect (hp2 : p ≠ 2) {q : ℕ} (hq : 8 * p ∣ q) {x : ℕ} (hx : x ≤ q) :
    eta p (q - x) = -eta p x := by
  rw [eta_eq' hp2, eta_eq' hp2]
  have h8 : ((q - x : ℕ) : ZMod 8) = -(x : ZMod 8) := by
    rw [Nat.cast_sub hx, (ZMod.natCast_eq_zero_iff q 8).2 (dvd_trans (dvd_mul_right 8 p) hq),
      zero_sub]
  have hL : legendreSym p ((q - x : ℕ) : ℤ) = legendreSym p (-1) * legendreSym p x := by
    rw [← legendreSym.mul, legendreSym.mod, legendreSym.mod p (-1 * (x : ℤ))]
    congr 1
    rw [Nat.cast_sub hx]
    obtain ⟨r, hr⟩ := hq
    rw [hr]
    push_cast
    rw [show (8 * (p : ℤ) * r - x) = -1 * x + (8 * r) * p by ring, Int.add_mul_emod_self_right]
  rw [h8, hL, kap_neg]
  have := kap_neg_one_mul_legendre hp2
  linear_combination (kap p (x : ZMod 8) * legendreSym p x) * this

end QuadraticFloor
