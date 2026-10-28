module

public import QuadraticFloor.Defs

@[expose] public section

/-!
# The root-count lemma (Lemma 2.1)

If `A + B` is even, then `A n² + B n + C` has the parity of `C`, so the parity of the quotient
`⌊(A n² + B n + C)/p⌋` is the parity of the residue shifted by `C`. Counting the solutions of
`A n² + B n + C ≡ r (mod p)` by the discriminant turns the floor sum into a sum of Legendre symbols
over an arithmetic progression:

`𝒮_{A,B,C}(p) = (-1)^C (1 + 2 ∑_{j=0}^{(p-1)/2} ((D + 8Aj)/p))`, `D = B² - 4AC`.
-/

namespace QuadraticFloor

open Finset

section General

/-- An alternating sum over an odd range is `1`. -/
lemma sum_range_alt_odd (m : ℕ) : ∑ r ∈ range (2 * m + 1), (-1 : ℤ) ^ r = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      (odd_two_mul_add_one m).neg_one_pow, (show Even (2 * m + 1 + 1) from ⟨m + 1, by ring⟩).neg_one_pow]
    ring

/-- The even terms of a sum over an odd range. -/
lemma sum_range_even_odd {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ r ∈ range (2 * m + 1), (if Even r then f r else 0) = ∑ j ∈ range (m + 1), f (2 * j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun j => f (2 * j)) (m + 1)]
    have h1 : ¬ Even (2 * m + 1) := by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one m
    simp only [h1, ite_false, add_zero, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, even_two_mul,
      ite_true]

end General

variable {p : ℕ} [hp : Fact p.Prime]

lemma odd_of_ne_two (hp2 : p ≠ 2) : Odd p := hp.out.odd_of_ne_two hp2

/-- A sum over `range p` of a function of the residue is the sum over `ZMod p`. -/
lemma sum_range_eq_sum_zmod {M : Type*} [AddCommMonoid M] (G : ZMod p → M) :
    ∑ n ∈ range p, G n = ∑ x : ZMod p, G x := by
  refine sum_nbij' (fun n => (n : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro n _; exact mem_univ _
  · intro x _; simpa using x.val_lt
  · intro n hn; simpa using ZMod.val_cast_of_lt (mem_range.1 hn)
  · intro x _; simp
  · intro n _; rfl

/-- The parity of the quotient of `v` by the odd prime `p` is the parity of `v - (v mod p)`. -/
lemma negOnePow_ediv (hp2 : p ≠ 2) (v C : ℤ) (hv : Even (v - C)) :
    ((v / (p : ℤ)).negOnePow : ℤ) = (C.negOnePow : ℤ) * ((v % (p : ℤ)).negOnePow : ℤ) := by
  obtain ⟨k, hk⟩ := odd_of_ne_two hp2
  have h1 : (v / (p : ℤ)).negOnePow = ((p : ℤ) * (v / (p : ℤ))).negOnePow := by
    rw [Int.negOnePow_eq_iff]
    refine ⟨-(k * (v / (p : ℤ))), ?_⟩
    rw [show (p : ℤ) = 2 * k + 1 by exact_mod_cast hk]
    ring
  have h2 : (p : ℤ) * (v / (p : ℤ)) = v - v % (p : ℤ) := by
    have := Int.emod_add_mul_ediv v (p : ℤ); linarith
  have h3 : v.negOnePow = C.negOnePow := (Int.negOnePow_eq_iff _ _).2 hv
  rw [h1, h2, Int.negOnePow_sub, h3, Units.val_mul]

/-- `A n² + B n + C ≡ C (mod 2)` when `A + B` is even. -/
lemma even_sub_C {A B : ℤ} (hAB : Even (A + B)) (n C : ℤ) : Even (A * n ^ 2 + B * n + C - C) := by
  rw [show A * n ^ 2 + B * n + C - C = n * (A * n + B) by ring]
  rcases Int.even_or_odd n with hn | ⟨m, rfl⟩
  · exact hn.mul_right _
  · apply Even.mul_left
    obtain ⟨r, hr⟩ := hAB
    exact ⟨A * m + r, by linear_combination hr⟩

/-- `(-1)^{x mod p}` written through the least residue in `ZMod p`. -/
lemma negOnePow_emod (v : ℤ) :
    ((v % (p : ℤ)).negOnePow : ℤ) = (-1) ^ ((v : ZMod p).val) := by
  rw [← ZMod.val_intCast v, Int.coe_negOnePow_natCast]

/-- The number of solutions of `A x² + B x + C = y` in `ZMod p` is `1 + ((D + 4Ay)/p)`. -/
lemma card_quadratic_eq (hp2 : p ≠ 2) {A B C : ZMod p} (hA : A ≠ 0) (y : ZMod p) :
    ((univ.filter fun x : ZMod p => A * x ^ 2 + B * x + C = y).card : ℤ) =
      quadraticChar (ZMod p) (B ^ 2 - 4 * A * C + 4 * A * y) + 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have h2A : (2 * A : ZMod p) ≠ 0 := mul_ne_zero h2 hA
  have h4A : (4 * A : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) * A = 2 * (2 * A) by ring]; exact mul_ne_zero h2 h2A
  have key : ∀ x : ZMod p, 4 * A * (A * x ^ 2 + B * x + C) =
      (2 * A * x + B) ^ 2 - (B ^ 2 - 4 * A * C) := fun x => by ring
  have hch : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  rw [← quadraticChar_card_sqrts hch, Set.toFinset_ofPred]
  congr 1
  refine card_nbij' (fun x => 2 * A * x + B) (fun z => (z - B) * (2 * A)⁻¹) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    have := key x
    rw [hx] at this
    linear_combination -this
  · intro z hz
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
    have hx : 2 * A * ((z - B) * (2 * A)⁻¹) + B = z := by field_simp; ring
    have := key ((z - B) * (2 * A)⁻¹)
    rw [hx, hz] at this
    exact mul_left_cancel₀ h4A (by linear_combination this)
  · intro x _; simp only; field_simp; ring
  · intro z _; simp only; field_simp; ring

/-- The complete sum of the quadratic character along an arithmetic progression vanishes. -/
lemma sum_quadraticChar_affine (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) (b : ZMod p) :
    ∑ y : ZMod p, quadraticChar (ZMod p) (b + a * y) = 0 := by
  have hch : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  let e : ZMod p ≃ ZMod p :=
    { toFun := fun y => b + a * y
      invFun := fun z => (z - b) * a⁻¹
      left_inv := fun y => by simp only; field_simp; ring
      right_inv := fun z => by simp only; field_simp; ring }
  rw [show (∑ y : ZMod p, quadraticChar (ZMod p) (b + a * y)) =
      ∑ y : ZMod p, quadraticChar (ZMod p) (e y) from rfl, Equiv.sum_comp e,
      quadraticChar_sum_zero hch]

/-- **Lemma 2.1 (root count).** If `A + B` is even and `p ∤ A`, then
`𝒮_{A,B,C}(p) = (-1)^C (1 + 2 ∑_{j=0}^{(p-1)/2} ((B² - 4AC + 8Aj)/p))`. -/
theorem root_count' (hp2 : p ≠ 2) {A B : ℤ} (C : ℤ) (hAB : Even (A + B)) (hpA : ¬ (p : ℤ) ∣ A) :
    floorSum A B C p = (C.negOnePow : ℤ) *
      (1 + 2 * ∑ j ∈ range ((p + 1) / 2), legendreSym p (B ^ 2 - 4 * A * C + 8 * A * j)) := by
  set χ := quadraticChar (ZMod p)
  have hA : (A : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨m, hm⟩ := odd_of_ne_two hp2
  -- Step 1: each term is `(-1)^C (-1)^{⟨v⟩}`.
  have hterm : ∀ n : ℕ, (((A * n ^ 2 + B * n + C) / (p : ℤ)).negOnePow : ℤ) = (C.negOnePow : ℤ) *
      (-1) ^ (((A : ZMod p) * (n : ZMod p) ^ 2 + B * n + C)).val := by
    intro n
    rw [negOnePow_ediv hp2 _ C (even_sub_C hAB n C), negOnePow_emod]
    push_cast; rfl
  rw [floorSum, sum_congr rfl fun n _ => hterm n, ← mul_sum]
  congr 1
  -- Step 2: pass to `ZMod p` and group by the value.
  rw [sum_range_eq_sum_zmod (fun x : ZMod p => (-1 : ℤ) ^ ((A : ZMod p) * x ^ 2 + B * x + C).val)]
  rw [← sum_fiberwise univ (fun x : ZMod p => (A : ZMod p) * x ^ 2 + B * x + C)
    (fun x => (-1 : ℤ) ^ ((A : ZMod p) * x ^ 2 + B * x + C).val)]
  have hfib : ∀ y : ZMod p, ∑ x ∈ univ.filter (fun x : ZMod p => (A : ZMod p) * x ^ 2 + B * x + C = y),
      (-1 : ℤ) ^ ((A : ZMod p) * x ^ 2 + B * x + C).val =
      (-1) ^ y.val * (χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * y) + 1) := by
    intro y
    rw [sum_congr rfl fun x hx => by rw [(mem_filter.1 hx).2], sum_const, nsmul_eq_mul,
      card_quadratic_eq hp2 hA y]
    ring
  rw [sum_congr rfl fun y _ => hfib y]
  -- Step 3: back to `range p`, and split the alternating sign into even terms.
  rw [← sum_range_eq_sum_zmod (fun y : ZMod p =>
    (-1 : ℤ) ^ y.val * (χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * y) + 1))]
  have hval : ∀ r ∈ range p, (-1 : ℤ) ^ ((r : ZMod p)).val *
      (χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * (r : ZMod p)) + 1) =
      2 * (if Even r then χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * (r : ZMod p)) else 0) -
        χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * (r : ZMod p)) + (-1) ^ r := by
    intro r hr
    rw [ZMod.val_cast_of_lt (mem_range.1 hr)]
    rcases Nat.even_or_odd r with h | h
    · simp only [h, ite_true, h.neg_one_pow]; ring
    · simp only [Nat.not_even_iff_odd.2 h, ite_false, h.neg_one_pow]; ring
  rw [sum_congr rfl hval, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  have hfull : ∑ r ∈ range p, χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * (r : ZMod p)) = 0 := by
    rw [sum_range_eq_sum_zmod (fun y : ZMod p => χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * y))]
    have h4A : (4 * A : ZMod p) ≠ 0 := by
      have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
      rw [show (4 : ZMod p) * A = 2 * (2 * A) by ring]; exact mul_ne_zero h2 (mul_ne_zero h2 hA)
    exact sum_quadraticChar_affine hp2 h4A _
  rw [hfull, show range p = range (2 * m + 1) by rw [hm], sum_range_alt_odd, sum_range_even_odd,
    show (p + 1) / 2 = m + 1 by omega]
  have hleg : ∀ j : ℕ, χ ((B : ZMod p) ^ 2 - 4 * A * C + 4 * A * ((2 * j : ℕ) : ZMod p)) =
      legendreSym p (B ^ 2 - 4 * A * C + 8 * A * j) := by
    intro j
    simp only [legendreSym, χ]
    push_cast; ring_nf
  rw [sum_congr rfl fun j _ => hleg j]
  ring

end QuadraticFloor
