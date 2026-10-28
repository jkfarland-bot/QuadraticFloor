module

public import QuadraticFloor.Eta

@[expose] public section

/-!
# Half-period identities (Lemma 3.1)

For a function `f` on `ℕ` and `h > 0`:

1. if `f(x + h) = f(x)` and the sum of `f` over `[1, 2h]` vanishes, so does the sum over `[1, h]`;
2. if `f(x + h) = -f(x)`, `f(0) = 0` and `f(2h - x) = f(x)`, the sum over `[1, h]` vanishes;
3. if `f(x + h) = -f(x)`, then `B_{1,f}^{(2h)} = -(1/2) ∑_{x=1}^{h} f(x)`.

We also record that `∑_{x=1}^{mp} g(x) (x/p) = 0` for any `m`-periodic `g` with `p ∤ m`.
-/

namespace QuadraticFloor

open Finset

lemma sum_Icc_one {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ x ∈ Icc 1 n, f x = ∑ k ∈ range n, f (k + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp [add_comm]

/-- Lemma 3.1(3). -/
lemma bern_antiperiodic' (f : ℕ → ℂ) {h : ℕ} (hh : 0 < h) (hf : ∀ x, f (x + h) = -f x) :
    bern (2 * h) f = -(1 / 2) * ∑ x ∈ Icc 1 h, f x := by
  unfold bern
  rw [sum_Icc_one, sum_Icc_one, two_mul, sum_range_add]
  have hs : ∀ k ∈ range h, (((h + k + 1 : ℕ) : ℂ) * f (h + k + 1)) =
      -(((k + 1 : ℕ) : ℂ) * f (k + 1)) - (h : ℂ) * f (k + 1) := by
    intro k _
    rw [show h + k + 1 = (k + 1) + h by ring, hf]
    push_cast; ring
  rw [sum_congr rfl hs, sum_sub_distrib, sum_neg_distrib, ← mul_sum]
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  push_cast
  field_simp
  ring

/-- Lemma 3.1(1). -/
lemma half_sum_zero_of_periodic' (f : ℕ → ℂ) {h : ℕ} (hf : ∀ x, f (x + h) = f x)
    (hfull : ∑ x ∈ Icc 1 (2 * h), f x = 0) : ∑ x ∈ Icc 1 h, f x = 0 := by
  rw [sum_Icc_one, two_mul, sum_range_add] at hfull
  rw [sum_Icc_one]
  have : ∀ k ∈ range h, f (h + k + 1) = f (k + 1) := fun k _ => by
    rw [show h + k + 1 = (k + 1) + h by ring, hf]
  rw [sum_congr rfl this] at hfull
  have h2 : (2 : ℂ) * ∑ k ∈ range h, f (k + 1) = 0 := by rw [two_mul]; exact hfull
  simpa using h2

/-- Lemma 3.1(2). -/
lemma half_sum_zero_of_even' (f : ℕ → ℂ) {h : ℕ} (hf : ∀ x, f (x + h) = -f x) (h0 : f 0 = 0)
    (hrefl : ∀ x ≤ 2 * h, f (2 * h - x) = f x) : ∑ x ∈ Icc 1 h, f x = 0 := by
  rw [sum_Icc_one]
  set T := ∑ k ∈ range h, f (k + 1)
  have hfh : f h = 0 := by have := hf 0; rw [zero_add, h0, neg_zero] at this; exact this
  -- reflect `k ↦ h - 1 - k`
  have hr := sum_range_reflect (fun k => f (k + 1)) h
  have hterm : ∀ j ∈ range h, f (h - 1 - j + 1) = -f j := by
    intro j hj
    have hj := mem_range.1 hj
    rw [show h - 1 - j + 1 = h - j by omega]
    have h1 := hf (h - j)
    rw [show h - j + h = 2 * h - j by omega, hrefl j (by omega)] at h1
    linear_combination h1
  rw [sum_congr rfl hterm, sum_neg_distrib] at hr
  have hshift : ∑ j ∈ range h, f j = T := by
    have a := sum_range_succ' f h
    have b := sum_range_succ f h
    rw [hfh, add_zero] at b
    rw [h0, add_zero] at a
    rw [← b, a]
  rw [hshift] at hr
  have : (2 : ℂ) * T = 0 := by linear_combination -hr
  simpa using this

lemma sum_range_mul {M : Type*} [AddCommMonoid M] (F : ℕ → M) (m n : ℕ) :
    ∑ x ∈ range (m * n), F x = ∑ k ∈ range n, ∑ y ∈ range m, F (m * k + y) := by
  induction n with
  | zero => simp
  | succ n ih => rw [mul_add, mul_one, sum_range_add, ih, sum_range_succ]

variable {p : ℕ} [hp : Fact p.Prime]

/-- A periodic function times the Legendre symbol sums to zero over a full period. -/
lemma sum_mul_legendre_eq_zero (hp2 : p ≠ 2) (g : ℕ → ℂ) {m : ℕ} (hm : ¬ p ∣ m)
    (hg : ∀ x, g (x + m) = g x) :
    ∑ x ∈ Icc 1 (m * p), g x * (legendreSym p x : ℂ) = 0 := by
  have hg' : ∀ y k, g (m * k + y) = g y := by
    intro y k
    induction k with
    | zero => simp
    | succ k ih => rw [show m * (k + 1) + y = (m * k + y) + m by ring, hg, ih]
  have hL0 : legendreSym p ((0 : ℕ) : ℤ) = 0 := by simp
  have hLmp : legendreSym p ((m * p : ℕ) : ℤ) = 0 := by
    rw [(legendreSym.eq_zero_iff p _).2]
    push_cast; simp
  -- pass from `[1, mp]` to `[0, mp)`
  have hIcc : ∑ x ∈ Icc 1 (m * p), g x * (legendreSym p x : ℂ) =
      ∑ x ∈ range (m * p), g x * (legendreSym p x : ℂ) := by
    rw [sum_Icc_one]
    have a := sum_range_succ' (fun x => g x * (legendreSym p x : ℂ)) (m * p)
    have b := sum_range_succ (fun x => g x * (legendreSym p x : ℂ)) (m * p)
    simp only [hL0, hLmp, Int.cast_zero, mul_zero, add_zero] at a b
    rw [← a, b]
  rw [hIcc, sum_range_mul, sum_comm]
  apply sum_eq_zero
  intro y _
  simp_rw [hg' y]
  rw [← mul_sum]
  have hm' : ((m : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hm
  have hsum : ∑ k ∈ range p, legendreSym p ((m * k + y : ℕ) : ℤ) = 0 := by
    have := sum_quadraticChar_affine hp2 hm' (y : ZMod p)
    rw [← sum_range_eq_sum_zmod (fun z : ZMod p => quadraticChar (ZMod p) ((y : ZMod p) + m * z))]
      at this
    rw [← this]
    apply sum_congr rfl
    intro k _
    simp only [legendreSym]
    push_cast; ring_nf
  have : ∑ k ∈ range p, (legendreSym p ((m * k + y : ℕ) : ℤ) : ℂ) = 0 := by
    exact_mod_cast hsum
  rw [this, mul_zero]

end QuadraticFloor
