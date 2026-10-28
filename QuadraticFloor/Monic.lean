module

public import QuadraticFloor.Corollaries

@[expose] public section

/-!
# The monic shifts (Theorem 7.1)

For fixed integers `a, b`, write `𝒮_{a,b}(p) = 𝒮_{1,a,b}(p) = ∑_{n<p} (-1)^{⌊(n² + an + b)/p⌋}`.

1. If `a = 2t + 1` and `b' = b - t(t+1)`, then
   `𝒮_{a,b}(p) = (𝒮_1(p) - 1) + (-1)^{b'} - 2 ∑*_{j=0}^{b'-1} (-1)^j ((-4j-3)/p)`,
   where `𝒮_1(p) - 1 = h(-8p)` by Theorem 4.1.
2. If `a = 2t` and `b' = b - t²`, then
   `𝒮_{a,b}(p) = (-1)^{⌊b'/p⌋} - 2 ∑*_{m=0}^{t-1} (-1)^{⌊(m² + b')/p⌋}`; in particular
   `|𝒮_{a,b}(p)| ≤ 1 + 2|t|`, and the sum is eventually constant in `p`.

`∑*` is the oriented sum `osum`.
-/

namespace QuadraticFloor

open Finset

/-! ### Oriented sums -/

lemma sum_Ico_eq_add_sum (g : ℤ → ℤ) {a b : ℤ} (h : a < b) :
    ∑ j ∈ Ico a b, g j = g a + ∑ j ∈ Ico (a + 1) b, g j := by
  have : Ico a b = insert a (Ico (a + 1) b) := by
    ext j; simp only [mem_Ico, mem_insert]; omega
  rw [this, sum_insert (by simp)]

lemma osum_zero (g : ℤ → ℤ) : osum 0 g = 0 := by simp [osum]

lemma osum_succ (t : ℤ) (g : ℤ → ℤ) : osum (t + 1) g = osum t g + g t := by
  unfold osum
  rcases lt_trichotomy t (-1) with h | h | h
  · rw [ite_of_neg (by omega), ite_of_neg (by omega), sum_Ico_eq_add_sum g (show t < 0 by omega)]
    ring
  · subst h
    have : Ico (-1 : ℤ) 0 = {-1} := by ext j; simp only [mem_Ico, mem_singleton]; omega
    simp [this]
  · rw [ite_of_pos (by omega), ite_of_pos (by omega), ← sum_Ico_add_eq_sum_Ico_add_one (by omega) g]

/-- Two functions related by a constant step have oriented sums related in the same way. -/
lemma eq_of_osum_step {F : ℤ → ℤ} {g : ℤ → ℤ} (hF : ∀ c, F (c + 1) = F c + g c) (c : ℤ) :
    F c = F 0 + osum c g := by
  induction c using Int.induction_on with
  | zero => rw [osum_zero, add_zero]
  | succ i ih => rw [hF, ih, osum_succ]; ring
  | pred i ih =>
    have h1 := hF (-(i : ℤ) - 1)
    have h2 := osum_succ (-(i : ℤ) - 1) g
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at h1 h2
    rw [ih] at h1
    linarith

set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
lemma osum_add (t : ℤ) (g h : ℤ → ℤ) : osum t (fun j => g j + h j) = osum t g + osum t h := by
  unfold osum; split_ifs <;> simp [sum_add_distrib] <;> ring

lemma osum_mul_left (t c : ℤ) (g : ℤ → ℤ) : osum t (fun j => c * g j) = c * osum t g := by
  unfold osum; split_ifs <;> simp [mul_sum]

lemma osum_negOnePow (t : ℤ) : 2 * osum t (fun j => (j.negOnePow : ℤ)) = 1 - (t.negOnePow : ℤ) := by
  have := eq_of_osum_step (F := fun c => 1 - (c.negOnePow : ℤ) - 2 * osum c (fun j => (j.negOnePow : ℤ)))
    (g := fun _ => 0) (by
      intro c
      simp only [osum_succ, Int.negOnePow_succ, Units.val_neg]
      ring) t
  simp only [osum_zero, Int.negOnePow_zero, Units.val_one] at this
  have h0 : osum t (fun _ : ℤ => (0 : ℤ)) = 0 := by unfold osum; split_ifs <;> simp
  rw [h0] at this
  linarith

lemma osum_abs_le (t : ℤ) (g : ℤ → ℤ) (hg : ∀ j, |g j| ≤ 1) : |osum t g| ≤ |t| := by
  unfold osum
  split_ifs with h
  · calc |∑ j ∈ Ico 0 t, g j| ≤ ∑ j ∈ Ico 0 t, |g j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Ico 0 t, (1 : ℤ) := sum_le_sum fun j _ => hg j
      _ = |t| := by
        rw [sum_const, Int.card_Ico, nsmul_eq_mul, mul_one, abs_of_nonneg h, sub_zero,
          Int.toNat_of_nonneg h]
  · rw [abs_neg]
    calc |∑ j ∈ Ico t 0, g j| ≤ ∑ j ∈ Ico t 0, |g j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Ico t 0, (1 : ℤ) := sum_le_sum fun j _ => hg j
      _ = |t| := by
        rw [sum_const, Int.card_Ico, nsmul_eq_mul, mul_one, abs_of_neg (by omega), zero_sub,
          Int.toNat_of_nonneg (by omega)]

lemma osum_congr {t : ℤ} {g g' : ℤ → ℤ} (h : ∀ j, |j| ≤ |t| → g j = g' j) :
    osum t g = osum t g' := by
  unfold osum
  split_ifs with ht
  · have ha := abs_of_nonneg ht
    exact sum_congr rfl fun j hj => h j (by
      rw [mem_Ico] at hj; rw [abs_le, ha]; constructor <;> omega)
  · have ha := abs_of_neg (show t < 0 by omega)
    congr 1
    exact sum_congr rfl fun j hj => h j (by
      rw [mem_Ico] at hj; rw [abs_le, ha]; constructor <;> omega)

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Sums of periodic functions -/

omit hp in
lemma periodic_int {g : ℤ → ℤ} (hg : ∀ m, g (m + p) = g m) (m k : ℤ) : g (m + p * k) = g m := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih => rw [show m + p * ((i : ℤ) + 1) = (m + p * i) + p by ring, hg, ih]
  | pred i ih =>
    rw [← ih, show m + p * (-(i : ℤ)) = (m + p * (-(i : ℤ) - 1)) + p by ring, hg]

lemma sum_range_shift {g : ℤ → ℤ} (hg : ∀ m, g (m + p) = g m) (t : ℤ) :
    ∑ n ∈ range p, g (n + t) = ∑ n ∈ range p, g n := by
  have hgz : ∀ m : ℤ, g m = g ((m : ZMod p).val) := by
    intro m
    rw [ZMod.val_intCast]
    have := periodic_int hg (m % p) (m / p)
    rw [Int.emod_add_mul_ediv] at this
    exact this
  set G : ZMod p → ℤ := fun x => g x.val
  have h1 : ∀ n : ℕ, g (n + t) = G ((n : ZMod p) + (t : ZMod p)) := by
    intro n; rw [hgz]; push_cast; rfl
  have h2 : ∀ n : ℕ, g n = G (n : ZMod p) := by
    intro n; rw [hgz]; push_cast; rfl
  simp_rw [h1, h2]
  rw [sum_range_eq_sum_zmod (fun x => G (x + (t : ZMod p))), sum_range_eq_sum_zmod G]
  exact Equiv.sum_comp (Equiv.addRight (t : ZMod p)) G

/-! ### The odd case -/

/-- `F(c) = ∑_{n<p} (-1)^{⌊(n² + n + c)/p⌋}`. -/
def Fodd (p : ℕ) (c : ℤ) : ℤ := floorSum 1 1 c p

omit hp in
lemma ediv_succ (hp0 : 0 < (p : ℤ)) (v : ℤ) :
    (v + 1) / (p : ℤ) = v / p + if (p : ℤ) ∣ v + 1 then 1 else 0 := by
  have hv := Int.emod_add_mul_ediv v p
  have hr0 := Int.emod_nonneg v hp0.ne'
  have hrp := Int.emod_lt_of_pos v hp0
  set q := v / (p : ℤ)
  set r := v % (p : ℤ)
  by_cases hr : r + 1 < p
  · have hnd : ¬ (p : ℤ) ∣ v + 1 := by
      rintro ⟨k, hk⟩
      have : (p : ℤ) * (k - q) = r + 1 := by linarith
      have hk0 : 0 < k - q := by
        by_contra hneg; rw [not_lt] at hneg; nlinarith
      nlinarith
    rw [ite_of_neg hnd, add_zero, show v + 1 = (r + 1) + (p : ℤ) * q by linarith,
      Int.add_mul_ediv_left _ _ hp0.ne', Int.ediv_eq_zero_of_lt (by omega) hr, zero_add]
  · have hr' : r + 1 = p := by omega
    have hd : (p : ℤ) ∣ v + 1 := ⟨q + 1, by linarith⟩
    rw [ite_of_pos hd, show v + 1 = 0 + (p : ℤ) * (q + 1) by linarith, Int.add_mul_ediv_left _ _ hp0.ne',
      Int.zero_ediv, zero_add]

lemma Fodd_succ (hp2 : p ≠ 2) (c : ℤ) :
    Fodd p (c + 1) = Fodd p c + (-2 * (c.negOnePow : ℤ) * (1 + legendreSym p (-4 * c - 3))) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  unfold Fodd floorSum
  -- termwise change
  have hterm : ∀ n : ℕ, (((1 * (n : ℤ) ^ 2 + 1 * n + (c + 1)) / (p : ℤ)).negOnePow : ℤ) =
      (((1 * (n : ℤ) ^ 2 + 1 * n + c) / (p : ℤ)).negOnePow : ℤ) +
        -2 * (c.negOnePow : ℤ) * (if ((n : ZMod p) ^ 2 + n + (c + 1 : ZMod p)) = 0 then 1 else 0) := by
    intro n
    set v := 1 * (n : ℤ) ^ 2 + 1 * n + c
    rw [show 1 * (n : ℤ) ^ 2 + 1 * n + (c + 1) = v + 1 by ring, ediv_succ hp0]
    have hz : ((n : ZMod p) ^ 2 + n + (c + 1 : ZMod p)) = 0 ↔ (p : ℤ) ∣ v + 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; simp only [v]; push_cast; ring_nf
    by_cases hd : (p : ℤ) ∣ v + 1
    · rw [ite_of_pos hd, ite_of_pos (hz.2 hd), Int.negOnePow_succ, Units.val_neg]
      -- the old sign is `(-1)^c`
      have hvc : Even (v - c) := by
        simp only [v]
        rw [show 1 * (n : ℤ) ^ 2 + 1 * n + c - c = n * (n + 1) by ring]
        exact Int.even_mul_succ_self n
      rw [negOnePow_ediv hp2 v c hvc]
      have hmod : v % (p : ℤ) = p - 1 := by
        obtain ⟨k, hk⟩ := hd
        rw [show v = (p - 1) + (p : ℤ) * (k - 1) by linarith, Int.add_mul_emod_self_left,
          Int.emod_eq_of_lt (by omega) (by omega)]
      rw [hmod, Int.negOnePow_even ((p : ℤ) - 1) (by
        obtain ⟨m, hm⟩ := odd_of_ne_two hp2
        exact ⟨m, by rw [hm]; push_cast; ring⟩)]
      simp; ring
    · rw [ite_of_neg hd, ite_of_neg (fun h => hd (hz.1 h)), add_zero]; ring
  rw [sum_congr rfl fun n _ => hterm n, sum_add_distrib, ← mul_sum]
  congr 1
  rw [sum_range_eq_sum_zmod (fun x : ZMod p => if x ^ 2 + x + (c + 1 : ZMod p) = 0 then (1 : ℤ) else 0),
    sum_boole]
  have hcard := card_quadratic_eq hp2 (A := 1) (B := 1) (C := (c + 1 : ZMod p)) one_ne_zero 0
  simp only [one_mul, mul_zero, add_zero] at hcard
  rw [hcard]
  simp only [legendreSym]
  push_cast
  ring_nf

/-- **Theorem 7.1(1), odd shifts.** For `a = 2t + 1` and `b' = b - t(t+1)`,
`𝒮_{a,b}(p) = (𝒮_1(p) - 1) + (-1)^{b'} - 2 ∑*_{j=0}^{b'-1} (-1)^j ((-4j-3)/p)`. -/
theorem monic_odd' (hp2 : p ≠ 2) (t b : ℤ) :
    floorSum 1 (2 * t + 1) b p = (floorSum 1 1 0 p - 1) + ((b - t * (t + 1)).negOnePow : ℤ) -
      2 * osum (b - t * (t + 1)) (fun j => (j.negOnePow : ℤ) * legendreSym p (-4 * j - 3)) := by
  set b' := b - t * (t + 1)
  -- shift `n ↦ n + t`
  have hshift : floorSum 1 (2 * t + 1) b p = Fodd p b' := by
    unfold Fodd floorSum
    set g : ℤ → ℤ := fun m => (((1 * m ^ 2 + 1 * m + b') / (p : ℤ)).negOnePow : ℤ)
    have hg : ∀ m, g (m + p) = g m := by
      intro m
      simp only [g]
      rw [show 1 * (m + p) ^ 2 + 1 * (m + p) + b' = (1 * m ^ 2 + 1 * m + b') + (p : ℤ) * (2 * m + p + 1)
        by ring, Int.add_mul_ediv_left _ _ (by exact_mod_cast hp.out.ne_zero), Int.negOnePow_add,
        Int.negOnePow_even (2 * m + p + 1) (by
          obtain ⟨k, hk⟩ := odd_of_ne_two hp2
          exact ⟨m + k + 1, by rw [hk]; push_cast; ring⟩), mul_one]
    have := sum_range_shift hg t
    simp only [g] at this
    rw [← this]
    apply sum_congr rfl
    intro n _
    congr 3
    simp only [b']; ring
  have hF := eq_of_osum_step (F := Fodd p)
    (g := fun c => -2 * (c.negOnePow : ℤ) * (1 + legendreSym p (-4 * c - 3)))
    (Fodd_succ hp2) b'
  rw [hshift, hF]
  have hsplit : osum b' (fun c => -2 * (c.negOnePow : ℤ) * (1 + legendreSym p (-4 * c - 3))) =
      -2 * osum b' (fun j => (j.negOnePow : ℤ)) +
        -2 * osum b' (fun j => (j.negOnePow : ℤ) * legendreSym p (-4 * j - 3)) := by
    rw [← osum_mul_left, ← osum_mul_left, ← osum_add]
    congr 1; funext j; ring
  rw [hsplit]
  have h1 := osum_negOnePow b'
  unfold Fodd
  linarith

/-! ### The even case -/

omit hp in
lemma negOnePow_ediv_add_mul (v : ℤ) (k : ℤ) (hp0 : (p : ℤ) ≠ 0) :
    (((v + p * k) / (p : ℤ)).negOnePow : ℤ) = ((v / p).negOnePow : ℤ) * (k.negOnePow : ℤ) := by
  rw [Int.add_mul_ediv_left _ _ hp0, Int.negOnePow_add, Units.val_mul]

/-- **Theorem 7.1(2), even shifts.** For `a = 2t` and `b' = b - t²`,
`𝒮_{a,b}(p) = (-1)^{⌊b'/p⌋} - 2 ∑*_{m=0}^{t-1} (-1)^{⌊(m² + b')/p⌋}`. -/
theorem monic_even' (hp2 : p ≠ 2) (t b : ℤ) :
    floorSum 1 (2 * t) b p = (((b - t ^ 2) / (p : ℤ)).negOnePow : ℤ) -
      2 * osum t (fun m => (((m ^ 2 + (b - t ^ 2)) / (p : ℤ)).negOnePow : ℤ)) := by
  set b' := b - t ^ 2
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨k, hk⟩ := odd_of_ne_two hp2
  set E : ℤ → ℤ := fun m => (((m ^ 2 + b') / (p : ℤ)).negOnePow : ℤ)
  have hE : ∀ m, E (m + p) = -E m := by
    intro m
    simp only [E]
    rw [show (m + p) ^ 2 + b' = (m ^ 2 + b') + (p : ℤ) * (2 * m + p) by ring,
      negOnePow_ediv_add_mul _ _ hp0, Int.negOnePow_odd (2 * m + p) ⟨m + k, by rw [hk]; push_cast; ring⟩]
    simp
  have hEr : ∀ m : ℕ, 1 ≤ m → m < p → E ((p - m : ℕ) : ℤ) = -E m := by
    intro m h1 h2
    simp only [E]
    rw [Nat.cast_sub h2.le, show ((p : ℤ) - m) ^ 2 + b' = ((m : ℤ) ^ 2 + b') + (p : ℤ) * (p - 2 * m)
      by ring, negOnePow_ediv_add_mul _ _ hp0,
      Int.negOnePow_odd ((p : ℤ) - 2 * m) ⟨(k : ℤ) - m, by rw [hk]; push_cast; ring⟩]
    simp
  -- the full period sums to `E 0`
  have hfull : ∑ m ∈ range p, E m = E 0 := by
    rw [hk, sum_range_succ']
    have hrefl := sum_range_reflect (fun j => E ((j + 1 : ℕ) : ℤ)) (2 * k)
    have hneg : ∀ j ∈ range (2 * k), E ((2 * k - 1 - j + 1 : ℕ) : ℤ) = -E ((j + 1 : ℕ) : ℤ) := by
      intro j hj
      rw [mem_range] at hj
      rw [show 2 * k - 1 - j + 1 = (2 * k + 1) - (j + 1) by omega, ← hk]
      exact hEr (j + 1) (by omega) (by omega)
    rw [sum_congr rfl hneg, sum_neg_distrib] at hrefl
    have : ∑ j ∈ range (2 * k), E ((j + 1 : ℕ) : ℤ) = 0 := by linarith
    simp only [Nat.cast_add, Nat.cast_one] at this ⊢
    rw [this, zero_add]
    simp
  -- the shifted window
  set G : ℤ → ℤ := fun t => ∑ n ∈ range p, E (n + t)
  have hG : ∀ c, G (c + 1) = G c + (-2 * E c) := by
    intro c
    simp only [G]
    have a := sum_range_succ (fun n : ℕ => E (n + c)) p
    have b := sum_range_succ' (fun n : ℕ => E (n + c)) p
    have hpc : E ((p : ℕ) + c) = -E c := by rw [add_comm]; exact hE c
    rw [hpc] at a
    have hb : ∑ n ∈ range p, E (((n + 1 : ℕ) : ℤ) + c) = ∑ n ∈ range p, E (n + (c + 1)) :=
      sum_congr rfl fun n _ => by push_cast; ring_nf
    rw [hb] at b
    simp only [Nat.cast_zero, zero_add] at b
    linarith
  have hGt := eq_of_osum_step hG t
  have hosum : osum t (fun c => -2 * E c) = -2 * osum t E := osum_mul_left t (-2) E
  have hG0 : G 0 = E 0 := by simp only [G, add_zero]; exact hfull
  have hlhs : floorSum 1 (2 * t) b p = G t := by
    unfold floorSum
    simp only [G, E]
    apply sum_congr rfl
    intro n _
    congr 3
    simp only [b']; ring
  rw [hlhs, hGt, hosum, hG0]
  simp only [E, zero_pow two_ne_zero, zero_add]
  ring

/-- **Theorem 7.1(2), the bound.** `|𝒮_{2t,b}(p)| ≤ 1 + 2|t|`. -/
theorem monic_even_bound' (hp2 : p ≠ 2) (t b : ℤ) :
    |floorSum 1 (2 * t) b p| ≤ 1 + 2 * |t| := by
  rw [monic_even' hp2]
  have h1 : |(((b - t ^ 2) / (p : ℤ)).negOnePow : ℤ)| = 1 := by
    rcases Int.isUnit_iff.1 (((b - t ^ 2) / (p : ℤ)).negOnePow.isUnit) with h | h <;> simp [h]
  have h2 := osum_abs_le t (fun m => (((m ^ 2 + (b - t ^ 2)) / (p : ℤ)).negOnePow : ℤ)) (by
    intro j
    rcases Int.isUnit_iff.1 (((j ^ 2 + (b - t ^ 2)) / (p : ℤ)).negOnePow.isUnit) with h | h <;>
      simp [h])
  calc _ ≤ |(((b - t ^ 2) / (p : ℤ)).negOnePow : ℤ)| +
        |2 * osum t (fun m => (((m ^ 2 + (b - t ^ 2)) / (p : ℤ)).negOnePow : ℤ))| := abs_sub _ _
    _ ≤ 1 + 2 * |t| := by rw [h1, abs_mul]; simp; linarith

lemma ediv_small {v : ℤ} {P : ℤ} (hP : |v| < P) :
    v / P = if v < 0 then -1 else 0 := by
  have hP0 : 0 < P := lt_of_le_of_lt (abs_nonneg v) hP
  rw [abs_lt] at hP
  split_ifs with h
  · have hv := Int.emod_add_mul_ediv v P
    have hr0 := Int.emod_nonneg v hP0.ne'
    have hrl := Int.emod_lt_of_pos v hP0
    set q := v / P
    set r := v % P
    have h1 : q < 0 := by
      by_contra hq; rw [not_lt] at hq; nlinarith
    have h2 : -2 < q := by
      by_contra hq; rw [not_lt] at hq; nlinarith
    omega
  · exact Int.ediv_eq_zero_of_lt (by omega) (by omega)

/-- **Theorem 7.1(2), eventual constancy.** For fixed `t` and `b`, the sum `𝒮_{2t,b}(p)` takes one
value for all sufficiently large primes `p`. -/
theorem monic_even_eventually_const' (t b : ℤ) :
    ∃ N : ℕ, ∃ c : ℤ, ∀ p : ℕ, p.Prime → N < p → floorSum 1 (2 * t) b p = c := by
  set b' := b - t ^ 2
  set E' : ℤ → ℤ := fun m => if m ^ 2 + b' < 0 then -1 else 1
  refine ⟨(|b'| + t ^ 2).toNat + 2, E' 0 - 2 * osum t E', ?_⟩
  intro p hpp hN
  have : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := by omega
  have hsmall : ∀ m : ℤ, |m| ≤ |t| → (((m ^ 2 + b') / (p : ℤ)).negOnePow : ℤ) = E' m := by
    intro m hm
    have hm2 : m ^ 2 ≤ t ^ 2 := sq_le_sq.2 hm
    have hlt : |m ^ 2 + b'| < (p : ℤ) := by
      have h1 := abs_add_le (m ^ 2) b'
      rw [abs_of_nonneg (sq_nonneg m)] at h1
      have : ((|b'| + t ^ 2).toNat : ℤ) = |b'| + t ^ 2 :=
        Int.toNat_of_nonneg (by positivity)
      have hN' : ((|b'| + t ^ 2).toNat : ℤ) + 2 < p := by exact_mod_cast hN
      linarith
    rw [ediv_small hlt]
    simp only [E']
    split_ifs <;> simp
  rw [monic_even' hp2 t b]
  have h0 := hsmall 0 (abs_nonneg t)
  simp only [zero_pow two_ne_zero, zero_add] at h0
  rw [h0, osum_congr hsmall]

end QuadraticFloor
