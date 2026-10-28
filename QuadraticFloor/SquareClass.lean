module

public import QuadraticFloor.HalfPeriod

@[expose] public section

/-!
# The square-class decomposition (Theorem 3.2)

For a positive odd `A`, an odd prime `p ∤ A` and an admissible pair `(B, C)`,

`𝒮_{A,B,C}(p) = (-1)^C - (1/φ(A)) ∑_{ψ mod A} conj(ψ(B))² B_{1,ϑ_{p,ψ}}^{(8Ap)}`.

The proof follows the paper. The root count becomes a sum of `η_p` over the residue class of
`D = B² - 4AC` modulo `8A` in `[1, 4Ap]` (the window form). The condition modulo `A` is expanded by
orthogonality of the characters modulo `A`. The condition modulo `8` is written with `χ_{-4}`,
`χ_8` and `χ_{-8}`; the terms with `χ_{±8}` are periodic under `x ↦ x + 4Ap` and vanish by
Lemma 3.1(1), and of the two terms with `1` and `χ_{-4}` the even one vanishes by Lemma 3.1(2). The
survivor is `ϑ_{p,ψ}`, and Lemma 3.1(3) turns its half sum into `-2 B_{1,ϑ_{p,ψ}}^{(8Ap)}`.
-/

namespace QuadraticFloor

open Finset

/-! ### Casts and characters -/

lemma cast_add_of_dvd (x m n : ℕ) (h : n ∣ m) : ((x + m : ℕ) : ZMod n) = x := by
  rw [Nat.cast_add, (ZMod.natCast_eq_zero_iff m n).2 h, add_zero]

lemma cast_sub_of_dvd {q x : ℕ} (n : ℕ) (hx : x ≤ q) (h : n ∣ q) :
    ((q - x : ℕ) : ZMod n) = -(x : ZMod n) := by
  rw [Nat.cast_sub hx, (ZMod.natCast_eq_zero_iff q n).2 h, zero_sub]

lemma cast8_add_half {A p : ℕ} (hAp : Odd (A * p)) (x : ℕ) :
    ((x + 4 * A * p : ℕ) : ZMod 8) = (x : ZMod 8) + 4 := by
  have h1 : (A * p) % 2 = 1 := Nat.odd_iff.1 hAp
  have hm : (4 * A * p) % 8 = 4 % 8 := by rw [show 4 * A * p = 4 * (A * p) by ring]; omega
  have h4 : ((4 * A * p : ℕ) : ZMod 8) = 4 := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ 8).2 hm
    rw [Nat.cast_ofNat] at this
    exact this
  rw [Nat.cast_add, h4]

lemma isUnit_intCast_of_gcd {A : ℕ} {B : ℤ} (h : Int.gcd B A = 1) : IsUnit (B : ZMod A) := by
  have hc : Nat.Coprime B.natAbs A := by rw [Int.gcd_eq_natAbs] at h; simpa using h
  rcases Int.natAbs_eq B with hB | hB
  · rw [hB, Int.cast_natCast]; exact (ZMod.isUnit_iff_coprime _ _).2 hc
  · rw [hB, Int.cast_neg, Int.cast_natCast]; exact ((ZMod.isUnit_iff_coprime _ _).2 hc).neg

lemma char_inv_eq_star {A : ℕ} [NeZero A] (ψ : DirichletCharacter ℂ A) {a : ZMod A}
    (ha : IsUnit a) : ψ a⁻¹ = star (ψ a) := by
  have h1 : ψ a⁻¹ * ψ a = 1 := by rw [← map_mul, mul_comm, ZMod.mul_inv_of_unit a ha, map_one]
  have h2 : star (ψ a) * ψ a = 1 := by
    rw [← MulChar.star_apply, MulChar.star_eq_inv, ← MulChar.mul_apply, MulChar.inv_mul,
      MulChar.one_apply ha]
  have h3 : ψ a ≠ 0 := by intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
  exact mul_right_cancel₀ h3 (h1.trans h2.symm)

lemma psi_neg_one {A : ℕ} (ψ : DirichletCharacter ℂ A) : ψ (-1) = 1 ∨ ψ (-1) = -1 :=
  ψ.even_or_odd

lemma psi_reflect {A : ℕ} (ψ : DirichletCharacter ℂ A) {q x : ℕ} (hx : x ≤ q) (hq : A ∣ q) :
    ψ ((q - x : ℕ) : ZMod A) = ψ (-1) * ψ (x : ZMod A) := by
  rw [cast_sub_of_dvd A hx hq, ← map_mul, neg_one_mul]

/-! ### The two indicator expansions -/

/-- Orthogonality modulo `A`: the indicator of `x ≡ d (mod A)`, with `d ≡ B²`. -/
lemma ind_mod_A {A : ℕ} [NeZero A] {B : ℤ} (hB : Int.gcd B A = 1) {d : ℕ}
    (hd : (d : ZMod A) = (B : ZMod A) ^ 2) (x : ℕ) :
    (if x % A = d % A then (1 : ℂ) else 0) =
      (1 / (A.totient : ℂ)) *
        ∑ ψ : DirichletCharacter ℂ A, (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 * ψ (x : ZMod A) := by
  have hu : IsUnit (d : ZMod A) := by rw [hd]; exact (isUnit_intCast_of_gcd hB).pow 2
  have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (x : ZMod A)
  have hw : ∀ ψ : DirichletCharacter ℂ A,
      ψ (d : ZMod A)⁻¹ = (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 := by
    intro ψ
    rw [char_inv_eq_star ψ hu, hd, map_pow, star_pow, starRingEnd_apply]
  simp_rw [hw] at horth
  rw [horth]
  have htot : (A.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne A))).ne'
  by_cases h : x % A = d % A
  · have : (d : ZMod A) = x := (ZMod.natCast_eq_natCast_iff' d x A).2 h.symm
    simp only [h, this, ite_true]
    field_simp
  · have : (d : ZMod A) ≠ x := fun e => h ((ZMod.natCast_eq_natCast_iff' d x A).1 e).symm
    simp only [h, this, ite_false, mul_zero]

/-- The indicator of `x ≡ d (mod 8)` for odd `x` and `d ≡ 1 (mod 4)`. -/
lemma ind_mod_eight {x d : ℕ} (hx : Odd x) (hd : d % 4 = 1) :
    (if x % 8 = d % 8 then (1 : ℂ) else 0) = (1 / 4) * (1 + (ZMod.χ₄ (x : ZMod 4) : ℂ) +
      (ZMod.χ₈ (d : ZMod 8) : ℂ) * ((ZMod.χ₈ (x : ZMod 8) : ℂ) + (ZMod.χ₈' (x : ZMod 8) : ℂ))) := by
  rw [ZMod.χ₄_nat_eq_if_mod_four, ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈_nat_eq_if_mod_eight,
    ZMod.χ₈'_nat_eq_if_mod_eight]
  have hx2 : x % 2 = 1 := Nat.odd_iff.1 hx
  have ex2 : x % 2 = x % 8 % 2 := (Nat.mod_mod_of_dvd x (by norm_num)).symm
  have ex4 : x % 4 = x % 8 % 4 := (Nat.mod_mod_of_dvd x (by norm_num)).symm
  have ed2 : d % 2 = d % 8 % 2 := (Nat.mod_mod_of_dvd d (by norm_num)).symm
  have h8 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  have hd8 : d % 8 = 1 ∨ d % 8 = 5 := by omega
  rw [ex2, ex4, ed2]
  rcases h8 with h | h | h | h <;> rcases hd8 with h' | h' <;> simp [h, h'] <;> norm_num

lemma mod_eight_mul_iff {A x d : ℕ} (hA : Odd A) (hd : d < 8 * A) :
    x % (8 * A) = d ↔ x % 8 = d % 8 ∧ x % A = d % A := by
  have hc : Nat.Coprime 8 A := by
    have := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.2 hA); simpa using this
  have : x % (8 * A) = d ↔ x ≡ d [MOD 8 * A] := by
    unfold Nat.ModEq; rw [Nat.mod_eq_of_lt hd]
  rw [this, ← Nat.modEq_and_modEq_iff_modEq_mul hc]
  rfl

/-! ### Data of an admissible pair -/

variable {p : ℕ} [hp : Fact p.Prime]

lemma not_dvd_eight_mul (hp2 : p ≠ 2) {A : ℕ} (hpA : ¬ p ∣ A) : ¬ p ∣ 8 * A := by
  intro h
  rcases (Nat.Prime.dvd_mul hp.out).1 h with h8 | h8
  · have : p ∣ 2 ^ 3 := by simpa using h8
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow this))
  · exact hpA h8

/-- The discriminant `D = B² - 4AC` of an admissible pair, as a natural number, and its
properties. -/
lemma admissible_data {A : ℕ} (hA : Odd A) {B C : ℤ} (hBC : Admissible A B C) :
    ∃ d : ℕ, (d : ℤ) = B ^ 2 - 4 * A * C ∧ 1 ≤ d ∧ d < 4 * A ∧ d % 4 = 1 ∧
      (d % 8 = if Even C then 1 else 5) := by
  obtain ⟨hB, -, hD1, hD2⟩ := hBC
  refine ⟨(B ^ 2 - 4 * A * C).toNat, Int.toNat_of_nonneg (by omega), by omega, by omega, ?_⟩
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨t, ht⟩ := Int.even_mul_succ_self b
  obtain ⟨a, ha⟩ := hA
  have hA' : (A : ℤ) = 2 * a + 1 := by exact_mod_cast ha
  have key : (2 * b + 1) ^ 2 - 4 * (A : ℤ) * C = 1 + 8 * (t - a * C) - 4 * C := by
    rw [hA']; linear_combination 4 * ht
  have hnn : 0 ≤ (2 * b + 1) ^ 2 - 4 * (A : ℤ) * C := by omega
  have hcast : (((2 * b + 1) ^ 2 - 4 * (A : ℤ) * C).toNat : ℤ) =
      1 + 8 * (t - a * C) - 4 * C := by rw [Int.toNat_of_nonneg hnn, key]
  generalize ((2 * b + 1) ^ 2 - 4 * (A : ℤ) * C).toNat = d at hcast ⊢
  generalize t - a * C = w at hcast
  rcases Int.even_or_odd C with ⟨c, hc⟩ | ⟨c, hc⟩
  · have : Even C := ⟨c, hc⟩
    simp only [this, ite_true]
    omega
  · have : ¬ Even C := Int.not_even_iff_odd.2 ⟨c, hc⟩
    simp only [this, ite_false]
    omega

omit hp in
/-- `κ_p(D) = (-1)^C` for the discriminant of an admissible pair. -/
lemma kap_disc {d : ℕ} {C : ℤ} (hd : d % 8 = if Even C then 1 else 5) :
    kap p (d : ZMod 8) = (C.negOnePow : ℤ) := by
  by_cases hC : Even C
  · simp only [hC, ite_true] at hd
    rw [Int.negOnePow_even C hC, show (d : ZMod 8) = 1 by
      rw [show (1 : ZMod 8) = ((1 : ℕ) : ZMod 8) by norm_num, ZMod.natCast_eq_natCast_iff']; omega,
      kap_one]
    rfl
  · simp only [hC, ite_false] at hd
    rw [Int.negOnePow_odd C (Int.not_even_iff_odd.1 hC), show (d : ZMod 8) = 5 by
      rw [show (5 : ZMod 8) = ((5 : ℕ) : ZMod 8) by norm_num, ZMod.natCast_eq_natCast_iff']; omega,
      kap_five]
    rfl

/-! ### The window form (Lemma 2.3) -/

/-- **Lemma 2.3 (window form).** `𝒮_{A,B,C}(p) - (-1)^C = 2 ∑ η_p(x)` over the `x ∈ [1, 4Ap]`
with `x ≡ D (mod 8A)`. -/
theorem window' (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A) {B C : ℤ}
    (hBC : Admissible A B C) {d : ℕ} (hdD : (d : ℤ) = B ^ 2 - 4 * A * C) (hd4A : d < 4 * A)
    (hd8 : d % 8 = if Even C then 1 else 5) :
    floorSum A B C p - (C.negOnePow : ℤ) =
      2 * ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = d), eta p x := by
  have hAB : Even ((A : ℤ) + B) := by
    have h1 : Odd (A : ℤ) := by exact_mod_cast hA
    exact h1.add_odd hBC.1
  have hpA' : ¬ (p : ℤ) ∣ (A : ℤ) := by exact_mod_cast hpA
  rw [root_count' hp2 C hAB hpA', ← hdD]
  have hterm : ∀ j : ℕ, (C.negOnePow : ℤ) * legendreSym p ((d : ℤ) + 8 * A * j) =
      eta p (d + 8 * A * j) := by
    intro j
    rw [eta_eq' hp2, show ((d + 8 * A * j : ℕ) : ZMod 8) = (d : ZMod 8) by
      rw [show d + 8 * A * j = d + 8 * (A * j) by ring]; exact cast_add_of_dvd _ _ _ (dvd_mul_right _ _),
      kap_disc hd8]
    push_cast; ring
  have hreindex : ∑ j ∈ range ((p + 1) / 2), eta p (d + 8 * A * j) =
      ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = d), eta p x := by
    have hA0 : 0 < A := hA.pos
    have h8A : 0 < 8 * A := by omega
    have hd1 : 1 ≤ d := by
      have := hBC.2.2.1; omega
    obtain ⟨m, hm⟩ := odd_of_ne_two hp2
    refine sum_nbij' (fun j => d + 8 * A * j) (fun x => x / (8 * A)) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [mem_range] at hj
      rw [mem_filter, mem_Icc]
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · have hj' : 2 * j ≤ p - 1 := by omega
        have : 8 * A * j ≤ 4 * A * (p - 1) := by
          rw [show 8 * A * j = 4 * A * (2 * j) by ring]; exact Nat.mul_le_mul_left _ hj'
        have h2 : 4 * A * (p - 1) + 4 * A = 4 * A * p := by
          rw [← Nat.mul_add_one]; congr 1; omega
        omega
      · rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
    · intro x hx
      rw [mem_filter, mem_Icc] at hx
      rw [mem_range]
      obtain ⟨⟨-, hx2⟩, hx3⟩ := hx
      have hdiv := Nat.mod_add_div x (8 * A)
      rw [hx3] at hdiv
      have : 8 * A * (x / (8 * A)) < 4 * A * p := by omega
      have : 4 * A * (2 * (x / (8 * A))) < 4 * A * p := by
        rw [show 4 * A * (2 * (x / (8 * A))) = 8 * A * (x / (8 * A)) by ring]; exact this
      have := Nat.lt_of_mul_lt_mul_left this
      omega
    · intro j _
      rw [Nat.add_mul_div_left _ _ h8A, Nat.div_eq_of_lt (by omega), zero_add]
    · intro x hx
      rw [mem_filter, mem_Icc] at hx
      have hdiv := Nat.mod_add_div x (8 * A)
      rw [hx.2] at hdiv
      exact hdiv
    · intro j _; rfl
  rw [← hreindex, ← sum_congr rfl fun j _ => hterm j, mul_add, mul_one, add_sub_cancel_left,
    mul_sum, mul_sum, mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-! ### Vanishing of the periodic and even terms -/

variable {A : ℕ}

/-- Terms with `χ_{±8}` are periodic under `x ↦ x + 4Ap` and vanish (Lemma 3.1(1)). -/
lemma sum_eta_psi_c8 (hp2 : p ≠ 2) (hA : Odd A) (hpA : ¬ p ∣ A) (ψ : DirichletCharacter ℂ A)
    (c : ZMod 8 → ℂ) (hc : ∀ y, c (y + 4) = -c y) :
    ∑ x ∈ Icc 1 (4 * A * p), (eta p x : ℂ) * ψ (x : ZMod A) * c (x : ZMod 8) = 0 := by
  have hAp : Odd (A * p) := hA.mul (odd_of_ne_two hp2)
  apply half_sum_zero_of_periodic _ (h := 4 * A * p)
  · intro x
    rw [eta_add_half hp2 hA, cast8_add_half hAp,
      cast_add_of_dvd x _ A ⟨4 * p, by ring⟩, hc]
    push_cast; ring
  · rw [show 2 * (4 * A * p) = 8 * A * p by ring]
    have := sum_mul_legendre_eq_zero hp2
      (fun x => (kap p (x : ZMod 8) : ℂ) * ψ (x : ZMod A) * c (x : ZMod 8))
      (m := 8 * A) (not_dvd_eight_mul hp2 hpA) (by
        intro x
        rw [cast_add_of_dvd x _ 8 ⟨A, rfl⟩, cast_add_of_dvd x _ A ⟨8, by ring⟩])
    rw [← this]
    apply sum_congr rfl
    intro x _
    rw [eta_eq' hp2]
    push_cast; ring

/-- An even, anti-periodic product `η_p ψ c` has vanishing half sum (Lemma 3.1(2)). -/
lemma sum_eta_psi_even (hp2 : p ≠ 2) (hA : Odd A) (ψ : DirichletCharacter ℂ A) (c : ℕ → ℂ)
    (s : ℂ) (hcper : ∀ x, c (x + 4 * A * p) = c x)
    (hcref : ∀ x ≤ 8 * A * p, c (8 * A * p - x) = s * c x) (hs : s * ψ (-1) = -1) :
    ∑ x ∈ Icc 1 (4 * A * p), (eta p x : ℂ) * ψ (x : ZMod A) * c x = 0 := by
  apply half_sum_zero_of_even _ (h := 4 * A * p)
  · intro x
    rw [eta_add_half hp2 hA, cast_add_of_dvd x _ A ⟨4 * p, by ring⟩, hcper]
    push_cast; ring
  · rw [eta_of_even (⟨0, rfl⟩ : Even 0)]; simp
  · intro x hx
    rw [show 2 * (4 * A * p) = 8 * A * p by ring] at hx ⊢
    rw [eta_reflect hp2 ⟨A, by ring⟩ hx, psi_reflect ψ hx ⟨8 * p, by ring⟩, hcref x hx]
    push_cast
    linear_combination (-(eta p x : ℂ) * ψ (x : ZMod A) * c x) * hs

lemma chi4_add (A p x : ℕ) : ZMod.χ₄ ((x + 4 * A * p : ℕ) : ZMod 4) = ZMod.χ₄ (x : ZMod 4) := by
  rw [cast_add_of_dvd x _ 4 ⟨A * p, by ring⟩]

lemma chi4_reflect (A p : ℕ) {x : ℕ} (hx : x ≤ 8 * A * p) :
    ZMod.χ₄ ((8 * A * p - x : ℕ) : ZMod 4) = -ZMod.χ₄ (x : ZMod 4) := by
  rw [cast_sub_of_dvd 4 hx ⟨2 * A * p, by ring⟩]
  generalize (x : ZMod 4) = y
  revert y; decide

lemma eta_mul_chi4_sq (p x : ℕ) : (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) ^ 2 = eta p x := by
  by_cases hx : Even x
  · simp [eta_of_even hx]
  · have hx2 : x % 2 = 1 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hx)
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    have : x % 4 = 1 ∨ x % 4 = 3 := by omega
    rcases this with h | h <;> simp [h, hx2]

/-- The windowed character sum for one `ψ` is the half sum of `ϑ_{p,ψ}`. -/
lemma sum_window_char (hp2 : p ≠ 2) (hA : Odd A) (hpA : ¬ p ∣ A) (ψ : DirichletCharacter ℂ A)
    (k : ℂ) :
    ∑ x ∈ Icc 1 (4 * A * p), (eta p x : ℂ) * ψ (x : ZMod A) *
      (1 + (ZMod.χ₄ (x : ZMod 4) : ℂ) + k * ((ZMod.χ₈ (x : ZMod 8) : ℂ) + (ZMod.χ₈' (x : ZMod 8) : ℂ)))
      = ∑ x ∈ Icc 1 (4 * A * p), vartheta p ψ x := by
  have h8 := sum_eta_psi_c8 hp2 hA hpA ψ (fun y => (ZMod.χ₈ y : ℂ)) (by
    intro y; have : ZMod.χ₈ (y + 4) = -ZMod.χ₈ y := by revert y; decide
    simp [this])
  have h8' := sum_eta_psi_c8 hp2 hA hpA ψ (fun y => (ZMod.χ₈' y : ℂ)) (by
    intro y; have : ZMod.χ₈' (y + 4) = -ZMod.χ₈' y := by revert y; decide
    simp [this])
  have hsplit : ∀ x ∈ Icc 1 (4 * A * p), (eta p x : ℂ) * ψ (x : ZMod A) *
      (1 + (ZMod.χ₄ (x : ZMod 4) : ℂ) + k * ((ZMod.χ₈ (x : ZMod 8) : ℂ) + (ZMod.χ₈' (x : ZMod 8) : ℂ)))
      = (eta p x : ℂ) * ψ (x : ZMod A) * 1 +
        (eta p x : ℂ) * ψ (x : ZMod A) * (ZMod.χ₄ (x : ZMod 4) : ℂ) +
        k * ((eta p x : ℂ) * ψ (x : ZMod A) * (ZMod.χ₈ (x : ZMod 8) : ℂ) +
          (eta p x : ℂ) * ψ (x : ZMod A) * (ZMod.χ₈' (x : ZMod 8) : ℂ)) := by
    intro x _; ring
  rw [sum_congr rfl hsplit, sum_add_distrib, sum_add_distrib, ← mul_sum, sum_add_distrib]
  beta_reduce at h8 h8'
  rw [h8, h8', add_zero, mul_zero, add_zero]
  rcases psi_neg_one ψ with hψ | hψ
  · -- `ψ` even: the term with `χ_{-4}` vanishes
    have hper : ∀ x, (fun x : ℕ => (ZMod.χ₄ (x : ZMod 4) : ℂ)) (x + 4 * A * p) =
        (fun x : ℕ => (ZMod.χ₄ (x : ZMod 4) : ℂ)) x := by
      intro x
      beta_reduce
      rw [chi4_add]
    have href : ∀ x ≤ 8 * A * p, (fun x : ℕ => (ZMod.χ₄ (x : ZMod 4) : ℂ)) (8 * A * p - x) =
        -1 * (fun x : ℕ => (ZMod.χ₄ (x : ZMod 4) : ℂ)) x := by
      intro x hx
      beta_reduce
      rw [chi4_reflect A p hx]
      push_cast; ring
    have h4 := sum_eta_psi_even hp2 hA ψ (fun x => (ZMod.χ₄ (x : ZMod 4) : ℂ)) (-1)
      hper href (by rw [hψ]; ring)
    beta_reduce at h4
    rw [h4, add_zero]
    apply sum_congr rfl
    intro x _
    unfold vartheta
    have : ψ (-1) ≠ -1 := by rw [hψ]; norm_num
    rw [if_neg this, mul_one, eta_mul_chi4_sq]
  · -- `ψ` odd: the term with `1` vanishes
    have h1 := sum_eta_psi_even hp2 hA ψ (fun _ => (1 : ℂ)) 1
      (fun x => rfl) (fun x _ => by rw [one_mul]) (by rw [hψ]; ring)
    beta_reduce at h1
    rw [h1, zero_add]
    apply sum_congr rfl
    intro x _
    unfold vartheta
    rw [if_pos hψ]
    ring

/-- `ϑ_{p,ψ}` changes sign under `x ↦ x + 4Ap`. -/
lemma vartheta_add_half (hp2 : p ≠ 2) (hA : Odd A) (ψ : DirichletCharacter ℂ A) (x : ℕ) :
    vartheta p ψ (x + 4 * A * p) = -vartheta p ψ x := by
  unfold vartheta
  rw [eta_add_half hp2 hA, chi4_add, cast_add_of_dvd x _ A ⟨4 * p, by ring⟩]
  push_cast; ring

/-! ### Theorem 3.2 -/

/-- **Theorem 3.2 (square-class decomposition).** -/
theorem square_class_decomposition' (hp2 : p ≠ 2) [NeZero A] (hA : Odd A) (hpA : ¬ p ∣ A)
    {B C : ℤ} (hBC : Admissible A B C) :
    (floorSum A B C p : ℂ) = (C.negOnePow : ℤ) - (1 / (A.totient : ℂ)) *
      ∑ ψ : DirichletCharacter ℂ A, (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 *
        bern (8 * A * p) (vartheta p ψ) := by
  obtain ⟨d, hdD, hd1, hd4A, hd4, hd8⟩ := admissible_data hA hBC
  have hwin := window' hp2 hA hpA hBC hdD hd4A hd8
  have hdA : (d : ZMod A) = (B : ZMod A) ^ 2 := by
    have : ((d : ℤ) : ZMod A) = ((B ^ 2 - 4 * A * C : ℤ) : ZMod A) := by rw [hdD]
    push_cast at this
    rw [this, ZMod.natCast_self]; ring
  have hd8A : d < 8 * A := by omega
  have hh : 0 < 4 * A * p := by
    have := hA.pos; have := hp.out.pos; positivity
  -- expand the indicator of `x ≡ d (mod 8A)` for every `x`
  have hpt : ∀ x ∈ Icc 1 (4 * A * p),
      (if x % (8 * A) = d then (eta p x : ℂ) else 0) =
        (1 / (4 * (A.totient : ℂ))) * ∑ ψ : DirichletCharacter ℂ A,
          (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 * ((eta p x : ℂ) * ψ (x : ZMod A) *
            (1 + (ZMod.χ₄ (x : ZMod 4) : ℂ) + (ZMod.χ₈ (d : ZMod 8) : ℂ) *
              ((ZMod.χ₈ (x : ZMod 8) : ℂ) + (ZMod.χ₈' (x : ZMod 8) : ℂ)))) := by
    intro x _
    by_cases hx : Even x
    · simp [eta_of_even hx]
    have hxo : Odd x := Nat.not_even_iff_odd.1 hx
    have e1 : (if x % (8 * A) = d then (eta p x : ℂ) else 0) =
        (if x % 8 = d % 8 then (1 : ℂ) else 0) * (if x % A = d % A then (1 : ℂ) else 0) *
          (eta p x : ℂ) := by
      by_cases h8 : x % 8 = d % 8 <;> by_cases hA' : x % A = d % A <;>
        simp [mod_eight_mul_iff hA hd8A, h8, hA']
    rw [e1, ind_mod_eight hxo hd4, ind_mod_A hBC.2.1 hdA x, mul_sum, mul_sum, sum_mul, mul_sum]
    apply sum_congr rfl
    intro ψ _
    ring
  have hfilter : ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = d), (eta p x : ℂ) =
      ∑ x ∈ Icc 1 (4 * A * p), (if x % (8 * A) = d then (eta p x : ℂ) else 0) := by
    rw [sum_filter]
  have hmain : ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = d), (eta p x : ℂ) =
      (1 / (4 * (A.totient : ℂ))) * ∑ ψ : DirichletCharacter ℂ A,
        (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 * (-2 * bern (8 * A * p) (vartheta p ψ)) := by
    rw [hfilter, sum_congr rfl hpt, ← mul_sum, sum_comm]
    congr 1
    apply sum_congr rfl
    intro ψ _
    rw [← mul_sum, sum_window_char hp2 hA hpA ψ, show 8 * A * p = 2 * (4 * A * p) by ring,
      bern_antiperiodic _ hh (vartheta_add_half hp2 hA ψ)]
    ring
  have hwinC : (floorSum A B C p : ℂ) - ((C.negOnePow : ℤ) : ℂ) =
      2 * ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = d), (eta p x : ℂ) := by
    exact_mod_cast hwin
  have htot : (A.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 hA.pos).ne'
  rw [hmain] at hwinC
  have : (floorSum A B C p : ℂ) = ((C.negOnePow : ℤ) : ℂ) + 2 * ((1 / (4 * (A.totient : ℂ))) *
      ∑ ψ : DirichletCharacter ℂ A,
        (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 * (-2 * bern (8 * A * p) (vartheta p ψ))) := by
    rw [← hwinC]; ring
  have hs : ∑ ψ : DirichletCharacter ℂ A,
      (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 * (-2 * bern (8 * A * p) (vartheta p ψ)) =
      -2 * ∑ ψ : DirichletCharacter ℂ A,
        (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 * bern (8 * A * p) (vartheta p ψ) := by
    rw [mul_sum]; exact sum_congr rfl fun ψ _ => by ring
  rw [this, hs]
  field_simp
  ring

end QuadraticFloor
