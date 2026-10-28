module

public import QuadraticFloor.Corollaries

@[expose] public section

/-!
# The coefficient five (Theorem 4.4, Corollary 4.5, Proposition 4.6)

The characters modulo `5` are `1, ξ, ξ², ξ̄`, determined by their value `1, i, -1, -i` at `2`. In the
square-class decomposition at `A = 5` the weights `conj ψ(B)²` for `B = 1, 3` are `1, 1, 1, 1` and
`1, -1, 1, -1`. So the difference of the two sums sees only the conjugate pair `ξ, ξ̄`, through
`B_{1,Θ_p} + conj B_{1,Θ_p} = 2 Re B_{1,Θ_p}`, and their sum sees only `1` and `ξ²`.
-/

namespace QuadraticFloor

open Finset

instance fact_one_lt_five : Fact (1 < 5) := ⟨by norm_num⟩

/-! ### The characters modulo `5` -/

lemma zmod5_eq_pow_lg (a : ZMod 5) (ha : a ≠ 0) : a = 2 ^ lg5 a := by revert a; decide

lemma xi_two : xi 2 = Complex.I := by
  show xiFun 2 = _
  simp only [xiFun, show (2 : ZMod 5) ≠ 0 by decide, ite_false, show lg5 2 = 1 by decide, pow_one]

lemma xi_three : xi 3 = -Complex.I := by
  show xiFun 3 = _
  simp only [xiFun, show (3 : ZMod 5) ≠ 0 by decide, ite_false, show lg5 3 = 3 by decide]
  rw [pow_three, ← mul_assoc, Complex.I_mul_I]; ring

lemma xi_four : xi 4 = -1 := by
  show xiFun 4 = _
  simp only [xiFun, show (4 : ZMod 5) ≠ 0 by decide, ite_false, show lg5 4 = 2 by decide, pow_two,
    Complex.I_mul_I]

lemma xi_zero : xi 0 = 0 := MulChar.map_nonunit _ not_isUnit_zero

/-- A character modulo `5` is determined by its value at `2`. -/
lemma char5_ext {ψ ψ' : DirichletCharacter ℂ 5} (h : ψ 2 = ψ' 2) : ψ = ψ' := by
  refine MulChar.ext' fun a => ?_
  by_cases ha : a = 0
  · rw [ha, MulChar.map_nonunit _ not_isUnit_zero, MulChar.map_nonunit _ not_isUnit_zero]
  · rw [zmod5_eq_pow_lg a ha, map_pow, map_pow, h]

lemma char5_two (ψ : DirichletCharacter ℂ 5) :
    ψ 2 = 1 ∨ ψ 2 = Complex.I ∨ ψ 2 = -1 ∨ ψ 2 = -Complex.I := by
  have h4 : ψ 2 ^ 4 = 1 := by rw [← map_pow, show (2 : ZMod 5) ^ 4 = 1 by decide, map_one]
  have hf : (ψ 2 - 1) * (ψ 2 + 1) * ((ψ 2 - Complex.I) * (ψ 2 + Complex.I)) = 0 := by
    have : (ψ 2 - Complex.I) * (ψ 2 + Complex.I) = ψ 2 ^ 2 + 1 := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [this]; linear_combination h4
  rcases mul_eq_zero.1 hf with h | h
  · rcases mul_eq_zero.1 h with h | h
    · left; linear_combination h
    · right; right; left; linear_combination h
  · rcases mul_eq_zero.1 h with h | h
    · right; left; linear_combination h
    · right; right; right; linear_combination h

lemma one_two : (1 : DirichletCharacter ℂ 5) 2 = 1 :=
  MulChar.one_apply (IsUnit.of_mul_eq_one (3 : ZMod 5) (by decide))

lemma xixi_two : (xi * xi) 2 = -1 := by
  rw [MulChar.mul_apply, xi_two, Complex.I_mul_I]

lemma starxi_two : (star xi) 2 = -Complex.I := by
  rw [MulChar.star_apply, xi_two]; simp

lemma univ_char5 :
    (univ : Finset (DirichletCharacter ℂ 5)) = {1, xi, xi * xi, star xi} := by
  ext ψ
  simp only [mem_univ, mem_insert, mem_singleton, true_iff]
  rcases char5_two ψ with h | h | h | h
  · left; exact char5_ext (h.trans one_two.symm)
  · right; left; exact char5_ext (h.trans xi_two.symm)
  · right; right; left; exact char5_ext (h.trans xixi_two.symm)
  · right; right; right; exact char5_ext (h.trans starxi_two.symm)

lemma I_ne_one : Complex.I ≠ 1 := by intro h; simpa using congrArg Complex.im h

lemma sum_char5 {M : Type*} [AddCommMonoid M] (F : DirichletCharacter ℂ 5 → M) :
    ∑ ψ, F ψ = F 1 + F xi + F (xi * xi) + F (star xi) := by
  have hv : ∀ ψ ψ' : DirichletCharacter ℂ 5, ψ 2 ≠ ψ' 2 → ψ ≠ ψ' := fun ψ ψ' h e => h (e ▸ rfl)
  have n1 : (1 : DirichletCharacter ℂ 5) ∉ ({xi, xi * xi, star xi} : Finset _) := by
    simp only [mem_insert, mem_singleton, not_or]
    refine ⟨hv _ _ ?_, hv _ _ ?_, hv _ _ ?_⟩ <;>
      rw [one_two] <;> simp only [xi_two, xixi_two, starxi_two] <;>
      intro h <;> simp [Complex.ext_iff] at h <;> norm_num at h
  have n2 : xi ∉ ({xi * xi, star xi} : Finset (DirichletCharacter ℂ 5)) := by
    simp only [mem_insert, mem_singleton, not_or]
    refine ⟨hv _ _ ?_, hv _ _ ?_⟩ <;>
      rw [xi_two] <;> simp only [xixi_two, starxi_two] <;>
      intro h <;> simp [Complex.ext_iff] at h <;> norm_num at h
  have n3 : xi * xi ∉ ({star xi} : Finset (DirichletCharacter ℂ 5)) := by
    simp only [mem_singleton]
    refine hv _ _ ?_
    rw [xixi_two, starxi_two]
    intro h; simp [Complex.ext_iff] at h
  rw [univ_char5, sum_insert n1, sum_insert n2, sum_insert n3, sum_singleton, add_assoc, add_assoc]

/-! ### The weights -/

lemma weight (ψ : DirichletCharacter ℂ 5) (B : ℤ) :
    (starRingEnd ℂ (ψ (B : ZMod 5))) ^ 2 = starRingEnd ℂ (ψ ((B : ZMod 5) ^ 2)) := by
  rw [map_pow, map_pow]

lemma three_sq : ((3 : ℤ) : ZMod 5) ^ 2 = 2 ^ 2 := by decide

/-! ### Conjugation -/

lemma bern_conj (q : ℕ) (f : ℕ → ℂ) :
    bern q (fun x => starRingEnd ℂ (f x)) = starRingEnd ℂ (bern q f) := by
  unfold bern
  rw [map_mul, map_sum]
  congr 1
  · simp
  · apply sum_congr rfl; intro x _; rw [map_mul, Complex.conj_natCast]

variable {p : ℕ} [hp : Fact p.Prime]

lemma vartheta_xi : vartheta p xi = Theta p := by
  funext x
  unfold vartheta Theta
  have : xi (-1) = -1 := by rw [show (-1 : ZMod 5) = 4 by decide, xi_four]
  rw [if_pos this]

lemma vartheta_starxi : vartheta p (star xi) = fun x => starRingEnd ℂ (Theta p x) := by
  funext x
  unfold vartheta Theta
  have : (star xi) (-1) = -1 := by
    rw [MulChar.star_apply, show (-1 : ZMod 5) = 4 by decide, xi_four]; simp
  rw [if_pos this, MulChar.star_apply, map_mul, map_mul, map_intCast, map_intCast,
    starRingEnd_apply]

lemma one_apply_nat (x : ℕ) :
    (1 : DirichletCharacter ℂ 5) (x : ZMod 5) = if 5 ∣ x then 0 else 1 := by
  by_cases h5 : 5 ∣ x
  · rw [if_pos h5, MulChar.map_nonunit, ]
    rw [(ZMod.natCast_eq_zero_iff x 5).2 h5]; exact not_isUnit_zero
  · rw [if_neg h5, MulChar.one_apply]
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5)

lemma xi_sq_nat (x : ℕ) : (xi (x : ZMod 5)) ^ 2 = (jacobiSym x 5 : ℂ) := by
  rw [jacobiSym.mod_left, ← ZMod.natCast_mod x 5]
  have : (x : ℤ) % ((5 : ℕ) : ℤ) = ((x % 5 : ℕ) : ℤ) := by push_cast; rfl
  rw [this]
  have h5 : x % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases (x % 5)
  · rw [Nat.cast_zero, xi_zero]; norm_num
  · simp
  · rw [Nat.cast_ofNat, xi_two, Complex.I_sq]; norm_num
  · rw [Nat.cast_ofNat, xi_three, neg_sq, Complex.I_sq]; norm_num
  · rw [Nat.cast_ofNat, xi_four]; norm_num

lemma vartheta_one : vartheta p (1 : DirichletCharacter ℂ 5) =
    fun x => (eta p x : ℂ) * (if 5 ∣ x then 0 else 1) := by
  funext x
  unfold vartheta
  have h1 : (1 : DirichletCharacter ℂ 5) (-1) ≠ -1 := by
    rw [MulChar.one_apply (IsUnit.neg isUnit_one)]; norm_num
  rw [if_neg h1, eta_mul_chi4_sq, one_apply_nat]

lemma vartheta_xixi : vartheta p (xi * xi) = fun x => (eta p x : ℂ) * (jacobiSym x 5 : ℂ) := by
  funext x
  unfold vartheta
  have h1 : (xi * xi) (-1) ≠ -1 := by
    rw [MulChar.mul_apply, show (-1 : ZMod 5) = 4 by decide, xi_four]; norm_num
  rw [if_neg h1, eta_mul_chi4_sq, MulChar.mul_apply, ← pow_two, xi_sq_nat]

/-! ### Theorem 4.4 and Corollary 4.5 -/

lemma admissible_five_one : Admissible 5 1 0 := ⟨odd_one, by decide, by norm_num, by norm_num⟩
lemma admissible_five_three : Admissible 5 3 0 := ⟨by decide, by decide, by norm_num, by norm_num⟩

/-- The two sums with `B = 1, 3`, each from Theorem 3.2 at `A = 5`. -/
lemma floorSum_five (hp2 : p ≠ 2) (hp5 : p ≠ 5) {B : ℤ} (hB : Admissible 5 B 0) :
    (floorSum 5 B 0 p : ℂ) = 1 - (1 / 4) *
      ∑ ψ : DirichletCharacter ℂ 5,
        starRingEnd ℂ (ψ ((B : ZMod 5) ^ 2)) * bern (40 * p) (vartheta p ψ) := by
  have hpA : ¬ p ∣ 5 := fun h => hp5 ((Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).1 h)
  have h := square_class_decomposition' (A := 5) hp2 (by decide) hpA hB
  push_cast at h
  rw [h, show Nat.totient 5 = 4 by decide, show 8 * 5 * p = 40 * p by ring]
  simp only [Int.negOnePow_zero, Units.val_one, Int.cast_one, Nat.cast_ofNat, weight]

/-- **Corollary 4.5, the quartic coordinate.** `Re B_{1,Θ_p} = 𝒮_{5,3,0}(p) - 𝒮_{5,1,0}(p)`. -/
theorem quartic_split' (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((floorSum 5 3 0 p - floorSum 5 1 0 p : ℤ) : ℝ) = (bern (40 * p) (Theta p)).re := by
  have h3 := floorSum_five hp2 hp5 admissible_five_three
  have h1 := floorSum_five hp2 hp5 admissible_five_one
  rw [sum_char5] at h3 h1
  simp only [Int.cast_one, one_pow, map_one, one_mul] at h1
  rw [three_sq] at h3
  simp only [map_pow, one_two, xi_two, xixi_two, starxi_two, map_one, one_pow, Complex.I_sq,
    neg_sq, map_neg] at h3
  rw [vartheta_starxi, bern_conj, vartheta_xi] at h3 h1
  have hdiff : ((floorSum 5 3 0 p - floorSum 5 1 0 p : ℤ) : ℂ) =
      (1 / 2) * (bern (40 * p) (Theta p) + starRingEnd ℂ (bern (40 * p) (Theta p))) := by
    push_cast
    rw [h3, h1]
    ring
  rw [Complex.add_conj] at hdiff
  have := congrArg Complex.re hdiff
  simp only [Complex.intCast_re] at this
  rw [this]
  simp

/-- **Theorem 4.4, the quadratic half (Bernoulli form).**
`𝒮_{5,1,0}(p) + 𝒮_{5,3,0}(p) - 2 = -(B_{1,η_p}^{(40p)} + B_{1,χ_{-40p}}^{(40p)})/2`, where `η_p` is
induced to modulus `40p` and `χ_{-40p} = η_p (·/5)`. By Dirichlet's class number formula the right
side is `h(-40p)/2 + (1 + (p/5)) h(-8p)/2`, which is not formalized. -/
theorem quadratic_half' (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((floorSum 5 1 0 p + floorSum 5 3 0 p - 2 : ℤ) : ℂ) = -(1 / 2) *
      (bern (40 * p) (fun x => (eta p x : ℂ) * (if 5 ∣ x then 0 else 1)) +
        bern (40 * p) (fun x => (eta p x : ℂ) * (jacobiSym x 5 : ℂ))) := by
  have h3 := floorSum_five hp2 hp5 admissible_five_three
  have h1 := floorSum_five hp2 hp5 admissible_five_one
  rw [sum_char5] at h3 h1
  simp only [Int.cast_one, one_pow, map_one, one_mul] at h1
  rw [three_sq] at h3
  simp only [map_pow, one_two, xi_two, xixi_two, starxi_two, map_one, one_pow, Complex.I_sq,
    neg_sq, map_neg] at h3
  rw [vartheta_one, vartheta_xixi] at h3 h1
  push_cast
  rw [h3, h1]
  ring

/-! ### Proposition 4.6 -/

/-- A sum of values in `{-1, 0, 1}` has the parity of the number of nonzero terms. -/
lemma sum_modEq_card {s : Finset ℕ} {f : ℕ → ℤ} (hf : ∀ j ∈ s, f j = 0 ∨ f j = 1 ∨ f j = -1) :
    ∑ j ∈ s, f j ≡ (s.filter fun j => f j ≠ 0).card [ZMOD 2] := by
  rw [card_filter]
  push_cast
  apply Int.ModEq.sum
  intro j hj
  rcases hf j hj with h | h | h <;> simp [h] <;> decide

/-- The number of vanishing terms in the progression `B² + 40 j`, `0 ≤ j ≤ (p-1)/2`, is `z_B`. -/
lemma card_zero_terms (hp2 : p ≠ 2) (hp5 : p ≠ 5) (B : ℤ) :
    (((range ((p + 1) / 2)).filter fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0).card : ℤ) =
      zB B p := by
  have hzero : ∀ j : ℕ, legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0 ↔ (p : ℤ) ∣ B ^ 2 + 40 * j := by
    intro j; rw [legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h40 : ¬ (p : ℤ) ∣ 40 := by
    intro h
    have h' : p ∣ 2 ^ 3 * 5 := by exact_mod_cast h
    rcases (Nat.Prime.dvd_mul hp.out).1 h' with h2 | h2
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h2))
    · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).1 h2)
  have huniq : ∀ j₁ ∈ range ((p + 1) / 2), ∀ j₂ ∈ range ((p + 1) / 2),
      (p : ℤ) ∣ B ^ 2 + 40 * j₁ → (p : ℤ) ∣ B ^ 2 + 40 * j₂ → j₁ = j₂ := by
    intro j₁ hj₁ j₂ hj₂ h₁ h₂
    have hd : (p : ℤ) ∣ 40 * ((j₁ : ℤ) - j₂) := by
      have := dvd_sub h₁ h₂; rw [show B ^ 2 + 40 * (j₁ : ℤ) - (B ^ 2 + 40 * j₂) =
        40 * ((j₁ : ℤ) - j₂) by ring] at this; exact this
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.out
    rcases hpr.dvd_or_dvd hd with h | h
    · exact absurd h h40
    · rw [mem_range] at hj₁ hj₂
      have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
      omega
  unfold zB
  split_ifs with hex
  · obtain ⟨j₀, hj₀, hd₀⟩ := hex
    have : (range ((p + 1) / 2)).filter (fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0) = {j₀} := by
      ext j
      simp only [mem_filter, mem_singleton, hzero]
      constructor
      · rintro ⟨hj, hd⟩; exact huniq j hj j₀ hj₀ hd hd₀
      · rintro rfl; exact ⟨hj₀, hd₀⟩
    rw [this, card_singleton]; rfl
  · simp only [not_exists, not_and] at hex
    have : (range ((p + 1) / 2)).filter (fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0) = ∅ := by
      ext j
      simp only [mem_filter, hzero, Finset.notMem_empty, iff_false, not_and]
      exact hex j
    rw [this, card_empty]; rfl

/-- `𝒮_{5,B,0}(p) - 1 ≡ 2((p+1)/2 - z_B) (mod 4)`. -/
lemma floorSum_five_modEq (hp2 : p ≠ 2) (hp5 : p ≠ 5) {B : ℤ} (hB : Odd B) :
    floorSum 5 B 0 p - 1 ≡ 2 * (((p + 1) / 2 : ℕ) - zB B p) [ZMOD 4] := by
  have hpA : ¬ (p : ℤ) ∣ 5 := by
    intro h
    have : p ∣ 5 := by exact_mod_cast h
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).1 this)
  have hAB : Even ((5 : ℤ) + B) := (by decide : Odd (5 : ℤ)).add_odd hB
  rw [root_count' hp2 0 hAB hpA, Int.negOnePow_zero, Units.val_one, one_mul, add_sub_cancel_left]
  have hs : ∑ j ∈ range ((p + 1) / 2), legendreSym p (B ^ 2 - 4 * 5 * 0 + 8 * 5 * j) =
      ∑ j ∈ range ((p + 1) / 2), legendreSym p (B ^ 2 + 40 * (j : ℤ)) :=
    sum_congr rfl fun j _ => by ring_nf
  rw [hs]
  have hmod := sum_modEq_card (s := range ((p + 1) / 2))
    (f := fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ))) (fun j _ => by
      by_cases h0 : legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0
      · left; exact h0
      · right
        exact legendreSym.eq_one_or_neg_one p (fun h => h0 ((legendreSym.eq_zero_iff p _).2 h)))
  have hcard := card_filter_add_card_filter_not (s := range ((p + 1) / 2))
    (fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0)
  rw [card_range] at hcard
  have hz := card_zero_terms hp2 hp5 B
  have hne : ((range ((p + 1) / 2)).filter fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) ≠ 0).card =
      (p + 1) / 2 - ((range ((p + 1) / 2)).filter
        fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0).card := by
    simp only [ne_eq]; omega
  rw [hne] at hmod
  have hle := card_filter_le (range ((p + 1) / 2)) (fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0)
  rw [card_range] at hle
  rw [Nat.cast_sub hle, hz] at hmod
  have := Int.ModEq.mul_left' (c := 2) hmod
  rw [show (2 : ℤ) * 2 = 4 by norm_num] at this
  exact this

/-- **Proposition 4.6.** `Re B_{1,Θ_p}` is an integer and `Re B_{1,Θ_p} ≡ 2 (z_1 - z_3) (mod 4)`;
in particular it is even. -/
theorem quartic_mod_four' (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ∃ m : ℤ, (bern (40 * p) (Theta p)).re = m ∧ m ≡ 2 * (zB 1 p - zB 3 p) [ZMOD 4] := by
  refine ⟨floorSum 5 3 0 p - floorSum 5 1 0 p, (quartic_split' hp2 hp5).symm, ?_⟩
  have h3 := floorSum_five_modEq hp2 hp5 (B := 3) (by decide)
  have h1 := floorSum_five_modEq hp2 hp5 (B := 1) odd_one
  have := h3.sub h1
  rw [show floorSum 5 3 0 p - 1 - (floorSum 5 1 0 p - 1) = floorSum 5 3 0 p - floorSum 5 1 0 p by
    ring] at this
  refine this.trans ?_
  rw [show 2 * ((((p + 1) / 2 : ℕ) : ℤ) - zB 3 p) - 2 * ((((p + 1) / 2 : ℕ) : ℤ) - zB 1 p) =
    2 * (zB 1 p - zB 3 p) by ring]

end QuadraticFloor
