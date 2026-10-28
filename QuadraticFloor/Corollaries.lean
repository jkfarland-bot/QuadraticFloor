module

public import QuadraticFloor.SquareClass

@[expose] public section

/-!
# Consequences of the root count and of Theorem 3.2

* Corollary 3.4: an admissible sum depends only on the square class `B² mod A`, and so does
  `(-1)^C`; every square class of units arises.
* Corollary 3.3: `𝒮_A(p) = 𝒮_{A,1,0}(p) = 1 - (1/φ(A)) ∑_ψ B_{1,ϑ_{p,ψ}}^{(8Ap)}`.
* Theorem 4.1 in Bernoulli form: `𝒮_1(p) = 1 - B_{1,η_p}^{(8p)}`; by Dirichlet's class number
  formula `B_{1,η_p} = -h(-8p)`, which is not formalized.
* Theorem 4.2 in Bernoulli form: `𝒮_3(p) = 1 - (B_{1,η_p}^{(24p)} + B_{1,χ_{-24p}}^{(24p)})/2`,
  where `η_p` is induced to modulus `24p` and `χ_{-24p} = η_p χ_{-4} χ_{-3}`.
-/

namespace QuadraticFloor

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Corollary 3.4 -/

/-- **Corollary 3.4.** Two admissible pairs with the same square class `B² mod A` give the same
floor sum and the same sign `(-1)^C`. -/
theorem floorSum_eq_of_sq_modEq' (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A)
    {B C B' C' : ℤ} (h : Admissible A B C) (h' : Admissible A B' C')
    (hBB : B ^ 2 ≡ B' ^ 2 [ZMOD A]) :
    floorSum A B C p = floorSum A B' C' p ∧ C.negOnePow = C'.negOnePow := by
  obtain ⟨d, hdD, hd1, hd4A, hd4, hd8⟩ := admissible_data hA h
  obtain ⟨d', hdD', hd1', hd4A', hd4', hd8'⟩ := admissible_data hA h'
  have hdvdA : (A : ℤ) ∣ (d' : ℤ) - d := by
    rw [hdD, hdD']
    have := hBB.dvd
    obtain ⟨k, hk⟩ := this
    exact ⟨k - 4 * (C' - C), by linear_combination hk⟩
  have hdvd4 : (4 : ℤ) ∣ (d' : ℤ) - d := by omega
  have hcop : IsCoprime (4 : ℤ) A := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime 4 A := by
      have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hA); simpa using this
    simpa [Int.gcd] using this
  have hdvd := hcop.mul_dvd hdvd4 hdvdA
  have heq : (d' : ℤ) - d = 0 := Int.eq_zero_of_abs_lt_dvd hdvd (by
    rw [abs_lt]; constructor <;> omega)
  have hdd : d = d' := by omega
  subst hdd
  have hC : C.negOnePow = C'.negOnePow := by
    rw [Int.negOnePow_eq_iff, Int.even_sub]
    rw [hd8] at hd8'
    by_cases hc : Even C <;> by_cases hc' : Even C' <;>
      simp only [hc, hc', ite_true, ite_false] at hd8' <;>
      first | exact iff_of_true hc hc' | exact iff_of_false hc hc' | omega
  refine ⟨?_, hC⟩
  have hAB : Even ((A : ℤ) + B) := (show Odd (A : ℤ) by exact_mod_cast hA).add_odd h.1
  have hAB' : Even ((A : ℤ) + B') := (show Odd (A : ℤ) by exact_mod_cast hA).add_odd h'.1
  have hpA' : ¬ (p : ℤ) ∣ (A : ℤ) := by exact_mod_cast hpA
  rw [root_count' hp2 C hAB hpA', root_count' hp2 C' hAB' hpA', ← hdD, ← hdD', hC]

/-- **Corollary 3.4, every square class arises.** For every `B₀` prime to `A` there is an admissible
pair `(B, C)` with `B ≡ B₀ (mod A)`. -/
theorem exists_admissible' {A : ℕ} (hA : Odd A) {B₀ : ℤ} (hB₀ : Int.gcd B₀ A = 1) :
    ∃ B C : ℤ, Admissible A B C ∧ B ≡ B₀ [ZMOD A] := by
  have hAz : Odd (A : ℤ) := by exact_mod_cast hA
  have hApos : (0 : ℤ) < A := by exact_mod_cast hA.pos
  obtain ⟨B, hBodd, hBmod, hBgcd⟩ : ∃ B : ℤ, Odd B ∧ B ≡ B₀ [ZMOD A] ∧ Int.gcd B A = 1 := by
    rcases Int.even_or_odd B₀ with hB | hB
    · refine ⟨B₀ + A, hB.add_odd hAz, ?_, ?_⟩
      · show (B₀ + A) % A = B₀ % A
        simp
      · rw [← Int.isCoprime_iff_gcd_eq_one] at hB₀ ⊢
        simpa using hB₀.add_mul_left_left 1
    · exact ⟨B₀, hB, rfl, hB₀⟩
  refine ⟨B, (B ^ 2 - 1) / (4 * A), ⟨hBodd, hBgcd, ?_, ?_⟩, hBmod⟩
  · have h1 := Int.emod_add_mul_ediv (B ^ 2 - 1) (4 * A)
    have h2 := Int.emod_nonneg (B ^ 2 - 1) (show (4 * (A : ℤ)) ≠ 0 by omega)
    linarith
  · have h1 := Int.emod_add_mul_ediv (B ^ 2 - 1) (4 * A)
    have h3 := Int.emod_lt_of_pos (B ^ 2 - 1) (show (0 : ℤ) < 4 * A by omega)
    rcases lt_or_eq_of_le (show B ^ 2 - 4 * A * ((B ^ 2 - 1) / (4 * A)) ≤ 4 * A by linarith)
      with hlt | heq
    · exact hlt
    · exfalso
      have hB2 : Odd (B ^ 2) := hBodd.pow
      have : Even (B ^ 2) := ⟨2 * A * ((B ^ 2 - 1) / (4 * A) + 1), by linarith⟩
      exact (Int.not_even_iff_odd.2 hB2) this

/-! ### Corollary 3.3 -/

/-- **Corollary 3.3.** `𝒮_A(p) = 1 - (1/φ(A)) ∑_ψ B_{1,ϑ_{p,ψ}}^{(8Ap)}`. -/
theorem floorSum_universal' (hp2 : p ≠ 2) {A : ℕ} [NeZero A] (hA : Odd A) (hpA : ¬ p ∣ A) :
    (floorSum A 1 0 p : ℂ) = 1 - (1 / (A.totient : ℂ)) *
      ∑ ψ : DirichletCharacter ℂ A, bern (8 * A * p) (vartheta p ψ) := by
  have hadm : Admissible A 1 0 := ⟨odd_one, by simp, by simp, by
    have := hA.pos; push_cast; omega⟩
  rw [square_class_decomposition' hp2 hA hpA hadm]
  simp

/-! ### The coefficient one -/

/-- **Theorem 4.1, Bernoulli form.** `𝒮_1(p) = ∑_{n<p} (-1)^{⌊n(n+1)/p⌋} = 1 - B_{1,η_p}^{(8p)}`. -/
theorem floorSum_one' (hp2 : p ≠ 2) :
    (floorSum 1 1 0 p : ℂ) = 1 - bern (8 * p) (fun x => (eta p x : ℂ)) := by
  have h := floorSum_universal' (A := 1) hp2 odd_one (fun h => by
    have := Nat.le_of_dvd one_pos h; have := hp.out.two_le; omega)
  have hsub : Subsingleton (DirichletCharacter ℂ 1) := ⟨fun ψ ψ' => MulChar.ext' fun a => by
    rw [Subsingleton.elim a 1, map_one, map_one]⟩
  rw [Fintype.sum_subsingleton _ 1] at h
  push_cast at h
  rw [h]
  simp only [Nat.totient_one, Nat.cast_one, div_one, one_mul]
  congr 2
  funext x
  unfold vartheta
  have h1 : (1 : DirichletCharacter ℂ 1) (-1) ≠ -1 := by
    rw [Subsingleton.elim (-1 : ZMod 1) 1, map_one]; norm_num
  rw [ite_of_neg h1, Subsingleton.elim (x : ZMod 1) 1, map_one, mul_one, eta_mul_chi4_sq]

/-! ### The coefficient three -/

/-- The odd character modulo `3`. -/
noncomputable def chi3 : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

lemma chi3_apply (x : ℕ) : chi3 (x : ZMod 3) = (legendreSym 3 x : ℂ) := by
  simp [chi3, legendreSym]

lemma chi3_two : chi3 2 = -1 := by
  have := chi3_apply 2
  rw [show legendreSym 3 ((2 : ℕ) : ℤ) = -1 by
    rw [legendreSym.mod]; decide] at this
  simpa using this

lemma zmod3_cases : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide

lemma char3_cases (ψ : DirichletCharacter ℂ 3) : ψ = 1 ∨ ψ = chi3 := by
  have h4 : ψ 2 ^ 2 = 1 := by rw [← map_pow, show (2 : ZMod 3) ^ 2 = 1 by decide, map_one]
  have hu : ∀ a : ZMod 3, a ≠ 0 → IsUnit a := by
    intro a ha; rcases zmod3_cases a with h | h | h
    · exact absurd h ha
    · rw [h]; exact isUnit_one
    · rw [h]; exact IsUnit.of_mul_eq_one (2 : ZMod 3) (by decide)
  rcases (mul_self_eq_one_iff (a := ψ 2)).1 (by rw [← pow_two]; exact h4) with h | h
  · left
    refine MulChar.ext' fun a => ?_
    rcases zmod3_cases a with ha | ha | ha
    · rw [ha, MulChar.map_nonunit _ (by decide), MulChar.map_nonunit _ (by decide)]
    · rw [ha, map_one, map_one]
    · rw [ha, h, MulChar.one_apply (hu 2 (by decide))]
  · right
    refine MulChar.ext' fun a => ?_
    rcases zmod3_cases a with ha | ha | ha
    · rw [ha, MulChar.map_nonunit _ (by decide), MulChar.map_nonunit _ (by decide)]
    · rw [ha, map_one, map_one]
    · rw [ha, h, chi3_two]

/-- **Theorem 4.2, Bernoulli form.**
`𝒮_3(p) = 1 - (B_{1,η_p}^{(24p)} + B_{1,χ_{-24p}}^{(24p)})/2`, where `η_p` is induced to modulus
`24p` (it vanishes on multiples of `3`) and `χ_{-24p} = η_p χ_{-4} (·/3)`. -/
theorem floorSum_three' (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (floorSum 3 1 0 p : ℂ) = 1 - (1 / 2) *
      (bern (24 * p) (fun x => (eta p x : ℂ) * (if 3 ∣ x then 0 else 1)) +
        bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
          (legendreSym 3 x : ℂ))) := by
  have hpA : ¬ p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 h)
  have h := floorSum_universal' (A := 3) hp2 (by decide) hpA
  have hne : (1 : DirichletCharacter ℂ 3) ≠ chi3 := by
    intro h; have := DFunLike.congr_fun h 2
    rw [chi3_two, MulChar.one_apply (IsUnit.of_mul_eq_one (2 : ZMod 3)
      (by decide))] at this; norm_num at this
  have huniv : (univ : Finset (DirichletCharacter ℂ 3)) = {1, chi3} := by
    ext ψ; simp only [mem_univ, mem_insert, mem_singleton, true_iff]; exact char3_cases ψ
  rw [huniv, sum_pair hne] at h
  push_cast at h
  rw [h, show Nat.totient 3 = 2 by decide, show 8 * 3 * p = 24 * p by ring]
  push_cast
  congr 3
  · congr 1
    funext x
    unfold vartheta
    have h1 : (1 : DirichletCharacter ℂ 3) (-1) ≠ -1 := by
      rw [MulChar.one_apply (IsUnit.neg isUnit_one)]; norm_num
    rw [ite_of_neg h1, eta_mul_chi4_sq]
    congr 1
    by_cases h3 : 3 ∣ x
    · rw [ite_of_pos h3, MulChar.map_nonunit]
      rw [(ZMod.natCast_eq_zero_iff x 3).2 h3]; exact not_isUnit_zero
    · rw [ite_of_neg h3, MulChar.one_apply]
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3))
  · congr 1
    funext x
    unfold vartheta
    have h1 : chi3 (-1) = -1 := by rw [show (-1 : ZMod 3) = 2 by decide, chi3_two]
    rw [ite_of_pos h1, chi3_apply]

end QuadraticFloor
