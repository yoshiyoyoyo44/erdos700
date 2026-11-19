import Erdos700.Arithmetic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum

namespace Erdos700

/-- Absorption for the binomial coefficient, with its common factors with n retained. -/
theorem dvd_index_mul_column (n k : ℕ) : n ∣ k * column n k := by
  have hc : n ∣ k * n.choose k := by
    cases n with
    | zero => cases k <;> simp
    | succ n =>
      cases k with
      | zero => simp
      | succ k =>
        exact ⟨n.choose k, by rw [Nat.add_one_mul_choose_eq, Nat.mul_comm]⟩
  simpa only [column, Nat.gcd_mul_left] using Nat.dvd_gcd (dvd_mul_left n k) hc

/-- If the gcd is small, the index must absorb the remaining power of p. -/
theorem pow_dvd_index_of_small_column {p s h n k : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hd : p ^ (s + h) ∣ n) (hg : column n k < p ^ (h + 1)) : p ^ s ∣ k := by
  by_cases hk : k = 0
  · simp [hk]
  have hg0 : 0 < column n k := Nat.gcd_pos_of_pos_left _ hn
  have hval := (hp.pow_dvd_iff_le_factorization (Nat.mul_ne_zero hk hg0.ne')).mp
    (hd.trans (dvd_index_mul_column n k))
  rw [Nat.factorization_mul hk hg0.ne', Finsupp.add_apply] at hval
  have hbound : (column n k).factorization p ≤ h := by
    by_contra! hlt
    exact (not_le_of_gt hg) (Nat.le_of_dvd hg0 ((hp.pow_dvd_iff_le_factorization hg0.ne').mpr hlt))
  exact (hp.pow_dvd_iff_le_factorization hk).mpr (by omega)

/-- Multiplication by a power of the base adds only zero digits. -/
theorem digitSum_shift {p : ℕ} (hp : 1 < p) (s x : ℕ) :
    (p.digits (p ^ s * x)).sum = (p.digits x).sum := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · simp [Nat.digits_base_pow_mul hp hx]

/-- Kummer's formula after multiplying the row and column by the same power of p. -/
theorem factorization_choose_shift {p n k : ℕ} (hp : p.Prime) (s : ℕ) (hk : k ≤ n) :
    ((p ^ s * n).choose (p ^ s * k)).factorization p = (n.choose k).factorization p := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  apply Nat.eq_of_mul_eq_mul_left (by have := hp.two_le; omega : 0 < p - 1)
  rw [sub_one_mul_padicValNat_choose_eq_sub_sum_digits (Nat.mul_le_mul_left _ hk),
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits hk, ← Nat.mul_sub]
  simp only [digitSum_shift hp.one_lt]

/-- The binary digit-sum form, with no subtraction in the coefficient's arguments. -/
theorem twoVal_choose {n k : ℕ} (hk : k ≤ n) :
    (n.choose k).factorization 2 =
      (Nat.digits 2 k).sum + (Nat.digits 2 (n - k)).sum - (Nat.digits 2 n).sum := by
  simpa [Nat.factorization_def _ Nat.prime_two] using
    (sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) hk)

private theorem dvd_iff_of_modEq {p x y : ℕ} (h : x ≡ y [MOD p]) : p ∣ x ↔ p ∣ y := by
  rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
  exact ⟨h.symm.trans, h.trans⟩

/-- Doubling a ternary expansion produces a carry exactly when a digit 2 occurs. -/
theorem three_dvd_central_iff (x : ℕ) : 3 ∣ (2 * x).choose x ↔ 2 ∈ Nat.digits 3 x := by
  by_cases hx : x = 0
  · simp [hx]
  have hi := three_dvd_central_iff (x / 3)
  have hr := Nat.mod_lt x (by decide : 0 < 3)
  rw [Nat.digits_def' (by decide : 1 < 3) (Nat.pos_of_ne_zero hx), List.mem_cons]
  rw [dvd_iff_of_modEq (Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (p := 3) (n := 2 * x) (k := x))]
  rcases (show x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 by omega) with h | h | h
  · rw [h, show (2 * x) / 3 = 2 * (x / 3) by omega]
    simpa using hi
  · rw [h, show (2 * x) % 3 = 2 by omega, show (2 * x) / 3 = 2 * (x / 3) by omega]
    simpa [Nat.prime_three.dvd_mul] using hi
  · simp [h, show (2 * x) % 3 = 1 by omega]
termination_by x
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hx) (by decide)

/-- Once 2^(e-3) is removed, only 36 indices and eight possible small gcds remain. -/
private theorem small9_table : ∀ t : Fin 37, ∀ g : Fin 9, 0 < t.val → 0 < g.val →
    72 ∣ t.val * g.val → g.val.factorization 2 =
      (Nat.digits 2 t.val).sum + (Nat.digits 2 (72 - t.val)).sum - (Nat.digits 2 72).sum →
    t.val = 36 ∧ g.val = 4 := by decide +kernel

private theorem factorization_gcd_at {n c : ℕ} (hn : n ≠ 0) (hc : c ≠ 0) (p : ℕ) :
    (n.gcd c).factorization p = min (n.factorization p) (c.factorization p) := by
  simp only [Nat.factorization_gcd hn hc, Finsupp.inf_apply]

private theorem nine_small_column {s k : ℕ} (hk : 0 < k) (hhalf : k ≤ 2 ^ s * 36)
    (hs : 1 ≤ s) (hg : column (2 ^ s * 72) k < 9) :
    k = 2 ^ s * 36 ∧ column (2 ^ s * 72) k = 4 := by
  let z := 2 ^ s
  let g := column (z * 72) k
  have hz : 0 < z := pow_pos (by decide) _
  have hn : 0 < z * 72 := by omega
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hn
  have hpow : 2 ^ (s + 3) ∣ z * 72 := by
    exact ⟨9, by dsimp [z]; rw [pow_add]; ring⟩
  obtain ⟨t, ht⟩ : z ∣ k :=
    pow_dvd_index_of_small_column Nat.prime_two hn hpow (by change g < 16; change g < 9 at hg; omega)
  have ht0 : 0 < t := by rw [ht] at hk; exact Nat.pos_of_mul_pos_left hk
  have ht36 : t ≤ 36 := by rw [ht] at hhalf; exact Nat.le_of_mul_le_mul_left hhalf hz
  have hdiv : 72 ∣ t * g := by
    have hh := dvd_index_mul_column (z * 72) k
    change z * 72 ∣ k * g at hh
    rw [ht, Nat.mul_assoc] at hh
    exact (Nat.mul_dvd_mul_iff_left hz).mp hh
  have hc : (z * 72).choose k ≠ 0 := Nat.choose_ne_zero (by change k ≤ z * 36 at hhalf; omega)
  have hgv := factorization_gcd_at hn.ne' hc 2
  change g.factorization 2 = _ at hgv
  have hnval : (z * 72).factorization 2 = s + 3 := by
    rw [Nat.factorization_mul hz.ne' (by decide), Finsupp.add_apply]
    change (2 ^ s).factorization 2 + _ = _
    rw [Nat.factorization_pow_self Nat.prime_two]
    congr 1
    decide +kernel
  rw [hnval, ht, factorization_choose_shift Nat.prime_two s (by omega : t ≤ 72),
    twoVal_choose (by omega : t ≤ 72)] at hgv
  change g < 9 at hg
  have small : ∀ i : Fin 9, i.val.factorization 2 ≤ 3 := by decide +kernel
  have hbound := small ⟨g, hg⟩
  obtain ⟨ht', hg'⟩ := small9_table ⟨t, by omega⟩ ⟨g, hg⟩ ht0 hg0 hdiv (by dsimp at *; omega)
  exact ⟨ht.trans (congrArg (z * ·) ht'), hg'⟩

/-- The gcd of a prime power and a nonzero coefficient is determined by its valuation. -/
theorem gcd_primePower_eq {p c : ℕ} (hp : p.Prime) (e : ℕ) (hc : c ≠ 0) :
    (p ^ e).gcd c = p ^ min e (c.factorization p) := by
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p ^ e) c)
  have hv := factorization_gcd_at (pow_ne_zero e hp.ne_zero) hc p
  rw [hi, Nat.factorization_pow_self hp, Nat.factorization_pow_self hp] at hv
  rw [hi, hv]

/-- The complete value on the family 9 times a power of two, for every e ≥ 4. -/
theorem nine_mul_two_pow {e : ℕ} (he : 4 ≤ e) :
    f (9 * 2 ^ e) = if 2 ∈ Nat.digits 3 (2 ^ (e - 1)) then 9 else 4 := by
  let s := e - 3
  let z := 2 ^ s
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hz : 0 < z := pow_pos (by decide) _
  have hrow : 9 * 2 ^ e = z * 72 := by
    have he' : e = s + 3 := by dsimp [s]; omega
    calc 9 * 2 ^ e = 9 * 2 ^ (s + 3) := by rw [he']
         _ = z * 72 := by dsimp [z]; rw [pow_add]; ring
  have hmid : z * 36 = 9 * 2 ^ (e - 1) := by
    have hej : e - 1 = s + 2 := by dsimp [s]; omega
    rw [hej, pow_add]; dsimp [z]; ring
  have hfull : 9 * 2 ^ e = 2 * (z * 36) := by omega
  have hn : 4 ≤ 9 * 2 ^ e := by omega
  have hmid3 : 3 ∣ (9 * 2 ^ e).choose (z * 36) ↔ 2 ∈ Nat.digits 3 (2 ^ (e - 1)) := by
    rw [hfull, three_dvd_central_iff, hmid]
    change 2 ∈ Nat.digits 3 (3 ^ 2 * 2 ^ (e - 1)) ↔ _
    rw [Nat.digits_base_pow_mul (by decide : 1 < 3) (pow_pos (by decide : 0 < 2) _)]
    simp
  have hmid2 : ((9 * 2 ^ e).choose (z * 36)).factorization 2 = 2 := by
    rw [hrow, factorization_choose_shift Nat.prime_two s (by decide : 36 ≤ 72),
      twoVal_choose (by decide : 36 ≤ 72)]
    decide +kernel
  have onlyMiddle (k : ℕ) (hk : 2 ≤ k) (hhalf : k ≤ 9 * 2 ^ e / 2)
      (hg : column (9 * 2 ^ e) k < 9) : k = z * 36 ∧ column (9 * 2 ^ e) k = 4 := by
    rw [hrow] at hg ⊢
    exact nine_small_column (by omega) (by omega) hs hg
  split_ifs with hdigit
  · apply le_antisymm
    · have hc := column_primePowerFactor (p := 2) (e := e) (m := 9) Nat.prime_two (by decide) (by decide)
      rw [Nat.mul_comm (2 ^ e) 9] at hc
      calc f (9 * 2 ^ e) ≤ column (9 * 2 ^ e) (2 ^ e) :=
             f_le_column (Nat.le_self_pow (by omega : e ≠ 0) 2) (by omega)
           _ = 9 := hc
    · apply (le_f_iff hn).mpr
      intro k hk hhalf
      by_contra! hg
      obtain ⟨rfl, heq⟩ := onlyMiddle k hk hhalf hg
      have hd : 3 ∣ column (9 * 2 ^ e) (z * 36) :=
        Nat.dvd_gcd ((by decide : 3 ∣ 9).trans (dvd_mul_right 9 _)) (hmid3.mpr hdigit)
      rw [heq] at hd
      omega
  · have h3 : Nat.Coprime 9 ((9 * 2 ^ e).choose (z * 36)) :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr (mt hmid3.mp hdigit)).pow_left 2
    have hc : column (9 * 2 ^ e) (z * 36) = 4 := by
      unfold column
      rw [h3.gcd_mul_left_cancel, gcd_primePower_eq Nat.prime_two _ (Nat.choose_ne_zero (by omega)),
        hmid2, min_eq_right (by omega : 2 ≤ e)]
      decide
    apply le_antisymm
    · rw [← hc]
      exact f_le_column (by omega) (by omega)
    · apply (le_f_iff hn).mpr
      intro k hk hhalf
      by_contra! hg
      have := (onlyMiddle k hk hhalf (by omega)).2
      omega

/-- Finiteness of the exceptional exponents is exactly the finiteness assertion in #406. -/
theorem nine_exceptions_finite_iff :
    {e : ℕ | 4 ≤ e ∧ f (9 * 2 ^ e) < 9}.Finite ↔
      {t : ℕ | 2 ∉ Nat.digits 3 (2 ^ t)}.Finite := by
  rw [Set.finite_iff_bddAbove, Set.finite_iff_bddAbove]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨max 2 B, ?_⟩
    intro t ht
    by_cases hsmall : t ≤ 2
    · exact hsmall.trans (le_max_left _ _)
    · have he : 4 ≤ t + 1 := by omega
      have hmem : t + 1 ∈ {e : ℕ | 4 ≤ e ∧ f (9 * 2 ^ e) < 9} := by
        refine ⟨he, ?_⟩
        rw [nine_mul_two_pow he]
        simpa only [Nat.add_sub_cancel, if_neg ht] using (by decide : 4 < 9)
      have := hB hmem
      omega
  · rintro ⟨B, hB⟩
    refine ⟨B + 1, ?_⟩
    rintro e ⟨he, h⟩
    have hex : e - 1 ∈ {t : ℕ | 2 ∉ Nat.digits 3 (2 ^ t)} := by
      intro hdigit
      rw [nine_mul_two_pow he, if_pos hdigit] at h
      omega
    have := hB hex
    omega

end Erdos700
