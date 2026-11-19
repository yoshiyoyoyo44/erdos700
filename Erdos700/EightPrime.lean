import Erdos700.LargePrime
import Erdos700.Splits
import Mathlib.Tactic.IntervalCases

namespace Erdos700

/-- Number of ones in the binary expansion. -/
def binaryWeight (x : ℕ) : ℕ := (Nat.digits 2 x).sum

private theorem binaryWeight_one_iff (x : ℕ) :
    binaryWeight x = 1 ↔ ∃ j : ℕ, x = 2 ^ j := by
  constructor
  · intro hx
    have hcard : (canonical 2 x).card = 1 := by simpa [binaryWeight] using hx
    obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp hcard
    exact ⟨j, by simpa only [value_canonical, value_singleton] using congrArg (value 2) hj⟩
  · rintro ⟨j, rfl⟩
    have h := digitSum_shift (by decide : 1 < 2) j 1
    simpa [binaryWeight, Nat.digits_of_lt 2 1 (by decide) (by decide)] using h

private theorem binaryWeight_odd {x : ℕ} (hx : 3 ≤ x) (ho : x % 2 = 1) :
    2 ≤ binaryWeight x ∧ (binaryWeight x ≤ 2 ↔ ∃ j : ℕ, x = 2 ^ j + 1) := by
  have hw : binaryWeight x = 1 + binaryWeight (x / 2) := by
    rw [binaryWeight, Nat.digits_def' (by decide : 1 < 2) (by omega : 0 < x), ho, List.sum_cons]
    rfl
  have hp : 0 < binaryWeight (x / 2) := by
    by_contra! h
    have hcard : (canonical 2 (x / 2)).card = 0 := by rw [card_canonical]; change binaryWeight _ = 0; omega
    have hz : x / 2 = 0 := calc
      x / 2 = value 2 (canonical 2 (x / 2)) := (value_canonical _ _).symm
      _ = value 2 0 := congrArg _ (Multiset.card_eq_zero.mp hcard)
      _ = 0 := rfl
    omega
  refine ⟨by omega, ?_⟩
  constructor
  · intro h
    obtain ⟨j, hj⟩ := (binaryWeight_one_iff (x / 2)).mp (by omega)
    exact ⟨j+1, by rw [pow_succ]; omega⟩
  · rintro ⟨j, hj⟩
    cases j with
    | zero => simp at hj; omega
    | succ j =>
      rw [pow_succ] at hj
      have ht := (binaryWeight_one_iff (x / 2)).mpr ⟨j, by omega⟩
      omega

private theorem eight_column_multiple {p t : ℕ} (hp : p.Prime) (hp8 : 8 < p) (ht : t ≤ 8) :
    column (8 * p) (t * p) = 2 ^ min 3 (((8 * p).choose (t * p)).factorization 2) := by
  rw [large_prime_column hp hp8 ht]
  exact gcd_primePower_eq Nat.prime_two 3 (Nat.choose_ne_zero (Nat.mul_le_mul_right p ht))

private theorem eight_even_columns (p : ℕ) (hp : p.Prime) (hp8 : 8 < p) :
    column (8 * p) (2 * p) = 2 ^ min 3 (binaryWeight (3 * p)) ∧
    column (8 * p) (4 * p) = 2 ^ min 3 (binaryWeight p) := by
  have row : (Nat.digits 2 (8 * p)).sum = binaryWeight p :=
    digitSum_shift (by decide : 1 < 2) 3 p
  have two : (Nat.digits 2 (2 * p)).sum = binaryWeight p :=
    digitSum_shift (by decide : 1 < 2) 1 p
  have four : (Nat.digits 2 (4 * p)).sum = binaryWeight p :=
    digitSum_shift (by decide : 1 < 2) 2 p
  have six : (Nat.digits 2 (6 * p)).sum = binaryWeight (3 * p) := by
    simpa [binaryWeight, ← Nat.mul_assoc] using digitSum_shift (by decide : 1 < 2) 1 (3 * p)
  constructor
  · rw [eight_column_multiple hp hp8 (by decide), twoVal_choose (by omega),
      show 8 * p - 2 * p = 6 * p by omega, two, six, row, Nat.add_sub_cancel_left]
  · rw [eight_column_multiple hp hp8 (by decide), twoVal_choose (by omega),
      show 8 * p - 4 * p = 4 * p by omega, four, row, Nat.add_sub_cancel]

/-- For p > 8 prime, the only columns that can improve on 8 are 2p and 4p. -/
theorem eight_prime_min {p : ℕ} (hp : p.Prime) (hp8 : 8 < p) :
    f (8 * p) = 2 ^ min 3 (min (binaryWeight p) (binaryWeight (3 * p))) := by
  obtain ⟨h2, h4⟩ := eight_even_columns p hp hp8
  let w := min 3 (min (binaryWeight p) (binaryWeight (3 * p)))
  have hle8 : 2 ^ w ≤ 8 := Nat.pow_le_pow_right (by decide : 0 < 2) (min_le_left _ _ : w ≤ 3)
  have hle2 : 2 ^ w ≤ column (8 * p) (2 * p) := by
    rw [h2]; apply Nat.pow_le_pow_right (by decide); dsimp [w]; omega
  have hle4 : 2 ^ w ≤ column (8 * p) (4 * p) := by
    rw [h4]; apply Nat.pow_le_pow_right (by decide); dsimp [w]; omega
  have hf2 : f (8 * p) ≤ column (8 * p) (2 * p) := f_le_column (by omega) (by omega)
  have hf4 : f (8 * p) ≤ column (8 * p) (4 * p) := f_le_column (by omega) (by omega)
  apply le_antisymm
  · rw [h2] at hf2
    rw [h4] at hf4
    rcases le_total (binaryWeight p) (binaryWeight (3*p)) with h | h
    · simpa only [min_eq_left h] using hf4
    · simpa only [min_eq_right h] using hf2
  · apply (le_f_iff (by omega)).mpr
    intro k hk hkn
    change 2 ^ w ≤ column _ _
    have hg0 : 0 < column (8 * p) k := Nat.gcd_pos_of_pos_left _ (by omega)
    have hdiv := dvd_index_mul_column (8 * p) k
    by_cases hpk : p ∣ k
    · obtain ⟨t, ht⟩ := hpk
      have hk' : k = t * p := ht.trans (Nat.mul_comm _ _)
      have htp : t * p ≤ 4 * p := by omega
      have ht4 := Nat.le_of_mul_le_mul_right htp hp.pos
      have ht0 : t ≠ 0 := by rintro rfl; simp at hk'; omega
      rw [hk']
      have hodd (t : ℕ) (hc : Nat.Coprime 8 (t * p)) :
          8 ≤ column (8 * p) (t * p) := by
        apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by omega))
        exact hc.dvd_of_dvd_mul_left ((dvd_mul_right 8 p).trans (dvd_index_mul_column _ _))
      have hp2 : Nat.Coprime 2 p := Nat.prime_two.coprime_iff_not_dvd.mpr
        (fun h => (by omega : 2 ≠ p) ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h))
      have h8 : Nat.Coprime 8 p := hp2.pow_left 3
      interval_cases t
      · contradiction
      · exact hle8.trans (hodd 1 (by simpa using h8))
      · exact hle2
      · exact hle8.trans (hodd 3 ((by decide : Nat.Coprime 8 3).mul_right h8))
      · exact hle4
    · have hpg := (hp.dvd_mul.mp ((dvd_mul_left p 8).trans hdiv)).resolve_left hpk
      exact hle8.trans ((by omega : 8 ≤ p).trans (Nat.le_of_dvd hg0 hpg))

/-- An explicit classification: the exceptional primes have p-1 or 3p-1 a power of two. -/
theorem eight_prime_classification {p : ℕ} (hp : p.Prime) (hp8 : 8 < p) :
    (f (8 * p) = 4 ↔ ∃ j : ℕ, p = 2 ^ j + 1 ∨ 3 * p = 2 ^ j + 1) ∧
    (f (8 * p) = 8 ↔ ¬ ∃ j : ℕ, p = 2 ^ j + 1 ∨ 3 * p = 2 ^ j + 1) := by
  have ho := hp.eq_two_or_odd.resolve_left (by omega)
  obtain ⟨h1, hs1⟩ := binaryWeight_odd (x := p) (by omega) ho
  obtain ⟨h3, hs3⟩ := binaryWeight_odd (x := 3*p) (by omega) (by omega)
  have hex : (∃ j : ℕ, p = 2 ^ j + 1 ∨ 3 * p = 2 ^ j + 1) ↔
      binaryWeight p ≤ 2 ∨ binaryWeight (3 * p) ≤ 2 := by
    rw [exists_or, ← hs1, ← hs3]
  rw [eight_prime_min hp hp8, hex]
  by_cases h : binaryWeight p ≤ 2 ∨ binaryWeight (3 * p) ≤ 2
  · rw [show min 3 (min (binaryWeight p) (binaryWeight (3 * p))) = 2 by omega]
    simp [h]
  · rw [show min 3 (min (binaryWeight p) (binaryWeight (3 * p))) = 3 by omega]
    simp [h]

end Erdos700
