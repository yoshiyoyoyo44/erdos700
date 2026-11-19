import Erdos700.Arithmetic

namespace Erdos700

/-- On a composite prime power the minimum is the underlying prime. -/
theorem f_prime_power {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) : f (p ^ a) = p := by
  have hk : 2 ≤ p ^ (a - 1) := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hmul : p ^ (a - 1) * p = p ^ a := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ a)]
  have hhalf : p ^ (a - 1) ≤ p ^ a / 2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    rw [← hmul]
    exact Nat.mul_le_mul_left _ hp.two_le
  have hn : 4 ≤ p ^ a := by omega
  apply le_antisymm
  · apply (f_le_column hk hhalf).trans
    have hcol := Nat.gcd_dvd_left (p ^ a) ((p ^ a).choose (p ^ (a - 1)))
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hcol
    have hdiv := Nat.gcd_dvd_right (p ^ a) ((p ^ a).choose (p ^ (a - 1)))
    rw [hj] at hdiv
    have hkn : p ^ (a - 1) ≤ p ^ a := by omega
    have hval := (hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hkn)).mp hdiv
    rw [Nat.factorization_choose_prime_pow hp hkn (pow_ne_zero _ hp.ne_zero),
      Nat.factorization_pow_self hp] at hval
    change (p ^ a).gcd _ ≤ p
    rw [hj]
    calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
         _ = p := pow_one _
  · apply (le_f_iff hn).mpr
    intro k hk' hhalf'
    apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (pow_pos hp.pos _))
    exact Nat.dvd_gcd (dvd_pow_self _ (by omega)) (hp.dvd_choose_pow (by omega) (by omega))

theorem prime_power_original_ne {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    f (p ^ a) ≠ p ^ a / maxPrimePower (p ^ a) := by
  have hq : maxPrimePower (p ^ a) = p ^ a := by
    simp [maxPrimePower, Nat.primeFactors_prime_pow (by omega : a ≠ 0) hp, hp]
  rw [f_prime_power hp ha, hq, Nat.div_self (pow_pos hp.pos _)]
  exact hp.ne_one

theorem prime_power_largestPrime_iff {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    f (p ^ a) = p ^ a / maxPrime (p ^ a) ↔ a = 2 := by
  have hP : maxPrime (p ^ a) = p := by
    simp [maxPrime, Nat.primeFactors_prime_pow (by omega : a ≠ 0) hp]
  have hmul : p ^ (a - 1) * p = p ^ a := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ a)]
  rw [f_prime_power hp ha, hP, ← hmul, Nat.mul_div_cancel _ hp.pos]
  constructor
  · intro h
    have hpow : p ^ 1 = p ^ (a - 1) := by simpa only [pow_one] using h
    have := Nat.pow_right_injective hp.two_le hpow
    omega
  · rintro rfl
    simp

end Erdos700
