import Erdos700.PowerFamilies
import Erdos700.EightPrime

namespace Erdos700

/-- A finite obstruction test in the single prime base q. It depends on m, q, h, a only. -/
def excludesSmallGCDs (m q h a : ℕ) : Prop :=
  ∀ t : Fin (m*q^h/2+1), ∀ g : Fin m, 0 < t.val → 0 < g.val →
    m*q^h ∣ t.val*g.val → min a (g.val.factorization q) ≠
      min a (((m*q^h).choose t.val).factorization q)

/-- If the finite table excludes every small gcd, equality holds at every later exponent. -/
theorem power_equality_of_exclusions {m q h a e : ℕ} (hm : 2 ≤ m) (hq : q.Prime)
    (hqm : ¬q ∣ m) (he : 0 < e) (hh : h ≤ e) (ha : a ≤ e) (hcut : m ≤ q^(h+1))
    (exclude : excludesSmallGCDs m q h a) : f (m*q^e) = m := by
  let s := e-h
  let A := m*q^h
  let z := q^s
  have hz : 0 < z := pow_pos hq.pos _
  have hsum : h+s=e := Nat.add_sub_of_le hh
  have row : m*q^(h+s) = A*z := by dsimp [A,z]; rw [pow_add, Nat.mul_assoc]
  rw [← hsum]
  apply (power_candidate_criterion hm hq hqm (by omega) (Or.inl hcut)).mpr
  intro t ht hhalf
  let g := column (m*q^(h+s)) (t*z)
  change m ≤ g
  by_contra! hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.mul_pos (by omega) (pow_pos hq.pos _))
  have hd : A*z ∣ (t*g)*z := by
    have hd := dvd_index_mul_column (m*q^(h+s)) (t*z)
    change m*q^(h+s) ∣ t*z*g at hd
    rwa [row, Nat.mul_right_comm t z g] at hd
  have hAg : A ∣ t*g := (Nat.mul_dvd_mul_iff_right hz).mp hd
  have htv : t < A/2+1 := by dsimp [A]; omega
  have hv : g.factorization q = min e ((A.choose t).factorization q) := by
    rw [← hsum]; exact power_candidate_qVal (by omega) hq hqm (by omega)
  apply exclude ⟨t,htv⟩ ⟨g,hg⟩ ht hg0 hAg
  change min a (g.factorization q) = min a ((A.choose t).factorization q)
  rw [hv, ← min_assoc, min_eq_left ha]

private theorem four_three_exclusions : excludesSmallGCDs 4 3 1 2 := by
  unfold excludesSmallGCDs
  simp only [Nat.choose_eq_descFactorial_div_factorial, Nat.factorization_def _ Nat.prime_three]
  decide +kernel

private theorem six_five_exclusions : excludesSmallGCDs 6 5 1 2 := by
  unfold excludesSmallGCDs
  simp only [Nat.choose_eq_descFactorial_div_factorial, Nat.factorization_def _ (by decide : Nat.Prime 5)]
  decide +kernel

private theorem four_dvd_central_of_odd {x : ℕ} (hx : 3 ≤ x) (hodd : x % 2 = 1) :
    4 ∣ (4*x).choose (2*x) := by
  have h2 : ((4*x).choose (2*x)).factorization 2 = binaryWeight x := by
    rw [twoVal_choose (by omega), show 4*x-2*x=2*x by omega,
      show (Nat.digits 2 (2*x)).sum = binaryWeight x from digitSum_shift (by decide : 1<2) 1 x,
      show (Nat.digits 2 (4*x)).sum = binaryWeight x from digitSum_shift (by decide : 1<2) 2 x,
      Nat.add_sub_cancel]
  exact (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.choose_ne_zero (by omega : 2*x ≤ 4*x))).mpr
    (h2 ▸ (binaryWeight_odd hx hodd).1)

/-- For every odd prime q and every positive exponent e, the only exception is n=12. -/
theorem four_odd_prime_power {q e : ℕ} (hq : q.Prime) (hodd : q ≠ 2) (he : 0 < e) :
    f (4*q^e) = if q = 3 ∧ e = 1 then 3 else 4 := by
  have hq4 : ¬q ∣ 4 := fun hd => hodd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
    (hq.dvd_of_dvd_pow (show q ∣ 2^2 from hd)))
  by_cases h3 : q=3
  · subst q
    by_cases h1 : e=1
    · subst e; decide +kernel
    · rw [if_neg (by simp [h1])]
      exact power_equality_of_exclusions (h := 1) (a := 2) (by decide) hq hq4 he (by omega)
        (by omega) (by decide) four_three_exclusions
  · rw [if_neg (by simp [h3])]
    have hqbig : 4 ≤ q := by have := hq.two_le; omega
    have hx : 3 ≤ q^e := (by omega : 3 ≤ q).trans (Nat.le_self_pow he.ne' _)
    have ho : Odd q := Nat.odd_iff.mpr (hq.eq_two_or_odd.resolve_left hodd)
    have test := power_candidate_criterion (h := 0) (s := e) (by decide : 2 ≤ 4) hq hq4
      (by omega) (Or.inl (by simpa using hqbig))
    simp only [zero_add, pow_zero, Nat.mul_one] at test
    apply test.mpr
    intro t ht hhalf
    have hcases : t=1 ∨ t=2 := by omega
    rcases hcases with rfl | rfl
    · simpa only [one_mul, Nat.mul_comm (q^e) 4] using
        (column_primePowerFactor (e := e) hq (by decide : 0<4) hq4).ge
    · exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by omega : 0<4*q^e))
        (Nat.dvd_gcd (dvd_mul_right 4 _) (four_dvd_central_of_odd hx (Nat.odd_iff.mp (show Odd (q^e) from ho.pow))))

/-- Every positive exponent attains the value six, including the seed n=30. -/
theorem six_five_power {e : ℕ} (he : 0 < e) : f (6*5^e) = 6 := by
  by_cases h1 : e=1
  · subst e
    unfold f column
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide +kernel
  · exact power_equality_of_exclusions (h := 1) (a := 2) (by decide) (by decide) (by decide)
      he (by omega) (by omega) (by decide) six_five_exclusions

end Erdos700
