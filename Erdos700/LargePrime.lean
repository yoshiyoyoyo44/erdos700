import Erdos700.Families

namespace Erdos700

/-- At a multiple of a prime larger than the cofactor, Lucas removes that prime from the gcd. -/
theorem large_prime_column {m p t : ℕ} (hp : p.Prime) (hmp : m < p) (ht : t ≤ m) :
    column (m * p) (t * p) = Nat.gcd m ((m * p).choose (t * p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hlucas : (m * p).choose (t * p) ≡ m.choose t [MOD p] := by
    simpa [Nat.mul_comm p] using
      (Choose.choose_mul_mul_modEq_choose_nat (p := p) (a := m) (b := t))
  have hcop : p.Coprime ((m * p).choose (t * p)) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have hdiv := Nat.modEq_zero_iff_dvd.mp (hlucas.symm.trans (Nat.modEq_zero_iff_dvd.mpr hd))
    have hpos := hp.factorization_pos_of_dvd (Nat.choose_ne_zero ht) hdiv
    rw [Nat.factorization_choose_eq_zero_of_lt hmp] at hpos
    omega
  exact hcop.gcd_mul_right_cancel m

/-- This test for a fixed cofactor has only ⌊m/2⌋ columns, independently of the prime. -/
theorem fixed_cofactor_iff {m p : ℕ} (hm : 2 ≤ m) (hp : p.Prime) (hmp : m < p) :
    f (m * p) = m ↔ ∀ t, 0 < t → 2 * t ≤ m → m ∣ (m * p).choose (t * p) := by
  have hn : 4 ≤ m * p := by nlinarith [hp.two_le]
  have hpcol : column (m * p) p = m := by
    simpa [Nat.mul_comm p] using column_primePowerFactor (e := 1) hp (by omega : 0 < m)
      (fun hd => (Nat.le_of_dvd (by omega : 0 < m) hd).not_gt hmp)
  constructor
  · intro heq t ht hhalf
    have hk := Nat.mul_le_mul_right p hhalf
    have hle := f_le_column (n := m*p) (k := t*p) (by nlinarith [hp.two_le])
      (by simpa only [Nat.le_div_iff_mul_le (by decide : 0 < 2), mul_assoc, mul_comm, mul_left_comm] using hk)
    rw [heq, large_prime_column hp hmp (by omega)] at hle
    have hge := Nat.gcd_le_left ((m*p).choose (t*p)) (by omega : 0 < m)
    exact (Nat.gcd_eq_left_iff_dvd.mp (le_antisymm hge hle))
  · intro h
    have hhalf : p ≤ m*p/2 := by rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]; nlinarith
    apply le_antisymm ((f_le_column hp.two_le hhalf).trans_eq hpcol)
    apply (le_f_iff hn).mpr
    intro k hk hhalf
    by_cases hpk : p ∣ k
    · obtain ⟨t, rfl⟩ := hpk
      have ht : 0 < t := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hk
      have hkm := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hhalf
      have ht2 : 2 * t ≤ m :=
        Nat.le_of_mul_le_mul_left (by simpa [mul_assoc, mul_comm, mul_left_comm] using hkm) hp.pos
      rw [Nat.mul_comm p t, large_prime_column hp hmp (by omega), Nat.gcd_eq_left (h t ht ht2)]
    · have hd := (hp.dvd_mul.mp ((dvd_mul_left p m).trans (dvd_index_mul_column (m*p) k))).resolve_left hpk
      exact hmp.le.trans (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by omega)) hd)

private theorem residue_of_dvd_add {M x v t : ℕ} (hd : M ∣ x + v) (ht : 0 < t * v)
    (hlt : t * v < M) : (t * x) % M = M - t * v := by
  have hdiv : M ∣ t * x + t * v := by simpa only [← Nat.mul_add] using dvd_mul_of_dvd_right hd t
  let r := t * x % M
  have hr : r < M := Nat.mod_lt _ (by omega)
  have hz : (r + t*v) % M = 0 := by
    simpa only [r, Nat.add_mod (t*x) (t*v), Nat.mod_eq_of_lt hlt, Nat.mod_mod] using
      Nat.mod_eq_zero_of_dvd hdiv
  change r = M - t*v
  by_cases hsmall : r + t*v < M
  · rw [Nat.mod_eq_of_lt hsmall] at hz
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : M ≤ r + t*v),
      Nat.mod_eq_of_lt (by omega : r + t*v - M < M)] at hz
    omega

/-- A run of all-maximal digits forces a carries in every split tx + (m-t)x.
The congruence says the run begins at position d, with the lower d digits arbitrary. -/
theorem block_forces_prime_power {ℓ m x a h d v t : ℕ} (hℓ : ℓ.Prime) (hh : 0 < h)
    (hm : m ≤ ℓ ^ h) (hv : 0 < v) (hvd : v ≤ ℓ ^ d)
    (hblock : ℓ ^ (d + h + a - 1) ∣ x + v) (ht : 0 < t) (htm : t < m) :
    ℓ ^ a ∣ (m*x).choose (t*x) := by
  have hkn := Nat.mul_le_mul_right x htm.le
  let b := max (d+h+a) (Nat.log ℓ (m*x) + 1)
  have hlog : Nat.log ℓ (m*x) < b := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  rw [hℓ.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hkn), Nat.factorization_choose hℓ hkn hlog]
  have hsub : Finset.Ico (d+h) (d+h+a) ⊆ (Finset.Ico 1 b).filter
      (fun i => ℓ ^ i ≤ t*x % ℓ ^ i + (m*x - t*x) % ℓ ^ i) := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hhi.trans_le (le_max_left _ _)⟩, ?_⟩
    let M := ℓ ^ i
    have hdiv : M ∣ x+v := (pow_dvd_pow ℓ (by omega : i ≤ d+h+a-1)).trans hblock
    have hmv : m*v ≤ M := calc
      m*v ≤ ℓ^h * ℓ^d := Nat.mul_le_mul hm hvd
      _ = ℓ^(d+h) := by rw [pow_add, Nat.mul_comm]
      _ ≤ M := Nat.pow_le_pow_right hℓ.pos hlo
    have hmt : m - t < m := by omega
    have hsum : t*v + (m-t)*v = m*v := by rw [← Nat.add_mul, Nat.add_sub_of_le htm.le]
    change M ≤ (t*x) % M + (m*x-t*x) % M
    rw [← Nat.sub_mul, residue_of_dvd_add hdiv (Nat.mul_pos ht hv)
        ((Nat.mul_lt_mul_of_pos_right htm hv).trans_le hmv),
      residue_of_dvd_add hdiv (Nat.mul_pos (by omega : 0 < m-t) hv)
        ((Nat.mul_lt_mul_of_pos_right hmt hv).trans_le hmv)]
    omega
  simpa using Finset.card_le_card hsub

/-- If every prime base dividing m supplies one such block in p, then the minimum is m. -/
theorem fixed_cofactor_of_blocks {m p : ℕ} (hm : 2 ≤ m) (hp : p.Prime) (hmp : m < p)
    (blocks : ∀ ℓ ∈ m.primeFactors, ∃ h d v : ℕ, 0 < h ∧ m ≤ ℓ ^ h ∧
      0 < v ∧ v ≤ ℓ ^ d ∧ ℓ ^ (d + h + m.factorization ℓ - 1) ∣ p + v) :
    f (m*p) = m := by
  apply (fixed_cofactor_iff hm hp hmp).mpr
  intro t ht hhalf
  have htm : t < m := by omega
  have hc := Nat.choose_ne_zero (Nat.mul_le_mul_right p htm.le)
  apply (Nat.factorization_le_iff_dvd (by omega : m ≠ 0) hc).mp
  intro ℓ
  by_cases hℓ : ℓ ∈ m.primeFactors
  · have hprime := (Nat.mem_primeFactors.mp hℓ).1
    obtain ⟨h, d, v, hh, hbound, hv, hvd, hblock⟩ := blocks ℓ hℓ
    exact (hprime.pow_dvd_iff_le_factorization hc).mp
      (block_forces_prime_power hprime hh hbound hv hvd hblock ht htm)
  · have hz : m.factorization ℓ = 0 := Finsupp.notMem_support_iff.mp hℓ
    simp [hz]

end Erdos700
