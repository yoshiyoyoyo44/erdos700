import Erdos700.Sparse

namespace Erdos700

theorem power_cofactor_le {m q e : ℕ} (hm : 2 ≤ m) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (he : 0 < e) : f (m*q^e) ≤ m := by
  have hz : 1 < q^e := one_lt_pow₀ hq.one_lt he.ne'
  have hhalf : q^e ≤ m*q^e/2 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right (q^e) hm
  have hc := column_primePowerFactor (e := e) hq (by omega : 0 < m) hqm
  rw [Nat.mul_comm (q^e) m] at hc
  exact (f_le_column hz hhalf).trans_eq hc

/-- Set e=h+s. If q^(h+1) ≥ m, every column improving on m is a multiple of q^s.
For s=0 the test covers the whole range and no size hypothesis is needed. -/
theorem power_candidate_criterion {m q h s : ℕ} (hm : 2 ≤ m) (hq : q.Prime)
    (hqm : ¬ q ∣ m) (he : 0 < h+s) (hcut : m ≤ q^(h+1) ∨ s = 0) :
    f (m*q^(h+s)) = m ↔ ∀ t, 0 < t → 2*t ≤ m*q^h →
      m ≤ column (m*q^(h+s)) (t*q^s) := by
  have hz : 0 < q^s := pow_pos hq.pos _
  have hpow : 1 < q^(h+s) := one_lt_pow₀ hq.one_lt he.ne'
  have hn : 4 ≤ m*q^(h+s) := by nlinarith
  have hrow : (m*q^h)*q^s = m*q^(h+s) := by rw [pow_add, Nat.mul_assoc]
  constructor
  · intro hf t ht hhalf
    have hkpos := Nat.mul_pos ht hz
    have hk : (t*q^s)*2 ≤ m*q^(h+s) := by
      rw [← hrow]
      simpa [mul_assoc, mul_comm, mul_left_comm] using Nat.mul_le_mul_right (q^s) hhalf
    by_cases hsmall : t*q^s = 1
    · simp only [hsmall, column, Nat.choose_one_right, Nat.gcd_self]
      nlinarith
    · exact hf.ge.trans (f_le_column (by omega) ((Nat.le_div_iff_mul_le (by decide : 0<2)).mpr hk))
  · intro hall
    apply le_antisymm (power_cofactor_le hm hq hqm he)
    apply (le_f_iff hn).mpr
    intro k hk hhalf
    by_contra! hg
    have hzdiv : q^s ∣ k := by
      rcases hcut with hcut | rfl
      · apply pow_dvd_index_of_small_column (h := h) hq (by omega) _ (hg.trans_le hcut)
        simp [Nat.add_comm s h]
      · simp
    obtain ⟨t, hkt⟩ := hzdiv
    have htk : k = t*q^s := hkt.trans (Nat.mul_comm _ _)
    have ht : 0 < t := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at htk; omega
    have hk' := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hhalf
    rw [htk, ← hrow] at hk'
    have hlim : 2*t ≤ m*q^h := Nat.le_of_mul_le_mul_right
      (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hk') hz
    exact hg.not_ge (htk ▸ hall t ht hlim)

/-- The candidate interval has at most m(m-1)/2 positive indices, even at small exponents. -/
theorem bounded_power_candidates {m q e : ℕ} (hm : 2 ≤ m) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (he : 0 < e) :
    let h := min e (Nat.log q (m-1))
    m*q^h ≤ m*(m-1) ∧
      (f (m*q^e) = m ↔ ∀ t, 0 < t → 2*t ≤ m*q^h → m ≤ column (m*q^e) (t*q^(e-h))) := by
  let h := min e (Nat.log q (m-1))
  have hh : h ≤ e := min_le_left _ _
  have hA := (Nat.pow_le_pow_right hq.pos (min_le_right e (Nat.log q (m-1)))).trans
    (Nat.pow_log_le_self q (by omega : m-1 ≠ 0))
  refine ⟨Nat.mul_le_mul_left m hA, ?_⟩
  have hcut : m ≤ q^(h+1) ∨ e-h = 0 := by
    by_cases hsmall : e ≤ Nat.log q (m-1)
    · exact Or.inr (by simp [h, min_eq_left hsmall])
    · have hmax : m-1 < q^(Nat.log q (m-1) + 1) := Nat.lt_pow_succ_log_self hq.one_lt (m-1)
      rw [show h = Nat.log q (m-1) from min_eq_right (by omega)]
      exact Or.inl (by omega)
  have hsum : h + (e-h) = e := by omega
  simpa only [hsum] using power_candidate_criterion (h := h) (s := e-h) hm hq hqm (by omega) hcut

/-- For large exponents, a maximal block in every relevant prime base certifies equality. -/
theorem power_equality_of_digits {m q s : ℕ} (hm : 2 ≤ m) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (he : 0 < Nat.log q (m-1) + s)
    (hdigits : ∀ ℓ ∈ m.primeFactors, ∃ i : ℕ,
      q^s / (blockBase (m*(m-1)) ℓ)^i % blockBase (m*(m-1)) ℓ =
      blockBase (m*(m-1)) ℓ - 1) :
    f (m*q^(Nat.log q (m-1) + s)) = m := by
  let h := Nat.log q (m-1)
  let A := m*q^h
  let Y := m*(m-1)
  have hY : 2 ≤ Y := by simpa only [Nat.mul_one] using Nat.mul_le_mul hm (by omega : 1 ≤ m-1)
  have hA : A ≤ Y := Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ (by omega : m-1 ≠ 0))
  have hcut : m-1 < q^(Nat.log q (m-1) + 1) := Nat.lt_pow_succ_log_self hq.one_lt (m-1)
  apply (power_candidate_criterion (h := h) (s := s) hm hq hqm he (Or.inl (by dsimp [h]; omega))).mpr
  intro t ht hhalf
  have htA : t < A := by dsimp [A]; omega
  have hrow : m*q^(h+s) = A*q^s := by dsimp [A]; rw [pow_add, Nat.mul_assoc]
  have hn : 0 < m*q^(h+s) := Nat.mul_pos (by omega) (pow_pos hq.pos _)
  apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hn)
  apply Nat.dvd_gcd (dvd_mul_right m _)
  rw [hrow]
  have hc := Nat.choose_ne_zero (Nat.mul_le_mul_right (q^s) htA.le)
  apply (Nat.factorization_le_iff_dvd (by omega : m ≠ 0) hc).mp
  intro ℓ
  by_cases hℓ : ℓ ∈ m.primeFactors
  · obtain ⟨hprime, hdiv, hm0⟩ := Nat.mem_primeFactors.mp hℓ
    have hmY : m ∣ Y := dvd_mul_right m _
    have hℓY := Nat.mem_primeFactors.mpr ⟨hprime, hdiv.trans hmY, (by omega : Y ≠ 0)⟩
    obtain ⟨i, hi⟩ := hdigits ℓ hℓ
    obtain ⟨H, d, v, hH, hbound, hv, hvd, hblock⟩ := max_digit_witness hY hℓY hi
    have hforce := block_forces_prime_power hprime hH (hA.trans hbound) hv hvd hblock ht htA
    exact ((Nat.factorization_le_iff_dvd hm0 (by omega : Y ≠ 0)).mpr hmY ℓ).trans
      ((hprime.pow_dvd_iff_le_factorization hc).mp hforce)
  · have hz : m.factorization ℓ = 0 := Finsupp.notMem_support_iff.mp hℓ
    simp [hz]

/-- The exact gcd at a candidate column: its q-adic contribution is read from a bounded row. -/
theorem power_candidate_gcd {m q h s t : ℕ} (hm : 0 < m) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (ht : t ≤ m*q^h) :
    column (m*q^(h+s)) (t*q^s) =
      q ^ min (h+s) (((m*q^h).choose t).factorization q) *
      ∏ ℓ ∈ m.primeFactors, ℓ ^ min (m.factorization ℓ)
        (((m*q^(h+s)).choose (t*q^s)).factorization ℓ) := by
  let n := m*q^(h+s)
  let k := t*q^s
  let g := column n k
  have hn : n ≠ 0 := Nat.mul_ne_zero hm.ne' (pow_ne_zero _ hq.ne_zero)
  have hrow : n = (m*q^h)*q^s := by dsimp [n]; rw [pow_add, Nat.mul_assoc]
  have hc : n.choose k ≠ 0 := by rw [hrow]; exact Nat.choose_ne_zero (Nat.mul_le_mul_right _ ht)
  have hg : g ≠ 0 := (Nat.gcd_pos_of_pos_left _ hn.bot_lt).ne'
  have hqmem : q ∉ m.primeFactors := fun h => hqm (Nat.mem_primeFactors.mp h).2.1
  have hsub : g.primeFactors ⊆ insert q m.primeFactors := by
    intro ℓ hℓ
    obtain ⟨hp, hdiv, _⟩ := Nat.mem_primeFactors.mp hℓ
    have hd : ℓ ∣ m*q^(h+s) := hdiv.trans (Nat.gcd_dvd_left n (n.choose k))
    rcases hp.dvd_mul.mp hd with hm' | hq'
    · exact Finset.mem_insert_of_mem (Nat.mem_primeFactors.mpr ⟨hp, hm', hm.ne'⟩)
    · exact Finset.mem_insert.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hq')))
  have hval (ℓ : ℕ) : g.factorization ℓ = min (n.factorization ℓ) ((n.choose k).factorization ℓ) := by
    simp only [g, column, Nat.factorization_gcd hn hc, Finsupp.inf_apply]
  have hqv : g.factorization q = min (h+s) (((m*q^h).choose t).factorization q) := by
    rw [hval, show n.factorization q = h+s by simp only [n, Nat.factorization_mul hm.ne' (pow_ne_zero _ hq.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqm, Nat.factorization_pow_self hq, zero_add]]
    rw [hrow, Nat.mul_comm (m*q^h), show k=q^s*t from Nat.mul_comm _ _, factorization_choose_shift hq s ht]
  calc
    g = ∏ ℓ ∈ g.primeFactors, ℓ^g.factorization ℓ := Nat.prod_primeFactors_pow_factorization hg
    _ = ∏ ℓ ∈ insert q m.primeFactors, ℓ^g.factorization ℓ := Finset.prod_subset hsub
      (fun ℓ _ hnot => by rw [show g.factorization ℓ = 0 from Finsupp.notMem_support_iff.mp hnot, pow_zero])
    _ = _ := by
      rw [Finset.prod_insert hqmem, hqv]
      congr 1
      apply Finset.prod_congr rfl
      intro ℓ hℓ
      obtain ⟨hp,hd,_⟩ := Nat.mem_primeFactors.mp hℓ
      have hnq : ¬ℓ ∣ q^(h+s) := fun hyp => hqm (((Nat.prime_dvd_prime_iff_eq hp hq).mp
        (hp.dvd_of_dvd_pow hyp)) ▸ hd)
      rw [hval, show n.factorization ℓ = m.factorization ℓ by simp only [n,
        Nat.factorization_mul hm.ne' (pow_ne_zero _ hq.ne_zero), Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnq, add_zero]]

end Erdos700
