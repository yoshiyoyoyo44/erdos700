import Erdos700.Arithmetic
import Erdos700.Splits

namespace Erdos700

/-- The intersection of the subset-sum sets for the exact prime-power factors of d. -/
def commonSums (n d : ℕ) : Set ℕ :=
  ⋂ p ∈ d.primeFactors, splitSums p n (n.factorization p - d.factorization p)

private theorem le_of_mem_splitSums {p n k budget : ℕ} (h : k ∈ splitSums p n budget) :
    k ≤ n := by
  obtain ⟨_, _, a, b, hr, ha⟩ := h
  have hv := hr.value_eq
  simp only [value_add, value_canonical, ha] at hv
  omega

/-- The common subset sums pick out precisely the columns with d dividing the gcd cofactor. -/
theorem mem_commonSums_iff {n d k : ℕ} (hn : n ≠ 0) (hd : d ∣ n) (hd1 : 1 < d) :
    k ∈ commonSums n d ↔ k ≤ n ∧ d ∣ n / column n k := by
  have hd0 : d ≠ 0 := by omega
  have hdf := (Nat.factorization_le_iff_dvd hd0 hn).mpr hd
  have hg := Nat.gcd_dvd_left n (n.choose k)
  have hquot : n / column n k ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn.bot_lt hg)
    (Nat.gcd_pos_of_pos_left _ hn.bot_lt)).ne'
  have hval (hk : k ≤ n) (p : ℕ) : (n / column n k).factorization p =
      n.factorization p - min (n.factorization p) ((n.choose k).factorization p) := by
    simp only [column, Nat.factorization_div hg, Nat.factorization_gcd hn (Nat.choose_ne_zero hk),
      Finsupp.tsub_apply, Finsupp.inf_apply]
  simp only [commonSums, Set.mem_iInter]
  constructor
  · intro h
    have hmin := Nat.minFac_prime (by omega : d ≠ 1)
    have hk := le_of_mem_splitSums (h d.minFac (Nat.mem_primeFactors.mpr ⟨hmin, Nat.minFac_dvd d, hd0⟩))
    refine ⟨hk, (Nat.factorization_le_iff_dvd hd0 hquot).mp (fun p => ?_)⟩
    by_cases hp : p ∈ d.primeFactors
    · have hv := (mem_splitSums_iff (Nat.mem_primeFactors.mp hp).1 hk).mp (h p hp)
      have hle := hdf p
      rw [hval hk]
      omega
    · have he : d.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
      simp [he]
  · rintro ⟨hk, hdiv⟩ p hp
    obtain ⟨hprime, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    apply (mem_splitSums_iff hprime hk).mpr
    have hle := (Nat.factorization_le_iff_dvd hd0 hquot).mpr hdiv p
    have hpos := hprime.factorization_pos_of_dvd hd0 hpd
    rw [hval hk] at hle
    omega

/-- Theorem 1, original version of Erdős and Szekeres (largest prime power). -/
theorem general_criterion {n : ℕ} (hmix : 1 < n.primeFactors.card) :
    f n = n / maxPrimePower n ↔ ∀ d, Critical n d → commonSums n d = {0, n} := by
  obtain ⟨hQ, hdQ, hm, _⟩ := maxPrimePower_spec hmix
  have hn : n ≠ 0 := by rintro rfl; simp at hmix
  rw [f_eq_iff_no_critical_column hmix]
  constructor
  · intro h d hd
    have h1 : 1 < d := lt_trans (by omega) hd.2.1
    ext k
    rw [mem_commonSums_iff hn hd.1 h1]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hk, hdiv⟩
      by_contra! hi
      exact h d hd k (by omega) (by omega) hdiv
    · rintro (rfl | rfl) <;> simp [column, hd.1]
  · intro h d hd k hk hkn hdiv
    have h1 : 1 < d := lt_trans (by omega) hd.2.1
    have hmemb := (mem_commonSums_iff hn hd.1 h1).mpr ⟨hkn.le, hdiv⟩
    rw [h d hd] at hmemb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmemb
    omega

/-- Theorem 1 for the formulation using the largest prime factor. -/
theorem largestPrime_criterion {n : ℕ} (hmix : 1 < n.primeFactors.card) :
    f n = n / maxPrime n ↔ maxPrime n = maxPrimePower n ∧
      ∀ d, Critical n d → commonSums n d = {0, n} := by
  obtain ⟨p, hpn, he⟩ := n.primeFactors.exists_mem_eq_sup
    (Finset.card_pos.mp (by omega)) id
  change maxPrime n = p at he
  obtain ⟨hp, hd, hn⟩ := Nat.mem_primeFactors.mp hpn
  have hpQ : maxPrime n ≤ maxPrimePower n := by
    rw [he]
    exact (Nat.le_self_pow (hp.factorization_pos_of_dvd hn hd).ne' p).trans
      (Finset.le_sup (f := fun q => q ^ n.factorization q) hpn)
  obtain ⟨hQ, hdQ, hm, _⟩ := maxPrimePower_spec hmix
  constructor
  · intro hf
    have hP : maxPrime n ∣ n := he ▸ hd
    have hmulP := Nat.div_mul_cancel hP
    have hmulQ := Nat.div_mul_cancel hdQ
    have hle := f_le_maxPrimePower_bound hmix
    rw [hf] at hle
    have hPQ : maxPrime n = maxPrimePower n := by
      by_contra hne
      have hlt := lt_of_le_of_ne hpQ hne
      nlinarith [Nat.mul_lt_mul_of_pos_left hlt (by omega : 0 < n / maxPrimePower n),
        Nat.mul_le_mul_right (maxPrime n) hle]
    exact ⟨hPQ, (general_criterion hmix).mp (hPQ ▸ hf)⟩
  · rintro ⟨hPQ, h⟩
    rw [hPQ]
    exact (general_criterion hmix).mpr h

end Erdos700
