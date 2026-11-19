import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic.Linarith

namespace Erdos700

/-- The gcd at the k-th column of the n-th row of Pascal's triangle. -/
def column (n k : ℕ) := Nat.gcd n (n.choose k)

/-- The minimum in the problem. The fallback for an empty interval is irrelevant for n ≥ 4. -/
def f (n : ℕ) : ℕ :=
  if h : 2 ≤ n / 2 then
    (Finset.Icc 2 (n / 2)).inf' (Finset.nonempty_Icc.mpr h) (column n)
  else n

theorem le_f_iff {n a : ℕ} (hn : 4 ≤ n) :
    a ≤ f n ↔ ∀ k, 2 ≤ k → k ≤ n / 2 → a ≤ column n k := by
  have h : 2 ≤ n / 2 := by omega
  simp [f, h, Finset.le_inf'_iff]

theorem f_le_column {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n / 2) :
    f n ≤ column n k :=
  (le_f_iff (by omega)).mp le_rfl k hk hkn

def maxPrimePower (n : ℕ) : ℕ := n.primeFactors.sup (fun p => p ^ n.factorization p)

def maxPrime (n : ℕ) : ℕ := n.primeFactors.sup id

private theorem cofactor_dvd_choose {a m : ℕ} (ha : 0 < a) (hm : 0 < m) :
    m ∣ (a * m).choose a := by
  have h := Nat.add_one_mul_choose_eq (a * m - 1) (a - 1)
  rw [Nat.sub_add_cancel (Nat.mul_pos ha hm), Nat.sub_add_cancel ha] at h
  refine ⟨(a * m - 1).choose (a - 1), Nat.eq_of_mul_eq_mul_left ha ?_⟩
  simpa only [mul_assoc, mul_comm ((a * m).choose a) a] using h.symm

/-- At an exact prime-power factor, the column gcd is its complementary factor. -/
theorem column_primePowerFactor {p e m : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : ¬ p ∣ m) :
    column (p ^ e * m) (p ^ e) = m := by
  letI : Fact p.Prime := ⟨hp⟩
  have hmod : (p ^ e * m).choose (p ^ e) ≡ m [MOD p] := by
    simpa using Choose.choose_pow_mul_pow_mul_modEq_choose_nat (p := p) (k := e) (a := m) (b := 1)
  have hc : ¬p ∣ (p ^ e * m).choose (p ^ e) := fun hd =>
    hpm (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hd)))
  exact Nat.gcd_mul_of_coprime_of_dvd ((hp.coprime_iff_not_dvd.mpr hc).pow_left e)
    (cofactor_dvd_choose (pow_pos hp.pos _) hm)

theorem maxPrimePower_spec {n : ℕ} (hmix : 1 < n.primeFactors.card) :
    2 ≤ maxPrimePower n ∧ maxPrimePower n ∣ n ∧ 2 ≤ n / maxPrimePower n ∧
      column n (maxPrimePower n) = n / maxPrimePower n := by
  obtain ⟨p, hpn, hQ⟩ := n.primeFactors.exists_mem_eq_sup
    (Finset.card_pos.mp (by omega)) (fun p => p ^ n.factorization p)
  change maxPrimePower n = _ at hQ
  obtain ⟨hp, hd, hn⟩ := Nat.mem_primeFactors.mp hpn
  have he := hp.factorization_pos_of_dvd hn hd
  have hpow : 2 ≤ p ^ n.factorization p :=
    hp.two_le.trans (Nat.le_self_pow he.ne' p)
  have hdiv := Nat.ordProj_dvd n p
  change p ^ n.factorization p ∣ n at hdiv
  have hmul := Nat.mul_div_cancel' hdiv
  have hm : 0 < n / p ^ n.factorization p :=
    Nat.div_pos (Nat.le_of_dvd hn.bot_lt hdiv) (pow_pos hp.pos _)
  have hne : n / p ^ n.factorization p ≠ 1 := by
    intro h
    have hnp : n = p ^ n.factorization p := by simpa [h] using hmul.symm
    have hcard := congrArg (fun x : ℕ => x.primeFactors.card) hnp
    rw [Nat.primeFactors_prime_pow he.ne' hp, Finset.card_singleton] at hcard
    omega
  rw [hQ]
  refine ⟨hpow, hdiv, by omega, ?_⟩
  simpa only [hmul] using
    (column_primePowerFactor (e := n.factorization p) hp hm (Nat.not_dvd_ordCompl hp hn))

theorem f_le_maxPrimePower_bound {n : ℕ} (hmix : 1 < n.primeFactors.card) :
    f n ≤ n / maxPrimePower n := by
  obtain ⟨hQ, hd, hm, hc⟩ := maxPrimePower_spec hmix
  apply hc ▸ f_le_column hQ
  have hmul := Nat.div_mul_cancel hd
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  nlinarith

/-- The divisors just above the largest prime power in the paper. -/
def Critical (n d : ℕ) : Prop :=
  d ∣ n ∧ maxPrimePower n < d ∧ d / d.minFac ≤ maxPrimePower n

private theorem exists_critical_dvd {n x : ℕ} (hpos : 1 ≤ maxPrimePower n)
    (hx : x ∣ n) (hQ : maxPrimePower n < x) :
    ∃ d, Critical n d ∧ d ∣ x := by
  classical
  have hex : ∃ d, maxPrimePower n < d ∧ d ∣ x := ⟨x, hQ, dvd_rfl⟩
  let d := Nat.find hex
  obtain ⟨hlt, hd⟩ := Nat.find_spec hex
  change maxPrimePower n < d at hlt
  change d ∣ x at hd
  refine ⟨d, ⟨hd.trans hx, hlt, ?_⟩, hd⟩
  by_contra! h
  have hne : d ≠ 1 := by omega
  have hsmall : d / d.minFac < d :=
    Nat.div_lt_self (by omega) (Nat.minFac_prime hne).one_lt
  exact Nat.find_min hex hsmall ⟨h, (Nat.div_dvd_of_dvd (Nat.minFac_dvd d)).trans hd⟩

/-- Equality iff no admissible column has a complementary divisor above the bound. -/
theorem f_eq_iff_no_critical_column {n : ℕ} (hmix : 1 < n.primeFactors.card) :
    f n = n / maxPrimePower n ↔
      ∀ d, Critical n d → ∀ k, 0 < k → k < n → ¬d ∣ n / column n k := by
  obtain ⟨hQ, hQd, hm, _⟩ := maxPrimePower_spec hmix
  have hnQ := Nat.div_mul_cancel hQd
  have hn : 4 ≤ n := by nlinarith
  have column_iff (k : ℕ) : n / maxPrimePower n ≤ column n k ↔ n / column n k ≤ maxPrimePower n := by
    have hd := Nat.gcd_dvd_left n (n.choose k)
    have hg : 0 < column n k := Nat.gcd_pos_of_pos_left _ (by omega)
    have hng := Nat.div_mul_cancel hd
    change n / column n k * column n k = n at hng
    constructor
    · intro h
      by_contra! hx
      nlinarith [Nat.mul_lt_mul_of_pos_right hx hg, Nat.mul_le_mul_right (maxPrimePower n) h]
    · intro h
      by_contra! hx
      nlinarith [Nat.mul_lt_mul_of_pos_right hx (by omega : 0 < maxPrimePower n),
        Nat.mul_le_mul_right (column n k) h]
  constructor
  · intro he d hcrit k hk hkn hd
    let i := min k (n - k)
    have hi : 0 < i := by dsimp [i]; omega
    have hi2 : i ≤ n / 2 := by dsimp [i]; omega
    have hc : column n i = column n k := by
      rcases le_total k (n - k) with h | h
      · simp [i, min_eq_left h]
      · simp [i, min_eq_right h, column, Nat.choose_symm hkn.le]
    have hb : n / column n k ≤ maxPrimePower n := by
      by_cases h1 : i = 1
      · rw [← hc, h1]; simp [column, Nat.div_self (by omega : 0 < n)]; omega
      · apply (column_iff k).mp
        rw [← he, ← hc]
        exact f_le_column (by omega) hi2
    have hx : 0 < n / column n k :=
      Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _))
        (Nat.gcd_pos_of_pos_left _ (by omega))
    exact (not_lt_of_ge ((Nat.le_of_dvd hx hd).trans hb)) hcrit.2.1
  · intro h
    apply le_antisymm (f_le_maxPrimePower_bound hmix)
    apply (le_f_iff hn).mpr
    intro k hk hkn
    apply (column_iff k).mpr
    by_contra! hx
    obtain ⟨d, hd, hdx⟩ := exists_critical_dvd (by omega : 1 ≤ maxPrimePower n)
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n (n.choose k))) hx
    exact h d hd k (by omega) (by omega) hdx

end Erdos700
