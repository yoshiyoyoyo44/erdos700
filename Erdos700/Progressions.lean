import Erdos700.ExponentDensity
import Mathlib.Algebra.GCDMonoid.Finset

namespace Erdos700

/-- Low digits in common preserve every carry present in the smaller row. -/
theorem choose_factorization_le_of_modEq {ℓ A t x y R : ℕ} (hℓ : ℓ.Prime) (ht : t ≤ A)
    (hR : Nat.log ℓ (A*x) < R) (hxy : x ≡ y [MOD ℓ^R]) :
    ((A*x).choose (t*x)).factorization ℓ ≤ ((A*y).choose (t*y)).factorization ℓ := by
  let b := max R (Nat.log ℓ (A*y)+1)
  have hb : Nat.log ℓ (A*y) < b := (Nat.lt_succ_self _).trans_le (le_max_right _ _)
  rw [Nat.factorization_choose hℓ (Nat.mul_le_mul_right x ht) hR,
    Nat.factorization_choose hℓ (Nat.mul_le_mul_right y ht) hb]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hiR, hcarry⟩ := Finset.mem_filter.mp hi
  obtain ⟨hi1, hiR⟩ := Finset.mem_Ico.mp hiR
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hi1, hiR.trans_le (le_max_left _ _)⟩, ?_⟩
  have hlow := hxy.of_dvd (pow_dvd_pow ℓ hiR.le)
  have hleft : (t*x) % ℓ^i = (t*y) % ℓ^i := hlow.mul_left t
  have hright : ((A-t)*x) % ℓ^i = ((A-t)*y) % ℓ^i := hlow.mul_left (A-t)
  rwa [← Nat.sub_mul, ← hleft, ← hright, Nat.sub_mul]

private theorem power_column_dvd {m q h u v t : ℕ} (hm : 0 < m) (hq : q.Prime) (huv : u ≤ v)
    (ht : t ≤ m*q^h) (hmod : ∀ ℓ ∈ m.primeFactors,
      q^u ≡ q^v [MOD ℓ^(Nat.log ℓ (m*q^(h+u))+1)]) :
    column (m*q^(h+u)) (t*q^u) ∣ column (m*q^(h+v)) (t*q^v) := by
  let A := m*q^h
  have row (s : ℕ) : m*q^(h+s) = A*q^s := by dsimp [A]; rw [pow_add, Nat.mul_assoc]
  have hn (s : ℕ) : m*q^(h+s) ≠ 0 := Nat.mul_ne_zero hm.ne' (pow_ne_zero _ hq.ne_zero)
  have hc (s : ℕ) : (m*q^(h+s)).choose (t*q^s) ≠ 0 := by
    rw [row]; exact Nat.choose_ne_zero (Nat.mul_le_mul_right _ ht)
  have hg (s : ℕ) : column (m*q^(h+s)) (t*q^s) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (hn s).bot_lt).ne'
  have hdiv : m*q^(h+u) ∣ m*q^(h+v) := Nat.mul_dvd_mul_left m (pow_dvd_pow _ (by omega))
  have hnle := (Nat.factorization_le_iff_dvd (hn u) (hn v)).mpr hdiv
  apply (Nat.factorization_le_iff_dvd (hg u) (hg v)).mp
  intro ℓ
  simp only [column, Nat.factorization_gcd (hn u) (hc u), Nat.factorization_gcd (hn v) (hc v), Finsupp.inf_apply]
  by_cases hqeq : ℓ = q
  · subst ℓ
    apply min_le_min (hnle _) (le_of_eq ?_)
    have hshift (s : ℕ) : ((m*q^(h+s)).choose (t*q^s)).factorization q = (A.choose t).factorization q := by
      rw [row, Nat.mul_comm A, Nat.mul_comm t]
      exact factorization_choose_shift hq s ht
    exact (hshift u).trans (hshift v).symm
  · by_cases hℓ : ℓ ∈ m.primeFactors
    · apply min_le_min (hnle _)
      rw [row u, row v]
      have hlow := hmod ℓ hℓ
      rw [row u] at hlow
      exact choose_factorization_le_of_modEq (Nat.mem_primeFactors.mp hℓ).1 ht (Nat.lt_succ_self _) hlow
    · have hnone : ℓ ∉ (m*q^(h+u)).primeFactors := by
        intro hh
        obtain ⟨hp, hl, _⟩ := Nat.mem_primeFactors.mp hh
        rcases hp.dvd_mul.mp hl with hd | hd
        · exact hℓ (Nat.mem_primeFactors.mpr ⟨hp, hd, hm.ne'⟩)
        · exact hqeq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hd))
      have hz : (m*q^(h+u)).factorization ℓ = 0 := Finsupp.notMem_support_iff.mp hnone
      simp [hz]

/-- A period given by the least common multiple of the local multiplicative orders. -/
noncomputable def equalityProgressionStep (m q e : ℕ) : ℕ :=
  m.primeFactors.lcm (fun ℓ => orderOf (q : ZMod (ℓ^(Nat.log ℓ (m*q^e)+1))))

private theorem period_spec {m q e : ℕ} (hq : q.Prime) (hqm : ¬ q ∣ m) :
    0 < equalityProgressionStep m q e ∧ ∀ ℓ ∈ m.primeFactors,
      q^(equalityProgressionStep m q e) ≡ 1 [MOD ℓ^(Nat.log ℓ (m*q^e)+1)] := by
  let M (ℓ : ℕ) := ℓ^(Nat.log ℓ (m*q^e)+1)
  let order (ℓ : ℕ) := orderOf (q : ZMod (M ℓ))
  have cast (ℓ k : ℕ) : (q : ZMod (M ℓ))^k = 1 ↔ q^k ≡ 1 [MOD M ℓ] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one]
  constructor
  · apply Nat.pos_of_ne_zero
    apply Finset.lcm_ne_zero_iff.mpr
    intro ℓ hℓ
    obtain ⟨hp, hdiv, _⟩ := Nat.mem_primeFactors.mp hℓ
    have hcop : ¬ℓ ∣ q := fun hd => hqm (((Nat.prime_dvd_prime_iff_eq hp hq).mp hd) ▸ hdiv)
    have hunit : q.Coprime (M ℓ) := (hp.coprime_iff_not_dvd.mpr hcop).symm.pow_right _
    have hord : order ℓ ∣ (M ℓ).totient := orderOf_dvd_of_pow_eq_one ((cast _ _).mpr
      (Nat.ModEq.pow_totient hunit))
    have hpos := Nat.totient_pos.mpr (pow_pos hp.pos (Nat.log ℓ (m*q^e)+1))
    change order ℓ ≠ 0
    intro hz
    rw [hz, zero_dvd_iff] at hord
    exact hpos.ne' hord
  · intro ℓ hℓ
    exact (cast ℓ _).mp (orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_lcm (f := order) hℓ))

/-- Every equality seed at or above the stable cutoff yields an infinite progression of equalities. -/
theorem equality_progression_of_seed {m q e : ℕ} (hm : 2 ≤ m) (hq : q.Prime) (hqm : ¬q ∣ m)
    (he : 0 < e) (hcut : Nat.log q (m-1) ≤ e) (hseed : f (m*q^e) = m) :
    0 < equalityProgressionStep m q e ∧ ∀ j : ℕ,
      f (m*q^(e+j*equalityProgressionStep m q e)) = m := by
  let h := Nat.log q (m-1)
  let u := e-h
  let T := equalityProgressionStep m q e
  obtain ⟨hT, hmod⟩ := period_spec (e := e) hq hqm
  have hu : h+u=e := Nat.add_sub_of_le hcut
  have hB : m ≤ q^(h+1) := by
    have hh : m-1 < q^(h+1) := Nat.lt_pow_succ_log_self hq.one_lt _
    omega
  have hbase := (power_candidate_criterion (h := h) (s := u) hm hq hqm (by omega) (Or.inl hB)).mp
    (by rwa [hu])
  refine ⟨hT, ?_⟩
  intro j
  let v := u+j*T
  have huv : u ≤ v := Nat.le_add_right _ _
  have hv : h+v=e+j*T := by dsimp [v]; omega
  change f (m*q^(e+j*T))=m
  rw [← hv]
  apply (power_candidate_criterion hm hq hqm (by omega) (Or.inl hB)).mpr
  intro t ht hhalf
  have hdiv : column (m*q^(h+u)) (t*q^u) ∣ column (m*q^(h+v)) (t*q^v) := by
    apply power_column_dvd (by omega) hq huv (by omega)
    intro ℓ hℓ
    rw [hu]
    have hh := (hmod ℓ hℓ).pow j
    simpa only [v, pow_add, Nat.mul_comm j T, pow_mul, one_pow, mul_one] using (hh.mul_left (q^u)).symm
  exact (hbase t ht hhalf).trans (Nat.le_of_dvd
    (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos (by omega) (pow_pos hq.pos _))) hdiv)

/-- Positive density of an arithmetic residue class supplies equality seeds above any threshold. -/
private theorem exists_equality_seed_in_class {m q D : ℕ} (hm : 2 ≤ m) (hq : q.Prime)
    (hqm : ¬q ∣ m) (hD : 0 < D) (r lower : ℕ) :
    ∃ e : ℕ, lower ≤ e ∧ 0 < e ∧ e ≡ r [MOD D] ∧ f (m*q^e)=m := by
  have hDr : 0 < (D:ℝ) := Nat.cast_pos.mpr hD
  obtain ⟨X₀,hX₀⟩ := Filter.eventually_atTop.mp
    ((exceptional_exponent_density_zero hm hq hqm).eventually_lt_const
      (by positivity : (0:ℝ) < 1 / (2*(D:ℝ))))
  let b := r+(lower+1)*D
  have hb : lower < b := by
    have hh : (lower+1)*1 ≤ (lower+1)*D := Nat.mul_le_mul_left _ hD
    simp only [Nat.mul_one] at hh
    dsimp [b]
    omega
  let N := max b X₀ + 1
  let E := b+N*D
  have hN : 0 < N := Nat.zero_lt_succ _
  have hbN : b ≤ N := (le_max_left b X₀).trans (Nat.le_succ _)
  have hXN : X₀ ≤ N := (le_max_right b X₀).trans (Nat.le_succ _)
  have hND : N ≤ N*D := by simpa using Nat.mul_le_mul_left N hD
  have hXE : X₀ ≤ E := by dsimp [E]; omega
  have hE : 0 < (E:ℝ) := Nat.cast_pos.mpr (by dsimp [E]; omega)
  by_contra! hnone
  have hcount : N ≤ exceptionalExponentCount m q E := by
    change N ≤ ((Finset.range (E+1)).filter (fun e => 0<e ∧ f (m*q^e)<m)).card
    rw [← Finset.card_range N]
    apply Finset.card_le_card_of_injOn (fun j : ℕ => b+j*D)
    · intro j hj
      have hjN := Finset.mem_range.mp hj
      have hjle := Nat.mul_le_mul_right D hjN.le
      have hpos : 0 < b+j*D := by omega
      have hclass : b+j*D ≡ r [MOD D] := by simp [b, Nat.ModEq, Nat.add_mod]
      have hne := hnone (b+j*D) (by omega) hpos hclass
      have hlow := power_cofactor_le hm hq hqm hpos
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [E]; omega), hpos, lt_of_le_of_ne hlow hne⟩
    · intro i _ j _ hij
      exact Nat.eq_of_mul_eq_mul_right hD (Nat.add_left_cancel hij)
  have hbound : E ≤ (2*D)*N := by dsimp [E]; nlinarith
  have hsmall := hX₀ E hXE
  change (exceptionalExponentCount m q E : ℝ) / E < 1 / (2*(D:ℝ)) at hsmall
  rw [div_lt_div_iff₀ hE (by positivity)] at hsmall
  have hcr : (N:ℝ) ≤ exceptionalExponentCount m q E := by exact_mod_cast hcount
  have hbr : (E:ℝ) ≤ (2*(D:ℝ))*N := by exact_mod_cast hbound
  nlinarith [mul_le_mul_of_nonneg_right hcr (by positivity : 0 ≤ 2*(D:ℝ))]

/-- Every prescribed residue class contains an infinite progression of equality exponents.
The starting point can be chosen beyond any prescribed lower bound. -/
theorem equality_progression_in_every_class {m q D : ℕ} (hm : 2 ≤ m) (hq : q.Prime)
    (hqm : ¬q ∣ m) (hD : 0 < D) (r lower : ℕ) :
    ∃ e T : ℕ, lower ≤ e ∧ 0 < e ∧ 0 < T ∧ D ∣ T ∧ e ≡ r [MOD D] ∧
      ∀ j : ℕ, f (m*q^(e+j*T)) = m := by
  obtain ⟨e, he, he0, hclass, hseed⟩ :=
    exists_equality_seed_in_class hm hq hqm hD r (max lower (Nat.log q (m-1)))
  obtain ⟨hT, hprog⟩ := equality_progression_of_seed hm hq hqm he0 ((le_max_right _ _).trans he) hseed
  refine ⟨e, D*equalityProgressionStep m q e, (le_max_left _ _).trans he, he0,
    Nat.mul_pos hD hT, dvd_mul_right D _, hclass, ?_⟩
  intro j
  simpa only [Nat.mul_assoc] using hprog (j*D)

/-- A concrete progression from the manuscript, checked at every index. -/
theorem four_three_progression (j : ℕ) : f (4*3^(2+16*j)) = 4 := by
  have hseed : f (4*3^2) = 4 := by
    unfold f column
    simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide +kernel
  have hstep : equalityProgressionStep 4 3 2 ∣ 16 := by
    apply Finset.lcm_dvd
    intro ℓ hℓ
    rw [show (4:ℕ).primeFactors = {2} by decide +kernel, Finset.mem_singleton] at hℓ
    subst ℓ
    apply orderOf_dvd_of_pow_eq_one
    change (3 : ZMod 64)^16 = 1
    decide +kernel
  obtain ⟨a,ha⟩ := hstep
  have hprog := (equality_progression_of_seed (q := 3) (e := 2) (by decide : 2 ≤ 4)
    Nat.prime_three (by decide) (by decide) (by decide) hseed).2 (j*a)
  rwa [show 16*j=(j*a)*equalityProgressionStep 4 3 2 by rw [ha]; ring]

end Erdos700
