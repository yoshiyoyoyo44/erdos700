import Erdos700.Sparse
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Chebyshev

namespace Erdos700

private noncomputable def digitExponent (B : ℕ) : ℝ := Real.logb B ((B-1 : ℕ) : ℝ)

private theorem digitExponent_lt_one {B : ℕ} (hB : 1 < B) : digitExponent B < 1 := by
  have hb : (1 : ℝ) < B := by exact_mod_cast hB
  have ha : (0 : ℝ) < ((B-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < B-1)
  have hlt : ((B-1 : ℕ) : ℝ) < B := by exact_mod_cast (by omega : B-1 < B)
  simpa [digitExponent, Real.logb_self_eq_one hb]
    using Real.logb_lt_logb hb ha hlt

private theorem digit_count_le_rpow {B X : ℕ} (hB : 1 < B) (hX : 1 ≤ X) :
    (((B-1)^(Nat.log B X + 1) : ℕ) : ℝ) ≤ ((B-1 : ℕ) : ℝ) * (X:ℝ)^(digitExponent B) := by
  have hb : (1 : ℝ) < B := by exact_mod_cast hB
  have hb0 : (0 : ℝ) < B := by linarith
  have ha : (1 : ℝ) ≤ ((B-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ B-1)
  have ht : 0 ≤ digitExponent B := Real.logb_nonneg hb ha
  have hpow : (B:ℝ) ^ digitExponent B = ((B-1 : ℕ) : ℝ) :=
    Real.rpow_logb hb0 hb.ne' (by linarith)
  have hle : (B:ℝ)^(Nat.log B X) ≤ X := by
    exact_mod_cast Nat.pow_log_le_self B (by omega : X ≠ 0)
  rw [Nat.cast_pow, pow_succ', mul_le_mul_iff_right₀ (by linarith : (0 : ℝ) < ((B-1 : ℕ) : ℝ))]
  calc
    _ = ((B:ℝ) ^ digitExponent B)^(Nat.log B X) := by rw [hpow]
    _ = ((B:ℝ)^(Nat.log B X))^(digitExponent B) := Real.rpow_pow_comm hb0.le _ _
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hle ht

/-- For a fixed cofactor there is a power saving over counting all integers up to X. -/
theorem exceptional_prime_power_saving {m : ℕ} (hm : 2 ≤ m) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      (exceptionalPrimeCount m X : ℝ) ≤ C * (X:ℝ) ^ (1-δ) := by
  let θ (ℓ : ℕ) := digitExponent (blockBase m ℓ)
  have hs : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  let t := m.primeFactors.sup' hs θ
  have ht : t < 1 := (Finset.sup'_lt_iff hs).mpr
    (fun ℓ hℓ => digitExponent_lt_one (blockBase_gt_one hm hℓ))
  let weight (ℓ : ℕ) : ℝ := ((blockBase m ℓ - 1 : ℕ) : ℝ)
  let C := ∑ ℓ ∈ m.primeFactors, weight ℓ
  have hC : 0 < C := Finset.sum_pos
    (fun ℓ hℓ => by
      dsimp [weight]
      exact_mod_cast Nat.sub_pos_of_lt (blockBase_gt_one hm hℓ)) hs
  refine ⟨1-t, C, by linarith, hC, ?_⟩
  intro X hX
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hcount := exceptional_prime_count hm X
  calc
    (exceptionalPrimeCount m X : ℝ) ≤ ∑ ℓ ∈ m.primeFactors,
        (((blockBase m ℓ - 1)^(Nat.log (blockBase m ℓ) X + 1) : ℕ) : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ ℓ ∈ m.primeFactors, weight ℓ * (X:ℝ)^t := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      apply (digit_count_le_rpow (blockBase_gt_one hm hℓ) hX).trans
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (Finset.le_sup' θ hℓ))
        (Nat.cast_nonneg _)
    _ = C * (X:ℝ)^(1-(1-t)) := by rw [sub_sub_cancel, Finset.sum_mul]

private theorem primeCounting_lower {X : ℕ} (hX : 32 ≤ X) :
    (X:ℝ) ≤ 8 * (Nat.primeCounting X : ℝ) * Real.log X := by
  have hx : (32 : ℝ) ≤ X := by exact_mod_cast hX
  have h2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ)⁻¹)
    rw [Real.log_inv] at h
    linarith
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < ((X:ℝ)+1)/4)
  rw [Real.log_div (by positivity) (by norm_num)] at hlog
  have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
  have hψ := Chebyshev.psi_ge X
  have hπ := Chebyshev.psi_le_primeCounting_mul_log X
  nlinarith [mul_nonneg (Nat.cast_nonneg X : (0:ℝ) ≤ X) (sub_nonneg.mpr h2)]

open Filter Topology in
/-- The exceptional primes have relative natural density zero among all primes. -/
theorem exceptional_prime_density_zero {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun X : ℕ => (exceptionalPrimeCount m X : ℝ) / Nat.primeCounting X)
      atTop (𝓝 0) := by
  obtain ⟨δ, C, hδ, hC, hbound⟩ := exceptional_prime_power_saving hm
  have hlim : Tendsto (fun X : ℕ => Real.log (X:ℝ) / (X:ℝ)^δ) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall (fun X => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    (g := fun X : ℕ => (8*C) * (Real.log (X:ℝ) / (X:ℝ)^δ))
  · filter_upwards [eventually_ge_atTop (32:ℕ)] with X hX
    have hx : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    have hpi := primeCounting_lower hX
    have hpos : 0 < (Nat.primeCounting X : ℝ) := by
      by_contra! h
      have hz := le_antisymm h (Nat.cast_nonneg _)
      rw [hz, mul_zero, zero_mul] at hpi
      linarith
    rw [div_le_iff₀ hpos]
    have hup := hbound X (by omega)
    rw [Real.rpow_sub hx, Real.rpow_one] at hup
    calc
      _ ≤ C * ((X:ℝ)/(X:ℝ)^δ) := hup
      _ ≤ C * ((8 * (Nat.primeCounting X : ℝ) * Real.log X) / (X:ℝ)^δ) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpi (Real.rpow_nonneg hx.le _)) hC.le
      _ = _ := by ring
  · simpa using hlim.const_mul (8*C)

/-- Number of primes m < p ≤ X that attain the cofactor bound. -/
def equalityPrimeCount (m X : ℕ) : ℕ :=
  ((Nat.primesLE X).filter (fun p => m < p ∧ f (m*p) = m)).card

private theorem prime_counts_partition {m X : ℕ} (hm : 2 ≤ m) (hX : m ≤ X) :
    equalityPrimeCount m X + exceptionalPrimeCount m X + Nat.primeCounting m =
      Nat.primeCounting X := by
  let s := (Nat.primesLE X).filter (m < ·)
  have hg : s.filter (fun p => f (m*p) = m) = (Nat.primesLE X).filter
      (fun p => m < p ∧ f (m*p) = m) := by ext p; simp [s, and_assoc]
  have hb : s.filter (fun p => ¬ f (m*p) = m) = (Finset.range (X+1)).filter
      (fun p => p.Prime ∧ m < p ∧ f (m*p) < m) := by
    ext p
    simp only [s, Finset.mem_filter, Nat.mem_primesLE, Finset.mem_range]
    by_cases hp : p.Prime <;> by_cases hmp : m < p <;> simp [hp, hmp]
    intro _
    have hhalf : p ≤ m*p/2 := by rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]; nlinarith
    have hcol := large_prime_column (t := 1) hp hmp (by omega : 1 ≤ m)
    simp only [one_mul] at hcol
    have hle := (f_le_column hp.two_le hhalf).trans (hcol.le.trans
      (Nat.gcd_le_left _ (by omega : 0 < m)))
    omega
  have hs : (Nat.primesLE X).filter (fun p => ¬ m < p) = Nat.primesLE m := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, hp⟩, hpm⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpm, hp⟩
      exact ⟨⟨hpm.trans hX, hp⟩, by omega⟩
  have h₁ := Finset.card_filter_add_card_filter_not (s := s) (fun p => f (m*p) = m)
  have h₂ := Finset.card_filter_add_card_filter_not (s := Nat.primesLE X) (m < ·)
  rw [hg, hb] at h₁
  rw [hs, Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at h₂
  exact (congrArg (· + Nat.primeCounting m) h₁).trans h₂

open Filter Topology in
theorem equality_prime_density_one {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun X : ℕ => (equalityPrimeCount m X : ℝ) / Nat.primeCounting X)
      atTop (𝓝 1) := by
  have hpi : Tendsto (fun X : ℕ => (Nat.primeCounting X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  have hsmall := hpi.const_div_atTop (Nat.primeCounting m : ℝ)
  have hlim : Tendsto (fun X : ℕ => 1 - (exceptionalPrimeCount m X : ℝ) / Nat.primeCounting X -
      (Nat.primeCounting m : ℝ) / Nat.primeCounting X) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub (exceptional_prime_density_zero hm)).sub hsmall
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop m, hpi.eventually_gt_atTop 0] with X hX hp
  have hc : (equalityPrimeCount m X : ℝ) + exceptionalPrimeCount m X + Nat.primeCounting m =
      Nat.primeCounting X := by exact_mod_cast prime_counts_partition hm hX
  field_simp [ne_of_gt hp]
  linarith

end Erdos700
