import Erdos700.Density
import Erdos700.PowerFamilies
import Erdos700.PowerPeriods

namespace Erdos700

/-- The block size for exponent statistics depends only on m and the base ℓ. -/
def exponentBlockBase (m ℓ : ℕ) := blockBase (m*(m-1)) ℓ

private theorem exponentBlockBase_gt_one {m ℓ : ℕ} (hm : 2 ≤ m) (hℓ : ℓ ∈ m.primeFactors) :
    1 < exponentBlockBase m ℓ := by
  have hY : 2 ≤ m*(m-1) := by simpa only [Nat.mul_one] using Nat.mul_le_mul hm (by omega : 1 ≤ m-1)
  have h := Nat.mem_primeFactors.mp hℓ
  exact blockBase_gt_one hY (Nat.mem_primeFactors.mpr
    ⟨h.1, h.2.1.trans (dvd_mul_right m _), by omega⟩)

/-- The exception count in Theorem 2 of the manuscript, including the endpoint E. -/
def exceptionalExponentCount (m q E : ℕ) : ℕ :=
  ((Finset.range (E+1)).filter fun e => 0 < e ∧ f (m*q^e) < m).card

theorem exceptional_exponent_count {m q : ℕ} (hm : 2 ≤ m) (hq : q.Prime) (hqm : ¬q ∣ m) (E : ℕ) :
    exceptionalExponentCount m q E ≤ Nat.log q (m-1) + ∑ ℓ ∈ m.primeFactors,
      ℓ^(periodLoss ℓ q) * (exponentBlockBase m ℓ - 1)^(Nat.log (exponentBlockBase m ℓ) E+1) := by
  let h := Nat.log q (m-1)
  let bad (ℓ : ℕ) := exponentsMissingBlock q (exponentBlockBase m ℓ) E
  let unshifted := m.primeFactors.biUnion bad
  let shifted := unshifted.image (fun s => h+s)
  have hsub : (Finset.range (E+1)).filter (fun e => 0<e ∧ f (m*q^e)<m) ⊆
      (Finset.range h) ∪ shifted := by
    intro e hmem
    obtain ⟨hE, he, hbad⟩ := Finset.mem_filter.mp hmem
    by_cases hshort : e < h
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hshort)
    let s := e-h
    have hsum : h+s=e := by dsimp [s]; omega
    have hsE : s ≤ E := by have := Finset.mem_range.mp hE; dsimp [s]; omega
    have hfail : ¬ ∀ ℓ ∈ m.primeFactors, ∃ i : ℕ,
        q^s / (exponentBlockBase m ℓ)^i % exponentBlockBase m ℓ = exponentBlockBase m ℓ-1 := by
      intro hall
      have heq := power_equality_of_digits (s := s) hm hq hqm (by change 0<h+s; omega) hall
      change f (m*q^(h+s))=m at heq
      exact hbad.ne (hsum ▸ heq)
    push Not at hfail
    obtain ⟨ℓ, hℓ, hmiss⟩ := hfail
    have hB := exponentBlockBase_gt_one hm hℓ
    have hmem : s ∈ bad ℓ := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      mem_missingDigitValues_mod hB (fun i _ => hmiss i)⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, Finset.mem_biUnion.mpr ⟨ℓ,hℓ,hmem⟩, hsum⟩)
  have hshifted : shifted.card ≤ ∑ ℓ ∈ m.primeFactors, (bad ℓ).card :=
    Finset.card_image_le.trans Finset.card_biUnion_le
  calc
    _ ≤ ((Finset.range h) ∪ shifted).card := Finset.card_le_card hsub
    _ ≤ (Finset.range h).card + shifted.card := Finset.card_union_le _ _
    _ ≤ _ := by
      rw [Finset.card_range]
      apply Nat.add_le_add_left (hshifted.trans ?_)
      apply Finset.sum_le_sum
      intro ℓ hℓ
      obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hℓ
      have hcop : ¬ℓ ∣ q := fun hd => hqm (((Nat.prime_dvd_prime_iff_eq hprime hq).mp hd) ▸ hdvd)
      exact card_exponentsMissingBlock hprime hq.one_lt hcop (exponentBlockBase_gt_one hm hℓ) E

/-- Theorem 2: one exponent saving works for every prime q coprime to the fixed cofactor. -/
theorem exceptional_exponent_power_saving {m : ℕ} (hm : 2 ≤ m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℕ, q.Prime → ¬q ∣ m → ∃ C : ℝ, 0 < C ∧
      ∀ E : ℕ, 1 ≤ E → (exceptionalExponentCount m q E : ℝ) ≤ C*(E:ℝ)^(1-δ) := by
  let θ (ℓ : ℕ) := digitExponent (exponentBlockBase m ℓ)
  have hs : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  let t := m.primeFactors.sup' hs θ
  have ht : t < 1 := (Finset.sup'_lt_iff hs).mpr
    (fun ℓ hℓ => digitExponent_lt_one (exponentBlockBase_gt_one hm hℓ))
  have ht0 : 0 ≤ t := by
    obtain ⟨ℓ,hℓ⟩ := hs
    have hB := exponentBlockBase_gt_one hm hℓ
    have hbr : (1:ℝ) < exponentBlockBase m ℓ := by exact_mod_cast hB
    have har : (1:ℝ) ≤ ((exponentBlockBase m ℓ-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ exponentBlockBase m ℓ-1)
    exact (Real.logb_nonneg hbr har).trans (Finset.le_sup' θ hℓ)
  refine ⟨1-t, by linarith, ?_⟩
  intro q hq hqm
  let h := Nat.log q (m-1)
  let k (ℓ : ℕ) : ℕ := ℓ^(periodLoss ℓ q)
  let w (ℓ : ℕ) : ℝ := (k ℓ : ℝ) * ((exponentBlockBase m ℓ - 1 : ℕ) : ℝ)
  let W := ∑ ℓ ∈ m.primeFactors, w ℓ
  have hW : 0 ≤ W := Finset.sum_nonneg (fun ℓ _ => by dsimp [w]; positivity)
  refine ⟨(h:ℝ)+1+W, by positivity, ?_⟩
  intro E hE
  have he : (1:ℝ) ≤ E := by exact_mod_cast hE
  have hge : 1 ≤ (E:ℝ)^t := Real.one_le_rpow he ht0
  have hcount := exceptional_exponent_count hm hq hqm E
  calc
    (exceptionalExponentCount m q E : ℝ) ≤ (h:ℝ) + ∑ ℓ ∈ m.primeFactors,
        (k ℓ:ℝ) * (((exponentBlockBase m ℓ-1)^(Nat.log (exponentBlockBase m ℓ) E+1) : ℕ) : ℝ) := by
      exact_mod_cast hcount
    _ ≤ (h:ℝ)*(E:ℝ)^t + ∑ ℓ ∈ m.primeFactors, w ℓ * (E:ℝ)^t := by
      apply add_le_add (by simpa using mul_le_mul_of_nonneg_left hge (Nat.cast_nonneg h))
      apply Finset.sum_le_sum
      intro ℓ hℓ
      rw [show w ℓ = (k ℓ:ℝ) * ((exponentBlockBase m ℓ - 1 : ℕ) : ℝ) from rfl, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact (digit_count_le_rpow (exponentBlockBase_gt_one hm hℓ) hE).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le he (Finset.le_sup' θ hℓ)) (Nat.cast_nonneg _))
    _ ≤ _ := by
      rw [sub_sub_cancel, ← Finset.sum_mul]
      change (h:ℝ)*(E:ℝ)^t + W*(E:ℝ)^t ≤ ((h:ℝ)+1+W)*(E:ℝ)^t
      linarith

open Filter Topology in
theorem exceptional_exponent_density_zero {m q : ℕ} (hm : 2 ≤ m) (hq : q.Prime) (hqm : ¬q ∣ m) :
    Tendsto (fun E : ℕ => (exceptionalExponentCount m q E : ℝ) / E) atTop (𝓝 0) := by
  obtain ⟨δ,hδ,hs⟩ := exceptional_exponent_power_saving hm
  obtain ⟨C,hC,hbound⟩ := hs q hq hqm
  have hlim : Tendsto (fun E : ℕ => (E:ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall (fun E => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    (g := fun E : ℕ => C/(E:ℝ)^δ)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with E hE
    have hpos : 0 < (E:ℝ) := by exact_mod_cast hE
    rw [div_le_iff₀ hpos]
    calc
      _ ≤ C*(E:ℝ)^(1-δ) := hbound E hE
      _ = _ := by rw [Real.rpow_sub hpos, Real.rpow_one]; ring
  · exact hlim.const_div_atTop C

open Filter Topology in
/-- Direct density-one statement for the equality exponents in 1,...,E. -/
theorem equality_exponent_density_one {m q : ℕ} (hm : 2 ≤ m) (hq : q.Prime) (hqm : ¬q ∣ m) :
    Tendsto (fun E : ℕ => (((Finset.Ioc 0 E).filter (fun e => f (m*q^e) = m)).card : ℝ) / E)
      atTop (𝓝 1) := by
  have hlim : Tendsto (fun E : ℕ => 1 - (exceptionalExponentCount m q E : ℝ) / E) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (exceptional_exponent_density_zero hm hq hqm)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with E hE
  have hbad : (Finset.Ioc 0 E).filter (fun e => ¬f (m*q^e) = m) =
      (Finset.range (E+1)).filter (fun e => 0<e ∧ f (m*q^e)<m) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    constructor
    · rintro ⟨⟨he,hbound⟩,hne⟩
      exact ⟨by omega, he, lt_of_le_of_ne (power_cofactor_le hm hq hqm he) hne⟩
    · rintro ⟨hbound,he,hlt⟩
      exact ⟨⟨he,by omega⟩,hlt.ne⟩
  have hpart := Finset.card_filter_add_card_filter_not (s := Finset.Ioc 0 E) (fun e => f (m*q^e)=m)
  rw [hbad, Nat.card_Ioc, Nat.sub_zero] at hpart
  have hsum : (((Finset.Ioc 0 E).filter (fun e => f (m*q^e)=m)).card : ℝ) + exceptionalExponentCount m q E = E := by
    exact_mod_cast hpart
  have hpos : (0:ℝ) < E := by exact_mod_cast hE
  field_simp [hpos.ne']
  linarith

end Erdos700
