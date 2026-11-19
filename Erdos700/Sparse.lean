import Erdos700.LargePrime
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Erdos700

/-- Each base-B digit is chosen from 0,...,B-2, including padded leading zeros. -/
private def missingDigitValues (B : ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | r+1 => ((missingDigitValues B r) ×ˢ Finset.range (B-1)).image
      (fun qr => B * qr.1 + qr.2)

private theorem card_missingDigitValues (B r : ℕ) :
    (missingDigitValues B r).card ≤ (B-1)^r := by
  induction r with
  | zero => simp [missingDigitValues]
  | succ r ih =>
    unfold missingDigitValues
    calc
      _ ≤ ((missingDigitValues B r) ×ˢ Finset.range (B-1)).card := Finset.card_image_le
      _ ≤ (B-1)^(r+1) := by simpa [pow_succ] using Nat.mul_le_mul_right (B-1) ih

private theorem mem_missingDigitValues {B r x : ℕ} (hB : 1 < B) (hx : x < B^r)
    (ha : ∀ i < r, x / B^i % B ≠ B-1) : x ∈ missingDigitValues B r := by
  induction r generalizing x with
  | zero => simp only [pow_zero, Nat.lt_one_iff] at hx; simp [hx, missingDigitValues]
  | succ r ih =>
    have hrem := Nat.mod_lt x (by omega : 0 < B)
    have hlow : x % B ≠ B-1 := by simpa using ha 0 (Nat.zero_lt_succ r)
    have hq : x / B < B^r := (Nat.div_lt_iff_lt_mul (by omega : 0 < B)).mpr (by simpa [pow_succ] using hx)
    have htail (i : ℕ) (hi : i < r) : x / B / B^i % B ≠ B-1 := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
      exact ha (i+1) (by omega)
    exact Finset.mem_image.mpr ⟨(x/B, x%B), Finset.mem_product.mpr
      ⟨ih hq htail, Finset.mem_range.mpr (by omega)⟩, Nat.div_add_mod x B⟩

private theorem block_of_max_digit {x B i : ℕ} (hB : 1 < B)
    (hi : x / B ^ i % B = B-1) : ∃ v, 0 < v ∧ v ≤ B ^ i ∧ B ^ (i+1) ∣ x+v := by
  let M := B ^ i
  have hM : 0 < M := pow_pos (by omega : 0 < B) i
  have hr := Nat.mod_lt x hM
  refine ⟨M - x%M, by omega, by omega, ?_⟩
  have hd : B ∣ x/M + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_eq_of_lt hB]
    change (x / B^i % B + 1) % B = 0
    rw [hi, Nat.sub_add_cancel (by omega : 1 ≤ B), Nat.mod_self]
  have hx : x + (M - x%M) = M*(x/M + 1) := by
    have hx := Nat.div_add_mod x M
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [hx, pow_succ]
  exact Nat.mul_dvd_mul_left M hd

/-- Group base-ℓ digits into blocks long enough to force all the necessary carries. -/
def blockBase (m ℓ : ℕ) : ℕ := ℓ ^ (Nat.clog ℓ m + m.factorization ℓ - 1)

theorem blockBase_gt_one {m ℓ : ℕ} (hm : 2 ≤ m) (hℓ : ℓ ∈ m.primeFactors) :
    1 < blockBase m ℓ := by
  obtain ⟨hp, hdiv, hm0⟩ := Nat.mem_primeFactors.mp hℓ
  have hh := Nat.clog_pos hp.one_lt (by omega : 1 < m)
  have ha := hp.factorization_pos_of_dvd hm0 hdiv
  exact one_lt_pow₀ hp.one_lt (by omega : Nat.clog ℓ m + m.factorization ℓ - 1 ≠ 0)

private theorem equality_of_max_digits {m p : ℕ} (hm : 2 ≤ m) (hp : p.Prime) (hmp : m < p)
    (hdigits : ∀ ℓ ∈ m.primeFactors, ∃ i : ℕ, p / (blockBase m ℓ)^i % blockBase m ℓ =
      blockBase m ℓ - 1) : f (m*p) = m := by
  apply fixed_cofactor_of_blocks hm hp hmp
  intro ℓ hℓ
  have hprime := (Nat.mem_primeFactors.mp hℓ).1
  let h := Nat.clog ℓ m
  let a := m.factorization ℓ
  let L := h+a-1
  obtain ⟨i, hi⟩ := hdigits ℓ hℓ
  obtain ⟨v, hv, hvd, hdiv⟩ := block_of_max_digit (blockBase_gt_one hm hℓ) hi
  have hh : 0 < h := Nat.clog_pos hprime.one_lt (by omega)
  have hl : L+1 = h+a := by dsimp [L]; omega
  refine ⟨h, L*i, v, hh, Nat.le_pow_clog hprime.one_lt m, hv, ?_, ?_⟩
  · simpa only [blockBase, ← pow_mul] using hvd
  · change ℓ^(L*i+h+a-1) ∣ p+v
    change (ℓ^L)^(i+1) ∣ p+v at hdiv
    rw [← pow_mul, Nat.mul_add, Nat.mul_one] at hdiv
    rwa [show L*i+h+a-1 = L*i+L by omega]

/-- Number of primes p through X, with p > m, where f(mp) falls below m. -/
def exceptionalPrimeCount (m X : ℕ) : ℕ :=
  ((Finset.range (X+1)).filter (fun p => p.Prime ∧ m < p ∧ f (m*p) < m)).card

/-- Explicit bound for exceptional primes through X, for every fixed cofactor m ≥ 2.
Each summand grows at most as a constant times X^(log(B-1)/log(B)), with B = blockBase m ℓ. -/
theorem exceptional_prime_count {m : ℕ} (hm : 2 ≤ m) (X : ℕ) :
    exceptionalPrimeCount m X ≤
      ∑ ℓ ∈ m.primeFactors, (blockBase m ℓ - 1) ^ (Nat.log (blockBase m ℓ) X + 1) := by
  let bad (ℓ : ℕ) := missingDigitValues (blockBase m ℓ) (Nat.log (blockBase m ℓ) X + 1)
  have hsub : (Finset.range (X+1)).filter (fun p => p.Prime ∧ m < p ∧ f (m*p) < m) ⊆
      m.primeFactors.biUnion bad := by
    intro p hmem
    obtain ⟨hX, hp, hmp, hbad⟩ := Finset.mem_filter.mp hmem
    have hpX : p ≤ X := by simpa using Finset.mem_range.mp hX
    have hfail : ¬ ∀ ℓ ∈ m.primeFactors, ∃ i : ℕ, p / (blockBase m ℓ)^i % blockBase m ℓ =
        blockBase m ℓ - 1 := fun h => hbad.ne (equality_of_max_digits hm hp hmp h)
    push Not at hfail
    obtain ⟨ℓ, hℓ, hmiss⟩ := hfail
    have hB := blockBase_gt_one hm hℓ
    exact Finset.mem_biUnion.mpr ⟨ℓ, hℓ, mem_missingDigitValues hB
      (hpX.trans_lt (Nat.lt_pow_succ_log_self hB X)) (fun i _ => hmiss i)⟩
  calc
    _ ≤ (m.primeFactors.biUnion bad).card := Finset.card_le_card hsub
    _ ≤ ∑ ℓ ∈ m.primeFactors, (bad ℓ).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun ℓ _ => card_missingDigitValues _ _)

end Erdos700
