import Erdos700.Criterion
import Erdos700.PrimePowers
import Mathlib.Data.Nat.Factorization.PrimePow

namespace Erdos700

/-- Both versions of Theorem 1, for every composite input. -/
theorem all_composite_criteria {n : ℕ} (hn : 4 ≤ n) (hc : ¬ n.Prime) :
    (f n = n / maxPrimePower n ↔ 1 < n.primeFactors.card ∧
      ∀ d, Critical n d → commonSums n d = {0, n}) ∧
    (f n = n / maxPrime n ↔ (∃ p : ℕ, p.Prime ∧ n = p ^ 2) ∨
      (1 < n.primeFactors.card ∧ maxPrime n = maxPrimePower n ∧
        ∀ d, Critical n d → commonSums n d = {0, n})) := by
  by_cases hmix : 1 < n.primeFactors.card
  · have hsq : ¬ ∃ p : ℕ, p.Prime ∧ n = p ^ 2 := by
      rintro ⟨p, hp, rfl⟩
      simp [Nat.primeFactors_prime_pow (by decide : 2 ≠ 0) hp] at hmix
    simpa only [hmix, hsq, true_and, false_or] using
      And.intro (general_criterion hmix) (largestPrime_criterion hmix)
  · have hpow : IsPrimePow n := by
      by_contra h
      exact hmix (Finset.one_lt_card_iff_nontrivial.mpr
        ((Nat.not_isPrimePow_iff_nontrivial_of_two_le (by omega)).mp h))
    obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
    have ha2 : 2 ≤ a := by
      by_contra! h
      have he : a = 1 := by omega
      simp [he, hp] at hc
    simp only [hmix, false_and, or_false, iff_false]
    refine ⟨prime_power_original_ne hp ha2, ?_⟩
    constructor
    · intro h
      exact ⟨p, hp, by rw [(prime_power_largestPrime_iff hp ha2).mp h]⟩
    · rintro ⟨q, hq, h⟩
      rw [h]
      exact (prime_power_largestPrime_iff hq (le_refl 2)).mpr rfl

end Erdos700
