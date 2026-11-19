import Erdos700.Classification

namespace Erdos700

/-- The infimum formulation of the minimum used in Formal Conjectures #700. -/
noncomputable def columnInfimum (n : ℕ) : ℕ :=
  sInf {g : ℕ | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ g = Nat.gcd n (n.choose k)}

theorem f_eq_columnInfimum {n : ℕ} (hn : 4 ≤ n) : f n = columnInfimum n := by
  let S : Set ℕ := {g | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ g = Nat.gcd n (n.choose k)}
  have hS : S.Nonempty := ⟨_, 2, by decide, by omega, rfl⟩
  change f n = sInf S
  apply le_antisymm
  · obtain ⟨k, hk, hhalf, hv⟩ := Nat.sInf_mem hS
    rw [hv]
    exact f_le_column (by omega) hhalf
  · apply (le_f_iff hn).mpr
    intro k hk hhalf
    exact Nat.sInf_le (s := S) ⟨k, by omega, hhalf, rfl⟩

/-- Answer for the largest prime power, using only the factorization and partial sums. -/
def largestPrimePowerAnswer : Set ℕ :=
  {n | ¬ n.Prime ∧ 1 < n ∧ 1 < n.primeFactors.card ∧
    ∀ d, Critical n d → commonSums n d = {0, n}}

/-- Answer for the largest prime, including the squares of primes. -/
def largestPrimeAnswer : Set ℕ :=
  {n | ¬ n.Prime ∧ 1 < n ∧ ((∃ p : ℕ, p.Prime ∧ n = p ^ 2) ∨
    (1 < n.primeFactors.card ∧ maxPrime n = maxPrimePower n ∧
      ∀ d, Critical n d → commonSums n d = {0, n}))}

private theorem four_le_of_composite {n : ℕ} (hc : ¬ n.Prime) (hn : 1 < n) : 4 ≤ n := by
  by_contra! h
  have h23 : n = 2 ∨ n = 3 := by omega
  rcases h23 with rfl | rfl
  · exact hc Nat.prime_two
  · exact hc Nat.prime_three

/-- The two equality sets in #700(a), in the infimum formulation, with explicit answers. -/
theorem equality_sets :
    {n : ℕ | ¬ n.Prime ∧ 1 < n ∧ columnInfimum n = n / maxPrimePower n} =
        largestPrimePowerAnswer ∧
    {n : ℕ | ¬ n.Prime ∧ 1 < n ∧ columnInfimum n = n / maxPrime n} =
        largestPrimeAnswer := by
  constructor <;> ext n
  · change (¬ n.Prime ∧ 1 < n ∧ columnInfimum n = n / maxPrimePower n) ↔ _
    apply and_congr_right
    intro hc
    apply and_congr_right
    intro hn
    have h4 := four_le_of_composite hc hn
    rw [← f_eq_columnInfimum h4]
    exact (all_composite_criteria h4 hc).1
  · change (¬ n.Prime ∧ 1 < n ∧ columnInfimum n = n / maxPrime n) ↔ _
    apply and_congr_right
    intro hc
    apply and_congr_right
    intro hn
    have h4 := four_le_of_composite hc hn
    rw [← f_eq_columnInfimum h4]
    exact (all_composite_criteria h4 hc).2

end Erdos700
