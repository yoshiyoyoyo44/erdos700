import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring

/-! Splitting a power at exponent j + 1 replaces it by p copies at exponent j.
A multiset stores the exponents, with multiplicities recording the number of copies of each power. -/

namespace Erdos700

/-- The value of a multiset of exponents in base p. -/
def value (p : ℕ) (s : Multiset ℕ) : ℕ := (s.map (p ^ ·)).sum

@[simp] theorem value_add (p : ℕ) (s t : Multiset ℕ) :
    value p (s + t) = value p s + value p t := by simp [value]

@[simp] theorem value_singleton (p j : ℕ) : value p {j} = p ^ j := by simp [value]

@[simp] theorem value_replicate (p a j : ℕ) :
    value p (Multiset.replicate a j) = a * p ^ j := by simp [value]

/-- Expand a list of digit counts, starting at exponent j. -/
def terms : ℕ → List ℕ → Multiset ℕ
  | _, [] => 0
  | j, a :: ds => Multiset.replicate a j + terms (j + 1) ds

/-- The unrefined partition into powers given by the base-p digits of n. -/
def canonical (p n : ℕ) : Multiset ℕ := terms 0 (p.digits n)

private theorem value_terms (p j : ℕ) (ds : List ℕ) :
    value p (terms j ds) = p ^ j * Nat.ofDigits p ds := by
  induction ds generalizing j with
  | nil => simp [terms, value, Nat.ofDigits]
  | cons a ds ih => simp [terms, ih, Nat.ofDigits, pow_succ]; ring

private theorem card_terms (j : ℕ) (ds : List ℕ) :
    (terms j ds).card = ds.sum := by
  induction ds generalizing j with
  | nil => simp [terms]
  | cons a ds ih => simp [terms, ih]

@[simp] theorem value_canonical (p n : ℕ) : value p (canonical p n) = n := by
  simp [canonical, value_terms, Nat.ofDigits_digits]

@[simp] theorem card_canonical (p n : ℕ) : (canonical p n).card = (p.digits n).sum :=
  card_terms _ _

private theorem terms_append_zeros (j : ℕ) (ds : List ℕ) (z : ℕ) :
    terms j (ds ++ List.replicate z 0) = terms j ds := by
  induction ds generalizing j with
  | nil =>
    induction z generalizing j with
    | zero => rfl
    | succ z ih => simpa [terms, List.replicate_succ] using ih (j + 1)
  | cons a ds ih => simp [terms, ih]

private def counts (s : Multiset ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | j, w + 1 => s.count j :: counts s (j + 1) w

private theorem count_terms_counts (s : Multiset ℕ) (j w i : ℕ) :
    (terms j (counts s j w)).count i = if j ≤ i ∧ i < j + w then s.count i else 0 := by
  induction w generalizing j with
  | zero => simp [counts, terms]
  | succ w ih =>
    simp only [counts, terms, Multiset.count_add, Multiset.count_replicate, ih]
    split_ifs <;> subst_vars <;> omega

private theorem terms_counts (s : Multiset ℕ) :
    terms 0 (counts s 0 (s.toFinset.sup id + 1)) = s := by
  ext i
  rw [count_terms_counts]
  split_ifs with h
  · rfl
  · have hi : i ∉ s := by
      intro hi
      have := Finset.le_sup (f := id) (Multiset.mem_toFinset.mpr hi)
      exact h ⟨Nat.zero_le _, by simpa using Nat.lt_succ_of_le this⟩
    simp [Multiset.count_eq_zero.mpr hi]

private theorem counts_lt {p : ℕ} {s : Multiset ℕ} (h : ∀ i, s.count i < p) (j w : ℕ) :
    ∀ a ∈ counts s j w, a < p := by
  induction w generalizing j with
  | zero => simp [counts]
  | succ w ih => simpa [counts] using And.intro (h j) (ih (j + 1))

/-- With fewer than p copies at every exponent, the partition is the base-p expansion. -/
theorem canonical_of_reduced {p : ℕ} (hp : 1 < p) (s : Multiset ℕ)
    (h : ∀ i, s.count i < p) : canonical p (value p s) = s := by
  let ds := counts s 0 (s.toFinset.sup id + 1)
  have hds : terms 0 ds = s := terms_counts s
  have hv : value p s = Nat.ofDigits p ds := by rw [← hds, value_terms]; simp
  have hpad : Nat.digitsAppend p ds.length (Nat.ofDigits p ds) = ds :=
    (Nat.setInvOn_digitsAppend_ofDigits hp ds.length).1 ⟨rfl, counts_lt h _ _⟩
  calc
    canonical p (value p s) = terms 0 (p.digits (Nat.ofDigits p ds)) := by rw [canonical, hv]
    _ = terms 0 (Nat.digitsAppend p ds.length (Nat.ofDigits p ds)) := by
      simp [Nat.digitsAppend, terms_append_zeros]
    _ = s := by rw [hpad, hds]

/-- A sequence of exactly t elementary splits from a fixed starting partition. -/
inductive Refines (p : ℕ) (start : Multiset ℕ) : ℕ → Multiset ℕ → Prop
  | refl : Refines p start 0 start
  | split {t j : ℕ} {rest : Multiset ℕ} : Refines p start t (rest + {j + 1}) →
      Refines p start (t + 1) (rest + Multiset.replicate p j)

theorem Refines.value_eq {p t : ℕ} {s u : Multiset ℕ} (h : Refines p s t u) :
    value p u = value p s := by
  induction h with
  | refl => rfl
  | @split t j rest _ ih => simpa [pow_succ, Nat.mul_comm] using ih

theorem Refines.card_eq {p t : ℕ} {s u : Multiset ℕ} (hp : 1 < p) (h : Refines p s t u) :
    u.card = s.card + (p - 1) * t := by
  induction h with
  | refl => simp
  | split _ ih =>
    simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_replicate,
      Nat.mul_succ] at *
    omega

/-- Reverse carries reduce the number of terms until every digit is below the base. -/
theorem exists_refinement {p : ℕ} (hp : 1 < p) (s : Multiset ℕ) :
    ∃ t, Refines p (canonical p (value p s)) t s := by
  by_cases h : ∀ i, s.count i < p
  · rw [canonical_of_reduced hp s h]
    exact ⟨0, .refl⟩
  · push Not at h
    obtain ⟨j, hj⟩ := h
    have hle : Multiset.replicate p j ≤ s := Multiset.le_count_iff_replicate_le.mp hj
    obtain ⟨rest, hs⟩ := exists_add_of_le hle
    have hv : value p (rest + {j + 1}) = value p s := by
      rw [hs]; simp [pow_succ, Nat.mul_comm, Nat.add_comm]
    have hsmall : (rest + {j + 1}).card < s.card := by rw [hs]; simp; omega
    obtain ⟨t, ht⟩ := exists_refinement hp (rest + {j + 1})
    rw [hv] at ht
    have hlast : rest + Multiset.replicate p j = s := (add_comm _ _).trans hs.symm
    exact ⟨t + 1, hlast ▸ ht.split⟩
termination_by s.card
decreasing_by exact hsmall

theorem digitSum_le_card {p : ℕ} (hp : 1 < p) (s : Multiset ℕ) :
    (p.digits (value p s)).sum ≤ s.card := by
  obtain ⟨t, h⟩ := exists_refinement hp s
  simpa only [h.card_eq hp, card_canonical] using
    (Nat.le_add_right (p.digits (value p s)).sum ((p - 1) * t))

/-- Subset sums after at most budget splits of the base-p expansion of n. -/
def splitSums (p n budget : ℕ) : Set ℕ :=
  {k | ∃ t ≤ budget, ∃ a b : Multiset ℕ,
    Refines p (canonical p n) t (a + b) ∧ value p a = k}

/-- For every k in the row, the exact least split budget is the exponent of p in choose n k. -/
theorem mem_splitSums_iff {p n k budget : ℕ} (hp : p.Prime) (hk : k ≤ n) :
    k ∈ splitSums p n budget ↔ (n.choose k).factorization p ≤ budget := by
  letI : Fact p.Prime := ⟨hp⟩
  have hK := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := p) hk
  rw [← Nat.factorization_def _ hp] at hK
  have hpos : 0 < p - 1 := by have := hp.two_le; omega
  constructor
  · rintro ⟨t, ht, a, b, h, ha⟩
    have hv := h.value_eq
    simp only [value_add, value_canonical, ha] at hv
    have hb : value p b = n - k := by omega
    have hcard := h.card_eq hp.one_lt
    simp only [Multiset.card_add, card_canonical] at hcard
    have hleft := digitSum_le_card hp.one_lt a
    have hright := digitSum_le_card hp.one_lt b
    rw [ha] at hleft
    rw [hb] at hright
    apply le_trans _ ht
    apply Nat.le_of_mul_le_mul_left (c := p - 1) ?_ hpos
    omega
  · intro hb
    let a := canonical p k
    let b := canonical p (n - k)
    have hv : value p (a + b) = n := by simp [a, b, Nat.add_sub_of_le hk]
    obtain ⟨t, h⟩ := exists_refinement hp.one_lt (a + b)
    rw [hv] at h
    have hcard := h.card_eq hp.one_lt
    simp only [a, b, Multiset.card_add, card_canonical] at hcard
    have ht : t = (n.choose k).factorization p := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      omega
    exact ⟨t, ht ▸ hb, a, b, h, value_canonical _ _⟩

end Erdos700
