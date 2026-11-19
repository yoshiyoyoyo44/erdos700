import Erdos700.Sparse
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity

namespace Erdos700

/-- A uniform loss in the exponent when cancelling two powers modulo ℓ^R. -/
def periodLoss (ℓ q : ℕ) : ℕ :=
  padicValNat ℓ (q^(ℓ-1)-1) + padicValNat ℓ (q+1) + padicValNat ℓ 2

private theorem valuation_of_power_period {ℓ q R d : ℕ} (hℓ : ℓ.Prime) (hq : 1 < q)
    (hcop : ¬ ℓ ∣ q) (hd : 0 < d) (hper : q^d ≡ 1 [MOD ℓ^R]) :
    R ≤ periodLoss ℓ q + padicValNat ℓ d := by
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  rcases hℓ.eq_two_or_odd with rfl | hodd
  · have h2d : 0 < 2*d := by omega
    have hgt : 1 < q^(2*d) := one_lt_pow₀ hq h2d.ne'
    have hh : q^(2*d) ≡ 1 [MOD 2^R] := by
      simpa only [Nat.mul_comm 2 d, pow_mul, one_pow] using hper.pow 2
    have hval := (padicValNat_dvd_iff_le (Nat.sub_ne_zero_of_lt hgt)).mp
      ((Nat.modEq_iff_dvd' hgt.le).mp hh.symm)
    have hlte := padicValNat.pow_two_sub_one hq hcop h2d.ne' (even_two_mul d)
    rw [padicValNat.mul (by decide : 2 ≠ 0) hd.ne'] at hlte
    simpa only [periodLoss, Nat.reduceSub, pow_one] using
      (by omega : R ≤ padicValNat 2 (q-1) + padicValNat 2 (q+1) + padicValNat 2 2 + padicValNat 2 d)
  · let b := ℓ-1
    have hb : 0 < b := Nat.sub_pos_of_lt hℓ.one_lt
    have hx : 1 < q^b := one_lt_pow₀ hq hb.ne'
    have hxd : 1 < (q^b)^d := one_lt_pow₀ hx hd.ne'
    have hbase : q^b ≡ 1 [MOD ℓ] := by
      simpa [b, Nat.totient_prime hℓ] using
        (Nat.ModEq.pow_totient (hℓ.coprime_iff_not_dvd.mpr hcop).symm)
    have hh : (q^b)^d ≡ 1 [MOD ℓ^R] := by
      simpa only [← pow_mul, Nat.mul_comm b d, one_pow] using hper.pow b
    have hval := (padicValNat_dvd_iff_le (Nat.sub_ne_zero_of_lt hxd)).mp
      ((Nat.modEq_iff_dvd' hxd.le).mp hh.symm)
    have hlte := padicValNat.pow_sub_pow (Nat.odd_iff.mpr hodd) hx ((Nat.modEq_iff_dvd' hx.le).mp hbase.symm)
      (fun h => hcop (hℓ.dvd_of_dvd_pow h)) hd.ne'
    simp only [one_pow] at hlte
    unfold periodLoss
    change R ≤ padicValNat ℓ (q^b-1) + _ + _ + _
    omega

/-- Equal power residues force the exponents to agree to within a fixed loss of ℓ-adic precision. -/
theorem exponent_modEq_of_power_modEq {ℓ q R i j : ℕ} (hℓ : ℓ.Prime) (hq : 1 < q)
    (hcop : ¬ ℓ ∣ q) (hh : q^i ≡ q^j [MOD ℓ^R]) :
    i ≡ j [MOD ℓ^(R-periodLoss ℓ q)] := by
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  suffices ordered : ∀ {u v : ℕ}, u ≤ v → q^u ≡ q^v [MOD ℓ^R] →
      u ≡ v [MOD ℓ^(R-periodLoss ℓ q)] by
    rcases le_total i j with h | h
    · exact ordered h hh
    · exact (ordered h hh.symm).symm
  intro u v huv hmod
  rcases huv.eq_or_lt with rfl | hlt
  · rfl
  have hd : 0 < v-u := by omega
  have hprod : q^u * q^(v-u) ≡ q^u * 1 [MOD ℓ^R] := by
    rw [← pow_add, Nat.add_sub_of_le huv, mul_one]
    exact hmod.symm
  have hrel := Nat.ModEq.cancel_left_of_coprime
    (((hℓ.coprime_iff_not_dvd.mpr hcop).pow_left R).pow_right u).gcd_eq_one hprod
  have hbound := valuation_of_power_period hℓ hq hcop hd hrel
  exact (Nat.modEq_iff_dvd' huv).mpr ((padicValNat_dvd_iff_le hd.ne').mpr (by omega))

theorem mem_missingDigitValues_mod {B r x : ℕ} (hB : 1 < B)
    (hmiss : ∀ i < r, x/B^i % B ≠ B-1) : x % B^r ∈ missingDigitValues B r := by
  apply mem_missingDigitValues hB (Nat.mod_lt _ (pow_pos (by omega : 0<B) _))
  intro i hi
  have hsplit : B^r = B^i * B^(r-i) := by rw [← pow_add, Nat.add_sub_of_le hi.le]
  rw [hsplit, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self B (by omega : r-i ≠ 0))]
  exact hmiss i hi

/-- Exponents whose lowest r base-B digits of q^e omit the maximal digit. -/
def exponentsMissingBlock (q B E : ℕ) : Finset ℕ :=
  (Finset.range (E+1)).filter fun e =>
    q^e % B^(Nat.log B E+1) ∈ missingDigitValues B (Nat.log B E+1)

/-- Uniform bound on the number of exponents giving any of the allowed digit strings. -/
theorem card_exponentsMissingBlock {q ℓ L : ℕ} (hℓ : ℓ.Prime) (hq : 1 < q)
    (hcop : ¬ ℓ ∣ q) (hB : 1 < ℓ^L) (E : ℕ) :
    (exponentsMissingBlock q (ℓ^L) E).card ≤
      ℓ^(periodLoss ℓ q) * (ℓ^L-1)^(Nat.log (ℓ^L) E + 1) := by
  let B := ℓ^L
  let r := Nat.log B E + 1
  let c := periodLoss ℓ q
  let D := ℓ^(L*r-c)
  let encode (s : ℕ) := (s/D, q^s % B^r)
  have hsize : E < D*ℓ^c := calc
    E < B^r := Nat.lt_pow_succ_log_self hB E
    _ = ℓ^(L*r) := (pow_mul ℓ L r).symm
    _ ≤ D*ℓ^c := by rw [show D*ℓ^c = ℓ^(L*r-c+c) by rw [pow_add]]; exact Nat.pow_le_pow_right hℓ.pos (by omega)
  have hcard : (exponentsMissingBlock q B E).card ≤
      ((Finset.range (ℓ^c)) ×ˢ missingDigitValues B r).card := by
    apply Finset.card_le_card_of_injOn encode
    · intro s hs
      obtain ⟨hE, hmem⟩ := Finset.mem_filter.mp hs
      have hsE : s ≤ E := by simpa using Finset.mem_range.mp hE
      have hquot : s/D < ℓ^c := (Nat.div_lt_iff_lt_mul (pow_pos hℓ.pos _)).mpr
        (by simpa [mul_comm D] using hsE.trans_lt hsize)
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hquot, hmem⟩
    · intro i _ j _ heq
      have hquot : i/D = j/D := congrArg Prod.fst heq
      have hmod : q^i ≡ q^j [MOD ℓ^(L*r)] := by
        rw [pow_mul]
        exact congrArg Prod.snd heq
      have hrem : i%D = j%D := exponent_modEq_of_power_modEq hℓ hq hcop hmod
      calc
        i = D*(i/D) + i%D := (Nat.div_add_mod i D).symm
        _ = D*(j/D) + j%D := by rw [hquot, hrem]
        _ = j := Nat.div_add_mod j D
  simp only [Finset.card_product, Finset.card_range] at hcard
  exact hcard.trans (Nat.mul_le_mul_left _ (card_missingDigitValues B r))

end Erdos700
