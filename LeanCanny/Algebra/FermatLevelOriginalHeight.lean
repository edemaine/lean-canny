/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FermatLevelPowerResidue
public import LeanCanny.Algebra.IntegralMixedFullHeightSyntax
public import LeanCanny.ETR.PolynomialMass
/-! # One original height ceiling for the old term and the appended power coefficient -/
@[expose] public section
namespace LeanCanny.Algebra.FermatLevelOriginalHeight
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask MvPolynomial

theorem mass_le {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (E : ℕ) :
    MvMass.mass (rename Fin.castSucc p - C ((2 : ℤ)^E)*X (Fin.last n)) ≤ MvMass.mass p + 2^E := by
  apply (MvMass.sub_le _ _).trans
  apply Nat.add_le_add (MvMass.rename_le _ _) (MvMass.mul_le _ _ |>.trans _)
  simp only [MvMass.C, MvMass.X, mul_one, Int.natAbs_pow]
  rfl

theorem term_mass (n : ℕ) (t : ETR.Term) (E : ℕ) :
    MvMass.mass (rename Fin.castSucc (t.finitePolynomial n) - C ((2 : ℤ)^E)*X (Fin.last n)) ≤
      2^t.toData.size + 2^E :=
  (mass_le _ E).trans (Nat.add_le_add_right (t.finitePolynomial_mass n) _)

theorem sum_powers (s e : ℕ) : 2^s + 2^e ≤ 2^(s+e+1) := by
  calc
    2^s + 2^e ≤ 2^(s+e) + 2^(s+e) := Nat.add_le_add
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
    _ = 2^(s+e+1) := by rw [pow_succ]; omega

def height (t : List Bool → ETR.Term) (E : List Bool → ℕ) (r : List Bool) : ℕ :=
  (t r).toData.size + E r + 1

theorem height_binary (t : List Bool → ETR.Term) (E : List Bool → ℕ)
    (ht : (fun r => (t r).toData.toBits) ∈ FP) (hE : BinaryFn E) : BinaryFn (height t E) := by
  have HS : UnaryFn (fun r => (t r).toData.size) := (UnaryFn.length ht).of_eq (fun r => Data.length_toBits (t r).toData)
  exact ((BinaryFn.ofUnary HS).add hE).add (BinaryFn.const 1)

theorem coefficient_bound (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (t : List Bool → ETR.Term) (E : List Bool → ℕ)
    (hlow : ∀ r, (D.spatial r).low = rename Fin.castSucc ((t r).finitePolynomial (P.ambient r)) -
      C ((2 : ℤ)^E r)*X (Fin.last (P.ambient r)))
    (r : List Bool) (e : Fin (P.ambient r+1) →₀ ℕ) :
    ((D.spatial r).low.coeff e).natAbs ≤ 2^height t E r := by
  rw [hlow]
  exact (MvMass.coeff_le _ e).trans ((term_mass _ _ _).trans (sum_powers _ _))

theorem inputs (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (t : List Bool → ETR.Term) (E L : List Bool → ℕ)
    (hlow : ∀ r, (D.spatial r).low = rename Fin.castSucc ((t r).finitePolynomial (P.ambient r)) -
      C ((2 : ℤ)^E r)*X (Fin.last (P.ambient r)))
    (hl : ∀ r, (D.spatial r).leading.natAbs.size ≤ height t E r)
    (hc : ∀ r, ∀ c ∈ D.rules r, IntegralMixedFullScriptHeight.CommandBounds (height t E r) (L r) c)
    (hf : ∀ key, IntegralMixedFullHeightBits.RuleBounds (height t E (pairFst key)) (L (pairFst key)) (D.fallback key).rule) :
    IntegralMixedFullHeightBits.Inputs P D (height t E) L :=
  IntegralMixedFullHeightBits.inputs_of_syntax P D (height t E) L (coefficient_bound P D t E hlow) hl hc hf

theorem word_height_binary (word : List Bool → List Bool) (E : List Bool → ℕ)
    (hw : word ∈ FP) (hE : BinaryFn E) :
    BinaryFn (height (fun r => ETR.TermView.term (word r)) E) := by
  have HT : (fun r => (ETR.TermView.term (word r)).toData.toBits) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp hw ETR.TermView.normalize_mem_FP) (fun r => ETR.TermView.normalize_eq_term (word r))
  exact height_binary _ E HT hE

theorem word_coefficient_bound (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (word : List Bool → List Bool) (E : List Bool → ℕ)
    (hlow : ∀ r, (D.spatial r).low = FermatLevelCoefficientBits.polynomial P.ambient
      (FermatLevelOriginalSpatialBits.old P word) (FermatLevelPowerResidue.coefficient E) r)
    (r : List Bool) (e : Fin (P.ambient r+1) →₀ ℕ) :
    ((D.spatial r).low.coeff e).natAbs ≤ 2^height (fun r => ETR.TermView.term (word r)) E r :=
  coefficient_bound P D _ E hlow r e

theorem word_inputs (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (word : List Bool → List Bool) (E L : List Bool → ℕ)
    (hlow : ∀ r, (D.spatial r).low = FermatLevelCoefficientBits.polynomial P.ambient
      (FermatLevelOriginalSpatialBits.old P word) (FermatLevelPowerResidue.coefficient E) r)
    (hl : ∀ r, (D.spatial r).leading.natAbs.size ≤ height (fun r => ETR.TermView.term (word r)) E r)
    (hc : ∀ r, ∀ c ∈ D.rules r, IntegralMixedFullScriptHeight.CommandBounds
      (height (fun r => ETR.TermView.term (word r)) E r) (L r) c)
    (hf : ∀ key, IntegralMixedFullHeightBits.RuleBounds (height (fun r => ETR.TermView.term (word r)) E (pairFst key))
      (L (pairFst key)) (D.fallback key).rule) :
    IntegralMixedFullHeightBits.Inputs P D (height (fun r => ETR.TermView.term (word r)) E) L :=
  inputs P D _ E L hlow hl hc hf

end LeanCanny.Algebra.FermatLevelOriginalHeight
