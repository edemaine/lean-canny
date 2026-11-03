/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockColumns
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockHeightRowSpace
public import LeanCanny.Algebra.IntegralMixedFramedHeightCellIdentities
/-! # Literal source, normal and height identifications at a creating prefix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask MvPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedPhysicalSourceAtBits (family)
open IntegralMixedFramedPhysicalHeightBits (Active)
open FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] MvPolynomial.pderiv MvPolynomial.rename

noncomputable abbrev criticalData (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) :=
  IntegralMixedHistory.data ((family P D J base).state q) ((family P D J base).birth_bound q)
    ((family P D J base).rule q)

theorem normal_integer_eq (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (selected : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) (hq : Active P (base q)) :
    IntegralMixedFramedPhysicalNormalAtBits.integer P D J base selected q=
      (criticalData P D J base q).scales ⟨selected q,hs q⟩ := by
  have HS : IntegralMixedPhysicalDenominatorPostBits.scale P (IntegralMixedFramedPhysicalBits.family P D J)
      (base q) (selected q)=((family P D J base).rule q).scales ⟨selected q,hs q⟩ := by
    change (if hi : selected q<spatialCount P D J base q then
      ((family P D J base).rule q).scales ⟨selected q,hi⟩ else 1)=_
    rw [dite_eq_left (hs q)]
  rw [IntegralMixedFramedPhysicalNormalAtBits.integer,ite_eq_left hq,HS]
  rfl

theorem normalPolynomial_eq (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (selected : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) (hq : Active P (base q)) :
    normalPolynomial P D J base selected hs q=
      C ((criticalData P D J base q).scales ⟨selected q,hs q⟩)*
        X (multiplierIndex P D J base q (⟨selected q,hs q⟩ : Fin (spatialCount P D J base q)).succ) := by
  unfold normalPolynomial FixedWidthMonomialBits.polynomial
  rw [dite_eq_left (multiplierSucc P D J base selected hs q).isLt,normal_integer_eq P D J base selected hs q hq]
  exact C_mul_X_eq_monomial.symm

theorem normalAmbientPolynomial_eq (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (selected : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) (hq : Active P (base q)) :
    normalAmbientPolynomial P D J base selected hs q=
      C ((criticalData P D J base q).scales ⟨selected q,hs q⟩)*X (ambientIndex P D J base q ⟨selected q,hs q⟩) := by
  unfold normalAmbientPolynomial FixedWidthMonomialBits.polynomial
  rw [dite_eq_left (ambientIndex P D J base q ⟨selected q,hs q⟩).isLt,normal_integer_eq P D J base selected hs q hq]
  exact C_mul_X_eq_monomial.symm

theorem heightPolynomial_eq (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (base : List Bool→List Bool) (selected : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) (hq : Active P (base q))
    (hi : get P .slot8 (base q)=selected q) :
    heightPolynomial P D J T hr base q=rename (columns P D J base q∘Sum.inl)
      (IntegralHistorySampler.historyHeights ((family P D J base).state q).sampler
        (criticalData P D J base q).heights ⟨selected q,hs q⟩) := by
  rw [heightPolynomial,IntegralMixedFramedPhysicalHeightBits.full_polynomial_height P D J T hr (base q) hq]
  have HE:=IntegralMixedFramedHeightCellIdentities.affine_eq P D J (base q) ⟨selected q,hs q⟩ hi.symm
  rw [IntegralMixedFramedScalarCellsBits.rule_physical P D J (base q) hq.2] at HE
  rw [HE]
  change rename (oldIndex P D J base q) (rename (oldEquiv P D J base q)
    (IntegralHistorySampler.historyHeights ((family P D J base).state q).sampler
      (criticalData P D J base q).heights ⟨selected q,hs q⟩))=_
  rw [rename_rename]
  have HC : oldIndex P D J base q∘oldEquiv P D J base q=columns P D J base q∘Sum.inl := by
    funext i
    exact (columns_old P D J base q i).symm
  rw [HC]

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
