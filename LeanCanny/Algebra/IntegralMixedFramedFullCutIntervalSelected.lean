/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullCutIntervalFamily
public import LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiSelected
public import LeanCanny.Algebra.RealRootOpenIntervalOrdered
/-! # Exact selected-factor semantics for the two endpoint interval statistics -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullCutIntervalSelected
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedBankSnapshotBits (atKey)
open IntegralMixedFramedFullCutHead (saved)
open IntegralMixedFramedTerminalTarskiSelected (specialization)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family RealIteratedTarski.evaluate

private theorem common_map (keep : Bool) (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (q : List Bool) (z : Fin (A q)→ℝ) :
    (FixedWidthBivariateParameterPairBits.lift keep A p q).map
      ((MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) z).comp
        (MvPolynomial.rename (Fin.cast (FixedWidthBivariateParameterPairBits.arity_eq (A q)))).toRingHom)=
      (FixedWidthBivariateParameterPairBits.common keep A p q).map
        (MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) z) :=by
  rw [FixedWidthBivariateParameterPairBits.common,Polynomial.map_map]

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d : List Bool→ℕ) (q : List Bool)

noncomputable def factor
    (φ : ((family P D H).state (saved P parent q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) : ℝ[X] :=
  (IntegralMixedRelativeCuts.factor ((family P D H).state (saved P parent q)) ((family P D H).birth_bound _)
    ((family P D H).rule _) ((family P D H).kind _)).map φ.toRingHom

theorem head_selected (hc : IntegralMixedFramedFullCutTerminalHead.Valid P D H parent terminal q)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P (parent q))
    (φ : ((family P D H).state (saved P parent q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (z : Fin (atKey P D H (terminal q)).count→ℝ)
    (hφ : ∀i,φ (((family P D H).state (saved P parent q)).sampler.scalarPrefix.basis.generator i)=
      z (UniformIntegralPowerSchedule.embed hc i)^UniformIntegralPowerSchedule.weights
        (P.cap (pairFst (saved P parent q))+1) (2^(family P D H).width (saved P parent q))
        ((family P D H).birth (saved P parent q)) i)
    (hd : (factor P D H parent q φ).natDegree≤IntegralMixedFramedFullCutHead.degree P parent d q) :
    (IntegralMixedFramedFullCutIntervalFamily.head P D H parent terminal d q).map
      (specialization P D H terminal q z)=
      IntegralMixedSelectedCoordinateWindowDegree.head (RealRootOpenIntervalOrdered.constantHead (factor P D H parent q φ)) :=by
  unfold IntegralMixedFramedFullCutIntervalFamily.head specialization
  refine (common_map true (fun c=>(atKey P D H (terminal c)).count)
    (IntegralMixedFramedFullCutTerminalHead.polynomial P D H parent terminal d) q z).trans ?_
  apply MvTwoParameterCoefficient.polynomial_ext
  intro ε δ
  refine (FixedWidthBivariateParameterPairBits.evaluated true (fun c=>(atKey P D H (terminal c)).count)
    (IntegralMixedFramedFullCutTerminalHead.polynomial P D H parent terminal d) q z ε δ).trans ?_
  rw [RealRootOpenIntervalOrdered.evaluated_head]
  exact IntegralMixedFramedFullCutTerminalHead.selected_evaluation P D H parent terminal d q hc ha z δ φ hφ hd

variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (selected : List Bool→ℕ)

theorem query_selected (hi : selected q<(atKey P D H (terminal q)).count)
    (z : Fin (atKey P D H (terminal q)).count→ℝ) (power : List Bool→Fin 3) (negative : Bool) :
    (IntegralMixedFramedFullCutIntervalFamily.query P D H L F C hs terminal selected power negative q).map
      (specialization P D H terminal q z)=
      IntegralMixedSelectedCoordinateWindowDegree.query
        (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q)) z ⟨selected q,hi⟩)
        (((atKey P D H (terminal q)).common:ℝ)^2) negative (power q) :=
  IntegralMixedFramedTerminalTarskiSelected.query_selected P D H L F C hs terminal selected q hi z power negative

theorem model_selected (hc : IntegralMixedFramedFullCutTerminalHead.Valid P D H parent terminal q)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P (parent q))
    (φ : ((family P D H).state (saved P parent q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (z : Fin (atKey P D H (terminal q)).count→ℝ)
    (hφ : ∀i,φ (((family P D H).state (saved P parent q)).sampler.scalarPrefix.basis.generator i)=
      z (UniformIntegralPowerSchedule.embed hc i)^UniformIntegralPowerSchedule.weights
        (P.cap (pairFst (saved P parent q))+1) (2^(family P D H).width (saved P parent q))
        ((family P D H).birth (saved P parent q)) i)
    (hd : (factor P D H parent q φ).natDegree≤IntegralMixedFramedFullCutHead.degree P parent d q)
    (hpos : 0<d q) (hi : selected q<(atKey P D H (terminal q)).count) (negative : Bool) :
    RealIteratedTarski.value
      (((IntegralMixedFramedFullCutIntervalFamily.family P D H L F C hs parent terminal d selected (fun _=>1) negative).head q).map
        (specialization P D H terminal q z))
      (((IntegralMixedFramedFullCutIntervalFamily.family P D H L F C hs parent terminal d selected (fun _=>1) negative).query q).map
        (specialization P D H terminal q z))
      (IntegralMixedFramedFullCutIntervalFamily.degree d q)
      (IntegralMixedFramedFullCutIntervalFamily.inputBound d q)
      (IntegralMixedFramedFullCutIntervalFamily.seedDegree d q)=
      RealRootOpenIntervalOrdered.value (factor P D H parent q φ) (d q)
        (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q)) z ⟨selected q,hi⟩)
        (((atKey P D H (terminal q)).common:ℝ)^2) negative :=by
  change RealIteratedTarski.value
    ((IntegralMixedFramedFullCutIntervalFamily.head P D H parent terminal d q).map (specialization P D H terminal q z))
    ((IntegralMixedFramedFullCutIntervalFamily.query P D H L F C hs terminal selected (fun _=>1) negative q).map
      (specialization P D H terminal q z)) _ _ _=_
  rw [head_selected P D H parent terminal d q hc ha φ z hφ hd,
    query_selected P D H terminal q L F C hs selected hi z (fun _=>1) negative]
  have HMAX : IntegralMixedFramedFullCutIntervalFamily.degree d q=d q:=max_eq_right hpos
  unfold IntegralMixedFramedFullCutIntervalFamily.inputBound IntegralMixedFramedFullCutIntervalFamily.seedDegree
  rw [HMAX]
  rfl

end LeanCanny.Algebra.IntegralMixedFramedFullCutIntervalSelected
