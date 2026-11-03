/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedScalarTarskiIteratedSign
/-! # The ordered native sign specializes the actual relative principal

The hom evaluates the SAME raw scalar columns and retains both formal
parameters. It specializes the determinant element itself, without a norm.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedScalarTarskiIteratedSign
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FixedWidthTarskiPrincipalBits.polynomial

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (key : List Bool→List Bool) (hpos : ∀c,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key c))
variable (O : SquareSampleInput.Inputs)
variable (hc : ∀c,O.count c=(IntegralMixedFramedBankSnapshotBits.atKey P D H (key c)).count)
variable (MF : FixedWidthTarskiPrincipalBits.Family) (read : List Bool→List Bool)
variable (j budget height : List Bool→ℕ)
variable (dim : ∀c b,MF.arity (read (pair c b))=O.count c+2)
variable (hdegree : ∀c b,(FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) (j (pair c b))).totalDegree≤budget (pair c b))
variable (hmass : ∀c b,MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) (j (pair c b)))≤2^height (pair c b))
local notation "S" => IntegralFramedPhysicalSquare.input P D H L F C hs key hpos

noncomputable def specialization (c w b : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    MvPolynomial (Fin (MF.arity (read (pair c b)))) ℤ→+*Polynomial (Polynomial ℝ) :=
  (MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ)
    (fun i=>(SquareSampleCompleteVertices.candidate S c w hv).val
      (IntegralMixedFramedScalarEmbedding.scalarMap P D H (key c) (Fin.cast (hc c) i)))).comp
        (MvPolynomial.rename (Fin.cast (dim c b))).toRingHom

theorem selected_principal (c w b : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    selected P D H L F C hs key hpos O hc MF read j dim c w b hv=
      PrincipalSubresultant.signedPsc
        ((MF.head (read (pair c b))).map (specialization P D H L F C hs key hpos O hc MF read dim c w b hv))
        (PseudoRemainder.seed
          ((MF.head (read (pair c b))).map (specialization P D H L F C hs key hpos O hc MF read dim c w b hv))
          ((MF.query (read (pair c b))).map (specialization P D H L F C hs key hpos O hc MF read dim c w b hv))
          (MF.degree (read (pair c b))) (MF.bound (read (pair c b))))
        (MF.degree (read (pair c b))) (MF.seedDegree (read (pair c b))) (j (pair c b)) :=
  FixedWidthTarskiPrincipalBits.selected MF (read (pair c b)) (j (pair c b))
    (specialization P D H L F C hs key hpos O hc MF read dim c w b hv)

theorem eventually_value (c w b : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    ∃η : ℝ,0<η ∧ ∀ε : ℝ,0<ε→ε<η→∃ζ : ℝ,0<ζ ∧ ∀δ : ℝ,0<δ→δ<ζ→
      value P D H L F C hs key hpos O hc MF read j budget height dim hdegree hmass (pair (pair c w) b)=
        RealInfinitesimalSignSpace.tag
          ((selected P D H L F C hs key hpos O hc MF read j dim c w b hv).eval₂ (Polynomial.evalRingHom ε) δ) :=by
  obtain ⟨η,hη,HE⟩:=RealIteratedInfinitesimalSignSpace.eventually_correct
    (selected P D H L F C hs key hpos O hc MF read j dim c w b hv)
  refine ⟨η,hη,fun ε he heη=>?_⟩
  obtain ⟨ζ,hζ,HD⟩:=HE ε he heη
  refine ⟨ζ,hζ,fun δ hd hdζ=>?_⟩
  rw [value_at P D H L F C hs key hpos O hc MF read j budget height dim hdegree hmass c w b hv]
  exact (HD δ hd hdζ).symm

end LeanCanny.Encoding.IntegralFramedScalarTarskiIteratedSign
