/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedScalarEmbedding
public import LeanCanny.Encoding.IntegralFramedPhysicalSquarePoint
/-! # One full vertex supplies the scalar-column interpreting hom -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedScalarEmbedding
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedScalarEmbedding (scalarMap)
open scoped Classical

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
variable (c w : List Bool)
local notation "S" => IntegralFramedPhysicalSquare.input P D H L F C hs key hpos
local notation "x" => IntegralMixedCutSource.Family.state (family P D H) (key c)

theorem exists_interpretation (hv : SquareSampleCompleteVertices.Valid S c w) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
        (SquareSampleCompleteVertices.candidate S c w hv).val (scalarMap P D H (key c) i)^
          UniformIntegralPowerSchedule.weights ((family P D H).cap (key c))
            (2^(family P D H).width (key c)) ((family P D H).birth (key c)) i) ∧
      ∀i,φ ((x).bank.numerator i)/((x).bank.denominator i:ℝ)=
        IntegralFramedPhysicalSquare.point P D H L F C hs key hpos c w hv i :=by
  exact IntegralFramedPhysicalSquare.exists_interpretation P D H L F C hs key hpos c w hv

end LeanCanny.Geometry.IntegralMixedFramedScalarEmbedding
