/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCanonicalCompleteVertex

/-! # One complete joint vertex is determined by its literal bank values

Odd power weights and nonzero integer denominators recover every scalar
prefix coordinate. This does not require nonsingular prefix roots or any
independent interpretation of retained coordinates.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedCanonicalBankPoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem point_injective (x : State P S B m ι) : Function.Injective (point x) := by
  intro z w H
  funext i
  apply (weights_odd S (2^B) m i).pow_injective
  have HI:=congrFun H i
  change z i^weights S (2^B) m i/(x.bank.denominator i:ℝ)=
    w i^weights S (2^B) m i/(x.bank.denominator i:ℝ) at HI
  have HH:=congrArg (fun a : ℝ=>a*(x.bank.denominator i:ℝ)) HI
  simpa only [div_mul_cancel₀ _ (denominator_ne_zero x i)] using HH

theorem vertex_injective (x : State P S B m ι) (F : SquareSampleInput.Inputs) (u w v : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F u w) (hv : SquareSampleCompleteVertices.Valid F u v)
    (hm : F.count u=m)
    (HE : point x (IntegralMixedCanonicalCompleteVertex.tuple F u w hw hm)=
      point x (IntegralMixedCanonicalCompleteVertex.tuple F u v hv hm)) : w=v := by
  cases hm
  have HT:=point_injective x HE
  apply SquareSampleCompleteVertices.candidate_injective F u w v hw hv
  exact Subtype.ext HT

end LeanCanny.Geometry.IntegralMixedCanonicalBankPoint
