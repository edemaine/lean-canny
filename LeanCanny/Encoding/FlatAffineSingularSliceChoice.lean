/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSliceRegularity

/-! # Computing an actual singular child label

When the native slice singularity test accepts, a streamed native word search
returns an accepted complete singular child, retaining its exact parent.
The output width is derived from the original complete sampler.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSingularSliceChoice
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineCompleteRootStages (next newest)
open FlatAffineCompleteChildLabels (parentCone)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def test (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (p : List Bool × List Bool) : Bool :=
  decide (FlatAffineSliceRegularity.query (pair p.1 p.2) ∈ FlatAffineSingularChildLabels.language F cone)

noncomputable def value (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) : List Bool → List Bool :=
  ImplicitGraph.findWord (test F cone) (FlatAffineSliceRegularity.width F cone)

theorem evaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    SpaceFunction (value F cone) := by
  have D := (FlatAffineSingularChildLabels.decider h cone).precompose FlatAffineSliceRegularity.query FlatAffineSliceRegularity.query_FP
  have P := pair_computable (Turing.MultiTapeTM.ComputableTidilyInPolyTime.fst Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.snd Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
  have E := D.computable.comp (Turing.MultiTapeTM.ComputableTidilyInPolySpace.of_polyTime P)
  exact ⟨ImplicitGraph.findWord_computable E (FlatAffineSliceRegularity.width_unary h cone)⟩

theorem value_length (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) (q : List Bool) :
    (value F cone q).length = FlatAffineSliceRegularity.width F cone q :=
  ImplicitGraph.findWord_length _ _ _

theorem value_accepted (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) (q : List Bool)
    (hq : q ∈ FlatAffineSliceRegularity.singularLanguage F cone) :
    FlatAffineSliceRegularity.query (pair q (value F cone q)) ∈ FlatAffineSingularChildLabels.language F cone := by
  obtain ⟨w, hw, ha⟩ := hq
  have H := ImplicitGraph.findWord_correct (test := test F cone)
    ⟨w, hw, show test F cone (q, w) = true from decide_eq_true ha⟩
  exact of_decide_eq_true H

theorem value_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) (u v : List Bool)
    (hq : pair u v ∈ FlatAffineSliceRegularity.singularLanguage F cone) :
    FlatAffineCompleteVertices.Valid (next F) cone u (value F cone (pair u v)) ∧
      FlatAffineCompleteVertices.Valid F (parentCone F cone) u v := by
  have H := value_accepted F cone (pair u v) hq
  rw [FlatAffineSliceRegularity.query_packet] at H
  exact FlatAffineCompleteChildLabels.valid F cone u (value F cone (pair u v)) v H.1

theorem value_singular (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) (u v : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v)
    (hq : pair u v ∈ FlatAffineSliceRegularity.singularLanguage F cone) :
    newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u
      ⟨value F cone (pair u v), (value_valid F cone u v hq).1⟩).val ∘ Sum.inl ∈
      FlatAffineSingularSliceSamples.singular F u (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩) := by
  have H := value_accepted F cone (pair u v) hq
  rw [FlatAffineSliceRegularity.query_packet] at H
  exact FlatAffineCompleteChildGeometry.singular_sound F cone u _ v (value_valid F cone u v hq).1 hv H

end LeanCanny.Encoding.FlatAffineSingularSliceChoice
