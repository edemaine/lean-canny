/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineCompleteChildGeometry
public import LeanCanny.Computation.SpaceFunctionWordExistence

/-! # Native singular-point search in an actual frozen affine slice

The streamed word search uses the derived complete-child width and the native
zero-objective child selector. Under independent slice normals it finds a
witness exactly when the stated parent slice has a singular point.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSliceRegularity
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next newest)
open FlatAffineCompleteComponentSamples (active direction)
open FlatAffineCompleteChildLabels (parentCone)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def query (r : List Bool) : List Bool :=
  pair (pairFst (pairFst r)) (pair (pairSnd r) (pairSnd (pairFst r)))
theorem query_FP : query ∈ FP := by polytime [query]
theorem query_packet (u v w : List Bool) : query (pair (pair u v) w) = pair u (pair w v) := by
  simp only [query, pairFst_pair, pairSnd_pair]

noncomputable def width (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) (q : List Bool) : ℕ :=
  FlatAffineCompleteVertices.width (next F) cone (pairFst q)
theorem width_unary {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    UnaryFn (width F cone) :=
  (FlatAffineCompleteVertices.width_unary (FlatAffineCompleteChildLabels.nextAccess h) cone).comp pairFst_mem_FP

noncomputable def singularLanguage (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) : Language :=
  {q | ∃ w : List Bool, w.length = width F cone q ∧
    query (pair q w) ∈ FlatAffineSingularChildLabels.language F cone}

theorem singularDecider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    SpaceDecider (singularLanguage F cone) := by
  have E := ((FlatAffineSingularChildLabels.decider h cone).precompose query query_FP).flagEvaluator
  have W := E.exists_words (width_unary h cone)
  apply W.decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [singularLanguage, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem singular_mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    singularLanguage F cone ∈ PSPACE := (singularDecider h cone).mem_PSPACE

theorem singular_correct (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v)
    (hheights : ∀ c : active F u → ℝ, (∀ i, ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ) = 0) → ∀ j, c j = 0) :
    pair u v ∈ singularLanguage F cone ↔
      (FlatAffineSingularSliceSamples.singular F u
        (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩)).Nonempty := by
  simp only [singularLanguage, Set.mem_ofPred_eq, width, pairFst_pair, query_packet]
  constructor
  · rintro ⟨w, _, ha⟩
    have HA : pair u (pair w v) ∈ FlatAffineCompleteChildLabels.language F cone := ha.1
    have HW := (FlatAffineCompleteChildLabels.valid F cone u w v HA).1
    exact ⟨_, FlatAffineCompleteChildGeometry.singular_sound F cone u w v HW hv ha⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, ha, _⟩ := FlatAffineSingularChildLabels.singular_accepted F cone u v hv hheights z hz
    exact ⟨w.val, FlatAffineCompleteVertices.word_length (next F) cone u w.val w.property, ha⟩

noncomputable def regularLanguage (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) : Language :=
  {q | q ∈ FlatAffineCompleteVertices.language F (parentCone F cone) ∧ q ∉ singularLanguage F cone}

theorem regularDecider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    SpaceDecider (regularLanguage F cone) := by
  have V := (SpaceDecider.ofPSPACE (FlatAffineCompleteVertices.mem_PSPACE h (parentCone F cone))).flagEvaluator
  have N := (singularDecider h cone).flagEvaluator.postcompose (fun z => [decide (z ≠ [true])])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  apply (V.andFlags N).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [regularLanguage, Set.mem_ofPred_eq, ne_eq, List.cons.injEq, and_true, decide_eq_true_eq, Function.comp_apply]

theorem regular_mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    regularLanguage F cone ∈ PSPACE := (regularDecider h cone).mem_PSPACE

theorem regular_correct (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v)
    (hheights : ∀ c : active F u → ℝ, (∀ i, ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ) = 0) → ∀ j, c j = 0) :
    pair u v ∈ regularLanguage F cone ↔
      ∀ z ∈ FlatAffineCompleteComponentSamples.slice F u
        (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩),
        Function.Surjective (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ)
          (FlatAffineCompleteComponentSamples.source F u) (active F u) (direction F u) z) := by
  have HV : pair u v ∈ FlatAffineCompleteVertices.language F (parentCone F cone) := by
    change SquareSampleCompleteVertices.Valid (FlatAffinePowerSampleInput.input F (parentCone F cone))
      (pairFst (pair u v)) (pairSnd (pair u v))
    rw [pairFst_pair, pairSnd_pair]
    exact hv
  change (pair u v ∈ FlatAffineCompleteVertices.language F (parentCone F cone) ∧ pair u v ∉ singularLanguage F cone) ↔ _
  rw [and_iff_right HV, singular_correct F cone u v hv hheights]
  simp only [FlatAffineSingularSliceSamples.singular, Set.nonempty_def, Set.mem_ofPred_eq,
    not_exists, not_and, not_not]

end LeanCanny.Encoding.FlatAffineSliceRegularity
