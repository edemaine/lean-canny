/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineCompleteChildSamples
public import LeanCanny.Encoding.SquareSampleCompleteCoordinateSign

/-! # Native selection of zero-objective critical children

The original objective multiplier vanishes exactly when its odd-power
coordinate vanishes. The complete sampler and its native sign reader thus
retain every singular slice point with its checked ancestry.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSingularChildLabels
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next newest)
open FlatAffineCompleteChildLabels (parentCone)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def objective (F : Inputs) (u : List Bool) : Fin (FlatAffineFullSourcePositive.count (next F) u) :=
  (FlatAffinePowerTower.multiplier (n := arity F u) ⟨F.depth u, Nat.lt_succ_self _⟩ 0).castSucc

theorem objective_unary {F : Inputs} (h : F.Access) : UnaryFn (fun u => (objective F u).val) := by
  apply ((FlatAffineFullSourceTower.stageWidth_unary h).mul h.depth |>.add
    (FlatAffineFullSourceTower.arity_unary h)).of_eq
  intro u
  change FlatAffineFullSourceTower.stageWidth F u * F.depth u + arity F u =
    (arity F u + 0) + FlatAffineFullSourceTower.stageWidth F u * F.depth u
  omega

lemma objective_zero_iff (F : Inputs) (u : List Bool)
    (z : {z : Fin (FlatAffineFullSourcePositive.count (next F) u) → ℝ //
      ∀ i, (FlatAffinePowerPositive.system (next F) u i).eval₂ (Int.castRingHom ℝ) z = 0}) :
    newest F u (FlatAffinePowerSampleInput.originalRootsEquiv (next F) u z).val (Sum.inr 0) = 0 ↔
      z.val (objective F u) = 0 := by
  have HI : TriangularPolynomialRows.block (FlatAffineFullSourceTower.stageWidth F u) (F.depth u)
      (F.depth u + 1) (by omega) (FlatAffineCriticalTower.blockEquiv (arity F u) (Sum.inr 0)) =
      FlatAffinePowerTower.multiplier (n := arity F u) ⟨F.depth u, Nat.lt_succ_self _⟩ 0 :=
    (FlatAffinePowerTower.row_index_eq ⟨F.depth u, Nat.lt_succ_self _⟩ (Sum.inr 0)).symm
  have HE := congrArg (FlatAffinePowerTower.powerPoint (n := arity F u) (k := F.depth u + 1)
    (FlatAffinePowerControls.degree (next F) u) (z.val ∘ Fin.castSucc)) HI
  have HV : newest F u (FlatAffinePowerSampleInput.originalRootsEquiv (next F) u z).val (Sum.inr 0) =
      z.val (objective F u) ^ (FlatAffinePowerControls.degree (next F) u - 1) :=
    HE.trans (FlatAffinePowerTower.powerPoint_multiplier (FlatAffinePowerControls.degree (next F) u)
      (z.val ∘ Fin.castSucc) ⟨F.depth u, Nat.lt_succ_self _⟩ 0)
  rw [HV]
  exact pow_eq_zero_iff (FlatAffinePowerRowReaders.power_ne_zero (next F) u)

noncomputable def query (F : Inputs) (q : List Bool) : List Bool :=
  pair (pair (pairFst q) (pairFst (pairSnd q))) (BinaryNatCode.encode (objective F (pairFst q)).val)

theorem query_FP {F : Inputs} (h : F.Access) : query F ∈ FP :=
  mem_FP_pair (mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))
    (BinaryFn.ofUnary ((objective_unary h).comp pairFst_mem_FP)).bits_mem_FP

noncomputable def value (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) : List Bool → List Bool :=
  SquareSampleCompleteCoordinateSign.value (FlatAffinePowerSampleInput.input (next F) cone) ∘ query F

theorem evaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    SpaceFunction (value F cone) :=
  (SquareSampleCompleteCoordinateSign.evaluator (FlatAffinePowerSampleInput.access (FlatAffineCompleteChildLabels.nextAccess h) cone)).precompose
    (query F) (query_FP h)

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) : Language :=
  {q | q ∈ FlatAffineCompleteChildLabels.language F cone ∧ value F cone q = InfinitesimalSign.encode 0}

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    SpaceDecider (language F cone) := by
  have V := (FlatAffineCompleteChildLabels.decider h cone).flagEvaluator
  have E := (evaluator h cone).postcompose (fun z => [decide (z = InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP (InfinitesimalSign.encode 0))).flag_mem_FP
  apply (V.andFlags E).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq, Function.comp_apply]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    language F cone ∈ PSPACE := (decider h cone).mem_PSPACE

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) (u w v : List Bool)
    (hw : FlatAffineCompleteVertices.Valid (next F) cone u w) :
    pair u (pair w v) ∈ language F cone ↔
      pair u (pair w v) ∈ FlatAffineCompleteChildLabels.language F cone ∧
      newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨w, hw⟩).val (Sum.inr 0) = 0 := by
  have H : query F (pair u (pair w v)) = pair (pair u w) (BinaryNatCode.encode (objective F u).val) := by
    unfold query
    rw [pairFst_pair, pairSnd_pair, pairFst_pair]
  simp only [language, Set.mem_ofPred_eq, value, Function.comp_apply, H,
    SquareSampleCompleteCoordinateSign.packet _ u w hw (objective F u), SquareSampleTestSign.encode_eq_iff,
    sign_eq_zero_iff]
  exact and_congr_right (fun _ => (objective_zero_iff F u
    (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input (next F) cone) u w hw)).symm)

theorem singular_accepted (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v)
    (hheights : ∀ c : FlatAffineCompleteComponentSamples.active F u → ℝ,
      (∀ i, ∑ j : FlatAffineCompleteComponentSamples.active F u,
        c j * (FlatAffineCompleteComponentSamples.direction F u j.val.succ i : ℝ) = 0) → ∀ j, c j = 0)
    (z : Fin (arity F u) → ℝ)
    (hz : z ∈ FlatAffineSingularSliceSamples.singular F u
      (FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩)) :
    ∃ w : {w : List Bool // FlatAffineCompleteVertices.Valid (next F) cone u w},
      pair u (pair w.val v) ∈ language F cone ∧
      newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u w).val ∘ Sum.inl = z := by
  obtain ⟨w, ha, he, hmu⟩ := FlatAffineCompleteChildSamples.singular_accepted F cone u v hv hheights z hz
  exact ⟨w, (packet F cone u w.val v w.property).mpr ⟨ha, hmu⟩, he⟩

end LeanCanny.Encoding.FlatAffineSingularChildLabels
