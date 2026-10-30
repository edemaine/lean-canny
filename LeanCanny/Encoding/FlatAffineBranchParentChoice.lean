/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineLastHeightRow
public import LeanCanny.Encoding.FlatAffineBranchPrefixChoice
public import LeanCanny.Encoding.FlatAffineShiftedRootGeometry

/-! # Native branch ancestor words name the exact original parent sampler -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineBranchParentChoice
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineEndpointBranchLabels (source)
open FlatAffineJointPrefixChoice (original)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineBranchPrefixChoice.value FlatAffineBranchChoice.value
  FlatAffineJointPrefixChoice.value

noncomputable def value (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) : List Bool → List Bool :=
  FlatAffineBranchPrefixChoice.value (next F) C (FlatAffineLastHeightRow.row F h)

noncomputable def currentAt (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (s q : List Bool) :
    Fin (FlatAffineFullSourcePositive.count (next F) (original s)) → ℝ :=
  FlatAffineEndpointRankWord.currentValue (next F) C (FlatAffineLastHeightRow.row F h) s
    (FlatAffineBranchChoice.value (next F) C (FlatAffineLastHeightRow.row F h) q)

noncomputable def current (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) :
    Fin (FlatAffineFullSourcePositive.count (next F) (original (source q))) → ℝ := currentAt F C h (source q) q

noncomputable def point (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F) (s w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F C) original) s w) :
    Fin (FlatAffineFullSourcePositive.count F (original s)) → ℝ :=
  (SquareSampleCompleteVertices.candidate (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F C) original) s w hw).val

noncomputable def prefixProjection (F : Inputs) (u : List Bool) :
    Fin (FlatAffineFullSourcePositive.count F u) → Fin (FlatAffineFullSourcePositive.count (next F) u) :=
  FlatAffinePowerPrefix.projection (next F) F.depth (fun u => by change F.depth u ≤ F.depth u + 1; omega) u

theorem evaluator {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) : SpaceFunction (value F C h) :=
  FlatAffineBranchPrefixChoice.evaluator (FlatAffineCompleteRootStages.access hF (hF.depth.add (UnaryFn.const 1)))
    C (FlatAffineLastHeightRow.row F h) (FlatAffineLastHeightRow.row_unary hF h hh)

theorem value_valid (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language (next F) C (FlatAffineLastHeightRow.row F h)) :
    SquareSampleCompleteVertices.Valid
      (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F (FlatAffineLastHeightRow.parentCone F C)) original)
      (source q) (value F C h q) := by
  rw [← FlatAffineLastHeightRow.target_eq F C h]
  exact FlatAffineBranchPrefixChoice.value_valid (next F) C (FlatAffineLastHeightRow.row F h) q hq
    (FlatAffineLastHeightRow.ordinary F h (original (source q)))

theorem value_point (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language (next F) C (FlatAffineLastHeightRow.row F h)) :
    point F (FlatAffineLastHeightRow.parentCone F C) (source q) (value F C h q) (value_valid F C h q hq) =
      current F C h q ∘ prefixProjection F (original (source q)) := by
  have HP := FlatAffineBranchPrefixChoice.value_point (next F) C (FlatAffineLastHeightRow.row F h) q hq
    (FlatAffineLastHeightRow.ordinary F h (original (source q)))
  have HD : FlatAffineShiftPrefixInput.depth (next F) (FlatAffineLastHeightRow.row F h) = F.depth :=
    funext (FlatAffineLastHeightRow.depth_eq F h)
  unfold FlatAffineJointPrefixChoice.target FlatAffineShiftPrefixInput.input FlatAffineShiftPrefixInput.inputs at HP
  change point (FlatAffineShiftPrefixInput.inputs (next F) (FlatAffineLastHeightRow.row F h))
    (FlatAffineShiftPrefixInput.cone (next F) C (FlatAffineLastHeightRow.row F h)) (source q)
    (value F C h q) _ = current F C h q ∘ FlatAffinePowerPrefix.projection (next F)
    (FlatAffineShiftPrefixInput.depth (next F) (FlatAffineLastHeightRow.row F h))
    (FlatAffineShiftPrefixInput.depth_le (next F) (FlatAffineLastHeightRow.row F h)) (original (source q)) at HP
  unfold FlatAffineShiftPrefixInput.inputs at HP
  have transport (d : List Bool → ℕ) (hd : ∀ u, d u ≤ (next F).depth u)
      (CG : FlatAffinePowerPositive.ConeCertificate (FlatAffineCompleteRootStages.truncate (next F) d))
      (hv : SquareSampleCompleteVertices.Valid
        (SquareSampleInput.comp (FlatAffinePowerSampleInput.input (FlatAffineCompleteRootStages.truncate (next F) d) CG) original)
        (source q) (value F C h q))
      (he : point (FlatAffineCompleteRootStages.truncate (next F) d) CG (source q) (value F C h q) hv =
        current F C h q ∘ FlatAffinePowerPrefix.projection (next F) d hd (original (source q)))
      (hdEq : d = F.depth) :
      point F (FlatAffineLastHeightRow.parentCone F C) (source q) (value F C h q) (value_valid F C h q hq) =
        current F C h q ∘ prefixProjection F (original (source q)) := by
    subst d
    exact he
  exact transport _ _ _ _ HP HD

noncomputable def decode (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F) (s w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F C) original) s w) :
    FlatAffinePowerSampleInput.OriginalRoots F (original s) :=
  FlatAffinePowerSampleInput.originalRootsEquiv F (original s)
    ⟨point F C s w hw,
      (SquareSampleCompleteVertices.candidate
        (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F C) original) s w hw).property⟩

noncomputable def parent (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language (next F) C (FlatAffineLastHeightRow.row F h)) :
    FlatAffinePowerSampleInput.OriginalRoots F (original (source q)) :=
  decode F (FlatAffineLastHeightRow.parentCone F C) (source q) (value F C h q) (value_valid F C h q hq)

theorem decode_injective (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F) (s w v : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F C) original) s w)
    (hv : SquareSampleCompleteVertices.Valid (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F C) original) s v)
    (he : decode F C s w hw = decode F C s v hv) : w = v := by
  have HE := (FlatAffinePowerSampleInput.originalRootsEquiv F (original s)).injective he
  exact SquareSampleCompleteVertices.candidate_injective _ s w v hw hv
    (Subtype.ext (congrArg Subtype.val HE))

theorem parent_val (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language (next F) C (FlatAffineLastHeightRow.row F h)) :
    (parent F C h q hq).val = FlatAffineShiftedSlice.ancestorPoint F (original (source q)) (current F C h q) := by
  let u := original (source q)
  let D := FlatAffinePowerControls.degree F u
  let w := point F (FlatAffineLastHeightRow.parentCone F C) (source q) (value F C h q) (value_valid F C h q hq)
  let z := current F C h q
  have HP := value_point F C h q hq
  have HR : w ∘ Fin.castSucc = (z ∘ Fin.castSucc) ∘
      FlatAffinePowerTower.prefixIndex (n := arity F u) (k := F.depth u + 1) (Nat.le_succ (F.depth u)) := by
    funext i
    have HE := FlatAffinePowerPrefix.projection_old (next F) F.depth
      (fun u => by change F.depth u ≤ F.depth u + 1; omega) u i
    exact (congrFun HP i.castSucc).trans (congrArg z HE)
  change FlatAffinePowerTower.powerPoint D (w ∘ Fin.castSucc) = _
  exact (congrArg (FlatAffinePowerTower.powerPoint D) HR).trans
    (FlatAffinePowerTower.powerPoint_prefix (Nat.le_succ (F.depth u)) D (z ∘ Fin.castSucc))

theorem value_valid_at (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q s : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language (next F) C (FlatAffineLastHeightRow.row F h)) (hs : source q = s) :
    SquareSampleCompleteVertices.Valid
      (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F (FlatAffineLastHeightRow.parentCone F C)) original)
      s (value F C h q) := hs ▸ value_valid F C h q hq

theorem parent_val_at (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q s : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language (next F) C (FlatAffineLastHeightRow.row F h)) (hs : source q = s) :
    (decode F (FlatAffineLastHeightRow.parentCone F C) s (value F C h q) (value_valid_at F C h q s hq hs)).val =
      FlatAffineShiftedSlice.ancestorPoint F (original s) (currentAt F C h s q) := by
  have HP := parent_val F C h q hq
  change (decode F (FlatAffineLastHeightRow.parentCone F C) (source q) (value F C h q) _).val =
    FlatAffineShiftedSlice.ancestorPoint F (original (source q)) (currentAt F C h (source q) q) at HP
  have transport (r : List Bool)
      (hv : SquareSampleCompleteVertices.Valid
        (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F (FlatAffineLastHeightRow.parentCone F C)) original) r (value F C h q))
      (he : (decode F (FlatAffineLastHeightRow.parentCone F C) r (value F C h q) hv).val =
        FlatAffineShiftedSlice.ancestorPoint F (original r) (currentAt F C h r q)) (hr : r = s) :
      (decode F (FlatAffineLastHeightRow.parentCone F C) s (value F C h q) (value_valid_at F C h q s hq hs)).val =
        FlatAffineShiftedSlice.ancestorPoint F (original s) (currentAt F C h s q) := by
    subst r
    exact he
  exact transport _ _ HP hs

end LeanCanny.Encoding.FlatAffineBranchParentChoice
