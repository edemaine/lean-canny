/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineBranchChoice
public import LeanCanny.Encoding.FlatAffineEndpointChildSamples

/-! # Native recursive child queries at computed branch sample points

The short branch descriptor computes its parent name. Native child selection
then retains that ancestry and recovers the actual current spatial point.
Regularity is required only for the child being sampled, not for the parent.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineBranchChildSamples
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointChildSamples (Controls original original_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def inputs (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (C : Controls) : NamedParentChildSelection.Inputs where
  parent := FlatAffineCurrentNamedParents.source F cone height
  source := F.source.comp original
  offset := C.offset
  dim := C.dim
  directionWidth := C.directionWidth
  direction := C.direction
  pivot := C.pivot

theorem access {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val))
    {C : Controls} (A : C.Access) : (inputs F cone height C).Access :=
  ⟨FlatAffineCurrentNamedParents.access h cone height hh, h.source.comp original_FP,
    A.offset, A.dim, A.directionWidth, A.direction, A.pivot, fun s => h.sourceArity (original s)⟩

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val))
    {C : Controls} (A : C.Access) : NamedParentChildSelection.language (inputs F cone height C) ∈ PSPACE :=
  NamedParentChildSelection.mem_PSPACE (access h cone height hh A)

theorem nextAccess {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val))
    {C : Controls} (A : C.Access) : NamedRationalParents.Access (NamedParentChildNext.next (inputs F cone height C)) :=
  NamedParentChildNext.access (access h cone height hh A)

theorem accepted_at_branch (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (C : Controls) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language F cone height)
    (y : Fin (C.dim (FlatAffineEndpointBranchLabels.source q)) → ℝ)
    (hy : ∀ i, (RationalParentChildParameters.originalRows (NamedParentChildSelection.generic (inputs F cone height C))
      (FlatAffineEndpointBranchLabels.source q) (FlatAffineBranchChoice.parent F cone height q hq).val i).eval y = 0)
    (hr : (fderiv ℝ (fun z => fun i => (RationalParentChildParameters.originalRows
      (NamedParentChildSelection.generic (inputs F cone height C)) (FlatAffineEndpointBranchLabels.source q)
      (FlatAffineBranchChoice.parent F cone height q hq).val i).eval z) y).IsInvertible) :
    ∃ x : NamedParentChildNext.Root (inputs F cone height C) (FlatAffineEndpointBranchLabels.source q),
      RationalParentChildParameters.decode (NamedParentChildSelection.generic (inputs F cone height C))
        (FlatAffineEndpointBranchLabels.source q) x.val = Fin.cons (FlatAffineBranchChoice.parent F cone height q hq).val y ∧
      (NamedParentChildNext.word (inputs F cone height C) (FlatAffineEndpointBranchLabels.source q) x).length ≤
        NamedParentChildNext.width (inputs F cone height C) (FlatAffineEndpointBranchLabels.source q) ∧
      pair (FlatAffineEndpointBranchLabels.source q) (NamedParentChildNext.word (inputs F cone height C) (FlatAffineEndpointBranchLabels.source q) x) ∈
        NamedRationalParents.language (NamedParentChildNext.next (inputs F cone height C)) :=
  NamedParentChildSamples.accepted_name (inputs F cone height C) (FlatAffineEndpointBranchLabels.source q)
    (FlatAffineBranchChoice.parent F cone height q hq) y hy hr

end LeanCanny.Encoding.FlatAffineBranchChildSamples
