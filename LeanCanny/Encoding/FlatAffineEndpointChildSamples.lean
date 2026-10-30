/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointNamedParents
public import LeanCanny.Encoding.NamedParentChildSamples

/-! # Native regular child samples over actual endpoint markers

Original full-source readers and explicit block/direction controls supply the
child equations. The endpoint's complete joint label is its ancestry name.
Accepted child names retain that parent, have the derived length bound, and
decode to the original block-critical point over the exact marker parameter.
The original endpoint point itself need not be regular.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointChildSamples
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

structure Controls where
  offset : List Bool → ℕ
  dim : List Bool → ℕ
  directionWidth : List Bool → ℕ
  direction : List Bool → List Bool
  pivot : (s : List Bool) → Fin (dim s)

structure Controls.Access (C : Controls) : Prop where
  offset : BinaryFn C.offset
  dim : UnaryFn C.dim
  directionWidth : UnaryFn C.directionWidth
  direction : SpaceFunction C.direction
  pivot : BinaryFn (fun s => (C.pivot s).val)

def original (s : List Bool) : List Bool := pairFst (pairFst s)
theorem original_FP : original ∈ FP := by polytime [original]

noncomputable def inputs (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (C : Controls) : NamedParentChildSelection.Inputs where
  parent := FlatAffineEndpointNamedParents.source F cone height
  source := F.source.comp original
  offset := C.offset
  dim := C.dim
  directionWidth := C.directionWidth
  direction := C.direction
  pivot := C.pivot

theorem access {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val))
    {C : Controls} (A : C.Access) : (inputs F cone height C).Access :=
  ⟨FlatAffineEndpointNamedParents.access h cone height hh, h.source.comp original_FP,
    A.offset, A.dim, A.directionWidth, A.direction, A.pivot, fun s => h.sourceArity (original s)⟩

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val))
    {C : Controls} (A : C.Access) : NamedParentChildSelection.language (inputs F cone height C) ∈ PSPACE :=
  NamedParentChildSelection.mem_PSPACE (access h cone height hh A)

theorem nextAccess {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val))
    {C : Controls} (A : C.Access) : NamedRationalParents.Access (NamedParentChildNext.next (inputs F cone height C)) :=
  NamedParentChildNext.access (access h cone height hh A)

theorem accepted_at_marker (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (C : Controls) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language F cone height)
    (y : Fin (C.dim (FlatAffineEndpointMarkers.source q)) → ℝ)
    (hy : ∀ i, (RationalParentChildParameters.originalRows (NamedParentChildSelection.generic (inputs F cone height C))
      (FlatAffineEndpointMarkers.source q) (FlatAffineEndpointNamedParents.markerRoot F cone height q hq).val i).eval y = 0)
    (hr : (fderiv ℝ (fun z => fun i => (RationalParentChildParameters.originalRows
      (NamedParentChildSelection.generic (inputs F cone height C)) (FlatAffineEndpointMarkers.source q)
      (FlatAffineEndpointNamedParents.markerRoot F cone height q hq).val i).eval z) y).IsInvertible) :
    ∃ x : NamedParentChildNext.Root (inputs F cone height C) (FlatAffineEndpointMarkers.source q),
      RationalParentChildParameters.decode (NamedParentChildSelection.generic (inputs F cone height C))
        (FlatAffineEndpointMarkers.source q) x.val = Fin.cons (FlatAffineEndpointNamedParents.markerRoot F cone height q hq).val y ∧
      (NamedParentChildNext.word (inputs F cone height C) (FlatAffineEndpointMarkers.source q) x).length ≤
        NamedParentChildNext.width (inputs F cone height C) (FlatAffineEndpointMarkers.source q) ∧
      pair (FlatAffineEndpointMarkers.source q) (NamedParentChildNext.word (inputs F cone height C) (FlatAffineEndpointMarkers.source q) x) ∈
        NamedRationalParents.language (NamedParentChildNext.next (inputs F cone height C)) :=
  NamedParentChildSamples.accepted_name (inputs F cone height C) (FlatAffineEndpointMarkers.source q)
    (FlatAffineEndpointNamedParents.markerRoot F cone height q hq) y hy hr

end LeanCanny.Encoding.FlatAffineEndpointChildSamples
