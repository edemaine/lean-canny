/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullBlockRegularity
public import LeanCanny.Encoding.BoundedCriticalSampleBlockData

/-! # Data semantics of full-source block regularity

Candidate-record metadata must leave both the actual parent family and the
constructed source fixed. Snapshotting the source readers at the context
provides this transport without rewriting dependent coordinate types.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullBlockData
open LeanCanny.Algebra LeanCanny.ETR LeanCanny.ETR.ComplexCircuit BoundedFullWriter MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair pairFst pairSnd BoundedFullDirectionChoice.record
  BoundedFullGeometry.polynomial BoundedFullWriter.original BoundedFullWriter.size BoundedFullWriter.degree

noncomputable def rows {N : ℕ} (source : List Bool) (sourceDim radius offset free : ℕ)
    (direction : ℕ → ℤ) (parent : Fin N → ℝ) :=
  let F : BoundedFullBlockKernel.Inputs :=
    ⟨⟨fun _ => source, fun _ => sourceDim, fun _ => radius⟩, fun _ => offset, fun _ => free,
      fun _ => direction, fun _ => .falsum⟩
  CriticalKernel.finiteRows (BoundedFullBlockKernel.slice F [] (Formula.extend parent))
    (fun i => (direction i.val : ℝ))

def Good (P : Readers) (c source : List Bool) (sourceDim radius offset free : ℕ) (direction : ℕ → ℤ) : Prop :=
  ∀ p : BoundedFullCriticalSamples.Samples P c, ∀ y : Fin (free + 1) → ℝ,
    (∀ i, (rows source sourceDim radius offset free direction p.val i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (rows source sourceDim radius offset free direction p.val i).eval z) y).IsInvertible

theorem data_iff (P : Readers) (F : BoundedFullBlockKernel.Inputs) (c : List Bool) :
    BoundedFullBlockRegularity.Good P F c ↔ Good P c (F.source.source c) (F.source.dim c) (F.source.radius c)
      (F.offset c) (F.free c) (F.direction c) := by
  let Q : Readers := ⟨fun _ => F.source.source c, fun _ => F.source.dim c, fun _ => F.source.radius c⟩
  have ho : original Q [] = original F.source c := original_comp F.source (fun _ => c) []
  have hz : size Q [] = size F.source c := size_comp F.source (fun _ => c) []
  have hr (p : BoundedFullCriticalSamples.Samples P c) :
      BoundedFullBlockRegularity.originalRows P F c p =
        rows (F.source.source c) (F.source.dim c) (F.source.radius c) (F.offset c) (F.free c) (F.direction c) p.val := by
    unfold BoundedFullBlockRegularity.originalRows rows BoundedFullBlockKernel.slice BoundedFullBlockKernel.fullPolynomial
    change CriticalKernel.finiteRows
      (CoordinateBlockSpecialization.finite (Int.castRingHom ℝ) (Formula.extend p.val) (F.offset c) (F.free c + 1)
        (BoundedFullGeometry.polynomial (original F.source c) (size F.source c) (size F.source c) (F.source.radius c)))
      (fun i => (F.direction c i.val : ℝ)) =
      CriticalKernel.finiteRows
        (CoordinateBlockSpecialization.finite (Int.castRingHom ℝ) (Formula.extend p.val) (F.offset c) (F.free c + 1)
          (BoundedFullGeometry.polynomial (original Q []) (size Q []) (size Q []) (Q.radius [])))
        (fun i => (F.direction c i.val : ℝ))
    rw [ho, hz]
  unfold BoundedFullBlockRegularity.Good Good
  simp only [BoundedFullBlockKernel.dim, hr]

theorem data_comp_iff (P : Readers) (f : List Bool → List Bool) (F : BoundedFullBlockKernel.Inputs) (c : List Bool) :
    BoundedFullBlockRegularity.Good (P.comp f) F c ↔
      Good P (f c) (F.source.source c) (F.source.dim c) (F.source.radius c)
        (F.offset c) (F.free c) (F.direction c) := by
  rw [data_iff]
  constructor
  · intro h p
    have hp : ∀ j, (BoundedFullCriticalSamples.equations (P.comp f) c j).eval₂
        (Int.castRingHom ℝ) p.val = 0 := by
      intro j
      rw [BoundedCriticalSampleBlockData.equations_comp P f c]
      exact p.property j
    exact h ⟨p.val, hp⟩
  · intro h p
    have hp : ∀ j, (BoundedFullCriticalSamples.equations P (f c) j).eval₂
        (Int.castRingHom ℝ) p.val = 0 := by
      intro j
      rw [← BoundedCriticalSampleBlockData.equations_comp P f c]
      exact p.property j
    exact h ⟨p.val, hp⟩

end LeanCanny.Encoding.BoundedFullBlockData
