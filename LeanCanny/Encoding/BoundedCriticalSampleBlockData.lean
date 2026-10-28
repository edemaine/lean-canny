/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBlockRegularity

/-! # Pointwise data semantics for actual-parent regularity queries

Query metadata changes the original readers' context without changing the
selected parent samples. The selected-record composition theorem transports
the parent equations; block regularity then depends only on the source data,
block controls, and decoded direction at the queried context.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleBlockData
open LeanCanny.Algebra LeanCanny.ETR LeanCanny.ETR.ComplexCircuit BoundedFullWriter MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair pairFst pairSnd BoundedFullDirectionChoice.record
  BoundedFullGeometry.polynomial BoundedFullWriter.original BoundedFullWriter.size BoundedFullWriter.degree
  BoundedCriticalSampleBlockScaling.original

noncomputable def rows {N : ℕ} (source : List Bool) (offset free : ℕ) (direction : ℕ → ℤ)
    (parent : Fin N → ℝ) :=
  CriticalKernel.finiteRows (BoundedCriticalSampleBlockScaling.original (TermView.term source) parent offset (free + 1))
    (fun i => (direction i.val : ℝ))

def Good (P : Readers) (c source : List Bool) (offset free : ℕ) (direction : ℕ → ℤ) : Prop :=
  ∀ p : BoundedFullCriticalSamples.Samples P c, ∀ y : Fin (free + 1) → ℝ,
    (∀ i, (rows source offset free direction p.val i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (rows source offset free direction p.val i).eval z) y).IsInvertible

theorem data_iff (P : Readers) (F : BlockKernel.Inputs) (c : List Bool) :
    BoundedCriticalSampleBlockRegularity.Good P F c ↔ Good P c (F.source c) (F.offset c) (F.free c) (F.direction c) := Iff.rfl

theorem equations_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) :
    BoundedFullCriticalSamples.equations (P.comp f) c = BoundedFullCriticalSamples.equations P (f c) := by
  have hp : BoundedFullCriticalSamples.polynomial (P.comp f) c =
      BoundedFullCriticalSamples.polynomial P (f c) := by
    unfold BoundedFullCriticalSamples.polynomial
    rw [original_comp, size_comp]
    rfl
  have hd : BoundedFullCriticalSamples.direction (P.comp f) c =
      BoundedFullCriticalSamples.direction P (f c) := by
    unfold BoundedFullCriticalSamples.direction
    rw [BoundedFullDirectionChoice.record_comp]
    exact BoundedFullDirectionQueries.direction_comp P (fun _ => BoundedFullDirectionChoice.record P (f c)) f c
  exact congrArg₂ (CriticalKernel.finiteRows (n := P.dim (f c) + 3)) hp
    (funext fun i => congrFun hd i.val)

def parentEquiv (P : Readers) (f : List Bool → List Bool) (c : List Bool) :
    BoundedFullCriticalSamples.Samples (P.comp f) c ≃ BoundedFullCriticalSamples.Samples P (f c) where
  toFun p := ⟨p.val, by
    intro j
    change (BoundedFullCriticalSamples.equations P (f c) j).eval₂ (Int.castRingHom ℝ) p.val = 0
    rw [← equations_comp P f c]
    exact p.property j⟩
  invFun p := ⟨p.val, by
    intro j
    change (BoundedFullCriticalSamples.equations (P.comp f) c j).eval₂ (Int.castRingHom ℝ) p.val = 0
    rw [equations_comp P f c]
    exact p.property j⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem data_comp_iff (P : Readers) (f : List Bool → List Bool) (F : BlockKernel.Inputs) (c : List Bool) :
    BoundedCriticalSampleBlockRegularity.Good (P.comp f) F c ↔
      Good P (f c) (F.source c) (F.offset c) (F.free c) (F.direction c) := by
  rw [data_iff]
  constructor
  · intro h p
    have hp : ∀ j, (BoundedFullCriticalSamples.equations (P.comp f) c j).eval₂
        (Int.castRingHom ℝ) p.val = 0 := by
      intro j
      rw [equations_comp P f c]
      exact p.property j
    exact h ⟨p.val, hp⟩
  · intro h p
    have hp : ∀ j, (BoundedFullCriticalSamples.equations P (f c) j).eval₂
        (Int.castRingHom ℝ) p.val = 0 := by
      intro j
      rw [← equations_comp P f c]
      exact p.property j
    exact h ⟨p.val, hp⟩

end LeanCanny.Encoding.BoundedCriticalSampleBlockData
