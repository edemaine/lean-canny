/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullBlockDirectionChoice
public import LeanCanny.Encoding.BoundedFullSampleChildParameters

/-! # Selected shared-source directions in the child parameter system

A leading fixed-width field aligns the selected free-direction record with
the full spatial vector. The pivot field is unused by the critical equations.
The native search is included in every child coefficient reader's space
bound. Accepted records give regularity of the original child critical
system and unique child parameters for all of its actual-parent roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleSelectedDirection
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open LeanCanny.ETR.ComplexCircuit BoundedFullWriter
open BoundedFullBlockDirectionChoice (Inputs width record Good)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair pairFst pairSnd record
  BoundedFullSampleBlockScaling.original BoundedFullSampleChildParameters.originalRows

noncomputable def padded (F : Inputs) (q : List Bool) : List Bool :=
  List.replicate (width F (pairFst q)) false ++ pairSnd q

theorem padded_FP {F : Inputs} (h : F.PolyTime) : padded F ∈ FP :=
  appendFn_mem_FP (((BoundedFullBlockDirectionChoice.width_unary h).comp pairFst_mem_FP).replicate_mem_FP false)
    pairSnd_mem_FP

theorem padded_succ (F : Inputs) (c r : List Bool) (i : ℕ) :
    FixedWidthQuery.coordinate (width F ∘ pairFst) (padded F) (pair c r) (i + 1) =
      FixedWidthQuery.coordinate (width F) (fun _ => r) c i := by
  have hd : (List.replicate (width F c) false ++ r).drop (width F c) = r := by
    simpa only [List.length_replicate] using @List.drop_left Bool (List.replicate (width F c) false) r
  simp only [FixedWidthQuery.coordinate, padded, Function.comp_apply, pairFst_pair, pairSnd_pair]
  rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (i * width F c), ← List.drop_drop, hd]

noncomputable def word (F : Inputs) (c : List Bool) : List Bool := padded F (pair c (record F c))

theorem word_evaluator {F : Inputs} (h : F.PolyTime)
    (htP : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c)
    (htS : ∀ c, (TermView.term (F.source.source c)).arity ≤ F.source.dim c) : SpaceFunction (word F) :=
  ((BoundedFullBlockDirectionChoice.evaluator h htP htS).withInput.postcompose (padded F) (padded_FP h)).congr
    (funext fun _ => rfl)

theorem word_length (F : Inputs) (c : List Bool) : (word F c).length = (F.free c + 1) * width F c := by
  simp only [word, padded, pairFst_pair, pairSnd_pair, List.length_append, List.length_replicate,
    BoundedFullBlockDirectionChoice.record_length, BoundedFullBlockDirectionChoice.recordLength]
  ring

noncomputable def child (F : Inputs) : BoundedFullSampleChildSource.Inputs where
  block := ⟨F.parent, F.source.comp pairFst, F.offset ∘ pairFst, fun u => F.free (pairFst u) + 1⟩
  directionWidth := width F ∘ pairFst
  direction := word F ∘ pairFst
  pivot _ := ⟨0, Nat.zero_lt_succ _⟩

theorem child_polyTime {F : Inputs} (h : F.PolyTime)
    (htP : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c)
    (htS : ∀ c, (TermView.term (F.source.source c)).arity ≤ F.source.dim c) : (child F).PolyTime :=
  ⟨⟨h.parent, h.source.comp pairFst_mem_FP, h.offset.comp pairFst_mem_FP,
      (h.free.comp pairFst_mem_FP).add (UnaryFn.const 1)⟩,
    (BoundedFullBlockDirectionChoice.width_unary h).comp pairFst_mem_FP,
    (word_evaluator h htP htS).precompose pairFst pairFst_mem_FP, BinaryFn.const 0,
    htP, fun u => htS (pairFst u)⟩

theorem original_eq (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :
    BoundedFullSampleBlockScaling.original (child F).block u p =
      BoundedFullBlockDirectionChoice.slice F (pairFst u) p := by
  unfold BoundedFullSampleBlockScaling.original BoundedFullBlockDirectionChoice.slice
    BoundedFullBlockKernel.slice BoundedFullBlockKernel.fullPolynomial
  change CoordinateBlockSpecialization.finite (Int.castRingHom ℝ) (Formula.extend p.val)
    (F.offset (pairFst u)) (F.free (pairFst u) + 1)
    (BoundedFullGeometry.polynomial (original (F.source.comp pairFst) u)
      (size (F.source.comp pairFst) u) (size (F.source.comp pairFst) u) (F.source.radius (pairFst u))) = _
  rw [original_comp, size_comp]
  rfl

theorem direction_succ (F : Inputs) (u : List Bool) (i : Fin (F.free (pairFst u))) :
    BoundedFullSampleBlockCriticalSource.direction (child F).block.dim (child F).directionWidth (child F).direction u i.succ =
      FixedWidthQuery.coordinate (width F) (record F) (pairFst u) i.val := by
  have H := padded_succ F (pairFst u) (record F (pairFst u)) i.val
  have hi : i.val + 1 < F.free (pairFst u) + 1 := Nat.add_lt_add_right i.isLt 1
  simpa only [BoundedFullSampleBlockCriticalSource.direction, child, FixedWidthQuery.entry, Fin.val_succ,
    ite_eq_left hi, FixedWidthQuery.coordinate, Function.comp_apply, word, pairFst_pair, pairSnd_pair] using H

theorem rows_eq (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :
    BoundedFullSampleChildParameters.originalRows (child F) u p =
      BoundedFullBlockRegularity.originalRows F.parent (BoundedFullBlockDirectionChoice.selected F) (pairFst u) p := by
  unfold BoundedFullSampleChildParameters.originalRows
  rw [original_eq]
  change ProjectionCriticalFamily.spatialEquation (BoundedFullBlockDirectionChoice.slice F (pairFst u) p)
    (0 : Fin (F.free (pairFst u) + 1))
    (fun j => (BoundedFullSampleBlockCriticalSource.direction (child F).block.dim (child F).directionWidth
      (child F).direction u j : ℝ)) =
    CriticalKernel.finiteRows (BoundedFullBlockDirectionChoice.slice F (pairFst u) p)
      (fun j => (BoundedFullBlockDirectionChoice.direction F (pairFst u) (record F (pairFst u)) j.val : ℝ))
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [ProjectionCriticalFamily.spatialEquation, ite_true, CriticalKernel.finiteRows, Fin.cons_zero]
  · simp only [ProjectionCriticalFamily.spatialEquation, Fin.succ_ne_zero, ite_false, CriticalKernel.finiteRows,
      Fin.cons_succ, direction_succ, BoundedFullBlockDirectionChoice.direction, Int.cast_natCast,
      FixedWidthQuery.coordinate]
    rfl

theorem critical_regular (F : Inputs) (u : List Bool) (hg : Good F (pairFst u) (record F (pairFst u)))
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (y : Fin (F.free (pairFst u) + 1) → ℝ)
    (hy : ∀ i, (BoundedFullSampleChildParameters.originalRows (child F) u p i).eval y = 0) :
    (fderiv ℝ (fun z => fun i => (BoundedFullSampleChildParameters.originalRows (child F) u p i).eval z) y).IsInvertible := by
  rw [rows_eq] at hy ⊢
  exact ((BoundedFullBlockDirectionChoice.selected_good_iff F (pairFst u)).mpr hg) p y hy

theorem sample_complete (F : Inputs) (u : List Bool) (hg : Good F (pairFst u) (record F (pairFst u)))
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (y : Fin (F.free (pairFst u) + 1) → ℝ)
    (hy : ∀ i, (BoundedFullSampleChildParameters.originalRows (child F) u p i).eval y = 0) :
    ∃! theta : BoundedFullSampleChildParameters.RegularParameters (child F) u,
      BoundedFullSampleChildParameters.decode (child F) u theta.val =
        Fin.cons (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val y :=
  BoundedFullSampleChildParameters.sample_complete (child F) u p y hy (critical_regular F u hg p y hy)

theorem sample_complete_of_regular (F : Inputs) (u : List Bool)
    (hfit : F.offset (pairFst u) + (F.free (pairFst u) + 1) ≤ F.source.dim (pairFst u) + 4)
    (hregular : BoundedFullBlockDirectionChoice.SliceRegular F (pairFst u))
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (y : Fin (F.free (pairFst u) + 1) → ℝ)
    (hy : ∀ i, (BoundedFullSampleChildParameters.originalRows (child F) u p i).eval y = 0) :
    ∃! theta : BoundedFullSampleChildParameters.RegularParameters (child F) u,
      BoundedFullSampleChildParameters.decode (child F) u theta.val =
        Fin.cons (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val y :=
  sample_complete F u (BoundedFullBlockDirectionChoice.record_good F (pairFst u) hfit hregular) p y hy

/-- The initial whole-source direction needs no supplied regularity or success
certificate; the constructed source supplies it. -/
theorem whole_sample_complete (P S : Readers) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples P (pairFst u)) (y : Fin (S.dim (pairFst u) + 4) → ℝ)
    (hy : ∀ i, (BoundedFullSampleChildParameters.originalRows (child (BoundedFullBlockDirectionChoice.whole P S)) u p i).eval y = 0) :
    ∃! theta : BoundedFullSampleChildParameters.RegularParameters (child (BoundedFullBlockDirectionChoice.whole P S)) u,
      BoundedFullSampleChildParameters.decode (child (BoundedFullBlockDirectionChoice.whole P S)) u theta.val =
        Fin.cons (BoundedCriticalSampleLabels.parameter P (pairFst u) p).val y :=
  sample_complete _ u (BoundedFullBlockDirectionChoice.whole_record_good P S (pairFst u)) p y hy

end LeanCanny.Encoding.BoundedFullSampleSelectedDirection
