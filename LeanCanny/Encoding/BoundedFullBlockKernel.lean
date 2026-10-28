/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexSharedKernel
public import LeanCanny.ETR.ComplexCircuitBlock
public import LeanCanny.Encoding.BoundedFullGeometry
public import LeanCanny.Algebra.CoordinateBlockSpecialization

/-! # Native block kernels of the constructed full regular source

The actual shared source program is reindexed and differentiated directly.
Its binary powers are never expanded into term syntax. Frozen-block semantics
retain the source's pure-power leading part whenever the free block lies
inside its geometric coordinates. Slice regularity is a separate obligation.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullBlockKernel
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open LeanCanny.ETR.ComplexCircuit BoundedFullWriter MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Inputs where
  source : Readers
  offset : List Bool → ℕ
  free : List Bool → ℕ
  direction : List Bool → ℕ → ℤ
  condition : List Bool → Formula

structure Inputs.PolyTime (F : Inputs) : Prop where
  source : F.source.PolyTime
  offset : BinaryFn F.offset
  free : UnaryFn F.free
  direction : (fun q => (Term.const (-F.direction (pairFst q) (pairSnd q).length)).toData.toBits) ∈ FP
  condition : (fun c => (F.condition c).encode) ∈ FP

def dim (F : Inputs) (c : List Bool) : ℕ := F.free c + 1
noncomputable def start (F : Inputs) (c : List Bool) : ℕ := BoundedFullWriter.start F.source c + dim F c

noncomputable def native (F : Inputs) : SharedKernel.Inputs where
  start := start F
  free := F.free
  program c := CircuitBlock.program (BoundedFullWriter.start F.source c) (F.offset c) (dim F c) (start F c)
    (BoundedFullWriter.program F.source c)
  output c := CircuitBlock.output (BoundedFullWriter.start F.source c) (F.offset c) (dim F c) (start F c)
    (BoundedFullWriter.output F.source c)
  direction := F.direction
  condition := F.condition

theorem dim_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (dim F) := h.free.add (UnaryFn.const 1)
theorem start_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (start F) :=
  (BoundedFullWriter.start_unary h.source).add (dim_unary h)

theorem native_polyTime {F : Inputs} (h : F.PolyTime) : (native F).PolyTime := by
  refine ⟨start_unary h, h.free, ?_, ?_, ?_, h.direction, h.condition⟩
  · exact (BoundedFullWriter.length_unary h.source).of_eq
      (fun c => (CircuitBlock.program_length _ _ _ _ _).symm)
  · exact CircuitBlock.output_unary (BoundedFullWriter.start_unary h.source) h.offset (dim_unary h)
      (start_unary h) (BoundedFullWriter.output_unary h.source)
  · exact CircuitBlock.encode_mem_FP (BoundedFullWriter.start_unary h.source) h.offset (dim_unary h)
      (start_unary h) (BoundedFullWriter.encode_mem_FP h.source)

theorem native_valid (F : Inputs) : (native F).Valid := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · exact CircuitBlock.wellFormed _ _ _ _ _ (BoundedFullWriter.wellFormed F.source c) le_rfl
  · exact CircuitBlock.output_lt _ _ _ _ _ _ le_rfl (BoundedFullWriter.output_lt F.source c)

noncomputable def fullPolynomial (F : Inputs) (c : List Bool) : MvPolynomial (Fin (F.source.dim c + 4)) ℤ :=
  BoundedFullGeometry.polynomial (original F.source c) (size F.source c) (size F.source c) (F.source.radius c)

theorem native_polynomial_eq (F : Inputs) (c : List Bool)
    (ht : (TermView.term (F.source.source c)).arity ≤ F.source.dim c) :
    SharedKernel.polynomial (native F) c = CircuitBlock.substitution (F.offset c) (dim F c)
      (rename Fin.val (fullPolynomial F c)) := by
  have H := CircuitBlock.symbolic_output (BoundedFullWriter.start F.source c) (F.offset c) (dim F c)
    (start F c) (BoundedFullWriter.output F.source c) (BoundedFullWriter.program F.source c)
    (BoundedFullWriter.wellFormed F.source c) le_rfl (BoundedFullWriter.output_lt F.source c)
  rw [BoundedFullGeometry.source_identity F.source c ht] at H
  exact H

noncomputable def slice (F : Inputs) (c : List Bool) (frozen : ℕ → ℝ) : MvPolynomial (Fin (dim F c)) ℝ :=
  CoordinateBlockSpecialization.finite (Int.castRingHom ℝ) frozen (F.offset c) (dim F c) (fullPolynomial F c)

theorem specialize_block {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (frozen : ℕ → ℝ) (offset dim : ℕ) :
    FreeCoordinateSpecialization.specialize (n := dim) (Int.castRingHom ℝ) frozen
      (CircuitBlock.substitution offset dim (rename Fin.val p)) =
        CoordinateBlockSpecialization.finite (Int.castRingHom ℝ) frozen offset dim p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [CircuitBlock.substitution, FreeCoordinateSpecialization.specialize,
      CoordinateBlockSpecialization.finite]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    rw [rename_X, CoordinateBlockSpecialization.finite, eval₂Hom_X']
    change FreeCoordinateSpecialization.specialize (n := dim) (Int.castRingHom ℝ) frozen
      (rename (CircuitBlock.input offset dim) (X i.val)) =
        CoordinateBlockSpecialization.coordinate frozen offset dim i.val
    rw [rename_X]
    by_cases hi : offset ≤ i.val ∧ i.val < offset + dim
    · have hh : i.val - offset < dim := by omega
      rw [CircuitBlock.input, ite_eq_left hi, FreeCoordinateSpecialization.specialize, eval₂Hom_X',
        dite_eq_left hh, CoordinateBlockSpecialization.coordinate, dite_eq_left hi]
    · have hh : ¬dim + i.val < dim := by omega
      rw [CircuitBlock.input_frozen _ _ _ hi, FreeCoordinateSpecialization.specialize, eval₂Hom_X',
        dite_eq_right hh, Nat.add_sub_cancel_left, CoordinateBlockSpecialization.coordinate, dite_eq_right hi]

theorem native_slice_eq (F : Inputs) (c : List Bool) (x : ℕ → ℝ)
    (ht : (TermView.term (F.source.source c)).arity ≤ F.source.dim c) :
    SharedKernel.slice (native F) c x = slice F c (fun i => x (dim F c + i)) := by
  unfold SharedKernel.slice CriticalKernel.realSlice
  rw [native_polynomial_eq F c ht]
  exact specialize_block _ _ _ _

theorem slice_congr (F : Inputs) (c : List Bool) (frozen parent : ℕ → ℝ)
    (h : ∀ i < F.source.dim c + 4, frozen i = parent i) : slice F c frozen = slice F c parent :=
  CoordinateBlockSpecialization.finite_congr _ _ _ _ _ _ h

theorem native_slice_parent {N : ℕ} (F : Inputs) (c : List Bool) (x : ℕ → ℝ) (parent : Fin N → ℝ)
    (ht : (TermView.term (F.source.source c)).arity ≤ F.source.dim c)
    (hp : ∀ i < BoundedFullWriter.start F.source c, x (dim F c + i) = Formula.extend parent i) :
    SharedKernel.slice (native F) c x = slice F c (Formula.extend parent) := by
  rw [native_slice_eq F c x ht]
  apply slice_congr
  intro i hi
  exact hp i (hi.trans_le (Nat.le_max_right _ _))

noncomputable def rows (F : Inputs) (c : List Bool) (x : ℕ → ℝ) :=
  CriticalKernel.finiteRows (slice F c (fun i => x (dim F c + i))) (fun i => (F.direction c i.val : ℝ))

def Regular (F : Inputs) (c : List Bool) : Prop :=
  ∀ x : ℕ → ℝ, (F.condition c).Holds x →
    (∀ i, (rows F c x i).eval (fun j => x j.val) = 0) →
      (fderiv ℝ (fun y => fun i => (rows F c x i).eval y) (fun j => x j.val)).IsInvertible

theorem regular_iff (F : Inputs) (c : List Bool)
    (ht : (TermView.term (F.source.source c)).arity ≤ F.source.dim c) :
    SharedKernel.Regular (native F) c ↔ Regular F c := by
  unfold SharedKernel.Regular Regular
  simp only [SharedKernel.rows, native_slice_eq F c _ ht]
  rfl

theorem evaluator {F : Inputs} (h : F.PolyTime)
    (ht : ∀ c, (TermView.term (F.source.source c)).arity ≤ F.source.dim c) :
    SpaceFunction (fun c => [decide (Regular F c)]) := by
  apply (SharedKernel.evaluator (native_polyTime h) (native_valid F)).congr
  funext c
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, regular_iff F c (ht c)]

noncomputable def fullLower (F : Inputs) (c : List Bool) : MvPolynomial (Fin (F.source.dim c + 4)) ℤ :=
  rename (BoundedFullGeometry.inputIndex (F.source.dim c + 3))
    (IntegerRegularSource.lower
      (BoundedRegularSource.lower (original F.source c) (size F.source c) (size F.source c) (F.source.radius c))
      (degree F.source c)
      (BoundedRegularSource.sourceMassExponent (F.source.dim c) (size F.source c) (size F.source c) (F.source.radius c)))

noncomputable def fullLeading (F : Inputs) (c : List Bool) : ℤ :=
  IntegerRegularSource.leading (F.source.dim c + 3) 1 (degree F.source c)
    (BoundedRegularSource.sourceMassExponent (F.source.dim c) (size F.source c) (size F.source c) (F.source.radius c))

theorem full_polynomial_eq (F : Inputs) (c : List Bool) : fullPolynomial F c =
    FermatCriticalHomogenization.polynomial (fullLower F c) (fullLeading F c) (degree F.source c) :=
  BoundedFullGeometry.polynomial_eq _ _ _ _

theorem fullLower_degree (F : Inputs) (c : List Bool) : (fullLower F c).totalDegree < degree F.source c :=
  (totalDegree_rename_le _ _).trans_lt (IntegerRegularSource.lower_degree _ _ _
    (BoundedRegularSource.lower_degree _ _ _ _ (original_degree F.source c)))

theorem fullLeading_ne_zero (F : Inputs) (c : List Bool) : fullLeading F c ≠ 0 :=
  IntegerRegularSource.leading_ne_zero _ _ _ one_ne_zero

noncomputable def lower (F : Inputs) (c : List Bool) (frozen : ℕ → ℝ) : MvPolynomial (Fin (dim F c)) ℝ :=
  CoordinateBlockSpecialization.lower (Int.castRingHom ℝ) frozen (F.offset c) (dim F c)
    (fullLower F c) (fullLeading F c) (degree F.source c)

theorem slice_fermat (F : Inputs) (c : List Bool) (frozen : ℕ → ℝ)
    (hfit : F.offset c + dim F c ≤ F.source.dim c + 4) :
    slice F c frozen = FermatCriticalHomogenization.polynomial (lower F c frozen)
      (fullLeading F c : ℝ) (degree F.source c) := by
  unfold slice
  rw [full_polynomial_eq]
  exact CoordinateBlockSpecialization.finite_fermat _ _ _ _ _ _ hfit

theorem lower_degree (F : Inputs) (c : List Bool) (frozen : ℕ → ℝ) :
    (lower F c frozen).totalDegree < degree F.source c :=
  CoordinateBlockSpecialization.lower_degree _ _ _ _ _ _ _ (fullLower_degree F c)

end LeanCanny.Encoding.BoundedFullBlockKernel
