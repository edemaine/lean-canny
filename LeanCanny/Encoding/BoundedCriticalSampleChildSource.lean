/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleJointCoordinateCoefficient
public import LeanCanny.Algebra.FiniteSourceDegreePreparation

/-! # Indexed finite annihilator sources for regular child candidates

The source contains one nonzero coordinate equation per joint variable.
Coordinate indices are query metadata, so every leaf uses the same original
joint system. Exact degrees are computed in native polynomial space and
recorded in the existing checked degree table; only upper bounds are FP.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleJointCoordinate.polynomial
  BoundedCriticalSampleJointCoordinate.count BoundedCriticalSampleJointCoordinate.coefficientBits

structure Inputs where
  parent : Readers
  term : List Bool → List Bool
  offset : List Bool → ℕ
  dim : List Bool → ℕ
  directionWidth : List Bool → ℕ
  direction : List Bool → List Bool
  pivot : (u : List Bool) → Fin (dim u)

structure Inputs.PolyTime (F : Inputs) : Prop where
  parent : F.parent.PolyTime
  term : F.term ∈ FP
  offset : BinaryFn F.offset
  dim : UnaryFn F.dim
  directionWidth : UnaryFn F.directionWidth
  direction : F.direction ∈ FP
  pivot : BinaryFn (fun u => (F.pivot u).val)
  arity : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c

def count (F : Inputs) (u : List Bool) : ℕ := F.dim u + 1
noncomputable def degreeBound (F : Inputs) := BoundedCriticalSampleJointCoordinate.count F.parent F.term F.dim
noncomputable def height (F : Inputs) := BoundedCriticalSampleJointCoordinate.coefficientBits F.parent F.term F.dim F.directionWidth
noncomputable def massBound (F : Inputs) (u : List Bool) : ℕ := height F u + (degreeBound F u + 1).size

theorem count_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (count F) := h.dim.add (UnaryFn.const 1)
theorem degreeBound_binary {F : Inputs} (h : F.PolyTime) : BinaryFn (degreeBound F) :=
  BoundedCriticalSampleJointCoordinate.count_binary h.parent F.term h.term h.dim
theorem height_binary {F : Inputs} (h : F.PolyTime) : BinaryFn (height F) :=
  BoundedCriticalSampleJointCoordinate.coefficientBits_binary h.parent F.term h.term h.dim h.directionWidth
theorem massBound_binary {F : Inputs} (h : F.PolyTime) : BinaryFn (massBound F) :=
  (height_binary h).add (((degreeBound_binary h).add (BinaryFn.const 1)).size)

def selected (F : Inputs) (q : List Bool) : Fin (F.dim (pairFst q) + 1) :=
  ⟨min (Nat.fromBitsLE (pairSnd q)) (F.dim (pairFst q)), by omega⟩
theorem selected_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (fun q => (selected F q).val) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP (h.dim.comp pairFst_mem_FP)

noncomputable def atIndex (F : Inputs) (u : List Bool) (i : ℕ) : Polynomial ℤ :=
  BoundedCriticalSampleJointCoordinate.polynomial F.parent F.term F.offset F.dim F.directionWidth F.direction
    u (F.pivot u) ⟨min i (F.dim u), by omega⟩

noncomputable def polynomial (F : Inputs) (q : List Bool) : Polynomial ℤ :=
  atIndex F (pairFst q) (Nat.fromBitsLE (pairSnd q))

theorem atIndex_valid (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    atIndex F u i.val = BoundedCriticalSampleJointCoordinate.polynomial F.parent F.term F.offset F.dim
      F.directionWidth F.direction u (F.pivot u) i := by
  have hi : (⟨min i.val (F.dim u), by omega⟩ : Fin (F.dim u + 1)) = i := by
    apply Fin.ext
    exact Nat.min_eq_left (show i.val ≤ F.dim u by have := i.isLt; unfold count at this; omega)
  unfold atIndex
  rw [hi]

theorem polynomial_packet (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    polynomial F (pair u (BinaryNatCode.encode i.val)) =
      BoundedCriticalSampleJointCoordinate.polynomial F.parent F.term F.offset F.dim
        F.directionWidth F.direction u (F.pivot u) i := by
  simp only [polynomial, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode, atIndex_valid]

theorem nonzero (F : Inputs) (q : List Bool) : polynomial F q ≠ 0 :=
  BoundedCriticalSampleJointCoordinate.ne_zero _ _ _ _ _ _ _ _ _

noncomputable def source (F : Inputs) : SeparableBits.Family where
  polynomial := polynomial F
  height q := height F (pairFst q)
  coefficient_bound q j := (Nat.lt_size_self _).le.trans
    (Nat.pow_le_pow_right (by decide)
      (BoundedCriticalSampleJointCoordinate.polynomial_coefficient_bits F.parent F.term F.offset F.dim
        F.directionWidth F.direction (pairFst q) (F.pivot (pairFst q)) _ j))

theorem source_degree (F : Inputs) (u : List Bool) (i : ℕ) (_hi : i < count F u) :
    ((source F).polynomial (pair u (BinaryNatCode.encode i))).natDegree ≤ degreeBound F u := by
  simp only [source, polynomial, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]
  exact BoundedCriticalSampleJointCoordinate.polynomial_degree _ _ _ _ _ _ _ _ _

theorem source_mass (F : Inputs) (u : List Bool) (i : ℕ) (hi : i < count F u) :
    coefficientMass ((source F).polynomial (pair u (BinaryNatCode.encode i))) ≤ 2 ^ massBound F u := by
  apply coefficientMass_le_pow_of_degree_coeff _ _ _ (source_degree F u i hi)
  intro j
  simpa only [source, pairFst_pair] using (source F).coefficient_bound (pair u (BinaryNatCode.encode i)) j

theorem coefficient_evaluator {F : Inputs} (h : F.PolyTime) :
    SpaceFunction (PrimitivePairBits.coefficient (source F).polynomial) := by
  have E := BoundedCriticalSampleJointCoordinateCoefficient.evaluator h.parent F.term h.term h.offset h.dim
    h.directionWidth h.direction pairFst_mem_FP F.pivot h.pivot (selected F) (selected_unary h) h.arity
  let value := fun q => MatrixPower.residueBits (((polynomial F (pairFst (pairFst q))).coeff
    (Nat.fromBitsLE (pairSnd q)) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1))
  have R : SpaceFunction value := E.congr (funext fun _ => rfl)
  refine (R.precompose PrimitivePairBits.modularCoefficientQuery PrimitivePairBits.modularCoefficientQuery_FP).congr
    (funext fun q => ?_)
  simp only [Function.comp_apply, value, PrimitivePairBits.coefficient, source,
    RationalSubstitution.IntegerBits.coefficientResidue]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => MatrixPower.residueBits (z : ZMod m))
    (by simp only [PrimitivePairBits.modularCoefficientQuery, pairFst_pair, pairSnd_pair,
      RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree])
    (by simp only [PrimitivePairBits.modularCoefficientQuery, pairFst_pair, pairSnd_pair,
      RationalSubstitution.IntegerBits.mValue])

noncomputable def prepare (F : Inputs) : List Bool → List Bool :=
  FiniteSourceDegreePreparation.prepare (source F) (count F) (degreeBound F)

theorem prepare_evaluator {F : Inputs} (h : F.PolyTime) : SpaceFunction (prepare F) :=
  FiniteSourceDegreePreparation.prepareEvaluator (source F) (count F) (degreeBound F) (massBound F)
    (source_degree F) (source_mass F) (count_unary h) (degreeBound_binary h) (massBound_binary h) (coefficient_evaluator h)

@[simp] theorem prepare_source (F : Inputs) (u : List Bool) : pairFst (prepare F u) = u :=
  FiniteSourceDegreePreparation.prepare_source _ _ _ _

noncomputable def family (F : Inputs) : SeparableBits.Family :=
  FiniteSourceDegreePreparation.family (source F) (count F) (degreeBound F) (massBound F) (source_mass F)

noncomputable def readers {F : Inputs} (h : F.PolyTime) : SeparableBits.Readers (family F) :=
  FiniteSourceDegreePreparation.readers (source F) (count F) (degreeBound F) (massBound F)
    (source_degree F) (source_mass F) (count_unary h) (degreeBound_binary h) (massBound_binary h) (coefficient_evaluator h)

theorem family_nonzero (F : Inputs) (p : List Bool) : (family F).polynomial p ≠ 0 :=
  FiniteSourceDegreePreparation.family_nonzero (source F) (count F) (degreeBound F) (massBound F)
    (source_mass F) (fun _ _ _ => nonzero _ _) p

theorem prepared_polynomial (F : Inputs) (u : List Bool) (i : ℕ) (hi : i < count F u) :
    (family F).polynomial (pair (prepare F u) (BinaryNatCode.encode i)) = polynomial F (pair u (BinaryNatCode.encode i)) :=
  FiniteSourceDegreePreparation.prepared_polynomial (source F) (count F) (degreeBound F) (massBound F)
    (source_degree F) (source_mass F) u i hi

end LeanCanny.Encoding.BoundedCriticalSampleChildSource
