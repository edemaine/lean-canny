/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourcePositiveCoordinateCoefficient
public import LeanCanny.Encoding.FlatFullSourcePositiveContext
public import LeanCanny.Algebra.FiniteSourceDegreePreparation

/-! # Indexed finite annihilator sources for complete flat sampling

The source contains one nonzero coordinate equation per padded flat variable.
Coordinate indices are query metadata, so every leaf uses the same complete
original-source tower. Exact degrees are computed in native polynomial space and
recorded in the existing checked degree table; only upper bounds are FP.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open scoped Classical
set_option backward.isDefEq.respectTransparency false
open FlatFullSourceTower (Inputs)
attribute [local irreducible] FlatFullSourcePositiveCoordinate.polynomial
  FlatFullSourcePositiveCoordinate.matrixCount FlatFullSourcePositiveCoordinate.coefficientBits

def count (F : Inputs) := FlatFullSourcePositive.count F
noncomputable def degreeBound (F : Inputs) := FlatFullSourcePositiveCoordinate.matrixCount F
noncomputable def height (F : Inputs) := FlatFullSourcePositiveCoordinate.coefficientBits F
noncomputable def massBound (F : Inputs) (u : List Bool) : ℕ := height F u + (degreeBound F u + 1).size

theorem count_pos (F : Inputs) (u : List Bool) : 0 < count F u := FlatFullSourcePositive.count_pos F u
theorem count_unary {F : Inputs} (h : F.Access) : UnaryFn (count F) := FlatFullSourcePositive.count_unary h
theorem degreeBound_binary {F : Inputs} (h : F.Access) : BinaryFn (degreeBound F) :=
  FlatFullSourcePositiveCoordinate.matrixCount_binary h
theorem height_binary {F : Inputs} (h : F.Access) : BinaryFn (height F) :=
  FlatFullSourcePositiveCoordinate.coefficientBits_binary h
theorem massBound_binary {F : Inputs} (h : F.Access) : BinaryFn (massBound F) :=
  (height_binary h).add (((degreeBound_binary h).add (BinaryFn.const 1)).size)

def selected (F : Inputs) (q : List Bool) : Fin (count F (pairFst q)) :=
  ⟨min (Nat.fromBitsLE (pairSnd q)) (count F (pairFst q) - 1), by have := count_pos F (pairFst q); omega⟩
theorem selected_unary {F : Inputs} (h : F.Access) : UnaryFn (fun q => (selected F q).val) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP ((count_unary h).comp pairFst_mem_FP |>.sub (UnaryFn.const 1))

noncomputable def atIndex (F : Inputs) (u : List Bool) (i : ℕ) : Polynomial ℤ :=
  FlatFullSourcePositiveCoordinate.polynomial F u
    ⟨min i (count F u - 1), (show min i (count F u - 1) < count F u by have := count_pos F u; omega)⟩

noncomputable def polynomial (F : Inputs) (q : List Bool) : Polynomial ℤ :=
  atIndex F (pairFst q) (Nat.fromBitsLE (pairSnd q))

theorem atIndex_valid (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    atIndex F u i.val = FlatFullSourcePositiveCoordinate.polynomial F u i := by
  have hi : (⟨min i.val (count F u - 1), by have := count_pos F u; omega⟩ : Fin (count F u)) = i := by
    apply Fin.ext
    exact Nat.min_eq_left (show i.val ≤ count F u - 1 by have := i.isLt; omega)
  unfold atIndex
  rw [hi]

theorem polynomial_packet (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    polynomial F (pair u (BinaryNatCode.encode i.val)) =
      FlatFullSourcePositiveCoordinate.polynomial F u i := by
  simp only [polynomial, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode, atIndex_valid]

theorem nonzero (F : Inputs) (q : List Bool) : polynomial F q ≠ 0 :=
  FlatFullSourcePositiveCoordinate.ne_zero _ _ _

noncomputable def source (F : Inputs) : SeparableBits.Family where
  polynomial := polynomial F
  height q := height F (pairFst q)
  coefficient_bound q j := (Nat.lt_size_self _).le.trans
    (Nat.pow_le_pow_right (by decide)
      (FlatFullSourcePositiveCoordinate.polynomial_coefficient_bits F (pairFst q) _ j))

theorem source_degree (F : Inputs) (u : List Bool) (i : ℕ) (_hi : i < count F u) :
    ((source F).polynomial (pair u (BinaryNatCode.encode i))).natDegree ≤ degreeBound F u := by
  simp only [source, polynomial, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]
  exact FlatFullSourcePositiveCoordinate.polynomial_degree _ _ _

theorem source_mass (F : Inputs) (u : List Bool) (i : ℕ) (hi : i < count F u) :
    coefficientMass ((source F).polynomial (pair u (BinaryNatCode.encode i))) ≤ 2 ^ massBound F u := by
  apply coefficientMass_le_pow_of_degree_coeff _ _ _ (source_degree F u i hi)
  intro j
  simpa only [source, pairFst_pair] using (source F).coefficient_bound (pair u (BinaryNatCode.encode i)) j

theorem coefficient_evaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (PrimitivePairBits.coefficient (source F).polynomial) := by
  have E := FlatFullSourcePositiveCoordinateCoefficient.evaluator (FlatFullSourceContext.access h pairFst_mem_FP)
    (selected F) (selected_unary h)
  let value := fun q => MatrixPower.residueBits (((polynomial F (pairFst (pairFst q))).coeff
    (Nat.fromBitsLE (pairSnd q)) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1))
  have hp (q : List Bool) : FlatFullSourcePositiveCoordinate.polynomial (FlatFullSourceContext.comp F pairFst) q
      (selected F q) = polynomial F q := by
    rw [FlatFullSourcePositiveContext.polynomial_comp]
    rfl
  have R : SpaceFunction value := E.congr (funext fun q => by
    unfold FlatFullSourcePositiveCoordinateCoefficient.value
    rw [hp])
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

theorem prepare_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (prepare F) :=
  FiniteSourceDegreePreparation.prepareEvaluator (source F) (count F) (degreeBound F) (massBound F)
    (source_degree F) (source_mass F) (count_unary h) (degreeBound_binary h) (massBound_binary h) (coefficient_evaluator h)

@[simp] theorem prepare_source (F : Inputs) (u : List Bool) : pairFst (prepare F u) = u :=
  FiniteSourceDegreePreparation.prepare_source _ _ _ _

noncomputable def family (F : Inputs) : SeparableBits.Family :=
  FiniteSourceDegreePreparation.family (source F) (count F) (degreeBound F) (massBound F) (source_mass F)

noncomputable def readers {F : Inputs} (h : F.Access) : SeparableBits.Readers (family F) :=
  FiniteSourceDegreePreparation.readers (source F) (count F) (degreeBound F) (massBound F)
    (source_degree F) (source_mass F) (count_unary h) (degreeBound_binary h) (massBound_binary h) (coefficient_evaluator h)

theorem family_nonzero (F : Inputs) (p : List Bool) : (family F).polynomial p ≠ 0 :=
  FiniteSourceDegreePreparation.family_nonzero (source F) (count F) (degreeBound F) (massBound F)
    (source_mass F) (fun _ _ _ => nonzero _ _) p

theorem prepared_polynomial (F : Inputs) (u : List Bool) (i : ℕ) (hi : i < count F u) :
    (family F).polynomial (pair (prepare F u) (BinaryNatCode.encode i)) = polynomial F (pair u (BinaryNatCode.encode i)) :=
  FiniteSourceDegreePreparation.prepared_polynomial (source F) (count F) (degreeBound F) (massBound F)
    (source_degree F) (source_mass F) u i hi

theorem prepared_coordinate (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    (family F).polynomial (pair (prepare F u) (BinaryNatCode.encode i.val)) =
      FlatFullSourcePositiveCoordinate.polynomial F u i :=
  (prepared_polynomial F u i.val i.isLt).trans (polynomial_packet F u i)

theorem prepared_regular_root (F : Inputs) (u : List Bool) (z : Fin (count F u) → ℝ)
    (hz : ∀ i, (FlatFullSourcePositive.system F u i).eval₂ (Int.castRingHom ℝ) z = 0)
    (hr : (fderiv ℝ (fun y => fun i => (FlatFullSourcePositive.system F u i).eval₂ (Int.castRingHom ℝ) y) z).IsInvertible)
    (i : Fin (count F u)) :
    ((family F).polynomial (pair (prepare F u) (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom ℝ) (z i) = 0 := by
  rw [prepared_coordinate]
  exact FlatFullSourcePositiveCoordinate.eval_regular_root F u z hz hr i

end LeanCanny.Encoding.FlatFullSourceSampleSource
