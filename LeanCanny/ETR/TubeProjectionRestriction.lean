/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeProjectionRepack
public import LeanCanny.ETR.TubeCoefficientSpace

/-! # Native correctness of projection-to-tube queries

Repacking computes exactly the restriction to embedded tube variables. With an
increment it computes the source exponent used by the derivative coefficient
formula. The resulting tube child includes its entire space certificate.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeProjectionQuery
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding TubeProjectionEncoding
open LeanCanny.Algebra

noncomputable def restriction (n W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) : Coordinate (n c) →₀ ℕ :=
  (exponent n W target c).comapDomain ProjectionFlatten.coefficientEmbedding
    ProjectionFlatten.coefficientEmbedding_injective.injOn

theorem restriction_apply (n W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) (j : Coordinate (n c)) :
    restriction n W target c j = FixedWidthQuery.coordinate W target c (embeddedIndex (n c) (coordinateEquiv (n c) j).val) := by
  simp only [restriction, Finsupp.comapDomain_apply, exponent, Finsupp.coe_equivFunOnFinite_symm, index_embedding]

theorem repacked_exponent (n W r : List Bool → ℕ) (target : List Bool → List Bool) (bumped : Bool)
    (c : List Bool) (j : Coordinate (n c)) (hr : r c = (coordinateEquiv (n c) j).val) :
    TubeZeroQuery.exponent n (fun c => W c + 1) (repacked n W r target bumped) c =
      restriction n W target c + (if bumped then Finsupp.single j 1 else 0) := by
  classical
  ext k
  simp only [TubeZeroQuery.exponent, Finsupp.coe_equivFunOnFinite_symm, Finsupp.add_apply]
  rw [coordinate_repacked n W r target bumped c _ (coordinateEquiv (n c) k).isLt,
    entry, ite_eq_left (coordinateEquiv (n c) k).isLt, restriction_apply]
  have he : (coordinateEquiv (n c) k).val = r c ↔ j = k := by
    rw [hr]
    constructor
    · intro h
      exact ((coordinateEquiv (n c)).injective (Fin.ext h)).symm
    · rintro rfl
      rfl
  cases bumped <;> simp only [Bool.false_eq_true, ite_false, ite_true, Finsupp.zero_apply,
    Finsupp.single_apply, he]

attribute [local irreducible] TubeDense.polynomial TubePolynomial.integerPolynomial TubeCoefficient.value

noncomputable def child (base : List Bool → List Bool) (W r : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (bumped : Bool) : List Bool → List Bool :=
  TubeCoefficient.value base (fun c => W c + 1) active (repacked (TubeDense.arity base) W r target bumped) modulus

noncomputable def childEvaluator (base : List Bool → List Bool) (W r : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (bumped : Bool)
    (hb : base ∈ FP) (hW : UnaryFn W) (hr : UnaryFn r) (ha : active ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (child base W r active target modulus bumped) :=
  TubeCoefficient.evaluator base (fun c => W c + 1) active (repacked (TubeDense.arity base) W r target bumped) modulus
    hb (hW.add (UnaryFn.const 1)) ha (repacked_mem_FP (TubeDense.arity_unary hb) hW hr ht bumped) hm

theorem child_correct (base : List Bool → List Bool) (W r : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (bumped : Bool) (c : List Bool)
    (j : Coordinate (TubeDense.arity base c)) (hr : r c = (coordinateEquiv (TubeDense.arity base c) j).val) :
    child base W r active target modulus bumped c = Algebra.MatrixPower.residueBits
      (((TubePolynomial.integerPolynomial (TubeDense.polynomial base c) (activeSet (TubeDense.arity base c) (active c))).coeff
        (restriction (TubeDense.arity base) W target c + (if bumped then Finsupp.single j 1 else 0)) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  unfold child TubeCoefficient.value TubeCoefficient.coefficient
  rw [repacked_exponent _ W r target bumped c j hr]

end LeanCanny.ETR.TubeProjectionQuery
