/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildQueries
public import LeanCanny.Encoding.SeparablePolynomialThom
public import LeanCanny.Algebra.UnivariateRationalSpace

/-! # Parent derivative-sign probes at child parameter roots

The retained parent coordinate is a rational function of the child parameter.
Even denominator clearing pulls back any binary-indexed parent derivative
without changing its sign. Native readers and binary degree/mass bounds use
only the original source. All derivative signs together identify precisely
the desired parent root, including among extraneous parent fibers.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildParentThom
open LeanCanny.Algebra LeanCanny.Computation
open RationalParentChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildCoordinates.parameter RationalParentChildCoordinates.coordinate
  SeparablePolynomialThom.polynomial SeparablePolynomialThom.massExponent PrimitivePairBits.coefficient

def child (w : List Bool) : List Bool := pairFst w
def parent (w : List Bool) : List Bool := child w
theorem child_FP : child ∈ FP := pairFst_mem_FP
theorem parent_FP : parent ∈ FP := child_FP

def first (F : Inputs) (u : List Bool) : Fin (RationalParentChildSource.count F u) :=
  ⟨0, by unfold RationalParentChildSource.count; omega⟩

noncomputable def source (F : Inputs) (w : List Bool) : Polynomial ℤ :=
  SeparablePolynomialThom.polynomial F.joint.parent (parent w) (Nat.fromBitsLE (pairSnd w))
noncomputable def exponent (F : Inputs) (w : List Bool) : ℕ :=
  2 * F.joint.parent.degree (parent w)
noncomputable def numerator (F : Inputs) (w : List Bool) : Polynomial ℤ :=
  RationalParentChildReaders.numerator F (child w) 0
noncomputable def denominator (F : Inputs) (w : List Bool) : Polynomial ℤ :=
  RationalParentChildReaders.denominator F (child w) 0
noncomputable def polynomial (F : Inputs) (w : List Bool) : Polynomial ℤ :=
  UnivariateRational.clear (exponent F w) (source F w) (numerator F w) (denominator F w)

theorem source_degree (F : Inputs) (w : List Bool) : (source F w).natDegree ≤ exponent F w :=
  (SeparablePolynomialThom.degree F.joint.parent (parent w) _).trans (by unfold exponent; omega)
theorem exponent_binary {F : Inputs} (h : F.Access) : BinaryFn (exponent F) :=
  (BinaryFn.const 2).mul (h.joint.parent.degree.comp parent_FP)

def sourceQuery (q : List Bool) : List Bool :=
  pair (pair (parent (RationalSubstitution.IntegerBits.context q))
    (pair (pairSnd (RationalSubstitution.IntegerBits.context q)) (RationalSubstitution.IntegerBits.selectedDegree q))) (pairSnd q)
theorem sourceQuery_FP : sourceQuery ∈ FP := by
  have hp := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP parent_FP
  have ho := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP
  have H := mem_FP_pair (mem_FP_pair hp (mem_FP_pair ho RationalSubstitution.IntegerBits.selectedDegree_mem_FP)) pairSnd_mem_FP
  exact mem_FP_of_eq H (fun _ => rfl)

theorem source_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (PrimitivePairBits.coefficient (source F)) := by
  have E := (SeparablePolynomialThom.evaluator h.joint.parent).precompose sourceQuery sourceQuery_FP
  refine E.congr (funext fun q => ?_)
  simp only [Function.comp_apply, SeparablePolynomialThom.value, PrimitivePairBits.coefficient,
    RationalSubstitution.IntegerBits.coefficientResidue]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => MatrixPower.residueBits (z : ZMod m))
    (by simp only [sourceQuery, SeparablePolynomialThom.original, SeparablePolynomialThom.order,
      SeparablePolynomialThom.index, pairFst_pair, pairSnd_pair]; rfl)
    (by simp only [sourceQuery, pairSnd_pair, RationalSubstitution.IntegerBits.mValue])

def coordinateContext (w : List Bool) : List Bool := pair (child w) []
theorem coordinateContext_FP : coordinateContext ∈ FP := mem_FP_pair child_FP (constFn_mem_FP [])

theorem coordinate_evaluators {F : Inputs} (h : F.Access) :
    SpaceFunction (PrimitivePairBits.coefficient (numerator F)) ∧
      SpaceFunction (PrimitivePairBits.coefficient (denominator F)) := by
  have E := RationalParentChildCoordinates.coefficient_evaluators h
  exact ⟨PrimitivePairBits.withContextEvaluator _ coordinateContext (SpaceFunction.ofFP _ coordinateContext_FP) E.1,
    PrimitivePairBits.withContextEvaluator _ coordinateContext (SpaceFunction.ofFP _ coordinateContext_FP) E.2⟩

theorem evaluator {F : Inputs} (h : F.Access) : SpaceFunction (PrimitivePairBits.coefficient (polynomial F)) :=
  UnivariateRationalBits.evaluator _ _ _ _ (exponent_binary h) (source_evaluator h)
    (coordinate_evaluators h).1 (coordinate_evaluators h).2

noncomputable def degree (F : Inputs) (w : List Bool) : ℕ :=
  exponent F w * RationalParentChildCoordinates.coordinateDegree F (child w)
noncomputable def mass (F : Inputs) (w : List Bool) : ℕ :=
  SeparablePolynomialThom.massExponent F.joint.parent (parent w) +
    exponent F w * RationalParentChildCoordinates.coordinateMass F (child w)

theorem degree_binary {F : Inputs} (h : F.Access) : BinaryFn (degree F) :=
  (exponent_binary h).mul ((RationalParentChildCoordinates.coordinateDegree_binary h).comp child_FP)
theorem mass_binary {F : Inputs} (h : F.Access) : BinaryFn (mass F) := by
  have H : BinaryFn (fun w => SeparablePolynomialThom.massExponent F.joint.parent (parent w)) :=
    (SeparablePolynomialThom.massExponent_binary h.joint.parent).comp parent_FP
  exact H.add
    ((exponent_binary h).mul ((RationalParentChildCoordinates.coordinateMass_binary h).comp child_FP))

theorem polynomial_degree (F : Inputs) (w : List Bool) : (polynomial F w).natDegree ≤ degree F w :=
  UnivariateRational.clear_degree _ _ _ _ _
    (RationalParentChildReaders.coordinate_bounds F (child w) 0).1
    (RationalParentChildReaders.coordinate_bounds F (child w) 0).2.1

theorem polynomial_mass (F : Inputs) (w : List Bool) : coefficientMass (polynomial F w) ≤ 2 ^ mass F w := by
  have H := RationalParentChildReaders.coordinate_bounds F (child w) 0
  exact (UnivariateRational.clear_mass _ _ _ _ (source_degree F w) _ H.2.2.1 H.2.2.2).trans
    ((Nat.mul_le_mul_right _ (SeparablePolynomialThom.mass_bound F.joint.parent (parent w) _)).trans_eq (by
      rw [← pow_mul, ← pow_add, Nat.mul_comm]; rfl))

theorem sign (F : Inputs) (u : List Bool) (k : ℕ) (theta : ℝ)
    (ht : (RationalParentChildCoordinates.parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0) :
    SignType.sign ((polynomial F (pair u (BinaryNatCode.encode k))).eval₂ (Int.castRingHom ℝ) theta) =
      SignType.sign ((SeparablePolynomialThom.polynomial F.joint.parent u k).eval₂ (Int.castRingHom ℝ)
        (RationalParentChildParameters.decode F u theta (first F u))) := by
  have hd := RationalParentChildReaders.denominator_ne_zero F u theta ht (first F u)
  have hd' : (denominator F (pair u (BinaryNatCode.encode k))).eval₂ (Int.castRingHom ℝ) theta ≠ 0 := by
    simpa only [denominator, child, pairFst_pair, first] using hd
  rw [polynomial, UnivariateRational.eval₂_clear _ _ _ _ _ (source_degree F _) _ hd', sign_mul]
  have hp : 0 < (denominator F (pair u (BinaryNatCode.encode k))).eval₂ (Int.castRingHom ℝ) theta ^
      exponent F (pair u (BinaryNatCode.encode k)) := by
    rw [exponent, pow_mul]
    exact pow_pos (sq_pos_of_ne_zero hd') _
  rw [sign_pos hp, one_mul]
  simp only [source, parent, child, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  simp only [numerator, denominator, child, pairFst_pair, first,
    RationalParentChildReaders.numerator, RationalParentChildReaders.denominator,
    RationalParentChildParameters.decode, UnivariateRational.Coordinate.eval]

theorem parent_root (F : Inputs) (u : List Bool) (theta : ℝ) (ht : theta ∈ RationalParentChildQueries.roots F u) :
    (F.joint.parent.polynomial u).eval₂ (Int.castRingHom ℝ)
      (RationalParentChildParameters.decode F u theta (first F u)) = 0 := by
  have H := (RationalParentChildQueries.mem_roots F u theta).mp ht
  have hz := H.2.1 (first F u)
  change (IndexedMultivariateRational.parameter (F.joint.block.dim u)
    (F.joint.parent.polynomial u)).eval₂ (Int.castRingHom ℝ)
      (RationalParentChildParameters.decode F u theta) = 0 at hz
  simpa only [IndexedMultivariateRational.eval_parameter, RationalParentChildParameters.decode,
    first, Fin.val_zero] using hz

theorem identifies_parent (F : Inputs) (u : List Bool) (theta : ℝ)
    (ht : theta ∈ RationalParentChildQueries.roots F u) (t : ℝ)
    (hp : (F.joint.parent.polynomial u).eval₂ (Int.castRingHom ℝ) t = 0) :
    RationalParentChildParameters.decode F u theta (first F u) = t ↔
      ∀ k ≤ F.joint.parent.degree u,
        SignType.sign ((polynomial F (pair u (BinaryNatCode.encode k))).eval₂ (Int.castRingHom ℝ) theta) =
          SignType.sign ((SeparablePolynomialThom.polynomial F.joint.parent u k).eval₂ (Int.castRingHom ℝ) t) := by
  have H := (RationalParentChildQueries.mem_roots F u theta).mp ht
  simp_rw [sign F u _ theta H.1]
  exact SeparablePolynomialThom.root_eq_iff F.joint.parent u _ t (parent_root F u theta ht) hp

end LeanCanny.Encoding.RationalParentChildParentThom
