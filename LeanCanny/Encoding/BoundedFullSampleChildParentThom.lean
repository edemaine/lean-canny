/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildQueries
public import LeanCanny.Encoding.BoundedCriticalSampleThom
public import LeanCanny.Algebra.UnivariateRationalSpace

/-! # Parent derivative-sign probes at child parameter roots

The retained parent coordinate is a rational function of the child parameter.
Even denominator clearing pulls back any binary-indexed parent derivative
without changing its sign. Native readers and binary degree/mass bounds use
only the original source. All derivative signs together identify precisely
the desired parent root, including among extraneous parent fibers.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildParentThom
open LeanCanny.Algebra LeanCanny.Computation
open BoundedFullSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter BoundedCriticalRationalCoordinates.parameterDegree
  BoundedFullSampleChildCoordinates.parameter BoundedFullSampleChildCoordinates.coordinate
  BoundedCriticalSampleThom.polynomial BoundedCriticalSampleThom.massExponent
  PrimitivePairBits.coefficient

def child (w : List Bool) : List Bool := pairFst w
def parent (w : List Bool) : List Bool := pairFst (child w)
theorem child_FP : child ∈ FP := pairFst_mem_FP
theorem parent_FP : parent ∈ FP := mem_FP_comp child_FP pairFst_mem_FP

def first (F : Inputs) (u : List Bool) : Fin (BoundedFullSampleChildSource.count F u) :=
  ⟨0, by unfold BoundedFullSampleChildSource.count; omega⟩

noncomputable def source (F : Inputs) (w : List Bool) : Polynomial ℤ :=
  BoundedCriticalSampleThom.polynomial F.block.parent (parent w) (Nat.fromBitsLE (pairSnd w))
noncomputable def exponent (F : Inputs) (w : List Bool) : ℕ :=
  2 * BoundedCriticalRationalCoordinates.parameterDegree F.block.parent (parent w)
noncomputable def numerator (F : Inputs) (w : List Bool) : Polynomial ℤ :=
  BoundedFullSampleChildReaders.numerator F (child w) 0
noncomputable def denominator (F : Inputs) (w : List Bool) : Polynomial ℤ :=
  BoundedFullSampleChildReaders.denominator F (child w) 0
noncomputable def polynomial (F : Inputs) (w : List Bool) : Polynomial ℤ :=
  UnivariateRational.clear (exponent F w) (source F w) (numerator F w) (denominator F w)

theorem source_degree (F : Inputs) (w : List Bool) : (source F w).natDegree ≤ exponent F w :=
  (BoundedCriticalSampleThom.degree F.block.parent (parent w) _).trans (by unfold exponent; omega)
theorem exponent_binary {F : Inputs} (h : F.PolyTime) : BinaryFn (exponent F) :=
  (BinaryFn.const 2).mul ((BoundedCriticalRationalCoordinates.parameterDegree_binary h.block.parent).comp parent_FP)

def sourceQuery (q : List Bool) : List Bool :=
  pair (pair (parent (RationalSubstitution.IntegerBits.context q))
    (pair (pairSnd (RationalSubstitution.IntegerBits.context q)) (RationalSubstitution.IntegerBits.selectedDegree q))) (pairSnd q)
theorem sourceQuery_FP : sourceQuery ∈ FP := by
  have hp := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP parent_FP
  have ho := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP
  have H := mem_FP_pair (mem_FP_pair hp (mem_FP_pair ho RationalSubstitution.IntegerBits.selectedDegree_mem_FP)) pairSnd_mem_FP
  exact mem_FP_of_eq H (fun _ => rfl)

theorem source_evaluator {F : Inputs} (h : F.PolyTime) : SpaceFunction (PrimitivePairBits.coefficient (source F)) := by
  have E := (BoundedCriticalSampleThom.evaluator h.block.parent h.parentArity).precompose sourceQuery sourceQuery_FP
  refine E.congr (funext fun q => ?_)
  simp only [Function.comp_apply, BoundedCriticalSampleThom.value, PrimitivePairBits.coefficient,
    RationalSubstitution.IntegerBits.coefficientResidue]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => MatrixPower.residueBits (z : ZMod m))
    (by simp only [sourceQuery, BoundedCriticalSampleThom.original, BoundedCriticalSampleThom.order,
      BoundedCriticalSampleThom.index, pairFst_pair, pairSnd_pair]; rfl)
    (by simp only [sourceQuery, pairSnd_pair, RationalSubstitution.IntegerBits.mValue])

def coordinateContext (w : List Bool) : List Bool := pair (child w) []
theorem coordinateContext_FP : coordinateContext ∈ FP := mem_FP_pair child_FP (constFn_mem_FP [])

theorem coordinate_evaluators {F : Inputs} (h : F.PolyTime) :
    SpaceFunction (PrimitivePairBits.coefficient (numerator F)) ∧
      SpaceFunction (PrimitivePairBits.coefficient (denominator F)) := by
  have E := BoundedFullSampleChildCoordinates.coefficient_evaluators h
  exact ⟨PrimitivePairBits.withContextEvaluator _ coordinateContext (SpaceFunction.ofFP _ coordinateContext_FP) E.1,
    PrimitivePairBits.withContextEvaluator _ coordinateContext (SpaceFunction.ofFP _ coordinateContext_FP) E.2⟩

theorem evaluator {F : Inputs} (h : F.PolyTime) : SpaceFunction (PrimitivePairBits.coefficient (polynomial F)) :=
  UnivariateRationalBits.evaluator _ _ _ _ (exponent_binary h) (source_evaluator h)
    (coordinate_evaluators h).1 (coordinate_evaluators h).2

noncomputable def degree (F : Inputs) (w : List Bool) : ℕ :=
  exponent F w * BoundedFullSampleChildCoordinates.coordinateDegree F (child w)
noncomputable def mass (F : Inputs) (w : List Bool) : ℕ :=
  BoundedCriticalSampleThom.massExponent F.block.parent (parent w) +
    exponent F w * BoundedFullSampleChildCoordinates.coordinateMass F (child w)

theorem degree_binary {F : Inputs} (h : F.PolyTime) : BinaryFn (degree F) :=
  (exponent_binary h).mul ((BoundedFullSampleChildCoordinates.coordinateDegree_binary h).comp child_FP)
theorem mass_binary {F : Inputs} (h : F.PolyTime) : BinaryFn (mass F) := by
  have H : BinaryFn (fun w => BoundedCriticalSampleThom.massExponent F.block.parent (parent w)) :=
    (BoundedCriticalSampleThom.massExponent_binary h.block.parent).comp parent_FP
  exact H.add
    ((exponent_binary h).mul ((BoundedFullSampleChildCoordinates.coordinateMass_binary h).comp child_FP))

theorem polynomial_degree (F : Inputs) (w : List Bool) : (polynomial F w).natDegree ≤ degree F w :=
  UnivariateRational.clear_degree _ _ _ _ _
    (BoundedFullSampleChildReaders.coordinate_bounds F (child w) 0).1
    (BoundedFullSampleChildReaders.coordinate_bounds F (child w) 0).2.1

theorem polynomial_mass (F : Inputs) (w : List Bool) : coefficientMass (polynomial F w) ≤ 2 ^ mass F w := by
  have H := BoundedFullSampleChildReaders.coordinate_bounds F (child w) 0
  exact (UnivariateRational.clear_mass _ _ _ _ (source_degree F w) _ H.2.2.1 H.2.2.2).trans
    ((Nat.mul_le_mul_right _ (BoundedCriticalSampleThom.mass_bound F.block.parent (parent w) _)).trans_eq (by
      rw [← pow_mul, ← pow_add, Nat.mul_comm]; rfl))

theorem sign (F : Inputs) (u : List Bool) (k : ℕ) (theta : ℝ)
    (ht : (BoundedFullSampleChildCoordinates.parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0) :
    SignType.sign ((polynomial F (pair u (BinaryNatCode.encode k))).eval₂ (Int.castRingHom ℝ) theta) =
      SignType.sign ((BoundedCriticalSampleThom.polynomial F.block.parent (pairFst u) k).eval₂ (Int.castRingHom ℝ)
        (BoundedFullSampleChildParameters.decode F u theta (first F u))) := by
  have hd := BoundedFullSampleChildReaders.denominator_ne_zero F u theta ht (first F u)
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
    BoundedFullSampleChildReaders.numerator, BoundedFullSampleChildReaders.denominator,
    BoundedFullSampleChildParameters.decode, UnivariateRational.Coordinate.eval]

theorem parent_root (F : Inputs) (u : List Bool) (theta : ℝ) (ht : theta ∈ BoundedFullSampleChildQueries.roots F u) :
    (BoundedCriticalRationalCoordinates.parameter F.block.parent (pairFst u)).eval₂ (Int.castRingHom ℝ)
      (BoundedFullSampleChildParameters.decode F u theta (first F u)) = 0 := by
  have H := (BoundedFullSampleChildQueries.mem_roots F u theta).mp ht
  have hz := H.2.1 (first F u)
  change (IndexedMultivariateRational.parameter (F.block.dim u)
    (BoundedCriticalRationalCoordinates.parameter F.block.parent (pairFst u))).eval₂ (Int.castRingHom ℝ)
      (BoundedFullSampleChildParameters.decode F u theta) = 0 at hz
  simpa only [IndexedMultivariateRational.eval_parameter, BoundedFullSampleChildParameters.decode,
    first, Fin.val_zero] using hz

theorem identifies_parent (F : Inputs) (u : List Bool) (theta : ℝ)
    (ht : theta ∈ BoundedFullSampleChildQueries.roots F u)
    (x : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) :
    BoundedFullSampleChildParameters.decode F u theta (first F u) = (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) x).val ↔
      ∀ k ≤ BoundedCriticalRationalCoordinates.parameterDegree F.block.parent (pairFst u),
        SignType.sign ((polynomial F (pair u (BinaryNatCode.encode k))).eval₂ (Int.castRingHom ℝ) theta) =
          SignType.sign ((BoundedCriticalSampleThom.polynomial F.block.parent (pairFst u) k).eval₂ (Int.castRingHom ℝ)
            (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) x).val) := by
  have H := (BoundedFullSampleChildQueries.mem_roots F u theta).mp ht
  simp_rw [sign F u _ theta H.1]
  constructor
  · intro he k _
    rw [he]
  · intro hs
    apply ThomEncoding.root_eq ((BoundedCriticalRationalCoordinates.parameter F.block.parent (pairFst u)).map (Int.castRingHom ℝ))
      (BoundedCriticalSampleLabels.mapped_ne_zero F.block.parent (pairFst u))
      (BoundedCriticalRationalCoordinates.parameterDegree F.block.parent (pairFst u))
      (Polynomial.natDegree_map_le.trans (BoundedCriticalRationalCoordinates.parameter_bounds F.block.parent (pairFst u)).1)
    · rw [Polynomial.eval_map]
      exact parent_root F u theta ht
    · rw [Polynomial.eval_map]
      exact ((BoundedCriticalSampleLabels.mem_rootSet F.block.parent (pairFst u) _).mp
        (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) x).property).1
    · intro k hk
      simpa only [ThomEncoding.sign, Polynomial.iterate_derivative_map, Polynomial.eval_map,
        BoundedCriticalSampleThom.polynomial] using hs k hk

end LeanCanny.Encoding.BoundedFullSampleChildParentThom
