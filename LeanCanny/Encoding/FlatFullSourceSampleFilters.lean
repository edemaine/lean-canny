/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleReaders

/-! # Native flat-equation tests on primitive parameter roots

The flat rows remain implicit. Fixed even denominator powers preserve their
zeros and real signs on every primitive parameter root. All original-source,
direction, and rational-coordinate readers are charged. These tests enforce
the complete flat equations; Jacobian filtering remains separate.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleFilters
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatFullSourceTower (Inputs)
open FlatFullSourceSampleSource (count selected)
open FlatFullSourceSampleCoordinates (parameter coordinateDegree coordinateMass)
open FlatFullSourceSampleReaders (numerator denominator)
open FlatFullSourceSampleParameters (decode)
open FlatFullSourcePositive (system)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourcePositive.system FlatFullSourceTower.degree
  FlatFullSourcePositiveCoordinate.width FlatFullSourceSampleCoordinates.coordinate

noncomputable def family (F : Inputs) : FixedWidthRationalSubstitutionBits.Family where
  arity w := count F (pairFst w)
  width w := FlatFullSourcePositiveCoordinate.width F (pairFst w)
  source w := system F (pairFst w) (selected F w)
  numerator w := numerator F (pairFst w)
  denominator w := denominator F (pairFst w)
  degree_fit w i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    ((FlatFullSourcePositive.polynomial_degree F (pairFst w) (selected F w)).trans_lt
        (FlatFullSourcePositiveCoordinate.degree_lt_width F (pairFst w)))

noncomputable def polynomial (F : Inputs) : List Bool → Polynomial ℤ := (family F).polynomial

def rowContext (q : List Bool) : List Bool := pairFst (pairFst q)
def base (q : List Bool) : List Bool := pairFst (rowContext q)
def rank (q : List Bool) : List Bool := pairSnd (pairFst q)
theorem rowContext_FP : rowContext ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem base_FP : base ∈ FP := mem_FP_comp rowContext_FP pairFst_mem_FP
theorem rank_FP : rank ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

def rowCode (F : Inputs) (q : List Bool) : List Bool :=
  BinaryNatCode.encode (selected F (rowContext q)).val

theorem rowCode_FP {F : Inputs} (h : F.Access) : rowCode F ∈ FP :=
  (BinaryFn.ofUnary ((FlatFullSourceSampleSource.selected_unary h).comp rowContext_FP)).bits_mem_FP

noncomputable def coefficient (F : Inputs) (q : List Bool) : List Bool :=
  residueBits (((family F).coefficient (rowContext q) (Nat.fromBitsLE (rank q)) : ℤ) :
    ZMod (Nat.fromBitsLE (pairSnd q) + 1))

theorem coefficient_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (coefficient F) := by
  have E := FlatFullSourcePositiveCoefficient.evaluator (FlatFullSourceContext.access h base_FP)
    ((FlatFullSourcePositiveCoordinate.width_unary h).comp base_FP) (rowCode_FP h) rank_FP pairSnd_mem_FP
  refine E.congr (funext fun q => ?_)
  have hw : FlatFullSourceTower.degree (FlatFullSourceContext.comp F base) q <
      2 ^ (FlatFullSourcePositiveCoordinate.width F ∘ base) q := by
    rw [FlatFullSourceContext.degree_comp]
    exact FlatFullSourcePositiveCoordinate.degree_lt_width F (base q)
  have H := FlatFullSourcePositiveCoefficient.packet (FlatFullSourceContext.comp F base)
    (FlatFullSourcePositiveCoordinate.width F ∘ base) (rowCode F) rank pairSnd q
    (selected F (rowContext q)) (MacaulayBits.fromBits_encode _) hw
  rw [FlatFullSourcePositiveRows.system_comp] at H
  rw [FixedWidthPolynomial.nativeExponent_refl] at H
  dsimp only [coefficient, FixedWidthRationalSubstitutionBits.Family.coefficient, family,
    Function.comp_def, count, FlatFullSourcePositive.count, FlatFullSourceTower.count,
    FlatFullSourceTower.arity, FlatFullSourceContext.comp, BoundedFullWriter.Readers.comp,
    base] at H ⊢
  exact H

theorem coefficient_packet (F : Inputs) (w : List Bool) (r m : ℕ) (hm : 0 < m) :
    coefficient F (pair (pair w (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      residueBits (((family F).coefficient w r : ℤ) : ZMod m) := by
  unfold coefficient
  have hc : rowContext (pair (pair w (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) = w := by
    simp only [rowContext, pairFst_pair]
  rw [hc]
  simp only [rank, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]
  apply congrArg₂ (fun (z : ℤ) (n : ℕ) => residueBits (z : ZMod n))
  · rfl
  · simp only [pairSnd_pair, MacaulayBits.fromBits_encode]
    omega

noncomputable def access {F : Inputs} (h : F.Access) : FixedWidthRationalSubstitutionBits.Access (family F) where
  arity := (FlatFullSourceSampleSource.count_unary h).comp pairFst_mem_FP
  width := (FlatFullSourcePositiveCoordinate.width_unary h).comp pairFst_mem_FP
  coefficient := coefficient F
  evaluator := coefficient_evaluator h
  coefficient_eq c r _ m hm := coefficient_packet F c r m hm
  coordinates := (FlatFullSourceSampleReaders.readers h).precompose pairFst pairFst_mem_FP

theorem evaluator {F : Inputs} (h : F.Access) : SpaceFunction (PrimitivePairBits.coefficient (polynomial F)) :=
  (access h).polynomialEvaluator

theorem zero_iff (F : Inputs) (w : List Bool) (theta : ℝ)
    (ht : (parameter F (pairFst w)).eval₂ (Int.castRingHom ℝ) theta = 0) :
    (polynomial F w).eval₂ (Int.castRingHom ℝ) theta = 0 ↔
      (system F (pairFst w) (selected F w)).eval₂ (Int.castRingHom ℝ) (decode F (pairFst w) theta) = 0 :=
  (family F).zero_iff w theta (fun i => FlatFullSourceSampleReaders.denominator_ne_zero F (pairFst w) theta ht i)

theorem sign (F : Inputs) (w : List Bool) (theta : ℝ)
    (ht : (parameter F (pairFst w)).eval₂ (Int.castRingHom ℝ) theta = 0) :
    SignType.sign ((polynomial F w).eval₂ (Int.castRingHom ℝ) theta) =
      SignType.sign ((system F (pairFst w) (selected F w)).eval₂ (Int.castRingHom ℝ) (decode F (pairFst w) theta)) :=
  (family F).sign w theta (fun i => FlatFullSourceSampleReaders.denominator_ne_zero F (pairFst w) theta ht i)

theorem zero_packet (F : Inputs) (u : List Bool) (i : Fin (count F u)) (theta : ℝ)
    (ht : (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0) :
    (polynomial F (pair u (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom ℝ) theta = 0 ↔
      (system F u i).eval₂ (Int.castRingHom ℝ) (decode F u theta) = 0 := by
  generalize hq : pair u (BinaryNatCode.encode i.val) = q
  have hu : pairFst q = u := by rw [← hq, pairFst_pair]
  have hi : Nat.fromBitsLE (pairSnd q) = i.val := by rw [← hq, pairSnd_pair]; exact Nat.fromBitsLE_bits _
  subst u
  have hs : selected F q = i := by
    apply Fin.ext
    simp only [selected, hi]
    exact Nat.min_eq_left (show i.val ≤ count F (pairFst q) - 1 by have := i.isLt; unfold count at this; omega)
  simpa only [hs] using zero_iff F q theta ht

def Valid (F : Inputs) (u : List Bool) (theta : ℝ) : Prop :=
  (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0 ∧
    ∀ i, (system F u i).eval₂ (Int.castRingHom ℝ) (decode F u theta) = 0

abbrev Roots (F : Inputs) (u : List Bool) := {theta : ℝ // Valid F u theta}

theorem valid_iff_filters (F : Inputs) (u : List Bool) (theta : ℝ) : Valid F u theta ↔
    (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0 ∧
      ∀ i : Fin (count F u), (polynomial F (pair u (BinaryNatCode.encode i.val))).eval₂
        (Int.castRingHom ℝ) theta = 0 := by
  constructor
  · rintro ⟨ht, hz⟩
    exact ⟨ht, fun i => (zero_packet F u i theta ht).mpr (hz i)⟩
  · rintro ⟨ht, hz⟩
    exact ⟨ht, fun i => (zero_packet F u i theta ht).mp (hz i)⟩

theorem regular_candidate_has_root (F : Inputs) (u : List Bool)
    (z : FlatFullSourceSampleParameters.Candidates F u) : Nonempty (Roots F u) := by
  let theta := (FlatFullSourceSampleParameters.regularEquiv F u).symm z
  exact ⟨⟨theta.val, theta.property.1, theta.property.2.1⟩⟩

noncomputable def degree (F : Inputs) (u : List Bool) : ℕ :=
  count F u * (2 * 2 ^ FlatFullSourcePositiveCoordinate.width F u) * coordinateDegree F u
noncomputable def mass (F : Inputs) (u : List Bool) : ℕ :=
  (FixedWidthPolynomial.count (count F u) (FlatFullSourcePositiveCoordinate.width F u)).size +
    FlatFullSourceTower.mass F u +
      count F u * (2 * 2 ^ FlatFullSourcePositiveCoordinate.width F u) * coordinateMass F u

theorem degree_binary {F : Inputs} (h : F.Access) : BinaryFn (degree F) := by
  have hg := (BinaryFn.const 2).powUnary (FlatFullSourcePositiveCoordinate.width_unary h)
  exact ((BinaryFn.ofUnary (FlatFullSourceSampleSource.count_unary h)).mul ((BinaryFn.const 2).mul hg)).mul
    (FlatFullSourceSampleCoordinates.coordinateDegree_binary h)

theorem mass_binary {F : Inputs} (h : F.Access) : BinaryFn (mass F) := by
  have ht : BinaryFn (fun u => FixedWidthPolynomial.count (count F u) (FlatFullSourcePositiveCoordinate.width F u)) :=
    BinaryFn.of_bits (mem_FP_of_eq (FixedWidthPolynomial.countCode_mem_FP (FlatFullSourceSampleSource.count_unary h)
      (FlatFullSourcePositiveCoordinate.width_unary h)) (FixedWidthPolynomial.countCode_code _ _))
  have hg := (BinaryFn.const 2).powUnary (FlatFullSourcePositiveCoordinate.width_unary h)
  exact (ht.size.add (FlatFullSourceTower.mass_binary h)).add
    (((BinaryFn.ofUnary (FlatFullSourceSampleSource.count_unary h)).mul ((BinaryFn.const 2).mul hg)).mul
      (FlatFullSourceSampleCoordinates.coordinateMass_binary h))

theorem polynomial_degree (F : Inputs) (w : List Bool) : (polynomial F w).natDegree ≤ degree F (pairFst w) :=
  (family F).polynomial_degree (coordinateDegree F ∘ pairFst)
    (fun v i _ => (FlatFullSourceSampleReaders.coordinate_bounds F (pairFst v) i).1)
    (fun v i _ => (FlatFullSourceSampleReaders.coordinate_bounds F (pairFst v) i).2.1) w

theorem polynomial_mass (F : Inputs) (w : List Bool) : coefficientMass (polynomial F w) ≤ 2 ^ mass F (pairFst w) :=
  (family F).polynomial_mass (FlatFullSourceTower.mass F ∘ pairFst)
    (coordinateMass F ∘ pairFst)
    (fun v _ _ => (MvMass.coeff_le _ _).trans (FlatFullSourcePositive.polynomial_mass F (pairFst v) (selected F v)))
    (fun v i _ => (FlatFullSourceSampleReaders.coordinate_bounds F (pairFst v) i).2.2.1)
    (fun v i _ => (FlatFullSourceSampleReaders.coordinate_bounds F (pairFst v) i).2.2.2) w

end LeanCanny.Encoding.FlatFullSourceSampleFilters
