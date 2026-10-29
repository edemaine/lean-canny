/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildReaders

/-! # Native joint-equation tests on child parameter roots

The joint rows remain implicit. Fixed even denominator powers preserve their
zeros and real signs on every child parameter root. These tests enforce the
joint equations; Jacobian and actual-parent filtering remain separate.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildFilters
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open RationalParentChildSource (Inputs count selected)
open RationalParentChildCoordinates (parameter coordinateDegree coordinateMass)
open RationalParentChildReaders (numerator denominator)
open RationalParentChildParameters (system decode)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentJointSource.system RationalParentJointSource.degree
  RationalParentJointSource.width RationalParentChildCoordinates.coordinate

noncomputable def family (F : Inputs) : FixedWidthRationalSubstitutionBits.Family where
  arity w := count F (pairFst w)
  width w := RationalParentJointSource.width F.joint (pairFst w)
  source w := system F (pairFst w) (selected F w)
  numerator w := numerator F (pairFst w)
  denominator w := denominator F (pairFst w)
  degree_fit w i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    ((RationalParentJointSource.polynomial_degree F.joint F.directionWidth
      F.direction (pairFst w) (F.pivot (pairFst w)) (selected F w)).trans_lt
        (RationalParentJointSource.degree_lt_width F.joint (pairFst w)))

noncomputable def polynomial (F : Inputs) : List Bool → Polynomial ℤ := (family F).polynomial

def rowContext (q : List Bool) : List Bool := pairFst (pairFst q)
def base (q : List Bool) : List Bool := pairFst (rowContext q)
def rank (q : List Bool) : List Bool := pairSnd (pairFst q)
theorem rowContext_FP : rowContext ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem base_FP : base ∈ FP := mem_FP_comp rowContext_FP pairFst_mem_FP
theorem rank_FP : rank ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

def query (F : Inputs) (q : List Bool) : List Bool :=
  pair (pair (base q) (pair (BinaryNatCode.encode (selected F (rowContext q)).val) (rank q))) (pairSnd q)
theorem query_FP {F : Inputs} (h : F.Access) : query F ∈ FP :=
  mem_FP_pair (mem_FP_pair base_FP
    (mem_FP_pair (bits_mem_FP ((RationalParentChildSource.selected_unary h).comp rowContext_FP)) rank_FP)) pairSnd_mem_FP

noncomputable def coefficient (F : Inputs) : List Bool → List Bool :=
  RationalParentJointCoefficient.value F.joint F.directionWidth
    (fun u => (F.pivot u).val) F.direction ∘ query F

theorem coefficient_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (coefficient F) :=
  (RationalParentJointCoefficient.evaluator h.joint h.directionWidth
    h.pivot h.direction h.sourceArity).precompose (query F) (query_FP h)

theorem coefficient_packet (F : Inputs) (w : List Bool) (r m : ℕ) (hm : 0 < m) :
    coefficient F (pair (pair w (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      residueBits (((family F).coefficient w r : ℤ) : ZMod m) := by
  have H := RationalParentJointCoefficient.packet F.joint F.directionWidth
    (fun u => (F.pivot u).val) F.direction (pairFst w) (F.pivot (pairFst w)) rfl (selected F w) r (m - 1)
  have hmod : m - 1 + 1 = m := by omega
  rw [hmod] at H
  have hw : rowContext (pair (pair w (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) = w := by
    simp only [rowContext, pairFst_pair]
  have hi : (selected F (rowContext (pair (pair w (BinaryNatCode.encode r))
      (BinaryNatCode.encode (m - 1))))).val = (selected F w).val := congrArg (fun v => (selected F v).val) hw
  simpa only [coefficient, Function.comp_apply, query, base, hw, hi, rank, pairFst_pair, pairSnd_pair,
    FixedWidthPolynomial.nativeExponent_refl, FixedWidthRationalSubstitutionBits.Family.coefficient, family, system, count] using H

noncomputable def access {F : Inputs} (h : F.Access) : FixedWidthRationalSubstitutionBits.Access (family F) where
  arity := (RationalParentChildSource.count_unary h).comp pairFst_mem_FP
  width := (RationalParentJointSource.width_unary h.joint).comp pairFst_mem_FP
  coefficient := coefficient F
  evaluator := coefficient_evaluator h
  coefficient_eq c r _ m hm := coefficient_packet F c r m hm
  coordinates := (RationalParentChildReaders.readers h).precompose pairFst pairFst_mem_FP

theorem evaluator {F : Inputs} (h : F.Access) : SpaceFunction (PrimitivePairBits.coefficient (polynomial F)) :=
  (access h).polynomialEvaluator

theorem zero_iff (F : Inputs) (w : List Bool) (theta : ℝ)
    (ht : (parameter F (pairFst w)).eval₂ (Int.castRingHom ℝ) theta = 0) :
    (polynomial F w).eval₂ (Int.castRingHom ℝ) theta = 0 ↔
      (system F (pairFst w) (selected F w)).eval₂ (Int.castRingHom ℝ) (decode F (pairFst w) theta) = 0 :=
  (family F).zero_iff w theta (fun i => RationalParentChildReaders.denominator_ne_zero F (pairFst w) theta ht i)

theorem sign (F : Inputs) (w : List Bool) (theta : ℝ)
    (ht : (parameter F (pairFst w)).eval₂ (Int.castRingHom ℝ) theta = 0) :
    SignType.sign ((polynomial F w).eval₂ (Int.castRingHom ℝ) theta) =
      SignType.sign ((system F (pairFst w) (selected F w)).eval₂ (Int.castRingHom ℝ) (decode F (pairFst w) theta)) :=
  (family F).sign w theta (fun i => RationalParentChildReaders.denominator_ne_zero F (pairFst w) theta ht i)

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
    exact Nat.min_eq_left (show i.val ≤ F.joint.block.dim (pairFst q) by have := i.isLt; unfold count at this; omega)
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
    (z : RationalParentChildParameters.Candidates F u) : Nonempty (Roots F u) := by
  let theta := (RationalParentChildParameters.regularEquiv F u).symm z
  exact ⟨⟨theta.val, theta.property.1, theta.property.2.1⟩⟩

noncomputable def degree (F : Inputs) (u : List Bool) : ℕ :=
  count F u * (2 * 2 ^ RationalParentJointSource.width F.joint u) * coordinateDegree F u
noncomputable def mass (F : Inputs) (u : List Bool) : ℕ :=
  (FixedWidthPolynomial.count (count F u) (RationalParentJointSource.width F.joint u)).size +
    RationalParentJointSource.massExponent F.joint F.directionWidth u +
      count F u * (2 * 2 ^ RationalParentJointSource.width F.joint u) * coordinateMass F u

theorem degree_binary {F : Inputs} (h : F.Access) : BinaryFn (degree F) := by
  have hg := (BinaryFn.const 2).powUnary (RationalParentJointSource.width_unary h.joint)
  exact ((BinaryFn.ofUnary (RationalParentChildSource.count_unary h)).mul ((BinaryFn.const 2).mul hg)).mul
    (RationalParentChildCoordinates.coordinateDegree_binary h)

theorem mass_binary {F : Inputs} (h : F.Access) : BinaryFn (mass F) := by
  have ht : BinaryFn (fun u => FixedWidthPolynomial.count (count F u) (RationalParentJointSource.width F.joint u)) :=
    BinaryFn.of_bits (mem_FP_of_eq (FixedWidthPolynomial.countCode_mem_FP (RationalParentChildSource.count_unary h)
      (RationalParentJointSource.width_unary h.joint)) (FixedWidthPolynomial.countCode_code _ _))
  have hg := (BinaryFn.const 2).powUnary (RationalParentJointSource.width_unary h.joint)
  exact (ht.size.add (RationalParentJointSource.massExponent_binary h.joint h.directionWidth)).add
    (((BinaryFn.ofUnary (RationalParentChildSource.count_unary h)).mul ((BinaryFn.const 2).mul hg)).mul
      (RationalParentChildCoordinates.coordinateMass_binary h))

theorem polynomial_degree (F : Inputs) (w : List Bool) : (polynomial F w).natDegree ≤ degree F (pairFst w) :=
  (family F).polynomial_degree (coordinateDegree F ∘ pairFst)
    (fun v i _ => (RationalParentChildReaders.coordinate_bounds F (pairFst v) i).1)
    (fun v i _ => (RationalParentChildReaders.coordinate_bounds F (pairFst v) i).2.1) w

theorem polynomial_mass (F : Inputs) (w : List Bool) : coefficientMass (polynomial F w) ≤ 2 ^ mass F (pairFst w) :=
  (family F).polynomial_mass (RationalParentJointSource.massExponent F.joint F.directionWidth ∘ pairFst)
    (coordinateMass F ∘ pairFst)
    (fun v _ _ => (MvMass.coeff_le _ _).trans (RationalParentJointSource.polynomial_mass F.joint F.directionWidth F.direction (pairFst v) (F.pivot (pairFst v)) (selected F v)))
    (fun v i _ => (RationalParentChildReaders.coordinate_bounds F (pairFst v) i).2.2.1)
    (fun v i _ => (RationalParentChildReaders.coordinate_bounds F (pairFst v) i).2.2.2) w

end LeanCanny.Encoding.RationalParentChildFilters
