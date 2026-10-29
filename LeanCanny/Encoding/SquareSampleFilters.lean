/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleReaders

/-! # Native system equation tests on primitive parameter roots

The square-system rows remain implicit. Fixed even denominator powers preserve their
zeros and real signs on every primitive parameter root. The canonical row and rational-coordinate readers are charged. These tests enforce
the square system equations; Jacobian filtering remains separate.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleFilters
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open SquareSampleInput (Inputs)
open SquareSampleSource (count selected)
open SquareSampleCoordinates (parameter coordinateDegree coordinateMass)
open SquareSampleReaders (numerator denominator)
open SquareSampleParameters (decode)

open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible]
  SquareSampleSource.width SquareSampleCoordinates.coordinate

noncomputable def family (F : Inputs) : FixedWidthRationalSubstitutionBits.Family where
  arity w := count F (pairFst w)
  width w := SquareSampleSource.width F (pairFst w)
  source w := F.system (pairFst w) (selected F w)
  numerator w := numerator F (pairFst w)
  denominator w := denominator F (pairFst w)
  degree_fit w i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    ((F.system_degree (pairFst w) (selected F w)).trans_lt
        (SquareSampleSource.degree_lt_width F (pairFst w)))

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
  (BinaryFn.ofUnary ((SquareSampleSource.selected_unary h).comp rowContext_FP)).bits_mem_FP

noncomputable def coefficient (F : Inputs) (q : List Bool) : List Bool :=
  residueBits (((family F).coefficient (rowContext q) (Nat.fromBitsLE (rank q)) : ℤ) :
    ZMod (Nat.fromBitsLE (pairSnd q) + 1))

theorem coefficient_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (coefficient F) := by
  have E := SquareSampleInput.row_evaluator h base_FP
    ((SquareSampleSource.width_unary h).comp base_FP)
    (fun q => selected F (rowContext q))
    ((SquareSampleSource.selected_unary h).comp rowContext_FP) rank_FP pairSnd_mem_FP
  refine E.congr (funext fun q => ?_)
  rw [FixedWidthPolynomial.nativeExponent_refl]
  rfl

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
  arity := (SquareSampleSource.count_unary h).comp pairFst_mem_FP
  width := (SquareSampleSource.width_unary h).comp pairFst_mem_FP
  coefficient := coefficient F
  evaluator := coefficient_evaluator h
  coefficient_eq c r _ m hm := coefficient_packet F c r m hm
  coordinates := (SquareSampleReaders.readers h).precompose pairFst pairFst_mem_FP

theorem evaluator {F : Inputs} (h : F.Access) : SpaceFunction (PrimitivePairBits.coefficient (polynomial F)) :=
  (access h).polynomialEvaluator

theorem zero_iff (F : Inputs) (w : List Bool) (theta : ℝ)
    (ht : (parameter F (pairFst w)).eval₂ (Int.castRingHom ℝ) theta = 0) :
    (polynomial F w).eval₂ (Int.castRingHom ℝ) theta = 0 ↔
      (F.system (pairFst w) (selected F w)).eval₂ (Int.castRingHom ℝ) (decode F (pairFst w) theta) = 0 :=
  (family F).zero_iff w theta (fun i => SquareSampleReaders.denominator_ne_zero F (pairFst w) theta ht i)

theorem sign (F : Inputs) (w : List Bool) (theta : ℝ)
    (ht : (parameter F (pairFst w)).eval₂ (Int.castRingHom ℝ) theta = 0) :
    SignType.sign ((polynomial F w).eval₂ (Int.castRingHom ℝ) theta) =
      SignType.sign ((F.system (pairFst w) (selected F w)).eval₂ (Int.castRingHom ℝ) (decode F (pairFst w) theta)) :=
  (family F).sign w theta (fun i => SquareSampleReaders.denominator_ne_zero F (pairFst w) theta ht i)

theorem zero_packet (F : Inputs) (u : List Bool) (i : Fin (count F u)) (theta : ℝ)
    (ht : (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0) :
    (polynomial F (pair u (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom ℝ) theta = 0 ↔
      (F.system u i).eval₂ (Int.castRingHom ℝ) (decode F u theta) = 0 := by
  generalize hq : pair u (BinaryNatCode.encode i.val) = q
  have hu : pairFst q = u := by rw [← hq, pairFst_pair]
  have hi : Nat.fromBitsLE (pairSnd q) = i.val := by rw [← hq, pairSnd_pair]; exact Nat.fromBitsLE_bits _
  subst u
  have hs : selected F q = i := by
    apply Fin.ext
    simp only [SquareSampleSource.selected, SquareSampleInput.selected, hi]
    exact Nat.min_eq_left (show i.val ≤ count F (pairFst q) - 1 by have := i.isLt; unfold count at this; omega)
  simpa only [hs] using zero_iff F q theta ht

def Valid (F : Inputs) (u : List Bool) (theta : ℝ) : Prop :=
  (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0 ∧
    ∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) (decode F u theta) = 0

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
    (z : SquareSampleParameters.Candidates F u) : Nonempty (Roots F u) := by
  let theta := (SquareSampleParameters.regularEquiv F u).symm z
  exact ⟨⟨theta.val, theta.property.1, theta.property.2.1⟩⟩

noncomputable def degree (F : Inputs) (u : List Bool) : ℕ :=
  count F u * (2 * 2 ^ SquareSampleSource.width F u) * coordinateDegree F u
noncomputable def mass (F : Inputs) (u : List Bool) : ℕ :=
  (FixedWidthPolynomial.count (count F u) (SquareSampleSource.width F u)).size +
    F.mass u +
      count F u * (2 * 2 ^ SquareSampleSource.width F u) * coordinateMass F u

theorem degree_binary {F : Inputs} (h : F.Access) : BinaryFn (degree F) := by
  have hg := (BinaryFn.const 2).powUnary (SquareSampleSource.width_unary h)
  exact ((BinaryFn.ofUnary (SquareSampleSource.count_unary h)).mul ((BinaryFn.const 2).mul hg)).mul
    (SquareSampleCoordinates.coordinateDegree_binary h)

theorem mass_binary {F : Inputs} (h : F.Access) : BinaryFn (mass F) := by
  have ht : BinaryFn (fun u => FixedWidthPolynomial.count (count F u) (SquareSampleSource.width F u)) :=
    BinaryFn.of_bits (mem_FP_of_eq (FixedWidthPolynomial.countCode_mem_FP (SquareSampleSource.count_unary h)
      (SquareSampleSource.width_unary h)) (FixedWidthPolynomial.countCode_code _ _))
  have hg := (BinaryFn.const 2).powUnary (SquareSampleSource.width_unary h)
  exact (ht.size.add (h.mass)).add
    (((BinaryFn.ofUnary (SquareSampleSource.count_unary h)).mul ((BinaryFn.const 2).mul hg)).mul
      (SquareSampleCoordinates.coordinateMass_binary h))

theorem polynomial_degree (F : Inputs) (w : List Bool) : (polynomial F w).natDegree ≤ degree F (pairFst w) :=
  (family F).polynomial_degree (coordinateDegree F ∘ pairFst)
    (fun v i _ => (SquareSampleReaders.coordinate_bounds F (pairFst v) i).1)
    (fun v i _ => (SquareSampleReaders.coordinate_bounds F (pairFst v) i).2.1) w

theorem polynomial_mass (F : Inputs) (w : List Bool) : coefficientMass (polynomial F w) ≤ 2 ^ mass F (pairFst w) :=
  (family F).polynomial_mass (F.mass ∘ pairFst)
    (coordinateMass F ∘ pairFst)
    (fun v _ _ => (MvMass.coeff_le _ _).trans (F.system_mass (pairFst v) (selected F v)))
    (fun v i _ => (SquareSampleReaders.coordinate_bounds F (pairFst v) i).2.2.1)
    (fun v i _ => (SquareSampleReaders.coordinate_bounds F (pairFst v) i).2.2.2) w

end LeanCanny.Encoding.SquareSampleFilters
