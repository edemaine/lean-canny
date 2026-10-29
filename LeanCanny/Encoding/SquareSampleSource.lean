/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleAccess
public import LeanCanny.Algebra.FiniteSourceDegreePreparation

/-! # Native indexed coordinate sources for a positive square system

The exact degree table is prepared from the proved canonical annihilator
reader. Only its degree and mass allowances are polynomial-time controls.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleSource
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def count (F : Inputs) := F.count
def degreeBound (F : Inputs) := F.annDegree
def height (F : Inputs) := F.annHeight
def massBound (F : Inputs) (u : List Bool) : ℕ := height F u + (degreeBound F u + 1).size

theorem count_pos (F : Inputs) (u : List Bool) : 0 < count F u := F.count_pos u
theorem count_unary {F : Inputs} (h : F.Access) : UnaryFn (count F) := h.count
theorem degreeBound_binary {F : Inputs} (h : F.Access) : BinaryFn (degreeBound F) := h.annDegree
theorem height_binary {F : Inputs} (h : F.Access) : BinaryFn (height F) := h.annHeight
theorem massBound_binary {F : Inputs} (h : F.Access) : BinaryFn (massBound F) :=
  h.annHeight.add ((h.annDegree.add (BinaryFn.const 1)).size)

def selected (F : Inputs) (q : List Bool) : Fin (count F (pairFst q)) :=
  SquareSampleInput.selected F (pairFst q) (pairSnd q)

theorem selected_unary {F : Inputs} (h : F.Access) : UnaryFn (fun q => (selected F q).val) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP ((h.count.comp pairFst_mem_FP).sub (UnaryFn.const 1))

def width (F : Inputs) (u : List Bool) : ℕ := (F.degree u).size

theorem width_unary {F : Inputs} (h : F.Access) : UnaryFn (width F) :=
  (UnaryFn.length h.degree.bits_mem_FP).of_eq (fun u => BinaryNatCode.length_encode (F.degree u))

theorem degree_lt_width (F : Inputs) (u : List Bool) : F.degree u < 2 ^ width F u := Nat.lt_size_self _

noncomputable def polynomial (F : Inputs) (q : List Bool) : Polynomial ℤ :=
  F.annihilator (pairFst q) (SquareSampleInput.selected F (pairFst q) (pairSnd q))

theorem polynomial_packet (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    polynomial F (pair u (BinaryNatCode.encode i.val)) = F.annihilator u i := by
  unfold polynomial
  rw [pairFst_pair, pairSnd_pair, SquareSampleInput.selected_encode]

theorem nonzero (F : Inputs) (q : List Bool) : polynomial F q ≠ 0 := F.ann_nonzero _ _

noncomputable def source (F : Inputs) : SeparableBits.Family where
  polynomial := polynomial F
  height q := height F (pairFst q)
  coefficient_bound q j := (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) (F.ann_height _ _ j))

theorem source_degree (F : Inputs) (u : List Bool) (i : ℕ) (_hi : i < count F u) :
    ((source F).polynomial (pair u (BinaryNatCode.encode i))).natDegree ≤ degreeBound F u := by
  exact (F.ann_degree _ _).trans_eq (congrArg F.annDegree (pairFst_pair _ _))

theorem source_mass (F : Inputs) (u : List Bool) (i : ℕ) (hi : i < count F u) :
    coefficientMass ((source F).polynomial (pair u (BinaryNatCode.encode i))) ≤ 2 ^ massBound F u := by
  apply coefficientMass_le_pow_of_degree_coeff _ _ _ (source_degree F u i hi)
  intro j
  simpa only [source, pairFst_pair] using (source F).coefficient_bound (pair u (BinaryNatCode.encode i)) j

def coefficientQuery (q : List Bool) : List Bool :=
  SquareSampleInput.query (pairFst (RationalSubstitution.IntegerBits.context q))
    (pairSnd (RationalSubstitution.IntegerBits.context q)) [] (RationalSubstitution.IntegerBits.selectedDegree q) (pairSnd q)

theorem coefficientQuery_FP : coefficientQuery ∈ FP :=
  SquareSampleInput.query_FP (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP)
    (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP) (constFn_mem_FP [])
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP

theorem coefficient_evaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (PrimitivePairBits.coefficient (source F).polynomial) := by
  refine (h.annihilator.precompose coefficientQuery coefficientQuery_FP).congr (funext fun q => ?_)
  simp only [Function.comp_apply, SquareSampleInput.annCoefficient, coefficientQuery, SquareSampleInput.query,
    SquareSampleInput.source, SquareSampleInput.indexWord, SquareSampleInput.rankWord, SquareSampleInput.modulusWord,
    pairFst_pair, pairSnd_pair]
  rfl

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
    (family F).polynomial (pair (prepare F u) (BinaryNatCode.encode i.val)) = F.annihilator u i :=
  (prepared_polynomial F u i.val i.isLt).trans (polynomial_packet F u i)

theorem prepared_regular_root (F : Inputs) (u : List Bool) (z : Fin (count F u) → ℝ)
    (hz : ∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) z = 0)
    (hr : (fderiv ℝ (fun y => fun i => (F.system u i).eval₂ (Int.castRingHom ℝ) y) z).IsInvertible)
    (i : Fin (count F u)) :
    ((family F).polynomial (pair (prepare F u) (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom ℝ) (z i) = 0 := by
  rw [prepared_coordinate]
  exact F.ann_root u z hz hr i

end LeanCanny.Encoding.SquareSampleSource
