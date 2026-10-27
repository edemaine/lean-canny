/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalCoordinate
public import LeanCanny.Algebra.FiniteSourceDegreePreparation

/-! # Native finite-leaf input from the actual critical coordinate equations

Exact degrees are computed in polynomial space and written into a bounded
table. Checked contexts expose exact FP degree metadata; on the native
prepared context every leaf is the original coordinate annihilator.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalLeafSource
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open Brackets
open scoped Classical
attribute [local irreducible] BoundedCriticalCoordinate.polynomial

noncomputable def count (P : Readers) (c : List Bool) : ℕ := P.dim c + 4
noncomputable def degreeBound (P : Readers) (c : List Bool) : ℕ := 2 ^ BoundedCriticalProjection.labelWidth P c
noncomputable def height (P : Readers) (c : List Bool) : ℕ := BoundedCriticalProjection.coefficientBits P c
noncomputable def massBound (P : Readers) (c : List Bool) : ℕ := height P c + (degreeBound P c + 1).size

theorem count_unary {P : Readers} (h : P.PolyTime) : UnaryFn (count P) := h.dim.add (UnaryFn.const 4)
theorem degreeBound_binary {P : Readers} (h : P.PolyTime) : BinaryFn (degreeBound P) :=
  (BinaryFn.const 2).powUnary (BoundedCriticalProjection.labelWidth_unary h)
theorem height_binary {P : Readers} (h : P.PolyTime) : BinaryFn (height P) :=
  BoundedCriticalProjection.coefficientBits_binary h
theorem massBound_binary {P : Readers} (h : P.PolyTime) : BinaryFn (massBound P) :=
  (height_binary h).add (((degreeBound_binary h).add (BinaryFn.const 1)).size)

noncomputable def source (P : Readers) : SeparableBits.Family where
  polynomial := BoundedCriticalCoordinate.polynomial P
  height q := height P (pairFst q)
  coefficient_bound q k := (Nat.lt_size_self _).le.trans
    (Nat.pow_le_pow_right (by decide) (BoundedCriticalCoordinate.coefficient_bits P q k))

theorem source_degree (P : Readers) (c : List Bool) (i : ℕ) (_hi : i < count P c) :
    ((source P).polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ degreeBound P c := by
  simpa only [source, pairFst_pair, degreeBound] using BoundedCriticalCoordinate.degree_le P (pair c (BinaryNatCode.encode i))

theorem source_mass (P : Readers) (c : List Bool) (i : ℕ) (hi : i < count P c) :
    coefficientMass ((source P).polynomial (pair c (BinaryNatCode.encode i))) ≤ 2 ^ massBound P c := by
  apply coefficientMass_le_pow_of_degree_coeff _ _ _ (source_degree P c i hi)
  intro k
  simpa only [source, pairFst_pair] using (source P).coefficient_bound (pair c (BinaryNatCode.encode i)) k

/-- Reorder the native coordinate residue packet to the finite-leaf convention. -/
def coefficientQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pairSnd q)) (pairSnd (pairFst q))

theorem coefficientQuery_FP : coefficientQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

theorem coefficient_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (PrimitivePairBits.coefficient (source P).polynomial) := by
  refine ((BoundedCriticalCoordinate.coefficient_evaluator h ha).precompose
    coefficientQuery coefficientQuery_FP).congr (funext fun q => ?_)
  simp only [Function.comp_apply, BoundedCriticalCoordinate.coefficient_eq,
    PrimitivePairBits.coefficient, source, RationalSubstitution.IntegerBits.coefficientResidue]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => MatrixPower.residueBits (z : ZMod m))
    (by simp only [coefficientQuery, pairFst_pair, pairSnd_pair,
      RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree])
    (by simp only [coefficientQuery, pairFst_pair, pairSnd_pair, RationalSubstitution.IntegerBits.mValue])

noncomputable def prepare (P : Readers) : List Bool → List Bool :=
  FiniteSourceDegreePreparation.prepare (source P) (count P) (degreeBound P)

theorem prepare_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (prepare P) :=
  FiniteSourceDegreePreparation.prepareEvaluator (source P) (count P) (degreeBound P) (massBound P)
    (source_degree P) (source_mass P) (count_unary h) (degreeBound_binary h) (massBound_binary h)
    (coefficient_evaluator h ha)

@[simp] theorem prepare_source (P : Readers) (c : List Bool) : pairFst (prepare P c) = c :=
  FiniteSourceDegreePreparation.prepare_source _ _ _ _

noncomputable def family (P : Readers) : SeparableBits.Family :=
  FiniteSourceDegreePreparation.family (source P) (count P) (degreeBound P) (massBound P) (source_mass P)

noncomputable def readers {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SeparableBits.Readers (family P) :=
  FiniteSourceDegreePreparation.readers (source P) (count P) (degreeBound P) (massBound P)
    (source_degree P) (source_mass P) (count_unary h) (degreeBound_binary h) (massBound_binary h)
    (coefficient_evaluator h ha)

theorem family_nonzero (P : Readers) (p : List Bool) : (family P).polynomial p ≠ 0 :=
  FiniteSourceDegreePreparation.family_nonzero (source P) (count P) (degreeBound P) (massBound P)
    (source_mass P) (fun _ _ _ => BoundedCriticalCoordinate.ne_zero _ _) p

theorem prepared_polynomial (P : Readers) (c : List Bool) (i : ℕ) (hi : i < count P c) :
    (family P).polynomial (pair (prepare P c) (BinaryNatCode.encode i)) =
      BoundedCriticalCoordinate.polynomial P (pair c (BinaryNatCode.encode i)) :=
  FiniteSourceDegreePreparation.prepared_polynomial (source P) (count P) (degreeBound P) (massBound P)
    (source_degree P) (source_mass P) c i hi

end LeanCanny.Encoding.BoundedCriticalLeafSource
