/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalIntegralPrefix
public import LeanCanny.Encoding.SquareSampleSource
public import LeanCanny.Algebra.ModularProductSpace
public import LeanCanny.Algebra.PurePowerReductionBounds

/-! # Native integer-polynomial leaves for the exceptional parent bank

Index zero selects the exceptional scalar. Successor indices select every
coordinate annihilator of the actual retained parent sampler. One fixed
initial binary degree bound covers this finite bank; no later norm degree
is fed back into the original spatial source degree.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalBankSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (row parentCone)
open scoped Classical BigOperators

abbrev births (F : Inputs) (u : List Bool) : ℕ := FlatAffineFullSourcePositive.count F u + 1
theorem births_unary {F : Inputs} (hF : F.Access) : UnaryFn (births F) :=
  (FlatAffineFullSourcePositive.count_unary hF).add (UnaryFn.const 1)

noncomputable def degreeBound (F : Inputs) (u : List Bool) : ℕ :=
  FlatAffinePowerGram.degreeBound F u + FlatAffineHeightSlabExceptional.degreeBound (next F) u

theorem degreeBound_binary {F : Inputs} (hF : F.Access) (h : (u : List Bool) → Fin (arity F u)) :
    BinaryFn (degreeBound F) :=
  (FlatAffinePowerGram.degreeBound_binary hF).add (FlatAffineHeightSlabExceptional.degreeBound_binary
    (FlatAffineCompleteRootStages.access hF (hF.depth.add (UnaryFn.const 1))) (row F h))

noncomputable def relativeDimension (F : Inputs) (u : List Bool) : ℕ :=
  PurePowerReductionBounds.dimension (arity F u) (FlatAffinePowerControls.degree F u)

theorem relativeDimension_binary {F : Inputs} (hF : F.Access) : BinaryFn (relativeDimension F) :=
  PurePowerReductionBounds.dimension_binary (FlatAffineFullSourceTower.arity_unary hF)
    (BinaryFn.ofUnary (FlatAffinePowerControls.degree_unary hF.source))

noncomputable def width (F : Inputs) (u : List Bool) : ℕ := (degreeBound F u + relativeDimension F u).size

theorem width_unary {F : Inputs} (hF : F.Access) (h : (u : List Bool) → Fin (arity F u)) : UnaryFn (width F) :=
  (UnaryFn.length ((degreeBound_binary hF h).add (relativeDimension_binary hF)).bits_mem_FP).of_eq
    (fun _ => BinaryNatCode.length_encode _)

theorem relative_cap (F : Inputs) (u : List Bool) : relativeDimension F u ≤ 2 ^ width F u :=
  (Nat.le_add_left _ _).trans (Nat.lt_size_self _).le

noncomputable def massBound (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) : ℕ :=
  SquareSampleSource.massBound (FlatAffinePowerSampleInput.input F (parentCone F C)) u +
    (FlatAffineExceptionalSliceFrame.scalarSource F C h).mass u

theorem massBound_binary {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) : BinaryFn (massBound F C h) :=
  (SquareSampleSource.massBound_binary (FlatAffinePowerSampleInput.access hF (parentCone F C))).add
    (FlatAffineExceptionalSliceFrame.scalarAccess hF C h hh).mass

def coordinateQuery (w : List Bool) : List Bool := pair (pairFst w)
  (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd w) - 1))
theorem coordinateQuery_FP : coordinateQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP ((BinaryFn.fromBits pairSnd_mem_FP).sub (BinaryFn.const 1)).bits_mem_FP

noncomputable def polynomial (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (w : List Bool) : Polynomial ℤ :=
  if Nat.fromBitsLE (pairSnd w) = 0 then FlatAffineExceptionalIntegralPrefix.polynomial F h (pairFst w)
  else SquareSampleSource.polynomial (FlatAffinePowerSampleInput.input F (parentCone F C)) (coordinateQuery w)

theorem degree_le (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (w : List Bool) :
    (polynomial F C h w).natDegree ≤ degreeBound F (pairFst w) := by
  unfold polynomial
  split_ifs
  · exact (FlatAffineHeightSlabExceptional.degree_bound (next F) C (row F h) _).trans (Nat.le_add_left _ _)
  · exact ((FlatAffinePowerSampleInput.input F (parentCone F C)).ann_degree _ _).trans
      (by simp only [coordinateQuery, pairFst_pair]; exact Nat.le_add_right _ _)

theorem mass_le (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (w : List Bool) :
    coefficientMass (polynomial F C h w) ≤ 2 ^ massBound F C h (pairFst w) := by
  unfold polynomial
  split_ifs
  · exact ((FlatAffineExceptionalSliceFrame.scalarSource F C h).mass_bound _).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  · let I := FlatAffinePowerSampleInput.input F (parentCone F C)
    have H : coefficientMass (SquareSampleSource.polynomial I (coordinateQuery w)) ≤
        2 ^ SquareSampleSource.massBound I (pairFst w) := by
      have HC : pairFst (coordinateQuery w) = pairFst w := by simp only [coordinateQuery, pairFst_pair]
      have HD : (SquareSampleSource.polynomial I (coordinateQuery w)).natDegree ≤ I.annDegree (pairFst w) :=
        (I.ann_degree _ _).trans_eq (congrArg I.annDegree HC)
      apply coefficientMass_le_pow_of_degree_coeff _ _ _ HD
      intro j
      have HH : ((SquareSampleSource.polynomial I (coordinateQuery w)).coeff j).natAbs.size ≤ I.annHeight (pairFst w) :=
        (I.ann_height _ _ j).trans_eq (congrArg I.annHeight HC)
      exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) HH)
    exact H.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))

noncomputable def source (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) : IntegerPolynomialRootQueriesBits.Source where
  polynomial := polynomial F C h
  degree w := degreeBound F (pairFst w)
  mass w := massBound F C h (pairFst w)
  degree_bound := degree_le F C h
  mass_bound := mass_le F C h

def exceptionalCoefficientQuery (q : List Bool) : List Bool := pair
  (pair (pairFst (RationalSubstitution.IntegerBits.context q)) (RationalSubstitution.IntegerBits.selectedDegree q)) (pairSnd q)
def coordinateCoefficientQuery (q : List Bool) : List Bool := pair
  (pair (coordinateQuery (RationalSubstitution.IntegerBits.context q)) (RationalSubstitution.IntegerBits.selectedDegree q)) (pairSnd q)
theorem exceptionalCoefficientQuery_FP : exceptionalCoefficientQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP
theorem coordinateCoefficientQuery_FP : coordinateCoefficientQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP coordinateQuery_FP)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP

theorem coefficient_evaluator {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial F C h)) := by
  have E := (FlatAffineExceptionalIntegralPrefix.polynomial_evaluator hF h hh).precompose
    exceptionalCoefficientQuery exceptionalCoefficientQuery_FP
  have P := (SquareSampleSource.coefficient_evaluator (FlatAffinePowerSampleInput.access hF (parentCone F C))).precompose
    coordinateCoefficientQuery coordinateCoefficientQuery_FP
  have G := ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)).comp RationalSubstitution.IntegerBits.context_mem_FP
  exact (SpaceFunction.branch _ G.flag_mem_FP E P).congr (funext fun q => by
    by_cases hz : Nat.fromBitsLE (pairSnd (pairFst (pairFst q))) = 0 <;>
      simp only [PrimitivePairBits.coefficient, polynomial, Function.comp_apply, exceptionalCoefficientQuery,
        coordinateCoefficientQuery, RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
        RationalSubstitution.IntegerBits.mValue, pairFst_pair, pairSnd_pair, SquareSampleSource.source,
        hz, ite_true, ite_false, decide_true, decide_false, Bool.false_eq_true])

theorem access {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    IntegerPolynomialRootQueriesBits.Access (source F C h) :=
  ⟨coefficient_evaluator hF C h hh, (degreeBound_binary hF h).comp pairFst_mem_FP,
    (massBound_binary hF C h hh).comp pairFst_mem_FP⟩

noncomputable def finitePolynomial (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) (i : Fin (births F u)) : Polynomial ℤ :=
  polynomial F C h (pair u (BinaryNatCode.encode i.val))

theorem finite_zero (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) :
    finitePolynomial F C h u ⟨0, Nat.zero_lt_succ _⟩ = FlatAffineExceptionalIntegralPrefix.polynomial F h u := by
  simp only [finitePolynomial, polynomial, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]

theorem finite_succ (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) (i : Fin (FlatAffineFullSourcePositive.count F u)) :
    finitePolynomial F C h u i.succ = (FlatAffinePowerSampleInput.input F (parentCone F C)).annihilator u i := by
  simp only [finitePolynomial, polynomial, Fin.val_succ, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, coordinateQuery, Nat.add_sub_cancel]
  exact SquareSampleSource.polynomial_packet _ _ _

theorem finite_nonzero (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) (i : Fin (births F u)) : finitePolynomial F C h u i ≠ 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [finitePolynomial, polynomial, Fin.val_zero, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]
    exact FlatAffineHeightSlabExceptional.ne_zero (next F) C (row F h) u
  · rw [finite_succ]
    exact (FlatAffinePowerSampleInput.input F (parentCone F C)).ann_nonzero u j

theorem finite_degree_cap (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) (i : Fin (births F u)) :
    (finitePolynomial F C h u i).natDegree ≤ 2 ^ width F u := by
  have H := degree_le F C h (pair u (BinaryNatCode.encode i.val))
  rw [pairFst_pair] at H
  exact H.trans ((Nat.le_add_right _ _).trans (Nat.lt_size_self _).le)

end LeanCanny.Encoding.FlatAffineExceptionalBankSource
