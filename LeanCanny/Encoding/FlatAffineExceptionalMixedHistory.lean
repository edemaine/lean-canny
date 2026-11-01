/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalBankCriticalData
public import LeanCanny.Algebra.IntegralMixedHistoryContinuation
public import LeanCanny.Algebra.IntegralIntegerRootBankOrigin
public import LeanCanny.Algebra.IntegralIntegerCompanionSpace

/-! # The concrete exceptional bank as a mixed-history initial state

The initial state is the existing actual whole-parent sampler and finite
integer-root bank. Its original spatial source and fixed initial scalar
cap are retained by the mixed interpreter. Each initial creating-generator
matrix has a native integer-companion reader, charged to the original
coefficient and exact-degree space readers; only its numeric query
metadata is required in polynomial time.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalMixedHistory
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width finitePolynomial)
open IntegralMixedHistory IntegralMixedHistoryScript IntegralHistorySampler
open scoped Classical

noncomputable def spatialSource (F : Inputs) (u : List Bool) : SpatialSource (F.source.dim u + 3) where
  low := FlatAffinePowerPositive.lower F u
  leading := FlatAffineExceptionalParentBank.sourceLeading F u
  degree := FlatAffinePowerControls.degree F u
  degree_two := by
    change 2 ≤ BoundedZeroSource.powerDegree (BoundedFullWriter.size F.source u)
    have H := BoundedRegularSource.powerDegree_gt_one (BoundedFullWriter.size F.source u)
    omega
  low_degree := FlatAffinePowerPositive.lower_degree F u
  leading_ne_zero := IntegerRegularSource.leading_ne_zero 1 _ _ (by decide)

noncomputable def initial (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1) :=
  retainIntegerBank (P := spatialSource F u) (FlatAffineExceptionalParentBank.bank F C h S u hm)
    (FlatAffineExceptionalBankSource.relative_cap F u)

noncomputable def continueHistory (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1)
    (cs : List (Command (F.source.dim u + 3) (width F u))) (hcs : births F u + cs.length ≤ S + 1) :=
  continueRun (initial F C h S u hm) cs hcs

theorem physical_arity (F : Inputs) (u : List Bool)
    (cs : List (Command (F.source.dim u + 3) (width F u))) :
    Fintype.card (Index (IntegralIntegerRootBank.Index (Fin (FlatAffineFullSourcePositive.count F u)) (births F u)) cs) =
      2 * FlatAffineFullSourcePositive.count F u + 1 + cs.length +
        (2 * (F.source.dim u + 3) + 3) * criticalCount cs := by
  rw [IntegralMixedHistoryScript.physical_arity, FlatAffineExceptionalParentBank.physical_arity]

noncomputable def initialOrigin (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1)
    (i : Fin (births F u)) :=
  IntegralIntegerRootBank.origin (FlatAffineExceptionalIntegralPrefix.parentSampler F C S (2 ^ width F u) u)
    (births F u) (finitePolynomial F C h u) (FlatAffineExceptionalBankSource.finite_nonzero F C h u) hm
    (FlatAffineExceptionalBankSource.finite_degree_cap F C h u) i

noncomputable def creatingFamily (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : List Bool → ℕ)
    (hm : ∀ q, births F (pairFst q) ≤ S q + 1) (i : ∀ q, Fin (births F (pairFst q)))
    (modulus : List Bool → ℕ) (hmod : ∀ q, modulus q ≠ 0)
    (row col : ∀ q, Fin (FixedWidthPolynomial.count ((initialOrigin F C h (S q) (pairFst q) (hm q) (i q)).birth + 1) (width F (pairFst q)))) :
    PaddedIntegralGeneratorFinBits.Family where
  arity q := (initialOrigin F C h (S q) (pairFst q) (hm q) (i q)).birth
  width q := width F (pairFst q)
  carrier q := (initialOrigin F C h (S q) (pairFst q) (hm q) (i q)).oldPrefix.carrier
  ring q := (initialOrigin F C h (S q) (pairFst q) (hm q) (i q)).oldPrefix.ring
  nontrivial q := (initialOrigin F C h (S q) (pairFst q) (hm q) (i q)).oldPrefix.nontrivial
  basis q := (initialOrigin F C h (S q) (pairFst q) (hm q) (i q)).oldPrefix.basis
  polynomial q := (initialOrigin F C h (S q) (pairFst q) (hm q) (i q)).polynomial
  degree q := (initialOrigin F C h (S q) (pairFst q) (hm q) (i q)).degree
  modulus := modulus
  modulus_ne_zero := hmod
  row := row
  col := col

def sourceWord {F : Inputs} (i : ∀ q, Fin (births F (pairFst q))) (q : List Bool) :=
  pair (pairFst q) (BinaryNatCode.encode (i q).val)

theorem sourceWord_FP {F : Inputs} (i : ∀ q, Fin (births F (pairFst q)))
    (hi : BinaryFn (fun q => (i q).val)) : sourceWord i ∈ FP :=
  mem_FP_pair pairFst_mem_FP hi.bits_mem_FP

def coefficientQuery {F : Inputs} (i : ∀ q, Fin (births F (pairFst q))) (q : List Bool) :=
  pair (pair (sourceWord i (RationalSubstitution.IntegerBits.context q))
    (RationalSubstitution.IntegerBits.selectedDegree q)) (pairSnd q)

theorem coefficientQuery_FP {F : Inputs} (i : ∀ q, Fin (births F (pairFst q)))
    (hi : BinaryFn (fun q => (i q).val)) : coefficientQuery i ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP (sourceWord_FP i hi))
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP

theorem creating_evaluator {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (S : List Bool → ℕ) (hm : ∀ q, births F (pairFst q) ≤ S q + 1)
    (i : ∀ q, Fin (births F (pairFst q))) (hi : BinaryFn (fun q => (i q).val))
    (modulus : List Bool → ℕ) (hmod : ∀ q, modulus q ≠ 0) (hM : BinaryFn modulus)
    (row col : ∀ q, Fin (FixedWidthPolynomial.count ((initialOrigin F C h (S q) (pairFst q) (hm q) (i q)).birth + 1) (width F (pairFst q))))
    (hR : BinaryFn (fun q => (row q).val)) (hC : BinaryFn (fun q => (col q).val)) :
    SpaceFunction (creatingFamily F C h S hm i modulus hmod row col).value := by
  let G := creatingFamily F C h S hm i modulus hmod row col
  let p : List Bool → Polynomial ℤ := fun q => finitePolynomial F C h (pairFst q) (i q)
  have HP : ∀ q, letI := G.ring q; G.polynomial q = (p q).map (Int.castRingHom (G.carrier q)) :=
    fun q => (initialOrigin F C h (S q) (pairFst q) (hm q) (i q)).original
  have HD : ∀ q, G.degree q = (p q).natDegree :=
    fun q => (initialOrigin F C h (S q) (pairFst q) (hm q) (i q)).actual_degree
  have ED := (FlatAffineExceptionalBankSource.actualDegree_evaluator hF C h hh).precompose (sourceWord i) (sourceWord_FP i hi)
  have EC := (FlatAffineExceptionalBankSource.coefficient_evaluator hF C h hh).precompose (coefficientQuery i) (coefficientQuery_FP i hi)
  have HEC : SpaceFunction (PrimitivePairBits.coefficient p) := EC.congr (funext fun q => by
    simp only [PrimitivePairBits.coefficient, coefficientQuery, sourceWord, Function.comp_apply,
      RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
      RationalSubstitution.IntegerBits.mValue, pairFst_pair, pairSnd_pair, p, finitePolynomial])
  exact IntegralIntegerCompanionBits.evaluator G p HP HD
    ⟨(FlatAffineExceptionalBankSource.width_unary hF h).comp pairFst_mem_FP, hM, hR, hC⟩
    (fun q => BinaryNatCode.encode (FlatAffineExceptionalBankSource.polynomial F C h (sourceWord i q)).natDegree)
    ED (fun q => congrArg BinaryNatCode.encode (HD q).symm) HEC

end LeanCanny.Encoding.FlatAffineExceptionalMixedHistory
