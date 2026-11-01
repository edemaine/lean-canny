/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCutProduct

/-! # Actual normalized-cut coefficient and companion readers

The top branch computes the characteristic trailing integer; every lower
branch uses the constructed inverse/raw product; coefficients above the
selected degree are zero. This supplies the actual padded companion from
one concrete nilpotent factor-value matrix stage and its raw height bound.
It assumes no normalized coefficient reader or FP leading computation.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutNormalizedSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedCutSource
open scoped Classical

noncomputable def matrix (F : Family) (q : List Bool) (k : ℕ) :
    Matrix (Fin (count (F.birth q) (F.width q))) (Fin (count (F.birth q) (F.width q))) ℤ :=
  Algebra.leftMulMatrix (F.state q).sampler.scalarPrefix.basis.finBasis
    ((normalizedScalarPolynomial (F.state q)
      (IntegralMixedCutMatrix.raw (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) (F.degree q)) (F.degree q)).coeff k)

noncomputable def source (F : Family) : PaddedIntegralGeneratorSource.Source where
  arity := F.birth
  width := F.width
  carrier q := (F.state q).sampler.scalarPrefix.carrier
  ring q := (F.state q).sampler.scalarPrefix.ring
  nontrivial q := (F.state q).sampler.scalarPrefix.nontrivial
  basis q := (F.state q).sampler.scalarPrefix.basis
  polynomial q := normalizedScalarPolynomial (F.state q)
    (IntegralMixedCutMatrix.raw (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) (F.degree q)) (F.degree q)
  degree := F.degree

theorem source_coefficient (F : Family) (q : List Bool) (k : ℕ) :
    (source F).coefficient q k = matrix F q k := rfl

theorem matrix_eq (F : Family) (q : List Bool) (k : ℕ) :
    matrix F q k = if k = F.degree q then
      normalizedScalarLeading (F.state q)
        (IntegralMixedCutMatrix.raw (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) (F.degree q)) (F.degree q) • 1
    else if k ≤ F.degree q then IntegralMixedCutProduct.inverse F q *
      IntegralMixedCutMatrix.coefficientMatrix (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) k else 0 := by
  rw [IntegralMixedCutProduct.inverse_eq]
  exact IntegralMixedCutMatrix.normalized_coefficient_matrix _ _ _ _ _ _

def scalarQuery (q : List Bool) : List Bool :=
  pair (pair (PaddedIntegralGeneratorSource.base q) (PaddedIntegralGeneratorSource.modulus q)) []

theorem scalarQuery_FP : scalarQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair PaddedIntegralGeneratorSource.base_FP PaddedIntegralGeneratorSource.modulus_FP) (constFn_mem_FP [])

def row (F : Family) := IntegralMixedCutProduct.index F IntegralMixedCutQueries.rawRow
def col (F : Family) := IntegralMixedCutProduct.index F IntegralMixedCutQueries.rawCol

theorem row_binary (F : Family) (a : Controls F) : BinaryFn (fun q => (row F q).val) :=
  (BinaryFn.fromBits IntegralMixedCutQueries.rawRow_FP).mod (IntegralMixedCutProduct.rank_binary F a)
theorem col_binary (F : Family) (a : Controls F) : BinaryFn (fun q => (col F q).val) :=
  (BinaryFn.fromBits IntegralMixedCutQueries.rawCol_FP).mod (IntegralMixedCutProduct.rank_binary F a)

noncomputable def diagonal (F : Family) (H : RawBounds F) (q : List Bool) : List Bool :=
  if (row F q).val = (col F q).val then leading F H (scalarQuery q) else []

noncomputable def entry (F : Family) (H : RawBounds F) (q : List Bool) : List Bool :=
  if coefficientIndex q = F.degree (PaddedIntegralGeneratorSource.base q) then diagonal F H q
  else if coefficientIndex q ≤ F.degree (PaddedIntegralGeneratorSource.base q) then (IntegralMixedCutProduct.family F).value q else []

theorem diagonal_evaluator (F : Family) (a : Controls F) (H : RawBounds F)
    (hH : BinaryFn H.height) (E : SpaceFunction (IntegralMixedCutQueries.value F)) : SpaceFunction (diagonal F H) := by
  have HP := (row_binary F a).eq (col_binary F a)
  exact (SpaceFunction.branch _ HP.flag_mem_FP
    ((IntegralMixedCutQueries.leading_evaluator F a H hH E).precompose _ scalarQuery_FP)
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (by funext q; simp only [diagonal, decide_eq_true_eq, Function.comp_apply])

theorem entry_evaluator (F : Family) (a : Controls F) (H : RawBounds F)
    (hH : BinaryFn H.height) (E : SpaceFunction (IntegralMixedCutQueries.value F)) : SpaceFunction (entry F H) := by
  have HD : BinaryFn (fun q => F.degree (PaddedIntegralGeneratorSource.base q)) :=
    a.degree.comp PaddedIntegralGeneratorSource.base_FP
  have HT := coefficientIndex_binary.eq HD
  have HB := coefficientIndex_binary.le HD
  have EL := SpaceFunction.branch _ HB.flag_mem_FP (IntegralMixedCutProduct.evaluator F a H hH E)
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact (SpaceFunction.branch _ HT.flag_mem_FP (diagonal_evaluator F a H hH E) EL).congr
    (by funext q; simp only [entry, decide_eq_true_eq])

theorem entry_value (F : Family) (H : RawBounds F) (q : List Bool) :
    entry F H q = residueBits ((matrix F (PaddedIntegralGeneratorSource.base q) (coefficientIndex q)
      (row F q) (col F q) : ℤ) : ZMod (Nat.fromBitsLE (PaddedIntegralGeneratorSource.modulus q) + 1)) := by
  by_cases HT : coefficientIndex q = F.degree (PaddedIntegralGeneratorSource.base q)
  · rw [entry, ite_eq_left HT, diagonal, matrix_eq, ite_eq_left HT]
    by_cases HI : (row F q).val = (col F q).val
    · have HF : row F q = col F q := Fin.ext HI
      rw [ite_eq_left HI, scalarQuery, leading_packet]
      change residueBits ((normalizedScalarLeading (F.state (PaddedIntegralGeneratorSource.base q))
        (IntegralMixedCutMatrix.raw (F.state (PaddedIntegralGeneratorSource.base q)) (F.birth_bound _) (F.rule _) (F.kind _) (F.degree _)) (F.degree _) : ℤ) :
          ZMod (Nat.fromBitsLE (PaddedIntegralGeneratorSource.modulus q) + 1)) =
        residueBits (((normalizedScalarLeading (F.state (PaddedIntegralGeneratorSource.base q))
          (IntegralMixedCutMatrix.raw (F.state (PaddedIntegralGeneratorSource.base q)) (F.birth_bound _) (F.rule _) (F.kind _) (F.degree _)) (F.degree _)) *
            (if row F q = col F q then 1 else 0) : ℤ) : ZMod (Nat.fromBitsLE (PaddedIntegralGeneratorSource.modulus q) + 1))
      rw [ite_eq_left HF, mul_one]
    · have HF : row F q ≠ col F q := fun H => HI (congrArg Fin.val H)
      rw [ite_eq_right HI]
      change [] = residueBits (((normalizedScalarLeading (F.state (PaddedIntegralGeneratorSource.base q))
        (IntegralMixedCutMatrix.raw (F.state (PaddedIntegralGeneratorSource.base q)) (F.birth_bound _) (F.rule _) (F.kind _) (F.degree _)) (F.degree _)) *
          (if row F q = col F q then 1 else 0) : ℤ) : ZMod (Nat.fromBitsLE (PaddedIntegralGeneratorSource.modulus q) + 1))
      rw [ite_eq_right HF, mul_zero]
      rfl
  · by_cases HB : coefficientIndex q ≤ F.degree (PaddedIntegralGeneratorSource.base q)
    · rw [entry, ite_eq_right HT, ite_eq_left HB, IntegralMixedCutProduct.value_eq,
        matrix_eq, ite_eq_right HT, ite_eq_left HB]
      rfl
    · rw [entry, ite_eq_right HT, ite_eq_right HB, matrix_eq, ite_eq_right HT, ite_eq_right HB]
      rfl

noncomputable def access (F : Family) (a : Controls F) (H : RawBounds F) :
    PaddedIntegralGeneratorSource.Access (source F) where
  arity := a.birth
  width := a.width
  degree := a.degree
  entry := entry F H
  entry_eq q mw k i j := by
    generalize HP : pair (pair q mw) (pair (BinaryNatCode.encode k)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) = p
    have HB : PaddedIntegralGeneratorSource.base p = q := by
      rw [← HP]
      simp only [PaddedIntegralGeneratorSource.base, pairFst_pair]
    have HM : PaddedIntegralGeneratorSource.modulus p = mw := by
      rw [← HP]
      simp only [PaddedIntegralGeneratorSource.modulus, pairFst_pair, pairSnd_pair]
    subst q
    subst mw
    have HK := congrArg coefficientIndex HP
    simp only [coefficientIndex, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] at HK
    have HK' : coefficientIndex p = k := HK.symm
    have HI : row F p = i := by
      apply Fin.ext
      have HR := congrArg (fun z => Nat.fromBitsLE (IntegralMixedCutQueries.rawRow z)) HP
      simp only [IntegralMixedCutQueries.rawRow, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] at HR
      change Nat.fromBitsLE (pairFst (pairSnd (pairSnd p))) % IntegralMixedCutProduct.rank F p = i.val
      rw [← HR]
      exact Nat.mod_eq_of_lt i.isLt
    have HJ : col F p = j := by
      apply Fin.ext
      have HR := congrArg (fun z => Nat.fromBitsLE (IntegralMixedCutQueries.rawCol z)) HP
      simp only [IntegralMixedCutQueries.rawCol, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] at HR
      change Nat.fromBitsLE (pairSnd (pairSnd (pairSnd p))) % IntegralMixedCutProduct.rank F p = j.val
      rw [← HR]
      exact Nat.mod_eq_of_lt j.isLt
    change entry F H p = residueBits ((matrix F (PaddedIntegralGeneratorSource.base p) k i j : ℤ) :
      ZMod (Nat.fromBitsLE (PaddedIntegralGeneratorSource.modulus p) + 1))
    rw [entry_value, HK', HI, HJ]

theorem companion_evaluator (F : Family) (a : Controls F) (H : RawBounds F)
    (hH : BinaryFn H.height) (E : SpaceFunction (IntegralMixedCutQueries.value F)) :
    SpaceFunction (PaddedIntegralGeneratorSource.value (source F)) :=
  PaddedIntegralGeneratorSource.evaluator (source F) (access F a H) (entry_evaluator F a H hH E)

theorem actual_generator (F : Family) (q : List Bool) [Fintype (F.physical q)] :
    (source F).matrix q = Algebra.leftMulMatrix
      (IntegralMixedRelativeCuts.step (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) (F.degree q)).sampler.scalarPrefix.basis.finBasis
      ((IntegralMixedRelativeCuts.step (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) (F.degree q)).sampler.scalarPrefix.basis.generator 0) := rfl

end LeanCanny.Algebra.IntegralMixedCutNormalizedSource
