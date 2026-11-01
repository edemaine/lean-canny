/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCutQueries
public import LeanCanny.Algebra.MatrixProductSpace

/-! # Native non-top normalization product for actual relative cuts

The two factors are the constructed characteristic inverse of the actual
top matrix and the requested actual raw coefficient matrix. Both readers
are derived from the SAME nilpotent factor-value stage, and internal
queries preserve its source and caller modulus.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutProduct
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedCutSource
open scoped Classical

def rank (F : Family) (q : List Bool) := count (F.birth (PaddedIntegralGeneratorSource.base q)) (F.width (PaddedIntegralGeneratorSource.base q))

def index (F : Family) (word : List Bool → List Bool) (q : List Bool) : Fin (rank F q) :=
  ⟨Nat.fromBitsLE (word q) % rank F q, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

theorem rank_binary (F : Family) (a : Controls F) : BinaryFn (rank F) :=
  BinaryFn.of_bits (mem_FP_of_eq
    (countCode_mem_FP (a.birth.comp PaddedIntegralGeneratorSource.base_FP) (a.width.comp PaddedIntegralGeneratorSource.base_FP))
    (fun q => countCode_code _ _ q))

noncomputable def inverse (F : Family) (q : List Bool) :
    Matrix (Fin (count (F.birth q) (F.width q))) (Fin (count (F.birth q) (F.width q))) ℤ :=
  PaddedIntegralSelectedMatrixSource.matrix (source F) q

theorem inverse_eq (F : Family) (q : List Bool) :
    inverse F q = Polynomial.aeval
      (IntegralMixedCutMatrix.coefficientMatrix (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) (F.degree q))
      (IntegralParameterInverse.inverse
        (IntegralMixedCutMatrix.coefficientMatrix (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) (F.degree q)).charpoly) := by
  change Polynomial.aeval ((source F).coefficient q (F.degree q))
    (IntegralParameterInverse.inverse ((source F).coefficient q (F.degree q)).charpoly) = _
  rw [source_coefficient, ite_eq_left (Nat.le_refl _)]
  rfl

noncomputable def family (F : Family) : MatrixProductBits.Family where
  width := rank F
  count _ := 2
  modulus q := Nat.fromBitsLE (PaddedIntegralGeneratorSource.modulus q) + 1
  row := index F IntegralMixedCutQueries.rawRow
  col := index F IntegralMixedCutQueries.rawCol
  factor q s := (if s = 0 then inverse F (PaddedIntegralGeneratorSource.base q)
    else IntegralMixedCutMatrix.coefficientMatrix (F.state (PaddedIntegralGeneratorSource.base q)) (F.birth_bound _)
      (F.rule _) (F.kind _) (coefficientIndex q)).map (Int.castRingHom _)
  modulus_ne_zero _ := by omega

def inverseQuery (p : List Bool) : List Bool :=
  pair (pair (PaddedIntegralGeneratorSource.base (pairFst p)) (PaddedIntegralGeneratorSource.modulus (pairFst p)))
    (pairSnd (pairSnd p))

def rawQuery (p : List Bool) : List Bool :=
  pair (pair (PaddedIntegralGeneratorSource.base (pairFst p)) (PaddedIntegralGeneratorSource.modulus (pairFst p)))
    (pair (BinaryNatCode.encode (coefficientIndex (pairFst p))) (pairSnd (pairSnd p)))

theorem inverseQuery_FP : inverseQuery ∈ FP := by
  have HB : (fun p => PaddedIntegralGeneratorSource.base (pairFst p)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := PaddedIntegralGeneratorSource.base) pairFst_mem_FP PaddedIntegralGeneratorSource.base_FP
  have HM : (fun p => PaddedIntegralGeneratorSource.modulus (pairFst p)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := PaddedIntegralGeneratorSource.modulus) pairFst_mem_FP PaddedIntegralGeneratorSource.modulus_FP
  exact mem_FP_pair (mem_FP_pair HB HM) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

theorem rawQuery_FP : rawQuery ∈ FP := by
  have HB : (fun p => PaddedIntegralGeneratorSource.base (pairFst p)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := PaddedIntegralGeneratorSource.base) pairFst_mem_FP PaddedIntegralGeneratorSource.base_FP
  have HM : (fun p => PaddedIntegralGeneratorSource.modulus (pairFst p)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := PaddedIntegralGeneratorSource.modulus) pairFst_mem_FP PaddedIntegralGeneratorSource.modulus_FP
  have HI : BinaryFn (fun p => coefficientIndex (pairFst p)) := coefficientIndex_binary.comp pairFst_mem_FP
  exact mem_FP_pair (mem_FP_pair HB HM) (mem_FP_pair HI.bits_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))

def isFirst (p : List Bool) : Bool := decide (Nat.fromBitsLE (pairFst (pairSnd p)) = 0)

theorem isFirst_FP : (fun p => [isFirst p]) ∈ FP :=
  ((BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)).eq (BinaryFn.const 0)).flag_mem_FP

noncomputable def entry (F : Family) (H : RawBounds F) (p : List Bool) : List Bool :=
  if isFirst p then PaddedIntegralSelectedMatrixSource.value (source F) (selectedBounds F H) (inverseQuery p)
  else IntegralMixedCutQueries.coefficientValue F (rawQuery p)

theorem entry_evaluator (F : Family) (a : Controls F) (H : RawBounds F)
    (hH : BinaryFn H.height) (E : SpaceFunction (IntegralMixedCutQueries.value F)) : SpaceFunction (entry F H) :=
  SpaceFunction.branch _ isFirst_FP
    ((IntegralMixedCutQueries.inverse_evaluator F a H hH E).precompose _ inverseQuery_FP)
    ((IntegralMixedCutQueries.coefficient_evaluator F a E).precompose _ rawQuery_FP)

noncomputable def access (F : Family) (a : Controls F) (H : RawBounds F) : MatrixProductBits.Access (family F) where
  width := rank_binary F a
  count := BinaryFn.const 2
  modulus := (BinaryFn.fromBits PaddedIntegralGeneratorSource.modulus_FP).add (BinaryFn.const 1)
  row := (BinaryFn.fromBits IntegralMixedCutQueries.rawRow_FP).mod (rank_binary F a)
  col := (BinaryFn.fromBits IntegralMixedCutQueries.rawCol_FP).mod (rank_binary F a)
  entry := entry F H
  entry_eq q s i j := by
    have HS : isFirst (pair q (pair (BinaryNatCode.encode s)
        (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = decide (s = 0) := by
      simp only [isFirst, pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    change (if isFirst _ then _ else _) = residueBits
      (((if s = 0 then inverse F (PaddedIntegralGeneratorSource.base q)
        else IntegralMixedCutMatrix.coefficientMatrix (F.state (PaddedIntegralGeneratorSource.base q)) (F.birth_bound _)
          (F.rule _) (F.kind _) (coefficientIndex q)).map (Int.castRingHom _)) i j)
    rw [HS]
    by_cases Hs : s = 0
    · rw [ite_eq_left (by simpa only [decide_eq_true_eq] using Hs),
        ite_eq_left Hs]
      simp only [inverseQuery, pairFst_pair, pairSnd_pair]
      exact PaddedIntegralSelectedMatrixSource.value_packet (source F) (selectedBounds F H)
        (PaddedIntegralGeneratorSource.base q) (PaddedIntegralGeneratorSource.modulus q) i j
    · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using Hs),
        ite_eq_right Hs]
      simp only [rawQuery, pairFst_pair, pairSnd_pair]
      exact (IntegralMixedCutQueries.requests F).correct
        (PaddedIntegralGeneratorSource.base q) (PaddedIntegralGeneratorSource.modulus q) (coefficientIndex q) i j

theorem evaluator (F : Family) (a : Controls F) (H : RawBounds F)
    (hH : BinaryFn H.height) (E : SpaceFunction (IntegralMixedCutQueries.value F)) :
    SpaceFunction (family F).value :=
  MatrixProductBits.evaluator (family F) (access F a H) (entry_evaluator F a H hH E)

theorem value_eq (F : Family) (q : List Bool) :
    (family F).value q = residueBits (((inverse F (PaddedIntegralGeneratorSource.base q) *
      IntegralMixedCutMatrix.coefficientMatrix (F.state (PaddedIntegralGeneratorSource.base q)) (F.birth_bound _)
        (F.rule _) (F.kind _) (coefficientIndex q))
      (index F IntegralMixedCutQueries.rawRow q) (index F IntegralMixedCutQueries.rawCol q) : ℤ) :
        ZMod (Nat.fromBitsLE (PaddedIntegralGeneratorSource.modulus q) + 1)) := by
  unfold MatrixProductBits.Family.value
  change residueBits (MatrixProduct.product
    (fun s => (if s = 0 then inverse F (PaddedIntegralGeneratorSource.base q)
      else IntegralMixedCutMatrix.coefficientMatrix (F.state (PaddedIntegralGeneratorSource.base q)) (F.birth_bound _)
        (F.rule _) (F.kind _) (coefficientIndex q)).map
          (Int.castRingHom (ZMod (Nat.fromBitsLE (PaddedIntegralGeneratorSource.modulus q) + 1)))) 0 2
    (index F IntegralMixedCutQueries.rawRow q) (index F IntegralMixedCutQueries.rawCol q)) = _
  simp only [MatrixProduct.product, Nat.reduceAdd, ite_eq_right (by decide : (1 : ℕ) ≠ 0),
    ite_true, mul_one, ← Matrix.map_mul]
  rfl

end LeanCanny.Algebra.IntegralMixedCutProduct
