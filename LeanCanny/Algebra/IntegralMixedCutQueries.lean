/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCutSource
public import LeanCanny.Algebra.IntegralMixedCutNilpotent

/-! # Native relative-factor coefficient requests with exact digit guards

A raw coefficient request becomes one entry request for the ACTUAL factor
value in the bounded formal nilpotent algebra. Its source and modulus are
preserved literally. The index writer is native FP, its auxiliary rank is
binary, and invalid sweep digits return zero instead of being reduced.
The matrix-entry arithmetic for the actual coordinate/PSC/Gram factor
values is deliberately still a lower stage, rather than a new oracle.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutQueries
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCoordinateBasis
open IntegralMixedCutSource
open scoped Classical

def rank (F : Family) (q : List Bool) := count (F.birth q + 1) (F.width q)

theorem rank_binary (F : Family) (a : Controls F) : BinaryFn (rank F) :=
  BinaryFn.of_bits (mem_FP_of_eq (countCode_mem_FP (a.birth.add (UnaryFn.const 1)) a.width)
    (fun q => countCode_code _ _ q))

def rawRow (q : List Bool) := pairFst (pairSnd (pairSnd q))
def rawCol (q : List Bool) := pairSnd (pairSnd (pairSnd q))

theorem rawRow_FP : rawRow ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem rawCol_FP : rawCol ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

def query (F : Family) (q : List Bool) : List Bool :=
  pair (pair (PaddedIntegralGeneratorSource.base q) (PaddedIntegralGeneratorSource.modulus q))
    (pair (BinaryNatCode.encode (coefficientIndex q + 2 ^ F.width (PaddedIntegralGeneratorSource.base q) * Nat.fromBitsLE (rawRow q)))
      (BinaryNatCode.encode (2 ^ F.width (PaddedIntegralGeneratorSource.base q) * Nat.fromBitsLE (rawCol q))))

theorem query_FP (F : Family) (a : Controls F) : query F ∈ FP := by
  have HN : BinaryFn (fun q => 2 ^ F.width (PaddedIntegralGeneratorSource.base q)) :=
    ((BinaryFn.const 2).powUnary a.width).comp PaddedIntegralGeneratorSource.base_FP
  exact mem_FP_pair (mem_FP_pair PaddedIntegralGeneratorSource.base_FP PaddedIntegralGeneratorSource.modulus_FP)
    (mem_FP_pair (coefficientIndex_binary.add (HN.mul (BinaryFn.fromBits rawRow_FP))).bits_mem_FP
      (HN.mul (BinaryFn.fromBits rawCol_FP)).bits_mem_FP)

theorem query_base (F : Family) (q : List Bool) :
    PaddedIntegralGeneratorSource.base (query F q) = PaddedIntegralGeneratorSource.base q := by
  simp only [query, PaddedIntegralGeneratorSource.base, pairFst_pair]

theorem query_modulus (F : Family) (q : List Bool) :
    PaddedIntegralGeneratorSource.modulus (query F q) = PaddedIntegralGeneratorSource.modulus q := by
  simp only [query, PaddedIntegralGeneratorSource.modulus, pairFst_pair, pairSnd_pair]

def index (F : Family) (word : List Bool → List Bool) (q : List Bool) :
    Fin (rank F (PaddedIntegralGeneratorSource.base q)) :=
  ⟨Nat.fromBitsLE (word q) % rank F (PaddedIntegralGeneratorSource.base q),
    Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

noncomputable def value (F : Family) (q : List Bool) : List Bool :=
  residueBits ((Algebra.leftMulMatrix
    (IntegralMixedCutNilpotent.basis (F.state (PaddedIntegralGeneratorSource.base q))).finBasis
    (IntegralMixedCutNilpotent.value (F.state (PaddedIntegralGeneratorSource.base q))
      (F.birth_bound _) (F.rule _) (F.kind _))
    (index F PaddedIntegralGeneratorSource.row q) (index F PaddedIntegralGeneratorSource.col q) : ℤ) :
      ZMod (Nat.fromBitsLE (PaddedIntegralGeneratorSource.modulus q) + 1))

theorem value_packet (F : Family) (q mw : List Bool) (i j : Fin (rank F q)) :
    value F (pair (pair q mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        (IntegralMixedCutNilpotent.value (F.state q) (F.birth_bound q) (F.rule q) (F.kind q)) i j : ℤ) :
          ZMod (Nat.fromBitsLE mw + 1)) := by
  generalize HP : pair (pair q mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) = p
  have HB : PaddedIntegralGeneratorSource.base p = q := by
    rw [← HP]
    simp only [PaddedIntegralGeneratorSource.base, pairFst_pair]
  have HM : PaddedIntegralGeneratorSource.modulus p = mw := by
    rw [← HP]
    simp only [PaddedIntegralGeneratorSource.modulus, pairFst_pair, pairSnd_pair]
  subst q
  subst mw
  have HI : index F PaddedIntegralGeneratorSource.row
      p = i := by
    apply Fin.ext
    have HR := congrArg (fun z => Nat.fromBitsLE (PaddedIntegralGeneratorSource.row z)) HP
    simp only [PaddedIntegralGeneratorSource.row, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits] at HR
    change Nat.fromBitsLE (pairFst (pairSnd p)) % rank F (PaddedIntegralGeneratorSource.base p) = _
    rw [← HR]
    exact Nat.mod_eq_of_lt i.isLt
  have HJ : index F PaddedIntegralGeneratorSource.col
      p = j := by
    apply Fin.ext
    have HR := congrArg (fun z => Nat.fromBitsLE (PaddedIntegralGeneratorSource.col z)) HP
    simp only [PaddedIntegralGeneratorSource.col, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits] at HR
    change Nat.fromBitsLE (pairSnd (pairSnd p)) % rank F (PaddedIntegralGeneratorSource.base p) = _
    rw [← HR]
    exact Nat.mod_eq_of_lt j.isLt
  rw [value, HI, HJ]

noncomputable def coefficientValue (F : Family) (q : List Bool) : List Bool :=
  if coefficientIndex q < 2 ^ F.width (PaddedIntegralGeneratorSource.base q) then value F (query F q) else []

theorem coefficient_evaluator (F : Family) (a : Controls F) (E : SpaceFunction (value F)) :
    SpaceFunction (coefficientValue F) := by
  have HN : BinaryFn (fun q => 2 ^ F.width (PaddedIntegralGeneratorSource.base q)) :=
    ((BinaryFn.const 2).powUnary a.width).comp PaddedIntegralGeneratorSource.base_FP
  have HP := coefficientIndex_binary.lt HN
  exact (SpaceFunction.branch _ HP.flag_mem_FP (E.precompose _ (query_FP F a))
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (by funext q; simp only [coefficientValue, decide_eq_true_eq, Function.comp_apply])

noncomputable def requests (F : Family) : RawRequests F where
  request := coefficientValue F
  correct q mw k i j := by
    let p := pair (pair q mw) (pair (BinaryNatCode.encode k)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
    have HK : coefficientIndex p = k := by simp only [p, coefficientIndex, pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have HB : PaddedIntegralGeneratorSource.base p = q := by
      simp only [p, PaddedIntegralGeneratorSource.base, pairFst_pair]
    change coefficientValue F p = _
    by_cases H : k < 2 ^ F.width q
    · let e : Fin (2 ^ F.width q) := ⟨k, H⟩
      have HQ : query F p = pair (pair q mw)
          (pair (BinaryNatCode.encode (pairIndex (F.birth q) (F.width q) (i, e)).val)
            (BinaryNatCode.encode (pairIndex (F.birth q) (F.width q) (j, 0)).val)) := by
        simp only [query, p, coefficientIndex, rawRow, rawCol, PaddedIntegralGeneratorSource.base,
          PaddedIntegralGeneratorSource.modulus, pairFst_pair, pairSnd_pair,
          BinaryNatCode.encode, Nat.fromBitsLE_bits, IntegralMixedCutNilpotent.pairIndex_value,
          Fin.val_zero, Nat.zero_add, e]
      have HG : k < 2 ^ F.width (PaddedIntegralGeneratorSource.base p) := HB.symm ▸ H
      rw [coefficientValue, HK, ite_eq_left HG, HQ]
      exact (value_packet F q mw (pairIndex (F.birth q) (F.width q) (i, e))
        (pairIndex (F.birth q) (F.width q) (j, 0))).trans
          (congrArg (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE mw + 1)))
            (IntegralMixedCutNilpotent.coefficient (F.state q) (F.birth_bound q)
              (F.rule q) (F.kind q) (F.scalar_cap q) e i j))
    · have HZ := IntegralMixedCutNilpotent.coefficient_outside (F.state q) (F.birth_bound q)
        (F.rule q) (F.kind q) (F.scalar_cap q) k (Nat.le_of_not_gt H)
      have HG : ¬k < 2 ^ F.width (PaddedIntegralGeneratorSource.base p) := HB.symm ▸ H
      rw [coefficientValue, HK, ite_eq_right HG, HZ]
      rfl

theorem leading_evaluator (F : Family) (a : Controls F) (H : RawBounds F)
    (hH : BinaryFn H.height) (E : SpaceFunction (value F)) :
    SpaceFunction (IntegralMixedCutSource.leading F H) :=
  IntegralMixedCutSource.leading_evaluator F a (requests F) H hH (coefficient_evaluator F a E)

theorem inverse_evaluator (F : Family) (a : Controls F) (H : RawBounds F)
    (hH : BinaryFn H.height) (E : SpaceFunction (value F)) :
    SpaceFunction (PaddedIntegralSelectedMatrixSource.value (source F) (selectedBounds F H)) :=
  IntegralMixedCutSource.inverse_evaluator F a (requests F) H hH (coefficient_evaluator F a E)

end LeanCanny.Algebra.IntegralMixedCutQueries
