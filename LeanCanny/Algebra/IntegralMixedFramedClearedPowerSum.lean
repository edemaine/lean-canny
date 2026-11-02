/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedClearedMatrixPower
public import LeanCanny.Algebra.ModularSumSpace
/-! # Streamed sums of actual old-coordinate matrix powers

Newest-first retained index N-i names original coordinate i in the positive
auxiliary prefix. The same saved key and old matrix rank are used for every
summand. The count and power are original native numeric readers.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedClearedPowerSumBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedClearedMatrixBits (rank matrix wrap)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def matrixSum (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N e : List Bool → ℕ) (key : List Bool) : Matrix (Fin (rank P D H key)) (Fin (rank P D H key)) ℤ :=
  ∑ i ∈ Finset.range (N key), matrix P D H key (N key-i)^e key

noncomputable def row (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  wrap P D H (PaddedIntegralGeneratorSource.base q) (Nat.fromBitsLE (PaddedIntegralGeneratorSource.row q))
noncomputable def col (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  wrap P D H (PaddedIntegralGeneratorSource.base q) (Nat.fromBitsLE (PaddedIntegralGeneratorSource.col q))

theorem row_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    BinaryFn (fun q=>(row P D H q).val) :=
  (BinaryFn.fromBits PaddedIntegralGeneratorSource.row_FP).mod ((IntegralMixedFramedClearedMatrixBits.rank_binary P a D H).comp PaddedIntegralGeneratorSource.base_FP)
theorem col_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    BinaryFn (fun q=>(col P D H q).val) :=
  (BinaryFn.fromBits PaddedIntegralGeneratorSource.col_FP).mod ((IntegralMixedFramedClearedMatrixBits.rank_binary P a D H).comp PaddedIntegralGeneratorSource.base_FP)

noncomputable def requestAt (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N e : List Bool → ℕ) (q : List Bool) (i : ℕ) :=
  IntegralMixedFramedClearedMatrixPowerBits.packet (PaddedIntegralGeneratorSource.base q)
    (PaddedIntegralGeneratorSource.modulus q)
    (BinaryNatCode.encode (N (PaddedIntegralGeneratorSource.base q)-i))
    (e (PaddedIntegralGeneratorSource.base q)) (row P D H q).val (col P D H q).val

noncomputable def request (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N e : List Bool → ℕ) (z : List Bool) := requestAt P D H N e (pairFst z) (Nat.fromBitsLE (pairSnd z))

theorem request_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    {N e : List Bool → ℕ} (hN : UnaryFn N) (he : BinaryFn e) : request P D H N e∈FP := by
  have HB : (fun z : List Bool=>PaddedIntegralGeneratorSource.base (pairFst z))∈FP :=
    mem_FP_comp (f := pairFst) (g := PaddedIntegralGeneratorSource.base) pairFst_mem_FP PaddedIntegralGeneratorSource.base_FP
  have HM : (fun z : List Bool=>PaddedIntegralGeneratorSource.modulus (pairFst z))∈FP :=
    mem_FP_comp (f := pairFst) (g := PaddedIntegralGeneratorSource.modulus) pairFst_mem_FP PaddedIntegralGeneratorSource.modulus_FP
  have HN : BinaryFn (fun z=>N (PaddedIntegralGeneratorSource.base (pairFst z))) := (BinaryFn.ofUnary hN).comp HB
  have HI : BinaryFn (fun z=>N (PaddedIntegralGeneratorSource.base (pairFst z))-Nat.fromBitsLE (pairSnd z)) :=
    HN.sub (BinaryFn.fromBits pairSnd_mem_FP)
  have HE : BinaryFn (fun z=>e (PaddedIntegralGeneratorSource.base (pairFst z))) := he.comp HB
  have HR : BinaryFn (fun z=>(row P D H (pairFst z)).val) := (row_binary P a D H).comp pairFst_mem_FP
  have HC : BinaryFn (fun z=>(col P D H (pairFst z)).val) := (col_binary P a D H).comp pairFst_mem_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair HB HM)
    (mem_FP_pair HI.bits_mem_FP (mem_FP_pair HR.bits_mem_FP HC.bits_mem_FP))) HE.bits_mem_FP

noncomputable def summand (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N e : List Bool → ℕ) := (IntegralMixedFramedClearedMatrixPowerBits.powerFamily P D H).value ∘ request P D H N e

theorem summand_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N e : List Bool → ℕ) (q : List Bool) (i : ℕ) :
    summand P D H N e (pair q (BinaryNatCode.encode i))=residueBits
      ((matrix P D H (PaddedIntegralGeneratorSource.base q) (N (PaddedIntegralGeneratorSource.base q)-i)^e (PaddedIntegralGeneratorSource.base q))
        (row P D H q) (col P D H q) : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)) := by
  have HP : request P D H N e (pair q (BinaryNatCode.encode i))=requestAt P D H N e q i :=
    congrArg₂ (requestAt P D H N e) (pairFst_pair q (BinaryNatCode.encode i))
      ((congrArg Nat.fromBitsLE (pairSnd_pair q (BinaryNatCode.encode i))).trans (Nat.fromBitsLE_bits i))
  rw [summand,Function.comp_apply,HP,requestAt]
  have HH := IntegralMixedFramedClearedMatrixPowerBits.value_packet P D H
    (PaddedIntegralGeneratorSource.base q) (PaddedIntegralGeneratorSource.modulus q)
    (BinaryNatCode.encode (N (PaddedIntegralGeneratorSource.base q)-i)) (e (PaddedIntegralGeneratorSource.base q))
    (row P D H q) (col P D H q)
  refine HH.trans ?_
  exact congrArg (fun j : ℕ=>residueBits
    ((matrix P D H (PaddedIntegralGeneratorSource.base q) j^e (PaddedIntegralGeneratorSource.base q))
      (row P D H q) (col P D H q) : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))
    (Nat.fromBitsLE_bits (N (PaddedIntegralGeneratorSource.base q)-i))

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (N e : List Bool → ℕ) (q : List Bool) := residueBits
  (matrixSum P D H N e (PaddedIntegralGeneratorSource.base q) (row P D H q) (col P D H q) : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    {N e : List Bool → ℕ} (hN : UnaryFn N) (he : BinaryFn e) : SpaceFunction (value P D H N e) := by
  have EC : BinaryFn (fun q=>N (PaddedIntegralGeneratorSource.base q)) := (BinaryFn.ofUnary hN).comp PaddedIntegralGeneratorSource.base_FP
  have EM := IntegralMixedFramedCompanionQueryBits.callerModulus_binary
  have ES := (IntegralMixedFramedClearedMatrixPowerBits.evaluator P a D H s hs hF hL).precompose
    (request P D H N e) (request_FP P a D H hN he)
  have EE := ModularSum.evaluatorWithModulus ES (fun q=>BinaryNatCode.encode (N (PaddedIntegralGeneratorSource.base q)))
    (fun q=>BinaryNatCode.encode (IntegralMixedFramedCompanionQueryBits.callerModulus q)) EC.bits_mem_FP EM.bits_mem_FP
    IntegralMixedFramedCompanionQueryBits.callerModulus (funext fun _=>Nat.fromBitsLE_bits _)
    (fun q i=>((matrix P D H (PaddedIntegralGeneratorSource.base q) (N (PaddedIntegralGeneratorSource.base q)-i)^e (PaddedIntegralGeneratorSource.base q))
      (row P D H q) (col P D H q) : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))
    (fun q=>by unfold IntegralMixedFramedCompanionQueryBits.callerModulus; omega)
    (fun q i _=>summand_packet P D H N e q i)
  exact EE.congr (funext fun q=>by
    simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits,value,matrixSum,Matrix.sum_apply,Int.cast_sum])

end LeanCanny.Algebra.IntegralMixedFramedClearedPowerSumBits
