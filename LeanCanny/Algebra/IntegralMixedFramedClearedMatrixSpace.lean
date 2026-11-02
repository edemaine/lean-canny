/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedClearedMatrix
/-! # Original syntax evaluates all common-cleared coordinate matrices

Packet: pair(pair savedKey modulusWord)(pair retainedIndex(pair row col)).
All matrices of a saved bank share one rank, and the caller modulus is exact.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedClearedMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def index (q : List Bool) := Nat.fromBitsLE (PaddedIntegralGeneratorSource.row q)
def rowWord (q : List Bool) := pairFst (PaddedIntegralGeneratorSource.col q)
def colWord (q : List Bool) := pairSnd (PaddedIntegralGeneratorSource.col q)

theorem index_binary : BinaryFn index := BinaryFn.fromBits PaddedIntegralGeneratorSource.row_FP
theorem rowWord_FP : rowWord∈FP := mem_FP_comp PaddedIntegralGeneratorSource.col_FP pairFst_mem_FP
theorem colWord_FP : colWord∈FP := mem_FP_comp PaddedIntegralGeneratorSource.col_FP pairSnd_mem_FP

noncomputable def row (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  wrap P D H (PaddedIntegralGeneratorSource.base q) (Nat.fromBitsLE (rowWord q))
noncomputable def col (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  wrap P D H (PaddedIntegralGeneratorSource.base q) (Nat.fromBitsLE (colWord q))

theorem row_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    BinaryFn (fun q=>(row P D H q).val) :=
  (BinaryFn.fromBits rowWord_FP).mod ((rank_binary P a D H).comp PaddedIntegralGeneratorSource.base_FP)
theorem col_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    BinaryFn (fun q=>(col P D H q).val) :=
  (BinaryFn.fromBits colWord_FP).mod ((rank_binary P a D H).comp PaddedIntegralGeneratorSource.base_FP)

noncomputable def request (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  packet (PaddedIntegralGeneratorSource.base q) (index q) (PaddedIntegralGeneratorSource.modulus q)
    (row P D H q).val (col P D H q).val

theorem request_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    request P D H∈FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_pair PaddedIntegralGeneratorSource.base_FP PaddedIntegralGeneratorSource.modulus_FP)
    (mem_FP_pair (row_binary P a D H).bits_mem_FP (col_binary P a D H).bits_mem_FP)) index_binary.bits_mem_FP

noncomputable def naturalEntry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i r t : ℕ) : ℤ := matrix P D H key i (wrap P D H key r) (wrap P D H key t)

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  residueBits (naturalEntry P D H (PaddedIntegralGeneratorSource.base q) (index q)
    (Nat.fromBitsLE (rowWord q)) (Nat.fromBitsLE (colWord q)) : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))

theorem value_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key mw iw : List Bool) (r t : Fin (rank P D H key)) :
    value P D H (pair (pair key mw) (pair iw (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))=
      residueBits (matrix P D H key (Nat.fromBitsLE iw) r t : ZMod (Nat.fromBitsLE mw+1)) := by
  let p:=pair (pair key mw) (pair iw (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HE : naturalEntry P D H (PaddedIntegralGeneratorSource.base p) (index p)
      (Nat.fromBitsLE (rowWord p)) (Nat.fromBitsLE (colWord p))=matrix P D H key (Nat.fromBitsLE iw) r t := by
    simp only [p,PaddedIntegralGeneratorSource.base,PaddedIntegralGeneratorSource.row,PaddedIntegralGeneratorSource.col,
      index,rowWord,colWord,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    rw [naturalEntry,show wrap P D H key r.val=r from Fin.ext (Nat.mod_eq_of_lt r.isLt),
      show wrap P D H key t.val=t from Fin.ext (Nat.mod_eq_of_lt t.isLt)]
  have HM : IntegralMixedFramedCompanionQueryBits.callerModulus p=Nat.fromBitsLE mw+1 := by
    simp only [p,IntegralMixedFramedCompanionQueryBits.callerModulus,PaddedIntegralGeneratorSource.modulus,pairFst_pair,pairSnd_pair]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m)) HE HM

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root) : SpaceFunction (value P D H) :=
  ((IntegralMixedFramedOldHeightQueryBits.evaluator P a D H s hs hF hL).precompose (request P D H)
    (request_FP P a D H)).congr (funext fun q =>
      finite_value P D H (PaddedIntegralGeneratorSource.base q) (PaddedIntegralGeneratorSource.modulus q)
        (index q) (row P D H q) (col P D H q))

end LeanCanny.Algebra.IntegralMixedFramedClearedMatrixBits
