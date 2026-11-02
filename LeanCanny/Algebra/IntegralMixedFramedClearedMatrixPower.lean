/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedClearedMatrixSpace
public import LeanCanny.Algebra.MatrixPowerSpaceEntries
/-! # Native powers of actual common-cleared old-bank matrices

The input pairs a cleared-matrix entry packet with a binary power. Existing
native matrix powering charges the actual old-height entry reader. All powers
use the same saved bank and exact original caller modulus.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedClearedMatrixPowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def powerFamily (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) : MatrixPower.ModularFamily where
  dimension q := IntegralMixedFramedClearedMatrixBits.rank P D H (PaddedIntegralGeneratorSource.base (pairFst q))
  modulus q := IntegralMixedFramedCompanionQueryBits.callerModulus (pairFst q)
  exponent q := Nat.fromBitsLE (pairSnd q)
  row q := IntegralMixedFramedClearedMatrixBits.row P D H (pairFst q)
  col q := IntegralMixedFramedClearedMatrixBits.col P D H (pairFst q)
  matrix q := (IntegralMixedFramedClearedMatrixBits.matrix P D H
    (PaddedIntegralGeneratorSource.base (pairFst q)) (IntegralMixedFramedClearedMatrixBits.index (pairFst q))).map
      (Int.castRingHom (ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus (pairFst q))))
  modulus_ne_zero q := by unfold IntegralMixedFramedCompanionQueryBits.callerModulus; omega

def request (z : List Bool) :=
  let p:=pairFst (pairFst z)
  pair (pair (PaddedIntegralGeneratorSource.base p) (PaddedIntegralGeneratorSource.modulus p))
    (pair (PaddedIntegralGeneratorSource.row p) (pairSnd z))

theorem request_FP : request∈FP := by
  have HP : (fun z : List Bool=>pairFst (pairFst z))∈FP :=
    mem_FP_comp (f := pairFst) (g := pairFst) pairFst_mem_FP pairFst_mem_FP
  exact mem_FP_pair (mem_FP_pair
    (mem_FP_comp (f := fun z=>pairFst (pairFst z)) (g := PaddedIntegralGeneratorSource.base) HP PaddedIntegralGeneratorSource.base_FP)
    (mem_FP_comp (f := fun z=>pairFst (pairFst z)) (g := PaddedIntegralGeneratorSource.modulus) HP PaddedIntegralGeneratorSource.modulus_FP))
    (mem_FP_pair (mem_FP_comp (f := fun z=>pairFst (pairFst z)) (g := PaddedIntegralGeneratorSource.row) HP PaddedIntegralGeneratorSource.row_FP) pairSnd_mem_FP)

noncomputable def entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :=
  IntegralMixedFramedClearedMatrixBits.value P D H ∘ request

noncomputable def access (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    MatrixPower.ModularAccess (powerFamily P D H) where
  dimension q := BinaryNatCode.encode ((powerFamily P D H).dimension q)
  modulus q := BinaryNatCode.encode ((powerFamily P D H).modulus q)
  exponent q := BinaryNatCode.encode ((powerFamily P D H).exponent q)
  row q := BinaryNatCode.encode ((powerFamily P D H).row q).val
  col q := BinaryNatCode.encode ((powerFamily P D H).col q).val
  entry := entry P D H
  dimension_eq _ := rfl
  modulus_eq _ := rfl
  exponent_eq _ := rfl
  row_eq _ := rfl
  col_eq _ := rfl
  entry_eq q r t := by
    simp only [entry,Function.comp_apply,request,pairFst_pair,pairSnd_pair]
    exact IntegralMixedFramedClearedMatrixBits.value_packet P D H
      (PaddedIntegralGeneratorSource.base (pairFst q)) (PaddedIntegralGeneratorSource.modulus (pairFst q))
      (PaddedIntegralGeneratorSource.row (pairFst q)) r t

theorem controls (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    (access P D H).ControlsPolyTime := by
  have HD : BinaryFn (powerFamily P D H).dimension :=
    (IntegralMixedFramedClearedMatrixBits.rank_binary P a D H).comp
      (mem_FP_comp (f := pairFst) (g := PaddedIntegralGeneratorSource.base) pairFst_mem_FP PaddedIntegralGeneratorSource.base_FP)
  have HM : BinaryFn (powerFamily P D H).modulus :=
    IntegralMixedFramedCompanionQueryBits.callerModulus_binary.comp pairFst_mem_FP
  have HR : BinaryFn (fun q=>((powerFamily P D H).row q).val) :=
    (IntegralMixedFramedClearedMatrixBits.row_binary P a D H).comp pairFst_mem_FP
  have HC : BinaryFn (fun q=>((powerFamily P D H).col q).val) :=
    (IntegralMixedFramedClearedMatrixBits.col_binary P a D H).comp pairFst_mem_FP
  exact ⟨HD.bits_mem_FP,HM.bits_mem_FP,(BinaryFn.fromBits pairSnd_mem_FP).bits_mem_FP,HR.bits_mem_FP,HC.bits_mem_FP⟩

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root) : SpaceFunction (powerFamily P D H).value :=
  MatrixPower.ModularAccess.evaluatorWithEntry (access P D H) (controls P a D H)
    ((IntegralMixedFramedClearedMatrixBits.evaluator P a D H s hs hF hL).precompose request request_FP)

noncomputable def integerEntry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i e r t : ℕ) : ℤ :=
  (IntegralMixedFramedClearedMatrixBits.matrix P D H key i^e)
    (IntegralMixedFramedClearedMatrixBits.wrap P D H key r) (IntegralMixedFramedClearedMatrixBits.wrap P D H key t)

theorem value_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    (powerFamily P D H).value q=residueBits (integerEntry P D H (PaddedIntegralGeneratorSource.base (pairFst q))
      (IntegralMixedFramedClearedMatrixBits.index (pairFst q)) (Nat.fromBitsLE (pairSnd q))
      (Nat.fromBitsLE (IntegralMixedFramedClearedMatrixBits.rowWord (pairFst q)))
      (Nat.fromBitsLE (IntegralMixedFramedClearedMatrixBits.colWord (pairFst q))) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus (pairFst q))) := by
  change residueBits (((IntegralMixedFramedClearedMatrixBits.matrix P D H
    (PaddedIntegralGeneratorSource.base (pairFst q)) (IntegralMixedFramedClearedMatrixBits.index (pairFst q))).map
      (Int.castRingHom (ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus (pairFst q)))) ^ Nat.fromBitsLE (pairSnd q))
      (IntegralMixedFramedClearedMatrixBits.row P D H (pairFst q)) (IntegralMixedFramedClearedMatrixBits.col P D H (pairFst q)))=_
  rw [←Matrix.map_pow,Matrix.map_apply]
  rfl

def packet (key mw iw : List Bool) (e r t : ℕ) :=
  pair (pair (pair key mw) (pair iw (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))) (BinaryNatCode.encode e)

theorem value_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key mw iw : List Bool) (e : ℕ) (r t : Fin (IntegralMixedFramedClearedMatrixBits.rank P D H key)) :
    (powerFamily P D H).value (packet key mw iw e r.val t.val)=
      residueBits ((IntegralMixedFramedClearedMatrixBits.matrix P D H key (Nat.fromBitsLE iw)^e) r t : ZMod (Nat.fromBitsLE mw+1)) := by
  rw [value_eq]
  have HE : integerEntry P D H (PaddedIntegralGeneratorSource.base (pairFst (packet key mw iw e r.val t.val)))
      (IntegralMixedFramedClearedMatrixBits.index (pairFst (packet key mw iw e r.val t.val)))
      (Nat.fromBitsLE (pairSnd (packet key mw iw e r.val t.val)))
      (Nat.fromBitsLE (IntegralMixedFramedClearedMatrixBits.rowWord (pairFst (packet key mw iw e r.val t.val))))
      (Nat.fromBitsLE (IntegralMixedFramedClearedMatrixBits.colWord (pairFst (packet key mw iw e r.val t.val))))=
      (IntegralMixedFramedClearedMatrixBits.matrix P D H key (Nat.fromBitsLE iw)^e) r t := by
    simp only [packet,PaddedIntegralGeneratorSource.base,PaddedIntegralGeneratorSource.row,PaddedIntegralGeneratorSource.col,
      IntegralMixedFramedClearedMatrixBits.index,IntegralMixedFramedClearedMatrixBits.rowWord,IntegralMixedFramedClearedMatrixBits.colWord,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    rw [integerEntry,
      show IntegralMixedFramedClearedMatrixBits.wrap P D H key r.val=r from Fin.ext (Nat.mod_eq_of_lt r.isLt),
      show IntegralMixedFramedClearedMatrixBits.wrap P D H key t.val=t from Fin.ext (Nat.mod_eq_of_lt t.isLt)]
  have HM : IntegralMixedFramedCompanionQueryBits.callerModulus (pairFst (packet key mw iw e r.val t.val))=Nat.fromBitsLE mw+1 := by
    simp only [packet,IntegralMixedFramedCompanionQueryBits.callerModulus,PaddedIntegralGeneratorSource.modulus,pairFst_pair,pairSnd_pair]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m)) HE HM

end LeanCanny.Algebra.IntegralMixedFramedClearedMatrixPowerBits
