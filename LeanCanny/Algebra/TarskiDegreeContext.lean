/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TarskiSeedDegreeSpace

/-! # Total source access with a retained head-degree word

An extended context pairs the original input with a binary degree. A positive
degree cap and coefficient truncation satisfy the source contracts even for
arbitrary metadata. At the computed head degree the truncation is the identity.
-/

@[expose] public section

namespace LeanCanny.Algebra.TarskiDegreeContext
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open IntegerTarskiSeedBits

def degree (x : List Bool) : List Bool := BinaryNat.succ (BinaryNat.pred (pairSnd x))

theorem degree_mem_FP : degree ∈ FP := by
  have h := mem_FP_comp (mem_FP_comp pairSnd_mem_FP BinaryNat.pred_mem_FP) BinaryNat.succ_mem_FP
  refine mem_FP_of_eq (g := degree) h ?_
  intro x
  simp only [degree, Function.comp_apply]

theorem degree_value (x : List Bool) : Nat.fromBitsLE (degree x) = Nat.fromBitsLE (pairSnd x) - 1 + 1 := by
  simp only [degree, BinaryNat.succ_eq_bits, BinaryNat.pred_eq_bits, Nat.fromBitsLE_bits]

noncomputable def family (F : Family) : Family where
  head x := PseudoRemainder.low (Nat.fromBitsLE (degree x) + 1) (F.head (pairFst x))
  query := F.query ∘ pairFst
  degree := degree
  queryBound := F.queryBound ∘ pairFst
  headMass := F.headMass ∘ pairFst
  queryMass := F.queryMass ∘ pairFst
  degree_pos x := by rw [degree_value]; omega
  head_degree x := by
    have h := PseudoRemainder.low_natDegree_lt (Nat.fromBitsLE (degree x) + 1) (F.head (pairFst x)) (by omega)
    omega
  query_degree x := F.query_degree (pairFst x)
  head_mass x := (PseudoRemainder.low_mass_le _ _).trans (F.head_mass (pairFst x))
  query_mass x := F.query_mass (pairFst x)

theorem controls (F : Family) (hF : ControlsPolyTime F) : ControlsPolyTime (family F) := by
  have hq := mem_FP_comp pairFst_mem_FP hF.queryBound
  have hp := mem_FP_comp pairFst_mem_FP hF.headMass
  have hf := mem_FP_comp pairFst_mem_FP hF.queryMass
  constructor
  · simpa only [family] using degree_mem_FP
  · simpa only [family] using hq
  · simpa only [family] using hp
  · simpa only [family] using hf

def sourceQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst q))) (pairSnd (pairFst q))) (pairSnd q)
def allowed (q : List Bool) : Prop :=
  Nat.fromBitsLE (pairSnd (pairFst q)) ≤ Nat.fromBitsLE (degree (pairFst (pairFst q)))
instance (q : List Bool) : Decidable (allowed q) := inferInstanceAs (Decidable (_ ≤ _))

theorem sourceQuery_mem_FP : sourceQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP
theorem allowed_fppred : FPPred allowed := by
  have hi := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hd := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) degree_mem_FP
  have h := BinaryNat.le_fppred hi hd
  refine h.of_iff (fun q => ?_)
  simp only [allowed, Function.comp_apply]

def headReader (f : List Bool → List Bool) (q : List Bool) : List Bool :=
  if allowed q then f (sourceQuery q) else []

theorem headEvaluator {f : List Bool → List Bool} (P : SpaceFunction f) :
    SpaceFunction (headReader f) := by
  let E := SpaceFunction.branch (fun q => decide (allowed q)) allowed_fppred.flag_mem_FP
    (P.precompose sourceQuery sourceQuery_mem_FP) (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine E.congr (funext fun q => ?_)
  simp only [headReader, Function.comp_apply, decide_eq_true_eq]

def access {F : Family} (a : Access F) : Access (family F) where
  headCoefficient := headReader a.headCoefficient
  queryCoefficient := a.queryCoefficient ∘ sourceQuery
  head_eq := by
    intro x k m hm
    have ha : allowed (pair (pair x (BinaryNatCode.encode k)) (BinaryNatCode.encode (m - 1))) ↔
        k ≤ Nat.fromBitsLE (degree x) := by
      simp only [allowed, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    simp only [headReader, ha, sourceQuery, pairFst_pair, pairSnd_pair, family,
      PseudoRemainder.low_coeff]
    by_cases hk : k ≤ Nat.fromBitsLE (degree x)
    · rw [ite_eq_left hk, a.head_eq _ _ _ hm, ite_eq_left (by omega)]
    · rw [ite_eq_right hk, ite_eq_right (by omega)]
      simp [integerResidue, MatrixPower.residueBits, BinaryNatCode.encode]
  query_eq := by
    intro x k m hm
    simpa only [Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair, family] using
      a.query_eq (pairFst x) k m hm

def prepared (F : Family) (c : List Bool) : List Bool :=
  pair c (BinaryNatCode.encode (F.head c).natDegree)

theorem prepared_degree (F : Family) (c : List Bool) (hp : 0 < (F.head c).natDegree) :
    Nat.fromBitsLE (degree (prepared F c)) = (F.head c).natDegree := by
  rw [degree_value]
  simp only [prepared, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  omega

theorem prepared_head (F : Family) (c : List Bool) : (family F).head (prepared F c) = F.head c := by
  simp only [family]
  rw [show pairFst (prepared F c) = c from pairFst_pair _ _]
  have hd : (F.head c).natDegree ≤ Nat.fromBitsLE (degree (prepared F c)) := by
    rw [degree_value]
    simp only [prepared, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    omega
  ext i
  rw [PseudoRemainder.low_coeff]
  by_cases hi : i < Nat.fromBitsLE (degree (prepared F c)) + 1
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

end LeanCanny.Algebra.TarskiDegreeContext
