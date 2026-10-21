/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerSignSpace
public import LeanCanny.Algebra.ModularNegFP
public import LeanCanny.Computation.SpaceFunctionChain

/-!
# Three-way integer signs from uniform residue access

Negating a canonical residue is FP. Applying the certified negativity algorithm
to an integer and its negation distinguishes zero, negative, and positive, with
canonical tags `[]`, `[true]`, and `[false,true]`. No full integer is computed.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerSignumBits

open LeanCanny.Encoding
open LeanCanny.Computation

def negateOutput (z : List Bool) : List Bool :=
  MatrixPower.ArithmeticBits.negate
    (pair (BinaryNat.succ (pairSnd (pairFst z))) (pairSnd z))

theorem negateOutput_mem_FP : negateOutput ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.succ_mem_FP
  have h := mem_FP_comp (mem_FP_pair hm pairSnd_mem_FP) MatrixPower.ArithmeticBits.negate_mem_FP
  refine mem_FP_of_eq (g := negateOutput) h ?_
  intro z
  simp only [Function.comp_apply, negateOutput]

def negatedResidue (rho : List Bool → List Bool) (q : List Bool) : List Bool := negateOutput (pair q (rho q))

theorem negatedResidueEvaluator {rho : List Bool → List Bool} (R : SpaceFunction rho) :
    SpaceFunction (negatedResidue rho) := by
  let E := R.withInput.postcompose negateOutput negateOutput_mem_FP
  refine E.congr (funext fun q => ?_)
  simp only [Function.comp_apply, negatedResidue]

theorem negatedResidue_packet (rho : List Bool → List Bool) (z : List Bool → ℤ)
    (hres : ∀ c (m : ℕ), 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((z c : ZMod m).val))
    (c : List Bool) (m : ℕ) (hm : 0 < m) :
    negatedResidue rho (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((-z c : ZMod m).val) := by
  let : NeZero m := ⟨hm.ne'⟩
  have hcode : BinaryNat.succ (BinaryNatCode.encode (m - 1)) = BinaryNatCode.encode m := by
    simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (by omega : 1 ≤ m)]
  rw [negatedResidue, hres c m hm]
  simp only [negateOutput, pairFst_pair, pairSnd_pair, hcode]
  simpa only [MatrixPower.residueBits, Int.cast_neg] using
    MatrixPower.ArithmeticBits.negate_residueBits m (z c : ZMod m)

def finish (p : List Bool) : List Bool :=
  if (pairSnd (pairFst p))[0]?.getD false then [true]
  else if (pairSnd p)[0]?.getD false then [false, true] else []

theorem finish_mem_FP : finish ∈ FP := by
  have h := (FPPred.getBit (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) (UnaryFn.const 0)).ite_mem_FP
    (constFn_mem_FP [true])
    ((FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0)).ite_mem_FP (constFn_mem_FP [false, true]) (constFn_mem_FP []))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem evaluator {rho : List Bool → List Bool} (R : SpaceFunction rho)
    (budget : List Bool → List Bool) (hb : budget ∈ FP) (z : List Bool → ℤ)
    (hbudget : ∀ c, (z c).natAbs.size ≤ Nat.fromBitsLE (budget c))
    (hres : ∀ c (m : ℕ), 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((z c : ZMod m).val)) :
    SpaceFunction (fun c => if z c = 0 then [] else if z c < 0 then [true] else [false, true]) := by
  let N := IntegerSignBits.evaluator R budget hb z hbudget hres
  let P := IntegerSignBits.evaluator (negatedResidueEvaluator R) budget hb (fun c => -z c)
    (by intro c; simpa only [Int.natAbs_neg] using hbudget c) (by
      intro c m hm
      simpa only [Int.cast_neg] using negatedResidue_packet rho z hres c m hm)
  let E := (N.withInput.chain ((P.precompose pairFst pairFst_mem_FP).withInput)).postcompose finish finish_mem_FP
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, finish, pairFst_pair, pairSnd_pair]
  by_cases hn : z c < 0
  · have hz : z c ≠ 0 := by omega
    simp [hn, hz]
  · by_cases hz : z c = 0
    · simp [hz]
    · have hp : 0 < z c := by omega
      simp [hn, hz, hp]

end LeanCanny.Algebra.IntegerSignumBits
