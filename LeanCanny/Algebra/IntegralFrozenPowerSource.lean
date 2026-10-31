/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralClearedCoefficientSpace
public import LeanCanny.Encoding.FixedWidthQueryBinary

/-! # Original retained-height sources for frozen Fermat powers

One retained-height matrix reader computes each actual height power.
Only coordinates outside the free block contribute. The original integer
Fermat coefficient has its own modular reader; no signed expansion is
required for either the coefficient or the heights.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralFrozenPowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Source extends IntegralClearedCoefficientBits.Source where
  leading : List Bool → ℤ

structure Access (S : Source) extends IntegralClearedCoefficientBits.Access S.toSource where
  leading : List Bool → List Bool
  leading_eq : ∀ c, leading c = residueBits (S.leading c : ZMod (S.modulus c))

noncomputable def powerFamily (S : Source) : IntegralPowerProductBits.Family where
  rank p := S.rank (pairFst p)
  carrier p := S.carrier (pairFst p)
  ring p := S.ring (pairFst p)
  basis p := S.basis (pairFst p)
  factor p _ := S.height (pairFst p) (Nat.fromBitsLE (pairSnd p))
  exponent p _ := S.allowance (pairFst p)
  count _ := 1
  row p := S.row (pairFst p)
  col p := S.col (pairFst p)
  modulus p := S.modulus (pairFst p)
  modulus_ne_zero p := S.modulus_ne_zero (pairFst p)

def heightQuery (z : List Bool) : List Bool :=
  pair (pairFst (pairFst z)) (pair (BinaryNat.normalize (pairSnd (pairFst z))) (pairSnd (pairSnd z)))

theorem heightQuery_FP : heightQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP)
      (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))

theorem heightQuery_packet (p : List Bool) (s r t : ℕ) :
    heightQuery (pair p (pair (BinaryNatCode.encode s) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))) =
      pair (pairFst p) (pair (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd p)))
        (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))) := by
  simp only [heightQuery, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]

noncomputable def powerAccess (S : Source) (a : Access S) : IntegralPowerProductBits.Access (powerFamily S) where
  rank := a.rank.comp pairFst_mem_FP
  count := BinaryFn.const 1
  modulus := a.modulus.comp pairFst_mem_FP
  row := a.row.comp pairFst_mem_FP
  col := a.col.comp pairFst_mem_FP
  exponent := a.allowance.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  entry := a.height ∘ heightQuery
  entry_eq p s r t := by
    rw [Function.comp_apply, heightQuery_packet]
    exact a.height_eq (pairFst p) (Nat.fromBitsLE (pairSnd p)) r t

theorem power_evaluator (S : Source) (a : Access S) (EH : SpaceFunction a.height) : SpaceFunction (powerFamily S).value :=
  IntegralPowerProductBits.evaluator (powerFamily S) (powerAccess S a) (EH.precompose heightQuery heightQuery_FP)

theorem power_value (S : Source) (p : List Bool) :
    letI := S.ring (pairFst p)
    (powerFamily S).value p = residueBits ((Algebra.leftMulMatrix (S.basis (pairFst p))
      (S.height (pairFst p) (Nat.fromBitsLE (pairSnd p)) ^ S.allowance (pairFst p))
      (S.row (pairFst p)) (S.col (pairFst p)) : ℤ) : ZMod (S.modulus (pairFst p))) := by
  let := S.ring (pairFst p)
  change residueBits ((Algebra.leftMulMatrix (S.basis (pairFst p))
    (S.height (pairFst p) (Nat.fromBitsLE (pairSnd p)) ^ S.allowance (pairFst p) * 1)
    (S.row (pairFst p)) (S.col (pairFst p)) : ℤ) : ZMod (S.modulus (pairFst p))) = _
  rw [mul_one]

def freePosition (S : Source) (p : List Bool) : Prop :=
  S.offset (pairFst p) ≤ Nat.fromBitsLE (pairSnd p) ∧
    Nat.fromBitsLE (pairSnd p) < S.offset (pairFst p) + S.free (pairFst p)

instance (S : Source) (p : List Bool) : Decidable (freePosition S p) := inferInstanceAs (Decidable (_ ∧ _))

theorem freePosition_fppred (S : Source) (a : Access S) : FPPred (freePosition S) := by
  have HO : BinaryFn (fun p => S.offset (pairFst p)) := (BinaryFn.ofUnary a.offset).comp pairFst_mem_FP
  have HF : BinaryFn (fun p => S.free (pairFst p)) := (BinaryFn.ofUnary a.free).comp pairFst_mem_FP
  exact (HO.le (BinaryFn.fromBits pairSnd_mem_FP)).and ((BinaryFn.fromBits pairSnd_mem_FP).lt (HO.add HF))

noncomputable def termProgram (S : Source) (p : List Bool) : List Bool :=
  if freePosition S p then [] else (powerFamily S).value p

theorem term_evaluator (S : Source) (a : Access S) (EH : SpaceFunction a.height) : SpaceFunction (termProgram S) :=
  (SpaceFunction.branch (fun p => decide (freePosition S p)) (freePosition_fppred S a).flag_mem_FP
    (SpaceFunction.ofFP _ (constFn_mem_FP [])) (power_evaluator S a EH)).congr
      (funext fun _ => by simp only [termProgram, decide_eq_true_eq])

end LeanCanny.Algebra.IntegralFrozenPowerBits
