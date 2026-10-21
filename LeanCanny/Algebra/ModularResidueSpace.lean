/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionComposition
public import LeanCanny.Computation.SpaceFunctionBranch
public import LeanCanny.Algebra.ModularAddFP
public import LeanCanny.Algebra.ModularNegFP
public import LeanCanny.Algebra.ModularPowFP

/-! # Native space composition of coefficient residue computations

The modulus is a binary predecessor word. Original child costs are retained
while addition, negation, and multiplication combine their canonical residues.
-/

@[expose] public section

namespace LeanCanny.Algebra.ModularResidueSpace
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
attribute [local irreducible] ArithmeticBits.addMod ArithmeticBits.negate BinaryNat.mulMod BinaryNat.succ

variable (modulus : List Bool → List Bool)
abbrev m (c : List Bool) : ℕ := Nat.fromBitsLE (modulus c) + 1

def prepare (q : List Bool) : List Bool :=
  pair (BinaryNat.succ (modulus (pairFst q))) (pairSnd q)

theorem prepare_mem_FP (hm : modulus ∈ FP) : prepare modulus ∈ FP := by
  have h := mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) BinaryNat.succ_mem_FP) pairSnd_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

variable (a b : (c : List Bool) → ZMod (m modulus c))

theorem addEvaluator (hm : modulus ∈ FP)
    (A : SpaceFunction (fun c => residueBits (a c))) (B : SpaceFunction (fun c => residueBits (b c))) :
    SpaceFunction (fun c => residueBits (a c + b c)) := by
  let E := (A.pairOutputs B).withInput.postcompose (ArithmeticBits.addMod ∘ prepare modulus)
    (mem_FP_comp (prepare_mem_FP modulus hm) ArithmeticBits.addMod_mem_FP)
  refine E.congr (funext fun c => ?_)
  let : NeZero (m modulus c) := ⟨by unfold m; omega⟩
  simp only [Function.comp_apply, prepare, pairFst_pair, pairSnd_pair]
  rw [BinaryNat.succ_eq_bits]
  exact ArithmeticBits.addMod_residueBits _ _ _

theorem negEvaluator (hm : modulus ∈ FP) (A : SpaceFunction (fun c => residueBits (a c))) :
    SpaceFunction (fun c => residueBits (-a c)) := by
  let E := A.withInput.postcompose (ArithmeticBits.negate ∘ prepare modulus)
    (mem_FP_comp (prepare_mem_FP modulus hm) ArithmeticBits.negate_mem_FP)
  refine E.congr (funext fun c => ?_)
  let : NeZero (m modulus c) := ⟨by unfold m; omega⟩
  simp only [Function.comp_apply, prepare, pairFst_pair, pairSnd_pair]
  rw [BinaryNat.succ_eq_bits]
  exact ArithmeticBits.negate_residueBits _ _

theorem mulEvaluator (hm : modulus ∈ FP)
    (A : SpaceFunction (fun c => residueBits (a c))) (B : SpaceFunction (fun c => residueBits (b c))) :
    SpaceFunction (fun c => residueBits (a c * b c)) := by
  let E := (A.pairOutputs B).withInput.postcompose (BinaryNat.mulMod ∘ prepare modulus)
    (mem_FP_comp (prepare_mem_FP modulus hm) BinaryNat.mulMod_mem_FP)
  refine E.congr (funext fun c => ?_)
  let : NeZero (m modulus c) := ⟨by unfold m; omega⟩
  simp only [Function.comp_apply, prepare, pairFst_pair, pairSnd_pair]
  rw [BinaryNat.succ_eq_bits]
  exact ArithmeticBits.mulMod_residueBits _ _ _

theorem branchEvaluator (p : List Bool → Prop) (hp : FPPred p)
    (A : SpaceFunction (fun c => residueBits (a c))) (B : SpaceFunction (fun c => residueBits (b c))) :
    SpaceFunction (fun c => residueBits (if p c then a c else b c)) := by
  let E := SpaceFunction.branch (fun c => decide (p c)) hp.flag_mem_FP A B
  exact E.congr (funext fun c => by by_cases h : p c <;> simp [h])

end LeanCanny.Algebra.ModularResidueSpace
