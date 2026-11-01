/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ModularScalarFP
public import LeanCanny.Computation.SpaceFunctionChain
/-! # Charged space composition with a native positive modulus -/
@[expose] public section
namespace LeanCanny.Algebra.ModularScalarSpace
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryNat.mulMod BinaryNat.powMod

variable {m : List Bool → ℕ}

def multiplyPacket (m : List Bool → ℕ) (z : List Bool) : List Bool := pair (BinaryNatCode.encode (m (pairFst z))) (pairSnd z)

theorem multiplyPacket_FP (hm : BinaryFn m) : multiplyPacket m ∈ FP :=
  mem_FP_pair (hm.bits_mem_FP |> mem_FP_comp pairFst_mem_FP) pairSnd_mem_FP

theorem mul (hm : BinaryFn m) (x y : (c : List Bool) → ZMod (m c))
    (EX : SpaceFunction (fun c => residueBits (x c))) (EY : SpaceFunction (fun c => residueBits (y c))) :
    SpaceFunction (fun c => residueBits (x c * y c)) := by
  have E := (EX.pairOutputs EY).withInput.postcompose (BinaryNat.mulMod ∘ multiplyPacket m)
    (mem_FP_comp (multiplyPacket_FP hm) BinaryNat.mulMod_mem_FP)
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, multiplyPacket, pairFst_pair, pairSnd_pair]
  exact ArithmeticBits.mulMod_residueBits _ _ _

def powerPacket (m e : List Bool → ℕ) (z : List Bool) : List Bool :=
  pair (pairSnd z) (pair (BinaryNatCode.encode (e (pairFst z))) (BinaryNatCode.encode (m (pairFst z) - 1)))

theorem powerPacket_FP (hm : BinaryFn m) {e : List Bool → ℕ} (he : BinaryFn e) : powerPacket m e ∈ FP := by
  have HM : BinaryFn (fun z => m (pairFst z)) := hm.comp pairFst_mem_FP
  exact mem_FP_pair pairSnd_mem_FP (mem_FP_pair (mem_FP_comp pairFst_mem_FP he.bits_mem_FP) (HM.sub (BinaryFn.const 1)).bits_mem_FP)

theorem pow (hm : BinaryFn m) (hm0 : ∀ c, m c ≠ 0) (e : List Bool → ℕ) (he : BinaryFn e)
    (x : (c : List Bool) → ZMod (m c)) (EX : SpaceFunction (fun c => residueBits (x c))) :
    SpaceFunction (fun c => residueBits (x c ^ e c)) := by
  have E := EX.withInput.postcompose (BinaryNat.powMod ∘ powerPacket m e)
    (mem_FP_comp (powerPacket_FP hm he) BinaryNat.powMod_mem_FP)
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, powerPacket, pairFst_pair, pairSnd_pair]
  exact IntegralScaledCharacteristicBits.pow_residue _ _ (hm0 c) (x c)
end LeanCanny.Algebra.ModularScalarSpace
