/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedScan

/-! # Polynomial-space universal scans by native typed iteration -/

@[expose] public section

namespace LeanCanny.Computation.BoundedScan
open Complexity LeanCanny.Encoding Turing.MultiTapeTM
open scoped Classical

theorem decider {L : Language} (D : SpaceDecider L)
    (bound : List Bool → List Bool) (hb : bound ∈ FP) (N : List Bool → ℕ)
    (hbound : ∀ c, bound c = BinaryNatCode.encode (N c)) : SpaceDecider (language L N) := by
  let child := fun p : List Bool × ℕ × Bool =>
    p.2.2 && decide (pair p.1 (BinaryNatCode.encode p.2.1) ∈ L)
  have hc := ComputableTidilyInPolyTime.fst encBits (encPair encNat encBool)
  have hr := ComputableTidilyInPolyTime.snd encBits (encPair encNat encBool)
  have hquery := TidyFP.pair hc (TidyFP.natBits.comp hr.fst')
  have hchild : ComputableTidilyInPolySpace child
      (TidyBoundedFold.encPacket encBits encBool) encBool := by
    have hraw := (ComputableTidilyInPolySpace.of_polyTime hr.snd').ite
      (D.computable.comp (ComputableTidilyInPolySpace.of_polyTime hquery))
      (ComputableTidilyInPolySpace.of_polyTime (ComputableTidilyInPolyTime.const false))
    exact hraw.congr fun p => by
      apply Bool.eq_iff_iff.mpr
      cases hp : p.2.2 <;>
        simp [child, hp, BinaryNatCode.encode, Function.comp_apply]
      exact decide_eq_true_iff.symm
  have hfold (c : List Bool) (k : ℕ) :
      TidyBoundedFold.fold child (fun _ => true) c k = allBelow L c k := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [TidyBoundedFold.fold, child, allBelow, ih]
  have h := TidyBoundedFold.evaluator hchild
    (TidyFP.fromBitsLE.comp (TidyFP.of_mem_FP hb))
    (ComputableTidilyInPolySpace.of_polyTime (ComputableTidilyInPolyTime.const true))
    (B := fun _ => 1) (PolyBounded.const 1) (fun _ _ _ => by simp)
  apply SpaceDecider.of_computable h
  intro c
  simp only [Function.comp_apply]
  rw [hfold, hbound, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact (allBelow_correct L c (N c)).symm

theorem language_mem_PSPACE {L : Language} (D : SpaceDecider L)
    (bound : List Bool → List Bool) (hb : bound ∈ FP) (N : List Bool → ℕ)
    (hbound : ∀ c, bound c = BinaryNatCode.encode (N c)) : language L N ∈ PSPACE :=
  (decider D bound hb N hbound).mem_PSPACE

end LeanCanny.Computation.BoundedScan
