/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CompactCoefficientSign
public import LeanCanny.Computation.BoundedScanPSPACE
public import LeanCanny.Algebra.IntegerModular

/-! # Polynomial-space zero testing of compactified coefficients

Scan the small moduli allowed by the proved coefficient magnitude budget.
Each modular query uses the complete compactification coefficient evaluator,
including the actual source-degree computation and both streamed loops.
-/

@[expose] public section

namespace LeanCanny.ETR.CompactCoefficient

open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets
open Algebra.MatrixPower

def residueZeroLanguage (source target : List Bool → List Bool) : Language :=
  {q | (coefficient source target (pairFst q) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) = 0}

theorem coefficient_lift (source target : List Bool → List Bool) (q : List Bool) :
    coefficient (source ∘ pairFst) (target ∘ pairFst) q = coefficient source target (pairFst q) := rfl

theorem residueZeroDecider (source target : List Bool → List Bool)
    (hs : source ∈ FP) (ht : target ∈ FP) : SpaceDecider (residueZeroLanguage source target) := by
  let R := evaluator (source ∘ pairFst) (target ∘ pairFst) pairSnd
    (mem_FP_comp pairFst_mem_FP hs) (mem_FP_comp pairFst_mem_FP ht) pairSnd_mem_FP
  have ha : (fun w : List Bool => [decide (w = [])]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  apply R.decider (fun w => decide (w = [])) ha
  intro q
  let : NeZero (Nat.fromBitsLE (pairSnd q) + 1) := ⟨by omega⟩
  change _ ↔ decide (value (source ∘ pairFst) (target ∘ pairFst) pairSnd q = []) = true
  rw [decide_eq_true_eq]
  have hz : residueBits (0 : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) = [] := by simp [residueBits, BinaryNatCode.encode]
  simp only [value, coefficient_lift]
  rw [← hz, (residueBits_injective _).eq_iff]
  rfl

def zeroScanCount (source : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNatCode.encode (2 * (CollectedCoefficient.dimension source c + 2 * CollectedCoefficient.dimension source c ^ 2 + 1) + 4)

theorem zeroScanCount_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : zeroScanCount source ∈ FP :=
  bits_mem_FP (((UnaryFn.const 2).mul (((CollectedCoefficient.dimension_unary hs).add
    ((UnaryFn.const 2).mul ((CollectedCoefficient.dimension_unary hs).pow_const 2))).add (UnaryFn.const 1))).add (UnaryFn.const 4))

theorem zeroLanguage_eq_scan (source target : List Bool → List Bool) :
    {c | coefficient source target c = 0} = BoundedScan.language (residueZeroLanguage source target)
      (fun c => 2 * (CollectedCoefficient.dimension source c + 2 * CollectedCoefficient.dimension source c ^ 2 + 1) + 4) := by
  ext c
  have hb := coefficient_bits source target c
  simp only [budget, BinaryNatCode.encode, Nat.fromBitsLE_bits] at hb
  rw [Set.mem_ofPred_eq, Algebra.IntegerModular.eq_zero_iff_residues _ _ hb]
  have hpacket (k : ℕ) : pair c (BinaryNatCode.encode k) ∈ residueZeroLanguage source target ↔
      (coefficient source target c : ZMod (k + 1)) = 0 := by
    change (coefficient source target (pairFst (pair c (BinaryNatCode.encode k))) :
      ZMod (Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode k))) + 1)) = 0 ↔ _
    rw [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  change (∀ m : ℕ, 1 ≤ m → m ≤ 2 * (CollectedCoefficient.dimension source c + 2 * CollectedCoefficient.dimension source c ^ 2 + 1) + 4 →
    (coefficient source target c : ZMod m) = 0) ↔
      ∀ k < 2 * (CollectedCoefficient.dimension source c + 2 * CollectedCoefficient.dimension source c ^ 2 + 1) + 4, pair c (BinaryNatCode.encode k) ∈ residueZeroLanguage source target
  simp_rw [hpacket]
  constructor
  · intro h k hk
    exact h (k + 1) (by omega) (by omega)
  · intro h m hm hl
    have he := h (m - 1) (by omega)
    exact (Nat.sub_add_cancel hm) ▸ he

theorem zeroDecider (source target : List Bool → List Bool)
    (hs : source ∈ FP) (ht : target ∈ FP) : SpaceDecider {c | coefficient source target c = 0} := by
  let D := BoundedScan.decider (residueZeroDecider source target hs ht) (zeroScanCount source)
    (zeroScanCount_mem_FP hs) (fun c => 2 * (CollectedCoefficient.dimension source c + 2 * CollectedCoefficient.dimension source c ^ 2 + 1) + 4) (fun _ => rfl)
  rw [zeroLanguage_eq_scan source target]
  exact D

theorem zeroLanguage_mem_PSPACE (source target : List Bool → List Bool)
    (hs : source ∈ FP) (ht : target ∈ FP) : {c | coefficient source target c = 0} ∈ PSPACE :=
  (zeroDecider source target hs ht).mem_PSPACE

end LeanCanny.ETR.CompactCoefficient
