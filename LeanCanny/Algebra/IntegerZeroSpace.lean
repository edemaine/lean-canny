/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerModular
public import LeanCanny.Algebra.MatrixPowerArithmeticFP
public import LeanCanny.Computation.BoundedScanPSPACE
public import LeanCanny.Encoding.BinaryAddFP

/-! # Integer zero testing from certified small-residue access

An FP binary writer supplies a bound B on the integer's magnitude bits. Scan
moduli one through 2*B+4, retaining only the counter and one residue child.
The bound and scan length may be exponential; neither is written in unary.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerZeroBits

open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets
open MatrixPower

def count (budget : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (BinaryNat.add (pair (budget c) (budget c))) (BinaryNatCode.encode 4))

theorem count_mem_FP {budget : List Bool → List Bool} (hb : budget ∈ FP) : count budget ∈ FP := by
  have hd := mem_FP_comp (mem_FP_pair hb hb) BinaryNat.add_mem_FP
  have h := mem_FP_comp (mem_FP_pair hd (constFn_mem_FP (BinaryNatCode.encode 4))) BinaryNat.add_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem count_code (budget : List Bool → List Bool) (c : List Bool) :
    count budget c = BinaryNatCode.encode (2 * Nat.fromBitsLE (budget c) + 4) := by
  simp only [count, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  congr 1
  omega

theorem residueZeroDecider {rho : List Bool → List Bool} (R : SpaceFunction rho) :
    SpaceDecider {q | rho q = []} := by
  have ha : (fun w : List Bool => [decide (w = [])]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  apply R.decider (fun w => decide (w = [])) ha
  intro q
  simp only [decide_eq_true_eq]
  rfl

theorem zeroLanguage_eq_scan (rho budget : List Bool → List Bool) (z : List Bool → ℤ)
    (hbudget : ∀ c, (z c).natAbs.size ≤ Nat.fromBitsLE (budget c))
    (hres : ∀ c (m : ℕ), 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = residueBits ((z c : ℤ) : ZMod m)) :
    {c | z c = 0} = BoundedScan.language {q | rho q = []} (fun c => 2 * Nat.fromBitsLE (budget c) + 4) := by
  ext c
  rw [Set.mem_ofPred_eq, IntegerModular.eq_zero_iff_residues _ _ (hbudget c)]
  have hpacket (k : ℕ) : rho (pair c (BinaryNatCode.encode k)) = [] ↔ (z c : ZMod (k + 1)) = 0 := by
    let : NeZero (k + 1) := ⟨by omega⟩
    have hr := hres c (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hr
    rw [hr]
    have hz : residueBits (0 : ZMod (k + 1)) = [] := by simp [residueBits, BinaryNatCode.encode]
    rw [← hz, (residueBits_injective _).eq_iff]
  change (∀ m : ℕ, 1 ≤ m → m ≤ 2 * Nat.fromBitsLE (budget c) + 4 → (z c : ZMod m) = 0) ↔
    ∀ k < 2 * Nat.fromBitsLE (budget c) + 4, rho (pair c (BinaryNatCode.encode k)) = []
  simp_rw [hpacket]
  constructor
  · intro h k hk
    exact h (k + 1) (by omega) (by omega)
  · intro h m hm hl
    have he := h (m - 1) (by omega)
    exact (Nat.sub_add_cancel hm) ▸ he

theorem zeroDecider {rho : List Bool → List Bool} (R : SpaceFunction rho)
    (budget : List Bool → List Bool) (hb : budget ∈ FP) (z : List Bool → ℤ)
    (hbudget : ∀ c, (z c).natAbs.size ≤ Nat.fromBitsLE (budget c))
    (hres : ∀ c (m : ℕ), 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = residueBits ((z c : ℤ) : ZMod m)) :
    SpaceDecider {c | z c = 0} := by
  let D := BoundedScan.decider (residueZeroDecider R) (count budget) (count_mem_FP hb)
    (fun c => 2 * Nat.fromBitsLE (budget c) + 4) (count_code budget)
  rw [zeroLanguage_eq_scan rho budget z hbudget hres]
  exact D

theorem zeroLanguage_mem_PSPACE {rho : List Bool → List Bool} (R : SpaceFunction rho)
    (budget : List Bool → List Bool) (hb : budget ∈ FP) (z : List Bool → ℤ)
    (hbudget : ∀ c, (z c).natAbs.size ≤ Nat.fromBitsLE (budget c))
    (hres : ∀ c (m : ℕ), 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = residueBits ((z c : ℤ) : ZMod m)) :
    {c | z c = 0} ∈ PSPACE := (zeroDecider R budget hb z hbudget hres).mem_PSPACE

end LeanCanny.Algebra.IntegerZeroBits
