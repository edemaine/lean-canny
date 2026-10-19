/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannySubresultantResidue
public import LeanCanny.Algebra.CannyResultantInteger
public import LeanCanny.Algebra.SubresultantRecoveryBounds

/-!
# Integer zero testing of Canny coordinate-recovery coefficients

The reduced-column subresultant bound is at most the full resultant budget.
The existing FP budget and scan-bound writers therefore suffice to certify
integer zero testing of each selected numerator or denominator coefficient.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannySubresultantBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation

structure BoundedFamily where
  source : CannyResultantBits.BoundedFamily
  coefficient : List Bool → ℕ

def BoundedFamily.family (F : BoundedFamily) : Family := ⟨F.source.source, F.coefficient⟩
def BoundedFamily.budget (F : BoundedFamily) : List Bool → ℕ := F.source.budget
def BoundedFamily.zeroLanguage (F : BoundedFamily) : Language := {c | F.family.integerCoefficient c = 0}

theorem BoundedFamily.coefficient_bits (F : BoundedFamily) (c : List Bool) :
    (F.family.integerCoefficient c).natAbs.size ≤ F.budget c := by
  have h := recoverySubresultant_coeff_coeff_size_le (F.source.source.left c) (F.source.source.right c)
    (F.source.source.direction c) (2 ^ F.source.leftBits c) (2 ^ F.source.rightBits c)
    (F.coefficient c) (F.source.source.degree c) (F.source.left_bound c) (F.source.right_bound c)
  have hb := Subresultant.budget_le_full (F.source.source.left c).natDegree (F.source.source.right c).natDegree
    1 (shiftBitBudget (F.source.source.left c).natDegree (F.source.source.direction c) (2 ^ F.source.leftBits c))
    (2 ^ F.source.rightBits c).size
  have he := h.trans hb
  simpa only [Family.integerCoefficient, family, budget, CannyResultantBits.BoundedFamily.budget,
    shiftBitBudget, Nat.size_pow, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he

structure IntegerAccess (F : BoundedFamily) where
  source : CannyResultantBits.IntegerAccess F.source
  coefficient : List Bool → List Bool
  coefficient_eq : ∀ c, coefficient c = BinaryNatCode.encode (F.coefficient c)

structure IntegerAccess.PolyTime {F : BoundedFamily} (a : IntegerAccess F) : Prop where
  source : a.source.PolyTime
  coefficient : a.coefficient ∈ FP

namespace IntegerAccess

def residue {F : BoundedFamily} (a : IntegerAccess F) : Access F.family :=
  ⟨a.source.residue, a.coefficient, a.coefficient_eq⟩

theorem residue_polyTime {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) : a.residue.PolyTime :=
  ⟨ha.source.residue, ha.coefficient⟩

theorem modular_packet (F : BoundedFamily) (c : List Bool) (k : ℕ) :
    pair c (BinaryNatCode.encode k) ∈ F.family.zeroLanguage ↔ (F.family.integerCoefficient c : ZMod (k + 1)) = 0 := by
  change (F.family.integerCoefficient (pairFst (pair c (BinaryNatCode.encode k))) :
    ZMod (CannyResultantBits.mValue (pair c (BinaryNatCode.encode k)))) = 0 ↔ _
  unfold CannyResultantBits.mValue
  rw [pairFst_pair, pairSnd_pair]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode k) = k from Nat.fromBitsLE_bits k]

theorem scan_language_eq (F : BoundedFamily) :
    BoundedScan.language F.family.zeroLanguage (fun c => 2 * F.budget c + 4) = F.zeroLanguage := by
  ext c
  change (∀ k < 2 * F.budget c + 4, pair c (BinaryNatCode.encode k) ∈ F.family.zeroLanguage) ↔
    F.family.integerCoefficient c = 0
  rw [IntegerModular.eq_zero_iff_residues (F.family.integerCoefficient c) (F.budget c) (F.coefficient_bits c)]
  constructor
  · intro h m hm hn
    have hr := (modular_packet F c (m - 1)).mp (h (m - 1) (by omega))
    rw [Nat.sub_add_cancel hm] at hr
    exact hr
  · intro h k hk
    exact (modular_packet F c k).mpr (h (k + 1) (by omega) (by omega))

noncomputable def decider {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) : SpaceDecider F.zeroLanguage := by
  rw [← scan_language_eq F]
  exact BoundedScan.decider (Access.decider a.residue (residue_polyTime a ha)) a.source.bound
    (a.source.bound_mem_FP ha.source) (fun c => 2 * F.budget c + 4) a.source.bound_code

theorem zeroLanguage_mem_PSPACE {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    F.zeroLanguage ∈ PSPACE := (decider a ha).mem_PSPACE

end IntegerAccess
end LeanCanny.Algebra.CannySubresultantBits
