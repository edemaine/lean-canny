/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FermatLevelOriginalSpatial
public import LeanCanny.Algebra.ImplicitPowerResidueFP
/-! # Original binary exponents supply the level coefficient without an integer word -/
@[expose] public section
namespace LeanCanny.Algebra.FermatLevelPowerResidue
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFullCriticalDispatcherBits

def coefficient (E : List Bool → ℕ) (root : List Bool) : ℤ := 2 ^ E root

def modulusWord (P : Parameters) (q : List Bool) : List Bool := BinaryNatCode.encode (modulus P q - 1)

theorem modulusWord_FP (P : Parameters) (a : Access P) : modulusWord P ∈ FP :=
  ((modulus_binary P a).sub (BinaryFn.const 1)).bits_mem_FP

theorem residue_FP (P : Parameters) (a : Access P) (E : List Bool → ℕ) (hE : BinaryFn E) :
    (fun q => residueBits (coefficient E (RankedHistoryTask.root q) : ZMod (modulus P q))) ∈ FP := by
  have HE : BinaryFn (fun q => E (RankedHistoryTask.root q)) := hE.comp RankedHistoryTask.root_FP
  have H := ImplicitPowerResidue.power_two_mem_FP (fun q => BinaryNatCode.encode (E (RankedHistoryTask.root q)))
    (modulusWord P) HE.bits_mem_FP (modulusWord_FP P a)
  apply mem_FP_of_eq H
  intro q
  have HM : Nat.fromBitsLE (modulusWord P q) + 1 = modulus P q := by
    simp only [modulusWord, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have Hpos := modulus_ne_zero P q
    omega
  rw [HM]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, coefficient]

theorem controls (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (full : IntegralMixedFullHistoryFamilyBits.Metadata P D)
    (physical : IntegralMixedPhysicalQueryBits.InputMetadata (physicalFamily P D))
    (word : List Bool → List Bool) (hword : word ∈ FP) (hs : ∀ r, (ETR.TermView.term (word r)).arity ≤ P.ambient r)
    (E : List Bool → ℕ) (hE : BinaryFn E)
    (hlow : ∀ r, (D.spatial r).low = FermatLevelCoefficientBits.polynomial P.ambient
      (FermatLevelOriginalSpatialBits.old P word) (coefficient E) r) :
    IntegralMixedFullCriticalDispatcherBits.Controls P D :=
  FermatLevelOriginalSpatialBits.controls P a D full physical word hword hs (coefficient E) hlow
    (SpaceFunction.ofFP _ (residue_FP P a E hE))

end LeanCanny.Algebra.FermatLevelPowerResidue
