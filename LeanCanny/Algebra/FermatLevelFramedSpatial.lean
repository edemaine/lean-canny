/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalDispatcher
public import LeanCanny.Algebra.FermatLevelOriginalLeaves
public import LeanCanny.Algebra.ImplicitPowerResidueFP
/-! # Saved-birth source records supply changing-source critical coefficients

The old LOW word and binary level exponent are indexed by the full saved
source key. The level integer is never serialized, and no interpreted matrix
or coefficient cost is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.FermatLevelFramedSpatialBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction)
open scoped Classical

def ambient (P : Parameters) (key : List Bool) := P.ambient (pairFst key)
noncomputable def old (P : Parameters) (word : List Bool → List Bool) (key : List Bool) :
    MvPolynomial (Fin (ambient P key)) ℤ :=
  (ETR.TermView.term (word key)).finitePolynomial (ambient P key)
def coefficient (E : List Bool → ℕ) (key : List Bool) : ℤ := 2 ^ E key
def modulusWord (P : Parameters) (q : List Bool) := BinaryNatCode.encode (modulus P q - 1)

theorem residue_FP (P : Parameters) (a : Access P) (saved : List Bool → List Bool) (hsaved : saved ∈ FP)
    (E : List Bool → ℕ) (hE : BinaryFn E) :
    (fun q => residueBits (coefficient E (saved q) : ZMod (modulus P q))) ∈ FP := by
  have HE : BinaryFn (fun q => E (saved q)) := hE.comp hsaved
  have HM : modulusWord P ∈ FP := ((modulus_binary P a).sub (BinaryFn.const 1)).bits_mem_FP
  have HP := ImplicitPowerResidue.power_two_mem_FP (fun q => BinaryNatCode.encode (E (saved q)))
    (modulusWord P) HE.bits_mem_FP HM
  apply mem_FP_of_eq HP
  intro q
  have Hmod : Nat.fromBitsLE (modulusWord P q) + 1 = modulus P q := by
    simp only [modulusWord, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have Hpos := modulus_ne_zero P q
    omega
  rw [Hmod]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, coefficient]

attribute [local irreducible] coefficient

theorem physical (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata (IntegralMixedFramedPhysicalBits.family P D H))
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ key, (ETR.TermView.term (word key)).arity ≤ ambient P key)
    (E : List Bool → ℕ) (hE : BinaryFn E)
    (hlow : ∀ key, (instruction P D key).source.low =
      FermatLevelCoefficientBits.polynomial (ambient P) (old P word) (coefficient E) key) :
    SpaceFunction (IntegralMixedPhysicalNativeLowerBits.originalScalar P
      (IntegralMixedFramedPhysicalBits.family P D H)) := by
  let F := IntegralMixedPhysicalTaskBits.family P (IntegralMixedFramedPhysicalBits.family P D H)
  let I := IntegralMixedPhysicalTaskBits.indices P (IntegralMixedFramedPhysicalBits.family P D H)
  have HM := IntegralMixedPhysicalTaskBits.metadata P a _ h
  let saved := IntegralMixedPhysicalTaskBits.saved P
  have HW : (fun q => word (saved q)) ∈ FP := mem_FP_comp (IntegralMixedPhysicalTaskBits.saved_FP P a) hword
  apply FermatLevelOriginalBits.physical F I HM (fun q => old P word (saved q)) (fun q => coefficient E (saved q))
  · intro q
    exact hlow _
  · apply IntegralOriginalTermCoefficientBits.evaluator F.ambient (fun q => (F.spatial q).degree.size) I.modulus
      HM.ambient (IntegralMixedPhysicalCriticalBits.sourceWidth_unary F I HM) HM.modulus I.modulus_ne_zero
      (fun q => old P word (saved q)) (fun q => word (saved q)) HW
    · intro q
      exact hs _
    · intro q
      rfl
  · have EA : SpaceFunction (fun q => residueBits (coefficient E (saved q) : ZMod (modulus P q))) :=
      SpaceFunction.ofFP _ (residue_FP P a saved (IntegralMixedPhysicalTaskBits.saved_FP P a) E hE)
    apply EA.congr
    funext q
    rfl

theorem virtual (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedVirtualQueryBits.InputMetadata (IntegralMixedFramedHistoryFamilyBits.family P D H))
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ key, (ETR.TermView.term (word key)).arity ≤ ambient P key)
    (E : List Bool → ℕ) (hE : BinaryFn E)
    (hlow : ∀ key, (instruction P D key).source.low =
      FermatLevelCoefficientBits.polynomial (ambient P) (old P word) (coefficient E) key) :
    SpaceFunction (IntegralMixedVirtualNativeLowerBits.originalScalar P
      (IntegralMixedFramedHistoryFamilyBits.family P D H)) := by
  let F := IntegralMixedVirtualTaskBits.family P (IntegralMixedFramedHistoryFamilyBits.family P D H)
  let I := IntegralMixedVirtualTaskBits.indices P (IntegralMixedFramedHistoryFamilyBits.family P D H)
  have HM := IntegralMixedVirtualTaskBits.metadata P a _ h
  let saved := IntegralMixedVirtualTaskBits.saved P
  have HW : (fun q => word (saved q)) ∈ FP := mem_FP_comp (IntegralMixedVirtualTaskBits.saved_FP P a) hword
  apply FermatLevelOriginalBits.virtual F I HM (fun q => old P word (saved q)) (fun q => coefficient E (saved q))
  · intro q
    exact hlow _
  · apply IntegralOriginalTermCoefficientBits.evaluator F.ambient (fun q => (F.spatial q).degree.size) I.modulus
      HM.ambient (IntegralMixedVirtualNativeBits.sourceWidth_unary F I HM) HM.modulus I.modulus_ne_zero
      (fun q => old P word (saved q)) (fun q => word (saved q)) HW
    · intro q
      exact hs _
    · intro q
      rfl
  · have EA : SpaceFunction (fun q => residueBits (coefficient E (saved q) : ZMod (modulus P q))) :=
      SpaceFunction.ofFP _ (residue_FP P a saved (IntegralMixedVirtualTaskBits.saved_FP P a) E hE)
    apply EA.congr
    funext q
    rfl

noncomputable def controls (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ key, (ETR.TermView.term (word key)).arity ≤ ambient P key)
    (E : List Bool → ℕ) (hE : BinaryFn E)
    (hlow : ∀ key, (instruction P D key).source.low =
      FermatLevelCoefficientBits.polynomial (ambient P) (old P word) (coefficient E) key) :
    IntegralMixedFramedCriticalBits.Controls P D H where
  tables := T
  native := ht
  represents := hr
  physicalOriginal := physical P a D H (IntegralMixedFramedPhysicalBits.inputMetadata P a D H T ht hr)
    word hword hs E hE hlow
  virtualOriginal := virtual P a D H (IntegralMixedFramedPhysicalBits.virtualInputMetadata P a D H T ht hr)
    word hword hs E hE hlow

end LeanCanny.Algebra.FermatLevelFramedSpatialBits
