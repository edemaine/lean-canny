/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOriginalSpatialTerm
public import LeanCanny.Algebra.IntegralOriginalTermCoefficientSpace
/-! # The same original term reader supplies both mixed critical backends

The saved task key retains its original root. Physical and virtual scalar
packets therefore read the same original integer coefficient, even though
the virtual backend has an additional formal nilpotent digit.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOriginalSpatialTermBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFullCriticalDispatcherBits


theorem physical_coefficient (F : IntegralMixedPhysicalCriticalBits.Family)
    (I : IntegralMixedPhysicalCriticalBits.Indices F) (q : List Bool) (k : ℕ) :
    IntegralMixedPhysicalOriginalBits.coefficient F I q k = (F.spatial q).low.coeff
      (RationalSubstitution.Indexed.exponentVector (F.ambient q + 1)
        (FixedWidthPolynomial.entry (F.spatial q).degree.size k)) := rfl

theorem virtual_coefficient (F : IntegralMixedCutSource.Family)
    (I : IntegralMixedVirtualSweepSource.Indices F) (q : List Bool) (k : ℕ) :
    IntegralMixedVirtualOriginalBits.coefficient F I q k = (F.spatial q).low.coeff
      (RationalSubstitution.Indexed.exponentVector (F.ambient q + 1)
        (FixedWidthPolynomial.entry (F.spatial q).degree.size k)) := rfl

theorem physical_source_scalar (F : IntegralMixedPhysicalCriticalBits.Family)
    (I : IntegralMixedPhysicalCriticalBits.Indices F) (p : List Bool) :
    IntegralMixedPhysicalOriginalBits.scalar F I p =
      residueBits (((F.spatial (pairFst p)).low.coeff
        (RationalSubstitution.Indexed.exponentVector (F.ambient (pairFst p) + 1)
          (FixedWidthPolynomial.entry (F.spatial (pairFst p)).degree.size (Nat.fromBitsLE (pairSnd p))))) :
        ZMod (I.modulus (pairFst p))) := by
  unfold IntegralMixedPhysicalOriginalBits.scalar
  rw [physical_coefficient]

theorem virtual_source_scalar (F : IntegralMixedCutSource.Family)
    (I : IntegralMixedVirtualSweepSource.Indices F) (p : List Bool) :
    IntegralMixedVirtualOriginalBits.scalar F I p =
      residueBits (((F.spatial (pairFst p)).low.coeff
        (RationalSubstitution.Indexed.exponentVector (F.ambient (pairFst p) + 1)
          (FixedWidthPolynomial.entry (F.spatial (pairFst p)).degree.size (Nat.fromBitsLE (pairSnd p))))) :
        ZMod (I.modulus (pairFst p))) := by
  unfold IntegralMixedVirtualOriginalBits.scalar
  rw [virtual_coefficient]

attribute [local irreducible] IntegralMixedPhysicalOriginalBits.scalar IntegralMixedVirtualOriginalBits.scalar scalar

theorem physical_family_evaluator (F : IntegralMixedPhysicalCriticalBits.Family)
    (I : IntegralMixedPhysicalCriticalBits.Indices F) (h : IntegralMixedPhysicalCriticalBits.Metadata F I)
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ q, (ETR.TermView.term (word q)).arity ≤ F.ambient q + 1)
    (hp : ∀ q, (ETR.TermView.term (word q)).finitePolynomial (F.ambient q + 1) = (F.spatial q).low) :
    SpaceFunction (IntegralMixedPhysicalOriginalBits.scalar F I) := by
  have E := IntegralOriginalTermCoefficientBits.evaluator (fun q => F.ambient q + 1)
    (fun q => (F.spatial q).degree.size) I.modulus (h.ambient.add (UnaryFn.const 1))
    (IntegralMixedPhysicalCriticalBits.sourceWidth_unary F I h) h.modulus I.modulus_ne_zero
    (fun q => (F.spatial q).low) word hword hs hp
  exact E.congr (funext fun p => (physical_source_scalar F I p).symm)

theorem virtual_family_evaluator (F : IntegralMixedCutSource.Family)
    (I : IntegralMixedVirtualSweepSource.Indices F) (h : IntegralMixedVirtualNativeBits.Metadata F I)
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ q, (ETR.TermView.term (word q)).arity ≤ F.ambient q + 1)
    (hp : ∀ q, (ETR.TermView.term (word q)).finitePolynomial (F.ambient q + 1) = (F.spatial q).low) :
    SpaceFunction (IntegralMixedVirtualOriginalBits.scalar F I) := by
  have E := IntegralOriginalTermCoefficientBits.evaluator (fun q => F.ambient q + 1)
    (fun q => (F.spatial q).degree.size) I.modulus (h.ambient.add (UnaryFn.const 1))
    (IntegralMixedVirtualNativeBits.sourceWidth_unary F I h) h.modulus I.modulus_ne_zero
    (fun q => (F.spatial q).low) word hword hs hp
  exact E.congr (funext fun p => (virtual_source_scalar F I p).symm)

theorem physical_saved_root (P : Parameters) (q : List Bool) :
    pairFst (IntegralMixedPhysicalTaskBits.saved P q) = RankedHistoryTask.root q := pairFst_pair _ _

theorem physical_evaluator (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata (physicalFamily P D))
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ r, (ETR.TermView.term (word r)).arity ≤ P.ambient r + 1)
    (hp : ∀ r, (ETR.TermView.term (word r)).finitePolynomial (P.ambient r + 1) = (D.spatial r).low) :
    SpaceFunction (IntegralMixedPhysicalNativeLowerBits.originalScalar P (physicalFamily P D)) := by
  apply physical_family_evaluator _ _ (IntegralMixedPhysicalTaskBits.metadata P a _ h)
    (fun q => word (RankedHistoryTask.root q)) (mem_FP_comp RankedHistoryTask.root_FP hword)
  · intro q
    change (ETR.TermView.term (word (RankedHistoryTask.root q))).arity ≤
      P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q)) + 1
    rw [physical_saved_root]
    exact hs _
  · intro q
    change (ETR.TermView.term (word (RankedHistoryTask.root q))).finitePolynomial
      (P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q)) + 1) =
      (D.spatial (pairFst (IntegralMixedPhysicalTaskBits.saved P q))).low
    rw [physical_saved_root]
    exact hp _

theorem virtual_evaluator (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullHistoryFamilyBits.Metadata P D)
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ r, (ETR.TermView.term (word r)).arity ≤ P.ambient r + 1)
    (hp : ∀ r, (ETR.TermView.term (word r)).finitePolynomial (P.ambient r + 1) = (D.spatial r).low) :
    SpaceFunction (IntegralMixedVirtualNativeLowerBits.originalScalar P (IntegralMixedFullHistoryFamilyBits.family P D)) := by
  apply virtual_family_evaluator _ _ (IntegralMixedVirtualTaskBits.metadata P a _ (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h))
    (fun q => word (RankedHistoryTask.root q)) (mem_FP_comp RankedHistoryTask.root_FP hword)
  · intro q
    change (ETR.TermView.term (word (RankedHistoryTask.root q))).arity ≤
      P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1
    rw [IntegralMixedFullHistoryFamilyBits.saved_root]
    exact hs _
  · intro q
    change (ETR.TermView.term (word (RankedHistoryTask.root q))).finitePolynomial
      (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1) =
      (D.spatial (pairFst (IntegralMixedVirtualTaskBits.saved P q))).low
    rw [IntegralMixedFullHistoryFamilyBits.saved_root]
    exact hp _

theorem controls (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (full : IntegralMixedFullHistoryFamilyBits.Metadata P D)
    (physical : IntegralMixedPhysicalQueryBits.InputMetadata (physicalFamily P D))
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ r, (ETR.TermView.term (word r)).arity ≤ P.ambient r + 1)
    (hp : ∀ r, (ETR.TermView.term (word r)).finitePolynomial (P.ambient r + 1) = (D.spatial r).low) :
    IntegralMixedFullCriticalDispatcherBits.Controls P D where
  full := full
  physical := physical
  physicalOriginal := physical_evaluator P a D physical word hword hs hp
  virtualOriginal := virtual_evaluator P a D full word hword hs hp

end LeanCanny.Algebra.IntegralMixedOriginalSpatialTermBits
