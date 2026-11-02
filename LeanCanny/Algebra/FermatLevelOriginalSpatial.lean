/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FermatLevelOriginalLeaves
/-! # Original-root term and charged level integer supply both critical leaves

Only the old LOW has a literal term word. The appended coefficient A is an
original residue source, charged in polynomial space. The saved root is
preserved, and the current task modulus remains the actual positive modulus.
-/
@[expose] public section
namespace LeanCanny.Algebra.FermatLevelOriginalSpatialBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFullCriticalDispatcherBits
open scoped Classical
attribute [local irreducible] IntegralMixedPhysicalOriginalBits.scalar IntegralMixedVirtualOriginalBits.scalar

noncomputable def old (P : Parameters) (word : List Bool → List Bool) (root : List Bool) :
    MvPolynomial (Fin (P.ambient root)) ℤ := (ETR.TermView.term (word root)).finitePolynomial (P.ambient root)

theorem physical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata (physicalFamily P D))
    (word : List Bool → List Bool) (hword : word ∈ FP) (hs : ∀ r, (ETR.TermView.term (word r)).arity ≤ P.ambient r)
    (A : List Bool → ℤ)
    (hlow : ∀ r, (D.spatial r).low = FermatLevelCoefficientBits.polynomial P.ambient (old P word) A r)
    (EA : SpaceFunction (fun q => residueBits (A (RankedHistoryTask.root q) : ZMod (modulus P q)))) :
    SpaceFunction (IntegralMixedPhysicalNativeLowerBits.originalScalar P (physicalFamily P D)) := by
  let F := IntegralMixedPhysicalTaskBits.family P (physicalFamily P D)
  let I := IntegralMixedPhysicalTaskBits.indices P (physicalFamily P D)
  have H := IntegralMixedPhysicalTaskBits.metadata P a (physicalFamily P D) h
  let saved := fun q => pairFst (IntegralMixedPhysicalTaskBits.saved P q)
  have HW : (fun q => word (saved q)) ∈ FP :=
    mem_FP_comp (mem_FP_comp (IntegralMixedPhysicalTaskBits.saved_FP P a) pairFst_mem_FP) hword
  apply FermatLevelOriginalBits.physical F I H (fun q => old P word (saved q)) (fun q => A (saved q))
  · intro q
    exact hlow _
  · apply IntegralOriginalTermCoefficientBits.evaluator F.ambient (fun q => (F.spatial q).degree.size) I.modulus
      H.ambient (IntegralMixedPhysicalCriticalBits.sourceWidth_unary F I H) H.modulus I.modulus_ne_zero
      (fun q => old P word (saved q)) (fun q => word (saved q)) HW
    · intro q
      exact hs _
    · intro q
      rfl
  · apply EA.congr
    funext q
    change residueBits (A (RankedHistoryTask.root q) : ZMod (modulus P q)) =
      residueBits (A (pairFst (IntegralMixedPhysicalTaskBits.saved P q)) : ZMod (modulus P q))
    rw [IntegralMixedOriginalSpatialTermBits.physical_saved_root]

theorem virtual (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullHistoryFamilyBits.Metadata P D)
    (word : List Bool → List Bool) (hword : word ∈ FP) (hs : ∀ r, (ETR.TermView.term (word r)).arity ≤ P.ambient r)
    (A : List Bool → ℤ)
    (hlow : ∀ r, (D.spatial r).low = FermatLevelCoefficientBits.polynomial P.ambient (old P word) A r)
    (EA : SpaceFunction (fun q => residueBits (A (RankedHistoryTask.root q) : ZMod (modulus P q)))) :
    SpaceFunction (IntegralMixedVirtualNativeLowerBits.originalScalar P (IntegralMixedFullHistoryFamilyBits.family P D)) := by
  let F := IntegralMixedVirtualTaskBits.family P (IntegralMixedFullHistoryFamilyBits.family P D)
  let I := IntegralMixedVirtualTaskBits.indices P (IntegralMixedFullHistoryFamilyBits.family P D)
  have H := IntegralMixedVirtualTaskBits.metadata P a (IntegralMixedFullHistoryFamilyBits.family P D)
    (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h)
  let saved := fun q => pairFst (IntegralMixedVirtualTaskBits.saved P q)
  have HW : (fun q => word (saved q)) ∈ FP :=
    mem_FP_comp (mem_FP_comp (IntegralMixedVirtualTaskBits.saved_FP P a) pairFst_mem_FP) hword
  apply FermatLevelOriginalBits.virtual F I H (fun q => old P word (saved q)) (fun q => A (saved q))
  · intro q
    exact hlow _
  · apply IntegralOriginalTermCoefficientBits.evaluator F.ambient (fun q => (F.spatial q).degree.size) I.modulus
      H.ambient (IntegralMixedVirtualNativeBits.sourceWidth_unary F I H) H.modulus I.modulus_ne_zero
      (fun q => old P word (saved q)) (fun q => word (saved q)) HW
    · intro q
      exact hs _
    · intro q
      rfl
  · apply EA.congr
    funext q
    change residueBits (A (RankedHistoryTask.root q) : ZMod (modulus P q)) =
      residueBits (A (pairFst (IntegralMixedVirtualTaskBits.saved P q)) : ZMod (modulus P q))
    rw [IntegralMixedFullHistoryFamilyBits.saved_root]

theorem controls (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (full : IntegralMixedFullHistoryFamilyBits.Metadata P D)
    (physicalMetadata : IntegralMixedPhysicalQueryBits.InputMetadata (physicalFamily P D))
    (word : List Bool → List Bool) (hword : word ∈ FP) (hs : ∀ r, (ETR.TermView.term (word r)).arity ≤ P.ambient r)
    (A : List Bool → ℤ)
    (hlow : ∀ r, (D.spatial r).low = FermatLevelCoefficientBits.polynomial P.ambient (old P word) A r)
    (EA : SpaceFunction (fun q => residueBits (A (RankedHistoryTask.root q) : ZMod (modulus P q)))) :
    IntegralMixedFullCriticalDispatcherBits.Controls P D where
  full := full
  physical := physicalMetadata
  physicalOriginal := physical P a D physicalMetadata word hword hs A hlow EA
  virtualOriginal := virtual P a D full word hword hs A hlow EA

end LeanCanny.Algebra.FermatLevelOriginalSpatialBits
