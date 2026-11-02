/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FermatLevelFramedSpatial
public import LeanCanny.ETR.FixedLeadingTiltedSourceFP
/-! # Actual tilted LOW words from original terms and saved-birth selectors -/
@[expose] public section
namespace LeanCanny.Algebra.FermatLevelFramedTiltedSyntax
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open LeanCanny.ETR
open IntegralMixedFramedHistoryFamilyBits (Plan instruction)
open scoped Classical

def word (t : List Bool → Term) (k u : List Bool → ℕ) (key : List Bool) : List Bool :=
  FixedLeadingTiltedSourceFP.lowWord (k key) (t key).toData.size (u key) (t key)

theorem word_FP (t : List Bool → Term) (k u : List Bool → ℕ)
    (ht : (fun key => (t key).toData.toBits) ∈ FP) (hk : UnaryFn k) (hu : UnaryFn u) :
    word t k u ∈ FP :=
  FixedLeadingTiltedSourceFP.original_lowWord_FP ht hk hu

theorem word_scope (P : Parameters) (t : List Bool → Term) (k u : List Bool → ℕ)
    (ha : ∀ key, (t key).arity+1 ≤ FermatLevelFramedSpatialBits.ambient P key)
    (hu : ∀ key, u key+2 ≤ FermatLevelFramedSpatialBits.ambient P key) (key : List Bool) :
    (TermView.term (word t k u key)).arity ≤ FermatLevelFramedSpatialBits.ambient P key := by
  rw [word,FixedLeadingTiltedSourceFP.lowWord,TermView.term_toBits]
  exact (FixedLeadingTiltedSource.lowTerm_arity _ _ _ _).trans (max_le (ha key) (hu key))

noncomputable def low (P : Parameters) (t : List Bool → Term) (k u E : List Bool → ℕ)
    (key : List Bool) : MvPolynomial (Fin (FermatLevelFramedSpatialBits.ambient P key+1)) ℤ :=
  FermatLevelCoefficientBits.polynomial (FermatLevelFramedSpatialBits.ambient P)
    (fun key => (FixedLeadingTiltedSource.lowTerm (k key) (t key).toData.size (u key) (t key)).finitePolynomial
      (FermatLevelFramedSpatialBits.ambient P key)) (FermatLevelFramedSpatialBits.coefficient E) key

theorem word_polynomial (P : Parameters) (t : List Bool → Term) (k u E : List Bool → ℕ)
    (key : List Bool) :
    FermatLevelCoefficientBits.polynomial (FermatLevelFramedSpatialBits.ambient P)
      (FermatLevelFramedSpatialBits.old P (word t k u)) (FermatLevelFramedSpatialBits.coefficient E) key =
        low P t k u E key := by
  have HO : FermatLevelFramedSpatialBits.old P (word t k u) =
      fun z => (FixedLeadingTiltedSource.lowTerm (k z) (t z).toData.size (u z) (t z)).finitePolynomial
        (FermatLevelFramedSpatialBits.ambient P z) := by
    funext z
    rw [FermatLevelFramedSpatialBits.old,word,FixedLeadingTiltedSourceFP.lowWord,TermView.term_toBits]
  exact congrArg (fun p => FermatLevelCoefficientBits.polynomial (FermatLevelFramedSpatialBits.ambient P)
    p (FermatLevelFramedSpatialBits.coefficient E) key) HO

noncomputable def controls (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
    (t : List Bool → Term) (k u E : List Bool → ℕ)
    (hterm : (fun key => (t key).toData.toBits) ∈ FP) (hk : UnaryFn k) (hu : UnaryFn u) (hE : BinaryFn E)
    (ha : ∀ key, (t key).arity+1 ≤ FermatLevelFramedSpatialBits.ambient P key)
    (hs : ∀ key, u key+2 ≤ FermatLevelFramedSpatialBits.ambient P key)
    (hlow : ∀ key, (instruction P D key).source.low = low P t k u E key) :
    IntegralMixedFramedCriticalBits.Controls P D H :=
  FermatLevelFramedSpatialBits.controls P a D H T ht hr (word t k u) (word_FP t k u hterm hk hu)
    (word_scope P t k u ha hs) E hE (fun key => (hlow key).trans (word_polynomial P t k u E key).symm)

end LeanCanny.Algebra.FermatLevelFramedTiltedSyntax
