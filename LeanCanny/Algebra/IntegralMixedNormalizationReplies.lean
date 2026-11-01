/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationFactorOutside
/-! # Internal normalization replies are projections of one current model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizationTopBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    answer q = (machine P a F h hd height hb).model q

attribute [local irreducible] IntegralMixedNormalizationTopBits.value IntegralMixedNormalizationTopBits.source
  topPowerValue momentEntry momentValue factorValue zeroValue indexValue inverseValue inverseTermValue
  inverseMatrixValue productTermValue productValue

variable (P : Parameters) (a : Access P) (F : Family)
  (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
  (height : List Bool → ℕ) (hb : BinaryFn height) (answer : List Bool → List Bool)
  (hm : Matches P a F h hd height hb answer)
include a h hd height hb hm

theorem top : TopMatches P F answer := by
  intro q hv hr hp
  rw [hm q hv hr]
  exact model_selected_index P a F h hd height hb q ⟨0, by decide⟩
    ((selected_iff P .originalCoefficient q).mpr ⟨hv, hr, hp⟩)

theorem topPower : TopPowerMatches P F answer := by
  intro q hv hr hp
  rw [hm q hv hr]
  exact model_selected_index P a F h hd height hb q ⟨1, by decide⟩
    ((selected_iff P .derivativeCoefficient q).mpr ⟨hv, hr, hp⟩)

theorem entry : EntryMatches P F answer := by
  intro q hv hr hp
  rw [hm q hv hr]
  exact model_selected_index P a F h hd height hb q ⟨2, by decide⟩
    ((selected_iff P .clearedHeight q).mpr ⟨hv, hr, hp⟩)

theorem moment : MomentEntryMatches P F answer := by
  intro q hv hr hp
  rw [hm q hv hr]
  exact model_selected_index P a F h hd height hb q ⟨3, by decide⟩
    ((selected_iff P .monomialFactor q).mpr ⟨hv, hr, hp⟩)

theorem momentPower : MomentPowerMatches P F answer := by
  intro q hv hr hp
  rw [hm q hv hr]
  exact model_selected_index P a F h hd height hb q ⟨4, by decide⟩
    ((selected_iff P .factorPower q).mpr ⟨hv, hr, hp⟩)

theorem characteristic : CharacteristicMatches P F answer := by
  intro q hv hr hp
  rw [hm q hv hr]
  exact model_selected_index P a F h hd height hb q ⟨6, by decide⟩
    ((selected_iff P .productPower q).mpr ⟨hv, hr, hp⟩)

theorem zero : ZeroMatches P F answer := by
  intro q hv hr hp hg
  rw [hm q hv hr]
  exact model_selected_index P a F h hd height hb q ⟨7, by decide⟩
    ((selected7_iff P q).mpr ⟨hv, hr, hp, hg⟩)

theorem index : IndexMatches P F answer := by
  intro q hv hr hp hg
  rw [hm q hv hr]
  exact model_selected_index P a F h hd height hb q ⟨8, by decide⟩
    ((selected8_iff P F q).mpr ⟨hv, hr, hp, hg⟩)

theorem inverse : InverseMatches P F answer := by
  intro q hv hr hp hg
  rw [hm q hv hr]
  exact model_selected_index P a F h hd height hb q ⟨9, by decide⟩
    ((selected9_iff P F q).mpr ⟨⟨hv, hr, hp⟩, hg⟩)

theorem inverseTerm : InverseTermMatches P F answer := by
  intro q hv hr hp hg
  rw [hm q hv hr]
  exact model_selected_index P a F h hd height hb q ⟨10, by decide⟩
    ((selected10_iff P F q).mpr ⟨⟨hv, hr, hp⟩, hg⟩)

theorem inverseMatrix : InverseMatrixMatches P F answer := by
  intro q hv hr hp
  rw [hm q hv hr]
  exact model_selected_index P a F h hd height hb q ⟨11, by decide⟩
    ((selected_iff P .frozenConstant q).mpr ⟨hv, hr, hp⟩)

theorem productTerm : ProductTermMatches P F answer := by
  intro q hv hr hp hg
  rw [hm q hv hr]
  exact model_selected_index P a F h hd height hb q ⟨12, by decide⟩
    ((selected12_iff P F q).mpr ⟨⟨hv, hr, hp⟩, hg⟩)

theorem product : ProductMatches P F answer := by
  intro q hv hr hp hg
  rw [hm q hv hr]
  exact model_selected_index P a F h hd height hb q ⟨13, by decide⟩
    ((selected13_iff P F q).mpr ⟨⟨hv, hr, hp⟩, hg⟩)

theorem factor : FactorMatches P F answer := by
  intro q hv hr hp
  rw [hm q hv hr]
  exact model_factor P a F h hd height hb q hv hr hp

theorem replies (hr : RawMatches P F answer) : Replies P F answer where
  raw := hr
  top := top P a F h hd height hb answer hm
  topPower := topPower P a F h hd height hb answer hm
  entry := entry P a F h hd height hb answer hm
  moment := moment P a F h hd height hb answer hm
  momentPower := momentPower P a F h hd height hb answer hm
  factor := factor P a F h hd height hb answer hm
  characteristic := characteristic P a F h hd height hb answer hm
  zero := zero P a F h hd height hb answer hm
  index := index P a F h hd height hb answer hm
  inverse := inverse P a F h hd height hb answer hm
  inverseTerm := inverseTerm P a F h hd height hb answer hm
  inverseMatrix := inverseMatrix P a F h hd height hb answer hm
  productTerm := productTerm P a F h hd height hb answer hm
  product := product P a F h hd height hb answer hm


omit answer hm in
theorem correct_of_matches (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (hh : ∀ q, IntegralMixedVirtualCaps.valid P q → ∀ i j,
      (IntegralMixedNormalizationTopBits.top F (IntegralMixedVirtualTaskBits.saved P q) i j).natAbs ≤
        2 ^ height (RankedHistoryTask.root q))
    (hc : ∀ r, 2 * characteristicBudget P height r + 4 ≤ P.modulusBound r)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hn : Matches P a F h hd height hb (fun q => residueBits (x q)))
    (hr : RawMatches P F (fun q => residueBits (x q))) :
    Correct (machine P a F h hd height hb) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h hd g height hb hh hc x (replies P a F h hd height hb _ hn hr)

end LeanCanny.Algebra.IntegralMixedNormalizationDispatcherBits
