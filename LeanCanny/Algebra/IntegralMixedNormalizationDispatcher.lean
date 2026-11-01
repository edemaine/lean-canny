/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeCoefficient
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeMomentEntry
/-! # One native dispatcher for the actual mixed normalization arithmetic -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizationTopBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

structure Replies (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop where
  raw : RawMatches P F answer
  top : TopMatches P F answer
  topPower : TopPowerMatches P F answer
  entry : EntryMatches P F answer
  moment : MomentEntryMatches P F answer
  momentPower : MomentPowerMatches P F answer
  factor : FactorMatches P F answer
  characteristic : CharacteristicMatches P F answer
  zero : ZeroMatches P F answer
  index : IndexMatches P F answer
  inverse : InverseMatches P F answer
  inverseTerm : InverseTermMatches P F answer
  inverseMatrix : InverseMatrixMatches P F answer
  productTerm : ProductTermMatches P F answer
  product : ProductMatches P F answer

noncomputable def machine (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) : Machine :=
  (stage0 P a F hd).choose ((stage1 P a F h).choose ((stage2 P a F).choose ((stage3 P a F h).choose
    ((stage4 P a F h).choose ((stage5 P a F h).choose ((stage6 P a F h).choose
      ((stage7 P a F height hb).choose ((stage8 P a F h).choose ((stage9 P a F h).choose
        ((stage10 P a F h).choose ((stage11 P a F h).choose ((stage12 P a F h).choose
          ((stage13 P a F h).choose (stage14 P a F h hd))))))))))))))

private theorem right_selected (M N : Machine) (q : List Bool) (h : N.selected q = true) :
    (M.choose N).selected q = true := by
  change (M.selected q || N.selected q) = true
  rw [h, Bool.or_true]

theorem machine_selected (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) (q : List Bool) :
    (machine P a F h hd height hb).selected q = true := by
  unfold machine
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  exact stage14_selected P a F h hd q

attribute [local irreducible] stage0 stage1 stage2 stage3 stage4 stage5 stage6 stage7 stage8 stage9 stage10 stage11 stage12 stage13 stage14

theorem correct (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (height : List Bool → ℕ) (hb : BinaryFn height)
    (hh : ∀ q, IntegralMixedVirtualCaps.valid P q → ∀ i j,
      (top F (IntegralMixedVirtualTaskBits.saved P q) i j).natAbs ≤ 2 ^ height (RankedHistoryTask.root q))
    (hc : ∀ r, 2 * characteristicBudget P height r + 4 ≤ P.modulusBound r)
    (x : (q : List Bool) → ZMod (modulus P q)) (hx : Replies P F (fun q => residueBits (x q))) :
    Correct (machine P a F h hd height hb) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  unfold machine
  apply choose_correct _ _ _ _ (correct0 P a F hd g x hx.raw)
  apply choose_correct _ _ _ _ (correct1 P a F h g _ hx.top)
  apply choose_correct _ _ _ _ (correct2 P a F x hx.top)
  apply choose_correct _ _ _ _ (correct3 P a F h g x hx.entry)
  apply choose_correct _ _ _ _ (correct4 P a F h g _ hx.moment)
  apply choose_correct _ _ _ _ (correct5 P a F h g x hx.entry hx.momentPower)
  apply choose_correct _ _ _ _ (correct6 P a F h g _ hx.factor)
  apply choose_correct _ _ _ _ (correct7 P a F g height hb hh hc _ hx.characteristic)
  apply choose_correct _ _ _ _ (correct8 P a F h g _ hx.zero)
  apply choose_correct _ _ _ _ (correct9 P a F h g x hx.index hx.characteristic)
  apply choose_correct _ _ _ _ (correct10 P a F h x hx.inverse hx.topPower)
  apply choose_correct _ _ _ _ (correct11 P a F h g _ hx.inverseTerm)
  apply choose_correct _ _ _ _ (correct12 P a F h x hx.inverseMatrix hx.raw)
  apply choose_correct _ _ _ _ (correct13 P a F h g _ hx.productTerm)
  exact correct14 P a F h hd g x hx.index hx.characteristic hx.product

end LeanCanny.Algebra.IntegralMixedNormalizationDispatcherBits
