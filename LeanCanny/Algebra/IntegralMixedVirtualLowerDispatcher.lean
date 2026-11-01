/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualNativeProductEntry
public import LeanCanny.Algebra.IntegralMixedVirtualNativeProductPower
public import LeanCanny.Algebra.IntegralMixedVirtualNativeGrid
public import LeanCanny.Algebra.IntegralMixedVirtualNativeFrozenPower
public import LeanCanny.Algebra.IntegralMixedVirtualNativeCoordinateProduct
/-! # One native dispatcher for the actual virtual lower arithmetic -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualLowerDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualNativeLowerBits NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Primitive (P : Parameters) (F : Family) := SpaceFunction (originalScalar P F)

structure Replies (P : Parameters) (F : Family) (reply : List Bool → List Bool) : Prop where
  derivative : ∀ q, selectedValid P .derivativeCoefficient q = true → DerivativeRepliesAt P F reply q
  monomial : ∀ q, selectedValid P .monomialFactor q = true → MonomialRepliesAt P F reply q
  factor : ∀ q, selectedValid P .factorPower q = true → FactorRepliesAt P F reply q
  productEntry : ∀ q, selectedValid P .productEntry q = true → ProductEntryRepliesAt P F reply q
  product : ∀ q, selectedValid P .productPower q = true → ProductRepliesAt P F reply q
  gridTerm : ∀ q, selectedValid P .originalGridTerm q = true → GridTermRepliesAt P F reply q
  grid : ∀ q, selectedValid P .clearedGridSum q = true → GridRepliesAt P F reply q
  frozenPower : ∀ q, selectedValid P .frozenPowerTerm q = true → FrozenPowerRepliesAt P F reply q
  frozenSum : ∀ q, selectedValid P .frozenPowerSum q = true → FrozenSumRepliesAt P F reply q
  frozenConstant : ∀ q, selectedValid P .frozenConstant q = true → FrozenConstantRepliesAt P F reply q
  frozenLower : ∀ q, selectedValid P .frozenLower q = true → FrozenLowerRepliesAt P F reply q
  coordinate : ∀ q, selectedValid P .coordinateGradientProduct q = true → CoordinateRepliesAt P F reply q
  sum : ∀ q, selectedValid P .eulerSum q = true → SumRepliesAt P F reply q
  objective : ∀ q, selectedValid P .eulerObjective q = true → ObjectiveRepliesAt P F reply q
  lower : ∀ q, selectedValid P .eulerLower q = true → LowerRepliesAt P F reply q
  height : ∀ q, selectedValid P .clearedHeight q = true →
    reply (IntegralMixedScalarQueryBits.virtualHeight P q) = height P F (IntegralMixedScalarQueryBits.virtualHeight P q)

noncomputable def stage0 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : Machine := originalMachine P a F h ha

noncomputable def stage1 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := derivativeMachine P a F h

noncomputable def stage2 (P : Parameters) (a : Access P) (F : Family) (_h : InputMetadata F) (_ha : Primitive P F) : Machine := heightMachine P a F

noncomputable def stage3 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := monomialMachine P a F h

noncomputable def stage4 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := factorMachine P a F h

noncomputable def stage5 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := productEntryMachine P a F h

noncomputable def stage6 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := productMachine P a F h

noncomputable def stage7 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := gridTermMachine P a F h

noncomputable def stage8 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := gridMachine P a F h

noncomputable def stage9 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := frozenPowerMachine P a F h

noncomputable def stage10 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := frozenSumMachine P a F h

noncomputable def stage11 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := frozenConstantMachine P a F h

noncomputable def stage12 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := frozenLowerMachine P a F h

noncomputable def stage13 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := coordinateMachine P a F h

noncomputable def stage14 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := sumMachine P a F h

noncomputable def stage15 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := objectiveMachine P a F h

noncomputable def stage16 (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (_ha : Primitive P F) : Machine := lowerMachine P a F h

noncomputable def inner (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : Machine :=
  (stage0 P a F h ha).choose ((stage1 P a F h ha).choose ((stage2 P a F h ha).choose ((stage3 P a F h ha).choose ((stage4 P a F h ha).choose ((stage5 P a F h ha).choose ((stage6 P a F h ha).choose ((stage7 P a F h ha).choose ((stage8 P a F h ha).choose ((stage9 P a F h ha).choose ((stage10 P a F h ha).choose ((stage11 P a F h ha).choose ((stage12 P a F h ha).choose ((stage13 P a F h ha).choose ((stage14 P a F h ha).choose ((stage15 P a F h ha).choose ((stage16 P a F h ha).choose (zero)))))))))))))))))

theorem right_selected (M N : Machine) (q : List Bool) (hn : N.selected q = true) : (M.choose N).selected q = true := by
  change (M.selected q || N.selected q) = true
  rw [hn, Bool.or_true]

theorem inner_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) (q : List Bool) :
    (inner P a F h ha).selected q = true := by
  unfold inner
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
  apply right_selected
  apply right_selected
  apply right_selected
  rfl

theorem inner_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool) (he : Replies P F reply) :
    Correct (inner P a F h ha) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  unfold inner
  apply choose_correct _ _ _ _ (original_correct P a F h ha reply)
  apply choose_correct _ _ _ _ (derivative_correct P a F h g reply he.derivative)
  apply choose_correct _ _ _ _ (height_correct P a F reply he.height)
  apply choose_correct _ _ _ _ (monomial_correct P a F h g reply he.monomial)
  apply choose_correct _ _ _ _ (factor_correct P a F h g reply he.factor)
  apply choose_correct _ _ _ _ (productEntry_correct P a F h g reply he.productEntry)
  apply choose_correct _ _ _ _ (product_correct P a F h g reply he.product)
  apply choose_correct _ _ _ _ (gridTerm_correct P a F h reply he.gridTerm)
  apply choose_correct _ _ _ _ (grid_correct P a F h g reply he.grid)
  apply choose_correct _ _ _ _ (frozenPower_correct P a F h g reply he.frozenPower)
  apply choose_correct _ _ _ _ (frozenSum_correct P a F h g reply he.frozenSum)
  apply choose_correct _ _ _ _ (frozenConstant_correct P a F h reply he.frozenConstant)
  apply choose_correct _ _ _ _ (frozenLower_correct P a F h reply he.frozenLower)
  apply choose_correct _ _ _ _ (coordinate_correct P a F h g reply he.coordinate)
  apply choose_correct _ _ _ _ (sum_correct P a F h g reply he.sum)
  apply choose_correct _ _ _ _ (objective_correct P a F h reply he.objective)
  apply choose_correct _ _ _ _ (lower_correct P a F h reply he.lower)
  exact zero_correct _ _

noncomputable def active (P : Parameters) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 1 ∧ phase q ≤ 16)

theorem active_FP (P : Parameters) (a : Access P) : (fun q => [active P q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 1)).and
      ((BinaryFn.ofUnary (RankedHistoryTask.phase_unary 27)).le (BinaryFn.const 16)))).flag_mem_FP

theorem active_iff (P : Parameters) (q : List Bool) : active P q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 1 ∧ phase q ≤ 16 := by simp only [active, decide_eq_true_eq]

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : Machine :=
  ((inner P a F h ha).withGuard (active P) (active_FP P a)).choose zero

theorem machine_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) (q : List Bool) :
    (machine P a F h ha).selected q = true := right_selected _ _ q rfl

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool) (he : Replies P F reply) :
    Correct (machine P a F h ha) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct _ _ _ _ ?_ (zero_correct _ _)
  exact withGuard_correct _ _ _ _ _ (inner_correct P a F h ha g reply he) (fun q _ => inner_selected P a F h ha q)

abbrev State (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) := (machine P a F h ha).State
noncomputable def encoding (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) := (machine P a F h ha).encoding
noncomputable def controller (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) := (machine P a F h ha).controller
noncomputable def clock (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) := (machine P a F h ha).clock
noncomputable def stateBound (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) := (machine P a F h ha).stateBound
noncomputable def model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) := (machine P a F h ha).model

theorem model_outside (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) (q : List Bool)
    (hq : active P q = false) : model P a F h ha q = [] := by
  change (if active P q then (inner P a F h ha).model q else []) = []
  rw [hq]
  rfl
end LeanCanny.Algebra.IntegralMixedVirtualLowerDispatcherBits
