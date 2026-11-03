/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateHead
public import LeanCanny.Algebra.IntegralMixedCutNilpotent
public import LeanCanny.Algebra.IntegralMixedCoordinateCoefficientTasks
/-! # Full coordinate bounds use the one original auxiliary cap

The true Y degree is the relative dimension, not the retained algebra rank.
The parameter box is the existing scalar width. No actual degree or sign
oracle is introduced by these two native metadata functions.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSelectedCoordinateHead
open IntegralMixedHistory IntegralHistorySampler IntegralMixedExceptionalBounds Polynomial
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem parameter_bound (r : IntegralMixedCriticalSweep.Rule n)
    (hcap : auxiliaryCap (n+1) P.degree≤2^B) : IntegralMixedCriticalSweep.parameterDegree P.degree r≤2^B-1 :=by
  have H : IntegralMixedCriticalSweep.parameterDegree P.degree r≤E (n+1) P.degree:=
    IntegralMixedSweepBounds.parameterDegree_le P.degree r
  have HE : E (n+1) P.degree<auxiliaryCap (n+1) P.degree:=by unfold auxiliaryCap;omega
  omega

theorem selected_at_width (x : State P S B m ι) (hm : m≤S) (r : IntegralMixedCriticalSweep.Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : Fin m→ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=
      z i^UniformIntegralPowerSchedule.weights S (2^B) m i)
    (hcap : auxiliaryCap (n+1) P.degree≤2^B) :
    (head x hm r j (PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree) (2^B-1)).map
      (SelectedMultivariatePolynomialLift.evaluate (MvPolynomial.aeval z).toRingHom)=
        IntegralMixedCriticalSweep.selected x hm r j φ :=
  selected x hm r j _ _ φ z hφ le_rfl (parameter_bound r hcap)

noncomputable def fullDegree (P : Parameters) (F : IntegralMixedCutSource.Family)
    (parent : List Bool→List Bool) (q : List Bool) :=IntegralMixedCoordinateCoefficientTasks.choiceBound P F (parent q)-1

def fullParameter (P : Parameters) (parent : List Bool→List Bool) (q : List Bool) :=
  2^P.width (RankedHistoryTask.root (parent q))-1

theorem fullDegree_binary (P : Parameters) (a : Access P) (F : IntegralMixedCutSource.Family)
    (I : IntegralMixedVirtualQueryBits.InputMetadata F) (parent : List Bool→List Bool) (hp : parent∈FP) :
    BinaryFn (fullDegree P F parent) :=by
  have HC : BinaryFn (fun q=>IntegralMixedCoordinateCoefficientTasks.choiceBound P F (parent q)):=
    (IntegralMixedCoordinateCoefficientTasks.choiceBound_binary P a F I).comp hp
  exact HC.sub (BinaryFn.const 1)

theorem fullParameter_binary (P : Parameters) (a : Access P) (parent : List Bool→List Bool) (hp : parent∈FP) :
    BinaryFn (fullParameter P parent) :=
  ((BinaryFn.const 2).powUnary (a.width.comp (mem_FP_comp hp RankedHistoryTask.root_FP))).sub (BinaryFn.const 1)

end LeanCanny.Algebra.IntegralMixedSelectedCoordinateHead
