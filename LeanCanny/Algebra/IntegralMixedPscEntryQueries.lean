/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscEntrySource
/-! # Native PSC coefficient queries retain the producer and coordinate -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical
attribute [local irreducible] IntegralMixedVirtualQueryBits.matrixCoefficient

noncomputable def requestedCoefficient (P : Parameters) (F : Family) (q : List Bool) :=
  PrincipalDerivativeEntryRequest.coefficient (parameters P F) (packet P q)
theorem requestedCoefficient_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    BinaryFn (requestedCoefficient P F) :=
  (PrincipalDerivativeEntryRequest.coefficient_binary _ (controls P a F h)).comp (packet_FP P a)

def Request (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  PrincipalDerivativeEntryRequest.valid (parameters P F) (packet P q) ∧ get P .row q < rank P F q ∧ get P .col q < rank P F q
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (Request P F q) := inferInstanceAs (Decidable (_ ∧ _))
theorem request_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (Request P F) :=
  ((PrincipalDerivativeEntryRequest.valid_FP _ (controls P a F h)).comp (packet_FP P a)).and
    (((get_binary P a .row).lt (rank_binary P a F h)).and ((get_binary P a .col).lt (rank_binary P a F h)))

theorem requestedCoefficient_le (P : Parameters) (F : Family) (q : List Bool) (hr : Request P F q) :
    requestedCoefficient P F q ≤ degree P F q := by
  have H := PrincipalDerivativeEntryRequest.requested_degree_le (parameters P F) (packet P q) hr.1
  simpa only [packet_original, parameters, requestedCoefficient] using H

theorem requestedCoefficient_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hr : Request P F q) : requestedCoefficient P F q ≤ numericCap P (RankedHistoryTask.root q) :=
  (requestedCoefficient_le P F q hr).trans
    ((IntegralMixedValueTaskBounds.coordinateDegree_lt_scalar (IntegralMixedVirtualTaskBits.family P F) q).le.trans
      (IntegralMixedValueTaskBounds.scalar_le_root_cap P F g q))

noncomputable def query (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P id .critical .criticalCoefficient .coefficient (requestedCoefficient P F)
theorem query_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : query P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP _ _ _ _ (requestedCoefficient_binary P a F h)
theorem query_root (P : Parameters) (F : Family) (q : List Bool) :
    RankedHistoryTask.root (query P F q) = RankedHistoryTask.root q :=
  IntegralMixedValueFieldQuery.query_root P id _ _ _ _ q
theorem query_birth (P : Parameters) (F : Family) (q : List Bool) : birth P (query P F q) = birth P q :=
  IntegralMixedValueFieldQuery.query_birth P id _ _ _ _ q
theorem query_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P F q) = IntegralMixedVirtualTaskBits.saved P q :=
  IntegralMixedValueFieldQuery.query_saved P id _ _ _ _ q (by decide)
theorem query_modulus (P : Parameters) (F : Family) (q : List Bool) : modulus P (query P F q) = modulus P q :=
  IntegralMixedValueFieldQuery.query_modulus P id _ _ _ _ q (by decide)
theorem query_get (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hr : Request P F q) (f : Field) :
    get P f (query P F q) = if f = .slot14 then 1 else if f = .coefficient then requestedCoefficient P F q else get P f q := by
  rw [query, IntegralMixedValueFieldQuery.query_get]
  simp only [id_eq]
  rw [min_eq_left (requestedCoefficient_cap P F g q hr)]
  cases f <;> rfl

theorem query_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2) : IntegralMixedRoutineTaskBits.Frame P q (query P F q) := by
  exact IntegralMixedValueFieldQuery.query_frame_routine P id .critical .criticalCoefficient .coefficient
    (requestedCoefficient P F) q (by rw [show IntegralMixedRoutineTaskBits.routine P (id q) = 2 from hr]; decide)

noncomputable def coefficientValue (P : Parameters) (F : Family) (q : List Bool) : ℤ :=
  matrixCoefficient F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
    (requestedCoefficient P F q) (get P .row q) (get P .col q)
theorem child_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hr : Request P F q) :
    (IntegralMixedVirtualTaskBits.source P F).value (query P F q) = residueBits (coefficientValue P F q : ZMod (modulus P q)) := by
  rw [IntegralMixedVirtualTaskBits.value_snapshot, query_saved]
  simp only [IntegralMixedVirtualTaskBits.coordinate, query_get P F g q hr, reduceCtorEq, ite_false, ite_true]
  exact congrArg (fun m : ℕ => residueBits (coefficientValue P F q : ZMod m)) (query_modulus P F q)

end LeanCanny.Algebra.IntegralMixedPscEntryBits
