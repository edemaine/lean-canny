/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualProductEntryTransport
public import LeanCanny.Algebra.IntegralMixedVirtualNativeMonomial
public import LeanCanny.Algebra.IntegralMixedVirtualLayeredCanonical
/-! # Native actual virtual layered entries with only the adjacent child reply -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
noncomputable abbrev productEntryProgram (P : Parameters) (F : Family) :=
  IntegralCriticalFlatGenericProductEntryBits.program P (monomialSource P F)
noncomputable abbrev productEntryInput (P : Parameters) (F : Family) :=
  IntegralCriticalFlatGenericProductEntryBits.input P (monomialSource P F)
noncomputable abbrev productEntryFamily (P : Parameters) (F : Family) :=
  IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family (monomialSource P F))

abbrev ProductEntryRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  (productEntryProgram P F).request (productEntryInput P F q) = true →
    reply ((productEntryProgram P F).query (productEntryInput P F q)) =
      IntegralMixedVirtualFactorBits.power P F ((productEntryProgram P F).query (productEntryInput P F q))

theorem productEntry_value_at (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (he : ProductEntryRepliesAt P F reply q) :
    (productEntryProgram P F).value reply (productEntryInput P F q) = IntegralMixedVirtualLayeredBits.productEntry P F q := by
  have H := IntegralCriticalFlatGenericProductEntryBits.value_at P (monomialSource P F) (monomialAccess P a F h)
    (IntegralMixedVirtualFactorBits.power P F) q (IntegralMixedVirtualProductEntryBits.entry_replies P F g q hv)
  have HC : (productEntryProgram P F).value reply (productEntryInput P F q) =
      (productEntryProgram P F).value (IntegralMixedVirtualFactorBits.power P F) (productEntryInput P F q) := by
    unfold SingleCall.Program.value
    split_ifs with hr
    · rw [he hr]
    · rfl
  refine HC.trans (H.trans ?_)
  exact (IntegralCriticalActualLowMatrixModel.entryBits_fin
    ((IntegralCriticalFlatGenericPowerBits.productFamily (monomialSource P F)).matrix q)
    (IntegralCriticalFlatGenericProductEntryBits.index P (monomialSource P F) .row q)
    (IntegralCriticalFlatGenericProductEntryBits.index P (monomialSource P F) .col q)).symm

noncomputable def productEntryMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofPreparedSingleCall (productEntryProgram P F)
    ((productEntryProgram P F).certificates (IntegralCriticalFlatGenericProductEntryBits.controls P a (monomialSource P F) (monomialAccess P a F h)))
    (productEntryInput P F) (IntegralCriticalFlatGenericProductEntryBits.input_FP P a (monomialSource P F) (monomialAccess P a F h))
    (selectedValid P .productEntry) (selectedValid_FP P a .productEntry)
    (IntegralMixedVirtualLayeredBits.productEntry P F) (heightBound P) (heightBound_unary P a)

theorem productEntry_requests_frame (P : Parameters) (S : IntegralMonomialTermBits.Source)
    (reply : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool) (hp : isPhase .productEntry q)
    (hc : ((IntegralCriticalFlatGenericProductEntryBits.program P S).controller.prepare
      (IntegralCriticalFlatGenericProductEntryBits.input P S)).Requests reply budget q c) : IntegralMixedRoutineTaskBits.Frame P q c := by
  let C := IntegralCriticalFlatGenericProductEntryBits.program P S
  let I := IntegralCriticalFlatGenericProductEntryBits.input P S
  have H0 : C.controller.Requests reply (fun _ => budget q) (I q) c :=
    (RecursiveController.Controller.prepare_requests_iff C.controller I reply budget q c).mp hc
  have H1 := (C.requests_iff reply (fun _ => budget q) (I q) c).mp H0
  have HQ : C.query (I q) = IntegralCriticalFlatFactorQuery.writer P .factorPower
      (MatrixProductBits.factorQuery (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family S)) (I q)) := rfl
  have HO : pairFst (MatrixProductBits.factorQuery (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family S)) (I q)) = q := by
    simp only [MatrixProductBits.factorQuery, I, IntegralCriticalFlatGenericProductEntryBits.input, pairFst_pair]
  have HP : 4 < phase (pairFst (MatrixProductBits.factorQuery
      (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family S)) (I q))) := by
    rw [HO]
    change phase q = 5 at hp
    omega
  have HF := monomial_factor_frame P .factorPower
    (MatrixProductBits.factorQuery (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family S)) (I q)) HP
  rw [HO] at HF
  exact Eq.mpr (congrArg (IntegralMixedRoutineTaskBits.Frame P q) (H1.2.trans HQ)) HF

theorem productEntry_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selectedValid P .productEntry q = true → ProductEntryRepliesAt P F reply q) :
    Correct (productEntryMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofPreparedSingleCall_correct
  · intro q hq
    exact productEntry_value_at P a F h g reply q ((selectedValid_iff P .productEntry q).mp hq).1 (he q hq)
  · intro q hq hr
    have HV := productEntry_value_at P a F h g reply q ((selectedValid_iff P .productEntry q).mp hq).1 (he q hq)
    simp only [SingleCall.Program.value, hr, ite_true] at HV
    change pairSnd (pair _ _) = _ at HV
    rw [pairSnd_pair] at HV
    change (reply ((productEntryProgram P F).query (productEntryInput P F q))).length ≤ heightBound P q
    rw [HV]
    obtain ⟨z, hz⟩ := IntegralMixedVirtualCanonicalBits.productEntry_canonical P F q
    rw [← hz]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact residueBits_length_le _ _
  · intro q c budget hq hc
    exact productEntry_requests_frame P (monomialSource P F) reply budget q c
      ((selectedValid_iff P .productEntry q).mp hq).2.2 hc
end LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
