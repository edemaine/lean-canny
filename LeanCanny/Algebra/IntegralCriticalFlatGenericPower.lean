/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatGenericGrid
public import LeanCanny.Algebra.IntegralCriticalFlatFactor
public import LeanCanny.Algebra.MatrixPowerModularRecursiveStageLocal
/-! # Local flat product and factor powers for actual monomial sources

The matrix controller only requires replies for its current context and
typed matrix ranks. Product and factor adapters use the actual monomial
algebra; their native certificates require metadata and fresh writers.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatGenericPowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks

noncomputable def controller (P : IntegralCriticalHistoryTask.Parameters) {M : ModularFamily}
    (b : ModularAccess M) (p : IntegralCriticalHistoryTask.Phase) :=
  ModularRecursiveStage.stage b (IntegralCriticalFlatMatrixQuery.writer P p)

abbrev RepliesAt (P : IntegralCriticalHistoryTask.Parameters) (M : ModularFamily)
    (p : IntegralCriticalHistoryTask.Phase) (answer : List Bool → List Bool) (c : List Bool) : Prop :=
  ∀ i j : Fin (M.dimension c), answer (IntegralCriticalFlatMatrixQuery.writer P p
    (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits (M.matrix c i j)

theorem certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    {M : ModularFamily} (b : ModularAccess M) (hb : b.ControlsPolyTime) (p : IntegralCriticalHistoryTask.Phase) :
    (controller P b p).Certificates (encQ := encBits) (encS := encBits) :=
  ModularRecursiveStage.certificates b hb _ (IntegralCriticalFlatMatrixQuery.writer_FP P a p)

theorem halted_after_local (P : IntegralCriticalHistoryTask.Parameters) {M : ModularFamily}
    (b : ModularAccess M) (p : IntegralCriticalHistoryTask.Phase) (answer : List Bool → List Bool) (c : List Bool)
    (he : RepliesAt P M p answer c) :
    (controller P b p).halted (((controller P b p).reference answer)^[ModularRecursiveStage.clock M c]
      ((controller P b p).initial c)) = true :=
  ModularRecursiveStage.halted_after_local b _ answer c he

theorem output_when_halted_local (P : IntegralCriticalHistoryTask.Parameters) {M : ModularFamily}
    (b : ModularAccess M) (p : IntegralCriticalHistoryTask.Phase) (answer : List Bool → List Bool) (c : List Bool)
    (he : RepliesAt P M p answer c) (t : ℕ)
    (hh : (controller P b p).halted (((controller P b p).reference answer)^[t] ((controller P b p).initial c)) = true) :
    (controller P b p).output (((controller P b p).reference answer)^[t] ((controller P b p).initial c)) = M.value c :=
  ModularRecursiveStage.output_when_halted_local b _ answer c he t hh

theorem state_length_local (P : IntegralCriticalHistoryTask.Parameters) {M : ModularFamily}
    (b : ModularAccess M) (p : IntegralCriticalHistoryTask.Phase) (answer : List Bool → List Bool) (c : List Bool)
    (he : RepliesAt P M p answer c) (t : ℕ) :
    (((controller P b p).reference answer)^[t] ((controller P b p).initial c)).length ≤ ModularRecursiveStage.stateBound M c :=
  ModularRecursiveStage.state_length_local b _ answer c he t

theorem requests_in_bounds_local (P : IntegralCriticalHistoryTask.Parameters) {M : ModularFamily}
    (b : ModularAccess M) (p : IntegralCriticalHistoryTask.Phase) (answer : List Bool → List Bool) (c : List Bool)
    (he : RepliesAt P M p answer c) (budget : List Bool → ℕ) (child : List Bool)
    (hc : (controller P b p).Requests answer budget c child) :
    ∃ i j : Fin (M.dimension c), child = IntegralCriticalFlatMatrixQuery.writer P p
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) :=
  ModularRecursiveStage.requests_in_bounds_local b _ answer c he budget child hc

theorem requests_rank_local (P : IntegralCriticalHistoryTask.Parameters) {M : ModularFamily}
    (b : ModularAccess M) (p : IntegralCriticalHistoryTask.Phase) (answer : List Bool → List Bool) (c : List Bool)
    (he : RepliesAt P M p answer c) (budget : List Bool → ℕ) (child : List Bool)
    (hp : p.code < IntegralCriticalHistoryTask.phase c)
    (hc : (controller P b p).Requests answer budget c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨i, j, rfl⟩ := requests_in_bounds_local P b p answer c he budget child hc
  simpa only [pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_lower_rank P p
    (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) (by simpa only [pairFst_pair] using hp)

theorem requests_tasks_local (P : IntegralCriticalHistoryTask.Parameters) {M : ModularFamily}
    (b : ModularAccess M) (p : IntegralCriticalHistoryTask.Phase) (answer : List Bool → List Bool) (c : List Bool)
    (he : RepliesAt P M p answer c) (budget : List Bool → ℕ) (root child : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P root c)
    (hc : (controller P b p).Requests answer budget c child) : IntegralCriticalHistoryTask.Tasks P root child := by
  obtain ⟨i, j, rfl⟩ := requests_in_bounds_local P b p answer c he budget child hc
  apply IntegralCriticalFlatMatrixQuery.writer_tasks
  simpa only [pairFst_pair] using ht

noncomputable def productFamily (S : IntegralMonomialTermBits.Source) :=
  (IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family S)).power
noncomputable def productAccess (S : IntegralMonomialTermBits.Source) (b : IntegralMonomialTermBits.Access S) :
    ModularAccess (productFamily S) :=
  MatrixProductBits.powerAccess _ (IntegralPowerProductBits.productAccess _ (IntegralMonomialTermBits.familyAccess S b))
theorem product_controls (S : IntegralMonomialTermBits.Source) (b : IntegralMonomialTermBits.Access S) :
    (productAccess S b).ControlsPolyTime :=
  MatrixProductBits.RecursiveStage.power_controls _ (IntegralPowerProductBits.productAccess _ (IntegralMonomialTermBits.familyAccess S b))

noncomputable def productController (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralMonomialTermBits.Source)
    (b : IntegralMonomialTermBits.Access S) := controller P (productAccess S b) .productEntry

theorem product_value_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralMonomialTermBits.Source)
    (b : IntegralMonomialTermBits.Access S) (answer : List Bool → List Bool) (c : List Bool)
    (he : RepliesAt P (productFamily S) .productEntry answer c) (t : ℕ)
    (hh : (productController P S b).halted (((productController P S b).reference answer)^[t]
      ((productController P S b).initial c)) = true) :
    (productController P S b).output (((productController P S b).reference answer)^[t]
      ((productController P S b).initial c)) = S.value c :=
  (output_when_halted_local P (productAccess S b) .productEntry answer c he t hh).trans
    ((congrFun ((IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family S)).power_value) c).trans
      ((congrFun (IntegralPowerProductBits.product_value (IntegralMonomialTermBits.family S)) c).trans
        (congrFun (IntegralMonomialTermBits.family_value S) c)))

noncomputable def factorFamily (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralMonomialTermBits.Source) :=
  (IntegralPowerProductBits.powerFamily (IntegralMonomialTermBits.family S)).requery (IntegralCriticalFlatFactorQuery.input P)
noncomputable def factorAccess (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralMonomialTermBits.Source)
    (b : IntegralMonomialTermBits.Access S) : ModularAccess (factorFamily P S) :=
  (IntegralPowerProductBits.powerAccess _ (IntegralMonomialTermBits.familyAccess S b)).requery _ (IntegralCriticalFlatFactorQuery.input P)
theorem factor_controls (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralMonomialTermBits.Source) (b : IntegralMonomialTermBits.Access S) : (factorAccess P S b).ControlsPolyTime :=
  ModularAccess.requery_controls _ _ (IntegralPowerProductBits.power_controls _ (IntegralMonomialTermBits.familyAccess S b))
    _ (IntegralCriticalFlatFactorQuery.input_FP P a)
noncomputable def factorController (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralMonomialTermBits.Source)
    (b : IntegralMonomialTermBits.Access S) := controller P (factorAccess P S b) .monomialFactor

theorem factor_value_local (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralMonomialTermBits.Source)
    (b : IntegralMonomialTermBits.Access S) (answer : List Bool → List Bool) (c : List Bool)
    (he : RepliesAt P (factorFamily P S) .monomialFactor answer c) (t : ℕ)
    (hh : (factorController P S b).halted (((factorController P S b).reference answer)^[t]
      ((factorController P S b).initial c)) = true) :
    (factorController P S b).output (((factorController P S b).reference answer)^[t]
      ((factorController P S b).initial c)) =
      (IntegralPowerProductBits.powerFamily (IntegralMonomialTermBits.family S)).value (IntegralCriticalFlatFactorQuery.input P c) :=
  output_when_halted_local P (factorAccess P S b) .monomialFactor answer c he t hh

end LeanCanny.Algebra.IntegralCriticalFlatGenericPowerBits
