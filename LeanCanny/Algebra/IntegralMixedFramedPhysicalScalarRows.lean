/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralHistoryScalarRows
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalColumn
/-! # Every actual full framed sampler retains its literal scalar rows -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
open MvPolynomial IntegralMixedHistory IntegralHistorySampler IntegralMixedFullHistoryScript
open IntegralMixedFramedHistoryScript (Instruction run)
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open LeanCanny.Encoding IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem step_scalarRows (x : State P S B m ι) (hF : ScalarRows x.sampler)
    (hm : m≤S) (c : Command P B) : ScalarRows (IntegralMixedFullHistoryScript.step x hm c).sampler := by
  cases c with
  | integer p hp hd=>exact scalarStep_scalarRows x.sampler hF _ _ _ _
  | critical r=>exact scalarStep_scalarRows _ (criticalStep_scalarRows x.sampler hF _) _ _ _ _
  | cut r k d ha hd=>exact scalarStep_scalarRows x.sampler hF _ _ _ _

theorem run_scalarRows (initial : State P S B 0 (Fin 0))
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1) : ScalarRows (run initial cs hcs).sampler := by
  induction cs with
  | nil=>intro i; exact Fin.elim0 i
  | cons c cs ih=>
    have HT : cs.length≤S+1 := by simp only [List.length_cons] at hcs; omega
    have HM : cs.length≤S := by simp only [List.length_cons] at hcs; omega
    exact step_scalarRows (reframe (run initial cs HT) c.source c.source_cap) (ih HT) HM c.command

theorem family_scalarRows (p : Parameters) (d : Plan p)
    (h : IntegralMixedFramedHistoryFamilyBits.Data p d) (key : List Bool) :
    ScalarRows ((family p d h).state key).sampler := run_scalarRows _ _ _

theorem indexed_scalar_row (p : Parameters) (d : Plan p)
    (h : IntegralMixedFramedHistoryFamilyBits.Data p d) (key : List Bool)
    (i : Fin (commands p d key).length) :
    PolynomialSystemReindex.system (enumerate (commands p d key)) ((family p d h).state key).sampler.rows
      (enumerate (commands p d key) (((family p d h).state key).sampler.scalar i))=
      rename ((enumerate (commands p d key))∘((family p d h).state key).sampler.scalar)
        (((family p d h).state key).sampler.scalarPrefix.rows i) := by
  unfold PolynomialSystemReindex.system
  rw [Equiv.symm_apply_apply,family_scalarRows p d h key i]
  exact rename_rename _ _ _
end LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
