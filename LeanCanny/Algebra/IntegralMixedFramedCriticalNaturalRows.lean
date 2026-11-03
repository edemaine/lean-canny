/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowTransport
public import LeanCanny.Algebra.IntegralMixedFramedCriticalRows
/-! # A literal critical instruction exposes its new natural-indexed rows -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCriticalNaturalRows
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory MvPolynomial
open IntegralMixedFramedHistoryScript (Instruction run Index)
open IntegralMixedFramedPhysicalIndex (arity enumerate stepEquiv criticalEquiv)
open IntegralMixedFramedPhysicalRowTransport (natRows)
open FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B : ℕ} {Q : SpatialSource n}

noncomputable def criticalInstruction (P : SpatialSource n)
    (hP : PurePowerReductionBounds.dimension (n+1) P.degree≤2^B) (r : CriticalRule n) : Instruction n B :=⟨P,hP,.critical r⟩

theorem natRows_critical (initial : State Q S B 0 (Fin 0)) (cs : List (Instruction n B))
    (hc : cs.length≤S) (P : SpatialSource n) (hP : PurePowerReductionBounds.dimension (n+1) P.degree≤2^B)
    (r : CriticalRule n) (j : Variables (n+1)) :
    natRows initial (criticalInstruction P hP r::cs) (by simp only [List.length_cons];omega)
      (arity cs+(criticalEquiv j).val)=
    rename Fin.val (rename (IntegralMixedFramedPhysicalIndex.criticalColumns (P:=P) (B:=B) r (enumerate cs))
      (PhysicalPowerCriticalRows.rows
        (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)
        (data (reframe (run initial cs (hc.trans (by omega))) P hP) hc r).frozen
        (PhysicalPowerCriticalRows.coordinateNormals 2
          (data (reframe (run initial cs (hc.trans (by omega))) P hP) hc r).scales
          (data (reframe (run initial cs (hc.trans (by omega))) P hP) hc r).free)
        (IntegralHistorySampler.historyHeights (reframe (run initial cs (hc.trans (by omega))) P hP).sampler
          (data (reframe (run initial cs (hc.trans (by omega))) P hP) hc r).heights)
        (fun _=>1) P.degree (UniformIntegralPowerSchedule.physical S (2^B) cs.length) j)) := by
  let e:=stepEquiv (.critical r : IntegralMixedFullHistoryScript.Command P B) (enumerate cs)
  let i:=e (Sum.inl (Sum.inr j))
  have HI : i.val=arity cs+(criticalEquiv j).val:=IntegralMixedFramedPhysicalIndex.critical_row_index r (enumerate cs) j
  have HR : arity cs+(criticalEquiv j).val<arity (criticalInstruction P hP r::cs) :=by
    rw [←HI]
    exact i.isLt
  rw [natRows,dite_eq_left HR]
  have HE : (⟨arity cs+(criticalEquiv j).val,HR⟩ : Fin (arity (criticalInstruction P hP r::cs)))=i :=Fin.ext HI.symm
  rw [HE]
  exact congrArg (rename Fin.val)
    (IntegralMixedFramedPhysicalIndex.critical_new_row (reframe (run initial cs (hc.trans (by omega))) P hP)
      (enumerate cs) hc r j)

end LeanCanny.Algebra.IntegralMixedFramedCriticalNaturalRows
