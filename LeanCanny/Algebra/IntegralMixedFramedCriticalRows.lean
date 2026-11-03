/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalAncestry
public import LeanCanny.Algebra.PhysicalPowerCriticalCoefficients
/-! # Literal indexed new physical rows after a mixed critical birth

The full critical block survives the following scalar append. Its raw
variables have explicit oldest-first columns: old columns are fixed,
ambient coordinates follow them, then multipliers, then the fresh scalar.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
open IntegralMixedHistory IntegralMixedFullHistoryScript MvPolynomial
open IntegralHistorySampler FlatAffineCriticalStage UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m L : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def criticalColumns (r : CriticalRule n) (e : ι≃Fin L) :
    (ι⊕Variables (n+1))→Fin (L+added (.critical r : Command P B)) :=
  (stepEquiv (.critical r : Command P B) e)∘Sum.inl

theorem criticalColumns_injective (r : CriticalRule n) (e : ι≃Fin L) :
    Function.Injective (criticalColumns (P:=P) (B:=B) r e) :=
  (stepEquiv (.critical r : Command P B) e).injective.comp Sum.inl_injective

theorem criticalColumns_old (r : CriticalRule n) (e : ι≃Fin L) (i : ι) :
    (criticalColumns (P:=P) (B:=B) r e (Sum.inl i)).val=(e i).val :=
  step_old (.critical r : Command P B) e i

theorem criticalColumns_ambient (r : CriticalRule n) (e : ι≃Fin L) (i : Fin (n+1)) :
    (criticalColumns (P:=P) (B:=B) r e (ambient i)).val=L+i.val :=step_ambient r e i

theorem criticalColumns_multiplier (r : CriticalRule n) (e : ι≃Fin L) (i : Fin (n+2)) :
    (criticalColumns (P:=P) (B:=B) r e (multiplier i)).val=L+(n+1)+i.val :=
  (step_multiplier r e i).trans (Nat.add_assoc _ _ _).symm

theorem critical_scalar_final (r : CriticalRule n) (e : ι≃Fin L) :
    (stepEquiv (.critical r : Command P B) e (Sum.inr ())).val=L+block n :=by
  have H:=step_fresh (.critical r : Command P B) e
  change _=L+added (.critical r : Command P B)-1 at H
  have HE : L+added (.critical r : Command P B)-1=L+block n :=by
    simp only [added,Command.isCritical,ite_true]
    omega
  exact H.trans HE

theorem critical_row_index (r : CriticalRule n) (e : ι≃Fin L) (j : Variables (n+1)) :
    (stepEquiv (.critical r : Command P B) e (Sum.inl (Sum.inr j))).val=L+(criticalEquiv j).val :=by
  cases j <;> rfl

variable [Fintype ι]

theorem critical_new_row (x : State P S B m ι) (e : ι≃Fin L) (hm : m≤S) (r : CriticalRule n)
    (j : Variables (n+1)) :
    PolynomialSystemReindex.system (stepEquiv (.critical r : Command P B) e)
      (step x hm (.critical r)).sampler.rows
      (stepEquiv (.critical r : Command P B) e (Sum.inl (Sum.inr j)))=
    rename (criticalColumns (P:=P) (B:=B) r e)
      (PhysicalPowerCriticalRows.rows
        (FermatCriticalHomogenization.polynomial P.low P.leading P.degree) (data x hm r).frozen
        (PhysicalPowerCriticalRows.coordinateNormals 2 (data x hm r).scales (data x hm r).free)
        (historyHeights x.sampler (data x hm r).heights) (fun _=>1) P.degree (physical S (2^B) m) j) :=by
  simp only [PolynomialSystemReindex.system,Equiv.symm_apply_apply]
  change rename (stepEquiv (.critical r : Command P B) e)
    (rename Sum.inl (PhysicalPowerCriticalRows.rows
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree) (data x hm r).frozen
      (PhysicalPowerCriticalRows.coordinateNormals 2 (data x hm r).scales (data x hm r).free)
      (historyHeights x.sampler (data x hm r).heights) (fun _=>1) P.degree (physical S (2^B) m) j))=_
  exact rename_rename _ _ _
end LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
