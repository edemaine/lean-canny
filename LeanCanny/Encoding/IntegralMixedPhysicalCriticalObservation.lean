/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalBankNaturalPoint
public import LeanCanny.Geometry.IntegralMixedCriticalReadback
/-! # The same natural full tuple reads the old bank and new physical point

Every column is the literal oldest-first column of the creating critical
step. Saved-prefix bank observations therefore retain the old quotients.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalObservation
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (Plan family commands instruction keyAt prefixLength)
open IntegralMixedFramedPhysicalIndex (arity enumerate stepEquiv)
open IntegralMixedFramedCriticalSuccessorRows (tuple)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable local instance familyFintype (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    Fintype ((family P D H).physical key) :=
  inferInstanceAs (Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) (commands P D key)))

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (r : CriticalRule (P.ambient (pairFst key))) (z : ℕ→ℝ)

theorem tuple_old (i : (family P D H).physical key) :
    tuple P D H key r z (Sum.inl (Sum.inl i))=z (enumerate (commands P D key) i).val :=
  congrArg z (IntegralMixedFramedPhysicalIndex.step_old
    (.critical (P:=(family P D H).spatial key) (B:=P.width (pairFst key)) r)
    (enumerate (commands P D key)) i)

theorem tuple_ambient (i : Fin (P.ambient (pairFst key)+1)) :
    tuple P D H key r z (Sum.inl (FlatAffineCriticalStage.ambient i))=
      z (arity (commands P D key)+i.val) :=
  congrArg z (IntegralMixedFramedPhysicalIndex.criticalColumns_ambient
    (P:=(family P D H).spatial key) (B:=P.width (pairFst key)) r (enumerate (commands P D key)) i)

theorem point_ambient (i : Fin (P.ambient (pairFst key)+1)) :
    IntegralMixedCriticalReadback.point
      (S:=(family P D H).cap key) (B:=(family P D H).width key) (m:=(family P D H).birth key)
      (tuple P D H key r z) i=
      z (arity (commands P D key)+i.val)^UniformIntegralPowerSchedule.physical
        ((family P D H).cap key) (2^(family P D H).width key) ((family P D H).birth key) :=
  congrArg (fun t=>t^UniformIntegralPowerSchedule.physical
    ((family P D H).cap key) (2^(family P D H).width key) ((family P D H).birth key))
      (tuple_ambient P D H key r z i)

theorem old_observation (i : Fin ((family P D H).birth key)) :
    (IntegralMixedFullBankObservation.atFamily P D H key).point z i.val=
      IntegralMixedCanonicalBankPoint.point ((family P D H).state key)
        (fun j=>tuple P D H key r z (Sum.inl (Sum.inl (((family P D H).state key).sampler.scalar j)))) i :=by
  rw [IntegralMixedFullBankObservation.atFamily,IntegralMixedFullBankObservation.point_ofState]
  apply congrArg (fun f=>IntegralMixedCanonicalBankPoint.point ((family P D H).state key) f i)
  funext j
  exact (tuple_old P D H key r z _).symm

theorem new_observation (context : List Bool) (hb : prefixLength P key≤P.cap (pairFst key))
    (hc : (instruction P D key).command=.critical r) :
    (IntegralMixedFullBankObservation.atFamily P D H
      (keyAt (pairFst key) (prefixLength P key+1) context)).point z 0=
      IntegralMixedCanonicalBankPoint.point
        (criticalStep ((family P D H).state key) ((family P D H).birth_bound key) r)
        (fun j=>tuple P D H key r z
          ((criticalStep ((family P D H).state key) ((family P D H).birth_bound key) r).sampler.scalar j)) 0 :=by
  rw [IntegralMixedFullBankObservation.successor P D H key context hb r hc]
  exact IntegralMixedFullBankObservation.point_ofState _ _ z 0

theorem retained_observation (context : List Bool) (hb : prefixLength P key≤P.cap (pairFst key))
    (hc : (instruction P D key).command=.critical r) (i : Fin ((family P D H).birth key)) :
    (IntegralMixedFullBankObservation.atFamily P D H
      (keyAt (pairFst key) (prefixLength P key+1) context)).point z (i.val+1)=
      (IntegralMixedFullBankObservation.atFamily P D H key).point z i.val :=by
  rw [IntegralMixedFullBankObservation.successor P D H key context hb r hc]
  have HE:=IntegralMixedFullBankObservation.point_ofState
    (criticalStep ((family P D H).state key) ((family P D H).birth_bound key) r)
    (stepEquiv (.critical (P:=(family P D H).spatial key) (B:=P.width (pairFst key)) r)
      (enumerate (commands P D key))) z i.succ
  exact HE.trans ((IntegralMixedCanonicalBankPoint.critical_step_succ _ _ r (tuple P D H key r z) i).trans
    (old_observation P D H key r z i).symm)

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalObservation
