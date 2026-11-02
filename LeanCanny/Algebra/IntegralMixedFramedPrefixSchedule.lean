/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedDegreeSchedule

/-! # Every actual framed scalar prefix obeys the fixed degree schedule

A critical instruction adds extra physical variables, but its scalar-prefix
extension still has the same literal new-head row and degree schedule. This
does not assert a bijection with the larger physical variable set.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open IntegralMixedHistory IntegralHistorySampler UniformIntegralPrefix UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem scheduled_step_all (x : State P S B m ι) (H : Scheduled x.sampler) (hm : m≤S)
    (c : IntegralMixedFullHistoryScript.Command P B) :
    Scheduled (IntegralMixedFullHistoryScript.step x hm c).sampler := by
  intro i
  have HD := congrArg (fun Q : Prefix S (2^B) (m+1)=>Q.degrees i)
    (IntegralMixedFullHistoryScript.step_prefix x hm c)
  rw [HD]
  refine Fin.cases ?_ (fun j=>?_) i
  · change 2^B*birth S (2^B) m=2^B*weights S (2^B) (m+1) 0
    rw [head]
  · change x.sampler.scalarPrefix.degrees j=2^B*weights S (2^B) (m+1) j.succ
    rw [old]
    exact H j

theorem scheduled_run_all (initial : State P S B 0 ι) (cs : List (Instruction n B))
    (hcs : cs.length≤S+1) : Scheduled (run initial cs hcs).sampler := by
  induction cs with
  | nil => intro i; exact Fin.elim0 i
  | cons c cs ih =>
    exact scheduled_step_all (reframe (run initial cs (by simp only [List.length_cons] at hcs; omega))
      c.source c.source_cap) (ih (by simp only [List.length_cons] at hcs; omega)) _ c.command

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript
