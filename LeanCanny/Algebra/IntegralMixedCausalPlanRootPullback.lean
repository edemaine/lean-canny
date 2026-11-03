/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalPlanHeaders
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackData
/-! # Root and caller-modulus pullback preserves the literal causal records

Only original context is projected. Serialization sees exactly the same old
prefixes, and thus computes the same current denominators for every cut.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalPlanBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (base : Plan P)
  (R : ∀root,List (IntegralMixedCausalRecordBits.Record (P.ambient root) (P.width root)))
  (hroom : ∀root,(R root).length+2≤P.cap root+1)
  (hn : ∀root,0<P.ambient root) (hd : ∀root,∀r∈R root,r.source.degree=P.degree root)
  (hW : ∀root,(P.degree root).size≤P.sourceWidth root)
  (project : List Bool→List Bool) (extra : List Bool→ℕ)

local notation "PP" => IntegralMixedFramedRootPullback.parameters P project extra
local notation "BB" => IntegralMixedFramedRootPullback.plan P base project extra

theorem plan_pullback :
    plan PP BB (fun root=>R (project root)) (fun root=>hroom (project root))=
      IntegralMixedFramedRootPullback.plan P (plan P base R hroom) project extra := rfl

theorem headerWords_pullback (root : List Bool) : headerWords PP (fun r=>R (project r)) root=
    headerWords P R (project root) := rfl

theorem modeWords_pullback (root : List Bool) : modeWords PP (fun r=>R (project r)) root=
    modeWords P R (project root) := rfl

private theorem transport_fallback {n m : ℕ} (S : SpatialSource n) (T : SpatialSource m)
    (hs : n=m) (he : HEq S T) (hn : 0<m) :
    IntegralMixedFramedRootPullback.transportSelection hs he (fallback T hn)=
      fallback S (by omega) := by
  cases hs
  cases eq_of_heq he
  rfl

theorem data_pullback :
    data PP BB (fun root=>R (project root)) (fun root=>hroom (project root))
      (fun root=>hn (project root)) (fun root=>hd (project root)) (fun root=>hW (project root))=
    IntegralMixedFramedRootPullback.data P (plan P base R hroom) (data P base R hroom hn hd hW) project extra := by
  unfold IntegralMixedFramedRootPullback.data data
  congr 1
  funext key
  exact (transport_fallback _ _ _ _ _).symm

theorem metadata_pullback (a : Access P) (hp : project∈FP) (he : BinaryFn extra)
    (hm : modeWords P R∈FP) : Metadata PP (fun root=>R (project root)) :=
  metadata PP (IntegralMixedFramedRootPullback.access P a project hp extra he) _
    (mem_FP_comp hp hm)

theorem tables_native_pullback (a : Access P) (hp : project∈FP) (he : BinaryFn extra)
    (hh : headerWords P R∈FP) : IntegralMixedHeaderTablesBits.Access (tables PP (fun root=>R (project root))) :=
  tables_native PP (IntegralMixedFramedRootPullback.access P a project hp extra he) _
    (mem_FP_comp hp hh)

end LeanCanny.Algebra.IntegralMixedCausalPlanBits
