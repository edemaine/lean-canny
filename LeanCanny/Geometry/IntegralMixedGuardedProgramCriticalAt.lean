/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedGuardedProgramCutAt
public import LeanCanny.Geometry.IntegralMixedGuardedProgramBirths
/-! # Each guarded critical birth retains its own selected powered coordinate -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedChosenLocalRealization IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]

noncomputable def selectedPhysical (x :State P S B m ι) (hm :m≤S) :
    (cmd :Command P B)→(NextIndex ι cmd→ℝ)→ℝ
  | .critical r,y=>y (Sum.inl (FlatAffineCriticalStage.ambient
      (ClearedCoordinateCritical.freeIndex r.offset.val ((family x hm r).fit []).le
        ((family x hm r).coordinate []))))^physical S (2^B) m
  | _,_=>0

noncomputable def CriticalGuardAt (x :State P S B m ι) (cs :List (Command P B))
    (room :m+cs.length≤S+1) (y :Index ι cs→ℝ) (i :ℕ) (hi :i<cs.length) :Prop:=
  let before:=continueRun x (cs.drop (i+1)) (cutAt_room cs room i)
  let hm:=cutAt_fit cs room i hi
  cs[i].isCritical=true→
    IntegralMixedFullBankPoint.point (step before hm cs[i]) (cutAtTuple cs i hi y) 0=
      selectedPhysical before hm cs[i] (cutAtTuple cs i hi y)

theorem BirthGuards.critical_at {x :State P S B m ι} {cs :List (Command P B)}
    {room :m+cs.length≤S+1} {y :Index ι cs→ℝ}
    (H :BirthGuards x cs room y) (i :ℕ) (hi :i<cs.length) :
    CriticalGuardAt x cs room y i hi:=by
  induction cs generalizing i with
  | nil=>simp only [List.length_nil] at hi;omega
  | cons c cs ih=>
    cases i with
    | zero=>
      cases c with
      | integer p hp hd=>intro hc;cases hc
      | critical r=>exact fun _=>H.2
      | cut r k d hs hd=>intro hc;cases hc
    | succ i=>
      have hc :m+cs.length≤S+1:=by simp only [List.length_cons] at room;omega
      have HT :BirthGuards x cs hc (y∘oldColumn c):=H.1
      exact ih HT i (by simpa using hi)

theorem GuardedProgram.critical_at
    {x :State P S B m ι} {hn :0<n}
    {hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
    {z :ι→ℝ} {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values :Fin m→ℝ}
    {cs :List (Command P B)} {room :m+cs.length≤S+1} {codes :List (List Bool)}
    {y :Index ι cs→ℝ} {ψ :(continueRun x cs room).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ}
    {next :Fin (m+cs.length)→ℝ}
    (G :GuardedProgram x hn hcap z φ values cs room codes y ψ next)
    (HC :Canonical x)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (i :ℕ) (hi :i<cs.length):CriticalGuardAt x cs room y i hi:=
  (G.birth_guards HC hφ).critical_at i hi

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
