/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedGuardedLocalProgram
public import LeanCanny.Geometry.IntegralMixedFullBankPoint
public import LeanCanny.Algebra.IntegralMixedRelativeCutCoefficientIff
/-! # Constructed local traces satisfy the numerical guards at every birth

Critical births compare the selected physical block with their own retained
quotient. Cut births retain the interpreting hom, valid factor, exact degree,
and the constant-coefficient condition required when the fresh raw head is
zero. Old tuples are restricted literally at each preceding prefix.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedChosenLocalRealization IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]

noncomputable def BirthGuards (x :State P S B m ι) :
    (cs :List (Command P B))→(room :m+cs.length≤S+1)→(Index ι cs→ℝ)→Prop
  | [],_,_=>True
  | c::cs,room,y=>
    let hc :m+cs.length≤S+1:=by simp only [List.length_cons] at room;omega
    let hm :m+cs.length≤S:=by simp only [List.length_cons] at room;omega
    let before:=continueRun x cs hc
    BirthGuards x cs hc (y∘oldColumn c) ∧
    match c with
    | .integer _ _ _=>False
    | .critical r=>IntegralMixedFullBankPoint.point (step before hm (.critical r)) y 0=
        y (Sum.inl (FlatAffineCriticalStage.ambient
          (ClearedCoordinateCritical.freeIndex r.offset.val ((family before hm r).fit []).le
            ((family before hm r).coordinate []))))^physical S (2^B) (m+cs.length)
    | .cut r k d _ _=>
      ∃φ :before.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
        (∀i,φ (before.sampler.scalarPrefix.basis.generator i)=
          y (Sum.inl (before.sampler.scalar i))^weights S (2^B) (m+cs.length) i) ∧
        IntegralMixedRelativeCuts.Valid before hm r φ k ∧
        ((IntegralMixedRelativeCuts.factor before hm r k).map φ.toRingHom).natDegree=d ∧
        (y (Sum.inr ())=0→φ ((IntegralMixedRelativeCuts.factor before hm r k).coeff 0)=0)

private theorem full_continue_canonical (x :State P S B m ι) (H :Canonical x)
    (cs :List (Command P B)) (room :m+cs.length≤S+1) :Canonical (continueRun x cs room):=by
  induction cs with
  | nil=>exact H
  | cons c cs ih=>exact step_canonical _ (ih (by simp only [List.length_cons] at room;omega)) _ c

theorem GuardedProgram.birth_guards
    {x :State P S B m ι} {hn :0<n}
    {hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
    {z :ι→ℝ} {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values :Fin m→ℝ}
    {cs :List (Command P B)} {room :m+cs.length≤S+1} {codes :List (List Bool)}
    {y :Index ι cs→ℝ} {ψ :(continueRun x cs room).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ}
    {next :Fin (m+cs.length)→ℝ}
    (H :GuardedProgram x hn hcap z φ values cs room codes y ψ next)
    (HC :Canonical x)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i) :
    BirthGuards x cs room y:=by
  induction H with
  | nil=>exact True.intro
  | @cons cs room codes y ψ next tail hm a code r ih=>
    have HT :r.tuple∘oldColumn r.command=y:=funext r.old_raw
    have HB :Canonical (continueRun x cs room):=full_continue_canonical x HC cs room
    have HNEW :IntegralMixedFullBankPoint.point (step (continueRun x cs room) hm r.command) r.tuple 0=a:=
      (IntegralMixedCanonicalBankPoint.quotient_eq (step (continueRun x cs room) hm r.command)
        (step_canonical _ HB hm r.command) (r.tuple∘(step (continueRun x cs room) hm r.command).sampler.scalar)
        r.hom r.generators 0).symm.trans (r.quotients 0)
    refine ⟨?_,?_⟩
    · change BirthGuards x cs room (r.tuple∘oldColumn r.command)
      rw [HT]
      exact ih
    · obtain ⟨c,hdec,u,χ,hu,hold,hrestrict,hgen,hvals,hguard⟩:=r
      dsimp only at HNEW HT ⊢
      cases c with
      | integer _ _ _=>exact hguard.elim
      | critical r=>exact HNEW.trans hguard.symm
      | cut r k d ha hd=>
        refine ⟨ψ,?_,hguard.1,?_,?_⟩
        · intro i
          have HH:=hold ((continueRun x cs room).sampler.scalar i)
          change u (Sum.inl ((continueRun x cs room).sampler.scalar i))=y ((continueRun x cs room).sampler.scalar i) at HH
          rw [HH]
          exact tail.generators hφ i
        · exact hguard.2.1.symm
        · intro hz
          have HA :a=0:=by
            have HQ:=HNEW
            change u (Sum.inr ())^weights S (2^B) (m+cs.length+1) 0/
              ((step (continueRun x cs room) hm (.cut r k d ha hd)).bank.denominator 0:ℝ)=a at HQ
            have HPOWER :weights S (2^B) (m+cs.length+1) 0≠0:=by
              unfold weights
              exact Nat.ne_of_gt (birth_pos S (2^B) _)
            rw [hz,zero_pow HPOWER,zero_div] at HQ
            exact HQ.symm
          have HR:=hguard.2.2
          rw [HA,Polynomial.eval₂_at_zero] at HR
          exact HR

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
