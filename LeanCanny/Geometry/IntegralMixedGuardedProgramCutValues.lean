/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedGuardedProgramCutAt
/-! # Every restricted creating tuple reads the final program's same bank values -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedChosenLocalRealization IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type}

def cutAtHeadIndex (m :ℕ) (cs :List (Command P B)) (i :ℕ) (hi :i<cs.length) :Fin (m+cs.length):=
  ⟨i,by omega⟩

def cutAtBeforeIndex (m :ℕ) (cs :List (Command P B)) (i :ℕ) (hi :i<cs.length)
    (j :Fin (m+(cs.drop (i+1)).length)) :Fin (m+cs.length):=
  ⟨i+1+j.val,by
    have H:=j.isLt
    have HL :(cs.drop (i+1)).length=cs.length-(i+1):=by simp only [List.length_drop]
    omega⟩

variable [Fintype ι]

noncomputable def CutAtValues (x :State P S B m ι) (cs :List (Command P B))
    (room :m+cs.length≤S+1) (y :Index ι cs→ℝ) (next :Fin (m+cs.length)→ℝ)
    (i :ℕ) (hi :i<cs.length) :Prop:=
  let before:=continueRun x (cs.drop (i+1)) (cutAt_room cs room i)
  let u:=cutAtTuple cs i hi y
  IntegralMixedFullBankPoint.point (step before (cutAt_fit cs room i hi) cs[i]) u 0=
      next (cutAtHeadIndex m cs i hi) ∧
    ∀j :Fin (m+(cs.drop (i+1)).length),
      IntegralMixedFullBankPoint.point before (u∘oldColumn cs[i]) j=
        next (cutAtBeforeIndex m cs i hi j)

private theorem values_continue_canonical (x :State P S B m ι) (H :Canonical x)
    (cs :List (Command P B)) (room :m+cs.length≤S+1) :Canonical (continueRun x cs room):=by
  induction cs with
  | nil=>exact H
  | cons c cs ih=>exact step_canonical _ (ih (by simp only [List.length_cons] at room;omega)) _ c

theorem GuardedProgram.cut_at_values
    {x :State P S B m ι} {hn :0<n}
    {hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
    {z :ι→ℝ} {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values :Fin m→ℝ}
    {cs :List (Command P B)} {room :m+cs.length≤S+1} {codes :List (List Bool)}
    {y :Index ι cs→ℝ} {ψ :(continueRun x cs room).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ}
    {next :Fin (m+cs.length)→ℝ}
    (H :GuardedProgram x hn hcap z φ values cs room codes y ψ next)
    (HC :Canonical x)
    (hφ :∀j,φ (x.sampler.scalarPrefix.basis.generator j)=z (x.sampler.scalar j)^weights S (2^B) m j)
    (hv :∀j,φ (x.bank.numerator j)/(x.bank.denominator j:ℝ)=values j)
    (i :ℕ) (hi :i<cs.length) :CutAtValues x cs room y next i hi:=by
  induction H generalizing i with
  | nil=>simp only [List.length_nil] at hi;omega
  | @cons cs room codes y ψ next tail hm a code r ih=>
    have HT :r.tuple∘oldColumn r.command=y:=funext r.old_raw
    cases i with
    | zero=>
      have HB :Canonical (continueRun x cs room):=values_continue_canonical x HC cs room
      have HNEW :IntegralMixedFullBankPoint.point (step (continueRun x cs room) hm r.command) r.tuple 0=a:=
        (IntegralMixedCanonicalBankPoint.quotient_eq (step (continueRun x cs room) hm r.command)
          (step_canonical _ HB hm r.command) (r.tuple∘(step (continueRun x cs room) hm r.command).sampler.scalar)
          r.hom r.generators 0).symm.trans (r.quotients 0)
      refine ⟨HNEW,?_⟩
      intro j
      change IntegralMixedFullBankPoint.point (continueRun x cs room) (r.tuple∘oldColumn r.command) j=
        (Fin.cons a next :Fin (m+cs.length+1)→ℝ) (cutAtBeforeIndex m (r.command::cs) 0 hi j)
      rw [HT]
      have HE :cutAtBeforeIndex m (r.command::cs) 0 hi j=j.succ:=by
        apply Fin.ext
        dsimp only [cutAtBeforeIndex,Fin.val_succ]
        omega
      rw [HE,Fin.cons_succ]
      exact (IntegralMixedCanonicalBankPoint.quotient_eq (continueRun x cs room) HB
        (y∘(continueRun x cs room).sampler.scalar) ψ (tail.generators hφ) j).symm.trans
          (tail.quotients hv j)
    | succ i=>
      have hi' :i<cs.length:=by simpa using hi
      have HU :cutAtTuple (r.command::cs) (i+1) hi r.tuple=cutAtTuple cs i hi' y:=by
        change (r.tuple∘oldColumn r.command)∘cutAtColumn cs i hi'=y∘cutAtColumn cs i hi'
        rw [HT]
      obtain ⟨HH,HV⟩:=ih i hi'
      constructor
      · rw [HU]
        have HE :cutAtHeadIndex m (r.command::cs) (i+1) hi=(cutAtHeadIndex m cs i hi').succ:=by
          apply Fin.ext
          rfl
        rw [HE,Fin.cons_succ]
        exact HH
      · intro j
        rw [HU]
        have HE :cutAtBeforeIndex m (r.command::cs) (i+1) hi j=(cutAtBeforeIndex m cs i hi' j).succ:=by
          apply Fin.ext
          dsimp only [cutAtBeforeIndex,Fin.val_succ]
          omega
        rw [HE,Fin.cons_succ]
        exact HV j

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
