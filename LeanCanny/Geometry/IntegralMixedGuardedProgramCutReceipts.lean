/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedGuardedProgramBirths
public import LeanCanny.Algebra.IntegralMixedPrefixCutReceipt
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # Exact creating-prefix cut receipts for constructed local traces

Each cut uses its actual preceding bank point on the restriction of the same
final tuple. The untruncated root comes from the constructed step's guard;
it is not inferred from a padded row root.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedChosenLocalRealization IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]

noncomputable def CutReceipts (x :State P S B m ι) :
    (cs :List (Command P B))→(room :m+cs.length≤S+1)→(Index ι cs→ℝ)→Prop
  | [],_,_=>True
  | c::cs,room,y=>
    let hc :m+cs.length≤S+1:=by simp only [List.length_cons] at room;omega
    let hm :m+cs.length≤S:=by simp only [List.length_cons] at room;omega
    let before:=continueRun x cs hc
    CutReceipts x cs hc (y∘oldColumn c) ∧
      (IntegralMixedPrefixSnapshot.ofState before).CutReceipt hm c
        (IntegralMixedFramedBankObservation.extend
          (IntegralMixedFullBankPoint.point before (y∘oldColumn c)))
        (IntegralMixedFullBankPoint.point (step before hm c) y 0)

private theorem receipts_continue_canonical (x :State P S B m ι) (H :Canonical x)
    (cs :List (Command P B)) (room :m+cs.length≤S+1) :Canonical (continueRun x cs room):=by
  induction cs with
  | nil=>exact H
  | cons c cs ih=>exact step_canonical _ (ih (by simp only [List.length_cons] at room;omega)) _ c

theorem GuardedProgram.cut_receipts
    {x :State P S B m ι} {hn :0<n}
    {hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
    {z :ι→ℝ} {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values :Fin m→ℝ}
    {cs :List (Command P B)} {room :m+cs.length≤S+1} {codes :List (List Bool)}
    {y :Index ι cs→ℝ} {ψ :(continueRun x cs room).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ}
    {next :Fin (m+cs.length)→ℝ}
    (H :GuardedProgram x hn hcap z φ values cs room codes y ψ next)
    (HC :Canonical x)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i) :
    CutReceipts x cs room y:=by
  induction H with
  | nil=>exact True.intro
  | @cons cs room codes y ψ next tail hm a code r ih=>
    have HT :r.tuple∘oldColumn r.command=y:=funext r.old_raw
    have HB :Canonical (continueRun x cs room):=receipts_continue_canonical x HC cs room
    have HNEW :IntegralMixedFullBankPoint.point (step (continueRun x cs room) hm r.command) r.tuple 0=a:=
      (IntegralMixedCanonicalBankPoint.quotient_eq (step (continueRun x cs room) hm r.command)
        (step_canonical _ HB hm r.command) (r.tuple∘(step (continueRun x cs room) hm r.command).sampler.scalar)
        r.hom r.generators 0).symm.trans (r.quotients 0)
    have HOLD :∀i,ψ ((continueRun x cs room).bank.numerator i)/
        ((continueRun x cs room).bank.denominator i:ℝ)=
        IntegralMixedFullBankPoint.point (continueRun x cs room) y i:=
      IntegralMixedCanonicalBankPoint.quotient_eq (continueRun x cs room) HB
        (y∘(continueRun x cs room).sampler.scalar) ψ (tail.generators hφ)
    refine ⟨?_,?_⟩
    · change CutReceipts x cs room (r.tuple∘oldColumn r.command)
      rw [HT]
      exact ih
    · obtain ⟨c,hdec,u,χ,hu,hold,hrestrict,hgen,hvals,hguard⟩:=r
      dsimp only at HNEW HT ⊢
      cases c with
      | integer _ _ _=>exact True.intro
      | critical _=>exact True.intro
      | cut r k d ha hd=>
        refine ⟨ψ,?_,?_,?_⟩
        · intro i
          change Fin (m+cs.length) at i
          rw [HT]
          change ψ ((continueRun x cs room).bank.numerator i)/
            ((continueRun x cs room).bank.denominator i:ℝ)=
            if hi :i.val<m+cs.length then
              IntegralMixedFullBankPoint.point (continueRun x cs room) y ⟨i.val,hi⟩ else 0
          rw [dite_eq_left i.isLt]
          exact HOLD i
        · exact (IntegralMixedRelativeCuts.coefficientGuards_iff_valid_degree
            (continueRun x cs room) hm r ψ k d).mpr ⟨hguard.1,hguard.2.1.symm⟩
        · rw [HNEW]
          exact hguard.2.2

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
