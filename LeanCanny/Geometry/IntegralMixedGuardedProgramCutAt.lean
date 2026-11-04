/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedGuardedProgramCutReceipts
/-! # Indexed creating-prefix receipts from one guarded final tuple

Indices of commands are newest first. Deleting each newer command restricts
the same final tuple through its literal oldColumn map. The selected receipt
uses the actual older prefix, command, and bank values of that restriction.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedChosenLocalRealization IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type}

def cutAtColumn : (cs :List (Command P B))→(i :ℕ)→(hi :i<cs.length)→
    NextIndex (Index ι (cs.drop (i+1))) cs[i]→Index ι cs
  | [],_,hi,_=>False.elim (by simp at hi)
  | _::_,0,_,j=>j
  | c::cs,i+1,hi,j=>oldColumn c (cutAtColumn cs i (by simpa using hi) j)

def cutAtTuple (cs :List (Command P B)) (i :ℕ) (hi :i<cs.length) (y :Index ι cs→ℝ) :
    NextIndex (Index ι (cs.drop (i+1))) cs[i]→ℝ:=y∘cutAtColumn cs i hi

theorem cutAt_index_append (as bs :List (Command P B)) :
    Index ι (as++bs)=Index (Index ι bs) as:=by
  induction as with
  | nil=>rfl
  | cons c as ih=>exact congrArg (fun α :Type=>NextIndex α c) ih

theorem cutAt_decomposition (cs :List (Command P B)) (i :ℕ) (hi :i<cs.length) :
    cs.take i++cs[i]::cs.drop (i+1)=cs:=by
  rw [←List.drop_eq_getElem_cons hi,List.take_append_drop]

theorem cutAt_index_eq (cs :List (Command P B)) (i :ℕ) (hi :i<cs.length) :
    Index ι cs=Index (NextIndex (Index ι (cs.drop (i+1))) cs[i]) (cs.take i):=
  (congrArg (Index ι) (cutAt_decomposition cs i hi)).symm.trans
    (cutAt_index_append (cs.take i) (cs[i]::cs.drop (i+1)))

private theorem oldColumn_comp_heq {α β δ :Type} (c :Command P B)
    (h :α=β) (f :δ→α) (g :δ→β) (he :HEq f g) :
    HEq (oldColumn c∘f) (oldColumn c∘g):=by
  subst β
  exact heq_of_eq (congrArg (fun v :δ→α=>oldColumn c∘v) (eq_of_heq he))

/-- The recursive restriction is precisely oldColumns of the newer commands;
HEq records only the reassociation of the dependent physical index type. -/
theorem cutAtColumn_oldColumns (cs :List (Command P B)) (i :ℕ) (hi :i<cs.length) :
    HEq (cutAtColumn (ι:=ι) cs i hi)
      (oldColumns (ι:=NextIndex (Index ι (cs.drop (i+1))) cs[i]) (cs.take i)):=by
  induction cs generalizing i with
  | nil=>simp only [List.length_nil] at hi;omega
  | cons c cs ih=>
    cases i with
    | zero=>exact HEq.rfl
    | succ i=>
      have hi' :i<cs.length:=by simpa using hi
      change HEq (oldColumn c∘cutAtColumn cs i hi')
        (oldColumn c∘oldColumns (ι:=NextIndex (Index ι (cs.drop (i+1))) cs[i]) (cs.take i))
      exact oldColumn_comp_heq c (cutAt_index_eq cs i hi') _ _ (ih i hi')

private theorem eq_comp_cast {α β δ :Type} (h :α=β) (f :δ→α) (g :δ→β)
    (he :HEq f g) :f=(cast h.symm)∘g:=by
  subst β
  exact eq_of_heq he

theorem cutAtTuple_oldColumns (cs :List (Command P B)) (i :ℕ) (hi :i<cs.length)
    (y :Index ι cs→ℝ) :
    cutAtTuple cs i hi y=
      y∘cast (cutAt_index_eq cs i hi).symm∘
        oldColumns (ι:=NextIndex (Index ι (cs.drop (i+1))) cs[i]) (cs.take i):=
  congrArg (fun f=>y∘f)
    (eq_comp_cast (cutAt_index_eq cs i hi) _ _ (cutAtColumn_oldColumns cs i hi))

theorem cutAt_room (cs :List (Command P B)) (room :m+cs.length≤S+1) (i :ℕ) :
    m+(cs.drop (i+1)).length≤S+1:=by
  rw [List.length_drop]
  omega

theorem cutAt_fit (cs :List (Command P B)) (room :m+cs.length≤S+1)
    (i :ℕ) (hi :i<cs.length) :m+(cs.drop (i+1)).length≤S:=by
  rw [List.length_drop]
  omega

theorem cutAt_birth (cs :List (Command P B)) (i :ℕ) (hi :i<cs.length) :
    m+(cs.drop (i+1)).length=m+cs.length-1-i:=by
  rw [List.length_drop]
  omega

variable [Fintype ι]

noncomputable def CutReceiptAt (x :State P S B m ι) (cs :List (Command P B))
    (room :m+cs.length≤S+1) (y :Index ι cs→ℝ) (i :ℕ) (hi :i<cs.length) :Prop:=
  let before:=continueRun x (cs.drop (i+1)) (cutAt_room cs room i)
  let hm:=cutAt_fit cs room i hi
  let current:=cs[i]
  let u:=cutAtTuple cs i hi y
  (IntegralMixedPrefixSnapshot.ofState before).CutReceipt hm current
    (IntegralMixedFramedBankObservation.extend
      (IntegralMixedFullBankPoint.point before (u∘oldColumn current)))
    (IntegralMixedFullBankPoint.point (step before hm current) u 0)

theorem CutReceipts.at {x :State P S B m ι} {cs :List (Command P B)}
    {room :m+cs.length≤S+1} {y :Index ι cs→ℝ}
    (H :CutReceipts x cs room y) (i :ℕ) (hi :i<cs.length) :
    CutReceiptAt x cs room y i hi:=by
  induction cs generalizing i with
  | nil=>simp only [List.length_nil] at hi;omega
  | cons c cs ih=>
    cases i with
    | zero=>exact H.2
    | succ i=>
      have hc :m+cs.length≤S+1:=by simp only [List.length_cons] at room;omega
      have HT :CutReceipts x cs hc (y∘oldColumn c):=H.1
      exact ih HT i (by simpa using hi)

theorem GuardedProgram.cut_receipt_at
    {x :State P S B m ι} {hn :0<n}
    {hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
    {z :ι→ℝ} {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values :Fin m→ℝ}
    {cs :List (Command P B)} {room :m+cs.length≤S+1} {codes :List (List Bool)}
    {y :Index ι cs→ℝ} {ψ :(continueRun x cs room).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ}
    {next :Fin (m+cs.length)→ℝ}
    (H :GuardedProgram x hn hcap z φ values cs room codes y ψ next)
    (HC :Canonical x)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (i :ℕ) (hi :i<cs.length) :CutReceiptAt x cs room y i hi:=
  (H.cut_receipts HC hφ).at i hi

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
