/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedStaticRecordLookup
public import LeanCanny.Algebra.IntegralMixedCausalPlanHeaders
/-! # Literal causal header lookup, including the integer prelude -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedStaticRecordHeaderReceipt
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem getD_header {n B : ℕ} (cs : List (Instruction n B)) (fallback : Instruction n B)
    (b : ℕ) : IntegralMixedCommandHeaderBits.command ((cs.reverse[b]?).getD fallback).command=
      ((cs.reverse[b]?).map (fun c=>IntegralMixedCommandHeaderBits.command c.command)).getD
        (IntegralMixedCommandHeaderBits.command fallback.command) :=by
  cases cs.reverse[b]? <;> rfl

theorem commands_header {n S B : ℕ} {P : SpatialSource n}
    (x : State P S B 0 (Fin 0)) (rs : List (Record n B)) (hr : rs.length≤S+1)
    (fallback : Instruction n B) (b : ℕ) :
    IntegralMixedCommandHeaderBits.command
      ((chronological (IntegralMixedCausalPlanBits.commands x rs hr) b).getD fallback).command=
      ((rs.reverse[b]?).map (fun r=>r.template.header)).getD
        (IntegralMixedCommandHeaderBits.command fallback.command) :=by
  have HM:=IntegralMixedCausalPlanBits.commands_headers x rs hr
  have HE:=congrArg (fun l=>l.reverse[b]?) HM
  rw [←List.map_reverse,←List.map_reverse,List.getElem?_map,List.getElem?_map] at HE
  rw [chronological,getD_header,HE]

variable {n B : ℕ} (Q : SpatialSource n) (hn : 0<n)
  (hQ : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
  (N C : ℕ) (p : ℕ→Polynomial ℤ) (hp : ∀i,p i≠0) (hd : ∀i,(p i).natDegree≤2^B)
  (w : ℕ→List Bool)
open IntegralMixedStaticRecordPrefix

theorem chronological_headers :
    (records Q hn hQ N C p hp hd w).reverse.map (fun r=>r.template.header)=
      List.replicate N IntegralMixedCommandHeaderBits.zero++
        (List.range C).map (fun i=>(IntegralMixedCausalUnitRecordBits.record Q hn (N+i) (w i) hQ).template.header) :=by
  rw [records,List.reverse_append,List.map_append,later,List.reverse_reverse,List.map_map]
  apply congrArg (fun l=>l++_)
  rw [List.map_reverse]
  have HE : (originals Q hQ N p hp hd).map (fun r=>r.template.header)=
      List.replicate N IntegralMixedCommandHeaderBits.zero:=by
    simp only [originals,List.map_ofFn,Template.header,Template.command,IntegralMixedCommandHeaderBits.command]
    change List.ofFn (fun _ : Fin N=>IntegralMixedCommandHeaderBits.zero)=_
    exact List.ofFn_const N _
  rw [HE,List.reverse_replicate]

theorem integer_header (b : ℕ) (hb : b<N) :
    (((records Q hn hQ N C p hp hd w).reverse[b]?).map (fun r=>r.template.header)).getD
      IntegralMixedCommandHeaderBits.zero=IntegralMixedCommandHeaderBits.zero :=by
  rw [←List.getElem?_map,chronological_headers,List.getElem?_append_left (by simp only [List.length_replicate];exact hb),
    List.getElem?_replicate,ite_eq_left hb,Option.getD_some]

theorem later_header (a : ℕ) (ha : a<C) :
    (((records Q hn hQ N C p hp hd w).reverse[N+a]?).map (fun r=>r.template.header)).getD
      IntegralMixedCommandHeaderBits.zero=
        (IntegralMixedCausalUnitRecordBits.record Q hn (N+a) (w a) hQ).template.header :=by
  rw [←List.getElem?_map,chronological_headers,List.getElem?_append_right (by simp only [List.length_replicate];omega)]
  simp only [List.length_replicate,Nat.add_sub_cancel_left,List.getElem?_map,List.getElem?_range ha,
    Option.map_some,Option.getD_some]

end LeanCanny.Algebra.IntegralMixedStaticRecordHeaderReceipt
