/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapLevelChecked
public import LeanCanny.Encoding.IntegralMixedRoadmapRecordBudget
/-! # Checked level bytes inhabit the existing bounded record ledger -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapLevel
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedRoadmapRecordChain
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def budget (n B birth : ℕ) (q : List Bool) :=IntegralMixedCutRecordConstructor.codeBudget n (endBirth n birth q) B

theorem budget_unary {n B birth : List Bool→ℕ} (hn : UnaryFn n) (hB : UnaryFn B) (hb : BinaryFn birth) :
    UnaryFn (fun q=>budget (n q) (B q) (birth q) q) :=
  IntegralMixedCutRecordConstructor.codeBudget_unary hn (endBirth_binary hn hb) hB

theorem critical_budget {n B current limit : ℕ} (hc : current≤limit) :
    IntegralMixedCriticalRecordConstructor.codeBudget n current≤IntegralMixedCutRecordConstructor.codeBudget n limit B :=
  (IntegralMixedCutRecordConstructor.critical_codeBudget_le n current B).trans
    (LeanCanny.Geometry.IntegralMixedOptionalEndpoints.codeBudget_mono n B current limit hc)

theorem endpoint_size {n B cap old current limit : ℕ} {w s : List Bool}
    (h : IntegralMixedRoadmapEndpointSyntax.Good n B cap old current w s)
    (hf : IntegralMixedChronologicalFrameCode.Good n old w) (ho : old≤current)
    (hk : WordListRecords.count w<n+1) (hl : current≤limit) (hcap : cap≤2^B)
    (hnew : IntegralMixedRoadmapEndpointSyntax.field s 0≠0) :
    (IntegralMixedRoadmapEndpointSyntax.code n w s).length≤IntegralMixedCutRecordConstructor.codeBudget n limit B :=by
  rcases IntegralMixedRoadmapEndpointSyntax.checked_code h hf ho hk with h|h|h
  · exact (hnew h.1).elim
  · rw [h.2.2.2]
    have HS:=(IntegralMixedChronologicalFrameCode.rawData n current w (WordListRecords.count w)
      (WordListRecords.count w) h.2.2.1).code_length
    rw [IntegralMixedChronologicalFrameCode.rawData_code] at HS
    exact HS.trans (critical_budget hl)
  · rw [h.2.2.2]
    have HC:=h.2.2.1
    exact (IntegralMixedChronologicalCutCode.raw_code_size n current B w _ _ _ _ _ HC.1 HC.2.1 HC.2.2.1
      (HC.2.2.2.trans hcap)).trans (LeanCanny.Geometry.IntegralMixedOptionalEndpoints.codeBudget_mono n B current limit hl)

noncomputable def endpoint {n B cap old current limit : ℕ} {w s : List Bool}
    (h : IntegralMixedRoadmapEndpointSyntax.Good n B cap old current w s)
    (hf : IntegralMixedChronologicalFrameCode.Good n old w) (ho : old≤current)
    (hk : WordListRecords.count w<n+1) (hl : current+IntegralMixedRoadmapEndpointSyntax.fresh s≤limit)
    (hcap : cap≤2^B) : Endpoint (IntegralMixedCutRecordConstructor.codeBudget n limit B) limit :=
  if hi : IntegralMixedRoadmapEndpointSyntax.field s 0=0 then
    .retained ⟨IntegralMixedRoadmapEndpointSyntax.field s 1,(IntegralMixedRoadmapEndpointSyntax.producer_lt h ho).trans_le hl⟩
  else .fresh ⟨IntegralMixedRoadmapEndpointSyntax.code n w s,
    endpoint_size h hf ho hk (by omega) hcap hi⟩

theorem endpoint_codes {n B cap old current limit : ℕ} {w s : List Bool}
    (h : IntegralMixedRoadmapEndpointSyntax.Good n B cap old current w s)
    (hf : IntegralMixedChronologicalFrameCode.Good n old w) (ho : old≤current)
    (hk : WordListRecords.count w<n+1) (hl : current+IntegralMixedRoadmapEndpointSyntax.fresh s≤limit)
    (hcap : cap≤2^B) :
    ((endpoint h hf ho hk hl hcap).codes.map Subtype.val)=IntegralMixedRoadmapEndpointSyntax.codes n w s :=by
  unfold endpoint IntegralMixedRoadmapEndpointSyntax.codes
  split_ifs <;> rfl

theorem midpoint_size {n B cap birth current j : ℕ} {q : List Bool}
    (h : Checked n B cap birth q) (hm : afterEndpoints birth q≤current)
    (hl : current≤endBirth n birth q) (hj : g q≤j) (hjn : j<n+1) :
    (IntegralMixedChronologicalMidpointCode.code n (labels q) (producer false q) (producer true q) (g q) j).length≤budget n B birth q :=
  (IntegralMixedChronologicalMidpointCode.raw_code_size n current (labels q) _ _ _ _
    (midpoint_good h.1 hm hj hjn)).trans (critical_budget hl)

theorem child_size {n B cap birth current j : ℕ} {q : List Bool}
    (h : Checked n B cap birth q) (hm : childBirth n birth q≤current)
    (hl : current≤endBirth n birth q) (hj : g q≤j) (hjn : j<n+1) :
    (IntegralMixedChronologicalEndpointCode.code n (labels q) (chosen q) (g q) j).length≤budget n B birth q :=
  (IntegralMixedChronologicalEndpointCode.raw_code_size n current (labels q) _ _ _
    (child_point_good h.1 hm hj hjn)).trans (critical_budget hl)

noncomputable def ledger {n B cap birth : ℕ} {q : List Bool} (h : Checked n B cap birth q) :
    Level n (k q) (budget n B birth q) (endBirth n birth q) where
  left:=endpoint h.1.2.2.1 h.1.1 le_rfl (by have H:=h.1.2.1;unfold g k at H;omega)
    (by unfold endBirth afterEndpoints freshLeft;omega) h.1.2.2.2.2.2.1
  right:=endpoint h.1.2.2.2.1 h.1.1 (by omega) (by have H:=h.1.2.1;unfold g k at H;omega)
    (by unfold endBirth afterEndpoints freshRight;omega) h.1.2.2.2.2.2.1
  anchor:=⟨midpointAnchor n q,midpoint_size (current:=afterEndpoints birth q) h le_rfl
    (by unfold endBirth;omega) le_rfl h.1.2.1⟩
  midpoint i:=⟨IntegralMixedChronologicalMidpointCode.code n (labels q) (producer false q) (producer true q) (g q) (n-i.val),
    midpoint_size (current:=afterEndpoints birth q+1+i.val) h (by omega)
      (by have HI:=i.isLt;unfold endBirth freeCount g;omega)
      (companion_coordinate i.isLt).1 (companion_coordinate i.isLt).2⟩
  endpoint:=⟨childAnchor n q,child_size (current:=childBirth n birth q) h le_rfl
    (by unfold childBirth endBirth;omega) le_rfl h.1.2.1⟩
  companions i:=⟨IntegralMixedChronologicalEndpointCode.code n (labels q) (chosen q) (g q) (n-i.val),
    child_size (current:=childBirth n birth q+1+i.val) h (by omega)
      (by have HI:=i.isLt;unfold childBirth endBirth freeCount g;omega)
      (companion_coordinate i.isLt).1 (companion_coordinate i.isLt).2⟩

private theorem ofFn_range {α : Type} (f : ℕ→α) (n : ℕ) :List.ofFn (fun i : Fin n=>f i.val)=(List.range n).map f :=by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_map,List.length_range]
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]

theorem ledger_codes {n B cap birth : ℕ} {q : List Bool} (h : Checked n B cap birth q) :
    (ledger h).codes.map Subtype.val=codes n q :=by
  simp only [IntegralMixedRoadmapRecordChain.Level.codes,List.map_append,List.map_cons,List.map_nil,
    List.map_ofFn,ledger,endpoint_codes,Function.comp_def,codes,midpointAnchor,childAnchor,k,
    IntegralMixedChronologicalMidpointCompanionCode.codes,IntegralMixedChronologicalCompanionCode.codes,
    childLabels,IntegralMixedChronologicalEndpointCode.code,IntegralMixedChronologicalEndpointCode.append_count]
  rw [ofFn_range (fun i=>IntegralMixedChronologicalMidpointCode.code n (labels q)
    (producer false q) (producer true q) (g q) (n-i))]
  rw [ofFn_range (fun i=>IntegralMixedChronologicalFrameCode.code n
    (IntegralMixedChronologicalEndpointCode.appendLabels (labels q) (chosen q)) (g q) (n-i))]

theorem ledger_word {n B cap birth : ℕ} {q : List Bool} (h : Checked n B cap birth q) :
    WordList.encode ((ledger h).codes.map Subtype.val)=slice q :=by
  rw [ledger_codes]
  exact h.2.symm

end LeanCanny.Encoding.IntegralMixedRoadmapLevel
