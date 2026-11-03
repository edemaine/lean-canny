/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapEndpointSyntax
/-! # Canonical endpoint metadata has bounded length even for retained producers -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapEndpointSyntax
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical

def specBudget (n limit B : ℕ):=(2*(n+limit+B+5)+2)*6

theorem specBudget_unary {n limit B : List Bool→ℕ} (hn : UnaryFn n) (hl : UnaryFn limit) (hB : UnaryFn B) :
    UnaryFn (fun q=>specBudget (n q) (limit q) (B q)) :=
  (((UnaryFn.const 2).mul (((hn.add hl).add hB).add (UnaryFn.const 5))).add (UnaryFn.const 2)).mul (UnaryFn.const 6)

theorem good_length {n B sourceCap oldBirth current limit : ℕ} {labels s : List Bool}
    (h : Good n B sourceCap oldBirth current labels s) (ho : oldBirth≤limit) (hc : current≤limit)
    (hcap : sourceCap≤2^B) (hk : WordListRecords.count labels≤n+1) : s.length≤specBudget n limit B :=by
  have HN : field s 0≤2 ∧ field s 1≤limit ∧ field s 2≤n+1 ∧
      field s 3≤2 ∧ field s 4≤2^B ∧ field s 5≤2^B :=by
    rcases h.2 with H|H|H
    · obtain ⟨H0,H1,H2,H3,H4,H5⟩:=H
      exact ⟨H0.le.trans (by decide),H1.le.trans ho,by omega,by omega,by omega,by omega⟩
    · obtain ⟨H0,H1,H2,H3,H4,H5⟩:=H
      exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
    · obtain ⟨H0,H1,HG,HT,Hchoice,HD⟩:=H
      have Hcoord:=HG.2.2.2.2
      exact ⟨by omega,by omega,Hcoord.le,HT,Hchoice,HD.trans hcap⟩
  have size_bound (a b : ℕ) (ha : a≤b) : a.size≤b:=
    Nat.size_le.mpr (ha.trans_lt (show b<2^b from Nat.lt_two_pow_self))
  have H0:=size_bound _ _ HN.1
  have H1:=size_bound _ _ HN.2.1
  have H2:=size_bound _ _ HN.2.2.1
  have H3:=size_bound _ _ HN.2.2.2.1
  have H4 : (field s 4).size≤B+1:=by simpa only [Nat.size_pow] using Nat.size_le_size HN.2.2.2.2.1
  have H5 : (field s 5).size≤B+1:=by simpa only [Nat.size_pow] using Nat.size_le_size HN.2.2.2.2.2
  have HF : ∀w∈[BinaryNatCode.encode (field s 0),BinaryNatCode.encode (field s 1),
      BinaryNatCode.encode (field s 2),BinaryNatCode.encode (field s 3),
      BinaryNatCode.encode (field s 4),BinaryNatCode.encode (field s 5)],w.length≤n+limit+B+5:=by
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      simp only [BinaryNatCode.encode,Nat.size_eq_bits_len]
      omega
  have HL:=WordList.length_le _ (n+limit+B+5) HF
  rw [h.1]
  simpa only [canonical,spec,List.map_cons,List.map_nil,List.length_cons,List.length_nil,specBudget] using HL

end LeanCanny.Encoding.IntegralMixedRoadmapEndpointSyntax
