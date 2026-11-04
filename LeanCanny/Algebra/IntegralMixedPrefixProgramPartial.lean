/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPrefixProgramTransport
/-! # Literal creating prefixes inside a fixed-source local program -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPrefixSnapshot
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedFixedContinuation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem ofCommands_heq {n k S T B C :ℕ} {Q :SpatialSource n} {V :SpatialSource k}
    (x :State Q S B 0 (Fin 0)) (y :State V T C 0 (Fin 0))
    (cs :List (Instruction n B)) (ds :List (Instruction k C))
    (hc :cs.length≤S+1) (hd :ds.length≤T+1)
    (hn :n=k) (hS :S=T) (hB :B=C) (hQ :HEq Q V) (hx :HEq x y) (hs :HEq cs ds) :
    ofCommands x cs hc=ofCommands y ds hd:=by
  subst k
  subst T
  subst C
  cases eq_of_heq hQ
  cases eq_of_heq hx
  cases eq_of_heq hs
  rfl

private theorem ofState_heq {n S B m l :ℕ} {Q :SpatialSource n} {ι κ :Type}
    (x :State Q S B m ι) (y :State Q S B l κ) (hm :m=l) (hi :ι=κ) (h :HEq x y) :
    ofState x=ofState y:=by
  subst l
  subst κ
  cases eq_of_heq h
  rfl

theorem wrapped_append (n S B :ℕ) (Q :SpatialSource n) (x :State Q S B 0 (Fin 0))
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (older :List (Instruction n B)) (ho :older.length≤S+1)
    (cs :List (IntegralMixedFullHistoryScript.Command Q B)) (hc :older.length+cs.length≤S+1) :
    ofCommands x (cs.map (wrap Q hQ)++older)
      (by simp only [List.length_append,List.length_map];omega)=
    ofState (IntegralMixedFullHistoryScript.continueRun
      (reframe (run x older ho) Q hQ) cs hc):=by
  exact ofState_heq _ _ (by simp only [List.length_append,List.length_map];omega)
    (index_append Q hQ cs older) (run_append x Q hQ older ho cs hc)

theorem partial_drop {α :Type} (newer cs older :List α) (i :ℕ) (hi :i<cs.length) :
    (newer++cs++older).drop (newer.length+(i+1))=cs.drop (i+1)++older:=by
  rw [List.append_assoc,List.drop_append]
  rw [List.drop_eq_nil_of_le (by omega),List.nil_append,Nat.add_sub_cancel_left,List.drop_append]
  rw [Nat.sub_eq_zero_of_le (by omega),List.drop_zero]

theorem partial_paddedPast {n B :ℕ} (fallback :Instruction n B)
    (newer cs older :List (Instruction n B)) (i :ℕ) (hi :i<cs.length) :
    paddedPast fallback (newer++cs++older) (older.length+cs.length-1-i)=
      cs.drop (i+1)++older:=by
  have HB :older.length+cs.length-1-i≤(newer++cs++older).length:=by
    simp only [List.length_append];omega
  rw [paddedPast_valid _ _ _ HB]
  simp only [past,List.reverse_take,List.length_reverse,List.reverse_reverse]
  have H : (newer++cs++older).length-(older.length+cs.length-1-i)=newer.length+(i+1):=by
    simp only [List.length_append];omega
  rw [H]
  exact partial_drop newer cs older i hi

theorem partial_chronological {n B :ℕ} (newer cs older :List (Instruction n B))
    (i :ℕ) (hi :i<cs.length) :
    chronological (newer++cs++older) (older.length+cs.length-1-i)=some cs[i]:=by
  rw [List.append_assoc]
  unfold chronological
  rw [List.getElem?_reverse' (l:=newer++(cs++older)) (j:=newer.length+i)
    (by simp only [List.length_append];omega)]
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,
    List.getElem?_append_left hi,List.getElem?_eq_getElem hi]

theorem list_drop_heq {n k B C :ℕ} (cs :List (Instruction n B)) (ds :List (Instruction k C))
    (hn :n=k) (hB :B=C) (he :HEq cs ds) (j :ℕ) :HEq (cs.drop j) (ds.drop j):=by
  subst k
  subst C
  cases eq_of_heq he
  rfl

theorem chronological_get_heq {n k B C :ℕ} (cs :List (Instruction n B)) (ds :List (Instruction k C))
    (hn :n=k) (hB :B=C) (he :HEq cs ds) (j :ℕ) (fallback :Instruction n B)
    (chosen :Instruction k C) (hc :chronological ds j=some chosen) :
    HEq ((chronological cs j).getD fallback) chosen:=by
  subst k
  subst C
  cases eq_of_heq he
  rw [hc]
  rfl

theorem instruction_command_heq {n k B C :ℕ} (a :Instruction n B) (b :Instruction k C)
    (hn :n=k) (hB :B=C) (he :HEq a b) :HEq a.command b.command:=by
  subst k
  subst C
  cases eq_of_heq he
  rfl

end LeanCanny.Algebra.IntegralMixedPrefixSnapshot
