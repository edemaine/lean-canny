/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalPrefixCongruence
public import LeanCanny.Algebra.IntegralMixedSourceReframe
public import LeanCanny.Algebra.IntegralMixedIntegerRealization
/-! # A literal causal prefix snapshot retains the actual coefficient algebra

Unlike the numerical row observation, this bundle keeps the full state and
its dependent scalar algebra. Equal chronological original prefixes give
ordinary equality of snapshots, so later semantics can be transported without
inventing a cast between independently interpreted coefficient algebras.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPrefixSnapshot
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedCausalRecordBits
open scoped Classical

structure Data where
 ambient : ℕ
 horizon : ℕ
 width : ℕ
 birth : ℕ
 source : SpatialSource ambient
 index : Type
 state : State source horizon width birth index

noncomputable def ofState {n S B m : ℕ} {Q : SpatialSource n} {ι : Type}
    (x : State Q S B m ι) : Data:=⟨n,S,B,m,Q,ι,x⟩

noncomputable def ofCommands {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs : List (Instruction n B)) (hc : cs.length≤S+1) : Data:=
 ofState (reframe (run x cs hc) Q x.critical_cap)

theorem ofCommands_birth {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs : List (Instruction n B)) (hc : cs.length≤S+1) :
    (ofCommands x cs hc).birth=cs.length:=rfl

theorem ofCommands_realizes {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs : List (Instruction n B)) (hc : cs.length≤S+1) (values : ℕ→ℝ) :
    IntegralMixedIntegerRealization.Realizes (ofCommands x cs hc).state values ↔
      IntegralMixedIntegerRealization.Realizes (run x cs hc) values:=Iff.rfl

theorem ofCommands_canonical {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (hx : Canonical x) (cs : List (Instruction n B)) (hc : cs.length≤S+1) :
    Canonical (ofCommands x cs hc).state:=
 reframe_canonical _ (run_canonical x hx cs hc) Q x.critical_cap

private theorem commands_congr {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) : ofCommands x cs hc=ofCommands x ds hd:=by
 cases he
 rfl

theorem prefix_congr {n m S T B C : ℕ} {Q : SpatialSource n} {Q' : SpatialSource m}
    (x : State Q S B 0 (Fin 0)) (y : State Q' T C 0 (Fin 0))
    (rs : List (Record n B)) (ds : List (Record m C))
    (hr : rs.length≤S+1) (hd : ds.length≤T+1) (fr : Instruction n B) (fd : Instruction m C)
    (a b : ℕ) (ha : a≤rs.length) (hb : b≤ds.length)
    (en : n=m) (eS : S=T) (eB : B=C) (ea : a=b) (eQ : HEq Q Q') (ex : HEq x y)
    (ep : HEq (rs.reverse.take a) (ds.reverse.take b)) :
    ofCommands x (paddedPast fr (IntegralMixedCausalPlanBits.commands x rs hr) a)
      (by rw [paddedPast_length];exact ha.trans hr)=
    ofCommands y (paddedPast fd (IntegralMixedCausalPlanBits.commands y ds hd) b)
      (by rw [paddedPast_length];exact hb.trans hd):=by
 subst m
 subst T
 subst C
 subst b
 cases eq_of_heq eQ
 cases eq_of_heq ex
 exact commands_congr x _ _ _ _
   (IntegralMixedCausalPrefixCongruence.prefix_eq x rs ds hr hd fr fd a ha hb (eq_of_heq ep))

end LeanCanny.Algebra.IntegralMixedPrefixSnapshot
