/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalPrefixCongruence
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowTransport
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # Natural full-row and bank readbacks of an actual causal prefix

One natural raw tuple is used throughout. Complete sample labels are absent.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRunObservation
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex (arity enumerate slotNumber)
open IntegralMixedFramedPhysicalRowTransport (natRows)
open scoped Classical

structure Data where
  bank : IntegralMixedFramedBankObservation.Data
  arity : ℕ
  rows : ℕ→MvPolynomial ℕ ℤ
  scalar : ℕ→ℕ

noncomputable def ofCommands {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs : List (Instruction n B)) (hc : cs.length≤S+1) : Data :=
  ⟨IntegralMixedFramedBankObservation.ofState (run x cs hc),arity cs,natRows x cs hc,slotNumber cs⟩
noncomputable def Data.point (d : Data) (z : ℕ→ℝ) (i : ℕ) :=d.bank.point (fun k=>z (d.scalar k)) i
def Data.Roots (d : Data) (z : ℕ→ℝ) :=∀i,(d.rows i).eval₂ (Int.castRingHom ℝ) z=0

theorem point_actual {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs : List (Instruction n B)) (hc : cs.length≤S+1)
    (z : ℕ→ℝ) (i : Fin cs.length) :
    (ofCommands x cs hc).point z i.val=
      LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point (run x cs hc)
        (fun j=>z (enumerate cs ((run x cs hc).sampler.scalar j)).val) i :=by
  dsimp only [Data.point,ofCommands,IntegralMixedFramedBankObservation.Data.point,
    IntegralMixedFramedBankObservation.ofState,
    LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point]
  rw [dite_eq_left i.isLt,IntegralMixedFramedPhysicalIndex.run_scalar_number]

theorem roots_actual {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs : List (Instruction n B)) (hc : cs.length≤S+1) (z : ℕ→ℝ) :
    (ofCommands x cs hc).Roots z↔∀i,((run x cs hc).sampler.rows i).eval₂ (Int.castRingHom ℝ)
      (fun j=>z (enumerate cs j).val)=0 :=by
  constructor
  · intro hz i
    have H:=hz (enumerate cs i).val
    change (natRows x cs hc (enumerate cs i).val).eval₂ (Int.castRingHom ℝ) z=0 at H
    rw [natRows,dite_eq_left (enumerate cs i).isLt] at H
    change (MvPolynomial.rename Fin.val (PolynomialSystemReindex.system (enumerate cs)
      (run x cs hc).sampler.rows (enumerate cs i))).eval₂ (Int.castRingHom ℝ) z=0 at H
    simpa only [PolynomialSystemReindex.system,MvPolynomial.eval₂_rename,Function.comp_def,
      Equiv.symm_apply_apply] using H
  · intro hz i
    change (natRows x cs hc i).eval₂ (Int.castRingHom ℝ) z=0
    by_cases hi :i<arity cs
    · rw [natRows,dite_eq_left hi]
      simpa only [PolynomialSystemReindex.system,MvPolynomial.eval₂_rename,Function.comp_def] using
        hz ((enumerate cs).symm ⟨i,hi⟩)
    · rw [natRows,dite_eq_right hi,MvPolynomial.eval₂_zero]

private theorem commands_congr {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :ofCommands x cs hc=ofCommands x ds hd :=by
  cases he
  rfl

theorem prefix_congr {n m S T B C : ℕ} {Q : SpatialSource n} {Q' : SpatialSource m}
    (x : State Q S B 0 (Fin 0)) (y : State Q' T C 0 (Fin 0))
    (rs : List (IntegralMixedCausalRecordBits.Record n B)) (ds : List (IntegralMixedCausalRecordBits.Record m C))
    (hr : rs.length≤S+1) (hd : ds.length≤T+1) (fr : Instruction n B) (fd : Instruction m C)
    (a b : ℕ) (ha : a≤rs.length) (hb : b≤ds.length)
    (en : n=m) (eS : S=T) (eB : B=C) (ea : a=b) (eQ : HEq Q Q') (ex : HEq x y)
    (ep : HEq (rs.reverse.take a) (ds.reverse.take b)) :
    ofCommands x (paddedPast fr (IntegralMixedCausalPlanBits.commands x rs hr) a)
      (by rw [paddedPast_length];exact ha.trans hr)=
    ofCommands y (paddedPast fd (IntegralMixedCausalPlanBits.commands y ds hd) b)
      (by rw [paddedPast_length];exact hb.trans hd) :=by
  subst m
  subst T
  subst C
  subst b
  cases eq_of_heq eQ
  cases eq_of_heq ex
  exact commands_congr x _ _ _ _
    (IntegralMixedCausalPrefixCongruence.prefix_eq x rs ds hr hd fr fd a ha hb (eq_of_heq ep))
end LeanCanny.Algebra.IntegralMixedFramedRunObservation
