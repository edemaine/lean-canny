/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
public import LeanCanny.Algebra.IntegralMixedFramedFixedTupleObservation
public import LeanCanny.Geometry.IntegralMixedPointCompanionColumns
public import LeanCanny.Geometry.IntegralMixedFullBankPoint
/-! # Literal oldest-first columns of a wrapped fixed-point companion program -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
open LeanCanny.Geometry LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex IntegralMixedPointCompanion IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem cast_target {ι :Type} {a b :ℕ} (e :ι≃Fin a) (h :a=b) :
    HEq (e.trans (finCongr h)) e:=by subst b;rfl

private theorem step_equiv_heq {n B :ℕ} {P :SpatialSource n} {ι κ :Type} {a b :ℕ}
    (r :CriticalRule n) (e :ι≃Fin a) (f :κ≃Fin b)
    (hi :ι=κ) (hab :a=b) (he :HEq e f) :
    HEq (stepEquiv (.critical r :IntegralMixedFullHistoryScript.Command P B) e)
      (stepEquiv (.critical r :IntegralMixedFullHistoryScript.Command P B) f):=by
  subst κ
  subst b
  cases eq_of_heq he
  rfl

private theorem column_readback {α β :Type} {a b :ℕ} (e :α≃Fin a) (f :β≃Fin b)
    (hi :α=β) (hab :a=b) (he :HEq e f) (u :ℕ→ℝ) (y :α→ℝ) (z :β→ℝ)
    (hy :HEq y z) (hu :∀i,u (e i).val=y i) :∀i,u (f i).val=z i:=by
  subst β
  subst b
  cases eq_of_heq he
  cases eq_of_heq hy
  exact hu

private theorem roots_same_index {n S B a b :ℕ} {Q :SpatialSource n} {ι :Type}
    (x :State Q S B a ι) (y :State Q S B b ι) (hab :a=b) (hx :HEq x y)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∀i,(y.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0:=by
  subst b
  cases eq_of_heq hx
  exact hz

private theorem point_heq {n S B a b :ℕ} {Q :SpatialSource n} {ι κ :Type} [Fintype ι] [Fintype κ]
    (x :State Q S B a ι) (y :State Q S B b κ) (hab :a=b) (hi :ι=κ) (hx :HEq x y)
    (z :ι→ℝ) (w :κ→ℝ) (hz :HEq z w) (i :Fin a) (j :Fin b) (hij :i.val=j.val) :
    IntegralMixedFullBankPoint.point x z i=IntegralMixedFullBankPoint.point y w j:=by
  subst b
  subst κ
  cases eq_of_heq hx
  cases eq_of_heq hz
  exact congrArg (IntegralMixedFullBankPoint.point x z) (Fin.ext hij)

private theorem run_canonical {n S B m :ℕ} {Q :SpatialSource n} {ι :Type} [Fintype ι]
    (x :State Q S B m ι) (HC :Canonical x)
    (frozen :Finset (Fin (n+1))) (double :Fin (n+1)→Bool) (rows :Fin (n+1)→Row m) (g :Free frozen)
    (js :List (Free frozen)) (room :m+js.length≤S+1) :
    Canonical (IntegralMixedPointCompanion.run x frozen double rows g js room):=by
  induction js with
  | nil=>exact HC
  | cons j js ih=>
    exact IntegralMixedFullHistoryScript.step_canonical _
      (ih (by simp only [List.length_cons] at room;omega)) _ _

theorem before_interprets {n S B :ℕ} {P :SpatialSource n}
    (initial :State P S B 0 (Fin 0)) (Q :SpatialSource n)
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (older :List (Instruction n B)) (ho :older.length≤S+1)
    (z :Index (Fin 0) older→ℝ)
    (hz :∀i,((run initial older ho).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∃φ :(reframe (run initial older ho) Q hQ).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((reframe (run initial older ho) Q hQ).sampler.scalarPrefix.basis.generator i)=
        z ((reframe (run initial older ho) Q hQ).sampler.scalar i)^
          UniformIntegralPowerSchedule.weights S (2^B) older.length i) ∧
      ∀i,φ ((reframe (run initial older ho) Q hQ).bank.numerator i)/
        ((reframe (run initial older ho) Q hQ).bank.denominator i:ℝ)=
          IntegralMixedFullBankPoint.point (reframe (run initial older ho) Q hQ) z i:=
  IntegralMixedFullBankPoint.interprets _
    (IntegralMixedFramedHistoryScript.reframe_canonical _
      (IntegralMixedFramedHistoryScript.run_canonical initial (fun i=>Fin.elim0 i) older ho) Q hQ) z hz

variable {n B m :ℕ} {Q :SpatialSource n}
  (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
  (older :List (Instruction n B)) (frozen :Finset (Fin (n+1))) (double :Fin (n+1)→Bool)
  (rows :Fin (n+1)→Row m) (g :Free frozen)

theorem companion_arity (js :List (Free frozen)) :
    arity ((commands (P:=Q) (B:=B) frozen double rows g js).map (wrap Q hQ)++older)=
      arity older+(2*n+4)*js.length:=by
  induction js with
  | nil=>simp only [commands,List.map_nil,List.nil_append,List.length_nil,Nat.mul_zero,Nat.add_zero]
  | cons j js ih=>
    simp only [commands,List.map_cons,List.cons_append,arity,wrap,command,added,
      IntegralMixedFullHistoryScript.Command.isCritical,ite_true,block,List.length_cons,ih]
    ring

theorem companion_columns (js :List (Free frozen)) :
    HEq (enumerate ((commands (P:=Q) (B:=B) frozen double rows g js).map (wrap Q hQ)++older))
      (columns (P:=Q) (B:=B) frozen double rows g (enumerate older) js):=by
  induction js with
  | nil=>rfl
  | cons j js ih=>
    have HS:=step_equiv_heq (P:=Q) (B:=B) (pointData frozen double rows g js.length j).rule
      (enumerate ((commands (P:=Q) (B:=B) frozen double rows g js).map (wrap Q hQ)++older))
      (columns (P:=Q) (B:=B) frozen double rows g (enumerate older) js)
      (index_append Q hQ (commands (P:=Q) (B:=B) frozen double rows g js) older)
      (companion_arity hQ older frozen double rows g js) ih
    exact HS.trans (cast_target _ _).symm

theorem companion_observation {n S B :ℕ} {P :SpatialSource n}
    (initial :State P S B 0 (Fin 0)) (Q :SpatialSource n)
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (older :List (Instruction n B)) (ho :older.length≤S+1)
    (frozen :Finset (Fin (n+1))) (double :Fin (n+1)→Bool)
    (rows :Fin (n+1)→Row older.length) (g :Free frozen)
    (z :Index (Fin 0) older→ℝ)
    (φ :(reframe (run initial older ho) Q hQ).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old :Fin older.length→ℝ) (p :Fin (n+1)→ℝ) (js :List (Free frozen))
    (room :older.length+js.length≤S+1)
    (R :Realized (reframe (run initial older ho) Q hQ) frozen double rows g z φ old p js room) :
    ∃u :ℕ→ℝ,
      (IntegralMixedFramedRunObservation.ofCommands initial
        ((commands (P:=Q) (B:=B) frozen double rows g js).map (wrap Q hQ)++older)
        (by simp only [List.length_append,List.length_map,commands_length];omega)).Roots u ∧
      (∀i,u (enumerate older i).val=z i) ∧
      (∀k :Fin js.length,∀i,
        u (arity older+(2*n+4)*(js.length-1-k.val)+i.val)^
          UniformIntegralPowerSchedule.physical S (2^B) (older.length+(js.length-1-k.val))=p i) ∧
      ∀i :Fin (older.length+js.length),
        (IntegralMixedFramedRunObservation.ofCommands initial
          ((commands (P:=Q) (B:=B) frozen double rows g js).map (wrap Q hQ)++older)
          (by simp only [List.length_append,List.length_map,commands_length];omega)).point u i.val=
            values p old js i:=by
  have HR:=run_continue (reframe (run initial older ho) Q hQ) frozen double rows g js room
  have HZ:=roots_same_index _ _ (congrArg (older.length+·)
    (commands_length (P:=Q) (B:=B) frozen double rows g js).symm) HR R.tuple R.roots
  obtain ⟨u,y,hy,hu,hcol⟩:=tuple_append_observation initial Q hQ older ho
    (commands (P:=Q) (B:=B) frozen double rows g js)
    (by simpa only [commands_length] using room) R.tuple HZ
  have HE:=column_readback _ _
    (index_append Q hQ (commands (P:=Q) (B:=B) frozen double rows g js) older)
    (companion_arity hQ older frozen double rows g js)
    (companion_columns hQ older frozen double rows g js) u y R.tuple hy hcol
  refine ⟨u,hu,?_,?_,?_⟩
  · intro i
    have HC:=HE (IntegralMixedOptionalEndpoints.oldColumns (commands frozen double rows g js) i)
    rw [columns_old] at HC
    exact HC.trans (R.old_raw i)
  · intro k i
    have HC:=HE (blockColumn frozen double rows g js k i)
    rw [columns_block] at HC
    rw [HC]
    exact R.blocks k i
  · intro i
    have HM :((commands (P:=Q) (B:=B) frozen double rows g js).map (wrap Q hQ)++older).length=
        older.length+js.length:=by simp only [List.length_append,List.length_map,commands_length];omega
    let j :Fin ((commands (P:=Q) (B:=B) frozen double rows g js).map (wrap Q hQ)++older).length:=
      ⟨i.val,by rw [HM];exact i.isLt⟩
    have HP:=IntegralMixedFramedRunObservation.point_actual initial
      ((commands (P:=Q) (B:=B) frozen double rows g js).map (wrap Q hQ)++older)
      (by simp only [List.length_append,List.length_map,commands_length];omega) u j
    have HT : (fun k=>u (enumerate ((commands (P:=Q) (B:=B) frozen double rows g js).map (wrap Q hQ)++older) k).val)=y:=
      funext hcol
    change _=IntegralMixedFullBankPoint.point _
      (fun k=>u (enumerate ((commands (P:=Q) (B:=B) frozen double rows g js).map (wrap Q hQ)++older) k).val) j at HP
    rw [HT] at HP
    have HS:=(run_append initial Q hQ older ho (commands (P:=Q) (B:=B) frozen double rows g js)
      (by simpa only [commands_length] using room)).trans HR.symm
    have HQ:=point_heq _ _ HM
      (index_append Q hQ (commands (P:=Q) (B:=B) frozen double rows g js) older) HS y R.tuple hy j i rfl
    have HC:=run_canonical (reframe (run initial older ho) Q hQ)
      (IntegralMixedFramedHistoryScript.reframe_canonical _
        (IntegralMixedFramedHistoryScript.run_canonical initial (fun k=>Fin.elim0 k) older ho) Q hQ)
      frozen double rows g js room
    have HV:=IntegralMixedCanonicalBankPoint.quotient_eq
      (IntegralMixedPointCompanion.run (reframe (run initial older ho) Q hQ) frozen double rows g js room)
      HC _ R.hom R.generators i
    exact HP.trans (HQ.trans (HV.symm.trans (R.quotients i)))

end LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
