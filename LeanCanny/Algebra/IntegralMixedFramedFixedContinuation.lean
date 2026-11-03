/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedDecodedAppend
public import LeanCanny.Algebra.IntegralMixedFramedHistoryScript
/-! # A fixed-source local program continues the literal source-framed history -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
open LeanCanny.Encoding IntegralMixedHistory
open IntegralMixedFramedHistoryScript (Instruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]

noncomputable def wrap (Q :SpatialSource n)
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (c :IntegralMixedFullHistoryScript.Command Q B) :Instruction n B:=⟨Q,hQ,c⟩

omit [Fintype ι] in
theorem index_append (Q :SpatialSource n)
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (cs :List (IntegralMixedFullHistoryScript.Command Q B)) (older :List (Instruction n B)) :
    IntegralMixedFramedHistoryScript.Index ι (cs.map (wrap Q hQ)++older)=
      IntegralMixedFullHistoryScript.Index (IntegralMixedFramedHistoryScript.Index ι older) cs:=by
  induction cs with
  | nil=>rfl
  | cons c cs ih=>exact congrArg (fun κ :Type=>IntegralMixedFullHistoryScript.NextIndex κ c) ih

private theorem reframe_self {m :ℕ} {Q :SpatialSource n} {κ :Type}
    (x :State Q S B m κ) (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) :reframe x Q hQ=x:=
  reframe_same x

theorem run_append (initial :State P S B 0 ι) (Q :SpatialSource n)
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (older :List (Instruction n B)) (ho :older.length≤S+1)
    (cs :List (IntegralMixedFullHistoryScript.Command Q B)) (hc :older.length+cs.length≤S+1) :
    HEq (reframe (IntegralMixedFramedHistoryScript.run initial (cs.map (wrap Q hQ)++older)
      (by simp only [List.length_append,List.length_map];omega)) Q hQ)
      (IntegralMixedFullHistoryScript.continueRun
        (reframe (IntegralMixedFramedHistoryScript.run initial older ho) Q hQ) cs hc):=by
  induction cs with
  | nil=>rfl
  | cons c cs ih=>
    have HT :older.length+cs.length≤S+1:=by simp only [List.length_cons] at hc;omega
    have HM :(cs.map (wrap Q hQ)++older).length=older.length+cs.length:=by
      simp only [List.length_append,List.length_map];omega
    have HE:=LeanCanny.Geometry.IntegralMixedOptionalEndpoints.step_heq
      (reframe (IntegralMixedFramedHistoryScript.run initial (cs.map (wrap Q hQ)++older)
        (by simp only [List.length_append,List.length_map];omega)) Q hQ)
      (IntegralMixedFullHistoryScript.continueRun
        (reframe (IntegralMixedFramedHistoryScript.run initial older ho) Q hQ) cs HT)
      (by simp only [List.length_append,List.length_map,List.length_cons] at hc ⊢;omega)
      (by simp only [List.length_cons] at hc;omega) HM (index_append Q hQ cs older) (ih HT) c
    change HEq (reframe (IntegralMixedFullHistoryScript.step _ _ c) Q hQ) _
    rw [reframe_self]
    exact HE

end LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
