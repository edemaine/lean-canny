/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
/-! # The entire constructed local tuple transports to the literal framed run -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem roots_heq {n S B m k :ℕ} {Q :SpatialSource n} {ι κ :Type}
    (x :State Q S B m ι) (y :State Q S B k κ) (hm :m=k) (hi :ι=κ) (hx :HEq x y)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∃w :κ→ℝ,HEq w z ∧ ∀i,(y.sampler.rows i).eval₂ (Int.castRingHom ℝ) w=0:=by
  subst k
  subst κ
  cases eq_of_heq hx
  exact ⟨z,HEq.rfl,hz⟩

theorem tuple_append {n S B :ℕ} {P :SpatialSource n}
    (initial :State P S B 0 (Fin 0)) (Q :SpatialSource n)
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (older :List (Instruction n B)) (ho :older.length≤S+1)
    (cs :List (IntegralMixedFullHistoryScript.Command Q B)) (hc :older.length+cs.length≤S+1)
    (z :IntegralMixedFullHistoryScript.Index (Index (Fin 0) older) cs→ℝ)
    (hz :∀i,((IntegralMixedFullHistoryScript.continueRun (reframe (run initial older ho) Q hQ) cs hc).sampler.rows i).eval₂
      (Int.castRingHom ℝ) z=0) :
    ∃y :Index (Fin 0) (cs.map (wrap Q hQ)++older)→ℝ,HEq y z ∧
      ∀i,((run initial (cs.map (wrap Q hQ)++older)
        (by simp only [List.length_append,List.length_map];omega)).sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0:=by
  have HM :(cs.map (wrap Q hQ)++older).length=older.length+cs.length:=by
    simp only [List.length_append,List.length_map]
    omega
  exact roots_heq _ _ HM.symm (index_append Q hQ cs older).symm
    (run_append initial Q hQ older ho cs hc).symm z hz

theorem tuple_list {n S B :ℕ} {P :SpatialSource n}
    (initial :State P S B 0 (Fin 0)) (cs ds :List (Instruction n B))
    (hc :cs.length≤S+1) (hd :ds.length≤S+1) (he :cs=ds)
    (z :Index (Fin 0) ds→ℝ) (hz :∀i,((run initial ds hd).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∃y :Index (Fin 0) cs→ℝ,HEq y z ∧∀i,((run initial cs hc).sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0:=by
  cases he
  exact ⟨z,HEq.rfl,hz⟩

end LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
