/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalSuccessor
/-! # All rows of the native successor are the literal critical-step rows

Natural column indices remove dependent casts while preserving the actual
oldest-first enumeration. This includes older rows and the fresh scalar row,
as well as the new physical critical block.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCriticalSuccessorRows
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory MvPolynomial
open IntegralMixedFramedHistoryScript (Instruction run)
open IntegralMixedFramedHistoryFamilyBits (Plan family commands instruction keyAt prefixLength initial)
open IntegralMixedFramedPhysicalIndex (arity enumerate stepEquiv)
open IntegralMixedFramedPhysicalRowTransport
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem natRows_critical {n S B : ℕ} {P : SpatialSource n}
    (x : State P S B 0 (Fin 0)) (c : Instruction n B) (cs : List (Instruction n B))
    (h : (c::cs).length≤S+1) (r : CriticalRule n) (hc : c.command=.critical r) (i : ℕ) :
    natRows x (c::cs) h i=
      if hi : i<arity cs+IntegralMixedFramedPhysicalIndex.added (.critical (P:=c.source) (B:=B) r) then
        rename Fin.val (PolynomialSystemReindex.system (stepEquiv (.critical (P:=c.source) (B:=B) r) (enumerate cs))
          (criticalStep (reframe (run x cs (by simp only [List.length_cons] at h;omega)) c.source c.source_cap)
            (by simp only [List.length_cons] at h;omega) r).sampler.rows ⟨i,hi⟩) else 0 :=by
  cases c with
  | mk source cap command =>
    dsimp only at hc ⊢
    cases hc
    rfl

noncomputable local instance familyFintype (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    Fintype ((family P D H).physical key) :=
  inferInstanceAs (Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) (commands P D key)))

noncomputable def rows (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (r : CriticalRule (P.ambient (pairFst key))) (i : ℕ) : MvPolynomial ℕ ℤ :=
  if hi : i<arity (commands P D key)+IntegralMixedFramedPhysicalIndex.added
      (.critical (P:=(family P D H).spatial key) (B:=P.width (pairFst key)) r) then
    rename Fin.val (PolynomialSystemReindex.system (stepEquiv
      (.critical (P:=(family P D H).spatial key) (B:=P.width (pairFst key)) r) (enumerate (commands P D key)))
      (criticalStep ((family P D H).state key) ((family P D H).birth_bound key) r).sampler.rows ⟨i,hi⟩) else 0

theorem keyRow_successor (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key context : List Bool) (hb : prefixLength P key≤P.cap (pairFst key))
    (r : CriticalRule (P.ambient (pairFst key))) (hc : (instruction P D key).command=.critical r) (i : ℕ) :
    keyRow P D (keyAt (pairFst key) (prefixLength P key+1) context) i=rows P D H key r i :=by
  have HS : (instruction P D key::commands P D key).length≤(P.cap (pairFst key)+1)+1:=by
    rw [List.length_cons,commands,IntegralMixedFramedHistoryScript.paddedPast_length]
    omega
  exact (IntegralMixedFramedPhysicalCreatingRows.keyRow_succ P D key context hb i).trans
    (natRows_critical (initial P D (pairFst key)) (instruction P D key) (commands P D key) HS r hc i)

noncomputable def tuple (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (r : CriticalRule (P.ambient (pairFst key))) (z : ℕ→ℝ) :
    (((family P D H).physical key⊕FlatAffineCriticalStage.Variables (P.ambient (pairFst key)+1))⊕Unit)→ℝ :=
  fun i=>z (stepEquiv (.critical (P:=(family P D H).spatial key) (B:=P.width (pairFst key)) r)
    (enumerate (commands P D key)) i).val

theorem rows_zero_iff (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (r : CriticalRule (P.ambient (pairFst key))) (z : ℕ→ℝ) :
    (∀i,(rows P D H key r i).eval₂ (Int.castRingHom ℝ) z=0) ↔
      ∀i,((criticalStep ((family P D H).state key) ((family P D H).birth_bound key) r).sampler.rows i).eval₂
        (Int.castRingHom ℝ) (tuple P D H key r z)=0 :=by
  let e:=stepEquiv (.critical (P:=(family P D H).spatial key) (B:=P.width (pairFst key)) r)
    (enumerate (commands P D key))
  constructor
  · intro HZ i
    have HE:=HZ (e i).val
    rw [rows,dite_eq_left (e i).isLt,MvPolynomial.eval₂_rename,
      PolynomialSystemReindex.system,MvPolynomial.eval₂_rename] at HE
    change ((criticalStep ((family P D H).state key) ((family P D H).birth_bound key) r).sampler.rows
      (e.symm (e i))).eval₂ (Int.castRingHom ℝ) (tuple P D H key r z)=0 at HE
    simpa only [Equiv.symm_apply_apply] using HE
  · intro HZ i
    unfold rows
    split_ifs with hi
    · rw [MvPolynomial.eval₂_rename,PolynomialSystemReindex.system,MvPolynomial.eval₂_rename]
      exact HZ (e.symm ⟨i,hi⟩)
    · exact MvPolynomial.eval₂_zero _ _

end LeanCanny.Algebra.IntegralMixedFramedCriticalSuccessorRows
