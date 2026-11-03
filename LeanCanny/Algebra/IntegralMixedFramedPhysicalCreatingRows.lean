/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalNaturalRows
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalFamily

/-! # The actual saved creating prefix is the literal critical step -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalCreatingRows
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory MvPolynomial
open IntegralMixedFramedHistoryScript (Instruction run paddedPast paddedPast_length)
open IntegralMixedFramedHistoryFamilyBits (Plan commands prefixLength initial defaultInstruction instruction keyAt family)
open IntegralMixedFramedPhysicalIndex (arity enumerate criticalEquiv stepEquiv)
open IntegralMixedFramedPhysicalRowTransport
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem keyRow_at (P : Parameters) (D : Plan P) (root : List Bool) (m : ℕ)
    (hm : m≤P.cap root+1) (context : List Bool) (r : ℕ) :
    keyRow P D (keyAt root m context) r=rowAt P D root m hm r :=
  rowAt_congr P D _ root _ m (min_le_right _ _) hm
    (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root m context hm) r

theorem keyRow_succ (P : Parameters) (D : Plan P) (key context : List Bool)
    (hb : prefixLength P key≤P.cap (pairFst key)) (r : ℕ) :
    keyRow P D (keyAt (pairFst key) (prefixLength P key+1) context) r=
      natRows (initial P D (pairFst key)) (instruction P D key::commands P D key)
        (by rw [List.length_cons,commands,paddedPast_length];omega) r :=by
  have HM : prefixLength P key+1≤P.cap (pairFst key)+1:=Nat.succ_le_succ hb
  have HE : paddedPast (defaultInstruction P D (pairFst key)) (D.rules (pairFst key)) (prefixLength P key+1)=
      instruction P D key::commands P D key :=
    IntegralMixedFramedHistoryScript.paddedPast_succ _ _ _
  exact (keyRow_at P D (pairFst key) _ HM context r).trans
    (natRows_congr (initial P D (pairFst key)) _ _ HE _ _ r)

private theorem instruction_critical {n B : ℕ} (c : Instruction n B) (r : CriticalRule n)
    (hc : c.command=.critical r) :
    c=IntegralMixedFramedCriticalNaturalRows.criticalInstruction c.source c.source_cap r :=by
  cases c with
  | mk source cap command =>
    dsimp only at hc ⊢
    cases hc
    rfl

noncomputable local instance familyFintype (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    Fintype ((family P D H).physical key) :=
  inferInstanceAs (Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) (commands P D key)))

theorem critical_creating_rows (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key context : List Bool) (hb : prefixLength P key≤P.cap (pairFst key))
    (r : CriticalRule (P.ambient (pairFst key))) (hc : (instruction P D key).command=.critical r)
    (j : FlatAffineCriticalStage.Variables (P.ambient (pairFst key)+1)) :
    keyRow P D (keyAt (pairFst key) (prefixLength P key+1) context)
      (arity (commands P D key)+(criticalEquiv j).val)=
    rename Fin.val (PolynomialSystemReindex.system
      (stepEquiv (.critical r) (enumerate (commands P D key)))
      (IntegralMixedFullHistoryScript.step ((family P D H).state key) ((family P D H).birth_bound key) (.critical r)).sampler.rows
      (stepEquiv (.critical r) (enumerate (commands P D key)) (Sum.inl (Sum.inr j)))) :=by
  let cs:=commands P D key
  let c:=instruction P D key
  let x:=initial P D (pairFst key)
  have HS : cs.length≤P.cap (pairFst key)+1 :=by
    dsimp only [cs]
    rw [IntegralMixedFramedHistoryFamilyBits.commands,paddedPast_length]
    exact min_le_right _ _
  have HE:=instruction_critical c r hc
  have HN:=IntegralMixedFramedCriticalNaturalRows.natRows_critical x cs HS c.source c.source_cap r j
  have HL : (c::cs).length≤(P.cap (pairFst key)+1)+1 :=by simp only [List.length_cons];omega
  have HL' : (IntegralMixedFramedCriticalNaturalRows.criticalInstruction c.source c.source_cap r::cs).length≤
      (P.cap (pairFst key)+1)+1 :=by simp only [List.length_cons];omega
  have HC:=natRows_congr x (c::cs) _ (congrArg (fun I=>I::cs) HE) HL HL' (arity cs+(criticalEquiv j).val)
  have HP:=congrArg (rename Fin.val)
    (IntegralMixedFramedPhysicalIndex.critical_new_row ((family P D H).state key)
      (enumerate (commands P D key)) ((family P D H).birth_bound key) r j)
  exact (keyRow_succ P D key context hb _).trans (HC.trans (HN.trans HP.symm))

end LeanCanny.Algebra.IntegralMixedFramedPhysicalCreatingRows
