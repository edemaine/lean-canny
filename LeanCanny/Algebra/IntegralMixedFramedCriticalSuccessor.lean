/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalCreatingRows
/-! # A consecutive saved prefix is the literal creating critical step

Reframing the child to its creating source preserves its sampler and bank.
The next instruction's spatial source therefore need not be identified with
the creating source. The original horizon and width stay fixed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCriticalSuccessor
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryScript (Instruction run)
open IntegralMixedFramedHistoryFamilyBits (Plan family commands instruction keyAt prefixLength initial)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem run_congr {n S B : ℕ} {P Q : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B 0 ι) (cs ds : List (Instruction n B)) (he : cs=ds)
    (hs : cs.length≤S+1) (hd : ds.length≤S+1)
    (cap : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) :
    HEq (reframe (run x cs hs) Q cap) (reframe (run x ds hd) Q cap) :=by
  cases he
  rfl

private theorem run_critical {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B 0 ι) (c : Instruction n B) (cs : List (Instruction n B))
    (h : (c::cs).length≤S+1) (r : CriticalRule n) (hc : c.command=.critical r) :
    HEq (reframe (run x (c::cs) h) c.source c.source_cap)
      (criticalStep (reframe (run x cs (by simp only [List.length_cons] at h;omega)) c.source c.source_cap)
        (by simp only [List.length_cons] at h;omega) r) :=by
  cases c with
  | mk source cap command =>
    dsimp only at hc ⊢
    cases hc
    exact heq_of_eq (reframe_same _)

private theorem snapshots_congr (P : Parameters) (D : Plan P)
    (root root' : List Bool) (he : root'=root) (m m' : ℕ) (hm : m'=m)
    (hb : m≤P.cap root+1) (hb' : m'≤P.cap root'+1)
    {n : ℕ} (Q : SpatialSource n)
    (cap : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^P.width root)
    (cap' : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^P.width root') :
    HEq (reframe (run (initial P D root')
      (IntegralMixedFramedHistoryScript.paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root')
        (D.rules root') m') (by rw [IntegralMixedFramedHistoryScript.paddedPast_length];omega)) Q cap')
      (reframe (run (initial P D root)
        (IntegralMixedFramedHistoryScript.paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root)
          (D.rules root) m) (by rw [IntegralMixedFramedHistoryScript.paddedPast_length];omega)) Q cap) :=by
  cases he
  cases hm
  rfl

noncomputable local instance familyFintype (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    Fintype ((family P D H).physical key) :=
  inferInstanceAs (Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) (commands P D key)))

theorem successor (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key context : List Bool) (hb : prefixLength P key≤P.cap (pairFst key))
    (r : CriticalRule (P.ambient (pairFst key))) (hc : (instruction P D key).command=.critical r) :
    HEq (reframe ((family P D H).state (keyAt (pairFst key) (prefixLength P key+1) context))
      ((family P D H).spatial key) (by
        change _≤2^P.width (pairFst (keyAt (pairFst key) (prefixLength P key+1) context))
        rw [IntegralMixedFramedHistoryFamilyBits.keyAt_root]
        exact ((family P D H).state key).critical_cap))
      (criticalStep ((family P D H).state key) ((family P D H).birth_bound key) r) :=by
  let next:=keyAt (pairFst key) (prefixLength P key+1) context
  have HB : prefixLength P key+1≤P.cap (pairFst key)+1:=Nat.succ_le_succ hb
  have HE : IntegralMixedFramedHistoryScript.paddedPast
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key)) (D.rules (pairFst key))
      (prefixLength P key+1)=instruction P D key::commands P D key:=
    IntegralMixedFramedHistoryScript.paddedPast_succ _ _ _
  have HL : (instruction P D key::commands P D key).length≤(P.cap (pairFst key)+1)+1:=by
    rw [List.length_cons,commands,IntegralMixedFramedHistoryScript.paddedPast_length]
    omega
  have HR:=run_congr (initial P D (pairFst key)) _
    (instruction P D key::commands P D key) HE (by
      rw [IntegralMixedFramedHistoryScript.paddedPast_length]
      exact HB.trans (Nat.le_succ _)) HL (instruction P D key).source_cap
  have HS:=snapshots_congr P D (pairFst key) (pairFst next)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _) _ _
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P _ _ _ HB) HB (min_le_right _ _)
    (instruction P D key).source (instruction P D key).source_cap (by
      change _≤2^P.width (pairFst (keyAt (pairFst key) (prefixLength P key+1) context))
      rw [IntegralMixedFramedHistoryFamilyBits.keyAt_root]
      exact (instruction P D key).source_cap)
  exact HS.trans (HR.trans (run_critical (initial P D (pairFst key)) (instruction P D key) (commands P D key) HL r hc))

end LeanCanny.Algebra.IntegralMixedFramedCriticalSuccessor
