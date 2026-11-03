/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
public import LeanCanny.Algebra.IntegralMixedFramedCriticalSuccessorRows
/-! # Bank observation with the actual full physical scalar columns

The resulting data have no dependent carrier. Saved roots and chronological
lengths can therefore be normalized before any finite-index transport.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullBankObservation
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryScript (Instruction run)
open IntegralMixedFramedHistoryFamilyBits (Plan family commands instruction keyAt prefixLength initial)
open IntegralMixedFramedPhysicalIndex (arity enumerate stepEquiv)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Data where
  bank : IntegralMixedFramedBankObservation.Data
  column : ℕ→ℕ

noncomputable def ofState {n S B m a : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (e : ι≃Fin a) : Data where
  bank:=IntegralMixedFramedBankObservation.ofState x
  column i:=if hi : i<m then (e (x.sampler.scalar ⟨i,hi⟩)).val else 0

noncomputable def Data.point (d : Data) (z : ℕ→ℝ) (i : ℕ) : ℝ:=
  d.bank.point (fun j=>z (d.column j)) i

theorem point_ofState {n S B m a : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (e : ι≃Fin a) (z : ℕ→ℝ) (i : Fin m) :
    (ofState x e).point z i.val=LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point x
      (fun j=>z (e (x.sampler.scalar j)).val) i :=by
  simp only [Data.point,ofState,IntegralMixedFramedBankObservation.Data.point,
    IntegralMixedFramedBankObservation.ofState,dite_eq_left i.isLt]
  rfl

noncomputable def ofRun {n S B : ℕ} {P : SpatialSource n}
    (x : State P S B 0 (Fin 0)) (cs : List (Instruction n B)) (h : cs.length≤S+1) : Data:=
  ofState (run x cs h) (enumerate cs)

private theorem run_congr {n S B : ℕ} {P : SpatialSource n}
    (x : State P S B 0 (Fin 0)) (cs ds : List (Instruction n B)) (he : cs=ds)
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) : ofRun x cs hc=ofRun x ds hd:=by
  cases he
  rfl

noncomputable def atRun (P : Parameters) (D : Plan P) (root : List Bool) (m : ℕ)
    (hm : m≤P.cap root+1) : Data:=
  ofRun (initial P D root)
    (IntegralMixedFramedHistoryScript.paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root)
      (D.rules root) m) (by rw [IntegralMixedFramedHistoryScript.paddedPast_length];omega)

private theorem atRun_congr (P : Parameters) (D : Plan P) (root root' : List Bool) (m m' : ℕ)
    (hr : root'=root) (hm : m'=m) (hb : m≤P.cap root+1) (hb' : m'≤P.cap root'+1) :
    atRun P D root' m' hb'=atRun P D root m hb:=by
  cases hr
  cases hm
  rfl

noncomputable def atFamily (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) : Data:=ofState ((family P D H).state key) (enumerate (commands P D key))

private theorem criticalRun {n S B : ℕ} {P : SpatialSource n}
    (x : State P S B 0 (Fin 0)) (c : Instruction n B) (cs : List (Instruction n B))
    (h : (c::cs).length≤S+1) (r : CriticalRule n) (hc : c.command=.critical r) :
    ofRun x (c::cs) h=ofState
      (criticalStep (reframe (run x cs (by simp only [List.length_cons] at h;omega)) c.source c.source_cap)
        (by simp only [List.length_cons] at h;omega) r)
      (stepEquiv (.critical (P:=c.source) (B:=B) r) (enumerate cs)) :=by
  cases c with
  | mk source cap command =>
    dsimp only at hc ⊢
    cases hc
    rfl

noncomputable local instance familyFintype (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    Fintype ((family P D H).physical key) :=
  inferInstanceAs (Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) (commands P D key)))

theorem successor (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key context : List Bool) (hb : prefixLength P key≤P.cap (pairFst key))
    (r : CriticalRule (P.ambient (pairFst key))) (hc : (instruction P D key).command=.critical r) :
    atFamily P D H (keyAt (pairFst key) (prefixLength P key+1) context)=
      ofState (criticalStep ((family P D H).state key) ((family P D H).birth_bound key) r)
        (stepEquiv (.critical (P:=(family P D H).spatial key) (B:=P.width (pairFst key)) r)
          (enumerate (commands P D key))) :=by
  have HB : prefixLength P key+1≤P.cap (pairFst key)+1:=Nat.succ_le_succ hb
  have HA : atFamily P D H (keyAt (pairFst key) (prefixLength P key+1) context)=
      atRun P D (pairFst key) (prefixLength P key+1) HB:=
    atRun_congr P D _ _ _ _ (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
      (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P _ _ _ HB) HB (min_le_right _ _)
  have HL : (instruction P D key::commands P D key).length≤(P.cap (pairFst key)+1)+1:=by
    rw [List.length_cons,commands,IntegralMixedFramedHistoryScript.paddedPast_length]
    omega
  have HE:=run_congr (initial P D (pairFst key)) _ (instruction P D key::commands P D key)
    (IntegralMixedFramedHistoryScript.paddedPast_succ
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key)) (D.rules (pairFst key))
      (prefixLength P key)) (by rw [IntegralMixedFramedHistoryScript.paddedPast_length];omega) HL
  exact HA.trans (HE.trans (criticalRun (initial P D (pairFst key)) (instruction P D key)
    (commands P D key) HL r hc))

end LeanCanny.Algebra.IntegralMixedFullBankObservation
