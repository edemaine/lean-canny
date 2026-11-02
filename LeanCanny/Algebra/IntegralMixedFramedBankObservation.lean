/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFamilyTerminalRows
public import LeanCanny.Geometry.IntegralMixedCanonicalBankPoint

/-! # Source-independent data for the actual bank-point readback

Bundling the horizon, width, count and integer denominators permits ordinary
transport across saved prefixes and spatial reframing. The joint scalar
coordinates remain arguments; no roots are chosen independently.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankObservation
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

structure Data where
  horizon : ℕ
  width : ℕ
  count : ℕ
  denominator : Fin count→ℤ

noncomputable def ofState {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) : Data := ⟨S,B,m,x.bank.denominator⟩

noncomputable def Data.point (d : Data) (z : ℕ→ℝ) (i : ℕ) : ℝ :=
  if hi : i<d.count then
    z i^UniformIntegralPowerSchedule.weights d.horizon (2^d.width) d.count ⟨i,hi⟩ /
      (d.denominator ⟨i,hi⟩:ℝ)
  else 0

noncomputable def extend {m : ℕ} (z : Fin m→ℝ) (i : ℕ) : ℝ :=
  if hi : i<m then z ⟨i,hi⟩ else 0

theorem point_ofState {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (z : Fin m→ℝ) (i : Fin m) :
    (ofState x).point (extend z) i.val=
      LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point x z i := by
  simp only [Data.point,ofState,dite_eq_left i.isLt,extend]
  rfl

theorem reframe_data {n S B m r : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (Q : SpatialSource r)
    (hQ : PurePowerReductionBounds.dimension (r+1) Q.degree≤2^B) :
    ofState (reframe x Q hQ)=ofState x := rfl

noncomputable def atRun (P : Parameters) (D : Plan P) (root : List Bool) (birth : ℕ)
    (hb : birth≤P.cap root+1) : Data :=
  ofState (IntegralMixedFramedFamilyRunView.runAt P D root birth hb)

theorem atRun_congr (P : Parameters) (D : Plan P) (r s : List Bool) (i j : ℕ)
    (hr : r=s) (hi : i=j) (hc : i≤P.cap r+1) (hd : j≤P.cap s+1) :
    atRun P D r i hc=atRun P D s j hd := by
  cases hr
  cases hi
  rfl

private theorem run_data_congr {n S B : ℕ} {P : SpatialSource n}
    (initial : State P S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (he : cs=ds) (hc : cs.length≤S+1) (hd : ds.length≤S+1) :
    ofState (run initial cs hc)=ofState (run initial ds hd) := by
  cases he
  rfl

theorem terminal (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (root : List Bool) (m : ℕ) (hm : m≤P.cap root) (hlen : (D.rules root).length=m) :
    ofState ((IntegralMixedFramedHistoryFamilyBits.family P D H).state
      (IntegralMixedFramedHistoryFamilyBits.keyAt root (m+1) []))=
    ofState (run (IntegralMixedFramedHistoryFamilyBits.initial P D root)
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root::D.rules root)
      (by simp only [List.length_cons,hlen]; omega)) := by
  let key:=IntegralMixedFramedHistoryFamilyBits.keyAt root (m+1) []
  have H1 : ofState ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key)=
      atRun P D (pairFst key) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (min_le_right _ _) := rfl
  refine H1.trans ((atRun_congr P D _ root _ (m+1) (pairFst_pair _ _)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root (m+1) [] (Nat.succ_le_succ hm))
    (min_le_right _ _) (Nat.succ_le_succ hm)).trans ?_)
  apply run_data_congr
  rw [←hlen]
  exact paddedPast_after _ _
end LeanCanny.Algebra.IntegralMixedFramedBankObservation
