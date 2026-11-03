/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalPrefixRealization
public import LeanCanny.Algebra.IntegralMixedFramedRunObservation
/-! # One full joint tuple satisfies the actual natural prefix observation -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalPrefixObservation
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (Plan family initial defaultInstruction prefixLength)
open IntegralMixedFramedPhysicalIndex (enumerate)
open IntegralMixedFramedRunObservation (ofCommands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def atRoot (P : Parameters) (D : Plan P) (root : List Bool) (m : ℕ) (hb : m≤P.cap root+1) :=
 ofCommands (initial P D root) (paddedPast (defaultInstruction P D root) (D.rules root) m)
   (by rw [paddedPast_length];exact hb.trans (Nat.le_succ _))

theorem at_congr (P : Parameters) (D : Plan P) (r s : List Bool) (m k : ℕ)
    (hr : m≤P.cap r+1) (hs : k≤P.cap s+1) (he : r=s) (hm : m=k) : atRoot P D r m hr=atRoot P D s k hs:=by
  cases he
  cases hm
  rfl

theorem at_roots (P : Parameters) (D : Plan P) (root : List Bool) (m : ℕ) (hb : m≤P.cap root+1) (z : ℕ→ℝ) :
    (atRoot P D root m hb).Roots z ↔
      ∀i,((IntegralMixedFramedFamilyRunView.runAt P D root m hb).sampler.rows i).eval₂ (Int.castRingHom ℝ)
        (fun j=>z (enumerate (paddedPast (defaultInstruction P D root) (D.rules root) m) j).val)=0 :=
  IntegralMixedFramedRunObservation.roots_actual _ _ _ _

theorem at_realizes (P : Parameters) (D : Plan P) (root : List Bool) (m : ℕ) (hb : m≤P.cap root+1) (z : ℕ→ℝ)
    (hz : (atRoot P D root m hb).Roots z) :
    IntegralMixedIntegerRealization.Realizes (IntegralMixedFramedFamilyRunView.runAt P D root m hb)
      ((atRoot P D root m hb).point z) :=by
  have HR:=(at_roots P D root m hb z).mp hz
  have HC : Canonical (IntegralMixedFramedFamilyRunView.runAt P D root m hb):=by
    apply run_canonical
    intro i
    exact Fin.elim0 i
  obtain ⟨φ,hφ,hvalues⟩:=IntegralMixedFullBankPoint.interprets
    (IntegralMixedFramedFamilyRunView.runAt P D root m hb) HC _ HR
  refine ⟨_,φ,HR,hφ,?_⟩
  intro i
  exact (hvalues i).trans (IntegralMixedFramedRunObservation.point_actual (initial P D root)
    (paddedPast (defaultInstruction P D root) (D.rules root) m) _ z i).symm

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
 (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
 (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
 (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hpos) c w)

noncomputable def tuple : ℕ→ℝ :=IntegralMixedFramedBankObservation.extend
 (IntegralFramedPhysicalSquare.joint P D H L F C hs key hpos c w hv)

theorem raw_tuple (m : ℕ) (hm : m≤prefixLength P (key c))
    (i : Index (Fin 0) (IntegralFramedPhysicalPrefixRealization.past P D key c m)) :
    IntegralFramedPhysicalPrefixRealization.raw P D H L F C hs key hpos c w hv m hm i=
      tuple P D H L F C hs key hpos c w hv
        (enumerate (IntegralFramedPhysicalPrefixRealization.past P D key c m) i).val :=by
  have HI : (enumerate (IntegralFramedPhysicalPrefixRealization.past P D key c m) i).val<
      IntegralFramedPhysicalSquare.count P D (key c):=by
    rw [←IntegralFramedPhysicalPrefixRealization.column P D key c m hm i]
    exact (enumerate (IntegralMixedFramedHistoryFamilyBits.commands P D (key c))
      (IntegralFramedPhysicalPrefixRealization.embedding P D key c m hm i)).isLt
  unfold tuple IntegralMixedFramedBankObservation.extend
  rw [dite_eq_left HI]
  exact IntegralFramedPhysicalPrefixRealization.raw_column P D H L F C hs key hpos c w hv m hm i

theorem roots (m : ℕ) (hm : m≤prefixLength P (key c)) :
    (atRoot P D (pairFst (key c)) m (hm.trans (min_le_right _ _))).Roots
      (tuple P D H L F C hs key hpos c w hv) :=by
  apply (at_roots P D (pairFst (key c)) m (hm.trans (min_le_right _ _)) _).mpr
  have HE : (fun j=>tuple P D H L F C hs key hpos c w hv
      (enumerate (IntegralFramedPhysicalPrefixRealization.past P D key c m) j).val)=
      IntegralFramedPhysicalPrefixRealization.raw P D H L F C hs key hpos c w hv m hm:=by
    funext j
    exact (raw_tuple P D H L F C hs key hpos c w hv m hm j).symm
  rw [HE]
  exact IntegralFramedPhysicalPrefixRealization.raw_roots P D H L F C hs key hpos c w hv m hm

end LeanCanny.Encoding.IntegralFramedPhysicalPrefixObservation
