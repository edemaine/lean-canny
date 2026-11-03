/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshot
public import LeanCanny.Algebra.IntegralMixedFramedFamilyRunView
/-! # An actual saved family has the literal static-source prefix snapshot -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPrefixSnapshot
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family initial instruction commands defaultInstruction prefixLength keyAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem reframe_source_congr {n r S B m : ℕ} {Q : SpatialSource n} {ι : Type}
    (x : State Q S B m ι) (P R : SpatialSource r)
    (hP : PurePowerReductionBounds.dimension (r+1) P.degree≤2^B)
    (hR : PurePowerReductionBounds.dimension (r+1) R.degree≤2^B) (he : P=R) :
    ofState (reframe x P hP)=ofState (reframe x R hR):=by cases he;rfl

noncomputable def atRoot (P : Parameters) (D : Plan P) (root : List Bool) (m : ℕ) (hb : m≤P.cap root+1) :=
 ofCommands (initial P D root) (paddedPast (defaultInstruction P D root) (D.rules root) m)
   (by rw [paddedPast_length];exact hb.trans (Nat.le_succ _))

theorem atRoot_congr (P : Parameters) (D : Plan P) (r s : List Bool) (a b : ℕ)
    (hr : a≤P.cap r+1) (hs : b≤P.cap s+1) (he : r=s) (hb : a=b) :
    atRoot P D r a hr=atRoot P D s b hs:=by cases he;cases hb;rfl

noncomputable def originalAtKey (P : Parameters) (D : Plan P) (key : List Bool) :=
 ofCommands (initial P D (pairFst key)) (commands P D key)
   (by rw [commands,paddedPast_length];exact (min_le_right _ _).trans (Nat.le_succ _))

theorem family_eq_original (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (hs : (instruction P D key).source=D.initialSource (pairFst key)) :
    ofState ((family P D H).state key)=originalAtKey P D key:=
 reframe_source_congr _ _ _ _ _ hs

theorem original_keyAt (P : Parameters) (D : Plan P) (root aux : List Bool) (m : ℕ) (hm : m≤P.cap root+1) :
    originalAtKey P D (keyAt root m aux)=atRoot P D root m hm:=by
 let key:=keyAt root m aux
 have HE :originalAtKey P D key=atRoot P D (pairFst key) (prefixLength P key) (min_le_right _ _):=rfl
 exact HE.trans (atRoot_congr P D _ root _ m _ hm (IntegralMixedFramedHistoryFamilyBits.keyAt_root root m aux)
   (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root m aux hm))

end LeanCanny.Algebra.IntegralMixedPrefixSnapshot
