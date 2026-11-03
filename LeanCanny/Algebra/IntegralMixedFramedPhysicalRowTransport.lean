/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalPersistence
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalDegreeValues
public import LeanCanny.Algebra.IntegralMixedFramedFamilyRunView

/-! # Saved full indexed rows retain their literal creating polynomial

Natural variables hide only the varying finite arity. Oldest-first column
numbers themselves never change, including across saved contexts.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalRowTransport
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryScript (Instruction run paddedPast paddedPast_length)
open IntegralMixedFramedPhysicalIndex (arity enumerate)
open IntegralMixedFramedHistoryFamilyBits (Plan commands prefixLength initial defaultInstruction)
open IntegralMixedFramedPhysicalPersistence
open MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def natRows {n S B : ℕ} {P : SpatialSource n} (x : State P S B 0 (Fin 0))
    (cs : List (Instruction n B)) (hc : cs.length≤S+1) (r : ℕ) : MvPolynomial ℕ ℤ :=
  if hr : r<arity cs then rename Fin.val
    (PolynomialSystemReindex.system (enumerate cs) (run x cs hc).sampler.rows ⟨r,hr⟩) else 0

theorem natRows_congr {n S B : ℕ} {P : SpatialSource n} (x : State P S B 0 (Fin 0))
    (cs ds : List (Instruction n B)) (he : cs=ds) (hc : cs.length≤S+1) (hd : ds.length≤S+1) (r : ℕ) :
    natRows x cs hc r=natRows x ds hd r :=by cases he;rfl

private theorem rename_castLE {a b : ℕ} (h : a≤b) (p : MvPolynomial (Fin a) ℤ) :
    rename Fin.val (rename (Fin.castLE h) p)=rename Fin.val p :=by
  rw [rename_rename]
  rfl

theorem natRows_append {n S B : ℕ} {P : SpatialSource n} (x : State P S B 0 (Fin 0))
    (newer older : List (Instruction n B)) (h : (newer++older).length≤S+1) (ho : older.length≤S+1)
    (r : ℕ) (hr : r<arity older) :
    natRows x (newer++older) h r=natRows x older ho r :=by
  have HM:=arity_le_append newer older
  have HT : r<arity (newer++older):=hr.trans_le HM
  have HE : Fin.castLE HM (⟨r,hr⟩ : Fin (arity older))=(⟨r,HT⟩ : Fin (arity (newer++older))) :=Fin.ext rfl
  have HX:=congrArg (rename Fin.val) (run_indexed_rows x newer older h ho ⟨r,hr⟩)
  rw [HE,rename_castLE] at HX
  simpa only [natRows,dite_eq_left HT,dite_eq_left hr] using HX

theorem natRows_padded {n S B : ℕ} {P : SpatialSource n} (x : State P S B 0 (Fin 0))
    (fallback : Instruction n B) (cs : List (Instruction n B)) (m b : ℕ)
    (hm : m≤S+1) (hb : b≤m) (r : ℕ) (hr : r<arity (paddedPast fallback cs b)) :
    natRows x (paddedPast fallback cs m) (by rw [paddedPast_length];exact hm) r=
      natRows x (paddedPast fallback cs b) (by rw [paddedPast_length];exact hb.trans hm) r :=by
  let newer:=(paddedPast fallback cs m).take (m-b)
  have HE:=IntegralMixedFramedPhysicalDegreeValues.padded_split fallback cs m b hb
  have HC : (newer++paddedPast fallback cs b).length≤S+1 :=by rw [←HE,paddedPast_length];exact hm
  exact (natRows_congr x _ _ HE _ HC r).trans
    (natRows_append x newer (paddedPast fallback cs b) HC _ r hr)

noncomputable def countAt (P : Parameters) (D : Plan P) (root : List Bool) (b : ℕ) :=
  arity (paddedPast (defaultInstruction P D root) (D.rules root) b)

noncomputable def rowAt (P : Parameters) (D : Plan P) (root : List Bool) (b : ℕ)
    (hb : b≤P.cap root+1) (r : ℕ) :=
  natRows (initial P D root) (paddedPast (defaultInstruction P D root) (D.rules root) b)
    (by rw [paddedPast_length];exact hb.trans (Nat.le_succ _)) r

noncomputable def keyRow (P : Parameters) (D : Plan P) (key : List Bool) (r : ℕ) :=
  rowAt P D (pairFst key) (prefixLength P key) (min_le_right _ _) r

theorem count_view (P : Parameters) (D : Plan P) (key : List Bool) :
    arity (commands P D key)=countAt P D (pairFst key) (prefixLength P key) :=rfl

theorem rowAt_congr (P : Parameters) (D : Plan P) (s t : List Bool) (a b : ℕ)
    (hs : a≤P.cap s+1) (ht : b≤P.cap t+1) (hr : s=t) (hb : a=b) (r : ℕ) :
    rowAt P D s a hs r=rowAt P D t b ht r :=by cases hr;cases hb;rfl

theorem countAt_mono (P : Parameters) (D : Plan P) (root : List Bool) (a b : ℕ) (hab : a≤b) :
    countAt P D root a≤countAt P D root b :=by
  unfold countAt
  rw [IntegralMixedFramedPhysicalDegreeValues.padded_split _ _ b a hab]
  exact arity_le_append _ _

theorem key_count_le (P : Parameters) (D : Plan P) (older terminal : List Bool)
    (hroot : pairFst older=pairFst terminal) (hfit : prefixLength P older≤prefixLength P terminal) :
    arity (commands P D older)≤arity (commands P D terminal) :=by
  rw [count_view,count_view,hroot]
  exact countAt_mono P D _ _ _ hfit

theorem key_rows (P : Parameters) (D : Plan P) (older terminal : List Bool)
    (hroot : pairFst older=pairFst terminal) (hfit : prefixLength P older≤prefixLength P terminal)
    (r : ℕ) (hr : r<arity (commands P D older)) :
    keyRow P D terminal r=keyRow P D older r :=by
  have HM : prefixLength P terminal≤P.cap (pairFst terminal)+1:=min_le_right _ _
  have HB : prefixLength P older≤P.cap (pairFst terminal)+1:=hfit.trans HM
  have HO:=rowAt_congr P D (pairFst older) (pairFst terminal) (prefixLength P older) (prefixLength P older)
    (min_le_right _ _) HB hroot rfl r
  have HR : r<countAt P D (pairFst terminal) (prefixLength P older) :=by
    rw [count_view,hroot] at hr
    exact hr
  exact (natRows_padded (initial P D (pairFst terminal)) (defaultInstruction P D (pairFst terminal))
    (D.rules (pairFst terminal)) _ _ (HM.trans (Nat.le_succ _)) hfit r HR).trans HO.symm

noncomputable def indexedRow (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : Fin (arity (commands P D key))) :=
  PolynomialSystemReindex.system (enumerate (commands P D key))
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).sampler.rows i

theorem keyRow_family (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (r : ℕ) (hr : r<arity (commands P D key)) :
    keyRow P D key r=rename Fin.val (indexedRow P D H key ⟨r,hr⟩) :=by
  change natRows (initial P D (pairFst key)) (commands P D key) _ r=rename Fin.val (indexedRow P D H key ⟨r,hr⟩)
  rw [natRows,dite_eq_left hr]
  rfl

theorem indexed_key_rows (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (older terminal : List Bool) (hroot : pairFst older=pairFst terminal)
    (hfit : prefixLength P older≤prefixLength P terminal) (i : Fin (arity (commands P D older))) :
    indexedRow P D H terminal (Fin.castLE (key_count_le P D older terminal hroot hfit) i)=
      rename (Fin.castLE (key_count_le P D older terminal hroot hfit)) (indexedRow P D H older i) :=by
  have HT : i.val<arity (commands P D terminal):=i.isLt.trans_le (key_count_le P D older terminal hroot hfit)
  have HE:=key_rows P D older terminal hroot hfit i.val i.isLt
  rw [keyRow_family P D H terminal i.val HT,keyRow_family P D H older i.val i.isLt] at HE
  apply (MvPolynomial.rename_injective (f:=Fin.val) Fin.val_injective)
  rw [rename_castLE]
  exact HE

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (T : IntegralMixedHeaderTablesBits.Tables)
  (ht : IntegralMixedFramedHeaderBits.Represents P D H T)

noncomputable def creatingAt (key : List Bool) (r : ℕ) (context : List Bool) :=
  IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst key)
    (IntegralMixedFramedPhysicalRowSelector.rowBirth P T (pair key (BinaryNatCode.encode r))+1) context

include ht in
theorem native_full_count (key : List Bool) (r : ℕ) :
    IntegralMixedFramedPhysicalRowSelector.fullArity P T (pair key (BinaryNatCode.encode r))=
      arity (commands P D key) :=by
  simp only [IntegralMixedFramedPhysicalRowSelector.fullArity,pairFst_pair]
  exact IntegralMixedFramedPhysicalIndex.prefixArity_packet P D H T ht key _

theorem creatingAt_root (key : List Bool) (r : ℕ) (context : List Bool) :
    pairFst (creatingAt P T key r context)=pairFst key :=
  IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _

include ht in
theorem creatingAt_prefix (key : List Bool) (r : ℕ) (context : List Bool)
    (hr : r<arity (commands P D key)) :
    prefixLength P (creatingAt P T key r context)=
      IntegralMixedFramedPhysicalRowSelector.rowBirth P T (pair key (BinaryNatCode.encode r))+1 :=by
  have HR:=hr.trans_eq (native_full_count P D H T ht key r).symm
  have HB:=(IntegralMixedFramedPhysicalRowSelector.rowBirth_interval P T key r HR).1
  apply IntegralMixedFramedHistoryFamilyBits.keyAt_prefix
  exact (Nat.succ_le_of_lt HB).trans (min_le_right _ _)

include ht in
theorem creatingAt_fits (key : List Bool) (r : ℕ) (context : List Bool)
    (hr : r<arity (commands P D key)) :
    prefixLength P (creatingAt P T key r context)≤prefixLength P key :=by
  rw [creatingAt_prefix P D H T ht key r context hr]
  exact Nat.succ_le_of_lt
    (IntegralMixedFramedPhysicalRowSelector.rowBirth_interval P T key r
      (hr.trans_eq (native_full_count P D H T ht key r).symm)).1

include ht in
theorem creatingAt_count (key : List Bool) (r : ℕ) (context : List Bool)
    (hr : r<arity (commands P D key)) :
    arity (commands P D (creatingAt P T key r context))=
      IntegralMixedFramedPhysicalIndex.prefixArity P T
        (pair key (List.replicate
          (IntegralMixedFramedPhysicalRowSelector.rowBirth P T (pair key (BinaryNatCode.encode r))+1) true)) :=by
  rw [count_view,creatingAt_root,creatingAt_prefix P D H T ht key r context hr]
  exact (IntegralMixedFramedPhysicalIndex.prefixArity_packet P D H T ht key _).symm

include ht in
theorem creatingAt_valid (key : List Bool) (r : ℕ) (context : List Bool)
    (hr : r<arity (commands P D key)) :
    r<arity (commands P D (creatingAt P T key r context)) :=by
  rw [creatingAt_count P D H T ht key r context hr]
  exact (IntegralMixedFramedPhysicalRowSelector.rowBirth_interval P T key r
    (hr.trans_eq (native_full_count P D H T ht key r).symm)).2.2

include ht in
theorem creatingAt_le (key : List Bool) (r : ℕ) (context : List Bool)
    (hr : r<arity (commands P D key)) :
    arity (commands P D (creatingAt P T key r context))≤arity (commands P D key) :=
  key_count_le P D _ key (creatingAt_root P T key r context) (creatingAt_fits P D H T ht key r context hr)

theorem creatingAt_rows (key : List Bool) (r : ℕ) (context : List Bool)
    (hr : r<arity (commands P D key)) :
    indexedRow P D H key ⟨r,hr⟩=
      rename (Fin.castLE (creatingAt_le P D H T ht key r context hr))
        (indexedRow P D H (creatingAt P T key r context)
          ⟨r,creatingAt_valid P D H T ht key r context hr⟩) :=by
  let i : Fin (arity (commands P D (creatingAt P T key r context))) :=
    ⟨r,creatingAt_valid P D H T ht key r context hr⟩
  have HE:=indexed_key_rows P D H (creatingAt P T key r context) key (creatingAt_root P T key r context)
    (creatingAt_fits P D H T ht key r context hr) i
  have HI : Fin.castLE (creatingAt_le P D H T ht key r context hr) i=(⟨r,hr⟩ : Fin (arity (commands P D key))) :=
    Fin.ext rfl
  rw [HI] at HE
  exact HE

end LeanCanny.Algebra.IntegralMixedFramedPhysicalRowTransport
