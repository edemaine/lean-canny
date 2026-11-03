/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixRecords
/-! # A changed reserved probe preserves the actual marked parent run

The compared runs use their own roots and their equal fixed horizon/width.
The old candidate and chronological original code prefix are literal data.
No complete word or branch ordinal is transported.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPrefixRun
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (Plan initial defaultInstruction keyAt)
open IntegralMixedFramedFamilyRunView (runAt familyRun)
open IntegralMixedAuxiliaryMarkedIntegerSource (candidate number)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)

theorem bound (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :
    number n root+8+j≤(P).cap root+1 :=by
  change number n root+8+j≤number n root+8+IntegralMixedCausalRecordPlanBits.count root+2+1
  omega

private theorem run_congr {a S B : ℕ} {Q : SpatialSource a} (x : State Q S B 0 (Fin 0))
    (cs ds : List (Instruction a B)) (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    HEq (run x cs hc) (run x ds hd) :=by cases he;rfl

theorem factor (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :
    HEq (runAt P D root (number n root+8+j) (bound hn ht ha hR0 root j hj))
      (IntegralMixedCausalPrefixCongruence.prefixRun (initial P D root)
        (IntegralMixedMarkedPrefixRecords.records hn ht ha hR0 root)
        (IntegralMixedMarkedPrefixRecords.room hn ht ha hR0 root) (defaultInstruction P D root)
        (number n root+8+j) (by rw [IntegralMixedMarkedPrefixRecords.length];omega)) :=by
  unfold runAt IntegralMixedCausalPrefixCongruence.prefixRun
  apply run_congr
  exact congrArg (fun cs=>paddedPast (defaultInstruction P D root) cs (number n root+8+j))
    (IntegralMixedMarkedPrefixRecords.rules hn ht ha hR0 root)

theorem runAt_heq (cL cR : List Bool) (hc : candidate cL=candidate cR)
    (hcount : IntegralMixedCausalRecordPlanBits.count cL=IntegralMixedCausalRecordPlanBits.count cR)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count cL)
    (hcode : ∀i,i<j→IntegralMixedCausalRecordPlanBits.code cL i=IntegralMixedCausalRecordPlanBits.code cR i) :
    HEq (runAt P D cL (number n cL+8+j) (bound hn ht ha hR0 cL j hj))
      (runAt P D cR (number n cR+8+j) (bound hn ht ha hR0 cR j (hj.trans_eq hcount))) :=by
  refine (factor hn ht ha hR0 cL j hj).trans
    (HEq.trans ?_ (factor hn ht ha hR0 cR j (hj.trans_eq hcount)).symm)
  unfold IntegralMixedMarkedPrefixRecords.records
  apply IntegralMixedStaticRecordPrefix.run_heq
  · exact hj
  · simpa only [IntegralMixedMarkedPrefixRecords.length] using IntegralMixedMarkedPrefixRecords.room hn ht ha hR0 cL
  · simpa only [IntegralMixedMarkedPrefixRecords.length] using IntegralMixedMarkedPrefixRecords.room hn ht ha hR0 cR
  · exact IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 cL cR hc
  · exact IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 cL cR hc
  · exact congrArg (·+1) (IntegralMixedMarkedPrefixParameters.cap hn ht ha hR0 cL cR hc hcount)
  · exact congrArg (·+8) (IntegralMixedMarkedPreludeCongruence.number_eq cL cR hc)
  · exact hcount
  · exact IntegralMixedMarkedPrefixRecords.source_heq (n:=n) (t:=t) (R0:=R0) cL cR hc
  · exact IntegralMixedMarkedPrefixRecords.initial_heq hn ht ha hR0 cL cR hc hcount
  · exact IntegralMixedMarkedPreludeCongruence.polynomial hn ht ha R0 cL cR hc
  · exact hcode

private theorem at_congr (A : Parameters) (E : Plan A) (r s : List Bool) (a b : ℕ)
    (hr : r=s) (hb : a=b) (ha : a≤A.cap r+1) (hc : b≤A.cap s+1) :
    HEq (runAt A E r a ha) (runAt A E s b hc) :=by cases hr;cases hb;rfl

theorem familyRun_at (A : Parameters) (E : Plan A) (root aux : List Bool) (b : ℕ) (hb : b≤A.cap root+1) :
    HEq (familyRun A E (keyAt root b aux)) (runAt A E root b hb) :=by
  let k:=keyAt root b aux
  have H0 :HEq (familyRun A E k)
      (runAt A E (pairFst k) (IntegralMixedFramedHistoryFamilyBits.prefixLength A k) (min_le_right _ _)) :=HEq.rfl
  exact H0.trans (at_congr A E _ root _ b (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix A root b aux hb) _ hb)

theorem familyRun_heq (cL cR : List Bool) (hc : candidate cL=candidate cR)
    (hcount : IntegralMixedCausalRecordPlanBits.count cL=IntegralMixedCausalRecordPlanBits.count cR)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count cL) (auxL auxR : List Bool)
    (hcode : ∀i,i<j→IntegralMixedCausalRecordPlanBits.code cL i=IntegralMixedCausalRecordPlanBits.code cR i) :
    HEq (familyRun P D (keyAt cL (number n cL+8+j) auxL))
      (familyRun P D (keyAt cR (number n cR+8+j) auxR)) :=
  (familyRun_at P D cL auxL _ (bound hn ht ha hR0 cL j hj)).trans
    ((runAt_heq hn ht ha hR0 cL cR hc hcount j hj hcode).trans
      (familyRun_at P D cR auxR _ (bound hn ht ha hR0 cR j (hj.trans_eq hcount))).symm)

def reservedRoot (old : List Bool) (codes : List (List Bool)) (probe aux : List Bool) :=
  pair old (pair (WordList.encode (codes++[probe])) aux)

theorem reserved_count (old : List Bool) (codes : List (List Bool)) (probe aux : List Bool) :
    IntegralMixedCausalRecordPlanBits.count (reservedRoot old codes probe aux)=codes.length+1 :=by
  simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
    reservedRoot,pairSnd_pair,pairFst_pair,WordListRecords.count_encode,List.length_append,List.length_singleton]

theorem reserved_prefix (old : List Bool) (codes : List (List Bool)) (p q a b : List Bool)
    (i : ℕ) (hi : i<codes.length) :
    IntegralMixedCausalRecordPlanBits.code (reservedRoot old codes p a) i=
      IntegralMixedCausalRecordPlanBits.code (reservedRoot old codes q b) i :=by
  simp only [IntegralMixedCausalRecordPlanBits.code,IntegralMixedCausalRecordPlanBits.records,
    reservedRoot,pairSnd_pair,pairFst_pair,WordList.get_encode,List.getElem?_append_left hi]

theorem reserved_run (old : List Bool) (codes : List (List Bool)) (p q a b auxL auxR : List Bool) :
    HEq (familyRun P D (keyAt (reservedRoot old codes p a)
      (number n (reservedRoot old codes p a)+8+codes.length) auxL))
      (familyRun P D (keyAt (reservedRoot old codes q b)
        (number n (reservedRoot old codes q b)+8+codes.length) auxR)) :=by
  apply familyRun_heq hn ht ha hR0 _ _
  · simp only [candidate,reservedRoot,pairFst_pair]
  · rw [reserved_count,reserved_count]
  · rw [reserved_count]
    omega
  · exact fun i hi=>reserved_prefix old codes p q a b i hi
end LeanCanny.Encoding.IntegralMixedMarkedPrefixRun
