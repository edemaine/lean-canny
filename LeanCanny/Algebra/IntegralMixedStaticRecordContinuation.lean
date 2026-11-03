/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalUnitContinuation
public import LeanCanny.Algebra.IntegralMixedStaticRecordLookup
/-! # Literal raw code slices are the actual causal continuation records -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedStaticRecordContinuation
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedCausalRecordBits
open IntegralMixedFramedHistoryScript (Instruction paddedPast paddedPast_length)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n B :ℕ} (Q :SpatialSource n) (hn :0<n)
  (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
  (N C :ℕ) (p :ℕ→Polynomial ℤ) (hp :∀i,p i≠0) (hd :∀i,(p i).natDegree≤2^B) (w :ℕ→List Bool)
local notation "rs"=>IntegralMixedStaticRecordPrefix.records Q hn hcap N C p hp hd w

theorem prefix_records (j :ℕ) (codes :List (List Bool)) (hj :j+codes.length≤C)
    (hw :∀i,i<codes.length→w (j+i)=(codes.reverse[i]?).getD []) :
    ((rs).reverse.take (N+j+codes.length)).reverse=
      IntegralMixedCausalUnitContinuation.records Q hn hcap (N+j) codes++((rs).reverse.take (N+j)).reverse :=by
  apply List.reverse_injective
  simp only [List.reverse_reverse,List.reverse_append]
  rw [List.take_add]
  apply congrArg (List.append ((rs).reverse.take (N+j)))
  apply List.ext_getElem?
  intro i
  by_cases HI :i<codes.length
  · rw [List.getElem?_take,ite_eq_left HI,List.getElem?_drop,
      IntegralMixedCausalUnitContinuation.records_reverse_get Q hn hcap (N+j) codes i HI]
    have HR:=IntegralMixedStaticRecordLookup.original_record_option Q hn hcap N C p hp hd w (j+i) (by omega)
    rw [hw i HI] at HR
    simpa only [Nat.add_assoc] using HR
  · rw [List.getElem?_take,ite_eq_right HI]
    exact (List.getElem?_eq_none_iff.mpr (by
      rw [List.length_reverse,IntegralMixedCausalUnitContinuation.records_length]
      omega)).symm

noncomputable def prefixRecords (j :ℕ):=((rs).reverse.take (N+j)).reverse

theorem prefixRecords_length (j :ℕ) (hj :j≤C) :(prefixRecords Q hn hcap N C p hp hd w j).length=N+j:=by
  simp only [prefixRecords,List.length_reverse,List.length_take,IntegralMixedStaticRecordPrefix.records_length]
  exact min_eq_left (by omega)

variable {S :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]
  (initial :State P S B 0 ι)
  (hr :(IntegralMixedStaticRecordPrefix.records Q hn hcap N C p hp hd w).length≤S+1)
local notation "hQ"=>IntegralMixedStaticRecordPrefix.cap Q hcap
local notation "oldRs" j=>prefixRecords Q hn hcap N C p hp hd w j

noncomputable def prefixStart (j :ℕ) (hj :j≤C):=
  IntegralMixedCausalUnitContinuation.start initial Q hcap (oldRs j)
    (by rw [prefixRecords_length Q hn hcap N C p hp hd w j hj];rw [IntegralMixedStaticRecordPrefix.records_length] at hr;omega)

theorem start_actual (fallback :Instruction n B) (j :ℕ) (hj :j≤C) :
    HEq (prefixStart Q hn hcap N C p hp hd w initial hr j hj)
      (reframe (IntegralMixedCausalPrefixCongruence.prefixRun initial rs hr fallback (N+j)
        (by rw [IntegralMixedStaticRecordPrefix.records_length];omega)) Q hQ):=by
  have HE:=IntegralMixedCausalPrefixCongruence.commands_prefix initial rs hr fallback (N+j)
    (by rw [IntegralMixedStaticRecordPrefix.records_length];omega)
  exact IntegralMixedCausalUnitContinuation.reframe_run_congr initial _ _ _ _ HE.symm Q hQ

theorem prefix_commands (fallback :Instruction n B) (j :ℕ) (codes :List (List Bool))
    (hj :j+codes.length≤C) (hw :∀i,i<codes.length→w (j+i)=(codes.reverse[i]?).getD [])
    (cs :List (IntegralMixedFullHistoryScript.Command Q B))
    (hc :(IntegralMixedCausalPlanBits.commands initial (oldRs j) (by
      rw [prefixRecords_length Q hn hcap N C p hp hd w j (by omega)]
      rw [IntegralMixedStaticRecordPrefix.records_length] at hr;omega)).length+cs.length≤S+1)
    (HD :LeanCanny.Geometry.IntegralMixedOptionalEndpoints.Decodes
      (prefixStart Q hn hcap N C p hp hd w initial hr j (by omega)) hn hcap cs hc codes) :
    paddedPast fallback (IntegralMixedCausalPlanBits.commands initial rs hr) (N+j+codes.length)=
      cs.map (IntegralMixedFramedFixedContinuation.wrap Q hQ)++
        IntegralMixedCausalPlanBits.commands initial (oldRs j) (by
          rw [prefixRecords_length Q hn hcap N C p hp hd w j (by omega)]
          rw [IntegralMixedStaticRecordPrefix.records_length] at hr;omega) :=by
  have HO :(oldRs j).length≤S+1:=by
    rw [prefixRecords_length Q hn hcap N C p hp hd w j (by omega)]
    rw [IntegralMixedStaticRecordPrefix.records_length] at hr
    omega
  let old:=IntegralMixedCausalPlanBits.commands initial (oldRs j) HO
  have HM :(old).length=N+j:=by
    rw [IntegralMixedCausalPlanBits.commands_length,prefixRecords_length Q hn hcap N C p hp hd w j (by omega)]
  let newRs:=IntegralMixedCausalUnitContinuation.records Q hn hcap (old).length codes++oldRs j
  have Hnew :newRs.length≤S+1:=by
    have HL:=IntegralMixedCausalUnitContinuation.decode_length
      (prefixStart Q hn hcap N C p hp hd w initial hr j (by omega)) hn hcap cs hc codes HD
    simp only [newRs,List.length_append,IntegralMixedCausalUnitContinuation.records_length]
    have HLold:=IntegralMixedCausalPlanBits.commands_length initial (oldRs j) HO
    omega
  have HE :((rs).reverse.take (N+j+codes.length)).reverse=newRs:=by
    rw [prefix_records Q hn hcap N C p hp hd w j codes hj hw]
    dsimp only [newRs,prefixRecords]
    rw [HM]
  have HP:=IntegralMixedCausalPrefixCongruence.commands_prefix initial rs hr fallback (N+j+codes.length)
    (by rw [IntegralMixedStaticRecordPrefix.records_length];omega)
  have HT:=IntegralMixedCausalUnitContinuation.commands_congr initial _ newRs
    (by simp only [List.length_reverse,List.length_take,List.length_reverse];exact (min_le_right _ _).trans hr) Hnew HE
  exact HP.trans (HT.trans (IntegralMixedCausalUnitContinuation.compile_commands initial Q hn hcap
    (oldRs j) HO cs hc codes HD))

theorem prefix_run (fallback :Instruction n B) (j :ℕ) (codes :List (List Bool))
    (hj :j+codes.length≤C) (hw :∀i,i<codes.length→w (j+i)=(codes.reverse[i]?).getD [])
    (cs :List (IntegralMixedFullHistoryScript.Command Q B))
    (hc :(IntegralMixedCausalPlanBits.commands initial (oldRs j) (by
      rw [prefixRecords_length Q hn hcap N C p hp hd w j (by omega)]
      rw [IntegralMixedStaticRecordPrefix.records_length] at hr;omega)).length+cs.length≤S+1)
    (HD :LeanCanny.Geometry.IntegralMixedOptionalEndpoints.Decodes
      (prefixStart Q hn hcap N C p hp hd w initial hr j (by omega)) hn hcap cs hc codes) :
    HEq (reframe (IntegralMixedCausalPrefixCongruence.prefixRun initial rs hr fallback (N+j+codes.length)
      (by rw [IntegralMixedStaticRecordPrefix.records_length];omega)) Q hQ)
      (IntegralMixedFullHistoryScript.continueRun
        (prefixStart Q hn hcap N C p hp hd w initial hr j (by omega)) cs hc):=by
  have HE:=prefix_commands Q hn hcap N C p hp hd w initial hr fallback j codes hj hw cs hc HD
  exact (IntegralMixedCausalUnitContinuation.reframe_run_congr initial _ _ _ _ HE Q hQ).trans
    (IntegralMixedFramedFixedContinuation.run_append initial Q hQ _ _ cs hc)

theorem prefix_index (fallback :Instruction n B) (j :ℕ) (codes :List (List Bool))
    (hj :j+codes.length≤C) (hw :∀i,i<codes.length→w (j+i)=(codes.reverse[i]?).getD [])
    (cs :List (IntegralMixedFullHistoryScript.Command Q B))
    (hc :(IntegralMixedCausalPlanBits.commands initial (oldRs j) (by
      rw [prefixRecords_length Q hn hcap N C p hp hd w j (by omega)]
      rw [IntegralMixedStaticRecordPrefix.records_length] at hr;omega)).length+cs.length≤S+1)
    (HD :LeanCanny.Geometry.IntegralMixedOptionalEndpoints.Decodes
      (prefixStart Q hn hcap N C p hp hd w initial hr j (by omega)) hn hcap cs hc codes) :
    IntegralMixedFramedHistoryScript.Index ι
      (paddedPast fallback (IntegralMixedCausalPlanBits.commands initial rs hr) (N+j+codes.length))=
      IntegralMixedFullHistoryScript.Index (IntegralMixedFramedHistoryScript.Index ι
        (IntegralMixedCausalPlanBits.commands initial (oldRs j) (by
          rw [prefixRecords_length Q hn hcap N C p hp hd w j (by omega)]
          rw [IntegralMixedStaticRecordPrefix.records_length] at hr;omega))) cs:=
  (congrArg (IntegralMixedFramedHistoryScript.Index ι)
    (prefix_commands Q hn hcap N C p hp hd w initial hr fallback j codes hj hw cs hc HD)).trans
    (IntegralMixedFramedFixedContinuation.index_append Q hQ cs _)

end LeanCanny.Algebra.IntegralMixedStaticRecordContinuation
