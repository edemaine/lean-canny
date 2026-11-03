/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalMidpointRaw
public import LeanCanny.Geometry.IntegralMixedPrefixPointReadback
/-! # Literal scale-two midpoint records recover their numerical frame -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalMidpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem raw_readback (x : State P S B m ι) (hm : m≤S) (b : ℕ) (hb : m=b)
    (w : List Bool) (A B g j : ℕ) (HG : IntegralMixedChronologicalMidpointCode.Good n b w A B g j)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : Fin (n+1)→ℝ)
    (HA : IntegralMixedCriticalReadback.CriticalPoint x hm
      (IntegralMixedChronologicalMidpointCode.rawData n b w A B g j HG).rule φ a) :
    (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) a=0 ∧
    (∀i (hi : i<WordListRecords.count w),a ⟨i,hi.trans_le HG.1.1⟩=
      values ⟨m-1-Nat.fromBitsLE (WordList.get w i),by have HH:=HG.1.2 i hi;omega⟩) ∧
    a ⟨WordListRecords.count w,by have H1:=HG.2.2.2.1;have H2:=HG.2.2.2.2.1;omega⟩=
      (values ⟨m-1-A,by have HH:=HG.2.1;omega⟩+values ⟨m-1-B,by have HH:=HG.2.2.1;omega⟩)/2 ∧
    ∀ (i : Fin (n+1)), Nat.le (WordListRecords.count w+1) (Fin.val i) → Ne (Fin.val i) g →
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) a=0 :=by
  subst b
  let d:=IntegralMixedChronologicalFrameCode.descriptor n m w HG.1
  let hk:=IntegralMixedChronologicalMidpointCode.raw_fit n m w A B g j HG
  let F:=IntegralMixedChronologicalMidpointCode.rawFrame n m w A B g j HG
  have HP : PrefixFrozen F:=prefix_frozen d hk ⟨A,HG.2.1⟩ ⟨B,HG.2.2.1⟩
  rw [IntegralMixedChronologicalMidpointCode.rawData_rule] at HA
  have HR:=HP.point_readback x hm φ F ⟨g,HG.2.2.2.2.1⟩ ⟨j,HG.2.2.2.2.2.2⟩
    (IntegralMixedChronologicalMidpointCode.raw_free_g n m w A B g j HG)
    (IntegralMixedChronologicalMidpointCode.raw_free_j n m w A B g j HG) values H a HA
  have HS : a∈slice P d.frame values∩{p | p (next d hk)=
      (values (reference ⟨A,HG.2.1⟩)+values (reference ⟨B,HG.2.2.1⟩))/2}:=by
    rw [←slice_eq d hk ⟨A,HG.2.1⟩ ⟨B,HG.2.2.1⟩ P values]
    exact HR.1
  refine ⟨HS.1.1,?_,?_,?_⟩
  · intro i hi
    have HI : i<d.labels.length:=by rw [IntegralMixedChronologicalFrameCode.descriptor_length];exact hi
    have HL:=((d.slice_iff P values a).mp HS.1).2 ⟨i,HI⟩
    convert HL using 1
    congr 1
    apply Fin.ext
    change m-1-Nat.fromBitsLE (WordList.get w i)=m-1-
      ((List.ofFn (fun k : Fin (WordListRecords.count w)=>
        (⟨Nat.fromBitsLE (WordList.get w k.val),HG.1.2 k.val k.isLt⟩ : Fin m)))[i]'(by
          rw [List.length_ofFn];exact hi)).val
    rw [List.getElem_ofFn]
  · simpa only [Set.mem_ofPred_eq,next,reference,d,IntegralMixedChronologicalFrameCode.descriptor_length] using HS.2
  · intro i hi hne
    apply HR.2 i
    · change i∉(frame d hk ⟨A,HG.2.1⟩ ⟨B,HG.2.2.1⟩).frozen
      rw [free_iff,IntegralMixedChronologicalFrameCode.descriptor_length]
      exact hi
    · exact fun he=>hne (congrArg Fin.val he)


theorem raw_selected (b : ℕ) (w : List Bool) (A B g j : ℕ)
    (HG : IntegralMixedChronologicalMidpointCode.Good n b w A B g j) :
    (IntegralMixedChronologicalMidpointCode.rawData n b w A B g j HG).rule.offset.val+
      (IntegralMixedChronologicalMidpointCode.rawData n b w A B g j HG).rule.coordinate%
        (n-(IntegralMixedChronologicalMidpointCode.rawData n b w A B g j HG).rule.offset.val+1)=j :=by
  let F:=IntegralMixedChronologicalMidpointCode.rawFrame n b w A B g j HG
  have HP : PrefixFrozen F:=prefix_frozen _ _ _ _
  have HI:=pointRule_index F ⟨g,HG.2.2.2.2.1⟩
    (IntegralMixedChronologicalMidpointCode.raw_free_g n b w A B g j HG)
    ⟨j,HG.2.2.2.2.2.2⟩ (IntegralMixedChronologicalMidpointCode.raw_free_j n b w A B g j HG)
  rw [HP.permutation] at HI
  have HH:=congrArg Fin.val HI
  change _=j at HH
  simpa only [IntegralMixedChronologicalMidpointCode.rawData_rule,
    ClearedCoordinateCritical.freeIndex,IntegralMixedCriticalRoot.coordinate] using HH

end LeanCanny.Geometry.IntegralMixedChronologicalMidpoint
