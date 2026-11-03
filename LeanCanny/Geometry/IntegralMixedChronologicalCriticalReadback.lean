/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameDecode
public import LeanCanny.Geometry.IntegralMixedFrozenFramePointReadback
/-! # A chronological point command reads its literal numerical frozen frame -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type}

theorem raw_selected (b :ℕ) (w :List Bool) (g j :ℕ)
    (HG :IntegralMixedChronologicalFrameCode.PointGood n b w g j) :
    (IntegralMixedChronologicalFrameCode.rawData n b w g j HG).rule.offset.val+
      (IntegralMixedChronologicalFrameCode.rawData n b w g j HG).rule.coordinate%
        (n-(IntegralMixedChronologicalFrameCode.rawData n b w g j HG).rule.offset.val+1)=j :=by
  let d:=IntegralMixedChronologicalFrameCode.descriptor n b w HG.1
  have HI:=pointRule_index d.frame ⟨g,HG.2.2.1⟩
    (by rw [d.frozen_mem,IntegralMixedChronologicalFrameCode.descriptor_length];exact Nat.not_lt.mpr HG.2.1)
    ⟨j,HG.2.2.2.2⟩ (by rw [d.frozen_mem,IntegralMixedChronologicalFrameCode.descriptor_length];exact Nat.not_lt.mpr HG.2.2.2.1)
  rw [d.prefix_frozen.permutation] at HI
  have HH:=congrArg Fin.val HI
  change _=j at HH
  simpa only [IntegralMixedChronologicalFrameCode.rawData,IntegralMixedChronologicalFrameCode.data_rule,
    ClearedCoordinateCritical.freeIndex,IntegralMixedCriticalRoot.coordinate] using HH

theorem critical_readback (x :State P S B m ι) (hm :m≤S) (d :Descriptor n m)
    (g j :Fin (n+1)) (hg :g∉d.frame.frozen) (hj :j∉d.frame.frozen)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values :Fin m→ℝ)
    (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a :Fin (n+1)→ℝ)
    (HA :IntegralMixedCriticalReadback.CriticalPoint x hm
      (IntegralMixedChronologicalFrameCode.data d g j hg hj).rule φ a) :
    (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) a=0 ∧
    (∀i :Fin d.labels.length,a ⟨i.val,lt_of_lt_of_le i.isLt d.length_le⟩=values (d.reference i)) ∧
    ∀ (i : Fin (n+1)), (d.labels.length ≤ i.val) → (i≠g) →
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) a=0 :=by
  rw [IntegralMixedChronologicalFrameCode.data_rule] at HA
  have HS :a∈slice P d.frame values:=by
    refine ⟨HA.1,?_⟩
    intro i hi
    have HI :i.val<(pointRule d.frame g hg j hj).offset.val:=by
      change i.val<d.frame.frozen.card
      rw [d.frozen_card]
      exact (d.frozen_mem i).mp hi
    have HF:=HA.2.1 i HI
    change ((commonDenominator x*d.frame.scales ((FrozenCoordinateOrdering.permutation d.frame.frozen) i):ℤ):ℝ)*a i=
      φ (expression x (d.frame.heights ((FrozenCoordinateOrdering.permutation d.frame.frozen) i))) at HF
    rw [d.prefix_frozen.permutation] at HF
    exact (constraint_iff x φ d.frame values H a i).mp HF
  refine ⟨HS.1,(d.slice_iff P values a).mp HS |>.2,?_⟩
  intro i hi hig
  have HI : (pointRule d.frame g hg j hj).offset.val ≤ i.val :=by
    change d.frame.frozen.card ≤ i.val
    rw [d.frozen_card]
    exact hi
  have HE :(data x hm (pointRule d.frame g hg j hj)).free=g:=by
    have HO:=coordinateRule_index d.frame g hg
    change ClearedCoordinateCritical.freeIndex (pointRule d.frame g hg j hj).offset.val
      (IntegralMixedCriticalRoot.fit (pointRule d.frame g hg j hj)).le
      (IntegralMixedCriticalRoot.objective (pointRule d.frame g hg j hj))=g
    rw [pointRule_objective]
    change ClearedCoordinateCritical.freeIndex (coordinateRule d.frame g hg).offset.val
      (IntegralMixedCriticalRoot.fit (coordinateRule d.frame g hg)).le
      (IntegralMixedCriticalRoot.coordinate (coordinateRule d.frame g hg))=g
    rw [HO,d.prefix_frozen.permutation]
    rfl
  exact HA.2.2 i HI (by rw [HE];exact hig)

theorem raw_readback (x :State P S B m ι) (hm :m≤S) (b :ℕ) (hb :m=b)
    (w :List Bool) (g j :ℕ) (HG :IntegralMixedChronologicalFrameCode.PointGood n b w g j)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values :Fin m→ℝ)
    (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a :Fin (n+1)→ℝ)
    (HA :IntegralMixedCriticalReadback.CriticalPoint x hm
      (IntegralMixedChronologicalFrameCode.rawData n b w g j HG).rule φ a) :
    (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) a=0 ∧
    (∀i (hi :i<WordListRecords.count w),a ⟨i,hi.trans_le HG.1.1⟩=
      values ⟨m-1-Nat.fromBitsLE (WordList.get w i),by have HH:=HG.1.2 i hi;omega⟩) ∧
    ∀ (i :Fin (n+1)), (WordListRecords.count w ≤ i.val) → i.val≠g →
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) a=0 :=by
  subst b
  let d:=IntegralMixedChronologicalFrameCode.descriptor n m w HG.1
  have HH:=critical_readback x hm d ⟨g,HG.2.2.1⟩ ⟨j,HG.2.2.2.2⟩ _ _ φ values H a HA
  refine ⟨HH.1,?_,?_⟩
  · intro i hi
    have HI :i<d.labels.length:=by rw [IntegralMixedChronologicalFrameCode.descriptor_length];exact hi
    have HL:=HH.2.1 ⟨i,HI⟩
    convert HL using 1
    congr 1
    apply Fin.ext
    change m-1-Nat.fromBitsLE (WordList.get w i)=m-1-
      ((List.ofFn (fun k :Fin (WordListRecords.count w)=>
        (⟨Nat.fromBitsLE (WordList.get w k.val),HG.1.2 k.val k.isLt⟩ :Fin m)))[i]'(by
          rw [List.length_ofFn];exact hi)).val
    rw [List.getElem_ofFn]
  · intro i hi hig
    exact HH.2.2 i (by rw [IntegralMixedChronologicalFrameCode.descriptor_length];exact hi)
      (fun H=>hig (congrArg Fin.val H))

end LeanCanny.Geometry.IntegralMixedChronologicalFrame
