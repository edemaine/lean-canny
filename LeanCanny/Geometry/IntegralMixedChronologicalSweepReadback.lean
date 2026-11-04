/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalCutRaw
public import LeanCanny.Connectivity.IntegralMixedSelectedPhysicalFiber
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateEndpoint
/-! # Physical points of the literal chronological ordinary sweep -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalSweepReadback
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedChronologicalSweepFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def rule (x : State P S B m ι) (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen) :=
  (data d hk g j hg hj).rule (commonDenominator x) (commonDenominator_ne_zero x)

theorem offset (x : State P S B m ι) (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen) :
    (rule x d hk g j hg hj).critical.offset.val=d.labels.length+1 :=pointData_offset d hk g j hg hj

theorem constraint (x : State P S B m ι) (hm : m≤S)
    (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (y : Fin (n+1)→ℝ) (i : Fin (n+1)) :
    (((IntegralMixedHistory.data x hm (rule x d hk g j hg hj).critical).scales i : ℝ)*y i=
      heightValue x (rule x d hk g j hg hj) φ t i) ↔
    y i=(d.frame.heights i).evaluate values+if i=next d hk then t else 0 :=by
  have HP:=(prefix_frozen d hk).permutation
  have HC : (rule x d hk g j hg hj).critical=(pointData d hk g j hg hj).rule:=rfl
  have HH : (rule x d hk g j hg hj).height=next d hk:=rfl
  have HS : (rule x d hk g j hg hj).slope=commonDenominator x:=rfl
  have Hscale : (rule x d hk g j hg hj).critical.scales i=1:=by
    rw [HC,pointData_rule]
    change (frame d hk).scales (FrozenCoordinateOrdering.permutation (frame d hk).frozen i)=1
    rfl
  have Hheight : (rule x d hk g j hg hj).critical.heights i=d.frame.heights i:=by
    rw [HC,pointData_rule]
    change (frame d hk).heights (FrozenCoordinateOrdering.permutation (frame d hk).frozen i)=d.frame.heights i
    rw [HP]
    rfl
  change ((commonDenominator x*(rule x d hk g j hg hj).critical.scales i:ℤ):ℝ)*y i=_ ↔ _
  unfold heightValue
  rw [Hscale,Hheight,HH,HS,expression_recover x φ values H]
  simp only [mul_one]
  have HE : (if i=next d hk then (commonDenominator x:ℝ)*t else 0)=
      (commonDenominator x:ℝ)*(if i=next d hk then t else 0):=by split_ifs <;> simp
  rw [HE,←mul_add]
  exact ⟨mul_left_cancel₀ (Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)),congrArg ((commonDenominator x:ℝ)*·)⟩

theorem frozen (x : State P S B m ι) (hm : m≤S)
    (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (y : Fin (n+1)→ℝ)
    (hf : ∀i : Fin d.labels.length,y ⟨i.val,i.isLt.trans_le d.length_le⟩=values (d.reference i))
    (ht : y (next d hk)=t) :
    IntegralMixedSelectedCoordinateEndpoint.Frozen x hm (rule x d hk g j hg hj) φ t y :=by
  intro i hi
  rw [constraint x hm d hk g j hg hj φ values H t y i]
  rw [offset] at hi
  by_cases HE : i=next d hk
  · subst i
    rw [ite_eq_left rfl]
    have Hfree:=d.free_normal (next d hk) (next_free d hk)
    rw [Hfree.2]
    simpa only [AffineExpr.evaluate,Int.cast_zero,zero_add] using ht
  · rw [ite_eq_right HE,add_zero]
    have HI : i.val<d.labels.length:=by
      have HV : i.val≠d.labels.length:=fun h=>HE (Fin.ext h)
      omega
    have HEi : (⟨i.val,HI.trans_le d.length_le⟩ : Fin (n+1))=i:=Fin.ext rfl
    have HH:=d.height ⟨i.val,HI⟩
    rw [HEi] at HH
    rw [HH]
    change y i=(if h : (d.reference ⟨i.val,HI⟩).val<m then values ⟨(d.reference ⟨i.val,HI⟩).val,h⟩ else 0)
    rw [dite_eq_left (d.reference ⟨i.val,HI⟩).isLt]
    simpa only [HEi] using hf ⟨i.val,HI⟩

theorem physical (x : State P S B m ι) (hm : m≤S)
    (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (y : Fin (n+1)→ℝ)
    (hz : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y=0)
    (hf : ∀i : Fin d.labels.length,y ⟨i.val,i.isLt.trans_le d.length_le⟩=values (d.reference i))
    (ht : y (next d hk)=t)
    (hgrad : ∀i : Fin (n+1),d.labels.length+1 ≤ i.val→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) y=0) :
    y∈IntegralMixedSelectedPhysicalFiber.physical x hm (rule x d hk g j hg hj) φ t :=by
  refine ⟨?_,?_⟩
  · intro i hi
    rw [constraint x hm d hk g j hg hj φ values H t y i]
    rw [offset] at hi
    by_cases HE : i=next d hk
    · subst i
      rw [ite_eq_left rfl]
      have Hfree:=d.free_normal (next d hk) (next_free d hk)
      rw [Hfree.2]
      simpa only [AffineExpr.evaluate,Int.cast_zero,zero_add] using ht
    · rw [ite_eq_right HE,add_zero]
      have HI : i.val<d.labels.length:=by
        have HV : i.val≠d.labels.length:=fun h=>HE (Fin.ext h)
        omega
      have HP:=(d.slice_iff P values y).mpr ⟨hz,hf⟩
      have HL:=HP.2 i ((d.frozen_mem i).mpr HI)
      simpa only [d.atomic.scale i,Int.cast_one,one_mul] using HL
  · intro k
    unfold IntegralMixedSweepRows.integerRow
    split_ifs with HE
    · exact hz
    · apply hgrad
      · have HV:=offset x d hk g j hg hj
        change d.labels.length+1≤(rule x d hk g j hg hj).critical.offset.val+k.val
        omega
      · intro HG
        apply HE
        apply Fin.ext
        have Hoffset:=offset x d hk g j hg hj
        have HGfree:=(free_iff d hk g).mp hg
        have HP:=(prefix_frozen d hk).permutation
        have HO : (objective (rule x d hk g j hg hj)).val=g.val-(d.labels.length+1):=by
          unfold objective rule IntegralMixedCutRecordConstructor.Data.rule
          change (((FrozenCoordinateOrdering.permutation (frame d hk).frozen).symm g).val-(frame d hk).frozen.card)%
            (n-(frame d hk).frozen.card+1)=_
          rw [HP,frozen_card]
          simp only [Equiv.refl_symm,Equiv.refl_apply]
          exact Nat.mod_eq_of_lt (by have :=g.isLt;omega)
        rw [HO]
        have HH:=congrArg Fin.val HG
        change (rule x d hk g j hg hj).critical.offset.val+k.val=g.val at HH
        omega


theorem raw_frozen (x : State P S B m ι) (hm : m≤S) (b : ℕ) (hb : m=b)
    (w : List Bool) (g j : ℕ) (HG : IntegralMixedChronologicalCutCode.Good n b w g j)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (y : Fin (n+1)→ℝ)
    (hf : ∀i (hi : i<WordListRecords.count w), y ⟨i,hi.trans_le HG.1.1⟩=
      values ⟨m-1-Nat.fromBitsLE (WordList.get w i),by have HJ:=HG.1.2 i hi;omega⟩)
    (ht : y ⟨WordListRecords.count w,by have HJ:=HG.2.1;have HL:=HG.2.2.1;omega⟩=t) :
    IntegralMixedSelectedCoordinateEndpoint.Frozen x hm
      ((IntegralMixedChronologicalCutCode.rawData n b w g j HG).rule
        (commonDenominator x) (commonDenominator_ne_zero x)) φ t y :=by
  subst b
  let d:=IntegralMixedChronologicalFrameCode.descriptor n m w HG.1
  apply frozen x hm d (IntegralMixedChronologicalCutCode.raw_fit n m w g j HG)
    ⟨g,HG.2.2.1⟩ ⟨j,HG.2.2.2.2⟩ (IntegralMixedChronologicalCutCode.raw_free_g n m w g j HG)
    (IntegralMixedChronologicalCutCode.raw_free_j n m w g j HG) φ values H t y
  · intro i
    have HI : i.val<WordListRecords.count w:=by
      simpa only [d,IntegralMixedChronologicalFrameCode.descriptor_length] using i.isLt
    convert hf i.val HI using 1
    apply congrArg values
    apply Fin.ext
    have HL:=(IntegralMixedChronologicalFrameCode.labels_lookup d i.val i.isLt).symm.trans
      (IntegralMixedChronologicalFrameCode.descriptor_lookup n m w HG.1 i.val HI)
    exact congrArg (fun j : ℕ=>m-1-j) HL
  · simpa only [next,d,IntegralMixedChronologicalFrameCode.descriptor_length] using ht

theorem raw_physical (x : State P S B m ι) (hm : m≤S) (b : ℕ) (hb : m=b)
    (w : List Bool) (g j : ℕ) (HG : IntegralMixedChronologicalCutCode.Good n b w g j)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (y : Fin (n+1)→ℝ)
    (hz : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y=0)
    (hf : ∀i (hi : i<WordListRecords.count w), y ⟨i,hi.trans_le HG.1.1⟩=
      values ⟨m-1-Nat.fromBitsLE (WordList.get w i),by have HJ:=HG.1.2 i hi;omega⟩)
    (ht : y ⟨WordListRecords.count w,by have HJ:=HG.2.1;have HL:=HG.2.2.1;omega⟩=t)
    (hgrad : ∀i : Fin (n+1),WordListRecords.count w+1 ≤ i.val→i.val≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) y=0) :
    y∈IntegralMixedSelectedPhysicalFiber.physical x hm
      ((IntegralMixedChronologicalCutCode.rawData n b w g j HG).rule
        (commonDenominator x) (commonDenominator_ne_zero x)) φ t :=by
  refine ⟨raw_frozen x hm b hb w g j HG φ values H t y hf ht,?_⟩
  subst b
  let d:=IntegralMixedChronologicalFrameCode.descriptor n m w HG.1
  have HP:=physical x hm d (IntegralMixedChronologicalCutCode.raw_fit n m w g j HG)
    ⟨g,HG.2.2.1⟩ ⟨j,HG.2.2.2.2⟩ (IntegralMixedChronologicalCutCode.raw_free_g n m w g j HG)
    (IntegralMixedChronologicalCutCode.raw_free_j n m w g j HG) φ values H t y hz
  apply (HP _ _ _).2
  · intro i
    have HI : i.val<WordListRecords.count w:=by
      simpa only [d,IntegralMixedChronologicalFrameCode.descriptor_length] using i.isLt
    convert hf i.val HI using 1
    apply congrArg values
    apply Fin.ext
    have HL:=(IntegralMixedChronologicalFrameCode.labels_lookup d i.val i.isLt).symm.trans
      (IntegralMixedChronologicalFrameCode.descriptor_lookup n m w HG.1 i.val HI)
    exact congrArg (fun j : ℕ=>m-1-j) HL
  · simpa only [next,d,IntegralMixedChronologicalFrameCode.descriptor_length] using ht
  · intro i hi hne
    apply hgrad i
    · simpa only [d,IntegralMixedChronologicalFrameCode.descriptor_length] using hi
    · exact fun HE=>hne (Fin.ext HE)

end LeanCanny.Geometry.IntegralMixedChronologicalSweepReadback
