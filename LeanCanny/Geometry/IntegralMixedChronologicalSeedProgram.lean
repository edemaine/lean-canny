/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapChainConstruction
public import LeanCanny.Geometry.IntegralMixedConstructedCriticalCorrelation
/-! # One chosen critical point realizes the entire canonical seed table

The initial anchor, every coordinate capture, and all padding blocks share
one physical point. The emitted bytes are exactly the depth-zero table.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalSeedProgram
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedCausalRowConstructor IntegralMixedChronologicalFrame IntegralMixedPointCompanion
open IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def descriptor (n m : ℕ) : Descriptor n m:=⟨[],by simp⟩

def zero (n m : ℕ) : Free (descriptor n m).frame.frozen:=
  ⟨⟨0,by omega⟩,by rw [(descriptor n m).frozen_mem];simp [descriptor]⟩

noncomputable def selections (n m tail : ℕ) : List (Free (descriptor n m).frame.frozen):=
  List.replicate tail (zero n m)++(descriptor n m).orderedFree++[zero n m]

theorem selections_length (n m tail : ℕ) : (selections n m tail).length=tail+n+2:=by
  simp only [selections,List.length_append,List.length_replicate,List.length_singleton,
    Descriptor.orderedFree_length,Descriptor.freeCount,descriptor,List.length_nil,Nat.sub_zero]
  omega

private theorem codes_map {n m : ℕ} (d : Descriptor n m) (g : Free d.frame.frozen)
    (js : List (Free d.frame.frozen)) :
    IntegralMixedPointCompanion.codes d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i)) g js=
      js.map (fun j=>IntegralMixedChronologicalFrameCode.code n
        (IntegralMixedChronologicalFrameCode.labels d) g.val.val j.val.val):=by
  induction js with
  | nil=>rfl
  | cons j js ih=>
    rw [IntegralMixedPointCompanion.codes,pointData_code_stable,ih]
    exact congrArg (·::_) (IntegralMixedChronologicalFrameCode.data_code d g.val j.val g.property j.property)

theorem codes_exact (n m tail : ℕ) :
    (IntegralMixedPointCompanion.codes (descriptor n m).frame.frozen (fun _=>false)
      (fun i=>.single ((descriptor n m).atom i)) (zero n m) (selections n m tail)).reverse=
      IntegralMixedRoadmapChain.seedCodes n++List.replicate tail (IntegralMixedRoadmapChain.seedCode n):=by
  have HC:=IntegralMixedChronologicalCompanionCode.codes_actual (descriptor n m) (zero n m)
  have HL : IntegralMixedChronologicalFrameCode.labels (descriptor n m)=[]:=rfl
  rw [codes_map,HL] at HC
  simp only [zero] at HC
  rw [codes_map,HL]
  simp only [selections,List.map_append,List.map_replicate,List.map_cons,List.map_nil,
    List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.reverse_replicate]
  simp only [zero]
  rw [HC]
  simp only [IntegralMixedRoadmapChain.seedCodes,IntegralMixedRoadmapChain.seedCode,List.append_assoc]

theorem selection_coordinate (n m tail :ℕ) (k :Fin (selections n m tail).length) :
    (selections n m tail)[k.val].val.val=
      if k.val<tail then 0 else if k.val<tail+n+1 then k.val-tail else 0:=by
  have HL :(descriptor n m).orderedFree.length=n+1:=by
    simp only [Descriptor.orderedFree_length,Descriptor.freeCount,descriptor,List.length_nil,Nat.sub_zero]
  change ((List.replicate tail (zero n m)++(descriptor n m).orderedFree)++[zero n m])[k.val].val.val=_
  by_cases HT :k.val<tail
  · rw [ite_eq_left HT,List.getElem_append_left (by simp only [List.length_append,List.length_replicate];omega),
      List.getElem_append_left (by rw [List.length_replicate];exact HT),List.getElem_replicate]
    rfl
  · rw [ite_eq_right HT]
    by_cases HF :k.val<tail+n+1
    · rw [ite_eq_left HF,List.getElem_append_left (by rw [List.length_append,List.length_replicate,HL];omega),
        List.getElem_append_right (by rw [List.length_replicate];omega)]
      simp only [List.length_replicate]
      have HE:=(descriptor n m).orderedFree_get ⟨k.val-tail,by rw [HL];omega⟩
      simpa only [List.get_eq_getElem,descriptor,List.length_nil,Nat.zero_add] using HE
    · rw [ite_eq_right HF,List.getElem_append_right (by rw [List.length_append,List.length_replicate,HL];omega)]
      have HK :k.val=tail+n+1:=by have H:=k.isLt;have HS:=selections_length n m tail;omega
      simp only [List.length_append,List.length_replicate,HL,HK,Nat.add_assoc,
        Nat.sub_self,List.getElem_cons_zero,zero]

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem exists_realized_seed (x : State P S B m ι) (hn :0<n) (charge :ℕ)
    (hdegree :P.degree=BoundedZeroSource.powerDegree charge)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (old :Fin m→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=old i)
    (p :Fin (n+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg :∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) p=0)
    (tail :ℕ) (room :m+(selections n m tail).length≤S+1) :
    Nonempty (Realized x (descriptor n m).frame.frozen (fun _=>false)
      (fun i=>.single ((descriptor n m).atom i)) (zero n m) z φ old p (selections n m tail) room) ∧
    Decoded x (descriptor n m).frame.frozen (fun _=>false)
      (fun i=>.single ((descriptor n m).atom i)) (zero n m) hn hcap (selections n m tail) room:=by
  apply IntegralMixedPointCompanion.exists_realized x _ _ _ _ hn charge hdegree hcap
    (descriptor n m).prefix_frozen z hz φ hφ old H p
  · apply ((descriptor n m).slice_iff P old p).mpr
    exact ⟨hp,fun i=>Fin.elim0 i⟩
  · intro i _ hi
    apply hg i
    intro he
    exact hi (Fin.ext he)

end LeanCanny.Geometry.IntegralMixedChronologicalSeedProgram
