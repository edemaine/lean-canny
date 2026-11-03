/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSourceIntegerLookup
public import LeanCanny.Algebra.IntegralMixedCanonicalUnitRules
/-! # Every source in an integer prelude is its literal fixed initial source

Padded births retain the same source and integer X. The total fallback uses
zero affine rows, unit scales and unit slope at every saved context.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
  (hdegree : ∀root,(Q root).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
  (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,count root+2≤P.cap root+1)

noncomputable def selectedInstruction (key : List Bool) : Instruction (P.ambient (pairFst key)) (P.width (pairFst key)) :=
  let D:=plan P Q hdegree hcap S count hz hd hroom
  if hb : IntegralMixedFramedHistoryFamilyBits.prefixLength P key<count (pairFst key) then
    instruction P Q (fun root=>(IntegralMixedFramedHistoryFamilyBits.initial P D root).critical_cap) S count hz hd
      (pairFst key) (index (count (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) hb)
  else IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key)

theorem instruction_selected (key : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.instruction P (plan P Q hdegree hcap S count hz hd hroom) key=
      selectedInstruction P Q hdegree hcap S count hz hd hroom key := by
  let D:=plan P Q hdegree hcap S count hz hd hroom
  let hq:=fun root=>(IntegralMixedFramedHistoryFamilyBits.initial P D root).critical_cap
  have HR : D.rules=commands P Q hq S count hz hd := rfl
  unfold IntegralMixedFramedHistoryFamilyBits.instruction
  rw [HR]
  dsimp only [selectedInstruction]
  by_cases HB : IntegralMixedFramedHistoryFamilyBits.prefixLength P key<count (pairFst key)
  · rw [chronological P Q hq S count hz hd _ _ HB,dite_eq_left HB]
    rfl
  · have HN : IntegralMixedFramedHistoryScript.chronological (commands P Q hq S count hz hd (pairFst key))
        (IntegralMixedFramedHistoryFamilyBits.prefixLength P key)=none := by
      apply List.getElem?_eq_none
      rw [List.length_reverse,commands_length]
      omega
    rw [HN,dite_eq_right HB]
    rfl

theorem instruction_source (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P Q hdegree hcap S count hz hd hroom) key).source=Q (pairFst key) := by
  rw [instruction_selected]
  dsimp only [selectedInstruction]
  split_ifs <;> rfl

theorem instruction_integer (key : List Bool) :
    ∃(p : Polynomial ℤ) (hp : p≠0) (hbound : p.natDegree≤2^P.width (pairFst key)),
      (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P Q hdegree hcap S count hz hd hroom) key).command=
        IntegralMixedFullHistoryScript.Command.integer p hp hbound := by
  rw [instruction_selected]
  dsimp only [selectedInstruction]
  by_cases HB : IntegralMixedFramedHistoryFamilyBits.prefixLength P key<count (pairFst key)
  · rw [dite_eq_left HB]
    exact ⟨_,_,_,rfl⟩
  · rw [dite_eq_right HB]
    exact ⟨_,_,_,rfl⟩

noncomputable def data (hn : ∀root,0<P.ambient root)
    (hSW : ∀root,(P.degree root).size≤P.sourceWidth root) :
    IntegralMixedFramedHistoryFamilyBits.Data P (plan P Q hdegree hcap S count hz hd hroom) where
  degree_eq key := by rw [instruction_source,hdegree]
  sourceWidth key := by rw [instruction_source,hdegree]; exact hSW _
  fallback key := IntegralMixedCanonicalUnitRuleBits.selection
    (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P Q hdegree hcap S count hz hd hroom) key).source
    (hn (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) []

end LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
