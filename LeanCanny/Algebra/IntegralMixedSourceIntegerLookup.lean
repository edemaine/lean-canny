/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
/-! # Literal chronological source lookup closes all integer original leaves -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def index (count b : ℕ) (hb : b<count) : Fin count := ⟨count-1-b,by omega⟩

theorem chronological (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (root : List Bool) (b : ℕ) (hb : b<count root) :
    IntegralMixedFramedHistoryScript.chronological (commands P Q hq S count hz hd root) b=
      some (instruction P Q hq S count hz hd root (index (count root) b hb)) := by
  unfold IntegralMixedFramedHistoryScript.chronological
  rw [List.getElem?_reverse' (j:=count root-1-b) (by rw [commands_length]; omega)]
  unfold commands
  rw [List.getElem?_ofFn]
  simp only [index]
  split_ifs with hi
  · rfl
  · omega

noncomputable def integerPolynomial {n B : ℕ} (I : Instruction n B) : Polynomial ℤ :=
  match I.command with
  | .integer p _ _=>p
  | _=>Polynomial.X

private theorem polynomial_instruction (P : Parameters) (D : Plan P) (key : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial P D key=
      integerPolynomial (IntegralMixedFramedHistoryFamilyBits.instruction P D key) := by
  unfold IntegralMixedFramedIntegerBits.polynomial integerPolynomial
  cases (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;> rfl

theorem polynomial (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hdegree : ∀root,(Q root).degree=P.degree root)
    (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (hroom : ∀root,count root+2≤P.cap root+1) (key : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial P (plan P Q hdegree hcap S count hz hd hroom) key=
      (source P S count).polynomial key := by
  let D := plan P Q hdegree hcap S count hz hd hroom
  let hq := fun root=> (IntegralMixedFramedHistoryFamilyBits.initial P D root).critical_cap
  have HR : D.rules=commands P Q hq S count hz hd := rfl
  rw [polynomial_instruction]
  unfold IntegralMixedFramedHistoryFamilyBits.instruction
  rw [HR]
  by_cases HB : IntegralMixedFramedHistoryFamilyBits.prefixLength P key<count (pairFst key)
  · rw [chronological P Q hq S count hz hd _ _ HB]
    simp only [Option.getD_some,integerPolynomial,instruction,index,source,IntegerPolynomialSourceChoice.choose,
      IntegerPolynomialSourceChoice.reindex,HB,ite_true,Function.comp_apply,query]
    congr 3
    have H:=HB
    omega
  · have HN : IntegralMixedFramedHistoryScript.chronological (commands P Q hq S count hz hd (pairFst key))
        (IntegralMixedFramedHistoryFamilyBits.prefixLength P key)=none := by
      apply List.getElem?_eq_none
      rw [List.length_reverse,commands_length]
      omega
    rw [HN]
    simp only [Option.getD_none,integerPolynomial,IntegralMixedFramedHistoryFamilyBits.defaultInstruction,IntegralMixedFullHistoryScript.defaultCommand,
      source,IntegerPolynomialSourceChoice.choose,HB,ite_false,IntegerPolynomialZeroRootSource.source]

theorem original (P : Parameters) (a : Access P) (Q : ∀root,SpatialSource (P.ambient root))
    (hdegree : ∀root,(Q root).degree=P.degree root)
    (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (hS : IntegerPolynomialRootQueriesBits.Access S)
    (count : List Bool → ℕ) (hc : UnaryFn count)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (hroom : ∀root,count root+2≤P.cap root+1) :
    IntegralMixedIntegerFamilyBits.Original P
      (IntegralMixedFramedIntegerBits.polynomial P (plan P Q hdegree hcap S count hz hd hroom)) :=
  IntegralMixedIntegerFamilyBits.original_of_source P a _ (source P S count) (native_access P a S hS hc)
    id id_mem_FP (polynomial P Q hdegree hcap S count hz hd hroom)

end LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
