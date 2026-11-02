/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCausalRecordControls
public import LeanCanny.Encoding.IntegralMixedEmptyIntegerOriginal
/-! # The causal noninteger record route has the literal total X integer leaf -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCausalRecordPlanBits
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open IntegralMixedCausalRecordBits IntegralMixedCausalPlanBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private noncomputable def integerPolynomial {n B : ℕ} (I : Instruction n B) : Polynomial ℤ :=
  match I.command with | .integer p _ _ => p | _ => Polynomial.X
private noncomputable def originalInteger {n B : ℕ} (r : Record n B) : Polynomial ℤ :=
  match r.template with | .integer p _ _ => p | _ => Polynomial.X

private theorem instantiate_integer {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (r : Record n B) : integerPolynomial (instantiate x r)=originalInteger r := by
  cases ht : r.template <;> simp only [integerPolynomial,instantiate,Template.command,ht,originalInteger]

private theorem commands_integer {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1) :
    (commands initial rs h).map integerPolynomial=rs.map originalInteger := by
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [commands_cons,List.map_cons,instantiate_integer,List.map_cons,ih]

private theorem integer_getD {n B : ℕ} (o : Option (Instruction n B)) (d : Instruction n B) :
    integerPolynomial (o.getD d)=(o.map integerPolynomial).getD (integerPolynomial d) := by cases o <;> rfl

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀ root,0<P.ambient root) (hd : ∀ root b,(S root b).degree=P.degree root)
  (hcap : ∀ root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (hroom : ∀ root,count root+2≤P.cap root+1)

theorem polynomial_X (key : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial P (plan P S hn hd hcap hroom) key=Polynomial.X := by
  have HE : IntegralMixedFramedIntegerBits.polynomial P (plan P S hn hd hcap hroom) key=
      integerPolynomial (instruction P (plan P S hn hd hcap hroom) key) := by
    unfold IntegralMixedFramedIntegerBits.polynomial integerPolynomial
    cases (instruction P (plan P S hn hd hcap hroom) key).command <;> rfl
  rw [HE]
  let initial := initial P (base P S hd hcap hroom) (pairFst key)
  let rs := originalRecords P S hn hd hcap (pairFst key)
  let b := prefixLength P key
  let h := records_bound P (originalRecords P S hn hd hcap)
    (fun root => (originalRecords_length P S hn hd hcap root) ▸ hroom root) (pairFst key)
  let fallbackI := defaultInstruction P (plan P S hn hd hcap hroom) (pairFst key)
  have H := congrArg (fun cs => cs.reverse[b]?) (commands_integer initial rs h)
  rw [← List.map_reverse,← List.map_reverse,List.getElem?_map,List.getElem?_map] at H
  change integerPolynomial ((chronological (commands initial rs h) b).getD fallbackI)=_
  rw [integer_getD]
  change (Option.map integerPolynomial (commands initial rs h).reverse[b]?).getD (integerPolynomial fallbackI)=_
  rw [H]
  change ((originalRecords P S hn hd hcap (pairFst key)).reverse[b]?.map originalInteger).getD Polynomial.X=Polynomial.X
  unfold originalRecords
  rw [List.reverse_reverse,List.getElem?_map]
  by_cases hb : b<count (pairFst key)
  · rw [List.getElem?_range hb]
    simp only [Option.map_some,Option.getD_some]
    unfold step originalInteger IntegralMixedCausalUnitRecordBits.record
    cases IntegralMixedUnitRecordCode.critical (code (pairFst key) b) <;> rfl
  · have HR : (List.range (count (pairFst key)))[b]?=none :=
      List.getElem?_eq_none (by simpa only [List.length_range] using Nat.le_of_not_gt hb)
    rw [HR]
    rfl

theorem integerOriginal (a : Access P) :
    IntegralMixedIntegerFamilyBits.Original P (IntegralMixedFramedIntegerBits.polynomial P (plan P S hn hd hcap hroom)) := by
  apply IntegralMixedFramedIntegerSyntaxBits.original P a _ IntegralMixedEmptyUnitPlan.integerWord IntegralMixedEmptyUnitPlan.integerWord_FP
  intro key
  rw [polynomial_X P S hn hd hcap hroom key]
  unfold ETR.IntegerUnivariateTermSource.polynomial IntegralMixedEmptyUnitPlan.integerWord
  rw [ETR.TermView.term_toBits]
  rfl

end LeanCanny.Encoding.IntegralMixedCausalRecordPlanBits
