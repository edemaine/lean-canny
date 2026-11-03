/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSourceIntegerCausalPrelude
public import LeanCanny.Algebra.IntegralMixedSourceIntegerLookup
public import LeanCanny.Algebra.IntegralMixedCausalPlanHeaders
/-! # Original integer leaves survive a causal continuation

Later templates are serialized after the literal integer prelude. Integer
coefficient queries still read the original source or the literal X fallback;
current-bank slopes never become original integer coefficient data.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedCausalRecordBits
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def templatePolynomial {n B : ℕ} {Q : SpatialSource n} : Template Q B → Polynomial ℤ
  | .integer p _ _=>p
  | .critical _=>Polynomial.X
  | .cut _=>Polynomial.X

theorem instantiate_polynomial {n horizon B m : ℕ} {Q : SpatialSource n} {ι : Type}
    (x : State Q horizon B m ι) (r : Record n B) :
    integerPolynomial (instantiate x r)=templatePolynomial r.template := by
  cases r with
  | mk source hc template => cases template <;> rfl

theorem commands_polynomials {n horizon B : ℕ} {Q : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State Q horizon B 0 ι) (rs : List (Record n B)) (hr : rs.length≤horizon+1) :
    (IntegralMixedCausalPlanBits.commands initial rs hr).map integerPolynomial=
      rs.map (fun r=>templatePolynomial r.template) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [IntegralMixedCausalPlanBits.commands_cons,List.map_cons,List.map_cons,instantiate_polynomial,ih]

private theorem option_polynomial {n B : ℕ} (o : Option (Instruction n B)) (d : Instruction n B)
    (hd : integerPolynomial d=Polynomial.X) :
    integerPolynomial (o.getD d)=(o.map integerPolynomial).getD Polynomial.X := by
  cases o <;> simp only [Option.getD_none,Option.getD_some,Option.map_none,Option.map_some,hd]

theorem causal_polynomial (P : Parameters) (base : Plan P)
    (rs : ∀root,List (Record (P.ambient root) (P.width root)))
    (hroom : ∀root,(rs root).length+2≤P.cap root+1) (key : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial P (IntegralMixedCausalPlanBits.plan P base rs hroom) key=
      (((rs (pairFst key)).reverse.map (fun r=>templatePolynomial r.template))[IntegralMixedFramedHistoryFamilyBits.prefixLength P key]?).getD Polynomial.X := by
  let D:=IntegralMixedCausalPlanBits.plan P base rs hroom
  have HP : IntegralMixedFramedIntegerBits.polynomial P D key=
      integerPolynomial (IntegralMixedFramedHistoryFamilyBits.instruction P D key) := by
    unfold IntegralMixedFramedIntegerBits.polynomial integerPolynomial
    cases (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;> rfl
  rw [HP]
  unfold IntegralMixedFramedHistoryFamilyBits.instruction
  rw [option_polynomial _ _ (by rfl)]
  change (((IntegralMixedCausalPlanBits.commands (IntegralMixedFramedHistoryFamilyBits.initial P base (pairFst key))
    (rs (pairFst key)) _).reverse[IntegralMixedFramedHistoryFamilyBits.prefixLength P key]?).map
      integerPolynomial).getD Polynomial.X= _
  rw [←List.getElem?_map,List.map_reverse,commands_polynomials,←List.map_reverse]

theorem polynomial_lookup (P : Parameters) (D : Plan P) (key : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial P D key=
      (((D.rules (pairFst key)).reverse.map integerPolynomial)[IntegralMixedFramedHistoryFamilyBits.prefixLength P key]?).getD Polynomial.X := by
  have HP : IntegralMixedFramedIntegerBits.polynomial P D key=
      integerPolynomial (IntegralMixedFramedHistoryFamilyBits.instruction P D key) := by
    unfold IntegralMixedFramedIntegerBits.polynomial integerPolynomial
    cases (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;> rfl
  rw [HP]
  unfold IntegralMixedFramedHistoryFamilyBits.instruction
  rw [option_polynomial _ _ (by rfl)]
  change (((D.rules (pairFst key)).reverse[IntegralMixedFramedHistoryFamilyBits.prefixLength P key]?).map
    integerPolynomial).getD Polynomial.X=_
  rw [←List.getElem?_map]

theorem records_polynomials (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (root : List Bool) :
    (commands P Q hq S count hz hd root).map integerPolynomial=
      (records P Q hq S count hz hd root).map (fun r=>templatePolynomial r.template) := by
  simp only [commands,records,List.map_ofFn]
  rfl

private theorem noninteger_lookup {n B : ℕ} (rs : List (Record n B))
    (hn : ∀r∈rs,templatePolynomial r.template=Polynomial.X) (k : ℕ) :
    ((rs.reverse.map (fun r=>templatePolynomial r.template))[k]?).getD Polynomial.X=Polynomial.X := by
  rw [List.getElem?_map]
  cases he : rs.reverse[k]? with
  | none => rfl
  | some r =>
    exact hn r (List.mem_reverse.mp (List.mem_of_getElem? he))

variable (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
  (hdegree : ∀root,(Q root).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
  (hz : ∀q,S.polynomial q≠0)
  (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (later : ∀root,List (Record (P.ambient root) (P.width root)))
  (hroom : ∀root,(later root).length+count root+2≤P.cap root+1)

include hroom in
theorem prelude_room (root : List Bool) : count root+2≤P.cap root+1 := by
  have H:=hroom root
  omega

noncomputable def extendedPlan : Plan P :=
  IntegralMixedCausalPlanBits.plan P (plan P Q hdegree hcap S count hz hd (prelude_room P count later hroom))
    (fun root=>later root++records P Q (fun root=>(IntegralMixedFramedHistoryFamilyBits.initial P
      (plan P Q hdegree hcap S count hz hd (prelude_room P count later hroom)) root).critical_cap) S count hz hd root)
    (fun root=>by rw [List.length_append,records_length]; exact hroom root)

theorem extended_length (root : List Bool) :
    ((extendedPlan P Q hdegree hcap S count hz hd later hroom).rules root).length=(later root).length+count root := by
  rw [extendedPlan,IntegralMixedCausalPlanBits.plan,IntegralMixedCausalPlanBits.commands_length,List.length_append,records_length]

theorem extended_suffix (root : List Bool) :
    ((extendedPlan P Q hdegree hcap S count hz hd later hroom).rules root).drop (later root).length=
      (plan P Q hdegree hcap S count hz hd (prelude_room P count later hroom)).rules root :=
  appended_integer_suffix P Q _ S count hz hd root _ (later root) _

theorem records_lookup (key : List Bool) :
    (((records P Q (fun root=>(IntegralMixedFramedHistoryFamilyBits.initial P
      (plan P Q hdegree hcap S count hz hd (prelude_room P count later hroom)) root).critical_cap)
      S count hz hd (pairFst key)).reverse.map (fun r=>templatePolynomial r.template))[IntegralMixedFramedHistoryFamilyBits.prefixLength P key]?).getD Polynomial.X=
      (source P S count).polynomial key := by
  rw [List.map_reverse,←records_polynomials,←List.map_reverse]
  exact (polynomial_lookup P (plan P Q hdegree hcap S count hz hd (prelude_room P count later hroom)) key).symm.trans
    (polynomial P Q hdegree hcap S count hz hd (prelude_room P count later hroom) key)

theorem extended_polynomial (hni : ∀root,∀r∈later root,templatePolynomial r.template=Polynomial.X)
    (key : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial P (extendedPlan P Q hdegree hcap S count hz hd later hroom) key=
      (source P S count).polynomial key := by
  rw [extendedPlan,causal_polynomial]
  simp only [List.reverse_append,List.map_append]
  have HL : ((records P Q (fun root=>(IntegralMixedFramedHistoryFamilyBits.initial P
      (plan P Q hdegree hcap S count hz hd (prelude_room P count later hroom)) root).critical_cap)
      S count hz hd (pairFst key)).reverse.map (fun r=>templatePolynomial r.template)).length=count (pairFst key) := by
    rw [List.length_map,List.length_reverse,records_length]
  by_cases hb : IntegralMixedFramedHistoryFamilyBits.prefixLength P key<count (pairFst key)
  · rw [List.getElem?_append_left (by rw [HL]; exact hb)]
    exact records_lookup P Q hdegree hcap S count hz hd later hroom key
  · rw [List.getElem?_append_right (by rw [HL]; omega)]
    rw [noninteger_lookup _ (hni (pairFst key))]
    simp only [source,IntegerPolynomialSourceChoice.choose,hb,ite_false,IntegerPolynomialZeroRootSource.source]

theorem extended_original (a : Access P) (hS : IntegerPolynomialRootQueriesBits.Access S) (hc : UnaryFn count)
    (hni : ∀root,∀r∈later root,templatePolynomial r.template=Polynomial.X) :
    IntegralMixedIntegerFamilyBits.Original P
      (IntegralMixedFramedIntegerBits.polynomial P (extendedPlan P Q hdegree hcap S count hz hd later hroom)) :=
  IntegralMixedIntegerFamilyBits.original_of_source P a _ (source P S count) (native_access P a S hS hc)
    id id_mem_FP (extended_polynomial P Q hdegree hcap S count hz hd later hroom hni)

end LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
