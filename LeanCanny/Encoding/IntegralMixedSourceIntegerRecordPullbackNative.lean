/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullbackControls
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackHeaders
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackSource
/-! # All native causal routines preserve the original root under caller lifting

Raw integer polynomials keep their charged source; original regular LOW,
affine syntax and scale masks are read at the projected full saved key.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullback
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ)
  (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (S root 0).degree≤2^P.width root)
  (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
  (hW : ∀root,(P.degree root).size≤P.sourceWidth root)
  (project : List Bool→List Bool) (extra : List Bool→ℕ)
local notation "D" => IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom
local notation "J" => IntegralMixedSourceIntegerRecordAppend.data P S hn hd hcap N hq T hz hT hroom hW
local notation "OR" => IntegralMixedSourceIntegerRecordAppend.originalRecords P S hn hd hcap N hq T hz hT
local notation "HT" => IntegralMixedCausalPlanBits.tables P OR
local notation "PP" => IntegralMixedFramedRootPullback.parameters P project extra
local notation "DD" => IntegralMixedFramedRootPullback.plan P D project extra
local notation "JJ" => IntegralMixedFramedRootPullback.data P D J project extra
local notation "NT" => IntegralMixedFramedRootPullback.tables HT project

theorem tables_native (a : Access P) (hN : UnaryFn N) (hp : project∈FP) : IntegralMixedHeaderTablesBits.Access NT :=
  IntegralMixedFramedRootPullback.tablesAccess HT (IntegralMixedSourceIntegerRecordAppend.tables_native P S hn hd hcap N hq T hz hT a hN) project hp

theorem tables_represent : IntegralMixedFramedHeaderBits.Represents PP DD JJ NT :=
  IntegralMixedFramedRootPullback.represents P D J HT
    (IntegralMixedSourceIntegerRecordAppend.tables_represent P S hn hd hcap N hq T hz hT hroom hW) project extra

private theorem integer_observation (p : Parameters) (script : Plan p) (key : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial p script key=
      IntegralMixedSourceIntegerPrelude.integerPolynomial (instruction p script key) := by
  unfold IntegralMixedFramedIntegerBits.polynomial IntegralMixedSourceIntegerPrelude.integerPolynomial
  cases (instruction p script key).command <;> rfl

theorem integer_polynomial (key : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial PP DD key=
      (IntegralMixedSourceIntegerPrelude.source P T N).polynomial (IntegralMixedFramedRootPullback.key project key) := by
  rw [integer_observation]
  have HI:=IntegralMixedFramedRootPullback.instruction_read
    (fun _ _ I=>IntegralMixedSourceIntegerPrelude.integerPolynomial I) _ _
    (congrArg P.ambient (IntegralMixedFramedRootPullback.key_root project key).symm)
    (congrArg P.width (IntegralMixedFramedRootPullback.key_root project key).symm)
    (IntegralMixedFramedRootPullback.instruction_heq P D project extra key)
  refine HI.trans ((integer_observation P D _).symm.trans ?_)
  exact IntegralMixedSourceIntegerPrelude.extended_polynomial P (fun root=>S root 0) (fun root=>hd root 0) hcap T N hz hT
    (IntegralMixedSourceIntegerRecordAppend.later P S hn hd hcap N)
    (fun root=>by rw [IntegralMixedSourceIntegerRecordAppend.later_length]; exact hroom root)
    (IntegralMixedSourceIntegerRecordAppend.later_noninteger P S hn hd hcap N) _

theorem integerOriginal (a : Access P) (hN : UnaryFn N) (hA : IntegerPolynomialRootQueriesBits.Access T)
    (hp : project∈FP) (he : BinaryFn extra) :
    IntegralMixedIntegerFamilyBits.Original PP (IntegralMixedFramedIntegerBits.polynomial PP DD) :=
  IntegralMixedIntegerFamilyBits.original_of_source PP (IntegralMixedFramedRootPullback.access P a project hp extra he)
    _ (IntegralMixedSourceIntegerPrelude.source P T N) (IntegralMixedSourceIntegerPrelude.native_access P a T hA hN)
    (IntegralMixedFramedRootPullback.key project) (IntegralMixedFramedRootPullback.key_FP project hp)
    (integer_polynomial P S hn hd hcap N T hz hT hroom project extra)

theorem snapshot (R : BoundedFullWriter.Readers) (s : BoundedRegularFramedOriginalBits.Snapshot P D R) :
    BoundedRegularFramedOriginalBits.Snapshot PP DD (R.comp (IntegralMixedFramedRootPullback.key project)) where
  ambient key:=by
    simpa only [BoundedFullWriter.Readers.comp,IntegralMixedFramedRootPullback.parameters,
      Function.comp_apply,IntegralMixedFramedRootPullback.key_root] using s.ambient (IntegralMixedFramedRootPullback.key project key)
  source key:=(IntegralMixedFramedRootPullback.instruction_source P D project extra key).trans (s.source _)

noncomputable def currentQControls (a : Access P) (hN : UnaryFn N) (hA : IntegerPolynomialRootQueriesBits.Access T)
    (hp : project∈FP) (he : BinaryFn extra)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (scope : ∀key,(ETR.TermView.term (R.source key)).arity≤R.dim key)
    (s : BoundedRegularFramedOriginalBits.Snapshot P D R)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) :
    IntegralMixedFramedCurrentQNativeBits.Controls PP DD JJ := by
  let aa:=IntegralMixedFramedRootPullback.access P a project hp extra he
  let RR:=R.comp (IntegralMixedFramedRootPullback.key project)
  have HH:=hR.comp (IntegralMixedFramedRootPullback.key_FP project hp)
  have SS:=snapshot P S hn hd hcap N T hz hT hroom project extra R s
  exact {
    scalar:=IntegralMixedFramedCurrentQIndexedBits.controls PP aa DD JJ
      (originalRules P S hn hd hcap N hq T hz hT hroom hW project extra a hN hp he)
      NT (tables_native P S hn hd hcap N hq T hz hT project a hN hp)
      (tables_represent P S hn hd hcap N hq T hz hT hroom hW project extra)
      (BoundedRegularFramedOriginalBits.leading PP aa DD JJ RR HH SS)
    critical:=BoundedRegularFramedOriginalBits.controls PP aa DD JJ NT
      (tables_native P S hn hd hcap N hq T hz hT project a hN hp)
      (tables_represent P S hn hd hcap N hq T hz hT hroom hW project extra)
      RR HH (fun key=>scope (IntegralMixedFramedRootPullback.key project key)) SS
    normalization:={
      tables:=NT
      native:=tables_native P S hn hd hcap N hq T hz hT project a hN hp
      represents:=tables_represent P S hn hd hcap N hq T hz hT hroom hW project extra
      nodes:=L∘project
      factor:=F∘project
      seed:=C∘project
      nodes_native:=hL.comp hp
      factor_native:=hF.comp hp
      seed_native:=hC.comp hp }
    producer:={
      tables:=NT
      native:=tables_native P S hn hd hcap N hq T hz hT project a hN hp
      represents:=tables_represent P S hn hd hcap N hq T hz hT hroom hW project extra
      integer:=integerOriginal P S hn hd hcap N T hz hT hroom project extra a hN hA hp he } }

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullback
