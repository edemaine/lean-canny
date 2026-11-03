/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedZeroRules
public import LeanCanny.Algebra.BoundedRegularFramedOriginal
public import LeanCanny.Algebra.IntegralMixedIntegerFamilyOriginalSource
public import LeanCanny.Algebra.IntegralMixedSourceIntegerLookup
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeSpace
/-! # Original regular syntax and integer sources rebuild current-Q controls

Only original syntax/source readers are charged. Planning and full-root
projection rebuild their caller-modulus leaves instead of reusing a clipped
old task oracle.
-/
@[expose] public section
namespace LeanCanny.Algebra.BoundedRegularIntegerCurrentQBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Original (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) where
  regular : BoundedFullWriter.Readers
  native : regular.PolyTime
  scope : ∀key,(ETR.TermView.term (regular.source key)).arity≤regular.dim key
  snapshot : BoundedRegularFramedOriginalBits.Snapshot P D regular
  zero : IntegralMixedFramedZeroRulesBits.Rules P D J
  integer : IntegerPolynomialRootQueriesBits.Source
  integer_native : IntegerPolynomialRootQueriesBits.Access integer
  query : List Bool → List Bool
  query_FP : query∈FP
  integer_eq : ∀key,IntegralMixedFramedIntegerBits.polynomial P D key=integer.polynomial (query key)

noncomputable def controls (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Original P D J)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (L F C : List Bool → ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) :
    IntegralMixedFramedCurrentQNativeBits.Controls P D J where
  scalar:=IntegralMixedFramedCurrentQIndexedBits.controls P a D J
    (IntegralMixedFramedZeroRulesBits.originalRules P D J s.zero) T ht hr
    (BoundedRegularFramedOriginalBits.leading P a D J s.regular s.native s.snapshot)
  critical:=BoundedRegularFramedOriginalBits.controls P a D J T ht hr s.regular s.native s.scope s.snapshot
  normalization:={
    tables:=T
    native:=ht
    represents:=hr
    nodes:=L
    factor:=F
    seed:=C
    nodes_native:=hL
    factor_native:=hF
    seed_native:=hC }
  producer:={
    tables:=T
    native:=ht
    represents:=hr
    integer:=IntegralMixedIntegerFamilyBits.original_of_source P a _ s.integer s.integer_native s.query s.query_FP s.integer_eq }

private theorem integer_observation (P : Parameters) (D : Plan P) (key : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial P D key=
      IntegralMixedSourceIntegerPrelude.integerPolynomial (IntegralMixedFramedHistoryFamilyBits.instruction P D key) := by
  unfold IntegralMixedFramedIntegerBits.polynomial IntegralMixedSourceIntegerPrelude.integerPolynomial
  cases (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;> rfl

noncomputable def Original.planned {P : Parameters} {D : Plan P}
    {J : IntegralMixedFramedHistoryFamilyBits.Data P D} (s : Original P D J) (L F C : List Bool → ℕ) :
    Original (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D J L F C) where
  regular:=s.regular
  native:=s.native
  scope:=s.scope
  snapshot:={
    ambient:=s.snapshot.ambient
    source key:=by
      rw [IntegralMixedFramedNormalizationBits.planned_instruction]
      exact s.snapshot.source key }
  zero:=s.zero.planned L F C
  integer:=s.integer
  integer_native:=s.integer_native
  query:=s.query
  query_FP:=s.query_FP
  integer_eq key:=by
    rw [integer_observation,IntegralMixedFramedNormalizationBits.planned_instruction,←integer_observation]
    exact s.integer_eq key

noncomputable def Original.pullback {P : Parameters} {D : Plan P}
    {J : IntegralMixedFramedHistoryFamilyBits.Data P D} (s : Original P D J)
    (project : List Bool → List Bool) (hp : project∈FP) (extra : List Bool → ℕ) :
    Original (IntegralMixedFramedRootPullback.parameters P project extra)
      (IntegralMixedFramedRootPullback.plan P D project extra)
      (IntegralMixedFramedRootPullback.data P D J project extra) where
  regular:=s.regular.comp (IntegralMixedFramedRootPullback.key project)
  native:=s.native.comp (IntegralMixedFramedRootPullback.key_FP project hp)
  scope key:=s.scope (IntegralMixedFramedRootPullback.key project key)
  snapshot:={
    ambient key:=by
      simpa only [BoundedFullWriter.Readers.comp,IntegralMixedFramedRootPullback.parameters,
        Function.comp_apply,IntegralMixedFramedRootPullback.key_root] using s.snapshot.ambient (IntegralMixedFramedRootPullback.key project key)
    source key:=(IntegralMixedFramedRootPullback.instruction_source P D project extra key).trans (s.snapshot.source _) }
  zero:=s.zero.pullback project extra
  integer:=s.integer
  integer_native:=s.integer_native
  query:=s.query ∘ IntegralMixedFramedRootPullback.key project
  query_FP:=mem_FP_comp (IntegralMixedFramedRootPullback.key_FP project hp) s.query_FP
  integer_eq key:=by
    rw [integer_observation]
    have HI:=IntegralMixedFramedRootPullback.instruction_read
      (fun _ _ I=>IntegralMixedSourceIntegerPrelude.integerPolynomial I) _ _
      (congrArg P.ambient (IntegralMixedFramedRootPullback.key_root project key).symm)
      (congrArg P.width (IntegralMixedFramedRootPullback.key_root project key).symm)
      (IntegralMixedFramedRootPullback.instruction_heq P D project extra key)
    exact HI.trans ((integer_observation P D _).symm.trans (s.integer_eq _))

end LeanCanny.Algebra.BoundedRegularIntegerCurrentQBits
