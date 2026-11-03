/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCutRecordKind
public import LeanCanny.Encoding.IntegralMixedCriticalRecordRealization
/-! # A chosen record extends one full tuple and its retained interpretation

Critical witnesses include a real physical point satisfying the source and
nonobjective gradients. Cut witnesses include the actual selected factor's
validity and root. These local hypotheses construct a decoded record and a
single correlated full extension; arbitrary original advice is not asserted
to have such witnesses.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChosenLocalRealization
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedRelativeCuts
open IntegralMixedFullHistoryScript IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

def oldColumn (c : Command P B) (i : ι) : NextIndex ι c :=
  match c with
  | .integer .. => Sum.inl i
  | .critical .. => Sum.inl (Sum.inl i)
  | .cut .. => Sum.inl i

noncomputable def scalarLift (x : State P S B m ι) (hm : m≤S) (c : Command P B) :
    x.sampler.scalarPrefix.carrier→ₐ[ℤ](step x hm c).sampler.scalarPrefix.carrier :=
  match c with
  | .integer .. => AdjoinRoot.ofAlgHom ℤ _
  | .critical r => AdjoinRoot.ofAlgHom ℤ (PaddedIntegralNormalization.polynomial
      (criticalPolynomial x hm r) (criticalDegree x hm r) (2^B))
  | .cut .. => AdjoinRoot.ofAlgHom ℤ _

def Correlated (x : State P S B m ι) (hm : m≤S) (c : Command P B)
    (z : ι→ℝ) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (a : ℝ) : Prop :=
  ∃ y : NextIndex ι c→ℝ,∃ ψ : (step x hm c).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀ i,((step x hm c).sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
    (∀ i,y (oldColumn c i)=z i) ∧ ψ.comp (scalarLift x hm c)=φ ∧
    (∀ i,ψ ((step x hm c).sampler.scalarPrefix.basis.generator i)=
      y ((step x hm c).sampler.scalar i)^weights S (2^B) (m+1) i) ∧
    ∀ i,ψ ((step x hm c).bank.numerator i)/((step x hm c).bank.denominator i:ℝ)=
      (Fin.cons a values : Fin (m+1)→ℝ) i

def Encoded (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ι→ℝ) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (a : ℝ) (code : List Bool) : Prop :=
  ∃ c : Command P B,
    (IntegralMixedCausalUnitRecordBits.record P hn m code hcap).template.command
      (commonDenominator x) (commonDenominator_ne_zero x)=c ∧
    Correlated x hm c z φ values a

structure CriticalChoice (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) where
  record : IntegralMixedCriticalRecordConstructor.Data n m
  charge : ℕ
  degree_eq : P.degree=LeanCanny.Geometry.BoundedZeroSource.powerDegree charge
  point : Fin (n+1)→ℝ
  frozen : ∀ i,i.val<record.rule.offset.val→((data x hm record.rule).scales i:ℝ)*point i=
    φ (expression x (record.rule.heights i))
  zero : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂
    (Int.castRingHom ℝ) point=0
  gradient : ∀ i : Fin (n+1),record.rule.offset.val≤ i.val→i≠(data x hm record.rule).free→
    (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
      (Int.castRingHom ℝ) point=0

noncomputable def CriticalChoice.value (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (w : CriticalChoice x hm φ) : ℝ :=
  w.point (ClearedCoordinateCritical.freeIndex w.record.rule.offset.val ((family x hm w.record.rule).fit []).le
    ((family x hm w.record.rule).coordinate []))

structure CutChoice (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) where
  record : IntegralMixedCutRecordConstructor.Data n m
  kind : Kind P (record.rule (commonDenominator x) (commonDenominator_ne_zero x))
  valid : Valid x hm (record.rule (commonDenominator x) (commonDenominator_ne_zero x)) φ kind
  value : ℝ
  root : (factor x hm (record.rule (commonDenominator x) (commonDenominator_ne_zero x)) kind).eval₂
    φ.toRingHom value=0

noncomputable def CutChoice.code (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (w : CutChoice x hm φ) : List Bool :=
  w.record.chosenCode (commonDenominator x) (commonDenominator_ne_zero x) w.kind
    (selectedDegree x hm (w.record.rule (commonDenominator x) (commonDenominator_ne_zero x)) φ w.kind)

theorem critical (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (w : CriticalChoice x hm φ) :
    Encoded x hm hn hcap z φ values (w.value x hm φ) w.record.code := by
  obtain ⟨hc,y,ψ,hy,hold,_,hrestrict,hψ,hvalues⟩:=
    IntegralMixedCriticalRecordConstructor.real_extend_record x hm hn w.record w.charge w.degree_eq hcap
      z hz φ hφ values H w.point w.frozen w.zero w.gradient
  exact ⟨.critical w.record.rule,hc,y,ψ,hy,hold,hrestrict,hψ,hvalues⟩

theorem cut (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (w : CutChoice x hm φ) : Encoded x hm hn hcap z φ values w.value (w.code x hm φ) := by
  let r:=w.record.rule (commonDenominator x) (commonDenominator_ne_zero x)
  let j:=IntegralMixedSweepRetarget.coordinateIndex r w.kind
  let rr:=IntegralMixedSweepRetarget.rule r j
  let cc:=IntegralMixedSweepRetarget.kind r j w.kind
  let d:=selectedDegree x hm rr φ cc
  have hd:=selectedDegree_bound x hm rr φ cc
  have he:=IntegralMixedSweepRetarget.selectedDegree_eq x hm r j φ w.kind
  have HC:=IntegralMixedCutRecordConstructor.chosen_command w.record P (commonDenominator x)
    (commonDenominator_ne_zero x) w.kind d hd hcap
  have Hcode : w.code x hm φ=w.record.chosenCode (commonDenominator x)
      (commonDenominator_ne_zero x) w.kind d:=by
    unfold CutChoice.code
    rw [← he]
  refine ⟨.cut rr cc d hd (hd.trans hcap),?_,?_⟩
  · rw [Hcode]
    exact HC
  · obtain ⟨_,y,ψ,hy,hold,hrestrict,hψ,hvalues⟩:=IntegralMixedSweepRetarget.real_extend_shared_coordinate
      x hm r φ w.kind w.valid hcap z hz hφ values H w.value w.root
    exact ⟨y,ψ,hy,hold,hrestrict,hψ,hvalues⟩

abbrev Choice (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) :=
  CriticalChoice x hm φ ⊕ CutChoice x hm φ

noncomputable def Choice.code (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) : Choice x hm φ→List Bool
  | .inl w=>w.record.code
  | .inr w=>w.code x hm φ

noncomputable def Choice.value (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) : Choice x hm φ→ℝ
  | .inl w=>w.value x hm φ
  | .inr w=>w.value

/-- Both permitted local witnesses use the same old full tuple and hom. -/
theorem realize (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (w : Choice x hm φ) :
    Encoded x hm hn hcap z φ values (w.value x hm φ) (w.code x hm φ) := by
  cases w with
  | inl w=>exact critical x hm hn hcap z hz φ hφ values H w
  | inr w=>exact cut x hm hn hcap z hz φ hφ values H w

/-- Transport from an actual geometry rule copies the literal factor/root. -/
noncomputable def CutChoice.ofRule (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (d : IntegralMixedCutRecordConstructor.Data n m)
    (r : IntegralMixedCriticalSweep.Rule n)
    (hr : d.rule (commonDenominator x) (commonDenominator_ne_zero x)=r)
    (c : Kind P r) (hc : Valid x hm r φ c) (a : ℝ)
    (ha : (factor x hm r c).eval₂ φ.toRingHom a=0) : CutChoice x hm φ := by
  subst r
  exact ⟨d,c,hc,a,ha⟩

end LeanCanny.Encoding.IntegralMixedChosenLocalRealization
