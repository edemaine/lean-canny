/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientMixedCriticalPolynomial
public import LeanCanny.Algebra.CoefficientHeightBankScalarStep
public import LeanCanny.Algebra.CoefficientHistoryHeights
/-! # The actual critical birth under coefficient specialization

The polynomial, leading scalar and physical critical rows are computed from
one bank, source and native rule. The map lands in the actual native quotient.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedCriticalBirth
open IntegralMixedHistory Polynomial
open scoped Classical
def free {n:ℕ} (r:CriticalRule n):Fin (n+1):=
  ⟨r.offset.val+r.objective%(n-r.offset.val+1),by
    have H : r.objective%(n-r.offset.val+1)<n-r.offset.val+1:=Nat.mod_lt _ (by omega)
    have HO:=r.offset.isLt
    omega⟩

variable {R A :Type*} [CommRing R] [CommRing A] [Algebra R A]
  {n m :ℕ} {P :SpatialSource n} {cap width :ℕ} {ι :Type} [Fintype ι]
  (bank :CoefficientHeightBank R A m) (b :CoefficientCoordinateBasis R A m (2^width))
  (low :MvPolynomial (Fin (n+1)) R) (a :R)
  (x :State P cap width m ι) (hm :m≤cap) (r :CriticalRule n)
  (φ :R→+*ℤ) (ψ :A→+*x.sampler.scalarPrefix.carrier)
  (HB :CoefficientHeightBank.Specializes φ ψ bank (CoefficientHeightBank.ofState x))
  (Hb :CoefficientCoordinateBasis.Specializes φ ψ b
    (CoefficientCoordinateBasis.ofIntegral x.sampler.scalarPrefix.basis))
  (HL :low.map φ=P.low) (HA :φ a=P.leading)

include HB HL HA

omit [Fintype ι] in
theorem polynomial_map_native :
    (CoefficientMixedCriticalPolynomial.polynomial bank low a P.degree r).map ψ=
      criticalPolynomial x hm r:=by
  rw [CoefficientMixedCriticalPolynomial.polynomial_map HB,HL,HA]
  exact CoefficientMixedCriticalPolynomial.polynomial_ofState x hm r

omit [Fintype ι] HL in
theorem leading_map_native :
    φ (CoefficientMixedCriticalPolynomial.leadingValue bank a P.degree r)=criticalLeading x hm r:=by
  rw [CoefficientMixedCriticalPolynomial.leadingValue_map HB,HA]
  exact CoefficientMixedCriticalPolynomial.leadingValue_ofState x hm r

/-- An actual quotient map, extending the parent map and retaining the new root. -/
noncomputable def specialize :
    PaddedIntegralParameterExtension.Extension
      (CoefficientMixedCriticalPolynomial.polynomial bank low a P.degree r)
      (PurePowerReductionBounds.dimension (n-r.offset.val+1) P.degree) (2^width)→+*
        (criticalStep x hm r).sampler.scalarPrefix.carrier:=by
  change PaddedIntegralParameterExtension.Extension
    (CoefficientMixedCriticalPolynomial.polynomial bank low a P.degree r)
    (criticalDegree x hm r) (2^width)→+*
      PaddedIntegralParameterExtension.Extension (criticalPolynomial x hm r) (criticalDegree x hm r) (2^width)
  exact AdjoinRoot.map ψ _ _ (by
    rw [PaddedIntegralNormalization.map,polynomial_map_native bank low a x hm r φ ψ HB HL HA])

theorem specialize_of (v :A) :
    specialize bank low a x hm r φ ψ HB HL HA (AdjoinRoot.of _ v)=AdjoinRoot.of _ (ψ v):=by
  exact AdjoinRoot.map_of ψ _ _ (by
    rw [PaddedIntegralNormalization.map,polynomial_map_native bank low a x hm r φ ψ HB HL HA]) v

theorem specialize_root :
    specialize bank low a x hm r φ ψ HB HL HA (AdjoinRoot.root _)=AdjoinRoot.root _:=by
  exact AdjoinRoot.map_root ψ _ _ (by
    rw [PaddedIntegralNormalization.map,polynomial_map_native bank low a x hm r φ ψ HB HL HA])

include Hb

theorem basis_specializes [Nontrivial A] :
    CoefficientCoordinateBasis.Specializes φ (specialize bank low a x hm r φ ψ HB HL HA)
      (b.paddedStep (CoefficientMixedCriticalPolynomial.polynomial bank low a P.degree r)
        (PurePowerReductionBounds.dimension (n-r.offset.val+1) P.degree))
      (CoefficientCoordinateBasis.ofIntegral (criticalStep x hm r).sampler.scalarPrefix.basis):=by
  constructor
  · intro z
    change specialize bank low a x hm r φ ψ HB HL HA
      (AdjoinRoot.of _ (algebraMap R A z))=AdjoinRoot.of _ (algebraMap ℤ x.sampler.scalarPrefix.carrier (φ z))
    rw [specialize_of,Hb.coefficients]
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact specialize_root bank low a x hm r φ ψ HB HL HA
    · change specialize bank low a x hm r φ ψ HB HL HA
        (AdjoinRoot.of _ (b.generator j))=AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator j)
      rw [specialize_of,Hb.generators]
      rfl

omit Hb in
theorem bank_specializes :
    CoefficientHeightBank.Specializes φ (specialize bank low a x hm r φ ψ HB HL HA)
      (bank.rootStep (CoefficientMixedCriticalPolynomial.polynomial bank low a P.degree r)
        (PurePowerReductionBounds.dimension (n-r.offset.val+1) P.degree) (2^width)
        (CoefficientMixedCriticalPolynomial.leadingValue bank a P.degree r))
      (CoefficientHeightBank.ofState (criticalStep x hm r)):=by
  constructor
  · intro z
    change specialize bank low a x hm r φ ψ HB HL HA
      (AdjoinRoot.of _ (algebraMap R A z))=AdjoinRoot.of _ (algebraMap ℤ x.sampler.scalarPrefix.carrier (φ z))
    rw [specialize_of,HB.coefficients]
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact specialize_root bank low a x hm r φ ψ HB HL HA
    · change specialize bank low a x hm r φ ψ HB HL HA
        (AdjoinRoot.of _ (bank.numerator j))=AdjoinRoot.of _ (x.bank.numerator j)
      rw [specialize_of,HB.numerator]
      rfl
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact leading_map_native bank a x hm r φ ψ HB HA
    · exact HB.denominator j

omit HB Hb HL HA in
/-- The actual physical critical block, before the scalar-root append. -/
noncomputable def physicalRows (q :ι→MvPolynomial ι R) (slots :Fin m→ι)
    (D :ℕ) : (ι⊕FlatAffineCriticalStage.Variables (n+1))→
      MvPolynomial (ι⊕FlatAffineCriticalStage.Variables (n+1)) R:=
  PhysicalPowerCriticalAppend.rows q low a 2 (CoefficientMixedCriticalPolynomial.scales bank r)
    (Finset.univ.filter (fun i:Fin (n+1)=>i.val<r.offset.val))
    (free r)
    (CoefficientHistoryHeights.historyHeights cap slots b (fun i=>bank.expression (r.heights i)))
    (fun _=>1) D (UniformIntegralPowerSchedule.physical cap (2^width) m)

omit HB Hb HL HA in
noncomputable def rows (q :ι→MvPolynomial ι R) (slots :Fin m→ι) (D :ℕ):=
  CoefficientCanonicalScalarAppend.rows cap (physicalRows (cap:=cap) bank b low a r q slots D)
    (fun i=>Sum.inl (slots i)) b
    (CoefficientMixedCriticalPolynomial.polynomial bank low a D r)
    (PurePowerReductionBounds.dimension (n-r.offset.val+1) D)

theorem physicalRows_map_native (q :ι→MvPolynomial ι R)
    (HQ :∀i,MvPolynomial.map φ (q i)=x.sampler.rows i):
    (fun j=>MvPolynomial.map φ (physicalRows (cap:=cap) bank b low a r q x.sampler.scalar P.degree j))=
      (IntegralHistorySampler.criticalStep x.sampler (data x hm r)).rows:=by
  have HS : (fun i=>φ (CoefficientMixedCriticalPolynomial.scales bank r i))=(data x hm r).scales:=by
    funext i
    rw [CoefficientMixedCriticalPolynomial.scales_map HB]
    rfl
  have HH : (fun i=>ψ (bank.expression (r.heights i)))=(data x hm r).heights:=by
    funext i
    rw [HB.expression,CoefficientHeightBank.expression_ofState]
    rfl
  unfold physicalRows
  rw [CoefficientHistoryHeights.critical_rows_map Hb cap x.sampler.scalar q x.sampler.rows HQ]
  rw [HL,HA,HS,HH,map_ofNat]
  exact CoefficientHistoryHeights.critical_rows_native x.sampler (data x hm r)

theorem rows_map_native (q :ι→MvPolynomial ι R)
    (HQ :∀i,MvPolynomial.map φ (q i)=x.sampler.rows i):
    (fun j=>MvPolynomial.map φ (rows (cap:=cap) bank b low a r q x.sampler.scalar P.degree j))=
      (criticalStep x hm r).sampler.rows:=by
  have HQ0:=physicalRows_map_native bank b low a x hm r φ ψ HB Hb HL HA q HQ
  have HP:=polynomial_map_native bank low a x hm r φ ψ HB HL HA
  unfold rows
  rw [CoefficientCanonicalScalarAppend.newrows_map Hb cap _ _ (congrFun HQ0)]
  rw [HP]
  rfl

end LeanCanny.Algebra.CoefficientMixedCriticalBirth
