/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientMixedCutDispatcher
public import LeanCanny.Algebra.CoefficientRelativeLeadingNormalizationSpecialization
public import LeanCanny.Algebra.CoefficientHeightBankScalarStep
public import LeanCanny.Algebra.IntegralMixedFullHistoryScript
/-! # Actual mixed cut normalization and quotient specialization

The mode chooses a literal integer slope or the actual changing bank product.
Existing parent bank/basis invariants derive the entire native raw polynomial.
Fixed mapped characteristic-coefficient guards select the native normalizer;
the next map is constructed into the actual native cut quotient.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedCutSpecialization
open IntegralMixedHistory IntegralMixedRelativeCuts Polynomial
open scoped Classical
variable {R A :Type*} [CommRing R] [CommRing A] [Algebra R A]
  {n m N :ℕ} {P :SpatialSource n}

noncomputable def slope (bank :CoefficientHeightBank R A m) (r :IntegralMixedCriticalSweep.Rule n) :Bool→R
  | false=>(r.slope:R)
  | true=>bank.commonDenominator

noncomputable def nativeRule {cap width :ℕ} {ι :Type} (x :State P cap width m ι)
    (r :IntegralMixedCriticalSweep.Rule n) :Bool→IntegralMixedCriticalSweep.Rule n
  | false=>r
  | true=>CoefficientMixedCriticalSweep.currentRule x r

def nativeKind {cap width :ℕ} {ι :Type} (x :State P cap width m ι)
    (r :IntegralMixedCriticalSweep.Rule n) :(current :Bool)→Kind P r→Kind P (nativeRule x r current)
  | false,c=>c
  | true,c=>CoefficientMixedCutDispatcher.currentKind x r c

noncomputable def raw (bank :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (a :R) (r :IntegralMixedCriticalSweep.Rule n)
    (current :Bool) (c :Kind P r) (d :ℕ) :A[X]:=
  CoefficientMixedCutDispatcher.raw bank low a r (slope bank r current) c d

noncomputable def polynomial (b :CoefficientCoordinateBasis R A m N) (bank :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (a :R) (r :IntegralMixedCriticalSweep.Rule n)
    (current :Bool) (c :Kind P r) (d τ :ℕ) :A[X]:=
  CoefficientRelativeLeadingNormalization.normalizeAt b.basis (raw bank low a r current c d) d τ

noncomputable def leading (b :CoefficientCoordinateBasis R A m N) (bank :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (a :R) (r :IntegralMixedCriticalSweep.Rule n)
    (current :Bool) (c :Kind P r) (d τ :ℕ) :R:=
  CoefficientRelativeLeadingNormalization.denominatorAt b.basis
    ((raw bank low a r current c d).coeff d) τ

noncomputable def nativeRaw {cap width :ℕ} {ι :Type} (x :State P cap width m ι)
    (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n) (current :Bool) (c :Kind P r) (d :ℕ) :=
  IntegralMixedCutMatrix.raw x hm (nativeRule x r current) (nativeKind x r current c) d

noncomputable def nativeStep {cap width :ℕ} {ι :Type} [Fintype ι] (x :State P cap width m ι)
    (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n) (current :Bool) (c :Kind P r) (d :ℕ) :=
  IntegralMixedRelativeCuts.step x hm (nativeRule x r current) (nativeKind x r current c) d

section Native
variable {cap width :ℕ} {ι :Type}
  (bank :CoefficientHeightBank R A m) (b :CoefficientCoordinateBasis R A m (2^width))
  (low :MvPolynomial (Fin (n+1)) R) (a :R)
  (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
  (current :Bool) (c :Kind P r) (d τ :ℕ)
  (φ :R→+*ℤ) (ψ :A→+*x.sampler.scalarPrefix.carrier)
  (HB :CoefficientHeightBank.Specializes φ ψ bank (CoefficientHeightBank.ofState x))
  (Hb :CoefficientCoordinateBasis.Specializes φ ψ b (CoefficientCoordinateBasis.ofIntegral x.sampler.scalarPrefix.basis))
  (HL :low.map φ=P.low) (HA :φ a=P.leading)

include HB HL HA

theorem raw_map_native :
    (raw bank low a r current c d).map ψ=nativeRaw x hm r current c d:=by
  cases current
  · dsimp only [raw,nativeRaw,slope,nativeRule,nativeKind]
    rw [CoefficientMixedCutDispatcher.raw_map HB,HL,HA,map_intCast]
    exact CoefficientMixedCutDispatcher.raw_ofState x hm r c d
  · dsimp only [raw,nativeRaw,slope,nativeRule,nativeKind]
    rw [CoefficientMixedCutDispatcher.raw_map HB,HL,HA,HB.commonDenominator]
    exact CoefficientMixedCutDispatcher.raw_currentQ_ofState x hm r c d

variable
  (Hbelow :∀k<τ,φ ((Algebra.leftMulMatrix b.basis ((raw bank low a r current c d).coeff d)).charpoly.coeff k)=0)
  (Hτ :φ ((Algebra.leftMulMatrix b.basis ((raw bank low a r current c d).coeff d)).charpoly.coeff τ)≠0)

include Hb Hbelow Hτ

theorem polynomial_map_native :
    (polynomial b bank low a r current c d τ).map ψ=
      normalizedScalarPolynomial x (nativeRaw x hm r current c d) d:=by
  have HP:=raw_map_native bank low a x hm r current c d φ ψ HB HL HA
  have HN:=CoefficientRelativeLeadingNormalization.normalizeAt_map_native_finBasis
    x.sampler.scalarPrefix.basis Hb (raw bank low a r current c d) d τ Hbelow Hτ
  simpa only [polynomial,HP,normalizedScalarPolynomial] using HN

theorem leading_map_native :
    φ (leading b bank low a r current c d τ)=
      normalizedScalarLeading x (nativeRaw x hm r current c d) d:=by
  have HP:=raw_map_native bank low a x hm r current c d φ ψ HB HL HA
  have HC :ψ ((raw bank low a r current c d).coeff d)=(nativeRaw x hm r current c d).coeff d:=by
    simpa only [coeff_map] using congrArg (fun p=>p.coeff d) HP
  unfold leading CoefficientRelativeLeadingNormalization.denominatorAt
    normalizedScalarLeading IntegralRelativeLeadingNormalization.denominator
  have HM :=Hb.charpoly_map ((raw bank low a r current c d).coeff d)
  change (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.basis
    (ψ ((raw bank low a r current c d).coeff d))).charpoly=
      (Algebra.leftMulMatrix b.basis ((raw bank low a r current c d).coeff d)).charpoly.map φ at HM
  rw [x.sampler.scalarPrefix.basis.finBasis_charpoly,←HC,HM]
  exact (IntegralParameterInverse.denominator_map_at φ _ τ Hbelow Hτ).symm


variable [Fintype ι]

/-- The map targets the literal next quotient of the actual native cut. -/
noncomputable def specialize :
    PaddedIntegralParameterExtension.Extension (polynomial b bank low a r current c d τ) d (2^width)→+*
      (nativeStep x hm r current c d).sampler.scalarPrefix.carrier:=by
  change PaddedIntegralParameterExtension.Extension (polynomial b bank low a r current c d τ) d (2^width)→+*
    PaddedIntegralParameterExtension.Extension (normalizedScalarPolynomial x (nativeRaw x hm r current c d) d) d (2^width)
  exact AdjoinRoot.map ψ _ _ (by
    rw [PaddedIntegralNormalization.map,
      polynomial_map_native bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ])

theorem specialize_of (v :A) :
    specialize bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ (AdjoinRoot.of _ v)=
      AdjoinRoot.of _ (ψ v):=by
  exact AdjoinRoot.map_of ψ _ _ (by
    rw [PaddedIntegralNormalization.map,
      polynomial_map_native bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ]) v

theorem specialize_root :
    specialize bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ (AdjoinRoot.root _)=
      AdjoinRoot.root _:=by
  exact AdjoinRoot.map_root ψ _ _ (by
    rw [PaddedIntegralNormalization.map,
      polynomial_map_native bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ])

theorem basis_specializes [Nontrivial A] :
    CoefficientCoordinateBasis.Specializes φ
      (specialize bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ)
      (b.paddedStep (polynomial b bank low a r current c d τ) d)
      (CoefficientCoordinateBasis.ofIntegral (nativeStep x hm r current c d).sampler.scalarPrefix.basis):=by
  constructor
  · intro z
    change specialize bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ
      (AdjoinRoot.of _ (algebraMap R A z))=
        AdjoinRoot.of _ (algebraMap ℤ x.sampler.scalarPrefix.carrier (φ z))
    rw [specialize_of,Hb.coefficients]
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · change specialize bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ
        (AdjoinRoot.root _)=AdjoinRoot.root _
      exact specialize_root bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ
    · change specialize bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ
        (AdjoinRoot.of _ (b.generator j))=AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator j)
      rw [specialize_of,Hb.generators]
      rfl

theorem bank_specializes :
    CoefficientHeightBank.Specializes φ
      (specialize bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ)
      (bank.rootStep (polynomial b bank low a r current c d τ) d (2^width)
        (leading b bank low a r current c d τ))
      (CoefficientHeightBank.ofState (nativeStep x hm r current c d)):=by
  constructor
  · intro z
    change specialize bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ
      (AdjoinRoot.of _ (algebraMap R A z))=
        AdjoinRoot.of _ (algebraMap ℤ x.sampler.scalarPrefix.carrier (φ z))
    rw [specialize_of,HB.coefficients]
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · change specialize bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ
        (AdjoinRoot.root _)=AdjoinRoot.root _
      exact specialize_root bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ
    · change specialize bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ
        (AdjoinRoot.of _ (bank.numerator j))=AdjoinRoot.of _ (x.bank.numerator j)
      rw [specialize_of,HB.numerator]
      rfl
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · change φ (leading b bank low a r current c d τ)=
        normalizedScalarLeading x (nativeRaw x hm r current c d) d
      exact leading_map_native bank b low a x hm r current c d τ φ ψ HB Hb HL HA Hbelow Hτ
    · change φ (bank.denominator j)=x.bank.denominator j
      exact HB.denominator j

end Native
end LeanCanny.Algebra.CoefficientMixedCutSpecialization
