/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizedScalar
public import LeanCanny.Algebra.IntegralRelativeTruncation

/-! # Selected scalar roots extend the literal old tuple and interpreting hom

No real lift to a critical physical tuple is required. The normalized
scalar-only birth uses the degree selected by the same old homomorphism.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
open UniformIntegralPrefix UniformIntegralPowerSchedule Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem selected_scalar_real_extend_correlated (x : State P S B m ι) (hm : m≤S)
    (p : Polynomial x.sampler.scalarPrefix.carrier) (hcap : p.natDegree≤2^B)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (hp : p.map φ.toRingHom≠0)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : ℝ) (ha : p.eval₂ φ.toRingHom a=0) :
    ∃ d≤p.natDegree,
      let born:=normalizedScalarStep x hm (IntegralRelativeTruncation.truncate p d) d
      ∃ y : (ι⊕Unit)→ℝ,∃ ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
        (∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
        (∀ i,y (Sum.inl i)=z i) ∧ ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
        (∀ i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
        ∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons a values : Fin (m+1)→ℝ) i := by
  let d:=(p.map φ.toRingHom).natDegree
  have HD : d≤p.natDegree:=natDegree_map_le
  have Hroot : (p.map φ.toRingHom).eval₂ (RingHom.id ℝ) a=0 := by
    rw [eval₂_id,eval_map]
    exact ha
  have Hpos : 1≤d:=natDegree_pos_of_eval₂_root hp (RingHom.id ℝ) Hroot (fun _ H=>H)
  have HA : φ ((IntegralRelativeTruncation.truncate p d).coeff d)≠0 := by
    rw [IntegralRelativeTruncation.coefficient,ite_eq_left (Nat.le_refl d)]
    have HC:=leadingCoeff_ne_zero.mpr hp
    rw [leadingCoeff,coeff_map] at HC
    exact HC
  have HT : (IntegralRelativeTruncation.truncate p d).eval₂ φ.toRingHom a=0:=
    (IntegralRelativeTruncation.eval_eq p d φ (Nat.le_refl d) a).trans ha
  obtain ⟨y,hy,hold,hhead⟩:=normalizedScalar_real_extend x hm (IntegralRelativeTruncation.truncate p d) d
    (IntegralRelativeTruncation.natDegree_le p d) Hpos (HD.trans hcap) z hz φ hφ HA a HT
  let born:=normalizedScalarStep x hm (IntegralRelativeTruncation.truncate p d) d
  obtain ⟨ψ,hψ⟩:=born.sampler.interpret ℝ y hy
  have HR : ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ := by
    apply x.sampler.scalarPrefix.basis.algHom_ext
    intro i
    have HI:=hψ i.succ
    change ψ (AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator i))=
      y (Sum.inl (x.sampler.scalar i))^weights S (2^B) (m+1) i.succ at HI
    rw [UniformIntegralPowerSchedule.old,hold] at HI
    exact HI.trans (hφ i).symm
  refine ⟨d,HD,y,ψ,hy,hold,HR,hψ,fun i=>Fin.cases (hhead ψ hψ) (fun j=>?_) i⟩
  change ψ (AdjoinRoot.of _ (x.bank.numerator j))/(x.bank.denominator j:ℝ)=values j
  have HE : ψ (AdjoinRoot.of _ (x.bank.numerator j))=φ (x.bank.numerator j):=
    congrArg (fun χ=>χ (x.bank.numerator j)) HR
  rw [HE]
  exact H j

end LeanCanny.Algebra.IntegralMixedHistory
