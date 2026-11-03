/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRelativeCutCorrelated
/-! # A correlated cut is realizable at its exact selected degree

The stored degree is the natDegree after the same old real specialization.
It is not the formal degree and need not be invariant over other embeddings.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRelativeCuts
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralHistorySampler
open UniformIntegralPrefix UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

noncomputable def selectedDegree (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind P r) : ℕ:=
  ((factor x hm r c).map φ.toRingHom).natDegree

omit [Fintype ι] in
theorem selectedDegree_bound (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind P r) :
    selectedDegree x hm r φ c≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree :=
  Polynomial.natDegree_map_le.trans (factor_degree x hm r c)

theorem real_extend_selectedDegree (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind P r) (hc : Valid x hm r φ c)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ι→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : ℝ) (ha : (factor x hm r c).eval₂ φ.toRingHom a=0) :
    let d:=selectedDegree x hm r φ c
    let hd:=selectedDegree_bound x hm r φ c
    let command : IntegralMixedFullHistoryScript.Command P B:=.cut r c d hd (hd.trans hcap)
    let born:=IntegralMixedFullHistoryScript.step x hm command
    ∃y : (ι⊕Unit)→ℝ,∃ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀i,y (Sum.inl i)=z i) ∧ ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
      (∀i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
      ∀i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons a values : Fin (m+1)→ℝ) i :=by
  let p:=factor x hm r c
  let d:=selectedDegree x hm r φ c
  have HP : p.map φ.toRingHom≠0:=selected_nonzero x hm r φ c hc
  have HD : d≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree:=selectedDegree_bound x hm r φ c
  have Hroot : (p.map φ.toRingHom).eval₂ (RingHom.id ℝ) a=0:=by
    rw [Polynomial.eval₂_id,Polynomial.eval_map]
    exact ha
  have Hpos : 1≤d:=Polynomial.natDegree_pos_of_eval₂_root HP (RingHom.id ℝ) Hroot (fun _ H=>H)
  have HA : φ ((IntegralRelativeTruncation.truncate p d).coeff d)≠0:=by
    rw [IntegralRelativeTruncation.coefficient,ite_eq_left (Nat.le_refl d)]
    have HL:=Polynomial.leadingCoeff_ne_zero.mpr HP
    rw [Polynomial.leadingCoeff,Polynomial.coeff_map] at HL
    exact HL
  have HT : (IntegralRelativeTruncation.truncate p d).eval₂ φ.toRingHom a=0:=
    (IntegralRelativeTruncation.eval_eq p d φ (Nat.le_refl d) a).trans ha
  obtain ⟨y,hy,htail,hhead⟩:=normalizedScalar_real_extend x hm (IntegralRelativeTruncation.truncate p d) d
    (IntegralRelativeTruncation.natDegree_le p d) Hpos (HD.trans hcap) z hz φ hφ HA a HT
  obtain ⟨ψ,hψ⟩:=(step x hm r c d).sampler.interpret ℝ y hy
  have Hrestrict : ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ:=by
    apply x.sampler.scalarPrefix.basis.algHom_ext
    intro i
    have HI:=hψ i.succ
    change ψ (AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator i))=
      y (Sum.inl (x.sampler.scalar i))^weights S (2^B) (m+1) i.succ at HI
    rw [UniformIntegralPowerSchedule.old,htail] at HI
    exact HI.trans (hφ i).symm
  refine ⟨y,ψ,hy,htail,Hrestrict,hψ,fun i=>Fin.cases (hhead ψ hψ) (fun j=>?_) i⟩
  change ψ (AdjoinRoot.of _ (x.bank.numerator j))/(x.bank.denominator j:ℝ)=values j
  have HE : ψ (AdjoinRoot.of _ (x.bank.numerator j))=φ (x.bank.numerator j):=
    congrArg (fun χ=>χ (x.bank.numerator j)) Hrestrict
  rw [HE]
  exact H j

end LeanCanny.Algebra.IntegralMixedRelativeCuts
