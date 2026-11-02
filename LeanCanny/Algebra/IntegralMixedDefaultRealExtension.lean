/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHistoryPrefix

/-! # The actual default integer X birth has a correlated real extension

The new physical scalar is zero. The interpreting hom extends the given old
hom, every old physical coordinate is unchanged, and old bank quotients shift
by one. No nonsingularity, row-mass or fresh sampler premise is supplied.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
open IntegralMixedFullHistoryScript IntegralHistorySampler UniformIntegralPrefix UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem default_real_extend (x : State P S B m ι) (hm : m≤S)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i) :
    ∃ y : (ι⊕Unit)→ℝ, ∃ ψ : (IntegralMixedFullHistoryScript.step x hm defaultCommand).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,((IntegralMixedFullHistoryScript.step x hm defaultCommand).sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀ i,y (Sum.inl i)=z i) ∧ y (Sum.inr ())=0 ∧
      ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
      (∀ i,ψ ((IntegralMixedFullHistoryScript.step x hm defaultCommand).sampler.scalarPrefix.basis.generator i)=
        y ((IntegralMixedFullHistoryScript.step x hm defaultCommand).sampler.scalar i)^weights S (2^B) (m+1) i) ∧
      ψ ((IntegralMixedFullHistoryScript.step x hm defaultCommand).bank.numerator 0)/
        ((IntegralMixedFullHistoryScript.step x hm defaultCommand).bank.denominator 0:ℝ)=0 ∧
      ∀ i,ψ ((IntegralMixedFullHistoryScript.step x hm defaultCommand).bank.numerator i.succ)/
        ((IntegralMixedFullHistoryScript.step x hm defaultCommand).bank.denominator i.succ:ℝ)=
        φ (x.bank.numerator i)/(x.bank.denominator i:ℝ) := by
  let p : Polynomial ℤ := Polynomial.X
  let q : Polynomial x.sampler.scalarPrefix.carrier := p.map (Int.castRingHom _)
  have hd : p.natDegree≤2^B := by simpa only [p,Polynomial.natDegree_X] using (Nat.one_le_two_pow : 1≤2^B)
  have HC : q.coeff p.natDegree=((1 : ℤ):x.sampler.scalarPrefix.carrier) := by simp [q,p]
  obtain ⟨y,hy,htail,hhead⟩ := scalarStep_real_extend_recover_root_integer x.sampler hm (Nat.two_pow_pos B)
    q p.natDegree hd 1 (by decide) HC z hz φ hφ 0
    (by simp [q,p]) (by simp [p]) (by simp [q,p])
  have HY : ∀ i,((IntegralMixedFullHistoryScript.step x hm defaultCommand).sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0 := hy
  obtain ⟨ψ,hψ⟩ := (scalarStep x.sampler hm (Nat.two_pow_pos B) q p.natDegree).interpret ℝ y hy
  have HR : ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ := by
    apply x.sampler.scalarPrefix.basis.algHom_ext
    intro i
    have HI := hψ i.succ
    change ψ (AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator i))=
      y (Sum.inl (x.sampler.scalar i))^weights S (2^B) (m+1) i.succ at HI
    rw [old,htail] at HI
    exact HI.trans (hφ i).symm
  have HH := hhead ψ hψ
  simp only [Int.cast_one,div_one] at HH
  have Hscalar : y (Sum.inr ())=0 := by
    have HI := hψ (0 : Fin (m+1))
    change ψ (AdjoinRoot.root _)=y (Sum.inr ())^weights S (2^B) (m+1) 0 at HI
    exact (pow_eq_zero_iff (weights_pos S (2^B) (m+1) 0).ne').mp (HI.symm.trans HH)
  refine ⟨y,ψ,HY,htail,Hscalar,HR,hψ,?_,?_⟩
  · change ψ (AdjoinRoot.root _)/((Polynomial.X : Polynomial ℤ).leadingCoeff:ℝ)=0
    rw [Polynomial.leadingCoeff_X,Int.cast_one,div_one]
    exact HH
  · intro i
    have HE := congrArg (fun χ=>χ (x.bank.numerator i)) HR
    change ψ (AdjoinRoot.of _ (x.bank.numerator i))/(x.bank.denominator i:ℝ)=_
    exact congrArg (fun a : ℝ=>a/(x.bank.denominator i:ℝ)) HE

end LeanCanny.Algebra.IntegralMixedHistory
