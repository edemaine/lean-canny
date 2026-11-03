/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCanonicalPaddingSeed
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalPersistence
public import LeanCanny.Algebra.IntegralMixedIntegerRealization
/-! # Honest empty-frame seed points realize actual framed padding steps -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedCanonicalPadding
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralMixedFrozenFrame IntegralMixedCausalRowConstructor
open IntegralMixedFramedHistoryScript IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem original_rule (n birth : ℕ) :
    (originalPointData (∅ : Finset (Fin (n+1))) (fun _=>false) (fun _=>Row.single (none : Atom birth))
      0 0 (Finset.notMem_empty _) (Finset.notMem_empty _)).rule=IntegralMixedCanonicalPaddingSeed.rule n :=by
  have HE : FrozenCoordinateOrdering.permutation (∅ : Finset (Fin (n+1)))=Equiv.refl (Fin (n+1)) :=
    (PrefixFrozen.of_empty (originalFrame (∅ : Finset (Fin (n+1))) (fun _=>false)
      (fun _=>Row.single (none : Atom birth))) rfl).permutation
  unfold originalPointData IntegralMixedCanonicalPaddingSeed.rule IntegralMixedCanonicalPaddingSeed.data
  simp only [freeCoordinate,originalFrame,HE,Equiv.refl_symm,Equiv.refl_apply,Finset.card_empty,
    Fin.val_zero,Nat.sub_zero]
  rfl

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem step (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (charge : ℕ) (hd : P.degree=BoundedZeroSource.powerDegree charge)
    (hc : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ι→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (old : Fin m→ℝ) (ho : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=old i)
    (p : Fin (n+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg : ∀i,i≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
      (Int.castRingHom ℝ) p=0) :
    let born:=IntegralMixedFullHistoryScript.step x hm (.critical (IntegralMixedCanonicalPaddingSeed.rule n))
    ∃y,∃ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀i,y (Sum.inl (Sum.inl i))=z i) ∧
      (∀i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
      ∀i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=((Fin.cons (p 0) old : Fin (m+1)→ℝ) i) :=by
  let F0:=originalFrame (∅ : Finset (Fin (n+1))) (fun _=>false) (fun _=>Row.single (none : Atom m))
  have HP : PrefixFrozen F0:=PrefixFrozen.of_empty F0 rfl
  have HS : p∈slice P F0 old:=⟨hp,fun i hi=>False.elim (Finset.notMem_empty i hi)⟩
  have HH:=HP.real_extend_original_point x hm hn charge hd hc ∅ (fun _=>false)
    (fun _=>Row.single (none : Atom m)) 0 0 (Finset.notMem_empty _) (Finset.notMem_empty _)
    z hz φ hφ old ho p HS (fun i _ hne=>hg i hne)
  dsimp only at HH
  rw [original_rule n m] at HH
  obtain ⟨_,_,y,ψ,hy,hr,_,_,hgen,hvalues⟩:=HH
  exact ⟨y,ψ,hy,hr,hgen,hvalues⟩

def values (a : ℝ) (old : ℕ→ℝ) (k i : ℕ) :=if i<k then a else old (i-k)

theorem values_zero (a : ℝ) (old : ℕ→ℝ) : values a old 0=old:=by
  funext i
  simp only [values,Nat.not_lt_zero,ite_false,Nat.sub_zero]

theorem values_succ (a : ℝ) (old : ℕ→ℝ) (k : ℕ) :
    values a old (k+1)=fun i=>if i=0 then a else values a old k (i-1) :=by
  funext i
  cases i with
  | zero=>simp only [values,Nat.zero_lt_succ,ite_true]
  | succ i=>
    have HN : i+1≠0:=by omega
    simp only [values,Nat.add_one_lt_add_one_iff,HN,ite_false,Nat.add_sub_cancel_right]
    split_ifs with hi
    · rfl
    · congr 1
      omega

variable {Q : SpatialSource n}

theorem run_exists (initial : State Q S B 0 (Fin 0)) (cs : List (Instruction n B))
    (ho : cs.length≤S+1) (P : SpatialSource n)
    (hP : PurePowerReductionBounds.dimension (n+1) P.degree≤2^B) (hn : 0<n)
    (charge : ℕ) (hd : P.degree=BoundedZeroSource.powerDegree charge)
    (hc : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : Index (Fin 0) cs→ℝ) (hz : ∀i,((run initial cs ho).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : (run initial cs ho).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ ((run initial cs ho).sampler.scalarPrefix.basis.generator i)=
      z ((run initial cs ho).sampler.scalar i)^weights S (2^B) cs.length i)
    (v : ℕ→ℝ) (hv : ∀i,φ ((run initial cs ho).bank.numerator i)/((run initial cs ho).bank.denominator i:ℝ)=v i.val)
    (p : Fin (n+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg : ∀i,i≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
      (Int.castRingHom ℝ) p=0) (k : ℕ)
    (room : (List.replicate k (IntegralMixedCanonicalPaddingSeed.instruction P hP)++cs).length≤S+1) :
    let newer:=List.replicate k (IntegralMixedCanonicalPaddingSeed.instruction P hP)
    let final:=run initial (newer++cs) room
    ∃y,∃ψ : final.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,(final.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀i,y (IntegralMixedFramedPhysicalPersistence.embed newer cs i)=z i) ∧
      (∀i,ψ (final.sampler.scalarPrefix.basis.generator i)=y (final.sampler.scalar i)^weights S (2^B) (newer++cs).length i) ∧
      ∀i,ψ (final.bank.numerator i)/(final.bank.denominator i:ℝ)=values (p 0) v k i.val :=by
  induction k with
  | zero=>
    dsimp only
    refine ⟨z,φ,hz,fun _=>rfl,hφ,?_⟩
    intro i
    simpa only [List.replicate_zero,List.nil_append,values_zero] using hv i
  | succ k ih=>
    have HR : (List.replicate k (IntegralMixedCanonicalPaddingSeed.instruction P hP)++cs).length≤S:=by
      simp only [List.length_append,List.length_replicate] at room ⊢
      omega
    obtain ⟨y,ψ,hy,hold,hgen,hvalues⟩ :=ih (HR.trans (Nat.le_succ _))
    let x:=reframe (run initial (List.replicate k (IntegralMixedCanonicalPaddingSeed.instruction P hP)++cs) (HR.trans (Nat.le_succ _))) P hP
    obtain ⟨y',ψ',hy',hold',hgen',hvalues'⟩:=step x HR hn charge hd hc y hy ψ hgen
      (fun i=>values (p 0) v k i.val) hvalues p hp hg
    refine ⟨y',ψ',hy',?_,hgen',?_⟩
    · intro i
      exact (hold' _).trans (hold i)
    · intro i
      refine (hvalues' i).trans ?_
      refine Fin.cases ?_ (fun j=>?_) i
      · rw [Fin.cons_zero,values_succ]
        rfl
      · simp only [Fin.cons_succ,Fin.val_succ,values_succ,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel_right]

theorem run_realizes (initial : State Q S B 0 (Fin 0)) (cs : List (Instruction n B))
    (ho : cs.length≤S+1) (P : SpatialSource n)
    (hP : PurePowerReductionBounds.dimension (n+1) P.degree≤2^B) (hn : 0<n)
    (charge : ℕ) (hd : P.degree=BoundedZeroSource.powerDegree charge)
    (hc : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (v : ℕ→ℝ) (hv : IntegralMixedIntegerRealization.Realizes (run initial cs ho) v)
    (p : Fin (n+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg : ∀i,i≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
      (Int.castRingHom ℝ) p=0) (k : ℕ)
    (room : (List.replicate k (IntegralMixedCanonicalPaddingSeed.instruction P hP)++cs).length≤S+1) :
    IntegralMixedIntegerRealization.Realizes
      (run initial (List.replicate k (IntegralMixedCanonicalPaddingSeed.instruction P hP)++cs) room) (values (p 0) v k) :=by
  obtain ⟨z,φ,hz,hφ,hv⟩:=hv
  obtain ⟨y,ψ,hy,_,hgen,hvalues⟩:=run_exists initial cs ho P hP hn charge hd hc z hz φ hφ v hv p hp hg k room
  exact ⟨y,ψ,hy,hgen,hvalues⟩

end LeanCanny.Geometry.IntegralMixedCanonicalPadding
