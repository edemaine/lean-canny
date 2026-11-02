/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRelative
public import LeanCanny.Algebra.IntegralMixedCriticalDegree
public import LeanCanny.Algebra.IntegralMixedRelativeScalar
public import LeanCanny.Algebra.IntegralMixedSourceReframe

/-! # Every selected critical-point coordinate has an actual native scalar companion -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def pointRule (F : Frame n) (g : Fin (n+1)) (hg : g∉F.frozen) (j : Fin (n+1)) (hj : j∉F.frozen) : CriticalRule n :=
  { critical F g hg with coordinate := (freeCoordinate F j hj).val }

theorem pointRule_index (F : Frame n) (g : Fin (n+1)) (hg : g∉F.frozen) (j : Fin (n+1)) (hj : j∉F.frozen) :
    ClearedCoordinateCritical.freeIndex (pointRule F g hg j hj).offset.val
      (IntegralMixedCriticalRoot.fit (pointRule F g hg j hj)).le
      (IntegralMixedCriticalRoot.coordinate (pointRule F g hg j hj))=
      (FrozenCoordinateOrdering.permutation F.frozen).symm j := by
  apply Fin.ext
  have HJ : ¬((FrozenCoordinateOrdering.permutation F.frozen).symm j).val<F.frozen.card:=
    fun H=>hj ((FrozenCoordinateOrdering.inverse_mem_iff F.frozen j).mp H)
  have HB:=((FrozenCoordinateOrdering.permutation F.frozen).symm j).isLt
  change F.frozen.card+(((FrozenCoordinateOrdering.permutation F.frozen).symm j).val-F.frozen.card)%
    (n-F.frozen.card+1)=_
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem pointRule_objective (F : Frame n) (g : Fin (n+1)) (hg : g∉F.frozen)
    (j : Fin (n+1)) (hj : j∉F.frozen) :
    IntegralMixedCriticalRoot.objective (pointRule F g hg j hj)=
      IntegralMixedCriticalRoot.coordinate (coordinateRule F g hg) := by
  apply Fin.ext
  rfl

theorem point_coordinate_root (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n)
    (g : Fin (n+1)) (hg : g∉F.frozen) (j : Fin (n+1)) (hj : j∉F.frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (y : Fin (n+1)→ℝ) (hy : y∈slice P F values)
    (hgrad : ∀ i, i∉F.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) y=0) :
    let e:=FrozenCoordinateOrdering.permutation F.frozen
    (criticalPolynomial (IntegralMixedCoordinateRename.state x e) hm (pointRule F g hg j hj)).eval₂ φ.toRingHom (y j)=0 := by
  let e:=FrozenCoordinateOrdering.permutation F.frozen
  let r:=pointRule F g hg j hj
  let x':=IntegralMixedCoordinateRename.state x e
  let z:=y ∘ e
  have HY : z∈actualSlice x' φ (permute F e) := by
    rw [actualSlice_permute]
    change z ∘ e.symm∈actualSlice x φ F
    rw [actualSlice_eq x φ F values H]
    simpa only [z,Function.comp_def,Equiv.apply_symm_apply] using hy
  have HF (i : Fin (n+1)) (hi : i.val<r.offset.val) :
      ((data x' hm r).scales i:ℝ)*z i=φ ((data x' hm r).heights i) := by
    have HI : i∈(permute F e).frozen := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (FrozenCoordinateOrdering.permutation_mem_iff F.frozen i).mpr hi⟩
    exact HY.2 i HI
  have Hroot:=IntegralMixedCriticalRoot.root x' hm r φ z HF HY.1 (fun i hi=>?G)
  · have HE : z (ClearedCoordinateCritical.freeIndex r.offset.val (IntegralMixedCriticalRoot.fit r).le
        (IntegralMixedCriticalRoot.coordinate r))=y j := by
      have HI:=pointRule_index F g hg j hj
      exact (congrArg (fun a=>y (e a)) HI).trans (congrArg y (e.apply_symm_apply j))
    rw [HE] at Hroot
    exact Hroot
  case G =>
    let k:=ClearedCoordinateCritical.freeIndex r.offset.val (IntegralMixedCriticalRoot.fit r).le i
    have HK : e k∉F.frozen := by
      intro hk
      have HL:=(FrozenCoordinateOrdering.permutation_mem_iff F.frozen k).mp hk
      change F.frozen.card+i.val<F.frozen.card at HL
      omega
    have Hkj : e k≠g := by
      intro he
      have HE : e (ClearedCoordinateCritical.freeIndex r.offset.val (IntegralMixedCriticalRoot.fit r).le
          (IntegralMixedCriticalRoot.objective r))=g := by
        rw [pointRule_objective F g hg j hj]
        exact (congrArg e (coordinateRule_index F g hg)).trans (e.apply_symm_apply g)
      have HF:=e.injective (he.trans HE.symm)
      have HV:=congrArg Fin.val HF
      apply hi
      apply Fin.ext
      change F.frozen.card+i.val=F.frozen.card+(IntegralMixedCriticalRoot.objective r).val at HV
      omega
    rw [IntegralMixedCoordinateRename.derivative_eval]
    have HZ : z ∘ e.symm=y := by funext a; exact congrArg y (e.apply_symm_apply a)
    rw [HZ]
    exact hgrad (e k) HK Hkj

def retained (F : Frame n) : Frame n := {F with heights:=fun i=>later (F.heights i)}

theorem slice_retained {k : ℕ} (F : Frame n) (values : Fin k→ℝ) (a : ℝ) :
    slice P (retained F) (Fin.cons a values)=slice P F values := by
  ext y
  simp only [slice,retained,evaluate_later]

noncomputable def pointScalarState [Fintype ι] (x : State P S B m ι) (hm : m≤S)
    (F : Frame n) (g : Fin (n+1)) (hg : g∉F.frozen) (j : Fin (n+1)) (hj : j∉F.frozen) :
    State P S B (m+1) (ι⊕Unit) :=
  reframe (relativeScalarStep (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen))
    hm (pointRule F g hg j hj)) P x.critical_cap

theorem pointScalarState_native_prefix [Fintype ι] (x : State P S B m ι) (hm : m≤S)
    (F : Frame n) (g : Fin (n+1)) (hg : g∉F.frozen) (j : Fin (n+1)) (hj : j∉F.frozen) :
    (pointScalarState x hm F g hg j hj).sampler.scalarPrefix=
      (criticalStep (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen))
        hm (pointRule F g hg j hj)).sampler.scalarPrefix := rfl

theorem pointScalarState_native_bank [Fintype ι] (x : State P S B m ι) (hm : m≤S)
    (F : Frame n) (g : Fin (n+1)) (hg : g∉F.frozen) (j : Fin (n+1)) (hj : j∉F.frozen) :
    (pointScalarState x hm F g hg j hj).bank=
      (criticalStep (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen))
        hm (pointRule F g hg j hj)).bank := rfl

theorem retain_point_coordinate [Fintype ι] (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n)
    (g : Fin (n+1)) (hg : g∉F.frozen) (j : Fin (n+1)) (hj : j∉F.frozen)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=
      z (x.sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : Fin (n+1)→ℝ) (ha : a∈slice P F values)
    (hgrad : ∀ i,i∉F.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) a=0) :
    let born:=pointScalarState x hm F g hg j hj
    ∃ w : (ι⊕Unit)→ℝ,∃ ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) w=0) ∧
      (∀ i,w (Sum.inl i)=z i) ∧ ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
      (∀ i,ψ (born.sampler.scalarPrefix.basis.generator i)=
        w (born.sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) (m+1) i) ∧
      (∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons (a j) values : Fin (m+1)→ℝ) i) ∧
      actualSlice born ψ (retained F)=actualSlice x φ F := by
  have Hroot:=point_coordinate_root x hm φ F g hg j hj values H a ha hgrad
  obtain ⟨w,ψ,hw,hold,hψ,Hnew⟩:=relativeScalar_real_extend_recover
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen)) hm (pointRule F g hg j hj)
    z hz φ hφ values H (a j) Hroot
  have HR : ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ := by
    apply x.sampler.scalarPrefix.basis.algHom_ext
    intro i
    have HI:=hψ i.succ
    change ψ (AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator i))=
      w (Sum.inl (x.sampler.scalar i))^UniformIntegralPowerSchedule.weights S (2^B) (m+1) i.succ at HI
    rw [UniformIntegralPowerSchedule.old,hold] at HI
    exact HI.trans (hφ i).symm
  refine ⟨w,ψ,hw,hold,HR,hψ,Hnew,?_⟩
  rw [actualSlice_eq (pointScalarState x hm F g hg j hj) ψ _ (Fin.cons (a j) values) Hnew,
    actualSlice_eq x φ F values H]
  exact slice_retained F values (a j)

end LeanCanny.Geometry.IntegralMixedFrozenFrame
