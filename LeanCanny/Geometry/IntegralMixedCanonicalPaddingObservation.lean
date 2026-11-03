/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCanonicalPaddingRealization
public import LeanCanny.Algebra.IntegralMixedFramedRunObservation
public import LeanCanny.Geometry.IntegralMixedFullBankPoint
/-! # Canonical padding retains every old natural physical column

The initial witness is one actual root of the old full row system. Padding
preserves its entire tuple, rather than only its retained bank values.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedCanonicalPadding
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedPhysicalPersistence IntegralMixedFramedRunObservation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n S B :ℕ} {Q :SpatialSource n}

theorem run_observation (initial :State Q S B 0 (Fin 0))
    (cs :List (Instruction n B)) (ho :cs.length≤S+1) (P :SpatialSource n)
    (hP :PurePowerReductionBounds.dimension (n+1) P.degree≤2^B) (hn :0<n)
    (charge :ℕ) (hd :P.degree=BoundedZeroSource.powerDegree charge)
    (hc :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z :ℕ→ℝ) (hz :(ofCommands initial cs ho).Roots z)
    (p :Fin (n+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂
      (Int.castRingHom ℝ) p=0)
    (hg :∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0) (k :ℕ)
    (room :(List.replicate k (IntegralMixedCanonicalPaddingSeed.instruction P hP)++cs).length≤S+1) :
    let newer:=List.replicate k (IntegralMixedCanonicalPaddingSeed.instruction P hP)
    ∃y :ℕ→ℝ,
      (ofCommands initial (newer++cs) room).Roots y ∧
      (∀i,i<arity cs→y i=z i) ∧
      ∀i :Fin (newer++cs).length,
        (ofCommands initial (newer++cs) room).point y i.val=
          values (p 0) ((ofCommands initial cs ho).point z) k i.val :=by
  let old:=run initial cs ho
  let raw :Index (Fin 0) cs→ℝ:=fun i=>z (enumerate cs i).val
  have HR :∀i,(old.sampler.rows i).eval₂ (Int.castRingHom ℝ) raw=0:=
    (roots_actual initial cs ho z).mp hz
  have HC :Canonical old:=run_canonical initial (fun i=>Fin.elim0 i) cs ho
  obtain ⟨φ,hφ,hvalues⟩:=IntegralMixedFullBankPoint.interprets old HC raw HR
  have HV :∀i,φ (old.bank.numerator i)/(old.bank.denominator i:ℝ)=
      (ofCommands initial cs ho).point z i.val:=by
    intro i
    exact (hvalues i).trans (point_actual initial cs ho z i).symm
  let newer:=List.replicate k (IntegralMixedCanonicalPaddingSeed.instruction P hP)
  obtain ⟨y,ψ,hy,hold,hgen,hvals⟩:=run_exists initial cs ho P hP hn charge hd hc
    raw HR φ hφ ((ofCommands initial cs ho).point z) HV p hp hg k room
  let nat :ℕ→ℝ:=IntegralMixedFramedBankObservation.extend (y∘(enumerate (newer++cs)).symm)
  have HN (i :Index (Fin 0) (newer++cs)) :nat (enumerate (newer++cs) i).val=y i:=by
    dsimp only [nat,IntegralMixedFramedBankObservation.extend]
    rw [dite_eq_left (enumerate (newer++cs) i).isLt]
    exact congrArg y ((enumerate (newer++cs)).symm_apply_apply i)
  have HE :(fun i=>nat (enumerate (newer++cs) i).val)=y:=funext HN
  refine ⟨nat,(roots_actual initial (newer++cs) room nat).mpr ?_,?_,?_⟩
  · rw [HE]
    exact hy
  · intro i hi
    let a:=(enumerate cs).symm ⟨i,hi⟩
    have HA :(enumerate (newer++cs) (embed newer cs a)).val=i:=
      (enumerate_embed newer cs a).trans (congrArg Fin.val ((enumerate cs).apply_symm_apply ⟨i,hi⟩))
    exact (congrArg nat HA.symm).trans ((HN _).trans ((hold a).trans
      (congrArg z (congrArg Fin.val ((enumerate cs).apply_symm_apply ⟨i,hi⟩)))))
  · intro i
    have HFINAL :Canonical (run initial (newer++cs) room):=
      run_canonical initial (fun j=>Fin.elim0 j) (newer++cs) room
    have HPOINT:=point_actual initial (newer++cs) room nat i
    have HG :∀j,ψ ((run initial (newer++cs) room).sampler.scalarPrefix.basis.generator j)=
        nat (enumerate (newer++cs) ((run initial (newer++cs) room).sampler.scalar j)).val^
          UniformIntegralPowerSchedule.weights S (2^B) (newer++cs).length j:=by
      intro j
      rw [HN]
      exact hgen j
    exact HPOINT.trans ((IntegralMixedCanonicalBankPoint.quotient_eq
      (run initial (newer++cs) room) HFINAL _ ψ HG i).symm.trans (hvals i))

end LeanCanny.Geometry.IntegralMixedCanonicalPadding
