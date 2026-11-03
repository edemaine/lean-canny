/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedJointGeneralSlab
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealRegular
/-! # Each regular midpoint component supplies the actual physical anchor witness

This reads back the source/gradient rows of the actual selected fiber. The
proper-fiber critical sampling theorem constructs the witness on the SAME
old hom, without lifting an arbitrary coordinate annihilator root.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem selected_physical_gradients (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (g : Fin (n+1)) (hg : g∉F.frozen) (t : ℝ) (a : Fin (n+1)→ℝ)
    (ha : (a ∘ FrozenCoordinateOrdering.permutation F.frozen)∈IntegralMixedSelectedPhysicalFiber.physical
      (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation F.frozen))
      hm (sweep x F h hh g hg) φ t) :
    ∀ i,i∉F.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) a=0 :=by
  intro i hi hig
  let r:=sweep x F h hh g hg
  let e:=FrozenCoordinateOrdering.permutation F.frozen
  let j:=freeCoordinate F i hi
  have HK : e (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j)=i:=by
    change e (ClearedCoordinateCritical.freeIndex F.frozen.card _ (freeCoordinate F i hi))=i
    rw [freeCoordinate_readback]
    exact e.apply_symm_apply i
  have HJ : j≠objective r:=by
    intro HE
    have HV:=congrArg (fun k=>e (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le k)) HE
    rw [HK] at HV
    exact hig (HV.trans (objective_physical x F h hh g hg))
  have HG:=ha.2 j
  unfold IntegralMixedSweepRows.integerRow at HG
  rw [ite_eq_right HJ,IntegralMixedCoordinateRename.derivative_eval] at HG
  have HP : (a ∘ e) ∘ e.symm=a:=by
    funext k
    exact congrArg a (e.apply_symm_apply k)
  change (MvPolynomial.pderiv (e (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j))
    (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
      (Int.castRingHom ℝ) ((a ∘ e) ∘ e.symm)=0 at HG
  rw [HP,HK] at HG
  exact HG

theorem exists_joint_midpoint_witness (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a b : ℝ) (havoid : (a+b)/2∉realCriticalValues P (line F h) values h)
    (y : Fin (n+1)→ℝ) (hy : y∈slice P F values) (hymid : y h=(a+b)/2)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y)) :
    ∃ point : Fin (n+1)→ℝ,
      JoinedIn (slice P F values∩{z | z h=(a+b)/2}) y point ∧
      point∈slice P F values ∧ point h=(a+b)/2 ∧
      ∀ i,i∉(line F h).frozen→i≠g→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
          (Int.castRingHom ℝ) point=0 :=by
  have HY : y∈shiftedSlice P (line F h) values h ((a+b)/2):=by
    rw [line_slice P F h hh HF values]
    exact ⟨hy,hymid⟩
  obtain ⟨point,Hpath,Hphysical⟩:=exists_path_sample_of_realCriticalValues x hm φ (line F h) h
    (Finset.mem_insert_self h F.frozen) g hg values H ((a+b)/2) havoid y HY hp
  have HM:=Hpath.target_mem
  rw [line_slice P F h hh HF values] at Hpath HM
  exact ⟨point,Hpath,HM.1,HM.2,
    selected_physical_gradients x hm φ (line F h) h (Finset.mem_insert_self h F.frozen) g hg ((a+b)/2) point Hphysical⟩

end LeanCanny.Geometry.IntegralMixedFrozenFrame
