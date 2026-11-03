/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankObservationShift
public import LeanCanny.Encoding.IntegralFramedPhysicalOlderParent
/-! # Older bank values are observations of the same full vertex

Every saved prefix uses its original powers and integer denominators.
Neither old labels nor algebraic-root choices are supplied independently.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalBankShift
open LeanCanny.Algebra LeanCanny.Geometry IntegralCriticalHistoryTask UniformIntegralPowerSchedule
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀q,0<(family P D H).birth (key q))
  (q w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hpos) q w)
  (old : List Bool) (hroot : pairFst (key q)=pairFst old)
  (hfit : (family P D H).birth old≤(family P D H).birth (key q))

include hroot in
theorem values_of_interpretation
    (φ : ((family P D H).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (((family P D H).state old).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hpos q w hv (embed hfit i)^
        weights ((family P D H).cap old) (2^(family P D H).width old) ((family P D H).birth old) i)
    (i : Fin ((family P D H).birth old)) :
    φ (((family P D H).state old).bank.numerator i)/(((family P D H).state old).bank.denominator i:ℝ)=
      IntegralFramedPhysicalSquare.point P D H L F C hs key hpos q w hv (embed hfit i) :=by
  have HO:=IntegralMixedCanonicalBankPoint.quotient_eq ((family P D H).state old)
    (IntegralMixedFramedHistoryFamilyBits.family_canonical P D H old)
    (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hpos q w hv∘embed hfit) φ hφ i
  exact HO.trans (IntegralMixedFramedBankObservationShift.point P D H old (key q) hroot hfit
    (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hpos q w hv) i)

include hroot in
theorem exists_interpretation_values :
    ∃φ : ((family P D H).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ (((family P D H).state old).sampler.scalarPrefix.basis.generator i)=
        IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hpos q w hv (embed hfit i)^
          weights ((family P D H).cap old) (2^(family P D H).width old) ((family P D H).birth old) i) ∧
      ∀i,φ (((family P D H).state old).bank.numerator i)/(((family P D H).state old).bank.denominator i:ℝ)=
        IntegralFramedPhysicalSquare.point P D H L F C hs key hpos q w hv (embed hfit i) :=by
  obtain ⟨φ,hφ⟩:=IntegralFramedPhysicalOlderParent.exists_interpretation P D H L F C hs key hpos q w hv old hroot hfit
  exact ⟨φ,hφ,values_of_interpretation P D H L F C hs key hpos q w hv old hroot hfit φ hφ⟩

variable (next : List Bool) (hnroot : pairFst (key q)=pairFst next)
  (hnfit : (family P D H).birth next≤(family P D H).birth (key q))
  (hstep : (family P D H).birth old≤(family P D H).birth next)

include hroot hnroot in
theorem compatible_values
    (φ : ((family P D H).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (((family P D H).state old).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hpos q w hv (embed hfit i)^
        weights ((family P D H).cap old) (2^(family P D H).width old) ((family P D H).birth old) i)
    (ψ : ((family P D H).state next).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hψ : ∀i,ψ (((family P D H).state next).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hpos q w hv (embed hnfit i)^
        weights ((family P D H).cap next) (2^(family P D H).width next) ((family P D H).birth next) i)
    (i : Fin ((family P D H).birth old)) :
    ψ (((family P D H).state next).bank.numerator (embed hstep i))/
      (((family P D H).state next).bank.denominator (embed hstep i):ℝ)=
        φ (((family P D H).state old).bank.numerator i)/(((family P D H).state old).bank.denominator i:ℝ) :=by
  have HI : embed hnfit (embed hstep i)=embed hfit i:=by
    apply Fin.ext
    dsimp only [embed]
    omega
  exact (values_of_interpretation P D H L F C hs key hpos q w hv next hnroot hnfit ψ hψ (embed hstep i)).trans
    ((congrArg (IntegralFramedPhysicalSquare.point P D H L F C hs key hpos q w hv) HI).trans
      (values_of_interpretation P D H L F C hs key hpos q w hv old hroot hfit φ hφ i).symm)

include hroot hnroot in
theorem compatible_cons
    (φ : ((family P D H).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (((family P D H).state old).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hpos q w hv (embed hfit i)^
        weights ((family P D H).cap old) (2^(family P D H).width old) ((family P D H).birth old) i)
    (ψ : ((family P D H).state next).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hψ : ∀i,ψ (((family P D H).state next).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs key hpos q w hv (embed hnfit i)^
        weights ((family P D H).cap next) (2^(family P D H).width next) ((family P D H).birth next) i)
    (hc : (family P D H).birth old+1=(family P D H).birth next)
    (i : Fin ((family P D H).birth old+1)) :
    ψ (((family P D H).state next).bank.numerator (Fin.cast hc i))/
      (((family P D H).state next).bank.denominator (Fin.cast hc i):ℝ)=
        (Fin.cons (α:=fun _ : Fin ((family P D H).birth old+1)=>ℝ)
          (ψ (((family P D H).state next).bank.numerator (Fin.cast hc 0))/
            (((family P D H).state next).bank.denominator (Fin.cast hc 0):ℝ))
          (fun j=>φ (((family P D H).state old).bank.numerator j)/
            (((family P D H).state old).bank.denominator j:ℝ))) i :=by
  have hstep : (family P D H).birth old≤(family P D H).birth next:=by omega
  refine Fin.cases rfl (fun j=>?_) i
  have HI : Fin.cast hc j.succ=embed hstep j:=by
    apply Fin.ext
    dsimp only [Fin.val_cast,Fin.val_succ,embed]
    omega
  change ψ (((family P D H).state next).bank.numerator (Fin.cast hc j.succ))/_=_
  rw [HI]
  exact compatible_values P D H L F C hs key hpos q w hv old hroot hfit next hnroot hnfit hstep φ hφ ψ hψ j

end LeanCanny.Encoding.IntegralFramedPhysicalBankShift
