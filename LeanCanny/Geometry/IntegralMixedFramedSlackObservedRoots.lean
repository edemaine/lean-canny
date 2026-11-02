/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFramedSlackPolynomialRootsAt
public import LeanCanny.Algebra.IntegralMixedFramedSlackRootSource

/-! # One old interpretation supplies both roots of the literal native sources -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedSlackObservedRoots
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedSlackMatrixBits (elementAt commonAt)
open IntegralMixedFramedClearedMatrixBits (family)
open IntegralMixedFramedSlackRootBits (sphereSource regularSource)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem roots (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (key : List Bool) (N R : List Bool→ℕ) (m r E b : ℕ) (d L K : List Bool→ℕ)
    (hn : N key=m) (hr : R key=r) (hd : d key=BoundedZeroSource.powerDegree E)
    (hl : L key=BoundedRegularSource.regularizationExponent m E b r)
    (hk : K key=BoundedZeroSource.penaltyExponent m E r)
    (q : MvPolynomial (Fin m) ℤ) (a : BoundedZeroSource.Bounded q r) (p : Fin m→ℝ)
    (hp : ∀i,a.val i=p i)
    (hx : ∃φ : ((family P D H).state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀i : Fin m,φ (elementAt P D H key (m-i.val))=(commonAt P D H key : ℝ)*p i) :
    ((sphereSource P D H s hs N R).polynomial key).eval₂ (Int.castRingHom ℝ)
        (BoundedRegularSource.sphereSlack q r a)=0 ∧
      ((regularSource P D H s hs N d R L K).polynomial key).eval₂ (Int.castRingHom ℝ)
        (BoundedRegularSource.regularSlack q E b r a).re=0 := by
  obtain ⟨φ,hφ⟩:=hx
  have HV : ∀i : Fin m,φ (elementAt P D H key (m-i.val))=(commonAt P D H key : ℝ)*a.val i :=
    fun i=>(hφ i).trans (congrArg (fun v : ℝ=>(commonAt P D H key : ℝ)*v) (hp i).symm)
  exact ⟨IntegralMixedFramedSlackPolynomialRootsAt.sphere_root P D H key N R m r hn hr φ q a HV,
    IntegralMixedFramedSlackPolynomialRootsAt.regular_root P D H key N R m r hn hr φ q a HV E b d L K hd hl hk⟩

end LeanCanny.Geometry.IntegralMixedFramedSlackObservedRoots
