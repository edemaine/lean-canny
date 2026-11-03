/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPrefixFrame
public import LeanCanny.Geometry.IntegralMixedCriticalReadback
/-! # Literal original-frame readback for a prefix-frozen critical block

All equations use the actual parent clearing denominator. Prefix ordering
identifies the physical coordinates without transporting a sampler.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem PrefixFrozen.point_readback (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (HP : PrefixFrozen F)
    (g j : Fin (n+1)) (hg : g∉F.frozen) (hj : j∉F.frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : Fin (n+1)→ℝ)
    (ha : IntegralMixedCriticalReadback.CriticalPoint x hm (pointRule F g hg j hj) φ a) :
    a∈slice P F values ∧
    ∀i,i∉F.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) a=0 :=by
  let r:=pointRule F g hg j hj
  have HR (i : Fin (n+1)) : r.heights i=F.heights i:=by
    change F.heights (FrozenCoordinateOrdering.permutation F.frozen i)=F.heights i
    rw [HP.permutation]
    rfl
  have HS (i : Fin (n+1)) : r.scales i=F.scales i:=by
    change F.scales (FrozenCoordinateOrdering.permutation F.frozen i)=F.scales i
    rw [HP.permutation]
    rfl
  have HG : (data x hm r).free=g:=by
    apply Fin.ext
    change F.frozen.card+(((FrozenCoordinateOrdering.permutation F.frozen).symm g).val-F.frozen.card)%
      (n-F.frozen.card+1)=g.val
    rw [HP.permutation]
    have HB:=g.isLt
    have HN : ¬g.val<F.frozen.card:=fun h=>hg ((HP g).mpr h)
    rw [Nat.mod_eq_of_lt (by change g.val-F.frozen.card<n-F.frozen.card+1; omega)]
    change F.frozen.card+(g.val-F.frozen.card)=g.val
    omega
  refine ⟨⟨ha.1,?_⟩,?_⟩
  · intro i hi
    have HE:=ha.2.1 i ((HP i).mp hi)
    change ((commonDenominator x*r.scales i:ℤ):ℝ)*a i=φ (expression x (r.heights i)) at HE
    rw [HS,HR] at HE
    exact (constraint_iff x φ F values H a i).mp HE
  · intro i hi hne
    apply ha.2.2 i
    · change F.frozen.card ≤ i.val
      have HN : ¬i.val<F.frozen.card:=fun h=>hi ((HP i).mpr h)
      omega
    · exact fun he=>hne (he.trans HG)

end LeanCanny.Geometry.IntegralMixedFrozenFrame
