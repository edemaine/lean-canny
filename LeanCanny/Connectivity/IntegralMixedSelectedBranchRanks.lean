/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateOrder
public import LeanCanny.Geometry.FiniteImageRank
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSectionCode

/-! # Distinct coordinate ranks of actual selected critical branches persist

Only the values of the supplied finite family are counted, with repetitions
counted once. The actual selected PSC cuts prove every needed comparison.
No symbolic integer norm polynomial or branch-order premise is substituted.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedBranchRanks
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι J : Type} [Fintype J] [LinearOrder J]

noncomputable def rank {K : Type} (curve : J→K→ℝ) (j : J) (i : K) : ℕ :=
  FiniteImageRank.rank Finset.univ (fun k=>curve k i) (curve j i)

theorem rank_injective {K : Type} (curve : J→K→ℝ) (Hcurve : Function.Injective curve) :
    Function.Injective (rank curve) := by
  intro j k H
  apply Hcurve
  funext i
  exact (FiniteImageRank.rank_eq_iff Finset.univ (fun l=>curve l i) j k (Finset.mem_univ _) (Finset.mem_univ _)).mp (congrFun H i)

theorem rank_le {K : Type} (curve : J→K→ℝ) (j : J) (i : K) : rank curve j i≤Fintype.card J := by
  simpa only [rank,Finset.card_univ] using FiniteImageRank.rank_le Finset.univ (fun k=>curve k i) (curve j i)

theorem rank_eq (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (choice : Free r→Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r))
    (hc : ∀ i,IntegralMixedCoordinateSquarefree.Valid x hm r i φ (choice i)) {a b : ℝ}
    (havoid : ∀ t∈Ioo a b,∀ i,(IntegralMixedCoordinateSquarefree.exceptional x hm r i (choice i)).eval₂ φ.toRingHom t≠0)
    (f : J→C(Ioo a b,Free r→ℝ))
    (hf : ∀ j t i,(selected x hm r i φ).eval₂ (Polynomial.evalRingHom t.val) (f j t i)=0)
    (j : J) (s t : Ioo a b) : rank (fun k=>f k s) j=rank (fun k=>f k t) j := by
  funext i
  apply FiniteImageRank.rank_eq_of_comparisons
  · intro k _ l _
    exact (IntegralMixedSelectedCoordinateOrder.comparison x hm r φ i (choice i) (hc i)
      (fun t ht=>havoid t ht i) (f k) (f l) (fun t=>hf k t i) (fun t=>hf l t i) s t).1
  · intro k _
    exact (IntegralMixedSelectedCoordinateOrder.comparison x hm r φ i (choice i) (hc i)
      (fun t ht=>havoid t ht i) (f k) (f j) (fun t=>hf k t i) (fun t=>hf j t i) s t).2

noncomputable def word (r : Rule n) (W : ℕ) (curve : J→Free r→ℝ) (j : J) : List Bool :=
  FixedWidthNatVector.encode (n+1) W
    (fun k=>if hk : k<n-r.critical.offset.val+1 then rank curve j ⟨k,hk⟩ else 0)

theorem word_length (r : Rule n) (W : ℕ) (curve : J→Free r→ℝ) (j : J) :
    (word r W curve j).length=(n+1)*W := FixedWidthNatVector.length_encode _ _ _

theorem word_digit (r : Rule n) (W : ℕ) (curve : J→Free r→ℝ) (j : J) (i : Free r)
    (Hfit : rank curve j i<2^W) :
    Nat.fromBitsLE (((word r W curve j).drop (i.val*W)).take W)=rank curve j i := by
  have HI : i.val<n+1:=by have H:=i.isLt; omega
  have HD:=FixedWidthNatVector.decode_block (n+1) W
    (fun k=>if hk : k<n-r.critical.offset.val+1 then rank curve j ⟨k,hk⟩ else 0)
    i.val HI (by simpa only [dite_eq_left i.isLt] using Hfit)
  simpa only [word,dite_eq_left i.isLt] using HD

theorem word_injective (r : Rule n) (W : ℕ) (curve : J→Free r→ℝ) (Hcurve : Function.Injective curve)
    (Hfit : ∀ j i,rank curve j i<2^W) : Function.Injective (word r W curve) := by
  intro j k Hword
  apply rank_injective curve Hcurve
  funext i
  rw [←word_digit r W curve j i (Hfit j i),←word_digit r W curve k i (Hfit k i),Hword]

theorem word_eq (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (choice : Free r→Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r))
    (hc : ∀ i,IntegralMixedCoordinateSquarefree.Valid x hm r i φ (choice i)) {a b : ℝ}
    (havoid : ∀ t∈Ioo a b,∀ i,(IntegralMixedCoordinateSquarefree.exceptional x hm r i (choice i)).eval₂ φ.toRingHom t≠0)
    (f : J→C(Ioo a b,Free r→ℝ))
    (hf : ∀ j t i,(selected x hm r i φ).eval₂ (Polynomial.evalRingHom t.val) (f j t i)=0)
    (W : ℕ) (j : J) (s t : Ioo a b) : word r W (fun k=>f k s) j=word r W (fun k=>f k t) j := by
  unfold word
  congr 1
  funext i
  split_ifs with hi
  · exact congrFun (rank_eq x hm r φ choice hc havoid f hf j s t) ⟨i,hi⟩
  · rfl

end LeanCanny.Connectivity.IntegralMixedSelectedBranchRanks
