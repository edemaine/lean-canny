/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ClearedCoordinateCriticalBounds
/-! # Frozen values determine the actual cleared coordinate system

When the free block fills the remaining coordinates, unused free-height
fields do not affect the source rows, gradients or coordinate annihilators.
-/
@[expose] public section
namespace LeanCanny.Algebra.ClearedCoordinateFrozenCongruence
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ} {R : Type*} [CommRing R]

theorem specialize (D : ℕ) (q : R) (H K : ℕ→R) (offset : ℕ)
    (hfit : offset+(k+1)=n+1) (hH : ∀i,i<offset→H i=K i)
    (p : MvPolynomial (Fin (n+1)) R) :
    ClearedCoordinateBlock.specialize D q H offset (k+1) p=
      ClearedCoordinateBlock.specialize D q K offset (k+1) p :=by
  have HC : (fun i : Fin (n+1)=>ClearedCoordinateBlock.coordinate q H offset (k+1) i.val)=
      fun i : Fin (n+1)=>ClearedCoordinateBlock.coordinate q K offset (k+1) i.val:=by
    funext i
    unfold ClearedCoordinateBlock.coordinate
    split_ifs with hi
    · rfl
    · rw [hH i.val (by have :=i.isLt;omega)]
  unfold ClearedCoordinateBlock.specialize
  rw [HC]

theorem frozenPower (D : ℕ) (H K : ℕ→R) (offset : ℕ)
    (hfit : offset+(k+1)=n+1) (hH : ∀i,i<offset→H i=K i) :
    CoordinateBlockSpecialization.frozenPower (n:=n+1) H offset (k+1) D=
      CoordinateBlockSpecialization.frozenPower (n:=n+1) K offset (k+1) D :=by
  unfold CoordinateBlockSpecialization.frozenPower
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rfl
  · rw [hH i.val (by have :=i.isLt;omega)]

theorem lower (D : ℕ) (q : R) (H K : ℕ→R) (offset : ℕ)
    (hfit : offset+(k+1)=n+1) (hH : ∀i,i<offset→H i=K i)
    (p : MvPolynomial (Fin (n+1)) R) (a : R) :
    ClearedCoordinateBlock.lower D q H offset (k+1) p a=
      ClearedCoordinateBlock.lower D q K offset (k+1) p a :=by
  unfold ClearedCoordinateBlock.lower
  rw [specialize D q H K offset hfit hH,frozenPower D H K offset hfit hH]

theorem gradient (D : ℕ) (q : R) (H K : ℕ→R) (offset : ℕ)
    (hfit : offset+(k+1)=n+1) (hH : ∀i,i<offset→H i=K i)
    (p : MvPolynomial (Fin (n+1)) R) (j : Fin (k+1)) :
    ClearedCoordinateCritical.gradientLower D q H offset hfit.le p j=
      ClearedCoordinateCritical.gradientLower D q K offset hfit.le p j :=by
  exact specialize D q H K offset hfit hH _

theorem annihilator (D : ℕ) (q : R) (H K : ℕ→R) (offset : ℕ)
    (hfit : offset+(k+1)=n+1) (hH : ∀i,i<offset→H i=K i)
    (p : MvPolynomial (Fin (n+1)) R) (a : R) (r j : Fin (k+1)) :
    ClearedCoordinateCritical.annihilator D q H offset hfit.le p a r j=
      ClearedCoordinateCritical.annihilator D q K offset hfit.le p a r j :=by
  have HL : ClearedCoordinateCritical.lower D q H offset hfit.le p a r=
      ClearedCoordinateCritical.lower D q K offset hfit.le p a r:=by
    funext i
    unfold ClearedCoordinateCritical.lower
    rw [lower D q H K offset hfit hH]
    have HG : ClearedCoordinateCritical.gradientLower D q H offset hfit.le p=
        ClearedCoordinateCritical.gradientLower D q K offset hfit.le p:=by
      funext l
      exact gradient D q H K offset hfit hH p l
    rw [HG]
  unfold ClearedCoordinateCritical.annihilator
  rw [HL]

end LeanCanny.Algebra.ClearedCoordinateFrozenCongruence
