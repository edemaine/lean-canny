/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowTransport
public import LeanCanny.Algebra.IntegralMixedFramedRootPullback
/-! # Full physical rows survive honest caller-modulus root augmentation -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalRowPullback
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan commands prefixLength)
open IntegralMixedFramedPhysicalRowTransport
open IntegralMixedFramedRootPullback (parameters plan key)
open IntegralMixedFramedPhysicalIndex (arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

 theorem countAt_pullback (P : Parameters) (D : Plan P) (project : List Bool→List Bool) (extra : List Bool→ℕ)
    (root : List Bool) (b : ℕ) :
    countAt (parameters P project extra) (plan P D project extra) root b=countAt P D (project root) b :=rfl

theorem rowAt_pullback (P : Parameters) (D : Plan P) (project : List Bool→List Bool) (extra : List Bool→ℕ)
    (root : List Bool) (b : ℕ) (hb : b≤P.cap (project root)+1) (r : ℕ) :
    rowAt (parameters P project extra) (plan P D project extra) root b hb r=rowAt P D (project root) b hb r :=rfl

theorem count_pullback (P : Parameters) (D : Plan P) (project : List Bool→List Bool) (extra : List Bool→ℕ)
    (q : List Bool) :
    arity (commands (parameters P project extra) (plan P D project extra) q)=
      arity (commands P D (key project q)) := by
  rw [count_view,count_view,countAt_pullback,IntegralMixedFramedRootPullback.key_root,
    IntegralMixedFramedRootPullback.key_prefix]

theorem row_pullback (P : Parameters) (D : Plan P) (project : List Bool→List Bool) (extra : List Bool→ℕ)
    (q : List Bool) (r : ℕ) :
    keyRow (parameters P project extra) (plan P D project extra) q r=keyRow P D (key project q) r := by
  rw [keyRow,rowAt_pullback,keyRow]
  exact rowAt_congr P D _ _ _ _ _ _ (IntegralMixedFramedRootPullback.key_root project q).symm
    (IntegralMixedFramedRootPullback.key_prefix P project extra q).symm r

private theorem poly_heq {a b : ℕ} (h : a=b) (p : MvPolynomial (Fin a) ℤ) (q : MvPolynomial (Fin b) ℤ)
    (hp : MvPolynomial.rename Fin.val p=MvPolynomial.rename Fin.val q) : HEq p q := by
  cases h
  exact heq_of_eq (MvPolynomial.rename_injective Fin.val Fin.val_injective hp)

theorem indexed_pullback (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool→List Bool) (extra : List Bool→ℕ)
    (Jnew : IntegralMixedFramedHistoryFamilyBits.Data (parameters P project extra) (plan P D project extra))
    (q : List Bool) (i : Fin (arity (commands (parameters P project extra) (plan P D project extra) q))) :
    HEq (indexedRow (parameters P project extra) (plan P D project extra) Jnew q i)
      (indexedRow P D J (key project q) (Fin.cast (count_pullback P D project extra q) i)) := by
  have H:=row_pullback P D project extra q i.val
  rw [keyRow_family _ _ Jnew q i.val i.isLt,keyRow_family P D J (key project q) i.val
    (i.isLt.trans_eq (count_pullback P D project extra q))] at H
  exact poly_heq (count_pullback P D project extra q) _ _ H

private theorem native_coefficient_heq {a b : ℕ} (h : a=b)
    (p : MvPolynomial (Fin a) ℤ) (q : MvPolynomial (Fin b) ℤ) (hp : HEq p q) (V t : ℕ) :
    p.coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) V t)=
      q.coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) V t) :=by
  cases h
  cases hp
  rfl

theorem coefficient_pullback (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool→List Bool) (extra : List Bool→ℕ)
    (Jnew : IntegralMixedFramedHistoryFamilyBits.Data (parameters P project extra) (plan P D project extra))
    (q : List Bool) (i : Fin (arity (commands (parameters P project extra) (plan P D project extra) q))) (V t : ℕ) :
    (indexedRow (parameters P project extra) (plan P D project extra) Jnew q i).coeff
      (FixedWidthPolynomial.nativeExponent (Equiv.refl _) V t)=
    (indexedRow P D J (key project q) (Fin.cast (count_pullback P D project extra q) i)).coeff
      (FixedWidthPolynomial.nativeExponent (Equiv.refl _) V t) :=
  native_coefficient_heq (count_pullback P D project extra q) _ _
    (indexed_pullback P D J project extra Jnew q i) V t

end LeanCanny.Algebra.IntegralMixedFramedPhysicalRowPullback
