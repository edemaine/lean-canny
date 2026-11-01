/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedSweepRows
public import LeanCanny.Algebra.IntegralMixedCoordinateSquarefree
public import LeanCanny.Algebra.RelativeAffineGridValueGram

/-! # The actual relative equation-value certificate of a mixed sweep

The coordinate grid is the constructed relative spatial annihilator grid.
Each tested polynomial is the cleared ORIGINAL source or free gradient row.
The complete reciprocal Gram certificate annihilates its value at every
grid point, including extraneous combinations and multiple roots. Its
nonzero selected component follows from the actual coordinate degree.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGridValue
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedCoordinateSquarefree Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def polynomial (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) : Polynomial (Polynomial x.sampler.scalarPrefix.carrier) :=
  RelativeAffineGridValueGram.annihilator (coordinate x hm r) (IntegralMixedSweepRows.row x hm r i)
    (fun _ => coordinateDegree P r) P.degree

def width (P : SpatialSource n) (r : Rule n) :=
  RelativeAffineGridValueGram.width (fun _ : Fin (n - r.critical.offset.val + 1) => coordinateDegree P r) P.degree

def dimension (P : SpatialSource n) (r : Rule n) :=
  RelativeProjectiveValueGram.dimension (n - r.critical.offset.val + 1) (width P r)

theorem coordinate_degree_eq (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    (coordinate x hm r j).natDegree = coordinateDegree P r :=
  Nat.le_antisymm (coordinate_degree x hm r j)
    ((selected_degree x hm r j φ).symm ▸ Polynomial.natDegree_map_le)

theorem evaluation_eq (x : State P S B m ι) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) :
    evaluation x φ t = Polynomial.eval₂RingHom φ.toRingHom t := by
  apply RingHom.ext
  intro q
  change (q.map φ.toRingHom).eval t = q.eval₂ φ.toRingHom t
  exact Polynomial.eval_map _ _

theorem complex_leading_nonzero (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) :
    (Complex.ofRealHom.comp (Polynomial.eval₂RingHom φ.toRingHom t)) (coordinate x hm r j).leadingCoeff ≠ 0 := by
  have HD : ((coordinate x hm r j).map (evaluation x φ t)).natDegree = coordinateDegree P r := by
    have H := specialized_degree x hm r j φ t
    rw [selected, Polynomial.map_map] at H
    convert H using 1
    rfl
  have HP : (coordinate x hm r j).map (evaluation x φ t) ≠ 0 := by
    intro HZ
    rw [HZ, Polynomial.natDegree_zero] at HD
    have HK : 0 < coordinateDegree P r := pow_pos (Nat.two_pow_pos _) _
    omega
  have HL := Polynomial.leadingCoeff_ne_zero.mpr HP
  rw [Polynomial.leadingCoeff, HD, Polynomial.coeff_map, evaluation_eq] at HL
  rw [Polynomial.leadingCoeff, coordinate_degree_eq x hm r j φ]
  change Complex.ofReal ((Polynomial.eval₂RingHom φ.toRingHom t)
    ((coordinate x hm r j).coeff (coordinateDegree P r))) ≠ 0
  exact fun H => HL (Complex.ofReal_eq_zero.mp H)

theorem selected_ne_zero (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    (polynomial x hm r i).map (Polynomial.mapRingHom φ.toRingHom) ≠ 0 := by
  exact RelativeAffineGridValueGram.selected_ne_zero (coordinate x hm r) (IntegralMixedSweepRows.row x hm r i)
    (fun _ => coordinateDegree P r) P.degree (fun j => coordinate_degree_eq x hm r j φ)
    (fun _ => pow_pos (Nat.two_pow_pos _) _) (by have H := P.degree_two; omega) φ.toRingHom 0
    (fun j => complex_leading_nonzero x hm r j φ 0)

theorem root (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (t : ℝ) (z : Fin (n - r.critical.offset.val + 1) → ℝ)
    (hz : ∀ j, (selected x hm r j φ).eval₂ (Polynomial.evalRingHom t) (z j) = 0) :
    ((polynomial x hm r i).map (Polynomial.mapRingHom φ.toRingHom)).eval₂ (Polynomial.evalRingHom t)
      ((IntegralMixedSweepRows.row x hm r i).eval₂ (evaluation x φ t) z) = 0 := by
  rw [Polynomial.eval₂_map]
  apply RelativeAffineGridValueGram.root (coordinate x hm r) (IntegralMixedSweepRows.row x hm r i)
    (fun _ => coordinateDegree P r) P.degree (coordinate_degree x hm r) (IntegralMixedSweepRows.row_degree x hm r i)
    (evaluation x φ t) z
  intro j
  have H := hz j
  rw [selected, Polynomial.eval₂_map] at H
  exact H

theorem degree_le (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) : (polynomial x hm r i).natDegree ≤ dimension P r + 1 :=
  RelativeAffineGridValueGram.degree_le _ _ _ _

theorem coefficient_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (k : ℕ) :
    ((polynomial x hm r i).coeff k).natDegree ≤ dimension P r * (parameterDegree P.degree r + P.degree) := by
  apply RelativeAffineGridValueGram.inner_degree
  · intro j v
    exact (coordinate_coefficient_degree x hm r j v).trans (Nat.le_add_right _ _)
  · intro v
    exact (IntegralMixedSweepRows.row_parameter_degree x hm r i v).trans (Nat.le_add_left _ _)

end LeanCanny.Algebra.IntegralMixedGridValue
