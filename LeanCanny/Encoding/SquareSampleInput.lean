/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MvCoefficientMass
public import LeanCanny.Algebra.FiniteSourceDegreePreparation
public import LeanCanny.Geometry.PolynomialSystemRegularity

/-! # A native interface for sampling positive square polynomial systems

Coordinate equations are explicit nonzero integer polynomials, with native
coefficient access and a proof that they retain every regular system root.
Canonical queries carry exponent width by word length, so arbitrary query
widths fit the native space bound. Context changes preserve every other field.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleInput
open LeanCanny.Algebra LeanCanny.Computation MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Inputs where
  count : List Bool → ℕ
  degree : List Bool → ℕ
  mass : List Bool → ℕ
  system : (u : List Bool) → Fin (count u) → MvPolynomial (Fin (count u)) ℤ
  count_pos : ∀ u, 0 < count u
  degree_pos : ∀ u, 0 < degree u
  system_degree : ∀ u i, (system u i).totalDegree ≤ degree u
  system_mass : ∀ u i, MvMass.mass (system u i) ≤ 2 ^ mass u
  annihilator : (u : List Bool) → Fin (count u) → Polynomial ℤ
  annDegree : List Bool → ℕ
  annHeight : List Bool → ℕ
  ann_nonzero : ∀ u i, annihilator u i ≠ 0
  ann_degree : ∀ u i, (annihilator u i).natDegree ≤ annDegree u
  ann_height : ∀ u i j, ((annihilator u i).coeff j).natAbs.size ≤ annHeight u
  ann_root : ∀ u (z : Fin (count u) → ℝ), (∀ i, (system u i).eval₂ (Int.castRingHom ℝ) z = 0) →
    (fderiv ℝ (fun x => fun i => (system u i).eval₂ (Int.castRingHom ℝ) x) z).IsInvertible →
    ∀ i, (annihilator u i).eval₂ (Int.castRingHom ℝ) (z i) = 0

def source (q : List Bool) : List Bool := pairFst (pairFst q)
def indexWord (q : List Bool) : List Bool := pairSnd (pairFst q)
def widthWord (q : List Bool) : List Bool := pairFst (pairSnd q)
def rankWord (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def modulusWord (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd q))

def query (u i w r m : List Bool) : List Bool := pair (pair u i) (pair w (pair r m))

def selected (F : Inputs) (u i : List Bool) : Fin (F.count u) :=
  ⟨min (Nat.fromBitsLE i) (F.count u - 1), by have := F.count_pos u; omega⟩

noncomputable def rowValue (F : Inputs) (u i : List Bool) (w : ℕ) (r m : List Bool) : List Bool :=
  MatrixPower.residueBits (((F.system u (selected F u i)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (F.count u))) w (Nat.fromBitsLE r)) : ℤ) :
      ZMod (Nat.fromBitsLE m + 1))

noncomputable def annValue (F : Inputs) (u i r m : List Bool) : List Bool :=
  MatrixPower.residueBits (((F.annihilator u (selected F u i)).coeff (Nat.fromBitsLE r) : ℤ) :
    ZMod (Nat.fromBitsLE m + 1))

noncomputable def rowCoefficient (F : Inputs) (q : List Bool) : List Bool :=
  rowValue F (source q) (indexWord q) (widthWord q).length (rankWord q) (modulusWord q)

noncomputable def annCoefficient (F : Inputs) (q : List Bool) : List Bool :=
  annValue F (source q) (indexWord q) (rankWord q) (modulusWord q)

structure Inputs.Access (F : Inputs) : Prop where
  count : UnaryFn F.count
  degree : BinaryFn F.degree
  mass : BinaryFn F.mass
  annDegree : BinaryFn F.annDegree
  annHeight : BinaryFn F.annHeight
  row : SpaceFunction (rowCoefficient F)
  annihilator : SpaceFunction (annCoefficient F)

noncomputable def comp (F : Inputs) (f : List Bool → List Bool) : Inputs where
  count := F.count ∘ f
  degree := F.degree ∘ f
  mass := F.mass ∘ f
  system u := F.system (f u)
  count_pos u := F.count_pos (f u)
  degree_pos u := F.degree_pos (f u)
  system_degree u := F.system_degree (f u)
  system_mass u := F.system_mass (f u)
  annihilator u := F.annihilator (f u)
  annDegree := F.annDegree ∘ f
  annHeight := F.annHeight ∘ f
  ann_nonzero u := F.ann_nonzero (f u)
  ann_degree u := F.ann_degree (f u)
  ann_height u := F.ann_height (f u)
  ann_root u := F.ann_root (f u)

end LeanCanny.Encoding.SquareSampleInput
