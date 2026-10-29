/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SeparablePolynomialThom
public import LeanCanny.Algebra.RationalCoordinateFamily
public import LeanCanny.Algebra.InfinitesimalSignSpace

/-! # Named rational parents with native validity and derivative probes

The actual parent roots form a specified subset of a separable equation's
roots. Every accepted name denotes exactly one such root and its defined
ambient coordinates. Native validity and derivative-sign access are part of
the computation certificate, so ancestor checks cannot become free oracles.
-/

@[expose] public section
namespace LeanCanny.Encoding.NamedRationalParents
open LeanCanny.Algebra LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair pairFst pairSnd

structure Source where
  equation : SeparablePolynomialFamily.Source
  coordinates : RationalCoordinateFamily.Family
  roots : List Bool → Set ℝ
  root_zero : ∀ u theta, theta ∈ roots u → (equation.polynomial u).eval₂ (Int.castRingHom ℝ) theta = 0
  defined : ∀ u theta, theta ∈ roots u → RationalCoordinateFamily.Defined coordinates u theta
  descriptor : (u : List Bool) → {theta : ℝ // theta ∈ roots u} → List Bool
  descriptor_injective : ∀ u, Function.Injective (descriptor u)
  width : List Bool → ℕ
  descriptor_length : ∀ u x, (descriptor u x).length ≤ width u
  derivativeValue : List Bool → List Bool
  derivative_packet : ∀ u x k,
    derivativeValue (pair (pair u (descriptor u x)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign ((SeparablePolynomialThom.polynomial equation u k).eval₂
        (Int.castRingHom ℝ) x.val))

abbrev Root (P : Source) (u : List Bool) := {theta : ℝ // theta ∈ P.roots u}

def language (P : Source) : Language := {q | ∃ x : Root P (pairFst q), P.descriptor (pairFst q) x = pairSnd q}

structure Access (P : Source) : Prop where
  equation : SeparablePolynomialFamily.Access P.equation
  coordinates : RationalCoordinateFamily.Access P.coordinates
  width : UnaryFn P.width
  validity : SpaceDecider (language P)
  derivative : SpaceFunction P.derivativeValue

theorem descriptor_valid (P : Source) (u : List Bool) (x : Root P u) :
    pair u (P.descriptor u x) ∈ language P := by
  generalize hq : pair u (P.descriptor u x) = q
  have hu : pairFst q = u := by rw [← hq, pairFst_pair]
  have hw : pairSnd q = P.descriptor u x := by rw [← hq, pairSnd_pair]
  change ∃ y : Root P (pairFst q), P.descriptor (pairFst q) y = pairSnd q
  rw [hu, hw]
  exact ⟨x, rfl⟩

theorem unique_root (P : Source) (q : List Bool) (hq : q ∈ language P) :
    ∃! x : Root P (pairFst q), P.descriptor (pairFst q) x = pairSnd q := by
  obtain ⟨x, hx⟩ := hq
  exact ⟨x, hx, fun y hy => P.descriptor_injective _ (hy.trans hx.symm)⟩

end LeanCanny.Encoding.NamedRationalParents
