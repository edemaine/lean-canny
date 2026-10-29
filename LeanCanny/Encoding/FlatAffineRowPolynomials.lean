/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineRowLayout
public import LeanCanny.Algebra.AffineHeightPolynomial

/-! # Explicit source, gradient, and ancestral-height components of affine rows -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineRowPolynomials
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineRowLayout
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullCriticalSamples.polynomial FlatAffineFullSourceTower.system

variable (F : Inputs) (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u))

noncomputable def source (u : List Bool) : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  rename (current F row u) (BoundedFullCriticalSamples.polynomial F.source u)

noncomputable def gradient (u : List Bool) : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  rename (current F row u) (pderiv (spatial F row u) (BoundedFullCriticalSamples.polynomial F.source u)) -
    ∑ j, C (FlatAffineFullSourceTower.direction F u (stage F row u) j (spatial F row u)) * X (multiplier F row u j)

noncomputable def currentHeight (u : List Bool) : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  AffineHeightPolynomial.polynomial (FlatAffineFullSourceTower.direction F u (stage F row u) (height F row u).succ)
    (current F row u)

noncomputable def oldHeight (u : List Bool) (k : ℕ) : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  AffineHeightPolynomial.polynomial
    (fun i : Fin (arity F u) => FlatAffineFullSourceTower.integer (F.width u)
      (FlatAffineFullSourceTower.normal (levelRecord F row u)) i.val)
    (fun i => coordinate F u k i.val)

noncomputable def constantLevel (u : List Bool) : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  C (FlatAffineFullSourceTower.integer (F.width u) (FlatAffineFullSourceTower.constant (levelRecord F row u)) 0)

noncomputable def oldLevel (u : List Bool) : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  if 0 < stage F row u then
    if FlatAffineFullSourceTower.tag (levelRecord F row u) = 1 then oldHeight F row u (oldLeft F row u)
    else if FlatAffineFullSourceTower.tag (levelRecord F row u) = 2 then
      oldHeight F row u (oldLeft F row u) + oldHeight F row u (oldRight F row u)
    else constantLevel F row u
  else constantLevel F row u

noncomputable def levelRow (u : List Bool) : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  if FlatAffineFullSourceTower.active (levelRecord F row u) then currentHeight F row u - oldLevel F row u
  else X (multiplier F row u (height F row u).succ)

noncomputable def polynomial (u : List Bool) : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  if index F row u < FlatAffineFullSourceTower.count F u then
    if slot F row u < arity F u then gradient F row u
    else if slot F row u = arity F u then source F row u else levelRow F row u
  else X (Fin.last (FlatAffineFullSourceTower.count F u))

end LeanCanny.Encoding.FlatAffineRowPolynomials
