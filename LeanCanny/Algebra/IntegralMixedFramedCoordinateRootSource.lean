/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicSpace
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBounds
public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace
/-! # An original-only integer root-query source for retained bank coordinates -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def rootSource (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) : IntegerPolynomialRootQueriesBits.Source where
  polynomial := polynomial P D H
  degree := dimension P D H
  mass := massBound P D H L F C
  degree_bound c := (degree P D H c).le
  mass_bound := polynomial_mass P D H L F C hs

theorem rootAccess (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root) :
    IntegerPolynomialRootQueriesBits.Access (rootSource P D H s.nodes s.factor s.seed hs) where
  coefficient := coefficient_space P a D H s hs hF hL
  degree := dimension_binary P a D H
  mass := massBound_binary P a D H s.nodes_native s.factor_native s.seed_native

end LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBits
