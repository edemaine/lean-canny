/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedSlackRootSource
/-! # Original syntax supplies every slack-annihilator coefficient and bound -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedSlackRootBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedSlackMatrixBounds
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem height_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H) : BinaryFn (height P D H s) :=
  IntegralMixedFramedStepHeight.familyHeight_binary P a s.nodes_native s.factor_native s.seed_native

private theorem birth_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    BinaryFn (fun key=>(IntegralMixedFramedClearedMatrixBits.family P D H).birth key) :=
  BinaryFn.ofUnary (IntegralMixedFramedClearedMatrixBits.birth_unary P a D H)

theorem rawSphereAccess (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    {n R : List Bool → ℕ} (hn : UnaryFn n) (hR : BinaryFn R) :
    IntegerPolynomialRootQueriesBits.Access (rawSphereSource P D H s hs n R) where
  coefficient := IntegralMixedFramedSlackCharacteristicBits.sphere_coefficient_space P a D H s hs hF hL hn hR
  degree := IntegralMixedFramedClearedMatrixBits.rank_binary P a D H
  mass := ScaledCharacteristicIntegerBounds.massHeight_binary (IntegralMixedFramedClearedMatrixBits.rank_binary P a D H)
    (sphereHeight_binary (birth_binary P a D H) (BinaryFn.ofUnary hn) (IntegralMixedFramedClearedMatrixBits.rank_binary P a D H)
      (height_binary P a D H s) hR)
    ((BinaryFn.const 2).mul ((birth_binary P a D H).mul (height_binary P a D H s)))

theorem rawRegularAccess (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    {n d R L K : List Bool → ℕ} (hn : UnaryFn n) (hd : BinaryFn d) (hR : BinaryFn R) (hLam : BinaryFn L) (hK : BinaryFn K) :
    IntegerPolynomialRootQueriesBits.Access (rawRegularSource P D H s hs n d R L K) where
  coefficient := IntegralMixedFramedSlackCharacteristicBits.regular_coefficient_space P a D H s hs hF hL hn hd hR hLam hK
  degree := IntegralMixedFramedClearedMatrixBits.rank_binary P a D H
  mass := ScaledCharacteristicIntegerBounds.massHeight_binary (IntegralMixedFramedClearedMatrixBits.rank_binary P a D H)
    (regularHeight_binary (birth_binary P a D H) (BinaryFn.ofUnary hn) (IntegralMixedFramedClearedMatrixBits.rank_binary P a D H)
      (height_binary P a D H s) hd hR hLam hK)
    (hLam.add (hd.mul ((birth_binary P a D H).mul (height_binary P a D H s))))

theorem sphereAccess (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    {n R : List Bool → ℕ} (hn : UnaryFn n) (hR : BinaryFn R) :
    IntegerPolynomialRootQueriesBits.Access (sphereSource P D H s hs n R) :=
  IntegerPolynomialExpandSource.access (rawSphereSource P D H s hs n R) (rawSphereAccess P a D H s hs hF hL hn hR)
    (BinaryFn.const 2) (fun _=>by decide)

theorem regularAccess (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    {n d R L K : List Bool → ℕ} (hn : UnaryFn n) (hd : BinaryFn d) (hR : BinaryFn R) (hLam : BinaryFn L) (hK : BinaryFn K)
    (hpos : ∀ key,0<d key) :
    IntegerPolynomialRootQueriesBits.Access (regularSource P D H s hs n d R L K) :=
  IntegerPolynomialExpandSource.access (rawRegularSource P D H s hs n d R L K)
    (rawRegularAccess P a D H s hs hF hL hn hd hR hLam hK) hd hpos

end LeanCanny.Algebra.IntegralMixedFramedSlackRootBits
