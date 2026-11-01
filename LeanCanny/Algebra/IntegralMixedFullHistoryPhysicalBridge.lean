/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHistoryFamily
public import LeanCanny.Algebra.IntegralMixedFullPhysicalFamily
/-! # Cut and physical readers interpret the same literal mixed command prefix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullHistoryFamilyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
set_option backward.isDefEq.respectTransparency false

def physicalData (P : Parameters) (D : Data P) : IntegralMixedFullPhysicalBits.Data P where
  spatial := D.spatial
  degree_eq := D.degree_eq
  sourceWidth := D.sourceWidth
  scalar_cap := D.scalar_cap
  rules := D.rules
  room := D.room

theorem physical_prefix (P : Parameters) (key : List Bool) :
    IntegralMixedFullPhysicalBits.prefixLength P key = prefixLength P key := rfl

theorem physical_commands (P : Parameters) (D : Data P) (key : List Bool) :
    IntegralMixedFullPhysicalBits.commands P (physicalData P D) key = commands P D key := rfl

theorem physical_creating (P : Parameters) (D : Data P) (key : List Bool) :
    IntegralMixedFullPhysicalBits.creating P (physicalData P D) key = creating P D key := rfl

theorem physical_state (P : Parameters) (D : Data P) (key : List Bool) :
    (IntegralMixedFullPhysicalBits.family P (physicalData P D)).state key = (family P D).state key := rfl

theorem physical_denominator (P : Parameters) (D : Data P) (key : List Bool) :
    commonDenominator ((IntegralMixedFullPhysicalBits.family P (physicalData P D)).state key) =
      commonDenominator ((family P D).state key) := rfl

end LeanCanny.Algebra.IntegralMixedFullHistoryFamilyBits
