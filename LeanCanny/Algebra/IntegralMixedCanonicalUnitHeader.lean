/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCanonicalUnitRules
public import LeanCanny.Algebra.IntegralMixedCommandHeaderWriter
/-! # Original unit records determine exact framed command headers

Only the source dimension and its fixed degree are inspected. Integer source
coefficients, original LOW polynomials and interpreted retained states are
absent from these header values.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCanonicalUnitHeaderBits
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory
open IntegralMixedUnitRecordCode (field physicalOffset virtualOffset)
open IntegralMixedCommandHeaderBits (Header)
open scoped Classical

def physicalFree (n : ℕ) (code : List Bool) := n-physicalOffset n code+1
def virtualFree (n : ℕ) (code : List Bool) := n-virtualOffset n code+1

def selection (n degree : ℕ) (code : List Bool) : Header :=
  ⟨2,Nat.fromBitsLE (field code 4)%virtualFree n code,virtualOffset n code,
    Nat.fromBitsLE (field code 3)%virtualFree n code,
    Nat.fromBitsLE (field code 9)%(IntegralMixedExceptionalBounds.auxiliaryCap (n+1) degree+1),
    Nat.fromBitsLE (field code 8)%(PurePowerReductionBounds.dimension (virtualFree n code) degree+1),5⟩

def physical (n : ℕ) (code : List Bool) : Header :=
  ⟨1,Nat.fromBitsLE (field code 4)%physicalFree n code,physicalOffset n code,
    Nat.fromBitsLE (field code 3)%physicalFree n code,0,0,1⟩

def command (n degree : ℕ) (code : List Bool) : Header :=
  if IntegralMixedUnitRecordCode.critical code then physical n code else selection n degree code

theorem selection_eq {n : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ) (code : List Bool) :
    IntegralMixedCommandHeaderBits.selection (IntegralMixedCanonicalUnitRuleBits.selection S hn birth code)=selection n S.degree code := rfl

theorem command_eq {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ) (code : List Bool)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B) :
    IntegralMixedCommandHeaderBits.command (IntegralMixedCanonicalUnitRuleBits.command S hn birth code hcap)=command n S.degree code := by
  unfold IntegralMixedCanonicalUnitRuleBits.command command
  split_ifs
  · simp only [IntegralMixedCommandHeaderBits.command,IntegralMixedCanonicalUnitRuleBits.physical,
      physical,physicalFree,Nat.mod_mod]
  · rfl

end LeanCanny.Algebra.IntegralMixedCanonicalUnitHeaderBits
