/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.BoundedRegularLowCoefficient
/-! # Original-only coefficient and leading heights of the literal regular LOW -/
@[expose] public section
namespace LeanCanny.Encoding.BoundedRegularLowHeight
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry LeanCanny.ETR MvPolynomial
open BoundedFullWriter
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def lowMass (P : Readers) (c : List Bool) :=
  BoundedRegularSource.lowMassExponent (P.dim c) (size P c) (size P c) (P.radius c)
noncomputable def height (P : Readers) (c : List Bool) := regularizationExponent P c+lowMass P c+1

theorem lowMass_binary {P : Readers} (h : P.PolyTime) : BinaryFn (lowMass P) :=
  (((scaleExponent_binary h).add (BoundedZeroControls.massExponent_binary h.dim (BinaryFn.ofUnary (size_unary h)) h.radius)).add
    (shiftExponent_binary h)).add (BinaryFn.const 1)
theorem height_binary {P : Readers} (h : P.PolyTime) : BinaryFn (height P) :=
  ((regularizationExponent_binary h).add (lowMass_binary h)).add (BinaryFn.const 1)

theorem lower_mass (P : Readers) (c : List Bool) :
    MvMass.mass (BoundedRegularSource.lower (original P c) (size P c) (size P c) (P.radius c))≤2^lowMass P c :=
  BoundedRegularSource.lower_mass _ _ _ _ ((TermView.term (P.source c)).finitePolynomial_mass (P.dim c))

theorem source_mass (P : Readers) (c : List Bool) :
    MvMass.mass (BoundedRegularLowModularTerm.source P c).low≤2^height P c := by
  dsimp only [BoundedRegularLowModularTerm.source,BoundedRegularLowModularTerm.low,BoundedFullWriter.controls]
  have HM := lower_mass P c
  have HL : MvMass.mass (C ((2 : ℤ)^regularizationExponent P c) : MvPolynomial (Fin (P.dim c+4)) ℤ)=2^regularizationExponent P c := by
    simp only [MvMass.C,Int.natAbs_pow,show (2 : ℤ).natAbs=2 from rfl]
  have HP := (MvMass.mul_le (C ((2 : ℤ)^regularizationExponent P c)) _).trans (Nat.mul_le_mul HL.le HM)
  rw [←pow_add] at HP
  have Hpos := Nat.one_le_two_pow (n:=regularizationExponent P c+lowMass P c)
  change MvMass.mass ((C ((2 : ℤ)^regularizationExponent P c)*
    BoundedRegularSource.lower (original P c) (size P c) (size P c) (P.radius c)-1 : MvPolynomial (Fin (P.dim c+4)) ℤ))≤_
  apply (MvMass.sub_le _ _).trans
  rw [MvMass.one]
  unfold height
  rw [pow_succ]
  omega

theorem coefficient (P : Readers) (c : List Bool) (e : Fin (P.dim c+4) →₀ ℕ) :
    (((BoundedRegularLowModularTerm.source P c).low).coeff e).natAbs≤2^height P c :=
  (MvMass.coeff_le _ e).trans (source_mass P c)

theorem leading (P : Readers) (c : List Bool) :
    (BoundedRegularLowModularTerm.source P c).leading.natAbs.size=regularizationExponent P c+1 := by
  simp only [BoundedRegularLowModularTerm.source,BoundedRegularLowModularTerm.leading,BoundedSourceWriter.leading,
    IntegerRegularSource.leading,IntegerRegularSource.scale,mul_one,Int.natAbs_pow,
    show (2 : ℤ).natAbs=2 from rfl,Nat.size_pow]
  rfl

end LeanCanny.Encoding.BoundedRegularLowHeight
