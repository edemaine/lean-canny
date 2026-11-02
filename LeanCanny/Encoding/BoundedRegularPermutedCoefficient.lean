/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthPermutationSpace
public import LeanCanny.Encoding.BoundedRegularLowCoefficient
public import LeanCanny.Algebra.IntegralMixedCoordinateRename
/-! # Original bounded regular leaves after a native spatial permutation

The original source is unchanged; native exponent queries carry the inverse
coordinate permutation. Large regularizing powers remain implicit.
-/
@[expose] public section
namespace LeanCanny.Encoding.BoundedRegularPermutedCoefficient
open LeanCanny.ETR LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Computation
open BoundedFullWriter MatrixPower RationalSubstitution.Indexed
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Readers) (ρ : (q : List Bool) → Equiv.Perm (Fin (P.dim q+4)))

noncomputable def source (q : List Bool) : IntegralMixedHistory.SpatialSource (P.dim q+3) :=
  IntegralMixedCoordinateRename.spatial (BoundedRegularLowModularTerm.source P q) (ρ q)

noncomputable def value (W : List Bool → ℕ) (target modulus : List Bool → List Bool) (q : List Bool) :=
  residueBits ((((source P ρ q).low).coeff (exponentVector (P.dim q+4)
    (FixedWidthQuery.coordinate W target q)) : ℤ) : ZMod (Nat.fromBitsLE (modulus q)+1))

theorem evaluator {W : List Bool → ℕ} {target modulus inverse : List Bool → List Bool}
    (h : P.PolyTime) (hW : UnaryFn W) (ht : target∈FP) (hm : modulus∈FP) (hi : inverse∈FP)
    (hr : ∀ q (i : Fin (P.dim q+4)),inverse (pair q (BinaryNatCode.encode i.val))=BinaryNatCode.encode ((ρ q).symm i).val)
    (ha : ∀ q,(TermView.term (P.source q)).arity≤P.dim q) : SpaceFunction (value P ρ W target modulus) := by
  have HW := FixedWidthPermutationBits.word_FP (fun q => P.dim q+4) W target inverse
    (h.dim.add (UnaryFn.const 4)) hW ht hi
  have E := BoundedRegularLowCoefficient.evaluator h hW HW hm ha
  apply E.congr
  funext q
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (modulus q)+1)))
    (FixedWidthPermutationBits.coefficient (fun q => P.dim q+4) W target inverse q (ρ q) (hr q)
      (BoundedRegularLowModularTerm.low P q))

def liftInverse (inverse : List Bool → List Bool) (z : List Bool) :=
  inverse (pair (pairFst (pairFst z)) (pairSnd z))

theorem liftInverse_FP {inverse : List Bool → List Bool} (hi : inverse∈FP) : liftInverse inverse∈FP :=
  mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP) hi

theorem scalar_evaluator (h : P.PolyTime) (W M : List Bool → ℕ)
    (hW : UnaryFn W) (hM : BinaryFn M) (hpos : ∀ q,M q≠0)
    (inverse : List Bool → List Bool) (hi : inverse∈FP)
    (hr : ∀ q (i : Fin (P.dim q+4)),inverse (pair q (BinaryNatCode.encode i.val))=BinaryNatCode.encode ((ρ q).symm i).val)
    (ha : ∀ q,(TermView.term (P.source q)).arity≤P.dim q) :
    SpaceFunction (IntegralOriginalTermCoefficientBits.scalar (fun q => P.dim q+4) W M (fun q => (source P ρ q).low)) := by
  let modulus := fun z => BinaryNatCode.encode (M (pairFst z)-1)
  have HMC : BinaryFn (fun z => M (pairFst z)) := hM.comp pairFst_mem_FP
  have HM : modulus∈FP := (HMC.sub (BinaryFn.const 1)).bits_mem_FP
  have E := evaluator (P.comp pairFst) (fun z => ρ (pairFst z)) (h.comp pairFst_mem_FP)
    (hW.comp pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP) HM (liftInverse_FP hi)
    (fun z i => by
      simp only [liftInverse,pairFst_pair,pairSnd_pair]
      exact hr (pairFst z) i)
    (fun z => ha (pairFst z))
  apply E.congr
  funext z
  have Hmod : Nat.fromBitsLE (modulus z)+1=M (pairFst z) := by
    simp only [modulus,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    have H := hpos (pairFst z)
    omega
  have HC : FixedWidthQuery.coordinate (fun z => W (pairFst z)) (BinaryNat.normalize ∘ pairSnd) z=
      FixedWidthPolynomial.entry (W (pairFst z)) (Nat.fromBitsLE (pairSnd z)) := by
    funext i
    simp only [FixedWidthQuery.coordinate,Function.comp_apply,BinaryNat.normalize_eq_bits,FixedWidthPolynomial.entry]
  unfold value IntegralOriginalTermCoefficientBits.scalar
  rw [Hmod,HC]
  rfl

theorem leading_FP {modulus : List Bool → List Bool} (h : P.PolyTime) (hm : modulus∈FP) :
    (fun q => residueBits ((source P ρ q).leading : ZMod (Nat.fromBitsLE (modulus q)+1)))∈FP :=
  BoundedRegularLowCoefficient.leading_FP h hm

/-- Frozen-first ordering uses only an original supplied mask word. -/
noncomputable def frozenPermutation (mask : List Bool → List Bool) (q : List Bool) : Equiv.Perm (Fin (P.dim q+4)) :=
  FrozenCoordinateOrdering.permutation (SuppliedFrozenMaskBits.selected (P.dim q+4) (mask q))

theorem frozen_scalar_evaluator (h : P.PolyTime) (W M : List Bool → ℕ)
    (hW : UnaryFn W) (hM : BinaryFn M) (hpos : ∀ q,M q≠0)
    (mask : List Bool → List Bool) (hm : mask∈FP)
    (ha : ∀ q,(TermView.term (P.source q)).arity≤P.dim q) :
    SpaceFunction (IntegralOriginalTermCoefficientBits.scalar (fun q => P.dim q+4) W M
      (fun q => (source P (frozenPermutation P mask) q).low)) :=
  scalar_evaluator P (frozenPermutation P mask) h W M hW hM hpos
    (FixedWidthPermutationBits.frozenInverse (fun q => P.dim q+4) mask)
    (FixedWidthPermutationBits.frozenInverse_FP _ (h.dim.add (UnaryFn.const 4)) mask hm)
    (FixedWidthPermutationBits.frozenInverse_packet _ mask) ha
end LeanCanny.Encoding.BoundedRegularPermutedCoefficient
