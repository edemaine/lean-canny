/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.BoundedRegularLowModularTerm
public import LeanCanny.Algebra.IntegralOriginalTermCoefficientSpace
public import LeanCanny.Algebra.ImplicitPowerResidueFP
/-! # Native original LOW and leading leaves of the bounded regular source -/
@[expose] public section
namespace LeanCanny.Encoding.BoundedRegularLowCoefficient
open LeanCanny.ETR LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Computation
open BoundedFullWriter MatrixPower RationalSubstitution.Indexed
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def value (P : Readers) (W : List Bool → ℕ) (target modulus : List Bool → List Bool) (c : List Bool) :=
  residueBits (((BoundedRegularLowModularTerm.low P c).coeff
    (exponentVector (P.dim c+4) (FixedWidthQuery.coordinate W target c)) : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1))

theorem evaluator {P : Readers} {W : List Bool → ℕ} {target modulus : List Bool → List Bool}
    (h : P.PolyTime) (hW : UnaryFn W) (ht : target∈FP) (hm : modulus∈FP)
    (ha : ∀ c,(TermView.term (P.source c)).arity≤P.dim c) : SpaceFunction (value P W target modulus) := by
  let source := fun c => (BoundedRegularLowModularTerm.term P modulus c).toData.toBits
  have HS : source∈FP := BoundedRegularLowModularTerm.encode_mem_FP h hm
  have E := SizedCollectedCoefficient.evaluator (h.dim.add (UnaryFn.const 4)) hW HS ht hm (fun c => by
    rw [show TermView.term (source c)=BoundedRegularLowModularTerm.term P modulus c from TermView.term_toBits _]
    exact BoundedRegularLowModularTerm.arity P modulus c (ha c))
  apply E.congr
  funext c
  unfold SizedCollectedCoefficient.value
  rw [show TermView.term (source c)=BoundedRegularLowModularTerm.term P modulus c from TermView.term_toBits _]
  have HC := congrArg (fun p : MvPolynomial (Fin (P.dim c+4)) (ZMod (Nat.fromBitsLE (modulus c)+1)) =>
    p.coeff (exponentVector (P.dim c+4) (FixedWidthQuery.coordinate W target c)))
    (BoundedRegularLowModularTerm.polynomial_map P modulus c (ha c))
  simp only [MvPolynomial.coeff_map,Int.coe_castRingHom] at HC
  exact congrArg residueBits HC

theorem scalar_evaluator {P : Readers} (h : P.PolyTime) (W M : List Bool → ℕ)
    (hW : UnaryFn W) (hM : BinaryFn M) (hpos : ∀ c,M c≠0)
    (ha : ∀ c,(TermView.term (P.source c)).arity≤P.dim c) :
    SpaceFunction (IntegralOriginalTermCoefficientBits.scalar (fun c => P.dim c+4) W M
      (BoundedRegularLowModularTerm.low P)) := by
  let modulus := fun p => BinaryNatCode.encode (M (pairFst p)-1)
  have HMC : BinaryFn (fun p => M (pairFst p)) := hM.comp pairFst_mem_FP
  have HM : modulus∈FP := (HMC.sub (BinaryFn.const 1)).bits_mem_FP
  have E := evaluator (h.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP)
    (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP) HM (fun p => ha (pairFst p))
  apply E.congr
  funext p
  have Hmod : Nat.fromBitsLE (modulus p)+1=M (pairFst p) := by
    simp only [modulus,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    have H:=hpos (pairFst p)
    omega
  have HC : FixedWidthQuery.coordinate (fun z => W (pairFst z)) (BinaryNat.normalize ∘ pairSnd) p=
      FixedWidthPolynomial.entry (W (pairFst p)) (Nat.fromBitsLE (pairSnd p)) := by
    funext i
    simp only [FixedWidthQuery.coordinate,Function.comp_apply,BinaryNat.normalize_eq_bits,FixedWidthPolynomial.entry]
  unfold value IntegralOriginalTermCoefficientBits.scalar
  rw [Hmod,HC]
  rfl

noncomputable def leadingValue (P : Readers) (modulus : List Bool → List Bool) (c : List Bool) :=
  residueBits (BoundedRegularLowModularTerm.leading P c : ZMod (Nat.fromBitsLE (modulus c)+1))

theorem leading_FP {P : Readers} {modulus : List Bool → List Bool} (h : P.PolyTime) (hm : modulus∈FP) :
    leadingValue P modulus∈FP := by
  have H := ImplicitPowerResidue.power_two_mem_FP
    (fun c => BinaryNatCode.encode (regularizationExponent P c)) modulus
    (regularizationExponent_binary h).bits_mem_FP hm
  apply mem_FP_of_eq H
  intro c
  simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HL : (2 : ℤ)^regularizationExponent P c=BoundedRegularLowModularTerm.leading P c := by
    unfold BoundedRegularLowModularTerm.leading BoundedSourceWriter.leading IntegerRegularSource.leading IntegerRegularSource.scale
    rw [mul_one]
    rfl
  rw [HL]
  rfl
/-- A concrete static source descriptor from original syntax and a binary radius. -/
def readers (n : List Bool → ℕ) (t : List Bool → Term) (radius : List Bool → ℕ) : Readers :=
  ⟨fun q => (t q).toData.toBits,n,radius⟩

theorem readers_native {n radius : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (hR : BinaryFn radius) :
    (readers n t radius).PolyTime := ⟨ht,hn,hR⟩

theorem readers_source_polynomial (n : List Bool → ℕ) (t : List Bool → Term) (radius : List Bool → ℕ)
    (q : List Bool) :
    FermatCriticalHomogenization.polynomial
      (BoundedRegularLowModularTerm.source (readers n t radius) q).low
      (BoundedRegularLowModularTerm.source (readers n t radius) q).leading
      (BoundedRegularLowModularTerm.source (readers n t radius) q).degree=
      BoundedRegularSource.polynomial ((t q).finitePolynomial (n q)) (t q).toData.size (t q).toData.size (radius q) := by
  rw [BoundedRegularLowModularTerm.source_polynomial]
  simp only [readers,BoundedFullWriter.original,controls,BoundedSourceWriter.original,
    size,BoundedSourceWriter.size,TermView.term_toBits]

theorem original_scalar_evaluator {n radius : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (hR : BinaryFn radius)
    (ha : ∀ q,(t q).arity≤n q) (W M : List Bool → ℕ) (hW : UnaryFn W) (hM : BinaryFn M)
    (hpos : ∀ q,M q≠0) :
    SpaceFunction (IntegralOriginalTermCoefficientBits.scalar (fun q => n q+4) W M
      (BoundedRegularLowModularTerm.low (readers n t radius))) := by
  apply scalar_evaluator (readers_native hn ht hR) W M hW hM hpos
  intro q
  simpa only [readers,TermView.term_toBits] using ha q
end LeanCanny.Encoding.BoundedRegularLowCoefficient
