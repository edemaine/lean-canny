/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankPolynomialModel
public import LeanCanny.Algebra.SquareFeatureProductFamily
public import LeanCanny.Algebra.FixedWidthRowReboxSpace
/-! # A bounded catalogue of charged integer-polynomial sources

Rows are selected by one FP packet writer. All casts preserve numerical
variable indices; all degree and mass controls precede real specialization.
-/
@[expose] public section
namespace LeanCanny.Encoding.ChargedPolynomialCatalogue
open LeanCanny.Algebra LeanCanny.Computation MvPolynomial MatrixPower FixedWidthPolynomial
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Input where
  source : Source
  row : List Bool → List Bool
  arity : List Bool → ℕ
  count : List Bool → ℕ
  degree : List Bool → ℕ
  mass : List Bool → ℕ
  dimension : ∀ c i, source.arity (row (pair c (BinaryNatCode.encode i)))=arity c
  degree_bound : ∀ c i, source.degree (row (pair c (BinaryNatCode.encode i)))≤degree c
  mass_bound : ∀ c i, source.mass (row (pair c (BinaryNatCode.encode i)))≤mass c

structure Access (C : Input) where
  source : IntegralFramedBankPolynomialModel.Access C.source
  row : C.row ∈ FP
  arity : UnaryFn C.arity
  count : BinaryFn C.count
  degree : BinaryFn C.degree
  mass : BinaryFn C.mass
  fit : ∀ z, C.source.degree z<2^C.source.width z

noncomputable def feature (C : Input) (c : List Bool) (i : ℕ) : MvPolynomial (Fin (C.arity c)) ℤ :=
  rename (Fin.cast (C.dimension c i)) (C.source.polynomial (C.row (pair c (BinaryNatCode.encode i))))
noncomputable def family (C : Input) : SquareFeatureProductFamily.Family where
  arity := C.arity
  count := C.count
  degree := C.degree
  mass := C.mass
  feature := feature C
  feature_degree c i _ := ((totalDegree_rename_le _ _).trans (C.source.polynomial_degree _)).trans (C.degree_bound c i)
  feature_mass c i _ := ((MvMass.rename_le _ _).trans (C.source.polynomial_mass _)).trans
    (Nat.pow_le_pow_right (by decide) (C.mass_bound c i))

def context := RationalSubstitution.IntegerBits.context
def target := RationalSubstitution.IntegerBits.selectedDegree
def original (q : List Bool) := pairFst (context q)
def index (q : List Bool) := Nat.fromBitsLE (pairSnd (context q))
def canonical (q : List Bool) := pair (original q) (BinaryNatCode.encode (index q))
theorem context_FP : context ∈ FP := RationalSubstitution.IntegerBits.context_mem_FP
theorem target_FP : target ∈ FP := RationalSubstitution.IntegerBits.selectedDegree_mem_FP
theorem original_FP : original ∈ FP := mem_FP_comp context_FP pairFst_mem_FP
theorem canonical_FP : canonical ∈ FP := mem_FP_pair original_FP
  (BinaryFn.fromBits (mem_FP_comp context_FP pairSnd_mem_FP)).bits_mem_FP

noncomputable def rowArity (C : Input) (q : List Bool) := C.arity (original q)
noncomputable def rowWidth (C : Input) (q : List Bool) := SquareFeatureProductFamily.inputWidth (family C) (original q)
noncomputable def oldWidth (C : Input) (q : List Bool) := C.source.width (C.row (canonical q))
noncomputable def rowPolynomial (C : Input) (q : List Bool) : MvPolynomial (Fin (rowArity C q)) ℤ := feature C (original q) (index q)
private theorem width_control (F : SquareFeatureProductFamily.Family) (H : BinaryFn F.degree) :
    UnaryFn (SquareFeatureProductFamily.inputWidth F) :=
  (UnaryFn.length (H.add (BinaryFn.const 1)).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
theorem rowArity_unary (C : Input) (A : Access C) : UnaryFn (rowArity C) := A.arity.comp original_FP
theorem rowWidth_unary (C : Input) (A : Access C) : UnaryFn (rowWidth C) := (width_control (family C) A.degree).comp original_FP
theorem oldWidth_unary (C : Input) (A : Access C) : UnaryFn (oldWidth C) := A.source.width.comp (mem_FP_comp canonical_FP A.row)

private theorem cast_coefficient {a b : ℕ} (h : a=b) (p : MvPolynomial (Fin a) ℤ) (W r : ℕ) :
    (rename (Fin.cast h) p).coeff (nativeExponent (Equiv.refl (Fin b)) W r)=
      p.coeff (nativeExponent (Equiv.refl (Fin a)) W r) := by
  subst b
  simp only [Fin.cast_refl,MvPolynomial.rename_id,AlgHom.id_apply]
theorem row_fit (C : Input) (A : Access C) (q : List Bool) : (rowPolynomial C q).totalDegree<2^oldWidth C q :=
  ((totalDegree_rename_le _ _).trans (C.source.polynomial_degree _)).trans_lt (A.fit (C.row (canonical q)))

noncomputable def coefficient (C : Input) : List Bool → List Bool :=
  FixedWidthRowBits.value (rowArity C) (rowWidth C) (rowPolynomial C) target pairSnd
theorem coefficient_evaluator (C : Input) (A : Access C) : SpaceFunction (coefficient C) := by
  let bits := FixedWidthQuery.repack (rowArity C) (rowWidth C) (rowArity C) (oldWidth C) target
  have HB : bits ∈ FP := FixedWidthQuery.repack_mem_FP (rowArity_unary C A) (rowWidth_unary C A)
    (rowArity_unary C A) (oldWidth_unary C A) target_FP
  let read := C.row ∘ canonical
  have HR : read ∈ FP := mem_FP_comp canonical_FP A.row
  let query := fun q => pair (pair (read q) (bits q)) (pairSnd q)
  have HQ : query ∈ FP := mem_FP_pair (mem_FP_pair HR HB) pairSnd_mem_FP
  have E := A.source.evaluator.precompose query HQ
  have EP : SpaceFunction (FixedWidthRowBits.value (rowArity C) (oldWidth C) (rowPolynomial C) bits pairSnd) := by
    apply E.congr
    funext q
    change A.source.coefficient (pair (pair (read q) (bits q)) (pairSnd q))=_
    rw [A.source.packet]
    exact congrArg (fun a : ℤ => residueBits (a : ZMod (Nat.fromBitsLE (pairSnd q)+1)))
      (cast_coefficient (C.dimension (original q) (index q)) (C.source.polynomial (read q))
        (oldWidth C q) (Nat.fromBitsLE (bits q))).symm
  exact FixedWidthRowReboxBits.evaluator (rowArity C) (oldWidth C) (rowWidth C) target (rowPolynomial C) pairSnd
    (rowArity_unary C A) (oldWidth_unary C A) (rowWidth_unary C A) target_FP (row_fit C A) EP

noncomputable def access (C : Input) (A : Access C) : SquareFeatureProductFamily.Access (family C) where
  arity := A.arity
  count := A.count
  degree := A.degree
  mass := A.mass
  coefficient := coefficient C
  evaluator := coefficient_evaluator C A
  packet c i _ bits modulus := by
    let H (c : List Bool) (i r m : ℕ) := residueBits (((feature C c i).coeff
      (nativeExponent (Equiv.refl _) (SquareFeatureProductFamily.inputWidth (family C) c) r) : ℤ) : ZMod (m+1))
    change H (original (pair (pair (pair c (BinaryNatCode.encode i)) bits) modulus))
      (index (pair (pair (pair c (BinaryNatCode.encode i)) bits) modulus))
      (Nat.fromBitsLE (target (pair (pair (pair c (BinaryNatCode.encode i)) bits) modulus)))
      (Nat.fromBitsLE (pairSnd (pair (pair (pair c (BinaryNatCode.encode i)) bits) modulus))) =
      H c i (Nat.fromBitsLE bits) (Nat.fromBitsLE modulus)
    congr 1 <;> simp only [original,index,context,target,RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

end LeanCanny.Encoding.ChargedPolynomialCatalogue
