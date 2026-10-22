/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayFullBoxEntryCorrect
public import LeanCanny.Algebra.BivariateDeterminantInteger

/-! # The native canonical full-box determinant from original row residues

Both the exponential matrix and its monomial shifts are implicit. Every
coefficient computation includes the supplied original-row reader's space.
-/

@[expose] public section
namespace LeanCanny.Algebra.MacaulayFullBoxBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def determinantValue (L : Layout) (modulus inner outer : List Bool → List Bool)
    (p : (c : List Bool) → Fin (L.arity c) → MvPolynomial (Fin (L.arity c)) Coefficient) : List Bool → List Bool :=
  BivariateDeterminantBits.integerValue
    (fun c => (L.arity c + 2) * FixedWidthPolynomial.count (L.arity c) (L.width c))
    modulus inner outer
    (fun c => MacaulayFullBoxFinite.matrix (p c) (fun i => L.degree c i.val) (L.width c))

/-- Original homogeneous-row coefficient residues and native metadata suffice
for the fixed canonical block determinant. No selected row family is an input. -/
theorem determinantEvaluator (L : Layout) (h : L.Controls)
    (modulus inner outer bound coefficient : List Bool → List Bool)
    (p : (c : List Bool) → Fin (L.arity c) → MvPolynomial (Fin (L.arity c)) Coefficient)
    (hlevel : ∀ c, L.level c = Macaulay.level (fun i : Fin (L.arity c) => L.degree c i.val))
    (hbound : ∀ c i e k, (((p c i).coeff e).coeff k).natDegree ≤ Nat.fromBitsLE (bound c))
    (hc : ∀ c (i : Fin (L.arity c)) r u v, coefficient
      (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode r)
        (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
      scalar modulus c u v ((p c i).coeff (RationalSubstitution.Indexed.exponentVector
        (L.arity c) (FixedWidthPolynomial.entry (L.width c) r))))
    (E : SpaceFunction coefficient) (hm : modulus ∈ FP) (hi : inner ∈ FP)
    (ho : outer ∈ FP) (hb : bound ∈ FP) :
    SpaceFunction (determinantValue L modulus inner outer p) := by
  have hC : BinaryFn (fun c => FixedWidthPolynomial.count (L.arity c) (L.width c)) :=
    BinaryFn.of_bits (mem_FP_of_eq (columnsCode_FP h) (columnsCode_eq L))
  have hA : BinaryFn (fun c => L.arity c + 2) :=
    BinaryFn.of_bits (bits_mem_FP (h.arity.add (UnaryFn.const 2)))
  have hN := (hA.mul hC).bits_mem_FP
  apply BivariateDeterminantBits.integerEvaluator _ _ _ _ _ _ (blockEntry L modulus coefficient)
    (fun c => by dsimp only [MacaulayFullBoxFinite.count, FixedWidthPolynomial.count]; positivity)
    (fun c i j k => MacaulayFullBoxFinite.matrix_inner_degree (p c) (fun i => L.degree c i.val)
      (L.width c) (Nat.fromBitsLE (bound c)) (hbound c) i j k)
    ?_ (blockEntryEvaluator h hm E) hN hm hi ho hb
  intro c i j u v
  exact blockEntry_packet L modulus coefficient c (p c) (hlevel c) (hc c) i j u v

lemma determinantValue_eq (L : Layout) (modulus inner outer : List Bool → List Bool)
    (p : (c : List Bool) → Fin (L.arity c) → MvPolynomial (Fin (L.arity c)) Coefficient) (c : List Bool) :
    determinantValue L modulus inner outer p c =
      scalar modulus c (Nat.fromBitsLE (inner c)) (Nat.fromBitsLE (outer c))
        (ProjectiveBoxGramEliminant.polynomial (p c) (fun i => L.degree c i.val) (L.width c)) := by
  simp only [determinantValue, BivariateDeterminantBits.integerValue,
    MacaulayFullBoxFinite.det_matrix, scalar]

end LeanCanny.Algebra.MacaulayFullBoxBits
