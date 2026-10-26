/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedRegularModularTerm
public import LeanCanny.ETR.SizedCollectedCoefficient

/-! # Native coefficients of the actual bounded regular source

The source term is specialized modulo the requested positive modulus before
coefficient collection. The result is the residue of the exact integer source,
including its exponentially large regularization constants.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedRegularCoefficient
open LeanCanny.ETR LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Computation
open BoundedFullWriter MatrixPower RationalSubstitution.Indexed
open scoped Classical

noncomputable def value (P : Readers) (W : List Bool → ℕ) (target modulus : List Bool → List Bool)
    (c : List Bool) : List Bool :=
  residueBits (((BoundedRegularSource.polynomial (original P c) (size P c) (size P c) (P.radius c)).coeff
    (exponentVector (P.dim c + 4) (FixedWidthQuery.coordinate W target c)) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus c) + 1))

theorem evaluator {P : Readers} {W : List Bool → ℕ} {target modulus : List Bool → List Bool}
    (h : P.PolyTime) (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (value P W target modulus) := by
  let source := fun c => (BoundedRegularModularTerm.term P modulus c).toData.toBits
  have hs : source ∈ FP := BoundedRegularModularTerm.encode_mem_FP h hm
  have he := SizedCollectedCoefficient.evaluator (h.dim.add (UnaryFn.const 4)) hW hs ht hm (fun c => by
    rw [show TermView.term (source c) = BoundedRegularModularTerm.term P modulus c from TermView.term_toBits _]
    have hN : 0 < degree P c := by
      have := BoundedRegularSource.powerDegree_gt_one (size P c)
      change 0 < BoundedZeroSource.powerDegree (size P c)
      omega
    exact (BoundedRegularTerm.arity _ _ _ _ _ _ _ (ha c) hN).le)
  apply he.congr
  funext c
  unfold SizedCollectedCoefficient.value
  rw [show TermView.term (source c) = BoundedRegularModularTerm.term P modulus c from TermView.term_toBits _]
  have hc := congrArg (fun p : MvPolynomial (Fin (P.dim c + 4)) (ZMod (Nat.fromBitsLE (modulus c) + 1)) =>
    p.coeff (exponentVector (P.dim c + 4) (FixedWidthQuery.coordinate W target c)))
    (BoundedRegularModularTerm.polynomial_map P modulus c (ha c))
  simp only [MvPolynomial.coeff_map, Int.coe_castRingHom] at hc
  exact congrArg residueBits hc

end LeanCanny.Encoding.BoundedRegularCoefficient
