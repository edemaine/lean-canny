/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceProductQuery
public import LeanCanny.Encoding.BoundedAlgebraicSliceAttach

/-! # Native specialization of indexed bivariate factors

An index is attached as metadata without changing the ordered base root.
The original indexed coefficient reader supplies the selected polynomial;
its specialized zero test is computed natively, including degree drops.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSliceIndexed
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice
open scoped Classical

def family (Q : BivariateQueryProductBits.Family) : Family where
  polynomial w := Q.polynomial (pairFst w) (Nat.fromBitsLE (pairSnd w))
  degree w := Q.degree (pairFst w)
  parameterDegree w := Q.parameterDegree (pairFst w)
  mass w := Q.mass (pairFst w)
  polynomial_degree w := Q.polynomial_degree (pairFst w) _
  coefficient_degree w := Q.coefficient_degree (pairFst w) _
  coefficient_mass w := Q.coefficient_mass (pairFst w) _

def access {Q : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access Q) : (family Q).Access where
  reader := A.reader
  degree_binary := A.degree_binary.comp pairFst_mem_FP
  parameterDegree_binary := A.parameterDegree_binary.comp pairFst_mem_FP
  mass_binary := A.mass_binary.comp pairFst_mem_FP

noncomputable def value (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : ℕ) : ℝ[X] :=
  specialized (P.comp pairFst) (family Q) (signQuery (pair u (BinaryNatCode.encode i)))

theorem value_valid (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : ℕ) (hu : u ∈ valid P) :
    value P Q u i = (Q.polynomial (pairFst u) i).map (ParameterTarski.evalHom (point P u)) := by
  rw [value, specialized_attach_raw, ite_eq_left hu]
  simp only [Family.slice, family, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem value_invalid (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : ℕ) (hu : u ∉ valid P) :
    value P Q u i = 0 := by
  rw [value, specialized_attach_raw, ite_eq_right hu]

def query (q : List Bool) : List Bool := signQuery (pair (pairFst q) (BinaryNat.normalize (pairSnd q)))
theorem query_FP : query ∈ FP := mem_FP_comp
  (mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)) signQuery_FP

noncomputable def nonzeroLanguage (P : Readers) (Q : BivariateQueryProductBits.Family) : Language :=
  query ⁻¹' BoundedAlgebraicSlice.nonzeroLanguage (P.comp pairFst) (family Q)

theorem nonzero_packet (P : Readers) (Q : BivariateQueryProductBits.Family) (q : List Bool) :
    q ∈ nonzeroLanguage P Q ↔ value P Q (pairFst q) (Nat.fromBitsLE (pairSnd q)) ≠ 0 := by
  simp only [nonzeroLanguage, Set.mem_preimage, BoundedAlgebraicSlice.nonzeroLanguage,
    Set.mem_ofPred_eq, query, BinaryNat.normalize_eq_bits, value, BinaryNatCode.encode]

theorem nonzero_decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider (nonzeroLanguage P Q) :=
  (BoundedAlgebraicSlice.nonzero_decider (h.comp pairFst_mem_FP) (access A) (fun c => ha (pairFst c))).precompose query query_FP

end LeanCanny.Encoding.BoundedAlgebraicSliceIndexed
