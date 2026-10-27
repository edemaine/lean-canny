/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionRootReindex
public import LeanCanny.Encoding.BoundedProjectionTestSign
public import LeanCanny.Algebra.CertifiedPolynomial
public import LeanCanny.Algebra.PolynomialDegreeSpace
public import LeanCanny.Algebra.ParameterizedTarski
public import LeanCanny.Algebra.DyadicPolynomialSpace
public import LeanCanny.Computation.PSPACEClosure
public import LeanCanny.Computation.SpaceFunctionSpaceBranch

/-! # Coefficient signs in a polynomial slice at an algebraic root

Original bivariate modular coefficient readers supply the scalar coefficient
tests. Reindexing preserves the ordered algebraic parameter. Invalid root
ordinals denote the zero polynomial, giving total coefficient and degree scans.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedProjectionTestMoments
open scoped Classical
attribute [local irreducible] BoundedCriticalProjection.polynomial BoundedProjectionOrderedRoot.root
  BoundedProjectionTestSign.value BoundedProjectionRootCount.count

structure Family where
  polynomial : List Bool → (ℤ[X])[X]
  degree : List Bool → ℕ
  parameterDegree : List Bool → ℕ
  mass : List Bool → ℕ
  polynomial_degree : ∀ c, (polynomial c).natDegree ≤ degree c
  coefficient_degree : ∀ c i, ((polynomial c).coeff i).natDegree ≤ parameterDegree c
  coefficient_mass : ∀ c i, coefficientMass ((polynomial c).coeff i) ≤ 2 ^ mass c

structure Family.Access (F : Family) where
  reader : CertifiedPolynomial.BivariateReader F.polynomial
  degree_binary : BinaryFn F.degree
  parameterDegree_binary : BinaryFn F.parameterDegree
  mass_binary : BinaryFn F.mass

/-- Reuse the original implicit bivariate sources also used by the dyadic
pipeline. The algebraic parameter replaces the dyadic exponent. -/
def Family.ofDyadic (F : DyadicPolynomialBits.Family) : Family where
  polynomial := F.polynomial
  degree c := Nat.fromBitsLE (F.degree c)
  parameterDegree c := Nat.fromBitsLE (F.parameterDegree c)
  mass c := Nat.fromBitsLE (F.mass c)
  polynomial_degree := F.polynomial_degree
  coefficient_degree := F.coefficient_degree
  coefficient_mass := F.coefficient_mass

def Family.accessOfDyadic (F : DyadicPolynomialBits.Family) (hF : DyadicPolynomialBits.ControlsPolyTime F)
    (A : CertifiedPolynomial.BivariateReader F.polynomial) : (Family.ofDyadic F).Access where
  reader := A
  degree_binary := BinaryFn.fromBits hF.degree
  parameterDegree_binary := BinaryFn.fromBits hF.parameterDegree
  mass_binary := BinaryFn.fromBits hF.mass

noncomputable def Family.slice (F : Family) (c : List Bool) (t : ℝ) : ℝ[X] :=
  (F.polynomial c).map (ParameterTarski.evalHom t)

noncomputable def scalar (F : Family) : Test where
  polynomial w := (F.polynomial (pairFst w)).coeff (Nat.fromBitsLE (pairSnd w))
  degree w := F.parameterDegree (pairFst w)
  mass w := F.mass (pairFst w)
  polynomial_degree w := F.coefficient_degree (pairFst w) _
  polynomial_mass w := F.coefficient_mass (pairFst w) _

def scalarQuery (q : List Bool) : List Bool := pair
  (pair (pairFst (pairFst (pairFst q))) (pairSnd q))
  (pair (pairSnd (pairFst q)) (BinaryNat.normalize (pairSnd (pairFst (pairFst q)))))
theorem scalarQuery_FP : scalarQuery ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
  have hu := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hv := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  exact mem_FP_pair (mem_FP_pair hc pairSnd_mem_FP) (mem_FP_pair hu hv)

noncomputable def scalarAccess {F : Family} (A : F.Access) : (scalar F).Access where
  degree_binary := A.parameterDegree_binary.comp pairFst_mem_FP
  mass_binary := A.mass_binary.comp pairFst_mem_FP
  coefficient := A.reader.coefficient ∘ scalarQuery
  coefficient_eq w k m hm := by
    simp only [Function.comp_apply, scalarQuery, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits]
    have H := A.reader.coefficient_eq (pair (pairFst w) (BinaryNatCode.encode (m - 1))) k (Nat.fromBitsLE (pairSnd w))
    refine H.trans ?_
    exact congrArg₂ (fun (z : ℤ) (n : ℕ) => MatrixPower.residueBits (z : ZMod n))
      (by simp only [pairFst_pair, scalar])
      (by simp only [pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (by omega : 1 ≤ m)])
  evaluator := A.reader.evaluator.precompose scalarQuery scalarQuery_FP

noncomputable def valid (P : Readers) : Language :=
  {u | Nat.fromBitsLE (pairSnd u) < BoundedProjectionRootCount.count P (pairFst u)}

def accept (z : List Bool) : Bool := decide (Nat.fromBitsLE (pairSnd (pairFst z)) < Nat.fromBitsLE (pairSnd z))
theorem accept_FP : (fun z => [accept z]) ∈ FP :=
  ((BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)).lt (BinaryFn.fromBits pairSnd_mem_FP)).flag_mem_FP

theorem valid_decider {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (valid P) := by
  apply ((BoundedProjectionRootCount.evaluator h ha).precompose pairFst pairFst_mem_FP).withInput.decider accept accept_FP
  intro u
  simp only [valid, Set.mem_ofPred_eq, accept, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

noncomputable def point (P : Readers) (u : List Bool) : ℝ :=
  if hu : u ∈ valid P then (BoundedProjectionOrderedRoot.root P (pairFst u) ⟨Nat.fromBitsLE (pairSnd u), hu⟩).val else 0

noncomputable def specialized (P : Readers) (F : Family) (u : List Bool) : ℝ[X] :=
  if u ∈ valid P then F.slice (pairFst u) (point P u) else 0

def signQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pairSnd q)) (BinaryNat.normalize (pairSnd (pairFst q)))
theorem signQuery_FP : signQuery ∈ FP := mem_FP_pair
  (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
  (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP)

noncomputable def rawSign (P : Readers) (F : Family) : List Bool → List Bool :=
  BoundedProjectionTestSign.value (P.comp pairFst) (scalar F) ∘ signQuery
theorem rawSign_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (rawSign P F) :=
  (BoundedProjectionTestSign.evaluator (h.comp pairFst_mem_FP) (scalarAccess A) (fun w => ha (pairFst w))).precompose signQuery signQuery_FP

noncomputable def coefficientSign (P : Readers) (F : Family) (q : List Bool) : List Bool :=
  if pairFst q ∈ valid P then rawSign P F q else []

theorem coefficientSign_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (coefficientSign P F) := by
  have D := (valid_decider h ha).precompose pairFst pairFst_mem_FP
  exact SpaceFunction.branchDecider D (rawSign_evaluator h A ha) (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))

theorem point_packet (P : Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    point P (pair c (BinaryNatCode.encode r.val)) = (BoundedProjectionOrderedRoot.root P c r).val := by
  have hr : pair c (BinaryNatCode.encode r.val) ∈ valid P := by
    simpa only [valid, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using r.isLt
  rw [point, dite_eq_left hr]
  apply BoundedProjectionOrderedRoot.root_value_context P _ c (pairFst_pair _ _)
  simp only [pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem coefficientSign_packet (P : Readers) (F : Family) (u : List Bool) (k : ℕ) :
    coefficientSign P F (pair u (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign ((specialized P F u).coeff k)) := by
  by_cases hu : u ∈ valid P
  · have hr : Nat.fromBitsLE (pairSnd u) < BoundedProjectionRootCount.count P (pairFst u) := hu
    let r : Fin (BoundedProjectionRootCount.count P (pairFst u)) := ⟨Nat.fromBitsLE (pairSnd u), hr⟩
    let w := pair (pairFst u) (BinaryNatCode.encode k)
    let s : Fin (BoundedProjectionRootCount.count (P.comp pairFst) w) :=
      ⟨r.val, by simpa only [BoundedProjectionRootCount.count_comp, w, pairFst_pair] using r.isLt⟩
    have hq : signQuery (pair u (BinaryNatCode.encode k)) = pair w (BinaryNatCode.encode s.val) := by
      simp only [signQuery, w, s, r, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]
    rw [coefficientSign, pairFst_pair, ite_eq_left hu, rawSign, Function.comp_apply, hq, BoundedProjectionTestSign.value_packet]
    have he := BoundedProjectionOrderedRoot.root_value_reindex P pairFst w (pairFst u)
      (pairFst_pair _ _) s r rfl
    simp only [w] at he
    have hk : Nat.fromBitsLE (BinaryNatCode.encode k) = k := Nat.fromBitsLE_bits k
    simp only [sign, scalar, w, pairFst_pair, pairSnd_pair, hk]
    rw [he]
    simp only [specialized, ite_eq_left hu, Family.slice, point, dite_eq_left hu, Polynomial.coeff_map,
      ParameterTarski.evalHom, Polynomial.eval_map]
    rfl
  · simp only [coefficientSign, pairFst_pair, hu, ite_false, specialized, Polynomial.coeff_zero, sign_zero, InfinitesimalSign.encode]

theorem specialized_degree (P : Readers) (F : Family) (u : List Bool) :
    (specialized P F u).natDegree ≤ F.degree (pairFst u) := by
  unfold specialized Family.slice
  split_ifs
  · exact Polynomial.natDegree_map_le.trans (F.polynomial_degree _)
  · simp only [Polynomial.natDegree_zero, Nat.zero_le]

end LeanCanny.Encoding.BoundedAlgebraicSlice
