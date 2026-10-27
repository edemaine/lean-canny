/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceDegree
public import LeanCanny.Algebra.PolynomialPrincipalCoefficientSpace
public import LeanCanny.Algebra.PrincipalParameterMass

/-! # Principal tests with actual algebraic-slice degrees

Actual degrees are computed in native space and attached to a fresh context.
The principal parameter polynomial then has FP degree metadata and original
modular coefficient access, so the ordered-root sign engine can evaluate it.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice.Principal
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedProjectionTestMoments
open scoped Classical
attribute [local irreducible] BoundedProjectionOrderedRoot.root BoundedProjectionRootCount.count
  BoundedProjectionTestSign.value

def origin (v : List Bool) : List Bool := pairFst (pairFst v)
def leftDegree (v : List Bool) : ℕ := Nat.fromBitsLE (pairFst (pairSnd v))
def rightDegree (v : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (pairSnd v))
theorem origin_FP : origin ∈ FP := by polytime [origin]
theorem leftDegree_binary : BinaryFn leftDegree := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem rightDegree_binary : BinaryFn rightDegree := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

def family (F G : Family) : PolynomialPrincipalCoefficientBits.Family where
  left := F.polynomial ∘ origin
  right := G.polynomial ∘ origin
  leftDegree := leftDegree
  rightDegree := rightDegree

def access {F G : Family} (A : F.Access) (B : G.Access) : (PolynomialPrincipalCoefficientBits.Access (family F G)) where
  left := PolynomialPrincipalCoefficientBits.reindexReader (PolynomialPrincipalCoefficientBits.reindexReader A.reader)
  right := PolynomialPrincipalCoefficientBits.reindexReader (PolynomialPrincipalCoefficientBits.reindexReader B.reader)
  leftDegree := leftDegree_binary
  rightDegree := rightDegree_binary

noncomputable def test (F G : Family) : Test where
  polynomial := PolynomialPrincipalCoefficientBits.polynomial (family F G)
  degree w := (leftDegree (pairFst w) + rightDegree (pairFst w) + 1) *
    (F.parameterDegree (origin (pairFst w)) + G.parameterDegree (origin (pairFst w)))
  mass w := PrincipalSubresultant.parameterMassBound (leftDegree (pairFst w) + rightDegree (pairFst w))
    (F.mass (origin (pairFst w)) + G.mass (origin (pairFst w)))
  polynomial_degree w := by
    change (PrincipalSubresultant.signedPsc (F.polynomial (origin (pairFst w))) (G.polynomial (origin (pairFst w)))
      (leftDegree (pairFst w)) (rightDegree (pairFst w)) (Nat.fromBitsLE (pairSnd w))).natDegree ≤ _
    apply PrincipalSubresultant.signedPsc_parameter_degree
    · intro i
      exact (F.coefficient_degree _ i).trans (Nat.le_add_right _ _)
    · intro i
      exact (G.coefficient_degree _ i).trans (Nat.le_add_left _ _)
  polynomial_mass w := by
    change coefficientMass (PrincipalSubresultant.signedPsc (F.polynomial (origin (pairFst w))) (G.polynomial (origin (pairFst w)))
      (leftDegree (pairFst w)) (rightDegree (pairFst w)) (Nat.fromBitsLE (pairSnd w))) ≤ _
    apply PrincipalSubresultant.signedPsc_mass_le _ _ _ _ _ _ _ (Nat.le_refl _)
    · intro i
      exact (F.coefficient_mass _ i).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
    · intro i
      exact (G.coefficient_mass _ i).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))

theorem test_eval (F G : Family) (w : List Bool) (t : ℝ) :
    (ParameterTarski.evalHom t) ((test F G).polynomial w) =
      PrincipalSubresultant.signedPsc (F.slice (origin (pairFst w)) t) (G.slice (origin (pairFst w)) t)
        (leftDegree (pairFst w)) (rightDegree (pairFst w)) (Nat.fromBitsLE (pairSnd w)) := by
  simpa only [test, PolynomialPrincipalCoefficientBits.polynomial, family, Function.comp_apply, Family.slice] using
    (PrincipalSubresultant.signedPsc_map_map (ParameterTarski.evalHom t)
      (F.polynomial (origin (pairFst w))) (G.polynomial (origin (pairFst w)))
      (leftDegree (pairFst w)) (rightDegree (pairFst w)) (Nat.fromBitsLE (pairSnd w))).symm

noncomputable def testAccess {F G : Family} (A : F.Access) (B : G.Access) : (test F G).Access where
  degree_binary := BinaryFn.mul
    (((leftDegree_binary.add rightDegree_binary).add (BinaryFn.const 1)).comp pairFst_mem_FP)
    ((BinaryFn.add (A.parameterDegree_binary.comp origin_FP) (B.parameterDegree_binary.comp origin_FP)).comp pairFst_mem_FP)
  mass_binary := by
    have hR : BinaryFn (fun w => leftDegree (pairFst w) + rightDegree (pairFst w)) :=
      (leftDegree_binary.add rightDegree_binary).comp pairFst_mem_FP
    have hb : BinaryFn (fun w => F.mass (origin (pairFst w)) + G.mass (origin (pairFst w))) :=
      (BinaryFn.add (A.mass_binary.comp origin_FP) (B.mass_binary.comp origin_FP)).comp pairFst_mem_FP
    exact ((hR.size.mul hR).add (hR.mul hb)).add hb
  coefficient := PolynomialPrincipalCoefficientBits.residueValue (access A B)
  coefficient_eq w k m hm := by
    refine (PolynomialPrincipalCoefficientBits.residueValue_eq (access A B) _).trans ?_
    exact congrArg₂ (fun (a : ℤ) (n : ℕ) => MatrixPower.residueBits (a : ZMod n))
      (by simp only [test, PolynomialPrincipalMinorBits.origin, PolynomialPrincipalCoefficientBits.parameter,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
      (by simp only [PolynomialPrincipalMinorBits.modulus, pairSnd_pair, BinaryNatCode.encode,
        Nat.fromBitsLE_bits, Nat.sub_add_cancel (by omega : 1 ≤ m)])
  evaluator := PolynomialPrincipalCoefficientBits.evaluator (access A B)

noncomputable def prepare (P : Readers) (F G : Family) (q : List Bool) : List Bool :=
  pair (pair (pairFst q) (pair (BinaryNatCode.encode (degree P F (pairFst q)))
    (BinaryNatCode.encode (degree P G (pairFst q))))) (pairSnd q)

def attach (z : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst z)) (pairSnd z)) (pairSnd (pairFst z))
theorem attach_FP : attach ∈ FP := by polytime [attach]

theorem prepare_evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (prepare P F G) := by
  have E := (((degree_evaluator h A ha).precompose pairFst pairFst_mem_FP).pairOutputs
    ((degree_evaluator h B ha).precompose pairFst pairFst_mem_FP)).withInput.postcompose attach attach_FP
  exact E.congr (funext fun q => by simp only [Function.comp_apply, attach, pairFst_pair, pairSnd_pair]; rfl)

def parameterContext (w : List Bool) : List Bool := origin (pairFst w)
theorem parameterContext_FP : parameterContext ∈ FP := mem_FP_comp pairFst_mem_FP origin_FP

def rootQuery (w : List Bool) : List Bool :=
  pair w (BinaryNat.normalize (pairSnd (pairFst (pairFst w))))
theorem rootQuery_FP : rootQuery ∈ FP := by polytime [rootQuery]

noncomputable def rawSign (P : Readers) (F G : Family) : List Bool → List Bool :=
  BoundedProjectionTestSign.value (P.comp parameterContext) (test F G) ∘ rootQuery ∘ prepare P F G

theorem rawSign_evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (rawSign P F G) :=
  (prepare_evaluator h A B ha).chain
    ((BoundedProjectionTestSign.evaluator (h.comp parameterContext_FP) (testAccess A B)
      (fun w => ha (parameterContext w))).precompose rootQuery rootQuery_FP)

theorem rawSign_packet (P : Readers) (F G : Family) (u : List Bool) (hu : u ∈ valid P) (k : ℕ) :
    rawSign P F G (pair u (BinaryNatCode.encode k)) = InfinitesimalSign.encode
      (SignType.sign (PrincipalSubresultant.signedPsc (specialized P F u) (specialized P G u)
        (degree P F u) (degree P G u) k)) := by
  let w := prepare P F G (pair u (BinaryNatCode.encode k))
  have hc : parameterContext w = pairFst u := by
    simp only [w, parameterContext, origin, prepare, pairFst_pair]
  let r : Fin (BoundedProjectionRootCount.count P (pairFst u)) := ⟨Nat.fromBitsLE (pairSnd u), hu⟩
  let s : Fin (BoundedProjectionRootCount.count (P.comp parameterContext) w) :=
    ⟨r.val, by simpa only [BoundedProjectionRootCount.count_comp, hc] using r.isLt⟩
  have hq : rootQuery w = pair w (BinaryNatCode.encode s.val) := by
    simp only [rootQuery, w, prepare, pairFst_pair, pairSnd_pair, s, r,
      BinaryNat.normalize_eq_bits, BinaryNatCode.encode]
  change BoundedProjectionTestSign.value (P.comp parameterContext) (test F G) (rootQuery w) = _
  rw [hq, BoundedProjectionTestSign.value_packet]
  have he := BoundedProjectionOrderedRoot.root_value_reindex P parameterContext w (pairFst u) hc s r rfl
  have hp : (BoundedProjectionOrderedRoot.root P (pairFst u) r).val = point P u := by
    rw [point, dite_eq_left hu]
  rw [he, hp]
  have hs : sign (test F G) w (point P u) = SignType.sign
      ((ParameterTarski.evalHom (point P u)) ((test F G).polynomial w)) := by
    simp only [sign, ParameterTarski.evalHom, Polynomial.eval_map, Polynomial.coe_eval₂RingHom]
  rw [hs, test_eval]
  simp only [w, prepare, pairFst_pair, pairSnd_pair, leftDegree, rightDegree, origin,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, specialized, ite_eq_left hu]

noncomputable def value (P : Readers) (F G : Family) (q : List Bool) : List Bool :=
  if pairFst q ∈ valid P then rawSign P F G q else []

theorem evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P F G) :=
  SpaceFunction.branchDecider ((valid_decider h ha).precompose pairFst pairFst_mem_FP)
    (rawSign_evaluator h A B ha) (SpaceFunction.ofFP _ (constFn_mem_FP []))

theorem value_packet (P : Readers) (F G : Family) (u : List Bool) (hu : u ∈ valid P) (k : ℕ) :
    value P F G (pair u (BinaryNatCode.encode k)) = InfinitesimalSign.encode
      (SignType.sign (PrincipalSubresultant.signedPsc (specialized P F u) (specialized P G u)
        (degree P F u) (degree P G u) k)) := by
  rw [value, pairFst_pair, ite_eq_left hu, rawSign_packet P F G u hu k]

theorem value_invalid (P : Readers) (F G : Family) (q : List Bool) (hq : pairFst q ∉ valid P) :
    value P F G q = [] := by rw [value, ite_eq_right hq]

end LeanCanny.Encoding.BoundedAlgebraicSlice.Principal
