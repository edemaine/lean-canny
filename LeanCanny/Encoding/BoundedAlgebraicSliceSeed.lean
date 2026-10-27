/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSlicePrincipal
public import LeanCanny.Algebra.BivariateTarskiSeedSpace

/-! # Bounded native seeds at algebraic slice degrees

A context retains its original root query and a degree-minus-one word.
Clamping that word gives a positive reduction degree on all inputs. At a
nonconstant slice, attaching its actual degree gives the intended Tarski seed.
All coefficient and growth data are derived from the two original sources.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice.Tarski
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open scoped Classical

def origin (v : List Bool) : List Bool := pairFst (pairFst v)
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
def bound (F G : Family) (v : List Bool) : ℕ := F.degree (origin v) + G.degree (origin v) + 1
def declared (F G : Family) (v : List Bool) : ℕ := min (Nat.fromBitsLE (pairSnd v) + 1) (bound F G v)
def headMass (F : Family) (v : List Bool) : ℕ := F.mass (origin v) + (F.degree (origin v) + 1).size

theorem bound_binary {F G : Family} (A : F.Access) (B : G.Access) : BinaryFn (bound F G) :=
  BinaryFn.add (BinaryFn.add (A.degree_binary.comp origin_FP) (B.degree_binary.comp origin_FP)) (BinaryFn.const 1)
theorem declared_binary {F G : Family} (A : F.Access) (B : G.Access) : BinaryFn (declared F G) :=
  PolynomialPrincipalCoefficientBits.minimum_binary
    ((BinaryFn.fromBits pairSnd_mem_FP).add (BinaryFn.const 1)) (bound_binary A B)
theorem headMass_binary {F : Family} (A : F.Access) : BinaryFn (headMass F) :=
  BinaryFn.add (A.mass_binary.comp origin_FP)
    (BinaryFn.size (BinaryFn.add (A.degree_binary.comp origin_FP) (BinaryFn.const 1)))

noncomputable def source (F G : Family) : BivariateTarskiSeedBits.Family where
  head v := F.polynomial (origin v)
  query v := G.polynomial (origin v)
  degree := declared F G
  bound := bound F G
  degree_pos v := by unfold declared bound; omega
  degree_le v := Nat.min_le_right _ _
  input_degree v := by
    have hp := (Polynomial.natDegree_derivative_le (F.polynomial (origin v))).trans (Nat.sub_le _ _)
    have hF := F.polynomial_degree (origin v)
    have hG := G.polynomial_degree (origin v)
    exact Polynomial.natDegree_mul_le.trans (by unfold bound; omega)

noncomputable def sourceAccess {F G : Family} (A : F.Access) (B : G.Access) : BivariateTarskiSeedBits.Access (source F G) where
  head := PolynomialPrincipalCoefficientBits.reindexReader (PolynomialPrincipalCoefficientBits.reindexReader A.reader)
  query := PolynomialPrincipalCoefficientBits.reindexReader (PolynomialPrincipalCoefficientBits.reindexReader B.reader)
  degree := declared_binary A B
  bound := bound_binary A B

theorem original_mass (F : Family) (v : List Bool) :
    NestedMass.mass (F.polynomial (origin v)) ≤ 2 ^ headMass F v :=
  NestedMass.le_pow _ _ _ (F.polynomial_degree _) (F.coefficient_mass _)

noncomputable def seedFamily (F G : Family) : Family where
  polynomial := (source F G).seed
  degree := bound F G
  parameterDegree v := 2 * (bound F G v + 1) * F.parameterDegree (origin v) +
    (G.parameterDegree (origin v) + F.parameterDegree (origin v))
  mass v := PseudoRemainder.fixedSeedMassBound (bound F G v) (F.degree (origin v)) (headMass F v) (headMass G v)
  polynomial_degree v := by
    have h := PseudoRemainder.seed_natDegree_lt (F.polynomial (origin v)) (G.polynomial (origin v))
      (declared F G v) (bound F G v) ((source F G).degree_pos v) ((source F G).input_degree v)
    exact h.le.trans ((source F G).degree_le v)
  coefficient_degree v i := PseudoRemainder.seed_parameter_degree _ _ _ _ _ _
    (F.coefficient_degree (origin v)) (G.coefficient_degree (origin v)) i
  coefficient_mass v i := (NestedMass.coeff_le _ i).trans
    (PseudoRemainder.seed_mass_le_pow _ _ _ _ _ _ _ (F.polynomial_degree (origin v))
      (original_mass F v) (original_mass G v))

noncomputable def seedAccess {F G : Family} (A : F.Access) (B : G.Access) : (seedFamily F G).Access where
  reader := BivariateTarskiSeedBits.reader (sourceAccess A B)
  degree_binary := bound_binary A B
  parameterDegree_binary := by
    have hN : BinaryFn (fun v => 2 * (bound F G v + 1)) :=
      (BinaryFn.const 2).mul ((bound_binary A B).add (BinaryFn.const 1))
    have hP : BinaryFn (fun v => F.parameterDegree (origin v)) := A.parameterDegree_binary.comp origin_FP
    have hQ : BinaryFn (fun v => G.parameterDegree (origin v)) := B.parameterDegree_binary.comp origin_FP
    exact (hN.mul hP).add (hQ.add hP)
  mass_binary := by
    have hN : BinaryFn (fun v => 2 * (bound F G v + 1)) :=
      (BinaryFn.const 2).mul ((bound_binary A B).add (BinaryFn.const 1))
    have hP := headMass_binary A
    have hQ := headMass_binary B
    have hD : BinaryFn (fun v => F.degree (origin v)) := A.degree_binary.comp origin_FP
    exact (((hN.mul (hP.add (BinaryFn.const 1))).add hQ).add hD.size).add hP

def headFamily (F : Family) : Family where
  polynomial v := F.polynomial (origin v)
  degree v := F.degree (origin v)
  parameterDegree v := F.parameterDegree (origin v)
  mass v := F.mass (origin v)
  polynomial_degree v := F.polynomial_degree (origin v)
  coefficient_degree v := F.coefficient_degree (origin v)
  coefficient_mass v := F.coefficient_mass (origin v)

def headAccess {F : Family} (A : F.Access) : (headFamily F).Access where
  reader := PolynomialPrincipalCoefficientBits.reindexReader (PolynomialPrincipalCoefficientBits.reindexReader A.reader)
  degree_binary := A.degree_binary.comp origin_FP
  parameterDegree_binary := A.parameterDegree_binary.comp origin_FP
  mass_binary := A.mass_binary.comp origin_FP

noncomputable def prepare (P : Readers) (F : Family) (u : List Bool) : List Bool :=
  pair u (BinaryNatCode.encode (degree P F u - 1))
theorem prepare_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (prepare P F) := by
  have E := ((degree_evaluator h A ha).postcompose BinaryNat.pred BinaryNat.pred_mem_FP).withInput
  exact E.congr (funext fun u => by simp only [Function.comp_apply, BinaryNat.pred_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)

end LeanCanny.Encoding.BoundedAlgebraicSlice.Tarski
