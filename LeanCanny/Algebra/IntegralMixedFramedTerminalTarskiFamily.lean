/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateOuterBounds
public import LeanCanny.Algebra.FixedWidthBivariateParameterPairSpace
public import LeanCanny.Algebra.MultivariateTarskiDegreeBounds
/-! # The actual delta/epsilon principal circuit and its whole-output box

All degree inequalities hold for the stored polynomial, including malformed
or truncated inputs. Full-annihilator identification remains a separate
selected-parent statement; no such identification is used for native costs.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiFamilyBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (d e center selected : List Bool→ℕ)

noncomputable def arity (c : List Bool) :=(atKey P D H (terminal c)).count
noncomputable def head (negative : Bool) :=FixedWidthBivariateParameterPairBits.lift true (arity P D H terminal)
  (IntegralMixedFramedTerminalTarskiHeadBits.head P D H L F C hs parent terminal d e center negative)
noncomputable def baseQuery (negative : Bool) :=FixedWidthBivariateParameterPairBits.lift false (arity P D H terminal)
  (IntegralMixedFramedWindowQuery.polynomial P D H L F C hs terminal selected negative)
noncomputable def query (power : List Bool→Fin 3) (negative : Bool) (c : List Bool) :=
  baseQuery P D H L F C hs terminal selected negative c^(power c).val

noncomputable def headBound :=IntegralMixedFramedTerminalTarskiHeadBits.degreeBound P D H L F C hs parent terminal e center
noncomputable def windowBound (c : List Bool) :=
  (IntegralMixedFramedWindowQuery.family P D H L F C hs terminal selected).weight c+1
noncomputable def queryBound (c : List Bool) :=2*windowBound P D H L F C hs terminal selected c

def degree (d : List Bool→ℕ) (c : List Bool) :=max 1 (d c)
def inputBound (d : List Bool→ℕ) (c : List Bool) :=degree d c+2
def seedDegree (d : List Bool→ℕ) (c : List Bool) :=degree d c-1

noncomputable def principalBound (c : List Bool) :=MultivariateTarskiDegreeBounds.principalDegreeBound
  (degree d c) (seedDegree d c) (inputBound d c)
  (headBound P D H L F C hs parent terminal e center c) (queryBound P D H L F C hs terminal selected c)
noncomputable def wholeBound (c : List Bool) :=headBound P D H L F C hs parent terminal e center c+
  queryBound P D H L F C hs terminal selected c+principalBound P D H L F C hs parent terminal d e center selected c
noncomputable def width (c : List Bool) :=(wholeBound P D H L F C hs parent terminal d e center selected c).size

theorem head_coefficient_degree (negative : Bool) (c : List Bool) (y : ℕ) :
    ((head P D H L F C hs parent terminal d e center negative c).coeff y).totalDegree≤
      headBound P D H L F C hs parent terminal e center c :=
  (FixedWidthBivariateParameterPairBits.degree true _ _ c y).trans
    (IntegralMixedFramedTerminalTarskiHeadBits.coefficient_degree P D H L F C hs parent terminal d e center negative c y)

private theorem pow_coefficient_degree {σ : Type*} (p : Polynomial (MvPolynomial σ ℤ)) (D : ℕ)
    (hp : ∀ i,(p.coeff i).totalDegree≤D) (k : ℕ) : ∀ i,((p^k).coeff i).totalDegree≤k*D :=by
  induction k with
  | zero =>
    intro i
    simp only [pow_zero,Polynomial.coeff_one,Nat.zero_mul]
    split_ifs <;> simp
  | succ k ih =>
    intro i
    rw [pow_succ]
    exact (MultivariateTarskiDegreeBounds.mul_coefficient _ _ (k*D) D ih hp i).trans_eq (by ring)

theorem query_coefficient_degree (power : List Bool→Fin 3) (negative : Bool) (c : List Bool) (y : ℕ) :
    ((query P D H L F C hs terminal selected power negative c).coeff y).totalDegree≤
      queryBound P D H L F C hs terminal selected c :=by
  have HC (i : ℕ) : ((baseQuery P D H L F C hs terminal selected negative c).coeff i).totalDegree≤
      windowBound P D H L F C hs terminal selected c :=
    (FixedWidthBivariateParameterPairBits.degree false _ _ c i).trans
      (IntegralMixedFramedWindowQuery.coefficient_degree P D H L F C hs terminal selected negative c i)
  exact (pow_coefficient_degree _ _ HC (power c).val y).trans
    (Nat.mul_le_mul_right _ (by have HH:=(power c).isLt;omega))

theorem head_outer_degree (negative : Bool) (c : List Bool) :
    (head P D H L F C hs parent terminal d e center negative c).natDegree≤d c :=
  Polynomial.natDegree_map_le.trans
    (IntegralMixedFramedCoordinateOuterBounds.shifted_outer_degree P D H L F C hs parent terminal d e center negative c)

theorem query_outer_degree (power : List Bool→Fin 3) (negative : Bool) (c : List Bool) :
    (query P D H L F C hs terminal selected power negative c).natDegree≤2 :=by
  have HQ : (baseQuery P D H L F C hs terminal selected negative c).natDegree≤1 :=
    Polynomial.natDegree_map_le.trans (RationalMonomialWindowQuery.degree _ negative c)
  exact Polynomial.natDegree_pow_le.trans ((Nat.mul_le_mul_left _ HQ).trans
    (by have HH:=(power c).isLt;omega))

noncomputable def family (power : List Bool→Fin 3) (negativeEta negativeEpsilon : Bool) : FixedWidthTarskiPrincipalBits.Family where
  arity c:=1+(arity P D H terminal c+1)
  width:=width P D H L F C hs parent terminal d e center selected
  head:=head P D H L F C hs parent terminal d e center negativeEta
  query:=query P D H L F C hs terminal selected power negativeEpsilon
  degree:=degree d
  bound:=inputBound d
  seedDegree:=seedDegree d
  degree_pos c:=lt_of_lt_of_le (by decide : 0<1) (Nat.le_max_left _ _)
  degree_le c:=by simp only [inputBound];omega
  input_degree c:=by
    have HQ:=query_outer_degree P D H L F C hs terminal selected power negativeEpsilon c
    have HH:=head_outer_degree P D H L F C hs parent terminal d e center negativeEta c
    have HD:=Polynomial.natDegree_derivative_le
      (head P D H L F C hs parent terminal d e center negativeEta c)
    exact Polynomial.natDegree_mul_le.trans (by
      change _≤max 1 (d c)+2
      omega)

theorem principal_degree (power : List Bool→Fin 3) (negativeEta negativeEpsilon : Bool) (c : List Bool) (j : ℕ) :
    (FixedWidthTarskiPrincipalBits.polynomial
      (family P D H L F C hs parent terminal d e center selected power negativeEta negativeEpsilon) c j).totalDegree≤
        wholeBound P D H L F C hs parent terminal d e center selected c :=
  (MultivariateTarskiDegreeBounds.principal_seed _ _ _ _ j _ _ _
    (head_coefficient_degree P D H L F C hs parent terminal d e center negativeEta c)
    (query_coefficient_degree P D H L F C hs terminal selected power negativeEpsilon c)).trans
      (Nat.le_add_left _ _)

end LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiFamilyBits
