/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedSlackRootProperties
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # Slack characteristic polynomials ignore saved auxiliary fields

The original root and scalar-prefix birth determine the entire old bank.
Only the explicitly listed numerical slack parameters may vary with a key.
No sample words or roots are identified here.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedSlackSibling
open LeanCanny.Encoding IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (Plan family prefixLength)
open IntegralMixedFramedClearedMatrixBits (rank matrix)
open IntegralMixedFramedSlackMatrixBits (commonAt)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (u v : List Bool) (hr : pairFst u=pairFst v) (hb : prefixLength P u=prefixLength P v)

include hr hb in
theorem rank_eq : rank P D H u=rank P D H v :=by
  unfold IntegralMixedFramedClearedMatrixBits.rank
  simp only [IntegralMixedFramedHistoryFamilyBits.family_birth]
  change FixedWidthPolynomial.count (prefixLength P u) (P.width (pairFst u))=
    FixedWidthPolynomial.count (prefixLength P v) (P.width (pairFst v))
  rw [hr,hb]

private noncomputable def common (d : IntegralMixedFramedBankObservation.Data) : ℤ:=∏i,d.denominator i

include hr hb in
theorem common_eq : commonAt P D H u=commonAt P D H v :=by
  change common (IntegralMixedFramedBankObservation.ofState ((family P D H).state u))=
    common (IntegralMixedFramedBankObservation.ofState ((family P D H).state v))
  have HU : IntegralMixedFramedBankObservation.ofState ((family P D H).state u)=
      IntegralMixedFramedBankObservation.atRun P D (pairFst u) (prefixLength P u) (min_le_right _ _) :=rfl
  have HV : IntegralMixedFramedBankObservation.ofState ((family P D H).state v)=
      IntegralMixedFramedBankObservation.atRun P D (pairFst v) (prefixLength P v) (min_le_right _ _) :=rfl
  rw [HU,HV]
  exact congrArg common (IntegralMixedFramedBankObservation.atRun_congr P D _ _ _ _ hr hb _ _)

include hr hb in
theorem matrix_apply (i : ℕ) (r t : Fin (rank P D H u)) :
    matrix P D H u i r t=matrix P D H v i
      (Fin.cast (rank_eq P D H u v hr hb) r) (Fin.cast (rank_eq P D H u v hr hb) t) :=by
  simp only [matrix,IntegralMixedFramedClearedMatrixBits.Active,
    IntegralMixedFramedOldHeightBankBits.sourceEntry_root,Fin.val_cast,hr,hb]

private theorem matrix_heq_of_entries {a b : ℕ} (h : a=b)
    (M : Matrix (Fin a) (Fin a) ℤ) (N : Matrix (Fin b) (Fin b) ℤ)
    (he : ∀r t,M r t=N (Fin.cast h r) (Fin.cast h t)) : HEq M N :=by
  subst b
  apply heq_of_eq
  funext r t
  exact he r t

include hr hb in
theorem matrix_heq (i : ℕ) : HEq (matrix P D H u i) (matrix P D H v i) :=
  matrix_heq_of_entries (rank_eq P D H u v hr hb) _ _ (matrix_apply P D H u v hr hb i)

private noncomputable def spherePolynomial {r : ℕ} (M : ℕ→Matrix (Fin r) (Fin r) ℤ) (Q : ℤ) (N R : ℕ) :=
  Polynomial.expand ℤ 2 (ScaledGradedReductionAnnihilator.polynomial
    (((Q^2*((2 : ℤ)^R)^2 : ℤ) : Matrix (Fin r) (Fin r) ℤ)-∑i∈Finset.range N,M (N-i)^2) (Q^2) 1)
private noncomputable def regularPolynomial {r : ℕ} (M : ℕ→Matrix (Fin r) (Fin r) ℤ) (Q : ℤ) (N d R L K : ℕ) :=
  Polynomial.expand ℤ d (ScaledGradedReductionAnnihilator.polynomial
    ((((2 : ℤ)^L*Q^d*(2 : ℤ)^K+Q^d : ℤ) : Matrix (Fin r) (Fin r) ℤ)-
      (2 : ℤ)^L • (∑i∈Finset.range N,M (N-i)^d)-
      (2 : ℤ)^L • ((((Q^2*((2 : ℤ)^R)^2 : ℤ) : Matrix (Fin r) (Fin r) ℤ)-
        ∑i∈Finset.range N,M (N-i)^2)^(d/2))) ((2 : ℤ)^L*Q^d) 1)

private theorem sphere_congr {a b : ℕ} (h : a=b)
    (M : ℕ→Matrix (Fin a) (Fin a) ℤ) (N : ℕ→Matrix (Fin b) (Fin b) ℤ)
    (he : ∀i,HEq (M i) (N i)) (Q : ℤ) (count R : ℕ) :
    spherePolynomial M Q count R=spherePolynomial N Q count R :=by
  subst b
  have HM : M=N:=funext (fun i=>eq_of_heq (he i))
  subst N
  rfl
private theorem regular_congr {a b : ℕ} (h : a=b)
    (M : ℕ→Matrix (Fin a) (Fin a) ℤ) (N : ℕ→Matrix (Fin b) (Fin b) ℤ)
    (he : ∀i,HEq (M i) (N i)) (Q : ℤ) (count d R L K : ℕ) :
    regularPolynomial M Q count d R L K=regularPolynomial N Q count d R L K :=by
  subst b
  have HM : M=N:=funext (fun i=>eq_of_heq (he i))
  subst N
  rfl

include hr hb in
theorem sphere_polynomial (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (N R : List Bool→ℕ) (hN : N u=N v) (hR : R u=R v) :
    (IntegralMixedFramedSlackRootBits.sphereSource P D H s hs N R).polynomial u=
      (IntegralMixedFramedSlackRootBits.sphereSource P D H s hs N R).polynomial v :=by
  rw [IntegralMixedFramedSlackRootBits.sphere_polynomial,IntegralMixedFramedSlackRootBits.sphere_polynomial]
  change spherePolynomial (matrix P D H u) (commonAt P D H u) (N u) (R u)=
    spherePolynomial (matrix P D H v) (commonAt P D H v) (N v) (R v)
  rw [common_eq P D H u v hr hb,hN,hR]
  exact sphere_congr (rank_eq P D H u v hr hb) _ _ (matrix_heq P D H u v hr hb) _ _ _

include hr hb in
theorem regular_polynomial (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (N d R L K : List Bool→ℕ) (hN : N u=N v) (hd : d u=d v) (hR : R u=R v)
    (hL : L u=L v) (hK : K u=K v) :
    (IntegralMixedFramedSlackRootBits.regularSource P D H s hs N d R L K).polynomial u=
      (IntegralMixedFramedSlackRootBits.regularSource P D H s hs N d R L K).polynomial v :=by
  rw [IntegralMixedFramedSlackRootBits.regular_polynomial,IntegralMixedFramedSlackRootBits.regular_polynomial]
  change regularPolynomial (matrix P D H u) (commonAt P D H u) (N u) (d u) (R u) (L u) (K u)=
    regularPolynomial (matrix P D H v) (commonAt P D H v) (N v) (d v) (R v) (L v) (K v)
  rw [common_eq P D H u v hr hb,hN,hd,hR,hL,hK]
  exact regular_congr (rank_eq P D H u v hr hb) _ _ (matrix_heq P D H u v hr hb) _ _ _ _ _ _
end LeanCanny.Algebra.IntegralMixedFramedSlackSibling
