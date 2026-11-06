/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordPointEqualityBounds
public import LeanCanny.Encoding.CoefficientMarkedRecordCompanionMetadata
public import LeanCanny.Encoding.CoefficientMarkedRecordRootBranches
/-! # Native physical equality tests on the actual complete root tuple -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordPointEqualityQuery
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial Set
open LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem rename_heq {m n : ℕ} (h : m = n) (p : MvPolynomial (Fin m) ℤ) :
    HEq (MvPolynomial.rename (Fin.cast h) p) p := by
  cases h
  change HEq (MvPolynomial.rename id p) p
  rw [MvPolynomial.rename_id]
  rfl

private theorem tuple_heq {m k n : ℕ} (hmk : m = k) (hmn : m = n)
    (f : Fin k → ℝ) (z : Fin n → ℝ) (hj : HEq f z) :
    HEq (fun i : Fin m => f (Fin.cast hmk i)) z := by
  cases hmk
  cases hmn
  exact hj

private theorem evaluate_heq {m n : ℕ} (h : m = n) (p : MvPolynomial (Fin m) ℤ)
    (q : MvPolynomial (Fin n) ℤ) (hp : HEq p q) (z : Fin m → ℝ) (w : Fin n → ℝ) (hz : HEq z w) :
    p.eval₂ (Int.castRingHom ℝ) z = q.eval₂ (Int.castRingHom ℝ) w := by
  cases h
  cases eq_of_heq hp
  cases eq_of_heq hz
  rfl

private theorem count_constants (P : Parameters) (T : IntegralMixedHeaderTablesBits.Tables)
    (key : List Bool → List Bool) (q : List Bool) :
    IntegralMixedFramedCriticalGuardBits.count P T key q =
      IntegralMixedFramedCriticalGuardBits.count P T (fun _ => key q) [] := rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
local notation "T" => IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.tables CoefficientMarkedRecordRows.symbolic
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedSourceIntegerRecordAppend.plan
  IntegralMixedSourceIntegerRecordAppend.data IntegralMixedAuxiliaryMarkedIntegerPlan.seed

theorem integer_native (ctx aux : List Bool) (a b i : ℕ) :
    HEq (integer hn ht ha ctx a b i)
      (IntegralMixedFramedPointEqualityBits.polynomial (B).parameters T
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralMixedPhysicalPointEquality.left
        IntegralMixedPhysicalPointEquality.right IntegralMixedPhysicalPointEquality.coordinate
        (pair (pair ctx aux) (IntegralMixedPhysicalPointEquality.datum a b i))) :=
  (rename_heq (CoefficientMarkedRecordCriticalFullQuery.count_eq hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] 0)
    (raw hn ht ha ctx a b i)).trans (raw_packet hn ht ha hR ctx aux a b i)

theorem native_count (ctx aux : List Bool) (a b i : ℕ) :
    IntegralMixedFramedCriticalGuardBits.count (B).parameters T (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key)
      (pair (pair ctx aux) (IntegralMixedPhysicalPointEquality.datum a b i)) =
        (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count := by
  have HM := congrArg CoefficientCriticalCorrelationQuery.Metadata.count
    (CoefficientMarkedRecordCriticalQuery.metadata_eq hn ht ha ctx hR (IntegralMixedCausalRecordPlanBits.count ctx) [] 0)
  have HC := CoefficientMarkedRecordCriticalFullQuery.count_eq hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] 0
  have HK : IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key
      (pair (pair ctx aux) (IntegralMixedPhysicalPointEquality.datum a b i)) = key (n := n) ctx := by
    simp only [IntegralFramedPhysicalCriticalGuardTest.keyDatum, pairFst_pair]
    exact native_key hn ht ha hR ctx aux
  have HP := count_constants (B).parameters T (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key)
    (pair (pair ctx aux) (IntegralMixedPhysicalPointEquality.datum a b i))
  rw [HK] at HP
  exact HP.trans (HM.symm.trans HC)

attribute [local irreducible] SquareSampleCompleteVertices.Valid SquareSampleCompleteVertices.candidate
  IntegralFramedPhysicalPointEqualityTest.value IntegralMixedPhysicalPointEquality.value

/-- Literal native value on the OWN full word. Each creating birth keeps its
own physical power; the coordinate is the actual arbitrary ambient selector. -/
theorem value_eq (ctx aux w : List Bool) (a b i : ℕ)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (pair ctx aux) w)
    (z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (pair ctx aux) w hw).val z) :
    IntegralMixedPhysicalPointEquality.value hn ht ha hR false
      (pair (pair (pair ctx aux) w) (IntegralMixedPhysicalPointEquality.datum a b i)) =
      InfinitesimalSign.encode (SignType.sign ((integer hn ht ha ctx a b i).eval₂ (Int.castRingHom ℝ) z)) := by
  have HC := native_count hn ht ha hR ctx aux a b i
  have HP := integer_native hn ht ha hR ctx aux a b i
  have HZ := tuple_heq (IntegralMixedPhysicalGuardScan.count_eq hn ht ha hR false (pair ctx aux) (IntegralMixedPhysicalPointEquality.datum a b i))
    HC _ z hj
  have HE := evaluate_heq HC _ _ HP.symm _ z HZ
  have HV := IntegralFramedPhysicalPointEqualityTest.packet (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
    (B).parameters T (B).key IntegralMixedPhysicalPointEquality.left IntegralMixedPhysicalPointEquality.right IntegralMixedPhysicalPointEquality.coordinate
    (IntegralMixedPhysicalGuardScan.count_eq hn ht ha hR false) (pair ctx aux) w (IntegralMixedPhysicalPointEquality.datum a b i) hw
  unfold IntegralMixedPhysicalPointEquality.value
  exact HV.trans (congrArg (fun x : ℝ => InfinitesimalSign.encode (SignType.sign x)) HE)

private theorem admissible_planned (P : Parameters) (TT : IntegralMixedHeaderTablesBits.Tables)
    (L F C : List Bool → ℕ) (key : List Bool → List Bool) (a b i : List Bool → ℕ) (q : List Bool) :
    IntegralMixedFramedPointEqualityBits.Admissible (IntegralMixedFramedNormalizationBits.planned P L F C) TT key a b i q ↔
      IntegralMixedFramedPointEqualityBits.Admissible P TT key a b i q := Iff.rfl

private theorem admissible_constants (P : Parameters) (TT : IntegralMixedHeaderTablesBits.Tables)
    (key : List Bool → List Bool) (a b i : List Bool → ℕ) (q : List Bool) :
    IntegralMixedFramedPointEqualityBits.Admissible P TT key a b i q ↔
      IntegralMixedFramedPointEqualityBits.Admissible P TT (fun _ => key q)
        (fun _ => a q) (fun _ => b q) (fun _ => i q) [] := Iff.rfl

theorem admissible_static (ctx aux w : List Bool) (a b i : ℕ) :
    IntegralMixedPhysicalPointEquality.Admissible hn ht ha hR false
      (pair (pair (pair ctx aux) w) (IntegralMixedPhysicalPointEquality.datum a b i)) ↔
    IntegralMixedFramedPointEqualityBits.Admissible (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) (fun _ => key (n := n) ctx)
      (fun _ => a) (fun _ => b) (fun _ => i) [] := by
  unfold IntegralMixedPhysicalPointEquality.Admissible IntegralMixedPhysicalPointEquality.context
  simp only [pairFst_pair, pairSnd_pair]
  rw [CoefficientMarkedRecordCriticalMetadata.tables_eq hn ht ha hR]
  have H := admissible_constants (B).parameters (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha)
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key)
    IntegralMixedPhysicalPointEquality.left IntegralMixedPhysicalPointEquality.right IntegralMixedPhysicalPointEquality.coordinate
    (pair (pair ctx aux) (IntegralMixedPhysicalPointEquality.datum a b i))
  have HK : IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key
      (pair (pair ctx aux) (IntegralMixedPhysicalPointEquality.datum a b i)) = key (n := n) ctx := by
    simp only [IntegralFramedPhysicalCriticalGuardTest.keyDatum, pairFst_pair]
    exact native_key hn ht ha hR ctx aux
  rw [HK, (IntegralMixedPhysicalPointEquality.datum_fields (pair ctx aux) a b i).1,
    (IntegralMixedPhysicalPointEquality.datum_fields (pair ctx aux) a b i).2.1,
    (IntegralMixedPhysicalPointEquality.datum_fields (pair ctx aux) a b i).2.2] at H
  exact H.trans (admissible_planned (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (fun _ => key (n := n) ctx) (fun _ => a) (fun _ => b) (fun _ => i) [])

variable {S : List Bool → ℕ} (hS : BinaryFn S)

theorem admissible_eq (ctx auxR auxS wR wS : List Bool) (a b i : ℕ) :
    IntegralMixedPhysicalPointEquality.Admissible hn ht ha hR false
      (pair (pair (pair ctx auxR) wR) (IntegralMixedPhysicalPointEquality.datum a b i)) ↔
    IntegralMixedPhysicalPointEquality.Admissible hn ht ha hS false
      (pair (pair (pair ctx auxS) wS) (IntegralMixedPhysicalPointEquality.datum a b i)) :=
  (admissible_static hn ht ha hR ctx auxR wR a b i).trans (admissible_static hn ht ha hS ctx auxS wS a b i).symm

theorem value_on_curve (ctx auxR auxS : List Bool) (s t i : ℕ)
    (hs : s ≤ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx+1)
    (ht0 : t ≤ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx+1)
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u))
    (u v : Ioo a b) (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (pair ctx auxR) wR)
    (hwS : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (pair ctx auxS) wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (pair ctx auxR) wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (pair ctx auxS) wS hwS).val (x v)) :
    IntegralMixedPhysicalPointEquality.value hn ht ha hR false
      (pair (pair (pair ctx auxR) wR) (IntegralMixedPhysicalPointEquality.datum s t i)) =
    IntegralMixedPhysicalPointEquality.value hn ht ha hS false
      (pair (pair (pair ctx auxS) wS) (IntegralMixedPhysicalPointEquality.datum s t i)) := by
  have HR := value_eq hn ht ha hR ctx auxR wR s t i hwR (x u) hjR
  have HS := value_eq hn ht ha hS ctx auxS wS s t i hwS (x v) hjS
  exact HR.trans ((congrArg InfinitesimalSign.encode (sign_on_root_curve hn ht ha ctx s t i hs ht0 ha0 x hx u v)).trans HS.symm)

/-- The actual accepted packet, including activity and ambient-coordinate
admissibility, is invariant on any shared full-row curve. No radius-function
or sampled-word equality is required. -/
theorem accepted_on_curve (ctx auxR auxS : List Bool) (s t i : ℕ)
    (hs : s ≤ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx+1)
    (ht0 : t ≤ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx+1)
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u))
    (u v : Ioo a b) (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (pair ctx auxR) wR)
    (hwS : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (pair ctx auxS) wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (pair ctx auxR) wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (pair ctx auxS) wS hwS).val (x v)) :
    IntegralMixedPhysicalPointEquality.Accepted hn ht ha hR false
      (pair (pair (pair ctx auxR) wR) (IntegralMixedPhysicalPointEquality.datum s t i)) ↔
    IntegralMixedPhysicalPointEquality.Accepted hn ht ha hS false
      (pair (pair (pair ctx auxS) wS) (IntegralMixedPhysicalPointEquality.datum s t i)) := by
  have HV := value_on_curve hn ht ha hR hS ctx auxR auxS s t i hs ht0 ha0 x hx u v wR wS hwR hwS hjR hjS
  have HA := admissible_eq hn ht ha hR hS ctx auxR auxS wR wS s t i
  simp only [IntegralMixedPhysicalPointEquality.Accepted,
    IntegralMixedPhysicalPointEquality.wellformed_packet, true_and, HA, HV]

end LeanCanny.Encoding.CoefficientMarkedRecordPointEqualityQuery
