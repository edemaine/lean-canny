/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullDirectionQueries
public import LeanCanny.Encoding.FermatDirectionKernelCertificate
public import LeanCanny.Computation.SpaceFunctionQuantifiers

/-! # Native bounded direction selection for the full regular source

The checker scans every normalized complex critical-kernel chart of the full
source. Bounded search uses the actual fixed-width direction records, and
existence follows from the constructed source's regular pure-power form.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullDirectionChoice
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation
open LeanCanny.Geometry LeanCanny.Algebra BoundedFullWriter MvPolynomial Turing.MultiTapeTM
open LeanCanny.Encoding.Brackets
open scoped Classical

noncomputable def lower (P : Readers) (c : List Bool) : MvPolynomial (Fin (P.dim c + 4)) ℚ :=
  (rename (BoundedFullGeometry.inputIndex (P.dim c + 3))
    (IntegerRegularSource.lower (BoundedRegularSource.lower (original P c) (size P c) (size P c) (P.radius c))
      (degree P c) (BoundedRegularSource.sourceMassExponent (P.dim c) (size P c) (size P c) (P.radius c)))).map (Int.castRingHom ℚ)

noncomputable def leading (P : Readers) (c : List Bool) : ℚ :=
  IntegerRegularSource.leading (P.dim c + 3) 1 (degree P c)
    (BoundedRegularSource.sourceMassExponent (P.dim c) (size P c) (size P c) (P.radius c))

theorem polynomial_eq (P : Readers) (c : List Bool) :
    (BoundedFullGeometry.polynomial (original P c) (size P c) (size P c) (P.radius c)).map (Int.castRingHom ℚ) =
      FermatCriticalHomogenization.polynomial (lower P c) (leading P c) (degree P c) := by
  rw [BoundedFullGeometry.polynomial_eq, FermatCriticalHomogenization.map_polynomial]
  rfl

theorem lower_degree (P : Readers) (c : List Bool) : (lower P c).totalDegree < degree P c :=
  (PolynomialMapDegree.degree_le _ _).trans_lt ((totalDegree_rename_le _ _).trans_lt
    (IntegerRegularSource.lower_degree _ _ _
      (BoundedRegularSource.lower_degree _ _ _ _ (original_degree P c))))

theorem leading_ne_zero (P : Readers) (c : List Bool) : leading P c ≠ 0 := by
  change (IntegerRegularSource.leading (P.dim c + 3) 1 (degree P c)
    (BoundedRegularSource.sourceMassExponent (P.dim c) (size P c) (size P c) (P.radius c)) : ℚ) ≠ 0
  exact_mod_cast IntegerRegularSource.leading_ne_zero (n := P.dim c + 3) 1 (degree P c)
    (BoundedRegularSource.sourceMassExponent (P.dim c) (size P c) (size P c) (P.radius c)) one_ne_zero

theorem regular (P : Readers) (c : List Bool) (K : Type) [Field K] [Algebra ℚ K]
    (x : Fin (P.dim c + 4) → K)
    (hx : aeval x (FermatCriticalHomogenization.polynomial (lower P c) (leading P c) (degree P c)) = 0) :
    ∃ j, aeval x (pderiv j (FermatCriticalHomogenization.polynomial (lower P c) (leading P c) (degree P c))) ≠ 0 := by
  rw [← polynomial_eq] at hx ⊢
  have hmap : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K := RingHom.ext_int _ _
  change eval₂ (algebraMap ℚ K) x
    ((BoundedFullGeometry.polynomial (original P c) (size P c) (size P c) (P.radius c)).map (Int.castRingHom ℚ)) = 0 at hx
  rw [eval₂_map, hmap] at hx
  obtain ⟨j, hj⟩ := BoundedFullGeometry.generated_regular P c x hx
  refine ⟨j, ?_⟩
  change eval₂ (algebraMap ℚ K) x (pderiv j
    ((BoundedFullGeometry.polynomial (original P c) (size P c) (size P c) (P.radius c)).map (Int.castRingHom ℚ))) ≠ 0
  rw [pderiv_map, eval₂_map, hmap]
  exact hj

def Good (P : Readers) (c r : List Bool) : Prop :=
  ∀ chart : Fin (P.dim c + 4), ¬ CriticalKernel.FiniteBad (BoundedFullCriticalKernel.polynomial P c)
    (BoundedFullDirectionQueries.direction P (fun _ => r) c) chart

theorem exists_record (P : Readers) (c : List Bool) :
    ∃ r : List Bool, r.length = (P.dim c + 3) * BoundedFullDirectionQueries.width P c ∧ Good P c r := by
  obtain ⟨r, hr, hg⟩ := FermatCriticalDirection.exists_record_no_bad (lower P c) (leading P c)
    (leading_ne_zero P c) (degree P c) (lower_degree P c)
    (BoundedRegularSource.powerDegree_gt_one (size P c)) (regular P c)
  refine ⟨r, hr, ?_⟩
  have hp : (FermatCriticalHomogenization.polynomial (lower P c) (leading P c) (degree P c)).map (algebraMap ℚ ℂ) =
      BoundedFullCriticalKernel.polynomial P c := by
    rw [← polynomial_eq, map_map]
    rw [show (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ from RingHom.ext_int _ _]
    rfl
  rw [hp] at hg
  exact hg

def chart (P : Readers) (p : List Bool) : Fin (P.dim (pairFst p) + 4) :=
  ⟨min (pairSnd p).length (P.dim (pairFst p) + 3), by omega⟩

noncomputable def badData (source : List Bool) (dim radius : ℕ) (r : List Bool) (k : ℕ) : Prop :=
  let P : Readers := ⟨fun _ => source, fun _ => dim, fun _ => radius⟩
  CriticalKernel.FiniteBad (BoundedFullCriticalKernel.polynomial P [])
    (BoundedFullDirectionQueries.direction P (fun _ => r) [])
    ⟨min k (dim + 3), by change min k (dim + 3) < dim + 4; omega⟩

private theorem badData_eq (P : Readers) (c r : List Bool) (k : ℕ) (hk : k < P.dim c + 4) :
    badData (P.source c) (P.dim c) (P.radius c) r k ↔
      CriticalKernel.FiniteBad (BoundedFullCriticalKernel.polynomial P c)
        (BoundedFullDirectionQueries.direction P (fun _ => r) c) ⟨k, hk⟩ := by
  unfold badData
  simp only [Nat.min_eq_left (show k ≤ P.dim c + 3 by omega)]
  rfl

noncomputable def chartTest (P : Readers) (record : List Bool → List Bool) (p : List Bool) : List Bool :=
  [decide (¬ badData (P.source (pairFst p)) (P.dim (pairFst p)) (P.radius (pairFst p))
    (record (pairFst p)) (pairSnd p).length)]

theorem chart_evaluator {P : Readers} {record : List Bool → List Bool}
    (h : P.PolyTime) (hr : record ∈ FP)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (chartTest P record) := by
  have hi : UnaryFn (fun p => (chart P p).val) :=
    (UnaryFn.length pairSnd_mem_FP).min ((h.dim.comp pairFst_mem_FP).add (UnaryFn.const 3))
  have he := BoundedFullDirectionQueries.empty_evaluator (h.comp pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP hr) hi (fun p => ht (pairFst p))
  apply he.congr
  funext p
  simp only [BoundedFullCriticalKernel.polynomial_comp, BoundedFullDirectionQueries.direction_comp]
  rfl

noncomputable def check (P : Readers) (record : List Bool → List Bool) (c : List Bool) : List Bool :=
  [decide (∀ k < P.dim c + 4, chartTest P record (pair c (List.replicate k true)) = [true])]

theorem check_evaluator {P : Readers} {record : List Bool → List Bool}
    (h : P.PolyTime) (hr : record ∈ FP)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (check P record) :=
  (chart_evaluator h hr ht).forall_unary (h.dim.add (UnaryFn.const 4))

theorem check_correct (P : Readers) (record : List Bool → List Bool) (c : List Bool) :
    check P record c = [true] ↔ Good P c (record c) := by
  simp only [check, chartTest, List.cons.injEq, and_true, decide_eq_true_eq,
    pairFst_pair, pairSnd_pair, List.length_replicate]
  constructor
  · intro h i
    exact fun hb => h i.val i.isLt ((badData_eq P c (record c) i.val i.isLt).mpr hb)
  · intro h k hk
    exact fun hb => h ⟨k, hk⟩ ((badData_eq P c (record c) k hk).mp hb)

noncomputable def test (P : Readers) (p : List Bool × List Bool) : Bool :=
  decide (check (P.comp pairFst) pairSnd (pair p.1 p.2) = [true])

noncomputable def record (P : Readers) : List Bool → List Bool :=
  ImplicitGraph.findWord (test P) (fun c => (P.dim c + 3) * BoundedFullDirectionQueries.width P c)

theorem test_computable {P : Readers} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    ComputableInPolySpace (test P) (encPair encBits encBits) encBool := by
  have hc := check_evaluator (h.comp pairFst_mem_FP) pairSnd_mem_FP (fun p => ht (pairFst p))
  have hp := pair_computable (ComputableTidilyInPolyTime.fst encBits encBits)
    (ComputableTidilyInPolyTime.snd encBits encBits)
  have heq := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).computable
  have he := (ComputableInPolySpace.of_tidyPolyTime heq).comp (hc.computable.comp (.of_tidyPolyTime hp))
  apply he.congr
  intro p
  apply Bool.eq_iff_iff.mpr
  simp only [test, decide_eq_true_eq, id_eq]

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (record P) :=
  ⟨ImplicitGraph.findWord_computable (test_computable h ht) (BoundedFullDirectionQueries.recordLength_unary h)⟩

theorem record_length (P : Readers) (c : List Bool) :
    (record P c).length = (P.dim c + 3) * BoundedFullDirectionQueries.width P c :=
  ImplicitGraph.findWord_length _ _ _

private def goodData (source : List Bool) (dim radius : ℕ) (r : List Bool) : Prop :=
  Good ⟨fun _ => source, fun _ => dim, fun _ => radius⟩ [] r

private theorem goodData_eq (P : Readers) (c r : List Bool) :
    Good P c r = goodData (P.source c) (P.dim c) (P.radius c) r := rfl

theorem test_correct (P : Readers) (c r : List Bool) : test P (c, r) = true ↔ Good P c r := by
  simp only [test, decide_eq_true_eq, check_correct, goodData_eq]
  simp only [Readers.comp, Function.comp_apply, pairFst_pair, pairSnd_pair]

@[simp] theorem record_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) :
    record (P.comp f) c = record P (f c) := by
  unfold record
  apply ImplicitGraph.findWord_congr (c := c) (c' := f c)
    (width := fun z => ((P.comp f).dim z + 3) * BoundedFullDirectionQueries.width (P.comp f) z)
    (width' := fun z => (P.dim z + 3) * BoundedFullDirectionQueries.width P z) rfl
  intro r
  apply Bool.eq_iff_iff.mpr
  rw [test_correct, test_correct, goodData_eq, goodData_eq]
  rfl

theorem record_good (P : Readers) (c : List Bool) : Good P c (record P c) := by
  apply (test_correct P c _).mp
  apply ImplicitGraph.findWord_correct
  obtain ⟨r, hr, hg⟩ := exists_record P c
  exact ⟨r, hr, (test_correct P c r).mpr hg⟩

/-- The selected record is computed in space, so it is passed to a separate
polynomial-time query writer rather than treated as a polynomial-time reader. -/
theorem selected_encode_evaluator {P : Readers} {index : List Bool → ℕ}
    (h : P.PolyTime) (hi : UnaryFn index)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => encode (BoundedFullCriticalKernel.query P
      (BoundedFullDirectionQueries.direction P (record P) c) (index c) c)) := by
  have he := (evaluator h ht).withInput.postcompose
    (fun p => encode (BoundedFullCriticalKernel.query (P.comp pairFst)
      (BoundedFullDirectionQueries.direction (P.comp pairFst) pairSnd p) (index (pairFst p)) p))
    (BoundedFullDirectionQueries.encode_mem_FP (h.comp pairFst_mem_FP) pairSnd_mem_FP (hi.comp pairFst_mem_FP))
  apply he.congr
  funext c
  simp only [Function.comp_apply]
  rw [BoundedFullCriticalKernel.query_comp]
  simp only [pairFst_pair]
  congr 2
  apply BoundedFullDirectionQueries.direction_eq
  · simp only [Readers.comp, Function.comp_apply, pairFst_pair]
  · rw [BoundedFullDirectionQueries.degree_comp, pairFst_pair]
  · exact pairSnd_pair _ _

end LeanCanny.Encoding.BoundedFullDirectionChoice
