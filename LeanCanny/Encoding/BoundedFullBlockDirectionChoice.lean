/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullBlockData
public import LeanCanny.Encoding.FermatCommonCriticalDirection
public import LeanCanny.Geometry.FermatCriticalRegularity
public import LeanCanny.ETR.NumericLiteralFP

/-! # Native direction selection for blocks of the shared regular source

The constructed source's degree and the actual parent sample-count width
bound the record search. The native shared-circuit validator checks every
critical root over every actual parent. Contained blocks inherit pure-power
shape and degree bounds, so coefficient-field slice regularity suffices for
success without a shape witness, expanded source term, or successful record.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullBlockDirectionChoice
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open LeanCanny.ETR.ComplexCircuit BoundedFullWriter MvPolynomial Turing.MultiTapeTM
open LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair pairFst pairSnd

structure Inputs where
  parent : Readers
  source : Readers
  offset : List Bool → ℕ
  free : List Bool → ℕ

structure Inputs.PolyTime (F : Inputs) : Prop where
  parent : F.parent.PolyTime
  source : F.source.PolyTime
  offset : BinaryFn F.offset
  free : UnaryFn F.free

noncomputable def width (F : Inputs) (c : List Bool) : ℕ :=
  Algebra.FermatCommonCriticalDirection.binaryWidth (F.free c) (degree F.source c)
    (BoundedFullCriticalSamples.labelWidth F.parent c)

noncomputable def recordLength (F : Inputs) (c : List Bool) : ℕ := F.free c * width F c

theorem width_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (width F) :=
  FermatCommonCriticalDirection.binaryWidth_unary h.free (degree_binary h.source)
    (BoundedFullCriticalSamples.labelWidth_unary h.parent)

theorem recordLength_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (recordLength F) := h.free.mul (width_unary h)

noncomputable def direction (F : Inputs) (c r : List Bool) (i : ℕ) : ℤ :=
  FixedWidthQuery.coordinate (width F) (fun _ => r) c i

noncomputable def base (F : Inputs) : BoundedFullBlockKernel.Inputs :=
  ⟨F.source, F.offset, F.free, fun _ _ => 0, fun _ => .falsum⟩

noncomputable def family (F : Inputs) : BoundedFullBlockKernel.Inputs where
  source := F.source.comp pairFst
  offset := F.offset ∘ pairFst
  free := F.free ∘ pairFst
  direction q i := FixedWidthQuery.coordinate (width F ∘ pairFst) pairSnd q i
  condition _ := .falsum

theorem family_polyTime {F : Inputs} (h : F.PolyTime) : (family F).PolyTime := by
  refine ⟨h.source.comp pairFst_mem_FP, h.offset.comp pairFst_mem_FP,
    h.free.comp pairFst_mem_FP, ?_, constFn_mem_FP Formula.falsum.encode⟩
  have hw := ((width_unary h).comp pairFst_mem_FP).comp pairFst_mem_FP
  have hb := take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
    ((UnaryFn.length pairSnd_mem_FP).mul hw)) hw
  exact mem_FP_of_eq (Term.negNat_toBits_mem_FP (BinaryFn.fromBits hb)) (fun _ => rfl)

def Good (F : Inputs) (c r : List Bool) : Prop :=
  BoundedFullBlockData.Good F.parent c (F.source.source c) (F.source.dim c) (F.source.radius c)
    (F.offset c) (F.free c) (direction F c r)

noncomputable def test (F : Inputs) (p : List Bool × List Bool) : Bool :=
  decide (BoundedFullBlockRegularity.Good (F.parent.comp pairFst) (family F) (pair p.1 p.2))

theorem test_correct (F : Inputs) (c r : List Bool) : test F (c, r) = true ↔ Good F c r := by
  simp only [test, decide_eq_true_eq, BoundedFullBlockData.data_comp_iff]
  have hd : (family F).direction (pair c r) = direction F c r := by
    funext i
    simp only [family, direction, FixedWidthQuery.coordinate, Function.comp_apply, pairFst_pair, pairSnd_pair]
  rw [hd]
  simp only [Good, family, Readers.comp, Function.comp_apply, pairFst_pair]

theorem test_computable {F : Inputs} (h : F.PolyTime)
    (htP : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c)
    (htS : ∀ c, (TermView.term (F.source.source c)).arity ≤ F.source.dim c) :
    ComputableTidilyInPolySpace (test F) (encPair encBits encBits) encBool := by
  have hc := BoundedFullBlockRegularity.evaluator (h.parent.comp pairFst_mem_FP) (family_polyTime h)
    (fun q => htP (pairFst q)) (fun q => htS (pairFst q))
  have hp := pair_computable (ComputableTidilyInPolyTime.fst encBits encBits)
    (ComputableTidilyInPolyTime.snd encBits encBits)
  have heq := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).computable
  have he := (ComputableTidilyInPolySpace.of_polyTime heq).comp (hc.computable.comp (.of_polyTime hp))
  apply he.congr
  intro p
  apply Bool.eq_iff_iff.mpr
  simp only [test, decide_eq_true_eq, id_eq, List.cons.injEq, and_true]

noncomputable def record (F : Inputs) : List Bool → List Bool :=
  ImplicitGraph.findWord (test F) (recordLength F)

theorem evaluator {F : Inputs} (h : F.PolyTime)
    (htP : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c)
    (htS : ∀ c, (TermView.term (F.source.source c)).arity ≤ F.source.dim c) : SpaceFunction (record F) :=
  ⟨ImplicitGraph.findWord_computable (test_computable h htP htS) (recordLength_unary h)⟩

theorem record_length (F : Inputs) (c : List Bool) : (record F c).length = recordLength F c :=
  ImplicitGraph.findWord_length _ _ _

noncomputable def selected (F : Inputs) : BoundedFullBlockKernel.Inputs :=
  ⟨F.source, F.offset, F.free, fun c => direction F c (record F c), fun _ => .falsum⟩

theorem selected_good_iff (F : Inputs) (c : List Bool) :
    BoundedFullBlockRegularity.Good F.parent (selected F) c ↔ Good F c (record F c) :=
  BoundedFullBlockData.data_iff F.parent (selected F) c

private def queryPacket (z : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst z)) (pairSnd z)) (pairSnd (pairFst z))

private theorem queryPacket_FP : queryPacket ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def read (F : Inputs) (q : List Bool) : List Bool :=
  FermatCommonCriticalDirection.read F.free (degree F.source) (BoundedFullCriticalSamples.labelWidth F.parent)
    (pair (pair (pairFst q) (record F (pairFst q))) (pairSnd q))

theorem read_evaluator {F : Inputs} (h : F.PolyTime)
    (htP : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c)
    (htS : ∀ c, (TermView.term (F.source.source c)).arity ≤ F.source.dim c) : SpaceFunction (read F) := by
  have hr := FermatCommonCriticalDirection.read_FP h.free (degree_binary h.source)
    (BoundedFullCriticalSamples.labelWidth_unary h.parent)
  have H := (evaluator h htP htS).call pairFst
    (FermatCommonCriticalDirection.read F.free (degree F.source) (BoundedFullCriticalSamples.labelWidth F.parent) ∘ queryPacket)
    pairFst_mem_FP (mem_FP_comp queryPacket_FP hr)
  exact H.congr (funext fun q => by simp only [Function.comp_apply, queryPacket, pairFst_pair, pairSnd_pair, read])

theorem read_packet (F : Inputs) (c : List Bool) (i : ℕ) (hi : i < F.free c) :
    read F (pair c (BinaryNatCode.encode i)) =
      BinaryNatCode.encode (FixedWidthQuery.coordinate (width F) (record F) c i) := by
  simp only [read, pairFst_pair, pairSnd_pair,
    FermatCommonCriticalDirection.read_packet _ _ _ _ _ i hi]
  rfl

private theorem source_start_comp (S : Readers) (f : List Bool → List Bool) (c : List Bool) :
    BoundedFullWriter.start (S.comp f) c = BoundedFullWriter.start S (f c) := rfl

private theorem source_program_comp (S : Readers) (f : List Bool → List Bool) (c : List Bool) :
    BoundedFullWriter.program (S.comp f) c = BoundedFullWriter.program S (f c) := rfl

private theorem source_output_comp (S : Readers) (f : List Bool → List Bool) (c : List Bool) :
    BoundedFullWriter.output (S.comp f) c = BoundedFullWriter.output S (f c) := rfl

theorem query_packet (F : Inputs) (c : List Bool) (i : ℕ) :
    SharedKernel.query (BoundedFullBlockKernel.native (family F)) (pair c (record F c)) i =
      SharedKernel.query (BoundedFullBlockKernel.native (selected F)) c i := by
  simp only [SharedKernel.query, SharedKernel.dim, BoundedFullBlockKernel.native, BoundedFullBlockKernel.start,
    BoundedFullBlockKernel.dim, family, selected, Function.comp_apply, source_start_comp, source_program_comp,
    source_output_comp, pairFst_pair, FixedWidthQuery.coordinate, pairSnd_pair]
  rfl

noncomputable def query (F : Inputs) (chart : List Bool → ℕ) (c : List Bool) : List Bool :=
  encode (SharedKernel.query (BoundedFullBlockKernel.native (selected F)) c (chart c))

theorem query_evaluator {F : Inputs} (h : F.PolyTime) {chart : List Bool → ℕ} (hi : UnaryFn chart)
    (htP : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c)
    (htS : ∀ c, (TermView.term (F.source.source c)).arity ≤ F.source.dim c) : SpaceFunction (query F chart) := by
  have H := BoundedFullBlockKernel.native_polyTime (family_polyTime h)
  let write := fun q => encode (SharedKernel.query (BoundedFullBlockKernel.native (family F)) q (chart (pairFst q)))
  have hw : write ∈ FP := CriticalKernel.query_encode_mem_FP H.start (SharedKernel.dim_unary H) H.output
    (hi.comp pairFst_mem_FP) H.length H.gates H.direction
  apply ((evaluator h htP htS).withInput.postcompose write hw).congr
  funext c
  simp only [Function.comp_apply, write, pairFst_pair, query_packet, query]

theorem record_good_of_exists (F : Inputs) (c : List Bool)
    (hex : ∃ r : List Bool, r.length = recordLength F c ∧ Good F c r) : Good F c (record F c) := by
  apply (test_correct F c _).mp
  apply ImplicitGraph.findWord_correct
  obtain ⟨r, hr, hg⟩ := hex
  exact ⟨r, hr, (test_correct F c r).mpr hg⟩

noncomputable def slice (F : Inputs) (c : List Bool) (p : BoundedFullCriticalSamples.Samples F.parent c) :=
  BoundedFullBlockKernel.slice (base F) c (Formula.extend p.val)

def SliceRegular (F : Inputs) (c : List Bool) : Prop :=
  ∀ p : BoundedFullCriticalSamples.Samples F.parent c,
    ∀ (L : Type) [Field L] [Algebra ℝ L] (x : Fin (F.free c + 1) → L),
      aeval x (slice F c p) = 0 → ∃ j, aeval x (pderiv j (slice F c p)) ≠ 0

theorem exists_record (F : Inputs) (c : List Bool)
    (hfit : F.offset c + (F.free c + 1) ≤ F.source.dim c + 4) (hregular : SliceRegular F c) :
    ∃ r : List Bool, r.length = recordLength F c ∧ Good F c r := by
  let low := fun p : BoundedFullCriticalSamples.Samples F.parent c =>
    BoundedFullBlockKernel.lower (base F) c (Formula.extend p.val)
  let a : ℝ := BoundedFullBlockKernel.fullLeading (base F) c
  have ha : a ≠ 0 := Int.cast_ne_zero.mpr (BoundedFullBlockKernel.fullLeading_ne_zero (base F) c)
  have hs (p : BoundedFullCriticalSamples.Samples F.parent c) :
      slice F c p = FermatCriticalHomogenization.polynomial (low p) a (degree F.source c) :=
    BoundedFullBlockKernel.slice_fermat (base F) c (Formula.extend p.val) hfit
  have hN : 1 < degree F.source c := BoundedRegularSource.powerDegree_gt_one (size F.source c)
  have hreg (p : BoundedFullCriticalSamples.Samples F.parent c)
      (L : Type) [Field L] [Algebra ℝ L] (x : Fin (F.free c + 1) → L)
      (hx : aeval x (FermatCriticalHomogenization.polynomial (low p) a (degree F.source c)) = 0) :
      ∃ j, aeval x (pderiv j (FermatCriticalHomogenization.polynomial (low p) a (degree F.source c))) ≠ 0 := by
    rw [← hs p] at hx ⊢
    exact hregular p L x hx
  obtain ⟨r, hr, hg⟩ := FermatCommonCriticalDirection.exists_parent_record F.parent c low (fun _ => a)
    (fun _ => ha) (degree F.source c) (fun p => BoundedFullBlockKernel.lower_degree (base F) c (Formula.extend p.val))
    hN hreg
  refine ⟨r, hr, ?_⟩
  intro p y hy
  let v := fun i : Fin (F.free c) =>
    (FermatCommonCriticalDirection.assignment (F.free c) (degree F.source c)
      (BoundedFullCriticalSamples.labelWidth F.parent c) r i : ℝ)
  have he : BoundedFullBlockData.rows (F.source.source c) (F.source.dim c) (F.source.radius c)
      (F.offset c) (F.free c) (direction F c r) p.val =
        CriticalKernel.finiteRows (FermatCriticalHomogenization.polynomial (low p) a (degree F.source c)) v := by
    change CriticalKernel.finiteRows (slice F c p) (fun i => (direction F c r i.val : ℝ)) = _
    rw [hs p]
    congr 1
  change (∀ i, (BoundedFullBlockData.rows (F.source.source c) (F.source.dim c) (F.source.radius c)
    (F.offset c) (F.free c) (direction F c r) p.val i).eval y = 0) at hy
  change (fderiv ℝ (fun z => fun i => (BoundedFullBlockData.rows (F.source.source c) (F.source.dim c)
    (F.source.radius c) (F.offset c) (F.free c) (direction F c r) p.val i).eval z) y).IsInvertible
  rw [he] at hy ⊢
  apply FermatCriticalRegularity.regular_of_certificate
  apply hg p ℝ y
  intro i
  change (FermatCriticalBadSystem.equations (low p) a (degree F.source c) i).eval₂ (eval₂Hom (RingHom.id ℝ) v) y = 0
  rw [← eval_map, FermatCriticalRegularity.equations_map]
  exact hy i

theorem record_good (F : Inputs) (c : List Bool)
    (hfit : F.offset c + (F.free c + 1) ≤ F.source.dim c + 4) (hregular : SliceRegular F c) :
    Good F c (record F c) := record_good_of_exists F c (exists_record F c hfit hregular)

/-- The initial, unfrozen source needs no supplied regularity premise. -/
def whole (P S : Readers) : Inputs := ⟨P, S, fun _ => 0, fun c => S.dim c + 3⟩

theorem whole_polyTime {P S : Readers} (hP : P.PolyTime) (hS : S.PolyTime) : (whole P S).PolyTime :=
  ⟨hP, hS, BinaryFn.const 0, hS.dim.add (UnaryFn.const 3)⟩

theorem whole_slice_regular (P S : Readers) (c : List Bool) : SliceRegular (whole P S) c := by
  change ∀ p : BoundedFullCriticalSamples.Samples P c,
    ∀ (L : Type) [Field L] [Algebra ℝ L] (x : Fin (S.dim c + 4) → L),
      aeval x (slice (whole P S) c p) = 0 → ∃ j, aeval x (pderiv j (slice (whole P S) c p)) ≠ 0
  intro p L _ _ x hx
  let : CharZero L := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℝ L)
  let q : MvPolynomial (Fin (S.dim c + 4)) ℤ :=
    BoundedFullGeometry.polynomial (original S c) (size S c) (size S c) (S.radius c)
  have hs : slice (whole P S) c p = q.map (Int.castRingHom ℝ) :=
    CoordinateBlockSpecialization.finite_all _ _ _
  rw [hs] at hx ⊢
  have hm : (algebraMap ℝ L).comp (Int.castRingHom ℝ) = Int.castRingHom L := RingHom.ext_int _ _
  change eval₂ (algebraMap ℝ L) x (q.map (Int.castRingHom ℝ)) = 0 at hx
  rw [eval₂_map, hm] at hx
  obtain ⟨j, hj⟩ := BoundedFullGeometry.generated_regular S c x hx
  refine ⟨j, ?_⟩
  change eval₂ (algebraMap ℝ L) x (pderiv j (q.map (Int.castRingHom ℝ))) ≠ 0
  rw [pderiv_map, eval₂_map, hm]
  exact hj

theorem whole_record_good (P S : Readers) (c : List Bool) :
    Good (whole P S) c (record (whole P S) c) :=
  record_good _ _ (by change 0 + (S.dim c + 3 + 1) ≤ S.dim c + 4; omega) (whole_slice_regular P S c)

end LeanCanny.Encoding.BoundedFullBlockDirectionChoice
