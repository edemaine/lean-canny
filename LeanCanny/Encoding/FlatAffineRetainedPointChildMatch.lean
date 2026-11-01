/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteSlotEquality
public import LeanCanny.Encoding.FlatAffineChildSpatialEquality
public import LeanCanny.Computation.SpaceFunctionWordExistence

/-! # Matching retained parent points to an actual complete child

The point query is `((source, parent), (left stage, right stage))`. A candidate
child must have that exact parent and its spatial point must equal both
retained points. Native coordinate comparisons stream one coordinate at a
time. Invalid stage references are rejected.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineRetainedPointChildMatch
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open FlatAffineCompleteRootStages (next newest)
open scoped Classical

def record (u v : List Bool) (a b : ℕ) : List Bool :=
  pair (pair u v) (pair (BinaryNatCode.encode a) (BinaryNatCode.encode b))
def source (q : List Bool) : List Bool := pairFst (pairFst q)
def parent (q : List Bool) : List Bool := pairSnd (pairFst q)
def refWord (right : Bool) (q : List Bool) : List Bool :=
  if right then pairSnd (pairSnd q) else pairFst (pairSnd q)
def context (p : List Bool) : List Bool := source (pairFst p)
def childQuery (p : List Bool) : List Bool := pair (context p) (pair (pairSnd p) (parent (pairFst p)))
theorem source_FP : source ∈ FP := by polytime [source]
theorem context_FP : context ∈ FP := by polytime [context, source]
theorem childQuery_FP : childQuery ∈ FP := by polytime [childQuery, context, source, parent]

def stage (F : Inputs) (u r : List Bool) : Fin (F.depth u + 1) :=
  ⟨min (Nat.fromBitsLE r) (F.depth u), by omega⟩
noncomputable def slot (F : Inputs) (u r d : List Bool) : Fin (FlatAffineFullSourcePositive.count (next F) u) :=
  (FlatAffinePowerTower.current (stage F u r) (FlatAffineChildSpatialEquality.selected F u d)).castSucc
noncomputable def slotWord (F : Inputs) (u r d : List Bool) : List Bool :=
  BinaryNatCode.encode (slot F u r d).val

theorem slot_encode (F : Inputs) (u : List Bool) (t : Fin (F.depth u)) (i : Fin (arity F u)) :
    slot F u (BinaryNatCode.encode t.val) (BinaryNatCode.encode i.val) =
      (FlatAffinePowerTower.current t.castSucc i).castSucc := by
  unfold slot
  rw [FlatAffineChildSpatialEquality.selected_encode]
  congr 2
  apply Fin.ext
  simp only [stage, BinaryNatCode.encode, Nat.fromBitsLE_bits, Fin.val_castSucc]
  exact Nat.min_eq_left (Nat.le_of_lt t.isLt)

theorem slotWord_FP {F : Inputs} (h : F.Access) :
    (fun q => slotWord F (pairFst (pairFst q)) (pairSnd (pairFst q)) (pairSnd q)) ∈ FP := by
  have hu : (fun q => pairFst (pairFst q)) ∈ FP := by polytime
  have hi := UnaryFn.fromBitsLE_min pairSnd_mem_FP
    (((FlatAffineFullSourceTower.arity_unary h).comp hu).sub (UnaryFn.const 1))
  have ht := UnaryFn.fromBitsLE_min (by polytime : (fun q => pairSnd (pairFst q)) ∈ FP) (h.depth.comp hu)
  have H : UnaryFn (fun q => (slot F (pairFst (pairFst q)) (pairSnd (pairFst q)) (pairSnd q)).val) :=
    (hi.add (((FlatAffineFullSourceTower.stageWidth_unary h).comp hu).mul ht)).of_eq (fun _ => rfl)
  exact (BinaryFn.ofUnary H).bits_mem_FP

def indexContext (right : Bool) (r : List Bool) : List Bool :=
  pair (pair (context (pairFst r)) (refWord right (pairFst (pairFst r)))) (pairSnd r)
def coordinateContext (r : List Bool) : List Bool := pair (context (pairFst r)) (pairSnd r)
theorem indexContext_FP (right : Bool) : indexContext right ∈ FP := by
  cases right <;> polytime [indexContext, context, source, refWord]
theorem coordinateContext_FP : coordinateContext ∈ FP := by polytime [coordinateContext, context, source]

attribute [local irreducible] slotWord FlatAffineChildSpatialEquality.slotWord

noncomputable def probe (F : Inputs) (right : Bool) (r : List Bool) : List Bool :=
  pair (pair (context (pairFst r)) (pairSnd (pairFst r)))
    (pair (slotWord F (pairFst (pairFst (indexContext right r)))
      (pairSnd (pairFst (indexContext right r))) (pairSnd (indexContext right r)))
      (FlatAffineChildSpatialEquality.slotWord F (pairFst (coordinateContext r)) (pairSnd (coordinateContext r))))

theorem probe_FP {F : Inputs} (h : F.Access) (right : Bool) : probe F right ∈ FP := by
  have V : (fun r => pair (context (pairFst r)) (pairSnd (pairFst r))) ∈ FP := by
    polytime [context, source]
  apply mem_FP_of_eq (mem_FP_pair V (mem_FP_pair (mem_FP_comp (indexContext_FP right) (slotWord_FP h))
    (mem_FP_comp coordinateContext_FP (FlatAffineChildSpatialEquality.slotWord_FP h))))
  intro r
  rfl

noncomputable def equalLanguage (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (right : Bool) : Language :=
  {p | ∀ i < arity F (context p), probe F right (pair p (BinaryNatCode.encode i)) ∈
    SquareSampleCompleteSlotEquality.language (FlatAffinePowerSampleInput.input (next F) cone)}

theorem equalEvaluator {F : Inputs} (h : F.Access)
    (cone : FlatAffinePowerPositive.ConeCertificate (next F)) (right : Bool) :
    SpaceFunction (fun p => [decide (p ∈ equalLanguage F cone right)]) := by
  have D := SquareSampleCompleteSlotEquality.decider
    (FlatAffinePowerSampleInput.access (FlatAffineCompleteChildLabels.nextAccess h) cone)
  have E := (D.precompose (probe F right) (probe_FP h right)).flagEvaluator
  have N := BinaryFn.ofUnary ((FlatAffineFullSourceTower.arity_unary h).comp context_FP)
  exact (E.forall_binary N).congr (funext fun p => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]
    rfl)

noncomputable def point (F : Inputs) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots F u) (t : Fin (F.depth u)) : Fin (arity F u) → ℝ :=
  fun i => x.val (FlatAffinePowerTower.current t i)

theorem point_project (F : Inputs) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots (next F) u) (t : Fin (F.depth u)) :
    point F u (FlatAffineCompleteRootStages.project (next F) F.depth u (Nat.le_succ _) x) t =
      point (next F) u x t.castSucc := by
  funext i
  apply congrArg x.val
  apply Fin.ext
  rfl

theorem probe_packet (F : Inputs) (u v z : List Bool) (a b : Fin (F.depth u))
    (right : Bool) (i : Fin (arity F u)) :
    probe F right (pair (pair (record u v a.val b.val) z) (BinaryNatCode.encode i.val)) =
      pair (pair u z) (pair
        (BinaryNatCode.encode (FlatAffinePowerTower.current
          (if right then b.castSucc else a.castSucc) i).castSucc.val)
        (BinaryNatCode.encode (FlatAffineChildSpatialEquality.slot F u i).val)) := by
  simp only [probe, indexContext, coordinateContext, context, source, refWord, record,
    pairFst_pair, pairSnd_pair]
  cases right <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals rw [slotWord, slot_encode, FlatAffineChildSpatialEquality.slotWord,
    FlatAffineChildSpatialEquality.selected_encode]

theorem equal_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v z : List Bool) (a b : Fin (F.depth u)) (right : Bool)
    (hz : FlatAffineCompleteVertices.Valid (next F) cone u z) :
    pair (record u v a.val b.val) z ∈ equalLanguage F cone right ↔
      point (next F) u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨z, hz⟩)
        (if right then b.castSucc else a.castSucc) =
      newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨z, hz⟩).val ∘ Sum.inl := by
  change _ ↔ (fun i : Fin (arity F u) =>
    point (next F) u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨z, hz⟩)
      (if right then b.castSucc else a.castSucc) i) =
    (fun i : Fin (arity F u) => newest F u
      (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨z, hz⟩).val (Sum.inl i))
  have H (i : Fin (arity F u)) := SquareSampleCompleteSlotEquality.packet
    (FlatAffinePowerSampleInput.input (next F) cone) (FlatAffinePowerSampleInput.complete (next F) cone) u z hz
    (FlatAffinePowerTower.current (if right then b.castSucc else a.castSucc) i).castSucc
    (FlatAffineChildSpatialEquality.slot F u i)
  have HL (i : Fin (arity F u)) := FlatAffineCompleteVertices.ambient_coordinate (next F) cone u z hz
    (if right then b.castSucc else a.castSucc) i
  have HR (i : Fin (arity F u)) := FlatAffineChildSpatialEquality.point_coordinate F cone u z hz i
  constructor
  · intro hEq
    funext i
    have hi := hEq i.val (by simpa only [context, source, record, pairFst_pair] using i.isLt)
    rw [probe_packet] at hi
    have he := (H i).mp hi
    exact (HL i).trans (he.trans (HR i).symm)
  · intro he i hi
    have hin : i < arity F u := by simpa only [context, source, record, pairFst_pair] using hi
    rw [probe_packet F u v z a b right ⟨i, hin⟩]
    apply (H ⟨i, hin⟩).mpr
    exact (HL ⟨i, hin⟩).symm.trans ((congrFun he ⟨i, hin⟩).trans (HR ⟨i, hin⟩))

def bounds (F : Inputs) (q : List Bool) : Prop :=
  Nat.fromBitsLE (refWord false q) < F.depth (source q) ∧
    Nat.fromBitsLE (refWord true q) < F.depth (source q)

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) : Language :=
  {p | bounds F (pairFst p) ∧ childQuery p ∈ FlatAffineCompleteChildLabels.language F cone ∧
    p ∈ equalLanguage F cone false ∧ p ∈ equalLanguage F cone true}

theorem bounds_fppred {F : Inputs} (h : F.Access) : FPPred (bounds F) := by
  have N := BinaryFn.ofUnary (h.depth.comp source_FP)
  have L : (fun q => refWord false q) ∈ FP := by polytime [refWord]
  have R : (fun q => refWord true q) ∈ FP := by polytime [refWord]
  exact ((BinaryFn.fromBits L).lt N).and ((BinaryFn.fromBits R).lt N)

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    SpaceDecider (language F cone) := by
  have B := SpaceFunction.ofFP _ ((bounds_fppred h).comp pairFst_mem_FP).flag_mem_FP
  have C := ((FlatAffineCompleteChildLabels.decider h cone).precompose childQuery childQuery_FP).flagEvaluator
  apply (B.andFlags (C.andFlags ((equalEvaluator h cone false).andFlags (equalEvaluator h cone true)))).decider
    (fun z => decide (z = [true])) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro p
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (q z : List Bool) (h : pair q z ∈ language F cone) :
    FlatAffineCompleteVertices.Valid (next F) cone (source q) z ∧
      FlatAffineCompleteVertices.Valid F (FlatAffineCompleteChildLabels.parentCone F cone) (source q) (parent q) := by
  have hc : pair (source q) (pair z (parent q)) ∈ FlatAffineCompleteChildLabels.language F cone := by
    simpa only [childQuery, context, pairFst_pair, pairSnd_pair] using h.2.1
  exact FlatAffineCompleteChildLabels.valid F cone (source q) z (parent q) hc

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v z : List Bool) (a b : Fin (F.depth u))
    (hv : FlatAffineCompleteVertices.Valid F (FlatAffineCompleteChildLabels.parentCone F cone) u v)
    (hz : FlatAffineCompleteVertices.Valid (next F) cone u z) :
    pair (record u v a.val b.val) z ∈ language F cone ↔
      FlatAffineCompleteRootStages.project (next F) F.depth u (Nat.le_succ _)
        (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨z, hz⟩) =
        FlatAffineCompleteVertices.vertexEquiv F (FlatAffineCompleteChildLabels.parentCone F cone) u ⟨v, hv⟩ ∧
      point F u (FlatAffineCompleteVertices.vertexEquiv F (FlatAffineCompleteChildLabels.parentCone F cone) u ⟨v, hv⟩) a =
        newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨z, hz⟩).val ∘ Sum.inl ∧
      point F u (FlatAffineCompleteVertices.vertexEquiv F (FlatAffineCompleteChildLabels.parentCone F cone) u ⟨v, hv⟩) b =
        newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨z, hz⟩).val ∘ Sum.inl := by
  simp only [language, Set.mem_ofPred_eq, bounds, refWord, source, record, childQuery, context, parent,
    pairFst_pair, pairSnd_pair, Bool.false_eq_true, ite_false, ite_true,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, a.isLt, b.isLt, true_and]
  change (pair u (pair z v) ∈ FlatAffineCompleteChildLabels.language F cone ∧
    pair (record u v a.val b.val) z ∈ equalLanguage F cone false ∧
    pair (record u v a.val b.val) z ∈ equalLanguage F cone true) ↔ _
  rw [FlatAffineCompleteChildLabels.packet F cone u z v hz hv,
    equal_packet F cone u v z a b false hz, equal_packet F cone u v z a b true hz]
  simp only [Bool.false_eq_true]
  have H (hp : FlatAffineCompleteRootStages.project (next F) F.depth u (Nat.le_succ _)
      (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨z, hz⟩) =
        FlatAffineCompleteVertices.vertexEquiv F (FlatAffineCompleteChildLabels.parentCone F cone) u ⟨v, hv⟩)
      (t : Fin (F.depth u)) :
      point F u (FlatAffineCompleteVertices.vertexEquiv F (FlatAffineCompleteChildLabels.parentCone F cone) u ⟨v, hv⟩) t =
        point (next F) u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨z, hz⟩) t.castSucc :=
    (congrArg (fun root => point F u root t) hp).symm.trans (point_project F u _ t)
  constructor
  · rintro ⟨hp, ha, hb⟩
    exact ⟨hp, (H hp a).trans ha, (H hp b).trans hb⟩
  · rintro ⟨hp, ha, hb⟩
    exact ⟨hp, (H hp a).symm.trans ha, (H hp b).symm.trans hb⟩

noncomputable def hits (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) : Language :=
  {q | ∃ z : List Bool, z.length = FlatAffineCompleteVertices.width (next F) cone (source q) ∧
    pair q z ∈ language F cone}

theorem hits_decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    SpaceDecider (hits F cone) := by
  have E := (decider h cone).flagEvaluator.exists_words
    ((FlatAffineCompleteVertices.width_unary (FlatAffineCompleteChildLabels.nextAccess h) cone).comp source_FP)
  apply E.decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [hits, Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq]

end LeanCanny.Encoding.FlatAffineRetainedPointChildMatch
