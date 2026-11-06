/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitCoefficientTest
public import LeanCanny.Computation.FiniteCoefficientSignScan
/-! # Genuine finite coordinate-selection guards on one implicit own tuple -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitCenterSelection
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input
attribute [local irreducible] FormulaSignSlotRadialImplicitCoefficientTest.value

def sample (q : List Bool) := pairFst (pairFst q)
def context (q : List Bool) := pairFst (sample q)
def coordinate (q : List Bool) := Nat.fromBitsLE (pairSnd (pairFst q))
def choice (q : List Bool) := Nat.fromBitsLE (pairFst (pairSnd q))
def degree (q : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd q))
noncomputable def bound (q : List Bool) := FormulaSignSlotRadialJointCoefficientCatalogue.degree
  (FormulaSignSlotRadialImplicitCoefficientTest.header (context q))
theorem context_FP : context ∈ FP := by polytime [context,sample]
theorem choice_binary : BinaryFn choice := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem degree_binary : BinaryFn degree := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
theorem bound_binary : BinaryFn bound := FormulaSignSlotRadialJointCoefficientCatalogue.degree_binary.comp
  (mem_FP_comp context_FP FormulaSignSlotRadialImplicitGridTest.header_FP)

def radiusQuery (z : List Bool) := pair (pairFst (pairFst (pairFst (pairFst z))))
  (WordList.encode [pairSnd (pairFst (pairFst (pairFst z))),
    BinaryNat.normalize (pairSnd (pairSnd (pairFst z))),
    BinaryNat.normalize (pairFst (pairSnd (pairFst z))),BinaryNat.normalize (pairSnd z)])
theorem radiusQuery_FP : radiusQuery ∈ FP := by
  unfold radiusQuery WordList.encode
  apply mem_FP_pair
  · polytime
  · apply mem_FP_pair
    · polytime
    · apply mem_FP_pair
      · exact mem_FP_comp (by polytime) BinaryNat.normalize_mem_FP
      · apply mem_FP_pair
        · exact mem_FP_comp (by polytime) BinaryNat.normalize_mem_FP
        · exact mem_FP_pair (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP) (constFn_mem_FP [])

noncomputable def RadiusZero (q : List Bool) : Prop := ∀ r < bound (pairFst q)+1,
  FormulaSignSlotRadialImplicitCoefficientTest.value (radiusQuery (pair q (BinaryNatCode.encode r))) =
    InfinitesimalSign.encode 0
noncomputable def marker (q : List Bool) := if RadiusZero q then InfinitesimalSign.encode 0 else InfinitesimalSign.encode 1

theorem marker_evaluator : SpaceFunction marker := by
  have ES := FormulaSignSlotRadialImplicitCoefficientTest.evaluator.precompose radiusQuery radiusQuery_FP
  have EZ := ES.postcompose _ (stringEq_fppred id_mem_FP (constFn_mem_FP (InfinitesimalSign.encode 0))).flag_mem_FP
  have HB0 : BinaryFn (fun q => bound (pairFst q)) := bound_binary.comp pairFst_mem_FP
  have HB := HB0.add (BinaryFn.const 1)
  have EA := EZ.forall_binary HB
  have EF := EA.postcompose (fun z => if z = [true] then InfinitesimalSign.encode 0 else InfinitesimalSign.encode 1)
    ((stringEq_fppred id_mem_FP (constFn_mem_FP [true])).ite_mem_FP (constFn_mem_FP _) (constFn_mem_FP _))
  exact EF.congr (funext fun q => by
    simp only [Function.comp_apply,id_eq,marker,RadiusZero,List.cons.injEq,and_true,decide_eq_true_eq]
    split_ifs <;> rfl)

theorem marker_zero (q : List Bool) : marker q = InfinitesimalSign.encode 0 ↔ RadiusZero q := by
  by_cases H : RadiusZero q
  · simp only [marker,H,ite_true]
  · simp only [marker,H,ite_false,iff_false]
    decide

noncomputable def Guards (q : List Bool) : Prop := (choice q ≤ bound q ∧ degree q ≤ bound q) ∧
  FiniteCoefficientSignScan.Guards marker (fun _ => InfinitesimalSign.encode 1) choice degree bound q

theorem evaluator : SpaceFunction (fun q => [decide (Guards q)]) := by
  have EC := FiniteCoefficientSignScan.evaluator marker (fun _ => InfinitesimalSign.encode 1)
    choice degree bound marker_evaluator (SpaceFunction.ofFP _ (constFn_mem_FP _)) choice_binary degree_binary bound_binary
  have EB := SpaceFunction.ofFP _ (((choice_binary.le bound_binary).and (degree_binary.le bound_binary)).flag_mem_FP)
  exact (EB.andFlags EC).congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Guards,List.cons.injEq,and_true,decide_eq_true_eq])

def packet (c w : List Bool) (j tau D : ℕ) :=
  pair (pair (pair c w) (BinaryNatCode.encode j)) (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode D))

private theorem bound_packet (c w : List Bool) (j tau D : ℕ) : bound (packet c w j tau D) =
    FormulaSignSlotRadialCenterSelection.bound (FormulaSignSlotRadialCoordinatePacket.packet
      (FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialImplicitCoefficientTest.header c)) j) := by
  apply FormulaSignSlotRadialEliminantRootProfiles.degree_eq
  simp only [context,sample,packet,FormulaSignSlotRadialImplicitCoefficientTest.header,
    FormulaSignSlotRadialJointCoefficientCatalogue.base,FormulaSignSlotRadialCoordinatePacket.root,LeanCanny.pairFst_pair]

theorem radius_query_packet (c w : List Bool) (j tau D e k r : ℕ) :
    radiusQuery (pair (FiniteCoefficientSignScan.query (packet c w j tau D) e k) (BinaryNatCode.encode r)) =
      pair (pair c w) (FormulaSignSlotRadialImplicitCoefficientTest.indices j k e r) := by
  simp only [radiusQuery,FiniteCoefficientSignScan.query,packet,LeanCanny.pairFst_pair,LeanCanny.pairSnd_pair,
    BinaryNat.normalize_eq_bits,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    FormulaSignSlotRadialImplicitCoefficientTest.indices]

private theorem constant_head (q : List Bool) :
    FiniteCoefficientSignScan.Guards marker (fun _ => InfinitesimalSign.encode 1) choice degree bound q ↔
      (∀ k < choice q,∀ e < bound q+1,FiniteCoefficientSignScan.Zero marker q e k) ∧
      ¬FiniteCoefficientSignScan.Zero marker q (degree q) (choice q) ∧
      (∀ e < bound q+1,degree q < e → FiniteCoefficientSignScan.Zero marker q e (choice q)) := by
  have H : InfinitesimalSign.encode (1 : SignType) ≠ InfinitesimalSign.encode 0 := by decide
  change (_ ∧ _ ∧ _ ∧ (_ ∨ _)) ↔ _
  constructor
  · intro h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · rintro ⟨hL,hC,hH⟩
    exact ⟨hL,hC,hH,Or.inl H⟩

/-- Every lower and higher coefficient is checked at this SAME decoded point. -/
theorem guards_packet (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) (j tau D : ℕ) :
    Guards (packet c w j tau D) ↔
      FormulaSignSlotRadialCenterSelection.Guards
        (FormulaSignSlotRadialCoordinatePacket.packet
          (FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialImplicitCoefficientTest.header c)) j)
        (fun i => FormulaSignSlotRadialImplicitCoefficientTest.env c w hw (4*i.val)) tau D := by
  let q := packet c w j tau D
  have HB := bound_packet c w j tau D
  have HZ (e k : ℕ) : FiniteCoefficientSignScan.Zero marker q e k ↔
      ∀ r < bound q+1,FormulaSignSlotRadialJointCoefficientCatalogue.coefficientValue
        (FormulaSignSlotRadialImplicitCoefficientTest.header c) j k e r
        (FormulaSignSlotRadialImplicitCoefficientTest.env c w hw) = 0 := by
    rw [FiniteCoefficientSignScan.Zero,marker_zero]
    simp only [RadiusZero,FiniteCoefficientSignScan.query,LeanCanny.pairFst_pair]
    change (∀ r < bound q+1,FormulaSignSlotRadialImplicitCoefficientTest.value
      (radiusQuery (pair (FiniteCoefficientSignScan.query (packet c w j tau D) e k) (BinaryNatCode.encode r))) = _) ↔ _
    simp_rw [radius_query_packet,FormulaSignSlotRadialImplicitCoefficientTest.zero_packet c w hw]
  change Guards q ↔ _
  rw [Guards,constant_head]
  simp_rw [HZ]
  simp only [choice,degree,q,packet,LeanCanny.pairFst_pair,LeanCanny.pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    FormulaSignSlotRadialCenterSelection.Guards,FormulaSignSlotRadialCenterSelection.Zero,
    FormulaSignSlotRadialJointCoefficientCatalogue.coefficientValue,and_assoc,not_forall,exists_prop]
  rw [←HB]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialImplicitCenterSelection
