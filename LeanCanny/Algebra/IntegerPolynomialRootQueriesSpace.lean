/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialFamilyProductSpace
public import LeanCanny.Algebra.SignPatternCountSpace
public import LeanCanny.Algebra.RationalCutSpace
public import LeanCanny.Geometry.OrderedRealCellLocation

/-! # Rational root queries from native integer polynomial readers

Binary upper bounds suffice for distinct-root counts and rational cuts.
Repeated roots are counted once; zero and constant polynomials are total.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialRootQueriesBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option maxHeartbeats 300000

structure Source where
  polynomial : List Bool → ℤ[X]
  degree : List Bool → ℕ
  mass : List Bool → ℕ
  degree_bound : ∀ c, (polynomial c).natDegree ≤ degree c
  mass_bound : ∀ c, coefficientMass (polynomial c) ≤ 2 ^ mass c

structure Access (S : Source) where
  coefficient : SpaceFunction (PrimitivePairBits.coefficient S.polynomial)
  degree : BinaryFn S.degree
  mass : BinaryFn S.mass

theorem coefficient_packet (p : List Bool → ℤ[X]) (c : List Bool) (k m : ℕ) (hm : 0 < m) :
    PrimitivePairBits.coefficient p (pair (pair c (BinaryNatCode.encode k)) (BinaryNatCode.encode (m - 1))) =
      IntegerTarskiSeedBits.integerResidue ((p c).coeff k) m := by
  change RationalSubstitution.IntegerBits.coefficientResidue _ _ =
    RationalSubstitution.IntegerBits.coefficientResidue _ _
  apply congrArg₂ RationalSubstitution.IntegerBits.coefficientResidue
  · simp only [RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · simp only [RationalSubstitution.IntegerBits.mValue, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    omega

noncomputable def rootSet (S : Source) (c : List Bool) : Finset ℝ :=
  ((S.polynomial c).map (algebraMap ℤ ℝ)).roots.toFinset

theorem root_count_le (S : Source) (c : List Bool) : (rootSet S c).card ≤ S.degree c :=
  ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)).trans
    (Polynomial.natDegree_map_le.trans (S.degree_bound c))

def labelWidth (S : Source) (c : List Bool) : ℕ := (2 * S.degree c + 1).size

theorem labelWidth_unary {S : Source} (A : Access S) : UnaryFn (labelWidth S) := by
  have hD : BinaryFn (fun c => 2 * S.degree c + 1) :=
    ((BinaryFn.const 2).mul A.degree).add (BinaryFn.const 1)
  exact (UnaryFn.length hD.bits_mem_FP).of_eq (fun c => Nat.size_eq_bits_len _)

noncomputable def countFamily (S : Source) : SignPatternBits.Family where
  root := S.polynomial
  polynomial _ _ := 0
  pattern _ _ := 0
  count _ := []
  rootDegree c := BinaryNatCode.encode (S.degree c + 1)
  degree _ := []
  rootMass c := BinaryNatCode.encode (S.mass c)
  mass _ := []
  rootDegree_pos c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega
  root_degree c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact (S.degree_bound c).trans (Nat.le_succ _)
  root_mass c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact S.mass_bound c
  polynomial_degree _ i hi := by change i < 0 at hi; omega
  polynomial_mass _ i hi := by change i < 0 at hi; omega

noncomputable def countAccess (S : Source) : SignPatternBits.Access (countFamily S) where
  rootCoefficient := PrimitivePairBits.coefficient S.polynomial
  polynomialCoefficient _ := []
  pattern _ := []
  root_eq := coefficient_packet S.polynomial
  polynomial_eq _ i hi := by change i < 0 at hi; omega
  pattern_eq _ _ := rfl

theorem countEvaluator {S : Source} (A : Access S) :
    SpaceFunction (fun c => BinaryNatCode.encode (rootSet S c).card) := by
  have C : SignPatternBits.ControlsPolyTime (countFamily S) :=
    ⟨constFn_mem_FP [], UnaryFn.const 0, (A.degree.add (BinaryFn.const 1)).bits_mem_FP,
      constFn_mem_FP [], A.mass.bits_mem_FP, constFn_mem_FP []⟩
  have H := SignPatternBits.rootCountEvaluator (countAccess S) C (constFn_mem_FP [])
    A.coefficient (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine H.congr (funext fun c => ?_)
  simp only [SignPatternBits.rootCount, countFamily, RootSignQueries.signCount, rootSet]
  simp

noncomputable def cutFamily (S : Source) (σ : SignType) : SignPatternBits.Family where
  root c := S.polynomial (pairFst c)
  polynomial c _ := RationalCutBits.polynomial c
  pattern _ _ := σ
  count _ := BinaryNatCode.encode 1
  rootDegree c := BinaryNatCode.encode (S.degree (pairFst c) + 1)
  degree _ := BinaryNatCode.encode 1
  rootMass c := BinaryNatCode.encode (S.mass (pairFst c))
  mass c := BinaryNatCode.encode (RationalCutBits.massExponent c)
  rootDegree_pos c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega
  root_degree c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact (S.degree_bound _).trans (Nat.le_succ _)
  root_mass c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact S.mass_bound _
  polynomial_degree c _ _ := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact RationalCutBits.polynomial_degree c
  polynomial_mass c _ _ := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact RationalCutBits.polynomial_mass c

def cutQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pairSnd (pairSnd (pairFst q)))) (pairSnd q)
theorem cutQuery_FP : cutQuery ∈ FP := by polytime [cutQuery]

noncomputable def cutAccess (S : Source) (σ : SignType) : SignPatternBits.Access (cutFamily S σ) where
  rootCoefficient := PrimitivePairBits.coefficient (S.polynomial ∘ pairFst)
  polynomialCoefficient := RationalCutBits.coefficient ∘ cutQuery
  pattern _ := InfinitesimalSign.encode σ
  root_eq := coefficient_packet (S.polynomial ∘ pairFst)
  polynomial_eq c _ _ k m hm := by
    simp only [Function.comp_apply, cutQuery, pairFst_pair, pairSnd_pair]
    exact RationalCutBits.coefficient_packet c k m hm
  pattern_eq _ _ := rfl

noncomputable def cutCount (S : Source) (σ : SignType) (c : List Bool) : ℕ :=
  ((rootSet S (pairFst c)).filter (fun x =>
    SignType.sign (((RationalCutBits.polynomial c).map (algebraMap ℤ ℝ)).eval x) = σ)).card

theorem cutEvaluator {S : Source} (A : Access S) (σ : SignType) :
    SpaceFunction (fun c => BinaryNatCode.encode (cutCount S σ c)) := by
  have C : SignPatternBits.ControlsPolyTime (cutFamily S σ) :=
    ⟨constFn_mem_FP _, UnaryFn.const 1,
      BinaryFn.bits_mem_FP ((A.degree.add (BinaryFn.const 1)).comp pairFst_mem_FP),
      constFn_mem_FP _, BinaryFn.bits_mem_FP (A.mass.comp pairFst_mem_FP), bits_mem_FP RationalCutBits.massExponent_unary⟩
  have Q : SpaceFunction (RationalCutBits.coefficient ∘ cutQuery) := SpaceFunction.ofFP _
    (mem_FP_comp (f := cutQuery) (g := RationalCutBits.coefficient) cutQuery_FP RationalCutBits.coefficient_FP)
  have H := SignPatternBits.rootCountEvaluator (cutAccess S σ) C
    (constFn_mem_FP (InfinitesimalSign.encode σ))
    (PolynomialFamilyProductBits.reindexEvaluator A.coefficient pairFst pairFst_mem_FP)
    Q
  refine H.congr (funext fun c => ?_)
  simp only [SignPatternBits.rootCount, cutFamily, RootSignQueries.signCount, cutCount, rootSet,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, forall_const]

theorem cut_below (S : Source) (c : List Bool) : cutCount S .neg c =
    Geometry.OrderedRealCells.lowerCount (rootSet S (pairFst c)) (RationalCutBits.threshold c) := by
  simp only [cutCount, RationalCutBits.sign_neg_iff, Geometry.OrderedRealCells.lowerCount]

theorem cut_sign_zero_iff (c : List Bool) (x : ℝ) :
    SignType.sign (((RationalCutBits.polynomial c).map (algebraMap ℤ ℝ)).eval x) = 0 ↔
      x = RationalCutBits.threshold c := by
  rw [sign_eq_zero_iff, RationalCutBits.eval_real]
  have hd : (RationalCutBits.divisor c : ℝ) ≠ 0 := by
    have h : 0 < RationalCutBits.divisor c := Nat.succ_pos _
    exact_mod_cast h.ne'
  rw [RationalCutBits.threshold, eq_div_iff hd]
  constructor <;> intro h <;> linarith

theorem cut_zero_pos_iff (S : Source) (c : List Bool) :
    0 < cutCount S 0 c ↔ RationalCutBits.threshold c ∈ rootSet S (pairFst c) := by
  rw [cutCount, Finset.card_pos, Finset.filter_nonempty_iff]
  simp only [cut_sign_zero_iff]
  constructor
  · rintro ⟨x, hx, he⟩
    rwa [he] at hx
  · intro h
    exact ⟨_, h, rfl⟩

noncomputable def cellCode (S : Source) (c : List Bool) : ℕ :=
  let s := rootSet S (pairFst c)
  let a := RationalCutBits.threshold c
  if a ∈ s then Geometry.OrderedRealCells.lowerCount s a
  else s.card + Geometry.OrderedRealCells.lowerCount s a

def cellFinish (z : List Bool) : List Bool :=
  if 0 < Nat.fromBitsLE (pairSnd (pairSnd z)) then pairFst (pairSnd z)
  else BinaryNat.add (pair (pairFst z) (pairFst (pairSnd z)))

theorem cellFinish_FP : cellFinish ∈ FP := by
  have hb := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hz := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have hsum : (fun z => BinaryNat.add (pair (pairFst z) (pairFst (pairSnd z)))) ∈ FP :=
    mem_FP_comp (f := fun z => pair (pairFst z) (pairFst (pairSnd z))) (g := BinaryNat.add)
      (mem_FP_pair pairFst_mem_FP hb) BinaryNat.add_mem_FP
  exact ((BinaryFn.const 0).lt hz).ite_mem_FP hb hsum

theorem cellEvaluator {S : Source} (A : Access S) :
    SpaceFunction (fun c => BinaryNatCode.encode (cellCode S c)) := by
  have H := ((countEvaluator A).precompose pairFst pairFst_mem_FP).pairOutputs
    ((cutEvaluator A .neg).pairOutputs (cutEvaluator A 0))
  refine (H.postcompose cellFinish cellFinish_FP).congr (funext fun c => ?_)
  simp only [Function.comp_apply, cellFinish, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, BinaryNat.add_pair]
  simp only [cut_zero_pos_iff, cut_below, cellCode]
  split_ifs <;> rfl

theorem cellCode_eq_of_mem_piece (S : Source) (c : List Bool)
    (i : Geometry.OrderedRealCells.Index (rootSet S (pairFst c)))
    (hi : RationalCutBits.threshold c ∈ Geometry.OrderedRealCells.piece (rootSet S (pairFst c)) i) :
    cellCode S c = Geometry.OrderedRealCells.code (rootSet S (pairFst c)) i :=
  (Geometry.OrderedRealCells.code_of_mem_piece _ _ i hi).symm

theorem cellCode_eq_iff_mem_piece (S : Source) (c : List Bool)
    (i : Geometry.OrderedRealCells.Index (rootSet S (pairFst c))) :
    cellCode S c = Geometry.OrderedRealCells.code (rootSet S (pairFst c)) i ↔
      RationalCutBits.threshold c ∈ Geometry.OrderedRealCells.piece (rootSet S (pairFst c)) i := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Geometry.OrderedRealCells.cover (rootSet S (pairFst c)) (RationalCutBits.threshold c)
    have he : j = i := Geometry.OrderedRealCells.code_injective _
      ((cellCode_eq_of_mem_piece S c j hj).symm.trans h)
    rwa [← he]
  · exact cellCode_eq_of_mem_piece S c i

theorem cellCode_lt (S : Source) (c : List Bool) : cellCode S c < 2 ^ labelWidth S (pairFst c) := by
  obtain ⟨i, hi⟩ := Geometry.OrderedRealCells.cover (rootSet S (pairFst c)) (RationalCutBits.threshold c)
  rw [cellCode_eq_of_mem_piece S c i hi]
  apply (Geometry.OrderedRealCells.code_lt _ i).trans_le
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (root_count_le S _)) 1).trans
    (Nat.lt_size_self _).le

noncomputable def cellLanguage (S : Source) : Language :=
  {q | cellCode S (pairFst q) = Nat.fromBitsLE (pairSnd q)}

def cellCompare (z : List Bool) : Bool :=
  decide (Nat.fromBitsLE (pairSnd z) = Nat.fromBitsLE (pairSnd (pairFst z)))

theorem cellCompare_FP : (fun z => [cellCompare z]) ∈ FP :=
  ((BinaryFn.fromBits pairSnd_mem_FP).eq
    (BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))).flag_mem_FP

theorem cellDecider {S : Source} (A : Access S) : SpaceDecider (cellLanguage S) := by
  have H := ((cellEvaluator A).precompose pairFst pairFst_mem_FP).withInput
  apply H.decider cellCompare cellCompare_FP
  intro q
  simp only [cellLanguage, Set.mem_ofPred_eq, cellCompare, pairFst_pair, pairSnd_pair,
    Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem cell_mem_PSPACE {S : Source} (A : Access S) : cellLanguage S ∈ PSPACE :=
  (cellDecider A).mem_PSPACE

theorem cell_packet (S : Source) (c : List Bool)
    (i : Geometry.OrderedRealCells.Index (rootSet S (pairFst c))) :
    pair c (BinaryNatCode.encode (Geometry.OrderedRealCells.code (rootSet S (pairFst c)) i)) ∈ cellLanguage S ↔
      RationalCutBits.threshold c ∈ Geometry.OrderedRealCells.piece (rootSet S (pairFst c)) i := by
  simp only [cellLanguage, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact cellCode_eq_iff_mem_piece S c i

end LeanCanny.Algebra.IntegerPolynomialRootQueriesBits
