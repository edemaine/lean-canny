/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TarskiSeedSpace
public import LeanCanny.Algebra.DerivativeProductBounds
public import LeanCanny.Algebra.IntegerSignumSpace

/-! # Uniform residues and signs of actual integer Tarski-seed coefficients

Input pairs an original context and coefficient index, then a modulus-minus-one
word. Indices outside the reduction bound return zero. Metadata and magnitude
budgets come from the original head and query polynomials; only their original
uniform coefficient-residue routines are external.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerTarskiSeedBits
open Polynomial
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower

noncomputable def integerResidue (z : ℤ) (m : ℕ) : List Bool := residueBits (z : ZMod m)

structure Family where
  head : List Bool → ℤ[X]
  query : List Bool → ℤ[X]
  degree : List Bool → List Bool
  queryBound : List Bool → List Bool
  headMass : List Bool → List Bool
  queryMass : List Bool → List Bool
  degree_pos : ∀ c, 0 < Nat.fromBitsLE (degree c)
  head_degree : ∀ c, (head c).natDegree ≤ Nat.fromBitsLE (degree c)
  query_degree : ∀ c, (query c).natDegree ≤ Nat.fromBitsLE (queryBound c)
  head_mass : ∀ c, coefficientMass (head c) ≤ 2 ^ Nat.fromBitsLE (headMass c)
  query_mass : ∀ c, coefficientMass (query c) ≤ 2 ^ Nat.fromBitsLE (queryMass c)

def origin (q : List Bool) : List Bool := pairFst (pairFst q)
def index (q : List Bool) : List Bool := pairSnd (pairFst q)
def mValue (q : List Bool) : ℕ := Nat.fromBitsLE (pairSnd q) + 1
def boundCode (F : Family) (q : List Bool) : List Bool :=
  BinaryNat.add (pair (F.degree (origin q)) (F.queryBound (origin q)))
def modulusCode (q : List Bool) : List Bool := BinaryNat.succ (pairSnd q)
def selectedCode (F : Family) (q : List Bool) : List Bool :=
  BinaryNat.mod (pair (index q) (BinaryNat.succ (boundCode F q)))
def valid (F : Family) (q : List Bool) : Prop :=
  Nat.fromBitsLE (index q) < Nat.fromBitsLE (boundCode F q) + 1
instance (F : Family) (q : List Bool) : Decidable (valid F q) := inferInstanceAs (Decidable (_ < _))

noncomputable def Family.reduced (F : Family) (c : List Bool) : ℤ[X] :=
  PseudoRemainder.seed (F.head c) (F.query c) (Nat.fromBitsLE (F.degree c))
    (Nat.fromBitsLE (F.degree c) + Nat.fromBitsLE (F.queryBound c))

noncomputable def Family.coefficient (F : Family) (r : List Bool) : ℤ :=
  (F.reduced (pairFst r)).coeff (Nat.fromBitsLE (pairSnd r))

noncomputable def Family.residue (F : Family) (q : List Bool) : List Bool :=
  integerResidue (F.coefficient (pairFst q)) (mValue q)

def Family.budget (F : Family) (r : List Bool) : List Bool :=
  TarskiSeedBits.seedBudgetCode (F.degree (pairFst r)) (F.queryBound (pairFst r))
    (F.headMass (pairFst r)) (F.queryMass (pairFst r))

theorem Family.coefficient_size (F : Family) (r : List Bool) :
    (F.coefficient r).natAbs.size ≤ Nat.fromBitsLE (F.budget r) :=
  TarskiSeedBits.seed_coeff_size_le (F.head (pairFst r)) (F.query (pairFst r)) _ _ _ _
    (F.head_degree _) (F.head_mass _) (F.query_mass _) _

noncomputable def Family.modular (F : Family) : TarskiSeedBits.Family where
  source := {
    modulus := mValue
    head q := (F.head (origin q)).map (Int.castRingHom (ZMod (mValue q)))
    query q := (F.query (origin q)).map (Int.castRingHom (ZMod (mValue q)))
    modulus_ne_zero q := by dsimp [mValue]; omega }
  degree q := Nat.fromBitsLE (F.degree (origin q))
  queryBound q := Nat.fromBitsLE (F.queryBound (origin q))
  selected q := ⟨Nat.fromBitsLE (index q) %
    (Nat.fromBitsLE (F.degree (origin q)) + Nat.fromBitsLE (F.queryBound (origin q)) + 1),
    Nat.mod_lt _ (Nat.succ_pos _)⟩
  degree_pos q := F.degree_pos (origin q)
  head_degree q := natDegree_map_le.trans (F.head_degree (origin q))
  query_degree q := natDegree_map_le.trans (F.query_degree (origin q))

set_option backward.isDefEq.respectTransparency false in
theorem Family.modular_value (F : Family) (q : List Bool) :
    F.modular.value q = integerResidue
      ((F.reduced (origin q)).coeff (Nat.fromBitsLE (index q) %
        (Nat.fromBitsLE (F.degree (origin q)) + Nat.fromBitsLE (F.queryBound (origin q)) + 1)))
      (mValue q) := by
  change residueBits ((PseudoRemainder.seed
    ((F.head (origin q)).map (Int.castRingHom (ZMod (mValue q))))
    ((F.query (origin q)).map (Int.castRingHom (ZMod (mValue q))))
    (Nat.fromBitsLE (F.degree (origin q)))
    (Nat.fromBitsLE (F.degree (origin q)) + Nat.fromBitsLE (F.queryBound (origin q)))).coeff _) = _
  rw [PseudoRemainder.seed_map, coeff_map]
  rfl

theorem Family.input_degree (F : Family) (c : List Bool) :
    (F.query c * (F.head c).derivative).natDegree ≤
      Nat.fromBitsLE (F.degree c) + Nat.fromBitsLE (F.queryBound c) := by
  have hp := ((natDegree_derivative_le (F.head c)).trans (Nat.sub_le _ _)).trans (F.head_degree c)
  exact natDegree_mul_le.trans (by have := F.query_degree c; omega)

theorem Family.guarded_value (F : Family) (q : List Bool) :
    (if valid F q then F.modular.value q else []) = F.residue q := by
  have hbound : Nat.fromBitsLE (boundCode F q) =
      Nat.fromBitsLE (F.degree (origin q)) + Nat.fromBitsLE (F.queryBound (origin q)) := by
    simp only [boundCode, BinaryNat.add_pair, Nat.fromBitsLE_bits]
  by_cases hv : valid F q
  · rw [ite_eq_left hv, Family.modular_value, Nat.mod_eq_of_lt (by
      simpa only [valid, hbound] using hv)]
    rfl
  · have hi : Nat.fromBitsLE (F.degree (origin q)) + Nat.fromBitsLE (F.queryBound (origin q)) + 1 ≤
        Nat.fromBitsLE (index q) := by simpa only [valid, hbound, not_lt] using hv
    have hz : F.coefficient (pairFst q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hd := PseudoRemainder.seed_natDegree_lt (F.head (origin q)) (F.query (origin q))
        (Nat.fromBitsLE (F.degree (origin q))) _ (F.degree_pos _) (F.input_degree _)
      change (F.reduced (origin q)).natDegree < Nat.fromBitsLE (index q)
      exact hd.trans_le (by omega)
    rw [ite_eq_right hv, Family.residue, hz]
    simp [integerResidue, residueBits, BinaryNatCode.encode]

def repack (s : List Bool) : List Bool :=
  pair (pair (origin (pairFst s)) (pairSnd s)) (BinaryNat.normalize (pairSnd (pairFst s)))

theorem origin_mem_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem index_mem_FP : index ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem modulusCode_mem_FP : modulusCode ∈ FP := by
  have h := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  refine mem_FP_of_eq (g := modulusCode) h ?_
  intro q
  simp only [modulusCode, Function.comp_apply]

theorem repack_mem_FP : repack ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP origin_mem_FP
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  have h := mem_FP_pair (mem_FP_pair hc pairSnd_mem_FP) hm
  refine mem_FP_of_eq (g := repack) h ?_
  intro s
  simp only [repack, Function.comp_apply]

theorem repack_packet (q : List Bool) (k : ℕ) :
    repack (pair q (BinaryNatCode.encode k)) =
      pair (pair (origin q) (BinaryNatCode.encode k)) (BinaryNatCode.encode (mValue q - 1)) := by
  simp only [repack, pairFst_pair, pairSnd_pair, mValue, Nat.add_sub_cancel,
    BinaryNat.normalize_eq_bits, BinaryNatCode.encode]

structure Access (F : Family) where
  headCoefficient : List Bool → List Bool
  queryCoefficient : List Bool → List Bool
  head_eq : ∀ c k m, 0 < m →
    headCoefficient (pair (pair c (BinaryNatCode.encode k)) (BinaryNatCode.encode (m - 1))) =
      integerResidue ((F.head c).coeff k) m
  query_eq : ∀ c k m, 0 < m →
    queryCoefficient (pair (pair c (BinaryNatCode.encode k)) (BinaryNatCode.encode (m - 1))) =
      integerResidue ((F.query c).coeff k) m

structure ControlsPolyTime (F : Family) : Prop where
  degree : F.degree ∈ FP
  queryBound : F.queryBound ∈ FP
  headMass : F.headMass ∈ FP
  queryMass : F.queryMass ∈ FP

theorem boundCode_mem_FP (F : Family) (hF : ControlsPolyTime F) : boundCode F ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp origin_mem_FP hF.degree)
    (mem_FP_comp origin_mem_FP hF.queryBound)) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := boundCode F) h ?_
  intro q
  simp only [boundCode, Function.comp_apply]

theorem selectedCode_mem_FP (F : Family) (hF : ControlsPolyTime F) : selectedCode F ∈ FP := by
  have hb := mem_FP_comp (boundCode_mem_FP F hF) BinaryNat.succ_mem_FP
  have h := mem_FP_comp (mem_FP_pair index_mem_FP hb) BinaryNat.mod_mem_FP
  refine mem_FP_of_eq (g := selectedCode F) h ?_
  intro q
  simp only [selectedCode, Function.comp_apply]

theorem valid_fppred (F : Family) (hF : ControlsPolyTime F) : FPPred (valid F) := by
  have h := BinaryNat.lt_fppred index_mem_FP (mem_FP_comp (boundCode_mem_FP F hF) BinaryNat.succ_mem_FP)
  exact h.of_iff fun q => by simp only [valid, Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]

namespace Access

set_option backward.isDefEq.respectTransparency false in
noncomputable def modular {F : Family} (a : Access F) : TarskiSeedBits.Access F.modular where
  source := {
    modulus := modulusCode
    headCoefficient := a.headCoefficient ∘ repack
    queryCoefficient := a.queryCoefficient ∘ repack
    modulus_eq q := by
      simp only [modulusCode, BinaryNat.succ_eq_bits, Family.modular, mValue, BinaryNatCode.encode]
    head_eq q k := by
      change a.headCoefficient (repack (pair q (BinaryNatCode.encode k))) = _
      rw [repack_packet, a.head_eq _ _ _ (by dsimp [mValue]; omega)]
      simp only [Family.modular, coeff_map, integerResidue, Int.coe_castRingHom]
    query_eq q k := by
      change a.queryCoefficient (repack (pair q (BinaryNatCode.encode k))) = _
      rw [repack_packet, a.query_eq _ _ _ (by dsimp [mValue]; omega)]
      simp only [Family.modular, coeff_map, integerResidue, Int.coe_castRingHom] }
  degree q := BinaryNat.normalize (F.degree (origin q))
  queryBound q := BinaryNat.normalize (F.queryBound (origin q))
  selected := selectedCode F
  degree_eq q := BinaryNat.normalize_eq_bits _
  queryBound_eq q := BinaryNat.normalize_eq_bits _
  selected_eq q := by
    simp only [selectedCode, boundCode, BinaryNat.mod_pair, BinaryNat.succ_eq_bits,
      BinaryNat.add_pair, Nat.fromBitsLE_bits, Family.modular, BinaryNatCode.encode]

theorem residueEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    SpaceFunction F.residue := by
  have hd := mem_FP_comp (mem_FP_comp origin_mem_FP hF.degree) BinaryNat.normalize_mem_FP
  have hq := mem_FP_comp (mem_FP_comp origin_mem_FP hF.queryBound) BinaryNat.normalize_mem_FP
  have hc : a.modular.ControlsPolyTime := by
    constructor
    · simpa only [modular] using modulusCode_mem_FP
    · simpa only [modular, Function.comp_def] using hd
    · simpa only [modular, Function.comp_def] using hq
    · simpa only [modular] using selectedCode_mem_FP F hF
  let M := TarskiSeedBits.Access.evaluator a.modular hc
    (P.precompose repack repack_mem_FP) (Q.precompose repack repack_mem_FP)
  let E := SpaceFunction.branch (fun q => decide (valid F q)) (valid_fppred F hF).flag_mem_FP M
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  exact E.congr (funext fun q => by simpa only [decide_eq_true_eq] using F.guarded_value q)

theorem budget_mem_FP {F : Family} (hF : ControlsPolyTime F) : F.budget ∈ FP := by
  have h := TarskiSeedBits.seedBudgetCode_mem_FP (mem_FP_comp pairFst_mem_FP hF.degree)
    (mem_FP_comp pairFst_mem_FP hF.queryBound) (mem_FP_comp pairFst_mem_FP hF.headMass)
    (mem_FP_comp pairFst_mem_FP hF.queryMass)
  refine mem_FP_of_eq (g := F.budget) h ?_
  intro r
  simp only [Family.budget, Function.comp_apply]

theorem signEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    SpaceFunction (fun r => if F.coefficient r = 0 then [] else
      if F.coefficient r < 0 then [true] else [false, true]) := by
  apply IntegerSignumBits.evaluator (residueEvaluator a hF P Q) F.budget (budget_mem_FP hF)
    F.coefficient F.coefficient_size
  intro r m hm
  simp only [Family.residue, pairFst_pair, mValue, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, Nat.sub_add_cancel (by omega : 1 ≤ m)]
  rfl

end Access
end LeanCanny.Algebra.IntegerTarskiSeedBits
