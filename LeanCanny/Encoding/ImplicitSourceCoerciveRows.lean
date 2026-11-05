/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ImplicitSourceCoercivePreparation
public import LeanCanny.Algebra.FixedWidthMonomialSpace
public import LeanCanny.Algebra.ModularResidueReaders
public import LeanCanny.Algebra.MacaulayFullBoxDeterminantSpace
/-! # The actual homogeneous coercive rows from implicit source access -/
@[expose] public section
namespace LeanCanny.Encoding.ImplicitSourceCoerciveBoxGram
open LeanCanny.Algebra LeanCanny.Computation Polynomial MatrixPower FixedWidthPolynomial
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def squareAt (S : Source) (input modulus : List Bool → List Bool) (q : List Bool) :=
  squareReader S (pair (pair (input (pairFst q)) (pairSnd q)) (modulus (pairFst q)))

theorem squareAt_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (input modulus : List Bool → List Bool) (hi : input ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (squareAt S input modulus) :=
  (square_evaluator S A).precompose _ (mem_FP_pair
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP hi) pairSnd_mem_FP) (mem_FP_comp pairFst_mem_FP hm))

theorem squareAt_packet (S : Source) (input modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    squareAt S input modulus (pair c (BinaryNatCode.encode r)) = residueBits
      (((S.polynomial (input c)^2).coeff (nativeExponent (Equiv.refl _) (workWidth S (input c)) r) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c)+1)) := by
  unfold squareAt
  rw [pairFst_pair, pairSnd_pair]
  let f (u : List Bool) (W r : ℕ) : ℤ := (S.polynomial u^2).coeff (nativeExponent (Equiv.refl _) W r)
  let g (u : List Bool) (W r m : ℕ) := residueBits (f u W r : ZMod (m+1))
  change g (RationalSubstitution.IntegerBits.context (pair (pair (input c) (BinaryNatCode.encode r)) (modulus c)))
      (workWidth S (RationalSubstitution.IntegerBits.context (pair (pair (input c) (BinaryNatCode.encode r)) (modulus c))))
      (Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree (pair (pair (input c) (BinaryNatCode.encode r)) (modulus c))))
        (Nat.fromBitsLE (pairSnd (pair (pair (input c) (BinaryNatCode.encode r)) (modulus c)))) =
      g (input c) (workWidth S (input c)) r (Nat.fromBitsLE (modulus c))
  simp only [RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def derivativeCoefficient (S : Source) (u : List Bool) (j W r : ℕ) : ℤ :=
  if hj : j<S.arity u then (MvPolynomial.pderiv ⟨j,hj⟩ (S.polynomial u^2)).coeff
    (nativeExponent (Equiv.refl _) W r) else 0

noncomputable def derivativeReader (S : Source) (input : List Bool → List Bool) (selected : List Bool → ℕ)
    (modulus : List Bool → List Bool) (q : List Bool) :=
  residueBits (derivativeCoefficient S (input (pairFst q)) (selected (pairFst q))
    (workWidth S (input (pairFst q))) (Nat.fromBitsLE (pairSnd q)) : ZMod (Nat.fromBitsLE (modulus (pairFst q))+1))

theorem derivative_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (input modulus : List Bool → List Bool) (selected : List Bool → ℕ)
    (hi : input ∈ FP) (hm : modulus ∈ FP) (hs : UnaryFn selected) :
    SpaceFunction (derivativeReader S input selected modulus) := by
  let I := input ∘ pairFst
  let M := modulus ∘ pairFst
  let N := S.arity ∘ I
  let W := workWidth S ∘ I
  let D := squareDegree S ∘ I
  let J := selected ∘ pairFst
  let C := squareAt S I M
  have hI : I ∈ FP := mem_FP_comp pairFst_mem_FP hi
  have hM : M ∈ FP := mem_FP_comp pairFst_mem_FP hm
  have hN : UnaryFn N := A.arity.comp hI
  have hW : UnaryFn W := (workWidth_unary S A).comp hI
  have hD : BinaryFn D := (((BinaryFn.const 2).mul A.degree).add (BinaryFn.const 1)).comp hI
  have hJ : UnaryFn J := hs.comp pairFst_mem_FP
  have E := FixedWidthDerivativeBits.evaluator_binary N W W D J pairSnd (BinaryNat.succ ∘ M)
    (squareAt_evaluator S A I M hI hM) hN hW hW hD hJ pairSnd_mem_FP (mem_FP_comp hM BinaryNat.succ_mem_FP)
  have HG := (BinaryFn.ofUnary hJ).lt (BinaryFn.ofUnary hN)
  have EB := SpaceFunction.branch (fun q => decide (J q<N q)) HG.flag_mem_FP E
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine EB.congr (funext fun q => ?_)
  by_cases hj : J q<N q
  · simp only [hj, decide_true, ite_true]
    have HP := FixedWidthDerivativeBits.packet N W W D J pairSnd (BinaryNat.succ ∘ M)
      (Equiv.refl _) C q (S.polynomial (I q)^2) ⟨J q,hj⟩ (Nat.fromBitsLE (M q)+1) rfl rfl
      (by dsimp [D, squareDegree]; omega)
      ((MvPolynomial.totalDegree_pow _ 2).trans (by dsimp [D, squareDegree]; nlinarith [S.polynomial_degree (I q)]))
      (work_fit S (I q)) (by rw [Function.comp_apply, BinaryNat.succ_eq_bits]; rfl)
      (fun r => squareAt_packet S I M q r)
    have HX : FixedWidthDerivativeBits.exponent W pairSnd (Equiv.refl _) q =
        nativeExponent (Equiv.refl (Fin (N q))) (W q) (Nat.fromBitsLE (pairSnd q)) := by
      ext i
      exact (FixedWidthPowerMonomial.native_coordinate N W pairSnd q i).symm
    rw [HX] at HP
    have hj' : selected (pairFst q)<S.arity (input (pairFst q)) := hj
    exact HP.trans (by unfold derivativeReader derivativeCoefficient; rw [dite_eq_left hj']; rfl)
  · simp only [hj, decide_false, Bool.false_eq_true, ite_false]
    unfold derivativeReader derivativeCoefficient
    have hj' : ¬selected (pairFst q)<S.arity (input (pairFst q)) := hj
    rw [dite_eq_right hj']
    simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

noncomputable def ordinaryValue (S : Source) (input : List Bool → List Bool) (selected : List Bool → ℕ)
    (modulus : List Bool → List Bool) := HomogenizationBits.value (S.arity ∘ input) (S.arity ∘ input)
      (workWidth S ∘ input) (squareDegree S ∘ input) (derivativeReader S input selected modulus)

theorem ordinary_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (input modulus : List Bool → List Bool) (selected : List Bool → ℕ)
    (hi : input ∈ FP) (hm : modulus ∈ FP) (hs : UnaryFn selected) : SpaceFunction (ordinaryValue S input selected modulus) :=
  HomogenizationBits.evaluator_binary_degree (A.arity.comp hi) (A.arity.comp hi) ((workWidth_unary S A).comp hi)
    ((((BinaryFn.const 2).mul A.degree).add (BinaryFn.const 1)).comp hi)
    (derivative_evaluator S A input modulus selected hi hm hs)

theorem ordinary_packet (S : Source) (input modulus : List Bool → List Bool) (selected : List Bool → ℕ)
    (c : List Bool) (j : Fin (S.arity (input c))) (hj : selected c=j.val) (r : ℕ) :
    ordinaryValue S input selected modulus (pair c (BinaryNatCode.encode r)) = residueBits
      (((WeightedHomogenization.homogenize (fun _ => 1) (squareDegree S (input c))
        (MvPolynomial.pderiv j (S.polynomial (input c)^2))).coeff
          (nativeExponent CoerciveCriticalHomogenization.layout (workWidth S (input c)) r) : ℤ) :
            ZMod (Nat.fromBitsLE (modulus c)+1)) := by
  have HP (k : ℕ) : derivativeReader S input selected modulus (pair c (BinaryNatCode.encode k)) = residueBits
      (((MvPolynomial.pderiv j (S.polynomial (input c)^2)).coeff
        (nativeExponent (Equiv.refl _) (workWidth S (input c)) k) : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1)) := by
    unfold derivativeReader
    rw [pairFst_pair, pairSnd_pair]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, hj, derivativeCoefficient, dite_eq_left j.isLt]
  simpa only [HomogenizationLayout.prefixWeight_all, ordinaryValue, CoerciveCriticalHomogenization.layout,
    Function.comp_apply] using HomogenizationBits.value_packet (S.arity ∘ input) (S.arity ∘ input)
      (workWidth S ∘ input) (squareDegree S ∘ input) (derivativeReader S input selected modulus) c (Equiv.refl _)
      (MvPolynomial.pderiv j (S.polynomial (input c)^2))
      (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (modulus c)+1)))
      (by simp [residueBits, BinaryNatCode.encode]) HP r

namespace Rows
def context (q : List Bool) := pairFst q
def row (q : List Bool) := Nat.fromBitsLE (pairFst (pairSnd q))
def rank (q : List Bool) := pairFst (pairSnd (pairSnd q))
def inner (q : List Bool) := Nat.fromBitsLE (pairFst (pairSnd (pairSnd (pairSnd q))))
def outer (q : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd (pairSnd (pairSnd q))))
def packet (c : List Bool) (j r u v : ℕ) := pair c (pair (BinaryNatCode.encode j)
  (pair (BinaryNatCode.encode r) (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))
theorem context_FP : context ∈ FP := pairFst_mem_FP
theorem row_binary : BinaryFn row := BinaryFn.fromBits (by polytime)
theorem rank_FP : rank ∈ FP := by polytime [rank]
theorem inner_binary : BinaryFn inner := BinaryFn.fromBits (by polytime)
theorem outer_binary : BinaryFn outer := BinaryFn.fromBits (by polytime)
def phase (u v : ℕ) (q : List Bool) := inner q=u ∧ outer q=v
noncomputable instance (u v : ℕ) : DecidablePred (phase u v) := fun _ => inferInstance
theorem phase_FP (u v : ℕ) : FPPred (phase u v) :=
  (inner_binary.eq (BinaryFn.const u)).and (outer_binary.eq (BinaryFn.const v))

def selected (S : Source) (input : List Bool → List Bool) (q : List Bool) :=
  min (row q) (S.arity (input (context q))+1)-1
theorem selected_unary (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (input : List Bool → List Bool) (hi : input ∈ FP) : UnaryFn (selected S input) :=
  (UnaryFn.fromBitsLE_min (by polytime)
    (((A.arity.comp hi).comp context_FP).add (UnaryFn.const 1))).sub (UnaryFn.const 1)

def target (S : Source) (input : List Bool → List Bool) :=
  FixedWidthQuery.repack (fun q => S.arity (input (context q))+1) (rowWidth S ∘ input ∘ context)
    (fun q => S.arity (input (context q))+1) (workWidth S ∘ input ∘ context) rank
theorem target_FP (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (input : List Bool → List Bool) (hi : input ∈ FP) : target S input ∈ FP :=
  FixedWidthQuery.repack_mem_FP (((A.arity.comp hi).comp context_FP).add (UnaryFn.const 1))
    (((rowWidth_unary S A).comp hi).comp context_FP)
    (((A.arity.comp hi).comp context_FP).add (UnaryFn.const 1))
    (((workWidth_unary S A).comp hi).comp context_FP) rank_FP

theorem target_exponent (S : Source) (input : List Bool → List Bool) (q : List Bool) :
    nativeExponent (CoerciveCriticalHomogenization.layout (n := S.arity (input (context q)))) (workWidth S (input (context q)))
      (Nat.fromBitsLE (target S input q)) =
    nativeExponent (CoerciveCriticalHomogenization.layout (n := S.arity (input (context q)))) (rowWidth S (input (context q))) (Nat.fromBitsLE (rank q)) :=
  nativeExponent_repack (CoerciveCriticalHomogenization.layout (n := S.arity (input (context q)))) (rowWidth S ∘ input ∘ context)
    (workWidth S ∘ input ∘ context) rank q (Nat.le_max_left _ _)

noncomputable def ordinary (S : Source) (input modulus : List Bool → List Bool) (q : List Bool) :=
  ordinaryValue S (input ∘ context) (selected S input) (modulus ∘ context)
    (pair q (BinaryNat.normalize (target S input q)))
theorem ordinary_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (input modulus : List Bool → List Bool) (hi : input ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (ordinary S input modulus) :=
  (ImplicitSourceCoerciveBoxGram.ordinary_evaluator S A (input ∘ context) (modulus ∘ context)
    (selected S input) (mem_FP_comp context_FP hi) (mem_FP_comp context_FP hm) (selected_unary S A input hi)).precompose _
      (mem_FP_pair id_mem_FP (mem_FP_comp (target_FP S A input hi) BinaryNat.normalize_mem_FP))

noncomputable def sparse (S : Source) (input modulus : List Bool → List Bool)
    (j d f : List Bool → ℕ) := FixedWidthRowBits.value (fun q => S.arity (input (context q))+1)
      (workWidth S ∘ input ∘ context)
      (FixedWidthMonomialBits.polynomial (fun q => S.arity (input (context q))+1) j d (fun q => (f q : ℤ)))
      (target S input) (modulus ∘ context)

theorem sparse_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (input modulus : List Bool → List Bool) (j d f : List Bool → ℕ)
    (hi : input ∈ FP) (hm : modulus ∈ FP) (hj : BinaryFn j) (hd : BinaryFn d) (hf : BinaryFn f) :
    SpaceFunction (sparse S input modulus j d f) := by
  let reader := fun q => residueBits (f q : ZMod (Nat.fromBitsLE (modulus (context q))+1))
  have ER : reader ∈ FP := by
    have H := mem_FP_comp (mem_FP_pair hf.bits_mem_FP
      (mem_FP_comp (mem_FP_comp context_FP hm) BinaryNat.succ_mem_FP)) BinaryNat.mod_mem_FP
    exact mem_FP_of_eq H (fun q => by simp only [Function.comp_apply, BinaryNat.mod_pair,
      BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, reader, residueBits, ZMod.val_natCast, BinaryNatCode.encode])
  exact FixedWidthMonomialBits.coefficient_evaluator _ _ j d (target S input) (fun q => (f q : ℤ))
    (modulus ∘ context) reader (SpaceFunction.ofFP _ ER) (fun _ => by simp only [Int.cast_natCast]; rfl)
    (((A.arity.comp hi).comp context_FP).add (UnaryFn.const 1))
    (((workWidth_unary S A).comp hi).comp context_FP) hj hd (target_FP S A input hi)

noncomputable def coordinatePart (S : Source) (input modulus : List Bool → List Bool) (coordinate : List Bool → ℕ) :=
  ModularResidueReaders.addValue (modulus ∘ context)
    (ModularResidueReaders.maskValue (phase 1 0) (sparse S input modulus (fun _ => 0) (fun _ => 1) (fun _ => 1)))
    (ModularResidueReaders.negValue (modulus ∘ context)
      (ModularResidueReaders.maskValue (phase 0 0) (sparse S input modulus (fun q => coordinate (context q)+1) (fun _ => 1) (fun _ => 1))))

noncomputable def gradientPart (S : Source) (input modulus : List Bool → List Bool) :=
  ModularResidueReaders.addValue (modulus ∘ context)
    (ModularResidueReaders.maskValue (phase 0 0) (ordinary S input modulus))
    (ModularResidueReaders.maskValue (phase 0 1) (sparse S input modulus (fun q => selected S input q+1)
      (squareDegree S ∘ input ∘ context) (fun q => 2*S.degree (input (context q))+2)))

def valid (S : Source) (input : List Bool → List Bool) (coordinate : List Bool → ℕ) (q : List Bool) :=
  coordinate (context q)<S.arity (input (context q)) ∧ row q<S.arity (input (context q))+1
noncomputable instance (S : Source) (input : List Bool → List Bool) (coordinate : List Bool → ℕ) : DecidablePred (valid S input coordinate) :=
  fun _ => inferInstance
theorem valid_FP (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (input : List Bool → List Bool) (coordinate : List Bool → ℕ) (hi : input ∈ FP) (hc : BinaryFn coordinate) :
    FPPred (valid S input coordinate) := by
  have HC : BinaryFn (coordinate ∘ context) := hc.comp context_FP
  have HN : BinaryFn (S.arity ∘ input ∘ context) := (BinaryFn.ofUnary A.arity).comp (mem_FP_comp context_FP hi)
  exact (HC.lt HN).and (row_binary.lt (HN.add (BinaryFn.const 1)))

noncomputable def program (S : Source) (input modulus : List Bool → List Bool) (coordinate : List Bool → ℕ) (q : List Bool) :=
  if valid S input coordinate q then if row q=0 then coordinatePart S input modulus coordinate q else gradientPart S input modulus q else []

theorem program_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (input modulus : List Bool → List Bool) (coordinate : List Bool → ℕ)
    (hi : input ∈ FP) (hm : modulus ∈ FP) (hc : BinaryFn coordinate) : SpaceFunction (program S input modulus coordinate) := by
  have H0 := sparse_evaluator S A input modulus (fun _ => 0) (fun _ => 1) (fun _ => 1) hi hm (BinaryFn.const 0) (BinaryFn.const 1) (BinaryFn.const 1)
  have HCC : BinaryFn (coordinate ∘ context) := hc.comp context_FP
  have HC := sparse_evaluator S A input modulus (fun q => coordinate (context q)+1) (fun _ => 1) (fun _ => 1)
    hi hm (HCC.add (BinaryFn.const 1)) (BinaryFn.const 1) (BinaryFn.const 1)
  have HL := sparse_evaluator S A input modulus (fun q => selected S input q+1) (squareDegree S ∘ input ∘ context)
    (fun q => 2*S.degree (input (context q))+2) hi hm
    ((BinaryFn.ofUnary (selected_unary S A input hi)).add (BinaryFn.const 1))
    ((((BinaryFn.const 2).mul A.degree).add (BinaryFn.const 1)).comp (mem_FP_comp context_FP hi))
    ((((BinaryFn.const 2).mul A.degree).add (BinaryFn.const 2)).comp (mem_FP_comp context_FP hi))
  have HM := mem_FP_comp context_FP hm
  have EC := ModularResidueReaders.addEvaluator HM (ModularResidueReaders.maskEvaluator (phase_FP 1 0) H0)
    (ModularResidueReaders.negEvaluator HM (ModularResidueReaders.maskEvaluator (phase_FP 0 0) HC))
  have EG := ModularResidueReaders.addEvaluator HM
    (ModularResidueReaders.maskEvaluator (phase_FP 0 0) (ordinary_evaluator S A input modulus hi hm))
    (ModularResidueReaders.maskEvaluator (phase_FP 0 1) HL)
  exact (SpaceFunction.branch (fun q => decide (valid S input coordinate q)) (valid_FP S A input coordinate hi hc).flag_mem_FP
    (SpaceFunction.branch (fun q => decide (row q=0)) (row_binary.eq (BinaryFn.const 0)).flag_mem_FP EC EG)
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))).congr
      (funext fun q => by simp only [program, decide_eq_true_eq]; rfl)

theorem sparse_at (S : Source) (input modulus : List Bool → List Bool) (j d f : List Bool → ℕ)
    (q : List Bool) (k : Option (Fin (S.arity (input (context q)))))
    (hk : j q=(CoerciveCriticalHomogenization.layout k).val) :
    sparse S input modulus j d f q = residueBits
      (((MvPolynomial.monomial (Finsupp.single k (d q)) (f q : ℤ)).coeff
        (nativeExponent CoerciveCriticalHomogenization.layout (rowWidth S (input (context q)))
          (Nat.fromBitsLE (rank q))) : ℤ) : ZMod (Nat.fromBitsLE (modulus (context q))+1)) := by
  have hfit : j q<S.arity (input (context q))+1 := hk ▸ (CoerciveCriticalHomogenization.layout k).isLt
  unfold sparse FixedWidthRowBits.value FixedWidthMonomialBits.polynomial
  rw [dite_eq_left hfit]
  have HE : (⟨j q,hfit⟩ : Fin (S.arity (input (context q))+1))=CoerciveCriticalHomogenization.layout k := Fin.ext hk
  rw [HE]
  dsimp only [Function.comp_apply]
  have HC := FixedWidthPolynomial.coeff_rename_rank CoerciveCriticalHomogenization.layout
    (MvPolynomial.monomial (Finsupp.single k (d q)) (f q : ℤ))
    (workWidth S (input (context q))) (Nat.fromBitsLE (target S input q))
  simp only [MvPolynomial.rename_monomial, Finsupp.mapDomain_single] at HC
  have HN : nativeExponent (Equiv.refl (Fin (S.arity (input (context q))+1)))
      (workWidth S (input (context q))) (Nat.fromBitsLE (target S input q)) =
      RationalSubstitution.Indexed.exponentVector (S.arity (input (context q))+1)
        (FixedWidthPolynomial.entry (workWidth S (input (context q))) (Nat.fromBitsLE (target S input q))) := rfl
  rw [HN, HC, target_exponent]

theorem ordinary_at (S : Source) (input modulus : List Bool → List Bool) (q : List Bool)
    (j : Fin (S.arity (input (context q)))) (hj : selected S input q=j.val) :
    ordinary S input modulus q = residueBits
      (((WeightedHomogenization.homogenize (fun _ => 1) (squareDegree S (input (context q)))
        (MvPolynomial.pderiv j (S.polynomial (input (context q))^2))).coeff
          (nativeExponent CoerciveCriticalHomogenization.layout (rowWidth S (input (context q)))
            (Nat.fromBitsLE (rank q))) : ℤ) : ZMod (Nat.fromBitsLE (modulus (context q))+1)) := by
  unfold ordinary
  rw [BinaryNat.normalize_eq_bits]
  change ordinaryValue S (input ∘ context) (selected S input) (modulus ∘ context)
    (pair q (BinaryNatCode.encode (Nat.fromBitsLE (target S input q)))) = _
  have H := ordinary_packet S (input ∘ context) (modulus ∘ context) (selected S input) q j hj
    (Nat.fromBitsLE (target S input q))
  dsimp only [Function.comp_apply] at H
  rw [target_exponent] at H
  exact H

theorem program_value (S : Source) (input modulus : List Bool → List Bool) (coordinate : List Bool → ℕ)
    (q : List Bool) (hc : coordinate (context q)<S.arity (input (context q)))
    (hr : row q<S.arity (input (context q))+1) :
    program S input modulus coordinate q = MacaulayFullBoxBits.scalar modulus (context q) (inner q) (outer q)
      ((CoerciveCriticalHomogenization.finSystem (S.polynomial (input (context q))) (S.degree (input (context q)))
        ⟨coordinate (context q),hc⟩ ⟨row q,hr⟩).coeff
        (RationalSubstitution.Indexed.exponentVector (S.arity (input (context q))+1)
          (FixedWidthPolynomial.entry (rowWidth S (input (context q))) (Nat.fromBitsLE (rank q))))) := by
  unfold program
  rw [ite_eq_left (show valid S input coordinate q from ⟨hc,hr⟩)]
  by_cases hz : row q=0
  · rw [ite_eq_left hz]
    have Hrow : (⟨row q,hr⟩ : Fin (S.arity (input (context q))+1))=0 := Fin.ext hz
    rw [Hrow]
    have HP := sparse_at S input modulus (fun _ => 0) (fun _ => 1) (fun _ => 1) q none
      (by simp only [CoerciveHomogeneousLayout.layout_none, Fin.val_zero])
    have HM := sparse_at S input modulus (fun q => coordinate (context q)+1) (fun _ => 1) (fun _ => 1)
      q (some ⟨coordinate (context q),hc⟩) (by simp only [CoerciveHomogeneousLayout.layout_some, Fin.val_succ])
    have EP := ModularResidueReaders.maskValue_eq (phase 1 0) _ q _ HP
    have EM := ModularResidueReaders.maskValue_eq (phase 0 0) _ q _ HM
    have EN := ModularResidueReaders.negValue_eq (modulus ∘ context) _ q _ EM
    have H := ModularResidueReaders.addValue_eq (modulus ∘ context) _ _ q _ _ EP EN
    change coordinatePart S input modulus coordinate q = _ at H
    refine H.trans ?_
    rw [MacaulayFullBoxBits.scalar, CoerciveHomogeneousLayout.fin_coordinate_coeff]
    simp only [phase, sub_eq_add_neg, Int.cast_add, Int.cast_neg, Int.cast_ite, Int.cast_zero, Int.natCast_one, and_comm]
  · rw [ite_eq_right hz]
    let j : Fin (S.arity (input (context q))) := ⟨row q-1,by omega⟩
    have Hrow : (⟨row q,hr⟩ : Fin (S.arity (input (context q))+1))=j.succ := Fin.ext (by dsimp [j]; omega)
    have Hsel : selected S input q=j.val := by unfold selected; rw [min_eq_left (by omega)]
    rw [Hrow]
    have HP := ordinary_at S input modulus q j Hsel
    have HM := sparse_at S input modulus (fun q => selected S input q+1)
      (squareDegree S ∘ input ∘ context) (fun q => 2*S.degree (input (context q))+2) q (some j)
      (by simp only [CoerciveHomogeneousLayout.layout_some, Fin.val_succ, Hsel])
    have EP := ModularResidueReaders.maskValue_eq (phase 0 0) _ q _ HP
    have EM := ModularResidueReaders.maskValue_eq (phase 0 1) _ q _ HM
    have H := ModularResidueReaders.addValue_eq (modulus ∘ context) _ _ q _ _ EP EM
    change gradientPart S input modulus q = _ at H
    refine H.trans ?_
    rw [MacaulayFullBoxBits.scalar, CoerciveHomogeneousLayout.fin_gradient]
    simp only [phase, squareDegree, Function.comp_apply, Int.cast_add, Int.cast_ite, Int.cast_zero, and_comm]

theorem program_packet (S : Source) (input modulus : List Bool → List Bool) (coordinate : List Bool → ℕ)
    (c : List Bool) (hc : coordinate c<S.arity (input c)) (j : Fin (S.arity (input c)+1)) (r u v : ℕ) :
    program S input modulus coordinate (packet c j.val r u v) = MacaulayFullBoxBits.scalar modulus c u v
      (((CoerciveCriticalHomogenization.finSystem (S.polynomial (input c)) (S.degree (input c)))
        ⟨coordinate c,hc⟩ j).coeff (RationalSubstitution.Indexed.exponentVector (S.arity (input c)+1)
          (FixedWidthPolynomial.entry (rowWidth S (input c)) r))) := by
  let f (c : List Bool) (j r u v : ℕ) := if hc : coordinate c<S.arity (input c) then
    if hj : j<S.arity (input c)+1 then MacaulayFullBoxBits.scalar modulus c u v
      (((CoerciveCriticalHomogenization.finSystem (S.polynomial (input c)) (S.degree (input c)))
        ⟨coordinate c,hc⟩ ⟨j,hj⟩).coeff (RationalSubstitution.Indexed.exponentVector (S.arity (input c)+1)
          (FixedWidthPolynomial.entry (rowWidth S (input c)) r))) else [] else []
  have HR : program S input modulus coordinate (packet c j.val r u v) =
      f (context (packet c j.val r u v)) (row (packet c j.val r u v))
        (Nat.fromBitsLE (rank (packet c j.val r u v))) (inner (packet c j.val r u v)) (outer (packet c j.val r u v)) := by
    unfold f
    rw [dite_eq_left (show coordinate (context (packet c j.val r u v))<S.arity (input (context (packet c j.val r u v))) by simpa only [context,packet,pairFst_pair] using hc),
      dite_eq_left (show row (packet c j.val r u v)<S.arity (input (context (packet c j.val r u v)))+1 by
        simpa only [row,context,packet,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using j.isLt)]
    exact program_value S input modulus coordinate _ _ _
  simp only [context,row,rank,inner,outer,packet,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] at HR
  exact HR.trans (by dsimp only [f]; rw [dite_eq_left hc,dite_eq_left j.isLt])

end Rows
end LeanCanny.Encoding.ImplicitSourceCoerciveBoxGram
