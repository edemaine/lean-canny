/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiFamily
public import LeanCanny.Algebra.FixedWidthHeadLiftSpace
public import LeanCanny.Algebra.FixedWidthBivariateReboxSpace
public import LeanCanny.Algebra.FixedWidthBivariateTernaryPower
/-! # Actual radius-window principal coefficient access

The endpoint is one unused coefficient variable in the head. The window
reader has exactly two signed monomials and preserves the caller modulus.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiFamily
open LeanCanny.Algebra LeanCanny.Computation Polynomial MvPolynomial MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def endpointLiftReader (A U :List Bool→ℕ)
    (p:(c:List Bool)→Polynomial (MvPolynomial (Fin (A c)) ℤ))
    (R:CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial A U p))
    (hA:UnaryFn A) (hU:UnaryFn U) (D:List Bool→ℕ)
    (hP:∀c y,((p c).coeff y).totalDegree≤D c) (hfit:∀c,D c<2^U c)
    (read:List Bool→List Bool) (hr:read∈FP) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial
      (fun c=>A (read c)+1) (U∘read) (fun c=>(p (read c)).map (MvPolynomial.rename Fin.succ).toRingHom)):=by
  let O:=FixedWidthBivariateReader.origin
  let target:=FixedWidthBivariateReboxBits.target
  let modulus:=FixedWidthBivariateReboxBits.modulus
  let y:=FixedWidthBivariateReboxBits.outer
  let r:=read∘O
  let W:=U∘r
  have HO:O∈FP:=FixedWidthBivariateReader.origin_FP
  have HR:r∈FP:=mem_FP_comp HO hr
  have HW:UnaryFn W:=hU.comp HR
  have HT:target∈FP:=by polytime [target,FixedWidthBivariateReboxBits.target]
  have HM:modulus∈FP:=by polytime [modulus,FixedWidthBivariateReboxBits.modulus]
  have HY:BinaryFn y:=BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have HS:=IntegerParameterCoefficientBits.spatial_mem_FP W target HW HT
  have E0:=FixedWidthBivariateRowBits.evaluator A U p R hA hU
    (fun c y=>(hP c y).trans_lt (hfit c)) r HR y HY
    (IntegerParameterCoefficientBits.spatial W target) modulus HS HM
  have E1:=FixedWidthHeadLiftBits.evaluator (A∘r) W (fun z=>(p (r z)).coeff (y z)) target modulus HW HT E0
  let Q:=fun c=>(p (read c)).map (MvPolynomial.rename Fin.succ).toRingHom
  have E:SpaceFunction (FixedWidthBivariateReboxBits.coefficient (fun c=>A (read c)+1) (U∘read) Q):=by
    exact E1.congr (funext fun z=>by
      unfold FixedWidthBivariateReboxBits.coefficient FixedWidthRowBits.value
      simp only [Q,Polynomial.coeff_map]
      rfl)
  refine FixedWidthBivariateReader.reader _ _ Q _ E (by exact (hA.comp hr).add (UnaryFn.const 1))
    (hU.comp hr) (D∘read) (fun c y=>?_) (fun c=>hfit (read c))
    (FixedWidthBivariateReboxBits.coefficient_packet _ _ Q)
  rw [Polynomial.coeff_map]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans (hP (read c) y)

theorem head_input_fit (c:List Bool) :inputBound c<2^FormulaSignSlotRadialRadiusHeadReader.width (original c):=
  FormulaSignSlotRadialEliminantPacked.result_fit _

theorem head_output_fit (c:List Bool) :inputBound c<2^width c:=by
  change inputBound c<2^((outputBound c+inputBound c+1).size)
  exact (by omega : inputBound c≤outputBound c+inputBound c+1).trans_lt (Nat.lt_size_self _)

theorem reader_fit (c:List Bool) :FormulaSignSlotRadialRadiusHeadReader.degree c<2^FormulaSignSlotRadialRadiusHeadReader.width c:=
  FormulaSignSlotRadialEliminantPacked.result_fit _

attribute [local irreducible] FormulaSignSlotRadialRadiusHeadReader.polynomial
  FormulaSignSlotRadialRadiusHeadReader.arity FormulaSignSlotRadialRadiusHeadReader.width
  FormulaSignSlotRadialRadiusHeadReader.degree

noncomputable def headReader :CertifiedPolynomial.BivariateReader
    (FixedWidthBivariateReader.polynomial arity width head):=by
  let A:=FormulaSignSlotRadialRadiusHeadReader.arity
  let U:=FormulaSignSlotRadialRadiusHeadReader.width
  let p:=FormulaSignSlotRadialRadiusHeadReader.polynomial
  have HA:UnaryFn A:=by
    unfold A FormulaSignSlotRadialRadiusHeadReader.arity FormulaSignSlotRadialRadiusHeadReader.original
    exact FormulaSignSlotSource.dimension_unary.comp
      (mem_FP_comp (f:=pairFst) (g:=pairFst) pairFst_mem_FP pairFst_mem_FP)
  have HU:UnaryFn U:=by
    unfold U FormulaSignSlotRadialRadiusHeadReader.width FormulaSignSlotRadialRadiusHeadReader.original
    exact FormulaSignSlotRadialEliminantPackingLayout.parameterWidth_unary.comp pairFst_mem_FP
  have HP:∀c y,((p c).coeff y).totalDegree≤FormulaSignSlotRadialRadiusHeadReader.degree c:=by
    intro c y
    unfold p FormulaSignSlotRadialRadiusHeadReader.polynomial FormulaSignSlotRadialRadiusHeadReader.degree
      FormulaSignSlotRadialRadiusHeadReader.arity
    exact FormulaSignSlotRadialRadiusHeadReader.radiusHeadReaderCoefficientDegree _ _ _ _
  let R:=endpointLiftReader A U p FormulaSignSlotRadialRadiusHeadReader.reader HA HU
    FormulaSignSlotRadialRadiusHeadReader.degree HP reader_fit original original_FP
  exact FixedWidthBivariateReboxBits.reader arity (U∘original) width head R arity_unary (HU.comp original_FP) width_unary
    (fun c y=>(head_coefficient_degree c y).trans_lt (head_input_fit c)) inputBound head_coefficient_degree head_output_fit

def modulusCode (z:List Bool):=BinaryNat.succ (FixedWidthBivariateReboxBits.modulus z)
theorem modulusCode_FP :modulusCode∈FP:=mem_FP_comp
  (by polytime [FixedWidthBivariateReboxBits.modulus]) BinaryNat.succ_mem_FP
def oneCode (z:List Bool):=ArithmeticBits.one (modulusCode z)
def negativeOneCode (z:List Bool):=ArithmeticBits.negate (pair (modulusCode z) (oneCode z))
theorem oneCode_FP :oneCode∈FP:=mem_FP_comp modulusCode_FP ArithmeticBits.one_mem_FP
attribute [local irreducible] ArithmeticBits.one ArithmeticBits.negate BinaryNat.succ
theorem negativeOneCode_FP :negativeOneCode∈FP:=mem_FP_comp
  (mem_FP_pair modulusCode_FP oneCode_FP) ArithmeticBits.negate_mem_FP
def windowValue (z:List Bool):=
  if FixedWidthBivariateReboxBits.outer z=1 ∧Nat.fromBitsLE (FixedWidthBivariateReboxBits.target z)=1 then oneCode z
  else if FixedWidthBivariateReboxBits.outer z=2 ∧Nat.fromBitsLE (FixedWidthBivariateReboxBits.target z)=0 then negativeOneCode z else []
theorem windowValue_FP :windowValue∈FP:=by
  have HY:BinaryFn FixedWidthBivariateReboxBits.outer:=BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have HX:BinaryFn (fun z=>Nat.fromBitsLE (FixedWidthBivariateReboxBits.target z)):=
    BinaryFn.fromBits (by polytime [FixedWidthBivariateReboxBits.target])
  exact ((HY.eq (BinaryFn.const 1)).and (HX.eq (BinaryFn.const 1))).ite_mem_FP oneCode_FP
    (((HY.eq (BinaryFn.const 2)).and (HX.eq (BinaryFn.const 0))).ite_mem_FP negativeOneCode_FP (constFn_mem_FP []))

theorem encoded_window (c:List Bool) :
    FixedWidthBivariateReader.polynomial arity width window c=
      Polynomial.monomial 1 (Polynomial.X:ℤ[X])-Polynomial.monomial 2 1:=by
  simp only [FixedWidthBivariateReader.polynomial,window,Polynomial.map_mul,Polynomial.map_sub,
    Polynomial.map_X,Polynomial.map_C,FixedWidthKronecker.encode,MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_X,Fin.val_zero,Nat.zero_mul,pow_zero,pow_one]
  simp only [←Polynomial.C_mul_X_pow_eq_monomial,pow_one,Polynomial.C_1]
  ring

theorem one_packet (q:List Bool) (u v:ℕ) :
    oneCode (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))=
      residueBits (1:ZMod (Nat.fromBitsLE (pairSnd q)+1)):=by
  simp only [oneCode,modulusCode,FixedWidthBivariateReboxBits.modulus,pairFst_pair]
  rw [BinaryNat.succ_eq_bits]
  exact ArithmeticBits.one_residueBits _
theorem negative_one_packet (q:List Bool) (u v:ℕ) :
    negativeOneCode (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))=
      residueBits (-1:ZMod (Nat.fromBitsLE (pairSnd q)+1)):=by
  rw [negativeOneCode,one_packet]
  simp only [modulusCode,FixedWidthBivariateReboxBits.modulus,pairFst_pair]
  rw [BinaryNat.succ_eq_bits]
  exact ArithmeticBits.negate_residueBits _ _

noncomputable def windowReader :CertifiedPolynomial.BivariateReader
    (FixedWidthBivariateReader.polynomial arity width window) where
  coefficient:=windowValue
  evaluator:=SpaceFunction.ofFP _ windowValue_FP
  coefficient_eq q u v:=by
    rw [encoded_window]
    unfold windowValue
    have HY:FixedWidthBivariateReboxBits.outer (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))=v:=by
      simp only [FixedWidthBivariateReboxBits.outer,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    have HX:Nat.fromBitsLE (FixedWidthBivariateReboxBits.target
        (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))=u:=by
      simp only [FixedWidthBivariateReboxBits.target,pairSnd_pair,pairFst_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    rw [HY,HX]
    have HO:=one_packet q u v
    have HN:=negative_one_packet q u v
    have HC:(((Polynomial.monomial 1 (Polynomial.X:ℤ[X])-Polynomial.monomial 2 1).coeff v).coeff u)=
        if v=1 ∧u=1 then 1 else if v=2 ∧u=0 then -1 else 0:=by
      by_cases hv1:v=1
      · subst v
        simp [Polynomial.coeff_monomial,Polynomial.coeff_X,eq_comm]
      · by_cases hv2:v=2
        · subst v
          by_cases hu:u=0 <;> simp [Polynomial.coeff_monomial,Polynomial.coeff_one,hu,eq_comm]
        · simp [Polynomial.coeff_monomial,hv1,hv2,Ne.symm hv1,Ne.symm hv2]
    rw [HC]
    by_cases H1:v=1 ∧u=1
    · rw [ite_eq_left H1,ite_eq_left H1,HO]
      rfl
    · by_cases H2:v=2 ∧u=0
      · rw [ite_eq_right H1,ite_eq_right H1,ite_eq_left H2,ite_eq_left H2,HN]
        rfl
      · rw [ite_eq_right H1,ite_eq_right H1,ite_eq_right H2,ite_eq_right H2]
        simp only [Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

noncomputable def queryReader :CertifiedPolynomial.BivariateReader
    (FixedWidthBivariateReader.polynomial arity width query):=by
  let e:List Bool→Fin 3:=fun c=>⟨moment c,by have H:=moment_le c;omega⟩
  exact FixedWidthBivariateTernaryPowerBits.reader arity width window windowReader e moment_binary

noncomputable def access :FixedWidthTarskiPrincipalBits.Access family where
  head:=by exact headReader
  query:=by exact queryReader
  degree:=degree_binary
  bound:=bound_binary
  seedDegree:=seedDegree_binary

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiFamily
