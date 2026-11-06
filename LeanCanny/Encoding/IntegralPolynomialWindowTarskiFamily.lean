/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPolynomialRadiusReader
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiAccess
public import LeanCanny.Algebra.FixedWidthTarskiAffineMass
/-! # Window Tarski families constructed from an actual radius-first source

The first input variable is radius. The resulting coefficient variables
are the interval endpoint followed by the unchanged center variables.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralPolynomialWindowTarski
open LeanCanny.Algebra LeanCanny.Computation Polynomial MvPolynomial
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
abbrev original:=FormulaSignSlotRadialRadiusTarskiFamily.original
abbrev degreeWord:=FormulaSignSlotRadialRadiusTarskiFamily.degreeWord
abbrev seedWord:=FormulaSignSlotRadialRadiusTarskiFamily.seedWord
abbrev moment:=FormulaSignSlotRadialRadiusTarskiFamily.moment

noncomputable def inputBound (S:Source) (c:List Bool):=S.degree (original c)
noncomputable def arity (N:List Bool→ℕ) (c:List Bool):=N (original c)+1
noncomputable def degree (S:Source) (c:List Bool):=min (Nat.fromBitsLE (degreeWord c)) (inputBound S c)+1
noncomputable def seedDegree (S:Source) (c:List Bool):=min (Nat.fromBitsLE (seedWord c)) (inputBound S c)
noncomputable def bound (S:Source) (c:List Bool):=inputBound S c+5
noncomputable def outputBound (S:Source) (c:List Bool):=MultivariateTarskiDegreeBounds.principalDegreeBound
  (degree S c) (seedDegree S c) (bound S c) (inputBound S c) 2
noncomputable def width (S:Source) (c:List Bool):=(outputBound S c+inputBound S c+1).size
noncomputable def head (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (c:List Bool):Polynomial (MvPolynomial (Fin (arity N c)) ℤ):=
  (IntegralPolynomialRadiusReader.polynomial S N hd (original c)).map (MvPolynomial.rename Fin.succ).toRingHom
local instance windowTarskiArityNeZero (N:List Bool→ℕ) (c:List Bool):NeZero (arity N c):=⟨by unfold arity;omega⟩
noncomputable def window (N:List Bool→ℕ) (c:List Bool):Polynomial (MvPolynomial (Fin (arity N c)) ℤ):=
  Polynomial.X*(Polynomial.C (MvPolynomial.X 0)-Polynomial.X)
noncomputable def query (N:List Bool→ℕ) (c:List Bool):=(window N c)^(moment c)

private theorem binary_min {f g:List Bool→ℕ} (hf:BinaryFn f) (hg:BinaryFn g):BinaryFn (fun c=>min (f c) (g c)):=
  (BinaryFn.ite (hf.le hg) hf hg).of_eq (fun _=>Nat.min_def.symm)
theorem inputBound_binary (S:Source) (A:IntegralFramedBankPolynomialModel.Access S):BinaryFn (inputBound S):=
  A.degree.comp FormulaSignSlotRadialRadiusTarskiFamily.original_FP
theorem arity_unary (N:List Bool→ℕ) (HN:UnaryFn N):UnaryFn (arity N):=
  (HN.comp FormulaSignSlotRadialRadiusTarskiFamily.original_FP).add (UnaryFn.const 1)
theorem degree_binary (S:Source) (A:IntegralFramedBankPolynomialModel.Access S):BinaryFn (degree S):=
  (binary_min (BinaryFn.fromBits FormulaSignSlotRadialRadiusTarskiFamily.degreeWord_FP) (inputBound_binary S A)).add (BinaryFn.const 1)
theorem seedDegree_binary (S:Source) (A:IntegralFramedBankPolynomialModel.Access S):BinaryFn (seedDegree S):=
  binary_min (BinaryFn.fromBits FormulaSignSlotRadialRadiusTarskiFamily.seedWord_FP) (inputBound_binary S A)
theorem bound_binary (S:Source) (A:IntegralFramedBankPolynomialModel.Access S):BinaryFn (bound S):=
  (inputBound_binary S A).add (BinaryFn.const 5)
theorem outputBound_binary (S:Source) (A:IntegralFramedBankPolynomialModel.Access S):BinaryFn (outputBound S):=
  MultivariateTarskiDegreeBounds.principalDegreeBound_binary (degree_binary S A) (seedDegree_binary S A)
    (bound_binary S A) (inputBound_binary S A) (BinaryFn.const 2)
theorem width_unary (S:Source) (A:IntegralFramedBankPolynomialModel.Access S):UnaryFn (width S):=
  (UnaryFn.length (((outputBound_binary S A).add (inputBound_binary S A)).add (BinaryFn.const 1)).bits_mem_FP).of_eq
    (fun _=>BinaryNatCode.length_encode _)

theorem head_degree (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (c:List Bool):
    (head S N hd c).natDegree ≤ inputBound S c:=
  Polynomial.natDegree_map_le.trans (IntegralPolynomialRadiusReader.polynomial_degree S N hd _)
theorem head_coefficient_degree (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (c:List Bool) (i:ℕ):
    ((head S N hd c).coeff i).totalDegree ≤ inputBound S c:=by
  rw [head,Polynomial.coeff_map]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans (IntegralPolynomialRadiusReader.coefficient_degree S N hd _ i)
theorem head_coefficient_mass (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (c:List Bool) (i:ℕ):
    MvMass.mass ((head S N hd c).coeff i) ≤ 2^S.mass (original c):=by
  rw [head,Polynomial.coeff_map]
  exact (MvMass.rename_le _ _).trans (IntegralPolynomialRadiusReader.coefficient_mass S N hd _ i)

theorem window_degree (N:List Bool→ℕ) (c:List Bool):(window N c).natDegree ≤ 2:=by
  unfold window
  apply Polynomial.natDegree_mul_le.trans
  have HC:(Polynomial.C (MvPolynomial.X (0:Fin (arity N c))):Polynomial (MvPolynomial (Fin (arity N c)) ℤ)).natDegree=0:=Polynomial.natDegree_C _
  have HD:=Polynomial.natDegree_sub_le (Polynomial.C (MvPolynomial.X (0:Fin (arity N c))):Polynomial (MvPolynomial (Fin (arity N c)) ℤ)) Polynomial.X
  rw [HC,Polynomial.natDegree_X] at HD
  rw [Polynomial.natDegree_X]
  omega

theorem window_monomials (N:List Bool→ℕ) (c:List Bool):window N c=
    Polynomial.monomial 1 (MvPolynomial.X (0:Fin (arity N c)))-Polynomial.monomial 2 1:=by
  simp only [window,←Polynomial.C_mul_X_pow_eq_monomial,pow_one,Polynomial.C_1]
  ring
theorem window_coefficient_degree (N:List Bool→ℕ) (c:List Bool) (i:ℕ):((window N c).coeff i).totalDegree ≤ 1:=by
  rw [window_monomials,Polynomial.coeff_sub,Polynomial.coeff_monomial,Polynomial.coeff_monomial]
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · split_ifs <;> simp
  · split_ifs <;> simp
theorem query_coefficient_degree (N:List Bool→ℕ) (c:List Bool) (i:ℕ):((query N c).coeff i).totalDegree ≤ 2:=by
  unfold query moment FormulaSignSlotRadialRadiusTarskiFamily.moment
  split_ifs
  · simpa only [pow_one] using (window_coefficient_degree N c i).trans (by omega:1 ≤ 2)
  · rw [pow_two]
    exact MultivariateTarskiDegreeBounds.mul_coefficient _ _ 1 1 (window_coefficient_degree N c) (window_coefficient_degree N c) i

theorem query_degree (N:List Bool→ℕ) (c:List Bool):(query N c).natDegree ≤ 4:=
  calc
    _ ≤ moment c*(window N c).natDegree:=Polynomial.natDegree_pow_le
    _ ≤ 2*2:=Nat.mul_le_mul (FormulaSignSlotRadialRadiusTarskiFamily.moment_le c) (window_degree N c)
    _ = 4:=by decide

theorem input_degree (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (c:List Bool):
    ((query N c)*(head S N hd c).derivative).natDegree ≤ bound S c:=by
  have HD:=(Polynomial.natDegree_derivative_le (head S N hd c)).trans (Nat.sub_le _ _)
  have H:=Polynomial.natDegree_mul_le.trans (Nat.add_le_add (query_degree N c) (HD.trans (head_degree S N hd c)))
  unfold bound
  omega

noncomputable def family (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1):FixedWidthTarskiPrincipalBits.Family where
  arity:=arity N
  width:=width S
  head:=head S N hd
  query:=query N
  degree:=degree S
  bound:=bound S
  seedDegree:=seedDegree S
  degree_pos _:=Nat.zero_lt_succ _
  degree_le c:=by
    have H:=Nat.min_le_right (Nat.fromBitsLE (degreeWord c)) (inputBound S c)
    unfold degree bound
    omega
  input_degree:=input_degree S N hd

theorem polynomial_degree (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (c:List Bool) (j:ℕ):
    (FixedWidthTarskiPrincipalBits.polynomial (family S N hd) c j).totalDegree ≤ outputBound S c:=
  MultivariateTarskiDegreeBounds.principal_seed _ _ _ _ _ _ _ _
    (head_coefficient_degree S N hd c) (query_coefficient_degree N c)

theorem output_fit (S:Source) (c:List Bool):outputBound S c < 2^width S c:=by
  unfold width
  exact (by omega:outputBound S c ≤ outputBound S c+inputBound S c+1).trans_lt (Nat.lt_size_self _)
theorem head_fit (S:Source) (c:List Bool):inputBound S c < 2^width S c:=by
  unfold width
  exact (by omega:inputBound S c ≤ outputBound S c+inputBound S c+1).trans_lt (Nat.lt_size_self _)

noncomputable def headReader (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1)
    (A:IntegralFramedBankPolynomialModel.Access S) (HN:UnaryFn N) (hfit:∀c,S.degree c < 2^S.width c):
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (arity N) (width S) (head S N hd)):=by
  let R0:=IntegralPolynomialRadiusReader.reader S N hd A HN hfit
  let R1:=FormulaSignSlotRadialRadiusTarskiFamily.endpointLiftReader N S.width
    (IntegralPolynomialRadiusReader.polynomial S N hd) R0 HN A.width S.degree
    (IntegralPolynomialRadiusReader.coefficient_degree S N hd) hfit original FormulaSignSlotRadialRadiusTarskiFamily.original_FP
  exact FixedWidthBivariateReboxBits.reader (arity N) (S.width∘original) (width S) (head S N hd) R1
    (arity_unary N HN) (A.width.comp FormulaSignSlotRadialRadiusTarskiFamily.original_FP) (width_unary S A)
    (fun c i=>(head_coefficient_degree S N hd c i).trans_lt (hfit (original c))) (inputBound S)
    (head_coefficient_degree S N hd) (head_fit S)

noncomputable def sparseWindowReader:CertifiedPolynomial.BivariateReader
    (fun _=>Polynomial.monomial 1 (Polynomial.X:ℤ[X])-Polynomial.monomial 2 1):=by
  have HE:FixedWidthBivariateReader.polynomial FormulaSignSlotRadialRadiusTarskiFamily.arity
      FormulaSignSlotRadialRadiusTarskiFamily.width FormulaSignSlotRadialRadiusTarskiFamily.window=
      (fun _=>Polynomial.monomial 1 (Polynomial.X:ℤ[X])-Polynomial.monomial 2 1):=
    funext FormulaSignSlotRadialRadiusTarskiFamily.encoded_window
  exact HE ▸ FormulaSignSlotRadialRadiusTarskiFamily.windowReader

noncomputable def queryReader (S:Source) (N:List Bool→ℕ):CertifiedPolynomial.BivariateReader
    (FixedWidthBivariateReader.polynomial (arity N) (width S) (query N)):=by
  have HE:FixedWidthBivariateReader.polynomial (arity N) (width S) (window N)=
      (fun _=>Polynomial.monomial 1 (Polynomial.X:ℤ[X])-Polynomial.monomial 2 1):=by
    funext c
    simp only [FixedWidthBivariateReader.polynomial,window,Polynomial.map_mul,Polynomial.map_sub,
      Polynomial.map_X,Polynomial.map_C,FixedWidthKronecker.encode,MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_X,Fin.val_zero,Nat.zero_mul,pow_zero,pow_one]
    simp only [←Polynomial.C_mul_X_pow_eq_monomial,pow_one,Polynomial.C_1]
    ring
  let R:CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (arity N) (width S) (window N)):=
    HE.symm ▸ sparseWindowReader
  let e:List Bool→Fin 3:=fun c=>⟨moment c,by have H:moment c ≤ 2:=FormulaSignSlotRadialRadiusTarskiFamily.moment_le c;omega⟩
  exact FixedWidthBivariateTernaryPowerBits.reader (arity N) (width S) (window N) R e
    FormulaSignSlotRadialRadiusTarskiFamily.moment_binary

noncomputable def access (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1)
    (A:IntegralFramedBankPolynomialModel.Access S) (HN:UnaryFn N) (hfit:∀c,S.degree c < 2^S.width c):
    FixedWidthTarskiPrincipalBits.Access (family S N hd) where
  head:=headReader S N hd A HN hfit
  query:=queryReader S N
  degree:=degree_binary S A
  bound:=bound_binary S A
  seedDegree:=seedDegree_binary S A

end LeanCanny.Encoding.IntegralPolynomialWindowTarski
