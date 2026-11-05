/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialExternalSlackRoots
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerPlan
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerVectorPoint
/-! # One external marked lift realizes the actual n+8 integer leaves -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerRealization
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.ETR
open FormulaSignSlotRadialExternalContext
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def vector (m R L B K : ℕ) (x : ℕ→ℝ) (u v : ℝ) (i : ℕ) : ℝ :=
  if i<m then x i else if i=m then u else if i=m+2 then v
  else if i=m+4 then (2:ℝ)^R else if i=m+5 then (2:ℝ)^L
  else if i=m+6 then (2:ℝ)^B else if i=m+7 then (2:ℝ)^K else 0

noncomputable def values (ctx : List Bool) (x : ℕ→ℝ) (u v : ℝ) := vector (number ctx)
  (FormulaSignSlotRadialExternalPrelude.radius ctx)
  (FormulaSignSlotRadialExternalSlackSource.Lam (FormulaSignSlotRadialExternalSlackSource.key ctx))
  (FormulaSignSlotRadialExternalSlackSource.beta (FormulaSignSlotRadialExternalSlackSource.key ctx))
  (FormulaSignSlotRadialExternalSlackSource.K (FormulaSignSlotRadialExternalSlackSource.key ctx)) x u v

private theorem positive_power_root (E : ℕ) :
    (PowerIntegerPolynomial.polynomial False E).eval₂ (Int.castRingHom ℝ) ((2:ℝ)^E)=0 := by
  rw [PowerIntegerPolynomial.root_iff]
  simp only [PowerIntegerPolynomial.value,ite_false,Int.cast_pow,Int.cast_ofNat]

theorem roots (ctx : List Bool) (hExt : external ctx)
    (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid ctx) (u v : ℝ)
    (hu : (FormulaSignSlotRadialExternalSlackSource.sphereSource.polynomial (FormulaSignSlotRadialExternalSlackSource.key ctx)).eval₂
      (Int.castRingHom ℝ) u=0)
    (hv : (FormulaSignSlotRadialExternalSlackSource.regularSource.polynomial (FormulaSignSlotRadialExternalSlackSource.key ctx)).eval₂
      (Int.castRingHom ℝ) v=0) (i : ℕ) :
    (FormulaSignSlotRadialProviderIntegerSource.source.polynomial (pair ctx (BinaryNatCode.encode i))).eval₂
      (Int.castRingHom ℝ) (values ctx (FormulaSignSlotRadialExternalCoordinates.point ctx hw) u v i)=0 := by
  rw [FormulaSignSlotRadialProviderIntegerSource.polynomial_external _
    (by simpa only [pairFst_pair] using hExt),FormulaSignSlotRadialProviderIntegerSource.external_polynomial]
  simp only [FormulaSignSlotRadialProviderIntegerSource.tag,FormulaSignSlotRadialProviderIntegerSource.saved,
    pairSnd_pair,pairFst_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    FormulaSignSlotRadialProviderIntegerSource.power,PowerIntegerPolynomial.source,Function.comp_apply,values,vector]
  split_ifs with hi hs hr hR hL hB hK
  · have HX := FormulaSignSlotRadialExternalCoordinates.roots ctx hw i
    simpa only [FormulaSignSlotRadialExternalCoordinates.values,ite_eq_left hi,BinaryNatCode.encode] using HX
  · exact hu
  · exact hv
  · exact positive_power_root _
  · exact positive_power_root _
  · exact positive_power_root _
  · exact positive_power_root _
  · simp only [Polynomial.eval₂_X]

private theorem vector_markedLift (m R L B K r : ℕ)
    (q : MvPolynomial (Fin m) ℤ) (D b : ℕ)
    (a : BoundedZeroSource.Bounded q r) (x : ℕ→ℝ)
    (hx : ∀i,∀hi : i<m,x i=(a).val ⟨i,hi⟩) :
    (fun i : Fin (m+4)=>vector m R L B K x
      (BoundedRegularSource.sphereSlack q r a)
      (BoundedRegularSource.regularSlack q D b r a).re i.val)=
      (BoundedRegularSource.markedLift q D b r a).val.val := by
  let U := BoundedRegularSource.sphereSlack q r a
  let V := (BoundedRegularSource.regularSlack q D b r a).re
  funext i
  change vector m R L B K x U V i.val=(BoundedRegularSource.lift q D b r a).val i
  rw [BoundedRegularSource.lift_coordinates]
  refine Fin.addCases (fun j : Fin (m)=>?_) (fun z : Fin 4=>?_) i
  · change vector m R L B K x U V j.val=
      (Fin.append (Fin.append (a).val ![U,0]) ![V,0]) ((j.castAdd 2).castAdd 2)
    rw [Fin.append_left,Fin.append_left]
    simp only [vector,ite_eq_left j.isLt]
    exact hx j.val j.isLt
  · fin_cases z
    · change vector m R L B K x U V (m)=
        (Fin.append (Fin.append (a).val ![U,0]) ![V,0]) ((Fin.natAdd (m) (0 : Fin 2)).castAdd 2)
      rw [Fin.append_left,Fin.append_right]
      simp only [Matrix.cons_val_zero]
      unfold vector
      split_ifs <;> first | rfl | omega
    · change vector m R L B K x U V (m+1)=
        (Fin.append (Fin.append (a).val ![U,0]) ![V,0]) ((Fin.natAdd (m) (1 : Fin 2)).castAdd 2)
      rw [Fin.append_left,Fin.append_right]
      simp only [Matrix.cons_val_one]
      unfold vector
      split_ifs <;> first | rfl | omega
    · change vector m R L B K x U V (m+2)=
        (Fin.append (Fin.append (a).val ![U,0]) ![V,0]) (Fin.natAdd (m+2) (0 : Fin 2))
      rw [Fin.append_right]
      simp only [Matrix.cons_val_zero]
      unfold vector
      split_ifs <;> first | rfl | omega
    · change vector m R L B K x U V (m+3)=
        (Fin.append (Fin.append (a).val ![U,0]) ![V,0]) (Fin.natAdd (m+2) (1 : Fin 2))
      rw [Fin.append_right]
      simp only [Matrix.cons_val_one]
      unfold vector
      split_ifs <;> first | rfl | omega

theorem values_markedLift (ctx : List Bool) (m : ℕ) (hm : number ctx=m)
    (q : MvPolynomial (Fin m) ℤ) (D b : ℕ)
    (a : BoundedZeroSource.Bounded q (FormulaSignSlotRadialExternalPrelude.radius ctx)) (x : ℕ→ℝ)
    (hx : ∀i,∀hi : i<m,x i=a.val ⟨i,hi⟩) :
    (fun i : Fin (m+4)=>values ctx x
      (BoundedRegularSource.sphereSlack q (FormulaSignSlotRadialExternalPrelude.radius ctx) a)
      (BoundedRegularSource.regularSlack q D b (FormulaSignSlotRadialExternalPrelude.radius ctx) a).re i.val)=
      (BoundedRegularSource.markedLift q D b (FormulaSignSlotRadialExternalPrelude.radius ctx) a).val.val := by
  unfold values
  rw [hm]
  exact vector_markedLift m _ _ _ _ _ q D b a x hx

section Actual
variable (H : List Bool) (k : ℕ) (Gamma label : List Bool) (side : Bool) (w : List Bool)
local notation "ctx" => packet H k Gamma label side w
local notation "m" => CanonicalAuxiliaryCandidateCover.dimension (FormulaSignSlotRadialJointLayout.source side H)
local notation "q" => AuxiliaryCandidateRegularLift.original CanonicalAuxiliaryCandidateCover.dimension
  CanonicalAuxiliaryCandidateCover.equation (FormulaSignSlotRadialJointLayout.source side H)
local notation "r" => FormulaSignSlotRadialExternalPrelude.radius ctx
local notation "E" => AuxiliaryCandidateRegularLift.allowance CanonicalAuxiliaryCandidateCover.equation
  (FormulaSignSlotRadialJointLayout.source side H)

attribute [local irreducible] Term.finitePolynomial CanonicalAuxiliaryCandidateCover.equation
  AuxiliaryCandidateRegularLift.original

theorem exists_external_values
    (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid ctx)
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈
      FormulaSignSlotRadialJointStratumSampler.language) :
    ∃ a : BoundedZeroSource.Bounded q r, ∃ v : ℕ→ℝ,
      (∀i,(FormulaSignSlotRadialProviderIntegerSource.source.polynomial (pair ctx (BinaryNatCode.encode i))).eval₂
        (Int.castRingHom ℝ) (v i)=0) ∧
      (fun i : Fin (m+4)=>v i.val)=(BoundedRegularSource.markedLift q E E r a).val.val ∧
      ∀i : Fin m,a.val i=FormulaSignSlotRadialExternalCoordinates.point ctx hw i.val := by
  obtain ⟨a,hA,hU,hV⟩ := FormulaSignSlotRadialExternalSlackRoots.exists_roots H k Gamma label side w hw hq
  let v := values ctx (FormulaSignSlotRadialExternalCoordinates.point ctx hw)
    (BoundedRegularSource.sphereSlack q r a) (BoundedRegularSource.regularSlack q E E r a).re
  refine ⟨a,v,fun i => roots ctx (external_packet H k Gamma label side w) hw _ _ hU hV i,?_,hA⟩
  have HN := number_packet H k Gamma label side w
  dsimp only [FormulaSignSlotRadialJointLayout.circleCount] at HN
  exact values_markedLift ctx m HN q E E a
    (FormulaSignSlotRadialExternalCoordinates.point ctx hw) (fun i hi => (hA ⟨i,hi⟩).symm)

end Actual
end LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerRealization
