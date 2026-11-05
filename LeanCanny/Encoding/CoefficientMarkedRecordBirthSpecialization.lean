/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoefficientMarkedRecordNative

/-! # Actual marked-record births preserve the constructed parent invariants

Source fields and degree transport are derived from the original radius
family. Physical rows and scalar slots accompany the actual quotient map.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordBirthSpecialization
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  (ctx : List Bool) (radius : List Bool → ℕ) {S m : ℕ} {ι : Type} [Fintype ι]

noncomputable def criticalPrefix
    (F : CoefficientHistoryPrefix.Prefix ℤ[X] S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι)
    (code : List Bool) :=
  CoefficientHistoryPrefix.criticalStep F
    (CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx)
    (CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx)
    (CoefficientMarkedRecordPrefix.source (n := n) (t := t) ctx 0).degree
    (IntegralMixedCausalUnitRecordBits.physical (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx + 3) m code)

theorem critical_specializes
    (F : CoefficientHistoryPrefix.Prefix ℤ[X] S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι)
    (x : State (CoefficientMarkedRecordNative.source (n := n) (t := t) ctx radius)
      S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι) (hm : m ≤ S)
    (ψ : F.carrier →+* x.sampler.scalarPrefix.carrier)
    (HB : CoefficientHeightBank.Specializes (evalRingHom ((2 : ℤ) ^ radius ctx)) ψ F.bank
      (CoefficientHeightBank.ofState x))
    (Hb : CoefficientCoordinateBasis.Specializes (evalRingHom ((2 : ℤ) ^ radius ctx)) ψ F.basis
      (CoefficientCoordinateBasis.ofIntegral x.sampler.scalarPrefix.basis))
    (HQ : ∀ j, MvPolynomial.map (evalRingHom ((2 : ℤ) ^ radius ctx)) (F.rows j) = x.sampler.rows j)
    (HS : F.scalar = x.sampler.scalar) (code : List Bool) :
    let F' := criticalPrefix hn ht ha ctx F code
    let x' := criticalStep x hm (IntegralMixedCausalUnitRecordBits.physical
      (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx + 3) m code)
    ∃ φ : F'.carrier →+* x'.sampler.scalarPrefix.carrier,
      CoefficientCoordinateBasis.Specializes (evalRingHom ((2 : ℤ) ^ radius ctx)) φ F'.basis
        (CoefficientCoordinateBasis.ofIntegral x'.sampler.scalarPrefix.basis) ∧
      CoefficientHeightBank.Specializes (evalRingHom ((2 : ℤ) ^ radius ctx)) φ F'.bank
        (CoefficientHeightBank.ofState x') ∧
      (∀ j, MvPolynomial.map (evalRingHom ((2 : ℤ) ^ radius ctx)) (F'.rows j) = x'.sampler.rows j) ∧
      F'.scalar = x'.sampler.scalar := by
  dsimp only [criticalPrefix]
  rw [CoefficientMarkedRecordNative.source_degree (n := n) (t := t) ctx radius]
  let low := CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx
  let leading := CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx
  let r := IntegralMixedCausalUnitRecordBits.physical (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx + 3) m code
  have hf := CoefficientMarkedRecordNative.source_fields (n := n) (t := t) ctx radius
  refine ⟨CoefficientMixedCriticalBirth.specialize F.bank low leading x hm r
    (evalRingHom ((2 : ℤ) ^ radius ctx)) ψ HB hf.1 hf.2, ?_, ?_, ?_, ?_⟩
  · exact CoefficientMixedCriticalBirth.basis_specializes F.bank F.basis low leading x hm r
      (evalRingHom ((2 : ℤ) ^ radius ctx)) ψ HB Hb hf.1 hf.2
  · exact CoefficientMixedCriticalBirth.bank_specializes F.bank low leading x hm r
      (evalRingHom ((2 : ℤ) ^ radius ctx)) ψ HB hf.1 hf.2
  · have hr := CoefficientMixedCriticalBirth.rows_map_native F.bank F.basis low leading x hm r
      (evalRingHom ((2 : ℤ) ^ radius ctx)) ψ HB Hb hf.1 hf.2 F.rows HQ
    change ∀ j, MvPolynomial.map (evalRingHom ((2 : ℤ) ^ radius ctx))
      (CoefficientMixedCriticalBirth.rows (cap := S) F.bank F.basis low leading r F.rows F.scalar _ j) = _
    rw [HS]
    exact congrFun hr
  · change (Fin.cons (Sum.inr ()) (fun j => Sum.inl (Sum.inl (F.scalar j))) :
        Fin (m + 1) → (ι ⊕ FlatAffineCriticalStage.Variables
          (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx + 3 + 1)) ⊕ Unit) =
      (Fin.cons (Sum.inr ()) (fun j => Sum.inl (Sum.inl (x.sampler.scalar j))) :
        Fin (m + 1) → (ι ⊕ FlatAffineCriticalStage.Variables
          (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx + 3 + 1)) ⊕ Unit)
    rw [HS]

theorem cut_transport (birth : ℕ) (code : List Bool) :
    CoefficientMixedCutSourceDegree.cut
      (CoefficientMarkedRecordNative.source_degree (n := n) (t := t) ctx radius)
      (CoefficientMarkedRecordPrefix.cut hn ht ha ctx birth code) =
        CoefficientMarkedRecordNative.cut hn ht ha ctx radius birth code := by
  exact CoefficientMixedCutSourceDegree.cut_of_code
    (CoefficientMarkedRecordNative.source_degree (n := n) (t := t) ctx radius)
    (by change 0 < IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx + 3; omega)
    birth code (CoefficientMarkedRecordPrefix.source_cap hn ht ha ctx)
    (CoefficientMarkedRecordNative.source_cap hn ht ha ctx radius)

noncomputable def cutPrefix
    (F : CoefficientHistoryPrefix.Prefix ℤ[X] S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι)
    (code : List Bool) :=
  let c := CoefficientMarkedRecordPrefix.cut hn ht ha ctx m code
  let τ := CoefficientMarkedRecordPrefix.cutIndex hn ht ha ctx F.bank F.basis m code
  CoefficientHistoryPrefix.scalarStep F
    (CoefficientMixedCutSpecialization.polynomial F.basis F.bank
      (CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx)
      (CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx)
      (c.rule 1 one_ne_zero) c.current (c.kind 1 one_ne_zero) c.degree τ) c.degree
    (CoefficientMixedCutSpecialization.leading F.basis F.bank
      (CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx)
      (CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx)
      (c.rule 1 one_ne_zero) c.current (c.kind 1 one_ne_zero) c.degree τ)

noncomputable def nativeCut
    (x : State (CoefficientMarkedRecordNative.source (n := n) (t := t) ctx radius)
      S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι) (hm : m ≤ S) (code : List Bool) :=
  let c := CoefficientMarkedRecordPrefix.cut hn ht ha ctx m code
  CoefficientMixedCutSpecialization.nativeStep x hm (c.rule 1 one_ne_zero) c.current
    (CoefficientMixedCutSourceDegree.kind
      (CoefficientMarkedRecordNative.source_degree (n := n) (t := t) ctx radius)
      (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero)) c.degree

private theorem command_step_heq {ambient width : ℕ} {P : SpatialSource ambient}
    {cap birth : ℕ} {I : Type} [Fintype I] (x : State P cap width birth I) (hm : birth ≤ cap)
    {a b : IntegralMixedFullHistoryScript.Command P width} (h : a = b) :
    HEq (IntegralMixedFullHistoryScript.step x hm a) (IntegralMixedFullHistoryScript.step x hm b) := by
  cases h
  rfl

private theorem retarget_step_heq {ambient width cap birth : ℕ}
    {P Q : SpatialSource ambient} {I : Type} [Fintype I]
    (x : State Q cap width birth I) (hm : birth ≤ cap) (hd : P.degree = Q.degree)
    (c : IntegralMixedCausalRecordBits.Cut P width) :
    HEq (CoefficientMixedCutSpecialization.nativeStep x hm (c.rule 1 one_ne_zero) c.current
      (CoefficientMixedCutSourceDegree.kind hd (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero)) c.degree)
      (IntegralMixedFullHistoryScript.step x hm
        ((IntegralMixedCausalRecordBits.Template.cut (CoefficientMixedCutSourceDegree.cut hd c)).command
          (commonDenominator x) (commonDenominator_ne_zero x))) := by
  have he := CoefficientMixedCutSourceDegree.native_command x (CoefficientMixedCutSourceDegree.cut hd c)
  rw [← CoefficientMixedCutSourceDegree.cut_kind hd c 1 one_ne_zero] at he
  exact command_step_heq x hm he

theorem nativeCut_command
    (x : State (CoefficientMarkedRecordNative.source (n := n) (t := t) ctx radius)
      S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι) (hm : m ≤ S) (code : List Bool) :
    HEq (nativeCut hn ht ha ctx radius x hm code)
      (IntegralMixedFullHistoryScript.step x hm
        ((IntegralMixedCausalRecordBits.Template.cut
          (CoefficientMarkedRecordNative.cut hn ht ha ctx radius m code)).command
          (commonDenominator x) (commonDenominator_ne_zero x))) := by
  rw [← cut_transport hn ht ha ctx radius m code]
  exact retarget_step_heq x hm
    (CoefficientMarkedRecordNative.source_degree (n := n) (t := t) ctx radius)
    (CoefficientMarkedRecordPrefix.cut hn ht ha ctx m code)

theorem critical_next_heq
    (x : State (CoefficientMarkedRecordNative.source (n := n) (t := t) ctx radius)
      S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι) (hm : m ≤ S) (code : List Bool)
    (hc : IntegralMixedUnitRecordCode.critical code = true) :
    HEq (criticalStep x hm (IntegralMixedCausalUnitRecordBits.physical
      (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx + 3) m code))
      (CoefficientMarkedRecordNative.next hn ht ha ctx radius x hm code) := by
  have he : (CoefficientMarkedRecordNative.instruction hn ht ha ctx radius x code).command =
      .critical (IntegralMixedCausalUnitRecordBits.physical
        (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx + 3) m code) := by
    simp only [CoefficientMarkedRecordNative.instruction, IntegralMixedCausalRecordBits.instantiate,
      IntegralMixedCausalUnitRecordBits.record, hc, ite_true, IntegralMixedCausalRecordBits.Template.command]
    rfl
  exact ((CoefficientMarkedRecordNative.next_command hn ht ha ctx radius x hm code).trans
    (command_step_heq x hm he)).symm

theorem cut_next_heq
    (x : State (CoefficientMarkedRecordNative.source (n := n) (t := t) ctx radius)
      S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι) (hm : m ≤ S) (code : List Bool)
    (hc : IntegralMixedUnitRecordCode.critical code ≠ true) :
    HEq (nativeCut hn ht ha ctx radius x hm code)
      (CoefficientMarkedRecordNative.next hn ht ha ctx radius x hm code) := by
  have he : (CoefficientMarkedRecordNative.instruction hn ht ha ctx radius x code).command =
      (IntegralMixedCausalRecordBits.Template.cut
        (CoefficientMarkedRecordNative.cut hn ht ha ctx radius m code)).command
        (commonDenominator x) (commonDenominator_ne_zero x) := by
    simp only [CoefficientMarkedRecordNative.instruction, IntegralMixedCausalRecordBits.instantiate,
      IntegralMixedCausalUnitRecordBits.record, hc]
    rfl
  exact (nativeCut_command hn ht ha ctx radius x hm code).trans
    ((CoefficientMarkedRecordNative.next_command hn ht ha ctx radius x hm code).trans
      (command_step_heq x hm he)).symm

private theorem retarget_cut_specializes {ambient width cap birth : ℕ}
    {P Q : SpatialSource ambient} {I : Type} [Fintype I]
    (F : CoefficientHistoryPrefix.Prefix ℤ[X] cap width birth I)
    (low : MvPolynomial (Fin (ambient + 1)) ℤ[X]) (a : ℤ[X])
    (hd : P.degree = Q.degree) (r : IntegralMixedCriticalSweep.Rule ambient) (current : Bool)
    (c : IntegralMixedRelativeCuts.Kind P r) (d radius entryBits : ℕ)
    (x : State Q cap width birth I) (hm : birth ≤ cap)
    (ψ : F.carrier →+* x.sampler.scalarPrefix.carrier)
    (HB : CoefficientHeightBank.Specializes (evalRingHom ((2 : ℤ) ^ radius)) ψ F.bank
      (CoefficientHeightBank.ofState x))
    (Hb : CoefficientCoordinateBasis.Specializes (evalRingHom ((2 : ℤ) ^ radius)) ψ F.basis
      (CoefficientCoordinateBasis.ofIntegral x.sampler.scalarPrefix.basis))
    (HL : low.map (evalRingHom ((2 : ℤ) ^ radius)) = Q.low)
    (HA : a.eval ((2 : ℤ) ^ radius) = Q.leading)
    (HQ : ∀ j, MvPolynomial.map (evalRingHom ((2 : ℤ) ^ radius)) (F.rows j) = x.sampler.rows j)
    (HS : F.scalar = x.sampler.scalar)
    (HE : ∀ i j, coefficientMass (Algebra.leftMulMatrix F.basis.basis
      ((CoefficientMixedCutSpecialization.raw F.bank low a r current c d).coeff d) i j) ≤ 2 ^ entryBits)
    (HR : ParameterMatrixMassBounds.characteristicBudget ((2 ^ width) ^ birth) entryBits + 1 ≤ radius) :
    let τ := CoefficientMixedCutAtInfinity.formalIndex F.basis F.bank low a r current c d
    let F' := CoefficientHistoryPrefix.scalarStep F
      (CoefficientMixedCutSpecialization.polynomial F.basis F.bank low a r current c d τ) d
      (CoefficientMixedCutSpecialization.leading F.basis F.bank low a r current c d τ)
    let x' := CoefficientMixedCutSpecialization.nativeStep x hm r current
      (CoefficientMixedCutSourceDegree.kind hd r c) d
    ∃ φ : F'.carrier →+* x'.sampler.scalarPrefix.carrier,
      CoefficientCoordinateBasis.Specializes (evalRingHom ((2 : ℤ) ^ radius)) φ F'.basis
        (CoefficientCoordinateBasis.ofIntegral x'.sampler.scalarPrefix.basis) ∧
      CoefficientHeightBank.Specializes (evalRingHom ((2 : ℤ) ^ radius)) φ F'.bank
        (CoefficientHeightBank.ofState x') ∧
      (∀ j, MvPolynomial.map (evalRingHom ((2 : ℤ) ^ radius)) (F'.rows j) = x'.sampler.rows j) ∧
      F'.scalar = x'.sampler.scalar := by
  let cq := CoefficientMixedCutSourceDegree.kind hd r c
  have hraw := CoefficientMixedCutSourceDegree.raw_eq hd F.bank low a r current c d
  have hτ : CoefficientMixedCutAtInfinity.formalIndex F.basis F.bank low a r current cq d =
      CoefficientMixedCutAtInfinity.formalIndex F.basis F.bank low a r current c d := by
    unfold CoefficientMixedCutAtInfinity.formalIndex
    rw [hraw]
  dsimp only
  rw [← CoefficientMixedCutSourceDegree.polynomial_eq hd F.basis F.bank low a r current c d,
    ← CoefficientMixedCutSourceDegree.leading_eq hd F.basis F.bank low a r current c d, ← hτ]
  have hE : ∀ i j, coefficientMass (Algebra.leftMulMatrix F.basis.basis
      ((CoefficientMixedCutSpecialization.raw F.bank low a r current cq d).coeff d) i j) ≤ 2 ^ entryBits := by
    rw [hraw]
    exact HE
  have hg := CoefficientMixedCutAtInfinity.guards_after_radius F.basis F.bank low a r current cq d
    entryBits radius hE HR
  refine ⟨CoefficientMixedCutAtInfinity.specialize F.bank F.basis low a x hm r current cq d radius entryBits
    ψ HB Hb HL HA hE HR, ?_, ?_, ?_, ?_⟩
  · exact CoefficientMixedCutAtInfinity.basis_specializes F.bank F.basis low a x hm r current cq d radius entryBits
      ψ HB Hb HL HA hE HR
  · exact CoefficientMixedCutAtInfinity.bank_specializes F.bank F.basis low a x hm r current cq d radius entryBits
      ψ HB Hb HL HA hE HR
  · have hp := CoefficientMixedCutSpecialization.polynomial_map_native F.bank F.basis low a x hm r current cq d
      (CoefficientMixedCutAtInfinity.formalIndex F.basis F.bank low a r current cq d)
      (evalRingHom ((2 : ℤ) ^ radius)) ψ HB Hb HL HA hg.1 hg.2
    change ∀ j, MvPolynomial.map (evalRingHom ((2 : ℤ) ^ radius))
      (CoefficientCanonicalScalarAppend.rows cap F.rows F.scalar F.basis _ d j) = _
    rw [HS]
    have hh := CoefficientCanonicalScalarAppend.newrows_map Hb cap F.rows x.sampler.rows HQ
      x.sampler.scalar
      (CoefficientMixedCutSpecialization.polynomial F.basis F.bank low a r current cq d
        (CoefficientMixedCutAtInfinity.formalIndex F.basis F.bank low a r current cq d)) d
    rw [hp] at hh
    exact congrFun hh
  · change (Fin.cons (Sum.inr ()) (fun j => Sum.inl (F.scalar j)) : Fin (birth + 1) → I ⊕ Unit) =
      (Fin.cons (Sum.inr ()) (fun j => Sum.inl (x.sampler.scalar j)) : Fin (birth + 1) → I ⊕ Unit)
    rw [HS]

theorem cut_specializes
    (F : CoefficientHistoryPrefix.Prefix ℤ[X] S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι)
    (x : State (CoefficientMarkedRecordNative.source (n := n) (t := t) ctx radius)
      S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι) (hm : m ≤ S)
    (ψ : F.carrier →+* x.sampler.scalarPrefix.carrier)
    (HB : CoefficientHeightBank.Specializes (evalRingHom ((2 : ℤ) ^ radius ctx)) ψ F.bank
      (CoefficientHeightBank.ofState x))
    (Hb : CoefficientCoordinateBasis.Specializes (evalRingHom ((2 : ℤ) ^ radius ctx)) ψ F.basis
      (CoefficientCoordinateBasis.ofIntegral x.sampler.scalarPrefix.basis))
    (HQ : ∀ j, MvPolynomial.map (evalRingHom ((2 : ℤ) ^ radius ctx)) (F.rows j) = x.sampler.rows j)
    (HS : F.scalar = x.sampler.scalar) (code : List Bool) (entryBits : ℕ)
    (HE : let c := CoefficientMarkedRecordPrefix.cut hn ht ha ctx m code
      ∀ i j, coefficientMass (Algebra.leftMulMatrix F.basis.basis
        ((CoefficientMixedCutSpecialization.raw F.bank
          (CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx)
          (CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx)
          (c.rule 1 one_ne_zero) c.current (c.kind 1 one_ne_zero) c.degree).coeff c.degree) i j) ≤ 2 ^ entryBits)
    (HR : ParameterMatrixMassBounds.characteristicBudget
      ((2 ^ CoefficientMarkedIntegerBirth.width hn ht ha ctx) ^ m) entryBits + 1 ≤ radius ctx) :
    let F' := cutPrefix hn ht ha ctx F code
    let x' := nativeCut hn ht ha ctx radius x hm code
    ∃ φ : F'.carrier →+* x'.sampler.scalarPrefix.carrier,
      CoefficientCoordinateBasis.Specializes (evalRingHom ((2 : ℤ) ^ radius ctx)) φ F'.basis
        (CoefficientCoordinateBasis.ofIntegral x'.sampler.scalarPrefix.basis) ∧
      CoefficientHeightBank.Specializes (evalRingHom ((2 : ℤ) ^ radius ctx)) φ F'.bank
        (CoefficientHeightBank.ofState x') ∧
      (∀ j, MvPolynomial.map (evalRingHom ((2 : ℤ) ^ radius ctx)) (F'.rows j) = x'.sampler.rows j) ∧
      F'.scalar = x'.sampler.scalar := by
  let c := CoefficientMarkedRecordPrefix.cut hn ht ha ctx m code
  have hf := CoefficientMarkedRecordNative.source_fields (n := n) (t := t) ctx radius
  exact retarget_cut_specializes F
    (CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx)
    (CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx)
    (CoefficientMarkedRecordNative.source_degree (n := n) (t := t) ctx radius)
    (c.rule 1 one_ne_zero) c.current (c.kind 1 one_ne_zero) c.degree (radius ctx) entryBits
    x hm ψ HB Hb hf.1 hf.2 HQ HS HE HR

end LeanCanny.Encoding.CoefficientMarkedRecordBirthSpecialization
