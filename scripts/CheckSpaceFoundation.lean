import LeanCanny
import Lean.Util.FoldConsts

open Turing.MultiTapeTM

/-! Check the public endpoints against the native class and accept an arbitrary
native space-bounded child, with no legacy evaluator or execution clock. -/

example : LeanCanny.PSPACE = Cslib.Complexity.PSPACE encBits := rfl

example : LeanCanny.P = Cslib.Complexity.P encBits := rfl

example {L K : Set (List Bool)} : LeanCanny.PolyTimeReduces L K ↔
    Cslib.Complexity.PolyTimeReducible encBits encBits L K := Iff.rfl

example {L K : Set (List Bool)} {f : List Bool → List Bool}
    (hf : ComputableTidilyInPolyTime f encBits encBits)
    (hcorrect : ∀ x, x ∈ L ↔ f x ∈ K) (hK : K ∈ LeanCanny.ExistsReal) :
    L ∈ LeanCanny.ExistsReal :=
  LeanCanny.existsReal_of_reduction ⟨f, hf, hcorrect⟩ hK

example : LeanCanny.ExistsReal ⊆ Cslib.Complexity.PSPACE encBits ↔
    LeanCanny.ETR.language ∈ Cslib.Complexity.PSPACE encBits :=
  LeanCanny.existsReal_subset_PSPACE_iff

/-! A single native machine handles input-dependent recursion depth. Neither
the local instruction computation nor the reply installer needs an FP clock. -/
example {localStep : List Bool → LeanCanny.Computation.RecursiveStack.Action (List Bool)}
    {receive : List Bool × List Bool → List Bool} {value : List Bool → List Bool}
    {rank fuel : List Bool → ℕ} {valid : List Bool → List Bool → Prop}
    {N R B : List Bool → ℕ}
    (hl : ComputableTidilyInPolySpace localStep encBits
      (LeanCanny.Computation.RecursiveStack.encAction encBits))
    (hr : ComputableTidilyInPolySpace receive (encPair encBits encBits) encBits)
    (hN : ComputableTidilyInPolyTime N encBits encNat)
    (hR : ComputableTidilyInPolyTime R encBits encUnary)
    (hB : PolyBounded List.length B)
    (rules : ∀ x, LeanCanny.Computation.RecursiveStack.Rules localStep receive value rank fuel (valid x) (N x))
    (hstart : ∀ x, valid x x)
    (hrank : ∀ x p, valid x p → rank p ≤ R x)
    (hframe : ∀ x p, valid x p → p.length ≤ B x)
    (hvalue : ∀ x p, valid x p → (value p).length ≤ B x) :
    ComputableTidilyInPolySpace value encBits encBits :=
  LeanCanny.Computation.RecursiveStack.evaluator hl hr ComputableTidilyInPolySpace.id'
    hN hR hB rules hstart hrank hframe hvalue

/-! Recursive entries receive no answer certificate; native base computations
and a uniformly bounded ranked task graph suffice. -/
example (S : LeanCanny.Algebra.RecursiveMatrixPower.Source) (h : S.Controls)
    (rank : List Bool → ℕ) (tasks : List Bool → List Bool → Prop)
    (R K M : List Bool → ℕ) (hR : LeanCanny.UnaryFn R)
    (hK : LeanCanny.UnaryFn K) (hM : LeanCanny.UnaryFn M)
    (hroot : ∀ q, tasks q q)
    (hrank : ∀ root q, tasks root q → rank q ≤ R root)
    (htask : ∀ root q, tasks root q → q.length ≤ K root)
    (hbase : ∀ root q, tasks root q → (S.base q).length ≤ K root)
    (hbits : ∀ root q, tasks root q →
      (S.family.dimension q).size + (S.family.exponent q).size + (S.family.modulus q).size ≤ M root)
    (hgraph : ∀ root q, tasks root q → S.leaf q = false → ∀ i j : Fin (S.family.dimension q),
      tasks root (S.entryTask (LeanCanny.pair q (LeanCanny.pair
        (LeanCanny.BinaryNatCode.encode i.val) (LeanCanny.BinaryNatCode.encode j.val)))) ∧
      rank (S.entryTask (LeanCanny.pair q (LeanCanny.pair
        (LeanCanny.BinaryNatCode.encode i.val) (LeanCanny.BinaryNatCode.encode j.val)))) < rank q) :
    ComputableTidilyInPolySpace S.answer encBits encBits :=
  (S.evaluator h rank tasks R K M hR hK hM hroot hrank htask hbase hbits hgraph).computable

/-! Determinant and factor stages expose task calls. Their local certificates
need FP query writers, with no certificate for factor, diagonal, or moment answers. -/
example {F : LeanCanny.Algebra.BerkowitzPolynomial.ModularFamily}
    (a : LeanCanny.Algebra.BerkowitzPolynomial.ModularAccess F) (ha : a.ControlsPolyTime)
    (factorTask : List Bool → List Bool) (hf : factorTask ∈ LeanCanny.FP) (zeroTask : List Bool) :
    (LeanCanny.Algebra.BerkowitzPolynomial.DeterminantStage.controller a factorTask zeroTask).Certificates
      (encQ := encBits) (encS := encBits) :=
  LeanCanny.Algebra.BerkowitzPolynomial.DeterminantStage.certificates a ha factorTask hf zeroTask

example {F : LeanCanny.Algebra.BerkowitzPolynomial.ModularFamily}
    (a : LeanCanny.Algebra.BerkowitzPolynomial.ModularAccess F) (ha : a.ControlsPolyTime)
    (diagonalTask momentTask : List Bool → List Bool)
    (hd : diagonalTask ∈ LeanCanny.FP) (hm : momentTask ∈ LeanCanny.FP) :
    (LeanCanny.Algebra.BerkowitzPolynomial.FactorStage.program a diagonalTask momentTask).controller.Certificates
      (encQ := encBits) (encS := LeanCanny.Computation.SingleCall.encState) :=
  LeanCanny.Algebra.BerkowitzPolynomial.FactorStage.certificates a ha diagonalTask momentTask hd hm

/-! The mixed-stage dispatcher accepts a source controller's local certificates,
without assuming a polynomial-space certificate for its coefficient answers. -/
example {F : LeanCanny.Algebra.BerkowitzPolynomial.ModularFamily}
    (a : LeanCanny.Algebra.BerkowitzPolynomial.ModularAccess F) (ha : a.ControlsPolyTime)
    {S : Type} [Inhabited S] {encS : S ↪ List Bool}
    (source : LeanCanny.Computation.RecursiveController.Controller (List Bool) S)
    (hs : source.Certificates (encQ := encBits) (encS := encS)) :
    (LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch.controller a source).Certificates
      (encQ := encBits) (encS := LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch.encState encS) :=
  LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch.certificates a ha source hs

example {F : LeanCanny.Algebra.BerkowitzPolynomial.ModularFamily}
    (a : LeanCanny.Algebra.BerkowitzPolynomial.ModularAccess F)
    (h : ComputableTidilyInPolySpace (LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch.answer a) encBits encBits) :
    F.zeroLanguage ∈ Cslib.Complexity.PSPACE encBits :=
  (LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch.determinant_decider a ⟨h⟩).mem_PSPACE

example {F : LeanCanny.Algebra.MatrixPower.ModularFamily}
    (a : LeanCanny.Algebra.MatrixPower.ModularAccess F) (ha : a.ControlsPolyTime)
    (he : ComputableTidilyInPolySpace a.entry encBits encBits) :
    ComputableTidilyInPolySpace F.value encBits encBits :=
  (LeanCanny.Algebra.MatrixPower.ModularAccess.evaluatorWithEntry a ha ⟨he⟩).computable

example {F : LeanCanny.Algebra.Berkowitz.ModularFamily}
    (a : LeanCanny.Algebra.Berkowitz.ModularAccess F) (ha : a.ControlsPolyTime)
    (he : ComputableTidilyInPolySpace a.access.entry encBits encBits) :
    F.zeroLanguage ∈ Cslib.Complexity.PSPACE encBits :=
  LeanCanny.Algebra.Berkowitz.ModularAccess.zeroLanguage_mem_PSPACE_of_evaluator a ha ⟨he⟩

example {F : LeanCanny.Algebra.CannySubresultantBits.Family}
    (a : LeanCanny.Algebra.CannySubresultantBits.Access F) (ha : a.ControlsPolyTime)
    (L : ComputableTidilyInPolySpace a.source.leftCoefficient encBits encBits)
    (R : ComputableTidilyInPolySpace a.source.rightCoefficient encBits encBits) :
    ComputableTidilyInPolySpace (LeanCanny.Algebra.CannyCoordinateBits.value F) encBits encBits :=
  (LeanCanny.Algebra.CannyCoordinateBits.evaluatorWithCoefficients a ha ⟨L⟩ ⟨R⟩).computable

example (S : LeanCanny.Algebra.PrimitivePairBits.Source)
    (A : LeanCanny.Algebra.PrimitivePairBits.Readers S) :
    ComputableTidilyInPolySpace (LeanCanny.Algebra.PrimitivePairBits.coefficient
      (fun c => LeanCanny.Algebra.PrimitivePair.leftNumerator (S.left c) (S.right c) (S.direction c))) encBits encBits :=
  (LeanCanny.Algebra.PrimitivePairBits.leftNumeratorEvaluator S A).computable

example (F : LeanCanny.Algebra.SeparableBits.Family)
    (A : LeanCanny.Algebra.SeparableBits.Readers F) (hne : ∀ c, F.polynomial c ≠ 0) :
    LeanCanny.Algebra.SeparableBits.language F ∈ Cslib.Complexity.PSPACE encBits :=
  (LeanCanny.Algebra.SeparableBits.decider F A hne).mem_PSPACE

example (F : LeanCanny.Algebra.SeparableBits.Family)
    (A : LeanCanny.Algebra.SeparableBits.Readers F) :
    ComputableTidilyInPolySpace (fun c => LeanCanny.BinaryNatCode.encode
      (LeanCanny.Algebra.SquarefreePart.common ((F.polynomial c).map (Int.castRingHom ℚ))).natDegree) encBits encBits :=
  (LeanCanny.Algebra.SeparableBits.gcdDegreeEvaluator F A).computable

example (F : LeanCanny.Algebra.SeparableBits.Family)
    (A : LeanCanny.Algebra.SeparableBits.Readers F) (hne : ∀ c, F.polynomial c ≠ 0) :
    ComputableTidilyInPolySpace (fun c => LeanCanny.BinaryNatCode.encode
      (LeanCanny.Algebra.SquarefreePart.part ((F.polynomial c).map (Int.castRingHom ℚ))).natDegree) encBits encBits :=
  (LeanCanny.Algebra.SeparableBits.squarefreeDegreeEvaluator F A hne).computable

example (F : LeanCanny.Algebra.SeparableBits.Family)
    (A : LeanCanny.Algebra.SeparableBits.Readers F) :
    ComputableTidilyInPolySpace (LeanCanny.Algebra.SeparableBits.squarefreeValue F) encBits encBits :=
  (LeanCanny.Algebra.SeparableBits.squarefreeEvaluator F A).computable

example (F : LeanCanny.Algebra.SeparableBits.Family)
    (A : LeanCanny.Algebra.SeparableBits.Readers F) :
    LeanCanny.Algebra.SeparableBits.squarefreeBudgetCode F A ∈ LeanCanny.FP :=
  LeanCanny.Algebra.SeparableBits.squarefreeBudgetCode_FP F A

example {L : Type*} [Field L] [CharZero L]
    (S : LeanCanny.Algebra.PrimitivePairBits.Source)
    (A : LeanCanny.Algebra.PrimitivePairBits.Readers S)
    (H : LeanCanny.Algebra.PrimitivePairBits.Heights S)
    (hp : ∀ c, ((S.left c).map (Int.castRingHom L)).Separable)
    (hq : ∀ c, ((S.right c).map (Int.castRingHom L)).Separable)
    (hsp : ∀ c, ((S.left c).map (Int.castRingHom L)).Splits)
    (hsq : ∀ c, ((S.right c).map (Int.castRingHom L)).Splits) :
    ComputableTidilyInPolySpace
      (LeanCanny.Algebra.PrimitivePairBits.coefficient (fun c =>
        LeanCanny.Algebra.cannyResultant (S.left c) (S.right c)
          (LeanCanny.Algebra.PrimitivePair.select (S.left c) (S.right c)))) encBits encBits := by
  simpa only [LeanCanny.Algebra.PrimitivePairBits.selectedDirection_eq] using
    (LeanCanny.Algebra.PrimitivePairBits.selectedResultantEvaluator S A H hp hq hsp hsq).computable

example (F G : LeanCanny.Algebra.SeparableBits.Family)
    (A : LeanCanny.Algebra.SeparableBits.Readers F)
    (B : LeanCanny.Algebra.SeparableBits.Readers G)
    (hF : ∀ c, F.polynomial c ≠ 0) (hG : ∀ c, G.polynomial c ≠ 0) :
    ComputableTidilyInPolySpace (LeanCanny.Algebra.PrimitivePairBits.coefficient
      (LeanCanny.Algebra.PreprocessedPair.parameter F G A B hF hG)) encBits encBits :=
  (LeanCanny.Algebra.PreprocessedPair.parameterEvaluator F G A B hF hG).computable

example (F G : LeanCanny.Algebra.SeparableBits.Family)
    (A : LeanCanny.Algebra.SeparableBits.Readers F)
    (B : LeanCanny.Algebra.SeparableBits.Readers G)
    (hF : ∀ c, F.polynomial c ≠ 0) (hG : ∀ c, G.polynomial c ≠ 0) :
    ComputableTidilyInPolySpace (LeanCanny.Algebra.PrimitivePairBits.coefficient
      (LeanCanny.Algebra.PreprocessedPair.denominator F G A B hF hG)) encBits encBits :=
  (LeanCanny.Algebra.PreprocessedPair.coordinateEvaluators F G A B hF hG).2.2.computable

example (F G : LeanCanny.Algebra.SeparableBits.Family)
    (A : LeanCanny.Algebra.SeparableBits.Readers F)
    (B : LeanCanny.Algebra.SeparableBits.Readers G) :
    ComputableTidilyInPolyTime (LeanCanny.Algebra.PreprocessedPair.outputHeight F G) encBits encNat :=
  LeanCanny.Algebra.PreprocessedPair.outputHeight_binary F G A B

example (F G : LeanCanny.Algebra.SeparableBits.Family)
    (A : LeanCanny.Algebra.SeparableBits.Readers F)
    (B : LeanCanny.Algebra.SeparableBits.Readers G) :
    ComputableTidilyInPolyTime (LeanCanny.Algebra.PreprocessedPair.coordinateHeight F G) encBits encNat :=
  LeanCanny.Algebra.PreprocessedPair.coordinateHeight_binary F G A B

example (F G : LeanCanny.Algebra.SeparableBits.Family)
    (A : LeanCanny.Algebra.SeparableBits.Readers F)
    (B : LeanCanny.Algebra.SeparableBits.Readers G)
    (hF : ∀ c, F.polynomial c ≠ 0) (hG : ∀ c, G.polynomial c ≠ 0) :
    ComputableTidilyInPolySpace
      (LeanCanny.Algebra.PreprocessedPair.reusableReaders F G A B hF hG).coefficient encBits encBits :=
  (LeanCanny.Algebra.PreprocessedPair.reusableReaders F G A B hF hG).evaluator.computable

example {D b n : List Bool → ℕ} (hD : LeanCanny.BinaryFn D) (hb : LeanCanny.BinaryFn b) (hn : LeanCanny.UnaryFn n) :
    ComputableTidilyInPolyTime (fun c => LeanCanny.Algebra.FiniteAnnihilatorTree.sourceHeight (D c) (b c) (n c)) encBits encNat :=
  LeanCanny.Algebra.FiniteAnnihilatorTree.sourceHeight_binary hD hb hn

example (F : LeanCanny.Algebra.SeparableBits.Family) (A : LeanCanny.Algebra.SeparableBits.Readers F)
    (hne : ∀ c, F.polynomial c ≠ 0) (count D : List Bool → ℕ)
    (hn : LeanCanny.UnaryFn count) (hD : LeanCanny.BinaryFn D)
    (hdegree : ∀ c i, i < count c →
      (F.polynomial (LeanCanny.pair c (LeanCanny.BinaryNatCode.encode i))).natDegree ≤ D c) :
    ComputableTidilyInPolySpace (fun c => LeanCanny.BinaryNatCode.encode
      (LeanCanny.Algebra.FiniteAnnihilatorBits.parameter F count hne c).natDegree) encBits encBits :=
  (LeanCanny.Algebra.FiniteAnnihilatorBits.degreeEvaluator F A hne count D hn hD hdegree).computable

example (p n d : List Bool → Polynomial ℤ) (e : List Bool → ℕ)
    (E : ComputableTidilyInPolySpace (fun c => LeanCanny.BinaryNatCode.encode (e c)) encBits encBits)
    (P : ComputableTidilyInPolySpace (LeanCanny.Algebra.PrimitivePairBits.coefficient p) encBits encBits)
    (N : ComputableTidilyInPolySpace (LeanCanny.Algebra.PrimitivePairBits.coefficient n) encBits encBits)
    (D : ComputableTidilyInPolySpace (LeanCanny.Algebra.PrimitivePairBits.coefficient d) encBits encBits) :
    ComputableTidilyInPolySpace (LeanCanny.Algebra.PrimitivePairBits.coefficient
      (fun c => LeanCanny.Algebra.UnivariateRational.clear (e c) (p c) (n c) (d c))) encBits encBits :=
  (LeanCanny.Algebra.UnivariateRationalBits.evaluatorWithExponent p n d e ⟨E⟩ ⟨P⟩ ⟨N⟩ ⟨D⟩).computable

example (outer inner : List Bool → LeanCanny.Algebra.UnivariateRational.Coordinate)
    (ON : ComputableTidilyInPolySpace (LeanCanny.Algebra.PrimitivePairBits.coefficient (fun c => (outer c).numerator)) encBits encBits)
    (OD : ComputableTidilyInPolySpace (LeanCanny.Algebra.PrimitivePairBits.coefficient (fun c => (outer c).denominator)) encBits encBits)
    (IN : ComputableTidilyInPolySpace (LeanCanny.Algebra.PrimitivePairBits.coefficient (fun c => (inner c).numerator)) encBits encBits)
    (ID : ComputableTidilyInPolySpace (LeanCanny.Algebra.PrimitivePairBits.coefficient (fun c => (inner c).denominator)) encBits encBits)
    (bound mass : List Bool → ℕ) (hB : LeanCanny.BinaryFn bound) (hM : LeanCanny.BinaryFn mass)
    (hdegree : ∀ c, (outer c).degree ≤ bound c)
    (hn : ∀ c, LeanCanny.Algebra.coefficientMass (outer c).numerator ≤ 2 ^ mass c)
    (hd : ∀ c, LeanCanny.Algebra.coefficientMass (outer c).denominator ≤ 2 ^ mass c) :
    ComputableTidilyInPolySpace (LeanCanny.Algebra.PrimitivePairBits.coefficient
      (fun c => ((outer c).comp (inner c)).numerator)) encBits encBits :=
  (LeanCanny.Algebra.RationalCoordinateBits.evaluators outer inner ⟨ON⟩ ⟨OD⟩ ⟨IN⟩ ⟨ID⟩ bound mass hB hM hdegree hn hd).1.computable

example (S : LeanCanny.Algebra.PrimitivePairBits.Source)
    (A : LeanCanny.Algebra.PrimitivePairBits.Readers S)
    (hdegree : ∀ c, (LeanCanny.Algebra.cannyResultant (S.left c) (S.right c) (S.direction c)).natDegree =
      (S.left c).natDegree * (S.right c).natDegree) :
    ComputableTidilyInPolySpace (LeanCanny.Algebra.PrimitivePairBits.coefficient
      (fun c => LeanCanny.Algebra.cannyResultant
        (LeanCanny.Algebra.cannyResultant (S.left c) (S.right c) (S.direction c)) (S.right c) (S.direction c))) encBits encBits :=
  (LeanCanny.Algebra.PrimitivePairBits.nestedResultantEvaluator S A hdegree).computable

example {S : LeanCanny.ETR.TubeLevelSign.Source} {B : LeanCanny.ETR.TubeLevelSign.Budget S}
    (a : LeanCanny.Algebra.SignPatternBits.Access (LeanCanny.ETR.TubeLevelSign.family S B))
    (hF : LeanCanny.Algebra.SignPatternBits.ControlsPolyTime (LeanCanny.ETR.TubeLevelSign.family S B))
    (hroot : ComputableTidilyInPolySpace a.rootCoefficient encBits encBits)
    (hquery : ComputableTidilyInPolySpace a.polynomialCoefficient encBits encBits) :
    LeanCanny.ETR.TubeLevelSign.sampleLanguage S ∈ Cslib.Complexity.PSPACE encBits :=
  LeanCanny.ETR.TubeLevelSign.sampleLanguage_mem_PSPACE a hF ⟨hroot⟩ ⟨hquery⟩

example {S : LeanCanny.ETR.TubeLevelSign.Source}
    (B : LeanCanny.ETR.TubeLevelSign.CoordinateBudget S) (hp : S.packet ∈ LeanCanny.FP)
    (a : LeanCanny.Algebra.SignPatternBits.Access (LeanCanny.ETR.TubeLevelSign.family S B.budget))
    (hroot : ComputableTidilyInPolySpace a.rootCoefficient encBits encBits)
    (hquery : ComputableTidilyInPolySpace a.polynomialCoefficient encBits encBits) :
    LeanCanny.ETR.TubeLevelSign.sampleLanguage S ∈ Cslib.Complexity.PSPACE encBits :=
  B.sampleLanguage_mem_PSPACE hp a ⟨hroot⟩ ⟨hquery⟩

example {S : LeanCanny.ETR.TubeLevelSign.Source}
    (C : LeanCanny.ETR.TubeLevelSign.CoefficientReaders S)
    (B : LeanCanny.ETR.TubeLevelSign.CoordinateBudget S)
    (hp : S.packet ∈ LeanCanny.FP) (hm : S.mask ∈ LeanCanny.FP) :
    LeanCanny.ETR.TubeLevelSign.sampleLanguage S ∈ Cslib.Complexity.PSPACE encBits :=
  C.sampleLanguage_mem_PSPACE B hp hm

example {S : LeanCanny.ETR.TubeLevelSign.Source}
    (C : LeanCanny.ETR.TubeLevelSign.CoefficientReaders S)
    (M : LeanCanny.ETR.TubeLevelSign.MassBudget S)
    (hp : S.packet ∈ LeanCanny.FP) (hm : S.mask ∈ LeanCanny.FP)
    (hl : LeanCanny.ETR.TubeLevelSign.SmallLevels S) :
    LeanCanny.ETR.TubeLevelSign.sampleLanguage S ∈ Cslib.Complexity.PSPACE encBits :=
  M.sampleLanguage_mem_PSPACE C hp hm hl

example (packet row target modulus : List Bool → List Bool) (W : List Bool → ℕ)
    (hp : packet ∈ LeanCanny.FP) (hr : row ∈ LeanCanny.FP) (ht : target ∈ LeanCanny.FP)
    (hm : modulus ∈ LeanCanny.FP) (hW : LeanCanny.UnaryFn W) :
    ComputableTidilyInPolySpace
      (fun c => LeanCanny.Algebra.MatrixPower.residueBits
        (((LeanCanny.ETR.TubeLevelPacket.integerConstraint (packet c)
          (LeanCanny.ETR.TubeConstraintCoefficient.decodedRow packet row c)).coeff
          (LeanCanny.ETR.TubeSampleCoefficient.exponent packet W target c) : ℤ) :
            ZMod (Nat.fromBitsLE (modulus c) + 1))) encBits encBits :=
  (LeanCanny.ETR.TubeConstraintCoefficient.encodedEvaluator packet row modulus W target hp hr hm hW ht).computable

#eval "Native PSPACE endpoints and arbitrary native child certificates checked."

/-! The structural class theorems must use native time certificates too. -/

open Lean in
run_cmd do
  let env ← getEnv
  for name in env.header.moduleNames do
    if (`Complexitylib).isPrefixOf name then
      throwError "Project imports obsolete foundation module: {name}"
  let mut pending := #[`LeanCanny.P, `LeanCanny.PolyTimeReduces, `LeanCanny.ExistsReal,
    `LeanCanny.P_subset_existsReal, `LeanCanny.existsReal_subset_PSPACE_iff,
    `LeanCanny.Computation.mem_PSPACE_of_reduction]
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    for forbidden in #[`Complexity.FP, `Complexity.P, `Complexity.MapReducesPoly,
        `LeanCanny.Computation.TidyFP] do
      if forbidden.isPrefixOf name then
        throwError "Structural class theorem depends on legacy time foundation: {name}"
    if let some info := env.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  logInfo m!"Audited {visited.size} transitive constants: native P, reductions, and class closure."

/-! Check actual proof dependencies, including opaque theorem bodies:
polynomial-time support must not reintroduce the old space class. -/

open Lean in
run_cmd do
  let env ← getEnv
  let mut pending : Array Name := #[]
  for (name, _) in env.constants.toList do
    if (`LeanCanny).isPrefixOf name then pending := pending.push name
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    for forbidden in #[`Complexity.PSPACE, `Complexity.NPSPACE, `Complexity.DSPACE,
        `Complexity.NSPACE, `Complexity.SpaceIter,
        `LeanCanny.Computation.SubroutineIteration, `LeanCanny.Computation.WindowedMachine] do
      if forbidden.isPrefixOf name then
        throwError "Project proof depends on obsolete space foundation: {name}"
    if let some info := env.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  logInfo m!"Audited {visited.size} transitive constants: no legacy space foundation."
