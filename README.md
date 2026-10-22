# lean-canny

Foundations for formalizing John Canny's 1988 report,
[*Some Algebraic and Geometric Computations in PSPACE*](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/6041.html).
The report is saved as [`canny-tr.pdf`](canny-tr.pdf).

**Canny's PSPACE upper bound is not proved here yet.** The current development defines
an encoded existential theory of the reals (ETR), its reduction class ∃ℝ, and several
algebraic ingredients. It uses Lean 4.36.0-rc1 with pinned Mathlib, CSLib,
and Complexitylib2 dependencies.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake exe cache get
lake build
```

`lean-toolchain` and `lake-manifest.json` record the versions used. The public entry
point is [`LeanCanny.lean`](LeanCanny.lean).

For stricter verification:

```sh
lake build --wfail
lake env lean scripts/CheckAxioms.lean
lake env lean scripts/CheckGrammar.lean
lake env lean scripts/CheckSpaceFoundation.lean
lake env lean scripts/CheckPolyTimeFoundation.lean
```

The audit checks all declarations in the `LeanCanny` namespace, the local Nat
codec extensions, and their transitive dependencies, allowing only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` axioms.
The space-foundation check also verifies native P, reductions, and PSPACE
endpoints. It rejects legacy time-class dependencies in the structural class
theorems and legacy space-class or scheduler dependencies throughout the project.

All space certificates and PSPACE theorems now use Complexitylib2.
[SpaceFunction](LeanCanny/Computation/SpaceFunction.lean) is a proof-only wrapper
around ComputableTidilyInPolySpace; it contains no initializer, transition,
halting time, execution clock, or saved-child state.
[SpaceDecider](LeanCanny/Computation/SpaceDecider.lean) carries membership in
Complexitylib2's machine-based PSPACE class. The main
[ETR closure theorem](LeanCanny/ETR/PSPACEClosure.lean) targets that class directly.

[TidyBoundedFold](LeanCanny/Computation/TidyBoundedFold.lean) supplies typed
binary-counted folds; [BoundedFold.evaluator](LeanCanny/Computation/BoundedFoldSpace.lean)
certifies the existing raw-code fold. Chaining, pairing, branching, universal
scans, streamed sum/product bits, matrix powering, and Berkowitz now compose
native space proofs. The suspended scheduler, windowed-machine representation,
and temporary legacy-space adapters have been removed. Recursive mathematical
controllers retain their correctness and state-size invariants; the
[iteration interface](LeanCanny/Computation/SpaceIteration.lean) handles their
binary iteration bounds without exposing child execution times.

[RecursiveStack.evaluator](LeanCanny/Computation/RecursiveStackSpace.lean) now
handles input-dependent recursive depth with one fixed native space machine.
Instructions finish a frame, continue locally, or call a lower-rank frame;
one reply installer resumes the caller. Both routines may use polynomial
space and arbitrary time. Semantic invariants, a decreasing potential, and
encoded stack bounds prove correctness and polynomial space. The iteration
budget is `(N+2)^(R+1)` for a binary FP local-progress bound N and unary FP
rank bound R. Canny's recursive coefficient stages still need concrete frames,
instruction/reply routines, and proofs of these contracts; the theorem alone
does not supply their uniform coefficient readers.

[RecursiveController.evaluator](LeanCanny/Computation/RecursiveControllerSpace.lean)
adapts resumable stages to this stack using task/state frames. The remaining
logical halting distance is proof data; frames store no progress counter.
[RecursiveMatrixPower.Source.evaluator](LeanCanny/Algebra/RecursiveMatrixPowerSpace.lean)
now closes input-dependent graphs of modular matrix-power tasks: entry requests
may call lower-rank tasks, and base tasks may use arbitrary polynomial space.
It derives the intermediate-state and logical-step bounds from common task-word
and binary-metadata length bounds. Only base answers require a computation
certificate. The complete Canny coefficient graph, including resultant and
square-free stages, still needs an instantiation.

The resumable [determinant stage](LeanCanny/Algebra/BerkowitzDeterminantRecursiveStage.lean)
now requests Berkowitz factor coefficients as tasks and applies the final parity
correction. Its [factor stage](LeanCanny/Algebra/BerkowitzFactorRecursiveStage.lean)
returns constants or requests one original diagonal/moment coefficient, then
negates the reply. Both have native local-operation certificates without an
answer-computability assumption. Their correctness and logical halting bounds
are proved. The dispatcher below connects them; Canny's full graph still needs
its source-controller instantiation and common rank/size bounds.

[BerkowitzTaskDispatch](LeanCanny/Algebra/BerkowitzTaskDispatch.lean) now joins
determinant, factor, moment, zero, and supplied source controllers in one tagged
task interface. Moment requests route directly to original matrix coefficients.
The dispatcher has native local-operation certificates, and its oracle run has
proved halting and output correctness from the source controller's explicit
semantic contract. The source controller may request other tagged tasks; its
answer function is not assumed space-computable.
[BerkowitzTaskSpace.evaluator](LeanCanny/Algebra/BerkowitzTaskSpace.lean) now
gives uniform native space evaluation from ranked query closure and common
word, reply, metadata, and source-controller bounds. It derives internal stage
storage and step bounds, including factor replies from query closure. The
result supplies actual determinant coefficient readers and zero testing in
native PSPACE. Canny's source controller and the required graph-bound
instantiations remain open.

P and all project polynomial-time reductions now use Complexitylib2 directly,
through [PolyTime](LeanCanny/Computation/PolyTime.lean). This includes the defining
reduction for ∃ℝ, normalization/compiler reductions, and PSPACE reduction closure.
[FP](LeanCanny/Computation/PolyTimeFunctions.lean) is now exactly native tidy
polynomial-time computation on binary strings. Its arithmetic, pairing,
right-fold, range, and bounded-quantifier rules compose native certificates.
Local [tree](LeanCanny/Encoding/Data.lean), [pair](LeanCanny/Encoding/Pairing.lean),
and [binary](LeanCanny/Encoding/BinaryNatCode.lean) codecs preserve the existing
wire formats. The original Complexitylib package, FP machine bridge, and
compatibility patch have been removed. The independent
[polynomial-time audit](scripts/CheckPolyTimeFoundation.lean) checks the
replacement interfaces without importing the rest of the Canny development.

The [isolated prototype](experiments/complexitylib2/README.md) records the
exponential-time-child experiment that motivated this choice.

## Proved so far

| Module | Result |
| --- | --- |
| [`ETR.Syntax`](LeanCanny/ETR/Syntax.lean) | Integer polynomial expressions; Boolean combinations of equality and strict inequality; real semantics; equivalence between an infinite assignment and a finite existential block. |
| [`ETR.Encoding`](LeanCanny/ETR/Encoding.lean) | A canonical binary codec with both round-trip laws; the ETR language rejects malformed strings. Integer constants use binary magnitudes; variable indices use unary. |
| [`ETR.EncodingBounds`](LeanCanny/ETR/EncodingBounds.lean) | Formula arity is at most encoded input length; binary integer payloads have linear bit overhead. |
| [`Encoding.Brackets`](LeanCanny/Encoding/Brackets.lean), [`BracketsFP`](LeanCanny/Encoding/BracketsFP.lean) | A numerical bracket criterion recognizes exactly the image of `Data.toBits`; its one-bit recognizer belongs to native machine-level `FP`. |
| [`Encoding.BracketAccess`](LeanCanny/Encoding/BracketAccess.lean) | Polynomial-time splitting of the first serialized node, child access, enclosing-bracket operations, and cons; exact behavior is proved against the dependency codec. |
| [`ETR.EncodingFP`](LeanCanny/ETR/EncodingFP.lean) | Polynomial-time unary-field writing and recognition, fresh-variable writing, and tagged-node construction; agreement with the typed term/formula encodings. |
| [`ETR.NumericPayloadFP`](LeanCanny/ETR/NumericPayloadFP.lean) | Polynomial-time recognition of exactly the canonical natural and signed-integer payload codes. A finite-state bit-node decoder keeps magnitudes as binary digit lists, with a linear output bound. |
| [`Encoding.TreeFold`](LeanCanny/Encoding/TreeFold.lean), [`TreeFoldFP`](LeanCanny/Encoding/TreeFoldFP.lean) | A bottom-up stack pass agrees with a generic fold on `Data` trees. Fixed finite frames with positive fixed-width injective codes give a uniform machine-level `FP` implementation, with every intermediate stack bounded. |
| [`Encoding.FiniteTreeLanguage`](LeanCanny/Encoding/FiniteTreeLanguage.lean) | Every finite-frame tree classifier yields a polynomial-time predicate on complete canonical tree encodings. |
| [`Encoding.DynamicTreeFold`](LeanCanny/Encoding/DynamicTreeFold.lean) | Input-dependent tree folds can use variable-length frames in a self-delimiting stack. Polynomial-time frame operations and polynomial intermediate stack bounds give `FP`; a polynomial additive frame-growth allowance supplies the stack bound automatically. |
| [`ETR.SyntaxClassifier`](LeanCanny/ETR/SyntaxClassifier.lean), [`SyntaxClassifierCorrect`](LeanCanny/ETR/SyntaxClassifierCorrect.lean) | A finite summary of children recognizes unary fields, bit nodes, canonical binary magnitudes, integers, terms, and formulas; every flag is proved equivalent to the corresponding typed codec image. |
| [`ETR.Grammar`](LeanCanny/ETR/Grammar.lean) | Executable, machine-certified polynomial-time recognizers for exactly the canonical term and formula encodings. Both syntax languages belong to `P`; the formula checker agrees with successful parsing by the original decoder. |
| [`ETR.Complexity`](LeanCanny/ETR/Complexity.lean) | ∃ℝ is the downward closure of ETR under native Complexitylib2 polynomial-time many-one reductions; ETR is complete by definition; reduction closure and `P ⊆ ∃ℝ`. |
| [`ETR.PSPACEClosure`](LeanCanny/ETR/PSPACEClosure.lean) | `∃ℝ ⊆ PSPACE` is equivalent to `ETR ∈ PSPACE`, using proved PSPACE closure under polynomial-time many-one reductions. The same equivalence holds for any ∃ℝ-complete language. The ETR membership hypothesis remains open. |
| [`ETR.Normalization`](LeanCanny/ETR/Normalization.lean) | Single inequalities and disequalities become equations using fresh witnesses; pairs of equations combine through sums of squares or products. |
| [`ETR.NegationNormalForm`](LeanCanny/ETR/NegationNormalForm.lean), [`NNFEncoding`](LeanCanny/ETR/NNFEncoding.lean), [`NNFFP`](LeanCanny/ETR/NNFFP.lean), [`NNFComplexity`](LeanCanny/ETR/NNFComplexity.lean) | A total polynomial-time normalizer pushes negations to atoms, preserves real semantics and arity, and has linear output length. Both polarities and every intermediate stack are bounded, even on raw malformed trees. NNF satisfiability is ∃ℝ-complete under reductions on all binary strings. |
| [`ETR.EquationSystem`](LeanCanny/ETR/EquationSystem.lean) | Arbitrary Boolean formulas compile into equation systems. Every satisfying assignment extends to a solution, preserving the original variables; every solution satisfies the formula. |
| [`ETR.EquationNormalization`](LeanCanny/ETR/EquationNormalization.lean) | A single final sum of squares collapses the system to one equisatisfiable integer polynomial equation. |
| [`ETR.EquationSize`](LeanCanny/ETR/EquationSize.lean) | For an input of `n` bits, the resulting equation has at most `500*(n+1)^3` encoded bits and arity at most `2*n`. This includes all unary fresh-variable indices and binary integer payloads. |
| [`ETR.SingleEquation`](LeanCanny/ETR/SingleEquation.lean) | A total executable map on binary strings preserves exactly the yes-instances from ETR to the single-equation language. Malformed inputs map to `1 = 0`; the output-length bound holds on all inputs. |
| [`ETR.EquationDegree`](LeanCanny/ETR/EquationDegree.lean) | The corresponding Mathlib integer multivariate polynomial has total degree at most `4*n` and has a real zero exactly when the original formula is satisfiable. |
| [`ETR.SingleEquationComplexity`](LeanCanny/ETR/SingleEquationComplexity.lean) | A polynomial-time many-one reduction from the single-equation language to ETR; hence the single-equation language belongs to ∃ℝ. Correctness covers malformed inputs too. |
| [`ETR.SumSquaresFP`](LeanCanny/ETR/SumSquaresFP.lean) | A polynomial-time bitstring writer collapses an encoded equation list into a sum of squares. Its complete paired state grows by at most 18 bits per iteration; the output vanishes exactly when every input term does. |
| [`ETR.EquationList`](LeanCanny/ETR/EquationList.lean), [`EquationListComplexity`](LeanCanny/ETR/EquationListComplexity.lean) | An exact `FP` recognizer for encoded term lists and a polynomial-time many-one reduction from satisfiable equation systems to one equation. Malformed strings map to `1 = 0`; the equation-system language belongs to ∃ℝ. |
| [`ETR.EquationEncoding`](LeanCanny/ETR/EquationEncoding.lean), [`EquationSystemEncoding`](LeanCanny/ETR/EquationSystemEncoding.lean) | Polynomial-time writers for fresh-witness equations, Boolean selectors, conjunction, and disjunction; exact agreement with the typed operations and literal length formulas. |
| [`ETR.EquationMaskFP`](LeanCanny/ETR/EquationMaskFP.lean) | A polynomial-time pass multiplies every equation by a branch selector, preserving order. The complete loop state adds at most `factor.length + 10` bits per step on all strings. |
| [`ETR.EquationCompilerMachine`](LeanCanny/ETR/EquationCompilerMachine.lean), [`EquationCompilerBounds`](LeanCanny/ETR/EquationCompilerBounds.lean), [`EquationCompilerStateEncoding`](LeanCanny/ETR/EquationCompilerStateEncoding.lean) | A sequential stack compiler agrees exactly with `SignedFormula.equations`, terminates within twice the formula's bit length, and keeps its entire encoded state below `10000*(n+1)^3` bits throughout the run, starting fresh indices at `n`. |
| [`ETR.EquationCompilerAtomEncoding`](LeanCanny/ETR/EquationCompilerAtomEncoding.lean), [`EquationCompilerStepEncoding`](LeanCanny/ETR/EquationCompilerStepEncoding.lean), [`EquationCompilerFP`](LeanCanny/ETR/EquationCompilerFP.lean) | The encoded step implements the typed stack machine and belongs to `FP`. The bounded loop gives polynomial-time reductions from ETR to equation systems and single equations, proving both target languages ∃ℝ-complete. Correctness covers all binary strings. |
| [`Algebra.Separation`](LeanCanny/Algebra/Separation.lean) | For `m` points in a characteristic-zero field, an integer `0 ≤ c ≤ m²` makes `(a,b) ↦ a+c*b` injective. Lagrange interpolation recovers both coordinates with degree below `m`. |
| [`Algebra.SymmetricRecoveryDegeneracy`](LeanCanny/Algebra/SymmetricRecoveryDegeneracy.lean) | The finite system `x^3-x=0, y=0` has no projective roots at infinity, yet the report's symmetric recovery pair at the middle root has a cubic GCD, even with distinct original projected roots. |
| [`Algebra.VectorSeparation`](LeanCanny/Algebra/VectorSeparation.lean), [`AffineGridAvoidance`](LeanCanny/Algebra/AffineGridAvoidance.lean), [`AsymmetricProjection`](LeanCanny/Algebra/AsymmetricProjection.lean) | For N vectors in n coordinates, a positive weight `k ≤ N^4+1` and integer direction coefficients `≤ (n+1)*N^4` separate every coordinate's asymmetric root pairs simultaneously. |
| [`Algebra.AsymmetricCoordinateRecovery`](LeanCanny/Algebra/AsymmetricCoordinateRecovery.lean) | Nodal projection polynomials give rational coordinates in the original projection parameter, with nonzero denominators on every point. Denominator degree is at most `max 1 ((N-1)*N)` and numerator degree at most one more. Constructing these polynomials from encoded multivariate equations remains open. |
| [`Algebra.VectorGaloisDescent`](LeanCanny/Algebra/VectorGaloisDescent.lean), [`AsymmetricBaseCoordinates`](LeanCanny/Algebra/AsymmetricBaseCoordinates.lean) | Over a Galois extension in characteristic zero, a stable finite vector set has a monic separable eliminant and bounded-degree rational coordinates over the base field, with the same bounded integer choices. Full finite zero sets of base-field equations are stable. |
| [`Algebra.GaloisFixedPolynomial`](LeanCanny/Algebra/GaloisFixedPolynomial.lean), [`FiniteSystemCoordinates`](LeanCanny/Algebra/FiniteSystemCoordinates.lean) | A full finite polynomial zero set in an algebraic closure has a base-field rational univariate representation. Eliminant roots and solutions are in bijection; directions and coordinate degrees are bounded in the solution count. No finite-dimensional ambient-field hypothesis is needed. |
| [`Algebra.ProjectionSystemCoordinates`](LeanCanny/Algebra/ProjectionSystemCoordinates.lean) | One common integer direction gives base-field rational representations for the extended regular critical systems of a finite family of hypersurfaces. Every eliminant root decodes to a regular critical point. The direction-grid bound is existential; input-size and coefficient algorithms remain open. |
| [`Algebra.RationalRepresentationTransfer`](LeanCanny/Algebra/RationalRepresentationTransfer.lean), [`ProjectionCoordinateTransfer`](LeanCanny/Algebra/ProjectionCoordinateTransfer.lean) | Algebraic-closure representations decode soundly at eliminant roots in every extension field, preserving nonzero denominators and the projection parameter. In particular, real parameter roots give real regular critical points. Solutions with algebraic coordinates are recovered from parameter roots in their own field; the certified critical systems below discharge this hypothesis. |
| [`Algebra.CoordinateAnnihilatorSpecialization`](LeanCanny/Algebra/CoordinateAnnihilatorSpecialization.lean), [`ProjectionAnnihilatorDirections`](LeanCanny/Algebra/ProjectionAnnihilatorDirections.lean), [`CompleteProjectionCoordinates`](LeanCanny/Algebra/CompleteProjectionCoordinates.lean) | Retained annihilators make every solution of selected critical systems algebraic over the input field in every extension. Eliminant roots and regular critical points are in bijection over the reals too, without a separate algebraicity hypothesis. One integer direction works for a finite surface family; its grid bound remains existential. |
| [`Algebra.FiniteSystemTransfer`](LeanCanny/Algebra/FiniteSystemTransfer.lean) | A finite full zero set over an algebraically closed field has no new solutions in extension fields. Algebraic-closure rational representations therefore decode completely in every target field, including the reals, without a separate algebraicity hypothesis on the solution. Parameter roots and full solutions are in bijection, and arbitrary predicates on solutions transfer to decoded roots. |
| [`Algebra.IntegerCoordinatePolynomials`](LeanCanny/Algebra/IntegerCoordinatePolynomials.lean), [`IntegerProjectionCoordinates`](LeanCanny/Algebra/IntegerProjectionCoordinates.lean) | Rational representations can use integer eliminants and integer coordinate numerator/denominator pairs, preserving degrees, roots, values and denominator nonvanishing. Certified regular critical points and integer eliminant roots are in bijection in every rational extension, including the reals. Multivariate input bounds and coefficient readers remain open. |
| [`Algebra.MacaulayMatrix`](LeanCanny/Algebra/MacaulayMatrix.lean), [`MacaulayRoots`](LeanCanny/Algebra/MacaulayRoots.lean) | A square coefficient matrix for homogeneous systems uses fixed-width monomial ranks and identity padding outside degree `1+∑(dᵢ−1)`. Entries select one source coefficient or an identity entry. Any nonzero common root forces determinant zero when the width covers that degree; coefficient maps commute with the construction. This is a determinant candidate, with no resultant identification or converse yet. |
| [`Algebra.MacaulayDeformation`](LeanCanny/Algebra/MacaulayDeformation.lean), [`MacaulayBounds`](LeanCanny/Algebra/MacaulayBounds.lean) | Interpolation to coordinate powers gives a nonzero determinant polynomial with value one at deformation parameter one. Its degree is at most the padded dimension M. Integer input coefficients bounded by `2^B` give determinant coefficient bit bound `M.size*M+M*(B+2)+1`. Extracting the required eliminant and proving its factorization remain open. |
| [`Algebra.MacaulayEntryControl`](LeanCanny/Algebra/MacaulayEntryControl.lean), [`MacaulayEntrySpace`](LeanCanny/Algebra/MacaulayEntrySpace.lean), [`MacaulayEntryCorrect`](LeanCanny/Algebra/MacaulayEntryCorrect.lean), [`MacaulayPSPACE`](LeanCanny/Algebra/MacaulayPSPACE.lean) | FP controls test total degree using clipped exponents, find the first divisible coordinate, and prepare the exact source coefficient query. Given polynomially bounded unary arity/width/degrees, an FP binary coefficient budget, and certified source residue readers, integer padded Macaulay determinant zero testing is in PSPACE, with space-bounded child costs included. The full regular-system coefficient evaluator is instantiated below; concrete parameter selection remains open. |
| [`Algebra.MacaulayEntryEncoding`](LeanCanny/Algebra/MacaulayEntryEncoding.lean), [`MacaulayPolynomialSpace`](LeanCanny/Algebra/MacaulayPolynomialSpace.lean) | The selector supports arbitrary scalar encodings, including a selected polynomial coefficient. FP controls and certified original polynomial-coefficient residue readers give a complete selected determinant-coefficient evaluator over a varying positive modulus; padding contributes only at coefficient degree zero. |
| [`Algebra.PolynomialKronecker`](LeanCanny/Algebra/PolynomialKronecker.lean), [`MacaulayBivariateSpace`](LeanCanny/Algebra/MacaulayBivariateSpace.lean) | Independent perturbation and projection variables are encoded with radix `M*D+1`, where `M` is the padded matrix dimension and `D` bounds each entry's inner degree. Exact coefficient recovery is proved using the full determinant bound. FP quotient/remainder queries compose the original bivariate source reader with the complete determinant evaluator; selected modular coefficient zero testing is in PSPACE. Requests outside the radix return zero. The full tube source and determinant evaluator are instantiated below. |
| [`Algebra.MacaulayAffineDeformation`](LeanCanny/Algebra/MacaulayAffineDeformation.lean), [`MacaulayDeformationSpace`](LeanCanny/Algebra/MacaulayDeformationSpace.lean), [`MacaulayDeformationResidue`](LeanCanny/Algebra/MacaulayDeformationResidue.lean), [`MacaulayDeformationSign`](LeanCanny/Algebra/MacaulayDeformationSign.lean) | The actual deformation matrix is `A+ε*(I-A)`. Its selected determinant coefficient has certified modular evaluation, three-way integer signs, and PSPACE zero/strict-sign tests from the original integer source residue reader, unary layout/degree certificates, and FP binary coefficient/degree fields. The original coefficient budget gives `M.size*M+M*(B+2)+1`; no separate reader for deformed source coefficients is assumed. The full three-parameter tube instance is certified below; identifying the eliminant coefficient remains open. |
| [`Algebra.WeightedHomogenization`](LeanCanny/Algebra/WeightedHomogenization.lean), [`HomogenizationLayout`](LeanCanny/Algebra/HomogenizationLayout.lean), [`HomogenizationSpace`](LeanCanny/Algebra/HomogenizationSpace.lean), [`HomogeneousSubstitution`](LeanCanny/Algebra/HomogeneousSubstitution.lean) | Partial homogenization keeps parameter weights zero and gives a single-source coefficient formula. The affine chart, coefficient maps, degree/coordinate bounds and fixed-width layout are proved. FP clipped-degree controls and one space-bounded original coefficient call give a complete residue reader. Substitution of coefficient constants turns weighted homogeneity into ordinary homogeneity. |
| [`ETR.TubeHomogenization`](LeanCanny/ETR/TubeHomogenization.lean), [`TubeMacaulaySystem`](LeanCanny/ETR/TubeMacaulaySystem.lean) | The actual compiled tube projection rows have partially homogenized residue readers, unchanged coefficient bounds, and complete coordinate-width coverage. Direction and perturbation parameters stay in the coefficient ring. An explicit flattening bijection connects ordinary homogeneous spatial rows to these integer sources. One linear projection equation gives square Macaulay inputs containing every original row; a projection point at the selected linear value forces determinant zero. The regular system and parameter-coefficient specialization below extend this construction; eliminant identification remains open. |
| [`Algebra.ReciprocalEquation`](LeanCanny/Algebra/ReciprocalEquation.lean), [`ReciprocalBounds`](LeanCanny/Algebra/ReciprocalBounds.lean), [`ReciprocalSpace`](LeanCanny/Algebra/ReciprocalSpace.lean) | The equation `u*∂p/∂x−1=0` enforces a nonzero partial and uniquely determines its inverse. Its degree is at most `max(deg p,1)`; coefficients have explicit derivative bounds. Fixed-width guards and one space-bounded derivative-coefficient call give a complete residue reader. |
| [`ETR.TubeRegularSource`](LeanCanny/ETR/TubeRegularSource.lean), [`TubeRegularDerivative`](LeanCanny/ETR/TubeRegularDerivative.lean), [`TubeRegularSpace`](LeanCanny/ETR/TubeRegularSpace.lean) | The actual compiled tube system includes the reciprocal equation. Roots correspond exactly to regular projection roots with their uniquely determined inverse. All rows retain degree allowance `8*N²+4`; coefficient magnitudes are at most `2^(28*N²+6*N+26)`. The existing derivative evaluator supplies a complete residue reader, with total row decoding and every original row covered. |
| [`ETR.TubeRegularHomogenization`](LeanCanny/ETR/TubeRegularHomogenization.lean), [`TubeRegularMacaulay`](LeanCanny/ETR/TubeRegularMacaulay.lean) | Partial homogenization includes the inverse and point coordinates while retaining direction and perturbation parameters as coefficients. Its complete residue reader preserves coefficient bounds and covers all supported exponents. An explicit flattening bijection connects the integer source to ordinary homogeneous spatial rows. Adding a linear projection equation gives square Macaulay inputs containing the reciprocal and every original row. Every regular-system root at the selected linear value forces determinant zero. The bivariate instance below composes the coefficient readers into a full determinant evaluator; identifying the eliminant remains open. |
| [`Algebra.PartialCoefficient`](LeanCanny/Algebra/PartialCoefficient.lean), [`PartialCoefficientSpace`](LeanCanny/Algebra/PartialCoefficientSpace.lean) | Filtering spatial exponents in a finite indexed monomial source gives exactly the selected coefficient polynomial in the remaining parameters. Fixed-width prefix equality is in FP, and filtering uses one space-bounded original coefficient call. Binary source ranks remain unexpanded. |
| [`ETR.TubeParameterLayout`](LeanCanny/ETR/TubeParameterLayout.lean), [`TubeParameterSource`](LeanCanny/ETR/TubeParameterSource.lean) | The regular tube system's spatial prefix and parameter suffix preserve the native reader's variable order. Actual regular-source residues supply the filtered coefficient source, including total row decoding, canonical modulus packets, and modulus one. |
| [`ETR.TubeParameterSubstitution`](LeanCanny/ETR/TubeParameterSubstitution.lean), [`TubeParameterCorrect`](LeanCanny/ETR/TubeParameterCorrect.lean) | Certified parameter-coordinate readers give a complete residue evaluator for the selected spatial coefficient after rational parameter substitution and denominator clearing. Its native coefficient identity and common even-power denominator scale are proved; for sufficiently small positive parameter values where all parameter denominators are nonzero, the spatial coefficient sign equals the cleared polynomial's trailing-coefficient sign. Source and parameter child workspace are included; no source-coefficient callback is assumed. |
| [`ETR.TubeParameterBounds`](LeanCanny/ETR/TubeParameterBounds.lean), [`TubeParameterDecisions`](LeanCanny/ETR/TubeParameterDecisions.lean) | Parameter degree and coefficient bounds give FP binary output-degree and coefficient-bit writers, three-way integer coefficient signs, coefficient zero testing in PSPACE, and a complete infinitesimal sign evaluator. The full Macaulay coefficient evaluator is instantiated below; concrete parameter selection and eliminant extraction remain open. |
| [`ETR.TubeClearedSystem`](LeanCanny/ETR/TubeClearedSystem.lean), [`TubeMacaulayLayout`](LeanCanny/ETR/TubeMacaulayLayout.lean), [`TubeClearedCoefficientSpace`](LeanCanny/ETR/TubeClearedCoefficientSpace.lean) | Uniform denominator clearing produces actual homogeneous regular rows over integer univariate polynomials. Specializing a cleared row equals a common scalar times the original specialized row. The FP layout width covers the full Macaulay level, and a guarded coefficient reader bridges that width to the native source width with all parameter-reader costs included. These readers compose into the full matrix source below. |
| [`Algebra.LinearCoefficientSpace`](LeanCanny/Algebra/LinearCoefficientSpace.lean), [`ETR.TubeLinearCoefficientSpace`](LeanCanny/ETR/TubeLinearCoefficientSpace.lean) | A streamed modular sum certifies coefficients of homogeneous linear polynomials. For the projection row, FP encoded integer direction access supplies every scalar residue internally, including modulus one. In the affine chart the actual polynomial evaluates to `X−ℓ·z`. Its coefficient evaluator composes with the regular-row evaluator for the full bivariate family below. |
| [`ETR.TubeParameterReaders`](LeanCanny/ETR/TubeParameterReaders.lean), [`TubeClearedRows`](LeanCanny/ETR/TubeClearedRows.lean), [`TubeBivariateSystem`](LeanCanny/ETR/TubeBivariateSystem.lean) | Parameter-coordinate readers and bounds compose with FP projections from extended matrix contexts. One FP degree allowance covers every spatial coefficient. The full homogeneous system combines the linear projection equation in the outer variable with the reciprocal and original regular rows over the inner perturbation variable. Its modular family meets the bivariate determinant backend's degree contract for every positive modulus. The source and determinant coefficient evaluators are certified below. |
| [`ETR.TubeBivariateCoefficients`](LeanCanny/ETR/TubeBivariateCoefficients.lean), [`TubeBivariateQuery`](LeanCanny/ETR/TubeBivariateQuery.lean), [`TubeBivariateSource`](LeanCanny/ETR/TubeBivariateSource.lean), [`TubeBivariateSpace`](LeanCanny/ETR/TubeBivariateSpace.lean) | Parameter-coordinate readers and bounds, FP input/degree fields, and FP encoded integer direction access give a complete evaluator for selected modular coefficients of the actual full regular-system Macaulay determinant. The reciprocal, original and linear projection rows are all internal, with independent inner and outer variables and space-bounded parameter-reader costs included. Selected modular coefficient zero testing is in PSPACE. Integer coefficient budgets and sign recovery are proved below; effective parameter choice, deformation/eliminant extraction, and the full ETR algorithm remain open. |
| [`ETR.TubeClearedBudget`](LeanCanny/ETR/TubeClearedBudget.lean), [`TubeDirectionBounds`](LeanCanny/ETR/TubeDirectionBounds.lean), [`TubeBivariateBudget`](LeanCanny/ETR/TubeBivariateBudget.lean) | FP binary budgets bound every integer coefficient of the actual full bivariate determinant by `M.size*M+M*b+1` magnitude bits. Regular-row mass allowances come from the parameter bounds; the direction budget is derived from the actual FP reader output lengths. Encoding the projection variable preserves these allowances for every radix. The determinant inner-degree bound covers out-of-range coefficient requests. The modulus-independent residue bridge and integer sign recovery are certified below. |
| [`ETR.TubeBivariateResidue`](LeanCanny/ETR/TubeBivariateResidue.lean), [`TubeBivariateSign`](LeanCanny/ETR/TubeBivariateSign.lean) | Appending a modulus preserves the original system, parameter polynomials, integer direction and selected degrees, so the full evaluator supplies residues of one fixed integer determinant coefficient. Its proved budget and actual residue evaluator give three-way integer signs and PSPACE zero/negative/positive tests under the existing parameter-reader and FP input contracts. No additional direction-size, row, entry, determinant or sign reader is assumed. Eliminant identification and effective parameter choice remain open. |
| [`Algebra.PolynomialTripleDegree`](LeanCanny/Algebra/PolynomialTripleDegree.lean), [`MacaulayDeformationParameters`](LeanCanny/Algebra/MacaulayDeformationParameters.lean), [`ETR.TubeDeformationSystem`](LeanCanny/ETR/TubeDeformationSystem.lean) | The actual full tube system has an independent third deformation parameter. Its determinant is nonzero, evaluates to one at deformation one, and returns the original determinant at zero. Its deformation degree is at most the padded dimension `M`; each inner coefficient degree is at most `M*E`. An FP radix writer and exact coefficient recovery preserve perturbation and projection variables while leaving deformation independent. The deformed coefficient evaluator is certified below; eliminant extraction remains open. |
| [`Algebra.PolynomialAffineDeformation`](LeanCanny/Algebra/PolynomialAffineDeformation.lean), [`MacaulayPolynomialDeformationBounds`](LeanCanny/Algebra/MacaulayPolynomialDeformationBounds.lean), [`ETR.TubeDeformationBudget`](LeanCanny/ETR/TubeDeformationBudget.lean) | An encoded affine entry coefficient uses one original coefficient, a quotient/remainder branch, and a scalar degree-zero test. Encoding the full deformation increases the source mass allowance by at most two bits. FP binary degree and magnitude budgets bound every integer coefficient of the actual three-parameter determinant by `M.size*M+M*(b+2)+1` magnitude bits. The complete deformed entry/determinant evaluator is certified below; eliminant extraction remains open. |
| [`Algebra.PolynomialAffineEntrySpace`](LeanCanny/Algebra/PolynomialAffineEntrySpace.lean), [`BerkowitzAffinePolynomialSpace`](LeanCanny/Algebra/BerkowitzAffinePolynomialSpace.lean) | A polynomial matrix deformed toward the identity has a complete selected modular determinant-coefficient evaluator. One original entry coefficient call, FP quotient/remainder controls, and modular arithmetic supply each deformed entry. A second bounded encoding preserves the independent deformation variable; all space-bounded original entry costs are included. |
| [`ETR.TubeDeformationModular`](LeanCanny/ETR/TubeDeformationModular.lean), [`TubeDeformationCoefficientMap`](LeanCanny/ETR/TubeDeformationCoefficientMap.lean), [`TubeDeformationSpace`](LeanCanny/ETR/TubeDeformationSpace.lean) | The actual full tube matrix instantiates that backend. Reduction commutes with both parameter encoding and deformation. Two exponent guards recover every selected perturbation/projection/deformation coefficient exactly, including zero outside its allowance. The complete modular evaluator uses the existing parameter-coordinate readers and bounds, FP input/degree fields, and FP integer direction reader; no row or entry oracle is added. |
| [`ETR.TubeDeformationResidue`](LeanCanny/ETR/TubeDeformationResidue.lean), [`TubeDeformationSign`](LeanCanny/ETR/TubeDeformationSign.lean) | Appending a modulus preserves the original three-parameter integer coefficient. Its actual residue evaluator and proved budget give three-way integer signs and PSPACE zero/negative/positive tests, with all original reader costs included. Eliminant identification, factor extraction, concrete sampler parameter readers, and effective parameter choice remain open. |
| [`Algebra.DeformationLowestCoefficient`](LeanCanny/Algebra/DeformationLowestCoefficient.lean), [`ETR.TubeDeformationLowest`](LeanCanny/ETR/TubeDeformationLowest.lean) | The lowest deformation coefficient is a nonzero bivariate candidate. Its vanishing under coefficient specialization is equivalent to an increase in deformation order; the specialized determinant stays nonzero because its value at one is one. Converging coefficient parameters with actual nonzero deformed homogeneous roots force candidate vanishing at the limit, over real or complex fields. Geometric root persistence and identification with the resultant quotient remain open. |
| [`ETR.TubeDeformationSpecialization`](LeanCanny/ETR/TubeDeformationSpecialization.lean) | The actual coefficient and degree budgets give an FP binary exponent `s=K+(M*E+1).size+1`. For every `0<θ≤2^(-s)`, the lowest coefficient specializes to a nonzero projection polynomial, preserving both the lowest deformation order and its coefficient. This is an effective nonvanishing bound. The lowest-coefficient access algorithm is certified below; geometric root persistence and the other sampling conditions remain open. |
| [`Computation.SpaceDeciderFunction`](LeanCanny/Computation/SpaceDeciderFunction.lean), [`Algebra.LowestCoefficientSpace`](LeanCanny/Algebra/LowestCoefficientSpace.lean) | Certified zero-test flags feed a bounded first-index scan for any coefficient ring. The accumulator stores one binary index, with the zero-polynomial convention included. An FP binary degree bound and complete space-bounded coefficient zero tests give an evaluator for the natural trailing degree, including all space-bounded child costs. |
| [`ETR.TubeBivariateReindex`](LeanCanny/ETR/TubeBivariateReindex.lean), [`TubeDeformationCoefficientPolynomial`](LeanCanny/ETR/TubeDeformationCoefficientPolynomial.lean), [`TubeDeformationCoefficientZero`](LeanCanny/ETR/TubeDeformationCoefficientZero.lean) | Each full deformation coefficient polynomial has an encoded degree allowance with an FP binary writer. Encoding preserves zero exactly; quotient/remainder queries recover scalar coefficients. A bounded scan of the complete integer zero evaluator decides whole coefficient-polynomial identity in PSPACE, using the existing parameter and direction readers. |
| [`ETR.TubeDeformationLowestSpace`](LeanCanny/ETR/TubeDeformationLowestSpace.lean), [`TubeDeformationLowestLanguages`](LeanCanny/ETR/TubeDeformationLowestLanguages.lean) | The full determinant's lowest nonzero deformation index is computed in polynomial space, with minimality and dimension bounds. Sequential composition gives selected modular coefficients, three-way integer signs, and PSPACE zero/negative/positive tests for the actual nonzero lowest bivariate coefficient. No index, row, entry, or sign oracle is supplied. Geometric root persistence and resultant-factor identification remain open. |
| [`Algebra.PolynomialAffineReparametrization`](LeanCanny/Algebra/PolynomialAffineReparametrization.lean), [`PolynomialSignedReflection`](LeanCanny/Algebra/PolynomialSignedReflection.lean) | Homogenizing a degree-bounded polynomial and substituting `(X,1-X)` preserves its lowest nonzero order and coefficient. Substituting `-X` preserves the order and multiplies its coefficient by `(-1)^order`. These identities hold over arbitrary commutative rings. |
| [`Algebra.AffineCharacteristic`](LeanCanny/Algebra/AffineCharacteristic.lean), [`MacaulayCharacteristic`](LeanCanny/Algebra/MacaulayCharacteristic.lean), [`ETR.TubeDeformationCharacteristic`](LeanCanny/ETR/TubeDeformationCharacteristic.lean) | The affine determinant is the homogeneous substitution of `det(A+sI)`. The actual full tube characteristic numerator `det(A-sI)=(-1)^M*χ_A(s)` has the same lowest order as the computed deformation, with lowest coefficient multiplied by `(-1)^order`. Its lowest coefficient is nonzero and has exactly the same zero condition after every coefficient specialization. This does not identify the resultant quotient. |
| [`Algebra.SignedTagSpace`](LeanCanny/Algebra/SignedTagSpace.lean), [`ETR.TubeDeformationCharacteristicSpace`](LeanCanny/ETR/TubeDeformationCharacteristicSpace.lean) | The complete lowest-index and integer-sign evaluators supply selected lowest characteristic-numerator coefficient signs through an FP parity correction. Zero, negative, and positive tests are in PSPACE, with both child costs included and no new reader or index oracle. The resultant quotient and geometric root persistence remain open. |
| [`Algebra.MacaulayExtraneous`](LeanCanny/Algebra/MacaulayExtraneous.lean), [`MacaulayExtraneousControl`](LeanCanny/Algebra/MacaulayExtraneousControl.lean), [`PolynomialPrincipalSpace`](LeanCanny/Algebra/PolynomialPrincipalSpace.lean) | The extraneous principal minor selects active level monomials divisible by at least two designated coordinate powers. Identity row padding preserves its determinant, affine deformation, and lowest characteristic coefficient; membership is in FP. A generic principal-deformation evaluator includes the original entry-reader costs. |
| [`ETR.TubeExtraneousSpace`](LeanCanny/ETR/TubeExtraneousSpace.lean), [`TubeExtraneousCharacteristic`](LeanCanny/ETR/TubeExtraneousCharacteristic.lean) | The actual full tube extraneous deformation is nonzero and its selected three-parameter coefficient residues have complete polynomial-space evaluators under the existing coordinate-reader contracts. The true minor's lowest subtractive characteristic order and coefficient agree with the affine ones up to the order sign. The resultant quotient formula remains open. |
| [`Algebra.PrincipalPolynomialBounds`](LeanCanny/Algebra/PrincipalPolynomialBounds.lean), [`MacaulayExtraneousBounds`](LeanCanny/Algebra/MacaulayExtraneousBounds.lean), [`ETR.TubeExtraneousSign`](LeanCanny/ETR/TubeExtraneousSign.lean) | Identity padding preserves entry degree and mass bounds. The full numerator's binary budget also bounds every extraneous deformation coefficient, giving complete integer sign/zero evaluators and PSPACE zero/negative/positive tests through streamed CRT. |
| [`ETR.TubeExtraneousCoefficientZero`](LeanCanny/ETR/TubeExtraneousCoefficientZero.lean), [`TubeExtraneousLowestLanguages`](LeanCanny/ETR/TubeExtraneousLowestLanguages.lean), [`TubeExtraneousCharacteristicSpace`](LeanCanny/ETR/TubeExtraneousCharacteristicSpace.lean) | Whole-coefficient zero tests compute the extraneous determinant's lowest nonzero deformation index in polynomial space, with minimality and dimension bounds. Selected lowest-coefficient residues and signs, and lowest characteristic-denominator signs, include all search and reader costs. No index or sign oracle is supplied. |
| [`Algebra.PrincipalCharacteristic`](LeanCanny/Algebra/PrincipalCharacteristic.lean), [`MacaulayActiveCharacteristic`](LeanCanny/Algebra/MacaulayActiveCharacteristic.lean), [`MacaulaySubtractiveSystem`](LeanCanny/Algebra/MacaulaySubtractiveSystem.lean) | The padded characteristic numerator equals the true degree-level numerator times `(1-s)^padding`, with identical lowest order and coefficient. Replacing every homogeneous input by `fᵢ-s*xᵢ^dᵢ` subtracts `s` on the diagonal of both true principal matrices. |
| [`Algebra.PolynomialQuotientLowest`](LeanCanny/Algebra/PolynomialQuotientLowest.lean), [`ETR.TubeCharacteristicQuotient`](LeanCanny/ETR/TubeCharacteristicQuotient.lean) | The nonzero rational quotient of the true tube characteristic determinants is constructed and equals the determinant ratio for the shifted system. Its signed order and lowest coefficient ratio are independent of the nonzero fraction representation. If a polynomial quotient identity is supplied, these are its ordinary lowest term. A concrete polynomial representative is proved below; resultant identification remains open. |
| [`ETR.TubeCharacteristicQuotientSpace`](LeanCanny/ETR/TubeCharacteristicQuotientSpace.lean) | Both complete lowest-index evaluators compute the rational quotient's signed order in polynomial space, and negative-order testing is in PSPACE. The existing sign routine also computes selected scalar signs of the true unpadded numerator's lowest coefficient. Both child costs are included. |
| [`Algebra.MacaulayReducedCount`](LeanCanny/Algebra/MacaulayReducedCount.lean), [`CharacteristicQuotientDegree`](LeanCanny/Algebra/CharacteristicQuotientDegree.lean) | An explicit bijection counts reduced monomials at the Macaulay level: the full/extraneous matrix-size difference is `D = Σᵢ ∏ⱼ≠ᵢ dⱼ`, for positive degrees and sufficient exponent width. The characteristic determinant quotient has Mathlib rational-function integer degree `D` after any faithful coefficient embedding in a field. |
| [`ETR.TubeCharacteristicQuotientDegree`](LeanCanny/ETR/TubeCharacteristicQuotientDegree.lean) | The tube quotient's faithful extension to its coefficient fraction field has integer degree `D`, with `0 < D ≤` the padded matrix dimension. The extension map is injective and agrees with the existing quotient. Any polynomial satisfying the quotient identity has natural degree exactly `D`; its concrete construction is proved below. |
| [`Algebra.CharacteristicPolynomialQuotient`](LeanCanny/Algebra/CharacteristicPolynomialQuotient.lean), [`MacaulayCharacteristicQuotient`](LeanCanny/Algebra/MacaulayCharacteristicQuotient.lean), [`ETR.TubeCharacteristicPolynomial`](LeanCanny/ETR/TubeCharacteristicPolynomial.lean), [`TubeCharacteristicPolynomialSpace`](LeanCanny/ETR/TubeCharacteristicPolynomialSpace.lean) | Monic division constructs the exact characteristic quotient over the original coefficient ring, commuting with all coefficient maps. Over a domain its degree is `D = sum_i product_(j!=i) d_j` and leading coefficient `(-1)^D`; that degree survives nontrivial specialization. The actual tube polynomial represents the existing rational value and lowest data, so its order is nonnegative. Its natural trailing degree has a space evaluator, and constant-coefficient zero testing belongs to PSPACE under the existing reader contracts. The projective common-root criterion is proved below; multivariate-resultant identification remains open. |
| [`Algebra.MacaulayUniversalQuotient`](LeanCanny/Algebra/MacaulayUniversalQuotient.lean), [`MacaulayQuotientSpecialization`](LeanCanny/Algebra/MacaulayQuotientSpecialization.lean), [`MacaulayQuotientRoots`](LeanCanny/Algebra/MacaulayQuotientRoots.lean) | The normalized universal integer polynomial specializes naturally over every commutative ring. Its value on shifted inputs equals the characteristic quotient, including parameter values where the extraneous determinant vanishes. An initial deformation proves axis-root vanishing; the general theorem below subsumes it. |
| [`Algebra.MacaulayRootModel`](LeanCanny/Algebra/MacaulayRootModel.lean), [`MacaulayRootDeformation`](LeanCanny/Algebra/MacaulayRootDeformation.lean), [`MacaulayQuotientPermutation`](LeanCanny/Algebra/MacaulayQuotientPermutation.lean), [`MacaulayProjectiveRoots`](LeanCanny/Algebra/MacaulayProjectiveRoots.lean), [`ETR.TubeCharacteristicRoots`](LeanCanny/ETR/TubeCharacteristicRoots.lean) | Every nonzero common homogeneous root over a domain annihilates the polynomial quotient, including roots in extension domains and specializations with zero extraneous determinant. A binomial root-preserving model has a triangular extraneous matrix with nonzero diagonal; polynomial deformation and universal ordering transport cover every projective chart. The actual tube characteristic polynomial vanishes at every shifted common-root parameter, and its constant coefficient vanishes at every original tube common root. The converse over algebraically closed fields is proved below; multivariate-resultant identification remains open. |
| [`Algebra.ProjectiveNullstellensatz`](LeanCanny/Algebra/ProjectiveNullstellensatz.lean), [`HomogeneousIdealMembership`](LeanCanny/Algebra/HomogeneousIdealMembership.lean), [`MacaulayIdealImage`](LeanCanny/Algebra/MacaulayIdealImage.lean), [`MacaulayNullstellensatz`](LeanCanny/Algebra/MacaulayNullstellensatz.lean) | Over an algebraically closed field, no nonzero common root is equivalent to the generated ideal containing coordinate powers, a power of the variable ideal, or every form of some degree. Homogeneous ideal expressions have homogeneous multipliers; over any commutative ring the full Macaulay row image equals the degree-level part of the ideal. A nonzero polynomial quotient supplies qualitative ideal-power and homogeneous Bezout certificates. The sharp Macaulay degree bound is proved below. |
| [`Algebra.MatrixSelectedMinorCross`](LeanCanny/Algebra/MatrixSelectedMinorCross.lean), [`MacaulayHigherDenominators`](LeanCanny/Algebra/MacaulayHigherDenominators.lean), [`MacaulayFullPermutation`](LeanCanny/Algebra/MacaulayFullPermutation.lean), [`MacaulayMinorCross`](LeanCanny/Algebra/MacaulayMinorCross.lean), [`MacaulayMaximalMinors`](LeanCanny/Algebra/MacaulayMaximalMinors.lean) | Selected-row factorization and the matrix determinant lemma give arbitrary-minor cross identities. The higher relation factors omit the last coefficient group and specialize to one. Transport across orderings and polynomial cancellation prove that the normalized quotient divides every maximal minor of the full Macaulay matrix, over any commutative ring after specialization. |
| [`Algebra.MatrixMaximalMinorSpan`](LeanCanny/Algebra/MatrixMaximalMinorSpan.lean), [`MacaulayQuotientSurjectivity`](LeanCanny/Algebra/MacaulayQuotientSurjectivity.lean), [`ETR.TubeCharacteristicSurjectivity`](LeanCanny/ETR/TubeCharacteristicSurjectivity.lean) | Surjectivity of the full Macaulay row map makes the polynomial quotient a unit over any commutative ring. Over a nontrivial ring it is nonzero, even when the extraneous determinant vanishes. The same conclusion follows from ideal membership of every form at the Macaulay level. For the actual tube polynomial, specialized full-matrix surjectivity makes its specialized constant coefficient a unit. The sharp degree bound and common-root converse over algebraically closed fields are proved below. |
| [`Algebra.CoordinatePowerRegularity`](LeanCanny/Algebra/CoordinatePowerRegularity.lean), [`ProjectiveRegularSequence`](LeanCanny/Algebra/ProjectiveRegularSequence.lean), [`ProjectiveDepth`](LeanCanny/Algebra/ProjectiveDepth.lean) | Positive powers of distinct variables form a regular sequence over any nontrivial commutative coefficient ring. No nonzero common root over an algebraically closed field gives an ambient regular sequence of length equal to the number of variables inside the input ideal. For positive homogeneous inputs, Rees' theorem then gives Ext vanishing below that length for finite modules supported on the input ideal's zero locus, including its quotient ring. This does not prove regularity of the original input forms. |
| [`Algebra.KoszulIdealAnnihilator`](LeanCanny/Algebra/KoszulIdealAnnihilator.lean), [`FiniteComplexSurjectivity`](LeanCanny/Algebra/FiniteComplexSurjectivity.lean), [`KoszulExactSurjectivity`](LeanCanny/Algebra/KoszulExactSurjectivity.lean) | The input ideal sends positive Koszul cycles to boundaries. Finite exact complexes on the same graded vector spaces have equal differential ranks. Comparing the actual weighted complex with coordinate powers proves that positive-degree exactness at the Macaulay level implies full-matrix surjectivity and a unit quotient. The acyclicity argument and weighted exactness from absence of projective roots are proved below. |
| [`Algebra.ExtVanishing`](LeanCanny/Algebra/ExtVanishing.lean), [`HomologySupport`](LeanCanny/Algebra/HomologySupport.lean), [`FiniteComplexAcyclicity`](LeanCanny/Algebra/FiniteComplexAcyclicity.lean), [`KoszulProjectiveExact`](LeanCanny/Algebra/KoszulProjectiveExact.lean) | Ext vanishing into a ring extends to finite free targets. The input ideal annihilates finite positive Koszul homology. Descending dimension shifting along the cokernels then proves positive Koszul exactness for as many positive homogeneous inputs as variables over an algebraically closed field, when their only common root is zero. |
| [`Algebra.KoszulWeightProjection`](LeanCanny/Algebra/KoszulWeightProjection.lean), [`KoszulWeightedExact`](LeanCanny/Algebra/KoszulWeightedExact.lean), [`MacaulayProjectiveCriterion`](LeanCanny/Algebra/MacaulayProjectiveCriterion.lean), [`ETR.TubeCharacteristicCriterion`](LeanCanny/ETR/TubeCharacteristicCriterion.lean) | Projection onto a total weight commutes with the homogeneous differential and transfers exactness to every finite weighted piece. This proves the sharp ideal-membership degree `1+Σᵢ(dᵢ−1)`. Over an algebraically closed field the polynomial quotient vanishes exactly at systems with a nonzero common root, including singular extraneous matrices. The actual tube characteristic polynomial has the corresponding shifted-root equivalence, and its constant coefficient detects unshifted common roots. Resultant identification, general proper-component persistence, and the remaining full ETR space bounds remain open. |
| [`Geometry.ImplicitRootPersistence`](LeanCanny/Geometry/ImplicitRootPersistence.lean), [`ParametricPolynomialCalculus`](LeanCanny/Geometry/ParametricPolynomialCalculus.lean), [`MacaulayRegularPersistence`](LeanCanny/Geometry/MacaulayRegularPersistence.lean), [`ETR.TubeCharacteristicRegularPersistence`](LeanCanny/ETR/TubeCharacteristicRegularPersistence.lean) | At a root with invertible square-system Jacobian, the implicit function theorem constructs continuous characteristic-shifted roots over the reals or complexes. Their quotient vanishing forces its lowest coefficient to vanish at the original projection parameter. The actual tube chart supplies the coefficient maps and smoothness proofs. The general singular proper-component case remains open. |
| [`Algebra.CharacteristicCoefficientDegree`](LeanCanny/Algebra/CharacteristicCoefficientDegree.lean), [`ETR.TubeCharacteristicLowestSpecialization`](LeanCanny/ETR/TubeCharacteristicLowestSpecialization.lean), [`TubeCharacteristicLowestBounds`](LeanCanny/ETR/TubeCharacteristicLowestBounds.lean) | The lowest quotient coefficient divides the lowest full characteristic coefficient. The existing FP dyadic exponent therefore gives an interval where its real perturbation specialization is nonzero and preserves the quotient's lowest order and coefficient. The resulting projection polynomial has degree at most the padded Macaulay dimension and covers every affine root with invertible full-system Jacobian; the same bound counts their distinct projection values. Coverage for finite affine fibers, including singular roots, is proved below. |
| [`Algebra.FiniteZeroLocus`](LeanCanny/Algebra/FiniteZeroLocus.lean), [`MvPolynomialPointHeight`](LeanCanny/Algebra/MvPolynomialPointHeight.lean), [`FiniteFiberSaturation`](LeanCanny/Algebra/FiniteFiberSaturation.lean), [`FiniteFiberLowestCoefficient`](LeanCanny/Algebra/FiniteFiberLowestCoefficient.lean) | Point ideals in `n` variables have height `n`. Krull's height theorem rules out vertical minimal components in a finite zero fiber of `n` equations in `n+1` variables. Deformation powers can therefore be cancelled in the radical ideal, proving lowest-coefficient vanishing on the entire finite fiber, including singular points. No analytic root curve is assumed or constructed. |
| [`Algebra.MacaulayFiniteFiber`](LeanCanny/Algebra/MacaulayFiniteFiber.lean), [`ETR.TubeCharacteristicFinitePersistence`](LeanCanny/ETR/TubeCharacteristicFinitePersistence.lean), [`TubeCharacteristicFiniteBounds`](LeanCanny/ETR/TubeCharacteristicFiniteBounds.lean) | The lowest quotient coefficient vanishes at every root of a finite affine system over an algebraically closed field; infinitely many projective roots at infinity are allowed. The actual tube specialization also covers all real affine roots when the affine fiber is finite over an algebraically closed extension of the reals. On the certified perturbation interval the nonzero projection polynomial bounds all their projection values by the padded matrix dimension, including singular roots. The geometric-to-compiled finiteness bridge is proved below. Effective parameter selection and the remaining proper components stay open. |
| [`Geometry.UniformExtendedProjectionDirections`](LeanCanny/Geometry/UniformExtendedProjectionDirections.lean), [`TubeUniformExtendedDirections`](LeanCanny/Geometry/TubeUniformExtendedDirections.lean), [`ETR.TubeRegularFiber`](LeanCanny/ETR/TubeRegularFiber.lean), [`TubeCompiledAffineRoots`](LeanCanny/ETR/TubeCompiledAffineRoots.lean), [`TubeCharacteristicGeometricPersistence`](LeanCanny/ETR/TubeCharacteristicGeometricPersistence.lean) | One nearby rational direction gives finite extended critical fibers for all active tubes on a common small-level interval, over every extension field of the reals. With nonzero substitution denominators and explicit parameter identities, these fibers give finite compiled affine zero sets; the lowest quotient coefficient then vanishes at every root over an algebraically closed field. No Jacobian invertibility is required. Concrete constant-parameter readers are supplied below; selecting suitable tuples with source-size bounds remains open. |
| [`ETR.TubeLevelPacket`](LeanCanny/ETR/TubeLevelPacket.lean), [`TubeLevelReaders`](LeanCanny/ETR/TubeLevelReaders.lean), [`TubeLevelParameters`](LeanCanny/ETR/TubeLevelParameters.lean), [`TubeLevelPacking`](LeanCanny/ETR/TubeLevelPacking.lean), [`TubeLevelFiniteFiber`](LeanCanny/ETR/TubeLevelFiniteFiber.lean) | A concrete packet stores rational epsilon, delta, and direction coordinates, with alpha as the variable. Positive constant denominators never vanish in characteristic zero; coordinate degrees are at most one and coefficients are bounded by `2^(W+1)` for the stored width W. Uniform FP modular coefficient readers and FP degree/bit bounds instantiate the regular-system substitution interfaces on all packets. Parameter identities hold over every real extension. Every rational tuple packs exactly with a width derived from its component bit lengths. A finite geometric critical fiber therefore gives a finite compiled fiber without separate denominator or parameter-identity hypotheses. Selecting a suitable tuple with source-size bounds remains open. |
| [`ETR.TubeLevelTuple`](LeanCanny/ETR/TubeLevelTuple.lean), [`TubeLevelChoice`](LeanCanny/ETR/TubeLevelChoice.lean), [`TubeLevelSampling`](LeanCanny/ETR/TubeLevelSampling.lean), [`TubeLevelSamplingSource`](LeanCanny/ETR/TubeLevelSamplingSource.lean) | Prescribed rational perturbations and direction coordinates pack exactly. A combined coordinate bit allowance B gives packet length at most `2*source.length + (5*parameterCount+2)*B + 8`. One packet stores a nearby normalized rational direction and gives finite compiled fibers for all active sets throughout a common positive level interval, over every real extension, and preserves positive-inactive critical samples. ETR is equivalent to the existence of a positive rational margin such that every positive rational radius admits these packet samples. This remains a qualitative criterion: source-size bounds for suitable choices and effective search remain open. Compiled sample lifts and nonzero eliminant coverage are supplied below. |
| [`ETR.TubeRegularSpatialLift`](LeanCanny/ETR/TubeRegularSpatialLift.lean), [`TubeCompiledAffineLift`](LeanCanny/ETR/TubeCompiledAffineLift.lean), [`TubeLevelRootLift`](LeanCanny/ETR/TubeLevelRootLift.lean) | A nonzero base derivative supplies the reciprocal coordinate; regular real hypersurface projection roots have that nonvanishing. Adding the prescribed linear projection gives actual compiled affine roots, and decoding preserves the original sample coordinates. One common small-level interval works for every active set and added linear projection. No full critical-system Jacobian hypothesis is imposed. |
| [`ETR.TubeLevelCompiledSampling`](LeanCanny/ETR/TubeLevelCompiledSampling.lean), [`TubeLevelEliminantSampling`](LeanCanny/ETR/TubeLevelEliminantSampling.lean) | ETR is equivalent to stored rational packets with actual compiled samples and positive inactive signs, finite fibers over all real extensions, and nonzero lowest-coefficient eliminants annihilating their projection values. The packet and active mask are fixed; the nonvanishing interval may depend on the added integer linear projection. An explicit dyadic threshold and padded-matrix degree bound also bound all distinct compiled projection values, including singular roots. Source-size parameter bounds, effective selection, and effective coordinate recovery remain open. The qualitative rational-level decoding is supplied below. |
| [`ETR.TubeFiniteSystemBaseChange`](LeanCanny/ETR/TubeFiniteSystemBaseChange.lean), [`TubeLevelCoordinates`](LeanCanny/ETR/TubeLevelCoordinates.lean) | At every rational level with finite compiled fibers, the actual rational system has an integer univariate representation complete over the reals. Nonzero integer parameter polynomials and rational coordinate formulas, with denominators nonzero at parameter roots, recover every compiled point. ETR is equivalent to these decoded samples with positive inactive signs at sufficiently small rational levels. The representation is existential and may vary with the level and linear projection; its coefficient-height bounds, effective construction, and relation to the computed lowest-coefficient eliminant remain open. Source-derived degree bounds at common small levels appear below. |
| [`ETR.TubeLevelSignQueries`](LeanCanny/ETR/TubeLevelSignQueries.lean), [`TubeLevelSignSpace`](LeanCanny/ETR/TubeLevelSignSpace.lean) | Positive rational-margin clearing and even coordinate-denominator powers give integer univariate queries for the actual inactive constraints. Active queries are one. A positive finite root-sign count is equivalent to a compiled sample. ETR is equivalent to these positive counts throughout small rational-level intervals. The existing native counter computes this count and decides sample existence under explicit coefficient-reader, degree/mass-budget, and control certificates. Constructing suitably bounded coordinate representations and their coefficient readers from the original input remains open. |
| [`Algebra.RationalSubstitutionWith`](LeanCanny/Algebra/RationalSubstitutionWith.lean), [`ETR.TubeLevelSignBounds`](LeanCanny/ETR/TubeLevelSignBounds.lean) | Fixed denominator-clearing allowances preserve evaluations and give uniform output budgets. Actual tube sign queries use raw stored margin integers and the source-size allowance `D=8*N^2+4`. With `Q=2*A*D`, coordinate degree E and coordinate mass at most `2^b` give query degree at most `Q*E` and mass at most `2^(W+N+2*N^2+4+Q*b)`. FP binary writers derive the native sign-stage budgets from coordinate bounds; separate query-bound assumptions are unnecessary. Effective coordinate construction and coefficient readers remain open. |
| [`Algebra.FixedWidthMonomial`](LeanCanny/Algebra/FixedWidthMonomial.lean), [`ModularResidueSpace`](LeanCanny/Algebra/ModularResidueSpace.lean), [`ETR.TubeSampleCoefficient`](LeanCanny/ETR/TubeSampleCoefficient.lean), [`TubeSparseConstraintCoefficient`](LeanCanny/ETR/TubeSparseConstraintCoefficient.lean), [`TubeConstraintCoefficientSource`](LeanCanny/ETR/TubeConstraintCoefficientSource.lean) | Native coefficient residues of the actual integer inactive-constraint polynomials. The dense compact source uses a guarded coordinate restriction; point, shift, and constant coefficients are FP checks. Native modular composition includes all dense-child workspace and the raw margin residues. Binary row selection is total and exact on valid indices. No constraint-coefficient oracle is assumed. Rational coordinate substitution and sign-counter integration are described below; constructing bounded coordinate representations remains open. |
| [`ETR.TubeConstraintIndexed`](LeanCanny/ETR/TubeConstraintIndexed.lean), [`TubeConstraintSubstitution`](LeanCanny/ETR/TubeConstraintSubstitution.lean), [`TubeLevelSignNative`](LeanCanny/ETR/TubeLevelSignNative.lean) | Binary rank access and native rational substitution compute the actual integer constraints' cleared coefficients. FP active-mask lookup supplies the complete sign-query reader. Root/coordinate coefficient readers and coordinate budgets suffice for native sample counting and sample-existence PSPACE membership; expanded sign-query coefficient access is derived internally. Effective bounded coordinate construction remains open. |
| [`ETR.TubeCompiledReprojection`](LeanCanny/ETR/TubeCompiledReprojection.lean), [`TubeCompiledCardinality`](LeanCanny/ETR/TubeCompiledCardinality.lean), [`TubeLevelDegreeBounds`](LeanCanny/ETR/TubeLevelDegreeBounds.lean) | Changing the added projection gives a bijection of full affine root sets. Coordinate eliminants bound all complex/algebraic-closure solutions, including singular roots. With A compiled coordinates, T=A-1 spatial coordinates, and matrix width W, the count is at most `B=(2^W)^(A*T)`. At a common FP-coded small-level threshold, every integer coordinate representation has parameter degree at most B and coordinate degrees at most `B^2+2`. Native sample counting derives all degree controls from the source; mass bounds and coefficient readers remain supplied. |
| [`Algebra.MacaulayExtraneousLast`](LeanCanny/Algebra/MacaulayExtraneousLast.lean), [`MacaulayLastParameter`](LeanCanny/Algebra/MacaulayLastParameter.lean) | No extraneous row uses the last polynomial. If only that input varies with a coefficient parameter `u`, the characteristic quotient is a nonzero polynomial in `u` over `K(s)`. A faithful variable-swap map connects this polynomial to the original determinant quotient. Polynomiality in the characteristic parameter `s` is proved below; resultant identification remains open. |
| [`Algebra.MacaulayPivotCount`](LeanCanny/Algebra/MacaulayPivotCount.lean), [`MacaulayLastParameterDegree`](LeanCanny/Algebra/MacaulayLastParameterDegree.lean) | Exactly `∏ⱼ≠last dⱼ` active rows use the last input. If its coefficients have parameter degree at most `E` and all other inputs are constant, the quotient polynomial over `K(s)` has degree at most `E*∏ⱼ≠last dⱼ`. The affine family `f_last+u*h` realizes `E=1` and preserves homogeneity when the variation has the specified degree. |
| [`Algebra.MacaulayMultiplicationMatrix`](LeanCanny/Algebra/MacaulayMultiplicationMatrix.lean) | The full graded rectangular matrix indexes all degree-compatible monomial multiples of every input. An injective row selector recovers the true square Macaulay matrix. Finite coefficient reconstruction identifies row combinations with polynomial multiplication; homogeneous inputs give homogeneous level rows. |
| [`Algebra.MacaulayKoszulRelations`](LeanCanny/Algebra/MacaulayKoszulRelations.lean), [`MacaulayShiftedKoszul`](LeanCanny/Algebra/MacaulayShiftedKoszul.lean), [`ETR.TubeMacaulayKoszul`](LeanCanny/ETR/TubeMacaulayKoszul.lean) | The commutativity relations `m*fⱼ*fᵢ-m*fᵢ*fⱼ=0` give finite kernel vectors of the full rectangular matrix. Over an integral domain, compatible shifted inputs give nonzero vectors; an explicit compatible pair is proved for the actual tube system without extra algebraic hypotheses. Generic kernel spanning, higher weighted exactness, and polynomial cancellation are proved below; resultant identification remains open. |
| [`Algebra.MatrixMinorSection`](LeanCanny/Algebra/MatrixMinorSection.lean), [`MacaulayGenericShift`](LeanCanny/Algebra/MacaulayGenericShift.lean), [`ETR.TubeMacaulayGenericShift`](LeanCanny/ETR/TubeMacaulayGenericShift.lean) | Over the rational-function field in the characteristic parameter, an explicit section proves surjectivity of the full shifted multiplication matrix. Every homogeneous polynomial at the Macaulay level belongs to the shifted ideal, which contains that power of the variable ideal. Any common zero over an integral-domain coefficient extension is the origin. These results apply to the actual tube system; the section has no space bound. |
| [`Algebra.MacaulayMonomialDivision`](LeanCanny/Algebra/MacaulayMonomialDivision.lean), [`MatrixKernelContraction`](LeanCanny/Algebra/MatrixKernelContraction.lean), [`MacaulayKoszulContraction`](LeanCanny/Algebra/MacaulayKoszulContraction.lean), [`ETR.TubeMacaulayKoszulExact`](LeanCanny/ETR/TubeMacaulayKoszulExact.lean) | Monomial division gives a coordinate-power Koszul contraction over any commutative ring. Two characteristic determinants transport it to the generic shifted system over `RatFunc R`: at the Macaulay level, the full multiplication matrix's kernel equals the span of all degree-compatible Koszul relations. A finite pivot family generates this kernel, including for the actual tube rows. Higher weighted exactness and polynomial cancellation are proved below; space bounds for the contraction remain open. |
| [`Algebra.MatrixSelectedBlock`](LeanCanny/Algebra/MatrixSelectedBlock.lean), [`MacaulayRelationMinor`](LeanCanny/Algebra/MacaulayRelationMinor.lean), [`ETR.TubeMacaulayKernelBasis`](LeanCanny/ETR/TubeMacaulayKernelBasis.lean) | Removing the zero selected relation rows gives a basis of the generic shifted kernel, with unique coordinates, including for the tube system. The complementary relation minor is the identity for coordinate powers and shifts by `-sI`. Block triangularity factors the source-contraction determinant, and its characteristic determinant, into the selected Macaulay and complementary relation determinants. This complementary block is not identified with the extraneous minor; polynomial cancellation is proved below; resultant identification and space bounds remain open. |
| [`Algebra.MacaulayRelationBlocks`](LeanCanny/Algebra/MacaulayRelationBlocks.lean), [`MacaulayRelationBlockEquiv`](LeanCanny/Algebra/MacaulayRelationBlockEquiv.lean), [`MacaulayRelationExtraneous`](LeanCanny/Algebra/MacaulayRelationExtraneous.lean), [`ETR.TubeMacaulayRelationFactor`](LeanCanny/ETR/TubeMacaulayRelationFactor.lean) | Two triangular decompositions and a monomial-division bijection identify the extraneous diagonal blocks inside the relation determinant. The extraneous determinant divides the relation determinant, with an explicit product of remaining blocks as factor, over any commutative ring. The characteristic version has a nonzero remaining polynomial over an integral domain and applies to the actual tube system. Divisibility of the Macaulay numerator by the extraneous determinant is proved below. |
| [`Algebra.KoszulExterior`](LeanCanny/Algebra/KoszulExterior.lean), [`KoszulComplex`](LeanCanny/Algebra/KoszulComplex.lean), [`MacaulayKoszulExteriorBridge`](LeanCanny/Algebra/MacaulayKoszulExteriorBridge.lean) | Exterior contraction defines the all-degree Koszul differential and a Mathlib chain complex. A unit combination gives a contracting homotopy, exactness in every positive exterior degree, and a surjective degree-zero map. Polynomial multiplication is its degree-one differential; compatible finite Macaulay kernels and the earlier monomial Koszul boundaries agree with this exterior construction. |
| [`Algebra.MacaulayLocalizedKoszul`](LeanCanny/Algebra/MacaulayLocalizedKoszul.lean), [`ETR.TubeMacaulayLocalizedKoszul`](LeanCanny/ETR/TubeMacaulayLocalizedKoszul.lean) | The proved generic ideal-power certificates give a unit combination after inverting any spatial coordinate. On each coordinate chart, the generic shifted Koszul complex is therefore exact in every exterior degree, with a contracting homotopy; this applies to the actual tube system without new reader or algebraic certificates. Higher exactness in the finite weighted Macaulay grade and polynomial cancellation are proved below; resultant identification remains open. |
| [`Algebra.KoszulWeightedSpace`](LeanCanny/Algebra/KoszulWeightedSpace.lean), [`KoszulWeightedComplex`](LeanCanny/Algebra/KoszulWeightedComplex.lean), [`KoszulWeightedMatrix`](LeanCanny/Algebra/KoszulWeightedMatrix.lean) | Monomial degree plus the input-degree sum in each exterior word defines finite weighted pieces. Sufficient exponent widths give the same space, and degree `k>n` gives zero. Homogeneous inputs preserve weight and form a finite Koszul chain complex. Over a field, chosen finite bases give row-vector matrices with zero consecutive products and dimension bound `n^k*(2^W)^n`. No entry-reader bound is claimed for these chosen bases. |
| [`Algebra.MacaulayWeightedBridge`](LeanCanny/Algebra/MacaulayWeightedBridge.lean), [`ETR.TubeMacaulayWeightedKoszul`](LeanCanny/ETR/TubeMacaulayWeightedKoszul.lean) | The first weighted differential on the canonical multiplier generators is the scalar image of the existing polynomial rows. Scalar retraction and coefficient queries recover every full Macaulay matrix entry. The finite weighted complex, arity bound, dimension bound, and square-zero matrices are instantiated for the actual generic shifted tube system. Higher exactness of this finite complex and polynomial cancellation are proved below; resultant identification remains open. |
| [`Algebra.KoszulWeightedBasis`](LeanCanny/Algebra/KoszulWeightedBasis.lean), [`KoszulCanonicalMatrix`](LeanCanny/Algebra/KoszulCanonicalMatrix.lean), [`MacaulayCanonicalMatrix`](LeanCanny/Algebra/MacaulayCanonicalMatrix.lean), [`ETR.TubeMacaulayCanonicalKoszul`](LeanCanny/ETR/TubeMacaulayCanonicalKoszul.lean) | Monomials and ordered subsets give bases of every weighted piece over any commutative coefficient ring. Coordinates are polynomial coefficients in the exterior basis. The resulting matrices have zero consecutive products; bijective index maps identify the entire first matrix with the full Macaulay matrix. The bases and matrices are instantiated for the shifted tube. Resource-bounded entry readers remain open. |
| [`Algebra.KoszulWeightedContraction`](LeanCanny/Algebra/KoszulWeightedContraction.lean), [`KoszulWeightedContractionMatrix`](LeanCanny/Algebra/KoszulWeightedContractionMatrix.lean), [`ETR.TubeMacaulayPowerKoszul`](LeanCanny/ETR/TubeMacaulayPowerKoszul.lean) | For the coordinate-power system, a multidegree-dependent polynomial homotopy contracts the finite weighted complex at the Macaulay level over any commutative coefficient ring. It proves exactness in every positive degree, surjectivity in degree zero, and canonical matrix identities `H D + D H = 1`. This applies to the tube's degrees and finite pieces. The generic shifted transfer is proved below. |
| [`Algebra.KoszulGenericContraction`](LeanCanny/Algebra/KoszulGenericContraction.lean), [`KoszulGenericExact`](LeanCanny/Algebra/KoszulGenericExact.lean), [`KoszulGenericZero`](LeanCanny/Algebra/KoszulGenericZero.lean), [`ETR.TubeMacaulayGenericKoszul`](LeanCanny/ETR/TubeMacaulayGenericKoszul.lean) | Canonical differential and homotopy matrices commute with coefficient maps. The generic shifted homotopy operator is a characteristic pencil with nonzero determinant. Finite-dimensional kernel invariance proves exactness in every positive exterior degree at the Macaulay weight; full Macaulay surjectivity gives degree zero. Both results hold for the actual shifted tube without additional algebraic certificates. Polynomial cancellation is proved below; resultant identification and resource bounds remain open. |
| [`Algebra.KoszulHomotopyNormalization`](LeanCanny/Algebra/KoszulHomotopyNormalization.lean), [`KoszulHomotopySplit`](LeanCanny/Algebra/KoszulHomotopySplit.lean), [`MacaulayHomotopyDeterminant`](LeanCanny/Algebra/MacaulayHomotopyDeterminant.lean), [`ETR.TubeMacaulayHomotopyDeterminant`](LeanCanny/ETR/TubeMacaulayHomotopyDeterminant.lean) | The polynomial homotopy squares to zero and gives a fixed complementary splitting with the pure-power differential. Every homogeneous-input homotopy operator preserves the incoming homotopy image. The first two homotopy operations recover the existing Macaulay row selector and relation matrix, so the finite degree-one operator has the proved active, extraneous, and higher-relation determinant factors, including for the tube. Numerator/extraneous cancellation is proved below. |
| [`Algebra.KoszulSpecializationExact`](LeanCanny/Algebra/KoszulSpecializationExact.lean), [`MacaulayUniversalExact`](LeanCanny/Algebra/MacaulayUniversalExact.lean), [`KoszulPivotBasis`](LeanCanny/Algebra/KoszulPivotBasis.lean), [`KoszulPivotContraction`](LeanCanny/Algebra/KoszulPivotContraction.lean) | Coordinate-power specialization proves exactness of the unshifted universal finite complex over its coefficient fraction field, including degree-zero surjectivity, for every ordering. Over any commutative ring, pivot-containing monomial basis vectors span exactly the incoming homotopy image and the remaining vectors give a complement, with explicit bases. The contraction determinant factors into these two principal blocks in every positive degree; both universal blocks have nonzero determinants. The higher Macaulay factors are identified below; ordering comparisons are proved below. |
| [`Algebra.KoszulPivotEquiv`](LeanCanny/Algebra/KoszulPivotEquiv.lean), [`KoszulAdjacentBlocks`](LeanCanny/Algebra/KoszulAdjacentBlocks.lean), [`MacaulayPivotBoundary`](LeanCanny/Algebra/MacaulayPivotBoundary.lean) | The homotopy identifies each nonpivot summand with the next pivot summand and conjugates their contraction operators. Adjacent principal blocks therefore have equal determinants over any commutative ring. The initial pivot determinant is the active Macaulay numerator; explicit reindexing identifies the first nonpivot block with the complementary relation minor, so the next pivot determinant has the known extraneous and higher-relation factors. Higher factor identification is proved below; ordering comparisons are proved below. |
| [`Algebra.KoszulNonpivotRows`](LeanCanny/Algebra/KoszulNonpivotRows.lean), [`KoszulNonpivotMacaulay`](LeanCanny/Algebra/KoszulNonpivotMacaulay.lean), [`KoszulNonpivotBlocks`](LeanCanny/Algebra/KoszulNonpivotBlocks.lean), [`KoszulSubsetDeterminant`](LeanCanny/Algebra/KoszulSubsetDeterminant.lean) | In every positive degree, the projected nonpivot contraction is triangular by the least exterior coordinate, with diagonal blocks separated by exterior subset. Its determinant is the product of one concrete active-Macaulay principal submatrix determinant for each exterior subset; the monomial index maps are injective. Adjacent conjugacy gives the same factorization for the next pivot block over any commutative ring. Full position-mask determinant factors are identified below; ordering comparisons and cancellation are proved below. |
| [`Algebra.KoszulEligibleIndices`](LeanCanny/Algebra/KoszulEligibleIndices.lean), [`FinitePositionMasks`](LeanCanny/Algebra/FinitePositionMasks.lean), [`KoszulEligiblePositions`](LeanCanny/Algebra/KoszulEligiblePositions.lean), [`MacaulayEligibleMonotonic`](LeanCanny/Algebra/MacaulayEligibleMonotonic.lean), [`MacaulayEligibilityLevels`](LeanCanny/Algebra/MacaulayEligibilityLevels.lean) | Exact monomial-index equivalences give decreasing eligible-position masks and binomial counts for each greatest-position stratum. Nonzero Macaulay entries preserve eligible coordinates apart from the source pivot, proving triangularity of fixed-subset factors by greatest selected position. Higher eligibility minors recover the active and extraneous determinants at levels one and two, are characteristic pencils under the standard shift, and specialize to one universally. The full-mask comparison and binomial determinant-power formula are proved below. |
| [`Algebra.MatrixWeightBlockProduct`](LeanCanny/Algebra/MatrixWeightBlockProduct.lean), [`MacaulayFullPositionMasks`](LeanCanny/Algebra/MacaulayFullPositionMasks.lean), [`FinitePositionSelection`](LeanCanny/Algebra/FinitePositionSelection.lean), [`MacaulayMaskedLevelIndices`](LeanCanny/Algebra/MacaulayMaskedLevelIndices.lean), [`MacaulayFullMaskComparison`](LeanCanny/Algebra/MacaulayFullMaskComparison.lean), [`FinitePositionMaskProduct`](LeanCanny/Algebra/FinitePositionMaskProduct.lean), [`MacaulayBinomialFactors`](LeanCanny/Algebra/MacaulayBinomialFactors.lean) | Full-mask triangularity and exact encoding/decoding identify each mask factor with a higher eligibility minor. Grouping by greatest position proves `det(Q_k) = det(P_(k+1)) = product_j det(W_(j+2))^choose(j,k)` over any commutative ring, including empty blocks. The first relation determinant is the product of these higher minors. Ordering comparisons and numerator/extraneous cancellation are proved below; resultant identification remains open. |
| [`Algebra.KoszulPowerComparison`](LeanCanny/Algebra/KoszulPowerComparison.lean), [`KoszulPowerComparisonSpecialization`](LeanCanny/Algebra/KoszulPowerComparisonSpecialization.lean), [`BinomialParityProducts`](LeanCanny/Algebra/BinomialParityProducts.lean), [`MacaulayAlternatingFactors`](LeanCanny/Algebra/MacaulayAlternatingFactors.lean), [`KoszulComparisonRatio`](LeanCanny/Algebra/KoszulComparisonRatio.lean), [`MacaulayUniversalComparison`](LeanCanny/Algebra/MacaulayUniversalComparison.lean) | The explicit map `F = D H + H D_power` intertwines the coordinate-power and input differentials. Its determinants are the active numerator in degree zero and the nonpivot factors in positive degrees. It gives linear equivalences in every degree over the universal coefficient fraction field. Alternating binomial cancellation identifies its determinant quotient with the actual numerator/extraneous ratio. Equality of these constructed ratios is proved equivalent to the required polynomial cross-comparison; ordering invariance and polynomial cancellation are proved below. |
| [`Algebra.ExactComplexDeterminant`](LeanCanny/Algebra/ExactComplexDeterminant.lean), [`ExactComplexComparison`](LeanCanny/Algebra/ExactComplexComparison.lean), [`ExactComplexTransport`](LeanCanny/Algebra/ExactComplexTransport.lean), [`MacaulayUniversalTransport`](LeanCanny/Algebra/MacaulayUniversalTransport.lean) | Kernel/range determinant factors telescope in a finite exact complex, giving equal even and odd determinant products. Degreewise chain equivalences therefore have an invariant alternating determinant ratio, preserved by simultaneous transport of both differentials. The weighted Koszul instantiation turns such a transport into the actual universal numerator/denominator cross-comparison. The input/spatial transport and polynomial cancellation are proved below; resultant identification remains open. |
| [`Algebra.GroupedDenominatorCancellation`](LeanCanny/Algebra/GroupedDenominatorCancellation.lean), [`MacaulayUniversalDenominators`](LeanCanny/Algebra/MacaulayUniversalDenominators.lean), [`MacaulayUniversalSpecialization`](LeanCanny/Algebra/MacaulayUniversalSpecialization.lean), [`ETR.TubeMacaulayUniversal`](LeanCanny/ETR/TubeMacaulayUniversal.lean) | Explicit universal extraneous determinants omit each coefficient group in turn and all specialize to one at the coordinate-power system. Every common divisor is therefore a unit. Over a UFD, cross-comparison identities for the actual universal numerator/denominator pairs are equivalent to a unique normalized polynomial quotient. Specialization reconstructs the actual tube characteristic determinants. The cross-comparisons and cancellation are proved below, including a unique polynomial quotient for the actual tube characteristic determinants. |
| [`Algebra.KoszulWeightedPermutation`](LeanCanny/Algebra/KoszulWeightedPermutation.lean), [`MacaulayUniversalOrdering`](LeanCanny/Algebra/MacaulayUniversalOrdering.lean), [`MacaulayUniversalCancellation`](LeanCanny/Algebra/MacaulayUniversalCancellation.lean), [`MacaulayPolynomialCancellation`](LeanCanny/Algebra/MacaulayPolynomialCancellation.lean) | Explicit spatial/exterior permutation equivalences intertwine both differentials and prove all universal ordering cross-comparisons. The universal quotient is a unique normalized polynomial over a UFD. Extending the integer identity and specializing proves extraneous-determinant divisibility of the numerator over any commutative ring, including the characteristic pencils and actual tube system. Resultant identification and the remaining algorithmic bounds remain open. |
| [`Algebra.FiniteDenominatorClearing`](LeanCanny/Algebra/FiniteDenominatorClearing.lean), [`RationalPolynomialClearing`](LeanCanny/Algebra/RationalPolynomialClearing.lean), [`BoundedIntegerCoordinates`](LeanCanny/Algebra/BoundedIntegerCoordinates.lean) | Explicit common-denominator products preserve rational polynomial degrees and values. A representation in n coordinates with degree cap D and rational component bit bound B gets integer coefficient and scale budget `B*((2*n+1)*(D+1))+1`. The conversion uses no chosen localization scale. |
| [`Algebra.DenominatorClearingSpace`](LeanCanny/Algebra/DenominatorClearingSpace.lean), [`DenominatorClearingSign`](LeanCanny/Algebra/DenominatorClearingSign.lean) | Streamed normalized coefficient residues use a product omitting the selected denominator, with no modular inverses. FP binary bounds/counts and space-certified canonical rational component residues give three-way signs and PSPACE zero/strict-sign tests, including all child costs. Instantiating the rational source from multivariate input remains open. |
| [`Algebra.GaloisDescent`](LeanCanny/Algebra/GaloisDescent.lean) | For finite point sets stable under a finite Galois group, the nodal polynomial and coordinate interpolants descend to the input field. The nodal polynomial is monic and separable, with exactly the projected points as roots. |
| [`Algebra.PrimitiveCoordinates`](LeanCanny/Algebra/PrimitiveCoordinates.lean) | The algebraic existence part of Lemma 2.1: two square-free polynomials of degrees `d₁,d₂` over a characteristic-zero field have a monic separable degree-`d₁*d₂` representation, with coordinate polynomials over that same field. A common finite Galois splitting field is supplied; `c ≤ (d₁*d₂)^2`. |
| [`Algebra.GCDRecovery`](LeanCanny/Algebra/GCDRecovery.lean) | At `θ = a+c*b`, the GCD of `p₁(θ-c*x)` and `p₂(x)` is linear. Its coefficients recover `b = -g₀/g₁` and `a = θ+c*g₀/g₁`, with `g₁ ≠ 0`. The hypotheses include separability, splitting, and a separating direction. |
| [`Algebra.PrimitiveResultant`](LeanCanny/Algebra/PrimitiveResultant.lean), [`ResultantFactorization`](LeanCanny/Algebra/ResultantFactorization.lean) | The parameter polynomial is defined by a fixed-degree Sylvester determinant. Specialization, its exact roots, its leading-coefficient factor, and degree `d₁*d₂` are proved. Scalar normalization gives a monic polynomial; the sign from swapping the inputs is tracked explicitly. |
| [`Algebra.ResultantCoordinates`](LeanCanny/Algebra/ResultantCoordinates.lean) | The bounded primitive-coordinate representation uses the specified normalized resultant. A separating direction makes it separable, and coordinate polynomials over the input field recover every pair of roots. |
| [`Algebra.ShiftCoefficients`](LeanCanny/Algebra/ShiftCoefficients.lean) | Direct access to the coefficient of `x^i θ^j` in `p(θ-c*x)`: `choose(i+j,i)*p[i+j]*(-c)^i`. For degree `d` and integer input coefficient bound `H`, its magnitude is at most `2^d*H*(c+1)^d` and its bit length at most `d + H.size + (c+1).size*d + 1`. |
| [`Algebra.CoefficientBounds`](LeanCanny/Algebra/CoefficientBounds.lean) | A polynomial determinant with column coefficient-mass bounds `Bⱼ` has each coefficient bounded by `N! * ∏ Bⱼ`. Power-of-two column budgets give explicit binary length bounds. Column degree bounds also bound the determinant's degree, including empty matrices. |
| [`Algebra.ResultantBounds`](LeanCanny/Algebra/ResultantBounds.lean) | The unnormalized integer resultant has explicit coefficient magnitude and binary length bounds. Its degree is at most `d₁*d₂` over any commutative ring, without separability or nonzero hypotheses. The two input orders have equal coefficient magnitudes. |
| [`Algebra.MatrixPowerEntry`](LeanCanny/Algebra/MatrixPowerEntry.lean), [`MatrixPowerMachine`](LeanCanny/Algebra/MatrixPowerMachine.lean), [`MatrixPowerWork`](LeanCanny/Algebra/MatrixPowerWork.lean) | A continuation machine computes one entry of `A^e` over any semiring by balanced recursion, streaming the summation through a counter and accumulator. Correctness and the exact abstract transition count are proved; no intermediate matrix power is stored. |
| [`Algebra.MatrixPowerBounds`](LeanCanny/Algebra/MatrixPowerBounds.lean), [`MatrixPowerEncoding`](LeanCanny/Algebra/MatrixPowerEncoding.lean) | Every reachable state has at most `e.size` frames. A binary state representation is injective when its scalar representation is. For residues modulo nonzero `m`, complete states have at most `64*(N.size + e.size + m.size + 1)^2` bits for an `N`-dimensional matrix supplied as an entry function. |
| [`Encoding.BinaryNatFP`](LeanCanny/Encoding/BinaryNatFP.lean) | Machine-certified polynomial-time normalization, successor, truncated predecessor, floor half, and ceiling half directly on binary words. The arithmetic specifications cover arbitrary little-endian inputs and produce canonical outputs; no magnitude is expanded to unary. Canonical binary words have an `FP` recognizer. |
| [`Encoding.BinaryAddFP`](LeanCanny/Encoding/BinaryAddFP.lean) | Binary natural-number addition belongs to native machine-level `FP`. A Horner fold doubles the partial sum and adds the two digits by binary increment; every intermediate word is linearly bounded in the input length. Correctness covers arbitrary little-endian words and canonical output has at most `a.length+b.length+1` bits. |
| [`Encoding.BinaryMulFP`](LeanCanny/Encoding/BinaryMulFP.lean) | Binary natural-number multiplication and multiply-accumulate belong to `FP`. Every partial product in the shift-and-add fold is canonical and has at most the sum of the operand bit lengths. Correctness includes zero, empty words, and redundant high zeroes. |
| [`Encoding.BinarySubFP`](LeanCanny/Encoding/BinarySubFP.lean) | Comparison and truncated subtraction on binary natural words have machine-level polynomial-time certificates. Fixed-width complement addition detects the subtraction carry; the low bits recover the difference. All specifications include noncanonical inputs. |
| [`Encoding.BinaryModFP`](LeanCanny/Encoding/BinaryModFP.lean) | Uniform `FP` modular reduction and modular multiply-accumulate, with the modulus supplied in binary. Long division uses one comparison and at most one subtraction per digit. Every partial remainder is canonical and no longer than the processed dividend; modulus zero follows `a % 0 = a`. |
| [`Encoding.BinaryPowModFP`](LeanCanny/Encoding/BinaryPowModFP.lean), [`Algebra.ModularPowFP`](LeanCanny/Algebra/ModularPowFP.lean) | Binary repeated squaring has an FP certificate. Input `pair base (pair exponent b)` specifies positive modulus `fromBitsLE b+1`. Every fold result fits in the modulus word; no unreduced power is stored. Binary products, negative natural bases, and powers agree with `ZMod` residue arithmetic. |
| [`Encoding.BinaryDivFP`](LeanCanny/Encoding/BinaryDivFP.lean) | Uniform FP binary quotient and paired quotient/remainder, with exact semantics on all words. Reusing the remainder routine determines each quotient digit. Every partial quotient is canonical and no longer than the processed dividend; division by zero gives zero. The final paired output has at most `3*a.length+2` bits. |
| [`Encoding.DyadicQuotientBitFP`](LeanCanny/Encoding/DyadicQuotientBitFP.lean) | An FP routine reads bit `k` of `floor(2^p*a/m)` for `a<m`, with `a,m-1,p,k` supplied in binary. Modular exponentiation modulo `2m`, multiplication, reduction, and division return the canonical zero/one word. It handles modulus one and out-of-range bit indices without constructing the full power or quotient. |
| [`Encoding.BinaryBitFP`](LeanCanny/Encoding/BinaryBitFP.lean), [`Computation.WordBitSpace`](LeanCanny/Computation/WordBitSpace.lean) | FP lookup reads a word at a binary index, capping unary conversion at the word length. It covers arbitrary words and out-of-range indices. Retaining the query while a space-bounded word evaluator runs gives a uniform bit evaluator. |
| [`Algebra.BinarySumCarry`](LeanCanny/Algebra/BinarySumCarry.lean), [`Computation.SumBitController`](LeanCanny/Computation/SumBitController.lean), [`SumBitCorrect`](LeanCanny/Computation/SumBitCorrect.lean), [`SumBitSpace`](LeanCanny/Computation/SumBitSpace.lean) | A selected sum bit has a tidy space certificate from FP binary count/index writers and space-bounded summand-bit access. Carry invariants bound the streamed state; no full summand or sum is stored. |
| [`Algebra.BinaryProduct`](LeanCanny/Algebra/BinaryProduct.lean), [`Computation.ProductBitSpace`](LeanCanny/Computation/ProductBitSpace.lean) | A selected product bit has a `SpaceFunction` certificate from space-bounded bit access to both implicit operands and an FP binary index writer. Bit `k` uses `k+1` shifted terms, each queried through one left selector and one right bit, and the streamed sum machine handles carries. Parent and child workspace are included. Balanced products of a variable number of factors remain separate. |
| [`Algebra.BalancedProduct`](LeanCanny/Algebra/BalancedProduct.lean), [`BalancedProductMachine`](LeanCanny/Algebra/BalancedProductMachine.lean), [`BalancedProductBounds`](LeanCanny/Algebra/BalancedProductBounds.lean), [`BalancedProductWork`](LeanCanny/Algebra/BalancedProductWork.lean), [`BalancedProductEncoding`](LeanCanny/Algebra/BalancedProductEncoding.lean), [`BalancedProductQueryFP`](LeanCanny/Algebra/BalancedProductQueryFP.lean), [`BalancedProductPadding`](LeanCanny/Algebra/BalancedProductPadding.lean) | A uniform typed continuation controller evaluates one bit of a complete balanced product tree. Its invariants prove the answer, stack depth at most `H`, abstract clock `2^(H*(2*K.size+5)+1)`, and binary state size at most `128*(H+K.size+1)^2`. Initial and child query writers are FP. Padding relates trees to finite products and omitted-factor cofactors. |
| [`Algebra.BalancedProductController`](LeanCanny/Algebra/BalancedProductController.lean), [`BalancedProductControllerCorrect`](LeanCanny/Algebra/BalancedProductControllerCorrect.lean), [`BalancedProductStepSpace`](LeanCanny/Algebra/BalancedProductStepSpace.lean), [`BalancedProductSpace`](LeanCanny/Algebra/BalancedProductSpace.lean), [`FiniteProductSpace`](LeanCanny/Algebra/FiniteProductSpace.lean) | Typed continuation invariants prove correctness and polynomial state size for a selected balanced-product bit. Native conditional composition handles space-bounded leaf queries; binary iteration gives the final certificate. |
| [`Algebra.BinarySubtract`](LeanCanny/Algebra/BinarySubtract.lean), [`Computation.SubtractBitSpace`](LeanCanny/Computation/SubtractBitSpace.lean), [`ArithmeticBitSpace`](LeanCanny/Computation/ArithmeticBitSpace.lean), [`SpaceFunctionSelect`](LeanCanny/Computation/SpaceFunctionSelect.lean) | Ordered subtraction reduces a selected bit to a three-term complemented sum. Certified source-bit routines and an FP index writer give its `SpaceFunction` evaluator. Uniform product/subtraction queries compose as bit oracles. A space-bounded computed predicate can select a child computation while accounting for the predicate, saved response, and selected child. |
| [`Algebra.MatrixPowerQueryFP`](LeanCanny/Algebra/MatrixPowerQueryFP.lean) | Total `FP` writers for the initial query and both child queries agree with the typed machine. Initial height comes from the exponent word's bit length. |
| [`Algebra.MatrixPowerDecoding`](LeanCanny/Algebra/MatrixPowerDecoding.lean) | Exact decoders for queries, frames, stacks, residues, and complete states. Successful state decoding characterizes equality with the canonical encoding. A checked total transition agrees with the typed step and inherits its result and quadratic modular-state bound. |
| [`Algebra.MatrixPowerArithmeticFP`](LeanCanny/Algebra/MatrixPowerArithmeticFP.lean) | The uniform modular multiply-accumulate routine agrees exactly with `ZMod` residue encodings for every nonzero modulus. Encoded zero and one are certified too, including modulus one. The modulus is an input field of one FP routine. |
| [`Algebra.MatrixPowerController`](LeanCanny/Algebra/MatrixPowerController.lean), [`MatrixPowerControllerCorrect`](LeanCanny/Algebra/MatrixPowerControllerCorrect.lean) | A total context-carrying bitstring transition belongs to `FP` when its explicit callbacks do. It simulates every typed transition on encoded states. The modular specialization supplies scalar callbacks and retains the original context for entry access. Packet initialization is certified too. Every modular packet has at most `2*c.length+2+64*(N.size+e.size+m.size+1)^2` bits throughout the run. |
| [`Computation.SpaceDecider`](LeanCanny/Computation/SpaceDecider.lean) | A proof-only certificate of membership in Complexitylib2 PSPACE. Native deciders yield canonical Boolean space computations, with no separate transition or clock record. |
| [PSPACERepresentation](LeanCanny/Computation/PSPACERepresentation.lean), [PSPACEClosure](LeanCanny/Computation/PSPACEClosure.lean) | Decider certificates are exactly native PSPACE membership. FP preprocessing and polynomial-time many-one reductions preserve membership by native space composition. |
| [`Computation.SpaceFunction`](LeanCanny/Computation/SpaceFunction.lean) | Exactly a Complexitylib2 tidy polynomial-space certificate, wrapped as a proposition. FP postprocessing and certified predicates compose directly. |
| [`Computation.SpaceFunctionComposition`](LeanCanny/Computation/SpaceFunctionComposition.lean) | Native composition and pairing certify input preparation, retained inputs, and paired outputs without a custom controller. |
| [`Computation.SpaceFunctionBranch`](LeanCanny/Computation/SpaceFunctionBranch.lean) | FP functions and predicates compose with native space computations using the library conditional machine combinator. |
| [`Computation.BoundedFold`](LeanCanny/Computation/BoundedFold.lean), [`BoundedFoldSpace`](LeanCanny/Computation/BoundedFoldSpace.lean), [`SpaceFunctionChain`](LeanCanny/Computation/SpaceFunctionChain.lean) | Binary-counted folds accept arbitrary tidy polynomial-space updates and polynomially bounded accumulator prefixes. Typed and raw-code folds have native certificates; sequential composition is direct. |
| [`Algebra.MatrixPowerHalting`](LeanCanny/Algebra/MatrixPowerHalting.lean), [`MatrixPowerPSPACE`](LeanCanny/Algebra/MatrixPowerPSPACE.lean) | The controller first finishes at exactly `work N e.size e + 1` steps. A `SpaceFunction` certificate returns the complete selected modular power entry, given canonical FP field writers and uniform FP entry access on every input. Zero testing belongs to Complexitylib2's PSPACE. Dimensions and exponents may be exponentially large; only their binary descriptions enter the bound. |
| [`Algebra.CharacteristicAdjugate`](LeanCanny/Algebra/CharacteristicAdjugate.lean), [`BorderedDeterminant`](LeanCanny/Algebra/BorderedDeterminant.lean) | Every coefficient of `adj(XI-A)` is a sum of characteristic coefficients times powers of `A`. Block elimination proves the bordered determinant formula by cancellation of a regular determinant; a monic characteristic polynomial supplies that cancellation over arbitrary commutative rings. |
| [`Algebra.BerkowitzRecurrence`](LeanCanny/Algebra/BerkowitzRecurrence.lean), [`BerkowitzCoefficients`](LeanCanny/Algebra/BerkowitzCoefficients.lean) | The division-free bordered characteristic-coefficient recurrence uses scalar moments `r A^k c`. A recursive reference on `Fin n` matrices agrees with every Mathlib characteristic coefficient, and its signed constant coefficient equals the determinant, including the empty matrix. This reference has linear recursion depth and no space certificate. |
| [`Algebra.BerkowitzTransform`](LeanCanny/Algebra/BerkowitzTransform.lean), [`BerkowitzProduct`](LeanCanny/Algebra/BerkowitzProduct.lean) | Padded coefficient vectors turn each bordered recurrence into a square matrix action. The ordered product's first column gives all characteristic coefficients; its signed top-left entry is the determinant. Factor entries depend on input entries and scalar power moments, without using characteristic coefficients. |
| [`Algebra.MatrixProductEntry`](LeanCanny/Algebra/MatrixProductEntry.lean), [`BerkowitzBalanced`](LeanCanny/Algebra/BerkowitzBalanced.lean) | Balanced interval recursion computes an entry of any ordered matrix product over a semiring, preserving factor order. Applied to the coefficient transformations, height `n.size` suffices to recover every characteristic coefficient and the determinant. A factor accessor avoids constructing the full list. These identities establish correctness and recursion height; later modules supply the encoded evaluator and its space bound. |
| [`Algebra.LayeredMatrix`](LeanCanny/Algebra/LayeredMatrix.lean), [`LayeredMatrixMachine`](LeanCanny/Algebra/LayeredMatrixMachine.lean) | An ordered product interval is one entry of a layered matrix power. Flattening the layer-coordinate pairs gives `Fin` indices. The existing streamed power machine and context-carrying controller evaluate the product under their entry-access contract, with the proved abstract transition and modular state bounds. |
| [`Algebra.BerkowitzPower`](LeanCanny/Algebra/BerkowitzPower.lean) | The `n`th power of an `(n+1)^2`-dimensional layered matrix contains every characteristic coefficient. The power machine computes them, and its encoded controller tests determinant zero under the explicit callback contract. Stored residue states have at most `64*(3*n.size+m.size+2)^2` bits; controller packets add `2*c.length+2`. The space-bounded implementation below accounts for factor-access workspace. |
| [`Algebra.PolynomialCoefficientMatrix`](LeanCanny/Algebra/PolynomialCoefficientMatrix.lean), [`BerkowitzCoefficientPower`](LeanCanny/Algebra/BerkowitzCoefficientPower.lean) | A lower triangular coefficient matrix preserves polynomial addition and multiplication through degree `d`. Flattening these blocks turns polynomial matrix-power coefficients into scalar power entries. Applied to Berkowitz, each degree-`d` determinant coefficient is a signed power entry in dimension `(n+1)^2*(d+1)`. The encoded evaluator below supplies its entry-access and space certificates. |
| [`Algebra.PolynomialPowerAccessFP`](LeanCanny/Algebra/PolynomialPowerAccessFP.lean), [`PolynomialPowerSpace`](LeanCanny/Algebra/PolynomialPowerSpace.lean) | FP binary division, remainder, subtraction, and guards select one coefficient of an original matrix entry or zero. Modular powering returns a selected polynomial matrix-power coefficient with a `SpaceFunction` certificate, given FP control fields and space-bounded input-coefficient access. Its zero-test language is in PSPACE. No polynomial coefficient vector is stored. |
| [`PolynomialProductPower`](LeanCanny/Algebra/PolynomialProductPower.lean), [`PolynomialProductSpace`](LeanCanny/Algebra/PolynomialProductSpace.lean), [`ModularSumSpace`](LeanCanny/Algebra/ModularSumSpace.lean) | A polynomial product is one entry of a shift-matrix power. FP binary factor-count/modulus/degree fields and space-bounded factor-coefficient access give a complete selected-coefficient evaluator and PSPACE zero test, including empty products. A modular-sum evaluator reduces after each space-bounded summand call and keeps its accumulator within the modulus word, including modulus one and empty sums. |
| [`Algebra.PolynomialMomentSpace`](LeanCanny/Algebra/PolynomialMomentSpace.lean) | Source/sink augmentation commutes with taking entry coefficients. FP query writers carry a requested degree into space-bounded vector/matrix coefficient routines. The polynomial power evaluator returns the selected coefficient of `r A^k c`, accounting for all child queries and states. |
| [`Algebra.BerkowitzPolynomialMoment`](LeanCanny/Algebra/BerkowitzPolynomialMoment.lean), [`BerkowitzPolynomialFactor`](LeanCanny/Algebra/BerkowitzPolynomialFactor.lean), [`BerkowitzPolynomialFactorSpace`](LeanCanny/Algebra/BerkowitzPolynomialFactorSpace.lean), [`BerkowitzPolynomialSpace`](LeanCanny/Algebra/BerkowitzPolynomialSpace.lean) | A certified routine returns a selected coefficient of a polynomial determinant modulo a positive modulus. FP dimension/modulus/degree fields and space-bounded original entry-coefficient access suffice. Offset queries compute trailing-block moments, four-case selection yields factor coefficients, and polynomial powering plus an FP parity test supplies the determinant coefficient with its sign. Its zero-test language is in PSPACE. |
| [`Algebra.MatrixPowerStepSpace`](LeanCanny/Algebra/MatrixPowerStepSpace.lean) | Exponent-one requests compose a space-bounded entry routine with FP query/result writers. The resulting transition agrees with the mathematical power controller. |
| [`Algebra.MatrixPowerSpaceEntries`](LeanCanny/Algebra/MatrixPowerSpaceEntries.lean) | Modular powering accepts arbitrary tidy polynomial-space entries and FP controls. Parent state-size and correctness invariants combine with native iteration; zero testing is in Complexitylib2 PSPACE. |
| [`Algebra.BerkowitzFactorAccess`](LeanCanny/Algebra/BerkowitzFactorAccess.lean) | Factor `s` is accessed directly through the trailing block `A[s+i,s+j]`, with a proved identity default beyond the last factor. Its entries split into one, a negated diagonal entry, a negated scalar moment, or zero. The moment case is exactly the negative of an augmented matrix-power entry. No preceding factors or coefficient vectors are needed. |
| [`Algebra.MatrixMomentPower`](LeanCanny/Algebra/MatrixMomentPower.lean), [`MatrixMomentFP`](LeanCanny/Algebra/MatrixMomentFP.lean) | Adding a source and sink makes `r A^k c` one entry of the `(k+2)`nd power of an `(n+2)`-dimensional matrix. Uniform FP binary field, row, column, and original-entry access gives certified augmented-entry access, child initialization, and a complete power controller. Result extraction, first halting time, and every packet's size are proved. The child computes one moment without storing its summands. |
| [`Algebra.MatrixMomentSpaceEntries`](LeanCanny/Algebra/MatrixMomentSpaceEntries.lean), [`BerkowitzMomentSpace`](LeanCanny/Algebra/BerkowitzMomentSpace.lean), [`BerkowitzFactorSpace`](LeanCanny/Algebra/BerkowitzFactorSpace.lean) | Scalar moments accept certified space-bounded row, column, and matrix routines. Offset query writers specialize this evaluator to each trailing principal block. FP guards choose one, a negative diagonal entry, a negative moment, or zero, giving the complete factor evaluator with space-bounded original entries. |
| [`Algebra.ModularNegFP`](LeanCanny/Algebra/ModularNegFP.lean) | Uniform FP negation of binary residues agrees with `ZMod`, including modulus one. Reducing, subtracting from the modulus, and reducing again handles arbitrary binary input words. The moment child has a certified negated-output projection for the factor evaluator. |
| [`Algebra.BerkowitzQueryFP`](LeanCanny/Algebra/BerkowitzQueryFP.lean), [`BerkowitzMomentAccessFP`](LeanCanny/Algebra/BerkowitzMomentAccessFP.lean) | FP division/remainder decodes flattened layer and coefficient indices. FP writers supply the trailing dimension, offset, moment exponent, and four-case selector, with exact numeric specifications. Offset query writers access the original input matrix and give certified callbacks for exactly the trailing block and border vectors in the moment formula. |
| [`Algebra.BerkowitzFactorChild`](LeanCanny/Algebra/BerkowitzFactorChild.lean), [`BerkowitzFactorChildCorrect`](LeanCanny/Algebra/BerkowitzFactorChildCorrect.lean) | The immediate and scalar-moment cases compute the correct layered entries. The semantic reference controller and correctness proof are retained; the native certificate composes the moment evaluator directly. |
| [BerkowitzPowerAccess](LeanCanny/Algebra/BerkowitzPowerAccess.lean), [BerkowitzPSPACE](LeanCanny/Algebra/BerkowitzPSPACE.lean) | Canonical binary dimensions and indices for the layered power, and the shared determinant families. Native determinant certificates are provided by BerkowitzSpaceEntries. |
| [`Algebra.BerkowitzSpaceEntries`](LeanCanny/Algebra/BerkowitzSpaceEntries.lean), [`IntegerDeterminantSpaceEntries`](LeanCanny/Algebra/IntegerDeterminantSpaceEntries.lean) | Modular and integer determinant zero testing compose native certificates for entries, moments, factors, powers, and modulus scans. Only the stated binary controls require FP. |
| [`Algebra.IntegerModular`](LeanCanny/Algebra/IntegerModular.lean) | An integer with at most `B` magnitude bits is zero exactly when its residues modulo `1,...,2*B+4` all vanish. An LCM growth estimate keeps the scan linear in the bit budget. The criterion applies to determinants; column entry bounds give determinant bit budgets, including empty matrices. |
| [`Algebra.IntegerReconstruction`](LeanCanny/Algebra/IntegerReconstruction.lean), [`ChineseRemainderSum`](LeanCanny/Algebra/ChineseRemainderSum.lean), [`ChineseRemainderSign`](LeanCanny/Algebra/ChineseRemainderSign.lean), [`SmallModulusCRT`](LeanCanny/Algebra/SmallModulusCRT.lean) | A bounded integer's sign is determined by a sum of small CRT fractions. Local inverse-weighted numerators are reduced modulo their own moduli. Downward truncation at denominator `D > 2*card*product` preserves the sign test after zero is excluded. Maximal prime powers up to `N=2*B+6` have product `lcmUpto N`, individual moduli at most `N`, and sufficient dyadic precision exponent `(N+2)*N.size+2`. The certified streamed evaluator below implements these specifications given local preparation. |
| [`Algebra.ChineseRemainderSignBit`](LeanCanny/Algebra/ChineseRemainderSignBit.lean), [`DyadicSumSpace`](LeanCanny/Algebra/DyadicSumSpace.lean), [`ChineseRemainderSignSpace`](LeanCanny/Algebra/ChineseRemainderSignSpace.lean) | One selected bit of the truncated CRT sum determines the integer sign, including zero through vanishing local numerators. A certified local preparation routine, FP count/precision writers, and the magnitude/precision bounds give a complete sign `SpaceFunction` and PSPACE negative-language theorem. Local preparation is implemented below. |
| [`Algebra.IndexedModulusCRT`](LeanCanny/Algebra/IndexedModulusCRT.lean) | Indexing `0,...,N` uses maximal prime powers at prime indices and modulus one elsewhere. The count is exactly `N+1`, the product remains `lcmUpto N`, and the same precision exponent suffices. For positive `N`, each modulus is at most `N`. No compressed prime enumeration or prime-counting routine is required. |
| [`Algebra.PrimalitySpace`](LeanCanny/Algebra/PrimalitySpace.lean), [`PrimePowerSpace`](LeanCanny/Algebra/PrimePowerSpace.lean), [`IndexedModulusSpace`](LeanCanny/Algebra/IndexedModulusSpace.lean) | The indexed CRT modulus has a `SpaceFunction` evaluator on arbitrary binary words `pair N i`. Trial division agrees with `Nat.Prime`, including zero and one. A capped multiplication fold returns exactly `i^(log i N)`, retaining magnitudes at most `N+1`, including zero/one bases and bound zero. Sequential composition and FP selection supply the prime-power-or-one result. |
| [`Algebra.CofactorProductSpace`](LeanCanny/Algebra/CofactorProductSpace.lean), [`CofactorResidueSpace`](LeanCanny/Algebra/CofactorResidueSpace.lean), [`ModularInverseSpace`](LeanCanny/Algebra/ModularInverseSpace.lean), [`CRTWeightSpace`](LeanCanny/Algebra/CRTWeightSpace.lean), [`CRTPreparationSpace`](LeanCanny/Algebra/CRTPreparationSpace.lean) | Certified local CRT preparation computes the selected modulus, streams its complementary product modulo that modulus, searches for the unique inverse, and combines it with a space-bounded integer-residue query. The output agrees exactly with the CRT numerator/modulus specification, including modulus one; every parent and child state is counted. |
| [`Algebra.IntegerSignSpace`](LeanCanny/Algebra/IntegerSignSpace.lean), [`CannyResultantSign`](LeanCanny/Algebra/CannyResultantSign.lean), [`Computation.SpaceDeciderOutput`](LeanCanny/Computation/SpaceDeciderOutput.lean) | A uniform `SpaceFunction` residue routine and FP binary magnitude-bit budget suffice for integer negativity in PSPACE, even with an exponential bit budget. Canny's selected integer resultant coefficient instantiates the theorem using its proved source-derived budget. Its negative and positive languages are in PSPACE, and a certified three-way evaluator returns canonical tags `0` for zero, `1` for negative, and `2` for positive. |
| [`ChineseRemainderDigits`](LeanCanny/Algebra/ChineseRemainderDigits.lean), [`ChineseRemainderRankSpace`](LeanCanny/Algebra/ChineseRemainderRankSpace.lean), [`IntegerRankSpace`](LeanCanny/Algebra/IntegerRankSpace.lean), [`CannyCoefficientRank`](LeanCanny/Algebra/CannyCoefficientRank.lean) | An exact integer truncation-error formula proves rounded CRT reconstruction and identifies the correction rank with the high part of the truncated sum. Any selected rank bit has a certified space-bounded evaluator from residue access and FP budget/index writers, including Canny's actual resultant and coordinate coefficients. The rank's width is bounded by the FP count word length. |
| [`IndexedProductSpace`](LeanCanny/Algebra/IndexedProductSpace.lean), [`IndexedSumSpace`](LeanCanny/Algebra/IndexedSumSpace.lean) | Certified indexed-modulus access supplies bits of the combined product and every cofactor. Local numerator preparation, streamed multiplication, and streamed summation supply bits of the inverse-weighted CRT integer sum. The bound writer is FP; residue access is space bounded. No product, cofactor, or sum is stored in full. |
| [`IntegerSignumSpace`](LeanCanny/Algebra/IntegerSignumSpace.lean), [`InfinitesimalSign`](LeanCanny/Algebra/InfinitesimalSign.lean), [`InfinitesimalSignSpace`](LeanCanny/Algebra/InfinitesimalSignSpace.lean), [`InfinitesimalResidueSpace`](LeanCanny/Algebra/InfinitesimalResidueSpace.lean) | A polynomial's sign on a sufficiently small positive interval equals its lowest nonzero coefficient's sign; zero polynomials and common intervals for finite families are included. A binary bounded scan retains a sign tag of at most two bits. Uniform coefficient residues and FP degree/coefficient-budget writers give its complete `SpaceFunction` certificate. This handles Canny's small-parameter sign rule; the full implicit-family algebraic-root specialization used by Canny remains open. |
| [`RationalSubstitution`](LeanCanny/Algebra/RationalSubstitution.lean), [`RationalSubstitutionMap`](LeanCanny/Algebra/RationalSubstitutionMap.lean) | An explicit univariate numerator equals the substituted multivariate polynomial times `∏ dᵢ^(2*degreeOfᵢ p)`. The denominator is positive wherever all `dᵢ` are nonzero, so signs agree. The numerator degree is at most `∑ᵢ 2*degreeOfᵢ p*max(deg nᵢ,deg dᵢ)`. Coefficient reduction commutes with the construction when denominator exponents retain the original degree allowances, including reductions that kill leading coefficients. |
| [`CoefficientMass`](LeanCanny/Algebra/CoefficientMass.lean), [`RationalSubstitutionBounds`](LeanCanny/Algebra/RationalSubstitutionBounds.lean), [`RationalSubstitutionBudget`](LeanCanny/Algebra/RationalSubstitutionBudget.lean) | Coefficient mass is subadditive and submultiplicative. For `A` variables, source variable degrees at most `D`, coordinate degrees at most `E`, source coefficient magnitudes at most `2^b₀`, and coordinate coefficient magnitudes at most `2^b`, the cleared numerator has degree at most `2*A*D*E` and coefficient magnitude-bit length at most `b₀+A*(D+1).size+2*A*D*(b+(E+1).size)+1`. Both bounds have FP binary writers. |
| [`IndexedRationalSubstitution`](LeanCanny/Algebra/IndexedRationalSubstitution.lean), [`RationalSubstitutionResidue`](LeanCanny/Algebra/RationalSubstitutionResidue.lean), [`RationalSubstitutionSign`](LeanCanny/Algebra/RationalSubstitutionSign.lean) | Indexed source terms, FP binary counts/width/exponent access, and space-bounded source/coordinate coefficient-residue routines give a complete modular coefficient evaluator for rational substitution. Repeated and cancelling terms, empty families, modulus one, and modular degree drops are included. Indexed degree and coefficient budgets have FP writers; these give a complete infinitesimal-sign evaluator. Even clearing widths preserve the original rational expression's sign wherever its denominators are nonzero. The encoded ETR source instantiation is supplied below; the full Canny algebraic-root specialization and the critical-point argument remain open. |
| [`ETR.IndexedExpansion`](LeanCanny/ETR/IndexedExpansion.lean), [`IndexedExpansionBounds`](LeanCanny/ETR/IndexedExpansionBounds.lean), [`IndexedExpansionSize`](LeanCanny/ETR/IndexedExpansionSize.lean), [`ETR.IndexedRationalSubstitution`](LeanCanny/ETR/IndexedRationalSubstitution.lean), [`MonomialCountFP`](LeanCanny/ETR/MonomialCountFP.lean) | Actual ETR expression trees have indexed monomials whose sum is exactly the original polynomial. Their count has at most `N+1` bits, individual coefficients have magnitude at most `2^N`, and exponents are at most the syntax degree bound, for encoded term length `N`. Finite-variable evaluation and rational-substitution signs agree with the original term; normalized ETR satisfiability is equivalent to the resulting indexed equation. A uniform FP reader computes the binary monomial count, with every stack state bounded even on malformed input. It constructs no expanded term list. |
| [`MonomialReaderMachine`](LeanCanny/ETR/MonomialReaderMachine.lean), [`MonomialReaderFP`](LeanCanny/ETR/MonomialReaderFP.lean), [`MonomialExponentFP`](LeanCanny/ETR/MonomialExponentFP.lean) | A syntax-directed stack visits one selected monomial in at most the term's encoded length. Exact binary-step simulation and bounds for every task/index/accumulator give an FP traversal theorem. The concrete exponent reader has uniform FP term/monomial-index/variable-index fields; it keeps indices binary, validates malformed terms to zero, and returns the exact syntax-derived exponent in the rational-substitution query format. |
| [`IntegerResidueFP`](LeanCanny/ETR/IntegerResidueFP.lean), [`MonomialCoefficientFP`](LeanCanny/ETR/MonomialCoefficientFP.lean), [`EncodedRationalSubstitution`](LeanCanny/ETR/EncodedRationalSubstitution.lean), [`CompiledRationalSource`](LeanCanny/ETR/CompiledRationalSource.lean) | Indexed ETR source coefficients have uniform FP residue access, including negative constants and modulus one. Source counts, exponents, even clearing widths, and bit budgets are supplied internally from encoded terms. Certified coordinate-residue routines give the full modular coefficient evaluator; coordinate degree/coefficient bounds also give infinitesimal signs with semantics in terms of the actual input expression. The existing FP compiler supplies a concrete source for every ETR input, with nonempty real zero set exactly on ETR yes-instances. The full Canny algebraic-root specialization and coordinate construction for the decision procedure remain open. |
| [`ScaledSignQueries`](LeanCanny/Algebra/ScaledSignQueries.lean), [`SignQueryBounds`](LeanCanny/Algebra/SignQueryBounds.lean), [`SignQueryBudget`](LeanCanny/Algebra/SignQueryBudget.lean), [`SignQueryProductSpace`](LeanCanny/Algebra/SignQueryProductSpace.lean) | Integer combinations of ternary product Tarski queries equal `2^k` times each sign-pattern count at distinct real roots. For a nonzero root polynomial, positivity is exactly realizability of the pattern. Query degree/coefficient bounds and the scaled output-bit bound have FP binary writers. Each query product has a complete streamed modular coefficient evaluator from space-bounded input coefficient routines. The identity uses `3^k` queries; the product-query Tarski evaluator below now includes the original indexed polynomial readers. Enumeration, weights, and exact counting are composed below for a polynomially bounded number of polynomials. Canny's stronger query-selection workspace bound remains open. |
| [`Sturm/Infinity`](LeanCanny/Algebra/Sturm/Infinity.lean), [`SturmQuery`](LeanCanny/Algebra/SturmQuery.lean) | Sturm–Tarski over ℝ: a query is the difference of leading-coefficient sign variations at the two infinities, using degree parity on the left. Repeated roots, vanishing queries, and the zero-polynomial convention are covered. Rational inputs can use rational signed remainders throughout. The formula substitutes into every scaled sign-pattern count. [Attributed proof adaptation](STURM_SOURCES.md) from TauCeti; no new dependency or resource bound is assumed. Original-source space-bounded evaluation is supplied by the principal pipeline below. |
| [`PrincipalQuery`](LeanCanny/Algebra/PrincipalQuery.lean), [`PrincipalSubresultant/Minor`](LeanCanny/Algebra/PrincipalSubresultant/Minor.lean) | Tarski queries equal the zero-gap sign statistic of signed principal subresultants of the head and its reduced derivative product. The algebraic recurrence works over ordered fields; real, rational, and integer input query formulas cover repeated roots and constant or zero heads. Every principal determinant matches the existing Sylvester-minor convention, including terminal indices, and inherits the integer bit budget. [TauCeti proof attribution](STURM_SOURCES.md). The integer pseudo-seed below avoids rational seed reduction. Actual-degree routines, determinant signs, and the sign scan are composed in the original-source Tarski evaluator below. |
| [`PseudoRemainder`](LeanCanny/Algebra/PseudoRemainder.lean), [`PseudoRemainderMatrix`](LeanCanny/Algebra/PseudoRemainderMatrix.lean), [`PseudoRemainderSpace`](LeanCanny/Algebra/PseudoRemainderSpace.lean), [`PseudoRemainderBudget`](LeanCanny/Algebra/PseudoRemainderBudget.lean), [`PseudoRemainderQuery`](LeanCanny/Algebra/PseudoRemainderQuery.lean) | A fixed linear, division-free reduction gives a smaller-degree seed congruent to a positive even-power multiple of the derivative product. For nonconstant integer heads, Tarski queries therefore use integer principal determinants throughout. Selected seed coefficients are scalar matrix-power moments. FP metadata and space-bounded coefficient access to the original head and input give a complete modular coefficient evaluator, including modulus one and modular degree drops; no reduction-matrix callback is assumed. Integer coefficient bit bounds have FP binary writers. The source instantiation and actual-degree routines below use the original two polynomial readers; the original sources and computed degrees are now composed with the principal pipeline below. |
| [`DerivativeProductSpace`](LeanCanny/Algebra/DerivativeProductSpace.lean), [`TarskiSeedSpace`](LeanCanny/Algebra/TarskiSeedSpace.lean), [`IntegerTarskiSeedSpace`](LeanCanny/Algebra/IntegerTarskiSeedSpace.lean), [`PolynomialDegreeSpace`](LeanCanny/Algebra/PolynomialDegreeSpace.lean), [`TarskiSeedDegreeSpace`](LeanCanny/Algebra/TarskiSeedDegreeSpace.lean) | The actual derivative product and seed have complete modular coefficient evaluators from only the original head and query coefficient routines. Degree and integer bit-budget writers are derived from their original bounds. A uniform arbitrary-positive-modulus adapter gives three-way integer seed-coefficient signs, with out-of-range indices returning zero. Space-bounded coefficient-zero scans compute actual head/seed degrees in polynomial space; an offset code distinguishes a zero head from a nonzero constant head. The computed metadata and all source routines are composed in the Tarski evaluator below. |
| [`SignStatistic`](LeanCanny/Algebra/SignStatistic.lean), [`SignStatisticSpace`](LeanCanny/Algebra/SignStatisticSpace.lean), [`SignStatisticQuery`](LeanCanny/Algebra/SignStatisticQuery.lean) | The complete zero-gap sign statistic has a polynomial-space streaming evaluator from space-bounded sign routines and an FP binary count. After `k` entries its accumulator has at most `5*k.size + 10` bits. FP descending indices connect it to the integer Tarski formula when supplied actual positive head-degree metadata and a certified principal-coefficient sign reader. The principal-coefficient reader below instantiates the sign source, and the Tarski evaluator supplies computed-degree metadata. |
| [`BerkowitzResidueSpace`](LeanCanny/Algebra/BerkowitzResidueSpace.lean), [`PrincipalMinorSpace`](LeanCanny/Algebra/PrincipalMinorSpace.lean) | Scalar determinants now return their complete modular residues from space-bounded entries. Principal minors embed in the original Sylvester matrix with non-strict order bounds, covering terminal one-block and empty minors. Their uniform residues use only the original two coefficient readers and FP degree/order/bit-budget metadata. |
| [`PrincipalCoefficientSpace`](LeanCanny/Algebra/PrincipalCoefficientSpace.lean), [`PrincipalCoefficientQuery`](LeanCanny/Algebra/PrincipalCoefficientQuery.lean) | Complete signed-principal-coefficient residues and three-way integer signs, including orders above the smaller degree bound. Binary parity correction, retained leading coefficients, and zero branches match the mathematical normalization. The descending scan is now certified from the two polynomial coefficient readers, with no principal-sign callback assumed. For the head and its integer pseudo-seed, actual-degree metadata gives a Tarski-query evaluator. The original-source Tarski evaluator below supplies the computed degrees and both coefficient readers. |
| [`TarskiDegreeContext`](LeanCanny/Algebra/TarskiDegreeContext.lean), [`TarskiPrincipalContext`](LeanCanny/Algebra/TarskiPrincipalContext.lean), [`TarskiQuerySpace`](LeanCanny/Algebra/TarskiQuerySpace.lean), [`TarskiQueryPSPACE`](LeanCanny/Algebra/TarskiQueryPSPACE.lean) | Complete Tarski-query evaluation from the original head and query coefficient-residue routines. FP upper-degree and coefficient-mass bounds suffice; actual head/seed degrees are computed in polynomial space and retained. Total capped contexts validate arbitrary metadata and recover the original head at its computed degree. Constant heads and the zero-polynomial finite-root convention are covered. The output is the full signed integer query, and zero/positive/negative query languages belong to PSPACE under the same source contracts. |
| [`SignQuerySource`](LeanCanny/Algebra/SignQuerySource.lean), [`SignQueryTarskiSpace`](LeanCanny/Algebra/SignQueryTarskiSpace.lean) | Each ternary product Tarski query has a complete polynomial-space evaluator from uniform root and indexed original-polynomial coefficient readers. Binary count/degree/mass fields and an FP exponent reader suffice; product degree and coefficient-mass budgets are derived internally. Empty products, modulus one, and zero/positive/negative query-language consequences are covered. |
| [`IntegerSumSpace`](LeanCanny/Algebra/IntegerSumSpace.lean) | A binary FP bound permits exponentially many signed summands evaluated by space-bounded space routines. Positive/negative accumulators have polynomial bit length by the child output bound, with full native space composition and a canonical signed result. FP signed multiplication supplies arithmetic for pattern weights. The complete sign-pattern count below composes this evaluator with ternary enumeration and pattern weights. |
| [`TernaryFP`](LeanCanny/Encoding/TernaryFP.lean), [`IntegerSmallProductSpace`](LeanCanny/Algebra/IntegerSmallProductSpace.lean) | A unary FP certificate for `k` gives FP binary `3^k` and ternary-digit access, with enumeration matched to Mathlib's finite-function equivalence. Products of signed factors of magnitude at most two retain at most `O(k)` bits and include all space-bounded factor calls. |
| [`SignPatternSource`](LeanCanny/Algebra/SignPatternSource.lean), [`SignPatternWeights`](LeanCanny/Algebra/SignPatternWeights.lean), [`SignPatternSpace`](LeanCanny/Algebra/SignPatternSpace.lean), [`SignPatternCountSpace`](LeanCanny/Algebra/SignPatternCountSpace.lean) | Full scaled and exact counts of distinct real roots realizing a sign pattern, from uniform root/indexed polynomial coefficient readers, an FP pattern reader, and FP degree/mass bounds. The polynomial-count field has an explicit unary FP certificate, so ternary enumeration fits polynomial space. Empty families and the zero-polynomial finite-root convention are included. Pattern realizability belongs to PSPACE for nonzero root polynomials; the guarded language includes that condition explicitly. Canny's stronger polylogarithmic dependence on implicit family size remains open. |
| [`ChineseRemainderDigitSpace`](LeanCanny/Algebra/ChineseRemainderDigitSpace.lean), [`IntegerDigitSpace`](LeanCanny/Algebra/IntegerDigitSpace.lean), [`CannyCoefficientDigits`](LeanCanny/Algebra/CannyCoefficientDigits.lean) | `IntegerDigitBits.evaluator` computes arbitrary integer-magnitude bits from uniform space-bounded residue access and an FP binary magnitude budget. Product, inverse-weighted sum, correction rank, sign, subtraction, and selection are all supplied internally with composed workspace certificates. The actual resultant and all-branch coordinate coefficients have specialized evaluators under their existing source contracts. |
| [`Computation.BoundedScan`](LeanCanny/Computation/BoundedScan.lean), [`BoundedScanPSPACE`](LeanCanny/Computation/BoundedScanPSPACE.lean) | A binary count and one Boolean accumulator give universal scans over native space-bounded predicates, without child clocks. |
| [`Algebra.IntegerDeterminantPSPACE`](LeanCanny/Algebra/IntegerDeterminantPSPACE.lean) | Integer determinant zero testing belongs to PSPACE under FP dimension and binary bit-budget access and uniform FP original-entry residue access. The scan instantiates the modular determinant decider, including its factor children. Integer entries and the determinant bit budget may be exponentially long/large respectively; their complete integer values are never stored. |
| [`Algebra.SylvesterAccessFP`](LeanCanny/Algebra/SylvesterAccessFP.lean), [`SylvesterAccessCorrect`](LeanCanny/Algebra/SylvesterAccessCorrect.lean) | FP binary guards and query writers access the two shifted coefficient blocks of Mathlib's Sylvester matrix. Entry correctness holds for arbitrary scalar encodings with empty-word zero. If coefficients have magnitude at most `2^b`, the resultant has at most `N.size*N+N*b+1` magnitude bits, where `N=m+n`; its budget writer is FP. |
| [`Algebra.ResultantPSPACE`](LeanCanny/Algebra/ResultantPSPACE.lean) | Zero testing for a specified-degree integer resultant belongs to PSPACE under FP binary degree/budget fields and uniform FP coefficient-residue access. The integer determinant decider runs on streamed Sylvester entries with a computed bit budget. A corollary covers the ordinary resultant when the supplied degrees equal the actual polynomial degrees. |
| [`Algebra.Subresultant`](LeanCanny/Algebra/Subresultant.lean), [`SubresultantMinor`](LeanCanny/Algebra/SubresultantMinor.lean), [`SubresultantBounds`](LeanCanny/Algebra/SubresultantBounds.lean) | Interior subresultants (`k<m,n`) are explicit Sylvester minors with Mathlib's column order. Order zero equals its resultant; coefficient-ring maps commute; degree is at most `k`; order one is explicitly linear. Injective binary row/column formulas embed each minor in the full Sylvester matrix. Column budgets bound every integer/parameter coefficient. |
| [`SubresultantAccessFP`](LeanCanny/Algebra/SubresultantAccessFP.lean), [`SubresultantEntrySpace`](LeanCanny/Algebra/SubresultantEntrySpace.lean), [`SubresultantPolynomialSpace`](LeanCanny/Algebra/SubresultantPolynomialSpace.lean) | Binary index transformations are FP. Given FP metadata and uniform space-bounded input coefficient routines, a certified evaluator computes a selected modular coefficient of any interior symbolic subresultant; its zero language is in PSPACE. Invalid orders/indices return zero, including empty-minor cases. |
| [`SubresultantRoot`](LeanCanny/Algebra/SubresultantRoot.lean), [`SubresultantGCD`](LeanCanny/Algebra/SubresultantGCD.lean) | For degree bounds `m,n>1`, the first subresultant is `D*(X-b)` at every common root `b`. Removing the common factor `X-b` identifies `D` with the quotient resultant. A nonzero linear GCD makes the quotients coprime and proves `D≠0` at the actual input degrees. |
| [`SubresultantRecovery`](LeanCanny/Algebra/SubresultantRecovery.lean), [`SubresultantRecoveryBounds`](LeanCanny/Algebra/SubresultantRecoveryBounds.lean) | Symbolic parameter polynomials `N,D` recover both coordinates at separating root pairs: `D(θ)≠0`, `b=-N(θ)/D(θ)`, `a=θ+c*N(θ)/D(θ)`, for nonzero direction and input degrees greater than one. Both polynomials have degree at most `(d₂-1)*d₁`, with explicit integer coefficient bit bounds. |
| [`CoordinateRecovery`](LeanCanny/Algebra/CoordinateRecovery.lean), [`CoordinateRecoveryBounds`](LeanCanny/Algebra/CoordinateRecoveryBounds.lean) | Direct linear-input branches extend the recovery formulas to every input degree and direction under the separating-root-pair hypotheses. A zero direction forces the second input to be linear. Numerator and denominator have degree at most `max 1 ((d₂-1)*d₁)` and explicit integer coefficient bit bounds. The full coordinate computation's space bound remains open. |
| [`Algebra.SylvesterSpaceAccess`](LeanCanny/Algebra/SylvesterSpaceAccess.lean), [`ResultantSpaceEntries`](LeanCanny/Algebra/ResultantSpaceEntries.lean) | Integer resultant zero testing accepts certified space-bounded coefficient-residue routines under FP degree/budget fields. Sylvester access selects a coefficient child or zero, and the strengthened integer determinant decider consumes the resulting entry routine. A corollary covers ordinary resultants at the actual degrees. |
| [`Algebra.SylvesterPolynomialSpace`](LeanCanny/Algebra/SylvesterPolynomialSpace.lean), [`ResultantPolynomialSpace`](LeanCanny/Algebra/ResultantPolynomialSpace.lean) | A selected coefficient of a specified-degree resultant over a polynomial residue ring has a `SpaceFunction` evaluator. The Sylvester accessor carries the coefficient degree into either input routine, and the polynomial determinant evaluator consumes these space-bounded calls. FP input-degree/modulus/output-degree fields suffice. Modular coefficient zero testing belongs to PSPACE. |
| [`Algebra.CannyResultantResidue`](LeanCanny/Algebra/CannyResultantResidue.lean) | The actual integer `cannyResultant` has a certified modular coefficient evaluator. Shifted-coefficient evaluation supplies `p₁(θ-c*x)`; an FP guard supplies `p₂(x)`. FP source-degree/direction/output-degree fields and uniform FP original-coefficient residue access suffice. Reduction commutes with the resultant at the fixed integer source degrees, including modular degree drops. Its modular coefficient zero test is in PSPACE. |
| [`CannySubresultantResidue`](LeanCanny/Algebra/CannySubresultantResidue.lean), [`CannySubresultantInteger`](LeanCanny/Algebra/CannySubresultantInteger.lean), [`CannySubresultantSign`](LeanCanny/Algebra/CannySubresultantSign.lean) | The concrete symbolic numerator and denominator have certified modular coefficient evaluation, integer zero testing, and three-way integer coefficient signs. The reduced-column bound fits the existing FP resultant budget writer. Under FP source metadata, coefficient selection, original-coefficient residue access, and source bit budgets, the zero and both strict-sign languages are in PSPACE. Sign evaluation at algebraic parameter values remains separate. |
| [`CannyCoordinateResidue`](LeanCanny/Algebra/CannyCoordinateResidue.lean), [`CannyCoordinateInteger`](LeanCanny/Algebra/CannyCoordinateInteger.lean), [`CannyCoordinateSign`](LeanCanny/Algebra/CannyCoordinateSign.lean) | FP degree tests include the direct linear branches in certified modular coefficient evaluation for the combined coordinate numerator and denominator. An expanded FP binary bit budget certifies integer zero testing and full three-way coefficient signs across every branch. Under the source metadata, selection, residue, and bit-budget contracts, the integer zero and both strict-sign languages are in PSPACE. Algebraic-parameter signs remain separate. |
| [`Algebra.ShiftCoefficientSpace`](LeanCanny/Algebra/ShiftCoefficientSpace.lean), [`CannyCoefficientSpace`](LeanCanny/Algebra/CannyCoefficientSpace.lean), [`PrimitivePairSpace`](LeanCanny/Algebra/PrimitivePairSpace.lean) | Shifted, resultant, subresultant, and full piecewise coordinate evaluation accept arbitrary native space-bounded source coefficient readers; metadata remains FP. The actual integer pair formulas have complete native coefficient readers. A computed resultant supplies a second resultant's left coefficient child under its exact product-degree identity. |
| [`Algebra.PrimitivePairCoordinates`](LeanCanny/Algebra/PrimitivePairCoordinates.lean), [`CoordinateRecoveryMap`](LeanCanny/Algebra/CoordinateRecoveryMap.lean), [`PrimitivePairInteger`](LeanCanny/Algebra/PrimitivePairInteger.lean), [`PrimitivePairBounds`](LeanCanny/Algebra/PrimitivePairBounds.lean) | Explicit numerators `theta*D+c*N` and `-N`, with common denominator D, decode the report's resultant roots bijectively to root pairs for a separating direction. Injective coefficient maps preserve the actual formulas, including linear branches. Output degree/mass bounds are explicit; split separable inputs give exact product degree and a bounded suitable direction. |
| [`Algebra.SeparableSpace`](LeanCanny/Algebra/SeparableSpace.lean), [`PrimitivePairSeparation`](LeanCanny/Algebra/PrimitivePairSeparation.lean), [`PrimitivePairSearch`](LeanCanny/Algebra/PrimitivePairSearch.lean), [`PrimitivePairSelected`](LeanCanny/Algebra/PrimitivePairSelected.lean) | A native polynomial-space search selects `c ≤ (d1*d2)^2` by testing separability of the actual integer resultant. All intermediate height bounds and coefficient readers follow from source readers with FP degree/height controls. Split separable inputs guarantee success. The space-computed direction feeds subsequent resultant and coordinate coefficient routines through prepared contexts. |
| [`Algebra.SubresultantGCDGeneral`](LeanCanny/Algebra/SubresultantGCDGeneral.lean), [`PolynomialGCDData`](LeanCanny/Algebra/PolynomialGCDData.lean), [`PolynomialGCDDegreeSpace`](LeanCanny/Algebra/PolynomialGCDDegreeSpace.lean), [`PolynomialGCDCoefficientSpace`](LeanCanny/Algebra/PolynomialGCDCoefficientSpace.lean) | For a nonzero smaller-degree right input, the first nonzero principal coefficient identifies the rational GCD degree. Its coefficient form is an integer representative of the GCD with explicit degree/height bounds, including the terminal divisor case. Native polynomial-space scans and coefficient determinants compute both degree and coefficient residues from source readers. |
| [`Algebra.SquarefreePart`](LeanCanny/Algebra/SquarefreePart.lean), [`SquarefreePartDegreeSpace`](LeanCanny/Algebra/SquarefreePartDegreeSpace.lean) | The canonical quotient `p/gcd(p,p')` is nonzero and separable for nonzero `p`, preserves all roots in characteristic-zero field extensions, and has native polynomial-space degree computation from original integer coefficient readers. |
| [`Algebra.CoefficientMinorSpace`](LeanCanny/Algebra/CoefficientMinorSpace.lean), [`CoefficientFormSpace`](LeanCanny/Algebra/CoefficientFormSpace.lean) | A selected first row extends principal-minor access to every coefficient of a subresultant coefficient form, including terminal orders and the empty determinant. Original coefficient children need only polynomial space. |
| [`Algebra.ScaledPolynomialQuotient`](LeanCanny/Algebra/ScaledPolynomialQuotient.lean), [`ScaledPolynomialQuotientSpace`](LeanCanny/Algebra/ScaledPolynomialQuotientSpace.lean) | Triangular Cramer determinants compute a leading-coefficient power times the exact quotient. Native residue evaluation uses source coefficient readers without inverses, so composite moduli and modular degree drops are covered. |
| [`Algebra.ScaledSquarefree`](LeanCanny/Algebra/ScaledSquarefree.lean), [`ScaledSquarefreeSpace`](LeanCanny/Algebra/ScaledSquarefreeSpace.lean), [`ScaledSquarefreeBounds`](LeanCanny/Algebra/ScaledSquarefreeBounds.lean) | Complete integer square-free preprocessing from native coefficient readers and FP input degree/height controls: output coefficients and exact degrees use polynomial space, an FP height bound is derived, and nonzero inputs give nonzero separable outputs preserving roots in every characteristic-zero field. Constant inputs are included. |
| [`Algebra.ValidatedPolynomialDegree`](LeanCanny/Algebra/ValidatedPolynomialDegree.lean), [`PreprocessedPairReaders`](LeanCanny/Algebra/PreprocessedPairReaders.lean), [`PreprocessedPair`](LeanCanny/Algebra/PreprocessedPair.lean) | Arbitrary nonzero integer input polynomials with FP degree/height controls and polynomial-space coefficient readers feed a complete two-input construction: square-free preprocessing, separating-direction search, and modular readers for the parameter and all coordinate polynomials. Every parameter root decodes to roots of the original inputs with a nonzero denominator. Checked stored degrees preserve exact FP metadata on malformed contexts too. |
| [`Algebra.PreprocessedPairProperties`](LeanCanny/Algebra/PreprocessedPairProperties.lean), [`PreprocessedPairBounds`](LeanCanny/Algebra/PreprocessedPairBounds.lean), [`PreprocessedPairCoordinateBounds`](LeanCanny/Algebra/PreprocessedPairCoordinateBounds.lean), [`PreprocessedPairReusable`](LeanCanny/Algebra/PreprocessedPairReusable.lean) | The computed parameter is nonzero and separable over every characteristic-zero field, with exact degree equal to the product of the square-free input degrees. Its degree has a native space evaluator. FP height writers bound the parameter coefficients and all coordinate masses using only original source controls; coordinate degrees are at most the product of the original degrees plus two. The output becomes a reusable checked polynomial family with full native readers. This proves fixed-stage composition, not uniform variable-depth evaluation. |
| [`Computation.PolyTimeBinaryNat`](LeanCanny/Computation/PolyTimeBinaryNat.lean), [`Algebra.CannyResultantBudget`](LeanCanny/Algebra/CannyResultantBudget.lean), [`ValidatedPolynomialReaders`](LeanCanny/Algebra/ValidatedPolynomialReaders.lean) | Binary natural outputs use Complexitylib2's native FP class directly. Addition, multiplication, binary sizes, and powers with unary exponents certify resultant height formulas from upper degree/direction bounds. Checked-family readers accept space-computed exact degrees while keeping their metadata FP. |
| [`Algebra.PrimitivePairConstruction`](LeanCanny/Algebra/PrimitivePairConstruction.lean), [`SeparableIntegerPolynomial`](LeanCanny/Algebra/SeparableIntegerPolynomial.lean), [`SeparableIntegerPolynomialField`](LeanCanny/Algebra/SeparableIntegerPolynomialField.lean) | The canonical direction depends only on the two integer polynomials and agrees with the native bounded scan. Separable integer polynomials are closed under this explicit resultant operation, with exact product degree. Integer rational decoding and shear encoding are inverse on roots in every characteristic-zero field, including the reals; an algebraic-closure embedding supplies the splitting proof. |
| [`Algebra.BalancedPrimitiveTree`](LeanCanny/Algebra/BalancedPrimitiveTree.lean), [`BalancedPrimitiveCoordinates`](LeanCanny/Algebra/BalancedPrimitiveCoordinates.lean), [`BalancedPrimitiveVectors`](LeanCanny/Algebra/BalancedPrimitiveVectors.lean) | Balanced repeated pair construction gives a separable integer parameter whose degree is the product of its leaf degrees. Its roots correspond bijectively to tuples of leaf roots. Indexed decoding uses nested explicit rational pair formulas; flattened polynomials are supplied below. Uniform native space evaluation remains open. |
| [`Algebra.FiniteAnnihilatorTree`](LeanCanny/Algebra/FiniteAnnihilatorTree.lean), [`FiniteAnnihilatorEquiv`](LeanCanny/Algebra/FiniteAnnihilatorEquiv.lean) | Any finite family of nonzero integer annihilants has an explicit balanced parameter: preprocess the leaves once and pad with X. Height is `n.size`, padded width is at most `2*(n+1)`, and degree is the product of the square-free degrees, at most `D^n` when original degrees are at most D. Parameter roots and vectors of original-polynomial roots are in bijection over every characteristic-zero field. The empty family has parameter X. No uniform coefficient-space bound is asserted. |
| [`Algebra.UnivariateRationalComposition`](LeanCanny/Algebra/UnivariateRationalComposition.lean), [`SeparableIntegerCoordinates`](LeanCanny/Algebra/SeparableIntegerCoordinates.lean), [`BalancedPrimitivePolynomials`](LeanCanny/Algebra/BalancedPrimitivePolynomials.lean), [`FiniteAnnihilatorPolynomials`](LeanCanny/Algebra/FiniteAnnihilatorPolynomials.lean) | Explicit common-exponent denominator clearing flattens every balanced coordinate to integer numerator/denominator polynomials. They agree with nested decoding and have nonzero denominators at every parameter root over any characteristic-zero field. Original degree bound D≥1 gives coordinate degrees at most `(D+2)^(4*(n+1))`. Clearing at a fixed exponent commutes with coefficient maps; composition has explicit degree and mass bounds. Source-derived heights are supplied below; uniform coefficient readers remain open. |
| [`Algebra.FiniteAnnihilatorFiltering`](LeanCanny/Algebra/FiniteAnnihilatorFiltering.lean) | Fixed even allowances clear arbitrary multivariate constraints in the explicit integer coordinates. At parameter roots, the univariate queries preserve zeros over characteristic-zero fields and signs over ℝ, with derived degree bounds. A supplied nonzero coordinate-annihilator family yields an exact equivalence between system solvability and a parameter root satisfying all cleared queries. The uniform space evaluator and actual tube specialization remain open. |
| [`Algebra.UniformPrimitivePairBounds`](LeanCanny/Algebra/UniformPrimitivePairBounds.lean), [`SeparableIntegerUniformBounds`](LeanCanny/Algebra/SeparableIntegerUniformBounds.lean), [`SquarefreeUniformBounds`](LeanCanny/Algebra/SquarefreeUniformBounds.lean), [`BalancedPrimitiveMass`](LeanCanny/Algebra/BalancedPrimitiveMass.lean) | A common bound T≥4 controls parameter degrees/mass exponents and flattened coordinate degrees/mass exponents. A pair step uses T^16, and height h uses `T^(16^h)`. The estimates include integer square-free preprocessing, both direct coordinate branches, and all denominator-cleared compositions. |
| [`Algebra.FiniteAnnihilatorHeight`](LeanCanny/Algebra/FiniteAnnihilatorHeight.lean) | Original degrees ≤D and coefficient magnitudes ≤`2^b` give the bound `H=(D+b+4)^(256*(n+1)^4)` on parameter and coordinate degrees, and mass ≤`2^H`. The same H covers every subtree of height ≤n.size. Cleared query mass exponents are derived too. The binary H writer is native FP for binary D,b controls and unary n. |
| [`Algebra.FiniteAnnihilatorDegreeSpace`](LeanCanny/Algebra/FiniteAnnihilatorDegreeSpace.lean) | One native bounded fold computes the exact finite-family parameter degree for an input-dependent unary count. Indexed original-polynomial readers and an FP binary degree bound suffice; square-free degree children may use arbitrary time in polynomial space. The accumulator is bounded by `(D+1)^n`, and no execution clocks are exposed. Uniform coefficient evaluation remains open. |
| [`Algebra.UnivariateRationalSpace`](LeanCanny/Algebra/UnivariateRationalSpace.lean), [`UnivariateRationalSpaceExponent`](LeanCanny/Algebra/UnivariateRationalSpaceExponent.lean) | Complete native modular coefficient evaluation of the clearing sum `Σ_{k≤e} pₖ*n^k*d^(e-k)`. Source, numerator, and denominator residues need only polynomial space. The clearing exponent may itself be space-computed; prepared contexts supply FP binary loop controls. Arbitrary positive moduli, including modulus one, are covered without expanding polynomials. |
| [`Algebra.IntegerPolynomialDegreeSpace`](LeanCanny/Algebra/IntegerPolynomialDegreeSpace.lean), [`RationalCoordinateSpace`](LeanCanny/Algebra/RationalCoordinateSpace.lean) | Native coefficient-zero scans recover actual degrees from polynomial-space residues and FP degree/mass bounds, including zero polynomials. Complete modular numerator/denominator readers compute actual rational-coordinate composition from four space-bounded coefficient children. Its common clearing exponent is computed internally; an FP exact degree or a child time bound is unnecessary. Applying this stage uniformly at input-dependent tree depth remains open. |
| [`Computation.RecursiveStack`](LeanCanny/Computation/RecursiveStack.lean), [`RecursiveStackPotential`](LeanCanny/Computation/RecursiveStackPotential.lean), [`RecursiveStackBounds`](LeanCanny/Computation/RecursiveStackBounds.lean), [`RecursiveStackStepSpace`](LeanCanny/Computation/RecursiveStackStepSpace.lean), [`RecursiveStackSpace`](LeanCanny/Computation/RecursiveStackSpace.lean) | A uniform native space evaluator supports input-dependent recursive depth and arbitrary polynomial-space instruction/reply routines. Semantic frame values are preserved, every running transition strictly decreases a potential, and rank bounds stack depth. Frame/result length bound B and rank bound R give encoded state size at most `5+4*B+R*(2*B+1)`. Canny stage instantiation remains open. |
| [`Computation.HaltingDistance`](LeanCanny/Computation/HaltingDistance.lean), [`RecursiveController`](LeanCanny/Computation/RecursiveController.lean), [`RecursiveControllerSpace`](LeanCanny/Computation/RecursiveControllerSpace.lean), [`Algebra.MatrixPowerRecursiveController`](LeanCanny/Algebra/MatrixPowerRecursiveController.lean), [`RecursiveMatrixPower`](LeanCanny/Algebra/RecursiveMatrixPower.lean), [`RecursiveMatrixPowerSpace`](LeanCanny/Algebra/RecursiveMatrixPowerSpace.lean) | Resumable streamed controllers issue recursive task queries and install replies without storing a clock. The actual matrix-power controller supplies a concrete instance, preserving its exact logical stopping index, power-entry answer, and quadratic state bound. A ranked graph of matrix-power and native space-bounded base tasks has one uniform native space evaluator. Unary FP bounds on task words, metadata bit lengths, and rank suffice; no certificate for recursive entry answers is assumed. |
| [`Algebra.PolynomialPowerRecursiveStage`](LeanCanny/Algebra/PolynomialPowerRecursiveStage.lean), [`BerkowitzDeterminantRecursiveStage`](LeanCanny/Algebra/BerkowitzDeterminantRecursiveStage.lean), [`BerkowitzFactorRecursiveStage`](LeanCanny/Algebra/BerkowitzFactorRecursiveStage.lean), [`Computation.SingleCallController`](LeanCanny/Computation/SingleCallController.lean) | Resumable polynomial-power and determinant coefficient stages delegate flattened matrix entries/factors to task queries. Their mathematical runs return the actual coefficients, preserve the original context, halt within the explicit logical power budget, and retain the quadratic state bound. A Berkowitz factor selector makes at most one diagonal/moment request and applies FP modular negation. Native local certificates do not assume computation certificates for any requested answers. Uniform closure for Canny's full graph remains open. |
| [`Algebra.MatrixMomentTaskRouting`](LeanCanny/Algebra/MatrixMomentTaskRouting.lean), [`PolynomialMomentRecursiveStage`](LeanCanny/Algebra/PolynomialMomentRecursiveStage.lean), [`BerkowitzMomentRecursiveStage`](LeanCanny/Algebra/BerkowitzMomentRecursiveStage.lean), [`Computation.ControllerDispatch`](LeanCanny/Computation/ControllerDispatch.lean), [`Algebra.BerkowitzTaskDispatch`](LeanCanny/Algebra/BerkowitzTaskDispatch.lean) | Moment guards route scalar coefficient requests to zero or original row/column/matrix coefficients, including empty trailing blocks. The actual Berkowitz moment has resumable correctness, halting, and quadratic storage contracts. Native dispatch preserves each selected stage's transcript across different state types and uses fixed defaults for inactive stages. One tagged determinant/factor/moment/source controller has native local certificates and proved oracle-run halting/output correctness under an explicit source-controller contract. Uniform graph rank/size bounds and Canny's source-controller instantiation remain open. |
| [`Algebra.BerkowitzTaskStorage`](LeanCanny/Algebra/BerkowitzTaskStorage.lean), [`BerkowitzTaskOrbitBounds`](LeanCanny/Algebra/BerkowitzTaskOrbitBounds.lean), [`BerkowitzTaskSpace`](LeanCanny/Algebra/BerkowitzTaskSpace.lean) | The mixed dispatcher has encoded length at most `32+2*L+c`, where c is the source default's encoded length. Task/reply bound K, metadata bit bound M, and source-state bound V give `L=3*K+4+64*(M+1)^2+V`; factor reply bounds follow from query closure. Internal logical budgets are at most `2^((M+2)*M+1)`. Ranked query closure and native common bound writers yield one uniform native space evaluator, determinant readers, and a zero-language decider. The source answer function is not assumed space-computable. Canny's concrete source controller and graph contracts remain open. |
| [`Algebra.CannyResultantInteger`](LeanCanny/Algebra/CannyResultantInteger.lean) | Zero testing for a selected integer coefficient of `cannyResultant` belongs to PSPACE. FP source coefficient-bit budgets determine the resultant coefficient budget through binary arithmetic and word lengths. The certified modulus scan tests the concrete Canny residue decider over `1,...,2*B+4`, accounting for all nested evaluator states. |
| [`Algebra.BinomialPower`](LeanCanny/Algebra/BinomialPower.lean), [`BinomialResidue`](LeanCanny/Algebra/BinomialResidue.lean) | The nth power of the lower bidiagonal matrix with diagonal and subdiagonal one contains `choose n k` at row `k`, column zero, in dimension `k+1`. An explicit FP entry accessor and binary field writers instantiate modular powering to return the complete binomial residue with a `SpaceFunction` certificate. It handles all words, modulus one, and `k>n`; its zero-test language is in PSPACE. |
| [`Algebra.ShiftCoefficientFP`](LeanCanny/Algebra/ShiftCoefficientFP.lean), [`ShiftCoefficientResidue`](LeanCanny/Algebra/ShiftCoefficientResidue.lean) | A certified space-bounded evaluator returns the coefficient of `x^i θ^j` in `p(θ-c*x)` modulo a positive binary modulus. It retains the query while the binomial child runs, then performs FP coefficient lookup, negative-direction powering, and modular multiplication. The contract requires FP original-coefficient residue access and a canonical FP direction writer. Result correctness and modular zero testing in PSPACE hold on every binary input. |

The full equation compiler is now certified in polynomial time. It pushes negations
to atoms, concatenates conjunctions, and masks disjunction branches using fresh Boolean
selectors. It introduces sums of squares once at the end, avoiding exponential tree
copying. Both equation-system satisfiability and single-equation satisfiability are
∃ℝ-complete under Complexitylib2's polynomial-time many-one reductions.

The certified entry points are `EquationCompiler.compileTerms` and
`EquationCompiler.toSingleEquation`. Their fresh-variable counter begins at the
normalized formula's encoded length, reserving all original indices. Every complete
intermediate state has a cubic bit-length bound. The earlier `500*(n+1)^3` output-size
theorem describes `Formula.singleEquation`, whose counter begins at the formula's arity.

The grammar checker agrees with the original decoder and validates canonical integer
payloads. It accepts well-formed unsatisfiable formulas; real satisfiability remains
the decision problem. Negation normalization copies arithmetic payloads unchanged.

The parameter polynomial in Lemma 2.1 is now the specified normalized Sylvester
resultant, with its roots, degree, and separability proved. The polynomial-coordinate
existence proof uses Galois descent and interpolation. The explicit rational pair
coordinates below use the computed recovery polynomials. Linear-GCD coefficient
recovery is also verified. The shifted input family's coefficients have
direct formulas and integer bit-length bounds. The unnormalized integer resultant
has at most `d₁*d₂+1` supported coefficients. Writing `N = d₁+d₂` and
`b = (d₁+1).size + d₁ + H₁.size + (c+1).size*d₁`, each coefficient's magnitude
has binary length at most `N.size*N + d₂*b + d₁*H₂.size + 1` when the input
coefficient magnitudes are bounded by `H₁,H₂`. Integer sign recovery is certified
below from residue access and a binary bit budget. Symbolic subresultant coefficients
have explicit bit bounds and certified modular evaluation. Direct linear branches
also handle degree-one recovery and zero directions. Magnitude bits now have certified
space-bounded evaluators under the same residue/budget contracts. The report's remaining
polylogarithmic-space computations remain open.

[`PrimitivePairCoordinates`](LeanCanny/Algebra/PrimitivePairCoordinates.lean)
uses the unnormalized resultant and the explicit integer-compatible coordinate
numerators `theta*D+c*N`, `-N`, with common denominator D. Here N,D are the
piecewise recovery polynomials, including direct linear cases. The denominator
is nonzero at every parameter root for a separating direction, and decoding is
bijective onto the Cartesian product of input root sets.
[`CoordinateRecoveryMap`](LeanCanny/Algebra/CoordinateRecoveryMap.lean) and
[`PrimitivePairInteger`](LeanCanny/Algebra/PrimitivePairInteger.lean) connect
these field identities to the actual integer polynomials. Coordinate degrees
and masses have explicit bounds in
[`PrimitivePairBounds`](LeanCanny/Algebra/PrimitivePairBounds.lean).

[`CannyCoefficientSpace`](LeanCanny/Algebra/CannyCoefficientSpace.lean) lets the
input coefficient routines use polynomial space and arbitrary time. Metadata
writers stay FP. [`PrimitivePairSpace`](LeanCanny/Algebra/PrimitivePairSpace.lean)
computes the resultant and all three integer coordinate polynomials' coefficient
residues from those children. [`PrimitivePairNested`](LeanCanny/Algebra/PrimitivePairNested.lean)
uses a computed resultant as a second resultant's left input; exact product
degrees supply its FP metadata.
[`PrimitivePairSearch`](LeanCanny/Algebra/PrimitivePairSearch.lean) now selects a
separating direction within `0..(d1*d2)^2` in polynomial space. It tests the actual
integer resultant against its derivative, deriving all height budgets from the
source bounds. The inputs must be split and separable over a characteristic-zero
field. [`PrimitivePairSelected`](LeanCanny/Algebra/PrimitivePairSelected.lean)
feeds that space-computed direction into subsequent coefficient routines.
[`SquarefreePart`](LeanCanny/Algebra/SquarefreePart.lean) proves the algebraic
preprocessing formula `p/gcd(p,p')`, including preservation of roots in
characteristic-zero extensions. A general subresultant theorem identifies the
GCD and supplies a bounded integer representative; native principal-minor scans
compute the GCD and quotient degrees from the original coefficient readers.
[`ScaledSquarefreeSpace`](LeanCanny/Algebra/ScaledSquarefreeSpace.lean) now computes
the integer square-free output through nested GCD and quotient determinants.
It includes constant inputs, and
[`ScaledSquarefreeBounds`](LeanCanny/Algebra/ScaledSquarefreeBounds.lean) derives
an FP output-height bound from the input degree and height controls.
[`PreprocessedPair`](LeanCanny/Algebra/PreprocessedPair.lean) composes these steps
for arbitrary nonzero integer inputs. It computes both square-free degrees in
space, stores them in a prepared context, and validates them before coefficient
access. An invalid degree selects `X^d-1` (or `1` for degree zero), so the existing
pair interface has exact FP degree fields and separable inputs on every binary
context. Correctly prepared contexts retain the actual square-free inputs.
The selected parameter and all three coordinate polynomials have native
polynomial-space coefficient readers; their root-recovery theorem returns roots
of the original inputs. This is a two-input composition theorem.
[`PreprocessedPairReusable`](LeanCanny/Algebra/PreprocessedPairReusable.lean)
now provides the full polynomial-reader interface for the computed output through
checked contexts. The parameter is nonzero and separable; its exact degree uses
polynomial space. Parameter heights and coordinate mass bounds are FP formulas
of the original degree/height controls, independent of the computed direction
and square-free degrees. Coordinate degrees are bounded by the original degree
product plus two. These contracts allow subsequent fixed algebraic stages.
[`FiniteAnnihilatorEquiv`](LeanCanny/Algebra/FiniteAnnihilatorEquiv.lean) now
gives a balanced algebraic construction for arbitrary finite nonzero annihilator
families. Square-free leaves are padded with X, preserving the Cartesian product
of their roots, including an empty family. The parameter has exact product degree,
and nested rational decoding gives a root bijection over the reals and every
characteristic-zero field. Uniform native coefficient evaluation at
input-dependent depth remains open.
[`FiniteAnnihilatorPolynomials`](LeanCanny/Algebra/FiniteAnnihilatorPolynomials.lean)
now flattens the nested ratios into integer coordinate polynomials, with nonzero
denominators at parameter roots and degree bound `(D+2)^(4*(n+1))` for D≥1.
[`FiniteAnnihilatorFiltering`](LeanCanny/Algebra/FiniteAnnihilatorFiltering.lean)
clears multivariate constraints in those coordinates, preserving zeros and real
signs. With valid coordinate annihilants, system solvability is equivalent to a
parameter root satisfying all the cleared constraints.
[`FiniteAnnihilatorHeight`](LeanCanny/Algebra/FiniteAnnihilatorHeight.lean)
now derives the common bound `H=(D+b+4)^(256*(n+1)^4)` from the original degrees
and coefficient heights. Parameter and coordinate masses are at most `2^H`,
including every subtree of height at most n.size. H has a native FP binary writer
for binary D,b controls and unary n.
[`FiniteAnnihilatorDegreeSpace`](LeanCanny/Algebra/FiniteAnnihilatorDegreeSpace.lean)
computes the exact parameter degree in polynomial space with one fold over the
space-computed square-free leaf degrees.
[`RationalCoordinateSpace`](LeanCanny/Algebra/RationalCoordinateSpace.lean)
now computes the complete coefficient streams of one actual coordinate
composition from four native space children. Coefficient-zero scans recover the
outer degree, and prepared contexts feed that space-computed clearing exponent
to the streamed sum/product evaluator. Uniform coefficient evaluation at
input-dependent tree depth and specialization to the actual tube annihilants remain open.

The streamed matrix-power primitive now has a verified continuation machine and
binary state-size bounds. Its abstract run takes at most
`2^((N.size+2)*e.size+1)` transitions. Entry access and scalar arithmetic count as
single abstract operations here. Certified query writers and modular arithmetic
implement the FP controls. The controller's semantic invariants bound its encoded
states. Native tidy space composition supports arbitrary space-bounded entry
computations; SpaceIteration.orbit handles the abstract stopping bound without
child execution clocks. Selected modular power-entry zero testing belongs to
Complexitylib2 PSPACE under the stated access contract on every input.
The division-free bordered recurrence behind
Berkowitz's algorithm is now proved, together with a recursive determinant reference.
Padded coefficient transformations give an ordered matrix product whose first
column contains the characteristic coefficients. `Berkowitz.balancedDeterminant`
recovers the determinant using product-entry recursion of height `n.size`.
The layered construction reduces that ordered product to the existing streamed
power machine, so no separate outer-product controller is needed. Its matrix has
dimension `(n+1)^2`, and stored residue states have at most
`64*(3*n.size+m.size+2)^2` bits. The abstract clock is at most
`2^((2*n.size+3)*n.size+1)`, counting entry access as one operation.
Direct trailing-block access now agrees with the recursive factor specification.
The nontrivial moment `r A^k c` is one power entry after adding a source and sink.
Its uniform child controller has FP initialization, transition, halting test,
result extraction, and modular negation, given certified binary fields and
row/column/matrix access.
For inner dimension `d`, exponent `k`, modulus `m`, and context `c`, every child
packet has at most `2*c.length+2+64*((d+2).size+(k+2).size+m.size+1)^2` bits.
Binary division/remainder, query decoding, and case selection now have FP
certificates. The offset writers supply exactly the trailing block and border
vectors from the original matrix, giving certified moment-child callbacks.
The factor evaluator composes immediate cases with the scalar-moment evaluator.
Berkowitz.ModularAccess.zeroLanguage_mem_PSPACE then uses the same native
matrix-power evaluator for the layered construction. Its access contract requires
canonical dimension/modulus fields and correct original matrix entries on every
input, with a nonzero modulus. It assumes no FP evaluator for whole factor entries.

`Berkowitz.IntegerAccess.zeroLanguage_mem_PSPACE` extends the result to integer
determinant zero testing. Its canonical FP budget field bounds the determinant's
magnitude bit length; the entry routine supplies residues modulo every positive
binary modulus. The integer entries need not fit in polynomial space. The
certified scan tests only the moduli `1,...,2*B+4`, where `B` is that bit budget.
An FP budget word gives polynomial-length modulus counters and exponentially many
calls. The combined bound includes the saved scan parent, modular controller,
and factor child. These contracts cover all input strings; concrete formats
still must supply validation/defaults and prove the access and budget properties.
The sign and magnitude-bit evaluators consume these residue/budget contracts.
Canny's remaining algebraic and geometric arguments remain open.

`Resultant.Access.zeroLanguage_mem_PSPACE` instantiates the integer determinant
theorem with streamed Sylvester access. Both degree parameters and a common
coefficient magnitude-bit budget are FP fields; coefficient residues must have
uniform FP access on all modular contexts and indices. The determinant budget
is computed from these fields. The main theorem retains the specified degree
parameters even when specialization lowers a polynomial's degree; the ordinary
resultant follows when those parameters equal the actual degrees. This is zero
testing of integer resultants. The symbolic modular coefficient evaluator below
extends this pipeline. Concrete residue algorithms for the report's remaining
constructed polynomial families still require proofs.

`BinomialResidue.evaluator` now supplies one ingredient of the shifted-coefficient
formula: a certified space-bounded routine returning `choose n k mod m`. Input
`pair n (pair k b)` uses arbitrary little-endian words and specifies positive
modulus `fromBitsLE b + 1`. Its bidiagonal matrix entries have a concrete FP
implementation. No Pascal row or unreduced binomial coefficient is stored.
The output certificate is a native tidy space proof and composes directly
with other space-bounded routines.
`ShiftCoefficientBits.certified` now composes it with the other factors of
`choose(i+j,i) * p[i+j] * (-c)^i`. The original query is retained in an explicit
paired state. Repeated squaring and modular multiplication are FP, as are the
required direction writer and original-coefficient residue routine. Input
`pair q (pair i j)` uses modular context `q = pair originalContext b`, with
positive modulus `fromBitsLE b+1`; the result agrees with the existing
shifted-polynomial identity on all words. Its modular zero-test language is
in PSPACE. `MatrixPower.ModularAccess.evaluatorWithEntry` now accepts a
`SpaceFunction` entry routine and proves the combined matrix-power certificate.
`Resultant.Access.integer_entryEvaluator` supplies a Sylvester entry routine
from certified coefficient children. `Berkowitz.ModularAccess.deciderWithEntry`
now propagates space-bounded original-entry calls through the augmented moment,
factor, and outer power evaluators. The integer modulus scan retains the same
contract. `Resultant.Access.zeroLanguage_mem_PSPACE_of_evaluators` therefore
proves integer resultant zero testing from space-bounded coefficient routines,
with only degree and bit-budget fields required to be FP.
`ResultantPolynomial.ModularAccess.evaluator` now returns selected symbolic
resultant coefficients over a positive modulus from space-bounded bivariate
input coefficient routines. `CannyResultantBits.Access.evaluator` specializes it
to the actual `cannyResultant` using the shifted-coefficient child and FP
original-coefficient residue access. `CannyResultantBits.IntegerAccess.decider`
adds a budget computed from source coefficient-bit bounds and the modulus scan,
giving PSPACE zero testing of the actual integer coefficient.
`IntegerSignBits.evaluator` now constructs local CRT numerators and computes the
required truncated-sum bit from certified residue access and an FP bit budget.
`CannyResultantBits.IntegerAccess.signumEvaluator` combines this negativity test
with the zero decider, returning the full three-way sign of that coefficient.
Its negative and positive languages belong to PSPACE under the same source-access
and bit-budget contracts. `IntegerDigitBits.evaluator` now supplies magnitude bits
under the same contracts, with actual resultant and coordinate specializations.

Binary addition, multiplication, comparison, subtraction, division, and modular reduction
now have uniform `FP` certificates, with exact semantics and bounds on intermediate
states. Their modular multiply-accumulate composition supplies the scalar arithmetic
callback required by the modular power machine.

The small-parameter pipeline now has an effective specialization as well.
[`EffectiveInfinitesimalSign`](LeanCanny/Algebra/EffectiveInfinitesimalSign.lean)
proves that an integer polynomial of coefficient mass at most `2^b` has its
trailing coefficient's sign throughout `0 < β ≤ 2^(-s)` whenever `b < s`.
[`DyadicSpecialization`](LeanCanny/Algebra/DyadicSpecialization.lean) and
[`DyadicSpecializationSpace`](LeanCanny/Algebra/DyadicSpecializationSpace.lean)
clear denominators by `2^(s*D)` and compute the resulting integer's residues and
sign from space-bounded original coefficient readers and FP binary bounds.

[`DyadicPolynomialSpecialization`](LeanCanny/Algebra/DyadicPolynomialSpecialization.lean)
applies the same factor to every coefficient of a parameterized root polynomial;
it proves degree preservation under the smallness bound and derives coefficient
mass bounds.
[`DyadicPolynomialSpace`](LeanCanny/Algebra/DyadicPolynomialSpace.lean) supplies
its uniform coefficient evaluator.
[`DyadicTarskiSpace`](LeanCanny/Algebra/DyadicTarskiSpace.lean) composes these
readers with the complete Tarski evaluator, computing the exact real-root query
at the selected dyadic parameter. Its positive-query language belongs to PSPACE.

[`DyadicSignPatternSource`](LeanCanny/Algebra/DyadicSignPatternSource.lean) and
[`DyadicSignPatternSpace`](LeanCanny/Algebra/DyadicSignPatternSpace.lean) extend
this to exact counts of distinct real roots realizing an indexed sign pattern,
with a unary FP bound on the query-family size. Positive counts and guarded
realizability are in PSPACE. Under the root's smallness bound, a nonzero original
root polynomial suffices for unguarded realizability; specialization preserves
its nonvanishing.

All specialized coefficient routines and budgets are derived from the original
bivariate sources.

[`ParameterizedTarski`](LeanCanny/Algebra/ParameterizedTarski.lean) now proves
eventual query stability from explicit polynomial tests in β: the leading
coefficients of the head and symbolic pseudo-seed and their signed principal
coefficients. A budget formed from their coefficient masses gives a dyadic
interval throughout which the query equals the trailing-coefficient sign formula.
[`ParameterizedSignPatterns`](LeanCanny/Algebra/ParameterizedSignPatterns.lean)
takes a maximum over the ternary product queries. One interval works for every
sign pattern; exact root counts are constant there, and realizability is constant
for a nonzero symbolic root polynomial. These are mathematical stability results.
[`NestedCoefficientMass`](LeanCanny/Algebra/NestedCoefficientMass.lean) and
[`PrincipalParameterMass`](LeanCanny/Algebra/PrincipalParameterMass.lean) bound
the whole coefficient mass of the bivariate pseudo-seed and its principal tests.
[`ParameterSourceBounds`](LeanCanny/Algebra/ParameterSourceBounds.lean) derives
a uniform test bound from the original outer degrees and coefficient masses,
including every ternary product query. No test-polynomial enumeration or β-degree
is needed for this bound.
[`ParameterSourceBudget`](LeanCanny/Algebra/ParameterSourceBudget.lean) gives
its FP binary writer on arbitrary metadata words.

[`InfinitesimalRootCountSpace`](LeanCanny/Algebra/InfinitesimalRootCountSpace.lean)
chooses the dyadic exponent internally from these original source bounds and
returns the exact eventual root-sign count in polynomial space. Its only
space-bounded arithmetic sources are the original bivariate coefficient readers.
The query-family size retains the explicit unary FP bound.
[`InfinitesimalRootPSPACE`](LeanCanny/Algebra/InfinitesimalRootPSPACE.lean) proves
that a positive count is equivalent, for a nonzero symbolic root polynomial,
to a realizing real root for every sufficiently small positive β. The guarded
language includes symbolic nonvanishing and belongs to PSPACE on all inputs;
the unguarded theorem assumes nonvanishing on every input. Canny's stronger
implicit family bounds and effective critical-point algorithm remain open.

The compactness stage now starts from the compiled equation for every encoded
ETR input.
[`CubeCoordinates`](LeanCanny/Geometry/CubeCoordinates.lean) proves that
`y/(1-y²)` maps the open unit cube onto the full real domain, with an explicit
coordinate inverse and a common positive boundary margin for every finite tuple.
[`CubePolynomial`](LeanCanny/Geometry/CubePolynomial.lean) gives the actual
denominator-cleared integer multivariate polynomial, preserves its zeros and
signs on the open cube, and bounds its degree by `4*n*degree(p)`.
Its inner-cube zero sets are compact, and every linear functional attains a
maximum on each nonempty such set.

[`FinitePolynomial`](LeanCanny/ETR/FinitePolynomial.lean) and
[`CompactSource`](LeanCanny/ETR/CompactSource.lean) connect this construction to
the verified ETR compiler. An input is a yes-instance exactly when some positive
margin gives a nonempty compact zero set; every smaller positive margin also
works. This includes malformed-input rejection and zero-variable equations.
Dimension and degree upper bounds have FP binary writers, using the normalized
source length.

[`CompactApproximation`](LeanCanny/Geometry/CompactApproximation.lean) proves
exact feasibility from arbitrarily accurate approximations on a compact set.
[`PolynomialPerturbation`](LeanCanny/Geometry/PolynomialPerturbation.lean)
applies it to the equation/cube system with independent shifts of prescribed
squared radius. Nonemptiness is equivalent to nonemptiness for every sufficiently
small positive radius, and each fixed-radius perturbed set is compact.
[`PerturbationPolynomials`](LeanCanny/Geometry/PerturbationPolynomials.lean)
gives the actual integer polynomials, with ε and δ as parameter variables.
[`PerturbedSource`](LeanCanny/ETR/PerturbedSource.lean) proves this equivalence
for every encoded ETR input, with FP bounds on variable count, inequality count,
and degree.

[`AdditiveSubmersion`](LeanCanny/Geometry/AdditiveSubmersion.lean) proves that the
full additive family is smooth and its derivative is surjective, using the shift
variables. This includes the compiled ETR family.
[`RadiusLinearization`](LeanCanny/Geometry/RadiusLinearization.lean) and
[`SquaredRadius`](LeanCanny/Geometry/SquaredRadius.lean) compute the joint
derivative including the radius parameter and prove it is onto when δ is nonzero.
[`ActiveRadiusLinearization`](LeanCanny/Geometry/ActiveRadiusLinearization.lean)
gives the fixed-radius criterion for each active constraint set.

[`ActiveRadiusCritical`](LeanCanny/Geometry/ActiveRadiusCritical.lean) proves
that a singular active-set point makes δ² a critical value of the sum of squares
of the unshifted active constraints.
[`CriticalEnergyPolynomial`](LeanCanny/Geometry/CriticalEnergyPolynomial.lean)
realizes that function as an integer polynomial.
[`RadiusSource`](LeanCanny/ETR/RadiusSource.lean) instantiates these results for
all encoded ETR inputs and supplies an FP degree bound.

[`PolynomialCalculus`](LeanCanny/Geometry/PolynomialCalculus.lean) identifies
analytic critical points with common zeros of formal partial derivatives.
[`SpatialPolynomialCalculus`](LeanCanny/Geometry/SpatialPolynomialCalculus.lean)
proves the corresponding statement with the perturbation parameters fixed.
[`RadiusCriticalEquations`](LeanCanny/Geometry/RadiusCriticalEquations.lean)
gives the integer system consisting of the energy minus δ² and its spatial
partial derivatives; every singular active point yields a common zero.
[`RadiusCriticalSource`](LeanCanny/ETR/RadiusCriticalSource.lean) supplies the
system for every encoded ETR input, with FP upper bounds on equation count and
degree. [`PartialDerivativeDegree`](LeanCanny/Algebra/PartialDerivativeDegree.lean)
proves that partial derivatives have degree at most the original degree minus one.
[`CriticalValueAnnihilator`](LeanCanny/Algebra/CriticalValueAnnihilator.lean)
proves existence of a nonzero polynomial annihilating all critical values, using
derivations and finitely many minimal primes of the gradient ideal. This proves
finiteness of polynomial critical values in characteristic zero.
[`PolynomialCriticalValues`](LeanCanny/Geometry/PolynomialCriticalValues.lean)
applies this to each specialized active energy.
[`RegularRadius`](LeanCanny/Geometry/RegularRadius.lean) gives a common positive
interval where every active augmented derivative is surjective.
[`RegularRadiusSource`](LeanCanny/ETR/RegularRadiusSource.lean) proves that ETR
satisfiability is equivalent to nonemptiness throughout such a regular interval.
Effective radius bounds, streamed coefficient access for the new polynomials,
and effective critical-point sampling remain open.

[`ActiveExtremum`](LeanCanny/Geometry/ActiveExtremum.lean) localizes a maximum
to its active equality fiber and normalizes the Lagrange multipliers when the
constraint derivative is onto.
[`PerturbedCriticalPoint`](LeanCanny/Geometry/PerturbedCriticalPoint.lean)
applies this to compact regular perturbations.
[`CriticalPointSource`](LeanCanny/ETR/CriticalPointSource.lean) characterizes ETR
satisfiability by the existence of such critical maxima for every linear
projection throughout a small regular-radius interval.
[`ProjectionEquations`](LeanCanny/Algebra/ProjectionEquations.lean) constructs
the hypersurface projection system, with exactly n equations and degree at most
`max(degree(p),1)`, including direction variables.
[`ProjectionCritical`](LeanCanny/Geometry/ProjectionCritical.lean) proves that
local projection maxima on a regular hypersurface satisfy this system when the
base direction coordinate is one.

[`TubePolynomial`](LeanCanny/Geometry/TubePolynomial.lean) forms the sum of
squares of the active shifted constraints and the radius equation, minus α.
At α = 0, its zeros are exactly their common zeros.
[`RegularPolynomialLevels`](LeanCanny/Geometry/RegularPolynomialLevels.lean)
and [`TubeRegularity`](LeanCanny/Geometry/TubeRegularity.lean) give a common
interval of regular positive α levels for all active sets at fixed ε and δ.
[`TubeProjection`](LeanCanny/Geometry/TubeProjection.lean) applies the projection
equations to these tubes.
[`TubeExpanded`](LeanCanny/Geometry/TubeExpanded.lean) expands the parameter
coefficients into ordinary integer polynomials, preserving evaluation and point
derivatives; the full degree, including parameters and directions, is at most
`2*max(degree(p),2)`.
[`TubeSource`](LeanCanny/ETR/TubeSource.lean) supplies these systems for every
encoded ETR input, with FP upper-bound writers for equation count, variable count,
and degree.

[`CompactLevelConvergence`](LeanCanny/Geometry/CompactLevelConvergence.lean)
proves uniform compact control of small levels and approximate maxima.
[`LocalLevelApproximation`](LeanCanny/Geometry/LocalLevelApproximation.lean)
and [`CompactLevelMaxima`](LeanCanny/Geometry/CompactLevelMaxima.lean) produce
nearby local maxima on positive levels near a unique zero-level maximum.
[`TubeApproximation`](LeanCanny/Geometry/TubeApproximation.lean) supplies a
continuous radial path giving nearby tube levels at positive radius.
[`TubeConvergence`](LeanCanny/Geometry/TubeConvergence.lean) proves that strict
local projection maxima are approximated in every neighborhood by local tube
maxima satisfying the integer critical equations.
[`TubeSigns`](LeanCanny/Geometry/TubeSigns.lean) preserves positive inactive
constraints and proves that convergent tube samples with nonnegative inactive
constraints have feasible limits.
[`TubeConvergenceSource`](LeanCanny/ETR/TubeConvergenceSource.lean) instantiates
the approximation theorem for encoded ETR, with the strict local maximum
hypothesis explicit.

[`TubeBounds`](LeanCanny/Geometry/TubeBounds.lean) bounds small tube samples with
nonnegative inactive constraints in a common compact box: shifts have magnitude
at most δ+1 and spatial coordinates at most δ+3. For δ≤1 and α≤1, every coordinate
lies in [-4,4].
[`TubeFeasibility`](LeanCanny/Geometry/TubeFeasibility.lean) proves perturbed
feasibility from arbitrarily small tube samples, allowing their active sets to
vary. At nonnegative ε and positive δ, feasibility is also equivalent to one
fixed active set supplying samples with positive inactive constraints at every
sufficiently small positive α.
[`TubeProjectionFeasibility`](LeanCanny/Geometry/TubeProjectionFeasibility.lean)
extracts the tube equation from the integer projection system, proving soundness
of arbitrarily small projection-root samples.
[`TubeFeasibilitySource`](LeanCanny/ETR/TubeFeasibilitySource.lean) gives both
semantic ETR characterizations and projection-sampling soundness on all inputs.
[`IsolatedCriticalMaximum`](LeanCanny/Geometry/IsolatedCriticalMaximum.lean)
proves that finite normalized critical sets make local maxima strict on regular
smooth fibers. [`TubeCriticalMaximum`](LeanCanny/Geometry/TubeCriticalMaximum.lean)
applies this to the active constraints.
[`TubeCriticalSampling`](LeanCanny/Geometry/TubeCriticalSampling.lean) then gives
positive-inactive integer projection roots at every sufficiently small tube
level, with one fixed direction and active set.
[`TubeCriticalSamplingSource`](LeanCanny/ETR/TubeCriticalSamplingSource.lean)
gives the corresponding ETR equivalence under an explicit finite-critical-direction
hypothesis and retains finiteness of the chosen direction's active critical
sets; it requires no additional nondegeneracy assumption.

[`CompactSupportingProjection`](LeanCanny/Geometry/CompactSupportingProjection.lean)
proves that every nonempty compact set has a strict supporting linear projection
whose chosen coordinate is one. A farthest point from a center below the set in
that coordinate supplies the direction.
[`TubeSupportingSampling`](LeanCanny/Geometry/TubeSupportingSampling.lean) uses
this to prove existence of eventual positive-inactive projection roots without
a finite-critical-set hypothesis.
[`TubeSupportingSamplingSource`](LeanCanny/ETR/TubeSupportingSamplingSource.lean)
therefore gives unconditional semantic ETR equivalences for both arbitrarily
small projection roots and eventual roots with one fixed normalized direction
and active set. These are real existence statements.
Effective direction selection, parameter bounds, and the full sampling decision
procedure remain open. Tube/projection coefficient residues are supplied below.

[`MvCoefficientDerivation`](LeanCanny/Algebra/MvCoefficientDerivation.lean) and
[`FieldDerivationExtension`](LeanCanny/Algebra/FieldDerivationExtension.lean)
extend coefficient derivations through arbitrary characteristic-zero field
extensions. [`AlgebraicDerivative`](LeanCanny/Algebra/AlgebraicDerivative.lean)
proves that such derivations preserve algebraicity over the coefficient field.
[`CoordinateDerivation`](LeanCanny/Algebra/CoordinateDerivation.lean) differentiates
one generator of an algebraically independent family while fixing the others.
[`ProjectionCoordinateAlgebraic`](LeanCanny/Algebra/ProjectionCoordinateAlgebraic.lean)
uses these facts to prove that stationary point coordinates are algebraic over
the direction field, including normalized directions whose other coordinates
are algebraically independent.
[`FiniteAlgebraicZeros`](LeanCanny/Algebra/FiniteAlgebraicZeros.lean) converts
algebraicity in minimal-prime quotient fields into coordinate annihilators
and a finite zero set.
[`GenericProjectionFinite`](LeanCanny/Algebra/GenericProjectionFinite.lean) applies
this to normalized projection equations with a reciprocal variable excluding
singular roots.
[`FiniteProjectionRoots`](LeanCanny/Geometry/FiniteProjectionRoots.lean) proves
finiteness of all projection-system roots on a regular real hypersurface when
the non-base direction coordinates are algebraically independent over its
coefficient field.
[`TubeFiniteRoots`](LeanCanny/Geometry/TubeFiniteRoots.lean) gives this result for
the actual expanded integer tube systems on their common small-level regularity
interval, assuming the specialization factors through such a field. Existence
of the field and directions is supplied below; effective selection and bounds
remain open.

[`TubeParameterField`](LeanCanny/Geometry/TubeParameterField.lean) constructs the
countable real field obtained by adjoining ε, δ, and α to ℚ and factors tube
specialization through it.
[`IndependentRealDirections`](LeanCanny/Geometry/IndependentRealDirections.lean)
constructs independent real tuples inside any product of nonempty open intervals.
[`GenericDirectionNeighborhood`](LeanCanny/Geometry/GenericDirectionNeighborhood.lean)
keeps one coordinate normalized to one while approximating any normalized
direction.
[`TubeGenericDirections`](LeanCanny/Geometry/TubeGenericDirections.lean) therefore
proves that directions giving finite projection root sets for every active tube
are dense at each sufficiently small positive level. The directions may depend
on the level.
[`ProjectionContinuity`](LeanCanny/Geometry/ProjectionContinuity.lean) controls
direction changes uniformly on compact sets.
[`CompactLevelPerturbedMaxima`](LeanCanny/Geometry/CompactLevelPerturbedMaxima.lean)
shows that nearby continuous objectives retain small-level local maxima near
a unique zero-level maximum.
[`TubeFiniteSampling`](LeanCanny/Geometry/TubeFiniteSampling.lean) combines these
facts: one active set supplies positive-inactive samples at every sufficiently
small level, with a normalized real direction giving finite root sets for all
active sets. The direction may vary with the level.
[`TubeFiniteSamplingSource`](LeanCanny/ETR/TubeFiniteSamplingSource.lean) proves
this qualitative finite-sampling criterion equivalent to ETR satisfiability
on all encoded inputs. Effective tube projection direction search, root enumeration, parameter
bounds, and the full PSPACE decision procedure remain open.

[`FiniteFiberSpecialization`](LeanCanny/Algebra/FiniteFiberSpecialization.lean)
clears generic coordinate annihilators to the parameter ring. One nonzero
parameter element suffices to preserve finite fibers under every field
specialization where that element stays nonzero.
[`ProjectionFiniteSpecialization`](LeanCanny/Algebra/ProjectionFiniteSpecialization.lean)
applies this to symbolic normalized projection directions and gives a nonzero
exceptional polynomial whose nonvanishing ensures finite extended projection
fibers.
[`PolynomialGridAvoidance`](LeanCanny/Algebra/PolynomialGridAvoidance.lean) avoids
nonzero exceptional polynomials on the integer grid `0,…,B` when B bounds their
total degree, including finite families of conditions. A normalized direction
with natural-number coordinates and a finite extended projection fiber therefore
exists. Input-size bounds for the exceptional polynomial and for suitable
encoded direction choices remain open.

A separate finite-set result now bounds the choices needed for coordinate recovery.
The report's fixed symmetric shifts (equations (13)--(15)) can have spurious common
roots for every projection direction; the three points `(-1,0),(0,0),(1,0)` give a
verified example. Replacing the positive shift by a bounded positive weight gives
simultaneously separating root pairs and rational coordinate formulas. This repairs
that finite-set recovery step; it does not supply the multivariate eliminants, their
coefficient algorithms, or the remaining input-size bounds for critical sampling.

[`IntegerProjectionDirections`](LeanCanny/Geometry/IntegerProjectionDirections.lean)
gives one normalized natural-number direction with finite projection root sets
for every hypersurface in a finite regular family. It combines their exceptional
polynomials using the common-grid theorem.
[`TubeIntegerDirections`](LeanCanny/Geometry/TubeIntegerDirections.lean) applies
this to every active tube at each sufficiently small positive level. The finite
grid bound and direction may depend on the real parameters and level. A common
integer choice throughout an interval, preservation of a positive-inactive sample,
and an input-size bound remain open.

[`PolynomialRationalAvoidance`](LeanCanny/Geometry/PolynomialRationalAvoidance.lean)
places finite rational grids inside arbitrary open coordinate boxes and avoids
nonzero real exceptional polynomials there.
[`RationalProjectionDirections`](LeanCanny/Geometry/RationalProjectionDirections.lean)
therefore gives a normalized rational finite-root direction near any normalized
real direction, for a finite regular family.
[`TubeRationalDirections`](LeanCanny/Geometry/TubeRationalDirections.lean) applies
this to all active tubes at every sufficiently small positive level.
The compact sampling argument now accepts a direction predicate and retains
it in its witnesses, allowing these rational choices to be used without
duplicating the objective-stability proof. Effective numerator and denominator
bounds remain open.

[`TubeRationalSampling`](LeanCanny/Geometry/TubeRationalSampling.lean) retains
explicit rational direction tuples while preserving positive inactive signs.
One active set works throughout the small-level interval; each chosen rational
direction gives finite projection root sets for every active set, with a
suitable sample in one of them.
[`TubeRationalSamplingSource`](LeanCanny/ETR/TubeRationalSamplingSource.lean)
proves this criterion equivalent to ETR satisfiability on all encoded inputs.
This criterion allows the rational tuple to vary with the level.

[`UniformRationalProjectionDirections`](LeanCanny/Geometry/UniformRationalProjectionDirections.lean)
avoids a nonzero level coefficient of the joint exceptional polynomial. One
nearby rational direction therefore works throughout a small positive level
interval, for an entire finite hypersurface family.
[`TubeUniformRationalDirections`](LeanCanny/Geometry/TubeUniformRationalDirections.lean)
applies this to every active tube. The sampling-neighborhood lemma retains
positive inactive signs for every nearby normalized direction throughout a
common small interval.
[`TubeUniformRationalSampling`](LeanCanny/Geometry/TubeUniformRationalSampling.lean)
combines them: one active set and one rational direction supply finite root
sets containing suitable samples at every sufficiently small positive level.
[`TubeUniformRationalSamplingSource`](LeanCanny/ETR/TubeUniformRationalSamplingSource.lean)
proves the stronger criterion equivalent to encoded ETR satisfiability.
The direction may depend on epsilon and delta.
[`UniformExtendedProjectionDirections`](LeanCanny/Geometry/UniformExtendedProjectionDirections.lean)
and [`TubeUniformExtendedDirections`](LeanCanny/Geometry/TubeUniformExtendedDirections.lean)
preserve finiteness over every extension field of the reals, including algebraically
closed extensions. [`TubeRegularFiber`](LeanCanny/ETR/TubeRegularFiber.lean) identifies
the specialized regular spatial rows with the extended critical equations.
[`TubeCompiledAffineRoots`](LeanCanny/ETR/TubeCompiledAffineRoots.lean) transfers
finiteness through denominator clearing and the projection equation.
[`TubeCharacteristicGeometricPersistence`](LeanCanny/ETR/TubeCharacteristicGeometricPersistence.lean)
combines these results: one rational direction gives finite compiled fibers whenever
the substitution has nonzero denominators and realizes the chosen perturbation
parameters and direction. The lowest characteristic quotient coefficient therefore
vanishes at every affine root over an algebraically closed field, even at singular
roots.
[`TubeLevelPacket`](LeanCanny/ETR/TubeLevelPacket.lean) now supplies a concrete
constant-parameter family: rational epsilon, delta, and direction entries are
stored in fixed-width blocks, while alpha is the polynomial variable. Signed
numerators use two natural blocks and denominators use a successor, ensuring
nonvanishing. [`TubeLevelReaders`](LeanCanny/ETR/TubeLevelReaders.lean) certifies
uniform FP coefficient access and instantiates the existing substitution interface;
degree is at most one and the coefficient-bit allowance is W+1.
[`TubeLevelParameters`](LeanCanny/ETR/TubeLevelParameters.lean) proves the native
parameter identities over real extensions, and
[`TubeLevelPacking`](LeanCanny/ETR/TubeLevelPacking.lean) packs every rational
tuple exactly with a width derived from its component bit lengths.
[`TubeLevelFiniteFiber`](LeanCanny/ETR/TubeLevelFiniteFiber.lean) consequently
transfers geometric finiteness for the stored normalized direction without
additional substitution identities or denominator assumptions.
[`TubeLevelTuple`](LeanCanny/ETR/TubeLevelTuple.lean) packs prescribed epsilon,
delta, and direction values. If every coordinate has combined numerator/denominator
bit allowance at most B, a packet exists with length at most
`2*source.length + (5*parameterCount+2)*B + 8`.
[`TubeLevelChoice`](LeanCanny/ETR/TubeLevelChoice.lean) chooses one packet whose direction lies
near any normalized real direction. At fixed rational epsilon and delta its
compiled fibers are finite for every active set and real extension throughout
one common small positive alpha interval.
[`TubeLevelSampling`](LeanCanny/ETR/TubeLevelSampling.lean) preserves
positive-inactive geometric critical samples with the same packet and one fixed
active set throughout a common interval.
[`TubeLevelSamplingSource`](LeanCanny/ETR/TubeLevelSamplingSource.lean) proves
ETR equivalent to a positive rational epsilon for which every positive rational
delta admits these packet samples, on all bitstrings. The reverse implication
uses arbitrarily small rational radii and compactness.
[`TubeRegularSpatialLift`](LeanCanny/ETR/TubeRegularSpatialLift.lean) adjoins the
inverse base derivative. Regularity of the hypersurface and normalization of
the critical direction ensure this derivative is nonzero at projection roots.
[`TubeCompiledAffineLift`](LeanCanny/ETR/TubeCompiledAffineLift.lean) then adds the
linear projection coordinate and proves the compiled equations; decoding
recovers the original spatial tuple.
[`TubeLevelRootLift`](LeanCanny/ETR/TubeLevelRootLift.lean) applies these maps to
the stored packet on a common regular-level interval, for every active set
and added integer linear projection.
[`TubeLevelCompiledSampling`](LeanCanny/ETR/TubeLevelCompiledSampling.lean)
therefore strengthens the ETR criterion to actual compiled samples with the
same positive inactive signs.
[`TubeLevelEliminantSampling`](LeanCanny/ETR/TubeLevelEliminantSampling.lean)
proves that every compiled root annihilates the lowest-coefficient eliminant,
using finiteness over the complex numbers. The explicit dyadic specialization
threshold makes that polynomial nonzero. The same packet and mask work for
every added linear projection, with a possibly smaller interval for each one.
The projection polynomial's degree, and the number of distinct compiled
projection values, are at most the padded Macaulay dimension. No invertibility
of the full critical-system Jacobian is required. The resulting ETR equivalence
retains the compiled equations and inactive-sign tests; a root of the eliminant
alone is not asserted to be a valid sample. Source-size bounds on suitable
parameter tuples and levels, effective selection, effective algebraic coordinate
recovery, the full nested perturbation readers, and the full PSPACE algorithm
remain open.

[`FiniteSystemTransfer`](LeanCanny/Algebra/FiniteSystemTransfer.lean) proves that
finite full zero sets over an algebraically closed field acquire no new
solutions in larger fields. This removes the separate coordinate-algebraicity
hypothesis from completeness of rational univariate representations.
[`TubeFiniteSystemBaseChange`](LeanCanny/ETR/TubeFiniteSystemBaseChange.lean)
commutes coefficient extension with the actual compiled tube specialization.
[`TubeLevelCoordinates`](LeanCanny/ETR/TubeLevelCoordinates.lean) consequently
obtains integer univariate representations at rational tube levels from the
packet's finite complex fibers. Their real parameter roots correspond exactly
to compiled real points; all coordinate denominators are nonzero at these
roots. The theorem `TubeLevelSamplingSource.coordinates_correct` gives an exact
ETR criterion using decoded inactive-sign tests at sufficiently small rational
levels. Compactness supplies the reverse implication from rational levels
alone. These representations may depend on the level and added projection.
They are separate existential univariate representations, with no identification
with the computed lowest-coefficient eliminant. Effective construction,
coefficient-height bounds in the input size, and the computation's space bound
remain open.
[`TubeLevelSignQueries`](LeanCanny/ETR/TubeLevelSignQueries.lean) turns the decoded
inactive signs into integer univariate queries. It first multiplies the
constraints by the positive denominator of the stored rational epsilon, then
clears coordinate denominators using even powers. Active constraints contribute
one. The count of parameter roots realizing the all-positive pattern is
positive exactly when a compiled sample exists.
The theorem `TubeLevelSamplingSource.signCounts_correct` expresses ETR
correctness using these positive counts at small rational tube levels.
[`TubeLevelSignSpace`](LeanCanny/ETR/TubeLevelSignSpace.lean) applies the native
root-sign counter to these actual polynomials: certified coefficient readers
and binary degree/mass budgets give a count evaluator and a PSPACE sample
language. Query-count control follows from FP packet access and the source
arity. The requested pattern is constant. This certifies the final sign stage
under those contracts; it does not construct the coordinate representations or
their bounded coefficient readers from an ETR input.

[`RationalSubstitutionWith`](LeanCanny/Algebra/RationalSubstitutionWith.lean)
proves evaluation and budget bounds with explicit clearing allowances.
[`TubeLevelSignBounds`](LeanCanny/ETR/TubeLevelSignBounds.lean) uses the packet's
raw margin integers and a fixed allowance `D=8*N^2+4`, where N is the normalized
compiled source size. Let A be the compiled coordinate count, W the packet
width, and `Q=2*A*D`. Coordinate degrees at most E and coefficient masses at
most `2^b` give query degree at most `Q*E` and mass at most
`2^(W+N+2*N^2+4+Q*b)`. The binary budget writers are FP. The native sample
counter and PSPACE theorem therefore need only coordinate/root bounds and
coefficient readers; callers no longer supply separate bounds for the expanded
sign queries. Constructing the coordinate representations and their readers
with suitable original-input bounds remains open.

[`TubeSampleCoefficient`](LeanCanny/ETR/TubeSampleCoefficient.lean) reuses the
compact source reader in compiled sample coordinates. A guard rejects nonzero
exponents outside the original point block; dropping the two leading blocks
then prepares the source query. [`FixedWidthMonomial`](LeanCanny/Algebra/FixedWidthMonomial.lean)
supplies FP residues for the constant, point, and shift terms.
[`TubeSparseConstraintCoefficient`](LeanCanny/ETR/TubeSparseConstraintCoefficient.lean)
combines all four unscaled constraint cases.
[`TubeConstraintCoefficient`](LeanCanny/ETR/TubeConstraintCoefficient.lean) applies
the raw stored margin numerator and denominator with native modular arithmetic.
[`TubeConstraintCoefficientSource`](LeanCanny/ETR/TubeConstraintCoefficientSource.lean)
accepts FP binary row selectors and preserves every valid row exactly; larger
indices select the final constraint. Its complete coefficient evaluator handles
arbitrary exponent words and positive moduli with no source-coefficient oracle.
[`TubeConstraintIndexed`](LeanCanny/ETR/TubeConstraintIndexed.lean) enumerates
these coefficients by binary rank, and
[`TubeConstraintSubstitution`](LeanCanny/ETR/TubeConstraintSubstitution.lean)
computes rational substitution with the sign query's fixed allowance `2*D`.
Every rank exponent is below `2^D.size`, which is at most `2*D`.

[`TubeLevelSignNative`](LeanCanny/ETR/TubeLevelSignNative.lean) derives the complete
sign-query coefficient reader from native root and coordinate coefficient
readers. An FP mask lookup selects constant one for active rows; inactive rows
run the constraint-substitution evaluator. With `CoordinateBudget`, the resulting
counter and sample-existence PSPACE theorem need no expanded sign-query reader
or separate query budgets. Constructing suitably bounded coordinate
representations and their root/coordinate coefficient readers from the original
input remains open.

[`TubeCompiledReprojection`](LeanCanny/ETR/TubeCompiledReprojection.lean) makes
the underlying spatial tuple independent of the added linear projection.
Coordinate directions therefore place each spatial coordinate among the roots
of a nonzero lowest-coefficient eliminant. Their product bounds the full
solution count by `B=(2^W)^(A*(A-1))`, including singular roots. Here W is the
Macaulay matrix width and A the compiled coordinate count.
[`TubeCoordinateThreshold`](LeanCanny/ETR/TubeCoordinateThreshold.lean) computes
one FP binary dyadic exponent for all coordinate directions. Below that
positive threshold, rational representations and their integer clearings have
parameter degree at most B and coordinate degrees at most `B^2+2`.
[`TubeLevelDegreeBounds`](LeanCanny/ETR/TubeLevelDegreeBounds.lean) writes those
bounds in FP and constructs the native sign-stage budget from `MassBudget`.
The resulting PSPACE endpoint still requires native root/coordinate coefficient
readers, coefficient-mass bounds, and suitable positive small levels. Effective
parameter selection and coordinate construction with source-size height and
workspace bounds remain open.

[`MvCoefficientMass`](LeanCanny/Algebra/MvCoefficientMass.lean) bounds the sum of
absolute coefficients under integer multivariate arithmetic, renaming, and
partial differentiation.
[`PolynomialMass`](LeanCanny/ETR/PolynomialMass.lean) bounds the finite source
polynomial's mass by `2^N`, for encoded term size N.
[`CubePolynomialMass`](LeanCanny/Geometry/CubePolynomialMass.lean) controls
denominator clearing, giving compactified mass at most `2^(N+2*N²)`.
[`TubeCoefficientMass`](LeanCanny/Geometry/TubeCoefficientMass.lean) propagates
these estimates through all active tubes and flattened projection equations.
[`TubeCoefficientBounds`](LeanCanny/ETR/TubeCoefficientBounds.lean) supplies an
FP writer for their common coefficient magnitude-bit budget `20*N²+6*N+22`.
Here N is the normalized compiled term size, itself polynomially bounded in
the input length. Coefficient-access machines and quantitative bounds for the
exceptional polynomials and chosen parameters remain open.

[`MvCoefficientChainRule`](LeanCanny/Algebra/MvCoefficientChainRule.lean)
extends the polynomial chain rule to varying coefficients.
[`ProjectionParameterAlgebraic`](LeanCanny/Algebra/ProjectionParameterAlgebraic.lean)
and [`ProjectionParameterCoordinates`](LeanCanny/Algebra/ProjectionParameterCoordinates.lean)
prove critical-coordinate algebraicity when direction derivations fix the
constraint polynomials. This allows symbolic level parameters to remain fixed,
including in the extended system with its reciprocal variable.
[`LevelProjectionSpecialization`](LeanCanny/Algebra/LevelProjectionSpecialization.lean)
uses this to construct a nonzero joint exceptional polynomial in the level and
direction coordinates. Every specialization avoiding it has a finite extended
projection fiber. No degree or coefficient bound is supplied.

[`CollectedCoefficients`](LeanCanny/ETR/CollectedCoefficients.lean) identifies an
actual source coefficient with the sum of all indexed monomials having its
exponent vector, including repetitions and cancellations.
[`CollectedCoefficientQuery`](LeanCanny/ETR/CollectedCoefficientQuery.lean)
checks this match in FP using fixed-width exponent blocks.
[`CollectedCoefficientSpace`](LeanCanny/ETR/CollectedCoefficientSpace.lean)
streams the matching coefficient residues in polynomial space.
[`CollectedCoefficientSign`](LeanCanny/ETR/CollectedCoefficientSign.lean) and
[`CollectedCoefficientZero`](LeanCanny/ETR/CollectedCoefficientZero.lean)
prove negativity and zero testing in PSPACE using the source's `N+1` bit budget.
[`SourceCoefficientSpace`](LeanCanny/ETR/SourceCoefficientSpace.lean) instantiates
residue access for the compiled ETR source on every binary input. Its polynomial
has N coordinates, with unused coordinates padded by zeros. Every nonzero
coefficient has an exponent query of length `N*(N+1)`.
This evaluator accesses the source before compactification.

[`FixedWidthNatVectorFP`](LeanCanny/Encoding/FixedWidthNatVectorFP.lean) writes
polynomial-length vectors from FP coordinate readers.
[`MonomialExponentVector`](LeanCanny/ETR/MonomialExponentVector.lean) uses it to
write exact collected-coefficient queries for selected indexed monomials.
[`CollectedDegree`](LeanCanny/ETR/CollectedDegree.lean) proves that the maximum
indexed exponent whose collected coefficient survives is the actual variable
degree, including complete cancellation.
[`BoundedMaximum`](LeanCanny/Computation/BoundedMaximum.lean) certifies a streamed
maximum over exponentially many space-bounded calls.
[`CollectedDegreeSpace`](LeanCanny/ETR/CollectedDegreeSpace.lean) combines these
with coefficient zero testing to compute actual degrees in polynomial space.
[`FinitePolynomialPadding`](LeanCanny/ETR/FinitePolynomialPadding.lean) proves
that padding preserves the degrees of original variables.
[`SourceDegreeSpace`](LeanCanny/ETR/SourceDegreeSpace.lean) therefore computes
the exact source degrees used in compactification for compiled ETR inputs.
[`CubeCoefficientFormula`](LeanCanny/Geometry/CubeCoefficientFormula.lean)
expresses compactified coefficients as sums of source coefficients times
products of univariate binomial coefficients. It uses actual source degrees,
including after cancellation.
[`CubeFactorResidue`](LeanCanny/Algebra/CubeFactorResidue.lean) computes each
factor in polynomial space.
[`ModularProductSpace`](LeanCanny/Algebra/ModularProductSpace.lean) streams
space-bounded factors, and
[`CompactCoefficientSpace`](LeanCanny/ETR/CompactCoefficientSpace.lean) combines
the coordinate product and source-term sum into compactified coefficient
residue access. Its polynomial has the validated source length as its padded
dimension.
[`CompactCoefficientPadding`](LeanCanny/ETR/CompactCoefficientPadding.lean)
proves that zero-padding preserves original compactified coefficients.
[`CompactSourceCoefficient`](LeanCanny/ETR/CompactSourceCoefficient.lean)
instantiates the evaluator for compiled ETR inputs and proves exact access to
`CompactSource.polynomial`. Every nonzero coefficient has a query of length
`N*(4*N²+1)`.
[`CompactCoefficientSign`](LeanCanny/ETR/CompactCoefficientSign.lean) supplies
the `N+2*N²+1` magnitude-bit budget and proves coefficient negativity in PSPACE.
[`CompactCoefficientZero`](LeanCanny/ETR/CompactCoefficientZero.lean) proves
coefficient zero testing in PSPACE using the complete residue evaluator.
[`CubePolynomialMultiplication`](LeanCanny/Geometry/CubePolynomialMultiplication.lean)
proves that integer compactification commutes with multiplication and powers,
including zero polynomials.
[`TermPowerFP`](LeanCanny/ETR/TermPowerFP.lean) writes bounded source powers in FP,
and [`CompactPowerCoefficient`](LeanCanny/ETR/CompactPowerCoefficient.lean)
uses this to access coefficients of powers of the original compact polynomial.
[`TubeCoefficientDecomposition`](LeanCanny/Geometry/TubeCoefficientDecomposition.lean)
expresses the integer tube as its source square with multiplicity at most two,
the source times a linear shift supported at two coordinates, and the
zero-source tube.
[`TubeCoefficientFormula`](LeanCanny/Geometry/TubeCoefficientFormula.lean)
extracts each tube coefficient from these three dense queries and one zero-source
tube coefficient. It also connects the projection coefficient formulas to the
actual integer projection system: each partial row uses two shifted tube queries.
[`TermArityFP`](LeanCanny/ETR/TermArityFP.lean) computes exact source syntax arity
in FP. [`TubeEncoding`](LeanCanny/ETR/TubeEncoding.lean) supplies the coordinate
layout and active-set bitmask round trip.
[`TubeZeroSyntax`](LeanCanny/ETR/TubeZeroSyntax.lean) represents the zero-source
tube by a short expression and proves equality with the existing integer
polynomial. [`TubeZeroFP`](LeanCanny/ETR/TubeZeroFP.lean) certifies its writer in FP.
[`TubeZeroSpace`](LeanCanny/ETR/TubeZeroSpace.lean) supplies coefficient residues,
negativity and zero testing in PSPACE, with native-coordinate query correctness
and coverage of every nonzero coefficient.
[`FixedWidthQuery`](LeanCanny/Encoding/FixedWidthQuery.lean) supplies FP block
access, zero-padding/repacking, and coordinate guards.
[`TubeZeroQuery`](LeanCanny/ETR/TubeZeroQuery.lean) uses the degree-four bound to
reject oversized exponents before repacking, giving exact sparse tube residues
on every binary target word.
[`TubeDenseQuery`](LeanCanny/ETR/TubeDenseQuery.lean) supplies the remaining dense
summands: an embedded positive source power, optionally times either source
shift variable. FP pattern and degree guards force zero on rejected queries;
valid queries call the full source-power evaluator. All target words and modulus
one are covered.
[`TubeCoefficientSpace`](LeanCanny/ETR/TubeCoefficientSpace.lean) combines all
four children into a polynomial-space residue evaluator for the full integer
tube, using sequential output pairing and FP modular addition.
[`TubeSourceCoefficient`](LeanCanny/ETR/TubeSourceCoefficient.lean) instantiates
this evaluator on compiled ETR inputs and proves native-coordinate query
correctness, including modulus one. Every nonzero tube coefficient has a query
of polynomial length.
[`TubeProjectionEncoding`](LeanCanny/ETR/TubeProjectionEncoding.lean) orders
projection variables as point, direction, and parameter blocks.
[`TubeProjectionGuard`](LeanCanny/ETR/TubeProjectionGuard.lean) certifies the
zero and unit direction patterns in FP, with their native polynomial equivalence.
[`TubeProjectionRepack`](LeanCanny/ETR/TubeProjectionRepack.lean) certifies FP
restriction and optional derivative increments using an extra exponent bit.
[`TubeProjectionRestriction`](LeanCanny/ETR/TubeProjectionRestriction.lean) proves
that these queries access exactly the required native tube coefficients and
supplies their complete space evaluators.
[`TubeProjectionFactor`](LeanCanny/ETR/TubeProjectionFactor.lean) supplies FP
binary derivative factors and modular multiplication.
[`TubeProjectionTermSpace`](LeanCanny/ETR/TubeProjectionTermSpace.lean) combines
the guards, tube children, and factors into certified projection terms.
[`TubeProjectionRows`](LeanCanny/ETR/TubeProjectionRows.lean) assembles the actual
level and partial rows, and
[`TubeProjectionSpace`](LeanCanny/ETR/TubeProjectionSpace.lean) selects them using
a total FP row decoder. Invalid row codes select the level row; every native
row has a proved encoding round trip.
[`TubeSourceProjectionCoefficient`](LeanCanny/ETR/TubeSourceProjectionCoefficient.lean)
instantiates the full residue evaluator on compiled ETR inputs. Native-coordinate
correctness and polynomial-length exponent queries cover every nonzero coefficient
of every actual integer projection row, including modulus one.
[`TubeCoefficientDecisions`](LeanCanny/ETR/TubeCoefficientDecisions.lean) connects
both full residue evaluators to the actual `20*N²+6*N+22` coefficient-bit budget.
It supplies complete three-way sign evaluators and proves coefficient negativity,
positivity, and zero testing in PSPACE on every binary input. Zero testing uses
[`IntegerZeroSpace`](LeanCanny/Algebra/IntegerZeroSpace.lean), which scans small
moduli with a binary size bound.
[`FixedWidthPolynomial`](LeanCanny/Algebra/FixedWidthPolynomial.lean) proves that
binary ranks enumerate bounded exponent vectors uniquely and reconstruct a
polynomial from its actual coefficients.
[`TubeIndexedSource`](LeanCanny/ETR/TubeIndexedSource.lean) instantiates this
representation for the native tube and projection layouts, with FP exponent
readers and binary term-count writers. Blocks use the binary length of the full
degree allowance.
[`TubeIndexedSpace`](LeanCanny/ETR/TubeIndexedSpace.lean) supplies complete residue
readers for these indexed coefficients, parameterized by FP source, active-set,
row, and modulus fields.
[`TubeIndexedBounds`](LeanCanny/ETR/TubeIndexedBounds.lean) supplies uniform
coefficient bounds and an FP even denominator-clearing allowance at most twice
the full degree bound.
[`TubeRationalSource`](LeanCanny/ETR/TubeRationalSource.lean) packages those actual
sources for rational substitution, including canonical modular coefficient
packets. [`TubeRationalSubstitution`](LeanCanny/ETR/TubeRationalSubstitution.lean)
composes the complete residue evaluator with certified rational-coordinate
readers. [`TubeRationalCorrect`](LeanCanny/ETR/TubeRationalCorrect.lean) proves
that the result is exactly denominator clearing of the native integer tube or
projection row, and that its trailing-coefficient sign equals the original
rational evaluation's sign on a sufficiently small positive interval wherever
coordinate denominators are nonzero.
[`TubeRationalBounds`](LeanCanny/ETR/TubeRationalBounds.lean) derives FP output
degree and coefficient-bit bounds from coordinate bounds and actual source
bounds. [`TubeRationalDecisions`](LeanCanny/ETR/TubeRationalDecisions.lean) supplies
coefficient sign/zero tests and a three-way infinitesimal sign evaluator.
[`TubeRationalLanguages`](LeanCanny/ETR/TubeRationalLanguages.lean) proves
polynomial identity and either strict trailing-coefficient sign in PSPACE under
the same coordinate-reader contracts. Concrete sampler coordinate readers,
quantitative parameter selection, and the full ETR algorithm remain open.

## Next obligations

1. Relate the chosen encoding to standard ETR presentations and prove an NP lower inclusion.
2. Instantiate the modular power PSPACE theorem with concrete validated input
   formats and uniform entry evaluators;
   use the native space-entry interface when the whole entry computation
   requires more than polynomial time.
3. Supply concrete parameter readers and bounds for the certified full Macaulay
   coefficient and sign evaluators, including the full three-parameter
   deformation and its computed lowest nonzero coefficient. Extend lowest-coefficient
   vanishing from finite affine fibers to the remaining proper components;
   bound and select suitable rational parameter packets in the source size, and
   extend the concrete variable-level readers to the full nested perturbation.
   The retained geometric samples now lift to actual compiled affine roots and
   are covered by nonzero lowest-coefficient eliminants.
   The qualitative geometric-to-compiled finiteness
   bridge is proved, uniformly on a small level interval over real extension fields.
   Identify the polynomial Macaulay quotient with the
   required resultant/eliminant. Polynomial cancellation of the extraneous
   determinant is proved, including for the actual tube characteristic pencils.
   The sharp Macaulay degree bound and the two-way common-root criterion over
   algebraically closed fields are proved, including for the actual tube
   polynomial and at singular extraneous matrices.
   The full and extraneous determinants now both have certified lowest-index and
   integer-sign evaluators under the existing reader contracts. Qualitative
   integer rational-coordinate decoding of actual compiled systems at rational
   levels is now proved. Construct these coordinates effectively from the
   streamed eliminants and bound their coefficients. Prove the full coordinate
   computation's space bound, including algebraic parameter values,
   and formalize the remaining parallel/streamed algebra used by the report.
   The final decoded-sample sign stage has native count and decision certificates
   under the explicit coefficient-reader and budget contracts. Query degree
   and mass budgets are derived from coordinate bounds using fixed clearing
   powers and raw packet margin integers.
4. Prove quantitative sampling bounds and effective parameter selection, implement
   critical-point sampling, and combine the algebraic sign tests into Canny's ETR
   decision procedure; prove `ETR ∈ PSPACE`.
5. Apply the proved PSPACE reduction closure once ETR membership is established;
   the conditional equivalence `∃ℝ ⊆ PSPACE ↔ ETR ∈ PSPACE` is already proved.
6. Extend to roadmap connectivity and the geometric consequences in the report.

See [`RESEARCH.md`](RESEARCH.md) for prior work, the machine-model comparison, and
where Savitch's theorem enters.

## Report integrity

Source: [Berkeley PDF](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/Archive/CSD-88-439.pdf).
The downloaded file has 936,246 bytes and SHA-256
`7606d41dea23ac1160562a759c196267906d8aec0f754cd4998fdd14fcd185f8`.
The report retains its original rights; the source-code license does not apply to it.
