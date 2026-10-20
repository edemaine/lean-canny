# Prior work and choice of complexity infrastructure

Investigation date: 2026-10-19. Negative findings below describe the repositories and
searches checked; they are not claims that no such formalization exists anywhere.

## Existing real-algebraic formalizations

* [TauCeti](https://github.com/TauCetiProject/TauCeti) includes real-algebraic
  quantifier elimination, CAD existence, Tarski–Seidenberg, and Sturm–Tarski/sign
  determination. See
  [quantifier elimination](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/RealAlgebraic/Semialgebraic/QuantifierElimination.lean)
  and [recursive sign determination](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/RealAlgebraic/SignDetermination/Recursive.lean).
  The inspected sign-determination construction uses noncomputable choices. Its
  correctness results do not supply Canny's workspace bound.
* [Hex](https://github.com/leanprover/hex) develops exact real-algebraic computation,
  including root isolation, algebraic numbers, resultants, and real-closed-field
  tactics. Such arithmetic can be useful without establishing a PSPACE bound for ETR.
* Isabelle AFP has [Ben-Or–Kozen–Reif](https://www.isa-afp.org/entries/BenOr_Kozen_Reif.html)
  and [hybrid real quantifier elimination](https://www.isa-afp.org/entries/Quantifier_Elimination_Hybrid.html).
  These are relevant algorithmic correctness precedents in a different prover.
* Coq has Cohen and Mahboubi's real-closed-field quantifier elimination and
  [MathComp CAD](https://github.com/math-comp/cad). These are additional prior work,
  rather than Lean complexity-class interfaces.

The project now adapts a selected Sturm–Tarski proof slice from TauCeti revision
`034e577c895d28c058d92af4036f7ce0b03081cf`. Its
[seed and common-factor proof](https://github.com/TauCetiProject/TauCeti/blob/034e577c895d28c058d92af4036f7ce0b03081cf/TauCeti/Algebra/Polynomial/Sturm/Tarski.lean)
handles repeated roots and queries that vanish at roots. Its
[infinite-endpoint formula](https://github.com/TauCetiProject/TauCeti/blob/034e577c895d28c058d92af4036f7ce0b03081cf/TauCeti/Algebra/Polynomial/Sturm/Infinity.lean)
uses leading coefficients and degree parity. The local adaptation specializes
analytic results to ℝ and uses Mathlib's intermediate value theorem, with no
new dependency; see [source attribution and changes](STURM_SOURCES.md).
`RootSignQueries.tarskiQuery_eq_coefficientQuery` connects this formula to the
existing sign-count identity. `tarskiQuery_rat` proves that rational input
polynomials need only rational signed remainders. The mathematical formula is
proved; an encoded implementation with Canny's workspace bound remains open.

The local proof now also includes TauCeti's signed-principal-subresultant
Euclidean identities and its permanences-minus-variations formula, adapted to
a coefficient-variation index over ordered fields. `tarskiQuery_eq_principalQuery`
reduces each real-root query to signs of explicit determinants after reducing
the derivative product modulo the head. Rational and integer input versions are
proved. `PrincipalSubresultant.matrix_eq_minor` verifies the same matrix convention
as the existing streamed subresultants, and `signedPsc_size_le` transfers their
integer bit budget, including the terminal principal index. The integer pseudo-seed
construction below supplies a streamed alternative to rational remainder access.
Actual-degree routines and the sign-statistic scan now have resource proofs.
Principal-determinant signs are now supplied by the project pipeline below.
The computed degrees and all source routines are composed in the original-source
Tarski evaluator below.

`PseudoRemainder` now replaces rational polynomial division by a fixed linear
operator. Splitting `g` into its coefficients below degree `d` and shifted high
part gives `T(g) = a*low(g) - low(p)*high(g)`, for `a = p[d]`.
When `degree(p) ≤ d`, this equals `a*g - p*high(g)`. With input degree bound `D`,
`2*(D+1)` iterations lower the result below `d` and give a positive scaling when
`p` has actual degree `d > 0`. The integer Tarski-query theorem therefore uses
an integral seed and integral principal determinants.

The operator is represented by a `(D+1)`-dimensional scalar matrix. Each entry
is zero, an original head coefficient, or its negation. The certified entry
controller derives all source queries and modular negations internally.
`PseudoRemainderBits.DataAccess.evaluator` combines suspended original-head and
input coefficient routines with the existing scalar-moment evaluator, proving
complete modular coefficient access without storing any intermediate remainder.
Fixed bounds commute with coefficient maps even if the modular head degree drops.
If head and input coefficient masses are bounded by `2^bp` and `2^bg`, a coefficient
after `n` steps has at most `n*(bp+1)+bg+1` magnitude bits. FP binary writers supply
this budget from original degree/coefficient bounds. The derivative-product
source instantiation, integer coefficient signs, and actual-degree routines are
now composed with the constant-head branch and principal-determinant pipeline
below. The full `ETR ∈ PSPACE` theorem is not yet established.

`DerivativeBits.evaluator` reads an original coefficient at binary index `k+1`
and multiplies it modulo the supplied modulus. `DerivativeProductBits.Access.evaluator`
then computes a selected coefficient of the actual product `f*p'` from the two
original coefficient routines. `TarskiSeedBits.Access.evaluator` supplies this
product internally to the division-free reduction; its degree bound is the sum
of the original degree bounds. Differentiation increases integer coefficient
mass by at most the degree, so FP seed bit-budget writers depend only on the
original polynomial bounds.

`IntegerTarskiSeedBits.Access.residueEvaluator` supplies uniform residues of an
actual integer seed coefficient for every positive modulus. It normalizes the
modulus and selected index for the original source protocol and returns zero
outside the reduction bound. `signEvaluator` composes the certified CRT sign
routine with these residues and the derived binary magnitude budget. The only
external arithmetic routines read coefficients of the original head and query.

`PolynomialDegreeBits.offsetEvaluator` scans coefficient-zero answers while
retaining just the binary index of the last nonzero coefficient, plus one.
Zero represents the zero polynomial, and one a nonzero constant. Its prefix
state/clock bounds include all suspended zero-test work. `degreeEvaluator`
returns Mathlib's natural degree, including zero for the zero polynomial.
The original head and computed seed have concrete degree evaluators using
these scans and the certified integer coefficient signs. These outputs may
use polynomial space; they are not asserted to be FP functions of the original
input. Their retained metadata now feeds the principal-determinant sign scan
through the total contexts below.

`SignStatisticBits.evaluator` now supplies the full permanences-minus-variations
scan from a suspended sign reader and an FP binary count. Its state keeps the
previous nonzero sign, the length of the pending zero gap, and positive and
negative contribution counts. After `k` entries, the encoded state has at most
`5*k.size + 10` bits. The certificate includes all sign-reader state and clock
costs, and returns the integer answer as canonical positive and negative parts.
`descendingEvaluator` derives descending coefficient indices in FP.
`tarskiEvaluator` connects this implementation to the integer pseudo-seed
Tarski formula, assuming certified signed-principal-coefficient signs and an
actual positive head-degree writer. The original-source evaluator below
instantiates both of these intermediate assumptions.

`PrincipalMinor.minor_eq_submatrix` extends the Sylvester embedding to terminal
orders using non-strict bounds. `PrincipalMinorBits.Access.residueEvaluator`
computes their full modular determinant residues from suspended original
coefficient readers. The scalar Berkowitz evaluator now includes the parity
correction needed to return the determinant rather than its characteristic
coefficient. Empty minors and modulus one are included.

`PrincipalCoefficientBits.signEvaluator` supplies the complete signed-principal
coefficient reader: inside the principal range it normalizes the determinant;
outside it selects the retained input leading coefficient or zero. The CRT
bit budget is derived from the common input coefficient bound and the two
binary degree parameters. The reader covers every requested order and input
word. `queryEvaluator` composes it with the descending sign-statistic scan;
no principal-sign oracle is assumed. With the head and its integer pseudo-seed
as inputs and actual degree metadata, `tarskiEvaluator` returns the real-root
Tarski query. The total contexts below supply this metadata from the original
head/query readers, including the constant-head branch.

`TarskiQueryBits.evaluator` now evaluates the full signed integer Tarski query
from the original two uniform coefficient-residue readers. The FP metadata
contains only upper degree and coefficient-mass bounds. It computes the actual
head degree first and retains it in the context. A positive degree cap truncates
the head on arbitrary metadata words, so every intermediate source contract
holds; at the computed degree, this truncation is the original polynomial.
The actual integer seed degree is then computed and retained before the
principal-sign scan. All nested coefficient, CRT, matrix, and scan costs are
included by the space-function composition certificates.

A separate constant-head branch returns zero, including Mathlib's finite-root
convention for the zero polynomial. The output encodes the query's canonical
positive and negative parts. `TarskiQueryBits.zeroLanguage_mem_PSPACE`,
`positiveLanguage_mem_PSPACE`, and `negativeLanguage_mem_PSPACE` give decision
consequences under the same original-source contracts. The remaining root-sign
work now has a complete enumeration, pattern-weight, and exact-count composition
for polynomially bounded family size, as described below. Canny's stronger query
selection, the effective critical-point algorithm, and `ETR ∈ PSPACE` remain open.

No existing encoded ∃ℝ complexity-class definition or formal proof of `ETR ∈ PSPACE`
was found in the inspected Mathlib, Complexitylib, CSLib, TauCeti, or adjacent projects.
The ∃ℝ definition in this project uses the standard reduction-class formulation;
equivalence with other finite presentations requires explicit efficient translations.

Mathlib already proves the ordinary
[primitive element theorem](https://github.com/leanprover-community/mathlib4/blob/728a93eeff833da3173895bb0575752fdc24edb0/Mathlib/FieldTheory/PrimitiveElement.lean),
including a linear-GCD argument for two separable elements. Its Galois fixed-field and
Lagrange interpolation theorems also supply the algebraic tools used here. The current
project strengthens the representation interface to all pairs of roots of two input
polynomials, with one bounded integer selector, a monic separable degree-`d₁*d₂`
polynomial, and coordinate polynomials over the input field. The GCD coefficient-ratio
recovery specification is proved. The parameter polynomial now uses Mathlib's
[Sylvester resultant](https://github.com/leanprover-community/mathlib4/blob/728a93eeff833da3173895bb0575752fdc24edb0/Mathlib/RingTheory/Polynomial/Resultant/Basic.lean),
with verified specialization, roots, scalar normalization, and degree. Taylor and Hasse
derivatives supply a direct shifted-coefficient formula and integer bit-length bounds.
The project now bounds coefficients of polynomial determinants by column coefficient
masses, and specializes this estimate to the integer resultant. Its degree is at most
`d₁*d₂` without nonzero or separability hypotheses, and its coefficient bit lengths
are bounded explicitly in the input degrees, coefficient lengths, and direction length.
Interior subresultants now have explicit determinant definitions, coefficient bit bounds,
and certified modular evaluation. The nonzero linear-GCD bridge now proves symbolic
coordinate recovery for input degrees greater than one and nonzero directions.
Direct linear branches extend recovery to every degree and direction under the
separating-pair hypotheses. Integer magnitude-bit recovery is certified from
residue access and an FP budget; the report's remaining space bounds are open.
Integer negativity is certified
from residue access and a binary bit budget, with a full three-way sign evaluator
for Canny's concrete resultant coefficient.
The modules below give certified modular determinant/resultant coefficient
evaluation and integer zero testing, including Canny's concrete resultant family.

The project also proves the division-free bordered characteristic-polynomial
recurrence behind Berkowitz's algorithm. Coefficients of `adj(XI-A)` are expressed
through powers of `A`; cancellation of the monic characteristic polynomial proves
the bordered identity even over rings with zero divisors. A recursive reference
on `Fin n` matrices returns exactly Mathlib's characteristic coefficients and
determinant, including dimension zero. Its linear recursion depth does not supply
the report's polylogarithmic workspace. The coefficient recurrence now acts by
square transformations on padded vectors; their ordered product contains the
characteristic coefficients in its first column. A generic balanced interval
recursion preserves factor order, and `Berkowitz.balancedDeterminant` uses height
`n.size` to recover the determinant. The factor accessor avoids building the full
list. The layered matrix
construction now converts this ordered product to a single power, with dimension
`(n+1)^2` and exponent `n`. It therefore reuses the existing continuation machine
and bitstring controller under their explicit entry-access contract. Stored residue
states have at most `64*(3*n.size+m.size+2)^2` bits; retaining context `c` adds
`2*c.length+2`. The abstract clock is at most `2^((2*n.size+3)*n.size+1)`, counting
entry access as one operation. A generic suspension wrapper and PSPACE composition
theorem now account for a saved parent alongside a running child. The power
controller intercepts exponent-one entry queries, runs the child through FP steps,
and resumes the original stack with its output. Correct and terminating calls
simulate the full abstract power run. Direct factor access is now proved through
the trailing principal block, with no lookup of preceding factors. The factor
cases are one, a negative diagonal entry, a negative scalar moment, or zero.
Adding a source and sink reduces `r A^k c` to a power entry in dimension `n+2`.
Given FP binary fields, row, column, and original-entry access, a uniform controller
computes this moment. Its first halting time, result, and packet bounds are proved;
FP modular negation supplies the negative output, including modulus one.
Uniform FP binary quotient/remainder now decodes the flattened query indices.
Its quotient fold keeps every partial word bounded by the processed dividend's
length, including noncanonical inputs and division by zero. FP field writers
supply the trailing dimension, offset, moment exponent, and four-case selector.
Offset query writers give exactly the original matrix entries for the trailing
block and border vectors, with a certified moment-child callback contract.
The complete factor child now combines the immediate and moment cases, with
correct results, exact first halting time, and concrete workspace/clock bounds.
`Berkowitz.ModularAccess.zeroLanguage_mem_PSPACE` instantiates the suspended
controller and proves modular determinant zero testing in Complexitylib's PSPACE.
It assumes FP canonical dimension/modulus fields and FP original-matrix entries
on every input, with a nonzero modulus. Dimension can be exponential in the input
length. The proof includes the retained parent and child packets and the expanded
physical clock; it assumes no FP computation of whole factor entries.
Integer determinant zero testing now also belongs to PSPACE under FP dimension
and binary determinant-bit-budget access and uniform FP original-entry residue
access. Mathlib's LCM growth bound implies that an integer of at most `B`
magnitude bits is zero exactly when its residues modulo `1,...,2*B+4` vanish.
The project proves this criterion and the determinant specialization. A generic
bounded universal scan retains a binary counter and one answer bit while each
space-certified child runs. Modular determinant evaluation now exposes a reusable
`SpaceDecider` with its FP primitives and full resource/correctness certificates.
The scan composes that decider, accounting for the scan parent, modular controller,
and factor child. Dimension, entry bit lengths, and the determinant bit budget can
be exponential in the input length; complete integer entries are not stored.
The access contract covers all contexts and positive binary moduli. Concrete
formats still must validate/default inputs and supply the uniform residue routine
and bit budget. The generic sign and magnitude-bit evaluators consume these
contracts; the report's ETR upper bound remains open.

The integer determinant theorem now also has a resultant instantiation. Binary
guards and offset writers implement exactly Mathlib's two Sylvester column
blocks through coefficient queries. They preserve the specified degree parameters,
including after a specialization lowers an actual degree. A common coefficient
bound `2^b` gives the computed resultant bit budget `N.size*N+N*b+1`, with `N=m+n`.
`Resultant.Access.zeroLanguage_mem_PSPACE` proves resultant zero testing under
FP degree and coefficient-budget fields and uniform FP coefficient-residue access
on all contexts and indices. A corollary uses the ordinary resultant when the
degree fields equal the actual polynomial degrees. Later modules provide symbolic
modular coefficient evaluation and generic integer sign recovery. Residue algorithms
for all polynomial constructions used in the report remain open.

The project now supplies an explicit binomial-residue routine for the shifted
coefficient formula. The lower bidiagonal matrix with diagonal and subdiagonal
one has `choose n k` at row `k`, column zero of its nth power in dimension `k+1`.
This identity holds over any semiring. Concrete FP binary writers and entry
access instantiate the modular power controller, including arbitrary positive
composite moduli and modulus one. `BinomialResidue.evaluator` returns the complete
residue through a `SpaceFunction` certificate with first halting time, polynomial
state bounds, and an exponential clock. All binary input words are covered;
`k>n` returns zero. Modular power evaluation now exposes the same output interface,
and FP final predicates derive PSPACE decision procedures from it.
The shifted-coefficient residue evaluator now combines the binomial child with
the original coefficient and the power of the negative direction. Binary modular
exponentiation has an FP certificate by repeated squaring, with every fold result
bounded by the modulus word. FP input preparation and an explicit input-retention
wrapper preserve the complete resource certificates. `ShiftCoefficientBits.certified`
returns exactly the coefficient of `x^i θ^j` in `p(θ-c*x)` modulo the supplied
positive modulus, assuming FP original-coefficient residue access and a canonical
FP direction writer. Its modular zero-test language is in PSPACE. All binary
queries, zero coefficients/direction, and modulus one are covered.
Modular powering now also accepts a `SpaceFunction` entry routine under FP field
writers. `MatrixPower.ModularAccess.evaluatorWithEntry` supplies the saved-parent,
query-length, child-workspace, and expanded-clock proofs for the complete output;
zero testing is in PSPACE under the same contracts. An FP-controlled branch
certificate lets Sylvester access select either coefficient routine or zero.
`Resultant.Access.integer_entryEvaluator` exposes a certified routine for the
exact integer-entry function used by the existing resultant encoding. This now
feeds the complete determinant pipeline: augmented scalar moments accept
space-bounded vector/matrix routines, offset queries specialize them to trailing
blocks, and the factor evaluator selects an immediate value or the moment child.
`Berkowitz.ModularAccess.deciderWithEntry` consumes the resulting factor routine
in the outer power; `Berkowitz.IntegerAccess.deciderWithEntry` adds the modulus
scan. `Resultant.Access.zeroLanguage_mem_PSPACE_of_evaluators` consequently
proves integer resultant zero testing under FP degree/budget fields and
`SpaceFunction` coefficient-residue certificates. The ordinary-resultant
corollary requires the supplied degrees to equal the actual degrees. Symbolic
coefficient evaluation for Canny's resultant is supplied by the specialization below,
as are its integer signs and magnitude bits.

The symbolic coefficient reduction now has a scalar matrix representation.
`PolynomialCoefficientMatrix.scalarHom` maps a polynomial to its lower
triangular coefficient matrix of width `d+1`, preserving addition and
multiplication. Entrywise application and block flattening preserve powers.
`Berkowitz.det_coeff_eq_coefficientPower` consequently expresses degree `d`
of a determinant over `R[X]` as a signed power entry over `R`, in dimension
`(n+1)^2*(d+1)`. `PolynomialPower.ModularAccess.evaluator` now implements the
generic polynomial matrix-power coefficient operation. FP binary controls
and a `SpaceFunction` routine for original entry coefficients suffice. The
flattened accessor decodes each coordinate by division/remainder and returns
one input coefficient or zero, with its own space certificate. This covers
all binary contexts and gives modular coefficient zero testing in PSPACE.
`PolynomialMoment.ModularAccess.evaluator` specializes it to coefficients of
`r A^k c`: taking an entry coefficient commutes with source/sink augmentation,
so FP guards and degree-carrying query writers select a vector or matrix
coefficient routine. These routines may each use polynomial space.
The determinant instantiation now supplies the layered factor coefficients.
`BerkowitzPolynomial.ModularAccess.momentEvaluator` carries coefficient degrees
through offset queries to the original trailing block and its border vectors.
The four factor cases have a certified evaluator and agree with coefficients
of the layered matrix on all valid indices. Polynomial powering and an FP
parity test then give `BerkowitzPolynomial.ModularAccess.evaluator`, returning
the selected determinant coefficient with the Berkowitz sign. Its contract
requires FP dimension/modulus/degree fields and a `SpaceFunction` routine for
original entry coefficients; modular coefficient zero testing is in PSPACE.
`ResultantPolynomial.ModularAccess.evaluator` now instantiates this determinant
routine for symbolic resultants. Its Sylvester accessor carries the requested
degree into each input coefficient routine, reusing the existing scalar guards
and indexing proof. FP input-degree/modulus/output-degree fields and certified
space-bounded bivariate coefficient routines suffice; modular resultant
coefficient zero testing is in PSPACE.

`CannyResultantBits.Access.evaluator` now supplies the concrete Canny
instantiation. The shifted-coefficient child accesses `p₁(θ-c*x)` and an FP
degree-zero guard accesses `p₂(x)`. The result is proved equal to a coefficient
of the existing integer `cannyResultant`, reduced modulo any positive modulus.
The fixed integer source degrees are preserved through modular reduction.
The contract requires FP source degrees, direction, and selected output degree,
plus uniform FP residue access to both original integer coefficient functions.
Its modular coefficient zero test is in PSPACE.

`CannyResultantBits.IntegerAccess.decider` extends this to zero testing of the
integer coefficient. For source degrees `m,n`, direction `c`, and coefficient
bounds `2^b₁,2^b₂`, its computed budget is
`B = (m+n).size*(m+n) + n*S + m*(b₂+1) + 1`, where
`S = (m+1).size + m + (b₁+1) + (c+1).size*m`.
The previous coefficient-size theorem proves this budget; binary arithmetic
and encoded word lengths give FP budget writers. The bounded modulus scan
then composes the concrete residue decider and tests moduli `1,...,2*B+4`, with
all child states included. FP source-bit-budget fields and the residue-access
contracts suffice, even when `B` is exponential. The sign evaluator below uses
the same budget and residue-access contracts; the magnitude-bit evaluator below
also consumes these contracts.

The reconstruction specification now has a proved CRT route. A coprime modulus
system uses locally reduced inverse-weighted numerators `aᵢ`; the fractional part
of `Σ aᵢ/mᵢ` equals the combined residue divided by the product `M`. For a nonzero
integer with `2*|z| < M`, comparison with `1/2` determines its sign. Replacing
each fraction by `floor(D*aᵢ/mᵢ)/D` has total downward error at most `card/D`;
`D > 2*card*M` preserves the comparison. The maximal prime powers up to
`N=2*B+6` instantiate this specification for a magnitude-bit budget `B`, with
every individual modulus at most `N` and sufficient precision
`D=2^((N+2)*N.size+2)`. The proof uses large products and sums only as mathematical
specifications. The local preparation and streamed arithmetic below now certify
integer sign recovery from residue access and a binary bit budget.

Individual bits of the dyadic quotients now have a uniform FP accessor.
`DyadicQuotientBits.value` takes binary `a,m-1,p,k`, assuming `a<m`, and returns
bit `k` of `floor(2^p*a/m)`. For `k≤p`, the bit is
`((2^(p-k)*a) mod (2*m))/m`; modular exponentiation keeps each word short.
Indices above `p` return zero. The proof covers arbitrary input words and
modulus one, and the implementation's FP theorem holds on every raw string.
`SumBits.evaluator` now certifies accumulation of these bit streams. The carry
is at most the summand count `N`, and every partial column accumulator is at
most `2N`. A single binary counter locates the column and summand, with one
division-by-two step between columns. The exact abstract run returns bit `K`
after `K*(N+1)+N` steps, including `N=0`. The physical suspended evaluator
accounts for child runs and returns a `SpaceFunction` certificate from FP
count/index writers and certified space-bounded summand-bit access.

The sign-specific instantiation is now proved. `DyadicSumBits.evaluator` retains
each query while a certified routine prepares its local numerator/modulus pair,
then reads the dyadic quotient bit with FP postprocessing. The strict magnitude
bound rules out equality at the half threshold, so only one selected sum bit is
needed. If the integer is zero, every local numerator and the whole truncated
sum vanish. `ChineseRemainder.signEvaluator` and `negativeLanguage_mem_PSPACE`
therefore include zero without a separate oracle, under the explicit local
preparation, FP count/precision, and magnitude/precision contracts. The preparation
routine is now constructed from residue access below.

`indexedSystem N` uses all indices `0,...,N`, assigning modulus one to nonprime
indices. Its count is exactly `N+1`, while its product is still `lcmUpto N` and
the previous precision bound still suffices. This avoids requiring an FP prime
count or a compressed prime enumeration in the eventual implementation.

Indexed moduli now have an actual certified evaluator. `PrimalityBits.evaluator`
scans trial divisors with FP modular reduction and retains one Boolean flag;
its answer agrees with `Nat.Prime`, including zero and one. A separate bounded
multiplication routine returns `i^(log i N)`, with each stored magnitude at most
`N+1`, for all binary `N,i`. `ModulusBits.evaluator` composes the routines and
uses FP selection to return the prime power or one. `BoundedFold.evaluator`
accounts for sequential space-bounded updates, and `SpaceFunction.chain` proves
sequential composition using polynomial output bounds.

`CofactorBits.evaluator` streams the complementary product, skips the selected
index, and reduces after each multiplication. Its output agrees with the actual
CRT cofactor modulo the selected modulus. `ModularInverseBits.evaluator` scans
candidates below a positive modulus; coprimality proves that the result equals
`ZMod`'s inverse value, including modulus one. `WeightBits.evaluator` composes
these routines, and `PreparationBits.evaluator` calls the original integer-residue
routine and performs FP modular multiplication to return exactly the local CRT
numerator and modulus-minus-one code.

`IntegerSignBits.evaluator` closes the sign-recovery pipeline. FP writers compute
`N=2*B+6`, count `N+1`, and precision exponent `(N+2)*N.size+2` from the binary
magnitude-bit budget. Indexed-system product, magnitude, and precision theorems
discharge the sign wrapper's remaining hypotheses. A uniform space-bounded
integer-residue routine and FP bit-budget writer therefore give a certified
integer negativity evaluator and PSPACE negative-language theorem. Neither the
integer nor the large CRT modulus or truncated sums are stored.

`CannyResultantBits.IntegerAccess.signumEvaluator` specializes this construction
to the actual integer coefficient and combines it with the existing zero decider.
Its tags are `0` for zero, `1` for negative, and `2` for positive. Both the negative
and positive languages are in PSPACE under the existing FP source degree,
direction, selected-degree, coefficient-residue, and source-bit-budget contracts.
The full coordinate computation's space bound and the
effective critical-point/ETR decision argument remain open.

The subresultant determinant specification is now explicit. For interior order
`k<m,n`, coefficient `r≤k` is the minor with `m-k` shifted `g` columns and `n-k`
shifted `f` columns, selecting coefficient row `r` followed by rows `k+1,k+2,...`.
This follows the ascending-coefficient determinantal construction in
[Definition 1 of the Inria report](https://who.rocq.inria.fr/Alban.Quadrat/PubsTemporaire/RR-9044.pdf),
with Mathlib's block order; its zeroth member is proved equal to Mathlib's
resultant. Mapping coefficients commutes with the construction, its degree is
at most `k`, and the first member is an explicit linear polynomial. Injective
index formulas identify these matrices with submatrices of the full Sylvester
matrix. Integer and parameter-coefficient budgets follow with the reduced
column counts.

`SubresultantPolynomial.ModularAccess.evaluator` now computes a selected modular
parameter coefficient of any selected subresultant coefficient. Binary row/column
selection and validity checks are FP; space-bounded source coefficient routines
supply the entries to the existing polynomial determinant evaluator. The outer
validity branch returns zero even when the invalid minor is empty, whose determinant
would otherwise be one. The corresponding zero language is in PSPACE.

`Subresultant.first_eq_mul_X_sub_C` proves that for degree bounds `m,n>1`, the first
subresultant equals `D*(X-b)` at any common root `b`: the root equations express
the constant row as a linear combination of the positive-degree rows. Hence the
determinant ratio recovers `b` whenever `D≠0`.

`Subresultant.minor_first_one_det_linear_factor` identifies `D` with the resultant
of the quotients after removing `X-b`: the high-coefficient minor is the quotient
Sylvester matrix multiplied by an upper triangular matrix with diagonal entries
one. A Bezout identity for a nonzero linear GCD makes these quotients coprime,
so their resultant is nonzero. Thus `first_spec_of_linear_gcd` proves that the
first subresultant is linear with a nonzero linear coefficient at the actual
input degrees, when both exceed one.

`subresultant_recovery_spec` specializes symbolic parameter polynomials `N,D` to
`p₁(θ-c*x),p₂(x)` and applies the existing separating-pair GCD theorem. For input
degrees greater than one and nonzero direction it proves `D(θ)≠0`,
`b=-N(θ)/D(θ)`, and `a=θ+c*N(θ)/D(θ)`. Both parameter degrees are bounded by
`(d₂-1)*d₁`; their integer coefficients satisfy the reduced-column bit budget.
`CannySubresultantBits.Access.evaluator` now specializes the modular evaluator to
these concrete integer numerator/denominator coefficients, reusing the shifted-input
and constant-input routines. Selection zero is explicitly identified with `N`, and
selection one with `D`. Fixed source degrees preserve the specification through
modular degree drops. The reduced-column coefficient budget is bounded by the full
resultant budget, so the existing FP budget and modulus-scan writers also certify
integer zero testing. Streamed integer sign recovery supplies negativity and the
full three-way sign; zero and both strict-sign languages are in PSPACE under the
same FP metadata, selection, source-residue, and source-bit-budget contracts.
`coordinate_recovery_spec` now removes the interior-degree and nonzero-direction
restrictions from the algebraic recovery statement. If `p₂` is linear, its constant
coefficients recover `b`; otherwise a linear `p₁` uses the shifted input's coefficients;
the remaining case uses the first subresultant. For a separating pair with zero
direction, all roots of `p₂` coincide; separability and splitting therefore force
`p₂` to be linear. Both coordinate polynomials have parameter degree at most
`max 1 ((d₂-1)*d₁)` and a uniform integer coefficient bit budget across the branches.
`CannyCoordinateBits.evaluator` includes these direct branches in the certified
modular coefficient evaluator. FP degree comparisons select the constant right
coefficient, shifted left coefficient, or first-subresultant routine. The explicit
selection identities connect its integer specification to the combined coordinate
numerator and denominator. Its modular coefficient zero language is in PSPACE
under the same FP source-metadata, selection, and original-residue contracts.
`CannyCoordinateBits.integerDecider` and `signumEvaluator` now cover the direct linear
branches as well. Their FP budget writer adds the shifted-input and right-input
allowances to the full resultant budget; the uniform coefficient theorem bounds
every branch by this sum. The zero and both strict-sign languages belong to PSPACE
under the existing FP source metadata, selection, residues, and source-bit budgets.
Signs at algebraic parameter values and the complete
coordinate computation's space bound remain open.

`ChineseRemainderDigits` supplies the exact reconstruction arithmetic behind
integer digit access. Writing `I` for the inverse-weighted integer sum, `M` for
the modulus product, and `T` for the truncated quotient sum at scale `D`, it proves
`D*I=M*T+E`, where `E` is the sum of each local division remainder times its
cofactor and `E≤card*M`. Thus `D>card*M` gives
`I=(M*T+D-1)/D`. It also proves the exact correction rank `T/D=I/M`, including
zero residues, and hence the combined residue is `I-(T/D)*M`. Centered reconstruction
recovers a signed integer under `2*natAbs<M`, with an explicit identity for each
magnitude digit.

`ChineseRemainder.rankBitEvaluator` reads rank bit `k` by reading truncated-sum
bit `precision+k`. `IntegerRankBits.evaluator` combines this with the existing
indexed modulus, inverse-weight, and local preparation certificates. Its rank
is bounded by the modulus count and its binary width by the FP count word length.
The indexed precision and magnitude theorems also specialize the exact centered
reconstruction formula to a binary magnitude budget. `CannyCoefficientRank`
instantiates the rank-bit evaluator for the actual resultant and all-branch
coordinate coefficients. Digit reconstruction uses the large product,
inverse-weighted sum, and rank-product subtraction; none is claimed to fit as a
complete binary word in polynomial space.

`ProductBits.evaluator` now supplies the two-operand multiplication primitive.
For selected index `k`, truncating the left factor to its first `k+1` bits preserves
the product modulo `2^(k+1)`. Each shifted summand's bit is the conjunction of
one left-selector bit, an index guard, and a shifted right bit. Sequentially
composed operand routines supply these bits to `SumBits.evaluator`, whose carry,
workspace, and physical-clock proofs give the product certificate. Both operands
may be implicit and exponentially long. The balanced-product and complete CRT
digit evaluators below use this primitive.

`SubtractBits.evaluator` now certifies ordered natural-number subtraction. At
selected bit `k`, the complemented low `k+1` bits of the second operand plus
one turn subtraction into a three-term sum modulo `2^(k+1)`. The complement
routine uses a source bit and a width guard, and the existing sum machine handles
the carry. `ArithmeticBits` supplies uniform `pair context binaryIndex` product
and subtraction interfaces so their outputs can feed further arithmetic.
`SpaceFunction.select` first runs a space-bounded predicate, retains its response,
then runs one selected child, with all workspace and clocks counted.

`ChineseRemainder.magnitudeBitEvaluatorOfOperands` now composes the product,
ordered subtraction, and computed selection certificates into the final CRT
magnitude-digit computation. The centered residue is `I-Q*M`; negativity selects
`M-(I-Q*M)` when needed. `IntegerDigitBits.evaluatorOfProducts` supplies rank and
sign directly from the original uniform residue routine and FP bit budget.
`IntegerDigitBits.evaluator` also supplies both large operand sources internally,
using the indexed product and weighted-sum implementations below. It computes any
selected magnitude bit from residue access and the FP budget alone;
`magnitudeBitLanguage_mem_PSPACE` places the corresponding query language in
Complexitylib's PSPACE.

`BalancedProduct` now defines the complete product tree, with height-`h` node
`i` covering the factor interval starting at `2^h*i`. Its typed continuation
controller computes one product bit by recursively requesting the two child bits
for each term of a streamed column sum. Frames retain the parent query, scan
counter, carry, and at most one returned selector bit. A carry/continuation
invariant proves the answer. The live-query invariant keeps heights decreasing,
node addresses inside the root tree, and bit indices below the root index `K`;
the stack contains at most `H` frames. A strictly decreasing work allowance proves
termination, the first halting time, and abstract clock bound
`2^(H*(2*K.size+5)+1)`. Every reachable binary state has at most
`128*(H+K.size+1)^2` bits; pairing keeps the continuation tail undoubled.
Initial and child query writers are FP, including binary division for scan
coordinates. Padding with ones identifies complete trees with finite products
and omitted-factor cofactors, including empty families. The binary controller is
FP and simulates every typed transition. `BalancedProduct.treeEvaluator` supplies
a complete `SpaceFunction` certificate from FP count/index writers and a
space-bounded factor-bit evaluator. Suspended calls retain the parent stack;
both child workspace and the expanded physical clock are counted.
`BalancedProduct.evaluator` and `cofactorEvaluator` mask padding and omitted
leaves with FP bits of one, requiring factor-bit correctness only at retained
indices. The count stays binary throughout.

`IndexedProductBits.productEvaluator` and `cofactorEvaluator` instantiate this
algorithm with the certified indexed-modulus evaluator. `BinaryNat.bitAt` reads
word bits at binary indices using unary conversion capped at the word length;
`WordBits.evaluator` retains the query while the word routine runs.
`IndexedSumBits.evaluator` combines local reduced-numerator words, cofactor bits,
the two-operand product evaluator, and the streamed sum evaluator to compute bits
of the inverse-weighted CRT integer sum. Exact semantics identify these operands
with the indexed CRT system used by rank and sign recovery. The complete digit
certificate includes every parent and child workspace and expanded clock.
`CannyCoefficientDigits` specializes it to the actual resultant and all-branch
coordinate coefficients under their existing uniform source/residue/budget contracts.
Signs at algebraic parameter values and the remaining critical-point/ETR argument
are still open.

The explicit sign transformations in Lemma 2.4 now have two further components.
`RationalSubstitution.cleared` expands the substitution `xᵢ=nᵢ(θ)/dᵢ(θ)` after
multiplication by `∏ dᵢ(θ)^(2*degreeOfᵢ p)`. Its exact evaluation identity proves
sign preservation wherever the coordinate denominators are nonzero. The even
powers make this denominator positive, including negative coordinate denominators.
The numerator degree is at most
`∑ᵢ 2*degreeOfᵢ p*max(deg nᵢ,deg dᵢ)`. These algebraic statements include zero
and constant polynomials and empty coordinate families.
`RationalSubstitutionMap.clearedWith` retains explicit degree allowances, proving
that coefficient-ring maps commute with the construction even when modular
reduction kills coefficients and lowers actual degrees.

`CoefficientMass` proves subadditivity, submultiplicativity, and finite
sum/product/power bounds for the sum of absolute integer coefficients.
`RationalSubstitutionBounds` bounds the cleared numerator's coefficient mass by
the source coefficient mass times `∏ Mᵢ^(2*degreeOfᵢ p)` when `Mᵢ` bounds both
coordinate masses. For `A` variables and source variable degrees bounded by `D`,
there are at most `(D+1)^A` supported monomials. Source coefficient magnitudes
at most `2^b₀`, coordinate degrees at most `E`, and coordinate coefficient
magnitudes at most `2^b` therefore give the explicit coefficient bit budget
`b₀+A*(D+1).size+2*A*D*(b+(E+1).size)+1`. The uniform degree allowance is
`2*A*D*E`. `RationalSubstitutionBudget` supplies FP binary writers and semantic
budget theorems for these quantities from arbitrary binary metadata words;
neither a whole source coefficient mass nor the expanded polynomial is computed.
The streamed indexed-source evaluator below supplies modular evaluation with
explicit source access contracts.

`PolynomialProduct` now reduces an indexed polynomial product to one entry of
a shift-matrix power. A one-coordinate layer carries each factor, and exact
power semantics identify the first-to-last entry with the full product, including
the empty family. `PolynomialProduct.ModularAccess.evaluator` uses the existing
polynomial coefficient-matrix and suspended matrix-power certificates. Its FP
control fields supply the factor count, positive modulus, and selected degree;
factor-coefficient access can use polynomial space. The selected-coefficient
zero language is in PSPACE. `ModularSum.evaluator` adds canonical summand residues
through suspended calls, reducing after every addition. The accumulator fits in
the modulus word, including modulus one; the empty sum is zero. These primitives
supply the product and outer-sum computations needed by rational substitution.

`IndexedRationalSubstitution` represents the source as `M` indexed monomials in
`A` variables, allowing repeated exponent vectors, zero coefficients, and
cancellation. A fixed width `W` bounds every exponent; clearing produces
`∑ᵣ aᵣ ∏ᵢ nᵢ^eᵣᵢ dᵢ^(W-eᵣᵢ)`. Coefficient-ring maps commute with this expression.
For even `W`, exact evaluation preserves the source expression's sign wherever
the coordinate denominators are nonzero.

`RationalSubstitution.evaluator` (in `RationalSubstitutionSpace`) computes any selected modular coefficient
by streaming coordinate-factor products, source scalar multiplication, and the
outer term sum through suspended routines. Term/variable counts and width stay
binary; exponent access is FP, and source/coordinate coefficient access may use
polynomial space. Invalid term indices are masked before source access.
`RationalSubstitution.IntegerBits.Access.evaluator` supplies uniform residues of
the actual cleared integer polynomial at packets
`pair (pair context selectedDegree) (m-1)`. It normalizes the modulus field for
source calls and preserves the original width under modular degree drops.

`IndexedRationalSubstitutionBounds` proves degree at most `A*W*E` and coefficient
magnitude-bit length at most `M.size+s+A*W*b+1`, where source coefficients have
magnitude at most `2^s` and coordinate coefficient masses at most `2^b`.
Coordinate degree and coefficient bounds give `b=b₁+(E+1).size`.
`IndexedRationalSubstitutionBudget` writes these bounds in FP, using normalized
word length for `M.size`. `RationalSubstitutionSign` combines the actual residue
evaluator and these budgets with integer sign recovery and the infinitesimal
scan. The output is the cleared numerator's sign throughout some sufficiently
small positive interval. For even width it is also the rational substitution's
sign wherever all coordinate denominators are nonzero. The ETR source bridge
below supplies the encoded source instantiation. The full BKR specialization
used by Canny and the critical-point decision argument are still required.

`ETR.IndexedExpansion` constructs indexed source monomials directly from the
arithmetic expression tree: addition concatenates the two index intervals, and
multiplication uses quotient/remainder to flatten their Cartesian product.
The sum is exactly `Term.toPolynomial`, with no collection of equal monomials.
`IndexedExpansionBounds` proves finite-variable evaluation agrees with the term,
each exponent is at most `Term.degreeBound`, and unused variables have exponent
zero. The count is at most `2^leafCount`. For literal term bit length `N`,
`IndexedExpansionSize` gives count bit length at most `N+1` and indexed coefficient
magnitude at most `2^N`, including negative constants with the original codec.

`ETR.IndexedRationalSubstitution` applies the even-width construction directly
to these syntax-derived monomials. Its evaluation and sign theorems refer to
`Term.eval` of the actual rational coordinate functions. Its degree is at most
`A*(2*degreeBound)*E`, and coefficient magnitude-bit length is at most
`2*N+A*(2*degreeBound)*b+2` when coordinate coefficient masses are at most `2^b`.
The compiled single-equation semantics proves ETR satisfiability equivalent to
the corresponding finite-variable indexed equation.

`MonomialCountData` extends the count algebra to all raw trees, with linear
binary output length even on malformed syntax. `ETR.MonomialCount.read` (in
`MonomialCountFP`) is a uniform FP implementation over the original bracket encoding. Each frame keeps
raw children and their binary counts; its length is at most ten times the raw
frame size. The tree-fold proof bounds every intermediate stack on all binary
inputs. On an encoded term, the reader returns its exact canonical count.
The exponent and coefficient readers below supply individual indexed access for
the full streamed substitution certificate.

`MonomialReaderMachine` visits a selected source monomial without expanding its
siblings: addition chooses one child, and multiplication divides the index by
the right child's count and visits both children. A monoid-valued leaf fold
describes coefficient multiplication and exponent addition. Exact execution takes
at most the original term's encoded size. Pending subtree sizes never increase,
and every child index is at most the initial index.

`MonomialReaderEncoding` supplies FP binary transitions using the actual count
reader and binary arithmetic. `MonomialReaderCorrect` proves exact simulation;
`MonomialReaderBounds` bounds the context, complete task stack, and accumulator
by `2*context.length+4+(4*index.size+20)*termSize+accumulator.length` throughout.
`MonomialReaderFP.reader_mem_FP` combines these results with FP input fields and
a polynomial accumulator bound, accounting for all intermediate states and the
polynomial traversal clock.

`TermView` validates arbitrary term strings in FP, replacing malformed syntax by
the zero expression. `MonomialExponentAtom` compares the selected binary variable
index with each visited unary variable payload and adds zero or one. Its
accumulator is at most the number of steps. Consequently
`MonomialReader.sourceExponent` is a complete uniform FP exponent reader on
`pair context (pair monomialIndex variableIndex)`, with exact canonical output
for the syntax-derived source family. No variable index is expanded to unary.

`IntegerResidueFP` reads the original integer payloads and computes residues in
FP, incrementing the stored magnitude before negation for `-(n+1)`. It handles
modulus one. `MonomialCoefficientAtom` multiplies the accumulator by a constant
residue or by one for a variable. Every partial accumulator fits in the positive
modulus word. `MonomialReader.sourceCoefficient` therefore has a uniform FP
certificate on `pair (pair context monomialIndex) (m-1)`, with exact integer-cast
semantics for every positive modulus. No complete indexed coefficient is stored.

`EncodedRationalSource` supplies a complete source adapter from an FP term field
and FP arity allowance. The default allowance is the validated term's literal
length `N`; the clearing width is `2*N`. Counts, exponent access, coefficient
residues, and source magnitude-bit budgets all have concrete FP implementations.
`RationalSubstitutionBits.Coordinates.evaluator` (in `EncodedRationalSubstitution`) needs only the coordinate
coefficient routines and their residue contracts. Its sign evaluator additionally
uses FP coordinate degree/coefficient bounds and supplies the source budget
internally. The semantic sign theorem refers to `Term.eval` on the actual rational
coordinate values throughout a sufficiently small positive interval, wherever
all coordinate denominators are nonzero.

`CompiledRationalSource` extracts the source term from the existing verified FP
compiler for arbitrary encoded ETR formulas. Every input produces a well-formed
term, whose real zero set is nonempty exactly when the original input belongs to
ETR. In particular, malformed formula inputs keep the compiler's unsatisfiable
default, even though the lower-level term reader uses zero for malformed term
fields. The source side is thus instantiated for general ETR inputs; constructing
the decision procedure's coordinates, determining signs at algebraic parameter
roots, and the effective critical-point decision argument remain open.

`InfinitesimalSign` proves that a real polynomial's sign on some interval
`0<β<δ` equals its trailing coefficient's sign, with a common interval for any
finite family. Injective coefficient maps preserve trailing degree and
coefficient, giving the same theorem for integer polynomials evaluated in the
reals. `InfinitesimalSign.evaluator` scans coefficients in increasing degree and
keeps the first nonzero sign; its accumulator has at most two bits, even when
the degree bound is exponential. Every coefficient call is a suspended child.
`IntegerSignumBits.evaluator` computes three-way integer signs from residue access
by testing negativity of the integer and its negation, with FP modular negation
of residue words. `InfinitesimalSign.evaluatorOfResidues` therefore needs only a
uniform coefficient-residue evaluator and FP binary degree/coefficient-budget
writers, with their semantic bounds. Its output agrees with the sign for all
sufficiently small positive parameters. This implements the small-parameter rule
at the end of Lemma 2.4. The finite-family root-sign count below complements it;
Lemma 2.3's full implicit-family and algebraic-parameter specialization remains
open.

`EffectiveInfinitesimalSign` makes the integer small-parameter bound explicit:
coefficient mass at most `2^b` and `b < s` suffice throughout
`0 < β ≤ 2^(-s)`. The proof factors the lowest power of β and bounds the remaining
tail by the coefficient mass. It includes the zero polynomial and provides the
same threshold for any family with a uniform mass bound.
`DyadicSpecialization` represents `2^(s*D) * p(2^(-s))` as an integer sum and
bounds its binary magnitude by `b+s*D+1` for degree at most `D`.
`DyadicBits.residueEvaluator` streams that sum using modular powers and suspended
original coefficient calls; `signEvaluator` adds the certified CRT sign routine.
No denominator or full specialized integer is stored.

`DyadicPolynomial` specializes coefficients of a polynomial in T over ℤ[β],
using one common clearing degree. Its real image is a positive constant times
the polynomial evaluated at the dyadic β. The smallness bound preserves its
outer degree; without a smallness assumption its degree and mass still have
explicit upper bounds. `DyadicPolynomialBits.residueEvaluator` derives uniform
specialized coefficient access from the original two-index source.
`DyadicTarskiBits.evaluator` composes two such readers with the complete integer
Tarski evaluator. Nonzero scaling preserves roots, and positive scaling
preserves query signs, so the output is exactly the Tarski query of the two
real polynomials at their common selected dyadic parameter. FP bounds and
space-bounded original bivariate readers suffice; query positivity is in PSPACE.

`DyadicSignPatternBits.rootCountEvaluator` extends the specialization to an
indexed family of query polynomials, with uniform degree and inner mass bounds
and the integer evaluator's unary FP family-size certificate. It computes the
exact number of distinct roots realizing the requested signs at the selected
parameter. The coefficient adapters normalize nested indices and supply all
specialized readers from the original bivariate sources. The positivity and
guarded-realizability languages are in PSPACE. A root mass bound `2^b` with
`b < s` preserves nonvanishing of a nonzero original root polynomial, giving
unguarded realizability under that effective hypothesis. These results cover
empty query families and the zero-polynomial finite-root convention.

These evaluator statements concern the selected parameter. The mathematical
stability argument is now proved in `ParameterizedTarski` and
`ParameterizedSignPatterns`. A symbolic pseudo-seed is formed over ℤ[β] at the
original outer degree and derivative-product degree bound. Its leading
coefficient and the head's leading coefficient keep both outer degrees fixed
on a sufficiently small interval. Fixed-bound signed principal coefficients
commute with parameter evaluation. Their trailing-coefficient signs therefore
give the same Tarski query throughout the interval, including constant and zero
heads. `budget` is the binary size of the sum of these finitely many test masses;
`query_eq_value_on_interval` uses β at most `2^(-(budget+1))`.

`patternBudget` takes the maximum test budget over all ternary product queries.
It is independent of the requested sign pattern. `rootCount_stable` proves that
every pattern's exact number of distinct roots is constant on the resulting
common interval. `realizable_stable` derives the same assertion for actual
realizability when the symbolic root polynomial is nonzero; its nonvanishing
throughout the interval is also proved. These budgets are expressions in the
constructed symbolic polynomials.

`NestedCoefficientMass` now proves subadditivity, submultiplicativity, derivative,
and pseudo-reduction estimates for the sum of all absolute bivariate integer
coefficients. `PrincipalParameterMass` bounds an entire determinant's coefficient
mass by a factorial times its column allowances. This bounds the signed principal
tests directly, including terminal and zero branches, without parameter degrees.
`ParameterSourceBounds` combines these estimates. With outer bounds `dp,df` and
total mass bounds `2^bp,2^bf`, the seed mass exponent is
`2*(dp+df+1)*(bp+1)+bf+dp.size+bp`. The principal-test exponent is bounded using
matrix size at most `2*dp`. Original coefficient-mass allowances are converted to
total-mass exponents by adding `(degree+1).size`. For ternary products the uniform
total-mass exponent is `2*k*(bf+(D+1).size)` and the outer degree is at most
`2*k*D`. Hence one source-derived bound works for every ternary query, without
constructing or enumerating the symbolic test polynomials.

`ParameterSourceBudget` provides FP binary writers for these expressions, including
binary size via normalized-word length. The contracts cover all raw metadata
words.

`InfinitesimalRootBits.parameterCode` chooses one more than the uniform
source-derived test bound. `effective_rootCount` proves that the selected-dyadic
count equals the eventual count specified by the symbolic stability interval.
`rootCountEvaluator` then composes the parameter writer with the existing
specialization and integer sign-pattern machines. All specialized coefficient
access is derived from the original bivariate readers.
The original FP degree/mass writers, an FP pattern reader, and a unary FP family
size certificate suffice. Arbitrary metadata encodings, empty query families,
repeated roots, and the zero-polynomial finite-root convention are covered.

`InfinitesimalRootPSPACE` gives the eventual count its quantified semantics.
For a nonzero symbolic root polynomial, positivity is equivalent to
`∃ δ>0, ∀ β, 0<β<δ → ∃ a`, with `a` a real root realizing all requested signs.
The guarded language also requires that symbolic nonvanishing, and belongs to
PSPACE on every input. The unguarded language belongs to PSPACE when all symbolic
root inputs are nonzero. Thus the polynomially bounded finite-family
small-parameter root-sign stage has a complete space certificate. Canny's stronger
implicit family bounds and critical-point construction remain separate obligations.

`ScaledSignQueries` starts the algebraic-root counting stage. At each sign value
`t∈{-1,0,1}`, the integer quadratics `2-2*t²`, `t²-t`, and `t²+t` are twice the
indicators of zero, negative, and positive respectively. Expanding a product of
these indicators proves that an integer combination of ternary product Tarski
queries equals `2^k` times the number of distinct real roots realizing the
requested sign pattern. For a nonzero root polynomial, strict positivity is
equivalent to an actual realizing real root. Repeated roots are counted once;
zero query values and an empty query family are included. The zero root polynomial
uses Mathlib's empty root multiset and is excluded from the realization theorem.

`SignQueryProductSpace.queryProductEvaluator` computes a selected modular
coefficient of `∏ Qᵢ^eᵢ`, `eᵢ∈{0,1,2}`, through the existing suspended product
machine. Two factor slots per polynomial suffice, with unit padding. Binary
count/exponent/modulus/degree fields are FP, and source coefficient routines may
use polynomial space. Empty products and modulus one are covered. Coefficient
maps commute with the query polynomial at fixed exponents, including modular
degree drops.

`SignQueryBits.evaluator` now combines that modular product reader with the
original-source Tarski evaluator. Its only arithmetic children read coefficients
of the root and indexed original polynomials. FP readers give the number of
polynomials, ternary exponents, and original degree/mass allowances. Product
query degree and mass budgets are derived internally as `2*k*D` and `2*k*B`.
Uniform residues normalize the modulus protocol and preserve the selected
coefficient. Empty products and modulus one are covered, and the query's zero,
positive, and negative languages belong to PSPACE under these source contracts.

`IntegerSumBits.evaluator` supplies the outer signed summation primitive for a
binary FP count and a suspended summand evaluator. It accumulates the positive
and negative parts separately, then subtracts them into a canonical signed
result. The summand evaluator's polynomial output bound controls both prefix
counters: their bit lengths grow by at most the binary length of the number of
terms. This includes every nested summand state and clock. FP signed
multiplication is also proved for the pattern-weight products. The complete
scaled-count evaluator below now composes these routines with explicit ternary
enumeration and a certified pattern-weight reader.

`SignQueryBounds` proves query degree at most `2*k*D` and integer coefficient
magnitude-bit length at most `2*k*(b+(D+1).size)+1` for input degree allowance `D`
and coefficient magnitude allowance `2^b`. A Tarski query lies between minus and
plus the root degree. The scaled count has at most `k+rootDegree.size+1` magnitude
bits. `SignQueryBudget` gives FP binary writers and semantic budget theorems from
count and degree words, without unary expansion of their values.

The ternary moment formulation also appears in TauCeti's
[polynomial sign-sum identities](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/RealAlgebraic/SignDetermination/Polynomial.lean)
and [adapted matrices](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/RealAlgebraic/SignDetermination/Adapted.lean).
The complete direct expansion now has a space certificate. `Ternary.count` and
`Ternary.digit` compute binary `3^k` and its query digits with FP modular
exponentiation using a modulus of `2*k+1` bits. The proof matches the enumeration
to Mathlib's equivalence between `Fin k → Fin 3` and `Fin (3^k)`, including `k=0`.
A unary FP certificate for `k` ensures polynomial output length; the binary
count writer alone would not provide this bound.

`SignPatternBits.weightEvaluator` selects the signed factors in the indicator
expansion and multiplies them with a complete suspended-call certificate. Each
factor has magnitude at most two, so every prefix product has at most order `k`
bits. `summandEvaluator` multiplies this weight by the original-source product
Tarski query. `evaluator` sums all `3^k` terms and proves exact agreement with
`scaledRootCount`. `rootCountEvaluator` then uses FP division by `2^k` to return
the binary number of distinct realizing roots. The only arithmetic children
read original root and indexed-polynomial coefficients; the pattern reader and
metadata writers are FP.

The realizability language is in PSPACE when the root polynomial is nonzero.
An unconditional guarded-language theorem includes nonzeroness as part of the
language. Repeated roots are counted once; empty families and the zero
polynomial's empty-root convention are covered. This proves direct sign-pattern
counting for polynomially bounded family size. It does not establish Canny's
stronger polylogarithmic dependence on an implicitly large polynomial family,
its full algebraic-parameter specialization, or the effective critical-point
argument. Those obligations and `ETR ∈ PSPACE` remain open.

## Symmetric recovery degeneracy and bounded asymmetric coordinates

The report's equations (13)--(15) do not always give the asserted linear GCD.
`SymmetricRecoveryDegeneracy` verifies the finite affine system `x^3-x=0, y=0`:
its solutions are `(-1,0),(0,0),(1,0)`, and homogenization has no nonzero solution
at infinity. For direction `(c₀,c₁)`, its nodal eliminant is
`q(X)=X*(X-c₀)*(X+c₀)`, separable when `c₀≠0`. Shifting `c₁` by either sign of
one leaves q unchanged. At the middle projected root zero, reflection gives
`q(-X)=-q(X)`, so the recovery GCD has degree three. The corresponding midpoint
triple makes condition (14) an identity in the direction coefficients. Thus the
claim on page 7 that these bad conditions become nonzero polynomials under
`cᵢ=βⁱ` needs an additional argument or a different construction. This identifies
a gap in the fixed symmetric construction, not a counterexample to the PSPACE
upper bound or the existence statement of Lemma 2.2. Previously proved
univariate recovery theorems retain their explicit separating-pair hypotheses.

`VectorSeparation.exists_bounded_pair_encoding` chooses a positive integer
`k ≤ N^4+1` for which `(a,b) ↦ a+k*b` is injective on all ordered pairs of a
finite N-point set S. Each collision of distinct pairs with unequal second
components excludes at most one scalar; equal second components cannot collide.
There are at most N⁴ excluded slopes, and excluding zero makes k positive.

`AffineGridAvoidance` bounds a common integer nonzero evaluation of m nonzero
affine forms by `0,...,m`. Its family separation theorem allows different affine
offsets on each vector. `AsymmetricProjection.exists_bounded_direction` applies
this to the encoded vector pairs: for every coordinate j, the affine scalar
`L(a+k*b)+k*(aⱼ-bⱼ)` must distinguish all pairs. One further family with zero
offsets ensures that L itself is injective on S. One common integer direction
works, with every coefficient at most `(n+1)*N^4`. No condition is assumed to
remain nonzero when it is identically zero; the vector-pair encoding proves
nonzeroness before the grid theorem is applied.

`AsymmetricCoordinateRecovery` forms nodal polynomials with roots
`L(a)+k*aⱼ` and `L(b)-bⱼ`. They are separable, and their Cartesian root pairs
are separated by `(A,B) ↦ A+k*B`. At a point x, the distinguished pair maps to
`(k+1)*L(x)`. The existing `coordinate_recovery_spec`, including its linear-input
branches, therefore gives a nonzero D and `xⱼ=L(x)+N/D`. Composing N and D with
`(k+1)*X` yields `rationalNumerator/rationalDenominator` in the original parameter
L(x), with denominator degree at most `max 1 ((N-1)*N)` and numerator degree at
most one more. `exists_bounded_rational_coordinates` assembles the bounded choices,
a separable projection eliminant, and simultaneous exact coordinate recovery.

These are finite-set algebraic theorems over a characteristic-zero field.
The nodal products use the supplied point set; they are not yet constructed from
encoded multivariate equations, and no descent to integer coefficients or
multivariate eliminant coefficient routine is supplied by these modules.
The remaining effective multivariate construction, its complexity bounds, and
`ETR ∈ PSPACE` remain open.

## Compactification before critical points

The report's §3.1 starts by substituting `x_i = y_i/(1-y_i²)` and bounding the
new coordinates inside the unit cube. The local route uses the existing
all-input equation compiler first. The remaining strict constraints are then
the cube bounds, while the compiled polynomial equation defines a closed set.

`Geometry.CubeCoordinates` supplies the explicit inverse
`2*x/(1+sqrt(1+4*x²))`, proves it lies strictly between -1 and 1, and proves the
coordinatewise map is onto. Every finite open-cube point has a common positive
margin; the resulting closed inner cubes are compact and nested as the margin
decreases.

`Geometry.CubePolynomial.cleared` is an integer multivariate polynomial, formed
by clearing each coordinate denominator to exponent `2*degreeOf_i(p)`.
Its real evaluation is a positive factor times the original polynomial evaluated
at the rational coordinates. Thus zeros and signs agree on the open cube. Its
total degree is at most `4*sum_i degreeOf_i(p)`, hence at most
`4*n*totalDegree(p)`. Intersecting its zero set with an inner cube is compact.
Existence of an original real zero is equivalent to nonemptiness for some positive
margin, and smaller margins preserve nonemptiness. Linear projections attain
maxima on these compact nonempty sets.

`ETR.FinitePolynomial` translates a term to a polynomial on its actual finite
variable block, preserving evaluation under extension by zero. Its compactified
degree is at most `4*arity*degreeBound`, hence at most `4*dataSize²`.
`ETR.CompactSource.correct` composes this with the existing FP compiler for all
binary inputs. `correct_all_small_margins` gives nonempty compact zero sets for
every sufficiently small positive margin exactly on ETR yes-instances.
The normalized source length provides certified FP dimension and degree upper
bounds. This establishes the semantic compactness stage.

## Additive perturbations

`Geometry.CompactApproximation` proves exact feasibility of a finite continuous
system on a compact set from uniform arbitrarily small violations. The proof
minimizes the sum of negative parts. Approximate feasibility forces this minimum
to be zero, giving an actual point satisfying all constraints.

`PolynomialPerturbation` represents the compactified equation `q=0` by `q≥0`
and `-q≥0`, together with two inner-cube inequalities per coordinate. Each
constraint has an independent additive shift `a_i`, with
`sum_i a_i² = δ²`. A feasible original point gives a perturbed point at every
nonnegative radius by placing a nonnegative shift in one inequality. Conversely,
arbitrarily small feasible perturbations bound the spatial points in `[-2,2]^n`
and give uniform small violations; compact approximation recovers an unperturbed
point. This proves the nonemptiness equivalence used in Lemma 3.2 for the compiled
equation route, including zero-variable inputs. Fixed-radius perturbed sets are
closed and lie in an explicitly bounded product of cubes, hence are compact.

`PerturbationPolynomials` realizes the constraints as integer multivariate
polynomials with separate ε, δ, spatial, and shift variables. For `n` spatial
variables there are `2+2*n` inequalities and `4+3*n` total variables including
the two parameters. Inequality degrees are at most `max(degree(q),1)` and the
radius equation has degree at most two. `ETR.PerturbedSource.correct` instantiates
the construction for every encoded ETR input:
`ETR(bits) ↔ ∃ ε>0, ∃ d>0, ∀ δ, 0<δ<d → Nonempty(T(bits,ε,δ))`.
The equivalent arbitrarily-small-radius statement is also proved. Dimension,
inequality-count, and degree upper bounds have FP binary writers. Compactness
gives extrema for every continuous objective on each nonempty perturbed set.

`AdditiveSubmersion` proves that `(x,a) ↦ f(x)+a` has derivative
`(h,b) ↦ Df(x)h+b`, which is onto via `b ↦ (0,b)`. Polynomial evaluation and
the actual equation/cube constraint maps are smooth, so the result applies to
the full parameterized ETR family.

## Radius slices and critical values

`RadiusLinearization` computes the derivative of
`((x,a),δ) ↦ (f(x)+a, r(a)-δ²)`. Its final coordinate includes `-2*δ*dδ`, so
an explicit preimage proves surjectivity whenever `δ≠0`. At fixed radius the
derivative is `(h,b) ↦ (Df(x)h+b, Dr(a)b)`; it is onto exactly when
`Dr(a) ∘ Df(x)` is nonzero. `SquaredRadius` specializes these formulas to
`r(a)=sum_i a_i²`, with `Dr(a)b=2*sum_i a_i*b_i`, and applies the joint result
to the actual equation/cube family.

`ActiveRadiusLinearization` handles an arbitrary active constraint set S. The
augmented fixed-radius derivative, retaining only the S coordinates and the
radius equation, is onto exactly when either some inactive shift `a_j` is
nonzero or `Dr(a) ∘ Df(x)` is nonzero. The proof supplies explicit derivative
preimages, including an inactive coordinate direction when available.

`ActiveRadiusCritical` uses this criterion at a point with `f_i(x)+a_i=0` for
every active i. A nonsurjective derivative forces all inactive shifts to vanish.
Its weighted spatial derivative is then the negative derivative of
`g_S(x)=sum_{i∈S} f_i(x)²`. The sphere equation gives `g_S(x)=δ²` and the
derivative of `g_S` is zero. Thus every radius failing this active-set
submersion test yields a critical value of a concrete sum-of-squares function.

`CriticalEnergyPolynomial` realizes `g_S` using the existing integer constraint
polynomials after subtracting their shift variables. Its evaluation is independent
of those shifts and of δ, and its total degree is at most
`2*max(degree(q),1)` for the compactified equation q. `ETR.RadiusSource` proves
the joint and active-set statements for every encoded source and supplies an FP
binary degree allowance `8*sourceSize²+4` for the energy polynomial.

`PolynomialCalculus` proves the analytic derivative formula for evaluation of a
multivariate polynomial over any coefficient semiring with a homomorphism to ℝ.
The derivative is the sum of evaluated formal partial derivatives times coordinate
projections. Its vanishing is equivalent to the vanishing of every formal partial,
including in zero spatial dimensions. `SpatialPolynomialCalculus` differentiates
the parameter assignment explicitly, so specializing ε, δ, and shifts retains only
the spatial partials.

`RadiusCriticalEquations` consequently gives an integer polynomial system
`g_S-δ²=0`, `∂g_S/∂y_i=0`, whose zeros are exactly the critical points with value
δ². Every singular active point supplies a zero with the shift coordinates set
to zero. `PartialDerivativeDegree` proves the degree bound `degree(p)-1` for
formal partial derivatives. All equations have degree at most
`2*max(degree(q),1)`. `ETR.RadiusCriticalSource` instantiates the system on every
encoded input, with FP count allowance `sourceSize+1` and degree allowance
`8*sourceSize²+4`. These are size-bound writers, not yet coefficient-access
certificates for the system.

`EtaleDerivation` extends a derivation through a formally etale algebra using
Mathlib's base-change isomorphism for Kahler differentials.
`TranscendentalDerivation` extends a coordinate derivation on a transcendence
basis through its fraction field and the remaining separable algebraic extension.
Thus every transcendental element in a characteristic-zero field extension is
sent to one by some derivation. `CriticalValueAlgebraic` proves the polynomial
chain rule for these derivations: vanishing of all formal partials forces the
value to be algebraic over the coefficient field.

`CriticalValueAnnihilator` applies that result in the fraction field of each
prime quotient containing the gradient ideal. The finitely many minimal primes
supply nonzero annihilating polynomials; their product evaluated at the original
polynomial belongs to the radical gradient ideal. Evaluating at any critical
point gives zero, so the critical values form a finite set. This is a qualitative
annihilator construction, without degree or coefficient estimates.

`PolynomialCriticalValues` specializes the integer energy polynomial to a real
polynomial in the spatial variables. Its analytic critical values are finite.
`RegularRadius` takes a common positive margin below positive critical values
over all active sets. Restricting also to radii below one ensures that δ² lies
below this margin. Every active augmented derivative is then surjective for all
`0<δ<d`. `ETR.RegularRadiusSource.correct` combines this interval with the compact
perturbation correctness theorem on every encoded input. Effective radius
selection, streamed coefficient access, and effective critical-point sampling remain open.

## Critical projection maxima

`ActiveExtremum.isLocalMaxOn_fiber` proves that inactive inequalities remain
positive near a feasible maximum. Fixing the active constraint values and the
radius equation therefore gives a fiber on which the objective is locally
maximal. Its multiplier theorem uses Mathlib's Lagrange theorem and surjectivity
of the equality derivative to exclude a zero objective multiplier. Normalization
gives `L(h)=Λ(DF(h))` for a linear functional Λ on the constraint codomain.

`PerturbedCriticalPoint` proves smoothness of the actual active augmented maps,
selects exactly the constraints vanishing at the maximum, and obtains normalized
multipliers at a maximum of any continuous linear projection on a nonempty
compact regular perturbation. `ETR.CriticalPointSource.correct` applies this to
every encoded input: satisfiability is equivalent to the existence of these
critical maxima for every projection throughout a small regular-radius interval.

`ProjectionEquations` constructs the hypersurface system `p=0` and
`partial_i(p)-v_i*partial_base(p)=0` for `i≠base`. Point and direction variables
are separate blocks; the direction is a parameter in the sampling problem.
There are exactly n equations for n point coordinates. Their total degree,
including the direction block, is at most `max(degree(p),1)`. The coefficient
ring is arbitrary, and integer coefficients remain integer coefficients.
`ProjectionCritical` proves that a local projection maximum on a regular
hypersurface satisfies this system when `v_base=1`. Its coefficient homomorphism
can specialize additional polynomial parameters to real values.

## Active tubes and their integer projection systems

`TubePolynomial` represents ε, δ, and α in the coefficient ring `Z[Option Bool]`.
The outer variables are the original spatial coordinates and every shift
coordinate. Its energy is the square of the radius equation plus the sum of
squares of the active shifted inequalities. Subtracting α gives the tube; its
zero level at α = 0 is exactly the original active common-zero set.

`RegularPolynomialLevels` uses finite critical values to find a positive margin
below every positive critical value of any real polynomial. The derivatives on
levels within that margin are surjective. `TubeRegularity` specializes the tube
energy at fixed ε and δ and takes a common margin over the finitely many active
sets. `TubeProjection` then applies the hypersurface projection theorem. A
root-shift coordinate supplies the base direction coordinate, including when
the compiled source has zero spatial arity.

`NestedPolynomial` uses Mathlib's sum-ring equivalence to expand coefficient
parameters into a variable block. It preserves evaluation and commutes with
point renaming and formal point partial derivatives. `ProjectionFlatten` bounds
the expanded projection equations by the expanded hypersurface degree.
`TubeExpanded` relates the expanded constraints to the earlier integer
perturbation polynomials and proves the full total-degree bound
`2*max(degree(q),2)` for both tube and projection systems. This counts parameter
and direction variables, not just the outer point variables.

`ETR.TubeSource` instantiates the symbolic and ordinary integer systems on every
encoded input. For normalized source size N it supplies FP equation-count
allowance `2+3*N`, point/direction-variable allowance `4+6*N`, expanded-variable
allowance `7+6*N`, and full degree allowance `8*N²+4`. Its common regular α
interval is qualitative and depends on fixed ε and δ. FP writers currently
certify these size bounds. Complete tube/projection coefficient residues are
supplied below; finite generic direction selection and effective parameter
selection remain open.

## Tube approximation at strict maxima

`CompactLevelConvergence` proves that small nonnegative levels in a compact
set lie in any open neighborhood containing its zero locus. It also gives a
joint energy/objective margin near a unique zero-level maximum: sufficiently
small energy and an objective value sufficiently close to the maximum force
the point into any specified neighborhood. The proof uses compact approximate
feasibility for the two inequalities, avoiding a choice of convergent samples.
An arbitrary filtered family whose energy tends to zero and whose objective
value tends to the unique maximum consequently converges to that maximizer.

`LocalLevelApproximation` uses the intermediate value theorem along a continuous
path with zero initial energy and positive energy for positive times. Every
neighborhood of the initial point contains points on all sufficiently small
positive levels. `CompactLevelMaxima` combines this recovery property with
compact separation. Maximizing over a compact level produces local maxima on
the full level, inside any prescribed neighborhood of a unique zero-level
maximum in the interior of the compact set.

`TubeApproximation` supplies the recovery path for the actual tubes at positive
delta: scale the shift vector by `1+t`. Its squared radius strictly increases
for positive t, so the sum-of-squares tube energy is positive. `TubeConvergence`
uses a small compact closed ball to turn a strict local projection maximum
on the active zero locus into the required unique compact maximum. In every
neighborhood, all sufficiently small positive alpha levels then have local
projection maxima satisfying the expanded integer critical equations.

`TubeSigns` preserves all positive inactive constraints in a common neighborhood,
so the approximating critical points can preserve these signs too. It also
proves the converse limit fact: a convergent family of vanishing tube levels
with nonnegative inactive constraints has a feasible limit in the original
perturbed set. `ETR.TubeConvergenceSource.approximation_of_strict_maximum`
instantiates the critical approximation with sign preservation on every encoded
input. Strictness is an explicit hypothesis of that theorem; the supporting
projection construction below now proves existence of a suitable strict
maximum. Effective finite sampling and parameter selection remain open.

## Compact tube sampling converse

`TubeBounds` controls samples with alpha at most one and nonnegative inactive
constraints. The tube's radius-residual square is at most alpha, so the squared
shift norm is at most `delta²+1` and each shift has magnitude at most `delta+1`.
Each active constraint has square at most alpha; inactive constraints are
nonnegative. Thus every constraint is at least -1. The cube constraints give
spatial coordinate bounds `[-(delta+3),delta+3]` when epsilon and delta are
nonnegative. All point coordinates lie in [-4,4] if delta is also at most one.
These bounds are independent of the polynomial and active set.

`TubeFeasibility` selects levels below both the desired squared error and one.
Both signs of the radius equation and all original inequalities then satisfy
the same approximate-feasibility allowance in a common compact box. Compact
approximation supplies an exact feasible point. Active sets may vary with each
sample; no convergent choice of samples or fixed active set is assumed.

The forward direction uses the radial recovery path near any feasible point
at positive radius. Its exact active set has positive inactive constraints in
a common neighborhood, producing positive-inactive samples on every sufficiently
small positive level. For nonnegative epsilon and positive delta, perturbed
feasibility is therefore equivalent both to arbitrarily small weak-inactive
samples and to one active set supplying eventual positive-inactive samples.

`TubeProjectionFeasibility` extracts the tube equation from the first row of the
expanded integer projection system. Arbitrarily small projection roots with
nonnegative inactive constraints imply feasibility, even if active sets and
directions vary. `ETR.TubeFeasibilitySource` translates the two equivalences into
ETR correctness statements and proves soundness of the projection-root criterion
for every encoded input. The qualitative forward direction with finite critical
root sets and coefficient residue machines are supplied below. Effective
direction selection and parameter choices remain open.

## Finite critical sets imply strict maxima

`IsolatedCriticalMaximum` proves a topological isolation argument: a nearby point
tied with a local maximum is itself a local maximum. Finiteness of a set containing
all local maxima therefore makes each local maximum strict. On a regular smooth
fiber, normalized Lagrange multipliers put every local maximum in the normalized
critical set. Finiteness of that set suffices; a Hessian or nondegeneracy theorem
is unnecessary for this step.

`TubeCriticalMaximum` transports this result to the actual active constraints
and radius equation. A projection maximum on the compact perturbed inequality
set is locally maximal on its active fiber. If that fiber is regular and has
finitely many normalized critical points, the maximum is strict on its active
zero locus. Its positive-inactive tube critical approximations follow from the
existing recovery and compact convergence theorems.

`TubeCriticalSampling` consequently supplies projection-system roots with
positive inactive constraints on every sufficiently small positive tube level.
One direction and one active set work throughout the interval. For a normalized
direction with finite active critical sets, this criterion is equivalent to
perturbed feasibility. `ETR.TubeCriticalSamplingSource` gives the corresponding
ETR equivalence retaining finite active critical sets for the chosen direction,
assuming suitable finite-critical directions exist throughout a small-radius
interval. The converse needs no such assumption. Existence and effective
selection of directions with finite active critical sets remain open. Later
modules establish tube-root finiteness and qualitative sampling completeness.

## Compact supporting projections and semantic completeness

`CompactSupportingProjection` supplies a strict linear projection maximum on
any nonempty compact set in finite-dimensional real coordinate space. Choose a
center whose designated coordinate is one below the minimum on the compact
set, then maximize squared Euclidean distance from that center. If p is a
maximizer, the identity

`D(a,x)-D(a,p) = 2*(p-a)·(x-p)+D(p,x)`, where `D(a,x)=Σᵢ(xᵢ-aᵢ)²`,

shows that `(p-a)·x < (p-a)·p` for every other point x in the set. The designated
coordinate of p-a is positive, so positive rescaling normalizes it to one.
This argument does not assume finite critical sets or genericity.

`TubeSupportingSampling` applies the construction to the compact perturbed
inequality set. Near a feasible maximum, all inactive constraints remain
positive, so the active zero locus is feasible there. The supporting maximum
is consequently strict on that zero locus. The existing tube approximation
then supplies integer projection-system roots with positive inactive signs at
every sufficiently small positive alpha, for one fixed normalized real
direction and active set.

`ETR.TubeSupportingSamplingSource` makes the projection-root semantic criterion
unconditionally equivalent to ETR satisfiability on all encoded inputs. It also
proves equivalence to arbitrarily small projection samples, where directions
and active sets may vary. These are existence statements over the reals.
Finite root sets containing suitable samples are supplied below; effective
selection and enumeration, parameter bounds, and the full PSPACE decision
procedure remain open. Coefficient residue machines are supplied below.

## Algebraic generic coordinates

`MvCoefficientDerivation` applies a derivation coefficientwise to a multivariate
polynomial, fixing its variables. `FieldDerivationExtension` holds a
transcendence basis fixed, then uses localization and separability to extend
any derivation through an arbitrary characteristic-zero field extension.
`CoordinateDerivation` instead differentiates one generator of an independent
family and fixes all the others, after extending that family to a basis.

`AlgebraicDerivative` differentiates a minimal polynomial with respect to both
its coefficients and its root. Separability makes the root derivative's
coefficient nonzero. The derivative is a quotient of polynomial values at the
root, and is therefore algebraic over the coefficient field whenever that
field is preserved by the derivation.

`ProjectionCoordinateAlgebraic` applies these results to normalized stationarity
on a common zero locus. A coefficient-field derivation kills the projection
value because the stationarity equation turns its derivative into a linear
combination of the constraint derivatives. The value is therefore algebraic
over the direction field. A derivation with respect to one independent direction
coordinate differentiates that value into the corresponding point coordinate.
Every point coordinate is consequently algebraic. For directions normalized
at one coordinate, independence of the remaining direction coordinates
suffices: they recover the other point coordinates, and the projection value
then recovers the normalized coordinate.

`FiniteAlgebraicZeros` proves a general finiteness criterion. If all coordinates
are algebraic in the fraction field of each minimal-prime quotient of a
polynomial ideal, each coordinate has a nonzero univariate annihilator modulo
the radical. Products over the finitely many minimal primes supply these
annihilators uniformly. The zero set lies in the finite product of their root
sets. No effective bounds on these annihilators are supplied yet; applying the
criterion to the regular projection systems is established below.

## Finite generic tube projection roots

`GenericProjectionFinite` adjoins one reciprocal variable t to the normalized
projection equations and adds `t*partial_base(p)-1=0`. At every solution in a
field extension, stationarity holds with multiplier t. Generic normalized
coordinate algebraicity makes all point coordinates algebraic over the direction
field; t is algebraic too because it is the reciprocal of a polynomial value
at those coordinates. Applying this argument in every minimal-prime quotient
field gives a finite extended zero set. Its projection contains all roots with
nonzero base partial derivative, so that regular projection-root set is finite.

`FiniteProjectionRoots` connects the algebraic statement to analytic regularity.
If a normalized projection root had zero base partial, its equations would
force every partial derivative to vanish, contradicting surjectivity of the
real hypersurface derivative. Thus every projection root on a regular
hypersurface belongs to the finite set just constructed. Coefficients may be
specialized through a smaller characteristic-zero field; independence is
required only over that field.

`TubeFiniteRoots` applies the theorem to the actual expanded integer projection
systems. At each sufficiently small regular positive alpha level, the root set
is finite whenever coefficient specialization factors through a field K and
the non-base direction coordinates are algebraically independent over K. The
common regularity interval is independent of this choice. The statement permits
a field and direction appropriate to the chosen level; it does not assert one
field containing every real alpha while retaining independent real directions.
Suitable fields and directions are constructed below. Finite effective direction
search, uniform parameter specialization, quantitative annihilator bounds, and
the full sampling algorithm remain open.

## Countable parameter fields and dense finite-root directions

`TubeParameterField` adjoins the three specialized real parameters to the
rationals. Cardinality bounds for finitely generated intermediate fields make
this field countable. Its coefficient map composes with the real inclusion to
give the actual tube specialization.

`IndependentRealDirections` proves that algebraic real elements over a countable
embedded coefficient ring form a countable union of finite polynomial root
sets. Every nonempty real interval therefore contains a transcendental element.
Induction on finite coordinate types constructs an independent tuple inside
any prescribed product of nonempty open intervals. At each step the already
generated polynomial algebra is countable.

`GenericDirectionNeighborhood` fixes the designated coordinate at one and
applies the interval construction to the remaining coordinates. Independent
normalized directions consequently occur in every neighborhood of every
normalized real direction. `TubeGenericDirections` combines this density with
the actual tube parameter field and regularity interval: at each sufficiently
small positive level, directions yielding finite projection root sets for all
active sets occur in every such neighborhood. The choice may vary with the
level. Positive inactive signs are preserved by the argument below; effective
finite direction selection remains open.

## Qualitative finite tube sampling correctness

`ProjectionContinuity` proves joint continuity of projection evaluation in the
direction and point. Compactness makes changes of direction uniformly small
over a compact point set.

`CompactLevelPerturbedMaxima` strengthens small-level recovery near a unique
zero-level maximum. Its conclusion holds for any continuous objective
uniformly close to the original objective on the compact neighborhood. Compact
separation supplies a positive objective margin; recovery supplies a level
point within one third of that margin. Uniform changes smaller than one third
leave every maximizing point above the separation threshold, inside the
prescribed neighborhood and the interior of the compact set.

`TubeFiniteSampling` starts with a strict supporting projection maximum and
chooses a compact neighborhood and a positive-inactive neighborhood around it.
At each sufficiently small positive alpha, dense generic directions give a
nearby normalized direction with finite projection root sets for every active
set. The uniform objective bound keeps a local tube maximum in the
positive-inactive neighborhood. Regularity makes it a root of the actual
expanded integer projection system.

The resulting `EventualFiniteProjectionSamples` criterion uses one fixed
active set throughout the interval. The normalized real direction may vary
with alpha; all active root sets are finite for each chosen direction, and
one of them contains a sample with positive inactive constraints. Perturbed
feasibility is equivalent to this criterion when epsilon is nonnegative and
delta is positive. `ETR.TubeFiniteSamplingSource.correct` lifts that equivalence
to every encoded ETR input. Effective finite direction search, root enumeration,
quantitative parameter and annihilator bounds, and the complete PSPACE decision
procedure are not yet established.

## Finite-fiber specialization and integer direction grids

`FiniteFiberSpecialization` clears a fraction-field coordinate annihilator to
a nonzero polynomial over the parameter ring. Localization of radical ideals
gives a further nonzero parameter multiple whose coordinate evaluation lies
in the original radical. Multiplying these parameter factors and the cleared
polynomials' leading coefficients gives one nonzero element d. Under any field
specialization where d stays nonzero, the specialized coordinate polynomials
remain nonzero and vanish on every solution. Their root sets give a finite
product containing the entire specialized zero set. No bound on d is supplied.

`ProjectionFiniteSpecialization` treats the non-base direction coordinates as
polynomial parameters. Their fraction-field images are independent, so generic
coordinate algebraicity applies to each minimal-prime quotient field. The
specialization theorem yields a nonzero exceptional polynomial in the direction
parameters. Its nonvanishing guarantees a finite extended projection fiber,
without requiring the specialized direction itself to be independent.

`PolynomialGridAvoidance` uses Mathlib's combinatorial Nullstellensatz: a nonzero
polynomial cannot vanish on a product of sets larger than its coordinate
degrees. In characteristic zero, coordinates in `0,...,B` suffice whenever B
bounds its total degree. Products give simultaneous avoidance for finite
families, using a bound on the sum of their degrees. Consequently a normalized
direction with natural-number coordinates and a finite extended projection
fiber exists. The current grid bound is the degree of an existential exceptional
polynomial; an input-size bound, a certified construction of that polynomial,
and size bounds for suitable encoded direction choices remain open.

`IntegerProjectionDirections` transfers the finite extended-fiber theorem to
the actual projection equations on regular real hypersurfaces. Regularity
forces a nonzero base partial at each root; the reciprocal variable therefore
covers every projection root. For a finite family of hypersurfaces, multiply
their exceptional conditions and use a grid bound given by the sum of their
degrees. One normalized direction with natural-number non-base coordinates
gives finite root sets for the whole family. Coefficients can be supplied by
any homomorphism into the reals.

`TubeIntegerDirections` instantiates this family with all active tubes. Every
sufficiently small positive level has a finite natural-number direction grid
containing a common direction with finite root sets for every active set.
The bound and direction may depend on epsilon, delta, and alpha. This does not
yet give one integer direction throughout a small-alpha interval or ensure
that the chosen direction preserves a positive-inactive sample. These and
the quantitative input-size bound remain open.

## Nearby rational directions avoiding exceptional conditions

`PolynomialRationalAvoidance` puts an arbitrarily large finite rational grid
inside any nonempty real interval. Applying the combinatorial Nullstellensatz
to the real images of such grids finds a rational tuple avoiding any nonzero
real polynomial inside any prescribed open coordinate box. Products give
simultaneous avoidance of finite families of exceptional polynomials.

`RationalProjectionDirections` keeps the base coordinate equal to one and
chooses the other coordinates in a sufficiently small rational box. Every
neighborhood of a normalized direction consequently contains a normalized
rational direction whose projection root sets are finite for every member of
a regular finite hypersurface family. `TubeRationalDirections` supplies these
nearby rational directions for all active tubes at each small regular level.

The compact small-level sampling argument in `TubeFiniteSampling` now accepts
a predicate on directions. A nearby finite-root selector satisfying that
predicate yields samples whose directions retain it. The original unrestricted
sampling theorems use the always-true predicate. This interface preserves the
single active set and all positive inactive signs while supporting restricted
direction witnesses. Effective rational height bounds remain open.

## Rational finite sampling correctness

`TubeRationalSampling` instantiates the direction-predicate sampling theorem
with rational directions. Nearby rational finite-root choices keep the local
tube maximum inside the positive-inactive neighborhood. The resulting
`EventualRationalFiniteProjectionSamples` statement retains an explicit tuple
of rational non-base direction coordinates at each level, with the base
coordinate normalized to one.

One active set works throughout each small-level interval. The rational tuple
may vary with alpha; for every chosen tuple, all active projection root sets
are finite and the selected active set has a root with positive inactive
constraints. This criterion is equivalent to perturbed feasibility for
nonnegative epsilon and positive delta. `ETR.TubeRationalSamplingSource.correct`
proves the corresponding equivalence for every encoded ETR input.

The following stronger result now supplies a direction fixed across the interval.

## One rational direction throughout a tube-level interval

`MvCoefficientChainRule` differentiates a polynomial's coefficients and its
evaluation point. `ProjectionParameterAlgebraic` uses direction derivations
that fix the constraint polynomial, even when some coefficients lie outside
the derivations' base field. Extending these derivations to the critical-point
field makes every point coordinate algebraic over the coefficient field.
`ProjectionParameterCoordinates` includes the reciprocal of the base partial
derivative in this conclusion.

`LevelProjectionSpecialization` uses the joint ring of level and direction
parameters. Coordinate derivations differentiate a direction parameter while
fixing the level. Algebraicity in minimal-prime quotient fields and denominator
clearing give a nonzero joint exceptional polynomial. Every field specialization
avoiding it has finitely many extended projection roots. No evaluation of a
rational-function field at a real level is needed.

`UniformRationalProjectionDirections` views the exceptional polynomial as a
univariate polynomial in alpha with direction-polynomial coefficients. A nearby
rational direction avoids its nonzero leading coefficient, leaving a nonzero
univariate polynomial. Its trailing-coefficient sign theorem gives an interval
of positive levels where it never vanishes. Products handle finite families.
Regularity then removes the reciprocal variable and gives finite projection
root sets. `TubeUniformRationalDirections` applies this to the actual tube
energies and expanded integer systems for all active sets.

`TubeFiniteSampling.exists_sample_neighborhood_of_strict` factors the compact
objective-stability argument: every normalized direction in one neighborhood
has positive-inactive samples on every sufficiently small positive level.
Choosing the uniform rational finite-root direction there proves
`UniformRationalFiniteProjectionSamples`. One active set and one rational tuple
work throughout the interval; the tuple may depend on epsilon and delta.
`ETR.TubeUniformRationalSamplingSource.correct` proves this criterion equivalent
to encoded ETR satisfiability. Quantitative exceptional-polynomial bounds,
rational height bounds, effective parameter choices, root enumeration, and
the full PSPACE decision procedure remain open.

## Coefficient bit budgets for the actual tube systems

`MvCoefficientMass` defines the sum of absolute integer coefficients for
multivariate polynomials. It is subadditive and submultiplicative, cannot
increase under variable renaming, and grows by at most the total degree under
one partial derivative. These statements permit variable collisions and zero
polynomials, and require no expansion algorithm.

`ETR.PolynomialMass` relates constant magnitudes to their binary payload sizes.
Expression-tree induction bounds the finite-variable source polynomial's mass
by `2^N`, for encoded term size N. `CubePolynomialMass` bounds each denominator
factor `1-X_i²` by two in coefficient mass. The total exponent in denominator
clearing is at most twice the sum of the source's coordinate degrees. The
compactified source consequently has mass at most `2^(N+2*N²)`.

`TubeCoefficientMass` bounds the flattened radius mass by `c+1` and every
flattened constraint mass by `H+4`, for c constraints and source mass H. The
integer tube mass is at most `(c+1)²+c*(H+4)²+1`, uniformly over active sets.
Formal partial derivatives and the additional direction variable bound each
flattened projection row by `(4*max(degree(p),2)+1)` times this allowance.
All parameter and direction variables are included.

`ETR.TubeCoefficientBounds` combines these estimates with the existing source
arity and degree bounds. Both integer tube and projection polynomials have
mass at most `2^(20*N²+6*N+21)`; each coefficient has at most
`20*N²+6*N+22` magnitude bits. The budget has an FP writer from the normalized
compiled source size, on all binary inputs. It bounds actual integer
coefficients. Complete coefficient residue machines are supplied below.
Exceptional-polynomial bounds, effective direction and parameter selection,
and the full decision procedure remain open.

## Collected source coefficients in polynomial space

The earlier indexed coefficient reader returns one expansion term. Repeated
monomials must still be combined to obtain an actual polynomial coefficient.
`ETR.CollectedCoefficients` proves the required sum identity for the finite
source polynomial, with all cancellations retained.

`FixedWidthNatVector` gives exact block-encoding round trips.
`CollectedCoefficientQuery` uses validated source length N as its dimension
and N+1 bits per exponent. It reads exponent blocks from arbitrary words and
checks every coordinate against an indexed monomial in FP. Short words supply
zero high bits; extra blocks are ignored. Source validation continues to use
the existing zero-term default for malformed encodings.

`CollectedCoefficientSpace` streams all indexed monomials, contributes zero
for a mismatch, and otherwise reads the indexed coefficient residue. Its
modular accumulator collects the actual coefficient, with parent and child
states included in the `SpaceFunction` certificate. Modulus one and repeated
or cancelling monomials are covered.

`CollectedCoefficientSign` uses the proved N+1 magnitude-bit budget to recover
coefficient negativity through the existing CRT sign algorithm. The negative
language belongs to Complexitylib's PSPACE. `CollectedCoefficientZero` scans
the small moduli justified by the same budget, using the full residue routine
as a child; the coefficient-zero language also belongs to PSPACE. This supplies
the zero test needed for detecting actual degrees after cancellation.

`SourceCoefficientSpace` supplies the compiled ETR source fields and proves
query correctness for every binary source input. Its finite polynomial uses N
variables; the unused variables contribute no nonconstant monomials. Every
nonzero coefficient has coordinate exponents at most the source degree and
therefore an exponent query of exactly `N*(N+1)` bits. This is collected access
to the source before compactification. Access through active tubes and projection equations is supplied below. Quantitative
sampling bounds and the complete ETR PSPACE decision procedure.

## Actual source degrees after cancellation

The compactification uses the original integer polynomial's coordinate degrees.
Syntax degree bounds and degrees after modular reduction do not in general
equal these values. `CollectedDegree` proves a cancellation-aware formula:
scan the indexed source monomials, discard those whose collected coefficient
is zero, and maximize their selected-variable exponents. Every nonzero
coefficient occurs in the indexed expansion, so this gives exactly `degreeOf`.
The zero polynomial gives zero.

`FixedWidthNatVectorFP` writes vectors from FP coordinate readers, and
`MonomialExponentVector` builds each selected indexed monomial's exact exponent
query. The source's degree bound ensures every exponent fits. This avoids
enumerating a larger grid of all possible monomials.

`BoundedMaximum` retains one binary maximum while calling a certified child
over a binary-sized range. Its workspace includes the saved parent and child
states. `CollectedDegreeSpace` uses the full coefficient zero decider as the
predicate child, then streams the surviving exponents through this maximum.
Its `SpaceFunction` returns the actual coordinate degree; binary variable
indices outside the padded dimension return zero. All malformed-source
defaults are retained.

`FinitePolynomialPadding` proves that enlarging the variable dimension above
the syntax arity only renames the source polynomial, preserving actual degrees
of original variables. `SourceDegreeSpace.value_original_variable` therefore
returns exactly the degree used for denominator clearing in the compactified
compiled ETR source. This supplies actual-degree access without an oracle.
`CubeCoefficientFormula` now combines it with binomial factors, as described
below. Tube/projection coefficient residues are also supplied below.
Quantitative sampling bounds and the complete ETR PSPACE algorithm remain open.

## Streamed compactification coefficients

`SeparateVariableCoefficients` proves that a coefficient of a product of
univariate polynomials in distinct variables is the product of the requested
univariate coefficients. `CubeFactorCoefficients` gives the coefficient of
`X^e*(1-X²)^s`: it is zero unless `e ≤ k` and `k-e` is even, and otherwise is
`choose s ((k-e)/2) * (-1)^((k-e)/2)`.

`CubeCoefficientFormula` packages clearing fixed denominator degrees as an
additive map. Applying it to the indexed syntax expansion gives exactly the
existing geometry polynomial, even when indexed source monomials cancel.
The denominator exponents use the collected integer polynomial's actual
coordinate degrees; no degree after modular reduction is substituted.

`CubeFactorResidue` combines the existing polynomial-space binomial routine
with FP modular powering and multiplication. `ModularProductSpace` retains
one reduced residue while suspending a certified factor child, including for
the empty product and modulus one. `CompactCoefficientQuery` prepares each
factor using the actual-degree child and target exponent blocks of width
`4*N²+1`. `CompactCoefficientSpace` streams the coordinate product and then
the indexed source-term sum. Its certificate includes the saved inputs,
accumulators, child states, and clocks at both loop levels.

The generic routine accesses `cleared (Term.finitePolynomial N t)` with
`N` the validated source length. `CompactCoefficientPadding` proves that
zero-padding the exponent query preserves coefficients in the original arity:
extra variables have source degree zero and contribute a factor of one.
`CompactSourceCoefficient` supplies the compiled ETR input fields and proves
exact query correctness for `CompactSource.polynomial`. The exponent query
has length `N*(4*N²+1)`; the proved compactification degree bound ensures every
nonzero coefficient is representable. Malformed source strings retain the
compiler's existing default semantics.

`CompactCoefficientSign` proves a coefficient mass bound of `2^(N+2*N²)`
for the padded compactification, hence a magnitude-bit budget of
`N+2*N²+1` with an FP writer. The full residue evaluator instantiates CRT
sign recovery, proving coefficient negativity in Complexitylib's PSPACE.
`CompactCoefficientZero` scans the small moduli justified by the same budget
and proves coefficient zero testing in PSPACE. Both routines include the
actual-degree and binomial children; they assume no coefficient oracle.
`CubePolynomialMultiplication` proves that clearing fixed coordinate
allowances respects products whose exponents fit those allowances. Actual
coordinate degrees of nonzero integer products add; handling zero factors
separately therefore proves `cleared (p*q) = cleared p * cleared q` and
`cleared (p^k) = (cleared p)^k`.

`TermPowerFP` retains the validated source once while writing one multiplication
per unary-counted round. The encoded expression grows linearly in the exponent
and source length, giving an FP writer for every unary FP exponent. No monomial
expansion is constructed. `CompactPowerCoefficient` composes it with the full
compactification evaluator. For positive powers, zero-padded queries provably
access coefficients of the original-arity compact polynomial raised to that
power; power zero is also handled in the evaluator's own padded dimension.

`TubeCoefficientDecomposition` proves an exact identity for the existing
expanded integer tube: a multiple of the embedded source square, the embedded
source times a linear shift, and the same tube with source zero. The square's
multiplicity is the number of active source-equation constraints, at most two.
The linear shift has at most their two shift coordinates. Thus the only dense
product needed for tube access is already supplied by the power routine.
`EmbeddedCoefficient` proves exact guarded access through injective variable
embeddings: all other coordinate exponents must be zero. Multiplication by one
variable shifts the source query by one. Embedded partial derivatives need one
incremented source query, multiplied by its integer exponent.
`TubeCoefficientFormula.coeff_integerPolynomial` extracts one source-square
coefficient, two possible shifted source coefficients, and one zero-source tube
coefficient. `ProjectionCoefficientFormula` expresses a flattened partial row
using two embedded derivative queries and a direction-variable shift.
`TubeCoefficientFormula` specializes both level and partial formulas to the
existing `integerProjection` definition.

`TermArityFP` computes the exact syntax arity with a raw tree fold, then validates
the source view. Numeric payload subtrees cannot contribute spurious variable
indices. Every encoded frame and stack has linear length in its raw tree,
including malformed inputs. A cap by validated source length yields a unary FP
arity reader as well as binary output. `TubeEncoding` gives explicit finite
equivalences for the point/shift/parameter coordinate layout and the constraint
order. Its active-set bitmask has exactly `2+2*n` bits and a proved round trip.

`TubeZeroSyntax` gives the zero-source tube as a short ETR term: the squared
radius expression, squares of the active affine constraints, and minus alpha.
Its finite polynomial equals the existing integer tube after the explicit
coordinate renaming. `TubeZeroBounds` proves exact syntax arity, including empty
active sets and zero-dimensional sources; the delta coordinate forces the full
layout. `TubeZeroFP` certifies serialization through polynomial range loops and
the sum-of-squares writer, without distributing products.

`FinitePolynomialCoefficientPadding` proves coefficient preservation under
zero-padding beyond the syntax arity. `TubeZeroSpace` composes the FP writer
with the full collected-coefficient routine. Native-coordinate queries have
proved padding and renaming round trips, and every nonzero coefficient is
representable by the fixed-width query. Coefficient residue access, negativity,
and zero testing have complete polynomial-space certificates. Arity and active
mask fields are arbitrary unary FP/FP functions, so the exact compiled-source
arity reader supplies the required dimension without an oracle.

`FixedWidthQuery` supplies FP binary-indexed coordinate access, with indices
capped for polynomial-time block slicing. Coordinates beyond the declared
prefix return zero. A certified repacker changes widths and pads coordinates,
and bounded coordinate guards are in FP.

`TubeZeroQuery` accepts an arbitrary FP exponent-block width and target word.
An FP guard checks every native coordinate against four. Failure forces the
actual integer tube coefficient to vanish by its proved degree bound; success
makes every exponent fit the sparse reader's format. The repacker has an exact
native-coordinate round trip, so truncation cannot turn an oversized exponent
into a nonzero coefficient. The complete guarded evaluator has a
`SpaceFunction` certificate on all inputs, including short/redundant words,
zero-width blocks, empty active sets, and modulus one.

`EmbeddedMonomialCoefficient` proves coefficient lookup for an injectively
embedded polynomial multiplied by a monomial disjoint from its variable image.
The restricted point exponent determines the only possible source query; a
single exponent-pattern equality checks the other coordinates.
`TubeDenseEncoding` turns that equality into the explicit native tube layout,
and `TubeDenseGuard` certifies its bounded binary-coordinate check in FP.

`TubeDenseMetadata` supplies the exact source arity and the written source-power
size M. The actual integer compact polynomial power has total degree at most
`4*M²`, with an FP bound and query-width writer. `TubeDenseQuery` checks both
that degree allowance on point exponents and the required zero/unit pattern
elsewhere. Rejection provably gives coefficient zero. Accepted queries are
repacked into the complete compactified-power evaluator. The resulting
`SpaceFunction` covers positive fixed powers, either source-shift variable,
malformed source defaults, arbitrary target words, and modulus one.
Its unshifted square and shifted first powers agree exactly with the three
dense terms in the existing tube coefficient formula.

`SpaceFunction.pairOutputs` retains one child response while running the next,
with space and clock bounds for the saved context. `TubeCoefficientSpace`
combines the source square, two source shifts, and sparse remainder using FP
modular arithmetic. `TubeSourceCoefficient` instantiates this complete tube
residue evaluator on compiled ETR inputs.

`TubeProjectionEncoding` adds a direction block between tube point and parameter
coordinates. `TubeProjectionGuard` certifies the zero/unit direction patterns in
FP. `TubeProjectionRepack` removes that block and optionally increments a tube
exponent. Its W+1 output width preserves even the largest W-bit exponent plus
one. `TubeProjectionRestriction` proves native correctness and composes the
complete tube child.

`TubeProjectionFactor` reads and increments derivative factors in binary, then
multiplies residues in FP. `TubeProjectionTermFormula` and `TubeProjectionTermSpace`
connect the guarded evaluator to embedded native polynomials and derivatives.
`TubeProjectionRows` proves the actual level/partial row identities and assembles
their evaluators, including modular subtraction of the two partial-row terms.
`TubeProjectionRowEncoding` has a total decoder: zero or invalid codes select
the level row; valid positive codes enumerate nonbase partial rows. Every native
row has a round trip. `TubeProjectionSpace` therefore certifies coefficient
residues of the actual integer projection system on every binary input.

`TubeProjectionNative` proves native exponent-query round trips.
`TubeSourceProjectionCoefficient` supplies the compiled ETR packet format and
FP field readers. The proved degree bound makes every nonzero coefficient
representable with at most `(6*N+7)*(8*N²+5)` exponent bits. All positive moduli,
including one, are covered.

`TubeCoefficientDecisions` derives magnitude-bit budgets directly from the actual
tube and projection coefficient mass bounds. Its lifted packet readers compose
the complete residue evaluators with CRT negativity and three-way sign recovery.
Coefficient negativity and positivity are in PSPACE. `IntegerZeroSpace` packages
the generic small-modulus zero scan for a certified residue child and FP binary
bit-budget writer; it also supports exponential budgets without unary expansion.
This proves zero testing for both full polynomial families in PSPACE. Native
coefficient-query equalities connect the predicates to representable exponents
of the actual compiled-input polynomials.

`FixedWidthPolynomial` uses the finite base-2^W function equivalence to enumerate
exponent vectors by binary rank. Injectivity and support coverage prove exact
reconstruction from actual coefficients, rather than expansion terms.
`FixedWidthPolynomialFP` writes the exponential term count with A*W+1 bits and
certifies binary coordinate readers, including invalid-index handling.
`FixedWidthPolynomialLayout` transports these statements through native variable
equivalences using a total-degree allowance.

`TubeIndexedSource` supplies the actual tube/projection source identities, with
W equal to the binary size of `8*N²+4`. All source metadata has FP writers.
`TubeIndexedSpace` connects arbitrary binary ranks to the complete native residue
machines, with FP source, active-mask, row, and modulus fields. The mathematical
term family is never materialized. `TubeIndexedBounds` retains the actual source
coefficient mass bound for every rank and supplies an FP even denominator-power
allowance `2^W`, bounded by twice the full degree allowance. These establish the
source-side contracts for streamed rational substitution.

`TubeRationalSource` instantiates the existing integer substitution family with
actual tube or projection coefficients. A static flag chooses the layout;
source, active mask, and row are FP fields of the caller context. The rank/modulus
packet conversion has a full space certificate and canonical residue equality.
`TubeRationalSubstitution` supplies the source and metadata internally. Its only
remaining coefficient-reader parameters are the rational-coordinate numerator
and denominator readers, each with a complete space certificate and modular
query contract.

`TubeRationalCorrect` proves exact equality with even denominator clearing of
the native tube/projection polynomial. The original rational evaluation and the
cleared polynomial's trailing coefficient have the same sign for sufficiently
small positive parameters wherever all coordinate denominators are nonzero.
A native row wrapper keeps the projection decoder's metadata arity separate
from the statement's native coordinate type.

`TubeRationalBounds` derives FP output-degree and coefficient-bit writers from
coordinate degree/coefficient bounds and actual source mass bounds. No actual
output-degree oracle or assumed source-coefficient bound is used.
`TubeRationalDecisions` composes the complete residue child with CRT sign
recovery, small-modulus zero testing, and the streamed trailing-coefficient scan.
The coefficient zero/negative tests are in PSPACE. `TubeRationalLanguages`
proves polynomial identity and either strict trailing-coefficient sign in PSPACE
under the same coordinate-reader contracts. Concrete sampler coordinate readers, quantitative
parameter selection, and the complete ETR PSPACE decision procedure remain open.

## TM2 versus Complexitylib's machines

The project now fills one class-level composition gap in Complexitylib's pinned
API. `nonempty_spaceDecider_of_mem_PSPACE` encodes any PSPACE machine using
Cobham's fixed-block representation in a polynomial space window. FP transition,
halting, and verdict operations, exact run simulation, and the existing
configuration-count theorem supply a complete `SpaceDecider` certificate.
`SpaceDecider.precompose` composes its space/clock polynomials with the output
length polynomial of an FP preprocessing function. Consequently PSPACE is
proved closed under FP preimages and polynomial-time many-one reductions.
`existsReal_subset_PSPACE_iff` discharges the class-theoretic consequence:
`∃ℝ ⊆ PSPACE ↔ ETR ∈ PSPACE`. This leaves the ETR algorithm proof open.

The distinction affects implementation and resource-accounting effort, even though
the intended polynomial-space classes agree mathematically.

* `lean-trominoes` uses Mathlib's `FinTM2`: a finite collection of stacks and structured
  statements for push, pop, peek, branching, and control transfer. Its PSPACE package
  requires finite alphabets on **all** stacks and bounds the total occupied stack
  cells on every reachable configuration. Finite labels and finite internal state
  prevent storage hidden in the control. Its input cells count toward space.
* [Complexitylib's base model](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Models/TuringMachine.lean)
  is a custom multitape TM, structurally closer to Mathlib's TM0 than to TM2. It uses
  local read/write/head transitions, a fixed four-symbol alphabet, read-only input,
  and named work/output tapes. It is not an instance of Mathlib's TM0. Its decision
  space predicate also bounds output and excursions of the input head.

TM2 gives a more convenient programming language, but not free arithmetic on arbitrary
integers. Such values still need finite encodings and proofs about the space used to
manipulate them. Conversely, using Complexitylib need not mean writing every algorithm
as individual tape transitions:

* [`SpaceIter.mem_PSPACE_of_iterate`](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Classes/Space/Iterate.lean)
  supplies a machine from a polynomial-time bitstring step function, polynomially
  bounded states, and a bounded terminating run (at most `2^poly` steps). There are
  also FP composition/iteration tools and polynomial-space folds.
* `lean-trominoes` has evaluator workspace certificates and a prepared-evaluator
  bridge to its TM2 PSPACE predicate. These can avoid rebuilding stack accounting
  for each arithmetic subroutine. The bridge already composes polynomial-time input
  preparation with space-certified evaluation, retaining the original input-length
  parameter. This is a concrete advantage. Its benefit depends on implementing the
  algorithm in that evaluator language.

Complexitylib also defines a higher-level
[rose-tree machine language](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Models/RoseTreeMachine/Prog.lean).
Its documentation explicitly states that no simulation theorem connecting its cost
model to the multitape TM has been proved. An RTM cost certificate alone would therefore
leave a bridge obligation before establishing membership in Complexitylib's `FP` or `PSPACE`.

An ordinary tape can be represented by two stacks, and finite alphabets admit
constant-size binary codes. This explains why a space-preserving simulation is
plausible, up to input-size overhead. **No proved bridge between these two library
PSPACE predicates has been established in this project.** Existing Mathlib
computability simulations cannot simply be assumed to preserve the required space.

The useful benchmark is a concrete symbolic-arithmetic routine with encoded inputs,
encoded intermediate states, and a workspace proof through the intended iteration
interface. For Canny, streamed access to large symbolic objects matters more than
the surface machine language alone. The current arithmetic and power-controller
implementation targets Complexitylib's FP/SpaceIter interface. A separate reusable
module would be justified by its interfaces or proved interoperability, not merely
by having fewer files; the TM2 evaluator remains a possible comparison target.

The project now supplies a concrete benchmark for that comparison: a continuation
machine for one entry of a matrix power, with balanced recursion and a streamed
summation. Its result, exact abstract transition count, and logarithmic frame count
are proved. Its binary representation is injective, and states over `ZMod m` have
a quadratic bound in the binary lengths of the dimension, exponent, and modulus.
Exact decoding and a total encoded transition now preserve the typed run and its
state-size bound. Binary normalization, successor, predecessor, and exponent halves
have actual Complexitylib FP certificates, as do the initial and child-query writers.
Binary addition, multiplication, comparison, subtraction, and modular reduction are
certified too, with exact semantics on all words and bounds on intermediate states.
A uniform modular multiply-accumulate callback takes the modulus as a binary input
and agrees with the machine's `ZMod` residue encoding, including modulus one.
The full context-carrying controller now has an FP certificate from explicit FP
callbacks, including matrix-entry access. Its correctness theorem simulates every
typed transition on encoded states; the modular specialization supplies the scalar
callbacks. Packet initialization is FP from certified binary field writers, and
the size bound includes the retained original context. The project now proves
`MatrixPower.ModularAccess.zeroLanguage_mem_PSPACE`: testing whether a selected modular
matrix-power entry is zero belongs to Complexitylib's PSPACE under canonical FP
field/entry access on every context. The proof supplies the exact first halting
time, FP completion and answer tests, and a general halting-loop wrapper for
SpaceIter. Dimension and exponent can be exponential in the context length.
A concrete input format still must validate or default malformed inputs to meet
the access contract, including valid indices and a nonzero modulus.
The direct callback contract still requires FP entry access. The new suspended
entry interface requires FP certificates only for the child initializer,
transition, halting test, and output projection. It saves the parent while the
child runs. A prefix classification accounts for every intermediate physical
state; parent/child bounds `S,U` give `2*S+U+3` bits. Polynomial state bounds and
exponential parent-step and child-run clocks yield Complexitylib PSPACE through
`SubroutineIteration.mem_PSPACE`. Its hypotheses concern only reachable parent
states and requested calls. The direct factor formulas and the uniform scalar-moment
child now form the complete determinant-factor evaluator, including certified
binary case selection and trailing-block query writers. Its result correctness,
exact first halting time, quadratic workspace bound in the dimension/modulus
binary lengths, and exponential clock bound are proved. Its saved query packet
is included in that workspace bound. The suspended outer determinant controller
now meets the combined polynomial-workspace and exponential-time contracts,
giving the modular determinant PSPACE theorem above.

Local comparison sources, at `lean-trominoes` commit
`6fe52dd234bb616fd4fb3c1e7b0a203de1482bc5`:

* `../lean-trominoes/LeanTrominoes/Complexity/Complexity.lean`
* `../lean-trominoes/LeanTrominoes/Computation/Partrec/PartrecPreparedEvaluatorSpace.lean`
* `../lean-trominoes/LeanTrominoes/Computation/Partrec/PartrecGenericSavitchReachSpace.lean`

The current `lean-wang` main branch inspected earlier did not itself define PSPACE;
the relevant Mathlib-only package was found in `lean-trominoes`.

## Savitch's theorem and Canny

Savitch is useful for reachability in an implicitly represented exponential graph,
as occurs in the report's roadmap/motion-planning consequences. Each vertex and the
recursion stack need polynomial-size representations. The adjacency algorithm also
needs a proved workspace bound; treating adjacency as a free Boolean oracle would
leave an essential gap.

The report's §3.1 ETR procedure instead gives a deterministic enumeration and algebraic
sign-testing argument. Savitch is not a substitute for its algebraic space analysis,
and need not be a dependency of that particular proof.

Savitch support is available in **both** candidate libraries:

* [Complexitylib](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Classes/Containments/NPSPACESubsetPSPACE.lean)
  proves `NPSPACE ⊆ PSPACE` and equality of the two polynomial-space classes. Its
  public statement explicitly does not provide the general quantitative theorem
  `NSPACE(S) ⊆ DSPACE(S²)`.
* `lean-trominoes` has a generic Savitch evaluator, reachability correctness, encoded
  search-state bounds, and workspace certificates. Its generic leaf interface accepts
  an evaluator-space certificate for adjacency, not only a polynomial-time test.

Neither result automatically transports algorithms or class membership across the
two machine models.
