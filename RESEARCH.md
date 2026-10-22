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
part gives $T(g) = a\cdot \operatorname{low}(g) - \operatorname{low}(p)\cdot \operatorname{high}(g)$, for $a = p[d]$.
When $\operatorname{degree}(p) \le d$, this equals $a\cdot g - p\cdot \operatorname{high}(g)$. With input degree bound `D`,
$2\cdot (D+1)$ iterations lower the result below `d` and give a positive scaling when
`p` has actual degree $d > 0$. The integer Tarski-query theorem therefore uses
an integral seed and integral principal determinants.

The operator is represented by a $(D+1)$-dimensional scalar matrix. Each entry
is zero, an original head coefficient, or its negation. The certified entry
controller derives all source queries and modular negations internally.
`PseudoRemainderBits.DataAccess.evaluator` combines suspended original-head and
input coefficient routines with the existing scalar-moment evaluator, proving
complete modular coefficient access without storing any intermediate remainder.
Fixed bounds commute with coefficient maps even if the modular head degree drops.
If head and input coefficient masses are bounded by $2^{\mathrm{bp}}$ and $2^{\mathrm{bg}}$, a coefficient
after `n` steps has at most $n\cdot (\mathrm{bp}+1)+\mathrm{bg}+1$ magnitude bits. FP binary writers supply
this budget from original degree/coefficient bounds. The derivative-product
source instantiation, integer coefficient signs, and actual-degree routines are
now composed with the constant-head branch and principal-determinant pipeline
below. The full $\mathrm{ETR} \in \mathrm{PSPACE}$ theorem is not yet established.

`DerivativeBits.evaluator` reads an original coefficient at binary index $k+1$
and multiplies it modulo the supplied modulus. `DerivativeProductBits.Access.evaluator`
then computes a selected coefficient of the actual product $f\cdot p'$ from the two
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
$5\cdot k.\operatorname{size} + 10$ bits. The certificate includes all sign-reader state and clock
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
selection, the effective critical-point algorithm, and $\mathrm{ETR} \in \mathrm{PSPACE}$ remain open.

No existing encoded ∃ℝ complexity-class definition or formal proof of $\mathrm{ETR} \in \mathrm{PSPACE}$
was found in the inspected Mathlib, Complexitylib, CSLib, TauCeti, or adjacent projects.
The ∃ℝ definition in this project uses the standard reduction-class formulation;
equivalence with other finite presentations requires explicit efficient translations.

Mathlib already proves the ordinary
[primitive element theorem](https://github.com/leanprover-community/mathlib4/blob/728a93eeff833da3173895bb0575752fdc24edb0/Mathlib/FieldTheory/PrimitiveElement.lean),
including a linear-GCD argument for two separable elements. Its Galois fixed-field and
Lagrange interpolation theorems also supply the algebraic tools used here. The current
project strengthens the representation interface to all pairs of roots of two input
polynomials, with one bounded integer selector, a monic separable degree-$d_{1}\cdot d_{2}$
polynomial, and coordinate polynomials over the input field. The GCD coefficient-ratio
recovery specification is proved. The parameter polynomial now uses Mathlib's
[Sylvester resultant](https://github.com/leanprover-community/mathlib4/blob/728a93eeff833da3173895bb0575752fdc24edb0/Mathlib/RingTheory/Polynomial/Resultant/Basic.lean),
with verified specialization, roots, scalar normalization, and degree. Taylor and Hasse
derivatives supply a direct shifted-coefficient formula and integer bit-length bounds.
The project now bounds coefficients of polynomial determinants by column coefficient
masses, and specializes this estimate to the integer resultant. Its degree is at most
$d_{1}\cdot d_{2}$ without nonzero or separability hypotheses, and its coefficient bit lengths
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
recurrence behind Berkowitz's algorithm. Coefficients of $\operatorname{adj}(XI-A)$ are expressed
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
$(n+1)^{2}$ and exponent `n`. It therefore reuses the existing continuation machine
and bitstring controller under their explicit entry-access contract. Stored residue
states have at most $64\cdot (3\cdot n.\operatorname{size}+m.\operatorname{size}+2)^{2}$ bits; retaining context `c` adds
$2\cdot c.\operatorname{length}+2$. The abstract clock is at most $2^{(2\cdot n.\operatorname{size}+3)\cdot n.\operatorname{size}+1}$, counting
entry access as one operation. A generic suspension wrapper and PSPACE composition
theorem now account for a saved parent alongside a running child. The power
controller intercepts exponent-one entry queries, runs the child through FP steps,
and resumes the original stack with its output. Correct and terminating calls
simulate the full abstract power run. Direct factor access is now proved through
the trailing principal block, with no lookup of preceding factors. The factor
cases are one, a negative diagonal entry, a negative scalar moment, or zero.
Adding a source and sink reduces $r A^k c$ to a power entry in dimension $n+2$.
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
controller and proves modular determinant zero testing in Complexitylib2's PSPACE.
It assumes FP canonical dimension/modulus fields and FP original-matrix entries
on every input, with a nonzero modulus. Dimension can be exponential in the input
length. The proof includes the retained parent and child packets and the expanded
physical clock; it assumes no FP computation of whole factor entries.
Integer determinant zero testing now also belongs to PSPACE under FP dimension
and binary determinant-bit-budget access and uniform FP original-entry residue
access. Mathlib's LCM growth bound implies that an integer of at most `B`
magnitude bits is zero exactly when its residues modulo $1,\ldots ,2\cdot B+4$ vanish.
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
bound $2^b$ gives the computed resultant bit budget $N.\operatorname{size}\cdot N+N\cdot b+1$, with $N=m+n$.
`Resultant.Access.zeroLanguage_mem_PSPACE` proves resultant zero testing under
FP degree and coefficient-budget fields and uniform FP coefficient-residue access
on all contexts and indices. A corollary uses the ordinary resultant when the
degree fields equal the actual polynomial degrees. Later modules provide symbolic
modular coefficient evaluation and generic integer sign recovery. Residue algorithms
for all polynomial constructions used in the report remain open.

The project now supplies an explicit binomial-residue routine for the shifted
coefficient formula. The lower bidiagonal matrix with diagonal and subdiagonal
one has `choose n k` at row `k`, column zero of its nth power in dimension $k+1$.
This identity holds over any semiring. Concrete FP binary writers and entry
access instantiate the modular power controller, including arbitrary positive
composite moduli and modulus one. `BinomialResidue.evaluator` returns the complete
residue through a `SpaceFunction` certificate with first halting time, polynomial
state bounds, and an exponential clock. All binary input words are covered;
$k>n$ returns zero. Modular power evaluation now exposes the same output interface,
and FP final predicates derive PSPACE decision procedures from it.
The shifted-coefficient residue evaluator now combines the binomial child with
the original coefficient and the power of the negative direction. Binary modular
exponentiation has an FP certificate by repeated squaring, with every fold result
bounded by the modulus word. FP input preparation and an explicit input-retention
wrapper preserve the complete resource certificates. `ShiftCoefficientBits.certified`
returns exactly the coefficient of $x^i \theta ^j$ in $p(\theta -c\cdot x)$ modulo the supplied
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
triangular coefficient matrix of width $d+1$, preserving addition and
multiplication. Entrywise application and block flattening preserve powers.
`Berkowitz.det_coeff_eq_coefficientPower` consequently expresses degree `d`
of a determinant over `R[X]` as a signed power entry over `R`, in dimension
$(n+1)^{2}\cdot (d+1)$. `PolynomialPower.ModularAccess.evaluator` now implements the
generic polynomial matrix-power coefficient operation. FP binary controls
and a `SpaceFunction` routine for original entry coefficients suffice. The
flattened accessor decodes each coordinate by division/remainder and returns
one input coefficient or zero, with its own space certificate. This covers
all binary contexts and gives modular coefficient zero testing in PSPACE.
`PolynomialMoment.ModularAccess.evaluator` specializes it to coefficients of
$r A^k c$: taking an entry coefficient commutes with source/sink augmentation,
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
instantiation. The shifted-coefficient child accesses $p_{1}(\theta -c\cdot x)$ and an FP
degree-zero guard accesses $p_{2}(x)$. The result is proved equal to a coefficient
of the existing integer `cannyResultant`, reduced modulo any positive modulus.
The fixed integer source degrees are preserved through modular reduction.
The contract requires FP source degrees, direction, and selected output degree,
plus uniform FP residue access to both original integer coefficient functions.
Its modular coefficient zero test is in PSPACE.

`CannyResultantBits.IntegerAccess.decider` extends this to zero testing of the
integer coefficient. For source degrees `m,n`, direction `c`, and coefficient
bounds $2^{b_{1}},2^{b_{2}}$, its computed budget is
$B = (m+n).\operatorname{size}\cdot (m+n) + n\cdot S + m\cdot (b_{2}+1) + 1$, where
$S = (m+1).\operatorname{size} + m + (b_{1}+1) + (c+1).\operatorname{size}\cdot m$.
The previous coefficient-size theorem proves this budget; binary arithmetic
and encoded word lengths give FP budget writers. The bounded modulus scan
then composes the concrete residue decider and tests moduli $1,\ldots ,2\cdot B+4$, with
all child states included. FP source-bit-budget fields and the residue-access
contracts suffice, even when `B` is exponential. The sign evaluator below uses
the same budget and residue-access contracts; the magnitude-bit evaluator below
also consumes these contracts.

The reconstruction specification now has a proved CRT route. A coprime modulus
system uses locally reduced inverse-weighted numerators `aᵢ`; the fractional part
of $\sum a_{i}/m_{i}$ equals the combined residue divided by the product `M`. For a nonzero
integer with $2\cdot |z| < M$, comparison with $1/2$ determines its sign. Replacing
each fraction by $\operatorname{floor}(D\cdot a_{i}/m_{i})/D$ has total downward error at most $\operatorname{card}/D$;
$D > 2\cdot \operatorname{card}\cdot M$ preserves the comparison. The maximal prime powers up to
$N=2\cdot B+6$ instantiate this specification for a magnitude-bit budget `B`, with
every individual modulus at most `N` and sufficient precision
$D=2^{(N+2)\cdot N.\operatorname{size}+2}$. The proof uses large products and sums only as mathematical
specifications. The local preparation and streamed arithmetic below now certify
integer sign recovery from residue access and a binary bit budget.

Individual bits of the dyadic quotients now have a uniform FP accessor.
`DyadicQuotientBits.value` takes binary `a,m-1,p,k`, assuming $a<m$, and returns
bit `k` of $\operatorname{floor}(2^p\cdot a/m)$. For $k\le p$, the bit is
$((2^{p-k}\cdot a) \mathrm{mod} (2\cdot m))/m$; modular exponentiation keeps each word short.
Indices above `p` return zero. The proof covers arbitrary input words and
modulus one, and the implementation's FP theorem holds on every raw string.
`SumBits.evaluator` now certifies accumulation of these bit streams. The carry
is at most the summand count `N`, and every partial column accumulator is at
most `2N`. A single binary counter locates the column and summand, with one
division-by-two step between columns. The exact abstract run returns bit `K`
after $K\cdot (N+1)+N$ steps, including $N=0$. The physical suspended evaluator
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

`indexedSystem N` uses all indices $0,\ldots,N$, assigning modulus one to nonprime
indices. Its count is exactly $N+1$, while its product is still `lcmUpto N` and
the previous precision bound still suffices. This avoids requiring an FP prime
count or a compressed prime enumeration in the eventual implementation.

Indexed moduli now have an actual certified evaluator. `PrimalityBits.evaluator`
scans trial divisors with FP modular reduction and retains one Boolean flag;
its answer agrees with `Nat.Prime`, including zero and one. A separate bounded
multiplication routine returns $i^{\operatorname{log} i N}$, with each stored magnitude at most
$N+1$, for all binary `N,i`. `ModulusBits.evaluator` composes the routines and
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
$N=2\cdot B+6$, count $N+1$, and precision exponent $(N+2)\cdot N.\operatorname{size}+2$ from the binary
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
$k<m,n$, coefficient $r\le k$ is the minor with `m-k` shifted `g` columns and `n-k`
shifted `f` columns, selecting coefficient row `r` followed by rows $k+1,k+2,\ldots$.
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

`Subresultant.first_eq_mul_X_sub_C` proves that for degree bounds $m,n>1$, the first
subresultant equals $D\cdot (X-b)$ at any common root `b`: the root equations express
the constant row as a linear combination of the positive-degree rows. Hence the
determinant ratio recovers `b` whenever $D\ne 0$.

`Subresultant.minor_first_one_det_linear_factor` identifies `D` with the resultant
of the quotients after removing `X-b`: the high-coefficient minor is the quotient
Sylvester matrix multiplied by an upper triangular matrix with diagonal entries
one. A Bezout identity for a nonzero linear GCD makes these quotients coprime,
so their resultant is nonzero. Thus `first_spec_of_linear_gcd` proves that the
first subresultant is linear with a nonzero linear coefficient at the actual
input degrees, when both exceed one.

`subresultant_recovery_spec` specializes symbolic parameter polynomials `N,D` to
$p_{1}(\theta -c\cdot x),p_{2}(x)$ and applies the existing separating-pair GCD theorem. For input
degrees greater than one and nonzero direction it proves $D(\theta )\ne 0$,
$b=-N(\theta )/D(\theta )$, and $a=\theta +c\cdot N(\theta )/D(\theta )$. Both parameter degrees are bounded by
$(d_{2}-1)\cdot d_{1}$; their integer coefficients satisfy the reduced-column bit budget.
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
restrictions from the algebraic recovery statement. If $p_{2}$ is linear, its constant
coefficients recover `b`; otherwise a linear $p_{1}$ uses the shifted input's coefficients;
the remaining case uses the first subresultant. For a separating pair with zero
direction, all roots of $p_{2}$ coincide; separability and splitting therefore force
$p_{2}$ to be linear. Both coordinate polynomials have parameter degree at most
$\max\{1,(d_{2}-1)d_{1}\}$ and a uniform integer coefficient bit budget across the branches.
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
$D\cdot I=M\cdot T+E$, where `E` is the sum of each local division remainder times its
cofactor and $E\le \operatorname{card}\cdot M$. Thus $D>\operatorname{card}\cdot M$ gives
$I=(M\cdot T+D-1)/D$. It also proves the exact correction rank $T/D=I/M$, including
zero residues, and hence the combined residue is $I-(T/D)\cdot M$. Centered reconstruction
recovers a signed integer under $2\cdot \operatorname{natAbs}<M$, with an explicit identity for each
magnitude digit.

`ChineseRemainder.rankBitEvaluator` reads rank bit `k` by reading truncated-sum
bit $\mathrm{precision}+k$. `IntegerRankBits.evaluator` combines this with the existing
indexed modulus, inverse-weight, and local preparation certificates. Its rank
is bounded by the modulus count and its binary width by the FP count word length.
The indexed precision and magnitude theorems also specialize the exact centered
reconstruction formula to a binary magnitude budget. `CannyCoefficientRank`
instantiates the rank-bit evaluator for the actual resultant and all-branch
coordinate coefficients. Digit reconstruction uses the large product,
inverse-weighted sum, and rank-product subtraction; none is claimed to fit as a
complete binary word in polynomial space.

`ProductBits.evaluator` now supplies the two-operand multiplication primitive.
For selected index `k`, truncating the left factor to its first $k+1$ bits preserves
the product modulo $2^{k+1}$. Each shifted summand's bit is the conjunction of
one left-selector bit, an index guard, and a shifted right bit. Sequentially
composed operand routines supply these bits to `SumBits.evaluator`, whose carry,
workspace, and physical-clock proofs give the product certificate. Both operands
may be implicit and exponentially long. The balanced-product and complete CRT
digit evaluators below use this primitive.

`SubtractBits.evaluator` now certifies ordered natural-number subtraction. At
selected bit `k`, the complemented low $k+1$ bits of the second operand plus
one turn subtraction into a three-term sum modulo $2^{k+1}$. The complement
routine uses a source bit and a width guard, and the existing sum machine handles
the carry. `ArithmeticBits` supplies uniform `pair context binaryIndex` product
and subtraction interfaces so their outputs can feed further arithmetic.
`SpaceFunction.select` first runs a space-bounded predicate, retains its response,
then runs one selected child, with all workspace and clocks counted.

`ChineseRemainder.magnitudeBitEvaluatorOfOperands` now composes the product,
ordered subtraction, and computed selection certificates into the final CRT
magnitude-digit computation. The centered residue is $I-Q\cdot M$; negativity selects
$M-(I-Q\cdot M)$ when needed. `IntegerDigitBits.evaluatorOfProducts` supplies rank and
sign directly from the original uniform residue routine and FP bit budget.
`IntegerDigitBits.evaluator` also supplies both large operand sources internally,
using the indexed product and weighted-sum implementations below. It computes any
selected magnitude bit from residue access and the FP budget alone;
`magnitudeBitLanguage_mem_PSPACE` places the corresponding query language in
Complexitylib2's PSPACE.

`BalancedProduct` now defines the complete product tree, with height-`h` node
`i` covering the factor interval starting at $2^h\cdot i$. Its typed continuation
controller computes one product bit by recursively requesting the two child bits
for each term of a streamed column sum. Frames retain the parent query, scan
counter, carry, and at most one returned selector bit. A carry/continuation
invariant proves the answer. The live-query invariant keeps heights decreasing,
node addresses inside the root tree, and bit indices below the root index `K`;
the stack contains at most `H` frames. A strictly decreasing work allowance proves
termination, the first halting time, and abstract clock bound
$2^{H\cdot (2\cdot K.\operatorname{size}+5)+1}$. Every reachable binary state has at most
$128\cdot (H+K.\operatorname{size}+1)^{2}$ bits; pairing keeps the continuation tail undoubled.
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
`RationalSubstitution.cleared` expands the substitution $x_{i}=n_{i}(\theta )/d_{i}(\theta )$ after
multiplication by $\prod d_{i}(\theta )^{2\cdot \operatorname{degreeOf}_{i} p}$. Its exact evaluation identity proves
sign preservation wherever the coordinate denominators are nonzero. The even
powers make this denominator positive, including negative coordinate denominators.
The numerator degree is at most
$\sum _{i} 2\cdot \operatorname{degreeOf}_{i} p\cdot \operatorname{max}(\operatorname{deg} n_{i},\operatorname{deg} d_{i})$. These algebraic statements include zero
and constant polynomials and empty coordinate families.
`RationalSubstitutionMap.clearedWith` retains explicit degree allowances, proving
that coefficient-ring maps commute with the construction even when modular
reduction kills coefficients and lowers actual degrees.

`CoefficientMass` proves subadditivity, submultiplicativity, and finite
sum/product/power bounds for the sum of absolute integer coefficients.
`RationalSubstitutionBounds` bounds the cleared numerator's coefficient mass by
the source coefficient mass times $\prod M_{i}^{2\cdot \operatorname{degreeOf}_{i} p}$ when `Mᵢ` bounds both
coordinate masses. For `A` variables and source variable degrees bounded by `D`,
there are at most $(D+1)^A$ supported monomials. Source coefficient magnitudes
at most $2^{b_{0}}$, coordinate degrees at most `E`, and coordinate coefficient
magnitudes at most $2^b$ therefore give the explicit coefficient bit budget
$b_{0}+A\cdot (D+1).\operatorname{size}+2\cdot A\cdot D\cdot (b+(E+1).\operatorname{size})+1$. The uniform degree allowance is
$2\cdot A\cdot D\cdot E$. `RationalSubstitutionBudget` supplies FP binary writers and semantic
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
$\sum _{r} a_{r} \prod _{i} n_{i}^{e_{ri}} d_{i}^{W-e_{ri}}$. Coefficient-ring maps commute with this expression.
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

`IndexedRationalSubstitutionBounds` proves degree at most $A\cdot W\cdot E$ and coefficient
magnitude-bit length at most $M.\operatorname{size}+s+A\cdot W\cdot b+1$, where source coefficients have
magnitude at most $2^s$ and coordinate coefficient masses at most $2^b$.
Coordinate degree and coefficient bounds give $b=b_{1}+(E+1).\operatorname{size}$.
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
zero. The count is at most $2^{\mathrm{leafCount}}$. For literal term bit length `N`,
`IndexedExpansionSize` gives count bit length at most $N+1$ and indexed coefficient
magnitude at most $2^N$, including negative constants with the original codec.

`ETR.IndexedRationalSubstitution` applies the even-width construction directly
to these syntax-derived monomials. Its evaluation and sign theorems refer to
`Term.eval` of the actual rational coordinate functions. Its degree is at most
$A\cdot (2\cdot \mathrm{degreeBound})\cdot E$, and coefficient magnitude-bit length is at most
$2\cdot N+A\cdot (2\cdot \mathrm{degreeBound})\cdot b+2$ when coordinate coefficient masses are at most $2^b$.
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
by $2\cdot \mathrm{context}.\operatorname{length}+4+(4\cdot \mathrm{index}.\operatorname{size}+20)\cdot \mathrm{termSize}+\mathrm{accumulator}.\operatorname{length}$ throughout.
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
FP, incrementing the stored magnitude before negation for $-(n+1)$. It handles
modulus one. `MonomialCoefficientAtom` multiplies the accumulator by a constant
residue or by one for a variable. Every partial accumulator fits in the positive
modulus word. `MonomialReader.sourceCoefficient` therefore has a uniform FP
certificate on `pair (pair context monomialIndex) (m-1)`, with exact integer-cast
semantics for every positive modulus. No complete indexed coefficient is stored.

`EncodedRationalSource` supplies a complete source adapter from an FP term field
and FP arity allowance. The default allowance is the validated term's literal
length `N`; the clearing width is $2\cdot N$. Counts, exponent access, coefficient
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
$0<\beta <\delta$ equals its trailing coefficient's sign, with a common interval for any
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
coefficient mass at most $2^b$ and $b < s$ suffice throughout
$0 < \beta \le 2^{-s}$. The proof factors the lowest power of β and bounds the remaining
tail by the coefficient mass. It includes the zero polynomial and provides the
same threshold for any family with a uniform mass bound.
`DyadicSpecialization` represents $2^{s\cdot D} \cdot p(2^{-s})$ as an integer sum and
bounds its binary magnitude by $b+s\cdot D+1$ for degree at most `D`.
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
guarded-realizability languages are in PSPACE. A root mass bound $2^b$ with
$b < s$ preserves nonvanishing of a nonzero original root polynomial, giving
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
`query_eq_value_on_interval` uses β at most $2^{-(\mathrm{budget}+1)}$.

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
total mass bounds $2^{\mathrm{bp}},2^{\mathrm{bf}}$, the seed mass exponent is
$2\cdot (\mathrm{dp}+\mathrm{df}+1)\cdot (\mathrm{bp}+1)+\mathrm{bf}+\mathrm{dp}.\operatorname{size}+\mathrm{bp}$. The principal-test exponent is bounded using
matrix size at most $2\cdot \mathrm{dp}$. Original coefficient-mass allowances are converted to
total-mass exponents by adding $(\operatorname{degree}+1).\operatorname{size}$. For ternary products the uniform
total-mass exponent is $2\cdot k\cdot (\mathrm{bf}+(D+1).\operatorname{size})$ and the outer degree is at most
$2\cdot k\cdot D$. Hence one source-derived bound works for every ternary query, without
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
$\exists \delta >0, \forall \beta , 0<\beta <\delta \to \exists a$, with `a` a real root realizing all requested signs.
The guarded language also requires that symbolic nonvanishing, and belongs to
PSPACE on every input. The unguarded language belongs to PSPACE when all symbolic
root inputs are nonzero. Thus the polynomially bounded finite-family
small-parameter root-sign stage has a complete space certificate. Canny's stronger
implicit family bounds and critical-point construction remain separate obligations.

`ScaledSignQueries` starts the algebraic-root counting stage. At each sign value
$t\in \{-1,0,1\}$, the integer quadratics $2-2\cdot t^{2}$, `t²-t`, and $t^{2}+t$ are twice the
indicators of zero, negative, and positive respectively. Expanding a product of
these indicators proves that an integer combination of ternary product Tarski
queries equals $2^k$ times the number of distinct real roots realizing the
requested sign pattern. For a nonzero root polynomial, strict positivity is
equivalent to an actual realizing real root. Repeated roots are counted once;
zero query values and an empty query family are included. The zero root polynomial
uses Mathlib's empty root multiset and is excluded from the realization theorem.

`SignQueryProductSpace.queryProductEvaluator` computes a selected modular
coefficient of $\prod Q_{i}^{e_{i}}$, $e_{i}\in \{0,1,2\}$, through the existing suspended product
machine. Two factor slots per polynomial suffice, with unit padding. Binary
count/exponent/modulus/degree fields are FP, and source coefficient routines may
use polynomial space. Empty products and modulus one are covered. Coefficient
maps commute with the query polynomial at fixed exponents, including modular
degree drops.

`SignQueryBits.evaluator` now combines that modular product reader with the
original-source Tarski evaluator. Its only arithmetic children read coefficients
of the root and indexed original polynomials. FP readers give the number of
polynomials, ternary exponents, and original degree/mass allowances. Product
query degree and mass budgets are derived internally as $2\cdot k\cdot D$ and $2\cdot k\cdot B$.
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

`SignQueryBounds` proves query degree at most $2\cdot k\cdot D$ and integer coefficient
magnitude-bit length at most $2\cdot k\cdot (b+(D+1).\operatorname{size})+1$ for input degree allowance `D`
and coefficient magnitude allowance $2^b$. A Tarski query lies between minus and
plus the root degree. The scaled count has at most $k+\mathrm{rootDegree}.\operatorname{size}+1$ magnitude
bits. `SignQueryBudget` gives FP binary writers and semantic budget theorems from
count and degree words, without unary expansion of their values.

The ternary moment formulation also appears in TauCeti's
[polynomial sign-sum identities](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/RealAlgebraic/SignDetermination/Polynomial.lean)
and [adapted matrices](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/RealAlgebraic/SignDetermination/Adapted.lean).
The complete direct expansion now has a space certificate. `Ternary.count` and
`Ternary.digit` compute binary $3^k$ and its query digits with FP modular
exponentiation using a modulus of $2\cdot k+1$ bits. The proof matches the enumeration
to Mathlib's equivalence between `Fin k → Fin 3` and `Fin (3^k)`, including $k=0$.
A unary FP certificate for `k` ensures polynomial output length; the binary
count writer alone would not provide this bound.

`SignPatternBits.weightEvaluator` selects the signed factors in the indicator
expansion and multiplies them with a complete suspended-call certificate. Each
factor has magnitude at most two, so every prefix product has at most order `k`
bits. `summandEvaluator` multiplies this weight by the original-source product
Tarski query. `evaluator` sums all $3^k$ terms and proves exact agreement with
`scaledRootCount`. `rootCountEvaluator` then uses FP division by $2^k$ to return
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
argument. Those obligations and $\mathrm{ETR} \in \mathrm{PSPACE}$ remain open.

## Symmetric recovery degeneracy and bounded asymmetric coordinates

The report's equations (13)--(15) do not always give the asserted linear GCD.
`SymmetricRecoveryDegeneracy` verifies the finite affine system $x^{3}-x=0, y=0$:
its solutions are $(-1,0),(0,0),(1,0)$, and homogenization has no nonzero solution
at infinity. For direction $(c_0,c_1)$, its nodal eliminant is
$q(X)=X(X-c_0)(X+c_0)$, separable when $c_0\ne0$. Shifting $c_1$ by either sign of
one leaves $q$ unchanged. At the middle projected root zero, reflection gives
$q(-X)=-q(X)$, so the recovery GCD has degree three. The corresponding midpoint
triple makes condition (14) an identity in the direction coefficients. Thus the
claim on page 7 that these bad conditions become nonzero polynomials under
$c_i=\beta^i$ needs an additional argument or a different construction. This identifies
a gap in the fixed symmetric construction, not a counterexample to the PSPACE
upper bound or the existence statement of Lemma 2.2. Previously proved
univariate recovery theorems retain their explicit separating-pair hypotheses.

The obstruction is preserved by every linear projection: if the three points
are $A,B,C$ with $A+C=2B$, then $L(A)+L(C)=2L(B)$. Since their second coordinates
are equal, the symmetric coordinate shifts do not break this midpoint relation.
Thus even a separating projection, or an infinitesimal choice of its coefficients,
cannot make the required GCD linear in this example. Canny already identifies
spurious roots; the gap is the assertion that suitable coefficient choices always
avoid them. See the [report](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/Archive/CSD-88-439.pdf),
printed pages 6--7, equations (13)--(16).

A relevant later source is Angelos Mantzaflaris, Éric Schost, and Elias Tsigaridas,
[*Sparse Rational Univariate Representation*, ISSAC 2017, pp. 301--308](https://doi.org/10.1145/3087604.3087653)
([author-hosted manuscript](https://cs.uwaterloo.ca/~eschost/publications/srur.pdf)).
Section 2.2, equation (16), explicitly assumes
$2\zeta_\ell=(\zeta_m+\alpha_{m,k})+(\zeta_\nu-\alpha_{\nu,k})$
only when $\ell=m=\nu$. The three-point example violates precisely this
no-spurious-pairs condition for every linear separating projection. The paper
also allows nonlinear separating polynomials and discusses coefficient choices
in Section 2.3. Its equations (7)--(8) give an alternative derivative-based
coordinate formula, using a parameterized square-free eliminant and the derivative
of the univariate eliminant as denominator. That derivative-based alternative is
not formalized here. These passages do not explicitly correct Canny's argument.
A targeted literature search on 2026-10-21 found neither this exact
counterexample nor an explicit correction of the linear-choice justification;
this negative search result does not establish novelty.

`VectorSeparation.exists_bounded_pair_encoding` chooses a positive integer
$k\le N^4+1$ for which $(a,b)\mapsto a+kb$ is injective on all ordered pairs of a
finite $N$-point set $S$. Each collision of distinct pairs with unequal second
components excludes at most one scalar; equal second components cannot collide.
There are at most $N^4$ excluded slopes, and excluding zero makes $k$ positive.

`AffineGridAvoidance` bounds a common integer nonzero evaluation of $m$ nonzero
affine forms by $0,\ldots,m$. Its family separation theorem allows different affine
offsets on each vector. `AsymmetricProjection.exists_bounded_direction` applies
this to the encoded vector pairs: for every coordinate $j$, the affine scalar
$L(a+kb)+k(a_j-b_j)$ must distinguish all pairs. One further family with zero
offsets ensures that $L$ itself is injective on $S$. One common integer direction
works, with every coefficient at most $(n+1)N^4$. No condition is assumed to
remain nonzero when it is identically zero; the vector-pair encoding proves
nonzeroness before the grid theorem is applied.

`AsymmetricCoordinateRecovery` forms nodal polynomials with roots
$L(a)+ka_j$ and $L(b)-b_j$. They are separable, and their Cartesian root pairs
are separated by $(A,B)\mapsto A+kB$. At a point $x$, the distinguished pair maps to
$(k+1)L(x)$. The existing `coordinate_recovery_spec`, including its linear-input
branches, therefore gives a nonzero $D$ and $x_j=L(x)+N/D$. Composing $N$ and $D$
with $(k+1)X$ gives `rationalNumerator` and `rationalDenominator` in the original
parameter $L(x)$, with denominator degree at most $\max\{1,(N-1)N\}$ and numerator degree at
most one more. `exists_bounded_rational_coordinates` assembles the bounded choices,
a separable projection eliminant, and simultaneous exact coordinate recovery.

`GaloisFixedPolynomial` applies the infinite Galois fixed-field theorem, removing
the finite-dimensional hypothesis from coefficient descent. `VectorGaloisDescent`
supplies the base-field coefficient step for vectors in any Galois extension $L/K$.
An automorphism permuting $S$ fixes every nodal
polynomial whose node map commutes with the automorphism. This product argument
retains multiplicities and does not require injective nodes. Original and
asymmetrically shifted integer projections commute with every $K$-automorphism,
so their nodal polynomials descend to $K$. `stable_of_zero_set` proves the stability
hypothesis for a full finite zero set of multivariate equations over $K$.

`AsymmetricBaseCoordinates.exists_bounded_coordinates` combines this descent with
the bounded asymmetric choice and the existing recovery theorem over $K$ with
roots in $L$. It returns a monic separable degree-$N$ polynomial over $K$ with exactly
the projected points as roots in $L$, plus numerator and denominator polynomials
over $K$ for every coordinate. The same degree bounds and nonzero-denominator
specifications hold simultaneously, including empty sets and linear inputs.
The ambient Galois extension and stable finite point set are hypotheses of this
finite-set theorem; the full-zero-set application below supplies them directly
in an algebraic closure.

These are finite-set algebraic theorems over a characteristic-zero field.
The nodal products use the supplied point set; they are not yet constructed from
encoded multivariate equations, and no descent to integer coefficients or
multivariate eliminant coefficient routine is supplied by these modules.
The remaining effective multivariate construction, its complexity bounds, and
$\mathrm{ETR} \in \mathrm{PSPACE}$ remain open.

The asymmetric construction therefore repairs the finite-set recovery step,
including denominator nonvanishing and bounded choices of weight and direction.
The existence results below extend it to full finite polynomial zero sets and
integer representations. Constructing the representation from encoded equations
with the required coefficient readers and polynomial-space bound remains a
separate obligation.

## Rational representations of full finite zero sets

`FiniteSystemCoordinates.zeroSet` evaluates a family of multivariate equations
over K in an extension L. Its `Representation` records an integer direction,
a monic separable eliminant of degree equal to the full solution count N, and
numerator/denominator polynomials over K for every coordinate. Direction
coefficients are at most $(n+1)\cdot N^{4}$; denominator degrees are at most
$\max\{1,(N-1)N\}$ and numerator degrees at most one more. Denominators do not
vanish on solutions, and the eliminant has exactly the projected solutions as
roots in L. `Representation.rootEquiv` is an actual bijection between eliminant
roots and system solutions, obtained by the rational decoding formulas.

`nonempty_representation` proves existence for any full finite zero set in a
characteristic-zero Galois extension. Stability follows from the equations.
`nonempty_algebraicClosure_representation` specializes this to the algebraic
closure of K, whose Galois structure follows from characteristic zero. Neither
a finite ambient extension nor a separately supplied stability proof is needed.
This is an algebraic existence result under a full-zero-set finiteness hypothesis;
it does not compute the zero set or construct the polynomials from encoded inputs.

`ProjectionSystemCoordinates.equations` instantiates the system with a surface
polynomial, its normalized projection equations, and a reciprocal for the base
partial derivative. `exists_representation` uses the existing exceptional
polynomial and integer-grid avoidance to choose a direction whose full extended
fiber is finite over the algebraic closure. Evaluation commutes with the base-field
embedding, so the direction and all equations still have coefficients over K.
The finite-system representation then applies. `exists_family_representations`
uses simultaneous avoidance to give one integer direction for every surface in
a finite family. `decode_regular_point` proves that each eliminant root decodes
to a point on the original surface, satisfying all normalized projection equations
with nonzero base partial after the reciprocal coordinate is discarded.

This connects the qualitative critical-fiber and rational-coordinate results.
The direction grid still depends on the degree of an existential exceptional
polynomial; an input-size bound on that degree, a bound on the number of critical
points, multivariate eliminant coefficient algorithms, and their space bounds
remain open. $\mathrm{ETR} \in \mathrm{PSPACE}$ is not proved.

## Sound rational decoding across extension fields

`RationalRepresentationTransfer` evaluates the same base-field numerator and
denominator polynomials in any target extension E. For a representation over
an algebraic closure L of K, `Representation.decodeOver_sound` proves that every
E-valued eliminant root decodes to a full solution over E, has no zero coordinate
denominator, and equals the integer projection of the decoded point. Different
parameter roots decode to different solutions.

The proof embeds E into its algebraic closure and embeds L into that same field.
Because the eliminant splits in L, every root in the common extension lifts from
an L-valued root. Polynomial evaluation, rational decoding, and the original
multivariate equations commute with the field embeddings. Injectivity of the
embedding of E transfers the solution and nonvanishing statements back to E.
The target extension need not be algebraic or Galois over K.

`ProjectionCoordinateTransfer.decodeOver_regular_point` applies this to the actual
extended projection equations and discards the reciprocal variable. Thus, for
example, a representation over the algebraic closure of the rationals decodes
at any real eliminant root to a real point of the original surface satisfying
all normalized projection equations with nonzero base partial.
`complete_at_algebraic_solution` proves the converse
for any target solution whose coordinates are algebraic over K. It restricts to
the intermediate field generated by those coordinates, embeds that algebraic
field into L, and transfers the source decoding identity back. For an algebraic
target extension, `rootEquivOver` gives a bijection with the full target zero set,
without a Galois hypothesis on that target.

`parameter_of_algebraic_regular_point` extends a regular critical point by the
reciprocal of its base partial. Algebraicity of the original coordinates implies
algebraicity of the reciprocal, so the point is recovered at an eliminant root
in the same target field. In particular this covers real algebraic critical
points for rational inputs. The retained annihilator certificates below now
prove algebraicity of every target solution for certified selected directions.
The coefficient algorithms and bounds and the final PSPACE composition remain
open; the algebraic-closure bijection alone does not establish them.

## Complete real-field critical representations from annihilator certificates

`CoordinateAnnihilatorSpecialization.Certificate` retains the cleared coordinate
polynomials Qᵢ, nonzero parameter factors sᵢ, and identities
$C(s_{i})\cdot Q_{i}(X_{i}) \in \operatorname{radical}(I)$ from the existing finite-fiber proof. Their product
$d=\prod _{i} s_{i}\cdot \operatorname{leadingCoeff}(Q_{i})$ is nonzero. At any specialization φ into a field K
with $\varphi (d)\ne 0$, each `Qᵢ.map φ` is a nonzero polynomial over K. Every solution in
every extension E/K is annihilated coordinatewise by those same K-polynomials.
Thus all coordinates are algebraic over K, even when E itself is not algebraic.
The certificate also supplies finiteness in every such target field.

`ProjectionFiniteSpecialization.generic_quotient_coordinates_algebraic` extracts
the generic-coordinate step previously internal to finite-fiber specialization.
`ProjectionAnnihilatorDirections` uses it to construct certificates for the
actual normalized critical equations with reciprocal base partial. A certified
integer direction records both its certificate and nonvanishing specialization.
The common integer-grid argument gives one direction certified simultaneously
for a finite surface family. The grid bound remains the total degree of
existential certificate polynomials, with no input-size estimate.

`CompleteProjectionCoordinates` combines these certificates with rational
representations over the algebraic closure. `CertifiedDirection.rootEquivOver`
is a bijection between eliminant roots and full extended-system solutions over
any target extension E/K, requiring neither algebraicity nor a Galois structure
of E. The reciprocal coordinate is uniquely determined by the nonzero base
partial. Removing it gives `regularRootEquiv`, a bijection with regular critical
points of the original hypersurface in that same field. This applies to real
solutions over rational inputs without an extra algebraicity assumption.

`exists_regularPoint_iff` transfers any predicate on those critical points to
their rationally decoded univariate parameter roots. For example, it applies to
additional polynomial inequalities used to retain positive-inactive samples.
One common integer direction admits these complete representations for every
surface in a finite family. This proves the semantic coordinate step, not an
encoded coefficient algorithm. Bounds on the exceptional polynomial, critical
point count and coefficient sizes, the multivariate eliminant computation,
and the full $\mathrm{ETR} \in \mathrm{PSPACE}$ proof remain open.

## Integer coefficient data for critical representations

`IntegerCoordinatePolynomials` clears rational coefficient denominators using
Mathlib's localization normalization. Each coordinate numerator and denominator
receives the same nonzero integer scale: separately normalize them and multiply
each result by the other's scale. The parameter eliminant receives its own
nonzero integer scale. `IntegerData` records the exact polynomial-map identities
over the rationals, rather than assuming the quotients are unchanged.

Every resulting polynomial has exactly its original degree. The integer
eliminant remains separable after mapping to the rational coefficient field;
separability over the integer ring itself is not asserted. In any rational
extension field, including the reals, eliminant roots are unchanged, integer
coordinate ratios equal the original rational ratios, and denominator
nonvanishing is equivalent. These statements also cover a zero numerator.

`IntegerProjectionCoordinates` combines this conversion with certified critical
representations. `integerRegularRootEquiv` gives the full target-field bijection
with regular critical points. `exists_regularPoint_iff_integer` transfers any
additional predicate to decoded roots using only integer univariate polynomials
for the eliminant and coordinate data. One common integer direction gives these
representations for a finite family of rational input surfaces.

This reaches the coefficient type used by the existing integer-polynomial sign
and substitution interfaces. The localization normalization is an existence
construction. The explicit alternative below now supplies bounds and coefficient
access from rational source contracts. Effective multivariate construction and
derivation of those source contracts from the original input remain open, as
does $\mathrm{ETR} \in \mathrm{PSPACE}$.

## Constructive normalization bounds and streamed coefficient signs

`FiniteDenominatorClearing` replaces a chosen localization multiple with the
product M of the canonical positive denominators of a finite rational family.
Its cleared value at i is the integer numerator at i times the product of all
other denominators. The value is exactly $M\cdot q_{i}$ over the rationals. If every
numerator magnitude and denominator has at most B bits and the family has N
entries, M and every cleared value have at most $B\cdot N+1$ bits.

`RationalPolynomialClearing` enumerates all coefficients through a common degree
cap D in a finite polynomial family, including high zero coefficients. Their
denominators are one. `Polynomial.ofFn` builds the explicit integer polynomials;
the common scalar identity proves equality after mapping to the rational field,
and injectivity preserves the original degrees. `BoundedIntegerCoordinates`
applies this to the eliminant and all coordinate pairs at once. For n coordinates
there are $(2\cdot n+1)\cdot (D+1)$ entries, yielding the coefficient and scale budget
$B\cdot ((2\cdot n+1)\cdot (D+1))+1$. The resulting `IntegerData` uses this specified positive
scale and retains the existing root, decoding, and nonvanishing theorems.

`DenominatorClearingSpace.Access.evaluator` computes one normalized integer value
modulo a binary positive modulus. A suspended denominator evaluator supplies
one factor at a time, with the selected factor replaced by one; the modular
product is then multiplied by the selected numerator residue. Thus the modulus
may divide any denominator: no modular inverse or integer quotient is required.
The product, factor branching and final multiplication have separate correctness
proofs. All saved inputs, child computations and clocks are included through
the existing modular-product and space-function composition interfaces.

`DenominatorClearingSign.SourceAccess` supplies an original query context,
canonical numerator/denominator residue routines, and FP binary count, selected
index and component-bit-bound writers. Its FP budget writer computes $B\cdot N+1$.
The uniform positive-modulus packet protocol connects the complete modular
product evaluator to indexed CRT sign recovery and the small-modulus zero scan.
The cleared coefficient's three-way sign has a space-function evaluator;
zero, negative and positive languages belong to Complexitylib2's PSPACE.
The count, bit bound and normalized integer may be exponentially large; the
routines do not store the full scale, normalized integer or coefficient array.

These results certify the normalization stage under explicit rational-source
contracts. They do not yet construct canonical rational component residues,
degree bounds or bit bounds for the multivariate critical eliminants. Those
source algorithms and quantitative estimates, and the final PSPACE composition,
remain open.

## Compactification before critical points

The report's §3.1 starts by substituting $x_i = y_i/(1-y_i^{2})$ and bounding the
new coordinates inside the unit cube. The local route uses the existing
all-input equation compiler first. The remaining strict constraints are then
the cube bounds, while the compiled polynomial equation defines a closed set.

`Geometry.CubeCoordinates` supplies the explicit inverse
$2\cdot x/(1+\mathrm{sqrt}(1+4\cdot x^{2}))$, proves it lies strictly between -1 and 1, and proves the
coordinatewise map is onto. Every finite open-cube point has a common positive
margin; the resulting closed inner cubes are compact and nested as the margin
decreases.

`Geometry.CubePolynomial.cleared` is an integer multivariate polynomial, formed
by clearing each coordinate denominator to exponent $2\cdot \operatorname{degreeOf}_i(p)$.
Its real evaluation is a positive factor times the original polynomial evaluated
at the rational coordinates. Thus zeros and signs agree on the open cube. Its
total degree is at most $4\cdot \sum_i \operatorname{degreeOf}_i(p)$, hence at most
$4\cdot n\cdot \mathrm{totalDegree}(p)$. Intersecting its zero set with an inner cube is compact.
Existence of an original real zero is equivalent to nonemptiness for some positive
margin, and smaller margins preserve nonemptiness. Linear projections attain
maxima on these compact nonempty sets.

`ETR.FinitePolynomial` translates a term to a polynomial on its actual finite
variable block, preserving evaluation under extension by zero. Its compactified
degree is at most $4\cdot \mathrm{arity}\cdot \mathrm{degreeBound}$, hence at most $4\cdot \mathrm{dataSize}^{2}$.
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

`PolynomialPerturbation` represents the compactified equation $q=0$ by $q\ge 0$
and $-q\ge 0$, together with two inner-cube inequalities per coordinate. Each
constraint has an independent additive shift `a_i`, with
$\sum_i a_i^{2} = \delta ^{2}$. A feasible original point gives a perturbed point at every
nonnegative radius by placing a nonnegative shift in one inequality. Conversely,
arbitrarily small feasible perturbations bound the spatial points in $[-2,2]^n$
and give uniform small violations; compact approximation recovers an unperturbed
point. This proves the nonemptiness equivalence used in Lemma 3.2 for the compiled
equation route, including zero-variable inputs. Fixed-radius perturbed sets are
closed and lie in an explicitly bounded product of cubes, hence are compact.

`PerturbationPolynomials` realizes the constraints as integer multivariate
polynomials with separate ε, δ, spatial, and shift variables. For `n` spatial
variables there are $2+2\cdot n$ inequalities and $4+3\cdot n$ total variables including
the two parameters. Inequality degrees are at most $\operatorname{max}(\operatorname{degree}(q),1)$ and the
radius equation has degree at most two. `ETR.PerturbedSource.correct` instantiates
the construction for every encoded ETR input:
$\mathrm{ETR}(\mathrm{bits}) \iff \exists \varepsilon >0, \exists d>0, \forall \delta , 0<\delta <d \to \mathrm{Nonempty}(T(\mathrm{bits},\varepsilon ,\delta ))$.
The equivalent arbitrarily-small-radius statement is also proved. Dimension,
inequality-count, and degree upper bounds have FP binary writers. Compactness
gives extrema for every continuous objective on each nonempty perturbed set.

`AdditiveSubmersion` proves that $(x,a) \mapsto f(x)+a$ has derivative
$(h,b) \mapsto Df(x)h+b$, which is onto via $b \mapsto (0,b)$. Polynomial evaluation and
the actual equation/cube constraint maps are smooth, so the result applies to
the full parameterized ETR family.

## Radius slices and critical values

`RadiusLinearization` computes the derivative of
$((x,a),\delta ) \mapsto (f(x)+a, r(a)-\delta ^{2})$. Its final coordinate includes $-2\cdot \delta \cdot d\delta$, so
an explicit preimage proves surjectivity whenever $\delta \ne 0$. At fixed radius the
derivative is $(h,b) \mapsto (Df(x)h+b, Dr(a)b)$; it is onto exactly when
$Dr(a) \circ Df(x)$ is nonzero. `SquaredRadius` specializes these formulas to
$r(a)=\sum_i a_i^{2}$, with $Dr(a)b=2\cdot \sum_i a_i\cdot b_i$, and applies the joint result
to the actual equation/cube family.

`ActiveRadiusLinearization` handles an arbitrary active constraint set S. The
augmented fixed-radius derivative, retaining only the S coordinates and the
radius equation, is onto exactly when either some inactive shift `a_j` is
nonzero or $Dr(a) \circ Df(x)$ is nonzero. The proof supplies explicit derivative
preimages, including an inactive coordinate direction when available.

`ActiveRadiusCritical` uses this criterion at a point with $f_i(x)+a_i=0$ for
every active i. A nonsurjective derivative forces all inactive shifts to vanish.
Its weighted spatial derivative is then the negative derivative of
$g_S(x)=\sum_{i\in S} f_i(x)^{2}$. The sphere equation gives $g_S(x)=\delta ^{2}$ and the
derivative of `g_S` is zero. Thus every radius failing this active-set
submersion test yields a critical value of a concrete sum-of-squares function.

`CriticalEnergyPolynomial` realizes `g_S` using the existing integer constraint
polynomials after subtracting their shift variables. Its evaluation is independent
of those shifts and of δ, and its total degree is at most
$2\cdot \operatorname{max}(\operatorname{degree}(q),1)$ for the compactified equation q. `ETR.RadiusSource` proves
the joint and active-set statements for every encoded source and supplies an FP
binary degree allowance $8\cdot \mathrm{sourceSize}^{2}+4$ for the energy polynomial.

`PolynomialCalculus` proves the analytic derivative formula for evaluation of a
multivariate polynomial over any coefficient semiring with a homomorphism to ℝ.
The derivative is the sum of evaluated formal partial derivatives times coordinate
projections. Its vanishing is equivalent to the vanishing of every formal partial,
including in zero spatial dimensions. `SpatialPolynomialCalculus` differentiates
the parameter assignment explicitly, so specializing ε, δ, and shifts retains only
the spatial partials.

`RadiusCriticalEquations` consequently gives an integer polynomial system
$g_S-\delta ^{2}=0$, $\partial g_S/\partial y_i=0$, whose zeros are exactly the critical points with value
δ². Every singular active point supplies a zero with the shift coordinates set
to zero. `PartialDerivativeDegree` proves the degree bound $\operatorname{degree}(p)-1$ for
formal partial derivatives. All equations have degree at most
$2\cdot \operatorname{max}(\operatorname{degree}(q),1)$. `ETR.RadiusCriticalSource` instantiates the system on every
encoded input, with FP count allowance $\mathrm{sourceSize}+1$ and degree allowance
$8\cdot \mathrm{sourceSize}^{2}+4$. These are size-bound writers, not yet coefficient-access
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
$0<\delta <d$. `ETR.RegularRadiusSource.correct` combines this interval with the compact
perturbation correctness theorem on every encoded input. Effective radius
selection, streamed coefficient access, and effective critical-point sampling remain open.

## Critical projection maxima

`ActiveExtremum.isLocalMaxOn_fiber` proves that inactive inequalities remain
positive near a feasible maximum. Fixing the active constraint values and the
radius equation therefore gives a fiber on which the objective is locally
maximal. Its multiplier theorem uses Mathlib's Lagrange theorem and surjectivity
of the equality derivative to exclude a zero objective multiplier. Normalization
gives $L(h)=\Lambda (DF(h))$ for a linear functional Λ on the constraint codomain.

`PerturbedCriticalPoint` proves smoothness of the actual active augmented maps,
selects exactly the constraints vanishing at the maximum, and obtains normalized
multipliers at a maximum of any continuous linear projection on a nonempty
compact regular perturbation. `ETR.CriticalPointSource.correct` applies this to
every encoded input: satisfiability is equivalent to the existence of these
critical maxima for every projection throughout a small regular-radius interval.

`ProjectionEquations` constructs the hypersurface system $p=0$ and
$\partial_i(p)-v_i\cdot \partial_{\mathrm{base}}(p)=0$ for $i\ne \mathrm{base}$. Point and direction variables
are separate blocks; the direction is a parameter in the sampling problem.
There are exactly n equations for n point coordinates. Their total degree,
including the direction block, is at most $\operatorname{max}(\operatorname{degree}(p),1)$. The coefficient
ring is arbitrary, and integer coefficients remain integer coefficients.
`ProjectionCritical` proves that a local projection maximum on a regular
hypersurface satisfies this system when $v_{\mathrm{base}}=1$. Its coefficient homomorphism
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
$2\cdot \operatorname{max}(\operatorname{degree}(q),2)$ for both tube and projection systems. This counts parameter
and direction variables, not just the outer point variables.

`ETR.TubeSource` instantiates the symbolic and ordinary integer systems on every
encoded input. For normalized source size N it supplies FP equation-count
allowance $2+3\cdot N$, point/direction-variable allowance $4+6\cdot N$, expanded-variable
allowance $7+6\cdot N$, and full degree allowance $8\cdot N^{2}+4$. Its common regular α
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
delta: scale the shift vector by $1+t$. Its squared radius strictly increases
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
shift norm is at most $\mathrm{delta}^{2}+1$ and each shift has magnitude at most $\mathrm{delta}+1$.
Each active constraint has square at most alpha; inactive constraints are
nonnegative. Thus every constraint is at least -1. The cube constraints give
spatial coordinate bounds $[-(\mathrm{delta}+3),\mathrm{delta}+3]$ when epsilon and delta are
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

$D(a,x)-D(a,p) = 2\cdot (p-a)\cdot (x-p)+D(p,x)$, where $D(a,x)=\sum _{i}(x_{i}-a_{i})^{2}$,

shows that $(p-a)\cdot x < (p-a)\cdot p$ for every other point x in the set. The designated
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
projection equations and adds $t\cdot \partial_{\mathrm{base}}(p)-1=0$. At every solution in a
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
to every encoded ETR input. Effective tube projection direction search, root enumeration,
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
degrees. In characteristic zero, coordinates in $0,\ldots,B$ suffice whenever B
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
by $2^N$, for encoded term size N. `CubePolynomialMass` bounds each denominator
factor `1-X_i²` by two in coefficient mass. The total exponent in denominator
clearing is at most twice the sum of the source's coordinate degrees. The
compactified source consequently has mass at most $2^{N+2\cdot N^{2}}$.

`TubeCoefficientMass` bounds the flattened radius mass by $c+1$ and every
flattened constraint mass by $H+4$, for c constraints and source mass H. The
integer tube mass is at most $(c+1)^{2}+c\cdot (H+4)^{2}+1$, uniformly over active sets.
Formal partial derivatives and the additional direction variable bound each
flattened projection row by $(4\cdot \operatorname{max}(\operatorname{degree}(p),2)+1)$ times this allowance.
All parameter and direction variables are included.

`ETR.TubeCoefficientBounds` combines these estimates with the existing source
arity and degree bounds. Both integer tube and projection polynomials have
mass at most $2^{20\cdot N^{2}+6\cdot N+21}$; each coefficient has at most
$20\cdot N^{2}+6\cdot N+22$ magnitude bits. The budget has an FP writer from the normalized
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
language belongs to Complexitylib2's PSPACE. `CollectedCoefficientZero` scans
the small moduli justified by the same budget, using the full residue routine
as a child; the coefficient-zero language also belongs to PSPACE. This supplies
the zero test needed for detecting actual degrees after cancellation.

`SourceCoefficientSpace` supplies the compiled ETR source fields and proves
query correctness for every binary source input. Its finite polynomial uses N
variables; the unused variables contribute no nonconstant monomials. Every
nonzero coefficient has coordinate exponents at most the source degree and
therefore an exponent query of exactly $N\cdot (N+1)$ bits. This is collected access
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
$X^e\cdot (1-X^{2})^s$: it is zero unless $e \le k$ and `k-e` is even, and otherwise is
$\binom{s}{(k-e)/2} \cdot (-1)^{(k-e)/2}$.

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
$4\cdot N^{2}+1$. `CompactCoefficientSpace` streams the coordinate product and then
the indexed source-term sum. Its certificate includes the saved inputs,
accumulators, child states, and clocks at both loop levels.

The generic routine accesses `cleared (Term.finitePolynomial N t)` with
`N` the validated source length. `CompactCoefficientPadding` proves that
zero-padding the exponent query preserves coefficients in the original arity:
extra variables have source degree zero and contribute a factor of one.
`CompactSourceCoefficient` supplies the compiled ETR input fields and proves
exact query correctness for `CompactSource.polynomial`. The exponent query
has length $N\cdot (4\cdot N^{2}+1)$; the proved compactification degree bound ensures every
nonzero coefficient is representable. Malformed source strings retain the
compiler's existing default semantics.

`CompactCoefficientSign` proves a coefficient mass bound of $2^{N+2\cdot N^{2}}$
for the padded compactification, hence a magnitude-bit budget of
$N+2\cdot N^{2}+1$ with an FP writer. The full residue evaluator instantiates CRT
sign recovery, proving coefficient negativity in Complexitylib2's PSPACE.
`CompactCoefficientZero` scans the small moduli justified by the same budget
and proves coefficient zero testing in PSPACE. Both routines include the
actual-degree and binomial children; they assume no coefficient oracle.
`CubePolynomialMultiplication` proves that clearing fixed coordinate
allowances respects products whose exponents fit those allowances. Actual
coordinate degrees of nonzero integer products add; handling zero factors
separately therefore proves $\mathrm{cleared} (p\cdot q) = \mathrm{cleared} p \cdot \mathrm{cleared} q$ and
$\mathrm{cleared} (p^k) = (\mathrm{cleared} p)^k$.

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
order. Its active-set bitmask has exactly $2+2\cdot n$ bits and a proved round trip.

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
$4\cdot M^{2}$, with an FP bound and query-width writer. `TubeDenseQuery` checks both
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
representable with at most $(6\cdot N+7)\cdot (8\cdot N^{2}+5)$ exponent bits. All positive moduli,
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
W equal to the binary size of $8\cdot N^{2}+4$. All source metadata has FP writers.
`TubeIndexedSpace` connects arbitrary binary ranks to the complete native residue
machines, with FP source, active-mask, row, and modulus fields. The mathematical
term family is never materialized. `TubeIndexedBounds` retains the actual source
coefficient mass bound for every rank and supplies an FP even denominator-power
allowance $2^W$, bounded by twice the full degree allowance. These establish the
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

## Full three-parameter tube deformation coefficients

The homogeneous cleared regular rows and the projection equation form the full
bivariate tube system. Parameter-coordinate readers and bounds, plus FP encoded
integer direction access, supply every row coefficient internally. The padded
Macaulay determinant has complete modular and integer-sign evaluators with all
suspended reader costs included.

The undeformed determinant can vanish identically. `TubeDeformationSystem`
therefore retains an independent deformation variable: its determinant is
nonzero, equals one at deformation one, and specializes to the original
candidate at zero. The first bounded encoding combines perturbation and
projection exponents while preserving deformation. `TubeDeformationBudget`
proves FP degree and integer magnitude-bit allowances for every resulting
three-parameter coefficient.

`PolynomialAffineEntrySpace` reads a deformed entry through one original
polynomial entry query. Quotient zero selects the original coefficient;
quotient one selects the corresponding identity coefficient minus that
coefficient; every other quotient returns zero. `BerkowitzAffinePolynomialSpace`
uses a second bounded encoding to evaluate a selected determinant coefficient,
including the original entry child's complete workspace and clock bounds.

`TubeDeformationModular`, `TubeDeformationCoefficientMap`, and
`TubeDeformationSpace` instantiate this backend with the actual full tube
matrix. Coefficient reduction commutes with encoding and deformation. The
inner-exponent guards prevent aliasing in both encodings. No deformed row,
matrix-entry, determinant, or sign callback is assumed.

`TubeDeformationResidue` varies the modulus without changing the original
integer coefficient or any of its three selected exponents.
`TubeDeformationSign` combines that complete evaluator with the proved budget
and streamed CRT routines. Selected coefficient zero, negativity, and positivity
are in Complexitylib2's PSPACE under the original reader contracts.

These results do not yet identify an eliminant coefficient or factor. That
identification, concrete sampler coordinate readers, quantitative bounds, and
effective parameter selection remain necessary for the ETR decision algorithm.

## Lowest deformation coefficient and effective nonvanishing

The [GCP report](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/Archive/CSD-88-440.pdf),
pages 4 and 6, distinguishes the padded determinant from the resultant quotient
and proves persistence on proper components for the lowest resultant coefficient.
This distinction remains a formalization obligation: the current padded
determinant candidate is not yet identified with that quotient or its factors.

`DeformationLowestCoefficient` proves the limit step independently of root
persistence. Factor out the lowest deformation power. At nonzero deformation
values the remaining factor still vanishes; continuity then forces its constant
coefficient to vanish at the limiting coefficient parameters. The theorem works
for Hausdorff topological fields and continuous coefficient evaluations.

`TubeDeformationLowest` applies that theorem to the actual full tube system.
Its lowest deformation coefficient is nonzero and obeys the uniform inner-degree
bound. If coefficient parameters converge, deformation tends to zero through
nonzero values, and the deformed homogeneous rows have nonzero common roots,
then the limiting parameters annihilate the candidate. No convergence assumption
on the spatial coordinates is required. Existence of the necessary root families
for original isolated solutions is not assumed to follow from this theorem.

A coefficient specialization always leaves the deformation determinant nonzero,
since evaluation at deformation one remains one. Vanishing of the lowest
coefficient is therefore equivalent to a strict increase in deformation order.
If its image is nonzero, both the lowest order and coefficient commute with the
specialization, without requiring the coefficient map to be injective.

`TubeDeformationSpecialization` makes nonvanishing effective for the original
perturbation variable. Write `M` for the padded dimension, `E` for the cleared
row coefficient degree allowance, and `K` for the proved full deformation
integer coefficient-bit budget. Every projection coefficient of the lowest
candidate has degree at most $M\cdot E$ and mass at most
$2^{K+(M\cdot E+1).\operatorname{size}}$. In particular its nonzero leading projection coefficient
cannot vanish for $0<\theta \le 2^{-s}$, where $s=K+(M\cdot E+1).\operatorname{size}+1$.
The exponent has an FP binary writer using the existing source, direction,
and coordinate-bound writers. Throughout this interval the projection polynomial
is nonzero, and extraction of the lowest deformation coefficient commutes with
perturbation specialization.

The lowest deformation index and coefficient reader are computed below.
Geometric root persistence, resultant-factor extraction, and the quantitative
conditions needed for tube sampling remain open.

## Computing the symbolic lowest deformation coefficient

`LowestCoefficientSpace` searches coefficient indices in increasing order using
certified space-bounded zero tests. The accumulator retains the first nonzero
index plus one, with zero as the unset marker. A final predecessor gives the
natural trailing degree, including the zero-polynomial convention. Its length
is bounded by the binary search-counter length. An FP binary degree allowance
therefore suffices for the full suspended fold certificate.

`TubeBivariateReindex` transports all original parameter-coordinate and direction
readers through FP context preparation and replaces selected degree fields.
`TubeDeformationCoefficientPolynomial` bounds each encoded coefficient
polynomial's degree by $M\cdot \mathrm{Eencoded}$ and proves exact zero preservation and scalar
quotient/remainder access. `TubeDeformationCoefficientZero` scans the corresponding
$M\cdot \mathrm{Eencoded}+1$ scalar coefficients, calling the complete integer zero evaluator.
Coefficients outside that allowance vanish. This gives whole deformation
coefficient-polynomial identity testing in PSPACE without materializing either
the original bivariate coefficient or its encoding.

`TubeDeformationLowestSpace` uses those identity tests and the proved deformation
degree bound `M` to compute the actual determinant's lowest nonzero deformation
index. Its specification includes minimality and the dimension bound. The result
is retained with the original context and passed to the complete coefficient
reader. Selected residues and three-way integer signs of the lowest bivariate
coefficient now have full space certificates. `TubeDeformationLowestLanguages`
proves selected coefficient zero, negativity, and positivity in PSPACE.
All saved search and identity-test states and original parameter-reader costs
are included. There is no additional supplied deformation index or row, entry,
determinant, or sign oracle.

The object computed is the lowest coefficient of the padded determinant
candidate. Identifying its relevant resultant factors and proving geometric
root persistence remain necessary for the eliminant and sampling algorithm.

## Affine deformation and the characteristic numerator

`PolynomialAffineReparametrization` homogenizes a polynomial to a certified
degree allowance and substitutes $(X,1-X)$. The resulting finite sum has terms
$p_i\cdot X^i\cdot (1-X)^{M-i}$. Coefficients below the original lowest order vanish;
at that order only the original lowest term contributes, with constant factor
one. Thus both the order and coefficient are preserved over every commutative
ring. `PolynomialSignedReflection` proves that replacing `X` by `-X` preserves
the order and multiplies its coefficient by the corresponding power of `-1`.

`AffineCharacteristic` proves that homogenization commutes with determinants
of matrices whose entries have degree at most one. Consequently
$F(\varepsilon )=\operatorname{det}(A+\varepsilon \cdot (I-A))$ is the homogeneous substitution of $P(s)=\operatorname{det}(A+sI)$.
For $Q(s)=\operatorname{det}(A-sI)$, the exact identities are
$Q(s)=(-1)^M\cdot \chi _A(s)$, $\operatorname{ord}(Q)=\operatorname{ord}(F)=k$, and
$\operatorname{trail}(Q)=(-1)^k\cdot \operatorname{trail}(F)$. No division or domain hypothesis is needed.

`MacaulayCharacteristic` and `TubeDeformationCharacteristic` apply these
identities to the actual padded full tube matrix. Its subtractive characteristic
numerator has a nonzero lowest coefficient, whose selected scalar coefficients
differ from the computed affine ones by exactly the lowest-order sign.
After every coefficient-ring specialization, vanishing of the two lowest
coefficients is equivalent.

`SignedTagSpace` supplies an FP parity correction of three-way integer signs.
`TubeDeformationCharacteristicSpace` pairs the complete lowest-index and sign
evaluators and applies that correction. Selected lowest characteristic-numerator
coefficient zero, negative, and positive tests are in PSPACE under the existing
reader contracts. The computation accounts for both child routines and assumes
no additional index or sign reader.

This removes the parameter-convention gap between the existing interpolation
and the characteristic numerator. The extraneous minor construction below
addresses the denominator. Its resultant quotient formula, geometric root
persistence, and effective sampling remain open.

## Extraneous Macaulay minor and its costed deformation

`MacaulayExtraneous` selects the active level monomials divisible by at least
two distinct designated coordinate powers: the eligible coordinate set has
cardinality greater than one. Inactive fixed-width padding indices are excluded.
The extraneous matrix is the actual principal submatrix on this finite set.
`PrincipalPadding` proves that replacing every omitted row by its identity row
preserves the principal determinant. Affine deformation commutes with this
padding, so the extraneous deformation evaluates to one at deformation parameter
one and is nonzero. Coefficient-ring maps commute with the construction.

`MacaulayExtraneousControl` recognizes this set in FP by counting eligible
coordinates through the existing fixed-width row reader. It does not enumerate
the principal subtype or assume an FP procedure for its cardinality.
`PolynomialPrincipalSpace` branches between the suspended original entry reader
and an identity coefficient. Its generic affine determinant evaluator includes
the original entry child's workspace.

`TubeExtraneousSystem`, `TubeExtraneousModular`, and `TubeExtraneousSpace`
instantiate this construction with the full tube matrix over `ℤ[θ][T][ε]`.
The shared parameter radix still recovers every selected coefficient; indices
outside its valid perturbation range give zero. Complete polynomial-space
residue evaluators use the existing coordinate readers and bounds without
new row, matrix-entry, or determinant readers.

`TubeExtraneousCharacteristic` uses the actual principal minor, rather than the
full padded matrix, for the subtractive characteristic denominator. Its lowest
order equals the extraneous affine deformation's lowest order, and its trailing
coefficient differs by $(-1)^{\mathrm{order}}$. These lowest coefficients vanish under
exactly the same coefficient-ring specializations. The characteristic lowest
coefficient is nonzero.

`PrincipalPolynomialBounds` proves that identity row padding preserves uniform
entry degree and coefficient-mass allowances. For an affine determinant over
integer polynomial entries, a second bounded radix encoding gives the scalar
coefficient bit bound $M.\operatorname{size}\cdot M + M\cdot (b+2) + 1$, where `M` is the padded dimension
and each original entry mass is at most $2^b$. `MacaulayExtraneousBounds` applies
this to the extraneous deformation. `TubeExtraneousBudget` reuses the full
numerator's FP binary budget; `TubeExtraneousResidue` and `TubeExtraneousSign`
combine the complete varying-modulus evaluator with streamed CRT to give
integer zero tests and three-way signs. Zero and either strict sign are in
PSPACE under the existing coordinate-reader contracts.

`TubeExtraneousCoefficientPolynomial` proves degree-bounded scalar recovery
and zero preservation for each encoded deformation coefficient.
`TubeExtraneousCoefficientZero` reuses the full numerator's FP quotient/remainder
queries and coefficient-count code to scan every scalar coefficient, including
the complete integer-zero child's cost. `TubeExtraneousLowestSpace` feeds these
whole-coefficient tests into the certified bounded first-index search. The
computed index is exactly the actual extraneous determinant's natural trailing
degree, is at most the padded dimension, and is minimal with nonzero coefficient.
Sequential composition gives selected residues and integer signs of that actual
lowest bivariate coefficient; `TubeExtraneousLowestLanguages` proves its scalar
zero, negative, and positive languages in PSPACE. Specialization remains
nonzero, and vanishing of the symbolic lowest coefficient is equivalent to
an increase in deformation order after specialization.

`TubeExtraneousCharacteristicSpace` pairs the complete lowest-index and sign
evaluators, then applies the FP order-parity correction to compute the true
principal minor's lowest characteristic-denominator coefficient signs. Both
child costs are included; no index, coefficient, or sign oracle is introduced.
The corresponding zero and strict-sign tests are in PSPACE.

The resultant quotient identity, geometric root persistence, effective sampling,
and ETR membership in PSPACE remain open. Both the full numerator and extraneous
denominator now have complete lowest-index and integer-sign computations under
the same original coordinate-reader contracts.

## True characteristic quotient and inactive padding

`PrincipalCharacteristic` proves the exact subtractive determinant identity
for a principal matrix padded by identity rows: each omitted index contributes
one factor of `1-s`. `MacaulayActiveCharacteristic` selects exactly the
fixed-width indices at the Macaulay level and removes all inactive rows and
columns. The padded numerator is $(1-s)^{\mathrm{padding}}$ times this true degree-level
characteristic determinant. Their natural trailing degrees and trailing
coefficients coincide, without a domain hypothesis. Thus removing computational
padding preserves the lowest data used by the existing evaluator.

`MacaulaySubtractiveSystem` replaces every homogeneous input by
$f_{i}-s\cdot x_{i}^{d_{i}}$. Every active principal matrix of the shifted system is exactly
the subtractive characteristic matrix of the corresponding original principal
matrix. This applies to both the full degree-level and extraneous matrices.

`PolynomialQuotientLowest` constructs rational functions from polynomial
numerator and denominator over an integral domain. For nonzero inputs, the
integer difference of trailing degrees and the ratio of trailing coefficients
in the coefficient fraction field depend only on the rational function.
Factoring the lowest powers of `s` gives a power with this signed exponent
times a quotient whose numerator and denominator have nonzero constant
coefficients. If $\mathrm{numerator} = \mathrm{polynomial} \cdot \mathrm{denominator}$ is proved, the signed
order and coefficient ratio equal that polynomial's ordinary lowest order and
coefficient.

`TubeCharacteristicQuotient` applies this to the true degree-level numerator
and actual extraneous denominator over `ℤ[θ][T]`. Both determinants and their
rational quotient are nonzero. The quotient equals the ratio of the two
principal determinants for the same shifted tube system. Its lowest data are
representation independent. Its order is the difference of the two computed
deformation indices, and its lowest coefficient ratio uses the already
certified characteristic trailing coefficients.

`TubeCharacteristicQuotientSpace` combines both complete lowest-index routines
and FP signed subtraction to evaluate the quotient order. Its negative-order
language is in PSPACE. The complete numerator sign routine also applies to
selected scalar coefficients of the true unpadded numerator's lowest term.
All original search and reader costs are included.

This definition uses rational functions. Its polynomial representative and
ordinary lowest data are constructed below. Identification with the
multivariate resultant, computing the remaining polynomial-quotient
coefficients, proving geometric root persistence, and completing the
sampling algorithm remain further obligations.

## Reduced-monomial count and characteristic quotient degree

`MacaulayReducedCount` gives an explicit bijection for positive homogeneous
degrees with $\mathrm{level} d < 2^W$. A reduced level monomial has exactly one eligible
coordinate `i`. Its other exponents range independently from zero to $d_j-1$;
the level fixes its exponent at `i`. The constructed exponent vector has the
required level, exactly that eligible coordinate, and fits the existing binary
rank representation. Injectivity and surjectivity give
$\operatorname{card}(\mathrm{active}) = \operatorname{card}(\mathrm{extraneous}) + \sum _{i} \prod_{j\ne i} d_{j}$.

`CharacteristicQuotientDegree` proves that every subtractive characteristic
determinant over an integral domain is nonzero and has natural degree equal to
its matrix dimension. After an injective coefficient embedding in a field,
Mathlib's `RatFunc.intDegree` of the determinant quotient is therefore exactly
$D = \sum _{i} \prod_{j\ne i} d_{j}$. This calculation does not require the quotient to be a
polynomial. The coefficient extension is an injective rational-function ring
homomorphism and maps fraction presentations to their coefficientwise images.

`TubeCharacteristicQuotientDegree` applies the count using the actual tube's
proved positive degrees and fixed-width coverage. The existing tube quotient
maps faithfully to the quotient over the fraction field of `ℤ[θ][T]`, with
integer degree `D`. The tube's `D` is positive and at most the padded matrix
dimension. The polynomial quotient constructed below has natural degree
exactly `D` over the original coefficient ring.

The degree calculation supplies the expected matrix-size difference without
assuming polynomiality or multivariate resultant identification. Polynomiality
is proved below; resultant identification remains open.

## Independence of the last polynomial and partial polynomiality

`MacaulayExtraneousLast` proves that an unreduced monomial's pivot cannot be
the last coordinate: it has at least two eligible coordinates and the pivot
is the least eligible one. Replacing the last input polynomial therefore
preserves both the true extraneous principal matrix and its identity-padded
representation. The same independence holds for the shifted characteristic
system. Coefficient maps commute with the true full and extraneous principal
determinants.

`MacaulayLastParameter` treats input polynomials with coefficients in `K[u]`,
where `K` is any field. Swapping `u` with the characteristic parameter `s`, then
embedding `K[s]` in $K(s)$, gives an injective coefficient map and an injective
map on rational functions. The mapped full and extraneous determinants agree
with those for the actual shifted input system.

If every input except the last is constant in `u`, the mapped extraneous
determinant is the constant polynomial whose value is the characteristic
determinant of the base extraneous matrix in $K(s)$. This value is nonzero,
with no supplied denominator-nonvanishing hypothesis. Multiplying the mapped
full determinant by its inverse explicitly constructs a nonzero polynomial
in $K(s)[u]$. The image of the original characteristic determinant quotient is
exactly this polynomial.

`MacaulayPivotCount` restricts the reduced-monomial bijection to the last pivot.
Every active row with that pivot is reduced, since an unreduced row cannot
choose the last coordinate. There are exactly $\prod_{j\ne\mathrm{last}} d_{j}$ such rows when the
degrees are positive and the fixed-width blocks cover the Macaulay level.

`MacaulayLastParameterDegree` bounds a parameter-dependent row by the source
coefficient degree and all other rows by zero. Transposing the matrix permits
the existing columnwise determinant degree theorem to sum these row bounds.
If coefficients of the last input have degree at most `E` in `u`, the full
mapped determinant and the quotient polynomial have degree at most
$E\cdot \prod_{j\ne\mathrm{last}} d_{j}$. Multiplication by the nonzero constant denominator inverse
preserves the numerator degree exactly.

The explicit affine family $f_{\mathrm{last}}+u\cdot h$ has coefficient degree at most one.
It preserves the specified spatial homogeneity when the original inputs and
variation are homogeneous of the corresponding degrees. The resulting
nonzero quotient polynomial in $K(s)[u]$ has degree at most $\prod_{j\ne\mathrm{last}} d_{j}$.

This proves polynomiality in a coefficient parameter confined to the last
input. Polynomiality in the characteristic parameter `s` is proved below.
The full multivariate resultant identity and subsequent sampling argument
remain open.

## Full multiplication matrix and finite Koszul relations

`MacaulayMultiplicationMatrix` indexes all monomial multipliers whose degree
plus the corresponding input degree is the Macaulay level. The columns are the
actual degree-level monomials. Homogeneous inputs give homogeneous level rows.
The original pivot and remainder determine an injective row selector; its
selected submatrix is exactly the true square Macaulay matrix. Both indices
use the existing fixed-width representation, with no identity padding in this
rectangular matrix.

For a family of compatible polynomial multipliers, finite coefficient
reconstruction proves that assembling the row coefficients gives precisely
$\sum _{i} q_{i}\cdot f_{i}$. Multiplication by the rectangular matrix reads the corresponding
level coefficients. `MacaulayKoszulRelations` constructs the family with
components $m\cdot f_{j}$ at `i` and $-m\cdot f_{i}$ at `j`. If
$\operatorname{degree}(m)+d_{i}+d_{j}=\mathrm{level}$, its coefficients form a kernel vector, by polynomial
commutativity. Over an integral domain it is nonzero whenever $f_j$ is nonzero.

`MacaulayShiftedKoszul` proves that $f_{i}-s\cdot x_{i}^{d_{i}}$ remains homogeneous and is
always nonzero over a nontrivial coefficient ring: its designated monomial
has characteristic coefficient `-1`. Over an integral domain, compatible pairs yield nonzero
finite Koszul relations for the shifted full multiplication matrix, without
requiring original inputs to be nonzero.

`TubeMacaulayKoszul` supplies an explicit compatible pair for the actual tube
system. The spatial count is at least three, the projection degree is one,
and two other coordinate degrees have the uniform bound at least two. These
facts provide a multiplier at the Macaulay level, and the existing width and
homogeneity theorems give a nonzero finite relation over `ℤ[θ][T][s]`.

These relations concern the full rectangular multiplication matrix. Generic
kernel spanning, higher graded exactness, and polynomial determinant
cancellation are proved below; resultant identification remains open.
No kernel statement for the selected square matrix is inferred from these
rectangular relations.

## Generic shifted multiplication is surjective

`MatrixMinorSection` constructs a section for a rectangular row-vector map
whenever a selected square row minor has unit determinant. If `E` is the row
selector and $A=E\cdot M$, the section matrix is $A^{-1}\cdot E$, and its product with `M`
is the identity. The argument works over any commutative ring with that unit
condition.

`MacaulayGenericShift` works over an integral-domain coefficient ring `R`.
The selected square matrix for $f_{i}-s\cdot x_{i}^{d_{i}}$ has nonzero determinant because
it is the subtractive characteristic matrix. Mapping to `RatFunc R` makes
this determinant a unit and supplies the section of the full multiplication
matrix. Homogeneity and the existing exponent-width bound turn coefficient
surjectivity into polynomial equality: every homogeneous polynomial at
$L=1+\sum _{i}(d_{i}-1)$ is an assembled combination of the shifted inputs.

Consequently, the ideal generated by the shifted inputs contains
$(x_{0},\ldots ,x_{n-1})^L$. Evaluating the coordinate monomial certificates proves that
any common zero over any integral-domain coefficient extension is the origin.
`TubeMacaulayGenericShift` instantiates the section, surjectivity, homogeneous
ideal membership, ideal-power containment, and common-zero theorem for the
actual bivariate tube rows, using their proved homogeneity and width bounds.
The coefficient field here is `RatFunc (Polynomial (Polynomial ℤ))`, with
independent characteristic, projection, and perturbation parameters.

This establishes exactness at the final target of the graded multiplication
map. Kernel spanning is established next. The inverse is noncomputable
and has no space bound here. These statements concern the generic shifted
system; specializing the characteristic parameter to zero is not an available
map on its entire rational-function coefficient field. The polynomial
resultant quotient and Canny's ETR upper bound remain unproved.

## Koszul relations span the generic shifted kernel

`MacaulayMonomialDivision` sends each multiplier row $a=(i,m)$ to its
coordinate-power product $m\cdot x_{i}^{d_{i}}$, a monomial at the Macaulay level. Let `j`
be its selected pivot. If $i=j$, this row is already selected. Otherwise
`m` is divisible by $x_{j}^{d_{j}}$; dividing it gives a degree-compatible Koszul
relation. For coordinate powers, its finite coefficient vector is exactly
$e_a-e_{\operatorname{selected}(\operatorname{product}(a))}$. With $D_{0}$ the full multiplication matrix,
`H` the selected-row embedding, and $E_{0}$ the matrix of these relation rows,
the proved identity is $D_{0}\cdot H+E_{0}=I$. Every coordinate-power kernel vector `v`
therefore satisfies $v\cdot E_{0}=v$, over any commutative ring.

`MatrixKernelContraction` proves a general finite exactness criterion. For
matrices `D,E,H` with $E\cdot D=0$, suppose both $A=D\cdot H+E$ and $H\cdot D$ have unit
determinant. For $v\cdot D=0$, set $w=v\cdot A^{-1}$. The identity $A\cdot D=D\cdot (H\cdot D)$ shows
$w\cdot D=0$, and then $v=w\cdot A=w\cdot E$. Thus every kernel vector is a row combination
of `E`; the converse follows from $E\cdot D=0$.

`MacaulayKoszulContraction` applies this criterion to $f_{i}-s\cdot x_{i}^{d_{i}}$. The
division relation matrix depends linearly on the inputs and commutes with
coefficient maps. Consequently the shifted source contraction is
$D_s\cdot H+E_s=(D\cdot H+E)-s\cdot I$. Its determinant is nonzero, as is the target
contraction's selected Macaulay characteristic determinant. Both become
units over `RatFunc R`, for any integral-domain input coefficient ring `R`.
The resulting kernel theorem supplies a finite generating family and proves
that the kernel equals the span of all degree-compatible Koszul relations.
`TubeMacaulayKoszulExact` specializes both statements to the actual tube
system using its existing homogeneity and width bounds, without extra
algebraic or coordinate-reader assumptions.

This proves exactness at the multiplier space, in addition to the previously
proved surjectivity at the final target. It concerns this single graded
piece over the generic coefficient field. Higher Koszul exactness and
polynomial cancellation are proved below. Resultant identification and the
space bounds for using these noncomputable inverses remain open.

## A kernel basis and the source-contraction determinant

`MacaulayRelationMinor` removes the selected multiplier rows, whose division
relations are identically zero. The remaining row indices define
`RelationIndex`; restricting the division relation matrix to the matching
columns gives the square `relationMinor`. For coordinate powers this minor
is the identity, because each relation is $e_a-e_{\operatorname{selected}(\operatorname{product}(a))}$ and
the second coordinate lies outside the complementary columns. Its
characteristic shift is exactly `B-sI`, with `B` the original relation minor.
The generic relation minor is therefore invertible over `RatFunc R`.

Restricting a linear relation among these remaining rows to the complementary
columns proves their linear independence. The earlier kernel-spanning
theorem still applies after discarding the zero selected rows, so every
generic kernel vector has a unique expansion in the remaining Koszul rows.
The module constructs a Mathlib `Basis` of this kernel and proves that its
vectors are exactly those rows. `TubeMacaulayKernelBasis` supplies the basis
and unique-coordinate theorem for the actual tube system.

`MatrixSelectedBlock` proves the associated determinant comparison over any
commutative coefficient ring. For an injective row selector `f`, write `H`
for its selection matrix. If `E` vanishes on the selected rows, then
$D\cdot H+E$ is block triangular along selected and complementary indices. Its
selected diagonal block is `D.submatrix f id`, and its complementary block
is the principal restriction of `E`. Hence the source-contraction determinant
is the product of these two determinants. Applied to Macaulay division
relations, this gives both the original and characteristic identities
$\operatorname{det}(D\cdot H+E-sI)=\operatorname{det}(A-sI)\cdot \operatorname{det}(B-sI)$, where `A` is the selected Macaulay
matrix and `B` is the complementary relation minor.

This factorization concerns the source contraction and its kernel basis.
The next comparison factors $\operatorname{det}(B)$ by the extraneous determinant. It does
not prove that the extraneous characteristic determinant divides
$\operatorname{det}(A-sI)$. Polynomial cancellation and higher Koszul exactness are proved
below; resultant identification and bounds for computing the noncomputable
kernel coordinates remain open.

## The extraneous determinant is a relation-determinant factor

`MacaulayRelationBlocks` orders the complementary relation rows by their
input coordinate `i`. The selected pivot `j` is strictly smaller than `i`.
The relation has components only at `i` and `j`, so its square relation
matrix is lower block triangular by `i`. Within a fixed component, adding
the same coordinate power to both monomial exponents identifies each entry
with the corresponding extraneous Macaulay entry. The extraneous matrix is
upper block triangular by the greatest eligible coordinate: a nonzero entry
must preserve every eligible coordinate other than the least pivot, and
therefore cannot decrease the greatest one.

`MacaulayRelationBlockEquiv` divides each unreduced target monomial by its
greatest eligible coordinate power. The resulting multiplier is not selected
and has that greatest coordinate as its input coordinate. This gives a
bijection between the extraneous block with greatest coordinate `i` and the
relation block with both input coordinate and greatest coordinate equal to
`i`. Simultaneous reindexing preserves the diagonal-block determinants.

`MacaulayRelationExtraneous` takes the determinant products over these finite
blocks, including empty blocks. The first relation decomposition is by input
coordinate `i`, and its second decomposition is by greatest coordinate `k`.
The diagonal factors $i=k$ multiply to the extraneous determinant. The
remaining $i\ne k$ factors define an explicit `higherRelationFactor`, proving
$\operatorname{det}(B)=\operatorname{det}(\mathrm{extraneous})\cdot \mathrm{higherRelationFactor}$ over any commutative ring.
Applying this identity to the shifted polynomial system proves
$\operatorname{det}(B-sI)=\operatorname{det}(\mathrm{extraneous}-sI)\cdot \mathrm{higherRelationFactor}_s$. Over an integral
domain the remaining polynomial is nonzero. Combining this with the source
contraction factorization gives the exact three-factor identity
$\operatorname{det}(D\cdot H+E-sI)=\operatorname{det}(A-sI)\cdot \operatorname{det}(\mathrm{extraneous}-sI)\cdot \mathrm{higherRelationFactor}_s$.

`TubeMacaulayRelationFactor` instantiates the characteristic factorization,
divisibility, and nonzero remaining factor for the actual bivariate tube
system using the existing width bound. No coordinate-reader hypothesis or
new algebraic assumption is supplied. These are relation and contraction
determinant identities. Polynomiality of the quotient
$\operatorname{det}(A-sI)/\operatorname{det}(\mathrm{extraneous}-sI)$ is proved below; resultant identification and
the remaining algorithmic space bounds remain open. Higher weighted
exactness is proved below using the pure-power contraction and characteristic
invertibility.

## The exterior Koszul complex and coordinate-chart exactness

`KoszulExterior` uses Mathlib's `CliffordAlgebra.contractLeft` on the exterior
algebra of the free module $I \to R$. For the linear form
$v \mapsto \sum _{i} v_{i}\cdot p_{i}$, contraction gives a square-zero differential, and different
coefficient families give anticommuting differentials. The differential
sends exterior degree $k+1$ into degree `k`; the proof uses the spanning
exterior products and the contraction rule for one more generator.
`KoszulComplex` packages these maps as a Mathlib `ChainComplex`.

If $\sum _{i} v_{i}\cdot p_{i}=1$, exterior multiplication by $\iota (v)$ gives
$d(\iota (v)\cdot x)+\iota (v)\cdot d(x)=x$. It raises exterior degree by one. Consequently the
kernel in every positive exterior degree is exactly the image from the
next degree, and the degree-one map surjects onto degree zero.

`MacaulayKoszulExteriorBridge` connects this construction to the existing
polynomial matrices. On exterior degree one the differential is the
polynomial combination $\sum _{i} q_{i}\cdot p_{i}$, embedded as a scalar in the exterior
algebra; scalar injectivity gives the zero equivalence. For compatible
homogeneous multiplier families, the finite Macaulay kernel condition is
equivalent to this exterior kernel condition. Each previously constructed
`koszulMultipliers` vector is the boundary of a monomial multiple of the
exterior pair in the corresponding orientation.

`MacaulayLocalizedKoszul` takes the generic coefficient field $K=\mathrm{RatFunc} R$
and the spatial polynomial ring $P=K[x_{0},\ldots ,x_{n-1}]$. The existing Macaulay
certificate puts $x_{i}^L$ in the shifted ideal. For any ring map from `P` that
makes `xᵢ` a unit, mapping the finite ideal combination and multiplying by
the inverse of $x_{i}^L$ gives a combination of the mapped inputs equal to one.
The canonical instance is `Localization.Away (X i)`. Thus the shifted
Koszul complex on every coordinate chart has a contracting homotopy,
exact maps in all positive exterior degrees, and a surjective degree-zero
map. `TubeMacaulayLocalizedKoszul` specializes these results to the actual
tube rows using their proved homogeneity and width bound, with no extra
coordinate-reader or algebraic certificate.

The grading here is exterior degree over the localized spatial polynomial
ring. The homotopy coefficients may contain inverted spatial coordinates.
Exactness on these charts does not by itself prove higher exactness in the
finite weighted polynomial grade used by the Macaulay determinant.
Higher exactness of that finite complex is now proved below using a
polynomial pure-power contraction and generic characteristic invertibility.
The resultant quotient identity and the full ETR algorithm remain open.
No algorithmic space bound for these homotopies is asserted.

## The finite weighted Koszul complex

`KoszulWeightedSpace` works inside the exterior algebra over the spatial
polynomial ring, viewed as a module over the coefficient ring. A generator
is a monomial times an exterior word of coordinate basis vectors. Its weight
is the monomial degree plus the sum of the corresponding input degrees.
At weight `L` and exterior degree `k`, all words `Fin k → Fin n` and all
compatible fixed-width monomial ranks form a finite spanning family. This
family may be redundant: the exterior algebra already imposes alternation
and makes repeated coordinates zero. Its span is a finite coefficient
module, agrees for any two widths with $L<2^W$, and is zero for $k>n$.

`KoszulWeightedComplex` proves that homogeneous inputs preserve this weight.
On one more exterior generator, contraction is the input polynomial times
the tail minus that generator times the contracted tail. Expanding a
homogeneous polynomial into monomials proves membership in the target
weighted span; exterior multiplication contributes precisely the removed
input degree. Restricting the exterior differential gives a Mathlib chain
complex of these finite modules, with proved zero consecutive compositions.
This construction is over any commutative coefficient ring.

`KoszulWeightedMatrix` chooses finite bases over a coefficient field and
transposes the usual linear-map matrices to use the project's row-vector
convention. Their consecutive products are zero. The spanning-family count
gives dimension bound $n^k\cdot (2^W)^n$. These bases are noncomputable and are
not supplied with polynomial-space coefficient readers.

`MacaulayWeightedBridge` puts every existing multiplier row into the
degree-one weighted generating family at $L=1+\sum _{i}(d_{i}-1)$. Its differential
is exactly the scalar embedding of that polynomial row. Applying the
exterior algebra's scalar retraction and a target-monomial coefficient query
recovers each entry of the original full rectangular Macaulay matrix.
This identifies the first linear operation on its canonical generators;
the original higher matrices use the separately chosen finite bases.

`KoszulMonomialBasis` combines the polynomial monomial basis with Mathlib's
ordered exterior basis. Restricting to pairs `(monomial, subset)` with the
specified subset size and total weight gives a finite independent family.
`KoszulWeightedBasis` proves that this family spans the existing weighted
space: repeated exterior coordinates vanish, and sorting an injective word
changes it by a unit sign. Consequently each weighted piece is free over
any commutative coefficient ring, with no field or exponent-width assumption
needed for this basis theorem. Its coordinates are exactly the polynomial
coefficients of the ambient exterior coordinates.

`KoszulCanonicalMatrix` uses these bases for the differential matrices and
proves both the coefficient formula and zero consecutive products.
`MacaulayCanonicalMatrix` identifies all degree-one subset indices with
the existing multiplier indices and all degree-zero indices with the active
monomial indices. Both identifications are bijective. Reindexing the first
canonical matrix therefore gives the entire full Macaulay matrix.
These bases are defined over the original
coefficient ring, with index sets depending only on degrees and width;
they avoid a field-dependent basis choice when studying a parameterized
complex. Polynomial-space entry readers remain to be constructed.

`TubeMacaulayWeightedKoszul` instantiates the complex and its matrices for
the actual generic shifted tube system, using its proved homogeneous
degrees and exponent width. It includes finite pieces, vanishing above the
spatial arity, the dimension bound, and zero consecutive matrix products.
`TubeMacaulayCanonicalKoszul` additionally supplies the canonical bases,
their matrices, and the full first-matrix reindexing identity for this system.
The pure-power case has a polynomial contraction, described below, and
generic characteristic invertibility transfers exactness to the shifted
system. Polynomial cancellation is proved below; resultant identification
and the ETR space bound remain open.

## Polynomial contraction of the finite pure-power complex

`KoszulCoefficientDivision` defines a coefficient-ring linear division
operator on the ambient monomial–subset basis. Terms not divisible by
the divisor are discarded. Division commutes with insertion of a coordinate
exterior generator; multiplying by the divisor and then dividing is the
identity. If the coefficient monomial is divisible, division also commutes
with the pure-power differential on that exterior word.

`KoszulPowerHomotopy` inserts coordinate `i` after dividing coefficients by
$X_i^{d_i}$. The identity $D H_i + H_i D = 1$ holds on a monomial exterior
word whenever its coefficient is divisible by this power or the word already
contains `i`. In the latter case insertion vanishes, and applying division
to the ordinary exterior homotopy identity proves the result.

`KoszulMultidegree` assigns a word the exponent vector
$m + \sum _j \operatorname{single}(v_j, d_{v_j})$. Its total degree is the previously defined
weight. The pure-power differential preserves this vector; exterior
insertion adds the corresponding single-coordinate exponent.
`KoszulLevelHomotopy` chooses the Macaulay pivot separately in each vector
of total degree `Macaulay.level d`. The pivot is eligible, so the local
homotopy identity applies. Preservation of multidegree keeps the same pivot
throughout each differential image, proving the assembled identity.

`KoszulWeightedContraction` proves that this polynomial homotopy maps the
finite weighted piece of exterior degree `k` into degree $k+1$, for the
usual exponent-width bound. It supplies the restricted homotopy identities,
exactness in every positive degree, and surjectivity in degree zero.
`KoszulWeightedContractionMatrix` expresses both identities in the canonical
finite bases. All results hold over any commutative coefficient ring.
`TubeMacaulayPowerKoszul` instantiates them for the coordinate-power system
with the tube's degrees, on the same finite pieces as the actual shifted
tube complex.

## Higher exactness for the finite generic shifted complex

`KoszulCoefficientMap` applies any coefficient ring homomorphism to the
ordered exterior coordinates. This semilinear map preserves monomial
exterior words and commutes with coordinate insertion and the differential.
`KoszulLinearInput` proves linear dependence of contraction on its input
system. `KoszulCanonicalMatrixMap` consequently proves coefficient-extension
identities for both the canonical differential and pure-power homotopy
matrices, and the scalar-pencil identity for the differential matrices.

`KoszulGenericContraction` writes the finite operator $H D + D H$ in these
canonical bases. For the subtractive system, the pure-power homotopy identity
identifies it with `A-s I`, where `A` is the unshifted operator over the
original coefficient ring. Its determinant is a signed characteristic
polynomial, hence nonzero. Mapping to the rational function field proves
invertibility of the actual shifted operator in every positive exterior
degree.

`MatrixHomotopyExact` supplies the finite-dimensional exactness argument.
For consecutive row-vector matrices $B D=0$, the operator $H B+D J$
preserves the kernel of `D`. If its determinant is a unit, its restriction
to that finite-dimensional kernel is injective and therefore surjective.
For a kernel vector `v`, choose a kernel vector `w` mapped to `v`; then
$v=w H B$, so `v` is a boundary.

`KoszulGenericExact` applies this criterion to every positive exterior
degree of the canonical shifted matrices and transfers the result through
the canonical coordinate bases to the actual weighted differential maps.
`KoszulGenericZero` transfers full Macaulay matrix surjectivity through the
proved index equivalences and bases, proving surjectivity in degree zero.
`TubeMacaulayGenericKoszul` instantiates both results for the actual shifted
tube complex, together with nonzero determinants for its finite homotopy
operators. No extra algebraic certificates or entry readers are assumed.

Higher exactness at the finite Macaulay grade is thus proved. Polynomial
cancellation is proved below. Identification of the quotient with the
multivariate resultant, resource bounds for this construction, and the
complete ETR polynomial-space theorem remain open.

## Normalized splitting and the concrete determinant factors

`KoszulHomotopyNormalization` proves that the polynomial homotopy preserves
multidegree and squares to zero. Its finite maps and matrices consequently
have zero consecutive compositions. The pure-power contraction identity
then proves exactness of these raising maps themselves, with an injective
degree-zero map.

`KoszulHomotopySplit` constructs complementary projections `H D_0` and
`D_0 H` on every positive weighted piece. Their images are exactly the
incoming homotopy image and incoming pure-power differential image. This
gives a module product decomposition over any commutative coefficient ring,
independent of the homogeneous input system. `KoszulHomotopyOperator` proves
that $D H+H D$ commutes with `H`, preserves the incoming homotopy image, and
has canonical matrix `contractionMatrix`.

`MacaulayHomotopyBridge` identifies the first two concrete homotopy
operations. On degree-zero basis terms, `H` selects precisely the existing
Macaulay multiplier row. In degree one, `D H` gives precisely the existing
`divisionRelations` matrix. Reindexing the finite degree-one operator
therefore gives $\mathrm{fullMatrix}\cdot \mathrm{rowSelection}+\mathrm{divisionRelations}$.

`MacaulayHomotopyDeterminant` transfers the existing determinant identities
to this same operator: its determinant is $\operatorname{det}(\mathrm{activeMinor})\cdot \operatorname{det}(\mathrm{relationMinor})$,
and hence $\operatorname{det}(\mathrm{activeMinor})\cdot \operatorname{det}(\mathrm{extraneousMinor})\cdot \mathrm{higherRelationFactor}$.
The characteristic identity holds over the original polynomial coefficient
ring. `TubeMacaulayPowerKoszul` supplies the normalized splitting for the
tube's pieces; `TubeMacaulayHomotopyDeterminant` supplies invariance and both
the characteristic and generic determinant factorizations for the tube.

These results connect the exact finite complex to the concrete factors in
the proposed resultant quotient. This factorization concerns the larger
degree-one homotopy determinant. The remaining higher factors are controlled
below to prove polynomial cancellation; exactness over the rational function
field alone does not supply that divisibility.

Two sources for the remaining step were checked on 2026-10-20.
[Quitté–Tête's combinatorial treatment](https://arxiv.org/abs/2308.12232)
uses the multiplicative structure of graded Koszul resolutions together
with Macaulay decompositions to obtain denominator formulas. Its
Theorem XIII.4.1 (printed pp. 244–245) was subsequently inspected, including
the rendered pages: its induction uses a polynomial resultant already
constructed earlier in the text. That proof cannot be used before
constructing that resultant. [D'Andrea–Dickenstein, §3](https://arxiv.org/html/math/0007036v1)
gives generalized quotient formulas, but the proof of Lemma 3.3 invokes
the classical Macaulay formula when the degree exceeds the critical degree.
That lemma therefore cannot supply an independent proof of the classical
case needed here.

## Universal denominator cancellation and ordering comparisons

`GroupedPolynomialDivisors` proves that a divisor of a nonzero polynomial
can use only variables present in that polynomial. If every variable has
an input-group owner and denominator `b_i` omits group `i`, a common divisor
of all the denominators has no variables and is constant. If all `b_i`
evaluate to one at a common assignment, the constant divisor is a unit.
This holds over any integral domain, including integer coefficients.

`GroupedDenominatorCancellation` uses reduced fractions over a UFD. The
reduced denominator divides every polynomial denominator representing the
same fraction. Thus a family with the property above forces that fraction
to be a polynomial. In particular, identities $a_i\cdot b_j=a_j\cdot b_i$ produce
one polynomial `q` with $a_i=b_i\cdot q$ for every `i`.

`MacaulayUniversalSystem` constructs the homogeneous input polynomials
explicitly from coefficient variables `(input, exponent)` and fixed-width
monomial sums. Its permuted form permutes both input and spatial indices.
The coefficient assignment selecting the original coordinate powers
specializes every such system to the corresponding diagonal power system.
Every homogeneous system with fitting exponents is reconstructed by its
own coefficient assignment.

`MacaulayUniversalDenominators` applies the common-divisor theorem to the
actual universal extraneous determinants. A coefficient-group erasure map
fixes the determinant because the extraneous matrix never uses its last
input. Swapping each input with the last one gives the required family,
and the common power specialization is one. The universal active
determinants have that same normalization. Consequently the actual
cross-comparison identities for these universal numerator/denominator pairs
are equivalent to existence of a unique common polynomial quotient
normalized to one at the power system. The concrete cross-comparisons and
the resulting normalized polynomial quotient are proved below.

`MacaulayUniversalSpecialization` proves that positive input degrees fit
whenever the usual Macaulay-level width fits. It specializes the universal
system and both determinants, and transfers universal polynomial
divisibility to the actual system. `TubeMacaulayUniversal` instantiates
these reconstruction and determinant identities for the actual tube
subtractive system over the polynomial characteristic-parameter ring.

This order of proof matters: specialize a universal polynomial quotient
after proving it exists. The absence of a common nonunit divisor in the
universal denominator family need not survive specialization. The universal
numerator/denominator cross-comparisons are proved below from the Koszul
determinant structure, before specializing the polynomial factorization.

`KoszulSpecializationExact` now proves that next exactness step. For a
homogeneous system admitting a coefficient homomorphism to the coordinate
powers over a nontrivial ring, each positive-degree finite homotopy operator
specializes to the identity. The degree-zero operator `H_0 D_0` does too.
Their determinants specialize to one and are therefore nonzero. Passing
from a domain to its fraction field makes these operators invertible;
canonical coordinates give exactness of the actual weighted differential
maps and degree-zero surjectivity. No characteristic shift is needed.

`MacaulayUniversalExact` applies this result to the universal system for
every simultaneous input/spatial ordering, over the fraction field of its
coefficient ring. The hypotheses are explicit input-degree and Macaulay-level
width bounds. The result concerns that fraction field, not exactness over
the polynomial coefficient ring or after arbitrary specialization.

`KoszulPivotBasis` supplies a monomial decomposition over any commutative
coefficient ring. For a canonical basis index $(m,s)$, `HasPivot` tests
whether the Macaulay pivot of $m + \operatorname{subsetExponent} d s$ belongs to `s`.
Such basis vectors are killed by the raising homotopy. Conversely every
homotopy image lies in their span: division and insertion preserve the
multidegree, and sorting an exterior word contributes only a unit sign.
The proved homotopy exactness identifies this span with its incoming image
in every positive degree. Explicit restricted monomial bases and the
complementary nonpivot basis give a product decomposition. These explicit
bases also establish freeness of both summands over the original ring.

`KoszulPivotContraction` uses preservation of the homotopy image to prove
that the canonical contraction matrix is block triangular for this monomial
partition. Its determinant is the product of the two concrete principal
block determinants in every positive degree. For the universal system over
the coefficient fraction field, both block determinants are nonzero.

The determinant-of-complex comparison below identifies the concrete
numerator/extraneous ratios across orderings, including the higher Macaulay
factors and signs. Exactness and the monomial block factorization alone do
not supply that comparison.

`KoszulPivotEquiv` now identifies adjacent monomial summands over the
original commutative coefficient ring. The kernel of `H_k` is the pivot
span in every degree, including degree zero, where both are zero. The
first isomorphism theorem and the monomial complement therefore give an
explicit linear equivalence from the nonpivot span in degree `k` to the
pivot span in degree $k+1$, whose forward map is `H_k`. Projection to the
nonpivot span preserves homotopy images and canonical nonpivot coordinates.

`KoszulAdjacentBlocks` restricts the contraction to the pivot span and
projects it to the nonpivot span. Their matrices in the restricted monomial
bases are the two existing principal blocks. Commutation with `H` makes
the pivot operator in the next degree conjugate to the projected nonpivot
operator. `MatrixBasisConjugate` compares their determinants in the specified
finite bases, even with different index types. This gives an exact equality
over any commutative ring, without an unspecified sign or field extension.

Write `P_k` and `Q_k` for the pivot and nonpivot blocks of the contraction
on exterior degree $k+1$. The proved recurrence is
$\operatorname{det}(P_{k+1}) = \operatorname{det}(Q_k)$, and hence
$\operatorname{det}(L_{k+1}) = \operatorname{det}(Q_k) \cdot \operatorname{det}(Q_{k+1})$.
`MacaulayPivotBoundary` supplies its concrete initial terms. The degree-zero
contraction reindexes exactly to `activeMinor`, and the degree-zero homotopy
conjugates it to the first pivot block, so $\operatorname{det}(P_0) = \operatorname{det}(\mathrm{activeMinor})$.
The canonical nonpivot indices in degree one are precisely the unselected
Macaulay multiplier indices. Explicit reindexing identifies `Q_0` with
`relationMinor` over any commutative ring. Thus $\operatorname{det}(P_1)$ is the relation
determinant, already factored as $\operatorname{det}(\mathrm{extraneousMinor})\cdot \mathrm{higherRelationFactor}$.
The higher factors, their ordering comparisons, and polynomial cancellation
of the extraneous factor are proved below.

`KoszulExteriorSupport` and `KoszulNonpivotRows` supply the higher-degree
row formula. For a nonpivot monomial/exterior basis index $(m,s)$, its
multidegree pivot `i` is absent from `s`, is smaller than every element of
`s`, and satisfies $d_i \le m_i$. The homotopy divides by $X_i^{d_i}$ and
inserts `i`. After projection to the nonpivot summand, the contraction is
`D H`; the other term is killed. Applying the exterior Leibniz identity
gives multiplication by `p_i` after division, plus terms whose exterior
subset contains `i`. The latter have zero coordinate on every target
subset omitting `i`. Thus the same-subset entry is precisely the coefficient
of $X^{m'}$ in $X^{m-d_i e_i} p_i$.

`KoszulNonpivotMacaulay` sends each basis index to the active monomial
$m + \operatorname{subsetExponent} d s$, with an explicit fixed-width rank. On a fixed
exterior subset, this map is injective. Multiplying by that subset's
coordinate powers identifies the diagonal entries exactly with the
corresponding active Macaulay entries. Every fixed-subset block is therefore
a concrete principal submatrix of `activeMinor`, without a field extension
or a sign ambiguity.

`KoszulNonpivotBlocks` proves triangularity by the least exterior coordinate.
Inside each such diagonal block, entries between different exterior subsets
vanish. `KoszulSubsetDeterminant` removes the empty intermediate blocks:
$\operatorname{det}(Q_k)$ is the product, over all exterior subsets, of these concrete
Macaulay principal-submatrix determinants. Subsets of the wrong cardinality
have empty index types and determinant one. Adjacent conjugacy transfers
this product to $\operatorname{det}(P_{k+1})$. All identities hold over any commutative ring.

This proves the exterior-subset stage of the higher determinant decomposition.
The next stage partitions the eligible-coordinate sequence by the positions
of the selected exterior coordinates. The following modules construct those
indices and counts, prove full-mask triangularity, and identify the factors.

`KoszulEligibleIndices` gives an exact description of each fixed-subset
factor using active monomials alone. For exterior subset `s` of cardinality
$k+1$, its index monomial `t` satisfies $s \subseteq \operatorname{eligible}(t)$ and omits the
least eligible coordinate. The inverse subtracts `subsetExponent d s` from
`t`; exponent bounds, weight, and the inverse identities are proved.
Reindexing gives an equal determinant of the corresponding eligible
principal submatrix, with no exterior-algebra coordinates in its definition.

`FinitePositionMasks` orders a finite coordinate set decreasingly and
identifies its `k`-element subsets with `k`-element position masks.
`KoszulEligiblePositions` applies this to the eligible coordinates with
the pivot erased. It gives a global bijection between actual nonpivot
indices and pairs of an active monomial and a position mask. If `q` is the
number of eligible coordinates of that monomial, its fiber has cardinality
$\binom{q-1}{k+1}$. Every mask of cardinality $k+1$ has a unique greatest
position `j`, and the actual index stratum at that position has cardinality
$\binom{j}{k}$. Writing $h=j+2$ gives the expected $\binom{h-2}{k}$ count.
The full-mask comparison below turns these counts into determinant powers.

`MacaulayEligibleMonotonic` connects the positions to the matrices. A nonzero
entry forces the source remainder to divide the target monomial, preserving
all source eligible coordinates except possibly the pivot. The decreasing
rank of a retained selected coordinate is its number of larger eligible
coordinates, and cannot decrease along such an entry. In a fixed nonempty
exterior subset, the smallest coordinate has the greatest position in the
mask. This proves triangularity and a determinant product by that position.

`MacaulayEligibilityLevels` defines the concrete higher minor at level `h`
on active monomials with at least `h` eligible coordinates. Level one
recovers the active numerator, level two the extraneous minor, and levels
above the arity have determinant one. All levels commute with coefficient
maps and are the identity at coordinate powers. The standard subtractive
shift gives their characteristic pencils and nonzero determinants over a
domain. `MacaulayUniversalExact` proves their universal power specialization
is one and hence their nonvanishing, for every ordering. A greatest-position
stratum at `j` supplies an index of the actual level-$j+2$ minor.

`MacaulayFullPositionMasks` proves monotonicity of every selected coordinate's
decreasing eligible rank along nonzero fixed-subset entries. Equality of the
rank sums forces equality of the full masks. `MatrixWeightBlockProduct`
turns these facts into a determinant product, using a finite tie-breaking
order on labels. All full-mask diagonal factors are concrete principal
submatrices.

`FinitePositionSelection` decodes a mask into any sufficiently long decreasing
coordinate list, with proved inverse identities and omission of the pivot.
`MacaulayMaskedLevelIndices` applies this to a mask of cardinality $k+1$ with
greatest position `j`: its fixed-subset index union is exactly the index set
of the level-$j+2$ eligibility minor. `MacaulayFullMaskComparison` proves the
decoded exterior coordinates are nondecreasing along nonzero entries of
that minor. Decomposing by exterior subsets and reindexing the diagonal
blocks identifies their determinant product with $\operatorname{det}(W_{j+2})$.

`FinitePositionMaskProduct` groups all masks by their unique greatest position.
`MacaulayBinomialFactors` combines the comparison with the mask counts to prove

```
det(Q_k) = det(P_(k+1)) = product_j det(W_(j+2)) ^ choose(j,k).
```

Here `j` ranges over `Fin n`; the level-$n+1$ determinant is one. The result
holds over any commutative ring, including empty blocks, without genericity
or nonvanishing assumptions. The first relation determinant is consequently
the product of all $\operatorname{det}(W_{j+2})$. Ordering comparisons and cancellation of
the extraneous polynomial from the numerator are proved below; resultant
identification remains open.

Write $D_k : V_{k+1} \to V_k$ and $H_k : V_k \to V_{k+1}$.
`KoszulPowerComparison` constructs $F_k = D_k H_k + H_{k-1} D^{\mathrm{power}}_{k-1}$,
with the second term omitted in degree zero. The identity
$D_k F_{k+1} = F_k D^{\mathrm{power}}_k$ is proved as an equality of linear maps
and in canonical row-vector matrices. At coordinate powers `F_k` is the
identity. On the incoming homotopy summand it is also the identity for
arbitrary homogeneous inputs. Its other diagonal block is the existing
nonpivot contraction block, so $\operatorname{det}(F_0)=\operatorname{det}(\mathrm{activeMinor})$ and
$\operatorname{det}(F_{k+1})=\operatorname{det}(Q_k)$ over any commutative ring.

`KoszulPowerComparisonSpecialization` proves that these matrices commute
with coefficient maps and specialize to the identity. Their determinants
are nonzero for systems admitting a coordinate-power specialization. Over
the coefficient fraction field, each actual comparison map is consequently
a linear equivalence. `MacaulayUniversalComparison` instantiates these
equivalences and their chain identity for every universal ordering.

`BinomialParityProducts` balances even and odd binomial sums and products,
including empty products, in any commutative monoid. Applied to the proved
higher determinant factors, `MacaulayAlternatingFactors` gives the polynomial
identity

```
product_(k even) det(Q_k) = det(extraneousMinor) * product_(k odd) det(Q_k).
```

The range is `k : Fin n`. No determinant is divided out in this identity.
`KoszulComparisonRatio` combines it with the comparison determinants:
over a field where these determinants are nonzero, the alternating quotient
of $\operatorname{det}(F_k)$ is exactly $\operatorname{det}(\mathrm{activeMinor})/\operatorname{det}(\mathrm{extraneousMinor})$.
`MacaulayUniversalComparison` proves this identification over the universal
coefficient fraction field and proves that equality of the constructed
ratios for two orderings is equivalent to the required polynomial
cross-comparison. The coordinate transport below proves equality across
orderings; the denominator argument then gives polynomial cancellation.

`IntertwiningDeterminant` now proves the kernel/range determinant comparison.
An intertwining square preserves the connecting map's kernel and range.
Its first-isomorphism equivalence conjugates the induced quotient map to
the range restriction. Mathlib's `LinearMap.det_eq_det_mul_det` consequently
factors the domain determinant into the kernel and range determinants.

`ExactComplexDeterminant` applies this to a chain endomorphism of a finite
exact complex. Exactness identifies each kernel factor with the next
boundary factor. `AlternatingProducts` telescopes the resulting adjacent
products, using only commutative-monoid identities. Surjectivity in degree
zero and a zero terminal space give equal even and odd determinant products.
This theorem does not require the chain endomorphism to be invertible.

`ExactComplexComparison` takes the quotient of two chain comparisons that
are linear equivalences in every degree. It is a chain automorphism of
the exact source complex, so its alternating determinant is one. Thus the
two comparisons have equal alternating determinant ratios.
`ExactComplexTransport` proves that simultaneous conjugation of both
differentials transports a comparison and preserves that ratio, with no
basis-orientation sign.

`KoszulComparisonInvariant` instantiates comparison independence for the
finite weighted coordinate-power complex, including its exactness, initial
surjectivity, and zero piece above arity. Its natural-range determinant
ratio agrees with the existing concrete Macaulay ratio.
`KoszulComparisonTransport` proves equality of the concrete ratios whenever
a graded equivalence intertwines both the input and coordinate-power
differentials. `MacaulayUniversalTransport.cross_of_transport` turns such
a transport into the actual universal polynomial numerator/denominator
cross-comparison; the needed nonzero determinants are supplied by the
proved universal specializations.

`KoszulPolynomialMap` lets an arbitrary polynomial-ring homomorphism act
semilinearly in exterior coordinates. It fixes exterior words and
intertwines the differential after mapping the inputs.
`KoszulExteriorPermutation` supplies the exterior-index action. Their
composition in `KoszulCoordinatePermutation` is an explicit linear
equivalence over the original coefficient ring, sending a monomial word
$(m,v)$ to $(\operatorname{rho}(m),\operatorname{rho}(v))$ and intertwining the renamed input differential.

`KoszulWeightedPermutation` proves that this map preserves total weight
under the corresponding permutation of degree labels. It restricts to
equivalences of the finite weighted pieces, even with different fitting
exponent widths, and intertwines both the input and coordinate-power
differentials. `FixedWidthPermutation` permutes the actual monomial ranks;
reindexing the universal defining sum in `MacaulayUniversalPermutation`
proves that the concrete universal systems, including their fraction-field
versions, transform by exactly this spatial renaming.

`MacaulayUniversalOrdering` applies the transport to prove

```
numerator(pi) * denominator(sigma) = numerator(sigma) * denominator(pi)
```

for every pair of orderings, over any coefficient domain, with fitting
input-degree and Macaulay-level widths. `MacaulayUniversalCancellation`
uses these actual identities and the coefficient-group denominator theorem
to obtain a unique common polynomial quotient over a UFD, normalized to
one at coordinate powers. Its factorization holds for every ordering.

`MacaulayPolynomialCancellation` extends the universal integer factorization
to any commutative coefficient ring and then specializes its coefficients.
For every homogeneous system with positive declared degrees and a fitting
Macaulay width, it proves

```
det(extraneousMinor) divides det(activeMinor).
```

This includes arity zero and needs no domain or UFD assumption on the
specialized ring. Applying it to the subtractive system gives polynomial
divisibility of the characteristic determinants. `TubeMacaulayUniversal`
instantiates that result for the actual tube rows and proves that their
characteristic determinants have a unique polynomial quotient.

Identification of this quotient with the multivariate resultant, its
remaining algorithmic bounds, and the full ETR polynomial-space theorem
remain open.

## The actual characteristic quotient polynomial

`CharacteristicPolynomialQuotient` defines an exact quotient candidate by
monic division over the original coefficient ring:

```
quotientPolynomial(A,E) = (-1)^dim(E) * (det(A-sI) /ₘ charpoly(E)).
```

When the subtractive characteristic determinants divide, this polynomial
factors the numerator exactly. The construction commutes with every
coefficient homomorphism, including noninjective specializations. Over a
domain its degree is $\operatorname{dim}(A)-\operatorname{dim}(E)$ and, when $\operatorname{dim}(E) \le \operatorname{dim}(A)$, its leading
coefficient is the corresponding power of `-1`.

`MacaulayCharacteristicQuotient` applies the proved polynomial cancellation.
The definition needs no homogeneity proofs as data. For homogeneous inputs
of positive declared degrees and a fitting Macaulay width, its factorization
is exact. Over a domain its natural degree is $D = \sum _{i} \prod_{j\ne i} d_{j}$, its leading
coefficient is $(-1)^D$, and multiplying by that sign gives a monic polynomial.
Its degree survives every coefficient specialization to a nontrivial ring.
Its rational-function image is the prior determinant ratio, and its ordinary
trailing degree and coefficient realize the prior signed order and fraction
of trailing coefficients.

`TubeCharacteristicPolynomial` supplies this concrete polynomial for the
actual tube system over `ℤ[θ][T]`. Its degree is the existing positive
`expectedDegree`, its leading coefficient is the dimension sign, and its
rational image is the existing `value`. Every specialization to a nontrivial
ring remains nonzero with exactly that degree; over a field its root multiset
has cardinality at most `expectedDegree`. The prior order is its natural
trailing degree and is therefore nonnegative; the negative-order language
is empty.

`TubeCharacteristicPolynomialSpace` postcomposes the existing signed-order
evaluator with positive-component projection to give a `SpaceFunction` for
the actual polynomial trailing degree. Testing positivity of that index
decides whether its constant coefficient vanishes, in PSPACE under the
existing `TubeBivariate.Data` contracts. All original source-reader and
suspended-child costs are retained. No full polynomial coefficient vector
is constructed by the evaluator.

The full multivariate-resultant common-root characterization and identification
are still unproved. The forward common-root implication is established below;
the converse, that every quotient root comes from a common projective root,
remains open.

`MacaulayUniversalQuotient` chooses the unique normalized universal integer
polynomial and defines its value by coefficient substitution. This value
commutes with every coefficient homomorphism, factors the actual active
determinant, and equals one on coordinate powers. The specialized ring
need not be a domain, and its extraneous determinant may vanish.

`MacaulayQuotientSpecialization` identifies this value on $p_{i}-s\cdot x_{i}^{d_{i}}$
with `characteristicQuotient p d W`. Evaluating at any scalar gives the
universal polynomial value on the corresponding specialized inputs.
In particular, evaluating the characteristic quotient at zero gives the
universal value of the original system. Uniqueness of factorization by a
subtractive characteristic determinant now holds over every commutative
ring, using its monic characteristic polynomial.

`MacaulayQuotientRoots` proves a first case without a nonzero-extraneous
hypothesis. Over any domain, a nonzero common root on the last coordinate
axis annihilates the universal polynomial value. Shift all inputs except
the last by their coordinate powers: this preserves that root, while the
extraneous matrix becomes the full subtractive characteristic matrix,
whose determinant is nonzero. The active determinant vanishes, so the
deformed quotient is zero; coefficient naturality specializes it back at
zero. The characteristic quotient consequently vanishes at every parameter
whose shifted system has such an axis root. A separate helper handles
arbitrary common roots when the extraneous determinant is nonzero.
The following general projective-root theorem subsumes this axis case.

`MacaulayRootModel` constructs a homogeneous system vanishing at a specified
point `x`. For each input degree `dᵢ`, its form is

```
qᵢ = x_last^dᵢ * Xᵢ^dᵢ - xᵢ^dᵢ * X_last^dᵢ.
```

Group extraneous indices by their last exponent. Each correction term
strictly increases that exponent, while the diagonal entry is
$x_{\mathrm{last}}^{d_{\mathrm{pivot}}}$. Hence $x_{\mathrm{last}} \ne 0$ makes the extraneous determinant
nonzero over any domain. No division by a root coordinate is used.

`MacaulayRootDeformation` adds a parameter times this model to the original
system. The common root persists over the polynomial coefficient ring.
The highest matrix-pencil coefficient is the model's nonzero extraneous
determinant, so the deformed extraneous determinant is a nonzero polynomial.
The active determinant vanishes; exact polynomial factorization makes the
deformed quotient zero. Coefficient naturality specializes it back at zero.

`MacaulayQuotientPermutation` proves that simultaneous input and spatial
permutations preserve the universal polynomial value. It transports the
integer quotient through coefficient-variable renaming and cancels only
in the universal integer coefficient domain, before any specialization.
`MacaulayProjectiveRoots.polynomialValue_eq_zero_of_common_root` therefore
handles every nonzero common homogeneous root over any domain, with positive
declared degrees and a fitting Macaulay width. Neither the original nor
specialized extraneous determinant is assumed nonzero. A coefficient-map
corollary handles roots in extension domains. Applied to shifted inputs,
the theorem proves vanishing of the characteristic quotient at the
corresponding parameter.

`TubeCharacteristicRoots` applies this theorem to the actual full tube rows
and the concrete tube quotient polynomial. Every specialized shifted common
root annihilates that polynomial; every common root of the original rows
annihilates its specialized constant coefficient. The converse over
algebraically closed fields is now proved in `TubeCharacteristicCriterion`,
as described below. Identification with the multivariate resultant,
geometric persistence, and the remaining full ETR space obligations remain open.

`ProjectiveNullstellensatz` now gives the qualitative ideal criterion needed
for the converse. Over an algebraically closed field with finitely many
variables, the following conditions on the ideal generated by the inputs
are equivalent: there is no nonzero common root; some power of each
coordinate belongs to the ideal; a power of the variable ideal is contained
in it; every homogeneous form of some degree belongs to it. The proof uses
Mathlib's ordinary Nullstellensatz and finite generation of the variable
ideal. No homogeneity assumption on the input system is needed for these
equivalences, and no bound on the required power is proved.

`HomogeneousIdealMembership` takes homogeneous components of arbitrary
ideal expressions. For homogeneous inputs of degrees `dᵢ` and a target of
degree `t`, it supplies multipliers homogeneous of degree `t-dᵢ`, with zero
multipliers when $t<d_{i}$. Their support degrees satisfy the exact equation
$\operatorname{degree}(m)+d_{i}=t$, giving the existing finite coefficient-reconstruction
contract without a separate multiplier or support assumption.

`MacaulayIdealImage` proves that, over any commutative ring and a fitting
width, a homogeneous form at the Macaulay level belongs to the generated
ideal exactly when its coefficient vector lies in the full rectangular
matrix's row image. Surjectivity of that matrix is therefore equivalent
to ideal membership of every form at that level. Surjectivity excludes
nonzero common roots over every domain. `MacaulayNullstellensatz` connects
the polynomial quotient in the proved direction: a nonzero value excludes
nonzero common roots, and over an algebraically closed field supplies an
ideal-power certificate and homogeneous Bezout expressions at every
sufficiently large degree.

The specific degree $1+\sum _{i}(d_{i}-1)$ is now proved sufficient by the Koszul
acyclicity and weighted projection argument below. The matrix-to-quotient
implication is proved as follows.

`MatrixSelectedMinorCross` replaces selected rows to factor an arbitrary
contraction determinant by the selected multiplication determinant. The
matrix determinant lemma identifies the same determinant with an arbitrary
selector determinant times the complementary relation determinant. The
domain version passes through the coefficient fraction field and injects
the equality back. `MacaulayMinorCross` applies this identity to the actual
division relations. Factoring their determinant as the extraneous factor
times the higher relation factor gives a polynomial cross identity for
every full Macaulay maximal minor.

`MacaulayHigherDenominators` proves that each higher relation factor omits
the last input polynomial: its diagonal relation blocks agree with
extraneous submatrices. The factor specializes to one at coordinate powers.
`MacaulayFullPermutation` transports arbitrary full-matrix row selectors
across simultaneous input and spatial orderings and preserves their maximal
minors. The higher factors therefore form a normalized denominator family
omitting every coefficient group in turn.

`MacaulayMaximalMinors` proves `MacaulayUniversal.integerQuotient_dvd_fullMinor`
using the existing UFD denominator-cancellation theorem on the fraction of a maximal minor by the
normalized integer quotient. The cross identities give each representation,
and the omitted groups force this fraction to be a polynomial. Specializing
the integer coefficient identity proves `polynomialValue_dvd_fullMinor`
over every commutative ring. No specialized extraneous or higher relation
factor is assumed nonzero.

`MatrixMaximalMinorSpan` expands the determinant of a rectangular product
over all full row selectors by multilinearity. Every common divisor of
the maximal minors divides this determinant. A surjective row map has a
matrix right section, whose product determinant is one, so that common
divisor is a unit. `MacaulayQuotientSurjectivity` consequently proves that
full Macaulay row surjectivity makes the polynomial quotient a unit over
any commutative ring, and nonzero over every nontrivial ring. Membership
of every form at the Macaulay level gives the same conclusion through the
proved ideal-image criterion.

`TubeCharacteristicSurjectivity` supplies the concrete tube specialization:
surjectivity of the specialized full row map makes the specialized constant
coefficient of the tube characteristic quotient a unit, without assuming
that the extraneous determinant survives specialization. The sharp bound
and common-root converse over algebraically closed fields are proved below.
Resultant identification, geometric persistence, the remaining algorithmic
bounds, and full ETR polynomial-space membership remain open.

`CoordinatePowerRegularity` supplies the ambient regularity needed for a
homological proof of the sharp degree bound. Multiplication by a power of
an unused variable is injective modulo an ideal generated by powers of
other variables; the proof uses the monomial ideal support criterion.
Powers of distinct variables form a weakly regular sequence over every
commutative coefficient ring, and a regular sequence when the powers are
positive and the coefficient ring is nontrivial.

`ProjectiveRegularSequence` turns coordinate-power membership into an
ambient regular sequence of length equal to the number of variables,
contained in the input ideal. Its powers are made positive by increasing
the exponents by one. The projective Nullstellensatz supplies the needed
coordinate powers from absence of nonzero common roots. These regular
elements are coordinate powers, not the original input forms.

`ProjectiveDepth` proves that positive homogeneous inputs generate a proper
ideal, since they all vanish at zero. Rees' theorem then gives
$\operatorname{Ext}^i(N,P)=0$ for $i<n$, where $P=K[X_{0},\ldots ,X_{n-1}]$, the field is
algebraically closed, the inputs have no nonzero common root, and `N` is
any finite `P`-module supported on the input ideal's zero locus. A concrete
corollary covers $N=P/I$. This is a proved Ext-vanishing certificate, not
an assumption that the input forms constitute a regular sequence.

`KoszulIdealAnnihilator` extends the exterior multiplication homotopy to
every input-ideal element. It proves that the ideal times the kernel of
each positive differential is contained in the range of the incoming
differential: every such scalar multiple of a cycle is an actual boundary.

`FiniteComplexSurjectivity` compares ranks downwards from the zero piece
above the complex length, using rank-nullity and positive-degree exactness.
`KoszulExactSurjectivity` applies this to the actual finite weighted Koszul
complex and the coordinate-power reference. Positive-degree exactness at
the Macaulay level implies degree-zero surjectivity, full rectangular
Macaulay surjectivity, and a unit quotient. No Hilbert-series identity or
new degree-count hypothesis is needed for that step.

`ExtVanishing` extends vanishing into the base ring to every finite free
target: a basis expresses the identity as a finite sum of coordinate
projections and inclusions. It also records the cokernel step of the
covariant long exact Ext sequence. `HomologySupport` proves that Noetherian
chain modules have finite homology and that an ideal sending cycles to
boundaries annihilates homology, hence supports it on the ideal's zero locus.

`FiniteComplexAcyclicity` proves a bounded-complex acyclicity lemma. Descend
from the zero module above the top degree through the differential cokernels.
Once degree $k+1$ is exact, those cokernels give a short exact sequence with
the degree-`k` chain module. Dimension shifting loses one Ext degree at each
step. Positive homology embeds in its cokernel, and vanishing of Hom forces
it to be zero. This uses the actual long exact Ext sequence, without
assuming Koszul regularity of the input forms.

`KoszulProjectiveExact` applies this argument to the polynomial Koszul complex.
There are equally many positive homogeneous inputs and variables over an
algebraically closed field, and their only common root is zero. Exterior
powers are finite free and vanish above the number of variables. Their
finite positive homology is annihilated by the input ideal. The proved
projective depth bound thus supplies all required Ext vanishings, proving
positive exactness in every exterior degree.

`KoszulWeightProjection` retains ambient monomial exterior coordinates with
polynomial degree plus input-degree subset weight equal to a selected value.
It fixes that weighted space, commutes with the homogeneous differential,
and maps each exterior degree into its finite weighted piece.
`KoszulWeightedExact` projects arbitrary polynomial preimages to transfer
positive exactness into every finite weighted complex, over any commutative
ring when polynomial exactness is supplied.

`MacaulayProjectiveCriterion` combines this with the coordinate-power rank
comparison. Absence of nonzero common roots gives full row surjectivity at
$\delta =1+\sum _{i}(d_{i}-1)$, and hence ideal membership of every homogeneous form of degree
`δ`. This is the sharp Macaulay degree bound, with no supplied exactness,
rank, or Hilbert-function assumption. The normalized polynomial quotient is
nonzero exactly when there is no nonzero common root. Equivalently, it is
zero exactly when a nonzero common root exists. The characteristic quotient
at a parameter has the analogous equivalence for the shifted equations.
All converse statements here require an algebraically closed field; root
vanishing in the forward direction remains valid over every domain.

`TubeCharacteristicCriterion` proves both implications for the actual tube
polynomial after any coefficient specialization to an algebraically closed
field. Its value at `s` vanishes exactly when the specialized tube equations
have a nonzero common solution of $p_{i}(x)=s\cdot x_{i}^{d_{i}}$. Its constant coefficient
vanishes exactly when the unshifted equations have a nonzero common root.
No specialized extraneous determinant is assumed nonzero. Identification
with a separately specified multivariate resultant, general geometric
persistence, and the remaining full Canny algorithm and space bounds stay open.

## Regular-point persistence for the actual quotient

The GCP report's Theorem 3.2 (printed page 6) uses algebraic component
dimensions to produce converging deformed solutions on proper components,
including singular points. The current analytic result covers points with
invertible square-system Jacobian. Extending it to the report's general
proper-component statement remains an obligation.

`ImplicitRootPersistence` constructs a continuous local root curve for a
`C¹` equation $f(s,z)=0$ over the reals or complexes when the derivative in
`z` is invertible at $(0,z_{0})$. Applying the existing lowest-coefficient limit
theorem along punctured neighborhoods of zero forces a polynomial's lowest
coefficient to vanish whenever that polynomial vanishes on the constructed
roots. No root curve is supplied as an assumption.

`ParametricPolynomialCalculus` proves smoothness of polynomial evaluation
when both coefficients and variables depend smoothly on the parameter.
`MacaulayRegularPersistence` applies the implicit function theorem to the
explicit equations $p_{i}(x(z))-s\cdot x_{i}(z)^{d_{i}}$. At $s=0$, their derivative in `z`
equals the derivative of the unshifted family. The proved common-root
vanishing theorem applies along the resulting curve, so the normalized
quotient's lowest characteristic coefficient vanishes at the original
parameter. A projective chart keeps the roots nonzero throughout.

`TubeCharacteristicRegularPersistence` supplies the concrete tube instance.
Fix the perturbation value `ε`; the unknowns are the projection parameter
`u` and the spatial coordinates in the chart $x_{0}=1$. All coefficient maps
and coordinate functions are explicit and proved smooth. Invertibility of
the full square-system Jacobian gives a curve $(u(s),y(s))$ through each
such root. Thus the polynomial obtained from the actual quotient's lowest
coefficient by specializing `ε` vanishes at $u(0)$. The Jacobian hypothesis
concerns the entire square system; proving the needed coverage for all
critical points remains open.

`TubeCharacteristicLowestSpecialization` transfers the existing effective
nonvanishing interval from the padded affine deformation to this quotient
coefficient. The lowest full characteristic coefficient equals the lowest
quotient coefficient times the lowest extraneous coefficient. Nonvanishing
of its specialization therefore implies nonvanishing of the quotient
coefficient, without a separate extraneous-value hypothesis. Under the
existing coordinate-bound and direction-reader contracts, the same FP
dyadic exponent supplies an explicit positive real perturbation interval.
Throughout it the projection polynomial is nonzero, and taking the
quotient's lowest coefficient and order commutes with specialization.

`CharacteristicCoefficientDegree` bounds every characteristic coefficient's
parameter degree by matrix size times the entry-degree allowance.
`TubeCharacteristicLowestBounds` applies the projection-entry bound of one.
The lowest quotient coefficient divides the lowest full characteristic
coefficient, so its projection degree, before and after specialization,
is at most the padded Macaulay dimension. In the effective interval, the
set of projection values of affine roots with invertible full-system
Jacobian is finite and has cardinality at most that dimension. This
establishes a bounded nonzero eliminant for those regular roots. Singular
proper-component persistence, a complete sampling argument, and the full
ETR polynomial-space theorem remain open. The finite-fiber algebraic result
below now supplies the missing vanishing at singular points when the affine
fiber is finite over an algebraically closed field.

## Lowest-coefficient vanishing at singular finite-fiber points

An algebraic argument now removes the full-system Jacobian hypothesis for
finite affine fibers. `FiniteZeroLocus` applies the Nullstellensatz to write
the radical of an ideal with finitely many affine zeros as a finite
intersection of point ideals. Every prime above it contains one of those
maximal ideals and is therefore maximal. `MvPolynomialPointHeight` proves
that a point ideal in `n` variables has height `n`, by splitting off one
polynomial variable at a time. The weak Nullstellensatz gives the same
height for every maximal ideal over an algebraically closed field.

`FiniteFiberSaturation` considers `n` equations in $n+1$ affine variables,
with a polynomial parameter whose zero fiber is finite. If that parameter
belonged to a minimal prime of the input ideal, the prime would lie above
the finite fiber and thus be maximal, of height $n+1$. Krull's height theorem
bounds its height by the `n` generators, a contradiction. The parameter
therefore avoids every minimal prime. Its powers can be cancelled in the
radical ideal. This concerns the radical and does not assert flatness of
the possibly nonreduced quotient ring.

`FiniteFiberLowestCoefficient` encodes a polynomial in the deformation
parameter as a multivariate polynomial. If it vanishes on the deformed
system, the Nullstellensatz puts it in the radical input ideal. Factoring
out a deformation power, cancelling it by the preceding theorem, and
evaluating on the zero fiber proves vanishing of the first possibly nonzero
coefficient there. The result applies to singular points; it neither assumes
nor constructs an analytic root family.

`MacaulayFiniteFiber` supplies the actual characteristic quotient. Polynomial
coefficient maps and polynomial projective-coordinate functions describe a
square affine model of the homogeneous inputs. When its affine zero set is
finite over an algebraically closed field and the projective coordinates
are nonzero, the globally selected lowest quotient coefficient vanishes at
every affine root. Its characteristic degree is selected before coefficient
specialization, so no preservation-of-order hypothesis is needed for the
vanishing theorem. Infinite projective components at infinity are allowed.

`TubeCharacteristicFinitePersistence` instantiates this with the compiled
tube rows, fixed perturbation `ε`, projection variable `u`, and chart $x_{0}=1$.
It also embeds real roots in an arbitrary algebraically closed extension of
the reals. Finiteness of the affine system over that extension therefore
gives lowest-coefficient vanishing for every real affine tube root, including
singular roots, with no Jacobian assumption. The coefficient evaluation and
lowest projection-polynomial definitions now work over arbitrary commutative
coefficient rings and are shared with the earlier analytic result.

`TubeCharacteristicFiniteBounds` combines this coverage with the proved
effective nonvanishing interval and projection-degree bound. Under the
existing coordinate-bound and direction-reader contracts, a positive real
perturbation in the certified dyadic interval and affine finiteness over an
algebraically closed extension give a finite set of **all** real projection
values, of cardinality at most the padded Macaulay dimension. Finiteness for
the chosen compiled sampler parameters and directions remains an explicit
hypothesis in this generic theorem. Stored rational packets now discharge
it through the geometric finiteness bridge. Extending beyond finite affine
fibers to remaining proper components, resultant identification, and the full
ETR space proof remain open.

## Compiled tube samples and nonzero eliminants

`TubeRegularSpatialLift` supplies the inverse base derivative required by the
reciprocal equation. At a normalized real projection root, all partials are
proportional to the base partial. If that partial vanished, the entire
hypersurface derivative would vanish, contradicting regularity. This uses
regularity of the hypersurface, with no nonsingularity assumption on the
larger square critical system.

`TubeCompiledAffineLift` adds a projection coordinate equal to the prescribed
integer linear form in the reciprocal and point coordinates. Every spatial
zero gives a compiled affine zero after denominator clearing. The decoding
map recovers the original spatial tuple. `TubeLevelRootLift` applies this
construction to the packet's actual parameter map. A common interval of
regular tube levels works for all active sets and all added linear forms.
Decoding any compiled root recovers the geometric projection equations even
outside that interval.

`TubeLevelSamplingSource.compiled_correct` strengthens the encoded ETR
criterion to actual compiled samples with strictly positive inactive signs.
The packet and active mask are fixed throughout the level interval; every
added integer linear projection has such samples. All compiled affine fibers
are finite over every real extension field.

`TubeLevelSamplingSource.eliminant_correct` adds a nonzero univariate
polynomial obtained from the actual quotient's lowest characteristic
coefficient. Finiteness over the complex numbers makes it vanish at every
compiled real projection value, including values at singular critical points.
The existing dyadic degree/height bound supplies an explicit nonvanishing
threshold, using the stored packet's coordinate bounds and the chosen linear
form's integer values. Each linear form may require its own smaller interval;
no uniform interval over all unbounded integer linear forms is asserted.
The polynomial degree and the number of distinct compiled projection values
are at most the padded Macaulay dimension.

These are exact qualitative ETR criteria on every bitstring. Their sample
conditions retain the compiled equations and positive inactive constraints;
arbitrary eliminant roots are not claimed to be valid samples. Bounds on
suitable parameter bit lengths and levels in the original source size,
effective selection, effective algebraic coordinate recovery and its space bound, and
the complete PSPACE decision procedure remain open.

## Complete decoding of rational-level tube samples

`FiniteSystemCoordinates.exists_solution_lift_of_finite`, in
`FiniteSystemTransfer`, proves that a finite full zero set over an algebraically closed field has no new points after a field
extension. The evaluation kernel of an extension-field solution is prime above
the system ideal. The finite-zero-locus theorem makes it maximal, and the
Nullstellensatz identifies it with a point ideal. Its coordinate equations
force the solution to be the image of that point. Applying this in a common
algebraic closure proves `Representation.complete_of_finite` and
`rootEquivOfFinite` for arbitrary target fields. Unlike the earlier general
transfer theorem, this needs no separate coordinate-algebraicity hypothesis.

`TubeCharacteristicQuotient.map_finiteSystem`, in `TubeFiniteSystemBaseChange`,
proves that coefficient extension commutes with the actual compiled affine system. At a rational level, embed
the algebraic closure of the rationals into the complex numbers. The packet's
finite complex fiber then implies finiteness of the rational system over that
algebraic closure. Existing finite-system representations and denominator
clearing produce a nonzero integer parameter polynomial and integer coordinate
numerator/denominator pairs. The new completeness theorem makes their real
parameter roots correspond to every compiled real point; denominator
nonvanishing at roots is inherited from the representation.

`TubeLevelPacket.exists_compiledSample_iff_integer` transfers the positive
inactive signs to these decoded parameter roots. The theorem
`TubeLevelSamplingSource.coordinates_correct` gives an exact ETR equivalence
using one stored packet and mask, with such samples at every sufficiently small
positive rational level. Only rational levels are needed in the reverse
implication: they supply arbitrarily small real levels for the existing
compactness argument.

The univariate representations may vary with the level and added linear
projection. They are existential representations of the full compiled system,
not identified with the computed quotient's lowest coefficient. The degree
and direction bounds already carried by finite-system representations depend
on the full solution count. Effective construction from the streamed
eliminants, coefficient-height and parameter-size bounds in the original
input, and the full coordinate computation's space bound remain open.

## Integer sign queries for the decoded tube coordinates

`TubeLevelSignQueries` constructs the actual inactive-constraint polynomials
in compiled coordinates. The source equation and its negative, the box
constraints, and their shifts are all multiplied by the stored positive denominator
of the packet's rational epsilon. Subtracting its raw numerator in each box
constraint accounts exactly for that margin. The resulting integer polynomial
evaluates to a positive multiple of the original constraint.

Substituting the integer coordinate numerator/denominator pairs and clearing
with fixed even powers preserves strict positivity at every parameter root. The
representation guarantees that none of those denominators vanish. Active
constraints are replaced by the constant polynomial one, leaving a fixed-size
all-positive pattern over the original finite constraint index. The theorem
`TubeLevelPacket.sampleRootCount_pos_iff` identifies positive root-sign count
with actual compiled sample existence.
`TubeLevelSamplingSource.signCounts_correct` replaces the decoded-root
conditions in the exact ETR criterion with positivity of these finite counts
throughout small positive rational-level intervals.

`TubeLevelSignSpace` instantiates the existing native sign-pattern counter with
these polynomials. Its `Source` records actual packets, rational levels, finite
fibers, and complete coordinate representations. Its `Budget` requires binary
degree and coefficient-mass allowances; the generic access interface requires
native space certificates for parameter/query coefficient residues. FP packet
access derives the polynomially bounded query count from the source arity.
The desired pattern has a constant reader. These contracts give the exact
count evaluator, a sample-existence decider, and PSPACE membership for that
sample language. They do not provide a construction of the representations,
original-input bounds, or the required coefficient readers.

## Derived budgets for the actual sign queries

`RationalSubstitutionWith` proves evaluation, degree, and coefficient-mass
bounds for explicit denominator allowances. The actual tube queries now use
the raw stored margin numerator and positive denominator, avoiding rational
normalization. Their variable degrees are bounded by the existing FP source
allowance `D=8*N^2+4`, independent of the active mask and query row. Every
coordinate denominator is raised to an even clearing allowance `2*D`.
Coefficient extension preserves these chosen allowances even if reduction
kills leading coefficients.

`TubeLevelSignBounds` bounds the integer constraint's source coefficient mass
by `2^(W+N+2*N^2+4)`, with W the stored width and N the normalized compiled
source size. For A compiled coordinates, put `Q=2*A*D`. Coordinate degrees
at most E and masses at most `2^b` give query degree at most `Q*E` and query
mass at most `2^(W+N+2*N^2+4+Q*b)`. Active queries equal one and satisfy the
same bounds. These formulas have FP binary writers, even when E and b are
exponentially large and only their binary descriptions are available.

`TubeLevelSign.CoordinateBudget` therefore constructs the former sign-stage
budget from root/coordinate data. Its native counter and PSPACE theorem need
no separately supplied query degree or mass proof. The coefficient reader
construction below removes the separate expanded sign-query access hypothesis.
Finding suitable coordinate representations with original-input degree,
height, and workspace bounds remains open.

## Native coefficient readers for the actual integer constraints

`TubeSampleCoefficient` computes coefficients of the compact source embedded
in compiled sample coordinates. The first two coordinates are the projection
and reciprocal; original point coordinates start at index two. An FP guard
checks that every exponent outside the point block vanishes. Remaining queries
restrict to that block and invoke the existing native compact-polynomial
reader, including its degree guard and all child workspace. The nonzero
outside-exponent guard prevents restriction from aliasing a zero coefficient
to a nonzero one.

`FixedWidthMonomial` computes constant and variable coefficients by checking
all exponent blocks in FP, including short, redundant, and zero-width words.
`TubeSparseConstraintCoefficient` combines the dense source, its negative,
the two affine box forms, and the shift variables. `ModularResidueSpace`
supplies native space composition of residue addition, negation, multiplication,
and branches. Retained inputs and all original child computations are included.

`TubeConstraintCoefficient` reads the packet's raw margin parts with the proved
FP accessors and computes coefficients of the actual `integerConstraint`.
The public `integerConstraint_coeff` identity expands coefficients at the
polynomial's defining module, avoiding imported multiplication implementation
transparency in the residue proof. `TubeConstraintCoefficientSource` caps
binary row indices before finite decoding. Valid indices preserve their exact
constraint; out-of-range indices select the final row. The complete native
reader needs only FP packet/row/exponent/modulus fields and a unary exponent
block width. It assumes no constraint-coefficient oracle.

## Native substitution and the derived sign-query reader

`TubeConstraintIndexed` streams the complete integer constraint by binary rank.
The exponent block width is `D.size` for `D=8*N^2+4`. The proved degree bound
shows that these blocks cover every supported monomial. Each rank exponent is
less than `2^D.size`, and that power is at most `2*D`, so all terms fit the exact
even clearing allowance used by the actual sign queries.

`TubeConstraintSubstitution` instantiates the generic native rational-substitution
engine with these actual coefficients and FP metadata. Only numerator and
denominator coefficient readers are supplied. Context reindexing preserves
coordinate/degree/modulus fields and includes each original child certificate.
Its polynomial is proved equal to `clearedWith` of the actual integer constraint,
with no change of clearing allowance.

`TubeLevelSignReaders` extends the decoded finite coordinate polynomials by zero
outside their spatial range and supplies substitution contexts containing a binary
constraint row. `TubeLevelSignCoefficient` selects the constant query one on
active rows using FP mask lookup. Other rows run the complete constraint and
substitution children. Binary row decoding is capped on arbitrary inputs; every
valid sign-query row has its exact mathematical coefficient modulo every positive
modulus. Short and redundant binary fields remain total machine inputs.

`TubeLevelSignNative` builds the final sign-pattern access contract internally.
Native root/coordinate coefficient readers, FP packet/mask fields, and
`CoordinateBudget` suffice for sample counting and sample-existence PSPACE
membership. An independent foundation example checks this endpoint directly
against Complexitylib2's PSPACE class. No expanded sign-query coefficient oracle
or separately assumed query degree/mass bounds remain.

Effective construction of suitable coordinate representations and their readers,
with bounds in the original input, and the complete ETR PSPACE theorem remain open.

## Full finite solution counts and source-derived coordinate degrees

`TubeCompiledReprojection` proves that decoding and relifting with a new linear
projection is a bijection between the full compiled affine root sets. The
spatial tail determines the extra parameter uniquely. This includes reciprocal
coordinates and singular roots; no Jacobian condition is used.

`TubeCompiledCardinality` applies the existing lowest quotient eliminant to
each coordinate direction. Each coordinate of the spatial tuple lies among at
most M roots, where `M=(2^W)^A`, A is the compiled coordinate count, and W is the
Macaulay matrix width. The full zero set injects into their Cartesian product,
so it has at most `B=M^(A-1)=(2^W)^(A*(A-1))` distinct solutions. This step
bounds points, rather than only projection values or regular roots.

`TubeLevelCardinality` transfers that bound through the full complex fiber and
an embedding of the rational algebraic closure. `FiniteSystemCardinality`
then bounds every representation's parameter degree by B, its coordinate
numerator/denominator degrees by `B^2+2`, and its separating-direction entries
by `(A+1)*B^4`. Integer clearing preserves the degree bounds.

The common coordinate threshold is effective in the stored packet.
`TubeCoordinateThreshold` proves that every coordinate direction has the same
encoded direction-size sum: one encoded one and A-1 encoded zeros. The existing
specialization exponent depends on this sum, so one fixed FP direction reader
computes a binary exponent for the whole family. This supplies a positive
common nonvanishing interval without a separate threshold oracle.

`TubeLevelDegreeBounds` gives FP binary writers for B and `B^2+2`; their bit
lengths are polynomial because A and W have unary FP controls. `MassBudget`
constructs the former `CoordinateBudget` at positive levels below the proved
threshold. Native sample counting and sample-existence PSPACE membership now
need only coefficient-mass bounds and root/coordinate readers as resource
hypotheses, along with FP packet/mask fields and the small-level condition.
An independent foundation example checks that endpoint against the native class.

Bounds on suitable packet selection, coordinate coefficient heights, effective
coordinate construction/readers, and the full ETR PSPACE theorem remain open.

## Compositional explicit primitive-pair coordinate computation

The existing Canny-specific interfaces required FP original coefficient readers,
even though the generic determinant engines accepted native space-bounded
children. `ShiftCoefficientSpace` and `CannyCoefficientSpace` now expose that
composition through the actual shifted, resultant, first-subresultant, and
piecewise coordinate formulas. Only degree/direction/selection metadata is FP.
The source coefficient children retain their original space certificates and
may take arbitrary time. Direct linear inputs and zero directions keep their
proved branch semantics; original source degrees survive modular degree drops.

`PrimitivePairCoordinates` defines the concrete rational coordinate pair
`(theta*D+c*N)/D`, `-N/D`, where N,D are the piecewise recovery polynomials.
The report's unnormalized resultant is the parameter polynomial. At every
parameter root, D is nonzero under the separating-direction hypothesis and the
formulas recover the unique input root pair. A root equivalence gives both
soundness and completeness. For split separable inputs, the parameter degree is
exactly `d1*d2`, separability is preserved by a separating direction, and a
suitable direction exists with `c <= (d1*d2)^2`. The formulas do not require a
finite Galois ambient field or interpolation of coordinate coefficients.

`CoordinateRecoveryMap` proves injective coefficient-extension identities for
the actual resultant and all recovery branches. `PrimitivePairInteger` thereby
proves correctness of the integer polynomials computed by the machines over a
characteristic-zero splitting field. This bridge preserves exact source degrees;
it does not replace the linear/interior branch conditions by modular degrees.

`PrimitivePairReaders` adapts canonical context/degree/modulus coefficient queries
to the Canny routines. `PrimitivePairSpace` supplies native coefficient machines
for the resultant, denominator, and both coordinate numerators. The left numerator
includes a guarded binary predecessor query for the shifted denominator and
modular multiplication by the direction. All dense children and retained inputs
are included in the bound. `PrimitivePairNested` instantiates a second resultant
with the first computed resultant as its left coefficient child. The product-degree
identity supplies new FP degree metadata; no FP coefficient assumption or explicit
child execution clock is introduced. Independent foundation examples check these
native endpoints, including the nested use.

`PrimitivePairBounds` bounds all three coordinate masses by `2^E`, with
`G=max(1,(d2-1)*d1)` and
`E=coordinateBitBudget(d1,d2,c,H1,H2)+(G+1).size+c.size`, for input coefficient
magnitudes bounded by H1,H2. The numerator degree allowances are G+1 and G,
and the common denominator allowance is G. These arithmetic bounds need no
root or separability hypotheses.

`SeparableResultant` characterizes separability over a characteristic-zero field
by nonvanishing of the integer derivative resultant, for nonzero inputs including
constants. `ResultantSpace` and `SeparableSpace` instantiate the native integer
determinant tester with space-bounded coefficients. Derivative coefficient heights
and the determinant budget are derived from the source degree and height exponent.
`CannyResultantHeightSpace` removes the FP-coefficient restriction from the existing
resultant height writers. `PrimitivePairSeparableSpace` consequently tests the
actual resultant using only the original two coefficient readers and their bounds.

`PrimitivePairSeparation` proves that the unnormalized resultant is nonzero in
every direction for split separable inputs, and that its separability is equivalent
to shear injectivity on the root-pair set. `BoundedChoice` finds a witness with a
binary counter and a binary accumulator, even when the predicate child has no
polynomial time bound. `PrimitivePairSearch` applies it to directions from zero
through `(d1*d2)^2`, proving both native polynomial-space evaluation of the selected
direction and its separating property. `PrimitivePairSelected` prepares the chosen
direction as part of the coefficient query context, so downstream metadata stays
FP without assuming that direction selection is FP.

`SubresultantGCDGeneral` extends GCD recovery to every degree: for a nonzero
right input of smaller degree, principal coefficients below the GCD degree
vanish, the coefficient at that degree is nonzero, and its full coefficient
form is associated to the GCD. The coefficient form includes the terminal order,
where the smaller input divides the larger one; the ordinary strict-index
subresultant definition alone would return zero there. The proof uses the
existing Euclidean subresultant identities. `PolynomialGCDData` descends this
formula to an integer representative of the rational GCD, with exact degree and
the full Sylvester coefficient-height bound.

`PolynomialGCDDegreeSpace` tests principal coefficients for zero by the native
modulus scan and visits the orders in reverse. The last successful order gives
the GCD degree. Its source coefficient readers may take arbitrary time in
polynomial space. `SquarefreePart` proves that `p/gcd(p,p')` is nonzero and
separable for nonzero field polynomials and commutes with field embeddings. In
characteristic zero it preserves the original roots, including roots in
extension fields. `SquarefreePartDegreeSpace` derives native derivative-GCD and
quotient degree writers from the original integer coefficient reader; constant
and zero source inputs are included in the GCD-degree computation.

`CoefficientMinorSpace` extends the principal-minor entry map by selecting a
different first row. Non-strict order bounds cover terminal and empty minors.
`CoefficientFormSpace` supplies all coefficient-form residues, returning zero
above the selected order. `PolynomialGCDCoefficientSpace` prepares the
space-computed GCD degree as part of the query and calls this determinant
reader. `SquarefreeGCDSpace` derives the complete derivative-GCD reader from
the original integer coefficient reader, including constant inputs.

`ScaledPolynomialQuotient` constructs an upper triangular coefficient system
for the high coefficients of `g*h`. Its Cramer determinants give
`g.coeff(d)^(L+1) * h` when `g.natDegree ≤ d` and `h.natDegree ≤ L`.
No inverses occur, and the construction commutes with coefficient maps.
`ScaledPolynomialQuotientSpace` supplies a native modular coefficient evaluator;
each matrix entry calls either the dividend reader, the divisor reader, or zero.
Formal degree bounds are retained under modular degree drops.

`ScaledSquarefree` applies this quotient to the actual integer derivative-GCD
representative. For nonzero input, the resulting integer polynomial is associated
over the rationals to the canonical square-free part. It is nonzero, separable
over every characteristic-zero field, and has exactly the original roots there.
`ScaledSquarefreeSpace` computes its coefficients in native polynomial space,
composing the original reader, derivative, GCD-degree scan, GCD coefficient
determinant, and quotient determinant through prepared contexts.

`ScaledSquarefreeBounds` derives an FP output-height writer independently of the
space-computed GCD degree. If the source degree is m and its coefficient-height
exponent is b, put `n=m-1`, `e=b+m.size`,
`B_G=(m+n).size*(m+n)+(m+n)*e+1`, and
`B_Q=(m+1).size*(m+1)+(m+1)*(B_G+b)+1`.
Every output coefficient has magnitude-bit size at most B_Q. The exact output
degree also has a native polynomial-space evaluator for nonzero source inputs.
Thus the square-free preprocessing step now has coefficient, degree, height,
and root-preservation certificates under the original reader contract.

`ValidatedPolynomialDegree` makes these space-computed degrees usable by exact
FP metadata interfaces. A context stores the original input and a declared
degree; a native space decider checks the declaration. Correct declarations keep
the source polynomial. Incorrect declarations select `X^d-1`, or `1` for `d=0`.
The fallback is separable in characteristic zero and has coefficient magnitudes
at most one, so degree, separability, and height contracts hold on every context.
The coefficient reader branches on that native space decision. No polynomial-time
degree computation is assumed.

`PreprocessedPairReaders` computes and stores the two square-free degrees, then
supplies the existing pair routines with validated polynomials and FP metadata.
`PreparedPolynomialContext` composes a space-computed context with a coefficient
reader. `PreprocessedPair` consequently combines square-free preprocessing,
separating-direction selection, and coefficient readers for the parameter,
both coordinate numerators, and the denominator. Its decoding theorem recovers
roots of the original input polynomials with a nonzero denominator. This covers
two arbitrary nonzero integer inputs with FP degree/height controls and native
space coefficient readers; it does not establish a uniform variable-depth fold.

`PreprocessedPairProperties` proves that the selected parameter is nonzero and
separable over every characteristic-zero field. Its exact degree is the product
of the two square-free degrees and has a native polynomial-space writer. The
original degree product bounds this degree, and its square bounds the direction.
`CannyResultantBudget` proves a monotone coefficient-bit bound in degree,
direction, and input-height upper bounds. `PreprocessedPairBounds` therefore
obtains an FP parameter height from the original input controls, independently
of the space-computed choices. `PolyTimeBinaryNat` exposes native binary-output
arithmetic for these formulas, including binary size; no unary magnitude is
constructed.

`PreprocessedPairCoordinateBounds` similarly bounds all coordinate masses by a
power of two with an FP exponent derived from the original controls. It bounds
all three coordinate degrees by the original degree product plus two. The mass
proof uses the full determinant budget to dominate the interior subresultant
budget and both linear branches, then adds the degree and direction allowances
for the explicit coordinate numerators.

`ValidatedPolynomialReaders` packages any polynomial family with native space
coefficient/degree readers and an FP height into the exact FP metadata interface
on checked contexts. `PreprocessedPairReusable` applies this to the computed
parameter. Correctly prepared contexts retain that exact parameter, and the
preparation itself has a native space certificate. Nonzero and separability
contracts hold even on invalid contexts. The computed pair is consequently a
valid input for subsequent fixed algebraic stages. Uniform evaluation with an
input-dependent nesting depth still needs a separate space proof.

`PrimitivePairConstruction` factors the last-successful bounded direction scan
into a canonical operation on two integer polynomials. `selectedDirection_eq`
proves that the existing native scan computes exactly this operation; its
correctness proof now uses the shared canonical selection theorem.
`SeparableIntegerPolynomial` closes certified square-free integer annihilants
under that operation, with exact product degree. Integer pair completeness
complements the existing soundness theorem. `SeparableIntegerPolynomialField`
commutes the integer evaluation and rational decoding formulas with a field
embedding, then descends soundness and completeness from an algebraic closure.
These results apply to every characteristic-zero field, including the reals.

`BalancedPrimitiveTree` recursively combines pairs at equal height. Its parameter
is an explicit integer polynomial, and its degree equals the product of the leaf
degrees. Recursive rational decoding and shear encoding give a root bijection
with leaf-root tuples. `BalancedPrimitiveCoordinates` and
`BalancedPrimitiveVectors` expose indexed leaf access, tabulation, and extensional
comparison of these tuples.

`FiniteAnnihilatorTree` square-free preprocesses each of n nonzero inputs once,
then pads to width `2^n.size` with X. This width is at most `2*(n+1)`.
Padding with X supplies one zero root per unused coordinate; padding with a
nonzero constant would instead annihilate the Cartesian root product. The
parameter degree is exactly the product of the square-free input degrees and
is at most `D^n` for original degree bound D. `FiniteAnnihilatorEquiv.rootEquiv`
removes the padded coordinates and gives a bijection with vectors of roots of
the original polynomials over any characteristic-zero field. For n=0 the
parameter is X and the root vector is the unique empty vector.

`UnivariateRationalComposition` clears an ordinary polynomial p at a ratio n/d
with an explicit exponent e, giving `d^e*p(n/d)` on evaluation. A coordinate
pair uses the maximum numerator/denominator degree as the same exponent for
both, so composition preserves the ratio. The denominator remains nonzero
when both component denominators are nonzero. Degree grows by at most the
product of coordinate degrees, and mass exponents satisfy `s+e*b` for outer
mass bound `2^s` and inner mass bound `2^b`. The clearing operation commutes
with coefficient maps while retaining e, including modular degree drops.

`SeparableIntegerCoordinates` packages the primitive-pair ratios for this
composition. `BalancedPrimitivePolynomials.flat` constructs flattened integer
coordinates along each branch. They agree with indexed nested decoding, with
nonzero denominators at every parameter root in any characteristic-zero field.
Their degree budget multiplies the pair allowances along the branch; a common
leaf degree bound D gives the bound `(D+2)^(2^(h+1))` at height h.
`FiniteAnnihilatorPolynomials` specializes to the padded family and derives
coordinate degree bound `(D+2)^(4*(n+1))` for original D≥1. It also proves
coordinate recovery at the encoding of every original root vector.

`FiniteAnnihilatorFiltering` substitutes these actual integer polynomials into
multivariate constraints with fixed even clearing allowances. The queries
preserve zero tests over all characteristic-zero fields and signs over ℝ.
Their degrees follow from the coordinate degree bound and the supplied
allowances. Original-polynomial root vectors satisfying all constraints are
equivalent to parameter roots satisfying all cleared queries. If every system
solution satisfies the supplied annihilants, this characterizes solvability
of the original system without an additional root-vector assumption.

`UniformPrimitivePairBounds` and `SeparableIntegerUniformBounds` give a common
polynomial envelope for a pair stage. Input degrees and mass exponents at most
T≥4 give parameter and pair-coordinate mass exponents at most T^10, and pair
coordinate degrees at most T^3. `BalancedPrimitiveMass.UniformBounds` tracks
parameter degree/mass and every flattened coordinate degree/mass together.
Composition and the pair estimates propagate T to T^16, yielding T^(16^h)
at height h. `SquarefreeUniformBounds` includes the determinantal preprocessing
under the same original degree/height controls.

`FiniteAnnihilatorHeight` combines these estimates. Original degrees at most D
and coefficient magnitudes at most 2^b give
`H=(D+b+4)^(256*(n+1)^4)`. Parameter and flattened coordinate masses are at most
2^H, and their degrees are at most H. This bound holds at every node of every
height up to n.size, including arbitrary padded node indices. Cleared constraint
mass exponents follow from the source constraint mass and clearing allowances.
The bound has a native FP binary writer with binary D,b controls and unary n;
the native binary-power theorem handles its polynomial unary exponent.

`FiniteAnnihilatorDegreeSpace` supplies the exact parameter degree in native
polynomial space for an input-dependent family count. Its fold multiplies the
square-free leaf degrees supplied by the existing native degree computation.
The source family is indexed by `pair context (code index)` and its original
coefficient reader may take arbitrary time in polynomial space. A common FP
binary degree bound D and unary count n bound every accumulator by (D+1)^n.
The native fold therefore needs no supplied execution clocks or child time bounds.

`UnivariateRationalSpace` specializes the existing indexed modular substitution
algorithm to one variable, width e, and e+1 terms. Its polynomial is exactly
the univariate clearing sum, including zero width. Original, numerator, and
denominator coefficient routines need only native polynomial space.
`UnivariateRationalSpaceExponent` also permits e to be computed in space:
the input and exponent are stored together, and downstream fields use FP
projections. Every stored exponent defines a valid truncated clearing sum,
so this preparation needs no degree validation. The complete coefficient
routine handles every positive modulus without storing an expanded polynomial.

`IntegerPolynomialDegreeSpace` gives coefficient signs and actual natural
degrees from arbitrary integer residue readers and FP degree/mass bounds.
It includes the zero polynomial. `RationalCoordinateSpace` computes the
maximum numerator/denominator degree by two such scans, then uses the
space-computed exponent in both clearing sums. Its two complete coefficient
readers evaluate the actual common-exponent coordinate composition from four
native space children. Only upper degree/mass controls for the outer coordinate
must be FP; no exact FP degree or polynomial-time child assumption is added.

`RecursiveStack.evaluator` now supplies the uniform native recursion machinery.
One local instruction routine either finishes, continues locally, or saves its
caller and starts a child. One reply installer resumes the saved caller. Both
routines may use arbitrary time in polynomial space. A semantic stack invariant
proves that transitions preserve the requested result. Calls strictly decrease
rank, while local continuations and installed replies decrease a logical fuel
measure. With fuel bounded by N, the active frame has weight
`(fuel+1)*(N+2)^rank`; saved callers have weight `fuel*(N+2)^rank`.
Every running transition strictly decreases their sum. Starting rank at most R
therefore gives the binary FP iteration budget `(N+2)^(R+1)` when N is binary FP
and R is unary FP. This fuel counts logical instructions, independently of the
execution times of the instruction routine and reply installer.

The strictly decreasing ranks also bound stack depth by R. If every valid frame
and semantic answer has encoded length at most B, the complete framed state is
at most `5+4*B+R*(2*B+1)` bits. Polynomial B and unary FP R suffice for the native
iterator's storage contract. The resulting certificate uses one fixed machine
at input-dependent recursion depth, rather than a separate certificate at each
fixed height. Validity may depend on the original input and need not be decidable.

`RecursiveController.evaluator` specializes this to streamed oracle controllers.
Its frames contain only a task and the current controller state. Validity
identifies that state with a prefix of the mathematical oracle run. The least
remaining halting index decreases at every local transition or completed reply;
this measure is proof-only, with no counter in the frame. The stage's logical
budget need not itself be computable when a binary FP common upper bound is
available. Native initialization, request writing, local transitions, reply
installation, and output are charged separately.

`MatrixPowerRecursiveController` gives a concrete stage. Its FP entry-request
test, request writer, and reply installer turn source entries into task calls.
The mathematical oracle run agrees with the existing typed matrix-power run,
halts at `work n e.size e + 1`, and returns the selected power entry whenever
it halts. Every requested row and column is proved to be in range, and the
quadratic encoded state bound transfers without an entry-answer certificate.

`RecursiveMatrixPower.Source.evaluator` now evaluates a ranked graph of these
tasks and base tasks with one uniform native machine. Base tasks may use
arbitrary polynomial space. A non-leaf task's entries are the semantic answers
of its designated lower-rank tasks; their computation certificates are not
assumed. A common unary FP bound M on binary dimension/exponent/modulus lengths
gives the logical budget `2^((M+2)*M+1)`. Common unary FP bounds on task words,
base outputs, and rank give the state/stack bounds internally. This establishes
uniform variable-depth nesting for the concrete matrix-power primitive, not
yet for the complete balanced Canny resultant/square-free/coordinate graph.

`PolynomialPowerRecursiveStage` now exposes the flattened coefficient-matrix
requests as tasks. Its lower-triangular guard routes a query either to an
original coefficient task or a fixed zero task. Correctness, the logical
halting bound, context preservation, and the scalar controller's quadratic
state bound transfer to the polynomial coefficient problem.

`BerkowitzDeterminantRecursiveStage` specializes this to the outer layered
power of the polynomial Berkowitz factors. It requests factor coefficients,
then applies the existing FP parity correction to return the actual determinant
coefficient. No native certificate for factor answers is assumed. The flattened
dimension is `(n+1)^2*(D+1)` and the exponent is n, so the logical stopping index
is `work ((n+1)^2*(D+1)) n.size n + 1`; the state bound depends on their binary
sizes and the modulus size.

`SingleCallController` implements one guarded request followed by FP
postprocessing. `BerkowitzFactorRecursiveStage` uses it for the actual factor
selector: one/zero cases return immediately, diagonal/moment cases request the
corresponding task and negate its reply. Its mathematical run halts after at
most one logical transition, and terminal output agrees with `factorValue`.
All local operations have native certificates from the FP metadata and task
writers, without assuming native diagonal/moment answer certificates. These
are resumable stage contracts. The dispatcher below connects them; uniform
rank/size bounds are still required before obtaining the complete recursive
Canny coefficient evaluator.

`MatrixMomentTaskRouting` now supplies FP source/sink routing to row, column,
matrix, or zero tasks, with a semantic equality to the actual augmented entry.
`PolynomialMomentRecursiveStage` carries the polynomial degree through these
requests and the flattened coefficient-matrix guard. Its oracle run returns
the actual moment coefficient, halts at the specified logical power index, and
inherits the scalar controller's quadratic state bound. `BerkowitzMomentRecursiveStage`
specializes it to trailing-block moments, routing every nonzero request back
to the original matrix coefficient protocol. The total definitions cover
empty trailing blocks and all binary input contexts.

`ControllerDispatch` chooses between resumable controllers with different state
types. Its native certificates retain only a selector flag, the active state,
and fixed defaults for inactive states. The selected oracle transcript, halt,
output, request flag, and query are preserved. A state-length bound charges
both default encodings explicitly, so repeated dispatch among a fixed number
of stages adds only constant factors and constants. Input preparation changes
the initializer while leaving shared task queries intact.

`BerkowitzTaskDispatch` uses these operations to connect determinant, factor,
moment, and supplied source controllers. Two-bit prefixes select the stage;
the empty word supplies zero. The semantic task answers are the actual
determinant coefficient, factor coefficient, moment coefficient, and original
matrix coefficient respectively. The shared controller has native local-operation
certificates from FP metadata/task writers and the supplied source controller's
local certificates. The original coefficient answer function is not assumed
space-computable. Its oracle run is proved to halt at the per-stage budget and
return the semantic task answer, assuming the explicit source-controller
halting/output contract. Halt/output/needs/query observations agree with the
selected stage's transcript.

`BerkowitzTaskStorage` now derives the exact encoding overhead of this dispatch.
If the selected stage state has length at most L, the dispatcher state has
length at most `32+2*L+c`, where c is the encoded source-state default. Each
inactive stage contributes a fixed encoding. A common metadata bit bound M
gives the internal logical budget `2^((M+2)*M+1)`; the overall budget adds a
binary FP common upper bound for the source controller's logical budget.

`BerkowitzTaskOrbitBounds` derives the common stage bound
`L=3*K+4+64*(M+1)^2+V` from task/reply word bound K, determinant/moment metadata
bound M, and source-state bound V. A factor's selected reply is bounded using
query closure at its initial request, rather than an assumption about unused
diagonal or moment answers. The source-state obligation is restricted to actual
source tasks and prefixes within their logical budget.

`BerkowitzTaskSpace.evaluator` applies the uniform recursive native evaluator
to this combined graph. It requires ranked query closure, a common unary FP
rank bound, unary FP K/M/V writers, and a binary FP source-budget upper bound.
The supplied source controller has native local-operation certificates and
explicit oracle-run halting/output correctness contracts. Its answer function
is not assumed to have a native computation certificate. Internal stage bounds
and factor reply bounds are supplied by the new proofs. The resulting native
space certificate covers all tagged task answers at input-dependent depth;
canonical determinant tasks give actual coefficient readers and determinant
coefficient zero testing in native PSPACE. Canny's full source controller and the
rank/reachable-task/common-bound proofs for its concrete graph remain open.

The algebraic filtering theorem still needs specialization to the actual tube
annihilants and constraints. Uniform native coefficient evaluation at
input-dependent depth remains open. The recursion theorem still needs concrete
coefficient frames, instruction/reply routines, and proofs of semantic, progress,
and size contracts for the actual Canny stages. Per-node composition alone does
not supply these contracts. The current exact
finite-system representations still have a qualitative construction; their
source-size heights, native readers, effective parameter selection, and the
full ETR PSPACE theorem are not established.

## TM2 versus Complexitylib's machines

The current project uses Complexitylib2's tidy multitape calculus.
SpaceDecider.precompose combines a native space certificate with native
polynomial-time input preparation. Closure under preimages and many-one
reductions follows directly, and existsReal_subset_PSPACE_iff gives
$\exists \mathbb{R} \subseteq \mathrm{PSPACE} \iff \mathrm{ETR} \in \mathrm{PSPACE}$.
The ETR algorithm proof remains open. The custom-machine simulation and
execution-clock interfaces from the earlier Complexitylib foundation have
been removed. The comparison below describes the machine models evaluated
before this migration.

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
  bounded states, and a bounded terminating run (at most $2^{\mathrm{poly}}$ steps). There are
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

The benchmark is a symbolic-arithmetic routine with encoded inputs,
encoded intermediate states, and a workspace proof through the chosen iteration
interface. The checked Complexitylib2 experiment composes a bounded modular scan
with an explicitly exponential-time child and also instantiates a generic typed
fold. Its child certificate requires only polynomial space; the native iteration
and composition rules hide child execution times.

The main development now uses this foundation throughout its space proofs.
SpaceFunction is a proof-only wrapper around Complexitylib2's
ComputableTidilyInPolySpace, and SpaceDecider carries membership in its native
PSPACE class. Sequential composition, pairing, branches, binary folds, universal
scans, sum/product bits, matrix powers, and Berkowitz all compose these native
certificates. The suspended scheduler and windowed-machine representation are
removed. Mathematical recursion controllers retain their correctness, abstract
step bounds, and encoded-state invariants; they no longer describe the physical
execution of nested children.

P, the defining reductions for ExistsReal, all normalization/compiler
reductions, and PSPACE reduction closure now use Complexitylib2 directly.
FP primitives now also use native tidy time certificates. Local tree, pair,
and binary codecs preserve the existing wire formats; no Complexitylib package,
FP machine bridge, or legacy compatibility patch remains. All project P,
reductions, and PSPACE statements use Complexitylib2 directly. No TM2 simulation
or equivalence with the trominoes predicate is assumed.

The advantage is the compositional interface: child computations may use
polynomial space and arbitrary time without contributing initialization,
transition, first-halt, or execution-clock fields to each enclosing proof.
The existing slow-child prototype tests that distinction. The retained state-size
and semantic invariants remain necessary; a smaller dependency alone would not
justify the switch.

Local comparison sources, at `lean-trominoes` commit
`6fe52dd234bb616fd4fb3c1e7b0a203de1482bc5`:

* `../lean-trominoes/LeanTrominoes/Complexity/Complexity.lean`
* `../lean-trominoes/LeanTrominoes/Computation/Partrec/PartrecPreparedEvaluatorSpace.lean`
* `../lean-trominoes/LeanTrominoes/Computation/Partrec/PartrecGenericSavitchReachSpace.lean`

The current `lean-wang` main branch inspected earlier did not itself define PSPACE;
the relevant Mathlib-only package was found in `lean-trominoes`.

## Internal task ranks from source-context levels

`BerkowitzTaskRouting` proves that the actual internal query words follow
determinant → factor → moment → source, with diagonal and zero shortcuts.
The decoded original matrix context is preserved by every nonzero internal
request. The proofs cover arbitrary task words and child replies; they do not
assume a certificate computing child answers or their correctness.

`BerkowitzTaskLevels` assigns zero rank to zero tasks and rank
`5 * level (origin q) + priority q` to the other tasks. `SourceLevels` asks
only that a source controller's nonzero requests strictly decrease the context
level. Together with query closure, this yields the full mixed-stage ranked
query contract. A common unary FP context-level bound H yields the native rank
bound `5*H+4`; the level function itself remains proof data.
`evaluator_of_source_levels` supplies uniform native polynomial-space evaluation
from these simpler contracts and the existing common word, reply, metadata,
source-budget, and source-state bounds. Canny's full source controller and
these graph-bound instantiations still need to be constructed. This result
does not establish ETR membership in PSPACE.

## A concrete resultant-entry source controller

`SylvesterPolynomialTaskRouting` exposes the selected coefficient input and
the binary band guards of the existing polynomial Sylvester accessor. The
coefficient request preserves its modular context and requested output degree.
`ShiftCoefficientRecursiveStage` suspends only for the original coefficient
of `p(θ-c*x)`: native polynomial-space postprocessing computes the binomial
factor and the modular power and products. `SingleCall.Program.certificates_of_space`
allows this local postprocessing to take arbitrary time without exposing its
execution clock or a suspended binomial controller.

`CannyResultantRecursiveStage` combines these operations into the actual
source controller for a Canny resultant determinant entry. The Sylvester
band guards and the constant-right coefficient guard return zero immediately.
The other cases request one original left or right coefficient and return the
specified Sylvester entry. The proof uses the specified integer source degrees,
so it remains valid after modular degree drops and on all binary query words.
Its local certificate needs FP metadata and task writers, with no computation
certificate for either original-coefficient answer function.

`CannyResultantTaskSource` connects this controller to the mixed determinant
graph. The logical source budget is one transition even though its local
binomial postprocessing may take exponential time. Query closure bounds the
sole stored reply, giving source-state length at most `3*K+4` under common
task/reply bound K. Pointwise decreases for the two actual original-polynomial
task writers imply `SourceLevels`. The uniform evaluator then returns Canny
resultant coefficient residues from explicit child-task semantic identities,
query closure, context-level decreases, and common task/reply/metadata bounds.
The square-free leaf extension below supplies a base branch. The complete balanced-parameter
semantic and quantitative graph contracts remain open. This conditional reader
does not establish the complete Canny coefficient graph or ETR in PSPACE.

## Square-free leaves in the recursive determinant family

`SquarefreeLeafMatrix` places the existing scaled square-free polynomial in a
one-by-one matrix. It proves the entry protocol, native coefficient access,
and equality of determinant coefficients with the certified square-free
reader. Arbitrary coefficient degrees are allowed; the leaf matrix dimension
is always one. Original leaf degree/height metadata and original coefficient
readers come from `SeparableBits.Readers`.

`BerkowitzPolynomialBranch` selects a complete determinant family by its
original context, including dimension, modulus, degree, matrix, and coefficient
access. `SingleCall.Program.withLeaf` uses an FP leaf selector and a native
space-bounded immediate output. Leaves request no child and introduce no extra
state or execution-clock field. Internal nodes retain their original query
and reply postprocessing.

`CannySquarefreeLeaves` instantiates both constructions with square-free leaf
matrices and the actual Canny resultant Sylvester matrices. The source's value
agrees with the mixed matrix entry protocol. Native local certificates include
square-free preprocessing and binomial postprocessing; internal original
coefficient answers need no computation certificate. Only nonleaf requests
require child-context level decreases. `BerkowitzSingleCallSource` derives the
logical budget one and source-state bound `3*K+4` from query closure and the
common task/reply bound K, for this and the earlier pure-resultant source.
The earlier resultant evaluator now reuses these proofs.

One uniform native machine evaluates the mixed determinant family under the
stated child-task semantic identities, context-level decreases, query closure,
and common metadata/task/reply bounds. Coefficient semantic identities for the actual tree,
prepared degree and direction metadata, quantitative graph contracts, and
specialization to the tube annihilators remain open. This is a conditional
mixed-stage reader, not the complete ETR PSPACE theorem.

## Concrete balanced-tree contexts and task ranks

`BalancedParameterContext` stores the original input, unary remaining height,
and a binary node index. FP child writers implement `(h,i) → (h-1,2*i+b)`.
The height decreases on every nonleaf step, including malformed words. On
paired node contexts the complete child address strictly shrinks: dropping a
height bit saves two encoded bits while the index grows by at most one.
The packet decoder agrees with `BalancedPrimitiveTree.node`, its children
agree with the algebraic combine operation, and the height `count.size`, index
zero root agrees with `FiniteAnnihilatorTree.parameter`. Root preparation is
FP from a binary FP count writer.

`CannyBalancedTaskRouting` uses matrix context
`pair (pair node degree) modulusPredecessor`. An original-coefficient request
produces a determinant task with the child address and new coefficient degree,
retaining the modulus. It replaces the parent address/degree rather than
nesting its matrix indices. The exact task length is
`4*child.length + 2*degree.length + modulusPredecessor.length + 8`.
The concrete height-zero leaf selector and these writers discharge all
`SourceLevels` obligations for the mixed square-free-leaf/resultant controller.
These routing/rank proofs use no child semantic or computation certificate.

`BerkowitzTaskReachability` defines the actual query-reachable task graph from
active oracle prefixes within the logical budgets. Closure follows directly;
ranked queries bound every reachable rank by its root rank.
`CannyBalancedTaskRanks` combines these results with the unary address height
and internal priorities. Every reachable task has rank at most
`5*root.length+4`, and its context level is at most `root.length`, on every
input word. These are native unary FP bounds. The uniform native evaluator
now derives reachability closure, source-level decreases, and rank bounds.
Its remaining graph hypotheses are the child coefficient semantic identities
and common word, reply, and binary-metadata bit bounds. Correctly prepared
degree/direction metadata, those quantitative contracts, and the tube-source
specialization remain open; ETR in PSPACE is not yet proved.

## Supplied Sylvester orders and total metadata

`cannyResultantWithDegrees` defines the shifted Sylvester determinant at two
supplied natural orders, without assuming they equal the source degrees.
Exact source degrees recover `cannyResultant`. The modular coefficient family
`Family.modularWithDegrees` agrees with the integer residue function
`Family.specifiedValue` at every supplied order, including modular degree
drops. Pointwise exact-order hypotheses recover the ordinary residue function.

`CannyResultantBits.Access` now takes optional order parameters, defaulting to
the actual source degrees. Its encoded order fields represent those parameters.
`withDegreeCodes` replaces them by normalized raw code writers, decoding the
new orders on every word. Its native metadata certificate needs only those
new writers and the retained direction/output-degree writers; it does not
certify the discarded old degree writers or any original-coefficient answer.
Incorrect degree codes still define their specified-order Sylvester determinant.
They do not assert equality with the ordinary Canny resultant.

The native streamed reader, one-request resultant source, square-free leaf
extension, concrete child routing, and common reachable rank bound all
generalize to the supplied-order parameters. They reuse the existing proofs;
the exact-degree readers, integer height consequences, coordinate readers,
and reductions retain their default exact-order interfaces. This removes the
global degree-consistency requirement from table-driven coefficient evaluation.
The actual encoded table access/preparation, its correctness for the intended
balanced polynomial tree, separating-direction selection, quantitative graph
bounds, and final ETR PSPACE theorem remain open.

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
  proves $\mathrm{NPSPACE} \subseteq \mathrm{PSPACE}$ and equality of the two polynomial-space classes. Its
  public statement explicitly does not provide the general quantitative theorem
  $\mathrm{NSPACE}(S) \subseteq \mathrm{DSPACE}(S^{2})$.
* `lean-trominoes` has a generic Savitch evaluator, reachability correctness, encoded
  search-state bounds, and workspace certificates. Its generic leaf interface accepts
  an evaluator-space certificate for adjacency, not only a polynomial-time test.

Neither result automatically transports algorithms or class membership across the
two machine models.
