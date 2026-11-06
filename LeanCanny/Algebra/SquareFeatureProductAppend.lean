/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SquareFeaturePackedReader
public import LeanCanny.Algebra.FixedWidthRowReboxSpace
/-! # Appending two streamed feature families without expanding their product

The first family's indices are retained. The second family's variables are
cast along the given arity equality; unused ordinals denote zero. Coefficient
reads rebox each old input width with a guard and retain the caller modulus.
-/
@[expose] public section
namespace LeanCanny.Algebra.SquareFeatureProductAppend
open LeanCanny.Encoding LeanCanny.Computation MvPolynomial MatrixPower FixedWidthPolynomial
open SquareFeatureProductFamily
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (F G :Family) (h :∀c,G.arity c=F.arity c)
noncomputable def bounded (P :Family) (c :List Bool) (i :ℕ) :MvPolynomial (Fin (P.arity c)) ℤ :=
  if i<P.count c then P.feature c i else 0
private theorem bounded_degree (P :Family) (c :List Bool) (i :ℕ) :
    (bounded P c i).totalDegree≤P.degree c :=by
  unfold bounded
  split_ifs with hi
  · exact P.feature_degree c i hi
  · simp
private theorem bounded_mass (P :Family) (c :List Bool) (i :ℕ) :
    MvMass.mass (bounded P c i)≤2^P.mass c :=by
  unfold bounded
  split_ifs with hi
  · exact P.feature_mass c i hi
  · simp
noncomputable def feature (c :List Bool) (i :ℕ) :MvPolynomial (Fin (F.arity c)) ℤ :=
  if i<F.count c then bounded F c i
  else rename (Fin.cast (h c)) (bounded G c (i-F.count c))
noncomputable def family :Family where
  arity:=F.arity
  count c:=F.count c+G.count c
  degree c:=max (F.degree c) (G.degree c)
  mass c:=max (F.mass c) (G.mass c)
  feature:=feature F G h
  feature_degree c i _:=by
    unfold feature
    split_ifs
    · exact (bounded_degree F c i).trans (le_max_left _ _)
    · exact ((totalDegree_rename_le _ _).trans (bounded_degree G c _)).trans (le_max_right _ _)
  feature_mass c i _:=by
    unfold feature
    split_ifs
    · exact (bounded_mass F c i).trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
    · exact ((MvMass.rename_le _ _).trans (bounded_mass G c _)).trans
        (Nat.pow_le_pow_right (by decide) (le_max_right _ _))

theorem feature_left (c :List Bool) (i :ℕ) (hi :i<F.count c) :
    (family F G h).feature c i=F.feature c i :=by
  simp only [family,feature,hi,ite_true,bounded]
theorem feature_right (c :List Bool) (i :ℕ) (hi :i<G.count c) :
    (family F G h).feature c (F.count c+i)=rename (Fin.cast (h c)) (G.feature c i) :=by
  have H :¬F.count c+i<F.count c:=by omega
  simp only [family,feature,H,ite_false,Nat.add_sub_cancel_left,bounded,hi,ite_true]

def original :=SquareFeaturePackedReader.parent
def index :=SquareFeaturePackedReader.index
def target :=SquareFeaturePackedReader.target
noncomputable def rowArity (q :List Bool) :=F.arity (original q)
noncomputable def rowWidth (q :List Bool) :=inputWidth (family F G h) (original q)
noncomputable def rowPolynomial (q :List Bool) :=feature F G h (original q) (index q)
noncomputable def coefficient :=FixedWidthRowBits.value (rowArity F) (rowWidth F G h)
  (rowPolynomial F G h) target pairSnd

private theorem max_binary {f g :List Bool→ℕ} (hf :BinaryFn f) (hg :BinaryFn g) :
    BinaryFn (fun c=>max (f c) (g c)) :=(BinaryFn.ite (hf.le hg) hg hf).of_eq (fun _=>Nat.max_def.symm)
theorem degree_binary (A :Access F) (B :Access G) :BinaryFn (family F G h).degree :=max_binary A.degree B.degree
theorem mass_binary (A :Access F) (B :Access G) :BinaryFn (family F G h).mass :=max_binary A.mass B.mass

private theorem wide_evaluator (P :Family) (A :Access P) (W :List Bool→ℕ) (hW :UnaryFn W) :
    SpaceFunction (FixedWidthRowBits.value (SquareFeaturePackedReader.rowArity P)
      (fun q=>W (original q)) (SquareFeaturePackedReader.rowPolynomial P) target pairSnd) :=by
  let C:=SquareFeaturePackedReader.rowArity P
  let U:=SquareFeaturePackedReader.rowInputWidth P
  let V:=fun q=>W (original q)
  have hC :UnaryFn C:=A.arity.comp SquareFeaturePackedReader.parent_FP
  have hU :UnaryFn U:=(inputWidth_unary P A).comp SquareFeaturePackedReader.parent_FP
  have hV :UnaryFn V:=hW.comp SquareFeaturePackedReader.parent_FP
  have ht :target∈FP:=SquareFeaturePackedReader.target_FP
  have HR:=FixedWidthQuery.repack_mem_FP hC hV hC hU ht
  have E:=SquareFeaturePackedReader.row_evaluator P A (FixedWidthQuery.repack C V C U target) pairSnd HR pairSnd_mem_FP
  apply FixedWidthRowReboxBits.evaluator C U V target (SquareFeaturePackedReader.rowPolynomial P) pairSnd
    hC hU hV ht _ E
  intro q
  exact (SquareFeaturePackedReader.masked_degree P _).trans_lt
    ((Nat.lt_succ_self _).trans (Nat.lt_size_self _))

noncomputable def shift (q :List Bool) :=pair (pair
  (pair (original q) (BinaryNatCode.encode (index q-F.count (original q)))) (target q)) (pairSnd q)
theorem shift_FP (A :Access F) :shift F∈FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_pair SquareFeaturePackedReader.parent_FP
    (SquareFeaturePackedReader.index_binary.sub (A.count.comp SquareFeaturePackedReader.parent_FP)).bits_mem_FP)
    SquareFeaturePackedReader.target_FP) pairSnd_mem_FP

private theorem cast_coefficient {a b :ℕ} (ha :a=b) (p :MvPolynomial (Fin a) ℤ) (W r :ℕ) :
    (rename (Fin.cast ha) p).coeff (nativeExponent (Equiv.refl (Fin b)) W r)=
      p.coeff (nativeExponent (Equiv.refl (Fin a)) W r) :=by
  subst b
  simp only [Fin.cast_refl,MvPolynomial.rename_id,AlgHom.id_apply]

noncomputable def read (P :Family) :=FixedWidthRowBits.value (SquareFeaturePackedReader.rowArity P)
  (fun q=>inputWidth (family F G h) (original q)) (SquareFeaturePackedReader.rowPolynomial P) target pairSnd

private noncomputable def native (P :Family) (c :List Bool) (i :ℕ) (bits modulus :List Bool) :=
  residueBits (((bounded P c i).coeff (nativeExponent (Equiv.refl (Fin (P.arity c)))
    (inputWidth (family F G h) c) (Nat.fromBitsLE bits)):ℤ):ZMod (Nat.fromBitsLE modulus+1))
private theorem read_eq (P :Family) (q :List Bool) :read F G h P q=
    native F G h P (original q) (index q) (target q) (pairSnd q) :=rfl
attribute [local irreducible] native
private theorem read_shift (q :List Bool) :read F G h G (shift F q)=
    native F G h G (original q) (index q-F.count (original q)) (target q) (pairSnd q) :=by
  rw [read_eq]
  have HO :original (shift F q)=original q :=by
    simp only [original,SquareFeaturePackedReader.parent,SquareFeaturePackedReader.sourceKey,shift,
      RationalSubstitution.IntegerBits.context,pairFst_pair]
  have HI :index (shift F q)=index q-F.count (original q) :=by
    simp only [index,SquareFeaturePackedReader.index,SquareFeaturePackedReader.sourceKey,shift,
      RationalSubstitution.IntegerBits.context,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HT :target (shift F q)=target q :=by
    simp only [target,SquareFeaturePackedReader.target,RationalSubstitution.IntegerBits.selectedDegree,
      shift,pairFst_pair,pairSnd_pair]
  have HM :pairSnd (shift F q)=pairSnd q :=by simp only [shift,pairSnd_pair]
  rw [HO,HI,HT,HM]


private theorem coefficient_cases (q :List Bool) :coefficient F G h q=
    if index q<F.count (original q) then read F G h F q else read F G h G (shift F q) :=by
  by_cases H :index q<F.count (original q)
  · rw [ite_eq_left H,read_eq]
    unfold coefficient FixedWidthRowBits.value rowArity rowWidth rowPolynomial
    rw [feature,ite_eq_left H]
    unfold native
    rfl
  · rw [ite_eq_right H,read_shift]
    unfold coefficient FixedWidthRowBits.value rowArity rowWidth rowPolynomial
    rw [feature,ite_eq_right H,cast_coefficient]
    unfold native
    rfl

theorem coefficient_evaluator (A :Access F) (B :Access G) :SpaceFunction (coefficient F G h) :=by
  have HW :UnaryFn (inputWidth (family F G h)):=
    (UnaryFn.length ((degree_binary F G h A B).add (BinaryFn.const 1)).bits_mem_FP).of_eq
      (fun _=>BinaryNatCode.length_encode _)
  have EL :SpaceFunction (read F G h F):=wide_evaluator F A _ HW
  have ER :SpaceFunction (read F G h G):=wide_evaluator G B _ HW
  have HP :FPPred (fun q=>index q<F.count (original q)):=
    SquareFeaturePackedReader.index_binary.lt (A.count.comp SquareFeaturePackedReader.parent_FP)
  have E:=SpaceFunction.branch (fun q=>decide (index q<F.count (original q))) HP.flag_mem_FP
    EL (ER.precompose (shift F) (shift_FP F A))
  exact E.congr (funext fun q=>by
    simp only [decide_eq_true_eq]
    exact (coefficient_cases F G h q).symm)

noncomputable def access (A :Access F) (B :Access G) :Access (family F G h) where
  arity:=A.arity
  count:=A.count.add B.count
  degree:=degree_binary F G h A B
  mass:=mass_binary F G h A B
  coefficient:=coefficient F G h
  evaluator:=coefficient_evaluator F G h A B
  packet c i _ bits modulus:=by
    let V (c :List Bool) (i r m :ℕ):=residueBits
      (((feature F G h c i).coeff (nativeExponent (Equiv.refl _) (inputWidth (family F G h) c) r):ℤ):ZMod (m+1))
    change V (original (pair (pair (pair c (BinaryNatCode.encode i)) bits) modulus))
      (index (pair (pair (pair c (BinaryNatCode.encode i)) bits) modulus))
      (Nat.fromBitsLE (target (pair (pair (pair c (BinaryNatCode.encode i)) bits) modulus)))
      (Nat.fromBitsLE (pairSnd (pair (pair (pair c (BinaryNatCode.encode i)) bits) modulus)))=
      V c i (Nat.fromBitsLE bits) (Nat.fromBitsLE modulus)
    congr 1 <;> simp only [original,index,target,SquareFeaturePackedReader.parent,SquareFeaturePackedReader.index,
      SquareFeaturePackedReader.sourceKey,SquareFeaturePackedReader.target,RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

end LeanCanny.Algebra.SquareFeatureProductAppend
