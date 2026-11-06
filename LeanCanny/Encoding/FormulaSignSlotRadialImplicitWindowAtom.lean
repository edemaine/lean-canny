/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitSourceTest
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitGridTest
public import LeanCanny.Encoding.FormulaSignSlotRadialBoundCenterSource
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiDecisionReadback
/-! # Streamed window signs at the same implicit sampler word

All window atoms use that word's unchanged radius and center columns.
The source reader is constructed from the actual raw source reader.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitWindowAtom
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity MvPolynomial
open IntegralFramedBankPolynomialModel (Source Access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F"=>FormulaSignSlotRadialJointStratumSampler.input

def sample (z:List Bool):=pairFst z
def context (z:List Bool):=pairFst (sample z)
def atomBase (q:List Bool):=pairFst (pairFst q)
def rebase (c z:List Bool):=pair (pair c (pairSnd (sample z))) (pairSnd z)
variable (Raw:Source) (N:List Bool→ℕ) (HD:∀c,Raw.arity c=N c+1)
  (rawContext:List Bool→List Bool)
  (hN:∀z,N (rawContext z)=FormulaSignSlotRadialJointLayout.centerCount
    (FormulaSignSlotRadialImplicitGridTest.header (context z)))
  (hfit:∀c,Raw.degree c<2^Raw.width c)
local notation "G"=>IntegralPolynomialWindowTarski.source Raw N HD

noncomputable def hostRaw (v:List Bool):=rawContext (rebase (pairFst v) (atomBase (pairSnd v)))
noncomputable def window (v:List Bool):=pair (hostRaw rawContext v) (pairSnd (pairFst (pairSnd v)))
noncomputable def read (v:List Bool):=pair (pairFst (pairSnd (pairSnd v)))
  (pair (window rawContext v) (pairSnd (pairSnd (pairSnd v))))
def sourceHeader (v:List Bool):=FormulaSignSlotRadialImplicitGridTest.header (pairFst v)

theorem hostRaw_FP (hr:rawContext∈FP):hostRaw rawContext∈FP:=mem_FP_comp
  (show (fun v=>rebase (pairFst v) (atomBase (pairSnd v)))∈FP by polytime [rebase,sample,atomBase]) hr
theorem read_FP (hr:rawContext∈FP):read rawContext∈FP:=mem_FP_pair (by polytime)
  (mem_FP_pair (mem_FP_pair (hostRaw_FP rawContext hr) (by polytime)) (by polytime))
theorem sourceHeader_FP:sourceHeader∈FP:=mem_FP_comp pairFst_mem_FP FormulaSignSlotRadialImplicitGridTest.header_FP

private theorem read_original (v:List Bool):
    IntegralPolynomialWindowTarski.original (IntegralPolynomialWindowTarski.control (read rawContext v))=
      hostRaw rawContext v:=by
  simp only [IntegralPolynomialWindowTarski.original,FormulaSignSlotRadialRadiusTarskiFamily.original,
    IntegralPolynomialWindowTarski.control,read,window,pairFst_pair,pairSnd_pair]
include hN in
theorem source_dimension (v:List Bool):(G).arity (read rawContext v)=
    FormulaSignSlotRadialJointLayout.centerCount (sourceHeader v)+1:=by
  change N (IntegralPolynomialWindowTarski.original (IntegralPolynomialWindowTarski.control (read rawContext v)))+1=_
  rw [read_original]
  change N (rawContext (rebase (pairFst v) (atomBase (pairSnd v))))+1=_
  rw [hN]
  simp only [context,sample,rebase,pairFst_pair,sourceHeader]
theorem window_fit (v:List Bool):(G).degree (read rawContext v)<2^(G).width (read rawContext v):=
  IntegralPolynomialWindowTarski.degree_fit Raw N HD _
noncomputable def source:=FormulaSignSlotRadialBoundCenterSource.source G (read rawContext) sourceHeader
  (source_dimension Raw N HD rawContext hN) (window_fit Raw N HD rawContext)
noncomputable def access (A:Access Raw) (hNU:UnaryFn N) (hr:rawContext∈FP):Access (source Raw N HD rawContext hN):=
  FormulaSignSlotRadialBoundCenterSource.access G (read rawContext) sourceHeader
    (source_dimension Raw N HD rawContext hN) (window_fit Raw N HD rawContext)
    (IntegralPolynomialWindowTarski.sourceAccess Raw N HD A hNU hfit) (read_FP rawContext hr) sourceHeader_FP

theorem source_count (v:List Bool):(source Raw N HD rawContext hN).arity (id v)+1=(F).count (pairFst v):=by
  change FormulaSignSlotRadialJointLayout.dimension (sourceHeader (id v))+1=
    FormulaSignSlotRadialJointLayout.dimension (FormulaSignSlotRadialImplicitGridTest.header (pairFst v))+1
  rfl
theorem source_fit (v:List Bool):(source Raw N HD rawContext hN).degree v<
    2^(source Raw N HD rawContext hN).width v:=window_fit Raw N HD rawContext v
noncomputable def value:=FormulaSignSlotRadialImplicitSourceTest.value
  (source Raw N HD rawContext hN) id (source_count Raw N HD rawContext hN) (source_fit Raw N HD rawContext hN)
noncomputable def env:=FormulaSignSlotRadialImplicitSourceTest.env
include hfit in
theorem evaluator (A:Access Raw) (hNU:UnaryFn N) (hr:rawContext∈FP):SpaceFunction (value Raw N HD rawContext hN):=
  FormulaSignSlotRadialImplicitSourceTest.evaluator (source Raw N HD rawContext hN) id
    (source_count Raw N HD rawContext hN) (source_fit Raw N HD rawContext hN) id_mem_FP
    (access Raw N HD rawContext hN hfit A hNU hr)

def atomQuery (q:List Bool):=pair (sample (atomBase q)) q
theorem atomQuery_FP:atomQuery∈FP:=mem_FP_pair (by polytime [sample,atomBase]) id_mem_FP
noncomputable def atom:=value Raw N HD rawContext hN∘atomQuery
include hfit in
theorem atom_evaluator (A:Access Raw) (hNU:UnaryFn N) (hr:rawContext∈FP):SpaceFunction (atom Raw N HD rawContext hN):=
  (evaluator Raw N HD rawContext hN hfit A hNU hr).precompose atomQuery atomQuery_FP

private noncomputable def rawValue (q:List Bool) (v:ℕ→ℝ):ℝ:=
  ((G).polynomial q).eval₂ (Int.castRingHom ℝ) (fun i=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val))
private theorem embedded_read (q:List Bool) (v:ℕ→ℝ):
    ((source Raw N HD rawContext hN).polynomial q).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      rawValue Raw N HD (read rawContext q) v:=
  FormulaSignSlotRadialBoundCenterSource.evaluation G (read rawContext) sourceHeader
    (source_dimension Raw N HD rawContext hN) (window_fit Raw N HD rawContext) q v

private noncomputable def entryValue (q:List Bool) (r j:ℕ) (v:ℕ→ℝ):ℝ:=
  (IntegralPolynomialWindowTarski.entryPolynomial Raw N HD q r j).eval₂ (Int.castRingHom ℝ)
    (fun i=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val))
private theorem window_entry (q:List Bool) (r j:ℕ) (v:ℕ→ℝ):
    rawValue Raw N HD (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j))) v=
    (IntegralPolynomialWindowTarski.entryPolynomial Raw N HD q r j).eval₂ (Int.castRingHom ℝ)
      (fun i=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val)):=by
  change entryValue Raw N HD
    (IntegralPolynomialWindowTarski.control (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j))))
    (IntegralPolynomialWindowTarski.role (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j))))
    (IntegralPolynomialWindowTarski.index (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j)))) v=
      entryValue Raw N HD q r j v
  have HC:IntegralPolynomialWindowTarski.control (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j)))=q:=by
    simp only [IntegralPolynomialWindowTarski.control,pairFst_pair,pairSnd_pair]
  have HR:IntegralPolynomialWindowTarski.role (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j)))=r:=by
    simp only [IntegralPolynomialWindowTarski.role,pairFst_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HJ:IntegralPolynomialWindowTarski.index (pair (BinaryNatCode.encode r) (pair q (BinaryNatCode.encode j)))=j:=by
    simp only [IntegralPolynomialWindowTarski.index,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [HC,HR,HJ]
private theorem cons_natural {n:ℕ} (b:ℝ) (a:ℕ→ℝ) (i:Fin (n+1)):
    (Fin.cons b (fun j:Fin n=>a j.val):Fin (n+1)→ℝ) i=(if i.val=0 then b else a (i.val-1)):=by
  refine Fin.cases ?_ (fun j=>?_) i
  · rfl
  · simp only [Fin.cons_succ,Fin.val_succ,Nat.add_sub_cancel_right]
    rw [ite_eq_right (by omega)]
private theorem values_natural (K:List Bool→ℕ) (c:List Bool) (d s:ℕ) (m:Bool) (v:ℕ→ℝ):
    IntegralPolynomialWindowTarski.values K c d s m (v 3) (fun i=>v (4*i.val))=
      (fun i=>v (FormulaSignSlotRadialJointRadiusTarskiSource.column i.val)):=by
  funext i
  unfold IntegralPolynomialWindowTarski.values IntegralPolynomialWindowTarski.intervalCastValues
  rw [cons_natural (n:=K c) (v 3) (fun j=>v (4*j))]
  simp only [Fin.val_cast]
  unfold FormulaSignSlotRadialJointRadiusTarskiSource.column FormulaSignSlotRadialJointLayout.boundVariable
  split_ifs <;>rfl
attribute [local irreducible] rawValue

private theorem read_packet (c w desc:List Bool) (d s:ℕ) (m:Bool) (r j:ℕ):
    read rawContext (pair c (IntegralPolynomialWindowTarskiDecision.query
      (IntegralPolynomialWindowTarskiDecision.control (pair (pair c w) desc) d s m) r j))=
    pair (BinaryNatCode.encode r) (pair
      (IntegralPolynomialWindowTarski.intervalControl (rawContext (pair (pair c w) desc)) d s m) (BinaryNatCode.encode j)):=by
  simp only [read,window,hostRaw,rebase,sample,atomBase,
    IntegralPolynomialWindowTarskiDecision.query,IntegralPolynomialWindowTarskiDecision.control,
    IntegralPolynomialWindowTarski.intervalControl,IntegralPolynomialWindowTarskiCatalogue.control,pairFst_pair,pairSnd_pair]

theorem packet (c w desc:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w):
    IntegralPolynomialWindowTarskiDecisionReadback.Packet Raw N HD (atom Raw N HD rawContext hN)
      (pair (pair c w) desc) (rawContext (pair (pair c w) desc))
      (env c w hw 3) (fun i=>env c w hw (4*i.val)):=by
  intro d s m r j
  have HQ:atomQuery (IntegralPolynomialWindowTarskiDecision.query
      (IntegralPolynomialWindowTarskiDecision.control (pair (pair c w) desc) d s m) r j)=
      pair (pair c w) (IntegralPolynomialWindowTarskiDecision.query
        (IntegralPolynomialWindowTarskiDecision.control (pair (pair c w) desc) d s m) r j):=by
    simp only [atomQuery,atomBase,IntegralPolynomialWindowTarskiDecision.query,
      IntegralPolynomialWindowTarskiDecision.control,IntegralPolynomialWindowTarskiCatalogue.control,sample,pairFst_pair]
  unfold IntegralPolynomialWindowTarskiDecision.At atom
  rw [Function.comp_apply,HQ,value,FormulaSignSlotRadialImplicitSourceTest.packet _ _ _ _ c w _ hw]
  apply congrArg (fun x:ℝ=>InfinitesimalSign.encode (SignType.sign x))
  simp only [id_eq]
  rw [embedded_read,read_packet]
  rw [window_entry,values_natural]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialImplicitWindowAtom
