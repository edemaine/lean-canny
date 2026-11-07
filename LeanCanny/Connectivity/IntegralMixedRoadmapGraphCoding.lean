/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapGraphReachability
/-! # Fixed-width graph paths faithfully represent the raw native vertices

Padding introduces no additional point relation. Every native vertex has a
literal label, and decoding every guarded graph step yields native adjacency.
The equivalence here concerns the actual native graph, before geometry.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)

noncomputable def label (c q : List Bool):=IntegralMixedRoadmapWordLabel.encode
  (IntegralMixedRoadmapAtomic.byteBudget hn ht ha hR0 (pairFst c)) q

theorem label_decode (c q : List Bool) : IntegralMixedRoadmapWordLabel.decode (label hn ht ha hR0 c q)=q:=
  IntegralMixedRoadmapWordLabel.decode_encode _ _

theorem label_valid (c q : List Bool) (hq : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc : IntegralMixedRoadmapAtomic.candidate q=c) :Valid hn ht ha hR0 c (label hn ht ha hR0 c q) :=by
  simpa only [Valid,label_decode] using And.intro hc hq

theorem label_length (c q : List Bool) (hq : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc : IntegralMixedRoadmapAtomic.candidate q=c) : (label hn ht ha hR0 c q).length=width hn ht ha hR0 c :=by
  have HO : IntegralMixedRoadmapAtomic.original q=pairFst c:=congrArg pairFst hc
  have HB:=IntegralMixedRoadmapAtomic.byte_bound hn ht ha hR0 q hq
  rw [HO] at HB
  exact IntegralMixedRoadmapWordLabel.encode_length _ q HB

theorem decode_step (c u v : List Bool)
    (h : ImplicitGraph.Step (ImplicitGraph.guard (edges hn ht ha hR0 c) (vertices hn ht ha hR0 c))
      (width hn ht ha hR0 c) u v) :
    IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0 (IntegralMixedRoadmapWordLabel.decode u) (IntegralMixedRoadmapWordLabel.decode v) :=by
  have H : vertices hn ht ha hR0 c u=true∧vertices hn ht ha hR0 c v=true∧edges hn ht ha hR0 c u v=true:=by
    simpa only [ImplicitGraph.guard,Bool.and_eq_true,and_assoc] using h.2.2
  exact of_decide_eq_true H.2.2

theorem labels_step (c u v : List Bool) (hu : u.length=width hn ht ha hR0 c) (hv : v.length=width hn ht ha hR0 c)
    (hU : Valid hn ht ha hR0 c u) (hV : Valid hn ht ha hR0 c v)
    (hE : IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0 (IntegralMixedRoadmapWordLabel.decode u) (IntegralMixedRoadmapWordLabel.decode v)) :
    ImplicitGraph.Step (ImplicitGraph.guard (edges hn ht ha hR0 c) (vertices hn ht ha hR0 c))
      (width hn ht ha hR0 c) u v :=by
  refine ⟨hu,hv,?_⟩
  simp only [ImplicitGraph.guard,vertices,edges,hU,hV,hE,decide_true,Bool.true_and]

theorem decode_path (c u v : List Bool)
    (h : Relation.ReflTransGen (ImplicitGraph.Step (ImplicitGraph.guard (edges hn ht ha hR0 c) (vertices hn ht ha hR0 c))
      (width hn ht ha hR0 c)) u v) :
    Relation.ReflTransGen (IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0)
      (IntegralMixedRoadmapWordLabel.decode u) (IntegralMixedRoadmapWordLabel.decode v) :=
  Relation.ReflTransGen.lift IntegralMixedRoadmapWordLabel.decode (fun a b H=>decode_step hn ht ha hR0 c a b H) _ _ h

theorem path_candidate_eq (a b : List Bool)
    (h : Relation.ReflTransGen (IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0) a b) :
    IntegralMixedRoadmapAtomic.candidate a=IntegralMixedRoadmapAtomic.candidate b :=
  Relation.reflTransGen_le_of_equivalence_of_le (Setoid.ker IntegralMixedRoadmapAtomic.candidate).iseqv
    (fun _ _ => IntegralMixedRoadmapEdge.candidate_eq hn ht ha hR0 _ _) _ _ h

theorem encode_path (c a b : List Bool)
    (hc : IntegralMixedRoadmapAtomic.candidate a=c)
    (h : Relation.ReflTransGen (IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0) a b) :
    Relation.ReflTransGen (ImplicitGraph.Step (ImplicitGraph.guard (edges hn ht ha hR0 c) (vertices hn ht ha hR0 c))
      (width hn ht ha hR0 c)) (label hn ht ha hR0 c a) (label hn ht ha hR0 c b) :=by
  induction h with
  | refl=>exact .refl
  | @tail b d Hab Hbd IH=>
    obtain ⟨HB,HD⟩:=IntegralMixedRoadmapEdge.valid hn ht ha hR0 b d Hbd
    have HC : IntegralMixedRoadmapAtomic.candidate b=c:=(path_candidate_eq hn ht ha hR0 a b Hab).symm.trans hc
    have HCd : IntegralMixedRoadmapAtomic.candidate d=c:=(IntegralMixedRoadmapEdge.candidate_eq hn ht ha hR0 b d Hbd).symm.trans HC
    exact IH.tail (labels_step hn ht ha hR0 c _ _ (label_length hn ht ha hR0 c b HB HC)
      (label_length hn ht ha hR0 c d HD HCd) (label_valid hn ht ha hR0 c b HB HC)
      (label_valid hn ht ha hR0 c d HD HCd) (by simpa only [label_decode] using Hbd))

noncomputable def NativeConnected (c : List Bool):=∀a b : List Bool,
  IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a→IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b→
  IntegralMixedRoadmapAtomic.candidate a=c→IntegralMixedRoadmapAtomic.candidate b=c→
    Relation.ReflTransGen (IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0) a b

theorem connected_iff_native (c : List Bool) : c∈connectedLanguage hn ht ha hR0↔NativeConnected hn ht ha hR0 c :=by
  constructor
  · intro H a b hA hB hc hd
    have HU:=label_valid hn ht ha hR0 c a hA hc
    have HV:=label_valid hn ht ha hR0 c b hB hd
    have HP:=H _ (label_length hn ht ha hR0 c a hA hc) _ (label_length hn ht ha hR0 c b hB hd)
      (by simpa only [vertices,decide_eq_true_eq] using HU)
      (by simpa only [vertices,decide_eq_true_eq] using HV)
    simpa only [label_decode] using decode_path hn ht ha hR0 c _ _ HP
  · intro H u hu v hv hU hV
    have HU : Valid hn ht ha hR0 c u:=of_decide_eq_true hU
    have HV : Valid hn ht ha hR0 c v:=of_decide_eq_true hV
    let a:=IntegralMixedRoadmapWordLabel.decode u
    let b:=IntegralMixedRoadmapWordLabel.decode v
    have HP:=H a b HU.2 HV.2 HU.1 HV.1
    have HE:=encode_path hn ht ha hR0 c a b HU.1 HP
    have H1:=labels_step hn ht ha hR0 c u (label hn ht ha hR0 c a) hu
      (label_length hn ht ha hR0 c a HU.2 HU.1) HU (label_valid hn ht ha hR0 c a HU.2 HU.1)
      (by rw [label_decode];exact IntegralMixedRoadmapEdge.refl hn ht ha hR0 a HU.2)
    have H2:=labels_step hn ht ha hR0 c (label hn ht ha hR0 c b) v
      (label_length hn ht ha hR0 c b HV.2 HV.1) hv (label_valid hn ht ha hR0 c b HV.2 HV.1) HV
      (by rw [label_decode];exact IntegralMixedRoadmapEdge.refl hn ht ha hR0 b HV.2)
    exact (Relation.ReflTransGen.head H1 HE).tail H2

noncomputable def nativeConnectedLanguage : Language:={c |NativeConnected hn ht ha hR0 c}

theorem native_connected_decider : SpaceDecider (nativeConnectedLanguage hn ht ha hR0):=by
  apply (connected_decider hn ht ha hR0).congr
  ext c
  exact connected_iff_native hn ht ha hR0 c

theorem native_connected_mem_PSPACE : nativeConnectedLanguage hn ht ha hR0∈PSPACE:=
  (native_connected_decider hn ht ha hR0).mem_PSPACE

noncomputable def RawReachable (c a b : List Bool):=IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a∧
  IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b∧IntegralMixedRoadmapAtomic.candidate a=c∧
  IntegralMixedRoadmapAtomic.candidate b=c∧Relation.ReflTransGen (IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0) a b

theorem label_reachable_iff (c a b : List Bool) :
    ImplicitGraph.Reachable (edges hn ht ha hR0 c) (vertices hn ht ha hR0 c) (width hn ht ha hR0 c)
      (label hn ht ha hR0 c a) (label hn ht ha hR0 c b)↔RawReachable hn ht ha hR0 c a b :=by
  constructor
  · intro H
    have HU : IntegralMixedRoadmapAtomic.candidate a=c∧IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a:=by
      simpa only [Valid,label_decode] using (show Valid hn ht ha hR0 c (label hn ht ha hR0 c a) from of_decide_eq_true H.1)
    have HV : IntegralMixedRoadmapAtomic.candidate b=c∧IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b:=by
      simpa only [Valid,label_decode] using (show Valid hn ht ha hR0 c (label hn ht ha hR0 c b) from of_decide_eq_true H.2.1)
    exact ⟨HU.2,HV.2,HU.1,HV.1,by simpa only [label_decode] using decode_path hn ht ha hR0 c _ _ H.2.2⟩
  · rintro ⟨HA,HB,HC,HD,HP⟩
    exact ⟨by simpa only [vertices,decide_eq_true_eq] using label_valid hn ht ha hR0 c a HA HC,
      by simpa only [vertices,decide_eq_true_eq] using label_valid hn ht ha hR0 c b HB HD,
      encode_path hn ht ha hR0 c a b HC HP⟩

noncomputable def rawPacket (z : List Bool):=pair (pairFst z)
  (pair (label hn ht ha hR0 (pairFst z) (leftLabel z)) (label hn ht ha hR0 (pairFst z) (rightLabel z)))

theorem rawPacket_FP : rawPacket hn ht ha hR0∈FP:=by
  have HW:=(IntegralMixedRoadmapAtomic.byteBudget_unary hn ht ha hR0).comp
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have HL : leftLabel∈FP:=mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have HR : rightLabel∈FP:=mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair
    (IntegralMixedRoadmapWordLabel.encode_FP HW HL) (IntegralMixedRoadmapWordLabel.encode_FP HW HR))

noncomputable def nativeReachLanguage : Language:={z |RawReachable hn ht ha hR0 (pairFst z) (leftLabel z) (rightLabel z)}

theorem native_reach_decider : SpaceDecider (nativeReachLanguage hn ht ha hR0):=by
  apply ((reach_decider hn ht ha hR0).precompose _ (rawPacket_FP hn ht ha hR0)).congr
  ext z
  simp only [Set.mem_preimage, reachLanguage, nativeReachLanguage, Set.mem_ofPred_eq,
    rawPacket, leftLabel, rightLabel, pairFst_pair, pairSnd_pair]
  change ((label hn ht ha hR0 (pairFst z) (leftLabel z)).length=width hn ht ha hR0 (pairFst z)∧
    (label hn ht ha hR0 (pairFst z) (rightLabel z)).length=width hn ht ha hR0 (pairFst z)∧
    ImplicitGraph.Reachable (edges hn ht ha hR0 (pairFst z)) (vertices hn ht ha hR0 (pairFst z))
      (width hn ht ha hR0 (pairFst z)) (label hn ht ha hR0 (pairFst z) (leftLabel z))
        (label hn ht ha hR0 (pairFst z) (rightLabel z)))↔RawReachable hn ht ha hR0 (pairFst z) (leftLabel z) (rightLabel z)
  rw [label_reachable_iff]
  constructor
  · intro H
    exact H.2.2
  · intro H
    exact ⟨label_length hn ht ha hR0 _ _ H.1 H.2.2.1,
      label_length hn ht ha hR0 _ _ H.2.1 H.2.2.2.1,H⟩

theorem native_reach_mem_PSPACE : nativeReachLanguage hn ht ha hR0∈PSPACE:=
  (native_reach_decider hn ht ha hR0).mem_PSPACE

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph
