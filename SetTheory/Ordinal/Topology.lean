/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Enum
public import Mathlib.SetTheory.Ordinal.Enum
public import Mathlib.Tactic.TFAE
public import Mathlib.Topology.Order.IsNormal
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Order.SuccPred

/-!
# Topology of ordinals

We prove some miscellaneous results involving the order topology of ordinals.

## Main results

* `Ordinal.isClosed_iff_iSup`: A set of ordinals is closed iff it's
  closed under suprema.
* `Ordinal.enumOrd_isNormal_iff_isClosed`: The function enumerating the ordinals of a set is
  normal iff the set is closed.

## Todo

Most things in this file should be generalized to other well-orders, or to Scott-Hausdorff
topologies.
-/

@[expose] public noncomputable section

universe u v

open Cardinal Order Topology

namespace Ordinal

variable {s : Set Ordinal.{u}} {a : Ordinal.{u}}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace Ordinal.{u}
  body: Preorder.topology Ordinal.{u}

中文:
实例 :
  签名: TopologicalSpace Ordinal.{u}
  定义体: Preorder.topology Ordinal.{u}

Depends on / 依赖: CompactSpace, Ordinal, Preorder, Preorder.topology, ProperSpace, proper_of_compact, topology
-/
instance : TopologicalSpace Ordinal.{u} := Preorder.topology Ordinal.{u}
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTopology Ordinal.{u}
  body: ⟨rfl⟩

@[deprecated SuccOrder.isOpen_singleton_iff (since := "2026-01-20")]

中文:
实例 :
  签名: OrderTopology Ordinal.{u}
  定义体: ⟨rfl⟩

@[deprecated SuccOrder.isOpen_singleton_iff (since := "2026-01-20")]

Depends on / 依赖: LocallyCompactSpace, ProperSpace, locallyCompact_of_proper
-/
instance : OrderTopology Ordinal.{u} := ⟨rfl⟩

@[deprecated SuccOrder.isOpen_singleton_iff (since := "2026-01-20")]
/--
theorem `isOpen_singleton_iff` / 定理 `isOpen_singleton_iff`

English:
theorem isOpen_singleton_iff
  statement: IsOpen ({a} : Set Ordinal) ↔ ¬ IsSuccLimit a
  proof: SuccOrder.isOpen_singleton_iff

@[deprecated SuccOrder.nhds_eq_pure (since := "2026-01-20")]

中文:
定理 isOpen_singleton_iff
  结论: IsOpen ({a} : Set Ordinal) ↔ ¬ IsSuccLimit a
  证明: SuccOrder.isOpen_singleton_iff

@[deprecated SuccOrder.nhds_eq_pure (since := "2026-01-20")]

Depends on / 依赖: CompleteSpace, ProperSpace, SuccOrder, SuccOrder.isOpen_singleton_iff, complete_of_proper, isOpen_singleton_iff
-/
theorem isOpen_singleton_iff : IsOpen ({a} : Set Ordinal) ↔ ¬ IsSuccLimit a :=
  SuccOrder.isOpen_singleton_iff

@[deprecated SuccOrder.nhds_eq_pure (since := "2026-01-20")]
/--
theorem `nhds_eq_pure` / 定理 `nhds_eq_pure`

English:
theorem nhds_eq_pure
  statement: 𝓝 a = pure a ↔ ¬ IsSuccLimit a
  proof: SuccOrder.nhds_eq_pure

@[deprecated SuccOrder.isOpen_iff (since := "2026-01-20")]

中文:
定理 nhds_eq_pure
  结论: 𝓝 a = pure a ↔ ¬ IsSuccLimit a
  证明: SuccOrder.nhds_eq_pure

@[deprecated SuccOrder.isOpen_iff (since := "2026-01-20")]

Depends on / 依赖: SuccOrder, SuccOrder.nhds_eq_pure, nhds_eq_pure
-/
theorem nhds_eq_pure : 𝓝 a = pure a ↔ ¬ IsSuccLimit a :=
  SuccOrder.nhds_eq_pure

@[deprecated SuccOrder.isOpen_iff (since := "2026-01-20")]
/--
theorem `isOpen_iff` / 定理 `isOpen_iff`

English:
theorem isOpen_iff
  statement: IsOpen s ↔ forall o in s, IsSuccLimit o -> exists a < o, Set.Ioo a o subseteq s
  proof: SuccOrder.isOpen_iff

中文:
定理 isOpen_iff
  结论: IsOpen s ↔ 对任意 o in s, IsSuccLimit o -> 存在 a < o, Set.Ioo a o subseteq s
  证明: SuccOrder.isOpen_iff

Depends on / 依赖: SuccOrder, SuccOrder.isOpen_iff, isOpen_iff
-/
theorem isOpen_iff : IsOpen s ↔ forall o in s, IsSuccLimit o -> exists a < o, Set.Ioo a o subseteq s :=
  SuccOrder.isOpen_iff

open List Set in
/--
theorem `mem_closure_tfae` / 定理 `mem_closure_tfae`

English:
theorem mem_closure_tfae
  given: (a : Ordinal.{u}) (s : Set Ordinal)
  proof: by
  tfae_have 1 -> 2 := by
    simpa only [mem_closure_iff_nhdsWithin_neBot, inter_comm s, nhdsWithin_inter',
      SuccOrder.nhdsLE_eq_nhds] using! id
  tfae_have 2 -> 3
  | h => by
    rcases (s inter Iic a).eq_empty_or_nonempty with he | hne
    · simp [he] at h
    · refine ⟨hne, (isLUB_of_mem_

中文:
定理 mem_closure_tfae
  条件: (a : Ordinal.{u}) (s : Set Ordinal)
  证明: by
  tfae_have 1 -> 2 := by
    simpa only [mem_closure_iff_nhdsWithin_neBot, inter_comm s, nhdsWithin_inter',
      SuccOrder.nhdsLE_eq_nhds] using! id
  tfae_have 2 -> 3
  | h => by
    rcases (s inter Iic a).eq_empty_or_nonempty with he | hne
    · simp [he] at h
    · refine ⟨hne, (isLUB_of_mem_

Depends on / 依赖: SuccOrder, SuccOrder.nhdsLE_eq_nhds, bddAbove_Iic, bddAbove_Iic.mono, bddAbove_iff_small, csSup_eq, eq_empty_or_nonempty, inter_comm, inter_subset_left, inter_subset_right, isLUB_of_mem_closure, mem_closure_iff_nhdsWithin_neBot, nhdsLE_eq_nhds, nhdsWithin_inter, tfae_have
-/
theorem mem_closure_tfae (a : Ordinal.{u}) (s : Set Ordinal) :
    TFAE [a in closure s,
      a in closure (s inter Iic a),
      (s inter Iic a).Nonempty ∧ sSup (s inter Iic a) = a,
      exists t, t subseteq s ∧ t.Nonempty ∧ BddAbove t ∧ sSup t = a,
      exists (ι : Type u), Nonempty ι ∧ exists f : ι -> Ordinal, (forall i, f i in s) ∧ ⨆ i, f i = a] := by
  tfae_have 1 -> 2 := by
    simpa only [mem_closure_iff_nhdsWithin_neBot, inter_comm s, nhdsWithin_inter',
      SuccOrder.nhdsLE_eq_nhds] using! id
  tfae_have 2 -> 3
  | h => by
    rcases (s inter Iic a).eq_empty_or_nonempty with he | hne
    · simp [he] at h
    · refine ⟨hne, (isLUB_of_mem_closure ?_ h).csSup_eq hne⟩
      exact fun x hx => hx.2
  tfae_have 3 -> 4
  | h => ⟨_, inter_subset_left, h.1, bddAbove_Iic.mono inter_subset_right, h.2⟩
  tfae_have 4 -> 5 := by
    rintro ⟨t, ht, ht₀, ht₁, rfl⟩
    rw [bddAbove_iff_small] at ht₁
    refine ⟨Shrink t, ?_, Subtype.val ∘ (equivShrink _).symm, ?_, ?_⟩
    · have := ht₀.to_subtype
      exact (equivShrink _).symm.nonempty
    · simpa [← (equivShrink t).forall_congr_left (p := (·.1 in s))]
    · simp [(equivShrink t).symm.iSup_comp, ← sSup_eq_iSup']
  tfae_have 5 -> 1 := by
    rintro ⟨ι, hne, f, hfs, rfl⟩
exact closure_mono (range_subset_iff.2 hfs) csSup_mem_closure (range_nonempty f)
      bddAbove_of_small
  tfae_finish

/--
theorem `mem_closure_iff_iSup` / 定理 `mem_closure_iff_iSup`

English:
theorem mem_closure_iff_iSup
  proof: by
  apply ((mem_closure_tfae a s).out 0 4).trans
  simp_rw [exists_prop]

中文:
定理 mem_closure_iff_iSup
  证明: by
  apply ((mem_closure_tfae a s).out 0 4).trans
  simp_rw [exists_prop]

Depends on / 依赖: exists_prop, mem_closure_tfae, simp_rw
-/
theorem mem_closure_iff_iSup :
    a in closure s ↔
      exists (ι : Type u) (_ : Nonempty ι) (f : ι -> Ordinal), (forall i, f i in s) ∧ ⨆ i, f i = a := by
  apply ((mem_closure_tfae a s).out 0 4).trans
  simp_rw [exists_prop]

/--
theorem `mem_iff_iSup_of_isClosed` / 定理 `mem_iff_iSup_of_isClosed`

English:
theorem mem_iff_iSup_of_isClosed
  given: (hs : IsClosed s)
  proof: by
  rw [← mem_closure_iff_iSup]; rw [hs.closure_eq]

@[deprecated mem_closure_iff_iSup (since := "2026-04-05")]

中文:
定理 mem_iff_iSup_of_isClosed
  条件: (hs : IsClosed s)
  证明: by
  rw [← mem_closure_iff_iSup]; rw [hs.closure_eq]

@[deprecated mem_closure_iff_iSup (since := "2026-04-05")]

Depends on / 依赖: closure_eq, hs.closure_eq, mem_closure_iff_iSup
-/
theorem mem_iff_iSup_of_isClosed (hs : IsClosed s) :
    a in s ↔ exists (ι : Type u) (_hι : Nonempty ι) (f : ι -> Ordinal),
      (forall i, f i in s) ∧ ⨆ i, f i = a := by
  rw [← mem_closure_iff_iSup]; rw [hs.closure_eq]

@[deprecated mem_closure_iff_iSup (since := "2026-04-05")]
/--
theorem `mem_closure_iff_bsup` / 定理 `mem_closure_iff_bsup`

English:
theorem mem_closure_iff_bsup
  proof: by
  rw [mem_closure_iff_iSup]
  constructor
  · rintro ⟨ι, _, f, hf, rfl⟩
    exact ⟨_, by simp, bfamilyOfFamily f, fun i hi => hf .., bsup_eq_iSup f⟩
  · rintro ⟨o, ho, f, hf, rfl⟩
    exact ⟨_, by simpa, familyOfBFamily _ f, fun i => hf .., iSup_eq_bsup f⟩

@[deprecated mem_closure_iff_iSup (sinc

中文:
定理 mem_closure_iff_bsup
  证明: by
  rw [mem_closure_iff_iSup]
  constructor
  · rintro ⟨ι, _, f, hf, rfl⟩
    exact ⟨_, by simp, bfamilyOfFamily f, fun i hi => hf .., bsup_eq_iSup f⟩
  · rintro ⟨o, ho, f, hf, rfl⟩
    exact ⟨_, by simpa, familyOfBFamily _ f, fun i => hf .., iSup_eq_bsup f⟩

@[deprecated mem_closure_iff_iSup (sinc

Depends on / 依赖: bfamilyOfFamily, bsup_eq_iSup, familyOfBFamily, iSup_eq_bsup, mem_closure_iff_iSup
-/
theorem mem_closure_iff_bsup :
    a in closure s ↔
      exists (o : Ordinal) (_ho : o != 0) (f : forall a < o, Ordinal),
        (forall i hi, f i hi in s) ∧ bsup.{u, u} o f = a := by
  rw [mem_closure_iff_iSup]
  constructor
  · rintro ⟨ι, _, f, hf, rfl⟩
    exact ⟨_, by simp, bfamilyOfFamily f, fun i hi => hf .., bsup_eq_iSup f⟩
  · rintro ⟨o, ho, f, hf, rfl⟩
    exact ⟨_, by simpa, familyOfBFamily _ f, fun i => hf .., iSup_eq_bsup f⟩

@[deprecated mem_closure_iff_iSup (since := "2026-04-05")]
/--
theorem `mem_closed_iff_bsup` / 定理 `mem_closed_iff_bsup`

English:
theorem mem_closed_iff_bsup
  given: (hs : IsClosed s)
  proof: by
  rw [← mem_closure_iff_bsup]; rw [hs.closure_eq]

中文:
定理 mem_closed_iff_bsup
  条件: (hs : IsClosed s)
  证明: by
  rw [← mem_closure_iff_bsup]; rw [hs.closure_eq]

Depends on / 依赖: closure_eq, hs.closure_eq, mem_closure_iff_bsup
-/
theorem mem_closed_iff_bsup (hs : IsClosed s) :
    a in s ↔
      exists (o : Ordinal) (_ho : o != 0) (f : forall a < o, Ordinal),
        (forall i hi, f i hi in s) ∧ bsup.{u, u} o f = a := by
  rw [← mem_closure_iff_bsup]; rw [hs.closure_eq]

/--
theorem `isClosed_iff_iSup` / 定理 `isClosed_iff_iSup`

English:
theorem isClosed_iff_iSup
  proof: by
  use fun hs ι hι f hf => (mem_iff_iSup_of_isClosed hs).2 ⟨ι, hι, f, hf, rfl⟩
  rw [← closure_subset_iff_isClosed]
  intro h x hx
  rcases mem_closure_iff_iSup.1 hx with ⟨ι, hι, f, hf, rfl⟩
  exact h hι f hf

@[deprecated isClosed_iff_iSup (since := "2026-04-05")]

中文:
定理 isClosed_iff_iSup
  证明: by
  use fun hs ι hι f hf => (mem_iff_iSup_of_isClosed hs).2 ⟨ι, hι, f, hf, rfl⟩
  rw [← closure_subset_iff_isClosed]
  intro h x hx
  rcases mem_closure_iff_iSup.1 hx with ⟨ι, hι, f, hf, rfl⟩
  exact h hι f hf

@[deprecated isClosed_iff_iSup (since := "2026-04-05")]

Depends on / 依赖: closure_subset_iff_isClosed, mem_closure_iff_iSup, mem_iff_iSup_of_isClosed
-/
theorem isClosed_iff_iSup :
    IsClosed s ↔
      forall {ι : Type u}, Nonempty ι -> forall f : ι -> Ordinal, (forall i, f i in s) -> ⨆ i, f i in s := by
  use fun hs ι hι f hf => (mem_iff_iSup_of_isClosed hs).2 ⟨ι, hι, f, hf, rfl⟩
  rw [← closure_subset_iff_isClosed]
  intro h x hx
  rcases mem_closure_iff_iSup.1 hx with ⟨ι, hι, f, hf, rfl⟩
  exact h hι f hf

@[deprecated isClosed_iff_iSup (since := "2026-04-05")]
/--
theorem `isClosed_iff_bsup` / 定理 `isClosed_iff_bsup`

English:
theorem isClosed_iff_bsup
  proof: by
  rw [isClosed_iff_iSup]
  refine ⟨fun H o ho f hf => H (nonempty_toType_iff.2 ho) _ ?_, fun H ι hι f hf => ?_⟩
  · exact fun i => hf _ _
  · rw [← bsup_eq_iSup]
    apply H (type_ne_zero_iff_nonempty.2 hι)
    exact fun i hi => hf _

@[deprecated SuccOrder.isSuccLimit_of_mem_frontier (since := "

中文:
定理 isClosed_iff_bsup
  证明: by
  rw [isClosed_iff_iSup]
  refine ⟨fun H o ho f hf => H (nonempty_toType_iff.2 ho) _ ?_, fun H ι hι f hf => ?_⟩
  · exact fun i => hf _ _
  · rw [← bsup_eq_iSup]
    apply H (type_ne_zero_iff_nonempty.2 hι)
    exact fun i hi => hf _

@[deprecated SuccOrder.isSuccLimit_of_mem_frontier (since := "

Depends on / 依赖: bsup_eq_iSup, isClosed_iff_iSup, nonempty_toType_iff, type_ne_zero_iff_nonempty
-/
theorem isClosed_iff_bsup :
    IsClosed s ↔
      forall {o : Ordinal}, o != 0 -> forall f : forall a < o, Ordinal,
        (forall i hi, f i hi in s) -> bsup.{u, u} o f in s := by
  rw [isClosed_iff_iSup]
  refine ⟨fun H o ho f hf => H (nonempty_toType_iff.2 ho) _ ?_, fun H ι hι f hf => ?_⟩
  · exact fun i => hf _ _
  · rw [← bsup_eq_iSup]
    apply H (type_ne_zero_iff_nonempty.2 hι)
    exact fun i hi => hf _

@[deprecated SuccOrder.isSuccLimit_of_mem_frontier (since := "2026-01-20")]
/--
theorem `isSuccLimit_of_mem_frontier` / 定理 `isSuccLimit_of_mem_frontier`

English:
theorem isSuccLimit_of_mem_frontier
  given: (ha : a in frontier s)
  statement: IsSuccLimit a
  proof: SuccOrder.isSuccLimit_of_mem_frontier ha

@[deprecated isNormal_enum_iff_dirSupClosed (since := "2026-05-25")]

中文:
定理 isSuccLimit_of_mem_frontier
  条件: (ha : a in frontier s)
  结论: IsSuccLimit a
  证明: SuccOrder.isSuccLimit_of_mem_frontier ha

@[deprecated isNormal_enum_iff_dirSupClosed (since := "2026-05-25")]

Depends on / 依赖: SuccOrder, SuccOrder.isSuccLimit_of_mem_frontier, isSuccLimit_of_mem_frontier
-/
theorem isSuccLimit_of_mem_frontier (ha : a in frontier s) : IsSuccLimit a :=
  SuccOrder.isSuccLimit_of_mem_frontier ha

@[deprecated isNormal_enum_iff_dirSupClosed (since := "2026-05-25")]
/--
theorem `enumOrd_isNormal_iff_isClosed` / 定理 `enumOrd_isNormal_iff_isClosed`

English:
theorem enumOrd_isNormal_iff_isClosed
  given: (hs : ¬ BddAbove s)
  proof: by
  have Hs := enumOrd_strictMono hs
  refine
    ⟨fun h => isClosed_iff_iSup.2 fun {ι} hι f hf => ?_, fun h =>
      isNormal_iff.2 ⟨Hs, fun a ha o H => ?_⟩⟩
  · let g : ι -> Ordinal.{u} := fun i => (enumOrdOrderIso s hs).symm ⟨_, hf i⟩
    suffices enumOrd s (⨆ i, g i) = ⨆ i, f i by
      rw [← t

中文:
定理 enumOrd_isNormal_iff_isClosed
  条件: (hs : ¬ BddAbove s)
  证明: by
  have Hs := enumOrd_strictMono hs
  refine
    ⟨fun h => isClosed_iff_iSup.2 fun {ι} hι f hf => ?_, fun h =>
      isNormal_iff.2 ⟨Hs, fun a ha o H => ?_⟩⟩
  · let g : ι -> Ordinal.{u} := fun i => (enumOrdOrderIso s hs).symm ⟨_, hf i⟩
    suffices enumOrd s (⨆ i, g i) = ⨆ i, f i by
      rw [← t

Depends on / 依赖: OrderIso, OrderIso.apply_symm_apply, Ordinal, apply_symm_apply, bddAbove_of_sma, bddAbove_of_small, csSup_mem_closure, enumOrd, enumOrdOrderIso, enumOrd_mem, enumOrd_strictMono, h.map_iSup, ha.nonempty_Iio.image, isClosed_iff_iSup, isNormal_iff, map_iSup, nonempty_Iio
-/
theorem enumOrd_isNormal_iff_isClosed (hs : ¬ BddAbove s) :
    IsNormal (enumOrd s) ↔ IsClosed s := by
  have Hs := enumOrd_strictMono hs
  refine
    ⟨fun h => isClosed_iff_iSup.2 fun {ι} hι f hf => ?_, fun h =>
      isNormal_iff.2 ⟨Hs, fun a ha o H => ?_⟩⟩
  · let g : ι -> Ordinal.{u} := fun i => (enumOrdOrderIso s hs).symm ⟨_, hf i⟩
    suffices enumOrd s (⨆ i, g i) = ⨆ i, f i by
      rw [← this]
      exact enumOrd_mem hs _
    rw [h.map_iSup bddAbove_of_small]
    congr
    ext x
    change (enumOrdOrderIso s hs _).val = f x
    rw [OrderIso.apply_symm_apply]
  · have := csSup_mem_closure (ha.nonempty_Iio.image (enumOrd s)) bddAbove_of_small
    have := h.closure_eq ▸ closure_mono (t := s) ?_ this
    · apply (Set.image_subset_range ..).trans_eq
      rw [range_enumOrd hs]
    · apply (enumOrd_le_of_forall_lt this _).trans
      · apply csSup_le'
        grind [upperBounds]
· exact fun b hb => (enumOrd_strictMono hs (lt_add_one b)).trans_le
le_csSup bddAbove_of_small Set.mem_image_of_mem _ (ha.add_one_lt hb)

open Set Filter Set.Notation

/-- An ordinal is an accumulation point of a set of ordinals if it is positive and there
are elements in the set arbitrarily close to the ordinal from below. -/
@[deprecated AccPt (since := "2026-05-24")]
/--
Definition of `IsAcc` / `IsAcc` 的定义

English:
definition IsAcc
  signature: (o : Ordinal) (S : Set Ordinal)
  body: AccPt o (𝓟 S)

中文:
定义 IsAcc
  签名: (o : Ordinal) (S : Set Ordinal)
  定义体: AccPt o (𝓟 S)
-/
def IsAcc (o : Ordinal) (S : Set Ordinal) : Prop :=
  AccPt o (𝓟 S)

/-- A set of ordinals is closed below an ordinal if it contains all of
its accumulation points below the ordinal. -/
@[deprecated IsClosed (since := "2026-05-24")]
/--
Definition of `IsClosedBelow` / `IsClosedBelow` 的定义

English:
definition IsClosedBelow
  signature: (S : Set Ordinal) (o : Ordinal)
  body: IsClosed (Iio o ↓inter S)

@[deprecated SuccOrder.accPt_principal (since := "2026-05-24")]

中文:
定义 IsClosedBelow
  签名: (S : Set Ordinal) (o : Ordinal)
  定义体: IsClosed (Iio o ↓inter S)

@[deprecated SuccOrder.accPt_principal (since := "2026-05-24")]

Depends on / 依赖: IsClosed
-/
def IsClosedBelow (S : Set Ordinal) (o : Ordinal) : Prop :=
  IsClosed (Iio o ↓inter S)

@[deprecated SuccOrder.accPt_principal (since := "2026-05-24")]
/--
theorem `isAcc_iff` / 定理 `isAcc_iff`

English:
theorem isAcc_iff
  given: (o : Ordinal) (S : Set Ordinal)
  statement: o.IsAcc S ↔
  proof: by
  apply SuccOrder.accPt_principal.trans
  simp

@[deprecated SuccOrder.accPt_principal (since := "2026-05-24")]

中文:
定理 isAcc_iff
  条件: (o : Ordinal) (S : Set Ordinal)
  结论: o.IsAcc S ↔
  证明: by
  apply SuccOrder.accPt_principal.trans
  simp

@[deprecated SuccOrder.accPt_principal (since := "2026-05-24")]

Depends on / 依赖: SuccOrder, SuccOrder.accPt_principal.trans, accPt_principal
-/
theorem isAcc_iff (o : Ordinal) (S : Set Ordinal) : o.IsAcc S ↔
    o != 0 ∧ forall p < o, (S inter Ioo p o).Nonempty := by
  apply SuccOrder.accPt_principal.trans
  simp

@[deprecated SuccOrder.accPt_principal (since := "2026-05-24")]
/--
theorem `IsAcc.forall_lt` / 定理 `IsAcc.forall_lt`

English:
theorem IsAcc.forall_lt
  given: {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S)
  proof: ((isAcc_iff _ _).mp h).2

@[deprecated AccPt.not_isMin (since := "2026-05-24")]

中文:
定理 IsAcc.forall_lt
  条件: {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S)
  证明: ((isAcc_iff _ _).mp h).2

@[deprecated AccPt.not_isMin (since := "2026-05-24")]

Depends on / 依赖: isAcc_iff
-/
theorem IsAcc.forall_lt {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) :
    forall p < o, (S inter Ioo p o).Nonempty := ((isAcc_iff _ _).mp h).2

@[deprecated AccPt.not_isMin (since := "2026-05-24")]
/--
theorem `IsAcc.pos` / 定理 `IsAcc.pos`

English:
theorem IsAcc.pos
  given: {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S)
  proof: pos_iff_ne_zero.mpr ((isAcc_iff _ _).mp h).1

@[deprecated AccPt.isSuccLimit (since := "2026-05-24")]

中文:
定理 IsAcc.pos
  条件: {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S)
  证明: pos_iff_ne_zero.mpr ((isAcc_iff _ _).mp h).1

@[deprecated AccPt.isSuccLimit (since := "2026-05-24")]

Depends on / 依赖: isAcc_iff, pos_iff_ne_zero, pos_iff_ne_zero.mpr
-/
theorem IsAcc.pos {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) :
    0 < o := pos_iff_ne_zero.mpr ((isAcc_iff _ _).mp h).1

@[deprecated AccPt.isSuccLimit (since := "2026-05-24")]
/--
theorem `IsAcc.isSuccLimit` / 定理 `IsAcc.isSuccLimit`

English:
theorem IsAcc.isSuccLimit
  given: {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S)
  statement: IsSuccLimit o
  proof: AccPt.isSuccLimit h

@[deprecated AccPt.mono (since := "2026-05-24")]

中文:
定理 IsAcc.isSuccLimit
  条件: {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S)
  结论: IsSuccLimit o
  证明: AccPt.isSuccLimit h

@[deprecated AccPt.mono (since := "2026-05-24")]

Depends on / 依赖: AccPt.isSuccLimit, isSuccLimit
-/
theorem IsAcc.isSuccLimit {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) : IsSuccLimit o :=
  AccPt.isSuccLimit h

@[deprecated AccPt.mono (since := "2026-05-24")]
/--
theorem `IsAcc.mono` / 定理 `IsAcc.mono`

English:
theorem IsAcc.mono
  given: {o : Ordinal} {S T : Set Ordinal} (h : S subseteq T) (ho : o.IsAcc S)
  statement: o.IsAcc T
  proof: AccPt.mono ho (monotone_principal h)

@[deprecated SuccOrder.accPt_principal (since := "2026-05-24")]

中文:
定理 IsAcc.mono
  条件: {o : Ordinal} {S T : Set Ordinal} (h : S subseteq T) (ho : o.IsAcc S)
  结论: o.IsAcc T
  证明: AccPt.mono ho (monotone_principal h)

@[deprecated SuccOrder.accPt_principal (since := "2026-05-24")]

Depends on / 依赖: AccPt.mono, monotone_principal
-/
theorem IsAcc.mono {o : Ordinal} {S T : Set Ordinal} (h : S subseteq T) (ho : o.IsAcc S) : o.IsAcc T :=
  AccPt.mono ho (monotone_principal h)

@[deprecated SuccOrder.accPt_principal (since := "2026-05-24")]
/--
theorem `IsAcc.inter_Ioo_nonempty` / 定理 `IsAcc.inter_Ioo_nonempty`

English:
theorem IsAcc.inter_Ioo_nonempty
  statement: {o : Ordinal} {S : Set Ordinal} (hS : o.IsAcc S)
  proof: hS.forall_lt p hp

@[deprecated IsOpenEmbedding.accPt_comap_iff (since := "2026-03-30")]

中文:
定理 IsAcc.inter_Ioo_nonempty
  结论: {o : Ordinal} {S : Set Ordinal} (hS : o.IsAcc S)
  证明: hS.forall_lt p hp

@[deprecated IsOpenEmbedding.accPt_comap_iff (since := "2026-03-30")]

Depends on / 依赖: forall_lt, hS.forall_lt
-/
theorem IsAcc.inter_Ioo_nonempty {o : Ordinal} {S : Set Ordinal} (hS : o.IsAcc S)
    {p : Ordinal} (hp : p < o) : (S inter Ioo p o).Nonempty := hS.forall_lt p hp

@[deprecated IsOpenEmbedding.accPt_comap_iff (since := "2026-03-30")]
/--
theorem `accPt_subtype` / 定理 `accPt_subtype`

English:
theorem accPt_subtype
  given: {p o : Ordinal} (S : Set Ordinal) (hpo : p < o)
  proof: by
  rw [← comap_principal]; rw [isOpen_Iio.isOpenEmbedding_subtypeVal.accPt_comap_iff]

@[deprecated isClosed_iff_accPt (since := "2026-05-24")]

中文:
定理 accPt_subtype
  条件: {p o : Ordinal} (S : Set Ordinal) (hpo : p < o)
  证明: by
  rw [← comap_principal]; rw [isOpen_Iio.isOpenEmbedding_subtypeVal.accPt_comap_iff]

@[deprecated isClosed_iff_accPt (since := "2026-05-24")]

Depends on / 依赖: accPt_comap_iff, comap_principal, isOpenEmbedding_subtypeVal, isOpen_Iio, isOpen_Iio.isOpenEmbedding_subtypeVal.accPt_comap_iff
-/
theorem accPt_subtype {p o : Ordinal} (S : Set Ordinal) (hpo : p < o) :
    AccPt p (𝓟 S) ↔ AccPt ⟨p, hpo⟩ (𝓟 (Iio o ↓inter S)) := by
  rw [← comap_principal]; rw [isOpen_Iio.isOpenEmbedding_subtypeVal.accPt_comap_iff]

@[deprecated isClosed_iff_accPt (since := "2026-05-24")]
/--
theorem `isClosedBelow_iff` / 定理 `isClosedBelow_iff`

English:
theorem isClosedBelow_iff
  given: {S : Set Ordinal} {o : Ordinal}
  statement: IsClosedBelow S o ↔
  proof: by
  simp [IsClosedBelow, IsAcc, isClosed_iff_accPt, ← comap_principal,
    isOpen_Iio.isOpenEmbedding_subtypeVal.accPt_comap_iff]

@[deprecated isClosed_iff_accPt (since := "2026-05-24")]
alias ⟨IsClosedBelow.forall_lt, _⟩ := isClosedBelow_iff

@[deprecated isClosed_sInter (since := "2026-05-24")]

中文:
定理 isClosedBelow_iff
  条件: {S : Set Ordinal} {o : Ordinal}
  结论: IsClosedBelow S o ↔
  证明: by
  simp [IsClosedBelow, IsAcc, isClosed_iff_accPt, ← comap_principal,
    isOpen_Iio.isOpenEmbedding_subtypeVal.accPt_comap_iff]

@[deprecated isClosed_iff_accPt (since := "2026-05-24")]
alias ⟨IsClosedBelow.forall_lt, _⟩ := isClosedBelow_iff

@[deprecated isClosed_sInter (since := "2026-05-24")]

Depends on / 依赖: IsClosedBelow, accPt_comap_iff, comap_principal, isClosed_iff_accPt, isOpenEmbedding_subtypeVal, isOpen_Iio, isOpen_Iio.isOpenEmbedding_subtypeVal.accPt_comap_iff
-/
theorem isClosedBelow_iff {S : Set Ordinal} {o : Ordinal} : IsClosedBelow S o ↔
    forall p < o, IsAcc p S -> p in S := by
  simp [IsClosedBelow, IsAcc, isClosed_iff_accPt, ← comap_principal,
    isOpen_Iio.isOpenEmbedding_subtypeVal.accPt_comap_iff]

@[deprecated isClosed_iff_accPt (since := "2026-05-24")]
alias ⟨IsClosedBelow.forall_lt, _⟩ := isClosedBelow_iff

@[deprecated isClosed_sInter (since := "2026-05-24")]
/--
theorem `IsClosedBelow.sInter` / 定理 `IsClosedBelow.sInter`

English:
theorem IsClosedBelow.sInter
  statement: {o : Ordinal} {S : Set (Set Ordinal)}
  proof: by
  rw [isClosedBelow_iff]
exact fun p plto pAcc C CmemS => (h C CmemS).forall_lt p plto
    AccPt.mono pAcc (monotone_principal (sInter_subset_of_mem CmemS))

@[deprecated isClosed_iInter (since := "2026-05-24")]

中文:
定理 IsClosedBelow.sInter
  结论: {o : Ordinal} {S : Set (Set Ordinal)}
  证明: by
  rw [isClosedBelow_iff]
exact fun p plto pAcc C CmemS => (h C CmemS).forall_lt p plto
    AccPt.mono pAcc (monotone_principal (sInter_subset_of_mem CmemS))

@[deprecated isClosed_iInter (since := "2026-05-24")]

Depends on / 依赖: AccPt.mono, forall_lt, isClosedBelow_iff, monotone_principal, sInter_subset_of_mem
-/
theorem IsClosedBelow.sInter {o : Ordinal} {S : Set (Set Ordinal)}
    (h : forall C in S, IsClosedBelow C o) : IsClosedBelow (⋂₀ S) o := by
  rw [isClosedBelow_iff]
exact fun p plto pAcc C CmemS => (h C CmemS).forall_lt p plto
    AccPt.mono pAcc (monotone_principal (sInter_subset_of_mem CmemS))

@[deprecated isClosed_iInter (since := "2026-05-24")]
/--
theorem `IsClosedBelow.iInter` / 定理 `IsClosedBelow.iInter`

English:
theorem IsClosedBelow.iInter
  statement: {ι : Type u} {f : ι -> Set Ordinal} {o : Ordinal}
  proof: IsClosedBelow.sInter fun _ ⟨i, hi⟩ => hi ▸ (h i)

中文:
定理 IsClosedBelow.iInter
  结论: {ι : 类型u} {f : ι -> Set Ordinal} {o : Ordinal}
  证明: IsClosedBelow.sInter fun _ ⟨i, hi⟩ => hi ▸ (h i)

Depends on / 依赖: IsClosedBelow, IsClosedBelow.sInter, sInter
-/
theorem IsClosedBelow.iInter {ι : Type u} {f : ι -> Set Ordinal} {o : Ordinal}
    (h : forall i, IsClosedBelow (f i) o) : IsClosedBelow (⋂ i, f i) o :=
  IsClosedBelow.sInter fun _ ⟨i, hi⟩ => hi ▸ (h i)

end Ordinal
