/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Topology.Connected.Clopen

/-!
# Totally disconnected and totally separated topological spaces

## Main definitions
We define the following properties for sets in a topological space:

* `IsTotallyDisconnected`: all of its connected components are singletons.
* `IsTotallySeparated`: any two points can be separated by two disjoint opens that cover the set.

For both of these definitions, we also have a class stating that the whole space
satisfies that property: `TotallyDisconnectedSpace`, `TotallySeparatedSpace`.
-/

@[expose] public section

open Function Set Topology

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι -> Type*} [TopologicalSpace α]
  {s t u v : Set α}

section TotallyDisconnected

/--
Definition of `IsTotallyDisconnected` / `IsTotallyDisconnected` 的定义

English:
definition IsTotallyDisconnected
  signature: (s : Set α)
  body: forall t, t subseteq s -> IsPreconnected t -> t.Subsingleton

中文:
定义 IsTotallyDisconnected
  签名: (s : Set α)
  定义体: forall t, t subseteq s -> IsPreconnected t -> t.Subsingleton

Depends on / 依赖: IsPreconnected, Subsingleton, subseteq, t.Subsingleton
-/
def IsTotallyDisconnected (s : Set α) : Prop :=
  forall t, t subseteq s -> IsPreconnected t -> t.Subsingleton

/--
theorem `isTotallyDisconnected_empty` / 定理 `isTotallyDisconnected_empty`

English:
theorem isTotallyDisconnected_empty
  statement: IsTotallyDisconnected (∅ : Set α)
  proof: fun _ ht _ _ x_in _ _ =>
  (ht x_in).elim

中文:
定理 isTotallyDisconnected_empty
  结论: IsTotallyDisconnected (∅ : Set α)
  证明: fun _ ht _ _ x_in _ _ =>
  (ht x_in).elim

Depends on / 依赖: x_in
-/
theorem isTotallyDisconnected_empty : IsTotallyDisconnected (∅ : Set α) := fun _ ht _ _ x_in _ _ =>
  (ht x_in).elim

/--
theorem `isTotallyDisconnected_singleton` / 定理 `isTotallyDisconnected_singleton`

English:
theorem isTotallyDisconnected_singleton
  given: {x}
  statement: IsTotallyDisconnected ({x} : Set α)
  proof: fun _ ht _ =>
  subsingleton_singleton.anti ht

中文:
定理 isTotallyDisconnected_singleton
  条件: {x}
  结论: IsTotallyDisconnected ({x} : Set α)
  证明: fun _ ht _ =>
  subsingleton_singleton.anti ht
-/
theorem isTotallyDisconnected_singleton {x} : IsTotallyDisconnected ({x} : Set α) := fun _ ht _ =>
  subsingleton_singleton.anti ht

/-- A space is totally disconnected if all of its connected components are singletons. -/
@[mk_iff]
/--
Definition of `TotallyDisconnectedSpace` / `TotallyDisconnectedSpace` 的定义

English:
class TotallyDisconnectedSpace
  parameters: (α : Type u) [TopologicalSpace α]
  axioms and operations (1):
    - isTotallyDisconnected_univ : IsTotallyDisconnected (univ : Set α)

中文:
类 TotallyDisconnectedSpace
  参数: (α : 类型u) [TopologicalSpace α]
  公理与运算 (1 个):
    - isTotallyDisconnected_univ : IsTotallyDisconnected (univ : Set α)
-/
class TotallyDisconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a totally disconnected space is totally disconnected. -/
  isTotallyDisconnected_univ : IsTotallyDisconnected (univ : Set α)

/--
theorem `IsPreconnected.subsingleton` / 定理 `IsPreconnected.subsingleton`

English:
theorem IsPreconnected.subsingleton
  statement: [TotallyDisconnectedSpace α] {s : Set α}
  proof: TotallyDisconnectedSpace.isTotallyDisconnected_univ s (subset_univ s) h

中文:
定理 IsPreconnected.subsingleton
  结论: [TotallyDisconnectedSpace α] {s : Set α}
  证明: TotallyDisconnectedSpace.isTotallyDisconnected_univ s (subset_univ s) h

Depends on / 依赖: TotallyDisconnectedSpace, TotallyDisconnectedSpace.isTotallyDisconnected_univ, isTotallyDisconnected_univ, subset_univ
-/
theorem IsPreconnected.subsingleton [TotallyDisconnectedSpace α] {s : Set α}
    (h : IsPreconnected s) : s.Subsingleton :=
  TotallyDisconnectedSpace.isTotallyDisconnected_univ s (subset_univ s) h

-- note: making this an instance breaks downstream files
/--
theorem `subsingleton_of_preconnected_totallyDisconnected` / 定理 `subsingleton_of_preconnected_totallyDisconnected`

English:
theorem subsingleton_of_preconnected_totallyDisconnected
  proof: Set.subsingleton_of_univ_subsingleton isPreconnected_univ.subsingleton

中文:
定理 subsingleton_of_preconnected_totallyDisconnected
  证明: Set.subsingleton_of_univ_subsingleton isPreconnected_univ.subsingleton

Depends on / 依赖: Set.subsingleton_of_univ_subsingleton, isPreconnected_univ, isPreconnected_univ.subsingleton, subsingleton, subsingleton_of_univ_subsingleton
-/
theorem subsingleton_of_preconnected_totallyDisconnected
    [PreconnectedSpace α] [TotallyDisconnectedSpace α] : Subsingleton α :=
  Set.subsingleton_of_univ_subsingleton isPreconnected_univ.subsingleton

/--
Instance `Pi.totallyDisconnectedSpace` / 实例 `Pi.totallyDisconnectedSpace`

English:
instance Pi.totallyDisconnectedSpace
  signature: {α : Type*} {β : α -> Type*}
  body: ⟨fun t _ h2 =>
    have : forall a, IsPreconnected ((fun x : forall a, β a => x a) '' t) := fun a =>
      h2.image (fun x => x a) (continuous_apply a).continuousOn
    fun x x_in y y_in => funext fun a => (this a).subsingleton ⟨x, x_in, rfl⟩ ⟨y, y_in, rfl⟩⟩

中文:
实例 Pi.totallyDisconnectedSpace
  签名: {α : 类型} {β : α -> 类型}
  定义体: ⟨fun t _ h2 =>
    have : forall a, IsPreconnected ((fun x : forall a, β a => x a) '' t) := fun a =>
      h2.image (fun x => x a) (continuous_apply a).continuousOn
    fun x x_in y y_in => funext fun a => (this a).subsingleton ⟨x, x_in, rfl⟩ ⟨y, y_in, rfl⟩⟩

Depends on / 依赖: IsPreconnected, continuousOn, continuous_apply, h2.image, subsingleton, x_in, y_in
-/
instance Pi.totallyDisconnectedSpace {α : Type*} {β : α -> Type*}
    [forall a, TopologicalSpace (β a)] [forall a, TotallyDisconnectedSpace (β a)] :
    TotallyDisconnectedSpace (forall a : α, β a) :=
  ⟨fun t _ h2 =>
    have : forall a, IsPreconnected ((fun x : forall a, β a => x a) '' t) := fun a =>
      h2.image (fun x => x a) (continuous_apply a).continuousOn
    fun x x_in y y_in => funext fun a => (this a).subsingleton ⟨x, x_in, rfl⟩ ⟨y, y_in, rfl⟩⟩

/--
Instance `Prod.totallyDisconnectedSpace` / 实例 `Prod.totallyDisconnectedSpace`

English:
instance Prod.totallyDisconnectedSpace
  signature: [TopologicalSpace β] [TotallyDisconnectedSpace α]
  body: ⟨fun t _ h2 =>
    have H1 : IsPreconnected (Prod.fst '' t) := h2.image Prod.fst continuous_fst.continuousOn
    have H2 : IsPreconnected (Prod.snd '' t) := h2.image Prod.snd continuous_snd.continuousOn
    fun x hx y hy =>
    Prod.ext (H1.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
      (H2.subsingle

中文:
实例 Prod.totallyDisconnectedSpace
  签名: [TopologicalSpace β] [TotallyDisconnectedSpace α]
  定义体: ⟨fun t _ h2 =>
    have H1 : IsPreconnected (Prod.fst '' t) := h2.image Prod.fst continuous_fst.continuousOn
    have H2 : IsPreconnected (Prod.snd '' t) := h2.image Prod.snd continuous_snd.continuousOn
    fun x hx y hy =>
    Prod.ext (H1.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
      (H2.subsingle

Depends on / 依赖: H1.subsingleton, H2.subsingleton, IsPreconnected, Prod.ext, Prod.fst, Prod.snd, continuousOn, continuous_fst, continuous_fst.continuousOn, continuous_snd, continuous_snd.continuousOn, h2.image, subsingleton
-/
instance Prod.totallyDisconnectedSpace [TopologicalSpace β] [TotallyDisconnectedSpace α]
    [TotallyDisconnectedSpace β] : TotallyDisconnectedSpace (α × β) :=
  ⟨fun t _ h2 =>
    have H1 : IsPreconnected (Prod.fst '' t) := h2.image Prod.fst continuous_fst.continuousOn
    have H2 : IsPreconnected (Prod.snd '' t) := h2.image Prod.snd continuous_snd.continuousOn
    fun x hx y hy =>
    Prod.ext (H1.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
      (H2.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: β] [TotallyDisconnectedSpace α] [TotallyDisconnectedSpace β] :
  body: by
  refine ⟨fun s _ hs => ?_⟩
  obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isPreconnected_iff.1 hs
  · exact ht.subsingleton.image _
  · exact ht.subsingleton.image _

中文:
实例 [TopologicalSpace
  签名: β] [TotallyDisconnectedSpace α] [TotallyDisconnectedSpace β] :
  定义体: by
  refine ⟨fun s _ hs => ?_⟩
  obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isPreconnected_iff.1 hs
  · exact ht.subsingleton.image _
  · exact ht.subsingleton.image _

Depends on / 依赖: Sum.isPreconnected_iff, ht.subsingleton.image, isPreconnected_iff, subsingleton
-/
instance [TopologicalSpace β] [TotallyDisconnectedSpace α] [TotallyDisconnectedSpace β] :
    TotallyDisconnectedSpace (α oplus β) := by
  refine ⟨fun s _ hs => ?_⟩
  obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isPreconnected_iff.1 hs
  · exact ht.subsingleton.image _
  · exact ht.subsingleton.image _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, TopologicalSpace (X i)] [forall i, TotallyDisconnectedSpace (X i)] :
  body: by
  refine ⟨fun s _ hs => ?_⟩
  obtain rfl | h := s.eq_empty_or_nonempty
  · exact subsingleton_empty
  · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
    exact ht.isPreconnected.subsingleton.image _

中文:
实例 [forall
  签名: i, TopologicalSpace (X i)] [对任意 i, TotallyDisconnectedSpace (X i)] :
  定义体: by
  refine ⟨fun s _ hs => ?_⟩
  obtain rfl | h := s.eq_empty_or_nonempty
  · exact subsingleton_empty
  · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
    exact ht.isPreconnected.subsingleton.image _

Depends on / 依赖: Sigma.isConnected_iff, eq_empty_or_nonempty, ht.isPreconnected.subsingleton.image, isConnected_iff, isPreconnected, s.eq_empty_or_nonempty, subsingleton, subsingleton_empty
-/
instance [forall i, TopologicalSpace (X i)] [forall i, TotallyDisconnectedSpace (X i)] :
    TotallyDisconnectedSpace (Σ i, X i) := by
  refine ⟨fun s _ hs => ?_⟩
  obtain rfl | h := s.eq_empty_or_nonempty
  · exact subsingleton_empty
  · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
    exact ht.isPreconnected.subsingleton.image _

/--
theorem `totallyDisconnectedSpace_iff_connectedComponent_subsingleton` / 定理 `totallyDisconnectedSpace_iff_connectedComponent_subsingleton`

English:
theorem totallyDisconnectedSpace_iff_connectedComponent_subsingleton
  proof: by
  constructor
  · intro h x
    apply h.1
    · exact subset_univ _
    exact isPreconnected_connectedComponent
  intro h; constructor
  intro s s_sub hs
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, x_in⟩)
  · exact subsingleton_empty
  · exact (h x).anti (hs.subset_connectedComponent x_in)

中文:
定理 totallyDisconnectedSpace_iff_connectedComponent_subsingleton
  证明: by
  constructor
  · intro h x
    apply h.1
    · exact subset_univ _
    exact isPreconnected_connectedComponent
  intro h; constructor
  intro s s_sub hs
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, x_in⟩)
  · exact subsingleton_empty
  · exact (h x).anti (hs.subset_connectedComponent x_in)

Depends on / 依赖: eq_empty_or_nonempty, hs.subset_connectedComponent, isPreconnected_connectedComponent, s_sub, subset_connectedComponent, subset_univ, subsingleton_empty, x_in
-/
theorem totallyDisconnectedSpace_iff_connectedComponent_subsingleton :
    TotallyDisconnectedSpace α ↔ forall x : α, (connectedComponent x).Subsingleton := by
  constructor
  · intro h x
    apply h.1
    · exact subset_univ _
    exact isPreconnected_connectedComponent
  intro h; constructor
  intro s s_sub hs
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, x_in⟩)
  · exact subsingleton_empty
  · exact (h x).anti (hs.subset_connectedComponent x_in)

/--
theorem `totallyDisconnectedSpace_iff_connectedComponent_singleton` / 定理 `totallyDisconnectedSpace_iff_connectedComponent_singleton`

English:
theorem totallyDisconnectedSpace_iff_connectedComponent_singleton
  proof: by
  rw [totallyDisconnectedSpace_iff_connectedComponent_subsingleton]
  refine forall_congr' fun x => ?_
  rw [subsingleton_iff_singleton]
  exact mem_connectedComponent

中文:
定理 totallyDisconnectedSpace_iff_connectedComponent_singleton
  证明: by
  rw [totallyDisconnectedSpace_iff_connectedComponent_subsingleton]
  refine forall_congr' fun x => ?_
  rw [subsingleton_iff_singleton]
  exact mem_connectedComponent

Depends on / 依赖: forall_congr, mem_connectedComponent, subsingleton_iff_singleton, totallyDisconnectedSpace_iff_connectedComponent_subsingleton
-/
theorem totallyDisconnectedSpace_iff_connectedComponent_singleton :
    TotallyDisconnectedSpace α ↔ forall x : α, connectedComponent x = {x} := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_subsingleton]
  refine forall_congr' fun x => ?_
  rw [subsingleton_iff_singleton]
  exact mem_connectedComponent

/--
theorem `connectedComponent_eq_singleton` / 定理 `connectedComponent_eq_singleton`

English:
theorem connectedComponent_eq_singleton
  given: [TotallyDisconnectedSpace α] (x : α)
  proof: totallyDisconnectedSpace_iff_connectedComponent_singleton.1 ‹_› x

中文:
定理 connectedComponent_eq_singleton
  条件: [TotallyDisconnectedSpace α] (x : α)
  证明: totallyDisconnectedSpace_iff_connectedComponent_singleton.1 ‹_› x
-/
@[simp] theorem connectedComponent_eq_singleton [TotallyDisconnectedSpace α] (x : α) :
    connectedComponent x = {x} :=
  totallyDisconnectedSpace_iff_connectedComponent_singleton.1 ‹_› x

/-- The image of a connected component in a totally disconnected space is a singleton. -/
@[simp]
/--
theorem `Continuous.image_connectedComponent_eq_singleton` / 定理 `Continuous.image_connectedComponent_eq_singleton`

English:
theorem Continuous.image_connectedComponent_eq_singleton
  statement: {β : Type*} [TopologicalSpace β]
  proof: (Set.subsingleton_iff_singleton <| mem_image_of_mem f mem_connectedComponent).mp
    (isPreconnected_connectedComponent.image f h.continuousOn).subsingleton

中文:
定理 Continuous.image_connectedComponent_eq_singleton
  结论: {β : 类型} [TopologicalSpace β]
  证明: (Set.subsingleton_iff_singleton <| mem_image_of_mem f mem_connectedComponent).mp
    (isPreconnected_connectedComponent.image f h.continuousOn).subsingleton

Depends on / 依赖: Set.subsingleton_iff_singleton, continuousOn, h.continuousOn, isPreconnected_connectedComponent, isPreconnected_connectedComponent.image, mem_connectedComponent, mem_image_of_mem, subsingleton, subsingleton_iff_singleton
-/
theorem Continuous.image_connectedComponent_eq_singleton {β : Type*} [TopologicalSpace β]
    [TotallyDisconnectedSpace β] {f : α -> β} (h : Continuous f) (a : α) :
    f '' connectedComponent a = {f a} :=
  (Set.subsingleton_iff_singleton <| mem_image_of_mem f mem_connectedComponent).mp
    (isPreconnected_connectedComponent.image f h.continuousOn).subsingleton

/--
theorem `isTotallyDisconnected_of_totallyDisconnectedSpace` / 定理 `isTotallyDisconnected_of_totallyDisconnectedSpace`

English:
theorem isTotallyDisconnected_of_totallyDisconnectedSpace
  given: [TotallyDisconnectedSpace α] (s : Set α)
  proof: fun t _ ht =>
  TotallyDisconnectedSpace.isTotallyDisconnected_univ _ t.subset_univ ht

中文:
定理 isTotallyDisconnected_of_totallyDisconnectedSpace
  条件: [TotallyDisconnectedSpace α] (s : Set α)
  证明: fun t _ ht =>
  TotallyDisconnectedSpace.isTotallyDisconnected_univ _ t.subset_univ ht
-/
theorem isTotallyDisconnected_of_totallyDisconnectedSpace [TotallyDisconnectedSpace α] (s : Set α) :
    IsTotallyDisconnected s := fun t _ ht =>
  TotallyDisconnectedSpace.isTotallyDisconnected_univ _ t.subset_univ ht

/--
lemma `TotallyDisconnectedSpace.eq_of_continuous` / 引理 `TotallyDisconnectedSpace.eq_of_continuous`

English:
lemma TotallyDisconnectedSpace.eq_of_continuous
  statement: [TopologicalSpace β]
  proof: (isPreconnected_univ.image f hf.continuousOn).subsingleton ⟨i, trivial, rfl⟩ ⟨j, trivial, rfl⟩

中文:
引理 TotallyDisconnectedSpace.eq_of_continuous
  结论: [TopologicalSpace β]
  证明: (isPreconnected_univ.image f hf.continuousOn).subsingleton ⟨i, trivial, rfl⟩ ⟨j, trivial, rfl⟩

Depends on / 依赖: continuousOn, hf.continuousOn, isPreconnected_univ, isPreconnected_univ.image, subsingleton
-/
lemma TotallyDisconnectedSpace.eq_of_continuous [TopologicalSpace β]
    [PreconnectedSpace α] [TotallyDisconnectedSpace β] (f : α -> β) (hf : Continuous f)
    (i j : α) : f i = f j :=
  (isPreconnected_univ.image f hf.continuousOn).subsingleton ⟨i, trivial, rfl⟩ ⟨j, trivial, rfl⟩

/-- The bijection `C(X, Y) ≃ Y` when `Y` is totally disconnected and `X` is connected. -/
@[simps! symm_apply_apply]
/--
Definition of `TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace` / `TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace` 的定义

English:
definition TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace
  body: f (Classical.arbitrary _)
  invFun y := ⟨fun _ => y, by fun_prop⟩
  left_inv f := ContinuousMap.ext (TotallyDisconnectedSpace.eq_of_continuous _ f.2 _)
  right_inv _ := rfl

中文:
定义 TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace
  定义体: f (Classical.arbitrary _)
  invFun y := ⟨fun _ => y, by fun_prop⟩
  left_inv f := ContinuousMap.ext (TotallyDisconnectedSpace.eq_of_continuous _ f.2 _)
  right_inv _ := rfl

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary
-/
noncomputable def TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace
    (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] [TotallyDisconnectedSpace Y] [ConnectedSpace X] :
    C(X, Y) ≃ Y where
  toFun f := f (Classical.arbitrary _)
  invFun y := ⟨fun _ => y, by fun_prop⟩
  left_inv f := ContinuousMap.ext (TotallyDisconnectedSpace.eq_of_continuous _ f.2 _)
  right_inv _ := rfl

/--
theorem `isTotallyDisconnected_of_image` / 定理 `isTotallyDisconnected_of_image`

English:
theorem isTotallyDisconnected_of_image
  statement: [TopologicalSpace β] {f : α -> β} (hf : ContinuousOn f s)
  proof: fun _t hts ht _x x_in _y y_in =>
hf'
    h _ (image_mono hts) (ht.image f <| hf.mono hts) (mem_image_of_mem f x_in)
      (mem_image_of_mem f y_in)

中文:
定理 isTotallyDisconnected_of_image
  结论: [TopologicalSpace β] {f : α -> β} (hf : ContinuousOn f s)
  证明: fun _t hts ht _x x_in _y y_in =>
hf'
    h _ (image_mono hts) (ht.image f <| hf.mono hts) (mem_image_of_mem f x_in)
      (mem_image_of_mem f y_in)

Depends on / 依赖: hf.mono, ht.image, image_mono, mem_image_of_mem, x_in, y_in
-/
theorem isTotallyDisconnected_of_image [TopologicalSpace β] {f : α -> β} (hf : ContinuousOn f s)
    (hf' : Injective f) (h : IsTotallyDisconnected (f '' s)) : IsTotallyDisconnected s :=
  fun _t hts ht _x x_in _y y_in =>
hf'
    h _ (image_mono hts) (ht.image f <| hf.mono hts) (mem_image_of_mem f x_in)
      (mem_image_of_mem f y_in)

/--
lemma `Topology.IsEmbedding.isTotallyDisconnected` / 引理 `Topology.IsEmbedding.isTotallyDisconnected`

English:
lemma Topology.IsEmbedding.isTotallyDisconnected
  statement: [TopologicalSpace β] {f : α -> β} {s : Set α}
  proof: isTotallyDisconnected_of_image hf.continuous.continuousOn hf.injective h

中文:
引理 Topology.IsEmbedding.isTotallyDisconnected
  结论: [TopologicalSpace β] {f : α -> β} {s : Set α}
  证明: isTotallyDisconnected_of_image hf.continuous.continuousOn hf.injective h

Depends on / 依赖: continuous, continuousOn, hf.continuous.continuousOn, hf.injective, injective, isTotallyDisconnected_of_image
-/
lemma Topology.IsEmbedding.isTotallyDisconnected [TopologicalSpace β] {f : α -> β} {s : Set α}
    (hf : IsEmbedding f) (h : IsTotallyDisconnected (f '' s)) : IsTotallyDisconnected s :=
  isTotallyDisconnected_of_image hf.continuous.continuousOn hf.injective h

/--
lemma `Topology.IsEmbedding.isTotallyDisconnected_image` / 引理 `Topology.IsEmbedding.isTotallyDisconnected_image`

English:
lemma Topology.IsEmbedding.isTotallyDisconnected_image
  statement: [TopologicalSpace β] {f : α -> β} {s : Set α}
  proof: by
  refine ⟨hf.isTotallyDisconnected, fun hs u hus hu => ?_⟩
  obtain ⟨v, hvs, rfl⟩ : exists v, v subseteq s ∧ f '' v = u :=
    ⟨f ⁻¹' u inter s, inter_subset_right, by rwa [image_preimage_inter, inter_eq_left]⟩
  rw [hf.isInducing.isPreconnected_image] at hu
  exact (hs v hvs hu).image _

中文:
引理 Topology.IsEmbedding.isTotallyDisconnected_image
  结论: [TopologicalSpace β] {f : α -> β} {s : Set α}
  证明: by
  refine ⟨hf.isTotallyDisconnected, fun hs u hus hu => ?_⟩
  obtain ⟨v, hvs, rfl⟩ : exists v, v subseteq s ∧ f '' v = u :=
    ⟨f ⁻¹' u inter s, inter_subset_right, by rwa [image_preimage_inter, inter_eq_left]⟩
  rw [hf.isInducing.isPreconnected_image] at hu
  exact (hs v hvs hu).image _

Depends on / 依赖: hf.isInducing.isPreconnected_image, hf.isTotallyDisconnected, image_preimage_inter, inter_eq_left, inter_subset_right, isInducing, isPreconnected_image, isTotallyDisconnected, subseteq
-/
lemma Topology.IsEmbedding.isTotallyDisconnected_image [TopologicalSpace β] {f : α -> β} {s : Set α}
    (hf : IsEmbedding f) : IsTotallyDisconnected (f '' s) ↔ IsTotallyDisconnected s := by
  refine ⟨hf.isTotallyDisconnected, fun hs u hus hu => ?_⟩
  obtain ⟨v, hvs, rfl⟩ : exists v, v subseteq s ∧ f '' v = u :=
    ⟨f ⁻¹' u inter s, inter_subset_right, by rwa [image_preimage_inter, inter_eq_left]⟩
  rw [hf.isInducing.isPreconnected_image] at hu
  exact (hs v hvs hu).image _

/--
lemma `Topology.IsEmbedding.isTotallyDisconnected_range` / 引理 `Topology.IsEmbedding.isTotallyDisconnected_range`

English:
lemma Topology.IsEmbedding.isTotallyDisconnected_range
  statement: [TopologicalSpace β] {f : α -> β}
  proof: by
  rw [totallyDisconnectedSpace_iff]; rw [← image_univ]; rw [hf.isTotallyDisconnected_image]

中文:
引理 Topology.IsEmbedding.isTotallyDisconnected_range
  结论: [TopologicalSpace β] {f : α -> β}
  证明: by
  rw [totallyDisconnectedSpace_iff]; rw [← image_univ]; rw [hf.isTotallyDisconnected_image]

Depends on / 依赖: hf.isTotallyDisconnected_image, image_univ, isTotallyDisconnected_image, totallyDisconnectedSpace_iff
-/
lemma Topology.IsEmbedding.isTotallyDisconnected_range [TopologicalSpace β] {f : α -> β}
    (hf : IsEmbedding f) : IsTotallyDisconnected (range f) ↔ TotallyDisconnectedSpace α := by
  rw [totallyDisconnectedSpace_iff]; rw [← image_univ]; rw [hf.isTotallyDisconnected_image]

/--
lemma `totallyDisconnectedSpace_subtype_iff` / 引理 `totallyDisconnectedSpace_subtype_iff`

English:
lemma totallyDisconnectedSpace_subtype_iff
  given: {s : Set α}
  proof: by
  rw [← IsEmbedding.subtypeVal.isTotallyDisconnected_range]; rw [Subtype.range_val]

中文:
引理 totallyDisconnectedSpace_subtype_iff
  条件: {s : Set α}
  证明: by
  rw [← IsEmbedding.subtypeVal.isTotallyDisconnected_range]; rw [Subtype.range_val]

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.isTotallyDisconnected_range, Subtype, Subtype.range_val, isTotallyDisconnected_range, range_val, subtypeVal
-/
lemma totallyDisconnectedSpace_subtype_iff {s : Set α} :
    TotallyDisconnectedSpace s ↔ IsTotallyDisconnected s := by
  rw [← IsEmbedding.subtypeVal.isTotallyDisconnected_range]; rw [Subtype.range_val]

/--
Instance `Subtype.totallyDisconnectedSpace` / 实例 `Subtype.totallyDisconnectedSpace`

English:
instance Subtype.totallyDisconnectedSpace
  signature: {α : Type*} {p : α -> Prop} [TopologicalSpace α]
  body: totallyDisconnectedSpace_subtype_iff.2 (isTotallyDisconnected_of_totallyDisconnectedSpace _)

中文:
实例 Subtype.totallyDisconnectedSpace
  签名: {α : 类型} {p : α -> 命题} [TopologicalSpace α]
  定义体: totallyDisconnectedSpace_subtype_iff.2 (isTotallyDisconnected_of_totallyDisconnectedSpace _)

Depends on / 依赖: isTotallyDisconnected_of_totallyDisconnectedSpace, totallyDisconnectedSpace_subtype_iff
-/
instance Subtype.totallyDisconnectedSpace {α : Type*} {p : α -> Prop} [TopologicalSpace α]
    [TotallyDisconnectedSpace α] : TotallyDisconnectedSpace (Subtype p) :=
  totallyDisconnectedSpace_subtype_iff.2 (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TotallyDisconnectedSpace
  signature: α] : TotallyDisconnectedSpace (Additive α)
  body: ‹TotallyDisconnectedSpace α›

中文:
实例 [TotallyDisconnectedSpace
  签名: α] : TotallyDisconnectedSpace (Additive α)
  定义体: ‹TotallyDisconnectedSpace α›

Depends on / 依赖: TotallyDisconnectedSpace
-/
instance [TotallyDisconnectedSpace α] : TotallyDisconnectedSpace (Additive α) :=
  ‹TotallyDisconnectedSpace α›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TotallyDisconnectedSpace
  signature: α] : TotallyDisconnectedSpace (Multiplicative α)
  body: ‹TotallyDisconnectedSpace α›

中文:
实例 [TotallyDisconnectedSpace
  签名: α] : TotallyDisconnectedSpace (Multiplicative α)
  定义体: ‹TotallyDisconnectedSpace α›

Depends on / 依赖: TotallyDisconnectedSpace
-/
instance [TotallyDisconnectedSpace α] : TotallyDisconnectedSpace (Multiplicative α) :=
  ‹TotallyDisconnectedSpace α›

end TotallyDisconnected

section TotallySeparated

/--
Definition of `IsTotallySeparated` / `IsTotallySeparated` 的定义

English:
definition IsTotallySeparated
  signature: (s : Set α)
  body: Set.Pairwise s fun x y =>
  exists u v : Set α, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ s subseteq u union v ∧ Disjoint u v

中文:
定义 IsTotallySeparated
  签名: (s : Set α)
  定义体: Set.Pairwise s fun x y =>
  exists u v : Set α, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ s subseteq u union v ∧ Disjoint u v

Depends on / 依赖: Disjoint, IsOpen, Pairwise, Set.Pairwise, subseteq
-/
def IsTotallySeparated (s : Set α) : Prop :=
  Set.Pairwise s fun x y =>
  exists u v : Set α, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ s subseteq u union v ∧ Disjoint u v

/--
theorem `isTotallySeparated_empty` / 定理 `isTotallySeparated_empty`

English:
theorem isTotallySeparated_empty
  statement: IsTotallySeparated (∅ : Set α)
  proof: fun _ => False.elim

中文:
定理 isTotallySeparated_empty
  结论: IsTotallySeparated (∅ : Set α)
  证明: fun _ => False.elim

Depends on / 依赖: False.elim
-/
theorem isTotallySeparated_empty : IsTotallySeparated (∅ : Set α) := fun _ => False.elim

/--
theorem `isTotallySeparated_singleton` / 定理 `isTotallySeparated_singleton`

English:
theorem isTotallySeparated_singleton
  given: {x}
  statement: IsTotallySeparated ({x} : Set α)
  proof: fun _ hp _ hq hpq =>
  (hpq <| (eq_of_mem_singleton hp).symm ▸ (eq_of_mem_singleton hq).symm).elim

中文:
定理 isTotallySeparated_singleton
  条件: {x}
  结论: IsTotallySeparated ({x} : Set α)
  证明: fun _ hp _ hq hpq =>
  (hpq <| (eq_of_mem_singleton hp).symm ▸ (eq_of_mem_singleton hq).symm).elim
-/
theorem isTotallySeparated_singleton {x} : IsTotallySeparated ({x} : Set α) := fun _ hp _ hq hpq =>
  (hpq <| (eq_of_mem_singleton hp).symm ▸ (eq_of_mem_singleton hq).symm).elim

/--
theorem `isTotallyDisconnected_of_isTotallySeparated` / 定理 `isTotallyDisconnected_of_isTotallySeparated`

English:
theorem isTotallyDisconnected_of_isTotallySeparated
  given: {s : Set α} (H : IsTotallySeparated s)
  proof: by
  intro t hts ht x x_in y y_in
  by_contra h
  obtain
    ⟨u : Set α, v : Set α, hu : IsOpen u, hv : IsOpen v, hxu : x in u, hyv : y in v, hs : s subseteq u union v,
      huv⟩ :=
    H (hts x_in) (hts y_in) h
  refine (ht _ _ hu hv (hts.trans hs) ⟨x, x_in, hxu⟩ ⟨y, y_in, hyv⟩).ne_empty ?_
  rw [

中文:
定理 isTotallyDisconnected_of_isTotallySeparated
  条件: {s : Set α} (H : IsTotallySeparated s)
  证明: by
  intro t hts ht x x_in y y_in
  by_contra h
  obtain
    ⟨u : Set α, v : Set α, hu : IsOpen u, hv : IsOpen v, hxu : x in u, hyv : y in v, hs : s subseteq u union v,
      huv⟩ :=
    H (hts x_in) (hts y_in) h
  refine (ht _ _ hu hv (hts.trans hs) ⟨x, x_in, hxu⟩ ⟨y, y_in, hyv⟩).ne_empty ?_
  rw [

Depends on / 依赖: IsOpen, hts.trans, huv.inter_eq, inter_empty, inter_eq, ne_empty, subseteq, x_in, y_in
-/
theorem isTotallyDisconnected_of_isTotallySeparated {s : Set α} (H : IsTotallySeparated s) :
    IsTotallyDisconnected s := by
  intro t hts ht x x_in y y_in
  by_contra h
  obtain
    ⟨u : Set α, v : Set α, hu : IsOpen u, hv : IsOpen v, hxu : x in u, hyv : y in v, hs : s subseteq u union v,
      huv⟩ :=
    H (hts x_in) (hts y_in) h
  refine (ht _ _ hu hv (hts.trans hs) ⟨x, x_in, hxu⟩ ⟨y, y_in, hyv⟩).ne_empty ?_
  rw [huv.inter_eq]; rw [inter_empty]

alias IsTotallySeparated.isTotallyDisconnected := isTotallyDisconnected_of_isTotallySeparated

/--
Definition of `TotallySeparatedSpace` / `TotallySeparatedSpace` 的定义

English:
class TotallySeparatedSpace
  parameters: (α : Type u) [TopologicalSpace α]
  axioms and operations (1):
    - isTotallySeparated_univ : IsTotallySeparated (univ : Set α)

中文:
类 TotallySeparatedSpace
  参数: (α : 类型u) [TopologicalSpace α]
  公理与运算 (1 个):
    - isTotallySeparated_univ : IsTotallySeparated (univ : Set α)
-/
@[mk_iff] class TotallySeparatedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a totally separated space is totally separated. -/
  isTotallySeparated_univ : IsTotallySeparated (univ : Set α)

-- see Note [lower instance priority]
instance (priority := 100) TotallySeparatedSpace.totallyDisconnectedSpace (α : Type u)
    [TopologicalSpace α] [TotallySeparatedSpace α] : TotallyDisconnectedSpace α :=
  ⟨TotallySeparatedSpace.isTotallySeparated_univ.isTotallyDisconnected⟩

-- see Note [lower instance priority]
instance (priority := 100) TotallySeparatedSpace.of_discrete (α : Type*) [TopologicalSpace α]
    [DiscreteTopology α] : TotallySeparatedSpace α :=
  ⟨fun _ _ b _ h => ⟨{b}ᶜ, {b}, isOpen_discrete _, isOpen_discrete _, h, rfl,
    (compl_union_self _).symm.subset, disjoint_compl_left⟩⟩

/--
theorem `totallySeparatedSpace_iff_exists_isClopen` / 定理 `totallySeparatedSpace_iff_exists_isClopen`

English:
theorem totallySeparatedSpace_iff_exists_isClopen
  given: {α : Type*} [TopologicalSpace α]
  proof: by
  simp only [totallySeparatedSpace_iff, IsTotallySeparated, Set.Pairwise, mem_univ, true_implies]
  refine forall₃_congr fun x y _ =>
    ⟨fun ⟨U, V, hU, hV, Ux, Vy, f, disj⟩ => ?_, fun ⟨U, hU, Ux, Ucy⟩ => ?_⟩
  · exact ⟨U, isClopen_of_disjoint_cover_open f hU hV disj,
      Ux, fun Uy => Set.dis

中文:
定理 totallySeparatedSpace_iff_exists_isClopen
  条件: {α : 类型} [TopologicalSpace α]
  证明: by
  simp only [totallySeparatedSpace_iff, IsTotallySeparated, Set.Pairwise, mem_univ, true_implies]
  refine forall₃_congr fun x y _ =>
    ⟨fun ⟨U, V, hU, hV, Ux, Vy, f, disj⟩ => ?_, fun ⟨U, hU, Ux, Ucy⟩ => ?_⟩
  · exact ⟨U, isClopen_of_disjoint_cover_open f hU hV disj,
      Ux, fun Uy => Set.dis

Depends on / 依赖: IsTotallySeparated, Pairwise, Set.Pairwise, Set.disjoint_iff.mp, Set.union_compl_self, disjoint_compl_right, disjoint_iff, hU.compl, isClopen_of_disjoint_cover_open, mem_univ, totallySeparatedSpace_iff, true_implies, union_compl_self
-/
theorem totallySeparatedSpace_iff_exists_isClopen {α : Type*} [TopologicalSpace α] :
    TotallySeparatedSpace α ↔ Pairwise (exists U : Set α, IsClopen U ∧ · in U ∧ · in Uᶜ) := by
  simp only [totallySeparatedSpace_iff, IsTotallySeparated, Set.Pairwise, mem_univ, true_implies]
  refine forall₃_congr fun x y _ =>
    ⟨fun ⟨U, V, hU, hV, Ux, Vy, f, disj⟩ => ?_, fun ⟨U, hU, Ux, Ucy⟩ => ?_⟩
  · exact ⟨U, isClopen_of_disjoint_cover_open f hU hV disj,
      Ux, fun Uy => Set.disjoint_iff.mp disj ⟨Uy, Vy⟩⟩
  · exact ⟨U, Uᶜ, hU.2, hU.compl.2, Ux, Ucy, (Set.union_compl_self U).ge, disjoint_compl_right⟩

/--
theorem `exists_isClopen_of_totally_separated` / 定理 `exists_isClopen_of_totally_separated`

English:
theorem exists_isClopen_of_totally_separated
  statement: {α : Type*} [TopologicalSpace α]
  proof: totallySeparatedSpace_iff_exists_isClopen.mp ‹_›

中文:
定理 exists_isClopen_of_totally_separated
  结论: {α : 类型} [TopologicalSpace α]
  证明: totallySeparatedSpace_iff_exists_isClopen.mp ‹_›

Depends on / 依赖: totallySeparatedSpace_iff_exists_isClopen, totallySeparatedSpace_iff_exists_isClopen.mp
-/
theorem exists_isClopen_of_totally_separated {α : Type*} [TopologicalSpace α]
    [TotallySeparatedSpace α] : Pairwise (exists U : Set α, IsClopen U ∧ · in U ∧ · in Uᶜ) :=
  totallySeparatedSpace_iff_exists_isClopen.mp ‹_›

end TotallySeparated


variable [TopologicalSpace β] [TotallyDisconnectedSpace β] {f : α -> β}

/--
theorem `Continuous.image_eq_of_connectedComponent_eq` / 定理 `Continuous.image_eq_of_connectedComponent_eq`

English:
theorem Continuous.image_eq_of_connectedComponent_eq
  statement: (h : Continuous f) (a b : α)
  proof: singleton_eq_singleton_iff.1
    h.image_connectedComponent_eq_singleton a ▸
      h.image_connectedComponent_eq_singleton b ▸ hab ▸ rfl

中文:
定理 Continuous.image_eq_of_connectedComponent_eq
  结论: (h : Continuous f) (a b : α)
  证明: singleton_eq_singleton_iff.1
    h.image_connectedComponent_eq_singleton a ▸
      h.image_connectedComponent_eq_singleton b ▸ hab ▸ rfl

Depends on / 依赖: h.image_connectedComponent_eq_singleton, image_connectedComponent_eq_singleton, singleton_eq_singleton_iff
-/
theorem Continuous.image_eq_of_connectedComponent_eq (h : Continuous f) (a b : α)
    (hab : connectedComponent a = connectedComponent b) : f a = f b :=
singleton_eq_singleton_iff.1
    h.image_connectedComponent_eq_singleton a ▸
      h.image_connectedComponent_eq_singleton b ▸ hab ▸ rfl

/--
Definition of `Continuous.connectedComponentsLift` / `Continuous.connectedComponentsLift` 的定义

English:
definition Continuous.connectedComponentsLift
  signature: (h : Continuous f)
  body: fun x =>
  Quotient.liftOn' x f h.image_eq_of_connectedComponent_eq

@[continuity]

中文:
定义 Continuous.connectedComponentsLift
  签名: (h : Continuous f)
  定义体: fun x =>
  Quotient.liftOn' x f h.image_eq_of_connectedComponent_eq

@[continuity]
-/
def Continuous.connectedComponentsLift (h : Continuous f) : ConnectedComponents α -> β := fun x =>
  Quotient.liftOn' x f h.image_eq_of_connectedComponent_eq

@[continuity]
/--
theorem `Continuous.connectedComponentsLift_continuous` / 定理 `Continuous.connectedComponentsLift_continuous`

English:
theorem Continuous.connectedComponentsLift_continuous
  given: (h : Continuous f)
  proof: h.quotient_liftOn' by convert! h.image_eq_of_connectedComponent_eq

@[simp]

中文:
定理 Continuous.connectedComponentsLift_continuous
  条件: (h : Continuous f)
  证明: h.quotient_liftOn' by convert! h.image_eq_of_connectedComponent_eq

@[simp]

Depends on / 依赖: convert, h.image_eq_of_connectedComponent_eq, h.quotient_liftOn, image_eq_of_connectedComponent_eq, quotient_liftOn
-/
theorem Continuous.connectedComponentsLift_continuous (h : Continuous f) :
    Continuous h.connectedComponentsLift :=
h.quotient_liftOn' by convert! h.image_eq_of_connectedComponent_eq

@[simp]
/--
theorem `Continuous.connectedComponentsLift_apply_coe` / 定理 `Continuous.connectedComponentsLift_apply_coe`

English:
theorem Continuous.connectedComponentsLift_apply_coe
  given: (h : Continuous f) (x : α)
  proof: rfl

@[simp]

中文:
定理 Continuous.connectedComponentsLift_apply_coe
  条件: (h : Continuous f) (x : α)
  证明: rfl

@[simp]
-/
theorem Continuous.connectedComponentsLift_apply_coe (h : Continuous f) (x : α) :
    h.connectedComponentsLift x = f x :=
  rfl

@[simp]
/--
theorem `Continuous.connectedComponentsLift_comp_coe` / 定理 `Continuous.connectedComponentsLift_comp_coe`

English:
theorem Continuous.connectedComponentsLift_comp_coe
  given: (h : Continuous f)
  proof: rfl

中文:
定理 Continuous.connectedComponentsLift_comp_coe
  条件: (h : Continuous f)
  证明: rfl
-/
theorem Continuous.connectedComponentsLift_comp_coe (h : Continuous f) :
    h.connectedComponentsLift ∘ (↑) = f :=
  rfl

/--
theorem `connectedComponents_lift_unique'` / 定理 `connectedComponents_lift_unique'`

English:
theorem connectedComponents_lift_unique'
  statement: {β : Sort*} {g₁ g₂ : ConnectedComponents α -> β}
  proof: ConnectedComponents.surjective_coe.injective_comp_right hg

中文:
定理 connectedComponents_lift_unique'
  结论: {β : Sort*} {g₁ g₂ : ConnectedComponents α -> β}
  证明: ConnectedComponents.surjective_coe.injective_comp_right hg

Depends on / 依赖: ConnectedComponents, ConnectedComponents.surjective_coe.injective_comp_right, injective_comp_right, surjective_coe
-/
theorem connectedComponents_lift_unique' {β : Sort*} {g₁ g₂ : ConnectedComponents α -> β}
    (hg : g₁ ∘ ((↑) : α -> ConnectedComponents α) = g₂ ∘ (↑)) : g₁ = g₂ :=
  ConnectedComponents.surjective_coe.injective_comp_right hg

/--
theorem `Continuous.connectedComponentsLift_unique` / 定理 `Continuous.connectedComponentsLift_unique`

English:
theorem Continuous.connectedComponentsLift_unique
  statement: (h : Continuous f) (g : ConnectedComponents α -> β)
  proof: connectedComponents_lift_unique' hg.trans h.connectedComponentsLift_comp_coe.symm

中文:
定理 Continuous.connectedComponentsLift_unique
  结论: (h : Continuous f) (g : ConnectedComponents α -> β)
  证明: connectedComponents_lift_unique' hg.trans h.connectedComponentsLift_comp_coe.symm

Depends on / 依赖: connectedComponentsLift_comp_coe, connectedComponents_lift_unique, h.connectedComponentsLift_comp_coe.symm, hg.trans
-/
theorem Continuous.connectedComponentsLift_unique (h : Continuous f) (g : ConnectedComponents α -> β)
    (hg : g ∘ (↑) = f) : g = h.connectedComponentsLift :=
connectedComponents_lift_unique' hg.trans h.connectedComponentsLift_comp_coe.symm

/--
Instance `ConnectedComponents.totallyDisconnectedSpace` / 实例 `ConnectedComponents.totallyDisconnectedSpace`

English:
instance ConnectedComponents.totallyDisconnectedSpace
  signature: :
  body: by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  refine ConnectedComponents.surjective_coe.forall.2 fun x => ?_
  rw [← ConnectedComponents.isQuotientMap_coe.image_connectedComponent]; rw [←
    connectedComponents_preimage_singleton]; rw [image_preimage_eq _ ConnectedComponents

中文:
实例 ConnectedComponents.totallyDisconnectedSpace
  签名: :
  定义体: by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  refine ConnectedComponents.surjective_coe.forall.2 fun x => ?_
  rw [← ConnectedComponents.isQuotientMap_coe.image_connectedComponent]; rw [←
    connectedComponents_preimage_singleton]; rw [image_preimage_eq _ ConnectedComponents

Depends on / 依赖: ConnectedComponents, ConnectedComponents.isQuotientMap_coe.image_connectedComponent, ConnectedComponents.surjective_coe, ConnectedComponents.surjective_coe.forall, connectedComponents_preimage_singleton, image_connectedComponent, image_preimage_eq, isConnected_connectedComponent, isQuotientMap_coe, surjective_coe, totallyDisconnectedSpace_iff_connectedComponent_singleton
-/
instance ConnectedComponents.totallyDisconnectedSpace :
    TotallyDisconnectedSpace (ConnectedComponents α) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  refine ConnectedComponents.surjective_coe.forall.2 fun x => ?_
  rw [← ConnectedComponents.isQuotientMap_coe.image_connectedComponent]; rw [←
    connectedComponents_preimage_singleton]; rw [image_preimage_eq _ ConnectedComponents.surjective_coe]
  refine ConnectedComponents.surjective_coe.forall.2 fun y => ?_
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

/--
Definition of `Continuous.connectedComponentsMap` / `Continuous.connectedComponentsMap` 的定义

English:
definition Continuous.connectedComponentsMap
  signature: {β : Type*} [TopologicalSpace β] {f : α -> β}
  body: Continuous.connectedComponentsLift (ConnectedComponents.continuous_coe.comp h)

@[simp]

中文:
定义 Continuous.connectedComponentsMap
  签名: {β : 类型} [TopologicalSpace β] {f : α -> β}
  定义体: Continuous.connectedComponentsLift (ConnectedComponents.continuous_coe.comp h)

@[simp]

Depends on / 依赖: ConnectedComponents, ConnectedComponents.continuous_coe.comp, Continuous, Continuous.connectedComponentsLift, connectedComponentsLift, continuous_coe
-/
def Continuous.connectedComponentsMap {β : Type*} [TopologicalSpace β] {f : α -> β}
    (h : Continuous f) : ConnectedComponents α -> ConnectedComponents β :=
  Continuous.connectedComponentsLift (ConnectedComponents.continuous_coe.comp h)

@[simp]
/--
lemma `Continuous.connectedComponentsMap_mk` / 引理 `Continuous.connectedComponentsMap_mk`

English:
lemma Continuous.connectedComponentsMap_mk
  statement: {β : Type*} [TopologicalSpace β] {f : α -> β}
  proof: rfl

中文:
引理 Continuous.connectedComponentsMap_mk
  结论: {β : 类型} [TopologicalSpace β] {f : α -> β}
  证明: rfl
-/
lemma Continuous.connectedComponentsMap_mk {β : Type*} [TopologicalSpace β] {f : α -> β}
    (hf : Continuous f) (x : α) :
    hf.connectedComponentsMap (.mk x) = .mk (f x) :=
  rfl

/--
theorem `Continuous.connectedComponentsMap_continuous` / 定理 `Continuous.connectedComponentsMap_continuous`

English:
theorem Continuous.connectedComponentsMap_continuous
  statement: {β : Type*} [TopologicalSpace β] {f : α -> β}
  proof: Continuous.connectedComponentsLift_continuous (ConnectedComponents.continuous_coe.comp h)

中文:
定理 Continuous.connectedComponentsMap_continuous
  结论: {β : 类型} [TopologicalSpace β] {f : α -> β}
  证明: Continuous.connectedComponentsLift_continuous (ConnectedComponents.continuous_coe.comp h)

Depends on / 依赖: ConnectedComponents, ConnectedComponents.continuous_coe.comp, Continuous, Continuous.connectedComponentsLift_continuous, connectedComponentsLift_continuous, continuous_coe
-/
theorem Continuous.connectedComponentsMap_continuous {β : Type*} [TopologicalSpace β] {f : α -> β}
    (h : Continuous f) : Continuous h.connectedComponentsMap :=
  Continuous.connectedComponentsLift_continuous (ConnectedComponents.continuous_coe.comp h)

/--
lemma `Topology.IsCoinducing.connectedComponentsMap` / 引理 `Topology.IsCoinducing.connectedComponentsMap`

English:
lemma Topology.IsCoinducing.connectedComponentsMap
  statement: {β : Type*} [TopologicalSpace β] {f : α -> β}
  proof: by
  rw [← ConnectedComponents.isQuotientMap_coe.isCoinducing.of_comp_iff]
  exact ConnectedComponents.isQuotientMap_coe.isCoinducing.comp hf

@[simp]

中文:
引理 Topology.IsCoinducing.connectedComponentsMap
  结论: {β : 类型} [TopologicalSpace β] {f : α -> β}
  证明: by
  rw [← ConnectedComponents.isQuotientMap_coe.isCoinducing.of_comp_iff]
  exact ConnectedComponents.isQuotientMap_coe.isCoinducing.comp hf

@[simp]

Depends on / 依赖: ConnectedComponents, ConnectedComponents.isQuotientMap_coe.isCoinducing.comp, ConnectedComponents.isQuotientMap_coe.isCoinducing.of_comp_iff, isCoinducing, isQuotientMap_coe, of_comp_iff
-/
lemma Topology.IsCoinducing.connectedComponentsMap {β : Type*} [TopologicalSpace β] {f : α -> β}
    (hf : IsCoinducing f) :
    IsCoinducing hf.continuous.connectedComponentsMap := by
  rw [← ConnectedComponents.isQuotientMap_coe.isCoinducing.of_comp_iff]
  exact ConnectedComponents.isQuotientMap_coe.isCoinducing.comp hf

@[simp]
/--
lemma `Continuous.connectedComponentsMap_surjective` / 引理 `Continuous.connectedComponentsMap_surjective`

English:
lemma Continuous.connectedComponentsMap_surjective
  statement: {β : Type*} [TopologicalSpace β] {f : α -> β}
  proof: Quotient.lift_surjective _ _ ConnectedComponents.surjective_coe.comp h

中文:
引理 Continuous.connectedComponentsMap_surjective
  结论: {β : 类型} [TopologicalSpace β] {f : α -> β}
  证明: Quotient.lift_surjective _ _ ConnectedComponents.surjective_coe.comp h

Depends on / 依赖: ConnectedComponents, ConnectedComponents.surjective_coe.comp, Quotient, Quotient.lift_surjective, lift_surjective, surjective_coe
-/
lemma Continuous.connectedComponentsMap_surjective {β : Type*} [TopologicalSpace β] {f : α -> β}
    (hf : Continuous f) (h : Surjective f) :
    Surjective hf.connectedComponentsMap :=
Quotient.lift_surjective _ _ ConnectedComponents.surjective_coe.comp h

/--
lemma `Topology.IsCoinducing.connectedComponentsMap_bijective` / 引理 `Topology.IsCoinducing.connectedComponentsMap_bijective`

English:
lemma Topology.IsCoinducing.connectedComponentsMap_bijective
  statement: {β : Type*} [TopologicalSpace β]
  proof: by
  refine ⟨fun x y h => ?_, Continuous.connectedComponentsMap_surjective _ fun y => (hf' y).nonempty⟩
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
  simp_all [← hf.preimage_connectedComponent hf']

中文:
引理 Topology.IsCoinducing.connectedComponentsMap_bijective
  结论: {β : 类型} [TopologicalSpace β]
  证明: by
  refine ⟨fun x y h => ?_, Continuous.connectedComponentsMap_surjective _ fun y => (hf' y).nonempty⟩
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
  simp_all [← hf.preimage_connectedComponent hf']

Depends on / 依赖: ConnectedComponents, ConnectedComponents.surjective_coe, Continuous, Continuous.connectedComponentsMap_surjective, connectedComponentsMap_surjective, hf.preimage_connectedComponent, nonempty, preimage_connectedComponent, surjective_coe
-/
lemma Topology.IsCoinducing.connectedComponentsMap_bijective {β : Type*} [TopologicalSpace β]
    {f : α -> β} (hf : IsCoinducing f) (hf' : forall y, IsConnected (f ⁻¹' {y})) :
    hf.continuous.connectedComponentsMap.Bijective := by
  refine ⟨fun x y h => ?_, Continuous.connectedComponentsMap_surjective _ fun y => (hf' y).nonempty⟩
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
  simp_all [← hf.preimage_connectedComponent hf']

/--
theorem `IsPreconnected.constant` / 定理 `IsPreconnected.constant`

English:
theorem IsPreconnected.constant
  statement: {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y] {s : Set α}
  proof: (hs.image f hf).subsingleton (mem_image_of_mem f hx) (mem_image_of_mem f hy)

中文:
定理 IsPreconnected.constant
  结论: {Y : 类型} [TopologicalSpace Y] [DiscreteTopology Y] {s : Set α}
  证明: (hs.image f hf).subsingleton (mem_image_of_mem f hx) (mem_image_of_mem f hy)

Depends on / 依赖: hs.image, mem_image_of_mem, subsingleton
-/
theorem IsPreconnected.constant {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y] {s : Set α}
    (hs : IsPreconnected s) {f : α -> Y} (hf : ContinuousOn f s) {x y : α} (hx : x in s)
    (hy : y in s) : f x = f y :=
  (hs.image f hf).subsingleton (mem_image_of_mem f hx) (mem_image_of_mem f hy)

/--
theorem `PreconnectedSpace.constant` / 定理 `PreconnectedSpace.constant`

English:
theorem PreconnectedSpace.constant
  statement: {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y]
  proof: IsPreconnected.constant hp.isPreconnected_univ (Continuous.continuousOn hf) trivial trivial

中文:
定理 PreconnectedSpace.constant
  结论: {Y : 类型} [TopologicalSpace Y] [DiscreteTopology Y]
  证明: IsPreconnected.constant hp.isPreconnected_univ (Continuous.continuousOn hf) trivial trivial

Depends on / 依赖: Continuous, Continuous.continuousOn, IsPreconnected, IsPreconnected.constant, constant, continuousOn, hp.isPreconnected_univ, isPreconnected_univ
-/
theorem PreconnectedSpace.constant {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y]
    (hp : PreconnectedSpace α) {f : α -> Y} (hf : Continuous f) {x y : α} : f x = f y :=
  IsPreconnected.constant hp.isPreconnected_univ (Continuous.continuousOn hf) trivial trivial

/--
theorem `IsPreconnected.constant_of_mapsTo` / 定理 `IsPreconnected.constant_of_mapsTo`

English:
theorem IsPreconnected.constant_of_mapsTo
  statement: {S : Set α} (hS : IsPreconnected S)
  proof: by
  let F : S -> T := hTm.restrict f S T
  suffices F ⟨x, hx⟩ = F ⟨y, hy⟩ by rwa [← Subtype.coe_inj] at this
  rw [isDiscrete_iff_discreteTopology] at hT
  exact (isPreconnected_iff_preconnectedSpace.mp hS).constant (hc.mapsToRestrict _)

中文:
定理 IsPreconnected.constant_of_mapsTo
  结论: {S : Set α} (hS : IsPreconnected S)
  证明: by
  let F : S -> T := hTm.restrict f S T
  suffices F ⟨x, hx⟩ = F ⟨y, hy⟩ by rwa [← Subtype.coe_inj] at this
  rw [isDiscrete_iff_discreteTopology] at hT
  exact (isPreconnected_iff_preconnectedSpace.mp hS).constant (hc.mapsToRestrict _)

Depends on / 依赖: Subtype, Subtype.coe_inj, coe_inj, constant, hTm.restrict, hc.mapsToRestrict, isDiscrete_iff_discreteTopology, isPreconnected_iff_preconnectedSpace, isPreconnected_iff_preconnectedSpace.mp, mapsToRestrict, restrict
-/
theorem IsPreconnected.constant_of_mapsTo {S : Set α} (hS : IsPreconnected S)
    {β} [TopologicalSpace β] {T : Set β} (hT : IsDiscrete T) {f : α -> β} (hc : ContinuousOn f S)
    (hTm : MapsTo f S T) {x y : α} (hx : x in S) (hy : y in S) : f x = f y := by
  let F : S -> T := hTm.restrict f S T
  suffices F ⟨x, hx⟩ = F ⟨y, hy⟩ by rwa [← Subtype.coe_inj] at this
  rw [isDiscrete_iff_discreteTopology] at hT
  exact (isPreconnected_iff_preconnectedSpace.mp hS).constant (hc.mapsToRestrict _)

/--
theorem `IsPreconnected.eqOn_const_of_mapsTo` / 定理 `IsPreconnected.eqOn_const_of_mapsTo`

English:
theorem IsPreconnected.eqOn_const_of_mapsTo
  statement: {S : Set α} (hS : IsPreconnected S)
  proof: by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨x, hx⟩)
  · exact hne.imp fun _ hy => ⟨hy, eqOn_empty _ _⟩
  · exact ⟨f x, hTm hx, fun x' hx' => hS.constant_of_mapsTo hT hc hTm hx' hx⟩

中文:
定理 IsPreconnected.eqOn_const_of_mapsTo
  结论: {S : Set α} (hS : IsPreconnected S)
  证明: by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨x, hx⟩)
  · exact hne.imp fun _ hy => ⟨hy, eqOn_empty _ _⟩
  · exact ⟨f x, hTm hx, fun x' hx' => hS.constant_of_mapsTo hT hc hTm hx' hx⟩

Depends on / 依赖: S.eq_empty_or_nonempty, constant_of_mapsTo, eqOn_empty, eq_empty_or_nonempty, hS.constant_of_mapsTo, hne.imp
-/
theorem IsPreconnected.eqOn_const_of_mapsTo {S : Set α} (hS : IsPreconnected S)
    {β} [TopologicalSpace β] {T : Set β} (hT : IsDiscrete T) {f : α -> β} (hc : ContinuousOn f S)
    (hTm : MapsTo f S T) (hne : T.Nonempty) : exists y in T, EqOn f (const α y) S := by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨x, hx⟩)
  · exact hne.imp fun _ hy => ⟨hy, eqOn_empty _ _⟩
  · exact ⟨f x, hTm hx, fun x' hx' => hS.constant_of_mapsTo hT hc hTm hx' hx⟩

/--
theorem `IsPreconnected.isDiscrete_iff_subsingleton` / 定理 `IsPreconnected.isDiscrete_iff_subsingleton`

English:
theorem IsPreconnected.isDiscrete_iff_subsingleton
  given: {S : Set α} (hS : IsPreconnected S)
  proof: by
    have : DiscreteTopology S := isDiscrete_iff_discreteTopology.mp h
    have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
    have : Subsingleton S := subsingleton_of_preconnected_totallyDisconnected
    simpa using this
  mpr h := h.isDiscrete

中文:
定理 IsPreconnected.isDiscrete_iff_subsingleton
  条件: {S : Set α} (hS : IsPreconnected S)
  证明: by
    have : DiscreteTopology S := isDiscrete_iff_discreteTopology.mp h
    have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
    have : Subsingleton S := subsingleton_of_preconnected_totallyDisconnected
    simpa using this
  mpr h := h.isDiscrete

Depends on / 依赖: DiscreteTopology, PreconnectedSpace, Subsingleton, h.isDiscrete, isDiscrete, isDiscrete_iff_discreteTopology, isDiscrete_iff_discreteTopology.mp, isPreconnected_iff_preconnectedSpace, isPreconnected_iff_preconnectedSpace.mp, subsingleton_of_preconnected_totallyDisconnected
-/
theorem IsPreconnected.isDiscrete_iff_subsingleton {S : Set α} (hS : IsPreconnected S) :
    IsDiscrete S ↔ S.Subsingleton where
  mp h := by
    have : DiscreteTopology S := isDiscrete_iff_discreteTopology.mp h
    have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
    have : Subsingleton S := subsingleton_of_preconnected_totallyDisconnected
    simpa using this
  mpr h := h.isDiscrete
