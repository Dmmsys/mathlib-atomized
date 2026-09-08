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

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι → Type*} [TopologicalSpace α]
  {s t u v : Set α}

section TotallyDisconnected

/-- A set `s` is called totally disconnected if every subset `t ⊆ s` which is preconnected is
a subsingleton, i.e. either empty or a singleton. -/
/-
**IsTotallyDisconnected** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsTotallyDisconnected (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is called totally disconnected if every subset `t ⊆ s` which is precon
nected is
a subsingleton, i.e. either empty or a singleton.
-/
def IsTotallyDisconnected (s : Set α) : Prop :=
  ∀ t, t ⊆ s → IsPreconnected t → t.Subsingleton
/-
**isTotallyDisconnected_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTotallyDisconnected_empty : IsTotallyDisconnected (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isTotallyDisconnected_empty : IsTotallyDisconnected (∅ : Set α) := fun _ ht _ _ x_in _ _ =>
  (ht x_in).elim
/-
**isTotallyDisconnected_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTotallyDisconnected_singleton {x} : IsTotallyDisconnected ({x} : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.anti`：∀ {α : Type u} {s t : Set α}, t.Subsingleton → s 
⊆ t → s.Subsingleton
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem isTotallyDisconnected_singleton {x} : IsTotallyDisconnected ({x} : Set α) := fun _ ht _ =>
  subsingleton_singleton.anti ht

/-- A space is totally disconnected if all of its connected components are singletons. -/
@[mk_iff]
/-
**TotallyDisconnectedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A space is totally disconnected if all of its connected components are singleton
s.
-/
class TotallyDisconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a totally disconnected space is totally disconnected. -/
  isTotallyDisconnected_univ : IsTotallyDisconnected (univ : Set α)
/-
**IsPreconnected.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.subsingleton [TotallyDisconnectedSpace α] {s : Set α} (h : 
IsPreconnected s) : s.Subsingleton
参数：h : IsPreconnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyDisconnectedSpace.isTotallyDisconnected_univ`：∀ {α : Type u} {ins
t : TopologicalSpace α} [self : TotallyDisconnectedSpace α], IsTotallyDisconnect
ed Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem IsPreconnected.subsingleton [TotallyDisconnectedSpace α] {s : Set α}
    (h : IsPreconnected s) : s.Subsingleton :=
  TotallyDisconnectedSpace.isTotallyDisconnected_univ s (subset_univ s) h

-- note: making this an instance breaks downstream files
/-
**subsingleton_of_preconnected_totallyDisconnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subsingleton_of_preconnected_totallyDisconnected [PreconnectedSpace α] [To
tallyDisconnectedSpace α] : Subsingleton α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subsingleton_of_univ_subsingleton`：subsingleton_of_univ_subsingleton
 (h : (univ : Set α).Subsingleton) : Subsingleton α
· 使用定理 `IsPreconnected.subsingleton`：IsPreconnected.subsingleton [TotallyDisconn
ectedSpace α] {s : Set α} (h : IsPreconnected s) : s.Subsingleton
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
-/
theorem subsingleton_of_preconnected_totallyDisconnected
    [PreconnectedSpace α] [TotallyDisconnectedSpace α] : Subsingleton α :=
  Set.subsingleton_of_univ_subsingleton isPreconnected_univ.subsingleton
/-
**Pi.totallyDisconnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.totallyDisconnectedSpace {α : Type*} {β : α -> Type*} [forall a, Topolo
gicalSpace (β a)] [forall a, TotallyDisconnectedSpace (β a)] : TotallyDisconnect
edSpace (forall a : α, β a)
参数：β a；β a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsPreconnected.subsingleton`：IsPreconnected.subsingleton [TotallyDisconn
ectedSpace α] {s : Set α} (h : IsPreconnected s) : s.Subsingleton
-/
instance Pi.totallyDisconnectedSpace {α : Type*} {β : α → Type*}
    [∀ a, TopologicalSpace (β a)] [∀ a, TotallyDisconnectedSpace (β a)] :
    TotallyDisconnectedSpace (∀ a : α, β a) :=
  ⟨fun t _ h2 =>
    have : ∀ a, IsPreconnected ((fun x : ∀ a, β a => x a) '' t) := fun a =>
      h2.image (fun x => x a) (continuous_apply a).continuousOn
    fun x x_in y y_in => funext fun a => (this a).subsingleton ⟨x, x_in, rfl⟩ ⟨y, y_in, rfl⟩⟩
/-
**Prod.totallyDisconnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.totallyDisconnectedSpace [TopologicalSpace β] [TotallyDisconnectedSpa
ce α] [TotallyDisconnectedSpace β] : TotallyDisconnectedSpace (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `IsPreconnected.subsingleton`：IsPreconnected.subsingleton [TotallyDisconn
ectedSpace α] {s : Set α} (h : IsPreconnected s) : s.Subsingleton
-/
instance Prod.totallyDisconnectedSpace [TopologicalSpace β] [TotallyDisconnectedSpace α]
    [TotallyDisconnectedSpace β] : TotallyDisconnectedSpace (α × β) :=
  ⟨fun t _ h2 =>
    have H1 : IsPreconnected (Prod.fst '' t) := h2.image Prod.fst continuous_fst.continuousOn
    have H2 : IsPreconnected (Prod.snd '' t) := h2.image Prod.snd continuous_snd.continuousOn
    fun x hx y hy =>
    Prod.ext (H1.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
      (H2.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace β] [TotallyDisconnectedSpace α] [TotallyDisconnectedSpace β] :
    TotallyDisconnectedSpace (α ⊕ β) := by
  refine ⟨fun s _ hs => ?_⟩
  obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isPreconnected_iff.1 hs
  · exact ht.subsingleton.image _
  · exact ht.subsingleton.image _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, TopologicalSpace (X i)] [∀ i, TotallyDisconnectedSpace (X i)] :
    TotallyDisconnectedSpace (Σ i, X i) := by
  refine ⟨fun s _ hs => ?_⟩
  obtain rfl | h := s.eq_empty_or_nonempty
  · exact subsingleton_empty
  · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
    exact ht.isPreconnected.subsingleton.image _

/-- A space is totally disconnected iff its connected components are subsingletons. -/
/-
**totallyDisconnectedSpace_iff_connectedComponent_subsingleton** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：totallyDisconnectedSpace_iff_connectedComponent_subsingleton : TotallyDisc
onnectedSpace α ↔ forall x : α, (connectedComponent x).Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyDisconnectedSpace.isTotallyDisconnected_univ`：∀ {α : Type u} {ins
t : TopologicalSpace α} [self : TotallyDisconnectedSpace α], IsTotallyDisconnect
ed Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `isPreconnected_connectedComponent`：isPreconnected_connectedComponent {x 
: α} : IsPreconnected (connectedComponent x)
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Set.subsingleton_empty`：subsingleton_empty : (∅ : Set α).Subsingleton
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Subsingleton.anti`：∀ {α : Type u} {s t : Set α}, t.Subsingleton → s 
⊆ t → s.Subsingleton
· 使用定理 `IsPreconnected.subset_connectedComponent`：IsPreconnected.subset_connecte
dComponent {x : α} {s : Set α} (H1 : IsPreconnected s) (H2 : x in s) : s subsete
q connectedComponent x

--- 原说明 ---
A space is totally disconnected iff its connected components are subsingletons.
-/
theorem totallyDisconnectedSpace_iff_connectedComponent_subsingleton :
    TotallyDisconnectedSpace α ↔ ∀ x : α, (connectedComponent x).Subsingleton := by
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

/-- A space is totally disconnected iff its connected components are singletons. -/
/-
**totallyDisconnectedSpace_iff_connectedComponent_singleton** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：totallyDisconnectedSpace_iff_connectedComponent_singleton : TotallyDisconn
ectedSpace α ↔ forall x : α, connectedComponent x = {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `totallyDisconnectedSpace_iff_connectedComponent_subsingleton`：totallyDis
connectedSpace_iff_connectedComponent_subsingleton : TotallyDisconnectedSpace α 
↔ forall x : α, (connectedComponent x).Subsingleto…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Set.subsingleton_iff_singleton`：subsingleton_iff_singleton {x} (hx : x i
n s) : s.Subsingleton ↔ s = {x}
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A space is totally disconnected iff its connected components are singletons.
-/
theorem totallyDisconnectedSpace_iff_connectedComponent_singleton :
    TotallyDisconnectedSpace α ↔ ∀ x : α, connectedComponent x = {x} := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_subsingleton]
  refine forall_congr' fun x => ?_
  rw [subsingleton_iff_singleton]
  exact mem_connectedComponent
/-
**connectedComponent_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] [TotallyDisconnectedSpace α] (x
 : α), connectedComponent x = {x}
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `totallyDisconnectedSpace_iff_connectedComponent_singleton`：totallyDiscon
nectedSpace_iff_connectedComponent_singleton : TotallyDisconnectedSpace α ↔ fora
ll x : α, connectedComponent x = {x}
-/
@[simp] theorem connectedComponent_eq_singleton [TotallyDisconnectedSpace α] (x : α) :
    connectedComponent x = {x} :=
  totallyDisconnectedSpace_iff_connectedComponent_singleton.1 ‹_› x

/-- The image of a connected component in a totally disconnected space is a singleton. -/
@[simp]
/-
**Continuous.image_connectedComponent_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.image_connectedComponent_eq_singleton {β : Type*} [TopologicalS
pace β] [TotallyDisconnectedSpace β] {f : α -> β} (h : Continuous f) (a : α) : f
 '' connectedComponent a = {f a}
参数：h : Continuous f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subsingleton_iff_singleton`：subsingleton_iff_singleton {x} (hx : x i
n s) : s.Subsingleton ↔ s = {x}
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
· 使用定理 `IsPreconnected.subsingleton`：IsPreconnected.subsingleton [TotallyDisconn
ectedSpace α] {s : Set α} (h : IsPreconnected s) : s.Subsingleton
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `isPreconnected_connectedComponent`：isPreconnected_connectedComponent {x 
: α} : IsPreconnected (connectedComponent x)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s

--- 原说明 ---
The image of a connected component in a totally disconnected space is a singleto
n.
-/
theorem Continuous.image_connectedComponent_eq_singleton {β : Type*} [TopologicalSpace β]
    [TotallyDisconnectedSpace β] {f : α → β} (h : Continuous f) (a : α) :
    f '' connectedComponent a = {f a} :=
  (Set.subsingleton_iff_singleton <| mem_image_of_mem f mem_connectedComponent).mp
    (isPreconnected_connectedComponent.image f h.continuousOn).subsingleton
/-
**isTotallyDisconnected_of_totallyDisconnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：isTotallyDisconnected_of_totallyDisconnectedSpace [TotallyDisconnectedSpac
e α] (s : Set α) : IsTotallyDisconnected s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyDisconnectedSpace.isTotallyDisconnected_univ`：∀ {α : Type u} {ins
t : TopologicalSpace α} [self : TotallyDisconnectedSpace α], IsTotallyDisconnect
ed Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem isTotallyDisconnected_of_totallyDisconnectedSpace [TotallyDisconnectedSpace α] (s : Set α) :
    IsTotallyDisconnected s := fun t _ ht =>
  TotallyDisconnectedSpace.isTotallyDisconnected_univ _ t.subset_univ ht
/-
**TotallyDisconnectedSpace.eq_of_continuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TotallyDisconnectedSpace.eq_of_continuous [TopologicalSpace β] [Preconnect
edSpace α] [TotallyDisconnectedSpace β] (f : α -> β) (hf : Continuous f) (i j : 
α) : f i = f j
参数：f : α -> β；hf : Continuous f；i j : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.subsingleton`：IsPreconnected.subsingleton [TotallyDisconn
ectedSpace α] {s : Set α} (h : IsPreconnected s) : s.Subsingleton
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `trivial`：True
-/
lemma TotallyDisconnectedSpace.eq_of_continuous [TopologicalSpace β]
    [PreconnectedSpace α] [TotallyDisconnectedSpace β] (f : α → β) (hf : Continuous f)
    (i j : α) : f i = f j :=
  (isPreconnected_univ.image f hf.continuousOn).subsingleton ⟨i, trivial, rfl⟩ ⟨j, trivial, rfl⟩

/-- The bijection `C(X, Y) ≃ Y` when `Y` is totally disconnected and `X` is connected. -/
@[simps! symm_apply_apply]
/-
**TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace** 是 Mathlib 中的一个定义
，位于命名空间 ``。
形式化陈述：TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace (X Y : Type*) 
[TopologicalSpace X] [TopologicalSpace Y] [TotallyDisconnectedSpace Y] [Connecte
dSpace X] : C(X, Y) ≃ Y where toFun f
参数：X Y : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ConnectedSpace.toNonempty`：∀ {α : Type u} {inst : TopologicalSpace α} [s
elf : ConnectedSpace α], Nonempty α

--- 原说明 ---
The bijection `C(X, Y) ≃ Y` when `Y` is totally disconnected and `X` is connecte
d.
-/
noncomputable def TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace
    (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] [TotallyDisconnectedSpace Y] [ConnectedSpace X] :
    C(X, Y) ≃ Y where
  toFun f := f (Classical.arbitrary _)
  invFun y := ⟨fun _ ↦ y, by fun_prop⟩
  left_inv f := ContinuousMap.ext (TotallyDisconnectedSpace.eq_of_continuous _ f.2 _)
  right_inv _ := rfl
/-
**isTotallyDisconnected_of_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTotallyDisconnected_of_image [TopologicalSpace β] {f : α -> β} (hf : Con
tinuousOn f s) (hf' : Injective f) (h : IsTotallyDisconnected (f '' s)) : IsTota
llyDisconnected s
参数：hf : ContinuousOn f s；hf' : Injective f；h : IsTotallyDisconnected (f '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem isTotallyDisconnected_of_image [TopologicalSpace β] {f : α → β} (hf : ContinuousOn f s)
    (hf' : Injective f) (h : IsTotallyDisconnected (f '' s)) : IsTotallyDisconnected s :=
  fun _t hts ht _x x_in _y y_in =>
  hf' <|
    h _ (image_mono hts) (ht.image f <| hf.mono hts) (mem_image_of_mem f x_in)
      (mem_image_of_mem f y_in)
/-
**Topology.IsEmbedding.isTotallyDisconnected** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.isTotallyDisconnected [TopologicalSpace β] {f : α -> 
β} {s : Set α} (hf : IsEmbedding f) (h : IsTotallyDisconnected (f '' s)) : IsTot
allyDisconnected s
参数：hf : IsEmbedding f；h : IsTotallyDisconnected (f '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isTotallyDisconnected_of_image`：isTotallyDisconnected_of_image [Topologi
calSpace β] {f : α -> β} (hf : ContinuousOn f s) (hf' : Injective f) (h : IsTota
llyDisconnected (f '…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
lemma Topology.IsEmbedding.isTotallyDisconnected [TopologicalSpace β] {f : α → β} {s : Set α}
    (hf : IsEmbedding f) (h : IsTotallyDisconnected (f '' s)) : IsTotallyDisconnected s :=
  isTotallyDisconnected_of_image hf.continuous.continuousOn hf.injective h
/-
**Topology.IsEmbedding.isTotallyDisconnected_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.isTotallyDisconnected_image [TopologicalSpace β] {f :
 α -> β} {s : Set α} (hf : IsEmbedding f) : IsTotallyDisconnected (f '' s) ↔ IsT
otallyDisconnected s
参数：hf : IsEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsEmbedding.isTotallyDisconnected`：Topology.IsEmbedding.isTotal
lyDisconnected [TopologicalSpace β] {f : α -> β} {s : Set α} (hf : IsEmbedding f
) (h : IsTotallyDisconnected (f …
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_inter`：image_preimage_inter (f : α -> β) (s : Set α) 
(t : Set β) : f '' (f ⁻¹' t inter s) = t inter f '' s
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `Set.Subsingleton.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.S
ubsingleton → ∀ (f : α → β), (f '' s).Subsingleton
· 使用定理 `Topology.IsInducing.isPreconnected_image`：Topology.IsInducing.isPreconne
cted_image [TopologicalSpace β] {s : Set α} {f : α -> β} (hf : IsInducing f) : I
sPreconnected (f '' s) ↔ IsPre…
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
-/
lemma Topology.IsEmbedding.isTotallyDisconnected_image [TopologicalSpace β] {f : α → β} {s : Set α}
    (hf : IsEmbedding f) : IsTotallyDisconnected (f '' s) ↔ IsTotallyDisconnected s := by
  refine ⟨hf.isTotallyDisconnected, fun hs u hus hu ↦ ?_⟩
  obtain ⟨v, hvs, rfl⟩ : ∃ v, v ⊆ s ∧ f '' v = u :=
    ⟨f ⁻¹' u ∩ s, inter_subset_right, by rwa [image_preimage_inter, inter_eq_left]⟩
  rw [hf.isInducing.isPreconnected_image] at hu
  exact (hs v hvs hu).image _
/-
**Topology.IsEmbedding.isTotallyDisconnected_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.isTotallyDisconnected_range [TopologicalSpace β] {f :
 α -> β} (hf : IsEmbedding f) : IsTotallyDisconnected (range f) ↔ TotallyDisconn
ectedSpace α
参数：hf : IsEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `totallyDisconnectedSpace_iff`：∀ (α : Type u) [inst : TopologicalSpace α]
, TotallyDisconnectedSpace α ↔ IsTotallyDisconnected Set.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用引理 `Topology.IsEmbedding.isTotallyDisconnected_image`：Topology.IsEmbedding.i
sTotallyDisconnected_image [TopologicalSpace β] {f : α -> β} {s : Set α} (hf : I
sEmbedding f) : IsTotallyDisconnected …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Topology.IsEmbedding.isTotallyDisconnected_range [TopologicalSpace β] {f : α → β}
    (hf : IsEmbedding f) : IsTotallyDisconnected (range f) ↔ TotallyDisconnectedSpace α := by
  rw [totallyDisconnectedSpace_iff, ← image_univ, hf.isTotallyDisconnected_image]
/-
**totallyDisconnectedSpace_subtype_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyDisconnectedSpace_subtype_iff {s : Set α} : TotallyDisconnectedSpac
e s ↔ IsTotallyDisconnected s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsEmbedding.isTotallyDisconnected_range`：Topology.IsEmbedding.i
sTotallyDisconnected_range [TopologicalSpace β] {f : α -> β} (hf : IsEmbedding f
) : IsTotallyDisconnected (range f) ↔ …
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma totallyDisconnectedSpace_subtype_iff {s : Set α} :
    TotallyDisconnectedSpace s ↔ IsTotallyDisconnected s := by
  rw [← IsEmbedding.subtypeVal.isTotallyDisconnected_range, Subtype.range_val]
/-
**Subtype.totallyDisconnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subtype.totallyDisconnectedSpace {α : Type*} {p : α -> Prop} [TopologicalS
pace α] [TotallyDisconnectedSpace α] : TotallyDisconnectedSpace (Subtype p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `totallyDisconnectedSpace_subtype_iff`：totallyDisconnectedSpace_subtype_i
ff {s : Set α} : TotallyDisconnectedSpace s ↔ IsTotallyDisconnected s
· 使用定理 `isTotallyDisconnected_of_totallyDisconnectedSpace`：isTotallyDisconnected
_of_totallyDisconnectedSpace [TotallyDisconnectedSpace α] (s : Set α) : IsTotall
yDisconnected s
-/
instance Subtype.totallyDisconnectedSpace {α : Type*} {p : α → Prop} [TopologicalSpace α]
    [TotallyDisconnectedSpace α] : TotallyDisconnectedSpace (Subtype p) :=
  totallyDisconnectedSpace_subtype_iff.2 (isTotallyDisconnected_of_totallyDisconnectedSpace _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TotallyDisconnectedSpace α] : TotallyDisconnectedSpace (Additive α) :=
  ‹TotallyDisconnectedSpace α›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TotallyDisconnectedSpace α] : TotallyDisconnectedSpace (Multiplicative α) :=
  ‹TotallyDisconnectedSpace α›

end TotallyDisconnected

section TotallySeparated

/-- A set `s` is called totally separated if any two points of this set can be separated
by two disjoint open sets covering `s`. -/
/-
**IsTotallySeparated** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsTotallySeparated (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is called totally separated if any two points of this set can be separ
ated
by two disjoint open sets covering `s`.
-/
def IsTotallySeparated (s : Set α) : Prop :=
  Set.Pairwise s fun x y =>
  ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ s ⊆ u ∪ v ∧ Disjoint u v
/-
**isTotallySeparated_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTotallySeparated_empty : IsTotallySeparated (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isTotallySeparated_empty : IsTotallySeparated (∅ : Set α) := fun _ => False.elim
/-
**isTotallySeparated_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTotallySeparated_singleton {x} : IsTotallySeparated ({x} : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y} : 
Set α)) : x = y
-/
theorem isTotallySeparated_singleton {x} : IsTotallySeparated ({x} : Set α) := fun _ hp _ hq hpq =>
  (hpq <| (eq_of_mem_singleton hp).symm ▸ (eq_of_mem_singleton hq).symm).elim
/-
**isTotallyDisconnected_of_isTotallySeparated** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTotallyDisconnected_of_isTotallySeparated {s : Set α} (H : IsTotallySepa
rated s) : IsTotallyDisconnected s
参数：H : IsTotallySeparated s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
-/
theorem isTotallyDisconnected_of_isTotallySeparated {s : Set α} (H : IsTotallySeparated s) :
    IsTotallyDisconnected s := by
  intro t hts ht x x_in y y_in
  by_contra h
  obtain
    ⟨u : Set α, v : Set α, hu : IsOpen u, hv : IsOpen v, hxu : x ∈ u, hyv : y ∈ v, hs : s ⊆ u ∪ v,
      huv⟩ :=
    H (hts x_in) (hts y_in) h
  refine (ht _ _ hu hv (hts.trans hs) ⟨x, x_in, hxu⟩ ⟨y, y_in, hyv⟩).ne_empty ?_
  rw [huv.inter_eq, inter_empty]

alias IsTotallySeparated.isTotallyDisconnected := isTotallyDisconnected_of_isTotallySeparated

/-- A space is totally separated if any two points can be separated by two disjoint open sets
covering the whole space. -/
/-
**TotallySeparatedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A space is totally separated if any two points can be separated by two disjoint 
open sets
covering the whole space.
-/
@[mk_iff] class TotallySeparatedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a totally separated space is totally separated. -/
  isTotallySeparated_univ : IsTotallySeparated (univ : Set α)

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) TotallySeparatedSpace.totallyDisconnectedSpace (α : Type u)
    [TopologicalSpace α] [TotallySeparatedSpace α] : TotallyDisconnectedSpace α :=
  ⟨TotallySeparatedSpace.isTotallySeparated_univ.isTotallyDisconnected⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) TotallySeparatedSpace.of_discrete (α : Type*) [TopologicalSpace α]
    [DiscreteTopology α] : TotallySeparatedSpace α :=
  ⟨fun _ _ b _ h => ⟨{b}ᶜ, {b}, isOpen_discrete _, isOpen_discrete _, h, rfl,
    (compl_union_self _).symm.subset, disjoint_compl_left⟩⟩
/-
**totallySeparatedSpace_iff_exists_isClopen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：totallySeparatedSpace_iff_exists_isClopen {α : Type*} [TopologicalSpace α]
 : TotallySeparatedSpace α ↔ Pairwise (exists U : Set α, IsClopen U ∧ · in U ∧ ·
 in Uᶜ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `forall₃_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {p q : (a : α) → (b : β a) → γ a b → Prop},   (∀ (a : α) (b : β a) (c 
: γ…
· 使用定理 `isClopen_of_disjoint_cover_open`：isClopen_of_disjoint_cover_open {a b : 
Set X} (cover : univ subseteq a union b) (ha : IsOpen a) (hb : IsOpen b) (hab : 
Disjoint a b) : IsClo…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsClopen.compl`：IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
-/
theorem totallySeparatedSpace_iff_exists_isClopen {α : Type*} [TopologicalSpace α] :
    TotallySeparatedSpace α ↔ Pairwise (∃ U : Set α, IsClopen U ∧ · ∈ U ∧ · ∈ Uᶜ) := by
  simp only [totallySeparatedSpace_iff, IsTotallySeparated, Set.Pairwise, mem_univ, true_implies]
  refine forall₃_congr fun x y _ ↦
    ⟨fun ⟨U, V, hU, hV, Ux, Vy, f, disj⟩ ↦ ?_, fun ⟨U, hU, Ux, Ucy⟩ ↦ ?_⟩
  · exact ⟨U, isClopen_of_disjoint_cover_open f hU hV disj,
      Ux, fun Uy ↦ Set.disjoint_iff.mp disj ⟨Uy, Vy⟩⟩
  · exact ⟨U, Uᶜ, hU.2, hU.compl.2, Ux, Ucy, (Set.union_compl_self U).ge, disjoint_compl_right⟩
/-
**exists_isClopen_of_totally_separated** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isClopen_of_totally_separated {α : Type*} [TopologicalSpace α] [Tot
allySeparatedSpace α] : Pairwise (exists U : Set α, IsClopen U ∧ · in U ∧ · in U
ᶜ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `totallySeparatedSpace_iff_exists_isClopen`：totallySeparatedSpace_iff_exi
sts_isClopen {α : Type*} [TopologicalSpace α] : TotallySeparatedSpace α ↔ Pairwi
se (exists U : Set α, IsClopen …
-/
theorem exists_isClopen_of_totally_separated {α : Type*} [TopologicalSpace α]
    [TotallySeparatedSpace α] : Pairwise (∃ U : Set α, IsClopen U ∧ · ∈ U ∧ · ∈ Uᶜ) :=
  totallySeparatedSpace_iff_exists_isClopen.mp ‹_›

end TotallySeparated


variable [TopologicalSpace β] [TotallyDisconnectedSpace β] {f : α → β}

/-
**Continuous.image_eq_of_connectedComponent_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.image_eq_of_connectedComponent_eq (h : Continuous f) (a b : α) 
(hab : connectedComponent a = connectedComponent b) : f a = f b
参数：h : Continuous f；a b : α；hab : connectedComponent a = connectedComponent b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.singleton_eq_singleton_iff`：singleton_eq_singleton_iff {x y : α} : {
x} = ({y} : Set α) ↔ x = y
· 使用定理 `Continuous.image_connectedComponent_eq_singleton`：Continuous.image_conne
ctedComponent_eq_singleton {β : Type*} [TopologicalSpace β] [TotallyDisconnected
Space β] {f : α -> β} (h : Continuous …
-/
theorem Continuous.image_eq_of_connectedComponent_eq (h : Continuous f) (a b : α)
    (hab : connectedComponent a = connectedComponent b) : f a = f b :=
  singleton_eq_singleton_iff.1 <|
    h.image_connectedComponent_eq_singleton a ▸
      h.image_connectedComponent_eq_singleton b ▸ hab ▸ rfl

/--
The lift to `connectedComponents α` of a continuous map from `α` to a totally disconnected space
-/
/-
**Continuous.connectedComponentsLift** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Continuous.connectedComponentsLift (h : Continuous f) : ConnectedComponent
s α -> β
参数：h : Continuous f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.image_eq_of_connectedComponent_eq`：Continuous.image_eq_of_con
nectedComponent_eq (h : Continuous f) (a b : α) (hab : connectedComponent a = co
nnectedComponent b) : f a = f b

--- 原说明 ---
The lift to `connectedComponents α` of a continuous map from `α` to a totally di
sconnected space
-/
def Continuous.connectedComponentsLift (h : Continuous f) : ConnectedComponents α → β := fun x =>
  Quotient.liftOn' x f h.image_eq_of_connectedComponent_eq

@[continuity]
/-
**Continuous.connectedComponentsLift_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.connectedComponentsLift_continuous (h : Continuous f) : Continu
ous h.connectedComponentsLift
参数：h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.quotient_liftOn'`：Continuous.quotient_liftOn' {f : X -> Y} (h
 : Continuous f) (hs : forall a b, s a b -> f a = f b) : Continuous (fun x => Qu
otient.liftOn' x …
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Continuous.image_eq_of_connectedComponent_eq`：Continuous.image_eq_of_con
nectedComponent_eq (h : Continuous f) (a b : α) (hab : connectedComponent a = co
nnectedComponent b) : f a = f b
-/
theorem Continuous.connectedComponentsLift_continuous (h : Continuous f) :
    Continuous h.connectedComponentsLift :=
  h.quotient_liftOn' <| by convert! h.image_eq_of_connectedComponent_eq

@[simp]
/-
**Continuous.connectedComponentsLift_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.connectedComponentsLift_apply_coe (h : Continuous f) (x : α) : 
h.connectedComponentsLift x = f x
参数：h : Continuous f；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Continuous.connectedComponentsLift_apply_coe (h : Continuous f) (x : α) :
    h.connectedComponentsLift x = f x :=
  rfl

@[simp]
/-
**Continuous.connectedComponentsLift_comp_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.connectedComponentsLift_comp_coe (h : Continuous f) : h.connect
edComponentsLift ∘ (↑) = f
参数：h : Continuous f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Continuous.connectedComponentsLift_comp_coe (h : Continuous f) :
    h.connectedComponentsLift ∘ (↑) = f :=
  rfl
/-
**connectedComponents_lift_unique'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponents_lift_unique' {β : Sort*} {g₁ g₂ : ConnectedComponents 
α -> β} (hg : g₁ ∘ ((↑) : α -> ConnectedComponents α) = g₂ ∘ (↑)) : g₁ = g₂
参数：hg : g₁ ∘ ((↑) : α -> ConnectedComponents α) = g₂ ∘ (↑)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.injective_comp_right`：∀ {α : Sort u_1} {β : Sort u_2
} {γ : Sort u_3} {f : α → β}, Function.Surjective f → Function.Injective fun g =
> g ∘ f
· 使用定理 `ConnectedComponents.surjective_coe`：surjective_coe : Surjective (mk : α 
-> ConnectedComponents α)
-/
theorem connectedComponents_lift_unique' {β : Sort*} {g₁ g₂ : ConnectedComponents α → β}
    (hg : g₁ ∘ ((↑) : α → ConnectedComponents α) = g₂ ∘ (↑)) : g₁ = g₂ :=
  ConnectedComponents.surjective_coe.injective_comp_right hg
/-
**Continuous.connectedComponentsLift_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.connectedComponentsLift_unique (h : Continuous f) (g : Connecte
dComponents α -> β) (hg : g ∘ (↑) = f) : g = h.connectedComponentsLift
参数：h : Continuous f；g : ConnectedComponents α -> β；hg : g ∘ (↑) = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `connectedComponents_lift_unique'`：connectedComponents_lift_unique' {β : 
Sort*} {g₁ g₂ : ConnectedComponents α -> β} (hg : g₁ ∘ ((↑) : α -> ConnectedComp
onents α) = g₂ ∘ (↑)) …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Continuous.connectedComponentsLift_comp_coe`：Continuous.connectedCompone
ntsLift_comp_coe (h : Continuous f) : h.connectedComponentsLift ∘ (↑) = f
-/
theorem Continuous.connectedComponentsLift_unique (h : Continuous f) (g : ConnectedComponents α → β)
    (hg : g ∘ (↑) = f) : g = h.connectedComponentsLift :=
  connectedComponents_lift_unique' <| hg.trans h.connectedComponentsLift_comp_coe.symm
/-
**ConnectedComponents.totallyDisconnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ConnectedComponents.totallyDisconnectedSpace : TotallyDisconnectedSpace (C
onnectedComponents α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `totallyDisconnectedSpace_iff_connectedComponent_singleton`：totallyDiscon
nectedSpace_iff_connectedComponent_singleton : TotallyDisconnectedSpace α ↔ fora
ll x : α, connectedComponent x = {x}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `ConnectedComponents.surjective_coe`：surjective_coe : Surjective (mk : α 
-> ConnectedComponents α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsCoinducing.image_connectedComponent`：Topology.IsCoinducing.im
age_connectedComponent {f : α -> β} (hf : IsCoinducing f) (h_fibers : forall y :
 β, IsConnected (f ⁻¹' {y})) (a : α)…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `ConnectedComponents.isQuotientMap_coe`：isQuotientMap_coe : IsQuotientMap
 (mk : α -> ConnectedComponents α)
· 使用定理 `connectedComponents_preimage_singleton`：connectedComponents_preimage_sin
gleton {x : α} : (↑) ⁻¹' ({↑x} : Set (ConnectedComponents α)) = connectedCompone
nt x
· 使用定理 `isConnected_connectedComponent`：isConnected_connectedComponent {x : α} :
 IsConnected (connectedComponent x)
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
-/
instance ConnectedComponents.totallyDisconnectedSpace :
    TotallyDisconnectedSpace (ConnectedComponents α) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  refine ConnectedComponents.surjective_coe.forall.2 fun x => ?_
  rw [← ConnectedComponents.isQuotientMap_coe.image_connectedComponent, ←
    connectedComponents_preimage_singleton, image_preimage_eq _ ConnectedComponents.surjective_coe]
  refine ConnectedComponents.surjective_coe.forall.2 fun y => ?_
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

/-- Functoriality of `connectedComponents` -/
/-
**Continuous.connectedComponentsMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Continuous.connectedComponentsMap {β : Type*} [TopologicalSpace β] {f : α 
-> β} (h : Continuous f) : ConnectedComponents α -> ConnectedComponents β
参数：h : Continuous f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality of `connectedComponents`
-/
def Continuous.connectedComponentsMap {β : Type*} [TopologicalSpace β] {f : α → β}
    (h : Continuous f) : ConnectedComponents α → ConnectedComponents β :=
  Continuous.connectedComponentsLift (ConnectedComponents.continuous_coe.comp h)

@[simp]
/-
**Continuous.connectedComponentsMap_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.connectedComponentsMap_mk {β : Type*} [TopologicalSpace β] {f :
 α -> β} (hf : Continuous f) (x : α) : hf.connectedComponentsMap (.mk x) = .mk (
f x)
参数：hf : Continuous f；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Continuous.connectedComponentsMap_mk {β : Type*} [TopologicalSpace β] {f : α → β}
    (hf : Continuous f) (x : α) :
    hf.connectedComponentsMap (.mk x) = .mk (f x) :=
  rfl
/-
**Continuous.connectedComponentsMap_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.connectedComponentsMap_continuous {β : Type*} [TopologicalSpace
 β] {f : α -> β} (h : Continuous f) : Continuous h.connectedComponentsMap
参数：h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.connectedComponentsLift_continuous`：Continuous.connectedCompo
nentsLift_continuous (h : Continuous f) : Continuous h.connectedComponentsLift
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ConnectedComponents.continuous_coe`：continuous_coe : Continuous (mk : α 
-> ConnectedComponents α)
-/
theorem Continuous.connectedComponentsMap_continuous {β : Type*} [TopologicalSpace β] {f : α → β}
    (h : Continuous f) : Continuous h.connectedComponentsMap :=
  Continuous.connectedComponentsLift_continuous (ConnectedComponents.continuous_coe.comp h)
/-
**Topology.IsCoinducing.connectedComponentsMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsCoinducing.connectedComponentsMap {β : Type*} [TopologicalSpace
 β] {f : α -> β} (hf : IsCoinducing f) : IsCoinducing hf.continuous.connectedCom
ponentsMap
参数：hf : IsCoinducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsCoinducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsCo
inducing f → Continuou…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z : 
Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topolo
gicalSpace Y] [inst_2 :…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `ConnectedComponents.isQuotientMap_coe`：isQuotientMap_coe : IsQuotientMap
 (mk : α -> ConnectedComponents α)
· 使用定理 `Topology.IsCoinducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_
3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSp
ace Y] [inst_2 :…
-/
lemma Topology.IsCoinducing.connectedComponentsMap {β : Type*} [TopologicalSpace β] {f : α → β}
    (hf : IsCoinducing f) :
    IsCoinducing hf.continuous.connectedComponentsMap := by
  rw [← ConnectedComponents.isQuotientMap_coe.isCoinducing.of_comp_iff]
  exact ConnectedComponents.isQuotientMap_coe.isCoinducing.comp hf

@[simp]
/-
**Continuous.connectedComponentsMap_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.connectedComponentsMap_surjective {β : Type*} [TopologicalSpace
 β] {f : α -> β} (hf : Continuous f) (h : Surjective f) : Surjective hf.connecte
dComponentsMap
参数：hf : Continuous f；h : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.lift_surjective`：Quotient.lift_surjective {α β : Sort*} {s : Se
toid α} (f : α -> β) (h : forall (a b : α), a ≈ b -> f a = f b) (hf : Function.S
urjective f) :…
· 使用定理 `Continuous.image_eq_of_connectedComponent_eq`：Continuous.image_eq_of_con
nectedComponent_eq (h : Continuous f) (a b : α) (hab : connectedComponent a = co
nnectedComponent b) : f a = f b
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `ConnectedComponents.surjective_coe`：surjective_coe : Surjective (mk : α 
-> ConnectedComponents α)
-/
lemma Continuous.connectedComponentsMap_surjective {β : Type*} [TopologicalSpace β] {f : α → β}
    (hf : Continuous f) (h : Surjective f) :
    Surjective hf.connectedComponentsMap :=
  Quotient.lift_surjective _ _ <| ConnectedComponents.surjective_coe.comp h
/-
**Topology.IsCoinducing.connectedComponentsMap_bijective** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：Topology.IsCoinducing.connectedComponentsMap_bijective {β : Type*} [Topolo
gicalSpace β] {f : α -> β} (hf : IsCoinducing f) (hf' : forall y, IsConnected (f
 ⁻¹' {y})) : hf.continuous.connectedComponentsMap.Bijective
参数：hf : IsCoinducing f；hf' : forall y, IsConnected (f ⁻¹' {y})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsCoinducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsCo
inducing f → Continuou…
· 使用定理 `ConnectedComponents.surjective_coe`：surjective_coe : Surjective (mk : α 
-> ConnectedComponents α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.preimage_connectedComponent`：Topology.IsCoinducing
.preimage_connectedComponent (hf : IsCoinducing f) (h_fibers : forall y : β, IsC
onnected (f ⁻¹' {y})) (a : α) : f ⁻¹' c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Continuous.connectedComponentsMap_surjective`：Continuous.connectedCompon
entsMap_surjective {β : Type*} [TopologicalSpace β] {f : α -> β} (hf : Continuou
s f) (h : Surjective f) : Surjecti…
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
-/
lemma Topology.IsCoinducing.connectedComponentsMap_bijective {β : Type*} [TopologicalSpace β]
    {f : α → β} (hf : IsCoinducing f) (hf' : ∀ y, IsConnected (f ⁻¹' {y})) :
    hf.continuous.connectedComponentsMap.Bijective := by
  refine ⟨fun x y h ↦ ?_, Continuous.connectedComponentsMap_surjective _ fun y ↦ (hf' y).nonempty⟩
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
  simp_all [← hf.preimage_connectedComponent hf']

/-- A preconnected set `s` has the property that every map to a
discrete space that is continuous on `s` is constant on `s` -/
/-
**IsPreconnected.constant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.constant {Y : Type*} [TopologicalSpace Y] [DiscreteTopology
 Y] {s : Set α} (hs : IsPreconnected s) {f : α -> Y} (hf : ContinuousOn f s) {x 
y : α} (hx : x in s) (hy : y in s) : f x = f y
参数：hs : IsPreconnected s；hf : ContinuousOn f s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.subsingleton`：IsPreconnected.subsingleton [TotallyDisconn
ectedSpace α] {s : Set α} (h : IsPreconnected s) : s.Subsingleton
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `TotallySeparatedSpace.of_discrete`：∀ (α : Type u_3) [inst : TopologicalS
pace α] [DiscreteTopology α], TotallySeparatedSpace α
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
A preconnected set `s` has the property that every map to a
discrete space that is continuous on `s` is constant on `s`
-/
theorem IsPreconnected.constant {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y] {s : Set α}
    (hs : IsPreconnected s) {f : α → Y} (hf : ContinuousOn f s) {x y : α} (hx : x ∈ s)
    (hy : y ∈ s) : f x = f y :=
  (hs.image f hf).subsingleton (mem_image_of_mem f hx) (mem_image_of_mem f hy)

/-- A `PreconnectedSpace` version of `isPreconnected.constant` -/
/-
**PreconnectedSpace.constant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PreconnectedSpace.constant {Y : Type*} [TopologicalSpace Y] [DiscreteTopol
ogy Y] (hp : PreconnectedSpace α) {f : α -> Y} (hf : Continuous f) {x y : α} : f
 x = f y
参数：hp : PreconnectedSpace α；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.constant`：IsPreconnected.constant {Y : Type*} [Topologica
lSpace Y] [DiscreteTopology Y] {s : Set α} (hs : IsPreconnected s) {f : α -> Y} 
(hf : Continu…
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `trivial`：True

--- 原说明 ---
A `PreconnectedSpace` version of `isPreconnected.constant`
-/
theorem PreconnectedSpace.constant {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y]
    (hp : PreconnectedSpace α) {f : α → Y} (hf : Continuous f) {x y : α} : f x = f y :=
  IsPreconnected.constant hp.isPreconnected_univ (Continuous.continuousOn hf) trivial trivial

/-- Refinement of `IsPreconnected.constant` only assuming the map factors through a
discrete subset of the target. -/
/-
**IsPreconnected.constant_of_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.constant_of_mapsTo {S : Set α} (hS : IsPreconnected S) {β} 
[TopologicalSpace β] {T : Set β} (hT : IsDiscrete T) {f : α -> β} (hc : Continuo
usOn f S) (hTm : MapsTo f S T) {x y : α} (hx : x in S) (hy : y in S) : f x = f y
参数：hS : IsPreconnected S；hT : IsDiscrete T；hc : ContinuousOn f S；hTm : MapsTo f 
S T；hx : x in S；hy : y in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PreconnectedSpace.constant`：PreconnectedSpace.constant {Y : Type*} [Topo
logicalSpace Y] [DiscreteTopology Y] (hp : PreconnectedSpace α) {f : α -> Y} (hf
 : Continuous f)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isDiscrete_iff_discreteTopology`：isDiscrete_iff_discreteTopology : IsDis
crete s ↔ DiscreteTopology s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPreconnected_iff_preconnectedSpace`：isPreconnected_iff_preconnectedSpa
ce {s : Set α} : IsPreconnected s ↔ PreconnectedSpace s
· 使用定理 `ContinuousOn.mapsToRestrict`：ContinuousOn.mapsToRestrict {t : Set β} (hf
 : ContinuousOn f s) (ht : MapsTo f s t) : Continuous (ht.restrict f s t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b

--- 原说明 ---
Refinement of `IsPreconnected.constant` only assuming the map factors through a
discrete subset of the target.
-/
theorem IsPreconnected.constant_of_mapsTo {S : Set α} (hS : IsPreconnected S)
    {β} [TopologicalSpace β] {T : Set β} (hT : IsDiscrete T) {f : α → β} (hc : ContinuousOn f S)
    (hTm : MapsTo f S T) {x y : α} (hx : x ∈ S) (hy : y ∈ S) : f x = f y := by
  let F : S → T := hTm.restrict f S T
  suffices F ⟨x, hx⟩ = F ⟨y, hy⟩ by rwa [← Subtype.coe_inj] at this
  rw [isDiscrete_iff_discreteTopology] at hT
  exact (isPreconnected_iff_preconnectedSpace.mp hS).constant (hc.mapsToRestrict _)

/-- A version of `IsPreconnected.constant_of_mapsTo` that assumes that the codomain is nonempty and
proves that `f` is equal to `const α y` on `S` for some `y ∈ T`. -/
/-
**IsPreconnected.eqOn_const_of_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.eqOn_const_of_mapsTo {S : Set α} (hS : IsPreconnected S) {β
} [TopologicalSpace β] {T : Set β} (hT : IsDiscrete T) {f : α -> β} (hc : Contin
uousOn f S) (hTm : MapsTo f S T) (hne : T.Nonempty) : exists y in T, EqOn f (con
st α y) S
参数：hS : IsPreconnected S；hT : IsDiscrete T；hc : ContinuousOn f S；hTm : MapsTo f 
S T；hne : T.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Set.eqOn_empty`：eqOn_empty (f₁ f₂ : α -> β) : EqOn f₁ f₂ ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPreconnected.constant_of_mapsTo`：IsPreconnected.constant_of_mapsTo {S 
: Set α} (hS : IsPreconnected S) {β} [TopologicalSpace β] {T : Set β} (hT : IsDi
screte T) {f : α -> β} …

--- 原说明 ---
A version of `IsPreconnected.constant_of_mapsTo` that assumes that the codomain 
is nonempty and
proves that `f` is equal to `const α y` on `S` for some `y ∈ T`.
-/
theorem IsPreconnected.eqOn_const_of_mapsTo {S : Set α} (hS : IsPreconnected S)
    {β} [TopologicalSpace β] {T : Set β} (hT : IsDiscrete T) {f : α → β} (hc : ContinuousOn f S)
    (hTm : MapsTo f S T) (hne : T.Nonempty) : ∃ y ∈ T, EqOn f (const α y) S := by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨x, hx⟩)
  · exact hne.imp fun _ hy => ⟨hy, eqOn_empty _ _⟩
  · exact ⟨f x, hTm hx, fun x' hx' => hS.constant_of_mapsTo hT hc hTm hx' hx⟩
/-
**IsPreconnected.isDiscrete_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.isDiscrete_iff_subsingleton {S : Set α} (hS : IsPreconnecte
d S) : IsDiscrete S ↔ S.Subsingleton where mp h
参数：hS : IsPreconnected S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isDiscrete_iff_discreteTopology`：isDiscrete_iff_discreteTopology : IsDis
crete s ↔ DiscreteTopology s
· 使用定理 `isPreconnected_iff_preconnectedSpace`：isPreconnected_iff_preconnectedSpa
ce {s : Set α} : IsPreconnected s ↔ PreconnectedSpace s
· 使用定理 `subsingleton_of_preconnected_totallyDisconnected`：subsingleton_of_precon
nected_totallyDisconnected [PreconnectedSpace α] [TotallyDisconnectedSpace α] : 
Subsingleton α
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `TotallySeparatedSpace.of_discrete`：∀ (α : Type u_3) [inst : TopologicalS
pace α] [DiscreteTopology α], TotallySeparatedSpace α
· 使用引理 `Set.Subsingleton.isDiscrete`：Set.Subsingleton.isDiscrete (hs : s.Subsing
leton) : IsDiscrete s
-/
theorem IsPreconnected.isDiscrete_iff_subsingleton {S : Set α} (hS : IsPreconnected S) :
    IsDiscrete S ↔ S.Subsingleton where
  mp h := by
    have : DiscreteTopology S := isDiscrete_iff_discreteTopology.mp h
    have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
    have : Subsingleton S := subsingleton_of_preconnected_totallyDisconnected
    simpa using this
  mpr h := h.isDiscrete
