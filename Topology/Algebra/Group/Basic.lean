/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.Submonoid.MulOpposite
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Order.Filter.Bases.Finite
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topological groups

This file defines the following typeclasses:

* `IsTopologicalGroup`, `IsTopologicalAddGroup`: multiplicative and additive topological groups,
  i.e., groups with continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`;

* `ContinuousSub G` means that `G` has a continuous subtraction operation.

There is an instance deducing `ContinuousSub` from `IsTopologicalGroup` but we use a separate
typeclass because, e.g., `ℕ` and `ℝ≥0` have continuous subtraction but are not additive groups.

We also define `Homeomorph` versions of several `Equiv`s: `Homeomorph.mulLeft`,
`Homeomorph.mulRight`, `Homeomorph.inv`, and prove a few facts about neighbourhood filters in
groups.

## Tags

topological space, group, topological group
-/

@[expose] public section

open Set Filter TopologicalSpace Function Topology MulOpposite Pointwise

universe u v w x

variable {G : Type w} {H : Type x} {α : Type u} {β : Type v}

/-- In a Hausdorff magma with continuous multiplication, the centralizer of any set is closed. -/
/-
**Set.isClosed_centralizer** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.isClosed_centralizer {M : Type*} (s : Set M) [Mul M] [TopologicalSpace
 M] [SeparatelyContinuousMul M] [T2Space M] : IsClosed (centralizer s)
参数：s : Set M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.centralizer.eq_1`：∀ {M : Type u_1} (S : Set M) [inst : Mul M], S.cen
tralizer = {c | ∀ m ∈ S, m * c = c * m}
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `isClosed_sInter`：isClosed_sInter {s : Set (Set X)} : (forall t in s, IsC
losed t) -> IsClosed (⋂₀ s)
· 使用定理 `isClosed_imp`：isClosed_imp {p q : X -> Prop} (hp : IsOpen { x | p x }) (
hq : IsClosed { x | q x }) : IsClosed { x | p x -> q x }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
In a Hausdorff magma with continuous multiplication, the centralizer of any set 
is closed.
-/
lemma Set.isClosed_centralizer {M : Type*} (s : Set M) [Mul M] [TopologicalSpace M]
    [SeparatelyContinuousMul M] [T2Space M] : IsClosed (centralizer s) := by
  rw [centralizer, ofPred_forall]
  refine isClosed_sInter ?_
  rintro - ⟨m, ht, rfl⟩
  refine isClosed_imp (by simp) <| isClosed_eq ?_ ?_
  all_goals fun_prop

section ContinuousMulGroup

/-!
### Groups with continuous multiplication

In this section we prove a few statements about groups with continuous `(*)`.
-/


variable [TopologicalSpace G] [Group G] [SeparatelyContinuousMul G]

/-- Multiplication from the left in a topological group as a homeomorphism. -/
@[to_additive /-- Addition from the left in a topological additive group as a homeomorphism. -/]
/-
**Homeomorph.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：{G : Type w} → [inst : TopologicalSpace G] → [inst_1 : Group G] → [Separat
elyContinuousMul G] → G → G ≃ₜ G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication from the left in a topological group as a homeomorphism.
-/
protected def Homeomorph.mulLeft (a : G) : G ≃ₜ G :=
  { Equiv.mulLeft a with }

@[to_additive (attr := simp)]
/-
**Homeomorph.coe_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.coe_mulLeft (a : G) : ⇑(Homeomorph.mulLeft a) = (a * ·)
参数：a : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Homeomorph.coe_mulLeft (a : G) : ⇑(Homeomorph.mulLeft a) = (a * ·) :=
  rfl

@[to_additive]
/-
**Homeomorph.mulLeft_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.mulLeft_symm (a : G) : (Homeomorph.mulLeft a).symm = Homeomorph
.mulLeft a⁻¹
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.ext`：ext {h h' : X ≃ₜ Y} (H : forall x, h x = h' x) : h = h'
-/
theorem Homeomorph.mulLeft_symm (a : G) : (Homeomorph.mulLeft a).symm = Homeomorph.mulLeft a⁻¹ := by
  ext
  rfl

@[to_additive]
/-
**isOpenMap_mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOpenMap_mul_left (a : G) : IsOpenMap (a * ·)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
-/
lemma isOpenMap_mul_left (a : G) : IsOpenMap (a * ·) := (Homeomorph.mulLeft a).isOpenMap

@[to_additive IsOpen.left_addCoset]
/-
**IsOpen.leftCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.leftCoset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (x • U)
参数：h : IsOpen U；x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isOpenMap_mul_left`：isOpenMap_mul_left (a : G) : IsOpenMap (a * ·)
-/
theorem IsOpen.leftCoset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (x • U) :=
  isOpenMap_mul_left x _ h

@[to_additive]
/-
**isClosedMap_mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosedMap_mul_left (a : G) : IsClosedMap (a * ·)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h
-/
lemma isClosedMap_mul_left (a : G) : IsClosedMap (a * ·) := (Homeomorph.mulLeft a).isClosedMap

@[to_additive IsClosed.left_addCoset]
/-
**IsClosed.leftCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.leftCoset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (x • U)
参数：h : IsClosed U；x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isClosedMap_mul_left`：isClosedMap_mul_left (a : G) : IsClosedMap (a * ·)
-/
theorem IsClosed.leftCoset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (x • U) :=
  isClosedMap_mul_left x _ h

@[to_additive (attr := simp)]
/-
**Filter.map_mul_left_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_mul_left_nhdsNE {c a : G} : map (c * ·) (𝓝[!=] a) = (𝓝[!=] (c *
 a))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `Set.preimage_mul_left_singleton`：preimage_mul_left_singleton : (a * ·) ⁻
¹' {b} = {a⁻¹ * b}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.map_mul_left_nhdsNE {c a : G} :
    map (c * ·) (𝓝[≠] a) = (𝓝[≠] (c * a)) := by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

/-- Multiplication from the right in a topological group as a homeomorphism. -/
@[to_additive /-- Addition from the right in a topological additive group as a homeomorphism. -/]
/-
**Homeomorph.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：{G : Type w} → [inst : TopologicalSpace G] → [inst_1 : Group G] → [Separat
elyContinuousMul G] → G → G ≃ₜ G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication from the right in a topological group as a homeomorphism.
-/
protected def Homeomorph.mulRight (a : G) : G ≃ₜ G :=
  { Equiv.mulRight a with }

@[to_additive (attr := simp)]
/-
**Homeomorph.coe_mulRight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Homeomorph.coe_mulRight (a : G) : ⇑(Homeomorph.mulRight a) = (· * a)
参数：a : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Homeomorph.coe_mulRight (a : G) : ⇑(Homeomorph.mulRight a) = (· * a) := rfl

@[to_additive]
/-
**Homeomorph.mulRight_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.mulRight_symm (a : G) : (Homeomorph.mulRight a).symm = Homeomor
ph.mulRight a⁻¹
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.ext`：ext {h h' : X ≃ₜ Y} (H : forall x, h x = h' x) : h = h'
-/
theorem Homeomorph.mulRight_symm (a : G) :
    (Homeomorph.mulRight a).symm = Homeomorph.mulRight a⁻¹ := by
  ext
  rfl

@[to_additive]
/-
**isOpenMap_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_mul_right (a : G) : IsOpenMap (· * a)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
-/
theorem isOpenMap_mul_right (a : G) : IsOpenMap (· * a) :=
  (Homeomorph.mulRight a).isOpenMap

@[to_additive IsOpen.right_addCoset]
/-
**IsOpen.rightCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.rightCoset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (op x • U)
参数：h : IsOpen U；x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpenMap_mul_right`：isOpenMap_mul_right (a : G) : IsOpenMap (· * a)
-/
theorem IsOpen.rightCoset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (op x • U) :=
  isOpenMap_mul_right x _ h

@[to_additive]
/-
**isClosedMap_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_mul_right (a : G) : IsClosedMap (· * a)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h
-/
theorem isClosedMap_mul_right (a : G) : IsClosedMap (· * a) :=
  (Homeomorph.mulRight a).isClosedMap

@[to_additive IsClosed.right_addCoset]
/-
**IsClosed.rightCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.rightCoset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (op x 
• U)
参数：h : IsClosed U；x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosedMap_mul_right`：isClosedMap_mul_right (a : G) : IsClosedMap (· * 
a)
-/
theorem IsClosed.rightCoset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (op x • U) :=
  isClosedMap_mul_right x _ h

@[to_additive (attr := simp)]
/-
**Filter.map_mul_right_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_mul_right_nhdsNE {c a : G} : map (· * c) (𝓝[!=] a) = (𝓝[!=] (a 
* c))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `Set.preimage_mul_right_singleton`：preimage_mul_right_singleton : (· * a)
 ⁻¹' {b} = {b * a⁻¹}
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.map_mul_right_nhdsNE {c a : G} :
    map (· * c) (𝓝[≠] a) = (𝓝[≠] (a * c)) := by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive]
/-
**discreteTopology_iff_isOpen_singleton_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_iff_isOpen_singleton_one : DiscreteTopology G ↔ IsOpen ({
1} : Set G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.IsPretransitive.discreteTopology_iff`：discreteTopology_iff (x 
: α) [IsPretransitive G α] : DiscreteTopology α ↔ IsOpen {x}
· 使用定理 `MulAction.Regular.isPretransitive`：∀ {G : Type u_2} [inst : Group G], Mu
lAction.IsPretransitive G G
-/
theorem discreteTopology_iff_isOpen_singleton_one : DiscreteTopology G ↔ IsOpen ({1} : Set G) :=
  MulAction.IsPretransitive.discreteTopology_iff G 1

@[to_additive]
/-
**discreteTopology_of_isOpen_singleton_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_of_isOpen_singleton_one (h : IsOpen ({1} : Set G)) : Disc
reteTopology G
参数：h : IsOpen ({1} : Set G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `discreteTopology_iff_isOpen_singleton_one`：discreteTopology_iff_isOpen_s
ingleton_one : DiscreteTopology G ↔ IsOpen ({1} : Set G)
-/
theorem discreteTopology_of_isOpen_singleton_one (h : IsOpen ({1} : Set G)) :
    DiscreteTopology G :=
  discreteTopology_iff_isOpen_singleton_one.mpr h

@[to_additive]
/-
**smul_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_connectedComponent (g h : G) : g • connectedComponent h = connectedCo
mponent (g * h)
参数：g h : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsCoinducing.image_connectedComponent`：Topology.IsCoinducing.im
age_connectedComponent {f : α -> β} (hf : IsCoinducing f) (h_fibers : forall y :
 β, IsConnected (f ⁻¹' {y})) (a : α)…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `Homeomorph.isQuotientMap`：isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_mul_left_singleton`：preimage_mul_left_singleton : (a * ·) ⁻
¹' {b} = {a⁻¹ * b}
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem smul_connectedComponent (g h : G) : g • connectedComponent h = connectedComponent (g * h) :=
  (Homeomorph.mulLeft g).isQuotientMap.image_connectedComponent (by simp [isConnected_singleton]) h

@[to_additive]
/-
**totallyDisconnectedSpace_iff_connectedComponent_one** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：totallyDisconnectedSpace_iff_connectedComponent_one : TotallyDisconnectedS
pace G ↔ connectedComponent (1 : G) = {1}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `connectedComponent_eq_singleton`：∀ {α : Type u} [inst : TopologicalSpace
 α] [TotallyDisconnectedSpace α] (x : α), connectedComponent x = {x}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `totallyDisconnectedSpace_iff_connectedComponent_singleton`：totallyDiscon
nectedSpace_iff_connectedComponent_singleton : TotallyDisconnectedSpace α ↔ fora
ll x : α, connectedComponent x = {x}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `smul_connectedComponent`：smul_connectedComponent (g h : G) : g • connect
edComponent h = connectedComponent (g * h)
· 使用引理 `Set.smul_set_singleton`：smul_set_singleton : a • ({b} : Set β) = {a • b}
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
-/
theorem totallyDisconnectedSpace_iff_connectedComponent_one :
    TotallyDisconnectedSpace G ↔ connectedComponent (1 : G) = {1} :=
  ⟨fun _ ↦ connectedComponent_eq_singleton 1,
    fun h ↦ totallyDisconnectedSpace_iff_connectedComponent_singleton.mpr fun g ↦ by
      rw [← mul_one g, ← smul_connectedComponent, h, Set.smul_set_singleton, smul_eq_mul]⟩

@[to_additive]
/-
**Filter.tendsto_mul_const_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.tendsto_mul_const_iff (b : G) {c : G} {f : α -> G} {l : Filter α} :
 Tendsto (f · * b) l (𝓝 (c * b)) ↔ Tendsto f l (𝓝 c)
参数：b : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `Filter.Tendsto.mul_const`：Filter.Tendsto.mul_const {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) 
x (𝓝 (a * b))
-/
lemma Filter.tendsto_mul_const_iff (b : G) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (f · * b) l (𝓝 (c * b)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨?_, Tendsto.mul_const b⟩
  convert! Tendsto.mul_const b⁻¹ using 3 <;> rw [mul_inv_cancel_right]

@[to_additive]
/-
**Filter.tendsto_const_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.tendsto_const_mul_iff (b : G) {c : G} {f : α -> G} {l : Filter α} :
 Tendsto (b * f ·) l (𝓝 (b * c)) ↔ Tendsto f l (𝓝 c)
参数：b : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
-/
lemma Filter.tendsto_const_mul_iff (b : G) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (b * f ·) l (𝓝 (b * c)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨?_, Tendsto.const_mul b⟩
  convert! Tendsto.const_mul b⁻¹ using 3 <;> rw [inv_mul_cancel_left]

end ContinuousMulGroup

/-!
### `ContinuousInv` and `ContinuousNeg`
-/

section ContinuousInv

variable [TopologicalSpace G] [Inv G] [ContinuousInv G]

@[to_additive]
/-
**ContinuousInv.induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousInv.induced {α : Type*} {β : Type*} {F : Type*} [FunLike F α β] 
[Group α] [DivisionMonoid β] [MonoidHomClass F α β] [tβ : TopologicalSpace β] [C
ontinuousInv β] (f : F) : @ContinuousInv α (tβ.induced f) _
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `Continuous.fun_inv`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Inv G]   [ContinuousInv G] {f : 
X → G}, …
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
theorem ContinuousInv.induced {α : Type*} {β : Type*} {F : Type*} [FunLike F α β] [Group α]
    [DivisionMonoid β] [MonoidHomClass F α β] [tβ : TopologicalSpace β] [ContinuousInv β] (f : F) :
    @ContinuousInv α (tβ.induced f) _ := by
  let _tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_inv]
  fun_prop

@[to_additive]
/-
**Specializes.inv** 是 Mathlib 中的一个定理，位于命名空间 `Specializes`。
形式化陈述：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Inv G] [ContinuousInv
 G] {x y : G}, x ⤳ y → x⁻¹ ⤳ y⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
protected theorem Specializes.inv {x y : G} (h : x ⤳ y) : (x⁻¹) ⤳ (y⁻¹) :=
  h.map continuous_inv

@[to_additive]
/-
**Inseparable.inv** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Inv G] [ContinuousInv
 G] {x y : G},   Inseparable x y → Inseparable x⁻¹ y⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.map`：map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
protected theorem Inseparable.inv {x y : G} (h : Inseparable x y) : Inseparable (x⁻¹) (y⁻¹) :=
  h.map continuous_inv

@[to_additive]
/-
**Specializes.zpow** 是 Mathlib 中的一个定理，位于命名空间 `Specializes`。
形式化陈述：∀ {G : Type u_1} [inst : DivInvMonoid G] [inst_1 : TopologicalSpace G] [Co
ntinuousMul G] [ContinuousInv G] {x y : G},   x ⤳ y → ∀ (m : ℤ), (x ^ m) ⤳ (y ^ 
m)
参数：m : ℤ；x ^ m；y ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Specializes.pow`：∀ {M : Type u_6} [inst : Monoid M] [inst_1 : Topologica
lSpace M] [ContinuousMul M] {a b : M},   a ⤳ b → ∀ (n : ℕ), (a ^ n) ⤳ (b ^ n)
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Specializes.inv`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : In
v G] [ContinuousInv G] {x y : G}, x ⤳ y → x⁻¹ ⤳ y⁻¹
-/
protected theorem Specializes.zpow {G : Type*} [DivInvMonoid G] [TopologicalSpace G]
    [ContinuousMul G] [ContinuousInv G] {x y : G} (h : x ⤳ y) : ∀ m : ℤ, (x ^ m) ⤳ (y ^ m)
  | .ofNat n => by simpa using h.pow n
  | .negSucc n => by simpa using (h.pow (n + 1)).inv

@[to_additive]
/-
**Inseparable.zpow** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：∀ {G : Type u_1} [inst : DivInvMonoid G] [inst_1 : TopologicalSpace G] [Co
ntinuousMul G] [ContinuousInv G] {x y : G},   Inseparable x y → ∀ (m : ℤ), Insep
arable (x ^ m) (y ^ m)
参数：m : ℤ；x ^ m；y ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.antisymm`：Specializes.antisymm (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x
 ~ᵢ y
· 使用定理 `Specializes.zpow`：∀ {G : Type u_1} [inst : DivInvMonoid G] [inst_1 : Top
ologicalSpace G] [ContinuousMul G] [ContinuousInv G] {x y : G},   x ⤳ y → ∀ (m :
 ℤ), (…
· 使用定理 `Inseparable.specializes`：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y
· 使用定理 `Inseparable.specializes'`：Inseparable.specializes' (h : x ~ᵢ y) : y ⤳ x
-/
protected theorem Inseparable.zpow {G : Type*} [DivInvMonoid G] [TopologicalSpace G]
    [ContinuousMul G] [ContinuousInv G] {x y : G} (h : Inseparable x y) (m : ℤ) :
    Inseparable (x ^ m) (y ^ m) :=
  (h.specializes.zpow m).antisymm (h.specializes'.zpow m)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousInv (ULift G) :=
  ⟨continuous_uliftUp.comp (continuous_inv.comp continuous_uliftDown)⟩

@[to_additive]
/-
**continuousOn_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_inv {s : Set G} : ContinuousOn Inv.inv s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
theorem continuousOn_inv {s : Set G} : ContinuousOn Inv.inv s :=
  continuous_inv.continuousOn

@[to_additive]
/-
**continuousWithinAt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_inv {s : Set G} {x : G} : ContinuousWithinAt Inv.inv s 
x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
theorem continuousWithinAt_inv {s : Set G} {x : G} : ContinuousWithinAt Inv.inv s x :=
  continuous_inv.continuousWithinAt

@[to_additive]
/-
**continuousAt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_inv {x : G} : ContinuousAt Inv.inv x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
theorem continuousAt_inv {x : G} : ContinuousAt Inv.inv x :=
  continuous_inv.continuousAt

@[to_additive]
/-
**tendsto_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv (a : G) : Tendsto Inv.inv (𝓝 a) (𝓝 a⁻¹)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousAt_inv`：continuousAt_inv {x : G} : ContinuousAt Inv.inv x
-/
theorem tendsto_inv (a : G) : Tendsto Inv.inv (𝓝 a) (𝓝 a⁻¹) :=
  continuousAt_inv

variable [TopologicalSpace α] {f : α → G} {s : Set α} {x : α}

@[to_additive]
/-
**OrderDual.instContinuousInv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instContinuousInv : ContinuousInv Gᵒᵈ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instContinuousInv : ContinuousInv Gᵒᵈ := ‹ContinuousInv G›

@[to_additive]
/-
**Prod.continuousInv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.continuousInv [TopologicalSpace H] [Inv H] [ContinuousInv H] : Contin
uousInv (G × H)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst'`：Continuous.fst' {f : X -> Z} (hf : Continuous f) : Cont
inuous fun x : X × Y => f x.fst
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `Continuous.snd'`：Continuous.snd' {f : Y -> Z} (hf : Continuous f) : Cont
inuous fun x : X × Y => f x.snd
-/
instance Prod.continuousInv [TopologicalSpace H] [Inv H] [ContinuousInv H] :
    ContinuousInv (G × H) :=
  ⟨continuous_inv.fst'.prodMk continuous_inv.snd'⟩

variable {ι : Type*}

@[to_additive]
/-
**Pi.continuousInv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.continuousInv {C : ι -> Type*} [forall i, TopologicalSpace (C i)] [fora
ll i, Inv (C i)] [forall i, ContinuousInv (C i)] : ContinuousInv (forall i, C i)
 where continuous_inv
参数：C i；C i；C i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.inv`：Continuous.inv (hf : Continuous f) : Continuous f⁻¹
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
instance Pi.continuousInv {C : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, Inv (C i)]
    [∀ i, ContinuousInv (C i)] : ContinuousInv (∀ i, C i) where
  continuous_inv := continuous_pi fun i => (continuous_apply i).inv

/-- A version of `Pi.continuousInv` for non-dependent functions. It is needed because sometimes
Lean fails to use `Pi.continuousInv` for non-dependent functions. -/
@[to_additive
  /-- A version of `Pi.continuousNeg` for non-dependent functions. It is needed
  because sometimes Lean fails to use `Pi.continuousNeg` for non-dependent functions. -/]
/-
**Pi.has_continuous_inv'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.has_continuous_inv' : ContinuousInv (ι -> G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.has_continuous_inv' : ContinuousInv (ι → G) :=
  Pi.continuousInv

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) continuousInv_of_discreteTopology [TopologicalSpace H] [Inv H]
    [DiscreteTopology H] : ContinuousInv H :=
  ⟨continuous_of_discreteTopology⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) continuousInv_of_indiscreteTopology [TopologicalSpace H] [Inv H]
    [IndiscreteTopology H] : ContinuousInv H :=
  ⟨continuous_of_indiscreteTopology⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) continuousDiv_of_discreteTopology [TopologicalSpace H] [Div H]
    [DiscreteTopology H] : ContinuousDiv H :=
  ⟨continuous_of_discreteTopology⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) continuousDiv_of_indiscreteTopology [TopologicalSpace H] [Div H]
    [IndiscreteTopology H] : ContinuousDiv H :=
  ⟨continuous_of_indiscreteTopology⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) topologicalGroup_of_discreteTopology
    [TopologicalSpace H] [Group H] [DiscreteTopology H] : IsTopologicalGroup H := ⟨⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) topologicalGroup_of_indiscreteTopology
    [TopologicalSpace H] [Group H] [IndiscreteTopology H] : IsTopologicalGroup H := ⟨⟩

section PointwiseLimits

variable (G₁ G₂ : Type*) [TopologicalSpace G₂] [T2Space G₂]

@[to_additive]
/-
**isClosed_setOfPred_map_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_setOfPred_map_inv [Inv G₁] [Inv G₂] [ContinuousInv G₂] : IsClosed
 { f : G₁ -> G₂ | forall x, f x⁻¹ = (f x)⁻¹ }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Continuous.inv`：Continuous.inv (hf : Continuous f) : Continuous f⁻¹
-/
theorem isClosed_setOfPred_map_inv [Inv G₁] [Inv G₂] [ContinuousInv G₂] :
    IsClosed { f : G₁ → G₂ | ∀ x, f x⁻¹ = (f x)⁻¹ } := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_eq (continuous_apply _) (continuous_apply _).inv

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_map_inv := isClosed_setOfPred_map_inv

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_map_neg := isClosed_setOfPred_map_neg

end PointwiseLimits

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace H] [Inv H] [ContinuousInv H] : ContinuousNeg (Additive H) where
  continuous_neg := @continuous_inv H _ _ _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace H] [Neg H] [ContinuousNeg H] : ContinuousInv (Multiplicative H) where
  continuous_inv := @continuous_neg H _ _ _

end ContinuousInv

section ContinuousInvolutiveInv

variable [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] {s : Set G}

@[to_additive (attr := simp)]
/-
**tendsto_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_iff {l : Filter α} {m : α -> G} {a : G} : Tendsto (fun x => (m
 x)⁻¹) l (𝓝 a⁻¹) ↔ Tendsto m l (𝓝 a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Filter.Tendsto.inv`：Filter.Tendsto.inv {f : α -> G} {l : Filter α} {y : 
G} (h : Tendsto f l (𝓝 y)) : Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹)
-/
theorem tendsto_inv_iff {l : Filter α} {m : α → G} {a : G} :
    Tendsto (fun x => (m x)⁻¹) l (𝓝 a⁻¹) ↔ Tendsto m l (𝓝 a) :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, Tendsto.inv⟩

@[to_additive]
/-
**IsCompact.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.inv (hs : IsCompact s) : IsCompact s⁻¹
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
theorem IsCompact.inv (hs : IsCompact s) : IsCompact s⁻¹ := by
  rw [← image_inv_eq_inv]
  exact hs.image continuous_inv

variable (G)

/-- Inversion in a topological group as a homeomorphism. -/
@[to_additive /-- Negation in a topological group as a homeomorphism. -/]
/-
**Homeomorph.inv** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：(G : Type u_1) → [inst : TopologicalSpace G] → [inst_1 : InvolutiveInv G] 
→ [ContinuousInv G] → G ≃ₜ G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inversion in a topological group as a homeomorphism.
-/
protected def Homeomorph.inv (G : Type*) [TopologicalSpace G] [InvolutiveInv G]
    [ContinuousInv G] : G ≃ₜ G :=
  { Equiv.inv G with }

@[to_additive (attr := simp)]
/-
**Homeomorph.symm_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Homeomorph.symm_inv {G : Type*} [TopologicalSpace G] [InvolutiveInv G] [Co
ntinuousInv G] : (Homeomorph.inv G).symm = Homeomorph.inv G
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Homeomorph.symm_inv {G : Type*} [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] :
    (Homeomorph.inv G).symm = Homeomorph.inv G := rfl

@[to_additive (attr := simp)]
/-
**Homeomorph.coe_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Homeomorph.coe_inv {G : Type*} [TopologicalSpace G] [InvolutiveInv G] [Con
tinuousInv G] : ⇑(Homeomorph.inv G) = Inv.inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Homeomorph.coe_inv {G : Type*} [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] :
    ⇑(Homeomorph.inv G) = Inv.inv := rfl

@[to_additive]
/-
**nhds_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_inv (a : G) : 𝓝 a⁻¹ = (𝓝 a)⁻¹
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
-/
theorem nhds_inv (a : G) : 𝓝 a⁻¹ = (𝓝 a)⁻¹ :=
  ((Homeomorph.inv G).map_nhds_eq a).symm

@[to_additive]
/-
**isOpenMap_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_inv : IsOpenMap (Inv.inv : G -> G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
-/
theorem isOpenMap_inv : IsOpenMap (Inv.inv : G → G) :=
  (Homeomorph.inv _).isOpenMap

@[to_additive]
/-
**isClosedMap_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_inv : IsClosedMap (Inv.inv : G -> G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h
-/
theorem isClosedMap_inv : IsClosedMap (Inv.inv : G → G) :=
  (Homeomorph.inv _).isClosedMap

variable {G}

@[to_additive]
/-
**IsOpen.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.inv (hs : IsOpen s) : IsOpen s⁻¹
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
theorem IsOpen.inv (hs : IsOpen s) : IsOpen s⁻¹ :=
  hs.preimage continuous_inv

@[to_additive]
/-
**IsClosed.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.inv (hs : IsClosed s) : IsClosed s⁻¹
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
theorem IsClosed.inv (hs : IsClosed s) : IsClosed s⁻¹ :=
  hs.preimage continuous_inv

@[to_additive]
/-
**inv_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_closure : forall s : Set G, (closure s)⁻¹ = closure s⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.preimage_closure`：preimage_closure (h : X ≃ₜ Y) (s : Set Y) :
 h ⁻¹' closure s = closure (h ⁻¹' s)
-/
theorem inv_closure : ∀ s : Set G, (closure s)⁻¹ = closure s⁻¹ :=
  (Homeomorph.inv G).preimage_closure

variable [TopologicalSpace α] {f : α → G} {s : Set α} {x : α}

@[to_additive (attr := simp)]
/-
**continuous_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_inv_iff : Continuous f⁻¹ ↔ Continuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.comp_continuous_iff`：comp_continuous_iff (h : X ≃ₜ Y) {f : Z 
-> X} : Continuous (h ∘ f) ↔ Continuous f
-/
lemma continuous_inv_iff : Continuous f⁻¹ ↔ Continuous f := (Homeomorph.inv G).comp_continuous_iff

@[to_additive (attr := simp)]
/-
**continuousAt_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuousAt_inv_iff : ContinuousAt f⁻¹ x ↔ ContinuousAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.comp_continuousAt_iff`：comp_continuousAt_iff (h : X ≃ₜ Y) (f 
: Z -> X) (z : Z) : ContinuousAt (h ∘ f) z ↔ ContinuousAt f z
-/
lemma continuousAt_inv_iff : ContinuousAt f⁻¹ x ↔ ContinuousAt f x :=
  (Homeomorph.inv G).comp_continuousAt_iff _ _

@[to_additive (attr := simp)]
/-
**continuousOn_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuousOn_inv_iff : ContinuousOn f⁻¹ s ↔ ContinuousOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.comp_continuousOn_iff`：comp_continuousOn_iff (h : X ≃ₜ Y) (f 
: Z -> X) (s : Set Z) : ContinuousOn (h ∘ f) s ↔ ContinuousOn f s
-/
lemma continuousOn_inv_iff : ContinuousOn f⁻¹ s ↔ ContinuousOn f s :=
  (Homeomorph.inv G).comp_continuousOn_iff _ _

@[to_additive] alias ⟨Continuous.of_inv, _⟩ := continuous_inv_iff
@[to_additive] alias ⟨ContinuousAt.of_inv, _⟩ := continuousAt_inv_iff
@[to_additive] alias ⟨ContinuousOn.of_inv, _⟩ := continuousOn_inv_iff

@[to_additive (attr := simp)]
/-
**Filter.inv_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.inv_nhdsNE {a : G} : (𝓝[!=] a)⁻¹ = 𝓝[!=] (a⁻¹)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.compl_inv`：compl_inv : sᶜ⁻¹ = s⁻¹ᶜ
· 使用定理 `Set.inv_singleton`：inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.inv_nhdsNE {a : G} : (𝓝[≠] a)⁻¹ = 𝓝[≠] (a⁻¹) := by
  convert! (Homeomorph.inv G).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

end ContinuousInvolutiveInv

section LatticeOps

variable {ι' : Sort*} [Inv G]

@[to_additive]
/-
**continuousInv_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousInv_sInf {ts : Set (TopologicalSpace G)} (h : forall t in ts, @C
ontinuousInv G t _) : @ContinuousInv G (sInf ts) _
参数：TopologicalSpace G；h : forall t in ts, @ContinuousInv G t _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_sInf_rng`：continuous_sInf_rng {t₁ : TopologicalSpace α} {T : 
Set (TopologicalSpace β)} : Continuous[t₁, sInf T] f ↔ forall t in T, Continuous
[t₁, t] f
· 使用定理 `continuous_sInf_dom`：continuous_sInf_dom {t₁ : Set (TopologicalSpace α)}
 {t₂ : TopologicalSpace β} {t : TopologicalSpace α} (h₁ : t in t₁) : Continuous[
t, t₂] f …
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
theorem continuousInv_sInf {ts : Set (TopologicalSpace G)}
    (h : ∀ t ∈ ts, @ContinuousInv G t _) : @ContinuousInv G (sInf ts) _ :=
  letI := sInf ts
  { continuous_inv :=
      continuous_sInf_rng.2 fun t ht =>
        continuous_sInf_dom ht (@ContinuousInv.continuous_inv G t _ (h t ht)) }

@[to_additive]
/-
**continuousInv_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousInv_iInf {ts' : ι' -> TopologicalSpace G} (h' : forall i, @Conti
nuousInv G (ts' i) _) : @ContinuousInv G (⨅ i, ts' i) _
参数：h' : forall i, @ContinuousInv G (ts' i) _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用定理 `continuousInv_sInf`：continuousInv_sInf {ts : Set (TopologicalSpace G)} (
h : forall t in ts, @ContinuousInv G t _) : @ContinuousInv G (sInf ts) _
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem continuousInv_iInf {ts' : ι' → TopologicalSpace G}
    (h' : ∀ i, @ContinuousInv G (ts' i) _) : @ContinuousInv G (⨅ i, ts' i) _ := by
  rw [← sInf_range]
  exact continuousInv_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
/-
**continuousInv_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousInv_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @ContinuousInv G t₁ _
) (h₂ : @ContinuousInv G t₂ _) : @ContinuousInv G (t₁ ⊓ t₂) _
参数：h₁ : @ContinuousInv G t₁ _；h₂ : @ContinuousInv G t₂ _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] (x y : α), x ⊓ 
y = ⨅ b, bif b then x else y
· 使用定理 `continuousInv_iInf`：continuousInv_iInf {ts' : ι' -> TopologicalSpace G} 
(h' : forall i, @ContinuousInv G (ts' i) _) : @ContinuousInv G (⨅ i, ts' i) _
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem continuousInv_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @ContinuousInv G t₁ _)
    (h₂ : @ContinuousInv G t₂ _) : @ContinuousInv G (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine continuousInv_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps

@[to_additive]
/-
**Topology.IsInducing.continuousInv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.continuousInv {G H : Type*} [Inv G] [Inv H] [Topologic
alSpace G] [TopologicalSpace H] [ContinuousInv H] {f : G -> H} (hf : IsInducing 
f) (hf_inv : forall x, f x⁻¹ = (f x)⁻¹) : ContinuousInv G
参数：hf : IsInducing f；hf_inv : forall x, f x⁻¹ = (f x)⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Continuous.fun_inv`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Inv G]   [ContinuousInv G] {f : 
X → G}, …
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
-/
theorem Topology.IsInducing.continuousInv {G H : Type*} [Inv G] [Inv H] [TopologicalSpace G]
    [TopologicalSpace H] [ContinuousInv H] {f : G → H} (hf : IsInducing f)
    (hf_inv : ∀ x, f x⁻¹ = (f x)⁻¹) : ContinuousInv G :=
  ⟨hf.continuous_iff.2 <| by simpa only [Function.comp_def, hf_inv] using hf.continuous.fun_inv⟩

section IsTopologicalGroup

/-!
### Topological groups

A topological group is a group in which the multiplication and inversion operations are
continuous. Topological additive groups are defined in the same way. Equivalently, we can require
that the division operation `x y ↦ x * y⁻¹` (resp., subtraction) is continuous.
-/

section Conj

/-
**ConjAct.units_continuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ConjAct.units_continuousConstSMul {M} [Monoid M] [TopologicalSpace M] [Con
tinuousMul M] : ContinuousConstSMul (ConjAct Mˣ) M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
instance ConjAct.units_continuousConstSMul {M} [Monoid M] [TopologicalSpace M]
    [ContinuousMul M] : ContinuousConstSMul (ConjAct Mˣ) M :=
  ⟨fun _ => (continuous_const.mul continuous_id).mul continuous_const⟩

open scoped Pointwise in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group G] [Group H] [TopologicalSpace G] [MulDistribMulAction H G]
    [ContinuousConstSMul H G] {𝒢 : Subgroup G} (h : H) [DiscreteTopology 𝒢] :
    DiscreteTopology ↑(h • 𝒢) := by
  simp only [← SetLike.coe_sort_coe, ← isDiscrete_iff_discreteTopology] at *
  refine IsDiscrete.image_of_isOpenMap ‹_› ?_ fun x y ↦ by simp
  apply IsOpenMap.of_inverse (f' := fun x ↦ h⁻¹ • x) (continuous_const_smul _) <;>
  · intro x
    simp

variable [TopologicalSpace G] [Inv G] [Mul G]

/-- Conjugation is jointly continuous on `G × G` when both `mul` and `inv` are continuous. -/
@[to_additive continuous_addConj_prod
  /-- Conjugation is jointly continuous on `G × G` when both `add` and `neg` are continuous. -/]
/-
**IsTopologicalGroup.continuous_conj_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.continuous_conj_prod [ContinuousMul G] [ContinuousInv G
] : Continuous fun g : G × G => g.fst * g.snd * g.fst⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
-/
theorem IsTopologicalGroup.continuous_conj_prod [ContinuousMul G] [ContinuousInv G] :
    Continuous fun g : G × G => g.fst * g.snd * g.fst⁻¹ :=
  continuous_mul.mul (continuous_inv.comp continuous_fst)

/-- Conjugation by a fixed element is continuous when `mul` is continuous. -/
@[to_additive (attr := continuity, fun_prop)
  /-- Conjugation by a fixed element is continuous when `add` is continuous. -/]
/-
**IsTopologicalGroup.continuous_conj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.continuous_conj [SeparatelyContinuousMul G] (g : G) : C
ontinuous fun h : G => g * h * g⁻¹
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
-/
theorem IsTopologicalGroup.continuous_conj [SeparatelyContinuousMul G] (g : G) :
    Continuous fun h : G => g * h * g⁻¹ :=
  (continuous_mul_const g⁻¹).comp (continuous_const_mul g)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] :
    ContinuousConstSMul (ConjAct G) G where
  continuous_const_smul h := IsTopologicalGroup.continuous_conj (ConjAct.ofConjAct h)

/-- Conjugation acting on fixed element of the group is continuous when both `mul` and
`inv` are continuous. -/
@[to_additive (attr := continuity, fun_prop)
  /-- Conjugation acting on fixed element of the additive group is continuous when both
    `add` and `neg` are continuous. -/]
/-
**IsTopologicalGroup.continuous_conj'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.continuous_conj' [ContinuousMul G] [ContinuousInv G] (h
 : G) : Continuous fun g : G => g * h * g⁻¹
参数：h : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
theorem IsTopologicalGroup.continuous_conj' [ContinuousMul G] [ContinuousInv G] (h : G) :
    Continuous fun g : G => g * h * g⁻¹ :=
  (continuous_mul_const h).mul continuous_inv

end Conj

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [TopologicalSpace α] {f : α → G}
  {s : Set α} {x : α}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalGroup (ULift G) where

section ZPow

@[to_additive (attr := continuity, fun_prop)]
/-
**continuous_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Group G] [IsTopologic
alGroup G] (z : ℤ), Continuous fun a => a ^ z
参数：z : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `continuous_pow`：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : M
onoid M] [ContinuousMul M] (n : ℕ), Continuous fun a => a ^ n
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Continuous.fun_inv`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Inv G]   [ContinuousInv G] {f : 
X → G}, …
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
-/
theorem continuous_zpow : ∀ z : ℤ, Continuous fun a : G => a ^ z
  | Int.ofNat n => by simpa using continuous_pow n
  | Int.negSucc n => by simpa using (continuous_pow (n + 1)).fun_inv
/-
**AddGroup.continuousConstSMul_int** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddGroup.continuousConstSMul_int {A} [AddGroup A] [TopologicalSpace A] [Is
TopologicalAddGroup A] : ContinuousConstSMul Int A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_zsmul`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : A
ddGroup G] [IsTopologicalAddGroup G] (z : ℤ),   Continuous fun a => z • a
-/
instance AddGroup.continuousConstSMul_int {A} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] : ContinuousConstSMul ℤ A :=
  ⟨continuous_zsmul⟩
/-
**AddGroup.continuousSMul_int** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddGroup.continuousSMul_int {A} [AddGroup A] [TopologicalSpace A] [IsTopol
ogicalAddGroup A] : ContinuousSMul Int A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_prod_of_discrete_left`：continuous_prod_of_discrete_left [Disc
reteTopology α] {f : α × β -> γ} : Continuous f ↔ forall a, Continuous (f ⟨a, ·⟩
)
· 使用定理 `instDiscreteTopologyInt`：DiscreteTopology ℤ
· 使用定理 `continuous_zsmul`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : A
ddGroup G] [IsTopologicalAddGroup G] (z : ℤ),   Continuous fun a => z • a
-/
instance AddGroup.continuousSMul_int {A} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] : ContinuousSMul ℤ A :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_zsmul⟩

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]
/-
**Continuous.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.zpow {f : α -> G} (h : Continuous f) (z : Int) : Continuous (f 
^ z)
参数：h : Continuous f；z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_zpow`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Gr
oup G] [IsTopologicalGroup G] (z : ℤ), Continuous fun a => a ^ z
-/
theorem Continuous.zpow {f : α → G} (h : Continuous f) (z : ℤ) : Continuous (f ^ z) :=
  (continuous_zpow z).comp h

@[to_additive]
/-
**continuousOn_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_zpow {s : Set G} (z : Int) : ContinuousOn (fun x => x ^ z) s
参数：z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_zpow`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Gr
oup G] [IsTopologicalGroup G] (z : ℤ), Continuous fun a => a ^ z
-/
theorem continuousOn_zpow {s : Set G} (z : ℤ) : ContinuousOn (fun x => x ^ z) s :=
  (continuous_zpow z).continuousOn

@[to_additive]
/-
**continuousAt_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_zpow (x : G) (z : Int) : ContinuousAt (fun x => x ^ z) x
参数：x : G；z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_zpow`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Gr
oup G] [IsTopologicalGroup G] (z : ℤ), Continuous fun a => a ^ z
-/
theorem continuousAt_zpow (x : G) (z : ℤ) : ContinuousAt (fun x => x ^ z) x :=
  (continuous_zpow z).continuousAt

@[to_additive]
/-
**Filter.Tendsto.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.zpow {α} {l : Filter α} {f : α -> G} {x : G} (hf : Tendsto 
f l (𝓝 x)) (z : Int) : Tendsto (fun x => f x ^ z) l (𝓝 (x ^ z))
参数：hf : Tendsto f l (𝓝 x)；z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuousAt_zpow`：continuousAt_zpow (x : G) (z : Int) : ContinuousAt (f
un x => x ^ z) x
-/
theorem Filter.Tendsto.zpow {α} {l : Filter α} {f : α → G} {x : G} (hf : Tendsto f l (𝓝 x))
    (z : ℤ) : Tendsto (fun x => f x ^ z) l (𝓝 (x ^ z)) :=
  (continuousAt_zpow _ _).tendsto.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**ContinuousWithinAt.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.zpow {f : α -> G} {x : α} {s : Set α} (hf : ContinuousW
ithinAt f s x) (z : Int) : ContinuousWithinAt (f ^ z) s x
参数：hf : ContinuousWithinAt f s x；z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.zpow`：Filter.Tendsto.zpow {α} {l : Filter α} {f : α -> G}
 {x : G} (hf : Tendsto f l (𝓝 x)) (z : Int) : Tendsto (fun x => f x ^ z) l (𝓝 (x
 ^ z))
-/
theorem ContinuousWithinAt.zpow {f : α → G} {x : α} {s : Set α} (hf : ContinuousWithinAt f s x)
    (z : ℤ) : ContinuousWithinAt (f ^ z) s x :=
  Filter.Tendsto.zpow hf z

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**ContinuousAt.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.zpow {f : α -> G} {x : α} (hf : ContinuousAt f x) (z : Int) :
 ContinuousAt (f ^ z) x
参数：hf : ContinuousAt f x；z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.zpow`：Filter.Tendsto.zpow {α} {l : Filter α} {f : α -> G}
 {x : G} (hf : Tendsto f l (𝓝 x)) (z : Int) : Tendsto (fun x => f x ^ z) l (𝓝 (x
 ^ z))
-/
theorem ContinuousAt.zpow {f : α → G} {x : α} (hf : ContinuousAt f x) (z : ℤ) :
    ContinuousAt (f ^ z) x :=
  Filter.Tendsto.zpow hf z

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**ContinuousOn.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.zpow {f : α -> G} {s : Set α} (hf : ContinuousOn f s) (z : In
t) : ContinuousOn (f ^ z) s
参数：hf : ContinuousOn f s；z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.zpow`：ContinuousWithinAt.zpow {f : α -> G} {x : α} {s
 : Set α} (hf : ContinuousWithinAt f s x) (z : Int) : ContinuousWithinAt (f ^ z)
 s x
-/
theorem ContinuousOn.zpow {f : α → G} {s : Set α} (hf : ContinuousOn f s) (z : ℤ) :
    ContinuousOn (f ^ z) s := fun x hx => (hf x hx).zpow z

end ZPow

section OrderedCommGroup

variable [TopologicalSpace H] [CommGroup H] [PartialOrder H] [IsOrderedMonoid H]

section mul

variable [ContinuousMul H]

@[to_additive (attr := simp)]
/-
**Filter.map_mul_left_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_mul_left_nhdsGT {c a : H} : map (c * ·) (𝓝[>] a) = 𝓝[>] (c * a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Ioi`：preimage_mul_const_Ioi : (fun x => x * a) ⁻¹
' Ioi b = Ioi (b / a)
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.map_mul_left_nhdsGT {c a : H} : map (c * ·) (𝓝[>] a) = 𝓝[>] (c * a) := by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [mul_comm]

@[to_additive (attr := simp)]
/-
**Filter.map_mul_left_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_mul_left_nhdsLT {c a : H} : map (c * ·) (𝓝[<] a) = 𝓝[<] (c * a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Set.preimage_mul_const_Iio`：preimage_mul_const_Iio : (fun x => x * a) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.map_mul_left_nhdsLT {c a : H} : map (c * ·) (𝓝[<] a) = 𝓝[<] (c * a) := by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [mul_comm]

@[to_additive (attr := simp)]
/-
**Filter.map_mul_right_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_mul_right_nhdsGT {c a : H} : map (· * c) (𝓝[>] a) = 𝓝[>] (a * c
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `Set.preimage_mul_const_Ioi`：preimage_mul_const_Ioi : (fun x => x * a) ⁻¹
' Ioi b = Ioi (b / a)
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.map_mul_right_nhdsGT {c a : H} : map (· * c) (𝓝[>] a) = 𝓝[>] (a * c) := by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
/-
**Filter.map_mul_right_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_mul_right_nhdsLT {c a : H} : map (· * c) (𝓝[<] a) = 𝓝[<] (a * c
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `Set.preimage_mul_const_Iio`：preimage_mul_const_Iio : (fun x => x * a) ⁻¹
' Iio b = Iio (b / a)
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.map_mul_right_nhdsLT {c a : H} : map (· * c) (𝓝[<] a) = 𝓝[<] (a * c) := by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

end mul

section inv

variable [ContinuousInv H]

@[to_additive (attr := simp)]
/-
**Filter.inv_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.inv_nhdsGT {a : H} : (𝓝[>] a)⁻¹ = 𝓝[<] (a⁻¹)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.inv_Ioi`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Ioi a)⁻¹ = Set.Iio a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.inv_nhdsGT {a : H} : (𝓝[>] a)⁻¹ = 𝓝[<] (a⁻¹) := by
  convert! (Homeomorph.inv H).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
/-
**Filter.inv_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.inv_nhdsLT {a : H} : (𝓝[<] a)⁻¹ = 𝓝[>] (a⁻¹)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.inv_Iio`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Iio a)⁻¹ = Set.Ioi a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.inv_nhdsLT {a : H} : (𝓝[<] a)⁻¹ = 𝓝[>] (a⁻¹) := by
  convert! (Homeomorph.inv H).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive]
/-
**tendsto_inv_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_nhdsGT {a : H} : Tendsto Inv.inv (𝓝[>] a) (𝓝[<] a⁻¹)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem tendsto_inv_nhdsGT {a : H} : Tendsto Inv.inv (𝓝[>] a) (𝓝[<] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp

@[to_additive]
/-
**tendsto_inv_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_nhdsLT {a : H} : Tendsto Inv.inv (𝓝[<] a) (𝓝[>] a⁻¹)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem tendsto_inv_nhdsLT {a : H} : Tendsto Inv.inv (𝓝[<] a) (𝓝[>] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp

@[to_additive]
/-
**tendsto_inv_nhdsGT_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_nhdsGT_inv {a : H} : Tendsto Inv.inv (𝓝[>] a⁻¹) (𝓝[<] a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `tendsto_inv_nhdsGT`：tendsto_inv_nhdsGT {a : H} : Tendsto Inv.inv (𝓝[>] a
) (𝓝[<] a⁻¹)
-/
theorem tendsto_inv_nhdsGT_inv {a : H} : Tendsto Inv.inv (𝓝[>] a⁻¹) (𝓝[<] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsGT (a := a⁻¹)

@[to_additive]
/-
**tendsto_inv_nhdsLT_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_nhdsLT_inv {a : H} : Tendsto Inv.inv (𝓝[<] a⁻¹) (𝓝[>] a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `tendsto_inv_nhdsLT`：tendsto_inv_nhdsLT {a : H} : Tendsto Inv.inv (𝓝[<] a
) (𝓝[>] a⁻¹)
-/
theorem tendsto_inv_nhdsLT_inv {a : H} : Tendsto Inv.inv (𝓝[<] a⁻¹) (𝓝[>] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsLT (a := a⁻¹)

@[to_additive]
/-
**tendsto_inv_nhdsGE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_nhdsGE {a : H} : Tendsto Inv.inv (𝓝[>=] a) (𝓝[<=] a⁻¹)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem tendsto_inv_nhdsGE {a : H} : Tendsto Inv.inv (𝓝[≥] a) (𝓝[≤] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp

@[to_additive]
/-
**tendsto_inv_nhdsLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_nhdsLE {a : H} : Tendsto Inv.inv (𝓝[<=] a) (𝓝[>=] a⁻¹)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem tendsto_inv_nhdsLE {a : H} : Tendsto Inv.inv (𝓝[≤] a) (𝓝[≥] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp

@[to_additive]
/-
**tendsto_inv_nhdsGE_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_nhdsGE_inv {a : H} : Tendsto Inv.inv (𝓝[>=] a⁻¹) (𝓝[<=] a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `tendsto_inv_nhdsGE`：tendsto_inv_nhdsGE {a : H} : Tendsto Inv.inv (𝓝[>=] 
a) (𝓝[<=] a⁻¹)
-/
theorem tendsto_inv_nhdsGE_inv {a : H} : Tendsto Inv.inv (𝓝[≥] a⁻¹) (𝓝[≤] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsGE (a := a⁻¹)

@[to_additive]
/-
**tendsto_inv_nhdsLE_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_nhdsLE_inv {a : H} : Tendsto Inv.inv (𝓝[<=] a⁻¹) (𝓝[>=] a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `tendsto_inv_nhdsLE`：tendsto_inv_nhdsLE {a : H} : Tendsto Inv.inv (𝓝[<=] 
a) (𝓝[>=] a⁻¹)
-/
theorem tendsto_inv_nhdsLE_inv {a : H} : Tendsto Inv.inv (𝓝[≤] a⁻¹) (𝓝[≥] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsLE (a := a⁻¹)

alias tendsto_inv_nhdsWithin_Iic_inv := tendsto_inv_nhdsLE_inv

end inv

end OrderedCommGroup

@[to_additive]
/-
**Prod.instIsTopologicalGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instIsTopologicalGroup [TopologicalSpace H] [Group H] [IsTopologicalG
roup H] : IsTopologicalGroup (G × H) where continuous_inv
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
-/
instance Prod.instIsTopologicalGroup [TopologicalSpace H] [Group H] [IsTopologicalGroup H] :
    IsTopologicalGroup (G × H) where
  continuous_inv := continuous_inv.prodMap continuous_inv

@[to_additive]
/-
**OrderDual.instIsTopologicalGroup** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Group G] [IsTopologic
alGroup G], IsTopologicalGroup Gᵒᵈ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instContinuousMulOrderDual`：∀ {M : Type u_3} [inst : TopologicalSpace M]
 [inst_1 : Mul M] [ContinuousMul M], ContinuousMul Mᵒᵈ
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
-/
instance OrderDual.instIsTopologicalGroup : IsTopologicalGroup Gᵒᵈ where

@[to_additive]
/-
**Pi.topologicalGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.topologicalGroup {C : β -> Type*} [forall b, TopologicalSpace (C b)] [f
orall b, Group (C b)] [forall b, IsTopologicalGroup (C b)] : IsTopologicalGroup 
(forall b, C b) where continuous_inv
参数：C b；C b；C b。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.inv`：Continuous.inv (hf : Continuous f) : Continuous f⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
instance Pi.topologicalGroup {C : β → Type*} [∀ b, TopologicalSpace (C b)] [∀ b, Group (C b)]
    [∀ b, IsTopologicalGroup (C b)] : IsTopologicalGroup (∀ b, C b) where
  continuous_inv := continuous_pi fun i => (continuous_apply i).inv

open MulOpposite

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inv α] [ContinuousInv α] : ContinuousInv αᵐᵒᵖ :=
  opHomeomorph.symm.isInducing.continuousInv unop_inv

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive /-- If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`.
-/
instance [Group α] [IsTopologicalGroup α] : IsTopologicalGroup αᵐᵒᵖ where

variable (G)

@[to_additive]
/-
**nhds_one_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_one_symm : comap Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `Homeomorph.comap_nhds_eq`：comap_nhds_eq (h : X ≃ₜ Y) (y : Y) : comap h (
𝓝 y) = 𝓝 (h.symm y)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
theorem nhds_one_symm : comap Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
  ((Homeomorph.inv G).comap_nhds_eq _).trans (congr_arg 𝓝 inv_one)

@[to_additive]
/-
**nhds_one_symm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_one_symm' : map Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
theorem nhds_one_symm' : map Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
  ((Homeomorph.inv G).map_nhds_eq _).trans (congr_arg 𝓝 inv_one)

@[to_additive]
/-
**inv_mem_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mem_nhds_one {S : Set G} (hS : S in (𝓝 1 : Filter G)) : S⁻¹ in 𝓝 (1 : 
G)
参数：hS : S in (𝓝 1 : Filter G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_one_symm'`：nhds_one_symm' : map Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G)
-/
theorem inv_mem_nhds_one {S : Set G} (hS : S ∈ (𝓝 1 : Filter G)) : S⁻¹ ∈ 𝓝 (1 : G) := by
  rwa [← nhds_one_symm'] at hS

set_option backward.defeqAttrib.useBackward true in
/-- The map `(x, y) ↦ (x, x * y)` as a homeomorphism. This is a shear mapping. -/
@[to_additive /-- The map `(x, y) ↦ (x, x + y)` as a homeomorphism. This is a shear mapping. -/]
/-
**Homeomorph.shearMulRight** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：(G : Type w) → [inst : TopologicalSpace G] → [inst_1 : Group G] → [IsTopol
ogicalGroup G] → G × G ≃ₜ G × G
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The map `(x, y) ↦ (x, x * y)` as a homeomorphism. This is a shear mapping.
-/
protected def Homeomorph.shearMulRight : G × G ≃ₜ G × G :=
  { Equiv.prodShear (Equiv.refl _) Equiv.mulLeft with }

@[to_additive (attr := simp)]
/-
**Homeomorph.shearMulRight_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.shearMulRight_coe : ⇑(Homeomorph.shearMulRight G) = fun z : G ×
 G => (z.1, z.1 * z.2)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Homeomorph.shearMulRight_coe :
    ⇑(Homeomorph.shearMulRight G) = fun z : G × G => (z.1, z.1 * z.2) :=
  rfl

@[to_additive (attr := simp)]
/-
**Homeomorph.shearMulRight_symm_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.shearMulRight_symm_coe : ⇑(Homeomorph.shearMulRight G).symm = f
un z : G × G => (z.1, z.1⁻¹ * z.2)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Homeomorph.shearMulRight_symm_coe :
    ⇑(Homeomorph.shearMulRight G).symm = fun z : G × G => (z.1, z.1⁻¹ * z.2) :=
  rfl

variable {G}

@[to_additive]
/-
**Topology.IsInducing.topologicalGroup** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInd
ucing`。
形式化陈述：∀ {G : Type w} {H : Type x} [inst : TopologicalSpace G] [inst_1 : Group G]
 [IsTopologicalGroup G] {F : Type u_1}   [inst_3 : Group H] [inst_4 : Topologica
lSpace H] [inst_5 : FunLike F H G] [MonoidHomClass F H G] (f : F),   Topology.Is
Inducing ⇑f → IsTopologicalGroup H
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.continuousMul`：Topology.IsInducing.continuousMul {M 
N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] [TopologicalSpa
ce M] [TopologicalSpace…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Topology.IsInducing.continuousInv`：Topology.IsInducing.continuousInv {G 
H : Type*} [Inv G] [Inv H] [TopologicalSpace G] [TopologicalSpace H] [Continuous
Inv H] {f : G -> H} (hf…
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
-/
protected theorem Topology.IsInducing.topologicalGroup {F : Type*} [Group H] [TopologicalSpace H]
    [FunLike F H G] [MonoidHomClass F H G] (f : F) (hf : IsInducing f) : IsTopologicalGroup H :=
  { toContinuousMul := hf.continuousMul _
    toContinuousInv := hf.continuousInv (map_inv f) }

@[to_additive]
/-
**topologicalGroup_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：topologicalGroup_induced {F : Type*} [Group H] [FunLike F H G] [MonoidHomC
lass F H G] (f : F) : @IsTopologicalGroup H (induced f ‹_›) _
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.topologicalGroup`：∀ {G : Type w} {H : Type x} [inst 
: TopologicalSpace G] [inst_1 : Group G] [IsTopologicalGroup G] {F : Type u_1}  
 [inst_3 : Group H] [inst_…
-/
theorem topologicalGroup_induced {F : Type*} [Group H] [FunLike F H G] [MonoidHomClass F H G]
    (f : F) :
    @IsTopologicalGroup H (induced f ‹_›) _ :=
  letI := induced f ‹_›
  IsInducing.topologicalGroup f ⟨rfl⟩

namespace Subgroup

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : Subgroup G) : IsTopologicalGroup S :=
  IsInducing.subtypeVal.topologicalGroup S.subtype

end Subgroup

/-- The (topological-space) closure of a subgroup of a topological group is
itself a subgroup. -/
@[to_additive
  /-- The (topological-space) closure of an additive subgroup of an additive topological group is
  itself an additive subgroup. -/]
/-
**Subgroup.topologicalClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subgroup.topologicalClosure (s : Subgroup G) : Subgroup G
参数：s : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Subgroup.topologicalClosure (s : Subgroup G) : Subgroup G :=
  { s.toSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set G)
    inv_mem' := fun {g} hg => by simpa only [← Set.mem_inv, inv_closure, inv_coe_set] using hg }

@[to_additive (attr := simp)]
/-
**Subgroup.topologicalClosure_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.topologicalClosure_coe {s : Subgroup G} : (s.topologicalClosure :
 Set G) = _root_.closure s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subgroup.topologicalClosure_coe {s : Subgroup G} :
    (s.topologicalClosure : Set G) = _root_.closure s :=
  rfl

@[to_additive]
/-
**Subgroup.le_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.le_topologicalClosure (s : Subgroup G) : s <= s.topologicalClosur
e
参数：s : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Subgroup.le_topologicalClosure (s : Subgroup G) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

@[to_additive]
/-
**Subgroup.isClosed_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.isClosed_topologicalClosure (s : Subgroup G) : IsClosed (s.topolo
gicalClosure : Set G)
参数：s : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem Subgroup.isClosed_topologicalClosure (s : Subgroup G) :
    IsClosed (s.topologicalClosure : Set G) := isClosed_closure

@[to_additive]
/-
**Subgroup.topologicalClosure_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.topologicalClosure_minimal (s : Subgroup G) {t : Subgroup G} (h :
 s <= t) (ht : IsClosed (t : Set G)) : s.topologicalClosure <= t
参数：s : Subgroup G；h : s <= t；ht : IsClosed (t : Set G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem Subgroup.topologicalClosure_minimal (s : Subgroup G) {t : Subgroup G} (h : s ≤ t)
    (ht : IsClosed (t : Set G)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

@[to_additive (attr := gcongr)]
/-
**Subgroup.topologicalClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.topologicalClosure_mono {s t : Subgroup G} (h : s <= t) : s.topol
ogicalClosure <= t.topologicalClosure
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem Subgroup.topologicalClosure_mono {s t : Subgroup G} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  _root_.closure_mono h

@[to_additive]
/-
**DenseRange.topologicalClosure_map_subgroup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.topologicalClosure_map_subgroup [Group H] [TopologicalSpace H] 
[IsTopologicalGroup H] {f : G ->* H} (hf : Continuous f) (hf' : DenseRange f) {s
 : Subgroup G} (hs : s.topologicalClosure = ⊤) : (s.map f).topologicalClosure = 
⊤
参数：hf : Continuous f；hf' : DenseRange f；hs : s.topologicalClosure = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `DenseRange.dense_image`：DenseRange.dense_image {f : X -> Y} (hf' : Dense
Range f) (hf : Continuous f) (hs : Dense s) : Dense (f '' s)
-/
theorem DenseRange.topologicalClosure_map_subgroup [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {f : G →* H} (hf : Continuous f) (hf' : DenseRange f) {s : Subgroup G}
    (hs : s.topologicalClosure = ⊤) : (s.map f).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Subgroup.topologicalClosure_coe, Subgroup.coe_top, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image hf hs

/-- The topological closure of a normal subgroup is normal. -/
@[to_additive /-- The topological closure of a normal additive subgroup is normal. -/]
/-
**Subgroup.is_normal_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.is_normal_topologicalClosure {G : Type*} [TopologicalSpace G] [Gr
oup G] [IsTopologicalGroup G] (N : Subgroup G) [N.Normal] : (Subgroup.topologica
lClosure N).Normal where conj_mem n hn g
参数：N : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mem_closure`：map_mem_closure {t : Set Y} (hf : Continuous f) (hx : x
 in closure s) (ht : MapsTo f s t) : f x in closure t
· 使用定理 `IsTopologicalGroup.continuous_conj`：IsTopologicalGroup.continuous_conj [
SeparatelyContinuousMul G] (g : G) : Continuous fun h : G => g * h * g⁻¹
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H

--- 原说明 ---
The topological closure of a normal subgroup is normal.
-/
theorem Subgroup.is_normal_topologicalClosure {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (N : Subgroup G) [N.Normal] :
    (Subgroup.topologicalClosure N).Normal where
  conj_mem n hn g := by
    apply map_mem_closure (IsTopologicalGroup.continuous_conj g) hn
    exact fun m hm => Subgroup.Normal.conj_mem inferInstance m hm g

@[to_additive]
/-
**mul_mem_connectedComponent_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_mem_connectedComponent_one {G : Type*} [TopologicalSpace G] [MulOneCla
ss G] [ContinuousMul G] {g h : G} (hg : g in connectedComponent (1 : G)) (hh : h
 in connectedComponent (1 : G)) : g * h in connectedComponent (1 : G)
参数：hg : g in connectedComponent (1 : G)；hh : h in connectedComponent (1 : G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `connectedComponent_eq`：connectedComponent_eq {x y : α} (h : y in connect
edComponent x) : connectedComponent x = connectedComponent y
· 使用定理 `Continuous.image_connectedComponent_subset`：Continuous.image_connectedCo
mponent_subset [TopologicalSpace β] {f : α -> β} (h : Continuous f) (a : α) : f 
'' connectedComponent a subseteq…
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_mem_connectedComponent_one {G : Type*} [TopologicalSpace G] [MulOneClass G]
    [ContinuousMul G] {g h : G} (hg : g ∈ connectedComponent (1 : G))
    (hh : h ∈ connectedComponent (1 : G)) : g * h ∈ connectedComponent (1 : G) := by
  rw [connectedComponent_eq hg]
  have hmul : g ∈ connectedComponent (g * h) := by
    apply Continuous.image_connectedComponent_subset (continuous_const_mul g)
    rw [← connectedComponent_eq hh]
    exact ⟨(1 : G), mem_connectedComponent, by simp only [mul_one]⟩
  simpa [← connectedComponent_eq hmul] using mem_connectedComponent

@[to_additive]
/-
**inv_mem_connectedComponent_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mem_connectedComponent_one {G : Type*} [TopologicalSpace G] [DivisionM
onoid G] [ContinuousInv G] {g : G} (hg : g in connectedComponent (1 : G)) : g⁻¹ 
in connectedComponent (1 : G)
参数：hg : g in connectedComponent (1 : G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Continuous.image_connectedComponent_subset`：Continuous.image_connectedCo
mponent_subset [TopologicalSpace β] {f : α -> β} (h : Continuous f) (a : α) : f 
'' connectedComponent a subseteq…
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
-/
theorem inv_mem_connectedComponent_one {G : Type*} [TopologicalSpace G] [DivisionMonoid G]
    [ContinuousInv G] {g : G} (hg : g ∈ connectedComponent (1 : G)) :
    g⁻¹ ∈ connectedComponent (1 : G) := by
  rw [← inv_one]
  exact
    Continuous.image_connectedComponent_subset continuous_inv _
      ((Set.mem_image _ _ _).mp ⟨g, hg, rfl⟩)

/-- The connected component of 1 is a subgroup of `G`. -/
@[to_additive /-- The connected component of 0 is a subgroup of `G`. -/]
/-
**Subgroup.connectedComponentOfOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subgroup.connectedComponentOfOne (G : Type*) [TopologicalSpace G] [Group G
] [IsTopologicalGroup G] : Subgroup G where carrier
参数：G : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connected component of 1 is a subgroup of `G`.
-/
def Subgroup.connectedComponentOfOne (G : Type*) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] : Subgroup G where
  carrier := connectedComponent (1 : G)
  one_mem' := mem_connectedComponent
  mul_mem' hg hh := mul_mem_connectedComponent_one hg hh
  inv_mem' hg := inv_mem_connectedComponent_one hg

/-- If a subgroup of a topological group is commutative, then so is its topological closure.

See note [reducible non-instances]. -/
@[to_additive
  /-- If a subgroup of an additive topological group is commutative, then so is its
topological closure.

See note [reducible non-instances]. -/]
/-
**Subgroup.commGroupTopologicalClosure** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Subgroup.commGroupTopologicalClosure [T2Space G] (s : Subgroup G) (hs : fo
rall x y : s, x * y = y * x) : CommGroup s.topologicalClosure
参数：s : Subgroup G；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev Subgroup.commGroupTopologicalClosure [T2Space G] (s : Subgroup G)
    (hs : ∀ x y : s, x * y = y * x) : CommGroup s.topologicalClosure :=
  { s.topologicalClosure.toGroup, s.toSubmonoid.commMonoidTopologicalClosure hs with }

variable (G) in
@[to_additive]
/-
**Subgroup.coe_topologicalClosure_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.coe_topologicalClosure_bot : ((⊥ : Subgroup G).topologicalClosure
 : Set G) = _root_.closure ({1} : Set G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Subgroup.coe_topologicalClosure_bot :
    ((⊥ : Subgroup G).topologicalClosure : Set G) = _root_.closure ({1} : Set G) := by simp

@[to_additive exists_nhds_half_neg]
/-
**exists_nhds_split_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_nhds_split_inv {s : Set G} (hs : s in 𝓝 (1 : G)) : exists V in 𝓝 (1
 : G), forall v in V, forall w in V, v / w in s
参数：hs : s in 𝓝 (1 : G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.mul`：ContinuousAt.mul (hf : ContinuousAt f x) (hg : Continu
ousAt g x) : ContinuousAt (f * g) x
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `continuousAt_fst`：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p
· 使用定理 `ContinuousAt.inv`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Inv G]   [ContinuousInv G] {f : X 
→ G} {…
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `continuousAt_snd`：continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
-/
theorem exists_nhds_split_inv {s : Set G} (hs : s ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), ∀ v ∈ V, ∀ w ∈ V, v / w ∈ s := by
  have : (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' s ∈ 𝓝 ((1, 1) : G × G) :=
    continuousAt_fst.mul continuousAt_snd.inv (by simpa)
  simpa only [div_eq_mul_inv, nhds_prod_eq, mem_prod_self_iff, prod_subset_iff, mem_preimage] using
    this

@[to_additive]
/-
**nhds_translation_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_translation_mul_inv (x : G) : comap (· * x⁻¹) (𝓝 1) = 𝓝 x
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Homeomorph.comap_nhds_eq`：comap_nhds_eq (h : X ≃ₜ Y) (y : Y) : comap h (
𝓝 y) = 𝓝 (h.symm y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhds_translation_mul_inv (x : G) : comap (· * x⁻¹) (𝓝 1) = 𝓝 x :=
  ((Homeomorph.mulRight x⁻¹).comap_nhds_eq 1).trans <| show 𝓝 (1 * x⁻¹⁻¹) = 𝓝 x by simp

@[to_additive]
/-
**nhds_translation_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_translation_inv_mul (x : G) : comap (x⁻¹ * ·) (𝓝 1) = 𝓝 x
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Homeomorph.comap_nhds_eq`：comap_nhds_eq (h : X ≃ₜ Y) (y : Y) : comap h (
𝓝 y) = 𝓝 (h.symm y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhds_translation_inv_mul (x : G) : comap (x⁻¹ * ·) (𝓝 1) = 𝓝 x :=
  ((Homeomorph.mulLeft x⁻¹).comap_nhds_eq 1).trans <| show 𝓝 (x⁻¹⁻¹ * 1) = 𝓝 x by simp

@[to_additive (attr := simp)]
/-
**map_mul_left_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mul_left_nhds (x y : G) : map (x * ·) (𝓝 y) = 𝓝 (x * y)
参数：x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
-/
theorem map_mul_left_nhds (x y : G) : map (x * ·) (𝓝 y) = 𝓝 (x * y) :=
  (Homeomorph.mulLeft x).map_nhds_eq y

@[to_additive]
/-
**map_mul_left_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mul_left_nhds_one (x : G) : map (x * ·) (𝓝 1) = 𝓝 x
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul_left_nhds`：map_mul_left_nhds (x y : G) : map (x * ·) (𝓝 y) = 𝓝 (
x * y)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_mul_left_nhds_one (x : G) : map (x * ·) (𝓝 1) = 𝓝 x := by simp

@[to_additive (attr := simp)]
/-
**map_mul_right_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mul_right_nhds (x y : G) : map (· * x) (𝓝 y) = 𝓝 (y * x)
参数：x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
-/
theorem map_mul_right_nhds (x y : G) : map (· * x) (𝓝 y) = 𝓝 (y * x) :=
  (Homeomorph.mulRight x).map_nhds_eq y

@[to_additive]
/-
**map_mul_right_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mul_right_nhds_one (x : G) : map (· * x) (𝓝 1) = 𝓝 x
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul_right_nhds`：map_mul_right_nhds (x y : G) : map (· * x) (𝓝 y) = 𝓝
 (y * x)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_mul_right_nhds_one (x : G) : map (· * x) (𝓝 1) = 𝓝 x := by simp

@[to_additive]
/-
**Filter.HasBasis.nhds_of_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.nhds_of_one {ι : Sort*} {p : ι -> Prop} {s : ι -> Set G} (
hb : HasBasis (𝓝 1 : Filter G) p s) (x : G) : HasBasis (𝓝 x) p fun i => { y | y 
/ x in s i }
参数：hb : HasBasis (𝓝 1 : Filter G) p s；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_translation_mul_inv`：nhds_translation_mul_inv (x : G) : comap (· * 
x⁻¹) (𝓝 1) = 𝓝 x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
-/
theorem Filter.HasBasis.nhds_of_one {ι : Sort*} {p : ι → Prop} {s : ι → Set G}
    (hb : HasBasis (𝓝 1 : Filter G) p s) (x : G) :
    HasBasis (𝓝 x) p fun i => { y | y / x ∈ s i } := by
  rw [← nhds_translation_mul_inv]
  simp_rw [div_eq_mul_inv]
  exact hb.comap _

@[to_additive]
/-
**mem_closure_iff_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_iff_nhds_one {x : G} {s : Set G} : x in closure s ↔ forall U i
n (𝓝 1 : Filter G), exists y in s, y / x in U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_nhds_basis`：mem_closure_iff_nhds_basis {p : ι -> Prop} {
s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : x in closure t ↔ forall i, p i -> exi
sts y in t, y in…
· 使用定理 `Filter.HasBasis.nhds_of_one`：Filter.HasBasis.nhds_of_one {ι : Sort*} {p 
: ι -> Prop} {s : ι -> Set G} (hb : HasBasis (𝓝 1 : Filter G) p s) (x : G) : Has
Basis (𝓝 x) p fun…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_closure_iff_nhds_one {x : G} {s : Set G} :
    x ∈ closure s ↔ ∀ U ∈ (𝓝 1 : Filter G), ∃ y ∈ s, y / x ∈ U := by
  rw [mem_closure_iff_nhds_basis ((𝓝 1 : Filter G).basis_sets.nhds_of_one x)]
  simp_rw [Set.mem_ofPred, id]

/-- A monoid homomorphism (a bundled morphism of a type that implements `MonoidHomClass`)
from a topological group to a topological monoid is continuous
provided that it is continuous at one.

This version assumes that `f x → 1` as `x → 1`,
saving a rewrite of `f 1 = 1` compared to `continuous_of_continuousAt_one` in some cases.
See also `uniformContinuous_of_continuousAt_one`. -/
@[to_additive
  /-- An additive monoid homomorphism (a bundled morphism of a type that implements
  `AddMonoidHomClass`) from an additive topological group to an additive topological monoid is
  continuous provided that it is continuous at zero.

  This version assumes that `f x → 0` as `x → 0`,
  saving a rewrite of `f 0 = 0` compared to `continuous_of_continuousAt_zero` in some cases.
  See also `uniformContinuous_of_continuousAt_zero`. -/]
/-
**continuous_of_tendsto_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_of_tendsto_nhds_one {M hom : Type*} [MulOneClass M] [Topologica
lSpace M] [ContinuousMul M] [FunLike hom G M] [MonoidHomClass hom G M] (f : hom)
 (hf : Tendsto f (𝓝 1) (𝓝 1)) : Continuous f
参数：f : hom；hf : Tendsto f (𝓝 1) (𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul_left_nhds_one`：map_mul_left_nhds_one (x : G) : map (x * ·) (𝓝 1)
 = 𝓝 x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
-/
theorem continuous_of_tendsto_nhds_one {M hom : Type*} [MulOneClass M] [TopologicalSpace M]
    [ContinuousMul M] [FunLike hom G M] [MonoidHomClass hom G M] (f : hom)
    (hf : Tendsto f (𝓝 1) (𝓝 1)) :
    Continuous f :=
  continuous_iff_continuousAt.2 fun x ↦ by
    simpa only [ContinuousAt, ← map_mul_left_nhds_one x, tendsto_map'_iff, Function.comp_def,
      map_mul, mul_one] using hf.const_mul (f x)

/-- A monoid homomorphism (a bundled morphism of a type that implements `MonoidHomClass`) from a
topological group to a topological monoid is continuous provided that it is continuous at one. See
also `uniformContinuous_of_continuousAt_one`. -/
@[to_additive
  /-- An additive monoid homomorphism (a bundled morphism of a type that implements
  `AddMonoidHomClass`) from an additive topological group to an additive topological monoid is
  continuous provided that it is continuous at zero. See also
  `uniformContinuous_of_continuousAt_zero`. -/]
/-
**continuous_of_continuousAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_of_continuousAt_one {M hom : Type*} [MulOneClass M] [Topologica
lSpace M] [ContinuousMul M] [FunLike hom G M] [MonoidHomClass hom G M] (f : hom)
 (hf : ContinuousAt f 1) : Continuous f
参数：f : hom；hf : ContinuousAt f 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_tendsto_nhds_one`：continuous_of_tendsto_nhds_one {M hom : 
Type*} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] [FunLike hom G M] 
[MonoidHomClass hom …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
-/
theorem continuous_of_continuousAt_one {M hom : Type*} [MulOneClass M] [TopologicalSpace M]
    [ContinuousMul M] [FunLike hom G M] [MonoidHomClass hom G M] (f : hom)
    (hf : ContinuousAt f 1) :
    Continuous f :=
  continuous_of_tendsto_nhds_one f <| by simpa using hf.tendsto

@[to_additive continuous_of_continuousAt_zero₂]
/-
**continuous_of_continuousAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_of_continuousAt_one {M hom : Type*} [MulOneClass M] [Topologica
lSpace M] [ContinuousMul M] [FunLike hom G M] [MonoidHomClass hom G M] (f : hom)
 (hf : ContinuousAt f 1) : Continuous f
参数：f : hom；hf : ContinuousAt f 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_tendsto_nhds_one`：continuous_of_tendsto_nhds_one {M hom : 
Type*} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] [FunLike hom G M] 
[MonoidHomClass hom …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
-/
theorem continuous_of_continuousAt_one₂ {H M : Type*} [CommMonoid M] [TopologicalSpace M]
    [ContinuousMul M] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (f : G →* H →* M)
    (hf : ContinuousAt (fun x : G × H ↦ f x.1 x.2) (1, 1))
    (hl : ∀ x, ContinuousAt (f x) 1) (hr : ∀ y, ContinuousAt (f · y) 1) :
    Continuous (fun x : G × H ↦ f x.1 x.2) := continuous_iff_continuousAt.2 fun (x, y) => by
  simp only [ContinuousAt, nhds_prod_eq, ← map_mul_left_nhds_one x, ← map_mul_left_nhds_one y,
    prod_map_map_eq, tendsto_map'_iff, Function.comp_def, map_mul, MonoidHom.mul_apply] at *
  refine ((tendsto_const_nhds.mul ((hr y).comp tendsto_fst)).mul
    (((hl x).comp tendsto_snd).mul hf)).mono_right (le_of_eq ?_)
  simp only [map_one, mul_one, MonoidHom.one_apply]

@[to_additive]
/-
**IsTopologicalGroup.isInducing_iff_nhds_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.isInducing_iff_nhds_one {H : Type*} [Group H] [Topologi
calSpace H] [IsTopologicalGroup H] {F : Type*} [FunLike F G H] [MonoidHomClass F
 G H] {f : F} : Topology.IsInducing f ↔ 𝓝 (1 : G) = (𝓝 (1 : H)).comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.isInducing_iff_nhds`：isInducing_iff_nhds : IsInducing f ↔ foral
l x, 𝓝 x = comap f (𝓝 (f x))
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_translation_mul_inv`：nhds_translation_mul_inv (x : G) : comap (· * 
x⁻¹) (𝓝 1) = 𝓝 x
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsTopologicalGroup.isInducing_iff_nhds_one
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {F : Type*}
    [FunLike F G H] [MonoidHomClass F G H] {f : F} :
    Topology.IsInducing f ↔ 𝓝 (1 : G) = (𝓝 (1 : H)).comap f := by
  rw [Topology.isInducing_iff_nhds]
  refine ⟨(map_one f ▸ · 1), fun hf x ↦ ?_⟩
  rw [← nhds_translation_mul_inv, ← nhds_translation_mul_inv (f x), Filter.comap_comap, hf,
    Filter.comap_comap]
  congr 1
  ext; simp

@[to_additive]
/-
**IsTopologicalGroup.isOpenMap_iff_nhds_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.isOpenMap_iff_nhds_one {H : Type*} [Monoid H] [Topologi
calSpace H] [ContinuousConstSMul H H] {F : Type*} [FunLike F G H] [MonoidHomClas
s F G H] {f : F} : IsOpenMap f ↔ 𝓝 1 <= .map f (𝓝 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ (x : X), nhd
s (f x)…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `IsOpenMap.of_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y],   (∀ (x : X), nhds (f x) ≤ 
Filter.map…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Homeomorph.smul_apply`：∀ {α : Type u_2} {G : Type u_4} [inst : Topologic
alSpace α] [inst_1 : Group G] [inst_2 : MulAction G α]   [inst_3 : ContinuousCon
stSMul G α]…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `val_toUnits_apply`：∀ {G : Type u_5} [inst : Group G] (x : G), ↑(toUnits 
x) = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul_left_nhds_one`：map_mul_left_nhds_one (x : G) : map (x * ·) (𝓝 1)
 = 𝓝 x
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
lemma IsTopologicalGroup.isOpenMap_iff_nhds_one
    {H : Type*} [Monoid H] [TopologicalSpace H] [ContinuousConstSMul H H]
    {F : Type*} [FunLike F G H] [MonoidHomClass F G H] {f : F} :
    IsOpenMap f ↔ 𝓝 1 ≤ .map f (𝓝 1) := by
  refine ⟨fun H ↦ map_one f ▸ H.nhds_le 1, fun h ↦ IsOpenMap.of_nhds_le fun x ↦ ?_⟩
  have : Filter.map (f x * ·) (𝓝 1) = 𝓝 (f x) := by
    simpa [-Homeomorph.map_nhds_eq, Units.smul_def] using!
      (Homeomorph.smul ((toUnits x).map (MonoidHomClass.toMonoidHom f))).map_nhds_eq (1 : H)
  rw [← map_mul_left_nhds_one x, Filter.map_map, Function.comp_def, ← this]
  refine (Filter.map_mono h).trans ?_
  simp [Function.comp_def]

-- TODO: unify with `QuotientGroup.isOpenQuotientMap_mk`
/-- Let `A` and `B` be topological groups, and let `φ : A → B` be a continuous surjective group
homomorphism. Assume furthermore that `φ` is a quotient map (i.e., `V ⊆ B`
is open iff `φ⁻¹ V` is open). Then `φ` is an open quotient map, and in particular an open map. -/
@[to_additive /-- Let `A` and `B` be topological additive groups, and let `φ : A → B` be a
continuous surjective additive group homomorphism. Assume furthermore that `φ` is a quotient map
(i.e., `V ⊆ B` is open iff `φ⁻¹ V` is open). Then `φ` is an open quotient map, and in particular an
open map. -/]
/-
**MonoidHom.isOpenQuotientMap_of_isQuotientMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.isOpenQuotientMap_of_isQuotientMap {A : Type*} [Group A] [Topolo
gicalSpace A] [ContinuousMul A] {B : Type*} [Group B] [TopologicalSpace B] {F : 
Type*} [FunLike F A B] [MonoidHomClass F A B] {φ : F} (hφ : IsQuotientMap φ) : I
sOpenQuotientMap φ where surjective
参数：hφ : IsQuotientMap φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
· 使用定理 `Topology.IsQuotientMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : 
X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsQ
uotientMap f → Continuo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.isOpen_preimage`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsCoinducing f → ∀ {s : Se…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `Continuous.mul_const`：Continuous.mul_const (hf : Continuous f) (b : M) :
 Continuous (f · * b)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
-/
lemma MonoidHom.isOpenQuotientMap_of_isQuotientMap {A : Type*} [Group A]
    [TopologicalSpace A] [ContinuousMul A] {B : Type*} [Group B] [TopologicalSpace B]
    {F : Type*} [FunLike F A B] [MonoidHomClass F A B] {φ : F}
    (hφ : IsQuotientMap φ) : IsOpenQuotientMap φ where
    surjective := hφ.surjective
    continuous := hφ.continuous
    isOpenMap := by
      -- We need to check that if `U ⊆ A` is open then `φ⁻¹ (φ U)` is open.
      intro U hU
      rw [← hφ.isOpen_preimage]
      -- It suffices to show that `φ⁻¹ (φ U) = ⋃ (U * k⁻¹)` as `k` runs through the kernel of `φ`,
      -- as `U * k⁻¹` is open because `x ↦ x * k` is continuous.
      -- Remark: here is where we use that we have groups not monoids (you cannot avoid
      -- using both `k` and `k⁻¹` at this point).
      suffices ⇑φ ⁻¹' ⇑φ '' U = ⋃ k ∈ ker (φ : A →* B), (fun x ↦ x * k) ⁻¹' U by
        exact this ▸ isOpen_biUnion (fun k _ ↦ Continuous.isOpen_preimage (by fun_prop) _ hU)
      ext x
      -- But this is an elementary calculation.
      constructor
      · rintro ⟨y, hyU, hyx⟩
        apply Set.mem_iUnion_of_mem (x⁻¹ * y)
        simp_all
      · rintro ⟨_, ⟨k, rfl⟩, _, ⟨(hk : φ k = 1), rfl⟩, hx⟩
        use x * k, hx
        rw [map_mul, hk, mul_one]

@[to_additive]
/-
**MonoidHom.isOpenQuotientMap_iff_isQuotientMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.isOpenQuotientMap_iff_isQuotientMap {A : Type*} [Group A] [Topol
ogicalSpace A] [ContinuousMul A] {B : Type*} [Group B] [TopologicalSpace B] {F :
 Type*} [FunLike F A B] [MonoidHomClass F A B] {φ : F} : IsOpenQuotientMap φ ↔ I
sQuotientMap φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenQuotientMap.isQuotientMap`：isQuotientMap (h : IsOpenQuotientMap f)
 : IsQuotientMap f
· 使用引理 `MonoidHom.isOpenQuotientMap_of_isQuotientMap`：MonoidHom.isOpenQuotientMa
p_of_isQuotientMap {A : Type*} [Group A] [TopologicalSpace A] [ContinuousMul A] 
{B : Type*} [Group B] [Topological…
-/
lemma MonoidHom.isOpenQuotientMap_iff_isQuotientMap {A : Type*} [Group A]
    [TopologicalSpace A] [ContinuousMul A] {B : Type*} [Group B] [TopologicalSpace B]
    {F : Type*} [FunLike F A B] [MonoidHomClass F A B] {φ : F} :
    IsOpenQuotientMap φ ↔ IsQuotientMap φ :=
  ⟨fun hf => hf.isQuotientMap, MonoidHom.isOpenQuotientMap_of_isQuotientMap⟩

@[to_additive]
/-
**IsTopologicalGroup.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.ext {G : Type*} [Group G] {t t' : TopologicalSpace G} (
tg : @IsTopologicalGroup G t _) (tg' : @IsTopologicalGroup G t' _) (h : @nhds G 
t 1 = @nhds G t' 1) : t = t'
参数：tg : @IsTopologicalGroup G t _；tg' : @IsTopologicalGroup G t' _；h : @nhds G t
 1 = @nhds G t' 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext_nhds`：∀ {X : Type u_2} {t t' : TopologicalSpace X},
 (∀ (x : X), nhds x = nhds x) → t = t'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_translation_mul_inv`：nhds_translation_mul_inv (x : G) : comap (· * 
x⁻¹) (𝓝 1) = 𝓝 x
-/
theorem IsTopologicalGroup.ext {G : Type*} [Group G] {t t' : TopologicalSpace G}
    (tg : @IsTopologicalGroup G t _) (tg' : @IsTopologicalGroup G t' _)
    (h : @nhds G t 1 = @nhds G t' 1) : t = t' :=
  TopologicalSpace.ext_nhds fun x ↦ by
    rw [← @nhds_translation_mul_inv G t _ _ x, ← @nhds_translation_mul_inv G t' _ _ x, ← h]

@[to_additive]
/-
**IsTopologicalGroup.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.ext_iff {G : Type*} [Group G] {t t' : TopologicalSpace 
G} (tg : @IsTopologicalGroup G t _) (tg' : @IsTopologicalGroup G t' _) : t = t' 
↔ @nhds G t 1 = @nhds G t' 1
参数：tg : @IsTopologicalGroup G t _；tg' : @IsTopologicalGroup G t' _。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalGroup.ext`：IsTopologicalGroup.ext {G : Type*} [Group G] {t 
t' : TopologicalSpace G} (tg : @IsTopologicalGroup G t _) (tg' : @IsTopologicalG
roup G t' _)…
-/
theorem IsTopologicalGroup.ext_iff {G : Type*} [Group G] {t t' : TopologicalSpace G}
    (tg : @IsTopologicalGroup G t _) (tg' : @IsTopologicalGroup G t' _) :
    t = t' ↔ @nhds G t 1 = @nhds G t' 1 :=
  ⟨fun h => h ▸ rfl, tg.ext tg'⟩

@[to_additive]
/-
**ContinuousInv.of_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousInv.of_nhds_one {G : Type*} [Group G] [TopologicalSpace G] (hinv
 : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1)) (hleft : forall x₀ : G, 𝓝 x₀ = map (f
un x : G => x₀ * x) (𝓝 1)) (hconj : forall x₀ : G, Tendsto (fun x : G => x₀ * x 
* x₀⁻¹) (𝓝 1) (𝓝 1)) : ContinuousInv G
参数：hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1)；hleft : forall x₀ : G, 𝓝 x₀ = m
ap (fun x : G => x₀ * x) (𝓝 1)；hconj : forall x₀ : G, Tendsto (fun x : G => x₀ *
 x * x₀⁻¹) (𝓝 1) (𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
theorem ContinuousInv.of_nhds_one {G : Type*} [Group G] [TopologicalSpace G]
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x : G => x₀ * x) (𝓝 1))
    (hconj : ∀ x₀ : G, Tendsto (fun x : G => x₀ * x * x₀⁻¹) (𝓝 1) (𝓝 1)) : ContinuousInv G := by
  refine ⟨continuous_iff_continuousAt.2 fun x₀ => ?_⟩
  have : Tendsto (fun x => x₀⁻¹ * (x₀ * x⁻¹ * x₀⁻¹)) (𝓝 1) (map (x₀⁻¹ * ·) (𝓝 1)) :=
    (tendsto_map.comp <| hconj x₀).comp hinv
  simpa only [ContinuousAt, hleft x₀, hleft x₀⁻¹, tendsto_map'_iff, Function.comp_def, mul_assoc,
    mul_inv_rev, inv_mul_cancel_left] using this

@[to_additive]
/-
**IsTopologicalGroup.of_nhds_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.of_nhds_one' {G : Type u} [Group G] [TopologicalSpace G
] (hmul : Tendsto (uncurry ((· * ·) : G -> G -> G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1)) (hinv : 
Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1)) (hleft : forall x₀ : G, 𝓝 x₀ = map (fun 
x => x₀ * x) (𝓝 1)) (hright : forall x₀ : G, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1))
 : IsTopologicalGroup G
参数：hmul : Tendsto (uncurry ((· * ·) : G -> G -> G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1)；hinv : Te
ndsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1)；hleft : forall x₀ : G, 𝓝 x₀ = map (fun x =>
 x₀ * x) (𝓝 1)；hright : forall x₀ : G, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMul.of_nhds_one`：ContinuousMul.of_nhds_one {M : Type u} [Monoi
d M] [TopologicalSpace M] (hmul : Tendsto (uncurry ((· * ·) : M -> M -> M)) (𝓝 1
 ×ˢ 𝓝 1) <| 𝓝 1…
· 使用定理 `ContinuousInv.of_nhds_one`：ContinuousInv.of_nhds_one {G : Type*} [Group 
G] [TopologicalSpace G] (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1)) (hleft :
 forall x₀ : G,…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `comp_mul_right`：comp_mul_right (x y : α) : (· * x) ∘ (· * y) = (· * (y *
 x))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Filter.map_id'`：map_id' : Filter.map (fun x => x) f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsTopologicalGroup.of_nhds_one' {G : Type u} [Group G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hright : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)) : IsTopologicalGroup G :=
  { toContinuousMul := ContinuousMul.of_nhds_one hmul hleft hright
    toContinuousInv :=
      ContinuousInv.of_nhds_one hinv hleft fun x₀ =>
        le_of_eq
          (by
            rw [show (fun x => x₀ * x * x₀⁻¹) = (fun x => x * x₀⁻¹) ∘ fun x => x₀ * x from rfl, ←
              map_map, ← hleft, hright, map_map]
            simp) }

@[to_additive]
/-
**IsTopologicalGroup.of_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.of_nhds_one {G : Type u} [Group G] [TopologicalSpace G]
 (hmul : Tendsto (uncurry ((· * ·) : G -> G -> G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1)) (hinv : T
endsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1)) (hleft : forall x₀ : G, 𝓝 x₀ = map (x₀ * 
·) (𝓝 1)) (hconj : forall x₀ : G, Tendsto (x₀ * · * x₀⁻¹) (𝓝 1) (𝓝 1)) : IsTopol
ogicalGroup G
参数：hmul : Tendsto (uncurry ((· * ·) : G -> G -> G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1)；hinv : Te
ndsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1)；hleft : forall x₀ : G, 𝓝 x₀ = map (x₀ * ·) 
(𝓝 1)；hconj : forall x₀ : G, Tendsto (x₀ * · * x₀⁻¹) (𝓝 1) (𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalGroup.of_nhds_one'`：IsTopologicalGroup.of_nhds_one' {G : Ty
pe u} [Group G] [TopologicalSpace G] (hmul : Tendsto (uncurry ((· * ·) : G -> G 
-> G)) (𝓝 1 ×ˢ 𝓝 1) (…
· 使用定理 `Filter.map_eq_of_inverse`：map_eq_of_inverse {f : Filter α} {g : Filter β
} {φ : α -> β} (ψ : β -> α) (eq : φ ∘ ψ = id) (hφ : Tendsto φ f g) (hψ : Tendsto
 ψ g f) : map …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
theorem IsTopologicalGroup.of_nhds_one {G : Type u} [Group G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (x₀ * ·) (𝓝 1))
    (hconj : ∀ x₀ : G, Tendsto (x₀ * · * x₀⁻¹) (𝓝 1) (𝓝 1)) : IsTopologicalGroup G := by
  refine IsTopologicalGroup.of_nhds_one' hmul hinv hleft fun x₀ => ?_
  replace hconj : ∀ x₀ : G, map (x₀ * · * x₀⁻¹) (𝓝 1) = 𝓝 1 :=
    fun x₀ => map_eq_of_inverse (x₀⁻¹ * · * x₀⁻¹⁻¹) (by ext; simp [mul_assoc]) (hconj _) (hconj _)
  rw [← hconj x₀]
  simpa [Function.comp_def] using hleft _

@[to_additive]
/-
**IsTopologicalGroup.of_comm_of_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.of_comm_of_nhds_one {G : Type u} [CommGroup G] [Topolog
icalSpace G] (hmul : Tendsto (uncurry ((· * ·) : G -> G -> G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1
)) (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1)) (hleft : forall x₀ : G, 𝓝 x₀ 
= map (x₀ * ·) (𝓝 1)) : IsTopologicalGroup G
参数：hmul : Tendsto (uncurry ((· * ·) : G -> G -> G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1)；hinv : Te
ndsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1)；hleft : forall x₀ : G, 𝓝 x₀ = map (x₀ * ·) 
(𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalGroup.of_nhds_one`：IsTopologicalGroup.of_nhds_one {G : Type
 u} [Group G] [TopologicalSpace G] (hmul : Tendsto (uncurry ((· * ·) : G -> G ->
 G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `mul_inv_cancel_comm`：mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem IsTopologicalGroup.of_comm_of_nhds_one {G : Type u} [CommGroup G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (x₀ * ·) (𝓝 1)) : IsTopologicalGroup G :=
  IsTopologicalGroup.of_nhds_one hmul hinv hleft (by simpa using! tendsto_id)

variable (G) in
/-- Any first countable topological group has an antitone neighborhood basis `u : ℕ → Set G` for
which `(u (n + 1)) ^ 2 ⊆ u n`. The existence of such a neighborhood basis is a key tool for
`QuotientGroup.completeSpace_right`. -/
@[to_additive
  /-- Any first countable topological additive group has an antitone neighborhood basis
  `u : ℕ → set G` for which `u (n + 1) + u (n + 1) ⊆ u n`.
  The existence of such a neighborhood basis is a key tool
  for `QuotientAddGroup.completeSpace_right`. -/]
/-
**IsTopologicalGroup.exists_antitone_basis_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：IsTopologicalGroup.exists_antitone_basis_nhds_one [FirstCountableTopology 
G] : exists u : Nat -> Set G, (𝓝 1).HasAntitoneBasis u ∧ forall n, u (n + 1) * u
 (n + 1) subseteq u n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_antitone_basis`：exists_antitone_basis (f : Filter α) [f.Is
CountablyGenerated] : exists x : Nat -> Set α, f.HasAntitoneBasis x
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.HasBasis.prod_nhds`：Filter.HasBasis.prod_nhds {ιX ιY : Type*} {px
 : ιX -> Prop} {py : ιY -> Prop} {sx : ιX -> Set X} {sy : ιY -> Set Y} {x : X} {
y : Y} (hx : (𝓝…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Filter.HasAntitoneBasis.subbasis_with_rel`：∀ {α : Type u_3} {f : Filter 
α} {s : ℕ → Set α},   f.HasAntitoneBasis s →     ∀ {r : ℕ → ℕ → Prop},       (∀ 
(m : ℕ), ∀ᶠ (n : ℕ) in Filter.a…
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem IsTopologicalGroup.exists_antitone_basis_nhds_one [FirstCountableTopology G] :
    ∃ u : ℕ → Set G, (𝓝 1).HasAntitoneBasis u ∧ ∀ n, u (n + 1) * u (n + 1) ⊆ u n := by
  rcases (𝓝 (1 : G)).exists_antitone_basis with ⟨u, hu, u_anti⟩
  have :=
    ((hu.prod_nhds hu).tendsto_iff hu).mp
      (by simpa only [mul_one] using continuous_mul.tendsto ((1, 1) : G × G))
  simp only [and_self_iff, mem_prod, and_imp, Prod.forall, Prod.exists,
    forall_true_left] at this
  have event_mul : ∀ n : ℕ, ∀ᶠ m in atTop, u m * u m ⊆ u n := by
    intro n
    rcases this n with ⟨j, k, -, h⟩
    refine atTop_basis.eventually_iff.mpr ⟨max j k, True.intro, fun m hm => ?_⟩
    rintro - ⟨a, ha, b, hb, rfl⟩
    exact h a b (u_anti ((le_max_left _ _).trans hm) ha) (u_anti ((le_max_right _ _).trans hm) hb)
  obtain ⟨φ, -, hφ, φ_anti_basis⟩ := HasAntitoneBasis.subbasis_with_rel ⟨hu, u_anti⟩ event_mul
  exact ⟨u ∘ φ, φ_anti_basis, fun n => hφ n.lt_succ_self⟩

end IsTopologicalGroup

section ContinuousDiv

variable [TopologicalSpace G] [Div G] [ContinuousDiv G]

@[to_additive sub_const]
/-
**Filter.Tendsto.div_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.div_const' {c : G} {f : α -> G} {l : Filter α} (h : Tendsto
 f l (𝓝 c)) (b : G) : Tendsto (f · / b) l (𝓝 (c / b))
参数：h : Tendsto f l (𝓝 c)；b : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.div'`：Filter.Tendsto.div' {f g : α -> G} {l : Filter α} {
a b : G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f
 x / g x)…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem Filter.Tendsto.div_const' {c : G} {f : α → G} {l : Filter α} (h : Tendsto f l (𝓝 c))
    (b : G) : Tendsto (f · / b) l (𝓝 (c / b)) :=
  h.div' tendsto_const_nhds
/-
**Filter.tendsto_div_const_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.tendsto_div_const_iff {G : Type*} [GroupWithZero G] [TopologicalSpa
ce G] [ContinuousDiv G] {b : G} (hb : b != 0) {c : G} {f : α -> G} {l : Filter α
} : Tendsto (f · / b) l (𝓝 (c / b)) ↔ Tendsto f l (𝓝 c)
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_eq_div_div_swap`：div_mul_eq_div_div_swap : a / (b * c) = a / c /
 b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Filter.Tendsto.div_const'`：Filter.Tendsto.div_const' {c : G} {f : α -> G
} {l : Filter α} (h : Tendsto f l (𝓝 c)) (b : G) : Tendsto (f · / b) l (𝓝 (c / b
))
-/
lemma Filter.tendsto_div_const_iff {G : Type*}
    [GroupWithZero G] [TopologicalSpace G] [ContinuousDiv G]
    {b : G} (hb : b ≠ 0) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (f · / b) l (𝓝 (c / b)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ Filter.Tendsto.div_const' h b⟩
  convert! h.div_const' b⁻¹ with k <;> rw [← div_mul_eq_div_div_swap, inv_mul_cancel₀ hb, div_one]

@[to_additive tendsto_sub_const_iff]
/-
**Filter.tendsto_div_const_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.tendsto_div_const_iff' {G : Type*} [TopologicalSpace G] [Group G] [
ContinuousDiv G] (b : G) {c : G} {f : α -> G} {l : Filter α} : Tendsto (f · / b)
 l (𝓝 (c / b)) ↔ Tendsto f l (𝓝 c)
参数：b : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_eq_div_div_swap`：div_mul_eq_div_div_swap : a / (b * c) = a / c /
 b
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Filter.Tendsto.div_const'`：Filter.Tendsto.div_const' {c : G} {f : α -> G
} {l : Filter α} (h : Tendsto f l (𝓝 c)) (b : G) : Tendsto (f · / b) l (𝓝 (c / b
))
-/
lemma Filter.tendsto_div_const_iff' {G : Type*}
    [TopologicalSpace G] [Group G] [ContinuousDiv G]
    (b : G) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (f · / b) l (𝓝 (c / b)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ Filter.Tendsto.div_const' h b⟩
  convert! h.div_const' b⁻¹ with k <;> rw [← div_mul_eq_div_div_swap, inv_mul_cancel, div_one]

@[to_additive const_sub]
/-
**Filter.Tendsto.const_div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.const_div' (b : G) {c : G} {f : α -> G} {l : Filter α} (h :
 Tendsto f l (𝓝 c)) : Tendsto (b / f ·) l (𝓝 (b / c))
参数：b : G；h : Tendsto f l (𝓝 c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.div'`：Filter.Tendsto.div' {f g : α -> G} {l : Filter α} {
a b : G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f
 x / g x)…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem Filter.Tendsto.const_div' (b : G) {c : G} {f : α → G} {l : Filter α}
    (h : Tendsto f l (𝓝 c)) : Tendsto (b / f ·) l (𝓝 (b / c)) :=
  tendsto_const_nhds.div' h

@[to_additive (attr := continuity) continuous_sub_left]
/-
**continuous_div_left'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_div_left' (a : G) : Continuous (a / ·)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.fun_div'`：∀ {G : Type u_1} {X : Type u_3} [inst : Topological
Space X] [inst_1 : TopologicalSpace G] [inst_2 : Div G]   [ContinuousDiv G] {f g
 : X → G}…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
-/
lemma continuous_div_left' (a : G) : Continuous (a / ·) := by fun_prop

@[to_additive (attr := continuity) continuous_sub_right]
/-
**continuous_div_right'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_div_right' (a : G) : Continuous (· / a)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.fun_div'`：∀ {G : Type u_1} {X : Type u_3} [inst : Topological
Space X] [inst_1 : TopologicalSpace G] [inst_2 : Div G]   [ContinuousDiv G] {f g
 : X → G}…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
lemma continuous_div_right' (a : G) : Continuous (· / a) := by fun_prop

end ContinuousDiv

section DivInvTopologicalGroup

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive tendsto_const_sub_iff]
/-
**Filter.tendsto_const_div_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.tendsto_const_div_iff' (b : G) {c : G} {f : α -> G} {l : Filter α} 
: Tendsto (fun k : α => b / f k) l (𝓝 (b / c)) ↔ Tendsto f l (𝓝 c)
参数：b : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `Filter.Tendsto.mul_const`：Filter.Tendsto.mul_const {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) 
x (𝓝 (a * b))
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Filter.Tendsto.inv`：Filter.Tendsto.inv {f : α -> G} {l : Filter α} {y : 
G} (h : Tendsto f l (𝓝 y)) : Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹)
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `Filter.Tendsto.const_div'`：Filter.Tendsto.const_div' (b : G) {c : G} {f 
: α -> G} {l : Filter α} (h : Tendsto f l (𝓝 c)) : Tendsto (b / f ·) l (𝓝 (b / c
))
· 使用定理 `IsTopologicalGroup.to_continuousDiv`：∀ {G : Type u} [inst : TopologicalS
pace G] [inst_1 : Group G] [IsTopologicalGroup G], ContinuousDiv G
-/
lemma Filter.tendsto_const_div_iff' (b : G) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (fun k : α ↦ b / f k) l (𝓝 (b / c)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h ↦ ?_, Filter.Tendsto.const_div' b⟩
  convert! h.inv.mul_const b with k <;> rw [inv_div, div_mul_cancel]

@[deprecated (since := "2026-02-03")]
alias Filter.tendsto_const_div_iff := Filter.tendsto_const_div_iff'

/-- A version of `Homeomorph.mulLeft a b⁻¹` that is defeq to `a / b`. -/
@[to_additive (attr := simps! +simpRhs)
  /-- A version of `Homeomorph.addLeft a (-b)` that is defeq to `a - b`. -/]
/-
**Homeomorph.divLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Homeomorph.divLeft (x : G) : G ≃ₜ G
参数：x : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Homeomorph.divLeft (x : G) : G ≃ₜ G :=
  { Equiv.divLeft x with }

@[to_additive (attr := simp)]
/-
**Homeomorph.coe_divLeft** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.coe_divLeft (a : G) : ⇑(Homeomorph.divLeft a) = (a / ·)
参数：a : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Homeomorph.coe_divLeft (a : G) : ⇑(Homeomorph.divLeft a) = (a / ·) :=
  rfl

@[to_additive]
/-
**isOpenMap_div_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_div_left (a : G) : IsOpenMap (a / ·)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
-/
theorem isOpenMap_div_left (a : G) : IsOpenMap (a / ·) :=
  (Homeomorph.divLeft _).isOpenMap

@[to_additive]
/-
**isClosedMap_div_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_div_left (a : G) : IsClosedMap (a / ·)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h
-/
theorem isClosedMap_div_left (a : G) : IsClosedMap (a / ·) :=
  (Homeomorph.divLeft _).isClosedMap

/-- A version of `Homeomorph.mulRight a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive (attr := simps! +simpRhs)
  /-- A version of `Homeomorph.addRight (-a) b` that is defeq to `b - a`. -/]
/-
**Homeomorph.divRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Homeomorph.divRight (x : G) : G ≃ₜ G
参数：x : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Homeomorph.divRight (x : G) : G ≃ₜ G :=
  { Equiv.divRight x with }

@[to_additive (attr := simp)]
/-
**Homeomorph.coe_divRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.coe_divRight (a : G) : ⇑(Homeomorph.divRight a) = (· / a)
参数：a : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Homeomorph.coe_divRight (a : G) : ⇑(Homeomorph.divRight a) = (· / a) :=
  rfl

@[to_additive]
/-
**isOpenMap_div_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOpenMap_div_right (a : G) : IsOpenMap (· / a)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
-/
lemma isOpenMap_div_right (a : G) : IsOpenMap (· / a) := (Homeomorph.divRight a).isOpenMap

@[to_additive]
/-
**isClosedMap_div_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosedMap_div_right (a : G) : IsClosedMap (· / a)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h
-/
lemma isClosedMap_div_right (a : G) : IsClosedMap (· / a) := (Homeomorph.divRight a).isClosedMap

@[to_additive]
/-
**tendsto_div_nhds_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_div_nhds_one_iff {α : Type*} {l : Filter α} {x : G} {u : α -> G} :
 Tendsto (u · / x) l (𝓝 1) ↔ Tendsto u l (𝓝 x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `Filter.Tendsto.div'`：Filter.Tendsto.div' {f g : α -> G} {l : Filter α} {
a b : G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f
 x / g x)…
· 使用定理 `IsTopologicalGroup.to_continuousDiv`：∀ {G : Type u} [inst : TopologicalS
pace G] [inst_1 : Group G] [IsTopologicalGroup G], ContinuousDiv G
-/
theorem tendsto_div_nhds_one_iff {α : Type*} {l : Filter α} {x : G} {u : α → G} :
    Tendsto (u · / x) l (𝓝 1) ↔ Tendsto u l (𝓝 x) :=
  haveI A : Tendsto (fun _ : α => x) l (𝓝 x) := tendsto_const_nhds
  ⟨fun h => by simpa using h.mul A, fun h => by simpa using h.div' A⟩

/-- If `f → a` and `g → b` along a nontrivial filter on the domain, valued in a
Hausdorff topological group, then `f / g → 1` if and only if `a = b`. -/
@[to_additive]
/-
**tendsto_div_nhds_one_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_div_nhds_one_iff_eq {α : Type*} {l : Filter α} [l.NeBot] [T2Space 
G] {f g : α -> G} {a b : G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) : 
Tendsto (fun x => f x / g x) l (𝓝 1) ↔ a = b
参数：hf : Tendsto f l (𝓝 a)；hg : Tendsto g l (𝓝 b)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `Filter.Tendsto.div'`：Filter.Tendsto.div' {f g : α -> G} {l : Filter α} {
a b : G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f
 x / g x)…
· 使用定理 `IsTopologicalGroup.to_continuousDiv`：∀ {G : Type u} [inst : TopologicalS
pace G] [inst_1 : Group G] [IsTopologicalGroup G], ContinuousDiv G

--- 原说明 ---
If `f → a` and `g → b` along a nontrivial filter on the domain, valued in a
Hausdorff topological group, then `f / g → 1` if and only if `a = b`.
-/
theorem tendsto_div_nhds_one_iff_eq {α : Type*} {l : Filter α} [l.NeBot] [T2Space G]
    {f g : α → G} {a b : G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun x ↦ f x / g x) l (𝓝 1) ↔ a = b :=
  ⟨fun hfg => tendsto_nhds_unique hf <| by simpa using hfg.mul hg,
   fun h => by subst h; simpa using hf.div' hg⟩

@[to_additive]
alias ⟨eq_of_tendsto_div_nhds_one, _⟩ := tendsto_div_nhds_one_iff_eq

@[to_additive]
/-
**nhds_translation_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_translation_div (x : G) : comap (· / x) (𝓝 1) = 𝓝 x
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `nhds_translation_mul_inv`：nhds_translation_mul_inv (x : G) : comap (· * 
x⁻¹) (𝓝 1) = 𝓝 x
-/
theorem nhds_translation_div (x : G) : comap (· / x) (𝓝 1) = 𝓝 x := by
  simpa only [div_eq_mul_inv] using nhds_translation_mul_inv x

variable [TopologicalSpace H] [CommGroup H] [IsTopologicalGroup H]
  [PartialOrder H] [IsOrderedMonoid H]

@[to_additive (attr := simp)]
/-
**Filter.map_divRight_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_divRight_nhdsGT {c a : H} : map (· / c) (𝓝[>] a) = 𝓝[>] (a / c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Homeomorph.divRight_apply`：∀ {G : Type w} [inst : Group G] [inst_1 : Top
ologicalSpace G] [inst_2 : IsTopologicalGroup G] (x b : G),   (Homeomorph.divRig
ht x) b = b / x
· 使用定理 `Set.image_div_const_Ioi`：image_div_const_Ioi : (fun x => x / a) '' Ioi b
 = Ioi (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.map_divRight_nhdsGT {c a : H} : map (· / c) (𝓝[>] a) = 𝓝[>] (a / c) := by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
/-
**Filter.map_divRight_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_divRight_nhdsLT {c a : H} : map (· / c) (𝓝[<] a) = 𝓝[<] (a / c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Homeomorph.divRight_apply`：∀ {G : Type w} [inst : Group G] [inst_1 : Top
ologicalSpace G] [inst_2 : IsTopologicalGroup G] (x b : G),   (Homeomorph.divRig
ht x) b = b / x
· 使用定理 `Set.image_div_const_Iio`：image_div_const_Iio : (fun x => x / a) '' Iio b
 = Iio (b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.map_divRight_nhdsLT {c a : H} : map (· / c) (𝓝[<] a) = 𝓝[<] (a / c) := by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
/-
**Filter.map_divRight_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_divRight_nhdsNE {c a : G} : map (· / c) (𝓝[!=] a) = 𝓝[!=] (a / 
c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Homeomorph.divRight_apply`：∀ {G : Type w} [inst : Group G] [inst_1 : Top
ologicalSpace G] [inst_2 : IsTopologicalGroup G] (x b : G),   (Homeomorph.divRig
ht x) b = b / x
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.preimage_mul_right_singleton`：preimage_mul_right_singleton : (· * a)
 ⁻¹' {b} = {b * a⁻¹}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.map_divRight_nhdsNE {c a : G} :
    map (· / c) (𝓝[≠] a) = 𝓝[≠] (a / c) := by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Filter.map_divRight_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_divRight_nhds {c a : G} : map (· / c) (𝓝 a) = 𝓝 (a / c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
-/
theorem Filter.map_divRight_nhds {c a : G} :
    map (· / c) (𝓝 a) = 𝓝 (a / c) := by
  convert! (Homeomorph.divRight c).map_nhds_eq .. using 2

@[to_additive (attr := simp)]
/-
**Filter.map_divLeft_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_divLeft_nhdsGT {c a : H} : map (c / ·) (𝓝[>] a) = 𝓝[<] (c / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Homeomorph.divLeft_apply`：∀ {G : Type w} [inst : Group G] [inst_1 : Topo
logicalSpace G] [inst_2 : IsTopologicalGroup G] (x b : G),   (Homeomorph.divLeft
 x) b = x / b
· 使用定理 `Set.image_const_div_Ioi`：image_const_div_Ioi : (fun x => a / x) '' Ioi b
 = Iio (a / b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.map_divLeft_nhdsGT {c a : H} : map (c / ·) (𝓝[>] a) = 𝓝[<] (c / a) := by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
/-
**Filter.map_divLeft_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_divLeft_nhdsLT {c a : H} : map (c / ·) (𝓝[<] a) = 𝓝[>] (c / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Homeomorph.divLeft_apply`：∀ {G : Type w} [inst : Group G] [inst_1 : Topo
logicalSpace G] [inst_2 : IsTopologicalGroup G] (x b : G),   (Homeomorph.divLeft
 x) b = x / b
· 使用定理 `Set.image_const_div_Iio`：image_const_div_Iio : (fun x => a / x) '' Iio b
 = Ioi (a / b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.map_divLeft_nhdsLT {c a : H} : map (c / ·) (𝓝[<] a) = 𝓝[>] (c / a) := by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
/-
**Filter.map_divLeft_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_divLeft_nhdsNE {c a : G} : map (c / ·) (𝓝[!=] a) = 𝓝[!=] (c / a
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Homeomorph.divLeft_apply`：∀ {G : Type w} [inst : Group G] [inst_1 : Topo
logicalSpace G] [inst_2 : IsTopologicalGroup G] (x b : G),   (Homeomorph.divLeft
 x) b = x / b
· 使用定理 `Set.image_div_left`：image_div_left : (a / ·) '' t = (·⁻¹ * a) ⁻¹' t
· 使用定理 `Set.preimage_inv_mul_right_singleton`：preimage_inv_mul_right_singleton :
 (·⁻¹ * a) ⁻¹' {b} = {a / b}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Filter.map_divLeft_nhdsNE {c a : G} :
    map (c / ·) (𝓝[≠] a) = 𝓝[≠] (c / a) := by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [image_div_left]

@[to_additive (attr := simp)]
/-
**Filter.map_divLeft_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_divLeft_nhds {c a : G} : map (c / ·) (𝓝 a) = 𝓝 (c / a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
-/
theorem Filter.map_divLeft_nhds {c a : G} :
    map (c / ·) (𝓝 a) = 𝓝 (c / a) := by
  convert! (Homeomorph.divLeft c).map_nhds_eq .. using 2

end DivInvTopologicalGroup

section FilterMul

section

variable (G) [TopologicalSpace G] [Group G] [ContinuousMul G]

@[to_additive]
/-
**IsTopologicalGroup.t1Space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalGroup.t1Space (h : @IsClosed G _ {1}) : T1Space G
参数：h : @IsClosed G _ {1}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `isClosedMap_mul_right`：isClosedMap_mul_right (a : G) : IsClosedMap (· * 
a)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
-/
theorem IsTopologicalGroup.t1Space (h : @IsClosed G _ {1}) : T1Space G :=
  ⟨fun x => by simpa using isClosedMap_mul_right x _ h⟩

end

section

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

variable (S : Subgroup G) [Subgroup.Normal S] [IsClosed (S : Set G)]

/-- A subgroup `S` of a topological group `G` acts on `G` properly discontinuously on the left, if
it is discrete in the sense that `S ∩ K` is finite for all compact `K`. (See also
`DiscreteTopology`.) -/
@[to_additive
  /-- A subgroup `S` of an additive topological group `G` acts on `G` properly
  discontinuously on the left, if it is discrete in the sense that `S ∩ K` is finite for all compact
  `K`. (See also `DiscreteTopology`.) -/]
/-
**Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite (S : Subgroup G) (h
S : Tendsto S.subtype cofinite (cocompact G)) : ProperlyDiscontinuousSMul S G
参数：S : Subgroup G；hS : Tendsto S.subtype cofinite (cocompact G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.compl_mem_cocompact`：∀ {X : Type u} [inst : TopologicalSpace X
] {s : Set X}, IsCompact s → sᶜ ∈ Filter.cocompact X
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
· 使用定理 `ContinuousDiv.continuous_div'`：∀ {G : Type u_4} {inst : TopologicalSpace
 G} {inst_1 : Div G} [self : ContinuousDiv G], Continuous fun p => p.1 / p.2
· 使用定理 `IsTopologicalGroup.to_continuousDiv`：∀ {G : Type u} [inst : TopologicalS
pace G] [inst_1 : Group G] [IsTopologicalGroup G], ContinuousDiv G
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.smul_inter_nonempty_iff'`：smul_inter_nonempty_iff' {s t : Set α} {x 
: α} : (x • s inter t).Nonempty ↔ exists a b, (a in t ∧ b in s) ∧ a / b = x
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
-/
theorem Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite (S : Subgroup G)
    (hS : Tendsto S.subtype cofinite (cocompact G)) : ProperlyDiscontinuousSMul S G :=
  { finite_disjoint_inter_image := by
      intro K L hK hL
      have H : Set.Finite _ := hS ((hL.prod hK).image continuous_div').compl_mem_cocompact
      rw [preimage_compl, compl_compl] at H
      convert! H
      ext x
      simp only [image_smul, mem_ofPred_eq, coe_subtype, mem_preimage, mem_image, Prod.exists]
      exact Set.smul_inter_nonempty_iff' }

/-- A subgroup `S` of a topological group `G` acts on `G` properly discontinuously on the right, if
it is discrete in the sense that `S ∩ K` is finite for all compact `K`. (See also
`DiscreteTopology`.)

If `G` is Hausdorff, this can be combined with `t2Space_of_properlyDiscontinuousSMul_of_t2Space`
to show that the quotient group `G ⧸ S` is Hausdorff. -/
@[to_additive
  /-- A subgroup `S` of an additive topological group `G` acts on `G` properly discontinuously
  on the right, if it is discrete in the sense that `S ∩ K` is finite for all compact `K`.
  (See also `DiscreteTopology`.)

  If `G` is Hausdorff, this can be combined with `t2Space_of_properlyDiscontinuousVAdd_of_t2Space`
  to show that the quotient group `G ⧸ S` is Hausdorff. -/]
/-
**Subgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite** 是 Mathlib 中的
一个定理，位于命名空间 ``。
形式化陈述：Subgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite (S : Subgr
oup G) (hS : Tendsto S.subtype cofinite (cocompact G)) : ProperlyDiscontinuousSM
ul S.op G
参数：S : Subgroup G；hS : Tendsto S.subtype cofinite (cocompact G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `IsCompact.compl_mem_cocompact`：∀ {X : Type u} [inst : TopologicalSpace X
] {s : Set X}, IsCompact s → sᶜ ∈ Filter.cocompact X
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Set.Finite.of_preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set
 β}, (f ⁻¹' s).Finite → Function.Surjective f → s.Finite
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.op_smul_inter_nonempty_iff`：op_smul_inter_nonempty_iff {s t : Set α}
 {x : αᵐᵒᵖ} : (x • s inter t).Nonempty ↔ exists a b, (a in s ∧ b in t) ∧ a⁻¹ * b
 = MulOpposite.unop …
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem Subgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite (S : Subgroup G)
    (hS : Tendsto S.subtype cofinite (cocompact G)) : ProperlyDiscontinuousSMul S.op G :=
  { finite_disjoint_inter_image := by
      intro K L hK hL
      have : Continuous fun p : G × G => (p.1⁻¹, p.2) := continuous_inv.prodMap continuous_id
      have H : Set.Finite _ :=
        hS ((hK.prod hL).image (continuous_mul.comp this)).compl_mem_cocompact
      simp only [preimage_compl, compl_compl, coe_subtype, comp_apply] at H
      apply Finite.of_preimage _ (equivOp S).surjective
      convert! H using 1
      ext x
      simp only [image_smul, mem_ofPred_eq, mem_preimage, mem_image, Prod.exists]
      exact Set.op_smul_inter_nonempty_iff }

end

section

/-! Some results about an open set containing the product of two sets in a topological group. -/


variable [TopologicalSpace G] [MulOneClass G] [ContinuousMul G]

/-- Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of `1`
  such that `K * V ⊆ U`. -/
@[to_additive
  /-- Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of
  `0` such that `K + V ⊆ U`. -/]
/-
**compact_open_separated_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compact_open_separated_mul_right {K U : Set G} (hK : IsCompact K) (hU : Is
Open U) (hKU : K subseteq U) : exists V in 𝓝 (1 : G), K * V subseteq U
参数：hK : IsCompact K；hU : IsOpen U；hKU : K subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.empty_mul`：empty_mul : ∅ * s = ∅
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mul_subset_mul_right`：mul_subset_mul_right : s₁ subseteq s₂ -> s₁ * 
t subseteq s₂ * t
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Set.union_mul`：union_mul : (s₁ union s₂) * t = s₁ * t union s₂ * t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Set.mul_subset_mul_left`：mul_subset_mul_left : t₁ subseteq t₂ -> s * t₁ 
subseteq s * t₂
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `tendsto_mul`：tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p
.snd) (𝓝 (a, b)) (𝓝 (a * b))
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `Set.image_mul_prod`：image_mul_prod : (fun x : α × α => x.fst * x.snd) ''
 s ×ˢ t = s * t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem compact_open_separated_mul_right {K U : Set G} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ V ∈ 𝓝 (1 : G), K * V ⊆ U := by
  refine hK.induction_on ?_ ?_ ?_ ?_
  · exact ⟨univ, by simp⟩
  · rintro s t hst ⟨V, hV, hV'⟩
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩
  · rintro s t ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩
    use V ∩ W, inter_mem V_in W_in
    rw [union_mul]
    exact
      union_subset ((mul_subset_mul_left V.inter_subset_left).trans hV')
        ((mul_subset_mul_left V.inter_subset_right).trans hW')
  · intro x hx
    have := tendsto_mul (show U ∈ 𝓝 (x * 1) by simpa using hU.mem_nhds (hKU hx))
    rw [nhds_prod_eq, mem_map, mem_prod_iff] at this
    rcases this with ⟨t, ht, s, hs, h⟩
    rw [← image_subset_iff, image_mul_prod] at h
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, s, hs, h⟩

open MulOpposite

/-- Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of `1`
  such that `V * K ⊆ U`. -/
@[to_additive
  /-- Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of
  `0` such that `V + K ⊆ U`. -/]
/-
**compact_open_separated_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compact_open_separated_mul_left {K U : Set G} (hK : IsCompact K) (hU : IsO
pen U) (hKU : K subseteq U) : exists V in 𝓝 (1 : G), V * K subseteq U
参数：hK : IsCompact K；hU : IsOpen U；hKU : K subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compact_open_separated_mul_right`：compact_open_separated_mul_right {K U 
: Set G} (hK : IsCompact K) (hU : IsOpen U) (hKU : K subseteq U) : exists V in 𝓝
 (1 : G), K * V subset…
· 使用定理 `MulOpposite.instContinuousMul`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] [inst_1 : Mul α] [ContinuousMul α], ContinuousMul αᵐᵒᵖ
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `MulOpposite.continuous_op`：continuous_op : Continuous (op : M -> Mᵐᵒᵖ)
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_op_mul`：image_op_mul : op '' (s * t) = op '' t * op '' s
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)
-/
theorem compact_open_separated_mul_left {K U : Set G} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ V ∈ 𝓝 (1 : G), V * K ⊆ U := by
  rcases compact_open_separated_mul_right (hK.image continuous_op) (opHomeomorph.isOpenMap U hU)
      (image_mono hKU) with
    ⟨V, hV : V ∈ 𝓝 (op (1 : G)), hV' : op '' K * V ⊆ op '' U⟩
  refine ⟨op ⁻¹' V, continuous_op.continuousAt hV, ?_⟩
  rwa [← image_preimage_eq V op_surjective, ← image_op_mul, image_subset_iff,
    preimage_image_eq _ op_injective] at hV'

end

section

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- A compact set is covered by finitely many left multiplicative translates of a set
  with non-empty interior. -/
@[to_additive
  /-- A compact set is covered by finitely many left additive translates of a set
    with non-empty interior. -/]
/-
**compact_covered_by_mul_left_translates** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compact_covered_by_mul_left_translates {K V : Set G} (hK : IsCompact K) (h
V : (interior V).Nonempty) : exists t : Finset G, K subseteq ⋃ g in t, (g * ·) ⁻
¹' V
参数：hK : IsCompact K；hV : (interior V).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `preimage_interior_subset_interior_preimage`：preimage_interior_subset_int
erior_preimage {t : Set Y} (hf : Continuous f) : f ⁻¹' interior t subseteq inter
ior (f ⁻¹' t)
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem compact_covered_by_mul_left_translates {K V : Set G} (hK : IsCompact K)
    (hV : (interior V).Nonempty) : ∃ t : Finset G, K ⊆ ⋃ g ∈ t, (g * ·) ⁻¹' V := by
  obtain ⟨t, ht⟩ : ∃ t : Finset G, K ⊆ ⋃ x ∈ t, interior ((x * ·) ⁻¹' V) := by
    refine
      hK.elim_finite_subcover (fun x => interior <| (x * ·) ⁻¹' V) (fun x => isOpen_interior) ?_
    obtain ⟨g₀, hg₀⟩ := hV
    refine fun g _ => mem_iUnion.2 ⟨g₀ * g⁻¹, ?_⟩
    refine preimage_interior_subset_interior_preimage (by fun_prop) ?_
    rwa [mem_preimage, inv_mul_cancel_right]
  exact ⟨t, Subset.trans ht <| iUnion₂_mono fun g _ => interior_subset⟩

/-- Every weakly locally compact separable topological group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis. -/
@[to_additive SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace
  /-- Every weakly locally compact separable topological additive group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SeparableWeaklyLocallyCompactGroup.sigmaCompactSpace [SeparableSpace G]
    [WeaklyLocallyCompactSpace G] : SigmaCompactSpace G := by
  obtain ⟨L, hLc, hL1⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨⟨fun n => (fun x => x * denseSeq G n) ⁻¹' L, ?_, ?_⟩⟩
  · intro n
    exact (Homeomorph.mulRight _).isCompact_preimage.mpr hLc
  · refine iUnion_eq_univ_iff.2 fun x => ?_
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ : (range (denseSeq G) ∩ (fun y => x * y) ⁻¹' L).Nonempty := by
      rw [← (Homeomorph.mulLeft x).apply_symm_apply 1] at hL1
      exact (denseRange_denseSeq G).inter_nhds_nonempty
          ((Homeomorph.mulLeft x).continuous.continuousAt <| hL1)
    exact ⟨n, hn⟩

/-- Given two compact sets in a noncompact topological group, there is a translate of the second
one that is disjoint from the first one. -/
@[to_additive
  /-- Given two compact sets in a noncompact additive topological group, there is a
  translate of the second one that is disjoint from the first one. -/]
/-
**exists_disjoint_smul_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_disjoint_smul_of_isCompact [NoncompactSpace G] {K L : Set G} (hK : 
IsCompact K) (hL : IsCompact L) : exists g : G, Disjoint K (g • L)
参数：hK : IsCompact K；hL : IsCompact L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.ne_univ`：IsCompact.ne_univ [NoncompactSpace X] (hs : IsCompact
 s) : s != univ
· 使用定理 `IsCompact.mul`：IsCompact.mul [TopologicalSpace N] [Mul N] [ContinuousMul
 N] {s t : Set N} (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s * t)
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsCompact.inv`：IsCompact.inv (hs : IsCompact s) : IsCompact s⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_disjoint_smul_of_isCompact [NoncompactSpace G] {K L : Set G} (hK : IsCompact K)
    (hL : IsCompact L) : ∃ g : G, Disjoint K (g • L) := by
  have A : ¬K * L⁻¹ = univ := (hK.mul hL.inv).ne_univ
  obtain ⟨g, hg⟩ : ∃ g, g ∉ K * L⁻¹ := by
    contrapose! A
    exact eq_univ_iff_forall.2 A
  refine ⟨g, ?_⟩
  refine disjoint_left.2 fun a ha h'a => hg ?_
  rcases h'a with ⟨b, bL, rfl⟩
  refine ⟨g * b, ha, b⁻¹, by simpa only [Set.mem_inv, inv_inv] using bL, ?_⟩
  simp only [mul_inv_cancel_right]

end

section

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

@[to_additive]
/-
**nhds_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_mul (x y : G) : 𝓝 (x * y) = 𝓝 x * 𝓝 y
参数：x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_mul_nhds_one`：nhds_mul_nhds_one {M} [MulOneClass M] [TopologicalSpa
ce M] [ContinuousMul M] (a : M) : 𝓝 a * 𝓝 1 = 𝓝 a
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `map_mul_right_nhds`：map_mul_right_nhds (x y : G) : map (· * x) (𝓝 y) = 𝓝
 (y * x)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_mul_left_nhds`：map_mul_left_nhds (x y : G) : map (x * ·) (𝓝 y) = 𝓝 (
x * y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map₂_mul`：map₂_mul : map₂ (· * ·) f g = f * g
· 使用定理 `Filter.map_map₂`：map_map₂ (m : α -> β -> γ) (n : γ -> δ) : (map₂ m f g).
map n = map₂ (fun a b => n (m a b)) f g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_mul_left_nhds_one`：map_mul_left_nhds_one (x : G) : map (x * ·) (𝓝 1)
 = 𝓝 x
· 使用定理 `map_mul_right_nhds_one`：map_mul_right_nhds_one (x : G) : map (· * x) (𝓝 
1) = 𝓝 x
· 使用定理 `Filter.map₂_map_left`：map₂_map_left (m : γ -> β -> δ) (n : α -> γ) : map
₂ m (f.map n) g = map₂ (fun a b => m (n a) b) f g
· 使用定理 `Filter.map₂_map_right`：map₂_map_right (m : α -> γ -> δ) (n : β -> γ) : m
ap₂ m f (g.map n) = map₂ (fun a b => m a (n b)) f g
-/
theorem nhds_mul (x y : G) : 𝓝 (x * y) = 𝓝 x * 𝓝 y :=
  calc
    𝓝 (x * y) = map (x * ·) (map (· * y) (𝓝 1 * 𝓝 1)) := by simp
    _ = map₂ (fun a b => x * (a * b * y)) (𝓝 1) (𝓝 1) := by rw [← map₂_mul, map_map₂, map_map₂]
    _ = map₂ (fun a b => x * a * (b * y)) (𝓝 1) (𝓝 1) := by simp only [mul_assoc]
    _ = 𝓝 x * 𝓝 y := by
      rw [← map_mul_left_nhds_one x, ← map_mul_right_nhds_one y, ← map₂_mul, map₂_map_left,
        map₂_map_right]

/-- On a topological group, `𝓝 : G → Filter G` can be promoted to a `MulHom`. -/
@[to_additive (attr := simps)
  /-- On an additive topological group, `𝓝 : G → Filter G` can be promoted to an `AddHom`. -/]
/-
**nhdsMulHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nhdsMulHom : G ->ₙ* Filter G where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_mul`：nhds_mul (x y : G) : 𝓝 (x * y) = 𝓝 x * 𝓝 y
-/
def nhdsMulHom : G →ₙ* Filter G where
  toFun := 𝓝
  map_mul' _ _ := nhds_mul _ _

end

end FilterMul

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    IsTopologicalAddGroup (Additive G) where
  continuous_neg := @continuous_inv G _ _ _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] :
    IsTopologicalGroup (Multiplicative G) where
  continuous_inv := @continuous_neg G _ _ _

/-- If `G` is a group with topological `⁻¹`, then it is homeomorphic to its units. -/
@[to_additive /-- If `G` is an additive group with topological negation, then it is homeomorphic to
its additive units. -/]
/-
**toUnits_homeomorph** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toUnits_homeomorph [Group G] [TopologicalSpace G] [ContinuousInv G] : G ≃ₜ
 Gˣ where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toUnits_homeomorph [Group G] [TopologicalSpace G] [ContinuousInv G] : G ≃ₜ Gˣ where
  toEquiv := toUnits.toEquiv
  continuous_toFun := Units.continuous_iff.2 ⟨continuous_id, continuous_inv⟩
/-
**Units.isEmbedding_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {G : Type w} [inst : Group G] [inst_1 : TopologicalSpace G] [ContinuousI
nv G], Topology.IsEmbedding Units.val
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
@[to_additive] theorem Units.isEmbedding_val [Group G] [TopologicalSpace G] [ContinuousInv G] :
    IsEmbedding (val : Gˣ → G) :=
  toUnits_homeomorph.symm.isEmbedding
/-
**Continuous.of_coeHom_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.of_coeHom_comp [Group G] [Monoid H] [TopologicalSpace G] [Topol
ogicalSpace H] [ContinuousInv G] {f : G ->* Hˣ} (hf : Continuous ((Units.coeHom 
H).comp f)) : Continuous f
参数：hf : Continuous ((Units.coeHom H).comp f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `continuous_prodMk`：continuous_prodMk {f : X -> Y} {g : X -> Z} : (Contin
uous fun x => (f x, g x)) ↔ Continuous f ∧ Continuous g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `MulOpposite.continuous_op`：continuous_op : Continuous (op : M -> Mᵐᵒᵖ)
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
lemma Continuous.of_coeHom_comp [Group G] [Monoid H] [TopologicalSpace G] [TopologicalSpace H]
    [ContinuousInv G] {f : G →* Hˣ} (hf : Continuous ((Units.coeHom H).comp f)) : Continuous f := by
  apply continuous_induced_rng.mpr ?_
  refine continuous_prodMk.mpr ⟨hf, ?_⟩
  simp_rw [← map_inv]
  exact MulOpposite.continuous_op.comp (hf.comp continuous_inv)

namespace Units

open MulOpposite (continuous_op continuous_unop)

@[to_additive]
/-
**Units.range_embedProduct** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：range_embedProduct [Monoid α] : Set.range (embedProduct α) = {p : α × αᵐᵒᵖ
 | p.1 * unop p.2 = 1 ∧ unop p.2 * p.1 = 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_iff`：range_eq_iff (f : α -> β) (s : Set β) : range f = s ↔ 
(forall a, f a in s) ∧ forall b in s, exists a, f a = b
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem range_embedProduct [Monoid α] :
    Set.range (embedProduct α) = {p : α × αᵐᵒᵖ | p.1 * unop p.2 = 1 ∧ unop p.2 * p.1 = 1} :=
  Set.range_eq_iff _ _ |>.mpr
    ⟨fun a ↦ ⟨a.mul_inv, a.inv_mul⟩, fun p hp ↦ ⟨⟨p.1, unop p.2, hp.1, hp.2⟩, rfl⟩⟩

variable [Monoid α] [TopologicalSpace α] [Monoid β] [TopologicalSpace β]

@[to_additive]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ContinuousMul α] : IsTopologicalGroup αˣ where
  continuous_inv := Units.continuous_iff.2 <| ⟨continuous_coe_inv, continuous_val⟩

@[to_additive]
/-
**Units.isClosedEmbedding_embedProduct** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：isClosedEmbedding_embedProduct [T1Space α] [ContinuousMul α] : IsClosedEmb
edding (embedProduct α) where toIsEmbedding
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isEmbedding_embedProduct`：isEmbedding_embedProduct : IsEmbedding (
embedProduct M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.range_embedProduct`：range_embedProduct [Monoid α] : Set.range (emb
edProduct α) = {p : α × αᵐᵒᵖ | p.1 * unop p.2 = 1 ∧ unop p.2 * p.1 = 1}
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MulOpposite.continuous_unop`：continuous_unop : Continuous (unop : Mᵐᵒᵖ -
> M)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
-/
theorem isClosedEmbedding_embedProduct [T1Space α] [ContinuousMul α] :
    IsClosedEmbedding (embedProduct α) where
  toIsEmbedding := isEmbedding_embedProduct
  isClosed_range := by
    rw [range_embedProduct]
    refine .inter (isClosed_singleton.preimage ?_) (isClosed_singleton.preimage ?_) <;>
    fun_prop
/-
**Units._root_.Topology.IsClosedEmbedding.units_map** 是 Mathlib 中的一个引理，位于命名空间 `U
nits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Topology.IsClosedEmbedding.units_map [ContinuousMul α] [T1Space α] {f : α →* β}
    (hf : IsClosedEmbedding f) : IsClosedEmbedding (map f) := by
  refine .of_comp isEmbedding_embedProduct ?_
  exact (hf.prodMap (opHomeomorph.isClosedEmbedding.comp
    <| hf.comp opHomeomorph.symm.isClosedEmbedding)).comp isClosedEmbedding_embedProduct

@[to_additive]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T1Space α] [ContinuousMul α] [CompactSpace α] : CompactSpace αˣ :=
  isClosedEmbedding_embedProduct.compactSpace

@[to_additive]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T1Space α] [ContinuousMul α] [WeaklyLocallyCompactSpace α] :
    WeaklyLocallyCompactSpace αˣ :=
  isClosedEmbedding_embedProduct.weaklyLocallyCompactSpace

@[to_additive]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T1Space α] [ContinuousMul α] [LocallyCompactSpace α] : LocallyCompactSpace αˣ :=
  isClosedEmbedding_embedProduct.locallyCompactSpace
/-
**Units._root_.Submonoid.units_isCompact** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Submonoid.units_isCompact [T1Space α] [ContinuousMul α] {S : Submonoid α}
    (hS : IsCompact (S : Set α)) : IsCompact (S.units : Set αˣ) := by
  have : IsCompact (S ×ˢ S.op) := hS.prod (opHomeomorph.isCompact_preimage.mp hS)
  exact isClosedEmbedding_embedProduct.isCompact_preimage this

/-- The topological group isomorphism between the units of a product of two monoids, and the product
of the units of each monoid. -/
@[to_additive prodAddUnits
  /-- The topological group isomorphism between the additive units of a product of two
  additive monoids, and the product of the additive units of each additive monoid. -/]
/-
**Units._root_.Homeomorph.prodUnits** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.Homeomorph.prodUnits : (α × β)ˣ ≃ₜ αˣ × βˣ where
  continuous_toFun :=
    (continuous_fst.units_map (MonoidHom.fst α β)).prodMk
      (continuous_snd.units_map (MonoidHom.snd α β))
  continuous_invFun :=
    Units.continuous_iff.2
      ⟨continuous_val.fst'.prodMk continuous_val.snd',
        continuous_coe_inv.fst'.prodMk continuous_coe_inv.snd'⟩
  toEquiv := MulEquiv.prodUnits.toEquiv

end Units

section LatticeOps

variable {ι : Sort*} [Group G]

@[to_additive]
/-
**topologicalGroup_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：topologicalGroup_sInf {ts : Set (TopologicalSpace G)} (h : forall t in ts,
 @IsTopologicalGroup G t _) : @IsTopologicalGroup G (sInf ts) _
参数：TopologicalSpace G；h : forall t in ts, @IsTopologicalGroup G t _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousMul_sInf`：continuousMul_sInf {ts : Set (TopologicalSpace M)} (
h : forall t in ts, @ContinuousMul M t _) : @ContinuousMul M (sInf ts) _
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `continuousInv_sInf`：continuousInv_sInf {ts : Set (TopologicalSpace G)} (
h : forall t in ts, @ContinuousInv G t _) : @ContinuousInv G (sInf ts) _
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
-/
theorem topologicalGroup_sInf {ts : Set (TopologicalSpace G)}
    (h : ∀ t ∈ ts, @IsTopologicalGroup G t _) : @IsTopologicalGroup G (sInf ts) _ :=
  letI := sInf ts
  { toContinuousInv :=
      @continuousInv_sInf _ _ _ fun t ht => @IsTopologicalGroup.toContinuousInv G t _ <| h t ht
    toContinuousMul :=
      @continuousMul_sInf _ _ _ fun t ht =>
        @IsTopologicalGroup.toContinuousMul G t _ <| h t ht }

@[to_additive]
/-
**topologicalGroup_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：topologicalGroup_iInf {ts' : ι -> TopologicalSpace G} (h' : forall i, @IsT
opologicalGroup G (ts' i) _) : @IsTopologicalGroup G (⨅ i, ts' i) _
参数：h' : forall i, @IsTopologicalGroup G (ts' i) _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用定理 `topologicalGroup_sInf`：topologicalGroup_sInf {ts : Set (TopologicalSpace
 G)} (h : forall t in ts, @IsTopologicalGroup G t _) : @IsTopologicalGroup G (sI
nf ts) _
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem topologicalGroup_iInf {ts' : ι → TopologicalSpace G}
    (h' : ∀ i, @IsTopologicalGroup G (ts' i) _) : @IsTopologicalGroup G (⨅ i, ts' i) _ := by
  rw [← sInf_range]
  exact topologicalGroup_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
/-
**topologicalGroup_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：topologicalGroup_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @IsTopologicalGrou
p G t₁ _) (h₂ : @IsTopologicalGroup G t₂ _) : @IsTopologicalGroup G (t₁ ⊓ t₂) _
参数：h₁ : @IsTopologicalGroup G t₁ _；h₂ : @IsTopologicalGroup G t₂ _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] (x y : α), x ⊓ 
y = ⨅ b, bif b then x else y
· 使用定理 `topologicalGroup_iInf`：topologicalGroup_iInf {ts' : ι -> TopologicalSpac
e G} (h' : forall i, @IsTopologicalGroup G (ts' i) _) : @IsTopologicalGroup G (⨅
 i, ts' i) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem topologicalGroup_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @IsTopologicalGroup G t₁ _)
    (h₂ : @IsTopologicalGroup G t₂ _) : @IsTopologicalGroup G (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine topologicalGroup_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps

