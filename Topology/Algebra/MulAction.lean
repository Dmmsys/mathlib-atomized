/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Order.Filter.Pointwise
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.Basic

/-!
# Continuous monoid action

In this file we define class `ContinuousSMul`. We say `ContinuousSMul M X` if `M` acts on `X` and
the map `(c, x) ↦ c • x` is continuous on `M × X`. We reuse this class for topological
(semi)modules, vector spaces and algebras.

## Main definitions

* `ContinuousSMul M X` : typeclass saying that the map `(c, x) ↦ c • x` is continuous
  on `M × X`;
* `Units.continuousSMul`: scalar multiplication by `Mˣ` is continuous when scalar
  multiplication by `M` is continuous. This allows `Homeomorph.smul` to be used with on monoids
  with `G = Mˣ`.

## Main results

Besides homeomorphisms mentioned above, in this file we provide lemmas like `Continuous.smul`
or `Filter.Tendsto.smul` that provide dot-syntax access to `ContinuousSMul`.
-/

public section

open Topology Pointwise

open Filter

/--
Definition of `ContinuousSMul` / `ContinuousSMul` 的定义

English:
class ContinuousSMul
  parameters: (M X : Type*) [SMul M X] [TopologicalSpace M] [TopologicalSpace X]
  axioms and operations (1):
    - continuous_smul : Continuous fun p : M × X => p.1 • p.2

中文:
类 连续标量乘法
  参数: (M X : 类型) [标量乘法 M X] [拓扑空间 M] [拓扑空间 X]
  公理与运算 (1 个):
    - continuous_smul : 连续 fun p : M × X => p.1 • p.2
-/
class ContinuousSMul (M X : Type*) [SMul M X] [TopologicalSpace M] [TopologicalSpace X] :
    Prop where
  /-- The scalar multiplication `(•)` is continuous. -/
  continuous_smul : Continuous fun p : M × X => p.1 • p.2

export ContinuousSMul (continuous_smul)

/--
Definition of `ContinuousVAdd` / `ContinuousVAdd` 的定义

English:
class ContinuousVAdd
  parameters: (M X : Type*) [VAdd M X] [TopologicalSpace M] [TopologicalSpace X]
  axioms and operations (1):
    - continuous_vadd : Continuous fun p : M × X => p.1 +ᵥ p.2

中文:
类 连续向量加法
  参数: (M X : 类型) [向量加法 M X] [拓扑空间 M] [拓扑空间 X]
  公理与运算 (1 个):
    - continuous_vadd : 连续 fun p : M × X => p.1 +ᵥ p.2
-/
class ContinuousVAdd (M X : Type*) [VAdd M X] [TopologicalSpace M] [TopologicalSpace X] :
    Prop where
  /-- The additive action `(+ᵥ)` is continuous. -/
  continuous_vadd : Continuous fun p : M × X => p.1 +ᵥ p.2

export ContinuousVAdd (continuous_vadd)

attribute [to_additive] ContinuousSMul

attribute [continuity, fun_prop] continuous_smul continuous_vadd

section Main

variable {M X Y α : Type*} [TopologicalSpace M] [TopologicalSpace X] [TopologicalSpace Y]

section SMul

variable [SMul M X] [ContinuousSMul M X]

/--
lemma `IsScalarTower.continuousSMul` / 引理 `IsScalarTower.continuousSMul`

English:
lemma IsScalarTower.continuousSMul
  statement: {M : Type*} (N : Type*) {α : Type*} [Monoid N] [SMul M N]
  proof: { continuous_smul := by
      suffices Continuous (fun p : M × α => (p.1 • (1 : N)) • p.2) by simpa
      fun_prop }

@[to_additive]

中文:
引理 标量塔.continuousSMul
  结论: {M : 类型} (N : 类型) {α : 类型} [幺半群 N] [标量乘法 M N]
  证明: { continuous_smul := by
      suffices Continuous (fun p : M × α => (p.1 • (1 : N)) • p.2) by simpa
      fun_prop }

@[to_additive]

Depends on / 依赖: Continuous, continuous_smul, fun_prop
-/
lemma IsScalarTower.continuousSMul {M : Type*} (N : Type*) {α : Type*} [Monoid N] [SMul M N]
    [MulAction N α] [SMul M α] [IsScalarTower M N α] [TopologicalSpace M] [TopologicalSpace N]
    [TopologicalSpace α] [ContinuousSMul M N] [ContinuousSMul N α] : ContinuousSMul M α :=
  { continuous_smul := by
      suffices Continuous (fun p : M × α => (p.1 • (1 : N)) • p.2) by simpa
      fun_prop }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousSMul (ULift M) X
  body: ⟨(continuous_smul (M := M)).comp₂ (continuous_uliftDown.comp continuous_fst) continuous_snd⟩

@[to_additive]

中文:
实例 :
  签名: 连续标量乘法 (类型层提升 M) X
  定义体: ⟨(continuous_smul (M := M)).comp₂ (continuous_uliftDown.comp continuous_fst) continuous_snd⟩

@[to_additive]

Depends on / 依赖: continuous_fst, continuous_smul, continuous_snd, continuous_uliftDown, continuous_uliftDown.comp
-/
instance : ContinuousSMul (ULift M) X :=
  ⟨(continuous_smul (M := M)).comp₂ (continuous_uliftDown.comp continuous_fst) continuous_snd⟩

@[to_additive]
/--
Instance `OrderDual.instContinuousSMul_right` / 实例 `OrderDual.instContinuousSMul_right`

English:
instance OrderDual.instContinuousSMul_right
  signature: : ContinuousSMul M Xᵒᵈ where
  body: continuous_smul (M := M) (X := X)

@[to_additive]

中文:
实例 OrderDual.instContinuousSMul_right
  签名: : 连续标量乘法 M Xᵒᵈ where
  定义体: continuous_smul (M := M) (X := X)

@[to_additive]

Depends on / 依赖: continuous_smul
-/
instance OrderDual.instContinuousSMul_right : ContinuousSMul M Xᵒᵈ where
  continuous_smul := continuous_smul (M := M) (X := X)

@[to_additive]
/--
Instance `OrderDual.instContinuousSMul_left` / 实例 `OrderDual.instContinuousSMul_left`

English:
instance OrderDual.instContinuousSMul_left
  signature: : ContinuousSMul Mᵒᵈ X where
  body: continuous_smul (M := M) (X := X)

@[to_additive]

中文:
实例 OrderDual.instContinuousSMul_left
  签名: : 连续标量乘法 Mᵒᵈ X where
  定义体: continuous_smul (M := M) (X := X)

@[to_additive]

Depends on / 依赖: continuous_smul
-/
instance OrderDual.instContinuousSMul_left : ContinuousSMul Mᵒᵈ X where
  continuous_smul := continuous_smul (M := M) (X := X)

@[to_additive]
instance (priority := 100) ContinuousSMul.continuousConstSMul : ContinuousConstSMul M X where
  continuous_const_smul _ := continuous_smul.comp (continuous_const.prodMk continuous_id)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ContinuousSMul.induced` / 定理 `ContinuousSMul.induced`

English:
theorem ContinuousSMul.induced
  statement: {R : Type*} {α : Type*} {β : Type*} {F : Type*} [FunLike F α β]
  proof: by
  let tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_smul]
  fun_prop

@[to_additive]

中文:
定理 连续标量乘法.induced
  结论: {R : 类型} {α : 类型} {β : 类型} {F : 类型} [函数状 F α β]
  证明: by
  let tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_smul]
  fun_prop

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, comp_def, continuous_induced_rng, fun_prop, induced, map_smul
-/
theorem ContinuousSMul.induced {R : Type*} {α : Type*} {β : Type*} {F : Type*} [FunLike F α β]
    [Semiring R] [AddCommMonoid α] [AddCommMonoid β] [Module R α] [Module R β]
    [TopologicalSpace R] [LinearMapClass F R α β] [tβ : TopologicalSpace β] [ContinuousSMul R β]
    (f : F) : @ContinuousSMul R α _ _ (tβ.induced f) := by
  let tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_smul]
  fun_prop

@[to_additive]
/--
theorem `Filter.Tendsto.smul` / 定理 `Filter.Tendsto.smul`

English:
theorem Filter.Tendsto.smul
  statement: {f : α -> M} {g : α -> X} {l : Filter α} {c : M} {a : X}
  proof: (continuous_smul.tendsto _).comp (hf.prodMk_nhds hg)

@[to_additive]

中文:
定理 滤子.收敛.smul
  结论: {f : α -> M} {g : α -> X} {l : 滤子 α} {c : M} {a : X}
  证明: (continuous_smul.tendsto _).comp (hf.prodMk_nhds hg)

@[to_additive]

Depends on / 依赖: continuous_smul, continuous_smul.tendsto, hf.prodMk_nhds, prodMk_nhds, tendsto
-/
theorem Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : Filter α} {c : M} {a : X}
    (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) :
    Tendsto (fun x => f x • g x) l (𝓝 <| c • a) :=
  (continuous_smul.tendsto _).comp (hf.prodMk_nhds hg)

@[to_additive]
/--
theorem `Filter.Tendsto.smul_const` / 定理 `Filter.Tendsto.smul_const`

English:
theorem Filter.Tendsto.smul_const
  statement: {f : α -> M} {l : Filter α} {c : M} (hf : Tendsto f l (𝓝 c))
  proof: hf.smul tendsto_const_nhds

中文:
定理 滤子.收敛.smul_const
  结论: {f : α -> M} {l : 滤子 α} {c : M} (hf : 收敛 f l (𝓝 c))
  证明: hf.smul tendsto_const_nhds

Depends on / 依赖: hf.smul, tendsto_const_nhds
-/
theorem Filter.Tendsto.smul_const {f : α -> M} {l : Filter α} {c : M} (hf : Tendsto f l (𝓝 c))
    (a : X) : Tendsto (fun x => f x • a) l (𝓝 (c • a)) :=
  hf.smul tendsto_const_nhds

variable {f : Y -> M} {g : Y -> X} {b : Y} {s : Set Y}

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `ContinuousWithinAt.smul` / 定理 `ContinuousWithinAt.smul`

English:
theorem ContinuousWithinAt.smul
  given: (hf : ContinuousWithinAt f s b) (hg : ContinuousWithinAt g s b)
  proof: Filter.Tendsto.smul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 ContinuousWithinAt.smul
  条件: (hf : ContinuousWithinAt f s b) (hg : ContinuousWithinAt g s b)
  证明: Filter.Tendsto.smul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: Filter, Filter.Tendsto.smul, Tendsto
-/
theorem ContinuousWithinAt.smul (hf : ContinuousWithinAt f s b) (hg : ContinuousWithinAt g s b) :
    ContinuousWithinAt (f • g) s b :=
  Filter.Tendsto.smul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `ContinuousAt.smul` / 定理 `ContinuousAt.smul`

English:
theorem ContinuousAt.smul
  given: (hf : ContinuousAt f b) (hg : ContinuousAt g b)
  proof: Filter.Tendsto.smul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 ContinuousAt.smul
  条件: (hf : ContinuousAt f b) (hg : ContinuousAt g b)
  证明: Filter.Tendsto.smul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: Filter, Filter.Tendsto.smul, Tendsto
-/
theorem ContinuousAt.smul (hf : ContinuousAt f b) (hg : ContinuousAt g b) :
    ContinuousAt (f • g) b :=
  Filter.Tendsto.smul hf hg

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `ContinuousOn.smul` / 定理 `ContinuousOn.smul`

English:
theorem ContinuousOn.smul
  given: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  proof: fun x hx => (hf x hx).smul (hg x hx)

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]

中文:
定理 ContinuousOn.smul
  条件: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  证明: fun x hx => (hf x hx).smul (hg x hx)

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]
-/
theorem ContinuousOn.smul (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (f • g) s := fun x hx => (hf x hx).smul (hg x hx)

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]
/--
theorem `Continuous.smul` / 定理 `Continuous.smul`

English:
theorem Continuous.smul
  given: (hf : Continuous f) (hg : Continuous g)
  statement: Continuous (f • g)
  proof: continuous_smul.comp (hf.prodMk hg)

中文:
定理 连续.smul
  条件: (hf : 连续 f) (hg : 连续 g)
  结论: 连续 (f • g)
  证明: continuous_smul.comp (hf.prodMk hg)

Depends on / 依赖: continuous_smul, continuous_smul.comp, hf.prodMk, prodMk
-/
theorem Continuous.smul (hf : Continuous f) (hg : Continuous g) : Continuous (f • g) :=
  continuous_smul.comp (hf.prodMk hg)

/-- If a scalar action is central, then its right action is continuous when its left action is. -/
@[to_additive /-- If an additive action is central, then its right action is continuous when its
left action is. -/]
/--
Instance `ContinuousSMul.op` / 实例 `ContinuousSMul.op`

English:
instance ContinuousSMul.op
  signature: [SMul Mᵐᵒᵖ X] [IsCentralScalar M X]
  body: ⟨by
    suffices Continuous fun p : M × X => MulOpposite.op p.fst • p.snd from
      this.comp (MulOpposite.continuous_unop.prodMap continuous_id)
    simpa only [op_smul_eq_smul] using (continuous_smul : Continuous fun p : M × X => _)⟩

@[to_additive]

中文:
实例 连续标量乘法.op
  签名: [标量乘法 Mᵐᵒᵖ X] [中心标量 M X]
  定义体: ⟨by
    suffices Continuous fun p : M × X => MulOpposite.op p.fst • p.snd from
      this.comp (MulOpposite.continuous_unop.prodMap continuous_id)
    simpa only [op_smul_eq_smul] using (continuous_smul : Continuous fun p : M × X => _)⟩

@[to_additive]

Depends on / 依赖: Continuous, MulOpposite, MulOpposite.continuous_unop.prodMap, MulOpposite.op, continuous_id, continuous_smul, continuous_unop, op_smul_eq_smul, p.fst, p.snd, prodMap, this.comp
-/
instance ContinuousSMul.op [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] : ContinuousSMul Mᵐᵒᵖ X :=
  ⟨by
    suffices Continuous fun p : M × X => MulOpposite.op p.fst • p.snd from
      this.comp (MulOpposite.continuous_unop.prodMap continuous_id)
    simpa only [op_smul_eq_smul] using (continuous_smul : Continuous fun p : M × X => _)⟩

@[to_additive]
/--
Instance `MulOpposite.continuousSMul` / 实例 `MulOpposite.continuousSMul`

English:
instance MulOpposite.continuousSMul
  signature: : ContinuousSMul M Xᵐᵒᵖ
  body: ⟨MulOpposite.continuous_op.comp
continuous_smul.comp continuous_id.prodMap MulOpposite.continuous_unop⟩

@[to_additive]

中文:
实例 MulOpposite.continuousSMul
  签名: : 连续标量乘法 M Xᵐᵒᵖ
  定义体: ⟨MulOpposite.continuous_op.comp
continuous_smul.comp continuous_id.prodMap MulOpposite.continuous_unop⟩

@[to_additive]

Depends on / 依赖: MulOpposite, MulOpposite.continuous_op.comp, MulOpposite.continuous_unop, continuous_id, continuous_id.prodMap, continuous_op, continuous_smul, continuous_smul.comp, continuous_unop, prodMap
-/
instance MulOpposite.continuousSMul : ContinuousSMul M Xᵐᵒᵖ :=
⟨MulOpposite.continuous_op.comp
continuous_smul.comp continuous_id.prodMap MulOpposite.continuous_unop⟩

@[to_additive]
/--
theorem `Specializes.smul` / 定理 `Specializes.smul`

English:
theorem Specializes.smul
  given: {a b : M} {x y : X} (h₁ : a ⤳ b) (h₂ : x ⤳ y)
  proof: (h₁.prod h₂).map continuous_smul

@[to_additive]

中文:
定理 Specializes.smul
  条件: {a b : M} {x y : X} (h₁ : a ⤳ b) (h₂ : x ⤳ y)
  证明: (h₁.prod h₂).map continuous_smul

@[to_additive]
-/
protected theorem Specializes.smul {a b : M} {x y : X} (h₁ : a ⤳ b) (h₂ : x ⤳ y) :
    (a • x) ⤳ (b • y) :=
  (h₁.prod h₂).map continuous_smul

@[to_additive]
/--
theorem `Inseparable.smul` / 定理 `Inseparable.smul`

English:
theorem Inseparable.smul
  statement: {a b : M} {x y : X} (h₁ : Inseparable a b)
  proof: (h₁.prod h₂).map continuous_smul

@[to_additive]

中文:
定理 不可分.smul
  结论: {a b : M} {x y : X} (h₁ : 不可分 a b)
  证明: (h₁.prod h₂).map continuous_smul

@[to_additive]
-/
protected theorem Inseparable.smul {a b : M} {x y : X} (h₁ : Inseparable a b)
    (h₂ : Inseparable x y) : Inseparable (a • x) (b • y) :=
  (h₁.prod h₂).map continuous_smul

@[to_additive]
/--
lemma `IsCompact.smul_set` / 引理 `IsCompact.smul_set`

English:
lemma IsCompact.smul_set
  given: {k : Set M} {u : Set X} (hk : IsCompact k) (hu : IsCompact u)
  proof: by
  rw [← Set.image_smul_prod]
  exact IsCompact.image (hk.prod hu) continuous_smul

@[to_additive]

中文:
引理 是紧集.smul_set
  条件: {k : 集合 M} {u : 集合 X} (hk : 是紧集 k) (hu : 是紧集 u)
  证明: by
  rw [← Set.image_smul_prod]
  exact IsCompact.image (hk.prod hu) continuous_smul

@[to_additive]

Depends on / 依赖: IsCompact, IsCompact.image, Set.image_smul_prod, continuous_smul, hk.prod, image_smul_prod
-/
lemma IsCompact.smul_set {k : Set M} {u : Set X} (hk : IsCompact k) (hu : IsCompact u) :
    IsCompact (k • u) := by
  rw [← Set.image_smul_prod]
  exact IsCompact.image (hk.prod hu) continuous_smul

@[to_additive]
/--
lemma `smul_set_closure_subset` / 引理 `smul_set_closure_subset`

English:
lemma smul_set_closure_subset
  given: (K : Set M) (L : Set X)
  proof: Set.smul_subset_iff.2 fun _x hx _y hy => map_mem_closure₂ continuous_smul hx hy fun _a ha _b hb =>
    Set.smul_mem_smul ha hb

中文:
引理 smul_set_closure_subset
  条件: (K : 集合 M) (L : 集合 X)
  证明: Set.smul_subset_iff.2 fun _x hx _y hy => map_mem_closure₂ continuous_smul hx hy fun _a ha _b hb =>
    Set.smul_mem_smul ha hb

Depends on / 依赖: Set.smul_mem_smul, Set.smul_subset_iff, continuous_smul, smul_mem_smul, smul_subset_iff
-/
lemma smul_set_closure_subset (K : Set M) (L : Set X) :
    closure K • closure L subseteq closure (K • L) :=
  Set.smul_subset_iff.2 fun _x hx _y hy => map_mem_closure₂ continuous_smul hx hy fun _a ha _b hb =>
    Set.smul_mem_smul ha hb

/-- Suppose that `N` acts on `X` and `M` continuously acts on `Y`.
Suppose that `g : Y → X` is an action homomorphism in the following sense:
there exists a continuous function `f : N → M` such that `g (c • x) = f c • g x`.
Then the action of `N` on `X` is continuous as well.

In many cases, `f = id` so that `g` is an action homomorphism in the sense of `MulActionHom`.
However, this version also works for semilinear maps and `f = Units.val`. -/
@[to_additive
  /-- Suppose that `N` additively acts on `X` and `M` continuously additively acts on `Y`.
Suppose that `g : Y → X` is an additive action homomorphism in the following sense:
there exists a continuous function `f : N → M` such that `g (c +ᵥ x) = f c +ᵥ g x`.
Then the action of `N` on `X` is continuous as well.

In many cases, `f = id` so that `g` is an action homomorphism in the sense of `AddActionHom`.
However, this version also works for `f = AddUnits.val`. -/]
/--
lemma `Topology.IsInducing.continuousSMul` / 引理 `Topology.IsInducing.continuousSMul`

English:
lemma Topology.IsInducing.continuousSMul
  statement: {N : Type*} [SMul N Y] [TopologicalSpace N] {f : N -> M}
  proof: by
    simpa only [hg.continuous_iff, Function.comp_def, hsmul]
using (hf.comp continuous_fst).fun_smul hg.continuous.comp continuous_snd

@[to_additive]

中文:
引理 拓扑.是Inducing.continuousSMul
  结论: {N : 类型} [标量乘法 N Y] [拓扑空间 N] {f : N -> M}
  证明: by
    simpa only [hg.continuous_iff, Function.comp_def, hsmul]
using (hf.comp continuous_fst).fun_smul hg.continuous.comp continuous_snd

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, comp_def, continuous, continuous_fst, continuous_iff, continuous_snd, fun_smul, hf.comp, hg.continuous.comp, hg.continuous_iff
-/
lemma Topology.IsInducing.continuousSMul {N : Type*} [SMul N Y] [TopologicalSpace N] {f : N -> M}
    (hg : IsInducing g) (hf : Continuous f) (hsmul : forall {c x}, g (c • x) = f c • g x) :
    ContinuousSMul N Y where
  continuous_smul := by
    simpa only [hg.continuous_iff, Function.comp_def, hsmul]
using (hf.comp continuous_fst).fun_smul hg.continuous.comp continuous_snd

@[to_additive]
/--
Instance `SMulMemClass.continuousSMul` / 实例 `SMulMemClass.continuousSMul`

English:
instance SMulMemClass.continuousSMul
  signature: {S : Type*} [SetLike S X] [SMulMemClass S M X] (s : S)
  body: IsInducing.subtypeVal.continuousSMul continuous_id rfl

中文:
实例 SMulMem类.continuousSMul
  签名: {S : 类型} [集合状 S X] [SMulMem类 S M X] (s : S)
  定义体: IsInducing.subtypeVal.continuousSMul continuous_id rfl

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.continuousSMul, continuousSMul, continuous_id, subtypeVal
-/
instance SMulMemClass.continuousSMul {S : Type*} [SetLike S X] [SMulMemClass S M X] (s : S) :
    ContinuousSMul M s :=
  IsInducing.subtypeVal.continuousSMul continuous_id rfl

end SMul

section SMulZeroClass

variable [Zero X] [SMulZeroClass M X] [ContinuousSMul M X]

/--
theorem `Filter.Tendsto.smul_zero` / 定理 `Filter.Tendsto.smul_zero`

English:
theorem Filter.Tendsto.smul_zero
  statement: {f : α -> M} {g : α -> X} {l : Filter α} {c : M}
  proof: smul_zero c (A := X) ▸ hf.smul hg

中文:
定理 滤子.收敛.smul_zero
  结论: {f : α -> M} {g : α -> X} {l : 滤子 α} {c : M}
  证明: smul_zero c (A := X) ▸ hf.smul hg
-/
protected theorem Filter.Tendsto.smul_zero {f : α -> M} {g : α -> X} {l : Filter α} {c : M}
    (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x • g x) l (𝓝 0) :=
  smul_zero c (A := X) ▸ hf.smul hg

end SMulZeroClass

section SMulWithZero

variable [Zero M] [Zero X] [SMulWithZero M X] [ContinuousSMul M X]

/--
theorem `Filter.Tendsto.zero_smul` / 定理 `Filter.Tendsto.zero_smul`

English:
theorem Filter.Tendsto.zero_smul
  statement: {f : α -> M} {g : α -> X} {l : Filter α} {a : X}
  proof: zero_smul M a ▸ hf.smul hg

中文:
定理 滤子.收敛.zero_smul
  结论: {f : α -> M} {g : α -> X} {l : 滤子 α} {a : X}
  证明: zero_smul M a ▸ hf.smul hg
-/
protected theorem Filter.Tendsto.zero_smul {f : α -> M} {g : α -> X} {l : Filter α} {a : X}
    (hf : Tendsto f l (𝓝 0)) (hg : Tendsto g l (𝓝 a)) :
    Tendsto (fun x => f x • g x) l (𝓝 0) :=
  zero_smul M a ▸ hf.smul hg

/--
theorem `Filter.Tendsto.zero_smul_const` / 定理 `Filter.Tendsto.zero_smul_const`

English:
theorem Filter.Tendsto.zero_smul_const
  statement: {f : α -> M} {l : Filter α}
  proof: hf.zero_smul tendsto_const_nhds

中文:
定理 滤子.收敛.zero_smul_const
  结论: {f : α -> M} {l : 滤子 α}
  证明: hf.zero_smul tendsto_const_nhds
-/
protected theorem Filter.Tendsto.zero_smul_const {f : α -> M} {l : Filter α}
    (hf : Tendsto f l (𝓝 0)) (a : X) :
    Tendsto (fun x => f x • a) l (𝓝 0) :=
  hf.zero_smul tendsto_const_nhds

end SMulWithZero

section Monoid

variable [Monoid M] [MulAction M X] [ContinuousSMul M X]

@[to_additive]
/--
theorem `Filter.Tendsto.one_smul` / 定理 `Filter.Tendsto.one_smul`

English:
theorem Filter.Tendsto.one_smul
  statement: {f : α -> M} {g : α -> X} {l : Filter α} {a : X}
  proof: one_smul M a ▸ hf.smul hg

@[to_additive]

中文:
定理 滤子.收敛.one_smul
  结论: {f : α -> M} {g : α -> X} {l : 滤子 α} {a : X}
  证明: one_smul M a ▸ hf.smul hg

@[to_additive]
-/
protected theorem Filter.Tendsto.one_smul {f : α -> M} {g : α -> X} {l : Filter α} {a : X}
    (hf : Tendsto f l (𝓝 1)) (hg : Tendsto g l (𝓝 a)) :
    Tendsto (fun x => f x • g x) l (𝓝 a) :=
  one_smul M a ▸ hf.smul hg

@[to_additive]
/--
theorem `Filter.Tendsto.one_smul_const` / 定理 `Filter.Tendsto.one_smul_const`

English:
theorem Filter.Tendsto.one_smul_const
  statement: {f : α -> M} {l : Filter α}
  proof: hf.one_smul tendsto_const_nhds

@[to_additive]

中文:
定理 滤子.收敛.one_smul_const
  结论: {f : α -> M} {l : 滤子 α}
  证明: hf.one_smul tendsto_const_nhds

@[to_additive]
-/
protected theorem Filter.Tendsto.one_smul_const {f : α -> M} {l : Filter α}
    (hf : Tendsto f l (𝓝 1)) (a : X) : Tendsto (fun x => f x • a) l (𝓝 a) :=
  hf.one_smul tendsto_const_nhds

@[to_additive]
/--
Instance `Units.continuousSMul` / 实例 `Units.continuousSMul`

English:
instance Units.continuousSMul
  signature: : ContinuousSMul Mˣ X
  body: IsInducing.id.continuousSMul Units.continuous_val rfl

中文:
实例 单位群.continuousSMul
  签名: : 连续标量乘法 Mˣ X
  定义体: IsInducing.id.continuousSMul Units.continuous_val rfl

Depends on / 依赖: IsInducing, IsInducing.id.continuousSMul, Units.continuous_val, continuousSMul, continuous_val
-/
instance Units.continuousSMul : ContinuousSMul Mˣ X :=
  IsInducing.id.continuousSMul Units.continuous_val rfl

/-- If an action is continuous, then composing this action with a continuous homomorphism gives
again a continuous action. -/
@[to_additive]
/--
theorem `MulAction.continuousSMul_compHom` / 定理 `MulAction.continuousSMul_compHom`

English:
theorem MulAction.continuousSMul_compHom
  proof: MulAction.compHom _ f
    ContinuousSMul N X := by
  let _ : MulAction N X := MulAction.compHom _ f
  exact ⟨(hf.comp continuous_fst).smul continuous_snd⟩

@[to_additive]

中文:
定理 乘法作用.continuousSMul_compHom
  证明: MulAction.compHom _ f
    ContinuousSMul N X := by
  let _ : MulAction N X := MulAction.compHom _ f
  exact ⟨(hf.comp continuous_fst).smul continuous_snd⟩

@[to_additive]

Depends on / 依赖: MulAction, MulAction.compHom, compHom
-/
theorem MulAction.continuousSMul_compHom
    {N : Type*} [TopologicalSpace N] [Monoid N] {f : N ->* M} (hf : Continuous f) :
    letI : MulAction N X := MulAction.compHom _ f
    ContinuousSMul N X := by
  let _ : MulAction N X := MulAction.compHom _ f
  exact ⟨(hf.comp continuous_fst).smul continuous_snd⟩

@[to_additive]
/--
Instance `Submonoid.continuousSMul` / 实例 `Submonoid.continuousSMul`

English:
instance Submonoid.continuousSMul
  signature: {S : Submonoid M}
  body: IsInducing.id.continuousSMul continuous_subtype_val rfl

中文:
实例 子幺半群.continuousSMul
  签名: {S : 子幺半群 M}
  定义体: IsInducing.id.continuousSMul continuous_subtype_val rfl

Depends on / 依赖: IsInducing, IsInducing.id.continuousSMul, continuousSMul, continuous_subtype_val
-/
instance Submonoid.continuousSMul {S : Submonoid M} : ContinuousSMul S X :=
  IsInducing.id.continuousSMul continuous_subtype_val rfl

end Monoid

section Group

variable [Group M] [MulAction M X] [ContinuousSMul M X]

@[to_additive]
/--
Instance `Subgroup.continuousSMul` / 实例 `Subgroup.continuousSMul`

English:
instance Subgroup.continuousSMul
  signature: {S : Subgroup M}
  body: S.toSubmonoid.continuousSMul

中文:
实例 子群.continuousSMul
  签名: {S : 子群 M}
  定义体: S.toSubmonoid.continuousSMul

Depends on / 依赖: S.toSubmonoid.continuousSMul, continuousSMul, toSubmonoid
-/
instance Subgroup.continuousSMul {S : Subgroup M} : ContinuousSMul S X :=
  S.toSubmonoid.continuousSMul

variable (M)

/--
lemma `stabilizer_isOpen` / 引理 `stabilizer_isOpen`

English:
lemma stabilizer_isOpen
  given: [DiscreteTopology X] (x : X)
  statement: IsOpen (MulAction.stabilizer M x : Set M)
  proof: IsOpen.preimage (f := fun g => g • x) (by fun_prop) (isOpen_discrete {x})

中文:
引理 stabilizer_isOpen
  条件: [离散拓扑 X] (x : X)
  结论: 是开集 (乘法作用.stabilizer M x : 集合 M)
  证明: IsOpen.preimage (f := fun g => g • x) (by fun_prop) (isOpen_discrete {x})

Depends on / 依赖: IsOpen, IsOpen.preimage, fun_prop, isOpen_discrete, preimage
-/
lemma stabilizer_isOpen [DiscreteTopology X] (x : X) : IsOpen (MulAction.stabilizer M x : Set M) :=
  IsOpen.preimage (f := fun g => g • x) (by fun_prop) (isOpen_discrete {x})

end Group

section IsTopologicalGroup

variable [Group M] [IsTopologicalGroup M] [MulAction M X]

/--
theorem `continuousSMul_iff_stabilizer_isOpen` / 定理 `continuousSMul_iff_stabilizer_isOpen`

English:
theorem continuousSMul_iff_stabilizer_isOpen
  given: [DiscreteTopology X]
  proof: by
  refine ⟨fun _ _ => stabilizer_isOpen .., fun h => ⟨?_⟩⟩
  rw [continuous_prod_of_discrete_right]
  intro y
  rw [continuous_discrete_rng]
  intro x
  let U := {m' : M | m' • y = x}
  have hU : IsOpen U := by
    by_cases hU' : U != ∅
    · obtain ⟨m, (hm : m • y = x)⟩ := Set.nonempty_iff_empty_ne.mpr hU'.symm
      convert! (h x).preimage (by fun_prop : Continuous fun m' : M => m' * m⁻¹)
      ext; simp [← smul_smul, U, eq_inv_smul_iff.mpr hm]
    simp_all
  simpa using! hU

中文:
定理 continuousSMul_iff_stabilizer_isOpen
  条件: [离散拓扑 X]
  证明: by
  refine ⟨fun _ _ => stabilizer_isOpen .., fun h => ⟨?_⟩⟩
  rw [continuous_prod_of_discrete_right]
  intro y
  rw [continuous_discrete_rng]
  intro x
  let U := {m' : M | m' • y = x}
  have hU : IsOpen U := by
    by_cases hU' : U != ∅
    · obtain ⟨m, (hm : m • y = x)⟩ := Set.nonempty_iff_empty_ne.mpr hU'.symm
      convert! (h x).preimage (by fun_prop : Continuous fun m' : M => m' * m⁻¹)
      ext; simp [← smul_smul, U, eq_inv_smul_iff.mpr hm]
    simp_all
  simpa using! hU

Depends on / 依赖: Continuous, IsOpen, Set.nonempty_iff_empty_ne.mpr, continuous_discrete_rng, continuous_prod_of_discrete_right, convert, eq_inv_smul_iff, eq_inv_smul_iff.mpr, fun_prop, nonempty_iff_empty_ne, preimage, smul_smul, stabilizer_isOpen
-/
theorem continuousSMul_iff_stabilizer_isOpen [DiscreteTopology X] :
    ContinuousSMul M X ↔ forall x : X, IsOpen (MulAction.stabilizer M x : Set M) := by
  refine ⟨fun _ _ => stabilizer_isOpen .., fun h => ⟨?_⟩⟩
  rw [continuous_prod_of_discrete_right]
  intro y
  rw [continuous_discrete_rng]
  intro x
  let U := {m' : M | m' • y = x}
  have hU : IsOpen U := by
    by_cases hU' : U != ∅
    · obtain ⟨m, (hm : m • y = x)⟩ := Set.nonempty_iff_empty_ne.mpr hU'.symm
      convert! (h x).preimage (by fun_prop : Continuous fun m' : M => m' * m⁻¹)
      ext; simp [← smul_smul, U, eq_inv_smul_iff.mpr hm]
    simp_all
  simpa using! hU

end IsTopologicalGroup

section GroupWithZero

variable {G₀ X : Type*} [GroupWithZero G₀] [Zero X] [MulActionWithZero G₀ X]
  [TopologicalSpace G₀] [(𝓝[!=] (0 : G₀)).NeBot] [TopologicalSpace X] [ContinuousSMul G₀ X]

/--
theorem `Set.univ_smul_nhds_zero` / 定理 `Set.univ_smul_nhds_zero`

English:
theorem Set.univ_smul_nhds_zero
  given: {s : Set X} (hs : s in 𝓝 0)
  statement: (univ : Set G₀) • s = Set.univ
  proof: by
  refine Set.eq_univ_of_forall fun x => ?_
  have : Tendsto (· • x) (𝓝 (0 : G₀)) (𝓝 0) :=
    zero_smul G₀ x ▸ tendsto_id.smul tendsto_const_nhds
  rcases Filter.nonempty_of_mem (inter_mem_nhdsWithin {0}ᶜ <| mem_map.1 <| this hs)
    with ⟨c, hc₀, hc⟩
  simp only [mem_compl_iff, mem_singleton_iff] at hc₀
  simp only [mem_smul, mem_univ, true_and]
  exact ⟨c⁻¹, c • x, hc, inv_smul_smul₀ hc₀ _⟩

@[simp]

中文:
定理 集合.univ_smul_nhds_zero
  条件: {s : 集合 X} (hs : s in 𝓝 0)
  结论: (univ : 集合 G₀) • s = 集合.univ
  证明: by
  refine Set.eq_univ_of_forall fun x => ?_
  have : Tendsto (· • x) (𝓝 (0 : G₀)) (𝓝 0) :=
    zero_smul G₀ x ▸ tendsto_id.smul tendsto_const_nhds
  rcases Filter.nonempty_of_mem (inter_mem_nhdsWithin {0}ᶜ <| mem_map.1 <| this hs)
    with ⟨c, hc₀, hc⟩
  simp only [mem_compl_iff, mem_singleton_iff] at hc₀
  simp only [mem_smul, mem_univ, true_and]
  exact ⟨c⁻¹, c • x, hc, inv_smul_smul₀ hc₀ _⟩

@[simp]

Depends on / 依赖: Filter, Filter.nonempty_of_mem, Set.eq_univ_of_forall, Tendsto, eq_univ_of_forall, inter_mem_nhdsWithin, mem_compl_iff, mem_map, mem_singleton_iff, mem_smul, mem_univ, nonempty_of_mem, tendsto_const_nhds, tendsto_id, tendsto_id.smul, true_and, zero_smul
-/
theorem Set.univ_smul_nhds_zero {s : Set X} (hs : s in 𝓝 0) : (univ : Set G₀) • s = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  have : Tendsto (· • x) (𝓝 (0 : G₀)) (𝓝 0) :=
    zero_smul G₀ x ▸ tendsto_id.smul tendsto_const_nhds
  rcases Filter.nonempty_of_mem (inter_mem_nhdsWithin {0}ᶜ <| mem_map.1 <| this hs)
    with ⟨c, hc₀, hc⟩
  simp only [mem_compl_iff, mem_singleton_iff] at hc₀
  simp only [mem_smul, mem_univ, true_and]
  exact ⟨c⁻¹, c • x, hc, inv_smul_smul₀ hc₀ _⟩

@[simp]
/--
theorem `Filter.top_smul_nhds_zero` / 定理 `Filter.top_smul_nhds_zero`

English:
theorem Filter.top_smul_nhds_zero
  statement: (⊤ : Filter G₀) • 𝓝 (0 : X) = ⊤
  proof: by
  rw [(hasBasis_top.smul (basis_sets _)).eq_top_iff]
  rintro ⟨_, s⟩ ⟨-, hs⟩
  exact Set.univ_smul_nhds_zero hs

中文:
定理 滤子.top_smul_nhds_zero
  结论: (⊤ : 滤子 G₀) • 𝓝 (0 : X) = ⊤
  证明: by
  rw [(hasBasis_top.smul (basis_sets _)).eq_top_iff]
  rintro ⟨_, s⟩ ⟨-, hs⟩
  exact Set.univ_smul_nhds_zero hs

Depends on / 依赖: Set.univ_smul_nhds_zero, basis_sets, eq_top_iff, hasBasis_top, hasBasis_top.smul, univ_smul_nhds_zero
-/
theorem Filter.top_smul_nhds_zero : (⊤ : Filter G₀) • 𝓝 (0 : X) = ⊤ := by
  rw [(hasBasis_top.smul (basis_sets _)).eq_top_iff]
  rintro ⟨_, s⟩ ⟨-, hs⟩
  exact Set.univ_smul_nhds_zero hs

end GroupWithZero

@[to_additive]
/--
Instance `Prod.continuousSMul` / 实例 `Prod.continuousSMul`

English:
instance Prod.continuousSMul
  signature: [SMul M X] [SMul M Y] [ContinuousSMul M X] [ContinuousSMul M Y]
  body: ⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩

@[to_additive]

中文:
实例 积类型.continuousSMul
  签名: [标量乘法 M X] [标量乘法 M Y] [连续标量乘法 M X] [连续标量乘法 M Y]
  定义体: ⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩

@[to_additive]

Depends on / 依赖: continuous_fst, continuous_fst.comp, continuous_fst.smul, continuous_snd, continuous_snd.comp, prodMk
-/
instance Prod.continuousSMul [SMul M X] [SMul M Y] [ContinuousSMul M X] [ContinuousSMul M Y] :
    ContinuousSMul M (X × Y) :=
  ⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩

@[to_additive]
instance {ι : Type*} {γ : ι -> Type*} [forall i, TopologicalSpace (γ i)] [forall i, SMul M (γ i)]
    [forall i, ContinuousSMul M (γ i)] : ContinuousSMul M (forall i, γ i) :=
  ⟨continuous_pi fun i =>
(continuous_fst.smul continuous_snd).comp
        continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)⟩

@[to_additive]
instance {ι : Type*} {γ : ι -> Type*} [Π i, TopologicalSpace (γ i)]
    {N : ι -> Type*} [Π i, TopologicalSpace (N i)] [Π i, SMul (N i) (γ i)]
    [forall i, ContinuousSMul (N i) (γ i)] : ContinuousSMul (Π i, N i) (Π i, γ i) :=
  ⟨continuous_pi fun i => ((continuous_apply i).comp continuous_id'.fst).smul
    ((continuous_apply i).comp continuous_id'.snd)⟩

end Main

section LatticeOps

variable {ι : Sort*} {M X : Type*} [TopologicalSpace M] [SMul M X]

@[to_additive]
/--
theorem `continuousSMul_sInf` / 定理 `continuousSMul_sInf`

English:
theorem continuousSMul_sInf
  statement: {ts : Set (TopologicalSpace X)}
  proof: let _ := sInf ts
  { continuous_smul := by
      -- Porting note: needs `( :)`
      rw [← (sInf_singleton (a := ‹TopologicalSpace M›) :)]
      exact
        continuous_sInf_rng.2 fun t ht =>
          continuous_sInf_dom₂ (Eq.refl _) ht
            (@ContinuousSMul.continuous_smul _ _ _ _ t (h t ht)) }

@[to_additive]

中文:
定理 continuousSMul_sInf
  结论: {ts : 集合 (拓扑空间 X)}
  证明: let _ := sInf ts
  { continuous_smul := by
      -- Porting note: needs `( :)`
      rw [← (sInf_singleton (a := ‹TopologicalSpace M›) :)]
      exact
        continuous_sInf_rng.2 fun t ht =>
          continuous_sInf_dom₂ (Eq.refl _) ht
            (@ContinuousSMul.continuous_smul _ _ _ _ t (h t ht)) }

@[to_additive]

Depends on / 依赖: continuous_smul
-/
theorem continuousSMul_sInf {ts : Set (TopologicalSpace X)}
    (h : forall t in ts, @ContinuousSMul M X _ _ t) : @ContinuousSMul M X _ _ (sInf ts) :=
  let _ := sInf ts
  { continuous_smul := by
      -- Porting note: needs `( :)`
      rw [← (sInf_singleton (a := ‹TopologicalSpace M›) :)]
      exact
        continuous_sInf_rng.2 fun t ht =>
          continuous_sInf_dom₂ (Eq.refl _) ht
            (@ContinuousSMul.continuous_smul _ _ _ _ t (h t ht)) }

@[to_additive]
/--
theorem `continuousSMul_iInf` / 定理 `continuousSMul_iInf`

English:
theorem continuousSMul_iInf
  statement: {ts' : ι -> TopologicalSpace X}
  proof: continuousSMul_sInf Set.forall_mem_range.mpr h

中文:
定理 continuousSMul_iInf
  结论: {ts' : ι -> 拓扑空间 X}
  证明: continuousSMul_sInf Set.forall_mem_range.mpr h

Depends on / 依赖: Set.forall_mem_range.mpr, continuousSMul_sInf, forall_mem_range
-/
theorem continuousSMul_iInf {ts' : ι -> TopologicalSpace X}
    (h : forall i, @ContinuousSMul M X _ _ (ts' i)) : @ContinuousSMul M X _ _ (⨅ i, ts' i) :=
continuousSMul_sInf Set.forall_mem_range.mpr h

set_option linter.overlappingInstances false in
@[to_additive]
/--
theorem `continuousSMul_inf` / 定理 `continuousSMul_inf`

English:
theorem continuousSMul_inf
  statement: {t₁ t₂ : TopologicalSpace X} [@ContinuousSMul M X _ _ t₁]
  proof: by
  rw [inf_eq_iInf]
  refine continuousSMul_iInf fun b => ?_
  cases b <;> assumption

中文:
定理 continuousSMul_inf
  结论: {t₁ t₂ : 拓扑空间 X} [@连续标量乘法 M X _ _ t₁]
  证明: by
  rw [inf_eq_iInf]
  refine continuousSMul_iInf fun b => ?_
  cases b <;> assumption

Depends on / 依赖: continuousSMul_iInf, inf_eq_iInf
-/
theorem continuousSMul_inf {t₁ t₂ : TopologicalSpace X} [@ContinuousSMul M X _ _ t₁]
    [@ContinuousSMul M X _ _ t₂] : @ContinuousSMul M X _ _ (t₁ ⊓ t₂) := by
  rw [inf_eq_iInf]
  refine continuousSMul_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps

section AddTorsor

variable (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P] [TopologicalSpace G]
variable [PreconnectedSpace G] [TopologicalSpace P] [ContinuousVAdd G P]

include G in
/--
theorem `AddTorsor.connectedSpace` / 定理 `AddTorsor.connectedSpace`

English:
theorem AddTorsor.connectedSpace
  statement: ConnectedSpace P
  proof: { isPreconnected_univ := by
      convert!
        isPreconnected_univ.image (Equiv.vaddConst (Classical.arbitrary P) : G -> P)
          (continuous_id.vadd continuous_const).continuousOn
      rw [Set.image_univ]; rw [Equiv.range_eq_univ]
    toNonempty := inferInstance }

中文:
定理 加法Torsor.connectedSpace
  结论: 连通空间 P
  证明: { isPreconnected_univ := by
      convert!
        isPreconnected_univ.image (Equiv.vaddConst (Classical.arbitrary P) : G -> P)
          (continuous_id.vadd continuous_const).continuousOn
      rw [Set.image_univ]; rw [Equiv.range_eq_univ]
    toNonempty := inferInstance }
-/
protected theorem AddTorsor.connectedSpace : ConnectedSpace P :=
  { isPreconnected_univ := by
      convert!
        isPreconnected_univ.image (Equiv.vaddConst (Classical.arbitrary P) : G -> P)
          (continuous_id.vadd continuous_const).continuousOn
      rw [Set.image_univ]; rw [Equiv.range_eq_univ]
    toNonempty := inferInstance }

end AddTorsor
