/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Maps.Proper.Basic
/-!
# Actions by proper maps

In this file we define `ProperConstSMul M X` to be a mixin `Prop`-value class
stating that `(c • ·)` is a proper map for all `c`.

Note that this is **not** the same as a proper action (not yet in `Mathlib`)
which requires `(c, x) ↦ (c • x, x)` to be a proper map.

We also provide 4 instances:
- for a continuous action on a compact Hausdorff space,
- and for a continuous group action on a general space;
- for the action on `X × Y`;
- for the action on `∀ i, X i`.
-/

public section

/-- A mixin typeclass saying that the `(c +ᵥ ·)` is a proper map for all `c`.

Note that this is **not** the same as a proper additive action (not yet in `Mathlib`). -/
/-
**ProperConstVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → (X : Type u_2) → [VAdd M X] → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mixin typeclass saying that the `(c +ᵥ ·)` is a proper map for all `c`.

Note that this is **not** the same as a proper additive action (not yet in `Math
lib`).
-/
class ProperConstVAdd (M X : Type*) [VAdd M X] [TopologicalSpace X] : Prop where
  /-- `(c +ᵥ ·)` is a proper map. -/
  isProperMap_vadd (c : M) : IsProperMap ((c +ᵥ ·) : X → X)

/-- A mixin typeclass saying that `(c • ·)` is a proper map for all `c`.

Note that this is **not** the same as a proper multiplicative action (not yet in `Mathlib`). -/
@[to_additive]
/-
**ProperConstSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → (X : Type u_2) → [SMul M X] → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mixin typeclass saying that `(c • ·)` is a proper map for all `c`.

Note that this is **not** the same as a proper multiplicative action (not yet in
 `Mathlib`).
-/
class ProperConstSMul (M X : Type*) [SMul M X] [TopologicalSpace X] : Prop where
  /-- `(c • ·)` is a proper map. -/
  isProperMap_smul (c : M) : IsProperMap ((c • ·) : X → X)

/-- `(c • ·)` is a proper map. -/
@[to_additive /-- `(c +ᵥ ·)` is a proper map. -/]
/-
**isProperMap_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isProperMap_smul {M : Type*} (c : M) (X : Type*) [SMul M X] [TopologicalSp
ace X] [h : ProperConstSMul M X] : IsProperMap ((c • ·) : X -> X)
参数：c : M；X : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProperConstSMul.isProperMap_smul`：∀ {M : Type u_1} {X : Type u_2} {inst 
: SMul M X} {inst_1 : TopologicalSpace X} [self : ProperConstSMul M X] (c : M), 
  IsProperMap fun x =>…

--- 原说明 ---
`(c • ·)` is a proper map.
-/
theorem isProperMap_smul {M : Type*} (c : M) (X : Type*) [SMul M X] [TopologicalSpace X]
    [h : ProperConstSMul M X] : IsProperMap ((c • ·) : X → X) := h.1 c

/-- The preimage of a compact set under `(c • ·)` is a compact set. -/
@[to_additive /-- The preimage of a compact set under `(c +ᵥ ·)` is a compact set. -/]
/-
**IsCompact.preimage_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.preimage_smul {M X : Type*} [SMul M X] [TopologicalSpace X] [Pro
perConstSMul M X] {s : Set X} (hs : IsCompact s) (c : M) : IsCompact ((c • ·) ⁻¹
' s)
参数：hs : IsCompact s；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsProperMap.isCompact_preimage`：IsProperMap.isCompact_preimage (h : IsPr
operMap f) {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K)
· 使用定理 `isProperMap_smul`：isProperMap_smul {M : Type*} (c : M) (X : Type*) [SMul
 M X] [TopologicalSpace X] [h : ProperConstSMul M X] : IsProperMap ((c • ·) : X 
-> X)

--- 原说明 ---
The preimage of a compact set under `(c • ·)` is a compact set.
-/
theorem IsCompact.preimage_smul {M X : Type*} [SMul M X] [TopologicalSpace X]
    [ProperConstSMul M X] {s : Set X} (hs : IsCompact s) (c : M) : IsCompact ((c • ·) ⁻¹' s) :=
  (isProperMap_smul c X).isCompact_preimage hs

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {M X : Type*} [SMul M X] [TopologicalSpace X] [ContinuousConstSMul M X]
    [T2Space X] [CompactSpace X] : ProperConstSMul M X :=
  ⟨fun c ↦ (continuous_const_smul c).isProperMap⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]
    [ContinuousConstSMul G X] : ProperConstSMul G X :=
  ⟨fun c ↦ (Homeomorph.smul c).isProperMap⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M X Y : Type*}
    [SMul M X] [TopologicalSpace X] [ProperConstSMul M X]
    [SMul M Y] [TopologicalSpace Y] [ProperConstSMul M Y] :
    ProperConstSMul M (X × Y) :=
  ⟨fun c ↦ (isProperMap_smul c X).prodMap (isProperMap_smul c Y)⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M ι : Type*} {X : ι → Type*}
    [∀ i, SMul M (X i)] [∀ i, TopologicalSpace (X i)] [∀ i, ProperConstSMul M (X i)] :
    ProperConstSMul M (∀ i, X i) :=
  ⟨fun c ↦ .pi_map fun i ↦ isProperMap_smul c (X i)⟩
