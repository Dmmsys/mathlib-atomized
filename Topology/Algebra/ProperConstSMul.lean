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

/--
Definition of `ProperConstVAdd` / `ProperConstVAdd` 的定义

English:
class ProperConstVAdd
  parameters: (M X : Type*) [VAdd M X] [TopologicalSpace X]
  axioms and operations (1):
    - isProperMap_vadd((c : M)) : IsProperMap ((c +ᵥ ·) : X -> X)

中文:
类 正常数向量加法
  参数: (M X : 类型) [向量加法 M X] [拓扑空间 X]
  公理与运算 (1 个):
    - isProperMap_vadd((c : M)) : 是真映射 ((c +ᵥ ·) : X -> X)
-/
class ProperConstVAdd (M X : Type*) [VAdd M X] [TopologicalSpace X] : Prop where
  /-- `(c +ᵥ ·)` is a proper map. -/
  isProperMap_vadd (c : M) : IsProperMap ((c +ᵥ ·) : X -> X)

/-- A mixin typeclass saying that `(c • ·)` is a proper map for all `c`.

Note that this is **not** the same as a proper multiplicative action (not yet in `Mathlib`). -/
@[to_additive]
/--
Definition of `ProperConstSMul` / `ProperConstSMul` 的定义

English:
class ProperConstSMul
  parameters: (M X : Type*) [SMul M X] [TopologicalSpace X]
  axioms and operations (1):
    - isProperMap_smul((c : M)) : IsProperMap ((c • ·) : X -> X)

中文:
类 正常数标量乘法
  参数: (M X : 类型) [标量乘法 M X] [拓扑空间 X]
  公理与运算 (1 个):
    - isProperMap_smul((c : M)) : 是真映射 ((c • ·) : X -> X)
-/
class ProperConstSMul (M X : Type*) [SMul M X] [TopologicalSpace X] : Prop where
  /-- `(c • ·)` is a proper map. -/
  isProperMap_smul (c : M) : IsProperMap ((c • ·) : X -> X)

/-- `(c • ·)` is a proper map. -/
@[to_additive /-- `(c +ᵥ ·)` is a proper map. -/]
/--
theorem `isProperMap_smul` / 定理 `isProperMap_smul`

English:
theorem isProperMap_smul
  statement: {M : Type*} (c : M) (X : Type*) [SMul M X] [TopologicalSpace X]
  proof: h.1 c

中文:
定理 isProperMap_smul
  结论: {M : 类型} (c : M) (X : 类型) [标量乘法 M X] [拓扑空间 X]
  证明: h.1 c
-/
theorem isProperMap_smul {M : Type*} (c : M) (X : Type*) [SMul M X] [TopologicalSpace X]
    [h : ProperConstSMul M X] : IsProperMap ((c • ·) : X -> X) := h.1 c

/-- The preimage of a compact set under `(c • ·)` is a compact set. -/
@[to_additive /-- The preimage of a compact set under `(c +ᵥ ·)` is a compact set. -/]
/--
theorem `IsCompact.preimage_smul` / 定理 `IsCompact.preimage_smul`

English:
theorem IsCompact.preimage_smul
  statement: {M X : Type*} [SMul M X] [TopologicalSpace X]
  proof: (isProperMap_smul c X).isCompact_preimage hs

@[to_additive]

中文:
定理 是紧集.preimage_smul
  结论: {M X : 类型} [标量乘法 M X] [拓扑空间 X]
  证明: (isProperMap_smul c X).isCompact_preimage hs

@[to_additive]

Depends on / 依赖: isCompact_preimage, isProperMap_smul
-/
theorem IsCompact.preimage_smul {M X : Type*} [SMul M X] [TopologicalSpace X]
    [ProperConstSMul M X] {s : Set X} (hs : IsCompact s) (c : M) : IsCompact ((c • ·) ⁻¹' s) :=
  (isProperMap_smul c X).isCompact_preimage hs

@[to_additive]
instance (priority := 100) {M X : Type*} [SMul M X] [TopologicalSpace X] [ContinuousConstSMul M X]
    [T2Space X] [CompactSpace X] : ProperConstSMul M X :=
  ⟨fun c => (continuous_const_smul c).isProperMap⟩

@[to_additive]
instance (priority := 100) {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]
    [ContinuousConstSMul G X] : ProperConstSMul G X :=
  ⟨fun c => (Homeomorph.smul c).isProperMap⟩

instance {M X Y : Type*}
    [SMul M X] [TopologicalSpace X] [ProperConstSMul M X]
    [SMul M Y] [TopologicalSpace Y] [ProperConstSMul M Y] :
    ProperConstSMul M (X × Y) :=
  ⟨fun c => (isProperMap_smul c X).prodMap (isProperMap_smul c Y)⟩

instance {M ι : Type*} {X : ι -> Type*}
    [forall i, SMul M (X i)] [forall i, TopologicalSpace (X i)] [forall i, ProperConstSMul M (X i)] :
    ProperConstSMul M (forall i, X i) :=
  ⟨fun c => .pi_map fun i => isProperMap_smul c (X i)⟩
