/-
Copyright (c) 2025 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Panagiotis Angelinos
-/
module

public import Mathlib.Topology.Sober
public import Mathlib.Topology.Spectral.Prespectral

/-!
# Spectral spaces

A topological space is spectral if it is T0, compact, sober, quasi-separated, and its compact open
subsets form an open basis. Prime spectra of commutative semirings are spectral spaces.

## Main Results

- `SpectralSpace` : Predicate for a topological space to be spectral.
- `Topology.IsOpenEmbedding.spectralSpace` : a compact open subspace of a spectral space is spectral

## References

See [stacks-project], tag 08YF for details.
-/

public section

open Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/--
A topological space is spectral if it is T0, compact, sober, quasi-separated, and its compact open
subsets form an open basis.
-/
@[stacks 08YG]
/-
**SpectralSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_3) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is spectral if it is T0, compact, sober, quasi-separated, an
d its compact open
subsets form an open basis.
-/
class SpectralSpace (X : Type*) [TopologicalSpace X] : Prop extends
  T0Space X, CompactSpace X, QuasiSober X, QuasiSeparatedSpace X, PrespectralSpace X
/-
**Topology.IsOpenEmbedding.spectralSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.spectralSpace [SpectralSpace Y] [CompactSpace X] 
(hf : IsOpenEmbedding f) : SpectralSpace X where __
参数：hf : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.quasiSober`：Topology.IsOpenEmbedding.quasiSober
 {f : α -> β} (hf : IsOpenEmbedding f) [QuasiSober β] : QuasiSober α where sober
 hS hS'
· 使用定理 `SpectralSpace.toQuasiSober`：∀ {X : Type u_3} {inst : TopologicalSpace X}
 [self : SpectralSpace X], QuasiSober X
· 使用引理 `Topology.IsOpenEmbedding.prespectralSpace`：Topology.IsOpenEmbedding.pres
pectralSpace [PrespectralSpace Y] {f : X -> Y} (hf : IsOpenEmbedding f) : Prespe
ctralSpace X where isTopologica…
· 使用定理 `SpectralSpace.toPrespectralSpace`：∀ {X : Type u_3} {inst : TopologicalSp
ace X} [self : SpectralSpace X], PrespectralSpace X
· 使用引理 `Topology.IsOpenEmbedding.quasiSeparatedSpace`：Topology.IsOpenEmbedding.q
uasiSeparatedSpace [QuasiSeparatedSpace β] (h : IsOpenEmbedding f) : QuasiSepara
tedSpace α
· 使用定理 `SpectralSpace.toQuasiSeparatedSpace`：∀ {X : Type u_3} {inst : Topologica
lSpace X} [self : SpectralSpace X], QuasiSeparatedSpace X
· 使用定理 `Topology.IsEmbedding.t0Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用定理 `SpectralSpace.toT0Space`：∀ {X : Type u_3} {inst : TopologicalSpace X} [s
elf : SpectralSpace X], T0Space X
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
-/
theorem Topology.IsOpenEmbedding.spectralSpace
    [SpectralSpace Y] [CompactSpace X] (hf : IsOpenEmbedding f) :
    SpectralSpace X where
  __ := hf.quasiSober
  __ := hf.prespectralSpace
  __ := hf.quasiSeparatedSpace
  __ := hf.isEmbedding.t0Space
