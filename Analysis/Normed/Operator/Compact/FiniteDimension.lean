/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Bhavik Mehta, Thomas Browning
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Compact operators and finite dimensional spaces

This file contains results linking `IsCompactOperator` with `FiniteDimensional`.

The motivation for not including this in the same file as the definition of compact operators
is that `Mathlib.Topology.Algebra.Module.FiniteDimension` is quite a heavy import to add there.
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-
**isCompactOperator_id_iff_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompactOperator_id_iff_finiteDimensional [LocallyCompactSpace 𝕜] : IsCom
pactOperator (_root_.id : E -> E) ↔ FiniteDimensional 𝕜 E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isCompactOperator_id_iff_locallyCompactSpace`：isCompactOperator_id_iff_l
ocallyCompactSpace {E : Type*} [AddGroup E] [TopologicalSpace E] [IsTopologicalA
ddGroup E] : IsCompactOperator (id…
· 使用定理 `FiniteDimensional.of_locallyCompactSpace`：FiniteDimensional.of_locallyCo
mpactSpace [WeaklyLocallyCompactSpace E] : FiniteDimensional 𝕜 E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `LocallyCompactSpace.of_finiteDimensional_of_complete`：LocallyCompactSpac
e.of_finiteDimensional_of_complete (K V : Type*) [NontriviallyNormedField K] [Co
mpleteSpace K] [LocallyCompactSpace K] [Ad…
-/
theorem isCompactOperator_id_iff_finiteDimensional [LocallyCompactSpace 𝕜] :
    IsCompactOperator (_root_.id : E → E) ↔ FiniteDimensional 𝕜 E :=
  isCompactOperator_id_iff_locallyCompactSpace.trans
    ⟨fun _ ↦ .of_locallyCompactSpace 𝕜, fun _ ↦ .of_finiteDimensional_of_complete 𝕜 E⟩

/-- If the identity operator of a Banach space over a nontrivially normed field is compact,
then the space is finite dimensional. -/
/-
**FiniteDimensional.of_isCompactOperator_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FiniteDimensional.of_isCompactOperator_id (h : IsCompactOperator (id : E -
> E)) : FiniteDimensional 𝕜 E
参数：h : IsCompactOperator (id : E -> E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyCompactSpace.of_isCompactOperator_id`：∀ {E : Type u_1} [inst : Ad
dGroup E] [inst_1 : TopologicalSpace E] [IsTopologicalAddGroup E],   IsCompactOp
erator id → LocallyCompactSpace E
· 使用定理 `FiniteDimensional.of_locallyCompactSpace`：FiniteDimensional.of_locallyCo
mpactSpace [WeaklyLocallyCompactSpace E] : FiniteDimensional 𝕜 E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X

--- 原说明 ---
If the identity operator of a Banach space over a nontrivially normed field is c
ompact,
then the space is finite dimensional.
-/
lemma FiniteDimensional.of_isCompactOperator_id (h : IsCompactOperator (id : E → E)) :
    FiniteDimensional 𝕜 E := by
  have := LocallyCompactSpace.of_isCompactOperator_id h
  exact FiniteDimensional.of_locallyCompactSpace 𝕜

@[deprecated (since := "2026-03-05")] alias IsCompactOperator.finiteDimensional :=
  FiniteDimensional.of_isCompactOperator_id
