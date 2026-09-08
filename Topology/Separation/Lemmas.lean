/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving, Bryan Wang, Oliver Nash
-/
module

public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Separation.Profinite

/-!
# Further separation lemmas
-/

public section

variable {X : Type*}

namespace CompletelyRegularSpace

variable [TopologicalSpace X] [T35Space X]

/-
**CompletelyRegularSpace.totallySeparatedSpace_of_cardinalMk_lt_continuum** 是 Ma
thlib 中的一个定理，位于命名空间 `CompletelyRegularSpace`。
形式化陈述：totallySeparatedSpace_of_cardinalMk_lt_continuum (h : Cardinal.mk X < Card
inal.continuum) : TotallySeparatedSpace X
参数：h : Cardinal.mk X < Cardinal.continuum。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `totallySeparatedSpace_of_t0_of_basis_clopen`：totallySeparatedSpace_of_t0
_of_basis_clopen [T0Space X] (h : IsTopologicalBasis { s : Set X | IsClopen s })
 : TotallySeparatedSpace X
· 使用定理 `T35Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T
35Space X], T0Space X
· 使用定理 `CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_conti
nuum`：CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continu
um [CompletelyRegularSpace X] (hX : Cardinal.mk X < continuum) : I…
· 使用定理 `T35Space.toCompletelyRegularSpace`：∀ {X : Type u} {inst : TopologicalSpa
ce X} [self : T35Space X], CompletelyRegularSpace X
-/
theorem totallySeparatedSpace_of_cardinalMk_lt_continuum (h : Cardinal.mk X < Cardinal.continuum) :
    TotallySeparatedSpace X :=
  totallySeparatedSpace_of_t0_of_basis_clopen <|
    CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continuum h
/-
**CompletelyRegularSpace.** 是 Mathlib 中的一个实例，位于命名空间 `CompletelyRegularSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Countable X] : TotallySeparatedSpace X :=
  totallySeparatedSpace_of_cardinalMk_lt_continuum <|
    (Cardinal.mk_le_aleph0_iff.mpr inferInstance).trans_lt Cardinal.aleph0_lt_continuum
/-
**CompletelyRegularSpace._root_.Set.Countable.totallySeparatedSpace** 是 Mathlib 
中的一个引理，位于命名空间 `CompletelyRegularSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.Set.Countable.totallySeparatedSpace {s : Set X} (h : s.Countable) :
    TotallySeparatedSpace s :=
  have : _root_.Countable s := h
  inferInstanceAs (TotallySeparatedSpace s)

end CompletelyRegularSpace

/-- Countable subsets of metric spaces are totally disconnected. -/
/-
**Set.Countable.isTotallyDisconnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Countable.isTotallyDisconnected [MetricSpace X] {s : Set X} (hs : s.Co
untable) : IsTotallyDisconnected s
参数：hs : s.Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `totallyDisconnectedSpace_subtype_iff`：totallyDisconnectedSpace_subtype_i
ff {s : Set α} : TotallyDisconnectedSpace s ↔ IsTotallyDisconnected s
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `CompletelyRegularSpace.instTotallySeparatedSpaceOfCountable`：∀ {X : Type
 u_1} [inst : TopologicalSpace X] [T35Space X] [Countable X], TotallySeparatedSp
ace X
· 使用定理 `instT35SpaceSubtype`：∀ {X : Type u} [inst : TopologicalSpace X] {p : X →
 Prop} [T35Space X], T35Space (Subtype p)
· 使用定理 `T4Space.instT35Space`：∀ {X : Type u} [inst : TopologicalSpace X] [T4Spac
e X], T35Space X
· 使用定理 `instT4SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T4Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α

--- 原说明 ---
Countable subsets of metric spaces are totally disconnected.
-/
theorem Set.Countable.isTotallyDisconnected [MetricSpace X] {s : Set X} (hs : s.Countable) :
    IsTotallyDisconnected s := by
  rw [← totallyDisconnectedSpace_subtype_iff]
  have : Countable s := hs
  infer_instance
