/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Short exact sequences of topological groups

In this file, we define a short exact sequence of topological groups to be a closed embedding `φ`
followed by an open quotient map `ψ` satisfying `φ.range = ψ.ker`.

## Main definitions

* `TopologicalGroup.IsSES φ ψ`: A predicate stating that `φ` is a closed embedding, `ψ` is an open
  quotient map, and `φ.range = ψ.ker`.

-/

public section

open scoped Pointwise

/-- A predicate stating that `φ` and `ψ` define a short exact sequence of topological groups. -/
/-
**TopologicalGroup.IsSES** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopologicalGroup`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {C : Type u_3} →       [inst : Gro
up A] →         [inst_1 : Group B] →           [inst_2 : Group C] →             
[TopologicalSpace A] → [TopologicalSpace B] → [TopologicalSpace C] → (A →* B) → 
(B →* C) → Prop
参数：A →* B；B →* C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate stating that `φ` and `ψ` define a short exact sequence of topologica
l groups.
-/
structure TopologicalGroup.IsSES {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] (φ : A →* B) (ψ : B →* C) where
  isClosedEmbedding : Topology.IsClosedEmbedding φ
  isOpenQuotientMap : IsOpenQuotientMap ψ
  mulExact : Function.MulExact φ ψ

/-- A predicate stating that `φ` and `ψ` define a short exact sequence of topological groups. -/
/-
**TopologicalAddGroup.IsSES** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopologicalAddGroup`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {C : Type u_3} →       [inst : Add
Group A] →         [inst_1 : AddGroup B] →           [inst_2 : AddGroup C] →    
         [TopologicalSpace A] → [TopologicalSpace B] → [TopologicalSpace C] → (A
 →+ B) → (B →+ C) → Prop
参数：A →+ B；B →+ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate stating that `φ` and `ψ` define a short exact sequence of topologica
l groups.
-/
structure TopologicalAddGroup.IsSES {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] (φ : A →+ B) (ψ : B →+ C) where
  isClosedEmbedding : Topology.IsClosedEmbedding φ
  isOpenQuotientMap : IsOpenQuotientMap ψ
  exact : Function.Exact φ ψ

attribute [to_additive TopologicalAddGroup.IsSES] TopologicalGroup.IsSES

namespace TopologicalGroup.IsSES

/-- Construct a short exact sequence of topological groups from a closed normal subgroup. -/
@[to_additive /-- Construct a short exact sequence of topological groups from a
closed normal subgroup. -/]
/-
**TopologicalGroup.IsSES.ofClosedSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Group.IsSES`。
形式化陈述：ofClosedSubgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopological
Group G] (H : Subgroup G) [H.Normal] (hH : IsClosed (H : Set G)) : TopologicalGr
oup.IsSES H.subtype (QuotientGroup.mk' H) where isClosedEmbedding
参数：H : Subgroup G；hH : IsClosed (H : Set G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `MulAction.isOpenQuotientMap_quotientMk`：MulAction.isOpenQuotientMap_quot
ientMk [ContinuousConstSMul Γ T] : IsOpenQuotientMap (Quotient.mk (MulAction.orb
itRel Γ T))
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem ofClosedSubgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [H.Normal] (hH : IsClosed (H : Set G)) :
    TopologicalGroup.IsSES H.subtype (QuotientGroup.mk' H) where
  isClosedEmbedding := ⟨⟨Topology.IsInducing.subtypeVal, H.subtype_injective⟩, by simpa⟩
  isOpenQuotientMap := MulAction.isOpenQuotientMap_quotientMk
  mulExact := by simp [Function.MulExact]

end TopologicalGroup.IsSES

