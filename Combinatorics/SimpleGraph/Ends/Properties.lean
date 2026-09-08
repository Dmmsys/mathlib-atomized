/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
public import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Properties of the ends of graphs

This file is meant to contain results about the ends of (locally finite connected) graphs.

-/

public section


variable {V : Type} (G : SimpleGraph V)

namespace SimpleGraph

/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite V] : IsEmpty G.end where
  false := by
    rintro ⟨s, _⟩
    cases nonempty_fintype V
    obtain ⟨v, h⟩ := (s <| Opposite.op Finset.univ).nonempty
    exact Set.disjoint_iff.mp (s _).disjoint_right
        ⟨by simp only [Finset.coe_univ, Set.mem_univ], h⟩

/-- The `componentCompl`s chosen by an end are all infinite. -/
/-
**SimpleGraph.end_componentCompl_infinite** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
形式化陈述：end_componentCompl_infinite (e : G.end) (K : (Finset V)ᵒᵖ) : ((e : (j : (F
inset V)ᵒᵖ) -> G.componentComplFunctor.obj j) K).supp.Infinite
参数：e : G.end；K : (Finset V)ᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.ComponentCompl.infinite_iff_in_all_ranges`：infinite_iff_in_a
ll_ranges {K : Finset V} (C : G.ComponentCompl K) : C.supp.Infinite ↔ forall (L)
 (h : K subseteq L), exists D : G.Component…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
The `componentCompl`s chosen by an end are all infinite.
-/
lemma end_componentCompl_infinite (e : G.end) (K : (Finset V)ᵒᵖ) :
    ((e : (j : (Finset V)ᵒᵖ) → G.componentComplFunctor.obj j) K).supp.Infinite := by
  refine (e.val K).infinite_iff_in_all_ranges.mpr (fun L h => ?_)
  change Opposite.unop K ⊆ Opposite.unop (Opposite.op L) at h
  exact ⟨e.val (Opposite.op L), (e.prop (CategoryTheory.opHomOfLE h))⟩
/-
**SimpleGraph.componentComplFunctor_nonempty_of_infinite** 是 Mathlib 中的一个实例，位于命名
空间 `SimpleGraph`。
形式化陈述：componentComplFunctor_nonempty_of_infinite [Infinite V] (K : (Finset V)ᵒᵖ)
 : Nonempty (G.componentComplFunctor.obj K)
参数：K : (Finset V)ᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance componentComplFunctor_nonempty_of_infinite [Infinite V] (K : (Finset V)ᵒᵖ) :
    Nonempty (G.componentComplFunctor.obj K) := G.componentCompl_nonempty_of_infinite K.unop
/-
**SimpleGraph.componentComplFunctor_finite** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGrap
h`。
形式化陈述：componentComplFunctor_finite [LocallyFinite G] [Fact G.Preconnected] (K : 
(Finset V)ᵒᵖ) : Finite (G.componentComplFunctor.obj K)
参数：K : (Finset V)ᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance componentComplFunctor_finite [LocallyFinite G] [Fact G.Preconnected]
    (K : (Finset V)ᵒᵖ) : Finite (G.componentComplFunctor.obj K) := G.componentCompl_finite K.unop

/-- A locally finite preconnected infinite graph has at least one end. -/
/-
**SimpleGraph.nonempty_ends_of_infinite** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：nonempty_ends_of_infinite [LocallyFinite G] [Fact G.Preconnected] [Infinit
e V] : G.end.Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_sections_of_finite_inverse_system`：nonempty_sections_of_finite_
inverse_system {J : Type u} [Preorder J] [IsDirectedOrder J] (F : Jᵒᵖ ⥤ Type v) 
[forall j : Jᵒᵖ, Finite (F.obj j…

--- 原说明 ---
A locally finite preconnected infinite graph has at least one end.
-/
lemma nonempty_ends_of_infinite [LocallyFinite G] [Fact G.Preconnected] [Infinite V] :
    G.end.Nonempty := by
  apply nonempty_sections_of_finite_inverse_system G.componentComplFunctor

end SimpleGraph

