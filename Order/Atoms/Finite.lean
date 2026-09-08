/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Atoms
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Preorder.Finite

/-!
# Atoms, Coatoms, Simple Lattices, and Finiteness

This module contains some results on atoms and simple lattices in the finite context.

## Main results
* `Finite.to_isAtomic`, `Finite.to_isCoatomic`: Finite partial orders with bottom resp. top
  are atomic resp. coatomic.

-/

public section


variable {α β : Type*}

namespace IsSimpleOrder

variable [LE α] [BoundedOrder α] [IsSimpleOrder α]

section DecidableEq

/-- It is important that `IsSimpleOrder` is the last type-class argument of this instance,
so that type-class inference fails quickly if it doesn't apply.

Note that as of 2025-08-13, this is false. Could someone investigate? -/
/-
**IsSimpleOrder.** 是 Mathlib 中的一个实例，位于命名空间 `IsSimpleOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
It is important that `IsSimpleOrder` is the last type-class argument of this ins
tance,
so that type-class inference fails quickly if it doesn't apply.

Note that as of 2025-08-13, this is false. Could someone investigate?
-/
scoped instance (priority := 200) [DecidableEq α] : Fintype α :=
  Fintype.ofEquiv Bool equivBool.symm

end DecidableEq

/-
**IsSimpleOrder.** 是 Mathlib 中的一个实例，位于命名空间 `IsSimpleOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance (priority := 200) : Finite α := by classical infer_instance

end IsSimpleOrder

namespace Fintype

namespace IsSimpleOrder

open scoped _root_.IsSimpleOrder

variable [LE α] [BoundedOrder α] [IsSimpleOrder α] [DecidableEq α]

/-
**Fintype.IsSimpleOrder.univ** 是 Mathlib 中的一个定理，位于命名空间 `Fintype.IsSimpleOrder`。
形式化陈述：univ : (Finset.univ : Finset α) = {⊤, ⊥}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
-/
theorem univ : (Finset.univ : Finset α) = {⊤, ⊥} := by
  ext
  simpa using (eq_bot_or_eq_top _).symm
/-
**Fintype.IsSimpleOrder.card** 是 Mathlib 中的一个定理，位于命名空间 `Fintype.IsSimpleOrder`。
形式化陈述：card : Fintype.card α = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Fintype.ofEquiv_card`：ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (of
Equiv α f) = card α
· 使用定理 `Fintype.card_bool`：Fintype.card_bool : Fintype.card Bool = 2
-/
theorem card : Fintype.card α = 2 :=
  (Fintype.ofEquiv_card _).trans Fintype.card_bool

end IsSimpleOrder

end Fintype

namespace Bool

/-
**Bool.** 是 Mathlib 中的一个实例，位于命名空间 `Bool`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSimpleOrder Bool :=
  ⟨fun a => by
    rw [← Finset.mem_singleton, Or.comm, ← Finset.mem_insert, top_eq_true, bot_eq_false, ←
      Fintype.univ_bool]
    apply Finset.mem_univ⟩

end Bool

section Fintype

open Finset

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Finite.to_isCoatomic [PartialOrder α] [OrderTop α] [Finite α] :
    IsCoatomic α :=
  IsStronglyCoatomic.toIsCoatomic α

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Finite.to_isAtomic [PartialOrder α] [OrderBot α] [Finite α] :
    IsAtomic α :=
  isCoatomic_dual_iff_isAtomic.mp Finite.to_isCoatomic

end Fintype

section LocallyFinite

variable [Preorder α] [LocallyFiniteOrder α]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStronglyAtomic α where
  exists_covBy_le_of_lt a b hab := by
    obtain ⟨x, hx, hxmin⟩ := (LocallyFiniteOrder.finsetIoc a b).exists_minimal
      ⟨b, by simpa [LocallyFiniteOrder.finset_mem_Ioc]⟩
    simp only [LocallyFiniteOrder.finset_mem_Ioc] at hx hxmin
    exact ⟨x, ⟨hx.1, fun c hac hcx ↦ hcx.not_ge <| hxmin ⟨hac, hcx.le.trans hx.2⟩ hcx.le⟩, hx.2⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStronglyCoatomic α := by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]; infer_instance

end LocallyFinite

section IsStronglyAtomic

variable [PartialOrder α] {a : α}

/-
**exists_covby_infinite_Ici_of_infinite_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_covby_infinite_Ici_of_infinite_Ici [IsStronglyAtomic α] (ha : (Set.
Ici a).Infinite) (hfin : {x | a ⋖ x}.Finite) : exists b, a ⋖ b ∧ (Set.Ici b).Inf
inite
参数：ha : (Set.Ici a).Infinite；hfin : {x | a ⋖ x}.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.Finite.not_infinite`：∀ {α : Type u} {s : Set α}, s.Finite → ¬s.Infin
ite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LT.lt.exists_covby_le`：∀ {α : Type u_4} {a b : α} [inst : Preorder α] [I
sStronglyAtomic α], a < b → ∃ x, a ⋖ x ∧ x ≤ b
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `Set.Infinite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Infinite → t.Finite 
→ (s \ t).Infinite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
theorem exists_covby_infinite_Ici_of_infinite_Ici [IsStronglyAtomic α]
    (ha : (Set.Ici a).Infinite) (hfin : {x | a ⋖ x}.Finite) :
    ∃ b, a ⋖ b ∧ (Set.Ici b).Infinite := by
  by_contra! h
  refine ((hfin.biUnion (t := Set.Ici) (by simpa using h)).subset (fun b hb ↦ ?_)).not_infinite
    (ha.sdiff (Set.finite_singleton a))
  obtain ⟨x, hax, hxb⟩ := ((show a ≤ b from hb.1).lt_of_ne (Ne.symm hb.2)).exists_covby_le
  exact Set.mem_biUnion hax hxb
/-
**exists_covby_infinite_Iic_of_infinite_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_covby_infinite_Iic_of_infinite_Iic [IsStronglyCoatomic α] (ha : (Se
t.Iic a).Infinite) (hfin : {x | x ⋖ a}.Finite) : exists b, b ⋖ a ∧ (Set.Iic b).I
nfinite
参数：ha : (Set.Iic a).Infinite；hfin : {x | x ⋖ a}.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `toDual_covBy_toDual_iff`：toDual_covBy_toDual_iff : toDual b ⋖ toDual a ↔
 a ⋖ b
· 使用定理 `exists_covby_infinite_Ici_of_infinite_Ici`：exists_covby_infinite_Ici_of_
infinite_Ici [IsStronglyAtomic α] (ha : (Set.Ici a).Infinite) (hfin : {x | a ⋖ x
}.Finite) : exists b, a ⋖ b ∧ (…
· 使用定理 `instIsStronglyAtomicOrderDualOfIsStronglyCoatomic`：∀ {α : Type u_4} [ins
t : Preorder α] [IsStronglyCoatomic α], IsStronglyAtomic αᵒᵈ
-/
theorem exists_covby_infinite_Iic_of_infinite_Iic [IsStronglyCoatomic α]
    (ha : (Set.Iic a).Infinite) (hfin : {x | x ⋖ a}.Finite) :
    ∃ b, b ⋖ a ∧ (Set.Iic b).Infinite := by
  simp_rw [← toDual_covBy_toDual_iff (α := α)] at hfin ⊢
  exact exists_covby_infinite_Ici_of_infinite_Ici (α := αᵒᵈ) ha hfin

end IsStronglyAtomic

