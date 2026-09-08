/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Order.LatticeIntervals

/-!
# Lattice structures on the type of nonnegative elements

-/

@[expose] public section
assert_not_exists Ring
assert_not_exists IsOrderedMonoid

open Set

variable {α : Type*}

namespace Nonneg

/-
**Nonneg.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：orderBot [Preorder α] {a : α} : OrderBot { x : α // a <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance orderBot [Preorder α] {a : α} : OrderBot { x : α // a ≤ x } :=
  inferInstanceAs <| OrderBot (Ici a)
/-
**Nonneg.bot_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：bot_eq [Preorder α] {a : α} : (⊥ : { x : α // a <= x }) = ⟨a, le_rfl⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_eq [Preorder α] {a : α} : (⊥ : { x : α // a ≤ x }) = ⟨a, le_rfl⟩ :=
  rfl
/-
**Nonneg.noMaxOrder** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：noMaxOrder [PartialOrder α] [NoMaxOrder α] {a : α} : NoMaxOrder { x : α //
 a <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance noMaxOrder [PartialOrder α] [NoMaxOrder α] {a : α} : NoMaxOrder { x : α // a ≤ x } :=
  inferInstanceAs <| NoMaxOrder (Ici a)
/-
**Nonneg.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup { x : α // a <=
 x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup { x : α // a ≤ x } :=
  inferInstanceAs <| SemilatticeSup (Ici a)
/-
**Nonneg.semilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf { x : α // a <=
 x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf { x : α // a ≤ x } :=
  inferInstanceAs <| SemilatticeInf (Ici a)
/-
**Nonneg.distribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：distribLattice [DistribLattice α] {a : α} : DistribLattice { x : α // a <=
 x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribLattice [DistribLattice α] {a : α} : DistribLattice { x : α // a ≤ x } :=
  inferInstanceAs <| DistribLattice (Ici a)
/-
**Nonneg.instDenselyOrdered** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：instDenselyOrdered [Preorder α] [DenselyOrdered α] {a : α} : DenselyOrdere
d { x : α // a <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDenselyOrdered [Preorder α] [DenselyOrdered α] {a : α} :
    DenselyOrdered { x : α // a ≤ x } :=
  inferInstanceAs <| DenselyOrdered (Ici a)

/-- If `sSup ∅ ≤ a` then `{x : α // a ≤ x}` is a `ConditionallyCompleteLinearOrder`. -/
/-
**Nonneg.conditionallyCompleteLinearOrder** 是 Mathlib 中的一个定义，位于命名空间 `Nonneg`。
形式化陈述：{α : Type u_1} → [inst : ConditionallyCompleteLinearOrder α] → {a : α} → C
onditionallyCompleteLinearOrder { x // a ≤ x }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `sSup ∅ ≤ a` then `{x : α // a ≤ x}` is a `ConditionallyCompleteLinearOrder`.
-/
protected noncomputable abbrev conditionallyCompleteLinearOrder [ConditionallyCompleteLinearOrder α]
    {a : α} : ConditionallyCompleteLinearOrder { x : α // a ≤ x } :=
  -- TODO: missing `Inhabited (Ici a)` instance
  haveI : Inhabited (Ici a) := ⟨a, le_rfl⟩
  inferInstanceAs <| ConditionallyCompleteLinearOrder (Ici a)


set_option backward.isDefEq.respectTransparency false in
/-- If `sSup ∅ ≤ a` then `{x : α // a ≤ x}` is a `ConditionallyCompleteLinearOrderBot`.

This instance uses data fields from `Subtype.linearOrder` to help type-class inference.
The `Set.Ici` data fields are definitionally equal, but that requires unfolding semireducible
definitions, so type-class inference won't see this. -/
/-
**Nonneg.conditionallyCompleteLinearOrderBot** 是 Mathlib 中的一个定义，位于命名空间 `Nonneg`。
形式化陈述：{α : Type u_1} →   [inst : ConditionallyCompleteLinearOrder α] → (a : α) →
 ConditionallyCompleteLinearOrderBot { x // a ≤ x }
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `sSup ∅ ≤ a` then `{x : α // a ≤ x}` is a `ConditionallyCompleteLinearOrderBo
t`.

This instance uses data fields from `Subtype.linearOrder` to help type-class inf
erence.
The `Set.Ici` data fields are definitionally equal, but that requires unfolding 
semireducible
definitions, so type-class inference won't see this.
-/
protected noncomputable abbrev conditionallyCompleteLinearOrderBot
    [ConditionallyCompleteLinearOrder α] (a : α) :
    ConditionallyCompleteLinearOrderBot { x : α // a ≤ x } :=
  { Nonneg.orderBot, Nonneg.conditionallyCompleteLinearOrder with
    csSup_empty := by
      rw [@subset_sSup_def α (Set.Ici a) _ _ ⟨⟨a, le_rfl⟩⟩]; simp [bot_eq] }

end Nonneg

