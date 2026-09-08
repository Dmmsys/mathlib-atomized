/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Eventually constant monotone functions

This file proves variations of the following theorem: if `α` is a linear order and `β` is a partial
order with `#β < cof α`, then any monotone function `f : α → β` must be eventually constant. In
particular, this applies for functions from `Cardinal.{u}` or `Ordinal.{u}` into a `Small.{u}` type.
-/

public section

universe u v

variable {α : Type u} {β : Type v} [LinearOrder α] [PartialOrder β]

open Cardinal Filter Order Set

namespace Filter.EventuallyConst
variable {f : α → β}

/-
**Filter.EventuallyConst.of_not_isCofinal_rangeSplitting** 是 Mathlib 中的一个定理，位于命名
空间 `Filter.EventuallyConst`。
形式化陈述：of_not_isCofinal_rangeSplitting [Nonempty α] (hf : Monotone f) (hf' : ¬ Is
Cofinal (range (rangeSplitting f))) : atTop.EventuallyConst f
参数：hf : Monotone f；hf' : ¬ IsCofinal (range (rangeSplitting f))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.eventuallyConst_atTop`：eventuallyConst_atTop [SemilatticeSup α] [
Nonempty α] : EventuallyConst f atTop ↔ (exists i, forall j, i <= j -> f j = f i
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_isCofinal_iff`：not_isCofinal_iff {s : Set α} : ¬ IsCofinal s ↔ exist
s x, forall y in s, y < x
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.apply_rangeSplitting`：apply_rangeSplitting (f : α -> β) (x : range f
) : f (rangeSplitting f x) = x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem of_not_isCofinal_rangeSplitting [Nonempty α] (hf : Monotone f)
    (hf' : ¬ IsCofinal (range (rangeSplitting f))) : atTop.EventuallyConst f := by
  rw [eventuallyConst_atTop]
  obtain ⟨i, hi⟩ := not_isCofinal_iff.1 hf'
  refine ⟨i, fun j hij ↦ (hf hij).antisymm' <| (hf (hi _ ⟨⟨f j, j, rfl⟩, rfl⟩).le).trans' ?_⟩
  rw [apply_rangeSplitting f]
/-
**Filter.EventuallyConst.of_monotone_of_lt_cof** 是 Mathlib 中的一个定理，位于命名空间 `Filter
.EventuallyConst`。
形式化陈述：of_monotone_of_lt_cof (hf : Monotone f) (hα : lift.{u} #β < lift.{v} (cof 
α)) : atTop.EventuallyConst f
参数：hf : Monotone f；hα : lift.{u} #β < lift.{v} (cof α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.cof_eq_zero`：cof_eq_zero [h : IsEmpty α] : cof α = 0
· 使用定理 `Cardinal.lift_zero`：lift_zero : lift 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Filter.EventuallyConst.of_not_isCofinal_rangeSplitting`：of_not_isCofinal
_rangeSplitting [Nonempty α] (hf : Monotone f) (hf' : ¬ IsCofinal (range (rangeS
plitting f))) : atTop.EventuallyConst f
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Monotone.isChain_range`：Monotone.isChain_range [LinearOrder α] [Preorder
 β] {f : α -> β} (hf : Monotone f) : IsChain (· <= ·) (range f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.lift_cof_congr_of_strictMono`：lift_cof_congr_of_strictMono {f : α 
-> β} (hf : StrictMono f) (hf' : IsCofinal (range f)) : lift.{v} (cof α) = lift.
{u} (cof β)
· 使用定理 `Set.rangeSplitting_strictMono`：rangeSplitting_strictMono [LinearOrder α]
 [Preorder β] {f : α -> β} (hf : Monotone f) : StrictMono (rangeSplitting f)
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.cof_le_cardinalMk`：cof_le_cardinalMk : cof α <= #α
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α
-/
theorem of_monotone_of_lt_cof (hf : Monotone f) (hα : lift.{u} #β < lift.{v} (cof α)) :
    atTop.EventuallyConst f := by
  have : Nonempty α := by by_contra!; simp at hα
  refine .of_not_isCofinal_rangeSplitting hf ?_
  contrapose! hα
  classical let := hf.isChain_range.linearOrder
  rw [← lift_cof_congr_of_strictMono (rangeSplitting_strictMono hf) hα, lift_le]
  exact (cof_le_cardinalMk _).trans (mk_set_le _)
/-
**Filter.EventuallyConst.of_antitone_of_lt_cof** 是 Mathlib 中的一个定理，位于命名空间 `Filter
.EventuallyConst`。
形式化陈述：of_antitone_of_lt_cof (hf : Antitone f) (hα : lift.{u} #β < lift.{v} (cof 
α)) : atTop.EventuallyConst f
参数：hf : Antitone f；hα : lift.{u} #β < lift.{v} (cof α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyConst.of_monotone_of_lt_cof`：of_monotone_of_lt_cof (hf 
: Monotone f) (hα : lift.{u} #β < lift.{v} (cof α)) : atTop.EventuallyConst f
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem of_antitone_of_lt_cof (hf : Antitone f) (hα : lift.{u} #β < lift.{v} (cof α)) :
    atTop.EventuallyConst f :=
  .of_monotone_of_lt_cof (β := βᵒᵈ) hf.dual_right hα

end Filter.EventuallyConst

namespace Cardinal
variable {f : Cardinal.{v} → β} [Small.{v} β]

/-
**Cardinal.eventuallyConst_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：eventuallyConst_of_monotone (hf : Monotone f) : atTop.EventuallyConst f
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyConst.of_monotone_of_lt_cof`：of_monotone_of_lt_cof (hf 
: Monotone f) (hα : lift.{u} #β < lift.{v} (cof α)) : atTop.EventuallyConst f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.cof_eq_cardinalMk`：cof_eq_cardinalMk : cof α = #α
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
· 使用定理 `Cardinal.instIsRegularCardinalOrder`：IsRegularCardinalOrder Cardinal.{u_
1}
· 使用定理 `Cardinal.mk_cardinal`：mk_cardinal : #Cardinal = univ.{u, u + 1}
· 使用定理 `Cardinal.lift_univ`：lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w}
-/
theorem eventuallyConst_of_monotone (hf : Monotone f) : atTop.EventuallyConst f := by
  refine .of_monotone_of_lt_cof hf ?_
  simpa [← small_iff_lift_mk_lt_univ]
/-
**Cardinal.eventuallyConst_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：eventuallyConst_of_antitone (hf : Antitone f) : atTop.EventuallyConst f
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.eventuallyConst_of_monotone`：eventuallyConst_of_monotone (hf : 
Monotone f) : atTop.EventuallyConst f
-/
theorem eventuallyConst_of_antitone (hf : Antitone f) : atTop.EventuallyConst f :=
  eventuallyConst_of_monotone (β := βᵒᵈ) hf

end Cardinal

namespace Ordinal
variable {f : Ordinal.{v} → β} [Small.{v} β]

/-
**Ordinal.eventuallyConst_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：eventuallyConst_of_monotone (hf : Monotone f) : atTop.EventuallyConst f
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyConst.of_monotone_of_lt_cof`：of_monotone_of_lt_cof (hf 
: Monotone f) (hα : lift.{u} #β < lift.{v} (cof α)) : atTop.EventuallyConst f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.cof_eq_cardinalMk`：cof_eq_cardinalMk : cof α = #α
· 使用定理 `instIsRegularCardinalOrderOrdinal`：IsRegularCardinalOrder Ordinal.{u_2}
· 使用定理 `Cardinal.mk_ordinal`：mk_ordinal : #Ordinal = univ.{u, u + 1}
· 使用定理 `Cardinal.lift_univ`：lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w}
-/
theorem eventuallyConst_of_monotone (hf : Monotone f) : atTop.EventuallyConst f := by
  refine .of_monotone_of_lt_cof hf ?_
  simpa [← small_iff_lift_mk_lt_univ]
/-
**Ordinal.eventuallyConst_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：eventuallyConst_of_antitone (hf : Antitone f) : atTop.EventuallyConst f
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.eventuallyConst_of_monotone`：eventuallyConst_of_monotone (hf : M
onotone f) : atTop.EventuallyConst f
-/
theorem eventuallyConst_of_antitone (hf : Antitone f) : atTop.EventuallyConst f :=
  eventuallyConst_of_monotone (β := βᵒᵈ) hf

end Ordinal

