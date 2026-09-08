/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Cofinal
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cofinality of an order

This file contains the definition of the cofinality `Order.cof α` of an order. This is the smallest
cardinality of a cofinal subset.
-/

public noncomputable section

open Function Cardinal Set Order

universe u v w

variable {α γ : Type u} {β : Type v}

/-! ### Cofinality of orders -/

namespace Order
section Preorder
variable [Preorder α]

variable (α) in
/-- The cofinality of a preorder is the smallest cardinality of a cofinal subset. -/
@[wikidata Q1283623]
/-
**Order.cof** 是 Mathlib 中的一个定义，位于命名空间 `Order`。
形式化陈述：cof : Cardinal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofinality of a preorder is the smallest cardinality of a cofinal subset.
-/
def cof : Cardinal :=
  ⨅ s : {s : Set α // IsCofinal s}, #s
/-
**Order.cof_le** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_le {s : Set α} (h : IsCofinal s) : cof α <= #s
参数：h : IsCofinal s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciInf_le'`：ciInf_le' (f : ι -> α) (i : ι) : iInf f <= f i
-/
theorem cof_le {s : Set α} (h : IsCofinal s) : cof α ≤ #s :=
  ciInf_le' (ι := {s : Set α // IsCofinal s}) _ ⟨s, h⟩
/-
**Order.le_lift_cof_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_lift_cof_iff {c : Cardinal.{max u v}} : c <= lift.{v} (cof α) ↔ forall 
s : Set α, IsCofinal s -> c <= lift.{v} #s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.SetTheory.Cardinal.Cofinality.Basic.0.Order.cof.eq_1`：∀
 (α : Type u) [inst : Preorder α], Order.cof α = ⨅ s, Cardinal.mk ↑↑s
· 使用定理 `Cardinal.lift_iInf`：lift_iInf {ι} (f : ι -> Cardinal) : lift.{u, v} (iIn
f f) = ⨅ i, lift.{u, v} (f i)
· 使用定理 `le_ciInf_iff'`：le_ciInf_iff' [Nonempty ι] {f : ι -> α} {a : α} : a <= iI
nf f ↔ forall i, a <= f i
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_lift_cof_iff {c : Cardinal.{max u v}} :
    c ≤ lift.{v} (cof α) ↔ ∀ s : Set α, IsCofinal s → c ≤ lift.{v} #s := by
  rw [cof, lift_iInf, le_ciInf_iff']
  simp
/-
**Order.le_cof_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_cof_iff {c : Cardinal} : c <= cof α ↔ forall s : Set α, IsCofinal s -> 
c <= #s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Order.le_lift_cof_iff`：le_lift_cof_iff {c : Cardinal.{max u v}} : c <= l
ift.{v} (cof α) ↔ forall s : Set α, IsCofinal s -> c <= lift.{v} #s
-/
theorem le_cof_iff {c : Cardinal} : c ≤ cof α ↔ ∀ s : Set α, IsCofinal s → c ≤ #s := by
  simpa using @le_lift_cof_iff.{u, u} α _ c

@[deprecated (since := "2026-02-18")] alias le_cof := le_cof_iff

variable (α) in
/-- Every well-order has a cofinal subset of cardinal `cof α`. -/
/-
**Order.exists_cof_eq** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：exists_cof_eq : exists s : Set α, IsCofinal s ∧ #s = cof α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciInf_mem`：ciInf_mem [Nonempty ι] (f : ι -> α) : iInf f in range f
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
Every well-order has a cofinal subset of cardinal `cof α`.
-/
theorem exists_cof_eq : ∃ s : Set α, IsCofinal s ∧ #s = cof α := by
  obtain ⟨s, hs⟩ := ciInf_mem fun s : {s : Set α // IsCofinal s} ↦ #s
  exact ⟨s.1, s.2, hs⟩

@[deprecated (since := "2026-05-25")] alias cof_eq := exists_cof_eq

variable (α) in
/-
**Order.cof_le_cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_le_cardinalMk : cof α <= #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Order.cof_le`：cof_le {s : Set α} (h : IsCofinal s) : cof α <= #s
· 使用定理 `IsCofinal.univ`：IsCofinal.univ : IsCofinal (@univ α)
· 使用定理 `Cardinal.mk_univ`：mk_univ {α : Type u} : #(@univ α) = #α
-/
theorem cof_le_cardinalMk : cof α ≤ #α :=
  cof_le .univ |>.trans_eq mk_univ
/-
**Order.cof_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_eq_zero_iff : cof α = 0 ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.exists_cof_eq`：exists_cof_eq : exists s : Set α, IsCofinal s ∧ #s 
= cof α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `ciInf_const`：∀ {α : Type u_1} {ι : Sort u_4} [inst : ConditionallyComple
tePartialOrderInf α] [hι : Nonempty ι] {a : α}, ⨅ x, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cof_eq_zero_iff : cof α = 0 ↔ IsEmpty α := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ by simp [cof]⟩
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  simp_all [mk_eq_zero_iff, isCofinal_empty_iff]

@[simp]
/-
**Order.cof_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_eq_zero [h : IsEmpty α] : cof α = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.cof_eq_zero_iff`：cof_eq_zero_iff : cof α = 0 ↔ IsEmpty α
-/
theorem cof_eq_zero [h : IsEmpty α] : cof α = 0 :=
  cof_eq_zero_iff.2 h
/-
**Order.cof_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_ne_zero_iff : cof α != 0 ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Order.cof_eq_zero_iff`：cof_eq_zero_iff : cof α = 0 ↔ IsEmpty α
-/
theorem cof_ne_zero_iff : cof α ≠ 0 ↔ Nonempty α := by
  simpa using cof_eq_zero_iff.not

@[simp]
/-
**Order.cof_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_ne_zero [h : Nonempty α] : cof α != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.cof_ne_zero_iff`：cof_ne_zero_iff : cof α != 0 ↔ Nonempty α
-/
theorem cof_ne_zero [h : Nonempty α] : cof α ≠ 0 :=
  cof_ne_zero_iff.2 h
/-
**Order.cof_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_eq_one_iff : cof α = 1 ↔ exists x : α, IsTop x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.exists_cof_eq`：exists_cof_eq : exists s : Set α, IsCofinal s ∧ #s 
= cof α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_set_eq_one_iff`：mk_set_eq_one_iff {s : Set α} : #s = 1 ↔ exi
sts x, s = {x}
· 使用定理 `isCofinal_singleton_iff`：isCofinal_singleton_iff {x : α} : IsCofinal {x}
 ↔ IsTop x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Order.cof_le`：cof_le {s : Set α} (h : IsCofinal s) : cof α <= #s
· 使用定理 `Cardinal.mk_singleton`：mk_singleton {α : Type u} (x : α) : #({x} : Set α
) = 1
· 使用定理 `Cardinal.one_le_iff_ne_zero`：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ c ≠ 0
· 使用定理 `Order.cof_ne_zero_iff`：cof_ne_zero_iff : cof α != 0 ↔ Nonempty α
-/
theorem cof_eq_one_iff : cof α = 1 ↔ ∃ x : α, IsTop x := by
  refine ⟨fun h ↦ ?_, fun ⟨t, ht⟩ ↦ ?_⟩
  · obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
    rw [h, mk_set_eq_one_iff] at hs'
    obtain ⟨t, rfl⟩ := hs'
    use t
    rwa [isCofinal_singleton_iff] at hs
  · apply le_antisymm
    · apply (cof_le (s := {t}) _).trans_eq (mk_singleton _)
      rwa [isCofinal_singleton_iff]
    · rw [Cardinal.one_le_iff_ne_zero, cof_ne_zero_iff]
      use t

@[simp]
/-
**Order.cof_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_eq_one [OrderTop α] : cof α = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.cof_eq_one_iff`：cof_eq_one_iff : cof α = 1 ↔ exists x : α, IsTop x
· 使用定理 `isTop_top`：isTop_top : IsTop (⊤ : α)
-/
theorem cof_eq_one [OrderTop α] : cof α = 1 :=
  cof_eq_one_iff.2 ⟨⊤, isTop_top⟩
/-
**Order.cof_ne_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_ne_one_iff : cof α != 1 ↔ NoTopOrder α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `noTopOrder_iff`：∀ {α : Type u_1} [inst : LE α], NoTopOrder α ↔ ∀ (x : α)
, ¬IsTop x
· 使用定理 `Order.cof_eq_one_iff`：cof_eq_one_iff : cof α = 1 ↔ exists x : α, IsTop x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cof_ne_one_iff : cof α ≠ 1 ↔ NoTopOrder α := by
  rw [← not_iff_not, not_not, noTopOrder_iff, cof_eq_one_iff]
  simp

@[simp]
/-
**Order.cof_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_ne_one [h : NoTopOrder α] : cof α != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.cof_ne_one_iff`：cof_ne_one_iff : cof α != 1 ↔ NoTopOrder α
-/
theorem cof_ne_one [h : NoTopOrder α] : cof α ≠ 1 :=
  cof_ne_one_iff.2 h
/-
**Order.cof_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_le_one_iff [Nonempty α] : cof α <= 1 ↔ exists x : α, IsTop x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `Cardinal.lt_one_iff`：∀ {c : Cardinal.{u_1}}, c < 1 ↔ c = 0
· 使用定理 `Order.cof_eq_one_iff`：cof_eq_one_iff : cof α = 1 ↔ exists x : α, IsTop x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cof_le_one_iff [Nonempty α] : cof α ≤ 1 ↔ ∃ x : α, IsTop x := by
  rw [le_iff_lt_or_eq, Cardinal.lt_one_iff, cof_eq_one_iff]
  simp
/-
**Order.one_lt_cof_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：one_lt_cof_iff [Nonempty α] : 1 < cof α ↔ NoTopOrder α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `noTopOrder_iff`：∀ {α : Type u_1} [inst : LE α], NoTopOrder α ↔ ∀ (x : α)
, ¬IsTop x
· 使用定理 `Order.cof_le_one_iff`：cof_le_one_iff [Nonempty α] : cof α <= 1 ↔ exists 
x : α, IsTop x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_lt_cof_iff [Nonempty α] : 1 < cof α ↔ NoTopOrder α := by
  rw [← not_iff_not, not_lt, noTopOrder_iff, cof_le_one_iff]
  simp

@[simp]
/-
**Order.one_lt_cof** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：one_lt_cof [Nonempty α] [h : NoTopOrder α] : 1 < cof α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_lt_cof_iff`：one_lt_cof_iff [Nonempty α] : 1 < cof α ↔ NoTopOrd
er α
-/
theorem one_lt_cof [Nonempty α] [h : NoTopOrder α] : 1 < cof α :=
  one_lt_cof_iff.2 h

end Preorder

section LinearOrder
variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-
**Order.lift_cof_congr_of_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lift_cof_congr_of_strictMono {f : α -> β} (hf : StrictMono f) (hf' : IsCof
inal (range f)) : lift.{v} (cof α) = lift.{u} (cof β)
参数：hf : StrictMono f；hf' : IsCofinal (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.le_lift_cof_iff`：le_lift_cof_iff {c : Cardinal.{max u v}} : c <= l
ift.{v} (cof α) ↔ forall s : Set α, IsCofinal s -> c <= lift.{v} #s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Order.cof_le`：cof_le {s : Set α} (h : IsCofinal s) : cof α <= #s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Cardinal.mk_range_le_lift`：mk_range_le_lift {α : Type u} {β : Type v} {f
 : α -> β} : lift.{u} #(range f) <= lift.{v} #α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `IsCofinal.image`：IsCofinal.image {f : α -> β} {s : Set α} (hs : IsCofina
l s) (hf : Monotone f) (hf' : IsCofinal (.range f)) : IsCofinal (f '' s)
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Cardinal.mk_image_le_lift`：mk_image_le_lift {α : Type u} {β : Type v} {f
 : α -> β} {s : Set α} : lift.{u} #(f '' s) <= lift.{v} #s
-/
theorem lift_cof_congr_of_strictMono {f : α → β} (hf : StrictMono f) (hf' : IsCofinal (range f)) :
    lift.{v} (cof α) = lift.{u} (cof β) := by
  apply le_antisymm <;> rw [le_lift_cof_iff] <;> intro s hs
  · have H (x : s) : ∃ y : α, x ≤ f y := by simpa using hf' x
    choose g hg using H
    refine (lift_le.2 <| cof_le (s := range g) fun a ↦ ?_).trans mk_range_le_lift
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hf' (f a)
    obtain ⟨c, hc, hc'⟩ := hs (f b)
    refine ⟨_, Set.mem_range_self ⟨c, hc⟩, ?_⟩
    rw [← hf.le_iff_le]
    exact hb.trans (hc'.trans (hg ⟨c, hc⟩))
  · exact (lift_le.2 <| cof_le (hs.image hf.monotone hf')).trans mk_image_le_lift
/-
**Order.cof_congr_of_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_congr_of_strictMono {f : α -> γ} (hf : StrictMono f) (hf' : IsCofinal 
(range f)) : cof α = cof γ
参数：hf : StrictMono f；hf' : IsCofinal (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Order.lift_cof_congr_of_strictMono`：lift_cof_congr_of_strictMono {f : α 
-> β} (hf : StrictMono f) (hf' : IsCofinal (range f)) : lift.{v} (cof α) = lift.
{u} (cof β)
-/
theorem cof_congr_of_strictMono {f : α → γ} (hf : StrictMono f) (hf' : IsCofinal (range f)) :
    cof α = cof γ := by
  simpa using lift_cof_congr_of_strictMono hf hf'
/-
**Order.cof_eq_of_isCofinal** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_eq_of_isCofinal {s : Set α} (hs : IsCofinal s) : cof s = cof α
参数：hs : IsCofinal s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.cof_congr_of_strictMono`：cof_congr_of_strictMono {f : α -> γ} (hf 
: StrictMono f) (hf' : IsCofinal (range f)) : cof α = cof γ
· 使用定理 `Subtype.strictMono_coe`：Subtype.strictMono_coe [Preorder α] (p : α -> Pr
op) : StrictMono ((↑) : Subtype p -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
-/
theorem cof_eq_of_isCofinal {s : Set α} (hs : IsCofinal s) : cof s = cof α :=
  cof_congr_of_strictMono (Subtype.strictMono_coe _) (by simpa)

@[simp]
/-
**Order.cof_lt_aleph0_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_lt_aleph0_iff : cof α < ℵ₀ ↔ cof α <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.exists_cof_eq`：exists_cof_eq : exists s : Set α, IsCofinal s ∧ #s 
= cof α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.eq_1`：∀ {α : Type u} (s : Set α), s.Finite = Finite ↑s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Cardinal.mk_lt_aleph0_iff`：mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Set.Finite.exists_subsingleton_isCofinal`：∀ {α : Type u_2} [inst : Linea
rOrder α] {s : Set α}, s.Finite → IsCofinal s → ∃ t, t.Subsingleton ∧ IsCofinal 
t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.cof_le`：cof_le {s : Set α} (h : IsCofinal s) : cof α <= #s
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Cardinal.one_lt_aleph0`：one_lt_aleph0 : 1 < ℵ₀
-/
theorem cof_lt_aleph0_iff : cof α < ℵ₀ ↔ cof α ≤ 1 := by
  refine ⟨fun h ↦ ?_, (lt_of_le_of_lt · one_lt_aleph0)⟩
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq α
  have hf : s.Finite := by
    rw [Set.Finite, ← mk_lt_aleph0_iff]
    exact hs'.trans_lt h
  obtain ⟨t, ht, ht'⟩ := hf.exists_subsingleton_isCofinal hs
  apply (cof_le ht').trans
  simpa

@[simp]
/-
**Order.aleph0_le_cof_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：aleph0_le_cof_iff : ℵ₀ <= cof α ↔ 1 < cof α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem aleph0_le_cof_iff : ℵ₀ ≤ cof α ↔ 1 < cof α := by
  simp [← not_lt]
/-
**Order.aleph0_le_cof** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：aleph0_le_cof [Nonempty α] [NoMaxOrder α] : ℵ₀ <= cof α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
-/
theorem aleph0_le_cof [Nonempty α] [NoMaxOrder α] : ℵ₀ ≤ cof α := by
  simp

@[simp]
/-
**Order.cof_eq_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_eq_aleph0 [NoMaxOrder α] [Nonempty α] [Countable α] : cof α = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.cof_le_cardinalMk`：cof_le_cardinalMk : cof α <= #α
· 使用定理 `Cardinal.mk_le_aleph0`：mk_le_aleph0 [Countable α] : #α <= ℵ₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
-/
theorem cof_eq_aleph0 [NoMaxOrder α] [Nonempty α] [Countable α] : cof α = ℵ₀ :=
  ((cof_le_cardinalMk _).trans mk_le_aleph0).antisymm (by simp)
/-
**Order.cof_nat** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：cof_nat : cof Nat = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.cof_eq_aleph0`：cof_eq_aleph0 [NoMaxOrder α] [Nonempty α] [Countabl
e α] : cof α = ℵ₀
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cof_nat : cof ℕ = ℵ₀ := by simp

end LinearOrder
end Order

section Congr
variable [Preorder α] [Preorder β] [Preorder γ]

/-
**GaloisConnection.cof_le_lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GaloisConnection.cof_le_lift {f : β -> α} {g : α -> β} (h : GaloisConnecti
on f g) : Cardinal.lift.{u} (Order.cof β) <= Cardinal.lift.{v} (Order.cof α)
参数：h : GaloisConnection f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.le_lift_cof_iff`：le_lift_cof_iff {c : Cardinal.{max u v}} : c <= l
ift.{v} (cof α) ↔ forall s : Set α, IsCofinal s -> c <= lift.{v} #s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Order.cof_le`：cof_le {s : Set α} (h : IsCofinal s) : cof α <= #s
· 使用定理 `GaloisConnection.map_isCofinal`：GaloisConnection.map_isCofinal {f : β ->
 α} {g : α -> β} (h : GaloisConnection f g) {s : Set α} (hs : IsCofinal s) : IsC
ofinal (g '' s)
· 使用定理 `Cardinal.mk_image_le_lift`：mk_image_le_lift {α : Type u} {β : Type v} {f
 : α -> β} {s : Set α} : lift.{u} #(f '' s) <= lift.{v} #s
-/
theorem GaloisConnection.cof_le_lift {f : β → α} {g : α → β} (h : GaloisConnection f g) :
    Cardinal.lift.{u} (Order.cof β) ≤ Cardinal.lift.{v} (Order.cof α) := by
  rw [le_lift_cof_iff]
  exact fun s hs ↦ (lift_le.2 <| cof_le (h.map_isCofinal hs)).trans mk_image_le_lift
/-
**GaloisConnection.cof_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GaloisConnection.cof_le {f : γ -> α} {g : α -> γ} (h : GaloisConnection f 
g) : Order.cof γ <= Order.cof α
参数：h : GaloisConnection f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `GaloisConnection.cof_le_lift`：GaloisConnection.cof_le_lift {f : β -> α} 
{g : α -> β} (h : GaloisConnection f g) : Cardinal.lift.{u} (Order.cof β) <= Car
dinal.lift.{v} (Or…
-/
theorem GaloisConnection.cof_le {f : γ → α} {g : α → γ} (h : GaloisConnection f g) :
    Order.cof γ ≤ Order.cof α := by
  simpa using h.cof_le_lift
/-
**OrderIso.lift_cof_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.lift_cof_congr (f : α ≃o β) : Cardinal.lift.{v} (Order.cof α) = C
ardinal.lift.{u} (Order.cof β)
参数：f : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `GaloisConnection.cof_le_lift`：GaloisConnection.cof_le_lift {f : β -> α} 
{g : α -> β} (h : GaloisConnection f g) : Cardinal.lift.{u} (Order.cof β) <= Car
dinal.lift.{v} (Or…
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
theorem OrderIso.lift_cof_congr (f : α ≃o β) :
    Cardinal.lift.{v} (Order.cof α) = Cardinal.lift.{u} (Order.cof β) :=
  f.to_galoisConnection.cof_le_lift.antisymm (f.symm.to_galoisConnection.cof_le_lift)

@[deprecated (since := "2026-03-20")] alias OrderIso.lift_cof_eq := OrderIso.lift_cof_congr
/-
**OrderIso.cof_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.cof_congr (f : α ≃o γ) : Order.cof α = Order.cof γ
参数：f : α ≃o γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `OrderIso.lift_cof_congr`：OrderIso.lift_cof_congr (f : α ≃o β) : Cardinal
.lift.{v} (Order.cof α) = Cardinal.lift.{u} (Order.cof β)
-/
theorem OrderIso.cof_congr (f : α ≃o γ) : Order.cof α = Order.cof γ := by
  simpa using f.lift_cof_congr

@[deprecated (since := "2026-03-20")] alias OrderIso.cof_eq := OrderIso.cof_congr

@[deprecated (since := "2026-02-18")] alias RelIso.cof_eq_lift := OrderIso.lift_cof_congr
@[deprecated (since := "2026-02-18")] alias RelIso.cof_eq := OrderIso.cof_congr

end Congr

/-- If the union of `s` is cofinal and `s` is smaller than the cofinality, then `s` has a cofinal
member. -/
/-
**isCofinal_of_isCofinal_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCofinal_of_isCofinal_sUnion {α : Type*} [LinearOrder α] {s : Set (Set α)
} (h₁ : IsCofinal (⋃₀ s)) (h₂ : #s < Order.cof α) : exists x in s, IsCofinal x
参数：Set α；h₁ : IsCofinal (⋃₀ s)；h₂ : #s < Order.cof α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Order.cof_le`：cof_le {s : Set α} (h : IsCofinal s) : cof α <= #s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.mk_range_le`：mk_range_le {α β : Type u} {f : α -> β} : #(range 
f) <= #α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If the union of `s` is cofinal and `s` is smaller than the cofinality, then `s` 
has a cofinal
member.
-/
theorem isCofinal_of_isCofinal_sUnion {α : Type*} [LinearOrder α] {s : Set (Set α)}
    (h₁ : IsCofinal (⋃₀ s)) (h₂ : #s < Order.cof α) : ∃ x ∈ s, IsCofinal x := by
  contrapose! h₂
  simp_rw [not_isCofinal_iff] at h₂
  choose f hf using h₂
  refine (cof_le (s := range fun x ↦ f x.1 x.2) fun a ↦ ?_).trans mk_range_le
  obtain ⟨b, ⟨t, ht, hb⟩, hab⟩ := h₁ a
  simpa using ⟨t, ht, hab.trans (hf t ht b hb).le⟩

/-- If the union of the `ι`-indexed family `s` is cofinal and `ι` is smaller than the cofinality,
then `s` has a cofinal member. -/
/-
**isCofinal_of_isCofinal_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCofinal_of_isCofinal_iUnion {α : Type*} {ι} [LinearOrder α] {s : ι -> Se
t α} (h₁ : IsCofinal (⋃ i, s i)) (h₂ : #ι < Order.cof α) : exists i, IsCofinal (
s i)
参数：h₁ : IsCofinal (⋃ i, s i)；h₂ : #ι < Order.cof α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCofinal_of_isCofinal_sUnion`：isCofinal_of_isCofinal_sUnion {α : Type*}
 [LinearOrder α] {s : Set (Set α)} (h₁ : IsCofinal (⋃₀ s)) (h₂ : #s < Order.cof 
α) : exists x in s,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_range`：sUnion_range (f : ι -> Set β) : ⋃₀ range f = ⋃ x, f x
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.mk_range_le`：mk_range_le {α β : Type u} {f : α -> β} : #(range 
f) <= #α

--- 原说明 ---
If the union of the `ι`-indexed family `s` is cofinal and `ι` is smaller than th
e cofinality,
then `s` has a cofinal member.
-/
theorem isCofinal_of_isCofinal_iUnion {α : Type*} {ι} [LinearOrder α] {s : ι → Set α}
    (h₁ : IsCofinal (⋃ i, s i)) (h₂ : #ι < Order.cof α) : ∃ i, IsCofinal (s i) := by
  rw [← sUnion_range] at h₁
  obtain ⟨_, ⟨i, rfl⟩, h⟩ := isCofinal_of_isCofinal_sUnion h₁ (mk_range_le.trans_lt h₂)
  exact ⟨i, h⟩
