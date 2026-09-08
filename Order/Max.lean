/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Order.OrderDual

/-!
# Minimal/maximal and bottom/top elements

This file defines predicates for elements to be minimal/maximal or bottom/top and typeclasses
saying that there are no such elements.

## Predicates

* `IsBot`: An element is *bottom* if all elements are greater than it.
* `IsTop`: An element is *top* if all elements are less than it.
* `IsMin`: An element is *minimal* if no element is strictly less than it.
* `IsMax`: An element is *maximal* if no element is strictly greater than it.

See also `isBot_iff_isMin` and `isTop_iff_isMax` for the equivalences in a (co)directed order.

## Typeclasses

* `NoBotOrder`: An order without bottom elements.
* `NoTopOrder`: An order without top elements.
* `NoMinOrder`: An order without minimal elements.
* `NoMaxOrder`: An order without maximal elements.
-/

@[expose] public section


open OrderDual

universe u v

variable {α β : Type*}

/-- Order without bottom elements. -/
@[mk_iff noBotOrder_iff']
/-
**NoBotOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [LE α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order without bottom elements.
-/
class NoBotOrder (α : Type*) [LE α] : Prop where
  /-- For each term `a`, there is some `b` which is either incomparable or strictly smaller. -/
  exists_not_ge (a : α) : ∃ b, ¬a ≤ b

/-- Order without top elements. -/
@[to_dual, mk_iff noTopOrder_iff']
/-
**NoTopOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [LE α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order without top elements.
-/
class NoTopOrder (α : Type*) [LE α] : Prop where
  /-- For each term `a`, there is some `b` which is either incomparable or strictly larger. -/
  exists_not_le (a : α) : ∃ b, ¬b ≤ a

/-- Order without minimal elements. Sometimes called coinitial or dense. -/
@[mk_iff noMinOrder_iff']
/-
**NoMinOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [LT α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order without minimal elements. Sometimes called coinitial or dense.
-/
class NoMinOrder (α : Type*) [LT α] : Prop where
  /-- For each term `a`, there is some strictly smaller `b`. -/
  exists_lt (a : α) : ∃ b, b < a

/-- Order without maximal elements. Sometimes called cofinal. -/
@[to_dual, mk_iff noMaxOrder_iff']
/-
**NoMaxOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [LT α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order without maximal elements. Sometimes called cofinal.
-/
class NoMaxOrder (α : Type*) [LT α] : Prop where
  /-- For each term `a`, there is some strictly greater `b`. -/
  exists_gt (a : α) : ∃ b, a < b

export NoBotOrder (exists_not_ge)
export NoTopOrder (exists_not_le)
export NoMinOrder (exists_lt)
export NoMaxOrder (exists_gt)

attribute [to_dual existing] noBotOrder_iff' noMinOrder_iff'

@[to_dual nonempty_gt]
/-
**nonempty_lt** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：nonempty_lt [LT α] [NoMinOrder α] (a : α) : Nonempty { x // x < a }
参数：a : α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
-/
instance nonempty_lt [LT α] [NoMinOrder α] (a : α) : Nonempty { x // x < a } :=
  nonempty_subtype.2 (exists_lt a)

@[to_dual]
/-
**IsEmpty.toNoMinOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsEmpty.toNoMinOrder [LT α] [IsEmpty α] : NoMinOrder α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsEmpty.toNoMinOrder [LT α] [IsEmpty α] : NoMinOrder α := ⟨isEmptyElim⟩

@[to_dual]
/-
**OrderDual.noBotOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.noBotOrder [LE α] [NoTopOrder α] : NoBotOrder αᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoTopOrder.exists_not_le`：∀ {α : Type u_3} {inst : LE α} [self : NoTopOr
der α] (a : α), ∃ b, ¬b ≤ a
-/
instance OrderDual.noBotOrder [LE α] [NoTopOrder α] : NoBotOrder αᵒᵈ :=
  ⟨fun a => exists_not_le (α := α) a⟩

@[to_dual]
/-
**OrderDual.noMinOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.noMinOrder [LT α] [NoMaxOrder α] : NoMinOrder αᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
-/
instance OrderDual.noMinOrder [LT α] [NoMaxOrder α] : NoMinOrder αᵒᵈ :=
  ⟨fun a => exists_gt (α := α) a⟩

-- See note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [Preorder α] [NoMinOrder α] : NoBotOrder α :=
  ⟨fun a => (exists_lt a).imp fun _ => not_le_of_gt⟩

@[to_dual]
/-
**noMinOrder_of_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：noMinOrder_of_left [Preorder α] [Preorder β] [NoMinOrder α] : NoMinOrder (
α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.mk_lt_mk_iff_left`：mk_lt_mk_iff_left : (a₁, b) < (a₂, b) ↔ a₁ < a₂
-/
instance noMinOrder_of_left [Preorder α] [Preorder β] [NoMinOrder α] : NoMinOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt a
    exact ⟨(c, b), Prod.mk_lt_mk_iff_left.2 h⟩⟩

@[to_dual]
/-
**noMinOrder_of_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：noMinOrder_of_right [Preorder α] [Preorder β] [NoMinOrder β] : NoMinOrder 
(α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.mk_lt_mk_iff_right`：mk_lt_mk_iff_right : (a, b₁) < (a, b₂) ↔ b₁ < b
₂
-/
instance noMinOrder_of_right [Preorder α] [Preorder β] [NoMinOrder β] : NoMinOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt b
    exact ⟨(a, c), Prod.mk_lt_mk_iff_right.2 h⟩⟩

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type u} {π : ι → Type*} [Nonempty ι] [∀ i, Preorder (π i)] [∀ i, NoMinOrder (π i)] :
    NoMinOrder (∀ i, π i) :=
  ⟨fun a => by
    classical
    obtain ⟨b, hb⟩ := exists_lt (a <| Classical.arbitrary _)
    exact ⟨_, update_lt_self_iff.2 hb⟩⟩

@[to_dual]
/-
**NoBotOrder.to_noMinOrder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NoBotOrder.to_noMinOrder (α : Type*) [LinearOrder α] [NoBotOrder α] : NoMi
nOrder α
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NoBotOrder.exists_not_ge`：∀ {α : Type u_3} {inst : LE α} [self : NoBotOr
der α] (a : α), ∃ b, ¬a ≤ b
-/
theorem NoBotOrder.to_noMinOrder (α : Type*) [LinearOrder α] [NoBotOrder α] : NoMinOrder α :=
  { exists_lt := fun a => by simpa [not_le] using exists_not_ge a }

@[to_dual]
/-
**noBotOrder_iff_noMinOrder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：noBotOrder_iff_noMinOrder (α : Type*) [LinearOrder α] : NoBotOrder α ↔ NoM
inOrder α
参数：α : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoBotOrder.to_noMinOrder`：NoBotOrder.to_noMinOrder (α : Type*) [LinearOr
der α] [NoBotOrder α] : NoMinOrder α
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
-/
theorem noBotOrder_iff_noMinOrder (α : Type*) [LinearOrder α] : NoBotOrder α ↔ NoMinOrder α :=
  ⟨fun _ => NoBotOrder.to_noMinOrder α, fun _ => inferInstance⟩

@[to_dual]
/-
**NoMinOrder.not_acc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NoMinOrder.not_acc [LT α] [NoMinOrder α] (a : α) : ¬Acc (· < ·) a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
-/
theorem NoMinOrder.not_acc [LT α] [NoMinOrder α] (a : α) : ¬Acc (· < ·) a := fun h =>
  Acc.recOn h fun x _ => (exists_lt x).recOn

section LE

variable [LE α] {a : α}

/-- `a : α` is a bottom element of `α` if it is less than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `OrderBot`, except that a preorder may have
several bottom elements. When `α` is linear, this is useful to make a case disjunction on
`NoMinOrder α` within a proof. -/
@[to_dual /--
`a : α` is a top element of `α` if it is greater than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `OrderBot`, except that a preorder may have
several top elements. When `α` is linear, this is useful to make a case disjunction on
`NoMaxOrder α` within a proof. -/]
/-
**IsBot** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsBot (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsBot (a : α) : Prop :=
  ∀ b, a ≤ b

/-- `a` is a minimal element of `α` if no element is strictly less than it. We spell it without `<`
to avoid having to convert between `≤` and `<`. Instead, `isMin_iff_forall_not_lt` does the
conversion. -/
@[to_dual /--
`a` is a maximal element of `α` if no element is strictly greater than it. We spell it without
`<` to avoid having to convert between `≤` and `<`. Instead, `isMax_iff_forall_not_lt` does the
conversion. -/]
/-
**IsMin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMin (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsMin (a : α) : Prop :=
  ∀ ⦃b⦄, b ≤ a → a ≤ b

@[to_dual]
/-
**noBotOrder_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：noBotOrder_iff : NoBotOrder α ↔ forall x : α, ¬ IsBot x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem noBotOrder_iff : NoBotOrder α ↔ ∀ x : α, ¬ IsBot x := by
  simp_rw [noBotOrder_iff', IsBot, not_forall]

@[to_dual (attr := simp)]
/-
**not_isBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isBot [NoBotOrder α] (a : α) : ¬IsBot a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoBotOrder.exists_not_ge`：∀ {α : Type u_3} {inst : LE α} [self : NoBotOr
der α] (a : α), ∃ b, ¬a ≤ b
-/
theorem not_isBot [NoBotOrder α] (a : α) : ¬IsBot a := fun h =>
  let ⟨_, hb⟩ := exists_not_ge a
  hb <| h _

@[to_dual]
/-
**IsBot.isMin** 是 Mathlib 中的一个定理，位于命名空间 `IsBot`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] {a : α}, IsBot a → IsMin a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem IsBot.isMin (h : IsBot a) : IsMin a := fun b _ => h b

@[to_dual]
/-
**IsBot.isMin_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBot.isMin_iff {α} [PartialOrder α] {i j : α} (h : IsBot i) : IsMin j ↔ j
 = i
参数：h : IsBot i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem IsBot.isMin_iff {α} [PartialOrder α] {i j : α} (h : IsBot i) : IsMin j ↔ j = i := by
  simp_rw [le_antisymm_iff, h j, and_true]
  exact ⟨fun a ↦ a (h j), fun a h' ↦ fun _ ↦ le_trans a (h h')⟩

@[to_dual (attr := simp)]
/-
**isBot_toDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBot_toDual_iff : IsBot (toDual a) ↔ IsTop a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBot_toDual_iff : IsBot (toDual a) ↔ IsTop a :=
  Iff.rfl

@[to_dual (attr := simp)]
/-
**isMin_toDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMin_toDual_iff : IsMin (toDual a) ↔ IsMax a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isMin_toDual_iff : IsMin (toDual a) ↔ IsMax a :=
  Iff.rfl

@[to_dual (attr := simp)]
/-
**isBot_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBot_ofDual_iff {a : αᵒᵈ} : IsBot (ofDual a) ↔ IsTop a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBot_ofDual_iff {a : αᵒᵈ} : IsBot (ofDual a) ↔ IsTop a :=
  Iff.rfl

@[to_dual (attr := simp)]
/-
**isMin_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMin_ofDual_iff {a : αᵒᵈ} : IsMin (ofDual a) ↔ IsMax a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isMin_ofDual_iff {a : αᵒᵈ} : IsMin (ofDual a) ↔ IsMax a :=
  Iff.rfl

@[to_dual]
alias ⟨_, IsTop.toDual⟩ := isBot_toDual_iff

@[to_dual]
alias ⟨_, IsMax.toDual⟩ := isMin_toDual_iff

@[to_dual]
alias ⟨_, IsTop.ofDual⟩ := isBot_ofDual_iff

@[to_dual]
alias ⟨_, IsMax.ofDual⟩ := isMin_ofDual_iff

end LE

section Preorder

variable [Preorder α] {a b : α}

@[to_dual]
/-
**noMinOrder_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：noMinOrder_iff : NoMinOrder α ↔ forall x : α, ¬ IsMin x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem noMinOrder_iff : NoMinOrder α ↔ ∀ x : α, ¬ IsMin x := by
  simp [noMinOrder_iff', IsMin, lt_iff_le_not_ge]

@[to_dual]
/-
**IsBot.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBot.mono (ha : IsBot a) (h : b <= a) : IsBot b
参数：ha : IsBot a；h : b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem IsBot.mono (ha : IsBot a) (h : b ≤ a) : IsBot b := fun _ => h.trans <| ha _

@[to_dual]
/-
**IsMin.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMin.mono (ha : IsMin a) (h : b <= a) : IsMin b
参数：ha : IsMin a；h : b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem IsMin.mono (ha : IsMin a) (h : b ≤ a) : IsMin b := fun _ hc => h.trans <| ha <| hc.trans h

@[to_dual]
/-
**IsMin.not_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMin.not_lt (h : IsMin a) : ¬b < a
参数：h : IsMin a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem IsMin.not_lt (h : IsMin a) : ¬b < a := fun hb => hb.not_ge <| h hb.le

@[to_dual]
/-
**not_isMin_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isMin_of_lt (h : b < a) : ¬IsMin a
参数：h : b < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMin.not_lt`：IsMin.not_lt (h : IsMin a) : ¬b < a
-/
theorem not_isMin_of_lt (h : b < a) : ¬IsMin a := fun ha => ha.not_lt h

@[to_dual]
alias LT.lt.not_isMin := not_isMin_of_lt

@[to_dual]
/-
**isMin_iff_forall_not_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMin_iff_forall_not_lt : IsMin a ↔ forall b, ¬b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMin.not_lt`：IsMin.not_lt (h : IsMin a) : ¬b < a
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `LE.le.lt_of_not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → ¬b ≤ a → a < b
-/
theorem isMin_iff_forall_not_lt : IsMin a ↔ ∀ b, ¬b < a :=
  ⟨fun h _ => h.not_lt, fun h _ hba => of_not_not fun hab => h _ <| hba.lt_of_not_ge hab⟩

@[to_dual (attr := simp)]
/-
**not_isMin_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isMin_iff : ¬IsMin a ↔ exists b, b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_isMin_iff : ¬IsMin a ↔ ∃ b, b < a := by
  simp [lt_iff_le_not_ge, IsMin, not_forall]

@[to_dual (attr := simp)]
/-
**not_isMin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_isMin_iff`：not_isMin_iff : ¬IsMin a ↔ exists b, b < a
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
-/
theorem not_isMin [NoMinOrder α] (a : α) : ¬IsMin a :=
  not_isMin_iff.2 <| exists_lt a

namespace Subsingleton

variable [Subsingleton α]

@[to_dual]
/-
**Subsingleton.isBot** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [Subsingleton α] (a : α), IsBot a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
protected theorem isBot (a : α) : IsBot a := fun _ => (Subsingleton.elim _ _).le

@[to_dual]
/-
**Subsingleton.isMin** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [Subsingleton α] (a : α), IsMin a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBot.isMin`：∀ {α : Type u_1} [inst : LE α] {a : α}, IsBot a → IsMin a
· 使用定理 `Subsingleton.isBot`：∀ {α : Type u_1} [inst : Preorder α] [Subsingleton α
] (a : α), IsBot a
-/
protected theorem isMin (a : α) : IsMin a :=
  (Subsingleton.isBot _).isMin

end Subsingleton

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

@[to_dual eq_of_ge]
/-
**IsMin.eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `IsMin`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsMin a → b ≤ a → b = 
a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
-/
protected theorem IsMin.eq_of_le (ha : IsMin a) (h : b ≤ a) : b = a :=
  h.antisymm <| ha h

@[to_dual eq_of_le]
/-
**IsMin.eq_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `IsMin`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsMin a → b ≤ a → a = 
b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
-/
protected theorem IsMin.eq_of_ge (ha : IsMin a) (h : b ≤ a) : a = b :=
  h.antisymm' <| ha h

@[to_dual lt_of_ne']
/-
**IsBot.lt_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `IsBot`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsBot a → a ≠ b → a < 
b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
-/
protected theorem IsBot.lt_of_ne (ha : IsBot a) (h : a ≠ b) : a < b :=
  (ha b).lt_of_ne h

@[to_dual lt_of_ne']
/-
**IsTop.lt_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `IsTop`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsTop a → b ≠ a → b < 
a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
-/
protected theorem IsTop.lt_of_ne (ha : IsTop a) (h : b ≠ a) : b < a :=
  (ha b).lt_of_ne h

@[to_dual]
/-
**IsBot.not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `IsBot`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {a : α} [Nontrivial α], IsBot a →
 ¬IsMax a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `IsMax.eq_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsMa
x a → a ≤ b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `IsBot.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsBo
t a → a ≠ b → a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
protected theorem IsBot.not_isMax [Nontrivial α] (ha : IsBot a) : ¬ IsMax a := by
  intro ha'
  obtain ⟨b, hb⟩ := exists_ne a
  exact hb <| ha'.eq_of_ge (ha.lt_of_ne hb.symm).le

@[to_dual]
/-
**IsBot.not_isTop** 是 Mathlib 中的一个定理，位于命名空间 `IsBot`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {a : α} [Nontrivial α], IsBot a →
 ¬IsTop a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `IsTop.isMax`：∀ {α : Type u_1} [inst : LE α] {a : α}, IsTop a → IsMax a
· 使用定理 `IsBot.not_isMax`：∀ {α : Type u_1} [inst : PartialOrder α] {a : α} [Nontr
ivial α], IsBot a → ¬IsMax a
-/
protected theorem IsBot.not_isTop [Nontrivial α] (ha : IsBot a) : ¬ IsTop a :=
  mt IsTop.isMax ha.not_isMax

end PartialOrder

section Prod

variable [Preorder α] [Preorder β] {a : α} {b : β} {x : α × β}

@[to_dual]
/-
**IsBot.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBot.prodMk (ha : IsBot a) (hb : IsBot b) : IsBot (a, b)
参数：ha : IsBot a；hb : IsBot b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsBot.prodMk (ha : IsBot a) (hb : IsBot b) : IsBot (a, b) := fun _ => ⟨ha _, hb _⟩

@[to_dual]
/-
**IsMin.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMin.prodMk (ha : IsMin a) (hb : IsMin b) : IsMin (a, b)
参数：ha : IsMin a；hb : IsMin b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsMin.prodMk (ha : IsMin a) (hb : IsMin b) : IsMin (a, b) := fun _ hc => ⟨ha hc.1, hb hc.2⟩

@[to_dual]
/-
**IsBot.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBot.fst (hx : IsBot x) : IsBot x.1
参数：hx : IsBot x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsBot.fst (hx : IsBot x) : IsBot x.1 := fun c => (hx (c, x.2)).1

@[to_dual]
/-
**IsBot.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBot.snd (hx : IsBot x) : IsBot x.2
参数：hx : IsBot x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsBot.snd (hx : IsBot x) : IsBot x.2 := fun c => (hx (x.1, c)).2

@[to_dual]
/-
**IsMin.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMin.fst (hx : IsMin x) : IsMin x.1
参数：hx : IsMin x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem IsMin.fst (hx : IsMin x) : IsMin x.1 :=
  fun c hc => (hx <| show (c, x.2) ≤ x from (and_iff_left le_rfl).2 hc).1

@[to_dual]
/-
**IsMin.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMin.snd (hx : IsMin x) : IsMin x.2
参数：hx : IsMin x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem IsMin.snd (hx : IsMin x) : IsMin x.2 :=
  fun c hc => (hx <| show (x.1, c) ≤ x from (and_iff_right le_rfl).2 hc).2

@[to_dual]
/-
**Prod.isBot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.isBot_iff : IsBot x ↔ IsBot x.1 ∧ IsBot x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBot.fst`：IsBot.fst (hx : IsBot x) : IsBot x.1
· 使用定理 `IsBot.snd`：IsBot.snd (hx : IsBot x) : IsBot x.2
· 使用定理 `IsBot.prodMk`：IsBot.prodMk (ha : IsBot a) (hb : IsBot b) : IsBot (a, b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Prod.isBot_iff : IsBot x ↔ IsBot x.1 ∧ IsBot x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prodMk h.2⟩

@[to_dual]
/-
**Prod.isMin_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.isMin_iff : IsMin x ↔ IsMin x.1 ∧ IsMin x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMin.fst`：IsMin.fst (hx : IsMin x) : IsMin x.1
· 使用定理 `IsMin.snd`：IsMin.snd (hx : IsMin x) : IsMin x.2
· 使用定理 `IsMin.prodMk`：IsMin.prodMk (ha : IsMin a) (hb : IsMin b) : IsMin (a, b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Prod.isMin_iff : IsMin x ↔ IsMin x.1 ∧ IsMin x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prodMk h.2⟩

end Prod

