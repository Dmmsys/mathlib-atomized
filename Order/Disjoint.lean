/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.BoundedOrder.Lattice

/-!
# Disjointness and complements

This file defines `Disjoint`, `Codisjoint`, and the `IsCompl` predicate.

## Main declarations

* `Disjoint x y`: two elements of a lattice are disjoint if their `inf` is the bottom element.
* `Codisjoint x y`: two elements of a lattice are codisjoint if their `join` is the top element.
* `IsCompl x y`: In a bounded lattice, predicate for "`x` is a complement of `y`". Note that in a
  non-distributive lattice, an element can have several complements.
* `ComplementedLattice α`: Typeclass stating that any element of a lattice has a complement.

-/

@[expose] public section

open Function

variable {α : Type*}

section Disjoint

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {a b c d : α}

/-- Two elements of a lattice are disjoint if their inf is the bottom element.
  (This generalizes disjoint sets, viewed as members of the subset lattice.)

Note that we define this without reference to `⊓`, as this allows us to talk about orders where
the infimum is not unique, or where implementing `Inf` would require additional `Decidable`
arguments. -/
@[to_dual /-- Two elements of a lattice are codisjoint if their sup is the top element.

Note that we define this without reference to `⊔`, as this allows us to talk about orders where
the supremum is not unique, or where implementing `Sup` would require additional `Decidable`
arguments. -/]
/-
**Disjoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Disjoint (a b : α) : Prop
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Disjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥

@[to_dual (attr := simp)]
/-
**disjoint_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_of_subsingleton [Subsingleton α] : Disjoint a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem disjoint_of_subsingleton [Subsingleton α] : Disjoint a b :=
  fun x _ _ ↦ le_of_eq (Subsingleton.elim x ⊥)

@[to_dual (attr := grind =)]
/-
**disjoint_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_comm : Disjoint a b ↔ Disjoint b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem disjoint_comm : Disjoint a b ↔ Disjoint b a :=
  forall_congr' fun _ ↦ forall_comm

@[to_dual (attr := symm)]
/-
**Disjoint.symm** 是 Mathlib 中的一个定理，位于命名空间 `Finmap`。
形式化陈述：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjoint y x
参数：x y : Finmap β；h : Disjoint x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
-/
theorem Disjoint.symm ⦃a b : α⦄ : Disjoint a b → Disjoint b a :=
  disjoint_comm.1

@[to_dual]
/-
**symm_disjoint** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：symm_disjoint : Std.Symm (Disjoint : α -> α -> Prop) where symm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
instance symm_disjoint : Std.Symm (Disjoint : α → α → Prop) where
  symm := Disjoint.symm

@[to_dual (attr := deprecated (since := "2026-06-10"))] alias symmetric_disjoint := symm_disjoint

@[to_dual (attr := simp, grind ←)]
/-
**disjoint_bot_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_bot_left : Disjoint ⊥ a
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_bot_left : Disjoint ⊥ a := fun _ hbot _ ↦ hbot

@[to_dual (attr := simp)]
/-
**disjoint_bot_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_bot_right : Disjoint a ⊥
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_bot_right : Disjoint a ⊥ := fun _ _ hbot ↦ hbot

@[to_dual (attr := gcongr)]
/-
**Disjoint.mono** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.support <= f.suppo
rt) (hg : y.support <= g.support) : Disjoint x y
参数：h : Disjoint f g；hf : x.support <= f.support；hg : y.support <= g.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem Disjoint.mono (h₁ : a ≤ b) (h₂ : c ≤ d) : Disjoint b d → Disjoint a c :=
  fun h _ ha hc ↦ h (ha.trans h₁) (hc.trans h₂)

@[to_dual]
/-
**Disjoint.mono_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Disjoint a c
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Disjoint.mono_left (h : a ≤ b) : Disjoint b c → Disjoint a c :=
  Disjoint.mono h le_rfl

grind_pattern Disjoint.mono_left => a ≤ b, Disjoint b c
grind_pattern Disjoint.mono_left => a ≤ b, Disjoint a c
grind_pattern Codisjoint.mono_left => a ≤ b, Codisjoint a c
grind_pattern Codisjoint.mono_left => a ≤ b, Codisjoint b c

@[to_dual]
/-
**Disjoint.mono_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.mono_right (h : b <= c) : Disjoint a c -> Disjoint a b
参数：h : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Disjoint.mono_right (h : b ≤ c) : Disjoint a c → Disjoint a b :=
  Disjoint.mono le_rfl h

-- Note: we don't need separate `grind` patterns for `Disjoint.mono_right` because `grind`
-- will use `disjoint_comm`.

@[to_dual]
/-
**Disjoint.out** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.out (h : Disjoint a b) (x : α) : x <= a -> x <= b -> x = ⊥
参数：h : Disjoint a b；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Disjoint.out (h : Disjoint a b) (x : α) : x ≤ a → x ≤ b → x = ⊥ :=
  fun h₁ h₂ => by simpa using h h₁ h₂

@[to_dual (attr := simp, grind =)]
/-
**disjoint_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_self : Disjoint a a ↔ a = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
-/
theorem disjoint_self : Disjoint a a ↔ a = ⊥ :=
  ⟨fun hd ↦ bot_unique <| hd le_rfl le_rfl, fun h _ ha _ ↦ ha.trans_eq h⟩

/- TODO: Rename `Disjoint.eq_bot` to `Disjoint.inf_eq` and `Disjoint.eq_bot_of_self` to
`Disjoint.eq_bot` -/
@[to_dual]
alias ⟨Disjoint.eq_bot_of_self, _⟩ := disjoint_self

@[to_dual]
/-
**Disjoint.ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.ne (ha : a != ⊥) (hab : Disjoint a b) : a != b
参数：ha : a != ⊥；hab : Disjoint a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Disjoint.ne (ha : a ≠ ⊥) (hab : Disjoint a b) : a ≠ b :=
  fun h ↦ ha <| disjoint_self.1 <| by rwa [← h] at hab

@[to_dual]
/-
**Disjoint.eq_bot_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.eq_bot_of_le (hab : Disjoint a b) (h : a <= b) : a = ⊥
参数：hab : Disjoint a b；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Disjoint.eq_bot_of_le (hab : Disjoint a b) (h : a ≤ b) : a = ⊥ :=
  eq_bot_iff.2 <| hab le_rfl h

grind_pattern Disjoint.eq_bot_of_le => Disjoint a b, a ≤ b
grind_pattern Codisjoint.eq_top_of_le => Codisjoint a b, b ≤ a

@[to_dual]
/-
**Disjoint.eq_bot_of_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.eq_bot_of_ge (hab : Disjoint a b) : b <= a -> b = ⊥
参数：hab : Disjoint a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.eq_bot_of_le`：Disjoint.eq_bot_of_le (hab : Disjoint a b) (h : a
 <= b) : a = ⊥
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
theorem Disjoint.eq_bot_of_ge (hab : Disjoint a b) : b ≤ a → b = ⊥ :=
  hab.symm.eq_bot_of_le

grind_pattern Disjoint.eq_bot_of_le => Disjoint a b, b ≤ a
grind_pattern Codisjoint.eq_top_of_ge => Codisjoint a b, a ≤ b
/-
**Disjoint.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Disjoint`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : OrderBot α] {a b : α}, 
Disjoint a b → (a = b ↔ a = ⊥ ∧ b = ⊥)
参数：a = b ↔ a = ⊥ ∧ b = ⊥。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual] lemma Disjoint.eq_iff (hab : Disjoint a b) : a = b ↔ a = ⊥ ∧ b = ⊥ := by grind
/-
**Disjoint.ne_iff** 是 Mathlib 中的一个定理，位于命名空间 `Disjoint`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : OrderBot α] {a b : α}, 
Disjoint a b → (a ≠ b ↔ a ≠ ⊥ ∨ b ≠ ⊥)
参数：a ≠ b ↔ a ≠ ⊥ ∨ b ≠ ⊥。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual] lemma Disjoint.ne_iff (hab : Disjoint a b) : a ≠ b ↔ a ≠ ⊥ ∨ b ≠ ⊥ := by grind
/-
**disjoint_of_le_iff_left_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_of_le_iff_left_eq_bot (h : a <= b) : Disjoint a b ↔ a = ⊥
参数：h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_of_le_iff_left_eq_bot (h : a ≤ b) :
    Disjoint a b ↔ a = ⊥ := by grind

end PartialOrderBot

section PartialBoundedOrder

variable [PartialOrder α] [BoundedOrder α] {a b : α}

@[to_dual (attr := simp, grind =)]
/-
**disjoint_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_top : Disjoint a ⊤ ↔ a = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
-/
theorem disjoint_top : Disjoint a ⊤ ↔ a = ⊥ :=
  ⟨fun h ↦ bot_unique <| h le_rfl le_top, fun h _ ha _ ↦ ha.trans_eq h⟩

@[to_dual (attr := simp, grind =)]
/-
**top_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：top_disjoint : Disjoint ⊤ a ↔ a = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
-/
theorem top_disjoint : Disjoint ⊤ a ↔ a = ⊥ :=
  ⟨fun h ↦ bot_unique <| h le_top le_rfl, fun h _ _ ha ↦ ha.trans_eq h⟩

@[to_dual]
/-
**Disjoint.ne_top_of_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.ne_top_of_ne_bot (h : Disjoint a b) (ha : a != ⊥) : b != ⊤
参数：h : Disjoint a b；ha : a != ⊥。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Disjoint.ne_top_of_ne_bot (h : Disjoint a b) (ha : a ≠ ⊥) : b ≠ ⊤ := by
  grind

end PartialBoundedOrder

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {a b c : α}

-- I would like to mark this as `@[grind =]`, but it results in excessive case splitting.
@[to_dual codisjoint_iff_le_sup]
/-
**disjoint_iff_inf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
-/
theorem disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b ≤ ⊥ :=
  ⟨fun hd ↦ hd inf_le_left inf_le_right, fun h _ ha hb ↦ (le_inf ha hb).trans h⟩

@[to_dual]
/-
**disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
-/
theorem disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥ :=
  disjoint_iff_inf_le.trans le_bot_iff

@[to_dual (attr := simp)]
/-
**disjoint_subtype_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjoint_subtype_iff {pr : α -> Prop} (Pinf : forall ⦃s t : α⦄, pr s -> pr
 t -> pr (s ⊓ t)) (hbot : pr (⊥ : α)) {a b : Subtype pr} : letI : SemilatticeInf
 (Subtype pr)
参数：Pinf : forall ⦃s t : α⦄, pr s -> pr t -> pr (s ⊓ t)；hbot : pr (⊥ : α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {P : α → Prop}
 (Pinf : ∀ ⦃x y : α⦄, P x → P y → P (x ⊓ y)) (x y : Subtype P),   ↑(x ⊓ y) = ↑x 
⊓ ↑y
· 使用定理 `Subtype.coe_bot`：Subtype.coe_bot {s : Set Nat} [DecidablePred (· in s)] 
[h : Nonempty s] : ((⊥ : s) : Nat) = Nat.find (nonempty_subtype.1 h)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
-/
lemma disjoint_subtype_iff {pr : α → Prop} (Pinf : ∀ ⦃s t : α⦄, pr s → pr t → pr (s ⊓ t))
    (hbot : pr (⊥ : α)) {a b : Subtype pr} :
    letI : SemilatticeInf (Subtype pr) := Subtype.semilatticeInf Pinf
    letI : OrderBot (Subtype pr) := Subtype.orderBot hbot
    Disjoint a b ↔ Disjoint a.val b.val := by
  let : SemilatticeInf (Subtype pr) := Subtype.semilatticeInf Pinf
  let : OrderBot (Subtype pr) := Subtype.orderBot hbot
  rw [disjoint_iff, disjoint_iff, ← Subtype.coe_inf Pinf, ← Subtype.coe_bot hbot]
  exact Subtype.coe_inj.symm

@[to_dual top_le]
/-
**Disjoint.le_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
-/
theorem Disjoint.le_bot : Disjoint a b → a ⊓ b ≤ ⊥ :=
  disjoint_iff_inf_le.mp

@[to_dual]
/-
**Disjoint.eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
-/
theorem Disjoint.eq_bot : Disjoint a b → a ⊓ b = ⊥ :=
  bot_unique ∘ Disjoint.le_bot

@[to_dual]
/-
**disjoint_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_assoc : Disjoint (a ⊓ b) c ↔ Disjoint a (b ⊓ c)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_assoc : Disjoint (a ⊓ b) c ↔ Disjoint a (b ⊓ c) := by
  grind [disjoint_iff_inf_le]

@[to_dual]
/-
**disjoint_left_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_left_comm : Disjoint a (b ⊓ c) ↔ Disjoint b (a ⊓ c)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_left_comm : Disjoint a (b ⊓ c) ↔ Disjoint b (a ⊓ c) := by
  grind [disjoint_iff_inf_le]

@[to_dual]
/-
**disjoint_right_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_right_comm : Disjoint (a ⊓ b) c ↔ Disjoint (a ⊓ c) b
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_right_comm : Disjoint (a ⊓ b) c ↔ Disjoint (a ⊓ c) b := by
  grind [disjoint_iff_inf_le]

variable (c)

@[to_dual]
/-
**Disjoint.inf_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.inf_left (h : Disjoint a b) : Disjoint (a ⊓ c) b
参数：h : Disjoint a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem Disjoint.inf_left (h : Disjoint a b) : Disjoint (a ⊓ c) b :=
  h.mono_left inf_le_left

@[to_dual]
/-
**Disjoint.inf_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.inf_left' (h : Disjoint a b) : Disjoint (c ⊓ a) b
参数：h : Disjoint a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem Disjoint.inf_left' (h : Disjoint a b) : Disjoint (c ⊓ a) b :=
  h.mono_left inf_le_right

@[to_dual]
/-
**Disjoint.inf_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.inf_right (h : Disjoint a b) : Disjoint a (b ⊓ c)
参数：h : Disjoint a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem Disjoint.inf_right (h : Disjoint a b) : Disjoint a (b ⊓ c) :=
  h.mono_right inf_le_left

@[to_dual]
/-
**Disjoint.inf_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.inf_right' (h : Disjoint a b) : Disjoint a (c ⊓ b)
参数：h : Disjoint a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem Disjoint.inf_right' (h : Disjoint a b) : Disjoint a (c ⊓ b) :=
  h.mono_right inf_le_right

variable {c}

@[to_dual]
/-
**Disjoint.of_disjoint_inf_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.of_disjoint_inf_of_le (h : Disjoint (a ⊓ b) c) (hle : a <= c) : D
isjoint a b
参数：h : Disjoint (a ⊓ b) c；hle : a <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Disjoint.eq_bot_of_le`：Disjoint.eq_bot_of_le (hab : Disjoint a b) (h : a
 <= b) : a = ⊥
· 使用定理 `inf_le_of_left_le`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α},
 a ≤ c → a ⊓ b ≤ c
-/
theorem Disjoint.of_disjoint_inf_of_le (h : Disjoint (a ⊓ b) c) (hle : a ≤ c) : Disjoint a b :=
  disjoint_iff.2 <| h.eq_bot_of_le <| inf_le_of_left_le hle

@[to_dual]
/-
**Disjoint.of_disjoint_inf_of_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.of_disjoint_inf_of_le' (h : Disjoint (a ⊓ b) c) (hle : b <= c) : 
Disjoint a b
参数：h : Disjoint (a ⊓ b) c；hle : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Disjoint.eq_bot_of_le`：Disjoint.eq_bot_of_le (hab : Disjoint a b) (h : a
 <= b) : a = ⊥
· 使用定理 `inf_le_of_right_le`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α}
, b ≤ c → a ⊓ b ≤ c
-/
theorem Disjoint.of_disjoint_inf_of_le' (h : Disjoint (a ⊓ b) c) (hle : b ≤ c) : Disjoint a b :=
  disjoint_iff.2 <| h.eq_bot_of_le <| inf_le_of_right_le hle

end SemilatticeInfBot

@[to_dual sup_lt_right_of_left_ne_bot]
/-
**Disjoint.right_lt_sup_of_left_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.right_lt_sup_of_left_ne_bot [SemilatticeSup α] [OrderBot α] {a b 
: α} (h : Disjoint a b) (ha : a != ⊥) : b < a ⊔ b
参数：h : Disjoint a b；ha : a != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Disjoint.right_lt_sup_of_left_ne_bot [SemilatticeSup α] [OrderBot α] {a b : α}
    (h : Disjoint a b) (ha : a ≠ ⊥) : b < a ⊔ b :=
  le_sup_right.lt_of_ne fun eq ↦ ha (le_bot_iff.mp <| h le_rfl <| sup_eq_right.mp eq.symm)

section DistribLatticeBot

variable [DistribLattice α] [OrderBot α] {a b c : α}

@[simp]
/-
**disjoint_sup_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_sup_left : Disjoint (a ⊔ b) c ↔ Disjoint a c ∧ Disjoint b c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_sup_left : Disjoint (a ⊔ b) c ↔ Disjoint a c ∧ Disjoint b c := by
  simp only [disjoint_iff, inf_sup_right, sup_eq_bot_iff]

@[simp]
/-
**disjoint_sup_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_sup_right : Disjoint a (b ⊔ c) ↔ Disjoint a b ∧ Disjoint a c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_sup_right : Disjoint a (b ⊔ c) ↔ Disjoint a b ∧ Disjoint a c := by
  simp only [disjoint_iff, inf_sup_left, sup_eq_bot_iff]
/-
**Disjoint.sup_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.sup_left (ha : Disjoint a c) (hb : Disjoint b c) : Disjoint (a ⊔ 
b) c
参数：ha : Disjoint a c；hb : Disjoint b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_sup_left`：disjoint_sup_left : Disjoint (a ⊔ b) c ↔ Disjoint a c
 ∧ Disjoint b c
-/
theorem Disjoint.sup_left (ha : Disjoint a c) (hb : Disjoint b c) : Disjoint (a ⊔ b) c :=
  disjoint_sup_left.2 ⟨ha, hb⟩
/-
**Disjoint.sup_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.sup_right (hb : Disjoint a b) (hc : Disjoint a c) : Disjoint a (b
 ⊔ c)
参数：hb : Disjoint a b；hc : Disjoint a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_sup_right`：disjoint_sup_right : Disjoint a (b ⊔ c) ↔ Disjoint a
 b ∧ Disjoint a c
-/
theorem Disjoint.sup_right (hb : Disjoint a b) (hc : Disjoint a c) : Disjoint a (b ⊔ c) :=
  disjoint_sup_right.2 ⟨hb, hc⟩
/-
**Disjoint.left_le_of_le_sup_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.left_le_of_le_sup_right (h : a <= b ⊔ c) (hd : Disjoint a c) : a 
<= b
参数：h : a <= b ⊔ c；hd : Disjoint a c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_inf_le_sup_le`：le_of_inf_le_sup_le (h₁ : x ⊓ z <= y ⊓ z) (h₂ : x ⊔
 z <= y ⊔ z) : x <= y
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem Disjoint.left_le_of_le_sup_right (h : a ≤ b ⊔ c) (hd : Disjoint a c) : a ≤ b :=
  le_of_inf_le_sup_le (le_trans hd.le_bot bot_le) <| sup_le h le_sup_right
/-
**Disjoint.left_le_of_le_sup_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.left_le_of_le_sup_left (h : a <= c ⊔ b) (hd : Disjoint a c) : a <
= b
参数：h : a <= c ⊔ b；hd : Disjoint a c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.left_le_of_le_sup_right`：Disjoint.left_le_of_le_sup_right (h : 
a <= b ⊔ c) (hd : Disjoint a c) : a <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem Disjoint.left_le_of_le_sup_left (h : a ≤ c ⊔ b) (hd : Disjoint a c) : a ≤ b :=
  hd.left_le_of_le_sup_right <| by rwa [sup_comm]

end DistribLatticeBot

end Disjoint

section Codisjoint

section DistribLatticeTop

variable [DistribLattice α] [OrderTop α] {a b c : α}

@[simp]
/-
**codisjoint_inf_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：codisjoint_inf_left : Codisjoint (a ⊓ b) c ↔ Codisjoint a c ∧ Codisjoint b
 c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem codisjoint_inf_left : Codisjoint (a ⊓ b) c ↔ Codisjoint a c ∧ Codisjoint b c := by
  simp only [codisjoint_iff, sup_inf_right, inf_eq_top_iff]

@[simp]
/-
**codisjoint_inf_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：codisjoint_inf_right : Codisjoint a (b ⊓ c) ↔ Codisjoint a b ∧ Codisjoint 
a c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem codisjoint_inf_right : Codisjoint a (b ⊓ c) ↔ Codisjoint a b ∧ Codisjoint a c := by
  simp only [codisjoint_iff, sup_inf_left, inf_eq_top_iff]
/-
**Codisjoint.inf_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Codisjoint.inf_left (ha : Codisjoint a c) (hb : Codisjoint b c) : Codisjoi
nt (a ⊓ b) c
参数：ha : Codisjoint a c；hb : Codisjoint b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `codisjoint_inf_left`：codisjoint_inf_left : Codisjoint (a ⊓ b) c ↔ Codisj
oint a c ∧ Codisjoint b c
-/
theorem Codisjoint.inf_left (ha : Codisjoint a c) (hb : Codisjoint b c) : Codisjoint (a ⊓ b) c :=
  codisjoint_inf_left.2 ⟨ha, hb⟩
/-
**Codisjoint.inf_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Codisjoint.inf_right (hb : Codisjoint a b) (hc : Codisjoint a c) : Codisjo
int a (b ⊓ c)
参数：hb : Codisjoint a b；hc : Codisjoint a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `codisjoint_inf_right`：codisjoint_inf_right : Codisjoint a (b ⊓ c) ↔ Codi
sjoint a b ∧ Codisjoint a c
-/
theorem Codisjoint.inf_right (hb : Codisjoint a b) (hc : Codisjoint a c) : Codisjoint a (b ⊓ c) :=
  codisjoint_inf_right.2 ⟨hb, hc⟩
/-
**Codisjoint.left_le_of_le_inf_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Codisjoint.left_le_of_le_inf_right (h : a ⊓ b <= c) (hd : Codisjoint b c) 
: a <= c
参数：h : a ⊓ b <= c；hd : Codisjoint b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.left_le_of_le_sup_right`：Disjoint.left_le_of_le_sup_right (h : 
a <= b ⊔ c) (hd : Disjoint a c) : a <= b
· 使用定理 `Codisjoint.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Orde
rTop α] ⦃a b : α⦄, Codisjoint a b → Codisjoint b a
-/
theorem Codisjoint.left_le_of_le_inf_right (h : a ⊓ b ≤ c) (hd : Codisjoint b c) : a ≤ c :=
  @Disjoint.left_le_of_le_sup_right αᵒᵈ _ _ _ _ _ h hd.symm
/-
**Codisjoint.left_le_of_le_inf_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Codisjoint.left_le_of_le_inf_left (h : b ⊓ a <= c) (hd : Codisjoint b c) :
 a <= c
参数：h : b ⊓ a <= c；hd : Codisjoint b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Codisjoint.left_le_of_le_inf_right`：Codisjoint.left_le_of_le_inf_right (
h : a ⊓ b <= c) (hd : Codisjoint b c) : a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
theorem Codisjoint.left_le_of_le_inf_left (h : b ⊓ a ≤ c) (hd : Codisjoint b c) : a ≤ c :=
  hd.left_le_of_le_inf_right <| by rwa [inf_comm]

end DistribLatticeTop

end Codisjoint

open OrderDual

@[to_dual]
/-
**Disjoint.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.dual [PartialOrder α] [OrderBot α] {a b : α} : Disjoint a b -> Co
disjoint (toDual a) (toDual b)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Disjoint.dual [PartialOrder α] [OrderBot α] {a b : α} :
    Disjoint a b → Codisjoint (toDual a) (toDual b) :=
  id

@[to_dual (attr := simp, grind =)]
/-
**disjoint_toDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_toDual_iff [PartialOrder α] [OrderTop α] {a b : α} : Disjoint (to
Dual a) (toDual b) ↔ Codisjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_toDual_iff [PartialOrder α] [OrderTop α] {a b : α} :
    Disjoint (toDual a) (toDual b) ↔ Codisjoint a b :=
  Iff.rfl

@[to_dual (attr := simp, grind =)]
/-
**disjoint_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_ofDual_iff [PartialOrder α] [OrderBot α] {a b : αᵒᵈ} : Disjoint (
ofDual a) (ofDual b) ↔ Codisjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_ofDual_iff [PartialOrder α] [OrderBot α] {a b : αᵒᵈ} :
    Disjoint (ofDual a) (ofDual b) ↔ Codisjoint a b :=
  Iff.rfl

section DistribLattice

variable [DistribLattice α] [BoundedOrder α] {a b c : α}

@[to_dual]
/-
**Disjoint.le_of_codisjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.le_of_codisjoint (hab : Disjoint a b) (hbc : Codisjoint b c) : a 
<= c
参数：hab : Disjoint a b；hbc : Codisjoint b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `Codisjoint.eq_top`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → a ⊔ b = ⊤
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
· 使用定理 `inf_le_inf_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c 
: α), b ≤ a → b ⊓ c ≤ a ⊓ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem Disjoint.le_of_codisjoint (hab : Disjoint a b) (hbc : Codisjoint b c) : a ≤ c := by
  rw [← @inf_top_eq _ _ _ a, ← @bot_sup_eq _ _ _ c, ← hab.eq_bot, ← hbc.eq_top, sup_inf_right]
  exact inf_le_inf_right _ le_sup_left

end DistribLattice

section IsCompl

/-- Two elements `x` and `y` are complements of each other if `x ⊔ y = ⊤` and `x ⊓ y = ⊥`. -/
/-
**IsCompl** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：IsCompl [PartialOrder α] [BoundedOrder α] (x y : α) : Prop where /-- If `x
` and `y` are to be complementary in an order, they should be disjoint. -/ prote
cted disjoint : Disjoint x y /-- If `x` and `y` are to be complementary in an or
der, they should be codisjoint. -/ protected codisjoint : Codisjoint x y  attrib
ute [to_dual existing] IsCompl.disjoint attribute [to_dual self (reorder
参数：x y : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two elements `x` and `y` are complements of each other if `x ⊔ y = ⊤` and `x ⊓ y
 = ⊥`.
-/
structure IsCompl [PartialOrder α] [BoundedOrder α] (x y : α) : Prop where
  /-- If `x` and `y` are to be complementary in an order, they should be disjoint. -/
  protected disjoint : Disjoint x y
  /-- If `x` and `y` are to be complementary in an order, they should be codisjoint. -/
  protected codisjoint : Codisjoint x y

attribute [to_dual existing] IsCompl.disjoint
attribute [to_dual self (reorder := disjoint codisjoint)] IsCompl.mk

@[to_dual isCompl_iff']
/-
**isCompl_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompl_iff [PartialOrder α] [BoundedOrder α] {a b : α} : IsCompl a b ↔ Di
sjoint a b ∧ Codisjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isCompl_iff [PartialOrder α] [BoundedOrder α] {a b : α} :
    IsCompl a b ↔ Disjoint a b ∧ Codisjoint a b :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

namespace IsCompl

section BoundedPartialOrder

variable [PartialOrder α] [BoundedOrder α] {x y : α}

@[symm]
/-
**IsCompl.symm** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : BoundedOrder α] {x y : 
α}, IsCompl x y → IsCompl y x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Codisjoint.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Orde
rTop α] ⦃a b : α⦄, Codisjoint a b → Codisjoint b a
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
-/
protected theorem symm (h : IsCompl x y) : IsCompl y x :=
  ⟨h.1.symm, h.2.symm⟩

@[grind =]
/-
**IsCompl._root_.isCompl_comm** 是 Mathlib 中的一个引理，位于命名空间 `IsCompl`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.isCompl_comm : IsCompl x y ↔ IsCompl y x := ⟨IsCompl.symm, IsCompl.symm⟩
/-
**IsCompl.dual** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：dual (h : IsCompl x y) : IsCompl (toDual x) (toDual y)
参数：h : IsCompl x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
-/
theorem dual (h : IsCompl x y) : IsCompl (toDual x) (toDual y) :=
  ⟨h.2, h.1⟩
/-
**IsCompl.ofDual** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：ofDual {a b : αᵒᵈ} (h : IsCompl a b) : IsCompl (ofDual a) (ofDual b)
参数：h : IsCompl a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
-/
theorem ofDual {a b : αᵒᵈ} (h : IsCompl a b) : IsCompl (ofDual a) (ofDual b) :=
  ⟨h.2, h.1⟩

end BoundedPartialOrder

section BoundedLattice

variable [Lattice α] [BoundedOrder α] {x y : α}

@[to_dual self (reorder := h₁ h₂)]
/-
**IsCompl.of_le** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：of_le (h₁ : x ⊓ y <= ⊥) (h₂ : ⊤ <= x ⊔ y) : IsCompl x y
参数：h₁ : x ⊓ y <= ⊥；h₂ : ⊤ <= x ⊔ y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_le (h₁ : x ⊓ y ≤ ⊥) (h₂ : ⊤ ≤ x ⊔ y) : IsCompl x y :=
  ⟨by grind [disjoint_iff_inf_le], by grind [codisjoint_iff_le_sup]⟩

@[to_dual self (reorder := h₁ h₂)]
/-
**IsCompl.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : IsCompl x y
参数：h₁ : x ⊓ y = ⊥；h₂ : x ⊔ y = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
-/
theorem of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : IsCompl x y :=
  ⟨disjoint_iff.mpr h₁, codisjoint_iff.mpr h₂⟩

@[to_dual]
/-
**IsCompl.inf_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥
参数：h : IsCompl x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
-/
theorem inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥ :=
  h.disjoint.eq_bot

end BoundedLattice

variable [DistribLattice α] [BoundedOrder α] {a b x y z : α}

/-
**IsCompl.inf_left_le_of_le_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：inf_left_le_of_le_sup_right (h : IsCompl x y) (hle : a <= b ⊔ y) : a ⊓ x <
= b
参数：h : IsCompl x y；hle : a <= b ⊔ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompl.inf_eq_bot`：inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem inf_left_le_of_le_sup_right (h : IsCompl x y) (hle : a ≤ b ⊔ y) : a ⊓ x ≤ b :=
  calc
    a ⊓ x ≤ (b ⊔ y) ⊓ x := inf_le_inf hle le_rfl
    _ = b ⊓ x ⊔ y ⊓ x := inf_sup_right _ _ _
    _ = b ⊓ x := by rw [h.symm.inf_eq_bot, sup_bot_eq]
    _ ≤ b := inf_le_left
/-
**IsCompl.le_sup_right_iff_inf_left_le** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：le_sup_right_iff_inf_left_le {a b} (h : IsCompl x y) : a <= b ⊔ y ↔ a ⊓ x 
<= b
参数：h : IsCompl x y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.inf_left_le_of_le_sup_right`：inf_left_le_of_le_sup_right (h : Is
Compl x y) (hle : a <= b ⊔ y) : a ⊓ x <= b
· 使用定理 `IsCompl.dual`：dual (h : IsCompl x y) : IsCompl (toDual x) (toDual y)
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
-/
theorem le_sup_right_iff_inf_left_le {a b} (h : IsCompl x y) : a ≤ b ⊔ y ↔ a ⊓ x ≤ b :=
  ⟨h.inf_left_le_of_le_sup_right, h.symm.dual.inf_left_le_of_le_sup_right⟩
/-
**IsCompl.inf_left_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：inf_left_eq_bot_iff (h : IsCompl y z) : x ⊓ y = ⊥ ↔ x <= z
参数：h : IsCompl y z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `IsCompl.le_sup_right_iff_inf_left_le`：le_sup_right_iff_inf_left_le {a b}
 (h : IsCompl x y) : a <= b ⊔ y ↔ a ⊓ x <= b
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inf_left_eq_bot_iff (h : IsCompl y z) : x ⊓ y = ⊥ ↔ x ≤ z := by
  rw [← le_bot_iff, ← h.le_sup_right_iff_inf_left_le, bot_sup_eq]
/-
**IsCompl.inf_right_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：inf_right_eq_bot_iff (h : IsCompl y z) : x ⊓ z = ⊥ ↔ x <= y
参数：h : IsCompl y z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.inf_left_eq_bot_iff`：inf_left_eq_bot_iff (h : IsCompl y z) : x ⊓
 y = ⊥ ↔ x <= z
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
-/
theorem inf_right_eq_bot_iff (h : IsCompl y z) : x ⊓ z = ⊥ ↔ x ≤ y :=
  h.symm.inf_left_eq_bot_iff
/-
**IsCompl.disjoint_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：disjoint_left_iff (h : IsCompl y z) : Disjoint x y ↔ x <= z
参数：h : IsCompl y z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `IsCompl.inf_left_eq_bot_iff`：inf_left_eq_bot_iff (h : IsCompl y z) : x ⊓
 y = ⊥ ↔ x <= z
-/
theorem disjoint_left_iff (h : IsCompl y z) : Disjoint x y ↔ x ≤ z := by
  rw [disjoint_iff]
  exact h.inf_left_eq_bot_iff
/-
**IsCompl.disjoint_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：disjoint_right_iff (h : IsCompl y z) : Disjoint x z ↔ x <= y
参数：h : IsCompl y z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.disjoint_left_iff`：disjoint_left_iff (h : IsCompl y z) : Disjoin
t x y ↔ x <= z
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
-/
theorem disjoint_right_iff (h : IsCompl y z) : Disjoint x z ↔ x ≤ y :=
  h.symm.disjoint_left_iff
/-
**IsCompl.le_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：le_left_iff (h : IsCompl x y) : z <= x ↔ Disjoint z y
参数：h : IsCompl x y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `IsCompl.disjoint_right_iff`：disjoint_right_iff (h : IsCompl y z) : Disjo
int x z ↔ x <= y
-/
theorem le_left_iff (h : IsCompl x y) : z ≤ x ↔ Disjoint z y :=
  h.disjoint_right_iff.symm
/-
**IsCompl.le_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：le_right_iff (h : IsCompl x y) : z <= y ↔ Disjoint z x
参数：h : IsCompl x y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.le_left_iff`：le_left_iff (h : IsCompl x y) : z <= x ↔ Disjoint z
 y
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
-/
theorem le_right_iff (h : IsCompl x y) : z ≤ y ↔ Disjoint z x :=
  h.symm.le_left_iff
/-
**IsCompl.left_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：left_le_iff (h : IsCompl x y) : x <= z ↔ Codisjoint z y
参数：h : IsCompl x y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.le_left_iff`：le_left_iff (h : IsCompl x y) : z <= x ↔ Disjoint z
 y
· 使用定理 `IsCompl.dual`：dual (h : IsCompl x y) : IsCompl (toDual x) (toDual y)
-/
theorem left_le_iff (h : IsCompl x y) : x ≤ z ↔ Codisjoint z y :=
  h.dual.le_left_iff
/-
**IsCompl.right_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：right_le_iff (h : IsCompl x y) : y <= z ↔ Codisjoint z x
参数：h : IsCompl x y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.left_le_iff`：left_le_iff (h : IsCompl x y) : x <= z ↔ Codisjoint
 z y
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
-/
theorem right_le_iff (h : IsCompl x y) : y ≤ z ↔ Codisjoint z x :=
  h.symm.left_le_iff
/-
**IsCompl.Antitone** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：∀ {α : Type u_1} [inst : DistribLattice α] [inst_1 : BoundedOrder α] {x y 
x' y' : α},   IsCompl x y → IsCompl x' y' → x ≤ x' → y' ≤ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsCompl.right_le_iff`：right_le_iff (h : IsCompl x y) : y <= z ↔ Codisjoi
nt z x
· 使用定理 `Codisjoint.mono_right`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 
: OrderTop α] {a b c : α}, c ≤ b → Codisjoint a c → Codisjoint a b
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
-/
protected theorem Antitone {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') (hx : x ≤ x') : y' ≤ y :=
  h'.right_le_iff.2 <| h.symm.codisjoint.mono_right hx
/-
**IsCompl.right_unique** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：right_unique (hxy : IsCompl x y) (hxz : IsCompl x z) : y = z
参数：hxy : IsCompl x y；hxz : IsCompl x z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsCompl.Antitone`：∀ {α : Type u_1} [inst : DistribLattice α] [inst_1 : B
oundedOrder α] {x y x' y' : α},   IsCompl x y → IsCompl x' y' → x ≤ x' → y' ≤ y
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem right_unique (hxy : IsCompl x y) (hxz : IsCompl x z) : y = z :=
  le_antisymm (hxz.Antitone hxy <| le_refl x) (hxy.Antitone hxz <| le_refl x)
/-
**IsCompl.left_unique** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：left_unique (hxz : IsCompl x z) (hyz : IsCompl y z) : x = y
参数：hxz : IsCompl x z；hyz : IsCompl y z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.right_unique`：right_unique (hxy : IsCompl x y) (hxz : IsCompl x 
z) : y = z
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
-/
theorem left_unique (hxz : IsCompl x z) (hyz : IsCompl y z) : x = y :=
  hxz.symm.right_unique hyz.symm
/-
**IsCompl.sup_inf** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：sup_inf {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') : IsCompl (x ⊔ x') 
(y ⊓ y')
参数：h : IsCompl x y；h' : IsCompl x' y'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.of_eq`：of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : IsCompl x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `IsCompl.inf_eq_bot`：inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥
· 使用定理 `bot_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊓ a = ⊥
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
· 使用定理 `inf_left_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓
 (b ⊓ c) = b ⊓ (a ⊓ c)
· 使用定理 `inf_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), a ⊓ ⊥ = ⊥
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用定理 `sup_top_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderTo
p α] (a : α), a ⊔ ⊤ = ⊤
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
· 使用定理 `sup_left_comm`：sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c)
-/
theorem sup_inf {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') : IsCompl (x ⊔ x') (y ⊓ y') :=
  of_eq
    (by rw [inf_sup_right, ← inf_assoc, h.inf_eq_bot, bot_inf_eq, bot_sup_eq, inf_left_comm,
      h'.inf_eq_bot, inf_bot_eq])
    (by rw [sup_inf_left, sup_comm x, sup_assoc, h.sup_eq_top, sup_top_eq, top_inf_eq,
      sup_assoc, sup_left_comm, h'.sup_eq_top, sup_top_eq])
/-
**IsCompl.inf_sup** 是 Mathlib 中的一个定理，位于命名空间 `IsCompl`。
形式化陈述：inf_sup {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') : IsCompl (x ⊓ x') 
(y ⊔ y')
参数：h : IsCompl x y；h' : IsCompl x' y'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `IsCompl.sup_inf`：sup_inf {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') 
: IsCompl (x ⊔ x') (y ⊓ y')
-/
theorem inf_sup {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') : IsCompl (x ⊓ x') (y ⊔ y') :=
  (h.symm.sup_inf h'.symm).symm

end IsCompl

namespace Prod

variable {β : Type*} [PartialOrder α] [PartialOrder β]

@[grind =]
/-
**Prod.disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PartialOrder α] [inst_1 : PartialO
rder β] [inst_2 : OrderBot α]   [inst_3 : OrderBot β] {x y : α × β}, Disjoint x 
y ↔ Disjoint x.1 y.1 ∧ Disjoint x.2 y.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem disjoint_iff [OrderBot α] [OrderBot β] {x y : α × β} :
    Disjoint x y ↔ Disjoint x.1 y.1 ∧ Disjoint x.2 y.2 := by
  constructor
  · intro h
    refine ⟨fun a hx hy ↦ (@h (a, ⊥) ⟨hx, ?_⟩ ⟨hy, ?_⟩).1,
      fun b hx hy ↦ (@h (⊥, b) ⟨?_, hx⟩ ⟨?_, hy⟩).2⟩
    all_goals exact bot_le
  · rintro ⟨ha, hb⟩ z hza hzb
    exact ⟨ha hza.1 hzb.1, hb hza.2 hzb.2⟩

@[grind =]
/-
**Prod.codisjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PartialOrder α] [inst_1 : PartialO
rder β] [inst_2 : OrderTop α]   [inst_3 : OrderTop β] {x y : α × β}, Codisjoint 
x y ↔ Codisjoint x.1 y.1 ∧ Codisjoint x.2 y.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.disjoint_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : PartialOrder 
α] [inst_1 : PartialOrder β] [inst_2 : OrderBot α]   [inst_3 : OrderBot β] {x y 
: α × β…
-/
protected theorem codisjoint_iff [OrderTop α] [OrderTop β] {x y : α × β} :
    Codisjoint x y ↔ Codisjoint x.1 y.1 ∧ Codisjoint x.2 y.2 :=
  @Prod.disjoint_iff αᵒᵈ βᵒᵈ _ _ _ _ _ _

@[grind =]
/-
**Prod.isCompl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PartialOrder α] [inst_1 : PartialO
rder β] [inst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β] {x y : α × β}, IsC
ompl x y ↔ IsCompl x.1 y.1 ∧ IsCompl x.2 y.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem isCompl_iff [BoundedOrder α] [BoundedOrder β] {x y : α × β} :
    IsCompl x y ↔ IsCompl x.1 y.1 ∧ IsCompl x.2 y.2 := by
  simp_rw [isCompl_iff, Prod.disjoint_iff, Prod.codisjoint_iff, and_and_and_comm]

end Prod

section

variable [Lattice α] [BoundedOrder α] {a b x : α}

@[simp, grind =]
/-
**isCompl_toDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompl_toDual_iff : IsCompl (toDual a) (toDual b) ↔ IsCompl a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.ofDual`：ofDual {a b : αᵒᵈ} (h : IsCompl a b) : IsCompl (ofDual a
) (ofDual b)
· 使用定理 `IsCompl.dual`：dual (h : IsCompl x y) : IsCompl (toDual x) (toDual y)
-/
theorem isCompl_toDual_iff : IsCompl (toDual a) (toDual b) ↔ IsCompl a b :=
  ⟨IsCompl.ofDual, IsCompl.dual⟩

@[simp, grind =]
/-
**isCompl_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompl_ofDual_iff {a b : αᵒᵈ} : IsCompl (ofDual a) (ofDual b) ↔ IsCompl a
 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.dual`：dual (h : IsCompl x y) : IsCompl (toDual x) (toDual y)
· 使用定理 `IsCompl.ofDual`：ofDual {a b : αᵒᵈ} (h : IsCompl a b) : IsCompl (ofDual a
) (ofDual b)
-/
theorem isCompl_ofDual_iff {a b : αᵒᵈ} : IsCompl (ofDual a) (ofDual b) ↔ IsCompl a b :=
  ⟨IsCompl.dual, IsCompl.ofDual⟩
/-
**isCompl_bot_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompl_bot_top : IsCompl (⊥ : α) ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.of_eq`：of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : IsCompl x y
· 使用定理 `bot_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊓ a = ⊥
· 使用定理 `sup_top_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderTo
p α] (a : α), a ⊔ ⊤ = ⊤
-/
theorem isCompl_bot_top : IsCompl (⊥ : α) ⊤ :=
  IsCompl.of_eq (bot_inf_eq _) (sup_top_eq _)
/-
**isCompl_top_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompl_top_bot : IsCompl (⊤ : α) ⊥
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.of_eq`：of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : IsCompl x y
· 使用定理 `inf_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), a ⊓ ⊥ = ⊥
· 使用定理 `top_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊔ a = ⊤
-/
theorem isCompl_top_bot : IsCompl (⊤ : α) ⊥ :=
  IsCompl.of_eq (inf_bot_eq _) (top_sup_eq _)
/-
**eq_top_of_isCompl_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_top_of_isCompl_bot (h : IsCompl x ⊥) : x = ⊤
参数：h : IsCompl x ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
-/
theorem eq_top_of_isCompl_bot (h : IsCompl x ⊥) : x = ⊤ := by rw [← sup_bot_eq x, h.sup_eq_top]
/-
**eq_top_of_bot_isCompl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_top_of_bot_isCompl (h : IsCompl ⊥ x) : x = ⊤
参数：h : IsCompl ⊥ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_of_isCompl_bot`：eq_top_of_isCompl_bot (h : IsCompl x ⊥) : x = ⊤
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
-/
theorem eq_top_of_bot_isCompl (h : IsCompl ⊥ x) : x = ⊤ :=
  eq_top_of_isCompl_bot h.symm
/-
**eq_bot_of_isCompl_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_bot_of_isCompl_top (h : IsCompl x ⊤) : x = ⊥
参数：h : IsCompl x ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_of_isCompl_bot`：eq_top_of_isCompl_bot (h : IsCompl x ⊥) : x = ⊤
· 使用定理 `IsCompl.dual`：dual (h : IsCompl x y) : IsCompl (toDual x) (toDual y)
-/
theorem eq_bot_of_isCompl_top (h : IsCompl x ⊤) : x = ⊥ :=
  eq_top_of_isCompl_bot h.dual
/-
**eq_bot_of_top_isCompl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_bot_of_top_isCompl (h : IsCompl ⊤ x) : x = ⊥
参数：h : IsCompl ⊤ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_of_bot_isCompl`：eq_top_of_bot_isCompl (h : IsCompl ⊥ x) : x = ⊤
· 使用定理 `IsCompl.dual`：dual (h : IsCompl x y) : IsCompl (toDual x) (toDual y)
-/
theorem eq_bot_of_top_isCompl (h : IsCompl ⊤ x) : x = ⊥ :=
  eq_top_of_bot_isCompl h.dual

end

section IsComplemented

section Lattice

variable [Lattice α] [BoundedOrder α]

/-- An element is *complemented* if it has a complement. -/
/-
**IsComplemented** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsComplemented (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element is *complemented* if it has a complement.
-/
def IsComplemented (a : α) : Prop :=
  ∃ b, IsCompl a b
/-
**isComplemented_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isComplemented_bot : IsComplemented (⊥ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompl_bot_top`：isCompl_bot_top : IsCompl (⊥ : α) ⊤
-/
theorem isComplemented_bot : IsComplemented (⊥ : α) :=
  ⟨⊤, isCompl_bot_top⟩
/-
**isComplemented_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isComplemented_top : IsComplemented (⊤ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompl_top_bot`：isCompl_top_bot : IsCompl (⊤ : α) ⊥
-/
theorem isComplemented_top : IsComplemented (⊤ : α) :=
  ⟨⊥, isCompl_top_bot⟩

end Lattice

variable [DistribLattice α] [BoundedOrder α] {a b : α}

/-
**IsComplemented.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsComplemented.sup : IsComplemented a -> IsComplemented b -> IsComplemente
d (a ⊔ b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.sup_inf`：sup_inf {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') 
: IsCompl (x ⊔ x') (y ⊓ y')
-/
theorem IsComplemented.sup : IsComplemented a → IsComplemented b → IsComplemented (a ⊔ b) :=
  fun ⟨a', ha⟩ ⟨b', hb⟩ => ⟨a' ⊓ b', ha.sup_inf hb⟩
/-
**IsComplemented.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsComplemented.inf : IsComplemented a -> IsComplemented b -> IsComplemente
d (a ⊓ b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.inf_sup`：inf_sup {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') 
: IsCompl (x ⊓ x') (y ⊔ y')
-/
theorem IsComplemented.inf : IsComplemented a → IsComplemented b → IsComplemented (a ⊓ b) :=
  fun ⟨a', ha⟩ ⟨b', hb⟩ => ⟨a' ⊔ b', ha.inf_sup hb⟩

end IsComplemented

/-- A complemented bounded lattice is one where every element has a (not necessarily unique)
complement. -/
/-
**ComplementedLattice** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [inst : Lattice α] → [BoundedOrder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complemented bounded lattice is one where every element has a (not necessarily
 unique)
complement.
-/
class ComplementedLattice (α) [Lattice α] [BoundedOrder α] : Prop where
  /-- In a `ComplementedLattice`, every element admits a complement. -/
  exists_isCompl : ∀ a : α, ∃ b : α, IsCompl a b
/-
**complementedLattice_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：complementedLattice_iff (α) [Lattice α] [BoundedOrder α] : ComplementedLat
tice α ↔ forall a : α, exists b : α, IsCompl a b
参数：α。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma complementedLattice_iff (α) [Lattice α] [BoundedOrder α] :
    ComplementedLattice α ↔ ∀ a : α, ∃ b : α, IsCompl a b :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

export ComplementedLattice (exists_isCompl)

-- This was previously a global instance,
-- but it doesn't appear to be used and has been implicated in slow typeclass resolutions.
/-
**Subsingleton.instComplementedLattice** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subsingleton.instComplementedLattice [Lattice α] [BoundedOrder α] [Subsing
leton α] : ComplementedLattice α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_bot_right`：disjoint_bot_right : Disjoint a ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `codisjoint_top_right`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 :
 OrderTop α] {a : α}, Codisjoint a ⊤
-/
lemma Subsingleton.instComplementedLattice
    [Lattice α] [BoundedOrder α] [Subsingleton α] : ComplementedLattice α := by
  refine ⟨fun a ↦ ⟨⊥, disjoint_bot_right, ?_⟩⟩
  rw [Subsingleton.elim ⊥ ⊤]
  exact codisjoint_top_right

namespace ComplementedLattice

variable [Lattice α] [BoundedOrder α] [ComplementedLattice α]

/-
**ComplementedLattice.** 是 Mathlib 中的一个实例，位于命名空间 `ComplementedLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ComplementedLattice αᵒᵈ :=
  ⟨fun a ↦
    let ⟨b, hb⟩ := exists_isCompl (show α from a)
    ⟨b, hb.dual⟩⟩

end ComplementedLattice

-- TODO: Define as a sublattice?
/-- The sublattice of complemented elements. -/
/-
**Complementeds** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Complementeds (α : Type*) [Lattice α] [BoundedOrder α] : Type _
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sublattice of complemented elements.
-/
abbrev Complementeds (α : Type*) [Lattice α] [BoundedOrder α] : Type _ :=
  {a : α // IsComplemented a}

namespace Complementeds

section Lattice

variable [Lattice α] [BoundedOrder α] {a b : Complementeds α}

/-
**Complementeds.hasCoeT** 是 Mathlib 中的一个实例，位于命名空间 `Complementeds`。
形式化陈述：hasCoeT : CoeTC (Complementeds α) α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeT : CoeTC (Complementeds α) α := ⟨Subtype.val⟩
/-
**Complementeds.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：coe_injective : Injective ((↑) : Complementeds α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem coe_injective : Injective ((↑) : Complementeds α → α) := Subtype.coe_injective

@[simp, norm_cast]
/-
**Complementeds.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：coe_inj : (a : α) = b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
-/
theorem coe_inj : (a : α) = b ↔ a = b := Subtype.coe_inj

@[norm_cast]
/-
**Complementeds.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：coe_le_coe : (a : α) <= b ↔ a <= b
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
theorem coe_le_coe : (a : α) ≤ b ↔ a ≤ b := by simp

@[norm_cast]
/-
**Complementeds.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：coe_lt_coe : (a : α) < b ↔ a < b
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
theorem coe_lt_coe : (a : α) < b ↔ a < b := by simp
/-
**Complementeds.** 是 Mathlib 中的一个实例，位于命名空间 `Complementeds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedOrder (Complementeds α) :=
  Subtype.boundedOrder isComplemented_bot isComplemented_top

@[simp, norm_cast]
/-
**Complementeds.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：coe_bot : ((⊥ : Complementeds α) : α) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ((⊥ : Complementeds α) : α) = ⊥ := rfl

@[simp, norm_cast]
/-
**Complementeds.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：coe_top : ((⊤ : Complementeds α) : α) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : Complementeds α) : α) = ⊤ := rfl
/-
**Complementeds.mk_bot** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：mk_bot : (⟨⊥, isComplemented_bot⟩ : Complementeds α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `isComplemented_bot`：isComplemented_bot : IsComplemented (⊥ : α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk_bot`：mk_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) 
: mk ⊥ hbot = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_bot : (⟨⊥, isComplemented_bot⟩ : Complementeds α) = ⊥ := by simp
/-
**Complementeds.mk_top** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：mk_top : (⟨⊤, isComplemented_top⟩ : Complementeds α) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `isComplemented_top`：isComplemented_top : IsComplemented (⊤ : α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk_top`：∀ {α : Type u} {p : α → Prop} [inst : PartialOrder α] [i
nst_1 : OrderTop α] [inst_2 : OrderTop (Subtype p)]   (htop : p ⊤), ⟨⊤, htop⟩ = 
⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_top : (⟨⊤, isComplemented_top⟩ : Complementeds α) = ⊤ := by simp
/-
**Complementeds.** 是 Mathlib 中的一个实例，位于命名空间 `Complementeds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Complementeds α) := ⟨⊥⟩

end Lattice

variable [DistribLattice α] [BoundedOrder α] {a b : Complementeds α}

/-
**Complementeds.** 是 Mathlib 中的一个实例，位于命名空间 `Complementeds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (Complementeds α) :=
  ⟨fun a b => ⟨a ⊔ b, a.2.sup b.2⟩⟩
/-
**Complementeds.** 是 Mathlib 中的一个实例，位于命名空间 `Complementeds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (Complementeds α) :=
  ⟨fun a b => ⟨a ⊓ b, a.2.inf b.2⟩⟩

@[simp, norm_cast]
/-
**Complementeds.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：coe_sup (a b : Complementeds α) : ↑(a ⊔ b) = (a : α) ⊔ b
参数：a b : Complementeds α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (a b : Complementeds α) : ↑(a ⊔ b) = (a : α) ⊔ b := rfl

@[simp, norm_cast]
/-
**Complementeds.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：coe_inf (a b : Complementeds α) : ↑(a ⊓ b) = (a : α) ⊓ b
参数：a b : Complementeds α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (a b : Complementeds α) : ↑(a ⊓ b) = (a : α) ⊓ b := rfl

@[simp]
/-
**Complementeds.mk_sup_mk** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：mk_sup_mk {a b : α} (ha : IsComplemented a) (hb : IsComplemented b) : (⟨a,
 ha⟩ ⊔ ⟨b, hb⟩ : Complementeds α) = ⟨a ⊔ b, ha.sup hb⟩
参数：ha : IsComplemented a；hb : IsComplemented b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_sup_mk {a b : α} (ha : IsComplemented a) (hb : IsComplemented b) :
    (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : Complementeds α) = ⟨a ⊔ b, ha.sup hb⟩ := rfl

@[simp]
/-
**Complementeds.mk_inf_mk** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：mk_inf_mk {a b : α} (ha : IsComplemented a) (hb : IsComplemented b) : (⟨a,
 ha⟩ ⊓ ⟨b, hb⟩ : Complementeds α) = ⟨a ⊓ b, ha.inf hb⟩
参数：ha : IsComplemented a；hb : IsComplemented b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_inf_mk {a b : α} (ha : IsComplemented a) (hb : IsComplemented b) :
    (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : Complementeds α) = ⟨a ⊓ b, ha.inf hb⟩ := rfl
/-
**Complementeds.** 是 Mathlib 中的一个实例，位于命名空间 `Complementeds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribLattice (Complementeds α) :=
  Complementeds.coe_injective.distribLattice _ .rfl .rfl coe_sup coe_inf

@[simp, norm_cast]
/-
**Complementeds.disjoint_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：disjoint_coe : Disjoint (a : α) b ↔ Disjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complementeds.coe_inf`：coe_inf (a b : Complementeds α) : ↑(a ⊓ b) = (a :
 α) ⊓ b
· 使用定理 `Complementeds.coe_bot`：coe_bot : ((⊥ : Complementeds α) : α) = ⊥
· 使用定理 `Complementeds.coe_inj`：coe_inj : (a : α) = b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_coe : Disjoint (a : α) b ↔ Disjoint a b := by
  rw [disjoint_iff, disjoint_iff, ← coe_inf, ← coe_bot, coe_inj]

@[simp, norm_cast]
/-
**Complementeds.codisjoint_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：codisjoint_coe : Codisjoint (a : α) b ↔ Codisjoint a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complementeds.coe_sup`：coe_sup (a b : Complementeds α) : ↑(a ⊔ b) = (a :
 α) ⊔ b
· 使用定理 `Complementeds.coe_top`：coe_top : ((⊤ : Complementeds α) : α) = ⊤
· 使用定理 `Complementeds.coe_inj`：coe_inj : (a : α) = b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem codisjoint_coe : Codisjoint (a : α) b ↔ Codisjoint a b := by
  rw [codisjoint_iff, codisjoint_iff, ← coe_sup, ← coe_top, coe_inj]

@[simp, norm_cast]
/-
**Complementeds.isCompl_coe** 是 Mathlib 中的一个定理，位于命名空间 `Complementeds`。
形式化陈述：isCompl_coe : IsCompl (a : α) b ↔ IsCompl a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCompl_coe : IsCompl (a : α) b ↔ IsCompl a b := by
  simp_rw [isCompl_iff, disjoint_coe, codisjoint_coe]
/-
**Complementeds.** 是 Mathlib 中的一个实例，位于命名空间 `Complementeds`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ComplementedLattice (Complementeds α) :=
  ⟨fun ⟨a, b, h⟩ => ⟨⟨b, a, h.symm⟩, isCompl_coe.1 h⟩⟩

end Complementeds
end IsCompl

