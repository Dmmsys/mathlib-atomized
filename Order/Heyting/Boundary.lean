/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Tactic.Common

/-!
# Co-Heyting boundary

The boundary of an element of a co-Heyting algebra is the intersection of its Heyting negation with
itself. The boundary in the co-Heyting algebra of closed sets coincides with the topological
boundary.

## Main declarations

* `Coheyting.boundary`: Co-Heyting boundary. `Coheyting.boundary a = a ⊓ ￢a`

## Notation

`∂ a` is notation for `Coheyting.boundary a` in scope `Heyting`.
-/

@[expose] public section

assert_not_exists RelIso

variable {α : Type*}

namespace Coheyting

variable [CoheytingAlgebra α] {a b : α}

/-- The boundary of an element of a co-Heyting algebra is the intersection of its Heyting negation
with itself. Note that this is always `⊥` for a Boolean algebra. -/
/-
**Coheyting.boundary** 是 Mathlib 中的一个定义，位于命名空间 `Coheyting`。
形式化陈述：boundary (a : α) : α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The boundary of an element of a co-Heyting algebra is the intersection of its He
yting negation
with itself. Note that this is always `⊥` for a Boolean algebra.
-/
def boundary (a : α) : α :=
  a ⊓ ￢a

/-- The boundary of an element of a co-Heyting algebra. -/
scoped[Heyting] prefix:120 "∂ " => Coheyting.boundary

open Heyting

-- TODO: Should hnot be named hNot?
/-
**Coheyting.inf_hnot_self** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：inf_hnot_self (a : α) : a ⊓ ￢a = ∂ a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_hnot_self (a : α) : a ⊓ ￢a = ∂ a :=
  rfl
/-
**Coheyting.boundary_le** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：boundary_le : ∂ a <= a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem boundary_le : ∂ a ≤ a :=
  inf_le_left
/-
**Coheyting.boundary_le_hnot** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：boundary_le_hnot : ∂ a <= ￢a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem boundary_le_hnot : ∂ a ≤ ￢a :=
  inf_le_right

@[simp]
/-
**Coheyting.boundary_bot** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：boundary_bot : ∂ (⊥ : α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊓ a = ⊥
-/
theorem boundary_bot : ∂ (⊥ : α) = ⊥ := bot_inf_eq _

@[simp]
/-
**Coheyting.boundary_top** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：boundary_top : ∂ (⊤ : α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Coheyting.boundary.eq_1`：∀ {α : Type u_1} [inst : CoheytingAlgebra α] (a
 : α), Coheyting.boundary a = a ⊓ ￢a
· 使用定理 `hnot_top`：∀ {α : Type u_2} [inst : CoheytingAlgebra α], ￢⊤ = ⊥
· 使用定理 `inf_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), a ⊓ ⊥ = ⊥
-/
theorem boundary_top : ∂ (⊤ : α) = ⊥ := by rw [boundary, hnot_top, inf_bot_eq]
/-
**Coheyting.boundary_hnot_le** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：boundary_hnot_le (a : α) : ∂ (￢a) <= ∂ a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_le_inf_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c 
: α), b ≤ a → b ⊓ c ≤ a ⊓ c
· 使用定理 `hnot_hnot_le`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] {a : α}, ￢￢a 
≤ a
-/
theorem boundary_hnot_le (a : α) : ∂ (￢a) ≤ ∂ a :=
  (inf_comm _ _).trans_le <| inf_le_inf_right _ hnot_hnot_le

@[simp]
/-
**Coheyting.boundary_hnot_hnot** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：boundary_hnot_hnot (a : α) : ∂ (￢￢a) = ∂ (￢a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hnot_hnot_hnot`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), ￢￢
￢a = ￢a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem boundary_hnot_hnot (a : α) : ∂ (￢￢a) = ∂ (￢a) := by
  simp_rw [boundary, hnot_hnot_hnot, inf_comm]

@[simp]
/-
**Coheyting.hnot_boundary** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：hnot_boundary (a : α) : ￢∂ a = ⊤
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Coheyting.boundary.eq_1`：∀ {α : Type u_1} [inst : CoheytingAlgebra α] (a
 : α), Coheyting.boundary a = a ⊓ ￢a
· 使用定理 `hnot_inf_distrib`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a b : α)
, ￢(a ⊓ b) = ￢a ⊔ ￢b
· 使用定理 `sup_hnot_self`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), a ⊔
 ￢a = ⊤
-/
theorem hnot_boundary (a : α) : ￢∂ a = ⊤ := by rw [boundary, hnot_inf_distrib, sup_hnot_self]

/-- **Leibniz rule** for the co-Heyting boundary. -/
/-
**Coheyting.boundary_inf** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：boundary_inf (a b : α) : ∂ (a ⊓ b) = ∂ a ⊓ b ⊔ a ⊓ ∂ b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hnot_inf_distrib`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a b : α)
, ￢(a ⊓ b) = ￢a ⊔ ￢b
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `inf_right_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a 
⊓ b ⊓ c = a ⊓ c ⊓ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)

--- 原说明 ---
**Leibniz rule** for the co-Heyting boundary.
-/
theorem boundary_inf (a b : α) : ∂ (a ⊓ b) = ∂ a ⊓ b ⊔ a ⊓ ∂ b := by
  unfold boundary
  rw [hnot_inf_distrib, inf_sup_left, inf_right_comm, ← inf_assoc]
/-
**Coheyting.boundary_inf_le** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：boundary_inf_le : ∂ (a ⊓ b) <= ∂ a ⊔ ∂ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Coheyting.boundary_inf`：boundary_inf (a b : α) : ∂ (a ⊓ b) = ∂ a ⊓ b ⊔ a
 ⊓ ∂ b
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem boundary_inf_le : ∂ (a ⊓ b) ≤ ∂ a ⊔ ∂ b :=
  (boundary_inf _ _).trans_le <| sup_le_sup inf_le_left inf_le_right
/-
**Coheyting.boundary_sup_le** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：boundary_sup_le : ∂ (a ⊔ b) <= ∂ a ⊔ ∂ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Coheyting.boundary.eq_1`：∀ {α : Type u_1} [inst : CoheytingAlgebra α] (a
 : α), Coheyting.boundary a = a ⊓ ￢a
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `hnot_anti`：∀ {α : Type u_2} [inst : CoheytingAlgebra α], Antitone hnot
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem boundary_sup_le : ∂ (a ⊔ b) ≤ ∂ a ⊔ ∂ b := by
  rw [boundary, inf_sup_right]
  exact
    sup_le_sup (inf_le_inf_left _ <| hnot_anti le_sup_left)
      (inf_le_inf_left _ <| hnot_anti le_sup_right)

/-- The intuitionistic version of `Coheyting.boundary_le_boundary_sup_sup_boundary_inf_left`. Either
proof can be obtained from the other using the equivalence of Heyting algebras and intuitionistic
logic and duality between Heyting and co-Heyting algebras. It is crucial that the following proof be
intuitionistic. -/
/-
**Coheyting.** 是 Mathlib 中的一个示例，位于命名空间 `Coheyting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intuitionistic version of `Coheyting.boundary_le_boundary_sup_sup_boundary_i
nf_left`. Either
proof can be obtained from the other using the equivalence of Heyting algebras a
nd intuitionistic
logic and duality between Heyting and co-Heyting algebras. It is crucial that th
e following proof be
intuitionistic.
-/
example (a b : Prop) : (a ∧ b ∨ ¬(a ∧ b)) ∧ ((a ∨ b) ∨ ¬(a ∨ b)) → a ∨ ¬a := by
  rintro ⟨⟨ha, _⟩ | hnab, (ha | hb) | hnab⟩ <;> try exact Or.inl ha
  · exact Or.inr fun ha => hnab ⟨ha, hb⟩
  · exact Or.inr fun ha => hnab <| Or.inl ha
/-
**Coheyting.boundary_le_boundary_sup_sup_boundary_inf_left** 是 Mathlib 中的一个定理，位于
命名空间 `Coheyting`。
形式化陈述：boundary_le_boundary_sup_sup_boundary_inf_left : ∂ a <= ∂ (a ⊔ b) ⊔ ∂ (a ⊓
 b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_right_idem`：sup_right_idem (a b : α) : a ⊔ b ⊔ b = a ⊔ b
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_of_right_le`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α}
, b ≤ c → a ⊓ b ≤ c
· 使用定理 `hnot_le_iff_codisjoint_right`：∀ {α : Type u_2} [inst : CoheytingAlgebra 
α] {a b : α}, ￢b ≤ a ↔ Codisjoint b a
· 使用定理 `codisjoint_left_comm`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1
 : OrderTop α] {a b c : α},   Codisjoint a (b ⊔ c) ↔ Codisjoint b (a ⊔ c)
· 使用定理 `codisjoint_hnot_left`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] {a : 
α}, Codisjoint (￢a) a
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
· 使用定理 `Codisjoint.mono_right`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 
: OrderTop α] {a b c : α}, c ≤ b → Codisjoint a c → Codisjoint a b
· 使用定理 `hnot_anti`：∀ {α : Type u_2} [inst : CoheytingAlgebra α], Antitone hnot
· 使用定理 `codisjoint_hnot_right`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] {a :
 α}, Codisjoint a (￢a)
-/
theorem boundary_le_boundary_sup_sup_boundary_inf_left : ∂ a ≤ ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) := by
  simp only [boundary, sup_inf_left, sup_inf_right, sup_right_idem, le_inf_iff, sup_assoc,
    sup_comm _ a]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_⟩ <;> try { exact le_sup_of_le_left inf_le_left } <;>
    refine inf_le_of_right_le ?_
  · rw [hnot_le_iff_codisjoint_right, codisjoint_left_comm]
    exact codisjoint_hnot_left
  · refine le_sup_of_le_right ?_
    rw [hnot_le_iff_codisjoint_right]
    exact codisjoint_hnot_right.mono_right (hnot_anti inf_le_left)
/-
**Coheyting.boundary_le_boundary_sup_sup_boundary_inf_right** 是 Mathlib 中的一个定理，位
于命名空间 `Coheyting`。
形式化陈述：boundary_le_boundary_sup_sup_boundary_inf_right : ∂ b <= ∂ (a ⊔ b) ⊔ ∂ (a 
⊓ b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Coheyting.boundary_le_boundary_sup_sup_boundary_inf_left`：boundary_le_bo
undary_sup_sup_boundary_inf_left : ∂ a <= ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b)
-/
theorem boundary_le_boundary_sup_sup_boundary_inf_right : ∂ b ≤ ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) := by
  rw [sup_comm a, inf_comm]
  exact boundary_le_boundary_sup_sup_boundary_inf_left
/-
**Coheyting.boundary_sup_sup_boundary_inf** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：boundary_sup_sup_boundary_inf (a b : α) : ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) = ∂ a ⊔ ∂ 
b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Coheyting.boundary_sup_le`：boundary_sup_le : ∂ (a ⊔ b) <= ∂ a ⊔ ∂ b
· 使用定理 `Coheyting.boundary_inf_le`：boundary_inf_le : ∂ (a ⊓ b) <= ∂ a ⊔ ∂ b
· 使用定理 `Coheyting.boundary_le_boundary_sup_sup_boundary_inf_left`：boundary_le_bo
undary_sup_sup_boundary_inf_left : ∂ a <= ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b)
· 使用定理 `Coheyting.boundary_le_boundary_sup_sup_boundary_inf_right`：boundary_le_b
oundary_sup_sup_boundary_inf_right : ∂ b <= ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b)
-/
theorem boundary_sup_sup_boundary_inf (a b : α) : ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) = ∂ a ⊔ ∂ b :=
  le_antisymm (sup_le boundary_sup_le boundary_inf_le) <|
    sup_le boundary_le_boundary_sup_sup_boundary_inf_left
      boundary_le_boundary_sup_sup_boundary_inf_right

@[simp]
/-
**Coheyting.boundary_boundary** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：boundary_boundary (a : α) : ∂ ∂ a = ∂ a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Coheyting.boundary.eq_1`：∀ {α : Type u_1} [inst : CoheytingAlgebra α] (a
 : α), Coheyting.boundary a = a ⊓ ￢a
· 使用定理 `Coheyting.hnot_boundary`：hnot_boundary (a : α) : ￢∂ a = ⊤
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
-/
theorem boundary_boundary (a : α) : ∂ ∂ a = ∂ a := by rw [boundary, hnot_boundary, inf_top_eq]

alias boundary_idem := boundary_boundary
/-
**Coheyting.hnot_hnot_sup_boundary** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：hnot_hnot_sup_boundary (a : α) : ￢￢a ⊔ ∂ a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Coheyting.boundary.eq_1`：∀ {α : Type u_1} [inst : CoheytingAlgebra α] (a
 : α), Coheyting.boundary a = a ⊓ ￢a
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
· 使用定理 `hnot_sup_self`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), ￢a 
⊔ a = ⊤
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `hnot_hnot_le`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] {a : α}, ￢￢a 
≤ a
-/
theorem hnot_hnot_sup_boundary (a : α) : ￢￢a ⊔ ∂ a = a := by
  rw [boundary, sup_inf_left, hnot_sup_self, inf_top_eq, sup_eq_right]
  exact hnot_hnot_le
/-
**Coheyting.sdiff_boundary_self** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting`。
形式化陈述：sdiff_boundary_self : a \ ∂ a = ￢￢a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Coheyting.hnot_hnot_sup_boundary`：hnot_hnot_sup_boundary (a : α) : ￢￢a ⊔
 ∂ a = a
· 使用定理 `sup_sdiff_distrib`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra 
α] (b c a : α), (b ⊔ c) \ a = b \ a ⊔ c \ a
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
· 使用定理 `hnot_sdiff_comm`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (b a : α),
 ￢b \ a = ￢a \ b
· 使用定理 `Coheyting.hnot_boundary`：hnot_boundary (a : α) : ￢∂ a = ⊤
· 使用定理 `top_sdiff'`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), ⊤ \ a 
= ￢a
-/
theorem sdiff_boundary_self : a \ ∂ a = ￢￢a := by
  rw (occs := [1]) [← hnot_hnot_sup_boundary a]
  rw [sup_sdiff_distrib, sdiff_self, sup_bot_eq, hnot_sdiff_comm,
    hnot_boundary, top_sdiff']
/-
**Coheyting.hnot_eq_top_iff_exists_boundary** 是 Mathlib 中的一个定理，位于命名空间 `Coheyting
`。
形式化陈述：hnot_eq_top_iff_exists_boundary : ￢a = ⊤ ↔ exists b, ∂ b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Coheyting.boundary.eq_1`：∀ {α : Type u_1} [inst : CoheytingAlgebra α] (a
 : α), Coheyting.boundary a = a ⊓ ￢a
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
· 使用定理 `Coheyting.hnot_boundary`：hnot_boundary (a : α) : ￢∂ a = ⊤
-/
theorem hnot_eq_top_iff_exists_boundary : ￢a = ⊤ ↔ ∃ b, ∂ b = a :=
  ⟨fun h => ⟨a, by rw [boundary, h, inf_top_eq]⟩, by
    rintro ⟨b, rfl⟩
    exact hnot_boundary _⟩

end Coheyting

open Heyting

section BooleanAlgebra

variable [BooleanAlgebra α]

@[simp]
/-
**Coheyting.boundary_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Coheyting.boundary_eq_bot (a : α) : ∂ a = ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_compl_eq_bot`：inf_compl_eq_bot : a ⊓ aᶜ = ⊥
-/
theorem Coheyting.boundary_eq_bot (a : α) : ∂ a = ⊥ :=
  inf_compl_eq_bot

end BooleanAlgebra

