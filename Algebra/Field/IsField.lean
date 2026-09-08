/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Tactic.Common

/-!
# `IsField` predicate

Predicate on a (semi)ring that it is a (semi)field, i.e. that the multiplication is
commutative, that it has more than one element and that all non-zero elements have a
multiplicative inverse. In contrast to `Field`, which contains the data of a function associating
to an element of the field its multiplicative inverse, this predicate only assumes the existence
and can therefore more easily be used to e.g. transfer along ring isomorphisms.
-/

@[expose] public section

universe u

section IsField

/-- A predicate to express that a (semi)ring is a (semi)field.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms.
Additionally, this is useful when trying to prove that
a particular ring structure extends to a (semi)field. -/
/-
**IsField** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [Semiring R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate to express that a (semi)ring is a (semi)field.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms.
Additionally, this is useful when trying to prove that
a particular ring structure extends to a (semi)field.
-/
structure IsField (R : Type u) [Semiring R] : Prop where
  /-- For a semiring to be a field, it must have two distinct elements. -/
  exists_pair_ne : ∃ x y : R, x ≠ y
  /-- Fields are commutative. -/
  mul_comm : ∀ x y : R, x * y = y * x
  /-- Nonzero elements have multiplicative inverses. -/
  mul_inv_cancel : ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1

/-- Transferring from `Semifield` to `IsField`. -/
/-
**Semifield.toIsField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Semifield.toIsField (R : Type u) [Semifield R] : IsField R where __
参数：R : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nontrivial.exists_pair_ne`：∀ {α : Type u_3} [self : Nontrivial α], ∃ x y
, x ≠ y
· 使用定理 `Semifield.toNontrivial`：∀ {K : Type u_2} [self : Semifield K], Nontrivia
l K
· 使用定理 `CommSemiring.mul_comm`：∀ {R : Type u} [self : CommSemiring R] (a b : R),
 a * b = b * a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1

--- 原说明 ---
Transferring from `Semifield` to `IsField`.
-/
theorem Semifield.toIsField (R : Type u) [Semifield R] : IsField R where
  __ := ‹Semifield R›
  mul_inv_cancel {a} ha := ⟨a⁻¹, mul_inv_cancel₀ ha⟩

/-- Transferring from `Field` to `IsField`. -/
/-
**Field.toIsField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Field.toIsField (R : Type u) [Field R] : IsField R
参数：R : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semifield.toIsField`：Semifield.toIsField (R : Type u) [Semifield R] : Is
Field R where __

--- 原说明 ---
Transferring from `Field` to `IsField`.
-/
theorem Field.toIsField (R : Type u) [Field R] : IsField R :=
  Semifield.toIsField _

@[simp]
/-
**IsField.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsField.nontrivial {R : Type u} [Semiring R] (h : IsField R) : Nontrivial 
R
参数：h : IsField R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsField.exists_pair_ne`：∀ {R : Type u} [inst : Semiring R], IsField R → 
∃ x y, x ≠ y
-/
theorem IsField.nontrivial {R : Type u} [Semiring R] (h : IsField R) : Nontrivial R :=
  ⟨h.exists_pair_ne⟩
/-
**IsField.isDomain** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsField.isDomain {R : Type u} [Semiring R] (h : IsField R) : IsDomain R wh
ere mul_left_cancel_of_ne_zero ha _ _ hb
参数：h : IsField R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsField.mul_inv_cancel`：∀ {R : Type u} [inst : Semiring R], IsField R → 
∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsField.mul_comm`：∀ {R : Type u} [inst : Semiring R], IsField R → ∀ (x y
 : R), x * y = y * x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsField.exists_pair_ne`：∀ {R : Type u} [inst : Semiring R], IsField R → 
∃ x y, x ≠ y
-/
lemma IsField.isDomain {R : Type u} [Semiring R] (h : IsField R) : IsDomain R where
  mul_left_cancel_of_ne_zero ha _ _ hb := by
    obtain ⟨x, hx⟩ := h.mul_inv_cancel ha
    simpa [← mul_assoc, h.mul_comm, hx] using congr_arg (x * ·) hb
  mul_right_cancel_of_ne_zero ha _ _ hb := by
    obtain ⟨x, hx⟩ := h.mul_inv_cancel ha
    simpa [mul_assoc, hx] using congr_arg (· * x) hb
  exists_pair_ne := h.exists_pair_ne
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type u} [Semifield R] : IsDomain R :=
  (Semifield.toIsField _).isDomain

@[simp]
/-
**not_isField_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isField_of_subsingleton (R : Type u) [Semiring R] [Subsingleton R] : ¬
IsField R
参数：R : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsField.exists_pair_ne`：∀ {R : Type u} [inst : Semiring R], IsField R → 
∃ x y, x ≠ y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem not_isField_of_subsingleton (R : Type u) [Semiring R] [Subsingleton R] : ¬IsField R :=
  fun h =>
  let ⟨_, _, h⟩ := h.exists_pair_ne
  h (Subsingleton.elim _ _)

open scoped Classical in
/-- Transferring from `IsField` to `Semifield`. -/
@[instance_reducible]
/-
**IsField.toSemifield** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsField.toSemifield {R : Type u} [Semiring R] (h : IsField R) : Semifield 
R where __
参数：h : IsField R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsField.mul_comm`：∀ {R : Type u} [inst : Semiring R], IsField R → ∀ (x y
 : R), x * y = y * x
· 使用定理 `IsField.mul_inv_cancel`：∀ {R : Type u} [inst : Semiring R], IsField R → 
∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1

--- 原说明 ---
Transferring from `IsField` to `Semifield`.
-/
noncomputable def IsField.toSemifield {R : Type u} [Semiring R] (h : IsField R) : Semifield R where
  __ := ‹Semiring R›
  __ := h
  inv a := if ha : a = 0 then 0 else Classical.choose (h.mul_inv_cancel ha)
  inv_zero := dif_pos rfl
  mul_inv_cancel a ha := by convert! Classical.choose_spec (h.mul_inv_cancel ha); exact dif_neg ha
  nnqsmul := _
  nnqsmul_def _ _ := rfl

/-- Transferring from `IsField` to `Field`. -/
@[instance_reducible]
/-
**IsField.toField** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsField.toField {R : Type u} [Ring R] (h : IsField R) : Field R where __
参数：h : IsField R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Semifield.div_eq_mul_inv`：∀ {K : Type u_2} [self : Semifield K] (a b : K
), a / b = a * b⁻¹
· 使用定理 `Semifield.zpow_zero'`：∀ {K : Type u_2} [self : Semifield K] (a : K), a ^
 0 = 1
· 使用定理 `Semifield.zpow_succ'`：∀ {K : Type u_2} [self : Semifield K] (n : ℕ) (a :
 K), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `Semifield.zpow_neg'`：∀ {K : Type u_2} [self : Semifield K] (n : ℕ) (a : 
K), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `Semifield.toNontrivial`：∀ {K : Type u_2} [self : Semifield K], Nontrivia
l K
· 使用定理 `Semifield.mul_inv_cancel`：∀ {K : Type u_2} [self : Semifield K] (a : K),
 a ≠ 0 → a * a⁻¹ = 1
· 使用定理 `Semifield.inv_zero`：∀ {K : Type u_2} [self : Semifield K], 0⁻¹ = 0
· 使用定理 `Semifield.nnratCast_def`：∀ {K : Type u_2} [self : Semifield K] (q : ℚ≥0)
, ↑q = ↑q.num / ↑q.den
· 使用定理 `Semifield.nnqsmul_def`：∀ {K : Type u_2} [self : Semifield K] (q : ℚ≥0) (
a : K), Semifield.nnqsmul q a = ↑q * a

--- 原说明 ---
Transferring from `IsField` to `Field`.
-/
noncomputable def IsField.toField {R : Type u} [Ring R] (h : IsField R) : Field R where
  __ := (‹Ring R› :) -- this also works without the `( :)`, but it's slow
  __ := h.toSemifield
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `IsField` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
/-
**uniq_inv_of_isField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniq_inv_of_isField (R : Type u) [Ring R] (hf : IsField R) : forall x : R,
 x != 0 -> exists! y : R, x * y = 1
参数：R : Type u；hf : IsField R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_of_exists_of_unique`：existsUnique_of_exists_of_unique {p : 
α -> Prop} (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y
₂) : exists! x, p x
· 使用定理 `IsField.mul_inv_cancel`：∀ {R : Type u} [inst : Semiring R], IsField R → 
∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsField.mul_comm`：∀ {R : Type u} [inst : Semiring R], IsField R → ∀ (x y
 : R), x * y = y * x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
For each field, and for each nonzero element of said field, there is a unique in
verse.
Since `IsField` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
theorem uniq_inv_of_isField (R : Type u) [Ring R] (hf : IsField R) :
    ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1 := by
  intro x hx
  apply existsUnique_of_exists_of_unique
  · exact hf.mul_inv_cancel hx
  · intro y z hxy hxz
    calc
      y = y * (x * z) := by rw [hxz, mul_one]
      _ = x * y * z := by rw [← mul_assoc, hf.mul_comm y x]
      _ = z := by rw [hxy, one_mul]

end IsField

