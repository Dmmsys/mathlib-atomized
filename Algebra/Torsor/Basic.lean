/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Torsors of group actions

Further results for torsors, that are not in `Mathlib/Algebra/AddTorsor/Defs.lean` to avoid
increasing imports there.
-/

@[expose] public section

open scoped Pointwise


section General

variable {G : Type*} {P : Type*} [Group G] [T : Torsor G P]

namespace Set

@[to_additive]
/-
**Set.singleton_sdiv_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_sdiv_self (p : P) : ({p} : Set P) /ₛ {p} = {(1 : G)}
参数：p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.singleton_sdiv_singleton`：singleton_sdiv_singleton : ({b} : Set β) /
ₛ {c} = {b /ₛ c}
· 使用定理 `sdiv_self`：sdiv_self (p : P) : p /ₛ p = (1 : G)
-/
theorem singleton_sdiv_self (p : P) : ({p} : Set P) /ₛ {p} = {(1 : G)} := by
  rw [Set.singleton_sdiv_singleton, sdiv_self]

@[to_additive (attr := simp)]
/-
**Set.one_mem_sdiv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：one_mem_sdiv_iff {s t : Set P} : (1 : G) in s /ₛ t ↔ ¬Disjoint s t
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
theorem one_mem_sdiv_iff {s t : Set P} : (1 : G) ∈ s /ₛ t ↔ ¬Disjoint s t := by
  simp [not_disjoint_iff_nonempty_inter, mem_sdiv, Set.Nonempty]

@[to_additive]
/-
**Set.Nonempty.one_mem_sdiv_self** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {G : Type u_1} {P : Type u_2} [inst : Group G] [T : Torsor G P] {s : Set
 P}, s.Nonempty → 1 ∈ s /ₛ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiv_self`：sdiv_self (p : P) : p /ₛ p = (1 : G)
-/
theorem Nonempty.one_mem_sdiv_self {s : Set P} (h : s.Nonempty) : (1 : G) ∈ s /ₛ s :=
  let ⟨p, hp⟩ := h
  ⟨p, hp, p, hp, sdiv_self _⟩

end Set
/-- If dividing two points by the same point produces equal results, those points are equal. -/
@[to_additive /-- If the same point subtracted from two points produces equal
results, those points are equal. -/]
/-
**sdiv_left_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_left_cancel {p₁ p₂ p : P} (h : p₁ /ₛ p = p₂ /ₛ p) : p₁ = p₂
参数：h : p₁ /ₛ p = p₂ /ₛ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiv_eq_one_iff_eq`：sdiv_eq_one_iff_eq {p₁ p₂ : P} : p₁ /ₛ p₂ = (1 : G) 
↔ p₁ = p₂
· 使用定理 `sdiv_div_sdiv_cancel_right`：sdiv_div_sdiv_cancel_right (p₁ p₂ p₃ : P) : 
(p₁ /ₛ p₃) / (p₂ /ₛ p₃) = p₁ /ₛ p₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_one`：div_eq_one : a / b = 1 ↔ a = b
-/
theorem sdiv_left_cancel {p₁ p₂ p : P} (h : p₁ /ₛ p = p₂ /ₛ p) : p₁ = p₂ := by
  rwa [← div_eq_one, sdiv_div_sdiv_cancel_right, sdiv_eq_one_iff_eq] at h

/-- Dividing two points by the same point produces equal results
if and only if those points are equal. -/
@[to_additive (attr := simp) /-- The same point subtracted from two points produces equal results
if and only if those points are equal. -/]
/-
**sdiv_left_cancel_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_left_cancel_iff {p₁ p₂ p : P} : p₁ /ₛ p = p₂ /ₛ p ↔ p₁ = p₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiv_left_cancel`：sdiv_left_cancel {p₁ p₂ p : P} (h : p₁ /ₛ p = p₂ /ₛ p)
 : p₁ = p₂
-/
theorem sdiv_left_cancel_iff {p₁ p₂ p : P} : p₁ /ₛ p = p₂ /ₛ p ↔ p₁ = p₂ :=
  ⟨sdiv_left_cancel, fun h => h ▸ rfl⟩

/-- Dividing by the point `p` is an injective function. -/
@[to_additive /-- Subtracting the point `p` is an injective function. -/]
/-
**sdiv_left_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_left_injective (p : P) : Function.Injective ((· /ₛ p) : P -> G)
参数：p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiv_left_cancel`：sdiv_left_cancel {p₁ p₂ p : P} (h : p₁ /ₛ p = p₂ /ₛ p)
 : p₁ = p₂

--- 原说明 ---
Dividing by the point `p` is an injective function.
-/
theorem sdiv_left_injective (p : P) : Function.Injective ((· /ₛ p) : P → G) := fun _ _ =>
  sdiv_left_cancel

/-- If dividing the same point by two points produces equal results, those points are equal. -/
@[to_additive /-- If subtracting two points from the same point produces equal
results, those points are equal. -/]
/-
**sdiv_right_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_right_cancel {p₁ p₂ p : P} (h : p /ₛ p₁ = p /ₛ p₂) : p₁ = p₂
参数：h : p /ₛ p₁ = p /ₛ p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_left_cancel`：smul_left_cancel (g : α) {x y : β} (h : g • x = g • y)
 : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiv_smul`：sdiv_smul (p₁ p₂ : P) : (p₁ /ₛ p₂) • p₂ = p₁
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sdiv_right_cancel {p₁ p₂ p : P} (h : p /ₛ p₁ = p /ₛ p₂) : p₁ = p₂ := by
  refine smul_left_cancel (p /ₛ p₂) ?_
  rw [sdiv_smul, ← h, sdiv_smul]

/-- Subtracting two points from the same point produces equal results
if and only if those points are equal. -/
@[to_additive (attr := simp)]
/-
**sdiv_right_cancel_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_right_cancel_iff {p₁ p₂ p : P} : p /ₛ p₁ = p /ₛ p₂ ↔ p₁ = p₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiv_right_cancel`：sdiv_right_cancel {p₁ p₂ p : P} (h : p /ₛ p₁ = p /ₛ p
₂) : p₁ = p₂

--- 原说明 ---
Subtracting two points from the same point produces equal results
if and only if those points are equal.
-/
theorem sdiv_right_cancel_iff {p₁ p₂ p : P} : p /ₛ p₁ = p /ₛ p₂ ↔ p₁ = p₂ :=
  ⟨sdiv_right_cancel, fun h => h ▸ rfl⟩

/-- Dividing the point `p` by other points is an injective function. -/
@[to_additive /-- Subtracting a point from the point `p` is an injective function. -/]
/-
**sdiv_right_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_right_injective (p : P) : Function.Injective ((p /ₛ ·) : P -> G)
参数：p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiv_right_cancel`：sdiv_right_cancel {p₁ p₂ p : P} (h : p /ₛ p₁ = p /ₛ p
₂) : p₁ = p₂

--- 原说明 ---
Dividing the point `p` by other points is an injective function.
-/
theorem sdiv_right_injective (p : P) : Function.Injective ((p /ₛ ·) : P → G) := fun _ _ =>
  sdiv_right_cancel

end General

section comm

variable {G : Type*} {P : Type*} [CommGroup G] [Torsor G P]

/-- Cancellation dividing the results of two divisions. -/
@[to_additive (attr := simp) /-- Cancellation subtracting the results of two subtractions. -/]
/-
**sdiv_div_sdiv_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_div_sdiv_cancel_left (p₁ p₂ p₃ : P) : (p₃ /ₛ p₂) / (p₃ /ₛ p₁) = p₁ /ₛ
 p₂
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_sdiv_eq_sdiv_rev`：inv_sdiv_eq_sdiv_rev (p₁ p₂ : P) : (p₁ /ₛ p₂)⁻¹ = 
p₂ /ₛ p₁
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `sdiv_mul_sdiv_cancel`：sdiv_mul_sdiv_cancel (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂) *
 (p₂ /ₛ p₃) = p₁ /ₛ p₃

--- 原说明 ---
Cancellation dividing the results of two divisions.
-/
theorem sdiv_div_sdiv_cancel_left (p₁ p₂ p₃ : P) : (p₃ /ₛ p₂) / (p₃ /ₛ p₁) = p₁ /ₛ p₂ := by
  rw [div_eq_mul_inv, inv_sdiv_eq_sdiv_rev, mul_comm, sdiv_mul_sdiv_cancel]

@[to_additive (attr := simp)]
/-
**smul_sdiv_smul_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_sdiv_smul_cancel_left (v : G) (p₁ p₂ : P) : (v • p₁) /ₛ (v • p₂) = p₁
 /ₛ p₂
参数：v : G；p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiv_smul_eq_sdiv_div`：sdiv_smul_eq_sdiv_div (p₁ p₂ : P) (g : G) : p₁ /ₛ
 (g • p₂) = (p₁ /ₛ p₂) / g
· 使用定理 `smul_sdiv_assoc`：smul_sdiv_assoc (g : G) (p₁ p₂ : P) : (g • p₁) /ₛ p₂ = 
g * (p₁ /ₛ p₂)
· 使用定理 `mul_div_cancel_left`：mul_div_cancel_left (a b : G) : a * b / a = b
-/
theorem smul_sdiv_smul_cancel_left (v : G) (p₁ p₂ : P) : (v • p₁) /ₛ (v • p₂) = p₁ /ₛ p₂ := by
  rw [sdiv_smul_eq_sdiv_div, smul_sdiv_assoc, mul_div_cancel_left]

@[to_additive]
/-
**smul_sdiv_smul_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_sdiv_smul_comm (v₁ v₂ : G) (p₁ p₂ : P) : (v₁ • p₁) /ₛ (v₂ • p₂) = (v₁
 / v₂) * (p₁ /ₛ p₂)
参数：v₁ v₂ : G；p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiv_smul_eq_sdiv_div`：sdiv_smul_eq_sdiv_div (p₁ p₂ : P) (g : G) : p₁ /ₛ
 (g • p₂) = (p₁ /ₛ p₂) / g
· 使用定理 `smul_sdiv_assoc`：smul_sdiv_assoc (g : G) (p₁ p₂ : P) : (g • p₁) /ₛ p₂ = 
g * (p₁ /ₛ p₂)
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm_div`：mul_comm_div : a / b * c = a * (c / b)
-/
theorem smul_sdiv_smul_comm (v₁ v₂ : G) (p₁ p₂ : P) :
    (v₁ • p₁) /ₛ (v₂ • p₂) = (v₁ / v₂) * (p₁ /ₛ p₂) := by
  rw [sdiv_smul_eq_sdiv_div, smul_sdiv_assoc, mul_div_assoc, ← mul_comm_div]

@[to_additive]
/-
**div_mul_sdiv_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_sdiv_comm (v₁ v₂ : G) (p₁ p₂ : P) : (v₁ / v₂) * (p₁ /ₛ p₂) = (v₁ •
 p₁) /ₛ (v₂ • p₂)
参数：v₁ v₂ : G；p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_sdiv_smul_comm`：smul_sdiv_smul_comm (v₁ v₂ : G) (p₁ p₂ : P) : (v₁ •
 p₁) /ₛ (v₂ • p₂) = (v₁ / v₂) * (p₁ /ₛ p₂)
-/
theorem div_mul_sdiv_comm (v₁ v₂ : G) (p₁ p₂ : P) :
    (v₁ / v₂) * (p₁ /ₛ p₂) = (v₁ • p₁) /ₛ (v₂ • p₂) :=
  smul_sdiv_smul_comm _ _ _ _ |>.symm

@[to_additive]
/-
**sdiv_smul_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_smul_comm (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂ : G) • p₃ = (p₃ /ₛ p₂) • p₁
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiv_eq_one_iff_eq`：sdiv_eq_one_iff_eq {p₁ p₂ : P} : p₁ /ₛ p₂ = (1 : G) 
↔ p₁ = p₂
· 使用定理 `smul_sdiv_assoc`：smul_sdiv_assoc (g : G) (p₁ p₂ : P) : (g • p₁) /ₛ p₂ = 
g * (p₁ /ₛ p₂)
· 使用定理 `sdiv_smul_eq_sdiv_div`：sdiv_smul_eq_sdiv_div (p₁ p₂ : P) (g : G) : p₁ /ₛ
 (g • p₂) = (p₁ /ₛ p₂) / g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sdiv_div_sdiv_cancel_left`：sdiv_div_sdiv_cancel_left (p₁ p₂ p₃ : P) : (p
₃ /ₛ p₂) / (p₃ /ₛ p₁) = p₁ /ₛ p₂
· 使用定理 `sdiv_mul_sdiv_cancel`：sdiv_mul_sdiv_cancel (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂) *
 (p₂ /ₛ p₃) = p₁ /ₛ p₃
· 使用定理 `sdiv_self`：sdiv_self (p : P) : p /ₛ p = (1 : G)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sdiv_smul_comm (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂ : G) • p₃ = (p₃ /ₛ p₂) • p₁ := by
  rw [← @sdiv_eq_one_iff_eq G, smul_sdiv_assoc, sdiv_smul_eq_sdiv_div]
  simp

@[to_additive]
/-
**smul_eq_smul_iff_div_eq_sdiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_eq_smul_iff_div_eq_sdiv {v₁ v₂ : G} {p₁ p₂ : P} : v₁ • p₁ = v₂ • p₂ ↔
 v₂ / v₁ = p₁ /ₛ p₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_eq_smul_iff_inv_mul_eq_sdiv`：smul_eq_smul_iff_inv_mul_eq_sdiv {v₁ v
₂ : G} {p₁ p₂ : P} : v₁ • p₁ = v₂ • p₂ ↔ v₁⁻¹ * v₂ = p₁ /ₛ p₂
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem smul_eq_smul_iff_div_eq_sdiv {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ • p₁ = v₂ • p₂ ↔ v₂ / v₁ = p₁ /ₛ p₂ := by
  rw [smul_eq_smul_iff_inv_mul_eq_sdiv, inv_mul_eq_div]

@[to_additive]
/-
**sdiv_div_sdiv_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_div_sdiv_comm (p₁ p₂ p₃ p₄ : P) : (p₁ /ₛ p₂) / (p₃ /ₛ p₄) = (p₁ /ₛ p₃
) / (p₂ /ₛ p₄)
参数：p₁ p₂ p₃ p₄ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiv_smul_eq_sdiv_div`：sdiv_smul_eq_sdiv_div (p₁ p₂ : P) (g : G) : p₁ /ₛ
 (g • p₂) = (p₁ /ₛ p₂) / g
· 使用定理 `sdiv_smul_comm`：sdiv_smul_comm (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂ : G) • p₃ = (p
₃ /ₛ p₂) • p₁
-/
theorem sdiv_div_sdiv_comm (p₁ p₂ p₃ p₄ : P) :
    (p₁ /ₛ p₂) / (p₃ /ₛ p₄) = (p₁ /ₛ p₃) / (p₂ /ₛ p₄) := by
  rw [← sdiv_smul_eq_sdiv_div, sdiv_smul_comm, sdiv_smul_eq_sdiv_div]

namespace Set

@[to_additive (attr := simp)]
/-
**Set.smul_set_sdiv_smul_set** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_sdiv_smul_set (v : G) (s t : Set P) : (v • s) /ₛ (v • t) = s /ₛ t
参数：v : G；s t : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_sdiv_smul_cancel_left`：smul_sdiv_smul_cancel_left (v : G) (p₁ p₂ : 
P) : (v • p₁) /ₛ (v • p₂) = p₁ /ₛ p₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma smul_set_sdiv_smul_set (v : G) (s t : Set P) : (v • s) /ₛ (v • t) = s /ₛ t := by
  ext; simp [mem_sdiv, mem_smul_set]

end Set

end comm

namespace Prod

variable {G G' P P' : Type*} [Group G] [Group G'] [Torsor G P] [Torsor G' P']

@[to_additive]
/-
**Prod.instTorsor** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instTorsor : Torsor (G × G') (P × P') where smul v p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTorsor : Torsor (G × G') (P × P') where
  smul v p := (v.1 • p.1, v.2 • p.2)
  one_smul _ := Prod.ext (one_smul _ _) (one_smul _ _)
  mul_smul _ _ _ := Prod.ext (mul_smul _ _ _) (mul_smul _ _ _)
  sdiv p₁ p₂ := (p₁.1 /ₛ p₂.1, p₁.2 /ₛ p₂.2)
  sdiv_smul' _ _ := Prod.ext (sdiv_smul _ _) (sdiv_smul _ _)
  smul_sdiv' _ _ := Prod.ext (smul_sdiv _ _) (smul_sdiv _ _)

@[to_additive (attr := simp)]
/-
**Prod.fst_smul** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_smul (v : G × G') (p : P × P') : (v • p).1 = v.1 • p.1
参数：v : G × G'；p : P × P'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_smul (v : G × G') (p : P × P') : (v • p).1 = v.1 • p.1 :=
  rfl

@[to_additive (attr := simp)]
/-
**Prod.snd_smul** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_smul (v : G × G') (p : P × P') : (v • p).2 = v.2 • p.2
参数：v : G × G'；p : P × P'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_smul (v : G × G') (p : P × P') : (v • p).2 = v.2 • p.2 :=
  rfl

@[to_additive (attr := simp)]
/-
**Prod.mk_smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_smul_mk (v : G) (v' : G') (p : P) (p' : P') : (v, v') • (p, p') = (v • 
p, v' • p')
参数：v : G；v' : G'；p : P；p' : P'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_smul_mk (v : G) (v' : G') (p : P) (p' : P') : (v, v') • (p, p') = (v • p, v' • p') :=
  rfl

@[to_additive (attr := simp)]
/-
**Prod.fst_sdiv** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_sdiv (p₁ p₂ : P × P') : (p₁ /ₛ p₂ : G × G').1 = p₁.1 /ₛ p₂.1
参数：p₁ p₂ : P × P'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_sdiv (p₁ p₂ : P × P') : (p₁ /ₛ p₂ : G × G').1 = p₁.1 /ₛ p₂.1 :=
  rfl

@[to_additive (attr := simp)]
/-
**Prod.snd_sdiv** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_sdiv (p₁ p₂ : P × P') : (p₁ /ₛ p₂ : G × G').2 = p₁.2 /ₛ p₂.2
参数：p₁ p₂ : P × P'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_sdiv (p₁ p₂ : P × P') : (p₁ /ₛ p₂ : G × G').2 = p₁.2 /ₛ p₂.2 :=
  rfl

@[to_additive (attr := simp)]
/-
**Prod.mk_sdiv_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_sdiv_mk (p₁ p₂ : P) (p₁' p₂' : P') : ((p₁, p₁') /ₛ (p₂, p₂') : G × G') 
= (p₁ /ₛ p₂, p₁' /ₛ p₂')
参数：p₁ p₂ : P；p₁' p₂' : P'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_sdiv_mk (p₁ p₂ : P) (p₁' p₂' : P') :
    ((p₁, p₁') /ₛ (p₂, p₂') : G × G') = (p₁ /ₛ p₂, p₁' /ₛ p₂') :=
  rfl

end Prod

namespace Set

variable {G G' P P' : Type*} [Group G] [Group G'] [Torsor G P] [Torsor G' P']

@[to_additive prod_vsub_prod_comm]
/-
**Set.prod_sdiv_prod_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_sdiv_prod_comm (s₁ s₂ : Set P) (t₁ t₂ : Set P') : (s₁ ×ˢ t₁) /ₛ (s₂ ×
ˢ t₂) = (s₁ /ₛ s₂) ×ˢ (t₁ /ₛ t₂)
参数：s₁ s₂ : Set P；t₁ t₂ : Set P'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_sdiv_prod_comm (s₁ s₂ : Set P) (t₁ t₂ : Set P') :
    (s₁ ×ˢ t₁) /ₛ (s₂ ×ˢ t₂) = (s₁ /ₛ s₂) ×ˢ (t₁ /ₛ t₂) := by
  aesop (add norm simp [mem_sdiv, mem_prod])

end Set

namespace Pi

universe u v w

variable {I : Type u} {fg : I → Type v} [∀ i, Group (fg i)] {fp : I → Type w}
  [∀ i, Torsor (fg i) (fp i)]

/-- A product of `Torsor`s is a `Torsor`. -/
@[to_additive /-- A product of `AddTorsor`s is an `AddTorsor`. -/]
/-
**Pi.instTorsor** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instTorsor : Torsor (forall i, fg i) (forall i, fp i) where sdiv p₁ p₂ i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product of `Torsor`s is a `Torsor`.
-/
instance instTorsor : Torsor (∀ i, fg i) (∀ i, fp i) where
  sdiv p₁ p₂ i := p₁ i /ₛ p₂ i
  sdiv_smul' p₁ p₂ := funext fun i => sdiv_smul (p₁ i) (p₂ i)
  smul_sdiv' g p := funext fun i => smul_sdiv (g i) (p i)

@[to_additive (attr := simp)]
/-
**Pi.sdiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：sdiv_apply (p q : forall i, fp i) (i : I) : (p /ₛ q) i = p i /ₛ q i
参数：p q : forall i, fp i；i : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiv_apply (p q : ∀ i, fp i) (i : I) : (p /ₛ q) i = p i /ₛ q i :=
  rfl

@[to_additive (attr := push ←)]
/-
**Pi.sdiv_def** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：sdiv_def (p q : forall i, fp i) : p /ₛ q = fun i => p i /ₛ q i
参数：p q : forall i, fp i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiv_def (p q : ∀ i, fp i) : p /ₛ q = fun i => p i /ₛ q i :=
  rfl

end Pi

namespace Equiv

variable (G : Type*) (P : Type*) [Group G] [Torsor G P]

@[to_additive (attr := simp)]
/-
**Equiv.constSMul_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：constSMul_one : constSMul P (1 : G) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem constSMul_one : constSMul P (1 : G) = 1 :=
  ext <| one_smul G

variable {G}

@[to_additive (attr := simp)]
/-
**Equiv.constSMul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：constSMul_mul (v₁ v₂ : G) : constSMul P (v₁ * v₂) = constSMul P v₁ * const
SMul P v₂
参数：v₁ v₂ : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem constSMul_mul (v₁ v₂ : G) : constSMul P (v₁ * v₂) = constSMul P v₁ * constSMul P v₂ :=
  ext <| mul_smul v₁ v₂

/-- `Equiv.constVAdd` as a homomorphism from `Multiplicative G` to `Equiv.perm P` -/
/-
**Equiv.constVAddHom** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：constVAddHom (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P] : Multip
licative G ->* Equiv.Perm P where toFun v
参数：G : Type*；P : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.constVAdd_zero`：∀ (G : Type u_1) (P : Type u_2) [inst : AddGroup G
] [inst_1 : AddTorsor G P], Equiv.constVAdd P 0 = 1

--- 原说明 ---
`Equiv.constVAdd` as a homomorphism from `Multiplicative G` to `Equiv.perm P`
-/
def constVAddHom (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P] :
    Multiplicative G →* Equiv.Perm P where
  toFun v := constVAdd P (v.toAdd)
  map_one' := constVAdd_zero G P
  map_mul' v v' := constVAdd_add P v.toAdd v'.toAdd

/-- `Equiv.constSMul` as a homomorphism from `G` to `Equiv.perm P` -/
/-
**Equiv.constSMulHom** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：constSMulHom : G ->* Equiv.Perm P where toFun v
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.constSMul_one`：constSMul_one : constSMul P (1 : G) = 1
· 使用定理 `Equiv.constSMul_mul`：constSMul_mul (v₁ v₂ : G) : constSMul P (v₁ * v₂) =
 constSMul P v₁ * constSMul P v₂

--- 原说明 ---
`Equiv.constSMul` as a homomorphism from `G` to `Equiv.perm P`
-/
def constSMulHom : G →* Equiv.Perm P where
  toFun v := constSMul P v
  map_one' := constSMul_one G P
  map_mul' := constSMul_mul P

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

open Function

@[simp]
/-
**Equiv.left_vsub_pointReflection** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：left_vsub_pointReflection (x y : P) : x -ᵥ pointReflection x y = y -ᵥ x
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `Equiv.pointReflection_vsub_left`：pointReflection_vsub_left (x y : P) : p
ointReflection x y -ᵥ x = x -ᵥ y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem left_vsub_pointReflection (x y : P) : x -ᵥ pointReflection x y = y -ᵥ x :=
  neg_injective <| by simp

@[simp]
/-
**Equiv.right_vsub_pointReflection** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：right_vsub_pointReflection (x y : P) : y -ᵥ pointReflection x y = 2 • (y -
ᵥ x)
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `Equiv.pointReflection_vsub_right`：pointReflection_vsub_right (x y : P) :
 pointReflection x y -ᵥ y = 2 • (x -ᵥ y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem right_vsub_pointReflection (x y : P) : y -ᵥ pointReflection x y = 2 • (y -ᵥ x) :=
  neg_injective <| by simp [← neg_nsmul]

/-- `x` is the only fixed point of `pointReflection x`. This lemma requires
`x + x = y + y ↔ x = y`. There is no typeclass to use here, so we add it as an explicit argument. -/
/-
**Equiv.pointReflection_fixed_iff_of_injective_two_nsmul** 是 Mathlib 中的一个定理，位于命名
空间 `Equiv`。
形式化陈述：pointReflection_fixed_iff_of_injective_two_nsmul {x y : P} (h : Injective 
(2 • · : G -> G)) : pointReflection x y = y ↔ y = x
参数：h : Injective (2 • · : G -> G)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.pointReflection_apply`：pointReflection_apply (x y : P) : pointRefl
ection x y = (x -ᵥ y) +ᵥ x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_vadd_iff_vsub_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p₁ : P) (g : G) (p₂ : P),   p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `neg_eq_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
-a = b ↔ a + b = 0
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`x` is the only fixed point of `pointReflection x`. This lemma requires
`x + x = y + y ↔ x = y`. There is no typeclass to use here, so we add it as an e
xplicit argument.
-/
theorem pointReflection_fixed_iff_of_injective_two_nsmul {x y : P} (h : Injective (2 • · : G → G)) :
    pointReflection x y = y ↔ y = x := by
  rw [pointReflection_apply, eq_comm, eq_vadd_iff_vsub_eq, ← neg_vsub_eq_vsub_rev,
    neg_eq_iff_add_eq_zero, ← two_nsmul, ← nsmul_zero 2, h.eq_iff, vsub_eq_zero_iff_eq, eq_comm]
/-
**Equiv.injective_pointReflection_left_of_injective_two_nsmul** 是 Mathlib 中的一个定理
，位于命名空间 `Equiv`。
形式化陈述：injective_pointReflection_left_of_injective_two_nsmul {G P : Type*} [AddCo
mmGroup G] [AddTorsor G P] (h : Injective (2 • · : G -> G)) (y : P) : Injective 
fun x : P => pointReflection x y
参数：h : Injective (2 • · : G -> G)；y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `neg_eq_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
-a = b ↔ a + b = 0
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `vadd_eq_vadd_iff_sub_eq_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : Ad
dCommGroup G] [inst_1 : AddTorsor G P] {v₁ v₂ : G} {p₁ p₂ : P},   v₁ +ᵥ p₁ = v₂ 
+ᵥ p₂ ↔ v₂ - v₁ = …
· 使用定理 `Equiv.pointReflection_apply`：pointReflection_apply (x y : P) : pointRefl
ection x y = (x -ᵥ y) +ᵥ x
-/
theorem injective_pointReflection_left_of_injective_two_nsmul {G P : Type*} [AddCommGroup G]
    [AddTorsor G P] (h : Injective (2 • · : G → G)) (y : P) :
    Injective fun x : P => pointReflection x y :=
  fun x₁ x₂ (hy : pointReflection x₁ y = pointReflection x₂ y) => by
  rwa [pointReflection_apply, pointReflection_apply, vadd_eq_vadd_iff_sub_eq_vsub,
    vsub_sub_vsub_cancel_right, ← neg_vsub_eq_vsub_rev, neg_eq_iff_add_eq_zero,
    ← two_nsmul, ← nsmul_zero 2, h.eq_iff, vsub_eq_zero_iff_eq] at hy

/-- In the special case of additive commutative groups (as opposed to just additive torsors),
`Equiv.pointReflection x` coincides with `Equiv.subLeft (2 • x)`. -/
/-
**Equiv.pointReflection_eq_subLeft** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：pointReflection_eq_subLeft {G : Type*} [AddCommGroup G] (x : G) : pointRef
lection x = Equiv.subLeft (2 • x)
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - b + c = a + c - b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `Equiv.subLeft_apply`：∀ {G : Type u_5} [inst : AddGroup G] (a b : G), (Eq
uiv.subLeft a) b = a - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the special case of additive commutative groups (as opposed to just additive 
torsors),
`Equiv.pointReflection x` coincides with `Equiv.subLeft (2 • x)`.
-/
lemma pointReflection_eq_subLeft {G : Type*} [AddCommGroup G] (x : G) :
    pointReflection x = Equiv.subLeft (2 • x) := by
  ext; simp [pointReflection, sub_add_eq_add_sub, two_nsmul]

end Equiv

/-- Pullback of a torsor along an injective map. -/
@[to_additive /-- Pullback of an add torsor along an injective map. -/]
/-
**Function.Injective.torsor** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.Injective.torsor {G P Q : Type*} [Group G] [Torsor G P] [SMul G Q
] [SDiv G Q] [Nonempty Q] (f : Q -> P) (hf : Function.Injective f) (smul : foral
l (c : G) (x : Q), f (c • x) = c • f x) (sdiv : forall (x y : Q), x /ₛ y = f x /
ₛ f y) : Torsor G Q where __
参数：f : Q -> P；hf : Function.Injective f；smul : forall (c : G) (x : Q), f (c • x)
 = c • f x；sdiv : forall (x y : Q), x /ₛ y = f x /ₛ f y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback of a torsor along an injective map.
-/
abbrev Function.Injective.torsor {G P Q : Type*}
    [Group G] [Torsor G P] [SMul G Q] [SDiv G Q] [Nonempty Q] (f : Q → P)
    (hf : Function.Injective f)
    (smul : ∀ (c : G) (x : Q), f (c • x) = c • f x)
    (sdiv : ∀ (x y : Q), x /ₛ y = f x /ₛ f y) : Torsor G Q where
  __ := hf.mulAction f smul
  sdiv_smul' x y := hf <| by simp only [sdiv, smul, sdiv_smul]
  smul_sdiv' c x := by simp [sdiv, smul]

/-- Pushforward of a torsor along a surjective map. -/
@[to_additive /-- Pushforward of an add torsor along a surjective map. -/]
/-
**Function.Surjective.torsor** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.Surjective.torsor {G P Q : Type*} [Group G] [Torsor G P] [SMul G 
Q] [SDiv G Q] (f : P -> Q) (hf : Surjective f) (smul : forall (c : G) (x : P), f
 (c • x) = c • f x) (sdiv : forall (x y : P), x /ₛ y = f x /ₛ f y) : Torsor G Q 
where __
参数：f : P -> Q；hf : Surjective f；smul : forall (c : G) (x : P), f (c • x) = c • f
 x；sdiv : forall (x y : P), x /ₛ y = f x /ₛ f y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushforward of a torsor along a surjective map.
-/
abbrev Function.Surjective.torsor {G P Q : Type*}
    [Group G] [Torsor G P] [SMul G Q] [SDiv G Q]
    (f : P → Q) (hf : Surjective f)
    (smul : ∀ (c : G) (x : P), f (c • x) = c • f x)
    (sdiv : ∀ (x y : P), x /ₛ y = f x /ₛ f y) : Torsor G Q where
  __ := hf.mulAction f smul
  nonempty := Torsor.nonempty.map f
  sdiv_smul' := by simp [hf.forall, ← smul, ← sdiv]
  smul_sdiv' := by simp [hf.forall, ← smul, ← sdiv]
