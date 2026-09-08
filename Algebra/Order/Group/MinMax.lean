/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax

/-!
# `min` and `max` in linearly ordered groups.
-/

public section


section

variable {α : Type*} [Group α] [LinearOrder α] [MulLeftMono α]

-- TODO: This duplicates `oneLePart_div_leOnePart`
@[to_additive (attr := simp)]
/-
**max_one_div_max_inv_one_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_one_div_max_inv_one_eq_self (a : α) : max a 1 / max a⁻¹ 1 = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem max_one_div_max_inv_one_eq_self (a : α) : max a 1 / max a⁻¹ 1 = a := by
  rcases le_total a 1 with (h | h) <;> simp [h]

alias max_zero_sub_eq_self := max_zero_sub_max_neg_zero_eq_self

@[to_additive]
/-
**max_inv_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：max_inv_one (a : α) : max a⁻¹ 1 = a⁻¹ * max a 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_inv_mul_iff_mul_eq`：eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_div_iff_mul_eq'`：eq_div_iff_mul_eq' : a = b / c ↔ a * c = b
· 使用定理 `max_one_div_max_inv_one_eq_self`：max_one_div_max_inv_one_eq_self (a : α)
 : max a 1 / max a⁻¹ 1 = a
-/
lemma max_inv_one (a : α) : max a⁻¹ 1 = a⁻¹ * max a 1 := by
  rw [eq_inv_mul_iff_mul_eq, ← eq_div_iff_mul_eq', max_one_div_max_inv_one_eq_self]

end

section Inv

variable {G₀ : Type*} [Inv G₀] [LinearOrder G₀] {x y : G₀}

/-
**min_inv_inv_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_inv_inv_le : min x⁻¹ y⁻¹ <= (max x y)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
-/
lemma min_inv_inv_le : min x⁻¹ y⁻¹ ≤ (max x y)⁻¹ := by
  cases le_total x y <;> simp_all

end Inv

section LinearOrderedCommGroup

variable {α : Type*} [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

@[to_additive min_neg_neg]
/-
**min_inv_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_inv_inv' (a b : α) : min a⁻¹ b⁻¹ = (max a b)⁻¹
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_le_inv_iff`：inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem min_inv_inv' (a b : α) : min a⁻¹ b⁻¹ = (max a b)⁻¹ :=
  Eq.symm <| (@Monotone.map_max α αᵒᵈ _ _ Inv.inv a b) fun _ _ =>
    inv_le_inv_iff.mpr

@[to_additive max_neg_neg]
/-
**max_inv_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_inv_inv' (a b : α) : max a⁻¹ b⁻¹ = (min a b)⁻¹
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_le_inv_iff`：inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem max_inv_inv' (a b : α) : max a⁻¹ b⁻¹ = (min a b)⁻¹ :=
  Eq.symm <| (@Monotone.map_min α αᵒᵈ _ _ Inv.inv a b) fun _ _ =>
    inv_le_inv_iff.mpr

@[to_additive min_sub_sub_right]
/-
**min_div_div_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_div_div_right' (a b c : α) : min (a / c) (b / c) = min a b / c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `min_mul_mul_right`：min_mul_mul_right (a b c : α) : min (a * c) (b * c) =
 min a b * c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem min_div_div_right' (a b c : α) : min (a / c) (b / c) = min a b / c := by
  simpa only [div_eq_mul_inv] using min_mul_mul_right a b c⁻¹

@[to_additive max_sub_sub_right]
/-
**max_div_div_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_div_div_right' (a b c : α) : max (a / c) (b / c) = max a b / c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `max_mul_mul_right`：max_mul_mul_right (a b c : α) : max (a * c) (b * c) =
 max a b * c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem max_div_div_right' (a b c : α) : max (a / c) (b / c) = max a b / c := by
  simpa only [div_eq_mul_inv] using max_mul_mul_right a b c⁻¹

@[to_additive min_sub_sub_left]
/-
**min_div_div_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_div_div_left' (a b c : α) : min (a / b) (a / c) = a / max b c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `min_mul_mul_left`：min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a
 * min b c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `min_inv_inv'`：min_inv_inv' (a b : α) : min a⁻¹ b⁻¹ = (max a b)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem min_div_div_left' (a b c : α) : min (a / b) (a / c) = a / max b c := by
  simp only [div_eq_mul_inv, min_mul_mul_left, min_inv_inv']

@[to_additive max_sub_sub_left]
/-
**max_div_div_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_div_div_left' (a b c : α) : max (a / b) (a / c) = a / min b c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `max_mul_mul_left`：max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a
 * max b c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `max_inv_inv'`：max_inv_inv' (a b : α) : max a⁻¹ b⁻¹ = (min a b)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem max_div_div_left' (a b c : α) : max (a / b) (a / c) = a / min b c := by
  simp only [div_eq_mul_inv, max_mul_mul_left, max_inv_inv']

end LinearOrderedCommGroup

section LinearOrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-
**max_sub_max_le_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_sub_max_le_max (a b c d : α) : max a b - max c d <= max (a - c) (b - d
)
参数：a b c d : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem max_sub_max_le_max (a b c d : α) : max a b - max c d ≤ max (a - c) (b - d) := by
  grind
/-
**abs_max_sub_max_le_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_max_sub_max_le_max (a b c d : α) : |max a b - max c d| <= max |a - c| 
|b - d|
参数：a b c d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_sub_le_iff`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] {a b c : G},   |a - b| ≤ c ↔ a - b ≤ c ∧ b - a 
≤ c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `max_sub_max_le_max`：max_sub_max_le_max (a b c d : α) : max a b - max c d
 <= max (a - c) (b - d)
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
-/
theorem abs_max_sub_max_le_max (a b c d : α) : |max a b - max c d| ≤ max |a - c| |b - d| := by
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))
  · rw [abs_sub_comm a c, abs_sub_comm b d]
    exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))
/-
**abs_min_sub_min_le_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_min_sub_min_le_max (a b c d : α) : |min a b - min c d| <= max |a - c| 
|b - d|
参数：a b c d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `max_neg_neg`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOr
der α] [IsOrderedAddMonoid α] (a b : α),   max (-a) (-b) = -min a b
· 使用定理 `neg_sub_neg`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α)
, -a - -b = b - a
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
· 使用定理 `abs_max_sub_max_le_max`：abs_max_sub_max_le_max (a b c d : α) : |max a b 
- max c d| <= max |a - c| |b - d|
-/
theorem abs_min_sub_min_le_max (a b c d : α) : |min a b - min c d| ≤ max |a - c| |b - d| := by
  simpa only [max_neg_neg, neg_sub_neg, abs_sub_comm] using
    abs_max_sub_max_le_max (-a) (-b) (-c) (-d)
/-
**abs_max_sub_max_le_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_max_sub_max_le_abs (a b c : α) : |max a c - max b c| <= |a - b|
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `abs_max_sub_max_le_max`：abs_max_sub_max_le_max (a b c d : α) : |max a b 
- max c d| <= max |a - c| |b - d|
-/
theorem abs_max_sub_max_le_abs (a b c : α) : |max a c - max b c| ≤ |a - b| := by
  simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (a - b))]
    using abs_max_sub_max_le_max a c b c

end LinearOrderedAddCommGroup

