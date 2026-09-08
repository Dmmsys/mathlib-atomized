/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
module

public import Mathlib.Algebra.Field.Opposite
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Ring.Periodic

/-!
# Periodic functions

This file proves facts about periodic and antiperiodic functions from and to a field.

## Main definitions

* `Function.Periodic`: A function `f` is *periodic* if `∀ x, f (x + c) = f x`.
  `f` is referred to as periodic with period `c` or `c`-periodic.

* `Function.Antiperiodic`: A function `f` is *antiperiodic* if `∀ x, f (x + c) = -f x`.
  `f` is referred to as antiperiodic with antiperiod `c` or `c`-antiperiodic.

Note that any `c`-antiperiodic function will necessarily also be `2 • c`-periodic.

## Tags

period, periodic, periodicity, antiperiodic
-/

public section

assert_not_exists TwoSidedIdeal

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

open Set

namespace Function

/-! ### Periodicity -/

/-
**Function.Periodic.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {c : α} [inst :
 AddMonoid α] [inst_1 : Group γ]   [inst_2 : DistribMulAction γ α], Function.Per
iodic f c → ∀ (a : γ), Function.Periodic (fun x => f (a • x)) (a⁻¹ • c)
参数：a : γ；fun x => f (a • x)；a⁻¹ • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a

--- 原说明 ---
### Periodicity
-/
protected theorem Periodic.const_smul₀ [AddCommMonoid α] [DivisionSemiring γ] [Module γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  by_cases ha : a = 0
  · simp only [ha, zero_smul]
  · simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)
/-
**Function.Periodic.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : DivisionSemiri
ng α],   Function.Periodic f c → ∀ (a : α), Function.Periodic (fun x => f (a * x
)) (a⁻¹ * c)
参数：a : α；fun x => f (a * x)；a⁻¹ * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.const_smul₀`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {f : α → β} {c : α} [inst : AddCommMonoid α]   [inst_1 : DivisionSemiring 
γ] [inst_2 : _root_…
-/
protected theorem Periodic.const_mul [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a * x)) (a⁻¹ * c) :=
  Periodic.const_smul₀ h a
/-
**Function.Periodic.const_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {c : α} [inst :
 AddMonoid α] [inst_1 : Group γ]   [inst_2 : DistribMulAction γ α], Function.Per
iodic f c → ∀ (a : γ), Function.Periodic (fun x => f (a⁻¹ • x)) (a • c)
参数：a : γ；fun x => f (a⁻¹ • x)；a • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Function.Periodic.const_smul`：∀ {α : Type u_1} {β : Type u_2} {γ : Type 
u_3} {f : α → β} {c : α} [inst : AddMonoid α] [inst_1 : Group γ]   [inst_2 : Dis
tribMulAction γ α]…
-/
theorem Periodic.const_inv_smul₀ [AddCommMonoid α] [DivisionSemiring γ] [Module γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul₀ a⁻¹
/-
**Function.Periodic.const_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : DivisionSemiri
ng α],   Function.Periodic f c → ∀ (a : α), Function.Periodic (fun x => f (a⁻¹ *
 x)) (a * c)
参数：a : α；fun x => f (a⁻¹ * x)；a * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.const_inv_smul₀`：∀ {α : Type u_1} {β : Type u_2} {γ : 
Type u_3} {f : α → β} {c : α} [inst : AddCommMonoid α]   [inst_1 : DivisionSemir
ing γ] [inst_2 : _root_…
-/
theorem Periodic.const_inv_mul [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ a
/-
**Function.Periodic.mul_const** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : DivisionSemiri
ng α],   Function.Periodic f c → ∀ (a : α), Function.Periodic (fun x => f (x * a
)) (c * a⁻¹)
参数：a : α；fun x => f (x * a)；c * a⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.const_smul₀`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {f : α → β} {c : α} [inst : AddCommMonoid α]   [inst_1 : DivisionSemiring 
γ] [inst_2 : _root_…
-/
theorem Periodic.mul_const [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a)) (c * a⁻¹) :=
  h.const_smul₀ (MulOpposite.op a)
/-
**Function.Periodic.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : DivisionSemiri
ng α],   Function.Periodic f c → ∀ (a : α), Function.Periodic (fun x => f (x * a
)) (c / a)
参数：a : α；fun x => f (x * a)；c / a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Function.Periodic.mul_const`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}
 {c : α} [inst : DivisionSemiring α],   Function.Periodic f c → ∀ (a : α), Funct
ion.Periodic (fun…
-/
theorem Periodic.mul_const' [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a)) (c / a) := by simpa only [div_eq_mul_inv] using h.mul_const a
/-
**Function.Periodic.mul_const_inv** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : DivisionSemiri
ng α],   Function.Periodic f c → ∀ (a : α), Function.Periodic (fun x => f (x * a
⁻¹)) (c * a)
参数：a : α；fun x => f (x * a⁻¹)；c * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.const_inv_smul₀`：∀ {α : Type u_1} {β : Type u_2} {γ : 
Type u_3} {f : α → β} {c : α} [inst : AddCommMonoid α]   [inst_1 : DivisionSemir
ing γ] [inst_2 : _root_…
-/
theorem Periodic.mul_const_inv [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a⁻¹)) (c * a) :=
  h.const_inv_smul₀ (MulOpposite.op a)
/-
**Function.Periodic.div_const** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : DivisionSemiri
ng α],   Function.Periodic f c → ∀ (a : α), Function.Periodic (fun x => f (x / a
)) (c * a)
参数：a : α；fun x => f (x / a)；c * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Function.Periodic.mul_const_inv`：∀ {α : Type u_1} {β : Type u_2} {f : α 
→ β} {c : α} [inst : DivisionSemiring α],   Function.Periodic f c → ∀ (a : α), F
unction.Periodic (fun…
-/
theorem Periodic.div_const [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x / a)) (c * a) := by simpa only [div_eq_mul_inv] using h.mul_const_inv a

/-- If a function `f` is `Periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico 0 c` such that `f x = f y`. -/
/-
**Function.Periodic.exists_mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddCommGroup α
] [inst_1 : LinearOrder α]   [IsOrderedAddMonoid α] [Archimedean α],   Function.
Periodic f c → 0 < c → ∀ (x a : α), ∃ y ∈ Set.Ico a (a + c), f x = f y
参数：x a : α；a + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_add_zsmul_mem_Ico`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Periodic.zsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddGroup α],   Function.Periodic f c → ∀ (n : ℤ), Function.Periodic
 f (n • c)

--- 原说明 ---
If a function `f` is `Periodic` with positive period `c`, then for all `x` there
 exists some
  `y ∈ Ico 0 c` such that `f x = f y`.
-/
theorem Periodic.exists_mem_Ico₀ [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x) : ∃ y ∈ Ico 0 c, f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_zsmul_near_of_pos' hc x
  ⟨x - n • c, H, (h.sub_zsmul_eq n).symm⟩

/-- If a function `f` is `Periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico a (a + c)` such that `f x = f y`. -/
/-
**Function.Periodic.exists_mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddCommGroup α
] [inst_1 : LinearOrder α]   [IsOrderedAddMonoid α] [Archimedean α],   Function.
Periodic f c → 0 < c → ∀ (x a : α), ∃ y ∈ Set.Ico a (a + c), f x = f y
参数：x a : α；a + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_add_zsmul_mem_Ico`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Periodic.zsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddGroup α],   Function.Periodic f c → ∀ (n : ℤ), Function.Periodic
 f (n • c)

--- 原说明 ---
If a function `f` is `Periodic` with positive period `c`, then for all `x` there
 exists some
  `y ∈ Ico a (a + c)` such that `f x = f y`.
-/
theorem Periodic.exists_mem_Ico [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x a) : ∃ y ∈ Ico a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ico hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

/-- If a function `f` is `Periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ioc a (a + c)` such that `f x = f y`. -/
/-
**Function.Periodic.exists_mem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddCommGroup α
] [inst_1 : LinearOrder α]   [IsOrderedAddMonoid α] [Archimedean α],   Function.
Periodic f c → 0 < c → ∀ (x a : α), ∃ y ∈ Set.Ioc a (a + c), f x = f y
参数：x a : α；a + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_add_zsmul_mem_Ioc`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Periodic.zsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddGroup α],   Function.Periodic f c → ∀ (n : ℤ), Function.Periodic
 f (n • c)

--- 原说明 ---
If a function `f` is `Periodic` with positive period `c`, then for all `x` there
 exists some
  `y ∈ Ioc a (a + c)` such that `f x = f y`.
-/
theorem Periodic.exists_mem_Ioc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x a) : ∃ y ∈ Ioc a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ioc hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩
/-
**Function.Periodic.image_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddCommGroup α
] [inst_1 : LinearOrder α]   [IsOrderedAddMonoid α] [Archimedean α],   Function.
Periodic f c → 0 < c → ∀ (a : α), f '' Set.Ioc a (a + c) = Set.range f
参数：a : α；a + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Function.Periodic.exists_mem_Ioc`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β} {c : α} [inst : AddCommGroup α] [inst_1 : LinearOrder α]   [IsOrderedAddMo
noid α] [Archimedean α…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Periodic.image_Ioc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (a : α) : f '' Ioc a (a + c) = range f :=
  (image_subset_range _ _).antisymm <| range_subset_iff.2 fun x =>
    let ⟨y, hy, hyx⟩ := h.exists_mem_Ioc hc x a
    ⟨y, hy, hyx.symm⟩
/-
**Function.Periodic.image_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddCommGroup α
] [inst_1 : LinearOrder α]   [IsOrderedAddMonoid α] [Archimedean α],   Function.
Periodic f c → 0 < c → ∀ (a : α), f '' Set.Icc a (a + c) = Set.range f
参数：a : α；a + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Function.Periodic.image_Ioc`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}
 {c : α} [inst : AddCommGroup α] [inst_1 : LinearOrder α]   [IsOrderedAddMonoid 
α] [Archimedean α…
-/
theorem Periodic.image_Icc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (a : α) : f '' Icc a (a + c) = range f :=
  (image_subset_range _ _).antisymm <| h.image_Ioc hc a ▸ image_mono Ioc_subset_Icc_self
/-
**Function.Periodic.image_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddCommGroup α
] [inst_1 : LinearOrder α]   [IsOrderedAddMonoid α] [Archimedean α],   Function.
Periodic f c → c ≠ 0 → ∀ (a : α), f '' Set.uIcc a (a + c) = Set.range f
参数：a : α；a + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
· 使用定理 `add_le_of_nonpos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, b ≤ 0 → a + b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Periodic.image_Icc`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}
 {c : α} [inst : AddCommGroup α] [inst_1 : LinearOrder α]   [IsOrderedAddMonoid 
α] [Archimedean α…
· 使用定理 `Function.Periodic.neg`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : 
α} [inst : AddGroup α],   Function.Periodic f c → Function.Periodic f (-c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
-/
theorem Periodic.image_uIcc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : c ≠ 0) (a : α) : f '' uIcc a (a + c) = range f := by
  cases hc.lt_or_gt with
  | inl hc =>
    rw [uIcc_of_ge (add_le_of_nonpos_right hc.le), ← h.neg.image_Icc (neg_pos.2 hc) (a + c),
      add_neg_cancel_right]
  | inr hc => rw [uIcc_of_le (le_add_of_nonneg_right hc.le), h.image_Icc hc]

/-! ### Antiperiodicity -/

/-
**Function.Antiperiodic.add_nat_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antip
eriodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : NonAssocSemi
ring α] [inst_1 : Ring β],   Function.Antiperiodic f c → ∀ (n : ℕ), f (x + ↑n * 
c) = (-1) ^ n * f x
参数：n : ℕ；x + ↑n * c；-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Function.Antiperiodic.add_nsmul_eq`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β} {c x : α} [inst : AddMonoid α] [inst_1 : SubtractionMonoid β],   Functio
n.Antiperiodic f c → ∀ (…

--- 原说明 ---
### Antiperiodicity
-/
theorem Antiperiodic.add_nat_mul_eq [NonAssocSemiring α] [Ring β] (h : Antiperiodic f c) (n : ℕ) :
    f (x + n * c) = (-1) ^ n * f x := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.add_nsmul_eq n
/-
**Function.Antiperiodic.sub_nat_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antip
eriodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : NonAssocRing
 α] [inst_1 : Ring β],   Function.Antiperiodic f c → ∀ (n : ℕ), f (x - ↑n * c) =
 (-1) ^ n * f x
参数：n : ℕ；x - ↑n * c；-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Function.Antiperiodic.sub_nsmul_eq`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β} {c x : α} [inst : AddGroup α] [inst_1 : SubtractionMonoid β],   Function
.Antiperiodic f c → ∀ (n…
-/
theorem Antiperiodic.sub_nat_mul_eq [NonAssocRing α] [Ring β] (h : Antiperiodic f c) (n : ℕ) :
    f (x - n * c) = (-1) ^ n * f x := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.sub_nsmul_eq n
/-
**Function.Antiperiodic.nat_mul_sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antip
eriodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : NonAssocRing
 α] [inst_1 : Ring β],   Function.Antiperiodic f c → ∀ (n : ℕ), f (↑n * c - x) =
 (-1) ^ n * f (-x)
参数：n : ℕ；↑n * c - x；-1；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Function.Antiperiodic.nsmul_sub_eq`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β} {c x : α} [inst : AddCommGroup α] [inst_1 : SubtractionMonoid β],   Func
tion.Antiperiodic f c → …
-/
theorem Antiperiodic.nat_mul_sub_eq [NonAssocRing α] [Ring β] (h : Antiperiodic f c) (n : ℕ) :
    f (n * c - x) = (-1) ^ n * f (-x) := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.nsmul_sub_eq n
/-
**Function.Antiperiodic.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperio
dic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {c : α} [inst :
 AddMonoid α] [inst_1 : Neg β]   [inst_2 : Group γ] [inst_3 : DistribMulAction γ
 α],   Function.Antiperiodic f c → ∀ (a : γ), Function.Antiperiodic (fun x => f 
(a • x)) (a⁻¹ • c)
参数：a : γ；fun x => f (a • x)；a⁻¹ • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
-/
theorem Antiperiodic.const_smul₀ [AddMonoid α] [Neg β] [GroupWithZero γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) {a : γ} (ha : a ≠ 0) : Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) :=
  fun x => by simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)
/-
**Function.Antiperiodic.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiod
ic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : DivisionSemiri
ng α] [inst_1 : Neg β],   Function.Antiperiodic f c → ∀ {a : α}, a ≠ 0 → Functio
n.Antiperiodic (fun x => f (a * x)) (a⁻¹ * c)
参数：fun x => f (a * x)；a⁻¹ * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Antiperiodic.const_smul₀`：∀ {α : Type u_1} {β : Type u_2} {γ : 
Type u_3} {f : α → β} {c : α} [inst : AddMonoid α] [inst_1 : Neg β]   [inst_2 : 
GroupWithZero γ] [inst_…
-/
theorem Antiperiodic.const_mul [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (a * x)) (a⁻¹ * c) :=
  h.const_smul₀ ha
/-
**Function.Antiperiodic.const_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antip
eriodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {c : α} [inst :
 AddMonoid α] [inst_1 : Neg β]   [inst_2 : Group γ] [inst_3 : DistribMulAction γ
 α],   Function.Antiperiodic f c → ∀ (a : γ), Function.Antiperiodic (fun x => f 
(a⁻¹ • x)) (a • c)
参数：a : γ；fun x => f (a⁻¹ • x)；a • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Function.Antiperiodic.const_smul`：∀ {α : Type u_1} {β : Type u_2} {γ : T
ype u_3} {f : α → β} {c : α} [inst : AddMonoid α] [inst_1 : Neg β]   [inst_2 : G
roup γ] [inst_3 : Dist…
-/
theorem Antiperiodic.const_inv_smul₀ [AddMonoid α] [Neg β] [GroupWithZero γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) {a : γ} (ha : a ≠ 0) : Antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul₀ (inv_ne_zero ha)
/-
**Function.Antiperiodic.const_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antipe
riodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : DivisionSemiri
ng α] [inst_1 : Neg β],   Function.Antiperiodic f c → ∀ {a : α}, a ≠ 0 → Functio
n.Antiperiodic (fun x => f (a⁻¹ * x)) (a * c)
参数：fun x => f (a⁻¹ * x)；a * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Antiperiodic.const_inv_smul₀`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} {f : α → β} {c : α} [inst : AddMonoid α] [inst_1 : Neg β]   [inst_
2 : GroupWithZero γ] [inst_…
-/
theorem Antiperiodic.const_inv_mul [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ ha
/-
**Function.Antiperiodic.mul_const** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiod
ic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : DivisionSemiri
ng α] [inst_1 : Neg β],   Function.Antiperiodic f c → ∀ {a : α}, a ≠ 0 → Functio
n.Antiperiodic (fun x => f (x * a)) (c * a⁻¹)
参数：fun x => f (x * a)；c * a⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Antiperiodic.const_smul₀`：∀ {α : Type u_1} {β : Type u_2} {γ : 
Type u_3} {f : α → β} {c : α} [inst : AddMonoid α] [inst_1 : Neg β]   [inst_2 : 
GroupWithZero γ] [inst_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulOpposite.op_ne_zero_iff`：op_ne_zero_iff [Zero α] (a : α) : op a != (0
 : αᵐᵒᵖ) ↔ a != (0 : α)
-/
theorem Antiperiodic.mul_const [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x * a)) (c * a⁻¹) :=
  h.const_smul₀ <| (MulOpposite.op_ne_zero_iff a).mpr ha
/-
**Function.Antiperiodic.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperio
dic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : DivisionSemiri
ng α] [inst_1 : Neg β],   Function.Antiperiodic f c → ∀ {a : α}, a ≠ 0 → Functio
n.Antiperiodic (fun x => f (x * a)) (c / a)
参数：fun x => f (x * a)；c / a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Function.Antiperiodic.mul_const`：∀ {α : Type u_1} {β : Type u_2} {f : α 
→ β} {c : α} [inst : DivisionSemiring α] [inst_1 : Neg β],   Function.Antiperiod
ic f c → ∀ {a : α}, a…
-/
theorem Antiperiodic.mul_const' [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x * a)) (c / a) := by
  simpa only [div_eq_mul_inv] using h.mul_const ha
/-
**Function.Antiperiodic.mul_const_inv** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antipe
riodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : DivisionSemiri
ng α] [inst_1 : Neg β],   Function.Antiperiodic f c → ∀ {a : α}, a ≠ 0 → Functio
n.Antiperiodic (fun x => f (x * a⁻¹)) (c * a)
参数：fun x => f (x * a⁻¹)；c * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Antiperiodic.const_inv_smul₀`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} {f : α → β} {c : α} [inst : AddMonoid α] [inst_1 : Neg β]   [inst_
2 : GroupWithZero γ] [inst_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulOpposite.op_ne_zero_iff`：op_ne_zero_iff [Zero α] (a : α) : op a != (0
 : αᵐᵒᵖ) ↔ a != (0 : α)
-/
theorem Antiperiodic.mul_const_inv [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x * a⁻¹)) (c * a) :=
  h.const_inv_smul₀ <| (MulOpposite.op_ne_zero_iff a).mpr ha
/-
**Function.Antiperiodic.div_inv** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiodic
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : DivisionSemiri
ng α] [inst_1 : Neg β],   Function.Antiperiodic f c → ∀ {a : α}, a ≠ 0 → Functio
n.Antiperiodic (fun x => f (x / a)) (c * a)
参数：fun x => f (x / a)；c * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Function.Antiperiodic.mul_const_inv`：∀ {α : Type u_1} {β : Type u_2} {f 
: α → β} {c : α} [inst : DivisionSemiring α] [inst_1 : Neg β],   Function.Antipe
riodic f c → ∀ {a : α}, a…
-/
theorem Antiperiodic.div_inv [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x / a)) (c * a) := by
  simpa only [div_eq_mul_inv] using h.mul_const_inv ha

end Function

/-
**Int.fract_periodic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.fract_periodic (α) [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [F
loorRing α] : Function.Periodic Int.fract (1 : α)
参数：α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.fract_add_intCast`：fract_add_intCast (a : R) (m : Int) : fract (a + 
m) = fract a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem Int.fract_periodic (α) [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α] :
    Function.Periodic Int.fract (1 : α) := fun a => mod_cast Int.fract_add_intCast a 1
