/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.GroupTheory.Complement

/-!
# Semidirect product

This file defines semidirect products of groups, and the canonical maps in and out of the
semidirect product. The semidirect product of `N` and `G` given a hom `φ` from
`G` to the automorphism group of `N` is the product of sets with the group
`⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩`

## Key definitions

There are two homs into the semidirect product `inl : N →* N ⋊[φ] G` and
`inr : G →* N ⋊[φ] G`, and `lift` can be used to define maps `N ⋊[φ] G →* H`
out of the semidirect product given maps `fn : N →* H` and `fg : G →* H` that satisfy the
condition `∀ n g, fn (φ g n) = fg g * fn n * fg g⁻¹`

## Notation

This file introduces the global notation `N ⋊[φ] G` for `SemidirectProduct N G φ`

## Tags
group, semidirect product
-/

@[expose] public section

open Subgroup

variable (N : Type*) (G : Type*) {H : Type*} [Group N] [Group G] [Group H]

-- Don't generate sizeOf and injectivity lemmas, which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The semidirect product of groups `N` and `G`, given a map `φ` from `G` to the automorphism
  group of `N`. It is the product of sets with the group operation
  `⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩` -/
@[ext]
/-
**SemidirectProduct** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(N : Type u_1) → (G : Type u_2) → [inst : Group N] → [inst_1 : Group G] → 
(G →* MulAut N) → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The semidirect product of groups `N` and `G`, given a map `φ` from `G` to the au
tomorphism
  group of `N`. It is the product of sets with the group operation
  `⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩`
-/
structure SemidirectProduct (φ : G →* MulAut N) where
  /-- The element of N -/
  left : N
  /-- The element of G -/
  right : G
  deriving DecidableEq

attribute [pp_using_anonymous_constructor] SemidirectProduct

@[inherit_doc]
notation:35 N " ⋊[" φ:35 "] " G:35 => SemidirectProduct N G φ

namespace SemidirectProduct

variable {N G}
variable {φ : G →* MulAut N}

/-
**SemidirectProduct.** 是 Mathlib 中的一个实例，位于命名空间 `SemidirectProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (SemidirectProduct N G φ) where
  mul a b := ⟨a.1 * φ a.2 b.1, a.2 * b.2⟩
/-
**SemidirectProduct.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `SemidirectProduct`。
形式化陈述：mul_def (a b : SemidirectProduct N G φ) : a * b = ⟨a.1 * φ a.2 b.1, a.2 * 
b.2⟩
参数：a b : SemidirectProduct N G φ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_def (a b : SemidirectProduct N G φ) : a * b = ⟨a.1 * φ a.2 b.1, a.2 * b.2⟩ := rfl

@[simp]
/-
**SemidirectProduct.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：mul_left (a b : N ⋊[φ] G) : (a * b).left = a.left * φ a.right b.left
参数：a b : N ⋊[φ] G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_left (a b : N ⋊[φ] G) : (a * b).left = a.left * φ a.right b.left := rfl

@[simp]
/-
**SemidirectProduct.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：mul_right (a b : N ⋊[φ] G) : (a * b).right = a.right * b.right
参数：a b : N ⋊[φ] G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_right (a b : N ⋊[φ] G) : (a * b).right = a.right * b.right := rfl
/-
**SemidirectProduct.** 是 Mathlib 中的一个实例，位于命名空间 `SemidirectProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (SemidirectProduct N G φ) where one := ⟨1, 1⟩

@[simp]
/-
**SemidirectProduct.one_left** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：one_left : (1 : N ⋊[φ] G).left = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_left : (1 : N ⋊[φ] G).left = 1 := rfl

@[simp]
/-
**SemidirectProduct.one_right** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：one_right : (1 : N ⋊[φ] G).right = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_right : (1 : N ⋊[φ] G).right = 1 := rfl
/-
**SemidirectProduct.** 是 Mathlib 中的一个实例，位于命名空间 `SemidirectProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (SemidirectProduct N G φ) where
  inv x := ⟨φ x.2⁻¹ x.1⁻¹, x.2⁻¹⟩

@[simp]
/-
**SemidirectProduct.inv_left** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：inv_left (a : N ⋊[φ] G) : a⁻¹.left = φ a.right⁻¹ a.left⁻¹
参数：a : N ⋊[φ] G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_left (a : N ⋊[φ] G) : a⁻¹.left = φ a.right⁻¹ a.left⁻¹ := rfl

@[simp]
/-
**SemidirectProduct.inv_right** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：inv_right (a : N ⋊[φ] G) : a⁻¹.right = a.right⁻¹
参数：a : N ⋊[φ] G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_right (a : N ⋊[φ] G) : a⁻¹.right = a.right⁻¹ := rfl
/-
**SemidirectProduct.** 是 Mathlib 中的一个实例，位于命名空间 `SemidirectProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (N ⋊[φ] G) where
  mul_assoc a b c := SemidirectProduct.ext (by simp [mul_assoc]) (by simp [mul_assoc])
  one_mul a := SemidirectProduct.ext (by simp) (one_mul a.2)
  mul_one a := SemidirectProduct.ext (by simp) (mul_one _)
  inv_mul_cancel a := SemidirectProduct.ext (by simp) (by simp)
/-
**SemidirectProduct.** 是 Mathlib 中的一个实例，位于命名空间 `SemidirectProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (N ⋊[φ] G) := ⟨1⟩

/-- The canonical map `N →* N ⋊[φ] G` sending `n` to `⟨n, 1⟩` -/
/-
**SemidirectProduct.inl** 是 Mathlib 中的一个定义，位于命名空间 `SemidirectProduct`。
形式化陈述：inl : N ->* N ⋊[φ] G where toFun n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `N →* N ⋊[φ] G` sending `n` to `⟨n, 1⟩`
-/
def inl : N →* N ⋊[φ] G where
  toFun n := ⟨n, 1⟩
  map_one' := rfl
  map_mul' := by intros; ext <;>
    simp only [mul_left, map_one, MulAut.one_apply, mul_right, mul_one]

@[simp]
/-
**SemidirectProduct.left_inl** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：left_inl (n : N) : (inl n : N ⋊[φ] G).left = n
参数：n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem left_inl (n : N) : (inl n : N ⋊[φ] G).left = n := rfl

@[simp]
/-
**SemidirectProduct.right_inl** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：right_inl (n : N) : (inl n : N ⋊[φ] G).right = 1
参数：n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem right_inl (n : N) : (inl n : N ⋊[φ] G).right = 1 := rfl
/-
**SemidirectProduct.inl_injective** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：inl_injective : Function.Injective (inl : N -> N ⋊[φ] G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.injective_iff_hasLeftInverse`：injective_iff_hasLeftInverse : In
jective f ↔ HasLeftInverse f
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `SemidirectProduct.left_inl`：left_inl (n : N) : (inl n : N ⋊[φ] G).left =
 n
-/
theorem inl_injective : Function.Injective (inl : N → N ⋊[φ] G) :=
  Function.injective_iff_hasLeftInverse.2 ⟨left, left_inl⟩

@[simp]
/-
**SemidirectProduct.inl_inj** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：inl_inj {n₁ n₂ : N} : (inl n₁ : N ⋊[φ] G) = inl n₂ ↔ n₁ = n₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SemidirectProduct.inl_injective`：inl_injective : Function.Injective (inl
 : N -> N ⋊[φ] G)
-/
theorem inl_inj {n₁ n₂ : N} : (inl n₁ : N ⋊[φ] G) = inl n₂ ↔ n₁ = n₂ :=
  inl_injective.eq_iff

/-- The canonical map `G →* N ⋊[φ] G` sending `g` to `⟨1, g⟩` -/
/-
**SemidirectProduct.inr** 是 Mathlib 中的一个定义，位于命名空间 `SemidirectProduct`。
形式化陈述：inr : G ->* N ⋊[φ] G where toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `G →* N ⋊[φ] G` sending `g` to `⟨1, g⟩`
-/
def inr : G →* N ⋊[φ] G where
  toFun g := ⟨1, g⟩
  map_one' := rfl
  map_mul' := by intros; ext <;> simp

@[simp]
/-
**SemidirectProduct.left_inr** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：left_inr (g : G) : (inr g : N ⋊[φ] G).left = 1
参数：g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem left_inr (g : G) : (inr g : N ⋊[φ] G).left = 1 := rfl

@[simp]
/-
**SemidirectProduct.right_inr** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：right_inr (g : G) : (inr g : N ⋊[φ] G).right = g
参数：g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem right_inr (g : G) : (inr g : N ⋊[φ] G).right = g := rfl
/-
**SemidirectProduct.inr_injective** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：inr_injective : Function.Injective (inr : G -> N ⋊[φ] G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.injective_iff_hasLeftInverse`：injective_iff_hasLeftInverse : In
jective f ↔ HasLeftInverse f
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `SemidirectProduct.right_inr`：right_inr (g : G) : (inr g : N ⋊[φ] G).righ
t = g
-/
theorem inr_injective : Function.Injective (inr : G → N ⋊[φ] G) :=
  Function.injective_iff_hasLeftInverse.2 ⟨right, right_inr⟩

@[simp]
/-
**SemidirectProduct.inr_inj** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：inr_inj {g₁ g₂ : G} : (inr g₁ : N ⋊[φ] G) = inr g₂ ↔ g₁ = g₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SemidirectProduct.inr_injective`：inr_injective : Function.Injective (inr
 : G -> N ⋊[φ] G)
-/
theorem inr_inj {g₁ g₂ : G} : (inr g₁ : N ⋊[φ] G) = inr g₂ ↔ g₁ = g₂ :=
  inr_injective.eq_iff
/-
**SemidirectProduct.inl_aut** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：inl_aut (g : G) (n : N) : (inl (φ g n) : N ⋊[φ] G) = inr g * inl n * inr g
⁻¹
参数：g : G；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemidirectProduct.ext`：∀ {N : Type u_1} {G : Type u_2} {inst : Group N} 
{inst_1 : Group G} {φ : G →* MulAut N} {x y : N ⋊[φ] G},   x.left = y.left → x.r
ight = y.ri…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `MulAut.inv_apply`：∀ (M : Type u_2) [inst : Mul M] (e : MulAut M) (m : M)
, e⁻¹ m = (MulEquiv.symm e) m
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
-/
theorem inl_aut (g : G) (n : N) : (inl (φ g n) : N ⋊[φ] G) = inr g * inl n * inr g⁻¹ := by
  ext <;> simp
/-
**SemidirectProduct.inl_aut_inv** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：inl_aut_inv (g : G) (n : N) : (inl ((φ g)⁻¹ n) : N ⋊[φ] G) = inr g⁻¹ * inl
 n * inr g
参数：g : G；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `SemidirectProduct.inl_aut`：inl_aut (g : G) (n : N) : (inl (φ g n) : N ⋊[
φ] G) = inr g * inl n * inr g⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem inl_aut_inv (g : G) (n : N) : (inl ((φ g)⁻¹ n) : N ⋊[φ] G) = inr g⁻¹ * inl n * inr g := by
  rw [← map_inv, inl_aut, inv_inv]

@[simp]
/-
**SemidirectProduct.mk_eq_inl_mul_inr** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProdu
ct`。
形式化陈述：mk_eq_inl_mul_inr (g : G) (n : N) : (⟨n, g⟩ : N ⋊[φ] G) = inl n * inr g
参数：g : G；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemidirectProduct.ext`：∀ {N : Type u_1} {G : Type u_2} {inst : Group N} 
{inst_1 : Group G} {φ : G →* MulAut N} {x y : N ⋊[φ] G},   x.left = y.left → x.r
ight = y.ri…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mk_eq_inl_mul_inr (g : G) (n : N) : (⟨n, g⟩ : N ⋊[φ] G) = inl n * inr g := by ext <;> simp

@[simp]
/-
**SemidirectProduct.inl_left_mul_inr_right** 是 Mathlib 中的一个定理，位于命名空间 `Semidirect
Product`。
形式化陈述：inl_left_mul_inr_right (x : N ⋊[φ] G) : inl x.left * inr x.right = x
参数：x : N ⋊[φ] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemidirectProduct.ext`：∀ {N : Type u_1} {G : Type u_2} {inst : Group N} 
{inst_1 : Group G} {φ : G →* MulAut N} {x y : N ⋊[φ] G},   x.left = y.left → x.r
ight = y.ri…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem inl_left_mul_inr_right (x : N ⋊[φ] G) : inl x.left * inr x.right = x := by ext <;> simp

/-- The canonical projection map `N ⋊[φ] G →* G`, as a group hom. -/
/-
**SemidirectProduct.rightHom** 是 Mathlib 中的一个定义，位于命名空间 `SemidirectProduct`。
形式化陈述：rightHom : N ⋊[φ] G ->* G where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection map `N ⋊[φ] G →* G`, as a group hom.
-/
def rightHom : N ⋊[φ] G →* G where
  toFun := SemidirectProduct.right
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
/-
**SemidirectProduct.rightHom_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProdu
ct`。
形式化陈述：rightHom_eq_right : (rightHom : N ⋊[φ] G -> G) = right
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightHom_eq_right : (rightHom : N ⋊[φ] G → G) = right := rfl

@[simp]
/-
**SemidirectProduct.rightHom_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProdu
ct`。
形式化陈述：rightHom_comp_inl : (rightHom : N ⋊[φ] G ->* G).comp inl = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightHom_comp_inl : (rightHom : N ⋊[φ] G →* G).comp inl = 1 := by ext; simp [rightHom]

@[simp]
/-
**SemidirectProduct.rightHom_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProdu
ct`。
形式化陈述：rightHom_comp_inr : (rightHom : N ⋊[φ] G ->* G).comp inr = MonoidHom.id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightHom_comp_inr : (rightHom : N ⋊[φ] G →* G).comp inr = MonoidHom.id _ := by
  ext; simp [rightHom]

@[simp]
/-
**SemidirectProduct.rightHom_inl** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：rightHom_inl (n : N) : rightHom (inl n : N ⋊[φ] G) = 1
参数：n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightHom_inl (n : N) : rightHom (inl n : N ⋊[φ] G) = 1 := by simp [rightHom]

@[simp]
/-
**SemidirectProduct.rightHom_inr** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：rightHom_inr (g : G) : rightHom (inr g : N ⋊[φ] G) = g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightHom_inr (g : G) : rightHom (inr g : N ⋊[φ] G) = g := by simp [rightHom]
/-
**SemidirectProduct.rightHom_surjective** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectPro
duct`。
形式化陈述：rightHom_surjective : Function.Surjective (rightHom : N ⋊[φ] G -> G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.surjective_iff_hasRightInverse`：surjective_iff_hasRightInverse 
: Surjective f ↔ HasRightInverse f
· 使用定理 `SemidirectProduct.rightHom_inr`：rightHom_inr (g : G) : rightHom (inr g :
 N ⋊[φ] G) = g
-/
theorem rightHom_surjective : Function.Surjective (rightHom : N ⋊[φ] G → G) :=
  Function.surjective_iff_hasRightInverse.2 ⟨inr, rightHom_inr⟩
/-
**SemidirectProduct.range_inl_eq_ker_rightHom** 是 Mathlib 中的一个定理，位于命名空间 `Semidir
ectProduct`。
形式化陈述：range_inl_eq_ker_rightHom : (inl : N ->* N ⋊[φ] G).range = rightHom.ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `SemidirectProduct.ext`：∀ {N : Type u_1} {G : Type u_2} {inst : Group N} 
{inst_1 : Group G} {φ : G →* MulAut N} {x y : N ⋊[φ] G},   x.left = y.left → x.r
ight = y.ri…
-/
theorem range_inl_eq_ker_rightHom : (inl : N →* N ⋊[φ] G).range = rightHom.ker :=
  le_antisymm (fun _ ↦ by simp +contextual [MonoidHom.mem_ker, eq_comm])
    fun x hx ↦ ⟨x.left, by ext <;> simp_all [MonoidHom.mem_ker]⟩

/-- The bijection between the semidirect product and the product. -/
@[simps]
/-
**SemidirectProduct.equivProd** 是 Mathlib 中的一个定义，位于命名空间 `SemidirectProduct`。
形式化陈述：equivProd : N ⋊[φ] G ≃ N × G where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection between the semidirect product and the product.
-/
def equivProd : N ⋊[φ] G ≃ N × G where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩

/-- The group isomorphism between a semidirect product with respect to the trivial map
  and the product. -/
@[simps (rhsMd := .default)]
/-
**SemidirectProduct.mulEquivProd** 是 Mathlib 中的一个定义，位于命名空间 `SemidirectProduct`。
形式化陈述：mulEquivProd : N ⋊[1] G ≃* N × G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group isomorphism between a semidirect product with respect to the trivial m
ap
  and the product.
-/
def mulEquivProd : N ⋊[1] G ≃* N × G :=
  { equivProd with map_mul' _ _ := rfl }

section lift

variable (fn : N →* H) (fg : G →* H)
  (h : ∀ g, fn.comp (φ g).toMonoidHom = (MulAut.conj (fg g)).toMonoidHom.comp fn)

/-- Define a group hom `N ⋊[φ] G →* H`, by defining maps `N →* H` and `G →* H` -/
/-
**SemidirectProduct.lift** 是 Mathlib 中的一个定义，位于命名空间 `SemidirectProduct`。
形式化陈述：lift : N ⋊[φ] G ->* H where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a group hom `N ⋊[φ] G →* H`, by defining maps `N →* H` and `G →* H`
-/
def lift : N ⋊[φ] G →* H where
  toFun a := fn a.1 * fg a.2
  map_one' := by simp
  map_mul' a b := by
    have := fun n g ↦ DFunLike.ext_iff.1 (h n) g
    simp only [MulAut.conj_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    simp only [mul_left, mul_right, map_mul, this, mul_assoc, inv_mul_cancel_left]

@[simp]
/-
**SemidirectProduct.lift_inl** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：lift_inl (n : N) : lift fn fg h (inl n) = fn n
参数：n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_inl (n : N) : lift fn fg h (inl n) = fn n := by simp [lift]

@[simp]
/-
**SemidirectProduct.lift_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：lift_comp_inl : (lift fn fg h).comp inl = fn
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemidirectProduct.lift_inl`：lift_inl (n : N) : lift fn fg h (inl n) = fn
 n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_comp_inl : (lift fn fg h).comp inl = fn := by ext; simp

@[simp]
/-
**SemidirectProduct.lift_inr** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：lift_inr (g : G) : lift fn fg h (inr g) = fg g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_inr (g : G) : lift fn fg h (inr g) = fg g := by simp [lift]

@[simp]
/-
**SemidirectProduct.lift_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：lift_comp_inr : (lift fn fg h).comp inr = fg
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemidirectProduct.lift_inr`：lift_inr (g : G) : lift fn fg h (inr g) = fg
 g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_comp_inr : (lift fn fg h).comp inr = fg := by ext; simp
/-
**SemidirectProduct.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：lift_unique (F : N ⋊[φ] G ->* H) : F = lift (F.comp inl) (F.comp inr) fun 
_ => by ext; simp [inl_aut]
参数：F : N ⋊[φ] G ->* H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `SemidirectProduct.inl_left_mul_inr_right`：inl_left_mul_inr_right (x : N 
⋊[φ] G) : inl x.left * inr x.right = x
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem lift_unique (F : N ⋊[φ] G →* H) :
    F = lift (F.comp inl) (F.comp inr) fun _ ↦ by ext; simp [inl_aut] := by
  rw [DFunLike.ext_iff]
  simp only [lift, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, ← map_mul,
    inl_left_mul_inr_right, forall_const]

/-- Two maps out of the semidirect product are equal if they're equal after composition
  with both `inl` and `inr` -/
/-
**SemidirectProduct.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：hom_ext {f g : N ⋊[φ] G ->* H} (hl : f.comp inl = g.comp inl) (hr : f.comp
 inr = g.comp inr) : f = g
参数：hl : f.comp inl = g.comp inl；hr : f.comp inr = g.comp inr。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemidirectProduct.lift_unique`：lift_unique (F : N ⋊[φ] G ->* H) : F = li
ft (F.comp inl) (F.comp inr) fun _ => by ext; simp [inl_aut]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemidirectProduct.lift.congr_simp`：∀ {N : Type u_1} {G : Type u_2} {H : 
Type u_3} [inst : Group N] [inst_1 : Group G] [inst_2 : Group H]   {φ : G →* Mul
Aut N} (fn fn_1 : N →* …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two maps out of the semidirect product are equal if they're equal after composit
ion
  with both `inl` and `inr`
-/
theorem hom_ext {f g : N ⋊[φ] G →* H} (hl : f.comp inl = g.comp inl)
    (hr : f.comp inr = g.comp inr) : f = g := by
  rw [lift_unique f, lift_unique g]
  simp only [*]

/-- The homomorphism from a semidirect product of subgroups to the ambient group. -/
@[simps!]
/-
**SemidirectProduct.monoidHomSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `SemidirectProdu
ct`。
形式化陈述：monoidHomSubgroup {H K : Subgroup G} (h : K <= normalizer H) : H ⋊[(H.norm
alizerMonoidHom).comp (inclusion h)] K ->* G
参数：h : K <= normalizer H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homomorphism from a semidirect product of subgroups to the ambient group.
-/
def monoidHomSubgroup {H K : Subgroup G} (h : K ≤ normalizer H) :
    H ⋊[(H.normalizerMonoidHom).comp (inclusion h)] K →* G :=
  lift H.subtype K.subtype (by simp [DFunLike.ext_iff])

/-- The isomorphism from a semidirect product of complementary subgroups to the ambient group. -/
@[simps!]
/-
**SemidirectProduct.mulEquivSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `SemidirectProduc
t`。
形式化陈述：mulEquivSubgroup {H K : Subgroup G} [H.Normal] (h : H.IsComplement' K) : H
 ⋊[(H.normalizerMonoidHom).comp (inclusion (H.normalizer_eq_top ▸ le_top))] K ≃*
 G
参数：h : H.IsComplement' K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism from a semidirect product of complementary subgroups to the ambi
ent group.
-/
noncomputable def mulEquivSubgroup {H K : Subgroup G} [H.Normal] (h : H.IsComplement' K) :
    H ⋊[(H.normalizerMonoidHom).comp (inclusion (H.normalizer_eq_top ▸ le_top))] K ≃* G :=
  MulEquiv.ofBijective (monoidHomSubgroup _) ((equivProd.bijective_comp _).mpr h)

end lift

section Map

variable {N₁ G₁ N₂ G₂ : Type*} [Group N₁] [Group G₁] [Group N₂] [Group G₂]
  {φ₁ : G₁ →* MulAut N₁} {φ₂ : G₂ →* MulAut N₂}
  (fn : N₁ →* N₂) (fg : G₁ →* G₂)
  (h : ∀ g : G₁, fn.comp (φ₁ g).toMonoidHom = (φ₂ (fg g)).toMonoidHom.comp fn)

/-- Define a map from `N₁ ⋊[φ₁] G₁` to `N₂ ⋊[φ₂] G₂` given maps `N₁ →* N₂` and `G₁ →* G₂` that
  satisfy a commutativity condition `∀ n g, fn (φ₁ g n) = φ₂ (fg g) (fn n)`. -/
/-
**SemidirectProduct.map** 是 Mathlib 中的一个定义，位于命名空间 `SemidirectProduct`。
形式化陈述：map : N₁ ⋊[φ₁] G₁ ->* N₂ ⋊[φ₂] G₂ where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a map from `N₁ ⋊[φ₁] G₁` to `N₂ ⋊[φ₂] G₂` given maps `N₁ →* N₂` and `G₁ →
* G₂` that
  satisfy a commutativity condition `∀ n g, fn (φ₁ g n) = φ₂ (fg g) (fn n)`.
-/
def map : N₁ ⋊[φ₁] G₁ →* N₂ ⋊[φ₂] G₂ where
  toFun x := ⟨fn x.1, fg x.2⟩
  map_one' := by simp
  map_mul' x y := by
    replace h := DFunLike.ext_iff.1 (h x.right) y.left
    ext <;> simp_all

@[simp]
/-
**SemidirectProduct.map_left** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：map_left (g : N₁ ⋊[φ₁] G₁) : (map fn fg h g).left = fn g.left
参数：g : N₁ ⋊[φ₁] G₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_left (g : N₁ ⋊[φ₁] G₁) : (map fn fg h g).left = fn g.left := rfl

@[simp]
/-
**SemidirectProduct.map_right** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：map_right (g : N₁ ⋊[φ₁] G₁) : (map fn fg h g).right = fg g.right
参数：g : N₁ ⋊[φ₁] G₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_right (g : N₁ ⋊[φ₁] G₁) : (map fn fg h g).right = fg g.right := rfl

@[simp]
/-
**SemidirectProduct.rightHom_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProdu
ct`。
形式化陈述：rightHom_comp_map : rightHom.comp (map fn fg h) = fg.comp rightHom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightHom_comp_map : rightHom.comp (map fn fg h) = fg.comp rightHom := rfl

@[simp]
/-
**SemidirectProduct.map_inl** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：map_inl (n : N₁) : map fn fg h (inl n) = inl (fn n)
参数：n : N₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SemidirectProduct.mk_eq_inl_mul_inr`：mk_eq_inl_mul_inr (g : G) (n : N) :
 (⟨n, g⟩ : N ⋊[φ] G) = inl n * inr g
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_inl (n : N₁) : map fn fg h (inl n) = inl (fn n) := by simp [map]

@[simp]
/-
**SemidirectProduct.map_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：map_comp_inl : (map fn fg h).comp inl = inl.comp fn
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `SemidirectProduct.ext`：∀ {N : Type u_1} {G : Type u_2} {inst : Group N} 
{inst_1 : Group G} {φ : G →* MulAut N} {x y : N ⋊[φ] G},   x.left = y.left → x.r
ight = y.ri…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemidirectProduct.map_inl`：map_inl (n : N₁) : map fn fg h (inl n) = inl 
(fn n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp_inl : (map fn fg h).comp inl = inl.comp fn := by ext <;> simp

@[simp]
/-
**SemidirectProduct.map_inr** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：map_inr (g : G₁) : map fn fg h (inr g) = inr (fg g)
参数：g : G₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SemidirectProduct.mk_eq_inl_mul_inr`：mk_eq_inl_mul_inr (g : G) (n : N) :
 (⟨n, g⟩ : N ⋊[φ] G) = inl n * inr g
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_inr (g : G₁) : map fn fg h (inr g) = inr (fg g) := by simp [map]

@[simp]
/-
**SemidirectProduct.map_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct`。
形式化陈述：map_comp_inr : (map fn fg h).comp inr = inr.comp fg
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `SemidirectProduct.ext`：∀ {N : Type u_1} {G : Type u_2} {inst : Group N} 
{inst_1 : Group G} {φ : G →* MulAut N} {x y : N ⋊[φ] G},   x.left = y.left → x.r
ight = y.ri…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SemidirectProduct.mk_eq_inl_mul_inr`：mk_eq_inl_mul_inr (g : G) (n : N) :
 (⟨n, g⟩ : N ⋊[φ] G) = inl n * inr g
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp_inr : (map fn fg h).comp inr = inr.comp fg := by ext <;> simp [map]

end Map

section Congr

variable {N₁ G₁ N₂ G₂ : Type*} [Group N₁] [Group G₁] [Group N₂] [Group G₂]
  {φ₁ : G₁ →* MulAut N₁} {φ₂ : G₂ →* MulAut N₂}
  (fn : N₁ ≃* N₂) (fg : G₁ ≃* G₂)
  (h : ∀ g : G₁, (φ₁ g).trans fn = fn.trans (φ₂ (fg g)))

/-- Define an isomorphism from `N₁ ⋊[φ₁] G₁` to `N₂ ⋊[φ₂] G₂` given isomorphisms `N₁ ≃* N₂` and
  `G₁ ≃* G₂` that satisfy a commutativity condition `∀ n g, fn (φ₁ g n) = φ₂ (fg g) (fn n)`. -/
@[simps]
/-
**SemidirectProduct.congr** 是 Mathlib 中的一个定义，位于命名空间 `SemidirectProduct`。
形式化陈述：congr : N₁ ⋊[φ₁] G₁ ≃* N₂ ⋊[φ₂] G₂ where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define an isomorphism from `N₁ ⋊[φ₁] G₁` to `N₂ ⋊[φ₂] G₂` given isomorphisms `N₁
 ≃* N₂` and
  `G₁ ≃* G₂` that satisfy a commutativity condition `∀ n g, fn (φ₁ g n) = φ₂ (fg
 g) (fn n)`.
-/
def congr : N₁ ⋊[φ₁] G₁ ≃* N₂ ⋊[φ₂] G₂ where
  toFun x := ⟨fn x.1, fg x.2⟩
  invFun x := ⟨fn.symm x.1, fg.symm x.2⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' x y := by
    replace h := DFunLike.ext_iff.1 (h x.right) y.left
    ext <;> simp_all

/-- Define an isomorphism from `N₁ ⋊[φ₁] G₁` to `N₂ ⋊[φ₂] G₂` without specifying `φ₂`. -/
@[simps!]
/-
**SemidirectProduct.congr'** 是 Mathlib 中的一个定义，位于命名空间 `SemidirectProduct`。
形式化陈述：congr' : N₁ ⋊[φ₁] G₁ ≃* N₂ ⋊[MonoidHom.comp (MulAut.congr fn) (φ₁.comp fg.
symm)] G₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define an isomorphism from `N₁ ⋊[φ₁] G₁` to `N₂ ⋊[φ₂] G₂` without specifying `φ₂
`.
-/
def congr' :
    N₁ ⋊[φ₁] G₁ ≃* N₂ ⋊[MonoidHom.comp (MulAut.congr fn) (φ₁.comp fg.symm)] G₂ :=
  congr fn fg (fun _ ↦ by ext; simp)

end Congr

@[simp]
/-
**SemidirectProduct.card** 是 Mathlib 中的一个引理，位于命名空间 `SemidirectProduct`。
形式化陈述：card : Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
-/
lemma card : Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G :=
  Nat.card_prod _ _ ▸ Nat.card_congr equivProd

end SemidirectProduct

