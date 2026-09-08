/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Map
public import Mathlib.Order.Filter.AtTopBot.Monoid

/-!
# Convergence to ±infinity in ordered commutative groups
-/

public section

variable {α G : Type*}
open Set

namespace Filter

section OrderedCommGroup

variable [CommGroup G] [PartialOrder G] [IsOrderedMonoid G] (l : Filter α) {f g : α → G}

@[to_additive]
/-
**Filter.tendsto_atTop_mul_left_of_le'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_mul_left_of_le' (C : G) (hf : forallᶠ x in l, C <= f x) (hg 
: Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atTop
参数：C : G；hf : forallᶠ x in l, C <= f x；hg : Tendsto g l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_of_isBoundedUnder_le_mul`：∀ {α : Type u_1} {M : Typ
e u_2} [inst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelMonoid M] {l 
: Filter α}   {f g : α → M},   Filt…
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
theorem tendsto_atTop_mul_left_of_le' (C : G) (hf : ∀ᶠ x in l, C ≤ f x) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
  .atTop_of_isBoundedUnder_le_mul (f := f⁻¹) ⟨C⁻¹, by simpa⟩ (by simpa)

@[to_additive]
/-
**Filter.tendsto_atBot_mul_left_of_ge'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atBot_mul_left_of_ge' (C : G) (hf : forallᶠ x in l, f x <= C) (hg 
: Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atBot
参数：C : G；hf : forallᶠ x in l, f x <= C；hg : Tendsto g l atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mul_left_of_le'`：tendsto_atTop_mul_left_of_le' (C :
 G) (hf : forallᶠ x in l, C <= f x) (hg : Tendsto g l atTop) : Tendsto (fun x =>
 f x * g x) l atTop
-/
theorem tendsto_atBot_mul_left_of_ge' (C : G) (hf : ∀ᶠ x in l, f x ≤ C) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  tendsto_atTop_mul_left_of_le' (G := Gᵒᵈ) _ C hf hg

@[to_additive]
/-
**Filter.tendsto_atTop_mul_left_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_mul_left_of_le (C : G) (hf : forall x, C <= f x) (hg : Tends
to g l atTop) : Tendsto (fun x => f x * g x) l atTop
参数：C : G；hf : forall x, C <= f x；hg : Tendsto g l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mul_left_of_le'`：tendsto_atTop_mul_left_of_le' (C :
 G) (hf : forallᶠ x in l, C <= f x) (hg : Tendsto g l atTop) : Tendsto (fun x =>
 f x * g x) l atTop
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem tendsto_atTop_mul_left_of_le (C : G) (hf : ∀ x, C ≤ f x) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
  tendsto_atTop_mul_left_of_le' l C (univ_mem' hf) hg

@[to_additive]
/-
**Filter.tendsto_atBot_mul_left_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atBot_mul_left_of_ge (C : G) (hf : forall x, f x <= C) (hg : Tends
to g l atBot) : Tendsto (fun x => f x * g x) l atBot
参数：C : G；hf : forall x, f x <= C；hg : Tendsto g l atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mul_left_of_le`：tendsto_atTop_mul_left_of_le (C : G
) (hf : forall x, C <= f x) (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g
 x) l atTop
-/
theorem tendsto_atBot_mul_left_of_ge (C : G) (hf : ∀ x, f x ≤ C) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  tendsto_atTop_mul_left_of_le (G := Gᵒᵈ) _ C hf hg

@[to_additive]
/-
**Filter.tendsto_atTop_mul_right_of_le'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_mul_right_of_le' (C : G) (hf : Tendsto f l atTop) (hg : fora
llᶠ x in l, C <= g x) : Tendsto (fun x => f x * g x) l atTop
参数：C : G；hf : Tendsto f l atTop；hg : forallᶠ x in l, C <= g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_of_mul_isBoundedUnder_le`：∀ {α : Type u_1} {M : Typ
e u_2} [inst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelMonoid M] {l 
: Filter α}   {f g : α → M},   Filt…
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
-/
theorem tendsto_atTop_mul_right_of_le' (C : G) (hf : Tendsto f l atTop) (hg : ∀ᶠ x in l, C ≤ g x) :
    Tendsto (fun x => f x * g x) l atTop :=
  .atTop_of_mul_isBoundedUnder_le (g := g⁻¹) ⟨C⁻¹, by simpa⟩ (by simpa)

@[to_additive]
/-
**Filter.tendsto_atBot_mul_right_of_ge'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atBot_mul_right_of_ge' (C : G) (hf : Tendsto f l atBot) (hg : fora
llᶠ x in l, g x <= C) : Tendsto (fun x => f x * g x) l atBot
参数：C : G；hf : Tendsto f l atBot；hg : forallᶠ x in l, g x <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mul_right_of_le'`：tendsto_atTop_mul_right_of_le' (C
 : G) (hf : Tendsto f l atTop) (hg : forallᶠ x in l, C <= g x) : Tendsto (fun x 
=> f x * g x) l atTop
-/
theorem tendsto_atBot_mul_right_of_ge' (C : G) (hf : Tendsto f l atBot) (hg : ∀ᶠ x in l, g x ≤ C) :
    Tendsto (fun x => f x * g x) l atBot :=
  tendsto_atTop_mul_right_of_le' (G := Gᵒᵈ) _ C hf hg

@[to_additive]
/-
**Filter.tendsto_atTop_mul_right_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_mul_right_of_le (C : G) (hf : Tendsto f l atTop) (hg : foral
l x, C <= g x) : Tendsto (fun x => f x * g x) l atTop
参数：C : G；hf : Tendsto f l atTop；hg : forall x, C <= g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mul_right_of_le'`：tendsto_atTop_mul_right_of_le' (C
 : G) (hf : Tendsto f l atTop) (hg : forallᶠ x in l, C <= g x) : Tendsto (fun x 
=> f x * g x) l atTop
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem tendsto_atTop_mul_right_of_le (C : G) (hf : Tendsto f l atTop) (hg : ∀ x, C ≤ g x) :
    Tendsto (fun x => f x * g x) l atTop :=
  tendsto_atTop_mul_right_of_le' l C hf (univ_mem' hg)

@[to_additive]
/-
**Filter.tendsto_atBot_mul_right_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atBot_mul_right_of_ge (C : G) (hf : Tendsto f l atBot) (hg : foral
l x, g x <= C) : Tendsto (fun x => f x * g x) l atBot
参数：C : G；hf : Tendsto f l atBot；hg : forall x, g x <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mul_right_of_le`：tendsto_atTop_mul_right_of_le (C :
 G) (hf : Tendsto f l atTop) (hg : forall x, C <= g x) : Tendsto (fun x => f x *
 g x) l atTop
-/
theorem tendsto_atBot_mul_right_of_ge (C : G) (hf : Tendsto f l atBot) (hg : ∀ x, g x ≤ C) :
    Tendsto (fun x => f x * g x) l atBot :=
  tendsto_atTop_mul_right_of_le (G := Gᵒᵈ) _ C hf hg

@[to_additive]
/-
**Filter.tendsto_atTop_mul_const_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_mul_const_left (C : G) (hf : Tendsto f l atTop) : Tendsto (f
un x => C * f x) l atTop
参数：C : G；hf : Tendsto f l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mul_left_of_le'`：tendsto_atTop_mul_left_of_le' (C :
 G) (hf : forallᶠ x in l, C <= f x) (hg : Tendsto g l atTop) : Tendsto (fun x =>
 f x * g x) l atTop
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem tendsto_atTop_mul_const_left (C : G) (hf : Tendsto f l atTop) :
    Tendsto (fun x => C * f x) l atTop :=
  tendsto_atTop_mul_left_of_le' l C (univ_mem' fun _ => le_refl C) hf

@[to_additive]
/-
**Filter.tendsto_atBot_mul_const_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atBot_mul_const_left (C : G) (hf : Tendsto f l atBot) : Tendsto (f
un x => C * f x) l atBot
参数：C : G；hf : Tendsto f l atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mul_const_left`：tendsto_atTop_mul_const_left (C : G
) (hf : Tendsto f l atTop) : Tendsto (fun x => C * f x) l atTop
-/
theorem tendsto_atBot_mul_const_left (C : G) (hf : Tendsto f l atBot) :
    Tendsto (fun x => C * f x) l atBot :=
  tendsto_atTop_mul_const_left (G := Gᵒᵈ) _ C hf

@[to_additive]
/-
**Filter.tendsto_atTop_mul_const_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_mul_const_right (C : G) (hf : Tendsto f l atTop) : Tendsto (
fun x => f x * C) l atTop
参数：C : G；hf : Tendsto f l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mul_right_of_le'`：tendsto_atTop_mul_right_of_le' (C
 : G) (hf : Tendsto f l atTop) (hg : forallᶠ x in l, C <= g x) : Tendsto (fun x 
=> f x * g x) l atTop
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem tendsto_atTop_mul_const_right (C : G) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * C) l atTop :=
  tendsto_atTop_mul_right_of_le' l C hf (univ_mem' fun _ => le_refl C)

@[to_additive]
/-
**Filter.tendsto_atBot_mul_const_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atBot_mul_const_right (C : G) (hf : Tendsto f l atBot) : Tendsto (
fun x => f x * C) l atBot
参数：C : G；hf : Tendsto f l atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mul_const_right`：tendsto_atTop_mul_const_right (C :
 G) (hf : Tendsto f l atTop) : Tendsto (fun x => f x * C) l atTop
-/
theorem tendsto_atBot_mul_const_right (C : G) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * C) l atBot :=
  tendsto_atTop_mul_const_right (G := Gᵒᵈ) _ C hf

@[to_additive]
/-
**Filter.map_inv_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_inv_atBot : map (Inv.inv : G -> G) atBot = atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_atBot`：map_atBot (e : α ≃o β) : map (e : α -> β) atBot = at
Bot
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem map_inv_atBot : map (Inv.inv : G → G) atBot = atTop :=
  (OrderIso.inv G).map_atBot

@[to_additive]
/-
**Filter.map_inv_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_inv_atTop : map (Inv.inv : G -> G) atTop = atBot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_atTop`：map_atTop (e : α ≃o β) : map (e : α -> β) atTop = at
Top
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem map_inv_atTop : map (Inv.inv : G → G) atTop = atBot :=
  (OrderIso.inv G).map_atTop

@[to_additive]
/-
**Filter.comap_inv_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_inv_atBot : comap (Inv.inv : G -> G) atBot = atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.comap_atTop`：comap_atTop (e : α ≃o β) : comap e atTop = atTop
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem comap_inv_atBot : comap (Inv.inv : G → G) atBot = atTop :=
  (OrderIso.inv G).comap_atTop

@[to_additive]
/-
**Filter.comap_inv_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_inv_atTop : comap (Inv.inv : G -> G) atTop = atBot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.comap_atBot`：comap_atBot (e : α ≃o β) : comap e atBot = atBot
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem comap_inv_atTop : comap (Inv.inv : G → G) atTop = atBot :=
  (OrderIso.inv G).comap_atBot

@[to_additive]
/-
**Filter.tendsto_inv_atTop_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_inv_atTop_atBot : Tendsto (Inv.inv : G -> G) atTop atBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.tendsto_atTop`：tendsto_atTop (e : α ≃o β) : Tendsto e atTop atT
op
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem tendsto_inv_atTop_atBot : Tendsto (Inv.inv : G → G) atTop atBot :=
  (OrderIso.inv G).tendsto_atTop

@[to_additive]
/-
**Filter.tendsto_inv_atBot_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_inv_atBot_atTop : Tendsto (Inv.inv : G -> G) atBot atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_inv_atTop_atBot`：tendsto_inv_atTop_atBot : Tendsto (Inv.i
nv : G -> G) atTop atBot
-/
theorem tendsto_inv_atBot_atTop : Tendsto (Inv.inv : G → G) atBot atTop :=
  tendsto_inv_atTop_atBot (G := Gᵒᵈ)

variable {l}

@[to_additive (attr := simp)]
/-
**Filter.tendsto_inv_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_inv_atTop_iff : Tendsto (fun x => (f x)⁻¹) l atTop ↔ Tendsto f l a
tBot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.tendsto_atBot_iff`：tendsto_atBot_iff {l : Filter γ} {f : γ -> α
} (e : α ≃o β) : Tendsto (fun x => e (f x)) l atBot ↔ Tendsto f l atBot
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem tendsto_inv_atTop_iff : Tendsto (fun x => (f x)⁻¹) l atTop ↔ Tendsto f l atBot :=
  (OrderIso.inv G).tendsto_atBot_iff

@[to_additive (attr := simp)]
/-
**Filter.tendsto_inv_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_inv_atBot_iff : Tendsto (fun x => (f x)⁻¹) l atBot ↔ Tendsto f l a
tTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.tendsto_atTop_iff`：tendsto_atTop_iff {l : Filter γ} {f : γ -> α
} (e : α ≃o β) : Tendsto (fun x => e (f x)) l atTop ↔ Tendsto f l atTop
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem tendsto_inv_atBot_iff : Tendsto (fun x => (f x)⁻¹) l atBot ↔ Tendsto f l atTop :=
  (OrderIso.inv G).tendsto_atTop_iff

@[to_additive (attr := simp)]
/-
**Filter.tendsto_comp_inv_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_comp_inv_atTop_iff {f : G -> α} : Tendsto (fun x => f (x⁻¹)) atTop
 l ↔ Tendsto f atBot l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_inv_atTop`：map_inv_atTop : map (Inv.inv : G -> G) atTop = atB
ot
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_comp_inv_atTop_iff {f : G → α} :
    Tendsto (fun x ↦ f (x⁻¹)) atTop l ↔ Tendsto f atBot l := by
  simp [← Function.comp_def, Tendsto, ← map_map, map_inv_atTop]

@[to_additive (attr := simp)]
/-
**Filter.tendsto_comp_inv_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_comp_inv_atBot_iff {f : G -> α} : Tendsto (fun x => f (x⁻¹)) atBot
 l ↔ Tendsto f atTop l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_inv_atBot`：map_inv_atBot : map (Inv.inv : G -> G) atBot = atT
op
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_comp_inv_atBot_iff {f : G → α} :
    Tendsto (fun x ↦ f (x⁻¹)) atBot l ↔ Tendsto f atTop l := by
  simp [← Function.comp_def, Tendsto, ← map_map, map_inv_atBot]

end OrderedCommGroup

section LinearOrderedCommGroup

variable [CommGroup G] [LinearOrder G]

/-- $\lim_{x\to+\infty}|x|_m=+\infty$ -/
@[to_additive /-- $\lim_{x\to+\infty}|x|=+\infty$ -/]
/-
**Filter.tendsto_mabs_atTop_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mabs_atTop_atTop : Tendsto (mabs : G -> G) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mono`：tendsto_atTop_mono [Preorder β] {l : Filter α
} {f g : α -> β} (h : forall n, f n <= g n) : Tendsto f l atTop -> Tendsto g l a
tTop
· 使用定理 `le_mabs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a 
: α), a ≤ |a|ₘ
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x

--- 原说明 ---
$\lim_{x\to+\infty}|x|_m=+\infty$
-/
theorem tendsto_mabs_atTop_atTop : Tendsto (mabs : G → G) atTop atTop :=
  tendsto_atTop_mono le_mabs_self tendsto_id

/-- $\lim_{x\to\infty^{-1}|x|_m=+\infty$ -/
@[to_additive /-- $\lim_{x\to-\infty}|x|=+\infty$ -/]
/-
**Filter.tendsto_mabs_atBot_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mabs_atBot_atTop [IsOrderedMonoid G] : Tendsto (mabs : G -> G) atB
ot atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mono`：tendsto_atTop_mono [Preorder β] {l : Filter α
} {f g : α -> β} (h : forall n, f n <= g n) : Tendsto f l atTop -> Tendsto g l a
tTop
· 使用定理 `inv_le_mabs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a :
 α), a⁻¹ ≤ |a|ₘ
· 使用定理 `Filter.tendsto_inv_atBot_atTop`：tendsto_inv_atBot_atTop : Tendsto (Inv.i
nv : G -> G) atBot atTop

--- 原说明 ---
$\lim_{x\to\infty^{-1}|x|_m=+\infty$
-/
theorem tendsto_mabs_atBot_atTop [IsOrderedMonoid G] : Tendsto (mabs : G → G) atBot atTop :=
  tendsto_atTop_mono inv_le_mabs tendsto_inv_atBot_atTop

@[to_additive (attr := simp)]
/-
**Filter.comap_mabs_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_mabs_atTop [IsOrderedMonoid G] : comap (mabs : G -> G) atTop = atBot
 ⊔ atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Filter.HasBasis.sup`：∀ {α : Type u_1} {l l' : Filter α} {ι : Type u_6} {
ι' : Type u_7} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set 
α},   l.H…
· 使用引理 `Filter.atBot_basis`：atBot_basis {α : Type*} [Preorder α] [IsCodirectedOr
der α] [Nonempty α] : (@atBot α _).HasBasis (fun _ => True) Iic
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `trivial`：True
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `le_min_iff`：le_min_iff : c <= min a b ↔ c <= a ∧ c <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `min_inv_inv'`：min_inv_inv' (a b : α) : min a⁻¹ b⁻¹ = (max a b)⁻¹
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `le_mabs'`：le_mabs' : a <= |b|ₘ ↔ b <= a⁻¹ ∨ a <= b
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `Filter.tendsto_mabs_atBot_atTop`：tendsto_mabs_atBot_atTop [IsOrderedMono
id G] : Tendsto (mabs : G -> G) atBot atTop
· 使用定理 `Filter.tendsto_mabs_atTop_atTop`：tendsto_mabs_atTop_atTop : Tendsto (mab
s : G -> G) atTop atTop
-/
theorem comap_mabs_atTop [IsOrderedMonoid G] : comap (mabs : G → G) atTop = atBot ⊔ atTop := by
  refine
    le_antisymm (((atTop_basis.comap _).le_basis_iff (atBot_basis.sup atTop_basis)).2 ?_)
      (sup_le tendsto_mabs_atBot_atTop.le_comap tendsto_mabs_atTop_atTop.le_comap)
  rintro ⟨a, b⟩ -
  refine ⟨max (a⁻¹) b, trivial, fun x hx => ?_⟩
  rw [mem_preimage, mem_Ici, le_mabs', max_le_iff, ← min_inv_inv', le_min_iff, inv_inv] at hx
  exact hx.imp And.left And.right

end LinearOrderedCommGroup

end Filter

