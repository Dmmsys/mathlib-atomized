/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Pointwise big operators on finsets

This file contains basic results on applying big operators (product and sum) on finsets.

## Implementation notes

We put all instances in the scope `Pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the scope to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`).

## Tags

finset multiplication, finset addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

public section

open scoped Pointwise

variable {α ι : Type*}

namespace Finset

section CommMonoid

variable [CommMonoid α]

variable [DecidableEq α]

@[to_additive (attr := simp, norm_cast)]
/-
**Finset.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_prod (s : Finset ι) (f : ι -> Finset α) : ↑(∏ i in s, f i) = ∏ i in s,
 (f i : Set α)
参数：s : Finset ι；f : ι -> Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem coe_prod (s : Finset ι) (f : ι → Finset α) :
    ↑(∏ i ∈ s, f i) = ∏ i ∈ s, (f i : Set α) :=
  map_prod (coeMonoidHom : Finset α →* Set α) _ _

omit [DecidableEq α]
variable [DecidableEq ι]
/-
**Finset.prod_inv_index** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : CommMonoid α] [inst_1 : DecidableE
q ι] [inst_2 : InvolutiveInv ι] (s : Finset ι)   (f : ι → α), ∏ i ∈ s⁻¹, f i = ∏
 i ∈ s, f i⁻¹
参数：s : Finset ι；f : ι → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_image`：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι
} : Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `inv_injective`：inv_injective : Function.Injective (Inv.inv : G -> G)
-/
@[to_additive (attr := simp)] lemma prod_inv_index [InvolutiveInv ι] (s : Finset ι) (f : ι → α) :
    ∏ i ∈ s⁻¹, f i = ∏ i ∈ s, f i⁻¹ := prod_image inv_injective.injOn
/-
**Finset.prod_neg_index** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : CommMonoid α] [inst_1 : DecidableE
q ι] [inst_2 : InvolutiveNeg ι] (s : Finset ι)   (f : ι → α), ∏ i ∈ -s, f i = ∏ 
i ∈ s, f (-i)
参数：s : Finset ι；f : ι → α；-i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_image`：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι
} : Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
-/
@[to_additive existing, simp] lemma prod_neg_index [InvolutiveNeg ι] (s : Finset ι) (f : ι → α) :
    ∏ i ∈ -s, f i = ∏ i ∈ s, f (-i) := prod_image neg_injective.injOn

end CommMonoid

section AddCommMonoid

variable [AddCommMonoid α] [DecidableEq ι]

/-
**Finset.sum_inv_index** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : AddCommMonoid α] [inst_1 : Decidab
leEq ι] [inst_2 : InvolutiveInv ι]   (s : Finset ι) (f : ι → α), ∑ i ∈ s⁻¹, f i 
= ∑ i ∈ s, f i⁻¹
参数：s : Finset ι；f : ι → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `inv_injective`：inv_injective : Function.Injective (Inv.inv : G -> G)
-/
@[to_additive existing, simp] lemma sum_inv_index [InvolutiveInv ι] (s : Finset ι) (f : ι → α) :
    ∑ i ∈ s⁻¹, f i = ∑ i ∈ s, f i⁻¹ := sum_image inv_injective.injOn

end AddCommMonoid

end Finset

