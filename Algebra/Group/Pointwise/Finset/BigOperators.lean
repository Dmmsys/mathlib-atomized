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
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (s : Finset ι) (f : ι -> Finset α)
  proof: map_prod (coeMonoidHom : Finset α ->* Set α) _ _

omit [DecidableEq α]

中文:
定理 coe_prod
  条件: (s : 有限集 ι) (f : ι -> 有限集 α)
  证明: map_prod (coeMonoidHom : Finset α ->* Set α) _ _

omit [DecidableEq α]

Depends on / 依赖: Finset, coeMonoidHom, map_prod
-/
theorem coe_prod (s : Finset ι) (f : ι -> Finset α) :
    ↑(∏ i in s, f i) = ∏ i in s, (f i : Set α) :=
  map_prod (coeMonoidHom : Finset α ->* Set α) _ _

omit [DecidableEq α]
variable [DecidableEq ι]

/--
lemma `prod_inv_index` / 引理 `prod_inv_index`

English:
lemma prod_inv_index
  given: [InvolutiveInv ι] (s : Finset ι) (f : ι -> α)
  proof: prod_image inv_injective.injOn

中文:
引理 prod_inv_index
  条件: [InvolutiveInv ι] (s : 有限集 ι) (f : ι -> α)
  证明: prod_image inv_injective.injOn
-/
@[to_additive (attr := simp)] lemma prod_inv_index [InvolutiveInv ι] (s : Finset ι) (f : ι -> α) :
    ∏ i in s⁻¹, f i = ∏ i in s, f i⁻¹ := prod_image inv_injective.injOn

/--
lemma `prod_neg_index` / 引理 `prod_neg_index`

English:
lemma prod_neg_index
  given: [InvolutiveNeg ι] (s : Finset ι) (f : ι -> α)
  proof: prod_image neg_injective.injOn

中文:
引理 prod_neg_index
  条件: [InvolutiveNeg ι] (s : 有限集 ι) (f : ι -> α)
  证明: prod_image neg_injective.injOn
-/
@[to_additive existing, simp] lemma prod_neg_index [InvolutiveNeg ι] (s : Finset ι) (f : ι -> α) :
    ∏ i in -s, f i = ∏ i in s, f (-i) := prod_image neg_injective.injOn

end CommMonoid

section AddCommMonoid

variable [AddCommMonoid α] [DecidableEq ι]

/--
lemma `sum_inv_index` / 引理 `sum_inv_index`

English:
lemma sum_inv_index
  given: [InvolutiveInv ι] (s : Finset ι) (f : ι -> α)
  proof: sum_image inv_injective.injOn

中文:
引理 sum_inv_index
  条件: [InvolutiveInv ι] (s : 有限集 ι) (f : ι -> α)
  证明: sum_image inv_injective.injOn
-/
@[to_additive existing, simp] lemma sum_inv_index [InvolutiveInv ι] (s : Finset ι) (f : ι -> α) :
    ∑ i in s⁻¹, f i = ∑ i in s, f i⁻¹ := sum_image inv_injective.injOn

end AddCommMonoid

end Finset
