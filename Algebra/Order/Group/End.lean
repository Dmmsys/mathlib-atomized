/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.RelIso.Basic
public import Mathlib.Data.FunLike.IsApply

/-!
# Relation isomorphisms form a group

This file contains `Monoid` instances for `RelHom` and `OrderHom`, where multiplication is
given by composition. Likewise there is a `Group` instance for `RelIso`. Because `OrderIso`
is an abbreviation for `RelIso`, there is no need for an additional instance.

## TODO

+ Rename the `mul_def`/`one_def` lemmas to `mul_eq_comp`/`one_eq_id`.
+ Use the `IsMulApplyEqComp` and `IsOneApplyEqSelf` classes for `RelHom` and `RelIso`.
-/

@[expose] public section

assert_not_exists MulAction MonoidWithZero

variable {α : Type*} {r : α -> α -> Prop}

namespace RelHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (r ->r r)
  body: .id r
  mul := .comp
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

中文:
实例 :
  签名: 幺半群 (r ->r r)
  定义体: .id r
  mul := .comp
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
-/
instance : Monoid (r ->r r) where
  one := .id r
  mul := .comp
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/--
lemma `one_def` / 引理 `one_def`

English:
lemma one_def
  statement: (1 : r ->r r) = .id r
  proof: rfl

中文:
引理 one_def
  结论: (1 : r ->r r) = .id r
  证明: rfl
-/
lemma one_def : (1 : r ->r r) = .id r := rfl
/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: (f g : r ->r r)
  statement: (f * g) = f.comp g
  proof: rfl

中文:
引理 mul_def
  条件: (f g : r ->r r)
  结论: (f * g) = f.comp g
  证明: rfl
-/
lemma mul_def (f g : r ->r r) : (f * g) = f.comp g := rfl

/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ⇑(1 : r ->r r) = id
  proof: rfl

中文:
引理 coe_one
  结论: ⇑(1 : r ->r r) = id
  证明: rfl
-/
@[simp] lemma coe_one : ⇑(1 : r ->r r) = id := rfl
/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (f g : r ->r r)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

中文:
引理 coe_mul
  条件: (f g : r ->r r)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl
-/
@[simp] lemma coe_mul (f g : r ->r r) : ⇑(f * g) = f ∘ g := rfl

/--
lemma `one_apply` / 引理 `one_apply`

English:
lemma one_apply
  given: (a : α)
  statement: (1 : r ->r r) a = a
  proof: rfl

中文:
引理 one_apply
  条件: (a : α)
  结论: (1 : r ->r r) a = a
  证明: rfl
-/
lemma one_apply (a : α) : (1 : r ->r r) a = a := rfl
/--
lemma `mul_apply` / 引理 `mul_apply`

English:
lemma mul_apply
  given: (e₁ e₂ : r ->r r) (x : α)
  statement: (e₁ * e₂) x = e₁ (e₂ x)
  proof: rfl

中文:
引理 mul_apply
  条件: (e₁ e₂ : r ->r r) (x : α)
  结论: (e₁ * e₂) x = e₁ (e₂ x)
  证明: rfl
-/
lemma mul_apply (e₁ e₂ : r ->r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

end RelHom

namespace RelEmbedding

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (r ↪r r)
  body: .refl r
  mul f g := g.trans f
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

中文:
实例 :
  签名: 幺半群 (r ↪r r)
  定义体: .refl r
  mul f g := g.trans f
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
-/
instance : Monoid (r ↪r r) where
  one := .refl r
  mul f g := g.trans f
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/--
lemma `one_def` / 引理 `one_def`

English:
lemma one_def
  statement: (1 : r ↪r r) = .refl r
  proof: rfl

中文:
引理 one_def
  结论: (1 : r ↪r r) = .refl r
  证明: rfl
-/
lemma one_def : (1 : r ↪r r) = .refl r := rfl
/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: (f g : r ↪r r)
  statement: (f * g) = g.trans f
  proof: rfl

中文:
引理 mul_def
  条件: (f g : r ↪r r)
  结论: (f * g) = g.trans f
  证明: rfl
-/
lemma mul_def (f g : r ↪r r) : (f * g) = g.trans f := rfl

/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ⇑(1 : r ↪r r) = id
  proof: rfl

中文:
引理 coe_one
  结论: ⇑(1 : r ↪r r) = id
  证明: rfl
-/
@[simp] lemma coe_one : ⇑(1 : r ↪r r) = id := rfl
/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (f g : r ↪r r)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

中文:
引理 coe_mul
  条件: (f g : r ↪r r)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl
-/
@[simp] lemma coe_mul (f g : r ↪r r) : ⇑(f * g) = f ∘ g := rfl

/--
lemma `one_apply` / 引理 `one_apply`

English:
lemma one_apply
  given: (a : α)
  statement: (1 : r ↪r r) a = a
  proof: rfl

中文:
引理 one_apply
  条件: (a : α)
  结论: (1 : r ↪r r) a = a
  证明: rfl
-/
lemma one_apply (a : α) : (1 : r ↪r r) a = a := rfl
/--
lemma `mul_apply` / 引理 `mul_apply`

English:
lemma mul_apply
  given: (e₁ e₂ : r ↪r r) (x : α)
  statement: (e₁ * e₂) x = e₁ (e₂ x)
  proof: rfl

中文:
引理 mul_apply
  条件: (e₁ e₂ : r ↪r r) (x : α)
  结论: (e₁ * e₂) x = e₁ (e₂ x)
  证明: rfl
-/
lemma mul_apply (e₁ e₂ : r ↪r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

end RelEmbedding

namespace RelIso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (r ≃r r)
  body: .refl r
  mul f₁ f₂ := f₂.trans f₁
  inv := .symm
  mul_assoc _ _ _ := rfl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv_mul_cancel f := ext f.symm_apply_apply

中文:
实例 :
  签名: 群 (r ≃r r)
  定义体: .refl r
  mul f₁ f₂ := f₂.trans f₁
  inv := .symm
  mul_assoc _ _ _ := rfl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv_mul_cancel f := ext f.symm_apply_apply
-/
instance : Group (r ≃r r) where
  one := .refl r
  mul f₁ f₂ := f₂.trans f₁
  inv := .symm
  mul_assoc _ _ _ := rfl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv_mul_cancel f := ext f.symm_apply_apply

/--
lemma `one_def` / 引理 `one_def`

English:
lemma one_def
  statement: (1 : r ≃r r) = .refl r
  proof: rfl

中文:
引理 one_def
  结论: (1 : r ≃r r) = .refl r
  证明: rfl
-/
lemma one_def : (1 : r ≃r r) = .refl r := rfl
/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: (f g : r ≃r r)
  statement: (f * g) = g.trans f
  proof: rfl

中文:
引理 mul_def
  条件: (f g : r ≃r r)
  结论: (f * g) = g.trans f
  证明: rfl
-/
lemma mul_def (f g : r ≃r r) : (f * g) = g.trans f := rfl

/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ((1 : r ≃r r) : α -> α) = id
  proof: rfl

中文:
引理 coe_one
  结论: ((1 : r ≃r r) : α -> α) = id
  证明: rfl
-/
@[simp] lemma coe_one : ((1 : r ≃r r) : α -> α) = id := rfl
/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (e₁ e₂ : r ≃r r)
  statement: ((e₁ * e₂) : α -> α) = e₁ ∘ e₂
  proof: rfl

中文:
引理 coe_mul
  条件: (e₁ e₂ : r ≃r r)
  结论: ((e₁ * e₂) : α -> α) = e₁ ∘ e₂
  证明: rfl
-/
@[simp] lemma coe_mul (e₁ e₂ : r ≃r r) : ((e₁ * e₂) : α -> α) = e₁ ∘ e₂ := rfl

/--
lemma `one_apply` / 引理 `one_apply`

English:
lemma one_apply
  given: (x : α)
  statement: (1 : r ≃r r) x = x
  proof: rfl

中文:
引理 one_apply
  条件: (x : α)
  结论: (1 : r ≃r r) x = x
  证明: rfl
-/
lemma one_apply (x : α) : (1 : r ≃r r) x = x := rfl
/--
lemma `mul_apply` / 引理 `mul_apply`

English:
lemma mul_apply
  given: (e₁ e₂ : r ≃r r) (x : α)
  statement: (e₁ * e₂) x = e₁ (e₂ x)
  proof: rfl

@[simp]

中文:
引理 mul_apply
  条件: (e₁ e₂ : r ≃r r) (x : α)
  结论: (e₁ * e₂) x = e₁ (e₂ x)
  证明: rfl

@[simp]
-/
lemma mul_apply (e₁ e₂ : r ≃r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

@[simp]
/--
theorem `inv_apply_self` / 定理 `inv_apply_self`

English:
theorem inv_apply_self
  given: (e : r ≃r r) (x)
  statement: e⁻¹ (e x) = x
  proof: e.symm_apply_apply x

@[simp]

中文:
定理 inv_apply_self
  条件: (e : r ≃r r) (x)
  结论: e⁻¹ (e x) = x
  证明: e.symm_apply_apply x

@[simp]

Depends on / 依赖: e.symm_apply_apply, symm_apply_apply
-/
theorem inv_apply_self (e : r ≃r r) (x) : e⁻¹ (e x) = x :=
  e.symm_apply_apply x

@[simp]
/--
theorem `apply_inv_self` / 定理 `apply_inv_self`

English:
theorem apply_inv_self
  given: (e : r ≃r r) (x)
  statement: e (e⁻¹ x) = x
  proof: e.apply_symm_apply x

中文:
定理 apply_inv_self
  条件: (e : r ≃r r) (x)
  结论: e (e⁻¹ x) = x
  证明: e.apply_symm_apply x

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply
-/
theorem apply_inv_self (e : r ≃r r) (x) : e (e⁻¹ x) = x :=
  e.apply_symm_apply x

end RelIso

namespace OrderHom

variable [Preorder α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (α ->o α)
  body: f.comp g

中文:
实例 :
  签名: 乘法 (α ->o α)
  定义体: f.comp g

Depends on / 依赖: f.comp
-/
instance : Mul (α ->o α) where mul f g := f.comp g
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (α ->o α)
  body: .id

中文:
实例 :
  签名: 幺 (α ->o α)
  定义体: .id
-/
instance : One (α ->o α) where one := .id
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMulApplyEqComp (α ->o α) α
  body: rfl

中文:
实例 :
  签名: 是MulApplyEqComp (α ->o α) α
  定义体: rfl
-/
instance : IsMulApplyEqComp (α ->o α) α where mul_apply_eq_comp _ _ _ := rfl
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOneApplyEqSelf (α ->o α) α
  body: rfl

中文:
实例 :
  签名: 是OneApplyEqSelf (α ->o α) α
  定义体: rfl
-/
instance : IsOneApplyEqSelf (α ->o α) α where one_apply_eq_self _ := rfl

/--
lemma `mul_eq_comp` / 引理 `mul_eq_comp`

English:
lemma mul_eq_comp
  given: (f g : α ->o α)
  statement: (f * g : α ->o α) = f.comp g
  proof: rfl

中文:
引理 mul_eq_comp
  条件: (f g : α ->o α)
  结论: (f * g : α ->o α) = f.comp g
  证明: rfl
-/
lemma mul_eq_comp (f g : α ->o α) : (f * g : α ->o α) = f.comp g := rfl
/--
lemma `one_eq_id` / 引理 `one_eq_id`

English:
lemma one_eq_id
  statement: (1 : α ->o α) = .id
  proof: rfl

中文:
引理 one_eq_id
  结论: (1 : α ->o α) = .id
  证明: rfl
-/
lemma one_eq_id : (1 : α ->o α) = .id := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (α ->o α)
  body: by simp [DFunLike.ext_iff]
  one_mul f := by simp [DFunLike.ext_iff]
  mul_one f := by simp [DFunLike.ext_iff]

中文:
实例 :
  签名: 幺半群 (α ->o α)
  定义体: by simp [DFunLike.ext_iff]
  one_mul f := by simp [DFunLike.ext_iff]
  mul_one f := by simp [DFunLike.ext_iff]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, mul_one, one_mul
-/
instance : Monoid (α ->o α) where
  mul_assoc f g h := by simp [DFunLike.ext_iff]
  one_mul f := by simp [DFunLike.ext_iff]
  mul_one f := by simp [DFunLike.ext_iff]

end OrderHom
