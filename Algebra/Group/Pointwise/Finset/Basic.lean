/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Finset.Preimage

/-!
# Pointwise operations of finsets

This file defines pointwise algebraic operations on finsets.

## Main declarations

For finsets `s` and `t`:
* `0` (`Finset.zero`): The singleton `{0}`.
* `1` (`Finset.one`): The singleton `{1}`.
* `-s` (`Finset.neg`): Negation, finset of all `-x` where `x ∈ s`.
* `s⁻¹` (`Finset.inv`): Inversion, finset of all `x⁻¹` where `x ∈ s`.
* `s + t` (`Finset.add`): Addition, finset of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s * t` (`Finset.mul`): Multiplication, finset of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s - t` (`Finset.sub`): Subtraction, finset of all `x - y` where `x ∈ s` and `y ∈ t`.
* `s / t` (`Finset.div`): Division, finset of all `x / y` where `x ∈ s` and `y ∈ t`.

For `α` a semigroup/monoid, `Finset α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

## Implementation notes

We put all instances in the scope `Pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the scope to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`).

## Tags

finset multiplication, finset addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

@[expose] public section

assert_not_exists Cardinal Finset.dens MonoidWithZero MulAction IsOrderedMonoid

open Function MulOpposite

open scoped Pointwise

variable {F α β γ : Type*}

namespace Finset

/-! ### `0`/`1` as finsets -/

section One

variable [One α] {s : Finset α} {a : α}

/-- The finset `1 : Finset α` is defined as `{1}` in scope `Pointwise`. -/
@[to_additive (attr := instance_reducible)
  /-- The finset `0 : Finset α` is defined as `{0}` in scope `Pointwise`. -/]
/--
Definition of `one` / `one` 的定义

English:
definition one
  signature: : One (Finset α)
  body: ⟨{1}⟩

scoped[Pointwise] attribute [instance] Finset.one Finset.zero

@[to_additive (attr := simp)]

中文:
定义 one
  签名: : 幺 (有限集 α)
  定义体: ⟨{1}⟩

scoped[Pointwise] attribute [instance] Finset.one Finset.zero

@[to_additive (attr := simp)]
-/
protected def one : One (Finset α) :=
  ⟨{1}⟩

scoped[Pointwise] attribute [instance] Finset.one Finset.zero

@[to_additive (attr := simp)]
/--
theorem `mem_one` / 定理 `mem_one`

English:
theorem mem_one
  statement: a in (1 : Finset α) ↔ a = 1
  proof: mem_singleton

@[to_additive (attr := simp, norm_cast)]

中文:
定理 mem_one
  结论: a in (1 : 有限集 α) ↔ a = 1
  证明: mem_singleton

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: mem_singleton
-/
theorem mem_one : a in (1 : Finset α) ↔ a = 1 :=
  mem_singleton

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ↑(1 : Finset α) = (1 : Set α)
  proof: coe_singleton 1

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_one
  结论: ↑(1 : 有限集 α) = (1 : 集合 α)
  证明: coe_singleton 1

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: coe_singleton
-/
theorem coe_one : ↑(1 : Finset α) = (1 : Set α) :=
  coe_singleton 1

@[to_additive (attr := simp, norm_cast)]
/--
lemma `coe_eq_one` / 引理 `coe_eq_one`

English:
lemma coe_eq_one
  statement: (s : Set α) = 1 ↔ s = 1
  proof: coe_eq_singleton

@[to_additive (attr := simp)]

中文:
引理 coe_eq_one
  结论: (s : 集合 α) = 1 ↔ s = 1
  证明: coe_eq_singleton

@[to_additive (attr := simp)]

Depends on / 依赖: coe_eq_singleton
-/
lemma coe_eq_one : (s : Set α) = 1 ↔ s = 1 := coe_eq_singleton

@[to_additive (attr := simp)]
/--
theorem `one_subset` / 定理 `one_subset`

English:
theorem one_subset
  statement: (1 : Finset α) subseteq s ↔ (1 : α) in s
  proof: singleton_subset_iff

中文:
定理 one_subset
  结论: (1 : 有限集 α) subseteq s ↔ (1 : α) in s
  证明: singleton_subset_iff

Depends on / 依赖: singleton_subset_iff
-/
theorem one_subset : (1 : Finset α) subseteq s ↔ (1 : α) in s :=
  singleton_subset_iff

-- TODO: This would be a good simp lemma scoped to `Pointwise`, but it seems `@[simp]` can't be
-- scoped
@[to_additive]
/--
theorem `singleton_one` / 定理 `singleton_one`

English:
theorem singleton_one
  statement: ({1} : Finset α) = 1
  proof: rfl

@[to_additive]

中文:
定理 singleton_one
  结论: ({1} : 有限集 α) = 1
  证明: rfl

@[to_additive]
-/
theorem singleton_one : ({1} : Finset α) = 1 :=
  rfl

@[to_additive]
/--
theorem `one_mem_one` / 定理 `one_mem_one`

English:
theorem one_mem_one
  statement: (1 : α) in (1 : Finset α)
  proof: mem_singleton_self _

@[to_additive (attr := simp, aesop safe apply (rule_sets := [finsetNonempty]))]

中文:
定理 one_mem_one
  结论: (1 : α) in (1 : 有限集 α)
  证明: mem_singleton_self _

@[to_additive (attr := simp, aesop safe apply (rule_sets := [finsetNonempty]))]

Depends on / 依赖: mem_singleton_self
-/
theorem one_mem_one : (1 : α) in (1 : Finset α) :=
  mem_singleton_self _

@[to_additive (attr := simp, aesop safe apply (rule_sets := [finsetNonempty]))]
/--
theorem `one_nonempty` / 定理 `one_nonempty`

English:
theorem one_nonempty
  statement: (1 : Finset α).Nonempty
  proof: ⟨1, one_mem_one⟩

@[to_additive (attr := simp)]

中文:
定理 one_nonempty
  结论: (1 : 有限集 α).非空
  证明: ⟨1, one_mem_one⟩

@[to_additive (attr := simp)]

Depends on / 依赖: one_mem_one
-/
theorem one_nonempty : (1 : Finset α).Nonempty :=
  ⟨1, one_mem_one⟩

@[to_additive (attr := simp)]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: {f : α ↪ β}
  statement: map f 1 = {f 1}
  proof: map_singleton f 1

@[to_additive (attr := simp)]

中文:
定理 map_one
  条件: {f : α ↪ β}
  结论: map f 1 = {f 1}
  证明: map_singleton f 1

@[to_additive (attr := simp)]
-/
protected theorem map_one {f : α ↪ β} : map f 1 = {f 1} :=
  map_singleton f 1

@[to_additive (attr := simp)]
/--
theorem `image_one` / 定理 `image_one`

English:
theorem image_one
  given: [DecidableEq β] {f : α -> β}
  statement: image f 1 = {f 1}
  proof: image_singleton _ _

@[to_additive]

中文:
定理 image_one
  条件: [DecidableEq β] {f : α -> β}
  结论: 像 f 1 = {f 1}
  证明: image_singleton _ _

@[to_additive]

Depends on / 依赖: image_singleton
-/
theorem image_one [DecidableEq β] {f : α -> β} : image f 1 = {f 1} :=
  image_singleton _ _

@[to_additive]
/--
theorem `subset_one_iff_eq` / 定理 `subset_one_iff_eq`

English:
theorem subset_one_iff_eq
  statement: s subseteq 1 ↔ s = ∅ ∨ s = 1
  proof: subset_singleton_iff

@[to_additive]

中文:
定理 subset_one_iff_eq
  结论: s subseteq 1 ↔ s = ∅ ∨ s = 1
  证明: subset_singleton_iff

@[to_additive]

Depends on / 依赖: subset_singleton_iff
-/
theorem subset_one_iff_eq : s subseteq 1 ↔ s = ∅ ∨ s = 1 :=
  subset_singleton_iff

@[to_additive]
/--
theorem `Nonempty.subset_one_iff` / 定理 `Nonempty.subset_one_iff`

English:
theorem Nonempty.subset_one_iff
  given: (h : s.Nonempty)
  statement: s subseteq 1 ↔ s = 1
  proof: h.subset_singleton_iff

@[to_additive (attr := simp)]

中文:
定理 非空.subset_one_iff
  条件: (h : s.非空)
  结论: s subseteq 1 ↔ s = 1
  证明: h.subset_singleton_iff

@[to_additive (attr := simp)]

Depends on / 依赖: h.subset_singleton_iff, subset_singleton_iff
-/
theorem Nonempty.subset_one_iff (h : s.Nonempty) : s subseteq 1 ↔ s = 1 :=
  h.subset_singleton_iff

@[to_additive (attr := simp)]
/--
theorem `card_one` / 定理 `card_one`

English:
theorem card_one
  statement: #(1 : Finset α) = 1
  proof: card_singleton _

中文:
定理 card_one
  结论: #(1 : 有限集 α) = 1
  证明: card_singleton _

Depends on / 依赖: card_singleton
-/
theorem card_one : #(1 : Finset α) = 1 :=
  card_singleton _

/-- The singleton operation as a `OneHom`. -/
@[to_additive /-- The singleton operation as a `ZeroHom`. -/]
/--
Definition of `singletonOneHom` / `singletonOneHom` 的定义

English:
definition singletonOneHom
  signature: : OneHom α (Finset α) where
  body: singleton; map_one' := singleton_one

@[to_additive (attr := simp)]

中文:
定义 singletonOneHom
  签名: : 幺态射 α (有限集 α) where
  定义体: singleton; map_one' := singleton_one

@[to_additive (attr := simp)]

Depends on / 依赖: map_one, singleton, singleton_one
-/
def singletonOneHom : OneHom α (Finset α) where
  toFun := singleton; map_one' := singleton_one

@[to_additive (attr := simp)]
/--
theorem `coe_singletonOneHom` / 定理 `coe_singletonOneHom`

English:
theorem coe_singletonOneHom
  statement: (singletonOneHom : α -> Finset α) = singleton
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_singletonOneHom
  结论: (singletonOneHom : α -> 有限集 α) = singleton
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_singletonOneHom : (singletonOneHom : α -> Finset α) = singleton :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `singletonOneHom_apply` / 定理 `singletonOneHom_apply`

English:
theorem singletonOneHom_apply
  given: (a : α)
  statement: singletonOneHom a = {a}
  proof: rfl

中文:
定理 singletonOneHom_apply
  条件: (a : α)
  结论: singletonOneHom a = {a}
  证明: rfl
-/
theorem singletonOneHom_apply (a : α) : singletonOneHom a = {a} :=
  rfl

/-- Lift a `OneHom` to `Finset` via `image`. -/
@[to_additive (attr := simps) /-- Lift a `ZeroHom` to `Finset` via `image` -/]
/--
Definition of `imageOneHom` / `imageOneHom` 的定义

English:
definition imageOneHom
  signature: [DecidableEq β] [One β] [FunLike F α β] [OneHomClass F α β] (f : F)
  body: Finset.image f
  map_one' := by rw [image_one, map_one, singleton_one]

@[to_additive (attr := simp)]

中文:
定义 imageOneHom
  签名: [DecidableEq β] [幺 β] [函数状 F α β] [幺态射类 F α β] (f : F)
  定义体: Finset.image f
  map_one' := by rw [image_one, map_one, singleton_one]

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.image
-/
def imageOneHom [DecidableEq β] [One β] [FunLike F α β] [OneHomClass F α β] (f : F) :
    OneHom (Finset α) (Finset β) where
  toFun := Finset.image f
  map_one' := by rw [image_one, map_one, singleton_one]

@[to_additive (attr := simp)]
/--
lemma `sup_one` / 引理 `sup_one`

English:
lemma sup_one
  given: [SemilatticeSup β] [OrderBot β] (f : α -> β)
  statement: sup 1 f = f 1
  proof: sup_singleton

@[to_additive (attr := simp)]

中文:
引理 sup_one
  条件: [SemilatticeSup β] [有底序 β] (f : α -> β)
  结论: 上确界 1 f = f 1
  证明: sup_singleton

@[to_additive (attr := simp)]

Depends on / 依赖: sup_singleton
-/
lemma sup_one [SemilatticeSup β] [OrderBot β] (f : α -> β) : sup 1 f = f 1 := sup_singleton

@[to_additive (attr := simp)]
/--
lemma `sup'_one` / 引理 `sup'_one`

English:
lemma sup'_one
  given: [SemilatticeSup β] (f : α -> β)
  statement: sup' 1 one_nonempty f = f 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 上确界'_one
  条件: [SemilatticeSup β] (f : α -> β)
  结论: 上确界' 1 one_nonempty f = f 1
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonempty f = f 1 := rfl

@[to_additive (attr := simp)]
/--
lemma `inf_one` / 引理 `inf_one`

English:
lemma inf_one
  given: [SemilatticeInf β] [OrderTop β] (f : α -> β)
  statement: inf 1 f = f 1
  proof: inf_singleton

@[to_additive (attr := simp)]

中文:
引理 inf_one
  条件: [SemilatticeInf β] [有顶序 β] (f : α -> β)
  结论: 下确界 1 f = f 1
  证明: inf_singleton

@[to_additive (attr := simp)]

Depends on / 依赖: inf_singleton
-/
lemma inf_one [SemilatticeInf β] [OrderTop β] (f : α -> β) : inf 1 f = f 1 := inf_singleton

@[to_additive (attr := simp)]
/--
lemma `inf'_one` / 引理 `inf'_one`

English:
lemma inf'_one
  given: [SemilatticeInf β] (f : α -> β)
  statement: inf' 1 one_nonempty f = f 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 下确界'_one
  条件: [SemilatticeInf β] (f : α -> β)
  结论: 下确界' 1 one_nonempty f = f 1
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonempty f = f 1 := rfl

@[to_additive (attr := simp)]
/--
lemma `max_one` / 引理 `max_one`

English:
lemma max_one
  given: [LinearOrder α]
  statement: (1 : Finset α).max = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 max_one
  条件: [线性序 α]
  结论: (1 : 有限集 α).最大值 = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma max_one [LinearOrder α] : (1 : Finset α).max = 1 := rfl

@[to_additive (attr := simp)]
/--
lemma `min_one` / 引理 `min_one`

English:
lemma min_one
  given: [LinearOrder α]
  statement: (1 : Finset α).min = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 min_one
  条件: [线性序 α]
  结论: (1 : 有限集 α).最小值 = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma min_one [LinearOrder α] : (1 : Finset α).min = 1 := rfl

@[to_additive (attr := simp)]
/--
lemma `max'_one` / 引理 `max'_one`

English:
lemma max'_one
  given: [LinearOrder α]
  statement: (1 : Finset α).max' one_nonempty = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 最大值'_one
  条件: [线性序 α]
  结论: (1 : 有限集 α).最大值' one_nonempty = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty = 1 := rfl

@[to_additive (attr := simp)]
/--
lemma `min'_one` / 引理 `min'_one`

English:
lemma min'_one
  given: [LinearOrder α]
  statement: (1 : Finset α).min' one_nonempty = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 最小值'_one
  条件: [线性序 α]
  结论: (1 : 有限集 α).最小值' one_nonempty = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty = 1 := rfl

@[to_additive (attr := simp)]
/--
lemma `image_op_one` / 引理 `image_op_one`

English:
lemma image_op_one
  given: [DecidableEq α]
  statement: (1 : Finset α).image op = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 image_op_one
  条件: [DecidableEq α]
  结论: (1 : 有限集 α).像 op = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma image_op_one [DecidableEq α] : (1 : Finset α).image op = 1 := rfl

@[to_additive (attr := simp)]
/--
lemma `map_op_one` / 引理 `map_op_one`

English:
lemma map_op_one
  statement: (1 : Finset α).map opEquiv.toEmbedding = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 map_op_one
  结论: (1 : 有限集 α).map opEquiv.toEmbedding = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma map_op_one : (1 : Finset α).map opEquiv.toEmbedding = 1 := rfl

@[to_additive (attr := simp)]
/--
lemma `one_product_one` / 引理 `one_product_one`

English:
lemma one_product_one
  given: [One β]
  statement: (1 ×ˢ 1 : Finset (α × β)) = 1
  proof: by ext; simp [Prod.ext_iff]

中文:
引理 one_product_one
  条件: [幺 β]
  结论: (1 ×ˢ 1 : 有限集 (α × β)) = 1
  证明: by ext; simp [Prod.ext_iff]

Depends on / 依赖: Prod.ext_iff, ext_iff
-/
lemma one_product_one [One β] : (1 ×ˢ 1 : Finset (α × β)) = 1 := by ext; simp [Prod.ext_iff]

end One

/-! ### Finset negation/inversion -/

section Inv

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

/-- The pointwise inversion of finset `s⁻¹` is defined as `{x⁻¹ | x ∈ s}` in scope `Pointwise`. -/
@[to_additive (attr := instance_reducible)
  /-- The pointwise negation of finset `-s` is defined as `{-x | x ∈ s}` in scope `Pointwise`. -/]
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : Inv (Finset α)
  body: ⟨image Inv.inv⟩

scoped[Pointwise] attribute [instance] Finset.inv Finset.neg

@[to_additive]

中文:
定义 inv
  签名: : 取逆 (有限集 α)
  定义体: ⟨image Inv.inv⟩

scoped[Pointwise] attribute [instance] Finset.inv Finset.neg

@[to_additive]
-/
protected def inv : Inv (Finset α) :=
  ⟨image Inv.inv⟩

scoped[Pointwise] attribute [instance] Finset.inv Finset.neg

@[to_additive]
/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  statement: s⁻¹ = s.image fun x => x⁻¹
  proof: rfl

中文:
定理 inv_def
  结论: s⁻¹ = s.像 fun x => x⁻¹
  证明: rfl
-/
theorem inv_def : s⁻¹ = s.image fun x => x⁻¹ :=
  rfl

/--
lemma `image_inv_eq_inv` / 引理 `image_inv_eq_inv`

English:
lemma image_inv_eq_inv
  given: (s : Finset α)
  statement: s.image (·⁻¹) = s⁻¹
  proof: rfl

@[to_additive]

中文:
引理 image_inv_eq_inv
  条件: (s : 有限集 α)
  结论: s.像 (·⁻¹) = s⁻¹
  证明: rfl

@[to_additive]
-/
@[to_additive] lemma image_inv_eq_inv (s : Finset α) : s.image (·⁻¹) = s⁻¹ := rfl

@[to_additive]
/--
theorem `mem_inv` / 定理 `mem_inv`

English:
theorem mem_inv
  given: {x : α}
  statement: x in s⁻¹ ↔ exists y in s, y⁻¹ = x
  proof: mem_image

@[to_additive]

中文:
定理 mem_inv
  条件: {x : α}
  结论: x in s⁻¹ ↔ 存在 y in s, y⁻¹ = x
  证明: mem_image

@[to_additive]

Depends on / 依赖: mem_image
-/
theorem mem_inv {x : α} : x in s⁻¹ ↔ exists y in s, y⁻¹ = x :=
  mem_image

@[to_additive]
/--
theorem `inv_mem_inv` / 定理 `inv_mem_inv`

English:
theorem inv_mem_inv
  given: (ha : a in s)
  statement: a⁻¹ in s⁻¹
  proof: mem_image_of_mem _ ha

@[to_additive]

中文:
定理 inv_mem_inv
  条件: (ha : a in s)
  结论: a⁻¹ in s⁻¹
  证明: mem_image_of_mem _ ha

@[to_additive]

Depends on / 依赖: mem_image_of_mem
-/
theorem inv_mem_inv (ha : a in s) : a⁻¹ in s⁻¹ :=
  mem_image_of_mem _ ha

@[to_additive]
/--
theorem `card_inv_le` / 定理 `card_inv_le`

English:
theorem card_inv_le
  statement: #s⁻¹ <= #s
  proof: card_image_le

@[to_additive (attr := simp)]

中文:
定理 card_inv_le
  结论: #s⁻¹ <= #s
  证明: card_image_le

@[to_additive (attr := simp)]

Depends on / 依赖: card_image_le
-/
theorem card_inv_le : #s⁻¹ <= #s :=
  card_image_le

@[to_additive (attr := simp)]
/--
theorem `inv_empty` / 定理 `inv_empty`

English:
theorem inv_empty
  statement: (∅ : Finset α)⁻¹ = ∅
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inv_empty
  结论: (∅ : 有限集 α)⁻¹ = ∅
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inv_empty : (∅ : Finset α)⁻¹ = ∅ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `inv_nonempty_iff` / 定理 `inv_nonempty_iff`

English:
theorem inv_nonempty_iff
  statement: s⁻¹.Nonempty ↔ s.Nonempty
  proof: image_nonempty

alias ⟨Nonempty.of_inv, Nonempty.inv⟩ := inv_nonempty_iff

中文:
定理 inv_nonempty_iff
  结论: s⁻¹.非空 ↔ s.非空
  证明: image_nonempty

alias ⟨Nonempty.of_inv, Nonempty.inv⟩ := inv_nonempty_iff

Depends on / 依赖: image_nonempty
-/
theorem inv_nonempty_iff : s⁻¹.Nonempty ↔ s.Nonempty := image_nonempty

alias ⟨Nonempty.of_inv, Nonempty.inv⟩ := inv_nonempty_iff

attribute [to_additive] Nonempty.inv Nonempty.of_inv
attribute [aesop safe apply (rule_sets := [finsetNonempty])] Nonempty.inv Nonempty.neg

@[to_additive (attr := simp)]
/--
theorem `inv_eq_empty` / 定理 `inv_eq_empty`

English:
theorem inv_eq_empty
  statement: s⁻¹ = ∅ ↔ s = ∅
  proof: image_eq_empty

@[to_additive (attr := mono, gcongr)]

中文:
定理 inv_eq_empty
  结论: s⁻¹ = ∅ ↔ s = ∅
  证明: image_eq_empty

@[to_additive (attr := mono, gcongr)]

Depends on / 依赖: image_eq_empty
-/
theorem inv_eq_empty : s⁻¹ = ∅ ↔ s = ∅ := image_eq_empty

@[to_additive (attr := mono, gcongr)]
/--
theorem `inv_subset_inv` / 定理 `inv_subset_inv`

English:
theorem inv_subset_inv
  given: (h : s subseteq t)
  statement: s⁻¹ subseteq t⁻¹
  proof: image_subset_image h

@[to_additive (attr := simp)]

中文:
定理 inv_subset_inv
  条件: (h : s subseteq t)
  结论: s⁻¹ subseteq t⁻¹
  证明: image_subset_image h

@[to_additive (attr := simp)]

Depends on / 依赖: image_subset_image
-/
theorem inv_subset_inv (h : s subseteq t) : s⁻¹ subseteq t⁻¹ :=
  image_subset_image h

@[to_additive (attr := simp)]
/--
theorem `inv_singleton` / 定理 `inv_singleton`

English:
theorem inv_singleton
  given: (a : α)
  statement: ({a} : Finset α)⁻¹ = {a⁻¹}
  proof: image_singleton _ _

@[to_additive (attr := simp)]

中文:
定理 inv_singleton
  条件: (a : α)
  结论: ({a} : 有限集 α)⁻¹ = {a⁻¹}
  证明: image_singleton _ _

@[to_additive (attr := simp)]

Depends on / 依赖: image_singleton
-/
theorem inv_singleton (a : α) : ({a} : Finset α)⁻¹ = {a⁻¹} :=
  image_singleton _ _

@[to_additive (attr := simp)]
/--
theorem `inv_insert` / 定理 `inv_insert`

English:
theorem inv_insert
  given: (a : α) (s : Finset α)
  statement: (insert a s)⁻¹ = insert a⁻¹ s⁻¹
  proof: image_insert _ _ _

@[to_additive (attr := simp)]

中文:
定理 inv_insert
  条件: (a : α) (s : 有限集 α)
  结论: (insert a s)⁻¹ = insert a⁻¹ s⁻¹
  证明: image_insert _ _ _

@[to_additive (attr := simp)]

Depends on / 依赖: image_insert
-/
theorem inv_insert (a : α) (s : Finset α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ :=
  image_insert _ _ _

@[to_additive (attr := simp)]
/--
lemma `sup_inv` / 引理 `sup_inv`

English:
lemma sup_inv
  given: [SemilatticeSup β] [OrderBot β] (s : Finset α) (f : α -> β)
  proof: sup_image ..

@[to_additive (attr := simp)]

中文:
引理 sup_inv
  条件: [SemilatticeSup β] [有底序 β] (s : 有限集 α) (f : α -> β)
  证明: sup_image ..

@[to_additive (attr := simp)]

Depends on / 依赖: sup_image
-/
lemma sup_inv [SemilatticeSup β] [OrderBot β] (s : Finset α) (f : α -> β) :
    sup s⁻¹ f = sup s (f ·⁻¹) :=
  sup_image ..

@[to_additive (attr := simp)]
/--
lemma `sup'_inv` / 引理 `sup'_inv`

English:
lemma sup'_inv
  given: [SemilatticeSup β] {s : Finset α} (hs : s⁻¹.Nonempty) (f : α -> β)
  proof: sup'_image ..

@[to_additive (attr := simp)]

中文:
引理 上确界'_inv
  条件: [SemilatticeSup β] {s : 有限集 α} (hs : s⁻¹.非空) (f : α -> β)
  证明: sup'_image ..

@[to_additive (attr := simp)]
-/
lemma sup'_inv [SemilatticeSup β] {s : Finset α} (hs : s⁻¹.Nonempty) (f : α -> β) :
    sup' s⁻¹ hs f = sup' s hs.of_inv (f ·⁻¹) :=
  sup'_image ..

@[to_additive (attr := simp)]
/--
lemma `inf_inv` / 引理 `inf_inv`

English:
lemma inf_inv
  given: [SemilatticeInf β] [OrderTop β] (s : Finset α) (f : α -> β)
  proof: inf_image ..

@[to_additive (attr := simp)]

中文:
引理 inf_inv
  条件: [SemilatticeInf β] [有顶序 β] (s : 有限集 α) (f : α -> β)
  证明: inf_image ..

@[to_additive (attr := simp)]

Depends on / 依赖: inf_image
-/
lemma inf_inv [SemilatticeInf β] [OrderTop β] (s : Finset α) (f : α -> β) :
    inf s⁻¹ f = inf s (f ·⁻¹) :=
  inf_image ..

@[to_additive (attr := simp)]
/--
lemma `inf'_inv` / 引理 `inf'_inv`

English:
lemma inf'_inv
  given: [SemilatticeInf β] {s : Finset α} (hs : s⁻¹.Nonempty) (f : α -> β)
  proof: inf'_image ..

中文:
引理 下确界'_inv
  条件: [SemilatticeInf β] {s : 有限集 α} (hs : s⁻¹.非空) (f : α -> β)
  证明: inf'_image ..
-/
lemma inf'_inv [SemilatticeInf β] {s : Finset α} (hs : s⁻¹.Nonempty) (f : α -> β) :
    inf' s⁻¹ hs f = inf' s hs.of_inv (f ·⁻¹) :=
  inf'_image ..

/--
lemma `image_op_inv` / 引理 `image_op_inv`

English:
lemma image_op_inv
  given: (s : Finset α)
  statement: s⁻¹.image op = (s.image op)⁻¹
  proof: image_comm op_inv

@[to_additive]

中文:
引理 image_op_inv
  条件: (s : 有限集 α)
  结论: s⁻¹.像 op = (s.像 op)⁻¹
  证明: image_comm op_inv

@[to_additive]
-/
@[to_additive] lemma image_op_inv (s : Finset α) : s⁻¹.image op = (s.image op)⁻¹ :=
  image_comm op_inv

@[to_additive]
/--
lemma `map_op_inv` / 引理 `map_op_inv`

English:
lemma map_op_inv
  given: (s : Finset α)
  statement: s⁻¹.map opEquiv.toEmbedding = (s.map opEquiv.toEmbedding)⁻¹
  proof: by
  simp [map_eq_image, image_op_inv]

中文:
引理 map_op_inv
  条件: (s : 有限集 α)
  结论: s⁻¹.map opEquiv.toEmbedding = (s.map opEquiv.toEmbedding)⁻¹
  证明: by
  simp [map_eq_image, image_op_inv]

Depends on / 依赖: image_op_inv, map_eq_image
-/
lemma map_op_inv (s : Finset α) : s⁻¹.map opEquiv.toEmbedding = (s.map opEquiv.toEmbedding)⁻¹ := by
  simp [map_eq_image, image_op_inv]

end Inv

open scoped Pointwise

section InvolutiveInv
variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

@[to_additive (attr := simp)]
/--
lemma `mem_inv'` / 引理 `mem_inv'`

English:
lemma mem_inv'
  statement: a in s⁻¹ ↔ a⁻¹ in s
  proof: by simp [mem_inv, inv_eq_iff_eq_inv]

@[to_additive (attr := simp)]

中文:
引理 mem_inv'
  结论: a in s⁻¹ ↔ a⁻¹ in s
  证明: by simp [mem_inv, inv_eq_iff_eq_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_eq_iff_eq_inv, mem_inv
-/
lemma mem_inv' : a in s⁻¹ ↔ a⁻¹ in s := by simp [mem_inv, inv_eq_iff_eq_inv]

@[to_additive (attr := simp)]
/--
theorem `inv_filter` / 定理 `inv_filter`

English:
theorem inv_filter
  given: (s : Finset α) (p : α -> Prop) [DecidablePred p]
  proof: by
  ext; simp

@[to_additive]

中文:
定理 inv_filter
  条件: (s : 有限集 α) (p : α -> 命题) [DecidablePred p]
  证明: by
  ext; simp

@[to_additive]
-/
theorem inv_filter (s : Finset α) (p : α -> Prop) [DecidablePred p] :
    ({x in s | p x} : Finset α)⁻¹ = {x in s⁻¹ | p x⁻¹} := by
  ext; simp

@[to_additive]
/--
theorem `inv_filter_univ` / 定理 `inv_filter_univ`

English:
theorem inv_filter_univ
  given: (p : α -> Prop) [Fintype α] [DecidablePred p]
  proof: by
  simp

@[to_additive (attr := simp, norm_cast)]

中文:
定理 inv_filter_univ
  条件: (p : α -> 命题) [有限类型 α] [DecidablePred p]
  证明: by
  simp

@[to_additive (attr := simp, norm_cast)]
-/
theorem inv_filter_univ (p : α -> Prop) [Fintype α] [DecidablePred p] :
    ({x | p x} : Finset α)⁻¹ = {x | p x⁻¹} := by
  simp

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (s : Finset α)
  statement: ↑s⁻¹ = (s : Set α)⁻¹
  proof: coe_image.trans Set.image_inv_eq_inv

@[to_additive (attr := simp)]

中文:
定理 coe_inv
  条件: (s : 有限集 α)
  结论: ↑s⁻¹ = (s : 集合 α)⁻¹
  证明: coe_image.trans Set.image_inv_eq_inv

@[to_additive (attr := simp)]

Depends on / 依赖: Set.image_inv_eq_inv, coe_image, coe_image.trans, image_inv_eq_inv
-/
theorem coe_inv (s : Finset α) : ↑s⁻¹ = (s : Set α)⁻¹ := coe_image.trans Set.image_inv_eq_inv

@[to_additive (attr := simp)]
/--
theorem `card_inv` / 定理 `card_inv`

English:
theorem card_inv
  given: (s : Finset α)
  statement: #s⁻¹ = #s
  proof: card_image_of_injective _ inv_injective

@[to_additive (attr := simp)]

中文:
定理 card_inv
  条件: (s : 有限集 α)
  结论: #s⁻¹ = #s
  证明: card_image_of_injective _ inv_injective

@[to_additive (attr := simp)]

Depends on / 依赖: card_image_of_injective, inv_injective
-/
theorem card_inv (s : Finset α) : #s⁻¹ = #s := card_image_of_injective _ inv_injective

@[to_additive (attr := simp)]
/--
theorem `preimage_inv` / 定理 `preimage_inv`

English:
theorem preimage_inv
  given: (s : Finset α)
  statement: s.preimage (·⁻¹) inv_injective.injOn = s⁻¹
  proof: coe_injective by rw [coe_preimage, Set.inv_preimage, coe_inv]

@[to_additive (attr := simp)]

中文:
定理 preimage_inv
  条件: (s : 有限集 α)
  结论: s.原像 (·⁻¹) inv_injective.injOn = s⁻¹
  证明: coe_injective by rw [coe_preimage, Set.inv_preimage, coe_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: Set.inv_preimage, coe_injective, coe_inv, coe_preimage, inv_preimage
-/
theorem preimage_inv (s : Finset α) : s.preimage (·⁻¹) inv_injective.injOn = s⁻¹ :=
coe_injective by rw [coe_preimage, Set.inv_preimage, coe_inv]

@[to_additive (attr := simp)]
/--
lemma `inv_univ` / 引理 `inv_univ`

English:
lemma inv_univ
  given: [Fintype α]
  statement: (univ : Finset α)⁻¹ = univ
  proof: by ext; simp

@[to_additive (attr := simp)]

中文:
引理 inv_univ
  条件: [有限类型 α]
  结论: (univ : 有限集 α)⁻¹ = univ
  证明: by ext; simp

@[to_additive (attr := simp)]
-/
lemma inv_univ [Fintype α] : (univ : Finset α)⁻¹ = univ := by ext; simp

@[to_additive (attr := simp)]
/--
lemma `inv_inter` / 引理 `inv_inter`

English:
lemma inv_inter
  given: (s t : Finset α)
  statement: (s inter t)⁻¹ = s⁻¹ inter t⁻¹
  proof: coe_injective by simp

@[to_additive (attr := simp)]

中文:
引理 inv_inter
  条件: (s t : 有限集 α)
  结论: (s inter t)⁻¹ = s⁻¹ inter t⁻¹
  证明: coe_injective by simp

@[to_additive (attr := simp)]

Depends on / 依赖: coe_injective
-/
lemma inv_inter (s t : Finset α) : (s inter t)⁻¹ = s⁻¹ inter t⁻¹ := coe_injective by simp

@[to_additive (attr := simp)]
/--
lemma `inv_product` / 引理 `inv_product`

English:
lemma inv_product
  given: [DecidableEq β] [InvolutiveInv β] (s : Finset α) (t : Finset β)
  proof: mod_cast (s : Set α).inv_prod (t : Set β)

中文:
引理 inv_product
  条件: [DecidableEq β] [InvolutiveInv β] (s : 有限集 α) (t : 有限集 β)
  证明: mod_cast (s : Set α).inv_prod (t : Set β)

Depends on / 依赖: inv_prod, mod_cast
-/
lemma inv_product [DecidableEq β] [InvolutiveInv β] (s : Finset α) (t : Finset β) :
    (s ×ˢ t)⁻¹ = s⁻¹ ×ˢ t⁻¹ := mod_cast (s : Set α).inv_prod (t : Set β)

end InvolutiveInv

open scoped Pointwise

/-! ### Finset addition/multiplication -/


section Mul

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

/-- The pointwise multiplication of finsets `s * t` and `t` is defined as `{x * y | x ∈ s, y ∈ t}`
in scope `Pointwise`. -/
@[to_additive (attr := instance_reducible)
  /-- The pointwise addition of finsets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in
  scope `Pointwise`. -/]
/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : Mul (Finset α)
  body: ⟨image₂ (· * ·)⟩

scoped[Pointwise] attribute [instance] Finset.mul Finset.add

@[to_additive]

中文:
定义 mul
  签名: : 乘法 (有限集 α)
  定义体: ⟨image₂ (· * ·)⟩

scoped[Pointwise] attribute [instance] Finset.mul Finset.add

@[to_additive]
-/
protected def mul : Mul (Finset α) :=
  ⟨image₂ (· * ·)⟩

scoped[Pointwise] attribute [instance] Finset.mul Finset.add

@[to_additive]
/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  statement: s * t = (s ×ˢ t).image fun p : α × α => p.1 * p.2
  proof: rfl

@[to_additive]

中文:
定理 mul_def
  结论: s * t = (s ×ˢ t).像 fun p : α × α => p.1 * p.2
  证明: rfl

@[to_additive]
-/
theorem mul_def : s * t = (s ×ˢ t).image fun p : α × α => p.1 * p.2 :=
  rfl

@[to_additive]
/--
theorem `image_mul_product` / 定理 `image_mul_product`

English:
theorem image_mul_product
  statement: ((s ×ˢ t).image fun x : α × α => x.fst * x.snd) = s * t
  proof: rfl

@[to_additive]

中文:
定理 image_mul_product
  结论: ((s ×ˢ t).像 fun x : α × α => x.fst * x.snd) = s * t
  证明: rfl

@[to_additive]
-/
theorem image_mul_product : ((s ×ˢ t).image fun x : α × α => x.fst * x.snd) = s * t :=
  rfl

@[to_additive]
/--
theorem `mem_mul` / 定理 `mem_mul`

English:
theorem mem_mul
  given: {x : α}
  statement: x in s * t ↔ exists y in s, exists z in t, y * z = x
  proof: mem_image₂

@[to_additive (attr := simp, norm_cast)]

中文:
定理 mem_mul
  条件: {x : α}
  结论: x in s * t ↔ 存在 y in s, 存在 z in t, y * z = x
  证明: mem_image₂

@[to_additive (attr := simp, norm_cast)]
-/
theorem mem_mul {x : α} : x in s * t ↔ exists y in s, exists z in t, y * z = x := mem_image₂

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (s t : Finset α)
  statement: (↑(s * t) : Set α) = ↑s * ↑t
  proof: coe_image₂ _ _ _

@[to_additive]

中文:
定理 coe_mul
  条件: (s t : 有限集 α)
  结论: (↑(s * t) : 集合 α) = ↑s * ↑t
  证明: coe_image₂ _ _ _

@[to_additive]
-/
theorem coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t :=
  coe_image₂ _ _ _

@[to_additive]
/--
theorem `mul_mem_mul` / 定理 `mul_mem_mul`

English:
theorem mul_mem_mul
  statement: a in s -> b in t -> a * b in s * t
  proof: mem_image₂_of_mem

@[to_additive]

中文:
定理 mul_mem_mul
  结论: a in s -> b in t -> a * b in s * t
  证明: mem_image₂_of_mem

@[to_additive]
-/
theorem mul_mem_mul : a in s -> b in t -> a * b in s * t :=
  mem_image₂_of_mem

@[to_additive]
/--
theorem `card_mul_le` / 定理 `card_mul_le`

English:
theorem card_mul_le
  statement: #(s * t) <= #s * #t
  proof: card_image₂_le _ _ _

@[to_additive]

中文:
定理 card_mul_le
  结论: #(s * t) <= #s * #t
  证明: card_image₂_le _ _ _

@[to_additive]
-/
theorem card_mul_le : #(s * t) <= #s * #t :=
  card_image₂_le _ _ _

@[to_additive]
/--
theorem `card_mul_iff` / 定理 `card_mul_iff`

English:
theorem card_mul_iff
  proof: card_image₂_iff

@[to_additive (attr := simp)]

中文:
定理 card_mul_iff
  证明: card_image₂_iff

@[to_additive (attr := simp)]
-/
theorem card_mul_iff :
    #(s * t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun p => p.1 * p.2 :=
  card_image₂_iff

@[to_additive (attr := simp)]
/--
theorem `empty_mul` / 定理 `empty_mul`

English:
theorem empty_mul
  given: (s : Finset α)
  statement: ∅ * s = ∅
  proof: image₂_empty_left

@[to_additive (attr := simp)]

中文:
定理 empty_mul
  条件: (s : 有限集 α)
  结论: ∅ * s = ∅
  证明: image₂_empty_left

@[to_additive (attr := simp)]
-/
theorem empty_mul (s : Finset α) : ∅ * s = ∅ :=
  image₂_empty_left

@[to_additive (attr := simp)]
/--
theorem `mul_empty` / 定理 `mul_empty`

English:
theorem mul_empty
  given: (s : Finset α)
  statement: s * ∅ = ∅
  proof: image₂_empty_right

@[to_additive (attr := simp)]

中文:
定理 mul_empty
  条件: (s : 有限集 α)
  结论: s * ∅ = ∅
  证明: image₂_empty_right

@[to_additive (attr := simp)]
-/
theorem mul_empty (s : Finset α) : s * ∅ = ∅ :=
  image₂_empty_right

@[to_additive (attr := simp)]
/--
theorem `mul_eq_empty` / 定理 `mul_eq_empty`

English:
theorem mul_eq_empty
  statement: s * t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: image₂_eq_empty_iff

@[to_additive (attr := simp)]

中文:
定理 mul_eq_empty
  结论: s * t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: image₂_eq_empty_iff

@[to_additive (attr := simp)]
-/
theorem mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff

@[to_additive (attr := simp)]
/--
theorem `mul_nonempty` / 定理 `mul_nonempty`

English:
theorem mul_nonempty
  statement: (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]

中文:
定理 mul_nonempty
  结论: (s * t).非空 ↔ s.非空 ∧ t.非空
  证明: image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
-/
theorem mul_nonempty : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
/--
theorem `Nonempty.mul` / 定理 `Nonempty.mul`

English:
theorem Nonempty.mul
  statement: s.Nonempty -> t.Nonempty -> (s * t).Nonempty
  proof: Nonempty.image₂

@[to_additive]

中文:
定理 非空.mul
  结论: s.非空 -> t.非空 -> (s * t).非空
  证明: Nonempty.image₂

@[to_additive]

Depends on / 依赖: Nonempty, Nonempty.image
-/
theorem Nonempty.mul : s.Nonempty -> t.Nonempty -> (s * t).Nonempty :=
  Nonempty.image₂

@[to_additive]
/--
theorem `Nonempty.of_mul_left` / 定理 `Nonempty.of_mul_left`

English:
theorem Nonempty.of_mul_left
  statement: (s * t).Nonempty -> s.Nonempty
  proof: Nonempty.of_image₂_left

@[to_additive]

中文:
定理 非空.of_mul_left
  结论: (s * t).非空 -> s.非空
  证明: Nonempty.of_image₂_left

@[to_additive]

Depends on / 依赖: Nonempty, Nonempty.of_image
-/
theorem Nonempty.of_mul_left : (s * t).Nonempty -> s.Nonempty :=
  Nonempty.of_image₂_left

@[to_additive]
/--
theorem `Nonempty.of_mul_right` / 定理 `Nonempty.of_mul_right`

English:
theorem Nonempty.of_mul_right
  statement: (s * t).Nonempty -> t.Nonempty
  proof: Nonempty.of_image₂_right

@[to_additive (attr := simp)]

中文:
定理 非空.of_mul_right
  结论: (s * t).非空 -> t.非空
  证明: Nonempty.of_image₂_right

@[to_additive (attr := simp)]

Depends on / 依赖: Nonempty, Nonempty.of_image
-/
theorem Nonempty.of_mul_right : (s * t).Nonempty -> t.Nonempty :=
  Nonempty.of_image₂_right

@[to_additive (attr := simp)]
/--
theorem `singleton_mul_singleton` / 定理 `singleton_mul_singleton`

English:
theorem singleton_mul_singleton
  given: (a b : α)
  statement: ({a} : Finset α) * {b} = {a * b}
  proof: image₂_singleton

@[to_additive]

中文:
定理 singleton_mul_singleton
  条件: (a b : α)
  结论: ({a} : 有限集 α) * {b} = {a * b}
  证明: image₂_singleton

@[to_additive]
-/
theorem singleton_mul_singleton (a b : α) : ({a} : Finset α) * {b} = {a * b} :=
  image₂_singleton

@[to_additive]
/--
theorem `mul_subset_mul` / 定理 `mul_subset_mul`

English:
theorem mul_subset_mul
  statement: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ * t₁ subseteq s₂ * t₂
  proof: image₂_subset

@[to_additive]

中文:
定理 mul_subset_mul
  结论: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ * t₁ subseteq s₂ * t₂
  证明: image₂_subset

@[to_additive]
-/
theorem mul_subset_mul : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ * t₁ subseteq s₂ * t₂ :=
  image₂_subset

@[to_additive]
/--
theorem `mul_subset_mul_left` / 定理 `mul_subset_mul_left`

English:
theorem mul_subset_mul_left
  statement: t₁ subseteq t₂ -> s * t₁ subseteq s * t₂
  proof: image₂_subset_left

@[to_additive]

中文:
定理 mul_subset_mul_left
  结论: t₁ subseteq t₂ -> s * t₁ subseteq s * t₂
  证明: image₂_subset_left

@[to_additive]
-/
theorem mul_subset_mul_left : t₁ subseteq t₂ -> s * t₁ subseteq s * t₂ :=
  image₂_subset_left

@[to_additive]
/--
theorem `mul_subset_mul_right` / 定理 `mul_subset_mul_right`

English:
theorem mul_subset_mul_right
  statement: s₁ subseteq s₂ -> s₁ * t subseteq s₂ * t
  proof: image₂_subset_right

中文:
定理 mul_subset_mul_right
  结论: s₁ subseteq s₂ -> s₁ * t subseteq s₂ * t
  证明: image₂_subset_right
-/
theorem mul_subset_mul_right : s₁ subseteq s₂ -> s₁ * t subseteq s₂ * t :=
  image₂_subset_right

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulLeftMono (Finset α)
  body: mul_subset_mul_left

中文:
实例 :
  签名: MulLeftMono (有限集 α)
  定义体: mul_subset_mul_left
-/
@[to_additive] instance : MulLeftMono (Finset α) where elim _s _t₁ _t₂ := mul_subset_mul_left
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulRightMono (Finset α)
  body: mul_subset_mul_right

@[to_additive]

中文:
实例 :
  签名: MulRightMono (有限集 α)
  定义体: mul_subset_mul_right

@[to_additive]
-/
@[to_additive] instance : MulRightMono (Finset α) where elim _t _s₁ _s₂ := mul_subset_mul_right

@[to_additive]
/--
theorem `mul_subset_iff` / 定理 `mul_subset_iff`

English:
theorem mul_subset_iff
  statement: s * t subseteq u ↔ forall x in s, forall y in t, x * y in u
  proof: image₂_subset_iff

@[to_additive]

中文:
定理 mul_subset_iff
  结论: s * t subseteq u ↔ 对任意 x in s, 对任意 y in t, x * y in u
  证明: image₂_subset_iff

@[to_additive]
-/
theorem mul_subset_iff : s * t subseteq u ↔ forall x in s, forall y in t, x * y in u :=
  image₂_subset_iff

@[to_additive]
/--
theorem `union_mul` / 定理 `union_mul`

English:
theorem union_mul
  statement: (s₁ union s₂) * t = s₁ * t union s₂ * t
  proof: image₂_union_left

@[to_additive]

中文:
定理 union_mul
  结论: (s₁ union s₂) * t = s₁ * t union s₂ * t
  证明: image₂_union_left

@[to_additive]
-/
theorem union_mul : (s₁ union s₂) * t = s₁ * t union s₂ * t :=
  image₂_union_left

@[to_additive]
/--
theorem `mul_union` / 定理 `mul_union`

English:
theorem mul_union
  statement: s * (t₁ union t₂) = s * t₁ union s * t₂
  proof: image₂_union_right

@[to_additive]

中文:
定理 mul_union
  结论: s * (t₁ union t₂) = s * t₁ union s * t₂
  证明: image₂_union_right

@[to_additive]
-/
theorem mul_union : s * (t₁ union t₂) = s * t₁ union s * t₂ :=
  image₂_union_right

@[to_additive]
/--
theorem `inter_mul_subset` / 定理 `inter_mul_subset`

English:
theorem inter_mul_subset
  statement: s₁ inter s₂ * t subseteq s₁ * t inter (s₂ * t)
  proof: image₂_inter_subset_left

@[to_additive]

中文:
定理 inter_mul_subset
  结论: s₁ inter s₂ * t subseteq s₁ * t inter (s₂ * t)
  证明: image₂_inter_subset_left

@[to_additive]
-/
theorem inter_mul_subset : s₁ inter s₂ * t subseteq s₁ * t inter (s₂ * t) :=
  image₂_inter_subset_left

@[to_additive]
/--
theorem `mul_inter_subset` / 定理 `mul_inter_subset`

English:
theorem mul_inter_subset
  statement: s * (t₁ inter t₂) subseteq s * t₁ inter (s * t₂)
  proof: image₂_inter_subset_right

@[to_additive]

中文:
定理 mul_inter_subset
  结论: s * (t₁ inter t₂) subseteq s * t₁ inter (s * t₂)
  证明: image₂_inter_subset_right

@[to_additive]
-/
theorem mul_inter_subset : s * (t₁ inter t₂) subseteq s * t₁ inter (s * t₂) :=
  image₂_inter_subset_right

@[to_additive]
/--
theorem `inter_mul_union_subset_union` / 定理 `inter_mul_union_subset_union`

English:
theorem inter_mul_union_subset_union
  statement: s₁ inter s₂ * (t₁ union t₂) subseteq s₁ * t₁ union s₂ * t₂
  proof: image₂_inter_union_subset_union

@[to_additive]

中文:
定理 inter_mul_union_subset_union
  结论: s₁ inter s₂ * (t₁ union t₂) subseteq s₁ * t₁ union s₂ * t₂
  证明: image₂_inter_union_subset_union

@[to_additive]
-/
theorem inter_mul_union_subset_union : s₁ inter s₂ * (t₁ union t₂) subseteq s₁ * t₁ union s₂ * t₂ :=
  image₂_inter_union_subset_union

@[to_additive]
/--
theorem `union_mul_inter_subset_union` / 定理 `union_mul_inter_subset_union`

English:
theorem union_mul_inter_subset_union
  statement: (s₁ union s₂) * (t₁ inter t₂) subseteq s₁ * t₁ union s₂ * t₂
  proof: image₂_union_inter_subset_union

中文:
定理 union_mul_inter_subset_union
  结论: (s₁ union s₂) * (t₁ inter t₂) subseteq s₁ * t₁ union s₂ * t₂
  证明: image₂_union_inter_subset_union
-/
theorem union_mul_inter_subset_union : (s₁ union s₂) * (t₁ inter t₂) subseteq s₁ * t₁ union s₂ * t₂ :=
  image₂_union_inter_subset_union

/-- If a finset `u` is contained in the product of two sets `s * t`, we can find two finsets `s'`,
`t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' * t'`. -/
@[to_additive
  /-- If a finset `u` is contained in the sum of two sets `s + t`, we can find two finsets
  `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' + t'`. -/]
/--
theorem `subset_mul` / 定理 `subset_mul`

English:
theorem subset_mul
  given: {s t : Set α}
  proof: subset_set_image₂

@[to_additive]

中文:
定理 subset_mul
  条件: {s t : 集合 α}
  证明: subset_set_image₂

@[to_additive]
-/
theorem subset_mul {s t : Set α} :
    ↑u subseteq s * t -> exists s' t' : Finset α, ↑s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq s' * t' :=
  subset_set_image₂

@[to_additive]
/--
theorem `image_mul` / 定理 `image_mul`

English:
theorem image_mul
  given: [DecidableEq β]
  statement: (s * t).image (f : α -> β) = s.image f * t.image f
  proof: image_image₂_distrib map_mul f

@[to_additive]

中文:
定理 image_mul
  条件: [DecidableEq β]
  结论: (s * t).像 (f : α -> β) = s.像 f * t.像 f
  证明: image_image₂_distrib map_mul f

@[to_additive]

Depends on / 依赖: map_mul
-/
theorem image_mul [DecidableEq β] : (s * t).image (f : α -> β) = s.image f * t.image f :=
image_image₂_distrib map_mul f

@[to_additive]
/--
lemma `image_op_mul` / 引理 `image_op_mul`

English:
lemma image_op_mul
  given: (s t : Finset α)
  statement: (s * t).image op = t.image op * s.image op
  proof: image_image₂_antidistrib op_mul

@[to_additive (attr := simp)]

中文:
引理 image_op_mul
  条件: (s t : 有限集 α)
  结论: (s * t).像 op = t.像 op * s.像 op
  证明: image_image₂_antidistrib op_mul

@[to_additive (attr := simp)]

Depends on / 依赖: op_mul
-/
lemma image_op_mul (s t : Finset α) : (s * t).image op = t.image op * s.image op :=
  image_image₂_antidistrib op_mul

@[to_additive (attr := simp)]
/--
lemma `product_mul_product_comm` / 引理 `product_mul_product_comm`

English:
lemma product_mul_product_comm
  given: [DecidableEq β] (s₁ s₂ : Finset α) (t₁ t₂ : Finset β)
  proof: mod_cast (s₁ : Set α).prod_mul_prod_comm s₂ (t₁ : Set β) t₂

@[to_additive]

中文:
引理 product_mul_product_comm
  条件: [DecidableEq β] (s₁ s₂ : 有限集 α) (t₁ t₂ : 有限集 β)
  证明: mod_cast (s₁ : Set α).prod_mul_prod_comm s₂ (t₁ : Set β) t₂

@[to_additive]

Depends on / 依赖: mod_cast, prod_mul_prod_comm
-/
lemma product_mul_product_comm [DecidableEq β] (s₁ s₂ : Finset α) (t₁ t₂ : Finset β) :
    (s₁ ×ˢ t₁) * (s₂ ×ˢ t₂) = (s₁ * s₂) ×ˢ (t₁ * t₂) :=
  mod_cast (s₁ : Set α).prod_mul_prod_comm s₂ (t₁ : Set β) t₂

@[to_additive]
/--
lemma `map_op_mul` / 引理 `map_op_mul`

English:
lemma map_op_mul
  given: (s t : Finset α)
  proof: by
  simp [map_eq_image, image_op_mul]

中文:
引理 map_op_mul
  条件: (s t : 有限集 α)
  证明: by
  simp [map_eq_image, image_op_mul]

Depends on / 依赖: image_op_mul, map_eq_image
-/
lemma map_op_mul (s t : Finset α) :
    (s * t).map opEquiv.toEmbedding = t.map opEquiv.toEmbedding * s.map opEquiv.toEmbedding := by
  simp [map_eq_image, image_op_mul]

/-- The singleton operation as a `MulHom`. -/
@[to_additive /-- The singleton operation as an `AddHom`. -/]
/--
Definition of `singletonMulHom` / `singletonMulHom` 的定义

English:
definition singletonMulHom
  signature: : α ->ₙ* Finset α where
  body: singleton; map_mul' _ _ := (singleton_mul_singleton _ _).symm

@[to_additive (attr := simp)]

中文:
定义 singletonMulHom
  签名: : α ->ₙ* 有限集 α where
  定义体: singleton; map_mul' _ _ := (singleton_mul_singleton _ _).symm

@[to_additive (attr := simp)]

Depends on / 依赖: map_mul, singleton, singleton_mul_singleton
-/
def singletonMulHom : α ->ₙ* Finset α where
  toFun := singleton; map_mul' _ _ := (singleton_mul_singleton _ _).symm

@[to_additive (attr := simp)]
/--
theorem `coe_singletonMulHom` / 定理 `coe_singletonMulHom`

English:
theorem coe_singletonMulHom
  statement: (singletonMulHom : α -> Finset α) = singleton
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_singletonMulHom
  结论: (singletonMulHom : α -> 有限集 α) = singleton
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_singletonMulHom : (singletonMulHom : α -> Finset α) = singleton :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `singletonMulHom_apply` / 定理 `singletonMulHom_apply`

English:
theorem singletonMulHom_apply
  given: (a : α)
  statement: singletonMulHom a = {a}
  proof: rfl

中文:
定理 singletonMulHom_apply
  条件: (a : α)
  结论: singletonMulHom a = {a}
  证明: rfl
-/
theorem singletonMulHom_apply (a : α) : singletonMulHom a = {a} :=
  rfl

/-- Lift a `MulHom` to `Finset` via `image`. -/
@[to_additive (attr := simps) /-- Lift an `AddHom` to `Finset` via `image` -/]
/--
Definition of `imageMulHom` / `imageMulHom` 的定义

English:
definition imageMulHom
  signature: [DecidableEq β]
  body: Finset.image f
  map_mul' _ _ := image_mul _

@[to_additive (attr := simp (default + 1))]

中文:
定义 imageMulHom
  签名: [DecidableEq β]
  定义体: Finset.image f
  map_mul' _ _ := image_mul _

@[to_additive (attr := simp (default + 1))]

Depends on / 依赖: Finset, Finset.image
-/
def imageMulHom [DecidableEq β] : Finset α ->ₙ* Finset β where
  toFun := Finset.image f
  map_mul' _ _ := image_mul _

@[to_additive (attr := simp (default + 1))]
/--
lemma `sup_mul_le` / 引理 `sup_mul_le`

English:
lemma sup_mul_le
  given: {β} [SemilatticeSup β] [OrderBot β] {s t : Finset α} {f : α -> β} {a : β}
  proof: sup_image₂_le

@[to_additive]

中文:
引理 sup_mul_le
  条件: {β} [SemilatticeSup β] [有底序 β] {s t : 有限集 α} {f : α -> β} {a : β}
  证明: sup_image₂_le

@[to_additive]
-/
lemma sup_mul_le {β} [SemilatticeSup β] [OrderBot β] {s t : Finset α} {f : α -> β} {a : β} :
    sup (s * t) f <= a ↔ forall x in s, forall y in t, f (x * y) <= a :=
  sup_image₂_le

@[to_additive]
/--
lemma `sup_mul_left` / 引理 `sup_mul_left`

English:
lemma sup_mul_left
  given: {β} [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α -> β)
  proof: sup_image₂_left ..

@[to_additive]

中文:
引理 sup_mul_left
  条件: {β} [SemilatticeSup β] [有底序 β] (s t : 有限集 α) (f : α -> β)
  证明: sup_image₂_left ..

@[to_additive]
-/
lemma sup_mul_left {β} [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α -> β) :
    sup (s * t) f = sup s fun x => sup t (f <| x * ·) :=
  sup_image₂_left ..

@[to_additive]
/--
lemma `sup_mul_right` / 引理 `sup_mul_right`

English:
lemma sup_mul_right
  given: {β} [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α -> β)
  proof: sup_image₂_right ..

@[to_additive (attr := simp (default + 1))]

中文:
引理 sup_mul_right
  条件: {β} [SemilatticeSup β] [有底序 β] (s t : 有限集 α) (f : α -> β)
  证明: sup_image₂_right ..

@[to_additive (attr := simp (default + 1))]
-/
lemma sup_mul_right {β} [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α -> β) :
    sup (s * t) f = sup t fun y => sup s (f <| · * y) :=
  sup_image₂_right ..

@[to_additive (attr := simp (default + 1))]
/--
lemma `le_inf_mul` / 引理 `le_inf_mul`

English:
lemma le_inf_mul
  given: {β} [SemilatticeInf β] [OrderTop β] {s t : Finset α} {f : α -> β} {a : β}
  proof: le_inf_image₂

@[to_additive]

中文:
引理 le_inf_mul
  条件: {β} [SemilatticeInf β] [有顶序 β] {s t : 有限集 α} {f : α -> β} {a : β}
  证明: le_inf_image₂

@[to_additive]
-/
lemma le_inf_mul {β} [SemilatticeInf β] [OrderTop β] {s t : Finset α} {f : α -> β} {a : β} :
    a <= inf (s * t) f ↔ forall x in s, forall y in t, a <= f (x * y) :=
  le_inf_image₂

@[to_additive]
/--
lemma `inf_mul_left` / 引理 `inf_mul_left`

English:
lemma inf_mul_left
  given: {β} [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α -> β)
  proof: inf_image₂_left ..

@[to_additive]

中文:
引理 inf_mul_left
  条件: {β} [SemilatticeInf β] [有顶序 β] (s t : 有限集 α) (f : α -> β)
  证明: inf_image₂_left ..

@[to_additive]
-/
lemma inf_mul_left {β} [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α -> β) :
    inf (s * t) f = inf s fun x => inf t (f <| x * ·) :=
  inf_image₂_left ..

@[to_additive]
/--
lemma `inf_mul_right` / 引理 `inf_mul_right`

English:
lemma inf_mul_right
  given: {β} [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α -> β)
  proof: inf_image₂_right ..

中文:
引理 inf_mul_right
  条件: {β} [SemilatticeInf β] [有顶序 β] (s t : 有限集 α) (f : α -> β)
  证明: inf_image₂_right ..
-/
lemma inf_mul_right {β} [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α -> β) :
    inf (s * t) f = inf t fun y => inf s (f <| · * y) :=
  inf_image₂_right ..

/--
See `card_le_card_mul_left` for a more convenient but less general version for types with a
left-cancellative multiplication.
-/
@[to_additive
/-- See `card_le_card_add_left` for a more convenient but less general version for types with a
left-cancellative addition. -/]
/--
lemma `card_le_card_mul_left_of_injective` / 引理 `card_le_card_mul_left_of_injective`

English:
lemma card_le_card_mul_left_of_injective
  given: (has : a in s) (ha : IsLeftRegular a)
  proof: card_le_card_image₂_left _ has ha

中文:
引理 card_le_card_mul_left_of_injective
  条件: (has : a in s) (ha : IsLeftRegular a)
  证明: card_le_card_image₂_left _ has ha
-/
lemma card_le_card_mul_left_of_injective (has : a in s) (ha : IsLeftRegular a) :
    #t <= #(s * t) :=
  card_le_card_image₂_left _ has ha

/--
See `card_le_card_mul_right` for a more convenient but less general version for types with a
right-cancellative multiplication.
-/
@[to_additive
/-- See `card_le_card_add_right` for a more convenient but less general version for types with a
right-cancellative addition. -/]
/--
lemma `card_le_card_mul_right_of_injective` / 引理 `card_le_card_mul_right_of_injective`

English:
lemma card_le_card_mul_right_of_injective
  given: (hat : a in t) (ha : IsRightRegular a)
  proof: card_le_card_image₂_right _ hat ha

中文:
引理 card_le_card_mul_right_of_injective
  条件: (hat : a in t) (ha : IsRightRegular a)
  证明: card_le_card_image₂_right _ hat ha
-/
lemma card_le_card_mul_right_of_injective (hat : a in t) (ha : IsRightRegular a) :
    #s <= #(s * t) :=
  card_le_card_image₂_right _ hat ha

end Mul

/-! ### Finset subtraction/division -/

section Div

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

/-- The pointwise division of finsets `s / t` is defined as `{x / y | x ∈ s, y ∈ t}` in locale
`Pointwise`. -/
@[to_additive (attr := instance_reducible)
  /-- The pointwise subtraction of finsets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}`
  in scope `Pointwise`. -/]
/--
Definition of `div` / `div` 的定义

English:
definition div
  signature: : Div (Finset α)
  body: ⟨image₂ (· / ·)⟩

scoped[Pointwise] attribute [instance] Finset.div Finset.sub

@[to_additive]

中文:
定义 div
  签名: : 除法 (有限集 α)
  定义体: ⟨image₂ (· / ·)⟩

scoped[Pointwise] attribute [instance] Finset.div Finset.sub

@[to_additive]
-/
protected def div : Div (Finset α) :=
  ⟨image₂ (· / ·)⟩

scoped[Pointwise] attribute [instance] Finset.div Finset.sub

@[to_additive]
/--
theorem `div_def` / 定理 `div_def`

English:
theorem div_def
  statement: s / t = (s ×ˢ t).image fun p : α × α => p.1 / p.2
  proof: rfl

@[to_additive]

中文:
定理 div_def
  结论: s / t = (s ×ˢ t).像 fun p : α × α => p.1 / p.2
  证明: rfl

@[to_additive]
-/
theorem div_def : s / t = (s ×ˢ t).image fun p : α × α => p.1 / p.2 :=
  rfl

@[to_additive]
/--
theorem `image_div_product` / 定理 `image_div_product`

English:
theorem image_div_product
  statement: ((s ×ˢ t).image fun x : α × α => x.fst / x.snd) = s / t
  proof: rfl

@[to_additive]

中文:
定理 image_div_product
  结论: ((s ×ˢ t).像 fun x : α × α => x.fst / x.snd) = s / t
  证明: rfl

@[to_additive]
-/
theorem image_div_product : ((s ×ˢ t).image fun x : α × α => x.fst / x.snd) = s / t :=
  rfl

@[to_additive]
/--
theorem `mem_div` / 定理 `mem_div`

English:
theorem mem_div
  statement: a in s / t ↔ exists b in s, exists c in t, b / c = a
  proof: mem_image₂

@[to_additive (attr := simp, norm_cast)]

中文:
定理 mem_div
  结论: a in s / t ↔ 存在 b in s, 存在 c in t, b / c = a
  证明: mem_image₂

@[to_additive (attr := simp, norm_cast)]
-/
theorem mem_div : a in s / t ↔ exists b in s, exists c in t, b / c = a :=
  mem_image₂

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: (s t : Finset α)
  statement: (↑(s / t) : Set α) = ↑s / ↑t
  proof: coe_image₂ _ _ _

@[to_additive]

中文:
定理 coe_div
  条件: (s t : 有限集 α)
  结论: (↑(s / t) : 集合 α) = ↑s / ↑t
  证明: coe_image₂ _ _ _

@[to_additive]
-/
theorem coe_div (s t : Finset α) : (↑(s / t) : Set α) = ↑s / ↑t :=
  coe_image₂ _ _ _

@[to_additive]
/--
theorem `div_mem_div` / 定理 `div_mem_div`

English:
theorem div_mem_div
  statement: a in s -> b in t -> a / b in s / t
  proof: mem_image₂_of_mem

@[to_additive]

中文:
定理 div_mem_div
  结论: a in s -> b in t -> a / b in s / t
  证明: mem_image₂_of_mem

@[to_additive]
-/
theorem div_mem_div : a in s -> b in t -> a / b in s / t :=
  mem_image₂_of_mem

@[to_additive]
/--
theorem `card_div_le` / 定理 `card_div_le`

English:
theorem card_div_le
  statement: #(s / t) <= #s * #t
  proof: card_image₂_le _ _ _

@[to_additive (attr := simp)]

中文:
定理 card_div_le
  结论: #(s / t) <= #s * #t
  证明: card_image₂_le _ _ _

@[to_additive (attr := simp)]
-/
theorem card_div_le : #(s / t) <= #s * #t :=
  card_image₂_le _ _ _

@[to_additive (attr := simp)]
/--
theorem `empty_div` / 定理 `empty_div`

English:
theorem empty_div
  given: (s : Finset α)
  statement: ∅ / s = ∅
  proof: image₂_empty_left

@[to_additive (attr := simp)]

中文:
定理 empty_div
  条件: (s : 有限集 α)
  结论: ∅ / s = ∅
  证明: image₂_empty_left

@[to_additive (attr := simp)]
-/
theorem empty_div (s : Finset α) : ∅ / s = ∅ :=
  image₂_empty_left

@[to_additive (attr := simp)]
/--
theorem `div_empty` / 定理 `div_empty`

English:
theorem div_empty
  given: (s : Finset α)
  statement: s / ∅ = ∅
  proof: image₂_empty_right

@[to_additive (attr := simp)]

中文:
定理 div_empty
  条件: (s : 有限集 α)
  结论: s / ∅ = ∅
  证明: image₂_empty_right

@[to_additive (attr := simp)]
-/
theorem div_empty (s : Finset α) : s / ∅ = ∅ :=
  image₂_empty_right

@[to_additive (attr := simp)]
/--
theorem `div_eq_empty` / 定理 `div_eq_empty`

English:
theorem div_eq_empty
  statement: s / t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: image₂_eq_empty_iff

@[to_additive (attr := simp)]

中文:
定理 div_eq_empty
  结论: s / t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: image₂_eq_empty_iff

@[to_additive (attr := simp)]
-/
theorem div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff

@[to_additive (attr := simp)]
/--
theorem `div_nonempty` / 定理 `div_nonempty`

English:
theorem div_nonempty
  statement: (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]

中文:
定理 div_nonempty
  结论: (s / t).非空 ↔ s.非空 ∧ t.非空
  证明: image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
-/
theorem div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
/--
theorem `Nonempty.div` / 定理 `Nonempty.div`

English:
theorem Nonempty.div
  statement: s.Nonempty -> t.Nonempty -> (s / t).Nonempty
  proof: Nonempty.image₂

@[to_additive]

中文:
定理 非空.div
  结论: s.非空 -> t.非空 -> (s / t).非空
  证明: Nonempty.image₂

@[to_additive]

Depends on / 依赖: Nonempty, Nonempty.image
-/
theorem Nonempty.div : s.Nonempty -> t.Nonempty -> (s / t).Nonempty :=
  Nonempty.image₂

@[to_additive]
/--
theorem `Nonempty.of_div_left` / 定理 `Nonempty.of_div_left`

English:
theorem Nonempty.of_div_left
  statement: (s / t).Nonempty -> s.Nonempty
  proof: Nonempty.of_image₂_left

@[to_additive]

中文:
定理 非空.of_div_left
  结论: (s / t).非空 -> s.非空
  证明: Nonempty.of_image₂_left

@[to_additive]

Depends on / 依赖: Nonempty, Nonempty.of_image
-/
theorem Nonempty.of_div_left : (s / t).Nonempty -> s.Nonempty :=
  Nonempty.of_image₂_left

@[to_additive]
/--
theorem `Nonempty.of_div_right` / 定理 `Nonempty.of_div_right`

English:
theorem Nonempty.of_div_right
  statement: (s / t).Nonempty -> t.Nonempty
  proof: Nonempty.of_image₂_right

@[to_additive (attr := simp)]

中文:
定理 非空.of_div_right
  结论: (s / t).非空 -> t.非空
  证明: Nonempty.of_image₂_right

@[to_additive (attr := simp)]

Depends on / 依赖: Nonempty, Nonempty.of_image
-/
theorem Nonempty.of_div_right : (s / t).Nonempty -> t.Nonempty :=
  Nonempty.of_image₂_right

@[to_additive (attr := simp)]
/--
theorem `div_singleton` / 定理 `div_singleton`

English:
theorem div_singleton
  given: (a : α)
  statement: s / {a} = s.image (· / a)
  proof: image₂_singleton_right

@[to_additive (attr := simp)]

中文:
定理 div_singleton
  条件: (a : α)
  结论: s / {a} = s.像 (· / a)
  证明: image₂_singleton_right

@[to_additive (attr := simp)]
-/
theorem div_singleton (a : α) : s / {a} = s.image (· / a) :=
  image₂_singleton_right

@[to_additive (attr := simp)]
/--
theorem `singleton_div` / 定理 `singleton_div`

English:
theorem singleton_div
  given: (a : α)
  statement: {a} / s = s.image (a / ·)
  proof: image₂_singleton_left

@[to_additive]

中文:
定理 singleton_div
  条件: (a : α)
  结论: {a} / s = s.像 (a / ·)
  证明: image₂_singleton_left

@[to_additive]
-/
theorem singleton_div (a : α) : {a} / s = s.image (a / ·) :=
  image₂_singleton_left

@[to_additive]
/--
theorem `singleton_div_singleton` / 定理 `singleton_div_singleton`

English:
theorem singleton_div_singleton
  given: (a b : α)
  statement: ({a} : Finset α) / {b} = {a / b}
  proof: image₂_singleton

@[to_additive (attr := mono, gcongr)]

中文:
定理 singleton_div_singleton
  条件: (a b : α)
  结论: ({a} : 有限集 α) / {b} = {a / b}
  证明: image₂_singleton

@[to_additive (attr := mono, gcongr)]
-/
theorem singleton_div_singleton (a b : α) : ({a} : Finset α) / {b} = {a / b} :=
  image₂_singleton

@[to_additive (attr := mono, gcongr)]
/--
theorem `div_subset_div` / 定理 `div_subset_div`

English:
theorem div_subset_div
  statement: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ / t₁ subseteq s₂ / t₂
  proof: image₂_subset

@[to_additive]

中文:
定理 div_subset_div
  结论: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ / t₁ subseteq s₂ / t₂
  证明: image₂_subset

@[to_additive]
-/
theorem div_subset_div : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ / t₁ subseteq s₂ / t₂ :=
  image₂_subset

@[to_additive]
/--
theorem `div_subset_div_left` / 定理 `div_subset_div_left`

English:
theorem div_subset_div_left
  statement: t₁ subseteq t₂ -> s / t₁ subseteq s / t₂
  proof: image₂_subset_left

@[to_additive]

中文:
定理 div_subset_div_left
  结论: t₁ subseteq t₂ -> s / t₁ subseteq s / t₂
  证明: image₂_subset_left

@[to_additive]
-/
theorem div_subset_div_left : t₁ subseteq t₂ -> s / t₁ subseteq s / t₂ :=
  image₂_subset_left

@[to_additive]
/--
theorem `div_subset_div_right` / 定理 `div_subset_div_right`

English:
theorem div_subset_div_right
  statement: s₁ subseteq s₂ -> s₁ / t subseteq s₂ / t
  proof: image₂_subset_right

@[to_additive]

中文:
定理 div_subset_div_right
  结论: s₁ subseteq s₂ -> s₁ / t subseteq s₂ / t
  证明: image₂_subset_right

@[to_additive]
-/
theorem div_subset_div_right : s₁ subseteq s₂ -> s₁ / t subseteq s₂ / t :=
  image₂_subset_right

@[to_additive]
/--
theorem `div_subset_iff` / 定理 `div_subset_iff`

English:
theorem div_subset_iff
  statement: s / t subseteq u ↔ forall x in s, forall y in t, x / y in u
  proof: image₂_subset_iff

@[to_additive]

中文:
定理 div_subset_iff
  结论: s / t subseteq u ↔ 对任意 x in s, 对任意 y in t, x / y in u
  证明: image₂_subset_iff

@[to_additive]
-/
theorem div_subset_iff : s / t subseteq u ↔ forall x in s, forall y in t, x / y in u :=
  image₂_subset_iff

@[to_additive]
/--
theorem `union_div` / 定理 `union_div`

English:
theorem union_div
  statement: (s₁ union s₂) / t = s₁ / t union s₂ / t
  proof: image₂_union_left

@[to_additive]

中文:
定理 union_div
  结论: (s₁ union s₂) / t = s₁ / t union s₂ / t
  证明: image₂_union_left

@[to_additive]
-/
theorem union_div : (s₁ union s₂) / t = s₁ / t union s₂ / t :=
  image₂_union_left

@[to_additive]
/--
theorem `div_union` / 定理 `div_union`

English:
theorem div_union
  statement: s / (t₁ union t₂) = s / t₁ union s / t₂
  proof: image₂_union_right

@[to_additive]

中文:
定理 div_union
  结论: s / (t₁ union t₂) = s / t₁ union s / t₂
  证明: image₂_union_right

@[to_additive]
-/
theorem div_union : s / (t₁ union t₂) = s / t₁ union s / t₂ :=
  image₂_union_right

@[to_additive]
/--
theorem `inter_div_subset` / 定理 `inter_div_subset`

English:
theorem inter_div_subset
  statement: s₁ inter s₂ / t subseteq s₁ / t inter (s₂ / t)
  proof: image₂_inter_subset_left

@[to_additive]

中文:
定理 inter_div_subset
  结论: s₁ inter s₂ / t subseteq s₁ / t inter (s₂ / t)
  证明: image₂_inter_subset_left

@[to_additive]
-/
theorem inter_div_subset : s₁ inter s₂ / t subseteq s₁ / t inter (s₂ / t) :=
  image₂_inter_subset_left

@[to_additive]
/--
theorem `div_inter_subset` / 定理 `div_inter_subset`

English:
theorem div_inter_subset
  statement: s / (t₁ inter t₂) subseteq s / t₁ inter (s / t₂)
  proof: image₂_inter_subset_right

@[to_additive]

中文:
定理 div_inter_subset
  结论: s / (t₁ inter t₂) subseteq s / t₁ inter (s / t₂)
  证明: image₂_inter_subset_right

@[to_additive]
-/
theorem div_inter_subset : s / (t₁ inter t₂) subseteq s / t₁ inter (s / t₂) :=
  image₂_inter_subset_right

@[to_additive]
/--
theorem `inter_div_union_subset_union` / 定理 `inter_div_union_subset_union`

English:
theorem inter_div_union_subset_union
  statement: s₁ inter s₂ / (t₁ union t₂) subseteq s₁ / t₁ union s₂ / t₂
  proof: image₂_inter_union_subset_union

@[to_additive]

中文:
定理 inter_div_union_subset_union
  结论: s₁ inter s₂ / (t₁ union t₂) subseteq s₁ / t₁ union s₂ / t₂
  证明: image₂_inter_union_subset_union

@[to_additive]
-/
theorem inter_div_union_subset_union : s₁ inter s₂ / (t₁ union t₂) subseteq s₁ / t₁ union s₂ / t₂ :=
  image₂_inter_union_subset_union

@[to_additive]
/--
theorem `union_div_inter_subset_union` / 定理 `union_div_inter_subset_union`

English:
theorem union_div_inter_subset_union
  statement: (s₁ union s₂) / (t₁ inter t₂) subseteq s₁ / t₁ union s₂ / t₂
  proof: image₂_union_inter_subset_union

中文:
定理 union_div_inter_subset_union
  结论: (s₁ union s₂) / (t₁ inter t₂) subseteq s₁ / t₁ union s₂ / t₂
  证明: image₂_union_inter_subset_union
-/
theorem union_div_inter_subset_union : (s₁ union s₂) / (t₁ inter t₂) subseteq s₁ / t₁ union s₂ / t₂ :=
  image₂_union_inter_subset_union

/-- If a finset `u` is contained in the product of two sets `s / t`, we can find two finsets `s'`,
`t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' / t'`. -/
@[to_additive
  /-- If a finset `u` is contained in the sum of two sets `s - t`, we can find two finsets
  `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' - t'`. -/]
/--
theorem `subset_div` / 定理 `subset_div`

English:
theorem subset_div
  given: {s t : Set α}
  proof: subset_set_image₂

@[to_additive (attr := simp (default + 1))]

中文:
定理 subset_div
  条件: {s t : 集合 α}
  证明: subset_set_image₂

@[to_additive (attr := simp (default + 1))]
-/
theorem subset_div {s t : Set α} :
    ↑u subseteq s / t -> exists s' t' : Finset α, ↑s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq s' / t' :=
  subset_set_image₂

@[to_additive (attr := simp (default + 1))]
/--
lemma `sup_div_le` / 引理 `sup_div_le`

English:
lemma sup_div_le
  given: [SemilatticeSup β] [OrderBot β] {s t : Finset α} {f : α -> β} {a : β}
  proof: sup_image₂_le

@[to_additive]

中文:
引理 sup_div_le
  条件: [SemilatticeSup β] [有底序 β] {s t : 有限集 α} {f : α -> β} {a : β}
  证明: sup_image₂_le

@[to_additive]
-/
lemma sup_div_le [SemilatticeSup β] [OrderBot β] {s t : Finset α} {f : α -> β} {a : β} :
    sup (s / t) f <= a ↔ forall x in s, forall y in t, f (x / y) <= a :=
  sup_image₂_le

@[to_additive]
/--
lemma `sup_div_left` / 引理 `sup_div_left`

English:
lemma sup_div_left
  given: [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α -> β)
  proof: sup_image₂_left ..

@[to_additive]

中文:
引理 sup_div_left
  条件: [SemilatticeSup β] [有底序 β] (s t : 有限集 α) (f : α -> β)
  证明: sup_image₂_left ..

@[to_additive]
-/
lemma sup_div_left [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α -> β) :
    sup (s / t) f = sup s fun x => sup t (f <| x / ·) :=
  sup_image₂_left ..

@[to_additive]
/--
lemma `sup_div_right` / 引理 `sup_div_right`

English:
lemma sup_div_right
  given: [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α -> β)
  proof: sup_image₂_right ..

@[to_additive (attr := simp (default + 1))]

中文:
引理 sup_div_right
  条件: [SemilatticeSup β] [有底序 β] (s t : 有限集 α) (f : α -> β)
  证明: sup_image₂_right ..

@[to_additive (attr := simp (default + 1))]
-/
lemma sup_div_right [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α -> β) :
    sup (s / t) f = sup t fun y => sup s (f <| · / y) :=
  sup_image₂_right ..

@[to_additive (attr := simp (default + 1))]
/--
lemma `le_inf_div` / 引理 `le_inf_div`

English:
lemma le_inf_div
  given: [SemilatticeInf β] [OrderTop β] {s t : Finset α} {f : α -> β} {a : β}
  proof: le_inf_image₂

@[to_additive]

中文:
引理 le_inf_div
  条件: [SemilatticeInf β] [有顶序 β] {s t : 有限集 α} {f : α -> β} {a : β}
  证明: le_inf_image₂

@[to_additive]
-/
lemma le_inf_div [SemilatticeInf β] [OrderTop β] {s t : Finset α} {f : α -> β} {a : β} :
    a <= inf (s / t) f ↔ forall x in s, forall y in t, a <= f (x / y) :=
  le_inf_image₂

@[to_additive]
/--
lemma `inf_div_left` / 引理 `inf_div_left`

English:
lemma inf_div_left
  given: [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α -> β)
  proof: inf_image₂_left ..

@[to_additive]

中文:
引理 inf_div_left
  条件: [SemilatticeInf β] [有顶序 β] (s t : 有限集 α) (f : α -> β)
  证明: inf_image₂_left ..

@[to_additive]
-/
lemma inf_div_left [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α -> β) :
    inf (s / t) f = inf s fun x => inf t (f <| x / ·) :=
  inf_image₂_left ..

@[to_additive]
/--
lemma `inf_div_right` / 引理 `inf_div_right`

English:
lemma inf_div_right
  given: [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α -> β)
  proof: inf_image₂_right ..

中文:
引理 inf_div_right
  条件: [SemilatticeInf β] [有顶序 β] (s t : 有限集 α) (f : α -> β)
  证明: inf_image₂_right ..
-/
lemma inf_div_right [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α -> β) :
    inf (s / t) f = inf t fun y => inf s (f <| · / y) :=
  inf_image₂_right ..

end Div

/-! ### Instances -/

section Instances

variable [DecidableEq α] [DecidableEq β]

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`Finset`. See note [pointwise nat action]. -/
@[to_additive (attr := instance_reducible)
/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `Finset`. See
note [pointwise nat action]. -/]
/--
Definition of `npow` / `npow` 的定义

English:
definition npow
  signature: [One α] [Mul α]
  body: ⟨fun s n => npowRec n s⟩

中文:
定义 npow
  签名: [幺 α] [乘法 α]
  定义体: ⟨fun s n => npowRec n s⟩
-/
protected def npow [One α] [Mul α] : Pow (Finset α) Nat :=
  ⟨fun s n => npowRec n s⟩

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `Finset`. See note [pointwise nat action]. -/
@[to_additive (attr := instance_reducible)
/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `Finset`. See note [pointwise nat action]. -/]
/--
Definition of `zpow` / `zpow` 的定义

English:
definition zpow
  signature: [One α] [Mul α] [Inv α]
  body: ⟨fun s n => zpowRec npowRec n s⟩

scoped[Pointwise] attribute [instance] Finset.nsmul Finset.npow Finset.zsmul Finset.zpow

中文:
定义 zpow
  签名: [幺 α] [乘法 α] [取逆 α]
  定义体: ⟨fun s n => zpowRec npowRec n s⟩

scoped[Pointwise] attribute [instance] Finset.nsmul Finset.npow Finset.zsmul Finset.zpow
-/
protected def zpow [One α] [Mul α] [Inv α] : Pow (Finset α) Int :=
  ⟨fun s n => zpowRec npowRec n s⟩

scoped[Pointwise] attribute [instance] Finset.nsmul Finset.npow Finset.zsmul Finset.zpow

/-- `Finset α` is a `Semigroup` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Finset α` is an `AddSemigroup` under pointwise operations if `α` is. -/]
/--
Definition of `semigroup` / `semigroup` 的定义

English:
definition semigroup
  signature: [Semigroup α]
  body: coe_injective.semigroup _ coe_mul

中文:
定义 semigroup
  签名: [半群 α]
  定义体: coe_injective.semigroup _ coe_mul
-/
protected def semigroup [Semigroup α] : Semigroup (Finset α) :=
  coe_injective.semigroup _ coe_mul

section CommSemigroup

variable [CommSemigroup α] {s t : Finset α}

/-- `Finset α` is a `CommSemigroup` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Finset α` is an `AddCommSemigroup` under pointwise operations if `α` is. -/]
/--
Definition of `commSemigroup` / `commSemigroup` 的定义

English:
definition commSemigroup
  signature: : CommSemigroup (Finset α)
  body: coe_injective.commSemigroup _ coe_mul

@[to_additive]

中文:
定义 commSemigroup
  签名: : 交换半群 (有限集 α)
  定义体: coe_injective.commSemigroup _ coe_mul

@[to_additive]
-/
protected def commSemigroup : CommSemigroup (Finset α) :=
  coe_injective.commSemigroup _ coe_mul

@[to_additive]
/--
theorem `inter_mul_union_subset` / 定理 `inter_mul_union_subset`

English:
theorem inter_mul_union_subset
  statement: s inter t * (s union t) subseteq s * t
  proof: image₂_inter_union_subset mul_comm

@[to_additive]

中文:
定理 inter_mul_union_subset
  结论: s inter t * (s union t) subseteq s * t
  证明: image₂_inter_union_subset mul_comm

@[to_additive]

Depends on / 依赖: mul_comm
-/
theorem inter_mul_union_subset : s inter t * (s union t) subseteq s * t :=
  image₂_inter_union_subset mul_comm

@[to_additive]
/--
theorem `union_mul_inter_subset` / 定理 `union_mul_inter_subset`

English:
theorem union_mul_inter_subset
  statement: (s union t) * (s inter t) subseteq s * t
  proof: image₂_union_inter_subset mul_comm

中文:
定理 union_mul_inter_subset
  结论: (s union t) * (s inter t) subseteq s * t
  证明: image₂_union_inter_subset mul_comm

Depends on / 依赖: mul_comm
-/
theorem union_mul_inter_subset : (s union t) * (s inter t) subseteq s * t :=
  image₂_union_inter_subset mul_comm

end CommSemigroup

section MulOneClass

variable [MulOneClass α]

/-- `Finset α` is a `MulOneClass` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Finset α` is an `AddZeroClass` under pointwise operations if `α` is. -/]
/--
Definition of `mulOneClass` / `mulOneClass` 的定义

English:
definition mulOneClass
  signature: : MulOneClass (Finset α)
  body: coe_injective.mulOneClass _ (coe_singleton 1) coe_mul

scoped[Pointwise] attribute [instance] Finset.semigroup Finset.addSemigroup Finset.commSemigroup
  Finset.addCommSemigroup Finset.mulOneClass Finset.addZeroClass

@[to_additive]

中文:
定义 mulOneClass
  签名: : MulOne类 (有限集 α)
  定义体: coe_injective.mulOneClass _ (coe_singleton 1) coe_mul

scoped[Pointwise] attribute [instance] Finset.semigroup Finset.addSemigroup Finset.commSemigroup
  Finset.addCommSemigroup Finset.mulOneClass Finset.addZeroClass

@[to_additive]
-/
protected def mulOneClass : MulOneClass (Finset α) :=
  coe_injective.mulOneClass _ (coe_singleton 1) coe_mul

scoped[Pointwise] attribute [instance] Finset.semigroup Finset.addSemigroup Finset.commSemigroup
  Finset.addCommSemigroup Finset.mulOneClass Finset.addZeroClass

@[to_additive]
/--
theorem `subset_mul_left` / 定理 `subset_mul_left`

English:
theorem subset_mul_left
  given: (s : Finset α) {t : Finset α} (ht : (1 : α) in t)
  statement: s subseteq s * t
  proof: fun a ha =>
  mem_mul.2 ⟨a, ha, 1, ht, mul_one _⟩

@[to_additive]

中文:
定理 subset_mul_left
  条件: (s : 有限集 α) {t : 有限集 α} (ht : (1 : α) in t)
  结论: s subseteq s * t
  证明: fun a ha =>
  mem_mul.2 ⟨a, ha, 1, ht, mul_one _⟩

@[to_additive]
-/
theorem subset_mul_left (s : Finset α) {t : Finset α} (ht : (1 : α) in t) : s subseteq s * t := fun a ha =>
  mem_mul.2 ⟨a, ha, 1, ht, mul_one _⟩

@[to_additive]
/--
theorem `subset_mul_right` / 定理 `subset_mul_right`

English:
theorem subset_mul_right
  given: {s : Finset α} (t : Finset α) (hs : (1 : α) in s)
  statement: t subseteq s * t
  proof: fun a ha =>
  mem_mul.2 ⟨1, hs, a, ha, one_mul _⟩

中文:
定理 subset_mul_right
  条件: {s : 有限集 α} (t : 有限集 α) (hs : (1 : α) in s)
  结论: t subseteq s * t
  证明: fun a ha =>
  mem_mul.2 ⟨1, hs, a, ha, one_mul _⟩
-/
theorem subset_mul_right {s : Finset α} (t : Finset α) (hs : (1 : α) in s) : t subseteq s * t := fun a ha =>
  mem_mul.2 ⟨1, hs, a, ha, one_mul _⟩

/-- The singleton operation as a `MonoidHom`. -/
@[to_additive /-- The singleton operation as an `AddMonoidHom`. -/]
/--
Definition of `singletonMonoidHom` / `singletonMonoidHom` 的定义

English:
definition singletonMonoidHom
  signature: : α ->* Finset α
  body: { singletonMulHom, singletonOneHom with }

@[to_additive (attr := simp)]

中文:
定义 singletonMonoidHom
  签名: : α ->* 有限集 α
  定义体: { singletonMulHom, singletonOneHom with }

@[to_additive (attr := simp)]

Depends on / 依赖: singletonMulHom, singletonOneHom
-/
def singletonMonoidHom : α ->* Finset α :=
  { singletonMulHom, singletonOneHom with }

@[to_additive (attr := simp)]
/--
theorem `coe_singletonMonoidHom` / 定理 `coe_singletonMonoidHom`

English:
theorem coe_singletonMonoidHom
  statement: (singletonMonoidHom : α -> Finset α) = singleton
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_singletonMonoidHom
  结论: (singletonMonoidHom : α -> 有限集 α) = singleton
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_singletonMonoidHom : (singletonMonoidHom : α -> Finset α) = singleton :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `singletonMonoidHom_apply` / 定理 `singletonMonoidHom_apply`

English:
theorem singletonMonoidHom_apply
  given: (a : α)
  statement: singletonMonoidHom a = {a}
  proof: rfl

中文:
定理 singletonMonoidHom_apply
  条件: (a : α)
  结论: singletonMonoidHom a = {a}
  证明: rfl
-/
theorem singletonMonoidHom_apply (a : α) : singletonMonoidHom a = {a} :=
  rfl

/-- The coercion from `Finset` to `Set` as a `MonoidHom`. -/
@[to_additive /-- The coercion from `Finset` to `set` as an `AddMonoidHom`. -/]
/--
Definition of `coeMonoidHom` / `coeMonoidHom` 的定义

English:
definition coeMonoidHom
  signature: : Finset α ->* Set α where
  body: (↑)
  map_one' := coe_one
  map_mul' := coe_mul

@[to_additive (attr := simp)]

中文:
定义 coeMonoidHom
  签名: : 有限集 α ->* 集合 α where
  定义体: (↑)
  map_one' := coe_one
  map_mul' := coe_mul

@[to_additive (attr := simp)]
-/
def coeMonoidHom : Finset α ->* Set α where
  toFun := (↑)
  map_one' := coe_one
  map_mul' := coe_mul

@[to_additive (attr := simp)]
/--
theorem `coe_coeMonoidHom` / 定理 `coe_coeMonoidHom`

English:
theorem coe_coeMonoidHom
  statement: (coeMonoidHom : Finset α -> Set α) = (↑)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_coeMonoidHom
  结论: (coeMonoidHom : 有限集 α -> 集合 α) = (↑)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_coeMonoidHom : (coeMonoidHom : Finset α -> Set α) = (↑) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coeMonoidHom_apply` / 定理 `coeMonoidHom_apply`

English:
theorem coeMonoidHom_apply
  given: (s : Finset α)
  statement: coeMonoidHom s = s
  proof: rfl

中文:
定理 coeMonoidHom_apply
  条件: (s : 有限集 α)
  结论: coeMonoidHom s = s
  证明: rfl
-/
theorem coeMonoidHom_apply (s : Finset α) : coeMonoidHom s = s :=
  rfl

/-- Lift a `MonoidHom` to `Finset` via `image`. -/
@[to_additive (attr := simps) /-- Lift an `add_monoid_hom` to `Finset` via `image` -/]
/--
Definition of `imageMonoidHom` / `imageMonoidHom` 的定义

English:
definition imageMonoidHom
  signature: [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β] (f : F)
  body: { imageMulHom f, imageOneHom f with }

中文:
定义 imageMonoidHom
  签名: [MulOne类 β] [函数状 F α β] [幺半群态射类 F α β] (f : F)
  定义体: { imageMulHom f, imageOneHom f with }

Depends on / 依赖: imageMulHom, imageOneHom
-/
def imageMonoidHom [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β] (f : F) :
    Finset α ->* Finset β :=
  { imageMulHom f, imageOneHom f with }

end MulOneClass

section Monoid

variable [Monoid α] {s t : Finset α} {a : α} {m n : Nat}

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (s : Finset α) (n : Nat)
  statement: ↑(s ^ n) = (s : Set α) ^ n
  proof: by
  change ↑(npowRec n s) = (s : Set α) ^ n
  induction n with
  | zero => rw [npowRec, pow_zero, coe_one]
  | succ n ih => rw [npowRec, pow_succ, coe_mul, ih]

中文:
定理 coe_pow
  条件: (s : 有限集 α) (n : 自然数)
  结论: ↑(s ^ n) = (s : 集合 α) ^ n
  证明: by
  change ↑(npowRec n s) = (s : Set α) ^ n
  induction n with
  | zero => rw [npowRec, pow_zero, coe_one]
  | succ n ih => rw [npowRec, pow_succ, coe_mul, ih]

Depends on / 依赖: coe_mul, coe_one, npowRec, pow_succ, pow_zero
-/
theorem coe_pow (s : Finset α) (n : Nat) : ↑(s ^ n) = (s : Set α) ^ n := by
  change ↑(npowRec n s) = (s : Set α) ^ n
  induction n with
  | zero => rw [npowRec, pow_zero, coe_one]
  | succ n ih => rw [npowRec, pow_succ, coe_mul, ih]

/-- `Finset α` is a `Monoid` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Finset α` is an `AddMonoid` under pointwise operations if `α` is. -/]
/--
Definition of `monoid` / `monoid` 的定义

English:
definition monoid
  signature: : Monoid (Finset α)
  body: coe_injective.monoid _ coe_one coe_mul coe_pow

scoped[Pointwise] attribute [instance] Finset.monoid Finset.addMonoid

中文:
定义 monoid
  签名: : 幺半群 (有限集 α)
  定义体: coe_injective.monoid _ coe_one coe_mul coe_pow

scoped[Pointwise] attribute [instance] Finset.monoid Finset.addMonoid
-/
protected def monoid : Monoid (Finset α) :=
  coe_injective.monoid _ coe_one coe_mul coe_pow

scoped[Pointwise] attribute [instance] Finset.monoid Finset.addMonoid

-- `Finset.pow_left_monotone` doesn't exist since it would syntactically be a special case of
-- `pow_left_mono`

@[to_additive]
/--
lemma `pow_right_monotone` / 引理 `pow_right_monotone`

English:
lemma pow_right_monotone
  given: (hs : 1 in s)
  statement: Monotone (s ^ ·)
  proof: pow_right_monotone one_subset.2 hs

@[to_additive]

中文:
引理 pow_right_monotone
  条件: (hs : 1 in s)
  结论: 递增 (s ^ ·)
  证明: pow_right_monotone one_subset.2 hs

@[to_additive]
-/
protected lemma pow_right_monotone (hs : 1 in s) : Monotone (s ^ ·) :=
pow_right_monotone one_subset.2 hs

@[to_additive]
/--
lemma `pow_subset_pow_left` / 引理 `pow_subset_pow_left`

English:
lemma pow_subset_pow_left
  given: (hst : s subseteq t)
  statement: s ^ n subseteq t ^ n
  proof: pow_left_mono n hst

@[to_additive]

中文:
引理 pow_subset_pow_left
  条件: (hst : s subseteq t)
  结论: s ^ n subseteq t ^ n
  证明: pow_left_mono n hst

@[to_additive]

Depends on / 依赖: pow_left_mono
-/
lemma pow_subset_pow_left (hst : s subseteq t) : s ^ n subseteq t ^ n := pow_left_mono n hst

@[to_additive]
/--
lemma `pow_subset_pow_right` / 引理 `pow_subset_pow_right`

English:
lemma pow_subset_pow_right
  given: (hs : 1 in s) (hmn : m <= n)
  statement: s ^ m subseteq s ^ n
  proof: Finset.pow_right_monotone hs hmn

@[to_additive (attr := gcongr)]

中文:
引理 pow_subset_pow_right
  条件: (hs : 1 in s) (hmn : m <= n)
  结论: s ^ m subseteq s ^ n
  证明: Finset.pow_right_monotone hs hmn

@[to_additive (attr := gcongr)]

Depends on / 依赖: Finset, Finset.pow_right_monotone, pow_right_monotone
-/
lemma pow_subset_pow_right (hs : 1 in s) (hmn : m <= n) : s ^ m subseteq s ^ n :=
  Finset.pow_right_monotone hs hmn

@[to_additive (attr := gcongr)]
/--
lemma `pow_subset_pow` / 引理 `pow_subset_pow`

English:
lemma pow_subset_pow
  given: (hst : s subseteq t) (ht : 1 in t) (hmn : m <= n)
  statement: s ^ m subseteq t ^ n
  proof: (pow_subset_pow_left hst).trans (pow_subset_pow_right ht hmn)

@[to_additive]

中文:
引理 pow_subset_pow
  条件: (hst : s subseteq t) (ht : 1 in t) (hmn : m <= n)
  结论: s ^ m subseteq t ^ n
  证明: (pow_subset_pow_left hst).trans (pow_subset_pow_right ht hmn)

@[to_additive]

Depends on / 依赖: pow_subset_pow_left, pow_subset_pow_right
-/
lemma pow_subset_pow (hst : s subseteq t) (ht : 1 in t) (hmn : m <= n) : s ^ m subseteq t ^ n :=
  (pow_subset_pow_left hst).trans (pow_subset_pow_right ht hmn)

@[to_additive]
/--
lemma `subset_pow` / 引理 `subset_pow`

English:
lemma subset_pow
  given: (hs : 1 in s) (hn : n != 0)
  statement: s subseteq s ^ n
  proof: by
simpa using pow_subset_pow_right hs Nat.one_le_iff_ne_zero.2 hn

@[to_additive]

中文:
引理 subset_pow
  条件: (hs : 1 in s) (hn : n != 0)
  结论: s subseteq s ^ n
  证明: by
simpa using pow_subset_pow_right hs Nat.one_le_iff_ne_zero.2 hn

@[to_additive]

Depends on / 依赖: Nat.one_le_iff_ne_zero, one_le_iff_ne_zero, pow_subset_pow_right
-/
lemma subset_pow (hs : 1 in s) (hn : n != 0) : s subseteq s ^ n := by
simpa using pow_subset_pow_right hs Nat.one_le_iff_ne_zero.2 hn

@[to_additive]
/--
lemma `pow_subset_pow_mul_of_sq_subset_mul` / 引理 `pow_subset_pow_mul_of_sq_subset_mul`

English:
lemma pow_subset_pow_mul_of_sq_subset_mul
  given: (hst : s ^ 2 subseteq t * s) (hn : n != 0)
  proof: pow_le_pow_mul_of_sq_le_mul hst hn

@[to_additive (attr := simp) nsmul_empty]

中文:
引理 pow_subset_pow_mul_of_sq_subset_mul
  条件: (hst : s ^ 2 subseteq t * s) (hn : n != 0)
  证明: pow_le_pow_mul_of_sq_le_mul hst hn

@[to_additive (attr := simp) nsmul_empty]

Depends on / 依赖: pow_le_pow_mul_of_sq_le_mul
-/
lemma pow_subset_pow_mul_of_sq_subset_mul (hst : s ^ 2 subseteq t * s) (hn : n != 0) :
    s ^ n subseteq t ^ (n - 1) * s := pow_le_pow_mul_of_sq_le_mul hst hn

@[to_additive (attr := simp) nsmul_empty]
/--
lemma `empty_pow` / 引理 `empty_pow`

English:
lemma empty_pow
  given: (hn : n != 0)
  statement: (∅ : Finset α) ^ n = ∅
  proof: match n with | n + 1 => by simp [pow_succ]

@[to_additive]

中文:
引理 empty_pow
  条件: (hn : n != 0)
  结论: (∅ : 有限集 α) ^ n = ∅
  证明: match n with | n + 1 => by simp [pow_succ]

@[to_additive]

Depends on / 依赖: pow_succ
-/
lemma empty_pow (hn : n != 0) : (∅ : Finset α) ^ n = ∅ := match n with | n + 1 => by simp [pow_succ]

@[to_additive]
/--
lemma `Nonempty.pow` / 引理 `Nonempty.pow`

English:
lemma Nonempty.pow
  given: (hs : s.Nonempty)
  statement: forall {n}, (s ^ n).Nonempty

中文:
引理 非空.pow
  条件: (hs : s.非空)
  结论: 对任意 {n}, (s ^ n).非空
-/
lemma Nonempty.pow (hs : s.Nonempty) : forall {n}, (s ^ n).Nonempty
  | 0 => by simp
  | n + 1 => by rw [pow_succ]; exact hs.pow.mul hs

/--
lemma `pow_eq_empty` / 引理 `pow_eq_empty`

English:
lemma pow_eq_empty
  statement: s ^ n = ∅ ↔ s = ∅ ∧ n != 0
  proof: by
  constructor
  · contrapose! +distrib
    rintro (hs | rfl)
    · exact hs.pow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_pow hn

@[to_additive (attr := simp) nsmul_singleton]

中文:
引理 pow_eq_empty
  结论: s ^ n = ∅ ↔ s = ∅ ∧ n != 0
  证明: by
  constructor
  · contrapose! +distrib
    rintro (hs | rfl)
    · exact hs.pow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_pow hn

@[to_additive (attr := simp) nsmul_singleton]
-/
@[to_additive (attr := simp)] lemma pow_eq_empty : s ^ n = ∅ ↔ s = ∅ ∧ n != 0 := by
  constructor
  · contrapose! +distrib
    rintro (hs | rfl)
    · exact hs.pow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_pow hn

@[to_additive (attr := simp) nsmul_singleton]
/--
lemma `singleton_pow` / 引理 `singleton_pow`

English:
lemma singleton_pow
  given: (a : α)
  statement: forall n, ({a} : Finset α) ^ n = {a ^ n}

中文:
引理 singleton_pow
  条件: (a : α)
  结论: 对任意 n, ({a} : 有限集 α) ^ n = {a ^ n}
-/
lemma singleton_pow (a : α) : forall n, ({a} : Finset α) ^ n = {a ^ n}
  | 0 => by simp [singleton_one]
  | n + 1 => by simp [pow_succ, singleton_pow _ n]

/--
lemma `pow_mem_pow` / 引理 `pow_mem_pow`

English:
lemma pow_mem_pow
  given: (ha : a in s)
  statement: a ^ n in s ^ n
  proof: by
  simpa using pow_subset_pow_left (singleton_subset_iff.2 ha)

中文:
引理 pow_mem_pow
  条件: (ha : a in s)
  结论: a ^ n in s ^ n
  证明: by
  simpa using pow_subset_pow_left (singleton_subset_iff.2 ha)
-/
@[to_additive] lemma pow_mem_pow (ha : a in s) : a ^ n in s ^ n := by
  simpa using pow_subset_pow_left (singleton_subset_iff.2 ha)

/--
lemma `one_mem_pow` / 引理 `one_mem_pow`

English:
lemma one_mem_pow
  given: (hs : 1 in s)
  statement: 1 in s ^ n
  proof: by simpa using pow_mem_pow hs

@[to_additive]

中文:
引理 one_mem_pow
  条件: (hs : 1 in s)
  结论: 1 in s ^ n
  证明: by simpa using pow_mem_pow hs

@[to_additive]
-/
@[to_additive] lemma one_mem_pow (hs : 1 in s) : 1 in s ^ n := by simpa using pow_mem_pow hs

@[to_additive]
/--
lemma `inter_pow_subset` / 引理 `inter_pow_subset`

English:
lemma inter_pow_subset
  statement: (s inter t) ^ n subseteq s ^ n inter t ^ n
  proof: by apply subset_inter <;> gcongr <;> simp

@[to_additive (attr := simp, norm_cast)]

中文:
引理 inter_pow_subset
  结论: (s inter t) ^ n subseteq s ^ n inter t ^ n
  证明: by apply subset_inter <;> gcongr <;> simp

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: subset_inter
-/
lemma inter_pow_subset : (s inter t) ^ n subseteq s ^ n inter t ^ n := by apply subset_inter <;> gcongr <;> simp

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_list_prod` / 定理 `coe_list_prod`

English:
theorem coe_list_prod
  given: (s : List (Finset α))
  statement: (↑s.prod : Set α) = (s.map (↑)).prod
  proof: map_list_prod (coeMonoidHom : Finset α ->* Set α) _

@[to_additive]

中文:
定理 coe_list_prod
  条件: (s : 列表 (有限集 α))
  结论: (↑s.乘积 : 集合 α) = (s.map (↑)).乘积
  证明: map_list_prod (coeMonoidHom : Finset α ->* Set α) _

@[to_additive]

Depends on / 依赖: Finset, coeMonoidHom, map_list_prod
-/
theorem coe_list_prod (s : List (Finset α)) : (↑s.prod : Set α) = (s.map (↑)).prod :=
  map_list_prod (coeMonoidHom : Finset α ->* Set α) _

@[to_additive]
/--
theorem `mem_prod_list_ofFn` / 定理 `mem_prod_list_ofFn`

English:
theorem mem_prod_list_ofFn
  given: {a : α} {s : Fin n -> Finset α}
  proof: by
  rw [← mem_coe]; rw [coe_list_prod]; rw [List.map_ofFn]; rw [Set.mem_prod_list_ofFn]
  rfl

@[to_additive]

中文:
定理 mem_prod_list_ofFn
  条件: {a : α} {s : 有限集 n -> 有限集 α}
  证明: by
  rw [← mem_coe]; rw [coe_list_prod]; rw [List.map_ofFn]; rw [Set.mem_prod_list_ofFn]
  rfl

@[to_additive]

Depends on / 依赖: List.map_ofFn, Set.mem_prod_list_ofFn, coe_list_prod, map_ofFn, mem_coe, mem_prod_list_ofFn
-/
theorem mem_prod_list_ofFn {a : α} {s : Fin n -> Finset α} :
    a in (List.ofFn s).prod ↔ exists f : forall i : Fin n, s i, (List.ofFn fun i => (f i : α)).prod = a := by
  rw [← mem_coe]; rw [coe_list_prod]; rw [List.map_ofFn]; rw [Set.mem_prod_list_ofFn]
  rfl

@[to_additive]
/--
theorem `mem_pow` / 定理 `mem_pow`

English:
theorem mem_pow
  given: {a : α} {n : Nat}
  proof: by
  simp [← mem_coe (s := s ^ n), coe_pow, Set.mem_pow]

@[to_additive]

中文:
定理 mem_pow
  条件: {a : α} {n : 自然数}
  证明: by
  simp [← mem_coe (s := s ^ n), coe_pow, Set.mem_pow]

@[to_additive]

Depends on / 依赖: Set.mem_pow, coe_pow, mem_coe, mem_pow
-/
theorem mem_pow {a : α} {n : Nat} :
    a in s ^ n ↔ exists f : Fin n -> s, (List.ofFn fun i => ↑(f i)).prod = a := by
  simp [← mem_coe (s := s ^ n), coe_pow, Set.mem_pow]

@[to_additive]
/--
lemma `card_pow_le` / 引理 `card_pow_le`

English:
lemma card_pow_le
  statement: forall {n}, #(s ^ n) <= #s ^ n

中文:
引理 card_pow_le
  结论: 对任意 {n}, #(s ^ n) <= #s ^ n
-/
lemma card_pow_le : forall {n}, #(s ^ n) <= #s ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ, pow_succ]; refine card_mul_le.trans (by gcongr; exact card_pow_le)

@[to_additive]
/--
theorem `mul_univ_of_one_mem` / 定理 `mul_univ_of_one_mem`

English:
theorem mul_univ_of_one_mem
  given: [Fintype α] (hs : (1 : α) in s)
  statement: s * univ = univ
  proof: eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, hs, _, mem_univ _, one_mul _⟩

@[to_additive]

中文:
定理 mul_univ_of_one_mem
  条件: [有限类型 α] (hs : (1 : α) in s)
  结论: s * univ = univ
  证明: eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, hs, _, mem_univ _, one_mul _⟩

@[to_additive]

Depends on / 依赖: eq_univ_iff_forall, mem_mul, mem_univ, one_mul
-/
theorem mul_univ_of_one_mem [Fintype α] (hs : (1 : α) in s) : s * univ = univ :=
  eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, hs, _, mem_univ _, one_mul _⟩

@[to_additive]
/--
theorem `univ_mul_of_one_mem` / 定理 `univ_mul_of_one_mem`

English:
theorem univ_mul_of_one_mem
  given: [Fintype α] (ht : (1 : α) in t)
  statement: univ * t = univ
  proof: eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, mem_univ _, _, ht, mul_one _⟩

@[to_additive (attr := simp)]

中文:
定理 univ_mul_of_one_mem
  条件: [有限类型 α] (ht : (1 : α) in t)
  结论: univ * t = univ
  证明: eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, mem_univ _, _, ht, mul_one _⟩

@[to_additive (attr := simp)]

Depends on / 依赖: eq_univ_iff_forall, mem_mul, mem_univ, mul_one
-/
theorem univ_mul_of_one_mem [Fintype α] (ht : (1 : α) in t) : univ * t = univ :=
  eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, mem_univ _, _, ht, mul_one _⟩

@[to_additive (attr := simp)]
/--
theorem `univ_mul_univ` / 定理 `univ_mul_univ`

English:
theorem univ_mul_univ
  given: [Fintype α]
  statement: (univ : Finset α) * univ = univ
  proof: mul_univ_of_one_mem mem_univ _

@[to_additive (attr := simp) nsmul_univ]

中文:
定理 univ_mul_univ
  条件: [有限类型 α]
  结论: (univ : 有限集 α) * univ = univ
  证明: mul_univ_of_one_mem mem_univ _

@[to_additive (attr := simp) nsmul_univ]

Depends on / 依赖: mem_univ, mul_univ_of_one_mem
-/
theorem univ_mul_univ [Fintype α] : (univ : Finset α) * univ = univ :=
mul_univ_of_one_mem mem_univ _

@[to_additive (attr := simp) nsmul_univ]
/--
theorem `univ_pow` / 定理 `univ_pow`

English:
theorem univ_pow
  given: [Fintype α] (hn : n != 0)
  statement: (univ : Finset α) ^ n = univ
  proof: coe_injective by rw [coe_pow, coe_univ, Set.univ_pow hn]

@[to_additive]

中文:
定理 univ_pow
  条件: [有限类型 α] (hn : n != 0)
  结论: (univ : 有限集 α) ^ n = univ
  证明: coe_injective by rw [coe_pow, coe_univ, Set.univ_pow hn]

@[to_additive]

Depends on / 依赖: Set.univ_pow, coe_injective, coe_pow, coe_univ, univ_pow
-/
theorem univ_pow [Fintype α] (hn : n != 0) : (univ : Finset α) ^ n = univ :=
coe_injective by rw [coe_pow, coe_univ, Set.univ_pow hn]

@[to_additive]
/--
theorem `_root_.IsUnit.finset` / 定理 `_root_.IsUnit.finset`

English:
theorem _root_.IsUnit.finset
  statement: IsUnit a -> IsUnit ({a} : Finset α)
  proof: IsUnit.map (singletonMonoidHom : α ->* Finset α)

@[to_additive]

中文:
定理 _root_.是单位.finset
  结论: 是单位 a -> 是单位 ({a} : 有限集 α)
  证明: IsUnit.map (singletonMonoidHom : α ->* Finset α)

@[to_additive]
-/
protected theorem _root_.IsUnit.finset : IsUnit a -> IsUnit ({a} : Finset α) :=
  IsUnit.map (singletonMonoidHom : α ->* Finset α)

@[to_additive]
/--
lemma `image_op_pow` / 引理 `image_op_pow`

English:
lemma image_op_pow
  given: (s : Finset α)
  statement: forall n : Nat, (s ^ n).image op = s.image op ^ n

中文:
引理 image_op_pow
  条件: (s : 有限集 α)
  结论: 对任意 n : 自然数, (s ^ n).像 op = s.像 op ^ n
-/
lemma image_op_pow (s : Finset α) : forall n : Nat, (s ^ n).image op = s.image op ^ n
  | 0 => by simp [singleton_one]
  | n + 1 => by rw [pow_succ, pow_succ', image_op_mul, image_op_pow]

@[to_additive]
/--
lemma `map_op_pow` / 引理 `map_op_pow`

English:
lemma map_op_pow
  given: (s : Finset α)

中文:
引理 map_op_pow
  条件: (s : 有限集 α)
-/
lemma map_op_pow (s : Finset α) :
    forall n : Nat, (s ^ n).map opEquiv.toEmbedding = s.map opEquiv.toEmbedding ^ n
  | 0 => by simp [singleton_one]
  | n + 1 => by rw [pow_succ, pow_succ', map_op_mul, map_op_pow]

@[to_additive]
/--
lemma `product_pow` / 引理 `product_pow`

English:
lemma product_pow
  given: [Monoid β] (s : Finset α) (t : Finset β)
  statement: forall n, (s ×ˢ t) ^ n = (s ^ n) ×ˢ (t ^ n)

中文:
引理 product_pow
  条件: [幺半群 β] (s : 有限集 α) (t : 有限集 β)
  结论: 对任意 n, (s ×ˢ t) ^ n = (s ^ n) ×ˢ (t ^ n)
-/
lemma product_pow [Monoid β] (s : Finset α) (t : Finset β) : forall n, (s ×ˢ t) ^ n = (s ^ n) ×ˢ (t ^ n)
  | 0 => by simp
  | n + 1 => by simp [pow_succ, product_pow _ _ n]

end Monoid

section CommMonoid

variable [CommMonoid α]

/-- `Finset α` is a `CommMonoid` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Finset α` is an `AddCommMonoid` under pointwise operations if `α` is. -/]
/--
Definition of `commMonoid` / `commMonoid` 的定义

English:
definition commMonoid
  signature: : CommMonoid (Finset α)
  body: coe_injective.commMonoid _ coe_one coe_mul coe_pow

scoped[Pointwise] attribute [instance] Finset.commMonoid Finset.addCommMonoid

中文:
定义 commMonoid
  签名: : 交换幺半群 (有限集 α)
  定义体: coe_injective.commMonoid _ coe_one coe_mul coe_pow

scoped[Pointwise] attribute [instance] Finset.commMonoid Finset.addCommMonoid
-/
protected def commMonoid : CommMonoid (Finset α) :=
  coe_injective.commMonoid _ coe_one coe_mul coe_pow

scoped[Pointwise] attribute [instance] Finset.commMonoid Finset.addCommMonoid

end CommMonoid

section DivisionMonoid

variable [DivisionMonoid α] {s t : Finset α} {n : Int}

@[to_additive (attr := simp)]
/--
theorem `coe_zpow` / 定理 `coe_zpow`

English:
theorem coe_zpow
  given: (s : Finset α)
  statement: forall n : Int, ↑(s ^ n) = (s : Set α) ^ n

中文:
定理 coe_zpow
  条件: (s : 有限集 α)
  结论: 对任意 n : 整数, ↑(s ^ n) = (s : 集合 α) ^ n
-/
theorem coe_zpow (s : Finset α) : forall n : Int, ↑(s ^ n) = (s : Set α) ^ n
  | Int.ofNat _ => coe_pow _ _
  | Int.negSucc n => by
    refine (coe_inv _).trans ?_
    exact congr_arg Inv.inv (coe_pow _ _)

@[to_additive]
/--
theorem `mul_eq_one_iff` / 定理 `mul_eq_one_iff`

English:
theorem mul_eq_one_iff
  statement: s * t = 1 ↔ exists a b, s = {a} ∧ t = {b} ∧ a * b = 1
  proof: by
  simp_rw [← coe_inj, coe_mul, coe_one, Set.mul_eq_one_iff, coe_singleton]

中文:
定理 mul_eq_one_iff
  结论: s * t = 1 ↔ 存在 a b, s = {a} ∧ t = {b} ∧ a * b = 1
  证明: by
  simp_rw [← coe_inj, coe_mul, coe_one, Set.mul_eq_one_iff, coe_singleton]
-/
protected theorem mul_eq_one_iff : s * t = 1 ↔ exists a b, s = {a} ∧ t = {b} ∧ a * b = 1 := by
  simp_rw [← coe_inj, coe_mul, coe_one, Set.mul_eq_one_iff, coe_singleton]

/-- `Finset α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Finset α` is a subtraction monoid under pointwise operations if `α` is. -/]
/--
Definition of `divisionMonoid` / `divisionMonoid` 的定义

English:
definition divisionMonoid
  signature: : DivisionMonoid (Finset α)
  body: coe_injective.divisionMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

scoped[Pointwise] attribute [instance] Finset.divisionMonoid Finset.subtractionMonoid

@[to_additive (attr := simp)]

中文:
定义 divisionMonoid
  签名: : Division幺半群 (有限集 α)
  定义体: coe_injective.divisionMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

scoped[Pointwise] attribute [instance] Finset.divisionMonoid Finset.subtractionMonoid

@[to_additive (attr := simp)]
-/
protected def divisionMonoid : DivisionMonoid (Finset α) :=
  coe_injective.divisionMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

scoped[Pointwise] attribute [instance] Finset.divisionMonoid Finset.subtractionMonoid

@[to_additive (attr := simp)]
/--
theorem `isUnit_iff` / 定理 `isUnit_iff`

English:
theorem isUnit_iff
  statement: IsUnit s ↔ exists a, s = {a} ∧ IsUnit a
  proof: by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Finset.mul_eq_one_iff.1 u.mul_inv
    refine ⟨a, ha, ⟨a, b, h, singleton_injective ?_⟩, rfl⟩
    rw [← singleton_mul_singleton]; rw [← ha]; rw [← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.finset

@[to_additive (a

中文:
定理 isUnit_iff
  结论: 是单位 s ↔ 存在 a, s = {a} ∧ 是单位 a
  证明: by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Finset.mul_eq_one_iff.1 u.mul_inv
    refine ⟨a, ha, ⟨a, b, h, singleton_injective ?_⟩, rfl⟩
    rw [← singleton_mul_singleton]; rw [← ha]; rw [← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.finset

@[to_additive (a

Depends on / 依赖: Finset, Finset.mul_eq_one_iff, finset, ha.finset, inv_mul, mul_eq_one_iff, mul_inv, singleton_injective, singleton_mul_singleton, u.inv_mul, u.mul_inv
-/
theorem isUnit_iff : IsUnit s ↔ exists a, s = {a} ∧ IsUnit a := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Finset.mul_eq_one_iff.1 u.mul_inv
    refine ⟨a, ha, ⟨a, b, h, singleton_injective ?_⟩, rfl⟩
    rw [← singleton_mul_singleton]; rw [← ha]; rw [← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.finset

@[to_additive (attr := simp)]
/--
theorem `isUnit_coe` / 定理 `isUnit_coe`

English:
theorem isUnit_coe
  statement: IsUnit (s : Set α) ↔ IsUnit s
  proof: by
  simp_rw [isUnit_iff, Set.isUnit_iff, coe_eq_singleton]

@[to_additive (attr := simp)]

中文:
定理 isUnit_coe
  结论: 是单位 (s : 集合 α) ↔ 是单位 s
  证明: by
  simp_rw [isUnit_iff, Set.isUnit_iff, coe_eq_singleton]

@[to_additive (attr := simp)]

Depends on / 依赖: Set.isUnit_iff, coe_eq_singleton, isUnit_iff, simp_rw
-/
theorem isUnit_coe : IsUnit (s : Set α) ↔ IsUnit s := by
  simp_rw [isUnit_iff, Set.isUnit_iff, coe_eq_singleton]

@[to_additive (attr := simp)]
/--
lemma `univ_div_univ` / 引理 `univ_div_univ`

English:
lemma univ_div_univ
  given: [Fintype α]
  statement: (univ / univ : Finset α) = univ
  proof: by simp [div_eq_mul_inv]

中文:
引理 univ_div_univ
  条件: [有限类型 α]
  结论: (univ / univ : 有限集 α) = univ
  证明: by simp [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv
-/
lemma univ_div_univ [Fintype α] : (univ / univ : Finset α) = univ := by simp [div_eq_mul_inv]

/--
lemma `subset_div_left` / 引理 `subset_div_left`

English:
lemma subset_div_left
  given: (ht : 1 in t)
  statement: s subseteq s / t
  proof: by
rw [div_eq_mul_inv]; exact subset_mul_left _ by simpa

中文:
引理 subset_div_left
  条件: (ht : 1 in t)
  结论: s subseteq s / t
  证明: by
rw [div_eq_mul_inv]; exact subset_mul_left _ by simpa
-/
@[to_additive] lemma subset_div_left (ht : 1 in t) : s subseteq s / t := by
rw [div_eq_mul_inv]; exact subset_mul_left _ by simpa

/--
lemma `inv_subset_div_right` / 引理 `inv_subset_div_right`

English:
lemma inv_subset_div_right
  given: (hs : 1 in s)
  statement: t⁻¹ subseteq s / t
  proof: by
  rw [div_eq_mul_inv]; exact subset_mul_right _ hs

@[to_additive (attr := simp) zsmul_empty]

中文:
引理 inv_subset_div_right
  条件: (hs : 1 in s)
  结论: t⁻¹ subseteq s / t
  证明: by
  rw [div_eq_mul_inv]; exact subset_mul_right _ hs

@[to_additive (attr := simp) zsmul_empty]
-/
@[to_additive] lemma inv_subset_div_right (hs : 1 in s) : t⁻¹ subseteq s / t := by
  rw [div_eq_mul_inv]; exact subset_mul_right _ hs

@[to_additive (attr := simp) zsmul_empty]
/--
lemma `empty_zpow` / 引理 `empty_zpow`

English:
lemma empty_zpow
  given: (hn : n != 0)
  statement: (∅ : Finset α) ^ n = ∅
  proof: by cases n <;> simp_all

@[to_additive]

中文:
引理 empty_zpow
  条件: (hn : n != 0)
  结论: (∅ : 有限集 α) ^ n = ∅
  证明: by cases n <;> simp_all

@[to_additive]
-/
lemma empty_zpow (hn : n != 0) : (∅ : Finset α) ^ n = ∅ := by cases n <;> simp_all

@[to_additive]
/--
lemma `Nonempty.zpow` / 引理 `Nonempty.zpow`

English:
lemma Nonempty.zpow
  given: (hs : s.Nonempty)
  statement: forall {n : Int}, (s ^ n).Nonempty

中文:
引理 非空.zpow
  条件: (hs : s.非空)
  结论: 对任意 {n : 整数}, (s ^ n).非空
-/
lemma Nonempty.zpow (hs : s.Nonempty) : forall {n : Int}, (s ^ n).Nonempty
  | (n : Nat) => hs.pow
  | .negSucc n => by simpa using hs.pow

/--
lemma `zpow_eq_empty` / 引理 `zpow_eq_empty`

English:
lemma zpow_eq_empty
  statement: s ^ n = ∅ ↔ s = ∅ ∧ n != 0
  proof: by
  constructor
  · contrapose! +distrib
    rintro (hs | rfl)
    · exact hs.zpow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_zpow hn

@[to_additive (attr := simp) zsmul_singleton]

中文:
引理 zpow_eq_empty
  结论: s ^ n = ∅ ↔ s = ∅ ∧ n != 0
  证明: by
  constructor
  · contrapose! +distrib
    rintro (hs | rfl)
    · exact hs.zpow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_zpow hn

@[to_additive (attr := simp) zsmul_singleton]
-/
@[to_additive (attr := simp)] lemma zpow_eq_empty : s ^ n = ∅ ↔ s = ∅ ∧ n != 0 := by
  constructor
  · contrapose! +distrib
    rintro (hs | rfl)
    · exact hs.zpow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_zpow hn

@[to_additive (attr := simp) zsmul_singleton]
/--
lemma `singleton_zpow` / 引理 `singleton_zpow`

English:
lemma singleton_zpow
  given: (a : α) (n : Int)
  statement: ({a} : Finset α) ^ n = {a ^ n}
  proof: by cases n <;> simp

中文:
引理 singleton_zpow
  条件: (a : α) (n : 整数)
  结论: ({a} : 有限集 α) ^ n = {a ^ n}
  证明: by cases n <;> simp

Depends on / 依赖: Characteristic, H.Characteristic, H.Normal, Normal, normal_of_characteristic
-/
lemma singleton_zpow (a : α) (n : Int) : ({a} : Finset α) ^ n = {a ^ n} := by cases n <;> simp

end DivisionMonoid

/-- `Finset α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible) subtractionCommMonoid
  /-- `Finset α` is a commutative subtraction monoid under pointwise operations if `α` is. -/]
/--
Definition of `divisionCommMonoid` / `divisionCommMonoid` 的定义

English:
definition divisionCommMonoid
  signature: [DivisionCommMonoid α]
  body: coe_injective.divisionCommMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

scoped[Pointwise] attribute [instance] Finset.divisionCommMonoid Finset.subtractionCommMonoid

中文:
定义 divisionCommMonoid
  签名: [DivisionComm幺半群 α]
  定义体: coe_injective.divisionCommMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

scoped[Pointwise] attribute [instance] Finset.divisionCommMonoid Finset.subtractionCommMonoid

Depends on / 依赖: Characteristic, H.Characteristic, H.Normal, Normal, normal_of_characteristic
-/
protected def divisionCommMonoid [DivisionCommMonoid α] :
    DivisionCommMonoid (Finset α) :=
  coe_injective.divisionCommMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

scoped[Pointwise] attribute [instance] Finset.divisionCommMonoid Finset.subtractionCommMonoid
section Group

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]
variable (f : F) {s t : Finset α} {a b : α}

/-! Note that `Finset` is not a `Group` because `s / s ≠ 1` in general. -/


@[to_additive (attr := simp)]
/--
theorem `one_mem_div_iff` / 定理 `one_mem_div_iff`

English:
theorem one_mem_div_iff
  statement: (1 : α) in s / t ↔ ¬Disjoint s t
  proof: by
  rw [← mem_coe]; rw [← disjoint_coe]; rw [coe_div]; rw [Set.one_mem_div_iff]

@[to_additive (attr := simp)]

中文:
定理 one_mem_div_iff
  结论: (1 : α) in s / t ↔ ¬Disjoint s t
  证明: by
  rw [← mem_coe]; rw [← disjoint_coe]; rw [coe_div]; rw [Set.one_mem_div_iff]

@[to_additive (attr := simp)]

Depends on / 依赖: Set.one_mem_div_iff, coe_div, disjoint_coe, mem_coe, one_mem_div_iff
-/
theorem one_mem_div_iff : (1 : α) in s / t ↔ ¬Disjoint s t := by
  rw [← mem_coe]; rw [← disjoint_coe]; rw [coe_div]; rw [Set.one_mem_div_iff]

@[to_additive (attr := simp)]
/--
lemma `one_mem_inv_mul_iff` / 引理 `one_mem_inv_mul_iff`

English:
lemma one_mem_inv_mul_iff
  statement: (1 : α) in t⁻¹ * s ↔ ¬Disjoint s t
  proof: by
  aesop (add simp [not_disjoint_iff_nonempty_inter, mem_mul, mul_eq_one_iff_eq_inv,
    Finset.Nonempty])

@[to_additive]

中文:
引理 one_mem_inv_mul_iff
  结论: (1 : α) in t⁻¹ * s ↔ ¬Disjoint s t
  证明: by
  aesop (add simp [not_disjoint_iff_nonempty_inter, mem_mul, mul_eq_one_iff_eq_inv,
    Finset.Nonempty])

@[to_additive]

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty, mem_mul, mul_eq_one_iff_eq_inv, not_disjoint_iff_nonempty_inter
-/
lemma one_mem_inv_mul_iff : (1 : α) in t⁻¹ * s ↔ ¬Disjoint s t := by
  aesop (add simp [not_disjoint_iff_nonempty_inter, mem_mul, mul_eq_one_iff_eq_inv,
    Finset.Nonempty])

@[to_additive]
/--
theorem `one_notMem_div_iff` / 定理 `one_notMem_div_iff`

English:
theorem one_notMem_div_iff
  statement: (1 : α) ∉ s / t ↔ Disjoint s t
  proof: one_mem_div_iff.not_left

@[to_additive]

中文:
定理 one_notMem_div_iff
  结论: (1 : α) ∉ s / t ↔ Disjoint s t
  证明: one_mem_div_iff.not_left

@[to_additive]

Depends on / 依赖: not_left, one_mem_div_iff, one_mem_div_iff.not_left
-/
theorem one_notMem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t :=
  one_mem_div_iff.not_left

@[to_additive]
/--
lemma `one_notMem_inv_mul_iff` / 引理 `one_notMem_inv_mul_iff`

English:
lemma one_notMem_inv_mul_iff
  statement: (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t
  proof: one_mem_inv_mul_iff.not_left

@[to_additive]

中文:
引理 one_notMem_inv_mul_iff
  结论: (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t
  证明: one_mem_inv_mul_iff.not_left

@[to_additive]

Depends on / 依赖: not_left, one_mem_inv_mul_iff, one_mem_inv_mul_iff.not_left
-/
lemma one_notMem_inv_mul_iff : (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t := one_mem_inv_mul_iff.not_left

@[to_additive]
/--
theorem `Nonempty.one_mem_div` / 定理 `Nonempty.one_mem_div`

English:
theorem Nonempty.one_mem_div
  given: (h : s.Nonempty)
  statement: (1 : α) in s / s
  proof: let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, ha, a, ha, div_self' _⟩

@[to_additive]

中文:
定理 非空.one_mem_div
  条件: (h : s.非空)
  结论: (1 : α) in s / s
  证明: let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, ha, a, ha, div_self' _⟩

@[to_additive]

Depends on / 依赖: div_self, mem_div
-/
theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) in s / s :=
  let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, ha, a, ha, div_self' _⟩

@[to_additive]
/--
theorem `isUnit_singleton` / 定理 `isUnit_singleton`

English:
theorem isUnit_singleton
  given: (a : α)
  statement: IsUnit ({a} : Finset α)
  proof: (Group.isUnit a).finset

中文:
定理 isUnit_singleton
  条件: (a : α)
  结论: 是单位 ({a} : 有限集 α)
  证明: (Group.isUnit a).finset

Depends on / 依赖: Group.isUnit, finset, isUnit
-/
theorem isUnit_singleton (a : α) : IsUnit ({a} : Finset α) :=
  (Group.isUnit a).finset

/--
theorem `isUnit_iff_singleton` / 定理 `isUnit_iff_singleton`

English:
theorem isUnit_iff_singleton
  statement: IsUnit s ↔ exists a, s = {a}
  proof: by
  simp only [isUnit_iff, Group.isUnit, and_true]

@[simp]

中文:
定理 isUnit_iff_singleton
  结论: 是单位 s ↔ 存在 a, s = {a}
  证明: by
  simp only [isUnit_iff, Group.isUnit, and_true]

@[simp]

Depends on / 依赖: Group.isUnit, and_true, isUnit, isUnit_iff
-/
theorem isUnit_iff_singleton : IsUnit s ↔ exists a, s = {a} := by
  simp only [isUnit_iff, Group.isUnit, and_true]

@[simp]
/--
theorem `isUnit_iff_singleton_aux` / 定理 `isUnit_iff_singleton_aux`

English:
theorem isUnit_iff_singleton_aux
  given: {α} [Group α] {s : Finset α}
  proof: by
  simp only [Group.isUnit, and_true]

@[to_additive (attr := simp)]

中文:
定理 isUnit_iff_singleton_aux
  条件: {α} [群 α] {s : 有限集 α}
  证明: by
  simp only [Group.isUnit, and_true]

@[to_additive (attr := simp)]

Depends on / 依赖: Group.isUnit, and_true, isUnit
-/
theorem isUnit_iff_singleton_aux {α} [Group α] {s : Finset α} :
    (exists a, s = {a} ∧ IsUnit a) ↔ exists a, s = {a} := by
  simp only [Group.isUnit, and_true]

@[to_additive (attr := simp)]
/--
theorem `image_mul_left` / 定理 `image_mul_left`

English:
theorem image_mul_left
  proof: coe_injective by simp

@[to_additive (attr := simp)]

中文:
定理 image_mul_left
  证明: coe_injective by simp

@[to_additive (attr := simp)]

Depends on / 依赖: coe_injective
-/
theorem image_mul_left :
    image (fun b => a * b) t = preimage t (fun b => a⁻¹ * b) (mul_right_injective _).injOn :=
coe_injective by simp

@[to_additive (attr := simp)]
/--
theorem `image_mul_right` / 定理 `image_mul_right`

English:
theorem image_mul_right
  statement: image (· * b) t = preimage t (· * b⁻¹) (mul_left_injective _).injOn
  proof: coe_injective by simp

@[to_additive]

中文:
定理 image_mul_right
  结论: 像 (· * b) t = 原像 t (· * b⁻¹) (mul_left_injective _).injOn
  证明: coe_injective by simp

@[to_additive]

Depends on / 依赖: coe_injective
-/
theorem image_mul_right : image (· * b) t = preimage t (· * b⁻¹) (mul_left_injective _).injOn :=
coe_injective by simp

@[to_additive]
/--
theorem `image_mul_left'` / 定理 `image_mul_left'`

English:
theorem image_mul_left'
  proof: by
  simp

@[to_additive]

中文:
定理 image_mul_left'
  证明: by
  simp

@[to_additive]
-/
theorem image_mul_left' :
    image (fun b => a⁻¹ * b) t = preimage t (fun b => a * b) (mul_right_injective _).injOn := by
  simp

@[to_additive]
/--
theorem `image_mul_right'` / 定理 `image_mul_right'`

English:
theorem image_mul_right'
  proof: by simp

@[to_additive]

中文:
定理 image_mul_right'
  证明: by simp

@[to_additive]
-/
theorem image_mul_right' :
    image (· * b⁻¹) t = preimage t (· * b) (mul_left_injective _).injOn := by simp

@[to_additive]
/--
lemma `image_inv` / 引理 `image_inv`

English:
lemma image_inv
  given: (f : F) (s : Finset α)
  statement: s⁻¹.image f = (s.image f)⁻¹
  proof: image_comm (map_inv _)

中文:
引理 image_inv
  条件: (f : F) (s : 有限集 α)
  结论: s⁻¹.像 f = (s.像 f)⁻¹
  证明: image_comm (map_inv _)

Depends on / 依赖: image_comm, map_inv
-/
lemma image_inv (f : F) (s : Finset α) : s⁻¹.image f = (s.image f)⁻¹ := image_comm (map_inv _)

/--
theorem `image_div` / 定理 `image_div`

English:
theorem image_div
  statement: (s / t).image (f : α -> β) = s.image f / t.image f
  proof: image_image₂_distrib map_div f

中文:
定理 image_div
  结论: (s / t).像 (f : α -> β) = s.像 f / t.像 f
  证明: image_image₂_distrib map_div f

Depends on / 依赖: map_div
-/
theorem image_div : (s / t).image (f : α -> β) = s.image f / t.image f :=
image_image₂_distrib map_div f

end Group

end Instances

section Group

variable [Group α] {a b : α}

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_left_singleton` / 定理 `preimage_mul_left_singleton`

English:
theorem preimage_mul_left_singleton
  proof: by
  classical rw [← image_mul_left', image_singleton]

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_left_singleton
  证明: by
  classical rw [← image_mul_left', image_singleton]

@[to_additive (attr := simp)]

Depends on / 依赖: classical, image_mul_left, image_singleton
-/
theorem preimage_mul_left_singleton :
    preimage {b} (a * ·) (mul_right_injective _).injOn = {a⁻¹ * b} := by
  classical rw [← image_mul_left', image_singleton]

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_right_singleton` / 定理 `preimage_mul_right_singleton`

English:
theorem preimage_mul_right_singleton
  proof: by
  classical rw [← image_mul_right', image_singleton]

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_right_singleton
  证明: by
  classical rw [← image_mul_right', image_singleton]

@[to_additive (attr := simp)]

Depends on / 依赖: classical, image_mul_right, image_singleton
-/
theorem preimage_mul_right_singleton :
    preimage {b} (· * a) (mul_left_injective _).injOn = {b * a⁻¹} := by
  classical rw [← image_mul_right', image_singleton]

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_left_one` / 定理 `preimage_mul_left_one`

English:
theorem preimage_mul_left_one
  statement: preimage 1 (a * ·) (mul_right_injective _).injOn = {a⁻¹}
  proof: by
  classical rw [← image_mul_left', image_one, mul_one]

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_left_one
  结论: 原像 1 (a * ·) (mul_right_injective _).injOn = {a⁻¹}
  证明: by
  classical rw [← image_mul_left', image_one, mul_one]

@[to_additive (attr := simp)]

Depends on / 依赖: classical, image_mul_left, image_one, mul_one
-/
theorem preimage_mul_left_one : preimage 1 (a * ·) (mul_right_injective _).injOn = {a⁻¹} := by
  classical rw [← image_mul_left', image_one, mul_one]

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_right_one` / 定理 `preimage_mul_right_one`

English:
theorem preimage_mul_right_one
  statement: preimage 1 (· * b) (mul_left_injective _).injOn = {b⁻¹}
  proof: by
  classical rw [← image_mul_right', image_one, one_mul]

@[to_additive]

中文:
定理 preimage_mul_right_one
  结论: 原像 1 (· * b) (mul_left_injective _).injOn = {b⁻¹}
  证明: by
  classical rw [← image_mul_right', image_one, one_mul]

@[to_additive]

Depends on / 依赖: classical, image_mul_right, image_one, one_mul
-/
theorem preimage_mul_right_one : preimage 1 (· * b) (mul_left_injective _).injOn = {b⁻¹} := by
  classical rw [← image_mul_right', image_one, one_mul]

@[to_additive]
/--
theorem `preimage_mul_left_one'` / 定理 `preimage_mul_left_one'`

English:
theorem preimage_mul_left_one'
  statement: preimage 1 (a⁻¹ * ·) (mul_right_injective _).injOn = {a}
  proof: by
  rw [preimage_mul_left_one]; rw [inv_inv]

@[to_additive]

中文:
定理 preimage_mul_left_one'
  结论: 原像 1 (a⁻¹ * ·) (mul_right_injective _).injOn = {a}
  证明: by
  rw [preimage_mul_left_one]; rw [inv_inv]

@[to_additive]

Depends on / 依赖: inv_inv, preimage_mul_left_one
-/
theorem preimage_mul_left_one' : preimage 1 (a⁻¹ * ·) (mul_right_injective _).injOn = {a} := by
  rw [preimage_mul_left_one]; rw [inv_inv]

@[to_additive]
/--
theorem `preimage_mul_right_one'` / 定理 `preimage_mul_right_one'`

English:
theorem preimage_mul_right_one'
  statement: preimage 1 (· * b⁻¹) (mul_left_injective _).injOn = {b}
  proof: by
  rw [preimage_mul_right_one]; rw [inv_inv]

中文:
定理 preimage_mul_right_one'
  结论: 原像 1 (· * b⁻¹) (mul_left_injective _).injOn = {b}
  证明: by
  rw [preimage_mul_right_one]; rw [inv_inv]

Depends on / 依赖: inv_inv, preimage_mul_right_one
-/
theorem preimage_mul_right_one' : preimage 1 (· * b⁻¹) (mul_left_injective _).injOn = {b} := by
  rw [preimage_mul_right_one]; rw [inv_inv]

end Group

section Monoid
variable [DecidableEq α] [DecidableEq β] [Monoid α] [Monoid β] [FunLike F α β]

@[to_additive]
/--
lemma `image_pow_of_ne_zero` / 引理 `image_pow_of_ne_zero`

English:
lemma image_pow_of_ne_zero
  given: [MulHomClass F α β]

中文:
引理 image_pow_of_ne_zero
  条件: [乘法态射类 F α β]
-/
lemma image_pow_of_ne_zero [MulHomClass F α β] :
    forall {n}, n != 0 -> forall (f : F) (s : Finset α), (s ^ n).image f = s.image f ^ n
  | 1, _ => by simp
  | n + 2, _ => by simp [image_mul, pow_succ _ n.succ, image_pow_of_ne_zero]

@[to_additive]
/--
lemma `image_pow` / 引理 `image_pow`

English:
lemma image_pow
  given: [MonoidHomClass F α β] (f : F) (s : Finset α)
  statement: forall n, (s ^ n).image f = s.image f ^ n

中文:
引理 image_pow
  条件: [幺半群态射类 F α β] (f : F) (s : 有限集 α)
  结论: 对任意 n, (s ^ n).像 f = s.像 f ^ n
-/
lemma image_pow [MonoidHomClass F α β] (f : F) (s : Finset α) : forall n, (s ^ n).image f = s.image f ^ n
  | 0 => by simp [singleton_one]
  | n + 1 => image_pow_of_ne_zero n.succ_ne_zero ..

end Monoid

section IsLeftCancelMul

variable [Mul α] [IsLeftCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

@[to_additive]
/--
lemma `Nontrivial.mul_left` / 引理 `Nontrivial.mul_left`

English:
lemma Nontrivial.mul_left
  statement: t.Nontrivial -> s.Nonempty -> (s * t).Nontrivial
  proof: by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨c * a, mul_mem_mul hc ha, c * b, mul_mem_mul hc hb, by simpa⟩

@[to_additive]

中文:
引理 非平凡.mul_left
  结论: t.非平凡 -> s.非空 -> (s * t).非平凡
  证明: by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨c * a, mul_mem_mul hc ha, c * b, mul_mem_mul hc hb, by simpa⟩

@[to_additive]

Depends on / 依赖: mul_mem_mul
-/
lemma Nontrivial.mul_left : t.Nontrivial -> s.Nonempty -> (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨c * a, mul_mem_mul hc ha, c * b, mul_mem_mul hc hb, by simpa⟩

@[to_additive]
/--
lemma `Nontrivial.mul` / 引理 `Nontrivial.mul`

English:
lemma Nontrivial.mul
  given: (hs : s.Nontrivial) (ht : t.Nontrivial)
  statement: (s * t).Nontrivial
  proof: ht.mul_left hs.nonempty

@[to_additive (attr := simp)]

中文:
引理 非平凡.mul
  条件: (hs : s.非平凡) (ht : t.非平凡)
  结论: (s * t).非平凡
  证明: ht.mul_left hs.nonempty

@[to_additive (attr := simp)]

Depends on / 依赖: hs.nonempty, ht.mul_left, mul_left, nonempty
-/
lemma Nontrivial.mul (hs : s.Nontrivial) (ht : t.Nontrivial) : (s * t).Nontrivial :=
  ht.mul_left hs.nonempty

@[to_additive (attr := simp)]
/--
theorem `card_singleton_mul` / 定理 `card_singleton_mul`

English:
theorem card_singleton_mul
  given: (a : α) (t : Finset α)
  statement: #({a} * t) = #t
  proof: card_image₂_singleton_left _ mul_right_injective _

@[to_additive]

中文:
定理 card_singleton_mul
  条件: (a : α) (t : 有限集 α)
  结论: #({a} * t) = #t
  证明: card_image₂_singleton_left _ mul_right_injective _

@[to_additive]

Depends on / 依赖: mul_right_injective
-/
theorem card_singleton_mul (a : α) (t : Finset α) : #({a} * t) = #t :=
card_image₂_singleton_left _ mul_right_injective _

@[to_additive]
/--
theorem `singleton_mul_inter` / 定理 `singleton_mul_inter`

English:
theorem singleton_mul_inter
  given: (a : α) (s t : Finset α)
  statement: {a} * (s inter t) = {a} * s inter ({a} * t)
  proof: image₂_singleton_inter _ _ mul_right_injective _

@[to_additive]

中文:
定理 singleton_mul_inter
  条件: (a : α) (s t : 有限集 α)
  结论: {a} * (s inter t) = {a} * s inter ({a} * t)
  证明: image₂_singleton_inter _ _ mul_right_injective _

@[to_additive]

Depends on / 依赖: mul_right_injective
-/
theorem singleton_mul_inter (a : α) (s t : Finset α) : {a} * (s inter t) = {a} * s inter ({a} * t) :=
image₂_singleton_inter _ _ mul_right_injective _

@[to_additive]
/--
theorem `card_le_card_mul_left` / 定理 `card_le_card_mul_left`

English:
theorem card_le_card_mul_left
  given: {s : Finset α} (hs : s.Nonempty)
  statement: #t <= #(s * t)
  proof: have ⟨_, ha⟩ := hs; card_le_card_mul_left_of_injective ha (mul_right_injective _)

中文:
定理 card_le_card_mul_left
  条件: {s : 有限集 α} (hs : s.非空)
  结论: #t <= #(s * t)
  证明: have ⟨_, ha⟩ := hs; card_le_card_mul_left_of_injective ha (mul_right_injective _)

Depends on / 依赖: card_le_card_mul_left_of_injective, mul_right_injective
-/
theorem card_le_card_mul_left {s : Finset α} (hs : s.Nonempty) : #t <= #(s * t) :=
  have ⟨_, ha⟩ := hs; card_le_card_mul_left_of_injective ha (mul_right_injective _)

/--
The size of `s * s` is at least the size of `s`, version with left-cancellative multiplication.
See `card_le_card_mul_self'` for the version with right-cancellative multiplication.
-/
@[to_additive
/-- The size of `s + s` is at least the size of `s`, version with left-cancellative addition.
See `card_le_card_add_self'` for the version with right-cancellative addition. -/]
/--
theorem `card_le_card_mul_self` / 定理 `card_le_card_mul_self`

English:
theorem card_le_card_mul_self
  given: {s : Finset α}
  statement: #s <= #(s * s)
  proof: by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_mul_left, *]

中文:
定理 card_le_card_mul_self
  条件: {s : 有限集 α}
  结论: #s <= #(s * s)
  证明: by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_mul_left, *]

Depends on / 依赖: card_le_card_mul_left, eq_empty_or_nonempty, s.eq_empty_or_nonempty
-/
theorem card_le_card_mul_self {s : Finset α} : #s <= #(s * s) := by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_mul_left, *]

end IsLeftCancelMul

section IsRightCancelMul

variable [Mul α] [IsRightCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

@[to_additive]
/--
lemma `Nontrivial.mul_right` / 引理 `Nontrivial.mul_right`

English:
lemma Nontrivial.mul_right
  statement: s.Nontrivial -> t.Nonempty -> (s * t).Nontrivial
  proof: by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨a * c, mul_mem_mul ha hc, b * c, mul_mem_mul hb hc, by simpa⟩

@[to_additive (attr := simp)]

中文:
引理 非平凡.mul_right
  结论: s.非平凡 -> t.非空 -> (s * t).非平凡
  证明: by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨a * c, mul_mem_mul ha hc, b * c, mul_mem_mul hb hc, by simpa⟩

@[to_additive (attr := simp)]

Depends on / 依赖: mul_mem_mul
-/
lemma Nontrivial.mul_right : s.Nontrivial -> t.Nonempty -> (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨a * c, mul_mem_mul ha hc, b * c, mul_mem_mul hb hc, by simpa⟩

@[to_additive (attr := simp)]
/--
theorem `card_mul_singleton` / 定理 `card_mul_singleton`

English:
theorem card_mul_singleton
  given: (s : Finset α) (a : α)
  statement: #(s * {a}) = #s
  proof: card_image₂_singleton_right _ mul_left_injective _

@[to_additive]

中文:
定理 card_mul_singleton
  条件: (s : 有限集 α) (a : α)
  结论: #(s * {a}) = #s
  证明: card_image₂_singleton_right _ mul_left_injective _

@[to_additive]

Depends on / 依赖: mul_left_injective
-/
theorem card_mul_singleton (s : Finset α) (a : α) : #(s * {a}) = #s :=
card_image₂_singleton_right _ mul_left_injective _

@[to_additive]
/--
theorem `inter_mul_singleton` / 定理 `inter_mul_singleton`

English:
theorem inter_mul_singleton
  given: (s t : Finset α) (a : α)
  statement: s inter t * {a} = s * {a} inter (t * {a})
  proof: image₂_inter_singleton _ _ mul_left_injective _

@[to_additive]

中文:
定理 inter_mul_singleton
  条件: (s t : 有限集 α) (a : α)
  结论: s inter t * {a} = s * {a} inter (t * {a})
  证明: image₂_inter_singleton _ _ mul_left_injective _

@[to_additive]

Depends on / 依赖: mul_left_injective
-/
theorem inter_mul_singleton (s t : Finset α) (a : α) : s inter t * {a} = s * {a} inter (t * {a}) :=
image₂_inter_singleton _ _ mul_left_injective _

@[to_additive]
/--
theorem `card_le_card_mul_right` / 定理 `card_le_card_mul_right`

English:
theorem card_le_card_mul_right
  given: (ht : t.Nonempty)
  statement: #s <= #(s * t)
  proof: have ⟨_, ha⟩ := ht; card_le_card_mul_right_of_injective ha (mul_left_injective _)

中文:
定理 card_le_card_mul_right
  条件: (ht : t.非空)
  结论: #s <= #(s * t)
  证明: have ⟨_, ha⟩ := ht; card_le_card_mul_right_of_injective ha (mul_left_injective _)

Depends on / 依赖: card_le_card_mul_right_of_injective, mul_left_injective
-/
theorem card_le_card_mul_right (ht : t.Nonempty) : #s <= #(s * t) :=
  have ⟨_, ha⟩ := ht; card_le_card_mul_right_of_injective ha (mul_left_injective _)

/--
The size of `s * s` is at least the size of `s`, version with right-cancellative multiplication.
See `card_le_card_mul_self` for the version with left-cancellative multiplication.
-/
@[to_additive
/-- The size of `s + s` is at least the size of `s`, version with right-cancellative addition.
See `card_le_card_add_self` for the version with left-cancellative addition. -/]
/--
theorem `card_le_card_mul_self'` / 定理 `card_le_card_mul_self'`

English:
theorem card_le_card_mul_self'
  statement: #s <= #(s * s)
  proof: by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_mul_right, *]

中文:
定理 card_le_card_mul_self'
  结论: #s <= #(s * s)
  证明: by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_mul_right, *]

Depends on / 依赖: card_le_card_mul_right, eq_empty_or_nonempty, s.eq_empty_or_nonempty
-/
theorem card_le_card_mul_self' : #s <= #(s * s) := by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_mul_right, *]

end IsRightCancelMul

section CancelMonoid
variable [DecidableEq α] [CancelMonoid α] {s : Finset α} {m n : Nat}

@[to_additive]
/--
lemma `Nontrivial.pow` / 引理 `Nontrivial.pow`

English:
lemma Nontrivial.pow
  given: (hs : s.Nontrivial)
  statement: forall {n}, n != 0 -> (s ^ n).Nontrivial

中文:
引理 非平凡.pow
  条件: (hs : s.非平凡)
  结论: 对任意 {n}, n != 0 -> (s ^ n).非平凡
-/
lemma Nontrivial.pow (hs : s.Nontrivial) : forall {n}, n != 0 -> (s ^ n).Nontrivial
  | 1, _ => by simpa
  | n + 2, _ => by simpa [pow_succ] using (hs.pow n.succ_ne_zero).mul hs

/-- See `Finset.card_pow_mono` for a version that works for the empty set. -/
@[to_additive /-- See `Finset.card_nsmul_mono` for a version that works for the empty set. -/]
/--
lemma `Nonempty.card_pow_mono` / 引理 `Nonempty.card_pow_mono`

English:
lemma Nonempty.card_pow_mono
  given: (hs : s.Nonempty)
  statement: Monotone fun n : Nat => #(s ^ n)
  proof: monotone_nat_of_le_succ fun n => by rw [pow_succ]; exact card_le_card_mul_right hs

中文:
引理 非空.card_pow_mono
  条件: (hs : s.非空)
  结论: 递增 fun n : 自然数 => #(s ^ n)
  证明: monotone_nat_of_le_succ fun n => by rw [pow_succ]; exact card_le_card_mul_right hs
-/
protected lemma Nonempty.card_pow_mono (hs : s.Nonempty) : Monotone fun n : Nat => #(s ^ n) :=
  monotone_nat_of_le_succ fun n => by rw [pow_succ]; exact card_le_card_mul_right hs

/-- See `Finset.Nonempty.card_pow_mono` for a version that works for zero powers. -/
@[to_additive
/-- See `Finset.Nonempty.card_nsmul_mono` for a version that works for zero scalars. -/]
/--
lemma `card_pow_mono` / 引理 `card_pow_mono`

English:
lemma card_pow_mono
  given: (hm : m != 0) (hmn : m <= n)
  statement: #(s ^ m) <= #(s ^ n)
  proof: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [hm]
  · exact hs.card_pow_mono hmn

@[to_additive]

中文:
引理 card_pow_mono
  条件: (hm : m != 0) (hmn : m <= n)
  结论: #(s ^ m) <= #(s ^ n)
  证明: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [hm]
  · exact hs.card_pow_mono hmn

@[to_additive]

Depends on / 依赖: card_pow_mono, eq_empty_or_nonempty, hs.card_pow_mono, s.eq_empty_or_nonempty
-/
lemma card_pow_mono (hm : m != 0) (hmn : m <= n) : #(s ^ m) <= #(s ^ n) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [hm]
  · exact hs.card_pow_mono hmn

@[to_additive]
/--
lemma `card_le_card_pow` / 引理 `card_le_card_pow`

English:
lemma card_le_card_pow
  given: (hn : n != 0)
  statement: #s <= #(s ^ n)
  proof: by
  simpa using card_pow_mono (s := s) one_ne_zero (Nat.one_le_iff_ne_zero.2 hn)

中文:
引理 card_le_card_pow
  条件: (hn : n != 0)
  结论: #s <= #(s ^ n)
  证明: by
  simpa using card_pow_mono (s := s) one_ne_zero (Nat.one_le_iff_ne_zero.2 hn)

Depends on / 依赖: Nat.one_le_iff_ne_zero, card_pow_mono, one_le_iff_ne_zero, one_ne_zero
-/
lemma card_le_card_pow (hn : n != 0) : #s <= #(s ^ n) := by
  simpa using card_pow_mono (s := s) one_ne_zero (Nat.one_le_iff_ne_zero.2 hn)

end CancelMonoid

section Group
variable [Group α] [DecidableEq α] {s t : Finset α}

/--
lemma `card_le_card_div_left` / 引理 `card_le_card_div_left`

English:
lemma card_le_card_div_left
  given: (hs : s.Nonempty)
  statement: #t <= #(s / t)
  proof: have ⟨_, ha⟩ := hs; card_le_card_image₂_left _ ha div_right_injective

中文:
引理 card_le_card_div_left
  条件: (hs : s.非空)
  结论: #t <= #(s / t)
  证明: have ⟨_, ha⟩ := hs; card_le_card_image₂_left _ ha div_right_injective
-/
@[to_additive] lemma card_le_card_div_left (hs : s.Nonempty) : #t <= #(s / t) :=
  have ⟨_, ha⟩ := hs; card_le_card_image₂_left _ ha div_right_injective

/--
lemma `card_le_card_div_right` / 引理 `card_le_card_div_right`

English:
lemma card_le_card_div_right
  given: (ht : t.Nonempty)
  statement: #s <= #(s / t)
  proof: have ⟨_, ha⟩ := ht; card_le_card_image₂_right _ ha div_left_injective

中文:
引理 card_le_card_div_right
  条件: (ht : t.非空)
  结论: #s <= #(s / t)
  证明: have ⟨_, ha⟩ := ht; card_le_card_image₂_right _ ha div_left_injective

Depends on / 依赖: H.subgroupOf, Normal, normal_in_normalizer, normalizer, subgroupOf
-/
@[to_additive] lemma card_le_card_div_right (ht : t.Nonempty) : #s <= #(s / t) :=
  have ⟨_, ha⟩ := ht; card_le_card_image₂_right _ ha div_left_injective

/--
lemma `card_le_card_div_self` / 引理 `card_le_card_div_self`

English:
lemma card_le_card_div_self
  statement: #s <= #(s / s)
  proof: by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_div_left, *]

中文:
引理 card_le_card_div_self
  结论: #s <= #(s / s)
  证明: by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_div_left, *]
-/
@[to_additive] lemma card_le_card_div_self : #s <= #(s / s) := by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_div_left, *]

end Group

end Finset

namespace Fintype
variable {ι : Type*} {α β : ι -> Type*} [Fintype ι] [DecidableEq ι] [forall i, DecidableEq (β i)]
  [forall i, DecidableEq (α i)]

@[to_additive]
/--
lemma `piFinset_mul` / 引理 `piFinset_mul`

English:
lemma piFinset_mul
  given: [forall i, Mul (α i)] (s t : forall i, Finset (α i))
  proof: piFinset_image₂ _ _ _

@[to_additive]

中文:
引理 piFinset_mul
  条件: [对任意 i, 乘法 (α i)] (s t : 对任意 i, 有限集 (α i))
  证明: piFinset_image₂ _ _ _

@[to_additive]
-/
lemma piFinset_mul [forall i, Mul (α i)] (s t : forall i, Finset (α i)) :
    piFinset (fun i => s i * t i) = piFinset s * piFinset t := piFinset_image₂ _ _ _

@[to_additive]
/--
lemma `piFinset_div` / 引理 `piFinset_div`

English:
lemma piFinset_div
  given: [forall i, Div (α i)] (s t : forall i, Finset (α i))
  proof: piFinset_image₂ _ _ _

@[to_additive (attr := simp)]

中文:
引理 piFinset_div
  条件: [对任意 i, 除法 (α i)] (s t : 对任意 i, 有限集 (α i))
  证明: piFinset_image₂ _ _ _

@[to_additive (attr := simp)]
-/
lemma piFinset_div [forall i, Div (α i)] (s t : forall i, Finset (α i)) :
    piFinset (fun i => s i / t i) = piFinset s / piFinset t := piFinset_image₂ _ _ _

@[to_additive (attr := simp)]
/--
lemma `piFinset_inv` / 引理 `piFinset_inv`

English:
lemma piFinset_inv
  given: [forall i, Inv (α i)] (s : forall i, Finset (α i))
  proof: piFinset_image _ _

中文:
引理 piFinset_inv
  条件: [对任意 i, 取逆 (α i)] (s : 对任意 i, 有限集 (α i))
  证明: piFinset_image _ _

Depends on / 依赖: piFinset_image
-/
lemma piFinset_inv [forall i, Inv (α i)] (s : forall i, Finset (α i)) :
    piFinset (fun i => (s i)⁻¹) = (piFinset s)⁻¹ := piFinset_image _ _

end Fintype

open scoped Pointwise

namespace Set

section One

-- Redeclaring an instance for better keys
@[to_additive]
/--
Instance `instFintypeOne` / 实例 `instFintypeOne`

English:
instance instFintypeOne
  signature: [One α]
  body: Set.fintypeSingleton _

中文:
实例 instFintypeOne
  签名: [幺 α]
  定义体: Set.fintypeSingleton _

Depends on / 依赖: Set.fintypeSingleton, fintypeSingleton
-/
instance instFintypeOne [One α] : Fintype (1 : Set α) := Set.fintypeSingleton _

variable [One α]

@[to_additive (attr := simp)]
/--
theorem `toFinset_one` / 定理 `toFinset_one`

English:
theorem toFinset_one
  statement: (1 : Set α).toFinset = 1
  proof: rfl

中文:
定理 toFinset_one
  结论: (1 : 集合 α).toFinset = 1
  证明: rfl
-/
theorem toFinset_one : (1 : Set α).toFinset = 1 :=
  rfl

-- should take simp priority over `Finite.toFinset_singleton`
@[to_additive (attr := simp high)]
/--
theorem `Finite.toFinset_one` / 定理 `Finite.toFinset_one`

English:
theorem Finite.toFinset_one
  given: (h : (1 : Set α).Finite := finite_one)
  statement: h.toFinset = 1
  proof: Finite.toFinset_singleton _

中文:
定理 有限.toFinset_one
  条件: (h : (1 : 集合 α).有限 := finite_one)
  结论: h.toFinset = 1
  证明: Finite.toFinset_singleton _

Depends on / 依赖: finite_one, h.toFinset, toFinset
-/
theorem Finite.toFinset_one (h : (1 : Set α).Finite := finite_one) : h.toFinset = 1 :=
  Finite.toFinset_singleton _

end One

section Mul

variable [DecidableEq α] [Mul α] {s t : Set α}

@[to_additive (attr := simp)]
/--
theorem `toFinset_mul` / 定理 `toFinset_mul`

English:
theorem toFinset_mul
  given: (s t : Set α) [Fintype s] [Fintype t] [Fintype ↑(s * t)]
  proof: toFinset_image2 _ _ _

@[to_additive]

中文:
定理 toFinset_mul
  条件: (s t : 集合 α) [有限类型 s] [有限类型 t] [有限类型 ↑(s * t)]
  证明: toFinset_image2 _ _ _

@[to_additive]

Depends on / 依赖: toFinset_image2
-/
theorem toFinset_mul (s t : Set α) [Fintype s] [Fintype t] [Fintype ↑(s * t)] :
    (s * t).toFinset = s.toFinset * t.toFinset :=
  toFinset_image2 _ _ _

@[to_additive]
/--
theorem `Finite.toFinset_mul` / 定理 `Finite.toFinset_mul`

English:
theorem Finite.toFinset_mul
  given: (hs : s.Finite) (ht : t.Finite) (hf := hs.mul ht)
  proof: Finite.toFinset_image2 _ _ _

中文:
定理 有限.toFinset_mul
  条件: (hs : s.有限) (ht : t.有限) (hf := hs.mul ht)
  证明: Finite.toFinset_image2 _ _ _

Depends on / 依赖: hs.mul
-/
theorem Finite.toFinset_mul (hs : s.Finite) (ht : t.Finite) (hf := hs.mul ht) :
    hf.toFinset = hs.toFinset * ht.toFinset :=
  Finite.toFinset_image2 _ _ _

end Mul

end Set
