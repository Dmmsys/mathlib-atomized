/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Data.Prod.Lex

/-! # Products of ordered monoids -/

public section

assert_not_exists MonoidWithZero

namespace Prod

variable {α β : Type*}

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: α] [Preorder α] [IsOrderedMonoid α]
  body: ⟨mul_le_mul_left h.1 _, mul_le_mul_left h.2 _⟩

@[to_additive]

中文:
实例 [交换幺半群
  签名: α] [预序 α] [是Ordered幺半群 α]
  定义体: ⟨mul_le_mul_left h.1 _, mul_le_mul_left h.2 _⟩

@[to_additive]

Depends on / 依赖: mul_le_mul_left
-/
instance [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
    [CommMonoid β] [Preorder β] [IsOrderedMonoid β] : IsOrderedMonoid (α × β) where
  mul_le_mul_left _ _ h _ := ⟨mul_le_mul_left h.1 _, mul_le_mul_left h.2 _⟩

@[to_additive]
/--
Instance `instIsOrderedCancelMonoid` / 实例 `instIsOrderedCancelMonoid`

English:
instance instIsOrderedCancelMonoid
  body: { le_of_mul_le_mul_left :=
      fun _ _ _ h => ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩ }

@[to_additive]

中文:
实例 instIsOrderedCancelMonoid
  定义体: { le_of_mul_le_mul_left :=
      fun _ _ _ h => ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩ }

@[to_additive]

Depends on / 依赖: le_of_mul_le_mul_left
-/
instance instIsOrderedCancelMonoid
    [CommMonoid α] [Preorder α] [IsOrderedCancelMonoid α]
    [CommMonoid β] [Preorder β] [IsOrderedCancelMonoid β] :
    IsOrderedCancelMonoid (α × β) :=
  { le_of_mul_le_mul_left :=
      fun _ _ _ h => ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩ }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: α] [LE β] [Mul α] [Mul β] [ExistsMulOfLE α] [ExistsMulOfLE β] :
  body: ⟨fun h =>
    let ⟨c, hc⟩ := exists_mul_of_le h.1
    let ⟨d, hd⟩ := exists_mul_of_le h.2
    ⟨(c, d), Prod.ext hc hd⟩⟩

@[to_additive]

中文:
实例 [LE
  签名: α] [LE β] [乘法 α] [乘法 β] [ExistsMulOfLE α] [ExistsMulOfLE β] :
  定义体: ⟨fun h =>
    let ⟨c, hc⟩ := exists_mul_of_le h.1
    let ⟨d, hd⟩ := exists_mul_of_le h.2
    ⟨(c, d), Prod.ext hc hd⟩⟩

@[to_additive]

Depends on / 依赖: Prod.ext, exists_mul_of_le
-/
instance [LE α] [LE β] [Mul α] [Mul β] [ExistsMulOfLE α] [ExistsMulOfLE β] :
    ExistsMulOfLE (α × β) :=
  ⟨fun h =>
    let ⟨c, hc⟩ := exists_mul_of_le h.1
    let ⟨d, hd⟩ := exists_mul_of_le h.2
    ⟨(c, d), Prod.ext hc hd⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [LE α] [CanonicallyOrderedMul α]
  body: fun _ _ => le_def.mpr ⟨le_mul_self, le_mul_self⟩
  le_self_mul := fun _ _ => le_def.mpr ⟨le_self_mul, le_self_mul⟩

中文:
实例 [乘法
  签名: α] [LE α] [典范有序乘法 α]
  定义体: fun _ _ => le_def.mpr ⟨le_mul_self, le_mul_self⟩
  le_self_mul := fun _ _ => le_def.mpr ⟨le_self_mul, le_self_mul⟩

Depends on / 依赖: le_def, le_def.mpr, le_mul_self
-/
instance [Mul α] [LE α] [CanonicallyOrderedMul α]
    [Mul β] [LE β] [CanonicallyOrderedMul β] : CanonicallyOrderedMul (α × β) where
  le_mul_self := fun _ _ => le_def.mpr ⟨le_mul_self, le_mul_self⟩
  le_self_mul := fun _ _ => le_def.mpr ⟨le_self_mul, le_self_mul⟩

namespace Lex

@[to_additive]
/--
Instance `isOrderedMonoid` / 实例 `isOrderedMonoid`

English:
instance isOrderedMonoid
  signature: [CommMonoid α] [Preorder α] [MulLeftStrictMono α]
  body: (le_iff.1 hxy).elim
    (fun hxy => left _ _ <| mul_lt_mul_left hxy _)
    (fun hxy => le_iff.2 <|
      Or.inr ⟨by simp only [ofLex_mul, fst_mul, hxy.1], mul_le_mul_left hxy.2 _⟩)

@[to_additive]

中文:
实例 isOrderedMonoid
  签名: [交换幺半群 α] [预序 α] [MulLeftStrictMono α]
  定义体: (le_iff.1 hxy).elim
    (fun hxy => left _ _ <| mul_lt_mul_left hxy _)
    (fun hxy => le_iff.2 <|
      Or.inr ⟨by simp only [ofLex_mul, fst_mul, hxy.1], mul_le_mul_left hxy.2 _⟩)

@[to_additive]

Depends on / 依赖: le_iff
-/
instance isOrderedMonoid [CommMonoid α] [Preorder α] [MulLeftStrictMono α]
    [CommMonoid β] [Preorder β] [IsOrderedMonoid β] :
    IsOrderedMonoid (α ×ₗ β) where
  mul_le_mul_left _ _ hxy z := (le_iff.1 hxy).elim
    (fun hxy => left _ _ <| mul_lt_mul_left hxy _)
    (fun hxy => le_iff.2 <|
      Or.inr ⟨by simp only [ofLex_mul, fst_mul, hxy.1], mul_le_mul_left hxy.2 _⟩)

@[to_additive]
/--
Instance `isOrderedCancelMonoid` / 实例 `isOrderedCancelMonoid`

English:
instance isOrderedCancelMonoid
  signature: [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
  body: (le_iff.1 hxyz).elim
    (fun hxy => left _ _ <| lt_of_mul_lt_mul_left' hxy)
    (fun hxy => le_iff.2 <| Or.inr ⟨mul_left_cancel hxy.1, le_of_mul_le_mul_left' hxy.2⟩)

中文:
实例 isOrderedCancelMonoid
  签名: [交换幺半群 α] [偏序 α] [是OrderedCancel幺半群 α]
  定义体: (le_iff.1 hxyz).elim
    (fun hxy => left _ _ <| lt_of_mul_lt_mul_left' hxy)
    (fun hxy => le_iff.2 <| Or.inr ⟨mul_left_cancel hxy.1, le_of_mul_le_mul_left' hxy.2⟩)

Depends on / 依赖: le_iff
-/
instance isOrderedCancelMonoid [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
    [CommMonoid β] [PartialOrder β] [IsOrderedCancelMonoid β] :
    IsOrderedCancelMonoid (α ×ₗ β) where
  le_of_mul_le_mul_left _ _ _ hxyz := (le_iff.1 hxyz).elim
    (fun hxy => left _ _ <| lt_of_mul_lt_mul_left' hxy)
    (fun hxy => le_iff.2 <| Or.inr ⟨mul_left_cancel hxy.1, le_of_mul_le_mul_left' hxy.2⟩)

end Lex

end Prod
