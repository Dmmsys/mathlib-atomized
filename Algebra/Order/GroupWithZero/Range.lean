/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.GroupWithZero.Range
public import Mathlib.Algebra.Order.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.Algebra.Order.Monoid.Basic

/-! # The range of a MonoidWithZeroHom

Given a `MonoidWithZeroHom` `f : A → B` whose codomain `B` is a `LinearOrderedCommGroupWithZero`,
we provide some order properties of the `MonoidWithZeroHom.ValueGroup₀` as defined in
`Mathlib.Algebra.GroupWithZero.Range`.

-/

@[expose] public section

namespace MonoidWithZeroHom

variable {A B : Type*} [MonoidWithZero A] [LinearOrderedCommGroupWithZero B] {f : A ->*₀ B}

namespace ValueGroup₀

open WithZero

variable (f) in
/--
Definition of `orderMonoidWithZeroHom` / `orderMonoidWithZeroHom` 的定义

English:
definition orderMonoidWithZeroHom
  signature: : ValueGroup₀ f ->*₀o WithZero Bˣ where
  body: WithZero.map' (valueGroup f).subtype
.monotone monotone' := map'_strictMono (Subtype.strictMono_coe _)

中文:
定义 orderMonoidWithZeroHom
  签名: : ValueGroup₀ f ->*₀o WithZero Bˣ where
  定义体: WithZero.map' (valueGroup f).subtype
.monotone monotone' := map'_strictMono (Subtype.strictMono_coe _)

Depends on / 依赖: IsDomain, IsStrictOrderedRing, IsStrictOrderedRing.isDomain, WithZero, WithZero.map, isDomain, subtype, valueGroup
-/
def orderMonoidWithZeroHom : ValueGroup₀ f ->*₀o WithZero Bˣ where
  __ := WithZero.map' (valueGroup f).subtype
.monotone monotone' := map'_strictMono (Subtype.strictMono_coe _)

/--
lemma `monoidWithZeroHom_strictMono` / 引理 `monoidWithZeroHom_strictMono`

English:
lemma monoidWithZeroHom_strictMono
  proof: map'_strictMono (Subtype.strictMono_coe _)

中文:
引理 monoidWithZeroHom_strictMono
  证明: map'_strictMono (Subtype.strictMono_coe _)

Depends on / 依赖: Subtype, Subtype.strictMono_coe, _strictMono, strictMono_coe
-/
lemma monoidWithZeroHom_strictMono :
    StrictMono (orderMonoidWithZeroHom f) :=
  map'_strictMono (Subtype.strictMono_coe _)

/--
lemma `embedding_strictMono` / 引理 `embedding_strictMono`

English:
lemma embedding_strictMono
  statement: StrictMono (embedding (f := f))
  proof: by
  intro x y hxy
  rw [← monoidWithZeroHom_strictMono.lt_iff_lt] at hxy
  simpa using! (OrderEmbedding.lt_iff_lt (OrderIso.withZeroUnits.toOrderEmbedding)).mpr hxy

中文:
引理 embedding_strictMono
  结论: 严格递增 (embedding (f := f))
  证明: by
  intro x y hxy
  rw [← monoidWithZeroHom_strictMono.lt_iff_lt] at hxy
  simpa using! (OrderEmbedding.lt_iff_lt (OrderIso.withZeroUnits.toOrderEmbedding)).mpr hxy

Depends on / 依赖: OrderEmbedding, OrderEmbedding.lt_iff_lt, OrderIso, OrderIso.withZeroUnits.toOrderEmbedding, lt_iff_lt, monoidWithZeroHom_strictMono, monoidWithZeroHom_strictMono.lt_iff_lt, toOrderEmbedding, withZeroUnits
-/
lemma embedding_strictMono : StrictMono (embedding (f := f)) := by
  intro x y hxy
  rw [← monoidWithZeroHom_strictMono.lt_iff_lt] at hxy
  simpa using! (OrderEmbedding.lt_iff_lt (OrderIso.withZeroUnits.toOrderEmbedding)).mpr hxy

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedMonoid (ValueGroup₀ f)
  body: Function.Injective.isOrderedMonoid embedding (map_mul _) embedding_strictMono.le_iff_le

中文:
实例 :
  签名: 是Ordered幺半群 (ValueGroup₀ f)
  定义体: Function.Injective.isOrderedMonoid embedding (map_mul _) embedding_strictMono.le_iff_le

Depends on / 依赖: Function, Function.Injective.isOrderedMonoid, Injective, embedding, embedding_strictMono, embedding_strictMono.le_iff_le, isOrderedMonoid, le_iff_le, map_mul
-/
instance : IsOrderedMonoid (ValueGroup₀ f) :=
  Function.Injective.isOrderedMonoid embedding (map_mul _) embedding_strictMono.le_iff_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrderedCommGroupWithZero (ValueGroup₀ f)
  body: by simp
  mul_lt_mul_of_pos_left a ha b c hbc := by
    simp only [← (embedding_strictMono (f := f)).lt_iff_lt, map_mul] at *
    exact (mul_lt_mul_iff_of_pos_left ha).mpr hbc

中文:
实例 :
  签名: 带零LinearOrderedComm群 (ValueGroup₀ f)
  定义体: by simp
  mul_lt_mul_of_pos_left a ha b c hbc := by
    simp only [← (embedding_strictMono (f := f)).lt_iff_lt, map_mul] at *
    exact (mul_lt_mul_iff_of_pos_left ha).mpr hbc

Depends on / 依赖: embedding_strictMono, lt_iff_lt, map_mul, mul_lt_mul_iff_of_pos_left, mul_lt_mul_of_pos_left
-/
instance : LinearOrderedCommGroupWithZero (ValueGroup₀ f) where
  isBot_zero _ := by simp
  mul_lt_mul_of_pos_left a ha b c hbc := by
    simp only [← (embedding_strictMono (f := f)).lt_iff_lt, map_mul] at *
    exact (mul_lt_mul_iff_of_pos_left ha).mpr hbc

/--
lemma `embedding_unit_pos` / 引理 `embedding_unit_pos`

English:
lemma embedding_unit_pos
  given: (a : (ValueGroup₀ f)ˣ)
  proof: by
  conv_lhs => rw [← map_zero f, ← ValueGroup₀.embedding_restrict₀ (0 : A)]
  rw [embedding_strictMono.lt_iff_lt]
  simp

中文:
引理 embedding_unit_pos
  条件: (a : (ValueGroup₀ f)ˣ)
  证明: by
  conv_lhs => rw [← map_zero f, ← ValueGroup₀.embedding_restrict₀ (0 : A)]
  rw [embedding_strictMono.lt_iff_lt]
  simp

Depends on / 依赖: conv_lhs, embedding_strictMono, embedding_strictMono.lt_iff_lt, lt_iff_lt, map_zero
-/
lemma embedding_unit_pos (a : (ValueGroup₀ f)ˣ) :
    0 < embedding a.1 := by
  conv_lhs => rw [← map_zero f, ← ValueGroup₀.embedding_restrict₀ (0 : A)]
  rw [embedding_strictMono.lt_iff_lt]
  simp

/--
lemma `embedding_unit_ne_zero` / 引理 `embedding_unit_ne_zero`

English:
lemma embedding_unit_ne_zero
  given: (a : (ValueGroup₀ f)ˣ)
  proof: (embedding_unit_pos a).ne.symm

中文:
引理 embedding_unit_ne_zero
  条件: (a : (ValueGroup₀ f)ˣ)
  证明: (embedding_unit_pos a).ne.symm

Depends on / 依赖: embedding_unit_pos, ne.symm
-/
lemma embedding_unit_ne_zero (a : (ValueGroup₀ f)ˣ) :
    embedding a.1 != 0 := (embedding_unit_pos a).ne.symm

end ValueGroup₀

end MonoidWithZeroHom
