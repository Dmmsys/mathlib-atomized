/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Order.Hom.Basic

/-!

# Tropical algebraic structures

This file defines algebraic structures of the (min-)tropical numbers, up to the tropical semiring.
Some basic lemmas about conversion from the base type `R` to `Tropical R` are provided, as
well as the expected implementations of tropical addition and tropical multiplication.

## Main declarations

* `Tropical R`: The type synonym of the tropical interpretation of `R`.
    If `[LinearOrder R]`, then addition on `R` is via `min`.
* `Semiring (Tropical R)`: A `LinearOrderedAddCommMonoidWithTop R`
    induces a `Semiring (Tropical R)`. If one solely has `[LinearOrderedAddCommMonoid R]`,
    then the "tropicalization of `R`" would be `Tropical (WithTop R)`.

## Implementation notes

The tropical structure relies on `Top` and `min`. For the max-tropical numbers, use
`OrderDual R`.

Inspiration was drawn from the implementation of `Additive`/`Multiplicative`/`Opposite`,
where a type synonym is created with some barebones API, and quickly made irreducible.

Algebraic structures are provided with as few typeclass assumptions as possible, even though
most references rely on `Semiring (Tropical R)` for building up the whole theory.

## References followed

* https://arxiv.org/pdf/math/0408099.pdf
* https://www.mathenjeans.fr/sites/default/files/sujets/tropical_geometry_-_casagrande.pdf

-/

@[expose] public section

assert_not_exists Nat.instMulOneClass

universe u v

variable (R : Type u)

/--
Definition of `Tropical` / `Tropical` 的定义

English:
definition Tropical
  signature: : Type u
  body: R

中文:
定义 Tropical
  签名: : 类型u
  定义体: R
-/
def Tropical : Type u :=
  R

variable {R}

namespace Tropical

/--
Definition of `trop` / `trop` 的定义

English:
definition trop
  signature: : R -> Tropical R
  body: id

中文:
定义 trop
  签名: : R -> Tropical R
  定义体: id
-/
def trop : R -> Tropical R :=
  id

/-- Reinterpret `x : Tropical R` as an element of `R`.
See `Tropical.tropEquiv` for the equivalence. -/
@[pp_nodot]
/--
Definition of `untrop` / `untrop` 的定义

English:
definition untrop
  signature: : Tropical R -> R
  body: id

中文:
定义 untrop
  签名: : Tropical R -> R
  定义体: id
-/
def untrop : Tropical R -> R :=
  id

/--
theorem `trop_injective` / 定理 `trop_injective`

English:
theorem trop_injective
  statement: Function.Injective (trop : R -> Tropical R)
  proof: fun _ _ => id

中文:
定理 trop_injective
  结论: 函数.单射 (trop : R -> Tropical R)
  证明: fun _ _ => id
-/
theorem trop_injective : Function.Injective (trop : R -> Tropical R) := fun _ _ => id

/--
theorem `untrop_injective` / 定理 `untrop_injective`

English:
theorem untrop_injective
  statement: Function.Injective (untrop : Tropical R -> R)
  proof: fun _ _ => id

@[simp]

中文:
定理 untrop_injective
  结论: 函数.单射 (untrop : Tropical R -> R)
  证明: fun _ _ => id

@[simp]
-/
theorem untrop_injective : Function.Injective (untrop : Tropical R -> R) := fun _ _ => id

@[simp]
/--
theorem `trop_inj_iff` / 定理 `trop_inj_iff`

English:
theorem trop_inj_iff
  given: (x y : R)
  statement: trop x = trop y ↔ x = y
  proof: Iff.rfl

@[simp]

中文:
定理 trop_inj_iff
  条件: (x y : R)
  结论: trop x = trop y ↔ x = y
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem trop_inj_iff (x y : R) : trop x = trop y ↔ x = y :=
  Iff.rfl

@[simp]
/--
theorem `untrop_inj_iff` / 定理 `untrop_inj_iff`

English:
theorem untrop_inj_iff
  given: (x y : Tropical R)
  statement: untrop x = untrop y ↔ x = y
  proof: Iff.rfl

@[simp]

中文:
定理 untrop_inj_iff
  条件: (x y : Tropical R)
  结论: untrop x = untrop y ↔ x = y
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem untrop_inj_iff (x y : Tropical R) : untrop x = untrop y ↔ x = y :=
  Iff.rfl

@[simp]
/--
theorem `trop_untrop` / 定理 `trop_untrop`

English:
theorem trop_untrop
  given: (x : Tropical R)
  statement: trop (untrop x) = x
  proof: rfl

@[simp]

中文:
定理 trop_untrop
  条件: (x : Tropical R)
  结论: trop (untrop x) = x
  证明: rfl

@[simp]
-/
theorem trop_untrop (x : Tropical R) : trop (untrop x) = x :=
  rfl

@[simp]
/--
theorem `untrop_trop` / 定理 `untrop_trop`

English:
theorem untrop_trop
  given: (x : R)
  statement: untrop (trop x) = x
  proof: rfl

中文:
定理 untrop_trop
  条件: (x : R)
  结论: untrop (trop x) = x
  证明: rfl
-/
theorem untrop_trop (x : R) : untrop (trop x) = x :=
  rfl

attribute [irreducible] Tropical

/--
theorem `leftInverse_trop` / 定理 `leftInverse_trop`

English:
theorem leftInverse_trop
  statement: Function.LeftInverse (trop : R -> Tropical R) untrop
  proof: trop_untrop

中文:
定理 leftInverse_trop
  结论: 函数.左逆 (trop : R -> Tropical R) untrop
  证明: trop_untrop

Depends on / 依赖: trop_untrop
-/
theorem leftInverse_trop : Function.LeftInverse (trop : R -> Tropical R) untrop :=
  trop_untrop

/--
theorem `rightInverse_trop` / 定理 `rightInverse_trop`

English:
theorem rightInverse_trop
  statement: Function.RightInverse (trop : R -> Tropical R) untrop
  proof: untrop_trop

中文:
定理 rightInverse_trop
  结论: 函数.右逆 (trop : R -> Tropical R) untrop
  证明: untrop_trop

Depends on / 依赖: untrop_trop
-/
theorem rightInverse_trop : Function.RightInverse (trop : R -> Tropical R) untrop :=
  untrop_trop

/--
Definition of `tropEquiv` / `tropEquiv` 的定义

English:
definition tropEquiv
  signature: : R ≃ Tropical R where
  body: trop
  invFun := untrop
  left_inv := untrop_trop
  right_inv := trop_untrop

@[simp]

中文:
定义 tropEquiv
  签名: : R ≃ Tropical R where
  定义体: trop
  invFun := untrop
  left_inv := untrop_trop
  right_inv := trop_untrop

@[simp]
-/
def tropEquiv : R ≃ Tropical R where
  toFun := trop
  invFun := untrop
  left_inv := untrop_trop
  right_inv := trop_untrop

@[simp]
/--
theorem `tropEquiv_coe_fn` / 定理 `tropEquiv_coe_fn`

English:
theorem tropEquiv_coe_fn
  statement: (tropEquiv : R -> Tropical R) = trop
  proof: rfl

@[simp]

中文:
定理 tropEquiv_coe_fn
  结论: (tropEquiv : R -> Tropical R) = trop
  证明: rfl

@[simp]
-/
theorem tropEquiv_coe_fn : (tropEquiv : R -> Tropical R) = trop :=
  rfl

@[simp]
/--
theorem `tropEquiv_symm_coe_fn` / 定理 `tropEquiv_symm_coe_fn`

English:
theorem tropEquiv_symm_coe_fn
  statement: (tropEquiv.symm : Tropical R -> R) = untrop
  proof: rfl

中文:
定理 tropEquiv_symm_coe_fn
  结论: (tropEquiv.symm : Tropical R -> R) = untrop
  证明: rfl
-/
theorem tropEquiv_symm_coe_fn : (tropEquiv.symm : Tropical R -> R) = untrop :=
  rfl

/--
theorem `trop_eq_iff_eq_untrop` / 定理 `trop_eq_iff_eq_untrop`

English:
theorem trop_eq_iff_eq_untrop
  given: {x : R} {y}
  statement: trop x = y ↔ x = untrop y
  proof: tropEquiv.eq_symm_apply.symm

中文:
定理 trop_eq_iff_eq_untrop
  条件: {x : R} {y}
  结论: trop x = y ↔ x = untrop y
  证明: tropEquiv.eq_symm_apply.symm

Depends on / 依赖: FormallyUnramified, IsOpenImmersion, IsZariskiLocalAtSource, IsZariskiLocalAtSource.iff, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_openCover, MorphismProperty, MorphismProperty.pullback_snd, Y.affineCover, Y.affineCover.f, affineCover, diagonal, eq_symm_apply, generalizing, iff_of_openCover, pullback, pullback.diagonal, pullback.snd, pullback_snd, tropEquiv
-/
theorem trop_eq_iff_eq_untrop {x : R} {y} : trop x = y ↔ x = untrop y :=
  tropEquiv.eq_symm_apply.symm

/--
theorem `untrop_eq_iff_eq_trop` / 定理 `untrop_eq_iff_eq_trop`

English:
theorem untrop_eq_iff_eq_trop
  given: {x} {y : R}
  statement: untrop x = y ↔ x = trop y
  proof: tropEquiv.symm.eq_symm_apply.symm

中文:
定理 untrop_eq_iff_eq_trop
  条件: {x} {y : R}
  结论: untrop x = y ↔ x = trop y
  证明: tropEquiv.symm.eq_symm_apply.symm

Depends on / 依赖: eq_symm_apply, tropEquiv, tropEquiv.symm.eq_symm_apply.symm
-/
theorem untrop_eq_iff_eq_trop {x} {y : R} : untrop x = y ↔ x = trop y :=
  tropEquiv.symm.eq_symm_apply.symm

/--
theorem `injective_trop` / 定理 `injective_trop`

English:
theorem injective_trop
  statement: Function.Injective (trop : R -> Tropical R)
  proof: tropEquiv.injective

中文:
定理 injective_trop
  结论: 函数.单射 (trop : R -> Tropical R)
  证明: tropEquiv.injective

Depends on / 依赖: injective, tropEquiv, tropEquiv.injective
-/
theorem injective_trop : Function.Injective (trop : R -> Tropical R) :=
  tropEquiv.injective

/--
theorem `injective_untrop` / 定理 `injective_untrop`

English:
theorem injective_untrop
  statement: Function.Injective (untrop : Tropical R -> R)
  proof: tropEquiv.symm.injective

中文:
定理 injective_untrop
  结论: 函数.单射 (untrop : Tropical R -> R)
  证明: tropEquiv.symm.injective

Depends on / 依赖: injective, tropEquiv, tropEquiv.symm.injective
-/
theorem injective_untrop : Function.Injective (untrop : Tropical R -> R) :=
  tropEquiv.symm.injective

/--
theorem `surjective_trop` / 定理 `surjective_trop`

English:
theorem surjective_trop
  statement: Function.Surjective (trop : R -> Tropical R)
  proof: tropEquiv.surjective

中文:
定理 surjective_trop
  结论: 函数.满射 (trop : R -> Tropical R)
  证明: tropEquiv.surjective

Depends on / 依赖: surjective, tropEquiv, tropEquiv.surjective
-/
theorem surjective_trop : Function.Surjective (trop : R -> Tropical R) :=
  tropEquiv.surjective

/--
theorem `surjective_untrop` / 定理 `surjective_untrop`

English:
theorem surjective_untrop
  statement: Function.Surjective (untrop : Tropical R -> R)
  proof: tropEquiv.symm.surjective

中文:
定理 surjective_untrop
  结论: 函数.满射 (untrop : Tropical R -> R)
  证明: tropEquiv.symm.surjective

Depends on / 依赖: surjective, tropEquiv, tropEquiv.symm.surjective
-/
theorem surjective_untrop : Function.Surjective (untrop : Tropical R -> R) :=
  tropEquiv.symm.surjective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: R] : Inhabited (Tropical R)
  body: ⟨trop default⟩

中文:
实例 [可居
  签名: R] : 可居 (Tropical R)
  定义体: ⟨trop default⟩
-/
instance [Inhabited R] : Inhabited (Tropical R) :=
  ⟨trop default⟩

/-- Recursing on an `x' : Tropical R` is the same as recursing on an `x : R` reinterpreted
as a term of `Tropical R` via `trop x`. -/
@[simp]
/--
Definition of `tropRec` / `tropRec` 的定义

English:
definition tropRec
  signature: {F : Tropical R -> Sort v} (h : forall X, F (trop X))
  body: fun X => h (untrop X)

中文:
定义 tropRec
  签名: {F : Tropical R -> 类型层 v} (h : 对任意 X, F (trop X))
  定义体: fun X => h (untrop X)

Depends on / 依赖: untrop
-/
def tropRec {F : Tropical R -> Sort v} (h : forall X, F (trop X)) : forall X, F X := fun X => h (untrop X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: R] : DecidableEq (Tropical R)
  body: fun _ _ =>
  decidable_of_iff _ injective_untrop.eq_iff

中文:
实例 [DecidableEq
  签名: R] : DecidableEq (Tropical R)
  定义体: fun _ _ =>
  decidable_of_iff _ injective_untrop.eq_iff
-/
instance [DecidableEq R] : DecidableEq (Tropical R) := fun _ _ =>
  decidable_of_iff _ injective_untrop.eq_iff

section Order

/--
Instance `instLETropical` / 实例 `instLETropical`

English:
instance instLETropical
  signature: [LE R]
  body: untrop x <= untrop y

@[simp]

中文:
实例 instLETropical
  签名: [LE R]
  定义体: untrop x <= untrop y

@[simp]

Depends on / 依赖: untrop
-/
instance instLETropical [LE R] : LE (Tropical R) where le x y := untrop x <= untrop y

@[simp]
/--
theorem `untrop_le_iff` / 定理 `untrop_le_iff`

English:
theorem untrop_le_iff
  given: [LE R] {x y : Tropical R}
  statement: untrop x <= untrop y ↔ x <= y
  proof: Iff.rfl

中文:
定理 untrop_le_iff
  条件: [LE R] {x y : Tropical R}
  结论: untrop x <= untrop y ↔ x <= y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem untrop_le_iff [LE R] {x y : Tropical R} : untrop x <= untrop y ↔ x <= y :=
  Iff.rfl

/--
Instance `decidableLE` / 实例 `decidableLE`

English:
instance decidableLE
  signature: [LE R] [DecidableLE R]
  body: fun x y =>
  ‹DecidableLE R› (untrop x) (untrop y)

中文:
实例 decidableLE
  签名: [LE R] [DecidableLE R]
  定义体: fun x y =>
  ‹DecidableLE R› (untrop x) (untrop y)
-/
instance decidableLE [LE R] [DecidableLE R] : DecidableLE (Tropical R) := fun x y =>
  ‹DecidableLE R› (untrop x) (untrop y)

/--
Instance `instLTTropical` / 实例 `instLTTropical`

English:
instance instLTTropical
  signature: [LT R]
  body: untrop x < untrop y

@[simp]

中文:
实例 instLTTropical
  签名: [LT R]
  定义体: untrop x < untrop y

@[simp]

Depends on / 依赖: untrop
-/
instance instLTTropical [LT R] : LT (Tropical R) where lt x y := untrop x < untrop y

@[simp]
/--
theorem `untrop_lt_iff` / 定理 `untrop_lt_iff`

English:
theorem untrop_lt_iff
  given: [LT R] {x y : Tropical R}
  statement: untrop x < untrop y ↔ x < y
  proof: Iff.rfl

中文:
定理 untrop_lt_iff
  条件: [LT R] {x y : Tropical R}
  结论: untrop x < untrop y ↔ x < y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem untrop_lt_iff [LT R] {x y : Tropical R} : untrop x < untrop y ↔ x < y :=
  Iff.rfl

/--
Instance `decidableLT` / 实例 `decidableLT`

English:
instance decidableLT
  signature: [LT R] [DecidableLT R]
  body: fun x y =>
  ‹DecidableLT R› (untrop x) (untrop y)

中文:
实例 decidableLT
  签名: [LT R] [DecidableLT R]
  定义体: fun x y =>
  ‹DecidableLT R› (untrop x) (untrop y)
-/
instance decidableLT [LT R] [DecidableLT R] : DecidableLT (Tropical R) := fun x y =>
  ‹DecidableLT R› (untrop x) (untrop y)

/--
Instance `instPreorderTropical` / 实例 `instPreorderTropical`

English:
instance instPreorderTropical
  signature: [Preorder R]
  body: { instLETropical, instLTTropical with
    le_refl := fun x => le_refl (untrop x)
    le_trans := fun _ _ _ h h' => le_trans (α := R) h h'
    lt_iff_le_not_ge := fun _ _ => lt_iff_le_not_ge (α := R) }

中文:
实例 instPreorderTropical
  签名: [预序 R]
  定义体: { instLETropical, instLTTropical with
    le_refl := fun x => le_refl (untrop x)
    le_trans := fun _ _ _ h h' => le_trans (α := R) h h'
    lt_iff_le_not_ge := fun _ _ => lt_iff_le_not_ge (α := R) }

Depends on / 依赖: instLETropical, instLTTropical, le_refl, le_trans, lt_iff_le_not_ge, untrop
-/
instance instPreorderTropical [Preorder R] : Preorder (Tropical R) :=
  { instLETropical, instLTTropical with
    le_refl := fun x => le_refl (untrop x)
    le_trans := fun _ _ _ h h' => le_trans (α := R) h h'
    lt_iff_le_not_ge := fun _ _ => lt_iff_le_not_ge (α := R) }

/--
Definition of `tropOrderIso` / `tropOrderIso` 的定义

English:
definition tropOrderIso
  signature: [Preorder R]
  body: { tropEquiv with map_rel_iff' := untrop_le_iff }

@[simp]

中文:
定义 tropOrderIso
  签名: [预序 R]
  定义体: { tropEquiv with map_rel_iff' := untrop_le_iff }

@[simp]

Depends on / 依赖: map_rel_iff, tropEquiv, untrop_le_iff
-/
def tropOrderIso [Preorder R] : R ≃o Tropical R :=
  { tropEquiv with map_rel_iff' := untrop_le_iff }

@[simp]
/--
theorem `tropOrderIso_coe_fn` / 定理 `tropOrderIso_coe_fn`

English:
theorem tropOrderIso_coe_fn
  given: [Preorder R]
  statement: (tropOrderIso : R -> Tropical R) = trop
  proof: rfl

@[simp]

中文:
定理 tropOrderIso_coe_fn
  条件: [预序 R]
  结论: (tropOrderIso : R -> Tropical R) = trop
  证明: rfl

@[simp]

Depends on / 依赖: IsImmersion, IsOpenImmersion
-/
theorem tropOrderIso_coe_fn [Preorder R] : (tropOrderIso : R -> Tropical R) = trop :=
  rfl

@[simp]
/--
theorem `tropOrderIso_symm_coe_fn` / 定理 `tropOrderIso_symm_coe_fn`

English:
theorem tropOrderIso_symm_coe_fn
  given: [Preorder R]
  statement: (tropOrderIso.symm : Tropical R -> R) = untrop
  proof: rfl

中文:
定理 tropOrderIso_symm_coe_fn
  条件: [预序 R]
  结论: (tropOrderIso.symm : Tropical R -> R) = untrop
  证明: rfl

Depends on / 依赖: IsClosedImmersion, IsImmersion
-/
theorem tropOrderIso_symm_coe_fn [Preorder R] : (tropOrderIso.symm : Tropical R -> R) = untrop :=
  rfl

/--
theorem `trop_monotone` / 定理 `trop_monotone`

English:
theorem trop_monotone
  given: [Preorder R]
  statement: Monotone (trop : R -> Tropical R)
  proof: fun _ _ => id

中文:
定理 trop_monotone
  条件: [预序 R]
  结论: 递增 (trop : R -> Tropical R)
  证明: fun _ _ => id
-/
theorem trop_monotone [Preorder R] : Monotone (trop : R -> Tropical R) := fun _ _ => id

/--
theorem `untrop_monotone` / 定理 `untrop_monotone`

English:
theorem untrop_monotone
  given: [Preorder R]
  statement: Monotone (untrop : Tropical R -> R)
  proof: fun _ _ => id

中文:
定理 untrop_monotone
  条件: [预序 R]
  结论: 递增 (untrop : Tropical R -> R)
  证明: fun _ _ => id
-/
theorem untrop_monotone [Preorder R] : Monotone (untrop : Tropical R -> R) := fun _ _ => id

/--
Instance `instPartialOrderTropical` / 实例 `instPartialOrderTropical`

English:
instance instPartialOrderTropical
  signature: [PartialOrder R]
  body: { instPreorderTropical with le_antisymm := fun _ _ h h' => untrop_injective (le_antisymm h h') }

中文:
实例 instPartialOrderTropical
  签名: [偏序 R]
  定义体: { instPreorderTropical with le_antisymm := fun _ _ h h' => untrop_injective (le_antisymm h h') }

Depends on / 依赖: instPreorderTropical, le_antisymm, untrop_injective
-/
instance instPartialOrderTropical [PartialOrder R] : PartialOrder (Tropical R) :=
  { instPreorderTropical with le_antisymm := fun _ _ h h' => untrop_injective (le_antisymm h h') }

/--
Instance `instZeroTropical` / 实例 `instZeroTropical`

English:
instance instZeroTropical
  signature: [Top R]
  body: ⟨trop ⊤⟩

中文:
实例 instZeroTropical
  签名: [顶元素 R]
  定义体: ⟨trop ⊤⟩
-/
instance instZeroTropical [Top R] : Zero (Tropical R) :=
  ⟨trop ⊤⟩

/--
Instance `instTopTropical` / 实例 `instTopTropical`

English:
instance instTopTropical
  signature: [Top R]
  body: ⟨0⟩

@[simp]

中文:
实例 instTopTropical
  签名: [顶元素 R]
  定义体: ⟨0⟩

@[simp]

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, pullback_fst
-/
instance instTopTropical [Top R] : Top (Tropical R) :=
  ⟨0⟩

@[simp]
/--
theorem `untrop_zero` / 定理 `untrop_zero`

English:
theorem untrop_zero
  given: [Top R]
  statement: untrop (0 : Tropical R) = ⊤
  proof: rfl

@[simp]

中文:
定理 untrop_zero
  条件: [顶元素 R]
  结论: untrop (0 : Tropical R) = ⊤
  证明: rfl

@[simp]

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd
-/
theorem untrop_zero [Top R] : untrop (0 : Tropical R) = ⊤ :=
  rfl

@[simp]
/--
theorem `trop_top` / 定理 `trop_top`

English:
theorem trop_top
  given: [Top R]
  statement: trop (⊤ : R) = 0
  proof: rfl

@[simp]

中文:
定理 trop_top
  条件: [顶元素 R]
  结论: trop (⊤ : R) = 0
  证明: rfl

@[simp]

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, restrict
-/
theorem trop_top [Top R] : trop (⊤ : R) = 0 :=
  rfl

@[simp]
/--
theorem `trop_coe_ne_zero` / 定理 `trop_coe_ne_zero`

English:
theorem trop_coe_ne_zero
  given: (x : R)
  statement: trop (x : WithTop R) != 0
  proof: nofun

@[simp]

中文:
定理 trop_coe_ne_zero
  条件: (x : R)
  结论: trop (x : WithTop R) != 0
  证明: nofun

@[simp]

Depends on / 依赖: Scheme, Scheme.Hom.resLE, infer_instance
-/
theorem trop_coe_ne_zero (x : R) : trop (x : WithTop R) != 0 :=
  nofun

@[simp]
/--
theorem `zero_ne_trop_coe` / 定理 `zero_ne_trop_coe`

English:
theorem zero_ne_trop_coe
  given: (x : R)
  statement: 0 != (trop x : Tropical (WithTop R))
  proof: nofun

@[simp]

中文:
定理 zero_ne_trop_coe
  条件: (x : R)
  结论: 0 != (trop x : Tropical (WithTop R))
  证明: nofun

@[simp]

Depends on / 依赖: IsImmersion, LocallyOfFiniteType, f.liftCoborder_, infer_instance
-/
theorem zero_ne_trop_coe (x : R) : 0 != (trop x : Tropical (WithTop R)) :=
  nofun

@[simp]
/--
theorem `le_zero` / 定理 `le_zero`

English:
theorem le_zero
  given: [LE R] [OrderTop R] (x : Tropical R)
  statement: x <= 0
  proof: le_top (α := R)

中文:
定理 le_zero
  条件: [LE R] [有顶序 R] (x : Tropical R)
  结论: x <= 0
  证明: le_top (α := R)

Depends on / 依赖: le_top
-/
theorem le_zero [LE R] [OrderTop R] (x : Tropical R) : x <= 0 :=
  le_top (α := R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: R] [OrderTop R] : OrderTop (Tropical R)
  body: { instTopTropical with le_top := fun _ => le_top (α := R) }

中文:
实例 [LE
  签名: R] [有顶序 R] : 有顶序 (Tropical R)
  定义体: { instTopTropical with le_top := fun _ => le_top (α := R) }

Depends on / 依赖: MorphismProperty, MorphismProperty.of_isPullback, instTopTropical, le_top, of_isPullback, pullback_map_diagonal_isPullback
-/
instance [LE R] [OrderTop R] : OrderTop (Tropical R) :=
  { instTopTropical with le_top := fun _ => le_top (α := R) }

variable [LinearOrder R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (Tropical R)
  body: ⟨fun x y => trop (min (untrop x) (untrop y))⟩

中文:
实例 :
  签名: 加法 (Tropical R)
  定义体: ⟨fun x y => trop (min (untrop x) (untrop y))⟩

Depends on / 依赖: untrop
-/
instance : Add (Tropical R) :=
  ⟨fun x y => trop (min (untrop x) (untrop y))⟩

/--
Instance `instAddCommSemigroupTropical` / 实例 `instAddCommSemigroupTropical`

English:
instance instAddCommSemigroupTropical
  signature: : AddCommSemigroup (Tropical R) where
  body: untrop_injective (min_assoc _ _ _)
  add_comm _ _ := untrop_injective (min_comm _ _)

@[simp]

中文:
实例 instAddCommSemigroupTropical
  签名: : 加法交换半群 (Tropical R) where
  定义体: untrop_injective (min_assoc _ _ _)
  add_comm _ _ := untrop_injective (min_comm _ _)

@[simp]

Depends on / 依赖: min_assoc, untrop_injective
-/
instance instAddCommSemigroupTropical : AddCommSemigroup (Tropical R) where
  add_assoc _ _ _ := untrop_injective (min_assoc _ _ _)
  add_comm _ _ := untrop_injective (min_comm _ _)

@[simp]
/--
theorem `untrop_add` / 定理 `untrop_add`

English:
theorem untrop_add
  given: (x y : Tropical R)
  statement: untrop (x + y) = min (untrop x) (untrop y)
  proof: rfl

@[simp]

中文:
定理 untrop_add
  条件: (x y : Tropical R)
  结论: untrop (x + y) = 最小值 (untrop x) (untrop y)
  证明: rfl

@[simp]
-/
theorem untrop_add (x y : Tropical R) : untrop (x + y) = min (untrop x) (untrop y) :=
  rfl

@[simp]
/--
theorem `trop_min` / 定理 `trop_min`

English:
theorem trop_min
  given: (x y : R)
  statement: trop (min x y) = trop x + trop y
  proof: rfl

@[simp]

中文:
定理 trop_min
  条件: (x y : R)
  结论: trop (最小值 x y) = trop x + trop y
  证明: rfl

@[simp]
-/
theorem trop_min (x y : R) : trop (min x y) = trop x + trop y :=
  rfl

@[simp]
/--
theorem `trop_inf` / 定理 `trop_inf`

English:
theorem trop_inf
  given: (x y : R)
  statement: trop (x ⊓ y) = trop x + trop y
  proof: rfl

中文:
定理 trop_inf
  条件: (x y : R)
  结论: trop (x ⊓ y) = trop x + trop y
  证明: rfl

Depends on / 依赖: IsImmersion, MorphismProperty, MorphismProperty.of_isPullback, isPullback_equalizer_prod, of_isPullback
-/
theorem trop_inf (x y : R) : trop (x ⊓ y) = trop x + trop y :=
  rfl

/--
theorem `trop_add_def` / 定理 `trop_add_def`

English:
theorem trop_add_def
  given: (x y : Tropical R)
  statement: x + y = trop (min (untrop x) (untrop y))
  proof: rfl

中文:
定理 trop_add_def
  条件: (x y : Tropical R)
  结论: x + y = trop (最小值 (untrop x) (untrop y))
  证明: rfl
-/
theorem trop_add_def (x y : Tropical R) : x + y = trop (min (untrop x) (untrop y)) :=
  rfl

/--
Instance `instLinearOrderTropical` / 实例 `instLinearOrderTropical`

English:
instance instLinearOrderTropical
  signature: : LinearOrder (Tropical R)
  body: { instPartialOrderTropical with
    le_total := fun a b => le_total (untrop a) (untrop b)
    toDecidableLE := Tropical.decidableLE
    toDecidableEq := Tropical.instDecidableEq
    toDecidableLT := Tropical.decidableLT
    max := fun a b => trop (max (untrop a) (untrop b))
    max_def := fun a b => untrop_injective (by
      simp only [max_def, untrop_le_iff, untrop_trop]; split_ifs <;> simp)
    min := (· + ·)
    min_def := fun a b => untrop_injective (by
      simp only [untrop_add, min_def, untrop_le_iff]; split_ifs <;> simp) }

@[simp]

中文:
实例 instLinearOrderTropical
  签名: : 线性序 (Tropical R)
  定义体: { instPartialOrderTropical with
    le_total := fun a b => le_total (untrop a) (untrop b)
    toDecidableLE := Tropical.decidableLE
    toDecidableEq := Tropical.instDecidableEq
    toDecidableLT := Tropical.decidableLT
    max := fun a b => trop (max (untrop a) (untrop b))
    max_def := fun a b => untrop_injective (by
      simp only [max_def, untrop_le_iff, untrop_trop]; split_ifs <;> simp)
    min := (· + ·)
    min_def := fun a b => untrop_injective (by
      simp only [untrop_add, min_def, untrop_le_iff]; split_ifs <;> simp) }

@[simp]

Depends on / 依赖: Tropical, Tropical.decidableLE, Tropical.decidableLT, Tropical.instDecidableEq, decidableLE, decidableLT, instDecidableEq, instPartialOrderTropical, le_total, max_def, min_def, split_ifs, toDecidableEq, toDecidableLE, toDecidableLT, untrop, untrop_add, untrop_injective, untrop_le_iff, untrop_trop
-/
instance instLinearOrderTropical : LinearOrder (Tropical R) :=
  { instPartialOrderTropical with
    le_total := fun a b => le_total (untrop a) (untrop b)
    toDecidableLE := Tropical.decidableLE
    toDecidableEq := Tropical.instDecidableEq
    toDecidableLT := Tropical.decidableLT
    max := fun a b => trop (max (untrop a) (untrop b))
    max_def := fun a b => untrop_injective (by
      simp only [max_def, untrop_le_iff, untrop_trop]; split_ifs <;> simp)
    min := (· + ·)
    min_def := fun a b => untrop_injective (by
      simp only [untrop_add, min_def, untrop_le_iff]; split_ifs <;> simp) }

@[simp]
/--
theorem `untrop_sup` / 定理 `untrop_sup`

English:
theorem untrop_sup
  given: (x y : Tropical R)
  statement: untrop (x ⊔ y) = untrop x ⊔ untrop y
  proof: rfl

@[simp]

中文:
定理 untrop_sup
  条件: (x y : Tropical R)
  结论: untrop (x ⊔ y) = untrop x ⊔ untrop y
  证明: rfl

@[simp]
-/
theorem untrop_sup (x y : Tropical R) : untrop (x ⊔ y) = untrop x ⊔ untrop y :=
  rfl

@[simp]
/--
theorem `untrop_max` / 定理 `untrop_max`

English:
theorem untrop_max
  given: (x y : Tropical R)
  statement: untrop (max x y) = max (untrop x) (untrop y)
  proof: rfl

@[simp]

中文:
定理 untrop_max
  条件: (x y : Tropical R)
  结论: untrop (最大值 x y) = 最大值 (untrop x) (untrop y)
  证明: rfl

@[simp]
-/
theorem untrop_max (x y : Tropical R) : untrop (max x y) = max (untrop x) (untrop y) :=
  rfl

@[simp]
/--
theorem `min_eq_add` / 定理 `min_eq_add`

English:
theorem min_eq_add
  statement: (min : Tropical R -> Tropical R -> Tropical R) = (· + ·)
  proof: rfl

@[simp]

中文:
定理 min_eq_add
  结论: (最小值 : Tropical R -> Tropical R -> Tropical R) = (· + ·)
  证明: rfl

@[simp]
-/
theorem min_eq_add : (min : Tropical R -> Tropical R -> Tropical R) = (· + ·) :=
  rfl

@[simp]
/--
theorem `inf_eq_add` / 定理 `inf_eq_add`

English:
theorem inf_eq_add
  statement: ((· ⊓ ·) : Tropical R -> Tropical R -> Tropical R) = (· + ·)
  proof: rfl

中文:
定理 inf_eq_add
  结论: ((· ⊓ ·) : Tropical R -> Tropical R -> Tropical R) = (· + ·)
  证明: rfl
-/
theorem inf_eq_add : ((· ⊓ ·) : Tropical R -> Tropical R -> Tropical R) = (· + ·) :=
  rfl

/--
theorem `trop_max_def` / 定理 `trop_max_def`

English:
theorem trop_max_def
  given: (x y : Tropical R)
  statement: max x y = trop (max (untrop x) (untrop y))
  proof: rfl

中文:
定理 trop_max_def
  条件: (x y : Tropical R)
  结论: 最大值 x y = trop (最大值 (untrop x) (untrop y))
  证明: rfl
-/
theorem trop_max_def (x y : Tropical R) : max x y = trop (max (untrop x) (untrop y)) :=
  rfl

/--
theorem `trop_sup_def` / 定理 `trop_sup_def`

English:
theorem trop_sup_def
  given: (x y : Tropical R)
  statement: x ⊔ y = trop (untrop x ⊔ untrop y)
  proof: rfl

@[simp]

中文:
定理 trop_sup_def
  条件: (x y : Tropical R)
  结论: x ⊔ y = trop (untrop x ⊔ untrop y)
  证明: rfl

@[simp]
-/
theorem trop_sup_def (x y : Tropical R) : x ⊔ y = trop (untrop x ⊔ untrop y) :=
  rfl

@[simp]
/--
theorem `add_eq_left` / 定理 `add_eq_left`

English:
theorem add_eq_left
  given: ⦃x y
  statement: Tropical R⦄ (h : x <= y) : x + y = x
  proof: untrop_injective (by simpa using h)

@[simp]

中文:
定理 add_eq_left
  条件: ⦃x y
  结论: Tropical R⦄ (h : x <= y) : x + y = x
  证明: untrop_injective (by simpa using h)

@[simp]

Depends on / 依赖: IsClosedImmersion, IsIntegralHom, untrop_injective
-/
theorem add_eq_left ⦃x y : Tropical R⦄ (h : x <= y) : x + y = x :=
  untrop_injective (by simpa using h)

@[simp]
/--
theorem `add_eq_right` / 定理 `add_eq_right`

English:
theorem add_eq_right
  given: ⦃x y
  statement: Tropical R⦄ (h : y <= x) : x + y = y
  proof: untrop_injective (by simpa using h)

中文:
定理 add_eq_right
  条件: ⦃x y
  结论: Tropical R⦄ (h : y <= x) : x + y = y
  证明: untrop_injective (by simpa using h)

Depends on / 依赖: untrop_injective
-/
theorem add_eq_right ⦃x y : Tropical R⦄ (h : y <= x) : x + y = y :=
  untrop_injective (by simpa using h)

/--
theorem `add_eq_left_iff` / 定理 `add_eq_left_iff`

English:
theorem add_eq_left_iff
  given: {x y : Tropical R}
  statement: x + y = x ↔ x <= y
  proof: by
  rw [trop_add_def]; rw [trop_eq_iff_eq_untrop]; rw [← untrop_le_iff]; rw [min_eq_left_iff]

中文:
定理 add_eq_left_iff
  条件: {x y : Tropical R}
  结论: x + y = x ↔ x <= y
  证明: by
  rw [trop_add_def]; rw [trop_eq_iff_eq_untrop]; rw [← untrop_le_iff]; rw [min_eq_left_iff]

Depends on / 依赖: MorphismProperty, MorphismProperty.comp_mem, comp_mem, min_eq_left_iff, trop_add_def, trop_eq_iff_eq_untrop, untrop_le_iff
-/
theorem add_eq_left_iff {x y : Tropical R} : x + y = x ↔ x <= y := by
  rw [trop_add_def]; rw [trop_eq_iff_eq_untrop]; rw [← untrop_le_iff]; rw [min_eq_left_iff]

/--
theorem `add_eq_right_iff` / 定理 `add_eq_right_iff`

English:
theorem add_eq_right_iff
  given: {x y : Tropical R}
  statement: x + y = y ↔ y <= x
  proof: by
  rw [trop_add_def]; rw [trop_eq_iff_eq_untrop]; rw [← untrop_le_iff]; rw [min_eq_right_iff]

中文:
定理 add_eq_right_iff
  条件: {x y : Tropical R}
  结论: x + y = y ↔ y <= x
  证明: by
  rw [trop_add_def]; rw [trop_eq_iff_eq_untrop]; rw [← untrop_le_iff]; rw [min_eq_right_iff]

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, min_eq_right_iff, pullback_fst, trop_add_def, trop_eq_iff_eq_untrop, untrop_le_iff
-/
theorem add_eq_right_iff {x y : Tropical R} : x + y = y ↔ y <= x := by
  rw [trop_add_def]; rw [trop_eq_iff_eq_untrop]; rw [← untrop_le_iff]; rw [min_eq_right_iff]

/--
theorem `add_self` / 定理 `add_self`

English:
theorem add_self
  given: (x : Tropical R)
  statement: x + x = x
  proof: untrop_injective (min_eq_right le_rfl)

中文:
定理 add_self
  条件: (x : Tropical R)
  结论: x + x = x
  证明: untrop_injective (min_eq_right le_rfl)

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, le_rfl, min_eq_right, pullback_snd, untrop_injective
-/
theorem add_self (x : Tropical R) : x + x = x :=
  untrop_injective (min_eq_right le_rfl)

/--
theorem `add_eq_iff` / 定理 `add_eq_iff`

English:
theorem add_eq_iff
  given: {x y z : Tropical R}
  statement: x + y = z ↔ x = z ∧ x <= y ∨ y = z ∧ y <= x
  proof: by
  rw [trop_add_def]; rw [trop_eq_iff_eq_untrop]
  simp [min_eq_iff]

@[simp]

中文:
定理 add_eq_iff
  条件: {x y z : Tropical R}
  结论: x + y = z ↔ x = z ∧ x <= y ∨ y = z ∧ y <= x
  证明: by
  rw [trop_add_def]; rw [trop_eq_iff_eq_untrop]
  simp [min_eq_iff]

@[simp]

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, min_eq_iff, restrict, trop_add_def, trop_eq_iff_eq_untrop
-/
theorem add_eq_iff {x y z : Tropical R} : x + y = z ↔ x = z ∧ x <= y ∨ y = z ∧ y <= x := by
  rw [trop_add_def]; rw [trop_eq_iff_eq_untrop]
  simp [min_eq_iff]

@[simp]
/--
theorem `add_eq_zero_iff` / 定理 `add_eq_zero_iff`

English:
theorem add_eq_zero_iff
  given: {a b : Tropical (WithTop R)}
  statement: a + b = 0 ↔ a = 0 ∧ b = 0
  proof: by
  rw [add_eq_iff]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨rfl, le_antisymm (le_zero _) h⟩
    · exact ⟨le_antisymm (le_zero _) h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp

中文:
定理 add_eq_zero_iff
  条件: {a b : Tropical (WithTop R)}
  结论: a + b = 0 ↔ a = 0 ∧ b = 0
  证明: by
  rw [add_eq_iff]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨rfl, le_antisymm (le_zero _) h⟩
    · exact ⟨le_antisymm (le_zero _) h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp

Depends on / 依赖: add_eq_iff, le_antisymm, le_zero
-/
theorem add_eq_zero_iff {a b : Tropical (WithTop R)} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [add_eq_iff]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨rfl, le_antisymm (le_zero _) h⟩
    · exact ⟨le_antisymm (le_zero _) h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp

/--
Instance `instAddCommMonoidTropical` / 实例 `instAddCommMonoidTropical`

English:
instance instAddCommMonoidTropical
  signature: [OrderTop R]
  body: { instZeroTropical, instAddCommSemigroupTropical with
    zero_add := fun _ => untrop_injective (min_top_left _)
    add_zero := fun _ => untrop_injective (min_top_right _)
    nsmul := nsmulRec }

中文:
实例 instAddCommMonoidTropical
  签名: [有顶序 R]
  定义体: { instZeroTropical, instAddCommSemigroupTropical with
    zero_add := fun _ => untrop_injective (min_top_left _)
    add_zero := fun _ => untrop_injective (min_top_right _)
    nsmul := nsmulRec }

Depends on / 依赖: add_zero, instAddCommSemigroupTropical, instZeroTropical, min_top_left, min_top_right, nsmulRec, untrop_injective, zero_add
-/
instance instAddCommMonoidTropical [OrderTop R] : AddCommMonoid (Tropical R) :=
  { instZeroTropical, instAddCommSemigroupTropical with
    zero_add := fun _ => untrop_injective (min_top_left _)
    add_zero := fun _ => untrop_injective (min_top_right _)
    nsmul := nsmulRec }

end Order

section Monoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: R] : Mul (Tropical R)
  body: ⟨fun x y => trop (untrop x + untrop y)⟩

@[simp]

中文:
实例 [加法
  签名: R] : 乘法 (Tropical R)
  定义体: ⟨fun x y => trop (untrop x + untrop y)⟩

@[simp]

Depends on / 依赖: untrop
-/
instance [Add R] : Mul (Tropical R) :=
  ⟨fun x y => trop (untrop x + untrop y)⟩

@[simp]
/--
theorem `trop_add` / 定理 `trop_add`

English:
theorem trop_add
  given: [Add R] (x y : R)
  statement: trop (x + y) = trop x * trop y
  proof: rfl

@[simp]

中文:
定理 trop_add
  条件: [加法 R] (x y : R)
  结论: trop (x + y) = trop x * trop y
  证明: rfl

@[simp]
-/
theorem trop_add [Add R] (x y : R) : trop (x + y) = trop x * trop y :=
  rfl

@[simp]
/--
theorem `untrop_mul` / 定理 `untrop_mul`

English:
theorem untrop_mul
  given: [Add R] (x y : Tropical R)
  statement: untrop (x * y) = untrop x + untrop y
  proof: rfl

中文:
定理 untrop_mul
  条件: [加法 R] (x y : Tropical R)
  结论: untrop (x * y) = untrop x + untrop y
  证明: rfl

Depends on / 依赖: RingHom, RingHom.isIntegral_respectsIso, algebraMap_isIntegral_iff, algebraMap_isIntegral_iff.mpr, algebraize, coprodDesc_affineAnd, hasAffineProperty, hasAffineProperty.coprodDesc_affineAnd, intros, isIntegral_respectsIso
-/
theorem untrop_mul [Add R] (x y : Tropical R) : untrop (x * y) = untrop x + untrop y :=
  rfl

/--
theorem `trop_mul_def` / 定理 `trop_mul_def`

English:
theorem trop_mul_def
  given: [Add R] (x y : Tropical R)
  statement: x * y = trop (untrop x + untrop y)
  proof: rfl

中文:
定理 trop_mul_def
  条件: [加法 R] (x y : Tropical R)
  结论: x * y = trop (untrop x + untrop y)
  证明: rfl

Depends on / 依赖: IsIntegralHom
-/
theorem trop_mul_def [Add R] (x y : Tropical R) : x * y = trop (untrop x + untrop y) :=
  rfl

/--
Instance `instOneTropical` / 实例 `instOneTropical`

English:
instance instOneTropical
  signature: [Zero R]
  body: ⟨trop 0⟩

@[simp]

中文:
实例 instOneTropical
  签名: [零 R]
  定义体: ⟨trop 0⟩

@[simp]
-/
instance instOneTropical [Zero R] : One (Tropical R) :=
  ⟨trop 0⟩

@[simp]
/--
theorem `trop_zero` / 定理 `trop_zero`

English:
theorem trop_zero
  given: [Zero R]
  statement: trop (0 : R) = 1
  proof: rfl

@[simp]

中文:
定理 trop_zero
  条件: [零 R]
  结论: trop (0 : R) = 1
  证明: rfl

@[simp]
-/
theorem trop_zero [Zero R] : trop (0 : R) = 1 :=
  rfl

@[simp]
/--
theorem `untrop_one` / 定理 `untrop_one`

English:
theorem untrop_one
  given: [Zero R]
  statement: untrop (1 : Tropical R) = 0
  proof: rfl

中文:
定理 untrop_one
  条件: [零 R]
  结论: untrop (1 : Tropical R) = 0
  证明: rfl
-/
theorem untrop_one [Zero R] : untrop (1 : Tropical R) = 0 :=
  rfl

/--
Instance `instAddMonoidWithOneTropical` / 实例 `instAddMonoidWithOneTropical`

English:
instance instAddMonoidWithOneTropical
  signature: [LinearOrder R] [OrderTop R] [Zero R]
  body: { instOneTropical, instAddCommMonoidTropical with
    natCast := fun n => if n = 0 then 0 else 1
    natCast_zero := rfl
    natCast_succ := fun n => (untrop_inj_iff _ _).1 (by cases n <;> simp) }

中文:
实例 instAddMonoidWithOneTropical
  签名: [线性序 R] [有顶序 R] [零 R]
  定义体: { instOneTropical, instAddCommMonoidTropical with
    natCast := fun n => if n = 0 then 0 else 1
    natCast_zero := rfl
    natCast_succ := fun n => (untrop_inj_iff _ _).1 (by cases n <;> simp) }

Depends on / 依赖: instAddCommMonoidTropical, instOneTropical, natCast, natCast_succ, natCast_zero, untrop_inj_iff
-/
instance instAddMonoidWithOneTropical [LinearOrder R] [OrderTop R] [Zero R] :
    AddMonoidWithOne (Tropical R) :=
  { instOneTropical, instAddCommMonoidTropical with
    natCast := fun n => if n = 0 then 0 else 1
    natCast_zero := rfl
    natCast_succ := fun n => (untrop_inj_iff _ _).1 (by cases n <;> simp) }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] : Nontrivial (Tropical (WithTop R))
  body: ⟨⟨0, 1, trop_injective.ne WithTop.top_ne_coe⟩⟩

中文:
实例 [零
  签名: R] : 非平凡 (Tropical (WithTop R))
  定义体: ⟨⟨0, 1, trop_injective.ne WithTop.top_ne_coe⟩⟩

Depends on / 依赖: WithTop, WithTop.top_ne_coe, top_ne_coe, trop_injective, trop_injective.ne
-/
instance [Zero R] : Nontrivial (Tropical (WithTop R)) :=
  ⟨⟨0, 1, trop_injective.ne WithTop.top_ne_coe⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Neg
  signature: R] : Inv (Tropical R)
  body: ⟨fun x => trop (-untrop x)⟩

@[simp]

中文:
实例 [取负
  签名: R] : 取逆 (Tropical R)
  定义体: ⟨fun x => trop (-untrop x)⟩

@[simp]

Depends on / 依赖: untrop
-/
instance [Neg R] : Inv (Tropical R) :=
  ⟨fun x => trop (-untrop x)⟩

@[simp]
/--
theorem `untrop_inv` / 定理 `untrop_inv`

English:
theorem untrop_inv
  given: [Neg R] (x : Tropical R)
  statement: untrop x⁻¹ = -untrop x
  proof: rfl

中文:
定理 untrop_inv
  条件: [取负 R] (x : Tropical R)
  结论: untrop x⁻¹ = -untrop x
  证明: rfl
-/
theorem untrop_inv [Neg R] (x : Tropical R) : untrop x⁻¹ = -untrop x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Sub
  signature: R] : Div (Tropical R)
  body: ⟨fun x y => trop (untrop x - untrop y)⟩

@[simp]

中文:
实例 [减法
  签名: R] : 除法 (Tropical R)
  定义体: ⟨fun x y => trop (untrop x - untrop y)⟩

@[simp]

Depends on / 依赖: untrop
-/
instance [Sub R] : Div (Tropical R) :=
  ⟨fun x y => trop (untrop x - untrop y)⟩

@[simp]
/--
theorem `untrop_div` / 定理 `untrop_div`

English:
theorem untrop_div
  given: [Sub R] (x y : Tropical R)
  statement: untrop (x / y) = untrop x - untrop y
  proof: rfl

中文:
定理 untrop_div
  条件: [减法 R] (x y : Tropical R)
  结论: untrop (x / y) = untrop x - untrop y
  证明: rfl
-/
theorem untrop_div [Sub R] (x y : Tropical R) : untrop (x / y) = untrop x - untrop y :=
  rfl

/--
Instance `instSemigroupTropical` / 实例 `instSemigroupTropical`

English:
instance instSemigroupTropical
  signature: [AddSemigroup R]
  body: untrop_injective (add_assoc _ _ _)

中文:
实例 instSemigroupTropical
  签名: [加法半群 R]
  定义体: untrop_injective (add_assoc _ _ _)

Depends on / 依赖: add_assoc, untrop_injective
-/
instance instSemigroupTropical [AddSemigroup R] : Semigroup (Tropical R) where
  mul_assoc _ _ _ := untrop_injective (add_assoc _ _ _)

/--
Instance `instCommSemigroupTropical` / 实例 `instCommSemigroupTropical`

English:
instance instCommSemigroupTropical
  signature: [AddCommSemigroup R]
  body: { instSemigroupTropical with mul_comm := fun _ _ => untrop_injective (add_comm _ _) }

中文:
实例 instCommSemigroupTropical
  签名: [加法交换半群 R]
  定义体: { instSemigroupTropical with mul_comm := fun _ _ => untrop_injective (add_comm _ _) }

Depends on / 依赖: add_comm, instSemigroupTropical, mul_comm, untrop_injective
-/
instance instCommSemigroupTropical [AddCommSemigroup R] : CommSemigroup (Tropical R) :=
  { instSemigroupTropical with mul_comm := fun _ _ => untrop_injective (add_comm _ _) }

instance {α : Type*} [SMul α R] : Pow (Tropical R) α where pow x n := trop n • untrop x

@[simp]
/--
theorem `untrop_pow` / 定理 `untrop_pow`

English:
theorem untrop_pow
  given: {α : Type*} [SMul α R] (x : Tropical R) (n : α)
  proof: rfl

@[simp]

中文:
定理 untrop_pow
  条件: {α : 类型} [标量乘法 α R] (x : Tropical R) (n : α)
  证明: rfl

@[simp]
-/
theorem untrop_pow {α : Type*} [SMul α R] (x : Tropical R) (n : α) :
    untrop (x ^ n) = n • untrop x :=
  rfl

@[simp]
/--
theorem `trop_smul` / 定理 `trop_smul`

English:
theorem trop_smul
  given: {α : Type*} [SMul α R] (x : R) (n : α)
  statement: trop (n • x) = trop x ^ n
  proof: rfl

中文:
定理 trop_smul
  条件: {α : 类型} [标量乘法 α R] (x : R) (n : α)
  结论: trop (n • x) = trop x ^ n
  证明: rfl
-/
theorem trop_smul {α : Type*} [SMul α R] (x : R) (n : α) : trop (n • x) = trop x ^ n :=
  rfl

/--
Instance `instMulOneClassTropical` / 实例 `instMulOneClassTropical`

English:
instance instMulOneClassTropical
  signature: [AddZeroClass R]
  body: untrop_injective zero_add _
mul_one _ := untrop_injective add_zero _

中文:
实例 instMulOneClassTropical
  签名: [加法零类 R]
  定义体: untrop_injective zero_add _
mul_one _ := untrop_injective add_zero _

Depends on / 依赖: untrop_injective, zero_add
-/
instance instMulOneClassTropical [AddZeroClass R] : MulOneClass (Tropical R) where
one_mul _ := untrop_injective zero_add _
mul_one _ := untrop_injective add_zero _

/--
Instance `instMonoidTropical` / 实例 `instMonoidTropical`

English:
instance instMonoidTropical
  signature: [AddMonoid R]
  body: { instMulOneClassTropical, instSemigroupTropical with
    npow := fun n x => x ^ n
npow_zero := fun _ => untrop_injective by simp
npow_succ := fun _ _ => untrop_injective succ_nsmul _ _ }

@[simp]

中文:
实例 instMonoidTropical
  签名: [加法幺半群 R]
  定义体: { instMulOneClassTropical, instSemigroupTropical with
    npow := fun n x => x ^ n
npow_zero := fun _ => untrop_injective by simp
npow_succ := fun _ _ => untrop_injective succ_nsmul _ _ }

@[simp]

Depends on / 依赖: instMulOneClassTropical, instSemigroupTropical, npow_succ, npow_zero, succ_nsmul, untrop_injective
-/
instance instMonoidTropical [AddMonoid R] : Monoid (Tropical R) :=
  { instMulOneClassTropical, instSemigroupTropical with
    npow := fun n x => x ^ n
npow_zero := fun _ => untrop_injective by simp
npow_succ := fun _ _ => untrop_injective succ_nsmul _ _ }

@[simp]
/--
theorem `trop_nsmul` / 定理 `trop_nsmul`

English:
theorem trop_nsmul
  given: [AddMonoid R] (x : R) (n : Nat)
  statement: trop (n • x) = trop x ^ n
  proof: rfl

中文:
定理 trop_nsmul
  条件: [加法幺半群 R] (x : R) (n : 自然数)
  结论: trop (n • x) = trop x ^ n
  证明: rfl
-/
theorem trop_nsmul [AddMonoid R] (x : R) (n : Nat) : trop (n • x) = trop x ^ n :=
  rfl

/--
Instance `instCommMonoidTropical` / 实例 `instCommMonoidTropical`

English:
instance instCommMonoidTropical
  signature: [AddCommMonoid R]
  body: { instMonoidTropical, instCommSemigroupTropical with }

中文:
实例 instCommMonoidTropical
  签名: [加法交换幺半群 R]
  定义体: { instMonoidTropical, instCommSemigroupTropical with }

Depends on / 依赖: instCommSemigroupTropical, instMonoidTropical
-/
instance instCommMonoidTropical [AddCommMonoid R] : CommMonoid (Tropical R) :=
  { instMonoidTropical, instCommSemigroupTropical with }

/--
Instance `instGroupTropical` / 实例 `instGroupTropical`

English:
instance instGroupTropical
  signature: [AddGroup R]
  body: { instMonoidTropical with
div_eq_mul_inv := fun _ _ => untrop_injective by simp [sub_eq_add_neg]
inv_mul_cancel := fun _ => untrop_injective neg_add_cancel _
zpow := fun n x => trop n • untrop x
zpow_zero' := fun _ => untrop_injective zero_zsmul _
zpow_succ' := fun _ _ => untrop_injective SubNegMonoid.zsmul_succ' _ _
zpow_neg' := fun _ _ => untrop_injective SubNegMonoid.zsmul_neg' _ _ }

中文:
实例 instGroupTropical
  签名: [加法群 R]
  定义体: { instMonoidTropical with
div_eq_mul_inv := fun _ _ => untrop_injective by simp [sub_eq_add_neg]
inv_mul_cancel := fun _ => untrop_injective neg_add_cancel _
zpow := fun n x => trop n • untrop x
zpow_zero' := fun _ => untrop_injective zero_zsmul _
zpow_succ' := fun _ _ => untrop_injective SubNegMonoid.zsmul_succ' _ _
zpow_neg' := fun _ _ => untrop_injective SubNegMonoid.zsmul_neg' _ _ }

Depends on / 依赖: SubNegMonoid, SubNegMonoid.zsmul_neg, SubNegMonoid.zsmul_succ, div_eq_mul_inv, instMonoidTropical, inv_mul_cancel, neg_add_cancel, sub_eq_add_neg, untrop, untrop_injective, zero_zsmul, zpow_neg, zpow_succ, zpow_zero, zsmul_neg, zsmul_succ
-/
instance instGroupTropical [AddGroup R] : Group (Tropical R) :=
  { instMonoidTropical with
div_eq_mul_inv := fun _ _ => untrop_injective by simp [sub_eq_add_neg]
inv_mul_cancel := fun _ => untrop_injective neg_add_cancel _
zpow := fun n x => trop n • untrop x
zpow_zero' := fun _ => untrop_injective zero_zsmul _
zpow_succ' := fun _ _ => untrop_injective SubNegMonoid.zsmul_succ' _ _
zpow_neg' := fun _ _ => untrop_injective SubNegMonoid.zsmul_neg' _ _ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: R] : CommGroup (Tropical R)
  body: { instGroupTropical with mul_comm := fun _ _ => untrop_injective (add_comm _ _) }

@[simp]

中文:
实例 [加法交换群
  签名: R] : 交换群 (Tropical R)
  定义体: { instGroupTropical with mul_comm := fun _ _ => untrop_injective (add_comm _ _) }

@[simp]

Depends on / 依赖: add_comm, instGroupTropical, mul_comm, untrop_injective
-/
instance [AddCommGroup R] : CommGroup (Tropical R) :=
  { instGroupTropical with mul_comm := fun _ _ => untrop_injective (add_comm _ _) }

@[simp]
/--
theorem `untrop_zpow` / 定理 `untrop_zpow`

English:
theorem untrop_zpow
  given: [AddGroup R] (x : Tropical R) (n : Int)
  statement: untrop (x ^ n) = n • untrop x
  proof: rfl

@[simp]

中文:
定理 untrop_zpow
  条件: [加法群 R] (x : Tropical R) (n : 整数)
  结论: untrop (x ^ n) = n • untrop x
  证明: rfl

@[simp]
-/
theorem untrop_zpow [AddGroup R] (x : Tropical R) (n : Int) : untrop (x ^ n) = n • untrop x :=
  rfl

@[simp]
/--
theorem `trop_zsmul` / 定理 `trop_zsmul`

English:
theorem trop_zsmul
  given: [AddGroup R] (x : R) (n : Int)
  statement: trop (n • x) = trop x ^ n
  proof: rfl

中文:
定理 trop_zsmul
  条件: [加法群 R] (x : R) (n : 整数)
  结论: trop (n • x) = trop x ^ n
  证明: rfl
-/
theorem trop_zsmul [AddGroup R] (x : R) (n : Int) : trop (n • x) = trop x ^ n :=
  rfl

end Monoid

section Distrib

/--
Instance `mulLeftMono` / 实例 `mulLeftMono`

English:
instance mulLeftMono
  signature: [LE R] [Add R] [AddLeftMono R]
  body: ⟨fun _ y z h => add_le_add_right (show untrop y <= untrop z from h) _⟩

中文:
实例 mulLeftMono
  签名: [LE R] [加法 R] [AddLeftMono R]
  定义体: ⟨fun _ y z h => add_le_add_right (show untrop y <= untrop z from h) _⟩

Depends on / 依赖: add_le_add_right, untrop
-/
instance mulLeftMono [LE R] [Add R] [AddLeftMono R] :
    MulLeftMono (Tropical R) :=
  ⟨fun _ y z h => add_le_add_right (show untrop y <= untrop z from h) _⟩

/--
Instance `mulRightMono` / 实例 `mulRightMono`

English:
instance mulRightMono
  signature: [LE R] [Add R] [AddRightMono R]
  body: ⟨fun _ y z h => add_le_add_left (show untrop y <= untrop z from h) _⟩

中文:
实例 mulRightMono
  签名: [LE R] [加法 R] [AddRightMono R]
  定义体: ⟨fun _ y z h => add_le_add_left (show untrop y <= untrop z from h) _⟩

Depends on / 依赖: add_le_add_left, untrop
-/
instance mulRightMono [LE R] [Add R] [AddRightMono R] :
    MulRightMono (Tropical R) :=
  ⟨fun _ y z h => add_le_add_left (show untrop y <= untrop z from h) _⟩

/--
Instance `addLeftMono` / 实例 `addLeftMono`

English:
instance addLeftMono
  signature: [LinearOrder R]
  body: ⟨fun x y z h => by
    rcases le_total x y with hx | hy
    · rw [add_eq_left hx, add_eq_left (hx.trans h)]
    · rw [add_eq_right hy]
      rcases le_total x z with hx | hx
      · rwa [add_eq_left hx]
      · rwa [add_eq_right hx]⟩

中文:
实例 addLeftMono
  签名: [线性序 R]
  定义体: ⟨fun x y z h => by
    rcases le_total x y with hx | hy
    · rw [add_eq_left hx, add_eq_left (hx.trans h)]
    · rw [add_eq_right hy]
      rcases le_total x z with hx | hx
      · rwa [add_eq_left hx]
      · rwa [add_eq_right hx]⟩

Depends on / 依赖: add_eq_left, add_eq_right, hx.trans, le_total
-/
instance addLeftMono [LinearOrder R] : AddLeftMono (Tropical R) :=
  ⟨fun x y z h => by
    rcases le_total x y with hx | hy
    · rw [add_eq_left hx, add_eq_left (hx.trans h)]
    · rw [add_eq_right hy]
      rcases le_total x z with hx | hx
      · rwa [add_eq_left hx]
      · rwa [add_eq_right hx]⟩

/--
Instance `mulLeftStrictMono` / 实例 `mulLeftStrictMono`

English:
instance mulLeftStrictMono
  signature: [LT R] [Add R] [AddLeftStrictMono R]
  body: ⟨fun _ _ _ h => add_lt_add_right (untrop_lt_iff.2 h) _⟩

中文:
实例 mulLeftStrictMono
  签名: [LT R] [加法 R] [AddLeftStrictMono R]
  定义体: ⟨fun _ _ _ h => add_lt_add_right (untrop_lt_iff.2 h) _⟩

Depends on / 依赖: add_lt_add_right, untrop_lt_iff
-/
instance mulLeftStrictMono [LT R] [Add R] [AddLeftStrictMono R] :
    MulLeftStrictMono (Tropical R) :=
  ⟨fun _ _ _ h => add_lt_add_right (untrop_lt_iff.2 h) _⟩

/--
Instance `mulRightStrictMono` / 实例 `mulRightStrictMono`

English:
instance mulRightStrictMono
  signature: [Preorder R] [Add R] [AddRightStrictMono R]
  body: ⟨fun _ y z h => add_lt_add_left (show untrop y < untrop z from h) _⟩

中文:
实例 mulRightStrictMono
  签名: [预序 R] [加法 R] [AddRightStrictMono R]
  定义体: ⟨fun _ y z h => add_lt_add_left (show untrop y < untrop z from h) _⟩

Depends on / 依赖: add_lt_add_left, untrop
-/
instance mulRightStrictMono [Preorder R] [Add R] [AddRightStrictMono R] :
    MulRightStrictMono (Tropical R) :=
  ⟨fun _ y z h => add_lt_add_left (show untrop y < untrop z from h) _⟩

/--
Instance `instDistribTropical` / 实例 `instDistribTropical`

English:
instance instDistribTropical
  signature: [LinearOrder R] [Add R] [AddLeftMono R] [AddRightMono R]
  body: untrop_injective (min_add_add_left _ _ _).symm
  right_distrib _ _ _ := untrop_injective (min_add_add_right _ _ _).symm

@[simp]

中文:
实例 instDistribTropical
  签名: [线性序 R] [加法 R] [AddLeftMono R] [AddRightMono R]
  定义体: untrop_injective (min_add_add_left _ _ _).symm
  right_distrib _ _ _ := untrop_injective (min_add_add_right _ _ _).symm

@[simp]

Depends on / 依赖: min_add_add_left, untrop_injective
-/
instance instDistribTropical [LinearOrder R] [Add R] [AddLeftMono R] [AddRightMono R] :
    Distrib (Tropical R) where
  left_distrib _ _ _ := untrop_injective (min_add_add_left _ _ _).symm
  right_distrib _ _ _ := untrop_injective (min_add_add_right _ _ _).symm

@[simp]
/--
theorem `add_pow` / 定理 `add_pow`

English:
theorem add_pow
  statement: [LinearOrder R] [AddMonoid R] [AddLeftMono R] [AddRightMono R]
  proof: by
  rcases le_total x y with h | h
  · rw [add_eq_left h, add_eq_left (pow_le_pow_left' h _)]
  · rw [add_eq_right h, add_eq_right (pow_le_pow_left' h _)]

中文:
定理 add_pow
  结论: [线性序 R] [加法幺半群 R] [AddLeftMono R] [AddRightMono R]
  证明: by
  rcases le_total x y with h | h
  · rw [add_eq_left h, add_eq_left (pow_le_pow_left' h _)]
  · rw [add_eq_right h, add_eq_right (pow_le_pow_left' h _)]

Depends on / 依赖: add_eq_left, add_eq_right, le_total, pow_le_pow_left
-/
theorem add_pow [LinearOrder R] [AddMonoid R] [AddLeftMono R] [AddRightMono R]
    (x y : Tropical R) (n : Nat) :
    (x + y) ^ n = x ^ n + y ^ n := by
  rcases le_total x y with h | h
  · rw [add_eq_left h, add_eq_left (pow_le_pow_left' h _)]
  · rw [add_eq_right h, add_eq_right (pow_le_pow_left' h _)]

end Distrib

section Semiring

variable [LinearOrderedAddCommMonoidWithTop R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemiring (Tropical R)
  body: { instAddMonoidWithOneTropical,
    instDistribTropical,
    instAddCommMonoidTropical,
    instCommMonoidTropical with
    zero_mul := fun _ => untrop_injective (by simp [top_add])
    mul_zero := fun _ => untrop_injective (by simp [add_top]) }

@[simp]

中文:
实例 :
  签名: 交换半环 (Tropical R)
  定义体: { instAddMonoidWithOneTropical,
    instDistribTropical,
    instAddCommMonoidTropical,
    instCommMonoidTropical with
    zero_mul := fun _ => untrop_injective (by simp [top_add])
    mul_zero := fun _ => untrop_injective (by simp [add_top]) }

@[simp]

Depends on / 依赖: add_top, instAddCommMonoidTropical, instAddMonoidWithOneTropical, instCommMonoidTropical, instDistribTropical, mul_zero, top_add, untrop_injective, zero_mul
-/
instance : CommSemiring (Tropical R) :=
  { instAddMonoidWithOneTropical,
    instDistribTropical,
    instAddCommMonoidTropical,
    instCommMonoidTropical with
    zero_mul := fun _ => untrop_injective (by simp [top_add])
    mul_zero := fun _ => untrop_injective (by simp [add_top]) }

@[simp]
/--
theorem `succ_nsmul` / 定理 `succ_nsmul`

English:
theorem succ_nsmul
  given: {R} [LinearOrder R] [OrderTop R] (x : Tropical R) (n : Nat)
  statement: (n + 1) • x = x
  proof: by
  induction n with
  | zero => simp [one_nsmul]
  | succ n IH => rw [add_nsmul, IH, one_nsmul, add_self]

中文:
定理 succ_nsmul
  条件: {R} [线性序 R] [有顶序 R] (x : Tropical R) (n : 自然数)
  结论: (n + 1) • x = x
  证明: by
  induction n with
  | zero => simp [one_nsmul]
  | succ n IH => rw [add_nsmul, IH, one_nsmul, add_self]

Depends on / 依赖: add_nsmul, add_self, one_nsmul
-/
theorem succ_nsmul {R} [LinearOrder R] [OrderTop R] (x : Tropical R) (n : Nat) : (n + 1) • x = x := by
  induction n with
  | zero => simp [one_nsmul]
  | succ n IH => rw [add_nsmul, IH, one_nsmul, add_self]

-- TODO: find/create the right classes to make this hold (for enat, ennreal, etc)
-- Requires `zero_eq_bot` to be true
-- lemma add_eq_zero_iff {a b : tropical R} :
-- a + b = 1 ↔ a = 1 ∨ b = 1 := sorry
/--
theorem `mul_eq_zero_iff` / 定理 `mul_eq_zero_iff`

English:
theorem mul_eq_zero_iff
  statement: {R : Type*} [AddCommMonoid R]
  proof: by
  simp [← untrop_inj_iff, WithTop.add_eq_top]

中文:
定理 mul_eq_zero_iff
  结论: {R : 类型} [加法交换幺半群 R]
  证明: by
  simp [← untrop_inj_iff, WithTop.add_eq_top]

Depends on / 依赖: WithTop, WithTop.add_eq_top, add_eq_top, untrop_inj_iff
-/
theorem mul_eq_zero_iff {R : Type*} [AddCommMonoid R]
    {a b : Tropical (WithTop R)} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  simp [← untrop_inj_iff, WithTop.add_eq_top]

instance {R : Type*} [AddCommMonoid R] :
    NoZeroDivisors (Tropical (WithTop R)) :=
  ⟨mul_eq_zero_iff.mp⟩

end Semiring

end Tropical
