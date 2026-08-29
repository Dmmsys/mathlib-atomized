/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Order.Hom.Basic
/-!
# Ordered monoid and group homomorphisms

This file defines morphisms between (additive) ordered monoids.

## Types of morphisms

* `OrderAddMonoidHom`: Ordered additive monoid homomorphisms.
* `OrderMonoidHom`: Ordered monoid homomorphisms.
* `OrderAddMonoidIso`: Ordered additive monoid isomorphisms.
* `OrderMonoidIso`: Ordered monoid isomorphisms.

## Notation

* `→+o`: Bundled ordered additive monoid homs. Also use for additive group homs.
* `→*o`: Bundled ordered monoid homs. Also use for group homs.
* `≃+o`: Bundled ordered additive monoid isos. Also use for additive group isos.
* `≃*o`: Bundled ordered monoid isos. Also use for group isos.

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical notation is to use the bundled hom as
a function via this coercion.

There is no `OrderGroupHom` -- the idea is that `OrderMonoidHom` is used.
The constructor for `OrderMonoidHom` needs a proof of `map_one` as well as `map_mul`; a separate
constructor `OrderMonoidHom.mk'` will construct ordered group homs (i.e. ordered monoid homs
between ordered groups) given only a proof that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets. This is done when the
instances can be inferred because they are implicit arguments to the type `OrderMonoidHom`. When
they can be inferred from the type it is faster to use this method than to use type class inference.

### Removed typeclasses

This file used to define typeclasses for order-preserving (additive) monoid homomorphisms:
`OrderAddMonoidHomClass`, `OrderMonoidHomClass`, and `OrderMonoidWithZeroHomClass`.

In https://github.com/leanprover-community/mathlib4/pull/10544 we migrated from these typeclasses
to assumptions like `[FunLike F M N] [MonoidHomClass F M N] [OrderHomClass F M N]`,
making some definitions and lemmas irrelevant.

## Tags

ordered monoid, ordered group
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Function

variable {F α β γ δ : Type*}

section AddMonoid

/--
Definition of `OrderAddMonoidHom` / `OrderAddMonoidHom` 的定义

English:
structure OrderAddMonoidHom
  parameters: (α β : Type*) [Preorder α] [Preorder β] [AddZeroClass α]
  extends: α ->+ β
  axioms and operations (1):
    - monotone' : Monotone toFun

中文:
结构 OrderAddMonoidHom
  参数: (α β : 类型) [Preorder α] [Preorder β] [AddZeroClass α]
  继承: α ->+ β
  公理与运算 (1 个):
    - monotone' : Monotone toFun
-/
structure OrderAddMonoidHom (α β : Type*) [Preorder α] [Preorder β] [AddZeroClass α]
  [AddZeroClass β] extends α ->+ β where
  /-- An `OrderAddMonoidHom` is a monotone function. -/
  monotone' : Monotone toFun

/-- Infix notation for `OrderAddMonoidHom`. -/
infixr:25 " ->+o " => OrderAddMonoidHom

/--
Definition of `OrderAddMonoidIso` / `OrderAddMonoidIso` 的定义

English:
structure OrderAddMonoidIso
  parameters: (α β : Type*) [Preorder α] [Preorder β] [Add α] [Add β]
  extends: α ≃+ β
  axioms and operations (1):
    - map_le_map_iff'({a b : α}) : toFun a <= toFun b ↔ a <= b

中文:
结构 OrderAddMonoidIso
  参数: (α β : 类型) [Preorder α] [Preorder β] [Add α] [Add β]
  继承: α ≃+ β
  公理与运算 (1 个):
    - map_le_map_iff'({a b : α}) : toFun a <= toFun b ↔ a <= b
-/
structure OrderAddMonoidIso (α β : Type*) [Preorder α] [Preorder β] [Add α] [Add β]
  extends α ≃+ β where
  /-- An `OrderAddMonoidIso` respects `≤`. -/
  map_le_map_iff' {a b : α} : toFun a <= toFun b ↔ a <= b

/-- Infix notation for `OrderAddMonoidIso`. -/
infixr:25 " ≃+o " => OrderAddMonoidIso

-- Instances and lemmas are defined below through `@[to_additive]`.
end AddMonoid

section Monoid

/-- `α →*o β` is the type of functions `α → β` that preserve the ordered monoid structure.

`OrderMonoidHom` is also used for ordered group homomorphisms.

When possible, instead of parametrizing results over `(f : α →*o β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [MonoidHomClass F M N] [OrderHomClass F M N] (f : F)`. -/
@[to_additive]
/--
Definition of `OrderMonoidHom` / `OrderMonoidHom` 的定义

English:
structure OrderMonoidHom
  parameters: (α β : Type*) [Preorder α] [Preorder β] [MulOneClass α]
  extends: α ->* β
  axioms and operations (1):
    - monotone' : Monotone toFun

中文:
结构 OrderMonoidHom
  参数: (α β : 类型) [Preorder α] [Preorder β] [MulOneClass α]
  继承: α ->* β
  公理与运算 (1 个):
    - monotone' : Monotone toFun
-/
structure OrderMonoidHom (α β : Type*) [Preorder α] [Preorder β] [MulOneClass α]
  [MulOneClass β] extends α ->* β where
  /-- An `OrderMonoidHom` is a monotone function. -/
  monotone' : Monotone toFun

/-- Infix notation for `OrderMonoidHom`. -/
infixr:25 " ->*o " => OrderMonoidHom

variable [Preorder α] [Preorder β] [MulOneClass α] [MulOneClass β] [FunLike F α β]

/-- Turn an element of a type `F` satisfying `OrderHomClass F α β` and `MonoidHomClass F α β`
into an actual `OrderMonoidHom`. This is declared as the default coercion from `F` to `α →*o β`. -/
@[to_additive (attr := coe)
  /-- Turn an element of a type `F` satisfying `OrderHomClass F α β` and `AddMonoidHomClass F α β`
  into an actual `OrderAddMonoidHom`.
  This is declared as the default coercion from `F` to `α →+o β`. -/]
/--
Definition of `OrderMonoidHomClass.toOrderMonoidHom` / `OrderMonoidHomClass.toOrderMonoidHom` 的定义

English:
definition OrderMonoidHomClass.toOrderMonoidHom
  signature: [OrderHomClass F α β] [MonoidHomClass F α β] (f : F)
  body: { (f : α ->* β) with monotone' := OrderHomClass.monotone f }

中文:
定义 OrderMonoidHomClass.toOrderMonoidHom
  签名: [OrderHomClass F α β] [MonoidHomClass F α β] (f : F)
  定义体: { (f : α ->* β) with monotone' := OrderHomClass.monotone f }

Depends on / 依赖: OrderHomClass, OrderHomClass.monotone, monotone
-/
def OrderMonoidHomClass.toOrderMonoidHom [OrderHomClass F α β] [MonoidHomClass F α β] (f : F) :
    α ->*o β :=
  { (f : α ->* β) with monotone' := OrderHomClass.monotone f }

/-- Any type satisfying `OrderMonoidHomClass` can be cast into `OrderMonoidHom` via
  `OrderMonoidHomClass.toOrderMonoidHom`. -/
@[to_additive /-- Any type satisfying `OrderAddMonoidHomClass` can be cast into `OrderAddMonoidHom`
  via `OrderAddMonoidHomClass.toOrderAddMonoidHom`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [OrderHomClass
  signature: F α β] [MonoidHomClass F α β] : CoeTC F (α ->*o β)
  body: ⟨OrderMonoidHomClass.toOrderMonoidHom⟩

中文:
实例 [OrderHomClass
  签名: F α β] [MonoidHomClass F α β] : CoeTC F (α ->*o β)
  定义体: ⟨OrderMonoidHomClass.toOrderMonoidHom⟩

Depends on / 依赖: OrderMonoidHomClass, OrderMonoidHomClass.toOrderMonoidHom, toOrderMonoidHom
-/
instance [OrderHomClass F α β] [MonoidHomClass F α β] : CoeTC F (α ->*o β) :=
  ⟨OrderMonoidHomClass.toOrderMonoidHom⟩

/-- `α ≃*o β` is the type of isomorphisms `α ≃ β` that preserve the ordered monoid structure.

`OrderMonoidIso` is also used for ordered group isomorphisms.

When possible, instead of parametrizing results over `(f : α ≃*o β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [MulEquivClass F M N] [OrderIsoClass F M N] (f : F)`. -/
@[to_additive]
/--
Definition of `OrderMonoidIso` / `OrderMonoidIso` 的定义

English:
structure OrderMonoidIso
  parameters: (α β : Type*) [Preorder α] [Preorder β] [Mul α] [Mul β]
  extends: α ≃* β
  axioms and operations (1):
    - map_le_map_iff'({a b : α}) : toFun a <= toFun b ↔ a <= b

中文:
结构 OrderMonoidIso
  参数: (α β : 类型) [Preorder α] [Preorder β] [Mul α] [Mul β]
  继承: α ≃* β
  公理与运算 (1 个):
    - map_le_map_iff'({a b : α}) : toFun a <= toFun b ↔ a <= b
-/
structure OrderMonoidIso (α β : Type*) [Preorder α] [Preorder β] [Mul α] [Mul β]
  extends α ≃* β where
  /-- An `OrderMonoidIso` respects `≤`. -/
  map_le_map_iff' {a b : α} : toFun a <= toFun b ↔ a <= b

/-- Infix notation for `OrderMonoidIso`. -/
infixr:25 " ≃*o " => OrderMonoidIso

/-- Turn an element of a type `F` satisfying `OrderIsoClass F α β` and `MulEquivClass F α β`
into an actual `OrderMonoidIso`. This is declared as the default coercion from `F` to `α ≃*o β`. -/
@[to_additive (attr := coe)
  /-- Turn an element of a type `F` satisfying `OrderIsoClass F α β` and `AddEquivClass F α β`
  into an actual `OrderAddMonoidIso`.
  This is declared as the default coercion from `F` to `α ≃+o β`. -/]
/--
Definition of `OrderMonoidIsoClass.toOrderMonoidIso` / `OrderMonoidIsoClass.toOrderMonoidIso` 的定义

English:
definition OrderMonoidIsoClass.toOrderMonoidIso
  signature: [EquivLike F α β] [OrderIsoClass F α β]
  body: { (f : α ≃* β) with map_le_map_iff' := OrderIsoClass.map_le_map_iff f }

中文:
定义 OrderMonoidIsoClass.toOrderMonoidIso
  签名: [EquivLike F α β] [OrderIsoClass F α β]
  定义体: { (f : α ≃* β) with map_le_map_iff' := OrderIsoClass.map_le_map_iff f }

Depends on / 依赖: OrderIsoClass, OrderIsoClass.map_le_map_iff, map_le_map_iff
-/
def OrderMonoidIsoClass.toOrderMonoidIso [EquivLike F α β] [OrderIsoClass F α β]
    [MulEquivClass F α β] (f : F) :
    α ≃*o β :=
  { (f : α ≃* β) with map_le_map_iff' := OrderIsoClass.map_le_map_iff f }

/-- Any type satisfying `OrderMonoidIsoClass` can be cast into `OrderMonoidIso` via
  `OrderMonoidIsoClass.toOrderMonoidIso`. -/
@[to_additive /-- Any type satisfying `OrderAddMonoidIsoClass` can be cast into `OrderAddMonoidIso`
  via `OrderAddMonoidIsoClass.toOrderAddMonoidIso`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EquivLike
  signature: F α β] [OrderIsoClass F α β] [MulEquivClass F α β] : CoeTC F (α ≃*o β)
  body: ⟨OrderMonoidIsoClass.toOrderMonoidIso⟩

中文:
实例 [EquivLike
  签名: F α β] [OrderIsoClass F α β] [MulEquivClass F α β] : CoeTC F (α ≃*o β)
  定义体: ⟨OrderMonoidIsoClass.toOrderMonoidIso⟩

Depends on / 依赖: OrderMonoidIsoClass, OrderMonoidIsoClass.toOrderMonoidIso, toOrderMonoidIso
-/
instance [EquivLike F α β] [OrderIsoClass F α β] [MulEquivClass F α β] : CoeTC F (α ≃*o β) :=
  ⟨OrderMonoidIsoClass.toOrderMonoidIso⟩

end Monoid

section MonoidHomClass

variable [Group α] [Monoid β]
variable {F : Type*} [FunLike F α β] [MonoidHomClass F α β]

@[to_additive]
/--
theorem `map_inv_le_map_inv_iff_map_le_map` / 定理 `map_inv_le_map_inv_iff_map_le_map`

English:
theorem map_inv_le_map_inv_iff_map_le_map
  statement: [LE β] [MulRightMono β] [MulLeftMono β]
  proof: by
  suffices h : forall (f g : F) (x), f x⁻¹ <= g x⁻¹ -> g x <= f x from
    ⟨h f g x, by simpa using h g f x⁻¹⟩
  exact fun f g x hfg => calc
    _ = f x * (f x⁻¹ * g x) := by simp [← mul_assoc, ← map_mul]
    _ <= f x * (g x⁻¹ * g x) := by gcongr
    _ = f x := by simp [← map_mul]

@[to_additive]

中文:
定理 map_inv_le_map_inv_iff_map_le_map
  结论: [LE β] [MulRightMono β] [MulLeftMono β]
  证明: by
  suffices h : forall (f g : F) (x), f x⁻¹ <= g x⁻¹ -> g x <= f x from
    ⟨h f g x, by simpa using h g f x⁻¹⟩
  exact fun f g x hfg => calc
    _ = f x * (f x⁻¹ * g x) := by simp [← mul_assoc, ← map_mul]
    _ <= f x * (g x⁻¹ * g x) := by gcongr
    _ = f x := by simp [← map_mul]

@[to_additive]

Depends on / 依赖: map_mul, mul_assoc
-/
theorem map_inv_le_map_inv_iff_map_le_map [LE β] [MulRightMono β] [MulLeftMono β]
    {f g : F} {x : α} : f x⁻¹ <= g x⁻¹ ↔ g x <= f x := by
  suffices h : forall (f g : F) (x), f x⁻¹ <= g x⁻¹ -> g x <= f x from
    ⟨h f g x, by simpa using h g f x⁻¹⟩
  exact fun f g x hfg => calc
    _ = f x * (f x⁻¹ * g x) := by simp [← mul_assoc, ← map_mul]
    _ <= f x * (g x⁻¹ * g x) := by gcongr
    _ = f x := by simp [← map_mul]

@[to_additive]
/--
theorem `MonoidHomClass.ext_iff_le` / 定理 `MonoidHomClass.ext_iff_le`

English:
theorem MonoidHomClass.ext_iff_le
  given: [PartialOrder β] [MulRightMono β] [MulLeftMono β] {f g : F}
  proof: by simp +contextual
  mpr h := DFunLike.ext f g
    fun x => le_antisymm (h x) (map_inv_le_map_inv_iff_map_le_map.mp <| h x⁻¹)

中文:
定理 MonoidHomClass.ext_iff_le
  条件: [PartialOrder β] [MulRightMono β] [MulLeftMono β] {f g : F}
  证明: by simp +contextual
  mpr h := DFunLike.ext f g
    fun x => le_antisymm (h x) (map_inv_le_map_inv_iff_map_le_map.mp <| h x⁻¹)

Depends on / 依赖: DFunLike, DFunLike.ext, contextual, le_antisymm, map_inv_le_map_inv_iff_map_le_map, map_inv_le_map_inv_iff_map_le_map.mp
-/
theorem MonoidHomClass.ext_iff_le [PartialOrder β] [MulRightMono β] [MulLeftMono β] {f g : F} :
    f = g ↔ forall x, f x <= g x where
  mp := by simp +contextual
  mpr h := DFunLike.ext f g
    fun x => le_antisymm (h x) (map_inv_le_map_inv_iff_map_le_map.mp <| h x⁻¹)

end MonoidHomClass

section OrderedZero

variable [FunLike F α β]
variable [Preorder α] [Zero α] [Preorder β] [Zero β] [OrderHomClass F α β]
  [ZeroHomClass F α β] (f : F) {a : α}

/--
theorem `map_nonneg` / 定理 `map_nonneg`

English:
theorem map_nonneg
  given: (ha : 0 <= a)
  statement: 0 <= f a
  proof: by
  rw [← map_zero f]
  exact OrderHomClass.mono _ ha

中文:
定理 map_nonneg
  条件: (ha : 0 <= a)
  结论: 0 <= f a
  证明: by
  rw [← map_zero f]
  exact OrderHomClass.mono _ ha

Depends on / 依赖: OrderHomClass, OrderHomClass.mono, map_zero
-/
theorem map_nonneg (ha : 0 <= a) : 0 <= f a := by
  rw [← map_zero f]
  exact OrderHomClass.mono _ ha

/--
theorem `map_nonpos` / 定理 `map_nonpos`

English:
theorem map_nonpos
  given: (ha : a <= 0)
  statement: f a <= 0
  proof: by
  rw [← map_zero f]
  exact OrderHomClass.mono _ ha

中文:
定理 map_nonpos
  条件: (ha : a <= 0)
  结论: f a <= 0
  证明: by
  rw [← map_zero f]
  exact OrderHomClass.mono _ ha

Depends on / 依赖: OrderHomClass, OrderHomClass.mono, map_zero
-/
theorem map_nonpos (ha : a <= 0) : f a <= 0 := by
  rw [← map_zero f]
  exact OrderHomClass.mono _ ha

end OrderedZero

section OrderedAddCommGroup

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [i : FunLike F α β]
variable (f : F)

/--
theorem `monotone_iff_map_nonneg` / 定理 `monotone_iff_map_nonneg`

English:
theorem monotone_iff_map_nonneg
  given: [iamhc : AddMonoidHomClass F α β]
  proof: ⟨fun h a => by
    rw [← map_zero f]
    apply h, fun h a b hl => by
    rw [← sub_add_cancel b a]; rw [map_add f]
    exact le_add_of_nonneg_left (h _ <| sub_nonneg.2 hl)⟩

中文:
定理 monotone_iff_map_nonneg
  条件: [iamhc : AddMonoidHomClass F α β]
  证明: ⟨fun h a => by
    rw [← map_zero f]
    apply h, fun h a b hl => by
    rw [← sub_add_cancel b a]; rw [map_add f]
    exact le_add_of_nonneg_left (h _ <| sub_nonneg.2 hl)⟩

Depends on / 依赖: le_add_of_nonneg_left, map_add, map_zero, sub_add_cancel, sub_nonneg
-/
theorem monotone_iff_map_nonneg [iamhc : AddMonoidHomClass F α β] :
    Monotone (f : α -> β) ↔ forall a, 0 <= a -> 0 <= f a :=
  ⟨fun h a => by
    rw [← map_zero f]
    apply h, fun h a b hl => by
    rw [← sub_add_cancel b a]; rw [map_add f]
    exact le_add_of_nonneg_left (h _ <| sub_nonneg.2 hl)⟩

variable [iamhc : AddMonoidHomClass F α β]

/--
theorem `antitone_iff_map_nonpos` / 定理 `antitone_iff_map_nonpos`

English:
theorem antitone_iff_map_nonpos
  statement: Antitone (f : α -> β) ↔ forall a, 0 <= a -> f a <= 0
  proof: monotone_toDual_comp_iff.symm.trans monotone_iff_map_nonneg (β := βᵒᵈ) (iamhc := iamhc) _

中文:
定理 antitone_iff_map_nonpos
  结论: Antitone (f : α -> β) ↔ 对任意 a, 0 <= a -> f a <= 0
  证明: monotone_toDual_comp_iff.symm.trans monotone_iff_map_nonneg (β := βᵒᵈ) (iamhc := iamhc) _

Depends on / 依赖: monotone_iff_map_nonneg, monotone_toDual_comp_iff, monotone_toDual_comp_iff.symm.trans
-/
theorem antitone_iff_map_nonpos : Antitone (f : α -> β) ↔ forall a, 0 <= a -> f a <= 0 :=
monotone_toDual_comp_iff.symm.trans monotone_iff_map_nonneg (β := βᵒᵈ) (iamhc := iamhc) _

/--
theorem `monotone_iff_map_nonpos` / 定理 `monotone_iff_map_nonpos`

English:
theorem monotone_iff_map_nonpos
  statement: Monotone (f : α -> β) ↔ forall a <= 0, f a <= 0
  proof: antitone_comp_ofDual_iff.symm.trans antitone_iff_map_nonpos (α := αᵒᵈ) (iamhc := iamhc) _

中文:
定理 monotone_iff_map_nonpos
  结论: Monotone (f : α -> β) ↔ 对任意 a <= 0, f a <= 0
  证明: antitone_comp_ofDual_iff.symm.trans antitone_iff_map_nonpos (α := αᵒᵈ) (iamhc := iamhc) _

Depends on / 依赖: antitone_comp_ofDual_iff, antitone_comp_ofDual_iff.symm.trans, antitone_iff_map_nonpos
-/
theorem monotone_iff_map_nonpos : Monotone (f : α -> β) ↔ forall a <= 0, f a <= 0 :=
antitone_comp_ofDual_iff.symm.trans antitone_iff_map_nonpos (α := αᵒᵈ) (iamhc := iamhc) _

/--
theorem `antitone_iff_map_nonneg` / 定理 `antitone_iff_map_nonneg`

English:
theorem antitone_iff_map_nonneg
  statement: Antitone (f : α -> β) ↔ forall a <= 0, 0 <= f a
  proof: monotone_comp_ofDual_iff.symm.trans monotone_iff_map_nonneg (α := αᵒᵈ) (iamhc := iamhc) _

中文:
定理 antitone_iff_map_nonneg
  结论: Antitone (f : α -> β) ↔ 对任意 a <= 0, 0 <= f a
  证明: monotone_comp_ofDual_iff.symm.trans monotone_iff_map_nonneg (α := αᵒᵈ) (iamhc := iamhc) _

Depends on / 依赖: monotone_comp_ofDual_iff, monotone_comp_ofDual_iff.symm.trans, monotone_iff_map_nonneg
-/
theorem antitone_iff_map_nonneg : Antitone (f : α -> β) ↔ forall a <= 0, 0 <= f a :=
monotone_comp_ofDual_iff.symm.trans monotone_iff_map_nonneg (α := αᵒᵈ) (iamhc := iamhc) _

/--
theorem `strictMono_iff_map_pos` / 定理 `strictMono_iff_map_pos`

English:
theorem strictMono_iff_map_pos
  proof: by
  refine ⟨fun h a => ?_, fun h a b hl => ?_⟩
  · rw [← map_zero f]
    apply h
  · rw [← sub_add_cancel b a, map_add f]
    exact lt_add_of_pos_left _ (h _ <| sub_pos.2 hl)

中文:
定理 strictMono_iff_map_pos
  证明: by
  refine ⟨fun h a => ?_, fun h a b hl => ?_⟩
  · rw [← map_zero f]
    apply h
  · rw [← sub_add_cancel b a, map_add f]
    exact lt_add_of_pos_left _ (h _ <| sub_pos.2 hl)

Depends on / 依赖: lt_add_of_pos_left, map_add, map_zero, sub_add_cancel, sub_pos
-/
theorem strictMono_iff_map_pos :
    StrictMono (f : α -> β) ↔ forall a, 0 < a -> 0 < f a := by
  refine ⟨fun h a => ?_, fun h a b hl => ?_⟩
  · rw [← map_zero f]
    apply h
  · rw [← sub_add_cancel b a, map_add f]
    exact lt_add_of_pos_left _ (h _ <| sub_pos.2 hl)

/--
theorem `strictAnti_iff_map_neg` / 定理 `strictAnti_iff_map_neg`

English:
theorem strictAnti_iff_map_neg
  statement: StrictAnti (f : α -> β) ↔ forall a, 0 < a -> f a < 0
  proof: strictMono_toDual_comp_iff.symm.trans strictMono_iff_map_pos (β := βᵒᵈ) (iamhc := iamhc) _

中文:
定理 strictAnti_iff_map_neg
  结论: StrictAnti (f : α -> β) ↔ 对任意 a, 0 < a -> f a < 0
  证明: strictMono_toDual_comp_iff.symm.trans strictMono_iff_map_pos (β := βᵒᵈ) (iamhc := iamhc) _

Depends on / 依赖: strictMono_iff_map_pos, strictMono_toDual_comp_iff, strictMono_toDual_comp_iff.symm.trans
-/
theorem strictAnti_iff_map_neg : StrictAnti (f : α -> β) ↔ forall a, 0 < a -> f a < 0 :=
strictMono_toDual_comp_iff.symm.trans strictMono_iff_map_pos (β := βᵒᵈ) (iamhc := iamhc) _

/--
theorem `strictMono_iff_map_neg` / 定理 `strictMono_iff_map_neg`

English:
theorem strictMono_iff_map_neg
  statement: StrictMono (f : α -> β) ↔ forall a < 0, f a < 0
  proof: strictAnti_comp_ofDual_iff.symm.trans strictAnti_iff_map_neg (α := αᵒᵈ) (iamhc := iamhc) _

中文:
定理 strictMono_iff_map_neg
  结论: StrictMono (f : α -> β) ↔ 对任意 a < 0, f a < 0
  证明: strictAnti_comp_ofDual_iff.symm.trans strictAnti_iff_map_neg (α := αᵒᵈ) (iamhc := iamhc) _

Depends on / 依赖: strictAnti_comp_ofDual_iff, strictAnti_comp_ofDual_iff.symm.trans, strictAnti_iff_map_neg
-/
theorem strictMono_iff_map_neg : StrictMono (f : α -> β) ↔ forall a < 0, f a < 0 :=
strictAnti_comp_ofDual_iff.symm.trans strictAnti_iff_map_neg (α := αᵒᵈ) (iamhc := iamhc) _

/--
theorem `strictAnti_iff_map_pos` / 定理 `strictAnti_iff_map_pos`

English:
theorem strictAnti_iff_map_pos
  statement: StrictAnti (f : α -> β) ↔ forall a < 0, 0 < f a
  proof: strictMono_comp_ofDual_iff.symm.trans strictMono_iff_map_pos (α := αᵒᵈ) (iamhc := iamhc) _

中文:
定理 strictAnti_iff_map_pos
  结论: StrictAnti (f : α -> β) ↔ 对任意 a < 0, 0 < f a
  证明: strictMono_comp_ofDual_iff.symm.trans strictMono_iff_map_pos (α := αᵒᵈ) (iamhc := iamhc) _

Depends on / 依赖: strictMono_comp_ofDual_iff, strictMono_comp_ofDual_iff.symm.trans, strictMono_iff_map_pos
-/
theorem strictAnti_iff_map_pos : StrictAnti (f : α -> β) ↔ forall a < 0, 0 < f a :=
strictMono_comp_ofDual_iff.symm.trans strictMono_iff_map_pos (α := αᵒᵈ) (iamhc := iamhc) _

end OrderedAddCommGroup

namespace OrderMonoidHom

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α ->*o β}

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (α ->*o β) α β
  body: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr

initialize_simps_projections OrderAddMonoidHom (toFun -> apply, -toAddMonoidHom)
initialize_simps_projections OrderMonoidHom (toFun -> apply, -toMonoidHom)

@[to_additive]

中文:
实例 :
  签名: FunLike (α ->*o β) α β
  定义体: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr

initialize_simps_projections OrderAddMonoidHom (toFun -> apply, -toAddMonoidHom)
initialize_simps_projections OrderMonoidHom (toFun -> apply, -toMonoidHom)

@[to_additive]

Depends on / 依赖: f.toFun
-/
instance : FunLike (α ->*o β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr

initialize_simps_projections OrderAddMonoidHom (toFun -> apply, -toAddMonoidHom)
initialize_simps_projections OrderMonoidHom (toFun -> apply, -toMonoidHom)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderHomClass (α ->*o β) α β
  body: f.monotone' h

@[to_additive]

中文:
实例 :
  签名: OrderHomClass (α ->*o β) α β
  定义体: f.monotone' h

@[to_additive]

Depends on / 依赖: f.monotone, monotone
-/
instance : OrderHomClass (α ->*o β) α β where
  map_rel f _ _ h := f.monotone' h

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidHomClass (α ->*o β) α β
  body: f.map_mul'
  map_one f := f.map_one'

中文:
实例 :
  签名: MonoidHomClass (α ->*o β) α β
  定义体: f.map_mul'
  map_one f := f.map_one'

Depends on / 依赖: f.map_mul, map_mul
-/
instance : MonoidHomClass (α ->*o β) α β where
  map_mul f := f.map_mul'
  map_one f := f.map_one'

-- Other lemmas should be accessed through the `FunLike` API
@[to_additive (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

@[to_additive]

中文:
定理 ext
  条件: (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[to_additive]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : α ->*o β)
  statement: f.toFun = (f : α -> β)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toFun_eq_coe
  条件: (f : α ->*o β)
  结论: f.toFun = (f : α -> β)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toFun_eq_coe (f : α ->*o β) : f.toFun = (f : α -> β) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : α ->* β) (h)
  statement: (OrderMonoidHom.mk f h : α -> β) = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mk
  条件: (f : α ->* β) (h)
  结论: (OrderMonoidHom.mk f h : α -> β) = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mk (f : α ->* β) (h) : (OrderMonoidHom.mk f h : α -> β) = f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : α ->*o β) (h)
  statement: OrderMonoidHom.mk (f : α ->* β) h = f
  proof: by
  ext
  rfl

中文:
定理 mk_coe
  条件: (f : α ->*o β) (h)
  结论: OrderMonoidHom.mk (f : α ->* β) h = f
  证明: by
  ext
  rfl
-/
theorem mk_coe (f : α ->*o β) (h) : OrderMonoidHom.mk (f : α ->* β) h = f := by
  ext
  rfl

/-- Reinterpret an ordered monoid homomorphism as an order homomorphism. -/
@[to_additive /-- Reinterpret an ordered additive monoid homomorphism as an order homomorphism. -/]
/--
Definition of `toOrderHom` / `toOrderHom` 的定义

English:
definition toOrderHom
  signature: (f : α ->*o β)
  body: { f with }

@[to_additive (attr := simp)]

中文:
定义 toOrderHom
  签名: (f : α ->*o β)
  定义体: { f with }

@[to_additive (attr := simp)]
-/
def toOrderHom (f : α ->*o β) : α ->o β :=
  { f with }

@[to_additive (attr := simp)]
/--
theorem `coe_monoidHom` / 定理 `coe_monoidHom`

English:
theorem coe_monoidHom
  given: (f : α ->*o β)
  statement: ((f : α ->* β) : α -> β) = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_monoidHom
  条件: (f : α ->*o β)
  结论: ((f : α ->* β) : α -> β) = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_monoidHom (f : α ->*o β) : ((f : α ->* β) : α -> β) = f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_orderHom` / 定理 `coe_orderHom`

English:
theorem coe_orderHom
  given: (f : α ->*o β)
  statement: ((f : α ->o β) : α -> β) = f
  proof: rfl

@[to_additive]

中文:
定理 coe_orderHom
  条件: (f : α ->*o β)
  结论: ((f : α ->o β) : α -> β) = f
  证明: rfl

@[to_additive]
-/
theorem coe_orderHom (f : α ->*o β) : ((f : α ->o β) : α -> β) = f :=
  rfl

@[to_additive]
/--
theorem `toMonoidHom_injective` / 定理 `toMonoidHom_injective`

English:
theorem toMonoidHom_injective
  statement: Injective (toMonoidHom : _ -> α ->* β)
  proof: fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0

@[to_additive]

中文:
定理 toMonoidHom_injective
  结论: Injective (toMonoidHom : _ -> α ->* β)
  证明: fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0

@[to_additive]
-/
theorem toMonoidHom_injective : Injective (toMonoidHom : _ -> α ->* β) := fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0

@[to_additive]
/--
theorem `toOrderHom_injective` / 定理 `toOrderHom_injective`

English:
theorem toOrderHom_injective
  statement: Injective (toOrderHom : _ -> α ->o β)
  proof: fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0

中文:
定理 toOrderHom_injective
  结论: Injective (toOrderHom : _ -> α ->o β)
  证明: fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0
-/
theorem toOrderHom_injective : Injective (toOrderHom : _ -> α ->o β) := fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0

/-- Copy of an `OrderMonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
@[to_additive /-- Copy of an `OrderAddMonoidHom` with a new `toFun` equal to the old one. Useful to
fix definitional equalities. -/]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : α ->*o β) (f' : α -> β) (h : f' = f)
  body: { f.toMonoidHom.copy f' h with toFun := f', monotone' := h.symm.subst f.monotone' }

@[to_additive (attr := simp)]

中文:
定义 copy
  签名: (f : α ->*o β) (f' : α -> β) (h : f' = f)
  定义体: { f.toMonoidHom.copy f' h with toFun := f', monotone' := h.symm.subst f.monotone' }

@[to_additive (attr := simp)]
-/
protected def copy (f : α ->*o β) (f' : α -> β) (h : f' = f) : α ->*o β :=
  { f.toMonoidHom.copy f' h with toFun := f', monotone' := h.symm.subst f.monotone' }

@[to_additive (attr := simp)]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : α ->*o β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

@[to_additive]

中文:
定理 coe_copy
  条件: (f : α ->*o β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl

@[to_additive]
-/
theorem coe_copy (f : α ->*o β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

@[to_additive]
/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : α ->*o β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : α ->*o β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : α ->*o β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- The identity map as an ordered monoid homomorphism. -/
@[to_additive /-- The identity map as an ordered additive monoid homomorphism. -/]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : α ->*o α
  body: { MonoidHom.id α, OrderHom.id with }

@[to_additive (attr := simp)]

中文:
定义 id
  签名: : α ->*o α
  定义体: { MonoidHom.id α, OrderHom.id with }

@[to_additive (attr := simp)]
-/
protected def id : α ->*o α :=
  { MonoidHom.id α, OrderHom.id with }

@[to_additive (attr := simp)]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(OrderMonoidHom.id α) = id
  proof: rfl

@[to_additive]

中文:
定理 coe_id
  结论: ⇑(OrderMonoidHom.id α) = id
  证明: rfl

@[to_additive]
-/
theorem coe_id : ⇑(OrderMonoidHom.id α) = id :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (α ->*o α)
  body: ⟨OrderMonoidHom.id α⟩

中文:
实例 :
  签名: Inhabited (α ->*o α)
  定义体: ⟨OrderMonoidHom.id α⟩

Depends on / 依赖: OrderMonoidHom, OrderMonoidHom.id
-/
instance : Inhabited (α ->*o α) :=
  ⟨OrderMonoidHom.id α⟩

variable {α}

/-- Composition of `OrderMonoidHom`s as an `OrderMonoidHom`. -/
@[to_additive /-- Composition of `OrderAddMonoidHom`s as an `OrderAddMonoidHom` -/]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : β ->*o γ) (g : α ->*o β)
  body: { f.toMonoidHom.comp (g : α ->* β), f.toOrderHom.comp (g : α ->o β) with }

@[to_additive (attr := simp)]

中文:
定义 comp
  签名: (f : β ->*o γ) (g : α ->*o β)
  定义体: { f.toMonoidHom.comp (g : α ->* β), f.toOrderHom.comp (g : α ->o β) with }

@[to_additive (attr := simp)]

Depends on / 依赖: f.toMonoidHom.comp, f.toOrderHom.comp, toMonoidHom, toOrderHom
-/
def comp (f : β ->*o γ) (g : α ->*o β) : α ->*o γ :=
  { f.toMonoidHom.comp (g : α ->* β), f.toOrderHom.comp (g : α ->o β) with }

@[to_additive (attr := simp)]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : β ->*o γ) (g : α ->*o β)
  statement: (f.comp g : α -> γ) = f ∘ g
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_comp
  条件: (f : β ->*o γ) (g : α ->*o β)
  结论: (f.comp g : α -> γ) = f ∘ g
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_comp (f : β ->*o γ) (g : α ->*o β) : (f.comp g : α -> γ) = f ∘ g :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : β ->*o γ) (g : α ->*o β) (a : α)
  statement: (f.comp g) a = f (g a)
  proof: rfl

@[to_additive]

中文:
定理 comp_apply
  条件: (f : β ->*o γ) (g : α ->*o β) (a : α)
  结论: (f.comp g) a = f (g a)
  证明: rfl

@[to_additive]
-/
theorem comp_apply (f : β ->*o γ) (g : α ->*o β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_additive]
/--
theorem `coe_comp_monoidHom` / 定理 `coe_comp_monoidHom`

English:
theorem coe_comp_monoidHom
  given: (f : β ->*o γ) (g : α ->*o β)
  proof: rfl

@[to_additive]

中文:
定理 coe_comp_monoidHom
  条件: (f : β ->*o γ) (g : α ->*o β)
  证明: rfl

@[to_additive]
-/
theorem coe_comp_monoidHom (f : β ->*o γ) (g : α ->*o β) :
    (f.comp g : α ->* γ) = (f : β ->* γ).comp g :=
  rfl

@[to_additive]
/--
theorem `coe_comp_orderHom` / 定理 `coe_comp_orderHom`

English:
theorem coe_comp_orderHom
  given: (f : β ->*o γ) (g : α ->*o β)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_comp_orderHom
  条件: (f : β ->*o γ) (g : α ->*o β)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_comp_orderHom (f : β ->*o γ) (g : α ->*o β) :
    (f.comp g : α ->o γ) = (f : β ->o γ).comp g :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : γ ->*o δ) (g : β ->*o γ) (h : α ->*o β)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 comp_assoc
  条件: (f : γ ->*o δ) (g : β ->*o γ) (h : α ->*o β)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem comp_assoc (f : γ ->*o δ) (g : β ->*o γ) (h : α ->*o β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : α ->*o β)
  statement: f.comp (OrderMonoidHom.id α) = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 comp_id
  条件: (f : α ->*o β)
  结论: f.comp (OrderMonoidHom.id α) = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem comp_id (f : α ->*o β) : f.comp (OrderMonoidHom.id α) = f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : α ->*o β)
  statement: (OrderMonoidHom.id β).comp f = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 id_comp
  条件: (f : α ->*o β)
  结论: (OrderMonoidHom.id β).comp f = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem id_comp (f : α ->*o β) : (OrderMonoidHom.id β).comp f = f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : β ->*o γ} {f : α ->*o β} (hf : Function.Surjective f)
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun _ => by congr⟩

@[to_additive (attr := simp)]

中文:
定理 cancel_right
  条件: {g₁ g₂ : β ->*o γ} {f : α ->*o β} (hf : Function.Surjective f)
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun _ => by congr⟩

@[to_additive (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : β ->*o γ} {f : α ->*o β} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun _ => by congr⟩

@[to_additive (attr := simp)]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : β ->*o γ} {f₁ f₂ : α ->*o β} (hg : Function.Injective g)
  proof: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : β ->*o γ} {f₁ f₂ : α ->*o β} (hg : Function.Injective g)
  证明: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {g : β ->*o γ} {f₁ f₂ : α ->*o β} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

/-- `1` is the homomorphism sending all elements to `1`. -/
@[to_additive /-- `0` is the homomorphism sending all elements to `0`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (α ->*o β)
  body: ⟨{ (1 : α ->* β) with monotone' := monotone_const }⟩

@[to_additive (attr := simp)]

中文:
实例 :
  签名: One (α ->*o β)
  定义体: ⟨{ (1 : α ->* β) with monotone' := monotone_const }⟩

@[to_additive (attr := simp)]

Depends on / 依赖: monotone, monotone_const
-/
instance : One (α ->*o β) :=
  ⟨{ (1 : α ->* β) with monotone' := monotone_const }⟩

@[to_additive (attr := simp)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : α ->*o β) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_one
  结论: ⇑(1 : α ->*o β) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_one : ⇑(1 : α ->*o β) = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (a : α)
  statement: (1 : α ->*o β) a = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 one_apply
  条件: (a : α)
  结论: (1 : α ->*o β) a = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem one_apply (a : α) : (1 : α ->*o β) a = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `one_comp` / 定理 `one_comp`

English:
theorem one_comp
  given: (f : α ->*o β)
  statement: (1 : β ->*o γ).comp f = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 one_comp
  条件: (f : α ->*o β)
  结论: (1 : β ->*o γ).comp f = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem one_comp (f : α ->*o β) : (1 : β ->*o γ).comp f = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comp_one` / 定理 `comp_one`

English:
theorem comp_one
  given: (f : β ->*o γ)
  statement: f.comp (1 : α ->*o β) = 1
  proof: ext fun _ => map_one f

中文:
定理 comp_one
  条件: (f : β ->*o γ)
  结论: f.comp (1 : α ->*o β) = 1
  证明: ext fun _ => map_one f

Depends on / 依赖: map_one
-/
theorem comp_one (f : β ->*o γ) : f.comp (1 : α ->*o β) = 1 :=
  ext fun _ => map_one f

end Preorder

section Mul

variable [CommMonoid α] [Preorder α]
  [CommMonoid β] [Preorder β]
  [CommMonoid γ] [Preorder γ]

/-- For two ordered monoid morphisms `f` and `g`, their product is the ordered monoid morphism
sending `a` to `f a * g a`. -/
@[to_additive /-- For two ordered additive monoid morphisms `f` and `g`, their product is the
ordered additive monoid morphism sending `a` to `f a + g a`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsOrderedMonoid
  signature: β] : Mul (α ->*o β)
  body: ⟨fun f g => { (f * g : α ->* β) with monotone' := f.monotone'.mul' g.monotone' }⟩

@[to_additive (attr := simp)]

中文:
实例 [IsOrderedMonoid
  签名: β] : Mul (α ->*o β)
  定义体: ⟨fun f g => { (f * g : α ->* β) with monotone' := f.monotone'.mul' g.monotone' }⟩

@[to_additive (attr := simp)]

Depends on / 依赖: f.monotone, g.monotone, monotone
-/
instance [IsOrderedMonoid β] : Mul (α ->*o β) :=
  ⟨fun f g => { (f * g : α ->* β) with monotone' := f.monotone'.mul' g.monotone' }⟩

@[to_additive (attr := simp)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: [IsOrderedMonoid β] (f g : α ->*o β)
  statement: ⇑(f * g) = f * g
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mul
  条件: [IsOrderedMonoid β] (f g : α ->*o β)
  结论: ⇑(f * g) = f * g
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mul [IsOrderedMonoid β] (f g : α ->*o β) : ⇑(f * g) = f * g :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: [IsOrderedMonoid β] (f g : α ->*o β) (a : α)
  statement: (f * g) a = f a * g a
  proof: rfl

@[to_additive]

中文:
定理 mul_apply
  条件: [IsOrderedMonoid β] (f g : α ->*o β) (a : α)
  结论: (f * g) a = f a * g a
  证明: rfl

@[to_additive]
-/
theorem mul_apply [IsOrderedMonoid β] (f g : α ->*o β) (a : α) : (f * g) a = f a * g a :=
  rfl

@[to_additive]
/--
theorem `mul_comp` / 定理 `mul_comp`

English:
theorem mul_comp
  given: [IsOrderedMonoid γ] (g₁ g₂ : β ->*o γ) (f : α ->*o β)
  proof: rfl

@[to_additive]

中文:
定理 mul_comp
  条件: [IsOrderedMonoid γ] (g₁ g₂ : β ->*o γ) (f : α ->*o β)
  证明: rfl

@[to_additive]
-/
theorem mul_comp [IsOrderedMonoid γ] (g₁ g₂ : β ->*o γ) (f : α ->*o β) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl

@[to_additive]
/--
theorem `comp_mul` / 定理 `comp_mul`

English:
theorem comp_mul
  given: [IsOrderedMonoid β] [IsOrderedMonoid γ] (g : β ->*o γ) (f₁ f₂ : α ->*o β)
  proof: ext fun _ => map_mul g _ _

中文:
定理 comp_mul
  条件: [IsOrderedMonoid β] [IsOrderedMonoid γ] (g : β ->*o γ) (f₁ f₂ : α ->*o β)
  证明: ext fun _ => map_mul g _ _

Depends on / 依赖: map_mul
-/
theorem comp_mul [IsOrderedMonoid β] [IsOrderedMonoid γ] (g : β ->*o γ) (f₁ f₂ : α ->*o β) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
  ext fun _ => map_mul g _ _

end Mul

section OrderedCommMonoid

variable {_ : Preorder α} {_ : Preorder β} {_ : MulOneClass α} {_ : MulOneClass β}

@[to_additive (attr := simp)]
/--
theorem `toMonoidHom_eq_coe` / 定理 `toMonoidHom_eq_coe`

English:
theorem toMonoidHom_eq_coe
  given: (f : α ->*o β)
  statement: f.toMonoidHom = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toMonoidHom_eq_coe
  条件: (f : α ->*o β)
  结论: f.toMonoidHom = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toMonoidHom_eq_coe (f : α ->*o β) : f.toMonoidHom = f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `toOrderHom_eq_coe` / 定理 `toOrderHom_eq_coe`

English:
theorem toOrderHom_eq_coe
  given: (f : α ->*o β)
  statement: f.toOrderHom = f
  proof: rfl

中文:
定理 toOrderHom_eq_coe
  条件: (f : α ->*o β)
  结论: f.toOrderHom = f
  证明: rfl
-/
theorem toOrderHom_eq_coe (f : α ->*o β) : f.toOrderHom = f :=
  rfl

end OrderedCommMonoid

section OrderedCommGroup

variable {_ : CommGroup α} {_ : Preorder α} {_ : CommGroup β} {_ : PartialOrder β}

/-- Makes an ordered group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive
      /-- Makes an ordered additive group homomorphism from a proof that the map preserves
      addition. -/]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (f : α -> β) (hf : Monotone f) (map_mul : forall a b : α, f (a * b) = f a * f b)
  body: { MonoidHom.mk' f map_mul with monotone' := hf }

中文:
定义 mk'
  签名: (f : α -> β) (hf : Monotone f) (map_mul : 对任意 a b : α, f (a * b) = f a * f b)
  定义体: { MonoidHom.mk' f map_mul with monotone' := hf }

Depends on / 依赖: MonoidHom, MonoidHom.mk, map_mul, monotone
-/
def mk' (f : α -> β) (hf : Monotone f) (map_mul : forall a b : α, f (a * b) = f a * f b) : α ->*o β :=
  { MonoidHom.mk' f map_mul with monotone' := hf }

end OrderedCommGroup

end OrderMonoidHom

namespace OrderMonoidIso

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (α ≃*o β) α β
  body: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr

@[to_additive]

中文:
实例 :
  签名: EquivLike (α ≃*o β) α β
  定义体: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr

@[to_additive]

Depends on / 依赖: f.toFun
-/
instance : EquivLike (α ≃*o β) α β where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderIsoClass (α ≃*o β) α β
  body: f.map_le_map_iff'

@[to_additive]

中文:
实例 :
  签名: OrderIsoClass (α ≃*o β) α β
  定义体: f.map_le_map_iff'

@[to_additive]

Depends on / 依赖: f.map_le_map_iff, map_le_map_iff
-/
instance : OrderIsoClass (α ≃*o β) α β where
  map_le_map_iff f := f.map_le_map_iff'

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulEquivClass (α ≃*o β) α β
  body: map_mul f.toMulEquiv

中文:
实例 :
  签名: MulEquivClass (α ≃*o β) α β
  定义体: map_mul f.toMulEquiv

Depends on / 依赖: f.toMulEquiv, map_mul, toMulEquiv
-/
instance : MulEquivClass (α ≃*o β) α β where
  map_mul f := map_mul f.toMulEquiv

-- Other lemmas should be accessed through the `FunLike` API
@[to_additive (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

@[to_additive]

中文:
定理 ext
  条件: (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[to_additive]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : α ≃*o β)
  statement: f.toFun = (f : α -> β)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toFun_eq_coe
  条件: (f : α ≃*o β)
  结论: f.toFun = (f : α -> β)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toFun_eq_coe (f : α ≃*o β) : f.toFun = (f : α -> β) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : α ≃* β) (h)
  statement: (OrderMonoidIso.mk f h : α -> β) = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mk
  条件: (f : α ≃* β) (h)
  结论: (OrderMonoidIso.mk f h : α -> β) = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mk (f : α ≃* β) (h) : (OrderMonoidIso.mk f h : α -> β) = f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : α ≃*o β) (h)
  statement: OrderMonoidIso.mk (f : α ≃* β) h = f
  proof: rfl

中文:
定理 mk_coe
  条件: (f : α ≃*o β) (h)
  结论: OrderMonoidIso.mk (f : α ≃* β) h = f
  证明: rfl
-/
theorem mk_coe (f : α ≃*o β) (h) : OrderMonoidIso.mk (f : α ≃* β) h = f := rfl

/-- Reinterpret an ordered monoid isomorphism as an order isomorphism. -/
@[to_additive
/-- Reinterpret an ordered additive monoid isomorphism as an order isomorphism. -/]
/--
Definition of `toOrderIso` / `toOrderIso` 的定义

English:
definition toOrderIso
  signature: (f : α ≃*o β)
  body: { f with
    map_rel_iff' := map_le_map_iff f }

@[to_additive (attr := simp)]

中文:
定义 toOrderIso
  签名: (f : α ≃*o β)
  定义体: { f with
    map_rel_iff' := map_le_map_iff f }

@[to_additive (attr := simp)]

Depends on / 依赖: map_le_map_iff, map_rel_iff
-/
def toOrderIso (f : α ≃*o β) : α ≃o β :=
  { f with
    map_rel_iff' := map_le_map_iff f }

@[to_additive (attr := simp)]
/--
theorem `coe_mulEquiv` / 定理 `coe_mulEquiv`

English:
theorem coe_mulEquiv
  given: (f : α ≃*o β)
  statement: ((f : α ≃* β) : α -> β) = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mulEquiv
  条件: (f : α ≃*o β)
  结论: ((f : α ≃* β) : α -> β) = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mulEquiv (f : α ≃*o β) : ((f : α ≃* β) : α -> β) = f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_orderIso` / 定理 `coe_orderIso`

English:
theorem coe_orderIso
  given: (f : α ≃*o β)
  statement: ((f : α ->o β) : α -> β) = f
  proof: rfl

@[to_additive]

中文:
定理 coe_orderIso
  条件: (f : α ≃*o β)
  结论: ((f : α ->o β) : α -> β) = f
  证明: rfl

@[to_additive]
-/
theorem coe_orderIso (f : α ≃*o β) : ((f : α ->o β) : α -> β) = f :=
  rfl

@[to_additive]
/--
theorem `toMulEquiv_injective` / 定理 `toMulEquiv_injective`

English:
theorem toMulEquiv_injective
  statement: Injective (toMulEquiv : _ -> α ≃* β)
  proof: fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0

@[to_additive]

中文:
定理 toMulEquiv_injective
  结论: Injective (toMulEquiv : _ -> α ≃* β)
  证明: fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0

@[to_additive]
-/
theorem toMulEquiv_injective : Injective (toMulEquiv : _ -> α ≃* β) := fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0

@[to_additive]
/--
theorem `toOrderIso_injective` / 定理 `toOrderIso_injective`

English:
theorem toOrderIso_injective
  statement: Injective (toOrderIso : _ -> α ≃o β)
  proof: fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0

中文:
定理 toOrderIso_injective
  结论: Injective (toOrderIso : _ -> α ≃o β)
  证明: fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0
-/
theorem toOrderIso_injective : Injective (toOrderIso : _ -> α ≃o β) := fun f g h =>
ext by convert! DFunLike.ext_iff.1 h using 0

variable (α)

/-- The identity map as an ordered monoid isomorphism. -/
@[to_additive /-- The identity map as an ordered additive monoid isomorphism. -/]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : α ≃*o α
  body: { MulEquiv.refl α with map_le_map_iff' := by simp }

@[to_additive (attr := simp)]

中文:
定义 refl
  签名: : α ≃*o α
  定义体: { MulEquiv.refl α with map_le_map_iff' := by simp }

@[to_additive (attr := simp)]
-/
protected def refl : α ≃*o α :=
  { MulEquiv.refl α with map_le_map_iff' := by simp }

@[to_additive (attr := simp)]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: ⇑(OrderMonoidIso.refl α) = id
  proof: rfl

@[to_additive]

中文:
定理 coe_refl
  结论: ⇑(OrderMonoidIso.refl α) = id
  证明: rfl

@[to_additive]
-/
theorem coe_refl : ⇑(OrderMonoidIso.refl α) = id :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (α ≃*o α)
  body: ⟨OrderMonoidIso.refl α⟩

中文:
实例 :
  签名: Inhabited (α ≃*o α)
  定义体: ⟨OrderMonoidIso.refl α⟩

Depends on / 依赖: OrderMonoidIso, OrderMonoidIso.refl
-/
instance : Inhabited (α ≃*o α) :=
  ⟨OrderMonoidIso.refl α⟩

variable {α}

/-- Transitivity of multiplication-preserving order isomorphisms -/
@[to_additive (attr := trans) /-- Transitivity of addition-preserving order isomorphisms -/]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (f : α ≃*o β) (g : β ≃*o γ)
  body: { (f : α ≃* β).trans g with map_le_map_iff' := by simp }

@[to_additive (attr := simp)]

中文:
定义 trans
  签名: (f : α ≃*o β) (g : β ≃*o γ)
  定义体: { (f : α ≃* β).trans g with map_le_map_iff' := by simp }

@[to_additive (attr := simp)]

Depends on / 依赖: map_le_map_iff
-/
def trans (f : α ≃*o β) (g : β ≃*o γ) : α ≃*o γ :=
  { (f : α ≃* β).trans g with map_le_map_iff' := by simp }

@[to_additive (attr := simp)]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (f : α ≃*o β) (g : β ≃*o γ)
  statement: (f.trans g : α -> γ) = g ∘ f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_trans
  条件: (f : α ≃*o β) (g : β ≃*o γ)
  结论: (f.trans g : α -> γ) = g ∘ f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_trans (f : α ≃*o β) (g : β ≃*o γ) : (f.trans g : α -> γ) = g ∘ f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (f : α ≃*o β) (g : β ≃*o γ) (a : α)
  statement: (f.trans g) a = g (f a)
  proof: rfl

@[to_additive]

中文:
定理 trans_apply
  条件: (f : α ≃*o β) (g : β ≃*o γ) (a : α)
  结论: (f.trans g) a = g (f a)
  证明: rfl

@[to_additive]
-/
theorem trans_apply (f : α ≃*o β) (g : β ≃*o γ) (a : α) : (f.trans g) a = g (f a) :=
  rfl

@[to_additive]
/--
theorem `coe_trans_mulEquiv` / 定理 `coe_trans_mulEquiv`

English:
theorem coe_trans_mulEquiv
  given: (f : α ≃*o β) (g : β ≃*o γ)
  proof: rfl

@[to_additive]

中文:
定理 coe_trans_mulEquiv
  条件: (f : α ≃*o β) (g : β ≃*o γ)
  证明: rfl

@[to_additive]
-/
theorem coe_trans_mulEquiv (f : α ≃*o β) (g : β ≃*o γ) :
    (f.trans g : α ≃* γ) = (f : α ≃* β).trans g :=
  rfl

@[to_additive]
/--
theorem `coe_trans_orderIso` / 定理 `coe_trans_orderIso`

English:
theorem coe_trans_orderIso
  given: (f : α ≃*o β) (g : β ≃*o γ)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_trans_orderIso
  条件: (f : α ≃*o β) (g : β ≃*o γ)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_trans_orderIso (f : α ≃*o β) (g : β ≃*o γ) :
    (f.trans g : α ≃o γ) = (f : α ≃o β).trans g :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  given: (f : α ≃*o β) (g : β ≃*o γ) (h : γ ≃*o δ)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 trans_assoc
  条件: (f : α ≃*o β) (g : β ≃*o γ) (h : γ ≃*o δ)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem trans_assoc (f : α ≃*o β) (g : β ≃*o γ) (h : γ ≃*o δ) :
    (f.trans g).trans h = f.trans (g.trans h) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  given: (f : α ≃*o β)
  statement: f.trans (OrderMonoidIso.refl β) = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 trans_refl
  条件: (f : α ≃*o β)
  结论: f.trans (OrderMonoidIso.refl β) = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem trans_refl (f : α ≃*o β) : f.trans (OrderMonoidIso.refl β) = f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  given: (f : α ≃*o β)
  statement: (OrderMonoidIso.refl α).trans f = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 refl_trans
  条件: (f : α ≃*o β)
  结论: (OrderMonoidIso.refl α).trans f = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem refl_trans (f : α ≃*o β) : (OrderMonoidIso.refl α).trans f = f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : α ≃*o β} {f : β ≃*o γ} (hf : Function.Injective f)
  proof: ⟨fun h => ext fun a => hf by rw [← trans_apply, h, trans_apply], by rintro rfl; rfl⟩

@[to_additive (attr := simp)]

中文:
定理 cancel_right
  条件: {g₁ g₂ : α ≃*o β} {f : β ≃*o γ} (hf : Function.Injective f)
  证明: ⟨fun h => ext fun a => hf by rw [← trans_apply, h, trans_apply], by rintro rfl; rfl⟩

@[to_additive (attr := simp)]

Depends on / 依赖: trans_apply
-/
theorem cancel_right {g₁ g₂ : α ≃*o β} {f : β ≃*o γ} (hf : Function.Injective f) :
    g₁.trans f = g₂.trans f ↔ g₁ = g₂ :=
⟨fun h => ext fun a => hf by rw [← trans_apply, h, trans_apply], by rintro rfl; rfl⟩

@[to_additive (attr := simp)]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : α ≃*o β} {f₁ f₂ : β ≃*o γ} (hg : Function.Surjective g)
  proof: ⟨fun h => ext hg.forall.2 DFunLike.ext_iff.1 h, fun _ => by congr⟩

@[to_additive (attr := simp)]

中文:
定理 cancel_left
  条件: {g : α ≃*o β} {f₁ f₂ : β ≃*o γ} (hg : Function.Surjective g)
  证明: ⟨fun h => ext hg.forall.2 DFunLike.ext_iff.1 h, fun _ => by congr⟩

@[to_additive (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, hg.forall
-/
theorem cancel_left {g : α ≃*o β} {f₁ f₂ : β ≃*o γ} (hg : Function.Surjective g) :
    g.trans f₁ = g.trans f₂ ↔ f₁ = f₂ :=
⟨fun h => ext hg.forall.2 DFunLike.ext_iff.1 h, fun _ => by congr⟩

@[to_additive (attr := simp)]
/--
theorem `toMulEquiv_eq_coe` / 定理 `toMulEquiv_eq_coe`

English:
theorem toMulEquiv_eq_coe
  given: (f : α ≃*o β)
  statement: f.toMulEquiv = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toMulEquiv_eq_coe
  条件: (f : α ≃*o β)
  结论: f.toMulEquiv = f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toMulEquiv_eq_coe (f : α ≃*o β) : f.toMulEquiv = f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `toOrderIso_eq_coe` / 定理 `toOrderIso_eq_coe`

English:
theorem toOrderIso_eq_coe
  given: (f : α ≃*o β)
  statement: f.toOrderIso = f
  proof: rfl

中文:
定理 toOrderIso_eq_coe
  条件: (f : α ≃*o β)
  结论: f.toOrderIso = f
  证明: rfl
-/
theorem toOrderIso_eq_coe (f : α ≃*o β) : f.toOrderIso = f :=
  rfl

/-- The inverse of an isomorphism is an isomorphism. -/
@[to_additive (attr := symm) /-- The inverse of an order isomorphism is an order isomorphism. -/]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (f : α ≃*o β)
  body: ⟨f.toMulEquiv.symm, f.toOrderIso.symm.map_rel_iff⟩

中文:
定义 symm
  签名: (f : α ≃*o β)
  定义体: ⟨f.toMulEquiv.symm, f.toOrderIso.symm.map_rel_iff⟩

Depends on / 依赖: f.toMulEquiv.symm, f.toOrderIso.symm.map_rel_iff, map_rel_iff, toMulEquiv, toOrderIso
-/
def symm (f : α ≃*o β) : β ≃*o α :=
  ⟨f.toMulEquiv.symm, f.toOrderIso.symm.map_rel_iff⟩

/-- See Note [custom simps projection]. -/
@[to_additive /-- See Note [custom simps projection]. -/]
/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (h : α ≃*o β)
  body: h

中文:
定义 Simps.apply
  签名: (h : α ≃*o β)
  定义体: h
-/
def Simps.apply (h : α ≃*o β) : α -> β :=
  h

/-- See Note [custom simps projection] -/
@[to_additive /-- See Note [custom simps projection]. -/]
/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (h : α ≃*o β)
  body: h.symm

initialize_simps_projections OrderAddMonoidIso (toFun -> apply, invFun -> symm_apply)
initialize_simps_projections OrderMonoidIso (toFun -> apply, invFun -> symm_apply)

@[to_additive]

中文:
定义 Simps.symm_apply
  签名: (h : α ≃*o β)
  定义体: h.symm

initialize_simps_projections OrderAddMonoidIso (toFun -> apply, invFun -> symm_apply)
initialize_simps_projections OrderMonoidIso (toFun -> apply, invFun -> symm_apply)

@[to_additive]
-/
def Simps.symm_apply (h : α ≃*o β) : β -> α :=
  h.symm

initialize_simps_projections OrderAddMonoidIso (toFun -> apply, invFun -> symm_apply)
initialize_simps_projections OrderMonoidIso (toFun -> apply, invFun -> symm_apply)

@[to_additive]
/--
theorem `invFun_eq_symm` / 定理 `invFun_eq_symm`

English:
theorem invFun_eq_symm
  given: {f : α ≃*o β}
  statement: f.invFun = f.symm
  proof: rfl

中文:
定理 invFun_eq_symm
  条件: {f : α ≃*o β}
  结论: f.invFun = f.symm
  证明: rfl

Depends on / 依赖: RightDistribClass
-/
theorem invFun_eq_symm {f : α ≃*o β} : f.invFun = f.symm := rfl

/-- `simp`-normal form of `invFun_eq_symm`. -/
@[to_additive (attr := simp)]
/--
theorem `coe_toEquiv_symm` / 定理 `coe_toEquiv_symm`

English:
theorem coe_toEquiv_symm
  given: (f : α ≃*o β)
  statement: ((f : α ≃ β).symm : β -> α) = f.symm
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_toEquiv_symm
  条件: (f : α ≃*o β)
  结论: ((f : α ≃ β).symm : β -> α) = f.symm
  证明: rfl

@[to_additive (attr := simp)]

Depends on / 依赖: NonUnitalNonAssocSemiring
-/
theorem coe_toEquiv_symm (f : α ≃*o β) : ((f : α ≃ β).symm : β -> α) = f.symm := rfl

@[to_additive (attr := simp)]
/--
theorem `equivLike_inv_eq_symm` / 定理 `equivLike_inv_eq_symm`

English:
theorem equivLike_inv_eq_symm
  given: (f : α ≃*o β)
  statement: EquivLike.inv f = f.symm
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 equivLike_inv_eq_symm
  条件: (f : α ≃*o β)
  结论: EquivLike.inv f = f.symm
  证明: rfl

@[to_additive (attr := simp)]

Depends on / 依赖: NatCast
-/
theorem equivLike_inv_eq_symm (f : α ≃*o β) : EquivLike.inv f = f.symm := rfl

@[to_additive (attr := simp)]
/--
theorem `toEquiv_symm` / 定理 `toEquiv_symm`

English:
theorem toEquiv_symm
  given: (f : α ≃*o β)
  statement: (f.symm : β ≃ α) = (f : α ≃ β).symm
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toEquiv_symm
  条件: (f : α ≃*o β)
  结论: (f.symm : β ≃ α) = (f : α ≃ β).symm
  证明: rfl

@[to_additive (attr := simp)]

Depends on / 依赖: IntCast
-/
theorem toEquiv_symm (f : α ≃*o β) : (f.symm : β ≃ α) = (f : α ≃ β).symm := rfl

@[to_additive (attr := simp)]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (f : α ≃*o β)
  statement: f.symm.symm = f
  proof: rfl

@[to_additive]

中文:
定理 symm_symm
  条件: (f : α ≃*o β)
  结论: f.symm.symm = f
  证明: rfl

@[to_additive]

Depends on / 依赖: AddMonoidWithOne
-/
theorem symm_symm (f : α ≃*o β) : f.symm.symm = f := rfl

@[to_additive]
/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (symm : (α ≃*o β) -> β ≃*o α)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[to_additive (attr := simp)]

中文:
定理 symm_bijective
  结论: Function.Bijective (symm : (α ≃*o β) -> β ≃*o α)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[to_additive (attr := simp)]

Depends on / 依赖: AddCommMonoidWithOne, Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (symm : (α ≃*o β) -> β ≃*o α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[to_additive (attr := simp)]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (OrderMonoidIso.refl α).symm = .refl α
  proof: rfl

中文:
定理 refl_symm
  结论: (OrderMonoidIso.refl α).symm = .refl α
  证明: rfl

Depends on / 依赖: AddGroupWithOne
-/
theorem refl_symm : (OrderMonoidIso.refl α).symm = .refl α := rfl

/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : α ≃*o β) (y : β)
  statement: e (e.symm y) = y
  proof: e.toEquiv.apply_symm_apply y

中文:
定理 apply_symm_apply
  条件: (e : α ≃*o β) (y : β)
  结论: e (e.symm y) = y
  证明: e.toEquiv.apply_symm_apply y

Depends on / 依赖: apply_symm_apply, e.toEquiv.apply_symm_apply, toEquiv
-/
theorem apply_symm_apply (e : α ≃*o β) (y : β) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y

/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : α ≃*o β) (x : α)
  statement: e.symm (e x) = x
  proof: e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]

中文:
定理 symm_apply_apply
  条件: (e : α ≃*o β) (x : α)
  结论: e.symm (e x) = x
  证明: e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]

Depends on / 依赖: NonUnitalSemiring, e.toEquiv.symm_apply_apply, symm_apply_apply, toEquiv
-/
theorem symm_apply_apply (e : α ≃*o β) (x : α) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]
/--
theorem `symm_comp_self` / 定理 `symm_comp_self`

English:
theorem symm_comp_self
  given: (e : α ≃*o β)
  statement: e.symm ∘ e = id
  proof: funext e.symm_apply_apply

@[to_additive (attr := simp)]

中文:
定理 symm_comp_self
  条件: (e : α ≃*o β)
  结论: e.symm ∘ e = id
  证明: funext e.symm_apply_apply

@[to_additive (attr := simp)]

Depends on / 依赖: NonAssocSemiring, e.symm_apply_apply, symm_apply_apply
-/
theorem symm_comp_self (e : α ≃*o β) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[to_additive (attr := simp)]
/--
theorem `self_comp_symm` / 定理 `self_comp_symm`

English:
theorem self_comp_symm
  given: (e : α ≃*o β)
  statement: e ∘ e.symm = id
  proof: funext e.apply_symm_apply

@[to_additive]

中文:
定理 self_comp_symm
  条件: (e : α ≃*o β)
  结论: e ∘ e.symm = id
  证明: funext e.apply_symm_apply

@[to_additive]

Depends on / 依赖: Semiring, apply_symm_apply, e.apply_symm_apply
-/
theorem self_comp_symm (e : α ≃*o β) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[to_additive]
/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (e : α ≃*o β) {x y}
  statement: e.symm x = y ↔ x = e y
  proof: e.toEquiv.symm_apply_eq

@[to_additive]

中文:
定理 symm_apply_eq
  条件: (e : α ≃*o β) {x y}
  结论: e.symm x = y ↔ x = e y
  证明: e.toEquiv.symm_apply_eq

@[to_additive]

Depends on / 依赖: e.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
theorem symm_apply_eq (e : α ≃*o β) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

@[to_additive]
/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (e : α ≃*o β) {x y}
  statement: y = e.symm x ↔ e y = x
  proof: e.toEquiv.eq_symm_apply

@[to_additive (attr := deprecated eq_symm_apply (since := "2026-07-26"))]

中文:
定理 eq_symm_apply
  条件: (e : α ≃*o β) {x y}
  结论: y = e.symm x ↔ e y = x
  证明: e.toEquiv.eq_symm_apply

@[to_additive (attr := deprecated eq_symm_apply (since := "2026-07-26"))]

Depends on / 依赖: e.toEquiv.eq_symm_apply, eq_symm_apply, toEquiv
-/
theorem eq_symm_apply (e : α ≃*o β) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[to_additive (attr := deprecated eq_symm_apply (since := "2026-07-26"))]
/--
theorem `apply_eq_iff_symm_apply` / 定理 `apply_eq_iff_symm_apply`

English:
theorem apply_eq_iff_symm_apply
  given: (e : α ≃*o β) {x : α} {y : β}
  statement: e x = y ↔ x = e.symm y
  proof: e.eq_symm_apply.symm

@[to_additive]

中文:
定理 apply_eq_iff_symm_apply
  条件: (e : α ≃*o β) {x : α} {y : β}
  结论: e x = y ↔ x = e.symm y
  证明: e.eq_symm_apply.symm

@[to_additive]

Depends on / 依赖: e.eq_symm_apply.symm, eq_symm_apply
-/
theorem apply_eq_iff_symm_apply (e : α ≃*o β) {x : α} {y : β} : e x = y ↔ x = e.symm y :=
  e.eq_symm_apply.symm

@[to_additive]
/--
theorem `eq_comp_symm` / 定理 `eq_comp_symm`

English:
theorem eq_comp_symm
  given: (e : α ≃*o β) (f : β -> α) (g : α -> α)
  proof: e.toEquiv.eq_comp_symm f g

@[to_additive]

中文:
定理 eq_comp_symm
  条件: (e : α ≃*o β) (f : β -> α) (g : α -> α)
  证明: e.toEquiv.eq_comp_symm f g

@[to_additive]

Depends on / 依赖: e.toEquiv.eq_comp_symm, eq_comp_symm, toEquiv
-/
theorem eq_comp_symm (e : α ≃*o β) (f : β -> α) (g : α -> α) :
    f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

@[to_additive]
/--
theorem `comp_symm_eq` / 定理 `comp_symm_eq`

English:
theorem comp_symm_eq
  given: (e : α ≃*o β) (f : β -> α) (g : α -> α)
  proof: e.toEquiv.comp_symm_eq f g

@[to_additive]

中文:
定理 comp_symm_eq
  条件: (e : α ≃*o β) (f : β -> α) (g : α -> α)
  证明: e.toEquiv.comp_symm_eq f g

@[to_additive]

Depends on / 依赖: comp_symm_eq, e.toEquiv.comp_symm_eq, toEquiv
-/
theorem comp_symm_eq (e : α ≃*o β) (f : β -> α) (g : α -> α) :
    g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g

@[to_additive]
/--
theorem `eq_symm_comp` / 定理 `eq_symm_comp`

English:
theorem eq_symm_comp
  given: (e : α ≃*o β) (f : α -> α) (g : α -> β)
  proof: e.toEquiv.eq_symm_comp f g

@[to_additive]

中文:
定理 eq_symm_comp
  条件: (e : α ≃*o β) (f : α -> α) (g : α -> β)
  证明: e.toEquiv.eq_symm_comp f g

@[to_additive]

Depends on / 依赖: e.toEquiv.eq_symm_comp, eq_symm_comp, toEquiv
-/
theorem eq_symm_comp (e : α ≃*o β) (f : α -> α) (g : α -> β) :
    f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g

@[to_additive]
/--
theorem `symm_comp_eq` / 定理 `symm_comp_eq`

English:
theorem symm_comp_eq
  given: (e : α ≃*o β) (f : α -> α) (g : α -> β)
  proof: e.toEquiv.symm_comp_eq f g

@[to_additive]

中文:
定理 symm_comp_eq
  条件: (e : α ≃*o β) (f : α -> α) (g : α -> β)
  证明: e.toEquiv.symm_comp_eq f g

@[to_additive]

Depends on / 依赖: e.toEquiv.symm_comp_eq, symm_comp_eq, toEquiv
-/
theorem symm_comp_eq (e : α ≃*o β) (f : α -> α) (g : α -> β) :
    e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g

@[to_additive]
/--
lemma `lt_symm_apply` / 引理 `lt_symm_apply`

English:
lemma lt_symm_apply
  given: (e : α ≃*o β) {x : α} {y : β}
  statement: x < e.symm y ↔ e x < y
  proof: e.toOrderIso.lt_symm_apply

@[to_additive]

中文:
引理 lt_symm_apply
  条件: (e : α ≃*o β) {x : α} {y : β}
  结论: x < e.symm y ↔ e x < y
  证明: e.toOrderIso.lt_symm_apply

@[to_additive]

Depends on / 依赖: e.toOrderIso.lt_symm_apply, lt_symm_apply, toOrderIso
-/
lemma lt_symm_apply (e : α ≃*o β) {x : α} {y : β} : x < e.symm y ↔ e x < y :=
  e.toOrderIso.lt_symm_apply

@[to_additive]
/--
lemma `symm_apply_lt` / 引理 `symm_apply_lt`

English:
lemma symm_apply_lt
  given: (e : α ≃*o β) {x : α} {y : β}
  statement: e.symm y < x ↔ y < e x
  proof: e.toOrderIso.symm_apply_lt

中文:
引理 symm_apply_lt
  条件: (e : α ≃*o β) {x : α} {y : β}
  结论: e.symm y < x ↔ y < e x
  证明: e.toOrderIso.symm_apply_lt

Depends on / 依赖: e.toOrderIso.symm_apply_lt, symm_apply_lt, toOrderIso
-/
lemma symm_apply_lt (e : α ≃*o β) {x : α} {y : β} : e.symm y < x ↔ y < e x :=
  e.toOrderIso.symm_apply_lt

variable (f)

@[to_additive]
/--
lemma `strictMono` / 引理 `strictMono`

English:
lemma strictMono
  statement: StrictMono f
  proof: strictMono_of_le_iff_le fun _ _ => (map_le_map_iff _).symm

@[to_additive]

中文:
引理 strictMono
  结论: StrictMono f
  证明: strictMono_of_le_iff_le fun _ _ => (map_le_map_iff _).symm

@[to_additive]

Depends on / 依赖: IsDomain
-/
protected lemma strictMono : StrictMono f :=
  strictMono_of_le_iff_le fun _ _ => (map_le_map_iff _).symm

@[to_additive]
/--
lemma `strictMono_symm` / 引理 `strictMono_symm`

English:
lemma strictMono_symm
  statement: StrictMono f.symm
  proof: strictMono_of_le_iff_le fun a b => by
    rw [← map_le_map_iff f]
    convert! Iff.rfl <;>
    exact f.toEquiv.apply_symm_apply _

中文:
引理 strictMono_symm
  结论: StrictMono f.symm
  证明: strictMono_of_le_iff_le fun a b => by
    rw [← map_le_map_iff f]
    convert! Iff.rfl <;>
    exact f.toEquiv.apply_symm_apply _
-/
protected lemma strictMono_symm : StrictMono f.symm :=
strictMono_of_le_iff_le fun a b => by
    rw [← map_le_map_iff f]
    convert! Iff.rfl <;>
    exact f.toEquiv.apply_symm_apply _

end Preorder

section OrderedCommGroup

variable {_ : CommGroup α} {_ : Preorder α} {_ : CommGroup β} {_ : PartialOrder β}

/-- Makes an ordered group isomorphism from a proof that the map preserves multiplication. -/
@[to_additive
      /-- Makes an ordered additive group isomorphism from a proof that the map preserves
      addition. -/]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (f : α ≃ β) (hf : forall {a b}, f a <= f b ↔ a <= b) (map_mul : forall a b : α, f (a * b) = f a * f b)
  body: { MulEquiv.mk' f map_mul with map_le_map_iff' := hf }

中文:
定义 mk'
  签名: (f : α ≃ β) (hf : 对任意 {a b}, f a <= f b ↔ a <= b) (map_mul : 对任意 a b : α, f (a * b) = f a * f b)
  定义体: { MulEquiv.mk' f map_mul with map_le_map_iff' := hf }

Depends on / 依赖: MulEquiv, MulEquiv.mk, map_le_map_iff, map_mul
-/
def mk' (f : α ≃ β) (hf : forall {a b}, f a <= f b ↔ a <= b) (map_mul : forall a b : α, f (a * b) = f a * f b) :
    α ≃*o β :=
  { MulEquiv.mk' f map_mul with map_le_map_iff' := hf }

end OrderedCommGroup

end OrderMonoidIso
