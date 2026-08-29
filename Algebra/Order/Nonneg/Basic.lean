/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# The type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

Currently we only state instances and states some `simp`/`norm_cast` lemmas.

When `α` is `ℝ`, this will give us some properties about `ℝ≥0`.

## Implementation Notes

Instead of `{x : α // 0 ≤ x}` we could also use `Set.Ici (0 : α)`, which is definitionally equal.
However, using the explicit subtype has a big advantage: when writing an element explicitly
with a proof of nonnegativity as `⟨x, hx⟩`, the `hx` is expected to have type `0 ≤ x`. If we would
use `Ici 0`, then the type is expected to be `x ∈ Ici 0`. Although these types are definitionally
equal, this often confuses the elaborator. Similar problems arise when doing cases on an element.

The disadvantage is that we have to duplicate some instances about `Set.Ici` to this subtype.
-/

@[expose] public section
assert_not_exists GeneralizedHeytingAlgebra
assert_not_exists IsOrderedMonoid
-- TODO -- assert_not_exists PosMulMono
assert_not_exists mem_upperBounds

open Set

variable {α : Type*}

namespace Nonneg

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: [Preorder α] {a : α}
  body: ⟨⟨a, le_rfl⟩⟩

中文:
实例 inhabited
  签名: [Preorder α] {a : α}
  定义体: ⟨⟨a, le_rfl⟩⟩

Depends on / 依赖: le_rfl
-/
instance inhabited [Preorder α] {a : α} : Inhabited { x : α // a <= x } :=
  ⟨⟨a, le_rfl⟩⟩

/--
Instance `zero` / 实例 `zero`

English:
instance zero
  signature: [Zero α] [Preorder α]
  body: ⟨⟨0, le_rfl⟩⟩

@[simp, norm_cast]

中文:
实例 zero
  签名: [Zero α] [Preorder α]
  定义体: ⟨⟨0, le_rfl⟩⟩

@[simp, norm_cast]

Depends on / 依赖: le_rfl
-/
instance zero [Zero α] [Preorder α] : Zero { x : α // 0 <= x } :=
  ⟨⟨0, le_rfl⟩⟩

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  given: [Zero α] [Preorder α]
  statement: ((0 : { x : α // 0 <= x }) : α) = 0
  proof: rfl

@[simp]

中文:
定理 coe_zero
  条件: [Zero α] [Preorder α]
  结论: ((0 : { x : α // 0 <= x }) : α) = 0
  证明: rfl

@[simp]
-/
protected theorem coe_zero [Zero α] [Preorder α] : ((0 : { x : α // 0 <= x }) : α) = 0 :=
  rfl

@[simp]
/--
theorem `mk_eq_zero` / 定理 `mk_eq_zero`

English:
theorem mk_eq_zero
  given: [Zero α] [Preorder α] {x : α} (hx : 0 <= x)
  proof: Subtype.ext_iff

中文:
定理 mk_eq_zero
  条件: [Zero α] [Preorder α] {x : α} (hx : 0 <= x)
  证明: Subtype.ext_iff

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem mk_eq_zero [Zero α] [Preorder α] {x : α} (hx : 0 <= x) :
    (⟨x, hx⟩ : { x : α // 0 <= x }) = 0 ↔ x = 0 :=
  Subtype.ext_iff

/--
Instance `add` / 实例 `add`

English:
instance add
  signature: [AddZeroClass α] [Preorder α] [AddLeftMono α]
  body: ⟨fun x y => ⟨x + y, add_nonneg x.2 y.2⟩⟩

@[simp]

中文:
实例 add
  签名: [AddZeroClass α] [Preorder α] [AddLeftMono α]
  定义体: ⟨fun x y => ⟨x + y, add_nonneg x.2 y.2⟩⟩

@[simp]

Depends on / 依赖: add_nonneg
-/
instance add [AddZeroClass α] [Preorder α] [AddLeftMono α] : Add { x : α // 0 <= x } :=
  ⟨fun x y => ⟨x + y, add_nonneg x.2 y.2⟩⟩

@[simp]
/--
theorem `mk_add_mk` / 定理 `mk_add_mk`

English:
theorem mk_add_mk
  statement: [AddZeroClass α] [Preorder α] [AddLeftMono α] {x y : α}
  proof: rfl

@[simp, norm_cast]

中文:
定理 mk_add_mk
  结论: [AddZeroClass α] [Preorder α] [AddLeftMono α] {x y : α}
  证明: rfl

@[simp, norm_cast]
-/
theorem mk_add_mk [AddZeroClass α] [Preorder α] [AddLeftMono α] {x y : α}
    (hx : 0 <= x) (hy : 0 <= y) :
    (⟨x, hx⟩ : { x : α // 0 <= x }) + ⟨y, hy⟩ = ⟨x + y, add_nonneg hx hy⟩ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  statement: [AddZeroClass α] [Preorder α] [AddLeftMono α]
  proof: rfl

中文:
定理 coe_add
  结论: [AddZeroClass α] [Preorder α] [AddLeftMono α]
  证明: rfl
-/
protected theorem coe_add [AddZeroClass α] [Preorder α] [AddLeftMono α]
    (a b : { x : α // 0 <= x }) : ((a + b : { x : α // 0 <= x }) : α) = a + b :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddZeroClass
  signature: α] [Preorder α] [AddLeftMono α] [IsLeftCancelAdd α] :
  body: Subtype.ext (add_left_cancel congr($eq))

中文:
实例 [AddZeroClass
  签名: α] [Preorder α] [AddLeftMono α] [IsLeftCancelAdd α] :
  定义体: Subtype.ext (add_left_cancel congr($eq))

Depends on / 依赖: Subtype, Subtype.ext, add_left_cancel
-/
instance [AddZeroClass α] [Preorder α] [AddLeftMono α] [IsLeftCancelAdd α] :
    IsLeftCancelAdd { x : α // 0 <= x } where
  add_left_cancel _ _ _ eq := Subtype.ext (add_left_cancel congr($eq))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddZeroClass
  signature: α] [Preorder α] [AddLeftMono α] [IsRightCancelAdd α] :
  body: Subtype.ext (add_right_cancel congr($eq))

中文:
实例 [AddZeroClass
  签名: α] [Preorder α] [AddLeftMono α] [IsRightCancelAdd α] :
  定义体: Subtype.ext (add_right_cancel congr($eq))

Depends on / 依赖: Subtype, Subtype.ext, add_right_cancel
-/
instance [AddZeroClass α] [Preorder α] [AddLeftMono α] [IsRightCancelAdd α] :
    IsRightCancelAdd { x : α // 0 <= x } where
  add_right_cancel _ _ _ eq := Subtype.ext (add_right_cancel congr($eq))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddZeroClass
  signature: α] [Preorder α] [AddLeftMono α] [IsCancelAdd α] :

中文:
实例 [AddZeroClass
  签名: α] [Preorder α] [AddLeftMono α] [IsCancelAdd α] :
-/
instance [AddZeroClass α] [Preorder α] [AddLeftMono α] [IsCancelAdd α] :
    IsCancelAdd { x : α // 0 <= x } where

/--
Instance `nsmul` / 实例 `nsmul`

English:
instance nsmul
  signature: [AddMonoid α] [Preorder α] [AddLeftMono α]
  body: ⟨fun n x => ⟨n • (x : α), nsmul_nonneg x.prop n⟩⟩

@[simp]

中文:
实例 nsmul
  签名: [AddMonoid α] [Preorder α] [AddLeftMono α]
  定义体: ⟨fun n x => ⟨n • (x : α), nsmul_nonneg x.prop n⟩⟩

@[simp]

Depends on / 依赖: nsmul_nonneg, x.prop
-/
instance nsmul [AddMonoid α] [Preorder α] [AddLeftMono α] : SMul Nat { x : α // 0 <= x } :=
  ⟨fun n x => ⟨n • (x : α), nsmul_nonneg x.prop n⟩⟩

@[simp]
/--
theorem `nsmul_mk` / 定理 `nsmul_mk`

English:
theorem nsmul_mk
  statement: [AddMonoid α] [Preorder α] [AddLeftMono α] (n : Nat) {x : α}
  proof: rfl

@[simp, norm_cast]

中文:
定理 nsmul_mk
  结论: [AddMonoid α] [Preorder α] [AddLeftMono α] (n : 自然数) {x : α}
  证明: rfl

@[simp, norm_cast]
-/
theorem nsmul_mk [AddMonoid α] [Preorder α] [AddLeftMono α] (n : Nat) {x : α}
    (hx : 0 <= x) : (n • (⟨x, hx⟩ : { x : α // 0 <= x })) = ⟨n • x, nsmul_nonneg hx n⟩ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_nsmul` / 定理 `coe_nsmul`

English:
theorem coe_nsmul
  statement: [AddMonoid α] [Preorder α] [AddLeftMono α]
  proof: rfl

中文:
定理 coe_nsmul
  结论: [AddMonoid α] [Preorder α] [AddLeftMono α]
  证明: rfl
-/
protected theorem coe_nsmul [AddMonoid α] [Preorder α] [AddLeftMono α]
    (n : Nat) (a : { x : α // 0 <= x }) : ((n • a : { x : α // 0 <= x }) : α) = n • (a : α) :=
  rfl

section One

variable [Zero α] [One α] [LE α] [ZeroLEOneClass α]

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One { x : α // 0 <= x } where
  body: ⟨1, zero_le_one⟩

@[simp, norm_cast]

中文:
实例 one
  签名: : One { x : α // 0 <= x } where
  定义体: ⟨1, zero_le_one⟩

@[simp, norm_cast]

Depends on / 依赖: zero_le_one
-/
instance one : One { x : α // 0 <= x } where
  one := ⟨1, zero_le_one⟩

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : { x : α // 0 <= x }) : α) = 1
  proof: rfl

@[simp]

中文:
定理 coe_one
  结论: ((1 : { x : α // 0 <= x }) : α) = 1
  证明: rfl

@[simp]
-/
protected theorem coe_one : ((1 : { x : α // 0 <= x }) : α) = 1 :=
  rfl

@[simp]
/--
theorem `mk_eq_one` / 定理 `mk_eq_one`

English:
theorem mk_eq_one
  given: {x : α} (hx : 0 <= x)
  proof: Subtype.ext_iff

中文:
定理 mk_eq_one
  条件: {x : α} (hx : 0 <= x)
  证明: Subtype.ext_iff

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem mk_eq_one {x : α} (hx : 0 <= x) :
    (⟨x, hx⟩ : { x : α // 0 <= x }) = 1 ↔ x = 1 :=
  Subtype.ext_iff

end One

section Mul

variable [MulZeroClass α] [Preorder α] [PosMulMono α]

/--
Instance `mul` / 实例 `mul`

English:
instance mul
  signature: : Mul { x : α // 0 <= x } where
  body: ⟨x * y, mul_nonneg x.2 y.2⟩

@[simp, norm_cast]

中文:
实例 mul
  签名: : Mul { x : α // 0 <= x } where
  定义体: ⟨x * y, mul_nonneg x.2 y.2⟩

@[simp, norm_cast]

Depends on / 依赖: mul_nonneg
-/
instance mul : Mul { x : α // 0 <= x } where
  mul x y := ⟨x * y, mul_nonneg x.2 y.2⟩

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (a b : { x : α // 0 <= x })
  proof: rfl

@[simp]

中文:
定理 coe_mul
  条件: (a b : { x : α // 0 <= x })
  证明: rfl

@[simp]
-/
protected theorem coe_mul (a b : { x : α // 0 <= x }) :
    ((a * b : { x : α // 0 <= x }) : α) = a * b :=
  rfl

@[simp]
/--
theorem `mk_mul_mk` / 定理 `mk_mul_mk`

English:
theorem mk_mul_mk
  given: {x y : α} (hx : 0 <= x) (hy : 0 <= y)
  proof: rfl

中文:
定理 mk_mul_mk
  条件: {x y : α} (hx : 0 <= x) (hy : 0 <= y)
  证明: rfl
-/
theorem mk_mul_mk {x y : α} (hx : 0 <= x) (hy : 0 <= y) :
    (⟨x, hx⟩ : { x : α // 0 <= x }) * ⟨y, hy⟩ = ⟨x * y, mul_nonneg hx hy⟩ :=
  rfl

end Mul

section AddMonoid

variable [AddMonoid α] [Preorder α] [AddLeftMono α]

/--
Instance `addMonoid` / 实例 `addMonoid`

English:
instance addMonoid
  signature: : AddMonoid { x : α // 0 <= x }
  body: fast_instance% Subtype.coe_injective.addMonoid _ Nonneg.coe_zero (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 addMonoid
  签名: : AddMonoid { x : α // 0 <= x }
  定义体: fast_instance% Subtype.coe_injective.addMonoid _ Nonneg.coe_zero (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: Nonneg, Nonneg.coe_zero, Subtype, Subtype.coe_injective.addMonoid, addMonoid, coe_injective, coe_zero, fast_instance
-/
instance addMonoid : AddMonoid { x : α // 0 <= x } :=
  fast_instance% Subtype.coe_injective.addMonoid _ Nonneg.coe_zero (fun _ _ => rfl) fun _ _ => rfl

/-- Coercion `{x : α // 0 ≤ x} → α` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `coeAddMonoidHom` / `coeAddMonoidHom` 的定义

English:
definition coeAddMonoidHom
  signature: : { x : α // 0 <= x } ->+ α
  body: { toFun := ((↑) : { x : α // 0 <= x } -> α)
    map_zero' := Nonneg.coe_zero
    map_add' := Nonneg.coe_add }

@[norm_cast]

中文:
定义 coeAddMonoidHom
  签名: : { x : α // 0 <= x } ->+ α
  定义体: { toFun := ((↑) : { x : α // 0 <= x } -> α)
    map_zero' := Nonneg.coe_zero
    map_add' := Nonneg.coe_add }

@[norm_cast]

Depends on / 依赖: Nonneg, Nonneg.coe_add, Nonneg.coe_zero, coe_add, coe_zero, map_add, map_zero
-/
def coeAddMonoidHom : { x : α // 0 <= x } ->+ α :=
  { toFun := ((↑) : { x : α // 0 <= x } -> α)
    map_zero' := Nonneg.coe_zero
    map_add' := Nonneg.coe_add }

@[norm_cast]
/--
theorem `nsmul_coe` / 定理 `nsmul_coe`

English:
theorem nsmul_coe
  given: (n : Nat) (r : { x : α // 0 <= x })
  proof: Nonneg.coeAddMonoidHom.map_nsmul _ _

中文:
定理 nsmul_coe
  条件: (n : 自然数) (r : { x : α // 0 <= x })
  证明: Nonneg.coeAddMonoidHom.map_nsmul _ _

Depends on / 依赖: Nonneg, Nonneg.coeAddMonoidHom.map_nsmul, coeAddMonoidHom, map_nsmul
-/
theorem nsmul_coe (n : Nat) (r : { x : α // 0 <= x }) :
    ↑(n • r) = n • (r : α) :=
  Nonneg.coeAddMonoidHom.map_nsmul _ _

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid α] [Preorder α] [AddLeftMono α]

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: : AddCommMonoid { x : α // 0 <= x }
  body: fast_instance%
    Subtype.coe_injective.addCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 addCommMonoid
  签名: : AddCommMonoid { x : α // 0 <= x }
  定义体: fast_instance%
    Subtype.coe_injective.addCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: Nonneg, Nonneg.coe_zero, Subtype, Subtype.coe_injective.addCommMonoid, addCommMonoid, coe_injective, coe_zero, fast_instance
-/
instance addCommMonoid : AddCommMonoid { x : α // 0 <= x } :=
  fast_instance%
    Subtype.coe_injective.addCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) (fun _ _ => rfl)

end AddCommMonoid

section AddCancelCommMonoid
variable [AddCancelCommMonoid α] [Preorder α] [AddLeftMono α]

/--
Instance `addCancelCommMonoid` / 实例 `addCancelCommMonoid`

English:
instance addCancelCommMonoid
  signature: : AddCancelCommMonoid {x : α // 0 <= x}
  body: fast_instance%
    Subtype.coe_injective.addCancelCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 addCancelCommMonoid
  签名: : AddCancelCommMonoid {x : α // 0 <= x}
  定义体: fast_instance%
    Subtype.coe_injective.addCancelCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: Nonneg, Nonneg.coe_zero, Subtype, Subtype.coe_injective.addCancelCommMonoid, addCancelCommMonoid, coe_injective, coe_zero, fast_instance
-/
instance addCancelCommMonoid : AddCancelCommMonoid {x : α // 0 <= x} :=
  fast_instance%
    Subtype.coe_injective.addCancelCommMonoid _ Nonneg.coe_zero (fun _ _ => rfl) (fun _ _ => rfl)

end AddCancelCommMonoid

section AddMonoidWithOne

variable [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α]

/--
Instance `natCast` / 实例 `natCast`

English:
instance natCast
  signature: : NatCast { x : α // 0 <= x }
  body: ⟨fun n => ⟨n, Nat.cast_nonneg' n⟩⟩

@[simp, norm_cast]

中文:
实例 natCast
  签名: : 自然数Cast { x : α // 0 <= x }
  定义体: ⟨fun n => ⟨n, Nat.cast_nonneg' n⟩⟩

@[simp, norm_cast]

Depends on / 依赖: Nat.cast_nonneg, cast_nonneg
-/
instance natCast : NatCast { x : α // 0 <= x } :=
  ⟨fun n => ⟨n, Nat.cast_nonneg' n⟩⟩

@[simp, norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (n : Nat)
  statement: ((↑n : { x : α // 0 <= x }) : α) = n
  proof: rfl

@[simp]

中文:
定理 coe_natCast
  条件: (n : 自然数)
  结论: ((↑n : { x : α // 0 <= x }) : α) = n
  证明: rfl

@[simp]
-/
protected theorem coe_natCast (n : Nat) : ((↑n : { x : α // 0 <= x }) : α) = n :=
  rfl

@[simp]
/--
theorem `mk_natCast` / 定理 `mk_natCast`

English:
theorem mk_natCast
  given: (n : Nat)
  statement: (⟨n, n.cast_nonneg'⟩ : { x : α // 0 <= x }) = n
  proof: rfl

中文:
定理 mk_natCast
  条件: (n : 自然数)
  结论: (⟨n, n.cast_nonneg'⟩ : { x : α // 0 <= x }) = n
  证明: rfl
-/
theorem mk_natCast (n : Nat) : (⟨n, n.cast_nonneg'⟩ : { x : α // 0 <= x }) = n :=
  rfl

/--
Instance `addMonoidWithOne` / 实例 `addMonoidWithOne`

English:
instance addMonoidWithOne
  signature: : AddMonoidWithOne { x : α // 0 <= x }
  body: { Nonneg.one (α := α) with
    toNatCast := Nonneg.natCast
    natCast_zero := by ext; simp
    natCast_succ := fun _ => by ext; simp }

中文:
实例 addMonoidWithOne
  签名: : AddMonoidWithOne { x : α // 0 <= x }
  定义体: { Nonneg.one (α := α) with
    toNatCast := Nonneg.natCast
    natCast_zero := by ext; simp
    natCast_succ := fun _ => by ext; simp }

Depends on / 依赖: Nonneg, Nonneg.natCast, Nonneg.one, natCast, natCast_succ, natCast_zero, toNatCast
-/
instance addMonoidWithOne : AddMonoidWithOne { x : α // 0 <= x } :=
  { Nonneg.one (α := α) with
    toNatCast := Nonneg.natCast
    natCast_zero := by ext; simp
    natCast_succ := fun _ => by ext; simp }

end AddMonoidWithOne

section Pow

variable [MonoidWithZero α] [Preorder α] [ZeroLEOneClass α] [PosMulMono α]

/--
Instance `pow` / 实例 `pow`

English:
instance pow
  signature: : Pow { x : α // 0 <= x } Nat where
  body: ⟨(x : α) ^ n, pow_nonneg x.2 n⟩

@[simp, norm_cast]

中文:
实例 pow
  签名: : Pow { x : α // 0 <= x } 自然数 where
  定义体: ⟨(x : α) ^ n, pow_nonneg x.2 n⟩

@[simp, norm_cast]

Depends on / 依赖: pow_nonneg
-/
instance pow : Pow { x : α // 0 <= x } Nat where
  pow x n := ⟨(x : α) ^ n, pow_nonneg x.2 n⟩

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (a : { x : α // 0 <= x }) (n : Nat)
  proof: rfl

@[simp]

中文:
定理 coe_pow
  条件: (a : { x : α // 0 <= x }) (n : 自然数)
  证明: rfl

@[simp]
-/
protected theorem coe_pow (a : { x : α // 0 <= x }) (n : Nat) :
    (↑(a ^ n) : α) = (a : α) ^ n :=
  rfl

@[simp]
/--
theorem `mk_pow` / 定理 `mk_pow`

English:
theorem mk_pow
  given: {x : α} (hx : 0 <= x) (n : Nat)
  proof: rfl

中文:
定理 mk_pow
  条件: {x : α} (hx : 0 <= x) (n : 自然数)
  证明: rfl
-/
theorem mk_pow {x : α} (hx : 0 <= x) (n : Nat) :
    (⟨x, hx⟩ : { x : α // 0 <= x }) ^ n = ⟨x ^ n, pow_nonneg hx n⟩ :=
  rfl

end Pow

section Semiring

variable [Semiring α] [PartialOrder α] [ZeroLEOneClass α]
  [AddLeftMono α] [PosMulMono α]

/--
Instance `semiring` / 实例 `semiring`

English:
instance semiring
  signature: : Semiring { x : α // 0 <= x }
  body: fast_instance% Subtype.coe_injective.semiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

中文:
实例 semiring
  签名: : Semiring { x : α // 0 <= x }
  定义体: fast_instance% Subtype.coe_injective.semiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

Depends on / 依赖: Nonneg, Nonneg.coe_one, Nonneg.coe_zero, Subtype, Subtype.coe_injective.semiring, coe_injective, coe_one, coe_zero, fast_instance, semiring
-/
instance semiring : Semiring { x : α // 0 <= x } :=
  fast_instance% Subtype.coe_injective.semiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

/--
Instance `monoidWithZero` / 实例 `monoidWithZero`

English:
instance monoidWithZero
  signature: : MonoidWithZero { x : α // 0 <= x }
  body: by infer_instance

中文:
实例 monoidWithZero
  签名: : MonoidWithZero { x : α // 0 <= x }
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance monoidWithZero : MonoidWithZero { x : α // 0 <= x } := by infer_instance

/--
Definition of `coeRingHom` / `coeRingHom` 的定义

English:
definition coeRingHom
  signature: : { x : α // 0 <= x } ->+* α
  body: { toFun := ((↑) : { x : α // 0 <= x } -> α)
    map_one' := Nonneg.coe_one
    map_mul' := Nonneg.coe_mul
    map_zero' := Nonneg.coe_zero,
    map_add' := Nonneg.coe_add }

中文:
定义 coeRingHom
  签名: : { x : α // 0 <= x } ->+* α
  定义体: { toFun := ((↑) : { x : α // 0 <= x } -> α)
    map_one' := Nonneg.coe_one
    map_mul' := Nonneg.coe_mul
    map_zero' := Nonneg.coe_zero,
    map_add' := Nonneg.coe_add }

Depends on / 依赖: Nonneg, Nonneg.coe_add, Nonneg.coe_mul, Nonneg.coe_one, Nonneg.coe_zero, coe_add, coe_mul, coe_one, coe_zero, map_add, map_mul, map_one, map_zero
-/
def coeRingHom : { x : α // 0 <= x } ->+* α :=
  { toFun := ((↑) : { x : α // 0 <= x } -> α)
    map_one' := Nonneg.coe_one
    map_mul' := Nonneg.coe_mul
    map_zero' := Nonneg.coe_zero,
    map_add' := Nonneg.coe_add }

end Semiring

section CommSemiring

variable [CommSemiring α] [PartialOrder α] [ZeroLEOneClass α]
  [AddLeftMono α] [PosMulMono α]

/--
Instance `commSemiring` / 实例 `commSemiring`

English:
instance commSemiring
  signature: : CommSemiring { x : α // 0 <= x }
  body: fast_instance% Subtype.coe_injective.commSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

中文:
实例 commSemiring
  签名: : CommSemiring { x : α // 0 <= x }
  定义体: fast_instance% Subtype.coe_injective.commSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

Depends on / 依赖: Nonneg, Nonneg.coe_one, Nonneg.coe_zero, Subtype, Subtype.coe_injective.commSemiring, coe_injective, coe_one, coe_zero, commSemiring, fast_instance
-/
instance commSemiring : CommSemiring { x : α // 0 <= x } :=
  fast_instance% Subtype.coe_injective.commSemiring _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

/--
Instance `commMonoidWithZero` / 实例 `commMonoidWithZero`

English:
instance commMonoidWithZero
  signature: : CommMonoidWithZero { x : α // 0 <= x }
  body: inferInstance

中文:
实例 commMonoidWithZero
  签名: : CommMonoidWithZero { x : α // 0 <= x }
  定义体: inferInstance
-/
instance commMonoidWithZero : CommMonoidWithZero { x : α // 0 <= x } := inferInstance

end CommSemiring

section SemilatticeSup
variable [Zero α] [SemilatticeSup α]

/--
Definition of `toNonneg` / `toNonneg` 的定义

English:
definition toNonneg
  signature: (a : α)
  body: ⟨max a 0, le_sup_right⟩

@[simp]

中文:
定义 toNonneg
  签名: (a : α)
  定义体: ⟨max a 0, le_sup_right⟩

@[simp]

Depends on / 依赖: le_sup_right
-/
def toNonneg (a : α) : { x : α // 0 <= x } :=
  ⟨max a 0, le_sup_right⟩

@[simp]
/--
theorem `coe_toNonneg` / 定理 `coe_toNonneg`

English:
theorem coe_toNonneg
  given: {a : α}
  statement: (toNonneg a : α) = max a 0
  proof: rfl

@[simp]

中文:
定理 coe_toNonneg
  条件: {a : α}
  结论: (toNonneg a : α) = max a 0
  证明: rfl

@[simp]
-/
theorem coe_toNonneg {a : α} : (toNonneg a : α) = max a 0 :=
  rfl

@[simp]
/--
theorem `toNonneg_of_nonneg` / 定理 `toNonneg_of_nonneg`

English:
theorem toNonneg_of_nonneg
  given: {a : α} (h : 0 <= a)
  statement: toNonneg a = ⟨a, h⟩
  proof: by simp [toNonneg, h]

@[simp]

中文:
定理 toNonneg_of_nonneg
  条件: {a : α} (h : 0 <= a)
  结论: toNonneg a = ⟨a, h⟩
  证明: by simp [toNonneg, h]

@[simp]

Depends on / 依赖: toNonneg
-/
theorem toNonneg_of_nonneg {a : α} (h : 0 <= a) : toNonneg a = ⟨a, h⟩ := by simp [toNonneg, h]

@[simp]
/--
theorem `toNonneg_coe` / 定理 `toNonneg_coe`

English:
theorem toNonneg_coe
  given: {a : { x : α // 0 <= x }}
  statement: toNonneg (a : α) = a
  proof: toNonneg_of_nonneg a.2

@[simp]

中文:
定理 toNonneg_coe
  条件: {a : { x : α // 0 <= x }}
  结论: toNonneg (a : α) = a
  证明: toNonneg_of_nonneg a.2

@[simp]

Depends on / 依赖: toNonneg_of_nonneg
-/
theorem toNonneg_coe {a : { x : α // 0 <= x }} : toNonneg (a : α) = a :=
  toNonneg_of_nonneg a.2

@[simp]
/--
theorem `toNonneg_le` / 定理 `toNonneg_le`

English:
theorem toNonneg_le
  given: {a : α} {b : { x : α // 0 <= x }}
  statement: toNonneg a <= b ↔ a <= b
  proof: by
  obtain ⟨b, hb⟩ := b
  simp [toNonneg, hb]

中文:
定理 toNonneg_le
  条件: {a : α} {b : { x : α // 0 <= x }}
  结论: toNonneg a <= b ↔ a <= b
  证明: by
  obtain ⟨b, hb⟩ := b
  simp [toNonneg, hb]

Depends on / 依赖: toNonneg
-/
theorem toNonneg_le {a : α} {b : { x : α // 0 <= x }} : toNonneg a <= b ↔ a <= b := by
  obtain ⟨b, hb⟩ := b
  simp [toNonneg, hb]

/--
Instance `sub` / 实例 `sub`

English:
instance sub
  signature: [Sub α]
  body: ⟨fun x y => toNonneg (x - y)⟩

@[simp]

中文:
实例 sub
  签名: [Sub α]
  定义体: ⟨fun x y => toNonneg (x - y)⟩

@[simp]

Depends on / 依赖: toNonneg
-/
instance sub [Sub α] : Sub { x : α // 0 <= x } :=
  ⟨fun x y => toNonneg (x - y)⟩

@[simp]
/--
theorem `mk_sub_mk` / 定理 `mk_sub_mk`

English:
theorem mk_sub_mk
  given: [Sub α] {x y : α} (hx : 0 <= x) (hy : 0 <= y)
  proof: rfl

中文:
定理 mk_sub_mk
  条件: [Sub α] {x y : α} (hx : 0 <= x) (hy : 0 <= y)
  证明: rfl
-/
theorem mk_sub_mk [Sub α] {x y : α} (hx : 0 <= x) (hy : 0 <= y) :
    (⟨x, hx⟩ : { x : α // 0 <= x }) - ⟨y, hy⟩ = toNonneg (x - y) :=
  rfl

end SemilatticeSup

section LinearOrder
variable [Zero α] [LinearOrder α]

@[simp]
/--
theorem `toNonneg_lt` / 定理 `toNonneg_lt`

English:
theorem toNonneg_lt
  given: {a : { x : α // 0 <= x }} {b : α}
  statement: a < toNonneg b ↔ ↑a < b
  proof: by
  obtain ⟨a, ha⟩ := a
  simp [toNonneg, ha.not_gt]

中文:
定理 toNonneg_lt
  条件: {a : { x : α // 0 <= x }} {b : α}
  结论: a < toNonneg b ↔ ↑a < b
  证明: by
  obtain ⟨a, ha⟩ := a
  simp [toNonneg, ha.not_gt]

Depends on / 依赖: ha.not_gt, not_gt, toNonneg
-/
theorem toNonneg_lt {a : { x : α // 0 <= x }} {b : α} : a < toNonneg b ↔ ↑a < b := by
  obtain ⟨a, ha⟩ := a
  simp [toNonneg, ha.not_gt]

end LinearOrder

end Nonneg
