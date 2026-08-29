/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Submonoid.Pointwise

/-!

# Submonoid of inverses

Given a submonoid `N` of a monoid `M`, we define the submonoid `N.leftInv` as the submonoid of
left inverses of `N`. When `M` is commutative, we may define `fromCommLeftInv : N.leftInv →* N`
since the inverses are unique. When `N ≤ IsUnit.Submonoid M`, this is precisely
the pointwise inverse of `N`, and we may define `leftInvEquiv : S.leftInv ≃* S`.

For the pointwise inverse of submonoids of groups, please refer to the file
`Mathlib/Algebra/Group/Submonoid/Pointwise.lean`.

`N.leftInv` is distinct from `N.units`, which is the subgroup of `Mˣ` containing all units that are
in `N`. See the implementation notes of `Mathlib/Algebra/Group/Submonoid/Units.lean` for more
details on related constructions.

## TODO

Define the submonoid of right inverses and two-sided inverses.
See the comments of https://github.com/leanprover-community/mathlib4/pull/10679 for a possible
implementation.
-/

@[expose] public section


variable {M : Type*}

namespace Submonoid

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] : Group (IsUnit.submonoid M)
  body: { (inferInstance : Monoid (IsUnit.submonoid M)) with
    inv := fun x => ⟨x.prop.unit⁻¹.val, x.prop.unit⁻¹.isUnit⟩
    inv_mul_cancel := fun x =>
      Subtype.ext ((Units.val_mul x.prop.unit⁻¹ _).trans x.prop.unit.inv_val) }

@[to_additive]

中文:
实例 [幺半群
  签名: M] : 群 (是单位.submonoid M)
  定义体: { (inferInstance : Monoid (IsUnit.submonoid M)) with
    inv := fun x => ⟨x.prop.unit⁻¹.val, x.prop.unit⁻¹.isUnit⟩
    inv_mul_cancel := fun x =>
      Subtype.ext ((Units.val_mul x.prop.unit⁻¹ _).trans x.prop.unit.inv_val) }

@[to_additive]

Depends on / 依赖: IsUnit, IsUnit.submonoid, Monoid, Subtype, Subtype.ext, Units.val_mul, inv_mul_cancel, inv_val, isUnit, submonoid, val_mul, x.prop.unit, x.prop.unit.inv_val
-/
noncomputable instance [Monoid M] : Group (IsUnit.submonoid M) :=
  { (inferInstance : Monoid (IsUnit.submonoid M)) with
    inv := fun x => ⟨x.prop.unit⁻¹.val, x.prop.unit⁻¹.isUnit⟩
    inv_mul_cancel := fun x =>
      Subtype.ext ((Units.val_mul x.prop.unit⁻¹ _).trans x.prop.unit.inv_val) }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: M] : CommGroup (IsUnit.submonoid M)
  body: { (inferInstance : Group (IsUnit.submonoid M)) with
    mul_comm := fun a b => by convert! mul_comm a b }

@[to_additive]

中文:
实例 [交换幺半群
  签名: M] : 交换群 (是单位.submonoid M)
  定义体: { (inferInstance : Group (IsUnit.submonoid M)) with
    mul_comm := fun a b => by convert! mul_comm a b }

@[to_additive]

Depends on / 依赖: IsUnit, IsUnit.submonoid, convert, mul_comm, submonoid
-/
noncomputable instance [CommMonoid M] : CommGroup (IsUnit.submonoid M) :=
  { (inferInstance : Group (IsUnit.submonoid M)) with
    mul_comm := fun a b => by convert! mul_comm a b }

@[to_additive]
/--
theorem `_root_.IsUnit.submonoid.coe_inv` / 定理 `_root_.IsUnit.submonoid.coe_inv`

English:
theorem _root_.IsUnit.submonoid.coe_inv
  given: [Monoid M] (x : IsUnit.submonoid M)
  proof: rfl

@[deprecated (since := "2026-05-24")]
alias _root_.AddSubmonoid.IsUnit.Submonoid.coe_neg := IsAddUnit.addSubmonoid.coe_neg

中文:
定理 _root_.是单位.submonoid.coe_inv
  条件: [幺半群 M] (x : 是单位.submonoid M)
  证明: rfl

@[deprecated (since := "2026-05-24")]
alias _root_.AddSubmonoid.IsUnit.Submonoid.coe_neg := IsAddUnit.addSubmonoid.coe_neg
-/
theorem _root_.IsUnit.submonoid.coe_inv [Monoid M] (x : IsUnit.submonoid M) :
    ↑x⁻¹ = (↑x.prop.unit⁻¹ : M) :=
  rfl

@[deprecated (since := "2026-05-24")]
alias _root_.AddSubmonoid.IsUnit.Submonoid.coe_neg := IsAddUnit.addSubmonoid.coe_neg
set_option linter.dupNamespace false in
@[to_additive existing, deprecated (since := "2026-05-24")]
alias IsUnit.Submonoid.coe_inv := IsUnit.submonoid.coe_inv

section Monoid

variable [Monoid M] (S : Submonoid M)

/-- `S.leftInv` is the submonoid containing all the left inverses of `S`. -/
@[to_additive
/-- `S.leftNeg` is the additive submonoid containing all the left additive inverses of `S`. -/]
/--
Definition of `leftInv` / `leftInv` 的定义

English:
definition leftInv
  signature: : Submonoid M where
  body: { x : M | exists y : S, x * y = 1 }
  one_mem' := ⟨1, mul_one 1⟩
  mul_mem' := fun {a} _b ⟨a', ha⟩ ⟨b', hb⟩ =>
    ⟨b' * a', by simp only [coe_mul, ← mul_assoc, mul_assoc a, hb, mul_one, ha]⟩

@[to_additive]

中文:
定义 leftInv
  签名: : 子幺半群 M where
  定义体: { x : M | exists y : S, x * y = 1 }
  one_mem' := ⟨1, mul_one 1⟩
  mul_mem' := fun {a} _b ⟨a', ha⟩ ⟨b', hb⟩ =>
    ⟨b' * a', by simp only [coe_mul, ← mul_assoc, mul_assoc a, hb, mul_one, ha]⟩

@[to_additive]
-/
def leftInv : Submonoid M where
  carrier := { x : M | exists y : S, x * y = 1 }
  one_mem' := ⟨1, mul_one 1⟩
  mul_mem' := fun {a} _b ⟨a', ha⟩ ⟨b', hb⟩ =>
    ⟨b' * a', by simp only [coe_mul, ← mul_assoc, mul_assoc a, hb, mul_one, ha]⟩

@[to_additive]
/--
theorem `leftInv_leftInv_le` / 定理 `leftInv_leftInv_le`

English:
theorem leftInv_leftInv_le
  statement: S.leftInv.leftInv <= S
  proof: by
  rintro x ⟨⟨y, z, h₁⟩, h₂ : x * y = 1⟩
  convert! z.prop
  rw [← mul_one x]; rw [← h₁]; rw [← mul_assoc]; rw [h₂]; rw [one_mul]

@[to_additive]

中文:
定理 leftInv_leftInv_le
  结论: S.leftInv.leftInv <= S
  证明: by
  rintro x ⟨⟨y, z, h₁⟩, h₂ : x * y = 1⟩
  convert! z.prop
  rw [← mul_one x]; rw [← h₁]; rw [← mul_assoc]; rw [h₂]; rw [one_mul]

@[to_additive]

Depends on / 依赖: convert, mul_assoc, mul_one, one_mul, z.prop
-/
theorem leftInv_leftInv_le : S.leftInv.leftInv <= S := by
  rintro x ⟨⟨y, z, h₁⟩, h₂ : x * y = 1⟩
  convert! z.prop
  rw [← mul_one x]; rw [← h₁]; rw [← mul_assoc]; rw [h₂]; rw [one_mul]

@[to_additive]
/--
theorem `unit_mem_leftInv` / 定理 `unit_mem_leftInv`

English:
theorem unit_mem_leftInv
  given: (x : Mˣ) (hx : (x : M) in S)
  statement: ((x⁻¹ :) : M) in S.leftInv
  proof: ⟨⟨x, hx⟩, x.inv_val⟩

@[to_additive]

中文:
定理 unit_mem_leftInv
  条件: (x : Mˣ) (hx : (x : M) in S)
  结论: ((x⁻¹ :) : M) in S.leftInv
  证明: ⟨⟨x, hx⟩, x.inv_val⟩

@[to_additive]

Depends on / 依赖: inv_val, x.inv_val
-/
theorem unit_mem_leftInv (x : Mˣ) (hx : (x : M) in S) : ((x⁻¹ :) : M) in S.leftInv :=
  ⟨⟨x, hx⟩, x.inv_val⟩

@[to_additive]
/--
theorem `leftInv_leftInv_eq` / 定理 `leftInv_leftInv_eq`

English:
theorem leftInv_leftInv_eq
  given: (hS : S <= IsUnit.submonoid M)
  statement: S.leftInv.leftInv = S
  proof: by
  refine le_antisymm S.leftInv_leftInv_le ?_
  intro x hx
  have : x = ((hS hx).unit⁻¹⁻¹ : Mˣ) := by
    rw [inv_inv (hS hx).unit]
    rfl
  rw [this]
  exact S.leftInv.unit_mem_leftInv _ (S.unit_mem_leftInv _ hx)

中文:
定理 leftInv_leftInv_eq
  条件: (hS : S <= 是单位.submonoid M)
  结论: S.leftInv.leftInv = S
  证明: by
  refine le_antisymm S.leftInv_leftInv_le ?_
  intro x hx
  have : x = ((hS hx).unit⁻¹⁻¹ : Mˣ) := by
    rw [inv_inv (hS hx).unit]
    rfl
  rw [this]
  exact S.leftInv.unit_mem_leftInv _ (S.unit_mem_leftInv _ hx)

Depends on / 依赖: S.leftInv.unit_mem_leftInv, S.leftInv_leftInv_le, S.unit_mem_leftInv, inv_inv, le_antisymm, leftInv, leftInv_leftInv_le, unit_mem_leftInv
-/
theorem leftInv_leftInv_eq (hS : S <= IsUnit.submonoid M) : S.leftInv.leftInv = S := by
  refine le_antisymm S.leftInv_leftInv_le ?_
  intro x hx
  have : x = ((hS hx).unit⁻¹⁻¹ : Mˣ) := by
    rw [inv_inv (hS hx).unit]
    rfl
  rw [this]
  exact S.leftInv.unit_mem_leftInv _ (S.unit_mem_leftInv _ hx)

/-- The function from `S.leftInv` to `S` sending an element to its right inverse in `S`.
This is a `MonoidHom` when `M` is commutative. -/
@[to_additive
/-- The function from `S.leftAdd` to `S` sending an element to its right additive
inverse in `S`. This is an `AddMonoidHom` when `M` is commutative. -/]
/--
Definition of `fromLeftInv` / `fromLeftInv` 的定义

English:
definition fromLeftInv
  signature: : S.leftInv -> S
  body: fun x => x.prop.choose

@[to_additive (attr := simp)]

中文:
定义 fromLeftInv
  签名: : S.leftInv -> S
  定义体: fun x => x.prop.choose

@[to_additive (attr := simp)]

Depends on / 依赖: x.prop.choose
-/
noncomputable def fromLeftInv : S.leftInv -> S := fun x => x.prop.choose

@[to_additive (attr := simp)]
/--
theorem `mul_fromLeftInv` / 定理 `mul_fromLeftInv`

English:
theorem mul_fromLeftInv
  given: (x : S.leftInv)
  statement: (x : M) * S.fromLeftInv x = 1
  proof: x.prop.choose_spec

@[to_additive (attr := simp)]

中文:
定理 mul_fromLeftInv
  条件: (x : S.leftInv)
  结论: (x : M) * S.fromLeftInv x = 1
  证明: x.prop.choose_spec

@[to_additive (attr := simp)]

Depends on / 依赖: choose_spec, x.prop.choose_spec
-/
theorem mul_fromLeftInv (x : S.leftInv) : (x : M) * S.fromLeftInv x = 1 :=
  x.prop.choose_spec

@[to_additive (attr := simp)]
/--
theorem `fromLeftInv_one` / 定理 `fromLeftInv_one`

English:
theorem fromLeftInv_one
  statement: S.fromLeftInv 1 = 1
  proof: (one_mul _).symm.trans (Subtype.ext <| S.mul_fromLeftInv 1)

中文:
定理 fromLeftInv_one
  结论: S.fromLeftInv 1 = 1
  证明: (one_mul _).symm.trans (Subtype.ext <| S.mul_fromLeftInv 1)

Depends on / 依赖: S.mul_fromLeftInv, Subtype, Subtype.ext, mul_fromLeftInv, one_mul, symm.trans
-/
theorem fromLeftInv_one : S.fromLeftInv 1 = 1 :=
  (one_mul _).symm.trans (Subtype.ext <| S.mul_fromLeftInv 1)

end Monoid

section CommMonoid

variable [CommMonoid M] (S : Submonoid M)

@[to_additive (attr := simp)]
/--
theorem `fromLeftInv_mul` / 定理 `fromLeftInv_mul`

English:
theorem fromLeftInv_mul
  given: (x : S.leftInv)
  statement: (S.fromLeftInv x : M) * x = 1
  proof: by
  rw [mul_comm]; rw [mul_fromLeftInv]

@[to_additive]

中文:
定理 fromLeftInv_mul
  条件: (x : S.leftInv)
  结论: (S.fromLeftInv x : M) * x = 1
  证明: by
  rw [mul_comm]; rw [mul_fromLeftInv]

@[to_additive]

Depends on / 依赖: mul_comm, mul_fromLeftInv
-/
theorem fromLeftInv_mul (x : S.leftInv) : (S.fromLeftInv x : M) * x = 1 := by
  rw [mul_comm]; rw [mul_fromLeftInv]

@[to_additive]
/--
theorem `leftInv_le_isUnit` / 定理 `leftInv_le_isUnit`

English:
theorem leftInv_le_isUnit
  statement: S.leftInv <= IsUnit.submonoid M
  proof: fun x ⟨y, hx⟩ =>
  ⟨⟨x, y, hx, mul_comm x y ▸ hx⟩, rfl⟩

@[to_additive]

中文:
定理 leftInv_le_isUnit
  结论: S.leftInv <= 是单位.submonoid M
  证明: fun x ⟨y, hx⟩ =>
  ⟨⟨x, y, hx, mul_comm x y ▸ hx⟩, rfl⟩

@[to_additive]
-/
theorem leftInv_le_isUnit : S.leftInv <= IsUnit.submonoid M := fun x ⟨y, hx⟩ =>
  ⟨⟨x, y, hx, mul_comm x y ▸ hx⟩, rfl⟩

@[to_additive]
/--
theorem `fromLeftInv_eq_iff` / 定理 `fromLeftInv_eq_iff`

English:
theorem fromLeftInv_eq_iff
  given: (a : S.leftInv) (b : M)
  proof: by
  rw [← IsUnit.mul_right_inj (leftInv_le_isUnit _ a.prop)]; rw [S.mul_fromLeftInv]; rw [eq_comm]

中文:
定理 fromLeftInv_eq_iff
  条件: (a : S.leftInv) (b : M)
  证明: by
  rw [← IsUnit.mul_right_inj (leftInv_le_isUnit _ a.prop)]; rw [S.mul_fromLeftInv]; rw [eq_comm]

Depends on / 依赖: IsUnit, IsUnit.mul_right_inj, S.mul_fromLeftInv, a.prop, eq_comm, leftInv_le_isUnit, mul_fromLeftInv, mul_right_inj
-/
theorem fromLeftInv_eq_iff (a : S.leftInv) (b : M) :
    (S.fromLeftInv a : M) = b ↔ (a : M) * b = 1 := by
  rw [← IsUnit.mul_right_inj (leftInv_le_isUnit _ a.prop)]; rw [S.mul_fromLeftInv]; rw [eq_comm]

/-- The `MonoidHom` from `S.leftInv` to `S` sending an element to its right inverse in `S`. -/
@[to_additive (attr := simps) /-- The `AddMonoidHom` from `S.leftNeg` to `S` sending an element to
its right additive inverse in `S`. -/]
/--
Definition of `fromCommLeftInv` / `fromCommLeftInv` 的定义

English:
definition fromCommLeftInv
  signature: : S.leftInv ->* S where
  body: S.fromLeftInv
  map_one' := S.fromLeftInv_one
  map_mul' x y :=
Subtype.ext by
      rw [fromLeftInv_eq_iff]; rw [mul_comm x]; rw [Submonoid.coe_mul]; rw [Submonoid.coe_mul]; rw [mul_assoc]; rw [←
        mul_assoc (x : M)]; rw [mul_fromLeftInv]; rw [one_mul]; rw [mul_fromLeftInv]

中文:
定义 fromCommLeftInv
  签名: : S.leftInv ->* S where
  定义体: S.fromLeftInv
  map_one' := S.fromLeftInv_one
  map_mul' x y :=
Subtype.ext by
      rw [fromLeftInv_eq_iff]; rw [mul_comm x]; rw [Submonoid.coe_mul]; rw [Submonoid.coe_mul]; rw [mul_assoc]; rw [←
        mul_assoc (x : M)]; rw [mul_fromLeftInv]; rw [one_mul]; rw [mul_fromLeftInv]

Depends on / 依赖: S.fromLeftInv, fromLeftInv
-/
noncomputable def fromCommLeftInv : S.leftInv ->* S where
  toFun := S.fromLeftInv
  map_one' := S.fromLeftInv_one
  map_mul' x y :=
Subtype.ext by
      rw [fromLeftInv_eq_iff]; rw [mul_comm x]; rw [Submonoid.coe_mul]; rw [Submonoid.coe_mul]; rw [mul_assoc]; rw [←
        mul_assoc (x : M)]; rw [mul_fromLeftInv]; rw [one_mul]; rw [mul_fromLeftInv]

variable (hS : S <= IsUnit.submonoid M)

set_option backward.isDefEq.respectTransparency false in
/-- The submonoid of pointwise inverse of `S` is `MulEquiv` to `S`. -/
@[to_additive (attr := simps apply) /-- The additive submonoid of pointwise additive inverse of `S`
is `AddEquiv` to `S`. -/]
/--
Definition of `leftInvEquiv` / `leftInvEquiv` 的定义

English:
definition leftInvEquiv
  signature: : S.leftInv ≃* S
  body: { S.fromCommLeftInv with
    invFun := fun x => ⟨↑(hS x.2).unit⁻¹, x, by simp⟩
    left_inv := by
      intro x
      ext
      simp [← Units.mul_eq_one_iff_inv_eq]
    right_inv := by
      rintro ⟨x, hx⟩
      ext
      simp [fromLeftInv_eq_iff] }

@[to_additive (attr := simp)]

中文:
定义 leftInvEquiv
  签名: : S.leftInv ≃* S
  定义体: { S.fromCommLeftInv with
    invFun := fun x => ⟨↑(hS x.2).unit⁻¹, x, by simp⟩
    left_inv := by
      intro x
      ext
      simp [← Units.mul_eq_one_iff_inv_eq]
    right_inv := by
      rintro ⟨x, hx⟩
      ext
      simp [fromLeftInv_eq_iff] }

@[to_additive (attr := simp)]

Depends on / 依赖: S.fromCommLeftInv, Units.mul_eq_one_iff_inv_eq, fromCommLeftInv, fromLeftInv_eq_iff, invFun, left_inv, mul_eq_one_iff_inv_eq, right_inv
-/
noncomputable def leftInvEquiv : S.leftInv ≃* S :=
  { S.fromCommLeftInv with
    invFun := fun x => ⟨↑(hS x.2).unit⁻¹, x, by simp⟩
    left_inv := by
      intro x
      ext
      simp [← Units.mul_eq_one_iff_inv_eq]
    right_inv := by
      rintro ⟨x, hx⟩
      ext
      simp [fromLeftInv_eq_iff] }

@[to_additive (attr := simp)]
/--
theorem `fromLeftInv_leftInvEquiv_symm` / 定理 `fromLeftInv_leftInvEquiv_symm`

English:
theorem fromLeftInv_leftInvEquiv_symm
  given: (x : S)
  statement: S.fromLeftInv ((S.leftInvEquiv hS).symm x) = x
  proof: (S.leftInvEquiv hS).right_inv x

@[to_additive (attr := simp)]

中文:
定理 fromLeftInv_leftInvEquiv_symm
  条件: (x : S)
  结论: S.fromLeftInv ((S.leftInvEquiv hS).symm x) = x
  证明: (S.leftInvEquiv hS).right_inv x

@[to_additive (attr := simp)]

Depends on / 依赖: S.leftInvEquiv, leftInvEquiv, right_inv
-/
theorem fromLeftInv_leftInvEquiv_symm (x : S) : S.fromLeftInv ((S.leftInvEquiv hS).symm x) = x :=
  (S.leftInvEquiv hS).right_inv x

@[to_additive (attr := simp)]
/--
theorem `leftInvEquiv_symm_fromLeftInv` / 定理 `leftInvEquiv_symm_fromLeftInv`

English:
theorem leftInvEquiv_symm_fromLeftInv
  given: (x : S.leftInv)
  proof: (S.leftInvEquiv hS).left_inv x

@[to_additive]

中文:
定理 leftInvEquiv_symm_fromLeftInv
  条件: (x : S.leftInv)
  证明: (S.leftInvEquiv hS).left_inv x

@[to_additive]

Depends on / 依赖: S.leftInvEquiv, leftInvEquiv, left_inv
-/
theorem leftInvEquiv_symm_fromLeftInv (x : S.leftInv) :
    (S.leftInvEquiv hS).symm (S.fromLeftInv x) = x :=
  (S.leftInvEquiv hS).left_inv x

@[to_additive]
/--
theorem `leftInvEquiv_mul` / 定理 `leftInvEquiv_mul`

English:
theorem leftInvEquiv_mul
  given: (x : S.leftInv)
  statement: (S.leftInvEquiv hS x : M) * x = 1
  proof: by
  simpa only [leftInvEquiv_apply, fromCommLeftInv] using fromLeftInv_mul S x

@[to_additive]

中文:
定理 leftInvEquiv_mul
  条件: (x : S.leftInv)
  结论: (S.leftInvEquiv hS x : M) * x = 1
  证明: by
  simpa only [leftInvEquiv_apply, fromCommLeftInv] using fromLeftInv_mul S x

@[to_additive]

Depends on / 依赖: fromCommLeftInv, fromLeftInv_mul, leftInvEquiv_apply
-/
theorem leftInvEquiv_mul (x : S.leftInv) : (S.leftInvEquiv hS x : M) * x = 1 := by
  simpa only [leftInvEquiv_apply, fromCommLeftInv] using fromLeftInv_mul S x

@[to_additive]
/--
theorem `mul_leftInvEquiv` / 定理 `mul_leftInvEquiv`

English:
theorem mul_leftInvEquiv
  given: (x : S.leftInv)
  statement: (x : M) * S.leftInvEquiv hS x = 1
  proof: by
  simp only [leftInvEquiv_apply, fromCommLeftInv, mul_fromLeftInv]

@[to_additive (attr := simp)]

中文:
定理 mul_leftInvEquiv
  条件: (x : S.leftInv)
  结论: (x : M) * S.leftInvEquiv hS x = 1
  证明: by
  simp only [leftInvEquiv_apply, fromCommLeftInv, mul_fromLeftInv]

@[to_additive (attr := simp)]

Depends on / 依赖: fromCommLeftInv, leftInvEquiv_apply, mul_fromLeftInv
-/
theorem mul_leftInvEquiv (x : S.leftInv) : (x : M) * S.leftInvEquiv hS x = 1 := by
  simp only [leftInvEquiv_apply, fromCommLeftInv, mul_fromLeftInv]

@[to_additive (attr := simp)]
/--
theorem `leftInvEquiv_symm_mul` / 定理 `leftInvEquiv_symm_mul`

English:
theorem leftInvEquiv_symm_mul
  given: (x : S)
  statement: ((S.leftInvEquiv hS).symm x : M) * x = 1
  proof: by
  convert! S.mul_leftInvEquiv hS ((S.leftInvEquiv hS).symm x)
  simp

@[to_additive (attr := simp)]

中文:
定理 leftInvEquiv_symm_mul
  条件: (x : S)
  结论: ((S.leftInvEquiv hS).symm x : M) * x = 1
  证明: by
  convert! S.mul_leftInvEquiv hS ((S.leftInvEquiv hS).symm x)
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: S.leftInvEquiv, S.mul_leftInvEquiv, convert, leftInvEquiv, mul_leftInvEquiv
-/
theorem leftInvEquiv_symm_mul (x : S) : ((S.leftInvEquiv hS).symm x : M) * x = 1 := by
  convert! S.mul_leftInvEquiv hS ((S.leftInvEquiv hS).symm x)
  simp

@[to_additive (attr := simp)]
/--
theorem `mul_leftInvEquiv_symm` / 定理 `mul_leftInvEquiv_symm`

English:
theorem mul_leftInvEquiv_symm
  given: (x : S)
  statement: (x : M) * (S.leftInvEquiv hS).symm x = 1
  proof: by
  convert! S.leftInvEquiv_mul hS ((S.leftInvEquiv hS).symm x)
  simp

中文:
定理 mul_leftInvEquiv_symm
  条件: (x : S)
  结论: (x : M) * (S.leftInvEquiv hS).symm x = 1
  证明: by
  convert! S.leftInvEquiv_mul hS ((S.leftInvEquiv hS).symm x)
  simp

Depends on / 依赖: S.leftInvEquiv, S.leftInvEquiv_mul, convert, leftInvEquiv, leftInvEquiv_mul
-/
theorem mul_leftInvEquiv_symm (x : S) : (x : M) * (S.leftInvEquiv hS).symm x = 1 := by
  convert! S.leftInvEquiv_mul hS ((S.leftInvEquiv hS).symm x)
  simp

end CommMonoid

section Group

variable [Group M] (S : Submonoid M)

open scoped Pointwise

@[to_additive]
/--
theorem `leftInv_eq_inv` / 定理 `leftInv_eq_inv`

English:
theorem leftInv_eq_inv
  statement: S.leftInv = S⁻¹
  proof: Submonoid.ext fun _ =>
    ⟨fun h => Submonoid.mem_inv.mpr ((inv_eq_of_mul_eq_one_right h.choose_spec).symm ▸
      h.choose.prop),
      fun h => ⟨⟨_, h⟩, mul_inv_cancel _⟩⟩

@[to_additive (attr := simp)]

中文:
定理 leftInv_eq_inv
  结论: S.leftInv = S⁻¹
  证明: Submonoid.ext fun _ =>
    ⟨fun h => Submonoid.mem_inv.mpr ((inv_eq_of_mul_eq_one_right h.choose_spec).symm ▸
      h.choose.prop),
      fun h => ⟨⟨_, h⟩, mul_inv_cancel _⟩⟩

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid, Submonoid.ext, Submonoid.mem_inv.mpr, choose_spec, h.choose.prop, h.choose_spec, inv_eq_of_mul_eq_one_right, mem_inv, mul_inv_cancel
-/
theorem leftInv_eq_inv : S.leftInv = S⁻¹ :=
  Submonoid.ext fun _ =>
    ⟨fun h => Submonoid.mem_inv.mpr ((inv_eq_of_mul_eq_one_right h.choose_spec).symm ▸
      h.choose.prop),
      fun h => ⟨⟨_, h⟩, mul_inv_cancel _⟩⟩

@[to_additive (attr := simp)]
/--
theorem `fromLeftInv_eq_inv` / 定理 `fromLeftInv_eq_inv`

English:
theorem fromLeftInv_eq_inv
  given: (x : S.leftInv)
  statement: (S.fromLeftInv x : M) = (x : M)⁻¹
  proof: by
  rw [← mul_right_inj (x : M)]; rw [mul_inv_cancel]; rw [mul_fromLeftInv]

中文:
定理 fromLeftInv_eq_inv
  条件: (x : S.leftInv)
  结论: (S.fromLeftInv x : M) = (x : M)⁻¹
  证明: by
  rw [← mul_right_inj (x : M)]; rw [mul_inv_cancel]; rw [mul_fromLeftInv]

Depends on / 依赖: mul_fromLeftInv, mul_inv_cancel, mul_right_inj
-/
theorem fromLeftInv_eq_inv (x : S.leftInv) : (S.fromLeftInv x : M) = (x : M)⁻¹ := by
  rw [← mul_right_inj (x : M)]; rw [mul_inv_cancel]; rw [mul_fromLeftInv]

end Group

section CommGroup

variable [CommGroup M] (S : Submonoid M) (hS : S <= IsUnit.submonoid M)

@[to_additive (attr := simp)]
/--
theorem `leftInvEquiv_symm_eq_inv` / 定理 `leftInvEquiv_symm_eq_inv`

English:
theorem leftInvEquiv_symm_eq_inv
  given: (x : S)
  statement: ((S.leftInvEquiv hS).symm x : M) = (x : M)⁻¹
  proof: by
  rw [← mul_right_inj (x : M)]; rw [mul_inv_cancel]; rw [mul_leftInvEquiv_symm]

中文:
定理 leftInvEquiv_symm_eq_inv
  条件: (x : S)
  结论: ((S.leftInvEquiv hS).symm x : M) = (x : M)⁻¹
  证明: by
  rw [← mul_right_inj (x : M)]; rw [mul_inv_cancel]; rw [mul_leftInvEquiv_symm]

Depends on / 依赖: mul_inv_cancel, mul_leftInvEquiv_symm, mul_right_inj
-/
theorem leftInvEquiv_symm_eq_inv (x : S) : ((S.leftInvEquiv hS).symm x : M) = (x : M)⁻¹ := by
  rw [← mul_right_inj (x : M)]; rw [mul_inv_cancel]; rw [mul_leftInvEquiv_symm]

end CommGroup

end Submonoid
