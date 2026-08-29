/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Units.Defs

/-! # Group actions on and by `Mˣ`

This file provides the action of a unit on a type `α`, `SMul Mˣ α`, in the presence of
`SMul M α`, with the obvious definition stated in `Units.smul_def`. This definition preserves
`MulAction` and `DistribMulAction` structures too.

Additionally, a `MulAction G M` for some group `G` satisfying some additional properties admits a
`MulAction G Mˣ` structure, again with the obvious definition stated in `Units.coe_smul`.
These instances use a primed name.

The results are repeated for `AddUnits` and `VAdd` where relevant.
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {G H M N α : Type*}

namespace Units

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [SMul M α] : SMul Mˣ α where smul m a
  body: (m : M) • a

中文:
实例 [幺半群
  签名: M] [标量乘法 M α] : 标量乘法 Mˣ α where smul m a
  定义体: (m : M) • a
-/
@[to_additive] instance [Monoid M] [SMul M α] : SMul Mˣ α where smul m a := (m : M) • a

/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: [Monoid M] [SMul M α] (m : Mˣ) (a : α)
  statement: m • a = (m : M) • a
  proof: rfl

@[to_additive, simp]

中文:
引理 smul_def
  条件: [幺半群 M] [标量乘法 M α] (m : Mˣ) (a : α)
  结论: m • a = (m : M) • a
  证明: rfl

@[to_additive, simp]
-/
@[to_additive] lemma smul_def [Monoid M] [SMul M α] (m : Mˣ) (a : α) : m • a = (m : M) • a := rfl

@[to_additive, simp]
/--
lemma `smul_mk_apply` / 引理 `smul_mk_apply`

English:
lemma smul_mk_apply
  given: {M α : Type*} [Monoid M] [SMul M α] (m n : M) (h₁) (h₂) (a : α)
  proof: rfl

@[simp]

中文:
引理 smul_mk_apply
  条件: {M α : 类型} [幺半群 M] [标量乘法 M α] (m n : M) (h₁) (h₂) (a : α)
  证明: rfl

@[simp]
-/
lemma smul_mk_apply {M α : Type*} [Monoid M] [SMul M α] (m n : M) (h₁) (h₂) (a : α) :
    (⟨m, n, h₁, h₂⟩ : Mˣ) • a = m • a := rfl

@[simp]
/--
lemma `smul_isUnit` / 引理 `smul_isUnit`

English:
lemma smul_isUnit
  given: [Monoid M] [SMul M α] {m : M} (hm : IsUnit m) (a : α)
  statement: hm.unit • a = m • a
  proof: rfl

@[to_additive]

中文:
引理 smul_isUnit
  条件: [幺半群 M] [标量乘法 M α] {m : M} (hm : 是单位 m) (a : α)
  结论: hm.unit • a = m • a
  证明: rfl

@[to_additive]
-/
lemma smul_isUnit [Monoid M] [SMul M α] {m : M} (hm : IsUnit m) (a : α) : hm.unit • a = m • a := rfl

@[to_additive]
/--
lemma `_root_.IsUnit.inv_smul` / 引理 `_root_.IsUnit.inv_smul`

English:
lemma _root_.IsUnit.inv_smul
  given: [Monoid α] {a : α} (h : IsUnit a)
  statement: h.unit⁻¹ • a = 1
  proof: h.val_inv_mul

@[to_additive]

中文:
引理 _root_.是单位.inv_smul
  条件: [幺半群 α] {a : α} (h : 是单位 a)
  结论: h.unit⁻¹ • a = 1
  证明: h.val_inv_mul

@[to_additive]

Depends on / 依赖: h.val_inv_mul, val_inv_mul
-/
lemma _root_.IsUnit.inv_smul [Monoid α] {a : α} (h : IsUnit a) : h.unit⁻¹ • a = 1 := h.val_inv_mul

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [SMul M α] [FaithfulSMul M α] : FaithfulSMul Mˣ α where
  body: Units.ext eq_of_smul_eq_smul h

@[to_additive]

中文:
实例 [幺半群
  签名: M] [标量乘法 M α] [忠实标量乘法 M α] : 忠实标量乘法 Mˣ α where
  定义体: Units.ext eq_of_smul_eq_smul h

@[to_additive]

Depends on / 依赖: Units.ext, eq_of_smul_eq_smul
-/
instance [Monoid M] [SMul M α] [FaithfulSMul M α] : FaithfulSMul Mˣ α where
eq_of_smul_eq_smul h := Units.ext eq_of_smul_eq_smul h

@[to_additive]
/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: [Monoid M] [MulAction M α]
  body: one_smul M
  mul_smul m n := mul_smul (m : M) n

@[to_additive]

中文:
实例 instMulAction
  签名: [幺半群 M] [乘法作用 M α]
  定义体: one_smul M
  mul_smul m n := mul_smul (m : M) n

@[to_additive]

Depends on / 依赖: one_smul
-/
instance instMulAction [Monoid M] [MulAction M α] : MulAction Mˣ α where
  one_smul := one_smul M
  mul_smul m n := mul_smul (m : M) n

@[to_additive]
/--
Instance `smulCommClass_left` / 实例 `smulCommClass_left`

English:
instance smulCommClass_left
  signature: [Monoid M] [SMul M α] [SMul N α] [SMulCommClass M N α]
  body: smul_comm (m : M) n

@[to_additive]

中文:
实例 smulCommClass_left
  签名: [幺半群 M] [标量乘法 M α] [标量乘法 N α] [标量交换类 M N α]
  定义体: smul_comm (m : M) n

@[to_additive]

Depends on / 依赖: smul_comm
-/
instance smulCommClass_left [Monoid M] [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass Mˣ N α where smul_comm m n := smul_comm (m : M) n

@[to_additive]
/--
Instance `smulCommClass_right` / 实例 `smulCommClass_right`

English:
instance smulCommClass_right
  signature: [Monoid N] [SMul M α] [SMul N α] [SMulCommClass M N α]
  body: smul_comm m (n : N)

@[to_additive]

中文:
实例 smulCommClass_right
  签名: [幺半群 N] [标量乘法 M α] [标量乘法 N α] [标量交换类 M N α]
  定义体: smul_comm m (n : N)

@[to_additive]

Depends on / 依赖: smul_comm
-/
instance smulCommClass_right [Monoid N] [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M Nˣ α where smul_comm m n := smul_comm m (n : N)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
  body: smul_assoc (m : M) n

中文:
实例 [幺半群
  签名: M] [标量乘法 M N] [标量乘法 M α] [标量乘法 N α] [标量塔 M N α] :
  定义体: smul_assoc (m : M) n

Depends on / 依赖: smul_assoc
-/
instance [Monoid M] [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower Mˣ N α where smul_assoc m n := smul_assoc (m : M) n

/-! ### Action of a group `G` on units of `M` -/

/-- If an action `G` associates and commutes with multiplication on `M`, then it lifts to an
action on `Mˣ`. Notably, this provides `MulAction Mˣ Nˣ` under suitable conditions. -/
@[to_additive]
/--
Instance `mulAction'` / 实例 `mulAction'`

English:
instance mulAction'
  signature: [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M]
  body: ⟨g • (m : M), (g⁻¹ • ((m⁻¹ : Mˣ) : M)),
      by rw [smul_mul_smul_comm, Units.mul_inv, mul_inv_cancel, one_smul],
      by rw [smul_mul_smul_comm, Units.inv_mul, inv_mul_cancel, one_smul]⟩
one_smul _ := Units.ext one_smul _ _
mul_smul _ _ _ := Units.ext mul_smul _ _ _

中文:
实例 mulAction'
  签名: [群 G] [幺半群 M] [乘法作用 G M] [标量交换类 G M M]
  定义体: ⟨g • (m : M), (g⁻¹ • ((m⁻¹ : Mˣ) : M)),
      by rw [smul_mul_smul_comm, Units.mul_inv, mul_inv_cancel, one_smul],
      by rw [smul_mul_smul_comm, Units.inv_mul, inv_mul_cancel, one_smul]⟩
one_smul _ := Units.ext one_smul _ _
mul_smul _ _ _ := Units.ext mul_smul _ _ _

Depends on / 依赖: Units.ext, Units.inv_mul, Units.mul_inv, inv_mul, inv_mul_cancel, mul_inv, mul_inv_cancel, mul_smul, one_smul, smul_mul_smul_comm
-/
instance mulAction' [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M]
    [IsScalarTower G M M] : MulAction G Mˣ where
  smul g m :=
    ⟨g • (m : M), (g⁻¹ • ((m⁻¹ : Mˣ) : M)),
      by rw [smul_mul_smul_comm, Units.mul_inv, mul_inv_cancel, one_smul],
      by rw [smul_mul_smul_comm, Units.inv_mul, inv_mul_cancel, one_smul]⟩
one_smul _ := Units.ext one_smul _ _
mul_smul _ _ _ := Units.ext mul_smul _ _ _

/-- `Units.mulAction' : MulAction G Mˣ` creates a diamond when `G = Mˣ` and `M` is commutative.

Discussed [on Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/units.2Emul_action'.20diamond/near/246400399). -/
example {M} [CommMonoid M] :
    (mulAction'.toSMul : SMul Mˣ Mˣ) = instSMulOfMul := by
  fail_if_success rfl -- there is an instance diamond here
  ext
  rfl

/-- This is not the usual `smul_eq_mul` because `mulAction'` creates a diamond.

Discussed [on Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/units.2Emul_action'.20diamond/near/246400399). -/
@[simp]
/--
lemma `smul_eq_mul` / 引理 `smul_eq_mul`

English:
lemma smul_eq_mul
  given: {M} [CommMonoid M] (u₁ u₂ : Mˣ)
  proof: by
  ext
  rfl

@[to_additive (attr := simp)]

中文:
引理 smul_eq_mul
  条件: {M} [交换幺半群 M] (u₁ u₂ : Mˣ)
  证明: by
  ext
  rfl

@[to_additive (attr := simp)]
-/
lemma smul_eq_mul {M} [CommMonoid M] (u₁ u₂ : Mˣ) :
    u₁ • u₂ = u₁ * u₂ := by
  ext
  rfl

@[to_additive (attr := simp)]
/--
lemma `val_smul` / 引理 `val_smul`

English:
lemma val_smul
  statement: [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
  proof: rfl

中文:
引理 val_smul
  结论: [群 G] [幺半群 M] [乘法作用 G M] [标量交换类 G M M] [标量塔 G M M]
  证明: rfl
-/
lemma val_smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    (g : G) (m : Mˣ) : ↑(g • m) = g • (m : M) := rfl

/-- Note that this lemma exists more generally as the global `smul_inv` -/
@[to_additive (attr := simp)]
/--
lemma `smul_inv` / 引理 `smul_inv`

English:
lemma smul_inv
  statement: [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
  proof: ext rfl

中文:
引理 smul_inv
  结论: [群 G] [幺半群 M] [乘法作用 G M] [标量交换类 G M M] [标量塔 G M M]
  证明: ext rfl
-/
lemma smul_inv [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    (g : G) (m : Mˣ) : (g • m)⁻¹ = g⁻¹ • m⁻¹ := ext rfl

/-- Transfer `SMulCommClass G H M` to `SMulCommClass G H Mˣ`. -/
@[to_additive /-- Transfer `VAddCommClass G H M` to `VAddCommClass G H (AddUnits M)`. -/]
/--
Instance `smulCommClass'` / 实例 `smulCommClass'`

English:
instance smulCommClass'
  signature: [Group G] [Group H] [Monoid M] [MulAction G M] [SMulCommClass G M M]
  body: Units.ext smul_comm g h (m : M)

中文:
实例 smulCommClass'
  签名: [群 G] [群 H] [幺半群 M] [乘法作用 G M] [标量交换类 G M M]
  定义体: Units.ext smul_comm g h (m : M)

Depends on / 依赖: Units.ext, smul_comm
-/
instance smulCommClass' [Group G] [Group H] [Monoid M] [MulAction G M] [SMulCommClass G M M]
    [MulAction H M] [SMulCommClass H M M] [IsScalarTower G M M] [IsScalarTower H M M]
    [SMulCommClass G H M] :
SMulCommClass G H Mˣ where smul_comm g h m := Units.ext smul_comm g h (m : M)

/-- Transfer `IsScalarTower G H M` to `IsScalarTower G H Mˣ`. -/
@[to_additive /-- Transfer `VAddAssocClass G H M` to `VAddAssocClass G H (AddUnits M)`. -/]
/--
Instance `isScalarTower'` / 实例 `isScalarTower'`

English:
instance isScalarTower'
  signature: [SMul G H] [Group G] [Group H] [Monoid M] [MulAction G M]
  body: Units.ext smul_assoc g h (m : M)

中文:
实例 isScalarTower'
  签名: [标量乘法 G H] [群 G] [群 H] [幺半群 M] [乘法作用 G M]
  定义体: Units.ext smul_assoc g h (m : M)

Depends on / 依赖: Units.ext, smul_assoc
-/
instance isScalarTower' [SMul G H] [Group G] [Group H] [Monoid M] [MulAction G M]
    [SMulCommClass G M M] [MulAction H M] [SMulCommClass H M M] [IsScalarTower G M M]
    [IsScalarTower H M M] [IsScalarTower G H M] :
IsScalarTower G H Mˣ where smul_assoc g h m := Units.ext smul_assoc g h (m : M)

/-- Transfer `IsScalarTower G M α` to `IsScalarTower G Mˣ α`. -/
@[to_additive /-- Transfer `VAddAssocClass G M α` to `VAddAssocClass G (AddUnits M) α`. -/]
/--
Instance `isScalarTower'_left` / 实例 `isScalarTower'_left`

English:
instance isScalarTower'_left
  signature: [Group G] [Monoid M] [MulAction G M] [SMul M α] [SMul G α]
  body: smul_assoc g (m : M)

中文:
实例 isScalarTower'_left
  签名: [群 G] [幺半群 M] [乘法作用 G M] [标量乘法 M α] [标量乘法 G α]
  定义体: smul_assoc g (m : M)
-/
instance isScalarTower'_left [Group G] [Monoid M] [MulAction G M] [SMul M α] [SMul G α]
    [SMulCommClass G M M] [IsScalarTower G M M] [IsScalarTower G M α] :
    IsScalarTower G Mˣ α where smul_assoc g m := smul_assoc g (m : M)

-- Just to prove this transfers a particularly useful instance.
example [Monoid M] [Monoid N] [MulAction M N] [SMulCommClass M N N] [IsScalarTower M N N] :
    MulAction Mˣ Nˣ := Units.mulAction'

section MulDistribMulAction
variable {M N : Type*} [Monoid M] [Monoid N] [MulDistribMulAction M N]

/--
Definition of `mulDistribMulActionRight` / `mulDistribMulActionRight` 的定义

English:
abbreviation mulDistribMulActionRight
  signature: : MulDistribMulAction M Nˣ where
  body: ⟨m • u, m • u⁻¹, by simp [← smul_mul', smul_one], by simp [← smul_mul', smul_one]⟩
one_smul u := Units.ext one_smul ..
mul_smul m₁ m₂ u := Units.ext mul_smul ..
smul_mul m₁ u₁ u₂ := Units.ext smul_mul' ..
smul_one m := Units.ext smul_one m

中文:
缩写 mulDistribMulActionRight
  签名: : MulDistribMul作用 M Nˣ where
  定义体: ⟨m • u, m • u⁻¹, by simp [← smul_mul', smul_one], by simp [← smul_mul', smul_one]⟩
one_smul u := Units.ext one_smul ..
mul_smul m₁ m₂ u := Units.ext mul_smul ..
smul_mul m₁ u₁ u₂ := Units.ext smul_mul' ..
smul_one m := Units.ext smul_one m

Depends on / 依赖: smul_mul, smul_one
-/
abbrev mulDistribMulActionRight : MulDistribMulAction M Nˣ where
  smul m u := ⟨m • u, m • u⁻¹, by simp [← smul_mul', smul_one], by simp [← smul_mul', smul_one]⟩
one_smul u := Units.ext one_smul ..
mul_smul m₁ m₂ u := Units.ext mul_smul ..
smul_mul m₁ u₁ u₂ := Units.ext smul_mul' ..
smul_one m := Units.ext smul_one m

attribute [local instance] mulDistribMulActionRight

/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: (m : M) (u : Nˣ)
  statement: (m • u).val = m • u.val
  proof: rfl

中文:
引理 coe_smul
  条件: (m : M) (u : Nˣ)
  结论: (m • u).val = m • u.val
  证明: rfl
-/
@[simp, norm_cast] lemma coe_smul (m : M) (u : Nˣ) : (m • u).val = m • u.val := rfl
/--
lemma `coe_inv_smul` / 引理 `coe_inv_smul`

English:
lemma coe_inv_smul
  given: (m : M) (u : Nˣ)
  statement: (m • u)⁻¹.val = m • u⁻¹.val
  proof: rfl

中文:
引理 coe_inv_smul
  条件: (m : M) (u : Nˣ)
  结论: (m • u)⁻¹.val = m • u⁻¹.val
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inv_smul (m : M) (u : Nˣ) : (m • u)⁻¹.val = m • u⁻¹.val := rfl

end MulDistribMulAction
end Units

@[to_additive]
/--
lemma `IsUnit.smul` / 引理 `IsUnit.smul`

English:
lemma IsUnit.smul
  statement: [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
  proof: let ⟨u, hu⟩ := h
  hu ▸ ⟨g • u, Units.val_smul _ _⟩

中文:
引理 是单位.smul
  结论: [群 G] [幺半群 M] [乘法作用 G M] [标量交换类 G M M] [标量塔 G M M]
  证明: let ⟨u, hu⟩ := h
  hu ▸ ⟨g • u, Units.val_smul _ _⟩

Depends on / 依赖: Units.val_smul, val_smul
-/
lemma IsUnit.smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
    {m : M} (g : G) (h : IsUnit m) : IsUnit (g • m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨g • u, Units.val_smul _ _⟩
