/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.TypeTags

/-!
# Pretransitive group actions

This file defines a typeclass for pretransitive group actions.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.
- `a +ᵥ b` is used as notation for `VAdd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

public section

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {M G α β : Type*}

/-!
### (Pre)transitive action

`M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y` (or `g +ᵥ x = y`
for an additive action). A transitive action should furthermore have `α` nonempty.

In this section we define typeclasses `MulAction.IsPretransitive` and
`AddAction.IsPretransitive` and provide `MulAction.exists_smul_eq`/`AddAction.exists_vadd_eq`,
`MulAction.surjective_smul`/`AddAction.surjective_vadd` as public interface to access this
property. We do not provide typeclasses `*Action.IsTransitive`; users should assume
`[MulAction.IsPretransitive M α] [Nonempty α]` instead.
-/

/--
Definition of `AddAction.IsPretransitive` / `AddAction.IsPretransitive` 的定义

English:
class AddAction.IsPretransitive
  parameters: (M α : Type*) [VAdd M α]
  axioms and operations (1):
    - exists_vadd_eq : forall x y : α, exists g : M, g +ᵥ x = y

中文:
类 加法作用.是Pretransitive
  参数: (M α : 类型) [向量加法 M α]
  公理与运算 (1 个):
    - exists_vadd_eq : 对任意 x y : α, 存在 g : M, g +ᵥ x = y
-/
class AddAction.IsPretransitive (M α : Type*) [VAdd M α] : Prop where
  /-- There is `g` such that `g +ᵥ x = y`. -/
  exists_vadd_eq : forall x y : α, exists g : M, g +ᵥ x = y

/-- `M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y`.
  A transitive action should furthermore have `α` nonempty. -/
@[to_additive (attr := mk_iff)]
/--
Definition of `MulAction.IsPretransitive` / `MulAction.IsPretransitive` 的定义

English:
class MulAction.IsPretransitive
  parameters: (M α : Type*) [SMul M α]
  axioms and operations (1):
    - exists_smul_eq : forall x y : α, exists g : M, g • x = y

中文:
类 乘法作用.是Pretransitive
  参数: (M α : 类型) [标量乘法 M α]
  公理与运算 (1 个):
    - exists_smul_eq : 对任意 x y : α, 存在 g : M, g • x = y
-/
class MulAction.IsPretransitive (M α : Type*) [SMul M α] : Prop where
  /-- There is `g` such that `g • x = y`. -/
  exists_smul_eq : forall x y : α, exists g : M, g • x = y

@[to_additive]
/--
Instance `MulAction.instIsPretransitiveOfSubsingleton` / 实例 `MulAction.instIsPretransitiveOfSubsingleton`

English:
instance MulAction.instIsPretransitiveOfSubsingleton
  body: ⟨1, by
    simp only [one_smul, Subsingleton.elim x y] ⟩

中文:
实例 乘法作用.instIsPretransitiveOfSubsingleton
  定义体: ⟨1, by
    simp only [one_smul, Subsingleton.elim x y] ⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, one_smul
-/
instance MulAction.instIsPretransitiveOfSubsingleton
    {M α : Type*} [Monoid M] [MulAction M α] [Subsingleton α] :
    MulAction.IsPretransitive M α where
  exists_smul_eq x y := ⟨1, by
    simp only [one_smul, Subsingleton.elim x y] ⟩

namespace MulAction
variable (M) [SMul M α] [IsPretransitive M α]

@[to_additive]
/--
lemma `exists_smul_eq` / 引理 `exists_smul_eq`

English:
lemma exists_smul_eq
  given: (x y : α)
  statement: exists m : M, m • x = y
  proof: IsPretransitive.exists_smul_eq x y

@[to_additive]

中文:
引理 存在_smul_eq
  条件: (x y : α)
  结论: 存在 m : M, m • x = y
  证明: IsPretransitive.exists_smul_eq x y

@[to_additive]

Depends on / 依赖: IsPretransitive, IsPretransitive.exists_smul_eq, exists_smul_eq
-/
lemma exists_smul_eq (x y : α) : exists m : M, m • x = y := IsPretransitive.exists_smul_eq x y

@[to_additive]
/--
lemma `surjective_smul` / 引理 `surjective_smul`

English:
lemma surjective_smul
  given: (x : α)
  statement: Surjective fun c : M => c • x
  proof: exists_smul_eq M x

中文:
引理 surjective_smul
  条件: (x : α)
  结论: 满射 fun c : M => c • x
  证明: exists_smul_eq M x

Depends on / 依赖: exists_smul_eq
-/
lemma surjective_smul (x : α) : Surjective fun c : M => c • x := exists_smul_eq M x

/-- The left regular action of a group on itself is transitive. -/
@[to_additive /-- The regular action of a group on itself is transitive. -/]
/--
Instance `Regular.isPretransitive` / 实例 `Regular.isPretransitive`

English:
instance Regular.isPretransitive
  signature: [Group G]
  body: ⟨fun x y => ⟨y * x⁻¹, inv_mul_cancel_right _ _⟩⟩

中文:
实例 正则.isPretransitive
  签名: [群 G]
  定义体: ⟨fun x y => ⟨y * x⁻¹, inv_mul_cancel_right _ _⟩⟩

Depends on / 依赖: inv_mul_cancel_right
-/
instance Regular.isPretransitive [Group G] : IsPretransitive G G :=
  ⟨fun x y => ⟨y * x⁻¹, inv_mul_cancel_right _ _⟩⟩

/-- The right regular action of a group on itself is transitive. -/
@[to_additive /-- The right regular action of an additive group on itself is transitive. -/]
/--
Instance `Regular.isPretransitive_mulOpposite` / 实例 `Regular.isPretransitive_mulOpposite`

English:
instance Regular.isPretransitive_mulOpposite
  signature: [Group G]
  body: ⟨fun x y => ⟨.op (x⁻¹ * y), mul_inv_cancel_left _ _⟩⟩

中文:
实例 正则.isPretransitive_mulOpposite
  签名: [群 G]
  定义体: ⟨fun x y => ⟨.op (x⁻¹ * y), mul_inv_cancel_left _ _⟩⟩

Depends on / 依赖: mul_inv_cancel_left
-/
instance Regular.isPretransitive_mulOpposite [Group G] : IsPretransitive Gᵐᵒᵖ G :=
  ⟨fun x y => ⟨.op (x⁻¹ * y), mul_inv_cancel_left _ _⟩⟩

/-- If `G` is a group acting multiplicatively on a set, then the action is transitive if there is
a single element whose orbit is everything. -/
@[to_additive /-- If `G` is a group acting additively on a set, then the action is transitive if
there is a single element whose orbit is everything. -/]
/--
lemma `IsPretransitive.of_orbit` / 引理 `IsPretransitive.of_orbit`

English:
lemma IsPretransitive.of_orbit
  statement: {X : Type*} [Group G] [MulAction G X] {x₀ : X}
  proof: by
  constructor
  intro x y
  rcases ha x with ⟨g, rfl⟩
  rcases ha y with ⟨h, rfl⟩
  exact ⟨h * g⁻¹, by simp [mul_smul]⟩

中文:
引理 是Pretransitive.of_orbit
  结论: {X : 类型} [群 G] [乘法作用 G X] {x₀ : X}
  证明: by
  constructor
  intro x y
  rcases ha x with ⟨g, rfl⟩
  rcases ha y with ⟨h, rfl⟩
  exact ⟨h * g⁻¹, by simp [mul_smul]⟩

Depends on / 依赖: mul_smul
-/
lemma IsPretransitive.of_orbit {X : Type*} [Group G] [MulAction G X] {x₀ : X}
    (ha : forall x, exists g : G, g • x₀ = x) :
    IsPretransitive G X := by
  constructor
  intro x y
  rcases ha x with ⟨g, rfl⟩
  rcases ha y with ⟨h, rfl⟩
  exact ⟨h * g⁻¹, by simp [mul_smul]⟩

end MulAction

namespace MulAction

@[to_additive]
/--
lemma `IsPretransitive.of_smul_eq` / 引理 `IsPretransitive.of_smul_eq`

English:
lemma IsPretransitive.of_smul_eq
  statement: {M N α : Type*} [SMul M α] [SMul N α] [IsPretransitive M α]
  proof: (exists_smul_eq x y).elim fun m h => ⟨f m, hf.trans h⟩

中文:
引理 是Pretransitive.of_smul_eq
  结论: {M N α : 类型} [标量乘法 M α] [标量乘法 N α] [是Pretransitive M α]
  证明: (exists_smul_eq x y).elim fun m h => ⟨f m, hf.trans h⟩

Depends on / 依赖: exists_smul_eq, hf.trans
-/
lemma IsPretransitive.of_smul_eq {M N α : Type*} [SMul M α] [SMul N α] [IsPretransitive M α]
    (f : M -> N) (hf : forall {c : M} {x : α}, f c • x = c • x) : IsPretransitive N α where
  exists_smul_eq x y := (exists_smul_eq x y).elim fun m h => ⟨f m, hf.trans h⟩

end MulAction

section CompatibleScalar

@[to_additive]
/--
lemma `MulAction.IsPretransitive.of_isScalarTower` / 引理 `MulAction.IsPretransitive.of_isScalarTower`

English:
lemma MulAction.IsPretransitive.of_isScalarTower
  statement: (M : Type*) {N α : Type*} [Monoid N] [SMul M N]
  proof: of_smul_eq (fun x : M => x • 1) (smul_one_smul N _ _)

中文:
引理 乘法作用.是Pretransitive.of_isScalarTower
  结论: (M : 类型) {N α : 类型} [幺半群 N] [标量乘法 M N]
  证明: of_smul_eq (fun x : M => x • 1) (smul_one_smul N _ _)

Depends on / 依赖: of_smul_eq, smul_one_smul
-/
lemma MulAction.IsPretransitive.of_isScalarTower (M : Type*) {N α : Type*} [Monoid N] [SMul M N]
    [MulAction N α] [SMul M α] [IsScalarTower M N α] [IsPretransitive M α] : IsPretransitive N α :=
  of_smul_eq (fun x : M => x • 1) (smul_one_smul N _ _)

end CompatibleScalar

/-! ### `Additive`, `Multiplicative` -/

section

open Additive Multiplicative

/--
Instance `Additive.addAction_isPretransitive` / 实例 `Additive.addAction_isPretransitive`

English:
instance Additive.addAction_isPretransitive
  signature: [Monoid α] [MulAction α β]
  body: ⟨@MulAction.exists_smul_eq α _ _ _⟩

中文:
实例 加性.addAction_isPretransitive
  签名: [幺半群 α] [乘法作用 α β]
  定义体: ⟨@MulAction.exists_smul_eq α _ _ _⟩

Depends on / 依赖: MulAction, MulAction.exists_smul_eq, exists_smul_eq
-/
instance Additive.addAction_isPretransitive [Monoid α] [MulAction α β]
    [MulAction.IsPretransitive α β] : AddAction.IsPretransitive (Additive α) β :=
  ⟨@MulAction.exists_smul_eq α _ _ _⟩

/--
Instance `Multiplicative.mulAction_isPretransitive` / 实例 `Multiplicative.mulAction_isPretransitive`

English:
instance Multiplicative.mulAction_isPretransitive
  signature: [AddMonoid α] [AddAction α β]
  body: ⟨@AddAction.exists_vadd_eq α _ _ _⟩

中文:
实例 Multiplicative.mulAction_isPretransitive
  签名: [加法幺半群 α] [加法作用 α β]
  定义体: ⟨@AddAction.exists_vadd_eq α _ _ _⟩

Depends on / 依赖: AddAction, AddAction.exists_vadd_eq, exists_vadd_eq
-/
instance Multiplicative.mulAction_isPretransitive [AddMonoid α] [AddAction α β]
    [AddAction.IsPretransitive α β] : MulAction.IsPretransitive (Multiplicative α) β :=
  ⟨@AddAction.exists_vadd_eq α _ _ _⟩

end
