/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Defs

/-!
# Faithful group actions

This file provides typeclasses for faithful actions.

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

variable {M G α : Type*}

/-! ### Faithful actions -/

/--
Definition of `FaithfulVAdd` / `FaithfulVAdd` 的定义

English:
class FaithfulVAdd
  parameters: (G : Type*) (P : Type*) [VAdd G P]
  axioms and operations (1):
    - eq_of_vadd_eq_vadd : forall {g₁ g₂ : G}, (forall p : P, g₁ +ᵥ p = g₂ +ᵥ p) -> g₁ = g₂

中文:
类 忠实向量加法
  参数: (G : 类型) (P : 类型) [向量加法 G P]
  公理与运算 (1 个):
    - eq_of_vadd_eq_vadd : 对任意 {g₁ g₂ : G}, (对任意 p : P, g₁ +ᵥ p = g₂ +ᵥ p) -> g₁ = g₂
-/
class FaithfulVAdd (G : Type*) (P : Type*) [VAdd G P] : Prop where
  /-- Two elements `g₁` and `g₂` are equal whenever they act in the same way on all points. -/
  eq_of_vadd_eq_vadd : forall {g₁ g₂ : G}, (forall p : P, g₁ +ᵥ p = g₂ +ᵥ p) -> g₁ = g₂

/-- Typeclass for faithful actions. -/
@[to_additive]
/--
Definition of `FaithfulSMul` / `FaithfulSMul` 的定义

English:
class FaithfulSMul
  parameters: (M : Type*) (α : Type*) [SMul M α]
  axioms and operations (1):
    - eq_of_smul_eq_smul : forall {m₁ m₂ : M}, (forall a : α, m₁ • a = m₂ • a) -> m₁ = m₂

中文:
类 忠实标量乘法
  参数: (M : 类型) (α : 类型) [标量乘法 M α]
  公理与运算 (1 个):
    - eq_of_smul_eq_smul : 对任意 {m₁ m₂ : M}, (对任意 a : α, m₁ • a = m₂ • a) -> m₁ = m₂
-/
class FaithfulSMul (M : Type*) (α : Type*) [SMul M α] : Prop where
  /-- Two elements `m₁` and `m₂` are equal whenever they act in the same way on all points. -/
  eq_of_smul_eq_smul : forall {m₁ m₂ : M}, (forall a : α, m₁ • a = m₂ • a) -> m₁ = m₂

export FaithfulSMul (eq_of_smul_eq_smul)
export FaithfulVAdd (eq_of_vadd_eq_vadd)

@[to_additive] instance (priority := low) [SMul M α] [Subsingleton M] : FaithfulSMul M α :=
  ⟨fun _ => Subsingleton.elim ..⟩

@[to_additive]
/--
lemma `smul_left_injective'` / 引理 `smul_left_injective'`

English:
lemma smul_left_injective'
  given: [SMul M α] [FaithfulSMul M α]
  statement: Injective ((· • ·) : M -> α -> α)
  proof: fun _ _ h => FaithfulSMul.eq_of_smul_eq_smul (congr_fun h)

中文:
引理 smul_left_injective'
  条件: [标量乘法 M α] [忠实标量乘法 M α]
  结论: 单射 ((· • ·) : M -> α -> α)
  证明: fun _ _ h => FaithfulSMul.eq_of_smul_eq_smul (congr_fun h)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.eq_of_smul_eq_smul, congr_fun, eq_of_smul_eq_smul
-/
lemma smul_left_injective' [SMul M α] [FaithfulSMul M α] : Injective ((· • ·) : M -> α -> α) :=
  fun _ _ h => FaithfulSMul.eq_of_smul_eq_smul (congr_fun h)

/-- `instSMulOfMul` is faithful when there is a (right) identity. -/
@[to_additive /-- `instVAddOfAdd` is faithful when there is a (right) identity. -/]
instance (R : Type*) [MulOneClass R] : FaithfulSMul R R where
  eq_of_smul_eq_smul {r₁ r₂} h := by simpa using h 1

/-- `Mul.toSMulMulOpposite` is faithful when there is a (left) identity. -/
@[to_additive /-- `Add.toVAddAddOpposite` is faithful when there is a (left) identity. -/]
instance (R : Type*) [MulOneClass R] : FaithfulSMul Rᵐᵒᵖ R where
  eq_of_smul_eq_smul {r₁ r₂} h := by simpa using h 1

/-- `instSMulOfMul` is faithful when multiplication is right cancellative. -/
@[to_additive /-- `instVAddOfAdd` is faithful when addition is right cancellative. -/]
instance (R : Type*) [Mul R] [IsRightCancelMul R] : FaithfulSMul R R where
  eq_of_smul_eq_smul {r₁ r₂} h := by simpa using h r₁

/-- `Mul.toSMulMulOpposite` is faithful when multiplication is left cancellative -/
@[to_additive /-- `Add.toVAddAddOpposite` is faithful when addition is left cancellative -/]
instance (R : Type*) [Mul R] [IsLeftCancelMul R] : FaithfulSMul Rᵐᵒᵖ R where
  eq_of_smul_eq_smul {r₁ r₂} h := by simpa using h r₁.unop

/-- `Monoid.toMulAction` is faithful on cancellative monoids. -/
@[to_additive (attr :=
  deprecated "subsumed by `instFaithfulSMul` or `instFaithfulSMulOfIsRightCancelMul`"
  (since := "2026-02-03"))
  /-- `AddMonoid.toAddAction` is faithful on additive cancellative monoids. -/]
/--
lemma `RightCancelMonoid.faithfulSMul` / 引理 `RightCancelMonoid.faithfulSMul`

English:
lemma RightCancelMonoid.faithfulSMul
  given: [RightCancelMonoid α]
  statement: FaithfulSMul α α
  proof: inferInstance

中文:
引理 右消去幺半群.faithfulSMul
  条件: [右消去幺半群 α]
  结论: 忠实标量乘法 α α
  证明: inferInstance
-/
lemma RightCancelMonoid.faithfulSMul [RightCancelMonoid α] : FaithfulSMul α α :=
  inferInstance

/-- `Monoid.toOppositeMulAction` is faithful on cancellative monoids. -/
@[to_additive (attr :=
    deprecated "subsumed by `instFaithfulSMulMulOpposite` or \
    `instFaithfulSMulMulOppositeOfIsLeftCancelMul`"
    (since := "2026-02-03"))
  /-- `AddMonoid.toOppositeAddAction` is faithful on additive cancellative monoids. -/]
/--
lemma `LeftCancelMonoid.to_faithfulSMul_mulOpposite` / 引理 `LeftCancelMonoid.to_faithfulSMul_mulOpposite`

English:
lemma LeftCancelMonoid.to_faithfulSMul_mulOpposite
  given: [LeftCancelMonoid α]
  statement: FaithfulSMul αᵐᵒᵖ α
  proof: inferInstance

@[to_additive]

中文:
引理 左消去幺半群.to_faithfulSMul_mulOpposite
  条件: [左消去幺半群 α]
  结论: 忠实标量乘法 αᵐᵒᵖ α
  证明: inferInstance

@[to_additive]
-/
lemma LeftCancelMonoid.to_faithfulSMul_mulOpposite [LeftCancelMonoid α] : FaithfulSMul αᵐᵒᵖ α :=
  inferInstance

@[to_additive]
/--
lemma `faithfulSMul_iff_injective_smul_one` / 引理 `faithfulSMul_iff_injective_smul_one`

English:
lemma faithfulSMul_iff_injective_smul_one
  statement: (R A : Type*)
  proof: by
  refine ⟨fun ⟨h⟩ {r₁ r₂} hr => h fun a => ?_, fun h => ⟨fun {r₁ r₂} hr => h ?_⟩⟩
  · simp only at hr
    rw [← one_mul a]; rw [← smul_mul_assoc]; rw [← smul_mul_assoc]; rw [hr]
  · simpa using hr 1

@[to_additive]

中文:
引理 faithfulSMul_iff_injective_smul_one
  结论: (R A : 类型)
  证明: by
  refine ⟨fun ⟨h⟩ {r₁ r₂} hr => h fun a => ?_, fun h => ⟨fun {r₁ r₂} hr => h ?_⟩⟩
  · simp only at hr
    rw [← one_mul a]; rw [← smul_mul_assoc]; rw [← smul_mul_assoc]; rw [hr]
  · simpa using hr 1

@[to_additive]

Depends on / 依赖: one_mul, smul_mul_assoc
-/
lemma faithfulSMul_iff_injective_smul_one (R A : Type*)
    [MulOneClass A] [SMul R A] [IsScalarTower R A A] :
    FaithfulSMul R A ↔ Injective (fun r : R => r • (1 : A)) := by
  refine ⟨fun ⟨h⟩ {r₁ r₂} hr => h fun a => ?_, fun h => ⟨fun {r₁ r₂} hr => h ?_⟩⟩
  · simp only at hr
    rw [← one_mul a]; rw [← smul_mul_assoc]; rw [← smul_mul_assoc]; rw [hr]
  · simpa using hr 1

@[to_additive]
/--
theorem `faithfulSMul_iff` / 定理 `faithfulSMul_iff`

English:
theorem faithfulSMul_iff
  given: [Group G] [MulAction G α]
  proof: by
  refine ⟨fun h a ha => h.eq_of_smul_eq_smul ?_, fun h => ⟨fun {a₁ a₂} h' => ?_⟩⟩
  · simpa only [one_smul]
  · rw [← inv_inv a₂, eq_inv_of_mul_eq_one_left (h (a₂⁻¹ * a₁) ?_), inv_inv]
    simpa only [mul_smul, inv_smul_eq_iff] using h'

@[to_additive]

中文:
定理 faithfulSMul_iff
  条件: [群 G] [乘法作用 G α]
  证明: by
  refine ⟨fun h a ha => h.eq_of_smul_eq_smul ?_, fun h => ⟨fun {a₁ a₂} h' => ?_⟩⟩
  · simpa only [one_smul]
  · rw [← inv_inv a₂, eq_inv_of_mul_eq_one_left (h (a₂⁻¹ * a₁) ?_), inv_inv]
    simpa only [mul_smul, inv_smul_eq_iff] using h'

@[to_additive]

Depends on / 依赖: eq_inv_of_mul_eq_one_left, eq_of_smul_eq_smul, h.eq_of_smul_eq_smul, inv_inv, inv_smul_eq_iff, mul_smul, one_smul
-/
theorem faithfulSMul_iff [Group G] [MulAction G α] :
    FaithfulSMul G α ↔ (forall g : G, (forall a : α, g • a = a) -> g = 1) := by
  refine ⟨fun h a ha => h.eq_of_smul_eq_smul ?_, fun h => ⟨fun {a₁ a₂} h' => ?_⟩⟩
  · simpa only [one_smul]
  · rw [← inv_inv a₂, eq_inv_of_mul_eq_one_left (h (a₂⁻¹ * a₁) ?_), inv_inv]
    simpa only [mul_smul, inv_smul_eq_iff] using h'

@[to_additive]
/--
lemma `FaithfulSMul.tower_bot` / 引理 `FaithfulSMul.tower_bot`

English:
lemma FaithfulSMul.tower_bot
  statement: (R S T : Type*) [Monoid S] [MulOneClass T]
  proof: by
  rw [faithfulSMul_iff_injective_smul_one]
  refine .of_comp (f := (· • (1 : T))) ?_
  simpa [Function.comp_def, one_smul, ← faithfulSMul_iff_injective_smul_one]

@[to_additive]

中文:
引理 忠实标量乘法.tower_bot
  结论: (R S T : 类型) [幺半群 S] [MulOne类 T]
  证明: by
  rw [faithfulSMul_iff_injective_smul_one]
  refine .of_comp (f := (· • (1 : T))) ?_
  simpa [Function.comp_def, one_smul, ← faithfulSMul_iff_injective_smul_one]

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, comp_def, faithfulSMul_iff_injective_smul_one, of_comp, one_smul
-/
lemma FaithfulSMul.tower_bot (R S T : Type*) [Monoid S] [MulOneClass T]
    [SMul R S] [SMul R T] [MulAction S T]
    [IsScalarTower R S S] [IsScalarTower R T T]
    [IsScalarTower R S T] [FaithfulSMul R T] : FaithfulSMul R S := by
  rw [faithfulSMul_iff_injective_smul_one]
  refine .of_comp (f := (· • (1 : T))) ?_
  simpa [Function.comp_def, one_smul, ← faithfulSMul_iff_injective_smul_one]

@[to_additive]
/--
lemma `FaithfulSMul.trans` / 引理 `FaithfulSMul.trans`

English:
lemma FaithfulSMul.trans
  statement: (R S T : Type*) [Monoid S] [MulOneClass T]
  proof: by
  simpa [faithfulSMul_iff_injective_smul_one, Function.comp_def] using
    ((faithfulSMul_iff_injective_smul_one S T).mp ‹_›).comp
      ((faithfulSMul_iff_injective_smul_one R S).mp ‹_›)

中文:
引理 忠实标量乘法.trans
  结论: (R S T : 类型) [幺半群 S] [MulOne类 T]
  证明: by
  simpa [faithfulSMul_iff_injective_smul_one, Function.comp_def] using
    ((faithfulSMul_iff_injective_smul_one S T).mp ‹_›).comp
      ((faithfulSMul_iff_injective_smul_one R S).mp ‹_›)

Depends on / 依赖: Function, Function.comp_def, comp_def, faithfulSMul_iff_injective_smul_one
-/
lemma FaithfulSMul.trans (R S T : Type*) [Monoid S] [MulOneClass T]
    [SMul R S] [IsScalarTower R S S] [MulAction S T] [IsScalarTower S T T]
    [SMul R T] [IsScalarTower R T T] [IsScalarTower R S T] [FaithfulSMul R S]
    [FaithfulSMul S T] : FaithfulSMul R T := by
  simpa [faithfulSMul_iff_injective_smul_one, Function.comp_def] using
    ((faithfulSMul_iff_injective_smul_one S T).mp ‹_›).comp
      ((faithfulSMul_iff_injective_smul_one R S).mp ‹_›)

/--
lemma `IsScalarTower.to₁₂₃` / 引理 `IsScalarTower.to₁₂₃`

English:
lemma IsScalarTower.to₁₂₃
  statement: (M N P Q)
  proof: by simp_rw [← (smul_left_injective' (α := Q)).eq_iff, smul_assoc]

中文:
引理 标量塔.to₁₂₃
  结论: (M N P Q)
  证明: by simp_rw [← (smul_left_injective' (α := Q)).eq_iff, smul_assoc]
-/
@[to_additive] lemma IsScalarTower.to₁₂₃ (M N P Q)
    [SMul M N] [SMul M P] [SMul M Q] [SMul N P] [SMul N Q] [SMul P Q] [FaithfulSMul P Q]
    [IsScalarTower M N Q] [IsScalarTower M P Q] [IsScalarTower N P Q] : IsScalarTower M N P where
  smul_assoc m n p := by simp_rw [← (smul_left_injective' (α := Q)).eq_iff, smul_assoc]

open MulOpposite in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: α M] [FaithfulSMul α M] : FaithfulSMul α Mᵐᵒᵖ where
  body: FaithfulSMul.eq_of_smul_eq_smul fun m => op_inj.mp h (op m)

中文:
实例 [标量乘法
  签名: α M] [忠实标量乘法 α M] : 忠实标量乘法 α Mᵐᵒᵖ where
  定义体: FaithfulSMul.eq_of_smul_eq_smul fun m => op_inj.mp h (op m)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.eq_of_smul_eq_smul, eq_of_smul_eq_smul, op_inj, op_inj.mp
-/
instance [SMul α M] [FaithfulSMul α M] : FaithfulSMul α Mᵐᵒᵖ where
eq_of_smul_eq_smul h := FaithfulSMul.eq_of_smul_eq_smul fun m => op_inj.mp h (op m)
