/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Opposite
public import Mathlib.Algebra.Notation.Pi.Basic

/-!
# Definitions of group actions

This file defines a hierarchy of group action type-classes on top of the previously defined
notation classes `SMul` and its additive version `VAdd`:

* `SMulZeroClass` is a typeclass for an action that preserves zero
* `DistribSMul M A` is a typeclass for an action on an additive monoid (`AddZeroClass`) that
  preserves addition and zero
* `DistribMulAction M A` is a typeclass for an action of a multiplicative monoid on
  an additive monoid such that `a • (b + c) = a • b + a • c` and `a • 0 = 0`.

The hierarchy is extended further by `Module`, defined elsewhere.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

@[expose] public section

assert_not_exists Equiv.Perm.equivUnitsEnd Prod.fst_mul Ring

open Function

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

/--
Definition of `SMulZeroClass` / `SMulZeroClass` 的定义

English:
class SMulZeroClass
  parameters: (M A : Type*) [Zero A]
  extends: SMul M A
  axioms and operations (1):
    - smul_zero : forall a : M, a • (0 : A) = 0

中文:
类 SMulZero类
  参数: (M A : 类型) [零 A]
  继承: 标量乘法 M A
  公理与运算 (1 个):
    - smul_zero : 对任意 a : M, a • (0 : A) = 0

Depends on / 依赖: F.map_injective, HomologicalComplex, HomologicalComplex.eval, congr_map, map_injective
-/
class SMulZeroClass (M A : Type*) [Zero A] extends SMul M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : forall a : M, a • (0 : A) = 0

section smul_zero

variable [Zero A] [SMulZeroClass M A]

@[simp]
/--
theorem `smul_zero` / 定理 `smul_zero`

English:
theorem smul_zero
  given: (a : M)
  statement: a • (0 : A) = 0
  proof: SMulZeroClass.smul_zero _

中文:
定理 smul_zero
  条件: (a : M)
  结论: a • (0 : A) = 0
  证明: SMulZeroClass.smul_zero _

Depends on / 依赖: SMulZeroClass, SMulZeroClass.smul_zero, smul_zero
-/
theorem smul_zero (a : M) : a • (0 : A) = 0 :=
  SMulZeroClass.smul_zero _

/--
lemma `smul_ite_zero` / 引理 `smul_ite_zero`

English:
lemma smul_ite_zero
  given: (p : Prop) [Decidable p] (a : M) (b : A)
  proof: by split_ifs <;> simp

中文:
引理 smul_ite_zero
  条件: (p : 命题) [可判定 p] (a : M) (b : A)
  证明: by split_ifs <;> simp

Depends on / 依赖: split_ifs
-/
lemma smul_ite_zero (p : Prop) [Decidable p] (a : M) (b : A) :
    (a • if p then b else 0) = if p then a • b else 0 := by split_ifs <;> simp

/--
lemma `smul_eq_zero_of_right` / 引理 `smul_eq_zero_of_right`

English:
lemma smul_eq_zero_of_right
  given: (a : M) {b : A} (h : b = 0)
  statement: a • b = 0
  proof: h.symm ▸ smul_zero a

中文:
引理 smul_eq_zero_of_right
  条件: (a : M) {b : A} (h : b = 0)
  结论: a • b = 0
  证明: h.symm ▸ smul_zero a

Depends on / 依赖: h.symm, smul_zero
-/
lemma smul_eq_zero_of_right (a : M) {b : A} (h : b = 0) : a • b = 0 := h.symm ▸ smul_zero a
/--
lemma `right_ne_zero_of_smul` / 引理 `right_ne_zero_of_smul`

English:
lemma right_ne_zero_of_smul
  given: {a : M} {b : A}
  statement: a • b != 0 -> b != 0
  proof: mt smul_eq_zero_of_right a

中文:
引理 right_ne_zero_of_smul
  条件: {a : M} {b : A}
  结论: a • b != 0 -> b != 0
  证明: mt smul_eq_zero_of_right a

Depends on / 依赖: smul_eq_zero_of_right
-/
lemma right_ne_zero_of_smul {a : M} {b : A} : a • b != 0 -> b != 0 := mt smul_eq_zero_of_right a

/--
Definition of `Function.Injective.smulZeroClass` / `Function.Injective.smulZeroClass` 的定义

English:
abbreviation Function.Injective.smulZeroClass
  signature: [Zero B] [SMul M B] (f : ZeroHom B A)
  body: hf by simp only [smul, map_zero, smul_zero]

中文:
缩写 函数.单射.smulZeroClass
  签名: [零 B] [标量乘法 M B] (f : 保零态射 B A)
  定义体: hf by simp only [smul, map_zero, smul_zero]
-/
protected abbrev Function.Injective.smulZeroClass [Zero B] [SMul M B] (f : ZeroHom B A)
    (hf : Injective f) (smul : forall (c : M) (x), f (c • x) = c • f x) :
    SMulZeroClass M B where
smul_zero c := hf by simp only [smul, map_zero, smul_zero]

/--
Definition of `ZeroHom.smulZeroClass` / `ZeroHom.smulZeroClass` 的定义

English:
abbreviation ZeroHom.smulZeroClass
  signature: [Zero B] [SMul M B] (f : ZeroHom A B)
  body: by rw [← map_zero f, ← smul, smul_zero]

中文:
缩写 保零态射.smulZeroClass
  签名: [零 B] [标量乘法 M B] (f : 保零态射 A B)
  定义体: by rw [← map_zero f, ← smul, smul_zero]
-/
protected abbrev ZeroHom.smulZeroClass [Zero B] [SMul M B] (f : ZeroHom A B)
    (smul : forall (c : M) (x), f (c • x) = c • f x) :
    SMulZeroClass M B where
  smul_zero c := by rw [← map_zero f, ← smul, smul_zero]

/--
Definition of `Function.Surjective.smulZeroClassLeft` / `Function.Surjective.smulZeroClassLeft` 的定义

English:
abbreviation Function.Surjective.smulZeroClassLeft
  signature: {R S M : Type*} [Zero M] [SMulZeroClass R M]
  body: hf.forall.mpr fun c => by rw [hsmul, smul_zero]

中文:
缩写 函数.满射.smulZeroClassLeft
  签名: {R S M : 类型} [零 M] [SMulZero类 R M]
  定义体: hf.forall.mpr fun c => by rw [hsmul, smul_zero]

Depends on / 依赖: hf.forall.mpr, smul_zero
-/
abbrev Function.Surjective.smulZeroClassLeft {R S M : Type*} [Zero M] [SMulZeroClass R M]
    [SMul S M] (f : R -> S) (hf : Function.Surjective f)
    (hsmul : forall (c) (x : M), f c • x = c • x) :
    SMulZeroClass S M where
  smul_zero := hf.forall.mpr fun c => by rw [hsmul, smul_zero]

variable (A)

/--
Definition of `SMulZeroClass.compFun` / `SMulZeroClass.compFun` 的定义

English:
abbreviation SMulZeroClass.compFun
  signature: (f : N -> M)
  body: SMul.comp.smul f
  smul_zero x := smul_zero (f x)

中文:
缩写 SMulZero类.compFun
  签名: (f : N -> M)
  定义体: SMul.comp.smul f
  smul_zero x := smul_zero (f x)

Depends on / 依赖: SMul.comp.smul
-/
abbrev SMulZeroClass.compFun (f : N -> M) :
    SMulZeroClass N A where
  smul := SMul.comp.smul f
  smul_zero x := smul_zero (f x)

/-- Each element of the scalars defines a zero-preserving map. -/
@[simps]
/--
Definition of `SMulZeroClass.toZeroHom` / `SMulZeroClass.toZeroHom` 的定义

English:
definition SMulZeroClass.toZeroHom
  signature: (x : M)
  body: (x • ·)
  map_zero' := smul_zero x

中文:
定义 SMulZero类.toZeroHom
  签名: (x : M)
  定义体: (x • ·)
  map_zero' := smul_zero x
-/
def SMulZeroClass.toZeroHom (x : M) :
    ZeroHom A A where
  toFun := (x • ·)
  map_zero' := smul_zero x

end smul_zero

section Zero
variable (M₀ A)

/--
Definition of `SMulWithZero` / `SMulWithZero` 的定义

English:
class SMulWithZero
  parameters: [Zero M₀] [Zero A]
  extends: SMulZeroClass M₀ A
  axioms and operations (1):
    - zero_smul : forall m : A, (0 : M₀) • m = 0

中文:
类 带零标量乘法
  参数: [零 M₀] [零 A]
  继承: SMulZero类 M₀ A
  公理与运算 (1 个):
    - zero_smul : 对任意 m : A, (0 : M₀) • m = 0

Depends on / 依赖: single
-/
class SMulWithZero [Zero M₀] [Zero A] extends SMulZeroClass M₀ A where
  /-- Scalar multiplication by the scalar `0` is `0`. -/
  zero_smul : forall m : A, (0 : M₀) • m = 0

-- see Note [higher instance priority]
instance (priority := 1100) MulZeroClass.toSMulWithZero [MulZeroClass M₀] : SMulWithZero M₀ M₀ where
  smul := (· * ·)
  smul_zero := mul_zero
  zero_smul := zero_mul

/--
Instance `MulZeroClass.toOppositeSMulWithZero` / 实例 `MulZeroClass.toOppositeSMulWithZero`

English:
instance MulZeroClass.toOppositeSMulWithZero
  signature: [MulZeroClass M₀]
  body: zero_mul _
  zero_smul := mul_zero

中文:
实例 乘零类.toOppositeSMulWithZero
  签名: [乘零类 M₀]
  定义体: zero_mul _
  zero_smul := mul_zero

Depends on / 依赖: zero_mul
-/
instance MulZeroClass.toOppositeSMulWithZero [MulZeroClass M₀] : SMulWithZero M₀ᵐᵒᵖ M₀ where
  smul_zero _ := zero_mul _
  zero_smul := mul_zero

variable {A} [Zero M₀] [Zero A] [SMulWithZero M₀ A]

@[simp]
/--
theorem `zero_smul` / 定理 `zero_smul`

English:
theorem zero_smul
  given: (m : A)
  statement: (0 : M₀) • m = 0
  proof: SMulWithZero.zero_smul m

中文:
定理 zero_smul
  条件: (m : A)
  结论: (0 : M₀) • m = 0
  证明: SMulWithZero.zero_smul m

Depends on / 依赖: SMulWithZero, SMulWithZero.zero_smul, zero_smul
-/
theorem zero_smul (m : A) : (0 : M₀) • m = 0 :=
  SMulWithZero.zero_smul m

variable {M₀} {a : M₀} {b : A}

/--
lemma `smul_eq_zero_of_left` / 引理 `smul_eq_zero_of_left`

English:
lemma smul_eq_zero_of_left
  given: (h : a = 0) (b : A)
  statement: a • b = 0
  proof: h.symm ▸ zero_smul _ b

中文:
引理 smul_eq_zero_of_left
  条件: (h : a = 0) (b : A)
  结论: a • b = 0
  证明: h.symm ▸ zero_smul _ b

Depends on / 依赖: h.symm, zero_smul
-/
lemma smul_eq_zero_of_left (h : a = 0) (b : A) : a • b = 0 := h.symm ▸ zero_smul _ b
/--
lemma `left_ne_zero_of_smul` / 引理 `left_ne_zero_of_smul`

English:
lemma left_ne_zero_of_smul
  statement: a • b != 0 -> a != 0
  proof: mt fun h => smul_eq_zero_of_left h b

中文:
引理 left_ne_zero_of_smul
  结论: a • b != 0 -> a != 0
  证明: mt fun h => smul_eq_zero_of_left h b

Depends on / 依赖: smul_eq_zero_of_left
-/
lemma left_ne_zero_of_smul : a • b != 0 -> a != 0 := mt fun h => smul_eq_zero_of_left h b

variable [Zero M₀'] [Zero A'] [SMul M₀ A']

-- See note [reducible non-instances]
/--
Definition of `Function.Injective.smulWithZero` / `Function.Injective.smulWithZero` 的定义

English:
abbreviation Function.Injective.smulWithZero
  signature: (f : ZeroHom A' A) (hf : Injective f)
  body: hf by simp [smul]
smul_zero a := hf by simp [smul]

中文:
缩写 函数.单射.smulWithZero
  签名: (f : 保零态射 A' A) (hf : 单射 f)
  定义体: hf by simp [smul]
smul_zero a := hf by simp [smul]
-/
protected abbrev Function.Injective.smulWithZero (f : ZeroHom A' A) (hf : Injective f)
    (smul : forall (a : M₀) (b), f (a • b) = a • f b) : SMulWithZero M₀ A' where
zero_smul a := hf by simp [smul]
smul_zero a := hf by simp [smul]

-- See note [reducible non-instances]
/--
Definition of `Function.Surjective.smulWithZero` / `Function.Surjective.smulWithZero` 的定义

English:
abbreviation Function.Surjective.smulWithZero
  signature: (f : ZeroHom A A') (hf : Surjective f)
  body: by
    rcases hf m with ⟨x, rfl⟩
    simp [← smul]
  smul_zero c := by rw [← f.map_zero, ← smul, smul_zero]

中文:
缩写 函数.满射.smulWithZero
  签名: (f : 保零态射 A A') (hf : 满射 f)
  定义体: by
    rcases hf m with ⟨x, rfl⟩
    simp [← smul]
  smul_zero c := by rw [← f.map_zero, ← smul, smul_zero]
-/
protected abbrev Function.Surjective.smulWithZero (f : ZeroHom A A') (hf : Surjective f)
    (smul : forall (a : M₀) (b), f (a • b) = a • f b) : SMulWithZero M₀ A' where
  zero_smul m := by
    rcases hf m with ⟨x, rfl⟩
    simp [← smul]
  smul_zero c := by rw [← f.map_zero, ← smul, smul_zero]

variable (A)

/-- Compose a `SMulWithZero` with a `ZeroHom`, with action `f r' • m` -/
@[instance_reducible]
/--
Definition of `SMulWithZero.compHom` / `SMulWithZero.compHom` 的定义

English:
definition SMulWithZero.compHom
  signature: (f : ZeroHom M₀' M₀)
  body: (f · • ·)
  smul_zero m := smul_zero (f m)
  zero_smul m := by change (f 0) • m = 0; rw [map_zero, zero_smul]

中文:
定义 带零标量乘法.compHom
  签名: (f : 保零态射 M₀' M₀)
  定义体: (f · • ·)
  smul_zero m := smul_zero (f m)
  zero_smul m := by change (f 0) • m = 0; rw [map_zero, zero_smul]
-/
def SMulWithZero.compHom (f : ZeroHom M₀' M₀) : SMulWithZero M₀' A where
  smul := (f · • ·)
  smul_zero m := smul_zero (f m)
  zero_smul m := by change (f 0) • m = 0; rw [map_zero, zero_smul]

end Zero

/--
Instance `AddMonoid.natSMulWithZero` / 实例 `AddMonoid.natSMulWithZero`

English:
instance AddMonoid.natSMulWithZero
  signature: [AddMonoid A]
  body: _root_.nsmul_zero
  zero_smul := zero_nsmul

中文:
实例 加法幺半群.natSMulWithZero
  签名: [加法幺半群 A]
  定义体: _root_.nsmul_zero
  zero_smul := zero_nsmul

Depends on / 依赖: _root_, _root_.nsmul_zero, nsmul_zero
-/
instance AddMonoid.natSMulWithZero [AddMonoid A] : SMulWithZero Nat A where
  smul_zero := _root_.nsmul_zero
  zero_smul := zero_nsmul

/--
Instance `AddGroup.intSMulWithZero` / 实例 `AddGroup.intSMulWithZero`

English:
instance AddGroup.intSMulWithZero
  signature: [AddGroup A]
  body: zsmul_zero
  zero_smul := zero_zsmul

中文:
实例 加法群.intSMulWithZero
  签名: [加法群 A]
  定义体: zsmul_zero
  zero_smul := zero_zsmul

Depends on / 依赖: zsmul_zero
-/
instance AddGroup.intSMulWithZero [AddGroup A] : SMulWithZero Int A where
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul

section MonoidWithZero
variable (M₀ A) [MonoidWithZero M₀] [MonoidWithZero M₀'] [Zero A]

/--
Definition of `MulActionWithZero` / `MulActionWithZero` 的定义

English:
class MulActionWithZero
  parameters: extends MulAction M₀ A
  extends: MulAction M₀ A
  axioms and operations (2):
    - smul_zero : forall r : M₀, r • (0 : A) = 0
    - zero_smul : forall m : A, (0 : M₀) • m = 0

中文:
类 带零乘法作用
  参数: extends 乘法作用 M₀ A
  继承: 乘法作用 M₀ A
  公理与运算 (2 个):
    - smul_zero : 对任意 r : M₀, r • (0 : A) = 0
    - zero_smul : 对任意 m : A, (0 : M₀) • m = 0
-/
class MulActionWithZero extends MulAction M₀ A where
  -- these fields are copied from `SMulWithZero`, as `extends` behaves poorly
  /-- Scalar multiplication by any element send `0` to `0`. -/
  smul_zero : forall r : M₀, r • (0 : A) = 0
  /-- Scalar multiplication by the scalar `0` is `0`. -/
  zero_smul : forall m : A, (0 : M₀) • m = 0

-- see Note [lower instance priority]
instance (priority := 100) MulActionWithZero.toSMulWithZero (M₀ A) {_ : MonoidWithZero M₀}
    {_ : Zero A} [m : MulActionWithZero M₀ A] : SMulWithZero M₀ A :=
  { m with }

-- see Note [higher instance priority]
/-- See also `Semiring.toModule` -/
instance (priority := 1100) MonoidWithZero.toMulActionWithZero : MulActionWithZero M₀ M₀ :=
  { MulZeroClass.toSMulWithZero M₀, Monoid.toMulAction M₀ with }

/--
Instance `MonoidWithZero.toOppositeMulActionWithZero` / 实例 `MonoidWithZero.toOppositeMulActionWithZero`

English:
instance MonoidWithZero.toOppositeMulActionWithZero
  signature: : MulActionWithZero M₀ᵐᵒᵖ M₀
  body: { MulZeroClass.toOppositeSMulWithZero M₀, Monoid.toOppositeMulAction with }

中文:
实例 带零幺半群.toOppositeMulActionWithZero
  签名: : 带零乘法作用 M₀ᵐᵒᵖ M₀
  定义体: { MulZeroClass.toOppositeSMulWithZero M₀, Monoid.toOppositeMulAction with }

Depends on / 依赖: Monoid, Monoid.toOppositeMulAction, MulZeroClass, MulZeroClass.toOppositeSMulWithZero, toOppositeMulAction, toOppositeSMulWithZero
-/
instance MonoidWithZero.toOppositeMulActionWithZero : MulActionWithZero M₀ᵐᵒᵖ M₀ :=
  { MulZeroClass.toOppositeSMulWithZero M₀, Monoid.toOppositeMulAction with }

/--
lemma `MulActionWithZero.subsingleton` / 引理 `MulActionWithZero.subsingleton`

English:
lemma MulActionWithZero.subsingleton
  given: [MulActionWithZero M₀ A] [Subsingleton M₀]
  proof: by
    rw [← one_smul M₀ x]; rw [← one_smul M₀ y]; rw [Subsingleton.elim (1 : M₀) 0]; rw [zero_smul]; rw [zero_smul]

中文:
引理 带零乘法作用.subsingleton
  条件: [带零乘法作用 M₀ A] [子单例 M₀]
  证明: by
    rw [← one_smul M₀ x]; rw [← one_smul M₀ y]; rw [Subsingleton.elim (1 : M₀) 0]; rw [zero_smul]; rw [zero_smul]
-/
protected lemma MulActionWithZero.subsingleton [MulActionWithZero M₀ A] [Subsingleton M₀] :
    Subsingleton A where
  allEq x y := by
    rw [← one_smul M₀ x]; rw [← one_smul M₀ y]; rw [Subsingleton.elim (1 : M₀) 0]; rw [zero_smul]; rw [zero_smul]

/--
lemma `MulActionWithZero.nontrivial` / 引理 `MulActionWithZero.nontrivial`

English:
lemma MulActionWithZero.nontrivial
  proof: (subsingleton_or_nontrivial M₀).resolve_left fun _ =>
not_subsingleton A MulActionWithZero.subsingleton M₀ A

中文:
引理 带零乘法作用.nontrivial
  证明: (subsingleton_or_nontrivial M₀).resolve_left fun _ =>
not_subsingleton A MulActionWithZero.subsingleton M₀ A
-/
protected lemma MulActionWithZero.nontrivial
    [MulActionWithZero M₀ A] [Nontrivial A] : Nontrivial M₀ :=
  (subsingleton_or_nontrivial M₀).resolve_left fun _ =>
not_subsingleton A MulActionWithZero.subsingleton M₀ A

variable {M₀ A} [MulActionWithZero M₀ A] [Zero A'] [SMul M₀ A'] (p : Prop) [Decidable p]

/--
lemma `ite_zero_smul` / 引理 `ite_zero_smul`

English:
lemma ite_zero_smul
  given: (a : M₀) (b : A)
  statement: (if p then a else 0 : M₀) • b = if p then a • b else 0
  proof: by
  rw [ite_smul]; rw [zero_smul]

中文:
引理 ite_zero_smul
  条件: (a : M₀) (b : A)
  结论: (if p then a else 0 : M₀) • b = if p then a • b else 0
  证明: by
  rw [ite_smul]; rw [zero_smul]

Depends on / 依赖: ite_smul, zero_smul
-/
lemma ite_zero_smul (a : M₀) (b : A) : (if p then a else 0 : M₀) • b = if p then a • b else 0 := by
  rw [ite_smul]; rw [zero_smul]

/--
lemma `boole_smul` / 引理 `boole_smul`

English:
lemma boole_smul
  given: (a : A)
  statement: (if p then 1 else 0 : M₀) • a = if p then a else 0
  proof: by simp

中文:
引理 boole_smul
  条件: (a : A)
  结论: (if p then 1 else 0 : M₀) • a = if p then a else 0
  证明: by simp
-/
lemma boole_smul (a : A) : (if p then 1 else 0 : M₀) • a = if p then a else 0 := by simp

/--
lemma `Pi.single_apply_smul` / 引理 `Pi.single_apply_smul`

English:
lemma Pi.single_apply_smul
  given: {ι : Type*} [DecidableEq ι] (x : A) (i j : ι)
  proof: by
  rw [single_apply]; rw [ite_smul]; rw [one_smul]; rw [zero_smul]; rw [single_apply]

中文:
引理 依赖函数类型.single_apply_smul
  条件: {ι : 类型} [DecidableEq ι] (x : A) (i j : ι)
  证明: by
  rw [single_apply]; rw [ite_smul]; rw [one_smul]; rw [zero_smul]; rw [single_apply]

Depends on / 依赖: ite_smul, one_smul, single_apply, zero_smul
-/
lemma Pi.single_apply_smul {ι : Type*} [DecidableEq ι] (x : A) (i j : ι) :
    (Pi.single i 1 : ι -> M₀) j • x = (Pi.single i x : ι -> A) j := by
  rw [single_apply]; rw [ite_smul]; rw [one_smul]; rw [zero_smul]; rw [single_apply]

-- See note [reducible non-instances]
/--
Definition of `Function.Injective.mulActionWithZero` / `Function.Injective.mulActionWithZero` 的定义

English:
abbreviation Function.Injective.mulActionWithZero
  signature: (f : ZeroHom A' A) (hf : Injective f)
  body: { hf.mulAction f smul, hf.smulWithZero f smul with }

中文:
缩写 函数.单射.mulActionWithZero
  签名: (f : 保零态射 A' A) (hf : 单射 f)
  定义体: { hf.mulAction f smul, hf.smulWithZero f smul with }
-/
protected abbrev Function.Injective.mulActionWithZero (f : ZeroHom A' A) (hf : Injective f)
    (smul : forall (a : M₀) (b), f (a • b) = a • f b) : MulActionWithZero M₀ A' :=
  { hf.mulAction f smul, hf.smulWithZero f smul with }

-- See note [reducible non-instances]
/--
Definition of `Function.Surjective.mulActionWithZero` / `Function.Surjective.mulActionWithZero` 的定义

English:
abbreviation Function.Surjective.mulActionWithZero
  signature: (f : ZeroHom A A') (hf : Surjective f)
  body: { hf.mulAction f smul, hf.smulWithZero f smul with }

中文:
缩写 函数.满射.mulActionWithZero
  签名: (f : 保零态射 A A') (hf : 满射 f)
  定义体: { hf.mulAction f smul, hf.smulWithZero f smul with }
-/
protected abbrev Function.Surjective.mulActionWithZero (f : ZeroHom A A') (hf : Surjective f)
    (smul : forall (a : M₀) (b), f (a • b) = a • f b) : MulActionWithZero M₀ A' :=
  { hf.mulAction f smul, hf.smulWithZero f smul with }

variable (A)

/-- Compose a `MulActionWithZero` with a `MonoidWithZeroHom`, with action `f r' • m` -/
@[instance_reducible]
/--
Definition of `MulActionWithZero.compHom` / `MulActionWithZero.compHom` 的定义

English:
definition MulActionWithZero.compHom
  signature: (f : M₀' ->*₀ M₀)
  body: SMulWithZero.compHom A f.toZeroHom
  mul_smul r s m := by change f (r * s) • m = f r • f s • m; simp [mul_smul]
  one_smul m := by change f 1 • m = m; simp

中文:
定义 带零乘法作用.compHom
  签名: (f : M₀' ->*₀ M₀)
  定义体: SMulWithZero.compHom A f.toZeroHom
  mul_smul r s m := by change f (r * s) • m = f r • f s • m; simp [mul_smul]
  one_smul m := by change f 1 • m = m; simp

Depends on / 依赖: SMulWithZero, SMulWithZero.compHom, alternatingConstHomologyDataEvenNEZero, alternatingConstHomologyDataOdd, alternatingConstHomologyDataZero, compHom, even_or_odd, f.toZeroHom, n.even_or_odd, toZeroHom
-/
def MulActionWithZero.compHom (f : M₀' ->*₀ M₀) : MulActionWithZero M₀' A where
  __ := SMulWithZero.compHom A f.toZeroHom
  mul_smul r s m := by change f (r * s) • m = f r • f s • m; simp [mul_smul]
  one_smul m := by change f 1 • m = m; simp

end MonoidWithZero

section GroupWithZero
variable [GroupWithZero G₀] [GroupWithZero G₀'] [MulActionWithZero G₀ G₀']
  [SMulCommClass G₀ G₀' G₀'] [IsScalarTower G₀ G₀' G₀']

/--
lemma `smul_inv₀` / 引理 `smul_inv₀`

English:
lemma smul_inv₀
  given: (c : G₀) (x : G₀')
  statement: (c • x)⁻¹ = c⁻¹ • x⁻¹
  proof: by
  obtain rfl | hc := eq_or_ne c 0
  · simp only [inv_zero, zero_smul]
  obtain rfl | hx := eq_or_ne x 0
  · simp only [inv_zero, smul_zero]
  · refine inv_eq_of_mul_eq_one_left ?_
    rw [smul_mul_smul_comm]; rw [inv_mul_cancel₀ hc]; rw [inv_mul_cancel₀ hx]; rw [one_smul]

中文:
引理 smul_inv₀
  条件: (c : G₀) (x : G₀')
  结论: (c • x)⁻¹ = c⁻¹ • x⁻¹
  证明: by
  obtain rfl | hc := eq_or_ne c 0
  · simp only [inv_zero, zero_smul]
  obtain rfl | hx := eq_or_ne x 0
  · simp only [inv_zero, smul_zero]
  · refine inv_eq_of_mul_eq_one_left ?_
    rw [smul_mul_smul_comm]; rw [inv_mul_cancel₀ hc]; rw [inv_mul_cancel₀ hx]; rw [one_smul]

Depends on / 依赖: eq_or_ne, inv_eq_of_mul_eq_one_left, inv_zero, one_smul, smul_mul_smul_comm, smul_zero, zero_smul
-/
lemma smul_inv₀ (c : G₀) (x : G₀') : (c • x)⁻¹ = c⁻¹ • x⁻¹ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp only [inv_zero, zero_smul]
  obtain rfl | hx := eq_or_ne x 0
  · simp only [inv_zero, smul_zero]
  · refine inv_eq_of_mul_eq_one_left ?_
    rw [smul_mul_smul_comm]; rw [inv_mul_cancel₀ hc]; rw [inv_mul_cancel₀ hx]; rw [one_smul]

end GroupWithZero

/-- Typeclass for scalar multiplication that preserves `0` and `+` on the right.

This is exactly `DistribMulAction` without the `MulAction` part.
-/
@[ext]
/--
Definition of `DistribSMul` / `DistribSMul` 的定义

English:
class DistribSMul
  parameters: (M A : Type*) [AddZeroClass A]
  extends: SMulZeroClass M A
  axioms and operations (1):
    - smul_add : forall (a : M) (x y : A), a • (x + y) = a • x + a • y

中文:
类 分配标量乘法
  参数: (M A : 类型) [加法零类 A]
  继承: SMulZero类 M A
  公理与运算 (1 个):
    - smul_add : 对任意 (a : M) (x y : A), a • (x + y) = a • x + a • y
-/
class DistribSMul (M A : Type*) [AddZeroClass A] extends SMulZeroClass M A where
  /-- Scalar multiplication distributes across addition -/
  smul_add : forall (a : M) (x y : A), a • (x + y) = a • x + a • y

section DistribSMul

variable [AddZeroClass A] [DistribSMul M A]

/--
theorem `smul_add` / 定理 `smul_add`

English:
theorem smul_add
  given: (a : M) (b₁ b₂ : A)
  statement: a • (b₁ + b₂) = a • b₁ + a • b₂
  proof: DistribSMul.smul_add _ _ _

中文:
定理 smul_add
  条件: (a : M) (b₁ b₂ : A)
  结论: a • (b₁ + b₂) = a • b₁ + a • b₂
  证明: DistribSMul.smul_add _ _ _

Depends on / 依赖: DistribSMul, DistribSMul.smul_add, smul_add
-/
theorem smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
  DistribSMul.smul_add _ _ _

/--
Definition of `Function.Injective.distribSMul` / `Function.Injective.distribSMul` 的定义

English:
abbreviation Function.Injective.distribSMul
  signature: [AddZeroClass B] [SMul M B] (f : B ->+ A)
  body: { hf.smulZeroClass f.toZeroHom smul with
smul_add := fun c x y => hf by simp only [smul, map_add, smul_add] }

中文:
缩写 函数.单射.distribSMul
  签名: [加法零类 B] [标量乘法 M B] (f : B ->+ A)
  定义体: { hf.smulZeroClass f.toZeroHom smul with
smul_add := fun c x y => hf by simp only [smul, map_add, smul_add] }
-/
protected abbrev Function.Injective.distribSMul [AddZeroClass B] [SMul M B] (f : B ->+ A)
    (hf : Injective f) (smul : forall (c : M) (x), f (c • x) = c • f x) : DistribSMul M B :=
  { hf.smulZeroClass f.toZeroHom smul with
smul_add := fun c x y => hf by simp only [smul, map_add, smul_add] }

/--
Definition of `Function.Surjective.distribSMul` / `Function.Surjective.distribSMul` 的定义

English:
abbreviation Function.Surjective.distribSMul
  signature: [AddZeroClass B] [SMul M B] (f : A ->+ B)
  body: { f.toZeroHom.smulZeroClass smul with
    smul_add := fun c x y => by
      rcases hf x with ⟨x, rfl⟩
      rcases hf y with ⟨y, rfl⟩
      simp only [smul_add, ← smul, ← map_add] }

中文:
缩写 函数.满射.distribSMul
  签名: [加法零类 B] [标量乘法 M B] (f : A ->+ B)
  定义体: { f.toZeroHom.smulZeroClass smul with
    smul_add := fun c x y => by
      rcases hf x with ⟨x, rfl⟩
      rcases hf y with ⟨y, rfl⟩
      simp only [smul_add, ← smul, ← map_add] }
-/
protected abbrev Function.Surjective.distribSMul [AddZeroClass B] [SMul M B] (f : A ->+ B)
    (hf : Surjective f) (smul : forall (c : M) (x), f (c • x) = c • f x) : DistribSMul M B :=
  { f.toZeroHom.smulZeroClass smul with
    smul_add := fun c x y => by
      rcases hf x with ⟨x, rfl⟩
      rcases hf y with ⟨y, rfl⟩
      simp only [smul_add, ← smul, ← map_add] }

/--
Definition of `Function.Surjective.distribSMulLeft` / `Function.Surjective.distribSMulLeft` 的定义

English:
abbreviation Function.Surjective.distribSMulLeft
  signature: {R S M : Type*} [AddZeroClass M] [DistribSMul R M]
  body: { hf.smulZeroClassLeft f hsmul with
    smul_add := hf.forall.mpr fun c x y => by simp only [hsmul, smul_add] }

中文:
缩写 函数.满射.distribSMulLeft
  签名: {R S M : 类型} [加法零类 M] [分配标量乘法 R M]
  定义体: { hf.smulZeroClassLeft f hsmul with
    smul_add := hf.forall.mpr fun c x y => by simp only [hsmul, smul_add] }

Depends on / 依赖: hf.forall.mpr, hf.smulZeroClassLeft, smulZeroClassLeft, smul_add
-/
abbrev Function.Surjective.distribSMulLeft {R S M : Type*} [AddZeroClass M] [DistribSMul R M]
    [SMul S M] (f : R -> S) (hf : Function.Surjective f)
    (hsmul : forall (c) (x : M), f c • x = c • x) : DistribSMul S M :=
  { hf.smulZeroClassLeft f hsmul with
    smul_add := hf.forall.mpr fun c x y => by simp only [hsmul, smul_add] }

variable (A)

/--
Definition of `DistribSMul.compFun` / `DistribSMul.compFun` 的定义

English:
abbreviation DistribSMul.compFun
  signature: (f : N -> M)
  body: { SMulZeroClass.compFun A f with
    smul_add := fun x => smul_add (f x) }

中文:
缩写 分配标量乘法.compFun
  签名: (f : N -> M)
  定义体: { SMulZeroClass.compFun A f with
    smul_add := fun x => smul_add (f x) }

Depends on / 依赖: SMulZeroClass, SMulZeroClass.compFun, compFun, smul_add
-/
abbrev DistribSMul.compFun (f : N -> M) : DistribSMul N A :=
  { SMulZeroClass.compFun A f with
    smul_add := fun x => smul_add (f x) }

/-- Each element of the scalars defines an additive monoid homomorphism. -/
@[simps]
/--
Definition of `DistribSMul.toAddMonoidHom` / `DistribSMul.toAddMonoidHom` 的定义

English:
definition DistribSMul.toAddMonoidHom
  signature: (x : M)
  body: { SMulZeroClass.toZeroHom A x with toFun := (x • ·), map_add' := smul_add x }

中文:
定义 分配标量乘法.toAddMonoidHom
  签名: (x : M)
  定义体: { SMulZeroClass.toZeroHom A x with toFun := (x • ·), map_add' := smul_add x }

Depends on / 依赖: SMulZeroClass, SMulZeroClass.toZeroHom, map_add, smul_add, toZeroHom
-/
def DistribSMul.toAddMonoidHom (x : M) : A ->+ A :=
  { SMulZeroClass.toZeroHom A x with toFun := (x • ·), map_add' := smul_add x }

/--
Instance `AddMonoid.nat_smulCommClass` / 实例 `AddMonoid.nat_smulCommClass`

English:
instance AddMonoid.nat_smulCommClass
  signature: {M A : Type*} [AddMonoid A] [DistribSMul M A]
  body: ((DistribSMul.toAddMonoidHom A x).map_nsmul n y).symm

中文:
实例 加法幺半群.nat_smulCommClass
  签名: {M A : 类型} [加法幺半群 A] [分配标量乘法 M A]
  定义体: ((DistribSMul.toAddMonoidHom A x).map_nsmul n y).symm

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, map_nsmul, toAddMonoidHom
-/
instance AddMonoid.nat_smulCommClass {M A : Type*} [AddMonoid A] [DistribSMul M A] :
    SMulCommClass Nat M A where
  smul_comm n x y := ((DistribSMul.toAddMonoidHom A x).map_nsmul n y).symm

-- `SMulCommClass.symm` is not registered as an instance, as it would cause a loop
/--
Instance `AddMonoid.nat_smulCommClass'` / 实例 `AddMonoid.nat_smulCommClass'`

English:
instance AddMonoid.nat_smulCommClass'
  signature: {M A : Type*} [AddMonoid A] [DistribSMul M A]
  body: .symm _ _ _

中文:
实例 加法幺半群.nat_smulCommClass'
  签名: {M A : 类型} [加法幺半群 A] [分配标量乘法 M A]
  定义体: .symm _ _ _
-/
instance AddMonoid.nat_smulCommClass' {M A : Type*} [AddMonoid A] [DistribSMul M A] :
    SMulCommClass M Nat A :=
  .symm _ _ _

end DistribSMul

/-- Typeclass for multiplicative actions on additive structures.

For example, if `G` is a group (with group law written as multiplication) and `A` is an
abelian group (with group law written as addition), then to give `A` a `G`-module
structure (for example, to use the theory of group cohomology) is to say `[DistribMulAction G A]`.
Note in that we do not use the `Module` typeclass for `G`-modules, as the `Module` typeclass
is for modules over a ring rather than a group.

Mathematically, `DistribMulAction G A` is equivalent to giving `A` the structure of
a `ℤ[G]`-module.
-/
@[ext]
/--
Definition of `DistribMulAction` / `DistribMulAction` 的定义

English:
class DistribMulAction
  parameters: (M A : Type*) [Monoid M] [AddMonoid A]
  extends: MulAction M A
  axioms and operations (2):
    - smul_zero : forall a : M, a • (0 : A) = 0
    - smul_add : forall (a : M) (x y : A), a • (x + y) = a • x + a • y

中文:
类 分配乘法作用
  参数: (M A : 类型) [幺半群 M] [加法幺半群 A]
  继承: 乘法作用 M A
  公理与运算 (2 个):
    - smul_zero : 对任意 a : M, a • (0 : A) = 0
    - smul_add : 对任意 (a : M) (x y : A), a • (x + y) = a • x + a • y
-/
class DistribMulAction (M A : Type*) [Monoid M] [AddMonoid A] extends MulAction M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : forall a : M, a • (0 : A) = 0
  /-- Scalar multiplication distributes across addition -/
  smul_add : forall (a : M) (x y : A), a • (x + y) = a • x + a • y

section

variable [Monoid M] [AddMonoid A] [DistribMulAction M A]

-- See note [lower instance priority]
instance (priority := 100) DistribMulAction.toDistribSMul : DistribSMul M A :=
  { ‹DistribMulAction M A› with }

/-! We make sure that the definition of `DistribMulAction.toDistribSMul` was done correctly,
and the two paths from `DistribMulAction` to `SMul` are indeed definitionally equal. -/
example :
    (DistribMulAction.toMulAction.toSMul : SMul M A) =
      DistribMulAction.toDistribSMul.toSMul :=
  rfl

/--
Definition of `Function.Injective.distribMulAction` / `Function.Injective.distribMulAction` 的定义

English:
abbreviation Function.Injective.distribMulAction
  signature: [AddMonoid B] [SMul M B] (f : B ->+ A)
  body: { hf.distribSMul f smul, hf.mulAction f smul with }

中文:
缩写 函数.单射.distribMulAction
  签名: [加法幺半群 B] [标量乘法 M B] (f : B ->+ A)
  定义体: { hf.distribSMul f smul, hf.mulAction f smul with }
-/
protected abbrev Function.Injective.distribMulAction [AddMonoid B] [SMul M B] (f : B ->+ A)
    (hf : Injective f) (smul : forall (c : M) (x), f (c • x) = c • f x) : DistribMulAction M B :=
  { hf.distribSMul f smul, hf.mulAction f smul with }

/--
Definition of `Function.Surjective.distribMulAction` / `Function.Surjective.distribMulAction` 的定义

English:
abbreviation Function.Surjective.distribMulAction
  signature: [AddMonoid B] [SMul M B] (f : A ->+ B)
  body: { hf.distribSMul f smul, hf.mulAction f smul with }

中文:
缩写 函数.满射.distribMulAction
  签名: [加法幺半群 B] [标量乘法 M B] (f : A ->+ B)
  定义体: { hf.distribSMul f smul, hf.mulAction f smul with }
-/
protected abbrev Function.Surjective.distribMulAction [AddMonoid B] [SMul M B] (f : A ->+ B)
    (hf : Surjective f) (smul : forall (c : M) (x), f (c • x) = c • f x) : DistribMulAction M B :=
  { hf.distribSMul f smul, hf.mulAction f smul with }

variable (A)

/-- Each element of the monoid defines an additive monoid homomorphism. -/
@[simps!, deprecated DistribSMul.toAddMonoidHom (since := "2026-01-07")]
/--
Definition of `DistribMulAction.toAddMonoidHom` / `DistribMulAction.toAddMonoidHom` 的定义

English:
definition DistribMulAction.toAddMonoidHom
  signature: (x : M)
  body: DistribSMul.toAddMonoidHom A x

中文:
定义 分配乘法作用.toAddMonoidHom
  签名: (x : M)
  定义体: DistribSMul.toAddMonoidHom A x

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, toAddMonoidHom
-/
def DistribMulAction.toAddMonoidHom (x : M) : A ->+ A :=
  DistribSMul.toAddMonoidHom A x

variable (M)

/-- Each element of the monoid defines an additive monoid homomorphism. -/
@[simps]
/--
Definition of `DistribMulAction.toAddMonoidEnd` / `DistribMulAction.toAddMonoidEnd` 的定义

English:
definition DistribMulAction.toAddMonoidEnd
  signature: :
  body: DistribSMul.toAddMonoidHom A
map_one' := AddMonoidHom.ext one_smul M
map_mul' x y := AddMonoidHom.ext mul_smul x y

中文:
定义 分配乘法作用.toAddMonoidEnd
  签名: :
  定义体: DistribSMul.toAddMonoidHom A
map_one' := AddMonoidHom.ext one_smul M
map_mul' x y := AddMonoidHom.ext mul_smul x y

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, toAddMonoidHom
-/
def DistribMulAction.toAddMonoidEnd :
    M ->* AddMonoid.End A where
  toFun := DistribSMul.toAddMonoidHom A
map_one' := AddMonoidHom.ext one_smul M
map_mul' x y := AddMonoidHom.ext mul_smul x y

end

section

variable [AddGroup A] [DistribSMul M A]

/--
Instance `AddGroup.int_smulCommClass` / 实例 `AddGroup.int_smulCommClass`

English:
instance AddGroup.int_smulCommClass
  signature: : SMulCommClass Int M A where
  body: ((DistribSMul.toAddMonoidHom A x).map_zsmul n y).symm

中文:
实例 加法群.int_smulCommClass
  签名: : 标量交换类 整数 M A where
  定义体: ((DistribSMul.toAddMonoidHom A x).map_zsmul n y).symm

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, map_zsmul, toAddMonoidHom
-/
instance AddGroup.int_smulCommClass : SMulCommClass Int M A where
  smul_comm n x y := ((DistribSMul.toAddMonoidHom A x).map_zsmul n y).symm

-- `SMulCommClass.symm` is not registered as an instance, as it would cause a loop
/--
Instance `AddGroup.int_smulCommClass'` / 实例 `AddGroup.int_smulCommClass'`

English:
instance AddGroup.int_smulCommClass'
  signature: : SMulCommClass M Int A
  body: SMulCommClass.symm _ _ _

@[simp]

中文:
实例 加法群.int_smulCommClass'
  签名: : 标量交换类 M 整数 A
  定义体: SMulCommClass.symm _ _ _

@[simp]

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance AddGroup.int_smulCommClass' : SMulCommClass M Int A :=
  SMulCommClass.symm _ _ _

@[simp]
/--
theorem `smul_neg` / 定理 `smul_neg`

English:
theorem smul_neg
  given: (r : M) (x : A)
  statement: r • -x = -(r • x)
  proof: eq_neg_of_add_eq_zero_left by rw [← smul_add, neg_add_cancel, smul_zero]

中文:
定理 smul_neg
  条件: (r : M) (x : A)
  结论: r • -x = -(r • x)
  证明: eq_neg_of_add_eq_zero_left by rw [← smul_add, neg_add_cancel, smul_zero]

Depends on / 依赖: eq_neg_of_add_eq_zero_left, neg_add_cancel, smul_add, smul_zero
-/
theorem smul_neg (r : M) (x : A) : r • -x = -(r • x) :=
eq_neg_of_add_eq_zero_left by rw [← smul_add, neg_add_cancel, smul_zero]

/--
theorem `smul_sub` / 定理 `smul_sub`

English:
theorem smul_sub
  given: (r : M) (x y : A)
  statement: r • (x - y) = r • x - r • y
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [smul_add]; rw [smul_neg]

中文:
定理 smul_sub
  条件: (r : M) (x y : A)
  结论: r • (x - y) = r • x - r • y
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [smul_add]; rw [smul_neg]

Depends on / 依赖: smul_add, smul_neg, sub_eq_add_neg
-/
theorem smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [smul_add]; rw [smul_neg]

end

section DistribMulAction
variable [Group α] [AddMonoid β] [DistribMulAction α β]

/--
lemma `smul_eq_zero_iff_eq` / 引理 `smul_eq_zero_iff_eq`

English:
lemma smul_eq_zero_iff_eq
  given: (a : α) {x : β}
  statement: a • x = 0 ↔ x = 0
  proof: ⟨fun h => by rw [← inv_smul_smul a x, h, smul_zero], fun h => h.symm ▸ smul_zero _⟩

中文:
引理 smul_eq_zero_iff_eq
  条件: (a : α) {x : β}
  结论: a • x = 0 ↔ x = 0
  证明: ⟨fun h => by rw [← inv_smul_smul a x, h, smul_zero], fun h => h.symm ▸ smul_zero _⟩

Depends on / 依赖: h.symm, inv_smul_smul, smul_zero
-/
lemma smul_eq_zero_iff_eq (a : α) {x : β} : a • x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← inv_smul_smul a x, h, smul_zero], fun h => h.symm ▸ smul_zero _⟩

/--
lemma `smul_ne_zero_iff_ne` / 引理 `smul_ne_zero_iff_ne`

English:
lemma smul_ne_zero_iff_ne
  given: (a : α) {x : β}
  statement: a • x != 0 ↔ x != 0
  proof: not_congr smul_eq_zero_iff_eq a

中文:
引理 smul_ne_zero_iff_ne
  条件: (a : α) {x : β}
  结论: a • x != 0 ↔ x != 0
  证明: not_congr smul_eq_zero_iff_eq a

Depends on / 依赖: not_congr, smul_eq_zero_iff_eq
-/
lemma smul_ne_zero_iff_ne (a : α) {x : β} : a • x != 0 ↔ x != 0 :=
not_congr smul_eq_zero_iff_eq a

end DistribMulAction

section MulDistribMulAction
variable [Group α] [GroupWithZero β] [MulDistribMulAction α β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulZeroClass α β
  body: not_imp_comm.mp mul_inv_cancel₀ by
    rw [← smul_one g]; rw [← inv_smul_eq_iff]; rw [smul_mul']; rw [inv_smul_smul]; rw [zero_mul]
    exact zero_ne_one

中文:
实例 :
  签名: SMulZero类 α β
  定义体: not_imp_comm.mp mul_inv_cancel₀ by
    rw [← smul_one g]; rw [← inv_smul_eq_iff]; rw [smul_mul']; rw [inv_smul_smul]; rw [zero_mul]
    exact zero_ne_one

Depends on / 依赖: inv_smul_eq_iff, inv_smul_smul, not_imp_comm, not_imp_comm.mp, smul_mul, smul_one, zero_mul, zero_ne_one
-/
instance : SMulZeroClass α β where
smul_zero g := not_imp_comm.mp mul_inv_cancel₀ by
    rw [← smul_one g]; rw [← inv_smul_eq_iff]; rw [smul_mul']; rw [inv_smul_smul]; rw [zero_mul]
    exact zero_ne_one

/--
theorem `smul_inv₀'` / 定理 `smul_inv₀'`

English:
theorem smul_inv₀'
  given: (g : α) (x : β)
  statement: g • x⁻¹ = (g • x)⁻¹
  proof: by
  by_cases hx : x = 0
  · rw [hx, inv_zero, smul_zero, inv_zero]
  · apply eq_inv_of_mul_eq_one_right
    rw [← smul_mul']; rw [mul_inv_cancel₀ hx]; rw [smul_one]

中文:
定理 smul_inv₀'
  条件: (g : α) (x : β)
  结论: g • x⁻¹ = (g • x)⁻¹
  证明: by
  by_cases hx : x = 0
  · rw [hx, inv_zero, smul_zero, inv_zero]
  · apply eq_inv_of_mul_eq_one_right
    rw [← smul_mul']; rw [mul_inv_cancel₀ hx]; rw [smul_one]
-/
@[simp] theorem smul_inv₀' (g : α) (x : β) : g • x⁻¹ = (g • x)⁻¹ := by
  by_cases hx : x = 0
  · rw [hx, inv_zero, smul_zero, inv_zero]
  · apply eq_inv_of_mul_eq_one_right
    rw [← smul_mul']; rw [mul_inv_cancel₀ hx]; rw [smul_one]

/--
theorem `smul_div₀'` / 定理 `smul_div₀'`

English:
theorem smul_div₀'
  given: (g : α) (x y : β)
  statement: g • (x / y) = (g • x) / (g • y)
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [smul_mul']; rw [smul_inv₀']

中文:
定理 smul_div₀'
  条件: (g : α) (x y : β)
  结论: g • (x / y) = (g • x) / (g • y)
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [smul_mul']; rw [smul_inv₀']

Depends on / 依赖: div_eq_mul_inv, smul_mul
-/
theorem smul_div₀' (g : α) (x y : β) : g • (x / y) = (g • x) / (g • y) := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [smul_mul']; rw [smul_inv₀']

end MulDistribMulAction
