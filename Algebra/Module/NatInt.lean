/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Modules over `ℕ` and `ℤ`

This file concerns modules where the scalars are the natural numbers or the integers.

## Main definitions

* `AddCommMonoid.toNatModule`: any `AddCommMonoid` is (uniquely) a module over the naturals.
* `AddCommGroup.toIntModule`: any `AddCommGroup` is a module over the integers.

## Main results

* `AddCommMonoid.uniqueNatModule`: there is a unique `AddCommMonoid ℕ M` structure for any `M`

## Tags

semimodule, module, vector space
-/

@[expose] public section

assert_not_exists RelIso Field Invertible Multiset Pi.single_smul₀ Set.indicator

open Function Set

universe u v

variable {R S M M₂ : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: M] : MulAction Nat M where
  body: one_nsmul
  mul_smul _ _ _ := mul_nsmul' ..

中文:
实例 [加法幺半群
  签名: M] : 乘法作用 自然数 M where
  定义体: one_nsmul
  mul_smul _ _ _ := mul_nsmul' ..

Depends on / 依赖: one_nsmul
-/
instance [AddMonoid M] : MulAction Nat M where
  one_smul := one_nsmul
  mul_smul _ _ _ := mul_nsmul' ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: M] : SMulWithZero Nat M where
  body: nsmul_zero
  zero_smul := zero_nsmul

中文:
实例 [加法幺半群
  签名: M] : 带零标量乘法 自然数 M where
  定义体: nsmul_zero
  zero_smul := zero_nsmul

Depends on / 依赖: nsmul_zero
-/
instance [AddMonoid M] : SMulWithZero Nat M where
  smul_zero := nsmul_zero
  zero_smul := zero_nsmul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SubtractionMonoid
  signature: M] : MulAction Int M where
  body: one_zsmul
  mul_smul _ _ _ := mul_zsmul ..

中文:
实例 [Subtraction幺半群
  签名: M] : 乘法作用 整数 M where
  定义体: one_zsmul
  mul_smul _ _ _ := mul_zsmul ..

Depends on / 依赖: one_zsmul
-/
instance [SubtractionMonoid M] : MulAction Int M where
  one_smul := one_zsmul
  mul_smul _ _ _ := mul_zsmul ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SubtractionMonoid
  signature: M] : SMulWithZero Int M where
  body: zsmul_zero
  zero_smul := zero_zsmul

中文:
实例 [Subtraction幺半群
  签名: M] : 带零标量乘法 整数 M where
  定义体: zsmul_zero
  zero_smul := zero_zsmul

Depends on / 依赖: zsmul_zero
-/
instance [SubtractionMonoid M] : SMulWithZero Int M where
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul

section AddCommMonoid

variable [AddCommMonoid M]

/--
Instance `AddCommMonoid.toNatModule` / 实例 `AddCommMonoid.toNatModule`

English:
instance AddCommMonoid.toNatModule
  signature: : Module Nat M where
  body: nsmul_add a b n
  smul_zero := nsmul_zero
  zero_smul := zero_nsmul
  add_smul r s x := add_nsmul x r s

中文:
实例 加法交换幺半群.to自然数Module
  签名: : 模 自然数 M where
  定义体: nsmul_add a b n
  smul_zero := nsmul_zero
  zero_smul := zero_nsmul
  add_smul r s x := add_nsmul x r s

Depends on / 依赖: nsmul_add
-/
instance AddCommMonoid.toNatModule : Module Nat M where
  smul_add n a b := nsmul_add a b n
  smul_zero := nsmul_zero
  zero_smul := zero_nsmul
  add_smul r s x := add_nsmul x r s

/--
theorem `DistribSMul.toAddMonoidHom_eq_nsmulAddMonoidHom` / 定理 `DistribSMul.toAddMonoidHom_eq_nsmulAddMonoidHom`

English:
theorem DistribSMul.toAddMonoidHom_eq_nsmulAddMonoidHom
  proof: rfl

中文:
定理 分配标量乘法.toAddMonoidHom_eq_nsmulAddMonoidHom
  证明: rfl
-/
theorem DistribSMul.toAddMonoidHom_eq_nsmulAddMonoidHom :
    toAddMonoidHom M = nsmulAddMonoidHom := rfl

end AddCommMonoid

section AddCommGroup

variable (M) [AddCommGroup M]

/--
Instance `AddCommGroup.toIntModule` / 实例 `AddCommGroup.toIntModule`

English:
instance AddCommGroup.toIntModule
  signature: : Module Int M where
  body: one_zsmul
  mul_smul m n a := mul_zsmul a m n
  smul_add n a b := zsmul_add a b n
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul
  add_smul r s x := add_zsmul x r s

中文:
实例 加法交换群.to整数Module
  签名: : 模 整数 M where
  定义体: one_zsmul
  mul_smul m n a := mul_zsmul a m n
  smul_add n a b := zsmul_add a b n
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul
  add_smul r s x := add_zsmul x r s

Depends on / 依赖: one_zsmul
-/
instance AddCommGroup.toIntModule : Module Int M where
  one_smul := one_zsmul
  mul_smul m n a := mul_zsmul a m n
  smul_add n a b := zsmul_add a b n
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul
  add_smul r s x := add_zsmul x r s

/--
theorem `DistribSMul.toAddMonoidHom_eq_zsmulAddGroupHom` / 定理 `DistribSMul.toAddMonoidHom_eq_zsmulAddGroupHom`

English:
theorem DistribSMul.toAddMonoidHom_eq_zsmulAddGroupHom
  proof: rfl

中文:
定理 分配标量乘法.toAddMonoidHom_eq_zsmulAddGroupHom
  证明: rfl
-/
theorem DistribSMul.toAddMonoidHom_eq_zsmulAddGroupHom :
    toAddMonoidHom M = zsmulAddGroupHom := rfl

end AddCommGroup

variable (R) in
/--
Definition of `Module.addCommMonoidToAddCommGroup` / `Module.addCommMonoidToAddCommGroup` 的定义

English:
abbreviation Module.addCommMonoidToAddCommGroup
  body: fun a => (-1 : R) • a
  neg_add_cancel := fun a =>
    show (-1 : R) • a + a = 0 by
      nth_rw 2 [← one_smul R a]
      rw [← add_smul]; rw [neg_add_cancel]; rw [zero_smul]
  zsmul z a := (z : R) • a
  zsmul_zero' a := by simp_rw [HSMul.hSMul, SMul.smul, Int.cast_zero]; exact zero_smul R a
  zsmul_succ' z a := by simp_rw [HSMul.hSMul, SMul.smul]; simp [add_comm, add_smul]
  zsmul_neg' z a := by
    change (Int.negSucc z : R) • a = -1 • ((z.succ : Int) : R) • a
    simp [← smul_assoc]

中文:
缩写 模.addCommMonoidToAddCommGroup
  定义体: fun a => (-1 : R) • a
  neg_add_cancel := fun a =>
    show (-1 : R) • a + a = 0 by
      nth_rw 2 [← one_smul R a]
      rw [← add_smul]; rw [neg_add_cancel]; rw [zero_smul]
  zsmul z a := (z : R) • a
  zsmul_zero' a := by simp_rw [HSMul.hSMul, SMul.smul, Int.cast_zero]; exact zero_smul R a
  zsmul_succ' z a := by simp_rw [HSMul.hSMul, SMul.smul]; simp [add_comm, add_smul]
  zsmul_neg' z a := by
    change (Int.negSucc z : R) • a = -1 • ((z.succ : Int) : R) • a
    simp [← smul_assoc]
-/
abbrev Module.addCommMonoidToAddCommGroup
    [Ring R] [AddCommMonoid M] [Module R M] : AddCommGroup M where
  neg := fun a => (-1 : R) • a
  neg_add_cancel := fun a =>
    show (-1 : R) • a + a = 0 by
      nth_rw 2 [← one_smul R a]
      rw [← add_smul]; rw [neg_add_cancel]; rw [zero_smul]
  zsmul z a := (z : R) • a
  zsmul_zero' a := by simp_rw [HSMul.hSMul, SMul.smul, Int.cast_zero]; exact zero_smul R a
  zsmul_succ' z a := by simp_rw [HSMul.hSMul, SMul.smul]; simp [add_comm, add_smul]
  zsmul_neg' z a := by
    change (Int.negSucc z : R) • a = -1 • ((z.succ : Int) : R) • a
    simp [← smul_assoc]

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

section

variable (R)

/-- `nsmul` is equal to any other module structure via a cast. -/
@[norm_cast]
/--
lemma `Nat.cast_smul_eq_nsmul` / 引理 `Nat.cast_smul_eq_nsmul`

English:
lemma Nat.cast_smul_eq_nsmul
  given: (n : Nat) (b : M)
  statement: (n : R) • b = n • b
  proof: by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, zero_smul]
  | succ n ih => rw [Nat.cast_succ, add_smul, add_smul, one_smul, ih, one_smul]

中文:
引理 自然数.cast_smul_eq_nsmul
  条件: (n : 自然数) (b : M)
  结论: (n : R) • b = n • b
  证明: by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, zero_smul]
  | succ n ih => rw [Nat.cast_succ, add_smul, add_smul, one_smul, ih, one_smul]

Depends on / 依赖: Nat.cast_succ, Nat.cast_zero, add_smul, cast_succ, cast_zero, one_smul, zero_smul
-/
lemma Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : R) • b = n • b := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, zero_smul]
  | succ n ih => rw [Nat.cast_succ, add_smul, add_smul, one_smul, ih, one_smul]

/--
lemma `ofNat_smul_eq_nsmul` / 引理 `ofNat_smul_eq_nsmul`

English:
lemma ofNat_smul_eq_nsmul
  given: (n : Nat) [n.AtLeastTwo] (b : M)
  proof: Nat.cast_smul_eq_nsmul ..

中文:
引理 of自然数_smul_eq_nsmul
  条件: (n : 自然数) [n.AtLeastTwo] (b : M)
  证明: Nat.cast_smul_eq_nsmul ..

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul
-/
lemma ofNat_smul_eq_nsmul (n : Nat) [n.AtLeastTwo] (b : M) :
    (ofNat(n) : R) • b = ofNat(n) • b := Nat.cast_smul_eq_nsmul ..

end

/--
theorem `nat_smul_eq_nsmul` / 定理 `nat_smul_eq_nsmul`

English:
theorem nat_smul_eq_nsmul
  given: (h : Module Nat M) (n : Nat) (x : M)
  statement: h.smul n x = n • x
  proof: Nat.cast_smul_eq_nsmul ..

中文:
定理 nat_smul_eq_nsmul
  条件: (h : 模 自然数 M) (n : 自然数) (x : M)
  结论: h.smul n x = n • x
  证明: Nat.cast_smul_eq_nsmul ..

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul
-/
theorem nat_smul_eq_nsmul (h : Module Nat M) (n : Nat) (x : M) : h.smul n x = n • x :=
  Nat.cast_smul_eq_nsmul ..

/-- All `ℕ`-module structures are equal. Not an instance since in mathlib all `AddCommMonoid`
should normally have exactly one `ℕ`-module structure by design. -/
@[instance_reducible]
/--
Definition of `AddCommMonoid.uniqueNatModule` / `AddCommMonoid.uniqueNatModule` 的定义

English:
definition AddCommMonoid.uniqueNatModule
  signature: : Unique (Module Nat M) where
  body: inferInstance
  uniq P := (Module.ext' P _) fun n => by convert! nat_smul_eq_nsmul P n

中文:
定义 加法交换幺半群.unique自然数Module
  签名: : 唯一 (模 自然数 M) where
  定义体: inferInstance
  uniq P := (Module.ext' P _) fun n => by convert! nat_smul_eq_nsmul P n
-/
def AddCommMonoid.uniqueNatModule : Unique (Module Nat M) where
  default := inferInstance
  uniq P := (Module.ext' P _) fun n => by convert! nat_smul_eq_nsmul P n

/--
Instance `AddCommMonoid.subsingletonNatModule` / 实例 `AddCommMonoid.subsingletonNatModule`

English:
instance AddCommMonoid.subsingletonNatModule
  signature: : Subsingleton (Module Nat M)
  body: AddCommMonoid.uniqueNatModule.instSubsingleton

中文:
实例 加法交换幺半群.subsingleton自然数Module
  签名: : 子单例 (模 自然数 M)
  定义体: AddCommMonoid.uniqueNatModule.instSubsingleton

Depends on / 依赖: AddCommMonoid, AddCommMonoid.uniqueNatModule.instSubsingleton, instSubsingleton, uniqueNatModule
-/
instance AddCommMonoid.subsingletonNatModule : Subsingleton (Module Nat M) :=
  AddCommMonoid.uniqueNatModule.instSubsingleton

/--
Instance `AddCommMonoid.nat_isScalarTower` / 实例 `AddCommMonoid.nat_isScalarTower`

English:
instance AddCommMonoid.nat_isScalarTower
  signature: : IsScalarTower Nat R M where
  body: by
    induction n with
    | zero => simp only [zero_smul]
    | succ n ih => simp only [add_smul, one_smul, ih]

中文:
实例 加法交换幺半群.nat_isScalarTower
  签名: : 标量塔 自然数 R M where
  定义体: by
    induction n with
    | zero => simp only [zero_smul]
    | succ n ih => simp only [add_smul, one_smul, ih]

Depends on / 依赖: add_smul, one_smul, zero_smul
-/
instance AddCommMonoid.nat_isScalarTower : IsScalarTower Nat R M where
  smul_assoc n x y := by
    induction n with
    | zero => simp only [zero_smul]
    | succ n ih => simp only [add_smul, one_smul, ih]

end AddCommMonoid

/--
theorem `map_natCast_smul` / 定理 `map_natCast_smul`

English:
theorem map_natCast_smul
  statement: [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
  proof: by
  simp only [Nat.cast_smul_eq_nsmul, map_nsmul]

中文:
定理 map_natCast_smul
  结论: [加法交换幺半群 M] [加法交换幺半群 M₂] {F : 类型} [函数状 F M M₂]
  证明: by
  simp only [Nat.cast_smul_eq_nsmul, map_nsmul]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, map_nsmul
-/
theorem map_natCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Semiring R] [Semiring S] [Module R M]
    [Module S M₂] (x : Nat) (a : M) : f ((x : R) • a) = (x : S) • f a := by
  simp only [Nat.cast_smul_eq_nsmul, map_nsmul]

/--
theorem `Nat.smul_one_eq_cast` / 定理 `Nat.smul_one_eq_cast`

English:
theorem Nat.smul_one_eq_cast
  given: {R : Type*} [NonAssocSemiring R] (m : Nat)
  statement: m • (1 : R) = ↑m
  proof: by
  rw [nsmul_eq_mul]; rw [mul_one]

中文:
定理 自然数.smul_one_eq_cast
  条件: {R : 类型} [非结合半环 R] (m : 自然数)
  结论: m • (1 : R) = ↑m
  证明: by
  rw [nsmul_eq_mul]; rw [mul_one]

Depends on / 依赖: mul_one, nsmul_eq_mul
-/
theorem Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring R] (m : Nat) : m • (1 : R) = ↑m := by
  rw [nsmul_eq_mul]; rw [mul_one]

/--
theorem `Int.smul_one_eq_cast` / 定理 `Int.smul_one_eq_cast`

English:
theorem Int.smul_one_eq_cast
  given: {R : Type*} [NonAssocRing R] (m : Int)
  statement: m • (1 : R) = ↑m
  proof: by
  rw [zsmul_eq_mul]; rw [mul_one]

中文:
定理 整数.smul_one_eq_cast
  条件: {R : 类型} [非结合环 R] (m : 整数)
  结论: m • (1 : R) = ↑m
  证明: by
  rw [zsmul_eq_mul]; rw [mul_one]

Depends on / 依赖: mul_one, zsmul_eq_mul
-/
theorem Int.smul_one_eq_cast {R : Type*} [NonAssocRing R] (m : Int) : m • (1 : R) = ↑m := by
  rw [zsmul_eq_mul]; rw [mul_one]

section AddCommGroup

variable [Ring R] [AddCommGroup M] [Module R M]

section

variable (R)

/-- `zsmul` is equal to any other module structure via a cast. -/
@[norm_cast]
/--
lemma `Int.cast_smul_eq_zsmul` / 引理 `Int.cast_smul_eq_zsmul`

English:
lemma Int.cast_smul_eq_zsmul
  given: (n : Int) (b : M)
  statement: (n : R) • b = n • b
  proof: by
  cases n with
  | ofNat => simp [Nat.cast_smul_eq_nsmul]
  | negSucc => simp [add_smul, Nat.cast_smul_eq_nsmul]

中文:
引理 整数.cast_smul_eq_zsmul
  条件: (n : 整数) (b : M)
  结论: (n : R) • b = n • b
  证明: by
  cases n with
  | ofNat => simp [Nat.cast_smul_eq_nsmul]
  | negSucc => simp [add_smul, Nat.cast_smul_eq_nsmul]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, add_smul, cast_smul_eq_nsmul, negSucc
-/
lemma Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : R) • b = n • b := by
  cases n with
  | ofNat => simp [Nat.cast_smul_eq_nsmul]
  | negSucc => simp [add_smul, Nat.cast_smul_eq_nsmul]

end

/--
theorem `int_smul_eq_zsmul` / 定理 `int_smul_eq_zsmul`

English:
theorem int_smul_eq_zsmul
  given: (h : Module Int M) (n : Int) (x : M)
  statement: h.smul n x = n • x
  proof: Int.cast_smul_eq_zsmul ..

中文:
定理 int_smul_eq_zsmul
  条件: (h : 模 整数 M) (n : 整数) (x : M)
  结论: h.smul n x = n • x
  证明: Int.cast_smul_eq_zsmul ..

Depends on / 依赖: Int.cast_smul_eq_zsmul, cast_smul_eq_zsmul
-/
theorem int_smul_eq_zsmul (h : Module Int M) (n : Int) (x : M) : h.smul n x = n • x :=
  Int.cast_smul_eq_zsmul ..

/-- All `ℤ`-module structures are equal. Not an instance since in mathlib all `AddCommGroup`
should normally have exactly one `ℤ`-module structure by design. -/
@[instance_reducible]
/--
Definition of `AddCommGroup.uniqueIntModule` / `AddCommGroup.uniqueIntModule` 的定义

English:
definition AddCommGroup.uniqueIntModule
  signature: : Unique (Module Int M) where
  body: inferInstance
  uniq P := (Module.ext' P _) fun n => by convert! int_smul_eq_zsmul P n

中文:
定义 加法交换群.unique整数Module
  签名: : 唯一 (模 整数 M) where
  定义体: inferInstance
  uniq P := (Module.ext' P _) fun n => by convert! int_smul_eq_zsmul P n
-/
def AddCommGroup.uniqueIntModule : Unique (Module Int M) where
  default := inferInstance
  uniq P := (Module.ext' P _) fun n => by convert! int_smul_eq_zsmul P n

end AddCommGroup

/--
Instance `AddCommMonoid.subsingletonIntModule` / 实例 `AddCommMonoid.subsingletonIntModule`

English:
instance AddCommMonoid.subsingletonIntModule
  signature: [AddCommMonoid M]
  body: let : AddCommGroup M := Module.addCommMonoidToAddCommGroup Int
    AddCommGroup.uniqueIntModule.instSubsingleton.allEq a b

中文:
实例 加法交换幺半群.subsingleton整数Module
  签名: [加法交换幺半群 M]
  定义体: let : AddCommGroup M := Module.addCommMonoidToAddCommGroup Int
    AddCommGroup.uniqueIntModule.instSubsingleton.allEq a b

Depends on / 依赖: AddCommGroup, AddCommGroup.uniqueIntModule.instSubsingleton.allEq, Module, Module.addCommMonoidToAddCommGroup, addCommMonoidToAddCommGroup, instSubsingleton, uniqueIntModule
-/
instance AddCommMonoid.subsingletonIntModule [AddCommMonoid M] : Subsingleton (Module Int M) where
  allEq a b :=
    let : AddCommGroup M := Module.addCommMonoidToAddCommGroup Int
    AddCommGroup.uniqueIntModule.instSubsingleton.allEq a b

/--
theorem `map_intCast_smul` / 定理 `map_intCast_smul`

English:
theorem map_intCast_smul
  statement: [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
  proof: by simp only [Int.cast_smul_eq_zsmul, map_zsmul]

中文:
定理 map_intCast_smul
  结论: [加法交换群 M] [加法交换群 M₂] {F : 类型} [函数状 F M M₂]
  证明: by simp only [Int.cast_smul_eq_zsmul, map_zsmul]

Depends on / 依赖: Int.cast_smul_eq_zsmul, cast_smul_eq_zsmul, map_zsmul
-/
theorem map_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Ring R] [Ring S] [Module R M] [Module S M₂]
    (x : Int) (a : M) :
    f ((x : R) • a) = (x : S) • f a := by simp only [Int.cast_smul_eq_zsmul, map_zsmul]

/--
Instance `AddCommGroup.intIsScalarTower` / 实例 `AddCommGroup.intIsScalarTower`

English:
instance AddCommGroup.intIsScalarTower
  signature: {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
  body: by
    cases n with
    | ofNat => simp [mul_smul, Nat.cast_smul_eq_nsmul]
    | negSucc => simp [mul_smul, add_smul, Nat.cast_smul_eq_nsmul]

中文:
实例 加法交换群.intIsScalarTower
  签名: {R : 类型u} {M : 类型v} [环 R] [加法交换群 M]
  定义体: by
    cases n with
    | ofNat => simp [mul_smul, Nat.cast_smul_eq_nsmul]
    | negSucc => simp [mul_smul, add_smul, Nat.cast_smul_eq_nsmul]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, add_smul, cast_smul_eq_nsmul, mul_smul, negSucc
-/
instance AddCommGroup.intIsScalarTower {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] : IsScalarTower Int R M where
  smul_assoc n x y := by
    cases n with
    | ofNat => simp [mul_smul, Nat.cast_smul_eq_nsmul]
    | negSucc => simp [mul_smul, add_smul, Nat.cast_smul_eq_nsmul]

variable (M) in
/--
lemma `CharZero.of_module` / 引理 `CharZero.of_module`

English:
lemma CharZero.of_module
  given: [Semiring R] [AddCommMonoidWithOne M] [CharZero M] [Module R M]
  proof: by
  refine ⟨fun m n h => @Nat.cast_injective M _ _ _ _ ?_⟩
  rw [← nsmul_one]; rw [← nsmul_one]; rw [← Nat.cast_smul_eq_nsmul R]; rw [← Nat.cast_smul_eq_nsmul R]; rw [h]

中文:
引理 特征零.of_module
  条件: [半环 R] [加法交换带幺幺半群 M] [特征零 M] [模 R M]
  证明: by
  refine ⟨fun m n h => @Nat.cast_injective M _ _ _ _ ?_⟩
  rw [← nsmul_one]; rw [← nsmul_one]; rw [← Nat.cast_smul_eq_nsmul R]; rw [← Nat.cast_smul_eq_nsmul R]; rw [h]

Depends on / 依赖: Nat.cast_injective, Nat.cast_smul_eq_nsmul, cast_injective, cast_smul_eq_nsmul, nsmul_one
-/
lemma CharZero.of_module [Semiring R] [AddCommMonoidWithOne M] [CharZero M] [Module R M] :
    CharZero R := by
  refine ⟨fun m n h => @Nat.cast_injective M _ _ _ _ ?_⟩
  rw [← nsmul_one]; rw [← nsmul_one]; rw [← Nat.cast_smul_eq_nsmul R]; rw [← Nat.cast_smul_eq_nsmul R]; rw [h]
