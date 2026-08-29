/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Tactic.ArithMult

/-!
# Arithmetic Functions and Dirichlet Convolution

This file defines arithmetic functions, which are functions from `ℕ` to a specified type that map 0
to 0. In the literature, they are often instead defined as functions from `ℕ+`. These arithmetic
functions are endowed with a multiplication, given by Dirichlet convolution, and pointwise addition,
to form the Dirichlet ring.

## Main Definitions

* `ArithmeticFunction R` consists of functions `f : ℕ → R` such that `f 0 = 0`.
* An arithmetic function `f` `IsMultiplicative` when `x.Coprime y → f (x * y) = f x * f y`.
* Multiplication and power instances on `ArithmeticFunction R`, are defined using Dirichlet
  convolution.

Further examples of arithmetic functions, such as the Möbius function `μ`, are available in
other files in the `Mathlib.NumberTheory.ArithmeticFunction` directory.

## Tags

arithmetic functions, dirichlet convolution, divisors
-/

@[expose] public section

open Finset

open Nat

variable (R : Type*)

/--
Definition of `ArithmeticFunction` / `ArithmeticFunction` 的定义

English:
definition ArithmeticFunction
  signature: [Zero R]
  body: ZeroHom Nat R

中文:
定义 ArithmeticFunction
  签名: [零 R]
  定义体: ZeroHom Nat R

Depends on / 依赖: ZeroHom
-/
def ArithmeticFunction [Zero R] :=
  ZeroHom Nat R

/--
Instance `ArithmeticFunction.zero` / 实例 `ArithmeticFunction.zero`

English:
instance ArithmeticFunction.zero
  signature: [Zero R]
  body: inferInstanceAs (Zero (ZeroHom Nat R))

中文:
实例 ArithmeticFunction.zero
  签名: [零 R]
  定义体: inferInstanceAs (Zero (ZeroHom Nat R))

Depends on / 依赖: ZeroHom
-/
instance ArithmeticFunction.zero [Zero R] : Zero (ArithmeticFunction R) :=
  inferInstanceAs (Zero (ZeroHom Nat R))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] : Inhabited (ArithmeticFunction R)
  body: inferInstanceAs (Inhabited (ZeroHom Nat R))

中文:
实例 [零
  签名: R] : 可居 (ArithmeticFunction R)
  定义体: inferInstanceAs (Inhabited (ZeroHom Nat R))

Depends on / 依赖: Inhabited, ZeroHom
-/
instance [Zero R] : Inhabited (ArithmeticFunction R) := inferInstanceAs (Inhabited (ZeroHom Nat R))

variable {R}

namespace ArithmeticFunction

section Zero

variable [Zero R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (ArithmeticFunction R) Nat R
  body: inferInstanceAs (FunLike (ZeroHom Nat R) Nat R)

@[simp]

中文:
实例 :
  签名: 函数状 (ArithmeticFunction R) 自然数 R
  定义体: inferInstanceAs (FunLike (ZeroHom Nat R) Nat R)

@[simp]

Depends on / 依赖: FunLike, ZeroHom
-/
instance : FunLike (ArithmeticFunction R) Nat R :=
  inferInstanceAs (FunLike (ZeroHom Nat R) Nat R)

@[simp]
/--
theorem `toFun_eq` / 定理 `toFun_eq`

English:
theorem toFun_eq
  given: (f : ArithmeticFunction R)
  statement: f.toFun = f
  proof: rfl

@[simp]

中文:
定理 toFun_eq
  条件: (f : ArithmeticFunction R)
  结论: f.toFun = f
  证明: rfl

@[simp]
-/
theorem toFun_eq (f : ArithmeticFunction R) : f.toFun = f := rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : Nat -> R) (hf)
  statement: @DFunLike.coe (ArithmeticFunction R) _ _ _
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (f : 自然数 -> R) (hf)
  结论: @依赖函数状.coe (ArithmeticFunction R) _ _ _
  证明: rfl

@[simp]
-/
theorem coe_mk (f : Nat -> R) (hf) : @DFunLike.coe (ArithmeticFunction R) _ _ _
    (ZeroHom.mk f hf) = f := rfl

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: {f : ArithmeticFunction R}
  statement: f 0 = 0
  proof: ZeroHom.map_zero' f

中文:
定理 map_zero
  条件: {f : ArithmeticFunction R}
  结论: f 0 = 0
  证明: ZeroHom.map_zero' f

Depends on / 依赖: ZeroHom, ZeroHom.map_zero, map_zero
-/
theorem map_zero {f : ArithmeticFunction R} : f 0 = 0 :=
  ZeroHom.map_zero' f

/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {f g : ArithmeticFunction R}
  statement: (f : Nat -> R) = g ↔ f = g
  proof: DFunLike.coe_fn_eq

中文:
定理 coe_inj
  条件: {f g : ArithmeticFunction R}
  结论: (f : 自然数 -> R) = g ↔ f = g
  证明: DFunLike.coe_fn_eq

Depends on / 依赖: DFunLike, DFunLike.coe_fn_eq, coe_fn_eq
-/
theorem coe_inj {f g : ArithmeticFunction R} : (f : Nat -> R) = g ↔ f = g :=
  DFunLike.coe_fn_eq

/--
theorem `range_coe` / 定理 `range_coe`

English:
theorem range_coe
  statement: Set.range ((↑) : ArithmeticFunction R -> (Nat -> R)) = {f | f 0 = 0}
  proof: by
  ext f
  exact ⟨by rintro ⟨f, rfl⟩; simp, fun hf => ⟨⟨f, hf⟩, rfl⟩⟩

@[simp]

中文:
定理 range_coe
  结论: 集合.range ((↑) : ArithmeticFunction R -> (自然数 -> R)) = {f | f 0 = 0}
  证明: by
  ext f
  exact ⟨by rintro ⟨f, rfl⟩; simp, fun hf => ⟨⟨f, hf⟩, rfl⟩⟩

@[simp]
-/
theorem range_coe : Set.range ((↑) : ArithmeticFunction R -> (Nat -> R)) = {f | f 0 = 0} := by
  ext f
  exact ⟨by rintro ⟨f, rfl⟩; simp, fun hf => ⟨⟨f, hf⟩, rfl⟩⟩

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: {x : Nat}
  statement: (0 : ArithmeticFunction R) x = 0
  proof: rfl

@[ext]

中文:
定理 zero_apply
  条件: {x : 自然数}
  结论: (0 : ArithmeticFunction R) x = 0
  证明: rfl

@[ext]
-/
theorem zero_apply {x : Nat} : (0 : ArithmeticFunction R) x = 0 :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: ArithmeticFunction R⦄ (h : forall x, f x = g x) : f = g
  proof: ZeroHom.ext h

中文:
定理 ext
  条件: ⦃f g
  结论: ArithmeticFunction R⦄ (h : 对任意 x, f x = g x) : f = g
  证明: ZeroHom.ext h

Depends on / 依赖: ZeroHom, ZeroHom.ext
-/
theorem ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, f x = g x) : f = g :=
  ZeroHom.ext h

section One

variable [One R]

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One (ArithmeticFunction R)
  body: ⟨⟨fun x => ite (x = 1) 1 0, rfl⟩⟩

中文:
实例 one
  签名: : 幺 (ArithmeticFunction R)
  定义体: ⟨⟨fun x => ite (x = 1) 1 0, rfl⟩⟩
-/
instance one : One (ArithmeticFunction R) :=
  ⟨⟨fun x => ite (x = 1) 1 0, rfl⟩⟩

/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: {x : Nat}
  statement: (1 : ArithmeticFunction R) x = ite (x = 1) 1 0
  proof: rfl

@[simp]

中文:
定理 one_apply
  条件: {x : 自然数}
  结论: (1 : ArithmeticFunction R) x = ite (x = 1) 1 0
  证明: rfl

@[simp]
-/
theorem one_apply {x : Nat} : (1 : ArithmeticFunction R) x = ite (x = 1) 1 0 :=
  rfl

@[simp]
/--
theorem `one_one` / 定理 `one_one`

English:
theorem one_one
  statement: (1 : ArithmeticFunction R) 1 = 1
  proof: rfl

@[simp]

中文:
定理 one_one
  结论: (1 : ArithmeticFunction R) 1 = 1
  证明: rfl

@[simp]
-/
theorem one_one : (1 : ArithmeticFunction R) 1 = 1 :=
  rfl

@[simp]
/--
theorem `one_apply_ne` / 定理 `one_apply_ne`

English:
theorem one_apply_ne
  given: {x : Nat} (h : x != 1)
  statement: (1 : ArithmeticFunction R) x = 0
  proof: if_neg h

中文:
定理 one_apply_ne
  条件: {x : 自然数} (h : x != 1)
  结论: (1 : ArithmeticFunction R) x = 0
  证明: if_neg h

Depends on / 依赖: if_neg
-/
theorem one_apply_ne {x : Nat} (h : x != 1) : (1 : ArithmeticFunction R) x = 0 :=
  if_neg h

end One

end Zero

/-- Coerce an arithmetic function with values in `ℕ` to one with values in `R`. We cannot inline
this in `natCoe` because it gets unfolded too much. -/
@[coe]
/--
Definition of `natToArithmeticFunction` / `natToArithmeticFunction` 的定义

English:
definition natToArithmeticFunction
  signature: [AddMonoidWithOne R]
  body: fun f => ⟨fun n => ↑(f n), by simp⟩

中文:
定义 natToArithmeticFunction
  签名: [加法带幺幺半群 R]
  定义体: fun f => ⟨fun n => ↑(f n), by simp⟩
-/
def natToArithmeticFunction [AddMonoidWithOne R] :
    (ArithmeticFunction Nat) -> (ArithmeticFunction R) :=
  fun f => ⟨fun n => ↑(f n), by simp⟩

/--
Instance `natCoe` / 实例 `natCoe`

English:
instance natCoe
  signature: [AddMonoidWithOne R]
  body: ⟨natToArithmeticFunction⟩

@[simp]

中文:
实例 natCoe
  签名: [加法带幺幺半群 R]
  定义体: ⟨natToArithmeticFunction⟩

@[simp]

Depends on / 依赖: natToArithmeticFunction
-/
instance natCoe [AddMonoidWithOne R] : Coe (ArithmeticFunction Nat) (ArithmeticFunction R) :=
  ⟨natToArithmeticFunction⟩

@[simp]
/--
theorem `natCoe_nat` / 定理 `natCoe_nat`

English:
theorem natCoe_nat
  given: (f : ArithmeticFunction Nat)
  statement: natToArithmeticFunction f = f
  proof: ext fun _ => cast_id _

@[simp]

中文:
定理 natCoe_nat
  条件: (f : ArithmeticFunction 自然数)
  结论: natToArithmeticFunction f = f
  证明: ext fun _ => cast_id _

@[simp]

Depends on / 依赖: cast_id
-/
theorem natCoe_nat (f : ArithmeticFunction Nat) : natToArithmeticFunction f = f :=
  ext fun _ => cast_id _

@[simp]
/--
theorem `natCoe_apply` / 定理 `natCoe_apply`

English:
theorem natCoe_apply
  given: [AddMonoidWithOne R] {f : ArithmeticFunction Nat} {x : Nat}
  proof: rfl

中文:
定理 natCoe_apply
  条件: [加法带幺幺半群 R] {f : ArithmeticFunction 自然数} {x : 自然数}
  证明: rfl
-/
theorem natCoe_apply [AddMonoidWithOne R] {f : ArithmeticFunction Nat} {x : Nat} :
    (f : ArithmeticFunction R) x = f x :=
  rfl

/-- Coerce an arithmetic function with values in `ℤ` to one with values in `R`. We cannot inline
this in `intCoe` because it gets unfolded too much. -/
@[coe]
/--
Definition of `ofInt` / `ofInt` 的定义

English:
definition ofInt
  signature: [AddGroupWithOne R]
  body: fun f => ⟨fun n => ↑(f n), by simp⟩

中文:
定义 of整数
  签名: [加法带幺群 R]
  定义体: fun f => ⟨fun n => ↑(f n), by simp⟩
-/
def ofInt [AddGroupWithOne R] :
    (ArithmeticFunction Int) -> (ArithmeticFunction R) :=
  fun f => ⟨fun n => ↑(f n), by simp⟩

/--
Instance `intCoe` / 实例 `intCoe`

English:
instance intCoe
  signature: [AddGroupWithOne R]
  body: ⟨ofInt⟩

@[simp]

中文:
实例 intCoe
  签名: [加法带幺群 R]
  定义体: ⟨ofInt⟩

@[simp]
-/
instance intCoe [AddGroupWithOne R] : Coe (ArithmeticFunction Int) (ArithmeticFunction R) :=
  ⟨ofInt⟩

@[simp]
/--
theorem `intCoe_int` / 定理 `intCoe_int`

English:
theorem intCoe_int
  given: (f : ArithmeticFunction Int)
  statement: ofInt f = f
  proof: ext fun _ => Int.cast_id

@[simp]

中文:
定理 intCoe_int
  条件: (f : ArithmeticFunction 整数)
  结论: of整数 f = f
  证明: ext fun _ => Int.cast_id

@[simp]

Depends on / 依赖: Int.cast_id, cast_id
-/
theorem intCoe_int (f : ArithmeticFunction Int) : ofInt f = f :=
  ext fun _ => Int.cast_id

@[simp]
/--
theorem `intCoe_apply` / 定理 `intCoe_apply`

English:
theorem intCoe_apply
  given: [AddGroupWithOne R] {f : ArithmeticFunction Int} {x : Nat}
  proof: rfl

@[simp]

中文:
定理 intCoe_apply
  条件: [加法带幺群 R] {f : ArithmeticFunction 整数} {x : 自然数}
  证明: rfl

@[simp]
-/
theorem intCoe_apply [AddGroupWithOne R] {f : ArithmeticFunction Int} {x : Nat} :
    (f : ArithmeticFunction R) x = f x := rfl

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: [AddGroupWithOne R] {f : ArithmeticFunction Nat}
  proof: by
  ext
  simp

@[simp]

中文:
定理 coe_coe
  条件: [加法带幺群 R] {f : ArithmeticFunction 自然数}
  证明: by
  ext
  simp

@[simp]
-/
theorem coe_coe [AddGroupWithOne R] {f : ArithmeticFunction Nat} :
    ((f : ArithmeticFunction Int) : ArithmeticFunction R) = (f : ArithmeticFunction R) := by
  ext
  simp

@[simp]
/--
theorem `natCoe_one` / 定理 `natCoe_one`

English:
theorem natCoe_one
  given: [AddMonoidWithOne R]
  proof: by
  ext n
  simp [one_apply]

@[simp]

中文:
定理 natCoe_one
  条件: [加法带幺幺半群 R]
  证明: by
  ext n
  simp [one_apply]

@[simp]

Depends on / 依赖: one_apply
-/
theorem natCoe_one [AddMonoidWithOne R] :
    ((1 : ArithmeticFunction Nat) : ArithmeticFunction R) = 1 := by
  ext n
  simp [one_apply]

@[simp]
/--
theorem `intCoe_one` / 定理 `intCoe_one`

English:
theorem intCoe_one
  given: [AddGroupWithOne R]
  statement: ((1 : ArithmeticFunction Int) :
  proof: by
  ext n
  simp [one_apply]

中文:
定理 intCoe_one
  条件: [加法带幺群 R]
  结论: ((1 : ArithmeticFunction 整数) :
  证明: by
  ext n
  simp [one_apply]

Depends on / 依赖: one_apply
-/
theorem intCoe_one [AddGroupWithOne R] : ((1 : ArithmeticFunction Int) :
    ArithmeticFunction R) = 1 := by
  ext n
  simp [one_apply]

section AddMonoid

variable [AddMonoid R]

/--
Instance `add` / 实例 `add`

English:
instance add
  signature: : Add (ArithmeticFunction R) where
  body: ⟨f + g, by simp⟩

@[simp]

中文:
实例 add
  签名: : 加法 (ArithmeticFunction R) where
  定义体: ⟨f + g, by simp⟩

@[simp]
-/
instance add : Add (ArithmeticFunction R) where
  add f g := ⟨f + g, by simp⟩

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: {f g : ArithmeticFunction R} {n : Nat}
  statement: (f + g) n = f n + g n
  proof: rfl

中文:
定理 add_apply
  条件: {f g : ArithmeticFunction R} {n : 自然数}
  结论: (f + g) n = f n + g n
  证明: rfl
-/
theorem add_apply {f g : ArithmeticFunction R} {n : Nat} : (f + g) n = f n + g n :=
  rfl

/--
Instance `instAddMonoid` / 实例 `instAddMonoid`

English:
instance instAddMonoid
  signature: : AddMonoid (ArithmeticFunction R) where
  body: ext fun _ => add_assoc _ _ _
  zero_add _ := ext fun _ => zero_add _
  add_zero _ := ext fun _ => add_zero _
  nsmul := nsmulRec

中文:
实例 instAddMonoid
  签名: : 加法幺半群 (ArithmeticFunction R) where
  定义体: ext fun _ => add_assoc _ _ _
  zero_add _ := ext fun _ => zero_add _
  add_zero _ := ext fun _ => add_zero _
  nsmul := nsmulRec

Depends on / 依赖: add_assoc
-/
instance instAddMonoid : AddMonoid (ArithmeticFunction R) where
  add_assoc _ _ _ := ext fun _ => add_assoc _ _ _
  zero_add _ := ext fun _ => zero_add _
  add_zero _ := ext fun _ => add_zero _
  nsmul := nsmulRec

end AddMonoid

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instAddMonoidWithOne` / 实例 `instAddMonoidWithOne`

English:
instance instAddMonoidWithOne
  signature: [AddMonoidWithOne R]
  body: ⟨fun x => if x = 1 then (n : R) else 0, by simp⟩
  natCast_zero := by ext; simp
  natCast_succ n := by ext x; by_cases h : x = 1 <;> simp [h]

中文:
实例 instAddMonoidWithOne
  签名: [加法带幺幺半群 R]
  定义体: ⟨fun x => if x = 1 then (n : R) else 0, by simp⟩
  natCast_zero := by ext; simp
  natCast_succ n := by ext x; by_cases h : x = 1 <;> simp [h]
-/
instance instAddMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne (ArithmeticFunction R) where
  natCast n := ⟨fun x => if x = 1 then (n : R) else 0, by simp⟩
  natCast_zero := by ext; simp
  natCast_succ n := by ext x; by_cases h : x = 1 <;> simp [h]

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: [AddCommMonoid R]
  body: ext fun _ => add_comm _ _

中文:
实例 instAddCommMonoid
  签名: [加法交换幺半群 R]
  定义体: ext fun _ => add_comm _ _

Depends on / 依赖: add_comm
-/
instance instAddCommMonoid [AddCommMonoid R] : AddCommMonoid (ArithmeticFunction R) where
  add_comm _ _ := ext fun _ => add_comm _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NegZeroClass
  signature: R] : Neg (ArithmeticFunction R) where
  body: ⟨-f, by simp⟩

@[simp]

中文:
实例 [NegZero类
  签名: R] : 取负 (ArithmeticFunction R) where
  定义体: ⟨-f, by simp⟩

@[simp]
-/
instance [NegZeroClass R] : Neg (ArithmeticFunction R) where
  neg f := ⟨-f, by simp⟩

@[simp]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: [NegZeroClass R] {f : ArithmeticFunction R} {n : Nat}
  statement: (-f) n = -f n
  proof: by
  rfl

中文:
定理 neg_apply
  条件: [NegZero类 R] {f : ArithmeticFunction R} {n : 自然数}
  结论: (-f) n = -f n
  证明: by
  rfl
-/
theorem neg_apply [NegZeroClass R] {f : ArithmeticFunction R} {n : Nat} : (-f) n = -f n := by
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: R] : AddGroup (ArithmeticFunction R) where
  body: ext fun _ => neg_add_cancel _
  zsmul := zsmulRec

中文:
实例 [加法群
  签名: R] : 加法群 (ArithmeticFunction R) where
  定义体: ext fun _ => neg_add_cancel _
  zsmul := zsmulRec

Depends on / 依赖: neg_add_cancel
-/
instance [AddGroup R] : AddGroup (ArithmeticFunction R) where
  neg_add_cancel _ := ext fun _ => neg_add_cancel _
  zsmul := zsmulRec

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: R] : AddCommGroup (ArithmeticFunction R) where
  body: fun _ _ => add_comm _ _

中文:
实例 [加法交换群
  签名: R] : 加法交换群 (ArithmeticFunction R) where
  定义体: fun _ _ => add_comm _ _

Depends on / 依赖: add_comm
-/
instance [AddCommGroup R] : AddCommGroup (ArithmeticFunction R) where
  add_comm := fun _ _ => add_comm _ _

section SMul

variable {M : Type*} [Zero R] [AddCommMonoid M] [SMul R M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (ArithmeticFunction R) (ArithmeticFunction M)
  body: ⟨fun n => ∑ x in divisorsAntidiagonal n, f x.fst • g x.snd, by simp⟩

@[simp]

中文:
实例 :
  签名: 标量乘法 (ArithmeticFunction R) (ArithmeticFunction M)
  定义体: ⟨fun n => ∑ x in divisorsAntidiagonal n, f x.fst • g x.snd, by simp⟩

@[simp]

Depends on / 依赖: divisorsAntidiagonal, x.fst, x.snd
-/
instance : SMul (ArithmeticFunction R) (ArithmeticFunction M) where
  smul f g := ⟨fun n => ∑ x in divisorsAntidiagonal n, f x.fst • g x.snd, by simp⟩

@[simp]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: {f : ArithmeticFunction R} {g : ArithmeticFunction M} {n : Nat}
  proof: rfl

中文:
定理 smul_apply
  条件: {f : ArithmeticFunction R} {g : ArithmeticFunction M} {n : 自然数}
  证明: rfl
-/
theorem smul_apply {f : ArithmeticFunction R} {g : ArithmeticFunction M} {n : Nat} :
    (f • g) n = ∑ x in divisorsAntidiagonal n, f x.fst • g x.snd :=
  rfl

end SMul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] : Mul (ArithmeticFunction R) where
  body: f • g

@[simp]

中文:
实例 [半环
  签名: R] : 乘法 (ArithmeticFunction R) where
  定义体: f • g

@[simp]
-/
instance [Semiring R] : Mul (ArithmeticFunction R) where
  mul f g := f • g

@[simp]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: [Semiring R] {f g : ArithmeticFunction R} {n : Nat}
  proof: rfl

中文:
定理 mul_apply
  条件: [半环 R] {f g : ArithmeticFunction R} {n : 自然数}
  证明: rfl
-/
theorem mul_apply [Semiring R] {f g : ArithmeticFunction R} {n : Nat} :
    (f * g) n = ∑ x in divisorsAntidiagonal n, f x.fst * g x.snd :=
  rfl

/--
theorem `mul_apply_one` / 定理 `mul_apply_one`

English:
theorem mul_apply_one
  given: [Semiring R] {f g : ArithmeticFunction R}
  statement: (f * g) 1 = f 1 * g 1
  proof: by simp

@[simp, norm_cast]

中文:
定理 mul_apply_one
  条件: [半环 R] {f g : ArithmeticFunction R}
  结论: (f * g) 1 = f 1 * g 1
  证明: by simp

@[simp, norm_cast]
-/
theorem mul_apply_one [Semiring R] {f g : ArithmeticFunction R} : (f * g) 1 = f 1 * g 1 := by simp

@[simp, norm_cast]
/--
theorem `natCoe_mul` / 定理 `natCoe_mul`

English:
theorem natCoe_mul
  given: [Semiring R] {f g : ArithmeticFunction Nat}
  proof: by
  ext n
  simp

@[simp, norm_cast]

中文:
定理 natCoe_mul
  条件: [半环 R] {f g : ArithmeticFunction 自然数}
  证明: by
  ext n
  simp

@[simp, norm_cast]
-/
theorem natCoe_mul [Semiring R] {f g : ArithmeticFunction Nat} :
    (↑(f * g) : ArithmeticFunction R) = f * g := by
  ext n
  simp

@[simp, norm_cast]
/--
theorem `intCoe_mul` / 定理 `intCoe_mul`

English:
theorem intCoe_mul
  given: [Ring R] {f g : ArithmeticFunction Int}
  proof: by
  ext n
  simp

中文:
定理 intCoe_mul
  条件: [环 R] {f g : ArithmeticFunction 整数}
  证明: by
  ext n
  simp
-/
theorem intCoe_mul [Ring R] {f g : ArithmeticFunction Int} :
    (↑(f * g) : ArithmeticFunction R) = ↑f * g := by
  ext n
  simp

section Module

variable {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/--
theorem `mul_smul'` / 定理 `mul_smul'`

English:
theorem mul_smul'
  given: (f g : ArithmeticFunction R) (h : ArithmeticFunction M)
  proof: by
  ext n
  simp only [mul_apply, smul_apply, sum_smul, mul_smul, smul_sum, sum_sigma']
  apply sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ => ⟨(k, l * j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ => ⟨(i * k, l), (i, k)⟩) <;> aesop (add simp mul_assoc)

中文:
定理 mul_smul'
  条件: (f g : ArithmeticFunction R) (h : ArithmeticFunction M)
  证明: by
  ext n
  simp only [mul_apply, smul_apply, sum_smul, mul_smul, smul_sum, sum_sigma']
  apply sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ => ⟨(k, l * j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ => ⟨(i * k, l), (i, k)⟩) <;> aesop (add simp mul_assoc)

Depends on / 依赖: mul_apply, mul_assoc, mul_smul, smul_apply, smul_sum, sum_nbij, sum_sigma, sum_smul
-/
theorem mul_smul' (f g : ArithmeticFunction R) (h : ArithmeticFunction M) :
    (f * g) • h = f • g • h := by
  ext n
  simp only [mul_apply, smul_apply, sum_smul, mul_smul, smul_sum, sum_sigma']
  apply sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ => ⟨(k, l * j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ => ⟨(i * k, l), (i, k)⟩) <;> aesop (add simp mul_assoc)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `one_smul'` / 定理 `one_smul'`

English:
theorem one_smul'
  given: (b : ArithmeticFunction M)
  statement: (1 : ArithmeticFunction R) • b = b
  proof: by
  ext x
  simp_all [← map_div_right_divisors, sum_eq_single 1]

中文:
定理 one_smul'
  条件: (b : ArithmeticFunction M)
  结论: (1 : ArithmeticFunction R) • b = b
  证明: by
  ext x
  simp_all [← map_div_right_divisors, sum_eq_single 1]

Depends on / 依赖: map_div_right_divisors, sum_eq_single
-/
theorem one_smul' (b : ArithmeticFunction M) : (1 : ArithmeticFunction R) • b = b := by
  ext x
  simp_all [← map_div_right_divisors, sum_eq_single 1]

end Module

section Semiring

variable [Semiring R]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid (ArithmeticFunction R) where
  body: one_smul'
  mul_one f := by
    ext x
    simp_all [← map_div_left_divisors, sum_eq_single 1]
  mul_assoc := mul_smul'

中文:
实例 instMonoid
  签名: : 幺半群 (ArithmeticFunction R) where
  定义体: one_smul'
  mul_one f := by
    ext x
    simp_all [← map_div_left_divisors, sum_eq_single 1]
  mul_assoc := mul_smul'

Depends on / 依赖: one_smul
-/
instance instMonoid : Monoid (ArithmeticFunction R) where
  one_mul := one_smul'
  mul_one f := by
    ext x
    simp_all [← map_div_left_divisors, sum_eq_single 1]
  mul_assoc := mul_smul'

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: : Semiring (ArithmeticFunction R) where
  body: by ext; simp
  mul_zero f := by ext; simp
  left_distrib a b c := by ext; simp [← sum_add_distrib, mul_add]
  right_distrib a b c := by ext; simp [← sum_add_distrib, add_mul]

中文:
实例 instSemiring
  签名: : 半环 (ArithmeticFunction R) where
  定义体: by ext; simp
  mul_zero f := by ext; simp
  left_distrib a b c := by ext; simp [← sum_add_distrib, mul_add]
  right_distrib a b c := by ext; simp [← sum_add_distrib, add_mul]

Depends on / 依赖: add_mul, left_distrib, mul_add, mul_zero, right_distrib, sum_add_distrib
-/
instance instSemiring : Semiring (ArithmeticFunction R) where
  zero_mul f := by ext; simp
  mul_zero f := by ext; simp
  left_distrib a b c := by ext; simp [← sum_add_distrib, mul_add]
  right_distrib a b c := by ext; simp [← sum_add_distrib, add_mul]

end Semiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: R] : CommSemiring (ArithmeticFunction R) where
  body: by
    ext
    rw [mul_apply]; rw [← map_swap_divisorsAntidiagonal]; rw [sum_map]
    simp [mul_comm]

中文:
实例 [交换半环
  签名: R] : 交换半环 (ArithmeticFunction R) where
  定义体: by
    ext
    rw [mul_apply]; rw [← map_swap_divisorsAntidiagonal]; rw [sum_map]
    simp [mul_comm]

Depends on / 依赖: map_swap_divisorsAntidiagonal, mul_apply, mul_comm, sum_map
-/
instance [CommSemiring R] : CommSemiring (ArithmeticFunction R) where
  mul_comm f g := by
    ext
    rw [mul_apply]; rw [← map_swap_divisorsAntidiagonal]; rw [sum_map]
    simp [mul_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: R] : CommRing (ArithmeticFunction R) where
  body: neg_add_cancel
  mul_comm := mul_comm

中文:
实例 [交换环
  签名: R] : 交换环 (ArithmeticFunction R) where
  定义体: neg_add_cancel
  mul_comm := mul_comm

Depends on / 依赖: neg_add_cancel
-/
instance [CommRing R] : CommRing (ArithmeticFunction R) where
  neg_add_cancel := neg_add_cancel
  mul_comm := mul_comm

instance {S : Type*} [Semiring R] [AddCommMonoid S] [Module R S] :
    Module R (ArithmeticFunction S) where
  smul x f := ⟨x • f, by simp⟩
  smul_zero x := ext fun n => smul_zero x
  smul_add x f g := ext fun n => smul_add x (f n) (g n)
  zero_smul f := ext fun n => zero_smul R (f n)
  one_smul f := ext fun n => one_smul R (f n)
  add_smul x y f := ext fun n => add_smul x y (f n)
  mul_smul x y f := ext fun n => mul_smul x y (f n)

-- note that `smul_apply` would be a more suitable name, but is already in use for the action of
-- `ArithmeticFunction R` on `ArithmeticFunction S`
@[simp]
/--
theorem `smul_map` / 定理 `smul_map`

English:
theorem smul_map
  statement: {S : Type*} [Semiring R] [AddCommMonoid S] [Module R S]
  proof: by
  rfl

中文:
定理 smul_map
  结论: {S : 类型} [半环 R] [加法交换幺半群 S] [模 R S]
  证明: by
  rfl
-/
theorem smul_map {S : Type*} [Semiring R] [AddCommMonoid S] [Module R S]
    (x : R) (f : ArithmeticFunction S) (n : Nat) : (x • f) n = x • f n := by
  rfl

-- We can deduce the `Algebra` structure from the `Module` structure here due to the lack of
-- a more natural definition of `algebraMap`.
instance {S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] :
    Algebra R (ArithmeticFunction S) :=
  .ofModule (fun x f g => ext fun n => by simp [Finset.smul_sum])
    fun x f g => ext fun n => by simp [Finset.smul_sum]

@[simp]
/--
theorem `algebraMap_apply_one` / 定理 `algebraMap_apply_one`

English:
theorem algebraMap_apply_one
  given: {S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] (x : R)
  proof: by
  simp [Algebra.algebraMap_eq_smul_one]

中文:
定理 algebraMap_apply_one
  条件: {S : 类型} [交换半环 R] [半环 S] [代数 R S] (x : R)
  证明: by
  simp [Algebra.algebraMap_eq_smul_one]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one
-/
theorem algebraMap_apply_one {S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] (x : R) :
    algebraMap R (ArithmeticFunction S) x 1 = algebraMap R S x := by
  simp [Algebra.algebraMap_eq_smul_one]

instance {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] :
    Module (ArithmeticFunction R) (ArithmeticFunction M) where
  one_smul := one_smul'
  mul_smul := mul_smul'
  smul_add r x y := by
    ext
    simp only [sum_add_distrib, smul_add, smul_apply, add_apply]
  smul_zero r := by
    ext
    simp only [smul_apply, sum_const_zero, smul_zero, zero_apply]
  add_smul r s x := by
    ext
    simp only [add_smul, sum_add_distrib, smul_apply, add_apply]
  zero_smul r := by
    ext
    simp only [smul_apply, sum_const_zero, zero_smul, zero_apply]

section DirichletInverse

section Ring

/- We use `(hf : Invertible (f 1))` instead of `[hf : Invertible (f 1)]` because in practice such
an instance is unlikely to be automatically synthesized due to the presence of `f`. -/
variable [Ring R] (f : Nat -> R) (hf : Invertible (f 1))

/--
Definition of `dirichletInverseFun` / `dirichletInverseFun` 的定义

English:
definition dirichletInverseFun
  signature: (n : Nat)
  body: if n = 0 then 0
  else if n = 1 then ⅟(f 1)
  else - ⅟(f 1) * ∑ d : n.properDivisors,
    have : d < n := (Nat.mem_properDivisors.mp d.2).2
    f (n / d) * dirichletInverseFun d

@[simp]

中文:
定义 dirichletInverseFun
  签名: (n : 自然数)
  定义体: if n = 0 then 0
  else if n = 1 then ⅟(f 1)
  else - ⅟(f 1) * ∑ d : n.properDivisors,
    have : d < n := (Nat.mem_properDivisors.mp d.2).2
    f (n / d) * dirichletInverseFun d

@[simp]

Depends on / 依赖: Nat.mem_properDivisors.mp, dirichletInverseFun, mem_properDivisors, n.properDivisors, properDivisors
-/
def dirichletInverseFun (n : Nat) : R :=
  if n = 0 then 0
  else if n = 1 then ⅟(f 1)
  else - ⅟(f 1) * ∑ d : n.properDivisors,
    have : d < n := (Nat.mem_properDivisors.mp d.2).2
    f (n / d) * dirichletInverseFun d

@[simp]
/--
theorem `dirichletInverseFun_apply_zero` / 定理 `dirichletInverseFun_apply_zero`

English:
theorem dirichletInverseFun_apply_zero
  statement: dirichletInverseFun f hf 0 = 0
  proof: by
  rw [dirichletInverseFun]; rw [if_pos rfl]

@[simp]

中文:
定理 dirichletInverseFun_apply_zero
  结论: dirichletInverseFun f hf 0 = 0
  证明: by
  rw [dirichletInverseFun]; rw [if_pos rfl]

@[simp]

Depends on / 依赖: dirichletInverseFun, if_pos
-/
theorem dirichletInverseFun_apply_zero : dirichletInverseFun f hf 0 = 0 := by
  rw [dirichletInverseFun]; rw [if_pos rfl]

@[simp]
/--
theorem `dirichletInverseFun_apply_one` / 定理 `dirichletInverseFun_apply_one`

English:
theorem dirichletInverseFun_apply_one
  statement: dirichletInverseFun f hf 1 = ⅟(f 1)
  proof: by
  rw [dirichletInverseFun]; rw [if_neg one_ne_zero]; rw [if_pos rfl]

@[simp]

中文:
定理 dirichletInverseFun_apply_one
  结论: dirichletInverseFun f hf 1 = ⅟(f 1)
  证明: by
  rw [dirichletInverseFun]; rw [if_neg one_ne_zero]; rw [if_pos rfl]

@[simp]

Depends on / 依赖: dirichletInverseFun, if_neg, if_pos, one_ne_zero
-/
theorem dirichletInverseFun_apply_one : dirichletInverseFun f hf 1 = ⅟(f 1) := by
  rw [dirichletInverseFun]; rw [if_neg one_ne_zero]; rw [if_pos rfl]

@[simp]
/--
theorem `dirichletInverseFun_apply_ne` / 定理 `dirichletInverseFun_apply_ne`

English:
theorem dirichletInverseFun_apply_ne
  given: {n : Nat} (hn0 : n != 0) (hn1 : n != 1)
  proof: by
  rw [dirichletInverseFun]; rw [if_neg hn0]; rw [if_neg hn1]
  conv_rhs => rw [← Finset.sum_attach, Finset.attach_eq_univ]

中文:
定理 dirichletInverseFun_apply_ne
  条件: {n : 自然数} (hn0 : n != 0) (hn1 : n != 1)
  证明: by
  rw [dirichletInverseFun]; rw [if_neg hn0]; rw [if_neg hn1]
  conv_rhs => rw [← Finset.sum_attach, Finset.attach_eq_univ]

Depends on / 依赖: Finset, Finset.attach_eq_univ, Finset.sum_attach, attach_eq_univ, conv_rhs, dirichletInverseFun, if_neg, sum_attach
-/
theorem dirichletInverseFun_apply_ne {n : Nat} (hn0 : n != 0) (hn1 : n != 1) :
    dirichletInverseFun f hf n =
      - ⅟(f 1) * ∑ d in n.properDivisors, f (n / d) * dirichletInverseFun f hf d := by
  rw [dirichletInverseFun]; rw [if_neg hn0]; rw [if_neg hn1]
  conv_rhs => rw [← Finset.sum_attach, Finset.attach_eq_univ]

/-- Given an inverse of `f 1`, construct the Dirichlet inverse of `f`. -/
@[simp]
/--
Definition of `dirichletInverse` / `dirichletInverse` 的定义

English:
definition dirichletInverse
  signature: : ArithmeticFunction R
  body: ⟨dirichletInverseFun f hf, dirichletInverseFun_apply_zero f hf⟩

中文:
定义 dirichletInverse
  签名: : ArithmeticFunction R
  定义体: ⟨dirichletInverseFun f hf, dirichletInverseFun_apply_zero f hf⟩

Depends on / 依赖: dirichletInverseFun, dirichletInverseFun_apply_zero
-/
def dirichletInverse : ArithmeticFunction R :=
  ⟨dirichletInverseFun f hf, dirichletInverseFun_apply_zero f hf⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `self_mul_dirichletInverse` / 定理 `self_mul_dirichletInverse`

English:
theorem self_mul_dirichletInverse
  given: (f : ArithmeticFunction R) (hf : Invertible (f 1))
  proof: by
  ext n
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · simp [hn1]
  rw [dirichletInverse]; rw [mul_apply]; rw [coe_mk]; rw [Nat.sum_divisorsAntidiagonal' fun x y => f x * dirichletInverseFun f hf y]; rw [← Nat.cons_self_properDivisors hn0]
  simp [hn0, hn1, pos_of_ne_zero]

中文:
定理 self_mul_dirichletInverse
  条件: (f : ArithmeticFunction R) (hf : 可逆 (f 1))
  证明: by
  ext n
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · simp [hn1]
  rw [dirichletInverse]; rw [mul_apply]; rw [coe_mk]; rw [Nat.sum_divisorsAntidiagonal' fun x y => f x * dirichletInverseFun f hf y]; rw [← Nat.cons_self_properDivisors hn0]
  simp [hn0, hn1, pos_of_ne_zero]

Depends on / 依赖: Nat.cons_self_properDivisors, Nat.sum_divisorsAntidiagonal, coe_mk, cons_self_properDivisors, dirichletInverse, dirichletInverseFun, mul_apply, pos_of_ne_zero, sum_divisorsAntidiagonal
-/
theorem self_mul_dirichletInverse (f : ArithmeticFunction R) (hf : Invertible (f 1)) :
    f * dirichletInverse f hf = 1 := by
  ext n
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · simp [hn1]
  rw [dirichletInverse]; rw [mul_apply]; rw [coe_mk]; rw [Nat.sum_divisorsAntidiagonal' fun x y => f x * dirichletInverseFun f hf y]; rw [← Nat.cons_self_properDivisors hn0]
  simp [hn0, hn1, pos_of_ne_zero]

end Ring

section CommRing

variable [CommRing R] (f : ArithmeticFunction R)

/--
theorem `dirichletInverse_mul_self` / 定理 `dirichletInverse_mul_self`

English:
theorem dirichletInverse_mul_self
  given: (hf : Invertible (f 1))
  statement: dirichletInverse f hf * f = 1
  proof: by
  rw [mul_comm]; rw [self_mul_dirichletInverse]

中文:
定理 dirichletInverse_mul_self
  条件: (hf : 可逆 (f 1))
  结论: dirichletInverse f hf * f = 1
  证明: by
  rw [mul_comm]; rw [self_mul_dirichletInverse]

Depends on / 依赖: mul_comm, self_mul_dirichletInverse
-/
theorem dirichletInverse_mul_self (hf : Invertible (f 1)) : dirichletInverse f hf * f = 1 := by
  rw [mul_comm]; rw [self_mul_dirichletInverse]

variable {f} in
/--
theorem `isUnit_iff_isUnit_apply_one` / 定理 `isUnit_iff_isUnit_apply_one`

English:
theorem isUnit_iff_isUnit_apply_one
  statement: IsUnit f ↔ IsUnit (f 1)
  proof: by
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨⟨f.val 1, f⁻¹.val 1, ?_, ?_⟩, rfl⟩
    · rw [← ArithmeticFunction.mul_apply_one, Units.mul_inv, one_one]
    · rw [← ArithmeticFunction.mul_apply_one, Units.inv_mul, one_one]
  · suffices Invertible (f 1) -> Invertible f by simpa using Nonempty.map th

中文:
定理 isUnit_iff_isUnit_apply_one
  结论: 是单位 f ↔ 是单位 (f 1)
  证明: by
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨⟨f.val 1, f⁻¹.val 1, ?_, ?_⟩, rfl⟩
    · rw [← ArithmeticFunction.mul_apply_one, Units.mul_inv, one_one]
    · rw [← ArithmeticFunction.mul_apply_one, Units.inv_mul, one_one]
  · suffices Invertible (f 1) -> Invertible f by simpa using Nonempty.map th

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.mul_apply_one, Invertible, Nonempty, Nonempty.map, Units.inv_mul, Units.mul_inv, dirichletInverse_mul_self, f.val, inv_mul, mul_apply_one, mul_inv, one_one, self_mul_dirichletInverse
-/
theorem isUnit_iff_isUnit_apply_one : IsUnit f ↔ IsUnit (f 1) := by
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨⟨f.val 1, f⁻¹.val 1, ?_, ?_⟩, rfl⟩
    · rw [← ArithmeticFunction.mul_apply_one, Units.mul_inv, one_one]
    · rw [← ArithmeticFunction.mul_apply_one, Units.inv_mul, one_one]
  · suffices Invertible (f 1) -> Invertible f by simpa using Nonempty.map this
    exact fun hf => ⟨_, dirichletInverse_mul_self f hf, self_mul_dirichletInverse f hf⟩

end CommRing

end DirichletInverse

/--
Definition of `IsMultiplicative` / `IsMultiplicative` 的定义

English:
definition IsMultiplicative
  signature: [MonoidWithZero R] (f : ArithmeticFunction R)
  body: f 1 = 1 ∧ forall {m n : Nat}, m.Coprime n -> f (m * n) = f m * f n

中文:
定义 是Multiplicative
  签名: [带零幺半群 R] (f : ArithmeticFunction R)
  定义体: f 1 = 1 ∧ forall {m n : Nat}, m.Coprime n -> f (m * n) = f m * f n

Depends on / 依赖: Coprime, m.Coprime
-/
def IsMultiplicative [MonoidWithZero R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 1 ∧ forall {m n : Nat}, m.Coprime n -> f (m * n) = f m * f n

namespace IsMultiplicative

section MonoidWithZero

variable [MonoidWithZero R]

@[simp, arith_mult]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: {f : ArithmeticFunction R} (h : f.IsMultiplicative)
  statement: f 1 = 1
  proof: h.1

@[simp]

中文:
定理 map_one
  条件: {f : ArithmeticFunction R} (h : f.是Multiplicative)
  结论: f 1 = 1
  证明: h.1

@[simp]
-/
theorem map_one {f : ArithmeticFunction R} (h : f.IsMultiplicative) : f 1 = 1 :=
  h.1

@[simp]
/--
theorem `map_mul_of_coprime` / 定理 `map_mul_of_coprime`

English:
theorem map_mul_of_coprime
  statement: {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {m n : Nat}
  proof: hf.2 h

中文:
定理 map_mul_of_coprime
  结论: {f : ArithmeticFunction R} (hf : f.是Multiplicative) {m n : 自然数}
  证明: hf.2 h
-/
theorem map_mul_of_coprime {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {m n : Nat}
    (h : m.gcd n = 1) : f (m * n) = f m * f n :=
  hf.2 h

end MonoidWithZero

open scoped Function in -- required for scoped `on` notation
/--
theorem `map_prod` / 定理 `map_prod`

English:
theorem map_prod
  statement: {ι : Type*} [CommMonoidWithZero R] (g : ι -> Nat) {f : ArithmeticFunction R}
  proof: by
  classical
    induction s using Finset.induction_on with
    | empty => simp [hf]
    | insert _ _ has ih =>
      rw [coe_insert]; rw [Set.pairwise_insert_of_symm] at hs
      rw [prod_insert has]; rw [prod_insert has]; rw [hf.map_mul_of_coprime]; rw [ih hs.1]
      exact Coprime.prod_right fu

中文:
定理 map_prod
  结论: {ι : 类型} [带零交换幺半群 R] (g : ι -> 自然数) {f : ArithmeticFunction R}
  证明: by
  classical
    induction s using Finset.induction_on with
    | empty => simp [hf]
    | insert _ _ has ih =>
      rw [coe_insert]; rw [Set.pairwise_insert_of_symm] at hs
      rw [prod_insert has]; rw [prod_insert has]; rw [hf.map_mul_of_coprime]; rw [ih hs.1]
      exact Coprime.prod_right fu

Depends on / 依赖: Coprime, Coprime.prod_right, Finset, Finset.induction_on, Set.pairwise_insert_of_symm, classical, coe_insert, hf.map_mul_of_coprime, hi.ne_of_notMem, induction_on, insert, map_mul_of_coprime, ne_of_notMem, pairwise_insert_of_symm, prod_insert, prod_right
-/
theorem map_prod {ι : Type*} [CommMonoidWithZero R] (g : ι -> Nat) {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (s : Finset ι) (hs : (s : Set ι).Pairwise (Coprime on g)) :
    f (∏ i in s, g i) = ∏ i in s, f (g i) := by
  classical
    induction s using Finset.induction_on with
    | empty => simp [hf]
    | insert _ _ has ih =>
      rw [coe_insert]; rw [Set.pairwise_insert_of_symm] at hs
      rw [prod_insert has]; rw [prod_insert has]; rw [hf.map_mul_of_coprime]; rw [ih hs.1]
      exact Coprime.prod_right fun i hi => hs.2 _ hi (hi.ne_of_notMem has).symm

/--
theorem `map_prod_of_prime` / 定理 `map_prod_of_prime`

English:
theorem map_prod_of_prime
  statement: [CommMonoidWithZero R] {f : ArithmeticFunction R}
  proof: map_prod _ h_mult t fun x hx y hy hxy => (coprime_primes (ht x hx) (ht y hy)).mpr hxy

中文:
定理 map_prod_of_prime
  结论: [带零交换幺半群 R] {f : ArithmeticFunction R}
  证明: map_prod _ h_mult t fun x hx y hy hxy => (coprime_primes (ht x hx) (ht y hy)).mpr hxy

Depends on / 依赖: coprime_primes, h_mult, map_prod
-/
theorem map_prod_of_prime [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (h_mult : ArithmeticFunction.IsMultiplicative f)
    (t : Finset Nat) (ht : forall p in t, p.Prime) :
    f (∏ a in t, a) = ∏ a in t, f a :=
  map_prod _ h_mult t fun x hx y hy hxy => (coprime_primes (ht x hx) (ht y hy)).mpr hxy

/--
theorem `map_prod_of_subset_primeFactors` / 定理 `map_prod_of_subset_primeFactors`

English:
theorem map_prod_of_subset_primeFactors
  statement: [CommMonoidWithZero R] {f : ArithmeticFunction R}
  proof: map_prod_of_prime h_mult t fun _ a => prime_of_mem_primeFactors (ht a)

中文:
定理 map_prod_of_subset_primeFactors
  结论: [带零交换幺半群 R] {f : ArithmeticFunction R}
  证明: map_prod_of_prime h_mult t fun _ a => prime_of_mem_primeFactors (ht a)

Depends on / 依赖: h_mult, map_prod_of_prime, prime_of_mem_primeFactors
-/
theorem map_prod_of_subset_primeFactors [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (h_mult : ArithmeticFunction.IsMultiplicative f) (l : Nat)
    (t : Finset Nat) (ht : t subseteq l.primeFactors) :
    f (∏ a in t, a) = ∏ a in t, f a :=
  map_prod_of_prime h_mult t fun _ a => prime_of_mem_primeFactors (ht a)

/--
theorem `prod_primeFactors` / 定理 `prod_primeFactors`

English:
theorem prod_primeFactors
  statement: [CommMonoidWithZero R] {f : ArithmeticFunction R}
  proof: by
  rw [← h_mult.map_prod_of_subset_primeFactors l _ Subset.rfl]; rw [prod_primeFactors_of_squarefree hl]

中文:
定理 prod_primeFactors
  结论: [带零交换幺半群 R] {f : ArithmeticFunction R}
  证明: by
  rw [← h_mult.map_prod_of_subset_primeFactors l _ Subset.rfl]; rw [prod_primeFactors_of_squarefree hl]

Depends on / 依赖: Subset, Subset.rfl, h_mult, h_mult.map_prod_of_subset_primeFactors, map_prod_of_subset_primeFactors, prod_primeFactors_of_squarefree
-/
theorem prod_primeFactors [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (h_mult : f.IsMultiplicative) {l : Nat} (hl : Squarefree l) :
    ∏ a in l.primeFactors, f a = f l := by
  rw [← h_mult.map_prod_of_subset_primeFactors l _ Subset.rfl]; rw [prod_primeFactors_of_squarefree hl]

/--
theorem `map_div_of_coprime` / 定理 `map_div_of_coprime`

English:
theorem map_div_of_coprime
  statement: [GroupWithZero R] {f : ArithmeticFunction R}
  proof: by
  apply (div_eq_of_eq_mul hd ..).symm
  rw [← hf.right hl]; rw [Nat.div_mul_cancel hdl]

@[arith_mult]

中文:
定理 map_div_of_coprime
  结论: [带零群 R] {f : ArithmeticFunction R}
  证明: by
  apply (div_eq_of_eq_mul hd ..).symm
  rw [← hf.right hl]; rw [Nat.div_mul_cancel hdl]

@[arith_mult]

Depends on / 依赖: Nat.div_mul_cancel, div_eq_of_eq_mul, div_mul_cancel, hf.right
-/
theorem map_div_of_coprime [GroupWithZero R] {f : ArithmeticFunction R}
    (hf : IsMultiplicative f) {l d : Nat} (hdl : d ∣ l) (hl : (l / d).Coprime d) (hd : f d != 0) :
    f (l / d) = f l / f d := by
  apply (div_eq_of_eq_mul hd ..).symm
  rw [← hf.right hl]; rw [Nat.div_mul_cancel hdl]

@[arith_mult]
/--
theorem `natCast` / 定理 `natCast`

English:
theorem natCast
  given: {f : ArithmeticFunction Nat} [Semiring R] (h : f.IsMultiplicative)
  proof: ⟨by simp [h], fun cop => by simp [h.2 cop]⟩

@[arith_mult]

中文:
定理 natCast
  条件: {f : ArithmeticFunction 自然数} [半环 R] (h : f.是Multiplicative)
  证明: ⟨by simp [h], fun cop => by simp [h.2 cop]⟩

@[arith_mult]
-/
theorem natCast {f : ArithmeticFunction Nat} [Semiring R] (h : f.IsMultiplicative) :
    IsMultiplicative (f : ArithmeticFunction R) :=
  ⟨by simp [h], fun cop => by simp [h.2 cop]⟩

@[arith_mult]
/--
theorem `intCast` / 定理 `intCast`

English:
theorem intCast
  given: {f : ArithmeticFunction Int} [Ring R] (h : f.IsMultiplicative)
  proof: ⟨by simp [h], fun cop => by simp [h.2 cop]⟩

@[arith_mult]

中文:
定理 intCast
  条件: {f : ArithmeticFunction 整数} [环 R] (h : f.是Multiplicative)
  证明: ⟨by simp [h], fun cop => by simp [h.2 cop]⟩

@[arith_mult]
-/
theorem intCast {f : ArithmeticFunction Int} [Ring R] (h : f.IsMultiplicative) :
    IsMultiplicative (f : ArithmeticFunction R) :=
  ⟨by simp [h], fun cop => by simp [h.2 cop]⟩

@[arith_mult]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative)
  proof: by
  refine ⟨by simp [hf.1, hg.1], ?_⟩
  simp only [mul_apply]
  intro m n cop
  rw [sum_mul_sum]; rw [← sum_product']
  symm
  apply sum_nbij fun ((i, j), k, l) => (i * k, j * l)
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h
    simp only [mem_divisorsAntidiagonal, Ne, mem_product] at h
    rcases h with ⟨⟨rfl

中文:
定理 mul
  结论: [交换半环 R] {f g : ArithmeticFunction R} (hf : f.是Multiplicative)
  证明: by
  refine ⟨by simp [hf.1, hg.1], ?_⟩
  simp only [mul_apply]
  intro m n cop
  rw [sum_mul_sum]; rw [← sum_product']
  symm
  apply sum_nbij fun ((i, j), k, l) => (i * k, j * l)
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h
    simp only [mem_divisorsAntidiagonal, Ne, mem_product] at h
    rcases h with ⟨⟨rfl

Depends on / 依赖: Prod.mk_inj, Set.InjOn, mem_coe, mem_divisorsAntidiagonal, mem_product, mk_inj, mul_apply, mul_eq_zero, not_or_intro, sum_mul_sum, sum_nbij, sum_product
-/
theorem mul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) : IsMultiplicative (f * g) := by
  refine ⟨by simp [hf.1, hg.1], ?_⟩
  simp only [mul_apply]
  intro m n cop
  rw [sum_mul_sum]; rw [← sum_product']
  symm
  apply sum_nbij fun ((i, j), k, l) => (i * k, j * l)
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h
    simp only [mem_divisorsAntidiagonal, Ne, mem_product] at h
    rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    simp only [mem_divisorsAntidiagonal, mul_eq_zero, Ne]
    constructor
    · ring
    rw [mul_eq_zero] at *
    exact not_or_intro ha hb
  · simp only [Set.InjOn, mem_coe, mem_divisorsAntidiagonal, mem_product, Prod.mk_inj]
    rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩ ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ hcd h
    ext
    · trans gcd (a1 * a2) (a1 * b1)
      · rw [gcd_mul_left, cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_one]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.1.1]; rw [h.1]; rw [gcd_mul_left]; rw [cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one]; rw [mul_one]
    · trans gcd (a1 * a2) (a2 * b2)
      · rw [mul_comm, gcd_mul_left, cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one,
          mul_one]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.1.1]; rw [h.2]; rw [mul_comm]; rw [gcd_mul_left]; rw [cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one]; rw [mul_one]
    · trans gcd (b1 * b2) (a1 * b1)
      · rw [mul_comm, gcd_mul_right, cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one,
          one_mul]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.2.1]; rw [h.1]; rw [mul_comm c1 d1]; rw [gcd_mul_left]; rw [cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one]; rw [mul_one]
    · trans gcd (b1 * b2) (a2 * b2)
      · rw [gcd_mul_right, cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.2.1]; rw [h.2]; rw [gcd_mul_right]; rw [cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one]; rw [one_mul]
  · simp only [Set.SurjOn, Set.subset_def, mem_coe, mem_divisorsAntidiagonal, mem_product,
      Set.mem_image]
    rintro ⟨b1, b2⟩ h
    use ((b1.gcd m, b2.gcd m), (b1.gcd n, b2.gcd n))
    rw [← cop.gcd_mul _]; rw [← cop.gcd_mul _]; rw [← h.1]; rw [gcd_mul_gcd_of_coprime_of_mul_eq_mul cop h.1]; rw [gcd_mul_gcd_of_coprime_of_mul_eq_mul cop.symm _]
    · rw [Ne, mul_eq_zero, not_or] at h
      simp [h.2.1, h.2.2]
    rw [mul_comm n m]; rw [h.1]
  · simp only [mem_divisorsAntidiagonal, mem_product]
    rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    rw [hf.map_mul_of_coprime cop.coprime_mul_right.coprime_mul_right_right]; rw [hg.map_mul_of_coprime cop.coprime_mul_left.coprime_mul_left_right]
    ring

/--
theorem `multiplicative_factorization` / 定理 `multiplicative_factorization`

English:
theorem multiplicative_factorization
  statement: [CommMonoidWithZero R] (f : ArithmeticFunction R)
  proof: Nat.multiplicative_factorization f (fun _ _ => hf.2) hf.1 hn

中文:
定理 multiplicative_factorization
  结论: [带零交换幺半群 R] (f : ArithmeticFunction R)
  证明: Nat.multiplicative_factorization f (fun _ _ => hf.2) hf.1 hn

Depends on / 依赖: Nat.multiplicative_factorization, multiplicative_factorization
-/
theorem multiplicative_factorization [CommMonoidWithZero R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) {n : Nat} (hn : n != 0) :
    f n = n.factorization.prod fun p k => f (p ^ k) :=
  Nat.multiplicative_factorization f (fun _ _ => hf.2) hf.1 hn

/--
theorem `iff_ne_zero` / 定理 `iff_ne_zero`

English:
theorem iff_ne_zero
  given: [MonoidWithZero R] {f : ArithmeticFunction R}
  proof: by
  refine and_congr_right' (forall₂_congr fun m n => ⟨fun h _ _ => h, fun h hmn => ?_⟩)
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  exact h hm hn hmn

中文:
定理 iff_ne_zero
  条件: [带零幺半群 R] {f : ArithmeticFunction R}
  证明: by
  refine and_congr_right' (forall₂_congr fun m n => ⟨fun h _ _ => h, fun h hmn => ?_⟩)
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  exact h hm hn hmn

Depends on / 依赖: and_congr_right, eq_or_ne
-/
theorem iff_ne_zero [MonoidWithZero R] {f : ArithmeticFunction R} :
    IsMultiplicative f ↔
      f 1 = 1 ∧ forall {m n : Nat}, m != 0 -> n != 0 -> m.Coprime n -> f (m * n) = f m * f n := by
  refine and_congr_right' (forall₂_congr fun m n => ⟨fun h _ _ => h, fun h hmn => ?_⟩)
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  exact h hm hn hmn

/--
theorem `eq_iff_eq_on_prime_powers` / 定理 `eq_iff_eq_on_prime_powers`

English:
theorem eq_iff_eq_on_prime_powers
  statement: [CommMonoidWithZero R] (f : ArithmeticFunction R)
  proof: by
  constructor <;> intro h
  · simp [h]
  ext n
  by_cases hn : n = 0
  · rw [hn, ArithmeticFunction.map_zero, ArithmeticFunction.map_zero]
  rw [multiplicative_factorization f hf hn]; rw [multiplicative_factorization g hg hn]
  exact prod_congr rfl fun p hp => h p _ (prime_of_mem_primeFactors hp)

中文:
定理 eq_iff_eq_on_prime_powers
  结论: [带零交换幺半群 R] (f : ArithmeticFunction R)
  证明: by
  constructor <;> intro h
  · simp [h]
  ext n
  by_cases hn : n = 0
  · rw [hn, ArithmeticFunction.map_zero, ArithmeticFunction.map_zero]
  rw [multiplicative_factorization f hf hn]; rw [multiplicative_factorization g hg hn]
  exact prod_congr rfl fun p hp => h p _ (prime_of_mem_primeFactors hp)

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.map_zero, map_zero, multiplicative_factorization, prime_of_mem_primeFactors, prod_congr
-/
theorem eq_iff_eq_on_prime_powers [CommMonoidWithZero R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) (g : ArithmeticFunction R) (hg : g.IsMultiplicative) :
    f = g ↔ forall p i : Nat, Nat.Prime p -> f (p ^ i) = g (p ^ i) := by
  constructor <;> intro h
  · simp [h]
  ext n
  by_cases hn : n = 0
  · rw [hn, ArithmeticFunction.map_zero, ArithmeticFunction.map_zero]
  rw [multiplicative_factorization f hf hn]; rw [multiplicative_factorization g hg hn]
  exact prod_congr rfl fun p hp => h p _ (prime_of_mem_primeFactors hp)

/--
theorem `lcm_apply_mul_gcd_apply` / 定理 `lcm_apply_mul_gcd_apply`

English:
theorem lcm_apply_mul_gcd_apply
  statement: [CommMonoidWithZero R] {f : ArithmeticFunction R}
  proof: by
  by_cases hx : x = 0
  · simp only [hx, f.map_zero, zero_mul, lcm_zero_left, gcd_zero_left]
  by_cases hy : y = 0
  · simp only [hy, f.map_zero, mul_zero, lcm_zero_right, gcd_zero_right, zero_mul]
  have hgcd_ne_zero : x.gcd y != 0 := gcd_ne_zero_left hx
  have hlcm_ne_zero : x.lcm y != 0 := lcm

中文:
定理 lcm_apply_mul_gcd_apply
  结论: [带零交换幺半群 R] {f : ArithmeticFunction R}
  证明: by
  by_cases hx : x = 0
  · simp only [hx, f.map_zero, zero_mul, lcm_zero_left, gcd_zero_left]
  by_cases hy : y = 0
  · simp only [hy, f.map_zero, mul_zero, lcm_zero_right, gcd_zero_right, zero_mul]
  have hgcd_ne_zero : x.gcd y != 0 := gcd_ne_zero_left hx
  have hlcm_ne_zero : x.lcm y != 0 := lcm

Depends on / 依赖: Finsupp, Finsupp.prod_of_support_subset, f.map_zero, gcd_ne_zero_left, gcd_zero_left, gcd_zero_right, hf.multiplicative_factorization, hfi_ze, hfi_zero, hgcd_ne_zero, hlcm_ne_zero, iterate, lcm_ne_zero, lcm_zero_left, lcm_zero_right, map_zero, mul_zero, multiplicative_factorization, pow_zero, prod_of_support_subset
-/
theorem lcm_apply_mul_gcd_apply [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) {x y : Nat} :
    f (x.lcm y) * f (x.gcd y) = f x * f y := by
  by_cases hx : x = 0
  · simp only [hx, f.map_zero, zero_mul, lcm_zero_left, gcd_zero_left]
  by_cases hy : y = 0
  · simp only [hy, f.map_zero, mul_zero, lcm_zero_right, gcd_zero_right, zero_mul]
  have hgcd_ne_zero : x.gcd y != 0 := gcd_ne_zero_left hx
  have hlcm_ne_zero : x.lcm y != 0 := lcm_ne_zero hx hy
  have hfi_zero : forall {i}, f (i ^ 0) = 1 := by
    intro i; rw [pow_zero, hf.1]
  iterate 4 rw [hf.multiplicative_factorization f (by assumption),
    Finsupp.prod_of_support_subset _ _ _ (fun _ _ => hfi_zero)
      (s := (x.primeFactors union y.primeFactors))]
  · rw [← prod_mul_distrib, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p _
    rcases Nat.le_or_le (x.factorization p) (y.factorization p) with h | h <;>
      simp only [factorization_lcm hx hy, Finsupp.sup_apply, h, sup_of_le_right,
        sup_of_le_left, inf_of_le_right, factorization_gcd hx hy, Finsupp.inf_apply,
        inf_of_le_left, mul_comm]
  · apply subset_union_right
  · apply subset_union_left
  · rw [factorization_gcd hx hy, Finsupp.support_inf]
    apply inter_subset_union
  · simp [factorization_lcm hx hy]

/--
theorem `map_gcd` / 定理 `map_gcd`

English:
theorem map_gcd
  statement: [CommGroupWithZero R] {f : ArithmeticFunction R}
  proof: by
  rw [← hf.lcm_apply_mul_gcd_apply]; rw [mul_div_cancel_left₀ _ hf_lcm]

中文:
定理 map_gcd
  结论: [带零交换群 R] {f : ArithmeticFunction R}
  证明: by
  rw [← hf.lcm_apply_mul_gcd_apply]; rw [mul_div_cancel_left₀ _ hf_lcm]

Depends on / 依赖: hf.lcm_apply_mul_gcd_apply, hf_lcm, lcm_apply_mul_gcd_apply
-/
theorem map_gcd [CommGroupWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) {x y : Nat} (hf_lcm : f (x.lcm y) != 0) :
    f (x.gcd y) = f x * f y / f (x.lcm y) := by
  rw [← hf.lcm_apply_mul_gcd_apply]; rw [mul_div_cancel_left₀ _ hf_lcm]

/--
theorem `map_lcm` / 定理 `map_lcm`

English:
theorem map_lcm
  statement: [CommGroupWithZero R] {f : ArithmeticFunction R}
  proof: by
  rw [← hf.lcm_apply_mul_gcd_apply]; rw [mul_div_cancel_right₀ _ hf_gcd]

中文:
定理 map_lcm
  结论: [带零交换群 R] {f : ArithmeticFunction R}
  证明: by
  rw [← hf.lcm_apply_mul_gcd_apply]; rw [mul_div_cancel_right₀ _ hf_gcd]

Depends on / 依赖: hf.lcm_apply_mul_gcd_apply, hf_gcd, lcm_apply_mul_gcd_apply
-/
theorem map_lcm [CommGroupWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) {x y : Nat} (hf_gcd : f (x.gcd y) != 0) :
    f (x.lcm y) = f x * f y / f (x.gcd y) := by
  rw [← hf.lcm_apply_mul_gcd_apply]; rw [mul_div_cancel_right₀ _ hf_gcd]

/--
theorem `eq_zero_of_squarefree_of_dvd_eq_zero` / 定理 `eq_zero_of_squarefree_of_dvd_eq_zero`

English:
theorem eq_zero_of_squarefree_of_dvd_eq_zero
  statement: [MonoidWithZero R] {f : ArithmeticFunction R}
  proof: by
  rcases hmn with ⟨k, rfl⟩
  simp only [zero_mul, hf.map_mul_of_coprime (coprime_of_squarefree_mul hn), h_zero]

中文:
定理 eq_zero_of_squarefree_of_dvd_eq_zero
  结论: [带零幺半群 R] {f : ArithmeticFunction R}
  证明: by
  rcases hmn with ⟨k, rfl⟩
  simp only [zero_mul, hf.map_mul_of_coprime (coprime_of_squarefree_mul hn), h_zero]

Depends on / 依赖: coprime_of_squarefree_mul, h_zero, hf.map_mul_of_coprime, map_mul_of_coprime, zero_mul
-/
theorem eq_zero_of_squarefree_of_dvd_eq_zero [MonoidWithZero R] {f : ArithmeticFunction R}
    (hf : IsMultiplicative f) {m n : Nat} (hn : Squarefree n) (hmn : m ∣ n)
    (h_zero : f m = 0) :
    f n = 0 := by
  rcases hmn with ⟨k, rfl⟩
  simp only [zero_mul, hf.map_mul_of_coprime (coprime_of_squarefree_mul hn), h_zero]

end IsMultiplicative

@[simp, arith_mult]
/--
theorem `isMultiplicative_one` / 定理 `isMultiplicative_one`

English:
theorem isMultiplicative_one
  given: [MonoidWithZero R]
  statement: IsMultiplicative (1 : ArithmeticFunction R)
  proof: IsMultiplicative.iff_ne_zero.2 ⟨by simp, by
    intro m n hm hn hmn
    by_cases h : m = 1 <;> aesop⟩

@[arith_mult]

中文:
定理 isMultiplicative_one
  条件: [带零幺半群 R]
  结论: 是Multiplicative (1 : ArithmeticFunction R)
  证明: IsMultiplicative.iff_ne_zero.2 ⟨by simp, by
    intro m n hm hn hmn
    by_cases h : m = 1 <;> aesop⟩

@[arith_mult]

Depends on / 依赖: IsMultiplicative, IsMultiplicative.iff_ne_zero, iff_ne_zero
-/
theorem isMultiplicative_one [MonoidWithZero R] : IsMultiplicative (1 : ArithmeticFunction R) :=
  IsMultiplicative.iff_ne_zero.2 ⟨by simp, by
    intro m n hm hn hmn
    by_cases h : m = 1 <;> aesop⟩

@[arith_mult]
/--
theorem `isMultiplicative_finsetProd` / 定理 `isMultiplicative_finsetProd`

English:
theorem isMultiplicative_finsetProd
  statement: [CommSemiring R] {ι : Type*}
  proof: by
  induction s using Finset.cons_induction
  case empty => simp
  case cons a s ha ih =>
    rw [Finset.prod_cons]
    exact (hf a (by grind)).mul (by grind)

@[arith_mult]

中文:
定理 isMultiplicative_finsetProd
  结论: [交换半环 R] {ι : 类型}
  证明: by
  induction s using Finset.cons_induction
  case empty => simp
  case cons a s ha ih =>
    rw [Finset.prod_cons]
    exact (hf a (by grind)).mul (by grind)

@[arith_mult]

Depends on / 依赖: Finset, Finset.cons_induction, Finset.prod_cons, cons_induction, prod_cons
-/
theorem isMultiplicative_finsetProd [CommSemiring R] {ι : Type*}
    (f : ι -> ArithmeticFunction R) (s : Finset ι) (hf : forall i in s, IsMultiplicative (f i)) :
    IsMultiplicative (∏ i in s, f i) := by
  induction s using Finset.cons_induction
  case empty => simp
  case cons a s ha ih =>
    rw [Finset.prod_cons]
    exact (hf a (by grind)).mul (by grind)

@[arith_mult]
/--
theorem `IsMultiplicative.pow` / 定理 `IsMultiplicative.pow`

English:
theorem IsMultiplicative.pow
  statement: [CommSemiring R] {f : ArithmeticFunction R}
  proof: by
  induction k
  case zero => simp
  case succ k hk =>
    rw [pow_succ]
    exact hk.mul hf

中文:
定理 是Multiplicative.pow
  结论: [交换半环 R] {f : ArithmeticFunction R}
  证明: by
  induction k
  case zero => simp
  case succ k hk =>
    rw [pow_succ]
    exact hk.mul hf

Depends on / 依赖: hk.mul, pow_succ
-/
theorem IsMultiplicative.pow [CommSemiring R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) {k : Nat} : IsMultiplicative (f ^ k) := by
  induction k
  case zero => simp
  case succ k hk =>
    rw [pow_succ]
    exact hk.mul hf

end ArithmeticFunction
