/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Group.Basic

/-!
# Maps (semi)conjugating a shift to a shift

Denote by $S^1$ the unit circle `UnitAddCircle`.
A common way to study a self-map $f\colon S^1\to S^1$ of degree `1`
is to lift it to a map $\tilde f\colon \mathbb R\to \mathbb R$
such that $\tilde f(x + 1) = \tilde f(x)+1$ for all `x`.

In this file we define a structure and a typeclass
for bundled maps satisfying `f (x + a) = f x + b`.

We use parameters `a` and `b` instead of `1` to accommodate for two use cases:

- maps between circles of different lengths;
- self-maps $f\colon S^1\to S^1$ of degree other than one,
  including orientation-reversing maps.
-/

@[expose] public section

assert_not_exists Finset

open Function Set

/--
Definition of `AddConstMap` / `AddConstMap` 的定义

English:
structure AddConstMap
  parameters: (G H : Type*) [Add G] [Add H] (a : G) (b : H)
  axioms and operations (2):
    - toFun : G -> H
    - map_add_const'((x : G)) : toFun (x + a) = toFun x + b

中文:
结构 加法余nst映射
  参数: (G H : 类型) [加法 G] [加法 H] (a : G) (b : H)
  公理与运算 (2 个):
    - toFun : G -> H
    - map_add_const'((x : G)) : toFun (x + a) = toFun x + b
-/
structure AddConstMap (G H : Type*) [Add G] [Add H] (a : G) (b : H) where
  /-- The underlying function of an `AddConstMap`.
  Use automatic coercion to function instead. -/
  protected toFun : G -> H
  /-- An `AddConstMap` satisfies `f (x + a) = f x + b`. Use `map_add_const` instead. -/
  map_add_const' (x : G) : toFun (x + a) = toFun x + b

@[inherit_doc]
scoped[AddConstMap] notation:25 G " ->+c[" a ", " b "] " H => AddConstMap G H a b

/--
Definition of `AddConstMapClass` / `AddConstMapClass` 的定义

English:
class AddConstMapClass
  parameters: (F : Type*) (G H : outParam Type*) [Add G] [Add H]
  axioms and operations (1):
    - map_add_const((f : F) (x : G)) : f (x + a) = f x + b

中文:
类 加法余nst映射类
  参数: (F : 类型) (G H : outParam 类型) [加法 G] [加法 H]
  公理与运算 (1 个):
    - map_add_const((f : F) (x : G)) : f (x + a) = f x + b
-/
class AddConstMapClass (F : Type*) (G H : outParam Type*) [Add G] [Add H]
    (a : outParam G) (b : outParam H) [FunLike F G H] : Prop where
  /-- A map of `AddConstMapClass` class semiconjugates shift by `a` to the shift by `b`:
  `∀ x, f (x + a) = f x + b`. -/
  map_add_const (f : F) (x : G) : f (x + a) = f x + b

namespace AddConstMapClass

/-!
### Properties of `AddConstMapClass` maps

In this section we prove properties like `f (x + n • a) = f x + n • b`.
-/

scoped[AddConstMapClass] attribute [simp] map_add_const

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

/--
theorem `semiconj` / 定理 `semiconj`

English:
theorem semiconj
  given: [Add G] [Add H] [AddConstMapClass F G H a b] (f : F)
  proof: map_add_const f

@[scoped simp]

中文:
定理 semiconj
  条件: [加法 G] [加法 H] [加法余nst映射类 F G H a b] (f : F)
  证明: map_add_const f

@[scoped simp]
-/
protected theorem semiconj [Add G] [Add H] [AddConstMapClass F G H a b] (f : F) :
    Semiconj f (· + a) (· + b) :=
  map_add_const f

@[scoped simp]
/--
theorem `map_add_nsmul` / 定理 `map_add_nsmul`

English:
theorem map_add_nsmul
  statement: [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
  proof: by
  simpa using (AddConstMapClass.semiconj f).iterate_right n x

@[scoped simp]

中文:
定理 map_add_nsmul
  结论: [加法幺半群 G] [加法幺半群 H] [加法余nst映射类 F G H a b]
  证明: by
  simpa using (AddConstMapClass.semiconj f).iterate_right n x

@[scoped simp]

Depends on / 依赖: AddConstMapClass, AddConstMapClass.semiconj, iterate_right, semiconj
-/
theorem map_add_nsmul [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : Nat) : f (x + n • a) = f x + n • b := by
  simpa using (AddConstMapClass.semiconj f).iterate_right n x

@[scoped simp]
/--
theorem `map_add_nat'` / 定理 `map_add_nat'`

English:
theorem map_add_nat'
  statement: [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
  proof: by simp [← map_add_nsmul]

中文:
定理 map_add_nat'
  结论: [加法带幺幺半群 G] [加法幺半群 H] [加法余nst映射类 F G H 1 b]
  证明: by simp [← map_add_nsmul]

Depends on / 依赖: map_add_nsmul
-/
theorem map_add_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : Nat) : f (x + n) = f x + n • b := by simp [← map_add_nsmul]

/--
theorem `map_add_one` / 定理 `map_add_one`

English:
theorem map_add_one
  statement: [AddMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b]
  proof: map_add_const f x

@[scoped simp]

中文:
定理 map_add_one
  结论: [加法带幺幺半群 G] [加法 H] [加法余nst映射类 F G H 1 b]
  证明: map_add_const f x

@[scoped simp]

Depends on / 依赖: map_add_const
-/
theorem map_add_one [AddMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (x + 1) = f x + b := map_add_const f x

@[scoped simp]
/--
theorem `map_add_ofNat'` / 定理 `map_add_ofNat'`

English:
theorem map_add_ofNat'
  statement: [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
  proof: map_add_nat' f x n

中文:
定理 map_add_of自然数'
  结论: [加法带幺幺半群 G] [加法幺半群 H] [加法余nst映射类 F G H 1 b]
  证明: map_add_nat' f x n

Depends on / 依赖: map_add_nat
-/
theorem map_add_ofNat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : Nat) [n.AtLeastTwo] :
    f (x + ofNat(n)) = f x + (ofNat(n) : Nat) • b :=
  map_add_nat' f x n

/--
theorem `map_add_nat` / 定理 `map_add_nat`

English:
theorem map_add_nat
  statement: [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
  proof: by simp

中文:
定理 map_add_nat
  结论: [加法带幺幺半群 G] [加法带幺幺半群 H] [加法余nst映射类 F G H 1 1]
  证明: by simp
-/
theorem map_add_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : Nat) : f (x + n) = f x + n := by simp

/--
theorem `map_add_ofNat` / 定理 `map_add_ofNat`

English:
theorem map_add_ofNat
  statement: [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
  proof: map_add_nat f x n

@[scoped simp]

中文:
定理 map_add_of自然数
  结论: [加法带幺幺半群 G] [加法带幺幺半群 H] [加法余nst映射类 F G H 1 1]
  证明: map_add_nat f x n

@[scoped simp]

Depends on / 依赖: map_add_nat
-/
theorem map_add_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : Nat) [n.AtLeastTwo] :
    f (x + ofNat(n)) = f x + ofNat(n) := map_add_nat f x n

@[scoped simp]
/--
theorem `map_const` / 定理 `map_const`

English:
theorem map_const
  given: [AddZeroClass G] [Add H] [AddConstMapClass F G H a b] (f : F)
  proof: by
  simpa using map_add_const f 0

中文:
定理 map_const
  条件: [加法零类 G] [加法 H] [加法余nst映射类 F G H a b] (f : F)
  证明: by
  simpa using map_add_const f 0

Depends on / 依赖: map_add_const
-/
theorem map_const [AddZeroClass G] [Add H] [AddConstMapClass F G H a b] (f : F) :
    f a = f 0 + b := by
  simpa using map_add_const f 0

/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: [AddZeroClass G] [One G] [Add H] [AddConstMapClass F G H 1 b] (f : F)
  proof: map_const f

@[scoped simp]

中文:
定理 map_one
  条件: [加法零类 G] [幺 G] [加法 H] [加法余nst映射类 F G H 1 b] (f : F)
  证明: map_const f

@[scoped simp]

Depends on / 依赖: map_const
-/
theorem map_one [AddZeroClass G] [One G] [Add H] [AddConstMapClass F G H 1 b] (f : F) :
    f 1 = f 0 + b :=
  map_const f

@[scoped simp]
/--
theorem `map_nsmul_const` / 定理 `map_nsmul_const`

English:
theorem map_nsmul_const
  statement: [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
  proof: by
  simpa using map_add_nsmul f 0 n

@[scoped simp]

中文:
定理 map_nsmul_const
  结论: [加法幺半群 G] [加法幺半群 H] [加法余nst映射类 F G H a b]
  证明: by
  simpa using map_add_nsmul f 0 n

@[scoped simp]

Depends on / 依赖: map_add_nsmul
-/
theorem map_nsmul_const [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (n : Nat) : f (n • a) = f 0 + n • b := by
  simpa using map_add_nsmul f 0 n

@[scoped simp]
/--
theorem `map_nat'` / 定理 `map_nat'`

English:
theorem map_nat'
  statement: [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
  proof: by
  simpa using map_add_nat' f 0 n

中文:
定理 map_nat'
  结论: [加法带幺幺半群 G] [加法幺半群 H] [加法余nst映射类 F G H 1 b]
  证明: by
  simpa using map_add_nat' f 0 n

Depends on / 依赖: map_add_nat
-/
theorem map_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : Nat) : f n = f 0 + n • b := by
  simpa using map_add_nat' f 0 n

/--
theorem `map_ofNat'` / 定理 `map_ofNat'`

English:
theorem map_ofNat'
  statement: [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
  proof: map_nat' f n

中文:
定理 map_of自然数'
  结论: [加法带幺幺半群 G] [加法幺半群 H] [加法余nst映射类 F G H 1 b]
  证明: map_nat' f n

Depends on / 依赖: map_nat
-/
theorem map_ofNat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : Nat) [n.AtLeastTwo] :
    f (ofNat(n)) = f 0 + (ofNat(n) : Nat) • b :=
  map_nat' f n

/--
theorem `map_nat` / 定理 `map_nat`

English:
theorem map_nat
  statement: [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
  proof: by simp

中文:
定理 map_nat
  结论: [加法带幺幺半群 G] [加法带幺幺半群 H] [加法余nst映射类 F G H 1 1]
  证明: by simp
-/
theorem map_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : Nat) : f n = f 0 + n := by simp

/--
theorem `map_ofNat` / 定理 `map_ofNat`

English:
theorem map_ofNat
  statement: [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
  proof: map_nat f n

@[scoped simp]

中文:
定理 map_of自然数
  结论: [加法带幺幺半群 G] [加法带幺幺半群 H] [加法余nst映射类 F G H 1 1]
  证明: map_nat f n

@[scoped simp]

Depends on / 依赖: map_nat
-/
theorem map_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : Nat) [n.AtLeastTwo] :
    f ofNat(n) = f 0 + ofNat(n) := map_nat f n

@[scoped simp]
/--
theorem `map_const_add` / 定理 `map_const_add`

English:
theorem map_const_add
  statement: [AddCommMagma G] [Add H] [AddConstMapClass F G H a b]
  proof: by
  rw [add_comm]; rw [map_add_const]

中文:
定理 map_const_add
  结论: [加法交换原群 G] [加法 H] [加法余nst映射类 F G H a b]
  证明: by
  rw [add_comm]; rw [map_add_const]

Depends on / 依赖: add_comm, map_add_const
-/
theorem map_const_add [AddCommMagma G] [Add H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : f (a + x) = f x + b := by
  rw [add_comm]; rw [map_add_const]

/--
theorem `map_one_add` / 定理 `map_one_add`

English:
theorem map_one_add
  statement: [AddCommMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b]
  proof: map_const_add f x

@[scoped simp]

中文:
定理 map_one_add
  结论: [加法交换带幺幺半群 G] [加法 H] [加法余nst映射类 F G H 1 b]
  证明: map_const_add f x

@[scoped simp]

Depends on / 依赖: map_const_add
-/
theorem map_one_add [AddCommMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (1 + x) = f x + b := map_const_add f x

@[scoped simp]
/--
theorem `map_nsmul_add` / 定理 `map_nsmul_add`

English:
theorem map_nsmul_add
  statement: [AddCommMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
  proof: by
  rw [add_comm]; rw [map_add_nsmul]

@[scoped simp]

中文:
定理 map_nsmul_add
  结论: [加法交换幺半群 G] [加法幺半群 H] [加法余nst映射类 F G H a b]
  证明: by
  rw [add_comm]; rw [map_add_nsmul]

@[scoped simp]

Depends on / 依赖: add_comm, map_add_nsmul
-/
theorem map_nsmul_add [AddCommMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (n : Nat) (x : G) : f (n • a + x) = f x + n • b := by
  rw [add_comm]; rw [map_add_nsmul]

@[scoped simp]
/--
theorem `map_nat_add'` / 定理 `map_nat_add'`

English:
theorem map_nat_add'
  statement: [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
  proof: by
  simpa using map_nsmul_add f n x

中文:
定理 map_nat_add'
  结论: [加法交换带幺幺半群 G] [加法幺半群 H] [加法余nst映射类 F G H 1 b]
  证明: by
  simpa using map_nsmul_add f n x

Depends on / 依赖: map_nsmul_add
-/
theorem map_nat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : Nat) (x : G) : f (↑n + x) = f x + n • b := by
  simpa using map_nsmul_add f n x

/--
theorem `map_ofNat_add'` / 定理 `map_ofNat_add'`

English:
theorem map_ofNat_add'
  statement: [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
  proof: map_nat_add' f n x

中文:
定理 map_of自然数_add'
  结论: [加法交换带幺幺半群 G] [加法幺半群 H] [加法余nst映射类 F G H 1 b]
  证明: map_nat_add' f n x

Depends on / 依赖: map_nat_add
-/
theorem map_ofNat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : Nat) [n.AtLeastTwo] (x : G) :
    f (ofNat(n) + x) = f x + ofNat(n) • b :=
  map_nat_add' f n x

/--
theorem `map_nat_add` / 定理 `map_nat_add`

English:
theorem map_nat_add
  statement: [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
  proof: by simp

中文:
定理 map_nat_add
  结论: [加法交换带幺幺半群 G] [加法带幺幺半群 H] [加法余nst映射类 F G H 1 1]
  证明: by simp
-/
theorem map_nat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : Nat) (x : G) : f (↑n + x) = f x + n := by simp

/--
theorem `map_ofNat_add` / 定理 `map_ofNat_add`

English:
theorem map_ofNat_add
  statement: [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
  proof: map_nat_add f n x

@[scoped simp]

中文:
定理 map_of自然数_add
  结论: [加法交换带幺幺半群 G] [加法带幺幺半群 H] [加法余nst映射类 F G H 1 1]
  证明: map_nat_add f n x

@[scoped simp]

Depends on / 依赖: map_nat_add
-/
theorem map_ofNat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : Nat) [n.AtLeastTwo] (x : G) :
    f (ofNat(n) + x) = f x + ofNat(n) :=
  map_nat_add f n x

@[scoped simp]
/--
theorem `map_sub_nsmul` / 定理 `map_sub_nsmul`

English:
theorem map_sub_nsmul
  statement: [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
  proof: by
  conv_rhs => rw [← sub_add_cancel x (n • a), map_add_nsmul, add_sub_cancel_right]

@[scoped simp]

中文:
定理 map_sub_nsmul
  结论: [加法群 G] [加法群 H] [加法余nst映射类 F G H a b]
  证明: by
  conv_rhs => rw [← sub_add_cancel x (n • a), map_add_nsmul, add_sub_cancel_right]

@[scoped simp]

Depends on / 依赖: add_sub_cancel_right, conv_rhs, map_add_nsmul, sub_add_cancel
-/
theorem map_sub_nsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : Nat) : f (x - n • a) = f x - n • b := by
  conv_rhs => rw [← sub_add_cancel x (n • a), map_add_nsmul, add_sub_cancel_right]

@[scoped simp]
/--
theorem `map_sub_const` / 定理 `map_sub_const`

English:
theorem map_sub_const
  statement: [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
  proof: by
  simpa using map_sub_nsmul f x 1

中文:
定理 map_sub_const
  结论: [加法群 G] [加法群 H] [加法余nst映射类 F G H a b]
  证明: by
  simpa using map_sub_nsmul f x 1

Depends on / 依赖: map_sub_nsmul
-/
theorem map_sub_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : f (x - a) = f x - b := by
  simpa using map_sub_nsmul f x 1

/--
theorem `map_sub_one` / 定理 `map_sub_one`

English:
theorem map_sub_one
  statement: [AddGroup G] [One G] [AddGroup H] [AddConstMapClass F G H 1 b]
  proof: map_sub_const f x

@[scoped simp]

中文:
定理 map_sub_one
  结论: [加法群 G] [幺 G] [加法群 H] [加法余nst映射类 F G H 1 b]
  证明: map_sub_const f x

@[scoped simp]

Depends on / 依赖: map_sub_const
-/
theorem map_sub_one [AddGroup G] [One G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (x - 1) = f x - b :=
  map_sub_const f x

@[scoped simp]
/--
theorem `map_sub_nat'` / 定理 `map_sub_nat'`

English:
theorem map_sub_nat'
  statement: [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
  proof: by
  simpa using map_sub_nsmul f x n

@[scoped simp]

中文:
定理 map_sub_nat'
  结论: [加法带幺群 G] [加法群 H] [加法余nst映射类 F G H 1 b]
  证明: by
  simpa using map_sub_nsmul f x n

@[scoped simp]

Depends on / 依赖: map_sub_nsmul
-/
theorem map_sub_nat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : Nat) : f (x - n) = f x - n • b := by
  simpa using map_sub_nsmul f x n

@[scoped simp]
/--
theorem `map_sub_ofNat'` / 定理 `map_sub_ofNat'`

English:
theorem map_sub_ofNat'
  statement: [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
  proof: map_sub_nat' f x n

@[scoped simp]

中文:
定理 map_sub_of自然数'
  结论: [加法带幺群 G] [加法群 H] [加法余nst映射类 F G H 1 b]
  证明: map_sub_nat' f x n

@[scoped simp]

Depends on / 依赖: map_sub_nat
-/
theorem map_sub_ofNat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : Nat) [n.AtLeastTwo] :
    f (x - ofNat(n)) = f x - ofNat(n) • b :=
  map_sub_nat' f x n

@[scoped simp]
/--
theorem `map_add_zsmul` / 定理 `map_add_zsmul`

English:
theorem map_add_zsmul
  statement: [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]

中文:
定理 map_add_zsmul
  结论: [加法群 G] [加法群 H] [加法余nst映射类 F G H a b]
-/
theorem map_add_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : forall n : Int, f (x + n • a) = f x + n • b
  | (n : Nat) => by simp
  | .negSucc n => by simp [← sub_eq_add_neg]

@[scoped simp]
/--
theorem `map_zsmul_const` / 定理 `map_zsmul_const`

English:
theorem map_zsmul_const
  statement: [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
  proof: by
  simpa using map_add_zsmul f 0 n

@[scoped simp]

中文:
定理 map_zsmul_const
  结论: [加法群 G] [加法群 H] [加法余nst映射类 F G H a b]
  证明: by
  simpa using map_add_zsmul f 0 n

@[scoped simp]

Depends on / 依赖: map_add_zsmul
-/
theorem map_zsmul_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : Int) : f (n • a) = f 0 + n • b := by
  simpa using map_add_zsmul f 0 n

@[scoped simp]
/--
theorem `map_add_int'` / 定理 `map_add_int'`

English:
theorem map_add_int'
  statement: [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
  proof: by
  rw [← map_add_zsmul f x n]; rw [zsmul_one]

中文:
定理 map_add_int'
  结论: [加法带幺群 G] [加法群 H] [加法余nst映射类 F G H 1 b]
  证明: by
  rw [← map_add_zsmul f x n]; rw [zsmul_one]

Depends on / 依赖: map_add_zsmul, zsmul_one
-/
theorem map_add_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : Int) : f (x + n) = f x + n • b := by
  rw [← map_add_zsmul f x n]; rw [zsmul_one]

/--
theorem `map_add_int` / 定理 `map_add_int`

English:
theorem map_add_int
  statement: [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
  proof: by simp

@[scoped simp]

中文:
定理 map_add_int
  结论: [加法带幺群 G] [加法带幺群 H] [加法余nst映射类 F G H 1 1]
  证明: by simp

@[scoped simp]
-/
theorem map_add_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : Int) : f (x + n) = f x + n := by simp

@[scoped simp]
/--
theorem `map_sub_zsmul` / 定理 `map_sub_zsmul`

English:
theorem map_sub_zsmul
  statement: [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
  proof: by
  simpa [sub_eq_add_neg] using map_add_zsmul f x (-n)

@[scoped simp]

中文:
定理 map_sub_zsmul
  结论: [加法群 G] [加法群 H] [加法余nst映射类 F G H a b]
  证明: by
  simpa [sub_eq_add_neg] using map_add_zsmul f x (-n)

@[scoped simp]

Depends on / 依赖: map_add_zsmul, sub_eq_add_neg
-/
theorem map_sub_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : Int) : f (x - n • a) = f x - n • b := by
  simpa [sub_eq_add_neg] using map_add_zsmul f x (-n)

@[scoped simp]
/--
theorem `map_sub_int'` / 定理 `map_sub_int'`

English:
theorem map_sub_int'
  statement: [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
  proof: by
  rw [← map_sub_zsmul]; rw [zsmul_one]

中文:
定理 map_sub_int'
  结论: [加法带幺群 G] [加法群 H] [加法余nst映射类 F G H 1 b]
  证明: by
  rw [← map_sub_zsmul]; rw [zsmul_one]

Depends on / 依赖: map_sub_zsmul, zsmul_one
-/
theorem map_sub_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : Int) : f (x - n) = f x - n • b := by
  rw [← map_sub_zsmul]; rw [zsmul_one]

/--
theorem `map_sub_int` / 定理 `map_sub_int`

English:
theorem map_sub_int
  statement: [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
  proof: by simp

@[scoped simp]

中文:
定理 map_sub_int
  结论: [加法带幺群 G] [加法带幺群 H] [加法余nst映射类 F G H 1 1]
  证明: by simp

@[scoped simp]
-/
theorem map_sub_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : Int) : f (x - n) = f x - n := by simp

@[scoped simp]
/--
theorem `map_zsmul_add` / 定理 `map_zsmul_add`

English:
theorem map_zsmul_add
  statement: [AddCommGroup G] [AddGroup H] [AddConstMapClass F G H a b]
  proof: by
  rw [add_comm]; rw [map_add_zsmul]

@[scoped simp]

中文:
定理 map_zsmul_add
  结论: [加法交换群 G] [加法群 H] [加法余nst映射类 F G H a b]
  证明: by
  rw [add_comm]; rw [map_add_zsmul]

@[scoped simp]

Depends on / 依赖: add_comm, map_add_zsmul
-/
theorem map_zsmul_add [AddCommGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : Int) (x : G) : f (n • a + x) = f x + n • b := by
  rw [add_comm]; rw [map_add_zsmul]

@[scoped simp]
/--
theorem `map_int_add'` / 定理 `map_int_add'`

English:
theorem map_int_add'
  statement: [AddCommGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
  proof: by
  rw [← map_zsmul_add]; rw [zsmul_one]

中文:
定理 map_int_add'
  结论: [加法交换带幺群 G] [加法群 H] [加法余nst映射类 F G H 1 b]
  证明: by
  rw [← map_zsmul_add]; rw [zsmul_one]

Depends on / 依赖: map_zsmul_add, zsmul_one
-/
theorem map_int_add' [AddCommGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (n : Int) (x : G) : f (↑n + x) = f x + n • b := by
  rw [← map_zsmul_add]; rw [zsmul_one]

/--
theorem `map_int_add` / 定理 `map_int_add`

English:
theorem map_int_add
  statement: [AddCommGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
  proof: by simp

中文:
定理 map_int_add
  结论: [加法交换带幺群 G] [加法带幺群 H] [加法余nst映射类 F G H 1 1]
  证明: by simp
-/
theorem map_int_add [AddCommGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : Int) (x : G) : f (↑n + x) = f x + n := by simp

/--
theorem `map_fract` / 定理 `map_fract`

English:
theorem map_fract
  statement: {R : Type*} [Ring R] [LinearOrder R] [FloorRing R] [AddGroup H]
  proof: map_sub_int' ..

中文:
定理 map_fract
  结论: {R : 类型} [环 R] [线性序 R] [Floor环 R] [加法群 H]
  证明: map_sub_int' ..

Depends on / 依赖: map_sub_int
-/
theorem map_fract {R : Type*} [Ring R] [LinearOrder R] [FloorRing R] [AddGroup H]
    [FunLike F R H] [AddConstMapClass F R H 1 b] (f : F) (x : R) :
    f (Int.fract x) = f x - ⌊x⌋ • b :=
  map_sub_int' ..

open scoped Relator in
/--
theorem `rel_map_of_Icc` / 定理 `rel_map_of_Icc`

English:
theorem rel_map_of_Icc
  statement: [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  proof: fun x y hxy => by
  replace hR := hR.elim
  have ha' : 0 <= a := ha.le
  -- Shift both points by `m • a` so that `l ≤ x < l + a`
  wlog hx : x in Ico l (l + a) generalizing x y
  · rcases existsUnique_sub_zsmul_mem_Ico ha x l with ⟨m, hm, -⟩
    suffices R (f (x - m • a)) (f (y - m • a)) by simpa us

中文:
定理 rel_map_of_Icc
  结论: [加法交换群 G] [线性序 G] [是OrderedAdd幺半群 G]
  证明: fun x y hxy => by
  replace hR := hR.elim
  have ha' : 0 <= a := ha.le
  -- Shift both points by `m • a` so that `l ≤ x < l + a`
  wlog hx : x in Ico l (l + a) generalizing x y
  · rcases existsUnique_sub_zsmul_mem_Ico ha x l with ⟨m, hm, -⟩
    suffices R (f (x - m • a)) (f (y - m • a)) by simpa us
-/
protected theorem rel_map_of_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Archimedean G] [AddGroup H]
    [AddConstMapClass F G H a b] {f : F} {R : H -> H -> Prop} [IsTrans H R]
    [hR : CovariantClass H H (fun x y => y + x) R] (ha : 0 < a) {l : G}
    (hf : forall x in Icc l (l + a), forall y in Icc l (l + a), x < y -> R (f x) (f y)) :
    ((· < ·) ⇒ R) f f := fun x y hxy => by
  replace hR := hR.elim
  have ha' : 0 <= a := ha.le
  -- Shift both points by `m • a` so that `l ≤ x < l + a`
  wlog hx : x in Ico l (l + a) generalizing x y
  · rcases existsUnique_sub_zsmul_mem_Ico ha x l with ⟨m, hm, -⟩
    suffices R (f (x - m • a)) (f (y - m • a)) by simpa using hR (m • b) this
    exact this _ _ (by simpa) hm
  · -- Now find `n` such that `l + n • a < y ≤ l + (n + 1) • a`
    rcases existsUnique_sub_zsmul_mem_Ioc ha y l with ⟨n, hny, -⟩
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · -- Since `l ≤ x ≤ y`, the case `n < 0` is impossible
      refine absurd ?_ hxy.not_ge
      calc
        y <= l + a + n • a := sub_le_iff_le_add.1 hny.2
        _ = l + (n + 1) • a := by rw [add_comm n, add_smul, one_smul, add_assoc]
        _ <= l + (0 : Int) • a := by gcongr; lia
        _ <= x := by simpa using hx.1
    · -- If `n = 0`, then `l < y ≤ l + a`, hence we can apply the assumption
      exact hf x (Ico_subset_Icc_self hx) y (by simpa using Ioc_subset_Icc_self hny) hxy
    · -- In the remaining case `0 < n` we use transitivity.
      -- If `R = (· < ·)`, then the proof looks like
      -- `f x < f (l + a) ≤ f (l + n • a) < f y`
      trans f (l + (1 : Int) • a)
      · grind
      have hy : R (f (l + n • a)) (f y) := by
        rw [← sub_add_cancel y (n • a)]; rw [map_add_zsmul]; rw [map_add_zsmul]
refine hR _ hf _ ?_ _ (Ioc_subset_Icc_self hny) hny.1; simpa
      rw [← Int.add_one_le_iff]; rw [zero_add] at hn
      rcases hn.eq_or_lt with rfl | hn; · assumption
      trans f (l + n • a)
      · refine Int.rel_of_forall_rel_succ_of_lt R (f := (f <| l + · • a)) (fun k => ?_) hn
        simp_rw [add_comm k 1, add_zsmul, ← add_assoc, one_zsmul, map_add_zsmul]
        refine hR (k • b) (hf _ ?_ _ ?_ ?_) <;> simpa
      · assumption

/--
theorem `monotone_iff_Icc` / 定理 `monotone_iff_Icc`

English:
theorem monotone_iff_Icc
  statement: [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
  proof: ⟨(Monotone.monotoneOn · _), fun hf => monotone_iff_forall_lt.2
    AddConstMapClass.rel_map_of_Icc ha fun _x hx _y hy hxy => hf hx hy hxy.le⟩

中文:
定理 monotone_iff_Icc
  结论: [加法交换群 G] [线性序 G] [是OrderedAdd幺半群 G] [阿基米德 G]
  证明: ⟨(Monotone.monotoneOn · _), fun hf => monotone_iff_forall_lt.2
    AddConstMapClass.rel_map_of_Icc ha fun _x hx _y hy hxy => hf hx hy hxy.le⟩

Depends on / 依赖: AddConstMapClass, AddConstMapClass.rel_map_of_Icc, Monotone, Monotone.monotoneOn, hxy.le, monotoneOn, monotone_iff_forall_lt, rel_map_of_Icc
-/
theorem monotone_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    Monotone f ↔ MonotoneOn f (Icc l (l + a)) :=
⟨(Monotone.monotoneOn · _), fun hf => monotone_iff_forall_lt.2
    AddConstMapClass.rel_map_of_Icc ha fun _x hx _y hy hxy => hf hx hy hxy.le⟩

/--
theorem `antitone_iff_Icc` / 定理 `antitone_iff_Icc`

English:
theorem antitone_iff_Icc
  statement: [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
  proof: monotone_iff_Icc (H := Hᵒᵈ) ha l

中文:
定理 antitone_iff_Icc
  结论: [加法交换群 G] [线性序 G] [是OrderedAdd幺半群 G] [阿基米德 G]
  证明: monotone_iff_Icc (H := Hᵒᵈ) ha l

Depends on / 依赖: monotone_iff_Icc
-/
theorem antitone_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    Antitone f ↔ AntitoneOn f (Icc l (l + a)) :=
  monotone_iff_Icc (H := Hᵒᵈ) ha l

/--
theorem `strictMono_iff_Icc` / 定理 `strictMono_iff_Icc`

English:
theorem strictMono_iff_Icc
  statement: [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
  proof: ⟨(StrictMono.strictMonoOn · _), AddConstMapClass.rel_map_of_Icc ha⟩

中文:
定理 strictMono_iff_Icc
  结论: [加法交换群 G] [线性序 G] [是OrderedAdd幺半群 G] [阿基米德 G]
  证明: ⟨(StrictMono.strictMonoOn · _), AddConstMapClass.rel_map_of_Icc ha⟩

Depends on / 依赖: AddConstMapClass, AddConstMapClass.rel_map_of_Icc, StrictMono, StrictMono.strictMonoOn, rel_map_of_Icc, strictMonoOn
-/
theorem strictMono_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    StrictMono f ↔ StrictMonoOn f (Icc l (l + a)) :=
  ⟨(StrictMono.strictMonoOn · _), AddConstMapClass.rel_map_of_Icc ha⟩

/--
theorem `strictAnti_iff_Icc` / 定理 `strictAnti_iff_Icc`

English:
theorem strictAnti_iff_Icc
  statement: [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
  proof: strictMono_iff_Icc (H := Hᵒᵈ) ha l

中文:
定理 strictAnti_iff_Icc
  结论: [加法交换群 G] [线性序 G] [是OrderedAdd幺半群 G] [阿基米德 G]
  证明: strictMono_iff_Icc (H := Hᵒᵈ) ha l

Depends on / 依赖: strictMono_iff_Icc
-/
theorem strictAnti_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    StrictAnti f ↔ StrictAntiOn f (Icc l (l + a)) :=
  strictMono_iff_Icc (H := Hᵒᵈ) ha l

end AddConstMapClass

open AddConstMapClass

namespace AddConstMap

section Add

variable {G H : Type*} [Add G] [Add H] {a : G} {b : H}


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (G ->+c[a, b] H) G H
  body: AddConstMap.toFun
  coe_injective | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

中文:
实例 :
  签名: 函数状 (G ->+c[a, b] H) G H
  定义体: AddConstMap.toFun
  coe_injective | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

Depends on / 依赖: AddConstMap, AddConstMap.toFun
-/
instance : FunLike (G ->+c[a, b] H) G H where
  coe := AddConstMap.toFun
  coe_injective | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : G -> H) (hf)
  statement: ⇑(mk f hf : G ->+c[a, b] H) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : G -> H) (hf)
  结论: ⇑(mk f hf : G ->+c[a, b] H) = f
  证明: rfl
-/
@[simp, push_cast] theorem coe_mk (f : G -> H) (hf) : ⇑(mk f hf : G ->+c[a, b] H) = f := rfl
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : G ->+c[a, b] H)
  statement: mk f f.2 = f
  proof: rfl

中文:
定理 mk_coe
  条件: (f : G ->+c[a, b] H)
  结论: mk f f.2 = f
  证明: rfl
-/
@[simp] theorem mk_coe (f : G ->+c[a, b] H) : mk f f.2 = f := rfl
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : G ->+c[a, b] H)
  statement: f.toFun = f
  proof: rfl

中文:
定理 toFun_eq_coe
  条件: (f : G ->+c[a, b] H)
  结论: f.toFun = f
  证明: rfl
-/
@[simp] theorem toFun_eq_coe (f : G ->+c[a, b] H) : f.toFun = f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddConstMapClass (G ->+c[a, b] H) G H a b
  body: f.map_add_const'

中文:
实例 :
  签名: 加法余nst映射类 (G ->+c[a, b] H) G H a b
  定义体: f.map_add_const'

Depends on / 依赖: f.map_add_const, map_add_const
-/
instance : AddConstMapClass (G ->+c[a, b] H) G H a b where
  map_add_const f := f.map_add_const'

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : G ->+c[a, b] H} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ h

initialize_simps_projections AddConstMap (toFun -> coe, as_prefix coe)

中文:
定理 ext
  条件: {f g : G ->+c[a, b] H} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ h

initialize_simps_projections AddConstMap (toFun -> coe, as_prefix coe)
-/
@[ext] protected theorem ext {f g : G ->+c[a, b] H} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

initialize_simps_projections AddConstMap (toFun -> coe, as_prefix coe)

/-!
### Constructions about `G →+c[a, b] H`
-/

/-- The identity map as `G →+c[a, a] G`. -/
@[simps -fullyApplied]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : G ->+c[a, a] G
  body: ⟨id, fun _ => rfl⟩

中文:
定义 id
  签名: : G ->+c[a, a] G
  定义体: ⟨id, fun _ => rfl⟩
-/
protected def id : G ->+c[a, a] G := ⟨id, fun _ => rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (G ->+c[a, a] G)
  body: ⟨.id⟩

中文:
实例 :
  签名: 可居 (G ->+c[a, a] G)
  定义体: ⟨.id⟩
-/
instance : Inhabited (G ->+c[a, a] G) := ⟨.id⟩

/-- Composition of two `AddConstMap`s. -/
@[simps -fullyApplied]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {K : Type*} [Add K] {c : K} (g : H ->+c[b, c] K) (f : G ->+c[a, b] H)
  body: ⟨g ∘ f, by simp⟩

中文:
定义 comp
  签名: {K : 类型} [加法 K] {c : K} (g : H ->+c[b, c] K) (f : G ->+c[a, b] H)
  定义体: ⟨g ∘ f, by simp⟩
-/
def comp {K : Type*} [Add K] {c : K} (g : H ->+c[b, c] K) (f : G ->+c[a, b] H) :
    G ->+c[a, c] K :=
  ⟨g ∘ f, by simp⟩

/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : G ->+c[a, b] H)
  statement: f.comp .id = f
  proof: rfl

中文:
定理 comp_id
  条件: (f : G ->+c[a, b] H)
  结论: f.comp .id = f
  证明: rfl
-/
@[simp] theorem comp_id (f : G ->+c[a, b] H) : f.comp .id = f := rfl
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : G ->+c[a, b] H)
  statement: .comp .id f = f
  proof: rfl

中文:
定理 id_comp
  条件: (f : G ->+c[a, b] H)
  结论: .comp .id f = f
  证明: rfl
-/
@[simp] theorem id_comp (f : G ->+c[a, b] H) : .comp .id f = f := rfl

/-- Change constants `a` and `b` in `(f : G →+c[a, b] H)` to improve definitional equalities. -/
@[simps -fullyApplied]
/--
Definition of `replaceConsts` / `replaceConsts` 的定义

English:
definition replaceConsts
  signature: (f : G ->+c[a, b] H) (a' b') (ha : a = a') (hb : b = b')
  body: f
  map_add_const' := ha ▸ hb ▸ f.map_add_const'

中文:
定义 replaceConsts
  签名: (f : G ->+c[a, b] H) (a' b') (ha : a = a') (hb : b = b')
  定义体: f
  map_add_const' := ha ▸ hb ▸ f.map_add_const'
-/
def replaceConsts (f : G ->+c[a, b] H) (a' b') (ha : a = a') (hb : b = b') :
    G ->+c[a', b'] H where
  toFun := f
  map_add_const' := ha ▸ hb ▸ f.map_add_const'

/-!
### Additive action on `G →+c[a, b] H`
-/

/-- If `f` is an `AddConstMap`, then so is `(c +ᵥ f ·)`. -/
instance {K : Type*} [VAdd K H] [VAddAssocClass K H H] : VAdd K (G ->+c[a, b] H) :=
  ⟨fun c f => ⟨c +ᵥ ⇑f, fun x => by simp [vadd_add_assoc]⟩⟩

@[simp, norm_cast]
/--
theorem `coe_vadd` / 定理 `coe_vadd`

English:
theorem coe_vadd
  given: {K : Type*} [VAdd K H] [VAddAssocClass K H H] (c : K) (f : G ->+c[a, b] H)
  proof: rfl

中文:
定理 coe_vadd
  条件: {K : 类型} [向量加法 K H] [VAddAssoc类 K H H] (c : K) (f : G ->+c[a, b] H)
  证明: rfl
-/
theorem coe_vadd {K : Type*} [VAdd K H] [VAddAssocClass K H H] (c : K) (f : G ->+c[a, b] H) :
    ⇑(c +ᵥ f) = c +ᵥ ⇑f :=
  rfl

instance {K : Type*} [AddMonoid K] [AddAction K H] [VAddAssocClass K H H] :
    AddAction K (G ->+c[a, b] H) :=
  DFunLike.coe_injective.addAction _ coe_vadd


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (G ->+c[a, a] G)
  body: ⟨comp⟩

中文:
实例 :
  签名: 乘法 (G ->+c[a, a] G)
  定义体: ⟨comp⟩
-/
instance : Mul (G ->+c[a, a] G) := ⟨comp⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (G ->+c[a, a] G)
  body: ⟨.id⟩

中文:
实例 :
  签名: 幺 (G ->+c[a, a] G)
  定义体: ⟨.id⟩
-/
instance : One (G ->+c[a, a] G) := ⟨.id⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (G ->+c[a, a] G) Nat
  body: ⟨f^[n], Commute.iterate_left (AddConstMapClass.semiconj f) _⟩

中文:
实例 :
  签名: 幂 (G ->+c[a, a] G) 自然数
  定义体: ⟨f^[n], Commute.iterate_left (AddConstMapClass.semiconj f) _⟩

Depends on / 依赖: AddConstMapClass, AddConstMapClass.semiconj, Commute, Commute.iterate_left, iterate_left, semiconj
-/
instance : Pow (G ->+c[a, a] G) Nat where
  pow f n := ⟨f^[n], Commute.iterate_left (AddConstMapClass.semiconj f) _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (G ->+c[a, a] G)
  body: DFunLike.coe_injective.monoid (M₂ := Function.End G) _ rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 :
  签名: 幺半群 (G ->+c[a, a] G)
  定义体: DFunLike.coe_injective.monoid (M₂ := Function.End G) _ rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.monoid, Function, Function.End, coe_injective, monoid
-/
instance : Monoid (G ->+c[a, a] G) :=
  DFunLike.coe_injective.monoid (M₂ := Function.End G) _ rfl (fun _ _ => rfl) fun _ _ => rfl

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (f g : G ->+c[a, a] G)
  statement: f * g = f.comp g
  proof: rfl

中文:
定理 mul_def
  条件: (f g : G ->+c[a, a] G)
  结论: f * g = f.comp g
  证明: rfl
-/
theorem mul_def (f g : G ->+c[a, a] G) : f * g = f.comp g := rfl
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (f g : G ->+c[a, a] G)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

中文:
定理 coe_mul
  条件: (f g : G ->+c[a, a] G)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl
-/
@[simp, push_cast] theorem coe_mul (f g : G ->+c[a, a] G) : ⇑(f * g) = f ∘ g := rfl

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : G ->+c[a, a] G) = .id
  proof: rfl

中文:
定理 one_def
  结论: (1 : G ->+c[a, a] G) = .id
  证明: rfl
-/
theorem one_def : (1 : G ->+c[a, a] G) = .id := rfl
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : G ->+c[a, a] G) = id
  proof: rfl

中文:
定理 coe_one
  结论: ⇑(1 : G ->+c[a, a] G) = id
  证明: rfl
-/
@[simp, push_cast] theorem coe_one : ⇑(1 : G ->+c[a, a] G) = id := rfl

/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (f : G ->+c[a, a] G) (n : Nat)
  statement: ⇑(f ^ n) = f^[n]
  proof: rfl

中文:
定理 coe_pow
  条件: (f : G ->+c[a, a] G) (n : 自然数)
  结论: ⇑(f ^ n) = f^[n]
  证明: rfl
-/
@[simp, push_cast] theorem coe_pow (f : G ->+c[a, a] G) (n : Nat) : ⇑(f ^ n) = f^[n] := rfl

/--
theorem `pow_apply` / 定理 `pow_apply`

English:
theorem pow_apply
  given: (f : G ->+c[a, a] G) (n : Nat) (x : G)
  statement: (f ^ n) x = f^[n] x
  proof: rfl

中文:
定理 pow_apply
  条件: (f : G ->+c[a, a] G) (n : 自然数) (x : G)
  结论: (f ^ n) x = f^[n] x
  证明: rfl
-/
theorem pow_apply (f : G ->+c[a, a] G) (n : Nat) (x : G) : (f ^ n) x = f^[n] x := rfl

/-- Coercion to functions as a monoid homomorphism to `Function.End G`. -/
@[simps -fullyApplied]
/--
Definition of `toEnd` / `toEnd` 的定义

English:
definition toEnd
  signature: : (G ->+c[a, a] G) ->* Function.End G where
  body: DFunLike.coe
  map_mul' _ _ := rfl
  map_one' := rfl

中文:
定义 toEnd
  签名: : (G ->+c[a, a] G) ->* 函数.End G where
  定义体: DFunLike.coe
  map_mul' _ _ := rfl
  map_one' := rfl

Depends on / 依赖: DFunLike, DFunLike.coe
-/
def toEnd : (G ->+c[a, a] G) ->* Function.End G where
  toFun := DFunLike.coe
  map_mul' _ _ := rfl
  map_one' := rfl

end Add

section AddZeroClass

variable {G H K : Type*} [Add G] [AddZeroClass H] {a : G} {b : H}

/-!
### Multiplicative action on `(b : H) × (G →+c[a, b] H)`

If `K` acts distributively on `H`, then for each `f : G →+c[a, b] H`
we define `(AddConstMap.smul c f : G →+c[a, c • b] H)`.

One can show that this defines a multiplicative action of `K` on `(b : H) × (G →+c[a, b] H)`
but we don't do this at the moment because we don't need this.
-/

/-- Pointwise scalar multiplication of `f : G →+c[a, b] H` as a map `G →+c[a, c • b] H`. -/
@[simps -fullyApplied]
/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: [DistribSMul K H] (c : K) (f : G ->+c[a, b] H)
  body: c • ⇑f
  map_add_const' x := by simp [smul_add]

中文:
定义 smul
  签名: [分配标量乘法 K H] (c : K) (f : G ->+c[a, b] H)
  定义体: c • ⇑f
  map_add_const' x := by simp [smul_add]
-/
def smul [DistribSMul K H] (c : K) (f : G ->+c[a, b] H) : G ->+c[a, c • b] H where
  toFun := c • ⇑f
  map_add_const' x := by simp [smul_add]

end AddZeroClass

section AddMonoid

variable {G : Type*} [AddMonoid G] {a : G}

/-- The map that sends `c` to a translation by `c`
as a monoid homomorphism from `Multiplicative G` to `G →+c[a, a] G`. -/
@[simps! -fullyApplied]
/--
Definition of `addLeftHom` / `addLeftHom` 的定义

English:
definition addLeftHom
  signature: : Multiplicative G ->* (G ->+c[a, a] G) where
  body: c.toAdd +ᵥ .id
  map_one' := by ext; apply zero_add
  map_mul' _ _ := by ext; apply add_assoc

中文:
定义 addLeftHom
  签名: : Multiplicative G ->* (G ->+c[a, a] G) where
  定义体: c.toAdd +ᵥ .id
  map_one' := by ext; apply zero_add
  map_mul' _ _ := by ext; apply add_assoc

Depends on / 依赖: c.toAdd
-/
def addLeftHom : Multiplicative G ->* (G ->+c[a, a] G) where
  toFun c := c.toAdd +ᵥ .id
  map_one' := by ext; apply zero_add
  map_mul' _ _ := by ext; apply add_assoc

end AddMonoid

section AddCommGroup

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] {a : G} {b : H}

/-- If `f : G → H` is an `AddConstMap`, then so is `fun x ↦ -f (-x)`. -/
@[simps! apply_coe]
/--
Definition of `conjNeg` / `conjNeg` 的定义

English:
definition conjNeg
  signature: : (G ->+c[a, b] H) ≃ (G ->+c[a, b] H)
  body: Involutive.toPerm (fun f => ⟨fun x => - f (-x), fun _ => by simp [neg_add_eq_sub]⟩) fun _ =>
    AddConstMap.ext fun _ => by simp

中文:
定义 conjNeg
  签名: : (G ->+c[a, b] H) ≃ (G ->+c[a, b] H)
  定义体: Involutive.toPerm (fun f => ⟨fun x => - f (-x), fun _ => by simp [neg_add_eq_sub]⟩) fun _ =>
    AddConstMap.ext fun _ => by simp

Depends on / 依赖: AddConstMap, AddConstMap.ext, Involutive, Involutive.toPerm, neg_add_eq_sub, toPerm
-/
def conjNeg : (G ->+c[a, b] H) ≃ (G ->+c[a, b] H) :=
  Involutive.toPerm (fun f => ⟨fun x => - f (-x), fun _ => by simp [neg_add_eq_sub]⟩) fun _ =>
    AddConstMap.ext fun _ => by simp

/--
theorem `conjNeg_symm` / 定理 `conjNeg_symm`

English:
theorem conjNeg_symm
  statement: (conjNeg (a := a) (b := b)).symm = conjNeg
  proof: rfl

中文:
定理 conjNeg_symm
  结论: (conjNeg (a := a) (b := b)).symm = conjNeg
  证明: rfl
-/
@[simp] theorem conjNeg_symm : (conjNeg (a := a) (b := b)).symm = conjNeg := rfl

end AddCommGroup

section FloorRing

variable {R G : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [AddGroup G]
  (a : G)

/--
Definition of `mkFract` / `mkFract` 的定义

English:
definition mkFract
  signature: : (Ico (0 : R) 1 -> G) ≃ (R ->+c[1, a] G) where
  body: ⟨fun x => f ⟨Int.fract x, Int.fract_nonneg _, Int.fract_lt_one _⟩ + ⌊x⌋ • a, fun x => by
    simp [add_one_zsmul, add_assoc]⟩
  invFun f x := f x
  left_inv _ := by ext x; simp [Int.fract_eq_self.2 x.2, Int.floor_eq_zero_iff.2 x.2]
  right_inv f := by ext x; simp [map_fract]

中文:
定义 mkFract
  签名: : (左闭右开区间 (0 : R) 1 -> G) ≃ (R ->+c[1, a] G) where
  定义体: ⟨fun x => f ⟨Int.fract x, Int.fract_nonneg _, Int.fract_lt_one _⟩ + ⌊x⌋ • a, fun x => by
    simp [add_one_zsmul, add_assoc]⟩
  invFun f x := f x
  left_inv _ := by ext x; simp [Int.fract_eq_self.2 x.2, Int.floor_eq_zero_iff.2 x.2]
  right_inv f := by ext x; simp [map_fract]

Depends on / 依赖: Int.floor_eq_zero_iff, Int.fract, Int.fract_eq_self, Int.fract_lt_one, Int.fract_nonneg, add_assoc, add_one_zsmul, floor_eq_zero_iff, fract_eq_self, fract_lt_one, fract_nonneg, invFun, left_inv, map_fract, right_inv
-/
def mkFract : (Ico (0 : R) 1 -> G) ≃ (R ->+c[1, a] G) where
  toFun f := ⟨fun x => f ⟨Int.fract x, Int.fract_nonneg _, Int.fract_lt_one _⟩ + ⌊x⌋ • a, fun x => by
    simp [add_one_zsmul, add_assoc]⟩
  invFun f x := f x
  left_inv _ := by ext x; simp [Int.fract_eq_self.2 x.2, Int.floor_eq_zero_iff.2 x.2]
  right_inv f := by ext x; simp [map_fract]

end FloorRing

end AddConstMap
