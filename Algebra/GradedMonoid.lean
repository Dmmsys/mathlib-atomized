/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Additively-graded multiplicative structures

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `GradedMonoid A` such that `(*) : A i → A j → A (i + j)`; that is to say, `A`
forms an additively-graded monoid. The typeclasses are:

* `GradedMonoid.GOne A`
* `GradedMonoid.GMul A`
* `GradedMonoid.GMonoid A`
* `GradedMonoid.GCommMonoid A`

These respectively imbue:

* `One (GradedMonoid A)`
* `Mul (GradedMonoid A)`
* `Monoid (GradedMonoid A)`
* `CommMonoid (GradedMonoid A)`

the base type `A 0` with:

* `GradedMonoid.GradeZero.One`
* `GradedMonoid.GradeZero.Mul`
* `GradedMonoid.GradeZero.Monoid`
* `GradedMonoid.GradeZero.CommMonoid`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* (nothing)
* `GradedMonoid.GradeZero.SMul (A 0)`
* `GradedMonoid.GradeZero.MulAction (A 0)`
* (nothing)

For now, these typeclasses are primarily used in the construction of `DirectSum.Ring` and the rest
of that file.

## Dependent graded products

This also introduces `List.dProd`, which takes the (possibly non-commutative) product of a list
of graded elements of type `A i`. This definition primarily exists to allow `GradedMonoid.mk`
and `DirectSum.of` to be pulled outside a product, such as in `GradedMonoid.mk_list_dProd` and
`DirectSum.of_list_dProd`.

## Internally graded monoids

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`SetLike` subobjects (such as `AddSubmonoid`s, `AddSubgroup`s, or `Submodule`s), this file
provides the `Prop` typeclasses:

* `SetLike.GradedOne A` (which provides the obvious `GradedMonoid.GOne A` instance)
* `SetLike.GradedMul A` (which provides the obvious `GradedMonoid.GMul A` instance)
* `SetLike.GradedMonoid A` (which provides the obvious `GradedMonoid.GMonoid A` and
  `GradedMonoid.GCommMonoid A` instances)

which respectively provide the API lemmas

* `SetLike.one_mem_graded`
* `SetLike.mul_mem_graded`
* `SetLike.pow_mem_graded`, `SetLike.list_prod_map_mem_graded`

Strictly this last class is unnecessary as it has no fields not present in its parents, but it is
included for convenience. Note that there is no need for `SetLike.GradedRing` or similar, as all
the information it would contain is already supplied by `GradedMonoid` when `A` is a collection
of objects satisfying `AddSubmonoidClass` such as `Submodule`s. These constructions are explored
in `Algebra.DirectSum.Internal`.

This file also defines:

* `SetLike.IsHomogeneousElem A` (which says that `a` is homogeneous iff `a ∈ A i` for some `i : ι`)
* `SetLike.homogeneousSubmonoid A`, which is, as the name suggests, the submonoid consisting of
  all the homogeneous elements.

## Tags

graded monoid
-/

@[expose] public section


variable {ι : Type*}

/--
Definition of `GradedMonoid` / `GradedMonoid` 的定义

English:
definition GradedMonoid
  signature: (A : ι -> Type*)
  body: Sigma A

中文:
定义 分次幺半群
  签名: (A : ι -> 类型)
  定义体: Sigma A
-/
def GradedMonoid (A : ι -> Type*) :=
  Sigma A

namespace GradedMonoid

instance {A : ι -> Type*} [Inhabited ι] [Inhabited (A default)] : Inhabited (GradedMonoid A) :=
inferInstanceAs Inhabited (Sigma _)

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {A : ι -> Type*}
  body: Sigma.mk

中文:
定义 mk
  签名: {A : ι -> 类型}
  定义体: Sigma.mk

Depends on / 依赖: Sigma.mk
-/
def mk {A : ι -> Type*} : forall i, A i -> GradedMonoid A :=
  Sigma.mk

/-! ### Actions -/

section actions
variable {α β} {A : ι -> Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, SMul α (A i)] : SMul α (GradedMonoid A) where
  body: GradedMonoid.mk g.1 (r • g.2)

中文:
实例 [对任意
  签名: i, 标量乘法 α (A i)] : 标量乘法 α (分次幺半群 A) where
  定义体: GradedMonoid.mk g.1 (r • g.2)

Depends on / 依赖: GradedMonoid, GradedMonoid.mk
-/
instance [forall i, SMul α (A i)] : SMul α (GradedMonoid A) where
  smul r g := GradedMonoid.mk g.1 (r • g.2)

/--
theorem `fst_smul` / 定理 `fst_smul`

English:
theorem fst_smul
  given: [forall i, SMul α (A i)] (a : α) (x : GradedMonoid A)
  proof: rfl

中文:
定理 fst_smul
  条件: [对任意 i, 标量乘法 α (A i)] (a : α) (x : 分次幺半群 A)
  证明: rfl
-/
@[simp] theorem fst_smul [forall i, SMul α (A i)] (a : α) (x : GradedMonoid A) :
    (a • x).fst = x.fst := rfl

/--
theorem `snd_smul` / 定理 `snd_smul`

English:
theorem snd_smul
  given: [forall i, SMul α (A i)] (a : α) (x : GradedMonoid A)
  proof: rfl

中文:
定理 snd_smul
  条件: [对任意 i, 标量乘法 α (A i)] (a : α) (x : 分次幺半群 A)
  证明: rfl
-/
@[simp] theorem snd_smul [forall i, SMul α (A i)] (a : α) (x : GradedMonoid A) :
    (a • x).snd = a • x.snd := rfl

/--
theorem `smul_mk` / 定理 `smul_mk`

English:
theorem smul_mk
  given: [forall i, SMul α (A i)] {i} (c : α) (a : A i)
  proof: rfl

中文:
定理 smul_mk
  条件: [对任意 i, 标量乘法 α (A i)] {i} (c : α) (a : A i)
  证明: rfl
-/
theorem smul_mk [forall i, SMul α (A i)] {i} (c : α) (a : A i) :
    c • mk i a = mk i (c • a) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, SMul α (A i)] [forall i, SMul β (A i)]
  body: Sigma.ext rfl heq_of_eq smul_comm a b g.2

中文:
实例 [对任意
  签名: i, 标量乘法 α (A i)] [对任意 i, 标量乘法 β (A i)]
  定义体: Sigma.ext rfl heq_of_eq smul_comm a b g.2

Depends on / 依赖: Sigma.ext, heq_of_eq, smul_comm
-/
instance [forall i, SMul α (A i)] [forall i, SMul β (A i)]
    [forall i, SMulCommClass α β (A i)] :
    SMulCommClass α β (GradedMonoid A) where
smul_comm a b g := Sigma.ext rfl heq_of_eq smul_comm a b g.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: α β] [forall i, SMul α (A i)] [forall i, SMul β (A i)]
  body: Sigma.ext rfl heq_of_eq smul_assoc a b g.2

中文:
实例 [标量乘法
  签名: α β] [对任意 i, 标量乘法 α (A i)] [对任意 i, 标量乘法 β (A i)]
  定义体: Sigma.ext rfl heq_of_eq smul_assoc a b g.2

Depends on / 依赖: Sigma.ext, heq_of_eq, smul_assoc
-/
instance [SMul α β] [forall i, SMul α (A i)] [forall i, SMul β (A i)]
    [forall i, IsScalarTower α β (A i)] :
    IsScalarTower α β (GradedMonoid A) where
smul_assoc a b g := Sigma.ext rfl heq_of_eq smul_assoc a b g.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [forall i, MulAction α (A i)] :
  body: Sigma.ext rfl heq_of_eq one_smul _ g.2
mul_smul r₁ r₂ g := Sigma.ext rfl heq_of_eq mul_smul r₁ r₂ g.2

中文:
实例 [幺半群
  签名: α] [对任意 i, 乘法作用 α (A i)] :
  定义体: Sigma.ext rfl heq_of_eq one_smul _ g.2
mul_smul r₁ r₂ g := Sigma.ext rfl heq_of_eq mul_smul r₁ r₂ g.2

Depends on / 依赖: Sigma.ext, heq_of_eq, one_smul
-/
instance [Monoid α] [forall i, MulAction α (A i)] :
    MulAction α (GradedMonoid A) where
one_smul g := Sigma.ext rfl heq_of_eq one_smul _ g.2
mul_smul r₁ r₂ g := Sigma.ext rfl heq_of_eq mul_smul r₁ r₂ g.2

end actions

/-! ### Typeclasses -/

section Defs

variable (A : ι -> Type*)

/--
Definition of `GOne` / `GOne` 的定义

English:
class GOne
  parameters: [Zero ι]
  axioms and operations (1):
    - one : A 0

中文:
类 GOne
  参数: [零 ι]
  公理与运算 (1 个):
    - one : A 0
-/
class GOne [Zero ι] where
  /-- The term `one` of grade 0 -/
  one : A 0

/--
Instance `GOne.toOne` / 实例 `GOne.toOne`

English:
instance GOne.toOne
  signature: [Zero ι] [GOne A]
  body: ⟨⟨_, GOne.one⟩⟩

中文:
实例 GOne.toOne
  签名: [零 ι] [GOne A]
  定义体: ⟨⟨_, GOne.one⟩⟩

Depends on / 依赖: GOne.one
-/
instance GOne.toOne [Zero ι] [GOne A] : One (GradedMonoid A) :=
  ⟨⟨_, GOne.one⟩⟩

/--
theorem `fst_one` / 定理 `fst_one`

English:
theorem fst_one
  given: [Zero ι] [GOne A]
  statement: (1 : GradedMonoid A).fst = 0
  proof: rfl

中文:
定理 fst_one
  条件: [零 ι] [GOne A]
  结论: (1 : 分次幺半群 A).fst = 0
  证明: rfl
-/
@[simp] theorem fst_one [Zero ι] [GOne A] : (1 : GradedMonoid A).fst = 0 := rfl

/--
theorem `snd_one` / 定理 `snd_one`

English:
theorem snd_one
  given: [Zero ι] [GOne A]
  statement: (1 : GradedMonoid A).snd = GOne.one
  proof: rfl

中文:
定理 snd_one
  条件: [零 ι] [GOne A]
  结论: (1 : 分次幺半群 A).snd = GOne.one
  证明: rfl
-/
@[simp] theorem snd_one [Zero ι] [GOne A] : (1 : GradedMonoid A).snd = GOne.one := rfl

/--
Definition of `GMul` / `GMul` 的定义

English:
class GMul
  parameters: [Add ι]
  axioms and operations (1):
    - mul({i j}) : A i -> A j -> A (i + j)

中文:
类 GMul
  参数: [加法 ι]
  公理与运算 (1 个):
    - mul({i j}) : A i -> A j -> A (i + j)
-/
class GMul [Add ι] where
  /-- The homogeneous multiplication map `mul` -/
  mul {i j} : A i -> A j -> A (i + j)

/--
Instance `GMul.toMul` / 实例 `GMul.toMul`

English:
instance GMul.toMul
  signature: [Add ι] [GMul A]
  body: ⟨fun x y => ⟨_, GMul.mul x.snd y.snd⟩⟩

中文:
实例 GMul.toMul
  签名: [加法 ι] [GMul A]
  定义体: ⟨fun x y => ⟨_, GMul.mul x.snd y.snd⟩⟩

Depends on / 依赖: GMul.mul, x.snd, y.snd
-/
instance GMul.toMul [Add ι] [GMul A] : Mul (GradedMonoid A) :=
  ⟨fun x y => ⟨_, GMul.mul x.snd y.snd⟩⟩

/--
theorem `fst_mul` / 定理 `fst_mul`

English:
theorem fst_mul
  given: [Add ι] [GMul A] (x y : GradedMonoid A)
  proof: rfl

中文:
定理 fst_mul
  条件: [加法 ι] [GMul A] (x y : 分次幺半群 A)
  证明: rfl
-/
@[simp] theorem fst_mul [Add ι] [GMul A] (x y : GradedMonoid A) :
    (x * y).fst = x.fst + y.fst := rfl

/--
theorem `snd_mul` / 定理 `snd_mul`

English:
theorem snd_mul
  given: [Add ι] [GMul A] (x y : GradedMonoid A)
  proof: rfl

中文:
定理 snd_mul
  条件: [加法 ι] [GMul A] (x y : 分次幺半群 A)
  证明: rfl
-/
@[simp] theorem snd_mul [Add ι] [GMul A] (x y : GradedMonoid A) :
    (x * y).snd = GMul.mul x.snd y.snd := rfl

/--
theorem `mk_mul_mk` / 定理 `mk_mul_mk`

English:
theorem mk_mul_mk
  given: [Add ι] [GMul A] {i j} (a : A i) (b : A j)
  proof: rfl

中文:
定理 mk_mul_mk
  条件: [加法 ι] [GMul A] {i j} (a : A i) (b : A j)
  证明: rfl
-/
theorem mk_mul_mk [Add ι] [GMul A] {i j} (a : A i) (b : A j) :
    mk i a * mk j b = mk (i + j) (GMul.mul a b) :=
  rfl

namespace GMonoid

variable {A}
variable [AddMonoid ι] [GMul A] [GOne A]

/--
Definition of `gnpowRec` / `gnpowRec` 的定义

English:
definition gnpowRec
  signature: : forall (n : Nat) {i}, A i -> A (n • i)

中文:
定义 gnpowRec
  签名: : 对任意 (n : 自然数) {i}, A i -> A (n • i)
-/
def gnpowRec : forall (n : Nat) {i}, A i -> A (n • i)
  | 0, i, _ => cast (congr_arg A (zero_nsmul i).symm) GOne.one
  | n + 1, i, a => cast (congr_arg A (succ_nsmul i n).symm) (GMul.mul (gnpowRec _ a) a)

@[simp]
/--
theorem `gnpowRec_zero` / 定理 `gnpowRec_zero`

English:
theorem gnpowRec_zero
  given: (a : GradedMonoid A)
  statement: GradedMonoid.mk _ (gnpowRec 0 a.snd) = 1
  proof: Sigma.ext (zero_nsmul _) (heq_of_cast_eq _ rfl).symm

@[simp]

中文:
定理 gnpowRec_zero
  条件: (a : 分次幺半群 A)
  结论: 分次幺半群.mk _ (gnpowRec 0 a.snd) = 1
  证明: Sigma.ext (zero_nsmul _) (heq_of_cast_eq _ rfl).symm

@[simp]

Depends on / 依赖: Sigma.ext, heq_of_cast_eq, zero_nsmul
-/
theorem gnpowRec_zero (a : GradedMonoid A) : GradedMonoid.mk _ (gnpowRec 0 a.snd) = 1 :=
  Sigma.ext (zero_nsmul _) (heq_of_cast_eq _ rfl).symm

@[simp]
/--
theorem `gnpowRec_succ` / 定理 `gnpowRec_succ`

English:
theorem gnpowRec_succ
  given: (n : Nat) (a : GradedMonoid A)
  proof: Sigma.ext (succ_nsmul _ _) (heq_of_cast_eq _ rfl).symm

中文:
定理 gnpowRec_succ
  条件: (n : 自然数) (a : 分次幺半群 A)
  证明: Sigma.ext (succ_nsmul _ _) (heq_of_cast_eq _ rfl).symm

Depends on / 依赖: Sigma.ext, heq_of_cast_eq, succ_nsmul
-/
theorem gnpowRec_succ (n : Nat) (a : GradedMonoid A) :
    (GradedMonoid.mk _ <| gnpowRec n.succ a.snd) = ⟨_, gnpowRec n a.snd⟩ * a :=
  Sigma.ext (succ_nsmul _ _) (heq_of_cast_eq _ rfl).symm

end GMonoid

/-- A tactic to for use as an optional value for `GMonoid.gnpow_zero'`. -/
macro "apply_gmonoid_gnpowRec_zero_tac" : tactic => `(tactic| apply GMonoid.gnpowRec_zero)
/-- A tactic to for use as an optional value for `GMonoid.gnpow_succ'`. -/
macro "apply_gmonoid_gnpowRec_succ_tac" : tactic => `(tactic| apply GMonoid.gnpowRec_succ)

/--
Definition of `GMonoid` / `GMonoid` 的定义

English:
class GMonoid
  parameters: [AddMonoid ι]
  extends: GMul A, GOne A
  axioms and operations (6):
    - one_mul((a : GradedMonoid A)) : 1 * a = a
    - mul_one((a : GradedMonoid A)) : a * 1 = a
    - mul_assoc((a b c : GradedMonoid A)) : a * b * c = a * (b * c)
    - gnpow : forall (n : Nat) {i}, A i -> A (n • i)  [default: GMonoid.gnpowRec]
    - gnpow_zero' : forall a : GradedMonoid A, GradedMonoid.mk _ (gnpow 0 a.snd) = 1  [default: by apply_gmonoid_gnpowRec_zero_tac]
    - gnpow_succ' : forall (n : Nat) (a : GradedMonoid A), (GradedMonoid.mk _ <| gnpow n.succ a.snd) = ⟨_, gnpow n a.snd⟩ * a  [default: by apply_gmonoid_gnpowRec_succ_tac]

中文:
类 G幺半群
  参数: [加法幺半群 ι]
  继承: GMul A, GOne A
  公理与运算 (6 个):
    - one_mul((a : 分次幺半群 A)) : 1 * a = a
    - mul_one((a : 分次幺半群 A)) : a * 1 = a
    - mul_assoc((a b c : 分次幺半群 A)) : a * b * c = a * (b * c)
    - gnpow : 对任意 (n : 自然数) {i}, A i -> A (n • i)  [默认: GMonoid.gnpowRec]
    - gnpow_zero' : 对任意 a : 分次幺半群 A, 分次幺半群.mk _ (gnpow 0 a.snd) = 1  [默认: by apply_gmonoid_gnpowRec_zero_tac]
    - gnpow_succ' : 对任意 (n : 自然数) (a : 分次幺半群 A), (分次幺半群.mk _ <| gnpow n.succ a.snd) = ⟨_, gnpow n a.snd⟩ * a  [默认: by apply_gmonoid_gnpowRec_succ_tac]

Depends on / 依赖: GMonoid, GMonoid.gnpowRec, gnpowRec
-/
class GMonoid [AddMonoid ι] extends GMul A, GOne A where
  /-- Multiplication by `one` on the left is the identity -/
  one_mul (a : GradedMonoid A) : 1 * a = a
  /-- Multiplication by `one` on the right is the identity -/
  mul_one (a : GradedMonoid A) : a * 1 = a
  /-- Multiplication is associative -/
  mul_assoc (a b c : GradedMonoid A) : a * b * c = a * (b * c)
  /-- Optional field to allow definitional control of natural powers -/
  gnpow : forall (n : Nat) {i}, A i -> A (n • i) := GMonoid.gnpowRec
  /-- The zeroth power will yield 1 -/
  gnpow_zero' : forall a : GradedMonoid A, GradedMonoid.mk _ (gnpow 0 a.snd) = 1 := by
    apply_gmonoid_gnpowRec_zero_tac
  /-- Successor powers behave as expected -/
  gnpow_succ' :
    forall (n : Nat) (a : GradedMonoid A),
      (GradedMonoid.mk _ <| gnpow n.succ a.snd) = ⟨_, gnpow n a.snd⟩ * a := by
    apply_gmonoid_gnpowRec_succ_tac

/--
Instance `GMonoid.toMonoid` / 实例 `GMonoid.toMonoid`

English:
instance GMonoid.toMonoid
  signature: [AddMonoid ι] [GMonoid A]
  body: GradedMonoid.mk _ (GMonoid.gnpow n a.snd)
  npow_zero a := GMonoid.gnpow_zero' a
  npow_succ n a := GMonoid.gnpow_succ' n a
  one_mul := GMonoid.one_mul
  mul_one := GMonoid.mul_one
  mul_assoc := GMonoid.mul_assoc

中文:
实例 G幺半群.toMonoid
  签名: [加法幺半群 ι] [G幺半群 A]
  定义体: GradedMonoid.mk _ (GMonoid.gnpow n a.snd)
  npow_zero a := GMonoid.gnpow_zero' a
  npow_succ n a := GMonoid.gnpow_succ' n a
  one_mul := GMonoid.one_mul
  mul_one := GMonoid.mul_one
  mul_assoc := GMonoid.mul_assoc

Depends on / 依赖: GMonoid, GMonoid.gnpow, GradedMonoid, GradedMonoid.mk, a.snd
-/
instance GMonoid.toMonoid [AddMonoid ι] [GMonoid A] : Monoid (GradedMonoid A) where
  npow n a := GradedMonoid.mk _ (GMonoid.gnpow n a.snd)
  npow_zero a := GMonoid.gnpow_zero' a
  npow_succ n a := GMonoid.gnpow_succ' n a
  one_mul := GMonoid.one_mul
  mul_one := GMonoid.mul_one
  mul_assoc := GMonoid.mul_assoc

/--
theorem `fst_pow` / 定理 `fst_pow`

English:
theorem fst_pow
  given: [AddMonoid ι] [GMonoid A] (x : GradedMonoid A) (n : Nat)
  proof: rfl

中文:
定理 fst_pow
  条件: [加法幺半群 ι] [G幺半群 A] (x : 分次幺半群 A) (n : 自然数)
  证明: rfl
-/
@[simp] theorem fst_pow [AddMonoid ι] [GMonoid A] (x : GradedMonoid A) (n : Nat) :
    (x ^ n).fst = n • x.fst := rfl

/--
theorem `snd_pow` / 定理 `snd_pow`

English:
theorem snd_pow
  given: [AddMonoid ι] [GMonoid A] (x : GradedMonoid A) (n : Nat)
  proof: rfl

中文:
定理 snd_pow
  条件: [加法幺半群 ι] [G幺半群 A] (x : 分次幺半群 A) (n : 自然数)
  证明: rfl
-/
@[simp] theorem snd_pow [AddMonoid ι] [GMonoid A] (x : GradedMonoid A) (n : Nat) :
    (x ^ n).snd = GMonoid.gnpow n x.snd := rfl

/--
theorem `mk_pow` / 定理 `mk_pow`

English:
theorem mk_pow
  given: [AddMonoid ι] [GMonoid A] {i} (a : A i) (n : Nat)
  proof: rfl

中文:
定理 mk_pow
  条件: [加法幺半群 ι] [G幺半群 A] {i} (a : A i) (n : 自然数)
  证明: rfl
-/
theorem mk_pow [AddMonoid ι] [GMonoid A] {i} (a : A i) (n : Nat) :
    mk i a ^ n = mk (n • i) (GMonoid.gnpow _ a) := rfl

/--
Definition of `GCommMonoid` / `GCommMonoid` 的定义

English:
class GCommMonoid
  parameters: [AddCommMonoid ι]
  extends: GMonoid A
  axioms and operations (1):
    - mul_comm((a : GradedMonoid A) (b : GradedMonoid A)) : a * b = b * a

中文:
类 GComm幺半群
  参数: [加法交换幺半群 ι]
  继承: G幺半群 A
  公理与运算 (1 个):
    - mul_comm((a : 分次幺半群 A) (b : 分次幺半群 A)) : a * b = b * a
-/
class GCommMonoid [AddCommMonoid ι] extends GMonoid A where
  /-- Multiplication is commutative -/
  mul_comm (a : GradedMonoid A) (b : GradedMonoid A) : a * b = b * a

/--
Instance `GCommMonoid.toCommMonoid` / 实例 `GCommMonoid.toCommMonoid`

English:
instance GCommMonoid.toCommMonoid
  signature: [AddCommMonoid ι] [GCommMonoid A]
  body: GCommMonoid.mul_comm

中文:
实例 GComm幺半群.toCommMonoid
  签名: [加法交换幺半群 ι] [GComm幺半群 A]
  定义体: GCommMonoid.mul_comm

Depends on / 依赖: GCommMonoid, GCommMonoid.mul_comm, mul_comm
-/
instance GCommMonoid.toCommMonoid [AddCommMonoid ι] [GCommMonoid A] :
    CommMonoid (GradedMonoid A) where
  mul_comm := GCommMonoid.mul_comm

end Defs

/-! ### Instances for `A 0`

The various `g*` instances are enough to promote the `AddCommMonoid (A 0)` structure to various
types of multiplicative structure.
-/


section GradeZero

variable (A : ι -> Type*)

section One

variable [Zero ι] [GOne A]

/-- `1 : A 0` is the value provided in `GOne.one`. -/
@[nolint unusedArguments]
instance (priority := 900) GradeZero.one : One (A 0) :=
  ⟨GOne.one⟩

end One

section Mul

variable [AddZeroClass ι] [GMul A]

/--
Instance `GradeZero.smul` / 实例 `GradeZero.smul`

English:
instance GradeZero.smul
  signature: (i : ι)
  body: @Eq.rec ι (0 + i) (fun a _ => A a) (GMul.mul x y) i (zero_add i)

中文:
实例 GradeZero.smul
  签名: (i : ι)
  定义体: @Eq.rec ι (0 + i) (fun a _ => A a) (GMul.mul x y) i (zero_add i)

Depends on / 依赖: Eq.rec, GMul.mul, zero_add
-/
instance GradeZero.smul (i : ι) : SMul (A 0) (A i) where
  smul x y := @Eq.rec ι (0 + i) (fun a _ => A a) (GMul.mul x y) i (zero_add i)

/-- `(*) : A 0 → A 0 → A 0` is the value provided in `GradedMonoid.GMul.mul`, composed with
an `Eq.rec` to turn `A (0 + 0)` into `A 0`.
-/
instance (priority := 900) GradeZero.mul : Mul (A 0) where mul := (· • ·)

variable {A}

@[simp]
/--
theorem `mk_zero_smul` / 定理 `mk_zero_smul`

English:
theorem mk_zero_smul
  given: {i} (a : A 0) (b : A i)
  statement: mk _ (a • b) = mk _ a * mk _ b
  proof: Sigma.ext (zero_add _).symm eqRec_heq _ _

@[scoped simp]

中文:
定理 mk_zero_smul
  条件: {i} (a : A 0) (b : A i)
  结论: mk _ (a • b) = mk _ a * mk _ b
  证明: Sigma.ext (zero_add _).symm eqRec_heq _ _

@[scoped simp]

Depends on / 依赖: Sigma.ext, eqRec_heq, zero_add
-/
theorem mk_zero_smul {i} (a : A 0) (b : A i) : mk _ (a • b) = mk _ a * mk _ b :=
Sigma.ext (zero_add _).symm eqRec_heq _ _

@[scoped simp]
/--
theorem `GradeZero.smul_eq_mul` / 定理 `GradeZero.smul_eq_mul`

English:
theorem GradeZero.smul_eq_mul
  given: (a b : A 0)
  statement: a • b = a * b
  proof: rfl

中文:
定理 GradeZero.smul_eq_mul
  条件: (a b : A 0)
  结论: a • b = a * b
  证明: rfl
-/
theorem GradeZero.smul_eq_mul (a b : A 0) : a • b = a * b :=
  rfl

end Mul

section Monoid

variable [AddMonoid ι] [GMonoid A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatPow (A 0)
  body: @Eq.rec ι (n • (0 : ι)) (fun a _ => A a) (GMonoid.gnpow n x) 0 (nsmul_zero n)

中文:
实例 :
  签名: 自然数Pow (A 0)
  定义体: @Eq.rec ι (n • (0 : ι)) (fun a _ => A a) (GMonoid.gnpow n x) 0 (nsmul_zero n)

Depends on / 依赖: Eq.rec, GMonoid, GMonoid.gnpow, nsmul_zero
-/
instance : NatPow (A 0) where
  pow x n := @Eq.rec ι (n • (0 : ι)) (fun a _ => A a) (GMonoid.gnpow n x) 0 (nsmul_zero n)

variable {A} in
@[simp]
/--
theorem `mk_zero_pow` / 定理 `mk_zero_pow`

English:
theorem mk_zero_pow
  given: (a : A 0) (n : Nat)
  statement: mk _ (a ^ n) = mk _ a ^ n
  proof: Sigma.ext (nsmul_zero n).symm eqRec_heq _ _

中文:
定理 mk_zero_pow
  条件: (a : A 0) (n : 自然数)
  结论: mk _ (a ^ n) = mk _ a ^ n
  证明: Sigma.ext (nsmul_zero n).symm eqRec_heq _ _

Depends on / 依赖: Sigma.ext, eqRec_heq, nsmul_zero
-/
theorem mk_zero_pow (a : A 0) (n : Nat) : mk _ (a ^ n) = mk _ a ^ n :=
Sigma.ext (nsmul_zero n).symm eqRec_heq _ _

/-- The `Monoid` structure derived from `GMonoid A`. -/
instance (priority := 900) GradeZero.monoid : Monoid (A 0) :=
  Function.Injective.monoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow

end Monoid

section Monoid

variable [AddCommMonoid ι] [GCommMonoid A]

/-- The `CommMonoid` structure derived from `GCommMonoid A`. -/
instance (priority := 900) GradeZero.commMonoid : CommMonoid (A 0) :=
  Function.Injective.commMonoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow

end Monoid

section MulAction

variable [AddMonoid ι] [GMonoid A]

/--
Definition of `mkZeroMonoidHom` / `mkZeroMonoidHom` 的定义

English:
definition mkZeroMonoidHom
  signature: : A 0 ->* GradedMonoid A where
  body: mk 0
  map_one' := rfl
  map_mul' := mk_zero_smul

中文:
定义 mkZeroMonoidHom
  签名: : A 0 ->* 分次幺半群 A where
  定义体: mk 0
  map_one' := rfl
  map_mul' := mk_zero_smul
-/
def mkZeroMonoidHom : A 0 ->* GradedMonoid A where
  toFun := mk 0
  map_one' := rfl
  map_mul' := mk_zero_smul

/--
Instance `GradeZero.mulAction` / 实例 `GradeZero.mulAction`

English:
instance GradeZero.mulAction
  signature: {i}
  body: letI := MulAction.compHom (GradedMonoid A) (mkZeroMonoidHom A)
  Function.Injective.mulAction (mk i) sigma_mk_injective mk_zero_smul

中文:
实例 GradeZero.mulAction
  签名: {i}
  定义体: letI := MulAction.compHom (GradedMonoid A) (mkZeroMonoidHom A)
  Function.Injective.mulAction (mk i) sigma_mk_injective mk_zero_smul

Depends on / 依赖: Function, Function.Injective.mulAction, GradedMonoid, Injective, MulAction, MulAction.compHom, compHom, mkZeroMonoidHom, mk_zero_smul, mulAction, sigma_mk_injective
-/
instance GradeZero.mulAction {i} : MulAction (A 0) (A i) :=
  letI := MulAction.compHom (GradedMonoid A) (mkZeroMonoidHom A)
  Function.Injective.mulAction (mk i) sigma_mk_injective mk_zero_smul

end MulAction

end GradeZero

end GradedMonoid

/-! ### Dependent products of graded elements -/


section DProd

variable {α : Type*} {A : ι -> Type*} [AddMonoid ι] [GradedMonoid.GMonoid A]

/--
Definition of `List.dProdIndex` / `List.dProdIndex` 的定义

English:
definition List.dProdIndex
  signature: (l : List α) (fι : α -> ι)
  body: l.foldr (fun i b => fι i + b) 0

@[simp]

中文:
定义 列表.dProdIndex
  签名: (l : 列表 α) (fι : α -> ι)
  定义体: l.foldr (fun i b => fι i + b) 0

@[simp]

Depends on / 依赖: l.foldr
-/
def List.dProdIndex (l : List α) (fι : α -> ι) : ι :=
  l.foldr (fun i b => fι i + b) 0

@[simp]
/--
theorem `List.dProdIndex_nil` / 定理 `List.dProdIndex_nil`

English:
theorem List.dProdIndex_nil
  given: (fι : α -> ι)
  statement: ([] : List α).dProdIndex fι = 0
  proof: rfl

@[simp]

中文:
定理 列表.dProdIndex_nil
  条件: (fι : α -> ι)
  结论: ([] : 列表 α).dProdIndex fι = 0
  证明: rfl

@[simp]
-/
theorem List.dProdIndex_nil (fι : α -> ι) : ([] : List α).dProdIndex fι = 0 :=
  rfl

@[simp]
/--
theorem `List.dProdIndex_cons` / 定理 `List.dProdIndex_cons`

English:
theorem List.dProdIndex_cons
  given: (a : α) (l : List α) (fι : α -> ι)
  proof: rfl

中文:
定理 列表.dProdIndex_cons
  条件: (a : α) (l : 列表 α) (fι : α -> ι)
  证明: rfl
-/
theorem List.dProdIndex_cons (a : α) (l : List α) (fι : α -> ι) :
    (a :: l).dProdIndex fι = fι a + l.dProdIndex fι :=
  rfl

/--
theorem `List.dProdIndex_eq_map_sum` / 定理 `List.dProdIndex_eq_map_sum`

English:
theorem List.dProdIndex_eq_map_sum
  given: (l : List α) (fι : α -> ι)
  proof: by
  match l with
  | [] => simp
  | head::tail => simp [List.dProdIndex_eq_map_sum tail fι]

中文:
定理 列表.dProdIndex_eq_map_sum
  条件: (l : 列表 α) (fι : α -> ι)
  证明: by
  match l with
  | [] => simp
  | head::tail => simp [List.dProdIndex_eq_map_sum tail fι]

Depends on / 依赖: List.dProdIndex_eq_map_sum, dProdIndex_eq_map_sum
-/
theorem List.dProdIndex_eq_map_sum (l : List α) (fι : α -> ι) :
    l.dProdIndex fι = (l.map fι).sum := by
  match l with
  | [] => simp
  | head::tail => simp [List.dProdIndex_eq_map_sum tail fι]

/--
Definition of `List.dProd` / `List.dProd` 的定义

English:
definition List.dProd
  signature: (l : List α) (fι : α -> ι) (fA : forall a, A (fι a))
  body: l.foldrRecOn _ GradedMonoid.GOne.one fun _ x a _ => GradedMonoid.GMul.mul (fA a) x

@[simp]

中文:
定义 列表.dProd
  签名: (l : 列表 α) (fι : α -> ι) (fA : 对任意 a, A (fι a))
  定义体: l.foldrRecOn _ GradedMonoid.GOne.one fun _ x a _ => GradedMonoid.GMul.mul (fA a) x

@[simp]

Depends on / 依赖: GradedMonoid, GradedMonoid.GMul.mul, GradedMonoid.GOne.one, foldrRecOn, l.foldrRecOn
-/
def List.dProd (l : List α) (fι : α -> ι) (fA : forall a, A (fι a)) : A (l.dProdIndex fι) :=
  l.foldrRecOn _ GradedMonoid.GOne.one fun _ x a _ => GradedMonoid.GMul.mul (fA a) x

@[simp]
/--
theorem `List.dProd_nil` / 定理 `List.dProd_nil`

English:
theorem List.dProd_nil
  given: (fι : α -> ι) (fA : forall a, A (fι a))
  proof: rfl

中文:
定理 列表.dProd_nil
  条件: (fι : α -> ι) (fA : 对任意 a, A (fι a))
  证明: rfl
-/
theorem List.dProd_nil (fι : α -> ι) (fA : forall a, A (fι a)) :
    (List.nil : List α).dProd fι fA = GradedMonoid.GOne.one :=
  rfl

-- the `( :)` in this lemma statement results in the type on the RHS not being unfolded, which
-- is nicer in the goal view.
@[simp]
/--
theorem `List.dProd_cons` / 定理 `List.dProd_cons`

English:
theorem List.dProd_cons
  given: (fι : α -> ι) (fA : forall a, A (fι a)) (a : α) (l : List α)
  proof: rfl

中文:
定理 列表.dProd_cons
  条件: (fι : α -> ι) (fA : 对任意 a, A (fι a)) (a : α) (l : 列表 α)
  证明: rfl
-/
theorem List.dProd_cons (fι : α -> ι) (fA : forall a, A (fι a)) (a : α) (l : List α) :
    (a :: l).dProd fι fA = (GradedMonoid.GMul.mul (fA a) (l.dProd fι fA) :) :=
  rfl

/--
theorem `GradedMonoid.mk_list_dProd` / 定理 `GradedMonoid.mk_list_dProd`

English:
theorem GradedMonoid.mk_list_dProd
  given: (l : List α) (fι : α -> ι) (fA : forall a, A (fι a))
  proof: by
  match l with
  | [] => simp only [List.dProdIndex_nil, List.dProd_nil, List.map_nil, List.prod_nil]; rfl
  | head::tail =>
    simp [← GradedMonoid.mk_list_dProd tail _ _, GradedMonoid.mk_mul_mk, List.prod_cons]

中文:
定理 分次幺半群.mk_list_dProd
  条件: (l : 列表 α) (fι : α -> ι) (fA : 对任意 a, A (fι a))
  证明: by
  match l with
  | [] => simp only [List.dProdIndex_nil, List.dProd_nil, List.map_nil, List.prod_nil]; rfl
  | head::tail =>
    simp [← GradedMonoid.mk_list_dProd tail _ _, GradedMonoid.mk_mul_mk, List.prod_cons]

Depends on / 依赖: GradedMonoid, GradedMonoid.mk_list_dProd, GradedMonoid.mk_mul_mk, List.dProdIndex_nil, List.dProd_nil, List.map_nil, List.prod_cons, List.prod_nil, dProdIndex_nil, dProd_nil, map_nil, mk_list_dProd, mk_mul_mk, prod_cons, prod_nil
-/
theorem GradedMonoid.mk_list_dProd (l : List α) (fι : α -> ι) (fA : forall a, A (fι a)) :
    GradedMonoid.mk _ (l.dProd fι fA) = (l.map fun a => GradedMonoid.mk (fι a) (fA a)).prod := by
  match l with
  | [] => simp only [List.dProdIndex_nil, List.dProd_nil, List.map_nil, List.prod_nil]; rfl
  | head::tail =>
    simp [← GradedMonoid.mk_list_dProd tail _ _, GradedMonoid.mk_mul_mk, List.prod_cons]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `GradedMonoid.list_prod_map_eq_dProd` / 定理 `GradedMonoid.list_prod_map_eq_dProd`

English:
theorem GradedMonoid.list_prod_map_eq_dProd
  given: (l : List α) (f : α -> GradedMonoid A)
  proof: by
  rw [GradedMonoid.mk_list_dProd]; rw [GradedMonoid.mk]
  simp_rw [Sigma.eta]

中文:
定理 分次幺半群.list_prod_map_eq_dProd
  条件: (l : 列表 α) (f : α -> 分次幺半群 A)
  证明: by
  rw [GradedMonoid.mk_list_dProd]; rw [GradedMonoid.mk]
  simp_rw [Sigma.eta]

Depends on / 依赖: GradedMonoid, GradedMonoid.mk, GradedMonoid.mk_list_dProd, Sigma.eta, mk_list_dProd, simp_rw
-/
theorem GradedMonoid.list_prod_map_eq_dProd (l : List α) (f : α -> GradedMonoid A) :
    (l.map f).prod = GradedMonoid.mk _ (l.dProd (fun i => (f i).1) fun i => (f i).2) := by
  rw [GradedMonoid.mk_list_dProd]; rw [GradedMonoid.mk]
  simp_rw [Sigma.eta]

/--
theorem `GradedMonoid.list_prod_ofFn_eq_dProd` / 定理 `GradedMonoid.list_prod_ofFn_eq_dProd`

English:
theorem GradedMonoid.list_prod_ofFn_eq_dProd
  given: {n : Nat} (f : Fin n -> GradedMonoid A)
  proof: by
  rw [List.ofFn_eq_map]; rw [GradedMonoid.list_prod_map_eq_dProd]

中文:
定理 分次幺半群.list_prod_ofFn_eq_dProd
  条件: {n : 自然数} (f : 有限集 n -> 分次幺半群 A)
  证明: by
  rw [List.ofFn_eq_map]; rw [GradedMonoid.list_prod_map_eq_dProd]

Depends on / 依赖: GradedMonoid, GradedMonoid.list_prod_map_eq_dProd, List.ofFn_eq_map, list_prod_map_eq_dProd, ofFn_eq_map
-/
theorem GradedMonoid.list_prod_ofFn_eq_dProd {n : Nat} (f : Fin n -> GradedMonoid A) :
    (List.ofFn f).prod =
      GradedMonoid.mk _ ((List.finRange n).dProd (fun i => (f i).1) fun i => (f i).2) := by
  rw [List.ofFn_eq_map]; rw [GradedMonoid.list_prod_map_eq_dProd]

end DProd

/-! ### Concrete instances -/


section

variable (ι) {R : Type*}

@[simps one]
/--
Instance `One.gOne` / 实例 `One.gOne`

English:
instance One.gOne
  signature: [Zero ι] [One R]
  body: 1

@[simps mul]

中文:
实例 幺.gOne
  签名: [零 ι] [幺 R]
  定义体: 1

@[simps mul]
-/
instance One.gOne [Zero ι] [One R] : GradedMonoid.GOne fun _ : ι => R where one := 1

@[simps mul]
/--
Instance `Mul.gMul` / 实例 `Mul.gMul`

English:
instance Mul.gMul
  signature: [Add ι] [Mul R]
  body: x * y

中文:
实例 乘法.gMul
  签名: [加法 ι] [乘法 R]
  定义体: x * y
-/
instance Mul.gMul [Add ι] [Mul R] : GradedMonoid.GMul fun _ : ι => R where mul x y := x * y

/-- If all grades are the same type and themselves form a monoid, then there is a trivial grading
structure. -/
@[simps gnpow]
/--
Instance `Monoid.gMonoid` / 实例 `Monoid.gMonoid`

English:
instance Monoid.gMonoid
  signature: [AddMonoid ι] [Monoid R]
  body: fun _ => Sigma.ext (zero_add _) (heq_of_eq (one_mul _))
  mul_one := fun _ => Sigma.ext (add_zero _) (heq_of_eq (mul_one _))
  mul_assoc := fun _ _ _ => Sigma.ext (add_assoc _ _ _) (heq_of_eq (mul_assoc _ _ _))
  gnpow := fun n _ a => a ^ n
  gnpow_zero' := fun _ => Sigma.ext (zero_nsmul _) (heq_of_

中文:
实例 幺半群.gMonoid
  签名: [加法幺半群 ι] [幺半群 R]
  定义体: fun _ => Sigma.ext (zero_add _) (heq_of_eq (one_mul _))
  mul_one := fun _ => Sigma.ext (add_zero _) (heq_of_eq (mul_one _))
  mul_assoc := fun _ _ _ => Sigma.ext (add_assoc _ _ _) (heq_of_eq (mul_assoc _ _ _))
  gnpow := fun n _ a => a ^ n
  gnpow_zero' := fun _ => Sigma.ext (zero_nsmul _) (heq_of_

Depends on / 依赖: Sigma.ext, heq_of_eq, one_mul, zero_add
-/
instance Monoid.gMonoid [AddMonoid ι] [Monoid R] : GradedMonoid.GMonoid fun _ : ι => R where
  one_mul := fun _ => Sigma.ext (zero_add _) (heq_of_eq (one_mul _))
  mul_one := fun _ => Sigma.ext (add_zero _) (heq_of_eq (mul_one _))
  mul_assoc := fun _ _ _ => Sigma.ext (add_assoc _ _ _) (heq_of_eq (mul_assoc _ _ _))
  gnpow := fun n _ a => a ^ n
  gnpow_zero' := fun _ => Sigma.ext (zero_nsmul _) (heq_of_eq (Monoid.npow_zero _))
  gnpow_succ' := fun _ ⟨_, _⟩ => Sigma.ext (succ_nsmul _ _) (heq_of_eq (Monoid.npow_succ _ _))

/--
Instance `CommMonoid.gCommMonoid` / 实例 `CommMonoid.gCommMonoid`

English:
instance CommMonoid.gCommMonoid
  signature: [AddCommMonoid ι] [CommMonoid R]
  body: fun _ _ => Sigma.ext (add_comm _ _) (heq_of_eq (mul_comm _ _))

中文:
实例 交换幺半群.gCommMonoid
  签名: [加法交换幺半群 ι] [交换幺半群 R]
  定义体: fun _ _ => Sigma.ext (add_comm _ _) (heq_of_eq (mul_comm _ _))

Depends on / 依赖: DivInvOneMonoid, DivisionMonoid, DivisionMonoid.toDivInvOneMonoid, Sigma.ext, add_comm, heq_of_eq, mul_comm, toDivInvOneMonoid
-/
instance CommMonoid.gCommMonoid [AddCommMonoid ι] [CommMonoid R] :
    GradedMonoid.GCommMonoid fun _ : ι => R where
  mul_comm := fun _ _ => Sigma.ext (add_comm _ _) (heq_of_eq (mul_comm _ _))

/-- When all the indexed types are the same, the dependent product is just the regular product. -/
@[simp]
/--
theorem `List.dProd_monoid` / 定理 `List.dProd_monoid`

English:
theorem List.dProd_monoid
  given: {α} [AddMonoid ι] [Monoid R] (l : List α) (fι : α -> ι) (fA : α -> R)
  proof: by
  match l with
  | [] =>
    rw [List.dProd_nil]; rw [List.map_nil]; rw [List.prod_nil]
    rfl
  | head::tail =>
    rw [List.dProd_cons]; rw [List.map_cons]; rw [List.prod_cons]; rw [List.dProd_monoid tail _ _]
    rfl

中文:
定理 列表.dProd_monoid
  条件: {α} [加法幺半群 ι] [幺半群 R] (l : 列表 α) (fι : α -> ι) (fA : α -> R)
  证明: by
  match l with
  | [] =>
    rw [List.dProd_nil]; rw [List.map_nil]; rw [List.prod_nil]
    rfl
  | head::tail =>
    rw [List.dProd_cons]; rw [List.map_cons]; rw [List.prod_cons]; rw [List.dProd_monoid tail _ _]
    rfl

Depends on / 依赖: List.dProd_cons, List.dProd_monoid, List.dProd_nil, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, dProd_cons, dProd_monoid, dProd_nil, map_cons, map_nil, prod_cons, prod_nil
-/
theorem List.dProd_monoid {α} [AddMonoid ι] [Monoid R] (l : List α) (fι : α -> ι) (fA : α -> R) :
    @List.dProd _ _ (fun _ : ι => R) _ _ l fι fA = (l.map fA).prod := by
  match l with
  | [] =>
    rw [List.dProd_nil]; rw [List.map_nil]; rw [List.prod_nil]
    rfl
  | head::tail =>
    rw [List.dProd_cons]; rw [List.map_cons]; rw [List.prod_cons]; rw [List.dProd_monoid tail _ _]
    rfl

end

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable {R : Type*}

/--
Definition of `SetLike.GradedOne` / `SetLike.GradedOne` 的定义

English:
class SetLike.GradedOne
  parameters: {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι -> S)
  axioms and operations (1):
    - one_mem : (1 : R) in A 0

中文:
类 集合状.分次幺元
  参数: {S : 类型} [集合状 S R] [幺 R] [零 ι] (A : ι -> S)
  公理与运算 (1 个):
    - one_mem : (1 : R) in A 0
-/
class SetLike.GradedOne {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι -> S) : Prop where
  /-- One has grade zero -/
  one_mem : (1 : R) in A 0

/--
theorem `SetLike.one_mem_graded` / 定理 `SetLike.one_mem_graded`

English:
theorem SetLike.one_mem_graded
  statement: {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι -> S)
  proof: SetLike.GradedOne.one_mem

中文:
定理 集合状.one_mem_graded
  结论: {S : 类型} [集合状 S R] [幺 R] [零 ι] (A : ι -> S)
  证明: SetLike.GradedOne.one_mem

Depends on / 依赖: GradedOne, SetLike, SetLike.GradedOne.one_mem, one_mem
-/
theorem SetLike.one_mem_graded {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι -> S)
    [SetLike.GradedOne A] : (1 : R) in A 0 :=
  SetLike.GradedOne.one_mem

/--
Instance `SetLike.gOne` / 实例 `SetLike.gOne`

English:
instance SetLike.gOne
  signature: {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι -> S)
  body: ⟨1, SetLike.one_mem_graded _⟩

@[simp]

中文:
实例 集合状.gOne
  签名: {S : 类型} [集合状 S R] [幺 R] [零 ι] (A : ι -> S)
  定义体: ⟨1, SetLike.one_mem_graded _⟩

@[simp]

Depends on / 依赖: SetLike, SetLike.one_mem_graded, one_mem_graded
-/
instance SetLike.gOne {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι -> S)
    [SetLike.GradedOne A] : GradedMonoid.GOne fun i => A i where
  one := ⟨1, SetLike.one_mem_graded _⟩

@[simp]
/--
theorem `SetLike.coe_gOne` / 定理 `SetLike.coe_gOne`

English:
theorem SetLike.coe_gOne
  statement: {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι -> S)
  proof: rfl

中文:
定理 集合状.coe_gOne
  结论: {S : 类型} [集合状 S R] [幺 R] [零 ι] (A : ι -> S)
  证明: rfl
-/
theorem SetLike.coe_gOne {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι -> S)
    [SetLike.GradedOne A] : ↑(@GradedMonoid.GOne.one _ (fun i => A i) _ _) = (1 : R) :=
  rfl

/--
Definition of `SetLike.GradedMul` / `SetLike.GradedMul` 的定义

English:
class SetLike.GradedMul
  parameters: {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι -> S)
  axioms and operations (1):
    - mul_mem : forall ⦃i j⦄ {gi gj}, gi in A i -> gj in A j -> gi * gj in A (i + j)

中文:
类 集合状.分次乘法
  参数: {S : 类型} [集合状 S R] [乘法 R] [加法 ι] (A : ι -> S)
  公理与运算 (1 个):
    - mul_mem : 对任意 ⦃i j⦄ {gi gj}, gi in A i -> gj in A j -> gi * gj in A (i + j)
-/
class SetLike.GradedMul {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι -> S) : Prop where
  /-- Multiplication is homogeneous -/
  mul_mem : forall ⦃i j⦄ {gi gj}, gi in A i -> gj in A j -> gi * gj in A (i + j)

/--
theorem `SetLike.mul_mem_graded` / 定理 `SetLike.mul_mem_graded`

English:
theorem SetLike.mul_mem_graded
  statement: {S : Type*} [SetLike S R] [Mul R] [Add ι] {A : ι -> S}
  proof: SetLike.GradedMul.mul_mem hi hj

中文:
定理 集合状.mul_mem_graded
  结论: {S : 类型} [集合状 S R] [乘法 R] [加法 ι] {A : ι -> S}
  证明: SetLike.GradedMul.mul_mem hi hj

Depends on / 依赖: GradedMul, SetLike, SetLike.GradedMul.mul_mem, mul_mem
-/
theorem SetLike.mul_mem_graded {S : Type*} [SetLike S R] [Mul R] [Add ι] {A : ι -> S}
    [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi in A i) (hj : gj in A j) : gi * gj in A (i + j) :=
  SetLike.GradedMul.mul_mem hi hj

/--
Instance `SetLike.gMul` / 实例 `SetLike.gMul`

English:
instance SetLike.gMul
  signature: {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι -> S)
  body: fun a b => ⟨(a * b : R), SetLike.mul_mem_graded a.prop b.prop⟩

@[simp]

中文:
实例 集合状.gMul
  签名: {S : 类型} [集合状 S R] [乘法 R] [加法 ι] (A : ι -> S)
  定义体: fun a b => ⟨(a * b : R), SetLike.mul_mem_graded a.prop b.prop⟩

@[simp]

Depends on / 依赖: SetLike, SetLike.mul_mem_graded, a.prop, b.prop, mul_mem_graded
-/
instance SetLike.gMul {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι -> S)
    [SetLike.GradedMul A] : GradedMonoid.GMul fun i => A i where
  mul := fun a b => ⟨(a * b : R), SetLike.mul_mem_graded a.prop b.prop⟩

@[simp]
/--
theorem `SetLike.coe_gMul` / 定理 `SetLike.coe_gMul`

English:
theorem SetLike.coe_gMul
  statement: {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι -> S)
  proof: rfl

中文:
定理 集合状.coe_gMul
  结论: {S : 类型} [集合状 S R] [乘法 R] [加法 ι] (A : ι -> S)
  证明: rfl
-/
theorem SetLike.coe_gMul {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι -> S)
    [SetLike.GradedMul A] {i j : ι} (x : A i) (y : A j) :
    ↑(@GradedMonoid.GMul.mul _ (fun i => A i) _ _ _ _ x y) = (x * y : R) :=
  rfl

/--
Definition of `SetLike.GradedMonoid` / `SetLike.GradedMonoid` 的定义

English:
class SetLike.GradedMonoid
  parameters: {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι -> S)
  extends: SetLike.GradedOne A, SetLike.GradedMul A
  (no additional axioms)

中文:
类 集合状.分次幺半群
  参数: {S : 类型} [集合状 S R] [幺半群 R] [加法幺半群 ι] (A : ι -> S)
  继承: 集合状.分次幺元 A, 集合状.分次乘法 A
  (无附加公理)
-/
class SetLike.GradedMonoid {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι -> S) : Prop
    extends SetLike.GradedOne A, SetLike.GradedMul A

namespace SetLike

variable {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι]
variable {A : ι -> S} [SetLike.GradedMonoid A]

namespace GradeZero
variable (A) in
/-- The submonoid `A 0` of `R`. -/
@[simps]
/--
Definition of `submonoid` / `submonoid` 的定义

English:
definition submonoid
  signature: : Submonoid R where
  body: A 0
  mul_mem' ha hb := add_zero (0 : ι) ▸ SetLike.mul_mem_graded ha hb
  one_mem' := SetLike.one_mem_graded A

中文:
定义 submonoid
  签名: : 子幺半群 R where
  定义体: A 0
  mul_mem' ha hb := add_zero (0 : ι) ▸ SetLike.mul_mem_graded ha hb
  one_mem' := SetLike.one_mem_graded A
-/
def submonoid : Submonoid R where
  carrier := A 0
  mul_mem' ha hb := add_zero (0 : ι) ▸ SetLike.mul_mem_graded ha hb
  one_mem' := SetLike.one_mem_graded A

-- TODO: it might be expensive to unify `A` in this instance in practice
/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid (A 0)
  body: inferInstanceAs Monoid (GradeZero.submonoid A)

中文:
实例 instMonoid
  签名: : 幺半群 (A 0)
  定义体: inferInstanceAs Monoid (GradeZero.submonoid A)

Depends on / 依赖: GradeZero, GradeZero.submonoid, Monoid, submonoid
-/
instance instMonoid : Monoid (A 0) :=
inferInstanceAs Monoid (GradeZero.submonoid A)

-- TODO: it might be expensive to unify `A` in this instance in practice
/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  body: inferInstanceAs CommMonoid (GradeZero.submonoid A)

中文:
实例 instCommMonoid
  定义体: inferInstanceAs CommMonoid (GradeZero.submonoid A)

Depends on / 依赖: CommMonoid, GradeZero, GradeZero.submonoid, submonoid
-/
instance instCommMonoid
    {R S : Type*} [SetLike S R] [CommMonoid R]
    {A : ι -> S} [SetLike.GradedMonoid A] :
    CommMonoid (A 0) :=
inferInstanceAs CommMonoid (GradeZero.submonoid A)

/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ↑(1 : A 0) = (1 : R)
  proof: rfl

中文:
定理 coe_one
  结论: ↑(1 : A 0) = (1 : R)
  证明: rfl
-/
@[simp, norm_cast] theorem coe_one : ↑(1 : A 0) = (1 : R) := rfl

/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (a b : A 0)
  statement: ↑(a * b) = (↑a * ↑b : R)
  proof: rfl

中文:
定理 coe_mul
  条件: (a b : A 0)
  结论: ↑(a * b) = (↑a * ↑b : R)
  证明: rfl
-/
@[simp, norm_cast] theorem coe_mul (a b : A 0) : ↑(a * b) = (↑a * ↑b : R) := rfl

/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (a : A 0) (n : Nat)
  statement: ↑(a ^ n) = (↑a : R) ^ n
  proof: rfl

中文:
定理 coe_pow
  条件: (a : A 0) (n : 自然数)
  结论: ↑(a ^ n) = (↑a : R) ^ n
  证明: rfl
-/
@[simp, norm_cast] theorem coe_pow (a : A 0) (n : Nat) : ↑(a ^ n) = (↑a : R) ^ n := rfl

end GradeZero

/--
theorem `pow_mem_graded` / 定理 `pow_mem_graded`

English:
theorem pow_mem_graded
  given: (n : Nat) {r : R} {i : ι} (h : r in A i)
  statement: r ^ n in A (n • i)
  proof: by
  match n with
  | 0 =>
    rw [pow_zero]; rw [zero_nsmul]
    exact one_mem_graded _
  | n + 1 =>
    rw [pow_succ']; rw [succ_nsmul']
    exact mul_mem_graded h (pow_mem_graded n h)

中文:
定理 pow_mem_graded
  条件: (n : 自然数) {r : R} {i : ι} (h : r in A i)
  结论: r ^ n in A (n • i)
  证明: by
  match n with
  | 0 =>
    rw [pow_zero]; rw [zero_nsmul]
    exact one_mem_graded _
  | n + 1 =>
    rw [pow_succ']; rw [succ_nsmul']
    exact mul_mem_graded h (pow_mem_graded n h)

Depends on / 依赖: mul_mem_graded, one_mem_graded, pow_mem_graded, pow_succ, pow_zero, succ_nsmul, zero_nsmul
-/
theorem pow_mem_graded (n : Nat) {r : R} {i : ι} (h : r in A i) : r ^ n in A (n • i) := by
  match n with
  | 0 =>
    rw [pow_zero]; rw [zero_nsmul]
    exact one_mem_graded _
  | n + 1 =>
    rw [pow_succ']; rw [succ_nsmul']
    exact mul_mem_graded h (pow_mem_graded n h)

/--
theorem `list_prod_map_mem_graded` / 定理 `list_prod_map_mem_graded`

English:
theorem list_prod_map_mem_graded
  statement: {ι'} (l : List ι') (i : ι' -> ι) (r : ι' -> R)
  proof: by
  match l with
  | [] =>
    rw [List.map_nil]; rw [List.map_nil]; rw [List.prod_nil]; rw [List.sum_nil]
    exact one_mem_graded _
  | head::tail =>
    rw [List.map_cons]; rw [List.map_cons]; rw [List.prod_cons]; rw [List.sum_cons]
    exact
      mul_mem_graded (h _ List.mem_cons_self)
       

中文:
定理 list_prod_map_mem_graded
  结论: {ι'} (l : 列表 ι') (i : ι' -> ι) (r : ι' -> R)
  证明: by
  match l with
  | [] =>
    rw [List.map_nil]; rw [List.map_nil]; rw [List.prod_nil]; rw [List.sum_nil]
    exact one_mem_graded _
  | head::tail =>
    rw [List.map_cons]; rw [List.map_cons]; rw [List.prod_cons]; rw [List.sum_cons]
    exact
      mul_mem_graded (h _ List.mem_cons_self)
       

Depends on / 依赖: List.map_cons, List.map_nil, List.mem_cons_of_mem, List.mem_cons_self, List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil, list_prod_map_mem_graded, map_cons, map_nil, mem_cons_of_mem, mem_cons_self, mul_mem_graded, one_mem_graded, prod_cons, prod_nil, sum_cons, sum_nil
-/
theorem list_prod_map_mem_graded {ι'} (l : List ι') (i : ι' -> ι) (r : ι' -> R)
    (h : forall j in l, r j in A (i j)) : (l.map r).prod in A (l.map i).sum := by
  match l with
  | [] =>
    rw [List.map_nil]; rw [List.map_nil]; rw [List.prod_nil]; rw [List.sum_nil]
    exact one_mem_graded _
  | head::tail =>
    rw [List.map_cons]; rw [List.map_cons]; rw [List.prod_cons]; rw [List.sum_cons]
    exact
      mul_mem_graded (h _ List.mem_cons_self)
        (list_prod_map_mem_graded tail _ _ fun j hj => h _ <| List.mem_cons_of_mem _ hj)

/--
theorem `list_prod_ofFn_mem_graded` / 定理 `list_prod_ofFn_mem_graded`

English:
theorem list_prod_ofFn_mem_graded
  given: {n} (i : Fin n -> ι) (r : Fin n -> R) (h : forall j, r j in A (i j))
  proof: by
  rw [List.ofFn_eq_map]; rw [List.ofFn_eq_map]
  exact list_prod_map_mem_graded _ _ _ fun _ _ => h _

中文:
定理 list_prod_ofFn_mem_graded
  条件: {n} (i : 有限集 n -> ι) (r : 有限集 n -> R) (h : 对任意 j, r j in A (i j))
  证明: by
  rw [List.ofFn_eq_map]; rw [List.ofFn_eq_map]
  exact list_prod_map_mem_graded _ _ _ fun _ _ => h _

Depends on / 依赖: List.ofFn_eq_map, list_prod_map_mem_graded, ofFn_eq_map
-/
theorem list_prod_ofFn_mem_graded {n} (i : Fin n -> ι) (r : Fin n -> R) (h : forall j, r j in A (i j)) :
    (List.ofFn r).prod in A (List.ofFn i).sum := by
  rw [List.ofFn_eq_map]; rw [List.ofFn_eq_map]
  exact list_prod_map_mem_graded _ _ _ fun _ _ => h _

end SetLike

/--
Instance `SetLike.gMonoid` / 实例 `SetLike.gMonoid`

English:
instance SetLike.gMonoid
  signature: {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι -> S)
  body: fun ⟨_, _, _⟩ => Sigma.subtype_ext (zero_add _) (one_mul _)
  mul_one := fun ⟨_, _, _⟩ => Sigma.subtype_ext (add_zero _) (mul_one _)
  mul_assoc := fun ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩ =>
    Sigma.subtype_ext (add_assoc _ _ _) (mul_assoc _ _ _)
  gnpow := fun n _ a => ⟨(a:R)^n, SetLike.pow_mem_graded 

中文:
实例 集合状.gMonoid
  签名: {S : 类型} [集合状 S R] [幺半群 R] [加法幺半群 ι] (A : ι -> S)
  定义体: fun ⟨_, _, _⟩ => Sigma.subtype_ext (zero_add _) (one_mul _)
  mul_one := fun ⟨_, _, _⟩ => Sigma.subtype_ext (add_zero _) (mul_one _)
  mul_assoc := fun ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩ =>
    Sigma.subtype_ext (add_assoc _ _ _) (mul_assoc _ _ _)
  gnpow := fun n _ a => ⟨(a:R)^n, SetLike.pow_mem_graded 

Depends on / 依赖: Sigma.subtype_ext, one_mul, subtype_ext, zero_add
-/
instance SetLike.gMonoid {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι -> S)
    [SetLike.GradedMonoid A] : GradedMonoid.GMonoid fun i => A i where
  one_mul := fun ⟨_, _, _⟩ => Sigma.subtype_ext (zero_add _) (one_mul _)
  mul_one := fun ⟨_, _, _⟩ => Sigma.subtype_ext (add_zero _) (mul_one _)
  mul_assoc := fun ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩ =>
    Sigma.subtype_ext (add_assoc _ _ _) (mul_assoc _ _ _)
  gnpow := fun n _ a => ⟨(a:R)^n, SetLike.pow_mem_graded n a.prop⟩
  gnpow_zero' := fun _ => Sigma.subtype_ext (zero_nsmul _) (pow_zero _)
  gnpow_succ' := fun _ _ => Sigma.subtype_ext (succ_nsmul _ _) (pow_succ _ _)

@[simp]
/--
theorem `SetLike.coe_gnpow` / 定理 `SetLike.coe_gnpow`

English:
theorem SetLike.coe_gnpow
  statement: {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι -> S)
  proof: rfl

中文:
定理 集合状.coe_gnpow
  结论: {S : 类型} [集合状 S R] [幺半群 R] [加法幺半群 ι] (A : ι -> S)
  证明: rfl
-/
theorem SetLike.coe_gnpow {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι -> S)
    [SetLike.GradedMonoid A] {i : ι} (x : A i) (n : Nat) :
    ↑(@GradedMonoid.GMonoid.gnpow _ (fun i => A i) _ _ n _ x) = (x : R) ^ n :=
  rfl

/--
Instance `SetLike.gCommMonoid` / 实例 `SetLike.gCommMonoid`

English:
instance SetLike.gCommMonoid
  signature: {S : Type*} [SetLike S R] [CommMonoid R] [AddCommMonoid ι] (A : ι -> S)
  body: fun ⟨_, _, _⟩ ⟨_, _, _⟩ => Sigma.subtype_ext (add_comm _ _) (mul_comm _ _)

中文:
实例 集合状.gCommMonoid
  签名: {S : 类型} [集合状 S R] [交换幺半群 R] [加法交换幺半群 ι] (A : ι -> S)
  定义体: fun ⟨_, _, _⟩ ⟨_, _, _⟩ => Sigma.subtype_ext (add_comm _ _) (mul_comm _ _)

Depends on / 依赖: Sigma.subtype_ext, add_comm, mul_comm, subtype_ext
-/
instance SetLike.gCommMonoid {S : Type*} [SetLike S R] [CommMonoid R] [AddCommMonoid ι] (A : ι -> S)
    [SetLike.GradedMonoid A] : GradedMonoid.GCommMonoid fun i => A i where
  mul_comm := fun ⟨_, _, _⟩ ⟨_, _, _⟩ => Sigma.subtype_ext (add_comm _ _) (mul_comm _ _)

section DProd

open SetLike SetLike.GradedMonoid

variable {α S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι]

@[simp]
/--
theorem `SetLike.coe_list_dProd` / 定理 `SetLike.coe_list_dProd`

English:
theorem SetLike.coe_list_dProd
  statement: (A : ι -> S) [SetLike.GradedMonoid A] (fι : α -> ι)
  proof: by
  match l with
  | [] =>
    rw [List.dProd_nil]; rw [coe_gOne]; rw [List.map_nil]; rw [List.prod_nil]
  | head::tail =>
    rw [List.dProd_cons]; rw [coe_gMul]; rw [List.map_cons]; rw [List.prod_cons]; rw [SetLike.coe_list_dProd _ _ _ tail]

中文:
定理 集合状.coe_list_dProd
  结论: (A : ι -> S) [集合状.分次幺半群 A] (fι : α -> ι)
  证明: by
  match l with
  | [] =>
    rw [List.dProd_nil]; rw [coe_gOne]; rw [List.map_nil]; rw [List.prod_nil]
  | head::tail =>
    rw [List.dProd_cons]; rw [coe_gMul]; rw [List.map_cons]; rw [List.prod_cons]; rw [SetLike.coe_list_dProd _ _ _ tail]

Depends on / 依赖: List.dProd_cons, List.dProd_nil, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, SetLike, SetLike.coe_list_dProd, coe_gMul, coe_gOne, coe_list_dProd, dProd_cons, dProd_nil, map_cons, map_nil, prod_cons, prod_nil
-/
theorem SetLike.coe_list_dProd (A : ι -> S) [SetLike.GradedMonoid A] (fι : α -> ι)
    (fA : forall a, A (fι a)) (l : List α) : ↑(@List.dProd _ _ (fun i => ↥(A i)) _ _ l fι fA)
    = (List.prod (l.map fun a => fA a) : R) := by
  match l with
  | [] =>
    rw [List.dProd_nil]; rw [coe_gOne]; rw [List.map_nil]; rw [List.prod_nil]
  | head::tail =>
    rw [List.dProd_cons]; rw [coe_gMul]; rw [List.map_cons]; rw [List.prod_cons]; rw [SetLike.coe_list_dProd _ _ _ tail]

/--
theorem `SetLike.list_dProd_eq` / 定理 `SetLike.list_dProd_eq`

English:
theorem SetLike.list_dProd_eq
  statement: (A : ι -> S) [SetLike.GradedMonoid A] (fι : α -> ι) (fA : forall a, A (fι a))
  proof: Subtype.ext SetLike.coe_list_dProd _ _ _ _

中文:
定理 集合状.list_dProd_eq
  结论: (A : ι -> S) [集合状.分次幺半群 A] (fι : α -> ι) (fA : 对任意 a, A (fι a))
  证明: Subtype.ext SetLike.coe_list_dProd _ _ _ _

Depends on / 依赖: SetLike, SetLike.coe_list_dProd, Subtype, Subtype.ext, coe_list_dProd
-/
theorem SetLike.list_dProd_eq (A : ι -> S) [SetLike.GradedMonoid A] (fι : α -> ι) (fA : forall a, A (fι a))
    (l : List α) :
    (@List.dProd _ _ (fun i => ↥(A i)) _ _ l fι fA) =
      ⟨List.prod (l.map fun a => fA a),
        (l.dProdIndex_eq_map_sum fι).symm ▸
          list_prod_map_mem_graded l _ _ fun i _ => (fA i).prop⟩ :=
Subtype.ext SetLike.coe_list_dProd _ _ _ _

end DProd

end Subobjects

section HomogeneousElements

variable {R S : Type*} [SetLike S R]

/--
Definition of `SetLike.IsHomogeneousElem` / `SetLike.IsHomogeneousElem` 的定义

English:
definition SetLike.IsHomogeneousElem
  signature: (A : ι -> S) (a : R)
  body: exists i, a in A i

@[simp]

中文:
定义 集合状.IsHomogeneousElem
  签名: (A : ι -> S) (a : R)
  定义体: exists i, a in A i

@[simp]
-/
def SetLike.IsHomogeneousElem (A : ι -> S) (a : R) : Prop :=
  exists i, a in A i

@[simp]
/--
theorem `SetLike.isHomogeneousElem_coe` / 定理 `SetLike.isHomogeneousElem_coe`

English:
theorem SetLike.isHomogeneousElem_coe
  given: {A : ι -> S} {i} (x : A i)
  proof: ⟨i, x.prop⟩

中文:
定理 集合状.isHomogeneousElem_coe
  条件: {A : ι -> S} {i} (x : A i)
  证明: ⟨i, x.prop⟩

Depends on / 依赖: x.prop
-/
theorem SetLike.isHomogeneousElem_coe {A : ι -> S} {i} (x : A i) :
    SetLike.IsHomogeneousElem A (x : R) :=
  ⟨i, x.prop⟩

/--
theorem `SetLike.isHomogeneousElem_one` / 定理 `SetLike.isHomogeneousElem_one`

English:
theorem SetLike.isHomogeneousElem_one
  given: [Zero ι] [One R] (A : ι -> S) [SetLike.GradedOne A]
  proof: ⟨0, SetLike.one_mem_graded _⟩

中文:
定理 集合状.isHomogeneousElem_one
  条件: [零 ι] [幺 R] (A : ι -> S) [集合状.分次幺元 A]
  证明: ⟨0, SetLike.one_mem_graded _⟩

Depends on / 依赖: SetLike, SetLike.one_mem_graded, one_mem_graded
-/
theorem SetLike.isHomogeneousElem_one [Zero ι] [One R] (A : ι -> S) [SetLike.GradedOne A] :
    SetLike.IsHomogeneousElem A (1 : R) :=
  ⟨0, SetLike.one_mem_graded _⟩

/--
theorem `SetLike.IsHomogeneousElem.mul` / 定理 `SetLike.IsHomogeneousElem.mul`

English:
theorem SetLike.IsHomogeneousElem.mul
  given: [Add ι] [Mul R] {A : ι -> S} [SetLike.GradedMul A] {a b : R}

中文:
定理 集合状.IsHomogeneousElem.mul
  条件: [加法 ι] [乘法 R] {A : ι -> S} [集合状.分次乘法 A] {a b : R}
-/
theorem SetLike.IsHomogeneousElem.mul [Add ι] [Mul R] {A : ι -> S} [SetLike.GradedMul A] {a b : R} :
    SetLike.IsHomogeneousElem A a -> SetLike.IsHomogeneousElem A b ->
    SetLike.IsHomogeneousElem A (a * b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i + j, SetLike.mul_mem_graded hi hj⟩

/--
Definition of `SetLike.homogeneousSubmonoid` / `SetLike.homogeneousSubmonoid` 的定义

English:
definition SetLike.homogeneousSubmonoid
  signature: [AddMonoid ι] [Monoid R] (A : ι -> S) [SetLike.GradedMonoid A]
  body: { a | SetLike.IsHomogeneousElem A a }
  one_mem' := SetLike.isHomogeneousElem_one A
  mul_mem' a b := SetLike.IsHomogeneousElem.mul a b

中文:
定义 集合状.homogeneousSubmonoid
  签名: [加法幺半群 ι] [幺半群 R] (A : ι -> S) [集合状.分次幺半群 A]
  定义体: { a | SetLike.IsHomogeneousElem A a }
  one_mem' := SetLike.isHomogeneousElem_one A
  mul_mem' a b := SetLike.IsHomogeneousElem.mul a b

Depends on / 依赖: IsHomogeneousElem, SetLike, SetLike.IsHomogeneousElem
-/
def SetLike.homogeneousSubmonoid [AddMonoid ι] [Monoid R] (A : ι -> S) [SetLike.GradedMonoid A] :
    Submonoid R where
  carrier := { a | SetLike.IsHomogeneousElem A a }
  one_mem' := SetLike.isHomogeneousElem_one A
  mul_mem' a b := SetLike.IsHomogeneousElem.mul a b

end HomogeneousElements

section CommMonoid

namespace SetLike

variable {ι R S : Type*} [SetLike S R] [CommMonoid R] [AddCommMonoid ι]
variable (A : ι -> S) [SetLike.GradedMonoid A]

variable {κ : Type*} (i : κ -> ι) (g : κ -> R) {F : Finset κ}

/--
theorem `prod_mem_graded` / 定理 `prod_mem_graded`

English:
theorem prod_mem_graded
  given: (hF : forall k in F, g k in A (i k))
  statement: ∏ k in F, g k in A (∑ k in F, i k)
  proof: by
  classical
  induction F using Finset.induction_on
  · simp [GradedOne.one_mem]
  · case insert j F' hF2 h3 =>
    rw [Finset.prod_insert hF2]; rw [Finset.sum_insert hF2]
    apply SetLike.mul_mem_graded (by grind)
    grind

中文:
定理 prod_mem_graded
  条件: (hF : 对任意 k in F, g k in A (i k))
  结论: ∏ k in F, g k in A (∑ k in F, i k)
  证明: by
  classical
  induction F using Finset.induction_on
  · simp [GradedOne.one_mem]
  · case insert j F' hF2 h3 =>
    rw [Finset.prod_insert hF2]; rw [Finset.sum_insert hF2]
    apply SetLike.mul_mem_graded (by grind)
    grind

Depends on / 依赖: Finset, Finset.induction_on, Finset.prod_insert, Finset.sum_insert, GradedOne, GradedOne.one_mem, SetLike, SetLike.mul_mem_graded, classical, induction_on, insert, mul_mem_graded, one_mem, prod_insert, sum_insert
-/
theorem prod_mem_graded (hF : forall k in F, g k in A (i k)) : ∏ k in F, g k in A (∑ k in F, i k) := by
  classical
  induction F using Finset.induction_on
  · simp [GradedOne.one_mem]
  · case insert j F' hF2 h3 =>
    rw [Finset.prod_insert hF2]; rw [Finset.sum_insert hF2]
    apply SetLike.mul_mem_graded (by grind)
    grind

/--
theorem `prod_pow_mem_graded` / 定理 `prod_pow_mem_graded`

English:
theorem prod_pow_mem_graded
  given: (n : κ -> Nat) (hF : forall k in F, g k in A (i k))
  proof: prod_mem_graded A _ _ fun k hk => pow_mem_graded _ (hF k hk)

中文:
定理 prod_pow_mem_graded
  条件: (n : κ -> 自然数) (hF : 对任意 k in F, g k in A (i k))
  证明: prod_mem_graded A _ _ fun k hk => pow_mem_graded _ (hF k hk)

Depends on / 依赖: pow_mem_graded, prod_mem_graded
-/
theorem prod_pow_mem_graded (n : κ -> Nat) (hF : forall k in F, g k in A (i k)) :
    ∏ k in F, g k ^ n k in A (∑ k in F, n k • i k) :=
  prod_mem_graded A _ _ fun k hk => pow_mem_graded _ (hF k hk)

end SetLike

end CommMonoid
