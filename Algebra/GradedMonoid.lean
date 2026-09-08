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

/-- A type alias of sigma types for graded monoids. -/
/-
**GradedMonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GradedMonoid (A : ι -> Type*)
参数：A : ι -> Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type alias of sigma types for graded monoids.
-/
def GradedMonoid (A : ι → Type*) :=
  Sigma A

namespace GradedMonoid

/-
**GradedMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `GradedMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : ι → Type*} [Inhabited ι] [Inhabited (A default)] : Inhabited (GradedMonoid A) :=
  inferInstanceAs <| Inhabited (Sigma _)

/-- Construct an element of a graded monoid. -/
/-
**GradedMonoid.mk** 是 Mathlib 中的一个定义，位于命名空间 `GradedMonoid`。
形式化陈述：mk {A : ι -> Type*} : forall i, A i -> GradedMonoid A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an element of a graded monoid.
-/
def mk {A : ι → Type*} : ∀ i, A i → GradedMonoid A :=
  Sigma.mk

/-! ### Actions -/

section actions
variable {α β} {A : ι → Type*}

/-- If `R` acts on each `A i`, then it acts on `GradedMonoid A` via the `.2` projection. -/
/-
**GradedMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `GradedMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` acts on each `A i`, then it acts on `GradedMonoid A` via the `.2` project
ion.
-/
instance [∀ i, SMul α (A i)] : SMul α (GradedMonoid A) where
  smul r g := GradedMonoid.mk g.1 (r • g.2)
/-
**GradedMonoid.fst_smul** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {A : ι → Type u_2} [inst : (i : ι) → SMul 
α (A i)] (a : α) (x : GradedMonoid A),   (a • x).fst = x.fst
参数：i : ι；A i；a : α；x : GradedMonoid A；a • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_smul [∀ i, SMul α (A i)] (a : α) (x : GradedMonoid A) :
    (a • x).fst = x.fst := rfl
/-
**GradedMonoid.snd_smul** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {A : ι → Type u_2} [inst : (i : ι) → SMul 
α (A i)] (a : α) (x : GradedMonoid A),   (a • x).snd = a • x.snd
参数：i : ι；A i；a : α；x : GradedMonoid A；a • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_smul [∀ i, SMul α (A i)] (a : α) (x : GradedMonoid A) :
    (a • x).snd = a • x.snd := rfl
/-
**GradedMonoid.smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid`。
形式化陈述：smul_mk [forall i, SMul α (A i)] {i} (c : α) (a : A i) : c • mk i a = mk i
 (c • a)
参数：A i；c : α；a : A i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_mk [∀ i, SMul α (A i)] {i} (c : α) (a : A i) :
    c • mk i a = mk i (c • a) :=
  rfl
/-
**GradedMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `GradedMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, SMul α (A i)] [∀ i, SMul β (A i)]
    [∀ i, SMulCommClass α β (A i)] :
    SMulCommClass α β (GradedMonoid A) where
  smul_comm a b g := Sigma.ext rfl <| heq_of_eq <| smul_comm a b g.2
/-
**GradedMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `GradedMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul α β] [∀ i, SMul α (A i)] [∀ i, SMul β (A i)]
    [∀ i, IsScalarTower α β (A i)] :
    IsScalarTower α β (GradedMonoid A) where
  smul_assoc a b g := Sigma.ext rfl <| heq_of_eq <| smul_assoc a b g.2
/-
**GradedMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `GradedMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] [∀ i, MulAction α (A i)] :
    MulAction α (GradedMonoid A) where
  one_smul g := Sigma.ext rfl <| heq_of_eq <| one_smul _ g.2
  mul_smul r₁ r₂ g := Sigma.ext rfl <| heq_of_eq <| mul_smul r₁ r₂ g.2

end actions

/-! ### Typeclasses -/

section Defs

variable (A : ι → Type*)

/-- A graded version of `One`, which must be of grade 0. -/
/-
**GradedMonoid.GOne** 是 Mathlib 中的一个归纳类型，位于命名空间 `GradedMonoid`。
形式化陈述：{ι : Type u_1} → (ι → Type u_2) → [Zero ι] → Type u_2
参数：ι → Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `One`, which must be of grade 0.
-/
class GOne [Zero ι] where
  /-- The term `one` of grade 0 -/
  one : A 0

/-- `GOne` implies `One (GradedMonoid A)` -/
/-
**GradedMonoid.GOne.toOne** 是 Mathlib 中的一个定义，位于命名空间 `GradedMonoid.GOne`。
形式化陈述：{ι : Type u_1} → (A : ι → Type u_2) → [inst : Zero ι] → [GradedMonoid.GOne
 A] → One (GradedMonoid A)
参数：A : ι → Type u_2；GradedMonoid A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`GOne` implies `One (GradedMonoid A)`
-/
instance GOne.toOne [Zero ι] [GOne A] : One (GradedMonoid A) :=
  ⟨⟨_, GOne.one⟩⟩
/-
**GradedMonoid.fst_one** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid`。
形式化陈述：∀ {ι : Type u_1} (A : ι → Type u_2) [inst : Zero ι] [inst_1 : GradedMonoid
.GOne A], Sigma.fst 1 = 0
参数：A : ι → Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_one [Zero ι] [GOne A] : (1 : GradedMonoid A).fst = 0 := rfl
/-
**GradedMonoid.snd_one** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid`。
形式化陈述：∀ {ι : Type u_1} (A : ι → Type u_2) [inst : Zero ι] [inst_1 : GradedMonoid
.GOne A], Sigma.snd 1 = GradedMonoid.GOne.one
参数：A : ι → Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_one [Zero ι] [GOne A] : (1 : GradedMonoid A).snd = GOne.one := rfl

/-- A graded version of `Mul`. Multiplication combines grades additively, like
`AddMonoidAlgebra`. -/
/-
**GradedMonoid.GMul** 是 Mathlib 中的一个归纳类型，位于命名空间 `GradedMonoid`。
形式化陈述：{ι : Type u_1} → (ι → Type u_2) → [Add ι] → Type (max u_1 u_2)
参数：ι → Type u_2；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `Mul`. Multiplication combines grades additively, like
`AddMonoidAlgebra`.
-/
class GMul [Add ι] where
  /-- The homogeneous multiplication map `mul` -/
  mul {i j} : A i → A j → A (i + j)

/-- `GMul` implies `Mul (GradedMonoid A)`. -/
/-
**GradedMonoid.GMul.toMul** 是 Mathlib 中的一个定义，位于命名空间 `GradedMonoid.GMul`。
形式化陈述：{ι : Type u_1} → (A : ι → Type u_2) → [inst : Add ι] → [GradedMonoid.GMul 
A] → Mul (GradedMonoid A)
参数：A : ι → Type u_2；GradedMonoid A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`GMul` implies `Mul (GradedMonoid A)`.
-/
instance GMul.toMul [Add ι] [GMul A] : Mul (GradedMonoid A) :=
  ⟨fun x y => ⟨_, GMul.mul x.snd y.snd⟩⟩
/-
**GradedMonoid.fst_mul** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid`。
形式化陈述：∀ {ι : Type u_1} (A : ι → Type u_2) [inst : Add ι] [inst_1 : GradedMonoid.
GMul A] (x y : GradedMonoid A),   (x * y).fst = x.fst + y.fst
参数：A : ι → Type u_2；x y : GradedMonoid A；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_mul [Add ι] [GMul A] (x y : GradedMonoid A) :
    (x * y).fst = x.fst + y.fst := rfl
/-
**GradedMonoid.snd_mul** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid`。
形式化陈述：∀ {ι : Type u_1} (A : ι → Type u_2) [inst : Add ι] [inst_1 : GradedMonoid.
GMul A] (x y : GradedMonoid A),   (x * y).snd = GradedMonoid.GMul.mul x.snd y.sn
d
参数：A : ι → Type u_2；x y : GradedMonoid A；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_mul [Add ι] [GMul A] (x y : GradedMonoid A) :
    (x * y).snd = GMul.mul x.snd y.snd := rfl
/-
**GradedMonoid.mk_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid`。
形式化陈述：mk_mul_mk [Add ι] [GMul A] {i j} (a : A i) (b : A j) : mk i a * mk j b = m
k (i + j) (GMul.mul a b)
参数：a : A i；b : A j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mul_mk [Add ι] [GMul A] {i j} (a : A i) (b : A j) :
    mk i a * mk j b = mk (i + j) (GMul.mul a b) :=
  rfl

namespace GMonoid

variable {A}
variable [AddMonoid ι] [GMul A] [GOne A]

/-- A default implementation of power on a graded monoid, like `npowRec`.
`GMonoid.gnpow` should be used instead. -/
/-
**GradedMonoid.GMonoid.gnpowRec** 是 Mathlib 中的一个定义，位于命名空间 `GradedMonoid.GMonoid`
。
形式化陈述：{ι : Type u_1} →   {A : ι → Type u_2} →     [inst : AddMonoid ι] → [Graded
Monoid.GMul A] → [GradedMonoid.GOne A] → (n : ℕ) → {i : ι} → A i → A (n • i)
参数：n : ℕ；n • i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A default implementation of power on a graded monoid, like `npowRec`.
`GMonoid.gnpow` should be used instead.
-/
def gnpowRec : ∀ (n : ℕ) {i}, A i → A (n • i)
  | 0, i, _ => cast (congr_arg A (zero_nsmul i).symm) GOne.one
  | n + 1, i, a => cast (congr_arg A (succ_nsmul i n).symm) (GMul.mul (gnpowRec _ a) a)

@[simp]
/-
**GradedMonoid.GMonoid.gnpowRec_zero** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid.GMo
noid`。
形式化陈述：gnpowRec_zero (a : GradedMonoid A) : GradedMonoid.mk _ (gnpowRec 0 a.snd) 
= 1
参数：a : GradedMonoid A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.ext`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x.fst = y.fs
t → x.snd ≍ y.snd → x = y
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `HEq.symm`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → b ≍ a
· 使用定理 `heq_of_cast_eq`：∀ {α β : Sort u_1} {a : α} {a' : β} (e : α = β), cast e 
a = a' → a ≍ a'
-/
theorem gnpowRec_zero (a : GradedMonoid A) : GradedMonoid.mk _ (gnpowRec 0 a.snd) = 1 :=
  Sigma.ext (zero_nsmul _) (heq_of_cast_eq _ rfl).symm

@[simp]
/-
**GradedMonoid.GMonoid.gnpowRec_succ** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid.GMo
noid`。
形式化陈述：gnpowRec_succ (n : Nat) (a : GradedMonoid A) : (GradedMonoid.mk _ <| gnpow
Rec n.succ a.snd) = ⟨_, gnpowRec n a.snd⟩ * a
参数：n : Nat；a : GradedMonoid A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.ext`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x.fst = y.fs
t → x.snd ≍ y.snd → x = y
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `HEq.symm`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → b ≍ a
· 使用定理 `heq_of_cast_eq`：∀ {α β : Sort u_1} {a : α} {a' : β} (e : α = β), cast e 
a = a' → a ≍ a'
-/
theorem gnpowRec_succ (n : ℕ) (a : GradedMonoid A) :
    (GradedMonoid.mk _ <| gnpowRec n.succ a.snd) = ⟨_, gnpowRec n a.snd⟩ * a :=
  Sigma.ext (succ_nsmul _ _) (heq_of_cast_eq _ rfl).symm

end GMonoid

/-- A tactic to for use as an optional value for `GMonoid.gnpow_zero'`. -/
macro "apply_gmonoid_gnpowRec_zero_tac" : tactic => `(tactic| apply GMonoid.gnpowRec_zero)
/-- A tactic to for use as an optional value for `GMonoid.gnpow_succ'`. -/
macro "apply_gmonoid_gnpowRec_succ_tac" : tactic => `(tactic| apply GMonoid.gnpowRec_succ)

/-- A graded version of `Monoid`

Like `Monoid.npow`, this has an optional `GMonoid.gnpow` field to allow definitional control of
natural powers of a graded monoid. -/
/-
**GradedMonoid.GMonoid** 是 Mathlib 中的一个类，位于命名空间 `GradedMonoid`。
形式化陈述：GMonoid [AddMonoid ι] extends GMul A, GOne A where /-- Multiplication by `
one` on the left is the identity -/ one_mul (a : GradedMonoid A) : 1 * a = a /--
 Multiplication by `one` on the right is the identity -/ mul_one (a : GradedMono
id A) : a * 1 = a /-- Multiplication is associative -/ mul_assoc (a b c : Graded
Monoid A) : a * b * c = a * (b * c) /-- Optional field to allow definitional con
trol of natural powers -/ gnpow : forall (n : Nat) {i}, A i -> A (n • i)
参数：a : GradedMonoid A。
继承自：GMul A, GOne A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `Monoid`

Like `Monoid.npow`, this has an optional `GMonoid.gnpow` field to allow definiti
onal control of
natural powers of a graded monoid.
-/
class GMonoid [AddMonoid ι] extends GMul A, GOne A where
  /-- Multiplication by `one` on the left is the identity -/
  one_mul (a : GradedMonoid A) : 1 * a = a
  /-- Multiplication by `one` on the right is the identity -/
  mul_one (a : GradedMonoid A) : a * 1 = a
  /-- Multiplication is associative -/
  mul_assoc (a b c : GradedMonoid A) : a * b * c = a * (b * c)
  /-- Optional field to allow definitional control of natural powers -/
  gnpow : ∀ (n : ℕ) {i}, A i → A (n • i) := GMonoid.gnpowRec
  /-- The zeroth power will yield 1 -/
  gnpow_zero' : ∀ a : GradedMonoid A, GradedMonoid.mk _ (gnpow 0 a.snd) = 1 := by
    apply_gmonoid_gnpowRec_zero_tac
  /-- Successor powers behave as expected -/
  gnpow_succ' :
    ∀ (n : ℕ) (a : GradedMonoid A),
      (GradedMonoid.mk _ <| gnpow n.succ a.snd) = ⟨_, gnpow n a.snd⟩ * a := by
    apply_gmonoid_gnpowRec_succ_tac

/-- `GMonoid` implies a `Monoid (GradedMonoid A)`. -/
/-
**GradedMonoid.GMonoid.toMonoid** 是 Mathlib 中的一个定义，位于命名空间 `GradedMonoid.GMonoid`
。
形式化陈述：{ι : Type u_1} → (A : ι → Type u_2) → [inst : AddMonoid ι] → [GradedMonoid
.GMonoid A] → Monoid (GradedMonoid A)
参数：A : ι → Type u_2；GradedMonoid A。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GradedMonoid.GMonoid.mul_assoc`：∀ {ι : Type u_1} {A : ι → Type u_2} {ins
t : AddMonoid ι} [self : GradedMonoid.GMonoid A] (a b c : GradedMonoid A),   a *
 b * c = a * (b * c)
· 使用定理 `GradedMonoid.GMonoid.one_mul`：∀ {ι : Type u_1} {A : ι → Type u_2} {inst 
: AddMonoid ι} [self : GradedMonoid.GMonoid A] (a : GradedMonoid A), 1 * a = a
· 使用定理 `GradedMonoid.GMonoid.mul_one`：∀ {ι : Type u_1} {A : ι → Type u_2} {inst 
: AddMonoid ι} [self : GradedMonoid.GMonoid A] (a : GradedMonoid A), a * 1 = a
· 使用定理 `GradedMonoid.GMonoid.gnpow_zero'`：∀ {ι : Type u_1} {A : ι → Type u_2} {i
nst : AddMonoid ι} [self : GradedMonoid.GMonoid A] (a : GradedMonoid A),   Grade
dMonoid.mk (0 • a.fst)…
· 使用定理 `GradedMonoid.GMonoid.gnpow_succ'`：∀ {ι : Type u_1} {A : ι → Type u_2} {i
nst : AddMonoid ι} [self : GradedMonoid.GMonoid A] (n : ℕ) (a : GradedMonoid A),
   GradedMonoid.mk (n.…

--- 原说明 ---
`GMonoid` implies a `Monoid (GradedMonoid A)`.
-/
instance GMonoid.toMonoid [AddMonoid ι] [GMonoid A] : Monoid (GradedMonoid A) where
  npow n a := GradedMonoid.mk _ (GMonoid.gnpow n a.snd)
  npow_zero a := GMonoid.gnpow_zero' a
  npow_succ n a := GMonoid.gnpow_succ' n a
  one_mul := GMonoid.one_mul
  mul_one := GMonoid.mul_one
  mul_assoc := GMonoid.mul_assoc
/-
**GradedMonoid.fst_pow** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid`。
形式化陈述：∀ {ι : Type u_1} (A : ι → Type u_2) [inst : AddMonoid ι] [inst_1 : GradedM
onoid.GMonoid A] (x : GradedMonoid A) (n : ℕ),   (x ^ n).fst = n • x.fst
参数：A : ι → Type u_2；x : GradedMonoid A；n : ℕ；x ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_pow [AddMonoid ι] [GMonoid A] (x : GradedMonoid A) (n : ℕ) :
    (x ^ n).fst = n • x.fst := rfl
/-
**GradedMonoid.snd_pow** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid`。
形式化陈述：∀ {ι : Type u_1} (A : ι → Type u_2) [inst : AddMonoid ι] [inst_1 : GradedM
onoid.GMonoid A] (x : GradedMonoid A) (n : ℕ),   (x ^ n).snd = GradedMonoid.GMon
oid.gnpow n x.snd
参数：A : ι → Type u_2；x : GradedMonoid A；n : ℕ；x ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_pow [AddMonoid ι] [GMonoid A] (x : GradedMonoid A) (n : ℕ) :
    (x ^ n).snd = GMonoid.gnpow n x.snd := rfl
/-
**GradedMonoid.mk_pow** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid`。
形式化陈述：mk_pow [AddMonoid ι] [GMonoid A] {i} (a : A i) (n : Nat) : mk i a ^ n = mk
 (n • i) (GMonoid.gnpow _ a)
参数：a : A i；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_pow [AddMonoid ι] [GMonoid A] {i} (a : A i) (n : ℕ) :
    mk i a ^ n = mk (n • i) (GMonoid.gnpow _ a) := rfl

/-- A graded version of `CommMonoid`. -/
/-
**GradedMonoid.GCommMonoid** 是 Mathlib 中的一个归纳类型，位于命名空间 `GradedMonoid`。
形式化陈述：{ι : Type u_1} → (ι → Type u_2) → [AddCommMonoid ι] → Type (max u_1 u_2)
参数：ι → Type u_2；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `CommMonoid`.
-/
class GCommMonoid [AddCommMonoid ι] extends GMonoid A where
  /-- Multiplication is commutative -/
  mul_comm (a : GradedMonoid A) (b : GradedMonoid A) : a * b = b * a

/-- `GCommMonoid` implies a `CommMonoid (GradedMonoid A)`, although this is only used as an
/-
**GradedMonoid.locally** 是 Mathlib 中的一个实例，位于命名空间 `GradedMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance locally to define notation in `gmonoid` and similar typeclasses. -/
/-
**GradedMonoid.GCommMonoid.toCommMonoid** 是 Mathlib 中的一个定义，位于命名空间 `GradedMonoid.
GCommMonoid`。
形式化陈述：{ι : Type u_1} →   (A : ι → Type u_2) → [inst : AddCommMonoid ι] → [Graded
Monoid.GCommMonoid A] → CommMonoid (GradedMonoid A)
参数：A : ι → Type u_2；GradedMonoid A。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GradedMonoid.GCommMonoid.mul_comm`：∀ {ι : Type u_1} {A : ι → Type u_2} {
inst : AddCommMonoid ι} [self : GradedMonoid.GCommMonoid A] (a b : GradedMonoid 
A),   a * b = b * a

--- 原说明 ---
`GCommMonoid` implies a `CommMonoid (GradedMonoid A)`, although this is only use
d as an
instance locally to define notation in `gmonoid` and similar typeclasses.
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

variable (A : ι → Type*)

section One

variable [Zero ι] [GOne A]

/-- `1 : A 0` is the value provided in `GOne.one`. -/
@[nolint unusedArguments]
/-
**GradedMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `GradedMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`1 : A 0` is the value provided in `GOne.one`.
-/
instance (priority := 900) GradeZero.one : One (A 0) :=
  ⟨GOne.one⟩

end One

section Mul

variable [AddZeroClass ι] [GMul A]

/-- `(•) : A 0 → A i → A i` is the value provided in `GradedMonoid.GMul.mul`, composed with
an `Eq.rec` to turn `A (0 + i)` into `A i`.
-/
/-
**GradedMonoid.GradeZero.smul** 是 Mathlib 中的一个定义，位于命名空间 `GradedMonoid.GradeZero`
。
形式化陈述：{ι : Type u_1} → (A : ι → Type u_2) → [inst : AddZeroClass ι] → [GradedMon
oid.GMul A] → (i : ι) → SMul (A 0) (A i)
参数：A : ι → Type u_2；i : ι；A 0；A i。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
`(•) : A 0 → A i → A i` is the value provided in `GradedMonoid.GMul.mul`, compos
ed with
an `Eq.rec` to turn `A (0 + i)` into `A i`.
-/
instance GradeZero.smul (i : ι) : SMul (A 0) (A i) where
  smul x y := @Eq.rec ι (0 + i) (fun a _ => A a) (GMul.mul x y) i (zero_add i)

/-- `(*) : A 0 → A 0 → A 0` is the value provided in `GradedMonoid.GMul.mul`, composed with
an `Eq.rec` to turn `A (0 + 0)` into `A 0`.
-/
/-
**GradedMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `GradedMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(*) : A 0 → A 0 → A 0` is the value provided in `GradedMonoid.GMul.mul`, compos
ed with
an `Eq.rec` to turn `A (0 + 0)` into `A 0`.
-/
instance (priority := 900) GradeZero.mul : Mul (A 0) where mul := (· • ·)

variable {A}

@[simp]
/-
**GradedMonoid.mk_zero_smul** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid`。
形式化陈述：mk_zero_smul {i} (a : A 0) (b : A i) : mk _ (a • b) = mk _ a * mk _ b
参数：a : A 0；b : A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.ext`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x.fst = y.fs
t → x.snd ≍ y.snd → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eqRec_heq`：∀ {α : Sort u} {φ : α → Sort v} {a a' : α} (h : a = a') (p : 
φ a), Eq.recOn h p ≍ p
-/
theorem mk_zero_smul {i} (a : A 0) (b : A i) : mk _ (a • b) = mk _ a * mk _ b :=
  Sigma.ext (zero_add _).symm <| eqRec_heq _ _

@[scoped simp]
/-
**GradedMonoid.GradeZero.smul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid.Gra
deZero`。
形式化陈述：∀ {ι : Type u_1} {A : ι → Type u_2} [inst : AddZeroClass ι] [inst_1 : Grad
edMonoid.GMul A] (a b : A 0), a • b = a * b
参数：a b : A 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem GradeZero.smul_eq_mul (a b : A 0) : a • b = a * b :=
  rfl

end Mul

section Monoid

variable [AddMonoid ι] [GMonoid A]

/-
**GradedMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `GradedMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatPow (A 0) where
  pow x n := @Eq.rec ι (n • (0 : ι)) (fun a _ => A a) (GMonoid.gnpow n x) 0 (nsmul_zero n)

variable {A} in
@[simp]
/-
**GradedMonoid.mk_zero_pow** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid`。
形式化陈述：mk_zero_pow (a : A 0) (n : Nat) : mk _ (a ^ n) = mk _ a ^ n
参数：a : A 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.ext`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x.fst = y.fs
t → x.snd ≍ y.snd → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `eqRec_heq`：∀ {α : Sort u} {φ : α → Sort v} {a a' : α} (h : a = a') (p : 
φ a), Eq.recOn h p ≍ p
-/
theorem mk_zero_pow (a : A 0) (n : ℕ) : mk _ (a ^ n) = mk _ a ^ n :=
  Sigma.ext (nsmul_zero n).symm <| eqRec_heq _ _

/-- The `Monoid` structure derived from `GMonoid A`. -/
/-
**GradedMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `GradedMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Monoid` structure derived from `GMonoid A`.
-/
instance (priority := 900) GradeZero.monoid : Monoid (A 0) :=
  Function.Injective.monoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow

end Monoid

section Monoid

variable [AddCommMonoid ι] [GCommMonoid A]

/-- The `CommMonoid` structure derived from `GCommMonoid A`. -/
/-
**GradedMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `GradedMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `CommMonoid` structure derived from `GCommMonoid A`.
-/
instance (priority := 900) GradeZero.commMonoid : CommMonoid (A 0) :=
  Function.Injective.commMonoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow

end Monoid

section MulAction

variable [AddMonoid ι] [GMonoid A]

/-- `GradedMonoid.mk 0` is a `MonoidHom`, using the `GradedMonoid.GradeZero.monoid` structure.
-/
/-
**GradedMonoid.mkZeroMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `GradedMonoid`。
形式化陈述：mkZeroMonoidHom : A 0 ->* GradedMonoid A where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`GradedMonoid.mk 0` is a `MonoidHom`, using the `GradedMonoid.GradeZero.monoid` 
structure.
-/
def mkZeroMonoidHom : A 0 →* GradedMonoid A where
  toFun := mk 0
  map_one' := rfl
  map_mul' := mk_zero_smul

/-- Each grade `A i` derives an `A 0`-action structure from `GMonoid A`. -/
/-
**GradedMonoid.GradeZero.mulAction** 是 Mathlib 中的一个定义，位于命名空间 `GradedMonoid.Grade
Zero`。
形式化陈述：{ι : Type u_1} →   (A : ι → Type u_2) → [inst : AddMonoid ι] → [inst_1 : G
radedMonoid.GMonoid A] → {i : ι} → MulAction (A 0) (A i)
参数：A : ι → Type u_2；A 0；A i。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)

--- 原说明 ---
Each grade `A i` derives an `A 0`-action structure from `GMonoid A`.
-/
instance GradeZero.mulAction {i} : MulAction (A 0) (A i) :=
  letI := MulAction.compHom (GradedMonoid A) (mkZeroMonoidHom A)
  Function.Injective.mulAction (mk i) sigma_mk_injective mk_zero_smul

end MulAction

end GradeZero

end GradedMonoid

/-! ### Dependent products of graded elements -/


section DProd

variable {α : Type*} {A : ι → Type*} [AddMonoid ι] [GradedMonoid.GMonoid A]

/-- The index used by `List.dProd`. Propositionally this is equal to `(l.map fι).Sum`, but
definitionally it needs to have a different form to avoid introducing `Eq.rec`s in `List.dProd`. -/
/-
**List.dProdIndex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：List.dProdIndex (l : List α) (fι : α -> ι) : ι
参数：l : List α；fι : α -> ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The index used by `List.dProd`. Propositionally this is equal to `(l.map fι).Sum
`, but
definitionally it needs to have a different form to avoid introducing `Eq.rec`s 
in `List.dProd`.
-/
def List.dProdIndex (l : List α) (fι : α → ι) : ι :=
  l.foldr (fun i b => fι i + b) 0

@[simp]
/-
**List.dProdIndex_nil** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.dProdIndex_nil (fι : α -> ι) : ([] : List α).dProdIndex fι = 0
参数：fι : α -> ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem List.dProdIndex_nil (fι : α → ι) : ([] : List α).dProdIndex fι = 0 :=
  rfl

@[simp]
/-
**List.dProdIndex_cons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.dProdIndex_cons (a : α) (l : List α) (fι : α -> ι) : (a :: l).dProdIn
dex fι = fι a + l.dProdIndex fι
参数：a : α；l : List α；fι : α -> ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem List.dProdIndex_cons (a : α) (l : List α) (fι : α → ι) :
    (a :: l).dProdIndex fι = fι a + l.dProdIndex fι :=
  rfl
/-
**List.dProdIndex_eq_map_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.dProdIndex_eq_map_sum (l : List α) (fι : α -> ι) : l.dProdIndex fι = 
(l.map fι).sum
参数：l : List α；fι : α -> ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem List.dProdIndex_eq_map_sum (l : List α) (fι : α → ι) :
    l.dProdIndex fι = (l.map fι).sum := by
  match l with
  | [] => simp
  | head::tail => simp [List.dProdIndex_eq_map_sum tail fι]

/-- A dependent product for graded monoids represented by the indexed family of types `A i`.
This is a dependent version of `(l.map fA).prod`.

For a list `l : List α`, this computes the product of `fA a` over `a`, where each `fA` is of type
`A (fι a)`. -/
/-
**List.dProd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：List.dProd (l : List α) (fι : α -> ι) (fA : forall a, A (fι a)) : A (l.dPr
odIndex fι)
参数：l : List α；fι : α -> ι；fA : forall a, A (fι a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A dependent product for graded monoids represented by the indexed family of type
s `A i`.
This is a dependent version of `(l.map fA).prod`.

For a list `l : List α`, this computes the product of `fA a` over `a`, where eac
h `fA` is of type
`A (fι a)`.
-/
def List.dProd (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) : A (l.dProdIndex fι) :=
  l.foldrRecOn _ GradedMonoid.GOne.one fun _ x a _ => GradedMonoid.GMul.mul (fA a) x

@[simp]
/-
**List.dProd_nil** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.dProd_nil (fι : α -> ι) (fA : forall a, A (fι a)) : (List.nil : List 
α).dProd fι fA = GradedMonoid.GOne.one
参数：fι : α -> ι；fA : forall a, A (fι a)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem List.dProd_nil (fι : α → ι) (fA : ∀ a, A (fι a)) :
    (List.nil : List α).dProd fι fA = GradedMonoid.GOne.one :=
  rfl

-- the `( :)` in this lemma statement results in the type on the RHS not being unfolded, which
-- is nicer in the goal view.
@[simp]
/-
**List.dProd_cons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.dProd_cons (fι : α -> ι) (fA : forall a, A (fι a)) (a : α) (l : List 
α) : (a :: l).dProd fι fA = (GradedMonoid.GMul.mul (fA a) (l.dProd fι fA) :)
参数：fι : α -> ι；fA : forall a, A (fι a)；a : α；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem List.dProd_cons (fι : α → ι) (fA : ∀ a, A (fι a)) (a : α) (l : List α) :
    (a :: l).dProd fι fA = (GradedMonoid.GMul.mul (fA a) (l.dProd fι fA) :) :=
  rfl
/-
**GradedMonoid.mk_list_dProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GradedMonoid.mk_list_dProd (l : List α) (fι : α -> ι) (fA : forall a, A (f
ι a)) : GradedMonoid.mk _ (l.dProd fι fA) = (l.map fun a => GradedMonoid.mk (fι 
a) (fA a)).prod
参数：l : List α；fι : α -> ι；fA : forall a, A (fι a)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem GradedMonoid.mk_list_dProd (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) :
    GradedMonoid.mk _ (l.dProd fι fA) = (l.map fun a => GradedMonoid.mk (fι a) (fA a)).prod := by
  match l with
  | [] => simp only [List.dProdIndex_nil, List.dProd_nil, List.map_nil, List.prod_nil]; rfl
  | head::tail =>
    simp [← GradedMonoid.mk_list_dProd tail _ _, GradedMonoid.mk_mul_mk, List.prod_cons]

set_option backward.isDefEq.respectTransparency false in
/-- A variant of `GradedMonoid.mk_list_dProd` for rewriting in the other direction. -/
/-
**GradedMonoid.list_prod_map_eq_dProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GradedMonoid.list_prod_map_eq_dProd (l : List α) (f : α -> GradedMonoid A)
 : (l.map f).prod = GradedMonoid.mk _ (l.dProd (fun i => (f i).1) fun i => (f i)
.2)
参数：l : List α；f : α -> GradedMonoid A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GradedMonoid.mk_list_dProd`：GradedMonoid.mk_list_dProd (l : List α) (fι 
: α -> ι) (fA : forall a, A (fι a)) : GradedMonoid.mk _ (l.dProd fι fA) = (l.map
 fun a => Graded…
· 使用定理 `GradedMonoid.mk.eq_1`：∀ {ι : Type u_1} {A : ι → Type u_2}, GradedMonoid.
mk = Sigma.mk
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A variant of `GradedMonoid.mk_list_dProd` for rewriting in the other direction.
-/
theorem GradedMonoid.list_prod_map_eq_dProd (l : List α) (f : α → GradedMonoid A) :
    (l.map f).prod = GradedMonoid.mk _ (l.dProd (fun i => (f i).1) fun i => (f i).2) := by
  rw [GradedMonoid.mk_list_dProd, GradedMonoid.mk]
  simp_rw [Sigma.eta]
/-
**GradedMonoid.list_prod_ofFn_eq_dProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GradedMonoid.list_prod_ofFn_eq_dProd {n : Nat} (f : Fin n -> GradedMonoid 
A) : (List.ofFn f).prod = GradedMonoid.mk _ ((List.finRange n).dProd (fun i => (
f i).1) fun i => (f i).2)
参数：f : Fin n -> GradedMonoid A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_eq_map`：ofFn_eq_map {n} {f : Fin n -> α} : ofFn f = (finRange 
n).map f
· 使用定理 `GradedMonoid.list_prod_map_eq_dProd`：GradedMonoid.list_prod_map_eq_dProd
 (l : List α) (f : α -> GradedMonoid A) : (l.map f).prod = GradedMonoid.mk _ (l.
dProd (fun i => (f i).1) …
-/
theorem GradedMonoid.list_prod_ofFn_eq_dProd {n : ℕ} (f : Fin n → GradedMonoid A) :
    (List.ofFn f).prod =
      GradedMonoid.mk _ ((List.finRange n).dProd (fun i => (f i).1) fun i => (f i).2) := by
  rw [List.ofFn_eq_map, GradedMonoid.list_prod_map_eq_dProd]

end DProd

/-! ### Concrete instances -/


section

variable (ι) {R : Type*}

@[simps one]
/-
**One.gOne** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：One.gOne [Zero ι] [One R] : GradedMonoid.GOne fun _ : ι => R where one
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance One.gOne [Zero ι] [One R] : GradedMonoid.GOne fun _ : ι => R where one := 1

@[simps mul]
/-
**Mul.gMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Mul.gMul [Add ι] [Mul R] : GradedMonoid.GMul fun _ : ι => R where mul x y
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Mul.gMul [Add ι] [Mul R] : GradedMonoid.GMul fun _ : ι => R where mul x y := x * y

/-- If all grades are the same type and themselves form a monoid, then there is a trivial grading
structure. -/
@[simps gnpow]
/-
**Monoid.gMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Monoid.gMonoid [AddMonoid ι] [Monoid R] : GradedMonoid.GMonoid fun _ : ι =
> R where one_mul
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If all grades are the same type and themselves form a monoid, then there is a tr
ivial grading
structure.
-/
instance Monoid.gMonoid [AddMonoid ι] [Monoid R] : GradedMonoid.GMonoid fun _ : ι => R where
  one_mul := fun _ => Sigma.ext (zero_add _) (heq_of_eq (one_mul _))
  mul_one := fun _ => Sigma.ext (add_zero _) (heq_of_eq (mul_one _))
  mul_assoc := fun _ _ _ => Sigma.ext (add_assoc _ _ _) (heq_of_eq (mul_assoc _ _ _))
  gnpow := fun n _ a => a ^ n
  gnpow_zero' := fun _ => Sigma.ext (zero_nsmul _) (heq_of_eq (Monoid.npow_zero _))
  gnpow_succ' := fun _ ⟨_, _⟩ => Sigma.ext (succ_nsmul _ _) (heq_of_eq (Monoid.npow_succ _ _))

/-- If all grades are the same type and themselves form a commutative monoid, then there is a
trivial grading structure. -/
/-
**CommMonoid.gCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CommMonoid.gCommMonoid [AddCommMonoid ι] [CommMonoid R] : GradedMonoid.GCo
mmMonoid fun _ : ι => R where mul_comm
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If all grades are the same type and themselves form a commutative monoid, then t
here is a
trivial grading structure.
-/
instance CommMonoid.gCommMonoid [AddCommMonoid ι] [CommMonoid R] :
    GradedMonoid.GCommMonoid fun _ : ι => R where
  mul_comm := fun _ _ => Sigma.ext (add_comm _ _) (heq_of_eq (mul_comm _ _))

/-- When all the indexed types are the same, the dependent product is just the regular product. -/
@[simp]
/-
**List.dProd_monoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.dProd_monoid {α} [AddMonoid ι] [Monoid R] (l : List α) (fι : α -> ι) 
(fA : α -> R) : @List.dProd _ _ (fun _ : ι => R) _ _ l fι fA = (l.map fA).prod
参数：l : List α；fι : α -> ι；fA : α -> R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When all the indexed types are the same, the dependent product is just the regul
ar product.
-/
theorem List.dProd_monoid {α} [AddMonoid ι] [Monoid R] (l : List α) (fι : α → ι) (fA : α → R) :
    @List.dProd _ _ (fun _ : ι => R) _ _ l fι fA = (l.map fA).prod := by
  match l with
  | [] =>
    rw [List.dProd_nil, List.map_nil, List.prod_nil]
    rfl
  | head::tail =>
    rw [List.dProd_cons, List.map_cons, List.prod_cons, List.dProd_monoid tail _ _]
    rfl

end

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable {R : Type*}

/-- A version of `GradedMonoid.GOne` for internally graded objects. -/
/-
**SetLike.GradedOne** 是 Mathlib 中的一个归纳类型，位于命名空间 `SetLike`。
形式化陈述：{ι : Type u_1} → {R : Type u_2} → {S : Type u_3} → [SetLike S R] → [One R]
 → [Zero ι] → (ι → S) → Prop
参数：ι → S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `GradedMonoid.GOne` for internally graded objects.
-/
class SetLike.GradedOne {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι → S) : Prop where
  /-- One has grade zero -/
  one_mem : (1 : R) ∈ A 0
/-
**SetLike.one_mem_graded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.one_mem_graded {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι -
> S) [SetLike.GradedOne A] : (1 : R) in A 0
参数：A : ι -> S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedOne.one_mem`：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3
} {inst : SetLike S R} {inst_1 : One R} {inst_2 : Zero ι} {A : ι → S}   [self : 
SetLike.GradedO…
-/
theorem SetLike.one_mem_graded {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.GradedOne A] : (1 : R) ∈ A 0 :=
  SetLike.GradedOne.one_mem
/-
**SetLike.gOne** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SetLike.gOne {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι -> S) [SetL
ike.GradedOne A] : GradedMonoid.GOne fun i => A i where one
参数：A : ι -> S。
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.one_mem_graded`：SetLike.one_mem_graded {S : Type*} [SetLike S R]
 [One R] [Zero ι] (A : ι -> S) [SetLike.GradedOne A] : (1 : R) in A 0
-/
instance SetLike.gOne {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.GradedOne A] : GradedMonoid.GOne fun i => A i where
  one := ⟨1, SetLike.one_mem_graded _⟩

@[simp]
/-
**SetLike.coe_gOne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.coe_gOne {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι -> S) [
SetLike.GradedOne A] : ↑(@GradedMonoid.GOne.one _ (fun i => A i) _ _) = (1 : R)
参数：A : ι -> S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SetLike.coe_gOne {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.GradedOne A] : ↑(@GradedMonoid.GOne.one _ (fun i => A i) _ _) = (1 : R) :=
  rfl

/-- A version of `GradedMonoid.ghas_one` for internally graded objects. -/
/-
**SetLike.GradedMul** 是 Mathlib 中的一个归纳类型，位于命名空间 `SetLike`。
形式化陈述：{ι : Type u_1} → {R : Type u_2} → {S : Type u_3} → [SetLike S R] → [Mul R]
 → [Add ι] → (ι → S) → Prop
参数：ι → S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `GradedMonoid.ghas_one` for internally graded objects.
-/
class SetLike.GradedMul {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι → S) : Prop where
  /-- Multiplication is homogeneous -/
  mul_mem : ∀ ⦃i j⦄ {gi gj}, gi ∈ A i → gj ∈ A j → gi * gj ∈ A (i + j)
/-
**SetLike.mul_mem_graded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.mul_mem_graded {S : Type*} [SetLike S R] [Mul R] [Add ι] {A : ι ->
 S} [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi in A i) (hj : gj in A j) : gi *
 gj in A (i + j)
参数：hi : gi in A i；hj : gj in A j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedMul.mul_mem`：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3
} {inst : SetLike S R} {inst_1 : Mul R} {inst_2 : Add ι} {A : ι → S}   [self : S
etLike.GradedMu…
-/
theorem SetLike.mul_mem_graded {S : Type*} [SetLike S R] [Mul R] [Add ι] {A : ι → S}
    [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi ∈ A i) (hj : gj ∈ A j) : gi * gj ∈ A (i + j) :=
  SetLike.GradedMul.mul_mem hi hj
/-
**SetLike.gMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SetLike.gMul {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι -> S) [SetLi
ke.GradedMul A] : GradedMonoid.GMul fun i => A i where mul
参数：A : ι -> S。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SetLike.gMul {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι → S)
    [SetLike.GradedMul A] : GradedMonoid.GMul fun i => A i where
  mul := fun a b => ⟨(a * b : R), SetLike.mul_mem_graded a.prop b.prop⟩

@[simp]
/-
**SetLike.coe_gMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.coe_gMul {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι -> S) [S
etLike.GradedMul A] {i j : ι} (x : A i) (y : A j) : ↑(@GradedMonoid.GMul.mul _ (
fun i => A i) _ _ _ _ x y) = (x * y : R)
参数：A : ι -> S；x : A i；y : A j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SetLike.coe_gMul {S : Type*} [SetLike S R] [Mul R] [Add ι] (A : ι → S)
    [SetLike.GradedMul A] {i j : ι} (x : A i) (y : A j) :
    ↑(@GradedMonoid.GMul.mul _ (fun i => A i) _ _ _ _ x y) = (x * y : R) :=
  rfl

/-- A version of `GradedMonoid.GMonoid` for internally graded objects. -/
/-
**SetLike.GradedMonoid** 是 Mathlib 中的一个归纳类型，位于命名空间 `SetLike`。
形式化陈述：{ι : Type u_1} → {R : Type u_2} → {S : Type u_3} → [SetLike S R] → [Monoid
 R] → [AddMonoid ι] → (ι → S) → Prop
参数：ι → S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `GradedMonoid.GMonoid` for internally graded objects.
-/
class SetLike.GradedMonoid {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S) : Prop
    extends SetLike.GradedOne A, SetLike.GradedMul A

namespace SetLike

variable {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι]
variable {A : ι → S} [SetLike.GradedMonoid A]

namespace GradeZero
variable (A) in
/-- The submonoid `A 0` of `R`. -/
@[simps]
/-
**SetLike.GradeZero.submonoid** 是 Mathlib 中的一个定义，位于命名空间 `SetLike.GradeZero`。
形式化陈述：submonoid : Submonoid R where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submonoid `A 0` of `R`.
-/
def submonoid : Submonoid R where
  carrier := A 0
  mul_mem' ha hb := add_zero (0 : ι) ▸ SetLike.mul_mem_graded ha hb
  one_mem' := SetLike.one_mem_graded A

-- TODO: it might be expensive to unify `A` in this instance in practice
/-- The monoid `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A`. -/
/-
**SetLike.GradeZero.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `SetLike.GradeZero`。
形式化陈述：instMonoid : Monoid (A 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoid `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A`.
-/
instance instMonoid : Monoid (A 0) :=
  inferInstanceAs <| Monoid (GradeZero.submonoid A)

-- TODO: it might be expensive to unify `A` in this instance in practice
/-- The commutative monoid `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A`. -/
/-
**SetLike.GradeZero.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `SetLike.GradeZero`
。
形式化陈述：instCommMonoid {R S : Type*} [SetLike S R] [CommMonoid R] {A : ι -> S} [Se
tLike.GradedMonoid A] : CommMonoid (A 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The commutative monoid `A 0` inherited from `R` in the presence of `SetLike.Grad
edMonoid A`.
-/
instance instCommMonoid
    {R S : Type*} [SetLike S R] [CommMonoid R]
    {A : ι → S} [SetLike.GradedMonoid A] :
    CommMonoid (A 0) :=
  inferInstanceAs <| CommMonoid (GradeZero.submonoid A)
/-
**SetLike.GradeZero.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `SetLike.GradeZero`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3} [inst : SetLike S R] [inst_
1 : Monoid R] [inst_2 : AddMonoid ι]   {A : ι → S} [inst_3 : SetLike.GradedMonoi
d A], ↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] theorem coe_one : ↑(1 : A 0) = (1 : R) := rfl
/-
**SetLike.GradeZero.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `SetLike.GradeZero`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3} [inst : SetLike S R] [inst_
1 : Monoid R] [inst_2 : AddMonoid ι]   {A : ι → S} [inst_3 : SetLike.GradedMonoi
d A] (a b : ↥(A 0)), ↑(a * b) = ↑a * ↑b
参数：a b : ↥(A 0)；a * b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] theorem coe_mul (a b : A 0) : ↑(a * b) = (↑a * ↑b : R) := rfl
/-
**SetLike.GradeZero.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `SetLike.GradeZero`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3} [inst : SetLike S R] [inst_
1 : Monoid R] [inst_2 : AddMonoid ι]   {A : ι → S} [inst_3 : SetLike.GradedMonoi
d A] (a : ↥(A 0)) (n : ℕ), ↑(a ^ n) = ↑a ^ n
参数：a : ↥(A 0)；n : ℕ；a ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] theorem coe_pow (a : A 0) (n : ℕ) : ↑(a ^ n) = (↑a : R) ^ n := rfl

end GradeZero

/-
**SetLike.pow_mem_graded** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：pow_mem_graded (n : Nat) {r : R} {i : ι} (h : r in A i) : r ^ n in A (n • 
i)
参数：n : Nat；h : r in A i。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_mem_graded (n : ℕ) {r : R} {i : ι} (h : r ∈ A i) : r ^ n ∈ A (n • i) := by
  match n with
  | 0 =>
    rw [pow_zero, zero_nsmul]
    exact one_mem_graded _
  | n + 1 =>
    rw [pow_succ', succ_nsmul']
    exact mul_mem_graded h (pow_mem_graded n h)
/-
**SetLike.list_prod_map_mem_graded** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：list_prod_map_mem_graded {ι'} (l : List ι') (i : ι' -> ι) (r : ι' -> R) (h
 : forall j in l, r j in A (i j)) : (l.map r).prod in A (l.map i).sum
参数：l : List ι'；i : ι' -> ι；r : ι' -> R；h : forall j in l, r j in A (i j)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem list_prod_map_mem_graded {ι'} (l : List ι') (i : ι' → ι) (r : ι' → R)
    (h : ∀ j ∈ l, r j ∈ A (i j)) : (l.map r).prod ∈ A (l.map i).sum := by
  match l with
  | [] =>
    rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil]
    exact one_mem_graded _
  | head::tail =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons]
    exact
      mul_mem_graded (h _ List.mem_cons_self)
        (list_prod_map_mem_graded tail _ _ fun j hj => h _ <| List.mem_cons_of_mem _ hj)
/-
**SetLike.list_prod_ofFn_mem_graded** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：list_prod_ofFn_mem_graded {n} (i : Fin n -> ι) (r : Fin n -> R) (h : foral
l j, r j in A (i j)) : (List.ofFn r).prod in A (List.ofFn i).sum
参数：i : Fin n -> ι；r : Fin n -> R；h : forall j, r j in A (i j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_eq_map`：ofFn_eq_map {n} {f : Fin n -> α} : ofFn f = (finRange 
n).map f
· 使用定理 `SetLike.list_prod_map_mem_graded`：list_prod_map_mem_graded {ι'} (l : Lis
t ι') (i : ι' -> ι) (r : ι' -> R) (h : forall j in l, r j in A (i j)) : (l.map r
).prod in A (l.map i).…
-/
theorem list_prod_ofFn_mem_graded {n} (i : Fin n → ι) (r : Fin n → R) (h : ∀ j, r j ∈ A (i j)) :
    (List.ofFn r).prod ∈ A (List.ofFn i).sum := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  exact list_prod_map_mem_graded _ _ _ fun _ _ => h _

end SetLike

/-- Build a `GMonoid` instance for a collection of subobjects. -/
/-
**SetLike.gMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SetLike.gMonoid {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι 
-> S) [SetLike.GradedMonoid A] : GradedMonoid.GMonoid fun i => A i where one_mul
参数：A : ι -> S。
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…

--- 原说明 ---
Build a `GMonoid` instance for a collection of subobjects.
-/
instance SetLike.gMonoid {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] : GradedMonoid.GMonoid fun i => A i where
  one_mul := fun ⟨_, _, _⟩ => Sigma.subtype_ext (zero_add _) (one_mul _)
  mul_one := fun ⟨_, _, _⟩ => Sigma.subtype_ext (add_zero _) (mul_one _)
  mul_assoc := fun ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩ =>
    Sigma.subtype_ext (add_assoc _ _ _) (mul_assoc _ _ _)
  gnpow := fun n _ a => ⟨(a:R)^n, SetLike.pow_mem_graded n a.prop⟩
  gnpow_zero' := fun _ => Sigma.subtype_ext (zero_nsmul _) (pow_zero _)
  gnpow_succ' := fun _ _ => Sigma.subtype_ext (succ_nsmul _ _) (pow_succ _ _)

@[simp]
/-
**SetLike.coe_gnpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.coe_gnpow {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : 
ι -> S) [SetLike.GradedMonoid A] {i : ι} (x : A i) (n : Nat) : ↑(@GradedMonoid.G
Monoid.gnpow _ (fun i => A i) _ _ n _ x) = (x : R) ^ n
参数：A : ι -> S；x : A i；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SetLike.coe_gnpow {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] {i : ι} (x : A i) (n : ℕ) :
    ↑(@GradedMonoid.GMonoid.gnpow _ (fun i => A i) _ _ n _ x) = (x : R) ^ n :=
  rfl

/-- Build a `GCommMonoid` instance for a collection of subobjects. -/
/-
**SetLike.gCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SetLike.gCommMonoid {S : Type*} [SetLike S R] [CommMonoid R] [AddCommMonoi
d ι] (A : ι -> S) [SetLike.GradedMonoid A] : GradedMonoid.GCommMonoid fun i => A
 i where mul_comm
参数：A : ι -> S。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `GCommMonoid` instance for a collection of subobjects.
-/
instance SetLike.gCommMonoid {S : Type*} [SetLike S R] [CommMonoid R] [AddCommMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] : GradedMonoid.GCommMonoid fun i => A i where
  mul_comm := fun ⟨_, _, _⟩ ⟨_, _, _⟩ => Sigma.subtype_ext (add_comm _ _) (mul_comm _ _)

section DProd

open SetLike SetLike.GradedMonoid

variable {α S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι]

@[simp]
/-
**SetLike.coe_list_dProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.coe_list_dProd (A : ι -> S) [SetLike.GradedMonoid A] (fι : α -> ι)
 (fA : forall a, A (fι a)) (l : List α) : ↑(@List.dProd _ _ (fun i => ↥(A i)) _ 
_ l fι fA) = (List.prod (l.map fun a => fA a) : R)
参数：A : ι -> S；fι : α -> ι；fA : forall a, A (fι a)；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SetLike.coe_list_dProd (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι)
    (fA : ∀ a, A (fι a)) (l : List α) : ↑(@List.dProd _ _ (fun i => ↥(A i)) _ _ l fι fA)
    = (List.prod (l.map fun a => fA a) : R) := by
  match l with
  | [] =>
    rw [List.dProd_nil, coe_gOne, List.map_nil, List.prod_nil]
  | head::tail =>
    rw [List.dProd_cons, coe_gMul, List.map_cons, List.prod_cons,
      SetLike.coe_list_dProd _ _ _ tail]

/-- A version of `List.coe_dProd_set_like` with `Subtype.mk`. -/
/-
**SetLike.list_dProd_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.list_dProd_eq (A : ι -> S) [SetLike.GradedMonoid A] (fι : α -> ι) 
(fA : forall a, A (fι a)) (l : List α) : (@List.dProd _ _ (fun i => ↥(A i)) _ _ 
l fι fA) = ⟨List.prod (l.map fun a => fA a), (l.dProdIndex_eq_map_sum fι).symm ▸
 list_prod_map_mem_graded l _ _ fun i _ => (fA i).prop⟩
参数：A : ι -> S；fι : α -> ι；fA : forall a, A (fι a)；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SetLike.list_prod_map_mem_graded`：list_prod_map_mem_graded {ι'} (l : Lis
t ι') (i : ι' -> ι) (r : ι' -> R) (h : forall j in l, r j in A (i j)) : (l.map r
).prod in A (l.map i).…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.dProdIndex_eq_map_sum`：List.dProdIndex_eq_map_sum (l : List α) (fι 
: α -> ι) : l.dProdIndex fι = (l.map fι).sum
· 使用定理 `SetLike.coe_list_dProd`：SetLike.coe_list_dProd (A : ι -> S) [SetLike.Gra
dedMonoid A] (fι : α -> ι) (fA : forall a, A (fι a)) (l : List α) : ↑(@List.dPro
d _ _ (fun i…

--- 原说明 ---
A version of `List.coe_dProd_set_like` with `Subtype.mk`.
-/
theorem SetLike.list_dProd_eq (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι) (fA : ∀ a, A (fι a))
    (l : List α) :
    (@List.dProd _ _ (fun i => ↥(A i)) _ _ l fι fA) =
      ⟨List.prod (l.map fun a => fA a),
        (l.dProdIndex_eq_map_sum fι).symm ▸
          list_prod_map_mem_graded l _ _ fun i _ => (fA i).prop⟩ :=
  Subtype.ext <| SetLike.coe_list_dProd _ _ _ _

end DProd

end Subobjects

section HomogeneousElements

variable {R S : Type*} [SetLike S R]

/-- An element `a : R` is said to be homogeneous if there is some `i : ι` such that `a ∈ A i`. -/
/-
**SetLike.IsHomogeneousElem** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SetLike.IsHomogeneousElem (A : ι -> S) (a : R) : Prop
参数：A : ι -> S；a : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `a : R` is said to be homogeneous if there is some `i : ι` such that 
`a ∈ A i`.
-/
def SetLike.IsHomogeneousElem (A : ι → S) (a : R) : Prop :=
  ∃ i, a ∈ A i

@[simp]
/-
**SetLike.isHomogeneousElem_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.isHomogeneousElem_coe {A : ι -> S} {i} (x : A i) : SetLike.IsHomog
eneousElem A (x : R)
参数：x : A i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem SetLike.isHomogeneousElem_coe {A : ι → S} {i} (x : A i) :
    SetLike.IsHomogeneousElem A (x : R) :=
  ⟨i, x.prop⟩
/-
**SetLike.isHomogeneousElem_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.isHomogeneousElem_one [Zero ι] [One R] (A : ι -> S) [SetLike.Grade
dOne A] : SetLike.IsHomogeneousElem A (1 : R)
参数：A : ι -> S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.one_mem_graded`：SetLike.one_mem_graded {S : Type*} [SetLike S R]
 [One R] [Zero ι] (A : ι -> S) [SetLike.GradedOne A] : (1 : R) in A 0
-/
theorem SetLike.isHomogeneousElem_one [Zero ι] [One R] (A : ι → S) [SetLike.GradedOne A] :
    SetLike.IsHomogeneousElem A (1 : R) :=
  ⟨0, SetLike.one_mem_graded _⟩
/-
**SetLike.IsHomogeneousElem.mul** 是 Mathlib 中的一个定理，位于命名空间 `SetLike.IsHomogeneous
Elem`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3} [inst : SetLike S R] [inst_
1 : Add ι] [inst_2 : Mul R] {A : ι → S}   [SetLike.GradedMul A] {a b : R},   Set
Like.IsHomogeneousElem A a → SetLike.IsHomogeneousElem A b → SetLike.IsHomogeneo
usElem A (a * b)
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.mul_mem_graded`：SetLike.mul_mem_graded {S : Type*} [SetLike S R]
 [Mul R] [Add ι] {A : ι -> S} [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi in A 
i) (hj : gj …
-/
theorem SetLike.IsHomogeneousElem.mul [Add ι] [Mul R] {A : ι → S} [SetLike.GradedMul A] {a b : R} :
    SetLike.IsHomogeneousElem A a → SetLike.IsHomogeneousElem A b →
    SetLike.IsHomogeneousElem A (a * b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i + j, SetLike.mul_mem_graded hi hj⟩

/-- When `A` is a `SetLike.GradedMonoid A`, then the homogeneous elements forms a submonoid. -/
/-
**SetLike.homogeneousSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SetLike.homogeneousSubmonoid [AddMonoid ι] [Monoid R] (A : ι -> S) [SetLik
e.GradedMonoid A] : Submonoid R where carrier
参数：A : ι -> S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `A` is a `SetLike.GradedMonoid A`, then the homogeneous elements forms a su
bmonoid.
-/
def SetLike.homogeneousSubmonoid [AddMonoid ι] [Monoid R] (A : ι → S) [SetLike.GradedMonoid A] :
    Submonoid R where
  carrier := { a | SetLike.IsHomogeneousElem A a }
  one_mem' := SetLike.isHomogeneousElem_one A
  mul_mem' a b := SetLike.IsHomogeneousElem.mul a b

end HomogeneousElements

section CommMonoid

namespace SetLike

variable {ι R S : Type*} [SetLike S R] [CommMonoid R] [AddCommMonoid ι]
variable (A : ι → S) [SetLike.GradedMonoid A]

variable {κ : Type*} (i : κ → ι) (g : κ → R) {F : Finset κ}

/-
**SetLike.prod_mem_graded** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：prod_mem_graded (hF : forall k in F, g k in A (i k)) : ∏ k in F, g k in A 
(∑ k in F, i k)
参数：hF : forall k in F, g k in A (i k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `SetLike.mul_mem_graded`：SetLike.mul_mem_graded {S : Type*} [SetLike S R]
 [Mul R] [Add ι] {A : ι -> S} [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi in A 
i) (hj : gj …
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
-/
theorem prod_mem_graded (hF : ∀ k ∈ F, g k ∈ A (i k)) : ∏ k ∈ F, g k ∈ A (∑ k ∈ F, i k) := by
  classical
  induction F using Finset.induction_on
  · simp [GradedOne.one_mem]
  · case insert j F' hF2 h3 =>
    rw [Finset.prod_insert hF2, Finset.sum_insert hF2]
    apply SetLike.mul_mem_graded (by grind)
    grind
/-
**SetLike.prod_pow_mem_graded** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：prod_pow_mem_graded (n : κ -> Nat) (hF : forall k in F, g k in A (i k)) : 
∏ k in F, g k ^ n k in A (∑ k in F, n k • i k)
参数：n : κ -> Nat；hF : forall k in F, g k in A (i k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.prod_mem_graded`：prod_mem_graded (hF : forall k in F, g k in A (
i k)) : ∏ k in F, g k in A (∑ k in F, i k)
· 使用定理 `SetLike.pow_mem_graded`：pow_mem_graded (n : Nat) {r : R} {i : ι} (h : r 
in A i) : r ^ n in A (n • i)
-/
theorem prod_pow_mem_graded (n : κ → ℕ) (hF : ∀ k ∈ F, g k ∈ A (i k)) :
    ∏ k ∈ F, g k ^ n k ∈ A (∑ k ∈ F, n k • i k) :=
  prod_mem_graded A _ _ fun k hk ↦ pow_mem_graded _ (hF k hk)

end SetLike

end CommMonoid

