/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Finset.MulAntidiagonal
public import Mathlib.Data.Finset.SMulAntidiagonal
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.HahnSeries.Addition

/-!
# Multiplicative properties of Hahn series

If `Γ` is ordered and `R` has zero, then `R⟦Γ⟧` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. This module introduces
multiplication and scalar multiplication on Hahn series. If `Γ` is an ordered cancellative
commutative additive monoid and `R` is a semiring, then we get a semiring structure on
`R⟦Γ⟧`. If `Γ` has an ordered vector-addition on `Γ'` and `R` has a scalar multiplication
on `V`, we define `HahnModule Γ' R V` as a type alias for `V⟦Γ'⟧` that admits a scalar
multiplication from `R⟦Γ⟧`. The scalar action of `R` on `R⟦Γ⟧` is compatible
with the action of `R⟦Γ⟧` on `HahnModule Γ' R V`.

## Main Definitions
* `HahnModule` is a type alias for `HahnSeries`, which we use for defining scalar multiplication
  of `R⟦Γ⟧` on `HahnModule Γ' R V` for an `R`-module `V`, where `Γ'` admits an ordered
  cancellative vector addition operation from `Γ`. The type alias allows us to avoid a potential
  instance diamond.
* `HahnModule.of` is the isomorphism from `V⟦Γ⟧` to `HahnModule Γ R V`.
* `HahnSeries.C` is the `constant term` ring homomorphism `R →+* R⟦Γ⟧`.
* `HahnSeries.embDomainRingHom` is the ring homomorphism `R⟦Γ⟧ →+* R⟦Γ'⟧`
  induced by an order embedding `Γ ↪o Γ'`.
* `HahnSeries.orderTopSubOnePos` is the group of invertible Hahn series close to 1, i.e., those
  series such that subtracting one yields a series with strictly positive `orderTop`.

## Main results
* If `R` is a (commutative) (semi-)ring, then so is `R⟦Γ⟧`.
* If `V` is an `R`-module, then `HahnModule Γ' R V` is a `R⟦Γ⟧`-module.

## TODO
The following may be useful for composing vertex operators, but they seem to take time.
* rightTensorMap: `HahnModule Γ' R U ⊗[R] V →ₗ[R] HahnModule Γ' R (U ⊗[R] V)`
* leftTensorMap: `U ⊗[R] HahnModule Γ' R V →ₗ[R] HahnModule Γ' R (U ⊗[R] V)`

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

@[expose] public section

open Finset Function HahnSeries Pointwise

noncomputable section

variable {Γ Γ' R S V : Type*}

namespace HahnSeries

variable [Zero Γ] [PartialOrder Γ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] [One R] : One R⟦Γ⟧ where one
  body: single 0 1

中文:
实例 [零
  签名: R] [幺 R] : 幺 R⟦Γ⟧ where one
  定义体: single 0 1

Depends on / 依赖: single
-/
instance [Zero R] [One R] : One R⟦Γ⟧ where one := single 0 1
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] [NatCast R] : NatCast R⟦Γ⟧ where natCast n
  body: single 0 n

中文:
实例 [零
  签名: R] [自然数嵌入 R] : 自然数嵌入 R⟦Γ⟧ where natCast n
  定义体: single 0 n

Depends on / 依赖: single
-/
instance [Zero R] [NatCast R] : NatCast R⟦Γ⟧ where natCast n := single 0 n
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] [IntCast R] : IntCast R⟦Γ⟧ where intCast z
  body: single 0 z

中文:
实例 [零
  签名: R] [整数嵌入 R] : 整数嵌入 R⟦Γ⟧ where intCast z
  定义体: single 0 z

Depends on / 依赖: single
-/
instance [Zero R] [IntCast R] : IntCast R⟦Γ⟧ where intCast z := single 0 z
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] [NNRatCast R] : NNRatCast R⟦Γ⟧ where nnratCast q
  body: single 0 q

中文:
实例 [零
  签名: R] [非负有理数嵌入 R] : 非负有理数嵌入 R⟦Γ⟧ where nnratCast q
  定义体: single 0 q

Depends on / 依赖: single
-/
instance [Zero R] [NNRatCast R] : NNRatCast R⟦Γ⟧ where nnratCast q := single 0 q
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] [RatCast R] : RatCast R⟦Γ⟧ where ratCast q
  body: single 0 q

中文:
实例 [零
  签名: R] [有理数嵌入 R] : 有理数嵌入 R⟦Γ⟧ where ratCast q
  定义体: single 0 q

Depends on / 依赖: single
-/
instance [Zero R] [RatCast R] : RatCast R⟦Γ⟧ where ratCast q := single 0 q

open scoped Classical in
@[simp]
/--
theorem `coeff_one` / 定理 `coeff_one`

English:
theorem coeff_one
  given: [Zero R] [One R] {a : Γ}
  statement: (1 : R⟦Γ⟧).coeff a = if a = 0 then 1 else 0
  proof: coeff_single

中文:
定理 coeff_one
  条件: [零 R] [幺 R] {a : Γ}
  结论: (1 : R⟦Γ⟧).coeff a = if a = 0 then 1 else 0
  证明: coeff_single

Depends on / 依赖: coeff_single
-/
theorem coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).coeff a = if a = 0 then 1 else 0 :=
  coeff_single

/--
theorem `single_zero_one` / 定理 `single_zero_one`

English:
theorem single_zero_one
  given: [Zero R] [One R]
  statement: single (0 : Γ) (1 : R) = 1
  proof: rfl

中文:
定理 single_zero_one
  条件: [零 R] [幺 R]
  结论: single (0 : Γ) (1 : R) = 1
  证明: rfl
-/
@[simp] theorem single_zero_one [Zero R] [One R] : single (0 : Γ) (1 : R) = 1 := rfl
/--
theorem `single_zero_natCast` / 定理 `single_zero_natCast`

English:
theorem single_zero_natCast
  given: [Zero R] [NatCast R] (n : Nat)
  statement: single (0 : Γ) (n : R) = n
  proof: rfl

中文:
定理 single_zero_natCast
  条件: [零 R] [自然数嵌入 R] (n : 自然数)
  结论: single (0 : Γ) (n : R) = n
  证明: rfl
-/
theorem single_zero_natCast [Zero R] [NatCast R] (n : Nat) : single (0 : Γ) (n : R) = n := rfl
/--
theorem `single_zero_intCast` / 定理 `single_zero_intCast`

English:
theorem single_zero_intCast
  given: [Zero R] [IntCast R] (z : Int)
  statement: single (0 : Γ) (z : R) = z
  proof: rfl

中文:
定理 single_zero_intCast
  条件: [零 R] [整数嵌入 R] (z : 整数)
  结论: single (0 : Γ) (z : R) = z
  证明: rfl
-/
theorem single_zero_intCast [Zero R] [IntCast R] (z : Int) : single (0 : Γ) (z : R) = z := rfl
/--
theorem `single_zero_nnratCast` / 定理 `single_zero_nnratCast`

English:
theorem single_zero_nnratCast
  given: [Zero R] [NNRatCast R] (q : Rat>=0)
  statement: single (0 : Γ) (q : R) = q
  proof: rfl

中文:
定理 single_zero_nnratCast
  条件: [零 R] [非负有理数嵌入 R] (q : 有理数>=0)
  结论: single (0 : Γ) (q : R) = q
  证明: rfl
-/
theorem single_zero_nnratCast [Zero R] [NNRatCast R] (q : Rat>=0) : single (0 : Γ) (q : R) = q := rfl
/--
theorem `single_zero_ratCast` / 定理 `single_zero_ratCast`

English:
theorem single_zero_ratCast
  given: [Zero R] [RatCast R] (q : Rat)
  statement: single (0 : Γ) (q : R) = q
  proof: rfl

中文:
定理 single_zero_ratCast
  条件: [零 R] [有理数嵌入 R] (q : 有理数)
  结论: single (0 : Γ) (q : R) = q
  证明: rfl
-/
theorem single_zero_ratCast [Zero R] [RatCast R] (q : Rat) : single (0 : Γ) (q : R) = q := rfl

/--
theorem `single_zero_ofNat` / 定理 `single_zero_ofNat`

English:
theorem single_zero_ofNat
  given: [Zero R] [NatCast R] (n : Nat) [n.AtLeastTwo]
  proof: rfl

@[simp]

中文:
定理 single_zero_of自然数
  条件: [零 R] [自然数嵌入 R] (n : 自然数) [n.AtLeastTwo]
  证明: rfl

@[simp]
-/
theorem single_zero_ofNat [Zero R] [NatCast R] (n : Nat) [n.AtLeastTwo] :
    single (0 : Γ) (ofNat(n) : R) = ofNat(n) := rfl

@[simp]
/--
theorem `support_one` / 定理 `support_one`

English:
theorem support_one
  given: [MulZeroOneClass R] [Nontrivial R]
  statement: support (1 : R⟦Γ⟧) = {0}
  proof: support_single_of_ne one_ne_zero

@[simp]

中文:
定理 support_one
  条件: [乘零幺类 R] [非平凡 R]
  结论: support (1 : R⟦Γ⟧) = {0}
  证明: support_single_of_ne one_ne_zero

@[simp]

Depends on / 依赖: one_ne_zero, support_single_of_ne
-/
theorem support_one [MulZeroOneClass R] [Nontrivial R] : support (1 : R⟦Γ⟧) = {0} :=
  support_single_of_ne one_ne_zero

@[simp]
/--
theorem `orderTop_one` / 定理 `orderTop_one`

English:
theorem orderTop_one
  given: [Zero R] [One R] [NeZero (1 : R)]
  statement: orderTop (1 : R⟦Γ⟧) = 0
  proof: by
  rw [← single_zero_one]; rw [orderTop_single one_ne_zero]; rw [WithTop.coe_eq_zero]

@[simp]

中文:
定理 orderTop_one
  条件: [零 R] [幺 R] [NeZero (1 : R)]
  结论: orderTop (1 : R⟦Γ⟧) = 0
  证明: by
  rw [← single_zero_one]; rw [orderTop_single one_ne_zero]; rw [WithTop.coe_eq_zero]

@[simp]

Depends on / 依赖: WithTop, WithTop.coe_eq_zero, coe_eq_zero, one_ne_zero, orderTop_single, single_zero_one
-/
theorem orderTop_one [Zero R] [One R] [NeZero (1 : R)] : orderTop (1 : R⟦Γ⟧) = 0 := by
  rw [← single_zero_one]; rw [orderTop_single one_ne_zero]; rw [WithTop.coe_eq_zero]

@[simp]
/--
theorem `order_one` / 定理 `order_one`

English:
theorem order_one
  given: [MulZeroOneClass R]
  statement: order (1 : R⟦Γ⟧) = 0
  proof: by
  cases subsingleton_or_nontrivial R
  · rw [Subsingleton.elim (1 : R⟦Γ⟧) 0, order_zero]
  · exact order_single one_ne_zero

@[simp]

中文:
定理 order_one
  条件: [乘零幺类 R]
  结论: order (1 : R⟦Γ⟧) = 0
  证明: by
  cases subsingleton_or_nontrivial R
  · rw [Subsingleton.elim (1 : R⟦Γ⟧) 0, order_zero]
  · exact order_single one_ne_zero

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim, one_ne_zero, order_single, order_zero, subsingleton_or_nontrivial
-/
theorem order_one [MulZeroOneClass R] : order (1 : R⟦Γ⟧) = 0 := by
  cases subsingleton_or_nontrivial R
  · rw [Subsingleton.elim (1 : R⟦Γ⟧) 0, order_zero]
  · exact order_single one_ne_zero

@[simp]
/--
theorem `leadingCoeff_one` / 定理 `leadingCoeff_one`

English:
theorem leadingCoeff_one
  given: [MulZeroOneClass R]
  statement: (1 : R⟦Γ⟧).leadingCoeff = 1
  proof: by
  simp [leadingCoeff_eq]

@[simp]

中文:
定理 leadingCoeff_one
  条件: [乘零幺类 R]
  结论: (1 : R⟦Γ⟧).leadingCoeff = 1
  证明: by
  simp [leadingCoeff_eq]

@[simp]

Depends on / 依赖: leadingCoeff_eq
-/
theorem leadingCoeff_one [MulZeroOneClass R] : (1 : R⟦Γ⟧).leadingCoeff = 1 := by
  simp [leadingCoeff_eq]

@[simp]
/--
lemma `map_one` / 引理 `map_one`

English:
lemma map_one
  given: [MonoidWithZero R] [MonoidWithZero S] (f : R ->*₀ S)
  proof: .trans congrArg _ f.map_one HahnSeries.map_single (a := (0 : Γ)) f.toZeroHom

中文:
引理 map_one
  条件: [带零幺半群 R] [带零幺半群 S] (f : R ->*₀ S)
  证明: .trans congrArg _ f.map_one HahnSeries.map_single (a := (0 : Γ)) f.toZeroHom
-/
protected lemma map_one [MonoidWithZero R] [MonoidWithZero S] (f : R ->*₀ S) :
    (1 : R⟦Γ⟧).map f = (1 : S⟦Γ⟧) :=
.trans congrArg _ f.map_one HahnSeries.map_single (a := (0 : Γ)) f.toZeroHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoidWithOne
  signature: R] : AddCommMonoidWithOne R⟦Γ⟧ where
  body: by simp [← single_zero_natCast]
  natCast_succ n := by simp [← single_zero_natCast]

中文:
实例 [加法交换带幺幺半群
  签名: R] : 加法交换带幺幺半群 R⟦Γ⟧ where
  定义体: by simp [← single_zero_natCast]
  natCast_succ n := by simp [← single_zero_natCast]

Depends on / 依赖: natCast_succ, single_zero_natCast
-/
instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne R⟦Γ⟧ where
  natCast_zero := by simp [← single_zero_natCast]
  natCast_succ n := by simp [← single_zero_natCast]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroupWithOne
  signature: R] : AddCommGroupWithOne R⟦Γ⟧ where
  body: by simp [← single_zero_natCast, ← single_zero_intCast]
  intCast_negSucc n := by simp [← single_zero_natCast, ← single_zero_intCast]

中文:
实例 [加法交换带幺群
  签名: R] : 加法交换带幺群 R⟦Γ⟧ where
  定义体: by simp [← single_zero_natCast, ← single_zero_intCast]
  intCast_negSucc n := by simp [← single_zero_natCast, ← single_zero_intCast]

Depends on / 依赖: intCast_negSucc, single_zero_intCast, single_zero_natCast
-/
instance [AddCommGroupWithOne R] : AddCommGroupWithOne R⟦Γ⟧ where
  intCast_ofNat n := by simp [← single_zero_natCast, ← single_zero_intCast]
  intCast_negSucc n := by simp [← single_zero_natCast, ← single_zero_intCast]

end HahnSeries

/-- We introduce a type alias for `HahnSeries` in order to work with scalar multiplication by
series. If we wrote a `SMul R⟦Γ⟧ V⟦Γ⟧` instance, then when
`V = R⟦Γ⟧`, we would have two different actions of `R⟦Γ⟧` on `V⟦Γ⟧`.
See `Mathlib/Algebra/Polynomial/Module/Basic.lean` for more discussion on this problem. -/
@[nolint unusedArguments]
/--
Definition of `HahnModule` / `HahnModule` 的定义

English:
definition HahnModule
  signature: (Γ R V : Type*) [PartialOrder Γ] [Zero V] [SMul R V]
  body: V⟦Γ⟧

中文:
定义 HahnModule
  签名: (Γ R V : 类型) [偏序 Γ] [零 V] [标量乘法 R V]
  定义体: V⟦Γ⟧

Depends on / 依赖: e.symm
-/
def HahnModule (Γ R V : Type*) [PartialOrder Γ] [Zero V] [SMul R V] :=
  V⟦Γ⟧

namespace HahnModule

section

variable [PartialOrder Γ] [Zero V] [SMul R V]

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (R : Type*) [SMul R V]
  body: Equiv.refl _

中文:
定义 of
  签名: (R : 类型) [标量乘法 R V]
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def of (R : Type*) [SMul R V] : V⟦Γ⟧ ≃ HahnModule Γ R V :=
  Equiv.refl _

/-- Recursion principle to reduce a result about the synonym to the original type. -/
@[elab_as_elim]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {motive : HahnModule Γ R V -> Sort*} (h : forall x : V⟦Γ⟧, motive (of R x))
  body: fun x => h (of R).symm x

@[ext]

中文:
定义 rec
  签名: {motive : HahnModule Γ R V -> 类型层*} (h : 对任意 x : V⟦Γ⟧, motive (of R x))
  定义体: fun x => h (of R).symm x

@[ext]
-/
def rec {motive : HahnModule Γ R V -> Sort*} (h : forall x : V⟦Γ⟧, motive (of R x)) :
    forall x, motive x :=
fun x => h (of R).symm x

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (x y : HahnModule Γ R V) (h : ((of R).symm x).coeff = ((of R).symm y).coeff)
  statement: x = y
  proof: (of R).symm.injective HahnSeries.coeff_inj.1 h

中文:
定理 ext
  条件: (x y : HahnModule Γ R V) (h : ((of R).symm x).coeff = ((of R).symm y).coeff)
  结论: x = y
  证明: (of R).symm.injective HahnSeries.coeff_inj.1 h

Depends on / 依赖: HahnSeries, HahnSeries.coeff_inj, coeff_inj, injective, symm.injective
-/
theorem ext (x y : HahnModule Γ R V) (h : ((of R).symm x).coeff = ((of R).symm y).coeff) : x = y :=
(of R).symm.injective HahnSeries.coeff_inj.1 h

end

section SMul

variable [PartialOrder Γ] [SMul R V]

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: [Zero V]
  body: inferInstanceAs Zero V⟦Γ⟧

中文:
实例 instZero
  签名: [零 V]
  定义体: inferInstanceAs Zero V⟦Γ⟧

Depends on / 依赖: e.symm
-/
instance instZero [Zero V] : Zero (HahnModule Γ R V) :=
inferInstanceAs Zero V⟦Γ⟧
/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: [AddCommMonoid V]
  body: inferInstanceAs AddCommMonoid V⟦Γ⟧

中文:
实例 instAddCommMonoid
  签名: [加法交换幺半群 V]
  定义体: inferInstanceAs AddCommMonoid V⟦Γ⟧

Depends on / 依赖: AddCommMonoid
-/
instance instAddCommMonoid [AddCommMonoid V] : AddCommMonoid (HahnModule Γ R V) :=
inferInstanceAs AddCommMonoid V⟦Γ⟧
/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: [AddCommGroup V]
  body: inferInstanceAs AddCommGroup V⟦Γ⟧

中文:
实例 instAddCommGroup
  签名: [加法交换群 V]
  定义体: inferInstanceAs AddCommGroup V⟦Γ⟧

Depends on / 依赖: AddCommGroup
-/
instance instAddCommGroup [AddCommGroup V] : AddCommGroup (HahnModule Γ R V) :=
inferInstanceAs AddCommGroup V⟦Γ⟧
/--
Instance `instBaseSMul` / 实例 `instBaseSMul`

English:
instance instBaseSMul
  signature: {V} [Monoid R] [AddMonoid V] [DistribMulAction R V]
  body: inferInstanceAs SMul R V⟦Γ⟧

中文:
实例 instBaseSMul
  签名: {V} [幺半群 R] [加法幺半群 V] [分配乘法作用 R V]
  定义体: inferInstanceAs SMul R V⟦Γ⟧
-/
instance instBaseSMul {V} [Monoid R] [AddMonoid V] [DistribMulAction R V] :
    SMul R (HahnModule Γ R V) :=
inferInstanceAs SMul R V⟦Γ⟧

/--
theorem `of_zero` / 定理 `of_zero`

English:
theorem of_zero
  given: [Zero V]
  statement: of R (0 : V⟦Γ⟧) = 0
  proof: rfl

中文:
定理 of_zero
  条件: [零 V]
  结论: of R (0 : V⟦Γ⟧) = 0
  证明: rfl
-/
@[simp] theorem of_zero [Zero V] : of R (0 : V⟦Γ⟧) = 0 := rfl
/--
theorem `of_add` / 定理 `of_add`

English:
theorem of_add
  given: [AddCommMonoid V] (x y : V⟦Γ⟧)
  proof: rfl

中文:
定理 of_add
  条件: [加法交换幺半群 V] (x y : V⟦Γ⟧)
  证明: rfl
-/
@[simp] theorem of_add [AddCommMonoid V] (x y : V⟦Γ⟧) :
    of R (x + y) = of R x + of R y := rfl
/--
theorem `of_sub` / 定理 `of_sub`

English:
theorem of_sub
  given: [AddCommGroup V] (x y : V⟦Γ⟧)
  proof: rfl

中文:
定理 of_sub
  条件: [加法交换群 V] (x y : V⟦Γ⟧)
  证明: rfl
-/
@[simp] theorem of_sub [AddCommGroup V] (x y : V⟦Γ⟧) :
    of R (x - y) = of R x - of R y := rfl

/--
theorem `of_symm_zero` / 定理 `of_symm_zero`

English:
theorem of_symm_zero
  given: [Zero V]
  statement: (of R).symm (0 : HahnModule Γ R V) = 0
  proof: rfl

中文:
定理 of_symm_zero
  条件: [零 V]
  结论: (of R).symm (0 : HahnModule Γ R V) = 0
  证明: rfl
-/
@[simp] theorem of_symm_zero [Zero V] : (of R).symm (0 : HahnModule Γ R V) = 0 := rfl
/--
theorem `of_symm_add` / 定理 `of_symm_add`

English:
theorem of_symm_add
  given: [AddCommMonoid V] (x y : HahnModule Γ R V)
  proof: rfl

中文:
定理 of_symm_add
  条件: [加法交换幺半群 V] (x y : HahnModule Γ R V)
  证明: rfl
-/
@[simp] theorem of_symm_add [AddCommMonoid V] (x y : HahnModule Γ R V) :
    (of R).symm (x + y) = (of R).symm x + (of R).symm y := rfl
/--
theorem `of_symm_sub` / 定理 `of_symm_sub`

English:
theorem of_symm_sub
  given: [AddCommGroup V] (x y : HahnModule Γ R V)
  proof: rfl

中文:
定理 of_symm_sub
  条件: [加法交换群 V] (x y : HahnModule Γ R V)
  证明: rfl
-/
@[simp] theorem of_symm_sub [AddCommGroup V] (x y : HahnModule Γ R V) :
    (of R).symm (x - y) = (of R).symm x - (of R).symm y := rfl

variable [PartialOrder Γ'] [VAdd Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [Zero R] [AddCommMonoid V]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul R⟦Γ⟧ (HahnModule Γ' R V) where
  body: (of R) {
    coeff := fun a =>
      ∑ ij in VAddAntidiagonal a
        (Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support ((of R).symm y).isPWO_support a),
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd
    isPWO_support' :=
        have h : { a : Γ' | (∑ ij in VAddAntidiagonal a
        

中文:
实例 instSMul
  签名: : 标量乘法 R⟦Γ⟧ (HahnModule Γ' R V) where
  定义体: (of R) {
    coeff := fun a =>
      ∑ ij in VAddAntidiagonal a
        (Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support ((of R).symm y).isPWO_support a),
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd
    isPWO_support' :=
        have h : { a : Γ' | (∑ ij in VAddAntidiagonal a
        
-/
instance instSMul : SMul R⟦Γ⟧ (HahnModule Γ' R V) where
  smul x y := (of R) {
    coeff := fun a =>
      ∑ ij in VAddAntidiagonal a
        (Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support ((of R).symm y).isPWO_support a),
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd
    isPWO_support' :=
        have h : { a : Γ' | (∑ ij in VAddAntidiagonal a
            (Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support ((of R).symm y).isPWO_support a),
              x.coeff ij.fst • ((of R).symm y).coeff ij.snd) != 0 } subseteq
            { a : Γ' | (VAddAntidiagonal a (Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support
              ((of R).symm y).isPWO_support a)).Nonempty } := by
          intro a ha
          simp only [Set.mem_ofPred_eq]
          contrapose! ha
          simp [ha]
        (isPWO_support_vaddAntidiagonal x.isPWO_support ((of R).symm y).isPWO_support).mono h }

/--
theorem `coeff_smul` / 定理 `coeff_smul`

English:
theorem coeff_smul
  given: (x : R⟦Γ⟧) (y : HahnModule Γ' R V) (a : Γ')
  proof: rfl

中文:
定理 coeff_smul
  条件: (x : R⟦Γ⟧) (y : HahnModule Γ' R V) (a : Γ')
  证明: rfl
-/
theorem coeff_smul (x : R⟦Γ⟧) (y : HahnModule Γ' R V) (a : Γ') :
    ((of R).symm <| x • y).coeff a =
      ∑ ij in VAddAntidiagonal a
        (Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support ((of R).symm y).isPWO_support a),
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd :=
  rfl

end SMul

section SMulZeroClass

variable [PartialOrder Γ] [PartialOrder Γ'] [VAdd Γ Γ'] [IsOrderedCancelVAdd Γ Γ']
  [AddCommMonoid V]

/--
Instance `instBaseSMulZeroClass` / 实例 `instBaseSMulZeroClass`

English:
instance instBaseSMulZeroClass
  signature: [SMulZeroClass R V]
  body: inferInstanceAs SMulZeroClass R V⟦Γ⟧

中文:
实例 instBaseSMulZeroClass
  签名: [SMulZero类 R V]
  定义体: inferInstanceAs SMulZeroClass R V⟦Γ⟧

Depends on / 依赖: SMulZeroClass
-/
instance instBaseSMulZeroClass [SMulZeroClass R V] :
    SMulZeroClass R (HahnModule Γ R V) :=
inferInstanceAs SMulZeroClass R V⟦Γ⟧

/--
theorem `of_smul` / 定理 `of_smul`

English:
theorem of_smul
  given: [SMulZeroClass R V] (r : R) (x : V⟦Γ⟧)
  proof: rfl

中文:
定理 of_smul
  条件: [SMulZero类 R V] (r : R) (x : V⟦Γ⟧)
  证明: rfl
-/
@[simp] theorem of_smul [SMulZeroClass R V] (r : R) (x : V⟦Γ⟧) :
    (of R) (r • x) = r • (of R) x := rfl
/--
theorem `of_symm_smul` / 定理 `of_symm_smul`

English:
theorem of_symm_smul
  given: [SMulZeroClass R V] (r : R) (x : HahnModule Γ R V)
  proof: rfl

中文:
定理 of_symm_smul
  条件: [SMulZero类 R V] (r : R) (x : HahnModule Γ R V)
  证明: rfl
-/
@[simp] theorem of_symm_smul [SMulZeroClass R V] (r : R) (x : HahnModule Γ R V) :
    (of R).symm (r • x) = r • (of R).symm x := rfl

variable [Zero R]

/--
Instance `instSMulZeroClass` / 实例 `instSMulZeroClass`

English:
instance instSMulZeroClass
  signature: [SMulZeroClass R V]
  body: by
    ext
    simp [coeff_smul]

中文:
实例 instSMulZeroClass
  签名: [SMulZero类 R V]
  定义体: by
    ext
    simp [coeff_smul]

Depends on / 依赖: coeff_smul
-/
instance instSMulZeroClass [SMulZeroClass R V] :
    SMulZeroClass R⟦Γ⟧ (HahnModule Γ' R V) where
  smul_zero x := by
    ext
    simp [coeff_smul]

/--
theorem `coeff_smul_right` / 定理 `coeff_smul_right`

English:
theorem coeff_smul_right
  statement: [SMulZeroClass R V] {x : R⟦Γ⟧} {y : HahnModule Γ' R V} {a : Γ'}
  proof: by
  classical
  rw [coeff_smul]
  apply sum_subset_zero_on_sdiff (vaddAntidiagonal_mono_right _ _ _ hys) _ fun _ _ => rfl
  intro b hb
  simp only [not_and, mem_sdiff, mem_vaddAntidiagonal, HahnSeries.mem_support, not_imp_not] at hb
  rw [hb.2 hb.1.1 hb.1.2.2]; rw [smul_zero]

中文:
定理 coeff_smul_right
  结论: [SMulZero类 R V] {x : R⟦Γ⟧} {y : HahnModule Γ' R V} {a : Γ'}
  证明: by
  classical
  rw [coeff_smul]
  apply sum_subset_zero_on_sdiff (vaddAntidiagonal_mono_right _ _ _ hys) _ fun _ _ => rfl
  intro b hb
  simp only [not_and, mem_sdiff, mem_vaddAntidiagonal, HahnSeries.mem_support, not_imp_not] at hb
  rw [hb.2 hb.1.1 hb.1.2.2]; rw [smul_zero]

Depends on / 依赖: HahnSeries, HahnSeries.mem_support, classical, coeff_smul, mem_sdiff, mem_support, mem_vaddAntidiagonal, not_and, not_imp_not, smul_zero, sum_subset_zero_on_sdiff, vaddAntidiagonal_mono_right
-/
theorem coeff_smul_right [SMulZeroClass R V] {x : R⟦Γ⟧} {y : HahnModule Γ' R V} {a : Γ'}
    {s : Set Γ'} (hs : s.IsPWO) (hys : ((of R).symm y).support subseteq s) :
    ((of R).symm <| x • y).coeff a =
      ∑ ij in VAddAntidiagonal a (Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support hs a),
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd := by
  classical
  rw [coeff_smul]
  apply sum_subset_zero_on_sdiff (vaddAntidiagonal_mono_right _ _ _ hys) _ fun _ _ => rfl
  intro b hb
  simp only [not_and, mem_sdiff, mem_vaddAntidiagonal, HahnSeries.mem_support, not_imp_not] at hb
  rw [hb.2 hb.1.1 hb.1.2.2]; rw [smul_zero]

/--
theorem `coeff_smul_left` / 定理 `coeff_smul_left`

English:
theorem coeff_smul_left
  statement: [SMulWithZero R V] {x : R⟦Γ⟧}
  proof: by
  classical
  rw [coeff_smul]
  apply sum_subset_zero_on_sdiff (vaddAntidiagonal_mono_left _ hxs _ _) _ fun _ _ => rfl
  intro b hb
  simp only [not_and', mem_sdiff, mem_vaddAntidiagonal, HahnSeries.mem_support, not_ne_iff] at hb
  rw [hb.2 ⟨hb.1.2.1]; rw [hb.1.2.2⟩]; rw [zero_smul]

中文:
定理 coeff_smul_left
  结论: [带零标量乘法 R V] {x : R⟦Γ⟧}
  证明: by
  classical
  rw [coeff_smul]
  apply sum_subset_zero_on_sdiff (vaddAntidiagonal_mono_left _ hxs _ _) _ fun _ _ => rfl
  intro b hb
  simp only [not_and', mem_sdiff, mem_vaddAntidiagonal, HahnSeries.mem_support, not_ne_iff] at hb
  rw [hb.2 ⟨hb.1.2.1]; rw [hb.1.2.2⟩]; rw [zero_smul]

Depends on / 依赖: HahnSeries, HahnSeries.mem_support, classical, coeff_smul, mem_sdiff, mem_support, mem_vaddAntidiagonal, not_and, not_ne_iff, sum_subset_zero_on_sdiff, vaddAntidiagonal_mono_left, zero_smul
-/
theorem coeff_smul_left [SMulWithZero R V] {x : R⟦Γ⟧}
    {y : HahnModule Γ' R V} {a : Γ'} {s : Set Γ}
    (hs : s.IsPWO) (hxs : x.support subseteq s) :
    ((of R).symm <| x • y).coeff a =
      ∑ ij in VAddAntidiagonal a
      (Set.VAddAntidiagonal.finite_of_isPWO hs ((of R).symm y).isPWO_support a),
      x.coeff ij.fst • ((of R).symm y).coeff ij.snd := by
  classical
  rw [coeff_smul]
  apply sum_subset_zero_on_sdiff (vaddAntidiagonal_mono_left _ hxs _ _) _ fun _ _ => rfl
  intro b hb
  simp only [not_and', mem_sdiff, mem_vaddAntidiagonal, HahnSeries.mem_support, not_ne_iff] at hb
  rw [hb.2 ⟨hb.1.2.1]; rw [hb.1.2.2⟩]; rw [zero_smul]

end SMulZeroClass

section DistribSMul

variable [PartialOrder Γ] [PartialOrder Γ'] [VAdd Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [AddCommMonoid V]

/--
theorem `smul_add` / 定理 `smul_add`

English:
theorem smul_add
  given: [Zero R] [DistribSMul R V] (x : R⟦Γ⟧) (y z : HahnModule Γ' R V)
  proof: by
  ext k
  have hwf := ((of R).symm y).isPWO_support.union ((of R).symm z).isPWO_support
  rw [coeff_smul_right hwf]; rw [of_symm_add]
  · simp_all only [HahnSeries.coeff_add', Pi.add_apply, of_symm_add]
    rw [coeff_smul_right hwf Set.subset_union_right]; rw [coeff_smul_right hwf Set.subset_unio

中文:
定理 smul_add
  条件: [零 R] [分配标量乘法 R V] (x : R⟦Γ⟧) (y z : HahnModule Γ' R V)
  证明: by
  ext k
  have hwf := ((of R).symm y).isPWO_support.union ((of R).symm z).isPWO_support
  rw [coeff_smul_right hwf]; rw [of_symm_add]
  · simp_all only [HahnSeries.coeff_add', Pi.add_apply, of_symm_add]
    rw [coeff_smul_right hwf Set.subset_union_right]; rw [coeff_smul_right hwf Set.subset_unio

Depends on / 依赖: HahnSeries, HahnSeries.coeff_add, HahnSeries.isPWO_support, HahnSeries.mem_support, Pi.add_apply, Set.isPWO_union, Set.mem_union, Set.subset_union_left, Set.subset_union_right, add_apply, and_self, coeff_add, coeff_smul_right, isPWO_support, isPWO_support.union, isPWO_union, mem_support, mem_union, ne_eq, of_symm_add
-/
theorem smul_add [Zero R] [DistribSMul R V] (x : R⟦Γ⟧) (y z : HahnModule Γ' R V) :
    x • (y + z) = x • y + x • z := by
  ext k
  have hwf := ((of R).symm y).isPWO_support.union ((of R).symm z).isPWO_support
  rw [coeff_smul_right hwf]; rw [of_symm_add]
  · simp_all only [HahnSeries.coeff_add', Pi.add_apply, of_symm_add]
    rw [coeff_smul_right hwf Set.subset_union_right]; rw [coeff_smul_right hwf Set.subset_union_left]
    simp_all [sum_add_distrib]
  · intro b
    simp_all only [Set.isPWO_union, HahnSeries.isPWO_support, and_self, of_symm_add,
      HahnSeries.coeff_add', Pi.add_apply, ne_eq, Set.mem_union, HahnSeries.mem_support]
    contrapose!
    intro h
    rw [h.1]; rw [h.2]; rw [add_zero]

/--
Instance `instDistribSMul` / 实例 `instDistribSMul`

English:
instance instDistribSMul
  signature: [MonoidWithZero R] [DistribSMul R V]
  body: smul_add

中文:
实例 instDistribSMul
  签名: [带零幺半群 R] [分配标量乘法 R V]
  定义体: smul_add

Depends on / 依赖: notation_class, ppSpace, smul_add
-/
instance instDistribSMul [MonoidWithZero R] [DistribSMul R V] : DistribSMul R⟦Γ⟧
    (HahnModule Γ' R V) where
  smul_add := smul_add

/--
theorem `add_smul` / 定理 `add_smul`

English:
theorem add_smul
  statement: [AddCommMonoid R] [SMulWithZero R V] {x y : R⟦Γ⟧}
  proof: by
  ext a
  have hwf := x.isPWO_support.union y.isPWO_support
  rw [coeff_smul_left hwf]; rw [HahnSeries.coeff_add']; rw [of_symm_add]
  · simp_all only [Pi.add_apply, HahnSeries.coeff_add']
    rw [coeff_smul_left hwf Set.subset_union_right]; rw [coeff_smul_left hwf Set.subset_union_left]
    simp

中文:
定理 add_smul
  结论: [加法交换幺半群 R] [带零标量乘法 R V] {x y : R⟦Γ⟧}
  证明: by
  ext a
  have hwf := x.isPWO_support.union y.isPWO_support
  rw [coeff_smul_left hwf]; rw [HahnSeries.coeff_add']; rw [of_symm_add]
  · simp_all only [Pi.add_apply, HahnSeries.coeff_add']
    rw [coeff_smul_left hwf Set.subset_union_right]; rw [coeff_smul_left hwf Set.subset_union_left]
    simp

Depends on / 依赖: HahnSeries, HahnSeries.coeff_add, Pi.add_apply, Set.subset_union_left, Set.subset_union_right, add_apply, coeff_add, coeff_smul_left, isPWO_support, of_symm_add, subset_union_left, subset_union_right, sum_add_distrib, support_add_subset, x.isPWO_support.union, y.isPWO_support
-/
theorem add_smul [AddCommMonoid R] [SMulWithZero R V] {x y : R⟦Γ⟧}
    {z : HahnModule Γ' R V} (h : forall (r s : R) (u : V), (r + s) • u = r • u + s • u) :
    (x + y) • z = x • z + y • z := by
  ext a
  have hwf := x.isPWO_support.union y.isPWO_support
  rw [coeff_smul_left hwf]; rw [HahnSeries.coeff_add']; rw [of_symm_add]
  · simp_all only [Pi.add_apply, HahnSeries.coeff_add']
    rw [coeff_smul_left hwf Set.subset_union_right]; rw [coeff_smul_left hwf Set.subset_union_left]
    simp only [sum_add_distrib]
  · exact support_add_subset _ _

/--
theorem `coeff_single_smul_vadd` / 定理 `coeff_single_smul_vadd`

English:
theorem coeff_single_smul_vadd
  statement: [MulZeroClass R] [SMulWithZero R V] {r : R} {x : HahnModule Γ' R V}
  proof: by
  by_cases hr : r = 0
  · simp_all only [map_zero, zero_smul, coeff_smul, HahnSeries.support_zero, HahnSeries.coeff_zero,
    sum_const_zero]
  simp only [hr, coeff_smul, coeff_smul, HahnSeries.support_single_of_ne, ne_eq, not_false_iff]
  by_cases hx : ((of R).symm x).coeff a = 0
  · simp only [

中文:
定理 coeff_single_smul_vadd
  结论: [乘零类 R] [带零标量乘法 R V] {r : R} {x : HahnModule Γ' R V}
  证明: by
  by_cases hr : r = 0
  · simp_all only [map_zero, zero_smul, coeff_smul, HahnSeries.support_zero, HahnSeries.coeff_zero,
    sum_const_zero]
  simp only [hr, coeff_smul, coeff_smul, HahnSeries.support_single_of_ne, ne_eq, not_false_iff]
  by_cases hx : ((of R).symm x).coeff a = 0
  · simp only [

Depends on / 依赖: HahnSeries, HahnSeries.coeff_zero, HahnSeries.support_single_of_ne, HahnSeries.support_zero, IsCancelVAdd, IsCancelVAdd.left_cancel, Set.mem_singleton_iff, coeff_smul, coeff_zero, iff_false, left_cancel, map_zero, mem_singleton_iff, mem_vaddAntidiagonal, ne_eq, notMem_empty, not_and, not_false_iff, smul_zero, sum_congr
-/
theorem coeff_single_smul_vadd [MulZeroClass R] [SMulWithZero R V] {r : R} {x : HahnModule Γ' R V}
    {a : Γ'} {b : Γ} :
    ((of R).symm (HahnSeries.single b r • x)).coeff (b +ᵥ a) = r • ((of R).symm x).coeff a := by
  by_cases hr : r = 0
  · simp_all only [map_zero, zero_smul, coeff_smul, HahnSeries.support_zero, HahnSeries.coeff_zero,
    sum_const_zero]
  simp only [hr, coeff_smul, coeff_smul, HahnSeries.support_single_of_ne, ne_eq, not_false_iff]
  by_cases hx : ((of R).symm x).coeff a = 0
  · simp only [hx, smul_zero]
    rw [sum_congr _ fun _ _ => rfl]; rw [sum_empty]
    ext ⟨a1, a2⟩
    simp only [notMem_empty, not_and, Set.mem_singleton_iff,
      mem_vaddAntidiagonal, iff_false]
    rintro rfl h2 h1
    rw [IsCancelVAdd.left_cancel a1 a2 a h1] at h2
    exact h2 hx
  trans ∑ ij in {(b, a)},
    (HahnSeries.single b r).coeff ij.fst • ((of R).symm x).coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp only [Set.mem_singleton_iff, Prod.mk_inj, mem_vaddAntidiagonal, mem_singleton]
    constructor
    · rintro ⟨rfl, _, h1⟩
      exact ⟨rfl, IsCancelVAdd.left_cancel a1 a2 a h1⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, by exact hx, rfl⟩
  · simp

/--
theorem `coeff_single_zero_smul` / 定理 `coeff_single_zero_smul`

English:
theorem coeff_single_zero_smul
  statement: {Γ} [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ']
  proof: by
  nth_rw 1 [← zero_vadd Γ a]
  exact coeff_single_smul_vadd

@[simp]

中文:
定理 coeff_single_zero_smul
  结论: {Γ} [加法交换幺半群 Γ] [偏序 Γ] [加法作用 Γ Γ']
  证明: by
  nth_rw 1 [← zero_vadd Γ a]
  exact coeff_single_smul_vadd

@[simp]

Depends on / 依赖: coeff_single_smul_vadd, nth_rw, zero_vadd
-/
theorem coeff_single_zero_smul {Γ} [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ']
    [IsOrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {r : R}
    {x : HahnModule Γ' R V} {a : Γ'} :
    ((of R).symm ((HahnSeries.single 0 r : R⟦Γ⟧) • x)).coeff a =
    r • ((of R).symm x).coeff a := by
  nth_rw 1 [← zero_vadd Γ a]
  exact coeff_single_smul_vadd

@[simp]
/--
theorem `single_zero_smul_eq_smul` / 定理 `single_zero_smul_eq_smul`

English:
theorem single_zero_smul_eq_smul
  statement: (Γ) [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ']
  proof: by
  ext
  exact coeff_single_zero_smul

@[simp]

中文:
定理 single_zero_smul_eq_smul
  结论: (Γ) [加法交换幺半群 Γ] [偏序 Γ] [加法作用 Γ Γ']
  证明: by
  ext
  exact coeff_single_zero_smul

@[simp]

Depends on / 依赖: coeff_single_zero_smul
-/
theorem single_zero_smul_eq_smul (Γ) [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ']
    [IsOrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {r : R}
    {x : HahnModule Γ' R V} :
    (HahnSeries.single (0 : Γ) r) • x = r • x := by
  ext
  exact coeff_single_zero_smul

@[simp]
/--
theorem `zero_smul'` / 定理 `zero_smul'`

English:
theorem zero_smul'
  given: [Zero R] [SMulWithZero R V] {x : HahnModule Γ' R V}
  statement: (0 : R⟦Γ⟧) • x = 0
  proof: by
  ext
  simp [coeff_smul]

@[simp]

中文:
定理 zero_smul'
  条件: [零 R] [带零标量乘法 R V] {x : HahnModule Γ' R V}
  结论: (0 : R⟦Γ⟧) • x = 0
  证明: by
  ext
  simp [coeff_smul]

@[simp]

Depends on / 依赖: coeff_smul
-/
theorem zero_smul' [Zero R] [SMulWithZero R V] {x : HahnModule Γ' R V} : (0 : R⟦Γ⟧) • x = 0 := by
  ext
  simp [coeff_smul]

@[simp]
/--
theorem `one_smul'` / 定理 `one_smul'`

English:
theorem one_smul'
  statement: {Γ} [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ'] [IsOrderedCancelVAdd Γ Γ']
  proof: by
  ext g
  exact coeff_single_zero_smul.trans (one_smul R (x.coeff g))

中文:
定理 one_smul'
  结论: {Γ} [加法交换幺半群 Γ] [偏序 Γ] [加法作用 Γ Γ'] [是OrderedCancelVAdd Γ Γ']
  证明: by
  ext g
  exact coeff_single_zero_smul.trans (one_smul R (x.coeff g))

Depends on / 依赖: coeff_single_zero_smul, coeff_single_zero_smul.trans, one_smul, x.coeff
-/
theorem one_smul' {Γ} [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ'] [IsOrderedCancelVAdd Γ Γ']
    [MonoidWithZero R] [MulActionWithZero R V] {x : HahnModule Γ' R V} : (1 : R⟦Γ⟧) • x = x := by
  ext g
  exact coeff_single_zero_smul.trans (one_smul R (x.coeff g))

/--
theorem `support_smul_subset_vadd_support'` / 定理 `support_smul_subset_vadd_support'`

English:
theorem support_smul_subset_vadd_support'
  statement: [MulZeroClass R] [SMulWithZero R V] {x : R⟦Γ⟧}
  proof: by
  refine Set.Subset.trans (fun x hx => ?_) (support_vaddAntidiagonal_subset_vadd
    fun a => Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support ((of R).symm y).isPWO_support a)
  simp only [Set.mem_ofPred_eq]
  contrapose! hx
  simp [coeff_smul, hx]

中文:
定理 support_smul_subset_vadd_support'
  结论: [乘零类 R] [带零标量乘法 R V] {x : R⟦Γ⟧}
  证明: by
  refine Set.Subset.trans (fun x hx => ?_) (support_vaddAntidiagonal_subset_vadd
    fun a => Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support ((of R).symm y).isPWO_support a)
  simp only [Set.mem_ofPred_eq]
  contrapose! hx
  simp [coeff_smul, hx]

Depends on / 依赖: Set.Subset.trans, Set.VAddAntidiagonal.finite_of_isPWO, Set.mem_ofPred_eq, Subset, VAddAntidiagonal, coeff_smul, contrapose, finite_of_isPWO, isPWO_support, mem_ofPred_eq, support_vaddAntidiagonal_subset_vadd, x.isPWO_support
-/
theorem support_smul_subset_vadd_support' [MulZeroClass R] [SMulWithZero R V] {x : R⟦Γ⟧}
    {y : HahnModule Γ' R V} :
    ((of R).symm (x • y)).support subseteq x.support +ᵥ ((of R).symm y).support := by
  refine Set.Subset.trans (fun x hx => ?_) (support_vaddAntidiagonal_subset_vadd
    fun a => Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support ((of R).symm y).isPWO_support a)
  simp only [Set.mem_ofPred_eq]
  contrapose! hx
  simp [coeff_smul, hx]

/--
theorem `support_smul_subset_vadd_support` / 定理 `support_smul_subset_vadd_support`

English:
theorem support_smul_subset_vadd_support
  statement: [MulZeroClass R] [SMulWithZero R V] {x : R⟦Γ⟧}
  proof: by
  exact support_smul_subset_vadd_support'

中文:
定理 support_smul_subset_vadd_support
  结论: [乘零类 R] [带零标量乘法 R V] {x : R⟦Γ⟧}
  证明: by
  exact support_smul_subset_vadd_support'

Depends on / 依赖: support_smul_subset_vadd_support
-/
theorem support_smul_subset_vadd_support [MulZeroClass R] [SMulWithZero R V] {x : R⟦Γ⟧}
    {y : HahnModule Γ' R V} :
    ((of R).symm (x • y)).support subseteq x.support +ᵥ ((of R).symm y).support := by
  exact support_smul_subset_vadd_support'

/--
theorem `orderTop_vAdd_le_orderTop_smul` / 定理 `orderTop_vAdd_le_orderTop_smul`

English:
theorem orderTop_vAdd_le_orderTop_smul
  statement: {Γ Γ'} [LinearOrder Γ] [LinearOrder Γ'] [VAdd Γ Γ']
  proof: by
  by_cases hx : x = 0; · simp_all
  by_cases hy : y = 0; · simp_all
  have hhy : ((of R).symm y) != 0 := hy
  rw [HahnSeries.orderTop_of_ne_zero hx]; rw [HahnSeries.orderTop_of_ne_zero hhy]; rw [← h]; rw [← Set.IsWF.min_vadd]
  by_cases hxy : (of R).symm (x • y) = 0
  · rw [hxy, HahnSeries.orderT

中文:
定理 orderTop_vAdd_le_orderTop_smul
  结论: {Γ Γ'} [线性序 Γ] [线性序 Γ'] [向量加法 Γ Γ']
  证明: by
  by_cases hx : x = 0; · simp_all
  by_cases hy : y = 0; · simp_all
  have hhy : ((of R).symm y) != 0 := hy
  rw [HahnSeries.orderTop_of_ne_zero hx]; rw [HahnSeries.orderTop_of_ne_zero hhy]; rw [← h]; rw [← Set.IsWF.min_vadd]
  by_cases hxy : (of R).symm (x • y) = 0
  · rw [hxy, HahnSeries.orderT

Depends on / 依赖: HahnSeries, HahnSeries.orderTop_of_ne_zero, HahnSeries.orderTop_zero, OrderTop, OrderTop.le_top, Set.IsWF.min_le_min_of_subset, Set.IsWF.min_vadd, WithTop, WithTop.coe_le_coe, coe_le_coe, le_top, min_le_min_of_subset, min_vadd, orderTop_of_ne_zero, orderTop_zero, support_smul_subset_vadd_support
-/
theorem orderTop_vAdd_le_orderTop_smul {Γ Γ'} [LinearOrder Γ] [LinearOrder Γ'] [VAdd Γ Γ']
    [IsOrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {x : R⟦Γ⟧}
    [VAdd (WithTop Γ) (WithTop Γ')] {y : HahnModule Γ' R V}
    (h : forall (γ : Γ) (γ' : Γ'), γ +ᵥ γ' = (γ : WithTop Γ) +ᵥ (γ' : WithTop Γ')) :
    x.orderTop +ᵥ ((of R).symm y).orderTop <= ((of R).symm (x • y)).orderTop := by
  by_cases hx : x = 0; · simp_all
  by_cases hy : y = 0; · simp_all
  have hhy : ((of R).symm y) != 0 := hy
  rw [HahnSeries.orderTop_of_ne_zero hx]; rw [HahnSeries.orderTop_of_ne_zero hhy]; rw [← h]; rw [← Set.IsWF.min_vadd]
  by_cases hxy : (of R).symm (x • y) = 0
  · rw [hxy, HahnSeries.orderTop_zero]
    exact OrderTop.le_top (α := WithTop Γ') _
  · rw [HahnSeries.orderTop_of_ne_zero hxy, WithTop.coe_le_coe]
    exact Set.IsWF.min_le_min_of_subset support_smul_subset_vadd_support

/--
theorem `coeff_smul_order_add_order` / 定理 `coeff_smul_order_add_order`

English:
theorem coeff_smul_order_add_order
  statement: {Γ}
  proof: by
  by_cases hx : x = (0 : R⟦Γ⟧); · simp [HahnSeries.coeff_zero, hx]
  by_cases hy : (of R).symm y = 0; · simp [hy, coeff_smul]
  rw [HahnSeries.order_of_ne hx]; rw [HahnSeries.order_of_ne hy]; rw [coeff_smul]; rw [HahnSeries.leadingCoeff_of_ne_zero hx]; rw [HahnSeries.leadingCoeff_of_ne_zero hy]; 

中文:
定理 coeff_smul_order_add_order
  结论: {Γ}
  证明: by
  by_cases hx : x = (0 : R⟦Γ⟧); · simp [HahnSeries.coeff_zero, hx]
  by_cases hy : (of R).symm y = 0; · simp [hy, coeff_smul]
  rw [HahnSeries.order_of_ne hx]; rw [HahnSeries.order_of_ne hy]; rw [coeff_smul]; rw [HahnSeries.leadingCoeff_of_ne_zero hx]; rw [HahnSeries.leadingCoeff_of_ne_zero hy]; 

Depends on / 依赖: Finset, Finset.sum_singleton, Finset.vaddAntidiagonal_min_vadd_min, HahnSeries, HahnSeries.coeff_zero, HahnSeries.leadingCoeff_of_ne_zero, HahnSeries.orderTop, HahnSeries.order_of_ne, coeff_smul, coeff_zero, leadingCoeff_of_ne_zero, orderTop, order_of_ne, sum_singleton, vaddAntidiagonal_min_vadd_min, vadd_eq_add
-/
theorem coeff_smul_order_add_order {Γ}
    [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [Zero R]
    [SMulWithZero R V] (x : R⟦Γ⟧) (y : HahnModule Γ R V) :
    ((of R).symm (x • y)).coeff (x.order + ((of R).symm y).order) =
    x.leadingCoeff • ((of R).symm y).leadingCoeff := by
  by_cases hx : x = (0 : R⟦Γ⟧); · simp [HahnSeries.coeff_zero, hx]
  by_cases hy : (of R).symm y = 0; · simp [hy, coeff_smul]
  rw [HahnSeries.order_of_ne hx]; rw [HahnSeries.order_of_ne hy]; rw [coeff_smul]; rw [HahnSeries.leadingCoeff_of_ne_zero hx]; rw [HahnSeries.leadingCoeff_of_ne_zero hy]; rw [← vadd_eq_add]; rw [Finset.vaddAntidiagonal_min_vadd_min]; rw [Finset.sum_singleton]
  simp [HahnSeries.orderTop, hx, hy]

end DistribSMul

end HahnModule

namespace HahnSeries

section mul

variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] : Mul R⟦Γ⟧ where
  body: (HahnModule.of R).symm (x • HahnModule.of R y)

中文:
实例 [非幺非结合半环
  签名: R] : 乘法 R⟦Γ⟧ where
  定义体: (HahnModule.of R).symm (x • HahnModule.of R y)

Depends on / 依赖: HahnModule, HahnModule.of
-/
instance [NonUnitalNonAssocSemiring R] : Mul R⟦Γ⟧ where
  mul x y := (HahnModule.of R).symm (x • HahnModule.of R y)

/--
theorem `of_symm_smul_of_eq_mul` / 定理 `of_symm_smul_of_eq_mul`

English:
theorem of_symm_smul_of_eq_mul
  given: [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧}
  proof: rfl

中文:
定理 of_symm_smul_of_eq_mul
  条件: [非幺非结合半环 R] {x y : R⟦Γ⟧}
  证明: rfl
-/
theorem of_symm_smul_of_eq_mul [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} :
    (HahnModule.of R).symm (x • HahnModule.of R y) = x * y := rfl

/--
theorem `coeff_mul` / 定理 `coeff_mul`

English:
theorem coeff_mul
  given: [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} {a : Γ}
  proof: rfl

中文:
定理 coeff_mul
  条件: [非幺非结合半环 R] {x y : R⟦Γ⟧} {a : Γ}
  证明: rfl
-/
theorem coeff_mul [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} {a : Γ} :
    (x * y).coeff a =
      ∑ ij in antidiagonal x.isPWO_support y.isPWO_support a, x.coeff ij.fst * y.coeff ij.snd :=
  rfl

/--
lemma `map_mul` / 引理 `map_mul`

English:
lemma map_mul
  statement: [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ->ₙ+* S)
  proof: by
  ext
  simp only [map_coeff, coeff_mul, map_sum, map_mul]
  refine Eq.symm (sum_subset (fun gh hgh => ?_) (fun gh hgh hz => ?_))
  · simp_all only [mem_antidiagonal, mem_support, map_coeff, ne_eq, and_true]
    exact ⟨fun h => hgh.1 (map_zero f ▸ congrArg f h), fun h => hgh.2.1 (map_zero f ▸ con

中文:
引理 map_mul
  结论: [非幺非结合半环 R] [非幺非结合半环 S] (f : R ->ₙ+* S)
  证明: by
  ext
  simp only [map_coeff, coeff_mul, map_sum, map_mul]
  refine Eq.symm (sum_subset (fun gh hgh => ?_) (fun gh hgh hz => ?_))
  · simp_all only [mem_antidiagonal, mem_support, map_coeff, ne_eq, and_true]
    exact ⟨fun h => hgh.1 (map_zero f ▸ congrArg f h), fun h => hgh.2.1 (map_zero f ▸ con
-/
protected lemma map_mul [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ->ₙ+* S)
    {x y : R⟦Γ⟧} : (x * y).map f = (x.map f : S⟦Γ⟧) * (y.map f) := by
  ext
  simp only [map_coeff, coeff_mul, map_sum, map_mul]
  refine Eq.symm (sum_subset (fun gh hgh => ?_) (fun gh hgh hz => ?_))
  · simp_all only [mem_antidiagonal, mem_support, map_coeff, ne_eq, and_true]
    exact ⟨fun h => hgh.1 (map_zero f ▸ congrArg f h), fun h => hgh.2.1 (map_zero f ▸ congrArg f h)⟩
  · simp_all only [mem_antidiagonal, mem_support, ne_eq, map_coeff, and_true,
      not_and, not_not]
    by_cases h : f (x.coeff gh.1) = 0
    · exact mul_eq_zero_of_left h (f (y.coeff gh.2))
    · exact mul_eq_zero_of_right (f (x.coeff gh.1)) (hz h)

/--
theorem `coeff_mul_left'` / 定理 `coeff_mul_left'`

English:
theorem coeff_mul_left'
  statement: [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} {a : Γ} {s : Set Γ}
  proof: HahnModule.coeff_smul_left hs hxs

中文:
定理 coeff_mul_left'
  结论: [非幺非结合半环 R] {x y : R⟦Γ⟧} {a : Γ} {s : 集合 Γ}
  证明: HahnModule.coeff_smul_left hs hxs

Depends on / 依赖: HahnModule, HahnModule.coeff_smul_left, coeff_smul_left
-/
theorem coeff_mul_left' [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} {a : Γ} {s : Set Γ}
    (hs : s.IsPWO) (hxs : x.support subseteq s) :
    (x * y).coeff a =
      ∑ ij in antidiagonal hs y.isPWO_support a, x.coeff ij.fst * y.coeff ij.snd :=
  HahnModule.coeff_smul_left hs hxs

/--
theorem `coeff_mul_right'` / 定理 `coeff_mul_right'`

English:
theorem coeff_mul_right'
  statement: [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} {a : Γ} {s : Set Γ}
  proof: HahnModule.coeff_smul_right hs hys

中文:
定理 coeff_mul_right'
  结论: [非幺非结合半环 R] {x y : R⟦Γ⟧} {a : Γ} {s : 集合 Γ}
  证明: HahnModule.coeff_smul_right hs hys

Depends on / 依赖: HahnModule, HahnModule.coeff_smul_right, coeff_smul_right
-/
theorem coeff_mul_right' [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} {a : Γ} {s : Set Γ}
    (hs : s.IsPWO) (hys : y.support subseteq s) :
    (x * y).coeff a =
      ∑ ij in antidiagonal x.isPWO_support hs a, x.coeff ij.fst * y.coeff ij.snd :=
  HahnModule.coeff_smul_right hs hys

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] : Distrib R⟦Γ⟧ where
  body: by
    simp only [← of_symm_smul_of_eq_mul]
    exact HahnModule.smul_add x y z
  right_distrib x y z := by
    simp only [← of_symm_smul_of_eq_mul]
    refine HahnModule.add_smul ?_
    simp only [smul_eq_mul]
    exact add_mul

中文:
实例 [非幺非结合半环
  签名: R] : Distrib R⟦Γ⟧ where
  定义体: by
    simp only [← of_symm_smul_of_eq_mul]
    exact HahnModule.smul_add x y z
  right_distrib x y z := by
    simp only [← of_symm_smul_of_eq_mul]
    refine HahnModule.add_smul ?_
    simp only [smul_eq_mul]
    exact add_mul

Depends on / 依赖: HahnModule, HahnModule.add_smul, HahnModule.smul_add, add_mul, add_smul, of_symm_smul_of_eq_mul, right_distrib, smul_add, smul_eq_mul
-/
instance [NonUnitalNonAssocSemiring R] : Distrib R⟦Γ⟧ where
  left_distrib x y z := by
    simp only [← of_symm_smul_of_eq_mul]
    exact HahnModule.smul_add x y z
  right_distrib x y z := by
    simp only [← of_symm_smul_of_eq_mul]
    refine HahnModule.add_smul ?_
    simp only [smul_eq_mul]
    exact add_mul

/--
theorem `coeff_single_mul_add` / 定理 `coeff_single_mul_add`

English:
theorem coeff_single_mul_add
  statement: [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a : Γ}
  proof: by
  rw [← of_symm_smul_of_eq_mul]; rw [add_comm]; rw [← vadd_eq_add]
  exact HahnModule.coeff_single_smul_vadd

中文:
定理 coeff_single_mul_add
  结论: [非幺非结合半环 R] {r : R} {x : R⟦Γ⟧} {a : Γ}
  证明: by
  rw [← of_symm_smul_of_eq_mul]; rw [add_comm]; rw [← vadd_eq_add]
  exact HahnModule.coeff_single_smul_vadd

Depends on / 依赖: HahnModule, HahnModule.coeff_single_smul_vadd, add_comm, coeff_single_smul_vadd, of_symm_smul_of_eq_mul, vadd_eq_add
-/
theorem coeff_single_mul_add [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a : Γ}
    {b : Γ} : (single b r * x).coeff (a + b) = r * x.coeff a := by
  rw [← of_symm_smul_of_eq_mul]; rw [add_comm]; rw [← vadd_eq_add]
  exact HahnModule.coeff_single_smul_vadd

/--
theorem `coeff_mul_single_add` / 定理 `coeff_mul_single_add`

English:
theorem coeff_mul_single_add
  statement: [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a : Γ}
  proof: by
  by_cases hr : r = 0
  · simp [hr, coeff_mul]
  simp only [hr, coeff_mul, support_single_of_ne, Ne, not_false_iff]
  by_cases hx : x.coeff a = 0
  · simp only [hx, zero_mul]
    rw [sum_congr _ fun _ _ => rfl]; rw [sum_empty]
    ext ⟨a1, a2⟩
    simp only [notMem_empty, not_and, Set.mem_singlet

中文:
定理 coeff_mul_single_add
  结论: [非幺非结合半环 R] {r : R} {x : R⟦Γ⟧} {a : Γ}
  证明: by
  by_cases hr : r = 0
  · simp [hr, coeff_mul]
  simp only [hr, coeff_mul, support_single_of_ne, Ne, not_false_iff]
  by_cases hx : x.coeff a = 0
  · simp only [hx, zero_mul]
    rw [sum_congr _ fun _ _ => rfl]; rw [sum_empty]
    ext ⟨a1, a2⟩
    simp only [notMem_empty, not_and, Set.mem_singlet

Depends on / 依赖: Set.mem_singleton_iff, add_right_cancel, coeff_mul, iff_false, ij.fst, ij.snd, mem_antidiagonal, mem_singleton_iff, notMem_empty, not_and, not_false_iff, single, sum_congr, sum_empty, support_single_of_ne, x.coeff, zero_mul
-/
theorem coeff_mul_single_add [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a : Γ}
    {b : Γ} : (x * single b r).coeff (a + b) = x.coeff a * r := by
  by_cases hr : r = 0
  · simp [hr, coeff_mul]
  simp only [hr, coeff_mul, support_single_of_ne, Ne, not_false_iff]
  by_cases hx : x.coeff a = 0
  · simp only [hx, zero_mul]
    rw [sum_congr _ fun _ _ => rfl]; rw [sum_empty]
    ext ⟨a1, a2⟩
    simp only [notMem_empty, not_and, Set.mem_singleton_iff,
      mem_antidiagonal, iff_false]
    rintro h2 rfl h1
    rw [← add_right_cancel h1] at hx
    exact h2 hx
  trans ∑ ij in {(a, b)}, x.coeff ij.fst * (single b r).coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp only [Set.mem_singleton_iff, Prod.mk_inj, mem_antidiagonal, mem_singleton]
    constructor
    · rintro ⟨_, rfl, h1⟩
      exact ⟨add_right_cancel h1, rfl⟩
    · rintro ⟨rfl, rfl⟩
      simp [hx]
  · simp

/--
theorem `coeff_single_mul` / 定理 `coeff_single_mul`

English:
theorem coeff_single_mul
  statement: [NonUnitalNonAssocSemiring R] [PartialOrder Γ'] [AddCommGroup Γ']
  proof: by
  simpa using coeff_single_mul_add (a := a - b) (b := b)

中文:
定理 coeff_single_mul
  结论: [非幺非结合半环 R] [偏序 Γ'] [加法交换群 Γ']
  证明: by
  simpa using coeff_single_mul_add (a := a - b) (b := b)

Depends on / 依赖: coeff_single_mul_add
-/
theorem coeff_single_mul [NonUnitalNonAssocSemiring R] [PartialOrder Γ'] [AddCommGroup Γ']
    [IsOrderedAddMonoid Γ'] {r : R} {x : R⟦Γ'⟧} {a b : Γ'} :
    (single b r * x).coeff a = r * x.coeff (a - b) := by
  simpa using coeff_single_mul_add (a := a - b) (b := b)

/--
theorem `coeff_mul_single` / 定理 `coeff_mul_single`

English:
theorem coeff_mul_single
  statement: [NonUnitalNonAssocSemiring R] [PartialOrder Γ'] [AddCommGroup Γ']
  proof: by
  simpa using coeff_mul_single_add (a := a - b) (b := b)

@[simp]

中文:
定理 coeff_mul_single
  结论: [非幺非结合半环 R] [偏序 Γ'] [加法交换群 Γ']
  证明: by
  simpa using coeff_mul_single_add (a := a - b) (b := b)

@[simp]

Depends on / 依赖: coeff_mul_single_add
-/
theorem coeff_mul_single [NonUnitalNonAssocSemiring R] [PartialOrder Γ'] [AddCommGroup Γ']
    [IsOrderedAddMonoid Γ'] {r : R} {x : R⟦Γ'⟧} {a b : Γ'} :
    (x * single b r).coeff a = x.coeff (a - b) * r := by
  simpa using coeff_mul_single_add (a := a - b) (b := b)

@[simp]
/--
theorem `coeff_mul_single_zero` / 定理 `coeff_mul_single_zero`

English:
theorem coeff_mul_single_zero
  given: [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a : Γ}
  proof: by rw [← add_zero a, coeff_mul_single_add, add_zero]

中文:
定理 coeff_mul_single_zero
  条件: [非幺非结合半环 R] {r : R} {x : R⟦Γ⟧} {a : Γ}
  证明: by rw [← add_zero a, coeff_mul_single_add, add_zero]

Depends on / 依赖: add_zero, coeff_mul_single_add
-/
theorem coeff_mul_single_zero [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a : Γ} :
    (x * single 0 r).coeff a = x.coeff a * r := by rw [← add_zero a, coeff_mul_single_add, add_zero]

/--
theorem `coeff_single_zero_mul` / 定理 `coeff_single_zero_mul`

English:
theorem coeff_single_zero_mul
  given: [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a : Γ}
  proof: by
  rw [← add_zero a]; rw [coeff_single_mul_add]; rw [add_zero]

@[simp]

中文:
定理 coeff_single_zero_mul
  条件: [非幺非结合半环 R] {r : R} {x : R⟦Γ⟧} {a : Γ}
  证明: by
  rw [← add_zero a]; rw [coeff_single_mul_add]; rw [add_zero]

@[simp]

Depends on / 依赖: add_zero, coeff_single_mul_add
-/
theorem coeff_single_zero_mul [NonUnitalNonAssocSemiring R] {r : R} {x : R⟦Γ⟧} {a : Γ} :
    ((single 0 r : R⟦Γ⟧) * x).coeff a = r * x.coeff a := by
  rw [← add_zero a]; rw [coeff_single_mul_add]; rw [add_zero]

@[simp]
/--
theorem `single_zero_mul_eq_smul` / 定理 `single_zero_mul_eq_smul`

English:
theorem single_zero_mul_eq_smul
  given: [Semiring R] {r : R} {x : R⟦Γ⟧}
  statement: single 0 r * x = r • x
  proof: by
  ext
  exact coeff_single_zero_mul

中文:
定理 single_zero_mul_eq_smul
  条件: [半环 R] {r : R} {x : R⟦Γ⟧}
  结论: single 0 r * x = r • x
  证明: by
  ext
  exact coeff_single_zero_mul

Depends on / 依赖: coeff_single_zero_mul
-/
theorem single_zero_mul_eq_smul [Semiring R] {r : R} {x : R⟦Γ⟧} : single 0 r * x = r • x := by
  ext
  exact coeff_single_zero_mul

/--
theorem `support_mul_subset` / 定理 `support_mul_subset`

English:
theorem support_mul_subset
  given: [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧}
  proof: by
  rw [← of_symm_smul_of_eq_mul]; rw [← vadd_eq_add]
  exact HahnModule.support_smul_subset_vadd_support

中文:
定理 support_mul_subset
  条件: [非幺非结合半环 R] {x y : R⟦Γ⟧}
  证明: by
  rw [← of_symm_smul_of_eq_mul]; rw [← vadd_eq_add]
  exact HahnModule.support_smul_subset_vadd_support

Depends on / 依赖: HahnModule, HahnModule.support_smul_subset_vadd_support, of_symm_smul_of_eq_mul, support_smul_subset_vadd_support, vadd_eq_add
-/
theorem support_mul_subset [NonUnitalNonAssocSemiring R] {x y : R⟦Γ⟧} :
    support (x * y) subseteq support x + support y := by
  rw [← of_symm_smul_of_eq_mul]; rw [← vadd_eq_add]
  exact HahnModule.support_smul_subset_vadd_support

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] : NonUnitalNonAssocSemiring R⟦Γ⟧ where
  body: by
    ext
    simp [coeff_mul]
  mul_zero _ := by
    ext
    simp [coeff_mul]

中文:
实例 [非幺非结合半环
  签名: R] : 非幺非结合半环 R⟦Γ⟧ where
  定义体: by
    ext
    simp [coeff_mul]
  mul_zero _ := by
    ext
    simp [coeff_mul]

Depends on / 依赖: coeff_mul, mul_zero
-/
instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring R⟦Γ⟧ where
  zero_mul _ := by
    ext
    simp [coeff_mul]
  mul_zero _ := by
    ext
    simp [coeff_mul]

end mul

section orderLemmas

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [NonUnitalNonAssocSemiring R]

/--
theorem `coeff_mul_order_add_order` / 定理 `coeff_mul_order_add_order`

English:
theorem coeff_mul_order_add_order
  given: (x y : R⟦Γ⟧)
  proof: by
  simp only [← of_symm_smul_of_eq_mul]
  exact HahnModule.coeff_smul_order_add_order x y

中文:
定理 coeff_mul_order_add_order
  条件: (x y : R⟦Γ⟧)
  证明: by
  simp only [← of_symm_smul_of_eq_mul]
  exact HahnModule.coeff_smul_order_add_order x y

Depends on / 依赖: HahnModule, HahnModule.coeff_smul_order_add_order, coeff_smul_order_add_order, of_symm_smul_of_eq_mul
-/
theorem coeff_mul_order_add_order (x y : R⟦Γ⟧) :
    (x * y).coeff (x.order + y.order) = x.leadingCoeff * y.leadingCoeff := by
  simp only [← of_symm_smul_of_eq_mul]
  exact HahnModule.coeff_smul_order_add_order x y

/--
theorem `orderTop_mul_of_ne_zero` / 定理 `orderTop_mul_of_ne_zero`

English:
theorem orderTop_mul_of_ne_zero
  given: {x y : R⟦Γ⟧} (h : x.leadingCoeff * y.leadingCoeff != 0)
  proof: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  have : (x * y).coeff (x.order + y.order) != 0 := by rwa [coeff_mul_order_add_order x y]
  have hxy : x * y != 0 := fun h => (by simp [h] at this)
  rw [← order_eq_orderTop_of_ne_zero hx]; rw [← order_eq_orderTop_of_ne_zero hy

中文:
定理 orderTop_mul_of_ne_zero
  条件: {x y : R⟦Γ⟧} (h : x.leadingCoeff * y.leadingCoeff != 0)
  证明: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  have : (x * y).coeff (x.order + y.order) != 0 := by rwa [coeff_mul_order_add_order x y]
  have hxy : x * y != 0 := fun h => (by simp [h] at this)
  rw [← order_eq_orderTop_of_ne_zero hx]; rw [← order_eq_orderTop_of_ne_zero hy

Depends on / 依赖: HahnSeries, HahnSeries.order_of_ne, WithTop, WithTop.coe_add, WithTop.coe_eq_coe, coe_add, coe_eq_coe, coeff_mul_order_add_order, le_antisymm, order_eq_orderTop_of_ne_zero, order_le_of_coeff_ne_zero, order_of_ne, x.order, y.order
-/
theorem orderTop_mul_of_ne_zero {x y : R⟦Γ⟧} (h : x.leadingCoeff * y.leadingCoeff != 0) :
    (x * y).orderTop = x.orderTop + y.orderTop := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  have : (x * y).coeff (x.order + y.order) != 0 := by rwa [coeff_mul_order_add_order x y]
  have hxy : x * y != 0 := fun h => (by simp [h] at this)
  rw [← order_eq_orderTop_of_ne_zero hx]; rw [← order_eq_orderTop_of_ne_zero hy]; rw [← order_eq_orderTop_of_ne_zero hxy]; rw [← WithTop.coe_add]; rw [WithTop.coe_eq_coe]
  refine le_antisymm (order_le_of_coeff_ne_zero this) ?_
  rw [HahnSeries.order_of_ne hx]; rw [HahnSeries.order_of_ne hy]; rw [HahnSeries.order_of_ne hxy]; rw [← Set.IsWF.min_add]
  exact Set.IsWF.min_le_min_of_subset support_mul_subset

@[deprecated (since := "2026-01-02")]
alias orderTop_mul_of_nonzero := orderTop_mul_of_ne_zero

@[simp]
/--
theorem `orderTop_mul` / 定理 `orderTop_mul`

English:
theorem orderTop_mul
  given: (x y : R⟦Γ⟧) [NoZeroDivisors R]
  proof: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  apply orderTop_mul_of_ne_zero
  simp_all

中文:
定理 orderTop_mul
  条件: (x y : R⟦Γ⟧) [无零因子 R]
  证明: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  apply orderTop_mul_of_ne_zero
  simp_all

Depends on / 依赖: orderTop_mul_of_ne_zero
-/
theorem orderTop_mul (x y : R⟦Γ⟧) [NoZeroDivisors R] :
    (x * y).orderTop = x.orderTop + y.orderTop := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  apply orderTop_mul_of_ne_zero
  simp_all

/--
theorem `orderTop_add_le_mul` / 定理 `orderTop_add_le_mul`

English:
theorem orderTop_add_le_mul
  given: {x y : R⟦Γ⟧}
  statement: x.orderTop + y.orderTop <= (x * y).orderTop
  proof: by
  rw [← smul_eq_mul]
  exact HahnModule.orderTop_vAdd_le_orderTop_smul fun i j => rfl

中文:
定理 orderTop_add_le_mul
  条件: {x y : R⟦Γ⟧}
  结论: x.orderTop + y.orderTop <= (x * y).orderTop
  证明: by
  rw [← smul_eq_mul]
  exact HahnModule.orderTop_vAdd_le_orderTop_smul fun i j => rfl

Depends on / 依赖: HahnModule, HahnModule.orderTop_vAdd_le_orderTop_smul, orderTop_vAdd_le_orderTop_smul, smul_eq_mul
-/
theorem orderTop_add_le_mul {x y : R⟦Γ⟧} : x.orderTop + y.orderTop <= (x * y).orderTop := by
  rw [← smul_eq_mul]
  exact HahnModule.orderTop_vAdd_le_orderTop_smul fun i j => rfl

/--
theorem `order_mul_of_ne_zero` / 定理 `order_mul_of_ne_zero`

English:
theorem order_mul_of_ne_zero
  statement: {x y : R⟦Γ⟧}
  proof: by
  have hx : x.leadingCoeff != 0 := by aesop
  have hy : y.leadingCoeff != 0 := by aesop
  have hxy : (x * y).coeff (x.order + y.order) != 0 :=
    ne_of_eq_of_ne (coeff_mul_order_add_order x y) h
  refine le_antisymm (order_le_of_coeff_ne_zero
    (Eq.mpr (congrArg (fun _a => _a != 0) (coeff_mul_

中文:
定理 order_mul_of_ne_zero
  结论: {x y : R⟦Γ⟧}
  证明: by
  have hx : x.leadingCoeff != 0 := by aesop
  have hy : y.leadingCoeff != 0 := by aesop
  have hxy : (x * y).coeff (x.order + y.order) != 0 :=
    ne_of_eq_of_ne (coeff_mul_order_add_order x y) h
  refine le_antisymm (order_le_of_coeff_ne_zero
    (Eq.mpr (congrArg (fun _a => _a != 0) (coeff_mul_

Depends on / 依赖: Eq.mpr, Set.IsWF.min_add, Set.IsWF.min_l, coeff_mul_order_add_order, le_antisymm, leadingCoeff, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mp, min_add, min_l, ne_of_eq_of_ne, ne_zero_of_coeff_ne_zero, order_le_of_coeff_ne_zero, order_of_ne, x.leadingCoeff, x.order, y.leadingCoeff, y.order
-/
theorem order_mul_of_ne_zero {x y : R⟦Γ⟧}
    (h : x.leadingCoeff * y.leadingCoeff != 0) : (x * y).order = x.order + y.order := by
  have hx : x.leadingCoeff != 0 := by aesop
  have hy : y.leadingCoeff != 0 := by aesop
  have hxy : (x * y).coeff (x.order + y.order) != 0 :=
    ne_of_eq_of_ne (coeff_mul_order_add_order x y) h
  refine le_antisymm (order_le_of_coeff_ne_zero
    (Eq.mpr (congrArg (fun _a => _a != 0) (coeff_mul_order_add_order x y)) h)) ?_
  rw [order_of_ne <| leadingCoeff_ne_zero.mp hx]; rw [order_of_ne <| leadingCoeff_ne_zero.mp hy]; rw [order_of_ne ne_zero_of_coeff_ne_zero hxy]; rw [← Set.IsWF.min_add]
  exact Set.IsWF.min_le_min_of_subset support_mul_subset

@[deprecated (since := "2026-01-02")]
alias order_mul_of_nonzero := order_mul_of_ne_zero

/--
theorem `leadingCoeff_mul_of_ne_zero` / 定理 `leadingCoeff_mul_of_ne_zero`

English:
theorem leadingCoeff_mul_of_ne_zero
  given: {x y : R⟦Γ⟧} (h : x.leadingCoeff * y.leadingCoeff != 0)
  proof: by
  simp only [leadingCoeff_eq, order_mul_of_ne_zero h, coeff_mul_order_add_order]

@[deprecated (since := "2026-01-02")]
alias leadingCoeff_mul_of_nonzero := leadingCoeff_mul_of_ne_zero

@[simp]

中文:
定理 leadingCoeff_mul_of_ne_zero
  条件: {x y : R⟦Γ⟧} (h : x.leadingCoeff * y.leadingCoeff != 0)
  证明: by
  simp only [leadingCoeff_eq, order_mul_of_ne_zero h, coeff_mul_order_add_order]

@[deprecated (since := "2026-01-02")]
alias leadingCoeff_mul_of_nonzero := leadingCoeff_mul_of_ne_zero

@[simp]

Depends on / 依赖: coeff_mul_order_add_order, leadingCoeff_eq, order_mul_of_ne_zero
-/
theorem leadingCoeff_mul_of_ne_zero {x y : R⟦Γ⟧} (h : x.leadingCoeff * y.leadingCoeff != 0) :
    (x * y).leadingCoeff = x.leadingCoeff * y.leadingCoeff := by
  simp only [leadingCoeff_eq, order_mul_of_ne_zero h, coeff_mul_order_add_order]

@[deprecated (since := "2026-01-02")]
alias leadingCoeff_mul_of_nonzero := leadingCoeff_mul_of_ne_zero

@[simp]
/--
theorem `leadingCoeff_mul` / 定理 `leadingCoeff_mul`

English:
theorem leadingCoeff_mul
  given: (x y : R⟦Γ⟧) [NoZeroDivisors R]
  proof: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  apply leadingCoeff_mul_of_ne_zero
  simp_all

中文:
定理 leadingCoeff_mul
  条件: (x y : R⟦Γ⟧) [无零因子 R]
  证明: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  apply leadingCoeff_mul_of_ne_zero
  simp_all

Depends on / 依赖: leadingCoeff_mul_of_ne_zero
-/
theorem leadingCoeff_mul (x y : R⟦Γ⟧) [NoZeroDivisors R] :
    (x * y).leadingCoeff = x.leadingCoeff * y.leadingCoeff := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  apply leadingCoeff_mul_of_ne_zero
  simp_all

/--
theorem `order_single_mul_of_isRegular` / 定理 `order_single_mul_of_isRegular`

English:
theorem order_single_mul_of_isRegular
  statement: {g : Γ} {r : R} (hr : IsRegular r)
  proof: by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact (hx <| Subsingleton.eq_zero x).elim
  have hrx : ((single g) r).leadingCoeff * x.leadingCoeff != 0 := by
    rwa [leadingCoeff_of_single, ne_eq, hr.left.mul_left_eq_zero_iff, leadingCoeff_eq_zero]
  rw [order_mul_of_ne_zero hrx]; rw [order_

中文:
定理 order_single_mul_of_isRegular
  结论: {g : Γ} {r : R} (hr : 是正则 r)
  证明: by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact (hx <| Subsingleton.eq_zero x).elim
  have hrx : ((single g) r).leadingCoeff * x.leadingCoeff != 0 := by
    rwa [leadingCoeff_of_single, ne_eq, hr.left.mul_left_eq_zero_iff, leadingCoeff_eq_zero]
  rw [order_mul_of_ne_zero hrx]; rw [order_

Depends on / 依赖: IsRegular, IsRegular.ne_zero, Subsingleton, Subsingleton.eq_zero, eq_zero, hr.left.mul_left_eq_zero_iff, leadingCoeff, leadingCoeff_eq_zero, leadingCoeff_of_single, mul_left_eq_zero_iff, ne_eq, ne_zero, order_mul_of_ne_zero, order_single, single, subsingleton_or_nontrivial, x.leadingCoeff
-/
theorem order_single_mul_of_isRegular {g : Γ} {r : R} (hr : IsRegular r)
    {x : R⟦Γ⟧} (hx : x != 0) : (((single g) r) * x).order = g + x.order := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact (hx <| Subsingleton.eq_zero x).elim
  have hrx : ((single g) r).leadingCoeff * x.leadingCoeff != 0 := by
    rwa [leadingCoeff_of_single, ne_eq, hr.left.mul_left_eq_zero_iff, leadingCoeff_eq_zero]
  rw [order_mul_of_ne_zero hrx]; rw [order_single <| IsRegular.ne_zero hr]

end orderLemmas

section Ring

variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

set_option backward.privateInPublic true in
/--
theorem `mul_assoc'` / 定理 `mul_assoc'`

English:
theorem mul_assoc'
  given: [NonUnitalSemiring R] (x y z : R⟦Γ⟧)
  statement: x * y * z = x * (y * z)
  proof: by
  ext b
  rw [coeff_mul_left' (x.isPWO_support.add y.isPWO_support) support_mul_subset]; rw [coeff_mul_right' (y.isPWO_support.add z.isPWO_support) support_mul_subset]
  simp only [coeff_mul, sum_mul, mul_sum, sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ => ⟨(k, l + j), (l, j)⟩)
  

中文:
定理 mul_assoc'
  条件: [非幺半环 R] (x y z : R⟦Γ⟧)
  结论: x * y * z = x * (y * z)
  证明: by
  ext b
  rw [coeff_mul_left' (x.isPWO_support.add y.isPWO_support) support_mul_subset]; rw [coeff_mul_right' (y.isPWO_support.add z.isPWO_support) support_mul_subset]
  simp only [coeff_mul, sum_mul, mul_sum, sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ => ⟨(k, l + j), (l, j)⟩)
  
-/
private theorem mul_assoc' [NonUnitalSemiring R] (x y z : R⟦Γ⟧) : x * y * z = x * (y * z) := by
  ext b
  rw [coeff_mul_left' (x.isPWO_support.add y.isPWO_support) support_mul_subset]; rw [coeff_mul_right' (y.isPWO_support.add z.isPWO_support) support_mul_subset]
  simp only [coeff_mul, sum_mul, mul_sum, sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ => ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ => ⟨(i + k, l), (i, k)⟩) <;>
    aesop (add safe Set.add_mem_add) (add simp [add_assoc, mul_assoc])

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSemiring
  signature: R] : NonUnitalSemiring R⟦Γ⟧ where
  body: mul_assoc'

中文:
实例 [非幺半环
  签名: R] : 非幺半环 R⟦Γ⟧ where
  定义体: mul_assoc'

Depends on / 依赖: mul_assoc
-/
instance [NonUnitalSemiring R] : NonUnitalSemiring R⟦Γ⟧ where
  mul_assoc := mul_assoc'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocSemiring
  signature: R] : NonAssocSemiring R⟦Γ⟧ where
  body: by
    ext
    exact coeff_single_zero_mul.trans (one_mul _)
  mul_one x := by
    ext
    exact coeff_mul_single_zero.trans (mul_one _)

中文:
实例 [非结合半环
  签名: R] : 非结合半环 R⟦Γ⟧ where
  定义体: by
    ext
    exact coeff_single_zero_mul.trans (one_mul _)
  mul_one x := by
    ext
    exact coeff_mul_single_zero.trans (mul_one _)

Depends on / 依赖: coeff_mul_single_zero, coeff_mul_single_zero.trans, coeff_single_zero_mul, coeff_single_zero_mul.trans, mul_one, one_mul
-/
instance [NonAssocSemiring R] : NonAssocSemiring R⟦Γ⟧ where
  one_mul x := by
    ext
    exact coeff_single_zero_mul.trans (one_mul _)
  mul_one x := by
    ext
    exact coeff_mul_single_zero.trans (mul_one _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] : Semiring R⟦Γ⟧ where

中文:
实例 [半环
  签名: R] : 半环 R⟦Γ⟧ where
-/
instance [Semiring R] : Semiring R⟦Γ⟧ where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommSemiring
  signature: R] : NonUnitalCommSemiring R⟦Γ⟧ where
  body: inferInstance
  mul_comm x y := by
    ext
    simp_rw [coeff_mul, mul_comm]
exact Finset.sum_equiv (Equiv.prodComm _ _) (fun _ => swap_mem_antidiagonal.symm) by simp

中文:
实例 [非幺交换半环
  签名: R] : 非幺交换半环 R⟦Γ⟧ where
  定义体: inferInstance
  mul_comm x y := by
    ext
    simp_rw [coeff_mul, mul_comm]
exact Finset.sum_equiv (Equiv.prodComm _ _) (fun _ => swap_mem_antidiagonal.symm) by simp
-/
instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring R⟦Γ⟧ where
  __ : NonUnitalSemiring R⟦Γ⟧ := inferInstance
  mul_comm x y := by
    ext
    simp_rw [coeff_mul, mul_comm]
exact Finset.sum_equiv (Equiv.prodComm _ _) (fun _ => swap_mem_antidiagonal.symm) by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: R] : CommSemiring R⟦Γ⟧ where

中文:
实例 [交换半环
  签名: R] : 交换半环 R⟦Γ⟧ where
-/
instance [CommSemiring R] : CommSemiring R⟦Γ⟧ where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: R] : NonUnitalNonAssocRing R⟦Γ⟧ where

中文:
实例 [非幺非结合环
  签名: R] : 非幺非结合环 R⟦Γ⟧ where
-/
instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing R⟦Γ⟧ where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalRing
  signature: R] : NonUnitalRing R⟦Γ⟧ where

中文:
实例 [非幺环
  签名: R] : 非幺环 R⟦Γ⟧ where
-/
instance [NonUnitalRing R] : NonUnitalRing R⟦Γ⟧ where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocRing
  signature: R] : NonAssocRing R⟦Γ⟧ where

中文:
实例 [非结合环
  签名: R] : 非结合环 R⟦Γ⟧ where
-/
instance [NonAssocRing R] : NonAssocRing R⟦Γ⟧ where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: R] : Ring R⟦Γ⟧ where

中文:
实例 [环
  签名: R] : 环 R⟦Γ⟧ where
-/
instance [Ring R] : Ring R⟦Γ⟧ where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommRing
  signature: R] : NonUnitalCommRing R⟦Γ⟧ where

中文:
实例 [非幺交换环
  签名: R] : 非幺交换环 R⟦Γ⟧ where
-/
instance [NonUnitalCommRing R] : NonUnitalCommRing R⟦Γ⟧ where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: R] : CommRing R⟦Γ⟧ where

中文:
实例 [交换环
  签名: R] : 交换环 R⟦Γ⟧ where
-/
instance [CommRing R] : CommRing R⟦Γ⟧ where

end Ring

/--
theorem `orderTop_nsmul_le_orderTop_pow` / 定理 `orderTop_nsmul_le_orderTop_pow`

English:
theorem orderTop_nsmul_le_orderTop_pow
  statement: [AddCommMonoid Γ] [LinearOrder Γ]
  proof: by
  induction n with
  | zero =>
    simp only [zero_smul, pow_zero]
    by_cases h : NeZero (1 : R)
    · simp
    · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp fun _ => h NeZero.one
      simp
  | succ n ih =>
    rw [add_nsmul]; rw [pow_add]
    calc
      n • x.orderTop + 1 • x.

中文:
定理 orderTop_nsmul_le_orderTop_pow
  结论: [加法交换幺半群 Γ] [线性序 Γ]
  证明: by
  induction n with
  | zero =>
    simp only [zero_smul, pow_zero]
    by_cases h : NeZero (1 : R)
    · simp
    · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp fun _ => h NeZero.one
      simp
  | succ n ih =>
    rw [add_nsmul]; rw [pow_add]
    calc
      n • x.orderTop + 1 • x.

Depends on / 依赖: NeZero, NeZero.one, Subsingleton, add_nsmul, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton.mp, one_nsmul, orderTo, orderTop, orderTop_add_le_mul, pow_add, pow_zero, x.orderTop, zero_smul
-/
theorem orderTop_nsmul_le_orderTop_pow [AddCommMonoid Γ] [LinearOrder Γ]
    [IsOrderedCancelAddMonoid Γ] [Semiring R] {x : R⟦Γ⟧} {n : Nat} :
    n • x.orderTop <= (x ^ n).orderTop := by
  induction n with
  | zero =>
    simp only [zero_smul, pow_zero]
    by_cases h : NeZero (1 : R)
    · simp
    · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp fun _ => h NeZero.one
      simp
  | succ n ih =>
    rw [add_nsmul]; rw [pow_add]
    calc
      n • x.orderTop + 1 • x.orderTop <= (x ^ n).orderTop + 1 • x.orderTop := by gcongr
      (x ^ n).orderTop + 1 • x.orderTop = (x ^ n).orderTop + x.orderTop := by rw [one_nsmul]
      (x ^ n).orderTop + x.orderTop <= (x ^ n * x).orderTop := orderTop_add_le_mul
      (x ^ n * x).orderTop <= (x ^ n * x ^ 1).orderTop := by rw [pow_one]

/--
theorem `orderTop_self_sub_one_pos_iff` / 定理 `orderTop_self_sub_one_pos_iff`

English:
theorem orderTop_self_sub_one_pos_iff
  statement: [LinearOrder Γ] [Zero Γ] [NonAssocRing R] [Nontrivial R]
  proof: by
  constructor
  · intro hx
    constructor
    · rw [← sub_add_cancel x 1, add_comm, ← orderTop_one (R := R)]
      exact orderTop_add_eq_left (Γ := Γ) (R := R) (orderTop_one (R := R) (Γ := Γ) ▸ hx)
    · rw [← sub_add_cancel x 1, add_comm, ← leadingCoeff_one (Γ := Γ) (R := R)]
      exact leadin

中文:
定理 orderTop_self_sub_one_pos_iff
  结论: [线性序 Γ] [零 Γ] [非结合环 R] [非平凡 R]
  证明: by
  constructor
  · intro hx
    constructor
    · rw [← sub_add_cancel x 1, add_comm, ← orderTop_one (R := R)]
      exact orderTop_add_eq_left (Γ := Γ) (R := R) (orderTop_one (R := R) (Γ := Γ) ▸ hx)
    · rw [← sub_add_cancel x 1, add_comm, ← leadingCoeff_one (Γ := Γ) (R := R)]
      exact leadin

Depends on / 依赖: Ne.symm, add_comm, le_of_eq_of_le, leadingCoeff_add_eq_left, leadingCoeff_one, lt_of_le_of_ne, min_orderTop_le_orderTop_sub, orderTo, orderTop_add_eq_left, orderTop_one, orderTop_sub_ne, sub_add_cancel
-/
theorem orderTop_self_sub_one_pos_iff [LinearOrder Γ] [Zero Γ] [NonAssocRing R] [Nontrivial R]
    (x : R⟦Γ⟧) :
    0 < (x - 1).orderTop ↔ x.orderTop = 0 ∧ x.leadingCoeff = 1 := by
  constructor
  · intro hx
    constructor
    · rw [← sub_add_cancel x 1, add_comm, ← orderTop_one (R := R)]
      exact orderTop_add_eq_left (Γ := Γ) (R := R) (orderTop_one (R := R) (Γ := Γ) ▸ hx)
    · rw [← sub_add_cancel x 1, add_comm, ← leadingCoeff_one (Γ := Γ) (R := R)]
      exact leadingCoeff_add_eq_left (Γ := Γ) (R := R) (orderTop_one (R := R) (Γ := Γ) ▸ hx)
  · intro h
    refine lt_of_le_of_ne (le_of_eq_of_le (by simp_all)
      (min_orderTop_le_orderTop_sub (Γ := Γ) (R := R))) <| Ne.symm <|
      orderTop_sub_ne h.1 orderTop_one ?_
    rw [h.2]; rw [leadingCoeff_one]

/--
theorem `orderTop_sub_pos` / 定理 `orderTop_sub_pos`

English:
theorem orderTop_sub_pos
  statement: [PartialOrder Γ] [Zero Γ] [AddCommGroup R] [One R] {g : Γ} (hg : 0 < g)
  proof: by
  by_cases hr : r = 0 <;> simp [hr, hg]

中文:
定理 orderTop_sub_pos
  结论: [偏序 Γ] [零 Γ] [加法交换群 R] [幺 R] {g : Γ} (hg : 0 < g)
  证明: by
  by_cases hr : r = 0 <;> simp [hr, hg]
-/
theorem orderTop_sub_pos [PartialOrder Γ] [Zero Γ] [AddCommGroup R] [One R] {g : Γ} (hg : 0 < g)
    (r : R) :
    0 < ((1 + single g r) - 1).orderTop := by
  by_cases hr : r = 0 <;> simp [hr, hg]

/--
Definition of `orderTopSubOnePos` / `orderTopSubOnePos` 的定义

English:
definition orderTopSubOnePos
  signature: (Γ R) [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
  body: { x : R⟦Γ⟧ˣ | 0 < (x.val - 1).orderTop}
  mul_mem' := by
    intro x y hx hy
    obtain (_ | _) := subsingleton_or_nontrivial R
    · simp
    · simp_all only [Set.mem_ofPred_eq, orderTop_self_sub_one_pos_iff]
      have h1 : x.val.leadingCoeff * y.val.leadingCoeff = 1 := by rw [hx.2, hy.2, mul_one]

中文:
定义 orderTopSubOnePos
  签名: (Γ R) [线性序 Γ] [加法交换幺半群 Γ] [是OrderedCancelAdd幺半群 Γ]
  定义体: { x : R⟦Γ⟧ˣ | 0 < (x.val - 1).orderTop}
  mul_mem' := by
    intro x y hx hy
    obtain (_ | _) := subsingleton_or_nontrivial R
    · simp
    · simp_all only [Set.mem_ofPred_eq, orderTop_self_sub_one_pos_iff]
      have h1 : x.val.leadingCoeff * y.val.leadingCoeff = 1 := by rw [hx.2, hy.2, mul_one]

Depends on / 依赖: orderTop, x.val
-/
def orderTopSubOnePos (Γ R) [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [CommRing R] : Subgroup R⟦Γ⟧ˣ where
  carrier := { x : R⟦Γ⟧ˣ | 0 < (x.val - 1).orderTop}
  mul_mem' := by
    intro x y hx hy
    obtain (_ | _) := subsingleton_or_nontrivial R
    · simp
    · simp_all only [Set.mem_ofPred_eq, orderTop_self_sub_one_pos_iff]
      have h1 : x.val.leadingCoeff * y.val.leadingCoeff = 1 := by rw [hx.2, hy.2, mul_one]
      constructor
      · rw [Units.val_mul, orderTop_mul_of_ne_zero (by simp [h1]), hx.1, hy.1, add_zero]
      · rw [Units.val_mul, leadingCoeff_mul_of_ne_zero (h1 ▸ one_ne_zero), h1]
  one_mem' := by simp
  inv_mem' {y} h := by
    suffices 0 < (y.inv - 1).orderTop by exact this
    obtain (_ | _) := subsingleton_or_nontrivial R
    · simp
    · have : 0 < (y.val - 1).orderTop := h
      rw [orderTop_self_sub_one_pos_iff] at this
      have nz : y.val.leadingCoeff * y.inv.leadingCoeff != 0 := by
        rw [this.2]; rw [one_mul]
        exact leadingCoeff_ne_zero.mpr (by simp)
      refine y.inv.orderTop_self_sub_one_pos_iff.mpr ⟨?_, ?_⟩
      · simpa [this.1, y.val_inv] using (orderTop_mul_of_ne_zero nz).symm
      · simpa [this.2, y.val_inv] using (leadingCoeff_mul_of_ne_zero nz).symm

@[simp]
/--
theorem `mem_orderTopSubOnePos_iff` / 定理 `mem_orderTopSubOnePos_iff`

English:
theorem mem_orderTopSubOnePos_iff
  statement: [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
  proof: .rfl

中文:
定理 mem_orderTopSubOnePos_iff
  结论: [线性序 Γ] [加法交换幺半群 Γ] [是OrderedCancelAdd幺半群 Γ]
  证明: .rfl
-/
theorem mem_orderTopSubOnePos_iff [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [CommRing R] (x : R⟦Γ⟧ˣ) :
    x in orderTopSubOnePos Γ R ↔ 0 < (x.val - 1).orderTop := .rfl

end HahnSeries

namespace HahnModule
variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
variable [PartialOrder Γ'] [AddAction Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [AddCommMonoid V]

set_option backward.privateInPublic true in
/--
theorem `mul_smul'` / 定理 `mul_smul'`

English:
theorem mul_smul'
  statement: [Semiring R] [Module R V] (x y : R⟦Γ⟧)
  proof: by
  ext b
  rw [coeff_smul_left (x.isPWO_support.add y.isPWO_support)
    HahnSeries.support_mul_subset]; rw [coeff_smul_right
    (y.isPWO_support.vadd ((of R).symm z).isPWO_support) support_smul_subset_vadd_support]
  simp only [HahnSeries.coeff_mul, coeff_smul, sum_smul, smul_sum, sum_sigma']
  

中文:
定理 mul_smul'
  结论: [半环 R] [模 R V] (x y : R⟦Γ⟧)
  证明: by
  ext b
  rw [coeff_smul_left (x.isPWO_support.add y.isPWO_support)
    HahnSeries.support_mul_subset]; rw [coeff_smul_right
    (y.isPWO_support.vadd ((of R).symm z).isPWO_support) support_smul_subset_vadd_support]
  simp only [HahnSeries.coeff_mul, coeff_smul, sum_smul, smul_sum, sum_sigma']
  
-/
private theorem mul_smul' [Semiring R] [Module R V] (x y : R⟦Γ⟧)
    (z : HahnModule Γ' R V) : (x * y) • z = x • (y • z) := by
  ext b
  rw [coeff_smul_left (x.isPWO_support.add y.isPWO_support)
    HahnSeries.support_mul_subset]; rw [coeff_smul_right
    (y.isPWO_support.vadd ((of R).symm z).isPWO_support) support_smul_subset_vadd_support]
  simp only [HahnSeries.coeff_mul, coeff_smul, sum_smul, smul_sum, sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ => ⟨(k, l +ᵥ j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ => ⟨(i + k, l), (i, k)⟩) <;>
    aesop (add safe [Set.vadd_mem_vadd, Set.add_mem_add]) (add simp [add_vadd, mul_smul])

/--
Instance `instBaseModule` / 实例 `instBaseModule`

English:
instance instBaseModule
  signature: [Semiring R] [Module R V]
  body: inferInstanceAs Module R V⟦Γ'⟧

中文:
实例 instBaseModule
  签名: [半环 R] [模 R V]
  定义体: inferInstanceAs Module R V⟦Γ'⟧

Depends on / 依赖: Module
-/
instance instBaseModule [Semiring R] [Module R V] : Module R (HahnModule Γ' R V) :=
inferInstanceAs Module R V⟦Γ'⟧

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring R] [Module R V]
  body: {
  (inferInstance : DistribSMul R⟦Γ⟧ (HahnModule Γ' R V)) with
  mul_smul := mul_smul'
  one_smul := fun _ => one_smul'
  add_smul := fun _ _ _ => add_smul Module.add_smul
  zero_smul := fun _ => zero_smul' }

中文:
实例 instModule
  签名: [半环 R] [模 R V]
  定义体: {
  (inferInstance : DistribSMul R⟦Γ⟧ (HahnModule Γ' R V)) with
  mul_smul := mul_smul'
  one_smul := fun _ => one_smul'
  add_smul := fun _ _ _ => add_smul Module.add_smul
  zero_smul := fun _ => zero_smul' }
-/
instance instModule [Semiring R] [Module R V] : Module R⟦Γ⟧
    (HahnModule Γ' R V) := {
  (inferInstance : DistribSMul R⟦Γ⟧ (HahnModule Γ' R V)) with
  mul_smul := mul_smul'
  one_smul := fun _ => one_smul'
  add_smul := fun _ _ _ => add_smul Module.add_smul
  zero_smul := fun _ => zero_smul' }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] {S
  body: by
    ext
    simp

中文:
实例 [零
  签名: R] {S
  定义体: by
    ext
    simp
-/
instance [Zero R] {S : Type*} [Zero S] [SMul R S] [SMulWithZero R V] [SMulWithZero S V]
    [IsScalarTower R S V] : IsScalarTower R S V⟦Γ⟧ where
  smul_assoc r s a := by
    ext
    simp

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [Module R V] : IsScalarTower R R⟦Γ⟧ (HahnModule Γ' R V) where
  body: by
    rw [← HahnSeries.single_zero_mul_eq_smul]; rw [mul_smul']; rw [← single_zero_smul_eq_smul Γ]

中文:
实例 [半环
  签名: R] [模 R V] : 标量塔 R R⟦Γ⟧ (HahnModule Γ' R V) where
  定义体: by
    rw [← HahnSeries.single_zero_mul_eq_smul]; rw [mul_smul']; rw [← single_zero_smul_eq_smul Γ]

Depends on / 依赖: HahnSeries, HahnSeries.single_zero_mul_eq_smul, mul_smul, single_zero_mul_eq_smul, single_zero_smul_eq_smul
-/
instance [Semiring R] [Module R V] : IsScalarTower R R⟦Γ⟧ (HahnModule Γ' R V) where
  smul_assoc r x a := by
    rw [← HahnSeries.single_zero_mul_eq_smul]; rw [mul_smul']; rw [← single_zero_smul_eq_smul Γ]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `SMulCommClass` / 实例 `SMulCommClass`

English:
instance SMulCommClass
  signature: [CommSemiring R] [Module R V]
  body: by
    rw [← single_zero_smul_eq_smul Γ]; rw [← mul_smul']; rw [mul_comm]; rw [mul_smul']; rw [single_zero_smul_eq_smul Γ]

中文:
实例 标量交换类
  签名: [交换半环 R] [模 R V]
  定义体: by
    rw [← single_zero_smul_eq_smul Γ]; rw [← mul_smul']; rw [mul_comm]; rw [mul_smul']; rw [single_zero_smul_eq_smul Γ]

Depends on / 依赖: mul_comm, mul_smul, single_zero_smul_eq_smul
-/
instance SMulCommClass [CommSemiring R] [Module R V] :
    SMulCommClass R R⟦Γ⟧ (HahnModule Γ' R V) where
  smul_comm r x y := by
    rw [← single_zero_smul_eq_smul Γ]; rw [← mul_smul']; rw [mul_comm]; rw [mul_smul']; rw [single_zero_smul_eq_smul Γ]

/--
Instance `instIsTorsionFree` / 实例 `instIsTorsionFree`

English:
instance instIsTorsionFree
  signature: {Γ V : Type*} [Ring R] [IsDomain R] [AddCommGroup V] [AddCommMonoid Γ]
  body: .of_smul_eq_zero fun x y hxy => by
    contrapose! hxy
    rw [ne_eq]; rw [HahnModule.ext_iff]; rw [funext_iff]; rw [not_forall]
    exact ⟨x.order + ((of R).symm y).order, by simpa [coeff_smul_order_add_order]⟩

中文:
实例 instIsTorsionFree
  签名: {Γ V : 类型} [环 R] [是整环 R] [加法交换群 V] [加法交换幺半群 Γ]
  定义体: .of_smul_eq_zero fun x y hxy => by
    contrapose! hxy
    rw [ne_eq]; rw [HahnModule.ext_iff]; rw [funext_iff]; rw [not_forall]
    exact ⟨x.order + ((of R).symm y).order, by simpa [coeff_smul_order_add_order]⟩

Depends on / 依赖: HahnModule, HahnModule.ext_iff, coeff_smul_order_add_order, contrapose, ext_iff, funext_iff, ne_eq, not_forall, of_smul_eq_zero, x.order
-/
instance instIsTorsionFree {Γ V : Type*} [Ring R] [IsDomain R] [AddCommGroup V] [AddCommMonoid Γ]
    [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [Module R V] [Module.IsTorsionFree R V] :
    Module.IsTorsionFree R⟦Γ⟧ (HahnModule Γ R V) :=
  .of_smul_eq_zero fun x y hxy => by
    contrapose! hxy
    rw [ne_eq]; rw [HahnModule.ext_iff]; rw [funext_iff]; rw [not_forall]
    exact ⟨x.order + ((of R).symm y).order, by simpa [coeff_smul_order_add_order]⟩

end HahnModule

namespace HahnSeries

section PartialOrder
variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R]

@[simp]
/--
theorem `single_mul_single` / 定理 `single_mul_single`

English:
theorem single_mul_single
  given: {a b : Γ} {r s : R}
  proof: by
  ext x
  by_cases h : x = a + b
  · rw [h, coeff_mul_single_add]
    simp
  · rw [coeff_single_of_ne h, coeff_mul, sum_eq_zero]
    simp_rw [mem_antidiagonal]
    rintro ⟨y, z⟩ ⟨hy, hz, rfl⟩
    rw [eq_of_mem_support_single hy]; rw [eq_of_mem_support_single hz] at h
    exact (h rfl).elim

中文:
定理 single_mul_single
  条件: {a b : Γ} {r s : R}
  证明: by
  ext x
  by_cases h : x = a + b
  · rw [h, coeff_mul_single_add]
    simp
  · rw [coeff_single_of_ne h, coeff_mul, sum_eq_zero]
    simp_rw [mem_antidiagonal]
    rintro ⟨y, z⟩ ⟨hy, hz, rfl⟩
    rw [eq_of_mem_support_single hy]; rw [eq_of_mem_support_single hz] at h
    exact (h rfl).elim

Depends on / 依赖: coeff_mul, coeff_mul_single_add, coeff_single_of_ne, eq_of_mem_support_single, mem_antidiagonal, simp_rw, sum_eq_zero
-/
theorem single_mul_single {a b : Γ} {r s : R} :
    single a r * single b s = single (a + b) (r * s) := by
  ext x
  by_cases h : x = a + b
  · rw [h, coeff_mul_single_add]
    simp
  · rw [coeff_single_of_ne h, coeff_mul, sum_eq_zero]
    simp_rw [mem_antidiagonal]
    rintro ⟨y, z⟩ ⟨hy, hz, rfl⟩
    rw [eq_of_mem_support_single hy]; rw [eq_of_mem_support_single hz] at h
    exact (h rfl).elim

end NonUnitalNonAssocSemiring

section Semiring

variable [Semiring R]

@[simp]
/--
theorem `single_pow` / 定理 `single_pow`

English:
theorem single_pow
  given: (a : Γ) (n : Nat) (r : R)
  statement: single a r ^ n = single (n • a) (r ^ n)
  proof: by
  induction n with
  | zero => ext; simp only [pow_zero, coeff_one, zero_smul, coeff_single]
  | succ n IH => rw [pow_succ, pow_succ, IH, single_mul_single, succ_nsmul]

中文:
定理 single_pow
  条件: (a : Γ) (n : 自然数) (r : R)
  结论: single a r ^ n = single (n • a) (r ^ n)
  证明: by
  induction n with
  | zero => ext; simp only [pow_zero, coeff_one, zero_smul, coeff_single]
  | succ n IH => rw [pow_succ, pow_succ, IH, single_mul_single, succ_nsmul]

Depends on / 依赖: coeff_one, coeff_single, pow_succ, pow_zero, single_mul_single, succ_nsmul, zero_smul
-/
theorem single_pow (a : Γ) (n : Nat) (r : R) : single a r ^ n = single (n • a) (r ^ n) := by
  induction n with
  | zero => ext; simp only [pow_zero, coeff_one, zero_smul, coeff_single]
  | succ n IH => rw [pow_succ, pow_succ, IH, single_mul_single, succ_nsmul]

end Semiring

section NonAssocSemiring

variable [NonAssocSemiring R]

/-- `C a` is the constant Hahn Series `a`. `C` is provided as a ring homomorphism. -/
@[simps]
/--
Definition of `C` / `C` 的定义

English:
definition C
  signature: : R ->+* R⟦Γ⟧ where
  body: single 0
  map_zero' := single_eq_zero
  map_one' := rfl
  map_add' x y := by
    ext a
    by_cases h : a = 0 <;> simp [h]
  map_mul' x y := by rw [single_mul_single, zero_add]

中文:
定义 C
  签名: : R ->+* R⟦Γ⟧ where
  定义体: single 0
  map_zero' := single_eq_zero
  map_one' := rfl
  map_add' x y := by
    ext a
    by_cases h : a = 0 <;> simp [h]
  map_mul' x y := by rw [single_mul_single, zero_add]

Depends on / 依赖: single
-/
def C : R ->+* R⟦Γ⟧ where
  toFun := single 0
  map_zero' := single_eq_zero
  map_one' := rfl
  map_add' x y := by
    ext a
    by_cases h : a = 0 <;> simp [h]
  map_mul' x y := by rw [single_mul_single, zero_add]

/--
theorem `C_zero` / 定理 `C_zero`

English:
theorem C_zero
  statement: C (0 : R) = (0 : R⟦Γ⟧)
  proof: C.map_zero

中文:
定理 C_zero
  结论: C (0 : R) = (0 : R⟦Γ⟧)
  证明: C.map_zero

Depends on / 依赖: C.map_zero, map_zero
-/
theorem C_zero : C (0 : R) = (0 : R⟦Γ⟧) :=
  C.map_zero

/--
theorem `C_one` / 定理 `C_one`

English:
theorem C_one
  statement: C (1 : R) = (1 : R⟦Γ⟧)
  proof: C.map_one

中文:
定理 C_one
  结论: C (1 : R) = (1 : R⟦Γ⟧)
  证明: C.map_one

Depends on / 依赖: C.map_one, map_one
-/
theorem C_one : C (1 : R) = (1 : R⟦Γ⟧) :=
  C.map_one

/--
theorem `map_C` / 定理 `map_C`

English:
theorem map_C
  given: [NonAssocSemiring S] (a : R) (f : R ->+* S)
  proof: by
  ext g
  by_cases h : g = 0 <;> simp [h]

中文:
定理 map_C
  条件: [非结合半环 S] (a : R) (f : R ->+* S)
  证明: by
  ext g
  by_cases h : g = 0 <;> simp [h]
-/
theorem map_C [NonAssocSemiring S] (a : R) (f : R ->+* S) :
    ((C a).map f : S⟦Γ⟧) = C (f a) := by
  ext g
  by_cases h : g = 0 <;> simp [h]

/--
theorem `C_injective` / 定理 `C_injective`

English:
theorem C_injective
  statement: Function.Injective (C : R -> R⟦Γ⟧)
  proof: by
  intro r s rs
  rw [HahnSeries.ext_iff]; rw [funext_iff] at rs
  have h := rs 0
  rwa [C_apply, coeff_single_same, C_apply, coeff_single_same] at h

中文:
定理 C_injective
  结论: 函数.单射 (C : R -> R⟦Γ⟧)
  证明: by
  intro r s rs
  rw [HahnSeries.ext_iff]; rw [funext_iff] at rs
  have h := rs 0
  rwa [C_apply, coeff_single_same, C_apply, coeff_single_same] at h

Depends on / 依赖: C_apply, HahnSeries, HahnSeries.ext_iff, coeff_single_same, ext_iff, funext_iff
-/
theorem C_injective : Function.Injective (C : R -> R⟦Γ⟧) := by
  intro r s rs
  rw [HahnSeries.ext_iff]; rw [funext_iff] at rs
  have h := rs 0
  rwa [C_apply, coeff_single_same, C_apply, coeff_single_same] at h

/--
theorem `C_ne_zero` / 定理 `C_ne_zero`

English:
theorem C_ne_zero
  given: {r : R} (h : r != 0)
  statement: (C r : R⟦Γ⟧) != 0
  proof: .mpr h C_injective.ne_iff' C_zero

中文:
定理 C_ne_zero
  条件: {r : R} (h : r != 0)
  结论: (C r : R⟦Γ⟧) != 0
  证明: .mpr h C_injective.ne_iff' C_zero

Depends on / 依赖: C_injective, C_injective.ne_iff, C_zero, ne_iff
-/
theorem C_ne_zero {r : R} (h : r != 0) : (C r : R⟦Γ⟧) != 0 :=
.mpr h C_injective.ne_iff' C_zero

/--
theorem `order_C` / 定理 `order_C`

English:
theorem order_C
  given: {r : R}
  statement: order (C r : R⟦Γ⟧) = 0
  proof: by
  by_cases h : r = 0
  · rw [h, C_zero, order_zero]
  · exact order_single h

中文:
定理 order_C
  条件: {r : R}
  结论: order (C r : R⟦Γ⟧) = 0
  证明: by
  by_cases h : r = 0
  · rw [h, C_zero, order_zero]
  · exact order_single h

Depends on / 依赖: C_zero, order_single, order_zero
-/
theorem order_C {r : R} : order (C r : R⟦Γ⟧) = 0 := by
  by_cases h : r = 0
  · rw [h, C_zero, order_zero]
  · exact order_single h

end NonAssocSemiring

section Semiring

variable [Semiring R]

/--
theorem `C_mul_eq_smul` / 定理 `C_mul_eq_smul`

English:
theorem C_mul_eq_smul
  given: {r : R} {x : R⟦Γ⟧}
  statement: C r * x = r • x
  proof: single_zero_mul_eq_smul

中文:
定理 C_mul_eq_smul
  条件: {r : R} {x : R⟦Γ⟧}
  结论: C r * x = r • x
  证明: single_zero_mul_eq_smul

Depends on / 依赖: single_zero_mul_eq_smul
-/
theorem C_mul_eq_smul {r : R} {x : R⟦Γ⟧} : C r * x = r • x :=
  single_zero_mul_eq_smul

end Semiring

section Domain

variable {Γ' : Type*} [AddCommMonoid Γ'] [PartialOrder Γ'] [IsOrderedCancelAddMonoid Γ']

/--
theorem `embDomain_mul` / 定理 `embDomain_mul`

English:
theorem embDomain_mul
  statement: [NonUnitalNonAssocSemiring R] (f : Γ ↪o Γ')
  proof: by
  ext g
  by_cases hg : g in Set.range f
  · obtain ⟨g, rfl⟩ := hg
    simp only [coeff_mul, embDomain_coeff]
    trans
      ∑ ij in
        (antidiagonal x.isPWO_support y.isPWO_support g).map
          (f.toEmbedding.prodMap f.toEmbedding),
        (embDomain f x).coeff ij.1 * (embDomain f y).

中文:
定理 embDomain_mul
  结论: [非幺非结合半环 R] (f : Γ ↪o Γ')
  证明: by
  ext g
  by_cases hg : g in Set.range f
  · obtain ⟨g, rfl⟩ := hg
    simp only [coeff_mul, embDomain_coeff]
    trans
      ∑ ij in
        (antidiagonal x.isPWO_support y.isPWO_support g).map
          (f.toEmbedding.prodMap f.toEmbedding),
        (embDomain f x).coeff ij.1 * (embDomain f y).

Depends on / 依赖: Embedding, Function, Function.Embedding.coe_prodMap, Prod.exists, Set.range, antidiagonal, coe_prodMap, coeff_mul, embDomain, embDomain_coeff, f.toEmbedding, f.toEmbedding.prodMap, isPWO_support, mem_antidiagonal, mem_map, mem_support, prodMap, sum_subset, toEmbedding, x.isPWO_support
-/
theorem embDomain_mul [NonUnitalNonAssocSemiring R] (f : Γ ↪o Γ')
    (hf : forall x y, f (x + y) = f x + f y) (x y : R⟦Γ⟧) :
    embDomain f (x * y) = embDomain f x * embDomain f y := by
  ext g
  by_cases hg : g in Set.range f
  · obtain ⟨g, rfl⟩ := hg
    simp only [coeff_mul, embDomain_coeff]
    trans
      ∑ ij in
        (antidiagonal x.isPWO_support y.isPWO_support g).map
          (f.toEmbedding.prodMap f.toEmbedding),
        (embDomain f x).coeff ij.1 * (embDomain f y).coeff ij.2
    · simp
    apply sum_subset
    · rintro ⟨i, j⟩ hij
      simp only [mem_map, mem_antidiagonal,
        Function.Embedding.coe_prodMap, mem_support, Prod.exists] at hij
      obtain ⟨i, j, ⟨hx, hy, rfl⟩, rfl, rfl⟩ := hij
      simp [hx, hy, hf]
    · rintro ⟨_, _⟩ h1 h2
      contrapose! h2
      obtain ⟨i, _, rfl⟩ := support_embDomain_subset (ne_zero_and_ne_zero_of_mul h2).1
      obtain ⟨j, _, rfl⟩ := support_embDomain_subset (ne_zero_and_ne_zero_of_mul h2).2
      simp only [mem_map, mem_antidiagonal,
        Function.Embedding.coe_prodMap, mem_support, Prod.exists]
      simp only [mem_antidiagonal, embDomain_coeff, mem_support, ← hf,
        OrderEmbedding.eq_iff_eq] at h1
      exact ⟨i, j, h1, rfl⟩
  · rw [embDomain_of_notMem_range hg, eq_comm]
    contrapose! hg
    obtain ⟨_, hi, _, hj, rfl⟩ := support_mul_subset ((mem_support _ _).2 hg)
    obtain ⟨i, _, rfl⟩ := support_embDomain_subset hi
    obtain ⟨j, _, rfl⟩ := support_embDomain_subset hj
    exact ⟨i + j, hf i j⟩

omit [IsOrderedCancelAddMonoid Γ] [IsOrderedCancelAddMonoid Γ'] in
/--
theorem `embDomain_one` / 定理 `embDomain_one`

English:
theorem embDomain_one
  given: [NonAssocSemiring R] (f : Γ ↪o Γ') (hf : f 0 = 0)
  proof: embDomain_single.trans hf.symm ▸ rfl

中文:
定理 embDomain_one
  条件: [非结合半环 R] (f : Γ ↪o Γ') (hf : f 0 = 0)
  证明: embDomain_single.trans hf.symm ▸ rfl

Depends on / 依赖: embDomain_single, embDomain_single.trans, hf.symm
-/
theorem embDomain_one [NonAssocSemiring R] (f : Γ ↪o Γ') (hf : f 0 = 0) :
    embDomain f (1 : R⟦Γ⟧) = (1 : R⟦Γ'⟧) :=
embDomain_single.trans hf.symm ▸ rfl

/-- Extending the domain of Hahn series is a ring homomorphism. -/
@[simps]
/--
Definition of `embDomainRingHom` / `embDomainRingHom` 的定义

English:
definition embDomainRingHom
  signature: [NonAssocSemiring R] (f : Γ ->+ Γ') (hfi : Function.Injective f)
  body: embDomain ⟨⟨f, hfi⟩, hf _ _⟩
  map_one' := embDomain_one _ f.map_zero
  map_mul' := embDomain_mul _ f.map_add
  map_zero' := embDomain_zero
  map_add' := embDomain_add _

中文:
定义 embDomainRingHom
  签名: [非结合半环 R] (f : Γ ->+ Γ') (hfi : 函数.单射 f)
  定义体: embDomain ⟨⟨f, hfi⟩, hf _ _⟩
  map_one' := embDomain_one _ f.map_zero
  map_mul' := embDomain_mul _ f.map_add
  map_zero' := embDomain_zero
  map_add' := embDomain_add _

Depends on / 依赖: embDomain
-/
def embDomainRingHom [NonAssocSemiring R] (f : Γ ->+ Γ') (hfi : Function.Injective f)
    (hf : forall g g' : Γ, f g <= f g' ↔ g <= g') : R⟦Γ⟧ ->+* R⟦Γ'⟧ where
  toFun := embDomain ⟨⟨f, hfi⟩, hf _ _⟩
  map_one' := embDomain_one _ f.map_zero
  map_mul' := embDomain_mul _ f.map_add
  map_zero' := embDomain_zero
  map_add' := embDomain_add _

/--
theorem `embDomainRingHom_C` / 定理 `embDomainRingHom_C`

English:
theorem embDomainRingHom_C
  statement: [NonAssocSemiring R] {f : Γ ->+ Γ'} {hfi : Function.Injective f}
  proof: embDomain_single.trans (by simp)

中文:
定理 embDomainRingHom_C
  结论: [非结合半环 R] {f : Γ ->+ Γ'} {hfi : 函数.单射 f}
  证明: embDomain_single.trans (by simp)

Depends on / 依赖: embDomain_single, embDomain_single.trans
-/
theorem embDomainRingHom_C [NonAssocSemiring R] {f : Γ ->+ Γ'} {hfi : Function.Injective f}
    {hf : forall g g' : Γ, f g <= f g' ↔ g <= g'} {r : R} : embDomainRingHom f hfi hf (C r) = C r :=
  embDomain_single.trans (by simp)

end Domain

section Algebra

variable [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R A⟦Γ⟧
  body: C.comp (algebraMap R A)
  smul_def' r x := by
    ext
    simp
  commutes' r x := by
    ext
    simp only [coeff_smul, single_zero_mul_eq_smul, RingHom.coe_comp, C_apply,
      Function.comp_apply, algebraMap_smul, coeff_mul_single_zero]
    rw [← Algebra.commutes]; rw [Algebra.smul_def]

中文:
实例 :
  签名: 代数 R A⟦Γ⟧
  定义体: C.comp (algebraMap R A)
  smul_def' r x := by
    ext
    simp
  commutes' r x := by
    ext
    simp only [coeff_smul, single_zero_mul_eq_smul, RingHom.coe_comp, C_apply,
      Function.comp_apply, algebraMap_smul, coeff_mul_single_zero]
    rw [← Algebra.commutes]; rw [Algebra.smul_def]

Depends on / 依赖: C.comp, algebraMap
-/
instance : Algebra R A⟦Γ⟧ where
  algebraMap := C.comp (algebraMap R A)
  smul_def' r x := by
    ext
    simp
  commutes' r x := by
    ext
    simp only [coeff_smul, single_zero_mul_eq_smul, RingHom.coe_comp, C_apply,
      Function.comp_apply, algebraMap_smul, coeff_mul_single_zero]
    rw [← Algebra.commutes]; rw [Algebra.smul_def]

/--
theorem `C_eq_algebraMap` / 定理 `C_eq_algebraMap`

English:
theorem C_eq_algebraMap
  statement: C = algebraMap R R⟦Γ⟧
  proof: rfl

中文:
定理 C_eq_algebraMap
  结论: C = algebraMap R R⟦Γ⟧
  证明: rfl
-/
theorem C_eq_algebraMap : C = algebraMap R R⟦Γ⟧ :=
  rfl

/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: {r : R}
  statement: algebraMap R A⟦Γ⟧ r = C (algebraMap R A r)
  proof: rfl

中文:
定理 algebraMap_apply
  条件: {r : R}
  结论: algebraMap R A⟦Γ⟧ r = C (algebraMap R A r)
  证明: rfl
-/
theorem algebraMap_apply {r : R} : algebraMap R A⟦Γ⟧ r = C (algebraMap R A r) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: Γ] [Nontrivial R] : Nontrivial (Subalgebra R R⟦Γ⟧)
  body: ⟨⟨⊥, ⊤, by
      rw [Ne]; rw [SetLike.ext_iff]; rw [not_forall]
      obtain ⟨a, ha⟩ := exists_ne (0 : Γ)
      refine ⟨single a 1, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top]
      intro x
      rw [HahnSeries.ext_iff]; rw [funext_iff]; rw [not_forall

中文:
实例 [非平凡
  签名: Γ] [非平凡 R] : 非平凡 (子代数 R R⟦Γ⟧)
  定义体: ⟨⟨⊥, ⊤, by
      rw [Ne]; rw [SetLike.ext_iff]; rw [not_forall]
      obtain ⟨a, ha⟩ := exists_ne (0 : Γ)
      refine ⟨single a 1, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top]
      intro x
      rw [HahnSeries.ext_iff]; rw [funext_iff]; rw [not_forall

Depends on / 依赖: Algebra, Algebra.mem_bot, Algebra.mem_top, C_apply, HahnSeries, HahnSeries.ext_iff, Set.mem_range, SetLike, SetLike.ext_iff, algebraMap_apply, coeff_single_of_ne, coeff_single_same, exists_ne, ext_iff, funext_iff, iff_true, mem_bot, mem_range, mem_top, not_exists
-/
instance [Nontrivial Γ] [Nontrivial R] : Nontrivial (Subalgebra R R⟦Γ⟧) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne]; rw [SetLike.ext_iff]; rw [not_forall]
      obtain ⟨a, ha⟩ := exists_ne (0 : Γ)
      refine ⟨single a 1, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top]
      intro x
      rw [HahnSeries.ext_iff]; rw [funext_iff]; rw [not_forall]
      refine ⟨a, ?_⟩
      rw [coeff_single_same]; rw [algebraMap_apply]; rw [C_apply]; rw [coeff_single_of_ne ha]
      exact zero_ne_one⟩⟩

section Domain

variable {Γ' : Type*} [AddCommMonoid Γ'] [PartialOrder Γ'] [IsOrderedCancelAddMonoid Γ']

/-- Extending the domain of Hahn series is an algebra homomorphism. -/
@[simps!]
/--
Definition of `embDomainAlgHom` / `embDomainAlgHom` 的定义

English:
definition embDomainAlgHom
  signature: (f : Γ ->+ Γ') (hfi : Function.Injective f)
  body: { embDomainRingHom f hfi hf with commutes' := fun _ => embDomainRingHom_C (hf := hf) }

中文:
定义 embDomainAlgHom
  签名: (f : Γ ->+ Γ') (hfi : 函数.单射 f)
  定义体: { embDomainRingHom f hfi hf with commutes' := fun _ => embDomainRingHom_C (hf := hf) }

Depends on / 依赖: commutes, embDomainRingHom, embDomainRingHom_C
-/
def embDomainAlgHom (f : Γ ->+ Γ') (hfi : Function.Injective f)
    (hf : forall g g' : Γ, f g <= f g' ↔ g <= g') : A⟦Γ⟧ ->ₐ[R] A⟦Γ'⟧ :=
  { embDomainRingHom f hfi hf with commutes' := fun _ => embDomainRingHom_C (hf := hf) }

end Domain

end Algebra
end PartialOrder

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCancelAdd
  signature: R] [IsCancelMulZero R] : IsCancelMulZero R⟦Γ⟧ where
  body: by
    let : AddCancelCommMonoid R := ⟨⟩
    contrapose! hyz
    simp only [ne_eq, ← coeff_inj, funext_iff, not_forall] at ⊢ hyz
    have : Set.IsWF {a | y.coeff a != z.coeff a} :=
      .mono (y.isWF_support.union z.isWF_support) (by intro; simp; grind)
    let a : Γ := this.min hyz
    have ha : y

中文:
实例 [是消去加法
  签名: R] [是乘零消去 R] : 是乘零消去 R⟦Γ⟧ where
  定义体: by
    let : AddCancelCommMonoid R := ⟨⟩
    contrapose! hyz
    simp only [ne_eq, ← coeff_inj, funext_iff, not_forall] at ⊢ hyz
    have : Set.IsWF {a | y.coeff a != z.coeff a} :=
      .mono (y.isWF_support.union z.isWF_support) (by intro; simp; grind)
    let a : Γ := this.min hyz
    have ha : y

Depends on / 依赖: AddCancelCommMonoid, Set.IsWF, antidiagonal, coeff_inj, coeff_mul, contrapose, funext_iff, isWF_support, min_mem, mul_r, ne_eq, not_forall, subset_union_left, subset_union_right, sum_eq_sum_iff_single, sum_subset, this.min, this.min_mem, x.order, y.coeff
-/
instance [IsCancelAdd R] [IsCancelMulZero R] : IsCancelMulZero R⟦Γ⟧ where
  -- TODO: This proof is painful because `coeff_mul` isn't stated in terms of `Finsupp.sum`.
  mul_left_cancel_of_ne_zero {x} hx y z hyz := by
    let : AddCancelCommMonoid R := ⟨⟩
    contrapose! hyz
    simp only [ne_eq, ← coeff_inj, funext_iff, not_forall] at ⊢ hyz
    have : Set.IsWF {a | y.coeff a != z.coeff a} :=
      .mono (y.isWF_support.union z.isWF_support) (by intro; simp; grind)
    let a : Γ := this.min hyz
    have ha : y.coeff a != z.coeff a := this.min_mem hyz
    refine ⟨x.order + a, ?_⟩
    rwa [coeff_mul, coeff_mul, sum_subset subset_union_left,
      sum_subset (s₁ := antidiagonal _ _ _) subset_union_right,
      sum_eq_sum_iff_single (i := (x.order, a)), mul_right_inj' (coeff_order_eq_zero.not.2 hx)]
    · simp [hx]
      grind
    · simp +contextual only [mem_union, mem_antidiagonal, mul_eq_mul_left_iff, Prod.mk.injEq,
        ne_eq, ← and_or_left, ← or_and_right, or_false, and_imp, Prod.forall, mem_support, not_and]
      rintro b c hxb - hbc hbc'
      contrapose! hbc'
      rwa [eq_comm, eq_comm (a := c), ← add_eq_add_iff_eq_and_eq (order_le_of_coeff_ne_zero hxb)
        (Set.IsWF.min_le this hyz hbc'), eq_comm]
    · simp +contextual [← and_or_left, ← or_and_right]
    · simp +contextual [← and_or_left, ← or_and_right]
  mul_right_cancel_of_ne_zero {x} hx y z hyz := by
    let : AddCancelCommMonoid R := ⟨⟩
    contrapose! hyz
    simp only [ne_eq, ← coeff_inj, funext_iff, not_forall] at ⊢ hyz
    have : Set.IsWF {a | y.coeff a != z.coeff a} :=
      .mono (y.isWF_support.union z.isWF_support) (by intro; simp; grind)
    let a : Γ := this.min hyz
    have ha : y.coeff a != z.coeff a := this.min_mem hyz
    refine ⟨a + x.order, ?_⟩
    rwa [coeff_mul, coeff_mul, sum_subset subset_union_left,
      sum_subset (s₁ := antidiagonal _ _ _) subset_union_right,
      sum_eq_sum_iff_single (i := (a, x.order)), mul_left_inj' (coeff_order_eq_zero.not.2 hx)]
    · simp [hx]
      grind
    · simp +contextual only [mem_union, mem_antidiagonal, mul_eq_mul_right_iff, Prod.mk.injEq,
        ne_eq, ← or_and_right, or_false, and_imp, Prod.forall, mem_support, not_and]
      rintro b c - hxb hbc hbc'
      contrapose! hbc'
      rwa [eq_comm, eq_comm (a := c), ← add_eq_add_iff_eq_and_eq
        (Set.IsWF.min_le this hyz ((Set.mem_ofPred (p := fun a => y.coeff a != z.coeff a)).mpr hbc'))
        (order_le_of_coeff_ne_zero hxb), eq_comm]
    · simp +contextual [← or_and_right]
    · simp +contextual [← or_and_right]

variable [NoZeroDivisors R] {x y : R⟦Γ⟧}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoZeroDivisors R⟦Γ⟧
  body: by
    contrapose! hxy
    simp only [ne_eq, HahnSeries.ext_iff, funext_iff, not_forall]
    exact ⟨x.order + y.order, by simpa [coeff_mul_order_add_order]⟩

@[simp]

中文:
实例 :
  签名: 无零因子 R⟦Γ⟧
  定义体: by
    contrapose! hxy
    simp only [ne_eq, HahnSeries.ext_iff, funext_iff, not_forall]
    exact ⟨x.order + y.order, by simpa [coeff_mul_order_add_order]⟩

@[simp]

Depends on / 依赖: HahnSeries, HahnSeries.ext_iff, coeff_mul_order_add_order, contrapose, ext_iff, funext_iff, ne_eq, not_forall, x.order, y.order
-/
instance : NoZeroDivisors R⟦Γ⟧ where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} hxy := by
    contrapose! hxy
    simp only [ne_eq, HahnSeries.ext_iff, funext_iff, not_forall]
    exact ⟨x.order + y.order, by simpa [coeff_mul_order_add_order]⟩

@[simp]
/--
lemma `order_mul` / 引理 `order_mul`

English:
lemma order_mul
  given: (hx : x != 0) (hy : y != 0)
  statement: (x * y).order = x.order + y.order
  proof: by
  apply le_antisymm
  · apply order_le_of_coeff_ne_zero
    simp [coeff_mul_order_add_order x y, *]
  · rw [order_of_ne hx, order_of_ne hy, order_of_ne (mul_ne_zero hx hy), ← Set.IsWF.min_add]
    exact Set.IsWF.min_le_min_of_subset support_mul_subset

中文:
引理 order_mul
  条件: (hx : x != 0) (hy : y != 0)
  结论: (x * y).order = x.order + y.order
  证明: by
  apply le_antisymm
  · apply order_le_of_coeff_ne_zero
    simp [coeff_mul_order_add_order x y, *]
  · rw [order_of_ne hx, order_of_ne hy, order_of_ne (mul_ne_zero hx hy), ← Set.IsWF.min_add]
    exact Set.IsWF.min_le_min_of_subset support_mul_subset

Depends on / 依赖: Set.IsWF.min_add, Set.IsWF.min_le_min_of_subset, coeff_mul_order_add_order, le_antisymm, min_add, min_le_min_of_subset, mul_ne_zero, order_le_of_coeff_ne_zero, order_of_ne, support_mul_subset
-/
lemma order_mul (hx : x != 0) (hy : y != 0) : (x * y).order = x.order + y.order := by
  apply le_antisymm
  · apply order_le_of_coeff_ne_zero
    simp [coeff_mul_order_add_order x y, *]
  · rw [order_of_ne hx, order_of_ne hy, order_of_ne (mul_ne_zero hx hy), ← Set.IsWF.min_add]
    exact Set.IsWF.min_le_min_of_subset support_mul_subset

end NonUnitalNonAssocSemiring

section Semiring
variable [Semiring R]

/--
lemma `order_pow` / 引理 `order_pow`

English:
lemma order_pow
  given: [NoZeroDivisors R] (x : R⟦Γ⟧)
  statement: forall n, (x ^ n).order = n • x.order
  proof: eq_or_ne x 0 <;> simp [pow_succ, succ_nsmul, order_pow, pow_ne_zero, *]

中文:
引理 order_pow
  条件: [无零因子 R] (x : R⟦Γ⟧)
  结论: 对任意 n, (x ^ n).order = n • x.order
  证明: eq_or_ne x 0 <;> simp [pow_succ, succ_nsmul, order_pow, pow_ne_zero, *]
-/
@[simp] lemma order_pow [NoZeroDivisors R] (x : R⟦Γ⟧) : forall n, (x ^ n).order = n • x.order
  | 0 => by simp
  | n + 1 => by
    obtain rfl | hx := eq_or_ne x 0 <;> simp [pow_succ, succ_nsmul, order_pow, pow_ne_zero, *]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCancelAdd
  signature: R] [IsDomain R] : IsDomain R⟦Γ⟧ where

中文:
实例 [是消去加法
  签名: R] [是整环 R] : 是整环 R⟦Γ⟧ where
-/
instance [IsCancelAdd R] [IsDomain R] : IsDomain R⟦Γ⟧ where

end Semiring
end HahnSeries
