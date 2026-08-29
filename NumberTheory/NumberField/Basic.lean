/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.AddMonoidHom
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Number fields

This file defines a number field and the ring of integers corresponding to it.

## Main definitions
- `NumberField` defines a number field as a field which has characteristic zero and is finite
  dimensional over ℚ.
- `RingOfIntegers` defines the ring of integers (or number ring) corresponding to a number field
  as the integral closure of ℤ in the number field.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags
number field, ring of integers
-/

@[expose] public section

/-- A number field is a field which has characteristic zero and is finite
dimensional over ℚ. -/
@[stacks 09GA, wikidata Q616608]
/--
Definition of `NumberField` / `NumberField` 的定义

English:
class NumberField
  parameters: (K : Type*) [Field K]
  axioms and operations (2):
    - [to_charZero : CharZero K]
    - [to_finiteDimensional : FiniteDimensional Rat K]

中文:
类 数域
  参数: (K : 类型) [域 K]
  公理与运算 (2 个):
    - [to_charZero : 特征零 K]
    - [to_finiteDimensional : 有限维 有理数 K]
-/
class NumberField (K : Type*) [Field K] : Prop where
  [to_charZero : CharZero K]
  [to_finiteDimensional : FiniteDimensional Rat K]

open Function Module

open scoped nonZeroDivisors

namespace NumberField

variable (K L : Type*) [Field K] [Field L]

-- See note [lower instance priority]
attribute [instance] NumberField.to_charZero NumberField.to_finiteDimensional

/--
theorem `isAlgebraic` / 定理 `isAlgebraic`

English:
theorem isAlgebraic
  given: [NumberField K]
  statement: Algebra.IsAlgebraic Rat K
  proof: Algebra.IsAlgebraic.of_finite _ _

中文:
定理 isAlgebraic
  条件: [数域 K]
  结论: 代数.是代数 有理数 K
  证明: Algebra.IsAlgebraic.of_finite _ _
-/
protected theorem isAlgebraic [NumberField K] : Algebra.IsAlgebraic Rat K :=
  Algebra.IsAlgebraic.of_finite _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NumberField
  signature: K] [NumberField L] [Algebra K L] : FiniteDimensional K L
  body: Module.Finite.of_restrictScalars_finite Rat K L

中文:
实例 [数域
  签名: K] [数域 L] [代数 K L] : 有限维 K L
  定义体: Module.Finite.of_restrictScalars_finite Rat K L

Depends on / 依赖: Finite, Module, Module.Finite.of_restrictScalars_finite, of_restrictScalars_finite
-/
instance [NumberField K] [NumberField L] [Algebra K L] : FiniteDimensional K L :=
  Module.Finite.of_restrictScalars_finite Rat K L

/--
theorem `of_module_finite` / 定理 `of_module_finite`

English:
theorem of_module_finite
  given: [NumberField K] [Algebra K L] [Module.Finite K L]
  statement: NumberField L where
  proof: charZero_of_injective_algebraMap (algebraMap K L).injective
  to_finiteDimensional :=
    letI := charZero_of_injective_algebraMap (algebraMap K L).injective
    Module.Finite.trans K L

中文:
定理 of_module_finite
  条件: [数域 K] [代数 K L] [模.有限 K L]
  结论: 数域 L where
  证明: charZero_of_injective_algebraMap (algebraMap K L).injective
  to_finiteDimensional :=
    letI := charZero_of_injective_algebraMap (algebraMap K L).injective
    Module.Finite.trans K L

Depends on / 依赖: algebraMap, charZero_of_injective_algebraMap, injective
-/
theorem of_module_finite [NumberField K] [Algebra K L] [Module.Finite K L] : NumberField L where
  to_charZero := charZero_of_injective_algebraMap (algebraMap K L).injective
  to_finiteDimensional :=
    letI := charZero_of_injective_algebraMap (algebraMap K L).injective
    Module.Finite.trans K L

variable {K} {L} in
/--
Instance `of_intermediateField` / 实例 `of_intermediateField`

English:
instance of_intermediateField
  signature: [NumberField K] [NumberField L] [Algebra K L]
  body: of_module_finite K E

中文:
实例 of_intermediateField
  签名: [数域 K] [数域 L] [代数 K L]
  定义体: of_module_finite K E

Depends on / 依赖: of_module_finite
-/
instance of_intermediateField [NumberField K] [NumberField L] [Algebra K L]
    (E : IntermediateField K L) : NumberField E :=
  of_module_finite K E

variable {K} in
/--
Instance `of_subfield` / 实例 `of_subfield`

English:
instance of_subfield
  signature: [NumberField K] (E : Subfield K)
  body: FiniteDimensional.left Rat E K

中文:
实例 of_subfield
  签名: [数域 K] (E : 子域 K)
  定义体: FiniteDimensional.left Rat E K

Depends on / 依赖: FiniteDimensional, FiniteDimensional.left
-/
instance of_subfield [NumberField K] (E : Subfield K) : NumberField E where
  to_finiteDimensional := FiniteDimensional.left Rat E K

/--
theorem `of_tower` / 定理 `of_tower`

English:
theorem of_tower
  statement: [NumberField K] [NumberField L] [Algebra K L] (E : Type*) [Field E]
  proof: letI := Module.Finite.left K E L
  of_module_finite K E

中文:
定理 of_tower
  结论: [数域 K] [数域 L] [代数 K L] (E : 类型) [域 E]
  证明: letI := Module.Finite.left K E L
  of_module_finite K E

Depends on / 依赖: Finite, Module, Module.Finite.left, of_module_finite
-/
theorem of_tower [NumberField K] [NumberField L] [Algebra K L] (E : Type*) [Field E]
    [Algebra K E] [Algebra E L] [IsScalarTower K E L] : NumberField E :=
  letI := Module.Finite.left K E L
  of_module_finite K E

/--
theorem `of_ringEquiv` / 定理 `of_ringEquiv`

English:
theorem of_ringEquiv
  given: (e : K ≃+* L) [NumberField K]
  statement: NumberField L
  proof: letI := CharZero.of_addMonoidHom e.toAddMonoidHom (by simp) e.injective
  {
    to_charZero := inferInstance
    to_finiteDimensional := (SemilinearEquivClass.semilinearEquiv e : K ≃ₗ[Rat] L).finiteDimensional
  }

中文:
定理 of_ringEquiv
  条件: (e : K ≃+* L) [数域 K]
  结论: 数域 L
  证明: letI := CharZero.of_addMonoidHom e.toAddMonoidHom (by simp) e.injective
  {
    to_charZero := inferInstance
    to_finiteDimensional := (SemilinearEquivClass.semilinearEquiv e : K ≃ₗ[Rat] L).finiteDimensional
  }

Depends on / 依赖: CharZero, CharZero.of_addMonoidHom, SemilinearEquivClass, SemilinearEquivClass.semilinearEquiv, e.injective, e.toAddMonoidHom, finiteDimensional, injective, of_addMonoidHom, semilinearEquiv, toAddMonoidHom, to_charZero, to_finiteDimensional
-/
theorem of_ringEquiv (e : K ≃+* L) [NumberField K] : NumberField L :=
  letI := CharZero.of_addMonoidHom e.toAddMonoidHom (by simp) e.injective
  {
    to_charZero := inferInstance
    to_finiteDimensional := (SemilinearEquivClass.semilinearEquiv e : K ≃ₗ[Rat] L).finiteDimensional
  }

/-- The ring of integers (or number ring) corresponding to a number field
is the integral closure of ℤ in the number field.

This is defined as its own type, rather than a `Subalgebra`, for performance reasons:
looking for instances of the form `SMul (RingOfIntegers _) (RingOfIntegers _)` makes
much more effective use of the discrimination tree than instances of the form
`SMul (Subtype _) (Subtype _)`.
The drawback is we have to copy over instances manually.
-/
@[wikidata Q1358313]
/--
Definition of `RingOfIntegers` / `RingOfIntegers` 的定义

English:
definition RingOfIntegers
  signature: : Type _
  body: integralClosure Int K
deriving CommRing, IsDomain, Nontrivial

@[inherit_doc] scoped notation "𝓞" => NumberField.RingOfIntegers

中文:
定义 RingOf整数egers
  签名: : 类型 _
  定义体: integralClosure Int K
deriving CommRing, IsDomain, Nontrivial

@[inherit_doc] scoped notation "𝓞" => NumberField.RingOfIntegers

Depends on / 依赖: integralClosure
-/
def RingOfIntegers : Type _ :=
  integralClosure Int K
deriving CommRing, IsDomain, Nontrivial

@[inherit_doc] scoped notation "𝓞" => NumberField.RingOfIntegers

namespace RingOfIntegers

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NumberField
  signature: K] : CharZero (𝓞 K)
  body: inferInstanceAs (CharZero (integralClosure _ _))

中文:
实例 [数域
  签名: K] : 特征零 (𝓞 K)
  定义体: inferInstanceAs (CharZero (integralClosure _ _))

Depends on / 依赖: CharZero, integralClosure
-/
instance [NumberField K] : CharZero (𝓞 K) :=
  inferInstanceAs (CharZero (integralClosure _ _))

instance {L : Type*} [Ring L] [Algebra K L] : Algebra (𝓞 K) L :=
  inferInstanceAs (Algebra (integralClosure _ _) L)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra (𝓞 K) K
  body: inferInstanceAs _

中文:
实例 :
  签名: 代数 (𝓞 K) K
  定义体: inferInstanceAs _
-/
instance : Algebra (𝓞 K) K := inferInstanceAs _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTorsionFree (𝓞 K) K
  body: inferInstanceAs (IsTorsionFree (integralClosure _ _) _)

中文:
实例 :
  签名: 是无挠 (𝓞 K) K
  定义体: inferInstanceAs (IsTorsionFree (integralClosure _ _) _)

Depends on / 依赖: IsTorsionFree, integralClosure
-/
instance : IsTorsionFree (𝓞 K) K :=
  inferInstanceAs (IsTorsionFree (integralClosure _ _) _)


instance {L : Type*} [Ring L] [Algebra K L] : IsScalarTower (𝓞 K) K L :=
  inferInstanceAs (IsScalarTower (integralClosure _ _) K L)

instance {G : Type*} [Group G] [MulSemiringAction G K] : MulSemiringAction G (𝓞 K) :=
  inferInstanceAs (MulSemiringAction G (integralClosure Int K))

instance {G : Type*} [Group G] [MulSemiringAction G K] : SMulDistribClass G (𝓞 K) K :=
  inferInstanceAs (SMulDistribClass G (integralClosure Int K) K)

-- verify that the two algebra instances agree
example : instAlgebra (L := K) (K := K) = instAlgebra_1 (K := K) := by
  with_reducible_and_instances rfl

variable {K}

/-- The canonical coercion from `𝓞 K` to `K`. -/
@[coe]
/--
Definition of `val` / `val` 的定义

English:
abbreviation val
  signature: (x : 𝓞 K)
  body: algebraMap _ _ x

中文:
缩写 val
  签名: (x : 𝓞 K)
  定义体: algebraMap _ _ x

Depends on / 依赖: algebraMap
-/
abbrev val (x : 𝓞 K) : K := algebraMap _ _ x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeHead (𝓞 K) K
  body: ⟨val⟩

中文:
实例 :
  签名: CoeHead (𝓞 K) K
  定义体: ⟨val⟩
-/
instance : CoeHead (𝓞 K) K := ⟨val⟩

/--
lemma `coe_eq_algebraMap` / 引理 `coe_eq_algebraMap`

English:
lemma coe_eq_algebraMap
  given: (x : 𝓞 K)
  statement: (x : K) = algebraMap _ _ x
  proof: rfl

中文:
引理 coe_eq_algebraMap
  条件: (x : 𝓞 K)
  结论: (x : K) = algebraMap _ _ x
  证明: rfl
-/
lemma coe_eq_algebraMap (x : 𝓞 K) : (x : K) = algebraMap _ _ x := rfl

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {x y : 𝓞 K} (h : (x : K) = (y : K))
  statement: x = y
  proof: Subtype.ext h

@[norm_cast]

中文:
定理 ext
  条件: {x y : 𝓞 K} (h : (x : K) = (y : K))
  结论: x = y
  证明: Subtype.ext h

@[norm_cast]
-/
@[ext] theorem ext {x y : 𝓞 K} (h : (x : K) = (y : K)) : x = y :=
  Subtype.ext h

@[norm_cast]
/--
theorem `eq_iff` / 定理 `eq_iff`

English:
theorem eq_iff
  given: {x y : 𝓞 K}
  statement: (x : K) = (y : K) ↔ x = y
  proof: NumberField.RingOfIntegers.ext_iff.symm

中文:
定理 eq_iff
  条件: {x y : 𝓞 K}
  结论: (x : K) = (y : K) ↔ x = y
  证明: NumberField.RingOfIntegers.ext_iff.symm

Depends on / 依赖: NumberField, NumberField.RingOfIntegers.ext_iff.symm, RingOfIntegers, ext_iff
-/
theorem eq_iff {x y : 𝓞 K} : (x : K) = (y : K) ↔ x = y :=
  NumberField.RingOfIntegers.ext_iff.symm

/--
lemma `map_mk` / 引理 `map_mk`

English:
lemma map_mk
  given: (x : K) (hx)
  statement: algebraMap (𝓞 K) K ⟨x, hx⟩ = x
  proof: rfl

中文:
引理 map_mk
  条件: (x : K) (hx)
  结论: algebraMap (𝓞 K) K ⟨x, hx⟩ = x
  证明: rfl
-/
@[simp] lemma map_mk (x : K) (hx) : algebraMap (𝓞 K) K ⟨x, hx⟩ = x := rfl

/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: {x : K} (hx)
  statement: ((⟨x, hx⟩ : 𝓞 K) : K) = x
  proof: rfl

中文:
引理 coe_mk
  条件: {x : K} (hx)
  结论: ((⟨x, hx⟩ : 𝓞 K) : K) = x
  证明: rfl
-/
lemma coe_mk {x : K} (hx) : ((⟨x, hx⟩ : 𝓞 K) : K) = x := rfl

/--
lemma `mk_eq_mk` / 引理 `mk_eq_mk`

English:
lemma mk_eq_mk
  given: (x y : K) (hx hy)
  statement: (⟨x, hx⟩ : 𝓞 K) = ⟨y, hy⟩ ↔ x = y
  proof: by simp

中文:
引理 mk_eq_mk
  条件: (x y : K) (hx hy)
  结论: (⟨x, hx⟩ : 𝓞 K) = ⟨y, hy⟩ ↔ x = y
  证明: by simp
-/
lemma mk_eq_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) = ⟨y, hy⟩ ↔ x = y := by simp

/--
lemma `mk_one` / 引理 `mk_one`

English:
lemma mk_one
  statement: (⟨1, one_mem _⟩ : 𝓞 K) = 1
  proof: rfl

中文:
引理 mk_one
  结论: (⟨1, one_mem _⟩ : 𝓞 K) = 1
  证明: rfl
-/
@[simp] lemma mk_one : (⟨1, one_mem _⟩ : 𝓞 K) = 1 :=
  rfl

/--
lemma `mk_zero` / 引理 `mk_zero`

English:
lemma mk_zero
  statement: (⟨0, zero_mem _⟩ : 𝓞 K) = 0
  proof: rfl

中文:
引理 mk_zero
  结论: (⟨0, zero_mem _⟩ : 𝓞 K) = 0
  证明: rfl
-/
@[simp] lemma mk_zero : (⟨0, zero_mem _⟩ : 𝓞 K) = 0 :=
  rfl
-- TODO: these lemmas don't seem to fire?
/--
lemma `mk_add_mk` / 引理 `mk_add_mk`

English:
lemma mk_add_mk
  given: (x y : K) (hx hy)
  statement: (⟨x, hx⟩ : 𝓞 K) + ⟨y, hy⟩ = ⟨x + y, add_mem hx hy⟩
  proof: rfl

中文:
引理 mk_add_mk
  条件: (x y : K) (hx hy)
  结论: (⟨x, hx⟩ : 𝓞 K) + ⟨y, hy⟩ = ⟨x + y, add_mem hx hy⟩
  证明: rfl
-/
@[simp] lemma mk_add_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) + ⟨y, hy⟩ = ⟨x + y, add_mem hx hy⟩ :=
  rfl

/--
lemma `mk_mul_mk` / 引理 `mk_mul_mk`

English:
lemma mk_mul_mk
  given: (x y : K) (hx hy)
  statement: (⟨x, hx⟩ : 𝓞 K) * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩
  proof: rfl

中文:
引理 mk_mul_mk
  条件: (x y : K) (hx hy)
  结论: (⟨x, hx⟩ : 𝓞 K) * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩
  证明: rfl
-/
@[simp] lemma mk_mul_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩ :=
  rfl

/--
lemma `mk_sub_mk` / 引理 `mk_sub_mk`

English:
lemma mk_sub_mk
  given: (x y : K) (hx hy)
  statement: (⟨x, hx⟩ : 𝓞 K) - ⟨y, hy⟩ = ⟨x - y, sub_mem hx hy⟩
  proof: rfl

中文:
引理 mk_sub_mk
  条件: (x y : K) (hx hy)
  结论: (⟨x, hx⟩ : 𝓞 K) - ⟨y, hy⟩ = ⟨x - y, sub_mem hx hy⟩
  证明: rfl
-/
@[simp] lemma mk_sub_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) - ⟨y, hy⟩ = ⟨x - y, sub_mem hx hy⟩ :=
  rfl

/--
lemma `neg_mk` / 引理 `neg_mk`

English:
lemma neg_mk
  given: (x : K) (hx)
  statement: (-⟨x, hx⟩ : 𝓞 K) = ⟨-x, neg_mem hx⟩
  proof: rfl

中文:
引理 neg_mk
  条件: (x : K) (hx)
  结论: (-⟨x, hx⟩ : 𝓞 K) = ⟨-x, neg_mem hx⟩
  证明: rfl
-/
@[simp] lemma neg_mk (x : K) (hx) : (-⟨x, hx⟩ : 𝓞 K) = ⟨-x, neg_mem hx⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mapRingHom` / `mapRingHom` 的定义

English:
definition mapRingHom
  signature: {K L : Type*} [Field K] [Field L] (f : K ->+* L)
  body: ⟨f k.val, map_isIntegral_int f k.2⟩
  map_zero' := by ext; simp only [map_mk, map_zero]
  map_one' := by ext; simp only [map_mk, map_one]
  map_add' x y := by ext; simp only [map_mk, map_add]
  map_mul' x y := by ext; simp only [map_mk, map_mul]

@[simp]

中文:
定义 mapRingHom
  签名: {K L : 类型} [域 K] [域 L] (f : K ->+* L)
  定义体: ⟨f k.val, map_isIntegral_int f k.2⟩
  map_zero' := by ext; simp only [map_mk, map_zero]
  map_one' := by ext; simp only [map_mk, map_one]
  map_add' x y := by ext; simp only [map_mk, map_add]
  map_mul' x y := by ext; simp only [map_mk, map_mul]

@[simp]

Depends on / 依赖: k.val, map_isIntegral_int
-/
def mapRingHom {K L : Type*} [Field K] [Field L] (f : K ->+* L) : (𝓞 K) ->+* (𝓞 L) where
  toFun k := ⟨f k.val, map_isIntegral_int f k.2⟩
  map_zero' := by ext; simp only [map_mk, map_zero]
  map_one' := by ext; simp only [map_mk, map_one]
  map_add' x y := by ext; simp only [map_mk, map_add]
  map_mul' x y := by ext; simp only [map_mk, map_mul]

@[simp]
/--
theorem `mapRingHom_apply` / 定理 `mapRingHom_apply`

English:
theorem mapRingHom_apply
  given: {K L : Type*} [Field K] [Field L] (f : K ->+* L) (x : 𝓞 K)
  proof: rfl

中文:
定理 mapRingHom_apply
  条件: {K L : 类型} [域 K] [域 L] (f : K ->+* L) (x : 𝓞 K)
  证明: rfl
-/
theorem mapRingHom_apply {K L : Type*} [Field K] [Field L] (f : K ->+* L) (x : 𝓞 K) :
    (mapRingHom f x : L) = f (x : K) := rfl

/--
Definition of `mapRingEquiv` / `mapRingEquiv` 的定义

English:
definition mapRingEquiv
  signature: {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
  body: RingEquiv.ofRingHom (mapRingHom e) (mapRingHom e.symm)
    (RingHom.ext fun x => ext (EquivLike.right_inv e x.1))
      (RingHom.ext fun x => ext (EquivLike.left_inv e x.1))

@[simp]

中文:
定义 mapRingEquiv
  签名: {K L : 类型} [域 K] [域 L] (e : K ≃+* L)
  定义体: RingEquiv.ofRingHom (mapRingHom e) (mapRingHom e.symm)
    (RingHom.ext fun x => ext (EquivLike.right_inv e x.1))
      (RingHom.ext fun x => ext (EquivLike.left_inv e x.1))

@[simp]

Depends on / 依赖: EquivLike, EquivLike.left_inv, EquivLike.right_inv, RingEquiv, RingEquiv.ofRingHom, RingHom, RingHom.ext, e.symm, left_inv, mapRingHom, ofRingHom, right_inv
-/
def mapRingEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) : (𝓞 K) ≃+* (𝓞 L) :=
  RingEquiv.ofRingHom (mapRingHom e) (mapRingHom e.symm)
    (RingHom.ext fun x => ext (EquivLike.right_inv e x.1))
      (RingHom.ext fun x => ext (EquivLike.left_inv e x.1))

@[simp]
/--
theorem `mapRingEquiv_apply` / 定理 `mapRingEquiv_apply`

English:
theorem mapRingEquiv_apply
  given: {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (x : 𝓞 K)
  proof: rfl

@[simp]

中文:
定理 mapRingEquiv_apply
  条件: {K L : 类型} [域 K] [域 L] (e : K ≃+* L) (x : 𝓞 K)
  证明: rfl

@[simp]
-/
theorem mapRingEquiv_apply {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (x : 𝓞 K) :
    (mapRingEquiv e x : L) = e (x : K) := rfl

@[simp]
/--
theorem `mapRingEquiv_symm_apply` / 定理 `mapRingEquiv_symm_apply`

English:
theorem mapRingEquiv_symm_apply
  given: {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (x : 𝓞 L)
  proof: rfl

中文:
定理 mapRingEquiv_symm_apply
  条件: {K L : 类型} [域 K] [域 L] (e : K ≃+* L) (x : 𝓞 L)
  证明: rfl
-/
theorem mapRingEquiv_symm_apply {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (x : 𝓞 L) :
    ((mapRingEquiv e).symm x : K) = e.symm (x : L) := rfl

end RingOfIntegers

/--
Instance `inst_ringOfIntegersAlgebra` / 实例 `inst_ringOfIntegersAlgebra`

English:
instance inst_ringOfIntegersAlgebra
  signature: [Algebra K L]
  body: (RingOfIntegers.mapRingHom (algebraMap K L)).toAlgebra

中文:
实例 inst_ringOf整数egersAlgebra
  签名: [代数 K L]
  定义体: (RingOfIntegers.mapRingHom (algebraMap K L)).toAlgebra

Depends on / 依赖: RingOfIntegers, RingOfIntegers.mapRingHom, algebraMap, mapRingHom, toAlgebra
-/
instance inst_ringOfIntegersAlgebra [Algebra K L] : Algebra (𝓞 K) (𝓞 L) :=
  (RingOfIntegers.mapRingHom (algebraMap K L)).toAlgebra

-- diamond at `reducible_and_instances` https://github.com/leanprover-community/mathlib4/issues/10906
example : Algebra.id (𝓞 K) = inst_ringOfIntegersAlgebra K K := rfl

namespace RingOfIntegers

/--
Definition of `mapAlgHom` / `mapAlgHom` 的定义

English:
definition mapAlgHom
  signature: {k K L F : Type*} [Field k] [Field K] [Field L] [Algebra k K]
  body: mapRingHom f
  commutes' x := SetCoe.ext (AlgHomClass.commutes
    ((AlgHomClass.toAlgHom f).restrictScalars (𝓞 k)) x)

中文:
定义 mapAlgHom
  签名: {k K L F : 类型} [域 k] [域 K] [域 L] [代数 k K]
  定义体: mapRingHom f
  commutes' x := SetCoe.ext (AlgHomClass.commutes
    ((AlgHomClass.toAlgHom f).restrictScalars (𝓞 k)) x)

Depends on / 依赖: mapRingHom
-/
def mapAlgHom {k K L F : Type*} [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] [FunLike F K L] [AlgHomClass F k K L] (f : F) : (𝓞 K) ->ₐ[𝓞 k] (𝓞 L) where
  toRingHom := mapRingHom f
  commutes' x := SetCoe.ext (AlgHomClass.commutes
    ((AlgHomClass.toAlgHom f).restrictScalars (𝓞 k)) x)

/--
Definition of `mapAlgEquiv` / `mapAlgEquiv` 的定义

English:
definition mapAlgEquiv
  signature: {k K L E : Type*} [Field k] [Field K] [Field L] [Algebra k K]
  body: AlgEquiv.ofAlgHom (mapAlgHom e) (mapAlgHom (AlgEquivClass.toAlgEquiv e : K ≃ₐ[k] L).symm)
    (AlgHom.ext fun x => ext (EquivLike.right_inv e x.1))
      (AlgHom.ext fun x => ext (EquivLike.left_inv e x.1))

中文:
定义 mapAlgEquiv
  签名: {k K L E : 类型} [域 k] [域 K] [域 L] [代数 k K]
  定义体: AlgEquiv.ofAlgHom (mapAlgHom e) (mapAlgHom (AlgEquivClass.toAlgEquiv e : K ≃ₐ[k] L).symm)
    (AlgHom.ext fun x => ext (EquivLike.right_inv e x.1))
      (AlgHom.ext fun x => ext (EquivLike.left_inv e x.1))

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, AlgEquivClass, AlgEquivClass.toAlgEquiv, AlgHom, AlgHom.ext, EquivLike, EquivLike.left_inv, EquivLike.right_inv, left_inv, mapAlgHom, ofAlgHom, right_inv, toAlgEquiv
-/
def mapAlgEquiv {k K L E : Type*} [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] [EquivLike E K L] [AlgEquivClass E k K L] (e : E) : (𝓞 K) ≃ₐ[𝓞 k] (𝓞 L) :=
  AlgEquiv.ofAlgHom (mapAlgHom e) (mapAlgHom (AlgEquivClass.toAlgEquiv e : K ≃ₐ[k] L).symm)
    (AlgHom.ext fun x => ext (EquivLike.right_inv e x.1))
      (AlgHom.ext fun x => ext (EquivLike.left_inv e x.1))

/--
Instance `inst_isScalarTower` / 实例 `inst_isScalarTower`

English:
instance inst_isScalarTower
  signature: (k K L : Type*) [Field k] [Field K] [Field L]
  body: IsScalarTower.of_algHom (mapAlgHom (IsScalarTower.toAlgHom k K L))

中文:
实例 inst_isScalarTower
  签名: (k K L : 类型) [域 k] [域 K] [域 L]
  定义体: IsScalarTower.of_algHom (mapAlgHom (IsScalarTower.toAlgHom k K L))

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algHom, IsScalarTower.toAlgHom, mapAlgHom, of_algHom, toAlgHom
-/
instance inst_isScalarTower (k K L : Type*) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] :
    IsScalarTower (𝓞 k) (𝓞 K) (𝓞 L) :=
  IsScalarTower.of_algHom (mapAlgHom (IsScalarTower.toAlgHom k K L))

variable {K}

/--
lemma `coe_injective` / 引理 `coe_injective`

English:
lemma coe_injective
  statement: Function.Injective (algebraMap (𝓞 K) K)
  proof: FaithfulSMul.algebraMap_injective _ _

中文:
引理 coe_injective
  结论: 函数.单射 (algebraMap (𝓞 K) K)
  证明: FaithfulSMul.algebraMap_injective _ _

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective
-/
lemma coe_injective : Function.Injective (algebraMap (𝓞 K) K) :=
  FaithfulSMul.algebraMap_injective _ _

/--
lemma `coe_eq_zero_iff` / 引理 `coe_eq_zero_iff`

English:
lemma coe_eq_zero_iff
  given: {x : 𝓞 K}
  statement: algebraMap _ K x = 0 ↔ x = 0
  proof: map_eq_zero_iff _ coe_injective

中文:
引理 coe_eq_zero_iff
  条件: {x : 𝓞 K}
  结论: algebraMap _ K x = 0 ↔ x = 0
  证明: map_eq_zero_iff _ coe_injective

Depends on / 依赖: coe_injective, map_eq_zero_iff
-/
lemma coe_eq_zero_iff {x : 𝓞 K} : algebraMap _ K x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ coe_injective

/--
lemma `coe_ne_zero_iff` / 引理 `coe_ne_zero_iff`

English:
lemma coe_ne_zero_iff
  given: {x : 𝓞 K}
  statement: algebraMap _ K x != 0 ↔ x != 0
  proof: map_ne_zero_iff _ coe_injective

中文:
引理 coe_ne_zero_iff
  条件: {x : 𝓞 K}
  结论: algebraMap _ K x != 0 ↔ x != 0
  证明: map_ne_zero_iff _ coe_injective

Depends on / 依赖: coe_injective, map_ne_zero_iff
-/
lemma coe_ne_zero_iff {x : 𝓞 K} : algebraMap _ K x != 0 ↔ x != 0 :=
  map_ne_zero_iff _ coe_injective

/--
theorem `minpoly_coe` / 定理 `minpoly_coe`

English:
theorem minpoly_coe
  given: (x : 𝓞 K)
  proof: minpoly.algebraMap_eq RingOfIntegers.coe_injective x

中文:
定理 minpoly_coe
  条件: (x : 𝓞 K)
  证明: minpoly.algebraMap_eq RingOfIntegers.coe_injective x

Depends on / 依赖: RingOfIntegers, RingOfIntegers.coe_injective, algebraMap_eq, coe_injective, minpoly, minpoly.algebraMap_eq
-/
theorem minpoly_coe (x : 𝓞 K) :
    minpoly Int (x : K) = minpoly Int x :=
  minpoly.algebraMap_eq RingOfIntegers.coe_injective x

/--
theorem `isIntegral_coe` / 定理 `isIntegral_coe`

English:
theorem isIntegral_coe
  given: (x : 𝓞 K)
  statement: IsIntegral Int (algebraMap _ K x)
  proof: x.2

中文:
定理 is整数egral_coe
  条件: (x : 𝓞 K)
  结论: 是整 整数 (algebraMap _ K x)
  证明: x.2
-/
theorem isIntegral_coe (x : 𝓞 K) : IsIntegral Int (algebraMap _ K x) :=
  x.2

/--
theorem `isIntegral` / 定理 `isIntegral`

English:
theorem isIntegral
  given: (x : 𝓞 K)
  statement: IsIntegral Int x
  proof: by
  obtain ⟨P, hPm, hP⟩ := x.isIntegral_coe
  refine ⟨P, hPm, ?_⟩
  rwa [IsScalarTower.algebraMap_eq (S := 𝓞 K), ← Polynomial.hom_eval₂, coe_eq_zero_iff] at hP

中文:
定理 is整数egral
  条件: (x : 𝓞 K)
  结论: 是整 整数 x
  证明: by
  obtain ⟨P, hPm, hP⟩ := x.isIntegral_coe
  refine ⟨P, hPm, ?_⟩
  rwa [IsScalarTower.algebraMap_eq (S := 𝓞 K), ← Polynomial.hom_eval₂, coe_eq_zero_iff] at hP

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, Polynomial, Polynomial.hom_eval, algebraMap_eq, coe_eq_zero_iff, isIntegral_coe, x.isIntegral_coe
-/
theorem isIntegral (x : 𝓞 K) : IsIntegral Int x := by
  obtain ⟨P, hPm, hP⟩ := x.isIntegral_coe
  refine ⟨P, hPm, ?_⟩
  rwa [IsScalarTower.algebraMap_eq (S := 𝓞 K), ← Polynomial.hom_eval₂, coe_eq_zero_iff] at hP

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NumberField
  signature: K] : IsFractionRing (𝓞 K) K
  body: integralClosure.isFractionRing_of_finite_extension Rat _

中文:
实例 [数域
  签名: K] : IsFractionRing (𝓞 K) K
  定义体: integralClosure.isFractionRing_of_finite_extension Rat _

Depends on / 依赖: integralClosure, integralClosure.isFractionRing_of_finite_extension, isFractionRing_of_finite_extension
-/
instance [NumberField K] : IsFractionRing (𝓞 K) K :=
  integralClosure.isFractionRing_of_finite_extension Rat _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIntegralClosure (𝓞 K) Int K
  body: integralClosure.isIntegralClosure _ _

中文:
实例 :
  签名: 是整闭包 (𝓞 K) 整数 K
  定义体: integralClosure.isIntegralClosure _ _

Depends on / 依赖: integralClosure, integralClosure.isIntegralClosure, isIntegralClosure
-/
instance : IsIntegralClosure (𝓞 K) Int K :=
  integralClosure.isIntegralClosure _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.IsIntegral Int (𝓞 K)
  body: IsIntegralClosure.isIntegral_algebra Int K

中文:
实例 :
  签名: 代数.是整 整数 (𝓞 K)
  定义体: IsIntegralClosure.isIntegral_algebra Int K

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isIntegral_algebra, isIntegral_algebra
-/
instance : Algebra.IsIntegral Int (𝓞 K) :=
  IsIntegralClosure.isIntegral_algebra Int K

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NumberField
  signature: K] : IsIntegrallyClosed (𝓞 K)
  body: integralClosure.isIntegrallyClosedOfFiniteExtension Rat

中文:
实例 [数域
  签名: K] : 是整闭 (𝓞 K)
  定义体: integralClosure.isIntegrallyClosedOfFiniteExtension Rat

Depends on / 依赖: integralClosure, integralClosure.isIntegrallyClosedOfFiniteExtension, isIntegrallyClosedOfFiniteExtension
-/
instance [NumberField K] : IsIntegrallyClosed (𝓞 K) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension Rat

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def equiv (R : Type*) [CommRing R] [Algebra R K]
  body: (IsIntegralClosure.equiv Int R K _).symm.toRingEquiv

中文:
定义 noncomputable
  签名: def equiv (R : 类型) [交换环 R] [代数 R K]
  定义体: (IsIntegralClosure.equiv Int R K _).symm.toRingEquiv
-/
protected noncomputable def equiv (R : Type*) [CommRing R] [Algebra R K]
    [IsIntegralClosure R Int K] : 𝓞 K ≃+* R :=
  (IsIntegralClosure.equiv Int R K _).symm.toRingEquiv

variable (K)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CharZero
  signature: K] : CharZero (𝓞 K)
  body: .of_module K

中文:
实例 [特征零
  签名: K] : 特征零 (𝓞 K)
  定义体: .of_module K

Depends on / 依赖: of_module
-/
instance [CharZero K] : CharZero (𝓞 K) := .of_module K

variable [NumberField K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNoetherian Int (𝓞 K)
  body: IsIntegralClosure.isNoetherian _ Rat K _

中文:
实例 :
  签名: 是Noether 整数 (𝓞 K)
  定义体: IsIntegralClosure.isNoetherian _ Rat K _

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isNoetherian, isNoetherian
-/
instance : IsNoetherian Int (𝓞 K) :=
  IsIntegralClosure.isNoetherian _ Rat K _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddGroup.FG (𝓞 K)
  body: Finite.iff_addGroup_fg.mp IsNoetherian.finite Int (𝓞 K)

中文:
实例 :
  签名: 加法群.FG (𝓞 K)
  定义体: Finite.iff_addGroup_fg.mp IsNoetherian.finite Int (𝓞 K)

Depends on / 依赖: Finite, Finite.iff_addGroup_fg.mp, IsNoetherian, IsNoetherian.finite, finite, iff_addGroup_fg
-/
instance : AddGroup.FG (𝓞 K) :=
Finite.iff_addGroup_fg.mp IsNoetherian.finite Int (𝓞 K)

/--
theorem `not_isField` / 定理 `not_isField`

English:
theorem not_isField
  statement: ¬IsField (𝓞 K)
  proof: by
  have h_inj : Function.Injective (algebraMap Int (𝓞 K)) := RingHom.injective_int (algebraMap Int (𝓞 K))
  intro hf
  exact Int.not_isField
    (((IsIntegralClosure.isIntegral_algebra Int K).isField_iff_isField h_inj).mpr hf)

中文:
定理 not_isField
  结论: ¬是域 (𝓞 K)
  证明: by
  have h_inj : Function.Injective (algebraMap Int (𝓞 K)) := RingHom.injective_int (algebraMap Int (𝓞 K))
  intro hf
  exact Int.not_isField
    (((IsIntegralClosure.isIntegral_algebra Int K).isField_iff_isField h_inj).mpr hf)

Depends on / 依赖: Function, Function.Injective, Injective, Int.not_isField, IsIntegralClosure, IsIntegralClosure.isIntegral_algebra, RingHom, RingHom.injective_int, algebraMap, h_inj, injective_int, isField_iff_isField, isIntegral_algebra, not_isField
-/
theorem not_isField : ¬IsField (𝓞 K) := by
  have h_inj : Function.Injective (algebraMap Int (𝓞 K)) := RingHom.injective_int (algebraMap Int (𝓞 K))
  intro hf
  exact Int.not_isField
    (((IsIntegralClosure.isIntegral_algebra Int K).isField_iff_isField h_inj).mpr hf)

instance {I : Ideal (𝓞 K)} [hI : I.IsMaximal] : NeZero I :=
⟨Ring.ne_bot_of_isMaximal_of_not_isField hI RingOfIntegers.not_isField K⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDedekindDomain (𝓞 K)
  body: IsIntegralClosure.isDedekindDomain Int Rat K _

中文:
实例 :
  签名: 是Dedekind整环 (𝓞 K)
  定义体: IsIntegralClosure.isDedekindDomain Int Rat K _

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isDedekindDomain, isDedekindDomain
-/
instance : IsDedekindDomain (𝓞 K) :=
  IsIntegralClosure.isDedekindDomain Int Rat K _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Free Int (𝓞 K)
  body: IsIntegralClosure.module_free Int Rat K (𝓞 K)

中文:
实例 :
  签名: 自由 整数 (𝓞 K)
  定义体: IsIntegralClosure.module_free Int Rat K (𝓞 K)

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.module_free, module_free
-/
instance : Free Int (𝓞 K) :=
  IsIntegralClosure.module_free Int Rat K (𝓞 K)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K) Int⁰) K
  body: IsIntegralClosure.isLocalization_of_isSeparable Int Rat K (𝓞 K)

中文:
实例 :
  签名: 是Localization (代数.algebraMapSubmonoid (𝓞 K) 整数⁰) K
  定义体: IsIntegralClosure.isLocalization_of_isSeparable Int Rat K (𝓞 K)

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isLocalization_of_isSeparable, isLocalization_of_isSeparable
-/
instance : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K) Int⁰) K :=
  IsIntegralClosure.isLocalization_of_isSeparable Int Rat K (𝓞 K)

/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: : Basis (Free.ChooseBasisIndex Int (𝓞 K)) Int (𝓞 K)
  body: Free.chooseBasis Int (𝓞 K)

中文:
定义 basis
  签名: : 基 (自由.ChooseBasisIndex 整数 (𝓞 K)) 整数 (𝓞 K)
  定义体: Free.chooseBasis Int (𝓞 K)

Depends on / 依赖: Free.chooseBasis, chooseBasis
-/
noncomputable def basis : Basis (Free.ChooseBasisIndex Int (𝓞 K)) Int (𝓞 K) :=
  Free.chooseBasis Int (𝓞 K)

variable {K} {M : Type*}

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (f : M -> K) (h : forall x, IsIntegral Int (f x)) (x : M)
  body: ⟨f x, h x⟩

中文:
定义 restrict
  签名: (f : M -> K) (h : 对任意 x, 是整 整数 (f x)) (x : M)
  定义体: ⟨f x, h x⟩
-/
def restrict (f : M -> K) (h : forall x, IsIntegral Int (f x)) (x : M) : 𝓞 K :=
  ⟨f x, h x⟩

/--
Definition of `restrict_addMonoidHom` / `restrict_addMonoidHom` 的定义

English:
definition restrict_addMonoidHom
  signature: [AddZeroClass M] (f : M ->+ K) (h : forall x, IsIntegral Int (f x))
  body: restrict f h
  map_zero' := by simp only [restrict, map_zero]; rfl
  map_add' x y := by simp only [restrict, map_add]; rfl

中文:
定义 restrict_addMonoidHom
  签名: [加法零类 M] (f : M ->+ K) (h : 对任意 x, 是整 整数 (f x))
  定义体: restrict f h
  map_zero' := by simp only [restrict, map_zero]; rfl
  map_add' x y := by simp only [restrict, map_add]; rfl

Depends on / 依赖: restrict
-/
def restrict_addMonoidHom [AddZeroClass M] (f : M ->+ K) (h : forall x, IsIntegral Int (f x)) :
    M ->+ 𝓞 K where
  toFun := restrict f h
  map_zero' := by simp only [restrict, map_zero]; rfl
  map_add' x y := by simp only [restrict, map_add]; rfl

/--
Definition of `restrict_monoidHom` / `restrict_monoidHom` 的定义

English:
definition restrict_monoidHom
  signature: [MulOneClass M] (f : M ->* K) (h : forall x, IsIntegral Int (f x))
  body: restrict f h
  map_one' := by simp only [restrict, map_one]; rfl
  map_mul' x y := by simp only [restrict, map_mul]; rfl

中文:
定义 restrict_monoidHom
  签名: [MulOne类 M] (f : M ->* K) (h : 对任意 x, 是整 整数 (f x))
  定义体: restrict f h
  map_one' := by simp only [restrict, map_one]; rfl
  map_mul' x y := by simp only [restrict, map_mul]; rfl

Depends on / 依赖: restrict
-/
def restrict_monoidHom [MulOneClass M] (f : M ->* K) (h : forall x, IsIntegral Int (f x)) : M ->* 𝓞 K where
  toFun := restrict f h
  map_one' := by simp only [restrict, map_one]; rfl
  map_mul' x y := by simp only [restrict, map_mul]; rfl

section extension

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower (𝓞 K) (𝓞 L) L
  body: IsScalarTower.of_algebraMap_eq' rfl

中文:
实例 :
  签名: 标量塔 (𝓞 K) (𝓞 L) L
  定义体: IsScalarTower.of_algebraMap_eq' rfl

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, of_algebraMap_eq
-/
instance : IsScalarTower (𝓞 K) (𝓞 L) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIntegralClosure (𝓞 L) (𝓞 K) L
  body: IsIntegralClosure.tower_top (R := Int)

中文:
实例 :
  签名: 是整闭包 (𝓞 L) (𝓞 K) L
  定义体: IsIntegralClosure.tower_top (R := Int)

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.tower_top, tower_top
-/
instance : IsIntegralClosure (𝓞 L) (𝓞 K) L :=
  IsIntegralClosure.tower_top (R := Int)

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def algEquiv (R : Type*) [CommRing R] [Algebra (𝓞 K) R] [Algebra R L]
  body: (IsIntegralClosure.equiv (𝓞 K) R L _).symm

中文:
定义 noncomputable
  签名: def algEquiv (R : 类型) [交换环 R] [代数 (𝓞 K) R] [代数 R L]
  定义体: (IsIntegralClosure.equiv (𝓞 K) R L _).symm
-/
protected noncomputable def algEquiv (R : Type*) [CommRing R] [Algebra (𝓞 K) R] [Algebra R L]
    [IsScalarTower (𝓞 K) R L] [IsIntegralClosure R (𝓞 K) L] : 𝓞 L ≃ₐ[𝓞 K] R :=
  (IsIntegralClosure.equiv (𝓞 K) R L _).symm

/--
Instance `extension_algebra_isIntegral` / 实例 `extension_algebra_isIntegral`

English:
instance extension_algebra_isIntegral
  signature: : Algebra.IsIntegral (𝓞 K) (𝓞 L)
  body: IsIntegralClosure.isIntegral_algebra (𝓞 K) L

中文:
实例 extension_algebra_is整数egral
  签名: : 代数.是整 (𝓞 K) (𝓞 L)
  定义体: IsIntegralClosure.isIntegral_algebra (𝓞 K) L

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isIntegral_algebra, isIntegral_algebra
-/
instance extension_algebra_isIntegral : Algebra.IsIntegral (𝓞 K) (𝓞 L) :=
  IsIntegralClosure.isIntegral_algebra (𝓞 K) L

/--
Instance `extension_isNoetherian` / 实例 `extension_isNoetherian`

English:
instance extension_isNoetherian
  signature: [NumberField K] [NumberField L]
  body: IsIntegralClosure.isNoetherian (𝓞 K) K L (𝓞 L)

中文:
实例 extension_isNoetherian
  签名: [数域 K] [数域 L]
  定义体: IsIntegralClosure.isNoetherian (𝓞 K) K L (𝓞 L)

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isNoetherian, isNoetherian
-/
instance extension_isNoetherian [NumberField K] [NumberField L] : IsNoetherian (𝓞 K) (𝓞 L) :=
  IsIntegralClosure.isNoetherian (𝓞 K) K L (𝓞 L)

/--
theorem `ker_algebraMap_eq_bot` / 定理 `ker_algebraMap_eq_bot`

English:
theorem ker_algebraMap_eq_bot
  statement: RingHom.ker (algebraMap (𝓞 K) (𝓞 L)) = ⊥
  proof: (RingHom.ker_eq_bot_iff_eq_zero (algebraMap (𝓞 K) (𝓞 L))).mpr fun x hx => by
  have h : (algebraMap K L) x = (algebraMap (𝓞 K) (𝓞 L)) x := rfl
  simp only [hx, map_zero, map_eq_zero, RingOfIntegers.coe_eq_zero_iff] at h
  exact h

中文:
定理 ker_algebraMap_eq_bot
  结论: 环态射.ker (algebraMap (𝓞 K) (𝓞 L)) = ⊥
  证明: (RingHom.ker_eq_bot_iff_eq_zero (algebraMap (𝓞 K) (𝓞 L))).mpr fun x hx => by
  have h : (algebraMap K L) x = (algebraMap (𝓞 K) (𝓞 L)) x := rfl
  simp only [hx, map_zero, map_eq_zero, RingOfIntegers.coe_eq_zero_iff] at h
  exact h

Depends on / 依赖: RingHom, RingHom.ker_eq_bot_iff_eq_zero, RingOfIntegers, RingOfIntegers.coe_eq_zero_iff, algebraMap, coe_eq_zero_iff, ker_eq_bot_iff_eq_zero, map_eq_zero, map_zero
-/
theorem ker_algebraMap_eq_bot : RingHom.ker (algebraMap (𝓞 K) (𝓞 L)) = ⊥ :=
(RingHom.ker_eq_bot_iff_eq_zero (algebraMap (𝓞 K) (𝓞 L))).mpr fun x hx => by
  have h : (algebraMap K L) x = (algebraMap (𝓞 K) (𝓞 L)) x := rfl
  simp only [hx, map_zero, map_eq_zero, RingOfIntegers.coe_eq_zero_iff] at h
  exact h

/--
theorem `algebraMap.injective` / 定理 `algebraMap.injective`

English:
theorem algebraMap.injective
  statement: Function.Injective (algebraMap (𝓞 K) (𝓞 L))
  proof: (RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 K) (𝓞 L))).mpr (ker_algebraMap_eq_bot K L)

中文:
定理 algebraMap.injective
  结论: 函数.单射 (algebraMap (𝓞 K) (𝓞 L))
  证明: (RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 K) (𝓞 L))).mpr (ker_algebraMap_eq_bot K L)

Depends on / 依赖: RingHom, RingHom.injective_iff_ker_eq_bot, algebraMap, injective_iff_ker_eq_bot, ker_algebraMap_eq_bot
-/
theorem algebraMap.injective : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
  (RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 K) (𝓞 L))).mpr (ker_algebraMap_eq_bot K L)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTorsionFree (𝓞 K) (𝓞 L)
  body: isTorsionFree_iff_algebraMap_injective.mpr algebraMap.injective K L

中文:
实例 :
  签名: 是无挠 (𝓞 K) (𝓞 L)
  定义体: isTorsionFree_iff_algebraMap_injective.mpr algebraMap.injective K L

Depends on / 依赖: algebraMap, algebraMap.injective, injective, isTorsionFree_iff_algebraMap_injective, isTorsionFree_iff_algebraMap_injective.mpr
-/
instance : IsTorsionFree (𝓞 K) (𝓞 L) :=
isTorsionFree_iff_algebraMap_injective.mpr algebraMap.injective K L

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTorsionFree (𝓞 K) L
  body: .trans_faithfulSMul (𝓞 K) (𝓞 L) L

中文:
实例 :
  签名: 是无挠 (𝓞 K) L
  定义体: .trans_faithfulSMul (𝓞 K) (𝓞 L) L

Depends on / 依赖: trans_faithfulSMul
-/
instance : IsTorsionFree (𝓞 K) L := .trans_faithfulSMul (𝓞 K) (𝓞 L) L

end extension

end RingOfIntegers

variable [NumberField K]

/--
Definition of `integralBasis` / `integralBasis` 的定义

English:
definition integralBasis
  signature: : Basis (Free.ChooseBasisIndex Int (𝓞 K)) Rat K
  body: Basis.localizationLocalization Rat (nonZeroDivisors Int) K (RingOfIntegers.basis K)

@[simp]

中文:
定义 integralBasis
  签名: : 基 (自由.ChooseBasisIndex 整数 (𝓞 K)) 有理数 K
  定义体: Basis.localizationLocalization Rat (nonZeroDivisors Int) K (RingOfIntegers.basis K)

@[simp]

Depends on / 依赖: Basis.localizationLocalization, RingOfIntegers, RingOfIntegers.basis, localizationLocalization, nonZeroDivisors
-/
noncomputable def integralBasis : Basis (Free.ChooseBasisIndex Int (𝓞 K)) Rat K :=
  Basis.localizationLocalization Rat (nonZeroDivisors Int) K (RingOfIntegers.basis K)

@[simp]
/--
theorem `integralBasis_apply` / 定理 `integralBasis_apply`

English:
theorem integralBasis_apply
  given: (i : Free.ChooseBasisIndex Int (𝓞 K))
  proof: Basis.localizationLocalization_apply Rat (nonZeroDivisors Int) K (RingOfIntegers.basis K) i

@[simp]

中文:
定理 integralBasis_apply
  条件: (i : 自由.ChooseBasisIndex 整数 (𝓞 K))
  证明: Basis.localizationLocalization_apply Rat (nonZeroDivisors Int) K (RingOfIntegers.basis K) i

@[simp]

Depends on / 依赖: Basis.localizationLocalization_apply, RingOfIntegers, RingOfIntegers.basis, localizationLocalization_apply, nonZeroDivisors
-/
theorem integralBasis_apply (i : Free.ChooseBasisIndex Int (𝓞 K)) :
    integralBasis K i = algebraMap (𝓞 K) K (RingOfIntegers.basis K i) :=
  Basis.localizationLocalization_apply Rat (nonZeroDivisors Int) K (RingOfIntegers.basis K) i

@[simp]
/--
theorem `integralBasis_repr_apply` / 定理 `integralBasis_repr_apply`

English:
theorem integralBasis_repr_apply
  given: (x : (𝓞 K)) (i : Free.ChooseBasisIndex Int (𝓞 K))
  proof: Basis.localizationLocalization_repr_algebraMap Rat (nonZeroDivisors Int) K _ x i

中文:
定理 integralBasis_repr_apply
  条件: (x : (𝓞 K)) (i : 自由.ChooseBasisIndex 整数 (𝓞 K))
  证明: Basis.localizationLocalization_repr_algebraMap Rat (nonZeroDivisors Int) K _ x i

Depends on / 依赖: Basis.localizationLocalization_repr_algebraMap, localizationLocalization_repr_algebraMap, nonZeroDivisors
-/
theorem integralBasis_repr_apply (x : (𝓞 K)) (i : Free.ChooseBasisIndex Int (𝓞 K)) :
    (integralBasis K).repr (algebraMap _ _ x) i =
      (algebraMap Int Rat) ((RingOfIntegers.basis K).repr x i) :=
  Basis.localizationLocalization_repr_algebraMap Rat (nonZeroDivisors Int) K _ x i

/--
theorem `mem_span_integralBasis` / 定理 `mem_span_integralBasis`

English:
theorem mem_span_integralBasis
  given: {x : K}
  proof: by
  simp [integralBasis, Basis.localizationLocalization_span]

中文:
定理 mem_span_integralBasis
  条件: {x : K}
  证明: by
  simp [integralBasis, Basis.localizationLocalization_span]

Depends on / 依赖: Basis.localizationLocalization_span, integralBasis, localizationLocalization_span
-/
theorem mem_span_integralBasis {x : K} :
    x in Submodule.span Int (Set.range (integralBasis K)) ↔ x in (algebraMap (𝓞 K) K).range := by
  simp [integralBasis, Basis.localizationLocalization_span]

/--
theorem `RingOfIntegers.rank` / 定理 `RingOfIntegers.rank`

English:
theorem RingOfIntegers.rank
  statement: Module.finrank Int (𝓞 K) = Module.finrank Rat K
  proof: IsIntegralClosure.rank Int Rat K (𝓞 K)

中文:
定理 RingOf整数egers.rank
  结论: 模.finrank 整数 (𝓞 K) = 模.finrank 有理数 K
  证明: IsIntegralClosure.rank Int Rat K (𝓞 K)

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.rank
-/
theorem RingOfIntegers.rank : Module.finrank Int (𝓞 K) = Module.finrank Rat K :=
  IsIntegralClosure.rank Int Rat K (𝓞 K)

end NumberField

namespace Rat

open NumberField

/--
Instance `numberField` / 实例 `numberField`

English:
instance numberField
  signature: : NumberField Rat where

中文:
实例 numberField
  签名: : 数域 有理数 where
-/
instance numberField : NumberField Rat where

/--
Definition of `ringOfIntegersEquiv` / `ringOfIntegersEquiv` 的定义

English:
definition ringOfIntegersEquiv
  signature: : 𝓞 Rat ≃+* Int
  body: RingOfIntegers.equiv Int

@[simp]

中文:
定义 ringOf整数egersEquiv
  签名: : 𝓞 有理数 ≃+* 整数
  定义体: RingOfIntegers.equiv Int

@[simp]

Depends on / 依赖: RingOfIntegers, RingOfIntegers.equiv
-/
noncomputable def ringOfIntegersEquiv : 𝓞 Rat ≃+* Int :=
  RingOfIntegers.equiv Int

@[simp]
/--
theorem `ringOfIntegersEquiv_apply_coe` / 定理 `ringOfIntegersEquiv_apply_coe`

English:
theorem ringOfIntegersEquiv_apply_coe
  given: (z : 𝓞 Rat)
  proof: by
  obtain ⟨z, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective z
  simp

中文:
定理 ringOf整数egersEquiv_apply_coe
  条件: (z : 𝓞 有理数)
  证明: by
  obtain ⟨z, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective z
  simp

Depends on / 依赖: Rat.ringOfIntegersEquiv.symm.surjective, ringOfIntegersEquiv, surjective
-/
theorem ringOfIntegersEquiv_apply_coe (z : 𝓞 Rat) :
    (Rat.ringOfIntegersEquiv z : Rat) = algebraMap (𝓞 Rat) Rat z := by
  obtain ⟨z, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective z
  simp

/--
theorem `ringOfIntegersEquiv_symm_apply_coe` / 定理 `ringOfIntegersEquiv_symm_apply_coe`

English:
theorem ringOfIntegersEquiv_symm_apply_coe
  given: (x : Int)
  proof: eq_intCast ringOfIntegersEquiv.symm _ ▸ rfl

中文:
定理 ringOf整数egersEquiv_symm_apply_coe
  条件: (x : 整数)
  证明: eq_intCast ringOfIntegersEquiv.symm _ ▸ rfl

Depends on / 依赖: eq_intCast, ringOfIntegersEquiv, ringOfIntegersEquiv.symm
-/
theorem ringOfIntegersEquiv_symm_apply_coe (x : Int) :
    (ringOfIntegersEquiv.symm x : Rat) = ↑x :=
  eq_intCast ringOfIntegersEquiv.symm _ ▸ rfl

end Rat

namespace AdjoinRoot

/-- The quotient of `ℚ[X]` by the ideal generated by an irreducible polynomial of `ℚ[X]`
is a number field. -/
instance {f : Polynomial Rat} [hf : Fact (Irreducible f)] : NumberField (AdjoinRoot f) where
  to_charZero := charZero_of_injective_algebraMap (algebraMap Rat _).injective
  to_finiteDimensional := by convert! (AdjoinRoot.powerBasis hf.out.ne_zero).finite

end AdjoinRoot
