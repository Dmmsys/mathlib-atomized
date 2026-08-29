/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Junyan Xu, Jack McKoen
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Algebra.Ring.Subring.Pointwise
public import Mathlib.Algebra.Ring.Action.Field
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!

# Valuation subrings of a field

## Projects

The order structure on `ValuationSubring K`.

-/

@[expose] public section

universe u

noncomputable section

variable (K : Type u) [Field K]

/--
Definition of `ValuationSubring` / `ValuationSubring` 的定义

English:
structure ValuationSubring
  parameters: extends Subring K
  extends: Subring K
  axioms and operations (1):
    - mem_or_inv_mem' : forall x : K, x in carrier ∨ x⁻¹ in carrier

中文:
结构 赋值子环
  参数: extends 子环 K
  继承: 子环 K
  公理与运算 (1 个):
    - mem_or_inv_mem' : 对任意 x : K, x in carrier ∨ x⁻¹ in carrier
-/
structure ValuationSubring extends Subring K where
  mem_or_inv_mem' : forall x : K, x in carrier ∨ x⁻¹ in carrier

namespace ValuationSubring

variable {K}
variable (A : ValuationSubring K)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (ValuationSubring K) K
  body: A.toSubring
  coe_injective := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    replace h := SetLike.coe_injective h
    congr

中文:
实例 :
  签名: 集合状 (赋值子环 K) K
  定义体: A.toSubring
  coe_injective := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    replace h := SetLike.coe_injective h
    congr

Depends on / 依赖: A.toSubring, toSubring
-/
instance : SetLike (ValuationSubring K) K where
  coe A := A.toSubring
  coe_injective := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    replace h := SetLike.coe_injective h
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (ValuationSubring K)
  body: .ofSetLike (ValuationSubring K) K

中文:
实例 :
  签名: 偏序 (赋值子环 K)
  定义体: .ofSetLike (ValuationSubring K) K

Depends on / 依赖: ValuationSubring, ofSetLike
-/
instance : PartialOrder (ValuationSubring K) := .ofSetLike (ValuationSubring K) K

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: (x : K)
  statement: x in A.carrier ↔ x in A
  proof: Iff.refl _

@[simp]

中文:
定理 mem_carrier
  条件: (x : K)
  结论: x in A.carrier ↔ x in A
  证明: Iff.refl _

@[simp]

Depends on / 依赖: Iff.refl
-/
theorem mem_carrier (x : K) : x in A.carrier ↔ x in A := Iff.refl _

@[simp]
/--
theorem `mem_toSubring` / 定理 `mem_toSubring`

English:
theorem mem_toSubring
  given: (x : K)
  statement: x in A.toSubring ↔ x in A
  proof: Iff.refl _

@[ext]

中文:
定理 mem_toSubring
  条件: (x : K)
  结论: x in A.toSubring ↔ x in A
  证明: Iff.refl _

@[ext]

Depends on / 依赖: Iff.refl
-/
theorem mem_toSubring (x : K) : x in A.toSubring ↔ x in A := Iff.refl _

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (A B : ValuationSubring K) (h : forall x, x in A ↔ x in B)
  statement: A = B
  proof: SetLike.ext h

中文:
定理 ext
  条件: (A B : 赋值子环 K) (h : 对任意 x, x in A ↔ x in B)
  结论: A = B
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext (A B : ValuationSubring K) (h : forall x, x in A ↔ x in B) : A = B := SetLike.ext h

/--
theorem `zero_mem` / 定理 `zero_mem`

English:
theorem zero_mem
  statement: (0 : K) in A
  proof: A.toSubring.zero_mem

中文:
定理 zero_mem
  结论: (0 : K) in A
  证明: A.toSubring.zero_mem

Depends on / 依赖: A.toSubring.zero_mem, toSubring, zero_mem
-/
theorem zero_mem : (0 : K) in A := A.toSubring.zero_mem

/--
theorem `one_mem` / 定理 `one_mem`

English:
theorem one_mem
  statement: (1 : K) in A
  proof: A.toSubring.one_mem

中文:
定理 one_mem
  结论: (1 : K) in A
  证明: A.toSubring.one_mem

Depends on / 依赖: A.toSubring.one_mem, one_mem, toSubring
-/
theorem one_mem : (1 : K) in A := A.toSubring.one_mem

/--
theorem `add_mem` / 定理 `add_mem`

English:
theorem add_mem
  given: (x y : K)
  statement: x in A -> y in A -> x + y in A
  proof: A.toSubring.add_mem

中文:
定理 add_mem
  条件: (x y : K)
  结论: x in A -> y in A -> x + y in A
  证明: A.toSubring.add_mem

Depends on / 依赖: A.toSubring.add_mem, add_mem, toSubring
-/
theorem add_mem (x y : K) : x in A -> y in A -> x + y in A := A.toSubring.add_mem

/--
theorem `mul_mem` / 定理 `mul_mem`

English:
theorem mul_mem
  given: (x y : K)
  statement: x in A -> y in A -> x * y in A
  proof: A.toSubring.mul_mem

中文:
定理 mul_mem
  条件: (x y : K)
  结论: x in A -> y in A -> x * y in A
  证明: A.toSubring.mul_mem

Depends on / 依赖: A.toSubring.mul_mem, mul_mem, toSubring
-/
theorem mul_mem (x y : K) : x in A -> y in A -> x * y in A := A.toSubring.mul_mem

/--
theorem `neg_mem` / 定理 `neg_mem`

English:
theorem neg_mem
  given: (x : K)
  statement: x in A -> -x in A
  proof: A.toSubring.neg_mem

中文:
定理 neg_mem
  条件: (x : K)
  结论: x in A -> -x in A
  证明: A.toSubring.neg_mem

Depends on / 依赖: A.toSubring.neg_mem, neg_mem, toSubring
-/
theorem neg_mem (x : K) : x in A -> -x in A := A.toSubring.neg_mem

/--
theorem `mem_or_inv_mem` / 定理 `mem_or_inv_mem`

English:
theorem mem_or_inv_mem
  given: (x : K)
  statement: x in A ∨ x⁻¹ in A
  proof: A.mem_or_inv_mem' _

中文:
定理 mem_or_inv_mem
  条件: (x : K)
  结论: x in A ∨ x⁻¹ in A
  证明: A.mem_or_inv_mem' _

Depends on / 依赖: A.mem_or_inv_mem, mem_or_inv_mem
-/
theorem mem_or_inv_mem (x : K) : x in A ∨ x⁻¹ in A := A.mem_or_inv_mem' _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubringClass (ValuationSubring K) K
  body: zero_mem
  add_mem {_} a b := add_mem _ a b
  one_mem := one_mem
  mul_mem {_} a b := mul_mem _ a b
  neg_mem {_} x := neg_mem _ x

中文:
实例 :
  签名: 子环类 (赋值子环 K) K
  定义体: zero_mem
  add_mem {_} a b := add_mem _ a b
  one_mem := one_mem
  mul_mem {_} a b := mul_mem _ a b
  neg_mem {_} x := neg_mem _ x

Depends on / 依赖: zero_mem
-/
instance : SubringClass (ValuationSubring K) K where
  zero_mem := zero_mem
  add_mem {_} a b := add_mem _ a b
  one_mem := one_mem
  mul_mem {_} a b := mul_mem _ a b
  neg_mem {_} x := neg_mem _ x

/--
theorem `toSubring_injective` / 定理 `toSubring_injective`

English:
theorem toSubring_injective
  statement: Function.Injective (toSubring : ValuationSubring K -> Subring K)
  proof: fun x y h => by cases x; cases y; congr

中文:
定理 toSubring_injective
  结论: 函数.单射 (toSubring : 赋值子环 K -> 子环 K)
  证明: fun x y h => by cases x; cases y; congr
-/
theorem toSubring_injective : Function.Injective (toSubring : ValuationSubring K -> Subring K) :=
  fun x y h => by cases x; cases y; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing A
  body: inferInstanceAs CommRing A.toSubring

中文:
实例 :
  签名: 交换环 A
  定义体: inferInstanceAs CommRing A.toSubring

Depends on / 依赖: A.toSubring, CommRing, toSubring
-/
instance : CommRing A := inferInstanceAs CommRing A.toSubring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDomain A
  body: inferInstanceAs IsDomain A.toSubring

中文:
实例 :
  签名: 是整环 A
  定义体: inferInstanceAs IsDomain A.toSubring

Depends on / 依赖: A.toSubring, IsDomain, toSubring
-/
instance : IsDomain A := inferInstanceAs IsDomain A.toSubring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (ValuationSubring K)
  body: Top.mk { (⊤ : Subring K) with mem_or_inv_mem' := fun _ => Or.inl trivial }

@[simp]

中文:
实例 :
  签名: 顶元素 (赋值子环 K)
  定义体: Top.mk { (⊤ : Subring K) with mem_or_inv_mem' := fun _ => Or.inl trivial }

@[simp]

Depends on / 依赖: Or.inl, Subring, Top.mk, mem_or_inv_mem
-/
instance : Top (ValuationSubring K) :=
Top.mk { (⊤ : Subring K) with mem_or_inv_mem' := fun _ => Or.inl trivial }

@[simp]
/--
theorem `toSubring_top` / 定理 `toSubring_top`

English:
theorem toSubring_top
  statement: (⊤ : ValuationSubring K).toSubring = ⊤
  proof: rfl

@[simp]

中文:
定理 toSubring_top
  结论: (⊤ : 赋值子环 K).toSubring = ⊤
  证明: rfl

@[simp]
-/
theorem toSubring_top : (⊤ : ValuationSubring K).toSubring = ⊤ := rfl

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: (x : K)
  statement: x in (⊤ : ValuationSubring K)
  proof: trivial

中文:
定理 mem_top
  条件: (x : K)
  结论: x in (⊤ : 赋值子环 K)
  证明: trivial
-/
theorem mem_top (x : K) : x in (⊤ : ValuationSubring K) :=
  trivial

/--
theorem `le_top` / 定理 `le_top`

English:
theorem le_top
  statement: A <= ⊤
  proof: fun _a _ha => mem_top _

中文:
定理 le_top
  结论: A <= ⊤
  证明: fun _a _ha => mem_top _

Depends on / 依赖: mem_top
-/
theorem le_top : A <= ⊤ := fun _a _ha => mem_top _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Field (⊤ : ValuationSubring K)
  body: inferInstanceAs (Field (⊤ : Subfield K))

@[simp, norm_cast]

中文:
实例 :
  签名: 域 (⊤ : 赋值子环 K)
  定义体: inferInstanceAs (Field (⊤ : Subfield K))

@[simp, norm_cast]

Depends on / 依赖: Subfield
-/
instance : Field (⊤ : ValuationSubring K) := inferInstanceAs (Field (⊤ : Subfield K))

@[simp, norm_cast]
/--
theorem `top_coe_div` / 定理 `top_coe_div`

English:
theorem top_coe_div
  given: (x y : (⊤ : ValuationSubring K))
  proof: rfl

@[simp, norm_cast]

中文:
定理 top_coe_div
  条件: (x y : (⊤ : 赋值子环 K))
  证明: rfl

@[simp, norm_cast]
-/
theorem top_coe_div (x y : (⊤ : ValuationSubring K)) :
    ((x / y : (⊤ : ValuationSubring K)) : K) = (x : K) / (y : K) :=
  rfl

@[simp, norm_cast]
/--
theorem `top_coe_inv` / 定理 `top_coe_inv`

English:
theorem top_coe_inv
  given: (x : (⊤ : ValuationSubring K))
  proof: rfl

中文:
定理 top_coe_inv
  条件: (x : (⊤ : 赋值子环 K))
  证明: rfl
-/
theorem top_coe_inv (x : (⊤ : ValuationSubring K)) :
    ((x⁻¹ : (⊤ : ValuationSubring K)) : K) = (x : K)⁻¹ :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTop (ValuationSubring K)
  body: le_top

中文:
实例 :
  签名: 有顶序 (赋值子环 K)
  定义体: le_top

Depends on / 依赖: le_top
-/
instance : OrderTop (ValuationSubring K) where
  le_top := le_top

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (ValuationSubring K)
  body: ⟨⊤⟩

中文:
实例 :
  签名: 可居 (赋值子环 K)
  定义体: ⟨⊤⟩
-/
instance : Inhabited (ValuationSubring K) :=
  ⟨⊤⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ValuationRing A
  body: by
    by_cases h : (b : K) = 0
    · use 0
      left
      ext
      simp [h]
    by_cases h : (a : K) = 0
    · use 0; right
      ext
      simp [h]
    rcases A.mem_or_inv_mem (a / b) with hh | hh
    · use ⟨a / b, hh⟩
      right
      ext
      simp [field]
    · rw [show (a / b : K)⁻¹ = b / a by simp] at hh
      use ⟨b / a, hh⟩
      left
      ext
      simp [field]

中文:
实例 :
  签名: 赋值环 A
  定义体: by
    by_cases h : (b : K) = 0
    · use 0
      left
      ext
      simp [h]
    by_cases h : (a : K) = 0
    · use 0; right
      ext
      simp [h]
    rcases A.mem_or_inv_mem (a / b) with hh | hh
    · use ⟨a / b, hh⟩
      right
      ext
      simp [field]
    · rw [show (a / b : K)⁻¹ = b / a by simp] at hh
      use ⟨b / a, hh⟩
      left
      ext
      simp [field]

Depends on / 依赖: A.mem_or_inv_mem, mem_or_inv_mem
-/
instance : ValuationRing A where
  cond' a b := by
    by_cases h : (b : K) = 0
    · use 0
      left
      ext
      simp [h]
    by_cases h : (a : K) = 0
    · use 0; right
      ext
      simp [h]
    rcases A.mem_or_inv_mem (a / b) with hh | hh
    · use ⟨a / b, hh⟩
      right
      ext
      simp [field]
    · rw [show (a / b : K)⁻¹ = b / a by simp] at hh
      use ⟨b / a, hh⟩
      left
      ext
      simp [field]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra A K
  body: inferInstance

中文:
实例 :
  签名: 代数 A K
  定义体: inferInstance
-/
instance : Algebra A K := inferInstance

/--
Instance `isLocalRing` / 实例 `isLocalRing`

English:
instance isLocalRing
  signature: : IsLocalRing A
  body: inferInstance

@[simp]

中文:
实例 isLocalRing
  签名: : 是局部环 A
  定义体: inferInstance

@[simp]
-/
instance isLocalRing : IsLocalRing A := inferInstance

@[simp]
/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (a : A)
  statement: algebraMap A K a = a
  proof: rfl

中文:
定理 algebraMap_apply
  条件: (a : A)
  结论: algebraMap A K a = a
  证明: rfl
-/
theorem algebraMap_apply (a : A) : algebraMap A K a = a := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFractionRing A K
  body: fun ⟨y, hy⟩ =>
    (Units.mk0 (y : K) fun c => nonZeroDivisors.ne_zero hy <| Subtype.ext c).isUnit
  surj z := by
    by_cases h : z = 0; · use (0, 1); simp [h]
    rcases A.mem_or_inv_mem z with hh | hh
    · use (⟨z, hh⟩, 1); simp
    · refine ⟨⟨1, ⟨⟨_, hh⟩, ?_⟩⟩, mul_inv_cancel₀ h⟩
      exact mem_nonZeroDivisors_iff_ne_zero.2 fun c => h (inv_eq_zero.mp (congr_arg Subtype.val c))
  exists_of_eq {a b} h := ⟨1, by ext; simpa using h⟩

中文:
实例 :
  签名: IsFractionRing A K
  定义体: fun ⟨y, hy⟩ =>
    (Units.mk0 (y : K) fun c => nonZeroDivisors.ne_zero hy <| Subtype.ext c).isUnit
  surj z := by
    by_cases h : z = 0; · use (0, 1); simp [h]
    rcases A.mem_or_inv_mem z with hh | hh
    · use (⟨z, hh⟩, 1); simp
    · refine ⟨⟨1, ⟨⟨_, hh⟩, ?_⟩⟩, mul_inv_cancel₀ h⟩
      exact mem_nonZeroDivisors_iff_ne_zero.2 fun c => h (inv_eq_zero.mp (congr_arg Subtype.val c))
  exists_of_eq {a b} h := ⟨1, by ext; simpa using h⟩
-/
instance : IsFractionRing A K where
  map_units := fun ⟨y, hy⟩ =>
    (Units.mk0 (y : K) fun c => nonZeroDivisors.ne_zero hy <| Subtype.ext c).isUnit
  surj z := by
    by_cases h : z = 0; · use (0, 1); simp [h]
    rcases A.mem_or_inv_mem z with hh | hh
    · use (⟨z, hh⟩, 1); simp
    · refine ⟨⟨1, ⟨⟨_, hh⟩, ?_⟩⟩, mul_inv_cancel₀ h⟩
      exact mem_nonZeroDivisors_iff_ne_zero.2 fun c => h (inv_eq_zero.mp (congr_arg Subtype.val c))
  exists_of_eq {a b} h := ⟨1, by ext; simpa using h⟩

/--
Definition of `ValueGroup` / `ValueGroup` 的定义

English:
definition ValueGroup
  body: ValuationRing.ValueGroup A K
deriving LinearOrderedCommGroupWithZero

中文:
定义 ValueGroup
  定义体: ValuationRing.ValueGroup A K
deriving LinearOrderedCommGroupWithZero

Depends on / 依赖: ValuationRing, ValuationRing.ValueGroup, ValueGroup
-/
def ValueGroup :=
  ValuationRing.ValueGroup A K
deriving LinearOrderedCommGroupWithZero

/--
Definition of `valuation` / `valuation` 的定义

English:
definition valuation
  signature: : Valuation K A.ValueGroup
  body: ValuationRing.valuation A K

中文:
定义 valuation
  签名: : 赋值 K A.ValueGroup
  定义体: ValuationRing.valuation A K

Depends on / 依赖: ValuationRing, ValuationRing.valuation, valuation
-/
def valuation : Valuation K A.ValueGroup :=
  ValuationRing.valuation A K

/--
Instance `inhabitedValueGroup` / 实例 `inhabitedValueGroup`

English:
instance inhabitedValueGroup
  signature: : Inhabited A.ValueGroup
  body: ⟨A.valuation 0⟩

中文:
实例 inhabitedValueGroup
  签名: : 可居 A.ValueGroup
  定义体: ⟨A.valuation 0⟩

Depends on / 依赖: A.valuation, valuation
-/
instance inhabitedValueGroup : Inhabited A.ValueGroup := ⟨A.valuation 0⟩

/--
theorem `valuation_le_one` / 定理 `valuation_le_one`

English:
theorem valuation_le_one
  given: (a : A)
  statement: A.valuation a <= 1
  proof: (ValuationRing.mem_integer_iff A K _).2 ⟨a, rfl⟩

中文:
定理 valuation_le_one
  条件: (a : A)
  结论: A.valuation a <= 1
  证明: (ValuationRing.mem_integer_iff A K _).2 ⟨a, rfl⟩

Depends on / 依赖: ValuationRing, ValuationRing.mem_integer_iff, mem_integer_iff
-/
theorem valuation_le_one (a : A) : A.valuation a <= 1 :=
  (ValuationRing.mem_integer_iff A K _).2 ⟨a, rfl⟩

/--
theorem `mem_of_valuation_le_one` / 定理 `mem_of_valuation_le_one`

English:
theorem mem_of_valuation_le_one
  given: (x : K) (h : A.valuation x <= 1)
  statement: x in A
  proof: let ⟨a, ha⟩ := (ValuationRing.mem_integer_iff A K x).1 h
  ha ▸ a.2

@[simp]

中文:
定理 mem_of_valuation_le_one
  条件: (x : K) (h : A.valuation x <= 1)
  结论: x in A
  证明: let ⟨a, ha⟩ := (ValuationRing.mem_integer_iff A K x).1 h
  ha ▸ a.2

@[simp]

Depends on / 依赖: ValuationRing, ValuationRing.mem_integer_iff, mem_integer_iff
-/
theorem mem_of_valuation_le_one (x : K) (h : A.valuation x <= 1) : x in A :=
  let ⟨a, ha⟩ := (ValuationRing.mem_integer_iff A K x).1 h
  ha ▸ a.2

@[simp]
/--
theorem `valuation_le_one_iff` / 定理 `valuation_le_one_iff`

English:
theorem valuation_le_one_iff
  given: (x : K)
  statement: A.valuation x <= 1 ↔ x in A
  proof: ⟨mem_of_valuation_le_one _ _, fun ha => A.valuation_le_one ⟨x, ha⟩⟩

中文:
定理 valuation_le_one_iff
  条件: (x : K)
  结论: A.valuation x <= 1 ↔ x in A
  证明: ⟨mem_of_valuation_le_one _ _, fun ha => A.valuation_le_one ⟨x, ha⟩⟩

Depends on / 依赖: A.valuation_le_one, mem_of_valuation_le_one, valuation_le_one
-/
theorem valuation_le_one_iff (x : K) : A.valuation x <= 1 ↔ x in A :=
  ⟨mem_of_valuation_le_one _ _, fun ha => A.valuation_le_one ⟨x, ha⟩⟩

/--
theorem `valuation_eq_iff` / 定理 `valuation_eq_iff`

English:
theorem valuation_eq_iff
  given: (x y : K)
  statement: A.valuation x = A.valuation y ↔ exists a : Aˣ, (a : K) * y = x
  proof: Quotient.eq''

中文:
定理 valuation_eq_iff
  条件: (x y : K)
  结论: A.valuation x = A.valuation y ↔ 存在 a : Aˣ, (a : K) * y = x
  证明: Quotient.eq''

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem valuation_eq_iff (x y : K) : A.valuation x = A.valuation y ↔ exists a : Aˣ, (a : K) * y = x :=
  Quotient.eq''

/--
theorem `valuation_le_iff` / 定理 `valuation_le_iff`

English:
theorem valuation_le_iff
  given: (x y : K)
  statement: A.valuation x <= A.valuation y ↔ exists a : A, (a : K) * y = x
  proof: Iff.rfl

中文:
定理 valuation_le_iff
  条件: (x y : K)
  结论: A.valuation x <= A.valuation y ↔ 存在 a : A, (a : K) * y = x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem valuation_le_iff (x y : K) : A.valuation x <= A.valuation y ↔ exists a : A, (a : K) * y = x :=
  Iff.rfl

/--
theorem `valuation_surjective` / 定理 `valuation_surjective`

English:
theorem valuation_surjective
  statement: Function.Surjective A.valuation
  proof: Quot.mk_surjective

@[simp]

中文:
定理 valuation_surjective
  结论: 函数.满射 A.valuation
  证明: Quot.mk_surjective

@[simp]

Depends on / 依赖: Quot.mk_surjective, mk_surjective
-/
theorem valuation_surjective : Function.Surjective A.valuation := Quot.mk_surjective

@[simp]
/--
theorem `valuation_unit` / 定理 `valuation_unit`

English:
theorem valuation_unit
  given: (a : Aˣ)
  statement: A.valuation a = 1
  proof: by
  rw [← A.valuation.map_one]; rw [valuation_eq_iff]; use a; simp

中文:
定理 valuation_unit
  条件: (a : Aˣ)
  结论: A.valuation a = 1
  证明: by
  rw [← A.valuation.map_one]; rw [valuation_eq_iff]; use a; simp

Depends on / 依赖: A.valuation.map_one, map_one, valuation, valuation_eq_iff
-/
theorem valuation_unit (a : Aˣ) : A.valuation a = 1 := by
  rw [← A.valuation.map_one]; rw [valuation_eq_iff]; use a; simp

/--
theorem `valuation_eq_one_iff` / 定理 `valuation_eq_one_iff`

English:
theorem valuation_eq_one_iff
  given: (a : A)
  statement: IsUnit a ↔ A.valuation a = 1 where
  proof: A.valuation_unit h.unit
  mpr h := by
    have ha : (a : K) != 0 := by
      intro c
      rw [c]; rw [A.valuation.map_zero] at h
      exact zero_ne_one h
    have ha' : (a : K)⁻¹ in A := by rw [← valuation_le_one_iff, map_inv₀, h, inv_one]
    refine .of_mul_eq_one ⟨a⁻¹, ha'⟩ ?_
    ext
    simp [field]

中文:
定理 valuation_eq_one_iff
  条件: (a : A)
  结论: 是单位 a ↔ A.valuation a = 1 where
  证明: A.valuation_unit h.unit
  mpr h := by
    have ha : (a : K) != 0 := by
      intro c
      rw [c]; rw [A.valuation.map_zero] at h
      exact zero_ne_one h
    have ha' : (a : K)⁻¹ in A := by rw [← valuation_le_one_iff, map_inv₀, h, inv_one]
    refine .of_mul_eq_one ⟨a⁻¹, ha'⟩ ?_
    ext
    simp [field]

Depends on / 依赖: A.valuation_unit, h.unit, valuation_unit
-/
theorem valuation_eq_one_iff (a : A) : IsUnit a ↔ A.valuation a = 1 where
  mp h := A.valuation_unit h.unit
  mpr h := by
    have ha : (a : K) != 0 := by
      intro c
      rw [c]; rw [A.valuation.map_zero] at h
      exact zero_ne_one h
    have ha' : (a : K)⁻¹ in A := by rw [← valuation_le_one_iff, map_inv₀, h, inv_one]
    refine .of_mul_eq_one ⟨a⁻¹, ha'⟩ ?_
    ext
    simp [field]

/--
theorem `eq_top_iff` / 定理 `eq_top_iff`

English:
theorem eq_top_iff
  statement: A = ⊤ ↔ ¬ A.valuation.IsNontrivial
  proof: by
  simp [Valuation.IsNontrivial_iff_exists_one_lt, SetLike.ext_iff]

中文:
定理 eq_top_iff
  结论: A = ⊤ ↔ ¬ A.valuation.是非平凡
  证明: by
  simp [Valuation.IsNontrivial_iff_exists_one_lt, SetLike.ext_iff]

Depends on / 依赖: IsNontrivial_iff_exists_one_lt, SetLike, SetLike.ext_iff, Valuation, Valuation.IsNontrivial_iff_exists_one_lt, ext_iff
-/
theorem eq_top_iff : A = ⊤ ↔ ¬ A.valuation.IsNontrivial := by
  simp [Valuation.IsNontrivial_iff_exists_one_lt, SetLike.ext_iff]

/--
theorem `valuation_lt_one_or_eq_one` / 定理 `valuation_lt_one_or_eq_one`

English:
theorem valuation_lt_one_or_eq_one
  given: (a : A)
  statement: A.valuation a < 1 ∨ A.valuation a = 1
  proof: lt_or_eq_of_le (A.valuation_le_one a)

中文:
定理 valuation_lt_one_or_eq_one
  条件: (a : A)
  结论: A.valuation a < 1 ∨ A.valuation a = 1
  证明: lt_or_eq_of_le (A.valuation_le_one a)

Depends on / 依赖: A.valuation_le_one, lt_or_eq_of_le, valuation_le_one
-/
theorem valuation_lt_one_or_eq_one (a : A) : A.valuation a < 1 ∨ A.valuation a = 1 :=
  lt_or_eq_of_le (A.valuation_le_one a)

/--
theorem `valuation_lt_one_iff` / 定理 `valuation_lt_one_iff`

English:
theorem valuation_lt_one_iff
  given: (a : A)
  statement: a in IsLocalRing.maximalIdeal A ↔ A.valuation a < 1
  proof: by
  rw [IsLocalRing.mem_maximalIdeal]
  dsimp [nonunits]; rw [valuation_eq_one_iff]
  exact (A.valuation_le_one a).lt_iff_ne.symm

中文:
定理 valuation_lt_one_iff
  条件: (a : A)
  结论: a in 是局部环.maximalIdeal A ↔ A.valuation a < 1
  证明: by
  rw [IsLocalRing.mem_maximalIdeal]
  dsimp [nonunits]; rw [valuation_eq_one_iff]
  exact (A.valuation_le_one a).lt_iff_ne.symm

Depends on / 依赖: A.valuation_le_one, IsLocalRing, IsLocalRing.mem_maximalIdeal, lt_iff_ne, lt_iff_ne.symm, mem_maximalIdeal, nonunits, valuation_eq_one_iff, valuation_le_one
-/
theorem valuation_lt_one_iff (a : A) : a in IsLocalRing.maximalIdeal A ↔ A.valuation a < 1 := by
  rw [IsLocalRing.mem_maximalIdeal]
  dsimp [nonunits]; rw [valuation_eq_one_iff]
  exact (A.valuation_le_one a).lt_iff_ne.symm

/--
Definition of `ofSubring` / `ofSubring` 的定义

English:
definition ofSubring
  signature: (R : Subring K) (hR : forall x : K, x in R ∨ x⁻¹ in R)
  body: { R with mem_or_inv_mem' := hR }

@[simp]

中文:
定义 ofSubring
  签名: (R : 子环 K) (hR : 对任意 x : K, x in R ∨ x⁻¹ in R)
  定义体: { R with mem_or_inv_mem' := hR }

@[simp]

Depends on / 依赖: mem_or_inv_mem
-/
def ofSubring (R : Subring K) (hR : forall x : K, x in R ∨ x⁻¹ in R) : ValuationSubring K :=
  { R with mem_or_inv_mem' := hR }

@[simp]
/--
theorem `mem_ofSubring` / 定理 `mem_ofSubring`

English:
theorem mem_ofSubring
  given: (R : Subring K) (hR : forall x : K, x in R ∨ x⁻¹ in R) (x : K)
  proof: Iff.refl _

中文:
定理 mem_ofSubring
  条件: (R : 子环 K) (hR : 对任意 x : K, x in R ∨ x⁻¹ in R) (x : K)
  证明: Iff.refl _

Depends on / 依赖: Iff.refl
-/
theorem mem_ofSubring (R : Subring K) (hR : forall x : K, x in R ∨ x⁻¹ in R) (x : K) :
    x in ofSubring R hR ↔ x in R :=
  Iff.refl _

/--
Definition of `ofLE` / `ofLE` 的定义

English:
definition ofLE
  signature: (R : ValuationSubring K) (S : Subring K) (h : R.toSubring <= S)
  body: { S with mem_or_inv_mem' := fun x => (R.mem_or_inv_mem x).imp (@h x) (@h _) }

中文:
定义 ofLE
  签名: (R : 赋值子环 K) (S : 子环 K) (h : R.toSubring <= S)
  定义体: { S with mem_or_inv_mem' := fun x => (R.mem_or_inv_mem x).imp (@h x) (@h _) }

Depends on / 依赖: R.mem_or_inv_mem, mem_or_inv_mem
-/
def ofLE (R : ValuationSubring K) (S : Subring K) (h : R.toSubring <= S) : ValuationSubring K :=
  { S with mem_or_inv_mem' := fun x => (R.mem_or_inv_mem x).imp (@h x) (@h _) }

section Order

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (ValuationSubring K)
  body: { (inferInstance : PartialOrder (ValuationSubring K)) with
sup := fun R S => ofLE R (R.toSubring ⊔ S.toSubring) le_sup_left
    le_sup_left := fun R S _ hx => (le_sup_left : R.toSubring <= R.toSubring ⊔ S.toSubring) hx
    le_sup_right := fun R S _ hx => (le_sup_right : S.toSubring <= R.toSubring ⊔ S.toSubring) hx
    sup_le := fun R S T hR hT _ hx => (sup_le hR hT : R.toSubring ⊔ S.toSubring <= T.toSubring) hx }

中文:
实例 :
  签名: SemilatticeSup (赋值子环 K)
  定义体: { (inferInstance : PartialOrder (ValuationSubring K)) with
sup := fun R S => ofLE R (R.toSubring ⊔ S.toSubring) le_sup_left
    le_sup_left := fun R S _ hx => (le_sup_left : R.toSubring <= R.toSubring ⊔ S.toSubring) hx
    le_sup_right := fun R S _ hx => (le_sup_right : S.toSubring <= R.toSubring ⊔ S.toSubring) hx
    sup_le := fun R S T hR hT _ hx => (sup_le hR hT : R.toSubring ⊔ S.toSubring <= T.toSubring) hx }

Depends on / 依赖: PartialOrder, R.toSubring, S.toSubring, T.toSubring, ValuationSubring, le_sup_left, le_sup_right, sup_le, toSubring
-/
instance : SemilatticeSup (ValuationSubring K) :=
  { (inferInstance : PartialOrder (ValuationSubring K)) with
sup := fun R S => ofLE R (R.toSubring ⊔ S.toSubring) le_sup_left
    le_sup_left := fun R S _ hx => (le_sup_left : R.toSubring <= R.toSubring ⊔ S.toSubring) hx
    le_sup_right := fun R S _ hx => (le_sup_right : S.toSubring <= R.toSubring ⊔ S.toSubring) hx
    sup_le := fun R S T hR hT _ hx => (sup_le hR hT : R.toSubring ⊔ S.toSubring <= T.toSubring) hx }

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: (R S : ValuationSubring K) (h : R <= S)
  body: Subring.inclusion h

中文:
定义 inclusion
  签名: (R S : 赋值子环 K) (h : R <= S)
  定义体: Subring.inclusion h

Depends on / 依赖: Subring, Subring.inclusion, inclusion
-/
def inclusion (R S : ValuationSubring K) (h : R <= S) : R ->+* S :=
  Subring.inclusion h

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (R : ValuationSubring K)
  body: Subring.subtype R.toSubring

@[simp]

中文:
定义 subtype
  签名: (R : 赋值子环 K)
  定义体: Subring.subtype R.toSubring

@[simp]

Depends on / 依赖: R.toSubring, Subring, Subring.subtype, subtype, toSubring
-/
def subtype (R : ValuationSubring K) : R ->+* K :=
  Subring.subtype R.toSubring

@[simp]
/--
lemma `subtype_apply` / 引理 `subtype_apply`

English:
lemma subtype_apply
  given: {R : ValuationSubring K} (x : R)
  proof: rfl

中文:
引理 subtype_apply
  条件: {R : 赋值子环 K} (x : R)
  证明: rfl
-/
lemma subtype_apply {R : ValuationSubring K} (x : R) :
    R.subtype x = x := rfl

/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  given: (R : ValuationSubring K)
  proof: R.toSubring.subtype_injective

@[simp]

中文:
引理 subtype_injective
  条件: (R : 赋值子环 K)
  证明: R.toSubring.subtype_injective

@[simp]

Depends on / 依赖: R.toSubring.subtype_injective, subtype_injective, toSubring
-/
lemma subtype_injective (R : ValuationSubring K) :
    Function.Injective R.subtype :=
  R.toSubring.subtype_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  given: (R : ValuationSubring K)
  statement: ⇑(subtype R) = Subtype.val
  proof: rfl

中文:
定理 coe_subtype
  条件: (R : 赋值子环 K)
  结论: ⇑(subtype R) = 子类型.val
  证明: rfl
-/
theorem coe_subtype (R : ValuationSubring K) : ⇑(subtype R) = Subtype.val :=
  rfl

/--
Definition of `mapOfLE` / `mapOfLE` 的定义

English:
definition mapOfLE
  signature: (R S : ValuationSubring K) (h : R <= S)
  body: Quotient.map' id fun _ _ ⟨u, hu⟩ => ⟨Units.map (R.inclusion S h).toMonoidHom u, hu⟩
  map_zero' := rfl
  map_one' := rfl
  map_mul' := by rintro ⟨⟩ ⟨⟩; rfl

@[gcongr, mono]

中文:
定义 mapOfLE
  签名: (R S : 赋值子环 K) (h : R <= S)
  定义体: Quotient.map' id fun _ _ ⟨u, hu⟩ => ⟨Units.map (R.inclusion S h).toMonoidHom u, hu⟩
  map_zero' := rfl
  map_one' := rfl
  map_mul' := by rintro ⟨⟩ ⟨⟩; rfl

@[gcongr, mono]

Depends on / 依赖: Quotient, Quotient.map, R.inclusion, Units.map, inclusion, toMonoidHom
-/
def mapOfLE (R S : ValuationSubring K) (h : R <= S) : R.ValueGroup ->*₀ S.ValueGroup where
  toFun := Quotient.map' id fun _ _ ⟨u, hu⟩ => ⟨Units.map (R.inclusion S h).toMonoidHom u, hu⟩
  map_zero' := rfl
  map_one' := rfl
  map_mul' := by rintro ⟨⟩ ⟨⟩; rfl

@[gcongr, mono]
/--
theorem `monotone_mapOfLE` / 定理 `monotone_mapOfLE`

English:
theorem monotone_mapOfLE
  given: (R S : ValuationSubring K) (h : R <= S)
  statement: Monotone (R.mapOfLE S h)
  proof: by
  rintro ⟨⟩ ⟨⟩ ⟨a, ha⟩; exact ⟨R.inclusion S h a, ha⟩

@[simp]

中文:
定理 monotone_mapOfLE
  条件: (R S : 赋值子环 K) (h : R <= S)
  结论: 递增 (R.mapOfLE S h)
  证明: by
  rintro ⟨⟩ ⟨⟩ ⟨a, ha⟩; exact ⟨R.inclusion S h a, ha⟩

@[simp]

Depends on / 依赖: R.inclusion, inclusion
-/
theorem monotone_mapOfLE (R S : ValuationSubring K) (h : R <= S) : Monotone (R.mapOfLE S h) := by
  rintro ⟨⟩ ⟨⟩ ⟨a, ha⟩; exact ⟨R.inclusion S h a, ha⟩

@[simp]
/--
theorem `mapOfLE_comp_valuation` / 定理 `mapOfLE_comp_valuation`

English:
theorem mapOfLE_comp_valuation
  given: (R S : ValuationSubring K) (h : R <= S)
  proof: by ext; rfl

@[simp]

中文:
定理 mapOfLE_comp_valuation
  条件: (R S : 赋值子环 K) (h : R <= S)
  证明: by ext; rfl

@[simp]
-/
theorem mapOfLE_comp_valuation (R S : ValuationSubring K) (h : R <= S) :
    R.mapOfLE S h ∘ R.valuation = S.valuation := by ext; rfl

@[simp]
/--
theorem `mapOfLE_valuation_apply` / 定理 `mapOfLE_valuation_apply`

English:
theorem mapOfLE_valuation_apply
  given: (R S : ValuationSubring K) (h : R <= S) (x : K)
  proof: rfl

中文:
定理 mapOfLE_valuation_apply
  条件: (R S : 赋值子环 K) (h : R <= S) (x : K)
  证明: rfl
-/
theorem mapOfLE_valuation_apply (R S : ValuationSubring K) (h : R <= S) (x : K) :
    R.mapOfLE S h (R.valuation x) = S.valuation x := rfl

/--
Definition of `idealOfLE` / `idealOfLE` 的定义

English:
definition idealOfLE
  signature: (R S : ValuationSubring K) (h : R <= S)
  body: (IsLocalRing.maximalIdeal S).comap (R.inclusion S h)

中文:
定义 idealOfLE
  签名: (R S : 赋值子环 K) (h : R <= S)
  定义体: (IsLocalRing.maximalIdeal S).comap (R.inclusion S h)

Depends on / 依赖: IsLocalRing, IsLocalRing.maximalIdeal, R.inclusion, inclusion, maximalIdeal
-/
def idealOfLE (R S : ValuationSubring K) (h : R <= S) : Ideal R :=
  (IsLocalRing.maximalIdeal S).comap (R.inclusion S h)

/--
theorem `idealOfLE_self` / 定理 `idealOfLE_self`

English:
theorem idealOfLE_self
  statement: A.idealOfLE A (refl _) = IsLocalRing.maximalIdeal A
  proof: rfl

@[simp]

中文:
定理 idealOfLE_self
  结论: A.idealOfLE A (refl _) = 是局部环.maximalIdeal A
  证明: rfl

@[simp]
-/
theorem idealOfLE_self : A.idealOfLE A (refl _) = IsLocalRing.maximalIdeal A := rfl

@[simp]
/--
theorem `idealOfLE_top` / 定理 `idealOfLE_top`

English:
theorem idealOfLE_top
  statement: A.idealOfLE ⊤ (le_top _) = ⊥
  proof: by
  rw [ValuationSubring.idealOfLE]; rw [IsLocalRing.maximalIdeal_eq_bot]; rw [Ideal.comap_bot_of_injective]
  exact Subring.inclusion_injective _

中文:
定理 idealOfLE_top
  结论: A.idealOfLE ⊤ (le_top _) = ⊥
  证明: by
  rw [ValuationSubring.idealOfLE]; rw [IsLocalRing.maximalIdeal_eq_bot]; rw [Ideal.comap_bot_of_injective]
  exact Subring.inclusion_injective _

Depends on / 依赖: Ideal.comap_bot_of_injective, IsLocalRing, IsLocalRing.maximalIdeal_eq_bot, Subring, Subring.inclusion_injective, ValuationSubring, ValuationSubring.idealOfLE, comap_bot_of_injective, idealOfLE, inclusion_injective, maximalIdeal_eq_bot
-/
theorem idealOfLE_top : A.idealOfLE ⊤ (le_top _) = ⊥ := by
  rw [ValuationSubring.idealOfLE]; rw [IsLocalRing.maximalIdeal_eq_bot]; rw [Ideal.comap_bot_of_injective]
  exact Subring.inclusion_injective _

/--
Instance `prime_idealOfLE` / 实例 `prime_idealOfLE`

English:
instance prime_idealOfLE
  signature: (R S : ValuationSubring K) (h : R <= S)
  body: (IsLocalRing.maximalIdeal S).comap_isPrime _

中文:
实例 prime_idealOfLE
  签名: (R S : 赋值子环 K) (h : R <= S)
  定义体: (IsLocalRing.maximalIdeal S).comap_isPrime _

Depends on / 依赖: IsLocalRing, IsLocalRing.maximalIdeal, comap_isPrime, maximalIdeal
-/
instance prime_idealOfLE (R S : ValuationSubring K) (h : R <= S) : (idealOfLE R S h).IsPrime :=
  (IsLocalRing.maximalIdeal S).comap_isPrime _

/--
Definition of `ofPrime` / `ofPrime` 的定义

English:
definition ofPrime
  signature: (A : ValuationSubring K) (P : Ideal A) [P.IsPrime]
  body: ofLE A (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors).toSubring
fun a ha => Subalgebra.mem_toSubring.mpr
      Subalgebra.algebraMap_mem
        (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors) (⟨a, ha⟩ : A)

中文:
定义 ofPrime
  签名: (A : 赋值子环 K) (P : 理想 A) [P.是素]
  定义体: ofLE A (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors).toSubring
fun a ha => Subalgebra.mem_toSubring.mpr
      Subalgebra.algebraMap_mem
        (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors) (⟨a, ha⟩ : A)

Depends on / 依赖: Localization, Localization.subalgebra.ofField, P.primeCompl_le_nonZeroDivisors, Subalgebra, Subalgebra.algebraMap_mem, Subalgebra.mem_toSubring.mpr, algebraMap_mem, mem_toSubring, ofField, primeCompl_le_nonZeroDivisors, subalgebra, toSubring
-/
def ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : ValuationSubring K :=
  ofLE A (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors).toSubring
fun a ha => Subalgebra.mem_toSubring.mpr
      Subalgebra.algebraMap_mem
        (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors) (⟨a, ha⟩ : A)

/--
Instance `ofPrimeAlgebra` / 实例 `ofPrimeAlgebra`

English:
instance ofPrimeAlgebra
  signature: (A : ValuationSubring K) (P : Ideal A) [P.IsPrime]
  body: inferInstanceAs Algebra A (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors)

中文:
实例 ofPrimeAlgebra
  签名: (A : 赋值子环 K) (P : 理想 A) [P.是素]
  定义体: inferInstanceAs Algebra A (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors)

Depends on / 依赖: Algebra, Localization, Localization.subalgebra.ofField, P.primeCompl_le_nonZeroDivisors, ofField, primeCompl_le_nonZeroDivisors, subalgebra
-/
instance ofPrimeAlgebra (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    Algebra A (A.ofPrime P) :=
inferInstanceAs Algebra A (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors)

/--
Instance `ofPrime_scalar_tower` / 实例 `ofPrime_scalar_tower`

English:
instance ofPrime_scalar_tower
  signature: (A : ValuationSubring K) (P : Ideal A) [P.IsPrime]
  body: SMulZeroClass.toSMul
    IsScalarTower A (A.ofPrime P) K :=
  IsScalarTower.subalgebra' A K K
    (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors)

中文:
实例 ofPrime_scalar_tower
  签名: (A : 赋值子环 K) (P : 理想 A) [P.是素]
  定义体: SMulZeroClass.toSMul
    IsScalarTower A (A.ofPrime P) K :=
  IsScalarTower.subalgebra' A K K
    (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors)

Depends on / 依赖: SMulZeroClass, SMulZeroClass.toSMul, toSMul
-/
instance ofPrime_scalar_tower (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    letI : SMul A (A.ofPrime P) := SMulZeroClass.toSMul
    IsScalarTower A (A.ofPrime P) K :=
  IsScalarTower.subalgebra' A K K
    (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors)

/--
Instance `ofPrime_localization` / 实例 `ofPrime_localization`

English:
instance ofPrime_localization
  signature: (A : ValuationSubring K) (P : Ideal A) [P.IsPrime]
  body: Localization.subalgebra.isLocalization_ofField K P.primeCompl
    P.primeCompl_le_nonZeroDivisors

中文:
实例 ofPrime_localization
  签名: (A : 赋值子环 K) (P : 理想 A) [P.是素]
  定义体: Localization.subalgebra.isLocalization_ofField K P.primeCompl
    P.primeCompl_le_nonZeroDivisors

Depends on / 依赖: Localization, Localization.subalgebra.isLocalization_ofField, P.primeCompl, P.primeCompl_le_nonZeroDivisors, isLocalization_ofField, primeCompl, primeCompl_le_nonZeroDivisors, subalgebra
-/
instance ofPrime_localization (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    IsLocalization.AtPrime (A.ofPrime P) P :=
  Localization.subalgebra.isLocalization_ofField K P.primeCompl
    P.primeCompl_le_nonZeroDivisors

/--
theorem `le_ofPrime` / 定理 `le_ofPrime`

English:
theorem le_ofPrime
  given: (A : ValuationSubring K) (P : Ideal A) [P.IsPrime]
  statement: A <= ofPrime A P
  proof: fun a ha => Subalgebra.mem_toSubring.mpr Subalgebra.algebraMap_mem _ (⟨a, ha⟩ : A)

中文:
定理 le_ofPrime
  条件: (A : 赋值子环 K) (P : 理想 A) [P.是素]
  结论: A <= ofPrime A P
  证明: fun a ha => Subalgebra.mem_toSubring.mpr Subalgebra.algebraMap_mem _ (⟨a, ha⟩ : A)

Depends on / 依赖: Subalgebra, Subalgebra.algebraMap_mem, Subalgebra.mem_toSubring.mpr, algebraMap_mem, mem_toSubring
-/
theorem le_ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : A <= ofPrime A P :=
fun a ha => Subalgebra.mem_toSubring.mpr Subalgebra.algebraMap_mem _ (⟨a, ha⟩ : A)

/--
theorem `ofPrime_valuation_eq_one_iff_mem_primeCompl` / 定理 `ofPrime_valuation_eq_one_iff_mem_primeCompl`

English:
theorem ofPrime_valuation_eq_one_iff_mem_primeCompl
  statement: (A : ValuationSubring K) (P : Ideal A)
  proof: by
  rw [← IsLocalization.AtPrime.isUnit_to_map_iff (A.ofPrime P) P x]; rw [valuation_eq_one_iff]; rfl

@[simp]

中文:
定理 ofPrime_valuation_eq_one_iff_mem_primeCompl
  结论: (A : 赋值子环 K) (P : 理想 A)
  证明: by
  rw [← IsLocalization.AtPrime.isUnit_to_map_iff (A.ofPrime P) P x]; rw [valuation_eq_one_iff]; rfl

@[simp]

Depends on / 依赖: A.ofPrime, AtPrime, IsLocalization, IsLocalization.AtPrime.isUnit_to_map_iff, isUnit_to_map_iff, ofPrime, valuation_eq_one_iff
-/
theorem ofPrime_valuation_eq_one_iff_mem_primeCompl (A : ValuationSubring K) (P : Ideal A)
    [P.IsPrime] (x : A) : (ofPrime A P).valuation x = 1 ↔ x in P.primeCompl := by
  rw [← IsLocalization.AtPrime.isUnit_to_map_iff (A.ofPrime P) P x]; rw [valuation_eq_one_iff]; rfl

@[simp]
/--
theorem `idealOfLE_ofPrime` / 定理 `idealOfLE_ofPrime`

English:
theorem idealOfLE_ofPrime
  given: (A : ValuationSubring K) (P : Ideal A) [P.IsPrime]
  proof: by
  refine Ideal.ext (fun x => ?_)
  apply IsLocalization.AtPrime.to_map_mem_maximal_iff
  exact isLocalRing (ofPrime A P)

@[simp]

中文:
定理 idealOfLE_ofPrime
  条件: (A : 赋值子环 K) (P : 理想 A) [P.是素]
  证明: by
  refine Ideal.ext (fun x => ?_)
  apply IsLocalization.AtPrime.to_map_mem_maximal_iff
  exact isLocalRing (ofPrime A P)

@[simp]

Depends on / 依赖: AtPrime, Ideal.ext, IsLocalization, IsLocalization.AtPrime.to_map_mem_maximal_iff, isLocalRing, ofPrime, to_map_mem_maximal_iff
-/
theorem idealOfLE_ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    idealOfLE A (ofPrime A P) (le_ofPrime A P) = P := by
  refine Ideal.ext (fun x => ?_)
  apply IsLocalization.AtPrime.to_map_mem_maximal_iff
  exact isLocalRing (ofPrime A P)

@[simp]
/--
theorem `ofPrime_idealOfLE` / 定理 `ofPrime_idealOfLE`

English:
theorem ofPrime_idealOfLE
  given: (R S : ValuationSubring K) (h : R <= S)
  proof: by
  ext x; constructor
  · rintro ⟨a, r, hr, rfl⟩; apply mul_mem; · exact h a.2
    · rw [← valuation_le_one_iff, map_inv₀, ← inv_one, inv_le_inv₀]
      · exact not_lt.1 ((not_iff_not.2 <| valuation_lt_one_iff S _).1 hr)
· simpa [Valuation.pos_iff] using fun hr₀ => hr₀ ▸ hr Ideal.zero_mem (R.idealOfLE S h)
      · exact zero_lt_one
  · intro hx; by_cases hr : x in R; · exact R.le_ofPrime _ hr
    have : x != 0 := fun h => hr (by rw [h]; exact R.zero_mem)
    replace hr := (R.mem_or_inv_mem x).resolve_left hr
    refine ⟨1, ⟨x⁻¹, hr⟩, ?_, ?_⟩
    · simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
        SetLike.mem_coe, idealOfLE, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        not_not]
      change IsUnit (⟨x⁻¹, h hr⟩ : S)
      refine .of_mul_eq_one (⟨x, hx⟩ : S) ?_
      ext
      simp [field]
    · simp

@[simp]

中文:
定理 ofPrime_idealOfLE
  条件: (R S : 赋值子环 K) (h : R <= S)
  证明: by
  ext x; constructor
  · rintro ⟨a, r, hr, rfl⟩; apply mul_mem; · exact h a.2
    · rw [← valuation_le_one_iff, map_inv₀, ← inv_one, inv_le_inv₀]
      · exact not_lt.1 ((not_iff_not.2 <| valuation_lt_one_iff S _).1 hr)
· simpa [Valuation.pos_iff] using fun hr₀ => hr₀ ▸ hr Ideal.zero_mem (R.idealOfLE S h)
      · exact zero_lt_one
  · intro hx; by_cases hr : x in R; · exact R.le_ofPrime _ hr
    have : x != 0 := fun h => hr (by rw [h]; exact R.zero_mem)
    replace hr := (R.mem_or_inv_mem x).resolve_left hr
    refine ⟨1, ⟨x⁻¹, hr⟩, ?_, ?_⟩
    · simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
        SetLike.mem_coe, idealOfLE, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        not_not]
      change IsUnit (⟨x⁻¹, h hr⟩ : S)
      refine .of_mul_eq_one (⟨x, hx⟩ : S) ?_
      ext
      simp [field]
    · simp

@[simp]

Depends on / 依赖: Ideal.zero_mem, R.idealOfLE, R.le_ofPrime, R.mem_or_inv_mem, R.zero_mem, Valuation, Valuation.pos_iff, idealOfLE, inv_one, le_ofPrime, mem_or_inv_mem, mul_mem, not_iff_not, not_lt, pos_iff, replace, resolve_left, valuation_le_one_iff, valuation_lt_one_iff, zero_lt_one
-/
theorem ofPrime_idealOfLE (R S : ValuationSubring K) (h : R <= S) :
    ofPrime R (idealOfLE R S h) = S := by
  ext x; constructor
  · rintro ⟨a, r, hr, rfl⟩; apply mul_mem; · exact h a.2
    · rw [← valuation_le_one_iff, map_inv₀, ← inv_one, inv_le_inv₀]
      · exact not_lt.1 ((not_iff_not.2 <| valuation_lt_one_iff S _).1 hr)
· simpa [Valuation.pos_iff] using fun hr₀ => hr₀ ▸ hr Ideal.zero_mem (R.idealOfLE S h)
      · exact zero_lt_one
  · intro hx; by_cases hr : x in R; · exact R.le_ofPrime _ hr
    have : x != 0 := fun h => hr (by rw [h]; exact R.zero_mem)
    replace hr := (R.mem_or_inv_mem x).resolve_left hr
    refine ⟨1, ⟨x⁻¹, hr⟩, ?_, ?_⟩
    · simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
        SetLike.mem_coe, idealOfLE, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        not_not]
      change IsUnit (⟨x⁻¹, h hr⟩ : S)
      refine .of_mul_eq_one (⟨x, hx⟩ : S) ?_
      ext
      simp [field]
    · simp

@[simp]
/--
theorem `ofPrime_bot` / 定理 `ofPrime_bot`

English:
theorem ofPrime_bot
  statement: A.ofPrime ⊥ = ⊤
  proof: by simp [← idealOfLE_top]

@[simp]

中文:
定理 ofPrime_bot
  结论: A.ofPrime ⊥ = ⊤
  证明: by simp [← idealOfLE_top]

@[simp]

Depends on / 依赖: idealOfLE_top
-/
theorem ofPrime_bot : A.ofPrime ⊥ = ⊤ := by simp [← idealOfLE_top]

@[simp]
/--
theorem `ofPrime_top` / 定理 `ofPrime_top`

English:
theorem ofPrime_top
  statement: A.ofPrime (IsLocalRing.maximalIdeal A) = A
  proof: by simp [← idealOfLE_self]

中文:
定理 ofPrime_top
  结论: A.ofPrime (是局部环.maximalIdeal A) = A
  证明: by simp [← idealOfLE_self]

Depends on / 依赖: IsCountablyGenerated, idealOfLE_self, instIsCountablyGeneratedUniformity
-/
theorem ofPrime_top : A.ofPrime (IsLocalRing.maximalIdeal A) = A := by simp [← idealOfLE_self]

/--
theorem `ofPrime_le_of_le` / 定理 `ofPrime_le_of_le`

English:
theorem ofPrime_le_of_le
  given: (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] (h : P <= Q)
  proof: fun _x ⟨a, s, hs, he⟩ => ⟨a, s, fun c => hs (h c), he⟩

中文:
定理 ofPrime_le_of_le
  条件: (P Q : 理想 A) [P.是素] [Q.是素] (h : P <= Q)
  证明: fun _x ⟨a, s, hs, he⟩ => ⟨a, s, fun c => hs (h c), he⟩
-/
theorem ofPrime_le_of_le (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] (h : P <= Q) :
    ofPrime A Q <= ofPrime A P := fun _x ⟨a, s, hs, he⟩ => ⟨a, s, fun c => hs (h c), he⟩

/--
theorem `idealOfLE_le_of_le` / 定理 `idealOfLE_le_of_le`

English:
theorem idealOfLE_le_of_le
  given: (R S : ValuationSubring K) (hR : A <= R) (hS : A <= S) (h : R <= S)
  proof: fun x hx =>
  (valuation_lt_one_iff R _).2
    (by
      by_contra! c; replace c := monotone_mapOfLE R S h c
      rw [(mapOfLE _ _ _).map_one]; rw [mapOfLE_valuation_apply] at c
      apply not_le_of_gt ((valuation_lt_one_iff S _).1 hx) c)

中文:
定理 idealOfLE_le_of_le
  条件: (R S : 赋值子环 K) (hR : A <= R) (hS : A <= S) (h : R <= S)
  证明: fun x hx =>
  (valuation_lt_one_iff R _).2
    (by
      by_contra! c; replace c := monotone_mapOfLE R S h c
      rw [(mapOfLE _ _ _).map_one]; rw [mapOfLE_valuation_apply] at c
      apply not_le_of_gt ((valuation_lt_one_iff S _).1 hx) c)
-/
theorem idealOfLE_le_of_le (R S : ValuationSubring K) (hR : A <= R) (hS : A <= S) (h : R <= S) :
    idealOfLE A S hS <= idealOfLE A R hR := fun x hx =>
  (valuation_lt_one_iff R _).2
    (by
      by_contra! c; replace c := monotone_mapOfLE R S h c
      rw [(mapOfLE _ _ _).map_one]; rw [mapOfLE_valuation_apply] at c
      apply not_le_of_gt ((valuation_lt_one_iff S _).1 hx) c)

/-- The equivalence between coarsenings of a valuation ring and its prime ideals. -/
@[simps apply]
/--
Definition of `primeSpectrumEquiv` / `primeSpectrumEquiv` 的定义

English:
definition primeSpectrumEquiv
  signature: : PrimeSpectrum A ≃ {S // A <= S} where
  body: ⟨ofPrime A P.asIdeal, le_ofPrime _ _⟩
  invFun S := ⟨idealOfLE _ S S.2, inferInstance⟩
  left_inv P := by ext1; simp
  right_inv S := by ext1; simp

中文:
定义 primeSpectrumEquiv
  签名: : 素谱 A ≃ {S // A <= S} where
  定义体: ⟨ofPrime A P.asIdeal, le_ofPrime _ _⟩
  invFun S := ⟨idealOfLE _ S S.2, inferInstance⟩
  left_inv P := by ext1; simp
  right_inv S := by ext1; simp

Depends on / 依赖: P.asIdeal, asIdeal, le_ofPrime, ofPrime
-/
def primeSpectrumEquiv : PrimeSpectrum A ≃ {S // A <= S} where
  toFun P := ⟨ofPrime A P.asIdeal, le_ofPrime _ _⟩
  invFun S := ⟨idealOfLE _ S S.2, inferInstance⟩
  left_inv P := by ext1; simp
  right_inv S := by ext1; simp

set_option backward.defeqAttrib.useBackward true in
/-- An ordered variant of `primeSpectrumEquiv`. -/
@[simps!]
/--
Definition of `primeSpectrumOrderEquiv` / `primeSpectrumOrderEquiv` 的定义

English:
definition primeSpectrumOrderEquiv
  signature: : (PrimeSpectrum A)ᵒᵈ ≃o {S // A <= S}
  body: { OrderDual.ofDual.trans (primeSpectrumEquiv A) with
    map_rel_iff' {a b} :=
⟨a.rec fun a => b.rec fun b h => by
        simp only [OrderDual.toDual_le_toDual]
        dsimp at h
        have := idealOfLE_le_of_le A _ _ ?_ ?_ h
        · rwa [idealOfLE_ofPrime, idealOfLE_ofPrime] at this
        all_goals exact le_ofPrime A (PrimeSpectrum.asIdeal _),
      fun h => by apply ofPrime_le_of_le; exact h⟩ }

中文:
定义 primeSpectrumOrderEquiv
  签名: : (素谱 A)ᵒᵈ ≃o {S // A <= S}
  定义体: { OrderDual.ofDual.trans (primeSpectrumEquiv A) with
    map_rel_iff' {a b} :=
⟨a.rec fun a => b.rec fun b h => by
        simp only [OrderDual.toDual_le_toDual]
        dsimp at h
        have := idealOfLE_le_of_le A _ _ ?_ ?_ h
        · rwa [idealOfLE_ofPrime, idealOfLE_ofPrime] at this
        all_goals exact le_ofPrime A (PrimeSpectrum.asIdeal _),
      fun h => by apply ofPrime_le_of_le; exact h⟩ }

Depends on / 依赖: OrderDual, OrderDual.ofDual.trans, OrderDual.toDual_le_toDual, PrimeSpectrum, PrimeSpectrum.asIdeal, a.rec, all_goals, asIdeal, b.rec, idealOfLE_le_of_le, idealOfLE_ofPrime, le_ofPrime, map_rel_iff, ofDual, ofPrime_le_of_le, primeSpectrumEquiv, toDual_le_toDual
-/
def primeSpectrumOrderEquiv : (PrimeSpectrum A)ᵒᵈ ≃o {S // A <= S} :=
  { OrderDual.ofDual.trans (primeSpectrumEquiv A) with
    map_rel_iff' {a b} :=
⟨a.rec fun a => b.rec fun b h => by
        simp only [OrderDual.toDual_le_toDual]
        dsimp at h
        have := idealOfLE_le_of_le A _ _ ?_ ?_ h
        · rwa [idealOfLE_ofPrime, idealOfLE_ofPrime] at this
        all_goals exact le_ofPrime A (PrimeSpectrum.asIdeal _),
      fun h => by apply ofPrime_le_of_le; exact h⟩ }

/--
Instance `le_total_ideal` / 实例 `le_total_ideal`

English:
instance le_total_ideal
  signature: : @Std.Total {S // A <= S} (· <= ·)
  body: by
  classical
  let _ : @Std.Total (PrimeSpectrum A) (· <= ·) := ⟨fun ⟨x, _⟩ ⟨y, _⟩ => LE.total.total x y⟩
  exact (primeSpectrumOrderEquiv A).symm.toRelEmbedding.total

中文:
实例 le_total_ideal
  签名: : @Std.全 {S // A <= S} (· <= ·)
  定义体: by
  classical
  let _ : @Std.Total (PrimeSpectrum A) (· <= ·) := ⟨fun ⟨x, _⟩ ⟨y, _⟩ => LE.total.total x y⟩
  exact (primeSpectrumOrderEquiv A).symm.toRelEmbedding.total

Depends on / 依赖: LE.total.total, PrimeSpectrum, PseudoEMetricSpace, PseudoEMetricSpace.induced, Std.Total, Subtype, Subtype.val, classical, induced, primeSpectrumOrderEquiv, symm.toRelEmbedding.total, toRelEmbedding
-/
instance le_total_ideal : @Std.Total {S // A <= S} (· <= ·) := by
  classical
  let _ : @Std.Total (PrimeSpectrum A) (· <= ·) := ⟨fun ⟨x, _⟩ ⟨y, _⟩ => LE.total.total x y⟩
  exact (primeSpectrumOrderEquiv A).symm.toRelEmbedding.total

open scoped Classical in
/--
Instance `linearOrderOverring` / 实例 `linearOrderOverring`

English:
instance linearOrderOverring
  signature: : LinearOrder {S // A <= S} where
  body: (le_total_ideal A).1
  max_def a b := congr_fun₂ sup_eq_maxDefault a b
  toDecidableLE := _

中文:
实例 linearOrderOverring
  签名: : 线性序 {S // A <= S} where
  定义体: (le_total_ideal A).1
  max_def a b := congr_fun₂ sup_eq_maxDefault a b
  toDecidableLE := _

Depends on / 依赖: le_total_ideal
-/
instance linearOrderOverring : LinearOrder {S // A <= S} where
  le_total := (le_total_ideal A).1
  max_def a b := congr_fun₂ sup_eq_maxDefault a b
  toDecidableLE := _

section

variable [Ring.KrullDimLE 1 A] {B : ValuationSubring K}

variable {A} in
/--
theorem `eq_self_or_eq_top_of_le` / 定理 `eq_self_or_eq_top_of_le`

English:
theorem eq_self_or_eq_top_of_le
  given: (hle : A <= B)
  statement: A = B ∨ B = ⊤
  proof: by
  obtain h | h := IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (A.primeSpectrumEquiv.symm ⟨B, hle⟩)
  all_goals
    replace h := congr(primeSpectrumEquiv A $h)
    simp_all

中文:
定理 eq_self_or_eq_top_of_le
  条件: (hle : A <= B)
  结论: A = B ∨ B = ⊤
  证明: by
  obtain h | h := IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (A.primeSpectrumEquiv.symm ⟨B, hle⟩)
  all_goals
    replace h := congr(primeSpectrumEquiv A $h)
    simp_all

Depends on / 依赖: A.primeSpectrumEquiv.symm, IsLocalRing, IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top, KrullDimLE, all_goals, eq_bot_or_eq_top, primeSpectrumEquiv, replace
-/
theorem eq_self_or_eq_top_of_le (hle : A <= B) : A = B ∨ B = ⊤ := by
  obtain h | h := IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (A.primeSpectrumEquiv.symm ⟨B, hle⟩)
  all_goals
    replace h := congr(primeSpectrumEquiv A $h)
    simp_all

/--
theorem `eq_of_le_of_ne_top` / 定理 `eq_of_le_of_ne_top`

English:
theorem eq_of_le_of_ne_top
  given: (hle : A <= B) (hTop : B != ⊤)
  statement: A = B
  proof: by
  obtain h | h := eq_self_or_eq_top_of_le hle <;> simp_all

中文:
定理 eq_of_le_of_ne_top
  条件: (hle : A <= B) (hTop : B != ⊤)
  结论: A = B
  证明: by
  obtain h | h := eq_self_or_eq_top_of_le hle <;> simp_all

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.induced, eq_self_or_eq_top_of_le, induced
-/
theorem eq_of_le_of_ne_top (hle : A <= B) (hTop : B != ⊤) : A = B := by
  obtain h | h := eq_self_or_eq_top_of_le hle <;> simp_all

/--
theorem `eq_of_le_of_ne_self` / 定理 `eq_of_le_of_ne_self`

English:
theorem eq_of_le_of_ne_self
  given: (hle : A <= B) (hne : A != B)
  statement: B = ⊤
  proof: by
  obtain h | h := eq_self_or_eq_top_of_le hle <;> simp_all

中文:
定理 eq_of_le_of_ne_self
  条件: (hle : A <= B) (hne : A != B)
  结论: B = ⊤
  证明: by
  obtain h | h := eq_self_or_eq_top_of_le hle <;> simp_all

Depends on / 依赖: eq_self_or_eq_top_of_le
-/
theorem eq_of_le_of_ne_self (hle : A <= B) (hne : A != B) : B = ⊤ := by
  obtain h | h := eq_self_or_eq_top_of_le hle <;> simp_all

/--
theorem `eq_of_lt` / 定理 `eq_of_lt`

English:
theorem eq_of_lt
  given: (hlt : A < B)
  statement: B = ⊤
  proof: by
  obtain h | h := eq_self_or_eq_top_of_le hlt.le <;> simp_all

中文:
定理 eq_of_lt
  条件: (hlt : A < B)
  结论: B = ⊤
  证明: by
  obtain h | h := eq_self_or_eq_top_of_le hlt.le <;> simp_all

Depends on / 依赖: eq_self_or_eq_top_of_le, hlt.le
-/
theorem eq_of_lt (hlt : A < B) : B = ⊤ := by
  obtain h | h := eq_self_or_eq_top_of_le hlt.le <;> simp_all

end

end Order

end ValuationSubring

namespace Valuation

variable {K}
variable {Γ Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ]
  [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂] (v : Valuation K Γ)
  (v₁ : Valuation K Γ₁) (v₂ : Valuation K Γ₂)

/--
Definition of `valuationSubring` / `valuationSubring` 的定义

English:
definition valuationSubring
  signature: : ValuationSubring K
  body: { v.integer with
    mem_or_inv_mem' := by
      intro x
      rcases val_le_one_or_val_inv_le_one v x with h | h
      exacts [Or.inl h, Or.inr h] }

@[simp]

中文:
定义 valuationSubring
  签名: : 赋值子环 K
  定义体: { v.integer with
    mem_or_inv_mem' := by
      intro x
      rcases val_le_one_or_val_inv_le_one v x with h | h
      exacts [Or.inl h, Or.inr h] }

@[simp]

Depends on / 依赖: Or.inl, Or.inr, exacts, integer, mem_or_inv_mem, v.integer, val_le_one_or_val_inv_le_one
-/
def valuationSubring : ValuationSubring K :=
  { v.integer with
    mem_or_inv_mem' := by
      intro x
      rcases val_le_one_or_val_inv_le_one v x with h | h
      exacts [Or.inl h, Or.inr h] }

@[simp]
/--
theorem `mem_valuationSubring_iff` / 定理 `mem_valuationSubring_iff`

English:
theorem mem_valuationSubring_iff
  given: (x : K)
  statement: x in v.valuationSubring ↔ v x <= 1
  proof: Iff.refl _

中文:
定理 mem_valuationSubring_iff
  条件: (x : K)
  结论: x in v.valuationSubring ↔ v x <= 1
  证明: Iff.refl _

Depends on / 依赖: Iff.refl
-/
theorem mem_valuationSubring_iff (x : K) : x in v.valuationSubring ↔ v x <= 1 := Iff.refl _

/--
theorem `isEquiv_iff_valuationSubring` / 定理 `isEquiv_iff_valuationSubring`

English:
theorem isEquiv_iff_valuationSubring
  proof: by
  constructor
  · intro h; ext x; specialize h x 1; simpa using h
  · intro h; apply isEquiv_of_val_le_one
    intro x
    have : x in v₁.valuationSubring ↔ x in v₂.valuationSubring := by rw [h]
    simpa using this

中文:
定理 isEquiv_iff_valuationSubring
  证明: by
  constructor
  · intro h; ext x; specialize h x 1; simpa using h
  · intro h; apply isEquiv_of_val_le_one
    intro x
    have : x in v₁.valuationSubring ↔ x in v₂.valuationSubring := by rw [h]
    simpa using this

Depends on / 依赖: isEquiv_of_val_le_one, specialize, valuationSubring
-/
theorem isEquiv_iff_valuationSubring :
    v₁.IsEquiv v₂ ↔ v₁.valuationSubring = v₂.valuationSubring := by
  constructor
  · intro h; ext x; specialize h x 1; simpa using h
  · intro h; apply isEquiv_of_val_le_one
    intro x
    have : x in v₁.valuationSubring ↔ x in v₂.valuationSubring := by rw [h]
    simpa using this

/--
theorem `isEquiv_valuation_valuationSubring` / 定理 `isEquiv_valuation_valuationSubring`

English:
theorem isEquiv_valuation_valuationSubring
  statement: v.IsEquiv v.valuationSubring.valuation
  proof: by
  rw [isEquiv_iff_val_le_one]
  intro x
  rw [ValuationSubring.valuation_le_one_iff]; rw [mem_valuationSubring_iff]

@[simp]

中文:
定理 isEquiv_valuation_valuationSubring
  结论: v.Is等价 v.valuationSubring.valuation
  证明: by
  rw [isEquiv_iff_val_le_one]
  intro x
  rw [ValuationSubring.valuation_le_one_iff]; rw [mem_valuationSubring_iff]

@[simp]

Depends on / 依赖: ValuationSubring, ValuationSubring.valuation_le_one_iff, isEquiv_iff_val_le_one, mem_valuationSubring_iff, valuation_le_one_iff
-/
theorem isEquiv_valuation_valuationSubring : v.IsEquiv v.valuationSubring.valuation := by
  rw [isEquiv_iff_val_le_one]
  intro x
  rw [ValuationSubring.valuation_le_one_iff]; rw [mem_valuationSubring_iff]

@[simp]
/--
theorem `isNontrivial_valuation_valuationSubring_iff` / 定理 `isNontrivial_valuation_valuationSubring_iff`

English:
theorem isNontrivial_valuation_valuationSubring_iff
  proof: (isEquiv_valuation_valuationSubring v).isNontrivial_iff.symm

中文:
定理 isNontrivial_valuation_valuationSubring_iff
  证明: (isEquiv_valuation_valuationSubring v).isNontrivial_iff.symm

Depends on / 依赖: isEquiv_valuation_valuationSubring, isNontrivial_iff, isNontrivial_iff.symm
-/
theorem isNontrivial_valuation_valuationSubring_iff :
    v.valuationSubring.valuation.IsNontrivial ↔ v.IsNontrivial :=
  (isEquiv_valuation_valuationSubring v).isNontrivial_iff.symm

/--
lemma `valuationSubring.integers` / 引理 `valuationSubring.integers`

English:
lemma valuationSubring.integers
  statement: v.Integers v.valuationSubring
  proof: Valuation.integer.integers _

@[simp]

中文:
引理 valuationSubring.integers
  结论: v.整数egers v.valuationSubring
  证明: Valuation.integer.integers _

@[simp]

Depends on / 依赖: Valuation, Valuation.integer.integers, integer, integers
-/
lemma valuationSubring.integers : v.Integers v.valuationSubring :=
  Valuation.integer.integers _

@[simp]
/--
theorem `valuationSubring_eq_top_iff` / 定理 `valuationSubring_eq_top_iff`

English:
theorem valuationSubring_eq_top_iff
  statement: v.valuationSubring = ⊤ ↔ ¬ v.IsNontrivial
  proof: by
  simp [ValuationSubring.eq_top_iff]

中文:
定理 valuationSubring_eq_top_iff
  结论: v.valuationSubring = ⊤ ↔ ¬ v.是非平凡
  证明: by
  simp [ValuationSubring.eq_top_iff]

Depends on / 依赖: ValuationSubring, ValuationSubring.eq_top_iff, eq_top_iff
-/
theorem valuationSubring_eq_top_iff : v.valuationSubring = ⊤ ↔ ¬ v.IsNontrivial := by
  simp [ValuationSubring.eq_top_iff]

end Valuation

namespace ValuationSubring

variable {K}
variable (A : ValuationSubring K)

@[simp]
/--
theorem `valuationSubring_valuation` / 定理 `valuationSubring_valuation`

English:
theorem valuationSubring_valuation
  statement: A.valuation.valuationSubring = A
  proof: by
  ext; rw [← A.valuation_le_one_iff]; rfl

中文:
定理 valuationSubring_valuation
  结论: A.valuation.valuationSubring = A
  证明: by
  ext; rw [← A.valuation_le_one_iff]; rfl

Depends on / 依赖: A.valuation_le_one_iff, valuation_le_one_iff
-/
theorem valuationSubring_valuation : A.valuation.valuationSubring = A := by
  ext; rw [← A.valuation_le_one_iff]; rfl

/--
theorem `integer_valuation` / 定理 `integer_valuation`

English:
theorem integer_valuation
  statement: A.valuation.integer = A.toSubring
  proof: congr(($A.valuationSubring_valuation).toSubring)

中文:
定理 integer_valuation
  结论: A.valuation.integer = A.toSubring
  证明: congr(($A.valuationSubring_valuation).toSubring)

Depends on / 依赖: A.valuationSubring_valuation, toSubring, valuationSubring_valuation
-/
theorem integer_valuation : A.valuation.integer = A.toSubring :=
  congr(($A.valuationSubring_valuation).toSubring)

section UnitGroup

/--
Definition of `unitGroup` / `unitGroup` 的定义

English:
definition unitGroup
  signature: : Subgroup Kˣ
  body: (A.valuation.toMonoidWithZeroHom.toMonoidHom.comp (Units.coeHom K)).ker

@[simp]

中文:
定义 unitGroup
  签名: : 子群 Kˣ
  定义体: (A.valuation.toMonoidWithZeroHom.toMonoidHom.comp (Units.coeHom K)).ker

@[simp]

Depends on / 依赖: A.valuation.toMonoidWithZeroHom.toMonoidHom.comp, Units.coeHom, coeHom, toMonoidHom, toMonoidWithZeroHom, valuation
-/
def unitGroup : Subgroup Kˣ :=
  (A.valuation.toMonoidWithZeroHom.toMonoidHom.comp (Units.coeHom K)).ker

@[simp]
/--
theorem `mem_unitGroup_iff` / 定理 `mem_unitGroup_iff`

English:
theorem mem_unitGroup_iff
  given: (x : Kˣ)
  statement: x in A.unitGroup ↔ A.valuation x = 1
  proof: Iff.rfl

中文:
定理 mem_unitGroup_iff
  条件: (x : Kˣ)
  结论: x in A.unitGroup ↔ A.valuation x = 1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_unitGroup_iff (x : Kˣ) : x in A.unitGroup ↔ A.valuation x = 1 := Iff.rfl

/--
Definition of `unitGroupMulEquiv` / `unitGroupMulEquiv` 的定义

English:
definition unitGroupMulEquiv
  signature: : A.unitGroup ≃* Aˣ where
  body: { val := ⟨(x : Kˣ), mem_of_valuation_le_one A _ x.prop.le⟩
      inv := ⟨((x⁻¹ : A.unitGroup) : Kˣ), mem_of_valuation_le_one _ _ x⁻¹.prop.le⟩
      val_inv := Subtype.ext (by simp)
      inv_val := Subtype.ext (by simp) }
  invFun x := ⟨Units.map A.subtype.toMonoidHom x, A.valuation_unit x⟩
  map_mul' a b := by ext; rfl

@[simp]

中文:
定义 unitGroupMulEquiv
  签名: : A.unitGroup ≃* Aˣ where
  定义体: { val := ⟨(x : Kˣ), mem_of_valuation_le_one A _ x.prop.le⟩
      inv := ⟨((x⁻¹ : A.unitGroup) : Kˣ), mem_of_valuation_le_one _ _ x⁻¹.prop.le⟩
      val_inv := Subtype.ext (by simp)
      inv_val := Subtype.ext (by simp) }
  invFun x := ⟨Units.map A.subtype.toMonoidHom x, A.valuation_unit x⟩
  map_mul' a b := by ext; rfl

@[simp]

Depends on / 依赖: A.subtype.toMonoidHom, A.unitGroup, A.valuation_unit, Subtype, Subtype.ext, Units.map, invFun, inv_val, map_mul, mem_of_valuation_le_one, prop.le, subtype, toMonoidHom, unitGroup, val_inv, valuation_unit, x.prop.le
-/
def unitGroupMulEquiv : A.unitGroup ≃* Aˣ where
  toFun x :=
    { val := ⟨(x : Kˣ), mem_of_valuation_le_one A _ x.prop.le⟩
      inv := ⟨((x⁻¹ : A.unitGroup) : Kˣ), mem_of_valuation_le_one _ _ x⁻¹.prop.le⟩
      val_inv := Subtype.ext (by simp)
      inv_val := Subtype.ext (by simp) }
  invFun x := ⟨Units.map A.subtype.toMonoidHom x, A.valuation_unit x⟩
  map_mul' a b := by ext; rfl

@[simp]
/--
theorem `coe_unitGroupMulEquiv_apply` / 定理 `coe_unitGroupMulEquiv_apply`

English:
theorem coe_unitGroupMulEquiv_apply
  given: (a : A.unitGroup)
  proof: rfl

@[simp]

中文:
定理 coe_unitGroupMulEquiv_apply
  条件: (a : A.unitGroup)
  证明: rfl

@[simp]
-/
theorem coe_unitGroupMulEquiv_apply (a : A.unitGroup) :
    ((A.unitGroupMulEquiv a : A) : K) = ((a : Kˣ) : K) := rfl

@[simp]
/--
theorem `coe_unitGroupMulEquiv_symm_apply` / 定理 `coe_unitGroupMulEquiv_symm_apply`

English:
theorem coe_unitGroupMulEquiv_symm_apply
  given: (a : Aˣ)
  statement: ((A.unitGroupMulEquiv.symm a : Kˣ) : K) = a
  proof: rfl

中文:
定理 coe_unitGroupMulEquiv_symm_apply
  条件: (a : Aˣ)
  结论: ((A.unitGroupMulEquiv.symm a : Kˣ) : K) = a
  证明: rfl
-/
theorem coe_unitGroupMulEquiv_symm_apply (a : Aˣ) : ((A.unitGroupMulEquiv.symm a : Kˣ) : K) = a :=
  rfl

/--
theorem `unitGroup_le_unitGroup` / 定理 `unitGroup_le_unitGroup`

English:
theorem unitGroup_le_unitGroup
  given: {A B : ValuationSubring K}
  statement: A.unitGroup <= B.unitGroup ↔ A <= B
  proof: by
  constructor
  · intro h x hx
    rw [← A.valuation_le_one_iff x]; rw [le_iff_lt_or_eq] at hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    by_cases h_2 : 1 + x = 0
    · simp only [← add_eq_zero_iff_neg_eq.1 h_2, neg_mem _ _ (one_mem _)]
    rcases hx with hx | hx
    · have := h (show Units.mk0 _ h_2 in A.unitGroup from A.valuation.map_one_add_of_lt hx)
      simpa using
        B.add_mem _ _ (show 1 + x in B from SetLike.coe_mem (B.unitGroupMulEquiv ⟨_, this⟩ : B))
          (B.neg_mem _ B.one_mem)
    · have := h (show Units.mk0 x h_1 in A.unitGroup from hx)
      exact SetLike.coe_mem (B.unitGroupMulEquiv ⟨_, this⟩ : B)
  · rintro h x (hx : A.valuation x = 1)
    apply_fun A.mapOfLE B h at hx
    simpa using hx

中文:
定理 unitGroup_le_unitGroup
  条件: {A B : 赋值子环 K}
  结论: A.unitGroup <= B.unitGroup ↔ A <= B
  证明: by
  constructor
  · intro h x hx
    rw [← A.valuation_le_one_iff x]; rw [le_iff_lt_or_eq] at hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    by_cases h_2 : 1 + x = 0
    · simp only [← add_eq_zero_iff_neg_eq.1 h_2, neg_mem _ _ (one_mem _)]
    rcases hx with hx | hx
    · have := h (show Units.mk0 _ h_2 in A.unitGroup from A.valuation.map_one_add_of_lt hx)
      simpa using
        B.add_mem _ _ (show 1 + x in B from SetLike.coe_mem (B.unitGroupMulEquiv ⟨_, this⟩ : B))
          (B.neg_mem _ B.one_mem)
    · have := h (show Units.mk0 x h_1 in A.unitGroup from hx)
      exact SetLike.coe_mem (B.unitGroupMulEquiv ⟨_, this⟩ : B)
  · rintro h x (hx : A.valuation x = 1)
    apply_fun A.mapOfLE B h at hx
    simpa using hx

Depends on / 依赖: A.unitGroup, A.valuation.map_one_add_of_lt, A.valuation_le_one_iff, B.add_mem, B.neg_mem, B.one_mem, B.unitGroupMulEquiv, SetLike, SetLike.coe_mem, Units.mk0, add_eq_zero_iff_neg_eq, add_mem, coe_mem, le_iff_lt_or_eq, map_one_add_of_lt, neg_mem, one_mem, unitGroup, unitGroupMulEquiv, valuation
-/
theorem unitGroup_le_unitGroup {A B : ValuationSubring K} : A.unitGroup <= B.unitGroup ↔ A <= B := by
  constructor
  · intro h x hx
    rw [← A.valuation_le_one_iff x]; rw [le_iff_lt_or_eq] at hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    by_cases h_2 : 1 + x = 0
    · simp only [← add_eq_zero_iff_neg_eq.1 h_2, neg_mem _ _ (one_mem _)]
    rcases hx with hx | hx
    · have := h (show Units.mk0 _ h_2 in A.unitGroup from A.valuation.map_one_add_of_lt hx)
      simpa using
        B.add_mem _ _ (show 1 + x in B from SetLike.coe_mem (B.unitGroupMulEquiv ⟨_, this⟩ : B))
          (B.neg_mem _ B.one_mem)
    · have := h (show Units.mk0 x h_1 in A.unitGroup from hx)
      exact SetLike.coe_mem (B.unitGroupMulEquiv ⟨_, this⟩ : B)
  · rintro h x (hx : A.valuation x = 1)
    apply_fun A.mapOfLE B h at hx
    simpa using hx

/--
theorem `unitGroup_injective` / 定理 `unitGroup_injective`

English:
theorem unitGroup_injective
  statement: Function.Injective (unitGroup : ValuationSubring K -> Subgroup _)
  proof: fun A B h => by simpa only [le_antisymm_iff, unitGroup_le_unitGroup] using h

中文:
定理 unitGroup_injective
  结论: 函数.单射 (unitGroup : 赋值子环 K -> 子群 _)
  证明: fun A B h => by simpa only [le_antisymm_iff, unitGroup_le_unitGroup] using h

Depends on / 依赖: le_antisymm_iff, unitGroup_le_unitGroup
-/
theorem unitGroup_injective : Function.Injective (unitGroup : ValuationSubring K -> Subgroup _) :=
  fun A B h => by simpa only [le_antisymm_iff, unitGroup_le_unitGroup] using h

/--
theorem `eq_iff_unitGroup` / 定理 `eq_iff_unitGroup`

English:
theorem eq_iff_unitGroup
  given: {A B : ValuationSubring K}
  statement: A = B ↔ A.unitGroup = B.unitGroup
  proof: unitGroup_injective.eq_iff.symm

中文:
定理 eq_iff_unitGroup
  条件: {A B : 赋值子环 K}
  结论: A = B ↔ A.unitGroup = B.unitGroup
  证明: unitGroup_injective.eq_iff.symm

Depends on / 依赖: eq_iff, unitGroup_injective, unitGroup_injective.eq_iff.symm
-/
theorem eq_iff_unitGroup {A B : ValuationSubring K} : A = B ↔ A.unitGroup = B.unitGroup :=
  unitGroup_injective.eq_iff.symm

/--
Definition of `unitGroupOrderEmbedding` / `unitGroupOrderEmbedding` 的定义

English:
definition unitGroupOrderEmbedding
  signature: : ValuationSubring K ↪o Subgroup Kˣ where
  body: A.unitGroup
  inj' := unitGroup_injective
  map_rel_iff' {_A _B} := unitGroup_le_unitGroup

中文:
定义 unitGroupOrderEmbedding
  签名: : 赋值子环 K ↪o 子群 Kˣ where
  定义体: A.unitGroup
  inj' := unitGroup_injective
  map_rel_iff' {_A _B} := unitGroup_le_unitGroup

Depends on / 依赖: A.unitGroup, unitGroup
-/
def unitGroupOrderEmbedding : ValuationSubring K ↪o Subgroup Kˣ where
  toFun A := A.unitGroup
  inj' := unitGroup_injective
  map_rel_iff' {_A _B} := unitGroup_le_unitGroup

/--
theorem `unitGroup_strictMono` / 定理 `unitGroup_strictMono`

English:
theorem unitGroup_strictMono
  statement: StrictMono (unitGroup : ValuationSubring K -> Subgroup _)
  proof: unitGroupOrderEmbedding.strictMono

中文:
定理 unitGroup_strictMono
  结论: 严格递增 (unitGroup : 赋值子环 K -> 子群 _)
  证明: unitGroupOrderEmbedding.strictMono

Depends on / 依赖: strictMono, unitGroupOrderEmbedding, unitGroupOrderEmbedding.strictMono
-/
theorem unitGroup_strictMono : StrictMono (unitGroup : ValuationSubring K -> Subgroup _) :=
  unitGroupOrderEmbedding.strictMono

end UnitGroup

section nonunits

/--
Definition of `nonunits` / `nonunits` 的定义

English:
definition nonunits
  signature: : NonUnitalSubring K where
  body: {x | A.valuation x < 1}
  mul_mem' ha hb := (mul_lt_mul'' (Set.mem_ofPred.mp ha) (Set.mem_ofPred.mp hb)
    zero_le zero_le).trans_eq <| mul_one _
  add_mem' ha hb := (A.valuation.map_add ..).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  neg_mem' h := (A.valuation.map_neg _).trans_lt h

中文:
定义 nonunits
  签名: : NonUnital子环 K where
  定义体: {x | A.valuation x < 1}
  mul_mem' ha hb := (mul_lt_mul'' (Set.mem_ofPred.mp ha) (Set.mem_ofPred.mp hb)
    zero_le zero_le).trans_eq <| mul_one _
  add_mem' ha hb := (A.valuation.map_add ..).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  neg_mem' h := (A.valuation.map_neg _).trans_lt h

Depends on / 依赖: A.valuation, valuation
-/
def nonunits : NonUnitalSubring K where
  carrier := {x | A.valuation x < 1}
  mul_mem' ha hb := (mul_lt_mul'' (Set.mem_ofPred.mp ha) (Set.mem_ofPred.mp hb)
    zero_le zero_le).trans_eq <| mul_one _
  add_mem' ha hb := (A.valuation.map_add ..).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  neg_mem' h := (A.valuation.map_neg _).trans_lt h

/--
theorem `mem_nonunits_iff` / 定理 `mem_nonunits_iff`

English:
theorem mem_nonunits_iff
  given: {x : K}
  statement: x in A.nonunits ↔ A.valuation x < 1
  proof: Iff.rfl

中文:
定理 mem_nonunits_iff
  条件: {x : K}
  结论: x in A.nonunits ↔ A.valuation x < 1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_nonunits_iff {x : K} : x in A.nonunits ↔ A.valuation x < 1 :=
  Iff.rfl

/--
theorem `mem_nonunits_iff_or` / 定理 `mem_nonunits_iff_or`

English:
theorem mem_nonunits_iff_or
  given: {x : K}
  statement: x in A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A
  proof: by
  rw [← valuation_le_one_iff]; rw [← or_congr_right' fun h => (A.valuation.one_le_val_iff h).not]; rw [← lt_iff_not_ge]; rw [← mem_nonunits_iff]; rw [or_iff_right_of_imp]
  rintro rfl
  exact A.nonunits.zero_mem

中文:
定理 mem_nonunits_iff_or
  条件: {x : K}
  结论: x in A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A
  证明: by
  rw [← valuation_le_one_iff]; rw [← or_congr_right' fun h => (A.valuation.one_le_val_iff h).not]; rw [← lt_iff_not_ge]; rw [← mem_nonunits_iff]; rw [or_iff_right_of_imp]
  rintro rfl
  exact A.nonunits.zero_mem

Depends on / 依赖: A.nonunits.zero_mem, A.valuation.one_le_val_iff, lt_iff_not_ge, mem_nonunits_iff, nonunits, one_le_val_iff, or_congr_right, or_iff_right_of_imp, valuation, valuation_le_one_iff, zero_mem
-/
theorem mem_nonunits_iff_or {x : K} : x in A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A := by
  rw [← valuation_le_one_iff]; rw [← or_congr_right' fun h => (A.valuation.one_le_val_iff h).not]; rw [← lt_iff_not_ge]; rw [← mem_nonunits_iff]; rw [or_iff_right_of_imp]
  rintro rfl
  exact A.nonunits.zero_mem

/--
theorem `inv_mem_nonunits_iff` / 定理 `inv_mem_nonunits_iff`

English:
theorem inv_mem_nonunits_iff
  given: {x : K}
  statement: x⁻¹ in A.nonunits ↔ x = 0 ∨ x ∉ A
  proof: by
  rw [mem_nonunits_iff_or]; rw [inv_inv]; rw [inv_eq_zero]

中文:
定理 inv_mem_nonunits_iff
  条件: {x : K}
  结论: x⁻¹ in A.nonunits ↔ x = 0 ∨ x ∉ A
  证明: by
  rw [mem_nonunits_iff_or]; rw [inv_inv]; rw [inv_eq_zero]

Depends on / 依赖: inv_eq_zero, inv_inv, mem_nonunits_iff_or
-/
theorem inv_mem_nonunits_iff {x : K} : x⁻¹ in A.nonunits ↔ x = 0 ∨ x ∉ A := by
  rw [mem_nonunits_iff_or]; rw [inv_inv]; rw [inv_eq_zero]

/--
theorem `nonunits_le_nonunits` / 定理 `nonunits_le_nonunits`

English:
theorem nonunits_le_nonunits
  given: {A B : ValuationSubring K}
  statement: B.nonunits <= A.nonunits ↔ A <= B
  proof: by
  constructor
  · intro h x hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    rw [← valuation_le_one_iff]; rw [← not_lt]; rw [Valuation.one_lt_val_iff _ h_1] at hx ⊢
    by_contra h_2; exact hx (h h_2)
  · intro h x hx
    by_contra h_1; exact not_lt.2 (monotone_mapOfLE _ _ h (not_lt.1 h_1)) hx

中文:
定理 nonunits_le_nonunits
  条件: {A B : 赋值子环 K}
  结论: B.nonunits <= A.nonunits ↔ A <= B
  证明: by
  constructor
  · intro h x hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    rw [← valuation_le_one_iff]; rw [← not_lt]; rw [Valuation.one_lt_val_iff _ h_1] at hx ⊢
    by_contra h_2; exact hx (h h_2)
  · intro h x hx
    by_contra h_1; exact not_lt.2 (monotone_mapOfLE _ _ h (not_lt.1 h_1)) hx

Depends on / 依赖: Valuation, Valuation.one_lt_val_iff, monotone_mapOfLE, not_lt, one_lt_val_iff, valuation_le_one_iff, zero_mem
-/
theorem nonunits_le_nonunits {A B : ValuationSubring K} : B.nonunits <= A.nonunits ↔ A <= B := by
  constructor
  · intro h x hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    rw [← valuation_le_one_iff]; rw [← not_lt]; rw [Valuation.one_lt_val_iff _ h_1] at hx ⊢
    by_contra h_2; exact hx (h h_2)
  · intro h x hx
    by_contra h_1; exact not_lt.2 (monotone_mapOfLE _ _ h (not_lt.1 h_1)) hx

/--
theorem `nonunits_injective` / 定理 `nonunits_injective`

English:
theorem nonunits_injective
  proof: fun A B h => by simpa only [le_antisymm_iff, nonunits_le_nonunits] using h.symm

中文:
定理 nonunits_injective
  证明: fun A B h => by simpa only [le_antisymm_iff, nonunits_le_nonunits] using h.symm

Depends on / 依赖: h.symm, le_antisymm_iff, nonunits_le_nonunits
-/
theorem nonunits_injective :
    Function.Injective (nonunits : ValuationSubring K -> NonUnitalSubring _) :=
  fun A B h => by simpa only [le_antisymm_iff, nonunits_le_nonunits] using h.symm

/--
theorem `nonunits_inj` / 定理 `nonunits_inj`

English:
theorem nonunits_inj
  given: {A B : ValuationSubring K}
  statement: A.nonunits = B.nonunits ↔ A = B
  proof: nonunits_injective.eq_iff

中文:
定理 nonunits_inj
  条件: {A B : 赋值子环 K}
  结论: A.nonunits = B.nonunits ↔ A = B
  证明: nonunits_injective.eq_iff

Depends on / 依赖: eq_iff, nonunits_injective, nonunits_injective.eq_iff
-/
theorem nonunits_inj {A B : ValuationSubring K} : A.nonunits = B.nonunits ↔ A = B :=
  nonunits_injective.eq_iff

/--
Definition of `nonunitsOrderEmbedding` / `nonunitsOrderEmbedding` 的定义

English:
definition nonunitsOrderEmbedding
  signature: : ValuationSubring K ↪o (NonUnitalSubring K)ᵒᵈ where
  body: A.nonunits
  inj' := nonunits_injective
  map_rel_iff' {_A _B} := nonunits_le_nonunits

中文:
定义 nonunitsOrderEmbedding
  签名: : 赋值子环 K ↪o (NonUnital子环 K)ᵒᵈ where
  定义体: A.nonunits
  inj' := nonunits_injective
  map_rel_iff' {_A _B} := nonunits_le_nonunits

Depends on / 依赖: A.nonunits, nonunits
-/
def nonunitsOrderEmbedding : ValuationSubring K ↪o (NonUnitalSubring K)ᵒᵈ where
  toFun A := A.nonunits
  inj' := nonunits_injective
  map_rel_iff' {_A _B} := nonunits_le_nonunits

variable {A}

/--
theorem `coe_mem_nonunits_iff` / 定理 `coe_mem_nonunits_iff`

English:
theorem coe_mem_nonunits_iff
  given: {a : A}
  statement: (a : K) in A.nonunits ↔ a in IsLocalRing.maximalIdeal A
  proof: (valuation_lt_one_iff _ _).symm

中文:
定理 coe_mem_nonunits_iff
  条件: {a : A}
  结论: (a : K) in A.nonunits ↔ a in 是局部环.maximalIdeal A
  证明: (valuation_lt_one_iff _ _).symm

Depends on / 依赖: valuation_lt_one_iff
-/
theorem coe_mem_nonunits_iff {a : A} : (a : K) in A.nonunits ↔ a in IsLocalRing.maximalIdeal A :=
  (valuation_lt_one_iff _ _).symm

/--
theorem `nonunits_le` / 定理 `nonunits_le`

English:
theorem nonunits_le
  statement: A.nonunits <= A.toNonUnitalSubring
  proof: fun _a ha =>
  (A.valuation_le_one_iff _).mp (A.mem_nonunits_iff.mp ha).le

中文:
定理 nonunits_le
  结论: A.nonunits <= A.toNonUnitalSubring
  证明: fun _a ha =>
  (A.valuation_le_one_iff _).mp (A.mem_nonunits_iff.mp ha).le
-/
theorem nonunits_le : A.nonunits <= A.toNonUnitalSubring := fun _a ha =>
  (A.valuation_le_one_iff _).mp (A.mem_nonunits_iff.mp ha).le

/--
theorem `nonunits_subset` / 定理 `nonunits_subset`

English:
theorem nonunits_subset
  statement: (A.nonunits : Set K) subseteq A
  proof: nonunits_le

中文:
定理 nonunits_subset
  结论: (A.nonunits : 集合 K) subseteq A
  证明: nonunits_le

Depends on / 依赖: nonunits_le
-/
theorem nonunits_subset : (A.nonunits : Set K) subseteq A :=
  nonunits_le

/--
theorem `mem_nonunits_iff_exists_mem_maximalIdeal` / 定理 `mem_nonunits_iff_exists_mem_maximalIdeal`

English:
theorem mem_nonunits_iff_exists_mem_maximalIdeal
  given: {a : K}
  proof: ⟨fun h => ⟨nonunits_subset h, coe_mem_nonunits_iff.mp h⟩, fun ⟨_, h⟩ =>
    coe_mem_nonunits_iff.mpr h⟩

中文:
定理 mem_nonunits_iff_存在_mem_maximalIdeal
  条件: {a : K}
  证明: ⟨fun h => ⟨nonunits_subset h, coe_mem_nonunits_iff.mp h⟩, fun ⟨_, h⟩ =>
    coe_mem_nonunits_iff.mpr h⟩

Depends on / 依赖: coe_mem_nonunits_iff, coe_mem_nonunits_iff.mp, coe_mem_nonunits_iff.mpr, nonunits_subset
-/
theorem mem_nonunits_iff_exists_mem_maximalIdeal {a : K} :
    a in A.nonunits ↔ exists ha, (⟨a, ha⟩ : A) in IsLocalRing.maximalIdeal A :=
  ⟨fun h => ⟨nonunits_subset h, coe_mem_nonunits_iff.mp h⟩, fun ⟨_, h⟩ =>
    coe_mem_nonunits_iff.mpr h⟩

/--
theorem `image_maximalIdeal` / 定理 `image_maximalIdeal`

English:
theorem image_maximalIdeal
  statement: ((↑) : A -> K) '' IsLocalRing.maximalIdeal A = A.nonunits
  proof: by
  ext a
  simp only [Set.mem_image, SetLike.mem_coe, mem_nonunits_iff_exists_mem_maximalIdeal]
  rw [Subtype.exists]
  simp_rw [exists_and_right, exists_eq_right]

中文:
定理 image_maximalIdeal
  结论: ((↑) : A -> K) '' 是局部环.maximalIdeal A = A.nonunits
  证明: by
  ext a
  simp only [Set.mem_image, SetLike.mem_coe, mem_nonunits_iff_exists_mem_maximalIdeal]
  rw [Subtype.exists]
  simp_rw [exists_and_right, exists_eq_right]

Depends on / 依赖: Set.mem_image, SetLike, SetLike.mem_coe, Subtype, Subtype.exists, exists_and_right, exists_eq_right, mem_coe, mem_image, mem_nonunits_iff_exists_mem_maximalIdeal, simp_rw
-/
theorem image_maximalIdeal : ((↑) : A -> K) '' IsLocalRing.maximalIdeal A = A.nonunits := by
  ext a
  simp only [Set.mem_image, SetLike.mem_coe, mem_nonunits_iff_exists_mem_maximalIdeal]
  rw [Subtype.exists]
  simp_rw [exists_and_right, exists_eq_right]

end nonunits

section PrincipalUnitGroup

/--
Definition of `principalUnitGroup` / `principalUnitGroup` 的定义

English:
definition principalUnitGroup
  signature: : Subgroup Kˣ where
  body: {x | A.valuation (x - 1) < 1}
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_ofPred] at ha hb ⊢
    refine lt_of_le_of_lt ?_ (max_lt hb ha)
    rw [← one_mul (A.valuation (b - 1))]; rw [← A.valuation.map_one_add_of_lt ha]; rw [add_sub_cancel]; rw [← Valuation.map_mul]; rw [mul_sub_one]; rw [← sub_add_sub_cancel]
    exact A.valuation.map_add _ _
  one_mem' := by simp
  inv_mem' := by
    dsimp
    intro a ha
    conv =>
      lhs
      rw [← mul_one (A.valuation _)]; rw [← A.valuation.map_one_add_of_lt ha]
    rwa [add_sub_cancel, ← Valuation.map_mul, sub_mul, Units.inv_mul, ← neg_sub, one_mul,
      Valuation.map_neg]

中文:
定义 principalUnitGroup
  签名: : 子群 Kˣ where
  定义体: {x | A.valuation (x - 1) < 1}
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_ofPred] at ha hb ⊢
    refine lt_of_le_of_lt ?_ (max_lt hb ha)
    rw [← one_mul (A.valuation (b - 1))]; rw [← A.valuation.map_one_add_of_lt ha]; rw [add_sub_cancel]; rw [← Valuation.map_mul]; rw [mul_sub_one]; rw [← sub_add_sub_cancel]
    exact A.valuation.map_add _ _
  one_mem' := by simp
  inv_mem' := by
    dsimp
    intro a ha
    conv =>
      lhs
      rw [← mul_one (A.valuation _)]; rw [← A.valuation.map_one_add_of_lt ha]
    rwa [add_sub_cancel, ← Valuation.map_mul, sub_mul, Units.inv_mul, ← neg_sub, one_mul,
      Valuation.map_neg]

Depends on / 依赖: A.valuation, valuation
-/
def principalUnitGroup : Subgroup Kˣ where
  carrier := {x | A.valuation (x - 1) < 1}
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_ofPred] at ha hb ⊢
    refine lt_of_le_of_lt ?_ (max_lt hb ha)
    rw [← one_mul (A.valuation (b - 1))]; rw [← A.valuation.map_one_add_of_lt ha]; rw [add_sub_cancel]; rw [← Valuation.map_mul]; rw [mul_sub_one]; rw [← sub_add_sub_cancel]
    exact A.valuation.map_add _ _
  one_mem' := by simp
  inv_mem' := by
    dsimp
    intro a ha
    conv =>
      lhs
      rw [← mul_one (A.valuation _)]; rw [← A.valuation.map_one_add_of_lt ha]
    rwa [add_sub_cancel, ← Valuation.map_mul, sub_mul, Units.inv_mul, ← neg_sub, one_mul,
      Valuation.map_neg]

/--
theorem `principal_units_le_units` / 定理 `principal_units_le_units`

English:
theorem principal_units_le_units
  statement: A.principalUnitGroup <= A.unitGroup
  proof: fun a h => by
  simpa only [add_sub_cancel] using! A.valuation.map_one_add_of_lt h

中文:
定理 principal_units_le_units
  结论: A.principalUnitGroup <= A.unitGroup
  证明: fun a h => by
  simpa only [add_sub_cancel] using! A.valuation.map_one_add_of_lt h

Depends on / 依赖: A.valuation.map_one_add_of_lt, add_sub_cancel, map_one_add_of_lt, valuation
-/
theorem principal_units_le_units : A.principalUnitGroup <= A.unitGroup := fun a h => by
  simpa only [add_sub_cancel] using! A.valuation.map_one_add_of_lt h

/--
theorem `mem_principalUnitGroup_iff` / 定理 `mem_principalUnitGroup_iff`

English:
theorem mem_principalUnitGroup_iff
  given: (x : Kˣ)
  proof: Iff.rfl

中文:
定理 mem_principalUnitGroup_iff
  条件: (x : Kˣ)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_principalUnitGroup_iff (x : Kˣ) :
    x in A.principalUnitGroup ↔ A.valuation ((x : K) - 1) < 1 :=
  Iff.rfl

/--
theorem `principalUnitGroup_le_principalUnitGroup` / 定理 `principalUnitGroup_le_principalUnitGroup`

English:
theorem principalUnitGroup_le_principalUnitGroup
  given: {A B : ValuationSubring K}
  proof: by
  constructor
  · intro h x hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    by_cases h_2 : x⁻¹ + 1 = 0
    · rw [add_eq_zero_iff_eq_neg, inv_eq_iff_eq_inv, inv_neg, inv_one] at h_2
      simpa only [h_2] using B.neg_mem _ B.one_mem
    · rw [← valuation_le_one_iff, ← not_lt, Valuation.one_lt_val_iff _ h_1,
        ← add_sub_cancel_right x⁻¹, ← Units.val_mk0 h_2, ← mem_principalUnitGroup_iff] at hx ⊢
      simpa only [hx] using @h (Units.mk0 (x⁻¹ + 1) h_2)
  · intro h x hx
    by_contra h_1; exact not_lt.2 (monotone_mapOfLE _ _ h (not_lt.1 h_1)) hx

中文:
定理 principalUnitGroup_le_principalUnitGroup
  条件: {A B : 赋值子环 K}
  证明: by
  constructor
  · intro h x hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    by_cases h_2 : x⁻¹ + 1 = 0
    · rw [add_eq_zero_iff_eq_neg, inv_eq_iff_eq_inv, inv_neg, inv_one] at h_2
      simpa only [h_2] using B.neg_mem _ B.one_mem
    · rw [← valuation_le_one_iff, ← not_lt, Valuation.one_lt_val_iff _ h_1,
        ← add_sub_cancel_right x⁻¹, ← Units.val_mk0 h_2, ← mem_principalUnitGroup_iff] at hx ⊢
      simpa only [hx] using @h (Units.mk0 (x⁻¹ + 1) h_2)
  · intro h x hx
    by_contra h_1; exact not_lt.2 (monotone_mapOfLE _ _ h (not_lt.1 h_1)) hx

Depends on / 依赖: B.neg_mem, B.one_mem, Units.mk0, Units.val_mk0, Valuation, Valuation.one_lt_val_iff, add_eq_zero_iff_eq_neg, add_sub_cancel_right, inv_eq_iff_eq_inv, inv_neg, inv_one, mem_principalUnitGroup_iff, monotone_mapOfLE, neg_mem, not_lt, one_lt_val_iff, one_mem, val_mk0, valuation_le_one_iff, zero_mem
-/
theorem principalUnitGroup_le_principalUnitGroup {A B : ValuationSubring K} :
    B.principalUnitGroup <= A.principalUnitGroup ↔ A <= B := by
  constructor
  · intro h x hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    by_cases h_2 : x⁻¹ + 1 = 0
    · rw [add_eq_zero_iff_eq_neg, inv_eq_iff_eq_inv, inv_neg, inv_one] at h_2
      simpa only [h_2] using B.neg_mem _ B.one_mem
    · rw [← valuation_le_one_iff, ← not_lt, Valuation.one_lt_val_iff _ h_1,
        ← add_sub_cancel_right x⁻¹, ← Units.val_mk0 h_2, ← mem_principalUnitGroup_iff] at hx ⊢
      simpa only [hx] using @h (Units.mk0 (x⁻¹ + 1) h_2)
  · intro h x hx
    by_contra h_1; exact not_lt.2 (monotone_mapOfLE _ _ h (not_lt.1 h_1)) hx

/--
theorem `principalUnitGroup_injective` / 定理 `principalUnitGroup_injective`

English:
theorem principalUnitGroup_injective
  proof: fun A B h => by
  simpa [le_antisymm_iff, principalUnitGroup_le_principalUnitGroup] using h.symm

中文:
定理 principalUnitGroup_injective
  证明: fun A B h => by
  simpa [le_antisymm_iff, principalUnitGroup_le_principalUnitGroup] using h.symm

Depends on / 依赖: h.symm, le_antisymm_iff, principalUnitGroup_le_principalUnitGroup
-/
theorem principalUnitGroup_injective :
    Function.Injective (principalUnitGroup : ValuationSubring K -> Subgroup _) := fun A B h => by
  simpa [le_antisymm_iff, principalUnitGroup_le_principalUnitGroup] using h.symm

/--
theorem `eq_iff_principalUnitGroup` / 定理 `eq_iff_principalUnitGroup`

English:
theorem eq_iff_principalUnitGroup
  given: {A B : ValuationSubring K}
  proof: principalUnitGroup_injective.eq_iff.symm

中文:
定理 eq_iff_principalUnitGroup
  条件: {A B : 赋值子环 K}
  证明: principalUnitGroup_injective.eq_iff.symm

Depends on / 依赖: eq_iff, principalUnitGroup_injective, principalUnitGroup_injective.eq_iff.symm
-/
theorem eq_iff_principalUnitGroup {A B : ValuationSubring K} :
    A = B ↔ A.principalUnitGroup = B.principalUnitGroup :=
  principalUnitGroup_injective.eq_iff.symm

/--
Definition of `principalUnitGroupOrderEmbedding` / `principalUnitGroupOrderEmbedding` 的定义

English:
definition principalUnitGroupOrderEmbedding
  signature: : ValuationSubring K ↪o (Subgroup Kˣ)ᵒᵈ where
  body: A.principalUnitGroup
  inj' := principalUnitGroup_injective
  map_rel_iff' {_A _B} := principalUnitGroup_le_principalUnitGroup

中文:
定义 principalUnitGroupOrderEmbedding
  签名: : 赋值子环 K ↪o (子群 Kˣ)ᵒᵈ where
  定义体: A.principalUnitGroup
  inj' := principalUnitGroup_injective
  map_rel_iff' {_A _B} := principalUnitGroup_le_principalUnitGroup

Depends on / 依赖: A.principalUnitGroup, principalUnitGroup
-/
def principalUnitGroupOrderEmbedding : ValuationSubring K ↪o (Subgroup Kˣ)ᵒᵈ where
  toFun A := A.principalUnitGroup
  inj' := principalUnitGroup_injective
  map_rel_iff' {_A _B} := principalUnitGroup_le_principalUnitGroup

/--
theorem `coe_mem_principalUnitGroup_iff` / 定理 `coe_mem_principalUnitGroup_iff`

English:
theorem coe_mem_principalUnitGroup_iff
  given: {x : A.unitGroup}
  proof: by
  rw [MonoidHom.mem_ker]; rw [Units.ext_iff]
  let π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
  convert_to! _ ↔ π _ = 1
  rw [← π.map_one]; rw [← sub_eq_zero]; rw [← π.map_sub]; rw [Ideal.Quotient.eq_zero_iff_mem]; rw [valuation_lt_one_iff]
  simp [mem_principalUnitGroup_iff]

中文:
定理 coe_mem_principalUnitGroup_iff
  条件: {x : A.unitGroup}
  证明: by
  rw [MonoidHom.mem_ker]; rw [Units.ext_iff]
  let π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
  convert_to! _ ↔ π _ = 1
  rw [← π.map_one]; rw [← sub_eq_zero]; rw [← π.map_sub]; rw [Ideal.Quotient.eq_zero_iff_mem]; rw [valuation_lt_one_iff]
  simp [mem_principalUnitGroup_iff]

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk, IsLocalRing, IsLocalRing.maximalIdeal, MonoidHom, MonoidHom.mem_ker, Quotient, Units.ext_iff, convert_to, eq_zero_iff_mem, ext_iff, map_one, map_sub, maximalIdeal, mem_ker, mem_principalUnitGroup_iff, sub_eq_zero, valuation_lt_one_iff
-/
theorem coe_mem_principalUnitGroup_iff {x : A.unitGroup} :
    (x : Kˣ) in A.principalUnitGroup ↔
      A.unitGroupMulEquiv x in (Units.map (IsLocalRing.residue A).toMonoidHom).ker := by
  rw [MonoidHom.mem_ker]; rw [Units.ext_iff]
  let π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
  convert_to! _ ↔ π _ = 1
  rw [← π.map_one]; rw [← sub_eq_zero]; rw [← π.map_sub]; rw [Ideal.Quotient.eq_zero_iff_mem]; rw [valuation_lt_one_iff]
  simp [mem_principalUnitGroup_iff]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `principalUnitGroupEquiv` / `principalUnitGroupEquiv` 的定义

English:
definition principalUnitGroupEquiv
  signature: :
  body: ⟨A.unitGroupMulEquiv ⟨_, A.principal_units_le_units x.2⟩,
      A.coe_mem_principalUnitGroup_iff.1 x.2⟩
  invFun x :=
    ⟨A.unitGroupMulEquiv.symm x, by
      rw [A.coe_mem_principalUnitGroup_iff]; simp⟩
  left_inv x := by simp
  right_inv x := by simp
  map_mul' _ _ := rfl

中文:
定义 principalUnitGroupEquiv
  签名: :
  定义体: ⟨A.unitGroupMulEquiv ⟨_, A.principal_units_le_units x.2⟩,
      A.coe_mem_principalUnitGroup_iff.1 x.2⟩
  invFun x :=
    ⟨A.unitGroupMulEquiv.symm x, by
      rw [A.coe_mem_principalUnitGroup_iff]; simp⟩
  left_inv x := by simp
  right_inv x := by simp
  map_mul' _ _ := rfl

Depends on / 依赖: A.coe_mem_principalUnitGroup_iff, A.principal_units_le_units, A.unitGroupMulEquiv, A.unitGroupMulEquiv.symm, coe_mem_principalUnitGroup_iff, invFun, left_inv, map_mul, principal_units_le_units, right_inv, unitGroupMulEquiv
-/
def principalUnitGroupEquiv :
    A.principalUnitGroup ≃* (Units.map (IsLocalRing.residue A).toMonoidHom).ker where
  toFun x :=
    ⟨A.unitGroupMulEquiv ⟨_, A.principal_units_le_units x.2⟩,
      A.coe_mem_principalUnitGroup_iff.1 x.2⟩
  invFun x :=
    ⟨A.unitGroupMulEquiv.symm x, by
      rw [A.coe_mem_principalUnitGroup_iff]; simp⟩
  left_inv x := by simp
  right_inv x := by simp
  map_mul' _ _ := rfl

/--
theorem `principalUnitGroupEquiv_apply` / 定理 `principalUnitGroupEquiv_apply`

English:
theorem principalUnitGroupEquiv_apply
  given: (a : A.principalUnitGroup)
  proof: rfl

中文:
定理 principalUnitGroupEquiv_apply
  条件: (a : A.principalUnitGroup)
  证明: rfl
-/
theorem principalUnitGroupEquiv_apply (a : A.principalUnitGroup) :
    (((principalUnitGroupEquiv A a : Aˣ) : A) : K) = (a : Kˣ) :=
  rfl

/--
theorem `principalUnitGroup_symm_apply` / 定理 `principalUnitGroup_symm_apply`

English:
theorem principalUnitGroup_symm_apply
  given: (a : (Units.map (IsLocalRing.residue A).toMonoidHom).ker)
  proof: rfl

中文:
定理 principalUnitGroup_symm_apply
  条件: (a : (单位群.map (是局部环.residue A).toMonoidHom).ker)
  证明: rfl
-/
theorem principalUnitGroup_symm_apply (a : (Units.map (IsLocalRing.residue A).toMonoidHom).ker) :
    ((A.principalUnitGroupEquiv.symm a : Kˣ) : K) = ((a : Aˣ) : A) :=
  rfl

/--
Definition of `unitGroupToResidueFieldUnits` / `unitGroupToResidueFieldUnits` 的定义

English:
definition unitGroupToResidueFieldUnits
  signature: : A.unitGroup ->* (IsLocalRing.ResidueField A)ˣ
  body: MonoidHom.comp (Units.map <| (Ideal.Quotient.mk _).toMonoidHom) A.unitGroupMulEquiv.toMonoidHom

@[simp]

中文:
定义 unitGroupToResidueFieldUnits
  签名: : A.unitGroup ->* (是局部环.ResidueField A)ˣ
  定义体: MonoidHom.comp (Units.map <| (Ideal.Quotient.mk _).toMonoidHom) A.unitGroupMulEquiv.toMonoidHom

@[simp]

Depends on / 依赖: A.unitGroupMulEquiv.toMonoidHom, Ideal.Quotient.mk, MonoidHom, MonoidHom.comp, Quotient, Units.map, toMonoidHom, unitGroupMulEquiv
-/
def unitGroupToResidueFieldUnits : A.unitGroup ->* (IsLocalRing.ResidueField A)ˣ :=
  MonoidHom.comp (Units.map <| (Ideal.Quotient.mk _).toMonoidHom) A.unitGroupMulEquiv.toMonoidHom

@[simp]
/--
theorem `coe_unitGroupToResidueFieldUnits_apply` / 定理 `coe_unitGroupToResidueFieldUnits_apply`

English:
theorem coe_unitGroupToResidueFieldUnits_apply
  given: (x : A.unitGroup)
  proof: rfl

中文:
定理 coe_unitGroupToResidueFieldUnits_apply
  条件: (x : A.unitGroup)
  证明: rfl
-/
theorem coe_unitGroupToResidueFieldUnits_apply (x : A.unitGroup) :
    (A.unitGroupToResidueFieldUnits x : IsLocalRing.ResidueField A) =
      Ideal.Quotient.mk _ (A.unitGroupMulEquiv x : A) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ker_unitGroupToResidueFieldUnits` / 定理 `ker_unitGroupToResidueFieldUnits`

English:
theorem ker_unitGroupToResidueFieldUnits
  proof: by
  ext
  simp_rw [Subgroup.mem_comap, Subgroup.coe_subtype, coe_mem_principalUnitGroup_iff,
    unitGroupToResidueFieldUnits, IsLocalRing.residue, RingHom.toMonoidHom_eq_coe,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.mem_ker, MonoidHom.coe_comp, MonoidHom.coe_coe,
    Function.comp_apply]

中文:
定理 ker_unitGroupToResidueFieldUnits
  证明: by
  ext
  simp_rw [Subgroup.mem_comap, Subgroup.coe_subtype, coe_mem_principalUnitGroup_iff,
    unitGroupToResidueFieldUnits, IsLocalRing.residue, RingHom.toMonoidHom_eq_coe,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.mem_ker, MonoidHom.coe_comp, MonoidHom.coe_coe,
    Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, IsLocalRing, IsLocalRing.residue, MonoidHom, MonoidHom.coe_coe, MonoidHom.coe_comp, MonoidHom.mem_ker, MulEquiv, MulEquiv.toMonoidHom_eq_coe, RingHom, RingHom.toMonoidHom_eq_coe, Subgroup, Subgroup.coe_subtype, Subgroup.mem_comap, coe_coe, coe_comp, coe_mem_principalUnitGroup_iff, coe_subtype, comp_apply
-/
theorem ker_unitGroupToResidueFieldUnits :
    A.unitGroupToResidueFieldUnits.ker = A.principalUnitGroup.comap A.unitGroup.subtype := by
  ext
  simp_rw [Subgroup.mem_comap, Subgroup.coe_subtype, coe_mem_principalUnitGroup_iff,
    unitGroupToResidueFieldUnits, IsLocalRing.residue, RingHom.toMonoidHom_eq_coe,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.mem_ker, MonoidHom.coe_comp, MonoidHom.coe_coe,
    Function.comp_apply]

/--
theorem `surjective_unitGroupToResidueFieldUnits` / 定理 `surjective_unitGroupToResidueFieldUnits`

English:
theorem surjective_unitGroupToResidueFieldUnits
  proof: IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective
.comp (MulEquiv.surjective _) (inferInstanceAs (IsLocalHom (IsLocalRing.residue A)))

中文:
定理 surjective_unitGroupToResidueFieldUnits
  证明: IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective
.comp (MulEquiv.surjective _) (inferInstanceAs (IsLocalHom (IsLocalRing.residue A)))

Depends on / 依赖: Ideal.Quotient.mk_surjective, IsLocalHom, IsLocalRing, IsLocalRing.residue, IsLocalRing.surjective_units_map_of_local_ringHom, MulEquiv, MulEquiv.surjective, Quotient, mk_surjective, residue, surjective, surjective_units_map_of_local_ringHom
-/
theorem surjective_unitGroupToResidueFieldUnits :
    Function.Surjective A.unitGroupToResidueFieldUnits :=
  IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective
.comp (MulEquiv.surjective _) (inferInstanceAs (IsLocalHom (IsLocalRing.residue A)))

/--
Definition of `unitsModPrincipalUnitsEquivResidueFieldUnits` / `unitsModPrincipalUnitsEquivResidueFieldUnits` 的定义

English:
definition unitsModPrincipalUnitsEquivResidueFieldUnits
  signature: :
  body: QuotientGroup.liftEquiv _ A.surjective_unitGroupToResidueFieldUnits
    A.ker_unitGroupToResidueFieldUnits.symm

中文:
定义 unitsModPrincipalUnitsEquivResidueFieldUnits
  签名: :
  定义体: QuotientGroup.liftEquiv _ A.surjective_unitGroupToResidueFieldUnits
    A.ker_unitGroupToResidueFieldUnits.symm

Depends on / 依赖: A.ker_unitGroupToResidueFieldUnits.symm, A.surjective_unitGroupToResidueFieldUnits, QuotientGroup, QuotientGroup.liftEquiv, ker_unitGroupToResidueFieldUnits, liftEquiv, surjective_unitGroupToResidueFieldUnits
-/
def unitsModPrincipalUnitsEquivResidueFieldUnits :
    A.unitGroup ⧸ A.principalUnitGroup.comap A.unitGroup.subtype ≃* (IsLocalRing.ResidueField A)ˣ :=
  QuotientGroup.liftEquiv _ A.surjective_unitGroupToResidueFieldUnits
    A.ker_unitGroupToResidueFieldUnits.symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk` / 定理 `unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk`

English:
theorem unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk
  proof: rfl

中文:
定理 unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk
  证明: rfl
-/
theorem unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk :
    (A.unitsModPrincipalUnitsEquivResidueFieldUnits : _ ⧸ Subgroup.comap _ _ ->* _).comp
        (QuotientGroup.mk' (A.principalUnitGroup.subgroupOf A.unitGroup)) =
      A.unitGroupToResidueFieldUnits := rfl

/--
theorem `unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk_apply` / 定理 `unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk_apply`

English:
theorem unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk_apply
  proof: rfl

中文:
定理 unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk_apply
  证明: rfl
-/
theorem unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk_apply
    (x : A.unitGroup) :
    A.unitsModPrincipalUnitsEquivResidueFieldUnits.toMonoidHom (QuotientGroup.mk x) =
      A.unitGroupToResidueFieldUnits x := rfl

end PrincipalUnitGroup

/-! ### Pointwise actions

This transfers the action from `Subring.pointwiseMulAction`, noting that it only applies when
the action is by a group. Notably this provides an instances when `G` is `K ≃+* K`.

These instances are in the `Pointwise` locale.

The lemmas in this section are copied from the file `Mathlib/Algebra/Ring/Subring/Pointwise.lean`;
try to keep these in sync.
-/


section PointwiseActions

open scoped Pointwise

variable {G : Type*} [Group G] [MulSemiringAction G K]

/-- The action on a valuation subring corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `pointwiseHasSMul` / `pointwiseHasSMul` 的定义

English:
definition pointwiseHasSMul
  signature: : SMul G (ValuationSubring K) where
  body: -- TODO: if we add `ValuationSubring.map` at a later date, we should use it here
    { g • S.toSubring with
      mem_or_inv_mem' := fun x =>
        (mem_or_inv_mem S (g⁻¹ • x)).imp Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr fun h =>
Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr by rwa [smul_inv''] }

scoped[Pointwise] attribute [instance] ValuationSubring.pointwiseHasSMul

中文:
定义 pointwiseHasSMul
  签名: : 标量乘法 G (赋值子环 K) where
  定义体: -- TODO: if we add `ValuationSubring.map` at a later date, we should use it here
    { g • S.toSubring with
      mem_or_inv_mem' := fun x =>
        (mem_or_inv_mem S (g⁻¹ • x)).imp Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr fun h =>
Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr by rwa [smul_inv''] }

scoped[Pointwise] attribute [instance] ValuationSubring.pointwiseHasSMul

Depends on / 依赖: ValuationSubring, ValuationSubring.map, should
-/
def pointwiseHasSMul : SMul G (ValuationSubring K) where
  smul g S := -- TODO: if we add `ValuationSubring.map` at a later date, we should use it here
    { g • S.toSubring with
      mem_or_inv_mem' := fun x =>
        (mem_or_inv_mem S (g⁻¹ • x)).imp Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr fun h =>
Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr by rwa [smul_inv''] }

scoped[Pointwise] attribute [instance] ValuationSubring.pointwiseHasSMul

open scoped Pointwise

@[simp]
/--
theorem `coe_pointwise_smul` / 定理 `coe_pointwise_smul`

English:
theorem coe_pointwise_smul
  given: (g : G) (S : ValuationSubring K)
  statement: ↑(g • S) = g • (S : Set K)
  proof: rfl

@[simp]

中文:
定理 coe_pointwise_smul
  条件: (g : G) (S : 赋值子环 K)
  结论: ↑(g • S) = g • (S : 集合 K)
  证明: rfl

@[simp]
-/
theorem coe_pointwise_smul (g : G) (S : ValuationSubring K) : ↑(g • S) = g • (S : Set K) := rfl

@[simp]
/--
theorem `pointwise_smul_toSubring` / 定理 `pointwise_smul_toSubring`

English:
theorem pointwise_smul_toSubring
  given: (g : G) (S : ValuationSubring K)
  proof: rfl

中文:
定理 pointwise_smul_toSubring
  条件: (g : G) (S : 赋值子环 K)
  证明: rfl
-/
theorem pointwise_smul_toSubring (g : G) (S : ValuationSubring K) :
    (g • S).toSubring = g • S.toSubring := rfl

/-- The action on a valuation subring corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.

This is a stronger version of `ValuationSubring.pointwiseSMul`. -/
@[instance_reducible]
/--
Definition of `pointwiseMulAction` / `pointwiseMulAction` 的定义

English:
definition pointwiseMulAction
  signature: : MulAction G (ValuationSubring K)
  body: toSubring_injective.mulAction toSubring pointwise_smul_toSubring

scoped[Pointwise] attribute [instance] ValuationSubring.pointwiseMulAction

中文:
定义 pointwiseMulAction
  签名: : 乘法作用 G (赋值子环 K)
  定义体: toSubring_injective.mulAction toSubring pointwise_smul_toSubring

scoped[Pointwise] attribute [instance] ValuationSubring.pointwiseMulAction

Depends on / 依赖: mulAction, pointwise_smul_toSubring, toSubring, toSubring_injective, toSubring_injective.mulAction
-/
def pointwiseMulAction : MulAction G (ValuationSubring K) :=
  toSubring_injective.mulAction toSubring pointwise_smul_toSubring

scoped[Pointwise] attribute [instance] ValuationSubring.pointwiseMulAction

open scoped Pointwise

/--
theorem `smul_mem_pointwise_smul` / 定理 `smul_mem_pointwise_smul`

English:
theorem smul_mem_pointwise_smul
  given: (g : G) (x : K) (S : ValuationSubring K)
  statement: x in S -> g • x in g • S
  proof: (Set.smul_mem_smul_set : _ -> _ in g • (S : Set K))

中文:
定理 smul_mem_pointwise_smul
  条件: (g : G) (x : K) (S : 赋值子环 K)
  结论: x in S -> g • x in g • S
  证明: (Set.smul_mem_smul_set : _ -> _ in g • (S : Set K))

Depends on / 依赖: Set.smul_mem_smul_set, smul_mem_smul_set
-/
theorem smul_mem_pointwise_smul (g : G) (x : K) (S : ValuationSubring K) : x in S -> g • x in g • S :=
  (Set.smul_mem_smul_set : _ -> _ in g • (S : Set K))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CovariantClass G (ValuationSubring K) HSMul.hSMul LE.le
  body: ⟨fun _ _ _ => Set.image_mono⟩

中文:
实例 :
  签名: 协变类 G (赋值子环 K) 异质标量乘法.hSMul LE.le
  定义体: ⟨fun _ _ _ => Set.image_mono⟩

Depends on / 依赖: Set.image_mono, image_mono
-/
instance : CovariantClass G (ValuationSubring K) HSMul.hSMul LE.le :=
  ⟨fun _ _ _ => Set.image_mono⟩

/--
theorem `mem_smul_pointwise_iff_exists` / 定理 `mem_smul_pointwise_iff_exists`

English:
theorem mem_smul_pointwise_iff_exists
  given: (g : G) (x : K) (S : ValuationSubring K)
  proof: (Set.mem_smul_set : x in g • (S : Set K) ↔ _)

中文:
定理 mem_smul_pointwise_iff_存在
  条件: (g : G) (x : K) (S : 赋值子环 K)
  证明: (Set.mem_smul_set : x in g • (S : Set K) ↔ _)

Depends on / 依赖: Set.mem_smul_set, mem_smul_set
-/
theorem mem_smul_pointwise_iff_exists (g : G) (x : K) (S : ValuationSubring K) :
    x in g • S ↔ exists s : K, s in S ∧ g • s = x :=
  (Set.mem_smul_set : x in g • (S : Set K) ↔ _)

/--
Instance `pointwise_central_scalar` / 实例 `pointwise_central_scalar`

English:
instance pointwise_central_scalar
  signature: [MulSemiringAction Gᵐᵒᵖ K] [IsCentralScalar G K]
  body: ⟨fun g S => toSubring_injective op_smul_eq_smul g S.toSubring⟩

@[simp]

中文:
实例 pointwise_central_scalar
  签名: [MulSemiring作用 Gᵐᵒᵖ K] [中心标量 G K]
  定义体: ⟨fun g S => toSubring_injective op_smul_eq_smul g S.toSubring⟩

@[simp]

Depends on / 依赖: S.toSubring, op_smul_eq_smul, toSubring, toSubring_injective
-/
instance pointwise_central_scalar [MulSemiringAction Gᵐᵒᵖ K] [IsCentralScalar G K] :
    IsCentralScalar G (ValuationSubring K) :=
⟨fun g S => toSubring_injective op_smul_eq_smul g S.toSubring⟩

@[simp]
/--
theorem `smul_mem_pointwise_smul_iff` / 定理 `smul_mem_pointwise_smul_iff`

English:
theorem smul_mem_pointwise_smul_iff
  given: {g : G} {S : ValuationSubring K} {x : K}
  proof: Set.smul_mem_smul_set_iff

中文:
定理 smul_mem_pointwise_smul_iff
  条件: {g : G} {S : 赋值子环 K} {x : K}
  证明: Set.smul_mem_smul_set_iff

Depends on / 依赖: Set.smul_mem_smul_set_iff, smul_mem_smul_set_iff
-/
theorem smul_mem_pointwise_smul_iff {g : G} {S : ValuationSubring K} {x : K} :
    g • x in g • S ↔ x in S := Set.smul_mem_smul_set_iff

/--
theorem `mem_pointwise_smul_iff_inv_smul_mem` / 定理 `mem_pointwise_smul_iff_inv_smul_mem`

English:
theorem mem_pointwise_smul_iff_inv_smul_mem
  given: {g : G} {S : ValuationSubring K} {x : K}
  proof: Set.mem_smul_set_iff_inv_smul_mem

中文:
定理 mem_pointwise_smul_iff_inv_smul_mem
  条件: {g : G} {S : 赋值子环 K} {x : K}
  证明: Set.mem_smul_set_iff_inv_smul_mem

Depends on / 依赖: Set.mem_smul_set_iff_inv_smul_mem, mem_smul_set_iff_inv_smul_mem
-/
theorem mem_pointwise_smul_iff_inv_smul_mem {g : G} {S : ValuationSubring K} {x : K} :
    x in g • S ↔ g⁻¹ • x in S := Set.mem_smul_set_iff_inv_smul_mem

/--
theorem `mem_inv_pointwise_smul_iff` / 定理 `mem_inv_pointwise_smul_iff`

English:
theorem mem_inv_pointwise_smul_iff
  given: {g : G} {S : ValuationSubring K} {x : K}
  proof: Set.mem_inv_smul_set_iff

@[simp]

中文:
定理 mem_inv_pointwise_smul_iff
  条件: {g : G} {S : 赋值子环 K} {x : K}
  证明: Set.mem_inv_smul_set_iff

@[simp]

Depends on / 依赖: Set.mem_inv_smul_set_iff, mem_inv_smul_set_iff
-/
theorem mem_inv_pointwise_smul_iff {g : G} {S : ValuationSubring K} {x : K} :
    x in g⁻¹ • S ↔ g • x in S := Set.mem_inv_smul_set_iff

@[simp]
/--
theorem `pointwise_smul_le_pointwise_smul_iff` / 定理 `pointwise_smul_le_pointwise_smul_iff`

English:
theorem pointwise_smul_le_pointwise_smul_iff
  given: {g : G} {S T : ValuationSubring K}
  proof: Set.smul_set_subset_smul_set_iff

中文:
定理 pointwise_smul_le_pointwise_smul_iff
  条件: {g : G} {S T : 赋值子环 K}
  证明: Set.smul_set_subset_smul_set_iff

Depends on / 依赖: Set.smul_set_subset_smul_set_iff, smul_set_subset_smul_set_iff
-/
theorem pointwise_smul_le_pointwise_smul_iff {g : G} {S T : ValuationSubring K} :
    g • S <= g • T ↔ S <= T := Set.smul_set_subset_smul_set_iff

/--
theorem `pointwise_smul_subset_iff` / 定理 `pointwise_smul_subset_iff`

English:
theorem pointwise_smul_subset_iff
  given: {g : G} {S T : ValuationSubring K}
  statement: g • S <= T ↔ S <= g⁻¹ • T
  proof: Set.smul_set_subset_iff_subset_inv_smul_set

中文:
定理 pointwise_smul_subset_iff
  条件: {g : G} {S T : 赋值子环 K}
  结论: g • S <= T ↔ S <= g⁻¹ • T
  证明: Set.smul_set_subset_iff_subset_inv_smul_set

Depends on / 依赖: Set.smul_set_subset_iff_subset_inv_smul_set, smul_set_subset_iff_subset_inv_smul_set
-/
theorem pointwise_smul_subset_iff {g : G} {S T : ValuationSubring K} : g • S <= T ↔ S <= g⁻¹ • T :=
  Set.smul_set_subset_iff_subset_inv_smul_set

/--
theorem `subset_pointwise_smul_iff` / 定理 `subset_pointwise_smul_iff`

English:
theorem subset_pointwise_smul_iff
  given: {g : G} {S T : ValuationSubring K}
  statement: S <= g • T ↔ g⁻¹ • S <= T
  proof: Set.subset_smul_set_iff

中文:
定理 subset_pointwise_smul_iff
  条件: {g : G} {S T : 赋值子环 K}
  结论: S <= g • T ↔ g⁻¹ • S <= T
  证明: Set.subset_smul_set_iff

Depends on / 依赖: Set.subset_smul_set_iff, subset_smul_set_iff
-/
theorem subset_pointwise_smul_iff {g : G} {S T : ValuationSubring K} : S <= g • T ↔ g⁻¹ • S <= T :=
  Set.subset_smul_set_iff

end PointwiseActions

section

variable {L J : Type*} [Field L] [Field J]

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (A : ValuationSubring L) (f : K ->+* L)
  body: { A.toSubring.comap f with mem_or_inv_mem' := fun k => by simp [ValuationSubring.mem_or_inv_mem] }

@[simp]

中文:
定义 comap
  签名: (A : 赋值子环 L) (f : K ->+* L)
  定义体: { A.toSubring.comap f with mem_or_inv_mem' := fun k => by simp [ValuationSubring.mem_or_inv_mem] }

@[simp]

Depends on / 依赖: A.toSubring.comap, ValuationSubring, ValuationSubring.mem_or_inv_mem, mem_or_inv_mem, toSubring
-/
def comap (A : ValuationSubring L) (f : K ->+* L) : ValuationSubring K :=
  { A.toSubring.comap f with mem_or_inv_mem' := fun k => by simp [ValuationSubring.mem_or_inv_mem] }

@[simp]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (A : ValuationSubring L) (f : K ->+* L)
  statement: (A.comap f : Set K) = f ⁻¹' A
  proof: rfl

@[simp]

中文:
定理 coe_comap
  条件: (A : 赋值子环 L) (f : K ->+* L)
  结论: (A.comap f : 集合 K) = f ⁻¹' A
  证明: rfl

@[simp]

Depends on / 依赖: EMetricSpace, EMetricSpace.induced, Subtype, Subtype.coe_injective, Subtype.val, coe_injective, induced
-/
theorem coe_comap (A : ValuationSubring L) (f : K ->+* L) : (A.comap f : Set K) = f ⁻¹' A := rfl

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {A : ValuationSubring L} {f : K ->+* L} {x : K}
  statement: x in A.comap f ↔ f x in A
  proof: Iff.rfl

中文:
定理 mem_comap
  条件: {A : 赋值子环 L} {f : K ->+* L} {x : K}
  结论: x in A.comap f ↔ f x in A
  证明: Iff.rfl

Depends on / 依赖: EMetricSpace, EMetricSpace.induced, Iff.rfl, MulOpposite, MulOpposite.unop, MulOpposite.unop_injective, induced, unop_injective
-/
theorem mem_comap {A : ValuationSubring L} {f : K ->+* L} {x : K} : x in A.comap f ↔ f x in A :=
  Iff.rfl

/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (A : ValuationSubring J) (g : L ->+* J) (f : K ->+* L)
  proof: rfl

中文:
定理 comap_comap
  条件: (A : 赋值子环 J) (g : L ->+* J) (f : K ->+* L)
  证明: rfl

Depends on / 依赖: EMetricSpace, EMetricSpace.induced, ULift.down, ULift.down_injective, down_injective, induced
-/
theorem comap_comap (A : ValuationSubring J) (g : L ->+* J) (f : K ->+* L) :
    (A.comap g).comap f = A.comap (g.comp f) := rfl

end

end ValuationSubring

namespace Valuation

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (x : Kˣ)

/--
theorem `mem_unitGroup_iff` / 定理 `mem_unitGroup_iff`

English:
theorem mem_unitGroup_iff
  statement: x in v.valuationSubring.unitGroup ↔ v x = 1
  proof: IsEquiv.eq_one_iff_eq_one (Valuation.isEquiv_valuation_valuationSubring _).symm

中文:
定理 mem_unitGroup_iff
  结论: x in v.valuationSubring.unitGroup ↔ v x = 1
  证明: IsEquiv.eq_one_iff_eq_one (Valuation.isEquiv_valuation_valuationSubring _).symm

Depends on / 依赖: IsEquiv, IsEquiv.eq_one_iff_eq_one, Valuation, Valuation.isEquiv_valuation_valuationSubring, eq_one_iff_eq_one, isEquiv_valuation_valuationSubring
-/
theorem mem_unitGroup_iff : x in v.valuationSubring.unitGroup ↔ v x = 1 :=
  IsEquiv.eq_one_iff_eq_one (Valuation.isEquiv_valuation_valuationSubring _).symm

/--
theorem `mem_maximalIdeal_iff` / 定理 `mem_maximalIdeal_iff`

English:
theorem mem_maximalIdeal_iff
  given: {a : v.valuationSubring}
  proof: Integer.not_isUnit_iff_valuation_lt_one

中文:
定理 mem_maximalIdeal_iff
  条件: {a : v.valuationSubring}
  证明: Integer.not_isUnit_iff_valuation_lt_one

Depends on / 依赖: Integer, Integer.not_isUnit_iff_valuation_lt_one, not_isUnit_iff_valuation_lt_one
-/
theorem mem_maximalIdeal_iff {a : v.valuationSubring} :
    a in IsLocalRing.maximalIdeal (v.valuationSubring) ↔ v a < 1 :=
  Integer.not_isUnit_iff_valuation_lt_one

end Valuation
