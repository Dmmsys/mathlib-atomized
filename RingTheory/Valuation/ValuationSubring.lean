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

/-- A valuation subring of a field `K` is a subring `A` such that for every `x : K`,
either `x ∈ A` or `x⁻¹ ∈ A`.

This is equivalent to being maximal in the domination order
of local subrings (the stacks project definition). See `LocalSubring.isMax_iff`.
-/
/-
**ValuationSubring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u) → [Field K] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A valuation subring of a field `K` is a subring `A` such that for every `x : K`,
either `x ∈ A` or `x⁻¹ ∈ A`.

This is equivalent to being maximal in the domination order
of local subrings (the stacks project definition). See `LocalSubring.isMax_iff`.
-/
structure ValuationSubring extends Subring K where
  mem_or_inv_mem' : ∀ x : K, x ∈ carrier ∨ x⁻¹ ∈ carrier

namespace ValuationSubring

variable {K}
variable (A : ValuationSubring K)

/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (ValuationSubring K) K where
  coe A := A.toSubring
  coe_injective := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    replace h := SetLike.coe_injective h
    congr
/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (ValuationSubring K) := .ofSetLike (ValuationSubring K) K
/-
**ValuationSubring.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：mem_carrier (x : K) : x in A.carrier ↔ x in A
参数：x : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.refl`：∀ (a : Prop), a ↔ a
-/
theorem mem_carrier (x : K) : x ∈ A.carrier ↔ x ∈ A := Iff.refl _

@[simp]
/-
**ValuationSubring.mem_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：mem_toSubring (x : K) : x in A.toSubring ↔ x in A
参数：x : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.refl`：∀ (a : Prop), a ↔ a
-/
theorem mem_toSubring (x : K) : x ∈ A.toSubring ↔ x ∈ A := Iff.refl _

@[ext]
/-
**ValuationSubring.ext** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：ext (A B : ValuationSubring K) (h : forall x, x in A ↔ x in B) : A = B
参数：A B : ValuationSubring K；h : forall x, x in A ↔ x in B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext (A B : ValuationSubring K) (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := SetLike.ext h
/-
**ValuationSubring.zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：zero_mem : (0 : K) in A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.zero_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R)
, 0 ∈ s
-/
theorem zero_mem : (0 : K) ∈ A := A.toSubring.zero_mem
/-
**ValuationSubring.one_mem** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：one_mem : (1 : K) in A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.one_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R),
 1 ∈ s
-/
theorem one_mem : (1 : K) ∈ A := A.toSubring.one_mem
/-
**ValuationSubring.add_mem** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：add_mem (x y : K) : x in A -> y in A -> x + y in A
参数：x y : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.add_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) 
{x y : R}, x ∈ s → y ∈ s → x + y ∈ s
-/
theorem add_mem (x y : K) : x ∈ A → y ∈ A → x + y ∈ A := A.toSubring.add_mem
/-
**ValuationSubring.mul_mem** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：mul_mem (x y : K) : x in A -> y in A -> x * y in A
参数：x y : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.mul_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) 
{x y : R}, x ∈ s → y ∈ s → x * y ∈ s
-/
theorem mul_mem (x y : K) : x ∈ A → y ∈ A → x * y ∈ A := A.toSubring.mul_mem
/-
**ValuationSubring.neg_mem** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：neg_mem (x : K) : x in A -> -x in A
参数：x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.neg_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) 
{x : R}, x ∈ s → -x ∈ s
-/
theorem neg_mem (x : K) : x ∈ A → -x ∈ A := A.toSubring.neg_mem
/-
**ValuationSubring.mem_or_inv_mem** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：mem_or_inv_mem (x : K) : x in A ∨ x⁻¹ in A
参数：x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.mem_or_inv_mem'`：∀ {K : Type u} [inst : Field K] (self 
: ValuationSubring K) (x : K), x ∈ self.carrier ∨ x⁻¹ ∈ self.carrier
-/
theorem mem_or_inv_mem (x : K) : x ∈ A ∨ x⁻¹ ∈ A := A.mem_or_inv_mem' _
/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubringClass (ValuationSubring K) K where
  zero_mem := zero_mem
  add_mem {_} a b := add_mem _ a b
  one_mem := one_mem
  mul_mem {_} a b := mul_mem _ a b
  neg_mem {_} x := neg_mem _ x
/-
**ValuationSubring.toSubring_injective** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubri
ng`。
形式化陈述：toSubring_injective : Function.Injective (toSubring : ValuationSubring K -
> Subring K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toSubring_injective : Function.Injective (toSubring : ValuationSubring K → Subring K) :=
  fun x y h => by cases x; cases y; congr
/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing A := inferInstanceAs <| CommRing A.toSubring
/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDomain A := inferInstanceAs <| IsDomain A.toSubring
/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (ValuationSubring K) :=
  Top.mk <| { (⊤ : Subring K) with mem_or_inv_mem' := fun _ => Or.inl trivial }

@[simp]
/-
**ValuationSubring.toSubring_top** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：toSubring_top : (⊤ : ValuationSubring K).toSubring = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubring_top : (⊤ : ValuationSubring K).toSubring = ⊤ := rfl

@[simp]
/-
**ValuationSubring.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：mem_top (x : K) : x in (⊤ : ValuationSubring K)
参数：x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem mem_top (x : K) : x ∈ (⊤ : ValuationSubring K) :=
  trivial
/-
**ValuationSubring.le_top** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：le_top : A <= ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.mem_top`：mem_top (x : K) : x in (⊤ : ValuationSubring K
)
-/
theorem le_top : A ≤ ⊤ := fun _a _ha => mem_top _

/-- If `K` is a field, then so is `K` viewed as a valuation subring
of itself. (That is, `⊤ : ValuationSubring K`.) -/
/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K` is a field, then so is `K` viewed as a valuation subring
of itself. (That is, `⊤ : ValuationSubring K`.)
-/
instance : Field (⊤ : ValuationSubring K) := inferInstanceAs (Field (⊤ : Subfield K))

@[simp, norm_cast]
/-
**ValuationSubring.top_coe_div** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：top_coe_div (x y : (⊤ : ValuationSubring K)) : ((x / y : (⊤ : ValuationSub
ring K)) : K) = (x : K) / (y : K)
参数：x y : (⊤ : ValuationSubring K)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_coe_div (x y : (⊤ : ValuationSubring K)) :
    ((x / y : (⊤ : ValuationSubring K)) : K) = (x : K) / (y : K) :=
  rfl

@[simp, norm_cast]
/-
**ValuationSubring.top_coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：top_coe_inv (x : (⊤ : ValuationSubring K)) : ((x⁻¹ : (⊤ : ValuationSubring
 K)) : K) = (x : K)⁻¹
参数：x : (⊤ : ValuationSubring K)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_coe_inv (x : (⊤ : ValuationSubring K)) :
    ((x⁻¹ : (⊤ : ValuationSubring K)) : K) = (x : K)⁻¹ :=
  rfl
/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTop (ValuationSubring K) where
  le_top := le_top
/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ValuationSubring K) :=
  ⟨⊤⟩
/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra A K := inferInstance
/-
**ValuationSubring.isLocalRing** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
形式化陈述：isLocalRing : IsLocalRing A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `ValuationRing.isLocalRing`：∀ (A : Type u) [inst : CommRing A] [Nontrivia
l A] [PreValuationRing A], IsLocalRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `ValuationSubring.instIsDomainSubtypeMem`：∀ {K : Type u} [inst : Field K]
 (A : ValuationSubring K), IsDomain ↥A
· 使用定理 `ValuationSubring.instValuationRingSubtypeMem`：∀ {K : Type u} [inst : Fie
ld K] (A : ValuationSubring K), ValuationRing ↥A
-/
instance isLocalRing : IsLocalRing A := inferInstance

@[simp]
/-
**ValuationSubring.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`
。
形式化陈述：algebraMap_apply (a : A) : algebraMap A K a = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
-/
theorem algebraMap_apply (a : A) : algebraMap A K a = a := rfl
/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- The value group of the valuation associated to `A`. Note: it is actually a group with zero. -/
/-
**ValuationSubring.ValueGroup** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：ValueGroup
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The value group of the valuation associated to `A`. Note: it is actually a group
 with zero.
-/
def ValueGroup :=
  ValuationRing.ValueGroup A K
deriving LinearOrderedCommGroupWithZero

/-- Any valuation subring of `K` induces a natural valuation on `K`. -/
/-
**ValuationSubring.valuation** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：valuation : Valuation K A.ValueGroup
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.instIsDomainSubtypeMem`：∀ {K : Type u} [inst : Field K]
 (A : ValuationSubring K), IsDomain ↥A
· 使用定理 `ValuationSubring.instValuationRingSubtypeMem`：∀ {K : Type u} [inst : Fie
ld K] (A : ValuationSubring K), ValuationRing ↥A
· 使用定理 `ValuationSubring.instIsFractionRingSubtypeMem`：∀ {K : Type u} [inst : Fi
eld K] (A : ValuationSubring K), IsFractionRing (↥A) K

--- 原说明 ---
Any valuation subring of `K` induces a natural valuation on `K`.
-/
def valuation : Valuation K A.ValueGroup :=
  ValuationRing.valuation A K
/-
**ValuationSubring.inhabitedValueGroup** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubri
ng`。
形式化陈述：inhabitedValueGroup : Inhabited A.ValueGroup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedValueGroup : Inhabited A.ValueGroup := ⟨A.valuation 0⟩
/-
**ValuationSubring.valuation_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`
。
形式化陈述：valuation_le_one (a : A) : A.valuation a <= 1
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ValuationSubring.instIsDomainSubtypeMem`：∀ {K : Type u} [inst : Field K]
 (A : ValuationSubring K), IsDomain ↥A
· 使用定理 `ValuationSubring.instValuationRingSubtypeMem`：∀ {K : Type u} [inst : Fie
ld K] (A : ValuationSubring K), ValuationRing ↥A
· 使用定理 `ValuationSubring.instIsFractionRingSubtypeMem`：∀ {K : Type u} [inst : Fi
eld K] (A : ValuationSubring K), IsFractionRing (↥A) K
· 使用定理 `ValuationRing.mem_integer_iff`：mem_integer_iff (x : K) : x in (valuation
 A K).integer ↔ exists a : A, algebraMap A K a = x
-/
theorem valuation_le_one (a : A) : A.valuation a ≤ 1 :=
  (ValuationRing.mem_integer_iff A K _).2 ⟨a, rfl⟩
/-
**ValuationSubring.mem_of_valuation_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ValuationS
ubring`。
形式化陈述：mem_of_valuation_le_one (x : K) (h : A.valuation x <= 1) : x in A
参数：x : K；h : A.valuation x <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ValuationSubring.instIsDomainSubtypeMem`：∀ {K : Type u} [inst : Field K]
 (A : ValuationSubring K), IsDomain ↥A
· 使用定理 `ValuationSubring.instValuationRingSubtypeMem`：∀ {K : Type u} [inst : Fie
ld K] (A : ValuationSubring K), ValuationRing ↥A
· 使用定理 `ValuationSubring.instIsFractionRingSubtypeMem`：∀ {K : Type u} [inst : Fi
eld K] (A : ValuationSubring K), IsFractionRing (↥A) K
· 使用定理 `ValuationRing.mem_integer_iff`：mem_integer_iff (x : K) : x in (valuation
 A K).integer ↔ exists a : A, algebraMap A K a = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mem_of_valuation_le_one (x : K) (h : A.valuation x ≤ 1) : x ∈ A :=
  let ⟨a, ha⟩ := (ValuationRing.mem_integer_iff A K x).1 h
  ha ▸ a.2

@[simp]
/-
**ValuationSubring.valuation_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubr
ing`。
形式化陈述：valuation_le_one_iff (x : K) : A.valuation x <= 1 ↔ x in A
参数：x : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.mem_of_valuation_le_one`：mem_of_valuation_le_one (x : K
) (h : A.valuation x <= 1) : x in A
· 使用定理 `ValuationSubring.valuation_le_one`：valuation_le_one (a : A) : A.valuatio
n a <= 1
-/
theorem valuation_le_one_iff (x : K) : A.valuation x ≤ 1 ↔ x ∈ A :=
  ⟨mem_of_valuation_le_one _ _, fun ha => A.valuation_le_one ⟨x, ha⟩⟩
/-
**ValuationSubring.valuation_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`
。
形式化陈述：valuation_eq_iff (x y : K) : A.valuation x = A.valuation y ↔ exists a : Aˣ
, (a : K) * y = x
参数：x y : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
-/
theorem valuation_eq_iff (x y : K) : A.valuation x = A.valuation y ↔ ∃ a : Aˣ, (a : K) * y = x :=
  Quotient.eq''
/-
**ValuationSubring.valuation_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`
。
形式化陈述：valuation_le_iff (x y : K) : A.valuation x <= A.valuation y ↔ exists a : A
, (a : K) * y = x
参数：x y : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem valuation_le_iff (x y : K) : A.valuation x ≤ A.valuation y ↔ ∃ a : A, (a : K) * y = x :=
  Iff.rfl
/-
**ValuationSubring.valuation_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubr
ing`。
形式化陈述：valuation_surjective : Function.Surjective A.valuation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
theorem valuation_surjective : Function.Surjective A.valuation := Quot.mk_surjective

@[simp]
/-
**ValuationSubring.valuation_unit** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：valuation_unit (a : Aˣ) : A.valuation a = 1
参数：a : Aˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
· 使用定理 `ValuationSubring.valuation_eq_iff`：valuation_eq_iff (x y : K) : A.valuat
ion x = A.valuation y ↔ exists a : Aˣ, (a : K) * y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem valuation_unit (a : Aˣ) : A.valuation a = 1 := by
  rw [← A.valuation.map_one, valuation_eq_iff]; use a; simp
/-
**ValuationSubring.valuation_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubr
ing`。
形式化陈述：valuation_eq_one_iff (a : A) : IsUnit a ↔ A.valuation a = 1 where mp h
参数：a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `ValuationSubring.valuation_unit`：valuation_unit (a : Aˣ) : A.valuation a
 = 1
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.map_zero`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [in
st_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuationSubring.valuation_le_one_iff`：valuation_le_one_iff (x : K) : A.
valuation x <= 1 ↔ x in A
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `SubmonoidClass.instIsDedekindFiniteMonoidSubtypeMem`：∀ {M : Type u_1} {A
 : Type u_3} [inst : MulOneClass M] [inst_1 : SetLike A M] [hA : SubmonoidClass 
A M] (S : A)   [IsDedekindFiniteMonoid M]…
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
（共 40 条，此处仅展示前 30 条）
-/
theorem valuation_eq_one_iff (a : A) : IsUnit a ↔ A.valuation a = 1 where
  mp h := A.valuation_unit h.unit
  mpr h := by
    have ha : (a : K) ≠ 0 := by
      intro c
      rw [c, A.valuation.map_zero] at h
      exact zero_ne_one h
    have ha' : (a : K)⁻¹ ∈ A := by rw [← valuation_le_one_iff, map_inv₀, h, inv_one]
    refine .of_mul_eq_one ⟨a⁻¹, ha'⟩ ?_
    ext
    simp [field]
/-
**ValuationSubring.eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：eq_top_iff : A = ⊤ ↔ ¬ A.valuation.IsNontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_top_iff : A = ⊤ ↔ ¬ A.valuation.IsNontrivial := by
  simp [Valuation.IsNontrivial_iff_exists_one_lt, SetLike.ext_iff]
/-
**ValuationSubring.valuation_lt_one_or_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuati
onSubring`。
形式化陈述：valuation_lt_one_or_eq_one (a : A) : A.valuation a < 1 ∨ A.valuation a = 1
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `ValuationSubring.valuation_le_one`：valuation_le_one (a : A) : A.valuatio
n a <= 1
-/
theorem valuation_lt_one_or_eq_one (a : A) : A.valuation a < 1 ∨ A.valuation a = 1 :=
  lt_or_eq_of_le (A.valuation_le_one a)
/-
**ValuationSubring.valuation_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubr
ing`。
形式化陈述：valuation_lt_one_iff (a : A) : a in IsLocalRing.maximalIdeal A ↔ A.valuati
on a < 1
参数：a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalRing.mem_maximalIdeal`：mem_maximalIdeal (x) : x in maximalIdeal R
 ↔ x in nonunits R
· 使用定理 `ValuationSubring.valuation_eq_one_iff`：valuation_eq_one_iff (a : A) : Is
Unit a ↔ A.valuation a = 1 where mp h
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `ValuationSubring.valuation_le_one`：valuation_le_one (a : A) : A.valuatio
n a <= 1
-/
theorem valuation_lt_one_iff (a : A) : a ∈ IsLocalRing.maximalIdeal A ↔ A.valuation a < 1 := by
  rw [IsLocalRing.mem_maximalIdeal]
  dsimp [nonunits]; rw [valuation_eq_one_iff]
  exact (A.valuation_le_one a).lt_iff_ne.symm

/-- A subring `R` of `K` such that for all `x : K` either `x ∈ R` or `x⁻¹ ∈ R` is
  a valuation subring of `K`. -/
/-
**ValuationSubring.ofSubring** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：ofSubring (R : Subring K) (hR : forall x : K, x in R ∨ x⁻¹ in R) : Valuati
onSubring K
参数：R : Subring K；hR : forall x : K, x in R ∨ x⁻¹ in R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subring `R` of `K` such that for all `x : K` either `x ∈ R` or `x⁻¹ ∈ R` is
  a valuation subring of `K`.
-/
def ofSubring (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) : ValuationSubring K :=
  { R with mem_or_inv_mem' := hR }

@[simp]
/-
**ValuationSubring.mem_ofSubring** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：mem_ofSubring (R : Subring K) (hR : forall x : K, x in R ∨ x⁻¹ in R) (x : 
K) : x in ofSubring R hR ↔ x in R
参数：R : Subring K；hR : forall x : K, x in R ∨ x⁻¹ in R；x : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.refl`：∀ (a : Prop), a ↔ a
-/
theorem mem_ofSubring (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) (x : K) :
    x ∈ ofSubring R hR ↔ x ∈ R :=
  Iff.refl _

/-- An overring of a valuation ring is a valuation ring. -/
/-
**ValuationSubring.ofLE** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：ofLE (R : ValuationSubring K) (S : Subring K) (h : R.toSubring <= S) : Val
uationSubring K
参数：R : ValuationSubring K；S : Subring K；h : R.toSubring <= S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An overring of a valuation ring is a valuation ring.
-/
def ofLE (R : ValuationSubring K) (S : Subring K) (h : R.toSubring ≤ S) : ValuationSubring K :=
  { S with mem_or_inv_mem' := fun x => (R.mem_or_inv_mem x).imp (@h x) (@h _) }

section Order

/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (ValuationSubring K) :=
  { (inferInstance : PartialOrder (ValuationSubring K)) with
    sup := fun R S => ofLE R (R.toSubring ⊔ S.toSubring) <| le_sup_left
    le_sup_left := fun R S _ hx => (le_sup_left : R.toSubring ≤ R.toSubring ⊔ S.toSubring) hx
    le_sup_right := fun R S _ hx => (le_sup_right : S.toSubring ≤ R.toSubring ⊔ S.toSubring) hx
    sup_le := fun R S T hR hT _ hx => (sup_le hR hT : R.toSubring ⊔ S.toSubring ≤ T.toSubring) hx }

/-- The ring homomorphism induced by the partial order. -/
/-
**ValuationSubring.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：inclusion (R S : ValuationSubring K) (h : R <= S) : R ->+* S
参数：R S : ValuationSubring K；h : R <= S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism induced by the partial order.
-/
def inclusion (R S : ValuationSubring K) (h : R ≤ S) : R →+* S :=
  Subring.inclusion h

/-- The canonical ring homomorphism from a valuation ring to its field of fractions. -/
/-
**ValuationSubring.subtype** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：subtype (R : ValuationSubring K) : R ->+* K
参数：R : ValuationSubring K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical ring homomorphism from a valuation ring to its field of fractions.
-/
def subtype (R : ValuationSubring K) : R →+* K :=
  Subring.subtype R.toSubring

@[simp]
/-
**ValuationSubring.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `ValuationSubring`。
形式化陈述：subtype_apply {R : ValuationSubring K} (x : R) : R.subtype x = x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
-/
lemma subtype_apply {R : ValuationSubring K} (x : R) :
    R.subtype x = x := rfl
/-
**ValuationSubring.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `ValuationSubring
`。
形式化陈述：subtype_injective (R : ValuationSubring K) : Function.Injective R.subtype
参数：R : ValuationSubring K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subring.subtype_injective`：subtype_injective (s : Subring R) : Function.
Injective s.subtype
-/
lemma subtype_injective (R : ValuationSubring K) :
    Function.Injective R.subtype :=
  R.toSubring.subtype_injective

@[simp]
/-
**ValuationSubring.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：coe_subtype (R : ValuationSubring K) : ⇑(subtype R) = Subtype.val
参数：R : ValuationSubring K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
-/
theorem coe_subtype (R : ValuationSubring K) : ⇑(subtype R) = Subtype.val :=
  rfl

/-- The canonical map on value groups induced by a coarsening of valuation rings. -/
/-
**ValuationSubring.mapOfLE** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：mapOfLE (R S : ValuationSubring K) (h : R <= S) : R.ValueGroup ->*₀ S.Valu
eGroup where toFun
参数：R S : ValuationSubring K；h : R <= S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)

--- 原说明 ---
The canonical map on value groups induced by a coarsening of valuation rings.
-/
def mapOfLE (R S : ValuationSubring K) (h : R ≤ S) : R.ValueGroup →*₀ S.ValueGroup where
  toFun := Quotient.map' id fun _ _ ⟨u, hu⟩ => ⟨Units.map (R.inclusion S h).toMonoidHom u, hu⟩
  map_zero' := rfl
  map_one' := rfl
  map_mul' := by rintro ⟨⟩ ⟨⟩; rfl

@[gcongr, mono]
/-
**ValuationSubring.monotone_mapOfLE** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`
。
形式化陈述：monotone_mapOfLE (R S : ValuationSubring K) (h : R <= S) : Monotone (R.map
OfLE S h)
参数：R S : ValuationSubring K；h : R <= S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
-/
theorem monotone_mapOfLE (R S : ValuationSubring K) (h : R ≤ S) : Monotone (R.mapOfLE S h) := by
  rintro ⟨⟩ ⟨⟩ ⟨a, ha⟩; exact ⟨R.inclusion S h a, ha⟩

@[simp]
/-
**ValuationSubring.mapOfLE_comp_valuation** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSu
bring`。
形式化陈述：mapOfLE_comp_valuation (R S : ValuationSubring K) (h : R <= S) : R.mapOfLE
 S h ∘ R.valuation = S.valuation
参数：R S : ValuationSubring K；h : R <= S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem mapOfLE_comp_valuation (R S : ValuationSubring K) (h : R ≤ S) :
    R.mapOfLE S h ∘ R.valuation = S.valuation := by ext; rfl

@[simp]
/-
**ValuationSubring.mapOfLE_valuation_apply** 是 Mathlib 中的一个定理，位于命名空间 `ValuationS
ubring`。
形式化陈述：mapOfLE_valuation_apply (R S : ValuationSubring K) (h : R <= S) (x : K) : 
R.mapOfLE S h (R.valuation x) = S.valuation x
参数：R S : ValuationSubring K；h : R <= S；x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapOfLE_valuation_apply (R S : ValuationSubring K) (h : R ≤ S) (x : K) :
    R.mapOfLE S h (R.valuation x) = S.valuation x := rfl

/-- The ideal corresponding to a coarsening of a valuation ring. -/
/-
**ValuationSubring.idealOfLE** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：idealOfLE (R S : ValuationSubring K) (h : R <= S) : Ideal R
参数：R S : ValuationSubring K；h : R <= S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ideal corresponding to a coarsening of a valuation ring.
-/
def idealOfLE (R S : ValuationSubring K) (h : R ≤ S) : Ideal R :=
  (IsLocalRing.maximalIdeal S).comap (R.inclusion S h)
/-
**ValuationSubring.idealOfLE_self** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：idealOfLE_self : A.idealOfLE A (refl _) = IsLocalRing.maximalIdeal A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem idealOfLE_self : A.idealOfLE A (refl _) = IsLocalRing.maximalIdeal A := rfl

@[simp]
/-
**ValuationSubring.idealOfLE_top** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：idealOfLE_top : A.idealOfLE ⊤ (le_top _) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `ValuationSubring.le_top`：le_top : A <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuationSubring.idealOfLE.eq_1`：∀ {K : Type u} [inst : Field K] (R S : 
ValuationSubring K) (h : R ≤ S),   R.idealOfLE S h = Ideal.comap (R.inclusion S 
h) (IsLocalRing.maxim…
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsLocalRing.maximalIdeal_eq_bot`：maximalIdeal_eq_bot {R : Type*} [Field 
R] : IsLocalRing.maximalIdeal R = ⊥
· 使用定理 `Ideal.comap_bot_of_injective`：comap_bot_of_injective (hf : Function.Inje
ctive f) : Ideal.comap f ⊥ = ⊥
· 使用定理 `Subring.inclusion_injective`：inclusion_injective {S T : Subring R} (h : 
S <= T) : Function.Injective (Subring.inclusion h)
-/
theorem idealOfLE_top : A.idealOfLE ⊤ (le_top _) = ⊥ := by
  rw [ValuationSubring.idealOfLE, IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective]
  exact Subring.inclusion_injective _
/-
**ValuationSubring.prime_idealOfLE** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
形式化陈述：prime_idealOfLE (R S : ValuationSubring K) (h : R <= S) : (idealOfLE R S h
).IsPrime
参数：R S : ValuationSubring K；h : R <= S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_isPrime`：comap_isPrime [H : IsPrime K] : IsPrime (comap f K)
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
-/
instance prime_idealOfLE (R S : ValuationSubring K) (h : R ≤ S) : (idealOfLE R S h).IsPrime :=
  (IsLocalRing.maximalIdeal S).comap_isPrime _

/-- The coarsening of a valuation ring associated to a prime ideal. -/
/-
**ValuationSubring.ofPrime** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : ValuationSubr
ing K
参数：A : ValuationSubring K；P : Ideal A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.instIsFractionRingSubtypeMem`：∀ {K : Type u} [inst : Fi
eld K] (A : ValuationSubring K), IsFractionRing (↥A) K

--- 原说明 ---
The coarsening of a valuation ring associated to a prime ideal.
-/
def ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : ValuationSubring K :=
  ofLE A (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors).toSubring
    fun a ha => Subalgebra.mem_toSubring.mpr <|
      Subalgebra.algebraMap_mem
        (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors) (⟨a, ha⟩ : A)
/-
**ValuationSubring.ofPrimeAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
形式化陈述：ofPrimeAlgebra (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : Algebr
a A (A.ofPrime P)
参数：A : ValuationSubring K；P : Ideal A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ofPrimeAlgebra (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    Algebra A (A.ofPrime P) :=
  inferInstanceAs <| Algebra A (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors)
/-
**ValuationSubring.ofPrime_scalar_tower** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubr
ing`。
形式化陈述：ofPrime_scalar_tower (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : 
letI : SMul A (A.ofPrime P)
参数：A : ValuationSubring K；P : Ideal A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `ValuationSubring.instIsFractionRingSubtypeMem`：∀ {K : Type u} [inst : Fi
eld K] (A : ValuationSubring K), IsFractionRing (↥A) K
-/
instance ofPrime_scalar_tower (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    letI : SMul A (A.ofPrime P) := SMulZeroClass.toSMul
    IsScalarTower A (A.ofPrime P) K :=
  IsScalarTower.subalgebra' A K K
    (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors)
/-
**ValuationSubring.ofPrime_localization** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubr
ing`。
形式化陈述：ofPrime_localization (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : 
IsLocalization.AtPrime (A.ofPrime P) P
参数：A : ValuationSubring K；P : Ideal A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `ValuationSubring.instIsFractionRingSubtypeMem`：∀ {K : Type u} [inst : Fi
eld K] (A : ValuationSubring K), IsFractionRing (↥A) K
-/
instance ofPrime_localization (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    IsLocalization.AtPrime (A.ofPrime P) P :=
  Localization.subalgebra.isLocalization_ofField K P.primeCompl
    P.primeCompl_le_nonZeroDivisors
/-
**ValuationSubring.le_ofPrime** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：le_ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : A <= ofPri
me A P
参数：A : ValuationSubring K；P : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ValuationSubring.instIsFractionRingSubtypeMem`：∀ {K : Type u} [inst : Fi
eld K] (A : ValuationSubring K), IsFractionRing (↥A) K
· 使用定理 `Subalgebra.mem_toSubring`：mem_toSubring {R : Type u} {A : Type v} [CommR
ing R] [Ring A] [Algebra R A] {S : Subalgebra R A} {x} : x in S.toSubring ↔ x in
 S
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
-/
theorem le_ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : A ≤ ofPrime A P :=
  fun a ha => Subalgebra.mem_toSubring.mpr <| Subalgebra.algebraMap_mem _ (⟨a, ha⟩ : A)
/-
**ValuationSubring.ofPrime_valuation_eq_one_iff_mem_primeCompl** 是 Mathlib 中的一个定
理，位于命名空间 `ValuationSubring`。
形式化陈述：ofPrime_valuation_eq_one_iff_mem_primeCompl (A : ValuationSubring K) (P : 
Ideal A) [P.IsPrime] (x : A) : (ofPrime A P).valuation x = 1 ↔ x in P.primeCompl
参数：A : ValuationSubring K；P : Ideal A；x : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.AtPrime.isUnit_to_map_iff`：isUnit_to_map_iff (x : R) : Is
Unit ((algebraMap R S) x) ↔ x in I.primeCompl
· 使用定理 `ValuationSubring.valuation_eq_one_iff`：valuation_eq_one_iff (a : A) : Is
Unit a ↔ A.valuation a = 1 where mp h
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofPrime_valuation_eq_one_iff_mem_primeCompl (A : ValuationSubring K) (P : Ideal A)
    [P.IsPrime] (x : A) : (ofPrime A P).valuation x = 1 ↔ x ∈ P.primeCompl := by
  rw [← IsLocalization.AtPrime.isUnit_to_map_iff (A.ofPrime P) P x, valuation_eq_one_iff]; rfl

@[simp]
/-
**ValuationSubring.idealOfLE_ofPrime** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring
`。
形式化陈述：idealOfLE_ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : ide
alOfLE A (ofPrime A P) (le_ofPrime A P) = P
参数：A : ValuationSubring K；P : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `ValuationSubring.le_ofPrime`：le_ofPrime (A : ValuationSubring K) (P : Id
eal A) [P.IsPrime] : A <= ofPrime A P
· 使用定理 `IsLocalization.AtPrime.to_map_mem_maximal_iff`：to_map_mem_maximal_iff (x
 : R) (h : IsLocalRing S
-/
theorem idealOfLE_ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    idealOfLE A (ofPrime A P) (le_ofPrime A P) = P := by
  refine Ideal.ext (fun x => ?_)
  apply IsLocalization.AtPrime.to_map_mem_maximal_iff
  exact isLocalRing (ofPrime A P)

@[simp]
/-
**ValuationSubring.ofPrime_idealOfLE** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring
`。
形式化陈述：ofPrime_idealOfLE (R S : ValuationSubring K) (h : R <= S) : ofPrime R (ide
alOfLE R S h) = S
参数：R S : ValuationSubring K；h : R <= S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.ext`：ext (A B : ValuationSubring K) (h : forall x, x in
 A ↔ x in B) : A = B
· 使用定理 `ValuationSubring.mul_mem`：mul_mem (x y : K) : x in A -> y in A -> x * y 
in A
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuationSubring.valuation_le_one_iff`：valuation_le_one_iff (x : K) : A.
valuation x <= 1 ↔ x in A
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `inv_le_inv₀`：inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toMulPosStrictMono`：∀ {α : Type u_1} [in
st : LinearOrderedCommMonoidWithZero α], MulPosStrictMono α
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 65 条，此处仅展示前 30 条）
-/
theorem ofPrime_idealOfLE (R S : ValuationSubring K) (h : R ≤ S) :
    ofPrime R (idealOfLE R S h) = S := by
  ext x; constructor
  · rintro ⟨a, r, hr, rfl⟩; apply mul_mem; · exact h a.2
    · rw [← valuation_le_one_iff, map_inv₀, ← inv_one, inv_le_inv₀]
      · exact not_lt.1 ((not_iff_not.2 <| valuation_lt_one_iff S _).1 hr)
      · simpa [Valuation.pos_iff] using fun hr₀ ↦ hr₀ ▸ hr <| Ideal.zero_mem (R.idealOfLE S h)
      · exact zero_lt_one
  · intro hx; by_cases hr : x ∈ R; · exact R.le_ofPrime _ hr
    have : x ≠ 0 := fun h => hr (by rw [h]; exact R.zero_mem)
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
/-
**ValuationSubring.ofPrime_bot** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：ofPrime_bot : A.ofPrime ⊥ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuationSubring.le_top`：le_top : A <= ⊤
· 使用定理 `ValuationSubring.ofPrime.congr_simp`：∀ {K : Type u} [inst : Field K] (A 
: ValuationSubring K) (P P_1 : Ideal ↥A) (e_P : P = P_1) [inst_1 : P.IsPrime],  
 A.ofPrime P = A.ofPrime …
· 使用定理 `ValuationSubring.ofPrime_idealOfLE`：ofPrime_idealOfLE (R S : ValuationSu
bring K) (h : R <= S) : ofPrime R (idealOfLE R S h) = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofPrime_bot : A.ofPrime ⊥ = ⊤ := by simp [← idealOfLE_top]

@[simp]
/-
**ValuationSubring.ofPrime_top** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：ofPrime_top : A.ofPrime (IsLocalRing.maximalIdeal A) = A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuationSubring.ofPrime_idealOfLE`：ofPrime_idealOfLE (R S : ValuationSu
bring K) (h : R <= S) : ofPrime R (idealOfLE R S h) = S
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofPrime_top : A.ofPrime (IsLocalRing.maximalIdeal A) = A := by simp [← idealOfLE_self]
/-
**ValuationSubring.ofPrime_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`
。
形式化陈述：ofPrime_le_of_le (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] (h : P <= Q) : of
Prime A Q <= ofPrime A P
参数：P Q : Ideal A；h : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
-/
theorem ofPrime_le_of_le (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    ofPrime A Q ≤ ofPrime A P := fun _x ⟨a, s, hs, he⟩ => ⟨a, s, fun c => hs (h c), he⟩
/-
**ValuationSubring.idealOfLE_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubrin
g`。
形式化陈述：idealOfLE_le_of_le (R S : ValuationSubring K) (hR : A <= R) (hS : A <= S) 
(h : R <= S) : idealOfLE A S hS <= idealOfLE A R hR
参数：R S : ValuationSubring K；hR : A <= R；hS : A <= S；h : R <= S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ValuationSubring.valuation_lt_one_iff`：valuation_lt_one_iff (a : A) : a 
in IsLocalRing.maximalIdeal A ↔ A.valuation a < 1
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `ValuationSubring.monotone_mapOfLE`：monotone_mapOfLE (R S : ValuationSubr
ing K) (h : R <= S) : Monotone (R.mapOfLE S h)
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuationSubring.mapOfLE_valuation_apply`：mapOfLE_valuation_apply (R S :
 ValuationSubring K) (h : R <= S) (x : K) : R.mapOfLE S h (R.valuation x) = S.va
luation x
· 使用定理 `MonoidWithZeroHom.map_one`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZe
roOneClass α] [inst_1 : MulZeroOneClass β] (f : α →*₀ β), f 1 = 1
-/
theorem idealOfLE_le_of_le (R S : ValuationSubring K) (hR : A ≤ R) (hS : A ≤ S) (h : R ≤ S) :
    idealOfLE A S hS ≤ idealOfLE A R hR := fun x hx =>
  (valuation_lt_one_iff R _).2
    (by
      by_contra! c; replace c := monotone_mapOfLE R S h c
      rw [(mapOfLE _ _ _).map_one, mapOfLE_valuation_apply] at c
      apply not_le_of_gt ((valuation_lt_one_iff S _).1 hx) c)

/-- The equivalence between coarsenings of a valuation ring and its prime ideals. -/
@[simps apply]
/-
**ValuationSubring.primeSpectrumEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubrin
g`。
形式化陈述：primeSpectrumEquiv : PrimeSpectrum A ≃ {S // A <= S} where toFun P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between coarsenings of a valuation ring and its prime ideals.
-/
def primeSpectrumEquiv : PrimeSpectrum A ≃ {S // A ≤ S} where
  toFun P := ⟨ofPrime A P.asIdeal, le_ofPrime _ _⟩
  invFun S := ⟨idealOfLE _ S S.2, inferInstance⟩
  left_inv P := by ext1; simp
  right_inv S := by ext1; simp

set_option backward.defeqAttrib.useBackward true in
/-- An ordered variant of `primeSpectrumEquiv`. -/
@[simps!]
/-
**ValuationSubring.primeSpectrumOrderEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ValuationS
ubring`。
形式化陈述：primeSpectrumOrderEquiv : (PrimeSpectrum A)ᵒᵈ ≃o {S // A <= S}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
An ordered variant of `primeSpectrumEquiv`.
-/
def primeSpectrumOrderEquiv : (PrimeSpectrum A)ᵒᵈ ≃o {S // A ≤ S} :=
  { OrderDual.ofDual.trans (primeSpectrumEquiv A) with
    map_rel_iff' {a b} :=
      ⟨a.rec <| fun a => b.rec <| fun b => fun h => by
        simp only [OrderDual.toDual_le_toDual]
        dsimp at h
        have := idealOfLE_le_of_le A _ _ ?_ ?_ h
        · rwa [idealOfLE_ofPrime, idealOfLE_ofPrime] at this
        all_goals exact le_ofPrime A (PrimeSpectrum.asIdeal _),
      fun h => by apply ofPrime_le_of_le; exact h⟩ }
/-
**ValuationSubring.le_total_ideal** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
形式化陈述：le_total_ideal : @Std.Total {S // A <= S} (· <= ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Std.Total.total`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Total r] 
(a b : α), r a b ∨ r b a
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `ValuationSubring.instIsDomainSubtypeMem`：∀ {K : Type u} [inst : Field K]
 (A : ValuationSubring K), IsDomain ↥A
· 使用定理 `ValuationSubring.instValuationRingSubtypeMem`：∀ {K : Type u} [inst : Fie
ld K] (A : ValuationSubring K), ValuationRing ↥A
· 使用定理 `RelEmbedding.total`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {
s : β → β → Prop} (x : r ↪r s) [Std.Total s], Std.Total r
-/
instance le_total_ideal : @Std.Total {S // A ≤ S} (· ≤ ·) := by
  classical
  let _ : @Std.Total (PrimeSpectrum A) (· ≤ ·) := ⟨fun ⟨x, _⟩ ⟨y, _⟩ => LE.total.total x y⟩
  exact (primeSpectrumOrderEquiv A).symm.toRelEmbedding.total

open scoped Classical in
/-
**ValuationSubring.linearOrderOverring** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubri
ng`。
形式化陈述：linearOrderOverring : LinearOrder {S // A <= S} where le_total
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance linearOrderOverring : LinearOrder {S // A ≤ S} where
  le_total := (le_total_ideal A).1
  max_def a b := congr_fun₂ sup_eq_maxDefault a b
  toDecidableLE := _

section

variable [Ring.KrullDimLE 1 A] {B : ValuationSubring K}

variable {A} in
/-
**ValuationSubring.eq_self_or_eq_top_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ValuationS
ubring`。
形式化陈述：eq_self_or_eq_top_of_le (hle : A <= B) : A = B ∨ B = ⊤
参数：hle : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `ValuationSubring.instIsDomainSubtypeMem`：∀ {K : Type u} [inst : Field K]
 (A : ValuationSubring K), IsDomain ↥A
· 使用定理 `IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top`：∀ {R : Type u} [inst : Com
mSemiring R] [inst_1 : IsLocalRing R] [inst_2 : IsDomain R] [Ring.KrullDimLE 1 R
]   (x : PrimeSpectrum R), x = ⊥ ∨…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ValuationSubring.ofPrime_bot`：ofPrime_bot : A.ofPrime ⊥ = ⊤
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `ValuationSubring.primeSpectrumEquiv_apply`：∀ {K : Type u} [inst : Field 
K] (A : ValuationSubring K) (P : PrimeSpectrum ↥A),   A.primeSpectrumEquiv P = ⟨
A.ofPrime P.asIdeal, ⋯⟩
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `ValuationSubring.ofPrime_top`：ofPrime_top : A.ofPrime (IsLocalRing.maxim
alIdeal A) = A
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem eq_self_or_eq_top_of_le (hle : A ≤ B) : A = B ∨ B = ⊤ := by
  obtain h | h := IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (A.primeSpectrumEquiv.symm ⟨B, hle⟩)
  all_goals
    replace h := congr(primeSpectrumEquiv A $h)
    simp_all
/-
**ValuationSubring.eq_of_le_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubrin
g`。
形式化陈述：eq_of_le_of_ne_top (hle : A <= B) (hTop : B != ⊤) : A = B
参数：hle : A <= B；hTop : B != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `ValuationSubring.eq_self_or_eq_top_of_le`：eq_self_or_eq_top_of_le (hle :
 A <= B) : A = B ∨ B = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem eq_of_le_of_ne_top (hle : A ≤ B) (hTop : B ≠ ⊤) : A = B := by
  obtain h | h := eq_self_or_eq_top_of_le hle <;> simp_all
/-
**ValuationSubring.eq_of_le_of_ne_self** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubri
ng`。
形式化陈述：eq_of_le_of_ne_self (hle : A <= B) (hne : A != B) : B = ⊤
参数：hle : A <= B；hne : A != B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `ValuationSubring.eq_self_or_eq_top_of_le`：eq_self_or_eq_top_of_le (hle :
 A <= B) : A = B ∨ B = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem eq_of_le_of_ne_self (hle : A ≤ B) (hne : A ≠ B) : B = ⊤ := by
  obtain h | h := eq_self_or_eq_top_of_le hle <;> simp_all
/-
**ValuationSubring.eq_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：eq_of_lt (hlt : A < B) : B = ⊤
参数：hlt : A < B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `ValuationSubring.eq_self_or_eq_top_of_le`：eq_self_or_eq_top_of_le (hle :
 A <= B) : A = B ∨ B = ⊤
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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

/-- The valuation subring associated to a valuation. -/
/-
**Valuation.valuationSubring** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：valuationSubring : ValuationSubring K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation subring associated to a valuation.
-/
def valuationSubring : ValuationSubring K :=
  { v.integer with
    mem_or_inv_mem' := by
      intro x
      rcases val_le_one_or_val_inv_le_one v x with h | h
      exacts [Or.inl h, Or.inr h] }

@[simp]
/-
**Valuation.mem_valuationSubring_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：mem_valuationSubring_iff (x : K) : x in v.valuationSubring ↔ v x <= 1
参数：x : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.refl`：∀ (a : Prop), a ↔ a
-/
theorem mem_valuationSubring_iff (x : K) : x ∈ v.valuationSubring ↔ v x ≤ 1 := Iff.refl _
/-
**Valuation.isEquiv_iff_valuationSubring** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isEquiv_iff_valuationSubring : v₁.IsEquiv v₂ ↔ v₁.valuationSubring = v₂.va
luationSubring
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.ext`：ext (A B : ValuationSubring K) (h : forall x, x in
 A ↔ x in B) : A = B
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.isEquiv_of_val_le_one`：isEquiv_of_val_le_one (h : forall x, v 
x <= 1 ↔ v' x <= 1) : v.IsEquiv v'
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isEquiv_iff_valuationSubring :
    v₁.IsEquiv v₂ ↔ v₁.valuationSubring = v₂.valuationSubring := by
  constructor
  · intro h; ext x; specialize h x 1; simpa using h
  · intro h; apply isEquiv_of_val_le_one
    intro x
    have : x ∈ v₁.valuationSubring ↔ x ∈ v₂.valuationSubring := by rw [h]
    simpa using this
/-
**Valuation.isEquiv_valuation_valuationSubring** 是 Mathlib 中的一个定理，位于命名空间 `Valuat
ion`。
形式化陈述：isEquiv_valuation_valuationSubring : v.IsEquiv v.valuationSubring.valuatio
n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.isEquiv_iff_val_le_one`：isEquiv_iff_val_le_one : v.IsEquiv v' 
↔ forall {x}, v x <= 1 ↔ v' x <= 1
· 使用定理 `ValuationSubring.valuation_le_one_iff`：valuation_le_one_iff (x : K) : A.
valuation x <= 1 ↔ x in A
· 使用定理 `Valuation.mem_valuationSubring_iff`：mem_valuationSubring_iff (x : K) : x
 in v.valuationSubring ↔ v x <= 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isEquiv_valuation_valuationSubring : v.IsEquiv v.valuationSubring.valuation := by
  rw [isEquiv_iff_val_le_one]
  intro x
  rw [ValuationSubring.valuation_le_one_iff, mem_valuationSubring_iff]

@[simp]
/-
**Valuation.isNontrivial_valuation_valuationSubring_iff** 是 Mathlib 中的一个定理，位于命名空
间 `Valuation`。
形式化陈述：isNontrivial_valuation_valuationSubring_iff : v.valuationSubring.valuation
.IsNontrivial ↔ v.IsNontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Valuation.IsEquiv.isNontrivial_iff`：∀ {R : Type u_3} {Γ₀ : Type u_4} {Γ'
₀ : Type u_5} [inst : Ring R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀]   [i
nst_2 : LinearOrderedCom…
· 使用定理 `Valuation.isEquiv_valuation_valuationSubring`：isEquiv_valuation_valuatio
nSubring : v.IsEquiv v.valuationSubring.valuation
-/
theorem isNontrivial_valuation_valuationSubring_iff :
    v.valuationSubring.valuation.IsNontrivial ↔ v.IsNontrivial :=
  (isEquiv_valuation_valuationSubring v).isNontrivial_iff.symm
/-
**Valuation.valuationSubring.integers** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.valua
tionSubring`。
形式化陈述：∀ {K : Type u} [inst : Field K] {Γ : Type u_1} [inst_1 : LinearOrderedComm
GroupWithZero Γ] (v : Valuation K Γ),   v.Integers ↥v.valuationSubring
参数：v : Valuation K Γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
-/
lemma valuationSubring.integers : v.Integers v.valuationSubring :=
  Valuation.integer.integers _

@[simp]
/-
**Valuation.valuationSubring_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：valuationSubring_eq_top_iff : v.valuationSubring = ⊤ ↔ ¬ v.IsNontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem valuationSubring_eq_top_iff : v.valuationSubring = ⊤ ↔ ¬ v.IsNontrivial := by
  simp [ValuationSubring.eq_top_iff]

end Valuation

namespace ValuationSubring

variable {K}
variable (A : ValuationSubring K)

@[simp]
/-
**ValuationSubring.valuationSubring_valuation** 是 Mathlib 中的一个定理，位于命名空间 `Valuati
onSubring`。
形式化陈述：valuationSubring_valuation : A.valuation.valuationSubring = A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.ext`：ext (A B : ValuationSubring K) (h : forall x, x in
 A ↔ x in B) : A = B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuationSubring.valuation_le_one_iff`：valuation_le_one_iff (x : K) : A.
valuation x <= 1 ↔ x in A
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem valuationSubring_valuation : A.valuation.valuationSubring = A := by
  ext; rw [← A.valuation_le_one_iff]; rfl
/-
**ValuationSubring.integer_valuation** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring
`。
形式化陈述：integer_valuation : A.valuation.integer = A.toSubring
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuationSubring.valuationSubring_valuation`：valuationSubring_valuation 
: A.valuation.valuationSubring = A
-/
theorem integer_valuation : A.valuation.integer = A.toSubring :=
  congr(($A.valuationSubring_valuation).toSubring)

section UnitGroup

/-- The unit group of a valuation subring, as a subgroup of `Kˣ`. -/
/-
**ValuationSubring.unitGroup** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：unitGroup : Subgroup Kˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit group of a valuation subring, as a subgroup of `Kˣ`.
-/
def unitGroup : Subgroup Kˣ :=
  (A.valuation.toMonoidWithZeroHom.toMonoidHom.comp (Units.coeHom K)).ker

@[simp]
/-
**ValuationSubring.mem_unitGroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring
`。
形式化陈述：mem_unitGroup_iff (x : Kˣ) : x in A.unitGroup ↔ A.valuation x = 1
参数：x : Kˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_unitGroup_iff (x : Kˣ) : x ∈ A.unitGroup ↔ A.valuation x = 1 := Iff.rfl

/-- For a valuation subring `A`, `A.unitGroup` agrees with the units of `A`. -/
/-
**ValuationSubring.unitGroupMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring
`。
形式化陈述：unitGroupMulEquiv : A.unitGroup ≃* Aˣ where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.valuation_unit`：valuation_unit (a : Aˣ) : A.valuation a
 = 1

--- 原说明 ---
For a valuation subring `A`, `A.unitGroup` agrees with the units of `A`.
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
/-
**ValuationSubring.coe_unitGroupMulEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Valuat
ionSubring`。
形式化陈述：coe_unitGroupMulEquiv_apply (a : A.unitGroup) : ((A.unitGroupMulEquiv a : 
A) : K) = ((a : Kˣ) : K)
参数：a : A.unitGroup。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
-/
theorem coe_unitGroupMulEquiv_apply (a : A.unitGroup) :
    ((A.unitGroupMulEquiv a : A) : K) = ((a : Kˣ) : K) := rfl

@[simp]
/-
**ValuationSubring.coe_unitGroupMulEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `V
aluationSubring`。
形式化陈述：coe_unitGroupMulEquiv_symm_apply (a : Aˣ) : ((A.unitGroupMulEquiv.symm a :
 Kˣ) : K) = a
参数：a : Aˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
-/
theorem coe_unitGroupMulEquiv_symm_apply (a : Aˣ) : ((A.unitGroupMulEquiv.symm a : Kˣ) : K) = a :=
  rfl
/-
**ValuationSubring.unitGroup_le_unitGroup** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSu
bring`。
形式化陈述：unitGroup_le_unitGroup {A B : ValuationSubring K} : A.unitGroup <= B.unitG
roup ↔ A <= B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_eq_zero_iff_neg_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ -a = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ValuationSubring.neg_mem`：neg_mem (x : K) : x in A -> -x in A
· 使用定理 `ValuationSubring.one_mem`：one_mem : (1 : K) in A
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `ValuationSubring.valuation_le_one_iff`：valuation_le_one_iff (x : K) : A.
valuation x <= 1 ↔ x in A
· 使用定理 `Valuation.map_one_add_of_lt`：map_one_add_of_lt (h : v x < 1) : v (1 + x)
 = 1
· 使用定理 `add_neg_cancel_comm`：∀ {G : Type u_1} [inst : AddCommGroup G] (a b : G),
 a + b + -a = b
· 使用定理 `ValuationSubring.add_mem`：add_mem (x y : K) : x in A -> y in A -> x + y 
in A
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem unitGroup_le_unitGroup {A B : ValuationSubring K} : A.unitGroup ≤ B.unitGroup ↔ A ≤ B := by
  constructor
  · intro h x hx
    rw [← A.valuation_le_one_iff x, le_iff_lt_or_eq] at hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    by_cases h_2 : 1 + x = 0
    · simp only [← add_eq_zero_iff_neg_eq.1 h_2, neg_mem _ _ (one_mem _)]
    rcases hx with hx | hx
    · have := h (show Units.mk0 _ h_2 ∈ A.unitGroup from A.valuation.map_one_add_of_lt hx)
      simpa using
        B.add_mem _ _ (show 1 + x ∈ B from SetLike.coe_mem (B.unitGroupMulEquiv ⟨_, this⟩ : B))
          (B.neg_mem _ B.one_mem)
    · have := h (show Units.mk0 x h_1 ∈ A.unitGroup from hx)
      exact SetLike.coe_mem (B.unitGroupMulEquiv ⟨_, this⟩ : B)
  · rintro h x (hx : A.valuation x = 1)
    apply_fun A.mapOfLE B h at hx
    simpa using hx
/-
**ValuationSubring.unitGroup_injective** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubri
ng`。
形式化陈述：unitGroup_injective : Function.Injective (unitGroup : ValuationSubring K -
> Subgroup _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem unitGroup_injective : Function.Injective (unitGroup : ValuationSubring K → Subgroup _) :=
  fun A B h => by simpa only [le_antisymm_iff, unitGroup_le_unitGroup] using h
/-
**ValuationSubring.eq_iff_unitGroup** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`
。
形式化陈述：eq_iff_unitGroup {A B : ValuationSubring K} : A = B ↔ A.unitGroup = B.unit
Group
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ValuationSubring.unitGroup_injective`：unitGroup_injective : Function.Inj
ective (unitGroup : ValuationSubring K -> Subgroup _)
-/
theorem eq_iff_unitGroup {A B : ValuationSubring K} : A = B ↔ A.unitGroup = B.unitGroup :=
  unitGroup_injective.eq_iff.symm

/-- The map on valuation subrings to their unit groups is an order embedding. -/
/-
**ValuationSubring.unitGroupOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `ValuationS
ubring`。
形式化陈述：unitGroupOrderEmbedding : ValuationSubring K ↪o Subgroup Kˣ where toFun A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.unitGroup_injective`：unitGroup_injective : Function.Inj
ective (unitGroup : ValuationSubring K -> Subgroup _)
· 使用定理 `ValuationSubring.unitGroup_le_unitGroup`：unitGroup_le_unitGroup {A B : V
aluationSubring K} : A.unitGroup <= B.unitGroup ↔ A <= B

--- 原说明 ---
The map on valuation subrings to their unit groups is an order embedding.
-/
def unitGroupOrderEmbedding : ValuationSubring K ↪o Subgroup Kˣ where
  toFun A := A.unitGroup
  inj' := unitGroup_injective
  map_rel_iff' {_A _B} := unitGroup_le_unitGroup
/-
**ValuationSubring.unitGroup_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubr
ing`。
形式化陈述：unitGroup_strictMono : StrictMono (unitGroup : ValuationSubring K -> Subgr
oup _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
-/
theorem unitGroup_strictMono : StrictMono (unitGroup : ValuationSubring K → Subgroup _) :=
  unitGroupOrderEmbedding.strictMono

end UnitGroup

section nonunits

/-- The nonunits of a valuation subring of `K`, as a nonunital subring of `K` -/
/-
**ValuationSubring.nonunits** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：nonunits : NonUnitalSubring K where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nonunits of a valuation subring of `K`, as a nonunital subring of `K`
-/
def nonunits : NonUnitalSubring K where
  carrier := {x | A.valuation x < 1}
  mul_mem' ha hb := (mul_lt_mul'' (Set.mem_ofPred.mp ha) (Set.mem_ofPred.mp hb)
    zero_le zero_le).trans_eq <| mul_one _
  add_mem' ha hb := (A.valuation.map_add ..).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  neg_mem' h := (A.valuation.map_neg _).trans_lt h
/-
**ValuationSubring.mem_nonunits_iff** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`
。
形式化陈述：mem_nonunits_iff {x : K} : x in A.nonunits ↔ A.valuation x < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nonunits_iff {x : K} : x ∈ A.nonunits ↔ A.valuation x < 1 :=
  Iff.rfl
/-
**ValuationSubring.mem_nonunits_iff_or** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubri
ng`。
形式化陈述：mem_nonunits_iff_or {x : K} : x in A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuationSubring.valuation_le_one_iff`：valuation_le_one_iff (x : K) : A.
valuation x <= 1 ↔ x in A
· 使用定理 `or_congr_right'`：or_congr_right' {c : Prop} (h : ¬a -> (b ↔ c)) : a ∨ b 
↔ a ∨ c
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Valuation.one_le_val_iff`：one_le_val_iff (v : Valuation K Γ₀) {x : K} (h
 : x != 0) : 1 <= v x ↔ v x⁻¹ <= 1
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用定理 `ValuationSubring.mem_nonunits_iff`：mem_nonunits_iff {x : K} : x in A.non
units ↔ A.valuation x < 1
· 使用定理 `or_iff_right_of_imp`：∀ {a b : Prop}, (a → b) → (a ∨ b ↔ b)
· 使用定理 `NonUnitalSubring.zero_mem`：∀ {R : Type u} [inst : NonUnitalNonAssocRing 
R] (s : NonUnitalSubring R), 0 ∈ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nonunits_iff_or {x : K} : x ∈ A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A := by
  rw [← valuation_le_one_iff, ← or_congr_right' fun h ↦ (A.valuation.one_le_val_iff h).not,
    ← lt_iff_not_ge, ← mem_nonunits_iff, or_iff_right_of_imp]
  rintro rfl
  exact A.nonunits.zero_mem
/-
**ValuationSubring.inv_mem_nonunits_iff** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubr
ing`。
形式化陈述：inv_mem_nonunits_iff {x : K} : x⁻¹ in A.nonunits ↔ x = 0 ∨ x ∉ A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuationSubring.mem_nonunits_iff_or`：mem_nonunits_iff_or {x : K} : x in
 A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `inv_eq_zero`：inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_mem_nonunits_iff {x : K} : x⁻¹ ∈ A.nonunits ↔ x = 0 ∨ x ∉ A := by
  rw [mem_nonunits_iff_or, inv_inv, inv_eq_zero]
/-
**ValuationSubring.nonunits_le_nonunits** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubr
ing`。
形式化陈述：nonunits_le_nonunits {A B : ValuationSubring K} : B.nonunits <= A.nonunits
 ↔ A <= B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuationSubring.valuation_le_one_iff`：valuation_le_one_iff (x : K) : A.
valuation x <= 1 ↔ x in A
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Valuation.one_lt_val_iff`：one_lt_val_iff (v : Valuation K Γ₀) {x : K} (h
 : x != 0) : 1 < v x ↔ v x⁻¹ < 1
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ValuationSubring.monotone_mapOfLE`：monotone_mapOfLE (R S : ValuationSubr
ing K) (h : R <= S) : Monotone (R.mapOfLE S h)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem nonunits_le_nonunits {A B : ValuationSubring K} : B.nonunits ≤ A.nonunits ↔ A ≤ B := by
  constructor
  · intro h x hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    rw [← valuation_le_one_iff, ← not_lt, Valuation.one_lt_val_iff _ h_1] at hx ⊢
    by_contra h_2; exact hx (h h_2)
  · intro h x hx
    by_contra h_1; exact not_lt.2 (monotone_mapOfLE _ _ h (not_lt.1 h_1)) hx
/-
**ValuationSubring.nonunits_injective** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubrin
g`。
形式化陈述：nonunits_injective : Function.Injective (nonunits : ValuationSubring K -> 
NonUnitalSubring _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonunits_injective :
    Function.Injective (nonunits : ValuationSubring K → NonUnitalSubring _) :=
  fun A B h => by simpa only [le_antisymm_iff, nonunits_le_nonunits] using h.symm
/-
**ValuationSubring.nonunits_inj** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：nonunits_inj {A B : ValuationSubring K} : A.nonunits = B.nonunits ↔ A = B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ValuationSubring.nonunits_injective`：nonunits_injective : Function.Injec
tive (nonunits : ValuationSubring K -> NonUnitalSubring _)
-/
theorem nonunits_inj {A B : ValuationSubring K} : A.nonunits = B.nonunits ↔ A = B :=
  nonunits_injective.eq_iff

/-- The map on valuation subrings to their nonunits is a dual order embedding. -/
/-
**ValuationSubring.nonunitsOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSu
bring`。
形式化陈述：nonunitsOrderEmbedding : ValuationSubring K ↪o (NonUnitalSubring K)ᵒᵈ wher
e toFun A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.nonunits_injective`：nonunits_injective : Function.Injec
tive (nonunits : ValuationSubring K -> NonUnitalSubring _)
· 使用定理 `ValuationSubring.nonunits_le_nonunits`：nonunits_le_nonunits {A B : Valua
tionSubring K} : B.nonunits <= A.nonunits ↔ A <= B

--- 原说明 ---
The map on valuation subrings to their nonunits is a dual order embedding.
-/
def nonunitsOrderEmbedding : ValuationSubring K ↪o (NonUnitalSubring K)ᵒᵈ where
  toFun A := A.nonunits
  inj' := nonunits_injective
  map_rel_iff' {_A _B} := nonunits_le_nonunits

variable {A}

/-- The elements of `A.nonunits` are those of the maximal ideal of `A` after coercion to `K`.

See also `mem_nonunits_iff_exists_mem_maximalIdeal`, which gets rid of the coercion to `K`,
at the expense of a more complicated right-hand side.
-/
/-
**ValuationSubring.coe_mem_nonunits_iff** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubr
ing`。
形式化陈述：coe_mem_nonunits_iff {a : A} : (a : K) in A.nonunits ↔ a in IsLocalRing.ma
ximalIdeal A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `ValuationSubring.valuation_lt_one_iff`：valuation_lt_one_iff (a : A) : a 
in IsLocalRing.maximalIdeal A ↔ A.valuation a < 1

--- 原说明 ---
The elements of `A.nonunits` are those of the maximal ideal of `A` after coercio
n to `K`.

See also `mem_nonunits_iff_exists_mem_maximalIdeal`, which gets rid of the coerc
ion to `K`,
at the expense of a more complicated right-hand side.
-/
theorem coe_mem_nonunits_iff {a : A} : (a : K) ∈ A.nonunits ↔ a ∈ IsLocalRing.maximalIdeal A :=
  (valuation_lt_one_iff _ _).symm
/-
**ValuationSubring.nonunits_le** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：nonunits_le : A.nonunits <= A.toNonUnitalSubring
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ValuationSubring.valuation_le_one_iff`：valuation_le_one_iff (x : K) : A.
valuation x <= 1 ↔ x in A
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ValuationSubring.mem_nonunits_iff`：mem_nonunits_iff {x : K} : x in A.non
units ↔ A.valuation x < 1
-/
theorem nonunits_le : A.nonunits ≤ A.toNonUnitalSubring := fun _a ha =>
  (A.valuation_le_one_iff _).mp (A.mem_nonunits_iff.mp ha).le
/-
**ValuationSubring.nonunits_subset** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：nonunits_subset : (A.nonunits : Set K) subseteq A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.nonunits_le`：nonunits_le : A.nonunits <= A.toNonUnitalS
ubring
-/
theorem nonunits_subset : (A.nonunits : Set K) ⊆ A :=
  nonunits_le

/-- The elements of `A.nonunits` are those of the maximal ideal of `A`.

See also `coe_mem_nonunits_iff`, which has a simpler right-hand side but requires the element
to be in `A` already.
-/
/-
**ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal** 是 Mathlib 中的一个定理，位
于命名空间 `ValuationSubring`。
形式化陈述：mem_nonunits_iff_exists_mem_maximalIdeal {a : K} : a in A.nonunits ↔ exist
s ha, (⟨a, ha⟩ : A) in IsLocalRing.maximalIdeal A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `ValuationSubring.nonunits_subset`：nonunits_subset : (A.nonunits : Set K)
 subseteq A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ValuationSubring.coe_mem_nonunits_iff`：coe_mem_nonunits_iff {a : A} : (a
 : K) in A.nonunits ↔ a in IsLocalRing.maximalIdeal A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
The elements of `A.nonunits` are those of the maximal ideal of `A`.

See also `coe_mem_nonunits_iff`, which has a simpler right-hand side but require
s the element
to be in `A` already.
-/
theorem mem_nonunits_iff_exists_mem_maximalIdeal {a : K} :
    a ∈ A.nonunits ↔ ∃ ha, (⟨a, ha⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
  ⟨fun h => ⟨nonunits_subset h, coe_mem_nonunits_iff.mp h⟩, fun ⟨_, h⟩ =>
    coe_mem_nonunits_iff.mpr h⟩

/-- `A.nonunits` agrees with the maximal ideal of `A`, after taking its image in `K`. -/
/-
**ValuationSubring.image_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubrin
g`。
形式化陈述：image_maximalIdeal : ((↑) : A -> K) '' IsLocalRing.maximalIdeal A = A.nonu
nits
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.exists`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∃ x, q x) ↔ ∃ a, ∃ (b : p a), q ⟨a, b⟩
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`A.nonunits` agrees with the maximal ideal of `A`, after taking its image in `K`
.
-/
theorem image_maximalIdeal : ((↑) : A → K) '' IsLocalRing.maximalIdeal A = A.nonunits := by
  ext a
  simp only [Set.mem_image, SetLike.mem_coe, mem_nonunits_iff_exists_mem_maximalIdeal]
  rw [Subtype.exists]
  simp_rw [exists_and_right, exists_eq_right]

end nonunits

section PrincipalUnitGroup

/-- The principal unit group of a valuation subring, as a subgroup of `Kˣ`. -/
/-
**ValuationSubring.principalUnitGroup** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubrin
g`。
形式化陈述：principalUnitGroup : Subgroup Kˣ where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The principal unit group of a valuation subring, as a subgroup of `Kˣ`.
-/
def principalUnitGroup : Subgroup Kˣ where
  carrier := {x | A.valuation (x - 1) < 1}
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_ofPred] at ha hb ⊢
    refine lt_of_le_of_lt ?_ (max_lt hb ha)
    rw [← one_mul (A.valuation (b - 1)), ← A.valuation.map_one_add_of_lt ha, add_sub_cancel,
      ← Valuation.map_mul, mul_sub_one, ← sub_add_sub_cancel]
    exact A.valuation.map_add _ _
  one_mem' := by simp
  inv_mem' := by
    dsimp
    intro a ha
    conv =>
      lhs
      rw [← mul_one (A.valuation _), ← A.valuation.map_one_add_of_lt ha]
    rwa [add_sub_cancel, ← Valuation.map_mul, sub_mul, Units.inv_mul, ← neg_sub, one_mul,
      Valuation.map_neg]
/-
**ValuationSubring.principal_units_le_units** 是 Mathlib 中的一个定理，位于命名空间 `Valuation
Subring`。
形式化陈述：principal_units_le_units : A.principalUnitGroup <= A.unitGroup
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `Valuation.map_one_add_of_lt`：map_one_add_of_lt (h : v x < 1) : v (1 + x)
 = 1
-/
theorem principal_units_le_units : A.principalUnitGroup ≤ A.unitGroup := fun a h => by
  simpa only [add_sub_cancel] using! A.valuation.map_one_add_of_lt h
/-
**ValuationSubring.mem_principalUnitGroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuati
onSubring`。
形式化陈述：mem_principalUnitGroup_iff (x : Kˣ) : x in A.principalUnitGroup ↔ A.valuat
ion ((x : K) - 1) < 1
参数：x : Kˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_principalUnitGroup_iff (x : Kˣ) :
    x ∈ A.principalUnitGroup ↔ A.valuation ((x : K) - 1) < 1 :=
  Iff.rfl
/-
**ValuationSubring.principalUnitGroup_le_principalUnitGroup** 是 Mathlib 中的一个定理，位
于命名空间 `ValuationSubring`。
形式化陈述：principalUnitGroup_le_principalUnitGroup {A B : ValuationSubring K} : B.pr
incipalUnitGroup <= A.principalUnitGroup ↔ A <= B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `inv_eq_iff_eq_inv`：inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `ValuationSubring.neg_mem`：neg_mem (x : K) : x in A -> -x in A
· 使用定理 `ValuationSubring.one_mem`：one_mem : (1 : K) in A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuationSubring.valuation_le_one_iff`：valuation_le_one_iff (x : K) : A.
valuation x <= 1 ↔ x in A
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Valuation.one_lt_val_iff`：one_lt_val_iff (v : Valuation K Γ₀) {x : K} (h
 : x != 0) : 1 < v x ↔ v x⁻¹ < 1
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Units.val_mk0`：val_mk0 {a : G₀} (h : a != 0) : (mk0 a h : G₀) = a
· 使用定理 `ValuationSubring.mem_principalUnitGroup_iff`：mem_principalUnitGroup_iff 
(x : Kˣ) : x in A.principalUnitGroup ↔ A.valuation ((x : K) - 1) < 1
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ValuationSubring.monotone_mapOfLE`：monotone_mapOfLE (R S : ValuationSubr
ing K) (h : R <= S) : Monotone (R.mapOfLE S h)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem principalUnitGroup_le_principalUnitGroup {A B : ValuationSubring K} :
    B.principalUnitGroup ≤ A.principalUnitGroup ↔ A ≤ B := by
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
/-
**ValuationSubring.principalUnitGroup_injective** 是 Mathlib 中的一个定理，位于命名空间 `Valua
tionSubring`。
形式化陈述：principalUnitGroup_injective : Function.Injective (principalUnitGroup : Va
luationSubring K -> Subgroup _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem principalUnitGroup_injective :
    Function.Injective (principalUnitGroup : ValuationSubring K → Subgroup _) := fun A B h => by
  simpa [le_antisymm_iff, principalUnitGroup_le_principalUnitGroup] using h.symm
/-
**ValuationSubring.eq_iff_principalUnitGroup** 是 Mathlib 中的一个定理，位于命名空间 `Valuatio
nSubring`。
形式化陈述：eq_iff_principalUnitGroup {A B : ValuationSubring K} : A = B ↔ A.principal
UnitGroup = B.principalUnitGroup
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ValuationSubring.principalUnitGroup_injective`：principalUnitGroup_inject
ive : Function.Injective (principalUnitGroup : ValuationSubring K -> Subgroup _)
-/
theorem eq_iff_principalUnitGroup {A B : ValuationSubring K} :
    A = B ↔ A.principalUnitGroup = B.principalUnitGroup :=
  principalUnitGroup_injective.eq_iff.symm

/-- The map on valuation subrings to their principal unit groups is an order embedding. -/
/-
**ValuationSubring.principalUnitGroupOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `V
aluationSubring`。
形式化陈述：principalUnitGroupOrderEmbedding : ValuationSubring K ↪o (Subgroup Kˣ)ᵒᵈ w
here toFun A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.principalUnitGroup_injective`：principalUnitGroup_inject
ive : Function.Injective (principalUnitGroup : ValuationSubring K -> Subgroup _)
· 使用定理 `ValuationSubring.principalUnitGroup_le_principalUnitGroup`：principalUnit
Group_le_principalUnitGroup {A B : ValuationSubring K} : B.principalUnitGroup <=
 A.principalUnitGroup ↔ A <= B

--- 原说明 ---
The map on valuation subrings to their principal unit groups is an order embeddi
ng.
-/
def principalUnitGroupOrderEmbedding : ValuationSubring K ↪o (Subgroup Kˣ)ᵒᵈ where
  toFun A := A.principalUnitGroup
  inj' := principalUnitGroup_injective
  map_rel_iff' {_A _B} := principalUnitGroup_le_principalUnitGroup
/-
**ValuationSubring.coe_mem_principalUnitGroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Val
uationSubring`。
形式化陈述：coe_mem_principalUnitGroup_iff {x : A.unitGroup} : (x : Kˣ) in A.principal
UnitGroup ↔ A.unitGroupMulEquiv x in (Units.map (IsLocalRing.residue A).toMonoid
Hom).ker
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `RingHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x y : α),   f (x - y) = f x - f y
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `ValuationSubring.valuation_lt_one_iff`：valuation_lt_one_iff (a : A) : a 
in IsLocalRing.maximalIdeal A ↔ A.valuation a < 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_mem_principalUnitGroup_iff {x : A.unitGroup} :
    (x : Kˣ) ∈ A.principalUnitGroup ↔
      A.unitGroupMulEquiv x ∈ (Units.map (IsLocalRing.residue A).toMonoidHom).ker := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  let π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
  convert_to! _ ↔ π _ = 1
  rw [← π.map_one, ← sub_eq_zero, ← π.map_sub, Ideal.Quotient.eq_zero_iff_mem, valuation_lt_one_iff]
  simp [mem_principalUnitGroup_iff]

set_option backward.isDefEq.respectTransparency.types false in
/-- The principal unit group agrees with the kernel of the canonical map from
the units of `A` to the units of the residue field of `A`. -/
/-
**ValuationSubring.principalUnitGroupEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ValuationS
ubring`。
形式化陈述：principalUnitGroupEquiv : A.principalUnitGroup ≃* (Units.map (IsLocalRing.
residue A).toMonoidHom).ker where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The principal unit group agrees with the kernel of the canonical map from
the units of `A` to the units of the residue field of `A`.
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
/-
**ValuationSubring.principalUnitGroupEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Valu
ationSubring`。
形式化陈述：principalUnitGroupEquiv_apply (a : A.principalUnitGroup) : (((principalUni
tGroupEquiv A a : Aˣ) : A) : K) = (a : Kˣ)
参数：a : A.principalUnitGroup。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
-/
theorem principalUnitGroupEquiv_apply (a : A.principalUnitGroup) :
    (((principalUnitGroupEquiv A a : Aˣ) : A) : K) = (a : Kˣ) :=
  rfl
/-
**ValuationSubring.principalUnitGroup_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Valu
ationSubring`。
形式化陈述：principalUnitGroup_symm_apply (a : (Units.map (IsLocalRing.residue A).toMo
noidHom).ker) : ((A.principalUnitGroupEquiv.symm a : Kˣ) : K) = ((a : Aˣ) : A)
参数：a : (Units.map (IsLocalRing.residue A).toMonoidHom).ker。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
-/
theorem principalUnitGroup_symm_apply (a : (Units.map (IsLocalRing.residue A).toMonoidHom).ker) :
    ((A.principalUnitGroupEquiv.symm a : Kˣ) : K) = ((a : Aˣ) : A) :=
  rfl

/-- The canonical map from the unit group of `A` to the units of the residue field of `A`. -/
/-
**ValuationSubring.unitGroupToResidueFieldUnits** 是 Mathlib 中的一个定义，位于命名空间 `Valua
tionSubring`。
形式化陈述：unitGroupToResidueFieldUnits : A.unitGroup ->* (IsLocalRing.ResidueField A
)ˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the unit group of `A` to the units of the residue field o
f `A`.
-/
def unitGroupToResidueFieldUnits : A.unitGroup →* (IsLocalRing.ResidueField A)ˣ :=
  MonoidHom.comp (Units.map <| (Ideal.Quotient.mk _).toMonoidHom) A.unitGroupMulEquiv.toMonoidHom

@[simp]
/-
**ValuationSubring.coe_unitGroupToResidueFieldUnits_apply** 是 Mathlib 中的一个定理，位于命
名空间 `ValuationSubring`。
形式化陈述：coe_unitGroupToResidueFieldUnits_apply (x : A.unitGroup) : (A.unitGroupToR
esidueFieldUnits x : IsLocalRing.ResidueField A) = Ideal.Quotient.mk _ (A.unitGr
oupMulEquiv x : A)
参数：x : A.unitGroup。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_unitGroupToResidueFieldUnits_apply (x : A.unitGroup) :
    (A.unitGroupToResidueFieldUnits x : IsLocalRing.ResidueField A) =
      Ideal.Quotient.mk _ (A.unitGroupMulEquiv x : A) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**ValuationSubring.ker_unitGroupToResidueFieldUnits** 是 Mathlib 中的一个定理，位于命名空间 `V
aluationSubring`。
形式化陈述：ker_unitGroupToResidueFieldUnits : A.unitGroupToResidueFieldUnits.ker = A.
principalUnitGroup.comap A.unitGroup.subtype
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_unitGroupToResidueFieldUnits :
    A.unitGroupToResidueFieldUnits.ker = A.principalUnitGroup.comap A.unitGroup.subtype := by
  ext
  simp_rw [Subgroup.mem_comap, Subgroup.coe_subtype, coe_mem_principalUnitGroup_iff,
    unitGroupToResidueFieldUnits, IsLocalRing.residue, RingHom.toMonoidHom_eq_coe,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.mem_ker, MonoidHom.coe_comp, MonoidHom.coe_coe,
    Function.comp_apply]
/-
**ValuationSubring.surjective_unitGroupToResidueFieldUnits** 是 Mathlib 中的一个定理，位于
命名空间 `ValuationSubring`。
形式化陈述：surjective_unitGroupToResidueFieldUnits : Function.Surjective A.unitGroupT
oResidueFieldUnits
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `IsLocalRing.surjective_units_map_of_local_ringHom`：surjective_units_map_
of_local_ringHom [Semiring R] [Semiring S] (f : R ->+* S) (hf : Function.Surject
ive f) (h : IsLocalHom f) : Function.Su…
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
-/
theorem surjective_unitGroupToResidueFieldUnits :
    Function.Surjective A.unitGroupToResidueFieldUnits :=
  IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective
    (inferInstanceAs (IsLocalHom (IsLocalRing.residue A))) |>.comp (MulEquiv.surjective _)

/-- The quotient of the unit group of `A` by the principal unit group of `A` agrees with
the units of the residue field of `A`. -/
/-
**ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits** 是 Mathlib 中的一个
定义，位于命名空间 `ValuationSubring`。
形式化陈述：unitsModPrincipalUnitsEquivResidueFieldUnits : A.unitGroup ⧸ A.principalUn
itGroup.comap A.unitGroup.subtype ≃* (IsLocalRing.ResidueField A)ˣ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.surjective_unitGroupToResidueFieldUnits`：surjective_uni
tGroupToResidueFieldUnits : Function.Surjective A.unitGroupToResidueFieldUnits

--- 原说明 ---
The quotient of the unit group of `A` by the principal unit group of `A` agrees 
with
the units of the residue field of `A`.
-/
def unitsModPrincipalUnitsEquivResidueFieldUnits :
    A.unitGroup ⧸ A.principalUnitGroup.comap A.unitGroup.subtype ≃* (IsLocalRing.ResidueField A)ˣ :=
  QuotientGroup.liftEquiv _ A.surjective_unitGroupToResidueFieldUnits
    A.ker_unitGroupToResidueFieldUnits.symm

set_option backward.isDefEq.respectTransparency false in
/-
**ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGro
up_mk** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk : (A.un
itsModPrincipalUnitsEquivResidueFieldUnits : _ ⧸ Subgroup.comap _ _ ->* _).comp 
(QuotientGroup.mk' (A.principalUnitGroup.subgroupOf A.unitGroup)) = A.unitGroupT
oResidueFieldUnits
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_subgroupOf`：∀ {G : Type u_1} [inst : Group G] {H N : Sub
group G} [N.Normal], (N.subgroupOf H).Normal
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `Subgroup.normal_comap`：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} 
[inst_1 : Group N] {H : Subgroup N} [nH : H.Normal] (f : G →* N),   (Subgroup.co
map f H).No…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk :
    (A.unitsModPrincipalUnitsEquivResidueFieldUnits : _ ⧸ Subgroup.comap _ _ →* _).comp
        (QuotientGroup.mk' (A.principalUnitGroup.subgroupOf A.unitGroup)) =
      A.unitGroupToResidueFieldUnits := rfl
/-
**ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGro
up_mk_apply** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk_apply (
x : A.unitGroup) : A.unitsModPrincipalUnitsEquivResidueFieldUnits.toMonoidHom (Q
uotientGroup.mk x) = A.unitGroupToResidueFieldUnits x
参数：x : A.unitGroup。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_comap`：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} 
[inst_1 : Group N] {H : Subgroup N} [nH : H.Normal] (f : G →* N),   (Subgroup.co
map f H).No…
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
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
/-
**ValuationSubring.pointwiseHasSMul** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`
。
形式化陈述：pointwiseHasSMul : SMul G (ValuationSubring K) where smul g S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on a valuation subring corresponding to applying the action to every 
element.

This is available as an instance in the `Pointwise` locale.
-/
def pointwiseHasSMul : SMul G (ValuationSubring K) where
  smul g S := -- TODO: if we add `ValuationSubring.map` at a later date, we should use it here
    { g • S.toSubring with
      mem_or_inv_mem' := fun x =>
        (mem_or_inv_mem S (g⁻¹ • x)).imp Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr fun h =>
          Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr <| by rwa [smul_inv''] }

scoped[Pointwise] attribute [instance] ValuationSubring.pointwiseHasSMul

open scoped Pointwise

@[simp]
/-
**ValuationSubring.coe_pointwise_smul** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubrin
g`。
形式化陈述：coe_pointwise_smul (g : G) (S : ValuationSubring K) : ↑(g • S) = g • (S : 
Set K)
参数：g : G；S : ValuationSubring K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pointwise_smul (g : G) (S : ValuationSubring K) : ↑(g • S) = g • (S : Set K) := rfl

@[simp]
/-
**ValuationSubring.pointwise_smul_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `Valuation
Subring`。
形式化陈述：pointwise_smul_toSubring (g : G) (S : ValuationSubring K) : (g • S).toSubr
ing = g • S.toSubring
参数：g : G；S : ValuationSubring K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_toSubring (g : G) (S : ValuationSubring K) :
    (g • S).toSubring = g • S.toSubring := rfl

/-- The action on a valuation subring corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.

This is a stronger version of `ValuationSubring.pointwiseSMul`. -/
@[instance_reducible]
/-
**ValuationSubring.pointwiseMulAction** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubrin
g`。
形式化陈述：pointwiseMulAction : MulAction G (ValuationSubring K)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.toSubring_injective`：toSubring_injective : Function.Inj
ective (toSubring : ValuationSubring K -> Subring K)
· 使用定理 `ValuationSubring.pointwise_smul_toSubring`：pointwise_smul_toSubring (g :
 G) (S : ValuationSubring K) : (g • S).toSubring = g • S.toSubring

--- 原说明 ---
The action on a valuation subring corresponding to applying the action to every 
element.

This is available as an instance in the `Pointwise` locale.

This is a stronger version of `ValuationSubring.pointwiseSMul`.
-/
def pointwiseMulAction : MulAction G (ValuationSubring K) :=
  toSubring_injective.mulAction toSubring pointwise_smul_toSubring

scoped[Pointwise] attribute [instance] ValuationSubring.pointwiseMulAction

open scoped Pointwise
/-
**ValuationSubring.smul_mem_pointwise_smul** 是 Mathlib 中的一个定理，位于命名空间 `ValuationS
ubring`。
形式化陈述：smul_mem_pointwise_smul (g : G) (x : K) (S : ValuationSubring K) : x in S 
-> g • x in g • S
参数：g : G；x : K；S : ValuationSubring K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem smul_mem_pointwise_smul (g : G) (x : K) (S : ValuationSubring K) : x ∈ S → g • x ∈ g • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ g • (S : Set K))
/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CovariantClass G (ValuationSubring K) HSMul.hSMul LE.le :=
  ⟨fun _ _ _ => Set.image_mono⟩
/-
**ValuationSubring.mem_smul_pointwise_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Valu
ationSubring`。
形式化陈述：mem_smul_pointwise_iff_exists (g : G) (x : K) (S : ValuationSubring K) : x
 in g • S ↔ exists s : K, s in S ∧ g • s = x
参数：g : G；x : K；S : ValuationSubring K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
-/
theorem mem_smul_pointwise_iff_exists (g : G) (x : K) (S : ValuationSubring K) :
    x ∈ g • S ↔ ∃ s : K, s ∈ S ∧ g • s = x :=
  (Set.mem_smul_set : x ∈ g • (S : Set K) ↔ _)
/-
**ValuationSubring.pointwise_central_scalar** 是 Mathlib 中的一个实例，位于命名空间 `Valuation
Subring`。
形式化陈述：pointwise_central_scalar [MulSemiringAction Gᵐᵒᵖ K] [IsCentralScalar G K] 
: IsCentralScalar G (ValuationSubring K)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.toSubring_injective`：toSubring_injective : Function.Inj
ective (toSubring : ValuationSubring K -> Subring K)
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance pointwise_central_scalar [MulSemiringAction Gᵐᵒᵖ K] [IsCentralScalar G K] :
    IsCentralScalar G (ValuationSubring K) :=
  ⟨fun g S => toSubring_injective <| op_smul_eq_smul g S.toSubring⟩

@[simp]
/-
**ValuationSubring.smul_mem_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuat
ionSubring`。
形式化陈述：smul_mem_pointwise_smul_iff {g : G} {S : ValuationSubring K} {x : K} : g •
 x in g • S ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
-/
theorem smul_mem_pointwise_smul_iff {g : G} {S : ValuationSubring K} {x : K} :
    g • x ∈ g • S ↔ x ∈ S := Set.smul_mem_smul_set_iff
/-
**ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem** 是 Mathlib 中的一个定理，位于命名空间
 `ValuationSubring`。
形式化陈述：mem_pointwise_smul_iff_inv_smul_mem {g : G} {S : ValuationSubring K} {x : 
K} : x in g • S ↔ g⁻¹ • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
-/
theorem mem_pointwise_smul_iff_inv_smul_mem {g : G} {S : ValuationSubring K} {x : K} :
    x ∈ g • S ↔ g⁻¹ • x ∈ S := Set.mem_smul_set_iff_inv_smul_mem
/-
**ValuationSubring.mem_inv_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuati
onSubring`。
形式化陈述：mem_inv_pointwise_smul_iff {g : G} {S : ValuationSubring K} {x : K} : x in
 g⁻¹ • S ↔ g • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inv_smul_set_iff`：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in
 A
-/
theorem mem_inv_pointwise_smul_iff {g : G} {S : ValuationSubring K} {x : K} :
    x ∈ g⁻¹ • S ↔ g • x ∈ S := Set.mem_inv_smul_set_iff

@[simp]
/-
**ValuationSubring.pointwise_smul_le_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空
间 `ValuationSubring`。
形式化陈述：pointwise_smul_le_pointwise_smul_iff {g : G} {S T : ValuationSubring K} : 
g • S <= g • T ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_smul_set_iff`：smul_set_subset_smul_set_iff : a • A s
ubseteq a • B ↔ A subseteq B
-/
theorem pointwise_smul_le_pointwise_smul_iff {g : G} {S T : ValuationSubring K} :
    g • S ≤ g • T ↔ S ≤ T := Set.smul_set_subset_smul_set_iff
/-
**ValuationSubring.pointwise_smul_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuatio
nSubring`。
形式化陈述：pointwise_smul_subset_iff {g : G} {S T : ValuationSubring K} : g • S <= T 
↔ S <= g⁻¹ • T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_iff_subset_inv_smul_set`：smul_set_subset_iff_subset_
inv_smul_set : a • A subseteq B ↔ A subseteq a⁻¹ • B
-/
theorem pointwise_smul_subset_iff {g : G} {S T : ValuationSubring K} : g • S ≤ T ↔ S ≤ g⁻¹ • T :=
  Set.smul_set_subset_iff_subset_inv_smul_set
/-
**ValuationSubring.subset_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuatio
nSubring`。
形式化陈述：subset_pointwise_smul_iff {g : G} {S T : ValuationSubring K} : S <= g • T 
↔ g⁻¹ • S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_smul_set_iff`：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • 
A subseteq B
-/
theorem subset_pointwise_smul_iff {g : G} {S T : ValuationSubring K} : S ≤ g • T ↔ g⁻¹ • S ≤ T :=
  Set.subset_smul_set_iff

end PointwiseActions

section

variable {L J : Type*} [Field L] [Field J]

/-- The pullback of a valuation subring `A` along a ring homomorphism `K →+* L`. -/
/-
**ValuationSubring.comap** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：comap (A : ValuationSubring L) (f : K ->+* L) : ValuationSubring K
参数：A : ValuationSubring L；f : K ->+* L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a valuation subring `A` along a ring homomorphism `K →+* L`.
-/
def comap (A : ValuationSubring L) (f : K →+* L) : ValuationSubring K :=
  { A.toSubring.comap f with mem_or_inv_mem' := fun k => by simp [ValuationSubring.mem_or_inv_mem] }

@[simp]
/-
**ValuationSubring.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：coe_comap (A : ValuationSubring L) (f : K ->+* L) : (A.comap f : Set K) = 
f ⁻¹' A
参数：A : ValuationSubring L；f : K ->+* L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (A : ValuationSubring L) (f : K →+* L) : (A.comap f : Set K) = f ⁻¹' A := rfl

@[simp]
/-
**ValuationSubring.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：mem_comap {A : ValuationSubring L} {f : K ->+* L} {x : K} : x in A.comap f
 ↔ f x in A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {A : ValuationSubring L} {f : K →+* L} {x : K} : x ∈ A.comap f ↔ f x ∈ A :=
  Iff.rfl
/-
**ValuationSubring.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubring`。
形式化陈述：comap_comap (A : ValuationSubring J) (g : L ->+* J) (f : K ->+* L) : (A.co
map g).comap f = A.comap (g.comp f)
参数：A : ValuationSubring J；g : L ->+* J；f : K ->+* L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap (A : ValuationSubring J) (g : L →+* J) (f : K →+* L) :
    (A.comap g).comap f = A.comap (g.comp f) := rfl

end

end ValuationSubring

namespace Valuation

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (x : Kˣ)

/-
**Valuation.mem_unitGroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：mem_unitGroup_iff : x in v.valuationSubring.unitGroup ↔ v x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valuation.IsEquiv.eq_one_iff_eq_one`：eq_one_iff_eq_one (h : v₁.IsEquiv v
₂) {x : R} : v₁ x = 1 ↔ v₂ x = 1
· 使用定理 `Valuation.IsEquiv.symm`：symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁
· 使用定理 `Valuation.isEquiv_valuation_valuationSubring`：isEquiv_valuation_valuatio
nSubring : v.IsEquiv v.valuationSubring.valuation
-/
theorem mem_unitGroup_iff : x ∈ v.valuationSubring.unitGroup ↔ v x = 1 :=
  IsEquiv.eq_one_iff_eq_one (Valuation.isEquiv_valuation_valuationSubring _).symm
/-
**Valuation.mem_maximalIdeal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：mem_maximalIdeal_iff {a : v.valuationSubring} : a in IsLocalRing.maximalId
eal (v.valuationSubring) ↔ v a < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.Integer.not_isUnit_iff_valuation_lt_one`：∀ {F : Type u} {Γ₀ : 
Type v} [inst : Field F] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valua
tion F Γ₀}   {x : ↥v.integer}, ¬IsUnit …
-/
theorem mem_maximalIdeal_iff {a : v.valuationSubring} :
    a ∈ IsLocalRing.maximalIdeal (v.valuationSubring) ↔ v a < 1 :=
  Integer.not_isUnit_iff_valuation_lt_one

end Valuation

