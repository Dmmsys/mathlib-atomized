/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.Algebra.Field.Equiv
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Submonoid
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Fraction ring / fraction field Frac(R) as localization

## Main definitions

* `IsFractionRing R K` expresses that `K` is a field of fractions of `R`, as an abbreviation of
  `IsLocalization (NonZeroDivisors R) K`

## Main results

* `IsFractionRing.field`: a definition (not an instance) stating the localization of an integral
  domain `R` at `R \ {0}` is a field
* `Rat.isFractionRing` is an instance stating `ℚ` is the field of fractions of `ℤ`

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section

assert_not_exists Ideal

open nonZeroDivisors

variable (R : Type*) [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]
variable [Algebra R S] {P : Type*} [CommRing P]
variable {A : Type*} [CommRing A] (K : Type*)

-- TODO: should this extend `Algebra` instead of assuming it?
-- TODO: this was recently generalized from `CommRing` to `CommSemiring`, but all lemmas below are
-- still stated for `CommRing`. Generalize these lemmas where it is appropriate.
/-- `IsFractionRing R K` states `K` is the ring of fractions of a commutative ring `R`. -/
/-
**IsFractionRing** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsFractionRing (R : Type*) [CommSemiring R] (K : Type*) [CommSemiring K] [
Algebra R K]
参数：R : Type*；K : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsFractionRing R K` states `K` is the ring of fractions of a commutative ring `
R`.
-/
abbrev IsFractionRing (R : Type*) [CommSemiring R] (K : Type*) [CommSemiring K] [Algebra R K] :=
  IsLocalization (nonZeroDivisors R) K
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [Field R] : IsFractionRing R R :=
  IsLocalization.of_le_isUnit fun _ ↦ isUnit_of_mem_nonZeroDivisors
/-
**IsFractionRing.of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsFractionRing.of_algEquiv {R : Type*} [CommSemiring R] {K L : Type*} [Com
mSemiring K] [Algebra R K] [CommSemiring L] [Algebra R L] [h : IsFractionRing R 
K] (e : K ≃ₐ[R] L) : IsFractionRing R L
参数：e : K ≃ₐ[R] L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isLocalization_of_algEquiv`：isLocalization_of_algEquiv [A
lgebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) : IsLocalization M P
-/
theorem IsFractionRing.of_algEquiv {R : Type*} [CommSemiring R] {K L : Type*}
    [CommSemiring K] [Algebra R K] [CommSemiring L] [Algebra R L] [h : IsFractionRing R K]
    (e : K ≃ₐ[R] L) :
    IsFractionRing R L := IsLocalization.isLocalization_of_algEquiv _ e

/-- The cast from `Int` to `Rat` as a `FractionRing`. -/
/-
**Rat.isFractionRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Rat.isFractionRing : IsFractionRing Int Rat where map_units
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Int.natCast_ne_zero_iff_pos`：∀ {n : ℕ}, ↑n ≠ 0 ↔ 0 < n
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `Rat.mul_den_eq_num`：∀ (q : ℚ), q * ↑q.den = ↑q.num
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n

--- 原说明 ---
The cast from `Int` to `Rat` as a `FractionRing`.
-/
instance Rat.isFractionRing : IsFractionRing ℤ ℚ where
  map_units := by
    rintro ⟨x, hx⟩
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    simpa only [eq_intCast, isUnit_iff_ne_zero, Int.cast_eq_zero, Ne, Subtype.coe_mk] using hx
  surj := by
    rintro ⟨n, d, hd, h⟩
    refine ⟨⟨n, ⟨d, ?_⟩⟩, Rat.mul_den_eq_num _⟩
    rw [mem_nonZeroDivisors_iff_ne_zero, Int.natCast_ne_zero_iff_pos]
    exact Nat.zero_lt_of_ne_zero hd
  exists_of_eq {x y} := by
    rw [eq_intCast, eq_intCast, Int.cast_inj]
    rintro rfl
    use 1

/-- As a corollary, `Rat` is also a localization at only positive integers. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As a corollary, `Rat` is also a localization at only positive integers.
-/
instance : IsLocalization (Submonoid.pos ℤ) ℚ where
  map_units y := by simpa using y.prop.ne'
  surj z := by
    obtain ⟨⟨x1, x2⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors ℤ) z
    obtain hx2 | hx2 := lt_or_gt_of_ne (show x2.val ≠ 0 by simp)
    · exact ⟨⟨-x1, ⟨-x2.val, by simpa using hx2⟩⟩, by simpa using hx⟩
    · exact ⟨⟨x1, ⟨x2.val, hx2⟩⟩, hx⟩
  exists_of_eq {x y} h := ⟨1, by simpa using Rat.intCast_inj.mp h⟩

/-- `NNRat` is the ring of fractions of `Nat`. -/
/-
**NNRat.isFractionRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NNRat.isFractionRing : IsFractionRing Nat Rat>=0 where map_units y
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNRat.mul_den_eq_num`：∀ (q : ℚ≥0), q * ↑q.den = ↑q.num
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
`NNRat` is the ring of fractions of `Nat`.
-/
instance NNRat.isFractionRing : IsFractionRing ℕ ℚ≥0 where
  map_units y := by simp
  surj z := ⟨⟨z.num, ⟨z.den, by simp⟩⟩, by simp⟩
  exists_of_eq {x y} h := ⟨1, by simpa using h⟩

namespace IsFractionRing

open IsLocalization

/-
**IsFractionRing.of_field** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：of_field [Field K] [Algebra R K] [FaithfulSMul R K] (surj : forall z : K, 
exists x y, z = algebraMap R K x / algebraMap R K y) : IsFractionRing R K
参数：surj : forall z : K, exists x y, z = algebraMap R K x / algebraMap R K y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Function.Injective.noZeroDivisors`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [i
nst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : M
₀ → M₀'),   Function.In…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
（共 32 条，此处仅展示前 30 条）
-/
theorem of_field [Field K] [Algebra R K] [FaithfulSMul R K]
    (surj : ∀ z : K, ∃ x y, z = algebraMap R K x / algebraMap R K y) :
    IsFractionRing R K :=
  have inj := FaithfulSMul.algebraMap_injective R K
  have := inj.noZeroDivisors _ (map_zero _) (map_mul _)
  have := Module.nontrivial R K
{ map_units x :=
    .mk0 _ <| (map_ne_zero_iff _ inj).mpr <| mem_nonZeroDivisors_iff_ne_zero.mp x.2
  surj z := by
    have ⟨x, y, eq⟩ := surj z
    obtain rfl | hy := eq_or_ne y 0
    · obtain rfl : z = 0 := by simpa using eq
      exact ⟨(0, 1), by simp⟩
    exact ⟨⟨x, y, mem_nonZeroDivisors_iff_ne_zero.mpr hy⟩,
      (eq_div_iff_mul_eq <| (map_ne_zero_iff _ inj).mpr hy).mp eq⟩
  exists_of_eq eq := ⟨1, by simpa using inj eq⟩ }

variable {R K}

section CommSemiring

/-
**IsFractionRing.of_ringEquiv_left** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：of_ringEquiv_left {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S
] {K : Type*} [CommSemiring K] [Algebra R K] (e : R ≃+* S) [Algebra S K] (h : fo
rall x, algebraMap R K x = algebraMap S K (e x)) [IsFractionRing S K] : IsFracti
onRing R K
参数：e : R ≃+* S；h : forall x, algebraMap R K x = algebraMap S K (e x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.of_ringEquiv_left`：of_ringEquiv_left {S : Type*} [CommSem
iring S] {K : Type*} [CommSemiring K] [Algebra R K] (e : R ≃+* S) [Algebra S K] 
{M₁ : Submonoid S} {M₂…
· 使用定理 `MulEquivClass.map_nonZeroDivisors`：MulEquivClass.map_nonZeroDivisors {M₀
 S F : Type*} [MonoidWithZero M₀] [MonoidWithZero S] [EquivLike F M₀ S] [MulEqui
vClass F M₀ S] (h : F) …
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem of_ringEquiv_left {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]
    {K : Type*} [CommSemiring K] [Algebra R K] (e : R ≃+* S) [Algebra S K]
    (h : ∀ x, algebraMap R K x = algebraMap S K (e x)) [IsFractionRing S K] :
    IsFractionRing R K := IsLocalization.of_ringEquiv_left e (MulEquivClass.map_nonZeroDivisors e) h

end CommSemiring

section CommRing

variable [CommRing K] [Algebra R K] [IsFractionRing R K] [Algebra A K] [IsFractionRing A K]

/-
**IsFractionRing.to_map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：to_map_eq_zero_iff {x : R} : algebraMap R K x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.to_map_eq_zero_iff`：to_map_eq_zero_iff {x : R} (hM : M <=
 nonZeroDivisors R) : algebraMap R S x = 0 ↔ x = 0
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem to_map_eq_zero_iff {x : R} : algebraMap R K x = 0 ↔ x = 0 :=
  IsLocalization.to_map_eq_zero_iff _ le_rfl

variable (R K)
/-
**IsFractionRing.injective** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] (K : Type u_5) [inst_1 : CommRing K] 
[inst_2 : Algebra R K] [IsFractionRing R K],   Function.Injective ⇑(algebraMap R
 K)
参数：R : Type u_1；K : Type u_5；algebraMap R K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
protected theorem injective : Function.Injective (algebraMap R K) :=
  IsLocalization.injective _ (le_of_eq rfl)

include R in
/-
**IsFractionRing.nonZeroDivisors_eq_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `IsFraction
Ring`。
形式化陈述：nonZeroDivisors_eq_isUnit : K⁰ = IsUnit.submonoid K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `mem_nonZeroDivisors_of_injective`：mem_nonZeroDivisors_of_injective [Mono
idWithZeroHomClass F M₀ M₀'] {f : F} (hf : Injective f) (hx : f x in M₀'⁰) : x i
n M₀⁰
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用引理 `IsUnit.mem_nonZeroDivisors`：IsUnit.mem_nonZeroDivisors (hx : IsUnit x) :
 x in M₀⁰
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `isUnit_of_mul_isUnit_left`：isUnit_of_mul_isUnit_left [Monoid M] [IsDedek
indFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isUnit_le_nonZeroDivisors`：isUnit_le_nonZeroDivisors : IsUnit.submonoid 
M₀ <= M₀⁰
-/
theorem nonZeroDivisors_eq_isUnit : K⁰ = IsUnit.submonoid K := by
  refine le_antisymm (fun x hx ↦ ?_) (isUnit_le_nonZeroDivisors K)
  have ⟨r, eq⟩ := surj R⁰ x
  let r' : R⁰ := ⟨r.1, mem_nonZeroDivisors_of_injective (IsFractionRing.injective R K)
    (eq ▸ mul_mem hx (map_units ..).mem_nonZeroDivisors)⟩
  exact isUnit_of_mul_isUnit_left <| eq ▸ map_units K r'

include R in
/-- If `L` is a fraction ring of `K` which is a fraction ring of `R`,
the `K`-algebra homomorphism from `K` to `L` is an isomorphism. -/
/-
**IsFractionRing.algEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsFractionRing`。
形式化陈述：algEquiv (L) [CommRing L] [Algebra K L] [IsFractionRing K L] : K ≃ₐ[K] L
参数：L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L` is a fraction ring of `K` which is a fraction ring of `R`,
the `K`-algebra homomorphism from `K` to `L` is an isomorphism.
-/
noncomputable def algEquiv (L) [CommRing L] [Algebra K L] [IsFractionRing K L] : K ≃ₐ[K] L :=
  atUnits K _ (nonZeroDivisors_eq_isUnit R K).le

include R in
/-
**IsFractionRing.idem** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：idem : IsFractionRing K K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.self`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submo
noid R}, M ≤ IsUnit.submonoid R → IsLocalization M R
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `IsFractionRing.nonZeroDivisors_eq_isUnit`：nonZeroDivisors_eq_isUnit : K⁰
 = IsUnit.submonoid K
-/
theorem idem : IsFractionRing K K := IsLocalization.self (nonZeroDivisors_eq_isUnit R K).le

/-- Taking fraction ring is idempotent: a fraction ring of a fraction ring of `R` is
itself a fraction ring of `R`. -/
/-
**IsFractionRing.trans** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：trans (L) [CommRing L] [Algebra K L] [IsFractionRing K L] [Algebra R L] [I
sScalarTower R K L] : IsFractionRing R L
参数：L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isLocalization_of_algEquiv`：isLocalization_of_algEquiv [A
lgebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) : IsLocalization M P
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Taking fraction ring is idempotent: a fraction ring of a fraction ring of `R` is
itself a fraction ring of `R`.
-/
theorem trans (L) [CommRing L] [Algebra K L] [IsFractionRing K L] [Algebra R L]
    [IsScalarTower R K L] : IsFractionRing R L :=
  isLocalization_of_algEquiv _ <| (algEquiv R K L).restrictScalars R
/-
**IsFractionRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsFractionRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : FaithfulSMul R K :=
  (faithfulSMul_iff_algebraMap_injective R K).mpr <| IsFractionRing.injective R K

variable {R}
/-
**IsFractionRing.self_iff_nonZeroDivisors_eq_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `I
sFractionRing`。
形式化陈述：self_iff_nonZeroDivisors_eq_isUnit : IsFractionRing R R ↔ R⁰ = IsUnit.subm
onoid R where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.nonZeroDivisors_eq_isUnit`：nonZeroDivisors_eq_isUnit : K⁰
 = IsUnit.submonoid K
· 使用定理 `IsLocalization.self`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submo
noid R}, M ≤ IsUnit.submonoid R → IsLocalization M R
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem self_iff_nonZeroDivisors_eq_isUnit : IsFractionRing R R ↔ R⁰ = IsUnit.submonoid R where
  mp _ := nonZeroDivisors_eq_isUnit R R
  mpr h := IsLocalization.self h.le
/-
**IsFractionRing.self_iff_nonZeroDivisors_le_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `I
sFractionRing`。
形式化陈述：self_iff_nonZeroDivisors_le_isUnit : IsFractionRing R R ↔ R⁰ <= IsUnit.sub
monoid R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.self_iff_nonZeroDivisors_eq_isUnit`：self_iff_nonZeroDivis
ors_eq_isUnit : IsFractionRing R R ↔ R⁰ = IsUnit.submonoid R where mp _
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用引理 `isUnit_le_nonZeroDivisors`：isUnit_le_nonZeroDivisors : IsUnit.submonoid 
M₀ <= M₀⁰
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem self_iff_nonZeroDivisors_le_isUnit : IsFractionRing R R ↔ R⁰ ≤ IsUnit.submonoid R := by
  rw [self_iff_nonZeroDivisors_eq_isUnit, le_antisymm_iff,
    and_iff_left (isUnit_le_nonZeroDivisors R)]
/-
**IsFractionRing.self_iff_bijective** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：self_iff_bijective : IsFractionRing R R ↔ Function.Bijective (algebraMap R
 K) where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsFractionRing.self_iff_nonZeroDivisors_le_isUnit`：self_iff_nonZeroDivis
ors_le_isUnit : IsFractionRing R R ↔ R⁰ <= IsUnit.submonoid R
· 使用定理 `IsLocalization.isLocalization_of_algEquiv`：isLocalization_of_algEquiv [A
lgebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) : IsLocalization M P
-/
theorem self_iff_bijective : IsFractionRing R R ↔ Function.Bijective (algebraMap R K) where
  mp h := (atUnits R _ <| self_iff_nonZeroDivisors_le_isUnit.mp h).bijective
  mpr h := isLocalization_of_algEquiv _ (AlgEquiv.ofBijective (Algebra.ofId R K) h).symm
/-
**IsFractionRing.self_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：self_iff_surjective : IsFractionRing R R ↔ Function.Surjective (algebraMap
 R K)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.self_iff_bijective`：self_iff_bijective : IsFractionRing R
 R ↔ Function.Bijective (algebraMap R K) where mp h
· 使用定理 `Function.Bijective.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} (f : α → β), Func
tion.Bijective f = (Function.Injective f ∧ Function.Surjective f)
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem self_iff_surjective : IsFractionRing R R ↔ Function.Surjective (algebraMap R K) := by
  rw [self_iff_bijective K, Function.Bijective, and_iff_right (IsFractionRing.injective R K)]

variable {K}

open algebraMap in
@[norm_cast]
/-
**IsFractionRing.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：coe_inj {a b : R} : (↑a : K) = ↑b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraMap.coe_inj`：coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
-/
theorem coe_inj {a b : R} : (↑a : K) = ↑b ↔ a = b :=
  algebraMap.coe_inj _ _
/-
**IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间
 `IsFractionRing`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_5} [inst_1 : CommRing K] 
[inst_2 : Algebra R K] [IsFractionRing R K]   [Nontrivial R] {x : R}, x ∈ nonZer
oDivisors R → (algebraMap R K) x ≠ 0
参数：algebraMap R K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors`：∀ {R : Type u_1} [
inst : CommSemiring R] {M : Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S
]   [inst_2 : Algebra R S] [IsLocalization…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
protected theorem to_map_ne_zero_of_mem_nonZeroDivisors [Nontrivial R] {x : R}
    (hx : x ∈ nonZeroDivisors R) : algebraMap R K x ≠ 0 :=
  IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ le_rfl hx

variable (A) [IsDomain A]

include A in
/-- A `CommRing` `K` which is the localization of an integral domain `R` at `R - {0}` is an
integral domain. -/
/-
**IsFractionRing.isDomain** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：∀ (A : Type u_4) [inst : CommRing A] {K : Type u_5} [inst_1 : CommRing K] 
[inst_2 : Algebra A K] [IsFractionRing A K]   [IsDomain A], IsDomain K
参数：A : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isDomain_of_le_nonZeroDivisors`：isDomain_of_le_nonZeroDiv
isors (hM : M <= nonZeroDivisors R) : IsDomain S where __ : IsCancelMulZero S
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
A `CommRing` `K` which is the localization of an integral domain `R` at `R - {0}
` is an
integral domain.
-/
protected theorem isDomain : IsDomain K :=
  isDomain_of_le_nonZeroDivisors _ (le_refl (nonZeroDivisors A))

/-- The inverse of an element in the field of fractions of an integral domain. -/
protected noncomputable irreducible_def inv (z : K) : K := open scoped Classical in
  if h : z = 0 then 0
  else
    mk' K ↑(sec (nonZeroDivisors A) z).2
      ⟨(sec _ z).1,
        mem_nonZeroDivisors_iff_ne_zero.2 fun h0 =>
          h <| eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) z) h0⟩

/-
**IsFractionRing.mul_inv_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：∀ (A : Type u_4) [inst : CommRing A] {K : Type u_5} [inst_1 : CommRing K] 
[inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K] [inst_4 : IsDomain A] (x 
: K), x ≠ 0 → x * IsFractionRing.inv A x = 1
参数：A : Type u_4；x : K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.inv_def`：∀ (A : Type u_6) [inst : CommRing A] {K : Type u
_7} [inst_1 : CommRing K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 [inst_4 : I…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsLocalization.eq_zero_of_fst_eq_zero`：eq_zero_of_fst_eq_zero {z x} {y :
 M} (h : z * algebraMap R S y = algebraMap R S x) (hx : x = 0) : z = 0
· 使用定理 `IsLocalization.sec_spec`：sec_spec (z : S) : z * algebraMap R S (IsLocali
zation.sec M z).2 = algebraMap R S (IsLocalization.sec M z).1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `IsLocalization.eq_mk'_iff_mul_eq`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_sec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
-/
protected theorem mul_inv_cancel (x : K) (hx : x ≠ 0) : x * IsFractionRing.inv A x = 1 := by
  rw [IsFractionRing.inv, dif_neg hx, ←
    IsUnit.mul_left_inj
      (map_units K
        ⟨(sec _ x).1,
          mem_nonZeroDivisors_iff_ne_zero.2 fun h0 =>
            hx <| eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) x) h0⟩),
    one_mul, mul_assoc]
  rw [mk'_spec, ← eq_mk'_iff_mul_eq]
  exact (mk'_sec _ x).symm

/-- A `CommRing` `K` which is the localization of an integral domain `R` at `R - {0}` is a field.
See note [reducible non-instances]. -/
@[stacks 09FJ]
/-
**IsFractionRing.toField** 是 Mathlib 中的一个缩写定义，位于命名空间 `IsFractionRing`。
形式化陈述：toField : Field K where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.isDomain`：∀ (A : Type u_4) [inst : CommRing A] {K : Type 
u_5} [inst_1 : CommRing K] [inst_2 : Algebra A K] [IsFractionRing A K]   [IsDoma
in A], IsDoma…
· 使用定理 `IsFractionRing.mul_inv_cancel`：∀ (A : Type u_4) [inst : CommRing A] {K :
 Type u_5} [inst_1 : CommRing K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRi
ng A K] [inst_4 : I…

--- 原说明 ---
A `CommRing` `K` which is the localization of an integral domain `R` at `R - {0}
` is a field.
See note [reducible non-instances].
-/
noncomputable abbrev toField : Field K where
  __ := IsFractionRing.isDomain A
  inv := IsFractionRing.inv A
  mul_inv_cancel := IsFractionRing.mul_inv_cancel A
  inv_zero := show IsFractionRing.inv A (0 : K) = 0 by rw [IsFractionRing.inv]; exact dif_pos rfl
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
/-
**IsFractionRing.surjective_iff_isField** 是 Mathlib 中的一个引理，位于命名空间 `IsFractionRin
g`。
形式化陈述：surjective_iff_isField [IsDomain R] : Function.Surjective (algebraMap R K)
 ↔ IsField R where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.isField`：∀ {A : Type u_1} {B : Type u_2} [inst : Semiring A] [i
nst_1 : Semiring B], IsField B → ∀ (e : A ≃* B), IsField A
· 使用定理 `Field.toIsField`：Field.toIsField (R : Type u) [Field R] : IsField R
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
lemma surjective_iff_isField [IsDomain R] : Function.Surjective (algebraMap R K) ↔ IsField R where
  mp h := (RingEquiv.ofBijective (algebraMap R K)
      ⟨IsFractionRing.injective R K, h⟩).toMulEquiv.isField (IsFractionRing.toField R).toIsField
  mpr h :=
    letI := h.toField
    (IsLocalization.atUnits R _ (S := K)
      (fun _ hx ↦ Ne.isUnit (mem_nonZeroDivisors_iff_ne_zero.mp hx))).surjective

end CommRing

variable {B : Type*} [CommRing B] [IsDomain B] [Field K] {L : Type*} [Field L] [Algebra A K]
  [IsFractionRing A K] {g : A →+* L}

/-
**IsFractionRing.mk'_mk_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：∀ {A : Type u_4} [inst : CommRing A] {K : Type u_5} [inst_1 : Field K] [in
st_2 : Algebra A K]   [inst_3 : IsFractionRing A K] {r s : A} (hs : s ∈ nonZeroD
ivisors A),   IsLocalization.mk' K r ⟨s, hs⟩ = (algebraMap A K) r / (algebraMap 
A K) s
参数：hs : s ∈ nonZeroDivisors A；algebraMap A K；algebraMap A K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.mk'_eq_iff_eq_mul`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors`：∀ {R : Type u_1} [
inst : CommRing R] {K : Type u_5} [inst_1 : CommRing K] [inst_2 : Algebra R K] [
IsFractionRing R K]   [Nontrivial R] {x : …
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem mk'_mk_eq_div {r s} (hs : s ∈ nonZeroDivisors A) :
    mk' K r ⟨s, hs⟩ = algebraMap A K r / algebraMap A K s :=
  haveI := (algebraMap A K).domain_nontrivial
  mk'_eq_iff_eq_mul.2 <|
    (div_mul_cancel₀ (algebraMap A K r)
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)).symm

@[simp]
/-
**IsFractionRing.mk'_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：∀ {A : Type u_4} [inst : CommRing A] {K : Type u_5} [inst_1 : Field K] [in
st_2 : Algebra A K]   [inst_3 : IsFractionRing A K] {r : A} (s : ↥(nonZeroDiviso
rs A)),   IsLocalization.mk' K r s = (algebraMap A K) r / (algebraMap A K) ↑s
参数：s : ↥(nonZeroDivisors A)；algebraMap A K；algebraMap A K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.mk'_mk_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : 
Type u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A
 K] {r s : A} (hs …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mk'_eq_div {r} (s : nonZeroDivisors A) : mk' K r s = algebraMap A K r / algebraMap A K s :=
  mk'_mk_eq_div s.2

variable (A) in
/-
**IsFractionRing.div_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：div_surjective (z : K) : exists x y : A, y in nonZeroDivisors A ∧ algebraM
ap _ _ x / algebraMap _ _ y = z
参数：z : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
-/
theorem div_surjective (z : K) :
    ∃ x y : A, y ∈ nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z :=
  let ⟨x, ⟨y, hy⟩, h⟩ := exists_mk'_eq (nonZeroDivisors A) z
  ⟨x, y, hy, by rwa [mk'_eq_div] at h⟩
/-
**IsFractionRing.isUnit_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRi
ng`。
形式化陈述：isUnit_map_of_injective (hg : Function.Injective g) (y : nonZeroDivisors A
) : IsUnit (g y)
参数：hg : Function.Injective g；y : nonZeroDivisors A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `map_ne_zero_of_mem_nonZeroDivisors`：map_ne_zero_of_mem_nonZeroDivisors [
Nontrivial M₀] [ZeroHomClass F M₀ M₀'] (g : F) (hg : Injective (g : M₀ -> M₀')) 
{x : M₀} (h : x in M₀⁰) …
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem isUnit_map_of_injective (hg : Function.Injective g) (y : nonZeroDivisors A) :
    IsUnit (g y) :=
  haveI := g.domain_nontrivial
  IsUnit.mk0 (g y) <|
    show g.toMonoidWithZeroHom y ≠ 0 from map_ne_zero_of_mem_nonZeroDivisors g hg y.2
/-
**IsFractionRing.mk'_eq_zero_iff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRi
ng`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_5} [inst_1 : Field K] [in
st_2 : Algebra R K]   [inst_3 : IsFractionRing R K] {x : R} {y : ↥(nonZeroDiviso
rs R)}, IsLocalization.mk' K x y = 0 ↔ x = 0
参数：nonZeroDivisors R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk'_eq_zero_iff_eq_zero [Algebra R K] [IsFractionRing R K] {x : R} {y : nonZeroDivisors R} :
    mk' K x y = 0 ↔ x = 0 := by
  have := (algebraMap R K).domain_nontrivial
  simp [nonZeroDivisors.ne_zero]
/-
**IsFractionRing.mk'_eq_one_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：∀ {A : Type u_4} [inst : CommRing A] {K : Type u_5} [inst_1 : Field K] [in
st_2 : Algebra A K]   [inst_3 : IsFractionRing A K] {x : A} {y : ↥(nonZeroDiviso
rs A)}, IsLocalization.mk' K x y = 1 ↔ x = ↑y
参数：nonZeroDivisors A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors`：∀ {R : Type u_1} [
inst : CommRing R] {K : Type u_5} [inst_1 : CommRing K] [inst_2 : Algebra R K] [
IsFractionRing R K]   [Nontrivial R] {x : …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_eq_one_iff_eq`：div_eq_one_iff_eq (hb : b != 0) : a / b = 1 ↔ a = b
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
· 使用定理 `IsLocalization.mk'_self'`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [
inst_3 : IsLoc…
-/
theorem mk'_eq_one_iff_eq {x : A} {y : nonZeroDivisors A} : mk' K x y = 1 ↔ x = y := by
  have := (algebraMap A K).domain_nontrivial
  refine ⟨?_, fun hxy => by rw [hxy, mk'_self']⟩
  intro hxy
  have hy : (algebraMap A K) ↑y ≠ (0 : K) :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.property
  rw [IsFractionRing.mk'_eq_div, div_eq_one_iff_eq hy] at hxy
  exact IsFractionRing.injective A K hxy
/-
**IsFractionRing.of_algHom** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：of_algHom [Algebra A L] (f : L ->ₐ[A] K) : IsFractionRing A L
参数：f : L ->ₐ[A] K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.of_algEquiv`：IsFractionRing.of_algEquiv {R : Type*} [Comm
Semiring R] {K L : Type*} [CommSemiring K] [Algebra R K] [CommSemiring L] [Algeb
ra R L] [h : IsF…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_algHom [Algebra A L] (f : L →ₐ[A] K) : IsFractionRing A L := by
  refine IsFractionRing.of_algEquiv <| .symm <| .ofBijective f ⟨f.injective, fun x ↦ ?_⟩
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective A x
  exact ⟨algebraMap A L x / algebraMap A L y, by simp⟩

section commutes

variable [Algebra A B] {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra A K₁] [Algebra A K₂]
  [IsFractionRing A K₁] {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra B L₁] [Algebra B L₂]
  [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra A L₁] [Algebra A L₂] [IsScalarTower A K₁ L₁]
  [IsScalarTower A K₂ L₂] [IsScalarTower A B L₁] [IsScalarTower A B L₂]

omit [IsDomain B]

/-
**IsFractionRing.algHom_commutes** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：algHom_commutes (e : K₁ ->ₐ[A] K₂) (f : L₁ ->ₐ[B] L₂) (x : K₁) : algebraMa
p K₂ L₂ (e x) = f (algebraMap K₁ L₁ x)
参数：e : K₁ ->ₐ[A] K₂；f : L₁ ->ₐ[B] L₂；x : K₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algHom_commutes (e : K₁ →ₐ[A] K₂) (f : L₁ →ₐ[B] L₂) (x : K₁) :
    algebraMap K₂ L₂ (e x) = f (algebraMap K₁ L₁ x) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective A x
  simp_rw [map_div₀, AlgHom.commutes, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply A B L₁, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
/-
**IsFractionRing.algEquiv_commutes** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：algEquiv_commutes (e : K₁ ≃ₐ[A] K₂) (f : L₁ ≃ₐ[B] L₂) (x : K₁) : algebraMa
p K₂ L₂ (e x) = f (algebraMap K₁ L₁ x)
参数：e : K₁ ≃ₐ[A] K₂；f : L₁ ≃ₐ[B] L₂；x : K₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.algHom_commutes`：algHom_commutes (e : K₁ ->ₐ[A] K₂) (f : 
L₁ ->ₐ[B] L₂) (x : K₁) : algebraMap K₂ L₂ (e x) = f (algebraMap K₁ L₁ x)
-/
theorem algEquiv_commutes (e : K₁ ≃ₐ[A] K₂) (f : L₁ ≃ₐ[B] L₂) (x : K₁) :
    algebraMap K₂ L₂ (e x) = f (algebraMap K₁ L₁ x) := by
  exact algHom_commutes e.toAlgHom f.toAlgHom _

end commutes

section Subfield

variable (A K) in
/-- If `A` is a commutative ring with fraction field `K`, then the subfield of `K` generated by
the image of `algebraMap A K` is equal to the whole field `K`. -/
/-
**IsFractionRing.closure_range_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionR
ing`。
形式化陈述：closure_range_algebraMap : Subfield.closure (Set.range (algebraMap A K)) =
 ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `div_mem`：div_mem {x y : M} (hx : x in H) (hy : y in H) : x / y in H
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `Subfield.subset_closure`：subset_closure {s : Set K} : s subseteq closure
 s

--- 原说明 ---
If `A` is a commutative ring with fraction field `K`, then the subfield of `K` g
enerated by
the image of `algebraMap A K` is equal to the whole field `K`.
-/
theorem closure_range_algebraMap : Subfield.closure (Set.range (algebraMap A K)) = ⊤ :=
  top_unique fun z _ ↦ by
    obtain ⟨_, _, -, rfl⟩ := div_surjective A z
    apply div_mem <;> exact Subfield.subset_closure ⟨_, rfl⟩

variable {L : Type*} [Field L] {g : A →+* L} {f : K →+* L}

/-- If `A` is a commutative ring with fraction field `K`, `L` is a field, `g : A →+* L` lifts to
`f : K →+* L`, then the image of `f` is the subfield generated by the image of `g`. -/
/-
**IsFractionRing.ringHom_fieldRange_eq_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsF
ractionRing`。
形式化陈述：ringHom_fieldRange_eq_of_comp_eq (h : RingHom.comp f (algebraMap A K) = g)
 : f.fieldRange = Subfield.closure g.range
参数：h : RingHom.comp f (algebraMap A K) = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.fieldRange_eq_map`：fieldRange_eq_map : f.fieldRange = Subfield.m
ap f ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsFractionRing.closure_range_algebraMap`：closure_range_algebraMap : Subf
ield.closure (Set.range (algebraMap A K)) = ⊤
· 使用定理 `RingHom.map_field_closure`：map_field_closure (f : K ->+* L) (s : Set K) 
: (closure s).map f = closure (f '' s)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `RingHom.coe_comp`：coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp
 hmn : α -> γ) = hnp ∘ hmn
· 使用定理 `RingHom.coe_range`：coe_range : (f.range : Set S) = Set.range f

--- 原说明 ---
If `A` is a commutative ring with fraction field `K`, `L` is a field, `g : A →+*
 L` lifts to
`f : K →+* L`, then the image of `f` is the subfield generated by the image of `
g`.
-/
theorem ringHom_fieldRange_eq_of_comp_eq (h : RingHom.comp f (algebraMap A K) = g) :
    f.fieldRange = Subfield.closure g.range := by
  rw [f.fieldRange_eq_map, ← closure_range_algebraMap A K,
    f.map_field_closure, ← Set.range_comp, ← f.coe_comp, h, g.coe_range]

/-- If `A` is a commutative ring with fraction field `K`, `L` is a field, `g : A →+* L` lifts to
`f : K →+* L`, `s` is a set such that the image of `g` is the subring generated by `s`,
then the image of `f` is the subfield generated by `s`. -/
/-
**IsFractionRing.ringHom_fieldRange_eq_of_comp_eq_of_range_eq** 是 Mathlib 中的一个定理
，位于命名空间 `IsFractionRing`。
形式化陈述：ringHom_fieldRange_eq_of_comp_eq_of_range_eq (h : RingHom.comp f (algebraM
ap A K) = g) {s : Set L} (hs : g.range = Subring.closure s) : f.fieldRange = Sub
field.closure s
参数：h : RingHom.comp f (algebraMap A K) = g；hs : g.range = Subring.closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.ringHom_fieldRange_eq_of_comp_eq`：ringHom_fieldRange_eq_o
f_comp_eq (h : RingHom.comp f (algebraMap A K) = g) : f.fieldRange = Subfield.cl
osure g.range
· 使用定理 `Subfield.ext`：ext {S T : Subfield K} (h : forall x, x in S ↔ x in T) : S
 = T
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subring.closure_eq`：closure_eq (s : Subring R) : closure (s : Set R) = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `A` is a commutative ring with fraction field `K`, `L` is a field, `g : A →+*
 L` lifts to
`f : K →+* L`, `s` is a set such that the image of `g` is the subring generated 
by `s`,
then the image of `f` is the subfield generated by `s`.
-/
theorem ringHom_fieldRange_eq_of_comp_eq_of_range_eq (h : RingHom.comp f (algebraMap A K) = g)
    {s : Set L} (hs : g.range = Subring.closure s) : f.fieldRange = Subfield.closure s := by
  rw [ringHom_fieldRange_eq_of_comp_eq h, hs]
  ext
  simp_rw [Subfield.mem_closure_iff, Subring.closure_eq]

end Subfield

open Function

/-- Given a commutative ring `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field, we get a
field hom sending `z : K` to `g x * (g y)⁻¹`, where `(x, y) : A × (NonZeroDivisors A)` are
such that `z = f x * (f y)⁻¹`. -/
/-
**IsFractionRing.lift** 是 Mathlib 中的一个定义，位于命名空间 `IsFractionRing`。
形式化陈述：lift (hg : Injective g) : K ->+* L
参数：hg : Injective g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.isUnit_map_of_injective`：isUnit_map_of_injective (hg : Fu
nction.Injective g) (y : nonZeroDivisors A) : IsUnit (g y)

--- 原说明 ---
Given a commutative ring `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field, we get a
field hom sending `z : K` to `g x * (g y)⁻¹`, where `(x, y) : A × (NonZeroDiviso
rs A)` are
such that `z = f x * (f y)⁻¹`.
-/
noncomputable def lift (hg : Injective g) : K →+* L :=
  IsLocalization.lift fun y : nonZeroDivisors A => isUnit_map_of_injective hg y
/-
**IsFractionRing.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：lift_unique (hg : Function.Injective g) {f : K ->+* L} (hf1 : forall x, f 
(algebraMap A K x) = g x) : IsFractionRing.lift hg = f
参数：hg : Function.Injective g；hf1 : forall x, f (algebraMap A K x) = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.lift_unique`：lift_unique {j : S ->+* P} (hj : forall x, j
 ((algebraMap R S) x) = g x) : lift hg = j
· 使用定理 `IsFractionRing.isUnit_map_of_injective`：isUnit_map_of_injective (hg : Fu
nction.Injective g) (y : nonZeroDivisors A) : IsUnit (g y)
-/
theorem lift_unique (hg : Function.Injective g) {f : K →+* L}
    (hf1 : ∀ x, f (algebraMap A K x) = g x) : IsFractionRing.lift hg = f :=
  IsLocalization.lift_unique _ hf1

/-- Another version of unique to give two lift maps should be equal -/
/-
**IsFractionRing.ringHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：ringHom_ext {f1 f2 : K ->+* L} (hf : forall x : A, f1 (algebraMap A K x) =
 f2 (algebraMap A K x)) : f1 = f2
参数：hf : forall x : A, f1 (algebraMap A K x) = f2 (algebraMap A K x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
Another version of unique to give two lift maps should be equal
-/
theorem ringHom_ext {f1 f2 : K →+* L}
    (hf : ∀ x : A, f1 (algebraMap A K x) = f2 (algebraMap A K x)) : f1 = f2 := by
  ext z
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective A z
  rw [map_div₀, map_div₀, hf, hf]
/-
**IsFractionRing.injective_comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsFraction
Ring`。
形式化陈述：injective_comp_algebraMap : Function.Injective fun (f : K ->+* L) => f.com
p (algebraMap A K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.ringHom_ext`：ringHom_ext {f1 f2 : K ->+* L} (hf : forall 
x : A, f1 (algebraMap A K x) = f2 (algebraMap A K x)) : f1 = f2
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
-/
theorem injective_comp_algebraMap :
    Function.Injective fun (f : K →+* L) => f.comp (algebraMap A K) :=
  fun _ _ h => ringHom_ext (fun x => RingHom.congr_fun h x)

section liftAlgHom

variable [Algebra R A] [Algebra R K] [IsScalarTower R A K] [Algebra R L]
  {g : A →ₐ[R] L} (hg : Injective g) (x : K)
include hg

/-- `AlgHom` version of `IsFractionRing.lift`. -/
/-
**IsFractionRing.liftAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `IsFractionRing`。
形式化陈述：liftAlgHom : K ->ₐ[R] L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgHom` version of `IsFractionRing.lift`.
-/
noncomputable def liftAlgHom : K →ₐ[R] L :=
  IsLocalization.liftAlgHom fun y : nonZeroDivisors A => isUnit_map_of_injective hg y
/-
**IsFractionRing.liftAlgHom_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`
。
形式化陈述：liftAlgHom_toRingHom : (liftAlgHom hg : K ->ₐ[R] L).toRingHom = lift hg
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAlgHom_toRingHom : (liftAlgHom hg : K →ₐ[R] L).toRingHom = lift hg := rfl

@[simp]
/-
**IsFractionRing.coe_liftAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：coe_liftAlgHom : ⇑(liftAlgHom hg : K ->ₐ[R] L) = lift hg
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_liftAlgHom : ⇑(liftAlgHom hg : K →ₐ[R] L) = lift hg := rfl
/-
**IsFractionRing.liftAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：liftAlgHom_apply : liftAlgHom hg x = lift hg x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAlgHom_apply : liftAlgHom hg x = lift hg x := rfl

end liftAlgHom

/-- Given a commutative ring `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
the field hom induced from `K` to `L` maps `x` to `g x` for all
`x : A`. -/
@[simp]
/-
**IsFractionRing.lift_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：lift_algebraMap (hg : Injective g) (x) : lift hg (algebraMap A K x) = g x
参数：hg : Injective g；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.lift_eq`：lift_eq (x : R) : lift hg ((algebraMap R S) x) =
 g x
· 使用定理 `IsFractionRing.isUnit_map_of_injective`：isUnit_map_of_injective (hg : Fu
nction.Injective g) (y : nonZeroDivisors A) : IsUnit (g y)

--- 原说明 ---
Given a commutative ring `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
the field hom induced from `K` to `L` maps `x` to `g x` for all
`x : A`.
-/
theorem lift_algebraMap (hg : Injective g) (x) : lift hg (algebraMap A K x) = g x :=
  lift_eq _ _

/-- The image of `IsFractionRing.lift` is the subfield generated by the image
of the ring hom. -/
/-
**IsFractionRing.lift_fieldRange** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：lift_fieldRange (hg : Injective g) : (lift hg : K ->+* L).fieldRange = Sub
field.closure g.range
参数：hg : Injective g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.ringHom_fieldRange_eq_of_comp_eq`：ringHom_fieldRange_eq_o
f_comp_eq (h : RingHom.comp f (algebraMap A K) = g) : f.fieldRange = Subfield.cl
osure g.range
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.lift_algebraMap`：lift_algebraMap (hg : Injective g) (x) :
 lift hg (algebraMap A K x) = g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The image of `IsFractionRing.lift` is the subfield generated by the image
of the ring hom.
-/
theorem lift_fieldRange (hg : Injective g) :
    (lift hg : K →+* L).fieldRange = Subfield.closure g.range :=
  ringHom_fieldRange_eq_of_comp_eq (by ext; simp)

/-- The image of `IsFractionRing.lift` is the subfield generated by `s`, if the image
of the ring hom is the subring generated by `s`. -/
/-
**IsFractionRing.lift_fieldRange_eq_of_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsFra
ctionRing`。
形式化陈述：lift_fieldRange_eq_of_range_eq (hg : Injective g) {s : Set L} (hs : g.rang
e = Subring.closure s) : (lift hg : K ->+* L).fieldRange = Subfield.closure s
参数：hg : Injective g；hs : g.range = Subring.closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.ringHom_fieldRange_eq_of_comp_eq_of_range_eq`：ringHom_fie
ldRange_eq_of_comp_eq_of_range_eq (h : RingHom.comp f (algebraMap A K) = g) {s :
 Set L} (hs : g.range = Subring.closure s) : f.fi…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.lift_algebraMap`：lift_algebraMap (hg : Injective g) (x) :
 lift hg (algebraMap A K x) = g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The image of `IsFractionRing.lift` is the subfield generated by `s`, if the imag
e
of the ring hom is the subring generated by `s`.
-/
theorem lift_fieldRange_eq_of_range_eq (hg : Injective g)
    {s : Set L} (hs : g.range = Subring.closure s) :
    (lift hg : K →+* L).fieldRange = Subfield.closure s :=
  ringHom_fieldRange_eq_of_comp_eq_of_range_eq (by ext; simp) hs

/-- Given a commutative ring `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
field hom induced from `K` to `L` maps `f x / f y` to `g x / g y` for all
`x : A, y ∈ NonZeroDivisors A`. -/
/-
**IsFractionRing.lift_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：lift_mk' (hg : Injective g) (x) (y : nonZeroDivisors A) : lift hg (mk' K x
 y) = g x / g y
参数：hg : Injective g；x；y : nonZeroDivisors A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsFractionRing.lift_algebraMap`：lift_algebraMap (hg : Injective g) (x) :
 lift hg (algebraMap A K x) = g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given a commutative ring `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
field hom induced from `K` to `L` maps `f x / f y` to `g x / g y` for all
`x : A, y ∈ NonZeroDivisors A`.
-/
theorem lift_mk' (hg : Injective g) (x) (y : nonZeroDivisors A) :
    lift hg (mk' K x y) = g x / g y := by simp only [mk'_eq_div, map_div₀, lift_algebraMap]

/-- Given commutative rings `A, B` where `B` is an integral domain, with fraction rings `K`, `L`
and an injective ring hom `j : A →+* B`, we get a ring hom
sending `z : K` to `g (j x) * (g (j y))⁻¹`, where `(x, y) : A × (NonZeroDivisors A)` are
such that `z = f x * (f y)⁻¹`. -/
/-
**IsFractionRing.map** 是 Mathlib 中的一个定义，位于命名空间 `IsFractionRing`。
形式化陈述：map {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B] [CommRing K] 
[Algebra A K] [IsFractionRing A K] [CommRing L] [Algebra B L] [IsFractionRing B 
L] {j : A ->+* B} (hj : Injective j) : K ->+* L
参数：hj : Injective j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given commutative rings `A, B` where `B` is an integral domain, with fraction ri
ngs `K`, `L`
and an injective ring hom `j : A →+* B`, we get a ring hom
sending `z : K` to `g (j x) * (g (j y))⁻¹`, where `(x, y) : A × (NonZeroDivisors
 A)` are
such that `z = f x * (f y)⁻¹`.
-/
noncomputable def map {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B] [CommRing K]
    [Algebra A K] [IsFractionRing A K] [CommRing L] [Algebra B L] [IsFractionRing B L] {j : A →+* B}
    (hj : Injective j) : K →+* L :=
  IsLocalization.map L j
    (show nonZeroDivisors A ≤ (nonZeroDivisors B).comap j from
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j hj)

section ringEquivOfRingEquiv

variable {A K B L : Type*} [CommRing A] [CommRing B] [CommRing K] [CommRing L]
  [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
  (h : A ≃+* B)

/-- Given rings `A, B` and localization maps to their fraction rings
`f : A →+* K, g : B →+* L`, an isomorphism `h : A ≃+* B` induces an isomorphism of
fraction rings `K ≃+* L`. -/
@[simps! apply]
/-
**IsFractionRing.ringEquivOfRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsFractionRing`
。
形式化陈述：ringEquivOfRingEquiv : K ≃+* L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given rings `A, B` and localization maps to their fraction rings
`f : A →+* K, g : B →+* L`, an isomorphism `h : A ≃+* B` induces an isomorphism 
of
fraction rings `K ≃+* L`.
-/
noncomputable def ringEquivOfRingEquiv : K ≃+* L :=
  IsLocalization.ringEquivOfRingEquiv K L h (MulEquivClass.map_nonZeroDivisors h)

set_option backward.isDefEq.respectTransparency false in
/-
**IsFractionRing.ringEquivOfRingEquiv_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `IsFr
actionRing`。
形式化陈述：ringEquivOfRingEquiv_algebraMap (a : A) : ringEquivOfRingEquiv h (algebraM
ap A K a) = algebraMap B L (h a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.ringEquivOfRingEquiv_apply`：∀ {A : Type u_8} {K : Type u_
9} {B : Type u_10} {L : Type u_11} [inst : CommRing A] [inst_1 : CommRing B]   [
inst_2 : CommRing K] [inst_3 : …
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ringEquivOfRingEquiv_algebraMap
    (a : A) : ringEquivOfRingEquiv h (algebraMap A K a) = algebraMap B L (h a) := by
  simp

@[simp]
/-
**IsFractionRing.ringEquivOfRingEquiv_refl** 是 Mathlib 中的一个引理，位于命名空间 `IsFraction
Ring`。
形式化陈述：ringEquivOfRingEquiv_refl : ringEquivOfRingEquiv (.refl A) = .refl K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.ringEquivOfRingEquiv_apply`：∀ {A : Type u_8} {K : Type u_
9} {B : Type u_10} {L : Type u_11} [inst : CommRing A] [inst_1 : CommRing B]   [
inst_2 : CommRing K] [inst_3 : …
· 使用定理 `IsLocalization.map_id`：map_id (z : S) (h : M <= M.comap (RingHom.id R)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ringEquivOfRingEquiv_refl :
    ringEquivOfRingEquiv (.refl A) = .refl K := by ext; simp

@[simp]
/-
**IsFractionRing.ringEquivOfRingEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `IsFraction
Ring`。
形式化陈述：ringEquivOfRingEquiv_symm : (ringEquivOfRingEquiv h : K ≃+* L).symm = ring
EquivOfRingEquiv h.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ringEquivOfRingEquiv_symm :
    (ringEquivOfRingEquiv h : K ≃+* L).symm = ringEquivOfRingEquiv h.symm := rfl

variable (K L) in
/-
**IsFractionRing.ringEquivOfRingEquiv_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsFraction
Ring`。
形式化陈述：ringEquivOfRingEquiv_comp {C : Type*} (M : Type*) [CommRing C] [CommRing M
] [Algebra C M] [IsFractionRing C M] (f : A ≃+* B) (g : B ≃+* C) : (ringEquivOfR
ingEquiv (f.trans g)) = (ringEquivOfRingEquiv (K
参数：M : Type*；f : A ≃+* B；g : B ≃+* C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.ringEquivOfRingEquiv_apply`：∀ {A : Type u_8} {K : Type u_
9} {B : Type u_10} {L : Type u_11} [inst : CommRing A] [inst_1 : CommRing B]   [
inst_2 : CommRing K] [inst_3 : …
· 使用定理 `IsLocalization.map_map`：map_map {A : Type*} [CommSemiring A] {U : Submon
oid A} {W} [CommSemiring W] [Algebra A W] [IsLocalization U W] {l : P ->+* A} (h
l : T <= U.c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ringEquivOfRingEquiv_comp {C : Type*} (M : Type*) [CommRing C]
  [CommRing M] [Algebra C M] [IsFractionRing C M] (f : A ≃+* B) (g : B ≃+* C) :
  (ringEquivOfRingEquiv (f.trans g)) =
    (ringEquivOfRingEquiv (K := K) f).trans (ringEquivOfRingEquiv (K := L) (L := M) g) := by
  ext a
  simp [IsLocalization.map_map]

variable (A K)

/-- A ring automorphism of a ring induces an ring automorphism of its fraction field.

This is a bundled version of `ringEquivOfRingEquiv`. -/
/-
**IsFractionRing.ringEquivOfRingEquivHom** 是 Mathlib 中的一个定义，位于命名空间 `IsFractionRi
ng`。
形式化陈述：ringEquivOfRingEquivHom : (A ≃+* A) ->* (K ≃+* K) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsFractionRing.ringEquivOfRingEquiv_refl`：ringEquivOfRingEquiv_refl : ri
ngEquivOfRingEquiv (.refl A) = .refl K
· 使用定理 `IsFractionRing.ringEquivOfRingEquiv_comp`：ringEquivOfRingEquiv_comp {C :
 Type*} (M : Type*) [CommRing C] [CommRing M] [Algebra C M] [IsFractionRing C M]
 (f : A ≃+* B) (g : B ≃+* C) :…

--- 原说明 ---
A ring automorphism of a ring induces an ring automorphism of its fraction field
.

This is a bundled version of `ringEquivOfRingEquiv`.
-/
noncomputable def ringEquivOfRingEquivHom : (A ≃+* A) →* (K ≃+* K) where
  toFun := ringEquivOfRingEquiv
  map_one' := ringEquivOfRingEquiv_refl
  map_mul' f g := ringEquivOfRingEquiv_comp K K K g f

@[simp]
/-
**IsFractionRing.ringEquivOfRingEquivHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsFrac
tionRing`。
形式化陈述：ringEquivOfRingEquivHom_apply (f : A ≃+* A) : ringEquivOfRingEquivHom A K 
f = ringEquivOfRingEquiv f
参数：f : A ≃+* A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ringEquivOfRingEquivHom_apply (f : A ≃+* A) :
    ringEquivOfRingEquivHom A K f = ringEquivOfRingEquiv f :=
  rfl
/-
**IsFractionRing.ringEquivOfRingEquivHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `Is
FractionRing`。
形式化陈述：ringEquivOfRingEquivHom_injective : Function.Injective (ringEquivOfRingEqu
ivHom A K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.ringEquivOfRingEquiv_apply`：∀ {A : Type u_8} {K : Type u_
9} {B : Type u_10} {L : Type u_11} [inst : CommRing A] [inst_1 : CommRing B]   [
inst_2 : CommRing K] [inst_3 : …
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingEquiv.ext_iff`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [inst_
1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] {f g : R ≃+* S},   f = g ↔ ∀ (x : R
), f x …
-/
lemma ringEquivOfRingEquivHom_injective : Function.Injective (ringEquivOfRingEquivHom A K) := by
  intro f g h
  ext b
  simpa using RingEquiv.ext_iff.mp h (algebraMap A K b)

end ringEquivOfRingEquiv

section semilinearEquivOfRingEquiv

variable {A B : Type*} (K L : Type*) [CommRing A] [CommRing B] [CommRing K] [CommRing L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] (f : A ≃+* B)

local instance : RingHomInvPair (f : A →+* B) f.symm :=
  RingHomInvPair.of_ringEquiv f

/-- Given rings `A, B` and localization maps to their fraction rings
`f : A →+* K, g : B →+* L`, an isomorphism `h : A ≃+* B` induces a semilinear equivalence
fraction rings `K ≃ₛₗ[f.toRingHom] L`. -/
/-
**IsFractionRing.semilinearEquivOfRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsFractio
nRing`。
形式化陈述：semilinearEquivOfRingEquiv : K ≃ₛₗ[(f : A ->+* B)] L
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.instRingHomInvPairToRingHomRingEquivSymm`：∀ {A : Type u_8
} {B : Type u_9} [inst : CommRing A] [inst_1 : CommRing B] (f : A ≃+* B), RingHo
mInvPair ↑f ↑f.symm

--- 原说明 ---
Given rings `A, B` and localization maps to their fraction rings
`f : A →+* K, g : B →+* L`, an isomorphism `h : A ≃+* B` induces a semilinear eq
uivalence
fraction rings `K ≃ₛₗ[f.toRingHom] L`.
-/
noncomputable def semilinearEquivOfRingEquiv : K ≃ₛₗ[(f : A →+* B)] L :=
{ ringEquivOfRingEquiv f with
  map_smul' r x := by simp [Algebra.smul_def] }

set_option backward.isDefEq.respectTransparency.types false in
/-
**IsFractionRing.semilinearEquivOfRingEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsF
ractionRing`。
形式化陈述：semilinearEquivOfRingEquiv_apply (x : K) : (semilinearEquivOfRingEquiv K L
 f) x = (ringEquivOfRingEquiv f) x
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsFractionRing.instRingHomInvPairToRingHomRingEquivSymm`：∀ {A : Type u_8
} {B : Type u_9} [inst : CommRing A] [inst_1 : CommRing B] (f : A ≃+* B), RingHo
mInvPair ↑f ↑f.symm
-/
lemma semilinearEquivOfRingEquiv_apply (x : K) :
    (semilinearEquivOfRingEquiv K L f) x = (ringEquivOfRingEquiv f) x := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**IsFractionRing.semilinearEquivOfRingEquiv_algebraMap** 是 Mathlib 中的一个引理，位于命名空间
 `IsFractionRing`。
形式化陈述：semilinearEquivOfRingEquiv_algebraMap (a : A) : semilinearEquivOfRingEquiv
 K L f (algebraMap A K a) = algebraMap B L (f a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsFractionRing.instRingHomInvPairToRingHomRingEquivSymm`：∀ {A : Type u_8
} {B : Type u_9} [inst : CommRing A] [inst_1 : CommRing B] (f : A ≃+* B), RingHo
mInvPair ↑f ↑f.symm
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.ringEquivOfRingEquiv_apply`：∀ {R : Type u_1} [inst : Comm
Semiring R] {M : Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2
 : Algebra R S] {P : Type u_3} …
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma semilinearEquivOfRingEquiv_algebraMap (a : A) :
    semilinearEquivOfRingEquiv K L f (algebraMap A K a) = algebraMap B L (f a) := by
  simp [semilinearEquivOfRingEquiv, ringEquivOfRingEquiv]

set_option backward.isDefEq.respectTransparency.types false in
/-
**IsFractionRing.semilinearEquivOfRingEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间
 `IsFractionRing`。
形式化陈述：semilinearEquivOfRingEquiv_symm_apply (x : L) : (semilinearEquivOfRingEqui
v K L f).symm x = (ringEquivOfRingEquiv f).symm x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsFractionRing.instRingHomInvPairToRingHomRingEquivSymm`：∀ {A : Type u_8
} {B : Type u_9} [inst : CommRing A] [inst_1 : CommRing B] (f : A ≃+* B), RingHo
mInvPair ↑f ↑f.symm
-/
lemma semilinearEquivOfRingEquiv_symm_apply (x : L) :
    (semilinearEquivOfRingEquiv K L f).symm x = (ringEquivOfRingEquiv f).symm x := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**IsFractionRing.semilinearEquivOfRingEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `IsFr
actionRing`。
形式化陈述：semilinearEquivOfRingEquiv_comp {C : Type*} (M : Type*) [CommRing C] [Comm
Ring M] [Algebra C M] [IsFractionRing C M] (g : B ≃+* C) : let : RingHomCompTrip
le f (g : B ->+* C) (f.trans g : A ->+* C)
参数：M : Type*；g : B ≃+* C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsFractionRing.instRingHomInvPairToRingHomRingEquivSymm`：∀ {A : Type u_8
} {B : Type u_9} [inst : CommRing A] [inst_1 : CommRing B] (f : A ≃+* B), RingHo
mInvPair ↑f ↑f.symm
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsFractionRing.semilinearEquivOfRingEquiv_apply`：semilinearEquivOfRingEq
uiv_apply (x : K) : (semilinearEquivOfRingEquiv K L f) x = (ringEquivOfRingEquiv
 f) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsFractionRing.ringEquivOfRingEquiv_comp`：ringEquivOfRingEquiv_comp {C :
 Type*} (M : Type*) [CommRing C] [CommRing M] [Algebra C M] [IsFractionRing C M]
 (f : A ≃+* B) (g : B ≃+* C) :…
· 使用定理 `IsFractionRing.ringEquivOfRingEquiv_apply`：∀ {A : Type u_8} {K : Type u_
9} {B : Type u_10} {L : Type u_11} [inst : CommRing A] [inst_1 : CommRing B]   [
inst_2 : CommRing K] [inst_3 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma semilinearEquivOfRingEquiv_comp {C : Type*} (M : Type*) [CommRing C] [CommRing M]
    [Algebra C M] [IsFractionRing C M] (g : B ≃+* C) :
    let : RingHomCompTriple f (g : B →+* C) (f.trans g : A →+* C) := ⟨rfl⟩
    let : RingHomCompTriple g.symm (f.symm : B →+* A) ((f.trans g).symm : C →+* A) := ⟨rfl⟩
    (semilinearEquivOfRingEquiv K M (f.trans g)) =
      LinearEquiv.trans (σ₁₃ := (f.trans g)) (σ₃₁ := (f.trans g).symm)
      (semilinearEquivOfRingEquiv K L f)
      (semilinearEquivOfRingEquiv L M g) := by
  ext a
  simp [-RingEquiv.coe_ringHom_trans, semilinearEquivOfRingEquiv_apply,
    semilinearEquivOfRingEquiv_apply K M, ringEquivOfRingEquiv_comp K L M]

end semilinearEquivOfRingEquiv

section algEquivOfAlgEquiv

variable {R A K B L : Type*} [CommSemiring R] [CommRing A] [CommRing B] [CommRing K] [CommRing L]
  [Algebra R A] [Algebra R K] [Algebra A K] [IsFractionRing A K] [IsScalarTower R A K]
  [Algebra R B] [Algebra R L] [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (h : A ≃ₐ[R] B)

/-- Given `R`-algebras `A, B` and localization maps to their fraction rings
`f : A →ₐ[R] K, g : B →ₐ[R] L`, an isomorphism `h : A ≃ₐ[R] B` induces an isomorphism of
fraction rings `K ≃ₐ[R] L`. -/
/-
**IsFractionRing.algEquivOfAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsFractionRing`。
形式化陈述：algEquivOfAlgEquiv : K ≃ₐ[R] L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `R`-algebras `A, B` and localization maps to their fraction rings
`f : A →ₐ[R] K, g : B →ₐ[R] L`, an isomorphism `h : A ≃ₐ[R] B` induces an isomor
phism of
fraction rings `K ≃ₐ[R] L`.
-/
noncomputable def algEquivOfAlgEquiv : K ≃ₐ[R] L :=
  IsLocalization.algEquivOfAlgEquiv K L h (MulEquivClass.map_nonZeroDivisors h)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**IsFractionRing.algEquivOfAlgEquiv_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `IsFrac
tionRing`。
形式化陈述：algEquivOfAlgEquiv_algebraMap (a : A) : algEquivOfAlgEquiv h (algebraMap A
 K a) = algebraMap B L (h a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `IsLocalization.algEquivOfAlgEquiv_apply`：∀ {A : Type u_4} [inst : CommSe
miring A] {R : Type u_5} [inst_1 : CommSemiring R] [inst_2 : Algebra A R]   {M :
 Submonoid R} (S : Type u_6) …
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma algEquivOfAlgEquiv_algebraMap
    (a : A) : algEquivOfAlgEquiv h (algebraMap A K a) = algebraMap B L (h a) := by
  simp [algEquivOfAlgEquiv]

@[simp]
/-
**IsFractionRing.algEquivOfAlgEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `IsFractionRi
ng`。
形式化陈述：algEquivOfAlgEquiv_symm : (algEquivOfAlgEquiv h : K ≃ₐ[R] L).symm = algEqu
ivOfAlgEquiv h.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma algEquivOfAlgEquiv_symm :
    (algEquivOfAlgEquiv h : K ≃ₐ[R] L).symm = algEquivOfAlgEquiv h.symm := rfl

end algEquivOfAlgEquiv

section fieldEquivOfAlgEquiv

variable {A B C D : Type*}
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D]
  (FA FB FC FD : Type*) [Field FA] [Field FB] [Field FC] [Field FD]
  [Algebra A FA] [Algebra B FB] [Algebra C FC] [Algebra D FD]
  [IsFractionRing A FA] [IsFractionRing B FB] [IsFractionRing C FC] [IsFractionRing D FD]
  [Algebra A FB] [IsScalarTower A B FB]
  [Algebra A FC] [IsScalarTower A C FC]
  [Algebra A FD] [IsScalarTower A D FD]
  [Algebra FA FB] [IsScalarTower A FA FB]
  [Algebra FA FC] [IsScalarTower A FA FC]
  [Algebra FA FD] [IsScalarTower A FA FD]

/-- An algebra isomorphism of rings induces an algebra isomorphism of fraction fields. -/
/-
**IsFractionRing.fieldEquivOfAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsFractionRing`
。
形式化陈述：fieldEquivOfAlgEquiv (f : B ≃ₐ[A] C) : FB ≃ₐ[FA] FC where __
参数：f : B ≃ₐ[A] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra isomorphism of rings induces an algebra isomorphism of fraction field
s.
-/
noncomputable def fieldEquivOfAlgEquiv (f : B ≃ₐ[A] C) : FB ≃ₐ[FA] FC where
  __ := IsFractionRing.ringEquivOfRingEquiv f.toRingEquiv
  commutes' x := by
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective A x
    simp_rw [map_div₀, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B FB]
    simp [← IsScalarTower.algebraMap_apply A C FC]
/-
**IsFractionRing.restrictScalars_fieldEquivOfAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 
`IsFractionRing`。
形式化陈述：restrictScalars_fieldEquivOfAlgEquiv (f : B ≃ₐ[A] C) : (fieldEquivOfAlgEqu
iv FA FB FC f).restrictScalars A = algEquivOfAlgEquiv f
参数：f : B ≃ₐ[A] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
-/
lemma restrictScalars_fieldEquivOfAlgEquiv (f : B ≃ₐ[A] C) :
    (fieldEquivOfAlgEquiv FA FB FC f).restrictScalars A = algEquivOfAlgEquiv f := by
  ext; rfl

/-- This says that `fieldEquivOfAlgEquiv f` is an extension of `f` (i.e., it agrees with `f` on
`B`). Whereas `(fieldEquivOfAlgEquiv f).commutes` says that `fieldEquivOfAlgEquiv f` fixes `K`. -/
@[simp]
/-
**IsFractionRing.fieldEquivOfAlgEquiv_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `IsFr
actionRing`。
形式化陈述：fieldEquivOfAlgEquiv_algebraMap (f : B ≃ₐ[A] C) (b : B) : fieldEquivOfAlgE
quiv FA FB FC f (algebraMap B FB b) = algebraMap C FC (f b)
参数：f : B ≃ₐ[A] C；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsFractionRing.ringEquivOfRingEquiv_algebraMap`：ringEquivOfRingEquiv_alg
ebraMap (a : A) : ringEquivOfRingEquiv h (algebraMap A K a) = algebraMap B L (h 
a)

--- 原说明 ---
This says that `fieldEquivOfAlgEquiv f` is an extension of `f` (i.e., it agrees 
with `f` on
`B`). Whereas `(fieldEquivOfAlgEquiv f).commutes` says that `fieldEquivOfAlgEqui
v f` fixes `K`.
-/
lemma fieldEquivOfAlgEquiv_algebraMap (f : B ≃ₐ[A] C) (b : B) :
    fieldEquivOfAlgEquiv FA FB FC f (algebraMap B FB b) = algebraMap C FC (f b) :=
  ringEquivOfRingEquiv_algebraMap f.toRingEquiv b

variable (A B) in
@[simp]
/-
**IsFractionRing.fieldEquivOfAlgEquiv_refl** 是 Mathlib 中的一个引理，位于命名空间 `IsFraction
Ring`。
形式化陈述：fieldEquivOfAlgEquiv_refl : fieldEquivOfAlgEquiv FA FB FB (AlgEquiv.refl :
 B ≃ₐ[A] B) = AlgEquiv.refl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用引理 `IsFractionRing.fieldEquivOfAlgEquiv_algebraMap`：fieldEquivOfAlgEquiv_alg
ebraMap (f : B ≃ₐ[A] C) (b : B) : fieldEquivOfAlgEquiv FA FB FC f (algebraMap B 
FB b) = algebraMap C FC (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fieldEquivOfAlgEquiv_refl :
    fieldEquivOfAlgEquiv FA FB FB (AlgEquiv.refl : B ≃ₐ[A] B) = AlgEquiv.refl := by
  ext x
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective B x
  simp
/-
**IsFractionRing.fieldEquivOfAlgEquiv_trans** 是 Mathlib 中的一个引理，位于命名空间 `IsFractio
nRing`。
形式化陈述：fieldEquivOfAlgEquiv_trans (f : B ≃ₐ[A] C) (g : C ≃ₐ[A] D) : fieldEquivOfA
lgEquiv FA FB FD (f.trans g) = (fieldEquivOfAlgEquiv FA FB FC f).trans (fieldEqu
ivOfAlgEquiv FA FC FD g)
参数：f : B ≃ₐ[A] C；g : C ≃ₐ[A] D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用引理 `IsFractionRing.fieldEquivOfAlgEquiv_algebraMap`：fieldEquivOfAlgEquiv_alg
ebraMap (f : B ≃ₐ[A] C) (b : B) : fieldEquivOfAlgEquiv FA FB FC f (algebraMap B 
FB b) = algebraMap C FC (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fieldEquivOfAlgEquiv_trans (f : B ≃ₐ[A] C) (g : C ≃ₐ[A] D) :
    fieldEquivOfAlgEquiv FA FB FD (f.trans g) =
      (fieldEquivOfAlgEquiv FA FB FC f).trans (fieldEquivOfAlgEquiv FA FC FD g) := by
  ext x
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective B x
  simp

end fieldEquivOfAlgEquiv

section fieldEquivOfAlgEquivHom

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (K L : Type*) [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower A K L]

/-- An algebra automorphism of a ring induces an algebra automorphism of its fraction field.

This is a bundled version of `fieldEquivOfAlgEquiv`. -/
/-
**IsFractionRing.fieldEquivOfAlgEquivHom** 是 Mathlib 中的一个定义，位于命名空间 `IsFractionRi
ng`。
形式化陈述：fieldEquivOfAlgEquivHom : (B ≃ₐ[A] B) ->* (L ≃ₐ[K] L) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsFractionRing.fieldEquivOfAlgEquiv_refl`：fieldEquivOfAlgEquiv_refl : fi
eldEquivOfAlgEquiv FA FB FB (AlgEquiv.refl : B ≃ₐ[A] B) = AlgEquiv.refl
· 使用引理 `IsFractionRing.fieldEquivOfAlgEquiv_trans`：fieldEquivOfAlgEquiv_trans (f
 : B ≃ₐ[A] C) (g : C ≃ₐ[A] D) : fieldEquivOfAlgEquiv FA FB FD (f.trans g) = (fie
ldEquivOfAlgEquiv FA FB FC f).t…

--- 原说明 ---
An algebra automorphism of a ring induces an algebra automorphism of its fractio
n field.

This is a bundled version of `fieldEquivOfAlgEquiv`.
-/
noncomputable def fieldEquivOfAlgEquivHom : (B ≃ₐ[A] B) →* (L ≃ₐ[K] L) where
  toFun := fieldEquivOfAlgEquiv K L L
  map_one' := fieldEquivOfAlgEquiv_refl A B K L
  map_mul' f g := fieldEquivOfAlgEquiv_trans K L L L g f

@[simp]
/-
**IsFractionRing.fieldEquivOfAlgEquivHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsFrac
tionRing`。
形式化陈述：fieldEquivOfAlgEquivHom_apply (f : B ≃ₐ[A] B) : fieldEquivOfAlgEquivHom K 
L f = fieldEquivOfAlgEquiv K L L f
参数：f : B ≃ₐ[A] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fieldEquivOfAlgEquivHom_apply (f : B ≃ₐ[A] B) :
    fieldEquivOfAlgEquivHom K L f = fieldEquivOfAlgEquiv K L L f :=
  rfl

variable (A B)
/-
**IsFractionRing.fieldEquivOfAlgEquivHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `Is
FractionRing`。
形式化陈述：fieldEquivOfAlgEquivHom_injective : Function.Injective (fieldEquivOfAlgEqu
ivHom K L : (B ≃ₐ[A] B) ->* (L ≃ₐ[K] L))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsFractionRing.fieldEquivOfAlgEquiv_algebraMap`：fieldEquivOfAlgEquiv_alg
ebraMap (f : B ≃ₐ[A] C) (b : B) : fieldEquivOfAlgEquiv FA FB FC f (algebraMap B 
FB b) = algebraMap C FC (f b)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgEquiv.ext_iff`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst 
: CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Alge
bra R …
-/
lemma fieldEquivOfAlgEquivHom_injective :
    Function.Injective (fieldEquivOfAlgEquivHom K L : (B ≃ₐ[A] B) →* (L ≃ₐ[K] L)) := by
  intro f g h
  ext b
  simpa using AlgEquiv.ext_iff.mp h (algebraMap B L b)

end fieldEquivOfAlgEquivHom

/-
**IsFractionRing.isFractionRing_iff_of_base_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 
`IsFractionRing`。
形式化陈述：isFractionRing_iff_of_base_ringEquiv (h : R ≃+* P) : IsFractionRing R S ↔ 
@IsFractionRing P _ S _ ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
参数：h : R ≃+* P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `MulEquivClass.map_nonZeroDivisors`：MulEquivClass.map_nonZeroDivisors {M₀
 S F : Type*} [MonoidWithZero M₀] [MonoidWithZero S] [EquivLike F M₀ S] [MulEqui
vClass F M₀ S] (h : F) …
· 使用定理 `IsLocalization.isLocalization_iff_of_base_ringEquiv`：isLocalization_iff_
of_base_ringEquiv (h : R ≃+* P) : IsLocalization M S ↔ haveI
-/
theorem isFractionRing_iff_of_base_ringEquiv (h : R ≃+* P) :
    IsFractionRing R S ↔
      @IsFractionRing P _ S _ ((algebraMap R S).comp h.symm.toRingHom).toAlgebra := by
  delta IsFractionRing
  convert! isLocalization_iff_of_base_ringEquiv (nonZeroDivisors R) S h
  exact (MulEquivClass.map_nonZeroDivisors h).symm

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [h : IsFractionRing R S]
/-
**IsFractionRing.nontrivial_iff_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `IsFraction
Ring`。
形式化陈述：nontrivial_iff_nontrivial : Nontrivial R ↔ Nontrivial S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.exists_of_eq`：exists_of_eq {x y : R} : algebraMap R S x =
 algebraMap R S y -> exists c : M, c * x = c * y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem nontrivial_iff_nontrivial : Nontrivial R ↔ Nontrivial S := by
  by_contra! ⟨_, _⟩ | ⟨_, _⟩
  · obtain ⟨c, hc⟩ := h.exists_of_eq (x := 1) (y := 0) (Subsingleton.elim _ _)
    simp at hc
  · apply (h.map_units S 1).ne_zero
    rw [Subsingleton.eq_zero ((1 : nonZeroDivisors R) : R), map_zero]
/-
**IsFractionRing.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：∀ (R : Type u_8) (S : Type u_9) [inst : CommSemiring R] [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S]   [h : IsFractionRing R S] [hR : Nontrivial R], N
ontrivial S
参数：R : Type u_8；S : Type u_9。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsFractionRing.nontrivial_iff_nontrivial`：nontrivial_iff_nontrivial : No
ntrivial R ↔ Nontrivial S
-/
protected theorem nontrivial [hR : Nontrivial R] : Nontrivial S :=
  h.nontrivial_iff_nontrivial.mp hR

section MulAction

variable (G A B K L : Type*) [Group G] [CommRing A] [CommRing B] [MulSemiringAction G B]
  [Algebra A B] [Field K] [Field L] [Algebra K L] [Algebra A K] [Algebra B L] [Algebra A L]
  [IsFractionRing A K] [IsFractionRing B L] [IsScalarTower A K L] [IsScalarTower A B L]

/-- Given a `MulSemiringAction G B`, extend the action of `G` on `B` to a `MulSemiringAction G L`
on the fraction field `L` of `B`. -/
@[instance_reducible]
/-
**IsFractionRing.mulSemiringAction** 是 Mathlib 中的一个定义，位于命名空间 `IsFractionRing`。
形式化陈述：mulSemiringAction : MulSemiringAction G L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `MulSemiringAction G B`, extend the action of `G` on `B` to a `MulSemiri
ngAction G L`
on the fraction field `L` of `B`.
-/
noncomputable def mulSemiringAction :
    MulSemiringAction G L :=
  MulSemiringAction.compHom L
    ((ringEquivOfRingEquivHom B L).comp (MulSemiringAction.toRingEquiv G B))

/-- The action of `G` on the fraction field `L` of `B` given by `IsFractionRing.mulSemiringAction`
is compatible with the embedding `B ⊆ L`. -/
/-
**IsFractionRing.smulDistribClass** 是 Mathlib 中的一个实例，位于命名空间 `IsFractionRing`。
形式化陈述：smulDistribClass : letI
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def'`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R} {
inst_1 : Semiring A} [self : Algebra R A] (r : R) (x : A),   r • x = (algebraMap
 R A) r…
· 使用引理 `smul_mul'`：smul_mul' (a : M) (b₁ b₂ : N) : a • (b₁ * b₂) = a • b₁ * a • 
b₂
· 使用引理 `IsFractionRing.ringEquivOfRingEquiv_algebraMap`：ringEquivOfRingEquiv_alg
ebraMap (a : A) : ringEquivOfRingEquiv h (algebraMap A K a) = algebraMap B L (h 
a)

--- 原说明 ---
The action of `G` on the fraction field `L` of `B` given by `IsFractionRing.mulS
emiringAction`
is compatible with the embedding `B ⊆ L`.
-/
instance smulDistribClass :
    letI := mulSemiringAction G B L
    SMulDistribClass G B L :=
  let := mulSemiringAction G B L
  ⟨fun g b x ↦ by
    rw [Algebra.smul_def', Algebra.smul_def', smul_mul']
    congr
    apply ringEquivOfRingEquiv_algebraMap⟩

variable [MulSemiringAction G L] [SMulDistribClass G B L]
/-
**IsFractionRing.faithfulSMul** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：∀ (G : Type u_10) (B : Type u_12) (L : Type u_14) [inst : Group G] [inst_1
 : CommRing B]   [inst_2 : MulSemiringAction G B] [inst_3 : Field L] [inst_4 : A
lgebra B L] [IsFractionRing B L]   [inst_6 : MulSemiringAction G L] [SMulDistrib
Class G B L] [FaithfulSMul G B], FaithfulSMul G L
参数：G : Type u_10；B : Type u_12；L : Type u_14。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
-/
protected theorem faithfulSMul [FaithfulSMul G B] : FaithfulSMul G L :=
  ⟨fun h ↦ eq_of_smul_eq_smul fun x ↦ by simpa [← algebraMap.coe_smul'] using h (algebraMap B L x)⟩
/-
**IsFractionRing.smulCommClass** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：∀ (G : Type u_10) (A : Type u_11) (B : Type u_12) (K : Type u_13) (L : Typ
e u_14) [inst : Group G] [inst_1 : CommRing A]   [inst_2 : CommRing B] [inst_3 :
 MulSemiringAction G B] [inst_4 : Algebra A B] [inst_5 : Field K] [inst_6 : Fiel
d L]   [inst_7 : Algebra K L] [inst_8 : Algebra A K] [inst_9 : Algebra B L] [ins
t_10 : Algebra A L] [IsFractionRing A K]   [IsFractionRing B L] [IsScalarTower A
 K L] [IsScalarTower A B L] [inst_15 : MulSemiringAction G L]   [SMulDistribClas
s G B L] [SMulCommClass G A B], SMulCommClass G K L
参数：G : Type u_10；A : Type u_11；B : Type u_12；K : Type u_13；L : Type u_14。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用引理 `smul_mul'`：smul_mul' (a : M) (b₁ b₂ : N) : a • (b₁ * b₂) = a • b₁ * a • 
b₂
· 使用定理 `smul_div₀'`：smul_div₀' (g : α) (x y : β) : g • (x / y) = (g • x) / (g • 
y)
· 使用定理 `smul_algebraMap`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Algebra R A] {α : Type u_2}   [inst_3 : Monoid α] [
inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem smulCommClass [SMulCommClass G A B] : SMulCommClass G K L :=
  ⟨fun g x y ↦ by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
    obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective B y
    simp [Algebra.smul_def, map_div₀, ← IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply A B L, smul_mul', smul_div₀',
      ← algebraMap.coe_smul', smul_algebraMap]⟩

end MulAction

end IsFractionRing

section algebraMap_injective

/-
**algebraMap_injective_of_field_isFractionRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraMap_injective_of_field_isFractionRing (K L : Type*) [Field K] [Semi
ring L] [Nontrivial L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [Algebra
 K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] : Function.Injec
tive (algebraMap R S)
参数：K L : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.coe_comp`：coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp
 hmn : α -> γ) = hnp ∘ hmn
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
-/
theorem algebraMap_injective_of_field_isFractionRing (K L : Type*) [Field K] [Semiring L]
    [Nontrivial L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] : Function.Injective (algebraMap R S) := by
  refine Function.Injective.of_comp (f := algebraMap S L) ?_
  rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
/-
**FaithfulSMul.of_field_isFractionRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FaithfulSMul.of_field_isFractionRing (K L : Type*) [Field K] [Semiring L] 
[Nontrivial L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [Algebra K L] [A
lgebra R L] [IsScalarTower R S L] [IsScalarTower R K L] : FaithfulSMul R S
参数：K L : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `algebraMap_injective_of_field_isFractionRing`：algebraMap_injective_of_fi
eld_isFractionRing (K L : Type*) [Field K] [Semiring L] [Nontrivial L] [Algebra 
R K] [IsFractionRing R K] [Algebra…
-/
theorem FaithfulSMul.of_field_isFractionRing (K L : Type*) [Field K] [Semiring L]
    [Nontrivial L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] : FaithfulSMul R S :=
  (faithfulSMul_iff_algebraMap_injective R S).mpr <|
    algebraMap_injective_of_field_isFractionRing R S K L

end algebraMap_injective

variable (A)

/-- The fraction ring of a commutative ring `R` as a quotient type.

We instantiate this definition as generally as possible, and assume that the
commutative ring `R` is an integral domain only when this is needed for proving.

In this generality, this construction is also known as the *total fraction ring* of `R`.
-/
/-
**FractionRing** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：FractionRing
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fraction ring of a commutative ring `R` as a quotient type.

We instantiate this definition as generally as possible, and assume that the
commutative ring `R` is an integral domain only when this is needed for proving.

In this generality, this construction is also known as the *total fraction ring*
 of `R`.
-/
abbrev FractionRing :=
  Localization (nonZeroDivisors R)

namespace FractionRing

/-
**FractionRing.** 是 Mathlib 中的一个实例，位于命名空间 `FractionRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFractionRing (FractionRing R) (FractionRing R) := IsFractionRing.idem R _
/-
**FractionRing.unique** 是 Mathlib 中的一个实例，位于命名空间 `FractionRing`。
形式化陈述：unique [Subsingleton R] : Unique (FractionRing R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance unique [Subsingleton R] : Unique (FractionRing R) := inferInstance
/-
**FractionRing.** 是 Mathlib 中的一个实例，位于命名空间 `FractionRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] : Nontrivial (FractionRing R) := inferInstance

variable {R} in
/-
**FractionRing.** 是 Mathlib 中的一个实例，位于命名空间 `FractionRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq R] : DecidableEq (FractionRing R) := by
  intro x y
  apply Localization.recOnSubsingleton₂ x y (r := fun x y ↦ Decidable (x = y))
  intro a c b d
  simp only [Localization.mk_eq_mk_iff, Localization.r_iff_of_le_nonZeroDivisors (le_refl _)]
  infer_instance

variable [IsDomain A]
/-
**FractionRing.field** 是 Mathlib 中的一个实例，位于命名空间 `FractionRing`。
形式化陈述：field : Field (FractionRing A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance field : Field (FractionRing A) := inferInstance

@[simp]
/-
**FractionRing.mk_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `FractionRing`。
形式化陈述：mk_eq_div {r s} : (Localization.mk r s : FractionRing A) = (algebraMap _ _
 r / algebraMap A _ s : FractionRing A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
-/
theorem mk_eq_div {r s} :
    (Localization.mk r s : FractionRing A) =
      (algebraMap _ _ r / algebraMap A _ s : FractionRing A) := by
  rw [Localization.mk_eq_mk', IsFractionRing.mk'_eq_div]

section liftAlgebra

variable [Field K] [Algebra R K] [FaithfulSMul R K]

/-- This is not an instance because it creates a diamond when `K = FractionRing R`.
Should usually be introduced locally along with `isScalarTower_liftAlgebra`
See note [reducible non-instances]. -/
/-
**FractionRing.liftAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 `FractionRing`。
形式化陈述：liftAlgebra : Algebra (FractionRing R) K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is not an instance because it creates a diamond when `K = FractionRing R`.
Should usually be introduced locally along with `isScalarTower_liftAlgebra`
See note [reducible non-instances].
-/
noncomputable abbrev liftAlgebra : Algebra (FractionRing R) K :=
  have := IsDomain.of_faithfulSMul R K
  RingHom.toAlgebra (IsFractionRing.lift (FaithfulSMul.algebraMap_injective R K))

attribute [local instance] liftAlgebra
/-
**FractionRing.isScalarTower_liftAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `FractionRing
`。
形式化陈述：isScalarTower_liftAlgebra : IsScalarTower R (FractionRing R) K
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDomain.of_faithfulSMul`：IsDomain.of_faithfulSMul [IsDomain A] : IsDoma
in R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.lift_algebraMap`：lift_algebraMap (hg : Injective g) (x) :
 lift hg (algebraMap A K x) = g x
-/
instance isScalarTower_liftAlgebra : IsScalarTower R (FractionRing R) K :=
  have := IsDomain.of_faithfulSMul R K
  .of_algebraMap_eq fun x ↦
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R K) x).symm
/-
**FractionRing.algebraMap_liftAlgebra** 是 Mathlib 中的一个引理，位于命名空间 `FractionRing`。
形式化陈述：algebraMap_liftAlgebra : have
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma algebraMap_liftAlgebra :
    have := IsDomain.of_faithfulSMul R K
    algebraMap (FractionRing R) K = IsFractionRing.lift (FaithfulSMul.algebraMap_injective R _) :=
  rfl
/-
**FractionRing.** 是 Mathlib 中的一个实例，位于命名空间 `FractionRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₀} [SMul R₀ R] [IsScalarTower R₀ R R] [SMul R₀ K] [IsScalarTower R₀ R K] :
    IsScalarTower R₀ (FractionRing R) K := IsScalarTower.to₁₃₄ _ R _ _

end liftAlgebra

/-- Given a ring `A` and a localization map to a fraction ring
`f : A →+* K`, we get an `A`-isomorphism between the fraction ring of `A` as a quotient
type and `K`. -/
/-
**FractionRing.algEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FractionRing`。
形式化陈述：algEquiv (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] : Fra
ctionRing A ≃ₐ[A] K
参数：K : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a ring `A` and a localization map to a fraction ring
`f : A →+* K`, we get an `A`-isomorphism between the fraction ring of `A` as a q
uotient
type and `K`.
-/
noncomputable def algEquiv (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] :
    FractionRing A ≃ₐ[A] K :=
  Localization.algEquiv (nonZeroDivisors A) K
/-
**FractionRing.** 是 Mathlib 中的一个实例，位于命名空间 `FractionRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra R A] [FaithfulSMul R A] : FaithfulSMul R (FractionRing A) := by
  rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq R A]
  exact (FaithfulSMul.algebraMap_injective A (FractionRing A)).comp
    (FaithfulSMul.algebraMap_injective R A)

section IsScalarTower

attribute [local instance] liftAlgebra

/-
**FractionRing.** 是 Mathlib 中的一个实例，位于命名空间 `FractionRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (k K : Type*) [Field k] [Field K] [Algebra A k] [Algebra A K] [Algebra k K]
    [FaithfulSMul A k] [FaithfulSMul A K] [IsScalarTower A k K] :
    IsScalarTower (FractionRing A) k K where
  smul_assoc a b c := a.ind fun ⟨a₁, a₂⟩ ↦ by
    rw [← smul_right_inj (nonZeroDivisors.coe_ne_zero a₂)]
    simp_rw [← smul_assoc, Localization.smul_mk, smul_eq_mul, Localization.mk_eq_mk',
      IsLocalization.mk'_mul_cancel_left, algebraMap_smul, smul_assoc]

end IsScalarTower

end FractionRing

