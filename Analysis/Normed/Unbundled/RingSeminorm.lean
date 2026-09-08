/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Seminorms and norms on rings

This file defines seminorms and norms on rings. These definitions are useful when one needs to
consider multiple (semi)norms on a given ring.

## Main declarations

For a ring `R`:
* `RingSeminorm`: A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes
  nonnegative values, is subadditive and submultiplicative and such that `f (-x) = f x` for all
  `x ∈ R`.
* `RingNorm`: A seminorm `f` is a norm if `f x = 0` if and only if `x = 0`.
* `MulRingSeminorm`: A multiplicative seminorm on a ring `R` is a ring seminorm that preserves
  multiplication.
* `MulRingNorm`: A multiplicative norm on a ring `R` is a ring norm that preserves multiplication.
  `MulRingNorm R` is essentially the same as `AbsoluteValue R ℝ`, and it is recommended to
  use the latter instead to avoid duplicating results.

## Notes

The corresponding hom classes are defined in `Mathlib/Algebra/Order/Hom/Basic.lean` to be used by
absolute values; see `Mathlib/Algebra/Order/AbsoluteValue/Basic.lean` for the bundled version.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags
ring_seminorm, ring_norm
-/

@[expose] public section


open NNReal

variable {R : Type*}

/-- A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes nonnegative
  values, is subadditive and submultiplicative and such that `f (-x) = f x` for all `x ∈ R`. -/
/-
**RingSeminorm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_2) → [NonUnitalNonAssocRing R] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes no
nnegative
  values, is subadditive and submultiplicative and such that `f (-x) = f x` for 
all `x ∈ R`.
-/
structure RingSeminorm (R : Type*) [NonUnitalNonAssocRing R] extends AddGroupSeminorm R where
  /-- The property of a `RingSeminorm` that for all `x` and `y` in the ring, the norm of `x * y` is
  less than the norm of `x` times the norm of `y`. -/
  mul_le' : ∀ x y : R, toFun (x * y) ≤ toFun x * toFun y

/-- A function `f : R → ℝ` is a norm on a (nonunital) ring if it is a seminorm and `f x = 0`
  implies `x = 0`. -/
/-
**RingNorm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_2) → [NonUnitalNonAssocRing R] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : R → ℝ` is a norm on a (nonunital) ring if it is a seminorm and `
f x = 0`
  implies `x = 0`.
-/
structure RingNorm (R : Type*) [NonUnitalNonAssocRing R] extends RingSeminorm R, AddGroupNorm R

/-- A multiplicative seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero and
multiplication, takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x`.
-/
/-
**MulRingSeminorm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_2) → [NonAssocRing R] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiplicative seminorm on a ring `R` is a function `f : R → ℝ` that preserves
 zero and
multiplication, takes nonnegative values, is subadditive and such that `f (-x) =
 f x` for all `x`.
-/
structure MulRingSeminorm (R : Type*) [NonAssocRing R] extends AddGroupSeminorm R,
  MonoidWithZeroHom R ℝ

/-- A multiplicative norm on a ring `R` is a multiplicative ring seminorm such that `f x = 0`
implies `x = 0`.

It is recommended to use `AbsoluteValue R ℝ` instead (which works for `Semiring R`
and is equivalent to `MulRingNorm R` for a nontrivial `Ring R`). -/
/-
**MulRingNorm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_2) → [NonAssocRing R] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiplicative norm on a ring `R` is a multiplicative ring seminorm such that 
`f x = 0`
implies `x = 0`.

It is recommended to use `AbsoluteValue R ℝ` instead (which works for `Semiring 
R`
and is equivalent to `MulRingNorm R` for a nontrivial `Ring R`).
-/
structure MulRingNorm (R : Type*) [NonAssocRing R] extends MulRingSeminorm R, AddGroupNorm R

attribute [nolint docBlame]
  RingSeminorm.toAddGroupSeminorm RingNorm.toAddGroupNorm RingNorm.toRingSeminorm
    MulRingSeminorm.toAddGroupSeminorm MulRingSeminorm.toMonoidWithZeroHom
    MulRingNorm.toAddGroupNorm MulRingNorm.toMulRingSeminorm

namespace RingSeminorm

section NonUnitalRing

variable [NonUnitalRing R]

/-
**RingSeminorm.funLike** 是 Mathlib 中的一个实例，位于命名空间 `RingSeminorm`。
形式化陈述：funLike : FunLike (RingSeminorm R) R Real where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (RingSeminorm R) R ℝ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x
/-
**RingSeminorm.ringSeminormClass** 是 Mathlib 中的一个实例，位于命名空间 `RingSeminorm`。
形式化陈述：ringSeminormClass : RingSeminormClass (RingSeminorm R) R Real where map_ze
ro f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupSeminorm.add_le'`：∀ {G : Type u_6} [inst : AddGroup G] (self : A
ddGroupSeminorm G) (r s : G),   self.toFun (r + s) ≤ self.toFun r + self.toFun s
· 使用定理 `AddGroupSeminorm.map_zero'`：∀ {G : Type u_6} [inst : AddGroup G] (self :
 AddGroupSeminorm G), self.toFun 0 = 0
· 使用定理 `AddGroupSeminorm.neg'`：∀ {G : Type u_6} [inst : AddGroup G] (self : AddG
roupSeminorm G) (r : G), self.toFun (-r) = self.toFun r
· 使用定理 `RingSeminorm.mul_le'`：∀ {R : Type u_2} [inst : NonUnitalNonAssocRing R] 
(self : RingSeminorm R) (x y : R),   self.toFun (x * y) ≤ self.toFun x * self.to
Fun y
-/
instance ringSeminormClass : RingSeminormClass (RingSeminorm R) R ℝ where
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'

@[simp]
/-
**RingSeminorm.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingSeminorm`。
形式化陈述：toFun_eq_coe (p : RingSeminorm R) : (p.toAddGroupSeminorm : R -> Real) = p
参数：p : RingSeminorm R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (p : RingSeminorm R) : (p.toAddGroupSeminorm : R → ℝ) = p :=
  rfl

@[ext]
/-
**RingSeminorm.ext** 是 Mathlib 中的一个定理，位于命名空间 `RingSeminorm`。
形式化陈述：ext {p q : RingSeminorm R} : (forall x, p x = q x) -> p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {p q : RingSeminorm R} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q
/-
**RingSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `RingSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (RingSeminorm R) :=
  ⟨{ AddGroupSeminorm.instZeroAddGroupSeminorm.zero with mul_le' :=
    fun _ _ => (zero_mul _).ge }⟩
/-
**RingSeminorm.eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingSeminorm`。
形式化陈述：eq_zero_iff {p : RingSeminorm R} : p = 0 ↔ forall x, p x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem eq_zero_iff {p : RingSeminorm R} : p = 0 ↔ ∀ x, p x = 0 :=
  DFunLike.ext_iff
/-
**RingSeminorm.ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingSeminorm`。
形式化陈述：ne_zero_iff {p : RingSeminorm R} : p != 0 ↔ exists x, p x != 0
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
theorem ne_zero_iff {p : RingSeminorm R} : p ≠ 0 ↔ ∃ x, p x ≠ 0 := by simp [eq_zero_iff]
/-
**RingSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `RingSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (RingSeminorm R) :=
  ⟨0⟩

/-- The trivial seminorm on a ring `R` is the `RingSeminorm` taking value `0` at `0` and `1` at
every other element. -/
/-
**RingSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `RingSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial seminorm on a ring `R` is the `RingSeminorm` taking value `0` at `0`
 and `1` at
every other element.
-/
instance [DecidableEq R] : One (RingSeminorm R) :=
  ⟨{ (1 : AddGroupSeminorm R) with
      mul_le' := fun x y => by
        by_cases h : x * y = 0
        · refine (if_pos h).trans_le (mul_nonneg ?_ ?_) <;>
            · change _ ≤ ite _ _ _
              split_ifs
              exacts [le_rfl, zero_le_one]
        · change ite _ _ _ ≤ ite _ _ _ * ite _ _ _
          simp only [if_false, h, left_ne_zero_of_mul h, right_ne_zero_of_mul h, mul_one,
            le_refl] }⟩

@[simp]
/-
**RingSeminorm.apply_one** 是 Mathlib 中的一个定理，位于命名空间 `RingSeminorm`。
形式化陈述：apply_one [DecidableEq R] (x : R) : (1 : RingSeminorm R) x = if x = 0 then
 0 else 1
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_one [DecidableEq R] (x : R) : (1 : RingSeminorm R) x = if x = 0 then 0 else 1 :=
  rfl

end NonUnitalRing

section Ring

variable [Ring R] (p : RingSeminorm R)

/-
**RingSeminorm.seminorm_one_eq_one_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `RingSe
minorm`。
形式化陈述：seminorm_one_eq_one_iff_ne_zero (hp : p 1 <= 1) : p 1 = 1 ↔ p != 0
参数：hp : p 1 <= 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingSeminorm.ne_zero_iff`：ne_zero_iff {p : RingSeminorm R} : p != 0 ↔ ex
ists x, p x != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用定理 `RingSeminorm.ext`：ext {p q : RingSeminorm R} : (forall x, p x = q x) -> 
p = q
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `SubmultiplicativeHomClass.map_mul_le_mul`：∀ {F : Type u_7} {α : outParam
 (Type u_8)} {β : outParam (Type u_9)} {inst : Mul α} {inst_1 : Mul β} {inst_2 :
 LE β}   {inst_3 : FunLike F α…
· 使用定理 `RingSeminormClass.toSubmultiplicativeHomClass`：∀ {F : Type u_7} {α : out
Param (Type u_8)} {β : outParam (Type u_9)} {inst : NonUnitalNonAssocRing α}   {
inst_1 : Semiring β} {inst_2 : Part…
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_mul_iff_one_le_left`：le_mul_iff_one_le_left [MulPosMono α] [MulPosRef
lectLE α] (a0 : 0 < a) : a <= b * a ↔ 1 <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem seminorm_one_eq_one_iff_ne_zero (hp : p 1 ≤ 1) : p 1 = 1 ↔ p ≠ 0 := by
  refine
    ⟨fun h => ne_zero_iff.mpr ⟨1, by rw [h]; exact one_ne_zero⟩,
      fun h => ?_⟩
  obtain hp0 | hp0 := (apply_nonneg p (1 : R)).eq_or_lt'
  · exfalso
    refine h (ext fun x => (apply_nonneg _ _).antisymm' ?_)
    simpa only [hp0, mul_one, mul_zero] using map_mul_le_mul p x 1
  · refine hp.antisymm ((le_mul_iff_one_le_left hp0).1 ?_)
    simpa only [one_mul] using map_mul_le_mul p (1 : R) _

/-- The `SeminormedRing` structure on a ring `R` determined by a `RingSeminorm`. -/
/-
**RingSeminorm.toSeminormedRing** 是 Mathlib 中的一个缩写定义，位于命名空间 `RingSeminorm`。
形式化陈述：toSeminormedRing : SeminormedRing R where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.dist_eq`：∀ {E : Type u_8} [self : SeminormedAddCo
mmGroup E] (x y : E), dist x y = ‖-x + y‖

--- 原说明 ---
The `SeminormedRing` structure on a ring `R` determined by a `RingSeminorm`.
-/
abbrev toSeminormedRing : SeminormedRing R where
  __ := ‹Ring R›
  __ := p.toAddGroupSeminorm.toSeminormedAddCommGroup
  norm_mul_le := map_mul_le_mul p

end Ring

section CommRing

variable [CommRing R] (p : RingSeminorm R)

/-
**RingSeminorm.exists_index_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `RingSeminorm`。
形式化陈述：exists_index_pow_le (hna : IsNonarchimedean p) (x y : R) (n : Nat) : exist
s (m : Nat), m < n + 1 ∧ p ((x + y) ^ (n : Nat)) ^ (1 / (n : Real)) <= (p (x ^ m
) * p (y ^ (n - m : Nat))) ^ (1 / (n : Real))
参数：hna : IsNonarchimedean p；x y : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNonarchimedean.add_pow_le`：add_pow_le {F α : Type*} [CommRing α] [FunL
ike F α R] [ZeroHomClass F α R] [NonnegHomClass F α R] [SubmultiplicativeHomClas
s F α R] {f : F} …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `RingSeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_7} {α : outPara
m (Type u_8)} {β : outParam (Type u_9)} {inst : NonUnitalNonAssocRing α}   {inst
_1 : Semiring β} {inst_2 : Part…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用定理 `RingSeminormClass.toSubmultiplicativeHomClass`：∀ {F : Type u_7} {α : out
Param (Type u_8)} {β : outParam (Type u_9)} {inst : NonUnitalNonAssocRing α}   {
inst_1 : Semiring β} {inst_2 : Part…
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem exists_index_pow_le (hna : IsNonarchimedean p) (x y : R) (n : ℕ) :
    ∃ (m : ℕ), m < n + 1 ∧ p ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤
      (p (x ^ m) * p (y ^ (n - m : ℕ))) ^ (1 / (n : ℝ)) := by
  obtain ⟨m, hm_lt, hm⟩ := IsNonarchimedean.add_pow_le hna n x y
  exact ⟨m, hm_lt, by gcongr⟩

end CommRing

end RingSeminorm

/-- If `f` is a ring seminorm on `a`, then `∀ {n : ℕ}, n ≠ 0 → f (a ^ n) ≤ f a ^ n`. -/
/-
**map_pow_le_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {F : Type u_2} {α : Type u_3} [inst : Ring α] [inst_1 : FunLike F α ℝ] [
RingSeminormClass F α ℝ] (f : F) (a : α)   {n : ℕ}, n ≠ 0 → f (a ^ n) ≤ f a ^ n
参数：f : F；a : α；a ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a ring seminorm on `a`, then `∀ {n : ℕ}, n ≠ 0 → f (a ^ n) ≤ f a ^ n`.
-/
theorem map_pow_le_pow {F α : Type*} [Ring α] [FunLike F α ℝ] [RingSeminormClass F α ℝ] (f : F)
    (a : α) : ∀ {n : ℕ}, n ≠ 0 → f (a ^ n) ≤ f a ^ n
  | 0, h => absurd rfl h
  | 1, _ => by simp only [pow_one, le_refl]
  | n + 2, _ => by
    simp only [pow_succ _ (n + 1)]
    grw [map_mul_le_mul, map_pow_le_pow _ _ n.succ_ne_zero]

/-- If `f` is a ring seminorm on `a` with `f 1 ≤ 1`, then `∀ (n : ℕ), f (a ^ n) ≤ f a ^ n`. -/
/-
**map_pow_le_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {F : Type u_2} {α : Type u_3} [inst : Ring α] [inst_1 : FunLike F α ℝ] [
RingSeminormClass F α ℝ] {f : F},   f 1 ≤ 1 → ∀ (a : α) (n : ℕ), f (a ^ n) ≤ f a
 ^ n
参数：a : α；n : ℕ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `map_pow_le_pow`：∀ {F : Type u_2} {α : Type u_3} [inst : Ring α] [inst_1 
: FunLike F α ℝ] [RingSeminormClass F α ℝ] (f : F) (a : α)   {n : ℕ}, n ≠ 0 → f 
(a ^…
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0

--- 原说明 ---
If `f` is a ring seminorm on `a` with `f 1 ≤ 1`, then `∀ (n : ℕ), f (a ^ n) ≤ f 
a ^ n`.
-/
theorem map_pow_le_pow' {F α : Type*} [Ring α] [FunLike F α ℝ] [RingSeminormClass F α ℝ] {f : F}
    (hf1 : f 1 ≤ 1) (a : α) : ∀ n : ℕ, f (a ^ n) ≤ f a ^ n
  | 0 => by simp only [pow_zero, hf1]
  | n + 1 => map_pow_le_pow _ _ n.succ_ne_zero

/-- The norm of a `NonUnitalSeminormedRing` as a `RingSeminorm`. -/
/-
**normRingSeminorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：normRingSeminorm (R : Type*) [NonUnitalSeminormedRing R] : RingSeminorm R
参数：R : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖

--- 原说明 ---
The norm of a `NonUnitalSeminormedRing` as a `RingSeminorm`.
-/
def normRingSeminorm (R : Type*) [NonUnitalSeminormedRing R] : RingSeminorm R :=
  { normAddGroupSeminorm R with
    toFun := norm
    mul_le' := norm_mul_le }

namespace RingSeminorm

variable [Ring R] (p : RingSeminorm R)

open Filter Nat Real

/-- If `f` is a ring seminorm on `R` with `f 1 ≤ 1` and `s : ℕ → ℕ` is bounded by `n`, then
  `f (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ))` is eventually bounded. -/
/-
**RingSeminorm.isBoundedUnder** 是 Mathlib 中的一个定理，位于命名空间 `RingSeminorm`。
形式化陈述：isBoundedUnder (hp : p 1 <= 1) {s : Nat -> Nat} (hs_le : forall n : Nat, s
 n <= n) {x : R} (ψ : Nat -> Nat) : IsBoundedUnder LE.le atTop fun n : Nat => p 
(x ^ s (ψ n)) ^ (1 / (ψ n : Real))
参数：hp : p 1 <= 1；hs_le : forall n : Nat, s n <= n；ψ : Nat -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one_div`：mul_one_div (x y : G) : x * (1 / y) = x / y
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `map_pow_le_pow'`：∀ {F : Type u_2} {α : Type u_3} [inst : Ring α] [inst_1
 : FunLike F α ℝ] [RingSeminormClass F α ℝ] {f : F},   f 1 ≤ 1 → ∀ (a : α) (n : 
ℕ), f…
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.isBoundedUnder_of`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {f : Filter β} {u : β → α},   (∃ b, ∀ (x : β), r (u x) b) → Filter.IsBounde
dUnder r f u
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Real.rpow_le_one`：rpow_le_one {x z : Real} (hx1 : 0 <= x) (hx2 : x <= 1)
 (hz : 0 <= z) : x ^ z <= 1
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `Real.rpow_le_self_of_one_le`：rpow_le_self_of_one_le (h₁ : 1 <= x) (h₂ : 
y <= 1) : x ^ y <= x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is a ring seminorm on `R` with `f 1 ≤ 1` and `s : ℕ → ℕ` is bounded by `n
`, then
  `f (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ))` is eventually bounded.
-/
theorem isBoundedUnder (hp : p 1 ≤ 1) {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x : R} (ψ : ℕ → ℕ) :
    IsBoundedUnder LE.le atTop fun n : ℕ => p (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ)) := by
  have h_le : ∀ m : ℕ, p (x ^ s (ψ m)) ^ (1 / (ψ m : ℝ)) ≤ p x ^ ((s (ψ m) : ℝ) / (ψ m : ℝ)) := by
    intro m
    rw [← mul_one_div (s (ψ m) : ℝ), rpow_mul (apply_nonneg p x), rpow_natCast]
    grw [map_pow_le_pow' hp x]
  apply isBoundedUnder_of
  cases le_or_gt (p x) 1 with
  | inl hfx =>
    use 1, fun m ↦ le_trans (h_le m) (rpow_le_one (by positivity) hfx (by positivity))
  | inr hfx =>
    use p x
    refine fun m ↦ le_trans (h_le m) <| rpow_le_self_of_one_le hfx.le ?_
    exact div_le_one_of_le₀ (mod_cast hs_le _) (cast_nonneg _)

end RingSeminorm

namespace RingNorm

section NonUnitalRing

variable [NonUnitalRing R]

/-
**RingNorm.funLike** 是 Mathlib 中的一个实例，位于命名空间 `RingNorm`。
形式化陈述：funLike : FunLike (RingNorm R) R Real where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (RingNorm R) R ℝ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x
/-
**RingNorm.ringNormClass** 是 Mathlib 中的一个实例，位于命名空间 `RingNorm`。
形式化陈述：ringNormClass : RingNormClass (RingNorm R) R Real where map_zero f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupSeminorm.add_le'`：∀ {G : Type u_6} [inst : AddGroup G] (self : A
ddGroupSeminorm G) (r s : G),   self.toFun (r + s) ≤ self.toFun r + self.toFun s
· 使用定理 `AddGroupSeminorm.map_zero'`：∀ {G : Type u_6} [inst : AddGroup G] (self :
 AddGroupSeminorm G), self.toFun 0 = 0
· 使用定理 `AddGroupSeminorm.neg'`：∀ {G : Type u_6} [inst : AddGroup G] (self : AddG
roupSeminorm G) (r : G), self.toFun (-r) = self.toFun r
· 使用定理 `RingSeminorm.mul_le'`：∀ {R : Type u_2} [inst : NonUnitalNonAssocRing R] 
(self : RingSeminorm R) (x y : R),   self.toFun (x * y) ≤ self.toFun x * self.to
Fun y
· 使用定理 `RingNorm.eq_zero_of_map_eq_zero'`：∀ {R : Type u_2} [inst : NonUnitalNonA
ssocRing R] (self : RingNorm R) (x : R), self.toFun x = 0 → x = 0
-/
instance ringNormClass : RingNormClass (RingNorm R) R ℝ where
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
/-
**RingNorm.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingNorm`。
形式化陈述：toFun_eq_coe (p : RingNorm R) : p.toFun = p
参数：p : RingNorm R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (p : RingNorm R) : p.toFun = p := rfl

@[ext]
/-
**RingNorm.ext** 是 Mathlib 中的一个定理，位于命名空间 `RingNorm`。
形式化陈述：ext {p q : RingNorm R} : (forall x, p x = q x) -> p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {p q : RingNorm R} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

variable (R)

/-- The trivial norm on a ring `R` is the `RingNorm` taking value `0` at `0` and `1` at every
  other element. -/
/-
**RingNorm.** 是 Mathlib 中的一个实例，位于命名空间 `RingNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial norm on a ring `R` is the `RingNorm` taking value `0` at `0` and `1`
 at every
  other element.
-/
instance [DecidableEq R] : One (RingNorm R) :=
  ⟨{ (1 : RingSeminorm R), (1 : AddGroupNorm R) with }⟩

@[simp]
/-
**RingNorm.apply_one** 是 Mathlib 中的一个定理，位于命名空间 `RingNorm`。
形式化陈述：apply_one [DecidableEq R] (x : R) : (1 : RingNorm R) x = if x = 0 then 0 e
lse 1
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_one [DecidableEq R] (x : R) : (1 : RingNorm R) x = if x = 0 then 0 else 1 :=
  rfl
/-
**RingNorm.** 是 Mathlib 中的一个实例，位于命名空间 `RingNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq R] : Inhabited (RingNorm R) :=
  ⟨1⟩

end NonUnitalRing

/-- The `NormedRing` structure on a ring `R` determined by a `RingNorm`. -/
-- See note |reducible non-instances]
/-
**RingNorm.toNormedRing** 是 Mathlib 中的一个缩写定义，位于命名空间 `RingNorm`。
形式化陈述：toNormedRing [Ring R] (f : RingNorm R) : NormedRing R where __
参数：f : RingNorm R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddCommGroup.dist_eq`：∀ {E : Type u_8} [self : NormedAddCommGroup 
E] (x y : E), dist x y = ‖-x + y‖
-/
abbrev toNormedRing [Ring R] (f : RingNorm R) : NormedRing R where
  __ := ‹Ring R›
  __ := f.toAddGroupNorm.toNormedAddCommGroup
  norm_mul_le := map_mul_le_mul f

end RingNorm

namespace MulRingSeminorm

variable [NonAssocRing R]

/-
**MulRingSeminorm.funLike** 是 Mathlib 中的一个实例，位于命名空间 `MulRingSeminorm`。
形式化陈述：funLike : FunLike (MulRingSeminorm R) R Real where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (MulRingSeminorm R) R ℝ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x
/-
**MulRingSeminorm.mulRingSeminormClass** 是 Mathlib 中的一个实例，位于命名空间 `MulRingSeminor
m`。
形式化陈述：mulRingSeminormClass : MulRingSeminormClass (MulRingSeminorm R) R Real whe
re map_zero f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupSeminorm.add_le'`：∀ {G : Type u_6} [inst : AddGroup G] (self : A
ddGroupSeminorm G) (r s : G),   self.toFun (r + s) ≤ self.toFun r + self.toFun s
· 使用定理 `AddGroupSeminorm.map_zero'`：∀ {G : Type u_6} [inst : AddGroup G] (self :
 AddGroupSeminorm G), self.toFun 0 = 0
· 使用定理 `AddGroupSeminorm.neg'`：∀ {G : Type u_6} [inst : AddGroup G] (self : AddG
roupSeminorm G) (r : G), self.toFun (-r) = self.toFun r
· 使用定理 `MulRingSeminorm.map_mul'`：∀ {R : Type u_2} [inst : NonAssocRing R] (self
 : MulRingSeminorm R) (x y : R),   self.toFun (x * y) = self.toFun x * self.toFu
n y
· 使用定理 `MulRingSeminorm.map_one'`：∀ {R : Type u_2} [inst : NonAssocRing R] (self
 : MulRingSeminorm R), self.toFun 1 = 1
-/
instance mulRingSeminormClass : MulRingSeminormClass (MulRingSeminorm R) R ℝ where
  map_zero f := f.map_zero'
  map_one f := f.map_one'
  map_add_le_add f := f.add_le'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'

@[simp]
/-
**MulRingSeminorm.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulRingSeminorm`。
形式化陈述：toFun_eq_coe (p : MulRingSeminorm R) : (p.toAddGroupSeminorm : R -> Real) 
= p
参数：p : MulRingSeminorm R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (p : MulRingSeminorm R) : (p.toAddGroupSeminorm : R → ℝ) = p :=
  rfl

@[ext]
/-
**MulRingSeminorm.ext** 是 Mathlib 中的一个定理，位于命名空间 `MulRingSeminorm`。
形式化陈述：ext {p q : MulRingSeminorm R} : (forall x, p x = q x) -> p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {p q : MulRingSeminorm R} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

variable [DecidableEq R] [NoZeroDivisors R] [Nontrivial R]

/-- The trivial seminorm on a ring `R` is the `MulRingSeminorm` taking value `0` at `0` and `1` at
every other element. -/
/-
**MulRingSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `MulRingSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial seminorm on a ring `R` is the `MulRingSeminorm` taking value `0` at 
`0` and `1` at
every other element.
-/
instance : One (MulRingSeminorm R) :=
  ⟨{ (1 : AddGroupSeminorm R) with
      map_one' := if_neg one_ne_zero
      map_mul' := fun x y => by
        obtain rfl | hx := eq_or_ne x 0
        · simp
        obtain rfl | hy := eq_or_ne y 0
        · simp
        · simp [hx, hy] }⟩

@[simp]
/-
**MulRingSeminorm.apply_one** 是 Mathlib 中的一个定理，位于命名空间 `MulRingSeminorm`。
形式化陈述：apply_one (x : R) : (1 : MulRingSeminorm R) x = if x = 0 then 0 else 1
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_one (x : R) : (1 : MulRingSeminorm R) x = if x = 0 then 0 else 1 :=
  rfl
/-
**MulRingSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `MulRingSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (MulRingSeminorm R) :=
  ⟨1⟩

end MulRingSeminorm

namespace MulRingNorm

variable [NonAssocRing R]

/-
**MulRingNorm.funLike** 是 Mathlib 中的一个实例，位于命名空间 `MulRingNorm`。
形式化陈述：funLike : FunLike (MulRingNorm R) R Real where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (MulRingNorm R) R ℝ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x
/-
**MulRingNorm.mulRingNormClass** 是 Mathlib 中的一个实例，位于命名空间 `MulRingNorm`。
形式化陈述：mulRingNormClass : MulRingNormClass (MulRingNorm R) R Real where map_zero 
f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupSeminorm.add_le'`：∀ {G : Type u_6} [inst : AddGroup G] (self : A
ddGroupSeminorm G) (r s : G),   self.toFun (r + s) ≤ self.toFun r + self.toFun s
· 使用定理 `AddGroupSeminorm.map_zero'`：∀ {G : Type u_6} [inst : AddGroup G] (self :
 AddGroupSeminorm G), self.toFun 0 = 0
· 使用定理 `AddGroupSeminorm.neg'`：∀ {G : Type u_6} [inst : AddGroup G] (self : AddG
roupSeminorm G) (r : G), self.toFun (-r) = self.toFun r
· 使用定理 `MulRingSeminorm.map_mul'`：∀ {R : Type u_2} [inst : NonAssocRing R] (self
 : MulRingSeminorm R) (x y : R),   self.toFun (x * y) = self.toFun x * self.toFu
n y
· 使用定理 `MulRingSeminorm.map_one'`：∀ {R : Type u_2} [inst : NonAssocRing R] (self
 : MulRingSeminorm R), self.toFun 1 = 1
· 使用定理 `MulRingNorm.eq_zero_of_map_eq_zero'`：∀ {R : Type u_2} [inst : NonAssocRi
ng R] (self : MulRingNorm R) (x : R), self.toFun x = 0 → x = 0
-/
instance mulRingNormClass : MulRingNormClass (MulRingNorm R) R ℝ where
  map_zero f := f.map_zero'
  map_one f := f.map_one'
  map_add_le_add f := f.add_le'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
/-
**MulRingNorm.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulRingNorm`。
形式化陈述：toFun_eq_coe (p : MulRingNorm R) : p.toFun = p
参数：p : MulRingNorm R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (p : MulRingNorm R) : p.toFun = p := rfl

@[ext]
/-
**MulRingNorm.ext** 是 Mathlib 中的一个定理，位于命名空间 `MulRingNorm`。
形式化陈述：ext {p q : MulRingNorm R} : (forall x, p x = q x) -> p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {p q : MulRingNorm R} : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

variable (R)
variable [DecidableEq R] [NoZeroDivisors R] [Nontrivial R]

/-- The trivial norm on a ring `R` is the `MulRingNorm` taking value `0` at `0` and `1` at every
other element. -/
/-
**MulRingNorm.** 是 Mathlib 中的一个实例，位于命名空间 `MulRingNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial norm on a ring `R` is the `MulRingNorm` taking value `0` at `0` and 
`1` at every
other element.
-/
instance : One (MulRingNorm R) :=
  ⟨{ (1 : MulRingSeminorm R), (1 : AddGroupNorm R) with }⟩

@[simp]
/-
**MulRingNorm.apply_one** 是 Mathlib 中的一个定理，位于命名空间 `MulRingNorm`。
形式化陈述：apply_one (x : R) : (1 : MulRingNorm R) x = if x = 0 then 0 else 1
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_one (x : R) : (1 : MulRingNorm R) x = if x = 0 then 0 else 1 :=
  rfl
/-
**MulRingNorm.** 是 Mathlib 中的一个实例，位于命名空间 `MulRingNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (MulRingNorm R) :=
  ⟨1⟩

section MulRingNorm_equiv_AbsoluteValue

variable {R : Type*} [Ring R] [Nontrivial R]

/-- The equivalence of `MulRingNorm R` and `AbsoluteValue R ℝ` when `R` is a nontrivial ring. -/
/-
**MulRingNorm.mulRingNormEquivAbsoluteValue** 是 Mathlib 中的一个定义，位于命名空间 `MulRingNo
rm`。
形式化陈述：mulRingNormEquivAbsoluteValue : MulRingNorm R ≃ AbsoluteValue R Real where
 toFun N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of `MulRingNorm R` and `AbsoluteValue R ℝ` when `R` is a nontriv
ial ring.
-/
def mulRingNormEquivAbsoluteValue : MulRingNorm R ≃ AbsoluteValue R ℝ where
  toFun N := {
    toFun := N.toFun
    map_mul' := N.map_mul'
    nonneg' := apply_nonneg N
    eq_zero' x := ⟨N.eq_zero_of_map_eq_zero' x, fun h ↦ h ▸ N.map_zero'⟩
    add_le' := N.add_le'
  }
  invFun v := {
    toFun := v.toFun
    map_zero' := (v.eq_zero' 0).mpr rfl
    add_le' := v.add_le'
    neg' := v.map_neg
    map_one' := v.map_one
    map_mul' := v.map_mul'
    eq_zero_of_map_eq_zero' x := (v.eq_zero' x).mp
  }
  left_inv N := by constructor
  right_inv v := by ext1 x; simp
/-
**MulRingNorm.mulRingNormEquivAbsoluteValue_apply** 是 Mathlib 中的一个引理，位于命名空间 `Mul
RingNorm`。
形式化陈述：mulRingNormEquivAbsoluteValue_apply (N : MulRingNorm R) (x : R) : mulRingN
ormEquivAbsoluteValue N x = N x
参数：N : MulRingNorm R；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulRingNormEquivAbsoluteValue_apply (N : MulRingNorm R) (x : R) :
    mulRingNormEquivAbsoluteValue N x = N x := rfl
/-
**MulRingNorm.mulRingNormEquivAbsoluteValue_symm_apply** 是 Mathlib 中的一个引理，位于命名空间
 `MulRingNorm`。
形式化陈述：mulRingNormEquivAbsoluteValue_symm_apply (v : AbsoluteValue R Real) (x : R
) : mulRingNormEquivAbsoluteValue.symm v x = v x
参数：v : AbsoluteValue R Real；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma mulRingNormEquivAbsoluteValue_symm_apply (v : AbsoluteValue R ℝ) (x : R) :
    mulRingNormEquivAbsoluteValue.symm v x = v x := rfl

end MulRingNorm_equiv_AbsoluteValue

end MulRingNorm

/-- A nonzero ring seminorm on a field `K` is a ring norm. -/
/-
**RingSeminorm.toRingNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingSeminorm.toRingNorm {K : Type*} [Field K] (f : RingSeminorm K) (hnt : 
f != 0) : RingNorm K
参数：f : RingSeminorm K；hnt : f != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonzero ring seminorm on a field `K` is a ring norm.
-/
def RingSeminorm.toRingNorm {K : Type*} [Field K] (f : RingSeminorm K) (hnt : f ≠ 0) :
    RingNorm K :=
  { f with
    eq_zero_of_map_eq_zero' := fun x hx => by
      obtain ⟨c, hc⟩ := RingSeminorm.ne_zero_iff.mp hnt
      by_contra hn0
      have hc0 : f c = 0 := by
        rw [← mul_one c, ← mul_inv_cancel₀ hn0, ← mul_assoc, mul_comm c, mul_assoc]
        exact
          le_antisymm
            (le_trans (map_mul_le_mul f _ _)
              (by rw [← RingSeminorm.toFun_eq_coe, ← AddGroupSeminorm.toFun_eq_coe, hx,
                zero_mul]))
            (apply_nonneg f _)
      exact hc hc0 }

/-- The norm of a `NonUnitalNormedRing` as a `RingNorm`. -/
@[simps!]
/-
**normRingNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：normRingNorm (R : Type*) [NonUnitalNormedRing R] : RingNorm R
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm of a `NonUnitalNormedRing` as a `RingNorm`.
-/
def normRingNorm (R : Type*) [NonUnitalNormedRing R] : RingNorm R :=
  { normAddGroupNorm R, normRingSeminorm R with }

open Int

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The seminorm on a `SeminormedRing`, as a `RingSeminorm`. -/
/-
**SeminormedRing.toRingSeminorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SeminormedRing.toRingSeminorm (R : Type*) [SeminormedRing R] : RingSeminor
m R where toFun
参数：R : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedRing.norm_mul_le`：∀ {α : Type u_5} [self : SeminormedRing α] (
a b : α), ‖a * b‖ ≤ ‖a‖ * ‖b‖

--- 原说明 ---
The seminorm on a `SeminormedRing`, as a `RingSeminorm`.
-/
def SeminormedRing.toRingSeminorm (R : Type*) [SeminormedRing R] : RingSeminorm R where
  toFun     := norm
  map_zero' := norm_zero
  add_le'   := norm_add_le
  mul_le'   := norm_mul_le
  neg'      := norm_neg

@[simp]
/-
**SeminormedRing.toRingSeminorm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeminormedRing.toRingSeminorm_apply (R : Type*) [SeminormedRing R] (x : R)
 : (SeminormedRing.toRingSeminorm R) x = ‖x‖
参数：R : Type*；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SeminormedRing.toRingSeminorm_apply (R : Type*) [SeminormedRing R] (x : R) :
    (SeminormedRing.toRingSeminorm R) x = ‖x‖ :=
  rfl

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The norm on a `NormedRing`, as a `RingNorm`. -/
@[simps]
/-
**NormedRing.toRingNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NormedRing.toRingNorm (R : Type*) [NormedRing R] : RingNorm R where toFun
参数：R : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NormedRing.norm_mul_le`：∀ {α : Type u_5} [self : NormedRing α] (a b : α)
, ‖a * b‖ ≤ ‖a‖ * ‖b‖

--- 原说明 ---
The norm on a `NormedRing`, as a `RingNorm`.
-/
def NormedRing.toRingNorm (R : Type*) [NormedRing R] : RingNorm R where
  toFun     := norm
  map_zero' := norm_zero
  add_le'   := norm_add_le
  mul_le'   := norm_mul_le
  neg'      := norm_neg
  eq_zero_of_map_eq_zero' x hx := by rw [← norm_eq_zero]; exact hx

@[simp]
/-
**NormedRing.toRingNorm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedRing.toRingNorm_apply (R : Type*) [NormedRing R] (x : R) : (NormedRi
ng.toRingNorm R) x = ‖x‖
参数：R : Type*；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NormedRing.toRingNorm_apply (R : Type*) [NormedRing R] (x : R) :
    (NormedRing.toRingNorm R) x = ‖x‖ :=
  rfl

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The norm on a `NormedField`, as a `MulRingNorm`. -/
/-
**NormedField.toMulRingNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NormedField.toMulRingNorm (R : Type*) [NormedField R] : MulRingNorm R wher
e toFun
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm on a `NormedField`, as a `MulRingNorm`.
-/
def NormedField.toMulRingNorm (R : Type*) [NormedField R] : MulRingNorm R where
  toFun     := norm
  map_zero' := norm_zero
  map_one'  := norm_one
  add_le'   := norm_add_le
  map_mul'  := norm_mul
  neg'      := norm_neg
  eq_zero_of_map_eq_zero' x hx := by rw [← norm_eq_zero]; exact hx

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The norm on a `NormedField`, as an `AbsoluteValue`. -/
/-
**NormedField.toAbsoluteValue** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NormedField.toAbsoluteValue (R : Type*) [NormedField R] : AbsoluteValue R 
Real where toFun
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm on a `NormedField`, as an `AbsoluteValue`.
-/
def NormedField.toAbsoluteValue (R : Type*) [NormedField R] : AbsoluteValue R ℝ where
  toFun     := norm
  map_mul'  := norm_mul
  nonneg'   := norm_nonneg
  eq_zero' _ := norm_eq_zero
  add_le'   := norm_add_le
