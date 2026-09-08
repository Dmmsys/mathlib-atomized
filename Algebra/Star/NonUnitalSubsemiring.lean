/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Basic
public import Mathlib.RingTheory.NonUnitalSubsemiring.Basic
public import Mathlib.Algebra.Star.Center

/-!
# Non-unital Star Subsemirings

In this file we define `NonUnitalStarSubsemiring`s and the usual operations on them.

## Implementation

This file is heavily inspired by `Mathlib/Algebra/Star/NonUnitalSubalgebra.lean`.

-/

@[expose] public section

universe v w w'

variable {A : Type v} {B : Type w} {C : Type w'}

/-- A sub star semigroup is a subset of a magma which is closed under the `star`. -/
/-
**SubStarSemigroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type v) → [Mul M] → [Star M] → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sub star semigroup is a subset of a magma which is closed under the `star`.
-/
structure SubStarSemigroup (M : Type v) [Mul M] [Star M] : Type v
    extends Subsemigroup M where
  /-- The `carrier` of a `StarSubset` is closed under the `star` operation. -/
  star_mem' : ∀ {a : M} (_ha : a ∈ carrier), star a ∈ carrier

/-- Reinterpret a `SubStarSemigroup` as a `Subsemigroup`. -/
add_decl_doc SubStarSemigroup.toSubsemigroup

/-- A non-unital star subsemiring is a non-unital subsemiring which also is closed under the
`star` operation. -/
/-
**NonUnitalStarSubsemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type v) → [NonUnitalNonAssocSemiring R] → [Star R] → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital star subsemiring is a non-unital subsemiring which also is closed u
nder the
`star` operation.
-/
structure NonUnitalStarSubsemiring (R : Type v) [NonUnitalNonAssocSemiring R] [Star R] : Type v
    extends NonUnitalSubsemiring R where
  /-- The `carrier` of a `NonUnitalStarSubsemiring` is closed under the `star` operation. -/
  star_mem' : ∀ {a : R} (_ha : a ∈ carrier), star a ∈ carrier

/-- Reinterpret a `NonUnitalStarSubsemiring` as a `NonUnitalSubsemiring`. -/
add_decl_doc NonUnitalStarSubsemiring.toNonUnitalSubsemiring

section NonUnitalStarSubsemiring

namespace NonUnitalStarSubsemiring

/-
**NonUnitalStarSubsemiring.instSetLike** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarS
ubsemiring`。
形式化陈述：instSetLike {R : Type v} [NonUnitalNonAssocSemiring R] [Star R] : SetLike 
(NonUnitalStarSubsemiring R) R where coe {s}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSetLike {R : Type v} [NonUnitalNonAssocSemiring R] [Star R] :
    SetLike (NonUnitalStarSubsemiring R) R where
  coe {s} := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

initialize_simps_projections NonUnitalStarSubsemiring (carrier → coe, as_prefix coe)

variable {R : Type v} [NonUnitalNonAssocSemiring R] [StarRing R]

/-- The actual `NonUnitalStarSubsemiring` obtained from an element of a type satisfying
`NonUnitalSubsemiringClass` and `StarMemClass`. -/
@[simps]
/-
**NonUnitalStarSubsemiring.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarSubse
miring`。
形式化陈述：ofClass {S R : Type*} [NonUnitalNonAssocSemiring R] [StarRing R] [SetLike 
S R] [NonUnitalSubsemiringClass S R] [StarMemClass S R] (s : S) : NonUnitalStarS
ubsemiring R where carrier
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The actual `NonUnitalStarSubsemiring` obtained from an element of a type satisfy
ing
`NonUnitalSubsemiringClass` and `StarMemClass`.
-/
def ofClass {S R : Type*} [NonUnitalNonAssocSemiring R] [StarRing R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] [StarMemClass S R] (s : S) : NonUnitalStarSubsemiring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  star_mem' := star_mem
/-
**NonUnitalStarSubsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarSubsemiring`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CanLift (Set R) (NonUnitalStarSubsemiring R) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧
      ∀ {x}, x ∈ s → star x ∈ s)
    where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        mul_mem' := h.2.2.1
        star_mem' := h.2.2.2 },
      rfl ⟩
/-
**NonUnitalStarSubsemiring.instNonUnitalSubsemiringClass** 是 Mathlib 中的一个实例，位于命名
空间 `NonUnitalStarSubsemiring`。
形式化陈述：instNonUnitalSubsemiringClass : NonUnitalSubsemiringClass (NonUnitalStarSu
bsemiring R) R where add_mem {s}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubsemigroup.add_mem'`：∀ {M : Type u_3} [inst : Add M] (self : AddSub
semigroup M) {a b : M},   a ∈ self.carrier → b ∈ self.carrier → a + b ∈ self.car
rier
· 使用定理 `AddSubmonoid.zero_mem'`：∀ {M : Type u_3} [inst : AddZeroClass M] (self :
 AddSubmonoid M), 0 ∈ self.carrier
· 使用定理 `NonUnitalSubsemiring.mul_mem'`：∀ {R : Type u} [inst : NonUnitalNonAssocS
emiring R] (self : NonUnitalSubsemiring R) {a b : R},   a ∈ self.carrier → b ∈ s
elf.carrier → a * b…
-/
instance instNonUnitalSubsemiringClass :
    NonUnitalSubsemiringClass (NonUnitalStarSubsemiring R) R where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'
/-
**NonUnitalStarSubsemiring.instStarMemClass** 是 Mathlib 中的一个实例，位于命名空间 `NonUnital
StarSubsemiring`。
形式化陈述：instStarMemClass : StarMemClass (NonUnitalStarSubsemiring R) R where star_
mem {s}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubsemiring.star_mem'`：∀ {R : Type v} [inst : NonUnitalNonA
ssocSemiring R] [inst_1 : Star R] (self : NonUnitalStarSubsemiring R) {a : R},  
 a ∈ self.carrier → star…
-/
instance instStarMemClass : StarMemClass (NonUnitalStarSubsemiring R) R where
  star_mem {s} := s.star_mem'
/-
**NonUnitalStarSubsemiring.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarS
ubsemiring`。
形式化陈述：mem_carrier {s : NonUnitalStarSubsemiring R} {x : R} : x in s.carrier ↔ x 
in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : NonUnitalStarSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/-- Copy of a non-unital star subsemiring with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
/-
**NonUnitalStarSubsemiring.copy** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarSubsemir
ing`。
形式化陈述：{R : Type v} →   [inst : NonUnitalNonAssocSemiring R] →     [inst_1 : Star
Ring R] → (S : NonUnitalStarSubsemiring R) → (s : Set R) → s = ↑S → NonUnitalSta
rSubsemiring R
参数：S : NonUnitalStarSubsemiring R；s : Set R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a non-unital star subsemiring with a new `carrier` equal to the old one.
Useful to fix definitional equalities.
-/
protected def copy (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    NonUnitalStarSubsemiring R :=
  { S.toNonUnitalSubsemiring.copy s hs with
    star_mem' := fun {x} (hx : x ∈ s) => by
      change star x ∈ s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp, norm_cast]
/-
**NonUnitalStarSubsemiring.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubs
emiring`。
形式化陈述：coe_copy (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) : (S.c
opy s hs : Set R) = s
参数：S : NonUnitalStarSubsemiring R；s : Set R；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    (S.copy s hs : Set R) = s :=
  rfl
/-
**NonUnitalStarSubsemiring.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubse
miring`。
形式化陈述：copy_eq (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.cop
y s hs = S
参数：S : NonUnitalStarSubsemiring R；s : Set R；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

section Center

variable (R)

/-- The center of a non-unital non-associative semiring `R` is the set of elements that
commute and associate with everything in `R`, here realized as a non-unital star
subsemiring. -/
/-
**NonUnitalStarSubsemiring.center** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarSubsem
iring`。
形式化陈述：center (R) [NonUnitalNonAssocSemiring R] [StarRing R] : NonUnitalStarSubse
miring R where toNonUnitalSubsemiring
参数：R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a non-unital non-associative semiring `R` is the set of elements t
hat
commute and associate with everything in `R`, here realized as a non-unital star
subsemiring.
-/
def center (R) [NonUnitalNonAssocSemiring R] [StarRing R] : NonUnitalStarSubsemiring R where
  toNonUnitalSubsemiring := NonUnitalSubsemiring.center R
  star_mem' := Set.star_mem_center

end Center

end NonUnitalStarSubsemiring

end NonUnitalStarSubsemiring

