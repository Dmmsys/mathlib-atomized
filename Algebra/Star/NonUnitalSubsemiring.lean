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

/--
Definition of `SubStarSemigroup` / `SubStarSemigroup` 的定义

English:
structure SubStarSemigroup
  parameters: (M : Type v) [Mul M] [Star M]
  extends: Subsemigroup M
  axioms and operations (1):
    - star_mem' : forall {a : M} (_ha : a in carrier), star a in carrier

中文:
结构 SubStar半群
  参数: (M : 类型v) [乘法 M] [对合 M]
  继承: 子半群 M
  公理与运算 (1 个):
    - star_mem' : 对任意 {a : M} (_ha : a in carrier), star a in carrier

Depends on / 依赖: Equation, eval_map, map_polynomial, map_zero
-/
structure SubStarSemigroup (M : Type v) [Mul M] [Star M] : Type v
    extends Subsemigroup M where
  /-- The `carrier` of a `StarSubset` is closed under the `star` operation. -/
  star_mem' : forall {a : M} (_ha : a in carrier), star a in carrier

/-- Reinterpret a `SubStarSemigroup` as a `Subsemigroup`. -/
add_decl_doc SubStarSemigroup.toSubsemigroup

/--
Definition of `NonUnitalStarSubsemiring` / `NonUnitalStarSubsemiring` 的定义

English:
structure NonUnitalStarSubsemiring
  parameters: (R : Type v) [NonUnitalNonAssocSemiring R] [Star R]
  extends: NonUnitalSubsemiring R
  axioms and operations (1):
    - star_mem' : forall {a : R} (_ha : a in carrier), star a in carrier

中文:
结构 非幺对合子半环
  参数: (R : 类型v) [非幺非结合半环 R] [对合 R]
  继承: NonUnital子半环 R
  公理与运算 (1 个):
    - star_mem' : 对任意 {a : R} (_ha : a in carrier), star a in carrier
-/
structure NonUnitalStarSubsemiring (R : Type v) [NonUnitalNonAssocSemiring R] [Star R] : Type v
    extends NonUnitalSubsemiring R where
  /-- The `carrier` of a `NonUnitalStarSubsemiring` is closed under the `star` operation. -/
  star_mem' : forall {a : R} (_ha : a in carrier), star a in carrier

/-- Reinterpret a `NonUnitalStarSubsemiring` as a `NonUnitalSubsemiring`. -/
add_decl_doc NonUnitalStarSubsemiring.toNonUnitalSubsemiring

section NonUnitalStarSubsemiring

namespace NonUnitalStarSubsemiring

/--
Instance `instSetLike` / 实例 `instSetLike`

English:
instance instSetLike
  signature: {R : Type v} [NonUnitalNonAssocSemiring R] [Star R]
  body: s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

initialize_simps_projections NonUnitalStarSubsemiring (carrier -> coe, as_prefix coe)

中文:
实例 instSetLike
  签名: {R : 类型v} [非幺非结合半环 R] [对合 R]
  定义体: s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

initialize_simps_projections NonUnitalStarSubsemiring (carrier -> coe, as_prefix coe)

Depends on / 依赖: carrier, s.carrier
-/
instance instSetLike {R : Type v} [NonUnitalNonAssocSemiring R] [Star R] :
    SetLike (NonUnitalStarSubsemiring R) R where
  coe {s} := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

initialize_simps_projections NonUnitalStarSubsemiring (carrier -> coe, as_prefix coe)

variable {R : Type v} [NonUnitalNonAssocSemiring R] [StarRing R]

/-- The actual `NonUnitalStarSubsemiring` obtained from an element of a type satisfying
`NonUnitalSubsemiringClass` and `StarMemClass`. -/
@[simps]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: {S R : Type*} [NonUnitalNonAssocSemiring R] [StarRing R] [SetLike S R]
  body: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  star_mem' := star_mem

中文:
定义 ofClass
  签名: {S R : 类型} [非幺非结合半环 R] [对合环 R] [集合状 S R]
  定义体: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  star_mem' := star_mem
-/
def ofClass {S R : Type*} [NonUnitalNonAssocSemiring R] [StarRing R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] [StarMemClass S R] (s : S) : NonUnitalStarSubsemiring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  star_mem' := star_mem

instance (priority := 100) : CanLift (Set R) (NonUnitalStarSubsemiring R) (↑)
    (fun s => 0 in s ∧ (forall {x y}, x in s -> y in s -> x + y in s) ∧ (forall {x y}, x in s -> y in s -> x * y in s) ∧
      forall {x}, x in s -> star x in s)
    where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        mul_mem' := h.2.2.1
        star_mem' := h.2.2.2 },
      rfl ⟩

/--
Instance `instNonUnitalSubsemiringClass` / 实例 `instNonUnitalSubsemiringClass`

English:
instance instNonUnitalSubsemiringClass
  signature: :
  body: s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'

中文:
实例 instNonUnitalSubsemiringClass
  签名: :
  定义体: s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'

Depends on / 依赖: add_mem, s.add_mem
-/
instance instNonUnitalSubsemiringClass :
    NonUnitalSubsemiringClass (NonUnitalStarSubsemiring R) R where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'

/--
Instance `instStarMemClass` / 实例 `instStarMemClass`

English:
instance instStarMemClass
  signature: : StarMemClass (NonUnitalStarSubsemiring R) R where
  body: s.star_mem'

中文:
实例 instStarMemClass
  签名: : StarMem类 (非幺对合子半环 R) R where
  定义体: s.star_mem'

Depends on / 依赖: s.star_mem, star_mem
-/
instance instStarMemClass : StarMemClass (NonUnitalStarSubsemiring R) R where
  star_mem {s} := s.star_mem'

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : NonUnitalStarSubsemiring R} {x : R}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

中文:
定理 mem_carrier
  条件: {s : 非幺对合子半环 R} {x : R}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : NonUnitalStarSubsemiring R} {x : R} : x in s.carrier ↔ x in s :=
  Iff.rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S)
  body: { S.toNonUnitalSubsemiring.copy s hs with
    star_mem' := fun {x} (hx : x in s) => by
      change star x in s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp, norm_cast]

中文:
定义 copy
  签名: (S : 非幺对合子半环 R) (s : 集合 R) (hs : s = ↑S)
  定义体: { S.toNonUnitalSubsemiring.copy s hs with
    star_mem' := fun {x} (hx : x in s) => by
      change star x in s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp, norm_cast]
-/
protected def copy (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    NonUnitalStarSubsemiring R :=
  { S.toNonUnitalSubsemiring.copy s hs with
    star_mem' := fun {x} (hx : x in s) => by
      change star x in s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp, norm_cast]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S)
  proof: rfl

中文:
定理 coe_copy
  条件: (S : 非幺对合子半环 R) (s : 集合 R) (hs : s = ↑S)
  证明: rfl

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, Equation, Equation.map, convert, f.toRingHom, map_baseChange, toRingHom, toRingHom_eq_coe
-/
theorem coe_copy (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    (S.copy s hs : Set R) = s :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: (S : 非幺对合子半环 R) (s : 集合 R) (hs : s = ↑S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

section Center

variable (R)

/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: (R) [NonUnitalNonAssocSemiring R] [StarRing R]
  body: NonUnitalSubsemiring.center R
  star_mem' := Set.star_mem_center

中文:
定义 center
  签名: (R) [非幺非结合半环 R] [对合环 R]
  定义体: NonUnitalSubsemiring.center R
  star_mem' := Set.star_mem_center

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.center, center
-/
def center (R) [NonUnitalNonAssocSemiring R] [StarRing R] : NonUnitalStarSubsemiring R where
  toNonUnitalSubsemiring := NonUnitalSubsemiring.center R
  star_mem' := Set.star_mem_center

end Center

end NonUnitalStarSubsemiring

end NonUnitalStarSubsemiring
