/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubsemiring
public import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!
# Star subrings

A \*-subring is a subring of a \*-ring which is closed under `*`.
-/

@[expose] public section

universe v

/--
Definition of `StarSubsemiring` / `StarSubsemiring` 的定义

English:
structure StarSubsemiring
  parameters: (R : Type v) [NonAssocSemiring R] [Star R]
  extends: Subsemiring R
  axioms and operations (1):
    - star_mem'({a}) : a in carrier -> star a in carrier

中文:
结构 StarSubsemiring
  参数: (R : 类型v) [NonAssocSemiring R] [Star R]
  继承: Subsemiring R
  公理与运算 (1 个):
    - star_mem'({a}) : a in carrier -> star a in carrier
-/
structure StarSubsemiring (R : Type v) [NonAssocSemiring R] [Star R] : Type v
    extends Subsemiring R where
  /-- The `carrier` of a `StarSubsemiring` is closed under the `star` operation. -/
  star_mem' {a} : a in carrier -> star a in carrier

section StarSubsemiring

namespace StarSubsemiring

/-- Reinterpret a `StarSubsemiring` as a `Subsemiring`. -/
add_decl_doc StarSubsemiring.toSubsemiring

/--
Instance `setLike` / 实例 `setLike`

English:
instance setLike
  signature: {R : Type v} [NonAssocSemiring R] [Star R]
  body: s.carrier
  coe_injective p q h := by obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := p; cases q; congr

中文:
实例 setLike
  签名: {R : 类型v} [NonAssocSemiring R] [Star R]
  定义体: s.carrier
  coe_injective p q h := by obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := p; cases q; congr

Depends on / 依赖: carrier, s.carrier
-/
instance setLike {R : Type v} [NonAssocSemiring R] [Star R] :
    SetLike (StarSubsemiring R) R where
  coe {s} := s.carrier
  coe_injective p q h := by obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := p; cases q; congr

instance {R : Type v} [NonAssocSemiring R] [Star R] : PartialOrder (StarSubsemiring R) :=
  .ofSetLike (StarSubsemiring R) R

initialize_simps_projections StarSubsemiring (carrier -> coe, as_prefix coe)

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

/-- The actual `StarSubsemiring` obtained from an element of a `StarSubsemiringClass`. -/
@[simps]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: {S R : Type*} [NonAssocSemiring R] [SetLike S R] [StarRing R] [SubsemiringClass S R]
  body: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  star_mem' := star_mem

中文:
定义 ofClass
  签名: {S R : 类型} [NonAssocSemiring R] [SetLike S R] [StarRing R] [SubsemiringClass S R]
  定义体: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  star_mem' := star_mem
-/
def ofClass {S R : Type*} [NonAssocSemiring R] [SetLike S R] [StarRing R] [SubsemiringClass S R]
    [StarMemClass S R] (s : S) : StarSubsemiring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  star_mem' := star_mem

instance (priority := 100) : CanLift (Set R) (StarSubsemiring R) (↑)
    (fun s => 0 in s ∧ (forall {x y}, x in s -> y in s -> x + y in s) ∧ 1 in s ∧
      (forall {x y}, x in s -> y in s -> x * y in s) ∧ (forall {x}, x in s -> star x in s)) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        one_mem' := h.2.2.1
        mul_mem' := h.2.2.2.1
        star_mem' := h.2.2.2.2 },
      rfl ⟩

/--
Instance `starMemClass` / 实例 `starMemClass`

English:
instance starMemClass
  signature: : StarMemClass (StarSubsemiring R) R where
  body: s.star_mem'

中文:
实例 starMemClass
  签名: : StarMemClass (StarSubsemiring R) R where
  定义体: s.star_mem'

Depends on / 依赖: s.star_mem, star_mem
-/
instance starMemClass : StarMemClass (StarSubsemiring R) R where
  star_mem {s} := s.star_mem'

/--
Instance `subsemiringClass` / 实例 `subsemiringClass`

English:
instance subsemiringClass
  signature: : SubsemiringClass (StarSubsemiring R) R where
  body: s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'
  one_mem {s} := s.one_mem'

中文:
实例 subsemiringClass
  签名: : SubsemiringClass (StarSubsemiring R) R where
  定义体: s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'
  one_mem {s} := s.one_mem'

Depends on / 依赖: add_mem, s.add_mem
-/
instance subsemiringClass : SubsemiringClass (StarSubsemiring R) R where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'
  one_mem {s} := s.one_mem'

-- this uses the `Star` instance `s` inherits from `StarMemClass (StarSubsemiring R A) A`
/--
Instance `starRing` / 实例 `starRing`

English:
instance starRing
  signature: (s : StarSubsemiring R)
  body: { StarMemClass.instStar s with
    star_involutive := fun r => Subtype.ext (star_star (r : R))
    star_mul := fun r₁ r₂ => Subtype.ext (star_mul (r₁ : R) (r₂ : R))
    star_add := fun r₁ r₂ => Subtype.ext (star_add (r₁ : R) (r₂ : R)) }

中文:
实例 starRing
  签名: (s : StarSubsemiring R)
  定义体: { StarMemClass.instStar s with
    star_involutive := fun r => Subtype.ext (star_star (r : R))
    star_mul := fun r₁ r₂ => Subtype.ext (star_mul (r₁ : R) (r₂ : R))
    star_add := fun r₁ r₂ => Subtype.ext (star_add (r₁ : R) (r₂ : R)) }

Depends on / 依赖: StarMemClass, StarMemClass.instStar, Subtype, Subtype.ext, instStar, star_add, star_involutive, star_mul, star_star
-/
instance starRing (s : StarSubsemiring R) : StarRing s :=
  { StarMemClass.instStar s with
    star_involutive := fun r => Subtype.ext (star_star (r : R))
    star_mul := fun r₁ r₂ => Subtype.ext (star_mul (r₁ : R) (r₂ : R))
    star_add := fun r₁ r₂ => Subtype.ext (star_add (r₁ : R) (r₂ : R)) }

/--
Instance `semiring` / 实例 `semiring`

English:
instance semiring
  signature: (s : StarSubsemiring R)
  body: s.toSubsemiring.toNonAssocSemiring

中文:
实例 semiring
  签名: (s : StarSubsemiring R)
  定义体: s.toSubsemiring.toNonAssocSemiring

Depends on / 依赖: s.toSubsemiring.toNonAssocSemiring, toNonAssocSemiring, toSubsemiring
-/
instance semiring (s : StarSubsemiring R) : NonAssocSemiring s :=
  s.toSubsemiring.toNonAssocSemiring

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : StarSubsemiring R} {x : R}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

@[ext]

中文:
定理 mem_carrier
  条件: {s : StarSubsemiring R} {x : R}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

@[ext]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : StarSubsemiring R} {x : R} : x in s.carrier ↔ x in s :=
  Iff.rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : StarSubsemiring R} (h : forall x : R, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

@[simp]

中文:
定理 ext
  条件: {S T : StarSubsemiring R} (h : 对任意 x : R, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

@[simp]

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : StarSubsemiring R} (h : forall x : R, x in S ↔ x in T) : S = T :=
  SetLike.ext h

@[simp]
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (S : Subsemiring R) (h)
  statement: ((⟨S, h⟩ : StarSubsemiring R) : Set R) = S
  proof: rfl

@[simp]

中文:
引理 coe_mk
  条件: (S : Subsemiring R) (h)
  结论: ((⟨S, h⟩ : StarSubsemiring R) : Set R) = S
  证明: rfl

@[simp]
-/
lemma coe_mk (S : Subsemiring R) (h) : ((⟨S, h⟩ : StarSubsemiring R) : Set R) = S := rfl

@[simp]
/--
theorem `mem_toSubsemiring` / 定理 `mem_toSubsemiring`

English:
theorem mem_toSubsemiring
  given: {S : StarSubsemiring R} {x}
  statement: x in S.toSubsemiring ↔ x in S
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toSubsemiring
  条件: {S : StarSubsemiring R} {x}
  结论: x in S.toSubsemiring ↔ x in S
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubsemiring {S : StarSubsemiring R} {x} : x in S.toSubsemiring ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `coe_toSubsemiring` / 定理 `coe_toSubsemiring`

English:
theorem coe_toSubsemiring
  given: (S : StarSubsemiring R)
  statement: (S.toSubsemiring : Set R) = S
  proof: rfl

中文:
定理 coe_toSubsemiring
  条件: (S : StarSubsemiring R)
  结论: (S.toSubsemiring : Set R) = S
  证明: rfl
-/
theorem coe_toSubsemiring (S : StarSubsemiring R) : (S.toSubsemiring : Set R) = S :=
  rfl

/--
theorem `toSubsemiring_injective` / 定理 `toSubsemiring_injective`

English:
theorem toSubsemiring_injective
  proof: fun S T h =>
  ext fun x => by rw [← mem_toSubsemiring, ← mem_toSubsemiring, h]

中文:
定理 toSubsemiring_injective
  证明: fun S T h =>
  ext fun x => by rw [← mem_toSubsemiring, ← mem_toSubsemiring, h]
-/
theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : StarSubsemiring R -> Subsemiring R) := fun S T h =>
  ext fun x => by rw [← mem_toSubsemiring, ← mem_toSubsemiring, h]

/--
theorem `toSubsemiring_inj` / 定理 `toSubsemiring_inj`

English:
theorem toSubsemiring_inj
  given: {S U : StarSubsemiring R}
  statement: S.toSubsemiring = U.toSubsemiring ↔ S = U
  proof: toSubsemiring_injective.eq_iff

中文:
定理 toSubsemiring_inj
  条件: {S U : StarSubsemiring R}
  结论: S.toSubsemiring = U.toSubsemiring ↔ S = U
  证明: toSubsemiring_injective.eq_iff

Depends on / 依赖: eq_iff, toSubsemiring_injective, toSubsemiring_injective.eq_iff
-/
theorem toSubsemiring_inj {S U : StarSubsemiring R} : S.toSubsemiring = U.toSubsemiring ↔ S = U :=
  toSubsemiring_injective.eq_iff

/--
theorem `toSubsemiring_le_iff` / 定理 `toSubsemiring_le_iff`

English:
theorem toSubsemiring_le_iff
  given: {S₁ S₂ : StarSubsemiring R}
  proof: Iff.rfl

中文:
定理 toSubsemiring_le_iff
  条件: {S₁ S₂ : StarSubsemiring R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toSubsemiring_le_iff {S₁ S₂ : StarSubsemiring R} :
    S₁.toSubsemiring <= S₂.toSubsemiring ↔ S₁ <= S₂ :=
  Iff.rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S)
  body: Subsemiring.copy S.toSubsemiring s hs
  star_mem' := @fun a ha => hs ▸ (S.star_mem' (by simpa [hs] using ha) : star a in (S : Set R))

@[simp, norm_cast]

中文:
定义 copy
  签名: (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S)
  定义体: Subsemiring.copy S.toSubsemiring s hs
  star_mem' := @fun a ha => hs ▸ (S.star_mem' (by simpa [hs] using ha) : star a in (S : Set R))

@[simp, norm_cast]
-/
protected def copy (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : StarSubsemiring R where
  toSubsemiring := Subsemiring.copy S.toSubsemiring s hs
  star_mem' := @fun a ha => hs ▸ (S.star_mem' (by simpa [hs] using ha) : star a in (S : Set R))

@[simp, norm_cast]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S)
  statement: (S.copy s hs : Set R) = s
  proof: rfl

中文:
定理 coe_copy
  条件: (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S)
  结论: (S.copy s hs : Set R) = s
  证明: rfl
-/
theorem coe_copy (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

section Center

variable (R)

/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: (R) [NonAssocSemiring R] [StarRing R]
  body: Subsemiring.center R
  star_mem' := Set.star_mem_center

中文:
定义 center
  签名: (R) [NonAssocSemiring R] [StarRing R]
  定义体: Subsemiring.center R
  star_mem' := Set.star_mem_center

Depends on / 依赖: Subsemiring, Subsemiring.center, center
-/
def center (R) [NonAssocSemiring R] [StarRing R] : StarSubsemiring R where
  toSubsemiring := Subsemiring.center R
  star_mem' := Set.star_mem_center

end Center

end StarSubsemiring

end StarSubsemiring
section SubStarSemigroup

variable (A) [Mul A] [StarMul A]

namespace SubStarSemigroup

/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: : SubStarSemigroup A
  body: { Subsemigroup.center A with
    star_mem' := Set.star_mem_center }

中文:
定义 center
  签名: : SubStarSemigroup A
  定义体: { Subsemigroup.center A with
    star_mem' := Set.star_mem_center }

Depends on / 依赖: Set.star_mem_center, Subsemigroup, Subsemigroup.center, center, star_mem, star_mem_center
-/
def center : SubStarSemigroup A :=
  { Subsemigroup.center A with
    star_mem' := Set.star_mem_center }

end SubStarSemigroup

end SubStarSemigroup
