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

/-- A (unital) star subsemiring is a non-associative ring which is closed under the `star`
operation. -/
/-
**StarSubsemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type v) → [NonAssocSemiring R] → [Star R] → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (unital) star subsemiring is a non-associative ring which is closed under the 
`star`
operation.
-/
structure StarSubsemiring (R : Type v) [NonAssocSemiring R] [Star R] : Type v
    extends Subsemiring R where
  /-- The `carrier` of a `StarSubsemiring` is closed under the `star` operation. -/
  star_mem' {a} : a ∈ carrier → star a ∈ carrier

section StarSubsemiring

namespace StarSubsemiring

/-- Reinterpret a `StarSubsemiring` as a `Subsemiring`. -/
add_decl_doc StarSubsemiring.toSubsemiring

/-
**StarSubsemiring.setLike** 是 Mathlib 中的一个实例，位于命名空间 `StarSubsemiring`。
形式化陈述：setLike {R : Type v} [NonAssocSemiring R] [Star R] : SetLike (StarSubsemir
ing R) R where coe {s}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance setLike {R : Type v} [NonAssocSemiring R] [Star R] :
    SetLike (StarSubsemiring R) R where
  coe {s} := s.carrier
  coe_injective p q h := by obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := p; cases q; congr
/-
**StarSubsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `StarSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type v} [NonAssocSemiring R] [Star R] : PartialOrder (StarSubsemiring R) :=
  .ofSetLike (StarSubsemiring R) R

initialize_simps_projections StarSubsemiring (carrier → coe, as_prefix coe)

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

/-- The actual `StarSubsemiring` obtained from an element of a `StarSubsemiringClass`. -/
@[simps]
/-
**StarSubsemiring.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `StarSubsemiring`。
形式化陈述：ofClass {S R : Type*} [NonAssocSemiring R] [SetLike S R] [StarRing R] [Sub
semiringClass S R] [StarMemClass S R] (s : S) : StarSubsemiring R where carrier
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The actual `StarSubsemiring` obtained from an element of a `StarSubsemiringClass
`.
-/
def ofClass {S R : Type*} [NonAssocSemiring R] [SetLike S R] [StarRing R] [SubsemiringClass S R]
    [StarMemClass S R] (s : S) : StarSubsemiring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  star_mem' := star_mem
/-
**StarSubsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `StarSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CanLift (Set R) (StarSubsemiring R) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ 1 ∈ s ∧
      (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧ (∀ {x}, x ∈ s → star x ∈ s)) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        one_mem' := h.2.2.1
        mul_mem' := h.2.2.2.1
        star_mem' := h.2.2.2.2 },
      rfl ⟩
/-
**StarSubsemiring.starMemClass** 是 Mathlib 中的一个实例，位于命名空间 `StarSubsemiring`。
形式化陈述：starMemClass : StarMemClass (StarSubsemiring R) R where star_mem {s}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubsemiring.star_mem'`：∀ {R : Type v} [inst : NonAssocSemiring R] [i
nst_1 : Star R] (self : StarSubsemiring R) {a : R},   a ∈ self.carrier → star a 
∈ self.carrier
-/
instance starMemClass : StarMemClass (StarSubsemiring R) R where
  star_mem {s} := s.star_mem'
/-
**StarSubsemiring.subsemiringClass** 是 Mathlib 中的一个实例，位于命名空间 `StarSubsemiring`。
形式化陈述：subsemiringClass : SubsemiringClass (StarSubsemiring R) R where add_mem {s
}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.mul_mem'`：∀ {M : Type u_3} [inst : Mul M] (self : Subsemigr
oup M) {a b : M},   a ∈ self.carrier → b ∈ self.carrier → a * b ∈ self.carrier
· 使用定理 `Submonoid.one_mem'`：∀ {M : Type u_3} [inst : MulOneClass M] (self : Subm
onoid M), 1 ∈ self.carrier
· 使用定理 `Subsemiring.add_mem'`：∀ {R : Type u} [inst : NonAssocSemiring R] (self :
 Subsemiring R) {a b : R},   a ∈ self.carrier → b ∈ self.carrier → a + b ∈ self.
carrier
· 使用定理 `Subsemiring.zero_mem'`：∀ {R : Type u} [inst : NonAssocSemiring R] (self 
: Subsemiring R), 0 ∈ self.carrier
-/
instance subsemiringClass : SubsemiringClass (StarSubsemiring R) R where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'
  one_mem {s} := s.one_mem'

-- this uses the `Star` instance `s` inherits from `StarMemClass (StarSubsemiring R A) A`
/-
**StarSubsemiring.starRing** 是 Mathlib 中的一个实例，位于命名空间 `StarSubsemiring`。
形式化陈述：starRing (s : StarSubsemiring R) : StarRing s
参数：s : StarSubsemiring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance starRing (s : StarSubsemiring R) : StarRing s :=
  { StarMemClass.instStar s with
    star_involutive := fun r => Subtype.ext (star_star (r : R))
    star_mul := fun r₁ r₂ => Subtype.ext (star_mul (r₁ : R) (r₂ : R))
    star_add := fun r₁ r₂ => Subtype.ext (star_add (r₁ : R) (r₂ : R)) }
/-
**StarSubsemiring.semiring** 是 Mathlib 中的一个实例，位于命名空间 `StarSubsemiring`。
形式化陈述：semiring (s : StarSubsemiring R) : NonAssocSemiring s
参数：s : StarSubsemiring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semiring (s : StarSubsemiring R) : NonAssocSemiring s :=
  s.toSubsemiring.toNonAssocSemiring
/-
**StarSubsemiring.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `StarSubsemiring`。
形式化陈述：mem_carrier {s : StarSubsemiring R} {x : R} : x in s.carrier ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : StarSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[ext]
/-
**StarSubsemiring.ext** 是 Mathlib 中的一个定理，位于命名空间 `StarSubsemiring`。
形式化陈述：ext {S T : StarSubsemiring R} (h : forall x : R, x in S ↔ x in T) : S = T
参数：h : forall x : R, x in S ↔ x in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext {S T : StarSubsemiring R} (h : ∀ x : R, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
/-
**StarSubsemiring.coe_mk** 是 Mathlib 中的一个引理，位于命名空间 `StarSubsemiring`。
形式化陈述：coe_mk (S : Subsemiring R) (h) : ((⟨S, h⟩ : StarSubsemiring R) : Set R) = 
S
参数：S : Subsemiring R；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk (S : Subsemiring R) (h) : ((⟨S, h⟩ : StarSubsemiring R) : Set R) = S := rfl

@[simp]
/-
**StarSubsemiring.mem_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `StarSubsemiring`。
形式化陈述：mem_toSubsemiring {S : StarSubsemiring R} {x} : x in S.toSubsemiring ↔ x i
n S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubsemiring {S : StarSubsemiring R} {x} : x ∈ S.toSubsemiring ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**StarSubsemiring.coe_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `StarSubsemiring`。
形式化陈述：coe_toSubsemiring (S : StarSubsemiring R) : (S.toSubsemiring : Set R) = S
参数：S : StarSubsemiring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubsemiring (S : StarSubsemiring R) : (S.toSubsemiring : Set R) = S :=
  rfl
/-
**StarSubsemiring.toSubsemiring_injective** 是 Mathlib 中的一个定理，位于命名空间 `StarSubsemi
ring`。
形式化陈述：toSubsemiring_injective : Function.Injective (toSubsemiring : StarSubsemir
ing R -> Subsemiring R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubsemiring.ext`：ext {S T : StarSubsemiring R} (h : forall x : R, x 
in S ↔ x in T) : S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StarSubsemiring.mem_toSubsemiring`：mem_toSubsemiring {S : StarSubsemirin
g R} {x} : x in S.toSubsemiring ↔ x in S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : StarSubsemiring R → Subsemiring R) := fun S T h =>
  ext fun x => by rw [← mem_toSubsemiring, ← mem_toSubsemiring, h]
/-
**StarSubsemiring.toSubsemiring_inj** 是 Mathlib 中的一个定理，位于命名空间 `StarSubsemiring`。
形式化陈述：toSubsemiring_inj {S U : StarSubsemiring R} : S.toSubsemiring = U.toSubsem
iring ↔ S = U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StarSubsemiring.toSubsemiring_injective`：toSubsemiring_injective : Funct
ion.Injective (toSubsemiring : StarSubsemiring R -> Subsemiring R)
-/
theorem toSubsemiring_inj {S U : StarSubsemiring R} : S.toSubsemiring = U.toSubsemiring ↔ S = U :=
  toSubsemiring_injective.eq_iff
/-
**StarSubsemiring.toSubsemiring_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `StarSubsemirin
g`。
形式化陈述：toSubsemiring_le_iff {S₁ S₂ : StarSubsemiring R} : S₁.toSubsemiring <= S₂.
toSubsemiring ↔ S₁ <= S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubsemiring_le_iff {S₁ S₂ : StarSubsemiring R} :
    S₁.toSubsemiring ≤ S₂.toSubsemiring ↔ S₁ ≤ S₂ :=
  Iff.rfl

/-- Copy of a non-unital star subalgebra with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
/-
**StarSubsemiring.copy** 是 Mathlib 中的一个定义，位于命名空间 `StarSubsemiring`。
形式化陈述：{R : Type v} →   [inst : NonAssocSemiring R] →     [inst_1 : StarRing R] →
 (S : StarSubsemiring R) → (s : Set R) → s = ↑S → StarSubsemiring R
参数：S : StarSubsemiring R；s : Set R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a non-unital star subalgebra with a new `carrier` equal to the old one. 
Useful to fix
definitional equalities.
-/
protected def copy (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : StarSubsemiring R where
  toSubsemiring := Subsemiring.copy S.toSubsemiring s hs
  star_mem' := @fun a ha => hs ▸ (S.star_mem' (by simpa [hs] using ha) : star a ∈ (S : Set R))

@[simp, norm_cast]
/-
**StarSubsemiring.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `StarSubsemiring`。
形式化陈述：coe_copy (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs 
: Set R) = s
参数：S : StarSubsemiring R；s : Set R；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl
/-
**StarSubsemiring.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `StarSubsemiring`。
形式化陈述：copy_eq (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = 
S
参数：S : StarSubsemiring R；s : Set R；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

section Center

variable (R)

/-- The center of a semiring `R` is the set of elements that commute and associate with everything
in `R` -/
/-
**StarSubsemiring.center** 是 Mathlib 中的一个定义，位于命名空间 `StarSubsemiring`。
形式化陈述：center (R) [NonAssocSemiring R] [StarRing R] : StarSubsemiring R where toS
ubsemiring
参数：R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a semiring `R` is the set of elements that commute and associate w
ith everything
in `R`
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

/-- The center of magma `A` is the set of elements that commute and associate
with everything in `A`, here realized as a `SubStarSemigroup`. -/
/-
**SubStarSemigroup.center** 是 Mathlib 中的一个定义，位于命名空间 `SubStarSemigroup`。
形式化陈述：center : SubStarSemigroup A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.star_mem_center`：Set.star_mem_center (ha : a in Set.center R) : star
 a in Set.center R where comm

--- 原说明 ---
The center of magma `A` is the set of elements that commute and associate
with everything in `A`, here realized as a `SubStarSemigroup`.
-/
def center : SubStarSemigroup A :=
  { Subsemigroup.center A with
    star_mem' := Set.star_mem_center }

end SubStarSemigroup

end SubStarSemigroup

