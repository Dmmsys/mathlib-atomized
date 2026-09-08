/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Int.CharZero

import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Further basic results about `Algebra`.

This file could usefully be split further.
-/

@[expose] public section

universe u v w u₁ v₁

open Function Module

namespace Algebra

variable {R A M : Type*}

section Semiring

variable [CommSemiring R]
variable [Semiring A] [Algebra R A]

section PUnit

/-
**Algebra._root_.PUnit.algebra** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.PUnit.algebra : Algebra R PUnit.{v + 1} where
  algebraMap :=
  { toFun _ := PUnit.unit
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl }
  commutes' _ _ := rfl
  smul_def' _ _ := rfl

@[simp]
/-
**Algebra.algebraMap_pUnit** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：algebraMap_pUnit (r : R) : algebraMap R PUnit r = PUnit.unit
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_pUnit (r : R) : algebraMap R PUnit r = PUnit.unit :=
  rfl

end PUnit

section ULift

/-
**Algebra._root_.ULift.algebra** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.ULift.algebra : Algebra R (ULift A) :=
  { ULift.module' with
    algebraMap :=
    { (ULift.ringEquiv : ULift A ≃+* A).symm.toRingHom.comp (algebraMap R A) with
      toFun := fun r => ULift.up (algebraMap R A r) }
    commutes' := fun r x => ULift.down_injective <| Algebra.commutes r x.down
    smul_def' := fun r x => ULift.down_injective <| Algebra.smul_def' r x.down }
/-
**Algebra._root_.ULift.algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ULift.algebraMap_eq (r : R) :
    algebraMap R (ULift A) r = ULift.up (algebraMap R A r) :=
  rfl

@[simp]
/-
**Algebra._root_.ULift.down_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ULift.down_algebraMap (r : R) : (algebraMap R (ULift A) r).down = algebraMap R A r :=
  rfl

variable (R A) in
/-- If `A` is an `R`-algebra, it is also a `ULift R`-algebra. In particular, `Ulift A` is a
`ULift R` algebra. This is not an instance, because it causes a non-reducible diamond in the case
where `A = Ulift R`. -/
@[instance_reducible]
/-
**Algebra._root_.ULift.algebra'** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is an `R`-algebra, it is also a `ULift R`-algebra. In particular, `Ulift 
A` is a
`ULift R` algebra. This is not an instance, because it causes a non-reducible di
amond in the case
where `A = Ulift R`.
-/
def _root_.ULift.algebra' : Algebra (ULift.{u} R) A where
  __ := ULift.module
  algebraMap := (algebraMap R A).comp ULift.ringEquiv.toRingHom
  commutes' _ _ := Algebra.commutes ..
  smul_def' _ _ := Algebra.smul_def' ..

attribute [local instance] ULift.algebra' in
/-- This references the `ULift.algebra'` instance. -/
@[simp]
/-
**Algebra._root_.ULift.algebraMap_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This references the `ULift.algebra'` instance.
-/
lemma _root_.ULift.algebraMap_apply' (r : ULift R) :
    algebraMap (ULift R) A r = algebraMap R A r.down := rfl

end ULift

section SubsemiringAlgebra

variable {C : Type*} [SetLike C R] [SubsemiringClass C R]

/-- Algebra over a subsemiring. This builds upon `Subsemiring.module`. -/
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebra over a subsemiring. This builds upon `Subsemiring.module`.
-/
instance (priority := 900) ofSubsemiring (S : C) : Algebra S A where
  algebraMap := (algebraMap R A).comp (Subsemiring.subtype <| .ofClass S)
  commutes' r x := Algebra.commutes (r : R) x
  smul_def' r x := Algebra.smul_def (r : R) x
/-
**Algebra.algebraMap_ofSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：algebraMap_ofSubsemiring (S : Subsemiring R) : (algebraMap S R : S ->+* R)
 = S.subtype
参数：S : Subsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
-/
theorem algebraMap_ofSubsemiring (S : Subsemiring R) :
    (algebraMap S R : S →+* R) = S.subtype :=
  rfl
/-
**Algebra.coe_algebraMap_ofSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：coe_algebraMap_ofSubsemiring (S : C) : (algebraMap S R : S -> R) = Subtype
.val
参数：S : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_algebraMap_ofSubsemiring (S : C) : (algebraMap S R : S → R) = Subtype.val :=
  rfl
/-
**Algebra.algebraMap_ofSubsemiring_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：algebraMap_ofSubsemiring_apply (S : C) (x : S) : algebraMap S R x = x
参数：S : C；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_ofSubsemiring_apply (S : C) (x : S) : algebraMap S R x = x :=
  rfl
/-
**Algebra.algebraMap_ofSubring** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：algebraMap_ofSubring {R : Type*} [CommRing R] (S : Subring R) : (algebraMa
p S R : S ->+* R) = S.subtype
参数：S : Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem algebraMap_ofSubring {R : Type*} [CommRing R] (S : Subring R) :
    (algebraMap S R : S →+* R) = S.subtype :=
  rfl

end SubsemiringAlgebra

/-- Explicit characterization of the submonoid map in the case of an algebra.
`S` is made explicit to help with type inference -/
/-
**Algebra.algebraMapSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：algebraMapSubmonoid (S : Type*) [Semiring S] [Algebra R S] (M : Submonoid 
R) : Submonoid S
参数：S : Type*；M : Submonoid R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Explicit characterization of the submonoid map in the case of an algebra.
`S` is made explicit to help with type inference
-/
def algebraMapSubmonoid (S : Type*) [Semiring S] [Algebra R S] (M : Submonoid R) : Submonoid S :=
  M.map (algebraMap R S)

variable {S : Type*} [Semiring S] [Algebra R S]
/-
**Algebra.mem_algebraMapSubmonoid_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：mem_algebraMapSubmonoid_of_mem {M : Submonoid R} (x : M) : algebraMap R S 
x in algebraMapSubmonoid S M
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mem_algebraMapSubmonoid_of_mem {M : Submonoid R}
    (x : M) : algebraMap R S x ∈ algebraMapSubmonoid S M :=
  Set.mem_image_of_mem (algebraMap R S) x.2

@[simp]
/-
**Algebra.algebraMapSubmonoid_self** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：algebraMapSubmonoid_self (M : Submonoid R) : Algebra.algebraMapSubmonoid R
 M = M
参数：M : Submonoid R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.map_id`：map_id (S : Submonoid M) : S.map (MonoidHom.id M) = S
-/
lemma algebraMapSubmonoid_self (M : Submonoid R) : Algebra.algebraMapSubmonoid R M = M :=
  Submonoid.map_id M

@[simp]
/-
**Algebra.algebraMapSubmonoid_powers** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：algebraMapSubmonoid_powers (r : R) : Algebra.algebraMapSubmonoid S (.power
s r) = Submonoid.powers (algebraMap R S r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.map_powers`：map_powers {N : Type*} {F : Type*} [Monoid N] [Fun
Like F M N] [MonoidHomClass F M N] (f : F) (m : M) : (powers m).map f = powers (
f m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma algebraMapSubmonoid_powers (r : R) :
    Algebra.algebraMapSubmonoid S (.powers r) = Submonoid.powers (algebraMap R S r) := by
  simp [Algebra.algebraMapSubmonoid]
/-
**Algebra.algebraMapSubmonoid_isUnit_le** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：algebraMapSubmonoid_isUnit_le : algebraMapSubmonoid S (IsUnit.submonoid R)
 <= IsUnit.submonoid S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma algebraMapSubmonoid_isUnit_le :
    algebraMapSubmonoid S (IsUnit.submonoid R) ≤ IsUnit.submonoid S := by
  rintro x ⟨y, hy, rfl⟩
  exact hy.map _

end Semiring

section CommSemiring

variable [CommSemiring R]

/-
**Algebra.mul_sub_algebraMap_commutes** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：mul_sub_algebraMap_commutes [Ring A] [Algebra R A] (x : A) (r : R) : x * (
x - algebraMap R A r) = (x - algebraMap R A r) * x
参数：x : A；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
-/
theorem mul_sub_algebraMap_commutes [Ring A] [Algebra R A] (x : A) (r : R) :
    x * (x - algebraMap R A r) = (x - algebraMap R A r) * x := by rw [mul_sub, ← commutes, sub_mul]
/-
**Algebra.mul_sub_algebraMap_pow_commutes** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：mul_sub_algebraMap_pow_commutes [Ring A] [Algebra R A] (x : A) (r : R) (n 
: Nat) : x * (x - algebraMap R A r) ^ n = (x - algebraMap R A r) ^ n * x
参数：x : A；r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Algebra.mul_sub_algebraMap_commutes`：mul_sub_algebraMap_commutes [Ring A
] [Algebra R A] (x : A) (r : R) : x * (x - algebraMap R A r) = (x - algebraMap R
 A r) * x
-/
theorem mul_sub_algebraMap_pow_commutes [Ring A] [Algebra R A] (x : A) (r : R) (n : ℕ) :
    x * (x - algebraMap R A r) ^ n = (x - algebraMap R A r) ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mul_assoc, mul_sub_algebraMap_commutes, mul_assoc, ih, ← mul_assoc]

end CommSemiring

section Ring

/-- A `Semiring` that is an `Algebra` over a commutative ring carries a natural `Ring` structure.
See note [reducible non-instances]. -/
/-
**Algebra.semiringToRing** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra`。
形式化陈述：semiringToRing (R : Type*) [CommRing R] [Semiring A] [Algebra R A] : Ring 
A
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Semiring` that is an `Algebra` over a commutative ring carries a natural `Rin
g` structure.
See note [reducible non-instances].
-/
abbrev semiringToRing (R : Type*) [CommRing R] [Semiring A] [Algebra R A] : Ring A :=
  { __ := (inferInstance : Semiring A)
    __ := Module.addCommMonoidToAddCommGroup R
    intCast := fun z => algebraMap R A z
    intCast_ofNat := fun z => by simp only [Int.cast_natCast, map_natCast]
    intCast_negSucc := fun z => by simp }

/-- The `CommRing` structure on a `CommSemiring` induced by a ring morphism from a `CommRing`. -/
/-
**Algebra._root_.RingHom.commSemiringToCommRing** 是 Mathlib 中的一个缩写定义，位于命名空间 `Alg
ebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `CommRing` structure on a `CommSemiring` induced by a ring morphism from a `
CommRing`.
-/
abbrev _root_.RingHom.commSemiringToCommRing {R A : Type*} [CommRing R] [CommSemiring A]
    (φ : R →+* A) : CommRing A :=
  let _ : Algebra R A := RingHom.toAlgebra φ
  { __ := Algebra.semiringToRing R
    mul_comm := CommMonoid.mul_comm }
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [Ring R] : Algebra (Subring.center R) R where
  algebraMap :=
  { toFun := Subtype.val
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl }
  commutes' r x := (Subring.mem_center_iff.1 r.2 x).symm
  smul_def' _ _ := rfl

end Ring

end Algebra

open scoped Algebra

namespace Module

variable (R : Type u) (S : Type v) (M : Type w)
variable [CommSemiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
variable [SMulCommClass S R M] [SMul R S] [IsScalarTower R S M]

/-
**Module.End.instAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Module.End`。
形式化陈述：(R : Type u) →   (S : Type v) →     (M : Type w) →       [inst : CommSemir
ing R] →         [inst_1 : Semiring S] →           [inst_2 : AddCommMonoid M] → 
            [inst_3 : _root_.Module R M] →               [inst_4 : _root_.Module
 S M] →                 [SMulCommClass S R M] → [inst_6 : SMul R S] → [IsScalarT
ower R S M] → Algebra R (Module.End S M)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance End.instAlgebra : Algebra R (Module.End S M) :=
  Algebra.ofModule smul_mul_assoc fun r f g => (smul_comm r f g).symm

-- to prove this is a special case of the above
/-
**Module.** 是 Mathlib 中的一个示例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Algebra R (Module.End R M) := End.instAlgebra _ _ _
/-
**Module.algebraMap_end_eq_smul_id** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：algebraMap_end_eq_smul_id (a : R) : algebraMap R (End S M) a = a • LinearM
ap.id
参数：a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_end_eq_smul_id (a : R) : algebraMap R (End S M) a = a • LinearMap.id :=
  rfl

@[simp]
/-
**Module.algebraMap_end_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：algebraMap_end_apply (a : R) (m : M) : algebraMap R (End S M) a m = a • m
参数：a : R；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_end_apply (a : R) (m : M) : algebraMap R (End S M) a m = a • m :=
  rfl

@[simp]
/-
**Module.ker_algebraMap_end** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：ker_algebraMap_end (K : Type u) (V : Type v) [Semifield K] [AddCommMonoid 
V] [Module K V] (a : K) (ha : a != 0) : LinearMap.ker ((algebraMap K (End K V)) 
a) = ⊥
参数：K : Type u；V : Type v；a : K；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_smul`：ker_smul (f : V ->ₗ[K] V₂) (a : K) (h : a != 0) : ke
r (a • f) = ker f
-/
theorem ker_algebraMap_end (K : Type u) (V : Type v) [Semifield K] [AddCommMonoid V] [Module K V]
    (a : K) (ha : a ≠ 0) : LinearMap.ker ((algebraMap K (End K V)) a) = ⊥ :=
  LinearMap.ker_smul _ _ ha

section

variable {R M}

/-
**Module.End.algebraMap_isUnit_inv_apply_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Modul
e.End`。
形式化陈述：∀ {R : Type u} (S : Type v) {M : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring S] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] [inst_4 :
 _root_.Module S M] [inst_5 : SMulCommClass S R M] [inst_6 : SMul R S]   [inst_7
 : IsScalarTower R S M] {x : R} (h : IsUnit ((algebraMap R (Module.End S M)) x))
 (m m' : M),   ↑h.unit⁻¹ m = m' ↔ m = x • m'
参数：S : Type v；h : IsUnit ((algebraMap R (Module.End S M)) x)；m m' : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.End.isUnit_apply_inv_apply_of_isUnit`：isUnit_apply_inv_apply_of_i
sUnit {f : End R M} (h : IsUnit f) (x : M) : f (h.unit.inv x) = x
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
theorem End.algebraMap_isUnit_inv_apply_eq_iff {x : R}
    (h : IsUnit (algebraMap R (Module.End S M) x)) (m m' : M) :
    (↑(h.unit⁻¹) : Module.End S M) m = m' ↔ m = x • m' where
  mp H := H ▸ (isUnit_apply_inv_apply_of_isUnit h m).symm
  mpr H := by
    apply_fun ⇑h.unit.val using ((isUnit_iff _).mp h).injective
    rw [H]
    simpa using Module.End.isUnit_apply_inv_apply_of_isUnit h (x • m')
/-
**Module.End.algebraMap_isUnit_inv_apply_eq_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Modu
le.End`。
形式化陈述：∀ {R : Type u} (S : Type v) {M : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring S] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] [inst_4 :
 _root_.Module S M] [inst_5 : SMulCommClass S R M] [inst_6 : SMul R S]   [inst_7
 : IsScalarTower R S M] {x : R} (h : IsUnit ((algebraMap R (Module.End S M)) x))
 (m m' : M),   m' = ↑h.unit⁻¹ m ↔ m = x • m'
参数：S : Type v；h : IsUnit ((algebraMap R (Module.End S M)) x)；m m' : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.End.isUnit_apply_inv_apply_of_isUnit`：isUnit_apply_inv_apply_of_i
sUnit {f : End R M} (h : IsUnit f) (x : M) : f (h.unit.inv x) = x
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
theorem End.algebraMap_isUnit_inv_apply_eq_iff' {x : R}
    (h : IsUnit (algebraMap R (Module.End S M) x)) (m m' : M) :
    m' = (↑h.unit⁻¹ : Module.End S M) m ↔ m = x • m' where
  mp H := H ▸ (isUnit_apply_inv_apply_of_isUnit h m).symm
  mpr H := by
    apply_fun (↑h.unit : M → M) using ((isUnit_iff _).mp h).injective
    rw [H]
    simpa using isUnit_apply_inv_apply_of_isUnit h (x • m') |>.symm

end

end Module

namespace LinearMap

variable {R : Type*} {A : Type*} {B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

/-- An alternate statement of `LinearMap.map_smul` for when `algebraMap` is more convenient to
work with than `•`. -/
/-
**LinearMap.map_algebraMap_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_algebraMap_mul (f : A ->ₗ[R] B) (a : A) (r : R) : f (algebraMap R A r 
* a) = algebraMap R B r * f a
参数：f : A ->ₗ[R] B；a : A；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…

--- 原说明 ---
An alternate statement of `LinearMap.map_smul` for when `algebraMap` is more con
venient to
work with than `•`.
-/
theorem map_algebraMap_mul (f : A →ₗ[R] B) (a : A) (r : R) :
    f (algebraMap R A r * a) = algebraMap R B r * f a := by
  rw [← Algebra.smul_def, ← Algebra.smul_def, map_smul]
/-
**LinearMap.map_mul_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_mul_algebraMap (f : A ->ₗ[R] B) (a : A) (r : R) : f (a * algebraMap R 
A r) = f a * algebraMap R B r
参数：f : A ->ₗ[R] B；a : A；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `LinearMap.map_algebraMap_mul`：map_algebraMap_mul (f : A ->ₗ[R] B) (a : A
) (r : R) : f (algebraMap R A r * a) = algebraMap R B r * f a
-/
theorem map_mul_algebraMap (f : A →ₗ[R] B) (a : A) (r : R) :
    f (a * algebraMap R A r) = f a * algebraMap R B r := by
  rw [← Algebra.commutes, ← Algebra.commutes, map_algebraMap_mul]

end LinearMap

section Nat

variable {R : Type*} [Semiring R]

-- Lower the priority so that `Algebra.id` is picked most of the time when working with
-- `ℕ`-algebras.
-- TODO: is this still needed?
/-- Semiring ⥤ ℕ-Alg -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Semiring ⥤ ℕ-Alg
-/
instance (priority := 99) Semiring.toNatAlgebra : Algebra ℕ R where
  commutes' := Nat.cast_commute
  smul_def' _ _ := nsmul_eq_mul _ _
  algebraMap := Nat.castRingHom R
/-
**nat_algebra_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：nat_algebra_subsingleton : Subsingleton (Algebra Nat R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.algebra_ext`：algebra_ext {R : Type*} [CommSemiring R] {A : Type*
} [Semiring A] (P Q : Algebra R A) (h : forall r : R, (haveI
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance nat_algebra_subsingleton : Subsingleton (Algebra ℕ R) :=
  ⟨fun P Q => by ext; simp⟩

@[simp]
/-
**algebraMap_comp_natCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_comp_natCast (R A : Type*) [CommSemiring R] [Semiring A] [Algeb
ra R A] : algebraMap R A ∘ Nat.cast = Nat.cast
参数：R A : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma algebraMap_comp_natCast (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    algebraMap R A ∘ Nat.cast = Nat.cast := by
  ext; simp

end Nat

section Int

variable (R : Type*) [Ring R]

-- Lower the priority so that `Algebra.id` is picked most of the time when working with
-- `ℤ`-algebras.
-- TODO: is this still needed?
/-- Ring ⥤ ℤ-Alg -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring ⥤ ℤ-Alg
-/
instance (priority := 99) Ring.toIntAlgebra : Algebra ℤ R where
  commutes' := Int.cast_commute
  smul_def' _ _ := zsmul_eq_mul _ _
  algebraMap := Int.castRingHom R

/-- A special case of `eq_intCast'` that happens to be true definitionally -/
@[simp]
/-
**algebraMap_int_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraMap_int_eq : algebraMap Int R = Int.castRingHom R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A special case of `eq_intCast'` that happens to be true definitionally
-/
theorem algebraMap_int_eq : algebraMap ℤ R = Int.castRingHom R :=
  rfl

variable {R}
/-
**int_algebra_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：int_algebra_subsingleton : Subsingleton (Algebra Int R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.algebra_ext`：algebra_ext {R : Type*} [CommSemiring R] {A : Type*
} [Semiring A] (P Q : Algebra R A) (h : forall r : R, (haveI
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `RingHom.Int.subsingleton_ringHom`：∀ {R : Type u_5} [inst : NonAssocSemir
ing R], Subsingleton (ℤ →+* R)
-/
instance int_algebra_subsingleton : Subsingleton (Algebra ℤ R) :=
  ⟨fun P Q => Algebra.algebra_ext P Q <| RingHom.congr_fun <| Subsingleton.elim _ _⟩

@[simp]
/-
**algebraMap_comp_intCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_comp_intCast (R A : Type*) [CommRing R] [Ring A] [Algebra R A] 
: algebraMap R A ∘ Int.cast = Int.cast
参数：R A : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma algebraMap_comp_intCast (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    algebraMap R A ∘ Int.cast = Int.cast := by
  ext; simp

end Int

section FaithfulSMul

/-
**_root_.NeZero.of_faithfulSMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.NeZero.of_faithfulSMul (R A : Type*) [Semiring R] [Semiring A] [Mod
ule R A] [IsScalarTower R A A] [FaithfulSMul R A] (n : Nat) [NeZero (n : R)] : N
eZero (n : A)
参数：R A : Type*；n : Nat；n : R。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NeZero.of_faithfulSMul (R A : Type*) [Semiring R] [Semiring A] [Module R A]
    [IsScalarTower R A A] [FaithfulSMul R A] (n : ℕ) [NeZero (n : R)] :
    NeZero (n : A) :=
  NeZero.nat_of_injective (f := ringHomEquivModuleIsScalarTower.symm ⟨_, ‹_›⟩) <|
    (faithfulSMul_iff_injective_smul_one R A).mp ‹_›

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
/-
**faithfulSMul_iff_algebraMap_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：faithfulSMul_iff_algebraMap_injective : FaithfulSMul R A ↔ Injective (alge
braMap R A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `faithfulSMul_iff_injective_smul_one`：faithfulSMul_iff_injective_smul_one
 (R A : Type*) [MulOneClass A] [SMul R A] [IsScalarTower R A A] : FaithfulSMul R
 A ↔ Injective (fun r : R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.algebraMap_eq_smul_one'`：algebraMap_eq_smul_one' : ⇑(algebraMap 
R A) = fun r => r • (1 : A)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma faithfulSMul_iff_algebraMap_injective : FaithfulSMul R A ↔ Injective (algebraMap R A) := by
  rw [faithfulSMul_iff_injective_smul_one, Algebra.algebraMap_eq_smul_one']

variable [FaithfulSMul R A]

namespace FaithfulSMul

/-
**FaithfulSMul.algebraMap_injective** 是 Mathlib 中的一个引理，位于命名空间 `FaithfulSMul`。
形式化陈述：algebraMap_injective : Injective (algebraMap R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
-/
lemma algebraMap_injective : Injective (algebraMap R A) :=
  (faithfulSMul_iff_algebraMap_injective R A).mp inferInstance

@[simp]
/-
**FaithfulSMul.algebraMap_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `FaithfulSMul`。
形式化陈述：algebraMap_eq_zero_iff {r : R} : algebraMap R A r = 0 ↔ r = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
lemma algebraMap_eq_zero_iff {r : R} : algebraMap R A r = 0 ↔ r = 0 :=
  map_eq_zero_iff (algebraMap R A) <| algebraMap_injective R A

@[simp]
/-
**FaithfulSMul.algebraMap_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `FaithfulSMul`。
形式化陈述：algebraMap_eq_one_iff {r : R} : algebraMap R A r = 1 ↔ r = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_one_iff`：map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Functio
n.Injective f) {x : M} : f x = 1 ↔ x = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
lemma algebraMap_eq_one_iff {r : R} : algebraMap R A r = 1 ↔ r = 1 :=
  map_eq_one_iff _ <| FaithfulSMul.algebraMap_injective R A

end FaithfulSMul

/-- If `R` embeds faithfully into `A` and `G` satisfies `SMulDistribClass G R A`, then
the `SMul` of `G` on `R` extends to a `MulSemiringAction`. -/
@[implicit_reducible]
/-
**mulSemiringActionOfSmulDistribClass** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulSemiringActionOfSmulDistribClass (G : Type*) [Monoid G] [MulSemiringAct
ion G A] [SMul G R] [SMulDistribClass G R A] : MulSemiringAction G R where one_s
mul _
参数：G : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` embeds faithfully into `A` and `G` satisfies `SMulDistribClass G R A`, th
en
the `SMul` of `G` on `R` extends to a `MulSemiringAction`.
-/
noncomputable def mulSemiringActionOfSmulDistribClass (G : Type*) [Monoid G]
    [MulSemiringAction G A] [SMul G R] [SMulDistribClass G R A] :
    MulSemiringAction G R where
  one_smul _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul', one_smul]
  smul_zero _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul', map_zero, smul_zero]
  mul_smul _ _ _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul', algebraMap.smul', algebraMap.smul', mul_smul]
  smul_add _ _ _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul', map_add, smul_add, ← algebraMap.smul', ← algebraMap.smul', ← map_add]
  smul_one _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul', map_one, smul_one]
  smul_mul _ _ _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul', map_mul, map_mul, algebraMap.smul', algebraMap.smul',
      MulSemiringAction.smul_mul]

namespace algebraMap

@[norm_cast, simp]
/-
**algebraMap.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `algebraMap`。
形式化陈述：coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b :=
  (FaithfulSMul.algebraMap_injective _ _).eq_iff

@[norm_cast]
/-
**algebraMap.coe_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `algebraMap`。
形式化陈述：coe_eq_zero_iff (a : R) : (↑a : A) = 0 ↔ a = 0
参数：a : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_eq_zero_iff`：algebraMap_eq_zero_iff {r : R} : al
gebraMap R A r = 0 ↔ r = 0
-/
theorem coe_eq_zero_iff (a : R) : (↑a : A) = 0 ↔ a = 0 :=
  FaithfulSMul.algebraMap_eq_zero_iff _ _

end algebraMap

/-
**Algebra.charZero_of_charZero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.charZero_of_charZero [CharZero R] : CharZero A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `algebraMap_comp_natCast`：algebraMap_comp_natCast (R A : Type*) [CommSemi
ring R] [Semiring A] [Algebra R A] : algebraMap R A ∘ Nat.cast = Nat.cast
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `CharZero.cast_injective`：∀ {R : Type u_1} {inst : AddMonoidWithOne R} [s
elf : CharZero R], Function.Injective Nat.cast
-/
lemma Algebra.charZero_of_charZero [CharZero R] : CharZero A :=
  have := algebraMap_comp_natCast R A
  ⟨this ▸ (FaithfulSMul.algebraMap_injective R A).comp CharZero.cast_injective⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CharZero R] : FaithfulSMul ℕ R := by
  simpa only [faithfulSMul_iff_algebraMap_injective] using (algebraMap ℕ R).injective_nat
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type*) [Ring R] [CharZero R] : FaithfulSMul ℤ R := by
  simpa only [faithfulSMul_iff_algebraMap_injective] using (algebraMap ℤ R).injective_int

end FaithfulSMul

section IsScalarTower

variable {R : Type*} [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable {M : Type*} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]

/-
**algebra_compatible_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebra_compatible_smul (r : R) (m : M) : r • m = (algebraMap R A) r • m
参数：r : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem algebra_compatible_smul (r : R) (m : M) : r • m = (algebraMap R A) r • m := by
  rw [← one_smul A m, ← smul_assoc, Algebra.smul_def, mul_one, one_smul]

@[simp]
/-
**algebraMap_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • m = r • m
参数：r : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `algebra_compatible_smul`：algebra_compatible_smul (r : R) (m : M) : r • m
 = (algebraMap R A) r • m
-/
theorem algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • m = r • m :=
  (algebra_compatible_smul A r m).symm
/-
**isSMulRegular_algebraMap_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSMulRegular_algebraMap_iff {r : R} : IsSMulRegular M (algebraMap R A r) 
↔ IsSMulRegular M r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.isSMulRegular_congr`：Equiv.isSMulRegular_congr {R S M M'} [SMul R 
M] [SMul S M'] {e : M ≃ M'} {r : R} {s : S} (h : forall x, e (r • x) = s • e x) 
: IsSMulRegular…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
lemma isSMulRegular_algebraMap_iff {r : R} :
    IsSMulRegular M (algebraMap R A r) ↔ IsSMulRegular M r :=
  (Equiv.refl M).isSMulRegular_congr (algebraMap_smul A r)

variable {A}

-- see Note [lower instance priority]
-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980, as it is a very common path
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 120) IsScalarTower.to_smulCommClass : SMulCommClass R A M :=
  ⟨fun r a m => by
    rw [algebra_compatible_smul A r (a • m), smul_smul, Algebra.commutes, mul_smul, ←
      algebra_compatible_smul]⟩

-- see Note [lower instance priority]
-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980, as it is a very common path
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 110) IsScalarTower.to_smulCommClass' : SMulCommClass A R M :=
  SMulCommClass.symm _ _ _

/-- This has high priority because it is almost always the right instance when it applies. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This has high priority because it is almost always the right instance when it ap
plies.
-/
instance (priority := high) Algebra.to_smulCommClass {R A} [CommSemiring R] [Semiring A]
    [Algebra R A] : SMulCommClass R A A :=
  IsScalarTower.to_smulCommClass

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {R S A : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
    [Algebra R A] [Algebra S A] :
    SMulCommClass R S A where
  smul_comm r s a := by
    rw [Algebra.smul_def, mul_smul_comm, ← Algebra.smul_def]
/-
**smul_algebra_smul_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_algebra_smul_comm (r : R) (a : A) (m : M) : a • r • m = r • a • m
参数：r : R；a : A；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
theorem smul_algebra_smul_comm (r : R) (a : A) (m : M) : a • r • m = r • a • m :=
  smul_comm _ _ _

end IsScalarTower

section FaithfulSMul
variable (R S A M : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A]

/-
**NoZeroDivisors.of_faithfulSMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NoZeroDivisors.of_faithfulSMul [NoZeroDivisors A] : NoZeroDivisors R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.noZeroDivisors`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [i
nst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : M
₀ → M₀'),   Function.In…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma NoZeroDivisors.of_faithfulSMul [NoZeroDivisors A] : NoZeroDivisors R :=
  (FaithfulSMul.algebraMap_injective R A).noZeroDivisors _ (by simp) (by simp)
/-
**IsCancelMulZero.of_faithfulSMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCancelMulZero.of_faithfulSMul [IsCancelMulZero A] : IsCancelMulZero R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [
inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : 
M₀ → M₀'),   Function.In…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma IsCancelMulZero.of_faithfulSMul [IsCancelMulZero A] : IsCancelMulZero R :=
  (FaithfulSMul.algebraMap_injective R A).isCancelMulZero _ (by simp) (by simp)
/-
**IsDomain.of_faithfulSMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDomain.of_faithfulSMul [IsDomain A] : IsDomain R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
lemma IsDomain.of_faithfulSMul [IsDomain A] : IsDomain R :=
  (FaithfulSMul.algebraMap_injective R A).isDomain
/-
**Module.IsTorsionFree.of_faithfulSMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.IsTorsionFree.of_faithfulSMul [Semiring S] [Module S R] [Module S A
] [IsScalarTower S R A] [IsTorsionFree S A] : IsTorsionFree S R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Injective.moduleIsTorsionFree`：Function.Injective.moduleIsTorsi
onFree [IsTorsionFree R N] (f : M -> N) (hf : f.Injective) (smul : forall (r : R
) (m : M), f (r • m) = r • f…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma Module.IsTorsionFree.of_faithfulSMul [Semiring S] [Module S R] [Module S A]
    [IsScalarTower S R A] [IsTorsionFree S A] : IsTorsionFree S R :=
  (FaithfulSMul.algebraMap_injective R A).moduleIsTorsionFree _
    (by simp [Algebra.algebraMap_eq_smul_one])
/-
**Module.IsTorsionFree.trans_faithfulSMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.IsTorsionFree.trans_faithfulSMul [Nontrivial R] [IsCancelMulZero A]
 [AddCommMonoid M] [Module A M] [Module R M] [IsTorsionFree A M] [IsScalarTower 
R A M] : IsTorsionFree R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.IsTorsionFree.comap`：Module.IsTorsionFree.comap [IsTorsionFree S 
M] (f : R -> S) (isRegular : forall r, IsRegular r -> IsRegular (f r)) (smul : f
orall (r : R) (m…
· 使用定理 `IsRegular.of_ne_zero`：IsRegular.of_ne_zero (a0 : a != 0) : IsRegular a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsRegular.ne_zero`：IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) :
 a != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma Module.IsTorsionFree.trans_faithfulSMul [Nontrivial R] [IsCancelMulZero A] [AddCommMonoid M]
    [Module A M] [Module R M] [IsTorsionFree A M] [IsScalarTower R A M] : IsTorsionFree R M :=
  .comap (algebraMap R A) (fun r hr ↦ .of_ne_zero <| by simpa using hr.ne_zero) (by simp)

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) FaithfulSMul.to_isTorsionFree [Nontrivial R] [IsCancelMulZero A] :
    IsTorsionFree R A := .trans_faithfulSMul R A A

end FaithfulSMul

namespace Module
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 101) IsTorsionFree.to_faithfulSMul [IsCancelMulZero R] [Nontrivial A]
    [IsTorsionFree R A] : FaithfulSMul R A where
  eq_of_smul_eq_smul h := smul_left_injective _ one_ne_zero <| h 1

variable [IsDomain R] [IsDomain A]
/-
**Module.isTorsionFree_iff_faithfulSMul** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：isTorsionFree_iff_faithfulSMul : IsTorsionFree R A ↔ FaithfulSMul R A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
-/
lemma isTorsionFree_iff_faithfulSMul : IsTorsionFree R A ↔ FaithfulSMul R A :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩
/-
**Module.isTorsionFree_iff_algebraMap_injective** 是 Mathlib 中的一个引理，位于命名空间 `Modul
e`。
形式化陈述：isTorsionFree_iff_algebraMap_injective : IsTorsionFree R A ↔ Injective (al
gebraMap R A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.isTorsionFree_iff_faithfulSMul`：isTorsionFree_iff_faithfulSMul : 
IsTorsionFree R A ↔ FaithfulSMul R A
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isTorsionFree_iff_algebraMap_injective : IsTorsionFree R A ↔ Injective (algebraMap R A) := by
  rw [isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective]

end Module

@[deprecated (since := "2026-01-21")]
alias NoZeroSMulDivisors.iff_algebraMap_injective := isTorsionFree_iff_algebraMap_injective

@[deprecated (since := "2026-01-21")]
alias NoZeroSMulDivisors.iff_faithfulSMul := isTorsionFree_iff_faithfulSMul

/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {R A} [CommSemiring R] [Semiring A] [Module R A] [SMulCommClass R A A]
    [IsScalarTower R A A] : Algebra R A :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

section invertibility

variable {R A B : Type*}
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- If there is a linear map `f : A →ₗ[R] B` that preserves `1`, then `algebraMap R B r` is
invertible when `algebraMap R A r` is. -/
/-
**Invertible.algebraMapOfInvertibleAlgebraMap** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Invertible.algebraMapOfInvertibleAlgebraMap (f : A ->ₗ[R] B) (hf : f 1 = 1
) {r : R} (h : Invertible (algebraMap R A r)) : Invertible (algebraMap R B r) wh
ere invOf
参数：f : A ->ₗ[R] B；hf : f 1 = 1；h : Invertible (algebraMap R A r)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If there is a linear map `f : A →ₗ[R] B` that preserves `1`, then `algebraMap R 
B r` is
invertible when `algebraMap R A r` is.
-/
abbrev Invertible.algebraMapOfInvertibleAlgebraMap (f : A →ₗ[R] B) (hf : f 1 = 1) {r : R}
    (h : Invertible (algebraMap R A r)) : Invertible (algebraMap R B r) where
  invOf := f ⅟(algebraMap R A r)
  invOf_mul_self := by rw [← Algebra.commutes, ← Algebra.smul_def, ← map_smul, Algebra.smul_def,
    mul_invOf_self, hf]
  mul_invOf_self := by rw [← Algebra.smul_def, ← map_smul, Algebra.smul_def, mul_invOf_self, hf]

/-- If there is a linear map `f : A →ₗ[R] B` that preserves `1`, then `algebraMap R B r` is
a unit when `algebraMap R A r` is. -/
/-
**IsUnit.algebraMap_of_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnit.algebraMap_of_algebraMap (f : A ->ₗ[R] B) (hf : f 1 = 1) {r : R} (h
 : IsUnit (algebraMap R A r)) : IsUnit (algebraMap R B r)
参数：f : A ->ₗ[R] B；hf : f 1 = 1；h : IsUnit (algebraMap R A r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.nonempty_invertible`：IsUnit.nonempty_invertible [Monoid α] {a : α
} (h : IsUnit a) : Nonempty (Invertible a)
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a

--- 原说明 ---
If there is a linear map `f : A →ₗ[R] B` that preserves `1`, then `algebraMap R 
B r` is
a unit when `algebraMap R A r` is.
-/
lemma IsUnit.algebraMap_of_algebraMap (f : A →ₗ[R] B) (hf : f 1 = 1) {r : R}
    (h : IsUnit (algebraMap R A r)) : IsUnit (algebraMap R B r) :=
  let ⟨i⟩ := nonempty_invertible h
  letI := Invertible.algebraMapOfInvertibleAlgebraMap f hf i
  isUnit_of_invertible _

end invertibility

section algebraMap

variable {F E : Type*} [CommSemiring F] [Semiring E] [Algebra F E] (b : F →ₗ[F] E)

/-- If `E` is an `F`-algebra, and there exists an injective `F`-linear map from `F` to `E`,
then the algebra map from `F` to `E` is also injective. -/
/-
**injective_algebraMap_of_linearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：injective_algebraMap_of_linearMap (hb : Injective b) : Injective (algebraM
ap F E)
参数：hb : Injective b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x

--- 原说明 ---
If `E` is an `F`-algebra, and there exists an injective `F`-linear map from `F` 
to `E`,
then the algebra map from `F` to `E` is also injective.
-/
theorem injective_algebraMap_of_linearMap (hb : Injective b) :
    Injective (algebraMap F E) := fun x y e ↦ hb <| by
  rw [← mul_one x, ← mul_one y, ← smul_eq_mul, ← smul_eq_mul,
    map_smul, map_smul, Algebra.smul_def, Algebra.smul_def, e]

/-- If `E` is an `F`-algebra, and there exists a surjective `F`-linear map from `F` to `E`,
then the algebra map from `F` to `E` is also surjective. -/
/-
**surjective_algebraMap_of_linearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjective_algebraMap_of_linearMap (hb : Surjective b) : Surjective (algeb
raMap F E)
参数：hb : Surjective b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
If `E` is an `F`-algebra, and there exists a surjective `F`-linear map from `F` 
to `E`,
then the algebra map from `F` to `E` is also surjective.
-/
theorem surjective_algebraMap_of_linearMap (hb : Surjective b) :
    Surjective (algebraMap F E) := fun x ↦ by
  obtain ⟨x, rfl⟩ := hb x
  obtain ⟨y, hy⟩ := hb (b 1 * b 1)
  refine ⟨x * y, ?_⟩
  obtain ⟨z, hz⟩ := hb 1
  apply_fun (x • z • ·) at hy
  rwa [← map_smul, smul_eq_mul, mul_comm, ← smul_mul_assoc, ← map_smul _ z, smul_eq_mul, mul_one,
    ← smul_eq_mul, map_smul, hz, one_mul, ← map_smul, smul_eq_mul, mul_one, smul_smul,
    ← Algebra.algebraMap_eq_smul_one] at hy

/-- If `E` is an `F`-algebra, and there exists a bijective `F`-linear map from `F` to `E`,
then the algebra map from `F` to `E` is also bijective.

NOTE: The same result can also be obtained if there are two `F`-linear maps from `F` to `E`,
one is injective, the other one is surjective. In this case, use
`injective_algebraMap_of_linearMap` and `surjective_algebraMap_of_linearMap` separately. -/
/-
**bijective_algebraMap_of_linearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bijective_algebraMap_of_linearMap (hb : Bijective b) : Bijective (algebraM
ap F E)
参数：hb : Bijective b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `injective_algebraMap_of_linearMap`：injective_algebraMap_of_linearMap (hb
 : Injective b) : Injective (algebraMap F E)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `surjective_algebraMap_of_linearMap`：surjective_algebraMap_of_linearMap (
hb : Surjective b) : Surjective (algebraMap F E)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `E` is an `F`-algebra, and there exists a bijective `F`-linear map from `F` t
o `E`,
then the algebra map from `F` to `E` is also bijective.

NOTE: The same result can also be obtained if there are two `F`-linear maps from
 `F` to `E`,
one is injective, the other one is surjective. In this case, use
`injective_algebraMap_of_linearMap` and `surjective_algebraMap_of_linearMap` sep
arately.
-/
theorem bijective_algebraMap_of_linearMap (hb : Bijective b) :
    Bijective (algebraMap F E) :=
  ⟨injective_algebraMap_of_linearMap b hb.1, surjective_algebraMap_of_linearMap b hb.2⟩

/-- If `E` is an `F`-algebra, there exists an `F`-linear isomorphism from `F` to `E` (namely,
`E` is a free `F`-module of rank one), then the algebra map from `F` to `E` is bijective. -/
/-
**bijective_algebraMap_of_linearEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bijective_algebraMap_of_linearEquiv (b : F ≃ₗ[F] E) : Bijective (algebraMa
p F E)
参数：b : F ≃ₗ[F] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bijective_algebraMap_of_linearMap`：bijective_algebraMap_of_linearMap (hb
 : Bijective b) : Bijective (algebraMap F E)
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
If `E` is an `F`-algebra, there exists an `F`-linear isomorphism from `F` to `E`
 (namely,
`E` is a free `F`-module of rank one), then the algebra map from `F` to `E` is b
ijective.
-/
theorem bijective_algebraMap_of_linearEquiv (b : F ≃ₗ[F] E) :
    Bijective (algebraMap F E) :=
  bijective_algebraMap_of_linearMap _ b.bijective

end algebraMap

section surjective

variable {R S} [CommSemiring R] [Semiring S] [Algebra R S]
variable {M N} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S M] [IsScalarTower R S M]
variable [Module R N] [Module S N] [IsScalarTower R S N]

/-- If `R →+* S` is surjective, then `S`-linear maps between modules are exactly `R`-linear maps. -/
/-
**LinearMap.extendScalarsOfSurjectiveEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.extendScalarsOfSurjectiveEquiv (h : Surjective (algebraMap R S))
 : (M ->ₗ[R] N) ≃ₗ[R] (M ->ₗ[S] N) where toFun f
参数：h : Surjective (algebraMap R S)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…

--- 原说明 ---
If `R →+* S` is surjective, then `S`-linear maps between modules are exactly `R`
-linear maps.
-/
def LinearMap.extendScalarsOfSurjectiveEquiv (h : Surjective (algebraMap R S)) :
    (M →ₗ[R] N) ≃ₗ[R] (M →ₗ[S] N) where
  toFun f := { __ := f, map_smul' := fun r x ↦ by obtain ⟨r, rfl⟩ := h r; simp }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f.restrictScalars S

/-- If `R →+* S` is surjective, then `R`-linear maps are also `S`-linear. -/
/-
**LinearMap.extendScalarsOfSurjective** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearMap.extendScalarsOfSurjective (h : Surjective (algebraMap R S)) (l :
 M ->ₗ[R] N) : M ->ₗ[S] N
参数：h : Surjective (algebraMap R S)；l : M ->ₗ[R] N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…

--- 原说明 ---
If `R →+* S` is surjective, then `R`-linear maps are also `S`-linear.
-/
abbrev LinearMap.extendScalarsOfSurjective (h : Surjective (algebraMap R S))
    (l : M →ₗ[R] N) : M →ₗ[S] N :=
  extendScalarsOfSurjectiveEquiv h l

/-- If `R →+* S` is surjective, then `R`-linear isomorphisms are also `S`-linear. -/
/-
**LinearEquiv.extendScalarsOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearEquiv.extendScalarsOfSurjective (h : Surjective (algebraMap R S)) (f
 : M ≃ₗ[R] N) : M ≃ₗ[S] N where __
参数：h : Surjective (algebraMap R S)；f : M ≃ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R →+* S` is surjective, then `R`-linear isomorphisms are also `S`-linear.
-/
def LinearEquiv.extendScalarsOfSurjective (h : Surjective (algebraMap R S))
    (f : M ≃ₗ[R] N) : M ≃ₗ[S] N where
  __ := f
  map_smul' r x := by obtain ⟨r, rfl⟩ := h r; simp

variable (h : Surjective (algebraMap R S))

@[simp]
/-
**LinearMap.extendScalarsOfSurjective_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.extendScalarsOfSurjective_apply (l : M ->ₗ[R] N) (x) : l.extendS
calarsOfSurjective h x = l x
参数：l : M ->ₗ[R] N；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LinearMap.extendScalarsOfSurjective_apply (l : M →ₗ[R] N) (x) :
    l.extendScalarsOfSurjective h x = l x := rfl

@[simp]
/-
**LinearEquiv.extendScalarsOfSurjective_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearEquiv.extendScalarsOfSurjective_apply (f : M ≃ₗ[R] N) (x) : f.extend
ScalarsOfSurjective h x = f x
参数：f : M ≃ₗ[R] N；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LinearEquiv.extendScalarsOfSurjective_apply (f : M ≃ₗ[R] N) (x) :
    f.extendScalarsOfSurjective h x = f x := rfl

@[simp]
/-
**LinearEquiv.extendScalarsOfSurjective_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearEquiv.extendScalarsOfSurjective_symm (f : M ≃ₗ[R] N) : (f.extendScal
arsOfSurjective h).symm = f.symm.extendScalarsOfSurjective h
参数：f : M ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LinearEquiv.extendScalarsOfSurjective_symm (f : M ≃ₗ[R] N) :
    (f.extendScalarsOfSurjective h).symm = f.symm.extendScalarsOfSurjective h := rfl

end surjective

namespace algebraMap

section CommSemiringCommSemiring

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {ι : Type*} {s : Finset ι}

@[norm_cast]
/-
**algebraMap.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `algebraMap`。
形式化陈述：coe_prod (a : ι -> R) : (↑(∏ i in s, a i : R) : A) = ∏ i in s, (↑(a i) : A
)
参数：a : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_prod (a : ι → R) : (↑(∏ i ∈ s, a i : R) : A) = ∏ i ∈ s, (↑(a i) : A) :=
  map_prod (algebraMap R A) a s

@[norm_cast]
/-
**algebraMap.coe_sum** 是 Mathlib 中的一个定理，位于命名空间 `algebraMap`。
形式化陈述：coe_sum (a : ι -> R) : ↑(∑ i in s, a i) = ∑ i in s, (↑(a i) : A)
参数：a : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem coe_sum (a : ι → R) : ↑(∑ i ∈ s, a i) = ∑ i ∈ s, (↑(a i) : A) :=
  map_sum (algebraMap R A) a s

end CommSemiringCommSemiring

end algebraMap

