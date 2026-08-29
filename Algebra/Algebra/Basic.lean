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

/--
Instance `_root_.PUnit.algebra` / 实例 `_root_.PUnit.algebra`

English:
instance _root_.PUnit.algebra
  signature: : Algebra R PUnit.{v + 1} where
  body: { toFun _ := PUnit.unit
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl }
  commutes' _ _ := rfl
  smul_def' _ _ := rfl

@[simp]

中文:
实例 _root_.命题单元.algebra
  签名: : 代数 R 命题单元.{v + 1} where
  定义体: { toFun _ := PUnit.unit
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl }
  commutes' _ _ := rfl
  smul_def' _ _ := rfl

@[simp]

Depends on / 依赖: PUnit.unit, commutes, map_add, map_mul, map_one, map_zero, smul_def
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
/--
theorem `algebraMap_pUnit` / 定理 `algebraMap_pUnit`

English:
theorem algebraMap_pUnit
  given: (r : R)
  statement: algebraMap R PUnit r = PUnit.unit
  proof: rfl

中文:
定理 algebraMap_pUnit
  条件: (r : R)
  结论: algebraMap R 命题单元 r = 命题单元.unit
  证明: rfl
-/
theorem algebraMap_pUnit (r : R) : algebraMap R PUnit r = PUnit.unit :=
  rfl

end PUnit

section ULift

/--
Instance `_root_.ULift.algebra` / 实例 `_root_.ULift.algebra`

English:
instance _root_.ULift.algebra
  signature: : Algebra R (ULift A)
  body: { ULift.module' with
    algebraMap :=
    { (ULift.ringEquiv : ULift A ≃+* A).symm.toRingHom.comp (algebraMap R A) with
      toFun := fun r => ULift.up (algebraMap R A r) }
commutes' := fun r x => ULift.down_injective Algebra.commutes r x.down
smul_def' := fun r x => ULift.down_injective Algebra.s

中文:
实例 _root_.类型层提升.algebra
  签名: : 代数 R (类型层提升 A)
  定义体: { ULift.module' with
    algebraMap :=
    { (ULift.ringEquiv : ULift A ≃+* A).symm.toRingHom.comp (algebraMap R A) with
      toFun := fun r => ULift.up (algebraMap R A r) }
commutes' := fun r x => ULift.down_injective Algebra.commutes r x.down
smul_def' := fun r x => ULift.down_injective Algebra.s

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.smul_def, ULift.down_injective, ULift.module, ULift.ringEquiv, ULift.up, algebraMap, commutes, down_injective, module, ringEquiv, smul_def, symm.toRingHom.comp, toRingHom, x.down
-/
instance _root_.ULift.algebra : Algebra R (ULift A) :=
  { ULift.module' with
    algebraMap :=
    { (ULift.ringEquiv : ULift A ≃+* A).symm.toRingHom.comp (algebraMap R A) with
      toFun := fun r => ULift.up (algebraMap R A r) }
commutes' := fun r x => ULift.down_injective Algebra.commutes r x.down
smul_def' := fun r x => ULift.down_injective Algebra.smul_def' r x.down }

/--
theorem `_root_.ULift.algebraMap_eq` / 定理 `_root_.ULift.algebraMap_eq`

English:
theorem _root_.ULift.algebraMap_eq
  given: (r : R)
  proof: rfl

@[simp]

中文:
定理 _root_.类型层提升.algebraMap_eq
  条件: (r : R)
  证明: rfl

@[simp]
-/
theorem _root_.ULift.algebraMap_eq (r : R) :
    algebraMap R (ULift A) r = ULift.up (algebraMap R A r) :=
  rfl

@[simp]
/--
theorem `_root_.ULift.down_algebraMap` / 定理 `_root_.ULift.down_algebraMap`

English:
theorem _root_.ULift.down_algebraMap
  given: (r : R)
  statement: (algebraMap R (ULift A) r).down = algebraMap R A r
  proof: rfl

中文:
定理 _root_.类型层提升.down_algebraMap
  条件: (r : R)
  结论: (algebraMap R (类型层提升 A) r).down = algebraMap R A r
  证明: rfl
-/
theorem _root_.ULift.down_algebraMap (r : R) : (algebraMap R (ULift A) r).down = algebraMap R A r :=
  rfl

variable (R A) in
/-- If `A` is an `R`-algebra, it is also a `ULift R`-algebra. In particular, `Ulift A` is a
`ULift R` algebra. This is not an instance, because it causes a non-reducible diamond in the case
where `A = Ulift R`. -/
@[instance_reducible]
/--
Definition of `_root_.ULift.algebra'` / `_root_.ULift.algebra'` 的定义

English:
definition _root_.ULift.algebra'
  signature: : Algebra (ULift.{u} R) A where
  body: ULift.module
  algebraMap := (algebraMap R A).comp ULift.ringEquiv.toRingHom
  commutes' _ _ := Algebra.commutes ..
  smul_def' _ _ := Algebra.smul_def' ..

中文:
定义 _root_.类型层提升.algebra'
  签名: : 代数 (类型层提升.{u} R) A where
  定义体: ULift.module
  algebraMap := (algebraMap R A).comp ULift.ringEquiv.toRingHom
  commutes' _ _ := Algebra.commutes ..
  smul_def' _ _ := Algebra.smul_def' ..

Depends on / 依赖: ULift.module, module
-/
def _root_.ULift.algebra' : Algebra (ULift.{u} R) A where
  __ := ULift.module
  algebraMap := (algebraMap R A).comp ULift.ringEquiv.toRingHom
  commutes' _ _ := Algebra.commutes ..
  smul_def' _ _ := Algebra.smul_def' ..

attribute [local instance] ULift.algebra' in
/-- This references the `ULift.algebra'` instance. -/
@[simp]
/--
lemma `_root_.ULift.algebraMap_apply'` / 引理 `_root_.ULift.algebraMap_apply'`

English:
lemma _root_.ULift.algebraMap_apply'
  given: (r : ULift R)
  proof: rfl

中文:
引理 _root_.类型层提升.algebraMap_apply'
  条件: (r : 类型层提升 R)
  证明: rfl
-/
lemma _root_.ULift.algebraMap_apply' (r : ULift R) :
    algebraMap (ULift R) A r = algebraMap R A r.down := rfl

end ULift

section SubsemiringAlgebra

variable {C : Type*} [SetLike C R] [SubsemiringClass C R]

/-- Algebra over a subsemiring. This builds upon `Subsemiring.module`. -/
instance (priority := 900) ofSubsemiring (S : C) : Algebra S A where
  algebraMap := (algebraMap R A).comp (Subsemiring.subtype <| .ofClass S)
  commutes' r x := Algebra.commutes (r : R) x
  smul_def' r x := Algebra.smul_def (r : R) x

/--
theorem `algebraMap_ofSubsemiring` / 定理 `algebraMap_ofSubsemiring`

English:
theorem algebraMap_ofSubsemiring
  given: (S : Subsemiring R)
  proof: rfl

中文:
定理 algebraMap_ofSubsemiring
  条件: (S : 子半环 R)
  证明: rfl
-/
theorem algebraMap_ofSubsemiring (S : Subsemiring R) :
    (algebraMap S R : S ->+* R) = S.subtype :=
  rfl

/--
theorem `coe_algebraMap_ofSubsemiring` / 定理 `coe_algebraMap_ofSubsemiring`

English:
theorem coe_algebraMap_ofSubsemiring
  given: (S : C)
  statement: (algebraMap S R : S -> R) = Subtype.val
  proof: rfl

中文:
定理 coe_algebraMap_ofSubsemiring
  条件: (S : C)
  结论: (algebraMap S R : S -> R) = 子类型.val
  证明: rfl
-/
theorem coe_algebraMap_ofSubsemiring (S : C) : (algebraMap S R : S -> R) = Subtype.val :=
  rfl

/--
theorem `algebraMap_ofSubsemiring_apply` / 定理 `algebraMap_ofSubsemiring_apply`

English:
theorem algebraMap_ofSubsemiring_apply
  given: (S : C) (x : S)
  statement: algebraMap S R x = x
  proof: rfl

中文:
定理 algebraMap_ofSubsemiring_apply
  条件: (S : C) (x : S)
  结论: algebraMap S R x = x
  证明: rfl
-/
theorem algebraMap_ofSubsemiring_apply (S : C) (x : S) : algebraMap S R x = x :=
  rfl

/--
theorem `algebraMap_ofSubring` / 定理 `algebraMap_ofSubring`

English:
theorem algebraMap_ofSubring
  given: {R : Type*} [CommRing R] (S : Subring R)
  proof: rfl

中文:
定理 algebraMap_ofSubring
  条件: {R : 类型} [交换环 R] (S : 子环 R)
  证明: rfl
-/
theorem algebraMap_ofSubring {R : Type*} [CommRing R] (S : Subring R) :
    (algebraMap S R : S ->+* R) = S.subtype :=
  rfl

end SubsemiringAlgebra

/--
Definition of `algebraMapSubmonoid` / `algebraMapSubmonoid` 的定义

English:
definition algebraMapSubmonoid
  signature: (S : Type*) [Semiring S] [Algebra R S] (M : Submonoid R)
  body: M.map (algebraMap R S)

中文:
定义 algebraMapSubmonoid
  签名: (S : 类型) [半环 S] [代数 R S] (M : 子幺半群 R)
  定义体: M.map (algebraMap R S)

Depends on / 依赖: M.map, algebraMap
-/
def algebraMapSubmonoid (S : Type*) [Semiring S] [Algebra R S] (M : Submonoid R) : Submonoid S :=
  M.map (algebraMap R S)

variable {S : Type*} [Semiring S] [Algebra R S]

/--
theorem `mem_algebraMapSubmonoid_of_mem` / 定理 `mem_algebraMapSubmonoid_of_mem`

English:
theorem mem_algebraMapSubmonoid_of_mem
  statement: {M : Submonoid R}
  proof: Set.mem_image_of_mem (algebraMap R S) x.2

@[simp]

中文:
定理 mem_algebraMapSubmonoid_of_mem
  结论: {M : 子幺半群 R}
  证明: Set.mem_image_of_mem (algebraMap R S) x.2

@[simp]

Depends on / 依赖: Set.mem_image_of_mem, algebraMap, mem_image_of_mem
-/
theorem mem_algebraMapSubmonoid_of_mem {M : Submonoid R}
    (x : M) : algebraMap R S x in algebraMapSubmonoid S M :=
  Set.mem_image_of_mem (algebraMap R S) x.2

@[simp]
/--
lemma `algebraMapSubmonoid_self` / 引理 `algebraMapSubmonoid_self`

English:
lemma algebraMapSubmonoid_self
  given: (M : Submonoid R)
  statement: Algebra.algebraMapSubmonoid R M = M
  proof: Submonoid.map_id M

@[simp]

中文:
引理 algebraMapSubmonoid_self
  条件: (M : 子幺半群 R)
  结论: 代数.algebraMapSubmonoid R M = M
  证明: Submonoid.map_id M

@[simp]

Depends on / 依赖: Submonoid, Submonoid.map_id, map_id
-/
lemma algebraMapSubmonoid_self (M : Submonoid R) : Algebra.algebraMapSubmonoid R M = M :=
  Submonoid.map_id M

@[simp]
/--
lemma `algebraMapSubmonoid_powers` / 引理 `algebraMapSubmonoid_powers`

English:
lemma algebraMapSubmonoid_powers
  given: (r : R)
  proof: by
  simp [Algebra.algebraMapSubmonoid]

中文:
引理 algebraMapSubmonoid_powers
  条件: (r : R)
  证明: by
  simp [Algebra.algebraMapSubmonoid]

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, algebraMapSubmonoid
-/
lemma algebraMapSubmonoid_powers (r : R) :
    Algebra.algebraMapSubmonoid S (.powers r) = Submonoid.powers (algebraMap R S r) := by
  simp [Algebra.algebraMapSubmonoid]

/--
lemma `algebraMapSubmonoid_isUnit_le` / 引理 `algebraMapSubmonoid_isUnit_le`

English:
lemma algebraMapSubmonoid_isUnit_le
  proof: by
  rintro x ⟨y, hy, rfl⟩
  exact hy.map _

中文:
引理 algebraMapSubmonoid_isUnit_le
  证明: by
  rintro x ⟨y, hy, rfl⟩
  exact hy.map _

Depends on / 依赖: hy.map
-/
lemma algebraMapSubmonoid_isUnit_le :
    algebraMapSubmonoid S (IsUnit.submonoid R) <= IsUnit.submonoid S := by
  rintro x ⟨y, hy, rfl⟩
  exact hy.map _

end Semiring

section CommSemiring

variable [CommSemiring R]

/--
theorem `mul_sub_algebraMap_commutes` / 定理 `mul_sub_algebraMap_commutes`

English:
theorem mul_sub_algebraMap_commutes
  given: [Ring A] [Algebra R A] (x : A) (r : R)
  proof: by rw [mul_sub, ← commutes, sub_mul]

中文:
定理 mul_sub_algebraMap_commutes
  条件: [环 A] [代数 R A] (x : A) (r : R)
  证明: by rw [mul_sub, ← commutes, sub_mul]

Depends on / 依赖: commutes, mul_sub, sub_mul
-/
theorem mul_sub_algebraMap_commutes [Ring A] [Algebra R A] (x : A) (r : R) :
    x * (x - algebraMap R A r) = (x - algebraMap R A r) * x := by rw [mul_sub, ← commutes, sub_mul]

/--
theorem `mul_sub_algebraMap_pow_commutes` / 定理 `mul_sub_algebraMap_pow_commutes`

English:
theorem mul_sub_algebraMap_pow_commutes
  given: [Ring A] [Algebra R A] (x : A) (r : R) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']; rw [← mul_assoc]; rw [mul_sub_algebraMap_commutes]; rw [mul_assoc]; rw [ih]; rw [← mul_assoc]

中文:
定理 mul_sub_algebraMap_pow_commutes
  条件: [环 A] [代数 R A] (x : A) (r : R) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']; rw [← mul_assoc]; rw [mul_sub_algebraMap_commutes]; rw [mul_assoc]; rw [ih]; rw [← mul_assoc]

Depends on / 依赖: mul_assoc, mul_sub_algebraMap_commutes, pow_succ
-/
theorem mul_sub_algebraMap_pow_commutes [Ring A] [Algebra R A] (x : A) (r : R) (n : Nat) :
    x * (x - algebraMap R A r) ^ n = (x - algebraMap R A r) ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']; rw [← mul_assoc]; rw [mul_sub_algebraMap_commutes]; rw [mul_assoc]; rw [ih]; rw [← mul_assoc]

end CommSemiring

section Ring

/--
Definition of `semiringToRing` / `semiringToRing` 的定义

English:
abbreviation semiringToRing
  signature: (R : Type*) [CommRing R] [Semiring A] [Algebra R A]
  body: { __ := (inferInstance : Semiring A)
    __ := Module.addCommMonoidToAddCommGroup R
    intCast := fun z => algebraMap R A z
    intCast_ofNat := fun z => by simp only [Int.cast_natCast, map_natCast]
    intCast_negSucc := fun z => by simp }

中文:
缩写 semiringToRing
  签名: (R : 类型) [交换环 R] [半环 A] [代数 R A]
  定义体: { __ := (inferInstance : Semiring A)
    __ := Module.addCommMonoidToAddCommGroup R
    intCast := fun z => algebraMap R A z
    intCast_ofNat := fun z => by simp only [Int.cast_natCast, map_natCast]
    intCast_negSucc := fun z => by simp }

Depends on / 依赖: Int.cast_natCast, Module, Module.addCommMonoidToAddCommGroup, Semiring, addCommMonoidToAddCommGroup, algebraMap, cast_natCast, intCast, intCast_negSucc, intCast_ofNat, map_natCast
-/
abbrev semiringToRing (R : Type*) [CommRing R] [Semiring A] [Algebra R A] : Ring A :=
  { __ := (inferInstance : Semiring A)
    __ := Module.addCommMonoidToAddCommGroup R
    intCast := fun z => algebraMap R A z
    intCast_ofNat := fun z => by simp only [Int.cast_natCast, map_natCast]
    intCast_negSucc := fun z => by simp }

/--
Definition of `_root_.RingHom.commSemiringToCommRing` / `_root_.RingHom.commSemiringToCommRing` 的定义

English:
abbreviation _root_.RingHom.commSemiringToCommRing
  signature: {R A : Type*} [CommRing R] [CommSemiring A]
  body: let _ : Algebra R A := RingHom.toAlgebra φ
  { __ := Algebra.semiringToRing R
    mul_comm := CommMonoid.mul_comm }

中文:
缩写 _root_.环态射.commSemiringToCommRing
  签名: {R A : 类型} [交换环 R] [交换半环 A]
  定义体: let _ : Algebra R A := RingHom.toAlgebra φ
  { __ := Algebra.semiringToRing R
    mul_comm := CommMonoid.mul_comm }

Depends on / 依赖: Algebra, Algebra.semiringToRing, CommMonoid, CommMonoid.mul_comm, RingHom, RingHom.toAlgebra, mul_comm, semiringToRing, toAlgebra
-/
abbrev _root_.RingHom.commSemiringToCommRing {R A : Type*} [CommRing R] [CommSemiring A]
    (φ : R ->+* A) : CommRing A :=
  let _ : Algebra R A := RingHom.toAlgebra φ
  { __ := Algebra.semiringToRing R
    mul_comm := CommMonoid.mul_comm }

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

/--
Instance `End.instAlgebra` / 实例 `End.instAlgebra`

English:
instance End.instAlgebra
  signature: : Algebra R (Module.End S M)
  body: Algebra.ofModule smul_mul_assoc fun r f g => (smul_comm r f g).symm

中文:
实例 End.instAlgebra
  签名: : 代数 R (模.End S M)
  定义体: Algebra.ofModule smul_mul_assoc fun r f g => (smul_comm r f g).symm

Depends on / 依赖: Algebra, Algebra.ofModule, ofModule, smul_comm, smul_mul_assoc
-/
instance End.instAlgebra : Algebra R (Module.End S M) :=
  Algebra.ofModule smul_mul_assoc fun r f g => (smul_comm r f g).symm

-- to prove this is a special case of the above
example : Algebra R (Module.End R M) := End.instAlgebra _ _ _

/--
theorem `algebraMap_end_eq_smul_id` / 定理 `algebraMap_end_eq_smul_id`

English:
theorem algebraMap_end_eq_smul_id
  given: (a : R)
  statement: algebraMap R (End S M) a = a • LinearMap.id
  proof: rfl

@[simp]

中文:
定理 algebraMap_end_eq_smul_id
  条件: (a : R)
  结论: algebraMap R (End S M) a = a • 线性映射.id
  证明: rfl

@[simp]
-/
theorem algebraMap_end_eq_smul_id (a : R) : algebraMap R (End S M) a = a • LinearMap.id :=
  rfl

@[simp]
/--
theorem `algebraMap_end_apply` / 定理 `algebraMap_end_apply`

English:
theorem algebraMap_end_apply
  given: (a : R) (m : M)
  statement: algebraMap R (End S M) a m = a • m
  proof: rfl

@[simp]

中文:
定理 algebraMap_end_apply
  条件: (a : R) (m : M)
  结论: algebraMap R (End S M) a m = a • m
  证明: rfl

@[simp]
-/
theorem algebraMap_end_apply (a : R) (m : M) : algebraMap R (End S M) a m = a • m :=
  rfl

@[simp]
/--
theorem `ker_algebraMap_end` / 定理 `ker_algebraMap_end`

English:
theorem ker_algebraMap_end
  statement: (K : Type u) (V : Type v) [Semifield K] [AddCommMonoid V] [Module K V]
  proof: LinearMap.ker_smul _ _ ha

中文:
定理 ker_algebraMap_end
  结论: (K : 类型u) (V : 类型v) [半域 K] [加法交换幺半群 V] [模 K V]
  证明: LinearMap.ker_smul _ _ ha

Depends on / 依赖: LinearMap, LinearMap.ker_smul, ker_smul
-/
theorem ker_algebraMap_end (K : Type u) (V : Type v) [Semifield K] [AddCommMonoid V] [Module K V]
    (a : K) (ha : a != 0) : LinearMap.ker ((algebraMap K (End K V)) a) = ⊥ :=
  LinearMap.ker_smul _ _ ha

section

variable {R M}

/--
theorem `End.algebraMap_isUnit_inv_apply_eq_iff` / 定理 `End.algebraMap_isUnit_inv_apply_eq_iff`

English:
theorem End.algebraMap_isUnit_inv_apply_eq_iff
  statement: {x : R}
  proof: H ▸ (isUnit_apply_inv_apply_of_isUnit h m).symm
  mpr H := by
    apply_fun ⇑h.unit.val using ((isUnit_iff _).mp h).injective
    rw [H]
    simpa using Module.End.isUnit_apply_inv_apply_of_isUnit h (x • m')

中文:
定理 End.algebraMap_isUnit_inv_apply_eq_iff
  结论: {x : R}
  证明: H ▸ (isUnit_apply_inv_apply_of_isUnit h m).symm
  mpr H := by
    apply_fun ⇑h.unit.val using ((isUnit_iff _).mp h).injective
    rw [H]
    simpa using Module.End.isUnit_apply_inv_apply_of_isUnit h (x • m')

Depends on / 依赖: isUnit_apply_inv_apply_of_isUnit
-/
theorem End.algebraMap_isUnit_inv_apply_eq_iff {x : R}
    (h : IsUnit (algebraMap R (Module.End S M) x)) (m m' : M) :
    (↑(h.unit⁻¹) : Module.End S M) m = m' ↔ m = x • m' where
  mp H := H ▸ (isUnit_apply_inv_apply_of_isUnit h m).symm
  mpr H := by
    apply_fun ⇑h.unit.val using ((isUnit_iff _).mp h).injective
    rw [H]
    simpa using Module.End.isUnit_apply_inv_apply_of_isUnit h (x • m')

/--
theorem `End.algebraMap_isUnit_inv_apply_eq_iff'` / 定理 `End.algebraMap_isUnit_inv_apply_eq_iff'`

English:
theorem End.algebraMap_isUnit_inv_apply_eq_iff'
  statement: {x : R}
  proof: H ▸ (isUnit_apply_inv_apply_of_isUnit h m).symm
  mpr H := by
    apply_fun (↑h.unit : M -> M) using ((isUnit_iff _).mp h).injective
    rw [H]
.symm simpa using isUnit_apply_inv_apply_of_isUnit h (x • m')

中文:
定理 End.algebraMap_isUnit_inv_apply_eq_iff'
  结论: {x : R}
  证明: H ▸ (isUnit_apply_inv_apply_of_isUnit h m).symm
  mpr H := by
    apply_fun (↑h.unit : M -> M) using ((isUnit_iff _).mp h).injective
    rw [H]
.symm simpa using isUnit_apply_inv_apply_of_isUnit h (x • m')

Depends on / 依赖: isUnit_apply_inv_apply_of_isUnit
-/
theorem End.algebraMap_isUnit_inv_apply_eq_iff' {x : R}
    (h : IsUnit (algebraMap R (Module.End S M) x)) (m m' : M) :
    m' = (↑h.unit⁻¹ : Module.End S M) m ↔ m = x • m' where
  mp H := H ▸ (isUnit_apply_inv_apply_of_isUnit h m).symm
  mpr H := by
    apply_fun (↑h.unit : M -> M) using ((isUnit_iff _).mp h).injective
    rw [H]
.symm simpa using isUnit_apply_inv_apply_of_isUnit h (x • m')

end

end Module

namespace LinearMap

variable {R : Type*} {A : Type*} {B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

/--
theorem `map_algebraMap_mul` / 定理 `map_algebraMap_mul`

English:
theorem map_algebraMap_mul
  given: (f : A ->ₗ[R] B) (a : A) (r : R)
  proof: by
  rw [← Algebra.smul_def]; rw [← Algebra.smul_def]; rw [map_smul]

中文:
定理 map_algebraMap_mul
  条件: (f : A ->ₗ[R] B) (a : A) (r : R)
  证明: by
  rw [← Algebra.smul_def]; rw [← Algebra.smul_def]; rw [map_smul]

Depends on / 依赖: Algebra, Algebra.smul_def, map_smul, smul_def
-/
theorem map_algebraMap_mul (f : A ->ₗ[R] B) (a : A) (r : R) :
    f (algebraMap R A r * a) = algebraMap R B r * f a := by
  rw [← Algebra.smul_def]; rw [← Algebra.smul_def]; rw [map_smul]

/--
theorem `map_mul_algebraMap` / 定理 `map_mul_algebraMap`

English:
theorem map_mul_algebraMap
  given: (f : A ->ₗ[R] B) (a : A) (r : R)
  proof: by
  rw [← Algebra.commutes]; rw [← Algebra.commutes]; rw [map_algebraMap_mul]

中文:
定理 map_mul_algebraMap
  条件: (f : A ->ₗ[R] B) (a : A) (r : R)
  证明: by
  rw [← Algebra.commutes]; rw [← Algebra.commutes]; rw [map_algebraMap_mul]

Depends on / 依赖: Algebra, Algebra.commutes, commutes, map_algebraMap_mul
-/
theorem map_mul_algebraMap (f : A ->ₗ[R] B) (a : A) (r : R) :
    f (a * algebraMap R A r) = f a * algebraMap R B r := by
  rw [← Algebra.commutes]; rw [← Algebra.commutes]; rw [map_algebraMap_mul]

end LinearMap

section Nat

variable {R : Type*} [Semiring R]

-- Lower the priority so that `Algebra.id` is picked most of the time when working with
-- `ℕ`-algebras.
-- TODO: is this still needed?
/-- Semiring ⥤ ℕ-Alg -/
instance (priority := 99) Semiring.toNatAlgebra : Algebra Nat R where
  commutes' := Nat.cast_commute
  smul_def' _ _ := nsmul_eq_mul _ _
  algebraMap := Nat.castRingHom R

/--
Instance `nat_algebra_subsingleton` / 实例 `nat_algebra_subsingleton`

English:
instance nat_algebra_subsingleton
  signature: : Subsingleton (Algebra Nat R)
  body: ⟨fun P Q => by ext; simp⟩

@[simp]

中文:
实例 nat_algebra_subsingleton
  签名: : 子单例 (代数 自然数 R)
  定义体: ⟨fun P Q => by ext; simp⟩

@[simp]
-/
instance nat_algebra_subsingleton : Subsingleton (Algebra Nat R) :=
  ⟨fun P Q => by ext; simp⟩

@[simp]
/--
lemma `algebraMap_comp_natCast` / 引理 `algebraMap_comp_natCast`

English:
lemma algebraMap_comp_natCast
  given: (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
  proof: by
  ext; simp

中文:
引理 algebraMap_comp_natCast
  条件: (R A : 类型) [交换半环 R] [半环 A] [代数 R A]
  证明: by
  ext; simp
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
instance (priority := 99) Ring.toIntAlgebra : Algebra Int R where
  commutes' := Int.cast_commute
  smul_def' _ _ := zsmul_eq_mul _ _
  algebraMap := Int.castRingHom R

/-- A special case of `eq_intCast'` that happens to be true definitionally -/
@[simp]
/--
theorem `algebraMap_int_eq` / 定理 `algebraMap_int_eq`

English:
theorem algebraMap_int_eq
  statement: algebraMap Int R = Int.castRingHom R
  proof: rfl

中文:
定理 algebraMap_int_eq
  结论: algebraMap 整数 R = 整数.castRingHom R
  证明: rfl
-/
theorem algebraMap_int_eq : algebraMap Int R = Int.castRingHom R :=
  rfl

variable {R}

/--
Instance `int_algebra_subsingleton` / 实例 `int_algebra_subsingleton`

English:
instance int_algebra_subsingleton
  signature: : Subsingleton (Algebra Int R)
  body: ⟨fun P Q => Algebra.algebra_ext P Q RingHom.congr_fun Subsingleton.elim _ _⟩

@[simp]

中文:
实例 int_algebra_subsingleton
  签名: : 子单例 (代数 整数 R)
  定义体: ⟨fun P Q => Algebra.algebra_ext P Q RingHom.congr_fun Subsingleton.elim _ _⟩

@[simp]

Depends on / 依赖: Algebra, Algebra.algebra_ext, RingHom, RingHom.congr_fun, Subsingleton, Subsingleton.elim, algebra_ext, congr_fun
-/
instance int_algebra_subsingleton : Subsingleton (Algebra Int R) :=
⟨fun P Q => Algebra.algebra_ext P Q RingHom.congr_fun Subsingleton.elim _ _⟩

@[simp]
/--
lemma `algebraMap_comp_intCast` / 引理 `algebraMap_comp_intCast`

English:
lemma algebraMap_comp_intCast
  given: (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
  proof: by
  ext; simp

中文:
引理 algebraMap_comp_intCast
  条件: (R A : 类型) [交换环 R] [环 A] [代数 R A]
  证明: by
  ext; simp
-/
lemma algebraMap_comp_intCast (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    algebraMap R A ∘ Int.cast = Int.cast := by
  ext; simp

end Int

section FaithfulSMul

/--
theorem `_root_.NeZero.of_faithfulSMul` / 定理 `_root_.NeZero.of_faithfulSMul`

English:
theorem _root_.NeZero.of_faithfulSMul
  statement: (R A : Type*) [Semiring R] [Semiring A] [Module R A]
  proof: NeZero.nat_of_injective (f := ringHomEquivModuleIsScalarTower.symm ⟨_, ‹_›⟩)
    (faithfulSMul_iff_injective_smul_one R A).mp ‹_›

中文:
定理 _root_.NeZero.of_faithfulSMul
  结论: (R A : 类型) [半环 R] [半环 A] [模 R A]
  证明: NeZero.nat_of_injective (f := ringHomEquivModuleIsScalarTower.symm ⟨_, ‹_›⟩)
    (faithfulSMul_iff_injective_smul_one R A).mp ‹_›

Depends on / 依赖: NeZero, NeZero.nat_of_injective, faithfulSMul_iff_injective_smul_one, nat_of_injective, ringHomEquivModuleIsScalarTower, ringHomEquivModuleIsScalarTower.symm
-/
theorem _root_.NeZero.of_faithfulSMul (R A : Type*) [Semiring R] [Semiring A] [Module R A]
    [IsScalarTower R A A] [FaithfulSMul R A] (n : Nat) [NeZero (n : R)] :
    NeZero (n : A) :=
NeZero.nat_of_injective (f := ringHomEquivModuleIsScalarTower.symm ⟨_, ‹_›⟩)
    (faithfulSMul_iff_injective_smul_one R A).mp ‹_›

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

/--
lemma `faithfulSMul_iff_algebraMap_injective` / 引理 `faithfulSMul_iff_algebraMap_injective`

English:
lemma faithfulSMul_iff_algebraMap_injective
  statement: FaithfulSMul R A ↔ Injective (algebraMap R A)
  proof: by
  rw [faithfulSMul_iff_injective_smul_one]; rw [Algebra.algebraMap_eq_smul_one']

中文:
引理 faithfulSMul_iff_algebraMap_injective
  结论: 忠实标量乘法 R A ↔ 单射 (algebraMap R A)
  证明: by
  rw [faithfulSMul_iff_injective_smul_one]; rw [Algebra.algebraMap_eq_smul_one']

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, faithfulSMul_iff_injective_smul_one
-/
lemma faithfulSMul_iff_algebraMap_injective : FaithfulSMul R A ↔ Injective (algebraMap R A) := by
  rw [faithfulSMul_iff_injective_smul_one]; rw [Algebra.algebraMap_eq_smul_one']

variable [FaithfulSMul R A]

namespace FaithfulSMul

/--
lemma `algebraMap_injective` / 引理 `algebraMap_injective`

English:
lemma algebraMap_injective
  statement: Injective (algebraMap R A)
  proof: (faithfulSMul_iff_algebraMap_injective R A).mp inferInstance

@[simp]

中文:
引理 algebraMap_injective
  结论: 单射 (algebraMap R A)
  证明: (faithfulSMul_iff_algebraMap_injective R A).mp inferInstance

@[simp]

Depends on / 依赖: faithfulSMul_iff_algebraMap_injective
-/
lemma algebraMap_injective : Injective (algebraMap R A) :=
  (faithfulSMul_iff_algebraMap_injective R A).mp inferInstance

@[simp]
/--
lemma `algebraMap_eq_zero_iff` / 引理 `algebraMap_eq_zero_iff`

English:
lemma algebraMap_eq_zero_iff
  given: {r : R}
  statement: algebraMap R A r = 0 ↔ r = 0
  proof: map_eq_zero_iff (algebraMap R A) algebraMap_injective R A

@[simp]

中文:
引理 algebraMap_eq_zero_iff
  条件: {r : R}
  结论: algebraMap R A r = 0 ↔ r = 0
  证明: map_eq_zero_iff (algebraMap R A) algebraMap_injective R A

@[simp]

Depends on / 依赖: algebraMap, algebraMap_injective, map_eq_zero_iff
-/
lemma algebraMap_eq_zero_iff {r : R} : algebraMap R A r = 0 ↔ r = 0 :=
map_eq_zero_iff (algebraMap R A) algebraMap_injective R A

@[simp]
/--
lemma `algebraMap_eq_one_iff` / 引理 `algebraMap_eq_one_iff`

English:
lemma algebraMap_eq_one_iff
  given: {r : R}
  statement: algebraMap R A r = 1 ↔ r = 1
  proof: map_eq_one_iff _ FaithfulSMul.algebraMap_injective R A

中文:
引理 algebraMap_eq_one_iff
  条件: {r : R}
  结论: algebraMap R A r = 1 ↔ r = 1
  证明: map_eq_one_iff _ FaithfulSMul.algebraMap_injective R A

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, map_eq_one_iff
-/
lemma algebraMap_eq_one_iff {r : R} : algebraMap R A r = 1 ↔ r = 1 :=
map_eq_one_iff _ FaithfulSMul.algebraMap_injective R A

end FaithfulSMul

/-- If `R` embeds faithfully into `A` and `G` satisfies `SMulDistribClass G R A`, then
the `SMul` of `G` on `R` extends to a `MulSemiringAction`. -/
@[implicit_reducible]
/--
Definition of `mulSemiringActionOfSmulDistribClass` / `mulSemiringActionOfSmulDistribClass` 的定义

English:
definition mulSemiringActionOfSmulDistribClass
  signature: (G : Type*) [Monoid G]
  body: by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul']; rw [one_smul]
  smul_zero _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul']; rw [map_zero]; rw [smul_zero]
  mul_smul _ _ _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [alge

中文:
定义 mulSemiringActionOfSmulDistribClass
  签名: (G : 类型) [幺半群 G]
  定义体: by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul']; rw [one_smul]
  smul_zero _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul']; rw [map_zero]; rw [smul_zero]
  mul_smul _ _ _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [alge

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap, algebraMap.smul, algebraMap_injective, map_add, map_zero, mul_smul, one_smul, smul_add, smul_zero
-/
noncomputable def mulSemiringActionOfSmulDistribClass (G : Type*) [Monoid G]
    [MulSemiringAction G A] [SMul G R] [SMulDistribClass G R A] :
    MulSemiringAction G R where
  one_smul _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul']; rw [one_smul]
  smul_zero _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul']; rw [map_zero]; rw [smul_zero]
  mul_smul _ _ _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul']; rw [algebraMap.smul']; rw [algebraMap.smul']; rw [mul_smul]
  smul_add _ _ _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul']; rw [map_add]; rw [smul_add]; rw [← algebraMap.smul']; rw [← algebraMap.smul']; rw [← map_add]
  smul_one _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul']; rw [map_one]; rw [smul_one]
  smul_mul _ _ _ := by
    apply FaithfulSMul.algebraMap_injective R A
    rw [algebraMap.smul']; rw [map_mul]; rw [map_mul]; rw [algebraMap.smul']; rw [algebraMap.smul']; rw [MulSemiringAction.smul_mul]

namespace algebraMap

@[norm_cast, simp]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {a b : R}
  statement: (↑a : A) = ↑b ↔ a = b
  proof: (FaithfulSMul.algebraMap_injective _ _).eq_iff

@[norm_cast]

中文:
定理 coe_inj
  条件: {a b : R}
  结论: (↑a : A) = ↑b ↔ a = b
  证明: (FaithfulSMul.algebraMap_injective _ _).eq_iff

@[norm_cast]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, eq_iff
-/
theorem coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b :=
  (FaithfulSMul.algebraMap_injective _ _).eq_iff

@[norm_cast]
/--
theorem `coe_eq_zero_iff` / 定理 `coe_eq_zero_iff`

English:
theorem coe_eq_zero_iff
  given: (a : R)
  statement: (↑a : A) = 0 ↔ a = 0
  proof: FaithfulSMul.algebraMap_eq_zero_iff _ _

中文:
定理 coe_eq_zero_iff
  条件: (a : R)
  结论: (↑a : A) = 0 ↔ a = 0
  证明: FaithfulSMul.algebraMap_eq_zero_iff _ _

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_eq_zero_iff, algebraMap_eq_zero_iff
-/
theorem coe_eq_zero_iff (a : R) : (↑a : A) = 0 ↔ a = 0 :=
  FaithfulSMul.algebraMap_eq_zero_iff _ _

end algebraMap

/--
lemma `Algebra.charZero_of_charZero` / 引理 `Algebra.charZero_of_charZero`

English:
lemma Algebra.charZero_of_charZero
  given: [CharZero R]
  statement: CharZero A
  proof: have := algebraMap_comp_natCast R A
  ⟨this ▸ (FaithfulSMul.algebraMap_injective R A).comp CharZero.cast_injective⟩

中文:
引理 代数.charZero_of_charZero
  条件: [特征零 R]
  结论: 特征零 A
  证明: have := algebraMap_comp_natCast R A
  ⟨this ▸ (FaithfulSMul.algebraMap_injective R A).comp CharZero.cast_injective⟩

Depends on / 依赖: CharZero, CharZero.cast_injective, FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_comp_natCast, algebraMap_injective, cast_injective
-/
lemma Algebra.charZero_of_charZero [CharZero R] : CharZero A :=
  have := algebraMap_comp_natCast R A
  ⟨this ▸ (FaithfulSMul.algebraMap_injective R A).comp CharZero.cast_injective⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CharZero
  signature: R] : FaithfulSMul Nat R
  body: by
  simpa only [faithfulSMul_iff_algebraMap_injective] using (algebraMap Nat R).injective_nat

中文:
实例 [特征零
  签名: R] : 忠实标量乘法 自然数 R
  定义体: by
  simpa only [faithfulSMul_iff_algebraMap_injective] using (algebraMap Nat R).injective_nat

Depends on / 依赖: algebraMap, faithfulSMul_iff_algebraMap_injective, injective_nat
-/
instance [CharZero R] : FaithfulSMul Nat R := by
  simpa only [faithfulSMul_iff_algebraMap_injective] using (algebraMap Nat R).injective_nat

instance (R : Type*) [Ring R] [CharZero R] : FaithfulSMul Int R := by
  simpa only [faithfulSMul_iff_algebraMap_injective] using (algebraMap Int R).injective_int

end FaithfulSMul

section IsScalarTower

variable {R : Type*} [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable {M : Type*} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]

/--
theorem `algebra_compatible_smul` / 定理 `algebra_compatible_smul`

English:
theorem algebra_compatible_smul
  given: (r : R) (m : M)
  statement: r • m = (algebraMap R A) r • m
  proof: by
  rw [← one_smul A m]; rw [← smul_assoc]; rw [Algebra.smul_def]; rw [mul_one]; rw [one_smul]

@[simp]

中文:
定理 algebra_compatible_smul
  条件: (r : R) (m : M)
  结论: r • m = (algebraMap R A) r • m
  证明: by
  rw [← one_smul A m]; rw [← smul_assoc]; rw [Algebra.smul_def]; rw [mul_one]; rw [one_smul]

@[simp]

Depends on / 依赖: Algebra, Algebra.smul_def, mul_one, one_smul, smul_assoc, smul_def
-/
theorem algebra_compatible_smul (r : R) (m : M) : r • m = (algebraMap R A) r • m := by
  rw [← one_smul A m]; rw [← smul_assoc]; rw [Algebra.smul_def]; rw [mul_one]; rw [one_smul]

@[simp]
/--
theorem `algebraMap_smul` / 定理 `algebraMap_smul`

English:
theorem algebraMap_smul
  given: (r : R) (m : M)
  statement: (algebraMap R A) r • m = r • m
  proof: (algebra_compatible_smul A r m).symm

中文:
定理 algebraMap_smul
  条件: (r : R) (m : M)
  结论: (algebraMap R A) r • m = r • m
  证明: (algebra_compatible_smul A r m).symm

Depends on / 依赖: algebra_compatible_smul
-/
theorem algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • m = r • m :=
  (algebra_compatible_smul A r m).symm

/--
lemma `isSMulRegular_algebraMap_iff` / 引理 `isSMulRegular_algebraMap_iff`

English:
lemma isSMulRegular_algebraMap_iff
  given: {r : R}
  proof: (Equiv.refl M).isSMulRegular_congr (algebraMap_smul A r)

中文:
引理 isSMulRegular_algebraMap_iff
  条件: {r : R}
  证明: (Equiv.refl M).isSMulRegular_congr (algebraMap_smul A r)

Depends on / 依赖: Equiv.refl, algebraMap_smul, isSMulRegular_congr
-/
lemma isSMulRegular_algebraMap_iff {r : R} :
    IsSMulRegular M (algebraMap R A r) ↔ IsSMulRegular M r :=
  (Equiv.refl M).isSMulRegular_congr (algebraMap_smul A r)

variable {A}

-- see Note [lower instance priority]
-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980, as it is a very common path
instance (priority := 120) IsScalarTower.to_smulCommClass : SMulCommClass R A M :=
  ⟨fun r a m => by
    rw [algebra_compatible_smul A r (a • m)]; rw [smul_smul]; rw [Algebra.commutes]; rw [mul_smul]; rw [←
      algebra_compatible_smul]⟩

-- see Note [lower instance priority]
-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980, as it is a very common path
instance (priority := 110) IsScalarTower.to_smulCommClass' : SMulCommClass A R M :=
  SMulCommClass.symm _ _ _

/-- This has high priority because it is almost always the right instance when it applies. -/
instance (priority := high) Algebra.to_smulCommClass {R A} [CommSemiring R] [Semiring A]
    [Algebra R A] : SMulCommClass R A A :=
  IsScalarTower.to_smulCommClass

-- see Note [lower instance priority]
instance (priority := 100) {R S A : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
    [Algebra R A] [Algebra S A] :
    SMulCommClass R S A where
  smul_comm r s a := by
    rw [Algebra.smul_def]; rw [mul_smul_comm]; rw [← Algebra.smul_def]

/--
theorem `smul_algebra_smul_comm` / 定理 `smul_algebra_smul_comm`

English:
theorem smul_algebra_smul_comm
  given: (r : R) (a : A) (m : M)
  statement: a • r • m = r • a • m
  proof: smul_comm _ _ _

中文:
定理 smul_algebra_smul_comm
  条件: (r : R) (a : A) (m : M)
  结论: a • r • m = r • a • m
  证明: smul_comm _ _ _

Depends on / 依赖: smul_comm
-/
theorem smul_algebra_smul_comm (r : R) (a : A) (m : M) : a • r • m = r • a • m :=
  smul_comm _ _ _

end IsScalarTower

section FaithfulSMul
variable (R S A M : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A]

/--
lemma `NoZeroDivisors.of_faithfulSMul` / 引理 `NoZeroDivisors.of_faithfulSMul`

English:
lemma NoZeroDivisors.of_faithfulSMul
  given: [NoZeroDivisors A]
  statement: NoZeroDivisors R
  proof: (FaithfulSMul.algebraMap_injective R A).noZeroDivisors _ (by simp) (by simp)

中文:
引理 无零因子.of_faithfulSMul
  条件: [无零因子 A]
  结论: 无零因子 R
  证明: (FaithfulSMul.algebraMap_injective R A).noZeroDivisors _ (by simp) (by simp)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, noZeroDivisors
-/
lemma NoZeroDivisors.of_faithfulSMul [NoZeroDivisors A] : NoZeroDivisors R :=
  (FaithfulSMul.algebraMap_injective R A).noZeroDivisors _ (by simp) (by simp)

/--
lemma `IsCancelMulZero.of_faithfulSMul` / 引理 `IsCancelMulZero.of_faithfulSMul`

English:
lemma IsCancelMulZero.of_faithfulSMul
  given: [IsCancelMulZero A]
  statement: IsCancelMulZero R
  proof: (FaithfulSMul.algebraMap_injective R A).isCancelMulZero _ (by simp) (by simp)

中文:
引理 是乘零消去.of_faithfulSMul
  条件: [是乘零消去 A]
  结论: 是乘零消去 R
  证明: (FaithfulSMul.algebraMap_injective R A).isCancelMulZero _ (by simp) (by simp)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, isCancelMulZero
-/
lemma IsCancelMulZero.of_faithfulSMul [IsCancelMulZero A] : IsCancelMulZero R :=
  (FaithfulSMul.algebraMap_injective R A).isCancelMulZero _ (by simp) (by simp)

/--
lemma `IsDomain.of_faithfulSMul` / 引理 `IsDomain.of_faithfulSMul`

English:
lemma IsDomain.of_faithfulSMul
  given: [IsDomain A]
  statement: IsDomain R
  proof: (FaithfulSMul.algebraMap_injective R A).isDomain

中文:
引理 是整环.of_faithfulSMul
  条件: [是整环 A]
  结论: 是整环 R
  证明: (FaithfulSMul.algebraMap_injective R A).isDomain

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, isDomain
-/
lemma IsDomain.of_faithfulSMul [IsDomain A] : IsDomain R :=
  (FaithfulSMul.algebraMap_injective R A).isDomain

/--
lemma `Module.IsTorsionFree.of_faithfulSMul` / 引理 `Module.IsTorsionFree.of_faithfulSMul`

English:
lemma Module.IsTorsionFree.of_faithfulSMul
  statement: [Semiring S] [Module S R] [Module S A]
  proof: (FaithfulSMul.algebraMap_injective R A).moduleIsTorsionFree _
    (by simp [Algebra.algebraMap_eq_smul_one])

中文:
引理 模.是无挠.of_faithfulSMul
  结论: [半环 S] [模 S R] [模 S A]
  证明: (FaithfulSMul.algebraMap_injective R A).moduleIsTorsionFree _
    (by simp [Algebra.algebraMap_eq_smul_one])

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_eq_smul_one, algebraMap_injective, moduleIsTorsionFree
-/
lemma Module.IsTorsionFree.of_faithfulSMul [Semiring S] [Module S R] [Module S A]
    [IsScalarTower S R A] [IsTorsionFree S A] : IsTorsionFree S R :=
  (FaithfulSMul.algebraMap_injective R A).moduleIsTorsionFree _
    (by simp [Algebra.algebraMap_eq_smul_one])

/--
lemma `Module.IsTorsionFree.trans_faithfulSMul` / 引理 `Module.IsTorsionFree.trans_faithfulSMul`

English:
lemma Module.IsTorsionFree.trans_faithfulSMul
  statement: [Nontrivial R] [IsCancelMulZero A] [AddCommMonoid M]
  proof: .comap (algebraMap R A) (fun r hr => .of_ne_zero <| by simpa using hr.ne_zero) (by simp)

中文:
引理 模.是无挠.trans_faithfulSMul
  结论: [非平凡 R] [是乘零消去 A] [加法交换幺半群 M]
  证明: .comap (algebraMap R A) (fun r hr => .of_ne_zero <| by simpa using hr.ne_zero) (by simp)

Depends on / 依赖: algebraMap, hr.ne_zero, ne_zero, of_ne_zero
-/
lemma Module.IsTorsionFree.trans_faithfulSMul [Nontrivial R] [IsCancelMulZero A] [AddCommMonoid M]
    [Module A M] [Module R M] [IsTorsionFree A M] [IsScalarTower R A M] : IsTorsionFree R M :=
  .comap (algebraMap R A) (fun r hr => .of_ne_zero <| by simpa using hr.ne_zero) (by simp)

-- see Note [lower instance priority]
instance (priority := 100) FaithfulSMul.to_isTorsionFree [Nontrivial R] [IsCancelMulZero A] :
    IsTorsionFree R A := .trans_faithfulSMul R A A

end FaithfulSMul

namespace Module
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

instance (priority := 101) IsTorsionFree.to_faithfulSMul [IsCancelMulZero R] [Nontrivial A]
    [IsTorsionFree R A] : FaithfulSMul R A where
eq_of_smul_eq_smul h := smul_left_injective _ one_ne_zero h 1

variable [IsDomain R] [IsDomain A]

/--
lemma `isTorsionFree_iff_faithfulSMul` / 引理 `isTorsionFree_iff_faithfulSMul`

English:
lemma isTorsionFree_iff_faithfulSMul
  statement: IsTorsionFree R A ↔ FaithfulSMul R A
  proof: ⟨fun _ => inferInstance, fun _ => inferInstance⟩

中文:
引理 isTorsionFree_iff_faithfulSMul
  结论: 是无挠 R A ↔ 忠实标量乘法 R A
  证明: ⟨fun _ => inferInstance, fun _ => inferInstance⟩
-/
lemma isTorsionFree_iff_faithfulSMul : IsTorsionFree R A ↔ FaithfulSMul R A :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

/--
lemma `isTorsionFree_iff_algebraMap_injective` / 引理 `isTorsionFree_iff_algebraMap_injective`

English:
lemma isTorsionFree_iff_algebraMap_injective
  statement: IsTorsionFree R A ↔ Injective (algebraMap R A)
  proof: by
  rw [isTorsionFree_iff_faithfulSMul]; rw [faithfulSMul_iff_algebraMap_injective]

中文:
引理 isTorsionFree_iff_algebraMap_injective
  结论: 是无挠 R A ↔ 单射 (algebraMap R A)
  证明: by
  rw [isTorsionFree_iff_faithfulSMul]; rw [faithfulSMul_iff_algebraMap_injective]

Depends on / 依赖: faithfulSMul_iff_algebraMap_injective, isTorsionFree_iff_faithfulSMul
-/
lemma isTorsionFree_iff_algebraMap_injective : IsTorsionFree R A ↔ Injective (algebraMap R A) := by
  rw [isTorsionFree_iff_faithfulSMul]; rw [faithfulSMul_iff_algebraMap_injective]

end Module

@[deprecated (since := "2026-01-21")]
alias NoZeroSMulDivisors.iff_algebraMap_injective := isTorsionFree_iff_algebraMap_injective

@[deprecated (since := "2026-01-21")]
alias NoZeroSMulDivisors.iff_faithfulSMul := isTorsionFree_iff_faithfulSMul

example {R A} [CommSemiring R] [Semiring A] [Module R A] [SMulCommClass R A A]
    [IsScalarTower R A A] : Algebra R A :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

section invertibility

variable {R A B : Type*}
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/--
Definition of `Invertible.algebraMapOfInvertibleAlgebraMap` / `Invertible.algebraMapOfInvertibleAlgebraMap` 的定义

English:
abbreviation Invertible.algebraMapOfInvertibleAlgebraMap
  signature: (f : A ->ₗ[R] B) (hf : f 1 = 1) {r : R}
  body: f ⅟(algebraMap R A r)
  invOf_mul_self := by rw [← Algebra.commutes, ← Algebra.smul_def, ← map_smul, Algebra.smul_def,
    mul_invOf_self, hf]
  mul_invOf_self := by rw [← Algebra.smul_def, ← map_smul, Algebra.smul_def, mul_invOf_self, hf]

中文:
缩写 可逆.algebraMapOfInvertibleAlgebraMap
  签名: (f : A ->ₗ[R] B) (hf : f 1 = 1) {r : R}
  定义体: f ⅟(algebraMap R A r)
  invOf_mul_self := by rw [← Algebra.commutes, ← Algebra.smul_def, ← map_smul, Algebra.smul_def,
    mul_invOf_self, hf]
  mul_invOf_self := by rw [← Algebra.smul_def, ← map_smul, Algebra.smul_def, mul_invOf_self, hf]

Depends on / 依赖: algebraMap
-/
abbrev Invertible.algebraMapOfInvertibleAlgebraMap (f : A ->ₗ[R] B) (hf : f 1 = 1) {r : R}
    (h : Invertible (algebraMap R A r)) : Invertible (algebraMap R B r) where
  invOf := f ⅟(algebraMap R A r)
  invOf_mul_self := by rw [← Algebra.commutes, ← Algebra.smul_def, ← map_smul, Algebra.smul_def,
    mul_invOf_self, hf]
  mul_invOf_self := by rw [← Algebra.smul_def, ← map_smul, Algebra.smul_def, mul_invOf_self, hf]

/--
lemma `IsUnit.algebraMap_of_algebraMap` / 引理 `IsUnit.algebraMap_of_algebraMap`

English:
lemma IsUnit.algebraMap_of_algebraMap
  statement: (f : A ->ₗ[R] B) (hf : f 1 = 1) {r : R}
  proof: let ⟨i⟩ := nonempty_invertible h
  letI := Invertible.algebraMapOfInvertibleAlgebraMap f hf i
  isUnit_of_invertible _

中文:
引理 是单位.algebraMap_of_algebraMap
  结论: (f : A ->ₗ[R] B) (hf : f 1 = 1) {r : R}
  证明: let ⟨i⟩ := nonempty_invertible h
  letI := Invertible.algebraMapOfInvertibleAlgebraMap f hf i
  isUnit_of_invertible _

Depends on / 依赖: Invertible, Invertible.algebraMapOfInvertibleAlgebraMap, algebraMapOfInvertibleAlgebraMap, isUnit_of_invertible, nonempty_invertible
-/
lemma IsUnit.algebraMap_of_algebraMap (f : A ->ₗ[R] B) (hf : f 1 = 1) {r : R}
    (h : IsUnit (algebraMap R A r)) : IsUnit (algebraMap R B r) :=
  let ⟨i⟩ := nonempty_invertible h
  letI := Invertible.algebraMapOfInvertibleAlgebraMap f hf i
  isUnit_of_invertible _

end invertibility

section algebraMap

variable {F E : Type*} [CommSemiring F] [Semiring E] [Algebra F E] (b : F ->ₗ[F] E)

/--
theorem `injective_algebraMap_of_linearMap` / 定理 `injective_algebraMap_of_linearMap`

English:
theorem injective_algebraMap_of_linearMap
  given: (hb : Injective b)
  proof: fun x y e => hb by
  rw [← mul_one x]; rw [← mul_one y]; rw [← smul_eq_mul]; rw [← smul_eq_mul]; rw [map_smul]; rw [map_smul]; rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [e]

中文:
定理 injective_algebraMap_of_linearMap
  条件: (hb : 单射 b)
  证明: fun x y e => hb by
  rw [← mul_one x]; rw [← mul_one y]; rw [← smul_eq_mul]; rw [← smul_eq_mul]; rw [map_smul]; rw [map_smul]; rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [e]

Depends on / 依赖: Algebra, Algebra.smul_def, map_smul, mul_one, smul_def, smul_eq_mul
-/
theorem injective_algebraMap_of_linearMap (hb : Injective b) :
Injective (algebraMap F E) := fun x y e => hb by
  rw [← mul_one x]; rw [← mul_one y]; rw [← smul_eq_mul]; rw [← smul_eq_mul]; rw [map_smul]; rw [map_smul]; rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [e]

/--
theorem `surjective_algebraMap_of_linearMap` / 定理 `surjective_algebraMap_of_linearMap`

English:
theorem surjective_algebraMap_of_linearMap
  given: (hb : Surjective b)
  proof: fun x => by
  obtain ⟨x, rfl⟩ := hb x
  obtain ⟨y, hy⟩ := hb (b 1 * b 1)
  refine ⟨x * y, ?_⟩
  obtain ⟨z, hz⟩ := hb 1
  apply_fun (x • z • ·) at hy
  rwa [← map_smul, smul_eq_mul, mul_comm, ← smul_mul_assoc, ← map_smul _ z, smul_eq_mul, mul_one,
    ← smul_eq_mul, map_smul, hz, one_mul, ← map_smul,

中文:
定理 surjective_algebraMap_of_linearMap
  条件: (hb : 满射 b)
  证明: fun x => by
  obtain ⟨x, rfl⟩ := hb x
  obtain ⟨y, hy⟩ := hb (b 1 * b 1)
  refine ⟨x * y, ?_⟩
  obtain ⟨z, hz⟩ := hb 1
  apply_fun (x • z • ·) at hy
  rwa [← map_smul, smul_eq_mul, mul_comm, ← smul_mul_assoc, ← map_smul _ z, smul_eq_mul, mul_one,
    ← smul_eq_mul, map_smul, hz, one_mul, ← map_smul,

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, apply_fun, map_smul, mul_comm, mul_one, one_mul, smul_eq_mul, smul_mul_assoc, smul_smul
-/
theorem surjective_algebraMap_of_linearMap (hb : Surjective b) :
    Surjective (algebraMap F E) := fun x => by
  obtain ⟨x, rfl⟩ := hb x
  obtain ⟨y, hy⟩ := hb (b 1 * b 1)
  refine ⟨x * y, ?_⟩
  obtain ⟨z, hz⟩ := hb 1
  apply_fun (x • z • ·) at hy
  rwa [← map_smul, smul_eq_mul, mul_comm, ← smul_mul_assoc, ← map_smul _ z, smul_eq_mul, mul_one,
    ← smul_eq_mul, map_smul, hz, one_mul, ← map_smul, smul_eq_mul, mul_one, smul_smul,
    ← Algebra.algebraMap_eq_smul_one] at hy

/--
theorem `bijective_algebraMap_of_linearMap` / 定理 `bijective_algebraMap_of_linearMap`

English:
theorem bijective_algebraMap_of_linearMap
  given: (hb : Bijective b)
  proof: ⟨injective_algebraMap_of_linearMap b hb.1, surjective_algebraMap_of_linearMap b hb.2⟩

中文:
定理 bijective_algebraMap_of_linearMap
  条件: (hb : 双射 b)
  证明: ⟨injective_algebraMap_of_linearMap b hb.1, surjective_algebraMap_of_linearMap b hb.2⟩

Depends on / 依赖: injective_algebraMap_of_linearMap, surjective_algebraMap_of_linearMap
-/
theorem bijective_algebraMap_of_linearMap (hb : Bijective b) :
    Bijective (algebraMap F E) :=
  ⟨injective_algebraMap_of_linearMap b hb.1, surjective_algebraMap_of_linearMap b hb.2⟩

/--
theorem `bijective_algebraMap_of_linearEquiv` / 定理 `bijective_algebraMap_of_linearEquiv`

English:
theorem bijective_algebraMap_of_linearEquiv
  given: (b : F ≃ₗ[F] E)
  proof: bijective_algebraMap_of_linearMap _ b.bijective

中文:
定理 bijective_algebraMap_of_linearEquiv
  条件: (b : F ≃ₗ[F] E)
  证明: bijective_algebraMap_of_linearMap _ b.bijective

Depends on / 依赖: b.bijective, bijective, bijective_algebraMap_of_linearMap
-/
theorem bijective_algebraMap_of_linearEquiv (b : F ≃ₗ[F] E) :
    Bijective (algebraMap F E) :=
  bijective_algebraMap_of_linearMap _ b.bijective

end algebraMap

section surjective

variable {R S} [CommSemiring R] [Semiring S] [Algebra R S]
variable {M N} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S M] [IsScalarTower R S M]
variable [Module R N] [Module S N] [IsScalarTower R S N]

/--
Definition of `LinearMap.extendScalarsOfSurjectiveEquiv` / `LinearMap.extendScalarsOfSurjectiveEquiv` 的定义

English:
definition LinearMap.extendScalarsOfSurjectiveEquiv
  signature: (h : Surjective (algebraMap R S))
  body: { __ := f, map_smul' := fun r x => by obtain ⟨r, rfl⟩ := h r; simp }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f.restrictScalars S

中文:
定义 线性映射.extendScalarsOfSurjectiveEquiv
  签名: (h : 满射 (algebraMap R S))
  定义体: { __ := f, map_smul' := fun r x => by obtain ⟨r, rfl⟩ := h r; simp }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f.restrictScalars S

Depends on / 依赖: map_smul
-/
def LinearMap.extendScalarsOfSurjectiveEquiv (h : Surjective (algebraMap R S)) :
    (M ->ₗ[R] N) ≃ₗ[R] (M ->ₗ[S] N) where
  toFun f := { __ := f, map_smul' := fun r x => by obtain ⟨r, rfl⟩ := h r; simp }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f.restrictScalars S

/--
Definition of `LinearMap.extendScalarsOfSurjective` / `LinearMap.extendScalarsOfSurjective` 的定义

English:
abbreviation LinearMap.extendScalarsOfSurjective
  signature: (h : Surjective (algebraMap R S))
  body: extendScalarsOfSurjectiveEquiv h l

中文:
缩写 线性映射.extendScalarsOfSurjective
  签名: (h : 满射 (algebraMap R S))
  定义体: extendScalarsOfSurjectiveEquiv h l

Depends on / 依赖: extendScalarsOfSurjectiveEquiv
-/
abbrev LinearMap.extendScalarsOfSurjective (h : Surjective (algebraMap R S))
    (l : M ->ₗ[R] N) : M ->ₗ[S] N :=
  extendScalarsOfSurjectiveEquiv h l

/--
Definition of `LinearEquiv.extendScalarsOfSurjective` / `LinearEquiv.extendScalarsOfSurjective` 的定义

English:
definition LinearEquiv.extendScalarsOfSurjective
  signature: (h : Surjective (algebraMap R S))
  body: f
  map_smul' r x := by obtain ⟨r, rfl⟩ := h r; simp

中文:
定义 线性等价.extendScalarsOfSurjective
  签名: (h : 满射 (algebraMap R S))
  定义体: f
  map_smul' r x := by obtain ⟨r, rfl⟩ := h r; simp
-/
def LinearEquiv.extendScalarsOfSurjective (h : Surjective (algebraMap R S))
    (f : M ≃ₗ[R] N) : M ≃ₗ[S] N where
  __ := f
  map_smul' r x := by obtain ⟨r, rfl⟩ := h r; simp

variable (h : Surjective (algebraMap R S))

@[simp]
/--
lemma `LinearMap.extendScalarsOfSurjective_apply` / 引理 `LinearMap.extendScalarsOfSurjective_apply`

English:
lemma LinearMap.extendScalarsOfSurjective_apply
  given: (l : M ->ₗ[R] N) (x)
  proof: rfl

@[simp]

中文:
引理 线性映射.extendScalarsOfSurjective_apply
  条件: (l : M ->ₗ[R] N) (x)
  证明: rfl

@[simp]
-/
lemma LinearMap.extendScalarsOfSurjective_apply (l : M ->ₗ[R] N) (x) :
    l.extendScalarsOfSurjective h x = l x := rfl

@[simp]
/--
lemma `LinearEquiv.extendScalarsOfSurjective_apply` / 引理 `LinearEquiv.extendScalarsOfSurjective_apply`

English:
lemma LinearEquiv.extendScalarsOfSurjective_apply
  given: (f : M ≃ₗ[R] N) (x)
  proof: rfl

@[simp]

中文:
引理 线性等价.extendScalarsOfSurjective_apply
  条件: (f : M ≃ₗ[R] N) (x)
  证明: rfl

@[simp]
-/
lemma LinearEquiv.extendScalarsOfSurjective_apply (f : M ≃ₗ[R] N) (x) :
    f.extendScalarsOfSurjective h x = f x := rfl

@[simp]
/--
lemma `LinearEquiv.extendScalarsOfSurjective_symm` / 引理 `LinearEquiv.extendScalarsOfSurjective_symm`

English:
lemma LinearEquiv.extendScalarsOfSurjective_symm
  given: (f : M ≃ₗ[R] N)
  proof: rfl

中文:
引理 线性等价.extendScalarsOfSurjective_symm
  条件: (f : M ≃ₗ[R] N)
  证明: rfl
-/
lemma LinearEquiv.extendScalarsOfSurjective_symm (f : M ≃ₗ[R] N) :
    (f.extendScalarsOfSurjective h).symm = f.symm.extendScalarsOfSurjective h := rfl

end surjective

namespace algebraMap

section CommSemiringCommSemiring

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {ι : Type*} {s : Finset ι}

@[norm_cast]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (a : ι -> R)
  statement: (↑(∏ i in s, a i : R) : A) = ∏ i in s, (↑(a i) : A)
  proof: map_prod (algebraMap R A) a s

@[norm_cast]

中文:
定理 coe_prod
  条件: (a : ι -> R)
  结论: (↑(∏ i in s, a i : R) : A) = ∏ i in s, (↑(a i) : A)
  证明: map_prod (algebraMap R A) a s

@[norm_cast]

Depends on / 依赖: FreeMagma, FreeMagma.repr, algebraMap, map_prod
-/
theorem coe_prod (a : ι -> R) : (↑(∏ i in s, a i : R) : A) = ∏ i in s, (↑(a i) : A) :=
  map_prod (algebraMap R A) a s

@[norm_cast]
/--
theorem `coe_sum` / 定理 `coe_sum`

English:
theorem coe_sum
  given: (a : ι -> R)
  statement: ↑(∑ i in s, a i) = ∑ i in s, (↑(a i) : A)
  proof: map_sum (algebraMap R A) a s

中文:
定理 coe_sum
  条件: (a : ι -> R)
  结论: ↑(∑ i in s, a i) = ∑ i in s, (↑(a i) : A)
  证明: map_sum (algebraMap R A) a s

Depends on / 依赖: algebraMap, map_sum
-/
theorem coe_sum (a : ι -> R) : ↑(∑ i in s, a i) = ∑ i in s, (↑(a i) : A) :=
  map_sum (algebraMap R A) a s

end CommSemiringCommSemiring

end algebraMap
