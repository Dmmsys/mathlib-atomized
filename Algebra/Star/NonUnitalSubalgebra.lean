/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Center
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.Prod

/-!
# Non-unital Star Subalgebras

In this file we define `NonUnitalStarSubalgebra`s and the usual operations on them
(`map`, `comap`).

## TODO

* once we have scalar actions by semigroups (as opposed to monoids), implement the action of a
  non-unital subalgebra on the larger algebra.
-/

@[expose] public section

open Module

namespace StarMemClass

/--
Instance `instInvolutiveStar` / 实例 `instInvolutiveStar`

English:
instance instInvolutiveStar
  signature: {S R : Type*} [InvolutiveStar R] [SetLike S R] [StarMemClass S R]
  body: Subtype.ext star_star (r : R)

中文:
实例 instInvolutiveStar
  签名: {S R : 类型} [InvolutiveStar R] [集合状 S R] [StarMem类 S R]
  定义体: Subtype.ext star_star (r : R)

Depends on / 依赖: Subtype, Subtype.ext, star_star
-/
instance instInvolutiveStar {S R : Type*} [InvolutiveStar R] [SetLike S R] [StarMemClass S R]
    (s : S) : InvolutiveStar s where
star_involutive r := Subtype.ext star_star (r : R)

/--
Instance `instStarMul` / 实例 `instStarMul`

English:
instance instStarMul
  signature: {S R : Type*} [Mul R] [StarMul R] [SetLike S R]
  body: Subtype.ext star_mul _ _

中文:
实例 instStarMul
  签名: {S R : 类型} [乘法 R] [StarMul R] [集合状 S R]
  定义体: Subtype.ext star_mul _ _

Depends on / 依赖: Subtype, Subtype.ext, star_mul
-/
instance instStarMul {S R : Type*} [Mul R] [StarMul R] [SetLike S R]
    [MulMemClass S R] [StarMemClass S R] (s : S) : StarMul s where
star_mul _ _ := Subtype.ext star_mul _ _

/--
Instance `instStarAddMonoid` / 实例 `instStarAddMonoid`

English:
instance instStarAddMonoid
  signature: {S R : Type*} [AddMonoid R] [StarAddMonoid R] [SetLike S R]
  body: Subtype.ext star_add _ _

中文:
实例 instStarAddMonoid
  签名: {S R : 类型} [加法幺半群 R] [StarAdd幺半群 R] [集合状 S R]
  定义体: Subtype.ext star_add _ _

Depends on / 依赖: Subtype, Subtype.ext, star_add
-/
instance instStarAddMonoid {S R : Type*} [AddMonoid R] [StarAddMonoid R] [SetLike S R]
    [AddSubmonoidClass S R] [StarMemClass S R] (s : S) : StarAddMonoid s where
star_add _ _ := Subtype.ext star_add _ _

/--
Instance `instStarRing` / 实例 `instStarRing`

English:
instance instStarRing
  signature: {S R : Type*} [NonUnitalNonAssocSemiring R] [StarRing R] [SetLike S R]
  body: { StarMemClass.instStarMul s, StarMemClass.instStarAddMonoid s with }

中文:
实例 instStarRing
  签名: {S R : 类型} [非幺非结合半环 R] [对合环 R] [集合状 S R]
  定义体: { StarMemClass.instStarMul s, StarMemClass.instStarAddMonoid s with }

Depends on / 依赖: StarMemClass, StarMemClass.instStarAddMonoid, StarMemClass.instStarMul, instStarAddMonoid, instStarMul
-/
instance instStarRing {S R : Type*} [NonUnitalNonAssocSemiring R] [StarRing R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] [StarMemClass S R] (s : S) : StarRing s :=
  { StarMemClass.instStarMul s, StarMemClass.instStarAddMonoid s with }

/--
Instance `instStarModule` / 实例 `instStarModule`

English:
instance instStarModule
  signature: {S : Type*} (R : Type*) {M : Type*} [Star R] [Star M] [SMul R M]
  body: Subtype.ext star_smul _ _

中文:
实例 instStarModule
  签名: {S : 类型} (R : 类型) {M : 类型} [对合 R] [对合 M] [标量乘法 R M]
  定义体: Subtype.ext star_smul _ _

Depends on / 依赖: Subtype, Subtype.ext, star_smul
-/
instance instStarModule {S : Type*} (R : Type*) {M : Type*} [Star R] [Star M] [SMul R M]
    [StarModule R M] [SetLike S M] [SMulMemClass S R M] [StarMemClass S M] (s : S) :
    StarModule R s where
star_smul _ _ := Subtype.ext star_smul _ _

end StarMemClass

universe u u' v v' w w' w''

variable {F : Type v'} {R' : Type u'} {R : Type u}
variable {A : Type v} {B : Type w} {C : Type w'}

namespace NonUnitalStarSubalgebraClass

variable [CommSemiring R] [NonUnitalNonAssocSemiring A]
variable [Star A] [Module R A]
variable {S : Type w''} [SetLike S A] [NonUnitalSubsemiringClass S A]
variable [hSR : SMulMemClass S R A] [StarMemClass S A] (s : S)

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (s : S)
  body: { NonUnitalSubalgebraClass.subtype s with
    toFun := Subtype.val
    map_star' := fun _ => rfl }

中文:
定义 subtype
  签名: (s : S)
  定义体: { NonUnitalSubalgebraClass.subtype s with
    toFun := Subtype.val
    map_star' := fun _ => rfl }

Depends on / 依赖: NonUnitalSubalgebraClass, NonUnitalSubalgebraClass.subtype, Subtype, Subtype.val, map_star, subtype
-/
def subtype (s : S) : s ->⋆ₙₐ[R] A :=
  { NonUnitalSubalgebraClass.subtype s with
    toFun := Subtype.val
    map_star' := fun _ => rfl }

variable {s} in
@[simp]
/--
lemma `subtype_apply` / 引理 `subtype_apply`

English:
lemma subtype_apply
  given: (x : s)
  statement: subtype s x = x
  proof: rfl

中文:
引理 subtype_apply
  条件: (x : s)
  结论: subtype s x = x
  证明: rfl
-/
lemma subtype_apply (x : s) : subtype s x = x := rfl

/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  proof: Subtype.coe_injective

@[simp]

中文:
引理 subtype_injective
  证明: Subtype.coe_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
lemma subtype_injective :
    Function.Injective (subtype s) :=
  Subtype.coe_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: (subtype s : s -> A) = Subtype.val
  proof: rfl

中文:
定理 coe_subtype
  结论: (subtype s : s -> A) = 子类型.val
  证明: rfl
-/
theorem coe_subtype : (subtype s : s -> A) = Subtype.val :=
  rfl

end NonUnitalStarSubalgebraClass

/--
Definition of `NonUnitalStarSubalgebra` / `NonUnitalStarSubalgebra` 的定义

English:
structure NonUnitalStarSubalgebra
  parameters: (R : Type u) (A : Type v) [CommSemiring R]
  extends: NonUnitalSubalgebra R A
  axioms and operations (1):
    - star_mem' : forall {a : A} (_ha : a in carrier), star a in carrier

中文:
结构 非幺对合子代数
  参数: (R : 类型u) (A : 类型v) [交换半环 R]
  继承: NonUnital子代数 R A
  公理与运算 (1 个):
    - star_mem' : 对任意 {a : A} (_ha : a in carrier), star a in carrier
-/
structure NonUnitalStarSubalgebra (R : Type u) (A : Type v) [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A] : Type v
    extends NonUnitalSubalgebra R A where
  /-- The `carrier` of a `NonUnitalStarSubalgebra` is closed under the `star` operation. -/
  star_mem' : forall {a : A} (_ha : a in carrier), star a in carrier

/-- Reinterpret a `NonUnitalStarSubalgebra` as a `NonUnitalSubalgebra`. -/
add_decl_doc NonUnitalStarSubalgebra.toNonUnitalSubalgebra

namespace NonUnitalStarSubalgebra

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

/--
Instance `instSetLike` / 实例 `instSetLike`

English:
instance instSetLike
  signature: : SetLike (NonUnitalStarSubalgebra R A) A where
  body: s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

中文:
实例 instSetLike
  签名: : 集合状 (非幺对合子代数 R A) A where
  定义体: s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

Depends on / 依赖: carrier, s.carrier
-/
instance instSetLike : SetLike (NonUnitalStarSubalgebra R A) A where
  coe {s} := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (NonUnitalStarSubalgebra R A)
  body: .ofSetLike (NonUnitalStarSubalgebra R A) A

中文:
实例 :
  签名: 偏序 (非幺对合子代数 R A)
  定义体: .ofSetLike (NonUnitalStarSubalgebra R A) A

Depends on / 依赖: NonUnitalStarSubalgebra, ofSetLike
-/
instance : PartialOrder (NonUnitalStarSubalgebra R A) := .ofSetLike (NonUnitalStarSubalgebra R A) A

/-- The actual `NonUnitalStarSubalgebra` obtained from an element of a type satisfying
`NonUnitalSubsemiringClass`, `SMulMemClass` and `StarMemClass`. -/
@[simps]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: {S R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
  body: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  smul_mem' := SMulMemClass.smul_mem
  star_mem' := star_mem

中文:
定义 ofClass
  签名: {S R A : 类型} [交换半环 R] [非幺非结合半环 A] [模 R A] [对合 A]
  定义体: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  smul_mem' := SMulMemClass.smul_mem
  star_mem' := star_mem
-/
def ofClass {S R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [SetLike S A] [NonUnitalSubsemiringClass S A] [SMulMemClass S R A] [StarMemClass S A]
    (s : S) : NonUnitalStarSubalgebra R A where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  smul_mem' := SMulMemClass.smul_mem
  star_mem' := star_mem

instance (priority := 100) : CanLift (Set A) (NonUnitalStarSubalgebra R A) (↑)
    (fun s => 0 in s ∧ (forall {x y}, x in s -> y in s -> x + y in s) ∧ (forall {x y}, x in s -> y in s -> x * y in s) ∧
      (forall (r : R) {x}, x in s -> r • x in s) ∧ forall {x}, x in s -> star x in s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        mul_mem' := h.2.2.1
        smul_mem' := h.2.2.2.1
        star_mem' := h.2.2.2.2 },
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
    NonUnitalSubsemiringClass (NonUnitalStarSubalgebra R A) A where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'

/--
Instance `instSMulMemClass` / 实例 `instSMulMemClass`

English:
instance instSMulMemClass
  signature: : SMulMemClass (NonUnitalStarSubalgebra R A) R A where
  body: s.smul_mem'

中文:
实例 instSMulMemClass
  签名: : SMulMem类 (非幺对合子代数 R A) R A where
  定义体: s.smul_mem'

Depends on / 依赖: s.smul_mem, smul_mem
-/
instance instSMulMemClass : SMulMemClass (NonUnitalStarSubalgebra R A) R A where
  smul_mem {s} := s.smul_mem'

/--
Instance `instStarMemClass` / 实例 `instStarMemClass`

English:
instance instStarMemClass
  signature: : StarMemClass (NonUnitalStarSubalgebra R A) A where
  body: s.star_mem'

中文:
实例 instStarMemClass
  签名: : StarMem类 (非幺对合子代数 R A) A where
  定义体: s.star_mem'

Depends on / 依赖: s.star_mem, star_mem
-/
instance instStarMemClass : StarMemClass (NonUnitalStarSubalgebra R A) A where
  star_mem {s} := s.star_mem'

/--
Instance `instNonUnitalSubringClass` / 实例 `instNonUnitalSubringClass`

English:
instance instNonUnitalSubringClass
  signature: {R : Type u} {A : Type v} [CommRing R] [NonUnitalNonAssocRing A]
  body: { NonUnitalStarSubalgebra.instNonUnitalSubsemiringClass with
    neg_mem := fun _S {x} hx => neg_one_smul R x ▸ SMulMemClass.smul_mem _ hx }

中文:
实例 instNonUnitalSubringClass
  签名: {R : 类型u} {A : 类型v} [交换环 R] [非幺非结合环 A]
  定义体: { NonUnitalStarSubalgebra.instNonUnitalSubsemiringClass with
    neg_mem := fun _S {x} hx => neg_one_smul R x ▸ SMulMemClass.smul_mem _ hx }

Depends on / 依赖: NonUnitalStarSubalgebra, NonUnitalStarSubalgebra.instNonUnitalSubsemiringClass, SMulMemClass, SMulMemClass.smul_mem, instNonUnitalSubsemiringClass, neg_mem, neg_one_smul, smul_mem
-/
instance instNonUnitalSubringClass {R : Type u} {A : Type v} [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [Star A] : NonUnitalSubringClass (NonUnitalStarSubalgebra R A) A :=
  { NonUnitalStarSubalgebra.instNonUnitalSubsemiringClass with
    neg_mem := fun _S {x} hx => neg_one_smul R x ▸ SMulMemClass.smul_mem _ hx }

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : NonUnitalStarSubalgebra R A} {x : A}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

@[ext]

中文:
定理 mem_carrier
  条件: {s : 非幺对合子代数 R A} {x : A}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

@[ext]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : NonUnitalStarSubalgebra R A} {x : A} : x in s.carrier ↔ x in s :=
  Iff.rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : NonUnitalStarSubalgebra R A} (h : forall x : A, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

@[simp]

中文:
定理 ext
  条件: {S T : 非幺对合子代数 R A} (h : 对任意 x : A, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

@[simp]

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : NonUnitalStarSubalgebra R A} (h : forall x : A, x in S ↔ x in T) : S = T :=
  SetLike.ext h

@[simp]
/--
theorem `mem_toNonUnitalSubalgebra` / 定理 `mem_toNonUnitalSubalgebra`

English:
theorem mem_toNonUnitalSubalgebra
  given: {S : NonUnitalStarSubalgebra R A} {x}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toNonUnitalSubalgebra
  条件: {S : 非幺对合子代数 R A} {x}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toNonUnitalSubalgebra {S : NonUnitalStarSubalgebra R A} {x} :
    x in S.toNonUnitalSubalgebra ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `coe_toNonUnitalSubalgebra` / 定理 `coe_toNonUnitalSubalgebra`

English:
theorem coe_toNonUnitalSubalgebra
  given: (S : NonUnitalStarSubalgebra R A)
  proof: rfl

中文:
定理 coe_toNonUnitalSubalgebra
  条件: (S : 非幺对合子代数 R A)
  证明: rfl
-/
theorem coe_toNonUnitalSubalgebra (S : NonUnitalStarSubalgebra R A) :
    (↑S.toNonUnitalSubalgebra : Set A) = S :=
  rfl

/--
theorem `toNonUnitalSubalgebra_injective` / 定理 `toNonUnitalSubalgebra_injective`

English:
theorem toNonUnitalSubalgebra_injective
  proof: fun S T h =>
  ext fun x => by rw [← mem_toNonUnitalSubalgebra, ← mem_toNonUnitalSubalgebra, h]

中文:
定理 toNonUnitalSubalgebra_injective
  证明: fun S T h =>
  ext fun x => by rw [← mem_toNonUnitalSubalgebra, ← mem_toNonUnitalSubalgebra, h]

Depends on / 依赖: mem_toNonUnitalSubalgebra
-/
theorem toNonUnitalSubalgebra_injective :
    Function.Injective
      (toNonUnitalSubalgebra : NonUnitalStarSubalgebra R A -> NonUnitalSubalgebra R A) :=
  fun S T h =>
  ext fun x => by rw [← mem_toNonUnitalSubalgebra, ← mem_toNonUnitalSubalgebra, h]

/--
theorem `toNonUnitalSubalgebra_inj` / 定理 `toNonUnitalSubalgebra_inj`

English:
theorem toNonUnitalSubalgebra_inj
  given: {S U : NonUnitalStarSubalgebra R A}
  proof: toNonUnitalSubalgebra_injective.eq_iff

中文:
定理 toNonUnitalSubalgebra_inj
  条件: {S U : 非幺对合子代数 R A}
  证明: toNonUnitalSubalgebra_injective.eq_iff

Depends on / 依赖: eq_iff, toNonUnitalSubalgebra_injective, toNonUnitalSubalgebra_injective.eq_iff
-/
theorem toNonUnitalSubalgebra_inj {S U : NonUnitalStarSubalgebra R A} :
    S.toNonUnitalSubalgebra = U.toNonUnitalSubalgebra ↔ S = U :=
  toNonUnitalSubalgebra_injective.eq_iff

/--
theorem `toNonUnitalSubalgebra_le_iff` / 定理 `toNonUnitalSubalgebra_le_iff`

English:
theorem toNonUnitalSubalgebra_le_iff
  given: {S₁ S₂ : NonUnitalStarSubalgebra R A}
  proof: Iff.rfl

中文:
定理 toNonUnitalSubalgebra_le_iff
  条件: {S₁ S₂ : 非幺对合子代数 R A}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toNonUnitalSubalgebra_le_iff {S₁ S₂ : NonUnitalStarSubalgebra R A} :
    S₁.toNonUnitalSubalgebra <= S₂.toNonUnitalSubalgebra ↔ S₁ <= S₂ :=
  Iff.rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S)
  body: { S.toNonUnitalSubalgebra.copy s hs with
    star_mem' := @fun x (hx : x in s) => by
      change star x in s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp, norm_cast]

中文:
定义 copy
  签名: (S : 非幺对合子代数 R A) (s : 集合 A) (hs : s = ↑S)
  定义体: { S.toNonUnitalSubalgebra.copy s hs with
    star_mem' := @fun x (hx : x in s) => by
      change star x in s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp, norm_cast]
-/
protected def copy (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    NonUnitalStarSubalgebra R A :=
  { S.toNonUnitalSubalgebra.copy s hs with
    star_mem' := @fun x (hx : x in s) => by
      change star x in s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp, norm_cast]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S)
  proof: rfl

中文:
定理 coe_copy
  条件: (S : 非幺对合子代数 R A) (s : 集合 A) (hs : s = ↑S)
  证明: rfl
-/
theorem coe_copy (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    (S.copy s hs : Set A) = s :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: (S : 非幺对合子代数 R A) (s : 集合 A) (hs : s = ↑S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S : NonUnitalStarSubalgebra R A)

/-- A non-unital star subalgebra over a ring is also a `Subring`. -/
@[reducible]
/--
Definition of `toNonUnitalSubring` / `toNonUnitalSubring` 的定义

English:
definition toNonUnitalSubring
  signature: {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
  body: S.toNonUnitalSubsemiring
  neg_mem' := neg_mem (s := S)

中文:
定义 toNonUnitalSubring
  签名: {R : 类型u} {A : 类型v} [交换环 R] [非幺环 A] [模 R A]
  定义体: S.toNonUnitalSubsemiring
  neg_mem' := neg_mem (s := S)

Depends on / 依赖: S.toNonUnitalSubsemiring, toNonUnitalSubsemiring
-/
def toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : NonUnitalSubring A where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  neg_mem' := neg_mem (s := S)

/--
theorem `mem_toNonUnitalSubring` / 定理 `mem_toNonUnitalSubring`

English:
theorem mem_toNonUnitalSubring
  statement: {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toNonUnitalSubring
  结论: {R : 类型u} {A : 类型v} [交换环 R] [非幺环 A] [模 R A]
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] {S : NonUnitalStarSubalgebra R A} {x} : x in S.toNonUnitalSubring ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `coe_toNonUnitalSubring` / 定理 `coe_toNonUnitalSubring`

English:
theorem coe_toNonUnitalSubring
  statement: {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
  proof: rfl

中文:
定理 coe_toNonUnitalSubring
  结论: {R : 类型u} {A : 类型v} [交换环 R] [非幺环 A] [模 R A]
  证明: rfl
-/
theorem coe_toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : (↑S.toNonUnitalSubring : Set A) = S :=
  rfl

/--
theorem `toNonUnitalSubring_injective` / 定理 `toNonUnitalSubring_injective`

English:
theorem toNonUnitalSubring_injective
  statement: {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A]
  proof: fun S T h => ext fun x => by rw [← mem_toNonUnitalSubring, ← mem_toNonUnitalSubring, h]

中文:
定理 toNonUnitalSubring_injective
  结论: {R : 类型u} {A : 类型v} [交换环 R] [非幺环 A]
  证明: fun S T h => ext fun x => by rw [← mem_toNonUnitalSubring, ← mem_toNonUnitalSubring, h]

Depends on / 依赖: mem_toNonUnitalSubring
-/
theorem toNonUnitalSubring_injective {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A]
    [Module R A] [Star A] :
    Function.Injective (toNonUnitalSubring : NonUnitalStarSubalgebra R A -> NonUnitalSubring A) :=
  fun S T h => ext fun x => by rw [← mem_toNonUnitalSubring, ← mem_toNonUnitalSubring, h]

/--
theorem `toNonUnitalSubring_inj` / 定理 `toNonUnitalSubring_inj`

English:
theorem toNonUnitalSubring_inj
  statement: {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
  proof: toNonUnitalSubring_injective.eq_iff

中文:
定理 toNonUnitalSubring_inj
  结论: {R : 类型u} {A : 类型v} [交换环 R] [非幺环 A] [模 R A]
  证明: toNonUnitalSubring_injective.eq_iff

Depends on / 依赖: eq_iff, toNonUnitalSubring_injective, toNonUnitalSubring_injective.eq_iff
-/
theorem toNonUnitalSubring_inj {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] {S U : NonUnitalStarSubalgebra R A} :
    S.toNonUnitalSubring = U.toNonUnitalSubring ↔ S = U :=
  toNonUnitalSubring_injective.eq_iff

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited S
  body: ⟨(0 : S.toNonUnitalSubalgebra)⟩

中文:
实例 instInhabited
  签名: : 可居 S
  定义体: ⟨(0 : S.toNonUnitalSubalgebra)⟩

Depends on / 依赖: S.toNonUnitalSubalgebra, toNonUnitalSubalgebra
-/
instance instInhabited : Inhabited S :=
  ⟨(0 : S.toNonUnitalSubalgebra)⟩

section


/--
Instance `toNonUnitalSemiring` / 实例 `toNonUnitalSemiring`

English:
instance toNonUnitalSemiring
  signature: {R A} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [Star A]
  body: inferInstance

中文:
实例 toNonUnitalSemiring
  签名: {R A} [交换半环 R] [非幺半环 A] [模 R A] [对合 A]
  定义体: inferInstance
-/
instance toNonUnitalSemiring {R A} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) : NonUnitalSemiring S :=
  inferInstance

/--
Instance `toNonUnitalCommSemiring` / 实例 `toNonUnitalCommSemiring`

English:
instance toNonUnitalCommSemiring
  signature: {R A} [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
  body: inferInstance

中文:
实例 toNonUnitalCommSemiring
  签名: {R A} [交换半环 R] [非幺交换半环 A] [模 R A]
  定义体: inferInstance
-/
instance toNonUnitalCommSemiring {R A} [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : NonUnitalCommSemiring S :=
  inferInstance

/--
Instance `toNonUnitalRing` / 实例 `toNonUnitalRing`

English:
instance toNonUnitalRing
  signature: {R A} [CommRing R] [NonUnitalRing A] [Module R A] [Star A]
  body: inferInstance

中文:
实例 toNonUnitalRing
  签名: {R A} [交换环 R] [非幺环 A] [模 R A] [对合 A]
  定义体: inferInstance
-/
instance toNonUnitalRing {R A} [CommRing R] [NonUnitalRing A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) : NonUnitalRing S :=
  inferInstance

/--
Instance `toNonUnitalCommRing` / 实例 `toNonUnitalCommRing`

English:
instance toNonUnitalCommRing
  signature: {R A} [CommRing R] [NonUnitalCommRing A] [Module R A] [Star A]
  body: inferInstance

中文:
实例 toNonUnitalCommRing
  签名: {R A} [交换环 R] [非幺交换环 A] [模 R A] [对合 A]
  定义体: inferInstance
-/
instance toNonUnitalCommRing {R A} [CommRing R] [NonUnitalCommRing A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) : NonUnitalCommRing S :=
  inferInstance
end

/--
Definition of `toNonUnitalSubalgebra'` / `toNonUnitalSubalgebra'` 的定义

English:
definition toNonUnitalSubalgebra'
  signature: : NonUnitalStarSubalgebra R A ↪o NonUnitalSubalgebra R A where
  body: { toFun := fun S => S.toNonUnitalSubalgebra
inj' := fun S T h => ext by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

中文:
定义 toNonUnitalSubalgebra'
  签名: : 非幺对合子代数 R A ↪o NonUnital子代数 R A where
  定义体: { toFun := fun S => S.toNonUnitalSubalgebra
inj' := fun S T h => ext by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

Depends on / 依赖: S.toNonUnitalSubalgebra, SetLike, SetLike.coe_subset_coe, SetLike.coe_subset_coe.symm.trans, SetLike.ext_iff, coe_subset_coe, ext_iff, map_rel_iff, toNonUnitalSubalgebra
-/
def toNonUnitalSubalgebra' : NonUnitalStarSubalgebra R A ↪o NonUnitalSubalgebra R A where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubalgebra
inj' := fun S T h => ext by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

section


/--
Instance `module'` / 实例 `module'`

English:
instance module'
  signature: [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
  body: SMulMemClass.toModule' _ R' R A S

中文:
实例 module'
  签名: [半环 R'] [标量乘法 R' R] [模 R' A] [标量塔 R' R A]
  定义体: SMulMemClass.toModule' _ R' R A S

Depends on / 依赖: SMulMemClass, SMulMemClass.toModule, toModule
-/
instance module' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : Module R' S :=
  SMulMemClass.toModule' _ R' R A S

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: : Module R S
  body: S.module'

中文:
实例 instModule
  签名: : 模 R S
  定义体: S.module'

Depends on / 依赖: S.module, module
-/
instance instModule : Module R S :=
  S.module'

/--
Instance `instIsScalarTower'` / 实例 `instIsScalarTower'`

English:
instance instIsScalarTower'
  signature: [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
  body: S.toNonUnitalSubalgebra.instIsScalarTower'

中文:
实例 instIsScalarTower'
  签名: [半环 R'] [标量乘法 R' R] [模 R' A] [标量塔 R' R A]
  定义体: S.toNonUnitalSubalgebra.instIsScalarTower'

Depends on / 依赖: S.toNonUnitalSubalgebra.instIsScalarTower, instIsScalarTower, toNonUnitalSubalgebra
-/
instance instIsScalarTower' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    IsScalarTower R' R S :=
  S.toNonUnitalSubalgebra.instIsScalarTower'

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [IsScalarTower R A A]
  body: Subtype.ext smul_assoc r (x : A) (y : A)

中文:
实例 instIsScalarTower
  签名: [标量塔 R A A]
  定义体: Subtype.ext smul_assoc r (x : A) (y : A)

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance instIsScalarTower [IsScalarTower R A A] : IsScalarTower R S S where
smul_assoc r x y := Subtype.ext smul_assoc r (x : A) (y : A)

/--
Instance `instSMulCommClass'` / 实例 `instSMulCommClass'`

English:
instance instSMulCommClass'
  signature: [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
  body: Subtype.ext smul_comm r' r (s : A)

中文:
实例 instSMulCommClass'
  签名: [半环 R'] [标量乘法 R' R] [模 R' A] [标量塔 R' R A]
  定义体: Subtype.ext smul_comm r' r (s : A)

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance instSMulCommClass' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
    [SMulCommClass R' R A] : SMulCommClass R' R S where
smul_comm r' r s := Subtype.ext smul_comm r' r (s : A)

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMulCommClass R A A]
  body: Subtype.ext smul_comm r (x : A) (y : A)

中文:
实例 instSMulCommClass
  签名: [标量交换类 R A A]
  定义体: Subtype.ext smul_comm r (x : A) (y : A)

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance instSMulCommClass [SMulCommClass R A A] : SMulCommClass R S S where
smul_comm r x y := Subtype.ext smul_comm r (x : A) (y : A)

end

/--
Instance `instIsTorsionFree` / 实例 `instIsTorsionFree`

English:
instance instIsTorsionFree
  signature: [IsTorsionFree R A]
  body: Subtype.coe_injective.moduleIsTorsionFree _ (by simp)

中文:
实例 instIsTorsionFree
  签名: [是无挠 R A]
  定义体: Subtype.coe_injective.moduleIsTorsionFree _ (by simp)

Depends on / 依赖: Subtype, Subtype.coe_injective.moduleIsTorsionFree, coe_injective, moduleIsTorsionFree
-/
instance instIsTorsionFree [IsTorsionFree R A] : IsTorsionFree R S :=
  Subtype.coe_injective.moduleIsTorsionFree _ (by simp)

/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (x y : S)
  statement: (↑(x + y) : A) = ↑x + ↑y
  proof: rfl

中文:
定理 coe_add
  条件: (x y : S)
  结论: (↑(x + y) : A) = ↑x + ↑y
  证明: rfl
-/
protected theorem coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y :=
  rfl

/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : S)
  statement: (↑(x * y) : A) = ↑x * ↑y
  proof: rfl

中文:
定理 coe_mul
  条件: (x y : S)
  结论: (↑(x * y) : A) = ↑x * ↑y
  证明: rfl
-/
protected theorem coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y :=
  rfl

/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : S) : A) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: ((0 : S) : A) = 0
  证明: rfl
-/
protected theorem coe_zero : ((0 : S) : A) = 0 :=
  rfl

/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  statement: {R : Type u} {A : Type v} [CommRing R] [NonUnitalNonAssocRing A]
  proof: rfl

中文:
定理 coe_neg
  结论: {R : 类型u} {A : 类型v} [交换环 R] [非幺非结合环 A]
  证明: rfl
-/
protected theorem coe_neg {R : Type u} {A : Type v} [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [Star A] {S : NonUnitalStarSubalgebra R A} (x : S) : (↑(-x) : A) = -↑x :=
  rfl

/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  statement: {R : Type u} {A : Type v} [CommRing R] [NonUnitalNonAssocRing A]
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sub
  结论: {R : 类型u} {A : 类型v} [交换环 R] [非幺非结合环 A]
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [Star A] {S : NonUnitalStarSubalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: [SMul R' R] [SMul R' A] [IsScalarTower R' R A] (r : R') (x : S)
  proof: rfl

中文:
定理 coe_smul
  条件: [标量乘法 R' R] [标量乘法 R' A] [标量塔 R' R A] (r : R') (x : S)
  证明: rfl
-/
theorem coe_smul [SMul R' R] [SMul R' A] [IsScalarTower R' R A] (r : R') (x : S) :
    ↑(r • x) = r • (x : A) :=
  rfl

/--
theorem `coe_eq_zero` / 定理 `coe_eq_zero`

English:
theorem coe_eq_zero
  given: {x : S}
  statement: (x : A) = 0 ↔ x = 0
  proof: ZeroMemClass.coe_eq_zero

@[simp]

中文:
定理 coe_eq_zero
  条件: {x : S}
  结论: (x : A) = 0 ↔ x = 0
  证明: ZeroMemClass.coe_eq_zero

@[simp]
-/
protected theorem coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
  ZeroMemClass.coe_eq_zero

@[simp]
/--
theorem `toNonUnitalSubalgebra_subtype` / 定理 `toNonUnitalSubalgebra_subtype`

English:
theorem toNonUnitalSubalgebra_subtype
  proof: rfl

@[simp]

中文:
定理 toNonUnitalSubalgebra_subtype
  证明: rfl

@[simp]
-/
theorem toNonUnitalSubalgebra_subtype :
    NonUnitalSubalgebraClass.subtype S = NonUnitalStarSubalgebraClass.subtype S :=
  rfl

@[simp]
/--
theorem `toSubring_subtype` / 定理 `toSubring_subtype`

English:
theorem toSubring_subtype
  statement: {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A] [Star A]
  proof: rfl

中文:
定理 toSubring_subtype
  结论: {R A : 类型} [交换环 R] [非幺非结合环 A] [模 R A] [对合 A]
  证明: rfl
-/
theorem toSubring_subtype {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) :
    NonUnitalSubringClass.subtype S = NonUnitalStarSubalgebraClass.subtype S :=
  rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : F) (S : NonUnitalStarSubalgebra R A)
  body: S.toNonUnitalSubalgebra.map (f : A ->ₙₐ[R] B)
  star_mem' := by rintro _ ⟨a, ha, rfl⟩; exact ⟨star a, star_mem (s := S) ha, map_star f a⟩

@[gcongr]

中文:
定义 map
  签名: (f : F) (S : 非幺对合子代数 R A)
  定义体: S.toNonUnitalSubalgebra.map (f : A ->ₙₐ[R] B)
  star_mem' := by rintro _ ⟨a, ha, rfl⟩; exact ⟨star a, star_mem (s := S) ha, map_star f a⟩

@[gcongr]

Depends on / 依赖: S.toNonUnitalSubalgebra.map, toNonUnitalSubalgebra
-/
def map (f : F) (S : NonUnitalStarSubalgebra R A) : NonUnitalStarSubalgebra R B where
  toNonUnitalSubalgebra := S.toNonUnitalSubalgebra.map (f : A ->ₙₐ[R] B)
  star_mem' := by rintro _ ⟨a, ha, rfl⟩; exact ⟨star a, star_mem (s := S) ha, map_star f a⟩

@[gcongr]
/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: {S₁ S₂ : NonUnitalStarSubalgebra R A} {f : F}
  proof: Set.image_mono

中文:
定理 map_mono
  条件: {S₁ S₂ : 非幺对合子代数 R A} {f : F}
  证明: Set.image_mono

Depends on / 依赖: Set.image_mono, image_mono
-/
theorem map_mono {S₁ S₂ : NonUnitalStarSubalgebra R A} {f : F} :
    S₁ <= S₂ -> (map f S₁ : NonUnitalStarSubalgebra R B) <= map f S₂ :=
  Set.image_mono

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : F} (hf : Function.Injective f)
  proof: fun _S₁ _S₂ ih =>
ext Set.ext_iff.1 Set.image_injective.2 hf Set.ext SetLike.ext_iff.mp ih

@[simp]

中文:
定理 map_injective
  条件: {f : F} (hf : 函数.单射 f)
  证明: fun _S₁ _S₂ ih =>
ext Set.ext_iff.1 Set.image_injective.2 hf Set.ext SetLike.ext_iff.mp ih

@[simp]

Depends on / 依赖: Set.ext, Set.ext_iff, Set.image_injective, SetLike, SetLike.ext_iff.mp, ext_iff, image_injective
-/
theorem map_injective {f : F} (hf : Function.Injective f) :
    Function.Injective (map f : NonUnitalStarSubalgebra R A -> NonUnitalStarSubalgebra R B) :=
  fun _S₁ _S₂ ih =>
ext Set.ext_iff.1 Set.image_injective.2 hf Set.ext SetLike.ext_iff.mp ih

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (S : NonUnitalStarSubalgebra R A)
  statement: map (NonUnitalStarAlgHom.id R A) S = S
  proof: SetLike.coe_injective Set.image_id _

中文:
定理 map_id
  条件: (S : 非幺对合子代数 R A)
  结论: map (非幺StarAlg态射.id R A) S = S
  证明: SetLike.coe_injective Set.image_id _

Depends on / 依赖: Set.image_id, SetLike, SetLike.coe_injective, coe_injective, image_id
-/
theorem map_id (S : NonUnitalStarSubalgebra R A) : map (NonUnitalStarAlgHom.id R A) S = S :=
SetLike.coe_injective Set.image_id _

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (S : NonUnitalStarSubalgebra R A) (g : B ->⋆ₙₐ[R] C) (f : A ->⋆ₙₐ[R] B)
  proof: SetLike.coe_injective Set.image_image _ _ _

@[simp]

中文:
定理 map_map
  条件: (S : 非幺对合子代数 R A) (g : B ->⋆ₙₐ[R] C) (f : A ->⋆ₙₐ[R] B)
  证明: SetLike.coe_injective Set.image_image _ _ _

@[simp]

Depends on / 依赖: Set.image_image, SetLike, SetLike.coe_injective, coe_injective, image_image
-/
theorem map_map (S : NonUnitalStarSubalgebra R A) (g : B ->⋆ₙₐ[R] C) (f : A ->⋆ₙₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
SetLike.coe_injective Set.image_image _ _ _

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {S : NonUnitalStarSubalgebra R A} {f : F} {y : B}
  proof: NonUnitalSubalgebra.mem_map

中文:
定理 mem_map
  条件: {S : 非幺对合子代数 R A} {f : F} {y : B}
  证明: NonUnitalSubalgebra.mem_map

Depends on / 依赖: NonUnitalSubalgebra, NonUnitalSubalgebra.mem_map, mem_map
-/
theorem mem_map {S : NonUnitalStarSubalgebra R A} {f : F} {y : B} :
    y in map f S ↔ exists x in S, f x = y :=
  NonUnitalSubalgebra.mem_map

/--
theorem `map_toNonUnitalSubalgebra` / 定理 `map_toNonUnitalSubalgebra`

English:
theorem map_toNonUnitalSubalgebra
  given: {S : NonUnitalStarSubalgebra R A} {f : F}
  proof: SetLike.coe_injective rfl

@[simp, norm_cast]

中文:
定理 map_toNonUnitalSubalgebra
  条件: {S : 非幺对合子代数 R A} {f : F}
  证明: SetLike.coe_injective rfl

@[simp, norm_cast]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem map_toNonUnitalSubalgebra {S : NonUnitalStarSubalgebra R A} {f : F} :
    (map f S : NonUnitalStarSubalgebra R B).toNonUnitalSubalgebra =
      NonUnitalSubalgebra.map f S.toNonUnitalSubalgebra :=
  SetLike.coe_injective rfl

@[simp, norm_cast]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (S : NonUnitalStarSubalgebra R A) (f : F)
  statement: map f S = f '' S
  proof: rfl

中文:
定理 coe_map
  条件: (S : 非幺对合子代数 R A) (f : F)
  结论: map f S = f '' S
  证明: rfl
-/
theorem coe_map (S : NonUnitalStarSubalgebra R A) (f : F) : map f S = f '' S :=
  rfl

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : F) (S : NonUnitalStarSubalgebra R B)
  body: S.toNonUnitalSubalgebra.comap f
  star_mem' := @fun a (ha : f a in S) =>
    show f (star a) in S from (map_star f a).symm ▸ star_mem (s := S) ha

中文:
定义 comap
  签名: (f : F) (S : 非幺对合子代数 R B)
  定义体: S.toNonUnitalSubalgebra.comap f
  star_mem' := @fun a (ha : f a in S) =>
    show f (star a) in S from (map_star f a).symm ▸ star_mem (s := S) ha

Depends on / 依赖: S.toNonUnitalSubalgebra.comap, toNonUnitalSubalgebra
-/
def comap (f : F) (S : NonUnitalStarSubalgebra R B) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := S.toNonUnitalSubalgebra.comap f
  star_mem' := @fun a (ha : f a in S) =>
    show f (star a) in S from (map_star f a).symm ▸ star_mem (s := S) ha

/--
theorem `map_le` / 定理 `map_le`

English:
theorem map_le
  given: {S : NonUnitalStarSubalgebra R A} {f : F} {U : NonUnitalStarSubalgebra R B}
  proof: Set.image_subset_iff

中文:
定理 map_le
  条件: {S : 非幺对合子代数 R A} {f : F} {U : 非幺对合子代数 R B}
  证明: Set.image_subset_iff

Depends on / 依赖: Set.image_subset_iff, image_subset_iff
-/
theorem map_le {S : NonUnitalStarSubalgebra R A} {f : F} {U : NonUnitalStarSubalgebra R B} :
    map f S <= U ↔ S <= comap f U :=
  Set.image_subset_iff

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : F)
  statement: GaloisConnection (map f) (comap f)
  proof: fun _S _U => map_le

@[simp]

中文:
定理 gc_map_comap
  条件: (f : F)
  结论: GaloisConnection (map f) (comap f)
  证明: fun _S _U => map_le

@[simp]

Depends on / 依赖: map_le
-/
theorem gc_map_comap (f : F) : GaloisConnection (map f) (comap f) :=
  fun _S _U => map_le

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: (S : NonUnitalStarSubalgebra R B) (f : F) (x : A)
  statement: x in comap f S ↔ f x in S
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 mem_comap
  条件: (S : 非幺对合子代数 R B) (f : F) (x : A)
  结论: x in comap f S ↔ f x in S
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap (S : NonUnitalStarSubalgebra R B) (f : F) (x : A) : x in comap f S ↔ f x in S :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (S : NonUnitalStarSubalgebra R B) (f : F)
  statement: comap f S = f ⁻¹' (S : Set B)
  proof: rfl

中文:
定理 coe_comap
  条件: (S : 非幺对合子代数 R B) (f : F)
  结论: comap f S = f ⁻¹' (S : 集合 B)
  证明: rfl
-/
theorem coe_comap (S : NonUnitalStarSubalgebra R B) (f : F) : comap f S = f ⁻¹' (S : Set B) :=
  rfl

/--
Instance `instNoZeroDivisors` / 实例 `instNoZeroDivisors`

English:
instance instNoZeroDivisors
  signature: {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [NoZeroDivisors A]
  body: NonUnitalSubsemiringClass.noZeroDivisors S

中文:
实例 instNoZeroDivisors
  签名: {R A : 类型} [交换半环 R] [非幺半环 A] [无零因子 A]
  定义体: NonUnitalSubsemiringClass.noZeroDivisors S

Depends on / 依赖: NonUnitalSubsemiringClass, NonUnitalSubsemiringClass.noZeroDivisors, noZeroDivisors
-/
instance instNoZeroDivisors {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [NoZeroDivisors A]
    [Module R A] [Star A] (S : NonUnitalStarSubalgebra R A) : NoZeroDivisors S :=
  NonUnitalSubsemiringClass.noZeroDivisors S

end NonUnitalStarSubalgebra

namespace NonUnitalSubalgebra

variable [CommSemiring R] [NonUnitalSemiring A] [Module R A] [Star A]
variable (s : NonUnitalSubalgebra R A)

/--
Definition of `toNonUnitalStarSubalgebra` / `toNonUnitalStarSubalgebra` 的定义

English:
definition toNonUnitalStarSubalgebra
  signature: (h_star : forall x, x in s -> star x in s)
  body: { s with
    star_mem' := @h_star }

@[simp]

中文:
定义 toNonUnitalStarSubalgebra
  签名: (h_star : 对任意 x, x in s -> star x in s)
  定义体: { s with
    star_mem' := @h_star }

@[simp]

Depends on / 依赖: h_star, star_mem
-/
def toNonUnitalStarSubalgebra (h_star : forall x, x in s -> star x in s) : NonUnitalStarSubalgebra R A :=
  { s with
    star_mem' := @h_star }

@[simp]
/--
theorem `mem_toNonUnitalStarSubalgebra` / 定理 `mem_toNonUnitalStarSubalgebra`

English:
theorem mem_toNonUnitalStarSubalgebra
  given: {s : NonUnitalSubalgebra R A} {h_star} {x}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toNonUnitalStarSubalgebra
  条件: {s : NonUnital子代数 R A} {h_star} {x}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toNonUnitalStarSubalgebra {s : NonUnitalSubalgebra R A} {h_star} {x} :
    x in s.toNonUnitalStarSubalgebra h_star ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `coe_toNonUnitalStarSubalgebra` / 定理 `coe_toNonUnitalStarSubalgebra`

English:
theorem coe_toNonUnitalStarSubalgebra
  given: (s : NonUnitalSubalgebra R A) (h_star)
  proof: rfl

@[simp]

中文:
定理 coe_toNonUnitalStarSubalgebra
  条件: (s : NonUnital子代数 R A) (h_star)
  证明: rfl

@[simp]
-/
theorem coe_toNonUnitalStarSubalgebra (s : NonUnitalSubalgebra R A) (h_star) :
    (s.toNonUnitalStarSubalgebra h_star : Set A) = s :=
  rfl

@[simp]
/--
theorem `toNonUnitalStarSubalgebra_toNonUnitalSubalgebra` / 定理 `toNonUnitalStarSubalgebra_toNonUnitalSubalgebra`

English:
theorem toNonUnitalStarSubalgebra_toNonUnitalSubalgebra
  given: (s : NonUnitalSubalgebra R A) (h_star)
  proof: SetLike.coe_injective rfl

@[simp]

中文:
定理 toNonUnitalStarSubalgebra_toNonUnitalSubalgebra
  条件: (s : NonUnital子代数 R A) (h_star)
  证明: SetLike.coe_injective rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem toNonUnitalStarSubalgebra_toNonUnitalSubalgebra (s : NonUnitalSubalgebra R A) (h_star) :
    (s.toNonUnitalStarSubalgebra h_star).toNonUnitalSubalgebra = s :=
  SetLike.coe_injective rfl

@[simp]
/--
theorem `_root_.NonUnitalStarSubalgebra.toNonUnitalSubalgebra_toNonUnitalStarSubalgebra` / 定理 `_root_.NonUnitalStarSubalgebra.toNonUnitalSubalgebra_toNonUnitalStarSubalgebra`

English:
theorem _root_.NonUnitalStarSubalgebra.toNonUnitalSubalgebra_toNonUnitalStarSubalgebra
  proof: SetLike.coe_injective rfl

中文:
定理 _root_.非幺对合子代数.toNonUnitalSubalgebra_toNonUnitalStarSubalgebra
  证明: SetLike.coe_injective rfl
-/
theorem _root_.NonUnitalStarSubalgebra.toNonUnitalSubalgebra_toNonUnitalStarSubalgebra
    (S : NonUnitalStarSubalgebra R A) :
    (S.toNonUnitalSubalgebra.toNonUnitalStarSubalgebra fun _ => star_mem (s := S)) = S :=
  SetLike.coe_injective rfl

end NonUnitalSubalgebra
namespace NonUnitalStarAlgHom

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (φ : F)
  body: NonUnitalAlgHom.range (φ : A ->ₙₐ[R] B)
  star_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨star a, map_star φ a⟩

@[simp]

中文:
定义 range
  签名: (φ : F)
  定义体: NonUnitalAlgHom.range (φ : A ->ₙₐ[R] B)
  star_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨star a, map_star φ a⟩

@[simp]
-/
protected def range (φ : F) : NonUnitalStarSubalgebra R B where
  toNonUnitalSubalgebra := NonUnitalAlgHom.range (φ : A ->ₙₐ[R] B)
  star_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨star a, map_star φ a⟩

@[simp]
/--
theorem `mem_range` / 定理 `mem_range`

English:
theorem mem_range
  given: (φ : F) {y : B}
  proof: NonUnitalRingHom.mem_srange

中文:
定理 mem_range
  条件: (φ : F) {y : B}
  证明: NonUnitalRingHom.mem_srange

Depends on / 依赖: NonUnitalRingHom, NonUnitalRingHom.mem_srange, mem_srange
-/
theorem mem_range (φ : F) {y : B} :
    y in (NonUnitalStarAlgHom.range φ : NonUnitalStarSubalgebra R B) ↔ exists x : A, φ x = y :=
  NonUnitalRingHom.mem_srange

/--
theorem `mem_range_self` / 定理 `mem_range_self`

English:
theorem mem_range_self
  given: (φ : F) (x : A)
  proof: (NonUnitalAlgHom.mem_range φ).2 ⟨x, rfl⟩

@[simp, norm_cast]

中文:
定理 mem_range_self
  条件: (φ : F) (x : A)
  证明: (NonUnitalAlgHom.mem_range φ).2 ⟨x, rfl⟩

@[simp, norm_cast]

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.mem_range, mem_range
-/
theorem mem_range_self (φ : F) (x : A) :
    φ x in (NonUnitalStarAlgHom.range φ : NonUnitalStarSubalgebra R B) :=
  (NonUnitalAlgHom.mem_range φ).2 ⟨x, rfl⟩

@[simp, norm_cast]
/--
theorem `coe_range` / 定理 `coe_range`

English:
theorem coe_range
  given: (φ : F)
  proof: by
  rfl

中文:
定理 coe_range
  条件: (φ : F)
  证明: by
  rfl
-/
theorem coe_range (φ : F) :
    ((NonUnitalStarAlgHom.range φ : NonUnitalStarSubalgebra R B) : Set B) =
    Set.range (φ : A -> B) := by
  rfl

/--
theorem `range_comp` / 定理 `range_comp`

English:
theorem range_comp
  given: (f : A ->⋆ₙₐ[R] B) (g : B ->⋆ₙₐ[R] C)
  proof: SetLike.coe_injective (Set.range_comp g f)

中文:
定理 range_comp
  条件: (f : A ->⋆ₙₐ[R] B) (g : B ->⋆ₙₐ[R] C)
  证明: SetLike.coe_injective (Set.range_comp g f)

Depends on / 依赖: Set.range_comp, SetLike, SetLike.coe_injective, coe_injective, range_comp
-/
theorem range_comp (f : A ->⋆ₙₐ[R] B) (g : B ->⋆ₙₐ[R] C) :
    NonUnitalStarAlgHom.range (g.comp f) = (NonUnitalStarAlgHom.range f).map g :=
  SetLike.coe_injective (Set.range_comp g f)

/--
theorem `range_comp_le_range` / 定理 `range_comp_le_range`

English:
theorem range_comp_le_range
  given: (f : A ->⋆ₙₐ[R] B) (g : B ->⋆ₙₐ[R] C)
  proof: SetLike.coe_mono (Set.range_comp_subset_range f g)

中文:
定理 range_comp_le_range
  条件: (f : A ->⋆ₙₐ[R] B) (g : B ->⋆ₙₐ[R] C)
  证明: SetLike.coe_mono (Set.range_comp_subset_range f g)

Depends on / 依赖: Set.range_comp_subset_range, SetLike, SetLike.coe_mono, coe_mono, range_comp_subset_range
-/
theorem range_comp_le_range (f : A ->⋆ₙₐ[R] B) (g : B ->⋆ₙₐ[R] C) :
    NonUnitalStarAlgHom.range (g.comp f) <= NonUnitalStarAlgHom.range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : F) (S : NonUnitalStarSubalgebra R B) (hf : forall x, f x in S)
  body: NonUnitalAlgHom.codRestrict f S.toNonUnitalSubalgebra hf
map_star' := fun a => Subtype.ext map_star f a

@[simp]

中文:
定义 codRestrict
  签名: (f : F) (S : 非幺对合子代数 R B) (hf : 对任意 x, f x in S)
  定义体: NonUnitalAlgHom.codRestrict f S.toNonUnitalSubalgebra hf
map_star' := fun a => Subtype.ext map_star f a

@[simp]

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.codRestrict, S.toNonUnitalSubalgebra, codRestrict, toNonUnitalSubalgebra
-/
def codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : forall x, f x in S) : A ->⋆ₙₐ[R] S where
  toNonUnitalAlgHom := NonUnitalAlgHom.codRestrict f S.toNonUnitalSubalgebra hf
map_star' := fun a => Subtype.ext map_star f a

@[simp]
/--
theorem `subtype_comp_codRestrict` / 定理 `subtype_comp_codRestrict`

English:
theorem subtype_comp_codRestrict
  given: (f : F) (S : NonUnitalStarSubalgebra R B) (hf : forall x : A, f x in S)
  proof: NonUnitalStarAlgHom.ext fun _ => rfl

@[simp]

中文:
定理 subtype_comp_codRestrict
  条件: (f : F) (S : 非幺对合子代数 R B) (hf : 对任意 x : A, f x in S)
  证明: NonUnitalStarAlgHom.ext fun _ => rfl

@[simp]

Depends on / 依赖: NonUnitalStarAlgHom, NonUnitalStarAlgHom.ext
-/
theorem subtype_comp_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : forall x : A, f x in S) :
    (NonUnitalStarSubalgebraClass.subtype S).comp (NonUnitalStarAlgHom.codRestrict f S hf) = f :=
  NonUnitalStarAlgHom.ext fun _ => rfl

@[simp]
/--
theorem `coe_codRestrict` / 定理 `coe_codRestrict`

English:
theorem coe_codRestrict
  given: (f : F) (S : NonUnitalStarSubalgebra R B) (hf : forall x, f x in S) (x : A)
  proof: rfl

中文:
定理 coe_codRestrict
  条件: (f : F) (S : 非幺对合子代数 R B) (hf : 对任意 x, f x in S) (x : A)
  证明: rfl
-/
theorem coe_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : forall x, f x in S) (x : A) :
    ↑(NonUnitalStarAlgHom.codRestrict f S hf x) = f x :=
  rfl

/--
theorem `injective_codRestrict` / 定理 `injective_codRestrict`

English:
theorem injective_codRestrict
  given: (f : F) (S : NonUnitalStarSubalgebra R B) (hf : forall x : A, f x in S)
  proof: ⟨fun H _x _y hxy => H Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

中文:
定理 injective_codRestrict
  条件: (f : F) (S : 非幺对合子代数 R B) (hf : 对任意 x : A, f x in S)
  证明: ⟨fun H _x _y hxy => H Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

Depends on / 依赖: Subtype, Subtype.ext, Subtype.val, congr_arg
-/
theorem injective_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : forall x : A, f x in S) :
    Function.Injective (NonUnitalStarAlgHom.codRestrict f S hf) ↔ Function.Injective f :=
⟨fun H _x _y hxy => H Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

/--
Definition of `rangeRestrict` / `rangeRestrict` 的定义

English:
abbreviation rangeRestrict
  signature: (f : F)
  body: NonUnitalStarAlgHom.codRestrict f (NonUnitalStarAlgHom.range f)
    (NonUnitalStarAlgHom.mem_range_self f)

中文:
缩写 rangeRestrict
  签名: (f : F)
  定义体: NonUnitalStarAlgHom.codRestrict f (NonUnitalStarAlgHom.range f)
    (NonUnitalStarAlgHom.mem_range_self f)

Depends on / 依赖: NonUnitalStarAlgHom, NonUnitalStarAlgHom.codRestrict, NonUnitalStarAlgHom.mem_range_self, NonUnitalStarAlgHom.range, codRestrict, mem_range_self
-/
abbrev rangeRestrict (f : F) :
    A ->⋆ₙₐ[R] (NonUnitalStarAlgHom.range f : NonUnitalStarSubalgebra R B) :=
  NonUnitalStarAlgHom.codRestrict f (NonUnitalStarAlgHom.range f)
    (NonUnitalStarAlgHom.mem_range_self f)

/--
Definition of `equalizer` / `equalizer` 的定义

English:
definition equalizer
  signature: (ϕ ψ : F)
  body: NonUnitalAlgHom.equalizer ϕ ψ
  star_mem' := @fun x (hx : ϕ x = ψ x) => by simp [map_star, hx]

@[simp]

中文:
定义 equalizer
  签名: (ϕ ψ : F)
  定义体: NonUnitalAlgHom.equalizer ϕ ψ
  star_mem' := @fun x (hx : ϕ x = ψ x) => by simp [map_star, hx]

@[simp]

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.equalizer, equalizer
-/
def equalizer (ϕ ψ : F) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := NonUnitalAlgHom.equalizer ϕ ψ
  star_mem' := @fun x (hx : ϕ x = ψ x) => by simp [map_star, hx]

@[simp]
/--
theorem `mem_equalizer` / 定理 `mem_equalizer`

English:
theorem mem_equalizer
  given: (φ ψ : F) (x : A)
  proof: Iff.rfl

中文:
定理 mem_equalizer
  条件: (φ ψ : F) (x : A)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_equalizer (φ ψ : F) (x : A) :
    x in NonUnitalStarAlgHom.equalizer φ ψ ↔ φ x = ψ x :=
  Iff.rfl

end NonUnitalStarAlgHom

namespace StarAlgEquiv
variable [CommSemiring R]
variable [NonUnitalSemiring A] [Module R A] [Star A]
variable [NonUnitalSemiring B] [Module R B] [Star B]
variable [NonUnitalSemiring C] [Module R C] [Star C]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

/--
Definition of `ofLeftInverse'` / `ofLeftInverse'` 的定义

English:
definition ofLeftInverse'
  signature: {g : B -> A} {f : F} (h : Function.LeftInverse g f)
  body: { NonUnitalStarAlgHom.rangeRestrict f with
    toFun := NonUnitalStarAlgHom.rangeRestrict f
    invFun := g ∘ (NonUnitalStarSubalgebraClass.subtype <| NonUnitalStarAlgHom.range f)
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := (NonUnitalStarAlgHom.mem_range f).mp x.

中文:
定义 ofLeftInverse'
  签名: {g : B -> A} {f : F} (h : 函数.左逆 g f)
  定义体: { NonUnitalStarAlgHom.rangeRestrict f with
    toFun := NonUnitalStarAlgHom.rangeRestrict f
    invFun := g ∘ (NonUnitalStarSubalgebraClass.subtype <| NonUnitalStarAlgHom.range f)
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := (NonUnitalStarAlgHom.mem_range f).mp x.

Depends on / 依赖: NonUnitalStarAlgHom, NonUnitalStarAlgHom.mem_range, NonUnitalStarAlgHom.range, NonUnitalStarAlgHom.rangeRestrict, NonUnitalStarSubalgebraClass, NonUnitalStarSubalgebraClass.subtype, Subtype, Subtype.ext, invFun, left_inv, mem_range, rangeRestrict, right_inv, subtype, x.prop
-/
def ofLeftInverse' {g : B -> A} {f : F} (h : Function.LeftInverse g f) :
    A ≃⋆ₐ[R] NonUnitalStarAlgHom.range f :=
  { NonUnitalStarAlgHom.rangeRestrict f with
    toFun := NonUnitalStarAlgHom.rangeRestrict f
    invFun := g ∘ (NonUnitalStarSubalgebraClass.subtype <| NonUnitalStarAlgHom.range f)
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := (NonUnitalStarAlgHom.mem_range f).mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
/--
theorem `ofLeftInverse'_apply` / 定理 `ofLeftInverse'_apply`

English:
theorem ofLeftInverse'_apply
  given: {g : B -> A} {f : F} (h : Function.LeftInverse g f) (x : A)
  proof: rfl

@[simp]

中文:
定理 ofLeftInverse'_apply
  条件: {g : B -> A} {f : F} (h : 函数.左逆 g f) (x : A)
  证明: rfl

@[simp]
-/
theorem ofLeftInverse'_apply {g : B -> A} {f : F} (h : Function.LeftInverse g f) (x : A) :
    ofLeftInverse' h x = f x :=
  rfl

@[simp]
/--
theorem `ofLeftInverse'_symm_apply` / 定理 `ofLeftInverse'_symm_apply`

English:
theorem ofLeftInverse'_symm_apply
  statement: {g : B -> A} {f : F} (h : Function.LeftInverse g f)
  proof: rfl

中文:
定理 ofLeftInverse'_symm_apply
  结论: {g : B -> A} {f : F} (h : 函数.左逆 g f)
  证明: rfl
-/
theorem ofLeftInverse'_symm_apply {g : B -> A} {f : F} (h : Function.LeftInverse g f)
    (x : NonUnitalStarAlgHom.range f) : (ofLeftInverse' h).symm x = g x :=
  rfl

/--
Definition of `ofInjective'` / `ofInjective'` 的定义

English:
definition ofInjective'
  signature: (f : F) (hf : Function.Injective f)
  body: ofLeftInverse' (Classical.choose_spec hf.hasLeftInverse)

@[simp]

中文:
定义 ofInjective'
  签名: (f : F) (hf : 函数.单射 f)
  定义体: ofLeftInverse' (Classical.choose_spec hf.hasLeftInverse)

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, hasLeftInverse, hf.hasLeftInverse, ofLeftInverse
-/
noncomputable def ofInjective' (f : F) (hf : Function.Injective f) :
    A ≃⋆ₐ[R] NonUnitalStarAlgHom.range f :=
  ofLeftInverse' (Classical.choose_spec hf.hasLeftInverse)

@[simp]
/--
theorem `ofInjective'_apply` / 定理 `ofInjective'_apply`

English:
theorem ofInjective'_apply
  given: (f : F) (hf : Function.Injective f) (x : A)
  proof: rfl

中文:
定理 ofInjective'_apply
  条件: (f : F) (hf : 函数.单射 f) (x : A)
  证明: rfl
-/
theorem ofInjective'_apply (f : F) (hf : Function.Injective f) (x : A) :
    ofInjective' f hf x = f x :=
  rfl

end StarAlgEquiv

/-! ### The star closure of a subalgebra -/


namespace NonUnitalSubalgebra

open scoped Pointwise

variable [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A] [Module R A]
variable [StarModule R A]

/--
Instance `instInvolutiveStar` / 实例 `instInvolutiveStar`

English:
instance instInvolutiveStar
  signature: : InvolutiveStar (NonUnitalSubalgebra R A) where
  body: { carrier := star S.carrier
      mul_mem' := @fun x y hx hy => by simpa only [Set.mem_star, NonUnitalSubalgebra.mem_carrier]
        using (star_mul x y).symm ▸ mul_mem hy hx
      add_mem' := @fun x y hx hy => by simpa only [Set.mem_star, NonUnitalSubalgebra.mem_carrier]
        using (star_add x 

中文:
实例 instInvolutiveStar
  签名: : InvolutiveStar (NonUnital子代数 R A) where
  定义体: { carrier := star S.carrier
      mul_mem' := @fun x y hx hy => by simpa only [Set.mem_star, NonUnitalSubalgebra.mem_carrier]
        using (star_mul x y).symm ▸ mul_mem hy hx
      add_mem' := @fun x y hx hy => by simpa only [Set.mem_star, NonUnitalSubalgebra.mem_carrier]
        using (star_add x 

Depends on / 依赖: NonUnitalSubalgebra, NonUnitalSubalgebra.mem_carrier, S.carrier, Set.mem_star, Set.mem_star.mp, add_mem, carrier, mem_carrier, mem_star, mul_mem, smul_mem, star_add, star_mul, star_smul, star_zero, zero_mem
-/
instance instInvolutiveStar : InvolutiveStar (NonUnitalSubalgebra R A) where
  star S :=
    { carrier := star S.carrier
      mul_mem' := @fun x y hx hy => by simpa only [Set.mem_star, NonUnitalSubalgebra.mem_carrier]
        using (star_mul x y).symm ▸ mul_mem hy hx
      add_mem' := @fun x y hx hy => by simpa only [Set.mem_star, NonUnitalSubalgebra.mem_carrier]
        using (star_add x y).symm ▸ add_mem hx hy
      zero_mem' := Set.mem_star.mp ((star_zero A).symm ▸ zero_mem S : star (0 : A) in S)
      smul_mem' := fun r x hx => by simpa only [Set.mem_star, NonUnitalSubalgebra.mem_carrier]
        using (star_smul r x).symm ▸ SMulMemClass.smul_mem (star r) hx }
  star_involutive S := NonUnitalSubalgebra.ext fun x =>
      ⟨fun hx => star_star x ▸ hx, fun hx => ((star_star x).symm ▸ hx : star (star x) in S)⟩

@[simp]
/--
theorem `mem_star_iff` / 定理 `mem_star_iff`

English:
theorem mem_star_iff
  given: (S : NonUnitalSubalgebra R A) (x : A)
  statement: x in star S ↔ star x in S
  proof: Iff.rfl

中文:
定理 mem_star_iff
  条件: (S : NonUnital子代数 R A) (x : A)
  结论: x in star S ↔ star x in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_star_iff (S : NonUnitalSubalgebra R A) (x : A) : x in star S ↔ star x in S :=
  Iff.rfl

/--
theorem `star_mem_star_iff` / 定理 `star_mem_star_iff`

English:
theorem star_mem_star_iff
  given: (S : NonUnitalSubalgebra R A) (x : A)
  statement: star x in star S ↔ x in S
  proof: by
  simp

@[simp]

中文:
定理 star_mem_star_iff
  条件: (S : NonUnital子代数 R A) (x : A)
  结论: star x in star S ↔ x in S
  证明: by
  simp

@[simp]
-/
theorem star_mem_star_iff (S : NonUnitalSubalgebra R A) (x : A) : star x in star S ↔ x in S := by
  simp

@[simp]
/--
theorem `coe_star` / 定理 `coe_star`

English:
theorem coe_star
  given: (S : NonUnitalSubalgebra R A)
  statement: star S = star (S : Set A)
  proof: rfl

中文:
定理 coe_star
  条件: (S : NonUnital子代数 R A)
  结论: star S = star (S : 集合 A)
  证明: rfl
-/
theorem coe_star (S : NonUnitalSubalgebra R A) : star S = star (S : Set A) :=
  rfl

/--
theorem `star_mono` / 定理 `star_mono`

English:
theorem star_mono
  statement: Monotone (star : NonUnitalSubalgebra R A -> NonUnitalSubalgebra R A)
  proof: fun _ _ h _ hx => h hx

中文:
定理 star_mono
  结论: 递增 (star : NonUnital子代数 R A -> NonUnital子代数 R A)
  证明: fun _ _ h _ hx => h hx
-/
theorem star_mono : Monotone (star : NonUnitalSubalgebra R A -> NonUnitalSubalgebra R A) :=
  fun _ _ h _ hx => h hx

variable (R)
variable [IsScalarTower R A A] [SMulCommClass R A A]

/--
theorem `star_adjoin_comm` / 定理 `star_adjoin_comm`

English:
theorem star_adjoin_comm
  given: (s : Set A)
  proof: have :
    forall t : Set A, NonUnitalAlgebra.adjoin R (star t) <= star (NonUnitalAlgebra.adjoin R t) := fun _ =>
    NonUnitalAlgebra.adjoin_le fun _ hx => NonUnitalAlgebra.subset_adjoin R hx
  le_antisymm (by simpa only [star_star] using NonUnitalSubalgebra.star_mono (this (star s)))
    (this s)

中文:
定理 star_adjoin_comm
  条件: (s : 集合 A)
  证明: have :
    forall t : Set A, NonUnitalAlgebra.adjoin R (star t) <= star (NonUnitalAlgebra.adjoin R t) := fun _ =>
    NonUnitalAlgebra.adjoin_le fun _ hx => NonUnitalAlgebra.subset_adjoin R hx
  le_antisymm (by simpa only [star_star] using NonUnitalSubalgebra.star_mono (this (star s)))
    (this s)

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.adjoin, NonUnitalAlgebra.adjoin_le, NonUnitalAlgebra.subset_adjoin, NonUnitalSubalgebra, NonUnitalSubalgebra.star_mono, adjoin, adjoin_le, le_antisymm, star_mono, star_star, subset_adjoin
-/
theorem star_adjoin_comm (s : Set A) :
    star (NonUnitalAlgebra.adjoin R s) = NonUnitalAlgebra.adjoin R (star s) :=
  have :
    forall t : Set A, NonUnitalAlgebra.adjoin R (star t) <= star (NonUnitalAlgebra.adjoin R t) := fun _ =>
    NonUnitalAlgebra.adjoin_le fun _ hx => NonUnitalAlgebra.subset_adjoin R hx
  le_antisymm (by simpa only [star_star] using NonUnitalSubalgebra.star_mono (this (star s)))
    (this s)

variable {R}

/--
Definition of `starClosure` / `starClosure` 的定义

English:
definition starClosure
  signature: (S : NonUnitalSubalgebra R A)
  body: S ⊔ star S
  star_mem' {a} ha := by
    simpa [← mem_star_iff _ a, ← (@NonUnitalAlgebra.gi R A _ _ _ _ _).l_sup_u _ _, star_adjoin_comm,
      Set.union_comm] using ha

@[simp]

中文:
定义 starClosure
  签名: (S : NonUnital子代数 R A)
  定义体: S ⊔ star S
  star_mem' {a} ha := by
    simpa [← mem_star_iff _ a, ← (@NonUnitalAlgebra.gi R A _ _ _ _ _).l_sup_u _ _, star_adjoin_comm,
      Set.union_comm] using ha

@[simp]
-/
def starClosure (S : NonUnitalSubalgebra R A) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := S ⊔ star S
  star_mem' {a} ha := by
    simpa [← mem_star_iff _ a, ← (@NonUnitalAlgebra.gi R A _ _ _ _ _).l_sup_u _ _, star_adjoin_comm,
      Set.union_comm] using ha

@[simp]
/--
theorem `coe_starClosure` / 定理 `coe_starClosure`

English:
theorem coe_starClosure
  given: (S : NonUnitalSubalgebra R A)
  proof: rfl

@[simp]

中文:
定理 coe_starClosure
  条件: (S : NonUnital子代数 R A)
  证明: rfl

@[simp]
-/
theorem coe_starClosure (S : NonUnitalSubalgebra R A) :
    (S.starClosure : Set A) = (S ⊔ star S : NonUnitalSubalgebra R A) := rfl

@[simp]
/--
theorem `mem_starClosure` / 定理 `mem_starClosure`

English:
theorem mem_starClosure
  given: (S : NonUnitalSubalgebra R A) {x : A}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_starClosure
  条件: (S : NonUnital子代数 R A) {x : A}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_starClosure (S : NonUnitalSubalgebra R A) {x : A} :
    x in S.starClosure ↔ x in S ⊔ star S := Iff.rfl

@[simp]
/--
theorem `starClosure_toNonUnitalSubalgebra` / 定理 `starClosure_toNonUnitalSubalgebra`

English:
theorem starClosure_toNonUnitalSubalgebra
  given: (S : NonUnitalSubalgebra R A)
  proof: rfl

中文:
定理 starClosure_toNonUnitalSubalgebra
  条件: (S : NonUnital子代数 R A)
  证明: rfl
-/
theorem starClosure_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A) :
    S.starClosure.toNonUnitalSubalgebra = S ⊔ star S := rfl

/--
theorem `starClosure_le` / 定理 `starClosure_le`

English:
theorem starClosure_le
  statement: {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebra R A}
  proof: NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff.1
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x in S₂ from h <| (S₁.mem_star_iff _).1 hx) : x in S₂)

中文:
定理 starClosure_le
  结论: {S₁ : NonUnital子代数 R A} {S₂ : 非幺对合子代数 R A}
  证明: NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff.1
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x in S₂ from h <| (S₁.mem_star_iff _).1 hx) : x in S₂)

Depends on / 依赖: NonUnitalStarSubalgebra, NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff, mem_star_iff, star_mem, star_star, sup_le, toNonUnitalSubalgebra_le_iff
-/
theorem starClosure_le {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebra R A}
    (h : S₁ <= S₂.toNonUnitalSubalgebra) : S₁.starClosure <= S₂ :=
NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff.1
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x in S₂ from h <| (S₁.mem_star_iff _).1 hx) : x in S₂)

/--
theorem `starClosure_le_iff` / 定理 `starClosure_le_iff`

English:
theorem starClosure_le_iff
  given: {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebra R A}
  proof: ⟨fun h => le_sup_left.trans h, starClosure_le⟩

@[gcongr, mono]

中文:
定理 starClosure_le_iff
  条件: {S₁ : NonUnital子代数 R A} {S₂ : 非幺对合子代数 R A}
  证明: ⟨fun h => le_sup_left.trans h, starClosure_le⟩

@[gcongr, mono]

Depends on / 依赖: le_sup_left, le_sup_left.trans, starClosure_le
-/
theorem starClosure_le_iff {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebra R A} :
    S₁.starClosure <= S₂ ↔ S₁ <= S₂.toNonUnitalSubalgebra :=
  ⟨fun h => le_sup_left.trans h, starClosure_le⟩

@[gcongr, mono]
/--
theorem `starClosure_mono` / 定理 `starClosure_mono`

English:
theorem starClosure_mono
  statement: Monotone (starClosure (R := R) (A := A))
  proof: fun _ _ h => starClosure_le h.trans le_sup_left

中文:
定理 starClosure_mono
  结论: 递增 (starClosure (R := R) (A := A))
  证明: fun _ _ h => starClosure_le h.trans le_sup_left
-/
theorem starClosure_mono : Monotone (starClosure (R := R) (A := A)) :=
fun _ _ h => starClosure_le h.trans le_sup_left

end NonUnitalSubalgebra

namespace NonUnitalStarAlgebra

variable [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A] [Module R A]
variable [NonUnitalSemiring B] [StarRing B] [Module R B]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

section StarSubAlgebraA

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

open scoped Pointwise

open NonUnitalStarSubalgebra

variable (R)

/--
Definition of `adjoin` / `adjoin` 的定义

English:
definition adjoin
  signature: (s : Set A)
  body: NonUnitalAlgebra.adjoin R (s union star s)
  star_mem' _ := by
    rwa [NonUnitalSubalgebra.mem_carrier, ← NonUnitalSubalgebra.mem_star_iff,
      NonUnitalSubalgebra.star_adjoin_comm, Set.union_star, star_star, Set.union_comm]

中文:
定义 adjoin
  签名: (s : 集合 A)
  定义体: NonUnitalAlgebra.adjoin R (s union star s)
  star_mem' _ := by
    rwa [NonUnitalSubalgebra.mem_carrier, ← NonUnitalSubalgebra.mem_star_iff,
      NonUnitalSubalgebra.star_adjoin_comm, Set.union_star, star_star, Set.union_comm]

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.adjoin, adjoin
-/
def adjoin (s : Set A) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := NonUnitalAlgebra.adjoin R (s union star s)
  star_mem' _ := by
    rwa [NonUnitalSubalgebra.mem_carrier, ← NonUnitalSubalgebra.mem_star_iff,
      NonUnitalSubalgebra.star_adjoin_comm, Set.union_star, star_star, Set.union_comm]

/--
theorem `adjoin_eq_starClosure_adjoin` / 定理 `adjoin_eq_starClosure_adjoin`

English:
theorem adjoin_eq_starClosure_adjoin
  given: (s : Set A)
  proof: toNonUnitalSubalgebra_injective show
    NonUnitalAlgebra.adjoin R (s union star s) =
      NonUnitalAlgebra.adjoin R s ⊔ star (NonUnitalAlgebra.adjoin R s)
    from
      (NonUnitalSubalgebra.star_adjoin_comm R s).symm ▸ NonUnitalAlgebra.adjoin_union s (star s)

中文:
定理 adjoin_eq_starClosure_adjoin
  条件: (s : 集合 A)
  证明: toNonUnitalSubalgebra_injective show
    NonUnitalAlgebra.adjoin R (s union star s) =
      NonUnitalAlgebra.adjoin R s ⊔ star (NonUnitalAlgebra.adjoin R s)
    from
      (NonUnitalSubalgebra.star_adjoin_comm R s).symm ▸ NonUnitalAlgebra.adjoin_union s (star s)

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.adjoin, NonUnitalAlgebra.adjoin_union, NonUnitalSubalgebra, NonUnitalSubalgebra.star_adjoin_comm, adjoin, adjoin_union, star_adjoin_comm, toNonUnitalSubalgebra_injective
-/
theorem adjoin_eq_starClosure_adjoin (s : Set A) :
    adjoin R s = (NonUnitalAlgebra.adjoin R s).starClosure :=
toNonUnitalSubalgebra_injective show
    NonUnitalAlgebra.adjoin R (s union star s) =
      NonUnitalAlgebra.adjoin R s ⊔ star (NonUnitalAlgebra.adjoin R s)
    from
      (NonUnitalSubalgebra.star_adjoin_comm R s).symm ▸ NonUnitalAlgebra.adjoin_union s (star s)

/--
theorem `adjoin_toNonUnitalSubalgebra` / 定理 `adjoin_toNonUnitalSubalgebra`

English:
theorem adjoin_toNonUnitalSubalgebra
  given: (s : Set A)
  proof: rfl

@[simp, aesop safe 20 (rule_sets := [SetLike])]

中文:
定理 adjoin_toNonUnitalSubalgebra
  条件: (s : 集合 A)
  证明: rfl

@[simp, aesop safe 20 (rule_sets := [SetLike])]
-/
theorem adjoin_toNonUnitalSubalgebra (s : Set A) :
    (adjoin R s).toNonUnitalSubalgebra = NonUnitalAlgebra.adjoin R (s union star s) := rfl

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/--
theorem `subset_adjoin` / 定理 `subset_adjoin`

English:
theorem subset_adjoin
  given: (s : Set A)
  statement: s subseteq adjoin R s
  proof: Set.subset_union_left.trans NonUnitalAlgebra.subset_adjoin R

@[simp, aesop safe 20 (rule_sets := [SetLike])]

中文:
定理 subset_adjoin
  条件: (s : 集合 A)
  结论: s subseteq adjoin R s
  证明: Set.subset_union_left.trans NonUnitalAlgebra.subset_adjoin R

@[simp, aesop safe 20 (rule_sets := [SetLike])]

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.subset_adjoin, Set.subset_union_left.trans, subset_adjoin, subset_union_left
-/
theorem subset_adjoin (s : Set A) : s subseteq adjoin R s :=
Set.subset_union_left.trans NonUnitalAlgebra.subset_adjoin R

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/--
theorem `star_subset_adjoin` / 定理 `star_subset_adjoin`

English:
theorem star_subset_adjoin
  given: (s : Set A)
  statement: star s subseteq adjoin R s
  proof: Set.subset_union_right.trans NonUnitalAlgebra.subset_adjoin R

@[aesop 80% (rule_sets := [SetLike])]

中文:
定理 star_subset_adjoin
  条件: (s : 集合 A)
  结论: star s subseteq adjoin R s
  证明: Set.subset_union_right.trans NonUnitalAlgebra.subset_adjoin R

@[aesop 80% (rule_sets := [SetLike])]

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.subset_adjoin, Set.subset_union_right.trans, subset_adjoin, subset_union_right
-/
theorem star_subset_adjoin (s : Set A) : star s subseteq adjoin R s :=
Set.subset_union_right.trans NonUnitalAlgebra.subset_adjoin R

@[aesop 80% (rule_sets := [SetLike])]
/--
theorem `mem_adjoin_of_mem` / 定理 `mem_adjoin_of_mem`

English:
theorem mem_adjoin_of_mem
  given: {s : Set A} {x : A} (hx : x in s)
  statement: x in adjoin R s
  proof: subset_adjoin R s hx

@[simp]

中文:
定理 mem_adjoin_of_mem
  条件: {s : 集合 A} {x : A} (hx : x in s)
  结论: x in adjoin R s
  证明: subset_adjoin R s hx

@[simp]

Depends on / 依赖: subset_adjoin
-/
theorem mem_adjoin_of_mem {s : Set A} {x : A} (hx : x in s) : x in adjoin R s := subset_adjoin R s hx

@[simp]
/--
theorem `self_mem_adjoin_singleton` / 定理 `self_mem_adjoin_singleton`

English:
theorem self_mem_adjoin_singleton
  given: (x : A)
  statement: x in adjoin R ({x} : Set A)
  proof: NonUnitalAlgebra.subset_adjoin R Set.mem_union_left _ (Set.mem_singleton x)

中文:
定理 self_mem_adjoin_singleton
  条件: (x : A)
  结论: x in adjoin R ({x} : 集合 A)
  证明: NonUnitalAlgebra.subset_adjoin R Set.mem_union_left _ (Set.mem_singleton x)

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.subset_adjoin, Set.mem_singleton, Set.mem_union_left, mem_singleton, mem_union_left, subset_adjoin
-/
theorem self_mem_adjoin_singleton (x : A) : x in adjoin R ({x} : Set A) :=
NonUnitalAlgebra.subset_adjoin R Set.mem_union_left _ (Set.mem_singleton x)

/--
theorem `star_self_mem_adjoin_singleton` / 定理 `star_self_mem_adjoin_singleton`

English:
theorem star_self_mem_adjoin_singleton
  given: (x : A)
  statement: star x in adjoin R ({x} : Set A)
  proof: star_mem self_mem_adjoin_singleton R x

@[elab_as_elim]

中文:
定理 star_self_mem_adjoin_singleton
  条件: (x : A)
  结论: star x in adjoin R ({x} : 集合 A)
  证明: star_mem self_mem_adjoin_singleton R x

@[elab_as_elim]

Depends on / 依赖: self_mem_adjoin_singleton, star_mem
-/
theorem star_self_mem_adjoin_singleton (x : A) : star x in adjoin R ({x} : Set A) :=
star_mem self_mem_adjoin_singleton R x

@[elab_as_elim]
/--
lemma `adjoin_induction` / 引理 `adjoin_induction`

English:
lemma adjoin_induction
  statement: {s : Set A} {p : (x : A) -> x in adjoin R s -> Prop}
  proof: by
  refine NonUnitalAlgebra.adjoin_induction (fun x hx => ?_) add zero mul smul ha
  push _ in _ at hx
  obtain (hx | hx) := hx
  · exact mem x hx
  · simpa using star _ (NonUnitalAlgebra.subset_adjoin R (by simpa using Or.inl hx)) (mem _ hx)

中文:
引理 adjoin_induction
  结论: {s : 集合 A} {p : (x : A) -> x in adjoin R s -> 命题}
  证明: by
  refine NonUnitalAlgebra.adjoin_induction (fun x hx => ?_) add zero mul smul ha
  push _ in _ at hx
  obtain (hx | hx) := hx
  · exact mem x hx
  · simpa using star _ (NonUnitalAlgebra.subset_adjoin R (by simpa using Or.inl hx)) (mem _ hx)

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.adjoin_induction, NonUnitalAlgebra.subset_adjoin, Or.inl, adjoin_induction, subset_adjoin
-/
lemma adjoin_induction {s : Set A} {p : (x : A) -> x in adjoin R s -> Prop}
    (mem : forall (x : A) (hx : x in s), p x (subset_adjoin R s hx))
    (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy))
    (zero : p 0 (zero_mem _)) (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy))
    (smul : forall (r : R) x hx, p x hx -> p (r • x) (SMulMemClass.smul_mem r hx))
    (star : forall x hx, p x hx -> p (star x) (star_mem hx))
    {a : A} (ha : a in adjoin R s) : p a ha := by
  refine NonUnitalAlgebra.adjoin_induction (fun x hx => ?_) add zero mul smul ha
  push _ in _ at hx
  obtain (hx | hx) := hx
  · exact mem x hx
  · simpa using star _ (NonUnitalAlgebra.subset_adjoin R (by simpa using Or.inl hx)) (mem _ hx)

variable {R}

/--
theorem `gc` / 定理 `gc`

English:
theorem gc
  statement: GaloisConnection (adjoin R : Set A -> NonUnitalStarSubalgebra R A) (↑)
  proof: by
  intro s S
  rw [← toNonUnitalSubalgebra_le_iff]; rw [adjoin_toNonUnitalSubalgebra]; rw [NonUnitalAlgebra.adjoin_le_iff]; rw [coe_toNonUnitalSubalgebra]
  exact ⟨fun h => Set.subset_union_left.trans h,
    fun h => Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x in S from h hx

中文:
定理 gc
  结论: GaloisConnection (adjoin R : 集合 A -> 非幺对合子代数 R A) (↑)
  证明: by
  intro s S
  rw [← toNonUnitalSubalgebra_le_iff]; rw [adjoin_toNonUnitalSubalgebra]; rw [NonUnitalAlgebra.adjoin_le_iff]; rw [coe_toNonUnitalSubalgebra]
  exact ⟨fun h => Set.subset_union_left.trans h,
    fun h => Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x in S from h hx
-/
protected theorem gc : GaloisConnection (adjoin R : Set A -> NonUnitalStarSubalgebra R A) (↑) := by
  intro s S
  rw [← toNonUnitalSubalgebra_le_iff]; rw [adjoin_toNonUnitalSubalgebra]; rw [NonUnitalAlgebra.adjoin_le_iff]; rw [coe_toNonUnitalSubalgebra]
  exact ⟨fun h => Set.subset_union_left.trans h,
    fun h => Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x in S from h hx)⟩

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (adjoin R : Set A -> NonUnitalStarSubalgebra R A) (↑) where
  body: (adjoin R s).copy s le_antisymm (NonUnitalStarAlgebra.gc.le_u_l s) hs
  gc := NonUnitalStarAlgebra.gc
le_l_u S := (NonUnitalStarAlgebra.gc (S : Set A) (adjoin R S)).1 le_rfl
  choice_eq _ _ := NonUnitalStarSubalgebra.copy_eq _ _ _

中文:
定义 gi
  签名: : Galois嵌入 (adjoin R : 集合 A -> 非幺对合子代数 R A) (↑) where
  定义体: (adjoin R s).copy s le_antisymm (NonUnitalStarAlgebra.gc.le_u_l s) hs
  gc := NonUnitalStarAlgebra.gc
le_l_u S := (NonUnitalStarAlgebra.gc (S : Set A) (adjoin R S)).1 le_rfl
  choice_eq _ _ := NonUnitalStarSubalgebra.copy_eq _ _ _
-/
protected def gi : GaloisInsertion (adjoin R : Set A -> NonUnitalStarSubalgebra R A) (↑) where
choice s hs := (adjoin R s).copy s le_antisymm (NonUnitalStarAlgebra.gc.le_u_l s) hs
  gc := NonUnitalStarAlgebra.gc
le_l_u S := (NonUnitalStarAlgebra.gc (S : Set A) (adjoin R S)).1 le_rfl
  choice_eq _ _ := NonUnitalStarSubalgebra.copy_eq _ _ _

/--
theorem `adjoin_le` / 定理 `adjoin_le`

English:
theorem adjoin_le
  given: {S : NonUnitalStarSubalgebra R A} {s : Set A} (hs : s subseteq S)
  statement: adjoin R s <= S
  proof: NonUnitalStarAlgebra.gc.l_le hs

@[simp]

中文:
定理 adjoin_le
  条件: {S : 非幺对合子代数 R A} {s : 集合 A} (hs : s subseteq S)
  结论: adjoin R s <= S
  证明: NonUnitalStarAlgebra.gc.l_le hs

@[simp]

Depends on / 依赖: NonUnitalStarAlgebra, NonUnitalStarAlgebra.gc.l_le, l_le
-/
theorem adjoin_le {S : NonUnitalStarSubalgebra R A} {s : Set A} (hs : s subseteq S) : adjoin R s <= S :=
  NonUnitalStarAlgebra.gc.l_le hs

@[simp]
/--
theorem `adjoin_le_iff` / 定理 `adjoin_le_iff`

English:
theorem adjoin_le_iff
  given: {S : NonUnitalStarSubalgebra R A} {s : Set A}
  statement: adjoin R s <= S ↔ s subseteq S
  proof: NonUnitalStarAlgebra.gc _ _

@[gcongr]

中文:
定理 adjoin_le_iff
  条件: {S : 非幺对合子代数 R A} {s : 集合 A}
  结论: adjoin R s <= S ↔ s subseteq S
  证明: NonUnitalStarAlgebra.gc _ _

@[gcongr]

Depends on / 依赖: NonUnitalStarAlgebra, NonUnitalStarAlgebra.gc
-/
theorem adjoin_le_iff {S : NonUnitalStarSubalgebra R A} {s : Set A} : adjoin R s <= S ↔ s subseteq S :=
  NonUnitalStarAlgebra.gc _ _

@[gcongr]
/--
theorem `adjoin_mono` / 定理 `adjoin_mono`

English:
theorem adjoin_mono
  given: {s t : Set A} (H : s subseteq t)
  statement: adjoin R s <= adjoin R t
  proof: NonUnitalStarAlgebra.gc.monotone_l H

@[simp]

中文:
定理 adjoin_mono
  条件: {s t : 集合 A} (H : s subseteq t)
  结论: adjoin R s <= adjoin R t
  证明: NonUnitalStarAlgebra.gc.monotone_l H

@[simp]

Depends on / 依赖: NonUnitalStarAlgebra, NonUnitalStarAlgebra.gc.monotone_l, monotone_l
-/
theorem adjoin_mono {s t : Set A} (H : s subseteq t) : adjoin R s <= adjoin R t :=
  NonUnitalStarAlgebra.gc.monotone_l H

@[simp]
/--
lemma `adjoin_eq` / 引理 `adjoin_eq`

English:
lemma adjoin_eq
  given: (s : NonUnitalStarSubalgebra R A)
  statement: adjoin R (s : Set A) = s
  proof: le_antisymm (adjoin_le le_rfl) (subset_adjoin R (s : Set A))

中文:
引理 adjoin_eq
  条件: (s : 非幺对合子代数 R A)
  结论: adjoin R (s : 集合 A) = s
  证明: le_antisymm (adjoin_le le_rfl) (subset_adjoin R (s : Set A))

Depends on / 依赖: adjoin_le, le_antisymm, le_rfl, subset_adjoin
-/
lemma adjoin_eq (s : NonUnitalStarSubalgebra R A) : adjoin R (s : Set A) = s :=
  le_antisymm (adjoin_le le_rfl) (subset_adjoin R (s : Set A))

/--
lemma `adjoin_eq_span` / 引理 `adjoin_eq_span`

English:
lemma adjoin_eq_span
  given: (s : Set A)
  proof: by
  rw [adjoin_toNonUnitalSubalgebra]; rw [NonUnitalAlgebra.adjoin_eq_span]

@[simp]

中文:
引理 adjoin_eq_span
  条件: (s : 集合 A)
  证明: by
  rw [adjoin_toNonUnitalSubalgebra]; rw [NonUnitalAlgebra.adjoin_eq_span]

@[simp]

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.adjoin_eq_span, adjoin_eq_span, adjoin_toNonUnitalSubalgebra
-/
lemma adjoin_eq_span (s : Set A) :
    (adjoin R s).toSubmodule = Submodule.span R (Subsemigroup.closure (s union star s)) := by
  rw [adjoin_toNonUnitalSubalgebra]; rw [NonUnitalAlgebra.adjoin_eq_span]

@[simp]
/--
lemma `span_eq_toSubmodule` / 引理 `span_eq_toSubmodule`

English:
lemma span_eq_toSubmodule
  given: {R} [CommSemiring R] [Module R A] (s : NonUnitalStarSubalgebra R A)
  proof: by
  simp [SetLike.ext'_iff, Submodule.coe_span_eq_self]

中文:
引理 span_eq_toSubmodule
  条件: {R} [交换半环 R] [模 R A] (s : 非幺对合子代数 R A)
  证明: by
  simp [SetLike.ext'_iff, Submodule.coe_span_eq_self]

Depends on / 依赖: SetLike, SetLike.ext, Submodule, Submodule.coe_span_eq_self, _iff, coe_span_eq_self
-/
lemma span_eq_toSubmodule {R} [CommSemiring R] [Module R A] (s : NonUnitalStarSubalgebra R A) :
    Submodule.span R (s : Set A) = s.toSubmodule := by
  simp [SetLike.ext'_iff, Submodule.coe_span_eq_self]

/--
theorem `_root_.NonUnitalSubalgebra.starClosure_eq_adjoin` / 定理 `_root_.NonUnitalSubalgebra.starClosure_eq_adjoin`

English:
theorem _root_.NonUnitalSubalgebra.starClosure_eq_adjoin
  given: (S : NonUnitalSubalgebra R A)
  proof: le_antisymm (NonUnitalSubalgebra.starClosure_le_iff.2 <| subset_adjoin R (S : Set A))
    (adjoin_le (le_sup_left : S <= S ⊔ star S))

中文:
定理 _root_.NonUnital子代数.starClosure_eq_adjoin
  条件: (S : NonUnital子代数 R A)
  证明: le_antisymm (NonUnitalSubalgebra.starClosure_le_iff.2 <| subset_adjoin R (S : Set A))
    (adjoin_le (le_sup_left : S <= S ⊔ star S))

Depends on / 依赖: NonUnitalSubalgebra, NonUnitalSubalgebra.starClosure_le_iff, adjoin_le, le_antisymm, le_sup_left, starClosure_le_iff, subset_adjoin
-/
theorem _root_.NonUnitalSubalgebra.starClosure_eq_adjoin (S : NonUnitalSubalgebra R A) :
    S.starClosure = adjoin R (S : Set A) :=
  le_antisymm (NonUnitalSubalgebra.starClosure_le_iff.2 <| subset_adjoin R (S : Set A))
    (adjoin_le (le_sup_left : S <= S ⊔ star S))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (NonUnitalStarSubalgebra R A)
  body: GaloisInsertion.liftCompleteLattice NonUnitalStarAlgebra.gi

@[simp, norm_cast]

中文:
实例 :
  签名: 完备格 (非幺对合子代数 R A)
  定义体: GaloisInsertion.liftCompleteLattice NonUnitalStarAlgebra.gi

@[simp, norm_cast]

Depends on / 依赖: GaloisInsertion, GaloisInsertion.liftCompleteLattice, NonUnitalStarAlgebra, NonUnitalStarAlgebra.gi, liftCompleteLattice
-/
instance : CompleteLattice (NonUnitalStarSubalgebra R A) :=
  GaloisInsertion.liftCompleteLattice NonUnitalStarAlgebra.gi

@[simp, norm_cast]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : NonUnitalStarSubalgebra R A) : Set A) = Set.univ
  proof: rfl

@[simp]

中文:
定理 coe_top
  结论: ((⊤ : 非幺对合子代数 R A) : 集合 A) = 集合.univ
  证明: rfl

@[simp]
-/
theorem coe_top : ((⊤ : NonUnitalStarSubalgebra R A) : Set A) = Set.univ :=
  rfl

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: {x : A}
  statement: x in (⊤ : NonUnitalStarSubalgebra R A)
  proof: Set.mem_univ x

@[simp]

中文:
定理 mem_top
  条件: {x : A}
  结论: x in (⊤ : 非幺对合子代数 R A)
  证明: Set.mem_univ x

@[simp]

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mem_top {x : A} : x in (⊤ : NonUnitalStarSubalgebra R A) :=
  Set.mem_univ x

@[simp]
/--
theorem `top_toNonUnitalSubalgebra` / 定理 `top_toNonUnitalSubalgebra`

English:
theorem top_toNonUnitalSubalgebra
  proof: by ext; simp

@[simp]

中文:
定理 top_toNonUnitalSubalgebra
  证明: by ext; simp

@[simp]
-/
theorem top_toNonUnitalSubalgebra :
    (⊤ : NonUnitalStarSubalgebra R A).toNonUnitalSubalgebra = ⊤ := by ext; simp

@[simp]
/--
theorem `toNonUnitalSubalgebra_eq_top` / 定理 `toNonUnitalSubalgebra_eq_top`

English:
theorem toNonUnitalSubalgebra_eq_top
  given: {S : NonUnitalStarSubalgebra R A}
  proof: NonUnitalStarSubalgebra.toNonUnitalSubalgebra_injective.eq_iff' top_toNonUnitalSubalgebra

中文:
定理 toNonUnitalSubalgebra_eq_top
  条件: {S : 非幺对合子代数 R A}
  证明: NonUnitalStarSubalgebra.toNonUnitalSubalgebra_injective.eq_iff' top_toNonUnitalSubalgebra

Depends on / 依赖: NonUnitalStarSubalgebra, NonUnitalStarSubalgebra.toNonUnitalSubalgebra_injective.eq_iff, eq_iff, toNonUnitalSubalgebra_injective, top_toNonUnitalSubalgebra
-/
theorem toNonUnitalSubalgebra_eq_top {S : NonUnitalStarSubalgebra R A} :
    S.toNonUnitalSubalgebra = ⊤ ↔ S = ⊤ :=
  NonUnitalStarSubalgebra.toNonUnitalSubalgebra_injective.eq_iff' top_toNonUnitalSubalgebra

/--
theorem `mem_sup_left` / 定理 `mem_sup_left`

English:
theorem mem_sup_left
  given: {S T : NonUnitalStarSubalgebra R A}
  statement: forall {x : A}, x in S -> x in S ⊔ T
  proof: by
  rw [← SetLike.le_def]
  exact le_sup_left

中文:
定理 mem_sup_left
  条件: {S T : 非幺对合子代数 R A}
  结论: 对任意 {x : A}, x in S -> x in S ⊔ T
  证明: by
  rw [← SetLike.le_def]
  exact le_sup_left

Depends on / 依赖: SetLike, SetLike.le_def, le_def, le_sup_left
-/
theorem mem_sup_left {S T : NonUnitalStarSubalgebra R A} : forall {x : A}, x in S -> x in S ⊔ T := by
  rw [← SetLike.le_def]
  exact le_sup_left

/--
theorem `mem_sup_right` / 定理 `mem_sup_right`

English:
theorem mem_sup_right
  given: {S T : NonUnitalStarSubalgebra R A}
  statement: forall {x : A}, x in T -> x in S ⊔ T
  proof: by
  rw [← SetLike.le_def]
  exact le_sup_right

中文:
定理 mem_sup_right
  条件: {S T : 非幺对合子代数 R A}
  结论: 对任意 {x : A}, x in T -> x in S ⊔ T
  证明: by
  rw [← SetLike.le_def]
  exact le_sup_right

Depends on / 依赖: SetLike, SetLike.le_def, le_def, le_sup_right
-/
theorem mem_sup_right {S T : NonUnitalStarSubalgebra R A} : forall {x : A}, x in T -> x in S ⊔ T := by
  rw [← SetLike.le_def]
  exact le_sup_right

/--
theorem `mul_mem_sup` / 定理 `mul_mem_sup`

English:
theorem mul_mem_sup
  given: {S T : NonUnitalStarSubalgebra R A} {x y : A} (hx : x in S) (hy : y in T)
  proof: mul_mem (mem_sup_left hx) (mem_sup_right hy)

中文:
定理 mul_mem_sup
  条件: {S T : 非幺对合子代数 R A} {x y : A} (hx : x in S) (hy : y in T)
  证明: mul_mem (mem_sup_left hx) (mem_sup_right hy)

Depends on / 依赖: mem_sup_left, mem_sup_right, mul_mem
-/
theorem mul_mem_sup {S T : NonUnitalStarSubalgebra R A} {x y : A} (hx : x in S) (hy : y in T) :
    x * y in S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  statement: [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F)
  proof: (NonUnitalStarSubalgebra.gc_map_comap f).l_sup

中文:
定理 map_sup
  结论: [标量塔 R B B] [标量交换类 R B B] [对合模 R B] (f : F)
  证明: (NonUnitalStarSubalgebra.gc_map_comap f).l_sup

Depends on / 依赖: NonUnitalStarSubalgebra, NonUnitalStarSubalgebra.gc_map_comap, gc_map_comap, l_sup
-/
theorem map_sup [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F)
    (S T : NonUnitalStarSubalgebra R A) :
    ((S ⊔ T).map f : NonUnitalStarSubalgebra R B) = S.map f ⊔ T.map f :=
  (NonUnitalStarSubalgebra.gc_map_comap f).l_sup

/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  statement: [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F)
  proof: SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]

中文:
定理 map_inf
  结论: [标量塔 R B B] [标量交换类 R B B] [对合模 R B] (f : F)
  证明: SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, image_inter
-/
theorem map_inf [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F)
    (hf : Function.Injective f) (S T : NonUnitalStarSubalgebra R A) :
    ((S ⊓ T).map f : NonUnitalStarSubalgebra R B) = S.map f ⊓ T.map f :=
  SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (S T : NonUnitalStarSubalgebra R A)
  statement: (↑(S ⊓ T) : Set A) = (S : Set A) inter T
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (S T : 非幺对合子代数 R A)
  结论: (↑(S ⊓ T) : 集合 A) = (S : 集合 A) inter T
  证明: rfl

@[simp]
-/
theorem coe_inf (S T : NonUnitalStarSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Set A) inter T :=
  rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {S T : NonUnitalStarSubalgebra R A} {x : A}
  statement: x in S ⊓ T ↔ x in S ∧ x in T
  proof: Iff.rfl

@[simp]

中文:
定理 mem_inf
  条件: {S T : 非幺对合子代数 R A} {x : A}
  结论: x in S ⊓ T ↔ x in S ∧ x in T
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {S T : NonUnitalStarSubalgebra R A} {x : A} : x in S ⊓ T ↔ x in S ∧ x in T :=
  Iff.rfl

@[simp]
/--
theorem `inf_toNonUnitalSubalgebra` / 定理 `inf_toNonUnitalSubalgebra`

English:
theorem inf_toNonUnitalSubalgebra
  given: (S T : NonUnitalStarSubalgebra R A)
  proof: SetLike.coe_injective coe_inf _ _
  -- it's a bit surprising `rfl` fails here.

@[simp, norm_cast]

中文:
定理 inf_toNonUnitalSubalgebra
  条件: (S T : 非幺对合子代数 R A)
  证明: SetLike.coe_injective coe_inf _ _
  -- it's a bit surprising `rfl` fails here.

@[simp, norm_cast]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_inf, coe_injective
-/
theorem inf_toNonUnitalSubalgebra (S T : NonUnitalStarSubalgebra R A) :
    (S ⊓ T).toNonUnitalSubalgebra = S.toNonUnitalSubalgebra ⊓ T.toNonUnitalSubalgebra :=
SetLike.coe_injective coe_inf _ _
  -- it's a bit surprising `rfl` fails here.

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (NonUnitalStarSubalgebra R A))
  statement: (↑(sInf S) : Set A) = ⋂ s in S, ↑s
  proof: sInf_image

@[simp]

中文:
定理 coe_sInf
  条件: (S : 集合 (非幺对合子代数 R A))
  结论: (↑(sInf S) : 集合 A) = ⋂ s in S, ↑s
  证明: sInf_image

@[simp]

Depends on / 依赖: sInf_image
-/
theorem coe_sInf (S : Set (NonUnitalStarSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s in S, ↑s :=
  sInf_image

@[simp]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (NonUnitalStarSubalgebra R A)} {x : A}
  statement: x in sInf S ↔ forall p in S, x in p
  proof: by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]

中文:
定理 mem_sInf
  条件: {S : 集合 (非幺对合子代数 R A)} {x : A}
  结论: x in sInf S ↔ 对任意 p in S, x in p
  证明: by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]

Depends on / 依赖: Set.mem_iInter, SetLike, SetLike.mem_coe, coe_sInf, mem_coe
-/
theorem mem_sInf {S : Set (NonUnitalStarSubalgebra R A)} {x : A} : x in sInf S ↔ forall p in S, x in p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]
/--
theorem `sInf_toNonUnitalSubalgebra` / 定理 `sInf_toNonUnitalSubalgebra`

English:
theorem sInf_toNonUnitalSubalgebra
  given: (S : Set (NonUnitalStarSubalgebra R A))
  proof: SetLike.coe_injective by simp

@[simp, norm_cast]

中文:
定理 sInf_toNonUnitalSubalgebra
  条件: (S : 集合 (非幺对合子代数 R A))
  证明: SetLike.coe_injective by simp

@[simp, norm_cast]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem sInf_toNonUnitalSubalgebra (S : Set (NonUnitalStarSubalgebra R A)) :
    (sInf S).toNonUnitalSubalgebra = sInf (NonUnitalStarSubalgebra.toNonUnitalSubalgebra '' S) :=
SetLike.coe_injective by simp

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} {S : ι -> NonUnitalStarSubalgebra R A}
  proof: by simp [iInf]

@[simp]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} {S : ι -> 非幺对合子代数 R A}
  证明: by simp [iInf]

@[simp]
-/
theorem coe_iInf {ι : Sort*} {S : ι -> NonUnitalStarSubalgebra R A} :
    (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by simp [iInf]

@[simp]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι : Sort*} {S : ι -> NonUnitalStarSubalgebra R A} {x : A}
  proof: by simp only [iInf, mem_sInf, Set.forall_mem_range]

中文:
定理 mem_iInf
  条件: {ι : 类型层*} {S : ι -> 非幺对合子代数 R A} {x : A}
  证明: by simp only [iInf, mem_sInf, Set.forall_mem_range]

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, mem_sInf
-/
theorem mem_iInf {ι : Sort*} {S : ι -> NonUnitalStarSubalgebra R A} {x : A} :
    x in ⨅ i, S i ↔ forall i, x in S i := by simp only [iInf, mem_sInf, Set.forall_mem_range]

/--
theorem `map_iInf` / 定理 `map_iInf`

English:
theorem map_iInf
  statement: {ι : Sort*} [Nonempty ι]
  proof: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ S)

@[simp]

中文:
定理 map_iInf
  结论: {ι : 类型层*} [非空 ι]
  证明: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ S)

@[simp]

Depends on / 依赖: Set.injOn_of_injective, SetLike, SetLike.coe, SetLike.coe_injective, coe_injective, image_iInter_eq, injOn_of_injective
-/
theorem map_iInf {ι : Sort*} [Nonempty ι]
    [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F)
    (hf : Function.Injective f) (S : ι -> NonUnitalStarSubalgebra R A) :
    ((⨅ i, S i).map f : NonUnitalStarSubalgebra R B) = ⨅ i, (S i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ S)

@[simp]
/--
theorem `iInf_toNonUnitalSubalgebra` / 定理 `iInf_toNonUnitalSubalgebra`

English:
theorem iInf_toNonUnitalSubalgebra
  given: {ι : Sort*} (S : ι -> NonUnitalStarSubalgebra R A)
  proof: SetLike.coe_injective by simp

中文:
定理 iInf_toNonUnitalSubalgebra
  条件: {ι : 类型层*} (S : ι -> 非幺对合子代数 R A)
  证明: SetLike.coe_injective by simp

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem iInf_toNonUnitalSubalgebra {ι : Sort*} (S : ι -> NonUnitalStarSubalgebra R A) :
    (⨅ i, S i).toNonUnitalSubalgebra = ⨅ i, (S i).toNonUnitalSubalgebra :=
SetLike.coe_injective by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (NonUnitalStarSubalgebra R A)
  body: ⟨⊥⟩

中文:
实例 :
  签名: 可居 (非幺对合子代数 R A)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (NonUnitalStarSubalgebra R A) :=
  ⟨⊥⟩

/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: {x : A}
  statement: x in (⊥ : NonUnitalStarSubalgebra R A) ↔ x = 0
  proof: show x in NonUnitalAlgebra.adjoin R (∅ union star ∅ : Set A) ↔ x = 0 by
    rw [Set.star_empty]; rw [Set.union_empty]; rw [NonUnitalAlgebra.adjoin_empty]; rw [NonUnitalAlgebra.mem_bot]

中文:
定理 mem_bot
  条件: {x : A}
  结论: x in (⊥ : 非幺对合子代数 R A) ↔ x = 0
  证明: show x in NonUnitalAlgebra.adjoin R (∅ union star ∅ : Set A) ↔ x = 0 by
    rw [Set.star_empty]; rw [Set.union_empty]; rw [NonUnitalAlgebra.adjoin_empty]; rw [NonUnitalAlgebra.mem_bot]

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.adjoin, NonUnitalAlgebra.adjoin_empty, NonUnitalAlgebra.mem_bot, Set.star_empty, Set.union_empty, adjoin, adjoin_empty, mem_bot, star_empty, union_empty
-/
theorem mem_bot {x : A} : x in (⊥ : NonUnitalStarSubalgebra R A) ↔ x = 0 :=
  show x in NonUnitalAlgebra.adjoin R (∅ union star ∅ : Set A) ↔ x = 0 by
    rw [Set.star_empty]; rw [Set.union_empty]; rw [NonUnitalAlgebra.adjoin_empty]; rw [NonUnitalAlgebra.mem_bot]

/--
theorem `toNonUnitalSubalgebra_bot` / 定理 `toNonUnitalSubalgebra_bot`

English:
theorem toNonUnitalSubalgebra_bot
  proof: by
  ext x
  simp only [mem_bot, NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra, NonUnitalAlgebra.mem_bot]

@[simp, norm_cast]

中文:
定理 toNonUnitalSubalgebra_bot
  证明: by
  ext x
  simp only [mem_bot, NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra, NonUnitalAlgebra.mem_bot]

@[simp, norm_cast]

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.mem_bot, NonUnitalStarSubalgebra, NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra, mem_bot, mem_toNonUnitalSubalgebra
-/
theorem toNonUnitalSubalgebra_bot :
    (⊥ : NonUnitalStarSubalgebra R A).toNonUnitalSubalgebra = ⊥ := by
  ext x
  simp only [mem_bot, NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra, NonUnitalAlgebra.mem_bot]

@[simp, norm_cast]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : NonUnitalStarSubalgebra R A) : Set A) = {0}
  proof: by
  simp only [Set.ext_iff, NonUnitalStarAlgebra.mem_bot, SetLike.mem_coe, Set.mem_singleton_iff,
    forall_const]

中文:
定理 coe_bot
  结论: ((⊥ : 非幺对合子代数 R A) : 集合 A) = {0}
  证明: by
  simp only [Set.ext_iff, NonUnitalStarAlgebra.mem_bot, SetLike.mem_coe, Set.mem_singleton_iff,
    forall_const]

Depends on / 依赖: NonUnitalStarAlgebra, NonUnitalStarAlgebra.mem_bot, Set.ext_iff, Set.mem_singleton_iff, SetLike, SetLike.mem_coe, ext_iff, forall_const, mem_bot, mem_coe, mem_singleton_iff
-/
theorem coe_bot : ((⊥ : NonUnitalStarSubalgebra R A) : Set A) = {0} := by
  simp only [Set.ext_iff, NonUnitalStarAlgebra.mem_bot, SetLike.mem_coe, Set.mem_singleton_iff,
    forall_const]

/--
theorem `eq_top_iff` / 定理 `eq_top_iff`

English:
theorem eq_top_iff
  given: {S : NonUnitalStarSubalgebra R A}
  statement: S = ⊤ ↔ forall x : A, x in S
  proof: ⟨fun h x => by rw [h]; exact mem_top,
    fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

@[simp]

中文:
定理 eq_top_iff
  条件: {S : 非幺对合子代数 R A}
  结论: S = ⊤ ↔ 对任意 x : A, x in S
  证明: ⟨fun h x => by rw [h]; exact mem_top,
    fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

@[simp]

Depends on / 依赖: mem_top
-/
theorem eq_top_iff {S : NonUnitalStarSubalgebra R A} : S = ⊤ ↔ forall x : A, x in S :=
  ⟨fun h x => by rw [h]; exact mem_top,
    fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

@[simp]
/--
theorem `range_id` / 定理 `range_id`

English:
theorem range_id
  statement: NonUnitalStarAlgHom.range (NonUnitalStarAlgHom.id R A) = ⊤
  proof: SetLike.coe_injective Set.range_id

@[simp]

中文:
定理 range_id
  结论: 非幺StarAlg态射.range (非幺StarAlg态射.id R A) = ⊤
  证明: SetLike.coe_injective Set.range_id

@[simp]

Depends on / 依赖: Set.range_id, SetLike, SetLike.coe_injective, coe_injective, range_id
-/
theorem range_id : NonUnitalStarAlgHom.range (NonUnitalStarAlgHom.id R A) = ⊤ :=
  SetLike.coe_injective Set.range_id

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F)
  proof: SetLike.coe_injective by simp [NonUnitalStarSubalgebra.coe_map]

@[simp]

中文:
定理 map_bot
  条件: [标量塔 R B B] [标量交换类 R B B] [对合模 R B] (f : F)
  证明: SetLike.coe_injective by simp [NonUnitalStarSubalgebra.coe_map]

@[simp]

Depends on / 依赖: NonUnitalStarSubalgebra, NonUnitalStarSubalgebra.coe_map, SetLike, SetLike.coe_injective, coe_injective, coe_map
-/
theorem map_bot [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F) :
    (⊥ : NonUnitalStarSubalgebra R A).map f = ⊥ :=
SetLike.coe_injective by simp [NonUnitalStarSubalgebra.coe_map]

@[simp]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  given: [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F)
  proof: eq_top_iff.2 fun _x => mem_top

中文:
定理 comap_top
  条件: [标量塔 R B B] [标量交换类 R B B] [对合模 R B] (f : F)
  证明: eq_top_iff.2 fun _x => mem_top

Depends on / 依赖: eq_top_iff, mem_top
-/
theorem comap_top [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F) :
    (⊤ : NonUnitalStarSubalgebra R B).comap f = ⊤ :=
  eq_top_iff.2 fun _x => mem_top

/--
Definition of `toTop` / `toTop` 的定义

English:
definition toTop
  signature: : A ->⋆ₙₐ[R] (⊤ : NonUnitalStarSubalgebra R A)
  body: NonUnitalStarAlgHom.codRestrict (NonUnitalStarAlgHom.id R A) ⊤ fun _ => mem_top

中文:
定义 toTop
  签名: : A ->⋆ₙₐ[R] (⊤ : 非幺对合子代数 R A)
  定义体: NonUnitalStarAlgHom.codRestrict (NonUnitalStarAlgHom.id R A) ⊤ fun _ => mem_top

Depends on / 依赖: NonUnitalStarAlgHom, NonUnitalStarAlgHom.codRestrict, NonUnitalStarAlgHom.id, codRestrict, mem_top
-/
def toTop : A ->⋆ₙₐ[R] (⊤ : NonUnitalStarSubalgebra R A) :=
  NonUnitalStarAlgHom.codRestrict (NonUnitalStarAlgHom.id R A) ⊤ fun _ => mem_top

end StarSubAlgebraA

/--
theorem `range_eq_top` / 定理 `range_eq_top`

English:
theorem range_eq_top
  statement: [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]
  proof: NonUnitalStarAlgebra.eq_top_iff

@[simp]

中文:
定理 range_eq_top
  结论: [标量塔 R B B] [标量交换类 R B B] [对合模 R B]
  证明: NonUnitalStarAlgebra.eq_top_iff

@[simp]

Depends on / 依赖: NonUnitalStarAlgebra, NonUnitalStarAlgebra.eq_top_iff, eq_top_iff
-/
theorem range_eq_top [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]
    (f : F) : NonUnitalStarAlgHom.range f = (⊤ : NonUnitalStarSubalgebra R B) ↔
      Function.Surjective f :=
  NonUnitalStarAlgebra.eq_top_iff

@[simp]
/--
theorem `map_top` / 定理 `map_top`

English:
theorem map_top
  given: [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] (f : F)
  proof: SetLike.coe_injective Set.image_univ

中文:
定理 map_top
  条件: [标量塔 R A A] [标量交换类 R A A] [对合模 R A] (f : F)
  证明: SetLike.coe_injective Set.image_univ

Depends on / 依赖: Set.image_univ, SetLike, SetLike.coe_injective, coe_injective, image_univ
-/
theorem map_top [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] (f : F) :
    (⊤ : NonUnitalStarSubalgebra R A).map f = NonUnitalStarAlgHom.range f :=
  SetLike.coe_injective Set.image_univ

end NonUnitalStarAlgebra

namespace NonUnitalStarSubalgebra

open NonUnitalStarAlgebra

variable [CommSemiring R]
variable [NonUnitalSemiring A] [StarRing A] [Module R A]
variable [NonUnitalSemiring B] [StarRing B] [Module R B]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]
variable (S : NonUnitalStarSubalgebra R A)

section StarSubalgebra

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {S T : NonUnitalStarSubalgebra R A} (h : S <= T)
  body: NonUnitalSubalgebra.inclusion h
  map_star' _ := rfl

中文:
定义 inclusion
  签名: {S T : 非幺对合子代数 R A} (h : S <= T)
  定义体: NonUnitalSubalgebra.inclusion h
  map_star' _ := rfl

Depends on / 依赖: NonUnitalSubalgebra, NonUnitalSubalgebra.inclusion, inclusion
-/
def inclusion {S T : NonUnitalStarSubalgebra R A} (h : S <= T) : S ->⋆ₙₐ[R] T where
  toNonUnitalAlgHom := NonUnitalSubalgebra.inclusion h
  map_star' _ := rfl

/--
theorem `inclusion_injective` / 定理 `inclusion_injective`

English:
theorem inclusion_injective
  given: {S T : NonUnitalStarSubalgebra R A} (h : S <= T)
  proof: fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]

中文:
定理 inclusion_injective
  条件: {S T : 非幺对合子代数 R A} (h : S <= T)
  证明: fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, Subtype.mk.inj
-/
theorem inclusion_injective {S T : NonUnitalStarSubalgebra R A} (h : S <= T) :
    Function.Injective (inclusion h) :=
  fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]
/--
theorem `inclusion_self` / 定理 `inclusion_self`

English:
theorem inclusion_self
  given: {S : NonUnitalStarSubalgebra R A}
  proof: NonUnitalAlgHom.ext fun _x => Subtype.ext rfl

@[simp]

中文:
定理 inclusion_self
  条件: {S : 非幺对合子代数 R A}
  证明: NonUnitalAlgHom.ext fun _x => Subtype.ext rfl

@[simp]

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.ext, Subtype, Subtype.ext
-/
theorem inclusion_self {S : NonUnitalStarSubalgebra R A} :
    inclusion (le_refl S) = NonUnitalAlgHom.id R S :=
  NonUnitalAlgHom.ext fun _x => Subtype.ext rfl

@[simp]
/--
theorem `inclusion_mk` / 定理 `inclusion_mk`

English:
theorem inclusion_mk
  given: {S T : NonUnitalStarSubalgebra R A} (h : S <= T) (x : A) (hx : x in S)
  proof: rfl

中文:
定理 inclusion_mk
  条件: {S T : 非幺对合子代数 R A} (h : S <= T) (x : A) (hx : x in S)
  证明: rfl
-/
theorem inclusion_mk {S T : NonUnitalStarSubalgebra R A} (h : S <= T) (x : A) (hx : x in S) :
    inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl

/--
theorem `inclusion_right` / 定理 `inclusion_right`

English:
theorem inclusion_right
  given: {S T : NonUnitalStarSubalgebra R A} (h : S <= T) (x : T) (m : (x : A) in S)
  proof: Subtype.ext rfl

@[simp]

中文:
定理 inclusion_right
  条件: {S T : 非幺对合子代数 R A} (h : S <= T) (x : T) (m : (x : A) in S)
  证明: Subtype.ext rfl

@[simp]

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem inclusion_right {S T : NonUnitalStarSubalgebra R A} (h : S <= T) (x : T) (m : (x : A) in S) :
    inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl

@[simp]
/--
theorem `inclusion_inclusion` / 定理 `inclusion_inclusion`

English:
theorem inclusion_inclusion
  statement: {S T U : NonUnitalStarSubalgebra R A} (hst : S <= T) (htu : T <= U)
  proof: Subtype.ext rfl

@[simp]

中文:
定理 inclusion_inclusion
  结论: {S T U : 非幺对合子代数 R A} (hst : S <= T) (htu : T <= U)
  证明: Subtype.ext rfl

@[simp]

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem inclusion_inclusion {S T U : NonUnitalStarSubalgebra R A} (hst : S <= T) (htu : T <= U)
    (x : S) : inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
  Subtype.ext rfl

@[simp]
/--
theorem `val_inclusion` / 定理 `val_inclusion`

English:
theorem val_inclusion
  given: {S T : NonUnitalStarSubalgebra R A} (h : S <= T) (s : S)
  proof: rfl

中文:
定理 val_inclusion
  条件: {S T : 非幺对合子代数 R A} (h : S <= T) (s : S)
  证明: rfl
-/
theorem val_inclusion {S T : NonUnitalStarSubalgebra R A} (h : S <= T) (s : S) :
    (inclusion h s : A) = s :=
  rfl

variable [StarRing R]
variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]

/--
lemma `_root_.NonUnitalStarAlgHom.map_adjoin` / 引理 `_root_.NonUnitalStarAlgHom.map_adjoin`

English:
lemma _root_.NonUnitalStarAlgHom.map_adjoin
  given: (f : F) (s : Set A)
  proof: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) NonUnitalStarAlgebra.gi.gc
    NonUnitalStarAlgebra.gi.gc fun _t => rfl

@[simp]

中文:
引理 _root_.非幺StarAlg态射.map_adjoin
  条件: (f : F) (s : 集合 A)
  证明: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) NonUnitalStarAlgebra.gi.gc
    NonUnitalStarAlgebra.gi.gc fun _t => rfl

@[simp]

Depends on / 依赖: NonUnitalStarAlgebra, NonUnitalStarAlgebra.gi.gc, Set.image_preimage.l_comm_of_u_comm, gc_map_comap, image_preimage, l_comm_of_u_comm
-/
lemma _root_.NonUnitalStarAlgHom.map_adjoin (f : F) (s : Set A) :
    map f (adjoin R s) = adjoin R (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) NonUnitalStarAlgebra.gi.gc
    NonUnitalStarAlgebra.gi.gc fun _t => rfl

@[simp]
/--
lemma `_root_.NonUnitalStarAlgHom.map_adjoin_singleton` / 引理 `_root_.NonUnitalStarAlgHom.map_adjoin_singleton`

English:
lemma _root_.NonUnitalStarAlgHom.map_adjoin_singleton
  given: (f : F) (x : A)
  proof: by
  simp [NonUnitalStarAlgHom.map_adjoin]

中文:
引理 _root_.非幺StarAlg态射.map_adjoin_singleton
  条件: (f : F) (x : A)
  证明: by
  simp [NonUnitalStarAlgHom.map_adjoin]

Depends on / 依赖: NonUnitalStarAlgHom, NonUnitalStarAlgHom.map_adjoin, map_adjoin
-/
lemma _root_.NonUnitalStarAlgHom.map_adjoin_singleton (f : F) (x : A) :
    map f (adjoin R {x}) = adjoin R {f x} := by
  simp [NonUnitalStarAlgHom.map_adjoin]

/--
Instance `subsingleton_of_subsingleton` / 实例 `subsingleton_of_subsingleton`

English:
instance subsingleton_of_subsingleton
  signature: [Subsingleton A]
  body: ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩

中文:
实例 subsingleton_of_subsingleton
  签名: [子单例 A]
  定义体: ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, zero_mem
-/
instance subsingleton_of_subsingleton [Subsingleton A] :
    Subsingleton (NonUnitalStarSubalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩

/--
Instance `_root_.NonUnitalStarAlgHom.subsingleton` / 实例 `_root_.NonUnitalStarAlgHom.subsingleton`

English:
instance _root_.NonUnitalStarAlgHom.subsingleton
  signature: [Subsingleton (NonUnitalStarSubalgebra R A)]
  body: ⟨fun f g => NonUnitalStarAlgHom.ext fun a =>
    have : a in (⊥ : NonUnitalStarSubalgebra R A) :=
      Subsingleton.elim (⊤ : NonUnitalStarSubalgebra R A) ⊥ ▸ mem_top
    (mem_bot.mp this).symm ▸ (map_zero f).trans (map_zero g).symm⟩

中文:
实例 _root_.非幺StarAlg态射.subsingleton
  签名: [子单例 (非幺对合子代数 R A)]
  定义体: ⟨fun f g => NonUnitalStarAlgHom.ext fun a =>
    have : a in (⊥ : NonUnitalStarSubalgebra R A) :=
      Subsingleton.elim (⊤ : NonUnitalStarSubalgebra R A) ⊥ ▸ mem_top
    (mem_bot.mp this).symm ▸ (map_zero f).trans (map_zero g).symm⟩

Depends on / 依赖: NonUnitalStarAlgHom, NonUnitalStarAlgHom.ext, NonUnitalStarSubalgebra, Subsingleton, Subsingleton.elim, map_zero, mem_bot, mem_bot.mp, mem_top
-/
instance _root_.NonUnitalStarAlgHom.subsingleton [Subsingleton (NonUnitalStarSubalgebra R A)] :
    Subsingleton (A ->⋆ₙₐ[R] B) :=
  ⟨fun f g => NonUnitalStarAlgHom.ext fun a =>
    have : a in (⊥ : NonUnitalStarSubalgebra R A) :=
      Subsingleton.elim (⊤ : NonUnitalStarSubalgebra R A) ⊥ ▸ mem_top
    (mem_bot.mp this).symm ▸ (map_zero f).trans (map_zero g).symm⟩

end StarSubalgebra

/--
theorem `range_val` / 定理 `range_val`

English:
theorem range_val
  statement: NonUnitalStarAlgHom.range (NonUnitalStarSubalgebraClass.subtype S) = S
  proof: ext Set.ext_iff.1
    (NonUnitalStarAlgHom.coe_range (NonUnitalStarSubalgebraClass.subtype S)).trans Subtype.range_val

中文:
定理 range_val
  结论: 非幺StarAlg态射.range (NonUnitalStarSubalgebraClass.subtype S) = S
  证明: ext Set.ext_iff.1
    (NonUnitalStarAlgHom.coe_range (NonUnitalStarSubalgebraClass.subtype S)).trans Subtype.range_val

Depends on / 依赖: NonUnitalStarAlgHom, NonUnitalStarAlgHom.coe_range, NonUnitalStarSubalgebraClass, NonUnitalStarSubalgebraClass.subtype, Set.ext_iff, Subtype, Subtype.range_val, coe_range, ext_iff, range_val, subtype
-/
theorem range_val : NonUnitalStarAlgHom.range (NonUnitalStarSubalgebraClass.subtype S) = S :=
ext Set.ext_iff.1
    (NonUnitalStarAlgHom.coe_range (NonUnitalStarSubalgebraClass.subtype S)).trans Subtype.range_val

section Prod

variable (S₁ : NonUnitalStarSubalgebra R B)

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : NonUnitalStarSubalgebra R (A × B)
  body: { S.toNonUnitalSubalgebra.prod S₁.toNonUnitalSubalgebra with
    carrier := S ×ˢ S₁
    star_mem' := fun hx => ⟨star_mem hx.1, star_mem hx.2⟩ }

@[simp, norm_cast]

中文:
定义 乘积
  签名: : 非幺对合子代数 R (A × B)
  定义体: { S.toNonUnitalSubalgebra.prod S₁.toNonUnitalSubalgebra with
    carrier := S ×ˢ S₁
    star_mem' := fun hx => ⟨star_mem hx.1, star_mem hx.2⟩ }

@[simp, norm_cast]

Depends on / 依赖: S.toNonUnitalSubalgebra.prod, carrier, star_mem, toNonUnitalSubalgebra
-/
def prod : NonUnitalStarSubalgebra R (A × B) :=
  { S.toNonUnitalSubalgebra.prod S₁.toNonUnitalSubalgebra with
    carrier := S ×ˢ S₁
    star_mem' := fun hx => ⟨star_mem hx.1, star_mem hx.2⟩ }

@[simp, norm_cast]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  statement: (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ S₁
  proof: rfl

中文:
定理 coe_prod
  结论: (乘积 S S₁ : 集合 (A × B)) = (S : 集合 A) ×ˢ S₁
  证明: rfl
-/
theorem coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ S₁ :=
  rfl

/--
theorem `prod_toNonUnitalSubalgebra` / 定理 `prod_toNonUnitalSubalgebra`

English:
theorem prod_toNonUnitalSubalgebra
  proof: rfl

@[simp]

中文:
定理 prod_toNonUnitalSubalgebra
  证明: rfl

@[simp]
-/
theorem prod_toNonUnitalSubalgebra :
    (S.prod S₁).toNonUnitalSubalgebra = S.toNonUnitalSubalgebra.prod S₁.toNonUnitalSubalgebra :=
  rfl

@[simp]
/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {S : NonUnitalStarSubalgebra R A} {S₁ : NonUnitalStarSubalgebra R B} {x : A × B}
  proof: Set.mem_prod

中文:
定理 mem_prod
  条件: {S : 非幺对合子代数 R A} {S₁ : 非幺对合子代数 R B} {x : A × B}
  证明: Set.mem_prod

Depends on / 依赖: Set.mem_prod, mem_prod
-/
theorem mem_prod {S : NonUnitalStarSubalgebra R A} {S₁ : NonUnitalStarSubalgebra R B} {x : A × B} :
    x in prod S S₁ ↔ x.1 in S ∧ x.2 in S₁ :=
  Set.mem_prod

/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: {S T : NonUnitalStarSubalgebra R A} {S₁ T₁ : NonUnitalStarSubalgebra R B}
  proof: Set.prod_mono

中文:
定理 prod_mono
  条件: {S T : 非幺对合子代数 R A} {S₁ T₁ : 非幺对合子代数 R B}
  证明: Set.prod_mono

Depends on / 依赖: Set.prod_mono, prod_mono
-/
theorem prod_mono {S T : NonUnitalStarSubalgebra R A} {S₁ T₁ : NonUnitalStarSubalgebra R B} :
    S <= T -> S₁ <= T₁ -> prod S S₁ <= prod T T₁ :=
  Set.prod_mono

variable [StarRing R]
variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]

@[simp]
/--
theorem `prod_top` / 定理 `prod_top`

English:
theorem prod_top
  statement: (prod ⊤ ⊤ : NonUnitalStarSubalgebra R (A × B)) = ⊤
  proof: by ext; simp

@[simp]

中文:
定理 prod_top
  结论: (乘积 ⊤ ⊤ : 非幺对合子代数 R (A × B)) = ⊤
  证明: by ext; simp

@[simp]
-/
theorem prod_top : (prod ⊤ ⊤ : NonUnitalStarSubalgebra R (A × B)) = ⊤ := by ext; simp

@[simp]
/--
theorem `prod_inf_prod` / 定理 `prod_inf_prod`

English:
theorem prod_inf_prod
  given: {S T : NonUnitalStarSubalgebra R A} {S₁ T₁ : NonUnitalStarSubalgebra R B}
  proof: SetLike.coe_injective Set.prod_inter_prod

中文:
定理 prod_inf_prod
  条件: {S T : 非幺对合子代数 R A} {S₁ T₁ : 非幺对合子代数 R B}
  证明: SetLike.coe_injective Set.prod_inter_prod

Depends on / 依赖: Set.prod_inter_prod, SetLike, SetLike.coe_injective, coe_injective, prod_inter_prod
-/
theorem prod_inf_prod {S T : NonUnitalStarSubalgebra R A} {S₁ T₁ : NonUnitalStarSubalgebra R B} :
    S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
  SetLike.coe_injective Set.prod_inter_prod

end Prod

section iSupLift

variable {ι : Type*}
variable [StarRing R] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

section StarSubalgebraB

variable [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]

/--
theorem `coe_iSup_of_directed` / 定理 `coe_iSup_of_directed`

English:
theorem coe_iSup_of_directed
  statement: [Nonempty ι] {S : ι -> NonUnitalStarSubalgebra R A}
  proof: let K : NonUnitalStarSubalgebra R A :=
    { __ := NonUnitalSubalgebra.copy _ _ (NonUnitalSubalgebra.coe_iSup_of_directed dir).symm
      star_mem' := fun hx =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, star_mem (s := S i) hi⟩ }
  have : iSup S = K := le_antisymm (iSup_

中文:
定理 coe_iSup_of_directed
  结论: [非空 ι] {S : ι -> 非幺对合子代数 R A}
  证明: let K : NonUnitalStarSubalgebra R A :=
    { __ := NonUnitalSubalgebra.copy _ _ (NonUnitalSubalgebra.coe_iSup_of_directed dir).symm
      star_mem' := fun hx =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, star_mem (s := S i) hi⟩ }
  have : iSup S = K := le_antisymm (iSup_

Depends on / 依赖: NonUnitalStarSubalgebra, NonUnitalSubalgebra, NonUnitalSubalgebra.coe_iSup_of_directed, NonUnitalSubalgebra.copy, Set.iUnion_subset, Set.mem_iUnion, coe_iSup_of_directed, iSup_le, iUnion_subset, le_antisymm, le_iSup, mem_iUnion, star_mem, this.symm
-/
theorem coe_iSup_of_directed [Nonempty ι] {S : ι -> NonUnitalStarSubalgebra R A}
    (dir : Directed (· <= ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A) :=
  let K : NonUnitalStarSubalgebra R A :=
    { __ := NonUnitalSubalgebra.copy _ _ (NonUnitalSubalgebra.coe_iSup_of_directed dir).symm
      star_mem' := fun hx =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, star_mem (s := S i) hi⟩ }
  have : iSup S = K := le_antisymm (iSup_le fun i => le_iSup (fun i => (S i : Set A)) i)
    (Set.iUnion_subset fun _ => le_iSup S _)
  this.symm ▸ rfl

/--
theorem `isMulCommutative_iSup` / 定理 `isMulCommutative_iSup`

English:
theorem isMulCommutative_iSup
  statement: [Nonempty ι] {S : ι -> NonUnitalStarSubalgebra R A}
  proof: by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, NonUnitalSubsemiring.coe_iSup_of_directed dir,
    coe_iSup_of_directed dir] using NonUnitalSubsemiring.isMulCommutative_iSup dir

中文:
定理 isMulCommutative_iSup
  结论: [非空 ι] {S : ι -> 非幺对合子代数 R A}
  证明: by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, NonUnitalSubsemiring.coe_iSup_of_directed dir,
    coe_iSup_of_directed dir] using NonUnitalSubsemiring.isMulCommutative_iSup dir

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.coe_iSup_of_directed, NonUnitalSubsemiring.isMulCommutative_iSup, SetLike, SetLike.mem_coe, coe_iSup_of_directed, isMulCommutative_iSup, isMulCommutative_iff, mem_coe
-/
theorem isMulCommutative_iSup [Nonempty ι] {S : ι -> NonUnitalStarSubalgebra R A}
    [hS : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) :
    IsMulCommutative (⨆ i, S i : NonUnitalStarSubalgebra R A) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, NonUnitalSubsemiring.coe_iSup_of_directed dir,
    coe_iSup_of_directed dir] using NonUnitalSubsemiring.isMulCommutative_iSup dir

/--
Instance `instIsMulCommutative_iSup` / 实例 `instIsMulCommutative_iSup`

English:
instance instIsMulCommutative_iSup
  signature: [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
  body: isMulCommutative_iSup S.monotone.directed_le

中文:
实例 instIsMulCommutative_iSup
  签名: [非空 ι] [预序 ι] [IsDirectedOrder ι]
  定义体: isMulCommutative_iSup S.monotone.directed_le

Depends on / 依赖: S.monotone.directed_le, directed_le, isMulCommutative_iSup, monotone
-/
instance instIsMulCommutative_iSup [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι ->o NonUnitalStarSubalgebra R A} [hS : forall i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : NonUnitalStarSubalgebra R A) :=
  isMulCommutative_iSup S.monotone.directed_le

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `iSupLift` / `iSupLift` 的定义

English:
definition iSupLift
  signature: [Nonempty ι] (K : ι -> NonUnitalStarSubalgebra R A)
  body: by
  subst hT
  exact
    { toFun :=
        Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x)
          (fun i j x hxi hxj => by
            let ⟨k, hik, hjk⟩ := dir i j
            rw [hf i k hik]; rw [hf j k hjk]
            rfl)
          _ (by rw [coe_iSup_of_directed dir])
      map_zero' :=

中文:
定义 iSupLift
  签名: [非空 ι] (K : ι -> 非幺对合子代数 R A)
  定义体: by
  subst hT
  exact
    { toFun :=
        Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x)
          (fun i j x hxi hxj => by
            let ⟨k, hik, hjk⟩ := dir i j
            rw [hf i k hik]; rw [hf j k hjk]
            rfl)
          _ (by rw [coe_iSup_of_directed dir])
      map_zero' :=

Depends on / 依赖: Eq.ndrec, Function, Function.comp_apply, NonUnitalAlgHom, NonUnitalAlgHom.coe_comp, Set.iUnionLift, Set.iUnionLift_const, SetLike, SetLike.coe_sort_coe, coe_comp, coe_iSup_of_directed, coe_sort_coe, comp_apply, eq_mpr_eq_cast, iUnionLift, iUnionLift_const, id_eq, inclusion_mk, map_mul, map_zero
-/
noncomputable def iSupLift [Nonempty ι] (K : ι -> NonUnitalStarSubalgebra R A)
    (dir : Directed (· <= ·) K) (f : forall i, K i ->⋆ₙₐ[R] B)
    (hf : forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h))
    (T : NonUnitalStarSubalgebra R A) (hT : T = iSup K) : ↥T ->⋆ₙₐ[R] B := by
  subst hT
  exact
    { toFun :=
        Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x)
          (fun i j x hxi hxj => by
            let ⟨k, hik, hjk⟩ := dir i j
            rw [hf i k hik]; rw [hf j k hjk]
            rfl)
          _ (by rw [coe_iSup_of_directed dir])
      map_zero' := by
        dsimp only [SetLike.coe_sort_coe, NonUnitalAlgHom.coe_comp, Function.comp_apply,
          inclusion_mk, Eq.ndrec, id_eq, eq_mpr_eq_cast]
        exact Set.iUnionLift_const _ (fun i : ι => (0 : K i)) (fun _ => rfl) _ (by simp)
      map_mul' := by
        dsimp only [SetLike.coe_sort_coe, NonUnitalAlgHom.coe_comp, Function.comp_apply,
          inclusion_mk, Eq.ndrec, id_eq, eq_mpr_eq_cast, ZeroMemClass.coe_zero,
          AddSubmonoid.mk_add_mk, Set.inclusion_mk]
        apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· * ·))
        all_goals simp
      map_add' := by
        dsimp only [SetLike.coe_sort_coe, NonUnitalAlgHom.coe_comp, Function.comp_apply,
          inclusion_mk, Eq.ndrec, id_eq, eq_mpr_eq_cast]
        apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· + ·))
        all_goals simp
      map_smul' := fun r => by
        dsimp only [SetLike.coe_sort_coe, NonUnitalAlgHom.coe_comp, Function.comp_apply,
          inclusion_mk, Eq.ndrec, id_eq, eq_mpr_eq_cast]
        apply Set.iUnionLift_unary (coe_iSup_of_directed dir) _ (fun _ x => r • x)
          (fun _ _ => rfl)
        all_goals simp
      map_star' := by
        dsimp only [SetLike.coe_sort_coe, NonUnitalStarAlgHom.comp_apply, inclusion_mk, Eq.ndrec,
          id_eq, eq_mpr_eq_cast, ZeroMemClass.coe_zero, AddSubmonoid.mk_add_mk, Set.inclusion_mk,
          MulMemClass.mk_mul_mk, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
          DistribMulActionHom.toFun_eq_coe, NonUnitalAlgHom.coe_to_distribMulActionHom,
          NonUnitalAlgHom.coe_mk]
        apply Set.iUnionLift_unary (coe_iSup_of_directed dir) _ (fun _ x => star x)
          (fun _ _ => rfl)
        all_goals simp [map_star] }

end StarSubalgebraB

variable [Nonempty ι] {K : ι -> NonUnitalStarSubalgebra R A} {dir : Directed (· <= ·) K}
  {f : forall i, K i ->⋆ₙₐ[R] B} {hf : forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h)}
  {T : NonUnitalStarSubalgebra R A} {hT : T = iSup K}

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `iSupLift_inclusion` / 定理 `iSupLift_inclusion`

English:
theorem iSupLift_inclusion
  given: {i : ι} (x : K i) (h : K i <= T)
  proof: by
  subst T
  dsimp [iSupLift]
  apply Set.iUnionLift_inclusion
  exact h

@[simp]

中文:
定理 iSupLift_inclusion
  条件: {i : ι} (x : K i) (h : K i <= T)
  证明: by
  subst T
  dsimp [iSupLift]
  apply Set.iUnionLift_inclusion
  exact h

@[simp]

Depends on / 依赖: Set.iUnionLift_inclusion, iSupLift, iUnionLift_inclusion
-/
theorem iSupLift_inclusion {i : ι} (x : K i) (h : K i <= T) :
    iSupLift K dir f hf T hT (inclusion h x) = f i x := by
  subst T
  dsimp [iSupLift]
  apply Set.iUnionLift_inclusion
  exact h

@[simp]
/--
theorem `iSupLift_comp_inclusion` / 定理 `iSupLift_comp_inclusion`

English:
theorem iSupLift_comp_inclusion
  given: {i : ι} (h : K i <= T)
  proof: by ext; simp

中文:
定理 iSupLift_comp_inclusion
  条件: {i : ι} (h : K i <= T)
  证明: by ext; simp
-/
theorem iSupLift_comp_inclusion {i : ι} (h : K i <= T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `iSupLift_mk` / 定理 `iSupLift_mk`

English:
theorem iSupLift_mk
  given: {i : ι} (x : K i) (hx : (x : A) in T)
  proof: by
  subst hT
  dsimp [iSupLift]
  apply Set.iUnionLift_mk

中文:
定理 iSupLift_mk
  条件: {i : ι} (x : K i) (hx : (x : A) in T)
  证明: by
  subst hT
  dsimp [iSupLift]
  apply Set.iUnionLift_mk

Depends on / 依赖: Set.iUnionLift_mk, iSupLift, iUnionLift_mk
-/
theorem iSupLift_mk {i : ι} (x : K i) (hx : (x : A) in T) :
    iSupLift K dir f hf T hT ⟨x, hx⟩ = f i x := by
  subst hT
  dsimp [iSupLift]
  apply Set.iUnionLift_mk

set_option backward.isDefEq.respectTransparency false in
/--
theorem `iSupLift_of_mem` / 定理 `iSupLift_of_mem`

English:
theorem iSupLift_of_mem
  given: {i : ι} (x : T) (hx : (x : A) in K i)
  proof: by
  subst hT
  dsimp [iSupLift]
  apply Set.iUnionLift_of_mem

中文:
定理 iSupLift_of_mem
  条件: {i : ι} (x : T) (hx : (x : A) in K i)
  证明: by
  subst hT
  dsimp [iSupLift]
  apply Set.iUnionLift_of_mem

Depends on / 依赖: Set.iUnionLift_of_mem, iSupLift, iUnionLift_of_mem
-/
theorem iSupLift_of_mem {i : ι} (x : T) (hx : (x : A) in K i) :
    iSupLift K dir f hf T hT x = f i ⟨x, hx⟩ := by
  subst hT
  dsimp [iSupLift]
  apply Set.iUnionLift_of_mem

end iSupLift

section Center

variable (R A)
variable [IsScalarTower R A A] [SMulCommClass R A A]

/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: : NonUnitalStarSubalgebra R A where
  body: NonUnitalSubalgebra.center R A
  star_mem' := Set.star_mem_center

@[norm_cast]

中文:
定义 center
  签名: : 非幺对合子代数 R A where
  定义体: NonUnitalSubalgebra.center R A
  star_mem' := Set.star_mem_center

@[norm_cast]

Depends on / 依赖: NonUnitalSubalgebra, NonUnitalSubalgebra.center, center
-/
def center : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := NonUnitalSubalgebra.center R A
  star_mem' := Set.star_mem_center

@[norm_cast]
/--
theorem `coe_center` / 定理 `coe_center`

English:
theorem coe_center
  statement: (center R A : Set A) = Set.center A
  proof: rfl

@[simp]

中文:
定理 coe_center
  结论: (center R A : 集合 A) = 集合.center A
  证明: rfl

@[simp]
-/
theorem coe_center : (center R A : Set A) = Set.center A :=
  rfl

@[simp]
/--
theorem `center_toNonUnitalSubalgebra` / 定理 `center_toNonUnitalSubalgebra`

English:
theorem center_toNonUnitalSubalgebra
  proof: rfl

@[simp]

中文:
定理 center_toNonUnitalSubalgebra
  证明: rfl

@[simp]
-/
theorem center_toNonUnitalSubalgebra :
    (center R A).toNonUnitalSubalgebra = NonUnitalSubalgebra.center R A :=
  rfl

@[simp]
/--
theorem `center_eq_top` / 定理 `center_eq_top`

English:
theorem center_eq_top
  statement: (A : Type*) [StarRing R] [NonUnitalCommSemiring A] [StarRing A] [Module R A]
  proof: SetLike.coe_injective (Set.center_eq_univ A)

中文:
定理 center_eq_top
  结论: (A : 类型) [对合环 R] [非幺交换半环 A] [对合环 A] [模 R A]
  证明: SetLike.coe_injective (Set.center_eq_univ A)

Depends on / 依赖: Set.center_eq_univ, SetLike, SetLike.coe_injective, center_eq_univ, coe_injective
-/
theorem center_eq_top (A : Type*) [StarRing R] [NonUnitalCommSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)

variable {R A}

/--
Instance `instNonUnitalCommSemiring` / 实例 `instNonUnitalCommSemiring`

English:
instance instNonUnitalCommSemiring
  signature: : NonUnitalCommSemiring (center R A)
  body: fast_instance% NonUnitalSubalgebra.center.instNonUnitalCommSemiring

中文:
实例 instNonUnitalCommSemiring
  签名: : 非幺交换半环 (center R A)
  定义体: fast_instance% NonUnitalSubalgebra.center.instNonUnitalCommSemiring

Depends on / 依赖: NonUnitalSubalgebra, NonUnitalSubalgebra.center.instNonUnitalCommSemiring, center, fast_instance, instNonUnitalCommSemiring
-/
instance instNonUnitalCommSemiring : NonUnitalCommSemiring (center R A) :=
  fast_instance% NonUnitalSubalgebra.center.instNonUnitalCommSemiring

/--
Instance `instNonUnitalCommRing` / 实例 `instNonUnitalCommRing`

English:
instance instNonUnitalCommRing
  signature: {A : Type*} [NonUnitalRing A] [StarRing A] [Module R A]
  body: fast_instance% NonUnitalSubalgebra.center.instNonUnitalCommRing

中文:
实例 instNonUnitalCommRing
  签名: {A : 类型} [非幺环 A] [对合环 A] [模 R A]
  定义体: fast_instance% NonUnitalSubalgebra.center.instNonUnitalCommRing

Depends on / 依赖: NonUnitalSubalgebra, NonUnitalSubalgebra.center.instNonUnitalCommRing, center, fast_instance, instNonUnitalCommRing
-/
instance instNonUnitalCommRing {A : Type*} [NonUnitalRing A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : NonUnitalCommRing (center R A) :=
  fast_instance% NonUnitalSubalgebra.center.instNonUnitalCommRing

/--
theorem `mem_center_iff` / 定理 `mem_center_iff`

English:
theorem mem_center_iff
  given: {a : A}
  statement: a in center R A ↔ forall b : A, b * a = a * b
  proof: Subsemigroup.mem_center_iff

中文:
定理 mem_center_iff
  条件: {a : A}
  结论: a in center R A ↔ 对任意 b : A, b * a = a * b
  证明: Subsemigroup.mem_center_iff

Depends on / 依赖: Subsemigroup, Subsemigroup.mem_center_iff, mem_center_iff
-/
theorem mem_center_iff {a : A} : a in center R A ↔ forall b : A, b * a = a * b :=
  Subsemigroup.mem_center_iff

/--
theorem `center_prod` / 定理 `center_prod`

English:
theorem center_prod
  given: [IsScalarTower R B B] [SMulCommClass R B B]
  proof: SetLike.coe_injective Set.center_prod

中文:
定理 center_prod
  条件: [标量塔 R B B] [标量交换类 R B B]
  证明: SetLike.coe_injective Set.center_prod
-/
protected theorem center_prod [IsScalarTower R B B] [SMulCommClass R B B] :
    center R (A × B) = prod (center R A) (center R B) :=
  SetLike.coe_injective Set.center_prod

end Center

section Centralizer

variable (R)
variable [IsScalarTower R A A] [SMulCommClass R A A]

/--
Definition of `centralizer` / `centralizer` 的定义

English:
definition centralizer
  signature: (s : Set A)
  body: { NonUnitalSubalgebra.centralizer R (s union star s) with
    star_mem' := Set.star_mem_centralizer }

@[simp, norm_cast]

中文:
定义 centralizer
  签名: (s : 集合 A)
  定义体: { NonUnitalSubalgebra.centralizer R (s union star s) with
    star_mem' := Set.star_mem_centralizer }

@[simp, norm_cast]

Depends on / 依赖: NonUnitalSubalgebra, NonUnitalSubalgebra.centralizer, Set.star_mem_centralizer, centralizer, star_mem, star_mem_centralizer
-/
def centralizer (s : Set A) : NonUnitalStarSubalgebra R A :=
  { NonUnitalSubalgebra.centralizer R (s union star s) with
    star_mem' := Set.star_mem_centralizer }

@[simp, norm_cast]
/--
theorem `coe_centralizer` / 定理 `coe_centralizer`

English:
theorem coe_centralizer
  given: (s : Set A)
  statement: (centralizer R s : Set A) = (s union star s).centralizer
  proof: rfl

中文:
定理 coe_centralizer
  条件: (s : 集合 A)
  结论: (centralizer R s : 集合 A) = (s union star s).centralizer
  证明: rfl
-/
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = (s union star s).centralizer :=
  rfl

/--
theorem `mem_centralizer_iff` / 定理 `mem_centralizer_iff`

English:
theorem mem_centralizer_iff
  given: {s : Set A} {z : A}
  proof: by
  change (forall g in s union star s, g * z = z * g) ↔ forall g in s, g * z = z * g ∧ star g * z = z * star g
  simp only [Set.mem_union, or_imp, forall_and, and_congr_right_iff]
  exact fun _ =>
    ⟨fun hz a ha => hz _ (Set.star_mem_star.mpr ha), fun hz a ha => star_star a ▸ hz _ ha⟩

中文:
定理 mem_centralizer_iff
  条件: {s : 集合 A} {z : A}
  证明: by
  change (forall g in s union star s, g * z = z * g) ↔ forall g in s, g * z = z * g ∧ star g * z = z * star g
  simp only [Set.mem_union, or_imp, forall_and, and_congr_right_iff]
  exact fun _ =>
    ⟨fun hz a ha => hz _ (Set.star_mem_star.mpr ha), fun hz a ha => star_star a ▸ hz _ ha⟩

Depends on / 依赖: Set.mem_union, Set.star_mem_star.mpr, and_congr_right_iff, forall_and, mem_union, or_imp, star_mem_star, star_star
-/
theorem mem_centralizer_iff {s : Set A} {z : A} :
    z in centralizer R s ↔ forall g in s, g * z = z * g ∧ star g * z = z * star g := by
  change (forall g in s union star s, g * z = z * g) ↔ forall g in s, g * z = z * g ∧ star g * z = z * star g
  simp only [Set.mem_union, or_imp, forall_and, and_congr_right_iff]
  exact fun _ =>
    ⟨fun hz a ha => hz _ (Set.star_mem_star.mpr ha), fun hz a ha => star_star a ▸ hz _ ha⟩

/--
theorem `centralizer_le` / 定理 `centralizer_le`

English:
theorem centralizer_le
  given: (s t : Set A) (h : s subseteq t)
  statement: centralizer R t <= centralizer R s
  proof: Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)

@[simp]

中文:
定理 centralizer_le
  条件: (s t : 集合 A) (h : s subseteq t)
  结论: centralizer R t <= centralizer R s
  证明: Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)

@[simp]

Depends on / 依赖: Set.centralizer_subset, Set.preimage_mono, Set.union_subset_union, centralizer_subset, preimage_mono, union_subset_union
-/
theorem centralizer_le (s t : Set A) (h : s subseteq t) : centralizer R t <= centralizer R s :=
  Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)

@[simp]
/--
theorem `centralizer_univ` / 定理 `centralizer_univ`

English:
theorem centralizer_univ
  statement: centralizer R Set.univ = center R A
  proof: SetLike.ext' by rw [coe_centralizer, Set.univ_union, coe_center, Set.centralizer_univ]

中文:
定理 centralizer_univ
  结论: centralizer R 集合.univ = center R A
  证明: SetLike.ext' by rw [coe_centralizer, Set.univ_union, coe_center, Set.centralizer_univ]

Depends on / 依赖: Set.centralizer_univ, Set.univ_union, SetLike, SetLike.ext, centralizer_univ, coe_center, coe_centralizer, univ_union
-/
theorem centralizer_univ : centralizer R Set.univ = center R A :=
SetLike.ext' by rw [coe_centralizer, Set.univ_union, coe_center, Set.centralizer_univ]

/--
theorem `centralizer_toNonUnitalSubalgebra` / 定理 `centralizer_toNonUnitalSubalgebra`

English:
theorem centralizer_toNonUnitalSubalgebra
  given: (s : Set A)
  proof: rfl

中文:
定理 centralizer_toNonUnitalSubalgebra
  条件: (s : 集合 A)
  证明: rfl
-/
theorem centralizer_toNonUnitalSubalgebra (s : Set A) :
    (centralizer R s).toNonUnitalSubalgebra = NonUnitalSubalgebra.centralizer R (s union star s) :=
  rfl

/--
theorem `coe_centralizer_centralizer` / 定理 `coe_centralizer_centralizer`

English:
theorem coe_centralizer_centralizer
  given: (s : Set A)
  proof: by
  rw [coe_centralizer]; rw [StarMemClass.star_coe_eq]; rw [Set.union_self]; rw [coe_centralizer]

中文:
定理 coe_centralizer_centralizer
  条件: (s : 集合 A)
  证明: by
  rw [coe_centralizer]; rw [StarMemClass.star_coe_eq]; rw [Set.union_self]; rw [coe_centralizer]

Depends on / 依赖: Set.union_self, StarMemClass, StarMemClass.star_coe_eq, coe_centralizer, star_coe_eq, union_self
-/
theorem coe_centralizer_centralizer (s : Set A) :
    (centralizer R (centralizer R s : Set A)) = (s union star s).centralizer.centralizer := by
  rw [coe_centralizer]; rw [StarMemClass.star_coe_eq]; rw [Set.union_self]; rw [coe_centralizer]

end Centralizer

end NonUnitalStarSubalgebra

namespace NonUnitalStarAlgebra

open NonUnitalStarSubalgebra

variable [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

variable (R) in
/--
lemma `adjoin_le_centralizer_centralizer` / 引理 `adjoin_le_centralizer_centralizer`

English:
lemma adjoin_le_centralizer_centralizer
  given: (s : Set A)
  proof: by
  rw [← toNonUnitalSubalgebra_le_iff]; rw [centralizer_toNonUnitalSubalgebra]; rw [adjoin_toNonUnitalSubalgebra]
  convert! NonUnitalAlgebra.adjoin_le_centralizer_centralizer R (s union star s)
  rw [StarMemClass.star_coe_eq]
  simp

中文:
引理 adjoin_le_centralizer_centralizer
  条件: (s : 集合 A)
  证明: by
  rw [← toNonUnitalSubalgebra_le_iff]; rw [centralizer_toNonUnitalSubalgebra]; rw [adjoin_toNonUnitalSubalgebra]
  convert! NonUnitalAlgebra.adjoin_le_centralizer_centralizer R (s union star s)
  rw [StarMemClass.star_coe_eq]
  simp

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.adjoin_le_centralizer_centralizer, StarMemClass, StarMemClass.star_coe_eq, adjoin_le_centralizer_centralizer, adjoin_toNonUnitalSubalgebra, centralizer_toNonUnitalSubalgebra, convert, star_coe_eq, toNonUnitalSubalgebra_le_iff
-/
lemma adjoin_le_centralizer_centralizer (s : Set A) :
    adjoin R s <= centralizer R (centralizer R s) := by
  rw [← toNonUnitalSubalgebra_le_iff]; rw [centralizer_toNonUnitalSubalgebra]; rw [adjoin_toNonUnitalSubalgebra]
  convert! NonUnitalAlgebra.adjoin_le_centralizer_centralizer R (s union star s)
  rw [StarMemClass.star_coe_eq]
  simp

/--
lemma `commute_of_mem_adjoin_of_forall_mem_commute` / 引理 `commute_of_mem_adjoin_of_forall_mem_commute`

English:
lemma commute_of_mem_adjoin_of_forall_mem_commute
  statement: {a b : A} {s : Set A}
  proof: NonUnitalAlgebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun b hb =>
    hb.elim (h b) (by simpa using h_star (star b))

中文:
引理 commute_of_mem_adjoin_of_对任意_mem_commute
  结论: {a b : A} {s : 集合 A}
  证明: NonUnitalAlgebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun b hb =>
    hb.elim (h b) (by simpa using h_star (star b))

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.commute_of_mem_adjoin_of_forall_mem_commute, commute_of_mem_adjoin_of_forall_mem_commute, h_star, hb.elim
-/
lemma commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A}
    (hb : b in adjoin R s) (h : forall b in s, Commute a b) (h_star : forall b in s, Commute a (star b)) :
    Commute a b :=
  NonUnitalAlgebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun b hb =>
    hb.elim (h b) (by simpa using h_star (star b))

/--
lemma `commute_of_mem_adjoin_singleton_of_commute` / 引理 `commute_of_mem_adjoin_singleton_of_commute`

English:
lemma commute_of_mem_adjoin_singleton_of_commute
  statement: {a b c : A}
  proof: commute_of_mem_adjoin_of_forall_mem_commute hc (by simpa) (by simpa)

中文:
引理 commute_of_mem_adjoin_singleton_of_commute
  结论: {a b c : A}
  证明: commute_of_mem_adjoin_of_forall_mem_commute hc (by simpa) (by simpa)

Depends on / 依赖: commute_of_mem_adjoin_of_forall_mem_commute
-/
lemma commute_of_mem_adjoin_singleton_of_commute {a b c : A}
    (hc : c in adjoin R {b}) (h : Commute a b) (h_star : Commute a (star b)) :
    Commute a c :=
  commute_of_mem_adjoin_of_forall_mem_commute hc (by simpa) (by simpa)

/--
lemma `commute_of_mem_adjoin_self` / 引理 `commute_of_mem_adjoin_self`

English:
lemma commute_of_mem_adjoin_self
  given: {a b : A} [IsStarNormal a] (hb : b in adjoin R {a})
  proof: commute_of_mem_adjoin_singleton_of_commute hb rfl (isStarNormal_iff a |>.mp inferInstance).symm

中文:
引理 commute_of_mem_adjoin_self
  条件: {a b : A} [是StarNormal a] (hb : b in adjoin R {a})
  证明: commute_of_mem_adjoin_singleton_of_commute hb rfl (isStarNormal_iff a |>.mp inferInstance).symm

Depends on / 依赖: commute_of_mem_adjoin_singleton_of_commute, isStarNormal_iff
-/
lemma commute_of_mem_adjoin_self {a b : A} [IsStarNormal a] (hb : b in adjoin R {a}) :
    Commute a b :=
  commute_of_mem_adjoin_singleton_of_commute hb rfl (isStarNormal_iff a |>.mp inferInstance).symm

variable (R) in
/--
theorem `isMulCommutative_adjoin` / 定理 `isMulCommutative_adjoin`

English:
theorem isMulCommutative_adjoin
  statement: {s : Set A} (hcomm : forall x in s, forall y in s, x * y = y * x)
  proof: by
  have := adjoin_le_centralizer_centralizer R s
  refine .of_setLike_mul_comm fun _ h₁ _ h₂ => ?_
  have hcomm : forall a in s union star s, forall b in s union star s, a * b = b * a := fun a ha b hb =>
    Set.union_star_self_comm (fun _ ha _ hb => hcomm _ hb _ ha)
      (fun _ ha _ hb => hcomm_

中文:
定理 isMulCommutative_adjoin
  结论: {s : 集合 A} (hcomm : 对任意 x in s, 对任意 y in s, x * y = y * x)
  证明: by
  have := adjoin_le_centralizer_centralizer R s
  refine .of_setLike_mul_comm fun _ h₁ _ h₂ => ?_
  have hcomm : forall a in s union star s, forall b in s union star s, a * b = b * a := fun a ha b hb =>
    Set.union_star_self_comm (fun _ ha _ hb => hcomm _ hb _ ha)
      (fun _ ha _ hb => hcomm_

Depends on / 依赖: Set.centralizer_centralizer_comm_of_comm, Set.union_star_self_comm, SetLike, SetLike.mem_coe, adjoin_le_centralizer_centralizer, centralizer_centralizer_comm_of_comm, coe_centralizer_centralizer, hcomm_star, mem_coe, of_setLike_mul_comm, union_star_self_comm
-/
theorem isMulCommutative_adjoin {s : Set A} (hcomm : forall x in s, forall y in s, x * y = y * x)
    (hcomm_star : forall a in s, forall b in s, a * star b = star b * a) :
    IsMulCommutative (adjoin R s) := by
  have := adjoin_le_centralizer_centralizer R s
  refine .of_setLike_mul_comm fun _ h₁ _ h₂ => ?_
  have hcomm : forall a in s union star s, forall b in s union star s, a * b = b * a := fun a ha b hb =>
    Set.union_star_self_comm (fun _ ha _ hb => hcomm _ hb _ ha)
      (fun _ ha _ hb => hcomm_star _ hb _ ha) b hb a ha
  apply this at h₁
  apply this at h₂
  rw [← SetLike.mem_coe]; rw [coe_centralizer_centralizer] at h₁ h₂
  exact Set.centralizer_centralizer_comm_of_comm hcomm _ h₁ _ h₂

variable (R) in
/--
Instance `isMulCommutative_adjoin_singleton` / 实例 `isMulCommutative_adjoin_singleton`

English:
instance isMulCommutative_adjoin_singleton
  signature: (a : A) [IsStarNormal a]
  body: isMulCommutative_adjoin R (by simp) (by grind)

中文:
实例 isMulCommutative_adjoin_singleton
  签名: (a : A) [是StarNormal a]
  定义体: isMulCommutative_adjoin R (by simp) (by grind)

Depends on / 依赖: isMulCommutative_adjoin
-/
instance isMulCommutative_adjoin_singleton (a : A) [IsStarNormal a] :
    IsMulCommutative (adjoin R ({a} : Set A)) :=
  isMulCommutative_adjoin R (by simp) (by grind)

open scoped IsMulCommutative in
variable (R) in
/-- If all elements of `s : Set A` commute pairwise and with elements of `star s`, then `adjoin R s`
is a non-unital commutative semiring.

See note [reducible non-instances]. -/
@[deprecated isMulCommutative_adjoin (since := "2026-03-11")]
/--
Definition of `adjoinNonUnitalCommSemiringOfComm` / `adjoinNonUnitalCommSemiringOfComm` 的定义

English:
abbreviation adjoinNonUnitalCommSemiringOfComm
  signature: {s : Set A} (hcomm : forall a in s, forall b in s, a * b = b * a)
  body: have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance

中文:
缩写 adjoinNonUnitalCommSemiringOfComm
  签名: {s : 集合 A} (hcomm : 对任意 a in s, 对任意 b in s, a * b = b * a)
  定义体: have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance

Depends on / 依赖: hcomm_star, isMulCommutative_adjoin
-/
abbrev adjoinNonUnitalCommSemiringOfComm {s : Set A} (hcomm : forall a in s, forall b in s, a * b = b * a)
    (hcomm_star : forall a in s, forall b in s, a * star b = star b * a) :
    NonUnitalCommSemiring (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance

/--
Instance `instIsMulCommutative_adjoin` / 实例 `instIsMulCommutative_adjoin`

English:
instance instIsMulCommutative_adjoin
  signature: {S : Type*} [SetLike S A] [MulMemClass S A] [StarMemClass S A]
  body: isMulCommutative_adjoin R
    (fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂)
    (fun _ h₁ _ h₂ => setLike_mul_comm h₁ (star_mem h₂))

中文:
实例 instIsMulCommutative_adjoin
  签名: {S : 类型} [集合状 S A] [MulMem类 S A] [StarMem类 S A]
  定义体: isMulCommutative_adjoin R
    (fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂)
    (fun _ h₁ _ h₂ => setLike_mul_comm h₁ (star_mem h₂))

Depends on / 依赖: isMulCommutative_adjoin, setLike_mul_comm, star_mem
-/
instance instIsMulCommutative_adjoin {S : Type*} [SetLike S A] [MulMemClass S A] [StarMemClass S A]
    (s : S) [IsMulCommutative s] : IsMulCommutative (adjoin R (s : Set A)) :=
  isMulCommutative_adjoin R
    (fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂)
    (fun _ h₁ _ h₂ => setLike_mul_comm h₁ (star_mem h₂))

open scoped IsMulCommutative in
/-- If all elements of `s : Set A` commute pairwise and with elements of `star s`, then `adjoin R s`
is a non-unital commutative ring.

See note [reducible non-instances]. -/
@[deprecated isMulCommutative_adjoin (since := "2026-03-11")]
/--
Definition of `adjoinNonUnitalCommRingOfComm` / `adjoinNonUnitalCommRingOfComm` 的定义

English:
abbreviation adjoinNonUnitalCommRingOfComm
  signature: (R : Type*) {A : Type*} [CommRing R] [StarRing R]
  body: have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance

中文:
缩写 adjoinNonUnitalCommRingOfComm
  签名: (R : 类型) {A : 类型} [交换环 R] [对合环 R]
  定义体: have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance

Depends on / 依赖: hcomm_star, isMulCommutative_adjoin
-/
abbrev adjoinNonUnitalCommRingOfComm (R : Type*) {A : Type*} [CommRing R] [StarRing R]
    [NonUnitalRing A] [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [StarModule R A] {s : Set A} (hcomm : forall a in s, forall b in s, a * b = b * a)
    (hcomm_star : forall a in s, forall b in s, a * star b = star b * a) : NonUnitalCommRing (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance

/--
Instance `isMulCommutative_toNonUnitalSubalgebra` / 实例 `isMulCommutative_toNonUnitalSubalgebra`

English:
instance isMulCommutative_toNonUnitalSubalgebra
  signature: (S : NonUnitalStarSubalgebra R A)
  body: ‹IsMulCommutative S›

中文:
实例 isMulCommutative_toNonUnitalSubalgebra
  签名: (S : 非幺对合子代数 R A)
  定义体: ‹IsMulCommutative S›

Depends on / 依赖: IsMulCommutative
-/
instance isMulCommutative_toNonUnitalSubalgebra (S : NonUnitalStarSubalgebra R A)
    [IsMulCommutative S] : IsMulCommutative S.toNonUnitalSubalgebra :=
  ‹IsMulCommutative S›

end NonUnitalStarAlgebra
