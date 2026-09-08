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

/-- If a type carries an involutive star, then any star-closed subset does too. -/
/-
**StarMemClass.instInvolutiveStar** 是 Mathlib 中的一个实例，位于命名空间 `StarMemClass`。
形式化陈述：instInvolutiveStar {S R : Type*} [InvolutiveStar R] [SetLike S R] [StarMem
Class S R] (s : S) : InvolutiveStar s where star_involutive r
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a type carries an involutive star, then any star-closed subset does too.
-/
instance instInvolutiveStar {S R : Type*} [InvolutiveStar R] [SetLike S R] [StarMemClass S R]
    (s : S) : InvolutiveStar s where
  star_involutive r := Subtype.ext <| star_star (r : R)

/-- In a star magma (i.e., a multiplication with an antimultiplicative involutive star
operation), any star-closed subset which is also closed under multiplication is itself a star
magma. -/
/-
**StarMemClass.instStarMul** 是 Mathlib 中的一个实例，位于命名空间 `StarMemClass`。
形式化陈述：instStarMul {S R : Type*} [Mul R] [StarMul R] [SetLike S R] [MulMemClass S
 R] [StarMemClass S R] (s : S) : StarMul s where star_mul _ _
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a star magma (i.e., a multiplication with an antimultiplicative involutive st
ar
operation), any star-closed subset which is also closed under multiplication is 
itself a star
magma.
-/
instance instStarMul {S R : Type*} [Mul R] [StarMul R] [SetLike S R]
    [MulMemClass S R] [StarMemClass S R] (s : S) : StarMul s where
  star_mul _ _ := Subtype.ext <| star_mul _ _

/-- In a `StarAddMonoid` (i.e., an additive monoid with an additive involutive star operation), any
star-closed subset which is also closed under addition and contains zero is itself a
`StarAddMonoid`. -/
/-
**StarMemClass.instStarAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `StarMemClass`。
形式化陈述：instStarAddMonoid {S R : Type*} [AddMonoid R] [StarAddMonoid R] [SetLike S
 R] [AddSubmonoidClass S R] [StarMemClass S R] (s : S) : StarAddMonoid s where s
tar_add _ _
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a `StarAddMonoid` (i.e., an additive monoid with an additive involutive star 
operation), any
star-closed subset which is also closed under addition and contains zero is itse
lf a
`StarAddMonoid`.
-/
instance instStarAddMonoid {S R : Type*} [AddMonoid R] [StarAddMonoid R] [SetLike S R]
    [AddSubmonoidClass S R] [StarMemClass S R] (s : S) : StarAddMonoid s where
  star_add _ _ := Subtype.ext <| star_add _ _

/-- In a star ring (i.e., a non-unital, non-associative, semiring with an additive,
antimultiplicative, involutive star operation), a star-closed non-unital subsemiring is itself a
star ring. -/
/-
**StarMemClass.instStarRing** 是 Mathlib 中的一个实例，位于命名空间 `StarMemClass`。
形式化陈述：instStarRing {S R : Type*} [NonUnitalNonAssocSemiring R] [StarRing R] [Set
Like S R] [NonUnitalSubsemiringClass S R] [StarMemClass S R] (s : S) : StarRing 
s
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…

--- 原说明 ---
In a star ring (i.e., a non-unital, non-associative, semiring with an additive,
antimultiplicative, involutive star operation), a star-closed non-unital subsemi
ring is itself a
star ring.
-/
instance instStarRing {S R : Type*} [NonUnitalNonAssocSemiring R] [StarRing R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] [StarMemClass S R] (s : S) : StarRing s :=
  { StarMemClass.instStarMul s, StarMemClass.instStarAddMonoid s with }

/-- In a star `R`-module (i.e., `star (r • m) = (star r) • m`) any star-closed subset which is also
closed under the scalar action by `R` is itself a star `R`-module. -/
/-
**StarMemClass.instStarModule** 是 Mathlib 中的一个实例，位于命名空间 `StarMemClass`。
形式化陈述：instStarModule {S : Type*} (R : Type*) {M : Type*} [Star R] [Star M] [SMul
 R M] [StarModule R M] [SetLike S M] [SMulMemClass S R M] [StarMemClass S M] (s 
: S) : StarModule R s where star_smul _ _
参数：R : Type*；s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …

--- 原说明 ---
In a star `R`-module (i.e., `star (r • m) = (star r) • m`) any star-closed subse
t which is also
closed under the scalar action by `R` is itself a star `R`-module.
-/
instance instStarModule {S : Type*} (R : Type*) {M : Type*} [Star R] [Star M] [SMul R M]
    [StarModule R M] [SetLike S M] [SMulMemClass S R M] [StarMemClass S M] (s : S) :
    StarModule R s where
  star_smul _ _ := Subtype.ext <| star_smul _ _

end StarMemClass

universe u u' v v' w w' w''

variable {F : Type v'} {R' : Type u'} {R : Type u}
variable {A : Type v} {B : Type w} {C : Type w'}

namespace NonUnitalStarSubalgebraClass

variable [CommSemiring R] [NonUnitalNonAssocSemiring A]
variable [Star A] [Module R A]
variable {S : Type w''} [SetLike S A] [NonUnitalSubsemiringClass S A]
variable [hSR : SMulMemClass S R A] [StarMemClass S A] (s : S)

/-- Embedding of a non-unital star subalgebra into the non-unital star algebra. -/
/-
**NonUnitalStarSubalgebraClass.subtype** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarS
ubalgebraClass`。
形式化陈述：subtype (s : S) : s ->⋆ₙₐ[R] A
参数：s : S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…

--- 原说明 ---
Embedding of a non-unital star subalgebra into the non-unital star algebra.
-/
def subtype (s : S) : s →⋆ₙₐ[R] A :=
  { NonUnitalSubalgebraClass.subtype s with
    toFun := Subtype.val
    map_star' := fun _ => rfl }

variable {s} in
@[simp]
/-
**NonUnitalStarSubalgebraClass.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `NonUnita
lStarSubalgebraClass`。
形式化陈述：subtype_apply (x : s) : subtype s x = x
参数：x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
-/
lemma subtype_apply (x : s) : subtype s x = x := rfl
/-
**NonUnitalStarSubalgebraClass.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `NonU
nitalStarSubalgebraClass`。
形式化陈述：subtype_injective : Function.Injective (subtype s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective :
    Function.Injective (subtype s) :=
  Subtype.coe_injective

@[simp]
/-
**NonUnitalStarSubalgebraClass.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalS
tarSubalgebraClass`。
形式化陈述：coe_subtype : (subtype s : s -> A) = Subtype.val
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
-/
theorem coe_subtype : (subtype s : s → A) = Subtype.val :=
  rfl

end NonUnitalStarSubalgebraClass

/-- A non-unital star subalgebra is a non-unital subalgebra which is closed under the `star`
operation. -/
/-
**NonUnitalStarSubalgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   (A : Type v) →     [inst : CommSemiring R] → [inst_1 : No
nUnitalNonAssocSemiring A] → [_root_.Module R A] → [Star A] → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital star subalgebra is a non-unital subalgebra which is closed under th
e `star`
operation.
-/
structure NonUnitalStarSubalgebra (R : Type u) (A : Type v) [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A] : Type v
    extends NonUnitalSubalgebra R A where
  /-- The `carrier` of a `NonUnitalStarSubalgebra` is closed under the `star` operation. -/
  star_mem' : ∀ {a : A} (_ha : a ∈ carrier), star a ∈ carrier

/-- Reinterpret a `NonUnitalStarSubalgebra` as a `NonUnitalSubalgebra`. -/
add_decl_doc NonUnitalStarSubalgebra.toNonUnitalSubalgebra

namespace NonUnitalStarSubalgebra

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
variable [NonUnitalNonAssocSemiring C] [Module R C] [Star C]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

/-
**NonUnitalStarSubalgebra.instSetLike** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarSu
balgebra`。
形式化陈述：instSetLike : SetLike (NonUnitalStarSubalgebra R A) A where coe {s}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSetLike : SetLike (NonUnitalStarSubalgebra R A) A where
  coe {s} := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h
/-
**NonUnitalStarSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (NonUnitalStarSubalgebra R A) := .ofSetLike (NonUnitalStarSubalgebra R A) A

/-- The actual `NonUnitalStarSubalgebra` obtained from an element of a type satisfying
`NonUnitalSubsemiringClass`, `SMulMemClass` and `StarMemClass`. -/
@[simps]
/-
**NonUnitalStarSubalgebra.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarSubalg
ebra`。
形式化陈述：ofClass {S R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Mo
dule R A] [Star A] [SetLike S A] [NonUnitalSubsemiringClass S A] [SMulMemClass S
 R A] [StarMemClass S A] (s : S) : NonUnitalStarSubalgebra R A where carrier
参数：s : S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s

--- 原说明 ---
The actual `NonUnitalStarSubalgebra` obtained from an element of a type satisfyi
ng
`NonUnitalSubsemiringClass`, `SMulMemClass` and `StarMemClass`.
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
/-
**NonUnitalStarSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CanLift (Set A) (NonUnitalStarSubalgebra R A) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧
      (∀ (r : R) {x}, x ∈ s → r • x ∈ s) ∧ ∀ {x}, x ∈ s → star x ∈ s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        mul_mem' := h.2.2.1
        smul_mem' := h.2.2.2.1
        star_mem' := h.2.2.2.2 },
      rfl ⟩
/-
**NonUnitalStarSubalgebra.instNonUnitalSubsemiringClass** 是 Mathlib 中的一个实例，位于命名空
间 `NonUnitalStarSubalgebra`。
形式化陈述：instNonUnitalSubsemiringClass : NonUnitalSubsemiringClass (NonUnitalStarSu
balgebra R A) A where add_mem {s}
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
    NonUnitalSubsemiringClass (NonUnitalStarSubalgebra R A) A where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'
/-
**NonUnitalStarSubalgebra.instSMulMemClass** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalS
tarSubalgebra`。
形式化陈述：instSMulMemClass : SMulMemClass (NonUnitalStarSubalgebra R A) R A where sm
ul_mem {s}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.smul_mem'`：∀ {R : Type u} {A : Type v} [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R A]  
 (self : NonUnitalS…
-/
instance instSMulMemClass : SMulMemClass (NonUnitalStarSubalgebra R A) R A where
  smul_mem {s} := s.smul_mem'
/-
**NonUnitalStarSubalgebra.instStarMemClass** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalS
tarSubalgebra`。
形式化陈述：instStarMemClass : StarMemClass (NonUnitalStarSubalgebra R A) A where star
_mem {s}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.star_mem'`：∀ {R : Type u} {A : Type v} [inst : C
ommSemiring R] [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R 
A]   [inst_3 : Star A] …
-/
instance instStarMemClass : StarMemClass (NonUnitalStarSubalgebra R A) A where
  star_mem {s} := s.star_mem'
/-
**NonUnitalStarSubalgebra.instNonUnitalSubringClass** 是 Mathlib 中的一个实例，位于命名空间 `N
onUnitalStarSubalgebra`。
形式化陈述：instNonUnitalSubringClass {R : Type u} {A : Type v} [CommRing R] [NonUnita
lNonAssocRing A] [Module R A] [Star A] : NonUnitalSubringClass (NonUnitalStarSub
algebra R A) A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
-/
instance instNonUnitalSubringClass {R : Type u} {A : Type v} [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [Star A] : NonUnitalSubringClass (NonUnitalStarSubalgebra R A) A :=
  { NonUnitalStarSubalgebra.instNonUnitalSubsemiringClass with
    neg_mem := fun _S {x} hx => neg_one_smul R x ▸ SMulMemClass.smul_mem _ hx }
/-
**NonUnitalStarSubalgebra.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSu
balgebra`。
形式化陈述：mem_carrier {s : NonUnitalStarSubalgebra R A} {x : A} : x in s.carrier ↔ x
 in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : NonUnitalStarSubalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[ext]
/-
**NonUnitalStarSubalgebra.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubalgebra
`。
形式化陈述：ext {S T : NonUnitalStarSubalgebra R A} (h : forall x : A, x in S ↔ x in T
) : S = T
参数：h : forall x : A, x in S ↔ x in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext {S T : NonUnitalStarSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
/-
**NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `N
onUnitalStarSubalgebra`。
形式化陈述：mem_toNonUnitalSubalgebra {S : NonUnitalStarSubalgebra R A} {x} : x in S.t
oNonUnitalSubalgebra ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toNonUnitalSubalgebra {S : NonUnitalStarSubalgebra R A} {x} :
    x ∈ S.toNonUnitalSubalgebra ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**NonUnitalStarSubalgebra.coe_toNonUnitalSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `N
onUnitalStarSubalgebra`。
形式化陈述：coe_toNonUnitalSubalgebra (S : NonUnitalStarSubalgebra R A) : (↑S.toNonUni
talSubalgebra : Set A) = S
参数：S : NonUnitalStarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNonUnitalSubalgebra (S : NonUnitalStarSubalgebra R A) :
    (↑S.toNonUnitalSubalgebra : Set A) = S :=
  rfl
/-
**NonUnitalStarSubalgebra.toNonUnitalSubalgebra_injective** 是 Mathlib 中的一个定理，位于命
名空间 `NonUnitalStarSubalgebra`。
形式化陈述：toNonUnitalSubalgebra_injective : Function.Injective (toNonUnitalSubalgebr
a : NonUnitalStarSubalgebra R A -> NonUnitalSubalgebra R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.ext`：ext {S T : NonUnitalStarSubalgebra R A} (h 
: forall x : A, x in S ↔ x in T) : S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra`：mem_toNonUnitalSubalg
ebra {S : NonUnitalStarSubalgebra R A} {x} : x in S.toNonUnitalSubalgebra ↔ x in
 S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toNonUnitalSubalgebra_injective :
    Function.Injective
      (toNonUnitalSubalgebra : NonUnitalStarSubalgebra R A → NonUnitalSubalgebra R A) :=
  fun S T h =>
  ext fun x => by rw [← mem_toNonUnitalSubalgebra, ← mem_toNonUnitalSubalgebra, h]
/-
**NonUnitalStarSubalgebra.toNonUnitalSubalgebra_inj** 是 Mathlib 中的一个定理，位于命名空间 `N
onUnitalStarSubalgebra`。
形式化陈述：toNonUnitalSubalgebra_inj {S U : NonUnitalStarSubalgebra R A} : S.toNonUni
talSubalgebra = U.toNonUnitalSubalgebra ↔ S = U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `NonUnitalStarSubalgebra.toNonUnitalSubalgebra_injective`：toNonUnitalSuba
lgebra_injective : Function.Injective (toNonUnitalSubalgebra : NonUnitalStarSuba
lgebra R A -> NonUnitalSubalgebra R A)
-/
theorem toNonUnitalSubalgebra_inj {S U : NonUnitalStarSubalgebra R A} :
    S.toNonUnitalSubalgebra = U.toNonUnitalSubalgebra ↔ S = U :=
  toNonUnitalSubalgebra_injective.eq_iff
/-
**NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff** 是 Mathlib 中的一个定理，位于命名空间
 `NonUnitalStarSubalgebra`。
形式化陈述：toNonUnitalSubalgebra_le_iff {S₁ S₂ : NonUnitalStarSubalgebra R A} : S₁.to
NonUnitalSubalgebra <= S₂.toNonUnitalSubalgebra ↔ S₁ <= S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toNonUnitalSubalgebra_le_iff {S₁ S₂ : NonUnitalStarSubalgebra R A} :
    S₁.toNonUnitalSubalgebra ≤ S₂.toNonUnitalSubalgebra ↔ S₁ ≤ S₂ :=
  Iff.rfl

/-- Copy of a non-unital star subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
/-
**NonUnitalStarSubalgebra.copy** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarSubalgebr
a`。
形式化陈述：{R : Type u} →   {A : Type v} →     [inst : CommSemiring R] →       [inst_
1 : NonUnitalNonAssocSemiring A] →         [inst_2 : _root_.Module R A] →       
    [inst_3 : Star A] → (S : NonUnitalStarSubalgebra R A) → (s : Set A) → s = ↑S
 → NonUnitalStarSubalgebra R A
参数：S : NonUnitalStarSubalgebra R A；s : Set A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a non-unital star subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities.
-/
protected def copy (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    NonUnitalStarSubalgebra R A :=
  { S.toNonUnitalSubalgebra.copy s hs with
    star_mem' := @fun x (hx : x ∈ s) => by
      change star x ∈ s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp, norm_cast]
/-
**NonUnitalStarSubalgebra.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubal
gebra`。
形式化陈述：coe_copy (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S) : (S.
copy s hs : Set A) = s
参数：S : NonUnitalStarSubalgebra R A；s : Set A；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    (S.copy s hs : Set A) = s :=
  rfl
/-
**NonUnitalStarSubalgebra.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubalg
ebra`。
形式化陈述：copy_eq (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.co
py s hs = S
参数：S : NonUnitalStarSubalgebra R A；s : Set A；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (S : NonUnitalStarSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S : NonUnitalStarSubalgebra R A)

/-- A non-unital star subalgebra over a ring is also a `Subring`. -/
@[reducible]
/-
**NonUnitalStarSubalgebra.toNonUnitalSubring** 是 Mathlib 中的一个定义，位于命名空间 `NonUnita
lStarSubalgebra`。
形式化陈述：toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A
] [Module R A] [Star A] (S : NonUnitalStarSubalgebra R A) : NonUnitalSubring A w
here toNonUnitalSubsemiring
参数：S : NonUnitalStarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital star subalgebra over a ring is also a `Subring`.
-/
def toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : NonUnitalSubring A where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  neg_mem' := neg_mem (s := S)
/-
**NonUnitalStarSubalgebra.mem_toNonUnitalSubring** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalStarSubalgebra`。
形式化陈述：mem_toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRi
ng A] [Module R A] [Star A] {S : NonUnitalStarSubalgebra R A} {x} : x in S.toNon
UnitalSubring ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] {S : NonUnitalStarSubalgebra R A} {x} : x ∈ S.toNonUnitalSubring ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**NonUnitalStarSubalgebra.coe_toNonUnitalSubring** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalStarSubalgebra`。
形式化陈述：coe_toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRi
ng A] [Module R A] [Star A] (S : NonUnitalStarSubalgebra R A) : (↑S.toNonUnitalS
ubring : Set A) = S
参数：S : NonUnitalStarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNonUnitalSubring {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : (↑S.toNonUnitalSubring : Set A) = S :=
  rfl
/-
**NonUnitalStarSubalgebra.toNonUnitalSubring_injective** 是 Mathlib 中的一个定理，位于命名空间
 `NonUnitalStarSubalgebra`。
形式化陈述：toNonUnitalSubring_injective {R : Type u} {A : Type v} [CommRing R] [NonUn
italRing A] [Module R A] [Star A] : Function.Injective (toNonUnitalSubring : Non
UnitalStarSubalgebra R A -> NonUnitalSubring A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.ext`：ext {S T : NonUnitalStarSubalgebra R A} (h 
: forall x : A, x in S ↔ x in T) : S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalStarSubalgebra.mem_toNonUnitalSubring`：mem_toNonUnitalSubring {
R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A] [Star A] {S
 : NonUnitalStarSubalgebra R A} {x} …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toNonUnitalSubring_injective {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A]
    [Module R A] [Star A] :
    Function.Injective (toNonUnitalSubring : NonUnitalStarSubalgebra R A → NonUnitalSubring A) :=
  fun S T h => ext fun x => by rw [← mem_toNonUnitalSubring, ← mem_toNonUnitalSubring, h]
/-
**NonUnitalStarSubalgebra.toNonUnitalSubring_inj** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalStarSubalgebra`。
形式化陈述：toNonUnitalSubring_inj {R : Type u} {A : Type v} [CommRing R] [NonUnitalRi
ng A] [Module R A] [Star A] {S U : NonUnitalStarSubalgebra R A} : S.toNonUnitalS
ubring = U.toNonUnitalSubring ↔ S = U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `NonUnitalStarSubalgebra.toNonUnitalSubring_injective`：toNonUnitalSubring
_injective {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
 [Star A] : Function.Injective (toNonUnita…
-/
theorem toNonUnitalSubring_inj {R : Type u} {A : Type v} [CommRing R] [NonUnitalRing A] [Module R A]
    [Star A] {S U : NonUnitalStarSubalgebra R A} :
    S.toNonUnitalSubring = U.toNonUnitalSubring ↔ S = U :=
  toNonUnitalSubring_injective.eq_iff
/-
**NonUnitalStarSubalgebra.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStar
Subalgebra`。
形式化陈述：instInhabited : Inhabited S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited S :=
  ⟨(0 : S.toNonUnitalSubalgebra)⟩

section

/-! `NonUnitalStarSubalgebra`s inherit structure from their `NonUnitalSubsemiringClass` and
`NonUnitalSubringClass` instances. -/

/-
**NonUnitalStarSubalgebra.toNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `NonUnit
alStarSubalgebra`。
形式化陈述：toNonUnitalSemiring {R A} [CommSemiring R] [NonUnitalSemiring A] [Module R
 A] [Star A] (S : NonUnitalStarSubalgebra R A) : NonUnitalSemiring S
参数：S : NonUnitalStarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonUnitalStarSubalgebra`s inherit structure from their `NonUnitalSubsemiringCla
ss` and
`NonUnitalSubringClass` instances.
-/
instance toNonUnitalSemiring {R A} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) : NonUnitalSemiring S :=
  inferInstance
/-
**NonUnitalStarSubalgebra.toNonUnitalCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Non
UnitalStarSubalgebra`。
形式化陈述：toNonUnitalCommSemiring {R A} [CommSemiring R] [NonUnitalCommSemiring A] [
Module R A] [Star A] (S : NonUnitalStarSubalgebra R A) : NonUnitalCommSemiring S
参数：S : NonUnitalStarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toNonUnitalCommSemiring {R A} [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : NonUnitalCommSemiring S :=
  inferInstance
/-
**NonUnitalStarSubalgebra.toNonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSt
arSubalgebra`。
形式化陈述：toNonUnitalRing {R A} [CommRing R] [NonUnitalRing A] [Module R A] [Star A]
 (S : NonUnitalStarSubalgebra R A) : NonUnitalRing S
参数：S : NonUnitalStarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toNonUnitalRing {R A} [CommRing R] [NonUnitalRing A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) : NonUnitalRing S :=
  inferInstance
/-
**NonUnitalStarSubalgebra.toNonUnitalCommRing** 是 Mathlib 中的一个实例，位于命名空间 `NonUnit
alStarSubalgebra`。
形式化陈述：toNonUnitalCommRing {R A} [CommRing R] [NonUnitalCommRing A] [Module R A] 
[Star A] (S : NonUnitalStarSubalgebra R A) : NonUnitalCommRing S
参数：S : NonUnitalStarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toNonUnitalCommRing {R A} [CommRing R] [NonUnitalCommRing A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) : NonUnitalCommRing S :=
  inferInstance
end

/-- The forgetful map from `NonUnitalStarSubalgebra` to `NonUnitalSubalgebra` as an
`OrderEmbedding` -/
/-
**NonUnitalStarSubalgebra.toNonUnitalSubalgebra'** 是 Mathlib 中的一个定义，位于命名空间 `NonU
nitalStarSubalgebra`。
形式化陈述：toNonUnitalSubalgebra' : NonUnitalStarSubalgebra R A ↪o NonUnitalSubalgebr
a R A where toEmbedding
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful map from `NonUnitalStarSubalgebra` to `NonUnitalSubalgebra` as an
`OrderEmbedding`
-/
def toNonUnitalSubalgebra' : NonUnitalStarSubalgebra R A ↪o NonUnitalSubalgebra R A where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubalgebra
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

section

/-! `NonUnitalStarSubalgebra`s inherit structure from their `Submodule` coercions. -/

/-
**NonUnitalStarSubalgebra.module'** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarSubalg
ebra`。
形式化陈述：module' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : M
odule R' S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonUnitalStarSubalgebra`s inherit structure from their `Submodule` coercions.
-/
instance module' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : Module R' S :=
  SMulMemClass.toModule' _ R' R A S
/-
**NonUnitalStarSubalgebra.instModule** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarSub
algebra`。
形式化陈述：instModule : Module R S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule : Module R S :=
  S.module'
/-
**NonUnitalStarSubalgebra.instIsScalarTower'** 是 Mathlib 中的一个实例，位于命名空间 `NonUnita
lStarSubalgebra`。
形式化陈述：instIsScalarTower' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower 
R' R A] : IsScalarTower R' R S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTower' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    IsScalarTower R' R S :=
  S.toNonUnitalSubalgebra.instIsScalarTower'
/-
**NonUnitalStarSubalgebra.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `NonUnital
StarSubalgebra`。
形式化陈述：instIsScalarTower [IsScalarTower R A A] : IsScalarTower R S S where smul_a
ssoc r x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance instIsScalarTower [IsScalarTower R A A] : IsScalarTower R S S where
  smul_assoc r x y := Subtype.ext <| smul_assoc r (x : A) (y : A)
/-
**NonUnitalStarSubalgebra.instSMulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `NonUnita
lStarSubalgebra`。
形式化陈述：instSMulCommClass' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower 
R' R A] [SMulCommClass R' R A] : SMulCommClass R' R S where smul_comm r' r s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
    [SMulCommClass R' R A] : SMulCommClass R' R S where
  smul_comm r' r s := Subtype.ext <| smul_comm r' r (s : A)
/-
**NonUnitalStarSubalgebra.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `NonUnital
StarSubalgebra`。
形式化陈述：instSMulCommClass [SMulCommClass R A A] : SMulCommClass R S S where smul_c
omm r x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass [SMulCommClass R A A] : SMulCommClass R S S where
  smul_comm r x y := Subtype.ext <| smul_comm r (x : A) (y : A)

end

/-
**NonUnitalStarSubalgebra.instIsTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `NonUnital
StarSubalgebra`。
形式化陈述：instIsTorsionFree [IsTorsionFree R A] : IsTorsionFree R S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Injective.moduleIsTorsionFree`：Function.Injective.moduleIsTorsi
onFree [IsTorsionFree R N] (f : M -> N) (hf : f.Injective) (smul : forall (r : R
) (m : M), f (r • m) = r • f…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance instIsTorsionFree [IsTorsionFree R A] : IsTorsionFree R S :=
  Subtype.coe_injective.moduleIsTorsionFree _ (by simp)
/-
**NonUnitalStarSubalgebra.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubalg
ebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNon
AssocSemiring A] [inst_2 : _root_.Module R A]   [inst_3 : Star A] (S : NonUnital
StarSubalgebra R A) (x y : ↥S), ↑(x + y) = ↑x + ↑y
参数：S : NonUnitalStarSubalgebra R A；x y : ↥S；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y :=
  rfl
/-
**NonUnitalStarSubalgebra.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubalg
ebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNon
AssocSemiring A] [inst_2 : _root_.Module R A]   [inst_3 : Star A] (S : NonUnital
StarSubalgebra R A) (x y : ↥S), ↑(x * y) = ↑x * ↑y
参数：S : NonUnitalStarSubalgebra R A；x y : ↥S；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y :=
  rfl
/-
**NonUnitalStarSubalgebra.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubal
gebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNon
AssocSemiring A] [inst_2 : _root_.Module R A]   [inst_3 : Star A] (S : NonUnital
StarSubalgebra R A), ↑0 = 0
参数：S : NonUnitalStarSubalgebra R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
-/
protected theorem coe_zero : ((0 : S) : A) = 0 :=
  rfl
/-
**NonUnitalStarSubalgebra.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubalg
ebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : NonUnitalNonAsso
cRing A] [inst_2 : _root_.Module R A]   [inst_3 : Star A] {S : NonUnitalStarSuba
lgebra R A} (x : ↥S), ↑(-x) = -↑x
参数：x : ↥S；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
-/
protected theorem coe_neg {R : Type u} {A : Type v} [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [Star A] {S : NonUnitalStarSubalgebra R A} (x : S) : (↑(-x) : A) = -↑x :=
  rfl
/-
**NonUnitalStarSubalgebra.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubalg
ebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : NonUnitalNonAsso
cRing A] [inst_2 : _root_.Module R A]   [inst_3 : Star A] {S : NonUnitalStarSuba
lgebra R A} (x y : ↥S), ↑(x - y) = ↑x - ↑y
参数：x y : ↥S；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [i
nst : SetLike S R] [inst_1 : NonUnitalNonAssocRing R] [h : NonUnitalSubringClass
 S R],   AddSubgroupClass S …
-/
protected theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [Star A] {S : NonUnitalStarSubalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y :=
  rfl

@[simp, norm_cast]
/-
**NonUnitalStarSubalgebra.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubal
gebra`。
形式化陈述：coe_smul [SMul R' R] [SMul R' A] [IsScalarTower R' R A] (r : R') (x : S) :
 ↑(r • x) = r • (x : A)
参数：r : R'；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul [SMul R' R] [SMul R' A] [IsScalarTower R' R A] (r : R') (x : S) :
    ↑(r • x) = r • (x : A) :=
  rfl
/-
**NonUnitalStarSubalgebra.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSu
balgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNon
AssocSemiring A] [inst_2 : _root_.Module R A]   [inst_3 : Star A] (S : NonUnital
StarSubalgebra R A) {x : ↥S}, ↑x = 0 ↔ x = 0
参数：S : NonUnitalStarSubalgebra R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroMemClass.coe_eq_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLi
ke A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] {S' : A} {x : ↥S'},   ↑x = 
0 ↔ x = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
-/
protected theorem coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
  ZeroMemClass.coe_eq_zero

@[simp]
/-
**NonUnitalStarSubalgebra.toNonUnitalSubalgebra_subtype** 是 Mathlib 中的一个定理，位于命名空
间 `NonUnitalStarSubalgebra`。
形式化陈述：toNonUnitalSubalgebra_subtype : NonUnitalSubalgebraClass.subtype S = NonUn
italStarSubalgebraClass.subtype S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
-/
theorem toNonUnitalSubalgebra_subtype :
    NonUnitalSubalgebraClass.subtype S = NonUnitalStarSubalgebraClass.subtype S :=
  rfl

@[simp]
/-
**NonUnitalStarSubalgebra.toSubring_subtype** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
StarSubalgebra`。
形式化陈述：toSubring_subtype {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Mo
dule R A] [Star A] (S : NonUnitalStarSubalgebra R A) : NonUnitalSubringClass.sub
type S = NonUnitalStarSubalgebraClass.subtype S
参数：S : NonUnitalStarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubring_subtype {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) :
    NonUnitalSubringClass.subtype S = NonUnitalStarSubalgebraClass.subtype S :=
  rfl

/-- Transport a non-unital star subalgebra via a non-unital star algebra homomorphism. -/
/-
**NonUnitalStarSubalgebra.map** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarSubalgebra
`。
形式化陈述：map (f : F) (S : NonUnitalStarSubalgebra R A) : NonUnitalStarSubalgebra R 
B where toNonUnitalSubalgebra
参数：f : F；S : NonUnitalStarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a non-unital star subalgebra via a non-unital star algebra homomorphis
m.
-/
def map (f : F) (S : NonUnitalStarSubalgebra R A) : NonUnitalStarSubalgebra R B where
  toNonUnitalSubalgebra := S.toNonUnitalSubalgebra.map (f : A →ₙₐ[R] B)
  star_mem' := by rintro _ ⟨a, ha, rfl⟩; exact ⟨star a, star_mem (s := S) ha, map_star f a⟩

@[gcongr]
/-
**NonUnitalStarSubalgebra.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubal
gebra`。
形式化陈述：map_mono {S₁ S₂ : NonUnitalStarSubalgebra R A} {f : F} : S₁ <= S₂ -> (map 
f S₁ : NonUnitalStarSubalgebra R B) <= map f S₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem map_mono {S₁ S₂ : NonUnitalStarSubalgebra R A} {f : F} :
    S₁ ≤ S₂ → (map f S₁ : NonUnitalStarSubalgebra R B) ≤ map f S₂ :=
  Set.image_mono
/-
**NonUnitalStarSubalgebra.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStar
Subalgebra`。
形式化陈述：map_injective {f : F} (hf : Function.Injective f) : Function.Injective (ma
p f : NonUnitalStarSubalgebra R A -> NonUnitalStarSubalgebra R B)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.ext`：ext {S T : NonUnitalStarSubalgebra R A} (h 
: forall x : A, x in S ↔ x in T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_injective`：image_injective : Injective (image f) ↔ Injective f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem map_injective {f : F} (hf : Function.Injective f) :
    Function.Injective (map f : NonUnitalStarSubalgebra R A → NonUnitalStarSubalgebra R B) :=
  fun _S₁ _S₂ ih =>
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih

@[simp]
/-
**NonUnitalStarSubalgebra.map_id** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubalge
bra`。
形式化陈述：map_id (S : NonUnitalStarSubalgebra R A) : map (NonUnitalStarAlgHom.id R A
) S = S
参数：S : NonUnitalStarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `NonUnitalStarAlgHom.instStarHomClass`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 
: DistribMulAction R A] [i…
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem map_id (S : NonUnitalStarSubalgebra R A) : map (NonUnitalStarAlgHom.id R A) S = S :=
  SetLike.coe_injective <| Set.image_id _
/-
**NonUnitalStarSubalgebra.map_map** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubalg
ebra`。
形式化陈述：map_map (S : NonUnitalStarSubalgebra R A) (g : B ->⋆ₙₐ[R] C) (f : A ->⋆ₙₐ[
R] B) : (S.map f).map g = S.map (g.comp f)
参数：S : NonUnitalStarSubalgebra R A；g : B ->⋆ₙₐ[R] C；f : A ->⋆ₙₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `NonUnitalStarAlgHom.instStarHomClass`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 
: DistribMulAction R A] [i…
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map (S : NonUnitalStarSubalgebra R A) (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

@[simp]
/-
**NonUnitalStarSubalgebra.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubalg
ebra`。
形式化陈述：mem_map {S : NonUnitalStarSubalgebra R A} {f : F} {y : B} : y in map f S ↔
 exists x in S, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.mem_map`：mem_map {S : NonUnitalSubalgebra R A} {f : 
F} {y : B} : y in map f S ↔ exists x in S, f x = y
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
-/
theorem mem_map {S : NonUnitalStarSubalgebra R A} {f : F} {y : B} :
    y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  NonUnitalSubalgebra.mem_map
/-
**NonUnitalStarSubalgebra.map_toNonUnitalSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `N
onUnitalStarSubalgebra`。
形式化陈述：map_toNonUnitalSubalgebra {S : NonUnitalStarSubalgebra R A} {f : F} : (map
 f S : NonUnitalStarSubalgebra R B).toNonUnitalSubalgebra = NonUnitalSubalgebra.
map f S.toNonUnitalSubalgebra
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem map_toNonUnitalSubalgebra {S : NonUnitalStarSubalgebra R A} {f : F} :
    (map f S : NonUnitalStarSubalgebra R B).toNonUnitalSubalgebra =
      NonUnitalSubalgebra.map f S.toNonUnitalSubalgebra :=
  SetLike.coe_injective rfl

@[simp, norm_cast]
/-
**NonUnitalStarSubalgebra.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubalg
ebra`。
形式化陈述：coe_map (S : NonUnitalStarSubalgebra R A) (f : F) : map f S = f '' S
参数：S : NonUnitalStarSubalgebra R A；f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (S : NonUnitalStarSubalgebra R A) (f : F) : map f S = f '' S :=
  rfl

/-- Preimage of a non-unital star subalgebra under a non-unital star algebra homomorphism. -/
/-
**NonUnitalStarSubalgebra.comap** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarSubalgeb
ra`。
形式化陈述：comap (f : F) (S : NonUnitalStarSubalgebra R B) : NonUnitalStarSubalgebra 
R A where toNonUnitalSubalgebra
参数：f : F；S : NonUnitalStarSubalgebra R B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preimage of a non-unital star subalgebra under a non-unital star algebra homomor
phism.
-/
def comap (f : F) (S : NonUnitalStarSubalgebra R B) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := S.toNonUnitalSubalgebra.comap f
  star_mem' := @fun a (ha : f a ∈ S) =>
    show f (star a) ∈ S from (map_star f a).symm ▸ star_mem (s := S) ha
/-
**NonUnitalStarSubalgebra.map_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubalge
bra`。
形式化陈述：map_le {S : NonUnitalStarSubalgebra R A} {f : F} {U : NonUnitalStarSubalge
bra R B} : map f S <= U ↔ S <= comap f U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le {S : NonUnitalStarSubalgebra R A} {f : F} {U : NonUnitalStarSubalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff
/-
**NonUnitalStarSubalgebra.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarS
ubalgebra`。
形式化陈述：gc_map_comap (f : F) : GaloisConnection (map f) (comap f)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.map_le`：map_le {S : NonUnitalStarSubalgebra R A}
 {f : F} {U : NonUnitalStarSubalgebra R B} : map f S <= U ↔ S <= comap f U
-/
theorem gc_map_comap (f : F) : GaloisConnection (map f) (comap f) :=
  fun _S _U => map_le

@[simp]
/-
**NonUnitalStarSubalgebra.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSuba
lgebra`。
形式化陈述：mem_comap (S : NonUnitalStarSubalgebra R B) (f : F) (x : A) : x in comap f
 S ↔ f x in S
参数：S : NonUnitalStarSubalgebra R B；f : F；x : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap (S : NonUnitalStarSubalgebra R B) (f : F) (x : A) : x ∈ comap f S ↔ f x ∈ S :=
  Iff.rfl

@[simp, norm_cast]
/-
**NonUnitalStarSubalgebra.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSuba
lgebra`。
形式化陈述：coe_comap (S : NonUnitalStarSubalgebra R B) (f : F) : comap f S = f ⁻¹' (S
 : Set B)
参数：S : NonUnitalStarSubalgebra R B；f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (S : NonUnitalStarSubalgebra R B) (f : F) : comap f S = f ⁻¹' (S : Set B) :=
  rfl
/-
**NonUnitalStarSubalgebra.instNoZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `NonUnita
lStarSubalgebra`。
形式化陈述：instNoZeroDivisors {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [N
oZeroDivisors A] [Module R A] [Star A] (S : NonUnitalStarSubalgebra R A) : NoZer
oDivisors S
参数：S : NonUnitalStarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNoZeroDivisors {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [NoZeroDivisors A]
    [Module R A] [Star A] (S : NonUnitalStarSubalgebra R A) : NoZeroDivisors S :=
  NonUnitalSubsemiringClass.noZeroDivisors S

end NonUnitalStarSubalgebra

namespace NonUnitalSubalgebra

variable [CommSemiring R] [NonUnitalSemiring A] [Module R A] [Star A]
variable (s : NonUnitalSubalgebra R A)

/-- A non-unital subalgebra closed under `star` is a non-unital star subalgebra. -/
/-
**NonUnitalSubalgebra.toNonUnitalStarSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `NonUn
italSubalgebra`。
形式化陈述：toNonUnitalStarSubalgebra (h_star : forall x, x in s -> star x in s) : Non
UnitalStarSubalgebra R A
参数：h_star : forall x, x in s -> star x in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subalgebra closed under `star` is a non-unital star subalgebra.
-/
def toNonUnitalStarSubalgebra (h_star : ∀ x, x ∈ s → star x ∈ s) : NonUnitalStarSubalgebra R A :=
  { s with
    star_mem' := @h_star }

@[simp]
/-
**NonUnitalSubalgebra.mem_toNonUnitalStarSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `N
onUnitalSubalgebra`。
形式化陈述：mem_toNonUnitalStarSubalgebra {s : NonUnitalSubalgebra R A} {h_star} {x} :
 x in s.toNonUnitalStarSubalgebra h_star ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toNonUnitalStarSubalgebra {s : NonUnitalSubalgebra R A} {h_star} {x} :
    x ∈ s.toNonUnitalStarSubalgebra h_star ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**NonUnitalSubalgebra.coe_toNonUnitalStarSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `N
onUnitalSubalgebra`。
形式化陈述：coe_toNonUnitalStarSubalgebra (s : NonUnitalSubalgebra R A) (h_star) : (s.
toNonUnitalStarSubalgebra h_star : Set A) = s
参数：s : NonUnitalSubalgebra R A；h_star。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNonUnitalStarSubalgebra (s : NonUnitalSubalgebra R A) (h_star) :
    (s.toNonUnitalStarSubalgebra h_star : Set A) = s :=
  rfl

@[simp]
/-
**NonUnitalSubalgebra.toNonUnitalStarSubalgebra_toNonUnitalSubalgebra** 是 Mathli
b 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：toNonUnitalStarSubalgebra_toNonUnitalSubalgebra (s : NonUnitalSubalgebra R
 A) (h_star) : (s.toNonUnitalStarSubalgebra h_star).toNonUnitalSubalgebra = s
参数：s : NonUnitalSubalgebra R A；h_star。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem toNonUnitalStarSubalgebra_toNonUnitalSubalgebra (s : NonUnitalSubalgebra R A) (h_star) :
    (s.toNonUnitalStarSubalgebra h_star).toNonUnitalSubalgebra = s :=
  SetLike.coe_injective rfl

@[simp]
/-
**NonUnitalSubalgebra._root_.NonUnitalStarSubalgebra.toNonUnitalSubalgebra_toNon
UnitalStarSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- Range of an `NonUnitalAlgHom` as a `NonUnitalStarSubalgebra`. -/
/-
**NonUnitalStarAlgHom.range** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：{F : Type v'} →   {R : Type u} →     {A : Type v} →       {B : Type w} →  
       [inst : CommSemiring R] →           [inst_1 : NonUnitalNonAssocSemiring A
] →             [inst_2 : _root_.Module R A] →               [inst_3 : Star A] →
                 [inst_4 : NonUnitalNonAssocSemiring B] →                   [ins
t_5 : _root_.Module R B] →                     [inst_6 : Star B] →              
         [inst_7 : FunLike F A B] →                         [NonUnitalAlgHomClas
s F R A B] → [StarHomClass F A B] → F → NonUnitalStarSubalgebra R B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Range of an `NonUnitalAlgHom` as a `NonUnitalStarSubalgebra`.
-/
protected def range (φ : F) : NonUnitalStarSubalgebra R B where
  toNonUnitalSubalgebra := NonUnitalAlgHom.range (φ : A →ₙₐ[R] B)
  star_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨star a, map_star φ a⟩

@[simp]
/-
**NonUnitalStarAlgHom.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：mem_range (φ : F) {y : B} : y in (NonUnitalStarAlgHom.range φ : NonUnitalS
tarSubalgebra R B) ↔ exists x : A, φ x = y
参数：φ : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.mem_srange`：mem_srange {f : F} {y : S} : y in srange f 
↔ exists x, f x = y
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
-/
theorem mem_range (φ : F) {y : B} :
    y ∈ (NonUnitalStarAlgHom.range φ : NonUnitalStarSubalgebra R B) ↔ ∃ x : A, φ x = y :=
  NonUnitalRingHom.mem_srange
/-
**NonUnitalStarAlgHom.mem_range_self** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlg
Hom`。
形式化陈述：mem_range_self (φ : F) (x : A) : φ x in (NonUnitalStarAlgHom.range φ : Non
UnitalStarSubalgebra R B)
参数：φ : F；x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalAlgHom.mem_range`：mem_range (φ : F) {y : B} : y in (NonUnitalAl
gHom.range φ : NonUnitalSubalgebra R B) ↔ exists x : A, φ x = y
-/
theorem mem_range_self (φ : F) (x : A) :
    φ x ∈ (NonUnitalStarAlgHom.range φ : NonUnitalStarSubalgebra R B) :=
  (NonUnitalAlgHom.mem_range φ).2 ⟨x, rfl⟩

@[simp, norm_cast]
/-
**NonUnitalStarAlgHom.coe_range** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：coe_range (φ : F) : ((NonUnitalStarAlgHom.range φ : NonUnitalStarSubalgebr
a R B) : Set B) = Set.range (φ : A -> B)
参数：φ : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_range (φ : F) :
    ((NonUnitalStarAlgHom.range φ : NonUnitalStarSubalgebra R B) : Set B) =
    Set.range (φ : A → B) := by
  rfl
/-
**NonUnitalStarAlgHom.range_comp** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`
。
形式化陈述：range_comp (f : A ->⋆ₙₐ[R] B) (g : B ->⋆ₙₐ[R] C) : NonUnitalStarAlgHom.ran
ge (g.comp f) = (NonUnitalStarAlgHom.range f).map g
参数：f : A ->⋆ₙₐ[R] B；g : B ->⋆ₙₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `NonUnitalStarAlgHom.instStarHomClass`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 
: DistribMulAction R A] [i…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem range_comp (f : A →⋆ₙₐ[R] B) (g : B →⋆ₙₐ[R] C) :
    NonUnitalStarAlgHom.range (g.comp f) = (NonUnitalStarAlgHom.range f).map g :=
  SetLike.coe_injective (Set.range_comp g f)
/-
**NonUnitalStarAlgHom.range_comp_le_range** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSt
arAlgHom`。
形式化陈述：range_comp_le_range (f : A ->⋆ₙₐ[R] B) (g : B ->⋆ₙₐ[R] C) : NonUnitalStarA
lgHom.range (g.comp f) <= NonUnitalStarAlgHom.range g
参数：f : A ->⋆ₙₐ[R] B；g : B ->⋆ₙₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `NonUnitalStarAlgHom.instStarHomClass`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 
: DistribMulAction R A] [i…
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
-/
theorem range_comp_le_range (f : A →⋆ₙₐ[R] B) (g : B →⋆ₙₐ[R] C) :
    NonUnitalStarAlgHom.range (g.comp f) ≤ NonUnitalStarAlgHom.range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

/-- Restrict the codomain of a non-unital star algebra homomorphism. -/
/-
**NonUnitalStarAlgHom.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgHom
`。
形式化陈述：codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : forall x, f x 
in S) : A ->⋆ₙₐ[R] S where toNonUnitalAlgHom
参数：f : F；S : NonUnitalStarSubalgebra R B；hf : forall x, f x in S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the codomain of a non-unital star algebra homomorphism.
-/
def codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : ∀ x, f x ∈ S) : A →⋆ₙₐ[R] S where
  toNonUnitalAlgHom := NonUnitalAlgHom.codRestrict f S.toNonUnitalSubalgebra hf
  map_star' := fun a => Subtype.ext <| map_star f a

@[simp]
/-
**NonUnitalStarAlgHom.subtype_comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `NonUni
talStarAlgHom`。
形式化陈述：subtype_comp_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : f
orall x : A, f x in S) : (NonUnitalStarSubalgebraClass.subtype S).comp (NonUnita
lStarAlgHom.codRestrict f S hf) = f
参数：f : F；S : NonUnitalStarSubalgebra R B；hf : forall x : A, f x in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgHom.ext`：ext {f g : A ->⋆ₙₐ[R] B} (h : forall x, f x = g
 x) : f = g
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
-/
theorem subtype_comp_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    (NonUnitalStarSubalgebraClass.subtype S).comp (NonUnitalStarAlgHom.codRestrict f S hf) = f :=
  NonUnitalStarAlgHom.ext fun _ => rfl

@[simp]
/-
**NonUnitalStarAlgHom.coe_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAl
gHom`。
形式化陈述：coe_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : forall x, 
f x in S) (x : A) : ↑(NonUnitalStarAlgHom.codRestrict f S hf x) = f x
参数：f : F；S : NonUnitalStarSubalgebra R B；hf : forall x, f x in S；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
    ↑(NonUnitalStarAlgHom.codRestrict f S hf x) = f x :=
  rfl
/-
**NonUnitalStarAlgHom.injective_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
StarAlgHom`。
形式化陈述：injective_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : fora
ll x : A, f x in S) : Function.Injective (NonUnitalStarAlgHom.codRestrict f S hf
) ↔ Function.Injective f
参数：f : F；S : NonUnitalStarSubalgebra R B；hf : forall x : A, f x in S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem injective_codRestrict (f : F) (S : NonUnitalStarSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    Function.Injective (NonUnitalStarAlgHom.codRestrict f S hf) ↔ Function.Injective f :=
  ⟨fun H _x _y hxy => H <| Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

/-- Restrict the codomain of a non-unital star algebra homomorphism `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`. -/
/-
**NonUnitalStarAlgHom.rangeRestrict** 是 Mathlib 中的一个缩写定义，位于命名空间 `NonUnitalStarAl
gHom`。
形式化陈述：rangeRestrict (f : F) : A ->⋆ₙₐ[R] (NonUnitalStarAlgHom.range f : NonUnita
lStarSubalgebra R B)
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgHom.mem_range_self`：mem_range_self (φ : F) (x : A) : φ x
 in (NonUnitalStarAlgHom.range φ : NonUnitalStarSubalgebra R B)

--- 原说明 ---
Restrict the codomain of a non-unital star algebra homomorphism `f` to `f.range`
.

This is the bundled version of `Set.rangeFactorization`.
-/
abbrev rangeRestrict (f : F) :
    A →⋆ₙₐ[R] (NonUnitalStarAlgHom.range f : NonUnitalStarSubalgebra R B) :=
  NonUnitalStarAlgHom.codRestrict f (NonUnitalStarAlgHom.range f)
    (NonUnitalStarAlgHom.mem_range_self f)

/-- The equalizer of two non-unital star `R`-algebra homomorphisms -/
/-
**NonUnitalStarAlgHom.equalizer** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：equalizer (ϕ ψ : F) : NonUnitalStarSubalgebra R A where toNonUnitalSubalge
bra
参数：ϕ ψ : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equalizer of two non-unital star `R`-algebra homomorphisms
-/
def equalizer (ϕ ψ : F) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := NonUnitalAlgHom.equalizer ϕ ψ
  star_mem' := @fun x (hx : ϕ x = ψ x) => by simp [map_star, hx]

@[simp]
/-
**NonUnitalStarAlgHom.mem_equalizer** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgH
om`。
形式化陈述：mem_equalizer (φ ψ : F) (x : A) : x in NonUnitalStarAlgHom.equalizer φ ψ ↔
 φ x = ψ x
参数：φ ψ : F；x : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_equalizer (φ ψ : F) (x : A) :
    x ∈ NonUnitalStarAlgHom.equalizer φ ψ ↔ φ x = ψ x :=
  Iff.rfl

end NonUnitalStarAlgHom

namespace StarAlgEquiv
variable [CommSemiring R]
variable [NonUnitalSemiring A] [Module R A] [Star A]
variable [NonUnitalSemiring B] [Module R B] [Star B]
variable [NonUnitalSemiring C] [Module R C] [Star C]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

/-- Restrict a non-unital star algebra homomorphism with a left inverse to an algebra isomorphism
to its range.

This is a computable alternative to `StarAlgEquiv.ofInjective`. -/
/-
**StarAlgEquiv.ofLeftInverse'** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquiv`。
形式化陈述：ofLeftInverse' {g : B -> A} {f : F} (h : Function.LeftInverse g f) : A ≃⋆ₐ
[R] NonUnitalStarAlgHom.range f
参数：h : Function.LeftInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a non-unital star algebra homomorphism with a left inverse to an algebr
a isomorphism
to its range.

This is a computable alternative to `StarAlgEquiv.ofInjective`.
-/
def ofLeftInverse' {g : B → A} {f : F} (h : Function.LeftInverse g f) :
    A ≃⋆ₐ[R] NonUnitalStarAlgHom.range f :=
  { NonUnitalStarAlgHom.rangeRestrict f with
    toFun := NonUnitalStarAlgHom.rangeRestrict f
    invFun := g ∘ (NonUnitalStarSubalgebraClass.subtype <| NonUnitalStarAlgHom.range f)
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := (NonUnitalStarAlgHom.mem_range f).mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
/-
**StarAlgEquiv.ofLeftInverse'_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：∀ {F : Type v'} {R : Type u} {A : Type v} {B : Type w} [inst : CommSemirin
g R] [inst_1 : NonUnitalSemiring A]   [inst_2 : _root_.Module R A] [inst_3 : Sta
r A] [inst_4 : NonUnitalSemiring B] [inst_5 : _root_.Module R B]   [inst_6 : Sta
r B] [inst_7 : FunLike F A B] [inst_8 : NonUnitalAlgHomClass F R A B] [inst_9 : 
StarHomClass F A B]   {g : B → A} {f : F} (h : Function.LeftInverse g ⇑f) (x : A
), ↑((StarAlgEquiv.ofLeftInverse' h) x) = f x
参数：h : Function.LeftInverse g ⇑f；x : A；(StarAlgEquiv.ofLeftInverse' h) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLeftInverse'_apply {g : B → A} {f : F} (h : Function.LeftInverse g f) (x : A) :
    ofLeftInverse' h x = f x :=
  rfl

@[simp]
/-
**StarAlgEquiv.ofLeftInverse'_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv
`。
形式化陈述：∀ {F : Type v'} {R : Type u} {A : Type v} {B : Type w} [inst : CommSemirin
g R] [inst_1 : NonUnitalSemiring A]   [inst_2 : _root_.Module R A] [inst_3 : Sta
r A] [inst_4 : NonUnitalSemiring B] [inst_5 : _root_.Module R B]   [inst_6 : Sta
r B] [inst_7 : FunLike F A B] [inst_8 : NonUnitalAlgHomClass F R A B] [inst_9 : 
StarHomClass F A B]   {g : B → A} {f : F} (h : Function.LeftInverse g ⇑f) (x : ↥
(NonUnitalStarAlgHom.range f)),   (StarAlgEquiv.ofLeftInverse' h).symm x = g ↑x
参数：h : Function.LeftInverse g ⇑f；x : ↥(NonUnitalStarAlgHom.range f)；StarAlgEquiv
.ofLeftInverse' h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLeftInverse'_symm_apply {g : B → A} {f : F} (h : Function.LeftInverse g f)
    (x : NonUnitalStarAlgHom.range f) : (ofLeftInverse' h).symm x = g x :=
  rfl

/-- Restrict an injective non-unital star algebra homomorphism to a star algebra isomorphism -/
/-
**StarAlgEquiv.ofInjective'** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquiv`。
形式化陈述：ofInjective' (f : F) (hf : Function.Injective f) : A ≃⋆ₐ[R] NonUnitalStarA
lgHom.range f
参数：f : F；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict an injective non-unital star algebra homomorphism to a star algebra iso
morphism
-/
noncomputable def ofInjective' (f : F) (hf : Function.Injective f) :
    A ≃⋆ₐ[R] NonUnitalStarAlgHom.range f :=
  ofLeftInverse' (Classical.choose_spec hf.hasLeftInverse)

@[simp]
/-
**StarAlgEquiv.ofInjective'_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：∀ {F : Type v'} {R : Type u} {A : Type v} {B : Type w} [inst : CommSemirin
g R] [inst_1 : NonUnitalSemiring A]   [inst_2 : _root_.Module R A] [inst_3 : Sta
r A] [inst_4 : NonUnitalSemiring B] [inst_5 : _root_.Module R B]   [inst_6 : Sta
r B] [inst_7 : FunLike F A B] [inst_8 : NonUnitalAlgHomClass F R A B] [inst_9 : 
StarHomClass F A B]   (f : F) (hf : Function.Injective ⇑f) (x : A), ↑((StarAlgEq
uiv.ofInjective' f hf) x) = f x
参数：f : F；hf : Function.Injective ⇑f；x : A；(StarAlgEquiv.ofInjective' f hf) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- The pointwise `star` of a non-unital subalgebra is a non-unital subalgebra. -/
/-
**NonUnitalSubalgebra.instInvolutiveStar** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSub
algebra`。
形式化陈述：instInvolutiveStar : InvolutiveStar (NonUnitalSubalgebra R A) where star S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pointwise `star` of a non-unital subalgebra is a non-unital subalgebra.
-/
instance instInvolutiveStar : InvolutiveStar (NonUnitalSubalgebra R A) where
  star S :=
    { carrier := star S.carrier
      mul_mem' := @fun x y hx hy => by simpa only [Set.mem_star, NonUnitalSubalgebra.mem_carrier]
        using (star_mul x y).symm ▸ mul_mem hy hx
      add_mem' := @fun x y hx hy => by simpa only [Set.mem_star, NonUnitalSubalgebra.mem_carrier]
        using (star_add x y).symm ▸ add_mem hx hy
      zero_mem' := Set.mem_star.mp ((star_zero A).symm ▸ zero_mem S : star (0 : A) ∈ S)
      smul_mem' := fun r x hx => by simpa only [Set.mem_star, NonUnitalSubalgebra.mem_carrier]
        using (star_smul r x).symm ▸ SMulMemClass.smul_mem (star r) hx }
  star_involutive S := NonUnitalSubalgebra.ext fun x =>
      ⟨fun hx => star_star x ▸ hx, fun hx => ((star_star x).symm ▸ hx : star (star x) ∈ S)⟩

@[simp]
/-
**NonUnitalSubalgebra.mem_star_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebr
a`。
形式化陈述：mem_star_iff (S : NonUnitalSubalgebra R A) (x : A) : x in star S ↔ star x 
in S
参数：S : NonUnitalSubalgebra R A；x : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_star_iff (S : NonUnitalSubalgebra R A) (x : A) : x ∈ star S ↔ star x ∈ S :=
  Iff.rfl
/-
**NonUnitalSubalgebra.star_mem_star_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSuba
lgebra`。
形式化陈述：star_mem_star_iff (S : NonUnitalSubalgebra R A) (x : A) : star x in star S
 ↔ x in S
参数：S : NonUnitalSubalgebra R A；x : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem star_mem_star_iff (S : NonUnitalSubalgebra R A) (x : A) : star x ∈ star S ↔ x ∈ S := by
  simp

@[simp]
/-
**NonUnitalSubalgebra.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：coe_star (S : NonUnitalSubalgebra R A) : star S = star (S : Set A)
参数：S : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_star (S : NonUnitalSubalgebra R A) : star S = star (S : Set A) :=
  rfl
/-
**NonUnitalSubalgebra.star_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：star_mono : Monotone (star : NonUnitalSubalgebra R A -> NonUnitalSubalgebr
a R A)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_mono : Monotone (star : NonUnitalSubalgebra R A → NonUnitalSubalgebra R A) :=
  fun _ _ h _ hx => h hx

variable (R)
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The star operation on `NonUnitalSubalgebra` commutes with `NonUnitalAlgebra.adjoin`. -/
/-
**NonUnitalSubalgebra.star_adjoin_comm** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubal
gebra`。
形式化陈述：star_adjoin_comm (s : Set A) : star (NonUnitalAlgebra.adjoin R s) = NonUni
talAlgebra.adjoin R (star s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.adjoin_le`：adjoin_le {S : NonUnitalSubalgebra R A} {s :
 Set A} (hs : s subseteq S) : adjoin R s <= S
· 使用定理 `NonUnitalAlgebra.subset_adjoin`：subset_adjoin {s : Set A} : s subseteq a
djoin R s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalAlgebra.adjoin.congr_simp`：∀ (R : Type u) {A : Type v} [inst : 
CommSemiring R] [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R
 A]   [inst_3 : IsScalar…
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `NonUnitalSubalgebra.star_mono`：star_mono : Monotone (star : NonUnitalSub
algebra R A -> NonUnitalSubalgebra R A)

--- 原说明 ---
The star operation on `NonUnitalSubalgebra` commutes with `NonUnitalAlgebra.adjo
in`.
-/
theorem star_adjoin_comm (s : Set A) :
    star (NonUnitalAlgebra.adjoin R s) = NonUnitalAlgebra.adjoin R (star s) :=
  have :
    ∀ t : Set A, NonUnitalAlgebra.adjoin R (star t) ≤ star (NonUnitalAlgebra.adjoin R t) := fun _ =>
    NonUnitalAlgebra.adjoin_le fun _ hx => NonUnitalAlgebra.subset_adjoin R hx
  le_antisymm (by simpa only [star_star] using NonUnitalSubalgebra.star_mono (this (star s)))
    (this s)

variable {R}

/-- The `NonUnitalStarSubalgebra` obtained from `S : NonUnitalSubalgebra R A` by taking the
smallest non-unital subalgebra containing both `S` and `star S`. -/
/-
**NonUnitalSubalgebra.starClosure** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubalgebra
`。
形式化陈述：starClosure (S : NonUnitalSubalgebra R A) : NonUnitalStarSubalgebra R A wh
ere toNonUnitalSubalgebra
参数：S : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `NonUnitalStarSubalgebra` obtained from `S : NonUnitalSubalgebra R A` by tak
ing the
smallest non-unital subalgebra containing both `S` and `star S`.
-/
def starClosure (S : NonUnitalSubalgebra R A) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := S ⊔ star S
  star_mem' {a} ha := by
    simpa [← mem_star_iff _ a, ← (@NonUnitalAlgebra.gi R A _ _ _ _ _).l_sup_u _ _, star_adjoin_comm,
      Set.union_comm] using ha

@[simp]
/-
**NonUnitalSubalgebra.coe_starClosure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalg
ebra`。
形式化陈述：coe_starClosure (S : NonUnitalSubalgebra R A) : (S.starClosure : Set A) = 
(S ⊔ star S : NonUnitalSubalgebra R A)
参数：S : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_starClosure (S : NonUnitalSubalgebra R A) :
    (S.starClosure : Set A) = (S ⊔ star S : NonUnitalSubalgebra R A) := rfl

@[simp]
/-
**NonUnitalSubalgebra.mem_starClosure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalg
ebra`。
形式化陈述：mem_starClosure (S : NonUnitalSubalgebra R A) {x : A} : x in S.starClosure
 ↔ x in S ⊔ star S
参数：S : NonUnitalSubalgebra R A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_starClosure (S : NonUnitalSubalgebra R A) {x : A} :
    x ∈ S.starClosure ↔ x ∈ S ⊔ star S := Iff.rfl

@[simp]
/-
**NonUnitalSubalgebra.starClosure_toNonUnitalSubalgebra** 是 Mathlib 中的一个定理，位于命名空
间 `NonUnitalSubalgebra`。
形式化陈述：starClosure_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A) : S.starCl
osure.toNonUnitalSubalgebra = S ⊔ star S
参数：S : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem starClosure_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A) :
    S.starClosure.toNonUnitalSubalgebra = S ⊔ star S := rfl
/-
**NonUnitalSubalgebra.starClosure_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalge
bra`。
形式化陈述：starClosure_le {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebr
a R A} (h : S₁ <= S₂.toNonUnitalSubalgebra) : S₁.starClosure <= S₂
参数：h : S₁ <= S₂.toNonUnitalSubalgebra。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff`：toNonUnitalSubalge
bra_le_iff {S₁ S₂ : NonUnitalStarSubalgebra R A} : S₁.toNonUnitalSubalgebra <= S
₂.toNonUnitalSubalgebra ↔ S₁ <= S₂
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
· 使用定理 `NonUnitalSubalgebra.mem_star_iff`：mem_star_iff (S : NonUnitalSubalgebra 
R A) (x : A) : x in star S ↔ star x in S
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
theorem starClosure_le {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebra R A}
    (h : S₁ ≤ S₂.toNonUnitalSubalgebra) : S₁.starClosure ≤ S₂ :=
  NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff.1 <|
    sup_le h fun x hx =>
      (star_star x ▸ star_mem (show star x ∈ S₂ from h <| (S₁.mem_star_iff _).1 hx) : x ∈ S₂)
/-
**NonUnitalSubalgebra.starClosure_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSub
algebra`。
形式化陈述：starClosure_le_iff {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubal
gebra R A} : S₁.starClosure <= S₂ ↔ S₁ <= S₂.toNonUnitalSubalgebra
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `NonUnitalSubalgebra.starClosure_le`：starClosure_le {S₁ : NonUnitalSubalg
ebra R A} {S₂ : NonUnitalStarSubalgebra R A} (h : S₁ <= S₂.toNonUnitalSubalgebra
) : S₁.starClosure <= S₂
-/
theorem starClosure_le_iff {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebra R A} :
    S₁.starClosure ≤ S₂ ↔ S₁ ≤ S₂.toNonUnitalSubalgebra :=
  ⟨fun h => le_sup_left.trans h, starClosure_le⟩

@[gcongr, mono]
/-
**NonUnitalSubalgebra.starClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubal
gebra`。
形式化陈述：starClosure_mono : Monotone (starClosure (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.starClosure_le`：starClosure_le {S₁ : NonUnitalSubalg
ebra R A} {S₂ : NonUnitalStarSubalgebra R A} (h : S₁ <= S₂.toNonUnitalSubalgebra
) : S₁.starClosure <= S₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem starClosure_mono : Monotone (starClosure (R := R) (A := A)) :=
  fun _ _ h => starClosure_le <| h.trans le_sup_left

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

/-- The minimal non-unital subalgebra that includes `s`. -/
/-
**NonUnitalStarAlgebra.adjoin** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：adjoin (s : Set A) : NonUnitalStarSubalgebra R A where toNonUnitalSubalgeb
ra
参数：s : Set A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimal non-unital subalgebra that includes `s`.
-/
def adjoin (s : Set A) : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := NonUnitalAlgebra.adjoin R (s ∪ star s)
  star_mem' _ := by
    rwa [NonUnitalSubalgebra.mem_carrier, ← NonUnitalSubalgebra.mem_star_iff,
      NonUnitalSubalgebra.star_adjoin_comm, Set.union_star, star_star, Set.union_comm]
/-
**NonUnitalStarAlgebra.adjoin_eq_starClosure_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `N
onUnitalStarAlgebra`。
形式化陈述：adjoin_eq_starClosure_adjoin (s : Set A) : adjoin R s = (NonUnitalAlgebra.
adjoin R s).starClosure
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.toNonUnitalSubalgebra_injective`：toNonUnitalSuba
lgebra_injective : Function.Injective (toNonUnitalSubalgebra : NonUnitalStarSuba
lgebra R A -> NonUnitalSubalgebra R A)
· 使用定理 `NonUnitalAlgebra.adjoin_union`：adjoin_union (s t : Set A) : adjoin R (s 
union t) = adjoin R s ⊔ adjoin R t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalSubalgebra.star_adjoin_comm`：star_adjoin_comm (s : Set A) : sta
r (NonUnitalAlgebra.adjoin R s) = NonUnitalAlgebra.adjoin R (star s)
-/
theorem adjoin_eq_starClosure_adjoin (s : Set A) :
    adjoin R s = (NonUnitalAlgebra.adjoin R s).starClosure :=
  toNonUnitalSubalgebra_injective <| show
    NonUnitalAlgebra.adjoin R (s ∪ star s) =
      NonUnitalAlgebra.adjoin R s ⊔ star (NonUnitalAlgebra.adjoin R s)
    from
      (NonUnitalSubalgebra.star_adjoin_comm R s).symm ▸ NonUnitalAlgebra.adjoin_union s (star s)
/-
**NonUnitalStarAlgebra.adjoin_toNonUnitalSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `N
onUnitalStarAlgebra`。
形式化陈述：adjoin_toNonUnitalSubalgebra (s : Set A) : (adjoin R s).toNonUnitalSubalge
bra = NonUnitalAlgebra.adjoin R (s union star s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjoin_toNonUnitalSubalgebra (s : Set A) :
    (adjoin R s).toNonUnitalSubalgebra = NonUnitalAlgebra.adjoin R (s ∪ star s) := rfl

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/-
**NonUnitalStarAlgebra.subset_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlg
ebra`。
形式化陈述：subset_adjoin (s : Set A) : s subseteq adjoin R s
参数：s : Set A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `NonUnitalAlgebra.subset_adjoin`：subset_adjoin {s : Set A} : s subseteq a
djoin R s
-/
theorem subset_adjoin (s : Set A) : s ⊆ adjoin R s :=
  Set.subset_union_left.trans <| NonUnitalAlgebra.subset_adjoin R

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/-
**NonUnitalStarAlgebra.star_subset_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSt
arAlgebra`。
形式化陈述：star_subset_adjoin (s : Set A) : star s subseteq adjoin R s
参数：s : Set A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `NonUnitalAlgebra.subset_adjoin`：subset_adjoin {s : Set A} : s subseteq a
djoin R s
-/
theorem star_subset_adjoin (s : Set A) : star s ⊆ adjoin R s :=
  Set.subset_union_right.trans <| NonUnitalAlgebra.subset_adjoin R

@[aesop 80% (rule_sets := [SetLike])]
/-
**NonUnitalStarAlgebra.mem_adjoin_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSta
rAlgebra`。
形式化陈述：mem_adjoin_of_mem {s : Set A} {x : A} (hx : x in s) : x in adjoin R s
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgebra.subset_adjoin`：subset_adjoin (s : Set A) : s subset
eq adjoin R s
-/
theorem mem_adjoin_of_mem {s : Set A} {x : A} (hx : x ∈ s) : x ∈ adjoin R s := subset_adjoin R s hx

@[simp]
/-
**NonUnitalStarAlgebra.self_mem_adjoin_singleton** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalStarAlgebra`。
形式化陈述：self_mem_adjoin_singleton (x : A) : x in adjoin R ({x} : Set A)
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.subset_adjoin`：subset_adjoin {s : Set A} : s subseteq a
djoin R s
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : Set A) :=
  NonUnitalAlgebra.subset_adjoin R <| Set.mem_union_left _ (Set.mem_singleton x)
/-
**NonUnitalStarAlgebra.star_self_mem_adjoin_singleton** 是 Mathlib 中的一个定理，位于命名空间 
`NonUnitalStarAlgebra`。
形式化陈述：star_self_mem_adjoin_singleton (x : A) : star x in adjoin R ({x} : Set A)
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
· 使用定理 `NonUnitalStarAlgebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleto
n (x : A) : x in adjoin R ({x} : Set A)
-/
theorem star_self_mem_adjoin_singleton (x : A) : star x ∈ adjoin R ({x} : Set A) :=
  star_mem <| self_mem_adjoin_singleton R x

@[elab_as_elim]
/-
**NonUnitalStarAlgebra.adjoin_induction** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalStar
Algebra`。
形式化陈述：adjoin_induction {s : Set A} {p : (x : A) -> x in adjoin R s -> Prop} (mem
 : forall (x : A) (hx : x in s), p x (subset_adjoin R s hx)) (add : forall x y h
x hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)) (zero : p 0 (zero_mem _)) (
mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)) (smul : f
orall (r : R) x hx, p x hx -> p (r • x) (SMulMemClass.smul_mem r hx)) (star : fo
rall x hx, p x hx -> p (star x) (star_mem hx)) {a : A} (ha : a in adjoin R s) : 
p a ha
参数：x : A；mem : forall (x : A) (hx : x in s), p x (subset_adjoin R s hx)；add : fo
rall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)；zero : p 0 (zero_m
em _)；mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)；smul
 : forall (r : R) x hx, p x hx -> p (r • x) (SMulMemClass.smul_mem r hx)；star : 
forall x hx, p x hx -> p (star x) (star_mem hx)；ha : a in adjoin R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgebra.subset_adjoin`：subset_adjoin (s : Set A) : s subset
eq adjoin R s
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
· 使用定理 `NonUnitalAlgebra.adjoin_induction`：adjoin_induction {s : Set A} {p : (x 
: A) -> x in adjoin R s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_ad
join R hx)) (add : fora…
· 使用定理 `NonUnitalAlgebra.subset_adjoin`：subset_adjoin {s : Set A} : s subseteq a
djoin R s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
lemma adjoin_induction {s : Set A} {p : (x : A) → x ∈ adjoin R s → Prop}
    (mem : ∀ (x : A) (hx : x ∈ s), p x (subset_adjoin R s hx))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (zero : p 0 (zero_mem _)) (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (smul : ∀ (r : R) x hx, p x hx → p (r • x) (SMulMemClass.smul_mem r hx))
    (star : ∀ x hx, p x hx → p (star x) (star_mem hx))
    {a : A} (ha : a ∈ adjoin R s) : p a ha := by
  refine NonUnitalAlgebra.adjoin_induction (fun x hx ↦ ?_) add zero mul smul ha
  push _ ∈ _ at hx
  obtain (hx | hx) := hx
  · exact mem x hx
  · simpa using star _ (NonUnitalAlgebra.subset_adjoin R (by simpa using Or.inl hx)) (mem _ hx)

variable {R}
/-
**NonUnitalStarAlgebra.gc** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : StarRing R] 
[inst_2 : NonUnitalSemiring A]   [inst_3 : StarRing A] [inst_4 : _root_.Module R
 A] [inst_5 : IsScalarTower R A A] [inst_6 : SMulCommClass R A A]   [inst_7 : St
arModule R A], GaloisConnection (NonUnitalStarAlgebra.adjoin R) SetLike.coe
参数：NonUnitalStarAlgebra.adjoin R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff`：toNonUnitalSubalge
bra_le_iff {S₁ S₂ : NonUnitalStarSubalgebra R A} : S₁.toNonUnitalSubalgebra <= S
₂.toNonUnitalSubalgebra ↔ S₁ <= S₂
· 使用定理 `NonUnitalStarAlgebra.adjoin_toNonUnitalSubalgebra`：adjoin_toNonUnitalSub
algebra (s : Set A) : (adjoin R s).toNonUnitalSubalgebra = NonUnitalAlgebra.adjo
in R (s union star s)
· 使用定理 `NonUnitalAlgebra.adjoin_le_iff`：adjoin_le_iff {S : NonUnitalSubalgebra R
 A} {s : Set A} : adjoin R s <= S ↔ s subseteq S
· 使用定理 `NonUnitalStarSubalgebra.coe_toNonUnitalSubalgebra`：coe_toNonUnitalSubalg
ebra (S : NonUnitalStarSubalgebra R A) : (↑S.toNonUnitalSubalgebra : Set A) = S
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
protected theorem gc : GaloisConnection (adjoin R : Set A → NonUnitalStarSubalgebra R A) (↑) := by
  intro s S
  rw [← toNonUnitalSubalgebra_le_iff, adjoin_toNonUnitalSubalgebra,
    NonUnitalAlgebra.adjoin_le_iff, coe_toNonUnitalSubalgebra]
  exact ⟨fun h => Set.subset_union_left.trans h,
    fun h => Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x ∈ S from h hx)⟩

/-- Galois insertion between `adjoin` and `SetLike.coe`. -/
/-
**NonUnitalStarAlgebra.gi** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：{R : Type u} →   {A : Type v} →     [inst : CommSemiring R] →       [inst_
1 : StarRing R] →         [inst_2 : NonUnitalSemiring A] →           [inst_3 : S
tarRing A] →             [inst_4 : _root_.Module R A] →               [inst_5 : 
IsScalarTower R A A] →                 [inst_6 : SMulCommClass R A A] →         
          [inst_7 : StarModule R A] → GaloisInsertion (NonUnitalStarAlgebra.adjo
in R) SetLike.coe
参数：NonUnitalStarAlgebra.adjoin R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemirin
g R] [inst_1 : StarRing R] [inst_2 : NonUnitalSemiring A]   [inst_3 : StarRing A
] [inst_4 : _…

--- 原说明 ---
Galois insertion between `adjoin` and `SetLike.coe`.
-/
protected def gi : GaloisInsertion (adjoin R : Set A → NonUnitalStarSubalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s <| le_antisymm (NonUnitalStarAlgebra.gc.le_u_l s) hs
  gc := NonUnitalStarAlgebra.gc
  le_l_u S := (NonUnitalStarAlgebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := NonUnitalStarSubalgebra.copy_eq _ _ _
/-
**NonUnitalStarAlgebra.adjoin_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra
`。
形式化陈述：adjoin_le {S : NonUnitalStarSubalgebra R A} {s : Set A} (hs : s subseteq S
) : adjoin R s <= S
参数：hs : s subseteq S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_le`：l_le {a : α} {b : β} : a <= u b -> l a <= b
· 使用定理 `NonUnitalStarAlgebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemirin
g R] [inst_1 : StarRing R] [inst_2 : NonUnitalSemiring A]   [inst_3 : StarRing A
] [inst_4 : _…
-/
theorem adjoin_le {S : NonUnitalStarSubalgebra R A} {s : Set A} (hs : s ⊆ S) : adjoin R s ≤ S :=
  NonUnitalStarAlgebra.gc.l_le hs

@[simp]
/-
**NonUnitalStarAlgebra.adjoin_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlg
ebra`。
形式化陈述：adjoin_le_iff {S : NonUnitalStarSubalgebra R A} {s : Set A} : adjoin R s <
= S ↔ s subseteq S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemirin
g R] [inst_1 : StarRing R] [inst_2 : NonUnitalSemiring A]   [inst_3 : StarRing A
] [inst_4 : _…
-/
theorem adjoin_le_iff {S : NonUnitalStarSubalgebra R A} {s : Set A} : adjoin R s ≤ S ↔ s ⊆ S :=
  NonUnitalStarAlgebra.gc _ _

@[gcongr]
/-
**NonUnitalStarAlgebra.adjoin_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgeb
ra`。
形式化陈述：adjoin_mono {s t : Set A} (H : s subseteq t) : adjoin R s <= adjoin R t
参数：H : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `NonUnitalStarAlgebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemirin
g R] [inst_1 : StarRing R] [inst_2 : NonUnitalSemiring A]   [inst_3 : StarRing A
] [inst_4 : _…
-/
theorem adjoin_mono {s t : Set A} (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
  NonUnitalStarAlgebra.gc.monotone_l H

@[simp]
/-
**NonUnitalStarAlgebra.adjoin_eq** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalStarAlgebra
`。
形式化陈述：adjoin_eq (s : NonUnitalStarSubalgebra R A) : adjoin R (s : Set A) = s
参数：s : NonUnitalStarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `NonUnitalStarAlgebra.adjoin_le`：adjoin_le {S : NonUnitalStarSubalgebra R
 A} {s : Set A} (hs : s subseteq S) : adjoin R s <= S
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `NonUnitalStarAlgebra.subset_adjoin`：subset_adjoin (s : Set A) : s subset
eq adjoin R s
-/
lemma adjoin_eq (s : NonUnitalStarSubalgebra R A) : adjoin R (s : Set A) = s :=
  le_antisymm (adjoin_le le_rfl) (subset_adjoin R (s : Set A))
/-
**NonUnitalStarAlgebra.adjoin_eq_span** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalStarAl
gebra`。
形式化陈述：adjoin_eq_span (s : Set A) : (adjoin R s).toSubmodule = Submodule.span R (
Subsemigroup.closure (s union star s))
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalStarAlgebra.adjoin_toNonUnitalSubalgebra`：adjoin_toNonUnitalSub
algebra (s : Set A) : (adjoin R s).toNonUnitalSubalgebra = NonUnitalAlgebra.adjo
in R (s union star s)
· 使用引理 `NonUnitalAlgebra.adjoin_eq_span`：adjoin_eq_span (s : Set A) : (adjoin R 
s).toSubmodule = span R (Subsemigroup.closure s)
-/
lemma adjoin_eq_span (s : Set A) :
    (adjoin R s).toSubmodule = Submodule.span R (Subsemigroup.closure (s ∪ star s)) := by
  rw [adjoin_toNonUnitalSubalgebra, NonUnitalAlgebra.adjoin_eq_span]

@[simp]
/-
**NonUnitalStarAlgebra.span_eq_toSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalS
tarAlgebra`。
形式化陈述：span_eq_toSubmodule {R} [CommSemiring R] [Module R A] (s : NonUnitalStarSu
balgebra R A) : Submodule.span R (s : Set A) = s.toSubmodule
参数：s : NonUnitalStarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.coe_span_eq_self`：coe_span_eq_self [SetLike S M] [AddSubmonoid
Class S M] [SMulMemClass S R M] (s : S) : (span R (s : Set M) : Set M) = s
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma span_eq_toSubmodule {R} [CommSemiring R] [Module R A] (s : NonUnitalStarSubalgebra R A) :
    Submodule.span R (s : Set A) = s.toSubmodule := by
  simp [SetLike.ext'_iff, Submodule.coe_span_eq_self]
/-
**NonUnitalStarAlgebra._root_.NonUnitalSubalgebra.starClosure_eq_adjoin** 是 Math
lib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NonUnitalSubalgebra.starClosure_eq_adjoin (S : NonUnitalSubalgebra R A) :
    S.starClosure = adjoin R (S : Set A) :=
  le_antisymm (NonUnitalSubalgebra.starClosure_le_iff.2 <| subset_adjoin R (S : Set A))
    (adjoin_le (le_sup_left : S ≤ S ⊔ star S))
/-
**NonUnitalStarAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (NonUnitalStarSubalgebra R A) :=
  GaloisInsertion.liftCompleteLattice NonUnitalStarAlgebra.gi

@[simp, norm_cast]
/-
**NonUnitalStarAlgebra.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：coe_top : ((⊤ : NonUnitalStarSubalgebra R A) : Set A) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : NonUnitalStarSubalgebra R A) : Set A) = Set.univ :=
  rfl

@[simp]
/-
**NonUnitalStarAlgebra.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：mem_top {x : A} : x in (⊤ : NonUnitalStarSubalgebra R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top {x : A} : x ∈ (⊤ : NonUnitalStarSubalgebra R A) :=
  Set.mem_univ x

@[simp]
/-
**NonUnitalStarAlgebra.top_toNonUnitalSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalStarAlgebra`。
形式化陈述：top_toNonUnitalSubalgebra : (⊤ : NonUnitalStarSubalgebra R A).toNonUnitalS
ubalgebra = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.ext`：ext {S T : NonUnitalSubalgebra R A} (h : forall
 x : A, x in S ↔ x in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem top_toNonUnitalSubalgebra :
    (⊤ : NonUnitalStarSubalgebra R A).toNonUnitalSubalgebra = ⊤ := by ext; simp

@[simp]
/-
**NonUnitalStarAlgebra.toNonUnitalSubalgebra_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `N
onUnitalStarAlgebra`。
形式化陈述：toNonUnitalSubalgebra_eq_top {S : NonUnitalStarSubalgebra R A} : S.toNonUn
italSubalgebra = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `NonUnitalStarSubalgebra.toNonUnitalSubalgebra_injective`：toNonUnitalSuba
lgebra_injective : Function.Injective (toNonUnitalSubalgebra : NonUnitalStarSuba
lgebra R A -> NonUnitalSubalgebra R A)
· 使用定理 `NonUnitalStarAlgebra.top_toNonUnitalSubalgebra`：top_toNonUnitalSubalgebr
a : (⊤ : NonUnitalStarSubalgebra R A).toNonUnitalSubalgebra = ⊤
-/
theorem toNonUnitalSubalgebra_eq_top {S : NonUnitalStarSubalgebra R A} :
    S.toNonUnitalSubalgebra = ⊤ ↔ S = ⊤ :=
  NonUnitalStarSubalgebra.toNonUnitalSubalgebra_injective.eq_iff' top_toNonUnitalSubalgebra
/-
**NonUnitalStarAlgebra.mem_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlge
bra`。
形式化陈述：mem_sup_left {S T : NonUnitalStarSubalgebra R A} : forall {x : A}, x in S 
-> x in S ⊔ T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem mem_sup_left {S T : NonUnitalStarSubalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T := by
  rw [← SetLike.le_def]
  exact le_sup_left
/-
**NonUnitalStarAlgebra.mem_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlg
ebra`。
形式化陈述：mem_sup_right {S T : NonUnitalStarSubalgebra R A} : forall {x : A}, x in T
 -> x in S ⊔ T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem mem_sup_right {S T : NonUnitalStarSubalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T := by
  rw [← SetLike.le_def]
  exact le_sup_right
/-
**NonUnitalStarAlgebra.mul_mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgeb
ra`。
形式化陈述：mul_mem_sup {S T : NonUnitalStarSubalgebra R A} {x y : A} (hx : x in S) (h
y : y in T) : x * y in S ⊔ T
参数：hx : x in S；hy : y in T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `NonUnitalStarAlgebra.mem_sup_left`：mem_sup_left {S T : NonUnitalStarSuba
lgebra R A} : forall {x : A}, x in S -> x in S ⊔ T
· 使用定理 `NonUnitalStarAlgebra.mem_sup_right`：mem_sup_right {S T : NonUnitalStarSu
balgebra R A} : forall {x : A}, x in T -> x in S ⊔ T
-/
theorem mul_mem_sup {S T : NonUnitalStarSubalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
    x * y ∈ S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)
/-
**NonUnitalStarAlgebra.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：map_sup [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : 
F) (S T : NonUnitalStarSubalgebra R A) : ((S ⊔ T).map f : NonUnitalStarSubalgebr
a R B) = S.map f ⊔ T.map f
参数：f : F；S T : NonUnitalStarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `NonUnitalStarSubalgebra.gc_map_comap`：gc_map_comap (f : F) : GaloisConne
ction (map f) (comap f)
-/
theorem map_sup [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F)
    (S T : NonUnitalStarSubalgebra R A) :
    ((S ⊔ T).map f : NonUnitalStarSubalgebra R B) = S.map f ⊔ T.map f :=
  (NonUnitalStarSubalgebra.gc_map_comap f).l_sup
/-
**NonUnitalStarAlgebra.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：map_inf [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : 
F) (hf : Function.Injective f) (S T : NonUnitalStarSubalgebra R A) : ((S ⊓ T).ma
p f : NonUnitalStarSubalgebra R B) = S.map f ⊓ T.map f
参数：f : F；hf : Function.Injective f；S T : NonUnitalStarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
-/
theorem map_inf [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F)
    (hf : Function.Injective f) (S T : NonUnitalStarSubalgebra R A) :
    ((S ⊓ T).map f : NonUnitalStarSubalgebra R B) = S.map f ⊓ T.map f :=
  SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]
/-
**NonUnitalStarAlgebra.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：coe_inf (S T : NonUnitalStarSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Se
t A) inter T
参数：S T : NonUnitalStarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (S T : NonUnitalStarSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Set A) ∩ T :=
  rfl

@[simp]
/-
**NonUnitalStarAlgebra.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：mem_inf {S T : NonUnitalStarSubalgebra R A} {x : A} : x in S ⊓ T ↔ x in S 
∧ x in T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {S T : NonUnitalStarSubalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

@[simp]
/-
**NonUnitalStarAlgebra.inf_toNonUnitalSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalStarAlgebra`。
形式化陈述：inf_toNonUnitalSubalgebra (S T : NonUnitalStarSubalgebra R A) : (S ⊓ T).to
NonUnitalSubalgebra = S.toNonUnitalSubalgebra ⊓ T.toNonUnitalSubalgebra
参数：S T : NonUnitalStarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalStarAlgebra.coe_inf`：coe_inf (S T : NonUnitalStarSubalgebra R A
) : (↑(S ⊓ T) : Set A) = (S : Set A) inter T
-/
theorem inf_toNonUnitalSubalgebra (S T : NonUnitalStarSubalgebra R A) :
    (S ⊓ T).toNonUnitalSubalgebra = S.toNonUnitalSubalgebra ⊓ T.toNonUnitalSubalgebra :=
  SetLike.coe_injective <| coe_inf _ _
  -- it's a bit surprising `rfl` fails here.

@[simp, norm_cast]
/-
**NonUnitalStarAlgebra.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`
。
形式化陈述：coe_sInf (S : Set (NonUnitalStarSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂
 s in S, ↑s
参数：S : Set (NonUnitalStarSubalgebra R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
s : Set β} {f : β → α}, sInf (f '' s) = ⨅ a ∈ s, f a
-/
theorem coe_sInf (S : Set (NonUnitalStarSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s :=
  sInf_image

@[simp]
/-
**NonUnitalStarAlgebra.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`
。
形式化陈述：mem_sInf {S : Set (NonUnitalStarSubalgebra R A)} {x : A} : x in sInf S ↔ f
orall p in S, x in p
参数：NonUnitalStarSubalgebra R A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NonUnitalStarAlgebra.coe_sInf`：coe_sInf (S : Set (NonUnitalStarSubalgebr
a R A)) : (↑(sInf S) : Set A) = ⋂ s in S, ↑s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sInf {S : Set (NonUnitalStarSubalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]
/-
**NonUnitalStarAlgebra.sInf_toNonUnitalSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Non
UnitalStarAlgebra`。
形式化陈述：sInf_toNonUnitalSubalgebra (S : Set (NonUnitalStarSubalgebra R A)) : (sInf
 S).toNonUnitalSubalgebra = sInf (NonUnitalStarSubalgebra.toNonUnitalSubalgebra 
'' S)
参数：S : Set (NonUnitalStarSubalgebra R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalStarAlgebra.coe_sInf`：coe_sInf (S : Set (NonUnitalStarSubalgebr
a R A)) : (↑(sInf S) : Set A) = ⋂ s in S, ↑s
· 使用定理 `NonUnitalAlgebra.coe_sInf`：coe_sInf (S : Set (NonUnitalSubalgebra R A)) 
: (↑(sInf S) : Set A) = ⋂ s in S, ↑s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_and'`：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iInter_iInter_eq_right`：iInter_iInter_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋂ (x) (h : b = x), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInf_toNonUnitalSubalgebra (S : Set (NonUnitalStarSubalgebra R A)) :
    (sInf S).toNonUnitalSubalgebra = sInf (NonUnitalStarSubalgebra.toNonUnitalSubalgebra '' S) :=
  SetLike.coe_injective <| by simp

@[simp, norm_cast]
/-
**NonUnitalStarAlgebra.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`
。
形式化陈述：coe_iInf {ι : Sort*} {S : ι -> NonUnitalStarSubalgebra R A} : (↑(⨅ i, S i)
 : Set A) = ⋂ i, S i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalStarAlgebra.coe_sInf`：coe_sInf (S : Set (NonUnitalStarSubalgebr
a R A)) : (↑(sInf S) : Set A) = ⋂ s in S, ↑s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf {ι : Sort*} {S : ι → NonUnitalStarSubalgebra R A} :
    (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by simp [iInf]

@[simp]
/-
**NonUnitalStarAlgebra.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`
。
形式化陈述：mem_iInf {ι : Sort*} {S : ι -> NonUnitalStarSubalgebra R A} {x : A} : x in
 ⨅ i, S i ↔ forall i, x in S i
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
theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalStarSubalgebra R A} {x : A} :
    x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_mem_range]
/-
**NonUnitalStarAlgebra.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`
。
形式化陈述：map_iInf {ι : Sort*} [Nonempty ι] [IsScalarTower R B B] [SMulCommClass R B
 B] [StarModule R B] (f : F) (hf : Function.Injective f) (S : ι -> NonUnitalStar
Subalgebra R A) : ((⨅ i, S i).map f : NonUnitalStarSubalgebra R B) = ⨅ i, (S i).
map f
参数：f : F；hf : Function.Injective f；S : ι -> NonUnitalStarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalStarAlgebra.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> NonUnitalS
tarSubalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
-/
theorem map_iInf {ι : Sort*} [Nonempty ι]
    [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F)
    (hf : Function.Injective f) (S : ι → NonUnitalStarSubalgebra R A) :
    ((⨅ i, S i).map f : NonUnitalStarSubalgebra R B) = ⨅ i, (S i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ S)

@[simp]
/-
**NonUnitalStarAlgebra.iInf_toNonUnitalSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Non
UnitalStarAlgebra`。
形式化陈述：iInf_toNonUnitalSubalgebra {ι : Sort*} (S : ι -> NonUnitalStarSubalgebra R
 A) : (⨅ i, S i).toNonUnitalSubalgebra = ⨅ i, (S i).toNonUnitalSubalgebra
参数：S : ι -> NonUnitalStarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalStarAlgebra.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> NonUnitalS
tarSubalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i
· 使用定理 `NonUnitalAlgebra.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> NonUnitalSubal
gebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInf_toNonUnitalSubalgebra {ι : Sort*} (S : ι → NonUnitalStarSubalgebra R A) :
    (⨅ i, S i).toNonUnitalSubalgebra = ⨅ i, (S i).toNonUnitalSubalgebra :=
  SetLike.coe_injective <| by simp
/-
**NonUnitalStarAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (NonUnitalStarSubalgebra R A) :=
  ⟨⊥⟩
/-
**NonUnitalStarAlgebra.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：mem_bot {x : A} : x in (⊥ : NonUnitalStarSubalgebra R A) ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.star_empty`：star_empty [Star α] : (∅ : Set α)⋆ = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `NonUnitalAlgebra.adjoin_empty`：adjoin_empty : adjoin R (∅ : Set A) = ⊥
· 使用定理 `NonUnitalAlgebra.mem_bot`：mem_bot {x : A} : x in (⊥ : NonUnitalSubalgebr
a R A) ↔ x = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_bot {x : A} : x ∈ (⊥ : NonUnitalStarSubalgebra R A) ↔ x = 0 :=
  show x ∈ NonUnitalAlgebra.adjoin R (∅ ∪ star ∅ : Set A) ↔ x = 0 by
    rw [Set.star_empty, Set.union_empty, NonUnitalAlgebra.adjoin_empty, NonUnitalAlgebra.mem_bot]
/-
**NonUnitalStarAlgebra.toNonUnitalSubalgebra_bot** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalStarAlgebra`。
形式化陈述：toNonUnitalSubalgebra_bot : (⊥ : NonUnitalStarSubalgebra R A).toNonUnitalS
ubalgebra = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.ext`：ext {S T : NonUnitalSubalgebra R A} (h : forall
 x : A, x in S ↔ x in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toNonUnitalSubalgebra_bot :
    (⊥ : NonUnitalStarSubalgebra R A).toNonUnitalSubalgebra = ⊥ := by
  ext x
  simp only [mem_bot, NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra, NonUnitalAlgebra.mem_bot]

@[simp, norm_cast]
/-
**NonUnitalStarAlgebra.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：coe_bot : ((⊥ : NonUnitalStarSubalgebra R A) : Set A) = {0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
-/
theorem coe_bot : ((⊥ : NonUnitalStarSubalgebra R A) : Set A) = {0} := by
  simp only [Set.ext_iff, NonUnitalStarAlgebra.mem_bot, SetLike.mem_coe, Set.mem_singleton_iff,
    forall_const]
/-
**NonUnitalStarAlgebra.eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebr
a`。
形式化陈述：eq_top_iff {S : NonUnitalStarSubalgebra R A} : S = ⊤ ↔ forall x : A, x in 
S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalStarAlgebra.mem_top`：mem_top {x : A} : x in (⊤ : NonUnitalStarS
ubalgebra R A)
· 使用定理 `NonUnitalStarSubalgebra.ext`：ext {S T : NonUnitalStarSubalgebra R A} (h 
: forall x : A, x in S ↔ x in T) : S = T
-/
theorem eq_top_iff {S : NonUnitalStarSubalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h]; exact mem_top,
    fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

@[simp]
/-
**NonUnitalStarAlgebra.range_id** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`
。
形式化陈述：range_id : NonUnitalStarAlgHom.range (NonUnitalStarAlgHom.id R A) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `NonUnitalStarAlgHom.instStarHomClass`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 
: DistribMulAction R A] [i…
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
-/
theorem range_id : NonUnitalStarAlgHom.range (NonUnitalStarAlgHom.id R A) = ⊤ :=
  SetLike.coe_injective Set.range_id

@[simp]
/-
**NonUnitalStarAlgebra.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：map_bot [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : 
F) : (⊥ : NonUnitalStarSubalgebra R A).map f = ⊥
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalStarAlgebra.coe_bot`：coe_bot : ((⊥ : NonUnitalStarSubalgebra R 
A) : Set A) = {0}
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_bot [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F) :
    (⊥ : NonUnitalStarSubalgebra R A).map f = ⊥ :=
  SetLike.coe_injective <| by simp [NonUnitalStarSubalgebra.coe_map]

@[simp]
/-
**NonUnitalStarAlgebra.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra
`。
形式化陈述：comap_top [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f 
: F) : (⊤ : NonUnitalStarSubalgebra R B).comap f = ⊤
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalStarAlgebra.eq_top_iff`：eq_top_iff {S : NonUnitalStarSubalgebra
 R A} : S = ⊤ ↔ forall x : A, x in S
· 使用定理 `NonUnitalStarAlgebra.mem_top`：mem_top {x : A} : x in (⊤ : NonUnitalStarS
ubalgebra R A)
-/
theorem comap_top [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] (f : F) :
    (⊤ : NonUnitalStarSubalgebra R B).comap f = ⊤ :=
  eq_top_iff.2 fun _x => mem_top

/-- `NonUnitalStarAlgHom` to `⊤ : NonUnitalStarSubalgebra R A`. -/
/-
**NonUnitalStarAlgebra.toTop** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：toTop : A ->⋆ₙₐ[R] (⊤ : NonUnitalStarSubalgebra R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonUnitalStarAlgHom` to `⊤ : NonUnitalStarSubalgebra R A`.
-/
def toTop : A →⋆ₙₐ[R] (⊤ : NonUnitalStarSubalgebra R A) :=
  NonUnitalStarAlgHom.codRestrict (NonUnitalStarAlgHom.id R A) ⊤ fun _ => mem_top

end StarSubAlgebraA

/-
**NonUnitalStarAlgebra.range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlge
bra`。
形式化陈述：range_eq_top [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B] 
(f : F) : NonUnitalStarAlgHom.range f = (⊤ : NonUnitalStarSubalgebra R B) ↔ Func
tion.Surjective f
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgebra.eq_top_iff`：eq_top_iff {S : NonUnitalStarSubalgebra
 R A} : S = ⊤ ↔ forall x : A, x in S
-/
theorem range_eq_top [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]
    (f : F) : NonUnitalStarAlgHom.range f = (⊤ : NonUnitalStarSubalgebra R B) ↔
      Function.Surjective f :=
  NonUnitalStarAlgebra.eq_top_iff

@[simp]
/-
**NonUnitalStarAlgebra.map_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：map_top [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] (f : 
F) : (⊤ : NonUnitalStarSubalgebra R A).map f = NonUnitalStarAlgHom.range f
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
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
The map `S → T` when `S` is a non-unital star subalgebra contained in the non-unital star
algebra `T`.

This is the non-unital star subalgebra version of `Submodule.inclusion`, or
`NonUnitalSubalgebra.inclusion` -/
/-
**NonUnitalStarSubalgebra.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarSuba
lgebra`。
形式化陈述：inclusion {S T : NonUnitalStarSubalgebra R A} (h : S <= T) : S ->⋆ₙₐ[R] T 
where toNonUnitalAlgHom
参数：h : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `S → T` when `S` is a non-unital star subalgebra contained in the non-un
ital star
algebra `T`.

This is the non-unital star subalgebra version of `Submodule.inclusion`, or
`NonUnitalSubalgebra.inclusion`
-/
def inclusion {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) : S →⋆ₙₐ[R] T where
  toNonUnitalAlgHom := NonUnitalSubalgebra.inclusion h
  map_star' _ := rfl
/-
**NonUnitalStarSubalgebra.inclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alStarSubalgebra`。
形式化陈述：inclusion_injective {S T : NonUnitalStarSubalgebra R A} (h : S <= T) : Fun
ction.Injective (inclusion h)
参数：h : S <= T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.mk.inj`：∀ {α : Sort u} {p : α → Prop} {val : α} {property : p va
l} {val_1 : α} {property_1 : p val_1},   ⟨val, property⟩ = ⟨val_1, property_1⟩ →
 val…
-/
theorem inclusion_injective {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) :
    Function.Injective (inclusion h) :=
  fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]
/-
**NonUnitalStarSubalgebra.inclusion_self** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSta
rSubalgebra`。
形式化陈述：inclusion_self {S : NonUnitalStarSubalgebra R A} : inclusion (le_refl S) =
 NonUnitalAlgHom.id R S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHom.ext`：ext {f g : A ->ₛₙₐ[φ] B} (h : forall x, f x = g x) 
: f = g
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem inclusion_self {S : NonUnitalStarSubalgebra R A} :
    inclusion (le_refl S) = NonUnitalAlgHom.id R S :=
  NonUnitalAlgHom.ext fun _x => Subtype.ext rfl

@[simp]
/-
**NonUnitalStarSubalgebra.inclusion_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarS
ubalgebra`。
形式化陈述：inclusion_mk {S T : NonUnitalStarSubalgebra R A} (h : S <= T) (x : A) (hx 
: x in S) : inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩
参数：h : S <= T；x : A；hx : x in S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_mk {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) (x : A) (hx : x ∈ S) :
    inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl
/-
**NonUnitalStarSubalgebra.inclusion_right** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSt
arSubalgebra`。
形式化陈述：inclusion_right {S T : NonUnitalStarSubalgebra R A} (h : S <= T) (x : T) (
m : (x : A) in S) : inclusion h ⟨x, m⟩ = x
参数：h : S <= T；x : T；m : (x : A) in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem inclusion_right {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) (x : T) (m : (x : A) ∈ S) :
    inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl

@[simp]
/-
**NonUnitalStarSubalgebra.inclusion_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alStarSubalgebra`。
形式化陈述：inclusion_inclusion {S T U : NonUnitalStarSubalgebra R A} (hst : S <= T) (
htu : T <= U) (x : S) : inclusion htu (inclusion hst x) = inclusion (le_trans hs
t htu) x
参数：hst : S <= T；htu : T <= U；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem inclusion_inclusion {S T U : NonUnitalStarSubalgebra R A} (hst : S ≤ T) (htu : T ≤ U)
    (x : S) : inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
  Subtype.ext rfl

@[simp]
/-
**NonUnitalStarSubalgebra.val_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStar
Subalgebra`。
形式化陈述：val_inclusion {S T : NonUnitalStarSubalgebra R A} (h : S <= T) (s : S) : (
inclusion h s : A) = s
参数：h : S <= T；s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_inclusion {S T : NonUnitalStarSubalgebra R A} (h : S ≤ T) (s : S) :
    (inclusion h s : A) = s :=
  rfl

variable [StarRing R]
variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]
/-
**NonUnitalStarSubalgebra._root_.NonUnitalStarAlgHom.map_adjoin** 是 Mathlib 中的一个
引理，位于命名空间 `NonUnitalStarSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.NonUnitalStarAlgHom.map_adjoin (f : F) (s : Set A) :
    map f (adjoin R s) = adjoin R (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) NonUnitalStarAlgebra.gi.gc
    NonUnitalStarAlgebra.gi.gc fun _t => rfl

@[simp]
/-
**NonUnitalStarSubalgebra._root_.NonUnitalStarAlgHom.map_adjoin_singleton** 是 Ma
thlib 中的一个引理，位于命名空间 `NonUnitalStarSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.NonUnitalStarAlgHom.map_adjoin_singleton (f : F) (x : A) :
    map f (adjoin R {x}) = adjoin R {f x} := by
  simp [NonUnitalStarAlgHom.map_adjoin]
/-
**NonUnitalStarSubalgebra.subsingleton_of_subsingleton** 是 Mathlib 中的一个实例，位于命名空间
 `NonUnitalStarSubalgebra`。
形式化陈述：subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (NonUnitalSta
rSubalgebra R A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.ext`：ext {S T : NonUnitalStarSubalgebra R A} (h 
: forall x : A, x in S ↔ x in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
instance subsingleton_of_subsingleton [Subsingleton A] :
    Subsingleton (NonUnitalStarSubalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩
/-
**NonUnitalStarSubalgebra._root_.NonUnitalStarAlgHom.subsingleton** 是 Mathlib 中的
一个实例，位于命名空间 `NonUnitalStarSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.NonUnitalStarAlgHom.subsingleton [Subsingleton (NonUnitalStarSubalgebra R A)] :
    Subsingleton (A →⋆ₙₐ[R] B) :=
  ⟨fun f g => NonUnitalStarAlgHom.ext fun a =>
    have : a ∈ (⊥ : NonUnitalStarSubalgebra R A) :=
      Subsingleton.elim (⊤ : NonUnitalStarSubalgebra R A) ⊥ ▸ mem_top
    (mem_bot.mp this).symm ▸ (map_zero f).trans (map_zero g).symm⟩

end StarSubalgebra

/-
**NonUnitalStarSubalgebra.range_val** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSuba
lgebra`。
形式化陈述：range_val : NonUnitalStarAlgHom.range (NonUnitalStarSubalgebraClass.subtyp
e S) = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.ext`：ext {S T : NonUnitalStarSubalgebra R A} (h 
: forall x : A, x in S ↔ x in T) : S = T
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `NonUnitalStarAlgHom.instStarHomClass`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 
: DistribMulAction R A] [i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NonUnitalStarAlgHom.coe_range`：coe_range (φ : F) : ((NonUnitalStarAlgHom
.range φ : NonUnitalStarSubalgebra R B) : Set B) = Set.range (φ : A -> B)
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
theorem range_val : NonUnitalStarAlgHom.range (NonUnitalStarSubalgebraClass.subtype S) = S :=
  ext <| Set.ext_iff.1 <|
    (NonUnitalStarAlgHom.coe_range (NonUnitalStarSubalgebraClass.subtype S)).trans Subtype.range_val

section Prod

variable (S₁ : NonUnitalStarSubalgebra R B)

/-- The product of two non-unital star subalgebras is a non-unital star subalgebra. -/
/-
**NonUnitalStarSubalgebra.prod** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarSubalgebr
a`。
形式化陈述：prod : NonUnitalStarSubalgebra R (A × B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two non-unital star subalgebras is a non-unital star subalgebra.
-/
def prod : NonUnitalStarSubalgebra R (A × B) :=
  { S.toNonUnitalSubalgebra.prod S₁.toNonUnitalSubalgebra with
    carrier := S ×ˢ S₁
    star_mem' := fun hx => ⟨star_mem hx.1, star_mem hx.2⟩ }

@[simp, norm_cast]
/-
**NonUnitalStarSubalgebra.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubal
gebra`。
形式化陈述：coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ S₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ S₁ :=
  rfl
/-
**NonUnitalStarSubalgebra.prod_toNonUnitalSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `
NonUnitalStarSubalgebra`。
形式化陈述：prod_toNonUnitalSubalgebra : (S.prod S₁).toNonUnitalSubalgebra = S.toNonUn
italSubalgebra.prod S₁.toNonUnitalSubalgebra
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_toNonUnitalSubalgebra :
    (S.prod S₁).toNonUnitalSubalgebra = S.toNonUnitalSubalgebra.prod S₁.toNonUnitalSubalgebra :=
  rfl

@[simp]
/-
**NonUnitalStarSubalgebra.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubal
gebra`。
形式化陈述：mem_prod {S : NonUnitalStarSubalgebra R A} {S₁ : NonUnitalStarSubalgebra R
 B} {x : A × B} : x in prod S S₁ ↔ x.1 in S ∧ x.2 in S₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_prod`：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
-/
theorem mem_prod {S : NonUnitalStarSubalgebra R A} {S₁ : NonUnitalStarSubalgebra R B} {x : A × B} :
    x ∈ prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ :=
  Set.mem_prod
/-
**NonUnitalStarSubalgebra.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSuba
lgebra`。
形式化陈述：prod_mono {S T : NonUnitalStarSubalgebra R A} {S₁ T₁ : NonUnitalStarSubalg
ebra R B} : S <= T -> S₁ <= T₁ -> prod S S₁ <= prod T T₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono {S T : NonUnitalStarSubalgebra R A} {S₁ T₁ : NonUnitalStarSubalgebra R B} :
    S ≤ T → S₁ ≤ T₁ → prod S S₁ ≤ prod T T₁ :=
  Set.prod_mono

variable [StarRing R]
variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]

@[simp]
/-
**NonUnitalStarSubalgebra.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSubal
gebra`。
形式化陈述：prod_top : (prod ⊤ ⊤ : NonUnitalStarSubalgebra R (A × B)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.ext`：ext {S T : NonUnitalStarSubalgebra R A} (h 
: forall x : A, x in S ↔ x in T) : S = T
· 使用定理 `Prod.instStarModule`：∀ {R : Type u} {S : Type v} {α : Type w} [inst : SM
ul α R] [inst_1 : SMul α S] [inst_2 : Star α] [inst_3 : Star R]   [inst_4 : Star
 S] [Star…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_top : (prod ⊤ ⊤ : NonUnitalStarSubalgebra R (A × B)) = ⊤ := by ext; simp

@[simp]
/-
**NonUnitalStarSubalgebra.prod_inf_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStar
Subalgebra`。
形式化陈述：prod_inf_prod {S T : NonUnitalStarSubalgebra R A} {S₁ T₁ : NonUnitalStarSu
balgebra R B} : S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Prod.instStarModule`：∀ {R : Type u} {S : Type v} {α : Type w} [inst : SM
ul α R] [inst_1 : SMul α S] [inst_2 : Star α] [inst_3 : Star R]   [inst_4 : Star
 S] [Star…
· 使用定理 `Set.prod_inter_prod`：prod_inter_prod : s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ int
er s₂) ×ˢ (t₁ inter t₂)
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

/-
**NonUnitalStarSubalgebra.coe_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `NonUni
talStarSubalgebra`。
形式化陈述：coe_iSup_of_directed [Nonempty ι] {S : ι -> NonUnitalStarSubalgebra R A} (
dir : Directed (· <= ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A)
参数：dir : Directed (· <= ·) S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalSubalgebra.coe_iSup_of_directed`：coe_iSup_of_directed [Nonempty
 ι] {S : ι -> NonUnitalSubalgebra R A} (dir : Directed (· <= ·) S) : ↑(iSup S) =
 ⋃ i, (S i : Set A)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
-/
theorem coe_iSup_of_directed [Nonempty ι] {S : ι → NonUnitalStarSubalgebra R A}
    (dir : Directed (· ≤ ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A) :=
  let K : NonUnitalStarSubalgebra R A :=
    { __ := NonUnitalSubalgebra.copy _ _ (NonUnitalSubalgebra.coe_iSup_of_directed dir).symm
      star_mem' := fun hx ↦
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, star_mem (s := S i) hi⟩ }
  have : iSup S = K := le_antisymm (iSup_le fun i ↦ le_iSup (fun i ↦ (S i : Set A)) i)
    (Set.iUnion_subset fun _ ↦ le_iSup S _)
  this.symm ▸ rfl
/-
**NonUnitalStarSubalgebra.isMulCommutative_iSup** 是 Mathlib 中的一个定理，位于命名空间 `NonUn
italStarSubalgebra`。
形式化陈述：isMulCommutative_iSup [Nonempty ι] {S : ι -> NonUnitalStarSubalgebra R A} 
[hS : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) : IsMulCommu
tative (⨆ i, S i : NonUnitalStarSubalgebra R A)
参数：S i；dir : Directed (· <= ·) S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalStarSubalgebra.coe_iSup_of_directed`：coe_iSup_of_directed [None
mpty ι] {S : ι -> NonUnitalStarSubalgebra R A} (dir : Directed (· <= ·) S) : ↑(i
Sup S) = ⋃ i, (S i : Set A)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
· 使用定理 `NonUnitalSubsemiring.coe_iSup_of_directed`：coe_iSup_of_directed {ι} [hι 
: Nonempty ι] {S : ι -> NonUnitalSubsemiring R} (hS : Directed (· <= ·) S) : ((⨆
 i, S i : NonUnitalSubsemiring …
· 使用定理 `NonUnitalSubsemiring.isMulCommutative_iSup`：isMulCommutative_iSup {ι : S
ort*} [Nonempty ι] {S : ι -> NonUnitalSubsemiring R} [hS : forall i, IsMulCommut
ative (S i)] (dir : Directed (· …
-/
theorem isMulCommutative_iSup [Nonempty ι] {S : ι → NonUnitalStarSubalgebra R A}
    [hS : ∀ i, IsMulCommutative (S i)] (dir : Directed (· ≤ ·) S) :
    IsMulCommutative (⨆ i, S i : NonUnitalStarSubalgebra R A) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, NonUnitalSubsemiring.coe_iSup_of_directed dir,
    coe_iSup_of_directed dir] using NonUnitalSubsemiring.isMulCommutative_iSup dir
/-
**NonUnitalStarSubalgebra.instIsMulCommutative_iSup** 是 Mathlib 中的一个实例，位于命名空间 `N
onUnitalStarSubalgebra`。
形式化陈述：instIsMulCommutative_iSup [Nonempty ι] [Preorder ι] [IsDirectedOrder ι] {S
 : ι ->o NonUnitalStarSubalgebra R A} [hS : forall i, IsMulCommutative (S i)] : 
IsMulCommutative (⨆ i, S i : NonUnitalStarSubalgebra R A)
参数：S i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.isMulCommutative_iSup`：isMulCommutative_iSup [No
nempty ι] {S : ι -> NonUnitalStarSubalgebra R A} [hS : forall i, IsMulCommutativ
e (S i)] (dir : Directed (· <= ·) S…
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
instance instIsMulCommutative_iSup [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o NonUnitalStarSubalgebra R A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : NonUnitalStarSubalgebra R A) :=
  isMulCommutative_iSup S.monotone.directed_le

set_option backward.isDefEq.respectTransparency false in
/-- Define a non-unital star algebra homomorphism on a directed supremum of non-unital star
subalgebras by defining it on each non-unital star subalgebra, and proving that it agrees on the
intersection of non-unital star subalgebras. -/
/-
**NonUnitalStarSubalgebra.iSupLift** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarSubal
gebra`。
形式化陈述：iSupLift [Nonempty ι] (K : ι -> NonUnitalStarSubalgebra R A) (dir : Direct
ed (· <= ·) K) (f : forall i, K i ->⋆ₙₐ[R] B) (hf : forall (i j : ι) (h : K i <=
 K j), f i = (f j).comp (inclusion h)) (T : NonUnitalStarSubalgebra R A) (hT : T
 = iSup K) : ↥T ->⋆ₙₐ[R] B
参数：K : ι -> NonUnitalStarSubalgebra R A；dir : Directed (· <= ·) K；f : forall i, 
K i ->⋆ₙₐ[R] B；hf : forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusi
on h)；T : NonUnitalStarSubalgebra R A；hT : T = iSup K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a non-unital star algebra homomorphism on a directed supremum of non-unit
al star
subalgebras by defining it on each non-unital star subalgebra, and proving that 
it agrees on the
intersection of non-unital star subalgebras.
-/
noncomputable def iSupLift [Nonempty ι] (K : ι → NonUnitalStarSubalgebra R A)
    (dir : Directed (· ≤ ·) K) (f : ∀ i, K i →⋆ₙₐ[R] B)
    (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
    (T : NonUnitalStarSubalgebra R A) (hT : T = iSup K) : ↥T →⋆ₙₐ[R] B := by
  subst hT
  exact
    { toFun :=
        Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x)
          (fun i j x hxi hxj => by
            let ⟨k, hik, hjk⟩ := dir i j
            rw [hf i k hik, hf j k hjk]
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

variable [Nonempty ι] {K : ι → NonUnitalStarSubalgebra R A} {dir : Directed (· ≤ ·) K}
  {f : ∀ i, K i →⋆ₙₐ[R] B} {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
  {T : NonUnitalStarSubalgebra R A} {hT : T = iSup K}

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**NonUnitalStarSubalgebra.iSupLift_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `NonUnita
lStarSubalgebra`。
形式化陈述：iSupLift_inclusion {i : ι} (x : K i) (h : K i <= T) : iSupLift K dir f hf 
T hT (inclusion h x) = f i x
参数：x : K i；h : K i <= T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnionLift_inclusion`：iUnionLift_inclusion {i : ι} (x : S i) (h : S 
i subseteq T) : iUnionLift S f hf T hT (Set.inclusion h x) = f i x
-/
theorem iSupLift_inclusion {i : ι} (x : K i) (h : K i ≤ T) :
    iSupLift K dir f hf T hT (inclusion h x) = f i x := by
  subst T
  dsimp [iSupLift]
  apply Set.iUnionLift_inclusion
  exact h

@[simp]
/-
**NonUnitalStarSubalgebra.iSupLift_comp_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Non
UnitalStarSubalgebra`。
形式化陈述：iSupLift_comp_inclusion {i : ι} (h : K i <= T) : (iSupLift K dir f hf T hT
).comp (inclusion h) = f i
参数：h : K i <= T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgHom.ext`：ext {f g : A ->⋆ₙₐ[R] B} (h : forall x, f x = g
 x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalStarSubalgebra.iSupLift_inclusion`：iSupLift_inclusion {i : ι} (
x : K i) (h : K i <= T) : iSupLift K dir f hf T hT (inclusion h x) = f i x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSupLift_comp_inclusion {i : ι} (h : K i ≤ T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**NonUnitalStarSubalgebra.iSupLift_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSu
balgebra`。
形式化陈述：iSupLift_mk {i : ι} (x : K i) (hx : (x : A) in T) : iSupLift K dir f hf T 
hT ⟨x, hx⟩ = f i x
参数：x : K i；hx : (x : A) in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnionLift_mk`：iUnionLift_mk {i : ι} (x : S i) (hx : (x : α) in T) :
 iUnionLift S f hf T hT ⟨x, hx⟩ = f i x
-/
theorem iSupLift_mk {i : ι} (x : K i) (hx : (x : A) ∈ T) :
    iSupLift K dir f hf T hT ⟨x, hx⟩ = f i x := by
  subst hT
  dsimp [iSupLift]
  apply Set.iUnionLift_mk

set_option backward.isDefEq.respectTransparency false in
/-
**NonUnitalStarSubalgebra.iSupLift_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSt
arSubalgebra`。
形式化陈述：iSupLift_of_mem {i : ι} (x : T) (hx : (x : A) in K i) : iSupLift K dir f h
f T hT x = f i ⟨x, hx⟩
参数：x : T；hx : (x : A) in K i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnionLift_of_mem`：iUnionLift_of_mem (x : T) {i : ι} (hx : (x : α) i
n S i) : iUnionLift S f hf T hT x = f i ⟨x, hx⟩
-/
theorem iSupLift_of_mem {i : ι} (x : T) (hx : (x : A) ∈ K i) :
    iSupLift K dir f hf T hT x = f i ⟨x, hx⟩ := by
  subst hT
  dsimp [iSupLift]
  apply Set.iUnionLift_of_mem

end iSupLift

section Center

variable (R A)
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The center of a non-unital star algebra is the set of elements which commute with every element.
They form a non-unital star subalgebra. -/
/-
**NonUnitalStarSubalgebra.center** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarSubalge
bra`。
形式化陈述：center : NonUnitalStarSubalgebra R A where toNonUnitalSubalgebra
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a non-unital star algebra is the set of elements which commute wit
h every element.
They form a non-unital star subalgebra.
-/
def center : NonUnitalStarSubalgebra R A where
  toNonUnitalSubalgebra := NonUnitalSubalgebra.center R A
  star_mem' := Set.star_mem_center

@[norm_cast]
/-
**NonUnitalStarSubalgebra.coe_center** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSub
algebra`。
形式化陈述：coe_center : (center R A : Set A) = Set.center A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_center : (center R A : Set A) = Set.center A :=
  rfl

@[simp]
/-
**NonUnitalStarSubalgebra.center_toNonUnitalSubalgebra** 是 Mathlib 中的一个定理，位于命名空间
 `NonUnitalStarSubalgebra`。
形式化陈述：center_toNonUnitalSubalgebra : (center R A).toNonUnitalSubalgebra = NonUni
talSubalgebra.center R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem center_toNonUnitalSubalgebra :
    (center R A).toNonUnitalSubalgebra = NonUnitalSubalgebra.center R A :=
  rfl

@[simp]
/-
**NonUnitalStarSubalgebra.center_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStar
Subalgebra`。
形式化陈述：center_eq_top (A : Type*) [StarRing R] [NonUnitalCommSemiring A] [StarRing
 A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] : 
center R A = ⊤
参数：A : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_eq_univ`：center_eq_univ : center M = univ
-/
theorem center_eq_top (A : Type*) [StarRing R] [NonUnitalCommSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)

variable {R A}
/-
**NonUnitalStarSubalgebra.instNonUnitalCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `N
onUnitalStarSubalgebra`。
形式化陈述：instNonUnitalCommSemiring : NonUnitalCommSemiring (center R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalCommSemiring : NonUnitalCommSemiring (center R A) :=
  fast_instance% NonUnitalSubalgebra.center.instNonUnitalCommSemiring
/-
**NonUnitalStarSubalgebra.instNonUnitalCommRing** 是 Mathlib 中的一个实例，位于命名空间 `NonUn
italStarSubalgebra`。
形式化陈述：instNonUnitalCommRing {A : Type*} [NonUnitalRing A] [StarRing A] [Module R
 A] [IsScalarTower R A A] [SMulCommClass R A A] : NonUnitalCommRing (center R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalCommRing {A : Type*} [NonUnitalRing A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : NonUnitalCommRing (center R A) :=
  fast_instance% NonUnitalSubalgebra.center.instNonUnitalCommRing
/-
**NonUnitalStarSubalgebra.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSta
rSubalgebra`。
形式化陈述：mem_center_iff {a : A} : a in center R A ↔ forall b : A, b * a = a * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.mem_center_iff`：mem_center_iff {z : M} : z in center M ↔ fo
rall g, g * z = z * g
-/
theorem mem_center_iff {a : A} : a ∈ center R A ↔ ∀ b : A, b * a = a * b :=
  Subsemigroup.mem_center_iff
/-
**NonUnitalStarSubalgebra.center_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarSu
balgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 NonUnitalSemiring A] [inst_2 : StarRing A]   [inst_3 : _root_.Module R A] [inst
_4 : NonUnitalSemiring B] [inst_5 : StarRing B] [inst_6 : _root_.Module R B]   [
inst_7 : IsScalarTower R A A] [inst_8 : SMulCommClass R A A] [inst_9 : IsScalarT
ower R B B]   [inst_10 : SMulCommClass R B B],   NonUnitalStarSubalgebra.center 
R (A × B) =     (NonUnitalStarSubalgebra.center R A).prod (NonUnitalStarSubalgeb
ra.center R B)
参数：A × B；NonUnitalStarSubalgebra.center R A；NonUnitalStarSubalgebra.center R B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_prod`：∀ {M : Type u_1} [inst : Mul M] {N : Type u_2} [inst_1 
: Mul N], Set.center (M × N) = Set.center M ×ˢ Set.center N
-/
protected theorem center_prod [IsScalarTower R B B] [SMulCommClass R B B] :
    center R (A × B) = prod (center R A) (center R B) :=
  SetLike.coe_injective Set.center_prod

end Center

section Centralizer

variable (R)
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The centralizer of the star-closure of a set as a non-unital star subalgebra. -/
/-
**NonUnitalStarSubalgebra.centralizer** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarSu
balgebra`。
形式化陈述：centralizer (s : Set A) : NonUnitalStarSubalgebra R A
参数：s : Set A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The centralizer of the star-closure of a set as a non-unital star subalgebra.
-/
def centralizer (s : Set A) : NonUnitalStarSubalgebra R A :=
  { NonUnitalSubalgebra.centralizer R (s ∪ star s) with
    star_mem' := Set.star_mem_centralizer }

@[simp, norm_cast]
/-
**NonUnitalStarSubalgebra.coe_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSt
arSubalgebra`。
形式化陈述：coe_centralizer (s : Set A) : (centralizer R s : Set A) = (s union star s)
.centralizer
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = (s ∪ star s).centralizer :=
  rfl
/-
**NonUnitalStarSubalgebra.mem_centralizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alStarSubalgebra`。
形式化陈述：mem_centralizer_iff {s : Set A} {z : A} : z in centralizer R s ↔ forall g 
in s, g * z = z * g ∧ star g * z = z * star g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.star_mem_star`：star_mem_star [InvolutiveStar α] : a⋆ in s⋆ ↔ a in s
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
theorem mem_centralizer_iff {s : Set A} {z : A} :
    z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g ∧ star g * z = z * star g := by
  change (∀ g ∈ s ∪ star s, g * z = z * g) ↔ ∀ g ∈ s, g * z = z * g ∧ star g * z = z * star g
  simp only [Set.mem_union, or_imp, forall_and, and_congr_right_iff]
  exact fun _ =>
    ⟨fun hz a ha => hz _ (Set.star_mem_star.mpr ha), fun hz a ha => star_star a ▸ hz _ ha⟩
/-
**NonUnitalStarSubalgebra.centralizer_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSta
rSubalgebra`。
形式化陈述：centralizer_le (s t : Set A) (h : s subseteq t) : centralizer R t <= centr
alizer R s
参数：s t : Set A；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.centralizer_subset`：centralizer_subset (h : S subseteq T) : centrali
zer T subseteq centralizer S
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  Set.centralizer_subset (Set.union_subset_union h <| Set.preimage_mono h)

@[simp]
/-
**NonUnitalStarSubalgebra.centralizer_univ** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalS
tarSubalgebra`。
形式化陈述：centralizer_univ : centralizer R Set.univ = center R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalStarSubalgebra.coe_centralizer`：coe_centralizer (s : Set A) : (
centralizer R s : Set A) = (s union star s).centralizer
· 使用定理 `Set.univ_union`：univ_union (s : Set α) : univ union s = univ
· 使用定理 `NonUnitalStarSubalgebra.coe_center`：coe_center : (center R A : Set A) = 
Set.center A
· 使用引理 `Set.centralizer_univ`：centralizer_univ : centralizer univ = center M
-/
theorem centralizer_univ : centralizer R Set.univ = center R A :=
  SetLike.ext' <| by rw [coe_centralizer, Set.univ_union, coe_center, Set.centralizer_univ]
/-
**NonUnitalStarSubalgebra.centralizer_toNonUnitalSubalgebra** 是 Mathlib 中的一个定理，位
于命名空间 `NonUnitalStarSubalgebra`。
形式化陈述：centralizer_toNonUnitalSubalgebra (s : Set A) : (centralizer R s).toNonUni
talSubalgebra = NonUnitalSubalgebra.centralizer R (s union star s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem centralizer_toNonUnitalSubalgebra (s : Set A) :
    (centralizer R s).toNonUnitalSubalgebra = NonUnitalSubalgebra.centralizer R (s ∪ star s) :=
  rfl
/-
**NonUnitalStarSubalgebra.coe_centralizer_centralizer** 是 Mathlib 中的一个定理，位于命名空间 
`NonUnitalStarSubalgebra`。
形式化陈述：coe_centralizer_centralizer (s : Set A) : (centralizer R (centralizer R s 
: Set A)) = (s union star s).centralizer.centralizer
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalStarSubalgebra.coe_centralizer`：coe_centralizer (s : Set A) : (
centralizer R s : Set A) = (s union star s).centralizer
· 使用引理 `StarMemClass.star_coe_eq`：StarMemClass.star_coe_eq {S α : Type*} [Involu
tiveStar α] [SetLike S α] [StarMemClass S α] (s : S) : star (s : Set α) = s
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
-/
theorem coe_centralizer_centralizer (s : Set A) :
    (centralizer R (centralizer R s : Set A)) = (s ∪ star s).centralizer.centralizer := by
  rw [coe_centralizer, StarMemClass.star_coe_eq, Set.union_self, coe_centralizer]

end Centralizer

end NonUnitalStarSubalgebra

namespace NonUnitalStarAlgebra

open NonUnitalStarSubalgebra

variable [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

variable (R) in
/-
**NonUnitalStarAlgebra.adjoin_le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名
空间 `NonUnitalStarAlgebra`。
形式化陈述：adjoin_le_centralizer_centralizer (s : Set A) : adjoin R s <= centralizer 
R (centralizer R s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff`：toNonUnitalSubalge
bra_le_iff {S₁ S₂ : NonUnitalStarSubalgebra R A} : S₁.toNonUnitalSubalgebra <= S
₂.toNonUnitalSubalgebra ↔ S₁ <= S₂
· 使用定理 `NonUnitalStarSubalgebra.centralizer_toNonUnitalSubalgebra`：centralizer_t
oNonUnitalSubalgebra (s : Set A) : (centralizer R s).toNonUnitalSubalgebra = Non
UnitalSubalgebra.centralizer R (s union star s)
· 使用定理 `NonUnitalStarAlgebra.adjoin_toNonUnitalSubalgebra`：adjoin_toNonUnitalSub
algebra (s : Set A) : (adjoin R s).toNonUnitalSubalgebra = NonUnitalAlgebra.adjo
in R (s union star s)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `StarMemClass.star_coe_eq`：StarMemClass.star_coe_eq {S α : Type*} [Involu
tiveStar α] [SetLike S α] [StarMemClass S α] (s : S) : star (s : Set α) = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `NonUnitalAlgebra.adjoin_le_centralizer_centralizer`：adjoin_le_centralize
r_centralizer (s : Set A) : adjoin R s <= centralizer R (centralizer R s)
-/
lemma adjoin_le_centralizer_centralizer (s : Set A) :
    adjoin R s ≤ centralizer R (centralizer R s) := by
  rw [← toNonUnitalSubalgebra_le_iff, centralizer_toNonUnitalSubalgebra,
    adjoin_toNonUnitalSubalgebra]
  convert! NonUnitalAlgebra.adjoin_le_centralizer_centralizer R (s ∪ star s)
  rw [StarMemClass.star_coe_eq]
  simp
/-
**NonUnitalStarAlgebra.commute_of_mem_adjoin_of_forall_mem_commute** 是 Mathlib 中
的一个引理，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A} (hb : b 
in adjoin R s) (h : forall b in s, Commute a b) (h_star : forall b in s, Commute
 a (star b)) : Commute a b
参数：hb : b in adjoin R s；h : forall b in s, Commute a b；h_star : forall b in s, C
ommute a (star b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NonUnitalAlgebra.commute_of_mem_adjoin_of_forall_mem_commute`：commute_of
_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A} (hb : b in adjoin R s) (
h : forall b in s, Commute a b) : Commute a b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
lemma commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A}
    (hb : b ∈ adjoin R s) (h : ∀ b ∈ s, Commute a b) (h_star : ∀ b ∈ s, Commute a (star b)) :
    Commute a b :=
  NonUnitalAlgebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun b hb ↦
    hb.elim (h b) (by simpa using h_star (star b))
/-
**NonUnitalStarAlgebra.commute_of_mem_adjoin_singleton_of_commute** 是 Mathlib 中的
一个引理，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：commute_of_mem_adjoin_singleton_of_commute {a b c : A} (hc : c in adjoin R
 {b}) (h : Commute a b) (h_star : Commute a (star b)) : Commute a c
参数：hc : c in adjoin R {b}；h : Commute a b；h_star : Commute a (star b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NonUnitalStarAlgebra.commute_of_mem_adjoin_of_forall_mem_commute`：commut
e_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A} (hb : b in adjoin R 
s) (h : forall b in s, Commute a b) (h_star : forall b…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma commute_of_mem_adjoin_singleton_of_commute {a b c : A}
    (hc : c ∈ adjoin R {b}) (h : Commute a b) (h_star : Commute a (star b)) :
    Commute a c :=
  commute_of_mem_adjoin_of_forall_mem_commute hc (by simpa) (by simpa)
/-
**NonUnitalStarAlgebra.commute_of_mem_adjoin_self** 是 Mathlib 中的一个引理，位于命名空间 `Non
UnitalStarAlgebra`。
形式化陈述：commute_of_mem_adjoin_self {a b : A} [IsStarNormal a] (hb : b in adjoin R 
{a}) : Commute a b
参数：hb : b in adjoin R {a}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NonUnitalStarAlgebra.commute_of_mem_adjoin_singleton_of_commute`：commute
_of_mem_adjoin_singleton_of_commute {a b c : A} (hc : c in adjoin R {b}) (h : Co
mmute a b) (h_star : Commute a (star b)) : Commute a …
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isStarNormal_iff`：∀ {R : Type u_1} [inst : Mul R] [inst_1 : Star R] (x :
 R), IsStarNormal x ↔ Commute (star x) x
-/
lemma commute_of_mem_adjoin_self {a b : A} [IsStarNormal a] (hb : b ∈ adjoin R {a}) :
    Commute a b :=
  commute_of_mem_adjoin_singleton_of_commute hb rfl (isStarNormal_iff a |>.mp inferInstance).symm

variable (R) in
/-- If all elements of `s : Set A` commute pairwise and with elements of `star s`, then `adjoin R s`
is commutative. -/
/-
**NonUnitalStarAlgebra.isMulCommutative_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `NonUni
talStarAlgebra`。
形式化陈述：isMulCommutative_adjoin {s : Set A} (hcomm : forall x in s, forall y in s,
 x * y = y * x) (hcomm_star : forall a in s, forall b in s, a * star b = star b 
* a) : IsMulCommutative (adjoin R s)
参数：hcomm : forall x in s, forall y in s, x * y = y * x；hcomm_star : forall a in 
s, forall b in s, a * star b = star b * a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NonUnitalStarAlgebra.adjoin_le_centralizer_centralizer`：adjoin_le_centra
lizer_centralizer (s : Set A) : adjoin R s <= centralizer R (centralizer R s)
· 使用定理 `IsMulCommutative.of_setLike_mul_comm`：∀ {S : Type u_3} {M : Type u_4} [i
nst : SetLike S M] [inst_1 : Mul M] [inst_2 : MulMemClass S M] {s : S},   (∀ a ∈
 s, ∀ b ∈ s, a * b = b * a…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `Set.union_star_self_comm`：Set.union_star_self_comm (hcomm : forall x in 
s, forall y in s, y * x = x * y) (hcomm_star : forall x in s, forall y in s, y *
 star x = star…
· 使用引理 `Set.centralizer_centralizer_comm_of_comm`：centralizer_centralizer_comm_o
f_comm (h_comm : forall x in S, forall y in S, x * y = y * x) : forall x in S.ce
ntralizer.centralizer, forall …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalStarSubalgebra.coe_centralizer_centralizer`：coe_centralizer_cen
tralizer (s : Set A) : (centralizer R (centralizer R s : Set A)) = (s union star
 s).centralizer.centralizer
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p

--- 原说明 ---
If all elements of `s : Set A` commute pairwise and with elements of `star s`, t
hen `adjoin R s`
is commutative.
-/
theorem isMulCommutative_adjoin {s : Set A} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (hcomm_star : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a) :
    IsMulCommutative (adjoin R s) := by
  have := adjoin_le_centralizer_centralizer R s
  refine .of_setLike_mul_comm fun _ h₁ _ h₂ ↦ ?_
  have hcomm : ∀ a ∈ s ∪ star s, ∀ b ∈ s ∪ star s, a * b = b * a := fun a ha b hb ↦
    Set.union_star_self_comm (fun _ ha _ hb ↦ hcomm _ hb _ ha)
      (fun _ ha _ hb ↦ hcomm_star _ hb _ ha) b hb a ha
  apply this at h₁
  apply this at h₂
  rw [← SetLike.mem_coe, coe_centralizer_centralizer] at h₁ h₂
  exact Set.centralizer_centralizer_comm_of_comm hcomm _ h₁ _ h₂

variable (R) in
/-
**NonUnitalStarAlgebra.isMulCommutative_adjoin_singleton** 是 Mathlib 中的一个实例，位于命名
空间 `NonUnitalStarAlgebra`。
形式化陈述：isMulCommutative_adjoin_singleton (a : A) [IsStarNormal a] : IsMulCommutat
ive (adjoin R ({a} : Set A))
参数：a : A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgebra.isMulCommutative_adjoin`：isMulCommutative_adjoin {s
 : Set A} (hcomm : forall x in s, forall y in s, x * y = y * x) (hcomm_star : fo
rall a in s, forall b in s, a * st…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**NonUnitalStarAlgebra.adjoinNonUnitalCommSemiringOfComm** 是 Mathlib 中的一个缩写定义，位于
命名空间 `NonUnitalStarAlgebra`。
形式化陈述：adjoinNonUnitalCommSemiringOfComm {s : Set A} (hcomm : forall a in s, fora
ll b in s, a * b = b * a) (hcomm_star : forall a in s, forall b in s, a * star b
 = star b * a) : NonUnitalCommSemiring (adjoin R s)
参数：hcomm : forall a in s, forall b in s, a * b = b * a；hcomm_star : forall a in 
s, forall b in s, a * star b = star b * a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgebra.isMulCommutative_adjoin`：isMulCommutative_adjoin {s
 : Set A} (hcomm : forall x in s, forall y in s, x * y = y * x) (hcomm_star : fo
rall a in s, forall b in s, a * st…

--- 原说明 ---
If all elements of `s : Set A` commute pairwise and with elements of `star s`, t
hen `adjoin R s`
is a non-unital commutative semiring.

See note [reducible non-instances].
-/
abbrev adjoinNonUnitalCommSemiringOfComm {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    (hcomm_star : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a) :
    NonUnitalCommSemiring (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance
/-
**NonUnitalStarAlgebra.instIsMulCommutative_adjoin** 是 Mathlib 中的一个实例，位于命名空间 `No
nUnitalStarAlgebra`。
形式化陈述：instIsMulCommutative_adjoin {S : Type*} [SetLike S A] [MulMemClass S A] [S
tarMemClass S A] (s : S) [IsMulCommutative s] : IsMulCommutative (adjoin R (s : 
Set A))
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgebra.isMulCommutative_adjoin`：isMulCommutative_adjoin {s
 : Set A} (hcomm : forall x in s, forall y in s, x * y = y * x) (hcomm_star : fo
rall a in s, forall b in s, a * st…
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
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
/-
**NonUnitalStarAlgebra.adjoinNonUnitalCommRingOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间
 `NonUnitalStarAlgebra`。
形式化陈述：adjoinNonUnitalCommRingOfComm (R : Type*) {A : Type*} [CommRing R] [StarRi
ng R] [NonUnitalRing A] [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCom
mClass R A A] [StarModule R A] {s : Set A} (hcomm : forall a in s, forall b in s
, a * b = b * a) (hcomm_star : forall a in s, forall b in s, a * star b = star b
 * a) : NonUnitalCommRing (adjoin R s)
参数：R : Type*；hcomm : forall a in s, forall b in s, a * b = b * a；hcomm_star : fo
rall a in s, forall b in s, a * star b = star b * a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If all elements of `s : Set A` commute pairwise and with elements of `star s`, t
hen `adjoin R s`
is a non-unital commutative ring.

See note [reducible non-instances].
-/
abbrev adjoinNonUnitalCommRingOfComm (R : Type*) {A : Type*} [CommRing R] [StarRing R]
    [NonUnitalRing A] [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [StarModule R A] {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    (hcomm_star : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a) : NonUnitalCommRing (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm hcomm_star
  inferInstance
/-
**NonUnitalStarAlgebra.isMulCommutative_toNonUnitalSubalgebra** 是 Mathlib 中的一个实例
，位于命名空间 `NonUnitalStarAlgebra`。
形式化陈述：isMulCommutative_toNonUnitalSubalgebra (S : NonUnitalStarSubalgebra R A) [
IsMulCommutative S] : IsMulCommutative S.toNonUnitalSubalgebra
参数：S : NonUnitalStarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isMulCommutative_toNonUnitalSubalgebra (S : NonUnitalStarSubalgebra R A)
    [IsMulCommutative S] : IsMulCommutative S.toNonUnitalSubalgebra :=
  ‹IsMulCommutative S›

end NonUnitalStarAlgebra

