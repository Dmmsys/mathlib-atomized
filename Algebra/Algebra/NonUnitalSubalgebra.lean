/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Data.Set.UnionLift
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.NonUnitalSubring.Basic

/-!
# Non-unital Subalgebras over Commutative Semirings

In this file we define `NonUnitalSubalgebra`s and the usual operations on them (`map`, `comap`).

## TODO

* once we have scalar actions by semigroups (as opposed to monoids), implement the action of a
  non-unital subalgebra on the larger algebra.
-/

@[expose] public section

universe u u' v v' w w'

section NonUnitalSubalgebraClass

variable {S R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
variable [SetLike S A] [NonUnitalSubsemiringClass S A] [hSR : SMulMemClass S R A] (s : S)

namespace NonUnitalSubalgebraClass

/-- Embedding of a non-unital subalgebra into the non-unital algebra. -/
/-
**NonUnitalSubalgebraClass.subtype** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubalgebr
aClass`。
形式化陈述：subtype (s : S) : s ->ₙₐ[R] A
参数：s : S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…

--- 原说明 ---
Embedding of a non-unital subalgebra into the non-unital algebra.
-/
def subtype (s : S) : s →ₙₐ[R] A :=
  { NonUnitalSubsemiringClass.subtype s, SMulMemClass.subtype s with toFun := (↑) }

variable {s} in
@[simp]
/-
**NonUnitalSubalgebraClass.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalSub
algebraClass`。
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
**NonUnitalSubalgebraClass.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `NonUnita
lSubalgebraClass`。
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
**NonUnitalSubalgebraClass.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubal
gebraClass`。
形式化陈述：coe_subtype : (subtype s : s -> A) = ((↑) : s -> A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
-/
theorem coe_subtype : (subtype s : s → A) = ((↑) : s → A) :=
  rfl

end NonUnitalSubalgebraClass

end NonUnitalSubalgebraClass

/-- A non-unital subalgebra is a sub(semi)ring that is also a submodule. -/
/-
**NonUnitalSubalgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   (A : Type v) → [inst : CommSemiring R] → [inst_1 : NonUni
talNonAssocSemiring A] → [_root_.Module R A] → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subalgebra is a sub(semi)ring that is also a submodule.
-/
structure NonUnitalSubalgebra (R : Type u) (A : Type v) [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] : Type v
    extends NonUnitalSubsemiring A, Submodule R A

/-- Reinterpret a `NonUnitalSubalgebra` as a `NonUnitalSubsemiring`. -/
add_decl_doc NonUnitalSubalgebra.toNonUnitalSubsemiring

/-- Reinterpret a `NonUnitalSubalgebra` as a `Submodule`. -/
add_decl_doc NonUnitalSubalgebra.toSubmodule

namespace NonUnitalSubalgebra

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

section NonUnitalNonAssocSemiring
variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]
variable [Module R A] [Module R B] [Module R C]

/-
**NonUnitalSubalgebra.toNonUnitalSubsemiring_injective** 是 Mathlib 中的一个引理，位于命名空间
 `NonUnitalSubalgebra`。
形式化陈述：toNonUnitalSubsemiring_injective : (toNonUnitalSubsemiring : NonUnitalSuba
lgebra R A -> NonUnitalSubsemiring A).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `NonUnitalSubalgebra.smul_mem'`：∀ {R : Type u} {A : Type v} [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R A]  
 (self : NonUnitalS…
-/
lemma toNonUnitalSubsemiring_injective :
    (toNonUnitalSubsemiring : NonUnitalSubalgebra R A → NonUnitalSubsemiring A).Injective :=
  fun ⟨s, hs⟩ t ↦ by congr!
/-
**NonUnitalSubalgebra.toNonUnitalSubsemiring_inj** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalSubalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNon
AssocSemiring A] [inst_2 : _root_.Module R A]   {s t : NonUnitalSubalgebra R A},
 s.toNonUnitalSubsemiring = t.toNonUnitalSubsemiring ↔ s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `NonUnitalSubalgebra.toNonUnitalSubsemiring_injective`：toNonUnitalSubsemi
ring_injective : (toNonUnitalSubsemiring : NonUnitalSubalgebra R A -> NonUnitalS
ubsemiring A).Injective
-/
@[simp] lemma toNonUnitalSubsemiring_inj {s t : NonUnitalSubalgebra R A} :
    s.toNonUnitalSubsemiring = t.toNonUnitalSubsemiring ↔ s = t :=
  toNonUnitalSubsemiring_injective.eq_iff
/-
**NonUnitalSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (NonUnitalSubalgebra R A) A where
  coe s := s.carrier
  coe_injective := SetLike.coe_injective.comp toNonUnitalSubsemiring_injective
/-
**NonUnitalSubalgebra.toSubmodule_injective** 是 Mathlib 中的一个引理，位于命名空间 `NonUnital
Subalgebra`。
形式化陈述：toSubmodule_injective : (toSubmodule : NonUnitalSubalgebra R A -> Submodul
e R A).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
lemma toSubmodule_injective : (toSubmodule : NonUnitalSubalgebra R A → Submodule R A).Injective :=
  fun _ _ h ↦ SetLike.ext (SetLike.ext_iff.mp h :)
/-
**NonUnitalSubalgebra.toSubmodule_inj** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalSubalg
ebra`。
形式化陈述：toSubmodule_inj {s t : NonUnitalSubalgebra R A} : s.toSubmodule = t.toSubm
odule ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `NonUnitalSubalgebra.toSubmodule_injective`：toSubmodule_injective : (toSu
bmodule : NonUnitalSubalgebra R A -> Submodule R A).Injective
-/
lemma toSubmodule_inj {s t : NonUnitalSubalgebra R A} : s.toSubmodule = t.toSubmodule ↔ s = t :=
  toSubmodule_injective.eq_iff
/-
**NonUnitalSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (NonUnitalSubalgebra R A) := .ofSetLike (NonUnitalSubalgebra R A) A

/-- The actual `NonUnitalSubalgebra` obtained from an element of a type satisfying
`NonUnitalSubsemiringClass` and `SMulMemClass`. -/
@[simps]
/-
**NonUnitalSubalgebra.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：ofClass {S R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Mo
dule R A] [SetLike S A] [NonUnitalSubsemiringClass S A] [SMulMemClass S R A] (s 
: S) : NonUnitalSubalgebra R A where carrier
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The actual `NonUnitalSubalgebra` obtained from an element of a type satisfying
`NonUnitalSubsemiringClass` and `SMulMemClass`.
-/
def ofClass {S R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [SetLike S A] [NonUnitalSubsemiringClass S A] [SMulMemClass S R A]
    (s : S) : NonUnitalSubalgebra R A where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  smul_mem' := SMulMemClass.smul_mem
/-
**NonUnitalSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CanLift (Set A) (NonUnitalSubalgebra R A) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧
      ∀ (r : R) {x}, x ∈ s → r • x ∈ s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        mul_mem' := h.2.2.1
        smul_mem' := h.2.2.2 },
      rfl ⟩
/-
**NonUnitalSubalgebra.instNonUnitalSubsemiringClass** 是 Mathlib 中的一个实例，位于命名空间 `N
onUnitalSubalgebra`。
形式化陈述：instNonUnitalSubsemiringClass : NonUnitalSubsemiringClass (NonUnitalSubalg
ebra R A) A where add_mem {s}
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
    NonUnitalSubsemiringClass (NonUnitalSubalgebra R A) A where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'
/-
**NonUnitalSubalgebra.instSMulMemClass** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubal
gebra`。
形式化陈述：instSMulMemClass : SMulMemClass (NonUnitalSubalgebra R A) R A where smul_m
em {s}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.smul_mem'`：∀ {R : Type u} {A : Type v} [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R A]  
 (self : NonUnitalS…
-/
instance instSMulMemClass : SMulMemClass (NonUnitalSubalgebra R A) R A where
  smul_mem {s} := s.smul_mem'
/-
**NonUnitalSubalgebra.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra
`。
形式化陈述：mem_carrier {s : NonUnitalSubalgebra R A} {x : A} : x in s.carrier ↔ x in 
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : NonUnitalSubalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[ext]
/-
**NonUnitalSubalgebra.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：ext {S T : NonUnitalSubalgebra R A} (h : forall x : A, x in S ↔ x in T) : 
S = T
参数：h : forall x : A, x in S ↔ x in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext {S T : NonUnitalSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
/-
**NonUnitalSubalgebra.mem_toNonUnitalSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalSubalgebra`。
形式化陈述：mem_toNonUnitalSubsemiring {S : NonUnitalSubalgebra R A} {x} : x in S.toNo
nUnitalSubsemiring ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toNonUnitalSubsemiring {S : NonUnitalSubalgebra R A} {x} :
    x ∈ S.toNonUnitalSubsemiring ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**NonUnitalSubalgebra.coe_toNonUnitalSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalSubalgebra`。
形式化陈述：coe_toNonUnitalSubsemiring (S : NonUnitalSubalgebra R A) : (↑S.toNonUnital
Subsemiring : Set A) = S
参数：S : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNonUnitalSubsemiring (S : NonUnitalSubalgebra R A) :
    (↑S.toNonUnitalSubsemiring : Set A) = S :=
  rfl
/-
**NonUnitalSubalgebra.mem_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalg
ebra`。
形式化陈述：mem_toSubmodule (S : NonUnitalSubalgebra R A) {x} : x in S.toSubmodule ↔ x
 in S
参数：S : NonUnitalSubalgebra R A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubmodule (S : NonUnitalSubalgebra R A) {x} : x ∈ S.toSubmodule ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**NonUnitalSubalgebra.coe_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalg
ebra`。
形式化陈述：coe_toSubmodule (S : NonUnitalSubalgebra R A) : (↑S.toSubmodule : Set A) =
 S
参数：S : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubmodule (S : NonUnitalSubalgebra R A) : (↑S.toSubmodule : Set A) = S :=
  rfl

/-- Copy of a non-unital subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
/-
**NonUnitalSubalgebra.copy** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：{R : Type u} →   {A : Type v} →     [inst : CommSemiring R] →       [inst_
1 : NonUnitalNonAssocSemiring A] →         [inst_2 : _root_.Module R A] → (S : N
onUnitalSubalgebra R A) → (s : Set A) → s = ↑S → NonUnitalSubalgebra R A
参数：S : NonUnitalSubalgebra R A；s : Set A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a non-unital subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities.
-/
protected def copy (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    NonUnitalSubalgebra R A :=
  { S.toNonUnitalSubsemiring.copy s hs with
    smul_mem' r a := by simpa [hs] using! S.smul_mem r }

@[simp, norm_cast]
/-
**NonUnitalSubalgebra.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：coe_copy (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) : (S.copy
 s hs : Set A) = s
参数：S : NonUnitalSubalgebra R A；s : Set A；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    (S.copy s hs : Set A) = s :=
  rfl
/-
**NonUnitalSubalgebra.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：copy_eq (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s
 hs = S
参数：S : NonUnitalSubalgebra R A；s : Set A；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
/-
**NonUnitalSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : NonUnitalSubalgebra R A) : Inhabited S :=
  ⟨(0 : S.toNonUnitalSubsemiring)⟩

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocRing
variable [CommRing R]
variable [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B] [NonUnitalNonAssocRing C]
variable [Module R A] [Module R B] [Module R C]

/-
**NonUnitalSubalgebra.instNonUnitalSubringClass** 是 Mathlib 中的一个实例，位于命名空间 `NonUn
italSubalgebra`。
形式化陈述：instNonUnitalSubringClass : NonUnitalSubringClass (NonUnitalSubalgebra R A
) A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
-/
instance instNonUnitalSubringClass : NonUnitalSubringClass (NonUnitalSubalgebra R A) A :=
  { NonUnitalSubalgebra.instNonUnitalSubsemiringClass with
    neg_mem {_ x} hx := neg_one_smul R x ▸ SMulMemClass.smul_mem _ hx }

/-- A non-unital subalgebra over a ring is also a `Subring`. -/
@[reducible]
/-
**NonUnitalSubalgebra.toNonUnitalSubring** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSub
algebra`。
形式化陈述：toNonUnitalSubring (S : NonUnitalSubalgebra R A) : NonUnitalSubring A wher
e toNonUnitalSubsemiring
参数：S : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subalgebra over a ring is also a `Subring`.
-/
def toNonUnitalSubring (S : NonUnitalSubalgebra R A) : NonUnitalSubring A where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  neg_mem' := neg_mem (s := S)
/-
**NonUnitalSubalgebra.mem_toNonUnitalSubring** 是 Mathlib 中的一个定理，位于命名空间 `NonUnita
lSubalgebra`。
形式化陈述：mem_toNonUnitalSubring {S : NonUnitalSubalgebra R A} {x} : x in S.toNonUni
talSubring ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toNonUnitalSubring {S : NonUnitalSubalgebra R A} {x} :
    x ∈ S.toNonUnitalSubring ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**NonUnitalSubalgebra.coe_toNonUnitalSubring** 是 Mathlib 中的一个定理，位于命名空间 `NonUnita
lSubalgebra`。
形式化陈述：coe_toNonUnitalSubring (S : NonUnitalSubalgebra R A) : (↑S.toNonUnitalSubr
ing : Set A) = S
参数：S : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNonUnitalSubring (S : NonUnitalSubalgebra R A) :
    (↑S.toNonUnitalSubring : Set A) = S :=
  rfl
/-
**NonUnitalSubalgebra.toNonUnitalSubring_injective** 是 Mathlib 中的一个定理，位于命名空间 `No
nUnitalSubalgebra`。
形式化陈述：toNonUnitalSubring_injective : Function.Injective (toNonUnitalSubring : No
nUnitalSubalgebra R A -> NonUnitalSubring A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.ext`：ext {S T : NonUnitalSubalgebra R A} (h : forall
 x : A, x in S ↔ x in T) : S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalSubalgebra.mem_toNonUnitalSubring`：mem_toNonUnitalSubring {S : 
NonUnitalSubalgebra R A} {x} : x in S.toNonUnitalSubring ↔ x in S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toNonUnitalSubring_injective :
    Function.Injective (toNonUnitalSubring : NonUnitalSubalgebra R A → NonUnitalSubring A) :=
  fun S T h => ext fun x => by rw [← mem_toNonUnitalSubring, ← mem_toNonUnitalSubring, h]
/-
**NonUnitalSubalgebra.toNonUnitalSubring_inj** 是 Mathlib 中的一个定理，位于命名空间 `NonUnita
lSubalgebra`。
形式化陈述：toNonUnitalSubring_inj {S U : NonUnitalSubalgebra R A} : S.toNonUnitalSubr
ing = U.toNonUnitalSubring ↔ S = U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `NonUnitalSubalgebra.toNonUnitalSubring_injective`：toNonUnitalSubring_inj
ective : Function.Injective (toNonUnitalSubring : NonUnitalSubalgebra R A -> Non
UnitalSubring A)
-/
theorem toNonUnitalSubring_inj {S U : NonUnitalSubalgebra R A} :
    S.toNonUnitalSubring = U.toNonUnitalSubring ↔ S = U :=
  toNonUnitalSubring_injective.eq_iff

end NonUnitalNonAssocRing

section

/-! `NonUnitalSubalgebra`s inherit structure from their `NonUnitalSubsemiring` / `Semiring`
coercions. -/


/-
**NonUnitalSubalgebra.toNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Non
UnitalSubalgebra`。
形式化陈述：toNonUnitalNonAssocSemiring [CommSemiring R] [NonUnitalNonAssocSemiring A]
 [Module R A] (S : NonUnitalSubalgebra R A) : NonUnitalNonAssocSemiring S
参数：S : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonUnitalSubalgebra`s inherit structure from their `NonUnitalSubsemiring` / `Se
miring`
coercions.
-/
instance toNonUnitalNonAssocSemiring [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalNonAssocSemiring S :=
  inferInstance
/-
**NonUnitalSubalgebra.toNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSu
balgebra`。
形式化陈述：toNonUnitalSemiring [CommSemiring R] [NonUnitalSemiring A] [Module R A] (S
 : NonUnitalSubalgebra R A) : NonUnitalSemiring S
参数：S : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toNonUnitalSemiring [CommSemiring R] [NonUnitalSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalSemiring S :=
  inferInstance
/-
**NonUnitalSubalgebra.toNonUnitalCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `NonUnit
alSubalgebra`。
形式化陈述：toNonUnitalCommSemiring [CommSemiring R] [NonUnitalCommSemiring A] [Module
 R A] (S : NonUnitalSubalgebra R A) : NonUnitalCommSemiring S
参数：S : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toNonUnitalCommSemiring [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalCommSemiring S :=
  inferInstance
/-
**NonUnitalSubalgebra.toNonUnitalNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `NonUnit
alSubalgebra`。
形式化陈述：toNonUnitalNonAssocRing [CommRing R] [NonUnitalNonAssocRing A] [Module R A
] (S : NonUnitalSubalgebra R A) : NonUnitalNonAssocRing S
参数：S : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toNonUnitalNonAssocRing [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalNonAssocRing S :=
  inferInstance
/-
**NonUnitalSubalgebra.toNonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubalg
ebra`。
形式化陈述：toNonUnitalRing [CommRing R] [NonUnitalRing A] [Module R A] (S : NonUnital
Subalgebra R A) : NonUnitalRing S
参数：S : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toNonUnitalRing [CommRing R] [NonUnitalRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalRing S :=
  inferInstance
/-
**NonUnitalSubalgebra.toNonUnitalCommRing** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSu
balgebra`。
形式化陈述：toNonUnitalCommRing [CommRing R] [NonUnitalCommRing A] [Module R A] (S : N
onUnitalSubalgebra R A) : NonUnitalCommRing S
参数：S : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toNonUnitalCommRing [CommRing R] [NonUnitalCommRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalCommRing S :=
  inferInstance

end

/-- The forgetful map from `NonUnitalSubalgebra` to `Submodule` as an `OrderEmbedding` -/
/-
**NonUnitalSubalgebra.toSubmodule'** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubalgebr
a`。
形式化陈述：toSubmodule' [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
 NonUnitalSubalgebra R A ↪o Submodule R A where toEmbedding
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful map from `NonUnitalSubalgebra` to `Submodule` as an `OrderEmbeddin
g`
-/
def toSubmodule' [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
    NonUnitalSubalgebra R A ↪o Submodule R A where
  toEmbedding :=
    { toFun := fun S => S.toSubmodule
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

/-- The forgetful map from `NonUnitalSubalgebra` to `NonUnitalSubsemiring` as an
`OrderEmbedding` -/
/-
**NonUnitalSubalgebra.toNonUnitalSubsemiring'** 是 Mathlib 中的一个定义，位于命名空间 `NonUnit
alSubalgebra`。
形式化陈述：toNonUnitalSubsemiring' [CommSemiring R] [NonUnitalNonAssocSemiring A] [Mo
dule R A] : NonUnitalSubalgebra R A ↪o NonUnitalSubsemiring A where toEmbedding
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful map from `NonUnitalSubalgebra` to `NonUnitalSubsemiring` as an
`OrderEmbedding`
-/
def toNonUnitalSubsemiring' [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
    NonUnitalSubalgebra R A ↪o NonUnitalSubsemiring A where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubsemiring
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

/-- The forgetful map from `NonUnitalSubalgebra` to `NonUnitalSubsemiring` as an
`OrderEmbedding` -/
/-
**NonUnitalSubalgebra.toNonUnitalSubring'** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSu
balgebra`。
形式化陈述：toNonUnitalSubring' [CommRing R] [NonUnitalNonAssocRing A] [Module R A] : 
NonUnitalSubalgebra R A ↪o NonUnitalSubring A where toEmbedding
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful map from `NonUnitalSubalgebra` to `NonUnitalSubsemiring` as an
`OrderEmbedding`
-/
def toNonUnitalSubring' [CommRing R] [NonUnitalNonAssocRing A] [Module R A] :
    NonUnitalSubalgebra R A ↪o NonUnitalSubring A where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubring
      inj' := fun S T h => ext <| by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]
variable [Module R A] [Module R B] [Module R C]
variable {S : NonUnitalSubalgebra R A}

section

/-! ### `NonUnitalSubalgebra`s inherit structure from their `Submodule` coercions. -/

/-
**NonUnitalSubalgebra.instModule'** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubalgebra
`。
形式化陈述：instModule' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
 : Module R' S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `NonUnitalSubalgebra`s inherit structure from their `Submodule` coercions.
-/
instance instModule' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : Module R' S :=
  SMulMemClass.toModule' _ R' R A S
/-
**NonUnitalSubalgebra.instModule** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubalgebra`
。
形式化陈述：instModule : Module R S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule : Module R S :=
  S.instModule'
/-
**NonUnitalSubalgebra.instIsScalarTower'** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSub
algebra`。
形式化陈述：instIsScalarTower' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower 
R' R A] : IsScalarTower R' R S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTower' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    IsScalarTower R' R S :=
  S.toSubmodule.isScalarTower
/-
**NonUnitalSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsScalarTower R A A] : IsScalarTower R S S where
  smul_assoc r x y := Subtype.ext <| smul_assoc r (x : A) (y : A)
/-
**NonUnitalSubalgebra.instSMulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSub
algebra`。
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
**NonUnitalSubalgebra.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSuba
lgebra`。
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
/-
**NonUnitalSubalgebra.instIsTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSuba
lgebra`。
形式化陈述：instIsTorsionFree [Module.IsTorsionFree R A] : Module.IsTorsionFree R S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsTorsionFree [Module.IsTorsionFree R A] : Module.IsTorsionFree R S :=
  S.toSubmodule.instIsTorsionFree

end

/-
**NonUnitalSubalgebra.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNon
AssocSemiring A] [inst_2 : _root_.Module R A]   {S : NonUnitalSubalgebra R A} (x
 y : ↥S), ↑(x + y) = ↑x + ↑y
参数：x y : ↥S；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y :=
  rfl
/-
**NonUnitalSubalgebra.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNon
AssocSemiring A] [inst_2 : _root_.Module R A]   {S : NonUnitalSubalgebra R A} (x
 y : ↥S), ↑(x * y) = ↑x * ↑y
参数：x y : ↥S；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y :=
  rfl
/-
**NonUnitalSubalgebra.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNon
AssocSemiring A] [inst_2 : _root_.Module R A]   {S : NonUnitalSubalgebra R A}, ↑
0 = 0
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
**NonUnitalSubalgebra.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : Ring A] [inst_2 
: Algebra R A] {S : NonUnitalSubalgebra R A}   (x : ↥S), ↑(-x) = -↑x
参数：x : ↥S；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
-/
protected theorem coe_neg {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : NonUnitalSubalgebra R A} (x : S) : (↑(-x) : A) = -↑x :=
  rfl
/-
**NonUnitalSubalgebra.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : Ring A] [inst_2 
: Algebra R A] {S : NonUnitalSubalgebra R A}   (x y : ↥S), ↑(x - y) = ↑x - ↑y
参数：x y : ↥S；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [i
nst : SetLike S R] [inst_1 : NonUnitalNonAssocRing R] [h : NonUnitalSubringClass
 S R],   AddSubgroupClass S …
-/
protected theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : NonUnitalSubalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y :=
  rfl

@[simp, norm_cast]
/-
**NonUnitalSubalgebra.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
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
**NonUnitalSubalgebra.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra
`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNon
AssocSemiring A] [inst_2 : _root_.Module R A]   {S : NonUnitalSubalgebra R A} {x
 : ↥S}, ↑x = 0 ↔ x = 0
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
**NonUnitalSubalgebra.toNonUnitalSubsemiring_subtype** 是 Mathlib 中的一个定理，位于命名空间 `
NonUnitalSubalgebra`。
形式化陈述：toNonUnitalSubsemiring_subtype : NonUnitalSubsemiringClass.subtype S = Non
UnitalSubalgebraClass.subtype (R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNonUnitalSubsemiring_subtype :
    NonUnitalSubsemiringClass.subtype S = NonUnitalSubalgebraClass.subtype (R := R) S :=
  rfl

@[simp]
/-
**NonUnitalSubalgebra.toSubring_subtype** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSuba
lgebra`。
形式化陈述：toSubring_subtype {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : N
onUnitalSubalgebra R A) : NonUnitalSubringClass.subtype S = NonUnitalSubalgebraC
lass.subtype (R
参数：S : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubring_subtype {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (S : NonUnitalSubalgebra R A) :
    NonUnitalSubringClass.subtype S = NonUnitalSubalgebraClass.subtype (R := R) S :=
  rfl

/-- Linear equivalence between `S : Submodule R A` and `S`. Though these types are equal,
we define it as a `LinearEquiv` to avoid type equalities. -/
/-
**NonUnitalSubalgebra.toSubmoduleEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubal
gebra`。
形式化陈述：toSubmoduleEquiv (S : NonUnitalSubalgebra R A) : S.toSubmodule ≃ₗ[R] S
参数：S : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear equivalence between `S : Submodule R A` and `S`. Though these types are e
qual,
we define it as a `LinearEquiv` to avoid type equalities.
-/
def toSubmoduleEquiv (S : NonUnitalSubalgebra R A) : S.toSubmodule ≃ₗ[R] S :=
  LinearEquiv.ofEq _ _ rfl

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

/-- Transport a non-unital subalgebra via an algebra homomorphism. -/
/-
**NonUnitalSubalgebra.map** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：map (f : F) (S : NonUnitalSubalgebra R A) : NonUnitalSubalgebra R B
参数：f : F；S : NonUnitalSubalgebra R A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…

--- 原说明 ---
Transport a non-unital subalgebra via an algebra homomorphism.
-/
def map (f : F) (S : NonUnitalSubalgebra R A) : NonUnitalSubalgebra R B :=
  { S.toNonUnitalSubsemiring.map (f : A →ₙ+* B) with
    smul_mem' := fun r b hb => by
      rcases hb with ⟨a, ha, rfl⟩
      exact map_smulₛₗ f r a ▸ Set.mem_image_of_mem f (S.smul_mem' r ha) }

@[gcongr]
/-
**NonUnitalSubalgebra.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：map_mono {S₁ S₂ : NonUnitalSubalgebra R A} {f : F} : S₁ <= S₂ -> (map f S₁
 : NonUnitalSubalgebra R B) <= map f S₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem map_mono {S₁ S₂ : NonUnitalSubalgebra R A} {f : F} :
    S₁ ≤ S₂ → (map f S₁ : NonUnitalSubalgebra R B) ≤ map f S₂ :=
  Set.image_mono
/-
**NonUnitalSubalgebra.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgeb
ra`。
形式化陈述：map_injective {f : F} (hf : Function.Injective f) : Function.Injective (ma
p f : NonUnitalSubalgebra R A -> NonUnitalSubalgebra R B)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.ext`：ext {S T : NonUnitalSubalgebra R A} (h : forall
 x : A, x in S ↔ x in T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_injective`：image_injective : Injective (image f) ↔ Injective f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem map_injective {f : F} (hf : Function.Injective f) :
    Function.Injective (map f : NonUnitalSubalgebra R A → NonUnitalSubalgebra R B) :=
  fun _S₁ _S₂ ih =>
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih

@[simp]
/-
**NonUnitalSubalgebra.map_id** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：map_id (S : NonUnitalSubalgebra R A) : map (NonUnitalAlgHom.id R A) S = S
参数：S : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem map_id (S : NonUnitalSubalgebra R A) : map (NonUnitalAlgHom.id R A) S = S :=
  SetLike.coe_injective <| Set.image_id _
/-
**NonUnitalSubalgebra.map_map** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：map_map (S : NonUnitalSubalgebra R A) (g : B ->ₙₐ[R] C) (f : A ->ₙₐ[R] B) 
: (S.map f).map g = S.map (g.comp f)
参数：S : NonUnitalSubalgebra R A；g : B ->ₙₐ[R] C；f : A ->ₙₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map (S : NonUnitalSubalgebra R A) (g : B →ₙₐ[R] C) (f : A →ₙₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

@[simp]
/-
**NonUnitalSubalgebra.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：mem_map {S : NonUnitalSubalgebra R A} {f : F} {y : B} : y in map f S ↔ exi
sts x in S, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.mem_map`：mem_map {f : F} {s : NonUnitalSubsemiring 
R} {y : S} : y in s.map f ↔ exists x in s, f x = y
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
-/
theorem mem_map {S : NonUnitalSubalgebra R A} {f : F} {y : B} : y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  NonUnitalSubsemiring.mem_map
/-
**NonUnitalSubalgebra.map_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalg
ebra`。
形式化陈述：map_toSubmodule {S : NonUnitalSubalgebra R A} {f : F} : -- TODO: introduce
 a better coercion from `NonUnitalAlgHomClass` to `LinearMap` (map f S).toSubmod
ule = Submodule.map (LinearMapClass.linearMap f) S.toSubmodule
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
-/
theorem map_toSubmodule {S : NonUnitalSubalgebra R A} {f : F} :
    -- TODO: introduce a better coercion from `NonUnitalAlgHomClass` to `LinearMap`
    (map f S).toSubmodule = Submodule.map (LinearMapClass.linearMap f) S.toSubmodule :=
  SetLike.coe_injective rfl
/-
**NonUnitalSubalgebra.map_toNonUnitalSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalSubalgebra`。
形式化陈述：map_toNonUnitalSubsemiring {S : NonUnitalSubalgebra R A} {f : F} : (map f 
S).toNonUnitalSubsemiring = S.toNonUnitalSubsemiring.map (f : A ->ₙ+* B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `NonUnitalAlgHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type
 u_2} {S : Type u_3} {A : Type u_4} {B : Type u_5} {x : Monoid R} {x_1 : Monoid 
S}   {φ : outParam (R →* S)} {x_2 …
-/
theorem map_toNonUnitalSubsemiring {S : NonUnitalSubalgebra R A} {f : F} :
    (map f S).toNonUnitalSubsemiring = S.toNonUnitalSubsemiring.map (f : A →ₙ+* B) :=
  SetLike.coe_injective rfl

@[simp]
/-
**NonUnitalSubalgebra.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：coe_map (S : NonUnitalSubalgebra R A) (f : F) : (map f S : Set B) = f '' S
参数：S : NonUnitalSubalgebra R A；f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (S : NonUnitalSubalgebra R A) (f : F) : (map f S : Set B) = f '' S :=
  rfl

/-- Preimage of a non-unital subalgebra under an algebra homomorphism. -/
/-
**NonUnitalSubalgebra.comap** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：comap (f : F) (S : NonUnitalSubalgebra R B) : NonUnitalSubalgebra R A
参数：f : F；S : NonUnitalSubalgebra R B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…

--- 原说明 ---
Preimage of a non-unital subalgebra under an algebra homomorphism.
-/
def comap (f : F) (S : NonUnitalSubalgebra R B) : NonUnitalSubalgebra R A :=
  { S.toNonUnitalSubsemiring.comap (f : A →ₙ+* B) with
    smul_mem' := fun r a (ha : f a ∈ S) =>
      show f (r • a) ∈ S from (map_smulₛₗ f r a).symm ▸ SMulMemClass.smul_mem r ha }
/-
**NonUnitalSubalgebra.map_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：map_le {S : NonUnitalSubalgebra R A} {f : F} {U : NonUnitalSubalgebra R B}
 : map f S <= U ↔ S <= comap f U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le {S : NonUnitalSubalgebra R A} {f : F} {U : NonUnitalSubalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff
/-
**NonUnitalSubalgebra.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebr
a`。
形式化陈述：gc_map_comap (f : F) : GaloisConnection (map f : NonUnitalSubalgebra R A -
> NonUnitalSubalgebra R B) (comap f)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.map_le`：map_le {S : NonUnitalSubalgebra R A} {f : F}
 {U : NonUnitalSubalgebra R B} : map f S <= U ↔ S <= comap f U
-/
theorem gc_map_comap (f : F) :
    GaloisConnection (map f : NonUnitalSubalgebra R A → NonUnitalSubalgebra R B) (comap f) :=
  fun _ _ => map_le

@[simp]
/-
**NonUnitalSubalgebra.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：mem_comap (S : NonUnitalSubalgebra R B) (f : F) (x : A) : x in comap f S ↔
 f x in S
参数：S : NonUnitalSubalgebra R B；f : F；x : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap (S : NonUnitalSubalgebra R B) (f : F) (x : A) : x ∈ comap f S ↔ f x ∈ S :=
  Iff.rfl

@[simp, norm_cast]
/-
**NonUnitalSubalgebra.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：coe_comap (S : NonUnitalSubalgebra R B) (f : F) : (comap f S : Set A) = f 
⁻¹' (S : Set B)
参数：S : NonUnitalSubalgebra R B；f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (S : NonUnitalSubalgebra R B) (f : F) : (comap f S : Set A) = f ⁻¹' (S : Set B) :=
  rfl
/-
**NonUnitalSubalgebra.noZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubalge
bra`。
形式化陈述：noZeroDivisors {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [NoZer
oDivisors A] [Module R A] (S : NonUnitalSubalgebra R A) : NoZeroDivisors S
参数：S : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance noZeroDivisors {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [NoZeroDivisors A]
    [Module R A] (S : NonUnitalSubalgebra R A) : NoZeroDivisors S :=
  NonUnitalSubsemiringClass.noZeroDivisors S

end NonUnitalSubalgebra

namespace Submodule

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

/-- A submodule closed under multiplication is a non-unital subalgebra. -/
/-
**Submodule.toNonUnitalSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：toNonUnitalSubalgebra (p : Submodule R A) (h_mul : forall x y, x in p -> y
 in p -> x * y in p) : NonUnitalSubalgebra R A
参数：p : Submodule R A；h_mul : forall x y, x in p -> y in p -> x * y in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule closed under multiplication is a non-unital subalgebra.
-/
def toNonUnitalSubalgebra (p : Submodule R A) (h_mul : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p) :
    NonUnitalSubalgebra R A :=
  { p with
    mul_mem' := h_mul _ _ }

@[simp]
/-
**Submodule.mem_toNonUnitalSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_toNonUnitalSubalgebra {p : Submodule R A} {h_mul} {x} : x in p.toNonUn
italSubalgebra h_mul ↔ x in p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toNonUnitalSubalgebra {p : Submodule R A} {h_mul} {x} :
    x ∈ p.toNonUnitalSubalgebra h_mul ↔ x ∈ p :=
  Iff.rfl

@[simp]
/-
**Submodule.coe_toNonUnitalSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_toNonUnitalSubalgebra (p : Submodule R A) (h_mul) : (p.toNonUnitalSuba
lgebra h_mul : Set A) = p
参数：p : Submodule R A；h_mul。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNonUnitalSubalgebra (p : Submodule R A) (h_mul) :
    (p.toNonUnitalSubalgebra h_mul : Set A) = p :=
  rfl
/-
**Submodule.toNonUnitalSubalgebra_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toNonUnitalSubalgebra_mk (p : Submodule R A) hmul : p.toNonUnitalSubalgebr
a hmul = NonUnitalSubalgebra.mk ⟨⟨⟨p, p.add_mem⟩, p.zero_mem⟩, hmul _ _⟩ p.smul_
mem'
参数：p : Submodule R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNonUnitalSubalgebra_mk (p : Submodule R A) hmul :
    p.toNonUnitalSubalgebra hmul =
      NonUnitalSubalgebra.mk ⟨⟨⟨p, p.add_mem⟩, p.zero_mem⟩, hmul _ _⟩ p.smul_mem' :=
  rfl

@[simp]
/-
**Submodule.toNonUnitalSubalgebra_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：toNonUnitalSubalgebra_toSubmodule (p : Submodule R A) (h_mul) : (p.toNonUn
italSubalgebra h_mul).toSubmodule = p
参数：p : Submodule R A；h_mul。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem toNonUnitalSubalgebra_toSubmodule (p : Submodule R A) (h_mul) :
    (p.toNonUnitalSubalgebra h_mul).toSubmodule = p :=
  SetLike.coe_injective rfl

@[simp]
/-
**Submodule._root_.NonUnitalSubalgebra.toSubmodule_toNonUnitalSubalgebra** 是 Mat
hlib 中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NonUnitalSubalgebra.toSubmodule_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A) :
    (S.toSubmodule.toNonUnitalSubalgebra fun _ _ => mul_mem (s := S)) = S :=
  SetLike.coe_injective rfl

end Submodule

namespace NonUnitalAlgHom

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}
variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [NonUnitalNonAssocSemiring B] [Module R B]
variable [NonUnitalNonAssocSemiring C] [Module R C] [FunLike F A B] [NonUnitalAlgHomClass F R A B]

/-- Range of an `NonUnitalAlgHom` as a non-unital subalgebra. -/
/-
**NonUnitalAlgHom.range** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：{F : Type v'} →   {R : Type u} →     {A : Type v} →       {B : Type w} →  
       [inst : CommSemiring R] →           [inst_1 : NonUnitalNonAssocSemiring A
] →             [inst_2 : _root_.Module R A] →               [inst_3 : NonUnital
NonAssocSemiring B] →                 [inst_4 : _root_.Module R B] →            
       [inst_5 : FunLike F A B] → [NonUnitalAlgHomClass F R A B] → F → NonUnital
Subalgebra R B
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…

--- 原说明 ---
Range of an `NonUnitalAlgHom` as a non-unital subalgebra.
-/
protected def range (φ : F) : NonUnitalSubalgebra R B where
  toNonUnitalSubsemiring := NonUnitalRingHom.srange (φ : A →ₙ+* B)
  smul_mem' := fun r a => by rintro ⟨a, rfl⟩; exact ⟨r • a, map_smul φ r a⟩

@[simp]
/-
**NonUnitalAlgHom.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：mem_range (φ : F) {y : B} : y in (NonUnitalAlgHom.range φ : NonUnitalSubal
gebra R B) ↔ exists x : A, φ x = y
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
    y ∈ (NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) ↔ ∃ x : A, φ x = y :=
  NonUnitalRingHom.mem_srange
/-
**NonUnitalAlgHom.mem_range_self** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：mem_range_self (φ : F) (x : A) : φ x in (NonUnitalAlgHom.range φ : NonUnit
alSubalgebra R B)
参数：φ : F；x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalAlgHom.mem_range`：mem_range (φ : F) {y : B} : y in (NonUnitalAl
gHom.range φ : NonUnitalSubalgebra R B) ↔ exists x : A, φ x = y
-/
theorem mem_range_self (φ : F) (x : A) :
    φ x ∈ (NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) :=
  (NonUnitalAlgHom.mem_range φ).2 ⟨x, rfl⟩

@[simp]
/-
**NonUnitalAlgHom.coe_range** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_range (φ : F) : ((NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) :
 Set B) = Set.range (φ : A -> B)
参数：φ : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `NonUnitalAlgHom.mem_range`：mem_range (φ : F) {y : B} : y in (NonUnitalAl
gHom.range φ : NonUnitalSubalgebra R B) ↔ exists x : A, φ x = y
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_range (φ : F) :
    ((NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) : Set B) = Set.range (φ : A → B) := by
  ext
  rw [SetLike.mem_coe, mem_range, Set.mem_range]
/-
**NonUnitalAlgHom.range_comp** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：range_comp (f : A ->ₙₐ[R] B) (g : B ->ₙₐ[R] C) : NonUnitalAlgHom.range (g.
comp f) = (NonUnitalAlgHom.range f).map g
参数：f : A ->ₙₐ[R] B；g : B ->ₙₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem range_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    NonUnitalAlgHom.range (g.comp f) = (NonUnitalAlgHom.range f).map g :=
  SetLike.coe_injective (Set.range_comp g f)
/-
**NonUnitalAlgHom.range_comp_le_range** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom
`。
形式化陈述：range_comp_le_range (f : A ->ₙₐ[R] B) (g : B ->ₙₐ[R] C) : NonUnitalAlgHom.
range (g.comp f) <= NonUnitalAlgHom.range g
参数：f : A ->ₙₐ[R] B；g : B ->ₙₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
-/
theorem range_comp_le_range (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    NonUnitalAlgHom.range (g.comp f) ≤ NonUnitalAlgHom.range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

/-- Restrict the codomain of a non-unital algebra homomorphism. -/
/-
**NonUnitalAlgHom.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : forall x, f x in S
) : A ->ₙₐ[R] S
参数：f : F；S : NonUnitalSubalgebra R B；hf : forall x, f x in S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…

--- 原说明 ---
Restrict the codomain of a non-unital algebra homomorphism.
-/
def codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : ∀ x, f x ∈ S) : A →ₙₐ[R] S :=
  { NonUnitalRingHom.codRestrict (f : A →ₙ+* B) S.toNonUnitalSubsemiring hf with
    map_smul' := fun r a => Subtype.ext <| map_smul f r a }

@[simp]
/-
**NonUnitalAlgHom.subtype_comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalA
lgHom`。
形式化陈述：subtype_comp_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : foral
l x : A, f x in S) : (NonUnitalSubalgebraClass.subtype S).comp (NonUnitalAlgHom.
codRestrict f S hf) = f
参数：f : F；S : NonUnitalSubalgebra R B；hf : forall x : A, f x in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
-/
theorem subtype_comp_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    (NonUnitalSubalgebraClass.subtype S).comp (NonUnitalAlgHom.codRestrict f S hf) = f :=
  rfl

@[simp]
/-
**NonUnitalAlgHom.coe_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : forall x, f x 
in S) (x : A) : ↑(NonUnitalAlgHom.codRestrict f S hf x) = f x
参数：f : F；S : NonUnitalSubalgebra R B；hf : forall x, f x in S；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
    ↑(NonUnitalAlgHom.codRestrict f S hf x) = f x :=
  rfl
/-
**NonUnitalAlgHom.injective_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgH
om`。
形式化陈述：injective_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : forall x
 : A, f x in S) : Function.Injective (NonUnitalAlgHom.codRestrict f S hf) ↔ Func
tion.Injective f
参数：f : F；S : NonUnitalSubalgebra R B；hf : forall x : A, f x in S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem injective_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : ∀ x : A, f x ∈ S) :
    Function.Injective (NonUnitalAlgHom.codRestrict f S hf) ↔ Function.Injective f :=
  ⟨fun H _x _y hxy => H <| Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

/-- Restrict the codomain of an `NonUnitalAlgHom` `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`. -/
/-
**NonUnitalAlgHom.rangeRestrict** 是 Mathlib 中的一个缩写定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：rangeRestrict (f : F) : A ->ₙₐ[R] (NonUnitalAlgHom.range f : NonUnitalSuba
lgebra R B)
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHom.mem_range_self`：mem_range_self (φ : F) (x : A) : φ x in 
(NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B)

--- 原说明 ---
Restrict the codomain of an `NonUnitalAlgHom` `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`.
-/
abbrev rangeRestrict (f : F) : A →ₙₐ[R] (NonUnitalAlgHom.range f : NonUnitalSubalgebra R B) :=
  NonUnitalAlgHom.codRestrict f (NonUnitalAlgHom.range f) (NonUnitalAlgHom.mem_range_self f)

/-- The equalizer of two non-unital `R`-algebra homomorphisms -/
/-
**NonUnitalAlgHom.equalizer** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：equalizer (ϕ ψ : F) : NonUnitalSubalgebra R A where carrier
参数：ϕ ψ : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equalizer of two non-unital `R`-algebra homomorphisms
-/
def equalizer (ϕ ψ : F) : NonUnitalSubalgebra R A where
  carrier := {a | (ϕ a : B) = ψ a}
  zero_mem' := by rw [Set.mem_ofPred_eq, map_zero, map_zero]
  add_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_ofPred_eq, map_add, map_add, hx, hy]
  mul_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_ofPred_eq, map_mul, map_mul, hx, hy]
  smul_mem' r x (hx : ϕ x = ψ x) := by rw [Set.mem_ofPred_eq, map_smul, map_smul, hx]

@[simp]
/-
**NonUnitalAlgHom.mem_equalizer** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：mem_equalizer (φ ψ : F) (x : A) : x in NonUnitalAlgHom.equalizer φ ψ ↔ φ x
 = ψ x
参数：φ ψ : F；x : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_equalizer (φ ψ : F) (x : A) :
    x ∈ NonUnitalAlgHom.equalizer φ ψ ↔ φ x = ψ x :=
  Iff.rfl

/-- The range of a morphism of algebras is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `Subtype.fintype` if `B` is also a fintype. -/
/-
**NonUnitalAlgHom.fintypeRange** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：fintypeRange [Fintype A] [DecidableEq B] (φ : F) : Fintype (NonUnitalAlgHo
m.range φ)
参数：φ : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a morphism of algebras is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `Subtype.fintype` if `B` is als
o a fintype.
-/
instance fintypeRange [Fintype A] [DecidableEq B] (φ : F) :
    Fintype (NonUnitalAlgHom.range φ) :=
  Set.fintypeRange φ

end NonUnitalAlgHom

namespace NonUnitalAlgebra

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}
variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

@[simp]
/-
**NonUnitalAlgebra.span_eq_toSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalAlgeb
ra`。
形式化陈述：span_eq_toSubmodule (s : NonUnitalSubalgebra R A) : Submodule.span R (s : 
Set A) = s.toSubmodule
参数：s : NonUnitalSubalgebra R A。
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
lemma span_eq_toSubmodule (s : NonUnitalSubalgebra R A) :
    Submodule.span R (s : Set A) = s.toSubmodule := by
  simp [SetLike.ext'_iff, Submodule.coe_span_eq_self]

variable [NonUnitalNonAssocSemiring B] [Module R B]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

section IsScalarTower

variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The minimal non-unital subalgebra that includes `s`. -/
/-
**NonUnitalAlgebra.adjoin** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：adjoin (s : Set A) : NonUnitalSubalgebra R A
参数：s : Set A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimal non-unital subalgebra that includes `s`.
-/
def adjoin (s : Set A) : NonUnitalSubalgebra R A :=
  { Submodule.span R (NonUnitalSubsemiring.closure s : Set A) with
    mul_mem' :=
      fun {a b} (ha : a ∈ Submodule.span R (NonUnitalSubsemiring.closure s : Set A))
        (hb : b ∈ Submodule.span R (NonUnitalSubsemiring.closure s : Set A)) =>
      show a * b ∈ Submodule.span R (NonUnitalSubsemiring.closure s : Set A) by
        refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
        · refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
          · exact fun x (hx : x ∈ NonUnitalSubsemiring.closure s) y
              (hy : y ∈ NonUnitalSubsemiring.closure s) => Submodule.subset_span (mul_mem hy hx)
          · exact fun x _hx => (mul_zero x).symm ▸ Submodule.zero_mem _
          · exact fun x y _ _ hx hy z hz => (mul_add z x y).symm ▸ add_mem (hx z hz) (hy z hz)
          · exact fun r x _ hx y hy =>
              (mul_smul_comm r y x).symm ▸ SMulMemClass.smul_mem r (hx y hy)
        · exact (zero_mul b).symm ▸ Submodule.zero_mem _
        · exact fun x y _ _ => (add_mul x y b).symm ▸ add_mem
        · exact fun r x _ hx => (smul_mul_assoc r x b).symm ▸ SMulMemClass.smul_mem r hx }
/-
**NonUnitalAlgebra.adjoin_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebr
a`。
形式化陈述：adjoin_toSubmodule (s : Set A) : (adjoin R s).toSubmodule = Submodule.span
 R (NonUnitalSubsemiring.closure s : Set A)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjoin_toSubmodule (s : Set A) :
    (adjoin R s).toSubmodule = Submodule.span R (NonUnitalSubsemiring.closure s : Set A) :=
  rfl

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/-
**NonUnitalAlgebra.subset_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：subset_adjoin {s : Set A} : s subseteq adjoin R s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `NonUnitalSubsemiring.subset_closure`：subset_closure {s : Set R} : s subs
eteq closure s
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
theorem subset_adjoin {s : Set A} : s ⊆ adjoin R s :=
  NonUnitalSubsemiring.subset_closure.trans Submodule.subset_span

@[aesop 80% (rule_sets := [SetLike])]
/-
**NonUnitalAlgebra.mem_adjoin_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra
`。
形式化陈述：mem_adjoin_of_mem {s : Set A} {x : A} (hx : x in s) : x in adjoin R s
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.subset_adjoin`：subset_adjoin {s : Set A} : s subseteq a
djoin R s
-/
theorem mem_adjoin_of_mem {s : Set A} {x : A} (hx : x ∈ s) : x ∈ adjoin R s := subset_adjoin R hx

@[simp]
/-
**NonUnitalAlgebra.self_mem_adjoin_singleton** 是 Mathlib 中的一个定理，位于命名空间 `NonUnita
lAlgebra`。
形式化陈述：self_mem_adjoin_singleton (x : A) : x in adjoin R ({x} : Set A)
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.subset_adjoin`：subset_adjoin {s : Set A} : s subseteq a
djoin R s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : Set A) :=
  NonUnitalAlgebra.subset_adjoin R (Set.mem_singleton x)

variable {R}
/-
**NonUnitalAlgebra.gc** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNon
AssocSemiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] [
inst_4 : SMulCommClass R A A],   GaloisConnection (NonUnitalAlgebra.adjoin R) Se
tLike.coe
参数：NonUnitalAlgebra.adjoin R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `NonUnitalSubsemiring.subset_closure`：subset_closure {s : Set R} : s subs
eteq closure s
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `NonUnitalSubsemiring.closure_le`：closure_le {s : Set R} {t : NonUnitalSu
bsemiring R} : closure s <= t ↔ s subseteq t
-/
protected theorem gc : GaloisConnection (adjoin R : Set A → NonUnitalSubalgebra R A) (↑) :=
  fun s S =>
  ⟨fun H => (NonUnitalSubsemiring.subset_closure.trans Submodule.subset_span).trans H,
    fun H => show Submodule.span R _ ≤ S.toSubmodule from Submodule.span_le.mpr <|
      show NonUnitalSubsemiring.closure s ≤ S.toNonUnitalSubsemiring from
        NonUnitalSubsemiring.closure_le.2 H⟩

/-- Galois insertion between `adjoin` and `SetLike.coe`. -/
/-
**NonUnitalAlgebra.gi** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：{R : Type u} →   {A : Type v} →     [inst : CommSemiring R] →       [inst_
1 : NonUnitalNonAssocSemiring A] →         [inst_2 : _root_.Module R A] →       
    [inst_3 : IsScalarTower R A A] →             [inst_4 : SMulCommClass R A A] 
→ GaloisInsertion (NonUnitalAlgebra.adjoin R) SetLike.coe
参数：NonUnitalAlgebra.adjoin R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R A]   [inst_3 :
 IsScalar…

--- 原说明 ---
Galois insertion between `adjoin` and `SetLike.coe`.
-/
protected def gi : GaloisInsertion (adjoin R : Set A → NonUnitalSubalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s <| le_antisymm (NonUnitalAlgebra.gc.le_u_l s) hs
  gc := NonUnitalAlgebra.gc
  le_l_u S := (NonUnitalAlgebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := NonUnitalSubalgebra.copy_eq _ _ _
/-
**NonUnitalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (NonUnitalSubalgebra R A) :=
  GaloisInsertion.liftCompleteLattice NonUnitalAlgebra.gi
/-
**NonUnitalAlgebra.adjoin_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：adjoin_le {S : NonUnitalSubalgebra R A} {s : Set A} (hs : s subseteq S) : 
adjoin R s <= S
参数：hs : s subseteq S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_le`：l_le {a : α} {b : β} : a <= u b -> l a <= b
· 使用定理 `NonUnitalAlgebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R A]   [inst_3 :
 IsScalar…
-/
theorem adjoin_le {S : NonUnitalSubalgebra R A} {s : Set A} (hs : s ⊆ S) : adjoin R s ≤ S :=
  NonUnitalAlgebra.gc.l_le hs

@[simp]
/-
**NonUnitalAlgebra.adjoin_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：adjoin_le_iff {S : NonUnitalSubalgebra R A} {s : Set A} : adjoin R s <= S 
↔ s subseteq S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R A]   [inst_3 :
 IsScalar…
-/
theorem adjoin_le_iff {S : NonUnitalSubalgebra R A} {s : Set A} : adjoin R s ≤ S ↔ s ⊆ S :=
  NonUnitalAlgebra.gc _ _

@[gcongr]
/-
**NonUnitalAlgebra.adjoin_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：adjoin_mono {s t : Set A} (H : s subseteq t) : adjoin R s <= adjoin R t
参数：H : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `NonUnitalAlgebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R A]   [inst_3 :
 IsScalar…
-/
theorem adjoin_mono {s t : Set A} (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
  NonUnitalAlgebra.gc.monotone_l H
/-
**NonUnitalAlgebra.adjoin_union** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：adjoin_union (s t : Set A) : adjoin R (s union t) = adjoin R s ⊔ adjoin R 
t
参数：s t : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `NonUnitalAlgebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R A]   [inst_3 :
 IsScalar…
-/
theorem adjoin_union (s t : Set A) : adjoin R (s ∪ t) = adjoin R s ⊔ adjoin R t :=
  (NonUnitalAlgebra.gc : GaloisConnection _ ((↑) : NonUnitalSubalgebra R A → Set A)).l_sup

@[simp]
/-
**NonUnitalAlgebra.adjoin_eq** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：adjoin_eq (s : NonUnitalSubalgebra R A) : adjoin R (s : Set A) = s
参数：s : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `NonUnitalAlgebra.adjoin_le`：adjoin_le {S : NonUnitalSubalgebra R A} {s :
 Set A} (hs : s subseteq S) : adjoin R s <= S
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `NonUnitalAlgebra.subset_adjoin`：subset_adjoin {s : Set A} : s subseteq a
djoin R s
-/
lemma adjoin_eq (s : NonUnitalSubalgebra R A) : adjoin R (s : Set A) = s :=
  le_antisymm (adjoin_le le_rfl) (subset_adjoin R)

/-- If some predicate holds for all `x ∈ (s : Set A)` and this predicate is closed under the
`algebraMap`, addition, multiplication and star operations, then it holds for `a ∈ adjoin R s`. -/
@[elab_as_elim]
/-
**NonUnitalAlgebra.adjoin_induction** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`
。
形式化陈述：adjoin_induction {s : Set A} {p : (x : A) -> x in adjoin R s -> Prop} (mem
 : forall (x) (hx : x in s), p x (subset_adjoin R hx)) (add : forall x y hx hy, 
p x hx -> p y hy -> p (x + y) (add_mem hx hy)) (zero : p 0 (zero_mem _)) (mul : 
forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)) (smul : forall 
r x hx, p x hx -> p (r • x) (SMulMemClass.smul_mem r hx)) {x} (hx : x in adjoin 
R s) : p x hx
参数：x : A；mem : forall (x) (hx : x in s), p x (subset_adjoin R hx)；add : forall x
 y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)；zero : p 0 (zero_mem _)；
mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)；smul : for
all r x hx, p x hx -> p (r • x) (SMulMemClass.smul_mem r hx)；hx : x in adjoin R 
s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.subset_adjoin`：subset_adjoin {s : Set A} : s subseteq a
djoin R s
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
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `NonUnitalAlgebra.adjoin_le`：adjoin_le {S : NonUnitalSubalgebra R A} {s :
 Set A} (hs : s subseteq S) : adjoin R s <= S

--- 原说明 ---
If some predicate holds for all `x ∈ (s : Set A)` and this predicate is closed u
nder the
`algebraMap`, addition, multiplication and star operations, then it holds for `a
 ∈ adjoin R s`.
-/
theorem adjoin_induction {s : Set A} {p : (x : A) → x ∈ adjoin R s → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (subset_adjoin R hx))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy)) (zero : p 0 (zero_mem _))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (smul : ∀ r x hx, p x hx → p (r • x) (SMulMemClass.smul_mem r hx))
    {x} (hx : x ∈ adjoin R s) : p x hx :=
  let S : NonUnitalSubalgebra R A :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := (Exists.elim · fun _ ha ↦ (Exists.elim · fun _ hb ↦ ⟨_, mul _ _ _ _ ha hb⟩))
      add_mem' := (Exists.elim · fun _ ha ↦ (Exists.elim · fun _ hb ↦ ⟨_, add _ _ _ _ ha hb⟩))
      smul_mem' := fun r ↦ (Exists.elim · fun _ hb ↦ ⟨_, smul r _ _ hb⟩)
      zero_mem' := ⟨_, zero⟩ }
  adjoin_le (S := S) (fun y hy ↦ ⟨subset_adjoin R hy, mem y hy⟩) hx |>.elim fun _ ↦ id

@[elab_as_elim]
/-
**NonUnitalAlgebra.adjoin_induction** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`
。
形式化陈述：adjoin_induction {s : Set A} {p : (x : A) -> x in adjoin R s -> Prop} (mem
 : forall (x) (hx : x in s), p x (subset_adjoin R hx)) (add : forall x y hx hy, 
p x hx -> p y hy -> p (x + y) (add_mem hx hy)) (zero : p 0 (zero_mem _)) (mul : 
forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)) (smul : forall 
r x hx, p x hx -> p (r • x) (SMulMemClass.smul_mem r hx)) {x} (hx : x in adjoin 
R s) : p x hx
参数：x : A；mem : forall (x) (hx : x in s), p x (subset_adjoin R hx)；add : forall x
 y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)；zero : p 0 (zero_mem _)；
mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)；smul : for
all r x hx, p x hx -> p (r • x) (SMulMemClass.smul_mem r hx)；hx : x in adjoin R 
s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.subset_adjoin`：subset_adjoin {s : Set A} : s subseteq a
djoin R s
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
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `NonUnitalAlgebra.adjoin_le`：adjoin_le {S : NonUnitalSubalgebra R A} {s :
 Set A} (hs : s subseteq S) : adjoin R s <= S
-/
theorem adjoin_induction₂ {s : Set A} {p : ∀ x y, x ∈ adjoin R s → y ∈ adjoin R s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (subset_adjoin R hx) (subset_adjoin R hy))
    (zero_left : ∀ x hx, p 0 x (zero_mem _) hx) (zero_right : ∀ x hx, p x 0 hx (zero_mem _))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    (smul_left : ∀ r x y hx hy, p x y hx hy → p (r • x) y (SMulMemClass.smul_mem r hx) hy)
    (smul_right : ∀ r x y hx hy, p x y hx hy → p x (r • y) hx (SMulMemClass.smul_mem r hy))
    {x y : A} (hx : x ∈ adjoin R s) (hy : y ∈ adjoin R s) :
    p x y hx hy := by
  induction hy using adjoin_induction with
  | mem z hz =>
    induction hx using adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | zero => exact zero_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | smul _ _ _ h => exact smul_left _ _ _ _ _ h
  | zero => exact zero_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | smul _ _ _ h => exact smul_right _ _ _ _ _ h

open Submodule in
/-
**NonUnitalAlgebra.adjoin_eq_span** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：adjoin_eq_span (s : Set A) : (adjoin R s).toSubmodule = span R (Subsemigro
up.closure s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `NonUnitalAlgebra.adjoin_induction`：adjoin_induction {s : Set A} {p : (x 
: A) -> x in adjoin R s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_ad
join R hx)) (add : fora…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Submodule.span_induction₂`：span_induction₂ {N : Type*} [AddCommMonoid N]
 [Module R N] {t : Set N} {p : (x : M) -> (y : N) -> x in span R s -> y in span 
R t -> Prop} (m…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `NonUnitalAlgebra.subset_adjoin`：subset_adjoin {s : Set A} : s subseteq a
djoin R s
-/
lemma adjoin_eq_span (s : Set A) : (adjoin R s).toSubmodule = span R (Subsemigroup.closure s) := by
  apply le_antisymm
  · intro x hx
    induction hx using adjoin_induction with
    | mem x hx => exact subset_span <| Subsemigroup.subset_closure hx
    | add x y _ _ hpx hpy => exact add_mem hpx hpy
    | zero => exact zero_mem _
    | mul x y _ _ hpx hpy =>
      apply span_induction₂ ?Hs (by simp) (by simp) ?Hadd_l ?Hadd_r ?Hsmul_l ?Hsmul_r hpx hpy
      case Hs => exact fun x y hx hy ↦ subset_span <| mul_mem hx hy
      case Hadd_l => exact fun x y z _ _ _ hxz hyz ↦ by simpa [add_mul] using add_mem hxz hyz
      case Hadd_r => exact fun x y z _ _ _ hxz hyz ↦ by simpa [mul_add] using add_mem hxz hyz
      case Hsmul_l => exact fun r x y _ _ hxy ↦ by simpa [smul_mul_assoc] using smul_mem _ _ hxy
      case Hsmul_r => exact fun r x y _ _ hxy ↦ by simpa [mul_smul_comm] using smul_mem _ _ hxy
    | smul r x _ hpx => exact smul_mem _ _ hpx
  · apply span_le.2 _
    change Subsemigroup.closure s ≤ (adjoin R s).toSubsemigroup
    exact Subsemigroup.closure_le.2 (subset_adjoin R)

variable (R A)

@[simp]
/-
**NonUnitalAlgebra.adjoin_empty** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：adjoin_empty : adjoin R (∅ : Set A) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `NonUnitalAlgebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R A]   [inst_3 :
 IsScalar…
-/
theorem adjoin_empty : adjoin R (∅ : Set A) = ⊥ :=
  show adjoin R ⊥ = ⊥ by apply GaloisConnection.l_bot; exact NonUnitalAlgebra.gc

@[simp]
/-
**NonUnitalAlgebra.adjoin_univ** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：adjoin_univ : adjoin R (Set.univ : Set A) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `NonUnitalAlgebra.subset_adjoin`：subset_adjoin {s : Set A} : s subseteq a
djoin R s
-/
theorem adjoin_univ : adjoin R (Set.univ : Set A) = ⊤ :=
  eq_top_iff.2 fun _x hx => subset_adjoin R hx

open NonUnitalSubalgebra in
/-
**NonUnitalAlgebra._root_.NonUnitalAlgHom.map_adjoin** 是 Mathlib 中的一个引理，位于命名空间 `
NonUnitalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.NonUnitalAlgHom.map_adjoin [IsScalarTower R B B] [SMulCommClass R B B]
    (f : F) (s : Set A) : map f (adjoin R s) = adjoin R (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) NonUnitalAlgebra.gi.gc
    NonUnitalAlgebra.gi.gc fun _t => rfl

open NonUnitalSubalgebra in
@[simp]
/-
**NonUnitalAlgebra._root_.NonUnitalAlgHom.map_adjoin_singleton** 是 Mathlib 中的一个引
理，位于命名空间 `NonUnitalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.NonUnitalAlgHom.map_adjoin_singleton [IsScalarTower R B B] [SMulCommClass R B B]
    (f : F) (x : A) : map f (adjoin R {x}) = adjoin R {f x} := by
  simp [NonUnitalAlgHom.map_adjoin]

variable {R A}

@[simp, norm_cast]
/-
**NonUnitalAlgebra.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：coe_top : (↑(⊤ : NonUnitalSubalgebra R A) : Set A) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : (↑(⊤ : NonUnitalSubalgebra R A) : Set A) = Set.univ :=
  rfl

@[simp]
/-
**NonUnitalAlgebra.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：mem_top {x : A} : x in (⊤ : NonUnitalSubalgebra R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top {x : A} : x ∈ (⊤ : NonUnitalSubalgebra R A) :=
  Set.mem_univ x

@[simp]
/-
**NonUnitalAlgebra.top_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：top_toSubmodule : (⊤ : NonUnitalSubalgebra R A).toSubmodule = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_toSubmodule : (⊤ : NonUnitalSubalgebra R A).toSubmodule = ⊤ :=
  rfl

@[simp]
/-
**NonUnitalAlgebra.top_toNonUnitalSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alAlgebra`。
形式化陈述：top_toNonUnitalSubsemiring : (⊤ : NonUnitalSubalgebra R A).toNonUnitalSubs
emiring = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_toNonUnitalSubsemiring : (⊤ : NonUnitalSubalgebra R A).toNonUnitalSubsemiring = ⊤ :=
  rfl

@[simp]
/-
**NonUnitalAlgebra.toNonUnitalSubring_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAl
gebra`。
形式化陈述：toNonUnitalSubring_top {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A
] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] : (⊤ : NonUnitalSubal
gebra R A).toNonUnitalSubring = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNonUnitalSubring_top {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] :
    (⊤ : NonUnitalSubalgebra R A).toNonUnitalSubring = ⊤ :=
  rfl

@[deprecated (since := "2026-01-03")] alias top_toSubring := toNonUnitalSubring_top
/-
**NonUnitalAlgebra.toNonUnitalSubsemiring_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalAlgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNon
AssocSemiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] [
inst_4 : SMulCommClass R A A] {S : NonUnitalSubalgebra R A},   S.toNonUnitalSubs
emiring = ⊤ ↔ S = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toNonUnitalSubsemiring_eq_top {S : NonUnitalSubalgebra R A} :
    S.toNonUnitalSubsemiring = ⊤ ↔ S = ⊤ := by simp [← SetLike.coe_set_eq]

-- This lemma isn't simp because `NonUnitalSubalgebra.toSubmodule` is reducible.
/-
**NonUnitalAlgebra.toSubmodule_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalAlgebr
a`。
形式化陈述：toSubmodule_eq_top {S : NonUnitalSubalgebra R A} : S.toSubmodule = ⊤ ↔ S =
 ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubalgebra.smul_mem'`：∀ {R : Type u} {A : Type v} [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R A]  
 (self : NonUnitalS…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toSubmodule_eq_top {S : NonUnitalSubalgebra R A} : S.toSubmodule = ⊤ ↔ S = ⊤ := by simp

@[simp]
/-
**NonUnitalAlgebra.toNonUnitalSubring_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnita
lAlgebra`。
形式化陈述：toNonUnitalSubring_eq_top {R A : Type*} [CommRing R] [Ring A] [Algebra R A
] {S : NonUnitalSubalgebra R A} : S.toNonUnitalSubring = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toNonUnitalSubring_eq_top {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {S : NonUnitalSubalgebra R A} : S.toNonUnitalSubring = ⊤ ↔ S = ⊤ := by
  simp [← SetLike.coe_set_eq]

@[deprecated (since := "2026-01-01")] alias to_subring_eq_top := toNonUnitalSubring_eq_top
/-
**NonUnitalAlgebra.mem_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：mem_sup_left {S T : NonUnitalSubalgebra R A} : forall {x : A}, x in S -> x
 in S ⊔ T
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
theorem mem_sup_left {S T : NonUnitalSubalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T := by
  rw [← SetLike.le_def]
  exact le_sup_left
/-
**NonUnitalAlgebra.mem_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：mem_sup_right {S T : NonUnitalSubalgebra R A} : forall {x : A}, x in T -> 
x in S ⊔ T
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
theorem mem_sup_right {S T : NonUnitalSubalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T := by
  rw [← SetLike.le_def]
  exact le_sup_right
/-
**NonUnitalAlgebra.mul_mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：mul_mem_sup {S T : NonUnitalSubalgebra R A} {x y : A} (hx : x in S) (hy : 
y in T) : x * y in S ⊔ T
参数：hx : x in S；hy : y in T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `NonUnitalAlgebra.mem_sup_left`：mem_sup_left {S T : NonUnitalSubalgebra R
 A} : forall {x : A}, x in S -> x in S ⊔ T
· 使用定理 `NonUnitalAlgebra.mem_sup_right`：mem_sup_right {S T : NonUnitalSubalgebra
 R A} : forall {x : A}, x in T -> x in S ⊔ T
-/
theorem mul_mem_sup {S T : NonUnitalSubalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
    x * y ∈ S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)
/-
**NonUnitalAlgebra.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：map_sup [IsScalarTower R B B] [SMulCommClass R B B] (f : F) (S T : NonUnit
alSubalgebra R A) : ((S ⊔ T).map f : NonUnitalSubalgebra R B) = S.map f ⊔ T.map 
f
参数：f : F；S T : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `NonUnitalSubalgebra.gc_map_comap`：gc_map_comap (f : F) : GaloisConnectio
n (map f : NonUnitalSubalgebra R A -> NonUnitalSubalgebra R B) (comap f)
-/
theorem map_sup [IsScalarTower R B B] [SMulCommClass R B B]
    (f : F) (S T : NonUnitalSubalgebra R A) :
    ((S ⊔ T).map f : NonUnitalSubalgebra R B) = S.map f ⊔ T.map f :=
  (NonUnitalSubalgebra.gc_map_comap f).l_sup
/-
**NonUnitalAlgebra.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：map_inf [IsScalarTower R B B] [SMulCommClass R B B] (f : F) (hf : Function
.Injective f) (S T : NonUnitalSubalgebra R A) : ((S ⊓ T).map f : NonUnitalSubalg
ebra R B) = S.map f ⊓ T.map f
参数：f : F；hf : Function.Injective f；S T : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
-/
theorem map_inf [IsScalarTower R B B] [SMulCommClass R B B]
    (f : F) (hf : Function.Injective f) (S T : NonUnitalSubalgebra R A) :
    ((S ⊓ T).map f : NonUnitalSubalgebra R B) = S.map f ⊓ T.map f :=
  SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]
/-
**NonUnitalAlgebra.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：coe_inf (S T : NonUnitalSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Set A)
 inter T
参数：S T : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (S T : NonUnitalSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Set A) ∩ T :=
  rfl

@[simp]
/-
**NonUnitalAlgebra.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：mem_inf {S T : NonUnitalSubalgebra R A} {x : A} : x in S ⊓ T ↔ x in S ∧ x 
in T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {S T : NonUnitalSubalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

@[simp]
/-
**NonUnitalAlgebra.inf_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：inf_toSubmodule (S T : NonUnitalSubalgebra R A) : (S ⊓ T).toSubmodule = S.
toSubmodule ⊓ T.toSubmodule
参数：S T : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_toSubmodule (S T : NonUnitalSubalgebra R A) :
    (S ⊓ T).toSubmodule = S.toSubmodule ⊓ T.toSubmodule :=
  rfl

@[simp]
/-
**NonUnitalAlgebra.inf_toNonUnitalSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alAlgebra`。
形式化陈述：inf_toNonUnitalSubsemiring (S T : NonUnitalSubalgebra R A) : (S ⊓ T).toNon
UnitalSubsemiring = S.toNonUnitalSubsemiring ⊓ T.toNonUnitalSubsemiring
参数：S T : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_toNonUnitalSubsemiring (S T : NonUnitalSubalgebra R A) :
    (S ⊓ T).toNonUnitalSubsemiring = S.toNonUnitalSubsemiring ⊓ T.toNonUnitalSubsemiring :=
  rfl

@[simp, norm_cast]
/-
**NonUnitalAlgebra.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：coe_sInf (S : Set (NonUnitalSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s i
n S, ↑s
参数：S : Set (NonUnitalSubalgebra R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
s : Set β} {f : β → α}, sInf (f '' s) = ⨅ a ∈ s, f a
-/
theorem coe_sInf (S : Set (NonUnitalSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s :=
  sInf_image

@[simp]
/-
**NonUnitalAlgebra.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：mem_sInf {S : Set (NonUnitalSubalgebra R A)} {x : A} : x in sInf S ↔ foral
l p in S, x in p
参数：NonUnitalSubalgebra R A。
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
· 使用定理 `NonUnitalAlgebra.coe_sInf`：coe_sInf (S : Set (NonUnitalSubalgebra R A)) 
: (↑(sInf S) : Set A) = ⋂ s in S, ↑s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sInf {S : Set (NonUnitalSubalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]
/-
**NonUnitalAlgebra.sInf_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`
。
形式化陈述：sInf_toSubmodule (S : Set (NonUnitalSubalgebra R A)) : (sInf S).toSubmodul
e = sInf (NonUnitalSubalgebra.toSubmodule '' S)
参数：S : Set (NonUnitalSubalgebra R A)。
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
theorem sInf_toSubmodule (S : Set (NonUnitalSubalgebra R A)) :
    (sInf S).toSubmodule = sInf (NonUnitalSubalgebra.toSubmodule '' S) :=
  SetLike.coe_injective <| by simp

@[simp]
/-
**NonUnitalAlgebra.sInf_toNonUnitalSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `NonUni
talAlgebra`。
形式化陈述：sInf_toNonUnitalSubsemiring (S : Set (NonUnitalSubalgebra R A)) : (sInf S)
.toNonUnitalSubsemiring = sInf (NonUnitalSubalgebra.toNonUnitalSubsemiring '' S)
参数：S : Set (NonUnitalSubalgebra R A)。
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
theorem sInf_toNonUnitalSubsemiring (S : Set (NonUnitalSubalgebra R A)) :
    (sInf S).toNonUnitalSubsemiring = sInf (NonUnitalSubalgebra.toNonUnitalSubsemiring '' S) :=
  SetLike.coe_injective <| by simp

@[simp, norm_cast]
/-
**NonUnitalAlgebra.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：coe_iInf {ι : Sort*} {S : ι -> NonUnitalSubalgebra R A} : (↑(⨅ i, S i) : S
et A) = ⋂ i, S i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf {ι : Sort*} {S : ι → NonUnitalSubalgebra R A} :
    (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by simp [iInf]

@[simp]
/-
**NonUnitalAlgebra.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：mem_iInf {ι : Sort*} {S : ι -> NonUnitalSubalgebra R A} {x : A} : x in ⨅ i
, S i ↔ forall i, x in S i
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
theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalSubalgebra R A} {x : A} :
    x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_mem_range]
/-
**NonUnitalAlgebra.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：map_iInf {ι : Sort*} [Nonempty ι] [IsScalarTower R B B] [SMulCommClass R B
 B] (f : F) (hf : Function.Injective f) (S : ι -> NonUnitalSubalgebra R A) : ((⨅
 i, S i).map f : NonUnitalSubalgebra R B) = ⨅ i, (S i).map f
参数：f : F；hf : Function.Injective f；S : ι -> NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalAlgebra.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> NonUnitalSubal
gebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
-/
theorem map_iInf {ι : Sort*} [Nonempty ι]
    [IsScalarTower R B B] [SMulCommClass R B B] (f : F)
    (hf : Function.Injective f) (S : ι → NonUnitalSubalgebra R A) :
    ((⨅ i, S i).map f : NonUnitalSubalgebra R B) = ⨅ i, (S i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ S)

@[simp]
/-
**NonUnitalAlgebra.iInf_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`
。
形式化陈述：iInf_toSubmodule {ι : Sort*} (S : ι -> NonUnitalSubalgebra R A) : (⨅ i, S 
i).toSubmodule = ⨅ i, (S i).toSubmodule
参数：S : ι -> NonUnitalSubalgebra R A。
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
· 使用定理 `NonUnitalAlgebra.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> NonUnitalSubal
gebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i
· 使用定理 `Submodule.coe_iInf`：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i)
 : Set M) = ⋂ i, ↑(p i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInf_toSubmodule {ι : Sort*} (S : ι → NonUnitalSubalgebra R A) :
    (⨅ i, S i).toSubmodule = ⨅ i, (S i).toSubmodule :=
  SetLike.coe_injective <| by simp
/-
**NonUnitalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (NonUnitalSubalgebra R A) :=
  ⟨⊥⟩
/-
**NonUnitalAlgebra.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：mem_bot {x : A} : x in (⊥ : NonUnitalSubalgebra R A) ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubsemiring.closure_empty`：closure_empty : closure (∅ : Set R) 
= ⊥
· 使用定理 `NonUnitalSubsemiring.coe_bot`：coe_bot : ((⊥ : NonUnitalSubsemiring R) : 
Set R) = {0}
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_bot {x : A} : x ∈ (⊥ : NonUnitalSubalgebra R A) ↔ x = 0 :=
  show x ∈ Submodule.span R (NonUnitalSubsemiring.closure (∅ : Set A) : Set A) ↔ x = 0 by
    rw [NonUnitalSubsemiring.closure_empty, NonUnitalSubsemiring.coe_bot,
      Submodule.span_zero_singleton, Submodule.mem_bot]
/-
**NonUnitalAlgebra.toSubmodule_bot** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：toSubmodule_bot : (⊥ : NonUnitalSubalgebra R A).toSubmodule = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toSubmodule_bot : (⊥ : NonUnitalSubalgebra R A).toSubmodule = ⊥ := by
  ext
  simp only [mem_bot, NonUnitalSubalgebra.mem_toSubmodule, Submodule.mem_bot]

@[simp, norm_cast]
/-
**NonUnitalAlgebra.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：coe_bot : ((⊥ : NonUnitalSubalgebra R A) : Set A) = {0}
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
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coe_bot : ((⊥ : NonUnitalSubalgebra R A) : Set A) = {0} := by
  simp [Set.ext_iff, NonUnitalAlgebra.mem_bot]
/-
**NonUnitalAlgebra.eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：eq_top_iff {S : NonUnitalSubalgebra R A} : S = ⊤ ↔ forall x : A, x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalAlgebra.mem_top`：mem_top {x : A} : x in (⊤ : NonUnitalSubalgebr
a R A)
· 使用定理 `NonUnitalSubalgebra.ext`：ext {S T : NonUnitalSubalgebra R A} (h : forall
 x : A, x in S ↔ x in T) : S = T
-/
theorem eq_top_iff {S : NonUnitalSubalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h]; exact mem_top, fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

@[simp]
/-
**NonUnitalAlgebra.range_id** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：range_id : NonUnitalAlgHom.range (NonUnitalAlgHom.id R A) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
-/
theorem range_id : NonUnitalAlgHom.range (NonUnitalAlgHom.id R A) = ⊤ :=
  SetLike.coe_injective Set.range_id

@[simp]
/-
**NonUnitalAlgebra.map_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：map_top (f : A ->ₙₐ[R] B) : (⊤ : NonUnitalSubalgebra R A).map f = NonUnita
lAlgHom.range f
参数：f : A ->ₙₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
theorem map_top (f : A →ₙₐ[R] B) : (⊤ : NonUnitalSubalgebra R A).map f = NonUnitalAlgHom.range f :=
  SetLike.coe_injective Set.image_univ

@[simp]
/-
**NonUnitalAlgebra.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：map_bot [IsScalarTower R B B] [SMulCommClass R B B] (f : A ->ₙₐ[R] B) : (⊥
 : NonUnitalSubalgebra R A).map f = ⊥
参数：f : A ->ₙₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalAlgebra.coe_bot`：coe_bot : ((⊥ : NonUnitalSubalgebra R A) : Set
 A) = {0}
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
theorem map_bot [IsScalarTower R B B] [SMulCommClass R B B]
    (f : A →ₙₐ[R] B) : (⊥ : NonUnitalSubalgebra R A).map f = ⊥ :=
  SetLike.coe_injective <| by simp [NonUnitalAlgebra.coe_bot, NonUnitalSubalgebra.coe_map]

@[simp]
/-
**NonUnitalAlgebra.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：comap_top [IsScalarTower R B B] [SMulCommClass R B B] (f : A ->ₙₐ[R] B) : 
(⊤ : NonUnitalSubalgebra R B).comap f = ⊤
参数：f : A ->ₙₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalAlgebra.eq_top_iff`：eq_top_iff {S : NonUnitalSubalgebra R A} : 
S = ⊤ ↔ forall x : A, x in S
· 使用定理 `NonUnitalAlgebra.mem_top`：mem_top {x : A} : x in (⊤ : NonUnitalSubalgebr
a R A)
-/
theorem comap_top [IsScalarTower R B B] [SMulCommClass R B B]
    (f : A →ₙₐ[R] B) : (⊤ : NonUnitalSubalgebra R B).comap f = ⊤ :=
  eq_top_iff.2 fun _ => mem_top

/-- `NonUnitalAlgHom` to `⊤ : NonUnitalSubalgebra R A`. -/
/-
**NonUnitalAlgebra.toTop** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：toTop : A ->ₙₐ[R] (⊤ : NonUnitalSubalgebra R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonUnitalAlgHom` to `⊤ : NonUnitalSubalgebra R A`.
-/
def toTop : A →ₙₐ[R] (⊤ : NonUnitalSubalgebra R A) :=
  NonUnitalAlgHom.codRestrict (NonUnitalAlgHom.id R A) ⊤ fun _ => mem_top

end IsScalarTower

/-
**NonUnitalAlgebra.range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：range_eq_top [IsScalarTower R B B] [SMulCommClass R B B] (f : A ->ₙₐ[R] B)
 : NonUnitalAlgHom.range f = (⊤ : NonUnitalSubalgebra R B) ↔ Function.Surjective
 f
参数：f : A ->ₙₐ[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.eq_top_iff`：eq_top_iff {S : NonUnitalSubalgebra R A} : 
S = ⊤ ↔ forall x : A, x in S
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
-/
theorem range_eq_top [IsScalarTower R B B] [SMulCommClass R B B] (f : A →ₙₐ[R] B) :
    NonUnitalAlgHom.range f = (⊤ : NonUnitalSubalgebra R B) ↔ Function.Surjective f :=
  NonUnitalAlgebra.eq_top_iff

end NonUnitalAlgebra

namespace NonUnitalSubalgebra

open NonUnitalAlgebra

section NonAssoc

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A]
variable (S : NonUnitalSubalgebra R A)

/-
**NonUnitalSubalgebra.range_val** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：range_val : NonUnitalAlgHom.range (NonUnitalSubalgebraClass.subtype S) = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.ext`：ext {S T : NonUnitalSubalgebra R A} (h : forall
 x : A, x in S ↔ x in T) : S = T
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NonUnitalAlgHom.coe_range`：coe_range (φ : F) : ((NonUnitalAlgHom.range φ
 : NonUnitalSubalgebra R B) : Set B) = Set.range (φ : A -> B)
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
theorem range_val : NonUnitalAlgHom.range (NonUnitalSubalgebraClass.subtype S) = S :=
  ext <| Set.ext_iff.1 <|
    (NonUnitalAlgHom.coe_range <| NonUnitalSubalgebraClass.subtype S).trans Subtype.range_val
/-
**NonUnitalSubalgebra.subsingleton_of_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `No
nUnitalSubalgebra`。
形式化陈述：subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (NonUnitalSub
algebra R A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.ext`：ext {S T : NonUnitalSubalgebra R A} (h : forall
 x : A, x in S ↔ x in T) : S = T
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
instance subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (NonUnitalSubalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩

variable [NonUnitalNonAssocSemiring B] [Module R B]

section Prod

variable (S₁ : NonUnitalSubalgebra R B)

/-- The product of two non-unital subalgebras is a non-unital subalgebra. -/
/-
**NonUnitalSubalgebra.prod** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：prod : NonUnitalSubalgebra R (A × B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two non-unital subalgebras is a non-unital subalgebra.
-/
def prod : NonUnitalSubalgebra R (A × B) :=
  { S.toNonUnitalSubsemiring.prod S₁.toNonUnitalSubsemiring with
    carrier := S ×ˢ S₁
    smul_mem' := fun r _x hx => ⟨SMulMemClass.smul_mem r hx.1, SMulMemClass.smul_mem r hx.2⟩ }

@[simp, norm_cast]
/-
**NonUnitalSubalgebra.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ S₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ S₁ :=
  rfl
/-
**NonUnitalSubalgebra.prod_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubal
gebra`。
形式化陈述：prod_toSubmodule : (S.prod S₁).toSubmodule = S.toSubmodule.prod S₁.toSubmo
dule
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_toSubmodule : (S.prod S₁).toSubmodule = S.toSubmodule.prod S₁.toSubmodule :=
  rfl

@[simp]
/-
**NonUnitalSubalgebra.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：mem_prod {S : NonUnitalSubalgebra R A} {S₁ : NonUnitalSubalgebra R B} {x :
 A × B} : x in prod S S₁ ↔ x.1 in S ∧ x.2 in S₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_prod`：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
-/
theorem mem_prod {S : NonUnitalSubalgebra R A} {S₁ : NonUnitalSubalgebra R B} {x : A × B} :
    x ∈ prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ :=
  Set.mem_prod
/-
**NonUnitalSubalgebra.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：prod_mono {S T : NonUnitalSubalgebra R A} {S₁ T₁ : NonUnitalSubalgebra R B
} : S <= T -> S₁ <= T₁ -> prod S S₁ <= prod T T₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono {S T : NonUnitalSubalgebra R A} {S₁ T₁ : NonUnitalSubalgebra R B} :
    S ≤ T → S₁ ≤ T₁ → prod S S₁ ≤ prod T T₁ :=
  Set.prod_mono

variable [IsScalarTower R A A] [SMulCommClass R A A] [IsScalarTower R B B] [SMulCommClass R B B]

@[simp]
/-
**NonUnitalSubalgebra.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：prod_top : (prod ⊤ ⊤ : NonUnitalSubalgebra R (A × B)) = ⊤
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
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_top : (prod ⊤ ⊤ : NonUnitalSubalgebra R (A × B)) = ⊤ := by ext; simp

@[simp]
/-
**NonUnitalSubalgebra.prod_inf_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgeb
ra`。
形式化陈述：prod_inf_prod {S T : NonUnitalSubalgebra R A} {S₁ T₁ : NonUnitalSubalgebra
 R B} : S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.prod_inter_prod`：prod_inter_prod : s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ int
er s₂) ×ˢ (t₁ inter t₂)
-/
theorem prod_inf_prod {S T : NonUnitalSubalgebra R A} {S₁ T₁ : NonUnitalSubalgebra R B} :
    S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
  SetLike.coe_injective Set.prod_inter_prod

end Prod


/-- The map `S → T` when `S` is a non-unital subalgebra contained in the non-unital subalgebra `T`.

This is the non-unital subalgebra version of `Submodule.inclusion`, or `Subring.inclusion` -/
/-
**NonUnitalSubalgebra.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：inclusion {S T : NonUnitalSubalgebra R A} (h : S <= T) : S ->ₙₐ[R] T where
 toFun
参数：h : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `S → T` when `S` is a non-unital subalgebra contained in the non-unital 
subalgebra `T`.

This is the non-unital subalgebra version of `Submodule.inclusion`, or `Subring.
inclusion`
-/
def inclusion {S T : NonUnitalSubalgebra R A} (h : S ≤ T) : S →ₙₐ[R] T where
  toFun := Set.inclusion h
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_smul' _ _ := rfl
/-
**NonUnitalSubalgebra.inclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
balgebra`。
形式化陈述：inclusion_injective {S T : NonUnitalSubalgebra R A} (h : S <= T) : Functio
n.Injective (inclusion h)
参数：h : S <= T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.mk.inj`：∀ {α : Sort u} {p : α → Prop} {val : α} {property : p va
l} {val_1 : α} {property_1 : p val_1},   ⟨val, property⟩ = ⟨val_1, property_1⟩ →
 val…
-/
theorem inclusion_injective {S T : NonUnitalSubalgebra R A} (h : S ≤ T) :
    Function.Injective (inclusion h) := fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]
/-
**NonUnitalSubalgebra.inclusion_self** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalge
bra`。
形式化陈述：inclusion_self {S : NonUnitalSubalgebra R A} : inclusion (le_refl S) = Non
UnitalAlgHom.id R S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem inclusion_self {S : NonUnitalSubalgebra R A} :
    inclusion (le_refl S) = NonUnitalAlgHom.id R S :=
  rfl

@[simp]
/-
**NonUnitalSubalgebra.inclusion_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebr
a`。
形式化陈述：inclusion_mk {S T : NonUnitalSubalgebra R A} (h : S <= T) (x : A) (hx : x 
in S) : inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩
参数：h : S <= T；x : A；hx : x in S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_mk {S T : NonUnitalSubalgebra R A} (h : S ≤ T) (x : A) (hx : x ∈ S) :
    inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl
/-
**NonUnitalSubalgebra.inclusion_right** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalg
ebra`。
形式化陈述：inclusion_right {S T : NonUnitalSubalgebra R A} (h : S <= T) (x : T) (m : 
(x : A) in S) : inclusion h ⟨x, m⟩ = x
参数：h : S <= T；x : T；m : (x : A) in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem inclusion_right {S T : NonUnitalSubalgebra R A} (h : S ≤ T) (x : T) (m : (x : A) ∈ S) :
    inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl

@[simp]
/-
**NonUnitalSubalgebra.inclusion_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
balgebra`。
形式化陈述：inclusion_inclusion {S T U : NonUnitalSubalgebra R A} (hst : S <= T) (htu 
: T <= U) (x : S) : inclusion htu (inclusion hst x) = inclusion (le_trans hst ht
u) x
参数：hst : S <= T；htu : T <= U；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem inclusion_inclusion {S T U : NonUnitalSubalgebra R A} (hst : S ≤ T) (htu : T ≤ U) (x : S) :
    inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
  Subtype.ext rfl

@[simp]
/-
**NonUnitalSubalgebra.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgeb
ra`。
形式化陈述：coe_inclusion {S T : NonUnitalSubalgebra R A} (h : S <= T) (s : S) : (incl
usion h s : A) = s
参数：h : S <= T；s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inclusion {S T : NonUnitalSubalgebra R A} (h : S ≤ T) (s : S) :
    (inclusion h s : A) = s :=
  rfl

variable [IsScalarTower R A A] [SMulCommClass R A A]
/-
**NonUnitalSubalgebra._root_.NonUnitalAlgHom.subsingleton** 是 Mathlib 中的一个实例，位于命
名空间 `NonUnitalSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.NonUnitalAlgHom.subsingleton [Subsingleton (NonUnitalSubalgebra R A)] :
    Subsingleton (A →ₙₐ[R] B) :=
  ⟨fun f g =>
    NonUnitalAlgHom.ext fun a =>
      have : a ∈ (⊥ : NonUnitalSubalgebra R A) :=
        Subsingleton.elim (⊤ : NonUnitalSubalgebra R A) ⊥ ▸ mem_top
      (mem_bot.mp this).symm ▸ (map_zero f).trans (map_zero g).symm⟩

section SuprLift

variable {ι : Sort*}

/-
**NonUnitalSubalgebra.coe_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalS
ubalgebra`。
形式化陈述：coe_iSup_of_directed [Nonempty ι] {S : ι -> NonUnitalSubalgebra R A} (dir 
: Directed (· <= ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A)
参数：dir : Directed (· <= ·) S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalSubsemiring.coe_iSup_of_directed`：coe_iSup_of_directed {ι} [hι 
: Nonempty ι] {S : ι -> NonUnitalSubsemiring R} (hS : Directed (· <= ·) S) : ((⨆
 i, S i : NonUnitalSubsemiring …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubalgebra.smul_mem'`：∀ {R : Type u} {A : Type v} [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : _root_.Module R A]  
 (self : NonUnitalS…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
-/
theorem coe_iSup_of_directed [Nonempty ι] {S : ι → NonUnitalSubalgebra R A}
    (dir : Directed (· ≤ ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A) :=
  let K : NonUnitalSubalgebra R A :=
    { __ := NonUnitalSubsemiring.copy _ _ (NonUnitalSubsemiring.coe_iSup_of_directed dir).symm
      smul_mem' := fun r _x hx ↦
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, (S i).smul_mem' r hi⟩ }
  have : iSup S = K := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (S i : Set A)) i) (Set.iUnion_subset fun _ ↦ le_iSup S _)
  this.symm ▸ rfl
/-
**NonUnitalSubalgebra.isMulCommutative_iSup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
Subalgebra`。
形式化陈述：isMulCommutative_iSup {ι : Sort*} [Nonempty ι] {S : ι -> NonUnitalSubalgeb
ra R A} [hS : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) : Is
MulCommutative (⨆ i, S i : NonUnitalSubalgebra R A)
参数：S i；dir : Directed (· <= ·) S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
· 使用定理 `NonUnitalSubsemiring.isMulCommutative_iSup`：isMulCommutative_iSup {ι : S
ort*} [Nonempty ι] {S : ι -> NonUnitalSubsemiring R} [hS : forall i, IsMulCommut
ative (S i)] (dir : Directed (· …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubalgebra.coe_iSup_of_directed`：coe_iSup_of_directed [Nonempty
 ι] {S : ι -> NonUnitalSubalgebra R A} (dir : Directed (· <= ·) S) : ↑(iSup S) =
 ⋃ i, (S i : Set A)
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
· 使用定理 `NonUnitalSubsemiring.coe_iSup_of_directed`：coe_iSup_of_directed {ι} [hι 
: Nonempty ι] {S : ι -> NonUnitalSubsemiring R} (hS : Directed (· <= ·) S) : ((⨆
 i, S i : NonUnitalSubsemiring …
-/
theorem isMulCommutative_iSup {ι : Sort*} [Nonempty ι] {S : ι → NonUnitalSubalgebra R A}
    [hS : ∀ i, IsMulCommutative (S i)] (dir : Directed (· ≤ ·) S) :
    IsMulCommutative (⨆ i, S i : NonUnitalSubalgebra R A) := by
  have := NonUnitalSubsemiring.isMulCommutative_iSup dir
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    NonUnitalSubsemiring.coe_iSup_of_directed dir]
/-
**NonUnitalSubalgebra.instIsMulCommutative_iSup** 是 Mathlib 中的一个实例，位于命名空间 `NonUn
italSubalgebra`。
形式化陈述：instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirecte
dOrder ι] {S : ι ->o NonUnitalSubalgebra R A} [hS : forall i, IsMulCommutative (
S i)] : IsMulCommutative (⨆ i, S i : NonUnitalSubalgebra R A)
参数：S i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.isMulCommutative_iSup`：isMulCommutative_iSup {ι : So
rt*} [Nonempty ι] {S : ι -> NonUnitalSubalgebra R A} [hS : forall i, IsMulCommut
ative (S i)] (dir : Directed (·…
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
instance instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o NonUnitalSubalgebra R A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : NonUnitalSubalgebra R A) :=
  isMulCommutative_iSup S.monotone.directed_le

/-- Define an algebra homomorphism on a directed supremum of non-unital subalgebras by defining
it on each non-unital subalgebra, and proving that it agrees on the intersection of
non-unital subalgebras. -/
/-
**NonUnitalSubalgebra.iSupLift** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：iSupLift [Nonempty ι] (K : ι -> NonUnitalSubalgebra R A) (dir : Directed (
· <= ·) K) (f : forall i, K i ->ₙₐ[R] B) (hf : forall (i j : ι) (h : K i <= K j)
, f i = (f j).comp (inclusion h)) (T : NonUnitalSubalgebra R A) (hT : T = iSup K
) : ↥T ->ₙₐ[R] B
参数：K : ι -> NonUnitalSubalgebra R A；dir : Directed (· <= ·) K；f : forall i, K i 
->ₙₐ[R] B；hf : forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h)
；T : NonUnitalSubalgebra R A；hT : T = iSup K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define an algebra homomorphism on a directed supremum of non-unital subalgebras 
by defining
it on each non-unital subalgebra, and proving that it agrees on the intersection
 of
non-unital subalgebras.
-/
noncomputable def iSupLift [Nonempty ι] (K : ι → NonUnitalSubalgebra R A) (dir : Directed (· ≤ ·) K)
    (f : ∀ i, K i →ₙₐ[R] B) (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
    (T : NonUnitalSubalgebra R A) (hT : T = iSup K) : ↥T →ₙₐ[R] B := by
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
          dsimp
          exact Set.iUnionLift_const _ (fun i : ι => (0 : K i)) (fun _ => rfl) _ (by simp)
        map_mul' := by
          dsimp
          apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· * ·))
          all_goals simp
        map_add' := by
          dsimp
          apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· + ·))
          all_goals simp
        map_smul' := fun r => by
          dsimp
          apply Set.iUnionLift_unary (coe_iSup_of_directed dir) _ (fun _ x => r • x)
            (fun _ _ => rfl)
          all_goals simp }

variable [Nonempty ι] {K : ι → NonUnitalSubalgebra R A} {dir : Directed (· ≤ ·) K}
  {f : ∀ i, K i →ₙₐ[R] B} {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
  {T : NonUnitalSubalgebra R A} {hT : T = iSup K}

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**NonUnitalSubalgebra.iSupLift_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSub
algebra`。
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
**NonUnitalSubalgebra.iSupLift_comp_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alSubalgebra`。
形式化陈述：iSupLift_comp_inclusion {i : ι} (h : K i <= T) : (iSupLift K dir f hf T hT
).comp (inclusion h) = f i
参数：h : K i <= T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHom.ext`：ext {f g : A ->ₛₙₐ[φ] B} (h : forall x, f x = g x) 
: f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubalgebra.iSupLift_inclusion`：iSupLift_inclusion {i : ι} (x : 
K i) (h : K i <= T) : iSupLift K dir f hf T hT (inclusion h x) = f i x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSupLift_comp_inclusion {i : ι} (h : K i ≤ T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by
  ext
  simp only [NonUnitalAlgHom.comp_apply, iSupLift_inclusion]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**NonUnitalSubalgebra.iSupLift_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra
`。
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
**NonUnitalSubalgebra.iSupLift_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalg
ebra`。
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

end SuprLift

end NonAssoc

section Center

section NonUnitalNonAssocSemiring
variable {R A : Type*}
variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-
**NonUnitalSubalgebra._root_.Set.smul_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.smul_mem_center (r : R) {a : A} (ha : a ∈ Set.center A) :
    r • a ∈ Set.center A where
  comm b := by rw [commute_iff_eq, mul_smul_comm, smul_mul_assoc, ha.comm]
  left_assoc b c := by rw [smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, ha.left_assoc]
  right_assoc b c := by
    rw [mul_smul_comm, mul_smul_comm, mul_smul_comm, ha.right_assoc]

variable (R A) in
/-- The center of a non-unital algebra is the set of elements which commute with every element.
They form a non-unital subalgebra. -/
/-
**NonUnitalSubalgebra.center** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：center : NonUnitalSubalgebra R A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_center`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemirin
g R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A] [IsSc
alarTower…

--- 原说明 ---
The center of a non-unital algebra is the set of elements which commute with eve
ry element.
They form a non-unital subalgebra.
-/
def center : NonUnitalSubalgebra R A :=
  { NonUnitalSubsemiring.center A with smul_mem' := Set.smul_mem_center }

@[norm_cast]
/-
**NonUnitalSubalgebra.coe_center** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra`
。
形式化陈述：coe_center : (center R A : Set A) = Set.center A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_center : (center R A : Set A) = Set.center A :=
  rfl

/-- The center of a non-unital algebra is commutative and associative -/
/-
**NonUnitalSubalgebra.center.instNonUnitalCommSemiring** 是 Mathlib 中的一个定义，位于命名空间
 `NonUnitalSubalgebra.center`。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     [inst : CommSemiring R] →       [i
nst_1 : NonUnitalNonAssocSemiring A] →         [inst_2 : _root_.Module R A] →   
        [inst_3 : IsScalarTower R A A] →             [inst_4 : SMulCommClass R A
 A] → NonUnitalCommSemiring ↥(NonUnitalSubalgebra.center R A)
参数：NonUnitalSubalgebra.center R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a non-unital algebra is commutative and associative
-/
instance center.instNonUnitalCommSemiring : NonUnitalCommSemiring (center R A) :=
  inferInstanceAs <| NonUnitalCommSemiring (NonUnitalSubsemiring.center A)
/-
**NonUnitalSubalgebra.center.instNonUnitalCommRing** 是 Mathlib 中的一个定义，位于命名空间 `No
nUnitalSubalgebra.center`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     {A : Type u_3} →       [i
nst_1 : NonUnitalNonAssocRing A] →         [inst_2 : _root_.Module R A] →       
    [inst_3 : IsScalarTower R A A] →             [inst_4 : SMulCommClass R A A] 
→ NonUnitalCommRing ↥(NonUnitalSubalgebra.center R A)
参数：NonUnitalSubalgebra.center R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance center.instNonUnitalCommRing {A : Type*} [NonUnitalNonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : NonUnitalCommRing (center R A) :=
  inferInstanceAs <| NonUnitalCommRing (NonUnitalSubring.center A)

@[simp]
/-
**NonUnitalSubalgebra.center_toNonUnitalSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `N
onUnitalSubalgebra`。
形式化陈述：center_toNonUnitalSubsemiring : (center R A).toNonUnitalSubsemiring = NonU
nitalSubsemiring.center A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem center_toNonUnitalSubsemiring :
    (center R A).toNonUnitalSubsemiring = NonUnitalSubsemiring.center A :=
  rfl
/-
**NonUnitalSubalgebra.center_toNonUnitalSubring** 是 Mathlib 中的一个定理，位于命名空间 `NonUn
italSubalgebra`。
形式化陈述：∀ (R : Type u_3) (A : Type u_4) [inst : CommRing R] [inst_1 : NonUnitalNon
AssocRing A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] [inst
_4 : SMulCommClass R A A],   (NonUnitalSubalgebra.center R A).toNonUnitalSubring
 = NonUnitalSubring.center A
参数：R : Type u_3；A : Type u_4；NonUnitalSubalgebra.center R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma center_toNonUnitalSubring (R A : Type*) [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    (center R A).toNonUnitalSubring = NonUnitalSubring.center A :=
  rfl
/-
**NonUnitalSubalgebra.center_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgebra
`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : NonUnita
lNonAssocSemiring A]   [inst_2 : _root_.Module R A] [inst_3 : IsScalarTower R A 
A] [inst_4 : SMulCommClass R A A] {B : Type u_3}   [inst_5 : NonUnitalNonAssocSe
miring B] [inst_6 : _root_.Module R B] [inst_7 : IsScalarTower R B B]   [inst_8 
: SMulCommClass R B B],   NonUnitalSubalgebra.center R (A × B) = (NonUnitalSubal
gebra.center R A).prod (NonUnitalSubalgebra.center R B)
参数：A × B；NonUnitalSubalgebra.center R A；NonUnitalSubalgebra.center R B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_prod`：∀ {M : Type u_1} [inst : Mul M] {N : Type u_2} [inst_1 
: Mul N], Set.center (M × N) = Set.center M ×ˢ Set.center N
-/
protected theorem center_prod {B : Type*} [NonUnitalNonAssocSemiring B] [Module R B]
    [IsScalarTower R B B] [SMulCommClass R B B] :
    center R (A × B) = prod (center R A) (center R B) :=
  SetLike.coe_injective Set.center_prod

end NonUnitalNonAssocSemiring

variable (R A : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

-- no instance diamond, as the `npow` field isn't present in the non-unital case.
/-
**NonUnitalSubalgebra.** 是 Mathlib 中的一个示例，位于命名空间 `NonUnitalSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : center.instNonUnitalCommSemiring.toNonUnitalSemiring =
    NonUnitalSubsemiringClass.toNonUnitalSemiring (center R A) := by
  with_reducible_and_instances rfl

@[simp]
/-
**NonUnitalSubalgebra.center_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalgeb
ra`。
形式化陈述：center_eq_top (A : Type*) [NonUnitalCommSemiring A] [Module R A] [IsScalar
Tower R A A] [SMulCommClass R A A] : center R A = ⊤
参数：A : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_eq_univ`：center_eq_univ : center M = univ
-/
theorem center_eq_top (A : Type*) [NonUnitalCommSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)

variable {R A}
/-
**NonUnitalSubalgebra.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalge
bra`。
形式化陈述：mem_center_iff {a : A} : a in center R A ↔ forall b : A, b * a = a * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.mem_center_iff`：mem_center_iff {z : M} : z in center M ↔ fo
rall g, g * z = z * g
-/
theorem mem_center_iff {a : A} : a ∈ center R A ↔ ∀ b : A, b * a = a * b :=
  Subsemigroup.mem_center_iff

end Center

section Centralizer

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

@[simp]
/-
**NonUnitalSubalgebra._root_.Set.smul_mem_centralizer** 是 Mathlib 中的一个定理，位于命名空间 
`NonUnitalSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.smul_mem_centralizer {s : Set A} (r : R) {a : A} (ha : a ∈ s.centralizer) :
    r • a ∈ s.centralizer :=
  fun x hx => by rw [mul_smul_comm, smul_mul_assoc, ha x hx]

variable (R)

/-- The centralizer of a set as a non-unital subalgebra. -/
/-
**NonUnitalSubalgebra.centralizer** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubalgebra
`。
形式化陈述：centralizer (s : Set A) : NonUnitalSubalgebra R A where toNonUnitalSubsemi
ring
参数：s : Set A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_centralizer`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSe
miring R] [inst_1 : NonUnitalSemiring A] [inst_2 : _root_.Module R A]   [IsScala
rTower R A A] …

--- 原说明 ---
The centralizer of a set as a non-unital subalgebra.
-/
def centralizer (s : Set A) : NonUnitalSubalgebra R A where
  toNonUnitalSubsemiring := NonUnitalSubsemiring.centralizer s
  smul_mem' := Set.smul_mem_centralizer

@[simp, norm_cast]
/-
**NonUnitalSubalgebra.coe_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalg
ebra`。
形式化陈述：coe_centralizer (s : Set A) : (centralizer R s : Set A) = s.centralizer
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = s.centralizer :=
  rfl
/-
**NonUnitalSubalgebra.mem_centralizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
balgebra`。
形式化陈述：mem_centralizer_iff {s : Set A} {z : A} : z in centralizer R s ↔ forall g 
in s, g * z = z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_centralizer_iff {s : Set A} {z : A} : z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl
/-
**NonUnitalSubalgebra.centralizer_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubalge
bra`。
形式化陈述：centralizer_le (s t : Set A) (h : s subseteq t) : centralizer R t <= centr
alizer R s
参数：s t : Set A；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.centralizer_subset`：centralizer_subset (h : S subseteq T) : centrali
zer T subseteq centralizer S
-/
theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  Set.centralizer_subset h

@[simp]
/-
**NonUnitalSubalgebra.centralizer_univ** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubal
gebra`。
形式化陈述：centralizer_univ : centralizer R Set.univ = center R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用引理 `Set.centralizer_univ`：centralizer_univ : centralizer univ = center M
-/
theorem centralizer_univ : centralizer R Set.univ = center R A :=
  SetLike.ext' (Set.centralizer_univ A)

end Centralizer

end NonUnitalSubalgebra

namespace NonUnitalAlgebra

open NonUnitalSubalgebra

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

variable (R) in
/-
**NonUnitalAlgebra.adjoin_le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `
NonUnitalAlgebra`。
形式化陈述：adjoin_le_centralizer_centralizer (s : Set A) : adjoin R s <= centralizer 
R (centralizer R s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.adjoin_le`：adjoin_le {S : NonUnitalSubalgebra R A} {s :
 Set A} (hs : s subseteq S) : adjoin R s <= S
· 使用引理 `Set.subset_centralizer_centralizer`：subset_centralizer_centralizer : S s
ubseteq S.centralizer.centralizer
-/
lemma adjoin_le_centralizer_centralizer (s : Set A) :
    adjoin R s ≤ centralizer R (centralizer R s) :=
  adjoin_le Set.subset_centralizer_centralizer
/-
**NonUnitalAlgebra.commute_of_mem_adjoin_of_forall_mem_commute** 是 Mathlib 中的一个引
理，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A} (hb : b 
in adjoin R s) (h : forall b in s, Commute a b) : Commute a b
参数：hb : b in adjoin R s；h : forall b in s, Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Commute.symm_iff`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b
 ↔ Commute b a
· 使用引理 `NonUnitalAlgebra.adjoin_le_centralizer_centralizer`：adjoin_le_centralize
r_centralizer (s : Set A) : adjoin R s <= centralizer R (centralizer R s)
-/
lemma commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A}
    (hb : b ∈ adjoin R s) (h : ∀ b ∈ s, Commute a b) :
    Commute a b := by
  have : a ∈ centralizer R s := by simpa only [Commute.symm_iff (a := a)] using! h
  exact adjoin_le_centralizer_centralizer R s hb a this
/-
**NonUnitalAlgebra.commute_of_mem_adjoin_singleton_of_commute** 是 Mathlib 中的一个引理
，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：commute_of_mem_adjoin_singleton_of_commute {a b c : A} (hc : c in adjoin R
 {b}) (h : Commute a b) : Commute a c
参数：hc : c in adjoin R {b}；h : Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NonUnitalAlgebra.commute_of_mem_adjoin_of_forall_mem_commute`：commute_of
_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A} (hb : b in adjoin R s) (
h : forall b in s, Commute a b) : Commute a b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma commute_of_mem_adjoin_singleton_of_commute {a b c : A}
    (hc : c ∈ adjoin R {b}) (h : Commute a b) :
    Commute a c :=
  commute_of_mem_adjoin_of_forall_mem_commute hc <| by simpa
/-
**NonUnitalAlgebra.commute_of_mem_adjoin_self** 是 Mathlib 中的一个引理，位于命名空间 `NonUnit
alAlgebra`。
形式化陈述：commute_of_mem_adjoin_self {a b : A} (hb : b in adjoin R {a}) : Commute a 
b
参数：hb : b in adjoin R {a}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NonUnitalAlgebra.commute_of_mem_adjoin_singleton_of_commute`：commute_of_
mem_adjoin_singleton_of_commute {a b c : A} (hc : c in adjoin R {b}) (h : Commut
e a b) : Commute a c
-/
lemma commute_of_mem_adjoin_self {a b : A} (hb : b ∈ adjoin R {a}) :
    Commute a b :=
  commute_of_mem_adjoin_singleton_of_commute hb rfl

variable (R) in
/-- If all elements of `s : Set A` commute pairwise, then `adjoin R s` is commutative. -/
/-
**NonUnitalAlgebra.isMulCommutative_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalA
lgebra`。
形式化陈述：isMulCommutative_adjoin {s : Set A} (hcomm : forall x in s, forall y in s,
 x * y = y * x) : IsMulCommutative (adjoin R s)
参数：hcomm : forall x in s, forall y in s, x * y = y * x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NonUnitalAlgebra.adjoin_le_centralizer_centralizer`：adjoin_le_centralize
r_centralizer (s : Set A) : adjoin R s <= centralizer R (centralizer R s)
· 使用定理 `IsMulCommutative.of_setLike_mul_comm`：∀ {S : Type u_3} {M : Type u_4} [i
nst : SetLike S M] [inst_1 : Mul M] [inst_2 : MulMemClass S M] {s : S},   (∀ a ∈
 s, ∀ b ∈ s, a * b = b * a…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用引理 `Set.centralizer_centralizer_comm_of_comm`：centralizer_centralizer_comm_o
f_comm (h_comm : forall x in S, forall y in S, x * y = y * x) : forall x in S.ce
ntralizer.centralizer, forall …

--- 原说明 ---
If all elements of `s : Set A` commute pairwise, then `adjoin R s` is commutativ
e.
-/
theorem isMulCommutative_adjoin {s : Set A} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    IsMulCommutative (adjoin R s) :=
  have := adjoin_le_centralizer_centralizer R s
  .of_setLike_mul_comm fun _ h₁ _ h₂ ↦
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

variable (R) in
/-
**NonUnitalAlgebra.isMulCommutative_adjoin_singleton** 是 Mathlib 中的一个实例，位于命名空间 `
NonUnitalAlgebra`。
形式化陈述：isMulCommutative_adjoin_singleton (x : A) : IsMulCommutative (adjoin R ({x
} : Set A))
参数：x : A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.isMulCommutative_adjoin`：isMulCommutative_adjoin {s : S
et A} (hcomm : forall x in s, forall y in s, x * y = y * x) : IsMulCommutative (
adjoin R s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isMulCommutative_adjoin_singleton (x : A) :
    IsMulCommutative (adjoin R ({x} : Set A)) :=
  isMulCommutative_adjoin R (by simp)

open scoped IsMulCommutative in
variable (R) in
/-- If all elements of `s : Set A` commute pairwise, then `adjoin R s` is a non-unital commutative
semiring.

See note [reducible non-instances]. -/
@[deprecated isMulCommutative_adjoin (since := "2026-03-11")]
/-
**NonUnitalAlgebra.adjoinNonUnitalCommSemiringOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间
 `NonUnitalAlgebra`。
形式化陈述：adjoinNonUnitalCommSemiringOfComm {s : Set A} (hcomm : forall a in s, fora
ll b in s, a * b = b * a) : NonUnitalCommSemiring (adjoin R s)
参数：hcomm : forall a in s, forall b in s, a * b = b * a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.isMulCommutative_adjoin`：isMulCommutative_adjoin {s : S
et A} (hcomm : forall x in s, forall y in s, x * y = y * x) : IsMulCommutative (
adjoin R s)

--- 原说明 ---
If all elements of `s : Set A` commute pairwise, then `adjoin R s` is a non-unit
al commutative
semiring.

See note [reducible non-instances].
-/
abbrev adjoinNonUnitalCommSemiringOfComm {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    NonUnitalCommSemiring (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm
  inferInstance
/-
**NonUnitalAlgebra.instIsMulCommutative_adjoin** 是 Mathlib 中的一个实例，位于命名空间 `NonUni
talAlgebra`。
形式化陈述：instIsMulCommutative_adjoin {S : Type*} [SetLike S A] [MulMemClass S A] (s
 : S) [IsMulCommutative s] : IsMulCommutative (adjoin R (s : Set A))
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.isMulCommutative_adjoin`：isMulCommutative_adjoin {s : S
et A} (hcomm : forall x in s, forall y in s, x * y = y * x) : IsMulCommutative (
adjoin R s)
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
-/
instance instIsMulCommutative_adjoin {S : Type*} [SetLike S A] [MulMemClass S A] (s : S)
    [IsMulCommutative s] : IsMulCommutative (adjoin R (s : Set A)) :=
  isMulCommutative_adjoin R fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

open scoped IsMulCommutative in
/-- If all elements of `s : Set A` commute pairwise, then `adjoin R s` is a non-unital commutative
ring.

See note [reducible non-instances]. -/
@[deprecated isMulCommutative_adjoin (since := "2026-03-11")]
/-
**NonUnitalAlgebra.adjoinNonUnitalCommRingOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间 `No
nUnitalAlgebra`。
形式化陈述：adjoinNonUnitalCommRingOfComm (R : Type*) {A : Type*} [CommRing R] [NonUni
talRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] {s : Set A} 
(hcomm : forall a in s, forall b in s, a * b = b * a) : NonUnitalCommRing (adjoi
n R s)
参数：R : Type*；hcomm : forall a in s, forall b in s, a * b = b * a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If all elements of `s : Set A` commute pairwise, then `adjoin R s` is a non-unit
al commutative
ring.

See note [reducible non-instances].
-/
abbrev adjoinNonUnitalCommRingOfComm (R : Type*) {A : Type*} [CommRing R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] {s : Set A}
    (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) : NonUnitalCommRing (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm
  inferInstance

end NonUnitalAlgebra

section Nat

variable {R : Type*} [NonUnitalNonAssocSemiring R]

/-- A non-unital subsemiring is a non-unital `ℕ`-subalgebra. -/
/-
**nonUnitalSubalgebraOfNonUnitalSubsemiring** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nonUnitalSubalgebraOfNonUnitalSubsemiring (S : NonUnitalSubsemiring R) : N
onUnitalSubalgebra Nat R where toNonUnitalSubsemiring
参数：S : NonUnitalSubsemiring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subsemiring is a non-unital `ℕ`-subalgebra.
-/
def nonUnitalSubalgebraOfNonUnitalSubsemiring (S : NonUnitalSubsemiring R) :
    NonUnitalSubalgebra ℕ R where
  toNonUnitalSubsemiring := S
  smul_mem' n _x hx := nsmul_mem (S := S) hx n

@[simp]
/-
**mem_nonUnitalSubalgebraOfNonUnitalSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nonUnitalSubalgebraOfNonUnitalSubsemiring {x : R} {S : NonUnitalSubsem
iring R} : x in nonUnitalSubalgebraOfNonUnitalSubsemiring S ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nonUnitalSubalgebraOfNonUnitalSubsemiring {x : R} {S : NonUnitalSubsemiring R} :
    x ∈ nonUnitalSubalgebraOfNonUnitalSubsemiring S ↔ x ∈ S :=
  Iff.rfl

end Nat

section Int

variable {R : Type*} [NonUnitalNonAssocRing R]

/-- A non-unital subring is a non-unital `ℤ`-subalgebra. -/
/-
**nonUnitalSubalgebraOfNonUnitalSubring** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nonUnitalSubalgebraOfNonUnitalSubring (S : NonUnitalSubring R) : NonUnital
Subalgebra Int R where toNonUnitalSubsemiring
参数：S : NonUnitalSubring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subring is a non-unital `ℤ`-subalgebra.
-/
def nonUnitalSubalgebraOfNonUnitalSubring (S : NonUnitalSubring R) : NonUnitalSubalgebra ℤ R where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  smul_mem' n _x hx := zsmul_mem (K := S) hx n

@[simp]
/-
**mem_nonUnitalSubalgebraOfNonUnitalSubring** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nonUnitalSubalgebraOfNonUnitalSubring {x : R} {S : NonUnitalSubring R}
 : x in nonUnitalSubalgebraOfNonUnitalSubring S ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nonUnitalSubalgebraOfNonUnitalSubring {x : R} {S : NonUnitalSubring R} :
    x ∈ nonUnitalSubalgebraOfNonUnitalSubring S ↔ x ∈ S :=
  Iff.rfl

end Int

