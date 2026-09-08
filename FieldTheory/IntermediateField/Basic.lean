/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Intermediate fields

Let `L / K` be a field extension, given as an instance `Algebra K L`.
This file defines the type of fields in between `K` and `L`, `IntermediateField K L`.
An `IntermediateField K L` is a subfield of `L` which contains (the image of) `K`,
i.e. it is a `Subfield L` and a `Subalgebra K L`.

## Main definitions

* `IntermediateField K L` : the type of intermediate fields between `K` and `L`.
* `Subalgebra.to_intermediateField`: turns a subalgebra closed under `⁻¹`
  into an intermediate field
* `Subfield.to_intermediateField`: turns a subfield containing the image of `K`
  into an intermediate field
* `IntermediateField.map`: map an intermediate field along an `AlgHom`
* `IntermediateField.restrict_scalars`: restrict the scalars of an intermediate field to a smaller
  field in a tower of fields.

## Implementation notes

Intermediate fields are defined with a structure extending `Subfield` and `Subalgebra`.
A `Subalgebra` is closed under all operations except `⁻¹`,

## Tags
intermediate field, field extension
-/

@[expose] public section


open Polynomial

variable (K L L' : Type*) [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

/-- `S : IntermediateField K L` is a subset of `L` such that there is a field
tower `L / S / K`. -/
/-
**IntermediateField** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u_1) → (L : Type u_2) → [inst : Field K] → [inst_1 : Field L] → 
[Algebra K L] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`S : IntermediateField K L` is a subset of `L` such that there is a field
tower `L / S / K`.
-/
structure IntermediateField extends Subalgebra K L where
  inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier

/-- Reinterpret an `IntermediateField` as a `Subalgebra`. -/
add_decl_doc IntermediateField.toSubalgebra

variable {K L L'}
variable (S : IntermediateField K L)

namespace IntermediateField

/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (IntermediateField K L) L :=
  ⟨fun S => S.toSubalgebra.carrier, by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp ⟩
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (IntermediateField K L) := .ofSetLike (IntermediateField K L) L
/-
**IntermediateField.neg_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   {x : L}, x ∈ S → -x ∈ S
参数：S : IntermediateField K L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
-/
protected theorem neg_mem {x : L} (hx : x ∈ S) : -x ∈ S := by
  change -x ∈ S.toSubalgebra; simpa

/-- Reinterpret an `IntermediateField` as a `Subfield`. -/
@[reducible]
/-
**IntermediateField.toSubfield** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：toSubfield : Subfield L
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.neg_mem`：∀ {K : Type u_1} {L : Type u_2} [inst : Field
 K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K L)   {x :
 L}, x ∈ S → -x…
· 使用定理 `IntermediateField.inv_mem'`：∀ {K : Type u_1} {L : Type u_2} [inst : Fiel
d K] [inst_1 : Field L] [inst_2 : Algebra K L]   (self : IntermediateField K L),
 ∀ x ∈ self.carr…

--- 原说明 ---
Reinterpret an `IntermediateField` as a `Subfield`.
-/
def toSubfield : Subfield L :=
  { S.toSubalgebra with
    neg_mem' := S.neg_mem,
    inv_mem' := S.inv_mem' }
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubfieldClass (IntermediateField K L) L where
  add_mem {s} := s.add_mem'
  zero_mem {s} := s.zero_mem'
  neg_mem {s} := s.neg_mem
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  inv_mem {s} := s.inv_mem' _
/-
**IntermediateField.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：mem_carrier {s : IntermediateField K L} {x : L} : x in s.carrier ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : IntermediateField K L} {x : L} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/-- Two intermediate fields are equal if they have the same elements. -/
@[ext]
/-
**IntermediateField.ext** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：ext {S T : IntermediateField K L} (h : forall x, x in S ↔ x in T) : S = T
参数：h : forall x, x in S ↔ x in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q

--- 原说明 ---
Two intermediate fields are equal if they have the same elements.
-/
theorem ext {S T : IntermediateField K L} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
/-
**IntermediateField.coe_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：coe_toSubalgebra : (S.toSubalgebra : Set L) = S
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubalgebra : (S.toSubalgebra : Set L) = S :=
  rfl

@[simp]
/-
**IntermediateField.coe_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：coe_toSubfield : (S.toSubfield : Set L) = S
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubfield : (S.toSubfield : Set L) = S :=
  rfl

@[simp]
/-
**IntermediateField.coe_type_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Intermediat
eField`。
形式化陈述：coe_type_toSubalgebra : (S.toSubalgebra : Type _) = S
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_type_toSubalgebra : (S.toSubalgebra : Type _) = S :=
  rfl

@[simp]
/-
**IntermediateField.coe_type_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：coe_type_toSubfield : (S.toSubfield : Type _) = S
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_type_toSubfield : (S.toSubfield : Type _) = S :=
  rfl

@[simp]
/-
**IntermediateField.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：mem_mk (s : Subsemiring L) (hK : forall x, algebraMap K L x in s) (hi) (x 
: L) : x in IntermediateField.mk (Subalgebra.mk s hK) hi ↔ x in s
参数：s : Subsemiring L；hK : forall x, algebraMap K L x in s；hi；x : L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk (s : Subsemiring L) (hK : ∀ x, algebraMap K L x ∈ s) (hi) (x : L) :
    x ∈ IntermediateField.mk (Subalgebra.mk s hK) hi ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**IntermediateField.mem_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：mem_toSubalgebra (s : IntermediateField K L) (x : L) : x in s.toSubalgebra
 ↔ x in s
参数：s : IntermediateField K L；x : L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubalgebra (s : IntermediateField K L) (x : L) : x ∈ s.toSubalgebra ↔ x ∈ s :=
  Iff.rfl
/-
**IntermediateField.mem_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：mem_toSubfield (s : IntermediateField K L) (x : L) : x in s.toSubfield ↔ x
 in s
参数：s : IntermediateField K L；x : L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubfield (s : IntermediateField K L) (x : L) : x ∈ s.toSubfield ↔ x ∈ s :=
  Iff.rfl
/-
**IntermediateField.toSubalgebra_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField`。
形式化陈述：toSubalgebra_strictMono : StrictMono (IntermediateField.toSubalgebra : _ -
> Subalgebra K L)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubalgebra_strictMono :
    StrictMono (IntermediateField.toSubalgebra : _ → Subalgebra K L) := fun _ _ h ↦ h

/-- Copy of an intermediate field with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
/-
**IntermediateField.copy** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：{K : Type u_1} →   {L : Type u_2} →     [inst : Field K] →       [inst_1 :
 Field L] →         [inst_2 : Algebra K L] → (S : IntermediateField K L) → (s : 
Set L) → s = ↑S → IntermediateField K L
参数：S : IntermediateField K L；s : Set L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of an intermediate field with a new `carrier` equal to the old one. Useful 
to fix
definitional equalities.
-/
protected def copy (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) :
    IntermediateField K L where
  toSubalgebra := S.toSubalgebra.copy s hs
  inv_mem' := hs.symm ▸ S.inv_mem'

@[simp]
/-
**IntermediateField.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：coe_copy (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) : (S.copy s
 hs : Set L) = s
参数：S : IntermediateField K L；s : Set L；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) :
    (S.copy s hs : Set L) = s :=
  rfl
/-
**IntermediateField.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：copy_eq (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) : S.copy s h
s = S
参数：S : IntermediateField K L；s : Set L；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

section InheritedLemmas

/-! ### Lemmas inherited from more general structures

The declarations in this section derive from the fact that an `IntermediateField` is also a
subalgebra or subfield. Their use should be replaceable with the corresponding lemma from a
subobject class.
-/


/-- An intermediate field contains the image of the smaller field. -/
/-
**IntermediateField.algebraMap_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：algebraMap_mem (x : K) : algebraMap K L x in S
参数：x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.algebraMap_mem'`：∀ {R : Type u} {A : Type v} [inst : CommSemi
ring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (self : Subalgebra R A)   (
r : R), (algebra…

--- 原说明 ---
An intermediate field contains the image of the smaller field.
-/
theorem algebraMap_mem (x : K) : algebraMap K L x ∈ S :=
  S.algebraMap_mem' x

/-- An intermediate field is closed under scalar multiplication. -/
/-
**IntermediateField.smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：smul_mem {y : L} : y in S -> forall {x : K}, x • y in S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S

--- 原说明 ---
An intermediate field is closed under scalar multiplication.
-/
theorem smul_mem {y : L} : y ∈ S → ∀ {x : K}, x • y ∈ S :=
  S.toSubalgebra.smul_mem

/-- An intermediate field contains the ring's 1. -/
/-
**IntermediateField.one_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L),   1 ∈ S
参数：S : IntermediateField K L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
An intermediate field contains the ring's 1.
-/
protected theorem one_mem : (1 : L) ∈ S :=
  one_mem S

/-- An intermediate field contains the ring's 0. -/
/-
**IntermediateField.zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L),   0 ∈ S
参数：S : IntermediateField K L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
An intermediate field contains the ring's 0.
-/
protected theorem zero_mem : (0 : L) ∈ S :=
  zero_mem S

/-- An intermediate field is closed under multiplication. -/
/-
**IntermediateField.mul_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   {x y : L}, x ∈ S → y ∈ S → x * y 
∈ S
参数：S : IntermediateField K L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
An intermediate field is closed under multiplication.
-/
protected theorem mul_mem {x y : L} : x ∈ S → y ∈ S → x * y ∈ S :=
  mul_mem

/-- An intermediate field is closed under addition. -/
/-
**IntermediateField.add_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   {x y : L}, x ∈ S → y ∈ S → x + y 
∈ S
参数：S : IntermediateField K L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
An intermediate field is closed under addition.
-/
protected theorem add_mem {x y : L} : x ∈ S → y ∈ S → x + y ∈ S :=
  add_mem

/-- An intermediate field is closed under subtraction. -/
/-
**IntermediateField.sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   {x y : L}, x ∈ S → y ∈ S → x - y 
∈ S
参数：S : IntermediateField K L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
An intermediate field is closed under subtraction.
-/
protected theorem sub_mem {x y : L} : x ∈ S → y ∈ S → x - y ∈ S :=
  sub_mem

/-- An intermediate field is closed under inverses. -/
/-
**IntermediateField.inv_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   {x : L}, x ∈ S → x⁻¹ ∈ S
参数：S : IntermediateField K L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubfieldClass.toInvMemClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Div
isionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   InvMemClass S 
K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
An intermediate field is closed under inverses.
-/
protected theorem inv_mem {x : L} : x ∈ S → x⁻¹ ∈ S :=
  inv_mem

/-- An intermediate field is closed under division. -/
/-
**IntermediateField.div_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   {x y : L}, x ∈ S → y ∈ S → x / y 
∈ S
参数：S : IntermediateField K L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_mem`：div_mem {x y : M} (hx : x in H) (hy : y in H) : x / y in H
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
An intermediate field is closed under division.
-/
protected theorem div_mem {x y : L} : x ∈ S → y ∈ S → x / y ∈ S :=
  div_mem

/-- Product of a list of elements in an intermediate field is in the intermediate field. -/
/-
**IntermediateField.list_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   {l : List L}, (∀ x ∈ l, x ∈ S) → 
l.prod ∈ S
参数：S : IntermediateField K L；∀ x ∈ l, x ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `list_prod_mem`：list_prod_mem {l : List M} (hl : forall x in l, x in S) :
 l.prod in S
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
Product of a list of elements in an intermediate field is in the intermediate fi
eld.
-/
protected theorem list_prod_mem {l : List L} : (∀ x ∈ l, x ∈ S) → l.prod ∈ S :=
  list_prod_mem

/-- Sum of a list of elements in an intermediate field is in the intermediate field. -/
/-
**IntermediateField.list_sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   {l : List L}, (∀ x ∈ l, x ∈ S) → 
l.sum ∈ S
参数：S : IntermediateField K L；∀ x ∈ l, x ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `list_sum_mem`：∀ {M : Type u_1} {B : Type u_3} [inst : AddMonoid M] [inst
_1 : SetLike B M] [AddSubmonoidClass B M] {S : B}   {l : List M}, (∀ x ∈ l, x ∈ 
S)…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
Sum of a list of elements in an intermediate field is in the intermediate field.
-/
protected theorem list_sum_mem {l : List L} : (∀ x ∈ l, x ∈ S) → l.sum ∈ S :=
  list_sum_mem

/-- Product of a multiset of elements in an intermediate field is in the intermediate field. -/
/-
**IntermediateField.multiset_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   (m : Multiset L), (∀ a ∈ m, a ∈ S
) → m.prod ∈ S
参数：S : IntermediateField K L；m : Multiset L；∀ a ∈ m, a ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_prod_mem`：multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [S
ubmonoidClass B M] (m : Multiset M) (hm : forall a in m, a in S) : m.prod in S
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
Product of a multiset of elements in an intermediate field is in the intermediat
e field.
-/
protected theorem multiset_prod_mem (m : Multiset L) : (∀ a ∈ m, a ∈ S) → m.prod ∈ S :=
  multiset_prod_mem m

/-- Sum of a multiset of elements in an `IntermediateField` is in the `IntermediateField`. -/
/-
**IntermediateField.multiset_sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   (m : Multiset L), (∀ a ∈ m, a ∈ S
) → m.sum ∈ S
参数：S : IntermediateField K L；m : Multiset L；∀ a ∈ m, a ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   (m : Multiset M), (∀
 a ∈ m…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
Sum of a multiset of elements in an `IntermediateField` is in the `IntermediateF
ield`.
-/
protected theorem multiset_sum_mem (m : Multiset L) : (∀ a ∈ m, a ∈ S) → m.sum ∈ S :=
  multiset_sum_mem m

/-- Product of elements of an intermediate field indexed by a `Finset` is in the intermediate field.
-/
/-
**IntermediateField.prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   {ι : Type u_4} {t : Finset ι} {f 
: ι → L}, (∀ c ∈ t, f c ∈ S) → ∏ i ∈ t, f i ∈ S
参数：S : IntermediateField K L；∀ c ∈ t, f c ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prod_mem`：prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidCl
ass B M] {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S)…
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
Product of elements of an intermediate field indexed by a `Finset` is in the int
ermediate field.
-/
protected theorem prod_mem {ι : Type*} {t : Finset ι} {f : ι → L} (h : ∀ c ∈ t, f c ∈ S) :
    (∏ i ∈ t, f i) ∈ S :=
  prod_mem h

/-- Sum of elements in an `IntermediateField` indexed by a `Finset` is in the `IntermediateField`.
-/
/-
**IntermediateField.sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   {ι : Type u_4} {t : Finset ι} {f 
: ι → L}, (∀ c ∈ t, f c ∈ S) → ∑ i ∈ t, f i ∈ S
参数：S : IntermediateField K L；∀ c ∈ t, f c ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
Sum of elements in an `IntermediateField` indexed by a `Finset` is in the `Inter
mediateField`.
-/
protected theorem sum_mem {ι : Type*} {t : Finset ι} {f : ι → L} (h : ∀ c ∈ t, f c ∈ S) :
    (∑ i ∈ t, f i) ∈ S :=
  sum_mem h
/-
**IntermediateField.pow_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   {x : L}, x ∈ S → ∀ (n : ℤ), x ^ n
 ∈ S
参数：S : IntermediateField K L；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zpow_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : DivInvMonoid M] [inst_
1 : SetLike S M] [hSM : SubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n : ℤ…
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
protected theorem pow_mem {x : L} (hx : x ∈ S) (n : ℤ) : x ^ n ∈ S :=
  zpow_mem hx n
/-
**IntermediateField.zsmul_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   {x : L}, x ∈ S → ∀ (n : ℤ), n • x
 ∈ S
参数：S : IntermediateField K L；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zsmul_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst
_1 : SetLike S M] [hSM : AddSubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n …
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
protected theorem zsmul_mem {x : L} (hx : x ∈ S) (n : ℤ) : n • x ∈ S :=
  zsmul_mem hx n
/-
**IntermediateField.intCast_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   (n : ℤ), ↑n ∈ S
参数：S : IntermediateField K L；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intCast_mem`：intCast_mem (n : Int) : (n : R) in s
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
protected theorem intCast_mem (n : ℤ) : (n : L) ∈ S :=
  intCast_mem S n

@[simp, norm_cast]
/-
**IntermediateField.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   (x y : ↥S), ↑(x + y) = ↑x + ↑y
参数：S : IntermediateField K L；x y : ↥S；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
protected theorem coe_add (x y : S) : (↑(x + y) : L) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
/-
**IntermediateField.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   (x : ↥S), ↑(-x) = -↑x
参数：S : IntermediateField K L；x : ↥S；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
protected theorem coe_neg (x : S) : (↑(-x) : L) = -↑x :=
  rfl

@[simp, norm_cast]
/-
**IntermediateField.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   (x y : ↥S), ↑(x * y) = ↑x * ↑y
参数：S : IntermediateField K L；x y : ↥S；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
protected theorem coe_mul (x y : S) : (↑(x * y) : L) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
/-
**IntermediateField.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   (x : ↥S), ↑x⁻¹ = (↑x)⁻¹
参数：S : IntermediateField K L；x : ↥S；↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubfieldClass.toInvMemClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Div
isionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   InvMemClass S 
K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
protected theorem coe_inv (x : S) : (↑x⁻¹ : L) = (↑x)⁻¹ :=
  rfl

@[simp, norm_cast]
/-
**IntermediateField.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   (x y : ↥S), ↑(x / y) = ↑x / ↑y
参数：S : IntermediateField K L；x y : ↥S；x / y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
protected theorem coe_div (x y : S) : (↑(x / y) : L) = ↑x / ↑y :=
  rfl

@[simp, norm_cast]
/-
**IntermediateField.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L),   ↑0 = 0
参数：S : IntermediateField K L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
protected theorem coe_zero : ((0 : S) : L) = 0 :=
  rfl

@[simp, norm_cast]
/-
**IntermediateField.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L),   ↑1 = 1
参数：S : IntermediateField K L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
protected theorem coe_one : ((1 : S) : L) = 1 :=
  rfl

@[simp, norm_cast]
/-
**IntermediateField.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   (x : ↥S) (n : ℕ), ↑(x ^ n) = ↑x ^
 n
参数：S : IntermediateField K L；x : ↥S；n : ℕ；x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubmonoidClass.coe_pow`：coe_pow {M} [Monoid M] {A : Type*} [SetLike A M]
 [SubmonoidClass A M] {S : A} (x : S) (n : Nat) : ↑(x ^ n) = (x : M) ^ n
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
protected theorem coe_pow (x : S) (n : ℕ) : (↑(x ^ n : S) : L) = (x : L) ^ n :=
  SubmonoidClass.coe_pow x n

end InheritedLemmas

/-
**IntermediateField.natCast_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：natCast_mem (n : Nat) : (n : L) in S
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
theorem natCast_mem (n : ℕ) : (n : L) ∈ S := by simp
/-
**IntermediateField.instSMulMemClass** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateFiel
d`。
形式化陈述：instSMulMemClass : SMulMemClass (IntermediateField K L) K L where smul_mem
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.smul_mem`：smul_mem {y : L} : y in S -> forall {x : K},
 x • y in S
-/
instance instSMulMemClass : SMulMemClass (IntermediateField K L) K L where
  smul_mem := fun _ _ hx ↦ IntermediateField.smul_mem _ hx

end IntermediateField

/-- Turn a subalgebra closed under inverses into an intermediate field. -/
/-
**Subalgebra.toIntermediateField** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subalgebra.toIntermediateField (S : Subalgebra K L) (inv_mem : forall x in
 S, x⁻¹ in S) : IntermediateField K L
参数：S : Subalgebra K L；inv_mem : forall x in S, x⁻¹ in S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a subalgebra closed under inverses into an intermediate field.
-/
def Subalgebra.toIntermediateField (S : Subalgebra K L) (inv_mem : ∀ x ∈ S, x⁻¹ ∈ S) :
    IntermediateField K L :=
  { S with
    inv_mem' := inv_mem }

@[simp]
/-
**toSubalgebra_toIntermediateField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toSubalgebra_toIntermediateField (S : Subalgebra K L) (inv_mem : forall x 
in S, x⁻¹ in S) : (S.toIntermediateField inv_mem).toSubalgebra = S
参数：S : Subalgebra K L；inv_mem : forall x in S, x⁻¹ in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubalgebra_toIntermediateField (S : Subalgebra K L) (inv_mem : ∀ x ∈ S, x⁻¹ ∈ S) :
    (S.toIntermediateField inv_mem).toSubalgebra = S := by
  ext
  rfl

@[simp]
/-
**toIntermediateField_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toIntermediateField_toSubalgebra (S : IntermediateField K L) : (S.toSubalg
ebra.toIntermediateField fun _ => S.inv_mem) = S
参数：S : IntermediateField K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `IntermediateField.inv_mem`：∀ {K : Type u_1} {L : Type u_2} [inst : Field
 K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K L)   {x :
 L}, x ∈ S → x⁻…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toIntermediateField_toSubalgebra (S : IntermediateField K L) :
    (S.toSubalgebra.toIntermediateField fun _ => S.inv_mem) = S := by
  ext
  rfl

/-- Turn a subalgebra satisfying `IsField` into an intermediate field. -/
/-
**Subalgebra.toIntermediateField'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subalgebra.toIntermediateField' (S : Subalgebra K L) (hS : IsField S) : In
termediateField K L
参数：S : Subalgebra K L；hS : IsField S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a subalgebra satisfying `IsField` into an intermediate field.
-/
def Subalgebra.toIntermediateField' (S : Subalgebra K L) (hS : IsField S) : IntermediateField K L :=
  S.toIntermediateField fun x hx => by
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]
      exact S.zero_mem
    let hS' := hS.toField
    obtain ⟨y, hy⟩ := hS.mul_inv_cancel (show (⟨x, hx⟩ : S) ≠ 0 from Subtype.coe_ne_coe.1 hx0)
    rw [Subtype.ext_iff, S.coe_mul, S.coe_one, Subtype.coe_mk, mul_eq_one_iff_inv_eq₀ hx0] at hy
    exact hy.symm ▸ y.2

@[simp]
/-
**toSubalgebra_toIntermediateField'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toSubalgebra_toIntermediateField' (S : Subalgebra K L) (hS : IsField S) : 
(S.toIntermediateField' hS).toSubalgebra = S
参数：S : Subalgebra K L；hS : IsField S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubalgebra_toIntermediateField' (S : Subalgebra K L) (hS : IsField S) :
    (S.toIntermediateField' hS).toSubalgebra = S := by
  ext
  rfl

@[simp]
/-
**toIntermediateField'_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L),   S.toIntermediateField' ⋯ = S
参数：S : IntermediateField K L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `Field.toIsField`：Field.toIsField (R : Type u) [Field R] : IsField R
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toIntermediateField'_toSubalgebra (S : IntermediateField K L) :
    S.toSubalgebra.toIntermediateField' (Field.toIsField S) = S := by
  ext
  rfl

/-- Turn a subfield of `L` containing the image of `K` into an intermediate field. -/
/-
**Subfield.toIntermediateField** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subfield.toIntermediateField (S : Subfield L) (algebra_map_mem : forall x,
 algebraMap K L x in S) : IntermediateField K L
参数：S : Subfield L；algebra_map_mem : forall x, algebraMap K L x in S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a subfield of `L` containing the image of `K` into an intermediate field.
-/
def Subfield.toIntermediateField (S : Subfield L) (algebra_map_mem : ∀ x, algebraMap K L x ∈ S) :
    IntermediateField K L :=
  { S with
    algebraMap_mem' := algebra_map_mem }

@[simp]
/-
**Subfield.toIntermediateField_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subfield.toIntermediateField_toSubfield (S : Subfield L) (algebra_map_mem 
: forall x, (algebraMap K L) x in S) : (S.toIntermediateField algebra_map_mem).t
oSubfield = S
参数：S : Subfield L；algebra_map_mem : forall x, (algebraMap K L) x in S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subfield.toIntermediateField_toSubfield (S : Subfield L)
    (algebra_map_mem : ∀ x, (algebraMap K L) x ∈ S) :
    (S.toIntermediateField algebra_map_mem).toSubfield = S := rfl

@[simp]
/-
**Subfield.coe_toIntermediateField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subfield.coe_toIntermediateField (S : Subfield L) (algebra_map_mem : foral
l x, (algebraMap K L) x in S) : ((S.toIntermediateField algebra_map_mem) : Set L
) = S
参数：S : Subfield L；algebra_map_mem : forall x, (algebraMap K L) x in S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subfield.coe_toIntermediateField (S : Subfield L)
    (algebra_map_mem : ∀ x, (algebraMap K L) x ∈ S) :
    ((S.toIntermediateField algebra_map_mem) : Set L) = S := rfl

namespace IntermediateField

/-- An intermediate field inherits a field structure. -/
/-
**IntermediateField.toField** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
形式化陈述：toField : Field S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An intermediate field inherits a field structure.
-/
instance toField : Field S :=
  S.toSubfield.toField

@[norm_cast]
/-
**IntermediateField.coe_sum** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：coe_sum {ι : Type*} [Fintype ι] (f : ι -> S) : (↑(∑ i, f i) : L) = ∑ i, (f
 i : L)
参数：f : ι -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.coe_finsetSum`：∀ {B : Type u_3} {S : B} {ι : Type u_4}
 {M : Type u_5} [inst : AddCommMonoid M] [inst_1 : SetLike B M]   [inst_2 : AddS
ubmonoidClass B M] (f…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
theorem coe_sum {ι : Type*} [Fintype ι] (f : ι → S) : (↑(∑ i, f i) : L) = ∑ i, (f i : L) :=
  AddSubmonoidClass.coe_finsetSum f Finset.univ

@[norm_cast]
/-
**IntermediateField.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：coe_prod {ι : Type*} [Fintype ι] (f : ι -> S) : (↑(∏ i, f i) : L) = ∏ i, (
f i : L)
参数：f : ι -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubmonoidClass.coe_finsetProd`：coe_finsetProd {ι M} [CommMonoid M] [SetL
ike B M] [SubmonoidClass B M] (f : ι -> S) (s : Finset ι) : ↑(∏ i in s, f i) = (
∏ i in s, f i : M)
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
theorem coe_prod {ι : Type*} [Fintype ι] (f : ι → S) : (↑(∏ i, f i) : L) = ∏ i, (f i : L) :=
  SubmonoidClass.coe_finsetProd f Finset.univ

/-!
`IntermediateField`s inherit structure from their `Subfield` coercions.
-/

variable {X Y}

/-- The action by an intermediate field is the action by the underlying field. -/
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by an intermediate field is the action by the underlying field.
-/
instance [SMul L X] (F : IntermediateField K L) : SMul F X :=
  inferInstanceAs (SMul F.toSubfield X)
/-
**IntermediateField.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：smul_def [SMul L X] {F : IntermediateField K L} (g : F) (m : X) : g • m = 
(g : L) • m
参数：g : F；m : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def [SMul L X] {F : IntermediateField K L} (g : F) (m : X) : g • m = (g : L) • m :=
  rfl
/-
**IntermediateField.smulCommClass_left** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateFi
eld`。
形式化陈述：smulCommClass_left [SMul L Y] [SMul X Y] [SMulCommClass L X Y] (F : Interm
ediateField K L) : SMulCommClass F X Y
参数：F : IntermediateField K L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulCommClass_left [SMul L Y] [SMul X Y] [SMulCommClass L X Y]
    (F : IntermediateField K L) : SMulCommClass F X Y :=
  inferInstanceAs (SMulCommClass F.toSubfield X Y)
/-
**IntermediateField.smulCommClass_right** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateF
ield`。
形式化陈述：smulCommClass_right [SMul X Y] [SMul L Y] [SMulCommClass X L Y] (F : Inter
mediateField K L) : SMulCommClass X F Y
参数：F : IntermediateField K L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulCommClass_right [SMul X Y] [SMul L Y] [SMulCommClass X L Y]
    (F : IntermediateField K L) : SMulCommClass X F Y :=
  inferInstanceAs (SMulCommClass X F.toSubfield Y)

-- note: giving this instance the default priority may trigger trouble with synthesizing instances
-- for field extensions with more than one intermediate field. For example, in a field extension
-- `E/F`, and with `K₁ ≤ K₂` of type `IntermediateField F E`, this instance will cause a search
-- for `IsScalarTower K₁ K₂ E` to trigger a search for `IsScalarTower E K₂ E` which may
-- take a long time to fail.
/-- Note that this provides `IsScalarTower F K K` which is needed by `smul_mul_assoc`. -/
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that this provides `IsScalarTower F K K` which is needed by `smul_mul_assoc
`.
-/
instance (priority := 900) [SMul X Y] [SMul L X] [SMul L Y] [IsScalarTower L X Y]
    (F : IntermediateField K L) : IsScalarTower F X Y :=
  inferInstanceAs (IsScalarTower F.toSubfield X Y)
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul L X] [FaithfulSMul L X] (F : IntermediateField K L) : FaithfulSMul F X :=
  inferInstanceAs (FaithfulSMul F.toSubfield X)

/-- The action by an intermediate field is the action by the underlying field. -/
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by an intermediate field is the action by the underlying field.
-/
instance [MulAction L X] (F : IntermediateField K L) : MulAction F X :=
  inferInstanceAs (MulAction F.toSubfield X)

/-- The action by an intermediate field is the action by the underlying field. -/
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by an intermediate field is the action by the underlying field.
-/
instance [AddMonoid X] [DistribMulAction L X] (F : IntermediateField K L) : DistribMulAction F X :=
  inferInstanceAs (DistribMulAction F.toSubfield X)

/-- The action by an intermediate field is the action by the underlying field. -/
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by an intermediate field is the action by the underlying field.
-/
instance [Monoid X] [MulDistribMulAction L X] (F : IntermediateField K L) :
    MulDistribMulAction F X :=
  inferInstanceAs (MulDistribMulAction F.toSubfield X)

/-- The action by an intermediate field is the action by the underlying field. -/
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by an intermediate field is the action by the underlying field.
-/
instance [Zero X] [SMulWithZero L X] (F : IntermediateField K L) : SMulWithZero F X :=
  inferInstanceAs (SMulWithZero F.toSubfield X)

/-- The action by an intermediate field is the action by the underlying field. -/
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by an intermediate field is the action by the underlying field.
-/
instance [Zero X] [MulActionWithZero L X] (F : IntermediateField K L) : MulActionWithZero F X :=
  inferInstanceAs (MulActionWithZero F.toSubfield X)

/-- The action by an intermediate field is the action by the underlying field. -/
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by an intermediate field is the action by the underlying field.
-/
instance [AddCommMonoid X] [Module L X] (F : IntermediateField K L) : Module F X :=
  inferInstanceAs (Module F.toSubfield X)

/-- The action by an intermediate field is the action by the underlying field. -/
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by an intermediate field is the action by the underlying field.
-/
instance [Semiring X] [MulSemiringAction L X] (F : IntermediateField K L) : MulSemiringAction F X :=
  inferInstanceAs (MulSemiringAction F.toSubfield X)

/-! `IntermediateField`s inherit structure from their `Subalgebra` coercions. -/

/-
**IntermediateField.toAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
形式化陈述：toAlgebra : Algebra S L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IntermediateField`s inherit structure from their `Subalgebra` coercions.
-/
instance toAlgebra : Algebra S L :=
  inferInstanceAs (Algebra S.toSubalgebra L)
/-
**IntermediateField.module'** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
形式化陈述：module' {R} [Semiring R] [SMul R K] [Module R L] [IsScalarTower R K L] : M
odule R S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module' {R} [Semiring R] [SMul R K] [Module R L] [IsScalarTower R K L] : Module R S :=
  inferInstanceAs (Module R S.toSubalgebra)
/-
**IntermediateField.algebra'** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
形式化陈述：algebra' {R' K L : Type*} [Field K] [Field L] [Algebra K L] (S : Intermedi
ateField K L) [CommSemiring R'] [SMul R' K] [Algebra R' L] [IsScalarTower R' K L
] : Algebra R' S
参数：S : IntermediateField K L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebra' {R' K L : Type*} [Field K] [Field L] [Algebra K L] (S : IntermediateField K L)
    [CommSemiring R'] [SMul R' K] [Algebra R' L] [IsScalarTower R' K L] : Algebra R' S :=
  inferInstanceAs (Algebra R' S.toSubalgebra)
/-
**IntermediateField.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
形式化陈述：isScalarTower {R} [Semiring R] [SMul R K] [Module R L] [IsScalarTower R K 
L] : IsScalarTower R K S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isScalarTower {R} [Semiring R] [SMul R K] [Module R L] [IsScalarTower R K L] :
    IsScalarTower R K S :=
  inferInstanceAs (IsScalarTower R K S.toSubalgebra)

@[simp]
/-
**IntermediateField.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：coe_smul {R} [SMul R K] [SMul R L] [IsScalarTower R K L] (r : R) (x : S) :
 ↑(r • x : S) = (r • (x : L))
参数：r : R；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul {R} [SMul R K] [SMul R L] [IsScalarTower R K L] (r : R) (x : S) :
    ↑(r • x : S) = (r • (x : L)) :=
  rfl
/-
**IntermediateField.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   (x : ↥S), (algebraMap (↥S) L) x =
 ↑x
参数：S : IntermediateField K L；x : ↥S；algebraMap (↥S) L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
@[simp] lemma algebraMap_apply (x : S) : algebraMap S L x = x := rfl
/-
**IntermediateField.coe_algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (S : IntermediateField K L)   (x : K), ↑((algebraMap K ↥S) x) =
 (algebraMap K L) x
参数：S : IntermediateField K L；x : K；(algebraMap K ↥S) x；algebraMap K L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_algebraMap_apply (x : K) : ↑(algebraMap K S x) = algebraMap K L x := rfl
/-
**IntermediateField.isScalarTower_bot** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateFie
ld`。
形式化陈述：isScalarTower_bot {R : Type*} [Semiring R] [Algebra L R] : IsScalarTower S
 L R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isScalarTower_bot {R : Type*} [Semiring R] [Algebra L R] : IsScalarTower S L R :=
  IsScalarTower.subalgebra _ _ _ S.toSubalgebra
/-
**IntermediateField.isScalarTower_mid** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateFie
ld`。
形式化陈述：isScalarTower_mid {R : Type*} [Semiring R] [Algebra L R] [Algebra K R] [Is
ScalarTower K L R] : IsScalarTower K S R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isScalarTower_mid {R : Type*} [Semiring R] [Algebra L R] [Algebra K R]
    [IsScalarTower K L R] : IsScalarTower K S R :=
  IsScalarTower.subalgebra' _ _ _ S.toSubalgebra

/-- Specialize `isScalarTower_mid` to the common case where the top field is `L`. -/
/-
**IntermediateField.isScalarTower_mid'** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateFi
eld`。
形式化陈述：isScalarTower_mid' : IsScalarTower K S L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Specialize `isScalarTower_mid` to the common case where the top field is `L`.
-/
instance isScalarTower_mid' : IsScalarTower K S L :=
  inferInstance
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {E} [Semiring E] [Algebra L E] : Algebra S E := inferInstanceAs (Algebra S.toSubalgebra E)

section shortcut_instances

variable {E} [Field E] [Algebra L E] (T : IntermediateField S E) {S}

/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra S T := T.algebra
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module S T := Algebra.toModule
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul S T := Algebra.toSMul
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra K E] [IsScalarTower K L E] : IsScalarTower K S T := T.isScalarTower

end shortcut_instances

/-- Given `f : L →ₐ[K] L'`, `S.comap f` is the intermediate field between `K` and `L`
  such that `f x ∈ S ↔ x ∈ S.comap f`. -/
/-
**IntermediateField.comap** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：comap (f : L ->ₐ[K] L') (S : IntermediateField K L') : IntermediateField K
 L where __
参数：f : L ->ₐ[K] L'；S : IntermediateField K L'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : L →ₐ[K] L'`, `S.comap f` is the intermediate field between `K` and `L
`
  such that `f x ∈ S ↔ x ∈ S.comap f`.
-/
def comap (f : L →ₐ[K] L') (S : IntermediateField K L') : IntermediateField K L where
  __ := S.toSubalgebra.comap f
  inv_mem' x hx := show f x⁻¹ ∈ S by rw [map_inv₀ f x]; exact S.inv_mem hx

/-- Given `f : L →ₐ[K] L'`, `S.map f` is the intermediate field between `K` and `L'`
such that `x ∈ S ↔ f x ∈ S.map f`. -/
/-
**IntermediateField.map** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：map (f : L ->ₐ[K] L') (S : IntermediateField K L) : IntermediateField K L'
 where __
参数：f : L ->ₐ[K] L'；S : IntermediateField K L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : L →ₐ[K] L'`, `S.map f` is the intermediate field between `K` and `L'`
such that `x ∈ S ↔ f x ∈ S.map f`.
-/
def map (f : L →ₐ[K] L') (S : IntermediateField K L) : IntermediateField K L' where
  __ := S.toSubalgebra.map f
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, S.inv_mem hx, map_inv₀ f x⟩

@[simp]
/-
**IntermediateField.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：coe_map (f : L ->ₐ[K] L') : (S.map f : Set L') = f '' S
参数：f : L ->ₐ[K] L'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (f : L →ₐ[K] L') : (S.map f : Set L') = f '' S :=
  rfl

@[simp]
/-
**IntermediateField.toSubalgebra_map** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：toSubalgebra_map (f : L ->ₐ[K] L') : (S.map f).toSubalgebra = S.toSubalgeb
ra.map f
参数：f : L ->ₐ[K] L'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubalgebra_map (f : L →ₐ[K] L') : (S.map f).toSubalgebra = S.toSubalgebra.map f :=
  rfl

@[simp]
/-
**IntermediateField.toSubfield_map** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：toSubfield_map (f : L ->ₐ[K] L') : (S.map f).toSubfield = S.toSubfield.map
 f
参数：f : L ->ₐ[K] L'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubfield_map (f : L →ₐ[K] L') : (S.map f).toSubfield = S.toSubfield.map f :=
  rfl

/-- Mapping intermediate fields along the identity does not change them. -/
/-
**IntermediateField.map_id** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：map_id : S.map (AlgHom.id K L) = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s

--- 原说明 ---
Mapping intermediate fields along the identity does not change them.
-/
theorem map_id : S.map (AlgHom.id K L) = S :=
  SetLike.coe_injective <| Set.image_id _

@[simp]
/-
**IntermediateField.mem_map** 是 Mathlib 中的一个引理，位于命名空间 `IntermediateField`。
形式化陈述：mem_map {f : L ->ₐ[K] L'} {y : L'} : y in S.map f ↔ exists x in S, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
-/
lemma mem_map {f : L →ₐ[K] L'} {y : L'} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  Set.mem_image f S y

-- Higher priority to apply before `mem_map`.
@[simp 1100]
/-
**IntermediateField.map_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：map_mem_map (f : L ->ₐ[K] L') {x : L} : f x in map f S ↔ x in S
参数：f : L ->ₐ[K] L'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_mem_map (f : L →ₐ[K] L') {x : L} :
    f x ∈ map f S ↔ x ∈ S :=
  calc
    _ ↔ f x ∈ (map f S : Set L') := Iff.rfl
    _ ↔ _ := by simp [Function.Injective.mem_set_image (f := f) f.injective]
/-
**IntermediateField.map_map** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：map_map {K L₁ L₂ L₃ : Type*} [Field K] [Field L₁] [Algebra K L₁] [Field L₂
] [Algebra K L₂] [Field L₃] [Algebra K L₃] (E : IntermediateField K L₁) (f : L₁ 
->ₐ[K] L₂) (g : L₂ ->ₐ[K] L₃) : (E.map f).map g = E.map (g.comp f)
参数：E : IntermediateField K L₁；f : L₁ ->ₐ[K] L₂；g : L₂ ->ₐ[K] L₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map {K L₁ L₂ L₃ : Type*} [Field K] [Field L₁] [Algebra K L₁] [Field L₂] [Algebra K L₂]
    [Field L₃] [Algebra K L₃] (E : IntermediateField K L₁) (f : L₁ →ₐ[K] L₂) (g : L₂ →ₐ[K] L₃) :
    (E.map f).map g = E.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

@[gcongr]
/-
**IntermediateField.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：map_mono (f : L ->ₐ[K] L') {S T : IntermediateField K L} (h : S <= T) : S.
map f <= T.map f
参数：f : L ->ₐ[K] L'；h : S <= T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem map_mono (f : L →ₐ[K] L') {S T : IntermediateField K L} (h : S ≤ T) :
    S.map f ≤ T.map f :=
  SetLike.coe_mono (Set.image_mono h)
/-
**IntermediateField.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：map_le_iff_le_comap {f : L ->ₐ[K] L'} {s : IntermediateField K L} {t : Int
ermediateField K L'} : s.map f <= t ↔ s <= t.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap {f : L →ₐ[K] L'}
    {s : IntermediateField K L} {t : IntermediateField K L'} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff
/-
**IntermediateField.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：gc_map_comap (f : L ->ₐ[K] L') : GaloisConnection (map f) (comap f)
参数：f : L ->ₐ[K] L'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.map_le_iff_le_comap`：map_le_iff_le_comap {f : L ->ₐ[K]
 L'} {s : IntermediateField K L} {t : IntermediateField K L'} : s.map f <= t ↔ s
 <= t.comap f
-/
theorem gc_map_comap (f : L →ₐ[K] L') : GaloisConnection (map f) (comap f) :=
  fun _ _ ↦ map_le_iff_le_comap

/-- Given an equivalence `e : L ≃ₐ[K] L'` of `K`-field extensions and an intermediate
field `E` of `L/K`, `intermediateFieldMap e E` is the induced equivalence
between `E` and `E.map e`. -/
/-
**IntermediateField.intermediateFieldMap** 是 Mathlib 中的一个定义，位于命名空间 `Intermediate
Field`。
形式化陈述：intermediateFieldMap (e : L ≃ₐ[K] L') (E : IntermediateField K L) : E ≃ₐ[K
] E.map e.toAlgHom
参数：e : L ≃ₐ[K] L'；E : IntermediateField K L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an equivalence `e : L ≃ₐ[K] L'` of `K`-field extensions and an intermediat
e
field `E` of `L/K`, `intermediateFieldMap e E` is the induced equivalence
between `E` and `E.map e`.
-/
def intermediateFieldMap (e : L ≃ₐ[K] L') (E : IntermediateField K L) : E ≃ₐ[K] E.map e.toAlgHom :=
  e.subalgebraMap E.toSubalgebra
/-
**IntermediateField.intermediateFieldMap_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `In
termediateField`。
形式化陈述：intermediateFieldMap_apply_coe (e : L ≃ₐ[K] L') (E : IntermediateField K L
) (a : E) : ↑(intermediateFieldMap e E a) = e a
参数：e : L ≃ₐ[K] L'；E : IntermediateField K L；a : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intermediateFieldMap_apply_coe (e : L ≃ₐ[K] L') (E : IntermediateField K L) (a : E) :
    ↑(intermediateFieldMap e E a) = e a :=
  rfl
/-
**IntermediateField.intermediateFieldMap_symm_apply_coe** 是 Mathlib 中的一个定理，位于命名空
间 `IntermediateField`。
形式化陈述：intermediateFieldMap_symm_apply_coe (e : L ≃ₐ[K] L') (E : IntermediateFiel
d K L) (a : E.map e.toAlgHom) : ↑((intermediateFieldMap e E).symm a) = e.symm a
参数：e : L ≃ₐ[K] L'；E : IntermediateField K L；a : E.map e.toAlgHom。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intermediateFieldMap_symm_apply_coe (e : L ≃ₐ[K] L') (E : IntermediateField K L)
    (a : E.map e.toAlgHom) : ↑((intermediateFieldMap e E).symm a) = e.symm a :=
  rfl

end IntermediateField

namespace AlgHom

variable (f : L →ₐ[K] L')

/-- The range of an algebra homomorphism, as an intermediate field. -/
@[simps toSubalgebra]
/-
**AlgHom.fieldRange** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：fieldRange : IntermediateField K L'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of an algebra homomorphism, as an intermediate field.
-/
def fieldRange : IntermediateField K L' :=
  { f.range, (f : L →+* L').fieldRange with }

@[simp]
/-
**AlgHom.coe_fieldRange** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_fieldRange : ↑f.fieldRange = Set.range f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fieldRange : ↑f.fieldRange = Set.range f :=
  rfl

@[simp]
/-
**AlgHom.fieldRange_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：fieldRange_toSubfield : f.fieldRange.toSubfield = (f : L ->+* L').fieldRan
ge
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fieldRange_toSubfield : f.fieldRange.toSubfield = (f : L →+* L').fieldRange :=
  rfl

variable {f} in
@[simp]
/-
**AlgHom.mem_fieldRange** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：mem_fieldRange {y : L'} : y in f.fieldRange ↔ exists x, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_fieldRange {y : L'} : y ∈ f.fieldRange ↔ ∃ x, f x = y :=
  Iff.rfl

/-- The isomorphism from `L` to the field range of the `AlgHom` `f`, sending `x` to `f x`. -/
@[simps! apply_coe]
/-
**AlgHom.equivFieldRange** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：equivFieldRange : L ≃ₐ[K] f.fieldRange
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism from `L` to the field range of the `AlgHom` `f`, sending `x` to 
`f x`.
-/
noncomputable def equivFieldRange : L ≃ₐ[K] f.fieldRange :=
  .ofBijective f.rangeRestrict ⟨f.rangeRestrict.injective, fun ⟨_, ⟨x, hx⟩⟩ ↦ ⟨x, Subtype.ext hx⟩⟩

@[deprecated (since := "2026-06-20")] alias equivFieldRange_apply := equivFieldRange_apply_coe

end AlgHom

variable (K L L') in
@[simp]
/-
**IsScalarTower.toAlgHom_fieldRange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsScalarTower.toAlgHom_fieldRange [Algebra L L'] [IsScalarTower K L L'] : 
(IsScalarTower.toAlgHom K L L').fieldRange = Set.range (algebraMap L L')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsScalarTower.toAlgHom_fieldRange [Algebra L L'] [IsScalarTower K L L'] :
    (IsScalarTower.toAlgHom K L L').fieldRange = Set.range (algebraMap L L') := by
  ext; simp

namespace IntermediateField

/-- The embedding from an intermediate field of `L / K` to `L`. -/
/-
**IntermediateField.val** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：val : S ->ₐ[K] L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding from an intermediate field of `L / K` to `L`.
-/
def val : S →ₐ[K] L :=
  S.toSubalgebra.val

@[simp]
/-
**IntermediateField.coe_val** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：coe_val : ⇑S.val = ((↑) : S -> L)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_val : ⇑S.val = ((↑) : S → L) :=
  rfl

@[simp]
/-
**IntermediateField.val_mk** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：val_mk {x : L} (hx : x in S) : S.val ⟨x, hx⟩ = x
参数：hx : x in S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_mk {x : L} (hx : x ∈ S) : S.val ⟨x, hx⟩ = x :=
  rfl
/-
**IntermediateField.range_val** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：range_val : S.val.range = S.toSubalgebra
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.range_val`：range_val : S.val.range = S
-/
theorem range_val : S.val.range = S.toSubalgebra :=
  S.toSubalgebra.range_val

@[simp]
/-
**IntermediateField.fieldRange_val** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：fieldRange_val : S.val.fieldRange = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
theorem fieldRange_val : S.val.fieldRange = S :=
  SetLike.ext' Subtype.range_val
/-
**IntermediateField.AlgHom.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateFiel
d.AlgHom`。
形式化陈述：{K : Type u_1} →   {L : Type u_2} →     [inst : Field K] →       [inst_1 :
 Field L] → [inst_2 : Algebra K L] → (S : IntermediateField K L) → Inhabited (↥S
 →ₐ[K] L)
参数：S : IntermediateField K L；↥S →ₐ[K] L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance AlgHom.inhabited : Inhabited (S →ₐ[K] L) :=
  ⟨S.val⟩
/-
**IntermediateField.aeval_coe** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：aeval_coe {R : Type*} [CommSemiring R] [Algebra R K] [Algebra R L] [IsScal
arTower R K L] (x : S) (P : R[X]) : aeval (x : L) P = aeval x P
参数：x : S；P : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
-/
theorem aeval_coe {R : Type*} [CommSemiring R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]
    (x : S) (P : R[X]) : aeval (x : L) P = aeval x P :=
  aeval_algHom_apply (S.val.restrictScalars R) x P

/-- The map `E → F` when `E` is an intermediate field contained in the intermediate field `F`.

This is the intermediate field version of `Subalgebra.inclusion`. -/
/-
**IntermediateField.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：inclusion {E F : IntermediateField K L} (hEF : E <= F) : E ->ₐ[K] F
参数：hEF : E <= F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `E → F` when `E` is an intermediate field contained in the intermediate 
field `F`.

This is the intermediate field version of `Subalgebra.inclusion`.
-/
def inclusion {E F : IntermediateField K L} (hEF : E ≤ F) : E →ₐ[K] F :=
  Subalgebra.inclusion hEF
/-
**IntermediateField.inclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：inclusion_injective {E F : IntermediateField K L} (hEF : E <= F) : Functio
n.Injective (inclusion hEF)
参数：hEF : E <= F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.inclusion_injective`：inclusion_injective : Function.Injective
 (inclusion h)
-/
theorem inclusion_injective {E F : IntermediateField K L} (hEF : E ≤ F) :
    Function.Injective (inclusion hEF) :=
  Subalgebra.inclusion_injective hEF

@[simp]
/-
**IntermediateField.inclusion_self** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：inclusion_self {E : IntermediateField K L} : inclusion (le_refl E) = AlgHo
m.id K E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.inclusion_self`：inclusion_self : inclusion (le_refl S) = AlgH
om.id R S
-/
theorem inclusion_self {E : IntermediateField K L} : inclusion (le_refl E) = AlgHom.id K E :=
  Subalgebra.inclusion_self

@[simp]
/-
**IntermediateField.inclusion_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：inclusion_inclusion {E F G : IntermediateField K L} (hEF : E <= F) (hFG : 
F <= G) (x : E) : inclusion hFG (inclusion hEF x) = inclusion (le_trans hEF hFG)
 x
参数：hEF : E <= F；hFG : F <= G；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.inclusion_inclusion`：inclusion_inclusion (hst : S <= T) (htu 
: T <= U) (x : S) : inclusion htu (inclusion hst x) = inclusion (le_trans hst ht
u) x
-/
theorem inclusion_inclusion {E F G : IntermediateField K L} (hEF : E ≤ F) (hFG : F ≤ G) (x : E) :
    inclusion hFG (inclusion hEF x) = inclusion (le_trans hEF hFG) x :=
  Subalgebra.inclusion_inclusion hEF hFG x

@[simp]
/-
**IntermediateField.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：coe_inclusion {E F : IntermediateField K L} (hEF : E <= F) (e : E) : (incl
usion hEF e : L) = e
参数：hEF : E <= F；e : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inclusion {E F : IntermediateField K L} (hEF : E ≤ F) (e : E) :
    (inclusion hEF e : L) = e :=
  rfl

variable {S}
/-
**IntermediateField.toSubalgebra_injective** 是 Mathlib 中的一个定理，位于命名空间 `Intermedia
teField`。
形式化陈述：toSubalgebra_injective : Function.Injective (toSubalgebra : IntermediateFi
eld K L -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toSubalgebra_injective : Function.Injective (toSubalgebra : IntermediateField K L → _) := by
  intro _ _ h
  ext
  simp_rw [← mem_toSubalgebra, h]
/-
**IntermediateField.toSubfield_injective** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：toSubfield_injective : Function.Injective (toSubfield : IntermediateField 
K L -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toSubfield_injective : Function.Injective (toSubfield : IntermediateField K L → _) := by
  intro _ _ h
  ext
  simp_rw [← mem_toSubfield, h]

variable {F E : IntermediateField K L}

@[simp]
/-
**IntermediateField.toSubalgebra_inj** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：toSubalgebra_inj : F.toSubalgebra = E.toSubalgebra ↔ F = E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IntermediateField.toSubalgebra_injective`：toSubalgebra_injective : Funct
ion.Injective (toSubalgebra : IntermediateField K L -> _)
-/
theorem toSubalgebra_inj : F.toSubalgebra = E.toSubalgebra ↔ F = E := toSubalgebra_injective.eq_iff
/-
**IntermediateField.toSubfield_inj** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：toSubfield_inj : F.toSubfield = E.toSubfield ↔ F = E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IntermediateField.toSubfield_injective`：toSubfield_injective : Function.
Injective (toSubfield : IntermediateField K L -> _)
-/
theorem toSubfield_inj : F.toSubfield = E.toSubfield ↔ F = E := toSubfield_injective.eq_iff
/-
**IntermediateField.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：map_injective (f : L ->ₐ[K] L') : Function.Injective (map f)
参数：f : L ->ₐ[K] L'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.toSubalgebra_inj`：toSubalgebra_inj : F.toSubalgebra = 
E.toSubalgebra ↔ F = E
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Subalgebra.map_injective`：map_injective {f : A ->ₐ[R] B} (hf : Function.
Injective f) : Function.Injective (map f)
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IntermediateField.toSubalgebra_map`：toSubalgebra_map (f : L ->ₐ[K] L') :
 (S.map f).toSubalgebra = S.toSubalgebra.map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.toSubalgebra_injective`：toSubalgebra_injective : Funct
ion.Injective (toSubalgebra : IntermediateField K L -> _)
-/
theorem map_injective (f : L →ₐ[K] L') : Function.Injective (map f) := by
  intro _ _ h
  rwa [← toSubalgebra_injective.eq_iff, toSubalgebra_map, toSubalgebra_map,
    (Subalgebra.map_injective f.injective).eq_iff, toSubalgebra_inj] at h

variable (S)
/-
**IntermediateField.set_range_subset** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：set_range_subset : Set.range (algebraMap K L) subseteq S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.range_subset`：range_subset : Set.range (algebraMap R A) subse
teq S
-/
theorem set_range_subset : Set.range (algebraMap K L) ⊆ S :=
  S.toSubalgebra.range_subset
/-
**IntermediateField.fieldRange_le** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：fieldRange_le : (algebraMap K L).fieldRange <= S.toSubfield
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.range_subset`：range_subset : Set.range (algebraMap R A) subse
teq S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.mem_fieldRange`：mem_fieldRange {f : K ->+* L} {y : L} : y in f.f
ieldRange ↔ exists x, f x = y
-/
theorem fieldRange_le : (algebraMap K L).fieldRange ≤ S.toSubfield := fun x hx =>
  S.toSubalgebra.range_subset (by rwa [Set.mem_range, ← RingHom.mem_fieldRange])

@[simp]
/-
**IntermediateField.toSubalgebra_le_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Inte
rmediateField`。
形式化陈述：toSubalgebra_le_toSubalgebra {S S' : IntermediateField K L} : S.toSubalgeb
ra <= S'.toSubalgebra ↔ S <= S'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubalgebra_le_toSubalgebra {S S' : IntermediateField K L} :
    S.toSubalgebra ≤ S'.toSubalgebra ↔ S ≤ S' :=
  Iff.rfl

@[simp]
/-
**IntermediateField.toSubalgebra_lt_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Inte
rmediateField`。
形式化陈述：toSubalgebra_lt_toSubalgebra {S S' : IntermediateField K L} : S.toSubalgeb
ra < S'.toSubalgebra ↔ S < S'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubalgebra_lt_toSubalgebra {S S' : IntermediateField K L} :
    S.toSubalgebra < S'.toSubalgebra ↔ S < S' :=
  Iff.rfl

variable {S}

section Tower

/-- Lift an intermediate field of an intermediate field. -/
/-
**IntermediateField.lift** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：lift {F : IntermediateField K L} (E : IntermediateField K F) : Intermediat
eField K L
参数：E : IntermediateField K F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift an intermediate field of an intermediate field.
-/
def lift {F : IntermediateField K L} (E : IntermediateField K F) : IntermediateField K L :=
  E.map (val F)
/-
**IntermediateField.lift_injective** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：lift_injective (F : IntermediateField K L) : Function.Injective F.lift
参数：F : IntermediateField K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.map_injective`：map_injective (f : L ->ₐ[K] L') : Funct
ion.Injective (map f)
-/
theorem lift_injective (F : IntermediateField K L) : Function.Injective F.lift :=
  map_injective F.val

@[simp]
/-
**IntermediateField.lift_inj** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：lift_inj {F : IntermediateField K L} (E E' : IntermediateField K F) : lift
 E = lift E' ↔ E = E'
参数：E E' : IntermediateField K F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IntermediateField.lift_injective`：lift_injective (F : IntermediateField 
K L) : Function.Injective F.lift
-/
theorem lift_inj {F : IntermediateField K L} (E E' : IntermediateField K F) :
    lift E = lift E' ↔ E = E' :=
  (lift_injective F).eq_iff
/-
**IntermediateField.lift_le** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：lift_le {F : IntermediateField K L} (E : IntermediateField K F) : lift E <
= F
参数：E : IntermediateField K F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem lift_le {F : IntermediateField K L} (E : IntermediateField K F) : lift E ≤ F := by
  rintro _ ⟨x, _, rfl⟩
  exact x.2
/-
**IntermediateField.mem_lift** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：mem_lift {F : IntermediateField K L} {E : IntermediateField K F} (x : F) :
 x.1 in lift E ↔ x in E
参数：x : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem mem_lift {F : IntermediateField K L} {E : IntermediateField K F} (x : F) :
    x.1 ∈ lift E ↔ x ∈ E :=
  Subtype.val_injective.mem_set_image

/-- The algEquiv between an intermediate field and its lift. -/
/-
**IntermediateField.liftAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：liftAlgEquiv {E : IntermediateField K L} (F : IntermediateField K E) : ↥F 
≃ₐ[K] lift F where toFun x
参数：F : IntermediateField K E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algEquiv between an intermediate field and its lift.
-/
def liftAlgEquiv {E : IntermediateField K L} (F : IntermediateField K E) : ↥F ≃ₐ[K] lift F where
  toFun x := ⟨x.1.1, (mem_lift x.1).mpr x.2⟩
  invFun x := ⟨⟨x.1, lift_le F x.2⟩, (mem_lift ⟨x.1, lift_le F x.2⟩).mp x.2⟩
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
/-
**IntermediateField.liftAlgEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：liftAlgEquiv_apply {E : IntermediateField K L} (F : IntermediateField K E)
 (x : F) : (liftAlgEquiv F x).1 = x
参数：F : IntermediateField K E；x : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftAlgEquiv_apply {E : IntermediateField K L} (F : IntermediateField K E) (x : F) :
    (liftAlgEquiv F x).1 = x := rfl

section RestrictScalars

variable (K)
variable [Algebra L' L] [IsScalarTower K L' L]

/-- Given a tower `L / ↥E / L' / K` of field extensions, where `E` is an `L'`-intermediate field of
`L`, reinterpret `E` as a `K`-intermediate field of `L`. -/
/-
**IntermediateField.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField
`。
形式化陈述：restrictScalars (E : IntermediateField L' L) : IntermediateField K L
参数：E : IntermediateField L' L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a tower `L / ↥E / L' / K` of field extensions, where `E` is an `L'`-interm
ediate field of
`L`, reinterpret `E` as a `K`-intermediate field of `L`.
-/
def restrictScalars (E : IntermediateField L' L) : IntermediateField K L :=
  { E.toSubfield, E.toSubalgebra.restrictScalars K with
    carrier := E.carrier }

@[simp]
/-
**IntermediateField.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：coe_restrictScalars {E : IntermediateField L' L} : (restrictScalars K E : 
Set L) = (E : Set L)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars {E : IntermediateField L' L} :
    (restrictScalars K E : Set L) = (E : Set L) :=
  rfl

@[simp]
/-
**IntermediateField.restrictScalars_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Inte
rmediateField`。
形式化陈述：restrictScalars_toSubalgebra {E : IntermediateField L' L} : (E.restrictSca
lars K).toSubalgebra = E.toSubalgebra.restrictScalars K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem restrictScalars_toSubalgebra {E : IntermediateField L' L} :
    (E.restrictScalars K).toSubalgebra = E.toSubalgebra.restrictScalars K :=
  SetLike.coe_injective rfl

@[simp]
/-
**IntermediateField.restrictScalars_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField`。
形式化陈述：restrictScalars_toSubfield {E : IntermediateField L' L} : (E.restrictScala
rs K).toSubfield = E.toSubfield
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem restrictScalars_toSubfield {E : IntermediateField L' L} :
    (E.restrictScalars K).toSubfield = E.toSubfield :=
  SetLike.coe_injective rfl

@[simp]
/-
**IntermediateField.mem_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：mem_restrictScalars {E : IntermediateField L' L} {x : L} : x in restrictSc
alars K E ↔ x in E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_restrictScalars {E : IntermediateField L' L} {x : L} :
    x ∈ restrictScalars K E ↔ x ∈ E :=
  Iff.rfl
/-
**IntermediateField.restrictScalars_injective** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField`。
形式化陈述：restrictScalars_injective : Function.Injective (restrictScalars K : Interm
ediateField L' L -> IntermediateField K L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.mem_restrictScalars`：mem_restrictScalars {E : Intermed
iateField L' L} {x : L} : x in restrictScalars K E ↔ x in E
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars K : IntermediateField L' L → IntermediateField K L) :=
  fun U V H => ext fun x => by rw [← mem_restrictScalars K, H, mem_restrictScalars]

@[simp]
/-
**IntermediateField.restrictScalars_inj** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：restrictScalars_inj {E E' : IntermediateField L' L} : E.restrictScalars K 
= E'.restrictScalars K ↔ E = E'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IntermediateField.restrictScalars_injective`：restrictScalars_injective :
 Function.Injective (restrictScalars K : IntermediateField L' L -> IntermediateF
ield K L)
-/
theorem restrictScalars_inj {E E' : IntermediateField L' L} :
    E.restrictScalars K = E'.restrictScalars K ↔ E = E' :=
  (restrictScalars_injective K).eq_iff

end RestrictScalars

/-- This was formerly an instance called `lift2_alg`, but an instance above already provides it. -/
/-
**IntermediateField.** 是 Mathlib 中的一个示例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This was formerly an instance called `lift2_alg`, but an instance above already 
provides it.
-/
example {F : IntermediateField K L} {E : IntermediateField F L} : Algebra K E := by infer_instance

end Tower

section equivMap

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
  {K : Type*} [Field K] [Algebra F K] (L : IntermediateField F E) (f : E →ₐ[F] K)

/-- Construct an algebra isomorphism from an equality of intermediate fields. -/
@[simps! apply]
/-
**IntermediateField.equivOfEq** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：equivOfEq {S T : IntermediateField F E} (h : S = T) : S ≃ₐ[F] T
参数：h : S = T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an algebra isomorphism from an equality of intermediate fields.
-/
def equivOfEq {S T : IntermediateField F E} (h : S = T) : S ≃ₐ[F] T :=
  Subalgebra.equivOfEq _ _ (congr_arg toSubalgebra h)

@[simp]
/-
**IntermediateField.equivOfEq_symm** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：equivOfEq_symm {S T : IntermediateField F E} (h : S = T) : (equivOfEq h).s
ymm = equivOfEq h.symm
参数：h : S = T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivOfEq_symm {S T : IntermediateField F E} (h : S = T) :
    (equivOfEq h).symm = equivOfEq h.symm :=
  rfl

@[simp]
/-
**IntermediateField.equivOfEq_rfl** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：equivOfEq_rfl (S : IntermediateField F E) : equivOfEq (rfl : S = S) = AlgE
quiv.refl
参数：S : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
-/
theorem equivOfEq_rfl (S : IntermediateField F E) : equivOfEq (rfl : S = S) = AlgEquiv.refl :=
  AlgEquiv.ext fun _ ↦ rfl

@[simp]
/-
**IntermediateField.equivOfEq_trans** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField
`。
形式化陈述：equivOfEq_trans {S T U : IntermediateField F E} (hST : S = T) (hTU : T = U
) : (equivOfEq hST).trans (equivOfEq hTU) = equivOfEq (hST.trans hTU)
参数：hST : S = T；hTU : T = U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivOfEq_trans {S T U : IntermediateField F E} (hST : S = T) (hTU : T = U) :
    (equivOfEq hST).trans (equivOfEq hTU) = equivOfEq (hST.trans hTU) :=
  rfl
/-
**IntermediateField.fieldRange_comp_val** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：fieldRange_comp_val : (f.comp L.val).fieldRange = L.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.toSubalgebra_injective`：toSubalgebra_injective : Funct
ion.Injective (toSubalgebra : IntermediateField K L -> _)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.toSubalgebra_map`：toSubalgebra_map (f : L ->ₐ[K] L') :
 (S.map f).toSubalgebra = S.toSubalgebra.map f
· 使用定理 `AlgHom.fieldRange_toSubalgebra`：∀ {K : Type u_1} {L : Type u_2} {L' : Ty
pe u_3} [inst : Field K] [inst_1 : Field L] [inst_2 : Field L']   [inst_3 : Alge
bra K L] [inst_4 : A…
· 使用定理 `AlgHom.range_comp`：range_comp (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) : (g.com
p f).range = f.range.map g
· 使用定理 `IntermediateField.range_val`：range_val : S.val.range = S.toSubalgebra
-/
theorem fieldRange_comp_val : (f.comp L.val).fieldRange = L.map f := toSubalgebra_injective <| by
  rw [toSubalgebra_map, AlgHom.fieldRange_toSubalgebra, AlgHom.range_comp, range_val]

/-- An intermediate field is isomorphic to its image under an `AlgHom`
(which is automatically injective). -/
/-
**IntermediateField.equivMap** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：equivMap : L ≃ₐ[F] L.map f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.fieldRange_comp_val`：fieldRange_comp_val : (f.comp L.v
al).fieldRange = L.map f

--- 原说明 ---
An intermediate field is isomorphic to its image under an `AlgHom`
(which is automatically injective).
-/
noncomputable def equivMap : L ≃ₐ[F] L.map f :=
  (AlgEquiv.ofInjective _ (f.comp L.val).injective).trans (equivOfEq (fieldRange_comp_val L f))

@[simp]
/-
**IntermediateField.coe_equivMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：coe_equivMap_apply (x : L) : ↑(equivMap L f x) = f x
参数：x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_equivMap_apply (x : L) : ↑(equivMap L f x) = f x := rfl

end equivMap

end IntermediateField

section ExtendScalars

namespace Subfield

variable {F E E' : Subfield L} (h : F ≤ E) (h' : F ≤ E') {x : L}

/-- If `F ≤ E` are two subfields of `L`, then `E` is also an intermediate field of
`L / F`. It can be viewed as an inverse to `IntermediateField.toSubfield`. -/
/-
**Subfield.extendScalars** 是 Mathlib 中的一个定义，位于命名空间 `Subfield`。
形式化陈述：extendScalars : IntermediateField F L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F ≤ E` are two subfields of `L`, then `E` is also an intermediate field of
`L / F`. It can be viewed as an inverse to `IntermediateField.toSubfield`.
-/
def extendScalars : IntermediateField F L := E.toIntermediateField fun ⟨_, hf⟩ ↦ h hf

@[simp]
/-
**Subfield.coe_extendScalars** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_extendScalars : (extendScalars h : Set L) = (E : Set L)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_extendScalars : (extendScalars h : Set L) = (E : Set L) := rfl

@[simp]
/-
**Subfield.extendScalars_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：extendScalars_toSubfield : (extendScalars h).toSubfield = E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem extendScalars_toSubfield : (extendScalars h).toSubfield = E := SetLike.coe_injective rfl

@[simp]
/-
**Subfield.mem_extendScalars** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_extendScalars : x in extendScalars h ↔ x in E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_extendScalars : x ∈ extendScalars h ↔ x ∈ E := Iff.rfl
/-
**Subfield.extendScalars_le_extendScalars_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subfiel
d`。
形式化陈述：extendScalars_le_extendScalars_iff : extendScalars h <= extendScalars h' ↔
 E <= E'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem extendScalars_le_extendScalars_iff : extendScalars h ≤ extendScalars h' ↔ E ≤ E' := Iff.rfl
/-
**Subfield.extendScalars_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：extendScalars_le_iff (E' : IntermediateField F L) : extendScalars h <= E' 
↔ E <= E'.toSubfield
参数：E' : IntermediateField F L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem extendScalars_le_iff (E' : IntermediateField F L) :
    extendScalars h ≤ E' ↔ E ≤ E'.toSubfield := Iff.rfl
/-
**Subfield.le_extendScalars_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：le_extendScalars_iff (E' : IntermediateField F L) : E' <= extendScalars h 
↔ E'.toSubfield <= E
参数：E' : IntermediateField F L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_extendScalars_iff (E' : IntermediateField F L) :
    E' ≤ extendScalars h ↔ E'.toSubfield ≤ E := Iff.rfl

variable (F)

/-- `Subfield.extendScalars.orderIso` bundles `Subfield.extendScalars`
into an order isomorphism from
`{ E : Subfield L // F ≤ E }` to `IntermediateField F L`. Its inverse is
`IntermediateField.toSubfield`. -/
@[simps apply symm_apply]
/-
**Subfield.extendScalars.orderIso** 是 Mathlib 中的一个定义，位于命名空间 `Subfield.extendScal
ars`。
形式化陈述：{L : Type u_2} → [inst : Field L] → (F : Subfield L) → { E // F ≤ E } ≃o I
ntermediateField (↥F) L
参数：F : Subfield L；↥F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subfield.extendScalars.orderIso` bundles `Subfield.extendScalars`
into an order isomorphism from
`{ E : Subfield L // F ≤ E }` to `IntermediateField F L`. Its inverse is
`IntermediateField.toSubfield`.
-/
def extendScalars.orderIso :
    { E : Subfield L // F ≤ E } ≃o IntermediateField F L where
  toFun E := extendScalars E.2
  invFun E := ⟨E.toSubfield, fun x hx ↦ E.algebraMap_mem ⟨x, hx⟩⟩
  map_rel_iff' {E E'} := by
    simp only [Equiv.coe_fn_mk]
    exact extendScalars_le_extendScalars_iff _ _
/-
**Subfield.extendScalars_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：extendScalars_injective : Function.Injective fun E : { E : Subfield L // F
 <= E } => extendScalars E.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
-/
theorem extendScalars_injective :
    Function.Injective fun E : { E : Subfield L // F ≤ E } ↦ extendScalars E.2 :=
  (extendScalars.orderIso F).injective

end Subfield

namespace IntermediateField

variable {F E E' : IntermediateField K L} (h : F ≤ E) (h' : F ≤ E') {x : L}

/-- If `F ≤ E` are two intermediate fields of `L / K`, then `E` is also an intermediate field of
`L / F`. It can be viewed as an inverse to `IntermediateField.restrictScalars`. -/
/-
**IntermediateField.extendScalars** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：extendScalars : IntermediateField F L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F ≤ E` are two intermediate fields of `L / K`, then `E` is also an intermedi
ate field of
`L / F`. It can be viewed as an inverse to `IntermediateField.restrictScalars`.
-/
def extendScalars : IntermediateField F L :=
  Subfield.extendScalars (show F.toSubfield ≤ E.toSubfield from h)

@[simp]
/-
**IntermediateField.coe_extendScalars** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：coe_extendScalars : (extendScalars h : Set L) = (E : Set L)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_extendScalars : (extendScalars h : Set L) = (E : Set L) := rfl

@[simp]
/-
**IntermediateField.extendScalars_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField`。
形式化陈述：extendScalars_toSubfield : (extendScalars h).toSubfield = E.toSubfield
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem extendScalars_toSubfield : (extendScalars h).toSubfield = E.toSubfield :=
  SetLike.coe_injective rfl

@[simp]
/-
**IntermediateField.mem_extendScalars** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：mem_extendScalars : x in extendScalars h ↔ x in E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_extendScalars : x ∈ extendScalars h ↔ x ∈ E := Iff.rfl

@[simp]
/-
**IntermediateField.extendScalars_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField`。
形式化陈述：extendScalars_restrictScalars : (extendScalars h).restrictScalars K = E
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extendScalars_restrictScalars : (extendScalars h).restrictScalars K = E := rfl
/-
**IntermediateField.extendScalars_le_extendScalars_iff** 是 Mathlib 中的一个定理，位于命名空间
 `IntermediateField`。
形式化陈述：extendScalars_le_extendScalars_iff : extendScalars h <= extendScalars h' ↔
 E <= E'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem extendScalars_le_extendScalars_iff : extendScalars h ≤ extendScalars h' ↔ E ≤ E' := Iff.rfl
/-
**IntermediateField.extendScalars_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：extendScalars_le_iff (E' : IntermediateField F L) : extendScalars h <= E' 
↔ E <= E'.restrictScalars K
参数：E' : IntermediateField F L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem extendScalars_le_iff (E' : IntermediateField F L) :
    extendScalars h ≤ E' ↔ E ≤ E'.restrictScalars K := Iff.rfl
/-
**IntermediateField.le_extendScalars_iff** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：le_extendScalars_iff (E' : IntermediateField F L) : E' <= extendScalars h 
↔ E'.restrictScalars K <= E
参数：E' : IntermediateField F L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_extendScalars_iff (E' : IntermediateField F L) :
    E' ≤ extendScalars h ↔ E'.restrictScalars K ≤ E := Iff.rfl

variable (F)

/-- `IntermediateField.extendScalars.orderIso` bundles `IntermediateField.extendScalars`
into an order isomorphism from
`{ E : IntermediateField K L // F ≤ E }` to `IntermediateField F L`. Its inverse is
`IntermediateField.restrictScalars`. -/
@[simps]
/-
**IntermediateField.extendScalars.orderIso** 是 Mathlib 中的一个定义，位于命名空间 `Intermedia
teField.extendScalars`。
形式化陈述：{K : Type u_1} →   {L : Type u_2} →     [inst : Field K] →       [inst_1 :
 Field L] →         [inst_2 : Algebra K L] → (F : IntermediateField K L) → { E /
/ F ≤ E } ≃o IntermediateField (↥F) L
参数：F : IntermediateField K L；↥F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IntermediateField.extendScalars.orderIso` bundles `IntermediateField.extendScal
ars`
into an order isomorphism from
`{ E : IntermediateField K L // F ≤ E }` to `IntermediateField F L`. Its inverse
 is
`IntermediateField.restrictScalars`.
-/
def extendScalars.orderIso : { E : IntermediateField K L // F ≤ E } ≃o IntermediateField F L where
  toFun E := extendScalars E.2
  invFun E := ⟨E.restrictScalars K, fun x hx ↦ E.algebraMap_mem ⟨x, hx⟩⟩
  map_rel_iff' {E E'} := by
    simp only [Equiv.coe_fn_mk]
    exact extendScalars_le_extendScalars_iff _ _
/-
**IntermediateField.extendScalars_injective** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField`。
形式化陈述：extendScalars_injective : Function.Injective fun E : { E : IntermediateFie
ld K L // F <= E } => extendScalars E.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
-/
theorem extendScalars_injective :
    Function.Injective fun E : { E : IntermediateField K L // F ≤ E } ↦ extendScalars E.2 :=
  (extendScalars.orderIso F).injective

end IntermediateField

end ExtendScalars

namespace IntermediateField

variable {S}

section Tower

section Restrict

variable {F E : IntermediateField K L} (h : F ≤ E)

/--
If `F ≤ E` are two intermediate fields of `L / K`, then `F` is also an intermediate field of
`E / K`. It is an inverse of `IntermediateField.lift`, and can be viewed as a dual to
`IntermediateField.extendScalars`.
-/
/-
**IntermediateField.restrict** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：restrict : IntermediateField K E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F ≤ E` are two intermediate fields of `L / K`, then `F` is also an intermedi
ate field of
`E / K`. It is an inverse of `IntermediateField.lift`, and can be viewed as a du
al to
`IntermediateField.extendScalars`.
-/
def restrict : IntermediateField K E :=
  (IntermediateField.inclusion h).fieldRange
/-
**IntermediateField.mem_restrict** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：mem_restrict (x : E) : x in restrict h ↔ x.1 in F
参数：x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Set.range_inclusion`：range_inclusion (h : s subseteq t) : range (inclusi
on h) = { x : t | (x : α) in s }
-/
theorem mem_restrict (x : E) : x ∈ restrict h ↔ x.1 ∈ F :=
  Set.ext_iff.mp (Set.range_inclusion h) x

@[simp]
/-
**IntermediateField.lift_restrict** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：lift_restrict : lift (restrict h) = F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `IntermediateField.lift_le`：lift_le {F : IntermediateField K L} (E : Inte
rmediateField K F) : lift E <= F
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.mem_restrict`：mem_restrict (x : E) : x in restrict h ↔
 x.1 in F
· 使用定理 `IntermediateField.mem_lift`：mem_lift {F : IntermediateField K L} {E : In
termediateField K F} (x : F) : x.1 in lift E ↔ x in E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem lift_restrict : lift (restrict h) = F := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · let y : E := ⟨x, lift_le (restrict h) hx⟩
    exact (mem_restrict h y).1 ((mem_lift y).1 hx)
  · let y : E := ⟨x, h hx⟩
    exact (mem_lift y).2 ((mem_restrict h y).2 hx)

/--
`F` is equivalent to `F` as an intermediate field of `E / K`.
-/
/-
**IntermediateField.restrictAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateFiel
d`。
形式化陈述：restrictAlgEquiv : F ≃ₐ[K] ↥(IntermediateField.restrict h)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F` is equivalent to `F` as an intermediate field of `E / K`.
-/
noncomputable def restrictAlgEquiv :
    F ≃ₐ[K] ↥(IntermediateField.restrict h) :=
  AlgEquiv.ofInjectiveField _

@[deprecated (since := "2026-07-25")]
alias restrict_algEquiv := restrictAlgEquiv

end Restrict

end Tower

end IntermediateField

