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

/--
Definition of `IntermediateField` / `IntermediateField` 的定义

English:
structure IntermediateField
  parameters: extends Subalgebra K L
  extends: Subalgebra K L
  axioms and operations (1):
    - inv_mem' : forall x in carrier, x⁻¹ in carrier

中文:
结构 中间域
  参数: extends 子代数 K L
  继承: 子代数 K L
  公理与运算 (1 个):
    - inv_mem' : 对任意 x in carrier, x⁻¹ in carrier
-/
structure IntermediateField extends Subalgebra K L where
  inv_mem' : forall x in carrier, x⁻¹ in carrier

/-- Reinterpret an `IntermediateField` as a `Subalgebra`. -/
add_decl_doc IntermediateField.toSubalgebra

variable {K L L'}
variable (S : IntermediateField K L)

namespace IntermediateField

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (IntermediateField K L) L
  body: ⟨fun S => S.toSubalgebra.carrier, by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp ⟩

中文:
实例 :
  签名: 集合状 (中间域 K L) L
  定义体: ⟨fun S => S.toSubalgebra.carrier, by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp ⟩

Depends on / 依赖: S.toSubalgebra.carrier, carrier, toSubalgebra
-/
instance : SetLike (IntermediateField K L) L :=
  ⟨fun S => S.toSubalgebra.carrier, by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (IntermediateField K L)
  body: .ofSetLike (IntermediateField K L) L

中文:
实例 :
  签名: 偏序 (中间域 K L)
  定义体: .ofSetLike (IntermediateField K L) L

Depends on / 依赖: IntermediateField, ofSetLike
-/
instance : PartialOrder (IntermediateField K L) := .ofSetLike (IntermediateField K L) L

/--
theorem `neg_mem` / 定理 `neg_mem`

English:
theorem neg_mem
  given: {x : L} (hx : x in S)
  statement: -x in S
  proof: by
  change -x in S.toSubalgebra; simpa

中文:
定理 neg_mem
  条件: {x : L} (hx : x in S)
  结论: -x in S
  证明: by
  change -x in S.toSubalgebra; simpa
-/
protected theorem neg_mem {x : L} (hx : x in S) : -x in S := by
  change -x in S.toSubalgebra; simpa

/-- Reinterpret an `IntermediateField` as a `Subfield`. -/
@[reducible]
/--
Definition of `toSubfield` / `toSubfield` 的定义

English:
definition toSubfield
  signature: : Subfield L
  body: { S.toSubalgebra with
    neg_mem' := S.neg_mem,
    inv_mem' := S.inv_mem' }

中文:
定义 toSubfield
  签名: : 子域 L
  定义体: { S.toSubalgebra with
    neg_mem' := S.neg_mem,
    inv_mem' := S.inv_mem' }

Depends on / 依赖: S.inv_mem, S.neg_mem, S.toSubalgebra, inv_mem, neg_mem, toSubalgebra
-/
def toSubfield : Subfield L :=
  { S.toSubalgebra with
    neg_mem' := S.neg_mem,
    inv_mem' := S.inv_mem' }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubfieldClass (IntermediateField K L) L
  body: s.add_mem'
  zero_mem {s} := s.zero_mem'
  neg_mem {s} := s.neg_mem
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  inv_mem {s} := s.inv_mem' _

中文:
实例 :
  签名: 子域类 (中间域 K L) L
  定义体: s.add_mem'
  zero_mem {s} := s.zero_mem'
  neg_mem {s} := s.neg_mem
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  inv_mem {s} := s.inv_mem' _

Depends on / 依赖: add_mem, s.add_mem
-/
instance : SubfieldClass (IntermediateField K L) L where
  add_mem {s} := s.add_mem'
  zero_mem {s} := s.zero_mem'
  neg_mem {s} := s.neg_mem
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  inv_mem {s} := s.inv_mem' _

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : IntermediateField K L} {x : L}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

中文:
定理 mem_carrier
  条件: {s : 中间域 K L} {x : L}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : IntermediateField K L} {x : L} : x in s.carrier ↔ x in s :=
  Iff.rfl

/-- Two intermediate fields are equal if they have the same elements. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : IntermediateField K L} (h : forall x, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

@[simp]

中文:
定理 ext
  条件: {S T : 中间域 K L} (h : 对任意 x, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

@[simp]

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : IntermediateField K L} (h : forall x, x in S ↔ x in T) : S = T :=
  SetLike.ext h

@[simp]
/--
theorem `coe_toSubalgebra` / 定理 `coe_toSubalgebra`

English:
theorem coe_toSubalgebra
  statement: (S.toSubalgebra : Set L) = S
  proof: rfl

@[simp]

中文:
定理 coe_toSubalgebra
  结论: (S.toSubalgebra : 集合 L) = S
  证明: rfl

@[simp]
-/
theorem coe_toSubalgebra : (S.toSubalgebra : Set L) = S :=
  rfl

@[simp]
/--
theorem `coe_toSubfield` / 定理 `coe_toSubfield`

English:
theorem coe_toSubfield
  statement: (S.toSubfield : Set L) = S
  proof: rfl

@[simp]

中文:
定理 coe_toSubfield
  结论: (S.toSubfield : 集合 L) = S
  证明: rfl

@[simp]
-/
theorem coe_toSubfield : (S.toSubfield : Set L) = S :=
  rfl

@[simp]
/--
theorem `coe_type_toSubalgebra` / 定理 `coe_type_toSubalgebra`

English:
theorem coe_type_toSubalgebra
  statement: (S.toSubalgebra : Type _) = S
  proof: rfl

@[simp]

中文:
定理 coe_type_toSubalgebra
  结论: (S.toSubalgebra : 类型 _) = S
  证明: rfl

@[simp]
-/
theorem coe_type_toSubalgebra : (S.toSubalgebra : Type _) = S :=
  rfl

@[simp]
/--
theorem `coe_type_toSubfield` / 定理 `coe_type_toSubfield`

English:
theorem coe_type_toSubfield
  statement: (S.toSubfield : Type _) = S
  proof: rfl

@[simp]

中文:
定理 coe_type_toSubfield
  结论: (S.toSubfield : 类型 _) = S
  证明: rfl

@[simp]
-/
theorem coe_type_toSubfield : (S.toSubfield : Type _) = S :=
  rfl

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: (s : Subsemiring L) (hK : forall x, algebraMap K L x in s) (hi) (x : L)
  proof: Iff.rfl

@[simp]

中文:
定理 mem_mk
  条件: (s : 子半环 L) (hK : 对任意 x, algebraMap K L x in s) (hi) (x : L)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk (s : Subsemiring L) (hK : forall x, algebraMap K L x in s) (hi) (x : L) :
    x in IntermediateField.mk (Subalgebra.mk s hK) hi ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `mem_toSubalgebra` / 定理 `mem_toSubalgebra`

English:
theorem mem_toSubalgebra
  given: (s : IntermediateField K L) (x : L)
  statement: x in s.toSubalgebra ↔ x in s
  proof: Iff.rfl

中文:
定理 mem_toSubalgebra
  条件: (s : 中间域 K L) (x : L)
  结论: x in s.toSubalgebra ↔ x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl, mk_surjective
-/
theorem mem_toSubalgebra (s : IntermediateField K L) (x : L) : x in s.toSubalgebra ↔ x in s :=
  Iff.rfl

/--
theorem `mem_toSubfield` / 定理 `mem_toSubfield`

English:
theorem mem_toSubfield
  given: (s : IntermediateField K L) (x : L)
  statement: x in s.toSubfield ↔ x in s
  proof: Iff.rfl

中文:
定理 mem_toSubfield
  条件: (s : 中间域 K L) (x : L)
  结论: x in s.toSubfield ↔ x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl, QuotientGroup, QuotientGroup.eq.trans, _root_, _root_.eq_inv_mul_iff_mul_eq, eq_inv_mul_iff_mul_eq, exists_eq_right
-/
theorem mem_toSubfield (s : IntermediateField K L) (x : L) : x in s.toSubfield ↔ x in s :=
  Iff.rfl

/--
theorem `toSubalgebra_strictMono` / 定理 `toSubalgebra_strictMono`

English:
theorem toSubalgebra_strictMono
  proof: fun _ _ h => h

中文:
定理 toSubalgebra_strictMono
  证明: fun _ _ h => h
-/
theorem toSubalgebra_strictMono :
    StrictMono (IntermediateField.toSubalgebra : _ -> Subalgebra K L) := fun _ _ h => h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : IntermediateField K L) (s : Set L) (hs : s = ↑S)
  body: S.toSubalgebra.copy s hs
  inv_mem' := hs.symm ▸ S.inv_mem'

@[simp]

中文:
定义 copy
  签名: (S : 中间域 K L) (s : 集合 L) (hs : s = ↑S)
  定义体: S.toSubalgebra.copy s hs
  inv_mem' := hs.symm ▸ S.inv_mem'

@[simp]
-/
protected def copy (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) :
    IntermediateField K L where
  toSubalgebra := S.toSubalgebra.copy s hs
  inv_mem' := hs.symm ▸ S.inv_mem'

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (S : IntermediateField K L) (s : Set L) (hs : s = ↑S)
  proof: rfl

中文:
定理 coe_copy
  条件: (S : 中间域 K L) (s : 集合 L) (hs : s = ↑S)
  证明: rfl
-/
theorem coe_copy (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) :
    (S.copy s hs : Set L) = s :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (S : IntermediateField K L) (s : Set L) (hs : s = ↑S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: (S : 中间域 K L) (s : 集合 L) (hs : s = ↑S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

section InheritedLemmas

/-! ### Lemmas inherited from more general structures

The declarations in this section derive from the fact that an `IntermediateField` is also a
subalgebra or subfield. Their use should be replaceable with the corresponding lemma from a
subobject class.
-/


/--
theorem `algebraMap_mem` / 定理 `algebraMap_mem`

English:
theorem algebraMap_mem
  given: (x : K)
  statement: algebraMap K L x in S
  proof: S.algebraMap_mem' x

中文:
定理 algebraMap_mem
  条件: (x : K)
  结论: algebraMap K L x in S
  证明: S.algebraMap_mem' x

Depends on / 依赖: S.algebraMap_mem, algebraMap_mem
-/
theorem algebraMap_mem (x : K) : algebraMap K L x in S :=
  S.algebraMap_mem' x

/--
theorem `smul_mem` / 定理 `smul_mem`

English:
theorem smul_mem
  given: {y : L}
  statement: y in S -> forall {x : K}, x • y in S
  proof: S.toSubalgebra.smul_mem

中文:
定理 smul_mem
  条件: {y : L}
  结论: y in S -> 对任意 {x : K}, x • y in S
  证明: S.toSubalgebra.smul_mem

Depends on / 依赖: S.toSubalgebra.smul_mem, smul_mem, toSubalgebra
-/
theorem smul_mem {y : L} : y in S -> forall {x : K}, x • y in S :=
  S.toSubalgebra.smul_mem

/--
theorem `one_mem` / 定理 `one_mem`

English:
theorem one_mem
  statement: (1 : L) in S
  proof: one_mem S

中文:
定理 one_mem
  结论: (1 : L) in S
  证明: one_mem S
-/
protected theorem one_mem : (1 : L) in S :=
  one_mem S

/--
theorem `zero_mem` / 定理 `zero_mem`

English:
theorem zero_mem
  statement: (0 : L) in S
  proof: zero_mem S

中文:
定理 zero_mem
  结论: (0 : L) in S
  证明: zero_mem S
-/
protected theorem zero_mem : (0 : L) in S :=
  zero_mem S

/--
theorem `mul_mem` / 定理 `mul_mem`

English:
theorem mul_mem
  given: {x y : L}
  statement: x in S -> y in S -> x * y in S
  proof: mul_mem

中文:
定理 mul_mem
  条件: {x y : L}
  结论: x in S -> y in S -> x * y in S
  证明: mul_mem
-/
protected theorem mul_mem {x y : L} : x in S -> y in S -> x * y in S :=
  mul_mem

/--
theorem `add_mem` / 定理 `add_mem`

English:
theorem add_mem
  given: {x y : L}
  statement: x in S -> y in S -> x + y in S
  proof: add_mem

中文:
定理 add_mem
  条件: {x y : L}
  结论: x in S -> y in S -> x + y in S
  证明: add_mem
-/
protected theorem add_mem {x y : L} : x in S -> y in S -> x + y in S :=
  add_mem

/--
theorem `sub_mem` / 定理 `sub_mem`

English:
theorem sub_mem
  given: {x y : L}
  statement: x in S -> y in S -> x - y in S
  proof: sub_mem

中文:
定理 sub_mem
  条件: {x y : L}
  结论: x in S -> y in S -> x - y in S
  证明: sub_mem
-/
protected theorem sub_mem {x y : L} : x in S -> y in S -> x - y in S :=
  sub_mem

/--
theorem `inv_mem` / 定理 `inv_mem`

English:
theorem inv_mem
  given: {x : L}
  statement: x in S -> x⁻¹ in S
  proof: inv_mem

中文:
定理 inv_mem
  条件: {x : L}
  结论: x in S -> x⁻¹ in S
  证明: inv_mem
-/
protected theorem inv_mem {x : L} : x in S -> x⁻¹ in S :=
  inv_mem

/--
theorem `div_mem` / 定理 `div_mem`

English:
theorem div_mem
  given: {x y : L}
  statement: x in S -> y in S -> x / y in S
  proof: div_mem

中文:
定理 div_mem
  条件: {x y : L}
  结论: x in S -> y in S -> x / y in S
  证明: div_mem
-/
protected theorem div_mem {x y : L} : x in S -> y in S -> x / y in S :=
  div_mem

/--
theorem `list_prod_mem` / 定理 `list_prod_mem`

English:
theorem list_prod_mem
  given: {l : List L}
  statement: (forall x in l, x in S) -> l.prod in S
  proof: list_prod_mem

中文:
定理 list_prod_mem
  条件: {l : 列表 L}
  结论: (对任意 x in l, x in S) -> l.乘积 in S
  证明: list_prod_mem
-/
protected theorem list_prod_mem {l : List L} : (forall x in l, x in S) -> l.prod in S :=
  list_prod_mem

/--
theorem `list_sum_mem` / 定理 `list_sum_mem`

English:
theorem list_sum_mem
  given: {l : List L}
  statement: (forall x in l, x in S) -> l.sum in S
  proof: list_sum_mem

中文:
定理 list_sum_mem
  条件: {l : 列表 L}
  结论: (对任意 x in l, x in S) -> l.求和 in S
  证明: list_sum_mem
-/
protected theorem list_sum_mem {l : List L} : (forall x in l, x in S) -> l.sum in S :=
  list_sum_mem

/--
theorem `multiset_prod_mem` / 定理 `multiset_prod_mem`

English:
theorem multiset_prod_mem
  given: (m : Multiset L)
  statement: (forall a in m, a in S) -> m.prod in S
  proof: multiset_prod_mem m

中文:
定理 multiset_prod_mem
  条件: (m : Multiset L)
  结论: (对任意 a in m, a in S) -> m.乘积 in S
  证明: multiset_prod_mem m

Depends on / 依赖: c.mul, c.refl
-/
protected theorem multiset_prod_mem (m : Multiset L) : (forall a in m, a in S) -> m.prod in S :=
  multiset_prod_mem m

/--
theorem `multiset_sum_mem` / 定理 `multiset_sum_mem`

English:
theorem multiset_sum_mem
  given: (m : Multiset L)
  statement: (forall a in m, a in S) -> m.sum in S
  proof: multiset_sum_mem m

中文:
定理 multiset_sum_mem
  条件: (m : Multiset L)
  结论: (对任意 a in m, a in S) -> m.求和 in S
  证明: multiset_sum_mem m
-/
protected theorem multiset_sum_mem (m : Multiset L) : (forall a in m, a in S) -> m.sum in S :=
  multiset_sum_mem m

/--
theorem `prod_mem` / 定理 `prod_mem`

English:
theorem prod_mem
  given: {ι : Type*} {t : Finset ι} {f : ι -> L} (h : forall c in t, f c in S)
  proof: prod_mem h

中文:
定理 prod_mem
  条件: {ι : 类型} {t : 有限集 ι} {f : ι -> L} (h : 对任意 c in t, f c in S)
  证明: prod_mem h
-/
protected theorem prod_mem {ι : Type*} {t : Finset ι} {f : ι -> L} (h : forall c in t, f c in S) :
    (∏ i in t, f i) in S :=
  prod_mem h

/--
theorem `sum_mem` / 定理 `sum_mem`

English:
theorem sum_mem
  given: {ι : Type*} {t : Finset ι} {f : ι -> L} (h : forall c in t, f c in S)
  proof: sum_mem h

中文:
定理 sum_mem
  条件: {ι : 类型} {t : 有限集 ι} {f : ι -> L} (h : 对任意 c in t, f c in S)
  证明: sum_mem h
-/
protected theorem sum_mem {ι : Type*} {t : Finset ι} {f : ι -> L} (h : forall c in t, f c in S) :
    (∑ i in t, f i) in S :=
  sum_mem h

/--
theorem `pow_mem` / 定理 `pow_mem`

English:
theorem pow_mem
  given: {x : L} (hx : x in S) (n : Int)
  statement: x ^ n in S
  proof: zpow_mem hx n

中文:
定理 pow_mem
  条件: {x : L} (hx : x in S) (n : 整数)
  结论: x ^ n in S
  证明: zpow_mem hx n
-/
protected theorem pow_mem {x : L} (hx : x in S) (n : Int) : x ^ n in S :=
  zpow_mem hx n

/--
theorem `zsmul_mem` / 定理 `zsmul_mem`

English:
theorem zsmul_mem
  given: {x : L} (hx : x in S) (n : Int)
  statement: n • x in S
  proof: zsmul_mem hx n

中文:
定理 zsmul_mem
  条件: {x : L} (hx : x in S) (n : 整数)
  结论: n • x in S
  证明: zsmul_mem hx n
-/
protected theorem zsmul_mem {x : L} (hx : x in S) (n : Int) : n • x in S :=
  zsmul_mem hx n

/--
theorem `intCast_mem` / 定理 `intCast_mem`

English:
theorem intCast_mem
  given: (n : Int)
  statement: (n : L) in S
  proof: intCast_mem S n

@[simp, norm_cast]

中文:
定理 intCast_mem
  条件: (n : 整数)
  结论: (n : L) in S
  证明: intCast_mem S n

@[simp, norm_cast]
-/
protected theorem intCast_mem (n : Int) : (n : L) in S :=
  intCast_mem S n

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (x y : S)
  statement: (↑(x + y) : L) = ↑x + ↑y
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  条件: (x y : S)
  结论: (↑(x + y) : L) = ↑x + ↑y
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_add (x y : S) : (↑(x + y) : L) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (x : S)
  statement: (↑(-x) : L) = -↑x
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_neg
  条件: (x : S)
  结论: (↑(-x) : L) = -↑x
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_neg (x : S) : (↑(-x) : L) = -↑x :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : S)
  statement: (↑(x * y) : L) = ↑x * ↑y
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mul
  条件: (x y : S)
  结论: (↑(x * y) : L) = ↑x * ↑y
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_mul (x y : S) : (↑(x * y) : L) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (x : S)
  statement: (↑x⁻¹ : L) = (↑x)⁻¹
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_inv
  条件: (x : S)
  结论: (↑x⁻¹ : L) = (↑x)⁻¹
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_inv (x : S) : (↑x⁻¹ : L) = (↑x)⁻¹ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: (x y : S)
  statement: (↑(x / y) : L) = ↑x / ↑y
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_div
  条件: (x y : S)
  结论: (↑(x / y) : L) = ↑x / ↑y
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_div (x y : S) : (↑(x / y) : L) = ↑x / ↑y :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : S) : L) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ((0 : S) : L) = 0
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_zero : ((0 : S) : L) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : S) : L) = 1
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_one
  结论: ((1 : S) : L) = 1
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_one : ((1 : S) : L) = 1 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (x : S) (n : Nat)
  statement: (↑(x ^ n : S) : L) = (x : L) ^ n
  proof: SubmonoidClass.coe_pow x n

中文:
定理 coe_pow
  条件: (x : S) (n : 自然数)
  结论: (↑(x ^ n : S) : L) = (x : L) ^ n
  证明: SubmonoidClass.coe_pow x n
-/
protected theorem coe_pow (x : S) (n : Nat) : (↑(x ^ n : S) : L) = (x : L) ^ n :=
  SubmonoidClass.coe_pow x n

end InheritedLemmas

/--
theorem `natCast_mem` / 定理 `natCast_mem`

English:
theorem natCast_mem
  given: (n : Nat)
  statement: (n : L) in S
  proof: by simp

中文:
定理 natCast_mem
  条件: (n : 自然数)
  结论: (n : L) in S
  证明: by simp
-/
theorem natCast_mem (n : Nat) : (n : L) in S := by simp

/--
Instance `instSMulMemClass` / 实例 `instSMulMemClass`

English:
instance instSMulMemClass
  signature: : SMulMemClass (IntermediateField K L) K L where
  body: fun _ _ hx => IntermediateField.smul_mem _ hx

中文:
实例 instSMulMemClass
  签名: : SMulMem类 (中间域 K L) K L where
  定义体: fun _ _ hx => IntermediateField.smul_mem _ hx

Depends on / 依赖: IntermediateField, IntermediateField.smul_mem, smul_mem
-/
instance instSMulMemClass : SMulMemClass (IntermediateField K L) K L where
  smul_mem := fun _ _ hx => IntermediateField.smul_mem _ hx

end IntermediateField

/--
Definition of `Subalgebra.toIntermediateField` / `Subalgebra.toIntermediateField` 的定义

English:
definition Subalgebra.toIntermediateField
  signature: (S : Subalgebra K L) (inv_mem : forall x in S, x⁻¹ in S)
  body: { S with
    inv_mem' := inv_mem }

@[simp]

中文:
定义 子代数.to整数ermediateField
  签名: (S : 子代数 K L) (inv_mem : 对任意 x in S, x⁻¹ in S)
  定义体: { S with
    inv_mem' := inv_mem }

@[simp]

Depends on / 依赖: inv_mem
-/
def Subalgebra.toIntermediateField (S : Subalgebra K L) (inv_mem : forall x in S, x⁻¹ in S) :
    IntermediateField K L :=
  { S with
    inv_mem' := inv_mem }

@[simp]
/--
theorem `toSubalgebra_toIntermediateField` / 定理 `toSubalgebra_toIntermediateField`

English:
theorem toSubalgebra_toIntermediateField
  given: (S : Subalgebra K L) (inv_mem : forall x in S, x⁻¹ in S)
  proof: by
  ext
  rfl

@[simp]

中文:
定理 toSubalgebra_to整数ermediateField
  条件: (S : 子代数 K L) (inv_mem : 对任意 x in S, x⁻¹ in S)
  证明: by
  ext
  rfl

@[simp]
-/
theorem toSubalgebra_toIntermediateField (S : Subalgebra K L) (inv_mem : forall x in S, x⁻¹ in S) :
    (S.toIntermediateField inv_mem).toSubalgebra = S := by
  ext
  rfl

@[simp]
/--
theorem `toIntermediateField_toSubalgebra` / 定理 `toIntermediateField_toSubalgebra`

English:
theorem toIntermediateField_toSubalgebra
  given: (S : IntermediateField K L)
  proof: by
  ext
  rfl

中文:
定理 to整数ermediateField_toSubalgebra
  条件: (S : 中间域 K L)
  证明: by
  ext
  rfl
-/
theorem toIntermediateField_toSubalgebra (S : IntermediateField K L) :
    (S.toSubalgebra.toIntermediateField fun _ => S.inv_mem) = S := by
  ext
  rfl

/--
Definition of `Subalgebra.toIntermediateField'` / `Subalgebra.toIntermediateField'` 的定义

English:
definition Subalgebra.toIntermediateField'
  signature: (S : Subalgebra K L) (hS : IsField S)
  body: S.toIntermediateField fun x hx => by
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]
      exact S.zero_mem
    let hS' := hS.toField
    obtain ⟨y, hy⟩ := hS.mul_inv_cancel (show (⟨x, hx⟩ : S) != 0 from Subtype.coe_ne_coe.1 hx0)
    rw [Subtype.ext_iff]; rw [S.coe_mul]; rw [S.coe_one]; rw [Subtyp

中文:
定义 子代数.to整数ermediateField'
  签名: (S : 子代数 K L) (hS : 是域 S)
  定义体: S.toIntermediateField fun x hx => by
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]
      exact S.zero_mem
    let hS' := hS.toField
    obtain ⟨y, hy⟩ := hS.mul_inv_cancel (show (⟨x, hx⟩ : S) != 0 from Subtype.coe_ne_coe.1 hx0)
    rw [Subtype.ext_iff]; rw [S.coe_mul]; rw [S.coe_one]; rw [Subtyp

Depends on / 依赖: S.coe_mul, S.coe_one, S.toIntermediateField, S.zero_mem, Subtype, Subtype.coe_mk, Subtype.coe_ne_coe, Subtype.ext_iff, coe_mk, coe_mul, coe_ne_coe, coe_one, ext_iff, hS.mul_inv_cancel, hS.toField, hy.symm, inv_zero, mul_inv_cancel, toField, toIntermediateField
-/
def Subalgebra.toIntermediateField' (S : Subalgebra K L) (hS : IsField S) : IntermediateField K L :=
  S.toIntermediateField fun x hx => by
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]
      exact S.zero_mem
    let hS' := hS.toField
    obtain ⟨y, hy⟩ := hS.mul_inv_cancel (show (⟨x, hx⟩ : S) != 0 from Subtype.coe_ne_coe.1 hx0)
    rw [Subtype.ext_iff]; rw [S.coe_mul]; rw [S.coe_one]; rw [Subtype.coe_mk]; rw [mul_eq_one_iff_inv_eq₀ hx0] at hy
    exact hy.symm ▸ y.2

@[simp]
/--
theorem `toSubalgebra_toIntermediateField'` / 定理 `toSubalgebra_toIntermediateField'`

English:
theorem toSubalgebra_toIntermediateField'
  given: (S : Subalgebra K L) (hS : IsField S)
  proof: by
  ext
  rfl

@[simp]

中文:
定理 toSubalgebra_to整数ermediateField'
  条件: (S : 子代数 K L) (hS : 是域 S)
  证明: by
  ext
  rfl

@[simp]
-/
theorem toSubalgebra_toIntermediateField' (S : Subalgebra K L) (hS : IsField S) :
    (S.toIntermediateField' hS).toSubalgebra = S := by
  ext
  rfl

@[simp]
/--
theorem `toIntermediateField'_toSubalgebra` / 定理 `toIntermediateField'_toSubalgebra`

English:
theorem toIntermediateField'_toSubalgebra
  given: (S : IntermediateField K L)
  proof: by
  ext
  rfl

中文:
定理 to整数ermediateField'_toSubalgebra
  条件: (S : 中间域 K L)
  证明: by
  ext
  rfl
-/
theorem toIntermediateField'_toSubalgebra (S : IntermediateField K L) :
    S.toSubalgebra.toIntermediateField' (Field.toIsField S) = S := by
  ext
  rfl

/--
Definition of `Subfield.toIntermediateField` / `Subfield.toIntermediateField` 的定义

English:
definition Subfield.toIntermediateField
  signature: (S : Subfield L) (algebra_map_mem : forall x, algebraMap K L x in S)
  body: { S with
    algebraMap_mem' := algebra_map_mem }

@[simp]

中文:
定义 子域.to整数ermediateField
  签名: (S : 子域 L) (algebra_map_mem : 对任意 x, algebraMap K L x in S)
  定义体: { S with
    algebraMap_mem' := algebra_map_mem }

@[simp]

Depends on / 依赖: algebraMap_mem, algebra_map_mem
-/
def Subfield.toIntermediateField (S : Subfield L) (algebra_map_mem : forall x, algebraMap K L x in S) :
    IntermediateField K L :=
  { S with
    algebraMap_mem' := algebra_map_mem }

@[simp]
/--
theorem `Subfield.toIntermediateField_toSubfield` / 定理 `Subfield.toIntermediateField_toSubfield`

English:
theorem Subfield.toIntermediateField_toSubfield
  statement: (S : Subfield L)
  proof: rfl

@[simp]

中文:
定理 子域.to整数ermediateField_toSubfield
  结论: (S : 子域 L)
  证明: rfl

@[simp]
-/
theorem Subfield.toIntermediateField_toSubfield (S : Subfield L)
    (algebra_map_mem : forall x, (algebraMap K L) x in S) :
    (S.toIntermediateField algebra_map_mem).toSubfield = S := rfl

@[simp]
/--
theorem `Subfield.coe_toIntermediateField` / 定理 `Subfield.coe_toIntermediateField`

English:
theorem Subfield.coe_toIntermediateField
  statement: (S : Subfield L)
  proof: rfl

中文:
定理 子域.coe_to整数ermediateField
  结论: (S : 子域 L)
  证明: rfl
-/
theorem Subfield.coe_toIntermediateField (S : Subfield L)
    (algebra_map_mem : forall x, (algebraMap K L) x in S) :
    ((S.toIntermediateField algebra_map_mem) : Set L) = S := rfl

namespace IntermediateField

/--
Instance `toField` / 实例 `toField`

English:
instance toField
  signature: : Field S
  body: S.toSubfield.toField

@[norm_cast]

中文:
实例 toField
  签名: : 域 S
  定义体: S.toSubfield.toField

@[norm_cast]

Depends on / 依赖: S.toSubfield.toField, toField, toSubfield
-/
instance toField : Field S :=
  S.toSubfield.toField

@[norm_cast]
/--
theorem `coe_sum` / 定理 `coe_sum`

English:
theorem coe_sum
  given: {ι : Type*} [Fintype ι] (f : ι -> S)
  statement: (↑(∑ i, f i) : L) = ∑ i, (f i : L)
  proof: AddSubmonoidClass.coe_finsetSum f Finset.univ

@[norm_cast]

中文:
定理 coe_sum
  条件: {ι : 类型} [有限类型 ι] (f : ι -> S)
  结论: (↑(∑ i, f i) : L) = ∑ i, (f i : L)
  证明: AddSubmonoidClass.coe_finsetSum f Finset.univ

@[norm_cast]

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.coe_finsetSum, Finset, Finset.univ, coe_finsetSum
-/
theorem coe_sum {ι : Type*} [Fintype ι] (f : ι -> S) : (↑(∑ i, f i) : L) = ∑ i, (f i : L) :=
  AddSubmonoidClass.coe_finsetSum f Finset.univ

@[norm_cast]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: {ι : Type*} [Fintype ι] (f : ι -> S)
  statement: (↑(∏ i, f i) : L) = ∏ i, (f i : L)
  proof: SubmonoidClass.coe_finsetProd f Finset.univ

中文:
定理 coe_prod
  条件: {ι : 类型} [有限类型 ι] (f : ι -> S)
  结论: (↑(∏ i, f i) : L) = ∏ i, (f i : L)
  证明: SubmonoidClass.coe_finsetProd f Finset.univ

Depends on / 依赖: Finset, Finset.univ, SubmonoidClass, SubmonoidClass.coe_finsetProd, coe_finsetProd
-/
theorem coe_prod {ι : Type*} [Fintype ι] (f : ι -> S) : (↑(∏ i, f i) : L) = ∏ i, (f i : L) :=
  SubmonoidClass.coe_finsetProd f Finset.univ

/-!
`IntermediateField`s inherit structure from their `Subfield` coercions.
-/

variable {X Y}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: L X] (F
  body: inferInstanceAs (SMul F.toSubfield X)

中文:
实例 [标量乘法
  签名: L X] (F
  定义体: inferInstanceAs (SMul F.toSubfield X)

Depends on / 依赖: F.toSubfield, toSubfield
-/
instance [SMul L X] (F : IntermediateField K L) : SMul F X :=
  inferInstanceAs (SMul F.toSubfield X)

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: [SMul L X] {F : IntermediateField K L} (g : F) (m : X)
  statement: g • m = (g : L) • m
  proof: rfl

中文:
定理 smul_def
  条件: [标量乘法 L X] {F : 中间域 K L} (g : F) (m : X)
  结论: g • m = (g : L) • m
  证明: rfl
-/
theorem smul_def [SMul L X] {F : IntermediateField K L} (g : F) (m : X) : g • m = (g : L) • m :=
  rfl

/--
Instance `smulCommClass_left` / 实例 `smulCommClass_left`

English:
instance smulCommClass_left
  signature: [SMul L Y] [SMul X Y] [SMulCommClass L X Y]
  body: inferInstanceAs (SMulCommClass F.toSubfield X Y)

中文:
实例 smulCommClass_left
  签名: [标量乘法 L Y] [标量乘法 X Y] [标量交换类 L X Y]
  定义体: inferInstanceAs (SMulCommClass F.toSubfield X Y)

Depends on / 依赖: F.toSubfield, SMulCommClass, toSubfield
-/
instance smulCommClass_left [SMul L Y] [SMul X Y] [SMulCommClass L X Y]
    (F : IntermediateField K L) : SMulCommClass F X Y :=
  inferInstanceAs (SMulCommClass F.toSubfield X Y)

/--
Instance `smulCommClass_right` / 实例 `smulCommClass_right`

English:
instance smulCommClass_right
  signature: [SMul X Y] [SMul L Y] [SMulCommClass X L Y]
  body: inferInstanceAs (SMulCommClass X F.toSubfield Y)

中文:
实例 smulCommClass_right
  签名: [标量乘法 X Y] [标量乘法 L Y] [标量交换类 X L Y]
  定义体: inferInstanceAs (SMulCommClass X F.toSubfield Y)

Depends on / 依赖: F.toSubfield, SMulCommClass, toSubfield
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
instance (priority := 900) [SMul X Y] [SMul L X] [SMul L Y] [IsScalarTower L X Y]
    (F : IntermediateField K L) : IsScalarTower F X Y :=
  inferInstanceAs (IsScalarTower F.toSubfield X Y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: L X] [FaithfulSMul L X] (F
  body: inferInstanceAs (FaithfulSMul F.toSubfield X)

中文:
实例 [标量乘法
  签名: L X] [忠实标量乘法 L X] (F
  定义体: inferInstanceAs (FaithfulSMul F.toSubfield X)

Depends on / 依赖: F.toSubfield, FaithfulSMul, toSubfield
-/
instance [SMul L X] [FaithfulSMul L X] (F : IntermediateField K L) : FaithfulSMul F X :=
  inferInstanceAs (FaithfulSMul F.toSubfield X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulAction
  signature: L X] (F
  body: inferInstanceAs (MulAction F.toSubfield X)

中文:
实例 [乘法作用
  签名: L X] (F
  定义体: inferInstanceAs (MulAction F.toSubfield X)

Depends on / 依赖: F.toSubfield, MulAction, toSubfield
-/
instance [MulAction L X] (F : IntermediateField K L) : MulAction F X :=
  inferInstanceAs (MulAction F.toSubfield X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: X] [DistribMulAction L X] (F
  body: inferInstanceAs (DistribMulAction F.toSubfield X)

中文:
实例 [加法幺半群
  签名: X] [分配乘法作用 L X] (F
  定义体: inferInstanceAs (DistribMulAction F.toSubfield X)

Depends on / 依赖: DistribMulAction, F.toSubfield, toSubfield
-/
instance [AddMonoid X] [DistribMulAction L X] (F : IntermediateField K L) : DistribMulAction F X :=
  inferInstanceAs (DistribMulAction F.toSubfield X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: X] [MulDistribMulAction L X] (F
  body: inferInstanceAs (MulDistribMulAction F.toSubfield X)

中文:
实例 [幺半群
  签名: X] [MulDistribMul作用 L X] (F
  定义体: inferInstanceAs (MulDistribMulAction F.toSubfield X)

Depends on / 依赖: F.toSubfield, MulDistribMulAction, toSubfield
-/
instance [Monoid X] [MulDistribMulAction L X] (F : IntermediateField K L) :
    MulDistribMulAction F X :=
  inferInstanceAs (MulDistribMulAction F.toSubfield X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: X] [SMulWithZero L X] (F
  body: inferInstanceAs (SMulWithZero F.toSubfield X)

中文:
实例 [零
  签名: X] [带零标量乘法 L X] (F
  定义体: inferInstanceAs (SMulWithZero F.toSubfield X)

Depends on / 依赖: F.toSubfield, SMulWithZero, toSubfield
-/
instance [Zero X] [SMulWithZero L X] (F : IntermediateField K L) : SMulWithZero F X :=
  inferInstanceAs (SMulWithZero F.toSubfield X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: X] [MulActionWithZero L X] (F
  body: inferInstanceAs (MulActionWithZero F.toSubfield X)

中文:
实例 [零
  签名: X] [带零乘法作用 L X] (F
  定义体: inferInstanceAs (MulActionWithZero F.toSubfield X)

Depends on / 依赖: F.toSubfield, MulActionWithZero, toSubfield
-/
instance [Zero X] [MulActionWithZero L X] (F : IntermediateField K L) : MulActionWithZero F X :=
  inferInstanceAs (MulActionWithZero F.toSubfield X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: X] [Module L X] (F
  body: inferInstanceAs (Module F.toSubfield X)

中文:
实例 [加法交换幺半群
  签名: X] [模 L X] (F
  定义体: inferInstanceAs (Module F.toSubfield X)

Depends on / 依赖: F.toSubfield, Module, toSubfield
-/
instance [AddCommMonoid X] [Module L X] (F : IntermediateField K L) : Module F X :=
  inferInstanceAs (Module F.toSubfield X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: X] [MulSemiringAction L X] (F
  body: inferInstanceAs (MulSemiringAction F.toSubfield X)

中文:
实例 [半环
  签名: X] [MulSemiring作用 L X] (F
  定义体: inferInstanceAs (MulSemiringAction F.toSubfield X)

Depends on / 依赖: F.toSubfield, MulSemiringAction, toSubfield
-/
instance [Semiring X] [MulSemiringAction L X] (F : IntermediateField K L) : MulSemiringAction F X :=
  inferInstanceAs (MulSemiringAction F.toSubfield X)


/--
Instance `toAlgebra` / 实例 `toAlgebra`

English:
instance toAlgebra
  signature: : Algebra S L
  body: inferInstanceAs (Algebra S.toSubalgebra L)

中文:
实例 toAlgebra
  签名: : 代数 S L
  定义体: inferInstanceAs (Algebra S.toSubalgebra L)

Depends on / 依赖: Algebra, S.toSubalgebra, toSubalgebra
-/
instance toAlgebra : Algebra S L :=
  inferInstanceAs (Algebra S.toSubalgebra L)

/--
Instance `module'` / 实例 `module'`

English:
instance module'
  signature: {R} [Semiring R] [SMul R K] [Module R L] [IsScalarTower R K L]
  body: inferInstanceAs (Module R S.toSubalgebra)

中文:
实例 module'
  签名: {R} [半环 R] [标量乘法 R K] [模 R L] [标量塔 R K L]
  定义体: inferInstanceAs (Module R S.toSubalgebra)

Depends on / 依赖: Module, S.toSubalgebra, toSubalgebra
-/
instance module' {R} [Semiring R] [SMul R K] [Module R L] [IsScalarTower R K L] : Module R S :=
  inferInstanceAs (Module R S.toSubalgebra)

/--
Instance `algebra'` / 实例 `algebra'`

English:
instance algebra'
  signature: {R' K L : Type*} [Field K] [Field L] [Algebra K L] (S : IntermediateField K L)
  body: inferInstanceAs (Algebra R' S.toSubalgebra)

中文:
实例 algebra'
  签名: {R' K L : 类型} [域 K] [域 L] [代数 K L] (S : 中间域 K L)
  定义体: inferInstanceAs (Algebra R' S.toSubalgebra)

Depends on / 依赖: Algebra, S.toSubalgebra, toSubalgebra
-/
instance algebra' {R' K L : Type*} [Field K] [Field L] [Algebra K L] (S : IntermediateField K L)
    [CommSemiring R'] [SMul R' K] [Algebra R' L] [IsScalarTower R' K L] : Algebra R' S :=
  inferInstanceAs (Algebra R' S.toSubalgebra)

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: {R} [Semiring R] [SMul R K] [Module R L] [IsScalarTower R K L]
  body: inferInstanceAs (IsScalarTower R K S.toSubalgebra)

@[simp]

中文:
实例 isScalarTower
  签名: {R} [半环 R] [标量乘法 R K] [模 R L] [标量塔 R K L]
  定义体: inferInstanceAs (IsScalarTower R K S.toSubalgebra)

@[simp]

Depends on / 依赖: IsScalarTower, S.toSubalgebra, toSubalgebra
-/
instance isScalarTower {R} [Semiring R] [SMul R K] [Module R L] [IsScalarTower R K L] :
    IsScalarTower R K S :=
  inferInstanceAs (IsScalarTower R K S.toSubalgebra)

@[simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: {R} [SMul R K] [SMul R L] [IsScalarTower R K L] (r : R) (x : S)
  proof: rfl

中文:
定理 coe_smul
  条件: {R} [标量乘法 R K] [标量乘法 R L] [标量塔 R K L] (r : R) (x : S)
  证明: rfl
-/
theorem coe_smul {R} [SMul R K] [SMul R L] [IsScalarTower R K L] (r : R) (x : S) :
    ↑(r • x : S) = (r • (x : L)) :=
  rfl

/--
lemma `algebraMap_apply` / 引理 `algebraMap_apply`

English:
lemma algebraMap_apply
  given: (x : S)
  statement: algebraMap S L x = x
  proof: rfl

中文:
引理 algebraMap_apply
  条件: (x : S)
  结论: algebraMap S L x = x
  证明: rfl
-/
@[simp] lemma algebraMap_apply (x : S) : algebraMap S L x = x := rfl

/--
lemma `coe_algebraMap_apply` / 引理 `coe_algebraMap_apply`

English:
lemma coe_algebraMap_apply
  given: (x : K)
  statement: ↑(algebraMap K S x) = algebraMap K L x
  proof: rfl

中文:
引理 coe_algebraMap_apply
  条件: (x : K)
  结论: ↑(algebraMap K S x) = algebraMap K L x
  证明: rfl
-/
@[simp] lemma coe_algebraMap_apply (x : K) : ↑(algebraMap K S x) = algebraMap K L x := rfl

/--
Instance `isScalarTower_bot` / 实例 `isScalarTower_bot`

English:
instance isScalarTower_bot
  signature: {R : Type*} [Semiring R] [Algebra L R]
  body: IsScalarTower.subalgebra _ _ _ S.toSubalgebra

中文:
实例 isScalarTower_bot
  签名: {R : 类型} [半环 R] [代数 L R]
  定义体: IsScalarTower.subalgebra _ _ _ S.toSubalgebra

Depends on / 依赖: IsScalarTower, IsScalarTower.subalgebra, S.toSubalgebra, subalgebra, toSubalgebra
-/
instance isScalarTower_bot {R : Type*} [Semiring R] [Algebra L R] : IsScalarTower S L R :=
  IsScalarTower.subalgebra _ _ _ S.toSubalgebra

/--
Instance `isScalarTower_mid` / 实例 `isScalarTower_mid`

English:
instance isScalarTower_mid
  signature: {R : Type*} [Semiring R] [Algebra L R] [Algebra K R]
  body: IsScalarTower.subalgebra' _ _ _ S.toSubalgebra

中文:
实例 isScalarTower_mid
  签名: {R : 类型} [半环 R] [代数 L R] [代数 K R]
  定义体: IsScalarTower.subalgebra' _ _ _ S.toSubalgebra

Depends on / 依赖: IsScalarTower, IsScalarTower.subalgebra, S.toSubalgebra, subalgebra, toSubalgebra
-/
instance isScalarTower_mid {R : Type*} [Semiring R] [Algebra L R] [Algebra K R]
    [IsScalarTower K L R] : IsScalarTower K S R :=
  IsScalarTower.subalgebra' _ _ _ S.toSubalgebra

/--
Instance `isScalarTower_mid'` / 实例 `isScalarTower_mid'`

English:
instance isScalarTower_mid'
  signature: : IsScalarTower K S L
  body: inferInstance

中文:
实例 isScalarTower_mid'
  签名: : 标量塔 K S L
  定义体: inferInstance
-/
instance isScalarTower_mid' : IsScalarTower K S L :=
  inferInstance

instance {E} [Semiring E] [Algebra L E] : Algebra S E := inferInstanceAs (Algebra S.toSubalgebra E)

section shortcut_instances

variable {E} [Field E] [Algebra L E] (T : IntermediateField S E) {S}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra S T
  body: T.algebra

中文:
实例 :
  签名: 代数 S T
  定义体: T.algebra

Depends on / 依赖: T.algebra, algebra
-/
instance : Algebra S T := T.algebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module S T
  body: Algebra.toModule

中文:
实例 :
  签名: 模 S T
  定义体: Algebra.toModule

Depends on / 依赖: Algebra, Algebra.toModule, toModule
-/
instance : Module S T := Algebra.toModule

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul S T
  body: Algebra.toSMul

中文:
实例 :
  签名: 标量乘法 S T
  定义体: Algebra.toSMul

Depends on / 依赖: Algebra, Algebra.toSMul, toSMul
-/
instance : SMul S T := Algebra.toSMul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra
  signature: K E] [IsScalarTower K L E] : IsScalarTower K S T
  body: T.isScalarTower

中文:
实例 [代数
  签名: K E] [标量塔 K L E] : 标量塔 K S T
  定义体: T.isScalarTower

Depends on / 依赖: T.isScalarTower, isScalarTower
-/
instance [Algebra K E] [IsScalarTower K L E] : IsScalarTower K S T := T.isScalarTower

end shortcut_instances

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : L ->ₐ[K] L') (S : IntermediateField K L')
  body: S.toSubalgebra.comap f
  inv_mem' x hx := show f x⁻¹ in S by rw [map_inv₀ f x]; exact S.inv_mem hx

中文:
定义 comap
  签名: (f : L ->ₐ[K] L') (S : 中间域 K L')
  定义体: S.toSubalgebra.comap f
  inv_mem' x hx := show f x⁻¹ in S by rw [map_inv₀ f x]; exact S.inv_mem hx

Depends on / 依赖: S.toSubalgebra.comap, toSubalgebra
-/
def comap (f : L ->ₐ[K] L') (S : IntermediateField K L') : IntermediateField K L where
  __ := S.toSubalgebra.comap f
  inv_mem' x hx := show f x⁻¹ in S by rw [map_inv₀ f x]; exact S.inv_mem hx

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : L ->ₐ[K] L') (S : IntermediateField K L)
  body: S.toSubalgebra.map f
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, S.inv_mem hx, map_inv₀ f x⟩

@[simp]

中文:
定义 map
  签名: (f : L ->ₐ[K] L') (S : 中间域 K L)
  定义体: S.toSubalgebra.map f
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, S.inv_mem hx, map_inv₀ f x⟩

@[simp]

Depends on / 依赖: S.toSubalgebra.map, toSubalgebra
-/
def map (f : L ->ₐ[K] L') (S : IntermediateField K L) : IntermediateField K L' where
  __ := S.toSubalgebra.map f
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, S.inv_mem hx, map_inv₀ f x⟩

@[simp]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (f : L ->ₐ[K] L')
  statement: (S.map f : Set L') = f '' S
  proof: rfl

@[simp]

中文:
定理 coe_map
  条件: (f : L ->ₐ[K] L')
  结论: (S.map f : 集合 L') = f '' S
  证明: rfl

@[simp]
-/
theorem coe_map (f : L ->ₐ[K] L') : (S.map f : Set L') = f '' S :=
  rfl

@[simp]
/--
theorem `toSubalgebra_map` / 定理 `toSubalgebra_map`

English:
theorem toSubalgebra_map
  given: (f : L ->ₐ[K] L')
  statement: (S.map f).toSubalgebra = S.toSubalgebra.map f
  proof: rfl

@[simp]

中文:
定理 toSubalgebra_map
  条件: (f : L ->ₐ[K] L')
  结论: (S.map f).toSubalgebra = S.toSubalgebra.map f
  证明: rfl

@[simp]
-/
theorem toSubalgebra_map (f : L ->ₐ[K] L') : (S.map f).toSubalgebra = S.toSubalgebra.map f :=
  rfl

@[simp]
/--
theorem `toSubfield_map` / 定理 `toSubfield_map`

English:
theorem toSubfield_map
  given: (f : L ->ₐ[K] L')
  statement: (S.map f).toSubfield = S.toSubfield.map f
  proof: rfl

中文:
定理 toSubfield_map
  条件: (f : L ->ₐ[K] L')
  结论: (S.map f).toSubfield = S.toSubfield.map f
  证明: rfl
-/
theorem toSubfield_map (f : L ->ₐ[K] L') : (S.map f).toSubfield = S.toSubfield.map f :=
  rfl

/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: S.map (AlgHom.id K L) = S
  proof: SetLike.coe_injective Set.image_id _

@[simp]

中文:
定理 map_id
  结论: S.map (代数态射.id K L) = S
  证明: SetLike.coe_injective Set.image_id _

@[simp]

Depends on / 依赖: Set.image_id, SetLike, SetLike.coe_injective, coe_injective, image_id
-/
theorem map_id : S.map (AlgHom.id K L) = S :=
SetLike.coe_injective Set.image_id _

@[simp]
/--
lemma `mem_map` / 引理 `mem_map`

English:
lemma mem_map
  given: {f : L ->ₐ[K] L'} {y : L'}
  statement: y in S.map f ↔ exists x in S, f x = y
  proof: Set.mem_image f S y

中文:
引理 mem_map
  条件: {f : L ->ₐ[K] L'} {y : L'}
  结论: y in S.map f ↔ 存在 x in S, f x = y
  证明: Set.mem_image f S y

Depends on / 依赖: Set.mem_image, mem_image
-/
lemma mem_map {f : L ->ₐ[K] L'} {y : L'} : y in S.map f ↔ exists x in S, f x = y :=
  Set.mem_image f S y

-- Higher priority to apply before `mem_map`.
@[simp 1100]
/--
theorem `map_mem_map` / 定理 `map_mem_map`

English:
theorem map_mem_map
  given: (f : L ->ₐ[K] L') {x : L}
  proof: calc
    _ ↔ f x in (map f S : Set L') := Iff.rfl
    _ ↔ _ := by simp [Function.Injective.mem_set_image (f := f) f.injective]

中文:
定理 map_mem_map
  条件: (f : L ->ₐ[K] L') {x : L}
  证明: calc
    _ ↔ f x in (map f S : Set L') := Iff.rfl
    _ ↔ _ := by simp [Function.Injective.mem_set_image (f := f) f.injective]

Depends on / 依赖: Function, Function.Injective.mem_set_image, Iff.rfl, Injective, f.injective, injective, mem_set_image
-/
theorem map_mem_map (f : L ->ₐ[K] L') {x : L} :
    f x in map f S ↔ x in S :=
  calc
    _ ↔ f x in (map f S : Set L') := Iff.rfl
    _ ↔ _ := by simp [Function.Injective.mem_set_image (f := f) f.injective]

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  statement: {K L₁ L₂ L₃ : Type*} [Field K] [Field L₁] [Algebra K L₁] [Field L₂] [Algebra K L₂]
  proof: SetLike.coe_injective Set.image_image _ _ _

@[gcongr]

中文:
定理 map_map
  结论: {K L₁ L₂ L₃ : 类型} [域 K] [域 L₁] [代数 K L₁] [域 L₂] [代数 K L₂]
  证明: SetLike.coe_injective Set.image_image _ _ _

@[gcongr]

Depends on / 依赖: Set.image_image, SetLike, SetLike.coe_injective, coe_injective, image_image
-/
theorem map_map {K L₁ L₂ L₃ : Type*} [Field K] [Field L₁] [Algebra K L₁] [Field L₂] [Algebra K L₂]
    [Field L₃] [Algebra K L₃] (E : IntermediateField K L₁) (f : L₁ ->ₐ[K] L₂) (g : L₂ ->ₐ[K] L₃) :
    (E.map f).map g = E.map (g.comp f) :=
SetLike.coe_injective Set.image_image _ _ _

@[gcongr]
/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: (f : L ->ₐ[K] L') {S T : IntermediateField K L} (h : S <= T)
  proof: SetLike.coe_mono (Set.image_mono h)

中文:
定理 map_mono
  条件: (f : L ->ₐ[K] L') {S T : 中间域 K L} (h : S <= T)
  证明: SetLike.coe_mono (Set.image_mono h)

Depends on / 依赖: Set.image_mono, SetLike, SetLike.coe_mono, coe_mono, image_mono
-/
theorem map_mono (f : L ->ₐ[K] L') {S T : IntermediateField K L} (h : S <= T) :
    S.map f <= T.map f :=
  SetLike.coe_mono (Set.image_mono h)

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  statement: {f : L ->ₐ[K] L'}
  proof: Set.image_subset_iff

中文:
定理 map_le_iff_le_comap
  结论: {f : L ->ₐ[K] L'}
  证明: Set.image_subset_iff

Depends on / 依赖: Set.image_subset_iff, image_subset_iff
-/
theorem map_le_iff_le_comap {f : L ->ₐ[K] L'}
    {s : IntermediateField K L} {t : IntermediateField K L'} :
    s.map f <= t ↔ s <= t.comap f :=
  Set.image_subset_iff

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : L ->ₐ[K] L')
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ => map_le_iff_le_comap

中文:
定理 gc_map_comap
  条件: (f : L ->ₐ[K] L')
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ => map_le_iff_le_comap

Depends on / 依赖: map_le_iff_le_comap
-/
theorem gc_map_comap (f : L ->ₐ[K] L') : GaloisConnection (map f) (comap f) :=
  fun _ _ => map_le_iff_le_comap

/--
Definition of `intermediateFieldMap` / `intermediateFieldMap` 的定义

English:
definition intermediateFieldMap
  signature: (e : L ≃ₐ[K] L') (E : IntermediateField K L)
  body: e.subalgebraMap E.toSubalgebra

中文:
定义 intermediateFieldMap
  签名: (e : L ≃ₐ[K] L') (E : 中间域 K L)
  定义体: e.subalgebraMap E.toSubalgebra

Depends on / 依赖: E.toSubalgebra, e.subalgebraMap, subalgebraMap, toSubalgebra
-/
def intermediateFieldMap (e : L ≃ₐ[K] L') (E : IntermediateField K L) : E ≃ₐ[K] E.map e.toAlgHom :=
  e.subalgebraMap E.toSubalgebra

/--
theorem `intermediateFieldMap_apply_coe` / 定理 `intermediateFieldMap_apply_coe`

English:
theorem intermediateFieldMap_apply_coe
  given: (e : L ≃ₐ[K] L') (E : IntermediateField K L) (a : E)
  proof: rfl

中文:
定理 intermediateFieldMap_apply_coe
  条件: (e : L ≃ₐ[K] L') (E : 中间域 K L) (a : E)
  证明: rfl
-/
theorem intermediateFieldMap_apply_coe (e : L ≃ₐ[K] L') (E : IntermediateField K L) (a : E) :
    ↑(intermediateFieldMap e E a) = e a :=
  rfl

/--
theorem `intermediateFieldMap_symm_apply_coe` / 定理 `intermediateFieldMap_symm_apply_coe`

English:
theorem intermediateFieldMap_symm_apply_coe
  statement: (e : L ≃ₐ[K] L') (E : IntermediateField K L)
  proof: rfl

中文:
定理 intermediateFieldMap_symm_apply_coe
  结论: (e : L ≃ₐ[K] L') (E : 中间域 K L)
  证明: rfl
-/
theorem intermediateFieldMap_symm_apply_coe (e : L ≃ₐ[K] L') (E : IntermediateField K L)
    (a : E.map e.toAlgHom) : ↑((intermediateFieldMap e E).symm a) = e.symm a :=
  rfl

end IntermediateField

namespace AlgHom

variable (f : L ->ₐ[K] L')

/-- The range of an algebra homomorphism, as an intermediate field. -/
@[simps toSubalgebra]
/--
Definition of `fieldRange` / `fieldRange` 的定义

English:
definition fieldRange
  signature: : IntermediateField K L'
  body: { f.range, (f : L ->+* L').fieldRange with }

@[simp]

中文:
定义 fieldRange
  签名: : 中间域 K L'
  定义体: { f.range, (f : L ->+* L').fieldRange with }

@[simp]

Depends on / 依赖: f.range, fieldRange
-/
def fieldRange : IntermediateField K L' :=
  { f.range, (f : L ->+* L').fieldRange with }

@[simp]
/--
theorem `coe_fieldRange` / 定理 `coe_fieldRange`

English:
theorem coe_fieldRange
  statement: ↑f.fieldRange = Set.range f
  proof: rfl

@[simp]

中文:
定理 coe_fieldRange
  结论: ↑f.fieldRange = 集合.range f
  证明: rfl

@[simp]
-/
theorem coe_fieldRange : ↑f.fieldRange = Set.range f :=
  rfl

@[simp]
/--
theorem `fieldRange_toSubfield` / 定理 `fieldRange_toSubfield`

English:
theorem fieldRange_toSubfield
  statement: f.fieldRange.toSubfield = (f : L ->+* L').fieldRange
  proof: rfl

中文:
定理 fieldRange_toSubfield
  结论: f.fieldRange.toSubfield = (f : L ->+* L').fieldRange
  证明: rfl

Depends on / 依赖: nontrivial_of_three_le_card
-/
theorem fieldRange_toSubfield : f.fieldRange.toSubfield = (f : L ->+* L').fieldRange :=
  rfl

variable {f} in
@[simp]
/--
theorem `mem_fieldRange` / 定理 `mem_fieldRange`

English:
theorem mem_fieldRange
  given: {y : L'}
  statement: y in f.fieldRange ↔ exists x, f x = y
  proof: Iff.rfl

中文:
定理 mem_fieldRange
  条件: {y : L'}
  结论: y in f.fieldRange ↔ 存在 x, f x = y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_fieldRange {y : L'} : y in f.fieldRange ↔ exists x, f x = y :=
  Iff.rfl

/-- The isomorphism from `L` to the field range of the `AlgHom` `f`, sending `x` to `f x`. -/
@[simps! apply_coe]
/--
Definition of `equivFieldRange` / `equivFieldRange` 的定义

English:
definition equivFieldRange
  signature: : L ≃ₐ[K] f.fieldRange
  body: .ofBijective f.rangeRestrict ⟨f.rangeRestrict.injective, fun ⟨_, ⟨x, hx⟩⟩ => ⟨x, Subtype.ext hx⟩⟩

@[deprecated (since := "2026-06-20")] alias equivFieldRange_apply := equivFieldRange_apply_coe

中文:
定义 equivFieldRange
  签名: : L ≃ₐ[K] f.fieldRange
  定义体: .ofBijective f.rangeRestrict ⟨f.rangeRestrict.injective, fun ⟨_, ⟨x, hx⟩⟩ => ⟨x, Subtype.ext hx⟩⟩

@[deprecated (since := "2026-06-20")] alias equivFieldRange_apply := equivFieldRange_apply_coe

Depends on / 依赖: Subtype, Subtype.ext, f.rangeRestrict, f.rangeRestrict.injective, injective, ofBijective, rangeRestrict
-/
noncomputable def equivFieldRange : L ≃ₐ[K] f.fieldRange :=
  .ofBijective f.rangeRestrict ⟨f.rangeRestrict.injective, fun ⟨_, ⟨x, hx⟩⟩ => ⟨x, Subtype.ext hx⟩⟩

@[deprecated (since := "2026-06-20")] alias equivFieldRange_apply := equivFieldRange_apply_coe

end AlgHom

variable (K L L') in
@[simp]
/--
theorem `IsScalarTower.toAlgHom_fieldRange` / 定理 `IsScalarTower.toAlgHom_fieldRange`

English:
theorem IsScalarTower.toAlgHom_fieldRange
  given: [Algebra L L'] [IsScalarTower K L L']
  proof: by
  ext; simp

中文:
定理 标量塔.toAlgHom_fieldRange
  条件: [代数 L L'] [标量塔 K L L']
  证明: by
  ext; simp
-/
theorem IsScalarTower.toAlgHom_fieldRange [Algebra L L'] [IsScalarTower K L L'] :
    (IsScalarTower.toAlgHom K L L').fieldRange = Set.range (algebraMap L L') := by
  ext; simp

namespace IntermediateField

/--
Definition of `val` / `val` 的定义

English:
definition val
  signature: : S ->ₐ[K] L
  body: S.toSubalgebra.val

@[simp]

中文:
定义 val
  签名: : S ->ₐ[K] L
  定义体: S.toSubalgebra.val

@[simp]

Depends on / 依赖: S.toSubalgebra.val, toSubalgebra
-/
def val : S ->ₐ[K] L :=
  S.toSubalgebra.val

@[simp]
/--
theorem `coe_val` / 定理 `coe_val`

English:
theorem coe_val
  statement: ⇑S.val = ((↑) : S -> L)
  proof: rfl

@[simp]

中文:
定理 coe_val
  结论: ⇑S.val = ((↑) : S -> L)
  证明: rfl

@[simp]
-/
theorem coe_val : ⇑S.val = ((↑) : S -> L) :=
  rfl

@[simp]
/--
theorem `val_mk` / 定理 `val_mk`

English:
theorem val_mk
  given: {x : L} (hx : x in S)
  statement: S.val ⟨x, hx⟩ = x
  proof: rfl

中文:
定理 val_mk
  条件: {x : L} (hx : x in S)
  结论: S.val ⟨x, hx⟩ = x
  证明: rfl
-/
theorem val_mk {x : L} (hx : x in S) : S.val ⟨x, hx⟩ = x :=
  rfl

/--
theorem `range_val` / 定理 `range_val`

English:
theorem range_val
  statement: S.val.range = S.toSubalgebra
  proof: S.toSubalgebra.range_val

@[simp]

中文:
定理 range_val
  结论: S.val.range = S.toSubalgebra
  证明: S.toSubalgebra.range_val

@[simp]

Depends on / 依赖: S.toSubalgebra.range_val, range_val, toSubalgebra
-/
theorem range_val : S.val.range = S.toSubalgebra :=
  S.toSubalgebra.range_val

@[simp]
/--
theorem `fieldRange_val` / 定理 `fieldRange_val`

English:
theorem fieldRange_val
  statement: S.val.fieldRange = S
  proof: SetLike.ext' Subtype.range_val

中文:
定理 fieldRange_val
  结论: S.val.fieldRange = S
  证明: SetLike.ext' Subtype.range_val

Depends on / 依赖: SetLike, SetLike.ext, Subtype, Subtype.range_val, range_val
-/
theorem fieldRange_val : S.val.fieldRange = S :=
  SetLike.ext' Subtype.range_val

/--
Instance `AlgHom.inhabited` / 实例 `AlgHom.inhabited`

English:
instance AlgHom.inhabited
  signature: : Inhabited (S ->ₐ[K] L)
  body: ⟨S.val⟩

中文:
实例 代数态射.inhabited
  签名: : 可居 (S ->ₐ[K] L)
  定义体: ⟨S.val⟩

Depends on / 依赖: S.val
-/
instance AlgHom.inhabited : Inhabited (S ->ₐ[K] L) :=
  ⟨S.val⟩

/--
theorem `aeval_coe` / 定理 `aeval_coe`

English:
theorem aeval_coe
  statement: {R : Type*} [CommSemiring R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]
  proof: aeval_algHom_apply (S.val.restrictScalars R) x P

中文:
定理 aeval_coe
  结论: {R : 类型} [交换半环 R] [代数 R K] [代数 R L] [标量塔 R K L]
  证明: aeval_algHom_apply (S.val.restrictScalars R) x P

Depends on / 依赖: S.val.restrictScalars, aeval_algHom_apply, restrictScalars
-/
theorem aeval_coe {R : Type*} [CommSemiring R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]
    (x : S) (P : R[X]) : aeval (x : L) P = aeval x P :=
  aeval_algHom_apply (S.val.restrictScalars R) x P

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {E F : IntermediateField K L} (hEF : E <= F)
  body: Subalgebra.inclusion hEF

中文:
定义 inclusion
  签名: {E F : 中间域 K L} (hEF : E <= F)
  定义体: Subalgebra.inclusion hEF

Depends on / 依赖: Subalgebra, Subalgebra.inclusion, inclusion
-/
def inclusion {E F : IntermediateField K L} (hEF : E <= F) : E ->ₐ[K] F :=
  Subalgebra.inclusion hEF

/--
theorem `inclusion_injective` / 定理 `inclusion_injective`

English:
theorem inclusion_injective
  given: {E F : IntermediateField K L} (hEF : E <= F)
  proof: Subalgebra.inclusion_injective hEF

@[simp]

中文:
定理 inclusion_injective
  条件: {E F : 中间域 K L} (hEF : E <= F)
  证明: Subalgebra.inclusion_injective hEF

@[simp]

Depends on / 依赖: Subalgebra, Subalgebra.inclusion_injective, inclusion_injective
-/
theorem inclusion_injective {E F : IntermediateField K L} (hEF : E <= F) :
    Function.Injective (inclusion hEF) :=
  Subalgebra.inclusion_injective hEF

@[simp]
/--
theorem `inclusion_self` / 定理 `inclusion_self`

English:
theorem inclusion_self
  given: {E : IntermediateField K L}
  statement: inclusion (le_refl E) = AlgHom.id K E
  proof: Subalgebra.inclusion_self

@[simp]

中文:
定理 inclusion_self
  条件: {E : 中间域 K L}
  结论: inclusion (le_refl E) = 代数态射.id K E
  证明: Subalgebra.inclusion_self

@[simp]

Depends on / 依赖: Subalgebra, Subalgebra.inclusion_self, inclusion_self
-/
theorem inclusion_self {E : IntermediateField K L} : inclusion (le_refl E) = AlgHom.id K E :=
  Subalgebra.inclusion_self

@[simp]
/--
theorem `inclusion_inclusion` / 定理 `inclusion_inclusion`

English:
theorem inclusion_inclusion
  given: {E F G : IntermediateField K L} (hEF : E <= F) (hFG : F <= G) (x : E)
  proof: Subalgebra.inclusion_inclusion hEF hFG x

@[simp]

中文:
定理 inclusion_inclusion
  条件: {E F G : 中间域 K L} (hEF : E <= F) (hFG : F <= G) (x : E)
  证明: Subalgebra.inclusion_inclusion hEF hFG x

@[simp]

Depends on / 依赖: Subalgebra, Subalgebra.inclusion_inclusion, inclusion_inclusion
-/
theorem inclusion_inclusion {E F G : IntermediateField K L} (hEF : E <= F) (hFG : F <= G) (x : E) :
    inclusion hFG (inclusion hEF x) = inclusion (le_trans hEF hFG) x :=
  Subalgebra.inclusion_inclusion hEF hFG x

@[simp]
/--
theorem `coe_inclusion` / 定理 `coe_inclusion`

English:
theorem coe_inclusion
  given: {E F : IntermediateField K L} (hEF : E <= F) (e : E)
  proof: rfl

中文:
定理 coe_inclusion
  条件: {E F : 中间域 K L} (hEF : E <= F) (e : E)
  证明: rfl
-/
theorem coe_inclusion {E F : IntermediateField K L} (hEF : E <= F) (e : E) :
    (inclusion hEF e : L) = e :=
  rfl

variable {S}

/--
theorem `toSubalgebra_injective` / 定理 `toSubalgebra_injective`

English:
theorem toSubalgebra_injective
  statement: Function.Injective (toSubalgebra : IntermediateField K L -> _)
  proof: by
  intro _ _ h
  ext
  simp_rw [← mem_toSubalgebra, h]

中文:
定理 toSubalgebra_injective
  结论: 函数.单射 (toSubalgebra : 中间域 K L -> _)
  证明: by
  intro _ _ h
  ext
  simp_rw [← mem_toSubalgebra, h]

Depends on / 依赖: mem_toSubalgebra, simp_rw
-/
theorem toSubalgebra_injective : Function.Injective (toSubalgebra : IntermediateField K L -> _) := by
  intro _ _ h
  ext
  simp_rw [← mem_toSubalgebra, h]

/--
theorem `toSubfield_injective` / 定理 `toSubfield_injective`

English:
theorem toSubfield_injective
  statement: Function.Injective (toSubfield : IntermediateField K L -> _)
  proof: by
  intro _ _ h
  ext
  simp_rw [← mem_toSubfield, h]

中文:
定理 toSubfield_injective
  结论: 函数.单射 (toSubfield : 中间域 K L -> _)
  证明: by
  intro _ _ h
  ext
  simp_rw [← mem_toSubfield, h]

Depends on / 依赖: mem_toSubfield, simp_rw
-/
theorem toSubfield_injective : Function.Injective (toSubfield : IntermediateField K L -> _) := by
  intro _ _ h
  ext
  simp_rw [← mem_toSubfield, h]

variable {F E : IntermediateField K L}

@[simp]
/--
theorem `toSubalgebra_inj` / 定理 `toSubalgebra_inj`

English:
theorem toSubalgebra_inj
  statement: F.toSubalgebra = E.toSubalgebra ↔ F = E
  proof: toSubalgebra_injective.eq_iff

中文:
定理 toSubalgebra_inj
  结论: F.toSubalgebra = E.toSubalgebra ↔ F = E
  证明: toSubalgebra_injective.eq_iff

Depends on / 依赖: eq_iff, toSubalgebra_injective, toSubalgebra_injective.eq_iff
-/
theorem toSubalgebra_inj : F.toSubalgebra = E.toSubalgebra ↔ F = E := toSubalgebra_injective.eq_iff

/--
theorem `toSubfield_inj` / 定理 `toSubfield_inj`

English:
theorem toSubfield_inj
  statement: F.toSubfield = E.toSubfield ↔ F = E
  proof: toSubfield_injective.eq_iff

中文:
定理 toSubfield_inj
  结论: F.toSubfield = E.toSubfield ↔ F = E
  证明: toSubfield_injective.eq_iff

Depends on / 依赖: eq_iff, toSubfield_injective, toSubfield_injective.eq_iff
-/
theorem toSubfield_inj : F.toSubfield = E.toSubfield ↔ F = E := toSubfield_injective.eq_iff

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: (f : L ->ₐ[K] L')
  statement: Function.Injective (map f)
  proof: by
  intro _ _ h
  rwa [← toSubalgebra_injective.eq_iff, toSubalgebra_map, toSubalgebra_map,
    (Subalgebra.map_injective f.injective).eq_iff, toSubalgebra_inj] at h

中文:
定理 map_injective
  条件: (f : L ->ₐ[K] L')
  结论: 函数.单射 (map f)
  证明: by
  intro _ _ h
  rwa [← toSubalgebra_injective.eq_iff, toSubalgebra_map, toSubalgebra_map,
    (Subalgebra.map_injective f.injective).eq_iff, toSubalgebra_inj] at h

Depends on / 依赖: Subalgebra, Subalgebra.map_injective, eq_iff, f.injective, injective, map_injective, toSubalgebra_inj, toSubalgebra_injective, toSubalgebra_injective.eq_iff, toSubalgebra_map
-/
theorem map_injective (f : L ->ₐ[K] L') : Function.Injective (map f) := by
  intro _ _ h
  rwa [← toSubalgebra_injective.eq_iff, toSubalgebra_map, toSubalgebra_map,
    (Subalgebra.map_injective f.injective).eq_iff, toSubalgebra_inj] at h

variable (S)

/--
theorem `set_range_subset` / 定理 `set_range_subset`

English:
theorem set_range_subset
  statement: Set.range (algebraMap K L) subseteq S
  proof: S.toSubalgebra.range_subset

中文:
定理 set_range_subset
  结论: 集合.range (algebraMap K L) subseteq S
  证明: S.toSubalgebra.range_subset

Depends on / 依赖: S.toSubalgebra.range_subset, range_subset, toSubalgebra
-/
theorem set_range_subset : Set.range (algebraMap K L) subseteq S :=
  S.toSubalgebra.range_subset

/--
theorem `fieldRange_le` / 定理 `fieldRange_le`

English:
theorem fieldRange_le
  statement: (algebraMap K L).fieldRange <= S.toSubfield
  proof: fun x hx =>
  S.toSubalgebra.range_subset (by rwa [Set.mem_range, ← RingHom.mem_fieldRange])

@[simp]

中文:
定理 fieldRange_le
  结论: (algebraMap K L).fieldRange <= S.toSubfield
  证明: fun x hx =>
  S.toSubalgebra.range_subset (by rwa [Set.mem_range, ← RingHom.mem_fieldRange])

@[simp]
-/
theorem fieldRange_le : (algebraMap K L).fieldRange <= S.toSubfield := fun x hx =>
  S.toSubalgebra.range_subset (by rwa [Set.mem_range, ← RingHom.mem_fieldRange])

@[simp]
/--
theorem `toSubalgebra_le_toSubalgebra` / 定理 `toSubalgebra_le_toSubalgebra`

English:
theorem toSubalgebra_le_toSubalgebra
  given: {S S' : IntermediateField K L}
  proof: Iff.rfl

@[simp]

中文:
定理 toSubalgebra_le_toSubalgebra
  条件: {S S' : 中间域 K L}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem toSubalgebra_le_toSubalgebra {S S' : IntermediateField K L} :
    S.toSubalgebra <= S'.toSubalgebra ↔ S <= S' :=
  Iff.rfl

@[simp]
/--
theorem `toSubalgebra_lt_toSubalgebra` / 定理 `toSubalgebra_lt_toSubalgebra`

English:
theorem toSubalgebra_lt_toSubalgebra
  given: {S S' : IntermediateField K L}
  proof: Iff.rfl

中文:
定理 toSubalgebra_lt_toSubalgebra
  条件: {S S' : 中间域 K L}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toSubalgebra_lt_toSubalgebra {S S' : IntermediateField K L} :
    S.toSubalgebra < S'.toSubalgebra ↔ S < S' :=
  Iff.rfl

variable {S}

section Tower

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {F : IntermediateField K L} (E : IntermediateField K F)
  body: E.map (val F)

中文:
定义 lift
  签名: {F : 中间域 K L} (E : 中间域 K F)
  定义体: E.map (val F)

Depends on / 依赖: E.map, IsCyclic, Subgroup, Subgroup.eq_top_iff, Subgroup.zpowers, Subgroup.zpowers_ne_bot, eq_bot_or_eq_top, eq_top_iff, exists_ne, isCyclic, nontriviality, resolve_left, zpowers, zpowers_ne_bot
-/
def lift {F : IntermediateField K L} (E : IntermediateField K F) : IntermediateField K L :=
  E.map (val F)

/--
theorem `lift_injective` / 定理 `lift_injective`

English:
theorem lift_injective
  given: (F : IntermediateField K L)
  statement: Function.Injective F.lift
  proof: map_injective F.val

@[simp]

中文:
定理 lift_injective
  条件: (F : 中间域 K L)
  结论: 函数.单射 F.lift
  证明: map_injective F.val

@[simp]

Depends on / 依赖: F.val, map_injective
-/
theorem lift_injective (F : IntermediateField K L) : Function.Injective F.lift :=
  map_injective F.val

@[simp]
/--
theorem `lift_inj` / 定理 `lift_inj`

English:
theorem lift_inj
  given: {F : IntermediateField K L} (E E' : IntermediateField K F)
  proof: (lift_injective F).eq_iff

中文:
定理 lift_inj
  条件: {F : 中间域 K L} (E E' : 中间域 K F)
  证明: (lift_injective F).eq_iff

Depends on / 依赖: eq_iff, lift_injective
-/
theorem lift_inj {F : IntermediateField K L} (E E' : IntermediateField K F) :
    lift E = lift E' ↔ E = E' :=
  (lift_injective F).eq_iff

/--
theorem `lift_le` / 定理 `lift_le`

English:
theorem lift_le
  given: {F : IntermediateField K L} (E : IntermediateField K F)
  statement: lift E <= F
  proof: by
  rintro _ ⟨x, _, rfl⟩
  exact x.2

中文:
定理 lift_le
  条件: {F : 中间域 K L} (E : 中间域 K F)
  结论: lift E <= F
  证明: by
  rintro _ ⟨x, _, rfl⟩
  exact x.2
-/
theorem lift_le {F : IntermediateField K L} (E : IntermediateField K F) : lift E <= F := by
  rintro _ ⟨x, _, rfl⟩
  exact x.2

/--
theorem `mem_lift` / 定理 `mem_lift`

English:
theorem mem_lift
  given: {F : IntermediateField K L} {E : IntermediateField K F} (x : F)
  proof: Subtype.val_injective.mem_set_image

中文:
定理 mem_lift
  条件: {F : 中间域 K L} {E : 中间域 K F} (x : F)
  证明: Subtype.val_injective.mem_set_image

Depends on / 依赖: Subtype, Subtype.val_injective.mem_set_image, mem_set_image, val_injective
-/
theorem mem_lift {F : IntermediateField K L} {E : IntermediateField K F} (x : F) :
    x.1 in lift E ↔ x in E :=
  Subtype.val_injective.mem_set_image

/--
Definition of `liftAlgEquiv` / `liftAlgEquiv` 的定义

English:
definition liftAlgEquiv
  signature: {E : IntermediateField K L} (F : IntermediateField K E)
  body: ⟨x.1.1, (mem_lift x.1).mpr x.2⟩
  invFun x := ⟨⟨x.1, lift_le F x.2⟩, (mem_lift ⟨x.1, lift_le F x.2⟩).mp x.2⟩
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

中文:
定义 liftAlgEquiv
  签名: {E : 中间域 K L} (F : 中间域 K E)
  定义体: ⟨x.1.1, (mem_lift x.1).mpr x.2⟩
  invFun x := ⟨⟨x.1, lift_le F x.2⟩, (mem_lift ⟨x.1, lift_le F x.2⟩).mp x.2⟩
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

Depends on / 依赖: mem_lift
-/
def liftAlgEquiv {E : IntermediateField K L} (F : IntermediateField K E) : ↥F ≃ₐ[K] lift F where
  toFun x := ⟨x.1.1, (mem_lift x.1).mpr x.2⟩
  invFun x := ⟨⟨x.1, lift_le F x.2⟩, (mem_lift ⟨x.1, lift_le F x.2⟩).mp x.2⟩
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/--
lemma `liftAlgEquiv_apply` / 引理 `liftAlgEquiv_apply`

English:
lemma liftAlgEquiv_apply
  given: {E : IntermediateField K L} (F : IntermediateField K E) (x : F)
  proof: rfl

中文:
引理 liftAlgEquiv_apply
  条件: {E : 中间域 K L} (F : 中间域 K E) (x : F)
  证明: rfl
-/
lemma liftAlgEquiv_apply {E : IntermediateField K L} (F : IntermediateField K E) (x : F) :
    (liftAlgEquiv F x).1 = x := rfl

section RestrictScalars

variable (K)
variable [Algebra L' L] [IsScalarTower K L' L]

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (E : IntermediateField L' L)
  body: { E.toSubfield, E.toSubalgebra.restrictScalars K with
    carrier := E.carrier }

@[simp]

中文:
定义 restrictScalars
  签名: (E : 中间域 L' L)
  定义体: { E.toSubfield, E.toSubalgebra.restrictScalars K with
    carrier := E.carrier }

@[simp]

Depends on / 依赖: E.carrier, E.toSubalgebra.restrictScalars, E.toSubfield, carrier, restrictScalars, toSubalgebra, toSubfield
-/
def restrictScalars (E : IntermediateField L' L) : IntermediateField K L :=
  { E.toSubfield, E.toSubalgebra.restrictScalars K with
    carrier := E.carrier }

@[simp]
/--
theorem `coe_restrictScalars` / 定理 `coe_restrictScalars`

English:
theorem coe_restrictScalars
  given: {E : IntermediateField L' L}
  proof: rfl

@[simp]

中文:
定理 coe_restrictScalars
  条件: {E : 中间域 L' L}
  证明: rfl

@[simp]
-/
theorem coe_restrictScalars {E : IntermediateField L' L} :
    (restrictScalars K E : Set L) = (E : Set L) :=
  rfl

@[simp]
/--
theorem `restrictScalars_toSubalgebra` / 定理 `restrictScalars_toSubalgebra`

English:
theorem restrictScalars_toSubalgebra
  given: {E : IntermediateField L' L}
  proof: SetLike.coe_injective rfl

@[simp]

中文:
定理 restrictScalars_toSubalgebra
  条件: {E : 中间域 L' L}
  证明: SetLike.coe_injective rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem restrictScalars_toSubalgebra {E : IntermediateField L' L} :
    (E.restrictScalars K).toSubalgebra = E.toSubalgebra.restrictScalars K :=
  SetLike.coe_injective rfl

@[simp]
/--
theorem `restrictScalars_toSubfield` / 定理 `restrictScalars_toSubfield`

English:
theorem restrictScalars_toSubfield
  given: {E : IntermediateField L' L}
  proof: SetLike.coe_injective rfl

@[simp]

中文:
定理 restrictScalars_toSubfield
  条件: {E : 中间域 L' L}
  证明: SetLike.coe_injective rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem restrictScalars_toSubfield {E : IntermediateField L' L} :
    (E.restrictScalars K).toSubfield = E.toSubfield :=
  SetLike.coe_injective rfl

@[simp]
/--
theorem `mem_restrictScalars` / 定理 `mem_restrictScalars`

English:
theorem mem_restrictScalars
  given: {E : IntermediateField L' L} {x : L}
  proof: Iff.rfl

中文:
定理 mem_restrictScalars
  条件: {E : 中间域 L' L} {x : L}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_restrictScalars {E : IntermediateField L' L} {x : L} :
    x in restrictScalars K E ↔ x in E :=
  Iff.rfl

/--
theorem `restrictScalars_injective` / 定理 `restrictScalars_injective`

English:
theorem restrictScalars_injective
  proof: fun U V H => ext fun x => by rw [← mem_restrictScalars K, H, mem_restrictScalars]

@[simp]

中文:
定理 restrictScalars_injective
  证明: fun U V H => ext fun x => by rw [← mem_restrictScalars K, H, mem_restrictScalars]

@[simp]

Depends on / 依赖: mem_restrictScalars
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars K : IntermediateField L' L -> IntermediateField K L) :=
  fun U V H => ext fun x => by rw [← mem_restrictScalars K, H, mem_restrictScalars]

@[simp]
/--
theorem `restrictScalars_inj` / 定理 `restrictScalars_inj`

English:
theorem restrictScalars_inj
  given: {E E' : IntermediateField L' L}
  proof: (restrictScalars_injective K).eq_iff

中文:
定理 restrictScalars_inj
  条件: {E E' : 中间域 L' L}
  证明: (restrictScalars_injective K).eq_iff

Depends on / 依赖: eq_iff, restrictScalars_injective
-/
theorem restrictScalars_inj {E E' : IntermediateField L' L} :
    E.restrictScalars K = E'.restrictScalars K ↔ E = E' :=
  (restrictScalars_injective K).eq_iff

end RestrictScalars

/-- This was formerly an instance called `lift2_alg`, but an instance above already provides it. -/
example {F : IntermediateField K L} {E : IntermediateField F L} : Algebra K E := by infer_instance

end Tower

section equivMap

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
  {K : Type*} [Field K] [Algebra F K] (L : IntermediateField F E) (f : E ->ₐ[F] K)

/-- Construct an algebra isomorphism from an equality of intermediate fields. -/
@[simps! apply]
/--
Definition of `equivOfEq` / `equivOfEq` 的定义

English:
definition equivOfEq
  signature: {S T : IntermediateField F E} (h : S = T)
  body: Subalgebra.equivOfEq _ _ (congr_arg toSubalgebra h)

@[simp]

中文:
定义 equivOfEq
  签名: {S T : 中间域 F E} (h : S = T)
  定义体: Subalgebra.equivOfEq _ _ (congr_arg toSubalgebra h)

@[simp]

Depends on / 依赖: Subalgebra, Subalgebra.equivOfEq, congr_arg, equivOfEq, toSubalgebra
-/
def equivOfEq {S T : IntermediateField F E} (h : S = T) : S ≃ₐ[F] T :=
  Subalgebra.equivOfEq _ _ (congr_arg toSubalgebra h)

@[simp]
/--
theorem `equivOfEq_symm` / 定理 `equivOfEq_symm`

English:
theorem equivOfEq_symm
  given: {S T : IntermediateField F E} (h : S = T)
  proof: rfl

@[simp]

中文:
定理 equivOfEq_symm
  条件: {S T : 中间域 F E} (h : S = T)
  证明: rfl

@[simp]
-/
theorem equivOfEq_symm {S T : IntermediateField F E} (h : S = T) :
    (equivOfEq h).symm = equivOfEq h.symm :=
  rfl

@[simp]
/--
theorem `equivOfEq_rfl` / 定理 `equivOfEq_rfl`

English:
theorem equivOfEq_rfl
  given: (S : IntermediateField F E)
  statement: equivOfEq (rfl : S = S) = AlgEquiv.refl
  proof: AlgEquiv.ext fun _ => rfl

@[simp]

中文:
定理 equivOfEq_rfl
  条件: (S : 中间域 F E)
  结论: equivOfEq (rfl : S = S) = 代数等价.refl
  证明: AlgEquiv.ext fun _ => rfl

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ext
-/
theorem equivOfEq_rfl (S : IntermediateField F E) : equivOfEq (rfl : S = S) = AlgEquiv.refl :=
  AlgEquiv.ext fun _ => rfl

@[simp]
/--
theorem `equivOfEq_trans` / 定理 `equivOfEq_trans`

English:
theorem equivOfEq_trans
  given: {S T U : IntermediateField F E} (hST : S = T) (hTU : T = U)
  proof: rfl

中文:
定理 equivOfEq_trans
  条件: {S T U : 中间域 F E} (hST : S = T) (hTU : T = U)
  证明: rfl
-/
theorem equivOfEq_trans {S T U : IntermediateField F E} (hST : S = T) (hTU : T = U) :
    (equivOfEq hST).trans (equivOfEq hTU) = equivOfEq (hST.trans hTU) :=
  rfl

/--
theorem `fieldRange_comp_val` / 定理 `fieldRange_comp_val`

English:
theorem fieldRange_comp_val
  statement: (f.comp L.val).fieldRange = L.map f
  proof: toSubalgebra_injective by
  rw [toSubalgebra_map]; rw [AlgHom.fieldRange_toSubalgebra]; rw [AlgHom.range_comp]; rw [range_val]

中文:
定理 fieldRange_comp_val
  结论: (f.comp L.val).fieldRange = L.map f
  证明: toSubalgebra_injective by
  rw [toSubalgebra_map]; rw [AlgHom.fieldRange_toSubalgebra]; rw [AlgHom.range_comp]; rw [range_val]

Depends on / 依赖: AlgHom, AlgHom.fieldRange_toSubalgebra, AlgHom.range_comp, fieldRange_toSubalgebra, range_comp, range_val, toSubalgebra_injective, toSubalgebra_map
-/
theorem fieldRange_comp_val : (f.comp L.val).fieldRange = L.map f := toSubalgebra_injective by
  rw [toSubalgebra_map]; rw [AlgHom.fieldRange_toSubalgebra]; rw [AlgHom.range_comp]; rw [range_val]

/--
Definition of `equivMap` / `equivMap` 的定义

English:
definition equivMap
  signature: : L ≃ₐ[F] L.map f
  body: (AlgEquiv.ofInjective _ (f.comp L.val).injective).trans (equivOfEq (fieldRange_comp_val L f))

@[simp]

中文:
定义 equivMap
  签名: : L ≃ₐ[F] L.map f
  定义体: (AlgEquiv.ofInjective _ (f.comp L.val).injective).trans (equivOfEq (fieldRange_comp_val L f))

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjective, L.val, equivOfEq, f.comp, fieldRange_comp_val, injective, ofInjective
-/
noncomputable def equivMap : L ≃ₐ[F] L.map f :=
  (AlgEquiv.ofInjective _ (f.comp L.val).injective).trans (equivOfEq (fieldRange_comp_val L f))

@[simp]
/--
theorem `coe_equivMap_apply` / 定理 `coe_equivMap_apply`

English:
theorem coe_equivMap_apply
  given: (x : L)
  statement: ↑(equivMap L f x) = f x
  proof: rfl

中文:
定理 coe_equivMap_apply
  条件: (x : L)
  结论: ↑(equivMap L f x) = f x
  证明: rfl
-/
theorem coe_equivMap_apply (x : L) : ↑(equivMap L f x) = f x := rfl

end equivMap

end IntermediateField

section ExtendScalars

namespace Subfield

variable {F E E' : Subfield L} (h : F <= E) (h' : F <= E') {x : L}

/--
Definition of `extendScalars` / `extendScalars` 的定义

English:
definition extendScalars
  signature: : IntermediateField F L
  body: E.toIntermediateField fun ⟨_, hf⟩ => h hf

@[simp]

中文:
定义 extendScalars
  签名: : 中间域 F L
  定义体: E.toIntermediateField fun ⟨_, hf⟩ => h hf

@[simp]

Depends on / 依赖: E.toIntermediateField, toIntermediateField
-/
def extendScalars : IntermediateField F L := E.toIntermediateField fun ⟨_, hf⟩ => h hf

@[simp]
/--
theorem `coe_extendScalars` / 定理 `coe_extendScalars`

English:
theorem coe_extendScalars
  statement: (extendScalars h : Set L) = (E : Set L)
  proof: rfl

@[simp]

中文:
定理 coe_extendScalars
  结论: (extendScalars h : 集合 L) = (E : 集合 L)
  证明: rfl

@[simp]
-/
theorem coe_extendScalars : (extendScalars h : Set L) = (E : Set L) := rfl

@[simp]
/--
theorem `extendScalars_toSubfield` / 定理 `extendScalars_toSubfield`

English:
theorem extendScalars_toSubfield
  statement: (extendScalars h).toSubfield = E
  proof: SetLike.coe_injective rfl

@[simp]

中文:
定理 extendScalars_toSubfield
  结论: (extendScalars h).toSubfield = E
  证明: SetLike.coe_injective rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem extendScalars_toSubfield : (extendScalars h).toSubfield = E := SetLike.coe_injective rfl

@[simp]
/--
theorem `mem_extendScalars` / 定理 `mem_extendScalars`

English:
theorem mem_extendScalars
  statement: x in extendScalars h ↔ x in E
  proof: Iff.rfl

中文:
定理 mem_extendScalars
  结论: x in extendScalars h ↔ x in E
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_extendScalars : x in extendScalars h ↔ x in E := Iff.rfl

/--
theorem `extendScalars_le_extendScalars_iff` / 定理 `extendScalars_le_extendScalars_iff`

English:
theorem extendScalars_le_extendScalars_iff
  statement: extendScalars h <= extendScalars h' ↔ E <= E'
  proof: Iff.rfl

中文:
定理 extendScalars_le_extendScalars_iff
  结论: extendScalars h <= extendScalars h' ↔ E <= E'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem extendScalars_le_extendScalars_iff : extendScalars h <= extendScalars h' ↔ E <= E' := Iff.rfl

/--
theorem `extendScalars_le_iff` / 定理 `extendScalars_le_iff`

English:
theorem extendScalars_le_iff
  given: (E' : IntermediateField F L)
  proof: Iff.rfl

中文:
定理 extendScalars_le_iff
  条件: (E' : 中间域 F L)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem extendScalars_le_iff (E' : IntermediateField F L) :
    extendScalars h <= E' ↔ E <= E'.toSubfield := Iff.rfl

/--
theorem `le_extendScalars_iff` / 定理 `le_extendScalars_iff`

English:
theorem le_extendScalars_iff
  given: (E' : IntermediateField F L)
  proof: Iff.rfl

中文:
定理 le_extendScalars_iff
  条件: (E' : 中间域 F L)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_extendScalars_iff (E' : IntermediateField F L) :
    E' <= extendScalars h ↔ E'.toSubfield <= E := Iff.rfl

variable (F)

/-- `Subfield.extendScalars.orderIso` bundles `Subfield.extendScalars`
into an order isomorphism from
`{ E : Subfield L // F ≤ E }` to `IntermediateField F L`. Its inverse is
`IntermediateField.toSubfield`. -/
@[simps apply symm_apply]
/--
Definition of `extendScalars.orderIso` / `extendScalars.orderIso` 的定义

English:
definition extendScalars.orderIso
  signature: :
  body: extendScalars E.2
  invFun E := ⟨E.toSubfield, fun x hx => E.algebraMap_mem ⟨x, hx⟩⟩
  map_rel_iff' {E E'} := by
    simp only [Equiv.coe_fn_mk]
    exact extendScalars_le_extendScalars_iff _ _

中文:
定义 extendScalars.orderIso
  签名: :
  定义体: extendScalars E.2
  invFun E := ⟨E.toSubfield, fun x hx => E.algebraMap_mem ⟨x, hx⟩⟩
  map_rel_iff' {E E'} := by
    simp only [Equiv.coe_fn_mk]
    exact extendScalars_le_extendScalars_iff _ _

Depends on / 依赖: extendScalars
-/
def extendScalars.orderIso :
    { E : Subfield L // F <= E } ≃o IntermediateField F L where
  toFun E := extendScalars E.2
  invFun E := ⟨E.toSubfield, fun x hx => E.algebraMap_mem ⟨x, hx⟩⟩
  map_rel_iff' {E E'} := by
    simp only [Equiv.coe_fn_mk]
    exact extendScalars_le_extendScalars_iff _ _

/--
theorem `extendScalars_injective` / 定理 `extendScalars_injective`

English:
theorem extendScalars_injective
  proof: (extendScalars.orderIso F).injective

中文:
定理 extendScalars_injective
  证明: (extendScalars.orderIso F).injective

Depends on / 依赖: extendScalars, extendScalars.orderIso, injective, orderIso
-/
theorem extendScalars_injective :
    Function.Injective fun E : { E : Subfield L // F <= E } => extendScalars E.2 :=
  (extendScalars.orderIso F).injective

end Subfield

namespace IntermediateField

variable {F E E' : IntermediateField K L} (h : F <= E) (h' : F <= E') {x : L}

/--
Definition of `extendScalars` / `extendScalars` 的定义

English:
definition extendScalars
  signature: : IntermediateField F L
  body: Subfield.extendScalars (show F.toSubfield <= E.toSubfield from h)

@[simp]

中文:
定义 extendScalars
  签名: : 中间域 F L
  定义体: Subfield.extendScalars (show F.toSubfield <= E.toSubfield from h)

@[simp]

Depends on / 依赖: E.toSubfield, F.toSubfield, Subfield, Subfield.extendScalars, extendScalars, toSubfield
-/
def extendScalars : IntermediateField F L :=
  Subfield.extendScalars (show F.toSubfield <= E.toSubfield from h)

@[simp]
/--
theorem `coe_extendScalars` / 定理 `coe_extendScalars`

English:
theorem coe_extendScalars
  statement: (extendScalars h : Set L) = (E : Set L)
  proof: rfl

@[simp]

中文:
定理 coe_extendScalars
  结论: (extendScalars h : 集合 L) = (E : 集合 L)
  证明: rfl

@[simp]
-/
theorem coe_extendScalars : (extendScalars h : Set L) = (E : Set L) := rfl

@[simp]
/--
theorem `extendScalars_toSubfield` / 定理 `extendScalars_toSubfield`

English:
theorem extendScalars_toSubfield
  statement: (extendScalars h).toSubfield = E.toSubfield
  proof: SetLike.coe_injective rfl

@[simp]

中文:
定理 extendScalars_toSubfield
  结论: (extendScalars h).toSubfield = E.toSubfield
  证明: SetLike.coe_injective rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem extendScalars_toSubfield : (extendScalars h).toSubfield = E.toSubfield :=
  SetLike.coe_injective rfl

@[simp]
/--
theorem `mem_extendScalars` / 定理 `mem_extendScalars`

English:
theorem mem_extendScalars
  statement: x in extendScalars h ↔ x in E
  proof: Iff.rfl

@[simp]

中文:
定理 mem_extendScalars
  结论: x in extendScalars h ↔ x in E
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_extendScalars : x in extendScalars h ↔ x in E := Iff.rfl

@[simp]
/--
theorem `extendScalars_restrictScalars` / 定理 `extendScalars_restrictScalars`

English:
theorem extendScalars_restrictScalars
  statement: (extendScalars h).restrictScalars K = E
  proof: rfl

中文:
定理 extendScalars_restrictScalars
  结论: (extendScalars h).restrictScalars K = E
  证明: rfl
-/
theorem extendScalars_restrictScalars : (extendScalars h).restrictScalars K = E := rfl

/--
theorem `extendScalars_le_extendScalars_iff` / 定理 `extendScalars_le_extendScalars_iff`

English:
theorem extendScalars_le_extendScalars_iff
  statement: extendScalars h <= extendScalars h' ↔ E <= E'
  proof: Iff.rfl

中文:
定理 extendScalars_le_extendScalars_iff
  结论: extendScalars h <= extendScalars h' ↔ E <= E'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem extendScalars_le_extendScalars_iff : extendScalars h <= extendScalars h' ↔ E <= E' := Iff.rfl

/--
theorem `extendScalars_le_iff` / 定理 `extendScalars_le_iff`

English:
theorem extendScalars_le_iff
  given: (E' : IntermediateField F L)
  proof: Iff.rfl

中文:
定理 extendScalars_le_iff
  条件: (E' : 中间域 F L)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem extendScalars_le_iff (E' : IntermediateField F L) :
    extendScalars h <= E' ↔ E <= E'.restrictScalars K := Iff.rfl

/--
theorem `le_extendScalars_iff` / 定理 `le_extendScalars_iff`

English:
theorem le_extendScalars_iff
  given: (E' : IntermediateField F L)
  proof: Iff.rfl

中文:
定理 le_extendScalars_iff
  条件: (E' : 中间域 F L)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_extendScalars_iff (E' : IntermediateField F L) :
    E' <= extendScalars h ↔ E'.restrictScalars K <= E := Iff.rfl

variable (F)

/-- `IntermediateField.extendScalars.orderIso` bundles `IntermediateField.extendScalars`
into an order isomorphism from
`{ E : IntermediateField K L // F ≤ E }` to `IntermediateField F L`. Its inverse is
`IntermediateField.restrictScalars`. -/
@[simps]
/--
Definition of `extendScalars.orderIso` / `extendScalars.orderIso` 的定义

English:
definition extendScalars.orderIso
  signature: : { E : IntermediateField K L // F <= E } ≃o IntermediateField F L where
  body: extendScalars E.2
  invFun E := ⟨E.restrictScalars K, fun x hx => E.algebraMap_mem ⟨x, hx⟩⟩
  map_rel_iff' {E E'} := by
    simp only [Equiv.coe_fn_mk]
    exact extendScalars_le_extendScalars_iff _ _

中文:
定义 extendScalars.orderIso
  签名: : { E : 中间域 K L // F <= E } ≃o 中间域 F L where
  定义体: extendScalars E.2
  invFun E := ⟨E.restrictScalars K, fun x hx => E.algebraMap_mem ⟨x, hx⟩⟩
  map_rel_iff' {E E'} := by
    simp only [Equiv.coe_fn_mk]
    exact extendScalars_le_extendScalars_iff _ _
-/
def extendScalars.orderIso : { E : IntermediateField K L // F <= E } ≃o IntermediateField F L where
  toFun E := extendScalars E.2
  invFun E := ⟨E.restrictScalars K, fun x hx => E.algebraMap_mem ⟨x, hx⟩⟩
  map_rel_iff' {E E'} := by
    simp only [Equiv.coe_fn_mk]
    exact extendScalars_le_extendScalars_iff _ _

/--
theorem `extendScalars_injective` / 定理 `extendScalars_injective`

English:
theorem extendScalars_injective
  proof: (extendScalars.orderIso F).injective

中文:
定理 extendScalars_injective
  证明: (extendScalars.orderIso F).injective

Depends on / 依赖: extendScalars, extendScalars.orderIso, injective, orderIso
-/
theorem extendScalars_injective :
    Function.Injective fun E : { E : IntermediateField K L // F <= E } => extendScalars E.2 :=
  (extendScalars.orderIso F).injective

end IntermediateField

end ExtendScalars

namespace IntermediateField

variable {S}

section Tower

section Restrict

variable {F E : IntermediateField K L} (h : F <= E)

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: : IntermediateField K E
  body: (IntermediateField.inclusion h).fieldRange

中文:
定义 restrict
  签名: : 中间域 K E
  定义体: (IntermediateField.inclusion h).fieldRange

Depends on / 依赖: IntermediateField, IntermediateField.inclusion, fieldRange, inclusion
-/
def restrict : IntermediateField K E :=
  (IntermediateField.inclusion h).fieldRange

/--
theorem `mem_restrict` / 定理 `mem_restrict`

English:
theorem mem_restrict
  given: (x : E)
  statement: x in restrict h ↔ x.1 in F
  proof: Set.ext_iff.mp (Set.range_inclusion h) x

@[simp]

中文:
定理 mem_restrict
  条件: (x : E)
  结论: x in restrict h ↔ x.1 in F
  证明: Set.ext_iff.mp (Set.range_inclusion h) x

@[simp]

Depends on / 依赖: Set.ext_iff.mp, Set.range_inclusion, ext_iff, range_inclusion
-/
theorem mem_restrict (x : E) : x in restrict h ↔ x.1 in F :=
  Set.ext_iff.mp (Set.range_inclusion h) x

@[simp]
/--
theorem `lift_restrict` / 定理 `lift_restrict`

English:
theorem lift_restrict
  statement: lift (restrict h) = F
  proof: by
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · let y : E := ⟨x, lift_le (restrict h) hx⟩
    exact (mem_restrict h y).1 ((mem_lift y).1 hx)
  · let y : E := ⟨x, h hx⟩
    exact (mem_lift y).2 ((mem_restrict h y).2 hx)

中文:
定理 lift_restrict
  结论: lift (restrict h) = F
  证明: by
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · let y : E := ⟨x, lift_le (restrict h) hx⟩
    exact (mem_restrict h y).1 ((mem_lift y).1 hx)
  · let y : E := ⟨x, h hx⟩
    exact (mem_lift y).2 ((mem_restrict h y).2 hx)

Depends on / 依赖: lift_le, mem_lift, mem_restrict, restrict
-/
theorem lift_restrict : lift (restrict h) = F := by
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · let y : E := ⟨x, lift_le (restrict h) hx⟩
    exact (mem_restrict h y).1 ((mem_lift y).1 hx)
  · let y : E := ⟨x, h hx⟩
    exact (mem_lift y).2 ((mem_restrict h y).2 hx)

/--
Definition of `restrictAlgEquiv` / `restrictAlgEquiv` 的定义

English:
definition restrictAlgEquiv
  signature: :
  body: AlgEquiv.ofInjectiveField _

@[deprecated (since := "2026-07-25")]
alias restrict_algEquiv := restrictAlgEquiv

中文:
定义 restrictAlgEquiv
  签名: :
  定义体: AlgEquiv.ofInjectiveField _

@[deprecated (since := "2026-07-25")]
alias restrict_algEquiv := restrictAlgEquiv

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, ofInjectiveField
-/
noncomputable def restrictAlgEquiv :
    F ≃ₐ[K] ↥(IntermediateField.restrict h) :=
  AlgEquiv.ofInjectiveField _

@[deprecated (since := "2026-07-25")]
alias restrict_algEquiv := restrictAlgEquiv

end Restrict

end Tower

end IntermediateField
