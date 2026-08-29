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

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (s : S)
  body: { NonUnitalSubsemiringClass.subtype s, SMulMemClass.subtype s with toFun := (↑) }

中文:
定义 subtype
  签名: (s : S)
  定义体: { NonUnitalSubsemiringClass.subtype s, SMulMemClass.subtype s with toFun := (↑) }

Depends on / 依赖: NonUnitalSubsemiringClass, NonUnitalSubsemiringClass.subtype, SMulMemClass, SMulMemClass.subtype, subtype
-/
def subtype (s : S) : s ->ₙₐ[R] A :=
  { NonUnitalSubsemiringClass.subtype s, SMulMemClass.subtype s with toFun := (↑) }

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
  statement: (subtype s : s -> A) = ((↑) : s -> A)
  proof: rfl

中文:
定理 coe_subtype
  结论: (subtype s : s -> A) = ((↑) : s -> A)
  证明: rfl
-/
theorem coe_subtype : (subtype s : s -> A) = ((↑) : s -> A) :=
  rfl

end NonUnitalSubalgebraClass

end NonUnitalSubalgebraClass

/--
Definition of `NonUnitalSubalgebra` / `NonUnitalSubalgebra` 的定义

English:
structure NonUnitalSubalgebra
  parameters: (R : Type u) (A : Type v) [CommSemiring R]
  extends: NonUnitalSubsemiring A, Submodule R A
  (no additional axioms)

中文:
结构 NonUnital子代数
  参数: (R : 类型u) (A : 类型v) [交换半环 R]
  继承: NonUnital子半环 A, 子模 R A
  (无附加公理)
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

/--
lemma `toNonUnitalSubsemiring_injective` / 引理 `toNonUnitalSubsemiring_injective`

English:
lemma toNonUnitalSubsemiring_injective
  proof: fun ⟨s, hs⟩ t => by congr!

中文:
引理 toNonUnitalSubsemiring_injective
  证明: fun ⟨s, hs⟩ t => by congr!
-/
lemma toNonUnitalSubsemiring_injective :
    (toNonUnitalSubsemiring : NonUnitalSubalgebra R A -> NonUnitalSubsemiring A).Injective :=
  fun ⟨s, hs⟩ t => by congr!

/--
lemma `toNonUnitalSubsemiring_inj` / 引理 `toNonUnitalSubsemiring_inj`

English:
lemma toNonUnitalSubsemiring_inj
  given: {s t : NonUnitalSubalgebra R A}
  proof: toNonUnitalSubsemiring_injective.eq_iff

中文:
引理 toNonUnitalSubsemiring_inj
  条件: {s t : NonUnital子代数 R A}
  证明: toNonUnitalSubsemiring_injective.eq_iff
-/
@[simp] lemma toNonUnitalSubsemiring_inj {s t : NonUnitalSubalgebra R A} :
    s.toNonUnitalSubsemiring = t.toNonUnitalSubsemiring ↔ s = t :=
  toNonUnitalSubsemiring_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (NonUnitalSubalgebra R A) A
  body: s.carrier
  coe_injective := SetLike.coe_injective.comp toNonUnitalSubsemiring_injective

中文:
实例 :
  签名: 集合状 (NonUnital子代数 R A) A
  定义体: s.carrier
  coe_injective := SetLike.coe_injective.comp toNonUnitalSubsemiring_injective

Depends on / 依赖: carrier, s.carrier
-/
instance : SetLike (NonUnitalSubalgebra R A) A where
  coe s := s.carrier
  coe_injective := SetLike.coe_injective.comp toNonUnitalSubsemiring_injective

/--
lemma `toSubmodule_injective` / 引理 `toSubmodule_injective`

English:
lemma toSubmodule_injective
  statement: (toSubmodule : NonUnitalSubalgebra R A -> Submodule R A).Injective
  proof: fun _ _ h => SetLike.ext (SetLike.ext_iff.mp h :)

中文:
引理 toSubmodule_injective
  结论: (toSubmodule : NonUnital子代数 R A -> 子模 R A).单射
  证明: fun _ _ h => SetLike.ext (SetLike.ext_iff.mp h :)

Depends on / 依赖: SetLike, SetLike.ext, SetLike.ext_iff.mp, ext_iff
-/
lemma toSubmodule_injective : (toSubmodule : NonUnitalSubalgebra R A -> Submodule R A).Injective :=
  fun _ _ h => SetLike.ext (SetLike.ext_iff.mp h :)

/--
lemma `toSubmodule_inj` / 引理 `toSubmodule_inj`

English:
lemma toSubmodule_inj
  given: {s t : NonUnitalSubalgebra R A}
  statement: s.toSubmodule = t.toSubmodule ↔ s = t
  proof: toSubmodule_injective.eq_iff

中文:
引理 toSubmodule_inj
  条件: {s t : NonUnital子代数 R A}
  结论: s.toSubmodule = t.toSubmodule ↔ s = t
  证明: toSubmodule_injective.eq_iff

Depends on / 依赖: eq_iff, toSubmodule_injective, toSubmodule_injective.eq_iff
-/
lemma toSubmodule_inj {s t : NonUnitalSubalgebra R A} : s.toSubmodule = t.toSubmodule ↔ s = t :=
  toSubmodule_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (NonUnitalSubalgebra R A)
  body: .ofSetLike (NonUnitalSubalgebra R A) A

中文:
实例 :
  签名: 偏序 (NonUnital子代数 R A)
  定义体: .ofSetLike (NonUnitalSubalgebra R A) A

Depends on / 依赖: NonUnitalSubalgebra, ofSetLike
-/
instance : PartialOrder (NonUnitalSubalgebra R A) := .ofSetLike (NonUnitalSubalgebra R A) A

/-- The actual `NonUnitalSubalgebra` obtained from an element of a type satisfying
`NonUnitalSubsemiringClass` and `SMulMemClass`. -/
@[simps]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: {S R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  body: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  smul_mem' := SMulMemClass.smul_mem

中文:
定义 ofClass
  签名: {S R A : 类型} [交换半环 R] [非幺非结合半环 A] [模 R A]
  定义体: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  smul_mem' := SMulMemClass.smul_mem
-/
def ofClass {S R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [SetLike S A] [NonUnitalSubsemiringClass S A] [SMulMemClass S R A]
    (s : S) : NonUnitalSubalgebra R A where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  smul_mem' := SMulMemClass.smul_mem

instance (priority := 100) : CanLift (Set A) (NonUnitalSubalgebra R A) (↑)
    (fun s => 0 in s ∧ (forall {x y}, x in s -> y in s -> x + y in s) ∧ (forall {x y}, x in s -> y in s -> x * y in s) ∧
      forall (r : R) {x}, x in s -> r • x in s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        mul_mem' := h.2.2.1
        smul_mem' := h.2.2.2 },
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
    NonUnitalSubsemiringClass (NonUnitalSubalgebra R A) A where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'

/--
Instance `instSMulMemClass` / 实例 `instSMulMemClass`

English:
instance instSMulMemClass
  signature: : SMulMemClass (NonUnitalSubalgebra R A) R A where
  body: s.smul_mem'

中文:
实例 instSMulMemClass
  签名: : SMulMem类 (NonUnital子代数 R A) R A where
  定义体: s.smul_mem'

Depends on / 依赖: s.smul_mem, smul_mem
-/
instance instSMulMemClass : SMulMemClass (NonUnitalSubalgebra R A) R A where
  smul_mem {s} := s.smul_mem'

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : NonUnitalSubalgebra R A} {x : A}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

@[ext]

中文:
定理 mem_carrier
  条件: {s : NonUnital子代数 R A} {x : A}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

@[ext]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : NonUnitalSubalgebra R A} {x : A} : x in s.carrier ↔ x in s :=
  Iff.rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : NonUnitalSubalgebra R A} (h : forall x : A, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

@[simp]

中文:
定理 ext
  条件: {S T : NonUnital子代数 R A} (h : 对任意 x : A, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

@[simp]

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : NonUnitalSubalgebra R A} (h : forall x : A, x in S ↔ x in T) : S = T :=
  SetLike.ext h

@[simp]
/--
theorem `mem_toNonUnitalSubsemiring` / 定理 `mem_toNonUnitalSubsemiring`

English:
theorem mem_toNonUnitalSubsemiring
  given: {S : NonUnitalSubalgebra R A} {x}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toNonUnitalSubsemiring
  条件: {S : NonUnital子代数 R A} {x}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toNonUnitalSubsemiring {S : NonUnitalSubalgebra R A} {x} :
    x in S.toNonUnitalSubsemiring ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `coe_toNonUnitalSubsemiring` / 定理 `coe_toNonUnitalSubsemiring`

English:
theorem coe_toNonUnitalSubsemiring
  given: (S : NonUnitalSubalgebra R A)
  proof: rfl

中文:
定理 coe_toNonUnitalSubsemiring
  条件: (S : NonUnital子代数 R A)
  证明: rfl
-/
theorem coe_toNonUnitalSubsemiring (S : NonUnitalSubalgebra R A) :
    (↑S.toNonUnitalSubsemiring : Set A) = S :=
  rfl

/--
theorem `mem_toSubmodule` / 定理 `mem_toSubmodule`

English:
theorem mem_toSubmodule
  given: (S : NonUnitalSubalgebra R A) {x}
  statement: x in S.toSubmodule ↔ x in S
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toSubmodule
  条件: (S : NonUnital子代数 R A) {x}
  结论: x in S.toSubmodule ↔ x in S
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubmodule (S : NonUnitalSubalgebra R A) {x} : x in S.toSubmodule ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `coe_toSubmodule` / 定理 `coe_toSubmodule`

English:
theorem coe_toSubmodule
  given: (S : NonUnitalSubalgebra R A)
  statement: (↑S.toSubmodule : Set A) = S
  proof: rfl

中文:
定理 coe_toSubmodule
  条件: (S : NonUnital子代数 R A)
  结论: (↑S.toSubmodule : 集合 A) = S
  证明: rfl
-/
theorem coe_toSubmodule (S : NonUnitalSubalgebra R A) : (↑S.toSubmodule : Set A) = S :=
  rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S)
  body: { S.toNonUnitalSubsemiring.copy s hs with
    smul_mem' r a := by simpa [hs] using! S.smul_mem r }

@[simp, norm_cast]

中文:
定义 copy
  签名: (S : NonUnital子代数 R A) (s : 集合 A) (hs : s = ↑S)
  定义体: { S.toNonUnitalSubsemiring.copy s hs with
    smul_mem' r a := by simpa [hs] using! S.smul_mem r }

@[simp, norm_cast]
-/
protected def copy (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    NonUnitalSubalgebra R A :=
  { S.toNonUnitalSubsemiring.copy s hs with
    smul_mem' r a := by simpa [hs] using! S.smul_mem r }

@[simp, norm_cast]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S)
  proof: rfl

中文:
定理 coe_copy
  条件: (S : NonUnital子代数 R A) (s : 集合 A) (hs : s = ↑S)
  证明: rfl
-/
theorem coe_copy (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) :
    (S.copy s hs : Set A) = s :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: (S : NonUnital子代数 R A) (s : 集合 A) (hs : s = ↑S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (S : NonUnitalSubalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

instance (S : NonUnitalSubalgebra R A) : Inhabited S :=
  ⟨(0 : S.toNonUnitalSubsemiring)⟩

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocRing
variable [CommRing R]
variable [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B] [NonUnitalNonAssocRing C]
variable [Module R A] [Module R B] [Module R C]

/--
Instance `instNonUnitalSubringClass` / 实例 `instNonUnitalSubringClass`

English:
instance instNonUnitalSubringClass
  signature: : NonUnitalSubringClass (NonUnitalSubalgebra R A) A
  body: { NonUnitalSubalgebra.instNonUnitalSubsemiringClass with
    neg_mem {_ x} hx := neg_one_smul R x ▸ SMulMemClass.smul_mem _ hx }

中文:
实例 instNonUnitalSubringClass
  签名: : NonUnital子环类 (NonUnital子代数 R A) A
  定义体: { NonUnitalSubalgebra.instNonUnitalSubsemiringClass with
    neg_mem {_ x} hx := neg_one_smul R x ▸ SMulMemClass.smul_mem _ hx }

Depends on / 依赖: NonUnitalSubalgebra, NonUnitalSubalgebra.instNonUnitalSubsemiringClass, SMulMemClass, SMulMemClass.smul_mem, instNonUnitalSubsemiringClass, neg_mem, neg_one_smul, smul_mem
-/
instance instNonUnitalSubringClass : NonUnitalSubringClass (NonUnitalSubalgebra R A) A :=
  { NonUnitalSubalgebra.instNonUnitalSubsemiringClass with
    neg_mem {_ x} hx := neg_one_smul R x ▸ SMulMemClass.smul_mem _ hx }

/-- A non-unital subalgebra over a ring is also a `Subring`. -/
@[reducible]
/--
Definition of `toNonUnitalSubring` / `toNonUnitalSubring` 的定义

English:
definition toNonUnitalSubring
  signature: (S : NonUnitalSubalgebra R A)
  body: S.toNonUnitalSubsemiring
  neg_mem' := neg_mem (s := S)

中文:
定义 toNonUnitalSubring
  签名: (S : NonUnital子代数 R A)
  定义体: S.toNonUnitalSubsemiring
  neg_mem' := neg_mem (s := S)

Depends on / 依赖: S.toNonUnitalSubsemiring, toNonUnitalSubsemiring
-/
def toNonUnitalSubring (S : NonUnitalSubalgebra R A) : NonUnitalSubring A where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  neg_mem' := neg_mem (s := S)

/--
theorem `mem_toNonUnitalSubring` / 定理 `mem_toNonUnitalSubring`

English:
theorem mem_toNonUnitalSubring
  given: {S : NonUnitalSubalgebra R A} {x}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toNonUnitalSubring
  条件: {S : NonUnital子代数 R A} {x}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toNonUnitalSubring {S : NonUnitalSubalgebra R A} {x} :
    x in S.toNonUnitalSubring ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `coe_toNonUnitalSubring` / 定理 `coe_toNonUnitalSubring`

English:
theorem coe_toNonUnitalSubring
  given: (S : NonUnitalSubalgebra R A)
  proof: rfl

中文:
定理 coe_toNonUnitalSubring
  条件: (S : NonUnital子代数 R A)
  证明: rfl
-/
theorem coe_toNonUnitalSubring (S : NonUnitalSubalgebra R A) :
    (↑S.toNonUnitalSubring : Set A) = S :=
  rfl

/--
theorem `toNonUnitalSubring_injective` / 定理 `toNonUnitalSubring_injective`

English:
theorem toNonUnitalSubring_injective
  proof: fun S T h => ext fun x => by rw [← mem_toNonUnitalSubring, ← mem_toNonUnitalSubring, h]

中文:
定理 toNonUnitalSubring_injective
  证明: fun S T h => ext fun x => by rw [← mem_toNonUnitalSubring, ← mem_toNonUnitalSubring, h]

Depends on / 依赖: mem_toNonUnitalSubring
-/
theorem toNonUnitalSubring_injective :
    Function.Injective (toNonUnitalSubring : NonUnitalSubalgebra R A -> NonUnitalSubring A) :=
  fun S T h => ext fun x => by rw [← mem_toNonUnitalSubring, ← mem_toNonUnitalSubring, h]

/--
theorem `toNonUnitalSubring_inj` / 定理 `toNonUnitalSubring_inj`

English:
theorem toNonUnitalSubring_inj
  given: {S U : NonUnitalSubalgebra R A}
  proof: toNonUnitalSubring_injective.eq_iff

中文:
定理 toNonUnitalSubring_inj
  条件: {S U : NonUnital子代数 R A}
  证明: toNonUnitalSubring_injective.eq_iff

Depends on / 依赖: eq_iff, toNonUnitalSubring_injective, toNonUnitalSubring_injective.eq_iff
-/
theorem toNonUnitalSubring_inj {S U : NonUnitalSubalgebra R A} :
    S.toNonUnitalSubring = U.toNonUnitalSubring ↔ S = U :=
  toNonUnitalSubring_injective.eq_iff

end NonUnitalNonAssocRing

section



/--
Instance `toNonUnitalNonAssocSemiring` / 实例 `toNonUnitalNonAssocSemiring`

English:
instance toNonUnitalNonAssocSemiring
  signature: [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  body: inferInstance

中文:
实例 toNonUnitalNonAssocSemiring
  签名: [交换半环 R] [非幺非结合半环 A] [模 R A]
  定义体: inferInstance
-/
instance toNonUnitalNonAssocSemiring [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalNonAssocSemiring S :=
  inferInstance

/--
Instance `toNonUnitalSemiring` / 实例 `toNonUnitalSemiring`

English:
instance toNonUnitalSemiring
  signature: [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  body: inferInstance

中文:
实例 toNonUnitalSemiring
  签名: [交换半环 R] [非幺半环 A] [模 R A]
  定义体: inferInstance
-/
instance toNonUnitalSemiring [CommSemiring R] [NonUnitalSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalSemiring S :=
  inferInstance

/--
Instance `toNonUnitalCommSemiring` / 实例 `toNonUnitalCommSemiring`

English:
instance toNonUnitalCommSemiring
  signature: [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
  body: inferInstance

中文:
实例 toNonUnitalCommSemiring
  签名: [交换半环 R] [非幺交换半环 A] [模 R A]
  定义体: inferInstance
-/
instance toNonUnitalCommSemiring [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalCommSemiring S :=
  inferInstance

/--
Instance `toNonUnitalNonAssocRing` / 实例 `toNonUnitalNonAssocRing`

English:
instance toNonUnitalNonAssocRing
  signature: [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  body: inferInstance

中文:
实例 toNonUnitalNonAssocRing
  签名: [交换环 R] [非幺非结合环 A] [模 R A]
  定义体: inferInstance
-/
instance toNonUnitalNonAssocRing [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalNonAssocRing S :=
  inferInstance

/--
Instance `toNonUnitalRing` / 实例 `toNonUnitalRing`

English:
instance toNonUnitalRing
  signature: [CommRing R] [NonUnitalRing A] [Module R A]
  body: inferInstance

中文:
实例 toNonUnitalRing
  签名: [交换环 R] [非幺环 A] [模 R A]
  定义体: inferInstance
-/
instance toNonUnitalRing [CommRing R] [NonUnitalRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalRing S :=
  inferInstance

/--
Instance `toNonUnitalCommRing` / 实例 `toNonUnitalCommRing`

English:
instance toNonUnitalCommRing
  signature: [CommRing R] [NonUnitalCommRing A] [Module R A]
  body: inferInstance

中文:
实例 toNonUnitalCommRing
  签名: [交换环 R] [非幺交换环 A] [模 R A]
  定义体: inferInstance
-/
instance toNonUnitalCommRing [CommRing R] [NonUnitalCommRing A] [Module R A]
    (S : NonUnitalSubalgebra R A) : NonUnitalCommRing S :=
  inferInstance

end

/--
Definition of `toSubmodule'` / `toSubmodule'` 的定义

English:
definition toSubmodule'
  signature: [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  body: { toFun := fun S => S.toSubmodule
inj' := fun S T h => ext by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

中文:
定义 toSubmodule'
  签名: [交换半环 R] [非幺非结合半环 A] [模 R A]
  定义体: { toFun := fun S => S.toSubmodule
inj' := fun S T h => ext by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

Depends on / 依赖: S.toSubmodule, SetLike, SetLike.coe_subset_coe, SetLike.coe_subset_coe.symm.trans, SetLike.ext_iff, coe_subset_coe, ext_iff, map_rel_iff, toSubmodule
-/
def toSubmodule' [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
    NonUnitalSubalgebra R A ↪o Submodule R A where
  toEmbedding :=
    { toFun := fun S => S.toSubmodule
inj' := fun S T h => ext by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

/--
Definition of `toNonUnitalSubsemiring'` / `toNonUnitalSubsemiring'` 的定义

English:
definition toNonUnitalSubsemiring'
  signature: [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  body: { toFun := fun S => S.toNonUnitalSubsemiring
inj' := fun S T h => ext by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

中文:
定义 toNonUnitalSubsemiring'
  签名: [交换半环 R] [非幺非结合半环 A] [模 R A]
  定义体: { toFun := fun S => S.toNonUnitalSubsemiring
inj' := fun S T h => ext by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

Depends on / 依赖: S.toNonUnitalSubsemiring, SetLike, SetLike.coe_subset_coe, SetLike.coe_subset_coe.symm.trans, SetLike.ext_iff, coe_subset_coe, ext_iff, map_rel_iff, toNonUnitalSubsemiring
-/
def toNonUnitalSubsemiring' [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
    NonUnitalSubalgebra R A ↪o NonUnitalSubsemiring A where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubsemiring
inj' := fun S T h => ext by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

/--
Definition of `toNonUnitalSubring'` / `toNonUnitalSubring'` 的定义

English:
definition toNonUnitalSubring'
  signature: [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  body: { toFun := fun S => S.toNonUnitalSubring
inj' := fun S T h => ext by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

中文:
定义 toNonUnitalSubring'
  签名: [交换环 R] [非幺非结合环 A] [模 R A]
  定义体: { toFun := fun S => S.toNonUnitalSubring
inj' := fun S T h => ext by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

Depends on / 依赖: S.toNonUnitalSubring, SetLike, SetLike.coe_subset_coe, SetLike.coe_subset_coe.symm.trans, SetLike.ext_iff, coe_subset_coe, ext_iff, map_rel_iff, toNonUnitalSubring
-/
def toNonUnitalSubring' [CommRing R] [NonUnitalNonAssocRing A] [Module R A] :
    NonUnitalSubalgebra R A ↪o NonUnitalSubring A where
  toEmbedding :=
    { toFun := fun S => S.toNonUnitalSubring
inj' := fun S T h => ext by apply SetLike.ext_iff.1 h }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]
variable [Module R A] [Module R B] [Module R C]
variable {S : NonUnitalSubalgebra R A}

section


/--
Instance `instModule'` / 实例 `instModule'`

English:
instance instModule'
  signature: [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
  body: SMulMemClass.toModule' _ R' R A S

中文:
实例 instModule'
  签名: [半环 R'] [标量乘法 R' R] [模 R' A] [标量塔 R' R A]
  定义体: SMulMemClass.toModule' _ R' R A S

Depends on / 依赖: SMulMemClass, SMulMemClass.toModule, toModule
-/
instance instModule' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : Module R' S :=
  SMulMemClass.toModule' _ R' R A S

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: : Module R S
  body: S.instModule'

中文:
实例 instModule
  签名: : 模 R S
  定义体: S.instModule'

Depends on / 依赖: S.instModule, instModule
-/
instance instModule : Module R S :=
  S.instModule'

/--
Instance `instIsScalarTower'` / 实例 `instIsScalarTower'`

English:
instance instIsScalarTower'
  signature: [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
  body: S.toSubmodule.isScalarTower

中文:
实例 instIsScalarTower'
  签名: [半环 R'] [标量乘法 R' R] [模 R' A] [标量塔 R' R A]
  定义体: S.toSubmodule.isScalarTower

Depends on / 依赖: S.toSubmodule.isScalarTower, isScalarTower, toSubmodule
-/
instance instIsScalarTower' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    IsScalarTower R' R S :=
  S.toSubmodule.isScalarTower

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsScalarTower
  signature: R A A] : IsScalarTower R S S where
  body: Subtype.ext smul_assoc r (x : A) (y : A)

中文:
实例 [标量塔
  签名: R A A] : 标量塔 R S S where
  定义体: Subtype.ext smul_assoc r (x : A) (y : A)

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance [IsScalarTower R A A] : IsScalarTower R S S where
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

/--
Instance `instIsTorsionFree` / 实例 `instIsTorsionFree`

English:
instance instIsTorsionFree
  signature: [Module.IsTorsionFree R A]
  body: S.toSubmodule.instIsTorsionFree

中文:
实例 instIsTorsionFree
  签名: [模.是无挠 R A]
  定义体: S.toSubmodule.instIsTorsionFree

Depends on / 依赖: S.toSubmodule.instIsTorsionFree, instIsTorsionFree, toSubmodule
-/
instance instIsTorsionFree [Module.IsTorsionFree R A] : Module.IsTorsionFree R S :=
  S.toSubmodule.instIsTorsionFree

end

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
  statement: {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  proof: rfl

中文:
定理 coe_neg
  结论: {R : 类型u} {A : 类型v} [交换环 R] [环 A] [代数 R A]
  证明: rfl
-/
protected theorem coe_neg {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : NonUnitalSubalgebra R A} (x : S) : (↑(-x) : A) = -↑x :=
  rfl

/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  statement: {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sub
  结论: {R : 类型u} {A : 类型v} [交换环 R] [环 A] [代数 R A]
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : NonUnitalSubalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y :=
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
theorem `toNonUnitalSubsemiring_subtype` / 定理 `toNonUnitalSubsemiring_subtype`

English:
theorem toNonUnitalSubsemiring_subtype
  proof: rfl

@[simp]

中文:
定理 toNonUnitalSubsemiring_subtype
  证明: rfl

@[simp]
-/
theorem toNonUnitalSubsemiring_subtype :
    NonUnitalSubsemiringClass.subtype S = NonUnitalSubalgebraClass.subtype (R := R) S :=
  rfl

@[simp]
/--
theorem `toSubring_subtype` / 定理 `toSubring_subtype`

English:
theorem toSubring_subtype
  statement: {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  proof: rfl

中文:
定理 toSubring_subtype
  结论: {R A : 类型} [交换环 R] [环 A] [代数 R A]
  证明: rfl
-/
theorem toSubring_subtype {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (S : NonUnitalSubalgebra R A) :
    NonUnitalSubringClass.subtype S = NonUnitalSubalgebraClass.subtype (R := R) S :=
  rfl

/--
Definition of `toSubmoduleEquiv` / `toSubmoduleEquiv` 的定义

English:
definition toSubmoduleEquiv
  signature: (S : NonUnitalSubalgebra R A)
  body: LinearEquiv.ofEq _ _ rfl

中文:
定义 toSubmoduleEquiv
  签名: (S : NonUnital子代数 R A)
  定义体: LinearEquiv.ofEq _ _ rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.ofEq
-/
def toSubmoduleEquiv (S : NonUnitalSubalgebra R A) : S.toSubmodule ≃ₗ[R] S :=
  LinearEquiv.ofEq _ _ rfl

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : F) (S : NonUnitalSubalgebra R A)
  body: { S.toNonUnitalSubsemiring.map (f : A ->ₙ+* B) with
    smul_mem' := fun r b hb => by
      rcases hb with ⟨a, ha, rfl⟩
      exact map_smulₛₗ f r a ▸ Set.mem_image_of_mem f (S.smul_mem' r ha) }

@[gcongr]

中文:
定义 map
  签名: (f : F) (S : NonUnital子代数 R A)
  定义体: { S.toNonUnitalSubsemiring.map (f : A ->ₙ+* B) with
    smul_mem' := fun r b hb => by
      rcases hb with ⟨a, ha, rfl⟩
      exact map_smulₛₗ f r a ▸ Set.mem_image_of_mem f (S.smul_mem' r ha) }

@[gcongr]

Depends on / 依赖: S.smul_mem, S.toNonUnitalSubsemiring.map, Set.mem_image_of_mem, mem_image_of_mem, smul_mem, toNonUnitalSubsemiring
-/
def map (f : F) (S : NonUnitalSubalgebra R A) : NonUnitalSubalgebra R B :=
  { S.toNonUnitalSubsemiring.map (f : A ->ₙ+* B) with
    smul_mem' := fun r b hb => by
      rcases hb with ⟨a, ha, rfl⟩
      exact map_smulₛₗ f r a ▸ Set.mem_image_of_mem f (S.smul_mem' r ha) }

@[gcongr]
/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: {S₁ S₂ : NonUnitalSubalgebra R A} {f : F}
  proof: Set.image_mono

中文:
定理 map_mono
  条件: {S₁ S₂ : NonUnital子代数 R A} {f : F}
  证明: Set.image_mono

Depends on / 依赖: Set.image_mono, image_mono
-/
theorem map_mono {S₁ S₂ : NonUnitalSubalgebra R A} {f : F} :
    S₁ <= S₂ -> (map f S₁ : NonUnitalSubalgebra R B) <= map f S₂ :=
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
    Function.Injective (map f : NonUnitalSubalgebra R A -> NonUnitalSubalgebra R B) :=
  fun _S₁ _S₂ ih =>
ext Set.ext_iff.1 Set.image_injective.2 hf Set.ext SetLike.ext_iff.mp ih

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (S : NonUnitalSubalgebra R A)
  statement: map (NonUnitalAlgHom.id R A) S = S
  proof: SetLike.coe_injective Set.image_id _

中文:
定理 map_id
  条件: (S : NonUnital子代数 R A)
  结论: map (非幺Alg态射.id R A) S = S
  证明: SetLike.coe_injective Set.image_id _

Depends on / 依赖: Set.image_id, SetLike, SetLike.coe_injective, coe_injective, image_id
-/
theorem map_id (S : NonUnitalSubalgebra R A) : map (NonUnitalAlgHom.id R A) S = S :=
SetLike.coe_injective Set.image_id _

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (S : NonUnitalSubalgebra R A) (g : B ->ₙₐ[R] C) (f : A ->ₙₐ[R] B)
  proof: SetLike.coe_injective Set.image_image _ _ _

@[simp]

中文:
定理 map_map
  条件: (S : NonUnital子代数 R A) (g : B ->ₙₐ[R] C) (f : A ->ₙₐ[R] B)
  证明: SetLike.coe_injective Set.image_image _ _ _

@[simp]

Depends on / 依赖: Set.image_image, SetLike, SetLike.coe_injective, coe_injective, image_image
-/
theorem map_map (S : NonUnitalSubalgebra R A) (g : B ->ₙₐ[R] C) (f : A ->ₙₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
SetLike.coe_injective Set.image_image _ _ _

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {S : NonUnitalSubalgebra R A} {f : F} {y : B}
  statement: y in map f S ↔ exists x in S, f x = y
  proof: NonUnitalSubsemiring.mem_map

中文:
定理 mem_map
  条件: {S : NonUnital子代数 R A} {f : F} {y : B}
  结论: y in map f S ↔ 存在 x in S, f x = y
  证明: NonUnitalSubsemiring.mem_map

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.mem_map, mem_map
-/
theorem mem_map {S : NonUnitalSubalgebra R A} {f : F} {y : B} : y in map f S ↔ exists x in S, f x = y :=
  NonUnitalSubsemiring.mem_map

/--
theorem `map_toSubmodule` / 定理 `map_toSubmodule`

English:
theorem map_toSubmodule
  given: {S : NonUnitalSubalgebra R A} {f : F}
  proof: SetLike.coe_injective rfl

中文:
定理 map_toSubmodule
  条件: {S : NonUnital子代数 R A} {f : F}
  证明: SetLike.coe_injective rfl

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem map_toSubmodule {S : NonUnitalSubalgebra R A} {f : F} :
    -- TODO: introduce a better coercion from `NonUnitalAlgHomClass` to `LinearMap`
    (map f S).toSubmodule = Submodule.map (LinearMapClass.linearMap f) S.toSubmodule :=
  SetLike.coe_injective rfl

/--
theorem `map_toNonUnitalSubsemiring` / 定理 `map_toNonUnitalSubsemiring`

English:
theorem map_toNonUnitalSubsemiring
  given: {S : NonUnitalSubalgebra R A} {f : F}
  proof: SetLike.coe_injective rfl

@[simp]

中文:
定理 map_toNonUnitalSubsemiring
  条件: {S : NonUnital子代数 R A} {f : F}
  证明: SetLike.coe_injective rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem map_toNonUnitalSubsemiring {S : NonUnitalSubalgebra R A} {f : F} :
    (map f S).toNonUnitalSubsemiring = S.toNonUnitalSubsemiring.map (f : A ->ₙ+* B) :=
  SetLike.coe_injective rfl

@[simp]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (S : NonUnitalSubalgebra R A) (f : F)
  statement: (map f S : Set B) = f '' S
  proof: rfl

中文:
定理 coe_map
  条件: (S : NonUnital子代数 R A) (f : F)
  结论: (map f S : 集合 B) = f '' S
  证明: rfl
-/
theorem coe_map (S : NonUnitalSubalgebra R A) (f : F) : (map f S : Set B) = f '' S :=
  rfl

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : F) (S : NonUnitalSubalgebra R B)
  body: { S.toNonUnitalSubsemiring.comap (f : A ->ₙ+* B) with
    smul_mem' := fun r a (ha : f a in S) =>
      show f (r • a) in S from (map_smulₛₗ f r a).symm ▸ SMulMemClass.smul_mem r ha }

中文:
定义 comap
  签名: (f : F) (S : NonUnital子代数 R B)
  定义体: { S.toNonUnitalSubsemiring.comap (f : A ->ₙ+* B) with
    smul_mem' := fun r a (ha : f a in S) =>
      show f (r • a) in S from (map_smulₛₗ f r a).symm ▸ SMulMemClass.smul_mem r ha }

Depends on / 依赖: S.toNonUnitalSubsemiring.comap, SMulMemClass, SMulMemClass.smul_mem, smul_mem, toNonUnitalSubsemiring
-/
def comap (f : F) (S : NonUnitalSubalgebra R B) : NonUnitalSubalgebra R A :=
  { S.toNonUnitalSubsemiring.comap (f : A ->ₙ+* B) with
    smul_mem' := fun r a (ha : f a in S) =>
      show f (r • a) in S from (map_smulₛₗ f r a).symm ▸ SMulMemClass.smul_mem r ha }

/--
theorem `map_le` / 定理 `map_le`

English:
theorem map_le
  given: {S : NonUnitalSubalgebra R A} {f : F} {U : NonUnitalSubalgebra R B}
  proof: Set.image_subset_iff

中文:
定理 map_le
  条件: {S : NonUnital子代数 R A} {f : F} {U : NonUnital子代数 R B}
  证明: Set.image_subset_iff

Depends on / 依赖: Set.image_subset_iff, image_subset_iff
-/
theorem map_le {S : NonUnitalSubalgebra R A} {f : F} {U : NonUnitalSubalgebra R B} :
    map f S <= U ↔ S <= comap f U :=
  Set.image_subset_iff

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : F)
  proof: fun _ _ => map_le

@[simp]

中文:
定理 gc_map_comap
  条件: (f : F)
  证明: fun _ _ => map_le

@[simp]

Depends on / 依赖: map_le
-/
theorem gc_map_comap (f : F) :
    GaloisConnection (map f : NonUnitalSubalgebra R A -> NonUnitalSubalgebra R B) (comap f) :=
  fun _ _ => map_le

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: (S : NonUnitalSubalgebra R B) (f : F) (x : A)
  statement: x in comap f S ↔ f x in S
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 mem_comap
  条件: (S : NonUnital子代数 R B) (f : F) (x : A)
  结论: x in comap f S ↔ f x in S
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap (S : NonUnitalSubalgebra R B) (f : F) (x : A) : x in comap f S ↔ f x in S :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (S : NonUnitalSubalgebra R B) (f : F)
  statement: (comap f S : Set A) = f ⁻¹' (S : Set B)
  proof: rfl

中文:
定理 coe_comap
  条件: (S : NonUnital子代数 R B) (f : F)
  结论: (comap f S : 集合 A) = f ⁻¹' (S : 集合 B)
  证明: rfl
-/
theorem coe_comap (S : NonUnitalSubalgebra R B) (f : F) : (comap f S : Set A) = f ⁻¹' (S : Set B) :=
  rfl

/--
Instance `noZeroDivisors` / 实例 `noZeroDivisors`

English:
instance noZeroDivisors
  signature: {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [NoZeroDivisors A]
  body: NonUnitalSubsemiringClass.noZeroDivisors S

中文:
实例 noZeroDivisors
  签名: {R A : 类型} [交换半环 R] [非幺半环 A] [无零因子 A]
  定义体: NonUnitalSubsemiringClass.noZeroDivisors S

Depends on / 依赖: NonUnitalSubsemiringClass, NonUnitalSubsemiringClass.noZeroDivisors, Subsingleton, noZeroDivisors
-/
instance noZeroDivisors {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [NoZeroDivisors A]
    [Module R A] (S : NonUnitalSubalgebra R A) : NoZeroDivisors S :=
  NonUnitalSubsemiringClass.noZeroDivisors S

end NonUnitalSubalgebra

namespace Submodule

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

/--
Definition of `toNonUnitalSubalgebra` / `toNonUnitalSubalgebra` 的定义

English:
definition toNonUnitalSubalgebra
  signature: (p : Submodule R A) (h_mul : forall x y, x in p -> y in p -> x * y in p)
  body: { p with
    mul_mem' := h_mul _ _ }

@[simp]

中文:
定义 toNonUnitalSubalgebra
  签名: (p : 子模 R A) (h_mul : 对任意 x y, x in p -> y in p -> x * y in p)
  定义体: { p with
    mul_mem' := h_mul _ _ }

@[simp]

Depends on / 依赖: Nontrivial, h_mul, mul_mem
-/
def toNonUnitalSubalgebra (p : Submodule R A) (h_mul : forall x y, x in p -> y in p -> x * y in p) :
    NonUnitalSubalgebra R A :=
  { p with
    mul_mem' := h_mul _ _ }

@[simp]
/--
theorem `mem_toNonUnitalSubalgebra` / 定理 `mem_toNonUnitalSubalgebra`

English:
theorem mem_toNonUnitalSubalgebra
  given: {p : Submodule R A} {h_mul} {x}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toNonUnitalSubalgebra
  条件: {p : 子模 R A} {h_mul} {x}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toNonUnitalSubalgebra {p : Submodule R A} {h_mul} {x} :
    x in p.toNonUnitalSubalgebra h_mul ↔ x in p :=
  Iff.rfl

@[simp]
/--
theorem `coe_toNonUnitalSubalgebra` / 定理 `coe_toNonUnitalSubalgebra`

English:
theorem coe_toNonUnitalSubalgebra
  given: (p : Submodule R A) (h_mul)
  proof: rfl

中文:
定理 coe_toNonUnitalSubalgebra
  条件: (p : 子模 R A) (h_mul)
  证明: rfl
-/
theorem coe_toNonUnitalSubalgebra (p : Submodule R A) (h_mul) :
    (p.toNonUnitalSubalgebra h_mul : Set A) = p :=
  rfl

/--
theorem `toNonUnitalSubalgebra_mk` / 定理 `toNonUnitalSubalgebra_mk`

English:
theorem toNonUnitalSubalgebra_mk
  given: (p : Submodule R A) hmul
  proof: rfl

@[simp]

中文:
定理 toNonUnitalSubalgebra_mk
  条件: (p : 子模 R A) hmul
  证明: rfl

@[simp]
-/
theorem toNonUnitalSubalgebra_mk (p : Submodule R A) hmul :
    p.toNonUnitalSubalgebra hmul =
      NonUnitalSubalgebra.mk ⟨⟨⟨p, p.add_mem⟩, p.zero_mem⟩, hmul _ _⟩ p.smul_mem' :=
  rfl

@[simp]
/--
theorem `toNonUnitalSubalgebra_toSubmodule` / 定理 `toNonUnitalSubalgebra_toSubmodule`

English:
theorem toNonUnitalSubalgebra_toSubmodule
  given: (p : Submodule R A) (h_mul)
  proof: SetLike.coe_injective rfl

@[simp]

中文:
定理 toNonUnitalSubalgebra_toSubmodule
  条件: (p : 子模 R A) (h_mul)
  证明: SetLike.coe_injective rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem toNonUnitalSubalgebra_toSubmodule (p : Submodule R A) (h_mul) :
    (p.toNonUnitalSubalgebra h_mul).toSubmodule = p :=
  SetLike.coe_injective rfl

@[simp]
/--
theorem `_root_.NonUnitalSubalgebra.toSubmodule_toNonUnitalSubalgebra` / 定理 `_root_.NonUnitalSubalgebra.toSubmodule_toNonUnitalSubalgebra`

English:
theorem _root_.NonUnitalSubalgebra.toSubmodule_toNonUnitalSubalgebra
  given: (S : NonUnitalSubalgebra R A)
  proof: SetLike.coe_injective rfl

中文:
定理 _root_.NonUnital子代数.toSubmodule_toNonUnitalSubalgebra
  条件: (S : NonUnital子代数 R A)
  证明: SetLike.coe_injective rfl
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

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (φ : F)
  body: NonUnitalRingHom.srange (φ : A ->ₙ+* B)
  smul_mem' := fun r a => by rintro ⟨a, rfl⟩; exact ⟨r • a, map_smul φ r a⟩

@[simp]

中文:
定义 range
  签名: (φ : F)
  定义体: NonUnitalRingHom.srange (φ : A ->ₙ+* B)
  smul_mem' := fun r a => by rintro ⟨a, rfl⟩; exact ⟨r • a, map_smul φ r a⟩

@[simp]
-/
protected def range (φ : F) : NonUnitalSubalgebra R B where
  toNonUnitalSubsemiring := NonUnitalRingHom.srange (φ : A ->ₙ+* B)
  smul_mem' := fun r a => by rintro ⟨a, rfl⟩; exact ⟨r • a, map_smul φ r a⟩

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
    y in (NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) ↔ exists x : A, φ x = y :=
  NonUnitalRingHom.mem_srange

/--
theorem `mem_range_self` / 定理 `mem_range_self`

English:
theorem mem_range_self
  given: (φ : F) (x : A)
  proof: (NonUnitalAlgHom.mem_range φ).2 ⟨x, rfl⟩

@[simp]

中文:
定理 mem_range_self
  条件: (φ : F) (x : A)
  证明: (NonUnitalAlgHom.mem_range φ).2 ⟨x, rfl⟩

@[simp]

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.mem_range, mem_range
-/
theorem mem_range_self (φ : F) (x : A) :
    φ x in (NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) :=
  (NonUnitalAlgHom.mem_range φ).2 ⟨x, rfl⟩

@[simp]
/--
theorem `coe_range` / 定理 `coe_range`

English:
theorem coe_range
  given: (φ : F)
  proof: by
  ext
  rw [SetLike.mem_coe]; rw [mem_range]; rw [Set.mem_range]

中文:
定理 coe_range
  条件: (φ : F)
  证明: by
  ext
  rw [SetLike.mem_coe]; rw [mem_range]; rw [Set.mem_range]

Depends on / 依赖: Set.mem_range, SetLike, SetLike.mem_coe, mem_coe, mem_range
-/
theorem coe_range (φ : F) :
    ((NonUnitalAlgHom.range φ : NonUnitalSubalgebra R B) : Set B) = Set.range (φ : A -> B) := by
  ext
  rw [SetLike.mem_coe]; rw [mem_range]; rw [Set.mem_range]

/--
theorem `range_comp` / 定理 `range_comp`

English:
theorem range_comp
  given: (f : A ->ₙₐ[R] B) (g : B ->ₙₐ[R] C)
  proof: SetLike.coe_injective (Set.range_comp g f)

中文:
定理 range_comp
  条件: (f : A ->ₙₐ[R] B) (g : B ->ₙₐ[R] C)
  证明: SetLike.coe_injective (Set.range_comp g f)

Depends on / 依赖: Set.range_comp, SetLike, SetLike.coe_injective, coe_injective, range_comp
-/
theorem range_comp (f : A ->ₙₐ[R] B) (g : B ->ₙₐ[R] C) :
    NonUnitalAlgHom.range (g.comp f) = (NonUnitalAlgHom.range f).map g :=
  SetLike.coe_injective (Set.range_comp g f)

/--
theorem `range_comp_le_range` / 定理 `range_comp_le_range`

English:
theorem range_comp_le_range
  given: (f : A ->ₙₐ[R] B) (g : B ->ₙₐ[R] C)
  proof: SetLike.coe_mono (Set.range_comp_subset_range f g)

中文:
定理 range_comp_le_range
  条件: (f : A ->ₙₐ[R] B) (g : B ->ₙₐ[R] C)
  证明: SetLike.coe_mono (Set.range_comp_subset_range f g)

Depends on / 依赖: Set.range_comp_subset_range, SetLike, SetLike.coe_mono, coe_mono, range_comp_subset_range
-/
theorem range_comp_le_range (f : A ->ₙₐ[R] B) (g : B ->ₙₐ[R] C) :
    NonUnitalAlgHom.range (g.comp f) <= NonUnitalAlgHom.range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : F) (S : NonUnitalSubalgebra R B) (hf : forall x, f x in S)
  body: { NonUnitalRingHom.codRestrict (f : A ->ₙ+* B) S.toNonUnitalSubsemiring hf with
map_smul' := fun r a => Subtype.ext map_smul f r a }

@[simp]

中文:
定义 codRestrict
  签名: (f : F) (S : NonUnital子代数 R B) (hf : 对任意 x, f x in S)
  定义体: { NonUnitalRingHom.codRestrict (f : A ->ₙ+* B) S.toNonUnitalSubsemiring hf with
map_smul' := fun r a => Subtype.ext map_smul f r a }

@[simp]

Depends on / 依赖: NonUnitalRingHom, NonUnitalRingHom.codRestrict, S.toNonUnitalSubsemiring, Subtype, Subtype.ext, codRestrict, map_smul, toNonUnitalSubsemiring
-/
def codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : forall x, f x in S) : A ->ₙₐ[R] S :=
  { NonUnitalRingHom.codRestrict (f : A ->ₙ+* B) S.toNonUnitalSubsemiring hf with
map_smul' := fun r a => Subtype.ext map_smul f r a }

@[simp]
/--
theorem `subtype_comp_codRestrict` / 定理 `subtype_comp_codRestrict`

English:
theorem subtype_comp_codRestrict
  given: (f : F) (S : NonUnitalSubalgebra R B) (hf : forall x : A, f x in S)
  proof: rfl

@[simp]

中文:
定理 subtype_comp_codRestrict
  条件: (f : F) (S : NonUnital子代数 R B) (hf : 对任意 x : A, f x in S)
  证明: rfl

@[simp]
-/
theorem subtype_comp_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : forall x : A, f x in S) :
    (NonUnitalSubalgebraClass.subtype S).comp (NonUnitalAlgHom.codRestrict f S hf) = f :=
  rfl

@[simp]
/--
theorem `coe_codRestrict` / 定理 `coe_codRestrict`

English:
theorem coe_codRestrict
  given: (f : F) (S : NonUnitalSubalgebra R B) (hf : forall x, f x in S) (x : A)
  proof: rfl

中文:
定理 coe_codRestrict
  条件: (f : F) (S : NonUnital子代数 R B) (hf : 对任意 x, f x in S) (x : A)
  证明: rfl
-/
theorem coe_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : forall x, f x in S) (x : A) :
    ↑(NonUnitalAlgHom.codRestrict f S hf x) = f x :=
  rfl

/--
theorem `injective_codRestrict` / 定理 `injective_codRestrict`

English:
theorem injective_codRestrict
  given: (f : F) (S : NonUnitalSubalgebra R B) (hf : forall x : A, f x in S)
  proof: ⟨fun H _x _y hxy => H Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

中文:
定理 injective_codRestrict
  条件: (f : F) (S : NonUnital子代数 R B) (hf : 对任意 x : A, f x in S)
  证明: ⟨fun H _x _y hxy => H Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

Depends on / 依赖: Subtype, Subtype.ext, Subtype.val, congr_arg
-/
theorem injective_codRestrict (f : F) (S : NonUnitalSubalgebra R B) (hf : forall x : A, f x in S) :
    Function.Injective (NonUnitalAlgHom.codRestrict f S hf) ↔ Function.Injective f :=
⟨fun H _x _y hxy => H Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

/--
Definition of `rangeRestrict` / `rangeRestrict` 的定义

English:
abbreviation rangeRestrict
  signature: (f : F)
  body: NonUnitalAlgHom.codRestrict f (NonUnitalAlgHom.range f) (NonUnitalAlgHom.mem_range_self f)

中文:
缩写 rangeRestrict
  签名: (f : F)
  定义体: NonUnitalAlgHom.codRestrict f (NonUnitalAlgHom.range f) (NonUnitalAlgHom.mem_range_self f)

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.codRestrict, NonUnitalAlgHom.mem_range_self, NonUnitalAlgHom.range, codRestrict, mem_range_self
-/
abbrev rangeRestrict (f : F) : A ->ₙₐ[R] (NonUnitalAlgHom.range f : NonUnitalSubalgebra R B) :=
  NonUnitalAlgHom.codRestrict f (NonUnitalAlgHom.range f) (NonUnitalAlgHom.mem_range_self f)

/--
Definition of `equalizer` / `equalizer` 的定义

English:
definition equalizer
  signature: (ϕ ψ : F)
  body: {a | (ϕ a : B) = ψ a}
  zero_mem' := by rw [Set.mem_ofPred_eq, map_zero, map_zero]
  add_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_ofPred_eq]; rw [map_add]; rw [map_add]; rw [hx]; rw [hy]
  mul_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_ofPred_eq]; rw [map_mul]; rw [map_mul]; rw [hx]; rw [hy]
  smul_mem' r x (hx : ϕ x = ψ x) := by rw [Set.mem_ofPred_eq, map_smul, map_smul, hx]

@[simp]

中文:
定义 equalizer
  签名: (ϕ ψ : F)
  定义体: {a | (ϕ a : B) = ψ a}
  zero_mem' := by rw [Set.mem_ofPred_eq, map_zero, map_zero]
  add_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_ofPred_eq]; rw [map_add]; rw [map_add]; rw [hx]; rw [hy]
  mul_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_ofPred_eq]; rw [map_mul]; rw [map_mul]; rw [hx]; rw [hy]
  smul_mem' r x (hx : ϕ x = ψ x) := by rw [Set.mem_ofPred_eq, map_smul, map_smul, hx]

@[simp]
-/
def equalizer (ϕ ψ : F) : NonUnitalSubalgebra R A where
  carrier := {a | (ϕ a : B) = ψ a}
  zero_mem' := by rw [Set.mem_ofPred_eq, map_zero, map_zero]
  add_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_ofPred_eq]; rw [map_add]; rw [map_add]; rw [hx]; rw [hy]
  mul_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_ofPred_eq]; rw [map_mul]; rw [map_mul]; rw [hx]; rw [hy]
  smul_mem' r x (hx : ϕ x = ψ x) := by rw [Set.mem_ofPred_eq, map_smul, map_smul, hx]

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
    x in NonUnitalAlgHom.equalizer φ ψ ↔ φ x = ψ x :=
  Iff.rfl

/--
Instance `fintypeRange` / 实例 `fintypeRange`

English:
instance fintypeRange
  signature: [Fintype A] [DecidableEq B] (φ : F)
  body: Set.fintypeRange φ

中文:
实例 fintypeRange
  签名: [有限类型 A] [DecidableEq B] (φ : F)
  定义体: Set.fintypeRange φ

Depends on / 依赖: Set.fintypeRange, fintypeRange
-/
instance fintypeRange [Fintype A] [DecidableEq B] (φ : F) :
    Fintype (NonUnitalAlgHom.range φ) :=
  Set.fintypeRange φ

end NonUnitalAlgHom

namespace NonUnitalAlgebra

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}
variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

@[simp]
/--
lemma `span_eq_toSubmodule` / 引理 `span_eq_toSubmodule`

English:
lemma span_eq_toSubmodule
  given: (s : NonUnitalSubalgebra R A)
  proof: by
  simp [SetLike.ext'_iff, Submodule.coe_span_eq_self]

中文:
引理 span_eq_toSubmodule
  条件: (s : NonUnital子代数 R A)
  证明: by
  simp [SetLike.ext'_iff, Submodule.coe_span_eq_self]

Depends on / 依赖: SetLike, SetLike.ext, Submodule, Submodule.coe_span_eq_self, _iff, coe_span_eq_self
-/
lemma span_eq_toSubmodule (s : NonUnitalSubalgebra R A) :
    Submodule.span R (s : Set A) = s.toSubmodule := by
  simp [SetLike.ext'_iff, Submodule.coe_span_eq_self]

variable [NonUnitalNonAssocSemiring B] [Module R B]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

section IsScalarTower

variable [IsScalarTower R A A] [SMulCommClass R A A]

/--
Definition of `adjoin` / `adjoin` 的定义

English:
definition adjoin
  signature: (s : Set A)
  body: { Submodule.span R (NonUnitalSubsemiring.closure s : Set A) with
    mul_mem' :=
      fun {a b} (ha : a in Submodule.span R (NonUnitalSubsemiring.closure s : Set A))
        (hb : b in Submodule.span R (NonUnitalSubsemiring.closure s : Set A)) =>
      show a * b in Submodule.span R (NonUnitalSubsemiring.closure s : Set A) by
        refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
        · refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
          · exact fun x (hx : x in NonUnitalSubsemiring.closure s) y
              (hy : y in NonUnitalSubsemiring.closure s) => Submodule.subset_span (mul_mem hy hx)
          · exact fun x _hx => (mul_zero x).symm ▸ Submodule.zero_mem _
          · exact fun x y _ _ hx hy z hz => (mul_add z x y).symm ▸ add_mem (hx z hz) (hy z hz)
          · exact fun r x _ hx y hy =>
              (mul_smul_comm r y x).symm ▸ SMulMemClass.smul_mem r (hx y hy)
        · exact (zero_mul b).symm ▸ Submodule.zero_mem _
        · exact fun x y _ _ => (add_mul x y b).symm ▸ add_mem
        · exact fun r x _ hx => (smul_mul_assoc r x b).symm ▸ SMulMemClass.smul_mem r hx }

中文:
定义 adjoin
  签名: (s : 集合 A)
  定义体: { Submodule.span R (NonUnitalSubsemiring.closure s : Set A) with
    mul_mem' :=
      fun {a b} (ha : a in Submodule.span R (NonUnitalSubsemiring.closure s : Set A))
        (hb : b in Submodule.span R (NonUnitalSubsemiring.closure s : Set A)) =>
      show a * b in Submodule.span R (NonUnitalSubsemiring.closure s : Set A) by
        refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
        · refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
          · exact fun x (hx : x in NonUnitalSubsemiring.closure s) y
              (hy : y in NonUnitalSubsemiring.closure s) => Submodule.subset_span (mul_mem hy hx)
          · exact fun x _hx => (mul_zero x).symm ▸ Submodule.zero_mem _
          · exact fun x y _ _ hx hy z hz => (mul_add z x y).symm ▸ add_mem (hx z hz) (hy z hz)
          · exact fun r x _ hx y hy =>
              (mul_smul_comm r y x).symm ▸ SMulMemClass.smul_mem r (hx y hy)
        · exact (zero_mul b).symm ▸ Submodule.zero_mem _
        · exact fun x y _ _ => (add_mul x y b).symm ▸ add_mem
        · exact fun r x _ hx => (smul_mul_assoc r x b).symm ▸ SMulMemClass.smul_mem r hx }

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.closure, Submodule, Submodule.span, Submodule.span_induction, closure, mul_mem, span_induction
-/
def adjoin (s : Set A) : NonUnitalSubalgebra R A :=
  { Submodule.span R (NonUnitalSubsemiring.closure s : Set A) with
    mul_mem' :=
      fun {a b} (ha : a in Submodule.span R (NonUnitalSubsemiring.closure s : Set A))
        (hb : b in Submodule.span R (NonUnitalSubsemiring.closure s : Set A)) =>
      show a * b in Submodule.span R (NonUnitalSubsemiring.closure s : Set A) by
        refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
        · refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
          · exact fun x (hx : x in NonUnitalSubsemiring.closure s) y
              (hy : y in NonUnitalSubsemiring.closure s) => Submodule.subset_span (mul_mem hy hx)
          · exact fun x _hx => (mul_zero x).symm ▸ Submodule.zero_mem _
          · exact fun x y _ _ hx hy z hz => (mul_add z x y).symm ▸ add_mem (hx z hz) (hy z hz)
          · exact fun r x _ hx y hy =>
              (mul_smul_comm r y x).symm ▸ SMulMemClass.smul_mem r (hx y hy)
        · exact (zero_mul b).symm ▸ Submodule.zero_mem _
        · exact fun x y _ _ => (add_mul x y b).symm ▸ add_mem
        · exact fun r x _ hx => (smul_mul_assoc r x b).symm ▸ SMulMemClass.smul_mem r hx }

/--
theorem `adjoin_toSubmodule` / 定理 `adjoin_toSubmodule`

English:
theorem adjoin_toSubmodule
  given: (s : Set A)
  proof: rfl

@[simp, aesop safe 20 (rule_sets := [SetLike])]

中文:
定理 adjoin_toSubmodule
  条件: (s : 集合 A)
  证明: rfl

@[simp, aesop safe 20 (rule_sets := [SetLike])]
-/
theorem adjoin_toSubmodule (s : Set A) :
    (adjoin R s).toSubmodule = Submodule.span R (NonUnitalSubsemiring.closure s : Set A) :=
  rfl

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/--
theorem `subset_adjoin` / 定理 `subset_adjoin`

English:
theorem subset_adjoin
  given: {s : Set A}
  statement: s subseteq adjoin R s
  proof: NonUnitalSubsemiring.subset_closure.trans Submodule.subset_span

@[aesop 80% (rule_sets := [SetLike])]

中文:
定理 subset_adjoin
  条件: {s : 集合 A}
  结论: s subseteq adjoin R s
  证明: NonUnitalSubsemiring.subset_closure.trans Submodule.subset_span

@[aesop 80% (rule_sets := [SetLike])]

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.subset_closure.trans, Submodule, Submodule.subset_span, subset_closure, subset_span
-/
theorem subset_adjoin {s : Set A} : s subseteq adjoin R s :=
  NonUnitalSubsemiring.subset_closure.trans Submodule.subset_span

@[aesop 80% (rule_sets := [SetLike])]
/--
theorem `mem_adjoin_of_mem` / 定理 `mem_adjoin_of_mem`

English:
theorem mem_adjoin_of_mem
  given: {s : Set A} {x : A} (hx : x in s)
  statement: x in adjoin R s
  proof: subset_adjoin R hx

@[simp]

中文:
定理 mem_adjoin_of_mem
  条件: {s : 集合 A} {x : A} (hx : x in s)
  结论: x in adjoin R s
  证明: subset_adjoin R hx

@[simp]

Depends on / 依赖: subset_adjoin
-/
theorem mem_adjoin_of_mem {s : Set A} {x : A} (hx : x in s) : x in adjoin R s := subset_adjoin R hx

@[simp]
/--
theorem `self_mem_adjoin_singleton` / 定理 `self_mem_adjoin_singleton`

English:
theorem self_mem_adjoin_singleton
  given: (x : A)
  statement: x in adjoin R ({x} : Set A)
  proof: NonUnitalAlgebra.subset_adjoin R (Set.mem_singleton x)

中文:
定理 self_mem_adjoin_singleton
  条件: (x : A)
  结论: x in adjoin R ({x} : 集合 A)
  证明: NonUnitalAlgebra.subset_adjoin R (Set.mem_singleton x)

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.subset_adjoin, Set.mem_singleton, mem_singleton, subset_adjoin
-/
theorem self_mem_adjoin_singleton (x : A) : x in adjoin R ({x} : Set A) :=
  NonUnitalAlgebra.subset_adjoin R (Set.mem_singleton x)

variable {R}

/--
theorem `gc` / 定理 `gc`

English:
theorem gc
  statement: GaloisConnection (adjoin R : Set A -> NonUnitalSubalgebra R A) (↑)
  proof: fun s S =>
  ⟨fun H => (NonUnitalSubsemiring.subset_closure.trans Submodule.subset_span).trans H,
fun H => show Submodule.span R _ <= S.toSubmodule from Submodule.span_le.mpr
      show NonUnitalSubsemiring.closure s <= S.toNonUnitalSubsemiring from
        NonUnitalSubsemiring.closure_le.2 H⟩

中文:
定理 gc
  结论: GaloisConnection (adjoin R : 集合 A -> NonUnital子代数 R A) (↑)
  证明: fun s S =>
  ⟨fun H => (NonUnitalSubsemiring.subset_closure.trans Submodule.subset_span).trans H,
fun H => show Submodule.span R _ <= S.toSubmodule from Submodule.span_le.mpr
      show NonUnitalSubsemiring.closure s <= S.toNonUnitalSubsemiring from
        NonUnitalSubsemiring.closure_le.2 H⟩
-/
protected theorem gc : GaloisConnection (adjoin R : Set A -> NonUnitalSubalgebra R A) (↑) :=
  fun s S =>
  ⟨fun H => (NonUnitalSubsemiring.subset_closure.trans Submodule.subset_span).trans H,
fun H => show Submodule.span R _ <= S.toSubmodule from Submodule.span_le.mpr
      show NonUnitalSubsemiring.closure s <= S.toNonUnitalSubsemiring from
        NonUnitalSubsemiring.closure_le.2 H⟩

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (adjoin R : Set A -> NonUnitalSubalgebra R A) (↑) where
  body: (adjoin R s).copy s le_antisymm (NonUnitalAlgebra.gc.le_u_l s) hs
  gc := NonUnitalAlgebra.gc
le_l_u S := (NonUnitalAlgebra.gc (S : Set A) (adjoin R S)).1 le_rfl
  choice_eq _ _ := NonUnitalSubalgebra.copy_eq _ _ _

中文:
定义 gi
  签名: : Galois嵌入 (adjoin R : 集合 A -> NonUnital子代数 R A) (↑) where
  定义体: (adjoin R s).copy s le_antisymm (NonUnitalAlgebra.gc.le_u_l s) hs
  gc := NonUnitalAlgebra.gc
le_l_u S := (NonUnitalAlgebra.gc (S : Set A) (adjoin R S)).1 le_rfl
  choice_eq _ _ := NonUnitalSubalgebra.copy_eq _ _ _
-/
protected def gi : GaloisInsertion (adjoin R : Set A -> NonUnitalSubalgebra R A) (↑) where
choice s hs := (adjoin R s).copy s le_antisymm (NonUnitalAlgebra.gc.le_u_l s) hs
  gc := NonUnitalAlgebra.gc
le_l_u S := (NonUnitalAlgebra.gc (S : Set A) (adjoin R S)).1 le_rfl
  choice_eq _ _ := NonUnitalSubalgebra.copy_eq _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (NonUnitalSubalgebra R A)
  body: GaloisInsertion.liftCompleteLattice NonUnitalAlgebra.gi

中文:
实例 :
  签名: 完备格 (NonUnital子代数 R A)
  定义体: GaloisInsertion.liftCompleteLattice NonUnitalAlgebra.gi

Depends on / 依赖: GaloisInsertion, GaloisInsertion.liftCompleteLattice, NonUnitalAlgebra, NonUnitalAlgebra.gi, liftCompleteLattice
-/
instance : CompleteLattice (NonUnitalSubalgebra R A) :=
  GaloisInsertion.liftCompleteLattice NonUnitalAlgebra.gi

/--
theorem `adjoin_le` / 定理 `adjoin_le`

English:
theorem adjoin_le
  given: {S : NonUnitalSubalgebra R A} {s : Set A} (hs : s subseteq S)
  statement: adjoin R s <= S
  proof: NonUnitalAlgebra.gc.l_le hs

@[simp]

中文:
定理 adjoin_le
  条件: {S : NonUnital子代数 R A} {s : 集合 A} (hs : s subseteq S)
  结论: adjoin R s <= S
  证明: NonUnitalAlgebra.gc.l_le hs

@[simp]

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.gc.l_le, l_le
-/
theorem adjoin_le {S : NonUnitalSubalgebra R A} {s : Set A} (hs : s subseteq S) : adjoin R s <= S :=
  NonUnitalAlgebra.gc.l_le hs

@[simp]
/--
theorem `adjoin_le_iff` / 定理 `adjoin_le_iff`

English:
theorem adjoin_le_iff
  given: {S : NonUnitalSubalgebra R A} {s : Set A}
  statement: adjoin R s <= S ↔ s subseteq S
  proof: NonUnitalAlgebra.gc _ _

@[gcongr]

中文:
定理 adjoin_le_iff
  条件: {S : NonUnital子代数 R A} {s : 集合 A}
  结论: adjoin R s <= S ↔ s subseteq S
  证明: NonUnitalAlgebra.gc _ _

@[gcongr]

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.gc
-/
theorem adjoin_le_iff {S : NonUnitalSubalgebra R A} {s : Set A} : adjoin R s <= S ↔ s subseteq S :=
  NonUnitalAlgebra.gc _ _

@[gcongr]
/--
theorem `adjoin_mono` / 定理 `adjoin_mono`

English:
theorem adjoin_mono
  given: {s t : Set A} (H : s subseteq t)
  statement: adjoin R s <= adjoin R t
  proof: NonUnitalAlgebra.gc.monotone_l H

中文:
定理 adjoin_mono
  条件: {s t : 集合 A} (H : s subseteq t)
  结论: adjoin R s <= adjoin R t
  证明: NonUnitalAlgebra.gc.monotone_l H

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.gc.monotone_l, monotone_l
-/
theorem adjoin_mono {s t : Set A} (H : s subseteq t) : adjoin R s <= adjoin R t :=
  NonUnitalAlgebra.gc.monotone_l H

/--
theorem `adjoin_union` / 定理 `adjoin_union`

English:
theorem adjoin_union
  given: (s t : Set A)
  statement: adjoin R (s union t) = adjoin R s ⊔ adjoin R t
  proof: (NonUnitalAlgebra.gc : GaloisConnection _ ((↑) : NonUnitalSubalgebra R A -> Set A)).l_sup

@[simp]

中文:
定理 adjoin_union
  条件: (s t : 集合 A)
  结论: adjoin R (s union t) = adjoin R s ⊔ adjoin R t
  证明: (NonUnitalAlgebra.gc : GaloisConnection _ ((↑) : NonUnitalSubalgebra R A -> Set A)).l_sup

@[simp]

Depends on / 依赖: GaloisConnection, NonUnitalAlgebra, NonUnitalAlgebra.gc, NonUnitalSubalgebra, l_sup
-/
theorem adjoin_union (s t : Set A) : adjoin R (s union t) = adjoin R s ⊔ adjoin R t :=
  (NonUnitalAlgebra.gc : GaloisConnection _ ((↑) : NonUnitalSubalgebra R A -> Set A)).l_sup

@[simp]
/--
lemma `adjoin_eq` / 引理 `adjoin_eq`

English:
lemma adjoin_eq
  given: (s : NonUnitalSubalgebra R A)
  statement: adjoin R (s : Set A) = s
  proof: le_antisymm (adjoin_le le_rfl) (subset_adjoin R)

中文:
引理 adjoin_eq
  条件: (s : NonUnital子代数 R A)
  结论: adjoin R (s : 集合 A) = s
  证明: le_antisymm (adjoin_le le_rfl) (subset_adjoin R)

Depends on / 依赖: adjoin_le, le_antisymm, le_rfl, subset_adjoin
-/
lemma adjoin_eq (s : NonUnitalSubalgebra R A) : adjoin R (s : Set A) = s :=
  le_antisymm (adjoin_le le_rfl) (subset_adjoin R)

/-- If some predicate holds for all `x ∈ (s : Set A)` and this predicate is closed under the
`algebraMap`, addition, multiplication and star operations, then it holds for `a ∈ adjoin R s`. -/
@[elab_as_elim]
/--
theorem `adjoin_induction` / 定理 `adjoin_induction`

English:
theorem adjoin_induction
  statement: {s : Set A} {p : (x : A) -> x in adjoin R s -> Prop}
  proof: let S : NonUnitalSubalgebra R A :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := (Exists.elim · fun _ ha => (Exists.elim · fun _ hb => ⟨_, mul _ _ _ _ ha hb⟩))
      add_mem' := (Exists.elim · fun _ ha => (Exists.elim · fun _ hb => ⟨_, add _ _ _ _ ha hb⟩))
      smul_mem' := fun r => (Exists.elim · fun _ hb => ⟨_, smul r _ _ hb⟩)
      zero_mem' := ⟨_, zero⟩ }
.elim fun _ => id adjoin_le (S := S) (fun y hy => ⟨subset_adjoin R hy, mem y hy⟩) hx

@[elab_as_elim]

中文:
定理 adjoin_induction
  结论: {s : 集合 A} {p : (x : A) -> x in adjoin R s -> 命题}
  证明: let S : NonUnitalSubalgebra R A :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := (Exists.elim · fun _ ha => (Exists.elim · fun _ hb => ⟨_, mul _ _ _ _ ha hb⟩))
      add_mem' := (Exists.elim · fun _ ha => (Exists.elim · fun _ hb => ⟨_, add _ _ _ _ ha hb⟩))
      smul_mem' := fun r => (Exists.elim · fun _ hb => ⟨_, smul r _ _ hb⟩)
      zero_mem' := ⟨_, zero⟩ }
.elim fun _ => id adjoin_le (S := S) (fun y hy => ⟨subset_adjoin R hy, mem y hy⟩) hx

@[elab_as_elim]

Depends on / 依赖: Exists, Exists.elim, NonUnitalSubalgebra, add_mem, adjoin_le, carrier, mul_mem, smul_mem, subset_adjoin, zero_mem
-/
theorem adjoin_induction {s : Set A} {p : (x : A) -> x in adjoin R s -> Prop}
    (mem : forall (x) (hx : x in s), p x (subset_adjoin R hx))
    (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)) (zero : p 0 (zero_mem _))
    (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy))
    (smul : forall r x hx, p x hx -> p (r • x) (SMulMemClass.smul_mem r hx))
    {x} (hx : x in adjoin R s) : p x hx :=
  let S : NonUnitalSubalgebra R A :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := (Exists.elim · fun _ ha => (Exists.elim · fun _ hb => ⟨_, mul _ _ _ _ ha hb⟩))
      add_mem' := (Exists.elim · fun _ ha => (Exists.elim · fun _ hb => ⟨_, add _ _ _ _ ha hb⟩))
      smul_mem' := fun r => (Exists.elim · fun _ hb => ⟨_, smul r _ _ hb⟩)
      zero_mem' := ⟨_, zero⟩ }
.elim fun _ => id adjoin_le (S := S) (fun y hy => ⟨subset_adjoin R hy, mem y hy⟩) hx

@[elab_as_elim]
/--
theorem `adjoin_induction₂` / 定理 `adjoin_induction₂`

English:
theorem adjoin_induction₂
  statement: {s : Set A} {p : forall x y, x in adjoin R s -> y in adjoin R s -> Prop}
  proof: by
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

中文:
定理 adjoin_induction₂
  结论: {s : 集合 A} {p : 对任意 x y, x in adjoin R s -> y in adjoin R s -> 命题}
  证明: by
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

Depends on / 依赖: add_left, add_right, adjoin_induction, mem_mem, mul_left, mul_right, smul_left, smul_ri, zero_left, zero_right
-/
theorem adjoin_induction₂ {s : Set A} {p : forall x y, x in adjoin R s -> y in adjoin R s -> Prop}
    (mem_mem : forall (x) (y) (hx : x in s) (hy : y in s), p x y (subset_adjoin R hx) (subset_adjoin R hy))
    (zero_left : forall x hx, p 0 x (zero_mem _) hx) (zero_right : forall x hx, p x 0 hx (zero_mem _))
    (add_left : forall x y z hx hy hz, p x z hx hz -> p y z hy hz -> p (x + y) z (add_mem hx hy) hz)
    (add_right : forall x y z hx hy hz, p x y hx hy -> p x z hx hz -> p x (y + z) hx (add_mem hy hz))
    (mul_left : forall x y z hx hy hz, p x z hx hz -> p y z hy hz -> p (x * y) z (mul_mem hx hy) hz)
    (mul_right : forall x y z hx hy hz, p x y hx hy -> p x z hx hz -> p x (y * z) hx (mul_mem hy hz))
    (smul_left : forall r x y hx hy, p x y hx hy -> p (r • x) y (SMulMemClass.smul_mem r hx) hy)
    (smul_right : forall r x y hx hy, p x y hx hy -> p x (r • y) hx (SMulMemClass.smul_mem r hy))
    {x y : A} (hx : x in adjoin R s) (hy : y in adjoin R s) :
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
/--
lemma `adjoin_eq_span` / 引理 `adjoin_eq_span`

English:
lemma adjoin_eq_span
  given: (s : Set A)
  statement: (adjoin R s).toSubmodule = span R (Subsemigroup.closure s)
  proof: by
  apply le_antisymm
  · intro x hx
    induction hx using adjoin_induction with
| mem x hx => exact subset_span Subsemigroup.subset_closure hx
    | add x y _ _ hpx hpy => exact add_mem hpx hpy
    | zero => exact zero_mem _
    | mul x y _ _ hpx hpy =>
      apply span_induction₂ ?Hs (by simp) (by simp) ?Hadd_l ?Hadd_r ?Hsmul_l ?Hsmul_r hpx hpy
case Hs => exact fun x y hx hy => subset_span mul_mem hx hy
      case Hadd_l => exact fun x y z _ _ _ hxz hyz => by simpa [add_mul] using add_mem hxz hyz
      case Hadd_r => exact fun x y z _ _ _ hxz hyz => by simpa [mul_add] using add_mem hxz hyz
      case Hsmul_l => exact fun r x y _ _ hxy => by simpa [smul_mul_assoc] using smul_mem _ _ hxy
      case Hsmul_r => exact fun r x y _ _ hxy => by simpa [mul_smul_comm] using smul_mem _ _ hxy
    | smul r x _ hpx => exact smul_mem _ _ hpx
  · apply span_le.2 _
    change Subsemigroup.closure s <= (adjoin R s).toSubsemigroup
    exact Subsemigroup.closure_le.2 (subset_adjoin R)

中文:
引理 adjoin_eq_span
  条件: (s : 集合 A)
  结论: (adjoin R s).toSubmodule = span R (子半群.closure s)
  证明: by
  apply le_antisymm
  · intro x hx
    induction hx using adjoin_induction with
| mem x hx => exact subset_span Subsemigroup.subset_closure hx
    | add x y _ _ hpx hpy => exact add_mem hpx hpy
    | zero => exact zero_mem _
    | mul x y _ _ hpx hpy =>
      apply span_induction₂ ?Hs (by simp) (by simp) ?Hadd_l ?Hadd_r ?Hsmul_l ?Hsmul_r hpx hpy
case Hs => exact fun x y hx hy => subset_span mul_mem hx hy
      case Hadd_l => exact fun x y z _ _ _ hxz hyz => by simpa [add_mul] using add_mem hxz hyz
      case Hadd_r => exact fun x y z _ _ _ hxz hyz => by simpa [mul_add] using add_mem hxz hyz
      case Hsmul_l => exact fun r x y _ _ hxy => by simpa [smul_mul_assoc] using smul_mem _ _ hxy
      case Hsmul_r => exact fun r x y _ _ hxy => by simpa [mul_smul_comm] using smul_mem _ _ hxy
    | smul r x _ hpx => exact smul_mem _ _ hpx
  · apply span_le.2 _
    change Subsemigroup.closure s <= (adjoin R s).toSubsemigroup
    exact Subsemigroup.closure_le.2 (subset_adjoin R)

Depends on / 依赖: Hadd_l, Hadd_r, Hsmul_l, Hsmul_r, Subsemigroup, Subsemigroup.subset_closure, add_mem, add_mul, adjoin_induction, le_antisymm, mul_mem, subset_closure, subset_span, zero_mem
-/
lemma adjoin_eq_span (s : Set A) : (adjoin R s).toSubmodule = span R (Subsemigroup.closure s) := by
  apply le_antisymm
  · intro x hx
    induction hx using adjoin_induction with
| mem x hx => exact subset_span Subsemigroup.subset_closure hx
    | add x y _ _ hpx hpy => exact add_mem hpx hpy
    | zero => exact zero_mem _
    | mul x y _ _ hpx hpy =>
      apply span_induction₂ ?Hs (by simp) (by simp) ?Hadd_l ?Hadd_r ?Hsmul_l ?Hsmul_r hpx hpy
case Hs => exact fun x y hx hy => subset_span mul_mem hx hy
      case Hadd_l => exact fun x y z _ _ _ hxz hyz => by simpa [add_mul] using add_mem hxz hyz
      case Hadd_r => exact fun x y z _ _ _ hxz hyz => by simpa [mul_add] using add_mem hxz hyz
      case Hsmul_l => exact fun r x y _ _ hxy => by simpa [smul_mul_assoc] using smul_mem _ _ hxy
      case Hsmul_r => exact fun r x y _ _ hxy => by simpa [mul_smul_comm] using smul_mem _ _ hxy
    | smul r x _ hpx => exact smul_mem _ _ hpx
  · apply span_le.2 _
    change Subsemigroup.closure s <= (adjoin R s).toSubsemigroup
    exact Subsemigroup.closure_le.2 (subset_adjoin R)

variable (R A)

@[simp]
/--
theorem `adjoin_empty` / 定理 `adjoin_empty`

English:
theorem adjoin_empty
  statement: adjoin R (∅ : Set A) = ⊥
  proof: show adjoin R ⊥ = ⊥ by apply GaloisConnection.l_bot; exact NonUnitalAlgebra.gc

@[simp]

中文:
定理 adjoin_empty
  结论: adjoin R (∅ : 集合 A) = ⊥
  证明: show adjoin R ⊥ = ⊥ by apply GaloisConnection.l_bot; exact NonUnitalAlgebra.gc

@[simp]

Depends on / 依赖: GaloisConnection, GaloisConnection.l_bot, NonUnitalAlgebra, NonUnitalAlgebra.gc, adjoin, l_bot
-/
theorem adjoin_empty : adjoin R (∅ : Set A) = ⊥ :=
  show adjoin R ⊥ = ⊥ by apply GaloisConnection.l_bot; exact NonUnitalAlgebra.gc

@[simp]
/--
theorem `adjoin_univ` / 定理 `adjoin_univ`

English:
theorem adjoin_univ
  statement: adjoin R (Set.univ : Set A) = ⊤
  proof: eq_top_iff.2 fun _x hx => subset_adjoin R hx

中文:
定理 adjoin_univ
  结论: adjoin R (集合.univ : 集合 A) = ⊤
  证明: eq_top_iff.2 fun _x hx => subset_adjoin R hx

Depends on / 依赖: eq_top_iff, subset_adjoin
-/
theorem adjoin_univ : adjoin R (Set.univ : Set A) = ⊤ :=
  eq_top_iff.2 fun _x hx => subset_adjoin R hx

open NonUnitalSubalgebra in
/--
lemma `_root_.NonUnitalAlgHom.map_adjoin` / 引理 `_root_.NonUnitalAlgHom.map_adjoin`

English:
lemma _root_.NonUnitalAlgHom.map_adjoin
  statement: [IsScalarTower R B B] [SMulCommClass R B B]
  proof: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) NonUnitalAlgebra.gi.gc
    NonUnitalAlgebra.gi.gc fun _t => rfl

中文:
引理 _root_.非幺Alg态射.map_adjoin
  结论: [标量塔 R B B] [标量交换类 R B B]
  证明: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) NonUnitalAlgebra.gi.gc
    NonUnitalAlgebra.gi.gc fun _t => rfl

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.gi.gc, Set.image_preimage.l_comm_of_u_comm, gc_map_comap, image_preimage, l_comm_of_u_comm
-/
lemma _root_.NonUnitalAlgHom.map_adjoin [IsScalarTower R B B] [SMulCommClass R B B]
    (f : F) (s : Set A) : map f (adjoin R s) = adjoin R (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) NonUnitalAlgebra.gi.gc
    NonUnitalAlgebra.gi.gc fun _t => rfl

open NonUnitalSubalgebra in
@[simp]
/--
lemma `_root_.NonUnitalAlgHom.map_adjoin_singleton` / 引理 `_root_.NonUnitalAlgHom.map_adjoin_singleton`

English:
lemma _root_.NonUnitalAlgHom.map_adjoin_singleton
  statement: [IsScalarTower R B B] [SMulCommClass R B B]
  proof: by
  simp [NonUnitalAlgHom.map_adjoin]

中文:
引理 _root_.非幺Alg态射.map_adjoin_singleton
  结论: [标量塔 R B B] [标量交换类 R B B]
  证明: by
  simp [NonUnitalAlgHom.map_adjoin]

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.map_adjoin, map_adjoin
-/
lemma _root_.NonUnitalAlgHom.map_adjoin_singleton [IsScalarTower R B B] [SMulCommClass R B B]
    (f : F) (x : A) : map f (adjoin R {x}) = adjoin R {f x} := by
  simp [NonUnitalAlgHom.map_adjoin]

variable {R A}

@[simp, norm_cast]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: (↑(⊤ : NonUnitalSubalgebra R A) : Set A) = Set.univ
  proof: rfl

@[simp]

中文:
定理 coe_top
  结论: (↑(⊤ : NonUnital子代数 R A) : 集合 A) = 集合.univ
  证明: rfl

@[simp]
-/
theorem coe_top : (↑(⊤ : NonUnitalSubalgebra R A) : Set A) = Set.univ :=
  rfl

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: {x : A}
  statement: x in (⊤ : NonUnitalSubalgebra R A)
  proof: Set.mem_univ x

@[simp]

中文:
定理 mem_top
  条件: {x : A}
  结论: x in (⊤ : NonUnital子代数 R A)
  证明: Set.mem_univ x

@[simp]

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mem_top {x : A} : x in (⊤ : NonUnitalSubalgebra R A) :=
  Set.mem_univ x

@[simp]
/--
theorem `top_toSubmodule` / 定理 `top_toSubmodule`

English:
theorem top_toSubmodule
  statement: (⊤ : NonUnitalSubalgebra R A).toSubmodule = ⊤
  proof: rfl

@[simp]

中文:
定理 top_toSubmodule
  结论: (⊤ : NonUnital子代数 R A).toSubmodule = ⊤
  证明: rfl

@[simp]
-/
theorem top_toSubmodule : (⊤ : NonUnitalSubalgebra R A).toSubmodule = ⊤ :=
  rfl

@[simp]
/--
theorem `top_toNonUnitalSubsemiring` / 定理 `top_toNonUnitalSubsemiring`

English:
theorem top_toNonUnitalSubsemiring
  statement: (⊤ : NonUnitalSubalgebra R A).toNonUnitalSubsemiring = ⊤
  proof: rfl

@[simp]

中文:
定理 top_toNonUnitalSubsemiring
  结论: (⊤ : NonUnital子代数 R A).toNonUnitalSubsemiring = ⊤
  证明: rfl

@[simp]
-/
theorem top_toNonUnitalSubsemiring : (⊤ : NonUnitalSubalgebra R A).toNonUnitalSubsemiring = ⊤ :=
  rfl

@[simp]
/--
theorem `toNonUnitalSubring_top` / 定理 `toNonUnitalSubring_top`

English:
theorem toNonUnitalSubring_top
  statement: {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  proof: rfl

@[deprecated (since := "2026-01-03")] alias top_toSubring := toNonUnitalSubring_top

中文:
定理 toNonUnitalSubring_top
  结论: {R A : 类型} [交换环 R] [非幺非结合环 A] [模 R A]
  证明: rfl

@[deprecated (since := "2026-01-03")] alias top_toSubring := toNonUnitalSubring_top
-/
theorem toNonUnitalSubring_top {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] :
    (⊤ : NonUnitalSubalgebra R A).toNonUnitalSubring = ⊤ :=
  rfl

@[deprecated (since := "2026-01-03")] alias top_toSubring := toNonUnitalSubring_top

/--
lemma `toNonUnitalSubsemiring_eq_top` / 引理 `toNonUnitalSubsemiring_eq_top`

English:
lemma toNonUnitalSubsemiring_eq_top
  given: {S : NonUnitalSubalgebra R A}
  proof: by simp [← SetLike.coe_set_eq]

中文:
引理 toNonUnitalSubsemiring_eq_top
  条件: {S : NonUnital子代数 R A}
  证明: by simp [← SetLike.coe_set_eq]
-/
@[simp] lemma toNonUnitalSubsemiring_eq_top {S : NonUnitalSubalgebra R A} :
    S.toNonUnitalSubsemiring = ⊤ ↔ S = ⊤ := by simp [← SetLike.coe_set_eq]

-- This lemma isn't simp because `NonUnitalSubalgebra.toSubmodule` is reducible.
/--
lemma `toSubmodule_eq_top` / 引理 `toSubmodule_eq_top`

English:
lemma toSubmodule_eq_top
  given: {S : NonUnitalSubalgebra R A}
  statement: S.toSubmodule = ⊤ ↔ S = ⊤
  proof: by simp

@[simp]

中文:
引理 toSubmodule_eq_top
  条件: {S : NonUnital子代数 R A}
  结论: S.toSubmodule = ⊤ ↔ S = ⊤
  证明: by simp

@[simp]
-/
lemma toSubmodule_eq_top {S : NonUnitalSubalgebra R A} : S.toSubmodule = ⊤ ↔ S = ⊤ := by simp

@[simp]
/--
theorem `toNonUnitalSubring_eq_top` / 定理 `toNonUnitalSubring_eq_top`

English:
theorem toNonUnitalSubring_eq_top
  statement: {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  proof: by
  simp [← SetLike.coe_set_eq]

@[deprecated (since := "2026-01-01")] alias to_subring_eq_top := toNonUnitalSubring_eq_top

中文:
定理 toNonUnitalSubring_eq_top
  结论: {R A : 类型} [交换环 R] [环 A] [代数 R A]
  证明: by
  simp [← SetLike.coe_set_eq]

@[deprecated (since := "2026-01-01")] alias to_subring_eq_top := toNonUnitalSubring_eq_top

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq
-/
theorem toNonUnitalSubring_eq_top {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {S : NonUnitalSubalgebra R A} : S.toNonUnitalSubring = ⊤ ↔ S = ⊤ := by
  simp [← SetLike.coe_set_eq]

@[deprecated (since := "2026-01-01")] alias to_subring_eq_top := toNonUnitalSubring_eq_top

/--
theorem `mem_sup_left` / 定理 `mem_sup_left`

English:
theorem mem_sup_left
  given: {S T : NonUnitalSubalgebra R A}
  statement: forall {x : A}, x in S -> x in S ⊔ T
  proof: by
  rw [← SetLike.le_def]
  exact le_sup_left

中文:
定理 mem_sup_left
  条件: {S T : NonUnital子代数 R A}
  结论: 对任意 {x : A}, x in S -> x in S ⊔ T
  证明: by
  rw [← SetLike.le_def]
  exact le_sup_left

Depends on / 依赖: SetLike, SetLike.le_def, le_def, le_sup_left
-/
theorem mem_sup_left {S T : NonUnitalSubalgebra R A} : forall {x : A}, x in S -> x in S ⊔ T := by
  rw [← SetLike.le_def]
  exact le_sup_left

/--
theorem `mem_sup_right` / 定理 `mem_sup_right`

English:
theorem mem_sup_right
  given: {S T : NonUnitalSubalgebra R A}
  statement: forall {x : A}, x in T -> x in S ⊔ T
  proof: by
  rw [← SetLike.le_def]
  exact le_sup_right

中文:
定理 mem_sup_right
  条件: {S T : NonUnital子代数 R A}
  结论: 对任意 {x : A}, x in T -> x in S ⊔ T
  证明: by
  rw [← SetLike.le_def]
  exact le_sup_right

Depends on / 依赖: SetLike, SetLike.le_def, le_def, le_sup_right
-/
theorem mem_sup_right {S T : NonUnitalSubalgebra R A} : forall {x : A}, x in T -> x in S ⊔ T := by
  rw [← SetLike.le_def]
  exact le_sup_right

/--
theorem `mul_mem_sup` / 定理 `mul_mem_sup`

English:
theorem mul_mem_sup
  given: {S T : NonUnitalSubalgebra R A} {x y : A} (hx : x in S) (hy : y in T)
  proof: mul_mem (mem_sup_left hx) (mem_sup_right hy)

中文:
定理 mul_mem_sup
  条件: {S T : NonUnital子代数 R A} {x y : A} (hx : x in S) (hy : y in T)
  证明: mul_mem (mem_sup_left hx) (mem_sup_right hy)

Depends on / 依赖: mem_sup_left, mem_sup_right, mul_mem
-/
theorem mul_mem_sup {S T : NonUnitalSubalgebra R A} {x y : A} (hx : x in S) (hy : y in T) :
    x * y in S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  statement: [IsScalarTower R B B] [SMulCommClass R B B]
  proof: (NonUnitalSubalgebra.gc_map_comap f).l_sup

中文:
定理 map_sup
  结论: [标量塔 R B B] [标量交换类 R B B]
  证明: (NonUnitalSubalgebra.gc_map_comap f).l_sup

Depends on / 依赖: NonUnitalSubalgebra, NonUnitalSubalgebra.gc_map_comap, gc_map_comap, l_sup
-/
theorem map_sup [IsScalarTower R B B] [SMulCommClass R B B]
    (f : F) (S T : NonUnitalSubalgebra R A) :
    ((S ⊔ T).map f : NonUnitalSubalgebra R B) = S.map f ⊔ T.map f :=
  (NonUnitalSubalgebra.gc_map_comap f).l_sup

/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  statement: [IsScalarTower R B B] [SMulCommClass R B B]
  proof: SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]

中文:
定理 map_inf
  结论: [标量塔 R B B] [标量交换类 R B B]
  证明: SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, image_inter
-/
theorem map_inf [IsScalarTower R B B] [SMulCommClass R B B]
    (f : F) (hf : Function.Injective f) (S T : NonUnitalSubalgebra R A) :
    ((S ⊓ T).map f : NonUnitalSubalgebra R B) = S.map f ⊓ T.map f :=
  SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (S T : NonUnitalSubalgebra R A)
  statement: (↑(S ⊓ T) : Set A) = (S : Set A) inter T
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (S T : NonUnital子代数 R A)
  结论: (↑(S ⊓ T) : 集合 A) = (S : 集合 A) inter T
  证明: rfl

@[simp]
-/
theorem coe_inf (S T : NonUnitalSubalgebra R A) : (↑(S ⊓ T) : Set A) = (S : Set A) inter T :=
  rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {S T : NonUnitalSubalgebra R A} {x : A}
  statement: x in S ⊓ T ↔ x in S ∧ x in T
  proof: Iff.rfl

@[simp]

中文:
定理 mem_inf
  条件: {S T : NonUnital子代数 R A} {x : A}
  结论: x in S ⊓ T ↔ x in S ∧ x in T
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {S T : NonUnitalSubalgebra R A} {x : A} : x in S ⊓ T ↔ x in S ∧ x in T :=
  Iff.rfl

@[simp]
/--
theorem `inf_toSubmodule` / 定理 `inf_toSubmodule`

English:
theorem inf_toSubmodule
  given: (S T : NonUnitalSubalgebra R A)
  proof: rfl

@[simp]

中文:
定理 inf_toSubmodule
  条件: (S T : NonUnital子代数 R A)
  证明: rfl

@[simp]
-/
theorem inf_toSubmodule (S T : NonUnitalSubalgebra R A) :
    (S ⊓ T).toSubmodule = S.toSubmodule ⊓ T.toSubmodule :=
  rfl

@[simp]
/--
theorem `inf_toNonUnitalSubsemiring` / 定理 `inf_toNonUnitalSubsemiring`

English:
theorem inf_toNonUnitalSubsemiring
  given: (S T : NonUnitalSubalgebra R A)
  proof: rfl

@[simp, norm_cast]

中文:
定理 inf_toNonUnitalSubsemiring
  条件: (S T : NonUnital子代数 R A)
  证明: rfl

@[simp, norm_cast]
-/
theorem inf_toNonUnitalSubsemiring (S T : NonUnitalSubalgebra R A) :
    (S ⊓ T).toNonUnitalSubsemiring = S.toNonUnitalSubsemiring ⊓ T.toNonUnitalSubsemiring :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (NonUnitalSubalgebra R A))
  statement: (↑(sInf S) : Set A) = ⋂ s in S, ↑s
  proof: sInf_image

@[simp]

中文:
定理 coe_sInf
  条件: (S : 集合 (NonUnital子代数 R A))
  结论: (↑(sInf S) : 集合 A) = ⋂ s in S, ↑s
  证明: sInf_image

@[simp]

Depends on / 依赖: sInf_image
-/
theorem coe_sInf (S : Set (NonUnitalSubalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s in S, ↑s :=
  sInf_image

@[simp]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (NonUnitalSubalgebra R A)} {x : A}
  statement: x in sInf S ↔ forall p in S, x in p
  proof: by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]

中文:
定理 mem_sInf
  条件: {S : 集合 (NonUnital子代数 R A)} {x : A}
  结论: x in sInf S ↔ 对任意 p in S, x in p
  证明: by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]

Depends on / 依赖: Set.mem_iInter, SetLike, SetLike.mem_coe, coe_sInf, mem_coe
-/
theorem mem_sInf {S : Set (NonUnitalSubalgebra R A)} {x : A} : x in sInf S ↔ forall p in S, x in p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]
/--
theorem `sInf_toSubmodule` / 定理 `sInf_toSubmodule`

English:
theorem sInf_toSubmodule
  given: (S : Set (NonUnitalSubalgebra R A))
  proof: SetLike.coe_injective by simp

@[simp]

中文:
定理 sInf_toSubmodule
  条件: (S : 集合 (NonUnital子代数 R A))
  证明: SetLike.coe_injective by simp

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem sInf_toSubmodule (S : Set (NonUnitalSubalgebra R A)) :
    (sInf S).toSubmodule = sInf (NonUnitalSubalgebra.toSubmodule '' S) :=
SetLike.coe_injective by simp

@[simp]
/--
theorem `sInf_toNonUnitalSubsemiring` / 定理 `sInf_toNonUnitalSubsemiring`

English:
theorem sInf_toNonUnitalSubsemiring
  given: (S : Set (NonUnitalSubalgebra R A))
  proof: SetLike.coe_injective by simp

@[simp, norm_cast]

中文:
定理 sInf_toNonUnitalSubsemiring
  条件: (S : 集合 (NonUnital子代数 R A))
  证明: SetLike.coe_injective by simp

@[simp, norm_cast]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem sInf_toNonUnitalSubsemiring (S : Set (NonUnitalSubalgebra R A)) :
    (sInf S).toNonUnitalSubsemiring = sInf (NonUnitalSubalgebra.toNonUnitalSubsemiring '' S) :=
SetLike.coe_injective by simp

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} {S : ι -> NonUnitalSubalgebra R A}
  proof: by simp [iInf]

@[simp]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} {S : ι -> NonUnital子代数 R A}
  证明: by simp [iInf]

@[simp]
-/
theorem coe_iInf {ι : Sort*} {S : ι -> NonUnitalSubalgebra R A} :
    (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by simp [iInf]

@[simp]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι : Sort*} {S : ι -> NonUnitalSubalgebra R A} {x : A}
  proof: by simp only [iInf, mem_sInf, Set.forall_mem_range]

中文:
定理 mem_iInf
  条件: {ι : 类型层*} {S : ι -> NonUnital子代数 R A} {x : A}
  证明: by simp only [iInf, mem_sInf, Set.forall_mem_range]

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, mem_sInf
-/
theorem mem_iInf {ι : Sort*} {S : ι -> NonUnitalSubalgebra R A} {x : A} :
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
    [IsScalarTower R B B] [SMulCommClass R B B] (f : F)
    (hf : Function.Injective f) (S : ι -> NonUnitalSubalgebra R A) :
    ((⨅ i, S i).map f : NonUnitalSubalgebra R B) = ⨅ i, (S i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ S)

@[simp]
/--
theorem `iInf_toSubmodule` / 定理 `iInf_toSubmodule`

English:
theorem iInf_toSubmodule
  given: {ι : Sort*} (S : ι -> NonUnitalSubalgebra R A)
  proof: SetLike.coe_injective by simp

中文:
定理 iInf_toSubmodule
  条件: {ι : 类型层*} (S : ι -> NonUnital子代数 R A)
  证明: SetLike.coe_injective by simp

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem iInf_toSubmodule {ι : Sort*} (S : ι -> NonUnitalSubalgebra R A) :
    (⨅ i, S i).toSubmodule = ⨅ i, (S i).toSubmodule :=
SetLike.coe_injective by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (NonUnitalSubalgebra R A)
  body: ⟨⊥⟩

中文:
实例 :
  签名: 可居 (NonUnital子代数 R A)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (NonUnitalSubalgebra R A) :=
  ⟨⊥⟩

/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: {x : A}
  statement: x in (⊥ : NonUnitalSubalgebra R A) ↔ x = 0
  proof: show x in Submodule.span R (NonUnitalSubsemiring.closure (∅ : Set A) : Set A) ↔ x = 0 by
    rw [NonUnitalSubsemiring.closure_empty]; rw [NonUnitalSubsemiring.coe_bot]; rw [Submodule.span_zero_singleton]; rw [Submodule.mem_bot]

中文:
定理 mem_bot
  条件: {x : A}
  结论: x in (⊥ : NonUnital子代数 R A) ↔ x = 0
  证明: show x in Submodule.span R (NonUnitalSubsemiring.closure (∅ : Set A) : Set A) ↔ x = 0 by
    rw [NonUnitalSubsemiring.closure_empty]; rw [NonUnitalSubsemiring.coe_bot]; rw [Submodule.span_zero_singleton]; rw [Submodule.mem_bot]

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.closure, NonUnitalSubsemiring.closure_empty, NonUnitalSubsemiring.coe_bot, Submodule, Submodule.mem_bot, Submodule.span, Submodule.span_zero_singleton, closure, closure_empty, coe_bot, mem_bot, span_zero_singleton
-/
theorem mem_bot {x : A} : x in (⊥ : NonUnitalSubalgebra R A) ↔ x = 0 :=
  show x in Submodule.span R (NonUnitalSubsemiring.closure (∅ : Set A) : Set A) ↔ x = 0 by
    rw [NonUnitalSubsemiring.closure_empty]; rw [NonUnitalSubsemiring.coe_bot]; rw [Submodule.span_zero_singleton]; rw [Submodule.mem_bot]

/--
theorem `toSubmodule_bot` / 定理 `toSubmodule_bot`

English:
theorem toSubmodule_bot
  statement: (⊥ : NonUnitalSubalgebra R A).toSubmodule = ⊥
  proof: by
  ext
  simp only [mem_bot, NonUnitalSubalgebra.mem_toSubmodule, Submodule.mem_bot]

@[simp, norm_cast]

中文:
定理 toSubmodule_bot
  结论: (⊥ : NonUnital子代数 R A).toSubmodule = ⊥
  证明: by
  ext
  simp only [mem_bot, NonUnitalSubalgebra.mem_toSubmodule, Submodule.mem_bot]

@[simp, norm_cast]

Depends on / 依赖: NonUnitalSubalgebra, NonUnitalSubalgebra.mem_toSubmodule, Submodule, Submodule.mem_bot, mem_bot, mem_toSubmodule
-/
theorem toSubmodule_bot : (⊥ : NonUnitalSubalgebra R A).toSubmodule = ⊥ := by
  ext
  simp only [mem_bot, NonUnitalSubalgebra.mem_toSubmodule, Submodule.mem_bot]

@[simp, norm_cast]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : NonUnitalSubalgebra R A) : Set A) = {0}
  proof: by
  simp [Set.ext_iff, NonUnitalAlgebra.mem_bot]

中文:
定理 coe_bot
  结论: ((⊥ : NonUnital子代数 R A) : 集合 A) = {0}
  证明: by
  simp [Set.ext_iff, NonUnitalAlgebra.mem_bot]

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.mem_bot, Set.ext_iff, ext_iff, mem_bot
-/
theorem coe_bot : ((⊥ : NonUnitalSubalgebra R A) : Set A) = {0} := by
  simp [Set.ext_iff, NonUnitalAlgebra.mem_bot]

/--
theorem `eq_top_iff` / 定理 `eq_top_iff`

English:
theorem eq_top_iff
  given: {S : NonUnitalSubalgebra R A}
  statement: S = ⊤ ↔ forall x : A, x in S
  proof: ⟨fun h x => by rw [h]; exact mem_top, fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

@[simp]

中文:
定理 eq_top_iff
  条件: {S : NonUnital子代数 R A}
  结论: S = ⊤ ↔ 对任意 x : A, x in S
  证明: ⟨fun h x => by rw [h]; exact mem_top, fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

@[simp]

Depends on / 依赖: mem_top
-/
theorem eq_top_iff {S : NonUnitalSubalgebra R A} : S = ⊤ ↔ forall x : A, x in S :=
  ⟨fun h x => by rw [h]; exact mem_top, fun h => by ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

@[simp]
/--
theorem `range_id` / 定理 `range_id`

English:
theorem range_id
  statement: NonUnitalAlgHom.range (NonUnitalAlgHom.id R A) = ⊤
  proof: SetLike.coe_injective Set.range_id

@[simp]

中文:
定理 range_id
  结论: 非幺Alg态射.range (非幺Alg态射.id R A) = ⊤
  证明: SetLike.coe_injective Set.range_id

@[simp]

Depends on / 依赖: Set.range_id, SetLike, SetLike.coe_injective, coe_injective, range_id
-/
theorem range_id : NonUnitalAlgHom.range (NonUnitalAlgHom.id R A) = ⊤ :=
  SetLike.coe_injective Set.range_id

@[simp]
/--
theorem `map_top` / 定理 `map_top`

English:
theorem map_top
  given: (f : A ->ₙₐ[R] B)
  statement: (⊤ : NonUnitalSubalgebra R A).map f = NonUnitalAlgHom.range f
  proof: SetLike.coe_injective Set.image_univ

@[simp]

中文:
定理 map_top
  条件: (f : A ->ₙₐ[R] B)
  结论: (⊤ : NonUnital子代数 R A).map f = 非幺Alg态射.range f
  证明: SetLike.coe_injective Set.image_univ

@[simp]

Depends on / 依赖: Set.image_univ, SetLike, SetLike.coe_injective, coe_injective, image_univ
-/
theorem map_top (f : A ->ₙₐ[R] B) : (⊤ : NonUnitalSubalgebra R A).map f = NonUnitalAlgHom.range f :=
  SetLike.coe_injective Set.image_univ

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  statement: [IsScalarTower R B B] [SMulCommClass R B B]
  proof: SetLike.coe_injective by simp [NonUnitalAlgebra.coe_bot, NonUnitalSubalgebra.coe_map]

@[simp]

中文:
定理 map_bot
  结论: [标量塔 R B B] [标量交换类 R B B]
  证明: SetLike.coe_injective by simp [NonUnitalAlgebra.coe_bot, NonUnitalSubalgebra.coe_map]

@[simp]

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.coe_bot, NonUnitalSubalgebra, NonUnitalSubalgebra.coe_map, SetLike, SetLike.coe_injective, coe_bot, coe_injective, coe_map
-/
theorem map_bot [IsScalarTower R B B] [SMulCommClass R B B]
    (f : A ->ₙₐ[R] B) : (⊥ : NonUnitalSubalgebra R A).map f = ⊥ :=
SetLike.coe_injective by simp [NonUnitalAlgebra.coe_bot, NonUnitalSubalgebra.coe_map]

@[simp]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  statement: [IsScalarTower R B B] [SMulCommClass R B B]
  proof: eq_top_iff.2 fun _ => mem_top

中文:
定理 comap_top
  结论: [标量塔 R B B] [标量交换类 R B B]
  证明: eq_top_iff.2 fun _ => mem_top

Depends on / 依赖: eq_top_iff, mem_top
-/
theorem comap_top [IsScalarTower R B B] [SMulCommClass R B B]
    (f : A ->ₙₐ[R] B) : (⊤ : NonUnitalSubalgebra R B).comap f = ⊤ :=
  eq_top_iff.2 fun _ => mem_top

/--
Definition of `toTop` / `toTop` 的定义

English:
definition toTop
  signature: : A ->ₙₐ[R] (⊤ : NonUnitalSubalgebra R A)
  body: NonUnitalAlgHom.codRestrict (NonUnitalAlgHom.id R A) ⊤ fun _ => mem_top

中文:
定义 toTop
  签名: : A ->ₙₐ[R] (⊤ : NonUnital子代数 R A)
  定义体: NonUnitalAlgHom.codRestrict (NonUnitalAlgHom.id R A) ⊤ fun _ => mem_top

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.codRestrict, NonUnitalAlgHom.id, codRestrict, mem_top
-/
def toTop : A ->ₙₐ[R] (⊤ : NonUnitalSubalgebra R A) :=
  NonUnitalAlgHom.codRestrict (NonUnitalAlgHom.id R A) ⊤ fun _ => mem_top

end IsScalarTower

/--
theorem `range_eq_top` / 定理 `range_eq_top`

English:
theorem range_eq_top
  given: [IsScalarTower R B B] [SMulCommClass R B B] (f : A ->ₙₐ[R] B)
  proof: NonUnitalAlgebra.eq_top_iff

中文:
定理 range_eq_top
  条件: [标量塔 R B B] [标量交换类 R B B] (f : A ->ₙₐ[R] B)
  证明: NonUnitalAlgebra.eq_top_iff

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.eq_top_iff, eq_top_iff
-/
theorem range_eq_top [IsScalarTower R B B] [SMulCommClass R B B] (f : A ->ₙₐ[R] B) :
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

/--
theorem `range_val` / 定理 `range_val`

English:
theorem range_val
  statement: NonUnitalAlgHom.range (NonUnitalSubalgebraClass.subtype S) = S
  proof: ext Set.ext_iff.1
    (NonUnitalAlgHom.coe_range <| NonUnitalSubalgebraClass.subtype S).trans Subtype.range_val

中文:
定理 range_val
  结论: 非幺Alg态射.range (NonUnitalSubalgebraClass.subtype S) = S
  证明: ext Set.ext_iff.1
    (NonUnitalAlgHom.coe_range <| NonUnitalSubalgebraClass.subtype S).trans Subtype.range_val

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.coe_range, NonUnitalSubalgebraClass, NonUnitalSubalgebraClass.subtype, Set.ext_iff, Subtype, Subtype.range_val, coe_range, ext_iff, range_val, subtype
-/
theorem range_val : NonUnitalAlgHom.range (NonUnitalSubalgebraClass.subtype S) = S :=
ext Set.ext_iff.1
    (NonUnitalAlgHom.coe_range <| NonUnitalSubalgebraClass.subtype S).trans Subtype.range_val

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
instance subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (NonUnitalSubalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩

variable [NonUnitalNonAssocSemiring B] [Module R B]

section Prod

variable (S₁ : NonUnitalSubalgebra R B)

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : NonUnitalSubalgebra R (A × B)
  body: { S.toNonUnitalSubsemiring.prod S₁.toNonUnitalSubsemiring with
    carrier := S ×ˢ S₁
    smul_mem' := fun r _x hx => ⟨SMulMemClass.smul_mem r hx.1, SMulMemClass.smul_mem r hx.2⟩ }

@[simp, norm_cast]

中文:
定义 乘积
  签名: : NonUnital子代数 R (A × B)
  定义体: { S.toNonUnitalSubsemiring.prod S₁.toNonUnitalSubsemiring with
    carrier := S ×ˢ S₁
    smul_mem' := fun r _x hx => ⟨SMulMemClass.smul_mem r hx.1, SMulMemClass.smul_mem r hx.2⟩ }

@[simp, norm_cast]

Depends on / 依赖: S.toNonUnitalSubsemiring.prod, SMulMemClass, SMulMemClass.smul_mem, carrier, smul_mem, toNonUnitalSubsemiring
-/
def prod : NonUnitalSubalgebra R (A × B) :=
  { S.toNonUnitalSubsemiring.prod S₁.toNonUnitalSubsemiring with
    carrier := S ×ˢ S₁
    smul_mem' := fun r _x hx => ⟨SMulMemClass.smul_mem r hx.1, SMulMemClass.smul_mem r hx.2⟩ }

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
theorem `prod_toSubmodule` / 定理 `prod_toSubmodule`

English:
theorem prod_toSubmodule
  statement: (S.prod S₁).toSubmodule = S.toSubmodule.prod S₁.toSubmodule
  proof: rfl

@[simp]

中文:
定理 prod_toSubmodule
  结论: (S.乘积 S₁).toSubmodule = S.toSubmodule.乘积 S₁.toSubmodule
  证明: rfl

@[simp]
-/
theorem prod_toSubmodule : (S.prod S₁).toSubmodule = S.toSubmodule.prod S₁.toSubmodule :=
  rfl

@[simp]
/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {S : NonUnitalSubalgebra R A} {S₁ : NonUnitalSubalgebra R B} {x : A × B}
  proof: Set.mem_prod

中文:
定理 mem_prod
  条件: {S : NonUnital子代数 R A} {S₁ : NonUnital子代数 R B} {x : A × B}
  证明: Set.mem_prod

Depends on / 依赖: Set.mem_prod, mem_prod
-/
theorem mem_prod {S : NonUnitalSubalgebra R A} {S₁ : NonUnitalSubalgebra R B} {x : A × B} :
    x in prod S S₁ ↔ x.1 in S ∧ x.2 in S₁ :=
  Set.mem_prod

/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: {S T : NonUnitalSubalgebra R A} {S₁ T₁ : NonUnitalSubalgebra R B}
  proof: Set.prod_mono

中文:
定理 prod_mono
  条件: {S T : NonUnital子代数 R A} {S₁ T₁ : NonUnital子代数 R B}
  证明: Set.prod_mono

Depends on / 依赖: Set.prod_mono, prod_mono
-/
theorem prod_mono {S T : NonUnitalSubalgebra R A} {S₁ T₁ : NonUnitalSubalgebra R B} :
    S <= T -> S₁ <= T₁ -> prod S S₁ <= prod T T₁ :=
  Set.prod_mono

variable [IsScalarTower R A A] [SMulCommClass R A A] [IsScalarTower R B B] [SMulCommClass R B B]

@[simp]
/--
theorem `prod_top` / 定理 `prod_top`

English:
theorem prod_top
  statement: (prod ⊤ ⊤ : NonUnitalSubalgebra R (A × B)) = ⊤
  proof: by ext; simp

@[simp]

中文:
定理 prod_top
  结论: (乘积 ⊤ ⊤ : NonUnital子代数 R (A × B)) = ⊤
  证明: by ext; simp

@[simp]
-/
theorem prod_top : (prod ⊤ ⊤ : NonUnitalSubalgebra R (A × B)) = ⊤ := by ext; simp

@[simp]
/--
theorem `prod_inf_prod` / 定理 `prod_inf_prod`

English:
theorem prod_inf_prod
  given: {S T : NonUnitalSubalgebra R A} {S₁ T₁ : NonUnitalSubalgebra R B}
  proof: SetLike.coe_injective Set.prod_inter_prod

中文:
定理 prod_inf_prod
  条件: {S T : NonUnital子代数 R A} {S₁ T₁ : NonUnital子代数 R B}
  证明: SetLike.coe_injective Set.prod_inter_prod

Depends on / 依赖: Set.prod_inter_prod, SetLike, SetLike.coe_injective, coe_injective, prod_inter_prod
-/
theorem prod_inf_prod {S T : NonUnitalSubalgebra R A} {S₁ T₁ : NonUnitalSubalgebra R B} :
    S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
  SetLike.coe_injective Set.prod_inter_prod

end Prod


/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {S T : NonUnitalSubalgebra R A} (h : S <= T)
  body: Set.inclusion h
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_smul' _ _ := rfl

中文:
定义 inclusion
  签名: {S T : NonUnital子代数 R A} (h : S <= T)
  定义体: Set.inclusion h
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: Set.inclusion, inclusion
-/
def inclusion {S T : NonUnitalSubalgebra R A} (h : S <= T) : S ->ₙₐ[R] T where
  toFun := Set.inclusion h
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_smul' _ _ := rfl

/--
theorem `inclusion_injective` / 定理 `inclusion_injective`

English:
theorem inclusion_injective
  given: {S T : NonUnitalSubalgebra R A} (h : S <= T)
  proof: fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]

中文:
定理 inclusion_injective
  条件: {S T : NonUnital子代数 R A} (h : S <= T)
  证明: fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, Subtype.mk.inj
-/
theorem inclusion_injective {S T : NonUnitalSubalgebra R A} (h : S <= T) :
    Function.Injective (inclusion h) := fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]
/--
theorem `inclusion_self` / 定理 `inclusion_self`

English:
theorem inclusion_self
  given: {S : NonUnitalSubalgebra R A}
  proof: rfl

@[simp]

中文:
定理 inclusion_self
  条件: {S : NonUnital子代数 R A}
  证明: rfl

@[simp]
-/
theorem inclusion_self {S : NonUnitalSubalgebra R A} :
    inclusion (le_refl S) = NonUnitalAlgHom.id R S :=
  rfl

@[simp]
/--
theorem `inclusion_mk` / 定理 `inclusion_mk`

English:
theorem inclusion_mk
  given: {S T : NonUnitalSubalgebra R A} (h : S <= T) (x : A) (hx : x in S)
  proof: rfl

中文:
定理 inclusion_mk
  条件: {S T : NonUnital子代数 R A} (h : S <= T) (x : A) (hx : x in S)
  证明: rfl
-/
theorem inclusion_mk {S T : NonUnitalSubalgebra R A} (h : S <= T) (x : A) (hx : x in S) :
    inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl

/--
theorem `inclusion_right` / 定理 `inclusion_right`

English:
theorem inclusion_right
  given: {S T : NonUnitalSubalgebra R A} (h : S <= T) (x : T) (m : (x : A) in S)
  proof: Subtype.ext rfl

@[simp]

中文:
定理 inclusion_right
  条件: {S T : NonUnital子代数 R A} (h : S <= T) (x : T) (m : (x : A) in S)
  证明: Subtype.ext rfl

@[simp]

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem inclusion_right {S T : NonUnitalSubalgebra R A} (h : S <= T) (x : T) (m : (x : A) in S) :
    inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl

@[simp]
/--
theorem `inclusion_inclusion` / 定理 `inclusion_inclusion`

English:
theorem inclusion_inclusion
  given: {S T U : NonUnitalSubalgebra R A} (hst : S <= T) (htu : T <= U) (x : S)
  proof: Subtype.ext rfl

@[simp]

中文:
定理 inclusion_inclusion
  条件: {S T U : NonUnital子代数 R A} (hst : S <= T) (htu : T <= U) (x : S)
  证明: Subtype.ext rfl

@[simp]

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem inclusion_inclusion {S T U : NonUnitalSubalgebra R A} (hst : S <= T) (htu : T <= U) (x : S) :
    inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
  Subtype.ext rfl

@[simp]
/--
theorem `coe_inclusion` / 定理 `coe_inclusion`

English:
theorem coe_inclusion
  given: {S T : NonUnitalSubalgebra R A} (h : S <= T) (s : S)
  proof: rfl

中文:
定理 coe_inclusion
  条件: {S T : NonUnital子代数 R A} (h : S <= T) (s : S)
  证明: rfl
-/
theorem coe_inclusion {S T : NonUnitalSubalgebra R A} (h : S <= T) (s : S) :
    (inclusion h s : A) = s :=
  rfl

variable [IsScalarTower R A A] [SMulCommClass R A A]

/--
Instance `_root_.NonUnitalAlgHom.subsingleton` / 实例 `_root_.NonUnitalAlgHom.subsingleton`

English:
instance _root_.NonUnitalAlgHom.subsingleton
  signature: [Subsingleton (NonUnitalSubalgebra R A)]
  body: ⟨fun f g =>
    NonUnitalAlgHom.ext fun a =>
      have : a in (⊥ : NonUnitalSubalgebra R A) :=
        Subsingleton.elim (⊤ : NonUnitalSubalgebra R A) ⊥ ▸ mem_top
      (mem_bot.mp this).symm ▸ (map_zero f).trans (map_zero g).symm⟩

中文:
实例 _root_.非幺Alg态射.subsingleton
  签名: [子单例 (NonUnital子代数 R A)]
  定义体: ⟨fun f g =>
    NonUnitalAlgHom.ext fun a =>
      have : a in (⊥ : NonUnitalSubalgebra R A) :=
        Subsingleton.elim (⊤ : NonUnitalSubalgebra R A) ⊥ ▸ mem_top
      (mem_bot.mp this).symm ▸ (map_zero f).trans (map_zero g).symm⟩

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.ext, NonUnitalSubalgebra, Subsingleton, Subsingleton.elim, map_zero, mem_bot, mem_bot.mp, mem_top
-/
instance _root_.NonUnitalAlgHom.subsingleton [Subsingleton (NonUnitalSubalgebra R A)] :
    Subsingleton (A ->ₙₐ[R] B) :=
  ⟨fun f g =>
    NonUnitalAlgHom.ext fun a =>
      have : a in (⊥ : NonUnitalSubalgebra R A) :=
        Subsingleton.elim (⊤ : NonUnitalSubalgebra R A) ⊥ ▸ mem_top
      (mem_bot.mp this).symm ▸ (map_zero f).trans (map_zero g).symm⟩

section SuprLift

variable {ι : Sort*}

/--
theorem `coe_iSup_of_directed` / 定理 `coe_iSup_of_directed`

English:
theorem coe_iSup_of_directed
  statement: [Nonempty ι] {S : ι -> NonUnitalSubalgebra R A}
  proof: let K : NonUnitalSubalgebra R A :=
    { __ := NonUnitalSubsemiring.copy _ _ (NonUnitalSubsemiring.coe_iSup_of_directed dir).symm
      smul_mem' := fun r _x hx =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, (S i).smul_mem' r hi⟩ }
  have : iSup S = K := le_antisymm
    (iSup_le fun i => le_iSup (fun i => (S i : Set A)) i) (Set.iUnion_subset fun _ => le_iSup S _)
  this.symm ▸ rfl

中文:
定理 coe_iSup_of_directed
  结论: [非空 ι] {S : ι -> NonUnital子代数 R A}
  证明: let K : NonUnitalSubalgebra R A :=
    { __ := NonUnitalSubsemiring.copy _ _ (NonUnitalSubsemiring.coe_iSup_of_directed dir).symm
      smul_mem' := fun r _x hx =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, (S i).smul_mem' r hi⟩ }
  have : iSup S = K := le_antisymm
    (iSup_le fun i => le_iSup (fun i => (S i : Set A)) i) (Set.iUnion_subset fun _ => le_iSup S _)
  this.symm ▸ rfl

Depends on / 依赖: NonUnitalSubalgebra, NonUnitalSubsemiring, NonUnitalSubsemiring.coe_iSup_of_directed, NonUnitalSubsemiring.copy, Set.iUnion_subset, Set.mem_iUnion, coe_iSup_of_directed, iSup_le, iUnion_subset, le_antisymm, le_iSup, mem_iUnion, smul_mem, this.symm
-/
theorem coe_iSup_of_directed [Nonempty ι] {S : ι -> NonUnitalSubalgebra R A}
    (dir : Directed (· <= ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A) :=
  let K : NonUnitalSubalgebra R A :=
    { __ := NonUnitalSubsemiring.copy _ _ (NonUnitalSubsemiring.coe_iSup_of_directed dir).symm
      smul_mem' := fun r _x hx =>
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, (S i).smul_mem' r hi⟩ }
  have : iSup S = K := le_antisymm
    (iSup_le fun i => le_iSup (fun i => (S i : Set A)) i) (Set.iUnion_subset fun _ => le_iSup S _)
  this.symm ▸ rfl

/--
theorem `isMulCommutative_iSup` / 定理 `isMulCommutative_iSup`

English:
theorem isMulCommutative_iSup
  statement: {ι : Sort*} [Nonempty ι] {S : ι -> NonUnitalSubalgebra R A}
  proof: by
  have := NonUnitalSubsemiring.isMulCommutative_iSup dir
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    NonUnitalSubsemiring.coe_iSup_of_directed dir]

中文:
定理 isMulCommutative_iSup
  结论: {ι : 类型层*} [非空 ι] {S : ι -> NonUnital子代数 R A}
  证明: by
  have := NonUnitalSubsemiring.isMulCommutative_iSup dir
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    NonUnitalSubsemiring.coe_iSup_of_directed dir]

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.coe_iSup_of_directed, NonUnitalSubsemiring.isMulCommutative_iSup, SetLike, SetLike.mem_coe, coe_iSup_of_directed, isMulCommutative_iSup, isMulCommutative_iff, mem_coe
-/
theorem isMulCommutative_iSup {ι : Sort*} [Nonempty ι] {S : ι -> NonUnitalSubalgebra R A}
    [hS : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) :
    IsMulCommutative (⨆ i, S i : NonUnitalSubalgebra R A) := by
  have := NonUnitalSubsemiring.isMulCommutative_iSup dir
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    NonUnitalSubsemiring.coe_iSup_of_directed dir]

/--
Instance `instIsMulCommutative_iSup` / 实例 `instIsMulCommutative_iSup`

English:
instance instIsMulCommutative_iSup
  signature: {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
  body: isMulCommutative_iSup S.monotone.directed_le

中文:
实例 instIsMulCommutative_iSup
  签名: {ι : 类型} [非空 ι] [预序 ι] [IsDirectedOrder ι]
  定义体: isMulCommutative_iSup S.monotone.directed_le

Depends on / 依赖: S.monotone.directed_le, directed_le, isMulCommutative_iSup, monotone
-/
instance instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι ->o NonUnitalSubalgebra R A} [hS : forall i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : NonUnitalSubalgebra R A) :=
  isMulCommutative_iSup S.monotone.directed_le

/--
Definition of `iSupLift` / `iSupLift` 的定义

English:
definition iSupLift
  signature: [Nonempty ι] (K : ι -> NonUnitalSubalgebra R A) (dir : Directed (· <= ·) K)
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

中文:
定义 iSupLift
  签名: [非空 ι] (K : ι -> NonUnital子代数 R A) (dir : Directed (· <= ·) K)
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

Depends on / 依赖: Set.iUnionLift, Set.iUnionLift_binary, Set.iUnionLift_const, all_goals, coe_iSup_of_directed, iUnionLift, iUnionLift_binary, iUnionLift_const, map_add, map_mul, map_zero
-/
noncomputable def iSupLift [Nonempty ι] (K : ι -> NonUnitalSubalgebra R A) (dir : Directed (· <= ·) K)
    (f : forall i, K i ->ₙₐ[R] B) (hf : forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h))
    (T : NonUnitalSubalgebra R A) (hT : T = iSup K) : ↥T ->ₙₐ[R] B := by
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

variable [Nonempty ι] {K : ι -> NonUnitalSubalgebra R A} {dir : Directed (· <= ·) K}
  {f : forall i, K i ->ₙₐ[R] B} {hf : forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h)}
  {T : NonUnitalSubalgebra R A} {hT : T = iSup K}

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
  proof: by
  ext
  simp only [NonUnitalAlgHom.comp_apply, iSupLift_inclusion]

中文:
定理 iSupLift_comp_inclusion
  条件: {i : ι} (h : K i <= T)
  证明: by
  ext
  simp only [NonUnitalAlgHom.comp_apply, iSupLift_inclusion]

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.comp_apply, comp_apply, iSupLift_inclusion
-/
theorem iSupLift_comp_inclusion {i : ι} (h : K i <= T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by
  ext
  simp only [NonUnitalAlgHom.comp_apply, iSupLift_inclusion]

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

end SuprLift

end NonAssoc

section Center

section NonUnitalNonAssocSemiring
variable {R A : Type*}
variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

/--
theorem `_root_.Set.smul_mem_center` / 定理 `_root_.Set.smul_mem_center`

English:
theorem _root_.Set.smul_mem_center
  given: (r : R) {a : A} (ha : a in Set.center A)
  proof: by rw [commute_iff_eq, mul_smul_comm, smul_mul_assoc, ha.comm]
  left_assoc b c := by rw [smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, ha.left_assoc]
  right_assoc b c := by
    rw [mul_smul_comm]; rw [mul_smul_comm]; rw [mul_smul_comm]; rw [ha.right_assoc]

中文:
定理 _root_.集合.smul_mem_center
  条件: (r : R) {a : A} (ha : a in 集合.center A)
  证明: by rw [commute_iff_eq, mul_smul_comm, smul_mul_assoc, ha.comm]
  left_assoc b c := by rw [smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, ha.left_assoc]
  right_assoc b c := by
    rw [mul_smul_comm]; rw [mul_smul_comm]; rw [mul_smul_comm]; rw [ha.right_assoc]

Depends on / 依赖: commute_iff_eq, ha.comm, ha.left_assoc, ha.right_assoc, left_assoc, mul_smul_comm, right_assoc, smul_mul_assoc
-/
theorem _root_.Set.smul_mem_center (r : R) {a : A} (ha : a in Set.center A) :
    r • a in Set.center A where
  comm b := by rw [commute_iff_eq, mul_smul_comm, smul_mul_assoc, ha.comm]
  left_assoc b c := by rw [smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, ha.left_assoc]
  right_assoc b c := by
    rw [mul_smul_comm]; rw [mul_smul_comm]; rw [mul_smul_comm]; rw [ha.right_assoc]

variable (R A) in
/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: : NonUnitalSubalgebra R A
  body: { NonUnitalSubsemiring.center A with smul_mem' := Set.smul_mem_center }

@[norm_cast]

中文:
定义 center
  签名: : NonUnital子代数 R A
  定义体: { NonUnitalSubsemiring.center A with smul_mem' := Set.smul_mem_center }

@[norm_cast]

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.center, Set.smul_mem_center, center, smul_mem, smul_mem_center
-/
def center : NonUnitalSubalgebra R A :=
  { NonUnitalSubsemiring.center A with smul_mem' := Set.smul_mem_center }

@[norm_cast]
/--
theorem `coe_center` / 定理 `coe_center`

English:
theorem coe_center
  statement: (center R A : Set A) = Set.center A
  proof: rfl

中文:
定理 coe_center
  结论: (center R A : 集合 A) = 集合.center A
  证明: rfl
-/
theorem coe_center : (center R A : Set A) = Set.center A :=
  rfl

/--
Instance `center.instNonUnitalCommSemiring` / 实例 `center.instNonUnitalCommSemiring`

English:
instance center.instNonUnitalCommSemiring
  signature: : NonUnitalCommSemiring (center R A)
  body: inferInstanceAs NonUnitalCommSemiring (NonUnitalSubsemiring.center A)

中文:
实例 center.instNonUnitalCommSemiring
  签名: : 非幺交换半环 (center R A)
  定义体: inferInstanceAs NonUnitalCommSemiring (NonUnitalSubsemiring.center A)

Depends on / 依赖: NonUnitalCommSemiring, NonUnitalSubsemiring, NonUnitalSubsemiring.center, center
-/
instance center.instNonUnitalCommSemiring : NonUnitalCommSemiring (center R A) :=
inferInstanceAs NonUnitalCommSemiring (NonUnitalSubsemiring.center A)

/--
Instance `center.instNonUnitalCommRing` / 实例 `center.instNonUnitalCommRing`

English:
instance center.instNonUnitalCommRing
  signature: {A : Type*} [NonUnitalNonAssocRing A] [Module R A]
  body: inferInstanceAs NonUnitalCommRing (NonUnitalSubring.center A)

@[simp]

中文:
实例 center.instNonUnitalCommRing
  签名: {A : 类型} [非幺非结合环 A] [模 R A]
  定义体: inferInstanceAs NonUnitalCommRing (NonUnitalSubring.center A)

@[simp]

Depends on / 依赖: NonUnitalCommRing, NonUnitalSubring, NonUnitalSubring.center, center
-/
instance center.instNonUnitalCommRing {A : Type*} [NonUnitalNonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : NonUnitalCommRing (center R A) :=
inferInstanceAs NonUnitalCommRing (NonUnitalSubring.center A)

@[simp]
/--
theorem `center_toNonUnitalSubsemiring` / 定理 `center_toNonUnitalSubsemiring`

English:
theorem center_toNonUnitalSubsemiring
  proof: rfl

中文:
定理 center_toNonUnitalSubsemiring
  证明: rfl
-/
theorem center_toNonUnitalSubsemiring :
    (center R A).toNonUnitalSubsemiring = NonUnitalSubsemiring.center A :=
  rfl

/--
lemma `center_toNonUnitalSubring` / 引理 `center_toNonUnitalSubring`

English:
lemma center_toNonUnitalSubring
  statement: (R A : Type*) [CommRing R] [NonUnitalNonAssocRing A]
  proof: rfl

中文:
引理 center_toNonUnitalSubring
  结论: (R A : 类型) [交换环 R] [非幺非结合环 A]
  证明: rfl
-/
@[simp] lemma center_toNonUnitalSubring (R A : Type*) [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    (center R A).toNonUnitalSubring = NonUnitalSubring.center A :=
  rfl

/--
theorem `center_prod` / 定理 `center_prod`

English:
theorem center_prod
  statement: {B : Type*} [NonUnitalNonAssocSemiring B] [Module R B]
  proof: SetLike.coe_injective Set.center_prod

中文:
定理 center_prod
  结论: {B : 类型} [非幺非结合半环 B] [模 R B]
  证明: SetLike.coe_injective Set.center_prod
-/
protected theorem center_prod {B : Type*} [NonUnitalNonAssocSemiring B] [Module R B]
    [IsScalarTower R B B] [SMulCommClass R B B] :
    center R (A × B) = prod (center R A) (center R B) :=
  SetLike.coe_injective Set.center_prod

end NonUnitalNonAssocSemiring

variable (R A : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

-- no instance diamond, as the `npow` field isn't present in the non-unital case.
example : center.instNonUnitalCommSemiring.toNonUnitalSemiring =
    NonUnitalSubsemiringClass.toNonUnitalSemiring (center R A) := by
  with_reducible_and_instances rfl

@[simp]
/--
theorem `center_eq_top` / 定理 `center_eq_top`

English:
theorem center_eq_top
  statement: (A : Type*) [NonUnitalCommSemiring A] [Module R A] [IsScalarTower R A A]
  proof: SetLike.coe_injective (Set.center_eq_univ A)

中文:
定理 center_eq_top
  结论: (A : 类型) [非幺交换半环 A] [模 R A] [标量塔 R A A]
  证明: SetLike.coe_injective (Set.center_eq_univ A)

Depends on / 依赖: Set.center_eq_univ, SetLike, SetLike.coe_injective, center_eq_univ, coe_injective
-/
theorem center_eq_top (A : Type*) [NonUnitalCommSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)

variable {R A}

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

end Center

section Centralizer

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

@[simp]
/--
theorem `_root_.Set.smul_mem_centralizer` / 定理 `_root_.Set.smul_mem_centralizer`

English:
theorem _root_.Set.smul_mem_centralizer
  given: {s : Set A} (r : R) {a : A} (ha : a in s.centralizer)
  proof: fun x hx => by rw [mul_smul_comm, smul_mul_assoc, ha x hx]

中文:
定理 _root_.集合.smul_mem_centralizer
  条件: {s : 集合 A} (r : R) {a : A} (ha : a in s.centralizer)
  证明: fun x hx => by rw [mul_smul_comm, smul_mul_assoc, ha x hx]

Depends on / 依赖: mul_smul_comm, smul_mul_assoc
-/
theorem _root_.Set.smul_mem_centralizer {s : Set A} (r : R) {a : A} (ha : a in s.centralizer) :
    r • a in s.centralizer :=
  fun x hx => by rw [mul_smul_comm, smul_mul_assoc, ha x hx]

variable (R)

/--
Definition of `centralizer` / `centralizer` 的定义

English:
definition centralizer
  signature: (s : Set A)
  body: NonUnitalSubsemiring.centralizer s
  smul_mem' := Set.smul_mem_centralizer

@[simp, norm_cast]

中文:
定义 centralizer
  签名: (s : 集合 A)
  定义体: NonUnitalSubsemiring.centralizer s
  smul_mem' := Set.smul_mem_centralizer

@[simp, norm_cast]

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.centralizer, centralizer
-/
def centralizer (s : Set A) : NonUnitalSubalgebra R A where
  toNonUnitalSubsemiring := NonUnitalSubsemiring.centralizer s
  smul_mem' := Set.smul_mem_centralizer

@[simp, norm_cast]
/--
theorem `coe_centralizer` / 定理 `coe_centralizer`

English:
theorem coe_centralizer
  given: (s : Set A)
  statement: (centralizer R s : Set A) = s.centralizer
  proof: rfl

中文:
定理 coe_centralizer
  条件: (s : 集合 A)
  结论: (centralizer R s : 集合 A) = s.centralizer
  证明: rfl
-/
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = s.centralizer :=
  rfl

/--
theorem `mem_centralizer_iff` / 定理 `mem_centralizer_iff`

English:
theorem mem_centralizer_iff
  given: {s : Set A} {z : A}
  statement: z in centralizer R s ↔ forall g in s, g * z = z * g
  proof: Iff.rfl

中文:
定理 mem_centralizer_iff
  条件: {s : 集合 A} {z : A}
  结论: z in centralizer R s ↔ 对任意 g in s, g * z = z * g
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_centralizer_iff {s : Set A} {z : A} : z in centralizer R s ↔ forall g in s, g * z = z * g :=
  Iff.rfl

/--
theorem `centralizer_le` / 定理 `centralizer_le`

English:
theorem centralizer_le
  given: (s t : Set A) (h : s subseteq t)
  statement: centralizer R t <= centralizer R s
  proof: Set.centralizer_subset h

@[simp]

中文:
定理 centralizer_le
  条件: (s t : 集合 A) (h : s subseteq t)
  结论: centralizer R t <= centralizer R s
  证明: Set.centralizer_subset h

@[simp]

Depends on / 依赖: Set.centralizer_subset, centralizer_subset
-/
theorem centralizer_le (s t : Set A) (h : s subseteq t) : centralizer R t <= centralizer R s :=
  Set.centralizer_subset h

@[simp]
/--
theorem `centralizer_univ` / 定理 `centralizer_univ`

English:
theorem centralizer_univ
  statement: centralizer R Set.univ = center R A
  proof: SetLike.ext' (Set.centralizer_univ A)

中文:
定理 centralizer_univ
  结论: centralizer R 集合.univ = center R A
  证明: SetLike.ext' (Set.centralizer_univ A)

Depends on / 依赖: Set.centralizer_univ, SetLike, SetLike.ext, centralizer_univ
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
/--
lemma `adjoin_le_centralizer_centralizer` / 引理 `adjoin_le_centralizer_centralizer`

English:
lemma adjoin_le_centralizer_centralizer
  given: (s : Set A)
  proof: adjoin_le Set.subset_centralizer_centralizer

中文:
引理 adjoin_le_centralizer_centralizer
  条件: (s : 集合 A)
  证明: adjoin_le Set.subset_centralizer_centralizer

Depends on / 依赖: Set.subset_centralizer_centralizer, adjoin_le, subset_centralizer_centralizer
-/
lemma adjoin_le_centralizer_centralizer (s : Set A) :
    adjoin R s <= centralizer R (centralizer R s) :=
  adjoin_le Set.subset_centralizer_centralizer

/--
lemma `commute_of_mem_adjoin_of_forall_mem_commute` / 引理 `commute_of_mem_adjoin_of_forall_mem_commute`

English:
lemma commute_of_mem_adjoin_of_forall_mem_commute
  statement: {a b : A} {s : Set A}
  proof: by
  have : a in centralizer R s := by simpa only [Commute.symm_iff (a := a)] using! h
  exact adjoin_le_centralizer_centralizer R s hb a this

中文:
引理 commute_of_mem_adjoin_of_对任意_mem_commute
  结论: {a b : A} {s : 集合 A}
  证明: by
  have : a in centralizer R s := by simpa only [Commute.symm_iff (a := a)] using! h
  exact adjoin_le_centralizer_centralizer R s hb a this

Depends on / 依赖: Commute, Commute.symm_iff, adjoin_le_centralizer_centralizer, centralizer, symm_iff
-/
lemma commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A}
    (hb : b in adjoin R s) (h : forall b in s, Commute a b) :
    Commute a b := by
  have : a in centralizer R s := by simpa only [Commute.symm_iff (a := a)] using! h
  exact adjoin_le_centralizer_centralizer R s hb a this

/--
lemma `commute_of_mem_adjoin_singleton_of_commute` / 引理 `commute_of_mem_adjoin_singleton_of_commute`

English:
lemma commute_of_mem_adjoin_singleton_of_commute
  statement: {a b c : A}
  proof: commute_of_mem_adjoin_of_forall_mem_commute hc by simpa

中文:
引理 commute_of_mem_adjoin_singleton_of_commute
  结论: {a b c : A}
  证明: commute_of_mem_adjoin_of_forall_mem_commute hc by simpa

Depends on / 依赖: commute_of_mem_adjoin_of_forall_mem_commute
-/
lemma commute_of_mem_adjoin_singleton_of_commute {a b c : A}
    (hc : c in adjoin R {b}) (h : Commute a b) :
    Commute a c :=
commute_of_mem_adjoin_of_forall_mem_commute hc by simpa

/--
lemma `commute_of_mem_adjoin_self` / 引理 `commute_of_mem_adjoin_self`

English:
lemma commute_of_mem_adjoin_self
  given: {a b : A} (hb : b in adjoin R {a})
  proof: commute_of_mem_adjoin_singleton_of_commute hb rfl

中文:
引理 commute_of_mem_adjoin_self
  条件: {a b : A} (hb : b in adjoin R {a})
  证明: commute_of_mem_adjoin_singleton_of_commute hb rfl

Depends on / 依赖: commute_of_mem_adjoin_singleton_of_commute
-/
lemma commute_of_mem_adjoin_self {a b : A} (hb : b in adjoin R {a}) :
    Commute a b :=
  commute_of_mem_adjoin_singleton_of_commute hb rfl

variable (R) in
/--
theorem `isMulCommutative_adjoin` / 定理 `isMulCommutative_adjoin`

English:
theorem isMulCommutative_adjoin
  given: {s : Set A} (hcomm : forall x in s, forall y in s, x * y = y * x)
  proof: have := adjoin_le_centralizer_centralizer R s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

中文:
定理 isMulCommutative_adjoin
  条件: {s : 集合 A} (hcomm : 对任意 x in s, 对任意 y in s, x * y = y * x)
  证明: have := adjoin_le_centralizer_centralizer R s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

Depends on / 依赖: Set.centralizer_centralizer_comm_of_comm, adjoin_le_centralizer_centralizer, centralizer_centralizer_comm_of_comm, of_setLike_mul_comm
-/
theorem isMulCommutative_adjoin {s : Set A} (hcomm : forall x in s, forall y in s, x * y = y * x) :
    IsMulCommutative (adjoin R s) :=
  have := adjoin_le_centralizer_centralizer R s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

variable (R) in
/--
Instance `isMulCommutative_adjoin_singleton` / 实例 `isMulCommutative_adjoin_singleton`

English:
instance isMulCommutative_adjoin_singleton
  signature: (x : A)
  body: isMulCommutative_adjoin R (by simp)

中文:
实例 isMulCommutative_adjoin_singleton
  签名: (x : A)
  定义体: isMulCommutative_adjoin R (by simp)

Depends on / 依赖: isMulCommutative_adjoin
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
/--
Definition of `adjoinNonUnitalCommSemiringOfComm` / `adjoinNonUnitalCommSemiringOfComm` 的定义

English:
abbreviation adjoinNonUnitalCommSemiringOfComm
  signature: {s : Set A} (hcomm : forall a in s, forall b in s, a * b = b * a)
  body: have := isMulCommutative_adjoin R hcomm
  inferInstance

中文:
缩写 adjoinNonUnitalCommSemiringOfComm
  签名: {s : 集合 A} (hcomm : 对任意 a in s, 对任意 b in s, a * b = b * a)
  定义体: have := isMulCommutative_adjoin R hcomm
  inferInstance

Depends on / 依赖: isMulCommutative_adjoin
-/
abbrev adjoinNonUnitalCommSemiringOfComm {s : Set A} (hcomm : forall a in s, forall b in s, a * b = b * a) :
    NonUnitalCommSemiring (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm
  inferInstance

/--
Instance `instIsMulCommutative_adjoin` / 实例 `instIsMulCommutative_adjoin`

English:
instance instIsMulCommutative_adjoin
  signature: {S : Type*} [SetLike S A] [MulMemClass S A] (s : S)
  body: isMulCommutative_adjoin R fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

中文:
实例 instIsMulCommutative_adjoin
  签名: {S : 类型} [集合状 S A] [MulMem类 S A] (s : S)
  定义体: isMulCommutative_adjoin R fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

Depends on / 依赖: isMulCommutative_adjoin, setLike_mul_comm
-/
instance instIsMulCommutative_adjoin {S : Type*} [SetLike S A] [MulMemClass S A] (s : S)
    [IsMulCommutative s] : IsMulCommutative (adjoin R (s : Set A)) :=
  isMulCommutative_adjoin R fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

open scoped IsMulCommutative in
/-- If all elements of `s : Set A` commute pairwise, then `adjoin R s` is a non-unital commutative
ring.

See note [reducible non-instances]. -/
@[deprecated isMulCommutative_adjoin (since := "2026-03-11")]
/--
Definition of `adjoinNonUnitalCommRingOfComm` / `adjoinNonUnitalCommRingOfComm` 的定义

English:
abbreviation adjoinNonUnitalCommRingOfComm
  signature: (R : Type*) {A : Type*} [CommRing R] [NonUnitalRing A]
  body: have := isMulCommutative_adjoin R hcomm
  inferInstance

中文:
缩写 adjoinNonUnitalCommRingOfComm
  签名: (R : 类型) {A : 类型} [交换环 R] [非幺环 A]
  定义体: have := isMulCommutative_adjoin R hcomm
  inferInstance

Depends on / 依赖: isMulCommutative_adjoin
-/
abbrev adjoinNonUnitalCommRingOfComm (R : Type*) {A : Type*} [CommRing R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] {s : Set A}
    (hcomm : forall a in s, forall b in s, a * b = b * a) : NonUnitalCommRing (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm
  inferInstance

end NonUnitalAlgebra

section Nat

variable {R : Type*} [NonUnitalNonAssocSemiring R]

/--
Definition of `nonUnitalSubalgebraOfNonUnitalSubsemiring` / `nonUnitalSubalgebraOfNonUnitalSubsemiring` 的定义

English:
definition nonUnitalSubalgebraOfNonUnitalSubsemiring
  signature: (S : NonUnitalSubsemiring R)
  body: S
  smul_mem' n _x hx := nsmul_mem (S := S) hx n

@[simp]

中文:
定义 nonUnitalSubalgebraOfNonUnitalSubsemiring
  签名: (S : NonUnital子半环 R)
  定义体: S
  smul_mem' n _x hx := nsmul_mem (S := S) hx n

@[simp]
-/
def nonUnitalSubalgebraOfNonUnitalSubsemiring (S : NonUnitalSubsemiring R) :
    NonUnitalSubalgebra Nat R where
  toNonUnitalSubsemiring := S
  smul_mem' n _x hx := nsmul_mem (S := S) hx n

@[simp]
/--
theorem `mem_nonUnitalSubalgebraOfNonUnitalSubsemiring` / 定理 `mem_nonUnitalSubalgebraOfNonUnitalSubsemiring`

English:
theorem mem_nonUnitalSubalgebraOfNonUnitalSubsemiring
  given: {x : R} {S : NonUnitalSubsemiring R}
  proof: Iff.rfl

中文:
定理 mem_nonUnitalSubalgebraOfNonUnitalSubsemiring
  条件: {x : R} {S : NonUnital子半环 R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_nonUnitalSubalgebraOfNonUnitalSubsemiring {x : R} {S : NonUnitalSubsemiring R} :
    x in nonUnitalSubalgebraOfNonUnitalSubsemiring S ↔ x in S :=
  Iff.rfl

end Nat

section Int

variable {R : Type*} [NonUnitalNonAssocRing R]

/--
Definition of `nonUnitalSubalgebraOfNonUnitalSubring` / `nonUnitalSubalgebraOfNonUnitalSubring` 的定义

English:
definition nonUnitalSubalgebraOfNonUnitalSubring
  signature: (S : NonUnitalSubring R)
  body: S.toNonUnitalSubsemiring
  smul_mem' n _x hx := zsmul_mem (K := S) hx n

@[simp]

中文:
定义 nonUnitalSubalgebraOfNonUnitalSubring
  签名: (S : NonUnital子环 R)
  定义体: S.toNonUnitalSubsemiring
  smul_mem' n _x hx := zsmul_mem (K := S) hx n

@[simp]

Depends on / 依赖: S.toNonUnitalSubsemiring, toNonUnitalSubsemiring
-/
def nonUnitalSubalgebraOfNonUnitalSubring (S : NonUnitalSubring R) : NonUnitalSubalgebra Int R where
  toNonUnitalSubsemiring := S.toNonUnitalSubsemiring
  smul_mem' n _x hx := zsmul_mem (K := S) hx n

@[simp]
/--
theorem `mem_nonUnitalSubalgebraOfNonUnitalSubring` / 定理 `mem_nonUnitalSubalgebraOfNonUnitalSubring`

English:
theorem mem_nonUnitalSubalgebraOfNonUnitalSubring
  given: {x : R} {S : NonUnitalSubring R}
  proof: Iff.rfl

中文:
定理 mem_nonUnitalSubalgebraOfNonUnitalSubring
  条件: {x : R} {S : NonUnital子环 R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_nonUnitalSubalgebraOfNonUnitalSubring {x : R} {S : NonUnitalSubring R} :
    x in nonUnitalSubalgebraOfNonUnitalSubring S ↔ x in S :=
  Iff.rfl

end Int
