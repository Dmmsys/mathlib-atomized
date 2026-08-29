/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.RingTheory.NonUnitalSubsemiring.Defs
public import Mathlib.Tactic.FastInstance

/-!
# `NonUnitalSubring`s

Let `R` be a non-unital ring. This file defines the "bundled" non-unital subring type
`NonUnitalSubring R`, a type whose terms correspond to non-unital subrings of `R`.
This is the preferred way to talk about non-unital subrings in mathlib.

## Main definitions

Notation used here:

`(R : Type u) [NonUnitalRing R] (S : Type u) [NonUnitalRing S] (f g : R →ₙ+* S)`
`(A : NonUnitalSubring R) (B : NonUnitalSubring S) (s : Set R)`

* `NonUnitalSubring R` : the type of non-unital subrings of a ring `R`.

## Implementation notes

A non-unital subring is implemented as a `NonUnitalSubsemiring` which is also an
additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a non-unital subring's underlying set.

## Tags
non-unital subring
-/

@[expose] public section

assert_not_exists RelIso

universe u v w

section Basic

variable {R : Type u} {S : Type v} [NonUnitalNonAssocRing R]

section NonUnitalSubringClass

/--
Definition of `NonUnitalSubringClass` / `NonUnitalSubringClass` 的定义

English:
class NonUnitalSubringClass
  parameters: (S : Type*) (R : Type u) [NonUnitalNonAssocRing R] [SetLike S R]
  extends: NonUnitalSubsemiringClass S R, NegMemClass S R
  (no additional axioms)

中文:
类 NonUnital子环类
  参数: (S : 类型) (R : 类型u) [非幺非结合环 R] [集合状 S R]
  继承: NonUnital子半环类 S R, NegMem类 S R
  (无附加公理)
-/
class NonUnitalSubringClass (S : Type*) (R : Type u) [NonUnitalNonAssocRing R] [SetLike S R] : Prop
  extends NonUnitalSubsemiringClass S R, NegMemClass S R where

-- See note [lower instance priority]
instance (priority := 100) NonUnitalSubringClass.addSubgroupClass (S : Type*) (R : Type u)
    [SetLike S R] [NonUnitalNonAssocRing R] [h : NonUnitalSubringClass S R] :
    AddSubgroupClass S R :=
  { h with }

variable [SetLike S R] [hSR : NonUnitalSubringClass S R] (s : S)

namespace NonUnitalSubringClass

-- Prefer subclasses of `NonUnitalRing` over subclasses of `NonUnitalSubringClass`.
/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
instance (priority := 75) toNonUnitalNonAssocRing : NonUnitalNonAssocRing s := fast_instance%
  Subtype.val_injective.nonUnitalNonAssocRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `NonUnitalRing` over subclasses of `NonUnitalSubringClass`.
/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
instance (priority := 75) toNonUnitalRing {R : Type*} [NonUnitalRing R] [SetLike S R]
    [NonUnitalSubringClass S R] (s : S) : NonUnitalRing s := fast_instance%
  Subtype.val_injective.nonUnitalRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `NonUnitalRing` over subclasses of `NonUnitalSubringClass`.
/-- A non-unital subring of a `NonUnitalNonAssocCommRing` is a `NonUnitalNonAssocCommRing`. -/
instance (priority := 75) toNonUnitalNonAssocCommRing {R} [NonUnitalNonAssocCommRing R]
    [SetLike S R] [NonUnitalSubringClass S R] (s : S) :
    NonUnitalNonAssocCommRing s := fast_instance%
  Subtype.val_injective.nonUnitalNonAssocCommRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `NonUnitalRing` over subclasses of `NonUnitalSubringClass`.
/-- A non-unital subring of a `NonUnitalCommRing` is a `NonUnitalCommRing`. -/
instance (priority := 75) toNonUnitalCommRing {R} [NonUnitalCommRing R] [SetLike S R]
    [NonUnitalSubringClass S R] : NonUnitalCommRing s := fast_instance%
  Subtype.val_injective.nonUnitalCommRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (s : S)
  body: { NonUnitalSubsemiringClass.subtype s,
    AddSubgroupClass.subtype s with
    toFun := Subtype.val }

中文:
定义 subtype
  签名: (s : S)
  定义体: { NonUnitalSubsemiringClass.subtype s,
    AddSubgroupClass.subtype s with
    toFun := Subtype.val }

Depends on / 依赖: AddSubgroupClass, AddSubgroupClass.subtype, NonUnitalSubsemiringClass, NonUnitalSubsemiringClass.subtype, Subtype, Subtype.val, subtype
-/
def subtype (s : S) : s ->ₙ+* R :=
  { NonUnitalSubsemiringClass.subtype s,
    AddSubgroupClass.subtype s with
    toFun := Subtype.val }

variable {s} in
@[simp]
/--
theorem `subtype_apply` / 定理 `subtype_apply`

English:
theorem subtype_apply
  given: (x : s)
  statement: subtype s x = x
  proof: rfl

中文:
定理 subtype_apply
  条件: (x : s)
  结论: subtype s x = x
  证明: rfl
-/
theorem subtype_apply (x : s) : subtype s x = x :=
  rfl

/--
theorem `subtype_injective` / 定理 `subtype_injective`

English:
theorem subtype_injective
  statement: Function.Injective (subtype s)
  proof: Subtype.coe_injective

@[simp]

中文:
定理 subtype_injective
  结论: 函数.单射 (subtype s)
  证明: Subtype.coe_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem subtype_injective : Function.Injective (subtype s) :=
  Subtype.coe_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: (subtype s : s -> R) = Subtype.val
  proof: rfl

中文:
定理 coe_subtype
  结论: (subtype s : s -> R) = 子类型.val
  证明: rfl
-/
theorem coe_subtype : (subtype s : s -> R) = Subtype.val :=
  rfl

end NonUnitalSubringClass

end NonUnitalSubringClass

/--
Definition of `NonUnitalSubring` / `NonUnitalSubring` 的定义

English:
structure NonUnitalSubring
  parameters: (R : Type u) [NonUnitalNonAssocRing R]
  (no additional axioms)

中文:
结构 NonUnital子环
  参数: (R : 类型u) [非幺非结合环 R]
  (无附加公理)
-/
structure NonUnitalSubring (R : Type u) [NonUnitalNonAssocRing R] extends
  NonUnitalSubsemiring R, AddSubgroup R

/-- Reinterpret a `NonUnitalSubring` as a `NonUnitalSubsemiring`. -/
add_decl_doc NonUnitalSubring.toNonUnitalSubsemiring

/-- Reinterpret a `NonUnitalSubring` as an `AddSubgroup`. -/
add_decl_doc NonUnitalSubring.toAddSubgroup

namespace NonUnitalSubring

/-- The underlying submonoid of a `NonUnitalSubring`. -/
@[reducible]
/--
Definition of `toSubsemigroup` / `toSubsemigroup` 的定义

English:
definition toSubsemigroup
  signature: (s : NonUnitalSubring R)
  body: { s.toNonUnitalSubsemiring.toSubsemigroup with carrier := s.carrier }

中文:
定义 toSubsemigroup
  签名: (s : NonUnital子环 R)
  定义体: { s.toNonUnitalSubsemiring.toSubsemigroup with carrier := s.carrier }

Depends on / 依赖: carrier, s.carrier, s.toNonUnitalSubsemiring.toSubsemigroup, toNonUnitalSubsemiring, toSubsemigroup
-/
def toSubsemigroup (s : NonUnitalSubring R) : Subsemigroup R :=
  { s.toNonUnitalSubsemiring.toSubsemigroup with carrier := s.carrier }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (NonUnitalSubring R) R
  body: s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

中文:
实例 :
  签名: 集合状 (NonUnital子环 R) R
  定义体: s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

Depends on / 依赖: carrier, s.carrier
-/
instance : SetLike (NonUnitalSubring R) R where
  coe s := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (NonUnitalSubring R)
  body: .ofSetLike (NonUnitalSubring R) R

中文:
实例 :
  签名: 偏序 (NonUnital子环 R)
  定义体: .ofSetLike (NonUnitalSubring R) R

Depends on / 依赖: NonUnitalSubring, ofSetLike
-/
instance : PartialOrder (NonUnitalSubring R) := .ofSetLike (NonUnitalSubring R) R

/-- The actual `NonUnitalSubring` obtained from an element of a `NonUnitalSubringClass`. -/
@[simps]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: {S R : Type*} [NonUnitalNonAssocRing R] [SetLike S R] [NonUnitalSubringClass S R]
  body: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  neg_mem' := neg_mem

中文:
定义 ofClass
  签名: {S R : 类型} [非幺非结合环 R] [集合状 S R] [NonUnital子环类 S R]
  定义体: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  neg_mem' := neg_mem
-/
def ofClass {S R : Type*} [NonUnitalNonAssocRing R] [SetLike S R] [NonUnitalSubringClass S R]
    (s : S) : NonUnitalSubring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  neg_mem' := neg_mem

instance (priority := 100) : CanLift (Set R) (NonUnitalSubring R) (↑)
    (fun s => 0 in s ∧ (forall {x y}, x in s -> y in s -> x + y in s) ∧
      (forall {x y}, x in s -> y in s -> x * y in s) ∧ forall {x}, x in s -> -x in s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        mul_mem' := h.2.2.1
        neg_mem' := h.2.2.2 },
      rfl ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonUnitalSubringClass (NonUnitalSubring R) R
  body: s.zero_mem'
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  neg_mem {s} := s.neg_mem'

中文:
实例 :
  签名: NonUnital子环类 (NonUnital子环 R) R
  定义体: s.zero_mem'
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  neg_mem {s} := s.neg_mem'

Depends on / 依赖: s.zero_mem, zero_mem
-/
instance : NonUnitalSubringClass (NonUnitalSubring R) R where
  zero_mem s := s.zero_mem'
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  neg_mem {s} := s.neg_mem'

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : NonUnitalSubring R} {x : R}
  statement: x in s.toNonUnitalSubsemiring ↔ x in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_carrier
  条件: {s : NonUnital子环 R} {x : R}
  结论: x in s.toNonUnitalSubsemiring ↔ x in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : NonUnitalSubring R} {x : R} : x in s.toNonUnitalSubsemiring ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {S : NonUnitalSubsemiring R} {x : R} (h)
  proof: Iff.rfl

@[simp]

中文:
定理 mem_mk
  条件: {S : NonUnital子半环 R} {x : R} (h)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk {S : NonUnitalSubsemiring R} {x : R} (h) :
    x in (⟨S, h⟩ : NonUnitalSubring R) ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `coe_set_mk` / 定理 `coe_set_mk`

English:
theorem coe_set_mk
  given: (S : NonUnitalSubsemiring R) (h)
  proof: rfl

@[simp]

中文:
定理 coe_set_mk
  条件: (S : NonUnital子半环 R) (h)
  证明: rfl

@[simp]
-/
theorem coe_set_mk (S : NonUnitalSubsemiring R) (h) :
    ((⟨S, h⟩ : NonUnitalSubring R) : Set R) = S :=
  rfl

@[simp]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: {S S' : NonUnitalSubsemiring R} (h h')
  proof: Iff.rfl

中文:
定理 mk_le_mk
  条件: {S S' : NonUnital子半环 R} (h h')
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mk_le_mk {S S' : NonUnitalSubsemiring R} (h h') :
    (⟨S, h⟩ : NonUnitalSubring R) <= (⟨S', h'⟩ : NonUnitalSubring R) ↔ S <= S' :=
  Iff.rfl

/-- Two non-unital subrings are equal if they have the same elements. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : NonUnitalSubring R} (h : forall x, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

中文:
定理 ext
  条件: {S T : NonUnital子环 R} (h : 对任意 x, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : NonUnitalSubring R} (h : forall x, x in S ↔ x in T) : S = T :=
  SetLike.ext h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S)
  body: { S.toNonUnitalSubsemiring.copy s hs with
    carrier := s
    neg_mem' := hs.symm ▸ S.neg_mem' }

@[simp]

中文:
定义 copy
  签名: (S : NonUnital子环 R) (s : 集合 R) (hs : s = ↑S)
  定义体: { S.toNonUnitalSubsemiring.copy s hs with
    carrier := s
    neg_mem' := hs.symm ▸ S.neg_mem' }

@[simp]
-/
protected def copy (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : NonUnitalSubring R :=
  { S.toNonUnitalSubsemiring.copy s hs with
    carrier := s
    neg_mem' := hs.symm ▸ S.neg_mem' }

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S)
  statement: (S.copy s hs : Set R) = s
  proof: rfl

中文:
定理 coe_copy
  条件: (S : NonUnital子环 R) (s : 集合 R) (hs : s = ↑S)
  结论: (S.copy s hs : 集合 R) = s
  证明: rfl
-/
theorem coe_copy (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: (S : NonUnital子环 R) (s : 集合 R) (hs : s = ↑S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

/--
theorem `toNonUnitalSubsemiring_injective` / 定理 `toNonUnitalSubsemiring_injective`

English:
theorem toNonUnitalSubsemiring_injective

中文:
定理 toNonUnitalSubsemiring_injective
-/
theorem toNonUnitalSubsemiring_injective :
    Function.Injective (toNonUnitalSubsemiring : NonUnitalSubring R -> NonUnitalSubsemiring R)
  | _r, _s, h => ext (SetLike.ext_iff.mp h :)

@[gcongr, mono]
/--
theorem `toNonUnitalSubsemiring_strictMono` / 定理 `toNonUnitalSubsemiring_strictMono`

English:
theorem toNonUnitalSubsemiring_strictMono
  proof: fun _ _ =>
  id

@[gcongr, mono]

中文:
定理 toNonUnitalSubsemiring_strictMono
  证明: fun _ _ =>
  id

@[gcongr, mono]
-/
theorem toNonUnitalSubsemiring_strictMono :
    StrictMono (toNonUnitalSubsemiring : NonUnitalSubring R -> NonUnitalSubsemiring R) := fun _ _ =>
  id

@[gcongr, mono]
/--
theorem `toNonUnitalSubsemiring_mono` / 定理 `toNonUnitalSubsemiring_mono`

English:
theorem toNonUnitalSubsemiring_mono
  proof: toNonUnitalSubsemiring_strictMono.monotone

中文:
定理 toNonUnitalSubsemiring_mono
  证明: toNonUnitalSubsemiring_strictMono.monotone

Depends on / 依赖: monotone, toNonUnitalSubsemiring_strictMono, toNonUnitalSubsemiring_strictMono.monotone
-/
theorem toNonUnitalSubsemiring_mono :
    Monotone (toNonUnitalSubsemiring : NonUnitalSubring R -> NonUnitalSubsemiring R) :=
  toNonUnitalSubsemiring_strictMono.monotone

/--
theorem `toAddSubgroup_injective` / 定理 `toAddSubgroup_injective`

English:
theorem toAddSubgroup_injective

中文:
定理 toAddSubgroup_injective
-/
theorem toAddSubgroup_injective :
    Function.Injective (toAddSubgroup : NonUnitalSubring R -> AddSubgroup R)
  | _r, _s, h => ext (SetLike.ext_iff.mp h :)

@[gcongr, mono]
/--
theorem `toAddSubgroup_strictMono` / 定理 `toAddSubgroup_strictMono`

English:
theorem toAddSubgroup_strictMono
  proof: fun _ _ => id

@[gcongr, mono]

中文:
定理 toAddSubgroup_strictMono
  证明: fun _ _ => id

@[gcongr, mono]
-/
theorem toAddSubgroup_strictMono :
    StrictMono (toAddSubgroup : NonUnitalSubring R -> AddSubgroup R) := fun _ _ => id

@[gcongr, mono]
/--
theorem `toAddSubgroup_mono` / 定理 `toAddSubgroup_mono`

English:
theorem toAddSubgroup_mono
  statement: Monotone (toAddSubgroup : NonUnitalSubring R -> AddSubgroup R)
  proof: toAddSubgroup_strictMono.monotone

中文:
定理 toAddSubgroup_mono
  结论: 递增 (toAddSubgroup : NonUnital子环 R -> 加法子群 R)
  证明: toAddSubgroup_strictMono.monotone

Depends on / 依赖: monotone, toAddSubgroup_strictMono, toAddSubgroup_strictMono.monotone
-/
theorem toAddSubgroup_mono : Monotone (toAddSubgroup : NonUnitalSubring R -> AddSubgroup R) :=
  toAddSubgroup_strictMono.monotone

/--
theorem `toSubsemigroup_injective` / 定理 `toSubsemigroup_injective`

English:
theorem toSubsemigroup_injective

中文:
定理 toSubsemigroup_injective
-/
theorem toSubsemigroup_injective :
    Function.Injective (toSubsemigroup : NonUnitalSubring R -> Subsemigroup R)
  | _r, _s, h => ext (SetLike.ext_iff.mp h :)

@[gcongr, mono]
/--
theorem `toSubsemigroup_strictMono` / 定理 `toSubsemigroup_strictMono`

English:
theorem toSubsemigroup_strictMono
  proof: fun _ _ => id

@[gcongr, mono]

中文:
定理 toSubsemigroup_strictMono
  证明: fun _ _ => id

@[gcongr, mono]
-/
theorem toSubsemigroup_strictMono :
    StrictMono (toSubsemigroup : NonUnitalSubring R -> Subsemigroup R) := fun _ _ => id

@[gcongr, mono]
/--
theorem `toSubsemigroup_mono` / 定理 `toSubsemigroup_mono`

English:
theorem toSubsemigroup_mono
  statement: Monotone (toSubsemigroup : NonUnitalSubring R -> Subsemigroup R)
  proof: toSubsemigroup_strictMono.monotone

中文:
定理 toSubsemigroup_mono
  结论: 递增 (toSubsemigroup : NonUnital子环 R -> 子半群 R)
  证明: toSubsemigroup_strictMono.monotone

Depends on / 依赖: monotone, toSubsemigroup_strictMono, toSubsemigroup_strictMono.monotone
-/
theorem toSubsemigroup_mono : Monotone (toSubsemigroup : NonUnitalSubring R -> Subsemigroup R) :=
  toSubsemigroup_strictMono.monotone

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (s : Set R) (sm : Subsemigroup R) (sa : AddSubgroup R) (hm : ↑sm = s)
  body: { sm.copy s hm.symm, sa.copy s ha.symm with }

@[simp]

中文:
定义 mk'
  签名: (s : 集合 R) (sm : 子半群 R) (sa : 加法子群 R) (hm : ↑sm = s)
  定义体: { sm.copy s hm.symm, sa.copy s ha.symm with }

@[simp]
-/
protected def mk' (s : Set R) (sm : Subsemigroup R) (sa : AddSubgroup R) (hm : ↑sm = s)
    (ha : ↑sa = s) : NonUnitalSubring R :=
  { sm.copy s hm.symm, sa.copy s ha.symm with }

@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  statement: {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
  proof: rfl

@[simp]

中文:
定理 coe_mk'
  结论: {s : 集合 R} {sm : 子半群 R} (hm : ↑sm = s) {sa : 加法子群 R}
  证明: rfl

@[simp]
-/
theorem coe_mk' {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (NonUnitalSubring.mk' s sm sa hm ha : Set R) = s :=
  rfl

@[simp]
/--
theorem `mem_mk'` / 定理 `mem_mk'`

English:
theorem mem_mk'
  statement: {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s)
  proof: Iff.rfl

@[simp]

中文:
定理 mem_mk'
  结论: {s : 集合 R} {sm : 子半群 R} (hm : ↑sm = s) {sa : 加法子群 R} (ha : ↑sa = s)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk' {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s)
    {x : R} : x in NonUnitalSubring.mk' s sm sa hm ha ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `mk'_toSubsemigroup` / 定理 `mk'_toSubsemigroup`

English:
theorem mk'_toSubsemigroup
  statement: {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
  proof: SetLike.coe_injective hm.symm

@[simp]

中文:
定理 mk'_toSubsemigroup
  结论: {s : 集合 R} {sm : 子半群 R} (hm : ↑sm = s) {sa : 加法子群 R}
  证明: SetLike.coe_injective hm.symm

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, hm.symm
-/
theorem mk'_toSubsemigroup {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (NonUnitalSubring.mk' s sm sa hm ha).toSubsemigroup = sm :=
  SetLike.coe_injective hm.symm

@[simp]
/--
theorem `mk'_toAddSubgroup` / 定理 `mk'_toAddSubgroup`

English:
theorem mk'_toAddSubgroup
  statement: {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
  proof: SetLike.coe_injective ha.symm

中文:
定理 mk'_toAddSubgroup
  结论: {s : 集合 R} {sm : 子半群 R} (hm : ↑sm = s) {sa : 加法子群 R}
  证明: SetLike.coe_injective ha.symm
-/
theorem mk'_toAddSubgroup {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (NonUnitalSubring.mk' s sm sa hm ha).toAddSubgroup = sa :=
  SetLike.coe_injective ha.symm

end NonUnitalSubring

namespace NonUnitalSubring

variable (s : NonUnitalSubring R)

/--
theorem `zero_mem` / 定理 `zero_mem`

English:
theorem zero_mem
  statement: (0 : R) in s
  proof: zero_mem _

中文:
定理 zero_mem
  结论: (0 : R) in s
  证明: zero_mem _
-/
protected theorem zero_mem : (0 : R) in s :=
  zero_mem _

/--
theorem `mul_mem` / 定理 `mul_mem`

English:
theorem mul_mem
  given: {x y : R}
  statement: x in s -> y in s -> x * y in s
  proof: mul_mem

中文:
定理 mul_mem
  条件: {x y : R}
  结论: x in s -> y in s -> x * y in s
  证明: mul_mem
-/
protected theorem mul_mem {x y : R} : x in s -> y in s -> x * y in s :=
  mul_mem

/--
theorem `add_mem` / 定理 `add_mem`

English:
theorem add_mem
  given: {x y : R}
  statement: x in s -> y in s -> x + y in s
  proof: add_mem

中文:
定理 add_mem
  条件: {x y : R}
  结论: x in s -> y in s -> x + y in s
  证明: add_mem
-/
protected theorem add_mem {x y : R} : x in s -> y in s -> x + y in s :=
  add_mem

/--
theorem `neg_mem` / 定理 `neg_mem`

English:
theorem neg_mem
  given: {x : R}
  statement: x in s -> -x in s
  proof: neg_mem

中文:
定理 neg_mem
  条件: {x : R}
  结论: x in s -> -x in s
  证明: neg_mem
-/
protected theorem neg_mem {x : R} : x in s -> -x in s :=
  neg_mem

/--
theorem `sub_mem` / 定理 `sub_mem`

English:
theorem sub_mem
  given: {x y : R} (hx : x in s) (hy : y in s)
  statement: x - y in s
  proof: sub_mem hx hy

中文:
定理 sub_mem
  条件: {x y : R} (hx : x in s) (hy : y in s)
  结论: x - y in s
  证明: sub_mem hx hy
-/
protected theorem sub_mem {x y : R} (hx : x in s) (hy : y in s) : x - y in s :=
  sub_mem hx hy

/--
Instance `toNonUnitalRing` / 实例 `toNonUnitalRing`

English:
instance toNonUnitalRing
  signature: {R : Type*} [NonUnitalRing R] (s : NonUnitalSubring R)
  body: NonUnitalSubringClass.toNonUnitalRing s

中文:
实例 toNonUnitalRing
  签名: {R : 类型} [非幺环 R] (s : NonUnital子环 R)
  定义体: NonUnitalSubringClass.toNonUnitalRing s

Depends on / 依赖: NonUnitalSubringClass, NonUnitalSubringClass.toNonUnitalRing, toNonUnitalRing
-/
instance toNonUnitalRing {R : Type*} [NonUnitalRing R] (s : NonUnitalSubring R) :
    NonUnitalRing s :=
  NonUnitalSubringClass.toNonUnitalRing s

/--
theorem `zsmul_mem` / 定理 `zsmul_mem`

English:
theorem zsmul_mem
  given: {x : R} (hx : x in s) (n : Int)
  statement: n • x in s
  proof: zsmul_mem hx n

@[simp, norm_cast]

中文:
定理 zsmul_mem
  条件: {x : R} (hx : x in s) (n : 整数)
  结论: n • x in s
  证明: zsmul_mem hx n

@[simp, norm_cast]
-/
protected theorem zsmul_mem {x : R} (hx : x in s) (n : Int) : n • x in s :=
  zsmul_mem hx n

@[simp, norm_cast]
/--
theorem `val_add` / 定理 `val_add`

English:
theorem val_add
  given: (x y : s)
  statement: (↑(x + y) : R) = ↑x + ↑y
  proof: rfl

@[simp, norm_cast]

中文:
定理 val_add
  条件: (x y : s)
  结论: (↑(x + y) : R) = ↑x + ↑y
  证明: rfl

@[simp, norm_cast]
-/
theorem val_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
/--
theorem `val_neg` / 定理 `val_neg`

English:
theorem val_neg
  given: (x : s)
  statement: (↑(-x) : R) = -↑x
  proof: rfl

@[simp, norm_cast]

中文:
定理 val_neg
  条件: (x : s)
  结论: (↑(-x) : R) = -↑x
  证明: rfl

@[simp, norm_cast]
-/
theorem val_neg (x : s) : (↑(-x) : R) = -↑x :=
  rfl

@[simp, norm_cast]
/--
theorem `val_mul` / 定理 `val_mul`

English:
theorem val_mul
  given: (x y : s)
  statement: (↑(x * y) : R) = ↑x * ↑y
  proof: rfl

@[simp, norm_cast]

中文:
定理 val_mul
  条件: (x y : s)
  结论: (↑(x * y) : R) = ↑x * ↑y
  证明: rfl

@[simp, norm_cast]
-/
theorem val_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
/--
theorem `val_zero` / 定理 `val_zero`

English:
theorem val_zero
  statement: ((0 : s) : R) = 0
  proof: rfl

中文:
定理 val_zero
  结论: ((0 : s) : R) = 0
  证明: rfl
-/
theorem val_zero : ((0 : s) : R) = 0 :=
  rfl

/--
theorem `coe_eq_zero_iff` / 定理 `coe_eq_zero_iff`

English:
theorem coe_eq_zero_iff
  given: {x : s}
  statement: (x : R) = 0 ↔ x = 0
  proof: by
  simp

中文:
定理 coe_eq_zero_iff
  条件: {x : s}
  结论: (x : R) = 0 ↔ x = 0
  证明: by
  simp
-/
theorem coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0 := by
  simp

/--
Instance `toNonUnitalCommRing` / 实例 `toNonUnitalCommRing`

English:
instance toNonUnitalCommRing
  signature: {R} [NonUnitalCommRing R] (s : NonUnitalSubring R)
  body: NonUnitalSubringClass.toNonUnitalCommRing s

中文:
实例 toNonUnitalCommRing
  签名: {R} [非幺交换环 R] (s : NonUnital子环 R)
  定义体: NonUnitalSubringClass.toNonUnitalCommRing s

Depends on / 依赖: NonUnitalSubringClass, NonUnitalSubringClass.toNonUnitalCommRing, toNonUnitalCommRing
-/
instance toNonUnitalCommRing {R} [NonUnitalCommRing R] (s : NonUnitalSubring R) :
    NonUnitalCommRing s :=
  NonUnitalSubringClass.toNonUnitalCommRing s



/--
theorem `mem_toSubsemigroup` / 定理 `mem_toSubsemigroup`

English:
theorem mem_toSubsemigroup
  given: {s : NonUnitalSubring R} {x : R}
  statement: x in s.toSubsemigroup ↔ x in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toSubsemigroup
  条件: {s : NonUnital子环 R} {x : R}
  结论: x in s.toSubsemigroup ↔ x in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubsemigroup {s : NonUnitalSubring R} {x : R} : x in s.toSubsemigroup ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `coe_toSubsemigroup` / 定理 `coe_toSubsemigroup`

English:
theorem coe_toSubsemigroup
  given: (s : NonUnitalSubring R)
  statement: (s.toSubsemigroup : Set R) = s
  proof: rfl

中文:
定理 coe_toSubsemigroup
  条件: (s : NonUnital子环 R)
  结论: (s.toSubsemigroup : 集合 R) = s
  证明: rfl
-/
theorem coe_toSubsemigroup (s : NonUnitalSubring R) : (s.toSubsemigroup : Set R) = s :=
  rfl

/--
theorem `mem_toAddSubgroup` / 定理 `mem_toAddSubgroup`

English:
theorem mem_toAddSubgroup
  given: {s : NonUnitalSubring R} {x : R}
  statement: x in s.toAddSubgroup ↔ x in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toAddSubgroup
  条件: {s : NonUnital子环 R} {x : R}
  结论: x in s.toAddSubgroup ↔ x in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toAddSubgroup {s : NonUnitalSubring R} {x : R} : x in s.toAddSubgroup ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `coe_toAddSubgroup` / 定理 `coe_toAddSubgroup`

English:
theorem coe_toAddSubgroup
  given: (s : NonUnitalSubring R)
  statement: (s.toAddSubgroup : Set R) = s
  proof: rfl

@[simp]

中文:
定理 coe_toAddSubgroup
  条件: (s : NonUnital子环 R)
  结论: (s.toAddSubgroup : 集合 R) = s
  证明: rfl

@[simp]
-/
theorem coe_toAddSubgroup (s : NonUnitalSubring R) : (s.toAddSubgroup : Set R) = s :=
  rfl

@[simp]
/--
theorem `mem_toNonUnitalSubsemiring` / 定理 `mem_toNonUnitalSubsemiring`

English:
theorem mem_toNonUnitalSubsemiring
  given: {s : NonUnitalSubring R} {x : R}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toNonUnitalSubsemiring
  条件: {s : NonUnital子环 R} {x : R}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toNonUnitalSubsemiring {s : NonUnitalSubring R} {x : R} :
    x in s.toNonUnitalSubsemiring ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `coe_toNonUnitalSubsemiring` / 定理 `coe_toNonUnitalSubsemiring`

English:
theorem coe_toNonUnitalSubsemiring
  given: (s : NonUnitalSubring R)
  proof: rfl

中文:
定理 coe_toNonUnitalSubsemiring
  条件: (s : NonUnital子环 R)
  证明: rfl
-/
theorem coe_toNonUnitalSubsemiring (s : NonUnitalSubring R) :
    (s.toNonUnitalSubsemiring : Set R) = s :=
  rfl

end NonUnitalSubring

end Basic

section Hom

namespace NonUnitalSubring

variable {R : Type u} [NonUnitalNonAssocRing R]

open NonUnitalRingHom

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {S T : NonUnitalSubring R} (h : S <= T)
  body: NonUnitalRingHom.codRestrict (NonUnitalSubringClass.subtype S) _ fun x => h x.2

中文:
定义 inclusion
  签名: {S T : NonUnital子环 R} (h : S <= T)
  定义体: NonUnitalRingHom.codRestrict (NonUnitalSubringClass.subtype S) _ fun x => h x.2

Depends on / 依赖: NonUnitalRingHom, NonUnitalRingHom.codRestrict, NonUnitalSubringClass, NonUnitalSubringClass.subtype, codRestrict, subtype
-/
def inclusion {S T : NonUnitalSubring R} (h : S <= T) : S ->ₙ+* T :=
  NonUnitalRingHom.codRestrict (NonUnitalSubringClass.subtype S) _ fun x => h x.2

end NonUnitalSubring

end Hom
