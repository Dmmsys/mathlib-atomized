/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Tactic.FastInstance

/-!
# Bundled non-unital subsemirings

We define bundled non-unital subsemirings and some standard constructions:
`subtype` and `inclusion` ring homomorphisms.
-/

@[expose] public section

assert_not_exists RelIso

universe u v w

section neg_mul

variable {R S : Type*} [Mul R] [HasDistribNeg R] [SetLike S R] [MulMemClass S R] {s : S}

/-- This lemma exists for `aesop`, as `aesop` simplifies `-x * y` to `-(x * y)` before applying
unsafe rules like `mul_mem`, leading to a dead end in cases where `neg_mem` does not hold. -/
@[aesop unsafe 80% (rule_sets := [SetLike])]
/--
theorem `neg_mul_mem` / 定理 `neg_mul_mem`

English:
theorem neg_mul_mem
  given: {x y : R} (hx : -x in s) (hy : y in s)
  statement: -(x * y) in s
  proof: by
  simpa using mul_mem hx hy

中文:
定理 neg_mul_mem
  条件: {x y : R} (hx : -x in s) (hy : y in s)
  结论: -(x * y) in s
  证明: by
  simpa using mul_mem hx hy

Depends on / 依赖: mul_mem
-/
theorem neg_mul_mem {x y : R} (hx : -x in s) (hy : y in s) : -(x * y) in s := by
  simpa using mul_mem hx hy

/-- This lemma exists for `aesop`, as `aesop` simplifies `x * -y` to `-(x * y)` before applying
unsafe rules like `mul_mem`, leading to a dead end in cases where `neg_mem` does not hold. -/
@[aesop unsafe 80% (rule_sets := [SetLike])]
/--
theorem `mul_neg_mem` / 定理 `mul_neg_mem`

English:
theorem mul_neg_mem
  given: {x y : R} (hx : x in s) (hy : -y in s)
  statement: -(x * y) in s
  proof: by
  simpa using mul_mem hx hy

中文:
定理 mul_neg_mem
  条件: {x y : R} (hx : x in s) (hy : -y in s)
  结论: -(x * y) in s
  证明: by
  simpa using mul_mem hx hy

Depends on / 依赖: mul_mem
-/
theorem mul_neg_mem {x y : R} (hx : x in s) (hy : -y in s) : -(x * y) in s := by
  simpa using mul_mem hx hy

-- doesn't work without the above `aesop` lemmas
example {x y z : R} (hx : x in s) (hy : -y in s) (hz : z in s) :
    x * (-y) * z in s := by aesop

end neg_mul

variable {R : Type u} {S : Type v} {T : Type w} [NonUnitalNonAssocSemiring R]

/--
Definition of `NonUnitalSubsemiringClass` / `NonUnitalSubsemiringClass` 的定义

English:
class NonUnitalSubsemiringClass
  parameters: (S : Type*) (R : outParam (Type u)) [NonUnitalNonAssocSemiring R]
  extends: AddSubmonoidClass S R
  axioms and operations (1):
    - mul_mem : forall {s : S} {a b : R}, a in s -> b in s -> a * b in s

中文:
类 NonUnitalSubsemiringClass
  参数: (S : 类型) (R : outParam (类型u)) [NonUnitalNonAssocSemiring R]
  继承: AddSubmonoidClass S R
  公理与运算 (1 个):
    - mul_mem : 对任意 {s : S} {a b : R}, a in s -> b in s -> a * b in s
-/
class NonUnitalSubsemiringClass (S : Type*) (R : outParam (Type u)) [NonUnitalNonAssocSemiring R]
    [SetLike S R] : Prop
  extends AddSubmonoidClass S R where
  mul_mem : forall {s : S} {a b : R}, a in s -> b in s -> a * b in s

-- See note [lower instance priority]
instance (priority := 100) NonUnitalSubsemiringClass.mulMemClass (S : Type*) (R : Type u)
    [NonUnitalNonAssocSemiring R] [SetLike S R] [h : NonUnitalSubsemiringClass S R] :
    MulMemClass S R :=
  { h with }

namespace NonUnitalSubsemiringClass

variable [SetLike S R] [NonUnitalSubsemiringClass S R] (s : S)

open AddSubmonoidClass

/- Prefer subclasses of `NonUnitalNonAssocSemiring` over subclasses of
`NonUnitalSubsemiringClass`. -/
/-- A non-unital subsemiring of a `NonUnitalNonAssocSemiring` inherits a
`NonUnitalNonAssocSemiring` structure -/
instance (priority := 75) toNonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring s := fast_instance%
  Subtype.coe_injective.nonUnitalNonAssocSemiring Subtype.val rfl (by simp) (fun _ _ => rfl)
    fun _ _ => rfl

/- Prefer subclasses of `NonUnitalNonAssocCommSemiring` over subclasses of
`NonUnitalSubsemiringClass`. -/
/-- A non-unital subsemiring of a `NonUnitalNonAssocCommSemiring` inherits a
`NonUnitalNonAssocCommSemiring` structure -/
instance (priority := 75) toNonUnitalNonAssocCommSemiring {R} [NonUnitalNonAssocCommSemiring R]
    [SetLike S R] [NonUnitalSubsemiringClass S R] :
    NonUnitalNonAssocCommSemiring s := fast_instance%
  Subtype.coe_injective.nonUnitalNonAssocCommSemiring Subtype.val rfl (by simp) (fun _ _ => rfl)
    fun _ _ => rfl

/--
Instance `noZeroDivisors` / 实例 `noZeroDivisors`

English:
instance noZeroDivisors
  signature: [NoZeroDivisors R]
  body: Subtype.coe_injective.noZeroDivisors Subtype.val rfl fun _ _ => rfl

中文:
实例 noZeroDivisors
  签名: [NoZeroDivisors R]
  定义体: Subtype.coe_injective.noZeroDivisors Subtype.val rfl fun _ _ => rfl

Depends on / 依赖: Subtype, Subtype.coe_injective.noZeroDivisors, Subtype.val, coe_injective, noZeroDivisors
-/
instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s :=
  Subtype.coe_injective.noZeroDivisors Subtype.val rfl fun _ _ => rfl

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : s ->ₙ+* R
  body: { AddSubmonoidClass.subtype s, MulMemClass.subtype s with toFun := (↑) }

中文:
定义 subtype
  签名: : s ->ₙ+* R
  定义体: { AddSubmonoidClass.subtype s, MulMemClass.subtype s with toFun := (↑) }

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.subtype, MulMemClass, MulMemClass.subtype, subtype
-/
def subtype : s ->ₙ+* R :=
  { AddSubmonoidClass.subtype s, MulMemClass.subtype s with toFun := (↑) }

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
  结论: Function.Injective (subtype s)
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
  statement: (subtype s : s -> R) = ((↑) : s -> R)
  proof: rfl

中文:
定理 coe_subtype
  结论: (subtype s : s -> R) = ((↑) : s -> R)
  证明: rfl
-/
theorem coe_subtype : (subtype s : s -> R) = ((↑) : s -> R) :=
  rfl

/--
Instance `toNonUnitalSemiring` / 实例 `toNonUnitalSemiring`

English:
instance toNonUnitalSemiring
  signature: {R} [NonUnitalSemiring R] [SetLike S R]
  body: fast_instance%
  Subtype.coe_injective.nonUnitalSemiring Subtype.val rfl (by simp) (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 toNonUnitalSemiring
  签名: {R} [NonUnitalSemiring R] [SetLike S R]
  定义体: fast_instance%
  Subtype.coe_injective.nonUnitalSemiring Subtype.val rfl (by simp) (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance toNonUnitalSemiring {R} [NonUnitalSemiring R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] : NonUnitalSemiring s := fast_instance%
  Subtype.coe_injective.nonUnitalSemiring Subtype.val rfl (by simp) (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `toNonUnitalCommSemiring` / 实例 `toNonUnitalCommSemiring`

English:
instance toNonUnitalCommSemiring
  signature: {R} [NonUnitalCommSemiring R] [SetLike S R]
  body: fast_instance%
  Subtype.coe_injective.nonUnitalCommSemiring Subtype.val rfl (by simp) (fun _ _ => rfl)
    fun _ _ => rfl

中文:
实例 toNonUnitalCommSemiring
  签名: {R} [NonUnitalCommSemiring R] [SetLike S R]
  定义体: fast_instance%
  Subtype.coe_injective.nonUnitalCommSemiring Subtype.val rfl (by simp) (fun _ _ => rfl)
    fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance toNonUnitalCommSemiring {R} [NonUnitalCommSemiring R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] : NonUnitalCommSemiring s := fast_instance%
  Subtype.coe_injective.nonUnitalCommSemiring Subtype.val rfl (by simp) (fun _ _ => rfl)
    fun _ _ => rfl

/-! Note: currently, there are no ordered versions of non-unital rings. -/

end NonUnitalSubsemiringClass

/--
Definition of `NonUnitalSubsemiring` / `NonUnitalSubsemiring` 的定义

English:
structure NonUnitalSubsemiring
  parameters: (R : Type u) [NonUnitalNonAssocSemiring R]
  extends: AddSubmonoid R, 
  (no additional axioms)

中文:
结构 NonUnitalSubsemiring
  参数: (R : 类型u) [NonUnitalNonAssocSemiring R]
  继承: AddSubmonoid R, 
  (无附加公理)
-/
structure NonUnitalSubsemiring (R : Type u) [NonUnitalNonAssocSemiring R] extends AddSubmonoid R,
  Subsemigroup R

/-- Reinterpret a `NonUnitalSubsemiring` as a `Subsemigroup`. -/
add_decl_doc NonUnitalSubsemiring.toSubsemigroup

/-- Reinterpret a `NonUnitalSubsemiring` as an `AddSubmonoid`. -/
add_decl_doc NonUnitalSubsemiring.toAddSubmonoid

namespace NonUnitalSubsemiring

/--
lemma `toAddSubmonoid_injective` / 引理 `toAddSubmonoid_injective`

English:
lemma toAddSubmonoid_injective
  proof: fun ⟨s, hs⟩ t => by congr!

中文:
引理 toAddSubmonoid_injective
  证明: fun ⟨s, hs⟩ t => by congr!
-/
lemma toAddSubmonoid_injective :
    (toAddSubmonoid : NonUnitalSubsemiring R -> AddSubmonoid R).Injective :=
  fun ⟨s, hs⟩ t => by congr!

/--
lemma `toAddSubmonoid_inj` / 引理 `toAddSubmonoid_inj`

English:
lemma toAddSubmonoid_inj
  given: {s t : NonUnitalSubsemiring R}
  proof: toAddSubmonoid_injective.eq_iff

中文:
引理 toAddSubmonoid_inj
  条件: {s t : NonUnitalSubsemiring R}
  证明: toAddSubmonoid_injective.eq_iff
-/
@[simp] lemma toAddSubmonoid_inj {s t : NonUnitalSubsemiring R} :
    s.toAddSubmonoid = t.toAddSubmonoid ↔ s = t := toAddSubmonoid_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (NonUnitalSubsemiring R) R
  body: s.carrier
  coe_injective := SetLike.coe_injective.comp toAddSubmonoid_injective

中文:
实例 :
  签名: SetLike (NonUnitalSubsemiring R) R
  定义体: s.carrier
  coe_injective := SetLike.coe_injective.comp toAddSubmonoid_injective

Depends on / 依赖: LocallyConvexSpace, LocallyConvexSpace.toLocallyPathConnectedSpace, Module, carrier, s.carrier, toLocallyPathConnectedSpace
-/
instance : SetLike (NonUnitalSubsemiring R) R where
  coe s := s.carrier
  coe_injective := SetLike.coe_injective.comp toAddSubmonoid_injective

/--
lemma `toSubsemigroup_injective` / 引理 `toSubsemigroup_injective`

English:
lemma toSubsemigroup_injective

中文:
引理 toSubsemigroup_injective
-/
lemma toSubsemigroup_injective :
    Function.Injective (toSubsemigroup : NonUnitalSubsemiring R -> Subsemigroup R)
  | _, _, h => SetLike.ext (SetLike.ext_iff.mp h :)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (NonUnitalSubsemiring R)
  body: .ofSetLike (NonUnitalSubsemiring R) R

中文:
实例 :
  签名: PartialOrder (NonUnitalSubsemiring R)
  定义体: .ofSetLike (NonUnitalSubsemiring R) R

Depends on / 依赖: NonUnitalSubsemiring, ofSetLike
-/
instance : PartialOrder (NonUnitalSubsemiring R) := .ofSetLike (NonUnitalSubsemiring R) R

/-- The actual `NonUnitalSubsemiring` obtained from an element of a `NonUnitalSubsemiringClass`. -/
@[simps]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: {S R : Type*} [NonUnitalNonAssocSemiring R] [SetLike S R]
  body: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem

中文:
定义 ofClass
  签名: {S R : 类型} [NonUnitalNonAssocSemiring R] [SetLike S R]
  定义体: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
-/
def ofClass {S R : Type*} [NonUnitalNonAssocSemiring R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] (s : S) : NonUnitalSubsemiring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem

instance (priority := 100) : CanLift (Set R) (NonUnitalSubsemiring R) (↑)
    (fun s => 0 in s ∧ (forall {x y}, x in s -> y in s -> x + y in s) ∧ forall {x y}, x in s -> y in s -> x * y in s)
    where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        mul_mem' := h.2.2 },
      rfl ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonUnitalSubsemiringClass (NonUnitalSubsemiring R) R
  body: AddSubmonoid.zero_mem' s.toAddSubmonoid
  add_mem {s} := AddSubsemigroup.add_mem' s.toAddSubmonoid.toAddSubsemigroup
  mul_mem {s} := mul_mem' s

中文:
实例 :
  签名: NonUnitalSubsemiringClass (NonUnitalSubsemiring R) R
  定义体: AddSubmonoid.zero_mem' s.toAddSubmonoid
  add_mem {s} := AddSubsemigroup.add_mem' s.toAddSubmonoid.toAddSubsemigroup
  mul_mem {s} := mul_mem' s

Depends on / 依赖: AddSubmonoid, AddSubmonoid.zero_mem, s.toAddSubmonoid, toAddSubmonoid, zero_mem
-/
instance : NonUnitalSubsemiringClass (NonUnitalSubsemiring R) R where
  zero_mem {s} := AddSubmonoid.zero_mem' s.toAddSubmonoid
  add_mem {s} := AddSubsemigroup.add_mem' s.toAddSubmonoid.toAddSubsemigroup
  mul_mem {s} := mul_mem' s

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : NonUnitalSubsemiring R} {x : R}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

中文:
定理 mem_carrier
  条件: {s : NonUnitalSubsemiring R} {x : R}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : NonUnitalSubsemiring R} {x : R} : x in s.carrier ↔ x in s :=
  Iff.rfl

/-- Two non-unital subsemirings are equal if they have the same elements. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : NonUnitalSubsemiring R} (h : forall x, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

中文:
定理 ext
  条件: {S T : NonUnitalSubsemiring R} (h : 对任意 x, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : NonUnitalSubsemiring R} (h : forall x, x in S ↔ x in T) : S = T :=
  SetLike.ext h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S)
  body: { S.toAddSubmonoid.copy s hs, S.toSubsemigroup.copy s hs with carrier := s }

@[simp]

中文:
定义 copy
  签名: (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S)
  定义体: { S.toAddSubmonoid.copy s hs, S.toSubsemigroup.copy s hs with carrier := s }

@[simp]
-/
protected def copy (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S) :
    NonUnitalSubsemiring R :=
  { S.toAddSubmonoid.copy s hs, S.toSubsemigroup.copy s hs with carrier := s }

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S)
  proof: rfl

中文:
定理 coe_copy
  条件: (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S)
  证明: rfl
-/
theorem coe_copy (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S) :
    (S.copy s hs : Set R) = s :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (s : Set R) (sg : Subsemigroup R) (hg : ↑sg = s) (sa : AddSubmonoid R)
  body: s
  zero_mem' := by subst ha; exact sa.zero_mem
  add_mem' := by subst ha; exact sa.add_mem
  mul_mem' := by subst hg; exact sg.mul_mem

@[simp]

中文:
定义 mk'
  签名: (s : Set R) (sg : Subsemigroup R) (hg : ↑sg = s) (sa : AddSubmonoid R)
  定义体: s
  zero_mem' := by subst ha; exact sa.zero_mem
  add_mem' := by subst ha; exact sa.add_mem
  mul_mem' := by subst hg; exact sg.mul_mem

@[simp]
-/
protected def mk' (s : Set R) (sg : Subsemigroup R) (hg : ↑sg = s) (sa : AddSubmonoid R)
    (ha : ↑sa = s) : NonUnitalSubsemiring R where
  carrier := s
  zero_mem' := by subst ha; exact sa.zero_mem
  add_mem' := by subst ha; exact sa.add_mem
  mul_mem' := by subst hg; exact sg.mul_mem

@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  statement: {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
  proof: rfl

@[simp]

中文:
定理 coe_mk'
  结论: {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
  证明: rfl

@[simp]
-/
theorem coe_mk' {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (NonUnitalSubsemiring.mk' s sg hg sa ha : Set R) = s :=
  rfl

@[simp]
/--
theorem `mem_mk'` / 定理 `mem_mk'`

English:
theorem mem_mk'
  statement: {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_mk'
  结论: {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk' {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) {x : R} : x in NonUnitalSubsemiring.mk' s sg hg sa ha ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `mk'_toSubsemigroup` / 定理 `mk'_toSubsemigroup`

English:
theorem mk'_toSubsemigroup
  statement: {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
  proof: SetLike.coe_injective hg.symm

@[simp]

中文:
定理 mk'_toSubsemigroup
  结论: {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
  证明: SetLike.coe_injective hg.symm

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, TopologicalSpace, coe_injective, hg.symm
-/
theorem mk'_toSubsemigroup {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (NonUnitalSubsemiring.mk' s sg hg sa ha).toSubsemigroup = sg :=
  SetLike.coe_injective hg.symm

@[simp]
/--
theorem `mk'_toAddSubmonoid` / 定理 `mk'_toAddSubmonoid`

English:
theorem mk'_toAddSubmonoid
  statement: {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
  proof: SetLike.coe_injective ha.symm

中文:
定理 mk'_toAddSubmonoid
  结论: {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
  证明: SetLike.coe_injective ha.symm
-/
theorem mk'_toAddSubmonoid {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (NonUnitalSubsemiring.mk' s sg hg sa ha).toAddSubmonoid = sa :=
  SetLike.coe_injective ha.symm

end NonUnitalSubsemiring

namespace NonUnitalSubsemiring

variable [NonUnitalNonAssocSemiring S]
variable {F : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S] (s : NonUnitalSubsemiring R)

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : s) : R) = (0 : R)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ((0 : s) : R) = (0 : R)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_zero : ((0 : s) : R) = (0 : R) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (x y : s)
  statement: ((x + y : s) : R) = (x + y : R)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  条件: (x y : s)
  结论: ((x + y : s) : R) = (x + y : R)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_add (x y : s) : ((x + y : s) : R) = (x + y : R) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : s)
  statement: ((x * y : s) : R) = (x * y : R)
  proof: rfl

中文:
定理 coe_mul
  条件: (x y : s)
  结论: ((x * y : s) : R) = (x * y : R)
  证明: rfl
-/
theorem coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R) :=
  rfl

/-! Note: currently, there are no ordered versions of non-unital rings. -/


@[simp high]
/--
theorem `mem_toSubsemigroup` / 定理 `mem_toSubsemigroup`

English:
theorem mem_toSubsemigroup
  given: {s : NonUnitalSubsemiring R} {x : R}
  statement: x in s.toSubsemigroup ↔ x in s
  proof: Iff.rfl

@[simp high]

中文:
定理 mem_toSubsemigroup
  条件: {s : NonUnitalSubsemiring R} {x : R}
  结论: x in s.toSubsemigroup ↔ x in s
  证明: Iff.rfl

@[simp high]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubsemigroup {s : NonUnitalSubsemiring R} {x : R} : x in s.toSubsemigroup ↔ x in s :=
  Iff.rfl

@[simp high]
/--
theorem `coe_toSubsemigroup` / 定理 `coe_toSubsemigroup`

English:
theorem coe_toSubsemigroup
  given: (s : NonUnitalSubsemiring R)
  statement: (s.toSubsemigroup : Set R) = s
  proof: rfl

@[simp]

中文:
定理 coe_toSubsemigroup
  条件: (s : NonUnitalSubsemiring R)
  结论: (s.toSubsemigroup : Set R) = s
  证明: rfl

@[simp]
-/
theorem coe_toSubsemigroup (s : NonUnitalSubsemiring R) : (s.toSubsemigroup : Set R) = s :=
  rfl

@[simp]
/--
theorem `mem_toAddSubmonoid` / 定理 `mem_toAddSubmonoid`

English:
theorem mem_toAddSubmonoid
  given: {s : NonUnitalSubsemiring R} {x : R}
  statement: x in s.toAddSubmonoid ↔ x in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toAddSubmonoid
  条件: {s : NonUnitalSubsemiring R} {x : R}
  结论: x in s.toAddSubmonoid ↔ x in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toAddSubmonoid {s : NonUnitalSubsemiring R} {x : R} : x in s.toAddSubmonoid ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `coe_toAddSubmonoid` / 定理 `coe_toAddSubmonoid`

English:
theorem coe_toAddSubmonoid
  given: (s : NonUnitalSubsemiring R)
  statement: (s.toAddSubmonoid : Set R) = s
  proof: rfl

中文:
定理 coe_toAddSubmonoid
  条件: (s : NonUnitalSubsemiring R)
  结论: (s.toAddSubmonoid : Set R) = s
  证明: rfl

Depends on / 依赖: IsTopologicalSemiring, _root_, _root_.IsTopologicalSemiring.toIsModuleTopology, toIsModuleTopology
-/
theorem coe_toAddSubmonoid (s : NonUnitalSubsemiring R) : (s.toAddSubmonoid : Set R) = s :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (NonUnitalSubsemiring R)
  body: ⟨{ (⊤ : Subsemigroup R), (⊤ : AddSubmonoid R) with }⟩

@[simp]

中文:
实例 :
  签名: Top (NonUnitalSubsemiring R)
  定义体: ⟨{ (⊤ : Subsemigroup R), (⊤ : AddSubmonoid R) with }⟩

@[simp]

Depends on / 依赖: AddSubmonoid, Subsemigroup
-/
instance : Top (NonUnitalSubsemiring R) :=
  ⟨{ (⊤ : Subsemigroup R), (⊤ : AddSubmonoid R) with }⟩

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: (x : R)
  statement: x in (⊤ : NonUnitalSubsemiring R)
  proof: Set.mem_univ x

@[simp]

中文:
定理 mem_top
  条件: (x : R)
  结论: x in (⊤ : NonUnitalSubsemiring R)
  证明: Set.mem_univ x

@[simp]

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mem_top (x : R) : x in (⊤ : NonUnitalSubsemiring R) :=
  Set.mem_univ x

@[simp]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : NonUnitalSubsemiring R) : Set R) = Set.univ
  proof: rfl

中文:
定理 coe_top
  结论: ((⊤ : NonUnitalSubsemiring R) : Set R) = Set.univ
  证明: rfl
-/
theorem coe_top : ((⊤ : NonUnitalSubsemiring R) : Set R) = Set.univ :=
  rfl

/--
lemma `toAddSubmonoid_top` / 引理 `toAddSubmonoid_top`

English:
lemma toAddSubmonoid_top
  statement: (⊤ : NonUnitalSubsemiring R).toAddSubmonoid = ⊤
  proof: rfl

@[simp]

中文:
引理 toAddSubmonoid_top
  结论: (⊤ : NonUnitalSubsemiring R).toAddSubmonoid = ⊤
  证明: rfl

@[simp]
-/
@[simp] lemma toAddSubmonoid_top : (⊤ : NonUnitalSubsemiring R).toAddSubmonoid = ⊤ := rfl

@[simp]
/--
lemma `toAddSubmonoid_eq_top` / 引理 `toAddSubmonoid_eq_top`

English:
lemma toAddSubmonoid_eq_top
  given: {S : NonUnitalSubsemiring R}
  statement: S.toAddSubmonoid = ⊤ ↔ S = ⊤
  proof: by
  simp [← SetLike.coe_set_eq]

中文:
引理 toAddSubmonoid_eq_top
  条件: {S : NonUnitalSubsemiring R}
  结论: S.toAddSubmonoid = ⊤ ↔ S = ⊤
  证明: by
  simp [← SetLike.coe_set_eq]

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq
-/
lemma toAddSubmonoid_eq_top {S : NonUnitalSubsemiring R} : S.toAddSubmonoid = ⊤ ↔ S = ⊤ := by
  simp [← SetLike.coe_set_eq]

end NonUnitalSubsemiring

namespace NonUnitalSubsemiring

-- should we define this as the range of the zero homomorphism?
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (NonUnitalSubsemiring R)
  body: ⟨{ carrier := {0}
      add_mem' := fun _ _ => by simp_all
      zero_mem' := Set.mem_singleton 0
      mul_mem' := fun _ _ => by simp_all }⟩

中文:
实例 :
  签名: Bot (NonUnitalSubsemiring R)
  定义体: ⟨{ carrier := {0}
      add_mem' := fun _ _ => by simp_all
      zero_mem' := Set.mem_singleton 0
      mul_mem' := fun _ _ => by simp_all }⟩

Depends on / 依赖: Set.mem_singleton, add_mem, carrier, mem_singleton, mul_mem, zero_mem
-/
instance : Bot (NonUnitalSubsemiring R) :=
  ⟨{ carrier := {0}
      add_mem' := fun _ _ => by simp_all
      zero_mem' := Set.mem_singleton 0
      mul_mem' := fun _ _ => by simp_all }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (NonUnitalSubsemiring R)
  body: ⟨⊥⟩

中文:
实例 :
  签名: Inhabited (NonUnitalSubsemiring R)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (NonUnitalSubsemiring R) :=
  ⟨⊥⟩

/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : NonUnitalSubsemiring R) : Set R) = {0}
  proof: rfl

中文:
定理 coe_bot
  结论: ((⊥ : NonUnitalSubsemiring R) : Set R) = {0}
  证明: rfl
-/
theorem coe_bot : ((⊥ : NonUnitalSubsemiring R) : Set R) = {0} :=
  rfl

/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: {x : R}
  statement: x in (⊥ : NonUnitalSubsemiring R) ↔ x = 0
  proof: Set.mem_singleton_iff

中文:
定理 mem_bot
  条件: {x : R}
  结论: x in (⊥ : NonUnitalSubsemiring R) ↔ x = 0
  证明: Set.mem_singleton_iff

Depends on / 依赖: Set.mem_singleton_iff, mem_singleton_iff
-/
theorem mem_bot {x : R} : x in (⊥ : NonUnitalSubsemiring R) ↔ x = 0 :=
  Set.mem_singleton_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (NonUnitalSubsemiring R)
  body: ⟨fun s t =>
    { s.toSubsemigroup ⊓ t.toSubsemigroup, s.toAddSubmonoid ⊓ t.toAddSubmonoid with
      carrier := s inter t }⟩

@[simp]

中文:
实例 :
  签名: Min (NonUnitalSubsemiring R)
  定义体: ⟨fun s t =>
    { s.toSubsemigroup ⊓ t.toSubsemigroup, s.toAddSubmonoid ⊓ t.toAddSubmonoid with
      carrier := s inter t }⟩

@[simp]

Depends on / 依赖: carrier, s.toAddSubmonoid, s.toSubsemigroup, t.toAddSubmonoid, t.toSubsemigroup, toAddSubmonoid, toSubsemigroup
-/
instance : Min (NonUnitalSubsemiring R) :=
  ⟨fun s t =>
    { s.toSubsemigroup ⊓ t.toSubsemigroup, s.toAddSubmonoid ⊓ t.toAddSubmonoid with
      carrier := s inter t }⟩

@[simp]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (p p' : NonUnitalSubsemiring R)
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (p p' : NonUnitalSubsemiring R)
  证明: rfl

@[simp]
-/
theorem coe_inf (p p' : NonUnitalSubsemiring R) :
    ((p ⊓ p' : NonUnitalSubsemiring R) : Set R) = (p : Set R) inter p' :=
  rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {p p' : NonUnitalSubsemiring R} {x : R}
  statement: x in p ⊓ p' ↔ x in p ∧ x in p'
  proof: Iff.rfl

中文:
定理 mem_inf
  条件: {p p' : NonUnitalSubsemiring R} {x : R}
  结论: x in p ⊓ p' ↔ x in p ∧ x in p'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {p p' : NonUnitalSubsemiring R} {x : R} : x in p ⊓ p' ↔ x in p ∧ x in p' :=
  Iff.rfl

end NonUnitalSubsemiring

namespace NonUnitalRingHom

variable {F : Type*} [FunLike F R S]

variable [NonUnitalNonAssocSemiring S]
  [NonUnitalRingHomClass F R S]
  {S' : Type*} [SetLike S' S] [NonUnitalSubsemiringClass S' S]
  {s : NonUnitalSubsemiring R}

open NonUnitalSubsemiringClass NonUnitalSubsemiring

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : F) (s : S') (h : forall x, f x in s)
  body: ⟨f n, h n⟩
  map_mul' x y := Subtype.ext (map_mul f x y)
  map_add' x y := Subtype.ext (map_add f x y)
  map_zero' := Subtype.ext (map_zero f)

中文:
定义 codRestrict
  签名: (f : F) (s : S') (h : 对任意 x, f x in s)
  定义体: ⟨f n, h n⟩
  map_mul' x y := Subtype.ext (map_mul f x y)
  map_add' x y := Subtype.ext (map_add f x y)
  map_zero' := Subtype.ext (map_zero f)
-/
def codRestrict (f : F) (s : S') (h : forall x, f x in s) : R ->ₙ+* s where
  toFun n := ⟨f n, h n⟩
  map_mul' x y := Subtype.ext (map_mul f x y)
  map_add' x y := Subtype.ext (map_add f x y)
  map_zero' := Subtype.ext (map_zero f)

/--
Definition of `eqSlocus` / `eqSlocus` 的定义

English:
definition eqSlocus
  signature: (f g : F)
  body: { (f : R ->ₙ* S).eqLocus (g : R ->ₙ* S), (f : R ->+ S).eqLocusM g with
    carrier := { x | f x = g x } }

中文:
定义 eqSlocus
  签名: (f g : F)
  定义体: { (f : R ->ₙ* S).eqLocus (g : R ->ₙ* S), (f : R ->+ S).eqLocusM g with
    carrier := { x | f x = g x } }

Depends on / 依赖: carrier, eqLocus, eqLocusM
-/
def eqSlocus (f g : F) : NonUnitalSubsemiring R :=
  { (f : R ->ₙ* S).eqLocus (g : R ->ₙ* S), (f : R ->+ S).eqLocusM g with
    carrier := { x | f x = g x } }

end NonUnitalRingHom

namespace NonUnitalSubsemiring

open NonUnitalRingHom NonUnitalSubsemiringClass

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {S T : NonUnitalSubsemiring R} (h : S <= T)
  body: codRestrict (subtype S) _ fun x => h x.2

中文:
定义 inclusion
  签名: {S T : NonUnitalSubsemiring R} (h : S <= T)
  定义体: codRestrict (subtype S) _ fun x => h x.2

Depends on / 依赖: codRestrict, subtype
-/
def inclusion {S T : NonUnitalSubsemiring R} (h : S <= T) : S ->ₙ+* T :=
  codRestrict (subtype S) _ fun x => h x.2

end NonUnitalSubsemiring
