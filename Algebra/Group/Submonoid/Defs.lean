/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Tactic.FastInstance
public import Mathlib.Data.Set.Insert

/-!
# Submonoids: definition

This file defines bundled multiplicative and additive submonoids. We also define
a `CompleteLattice` structure on `Submonoid`s, define the closure of a set as the minimal submonoid
that includes this set, and prove a few results about extending properties from a dense set (i.e.
a set with `closure s = ⊤`) to the whole monoid, see `Submonoid.dense_induction` and
`MonoidHom.ofClosureEqTopLeft`/`MonoidHom.ofClosureEqTopRight`.

## Main definitions

* `Submonoid M`: the type of bundled submonoids of a monoid `M`; the underlying set is given in
  the `carrier` field of the structure, and should be accessed through coercion as in `(S : Set M)`.
* `AddSubmonoid M` : the type of bundled submonoids of an additive monoid `M`.

For each of the following definitions in the `Submonoid` namespace, there is a corresponding
definition in the `AddSubmonoid` namespace.

* `Submonoid.copy` : copy of a submonoid with `carrier` replaced by a set that is equal but possibly
  not definitionally equal to the carrier of the original `Submonoid`.
* `MonoidHom.eqLocusM`: the submonoid of elements `x : M` such that `f x = g x`;

## Implementation notes

Submonoid inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a submonoid's underlying set.

Note that `Submonoid M` does not actually require `Monoid M`, instead requiring only the weaker
`MulOneClass M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers. `Submonoid` is implemented by extending `Subsemigroup` requiring `one_mem'`.

## Tags
submonoid, submonoids
-/

@[expose] public section

assert_not_exists RelIso CompleteLattice MonoidWithZero

variable {M : Type*} {N : Type*}

section NonAssoc

variable [MulOneClass M] {s : Set M}

/--
Definition of `OneMemClass` / `OneMemClass` 的定义

English:
class OneMemClass
  parameters: (S : Type*) (M : outParam Type*) [One M] [SetLike S M]
  axioms and operations (1):
    - one_mem : forall s : S, (1 : M) in s

中文:
类 OneMem类
  参数: (S : 类型) (M : outParam 类型) [幺 M] [集合状 S M]
  公理与运算 (1 个):
    - one_mem : 对任意 s : S, (1 : M) in s
-/
class OneMemClass (S : Type*) (M : outParam Type*) [One M] [SetLike S M] : Prop where
  /-- By definition, if we have `OneMemClass S M`, we have `1 ∈ s` for all `s : S`. -/
  one_mem : forall s : S, (1 : M) in s

export OneMemClass (one_mem)

/--
Definition of `ZeroMemClass` / `ZeroMemClass` 的定义

English:
class ZeroMemClass
  parameters: (S : Type*) (M : outParam Type*) [Zero M] [SetLike S M]
  axioms and operations (1):
    - zero_mem : forall s : S, (0 : M) in s

中文:
类 ZeroMem类
  参数: (S : 类型) (M : outParam 类型) [零 M] [集合状 S M]
  公理与运算 (1 个):
    - zero_mem : 对任意 s : S, (0 : M) in s

Depends on / 依赖: SetLike, one_mem, zero_mem
-/
class ZeroMemClass (S : Type*) (M : outParam Type*) [Zero M] [SetLike S M] : Prop where
  /-- By definition, if we have `ZeroMemClass S M`, we have `0 ∈ s` for all `s : S`. -/
  zero_mem : forall s : S, (0 : M) in s

export ZeroMemClass (zero_mem)

attribute [to_additive] OneMemClass

attribute [simp, aesop safe (rule_sets := [SetLike])] one_mem zero_mem

/-- The underlying set of a term of a `OneMemClass` is nonempty. -/
@[to_additive (attr := simp)
/-- The underlying set of a term of a `ZeroMemClass` is nonempty. -/]
/--
theorem `OneMemClass.coe_nonempty` / 定理 `OneMemClass.coe_nonempty`

English:
theorem OneMemClass.coe_nonempty
  given: {S M : Type*} [One M] [SetLike S M] [OneMemClass S M] (s : S)
  proof: ⟨1, one_mem s⟩

中文:
定理 OneMem类.coe_nonempty
  条件: {S M : 类型} [幺 M] [集合状 S M] [OneMem类 S M] (s : S)
  证明: ⟨1, one_mem s⟩

Depends on / 依赖: one_mem
-/
theorem OneMemClass.coe_nonempty {S M : Type*} [One M] [SetLike S M] [OneMemClass S M] (s : S) :
    (s : Set M).Nonempty :=
  ⟨1, one_mem s⟩

section

/--
Definition of `Submonoid` / `Submonoid` 的定义

English:
structure Submonoid
  parameters: (M : Type*) [MulOneClass M]
  extends: Subsemigroup M
  axioms and operations (1):
    - one_mem' : (1 : M) in carrier

中文:
结构 子幺半群
  参数: (M : 类型) [MulOne类 M]
  继承: 子半群 M
  公理与运算 (1 个):
    - one_mem' : (1 : M) in carrier
-/
structure Submonoid (M : Type*) [MulOneClass M] extends Subsemigroup M where
  /-- A submonoid contains `1`. -/
  one_mem' : (1 : M) in carrier

end

/-- A submonoid of a monoid `M` can be considered as a subsemigroup of that monoid. -/
add_decl_doc Submonoid.toSubsemigroup

/--
Definition of `SubmonoidClass` / `SubmonoidClass` 的定义

English:
class SubmonoidClass
  parameters: (S : Type*) (M : outParam Type*) [MulOneClass M] [SetLike S M]
  extends: MulMemClass S M, OneMemClass S M
  (no additional axioms)

中文:
类 子幺半群类
  参数: (S : 类型) (M : outParam 类型) [MulOne类 M] [集合状 S M]
  继承: MulMem类 S M, OneMem类 S M
  (无附加公理)
-/
class SubmonoidClass (S : Type*) (M : outParam Type*) [MulOneClass M] [SetLike S M] : Prop
    extends MulMemClass S M, OneMemClass S M

section

/--
Definition of `AddSubmonoid` / `AddSubmonoid` 的定义

English:
structure AddSubmonoid
  parameters: (M : Type*) [AddZeroClass M]
  extends: AddSubsemigroup M
  axioms and operations (1):
    - zero_mem' : (0 : M) in carrier

中文:
结构 加法子幺半群
  参数: (M : 类型) [加法零类 M]
  继承: 加法子半群 M
  公理与运算 (1 个):
    - zero_mem' : (0 : M) in carrier
-/
structure AddSubmonoid (M : Type*) [AddZeroClass M] extends AddSubsemigroup M where
  /-- An additive submonoid contains `0`. -/
  zero_mem' : (0 : M) in carrier

end

/-- An additive submonoid of an additive monoid `M` can be considered as an
additive subsemigroup of that additive monoid. -/
add_decl_doc AddSubmonoid.toAddSubsemigroup

/--
Definition of `AddSubmonoidClass` / `AddSubmonoidClass` 的定义

English:
class AddSubmonoidClass
  parameters: (S : Type*) (M : outParam Type*) [AddZeroClass M] [SetLike S M]
  extends: AddMemClass S M, ZeroMemClass S M
  (no additional axioms)

中文:
类 加法子幺半群类
  参数: (S : 类型) (M : outParam 类型) [加法零类 M] [集合状 S M]
  继承: 加法Mem类 S M, ZeroMem类 S M
  (无附加公理)
-/
class AddSubmonoidClass (S : Type*) (M : outParam Type*) [AddZeroClass M] [SetLike S M] : Prop
  extends AddMemClass S M, ZeroMemClass S M

attribute [to_additive] Submonoid SubmonoidClass

@[to_additive (attr := aesop 90% (rule_sets := [SetLike]))]
/--
theorem `pow_mem` / 定理 `pow_mem`

English:
theorem pow_mem
  statement: {M A} [Monoid M] [SetLike A M] [SubmonoidClass A M] {S : A} {x : M}

中文:
定理 pow_mem
  结论: {M A} [幺半群 M] [集合状 A M] [子幺半群类 A M] {S : A} {x : M}
-/
theorem pow_mem {M A} [Monoid M] [SetLike A M] [SubmonoidClass A M] {S : A} {x : M}
    (hx : x in S) : forall n : Nat, x ^ n in S
  | 0 => by
    rw [pow_zero]
    exact OneMemClass.one_mem S
  | n + 1 => by
    rw [pow_succ]
    exact mul_mem (pow_mem hx n) hx

namespace Submonoid

@[to_additive]
/--
lemma `toSubsemigroup_injective` / 引理 `toSubsemigroup_injective`

English:
lemma toSubsemigroup_injective
  statement: (toSubsemigroup : Submonoid M -> Subsemigroup M).Injective
  proof: fun ⟨s, hs⟩ ⟨t, ht⟩ => by congr!

@[to_additive (attr := simp)]

中文:
引理 toSubsemigroup_injective
  结论: (toSubsemigroup : 子幺半群 M -> 子半群 M).单射
  证明: fun ⟨s, hs⟩ ⟨t, ht⟩ => by congr!

@[to_additive (attr := simp)]
-/
lemma toSubsemigroup_injective : (toSubsemigroup : Submonoid M -> Subsemigroup M).Injective :=
  fun ⟨s, hs⟩ ⟨t, ht⟩ => by congr!

@[to_additive (attr := simp)]
/--
lemma `toSubsemigroup_inj` / 引理 `toSubsemigroup_inj`

English:
lemma toSubsemigroup_inj
  given: {s t : Submonoid M}
  statement: s.toSubsemigroup = t.toSubsemigroup ↔ s = t
  proof: toSubsemigroup_injective.eq_iff

@[to_additive]

中文:
引理 toSubsemigroup_inj
  条件: {s t : 子幺半群 M}
  结论: s.toSubsemigroup = t.toSubsemigroup ↔ s = t
  证明: toSubsemigroup_injective.eq_iff

@[to_additive]

Depends on / 依赖: eq_iff, toSubsemigroup_injective, toSubsemigroup_injective.eq_iff
-/
lemma toSubsemigroup_inj {s t : Submonoid M} : s.toSubsemigroup = t.toSubsemigroup ↔ s = t :=
  toSubsemigroup_injective.eq_iff

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Submonoid M) M
  body: s.carrier
  coe_injective := SetLike.coe_injective.comp toSubsemigroup_injective

中文:
实例 :
  签名: 集合状 (子幺半群 M) M
  定义体: s.carrier
  coe_injective := SetLike.coe_injective.comp toSubsemigroup_injective

Depends on / 依赖: carrier, s.carrier
-/
instance : SetLike (Submonoid M) M where
  coe s := s.carrier
  coe_injective := SetLike.coe_injective.comp toSubsemigroup_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Submonoid M)
  body: .ofSetLike (Submonoid M) M

initialize_simps_projections Submonoid (carrier -> coe, as_prefix coe)
initialize_simps_projections AddSubmonoid (carrier -> coe, as_prefix coe)

中文:
实例 :
  签名: 偏序 (子幺半群 M)
  定义体: .ofSetLike (Submonoid M) M

initialize_simps_projections Submonoid (carrier -> coe, as_prefix coe)
initialize_simps_projections AddSubmonoid (carrier -> coe, as_prefix coe)
-/
@[to_additive] instance : PartialOrder (Submonoid M) := .ofSetLike (Submonoid M) M

initialize_simps_projections Submonoid (carrier -> coe, as_prefix coe)
initialize_simps_projections AddSubmonoid (carrier -> coe, as_prefix coe)

/-- The actual `Submonoid` obtained from an element of a `SubmonoidClass` -/
@[to_additive (attr := simps) /-- The actual `AddSubmonoid` obtained from an element of a
`AddSubmonoidClass` -/]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: {S M : Type*} [Monoid M] [SetLike S M] [SubmonoidClass S M] (s : S)
  body: ⟨⟨s, MulMemClass.mul_mem⟩, OneMemClass.one_mem s⟩

@[to_additive]

中文:
定义 ofClass
  签名: {S M : 类型} [幺半群 M] [集合状 S M] [子幺半群类 S M] (s : S)
  定义体: ⟨⟨s, MulMemClass.mul_mem⟩, OneMemClass.one_mem s⟩

@[to_additive]

Depends on / 依赖: MulMemClass, MulMemClass.mul_mem, OneMemClass, OneMemClass.one_mem, mul_mem, one_mem
-/
def ofClass {S M : Type*} [Monoid M] [SetLike S M] [SubmonoidClass S M] (s : S) : Submonoid M :=
  ⟨⟨s, MulMemClass.mul_mem⟩, OneMemClass.one_mem s⟩

@[to_additive]
instance (priority := 100) : CanLift (Set M) (Submonoid M) (↑)
    (fun s => 1 in s ∧ forall {x y}, x in s -> y in s -> x * y in s) where
  prf s h := ⟨{ carrier := s, one_mem' := h.1, mul_mem' := h.2 }, rfl⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubmonoidClass (Submonoid M) M
  body: Submonoid.one_mem'
  mul_mem {s} := s.mul_mem'

@[to_additive (attr := simp)]

中文:
实例 :
  签名: 子幺半群类 (子幺半群 M) M
  定义体: Submonoid.one_mem'
  mul_mem {s} := s.mul_mem'

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid, Submonoid.one_mem, one_mem
-/
instance : SubmonoidClass (Submonoid M) M where
  one_mem := Submonoid.one_mem'
  mul_mem {s} := s.mul_mem'

@[to_additive (attr := simp)]
/--
theorem `mem_toSubsemigroup` / 定理 `mem_toSubsemigroup`

English:
theorem mem_toSubsemigroup
  given: {s : Submonoid M} {x : M}
  statement: x in s.toSubsemigroup ↔ x in s
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_toSubsemigroup
  条件: {s : 子幺半群 M} {x : M}
  结论: x in s.toSubsemigroup ↔ x in s
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubsemigroup {s : Submonoid M} {x : M} : x in s.toSubsemigroup ↔ x in s :=
  Iff.rfl

@[to_additive]
/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : Submonoid M} {x : M}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

@[to_additive (attr := simp)]

中文:
定理 mem_carrier
  条件: {s : 子幺半群 M} {x : M}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : Submonoid M} {x : M} : x in s.carrier ↔ x in s :=
  Iff.rfl

@[to_additive (attr := simp)]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {s : Subsemigroup M} {x : M} (h_one)
  statement: x in mk s h_one ↔ x in s
  proof: Iff.rfl

@[to_additive (attr := simp)]

中文:
定理 mem_mk
  条件: {s : 子半群 M} {x : M} (h_one)
  结论: x in mk s h_one ↔ x in s
  证明: Iff.rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk {s : Subsemigroup M} {x : M} (h_one) : x in mk s h_one ↔ x in s :=
  Iff.rfl

@[to_additive (attr := simp)]
/--
theorem `coe_set_mk` / 定理 `coe_set_mk`

English:
theorem coe_set_mk
  given: {s : Subsemigroup M} (h_one)
  statement: (mk s h_one : Set M) = s
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_set_mk
  条件: {s : 子半群 M} (h_one)
  结论: (mk s h_one : 集合 M) = s
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_set_mk {s : Subsemigroup M} (h_one) : (mk s h_one : Set M) = s :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: {s t : Subsemigroup M} (h_one) (h_one')
  statement: mk s h_one <= mk t h_one' ↔ s <= t
  proof: Iff.rfl

中文:
定理 mk_le_mk
  条件: {s t : 子半群 M} (h_one) (h_one')
  结论: mk s h_one <= mk t h_one' ↔ s <= t
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mk_le_mk {s t : Subsemigroup M} (h_one) (h_one') : mk s h_one <= mk t h_one' ↔ s <= t :=
  Iff.rfl

/-- Two submonoids are equal if they have the same elements. -/
@[to_additive (attr := ext) /-- Two `AddSubmonoid`s are equal if they have the same elements. -/]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : Submonoid M} (h : forall x, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

中文:
定理 ext
  条件: {S T : 子幺半群 M} (h : 对任意 x, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) : S = T :=
  SetLike.ext h

/-- Copy a submonoid replacing `carrier` with a set that is equal to it. -/
@[to_additive /-- Copy an additive submonoid replacing `carrier` with a set that is equal to it. -/]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : Submonoid M) (s : Set M) (hs : s = S)
  body: s
  one_mem' := show 1 in s from hs.symm ▸ S.one_mem'
  mul_mem' := hs.symm ▸ S.mul_mem'

中文:
定义 copy
  签名: (S : 子幺半群 M) (s : 集合 M) (hs : s = S)
  定义体: s
  one_mem' := show 1 in s from hs.symm ▸ S.one_mem'
  mul_mem' := hs.symm ▸ S.mul_mem'
-/
protected def copy (S : Submonoid M) (s : Set M) (hs : s = S) : Submonoid M where
  carrier := s
  one_mem' := show 1 in s from hs.symm ▸ S.one_mem'
  mul_mem' := hs.symm ▸ S.mul_mem'

variable {S : Submonoid M}

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: {s : Set M} (hs : s = S)
  statement: (S.copy s hs : Set M) = s
  proof: rfl

@[to_additive]

中文:
定理 coe_copy
  条件: {s : 集合 M} (hs : s = S)
  结论: (S.copy s hs : 集合 M) = s
  证明: rfl

@[to_additive]
-/
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl

@[to_additive]
/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: {s : Set M} (hs : s = S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: {s : 集合 M} (hs : s = S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S)

/-- A submonoid contains the monoid's 1. -/
@[to_additive /-- An `AddSubmonoid` contains the monoid's 0. -/]
/--
theorem `one_mem` / 定理 `one_mem`

English:
theorem one_mem
  statement: (1 : M) in S
  proof: one_mem S

中文:
定理 one_mem
  结论: (1 : M) in S
  证明: one_mem S
-/
protected theorem one_mem : (1 : M) in S :=
  one_mem S

/-- A submonoid is closed under multiplication. -/
@[to_additive /-- An `AddSubmonoid` is closed under addition. -/]
/--
theorem `mul_mem` / 定理 `mul_mem`

English:
theorem mul_mem
  given: {x y : M}
  statement: x in S -> y in S -> x * y in S
  proof: mul_mem

中文:
定理 mul_mem
  条件: {x y : M}
  结论: x in S -> y in S -> x * y in S
  证明: mul_mem
-/
protected theorem mul_mem {x y : M} : x in S -> y in S -> x * y in S :=
  mul_mem

/-- The submonoid `M` of the monoid `M`. -/
@[to_additive /-- The additive submonoid `M` of the `AddMonoid M`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (Submonoid M)
  body: ⟨{ carrier := Set.univ
      one_mem' := Set.mem_univ 1
      mul_mem' := fun _ _ => Set.mem_univ _ }⟩

中文:
实例 :
  签名: 顶元素 (子幺半群 M)
  定义体: ⟨{ carrier := Set.univ
      one_mem' := Set.mem_univ 1
      mul_mem' := fun _ _ => Set.mem_univ _ }⟩

Depends on / 依赖: Set.mem_univ, Set.univ, carrier, mem_univ, mul_mem, one_mem
-/
instance : Top (Submonoid M) :=
  ⟨{ carrier := Set.univ
      one_mem' := Set.mem_univ 1
      mul_mem' := fun _ _ => Set.mem_univ _ }⟩

/-- The trivial submonoid `{1}` of a monoid `M`. -/
@[to_additive /-- The trivial `AddSubmonoid` `{0}` of an `AddMonoid` `M`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (Submonoid M)
  body: ⟨{ carrier := {1}
      one_mem' := Set.mem_singleton 1
      mul_mem' := fun ha hb => by
        push _ in _ at *
        rw [ha]; rw [hb]; rw [mul_one] }⟩

@[to_additive]

中文:
实例 :
  签名: 底元素 (子幺半群 M)
  定义体: ⟨{ carrier := {1}
      one_mem' := Set.mem_singleton 1
      mul_mem' := fun ha hb => by
        push _ in _ at *
        rw [ha]; rw [hb]; rw [mul_one] }⟩

@[to_additive]

Depends on / 依赖: Set.mem_singleton, carrier, mem_singleton, mul_mem, mul_one, one_mem
-/
instance : Bot (Submonoid M) :=
  ⟨{ carrier := {1}
      one_mem' := Set.mem_singleton 1
      mul_mem' := fun ha hb => by
        push _ in _ at *
        rw [ha]; rw [hb]; rw [mul_one] }⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Submonoid M)
  body: ⟨⊥⟩

@[to_additive (attr := simp)]

中文:
实例 :
  签名: 可居 (子幺半群 M)
  定义体: ⟨⊥⟩

@[to_additive (attr := simp)]
-/
instance : Inhabited (Submonoid M) :=
  ⟨⊥⟩

@[to_additive (attr := simp)]
/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: {x : M}
  statement: x in (⊥ : Submonoid M) ↔ x = 1
  proof: Set.mem_singleton_iff

@[to_additive (attr := simp)]

中文:
定理 mem_bot
  条件: {x : M}
  结论: x in (⊥ : 子幺半群 M) ↔ x = 1
  证明: Set.mem_singleton_iff

@[to_additive (attr := simp)]

Depends on / 依赖: Set.mem_singleton_iff, mem_singleton_iff
-/
theorem mem_bot {x : M} : x in (⊥ : Submonoid M) ↔ x = 1 :=
  Set.mem_singleton_iff

@[to_additive (attr := simp)]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: (x : M)
  statement: x in (⊤ : Submonoid M)
  proof: Set.mem_univ x

@[to_additive (attr := simp, norm_cast)]

中文:
定理 mem_top
  条件: (x : M)
  结论: x in (⊤ : 子幺半群 M)
  证明: Set.mem_univ x

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mem_top (x : M) : x in (⊤ : Submonoid M) :=
  Set.mem_univ x

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : Submonoid M) : Set M) = Set.univ
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_top
  结论: ((⊤ : 子幺半群 M) : 集合 M) = 集合.univ
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_top : ((⊤ : Submonoid M) : Set M) = Set.univ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : Submonoid M) : Set M) = {1}
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_bot
  结论: ((⊥ : 子幺半群 M) : 集合 M) = {1}
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_bot : ((⊥ : Submonoid M) : Set M) = {1} :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `mk_eq_top` / 引理 `mk_eq_top`

English:
lemma mk_eq_top
  given: (toSubsemigroup : Subsemigroup M) (one_mem')
  proof: by simp [← SetLike.coe_set_eq]

@[to_additive (attr := simp)]

中文:
引理 mk_eq_top
  条件: (toSubsemigroup : 子半群 M) (one_mem')
  证明: by simp [← SetLike.coe_set_eq]

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq
-/
lemma mk_eq_top (toSubsemigroup : Subsemigroup M) (one_mem') :
    mk toSubsemigroup one_mem' = ⊤ ↔ toSubsemigroup = ⊤ := by simp [← SetLike.coe_set_eq]

@[to_additive (attr := simp)]
/--
lemma `mk_eq_bot` / 引理 `mk_eq_bot`

English:
lemma mk_eq_bot
  given: (toSubsemigroup : Subsemigroup M) (one_mem')
  proof: by
  simp [← SetLike.coe_set_eq]

中文:
引理 mk_eq_bot
  条件: (toSubsemigroup : 子半群 M) (one_mem')
  证明: by
  simp [← SetLike.coe_set_eq]

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq
-/
lemma mk_eq_bot (toSubsemigroup : Subsemigroup M) (one_mem') :
    mk toSubsemigroup one_mem' = ⊥ ↔ (toSubsemigroup : Set M) = {1} := by
  simp [← SetLike.coe_set_eq]

/-- The inf of two submonoids is their intersection. -/
@[to_additive /-- The inf of two `AddSubmonoid`s is their intersection. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Submonoid M)
  body: ⟨fun S₁ S₂ =>
    { carrier := S₁ inter S₂
      one_mem' := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 :
  签名: 最小值 (子幺半群 M)
  定义体: ⟨fun S₁ S₂ =>
    { carrier := S₁ inter S₂
      one_mem' := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: carrier, mul_mem, one_mem
-/
instance : Min (Submonoid M) :=
  ⟨fun S₁ S₂ =>
    { carrier := S₁ inter S₂
      one_mem' := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (p p' : Submonoid M)
  statement: ((p ⊓ p' : Submonoid M) : Set M) = (p : Set M) inter p'
  proof: rfl

@[to_additive (attr := simp, grind =)]

中文:
定理 coe_inf
  条件: (p p' : 子幺半群 M)
  结论: ((p ⊓ p' : 子幺半群 M) : 集合 M) = (p : 集合 M) inter p'
  证明: rfl

@[to_additive (attr := simp, grind =)]
-/
theorem coe_inf (p p' : Submonoid M) : ((p ⊓ p' : Submonoid M) : Set M) = (p : Set M) inter p' :=
  rfl

@[to_additive (attr := simp, grind =)]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {p p' : Submonoid M} {x : M}
  statement: x in p ⊓ p' ↔ x in p ∧ x in p'
  proof: Iff.rfl

@[to_additive (attr := simp)]

中文:
定理 mem_inf
  条件: {p p' : 子幺半群 M} {x : M}
  结论: x in p ⊓ p' ↔ x in p ∧ x in p'
  证明: Iff.rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {p p' : Submonoid M} {x : M} : x in p ⊓ p' ↔ x in p ∧ x in p' :=
  Iff.rfl

@[to_additive (attr := simp)]
/--
theorem `subsingleton_iff` / 定理 `subsingleton_iff`

English:
theorem subsingleton_iff
  statement: Subsingleton (Submonoid M) ↔ Subsingleton M
  proof: ⟨fun _ =>
    ⟨fun x y =>
      have : forall i : M, i = 1 := fun i =>
mem_bot.mp Subsingleton.elim (⊤ : Submonoid M) ⊥ ▸ mem_top i
      (this x).trans (this y).symm⟩,
    fun _ => ⟨fun x y => Submonoid.ext fun i => by simp [← Subsingleton.elim 1 i]⟩⟩

@[to_additive (attr := simp)]

中文:
定理 subsingleton_iff
  结论: 子单例 (子幺半群 M) ↔ 子单例 M
  证明: ⟨fun _ =>
    ⟨fun x y =>
      have : forall i : M, i = 1 := fun i =>
mem_bot.mp Subsingleton.elim (⊤ : Submonoid M) ⊥ ▸ mem_top i
      (this x).trans (this y).symm⟩,
    fun _ => ⟨fun x y => Submonoid.ext fun i => by simp [← Subsingleton.elim 1 i]⟩⟩

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid, Submonoid.ext, Subsingleton, Subsingleton.elim, mem_bot, mem_bot.mp, mem_top
-/
theorem subsingleton_iff : Subsingleton (Submonoid M) ↔ Subsingleton M :=
  ⟨fun _ =>
    ⟨fun x y =>
      have : forall i : M, i = 1 := fun i =>
mem_bot.mp Subsingleton.elim (⊤ : Submonoid M) ⊥ ▸ mem_top i
      (this x).trans (this y).symm⟩,
    fun _ => ⟨fun x y => Submonoid.ext fun i => by simp [← Subsingleton.elim 1 i]⟩⟩

@[to_additive (attr := simp)]
/--
theorem `nontrivial_iff` / 定理 `nontrivial_iff`

English:
theorem nontrivial_iff
  statement: Nontrivial (Submonoid M) ↔ Nontrivial M
  proof: not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans subsingleton_iff).trans
      not_nontrivial_iff_subsingleton.symm)

@[to_additive]

中文:
定理 nontrivial_iff
  结论: 非平凡 (子幺半群 M) ↔ 非平凡 M
  证明: not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans subsingleton_iff).trans
      not_nontrivial_iff_subsingleton.symm)

@[to_additive]

Depends on / 依赖: not_iff_not, not_iff_not.mp, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton.symm, not_nontrivial_iff_subsingleton.trans, subsingleton_iff
-/
theorem nontrivial_iff : Nontrivial (Submonoid M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans subsingleton_iff).trans
      not_nontrivial_iff_subsingleton.symm)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: M] : Unique (Submonoid M)
  body: ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ (subsingleton_iff.mpr ‹_›) a _⟩

@[to_additive]

中文:
实例 [子单例
  签名: M] : 唯一 (子幺半群 M)
  定义体: ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ (subsingleton_iff.mpr ‹_›) a _⟩

@[to_additive]

Depends on / 依赖: Subsingleton, Subsingleton.elim, subsingleton_iff, subsingleton_iff.mpr
-/
instance [Subsingleton M] : Unique (Submonoid M) :=
  ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ (subsingleton_iff.mpr ‹_›) a _⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: M] : Nontrivial (Submonoid M)
  body: nontrivial_iff.mpr ‹_›

中文:
实例 [非平凡
  签名: M] : 非平凡 (子幺半群 M)
  定义体: nontrivial_iff.mpr ‹_›

Depends on / 依赖: nontrivial_iff, nontrivial_iff.mpr
-/
instance [Nontrivial M] : Nontrivial (Submonoid M) :=
  nontrivial_iff.mpr ‹_›

end Submonoid

namespace MonoidHom

variable [MulOneClass N]

open Submonoid

/-- The submonoid of elements `x : M` such that `f x = g x` -/
@[to_additive /-- The additive submonoid of elements `x : M` such that `f x = g x` -/]
/--
Definition of `eqLocusM` / `eqLocusM` 的定义

English:
definition eqLocusM
  signature: (f g : M ->* N)
  body: { x | f x = g x }
  one_mem' := by rw [Set.mem_ofPred_eq, f.map_one, g.map_one]
  mul_mem' (hx : _ = _) (hy : _ = _) := by simp [*]

@[to_additive (attr := simp)]

中文:
定义 eqLocusM
  签名: (f g : M ->* N)
  定义体: { x | f x = g x }
  one_mem' := by rw [Set.mem_ofPred_eq, f.map_one, g.map_one]
  mul_mem' (hx : _ = _) (hy : _ = _) := by simp [*]

@[to_additive (attr := simp)]
-/
def eqLocusM (f g : M ->* N) : Submonoid M where
  carrier := { x | f x = g x }
  one_mem' := by rw [Set.mem_ofPred_eq, f.map_one, g.map_one]
  mul_mem' (hx : _ = _) (hy : _ = _) := by simp [*]

@[to_additive (attr := simp)]
/--
theorem `mem_eqLocusM` / 定理 `mem_eqLocusM`

English:
theorem mem_eqLocusM
  given: {f g : M ->* N} {x : M}
  statement: x in f.eqLocusM g ↔ f x = g x
  proof: Iff.rfl

@[to_additive (attr := simp)]

中文:
定理 mem_eqLocusM
  条件: {f g : M ->* N} {x : M}
  结论: x in f.eqLocusM g ↔ f x = g x
  证明: Iff.rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_eqLocusM {f g : M ->* N} {x : M} : x in f.eqLocusM g ↔ f x = g x := Iff.rfl

@[to_additive (attr := simp)]
/--
theorem `eqLocusM_same` / 定理 `eqLocusM_same`

English:
theorem eqLocusM_same
  given: (f : M ->* N)
  statement: f.eqLocusM f = ⊤
  proof: SetLike.ext fun _ => eq_self_iff_true _

@[to_additive]

中文:
定理 eqLocusM_same
  条件: (f : M ->* N)
  结论: f.eqLocusM f = ⊤
  证明: SetLike.ext fun _ => eq_self_iff_true _

@[to_additive]

Depends on / 依赖: SetLike, SetLike.ext, eq_self_iff_true
-/
theorem eqLocusM_same (f : M ->* N) : f.eqLocusM f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

@[to_additive]
/--
theorem `eq_of_eqOn_topM` / 定理 `eq_of_eqOn_topM`

English:
theorem eq_of_eqOn_topM
  given: {f g : M ->* N} (h : Set.EqOn f g (⊤ : Submonoid M))
  statement: f = g
  proof: ext fun _ => h trivial

中文:
定理 eq_of_eqOn_topM
  条件: {f g : M ->* N} (h : 集合.EqOn f g (⊤ : 子幺半群 M))
  结论: f = g
  证明: ext fun _ => h trivial
-/
theorem eq_of_eqOn_topM {f g : M ->* N} (h : Set.EqOn f g (⊤ : Submonoid M)) : f = g :=
  ext fun _ => h trivial

end MonoidHom

end NonAssoc

namespace OneMemClass

variable {A M₁ : Type*} [SetLike A M₁] [One M₁] [hA : OneMemClass A M₁] (S' : A)

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits a zero. -/]
/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One S'
  body: ⟨⟨1, OneMemClass.one_mem S'⟩⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 one
  签名: : 幺 S'
  定义体: ⟨⟨1, OneMemClass.one_mem S'⟩⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: OneMemClass, OneMemClass.one_mem, one_mem
-/
instance one : One S' :=
  ⟨⟨1, OneMemClass.one_mem S'⟩⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : S') : M₁) = 1
  proof: rfl

中文:
定理 coe_one
  结论: ((1 : S') : M₁) = 1
  证明: rfl
-/
theorem coe_one : ((1 : S') : M₁) = 1 :=
  rfl

variable {S'}

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_eq_one` / 定理 `coe_eq_one`

English:
theorem coe_eq_one
  given: {x : S'}
  statement: (↑x : M₁) = 1 ↔ x = 1
  proof: (Subtype.ext_iff.symm : (x : M₁) = (1 : S') ↔ x = 1)

中文:
定理 coe_eq_one
  条件: {x : S'}
  结论: (↑x : M₁) = 1 ↔ x = 1
  证明: (Subtype.ext_iff.symm : (x : M₁) = (1 : S') ↔ x = 1)

Depends on / 依赖: Subtype, Subtype.ext_iff.symm, ext_iff
-/
theorem coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1 :=
  (Subtype.ext_iff.symm : (x : M₁) = (1 : S') ↔ x = 1)

variable (S')

@[to_additive]
/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : S') = ⟨1, OneMemClass.one_mem S'⟩
  proof: rfl

中文:
定理 one_def
  结论: (1 : S') = ⟨1, OneMem类.one_mem S'⟩
  证明: rfl
-/
theorem one_def : (1 : S') = ⟨1, OneMemClass.one_mem S'⟩ :=
  rfl

end OneMemClass

variable {A : Type*} [MulOneClass M] [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

namespace SubmonoidClass

/-- A submonoid of a monoid inherits a power operator. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits a scalar multiplication. -/]
/--
Instance `instPow` / 实例 `instPow`

English:
instance instPow
  signature: {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] (S : A)
  body: ⟨fun a n => ⟨a.1 ^ n, pow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 instPow
  签名: {M} [幺半群 M] {A : 类型} [集合状 A M] [子幺半群类 A M] (S : A)
  定义体: ⟨fun a n => ⟨a.1 ^ n, pow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: pow_mem
-/
instance instPow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] (S : A) : Pow S Nat :=
  ⟨fun a n => ⟨a.1 ^ n, pow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  statement: {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] {S : A} (x : S)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_pow
  结论: {M} [幺半群 M] {A : 类型} [集合状 A M] [子幺半群类 A M] {S : A} (x : S)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_pow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] {S : A} (x : S)
    (n : Nat) : ↑(x ^ n) = (x : M) ^ n :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mk_pow` / 定理 `mk_pow`

English:
theorem mk_pow
  statement: {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] {S : A} (x : M)
  proof: rfl

中文:
定理 mk_pow
  结论: {M} [幺半群 M] {A : 类型} [集合状 A M] [子幺半群类 A M] {S : A} (x : M)
  证明: rfl
-/
theorem mk_pow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] {S : A} (x : M)
    (hx : x in S) (n : Nat) : (⟨x, hx⟩ : S) ^ n = ⟨x ^ n, pow_mem hx n⟩ :=
  rfl

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive
  /-- An `AddSubmonoid` of a unital additive magma inherits a unital additive magma structure. -/]
instance (priority := 75) toMulOneClass {M : Type*} [MulOneClass M] {A : Type*} [SetLike A M]
    [SubmonoidClass A M] (S : A) : MulOneClass S := fast_instance%
  Subtype.coe_injective.mulOneClass Subtype.val rfl (fun _ _ => rfl)

instance (S : A) [IsDedekindFiniteMonoid M] : IsDedekindFiniteMonoid S where
  mul_eq_one_symm eq := Subtype.ext (mul_eq_one_symm <| congr_arg (·.1) eq)

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits an `AddMonoid` structure. -/]
instance (priority := 75) toMonoid {M : Type*} [Monoid M] {A : Type*} [SetLike A M]
    [SubmonoidClass A M] (S : A) : Monoid S := fast_instance%
  Subtype.coe_injective.monoid Subtype.val rfl (fun _ _ => rfl) (fun _ _ => rfl)

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a `CommMonoid` is a `CommMonoid`. -/
@[to_additive /-- An `AddSubmonoid` of an `AddCommMonoid` is an `AddCommMonoid`. -/]
instance (priority := 75) toCommMonoid {M} [CommMonoid M] {A : Type*} [SetLike A M]
    [SubmonoidClass A M] (S : A) : CommMonoid S := fast_instance%
  Subtype.coe_injective.commMonoid Subtype.val rfl (fun _ _ => rfl) fun _ _ => rfl

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive /-- The natural monoid hom from an `AddSubmonoid` of `AddMonoid` `M` to `M`. -/]
/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : S' ->* M where
  body: Subtype.val; map_one' := rfl; map_mul' _ _ := by simp

中文:
定义 subtype
  签名: : S' ->* M where
  定义体: Subtype.val; map_one' := rfl; map_mul' _ _ := by simp

Depends on / 依赖: Subtype, Subtype.val, map_mul, map_one
-/
def subtype : S' ->* M where
  toFun := Subtype.val; map_one' := rfl; map_mul' _ _ := by simp

variable {S'} in
@[to_additive (attr := simp)]
/--
lemma `subtype_apply` / 引理 `subtype_apply`

English:
lemma subtype_apply
  given: (x : S')
  proof: rfl

@[to_additive]

中文:
引理 subtype_apply
  条件: (x : S')
  证明: rfl

@[to_additive]
-/
lemma subtype_apply (x : S') :
    SubmonoidClass.subtype S' x = x := rfl

@[to_additive]
/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  proof: Subtype.coe_injective

@[to_additive (attr := simp)]

中文:
引理 subtype_injective
  证明: Subtype.coe_injective

@[to_additive (attr := simp)]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
lemma subtype_injective :
    Function.Injective (SubmonoidClass.subtype S') :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: (SubmonoidClass.subtype S' : S' -> M) = Subtype.val
  proof: rfl

中文:
定理 coe_subtype
  结论: (子幺半群类.subtype S' : S' -> M) = 子类型.val
  证明: rfl
-/
theorem coe_subtype : (SubmonoidClass.subtype S' : S' -> M) = Subtype.val :=
  rfl

end SubmonoidClass

namespace Submonoid

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

/-- A submonoid of a monoid inherits a multiplication. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits an addition. -/]
/--
Instance `mul` / 实例 `mul`

English:
instance mul
  signature: : Mul S
  body: ⟨fun a b => ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩

中文:
实例 mul
  签名: : 乘法 S
  定义体: ⟨fun a b => ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩

Depends on / 依赖: S.mul_mem, mul_mem
-/
instance mul : Mul S :=
  ⟨fun a b => ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits a zero. -/]
/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One S
  body: ⟨⟨_, S.one_mem⟩⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 one
  签名: : 幺 S
  定义体: ⟨⟨_, S.one_mem⟩⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: S.one_mem, one_mem
-/
instance one : One S :=
  ⟨⟨_, S.one_mem⟩⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : S)
  statement: (↑(x * y) : M) = ↑x * ↑y
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_mul
  条件: (x y : S)
  结论: (↑(x * y) : M) = ↑x * ↑y
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : S) : M) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_one
  结论: ((1 : S) : M) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_one : ((1 : S) : M) = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `mk_eq_one` / 引理 `mk_eq_one`

English:
lemma mk_eq_one
  given: {a : M} {ha}
  statement: (⟨a, ha⟩ : S) = 1 ↔ a = 1
  proof: by simp [← SetLike.coe_eq_coe]

@[to_additive (attr := simp)]

中文:
引理 mk_eq_one
  条件: {a : M} {ha}
  结论: (⟨a, ha⟩ : S) = 1 ↔ a = 1
  证明: by simp [← SetLike.coe_eq_coe]

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.coe_eq_coe, coe_eq_coe
-/
lemma mk_eq_one {a : M} {ha} : (⟨a, ha⟩ : S) = 1 ↔ a = 1 := by simp [← SetLike.coe_eq_coe]

@[to_additive (attr := simp)]
/--
theorem `mk_mul_mk` / 定理 `mk_mul_mk`

English:
theorem mk_mul_mk
  given: (x y : M) (hx : x in S) (hy : y in S)
  proof: rfl

@[to_additive]

中文:
定理 mk_mul_mk
  条件: (x y : M) (hx : x in S) (hy : y in S)
  证明: rfl

@[to_additive]
-/
theorem mk_mul_mk (x y : M) (hx : x in S) (hy : y in S) :
    (⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨x * y, S.mul_mem hx hy⟩ :=
  rfl

@[to_additive]
/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (x y : S)
  statement: x * y = ⟨x * y, S.mul_mem x.2 y.2⟩
  proof: rfl

@[to_additive]

中文:
定理 mul_def
  条件: (x y : S)
  结论: x * y = ⟨x * y, S.mul_mem x.2 y.2⟩
  证明: rfl

@[to_additive]
-/
theorem mul_def (x y : S) : x * y = ⟨x * y, S.mul_mem x.2 y.2⟩ :=
  rfl

@[to_additive]
/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : S) = ⟨1, S.one_mem⟩
  proof: rfl

中文:
定理 one_def
  结论: (1 : S) = ⟨1, S.one_mem⟩
  证明: rfl
-/
theorem one_def : (1 : S) = ⟨1, S.one_mem⟩ :=
  rfl

/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive
  /-- An `AddSubmonoid` of a unital additive magma inherits a unital additive magma structure. -/]
/--
Instance `toMulOneClass` / 实例 `toMulOneClass`

English:
instance toMulOneClass
  signature: {M : Type*} [MulOneClass M] (S : Submonoid M)
  body: SubmonoidClass.toMulOneClass S

@[to_additive]

中文:
实例 toMulOneClass
  签名: {M : 类型} [MulOne类 M] (S : 子幺半群 M)
  定义体: SubmonoidClass.toMulOneClass S

@[to_additive]

Depends on / 依赖: SubmonoidClass, SubmonoidClass.toMulOneClass, toMulOneClass
-/
instance toMulOneClass {M : Type*} [MulOneClass M] (S : Submonoid M) : MulOneClass S :=
  SubmonoidClass.toMulOneClass S

@[to_additive]
/--
theorem `pow_mem` / 定理 `pow_mem`

English:
theorem pow_mem
  given: {M : Type*} [Monoid M] (S : Submonoid M) {x : M} (hx : x in S) (n : Nat)
  proof: pow_mem hx n

中文:
定理 pow_mem
  条件: {M : 类型} [幺半群 M] (S : 子幺半群 M) {x : M} (hx : x in S) (n : 自然数)
  证明: pow_mem hx n
-/
protected theorem pow_mem {M : Type*} [Monoid M] (S : Submonoid M) {x : M} (hx : x in S) (n : Nat) :
    x ^ n in S :=
  pow_mem hx n

/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits an `AddMonoid` structure. -/]
/--
Instance `toMonoid` / 实例 `toMonoid`

English:
instance toMonoid
  signature: {M : Type*} [Monoid M] (S : Submonoid M)
  body: SubmonoidClass.toMonoid S

中文:
实例 toMonoid
  签名: {M : 类型} [幺半群 M] (S : 子幺半群 M)
  定义体: SubmonoidClass.toMonoid S

Depends on / 依赖: SubmonoidClass, SubmonoidClass.toMonoid, toMonoid
-/
instance toMonoid {M : Type*} [Monoid M] (S : Submonoid M) : Monoid S :=
  SubmonoidClass.toMonoid S

/-- A submonoid of a `CommMonoid` is a `CommMonoid`. -/
@[to_additive /-- An `AddSubmonoid` of an `AddCommMonoid` is an `AddCommMonoid`. -/]
/--
Instance `toCommMonoid` / 实例 `toCommMonoid`

English:
instance toCommMonoid
  signature: {M} [CommMonoid M] (S : Submonoid M)
  body: SubmonoidClass.toCommMonoid S

中文:
实例 toCommMonoid
  签名: {M} [交换幺半群 M] (S : 子幺半群 M)
  定义体: SubmonoidClass.toCommMonoid S

Depends on / 依赖: SubmonoidClass, SubmonoidClass.toCommMonoid, toCommMonoid
-/
instance toCommMonoid {M} [CommMonoid M] (S : Submonoid M) : CommMonoid S :=
  SubmonoidClass.toCommMonoid S

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive /-- The natural monoid hom from an `AddSubmonoid` of `AddMonoid` `M` to `M`. -/]
/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : S ->* M where
  body: Subtype.val; map_one' := rfl; map_mul' _ _ := by simp

@[to_additive (attr := simp)]

中文:
定义 subtype
  签名: : S ->* M where
  定义体: Subtype.val; map_one' := rfl; map_mul' _ _ := by simp

@[to_additive (attr := simp)]

Depends on / 依赖: Subtype, Subtype.val, map_mul, map_one
-/
def subtype : S ->* M where
  toFun := Subtype.val; map_one' := rfl; map_mul' _ _ := by simp

@[to_additive (attr := simp)]
/--
lemma `subtype_apply` / 引理 `subtype_apply`

English:
lemma subtype_apply
  given: {s : Submonoid M} (x : s)
  proof: rfl

@[to_additive]

中文:
引理 subtype_apply
  条件: {s : 子幺半群 M} (x : s)
  证明: rfl

@[to_additive]
-/
lemma subtype_apply {s : Submonoid M} (x : s) :
    s.subtype x = x := rfl

@[to_additive]
/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  given: (s : Submonoid M)
  proof: Subtype.coe_injective

@[to_additive (attr := simp)]

中文:
引理 subtype_injective
  条件: (s : 子幺半群 M)
  证明: Subtype.coe_injective

@[to_additive (attr := simp)]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
lemma subtype_injective (s : Submonoid M) :
    Function.Injective s.subtype :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: ⇑S.subtype = Subtype.val
  proof: rfl

中文:
定理 coe_subtype
  结论: ⇑S.subtype = 子类型.val
  证明: rfl
-/
theorem coe_subtype : ⇑S.subtype = Subtype.val :=
  rfl

end Submonoid
