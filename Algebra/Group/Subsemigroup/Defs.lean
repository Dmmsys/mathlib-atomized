/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Tactic.FastInstance

/-!
# Subsemigroups: definition

This file defines bundled multiplicative and additive subsemigroups.

## Main definitions

* `Subsemigroup M`: the type of bundled subsemigroup of a magma `M`; the underlying set is given in
  the `carrier` field of the structure, and should be accessed through coercion as in `(S : Set M)`.
* `AddSubsemigroup M` : the type of bundled subsemigroups of an additive magma `M`.

For each of the following definitions in the `Subsemigroup` namespace, there is a corresponding
definition in the `AddSubsemigroup` namespace.

* `Subsemigroup.copy` : copy of a subsemigroup with `carrier` replaced by a set that is equal but
  possibly not definitionally equal to the carrier of the original `Subsemigroup`.

Similarly, for each of these definitions in the `MulHom` namespace, there is a corresponding
definition in the `AddHom` namespace.

* `MulHom.eqLocus f g`: the subsemigroup of those `x` such that `f x = g x`

## Implementation notes

Subsemigroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subsemigroup's underlying set.

Note that `Subsemigroup M` does not actually require `Semigroup M`,
instead requiring only the weaker `Mul M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers.

## Tags
subsemigroup, subsemigroups
-/

@[expose] public section

assert_not_exists RelIso CompleteLattice MonoidWithZero

variable {M : Type*} {N : Type*}

section NonAssoc

variable [Mul M] {s : Set M}

/--
Definition of `MulMemClass` / `MulMemClass` 的定义

English:
class MulMemClass
  parameters: (S : Type*) (M : outParam Type*) [Mul M] [SetLike S M]
  axioms and operations (1):
    - mul_mem : forall {s : S} {a b : M}, a in s -> b in s -> a * b in s

中文:
类 MulMem类
  参数: (S : 类型) (M : outParam 类型) [乘法 M] [集合状 S M]
  公理与运算 (1 个):
    - mul_mem : 对任意 {s : S} {a b : M}, a in s -> b in s -> a * b in s
-/
class MulMemClass (S : Type*) (M : outParam Type*) [Mul M] [SetLike S M] : Prop where
  /-- A substructure satisfying `MulMemClass` is closed under multiplication. -/
  mul_mem : forall {s : S} {a b : M}, a in s -> b in s -> a * b in s

export MulMemClass (mul_mem)

/--
Definition of `AddMemClass` / `AddMemClass` 的定义

English:
class AddMemClass
  parameters: (S : Type*) (M : outParam Type*) [Add M] [SetLike S M]
  axioms and operations (1):
    - add_mem : forall {s : S} {a b : M}, a in s -> b in s -> a + b in s

中文:
类 加法Mem类
  参数: (S : 类型) (M : outParam 类型) [加法 M] [集合状 S M]
  公理与运算 (1 个):
    - add_mem : 对任意 {s : S} {a b : M}, a in s -> b in s -> a + b in s

Depends on / 依赖: SetLike, add_mem, mul_mem
-/
class AddMemClass (S : Type*) (M : outParam Type*) [Add M] [SetLike S M] : Prop where
  /-- A substructure satisfying `AddMemClass` is closed under addition. -/
  add_mem : forall {s : S} {a b : M}, a in s -> b in s -> a + b in s

export AddMemClass (add_mem)

attribute [to_additive] MulMemClass

attribute [aesop 90% (rule_sets := [SetLike])] mul_mem add_mem

/--
Definition of `Subsemigroup` / `Subsemigroup` 的定义

English:
structure Subsemigroup
  parameters: (M : Type*) [Mul M]
  axioms and operations (2):
    - carrier : Set M
    - mul_mem'({a b}) : a in carrier -> b in carrier -> a * b in carrier

中文:
结构 子半群
  参数: (M : 类型) [乘法 M]
  公理与运算 (2 个):
    - carrier : 集合 M
    - mul_mem'({a b}) : a in carrier -> b in carrier -> a * b in carrier
-/
structure Subsemigroup (M : Type*) [Mul M] where
  /-- The carrier of a subsemigroup. -/
  carrier : Set M
  /-- The product of two elements of a subsemigroup belongs to the subsemigroup. -/
  mul_mem' {a b} : a in carrier -> b in carrier -> a * b in carrier

/--
Definition of `AddSubsemigroup` / `AddSubsemigroup` 的定义

English:
structure AddSubsemigroup
  parameters: (M : Type*) [Add M]
  axioms and operations (2):
    - carrier : Set M
    - add_mem'({a b}) : a in carrier -> b in carrier -> a + b in carrier

中文:
结构 加法子半群
  参数: (M : 类型) [加法 M]
  公理与运算 (2 个):
    - carrier : 集合 M
    - add_mem'({a b}) : a in carrier -> b in carrier -> a + b in carrier
-/
structure AddSubsemigroup (M : Type*) [Add M] where
  /-- The carrier of an additive subsemigroup. -/
  carrier : Set M
  /-- The sum of two elements of an additive subsemigroup belongs to the subsemigroup. -/
  add_mem' {a b} : a in carrier -> b in carrier -> a + b in carrier

attribute [to_additive AddSubsemigroup] Subsemigroup

namespace Subsemigroup

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Subsemigroup M) M
  body: ⟨Subsemigroup.carrier, fun p q h => by cases p; cases q; congr⟩

中文:
实例 :
  签名: 集合状 (子半群 M) M
  定义体: ⟨Subsemigroup.carrier, fun p q h => by cases p; cases q; congr⟩

Depends on / 依赖: Subsemigroup, Subsemigroup.carrier, carrier
-/
instance : SetLike (Subsemigroup M) M :=
  ⟨Subsemigroup.carrier, fun p q h => by cases p; cases q; congr⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Subsemigroup M)
  body: .ofSetLike (Subsemigroup M) M

initialize_simps_projections Subsemigroup (carrier -> coe, as_prefix coe)
initialize_simps_projections AddSubsemigroup (carrier -> coe, as_prefix coe)

中文:
实例 :
  签名: 偏序 (子半群 M)
  定义体: .ofSetLike (Subsemigroup M) M

initialize_simps_projections Subsemigroup (carrier -> coe, as_prefix coe)
initialize_simps_projections AddSubsemigroup (carrier -> coe, as_prefix coe)
-/
@[to_additive] instance : PartialOrder (Subsemigroup M) := .ofSetLike (Subsemigroup M) M

initialize_simps_projections Subsemigroup (carrier -> coe, as_prefix coe)
initialize_simps_projections AddSubsemigroup (carrier -> coe, as_prefix coe)

/-- The actual `Subsemigroup` obtained from an element of a `MulMemClass`. -/
@[to_additive (attr := simps) /-- The actual `AddSubsemigroup` obtained from an element of a
`AddMemClass` -/]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: {S M : Type*} [Mul M] [SetLike S M] [MulMemClass S M] (s : S)
  body: ⟨s, MulMemClass.mul_mem⟩

@[to_additive]

中文:
定义 ofClass
  签名: {S M : 类型} [乘法 M] [集合状 S M] [MulMem类 S M] (s : S)
  定义体: ⟨s, MulMemClass.mul_mem⟩

@[to_additive]

Depends on / 依赖: MulMemClass, MulMemClass.mul_mem, mul_mem
-/
def ofClass {S M : Type*} [Mul M] [SetLike S M] [MulMemClass S M] (s : S) : Subsemigroup M :=
  ⟨s, MulMemClass.mul_mem⟩

@[to_additive]
instance (priority := 100) : CanLift (Set M) (Subsemigroup M) (↑)
    (fun s => forall {x y}, x in s -> y in s -> x * y in s) where
  prf s h := ⟨{ carrier := s, mul_mem' := h }, rfl⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulMemClass (Subsemigroup M) M
  body: fun {_ _ _} => Subsemigroup.mul_mem' _

@[to_additive (attr := simp)]

中文:
实例 :
  签名: MulMem类 (子半群 M) M
  定义体: fun {_ _ _} => Subsemigroup.mul_mem' _

@[to_additive (attr := simp)]

Depends on / 依赖: Subsemigroup, Subsemigroup.mul_mem, mul_mem
-/
instance : MulMemClass (Subsemigroup M) M where mul_mem := fun {_ _ _} => Subsemigroup.mul_mem' _

@[to_additive (attr := simp)]
/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : Subsemigroup M} {x : M}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

@[to_additive (attr := simp)]

中文:
定理 mem_carrier
  条件: {s : 子半群 M} {x : M}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : Subsemigroup M} {x : M} : x in s.carrier ↔ x in s :=
  Iff.rfl

@[to_additive (attr := simp)]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {s : Set M} {x : M} (h_mul)
  statement: x in mk s h_mul ↔ x in s
  proof: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 mem_mk
  条件: {s : 集合 M} {x : M} (h_mul)
  结论: x in mk s h_mul ↔ x in s
  证明: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk {s : Set M} {x : M} (h_mul) : x in mk s h_mul ↔ x in s :=
  Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_set_mk` / 定理 `coe_set_mk`

English:
theorem coe_set_mk
  given: (s : Set M) (h_mul)
  statement: (mk s h_mul : Set M) = s
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_set_mk
  条件: (s : 集合 M) (h_mul)
  结论: (mk s h_mul : 集合 M) = s
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_set_mk (s : Set M) (h_mul) : (mk s h_mul : Set M) = s :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: {s t : Set M} (h_mul) (h_mul')
  statement: mk s h_mul <= mk t h_mul' ↔ s subseteq t
  proof: Iff.rfl

中文:
定理 mk_le_mk
  条件: {s t : 集合 M} (h_mul) (h_mul')
  结论: mk s h_mul <= mk t h_mul' ↔ s subseteq t
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl, Subsingleton, isReduced_of_subsingleton
-/
theorem mk_le_mk {s t : Set M} (h_mul) (h_mul') : mk s h_mul <= mk t h_mul' ↔ s subseteq t :=
  Iff.rfl

/-- Two subsemigroups are equal if they have the same elements. -/
@[to_additive (attr := ext) /-- Two `AddSubsemigroup`s are equal if they have the same elements. -/]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : Subsemigroup M} (h : forall x, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

中文:
定理 ext
  条件: {S T : 子半群 M} (h : 对任意 x, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : Subsemigroup M} (h : forall x, x in S ↔ x in T) : S = T :=
  SetLike.ext h

/-- Copy a subsemigroup replacing `carrier` with a set that is equal to it. -/
@[to_additive
/-- Copy an additive subsemigroup replacing `carrier` with a set that is equal to it. -/]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : Subsemigroup M) (s : Set M) (hs : s = S)
  body: s
  mul_mem' := hs.symm ▸ S.mul_mem'

中文:
定义 copy
  签名: (S : 子半群 M) (s : 集合 M) (hs : s = S)
  定义体: s
  mul_mem' := hs.symm ▸ S.mul_mem'
-/
protected def copy (S : Subsemigroup M) (s : Set M) (hs : s = S) :
    Subsemigroup M where
  carrier := s
  mul_mem' := hs.symm ▸ S.mul_mem'

variable {S : Subsemigroup M}

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

/-- A subsemigroup is closed under multiplication. -/
@[to_additive /-- An `AddSubsemigroup` is closed under addition. -/]
/--
theorem `mul_mem` / 定理 `mul_mem`

English:
theorem mul_mem
  given: {x y : M}
  statement: x in S -> y in S -> x * y in S
  proof: Subsemigroup.mul_mem' S

中文:
定理 mul_mem
  条件: {x y : M}
  结论: x in S -> y in S -> x * y in S
  证明: Subsemigroup.mul_mem' S
-/
protected theorem mul_mem {x y : M} : x in S -> y in S -> x * y in S :=
  Subsemigroup.mul_mem' S

/-- The subsemigroup `M` of the magma `M`. -/
@[to_additive /-- The additive subsemigroup `M` of the magma `M`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (Subsemigroup M)
  body: ⟨{ carrier := Set.univ
      mul_mem' := fun _ _ => Set.mem_univ _ }⟩

中文:
实例 :
  签名: 顶元素 (子半群 M)
  定义体: ⟨{ carrier := Set.univ
      mul_mem' := fun _ _ => Set.mem_univ _ }⟩

Depends on / 依赖: Set.mem_univ, Set.univ, carrier, mem_univ, mul_mem
-/
instance : Top (Subsemigroup M) :=
  ⟨{ carrier := Set.univ
      mul_mem' := fun _ _ => Set.mem_univ _ }⟩

/-- The trivial subsemigroup `∅` of a magma `M`. -/
@[to_additive /-- The trivial `AddSubsemigroup` `∅` of an additive magma `M`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (Subsemigroup M)
  body: ⟨{ carrier := ∅
      mul_mem' := False.elim }⟩

@[to_additive]

中文:
实例 :
  签名: 底元素 (子半群 M)
  定义体: ⟨{ carrier := ∅
      mul_mem' := False.elim }⟩

@[to_additive]

Depends on / 依赖: False.elim, carrier, mul_mem
-/
instance : Bot (Subsemigroup M) :=
  ⟨{ carrier := ∅
      mul_mem' := False.elim }⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Subsemigroup M)
  body: ⟨⊥⟩

@[to_additive]

中文:
实例 :
  签名: 可居 (子半群 M)
  定义体: ⟨⊥⟩

@[to_additive]
-/
instance : Inhabited (Subsemigroup M) :=
  ⟨⊥⟩

@[to_additive]
/--
theorem `notMem_bot` / 定理 `notMem_bot`

English:
theorem notMem_bot
  given: {x : M}
  statement: x ∉ (⊥ : Subsemigroup M)
  proof: Set.notMem_empty x

@[to_additive (attr := simp)]

中文:
定理 notMem_bot
  条件: {x : M}
  结论: x ∉ (⊥ : 子半群 M)
  证明: Set.notMem_empty x

@[to_additive (attr := simp)]

Depends on / 依赖: NoZeroDivisors, Set.notMem_empty, isReduced_of_noZeroDivisors, notMem_empty
-/
theorem notMem_bot {x : M} : x ∉ (⊥ : Subsemigroup M) :=
  Set.notMem_empty x

@[to_additive (attr := simp)]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: (x : M)
  statement: x in (⊤ : Subsemigroup M)
  proof: Set.mem_univ x

@[to_additive (attr := simp, norm_cast)]

中文:
定理 mem_top
  条件: (x : M)
  结论: x in (⊤ : 子半群 M)
  证明: Set.mem_univ x

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mem_top (x : M) : x in (⊤ : Subsemigroup M) :=
  Set.mem_univ x

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : Subsemigroup M) : Set M) = Set.univ
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_top
  结论: ((⊤ : 子半群 M) : 集合 M) = 集合.univ
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_top : ((⊤ : Subsemigroup M) : Set M) = Set.univ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : Subsemigroup M) : Set M) = ∅
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_bot
  结论: ((⊥ : 子半群 M) : 集合 M) = ∅
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_bot : ((⊥ : Subsemigroup M) : Set M) = ∅ :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `mk_eq_top` / 引理 `mk_eq_top`

English:
lemma mk_eq_top
  given: (carrier : Set M) (mul_mem')
  statement: mk carrier mul_mem' = ⊤ ↔ carrier = .univ
  proof: by
  simp [← SetLike.coe_set_eq]

@[to_additive (attr := simp)]

中文:
引理 mk_eq_top
  条件: (carrier : 集合 M) (mul_mem')
  结论: mk carrier mul_mem' = ⊤ ↔ carrier = .univ
  证明: by
  simp [← SetLike.coe_set_eq]

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq
-/
lemma mk_eq_top (carrier : Set M) (mul_mem') : mk carrier mul_mem' = ⊤ ↔ carrier = .univ := by
  simp [← SetLike.coe_set_eq]

@[to_additive (attr := simp)]
/--
lemma `mk_eq_bot` / 引理 `mk_eq_bot`

English:
lemma mk_eq_bot
  given: (carrier : Set M) (mul_mem')
  statement: mk carrier mul_mem' = ⊥ ↔ carrier = ∅
  proof: by
  simp [← SetLike.coe_set_eq]

中文:
引理 mk_eq_bot
  条件: (carrier : 集合 M) (mul_mem')
  结论: mk carrier mul_mem' = ⊥ ↔ carrier = ∅
  证明: by
  simp [← SetLike.coe_set_eq]

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq
-/
lemma mk_eq_bot (carrier : Set M) (mul_mem') : mk carrier mul_mem' = ⊥ ↔ carrier = ∅ := by
  simp [← SetLike.coe_set_eq]

/-- The inf of two subsemigroups is their intersection. -/
@[to_additive /-- The inf of two `AddSubsemigroup`s is their intersection. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Subsemigroup M)
  body: ⟨fun S₁ S₂ =>
    { carrier := S₁ inter S₂
      mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 :
  签名: 最小值 (子半群 M)
  定义体: ⟨fun S₁ S₂ =>
    { carrier := S₁ inter S₂
      mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: carrier, mul_mem
-/
instance : Min (Subsemigroup M) :=
  ⟨fun S₁ S₂ =>
    { carrier := S₁ inter S₂
      mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (p p' : Subsemigroup M)
  statement: ((p ⊓ p' : Subsemigroup M) : Set M) = (p : Set M) inter p'
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_inf
  条件: (p p' : 子半群 M)
  结论: ((p ⊓ p' : 子半群 M) : 集合 M) = (p : 集合 M) inter p'
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_inf (p p' : Subsemigroup M) : ((p ⊓ p' : Subsemigroup M) : Set M) = (p : Set M) inter p' :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {p p' : Subsemigroup M} {x : M}
  statement: x in p ⊓ p' ↔ x in p ∧ x in p'
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_inf
  条件: {p p' : 子半群 M} {x : M}
  结论: x in p ⊓ p' ↔ x in p ∧ x in p'
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {p p' : Subsemigroup M} {x : M} : x in p ⊓ p' ↔ x in p ∧ x in p' :=
  Iff.rfl

@[to_additive]
/--
theorem `subsingleton_of_subsingleton` / 定理 `subsingleton_of_subsingleton`

English:
theorem subsingleton_of_subsingleton
  given: [Subsingleton (Subsemigroup M)]
  statement: Subsingleton M
  proof: by
  constructor; intro x y
  have : forall a : M, a in (⊥ : Subsemigroup M) := by simp [Subsingleton.elim (⊥ : Subsemigroup M) ⊤]
  exact absurd (this x) notMem_bot

@[to_additive]

中文:
定理 subsingleton_of_subsingleton
  条件: [子单例 (子半群 M)]
  结论: 子单例 M
  证明: by
  constructor; intro x y
  have : forall a : M, a in (⊥ : Subsemigroup M) := by simp [Subsingleton.elim (⊥ : Subsemigroup M) ⊤]
  exact absurd (this x) notMem_bot

@[to_additive]

Depends on / 依赖: Subsemigroup, Subsingleton, Subsingleton.elim, absurd, notMem_bot
-/
theorem subsingleton_of_subsingleton [Subsingleton (Subsemigroup M)] : Subsingleton M := by
  constructor; intro x y
  have : forall a : M, a in (⊥ : Subsemigroup M) := by simp [Subsingleton.elim (⊥ : Subsemigroup M) ⊤]
  exact absurd (this x) notMem_bot

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hn
  signature: : Nonempty M] : Nontrivial (Subsemigroup M)
  body: ⟨⟨⊥, ⊤, fun h => by
      obtain ⟨x⟩ := id hn
      refine absurd (?_ : x in ⊥) notMem_bot
      simp [h]⟩⟩

中文:
实例 [hn
  签名: : 非空 M] : 非平凡 (子半群 M)
  定义体: ⟨⟨⊥, ⊤, fun h => by
      obtain ⟨x⟩ := id hn
      refine absurd (?_ : x in ⊥) notMem_bot
      simp [h]⟩⟩

Depends on / 依赖: absurd, notMem_bot
-/
instance [hn : Nonempty M] : Nontrivial (Subsemigroup M) :=
  ⟨⟨⊥, ⊤, fun h => by
      obtain ⟨x⟩ := id hn
      refine absurd (?_ : x in ⊥) notMem_bot
      simp [h]⟩⟩

end Subsemigroup

namespace MulHom

variable [Mul N]

open Subsemigroup

/-- The subsemigroup of elements `x : M` such that `f x = g x` -/
@[to_additive /-- The additive subsemigroup of elements `x : M` such that `f x = g x` -/]
/--
Definition of `eqLocus` / `eqLocus` 的定义

English:
definition eqLocus
  signature: (f g : M ->ₙ* N)
  body: { x | f x = g x }
  mul_mem' (hx : _ = _) (hy : _ = _) := by simp [*]

@[to_additive (attr := simp)]

中文:
定义 eqLocus
  签名: (f g : M ->ₙ* N)
  定义体: { x | f x = g x }
  mul_mem' (hx : _ = _) (hy : _ = _) := by simp [*]

@[to_additive (attr := simp)]
-/
def eqLocus (f g : M ->ₙ* N) : Subsemigroup M where
  carrier := { x | f x = g x }
  mul_mem' (hx : _ = _) (hy : _ = _) := by simp [*]

@[to_additive (attr := simp)]
/--
theorem `mem_eqLocus` / 定理 `mem_eqLocus`

English:
theorem mem_eqLocus
  given: {f g : M ->ₙ* N} {x : M}
  statement: x in f.eqLocus g ↔ f x = g x
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_eqLocus
  条件: {f g : M ->ₙ* N} {x : M}
  结论: x in f.eqLocus g ↔ f x = g x
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_eqLocus {f g : M ->ₙ* N} {x : M} : x in f.eqLocus g ↔ f x = g x := Iff.rfl

@[to_additive]
/--
theorem `eq_of_eqOn_top` / 定理 `eq_of_eqOn_top`

English:
theorem eq_of_eqOn_top
  given: {f g : M ->ₙ* N} (h : Set.EqOn f g (⊤ : Subsemigroup M))
  statement: f = g
  proof: ext fun _ => h trivial

中文:
定理 eq_of_eqOn_top
  条件: {f g : M ->ₙ* N} (h : 集合.EqOn f g (⊤ : 子半群 M))
  结论: f = g
  证明: ext fun _ => h trivial
-/
theorem eq_of_eqOn_top {f g : M ->ₙ* N} (h : Set.EqOn f g (⊤ : Subsemigroup M)) : f = g :=
  ext fun _ => h trivial

end MulHom

end NonAssoc

namespace MulMemClass

variable {A : Type*} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)

-- lower priority so other instances are found first
/-- A submagma of a magma inherits a multiplication. -/
@[to_additive /-- An additive submagma of an additive magma inherits an addition. -/]
instance (priority := 900) mul : Mul S' :=
  ⟨fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩⟩

-- lower priority so later simp lemmas are used first; to appease simp_nf
@[to_additive (attr := simp low, norm_cast)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : S')
  statement: (↑(x * y) : M) = ↑x * ↑y
  proof: rfl

中文:
定理 coe_mul
  条件: (x y : S')
  结论: (↑(x * y) : M) = ↑x * ↑y
  证明: rfl

Depends on / 依赖: IsDedekindFiniteMonoid, IsLeftCancelMulZero
-/
theorem coe_mul (x y : S') : (↑(x * y) : M) = ↑x * ↑y :=
  rfl

-- lower priority so later simp lemmas are used first; to appease simp_nf
@[to_additive (attr := simp low)]
/--
theorem `mk_mul_mk` / 定理 `mk_mul_mk`

English:
theorem mk_mul_mk
  given: (x y : M) (hx : x in S') (hy : y in S')
  proof: rfl

@[to_additive]

中文:
定理 mk_mul_mk
  条件: (x y : M) (hx : x in S') (hy : y in S')
  证明: rfl

@[to_additive]

Depends on / 依赖: IsDedekindFiniteMonoid, IsRightCancelMulZero
-/
theorem mk_mul_mk (x y : M) (hx : x in S') (hy : y in S') :
    (⟨x, hx⟩ : S') * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩ :=
  rfl

@[to_additive]
/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (x y : S')
  statement: x * y = ⟨x * y, mul_mem x.2 y.2⟩
  proof: rfl

中文:
定理 mul_def
  条件: (x y : S')
  结论: x * y = ⟨x * y, mul_mem x.2 y.2⟩
  证明: rfl
-/
theorem mul_def (x y : S') : x * y = ⟨x * y, mul_mem x.2 y.2⟩ :=
  rfl

/-- A subsemigroup of a semigroup inherits a semigroup structure. -/
@[to_additive
/-- An `AddSubsemigroup` of an `AddSemigroup` inherits an `AddSemigroup` structure. -/]
/--
Instance `toSemigroup` / 实例 `toSemigroup`

English:
instance toSemigroup
  signature: {M : Type*} [Semigroup M] {A : Type*} [SetLike A M] [MulMemClass A M]
  body: fast_instance%
  Subtype.coe_injective.semigroup Subtype.val fun _ _ => rfl

中文:
实例 toSemigroup
  签名: {M : 类型} [半群 M] {A : 类型} [集合状 A M] [MulMem类 A M]
  定义体: fast_instance%
  Subtype.coe_injective.semigroup Subtype.val fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance toSemigroup {M : Type*} [Semigroup M] {A : Type*} [SetLike A M] [MulMemClass A M]
    (S : A) : Semigroup S := fast_instance%
  Subtype.coe_injective.semigroup Subtype.val fun _ _ => rfl

/-- A subsemigroup of a `CommSemigroup` is a `CommSemigroup`. -/
@[to_additive /-- An `AddSubsemigroup` of an `AddCommSemigroup` is an `AddCommSemigroup`. -/]
/--
Instance `toCommSemigroup` / 实例 `toCommSemigroup`

English:
instance toCommSemigroup
  signature: {M} [CommSemigroup M] {A : Type*} [SetLike A M] [MulMemClass A M]
  body: fast_instance%
  Subtype.coe_injective.commSemigroup Subtype.val fun _ _ => rfl

中文:
实例 toCommSemigroup
  签名: {M} [交换半群 M] {A : 类型} [集合状 A M] [MulMem类 A M]
  定义体: fast_instance%
  Subtype.coe_injective.commSemigroup Subtype.val fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance toCommSemigroup {M} [CommSemigroup M] {A : Type*} [SetLike A M] [MulMemClass A M]
    (S : A) : CommSemigroup S := fast_instance%
  Subtype.coe_injective.commSemigroup Subtype.val fun _ _ => rfl

/-- A submagma of a left cancellative magma inherits left cancellation. -/
@[to_additive
/-- An additive submagma of a left cancellative additive magma inherits left cancellation. -/]
/--
Instance `isLeftCancelMul` / 实例 `isLeftCancelMul`

English:
instance isLeftCancelMul
  signature: [IsLeftCancelMul M] (S : A)
  body: Subtype.coe_injective.isLeftCancelMul Subtype.val fun _ _ => rfl

中文:
实例 isLeftCancelMul
  签名: [左乘消去 M] (S : A)
  定义体: Subtype.coe_injective.isLeftCancelMul Subtype.val fun _ _ => rfl

Depends on / 依赖: Subtype, Subtype.coe_injective.isLeftCancelMul, Subtype.val, coe_injective, isLeftCancelMul
-/
instance isLeftCancelMul [IsLeftCancelMul M] (S : A) : IsLeftCancelMul S :=
  Subtype.coe_injective.isLeftCancelMul Subtype.val fun _ _ => rfl

/-- A submagma of a right cancellative magma inherits right cancellation. -/
@[to_additive
/-- An additive submagma of a right cancellative additive magma inherits right cancellation. -/]
/--
Instance `isRightCancelMul` / 实例 `isRightCancelMul`

English:
instance isRightCancelMul
  signature: [IsRightCancelMul M] (S : A)
  body: Subtype.coe_injective.isRightCancelMul Subtype.val fun _ _ => rfl

中文:
实例 isRightCancelMul
  签名: [右乘消去 M] (S : A)
  定义体: Subtype.coe_injective.isRightCancelMul Subtype.val fun _ _ => rfl

Depends on / 依赖: DivisionMonoid, GroupWithZero, GroupWithZero.toDivisionMonoid, Subtype, Subtype.coe_injective.isRightCancelMul, Subtype.val, coe_injective, isRightCancelMul, toDivisionMonoid
-/
instance isRightCancelMul [IsRightCancelMul M] (S : A) : IsRightCancelMul S :=
  Subtype.coe_injective.isRightCancelMul Subtype.val fun _ _ => rfl

/-- A submagma of a cancellative magma inherits cancellation. -/
@[to_additive /-- An additive submagma of a cancellative additive magma inherits cancellation. -/]
/--
Instance `isCancelMul` / 实例 `isCancelMul`

English:
instance isCancelMul
  signature: [IsCancelMul M] (S : A)

中文:
实例 isCancelMul
  签名: [是消去乘法 M] (S : A)

Depends on / 依赖: IsCancelMulZero
-/
instance isCancelMul [IsCancelMul M] (S : A) : IsCancelMul S where

/-- The natural semigroup hom from a subsemigroup of semigroup `M` to `M`. -/
@[to_additive /-- The natural semigroup hom from an `AddSubsemigroup` of
`AddSubsemigroup` `M` to `M`. -/]
/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : S' ->ₙ* M where
  body: Subtype.val; map_mul' := fun _ _ => rfl

中文:
定义 subtype
  签名: : S' ->ₙ* M where
  定义体: Subtype.val; map_mul' := fun _ _ => rfl

Depends on / 依赖: Subtype, Subtype.val, map_mul
-/
def subtype : S' ->ₙ* M where
  toFun := Subtype.val; map_mul' := fun _ _ => rfl

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
    MulMemClass.subtype S' x = x := rfl

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
    Function.Injective (MulMemClass.subtype S') :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: (MulMemClass.subtype S' : S' -> M) = Subtype.val
  proof: rfl

中文:
定理 coe_subtype
  结论: (MulMem类.subtype S' : S' -> M) = 子类型.val
  证明: rfl
-/
theorem coe_subtype : (MulMemClass.subtype S' : S' -> M) = Subtype.val :=
  rfl

end MulMemClass

@[to_additive]
/--
lemma `isMulCommutative_iff_of_setLike` / 引理 `isMulCommutative_iff_of_setLike`

English:
lemma isMulCommutative_iff_of_setLike
  statement: {S M : Type*} [SetLike S M] [Mul M] [MulMemClass S M]
  proof: by
  simp [isMulCommutative_iff]

@[to_additive]
alias ⟨_, IsMulCommutative.of_setLike_mul_comm⟩ := isMulCommutative_iff_of_setLike

中文:
引理 isMulCommutative_iff_of_setLike
  结论: {S M : 类型} [集合状 S M] [乘法 M] [MulMem类 S M]
  证明: by
  simp [isMulCommutative_iff]

@[to_additive]
alias ⟨_, IsMulCommutative.of_setLike_mul_comm⟩ := isMulCommutative_iff_of_setLike

Depends on / 依赖: isMulCommutative_iff
-/
lemma isMulCommutative_iff_of_setLike {S M : Type*} [SetLike S M] [Mul M] [MulMemClass S M]
    {s : S} : IsMulCommutative s ↔ forall a in s, forall b in s, a * b = b * a := by
  simp [isMulCommutative_iff]

@[to_additive]
alias ⟨_, IsMulCommutative.of_setLike_mul_comm⟩ := isMulCommutative_iff_of_setLike

/-- Commutativity of multiplication in commutative subobjects. -/
@[to_additive /-- Commutativity of addition in commutative subobjects. -/ ]
/--
lemma `setLike_mul_comm` / 引理 `setLike_mul_comm`

English:
lemma setLike_mul_comm
  statement: {S M : Type*} [SetLike S M] [Mul M] [MulMemClass S M]
  proof: isMulCommutative_iff_of_setLike.mp ‹_› a ha b hb

中文:
引理 setLike_mul_comm
  结论: {S M : 类型} [集合状 S M] [乘法 M] [MulMem类 S M]
  证明: isMulCommutative_iff_of_setLike.mp ‹_› a ha b hb

Depends on / 依赖: isMulCommutative_iff_of_setLike, isMulCommutative_iff_of_setLike.mp
-/
lemma setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [MulMemClass S M]
    {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in s) :
    a * b = b * a :=
  isMulCommutative_iff_of_setLike.mp ‹_› a ha b hb
