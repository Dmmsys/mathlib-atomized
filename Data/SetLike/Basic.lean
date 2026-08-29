/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Tactic.Monotonicity.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Data.Set.Basic

/-!
# Typeclass for types with a set-like extensionality property

The `Membership` typeclass is used to let terms of a type have elements.
Many instances of `Membership` have a set-like extensionality property:
things are equal iff they have the same elements. The `SetLike`
typeclass provides a unified interface to define a `Membership` that is
extensional in this way.

The main use of `SetLike` is for algebraic subobjects (such as
`Submonoid` and `Submodule`), whose non-proof data consists only of a
carrier set. In such a situation, the projection to the carrier set
is injective.

In general, a type `A` is `SetLike` with elements of type `B` if it
has an injective map to `Set B`. This module provides standard
boilerplate for every `SetLike`: a `coe_sort`, a `coe` to set,
and various extensionality and simp lemmas. The order induced by set inclusion is
called `PartialOrder.ofSetlike`: this is not an instance for flexibility in choosing orders.
The class `IsConcreteLE` abstractly states the order is equal to that induced by set inclusion;
an instance is automatically available when defining a `PartialOrder` as
`.ofSetLike (MySubobject X) X`.

A typical subobject should be declared as:
```
structure MySubobject (X : Type*) [ObjectTypeclass X] where
  (carrier : Set X)
  (op_mem' : ∀ {x : X}, x ∈ carrier → sorry ∈ carrier)

namespace MySubobject

variable {X : Type*} [ObjectTypeclass X] {x : X}

instance : SetLike (MySubobject X) X :=
  ⟨MySubobject.carrier, fun p q h => by cases p; cases q; congr!⟩

instance : PartialOrder (MySubobject X) := .ofSetLike (MySubobject X) X

@[simp] lemma mem_carrier {p : MySubobject X} : x ∈ p.carrier ↔ x ∈ (p : Set X) := Iff.rfl

@[ext] theorem ext {p q : MySubobject X} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (p : MySubobject X) (s : Set X) (hs : s = ↑p)
  body: { carrier := s
    op_mem' := hs.symm ▸ p.op_mem' }

中文:
定义 copy
  签名: (p : MySubobject X) (s : 集合 X) (hs : s = ↑p)
  定义体: { carrier := s
    op_mem' := hs.symm ▸ p.op_mem' }
-/
protected def copy (p : MySubobject X) (s : Set X) (hs : s = ↑p) : MySubobject X :=
  { carrier := s
    op_mem' := hs.symm ▸ p.op_mem' }

/--
lemma `coe_copy` / 引理 `coe_copy`

English:
lemma coe_copy
  given: (p : MySubobject X) (s : Set X) (hs : s = ↑p)
  proof: rfl

中文:
引理 coe_copy
  条件: (p : MySubobject X) (s : 集合 X) (hs : s = ↑p)
  证明: rfl
-/
@[simp] lemma coe_copy (p : MySubobject X) (s : Set X) (hs : s = ↑p) :
  (p.copy s hs : Set X) = s := rfl

/--
lemma `copy_eq` / 引理 `copy_eq`

English:
lemma copy_eq
  given: (p : MySubobject X) (s : Set X) (hs : s = ↑p)
  statement: p.copy s hs = p
  proof: SetLike.coe_injective hs

中文:
引理 copy_eq
  条件: (p : MySubobject X) (s : 集合 X) (hs : s = ↑p)
  结论: p.copy s hs = p
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
lemma copy_eq (p : MySubobject X) (s : Set X) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs

end MySubobject
```

An alternative to `SetLike` could have been an extensional `Membership` typeclass:
```
/--
Definition of `ExtMembership` / `ExtMembership` 的定义

English:
class ExtMembership
  parameters: (α : out_param <| Type u) (β : Type v)
  extends: Membership α β
  axioms and operations (1):
    - (ext_iff : forall {s t : β}, s = t ↔ forall (x : α), x in s ↔ x in t)

中文:
类 ExtMembership
  参数: (α : out_param <| 类型u) (β : 类型v)
  继承: Membership α β
  公理与运算 (1 个):
    - (ext_iff : 对任意 {s t : β}, s = t ↔ 对任意 (x : α), x in s ↔ x in t)
-/
class ExtMembership (α : out_param <| Type u) (β : Type v) extends Membership α β where
  (ext_iff : forall {s t : β}, s = t ↔ forall (x : α), x in s ↔ x in t)
```
While this is equivalent, `SetLike` conveniently uses a carrier set projection directly.

## Tags

subobjects
-/

@[expose] public section

assert_not_exists RelIso

/-- A class to indicate that there is a canonical injection between `A` and `Set B`.

This has the effect of giving terms of `A` elements of type `B` (through a `Membership`
instance) and a compatible coercion to `Type*` as a subtype.

Note: if `SetLike.coe` is a projection, implementers should create a simp lemma such as
```
@[simp] lemma mem_carrier {p : MySubobject X} : x ∈ p.carrier ↔ x ∈ (p : Set X) := Iff.rfl
```
to normalize terms.

If you declare an unbundled subclass of `SetLike`, for example:
```
class MulMemClass (S : Type*) (M : Type*) [Mul M] [SetLike S M] where
  ...
```
Then you should *not* repeat the `outParam` declaration so `SetLike` will supply the value instead.
This ensures your subclass will not have issues with synthesis of the `[Mul M]` parameter starting
before the value of `M` is known.
-/
@[notation_class* carrier Simps.findCoercionArgs]
/--
Definition of `SetLike` / `SetLike` 的定义

English:
class SetLike
  parameters: (A : Type*) (B : outParam Type*)
  axioms and operations (2):
    - coe : A -> Set B
    - coe_injective : Function.Injective coe

中文:
类 集合状
  参数: (A : 类型) (B : outParam 类型)
  公理与运算 (2 个):
    - coe : A -> 集合 B
    - coe_injective : 函数.单射 coe
-/
class SetLike (A : Type*) (B : outParam Type*) where
  /-- The coercion from a term of a `SetLike` to its corresponding `Set`. -/
  protected coe : A -> Set B
  /-- The coercion from a term of a `SetLike` to its corresponding `Set` is injective. -/
  coe_injective : Function.Injective coe

attribute [coe] SetLike.coe

namespace SetLike

variable {A : Type*} {B : Type*} [i : SetLike A B]

@[deprecated (since := "2026-06-04")] alias coe_injective' := coe_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC A (Set B)
  body: SetLike.coe

中文:
实例 :
  签名: CoeTC A (集合 B)
  定义体: SetLike.coe

Depends on / 依赖: SetLike, SetLike.coe
-/
instance : CoeTC A (Set B) where coe := SetLike.coe

instance (priority := 100) instMembership : Membership B A :=
  ⟨fun p x => x in (p : Set B)⟩

instance (priority := 100) : CoeSort A (Type _) :=
  ⟨fun p => { x : B // x in p }⟩

section Delab
open Lean PrettyPrinter.Delaborator SubExpr

/-- For terms that match the `CoeSort` instance's body, pretty print as `↥S`
rather than as `{ x // x ∈ S }`. The discriminating feature is that membership
uses the `SetLike.instMembership` instance. -/
@[app_delab Subtype]
meta def delabSubtypeSetLike : Delab := whenPPOption getPPNotation do
  let #[_, .lam n _ body _] := (← getExpr).getAppArgs | failure
guard body.isAppOf ``Membership.mem
  let #[_, _, inst, _, .bvar 0] := body.getAppArgs | failure
guard inst.isAppOfArity ``instMembership 3
let S ← withAppArg withBindingBody n withNaryArg 3 delab
  `(↥$S)

end Delab

variable (p q : A)

@[simp, norm_cast]
/--
theorem `coe_sort_coe` / 定理 `coe_sort_coe`

English:
theorem coe_sort_coe
  statement: ((p : Set B) : Type _) = p
  proof: rfl

中文:
定理 coe_sort_coe
  结论: ((p : 集合 B) : 类型 _) = p
  证明: rfl
-/
theorem coe_sort_coe : ((p : Set B) : Type _) = p :=
  rfl

variable {p q}

/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {q : p -> Prop}
  statement: (exists x, q x) ↔ exists (x : B) (h : x in p), q ⟨x, ‹_›⟩
  proof: SetCoe.exists

中文:
定理 «存在»
  条件: {q : p -> 命题}
  结论: (存在 x, q x) ↔ 存在 (x : B) (h : x in p), q ⟨x, ‹_›⟩
  证明: SetCoe.exists
-/
protected theorem «exists» {q : p -> Prop} : (exists x, q x) ↔ exists (x : B) (h : x in p), q ⟨x, ‹_›⟩ :=
  SetCoe.exists

/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {q : p -> Prop}
  statement: (forall x, q x) ↔ forall (x : B) (h : x in p), q ⟨x, ‹_›⟩
  proof: SetCoe.forall

@[simp, norm_cast]

中文:
定理 «对任意»
  条件: {q : p -> 命题}
  结论: (对任意 x, q x) ↔ 对任意 (x : B) (h : x in p), q ⟨x, ‹_›⟩
  证明: SetCoe.forall

@[simp, norm_cast]
-/
protected theorem «forall» {q : p -> Prop} : (forall x, q x) ↔ forall (x : B) (h : x in p), q ⟨x, ‹_›⟩ :=
  SetCoe.forall

@[simp, norm_cast]
/--
theorem `coe_set_eq` / 定理 `coe_set_eq`

English:
theorem coe_set_eq
  statement: (p : Set B) = q ↔ p = q
  proof: coe_injective.eq_iff

中文:
定理 coe_set_eq
  结论: (p : 集合 B) = q ↔ p = q
  证明: coe_injective.eq_iff

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff
-/
theorem coe_set_eq : (p : Set B) = q ↔ p = q :=
  coe_injective.eq_iff

/--
lemma `coe_ne_coe` / 引理 `coe_ne_coe`

English:
lemma coe_ne_coe
  statement: (p : Set B) != q ↔ p != q
  proof: coe_injective.ne_iff

中文:
引理 coe_ne_coe
  结论: (p : 集合 B) != q ↔ p != q
  证明: coe_injective.ne_iff
-/
@[norm_cast] lemma coe_ne_coe : (p : Set B) != q ↔ p != q := coe_injective.ne_iff

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: (h : (p : Set B) = q)
  statement: p = q
  proof: coe_injective h

中文:
定理 ext'
  条件: (h : (p : 集合 B) = q)
  结论: p = q
  证明: coe_injective h

Depends on / 依赖: coe_injective
-/
theorem ext' (h : (p : Set B) = q) : p = q :=
  coe_injective h

/--
theorem `ext'_iff` / 定理 `ext'_iff`

English:
theorem ext'_iff
  statement: p = q ↔ (p : Set B) = q
  proof: coe_set_eq.symm

中文:
定理 ext'_iff
  结论: p = q ↔ (p : 集合 B) = q
  证明: coe_set_eq.symm
-/
theorem ext'_iff : p = q ↔ (p : Set B) = q :=
  coe_set_eq.symm

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall x, x in p ↔ x in q)
  statement: p = q
  proof: coe_injective Set.ext h

中文:
定理 ext
  条件: (h : 对任意 x, x in p ↔ x in q)
  结论: p = q
  证明: coe_injective Set.ext h

Depends on / 依赖: Set.ext, coe_injective
-/
theorem ext (h : forall x, x in p ↔ x in q) : p = q :=
coe_injective Set.ext h

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  statement: p = q ↔ forall x, x in p ↔ x in q
  proof: coe_injective.eq_iff.symm.trans Set.ext_iff

@[simp, push]

中文:
定理 ext_iff
  结论: p = q ↔ 对任意 x, x in p ↔ x in q
  证明: coe_injective.eq_iff.symm.trans Set.ext_iff

@[simp, push]

Depends on / 依赖: Set.ext_iff, coe_injective, coe_injective.eq_iff.symm.trans, eq_iff, ext_iff
-/
theorem ext_iff : p = q ↔ forall x, x in p ↔ x in q :=
  coe_injective.eq_iff.symm.trans Set.ext_iff

@[simp, push]
/--
theorem `mem_coe` / 定理 `mem_coe`

English:
theorem mem_coe
  given: {x : B}
  statement: x in (p : Set B) ↔ x in p
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 mem_coe
  条件: {x : B}
  结论: x in (p : 集合 B) ↔ x in p
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe {x : B} : x in (p : Set B) ↔ x in p :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_eq_coe` / 定理 `coe_eq_coe`

English:
theorem coe_eq_coe
  given: {x y : p}
  statement: (x : B) = y ↔ x = y
  proof: Subtype.ext_iff.symm

@[simp]

中文:
定理 coe_eq_coe
  条件: {x y : p}
  结论: (x : B) = y ↔ x = y
  证明: Subtype.ext_iff.symm

@[simp]

Depends on / 依赖: Subtype, Subtype.ext_iff.symm, ext_iff
-/
theorem coe_eq_coe {x y : p} : (x : B) = y ↔ x = y :=
  Subtype.ext_iff.symm

@[simp]
/--
theorem `coe_mem` / 定理 `coe_mem`

English:
theorem coe_mem
  given: (x : p)
  statement: (x : B) in p
  proof: x.2

@[aesop 5% (rule_sets := [SetLike!])]

中文:
定理 coe_mem
  条件: (x : p)
  结论: (x : B) in p
  证明: x.2

@[aesop 5% (rule_sets := [SetLike!])]
-/
theorem coe_mem (x : p) : (x : B) in p :=
  x.2

@[aesop 5% (rule_sets := [SetLike!])]
/--
lemma `mem_of_subset` / 引理 `mem_of_subset`

English:
lemma mem_of_subset
  given: {s : Set B} (hp : s subseteq p) {x : B} (hx : x in s)
  statement: x in p
  proof: hp hx

@[simp]

中文:
引理 mem_of_subset
  条件: {s : 集合 B} (hp : s subseteq p) {x : B} (hx : x in s)
  结论: x in p
  证明: hp hx

@[simp]
-/
lemma mem_of_subset {s : Set B} (hp : s subseteq p) {x : B} (hx : x in s) : x in p := hp hx

@[simp]
/--
theorem `eta` / 定理 `eta`

English:
theorem eta
  given: (x : p) (hx : (x : B) in p)
  statement: (⟨x, hx⟩ : p) = x
  proof: rfl

中文:
定理 eta
  条件: (x : p) (hx : (x : B) in p)
  结论: (⟨x, hx⟩ : p) = x
  证明: rfl
-/
protected theorem eta (x : p) (hx : (x : B) in p) : (⟨x, hx⟩ : p) = x := rfl

/--
lemma `setOfPred_mem_eq` / 引理 `setOfPred_mem_eq`

English:
lemma setOfPred_mem_eq
  given: (a : A)
  statement: {b | b in a} = a
  proof: rfl

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq := setOfPred_mem_eq

@[nontriviality]

中文:
引理 setOfPred_mem_eq
  条件: (a : A)
  结论: {b | b in a} = a
  证明: rfl

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq := setOfPred_mem_eq

@[nontriviality]
-/
@[simp] lemma setOfPred_mem_eq (a : A) : {b | b in a} = a := rfl

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq := setOfPred_mem_eq

@[nontriviality]
/--
lemma `mem_of_subsingleton` / 引理 `mem_of_subsingleton`

English:
lemma mem_of_subsingleton
  given: [Subsingleton B] (S : A) [h : Nonempty S] {b : B}
  statement: b in S
  proof: by
  obtain ⟨s, hs⟩ := nonempty_subtype.mp h
  simpa [Subsingleton.elim b s]

中文:
引理 mem_of_subsingleton
  条件: [子单例 B] (S : A) [h : 非空 S] {b : B}
  结论: b in S
  证明: by
  obtain ⟨s, hs⟩ := nonempty_subtype.mp h
  simpa [Subsingleton.elim b s]

Depends on / 依赖: Subsingleton, Subsingleton.elim, nonempty_subtype, nonempty_subtype.mp
-/
lemma mem_of_subsingleton [Subsingleton B] (S : A) [h : Nonempty S] {b : B} : b in S := by
  obtain ⟨s, hs⟩ := nonempty_subtype.mp h
  simpa [Subsingleton.elim b s]

/--
lemma `exists_not_mem_of_ne_top` / 引理 `exists_not_mem_of_ne_top`

English:
lemma exists_not_mem_of_ne_top
  statement: [LE A] [OrderTop A] (s : A) (hs : s != ⊤)
  proof: by
  simpa [-SetLike.coe_set_eq, SetLike.ext'_iff, h_top, Set.ne_univ_iff_exists_notMem] using hs

中文:
引理 存在_not_mem_of_ne_top
  结论: [LE A] [有顶序 A] (s : A) (hs : s != ⊤)
  证明: by
  simpa [-SetLike.coe_set_eq, SetLike.ext'_iff, h_top, Set.ne_univ_iff_exists_notMem] using hs

Depends on / 依赖: Set.ne_univ_iff_exists_notMem, SetLike, SetLike.coe_set_eq, SetLike.ext, _iff, coe_set_eq, h_top, ne_univ_iff_exists_notMem
-/
lemma exists_not_mem_of_ne_top [LE A] [OrderTop A] (s : A) (hs : s != ⊤)
    (h_top : ((⊤ : A) : Set B) = Set.univ := by simp) :
    exists b : B, b ∉ s := by
  simpa [-SetLike.coe_set_eq, SetLike.ext'_iff, h_top, Set.ne_univ_iff_exists_notMem] using hs

end SetLike

/--
Definition of `IsConcreteLE` / `IsConcreteLE` 的定义

English:
class IsConcreteLE
  parameters: (A : Type*) (B : outParam Type*) [SetLike A B] [LE A]
  axioms and operations (1):
    - coe_subset_coe'({S T : A}) : SetLike.coe S subseteq SetLike.coe T ↔ S <= T

中文:
类 是余ncreteLE
  参数: (A : 类型) (B : outParam 类型) [集合状 A B] [LE A]
  公理与运算 (1 个):
    - coe_subset_coe'({S T : A}) : 集合状.coe S subseteq 集合状.coe T ↔ S <= T
-/
class IsConcreteLE (A : Type*) (B : outParam Type*) [SetLike A B] [LE A] where
  /-- The coercion from a `SetLike` type preserves the ordering. -/
  protected coe_subset_coe' {S T : A} : SetLike.coe S subseteq SetLike.coe T ↔ S <= T

section default

variable (A B : Type*) [SetLike A B]

/--
Definition of `LE.ofSetLike` / `LE.ofSetLike` 的定义

English:
definition LE.ofSetLike
  signature: : LE A where
  body: fun H K => forall ⦃x⦄, x in H -> x in K

中文:
定义 LE.ofSetLike
  签名: : LE A where
  定义体: fun H K => forall ⦃x⦄, x in H -> x in K
-/
@[reducible] def LE.ofSetLike : LE A where
  le := fun H K => forall ⦃x⦄, x in H -> x in K

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: letI
  body: LE.ofSetLike A B; IsConcreteLE A B :=
  letI := LE.ofSetLike A B; { coe_subset_coe' := Iff.rfl }

中文:
实例 :
  签名: letI
  定义体: LE.ofSetLike A B; IsConcreteLE A B :=
  letI := LE.ofSetLike A B; { coe_subset_coe' := Iff.rfl }

Depends on / 依赖: IsConcreteLE, LE.ofSetLike, ofSetLike
-/
instance : letI := LE.ofSetLike A B; IsConcreteLE A B :=
  letI := LE.ofSetLike A B; { coe_subset_coe' := Iff.rfl }

/--
Definition of `PartialOrder.ofSetLike` / `PartialOrder.ofSetLike` 的定义

English:
definition PartialOrder.ofSetLike
  signature: : PartialOrder A where
  body: LE.ofSetLike A B
  lt s t := letI := LE.ofSetLike A B; s <= t ∧ ¬t <= s
  __ := PartialOrder.lift (SetLike.coe : A -> Set B) SetLike.coe_injective

中文:
定义 偏序.ofSetLike
  签名: : 偏序 A where
  定义体: LE.ofSetLike A B
  lt s t := letI := LE.ofSetLike A B; s <= t ∧ ¬t <= s
  __ := PartialOrder.lift (SetLike.coe : A -> Set B) SetLike.coe_injective
-/
@[reducible] def PartialOrder.ofSetLike : PartialOrder A where
  __ := LE.ofSetLike A B
  lt s t := letI := LE.ofSetLike A B; s <= t ∧ ¬t <= s
  __ := PartialOrder.lift (SetLike.coe : A -> Set B) SetLike.coe_injective

end default

namespace SetLike

variable {A B : Type*} [SetLike A B]

section LE

variable [LE A] [IsConcreteLE A B] {p q : A}

/--
lemma `coe_subset_coe` / 引理 `coe_subset_coe`

English:
lemma coe_subset_coe
  given: {S T : A}
  statement: (S : Set B) subseteq T ↔ S <= T
  proof: IsConcreteLE.coe_subset_coe'

中文:
引理 coe_subset_coe
  条件: {S T : A}
  结论: (S : 集合 B) subseteq T ↔ S <= T
  证明: IsConcreteLE.coe_subset_coe'
-/
@[simp, norm_cast, gcongr] lemma coe_subset_coe {S T : A} : (S : Set B) subseteq T ↔ S <= T :=
  IsConcreteLE.coe_subset_coe'

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {S T : A}
  statement: S <= T ↔ forall ⦃x : B⦄, x in S -> x in T
  proof: by
  simp [← coe_subset_coe, Set.subset_def]

@[gcongr low] -- lower priority than `Set.mem_of_subset_of_mem`
alias ⟨_root_.mem_of_le_of_mem, _⟩ := le_def

@[deprecated (since := "2026-01-07")] alias GCongr.mem_of_le_of_mem := _root_.mem_of_le_of_mem

中文:
定理 le_def
  条件: {S T : A}
  结论: S <= T ↔ 对任意 ⦃x : B⦄, x in S -> x in T
  证明: by
  simp [← coe_subset_coe, Set.subset_def]

@[gcongr low] -- lower priority than `Set.mem_of_subset_of_mem`
alias ⟨_root_.mem_of_le_of_mem, _⟩ := le_def

@[deprecated (since := "2026-01-07")] alias GCongr.mem_of_le_of_mem := _root_.mem_of_le_of_mem

Depends on / 依赖: Set.subset_def, coe_subset_coe, subset_def
-/
theorem le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x in T := by
  simp [← coe_subset_coe, Set.subset_def]

@[gcongr low] -- lower priority than `Set.mem_of_subset_of_mem`
alias ⟨_root_.mem_of_le_of_mem, _⟩ := le_def

@[deprecated (since := "2026-01-07")] alias GCongr.mem_of_le_of_mem := _root_.mem_of_le_of_mem

/--
theorem `not_le_iff_exists` / 定理 `not_le_iff_exists`

English:
theorem not_le_iff_exists
  statement: ¬p <= q ↔ exists x in p, x ∉ q
  proof: by
  simpa [← coe_subset_coe] using! Set.not_subset

中文:
定理 not_le_iff_存在
  结论: ¬p <= q ↔ 存在 x in p, x ∉ q
  证明: by
  simpa [← coe_subset_coe] using! Set.not_subset

Depends on / 依赖: Set.not_subset, coe_subset_coe, not_subset
-/
theorem not_le_iff_exists : ¬p <= q ↔ exists x in p, x ∉ q := by
  simpa [← coe_subset_coe] using! Set.not_subset

end LE

section Preorder

variable [Preorder A] [IsConcreteLE A B] {p q : A}

@[gcongr, mono]
/--
theorem `coe_mono` / 定理 `coe_mono`

English:
theorem coe_mono
  statement: Monotone (SetLike.coe : A -> Set B)
  proof: fun _ _ => coe_subset_coe.mpr

中文:
定理 coe_mono
  结论: 递增 (集合状.coe : A -> 集合 B)
  证明: fun _ _ => coe_subset_coe.mpr

Depends on / 依赖: coe_subset_coe, coe_subset_coe.mpr
-/
theorem coe_mono : Monotone (SetLike.coe : A -> Set B) := fun _ _ => coe_subset_coe.mpr

end Preorder

section PartialOrder

variable [PartialOrder A] [IsConcreteLE A B] {p q : A}

/--
lemma `coe_ssubset_coe` / 引理 `coe_ssubset_coe`

English:
lemma coe_ssubset_coe
  given: {S T : A}
  statement: (S : Set B) ⊂ T ↔ S < T
  proof: by
  rw [ssubset_iff_subset_ne]; rw [lt_iff_le_and_ne]; rw [coe_subset_coe]; rw [SetLike.coe_ne_coe]

@[gcongr, mono]

中文:
引理 coe_ssubset_coe
  条件: {S T : A}
  结论: (S : 集合 B) ⊂ T ↔ S < T
  证明: by
  rw [ssubset_iff_subset_ne]; rw [lt_iff_le_and_ne]; rw [coe_subset_coe]; rw [SetLike.coe_ne_coe]

@[gcongr, mono]
-/
@[simp, norm_cast, gcongr] lemma coe_ssubset_coe {S T : A} : (S : Set B) ⊂ T ↔ S < T := by
  rw [ssubset_iff_subset_ne]; rw [lt_iff_le_and_ne]; rw [coe_subset_coe]; rw [SetLike.coe_ne_coe]

@[gcongr, mono]
/--
theorem `coe_strictMono` / 定理 `coe_strictMono`

English:
theorem coe_strictMono
  statement: StrictMono (SetLike.coe : A -> Set B)
  proof: fun _ _ => coe_ssubset_coe.mpr

中文:
定理 coe_strictMono
  结论: 严格递增 (集合状.coe : A -> 集合 B)
  证明: fun _ _ => coe_ssubset_coe.mpr

Depends on / 依赖: coe_ssubset_coe, coe_ssubset_coe.mpr
-/
theorem coe_strictMono : StrictMono (SetLike.coe : A -> Set B) := fun _ _ => coe_ssubset_coe.mpr

/--
theorem `exists_of_lt` / 定理 `exists_of_lt`

English:
theorem exists_of_lt
  statement: p < q -> exists x in q, x ∉ p
  proof: by
  simpa [← coe_ssubset_coe] using! Set.exists_of_ssubset

中文:
定理 存在_of_lt
  结论: p < q -> 存在 x in q, x ∉ p
  证明: by
  simpa [← coe_ssubset_coe] using! Set.exists_of_ssubset

Depends on / 依赖: Set.exists_of_ssubset, coe_ssubset_coe, exists_of_ssubset
-/
theorem exists_of_lt : p < q -> exists x in q, x ∉ p := by
  simpa [← coe_ssubset_coe] using! Set.exists_of_ssubset

/--
theorem `lt_iff_le_and_exists` / 定理 `lt_iff_le_and_exists`

English:
theorem lt_iff_le_and_exists
  statement: p < q ↔ p <= q ∧ exists x in q, x ∉ p
  proof: by
  rw [lt_iff_le_not_ge]; rw [not_le_iff_exists]

中文:
定理 lt_iff_le_and_存在
  结论: p < q ↔ p <= q ∧ 存在 x in q, x ∉ p
  证明: by
  rw [lt_iff_le_not_ge]; rw [not_le_iff_exists]

Depends on / 依赖: lt_iff_le_not_ge, not_le_iff_exists
-/
theorem lt_iff_le_and_exists : p < q ↔ p <= q ∧ exists x in q, x ∉ p := by
  rw [lt_iff_le_not_ge]; rw [not_le_iff_exists]

/--
Definition of `instSubtypeSet` / `instSubtypeSet` 的定义

English:
abbreviation instSubtypeSet
  signature: {X} {p : Set X -> Prop}
  body: (↑)
  coe_injective := Subtype.val_injective

中文:
缩写 instSubtypeSet
  签名: {X} {p : 集合 X -> 命题}
  定义体: (↑)
  coe_injective := Subtype.val_injective
-/
abbrev instSubtypeSet {X} {p : Set X -> Prop} : SetLike {s // p s} X where
  coe := (↑)
  coe_injective := Subtype.val_injective

/--
Definition of `instSubtype` / `instSubtype` 的定义

English:
abbreviation instSubtype
  signature: {X S} [SetLike S X] {p : S -> Prop}
  body: (↑)
  coe_injective := SetLike.coe_injective.comp Subtype.val_injective

中文:
缩写 instSubtype
  签名: {X S} [集合状 S X] {p : S -> 命题}
  定义体: (↑)
  coe_injective := SetLike.coe_injective.comp Subtype.val_injective
-/
abbrev instSubtype {X S} [SetLike S X] {p : S -> Prop} : SetLike {s // p s} X where
  coe := (↑)
  coe_injective := SetLike.coe_injective.comp Subtype.val_injective

section

attribute [local instance] instSubtypeSet instSubtype

/--
lemma `mem_mk_set` / 引理 `mem_mk_set`

English:
lemma mem_mk_set
  given: {X} {p : Set X -> Prop} {U : Set X} {h : p U} {x : X}
  proof: Iff.rfl

中文:
引理 mem_mk_set
  条件: {X} {p : 集合 X -> 命题} {U : 集合 X} {h : p U} {x : X}
  证明: Iff.rfl
-/
@[simp] lemma mem_mk_set {X} {p : Set X -> Prop} {U : Set X} {h : p U} {x : X} :
    x in Subtype.mk U h ↔ x in U := Iff.rfl

/--
lemma `mem_mk` / 引理 `mem_mk`

English:
lemma mem_mk
  given: {X S} [SetLike S X] {p : S -> Prop} {U : S} {h : p U} {x : X}
  proof: Iff.rfl

中文:
引理 mem_mk
  条件: {X S} [集合状 S X] {p : S -> 命题} {U : S} {h : p U} {x : X}
  证明: Iff.rfl
-/
@[simp] lemma mem_mk {X S} [SetLike S X] {p : S -> Prop} {U : S} {h : p U} {x : X} :
    x in Subtype.mk U h ↔ x in U := Iff.rfl

end

end PartialOrder

end SetLike
