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

/-- `OneMemClass S M` says `S` is a type of subsets `s ≤ M`, such that `1 ∈ s` for all `s`. -/
/-
**OneMemClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_3) → (M : outParam (Type u_4)) → [One M] → [SetLike S M] → Pro
p
参数：Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OneMemClass S M` says `S` is a type of subsets `s ≤ M`, such that `1 ∈ s` for a
ll `s`.
-/
class OneMemClass (S : Type*) (M : outParam Type*) [One M] [SetLike S M] : Prop where
  /-- By definition, if we have `OneMemClass S M`, we have `1 ∈ s` for all `s : S`. -/
  one_mem : ∀ s : S, (1 : M) ∈ s

export OneMemClass (one_mem)

/-- `ZeroMemClass S M` says `S` is a type of subsets `s ≤ M`, such that `0 ∈ s` for all `s`. -/
/-
**ZeroMemClass** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：ZeroMemClass (S : Type*) (M : outParam Type*) [Zero M] [SetLike S M] : Pro
p where /-- By definition, if we have `ZeroMemClass S M`, we have `0 ∈ s` for al
l `s : S`. -/ zero_mem : forall s : S, (0 : M) in s  export ZeroMemClass (zero_m
em)  attribute [to_additive] OneMemClass  attribute [simp, aesop safe (rule_sets
参数：S : Type*；M : outParam Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ZeroMemClass S M` says `S` is a type of subsets `s ≤ M`, such that `0 ∈ s` for 
all `s`.
-/
class ZeroMemClass (S : Type*) (M : outParam Type*) [Zero M] [SetLike S M] : Prop where
  /-- By definition, if we have `ZeroMemClass S M`, we have `0 ∈ s` for all `s : S`. -/
  zero_mem : ∀ s : S, (0 : M) ∈ s

export ZeroMemClass (zero_mem)

attribute [to_additive] OneMemClass

attribute [simp, aesop safe (rule_sets := [SetLike])] one_mem zero_mem

/-- The underlying set of a term of a `OneMemClass` is nonempty. -/
@[to_additive (attr := simp)
/-- The underlying set of a term of a `ZeroMemClass` is nonempty. -/]
/-
**OneMemClass.coe_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneMemClass.coe_nonempty {S M : Type*} [One M] [SetLike S M] [OneMemClass 
S M] (s : S) : (s : Set M).Nonempty
参数：s : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
-/
theorem OneMemClass.coe_nonempty {S M : Type*} [One M] [SetLike S M] [OneMemClass S M] (s : S) :
    (s : Set M).Nonempty :=
  ⟨1, one_mem s⟩

section

/-- A submonoid of a monoid `M` is a subset containing 1 and closed under multiplication. -/
/-
**Submonoid** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_3) → [MulOneClass M] → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submonoid of a monoid `M` is a subset containing 1 and closed under multiplica
tion.
-/
structure Submonoid (M : Type*) [MulOneClass M] extends Subsemigroup M where
  /-- A submonoid contains `1`. -/
  one_mem' : (1 : M) ∈ carrier

end

/-- A submonoid of a monoid `M` can be considered as a subsemigroup of that monoid. -/
add_decl_doc Submonoid.toSubsemigroup

/-- `SubmonoidClass S M` says `S` is a type of subsets `s ≤ M` that contain `1`
and are closed under `(*)` -/
/-
**SubmonoidClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_3) → (M : outParam (Type u_4)) → [MulOneClass M] → [SetLike S 
M] → Prop
参数：Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SubmonoidClass S M` says `S` is a type of subsets `s ≤ M` that contain `1`
and are closed under `(*)`
-/
class SubmonoidClass (S : Type*) (M : outParam Type*) [MulOneClass M] [SetLike S M] : Prop
    extends MulMemClass S M, OneMemClass S M

section

/-- An additive submonoid of an additive monoid `M` is a subset containing 0 and
  closed under addition. -/
/-
**AddSubmonoid** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_3) → [AddZeroClass M] → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive submonoid of an additive monoid `M` is a subset containing 0 and
  closed under addition.
-/
structure AddSubmonoid (M : Type*) [AddZeroClass M] extends AddSubsemigroup M where
  /-- An additive submonoid contains `0`. -/
  zero_mem' : (0 : M) ∈ carrier

end

/-- An additive submonoid of an additive monoid `M` can be considered as an
additive subsemigroup of that additive monoid. -/
add_decl_doc AddSubmonoid.toAddSubsemigroup

/-- `AddSubmonoidClass S M` says `S` is a type of subsets `s ≤ M` that contain `0`
and are closed under `(+)` -/
/-
**AddSubmonoidClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_3) → (M : outParam (Type u_4)) → [AddZeroClass M] → [SetLike S
 M] → Prop
参数：Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddSubmonoidClass S M` says `S` is a type of subsets `s ≤ M` that contain `0`
and are closed under `(+)`
-/
class AddSubmonoidClass (S : Type*) (M : outParam Type*) [AddZeroClass M] [SetLike S M] : Prop
  extends AddMemClass S M, ZeroMemClass S M

attribute [to_additive] Submonoid SubmonoidClass

@[to_additive (attr := aesop 90% (rule_sets := [SetLike]))]
/-
**pow_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : SetLike A M] [
SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ S
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_mem {M A} [Monoid M] [SetLike A M] [SubmonoidClass A M] {S : A} {x : M}
    (hx : x ∈ S) : ∀ n : ℕ, x ^ n ∈ S
  | 0 => by
    rw [pow_zero]
    exact OneMemClass.one_mem S
  | n + 1 => by
    rw [pow_succ]
    exact mul_mem (pow_mem hx n) hx

namespace Submonoid

@[to_additive]
/-
**Submonoid.toSubsemigroup_injective** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：toSubsemigroup_injective : (toSubsemigroup : Submonoid M -> Subsemigroup M
).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma toSubsemigroup_injective : (toSubsemigroup : Submonoid M → Subsemigroup M).Injective :=
  fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ by congr!

@[to_additive (attr := simp)]
/-
**Submonoid.toSubsemigroup_inj** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：toSubsemigroup_inj {s t : Submonoid M} : s.toSubsemigroup = t.toSubsemigro
up ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Submonoid.toSubsemigroup_injective`：toSubsemigroup_injective : (toSubsem
igroup : Submonoid M -> Subsemigroup M).Injective
-/
lemma toSubsemigroup_inj {s t : Submonoid M} : s.toSubsemigroup = t.toSubsemigroup ↔ s = t :=
  toSubsemigroup_injective.eq_iff

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Submonoid M) M where
  coe s := s.carrier
  coe_injective := SetLike.coe_injective.comp toSubsemigroup_injective
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : PartialOrder (Submonoid M) := .ofSetLike (Submonoid M) M

initialize_simps_projections Submonoid (carrier → coe, as_prefix coe)
initialize_simps_projections AddSubmonoid (carrier → coe, as_prefix coe)

/-- The actual `Submonoid` obtained from an element of a `SubmonoidClass` -/
@[to_additive (attr := simps) /-- The actual `AddSubmonoid` obtained from an element of a
`AddSubmonoidClass` -/]
/-
**Submonoid.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：ofClass {S M : Type*} [Monoid M] [SetLike S M] [SubmonoidClass S M] (s : S
) : Submonoid M
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofClass {S M : Type*} [Monoid M] [SetLike S M] [SubmonoidClass S M] (s : S) : Submonoid M :=
  ⟨⟨s, MulMemClass.mul_mem⟩, OneMemClass.one_mem s⟩

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CanLift (Set M) (Submonoid M) (↑)
    (fun s ↦ 1 ∈ s ∧ ∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) where
  prf s h := ⟨{ carrier := s, one_mem' := h.1, mul_mem' := h.2 }, rfl⟩

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubmonoidClass (Submonoid M) M where
  one_mem := Submonoid.one_mem'
  mul_mem {s} := s.mul_mem'

@[to_additive (attr := simp)]
/-
**Submonoid.mem_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_toSubsemigroup {s : Submonoid M} {x : M} : x in s.toSubsemigroup ↔ x i
n s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubsemigroup {s : Submonoid M} {x : M} : x ∈ s.toSubsemigroup ↔ x ∈ s :=
  Iff.rfl

@[to_additive]
/-
**Submonoid.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_carrier {s : Submonoid M} {x : M} : x in s.carrier ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : Submonoid M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[to_additive (attr := simp)]
/-
**Submonoid.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_mk {s : Subsemigroup M} {x : M} (h_one) : x in mk s h_one ↔ x in s
参数：h_one。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk {s : Subsemigroup M} {x : M} (h_one) : x ∈ mk s h_one ↔ x ∈ s :=
  Iff.rfl

@[to_additive (attr := simp)]
/-
**Submonoid.coe_set_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_set_mk {s : Subsemigroup M} (h_one) : (mk s h_one : Set M) = s
参数：h_one。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_set_mk {s : Subsemigroup M} (h_one) : (mk s h_one : Set M) = s :=
  rfl

@[to_additive (attr := simp)]
/-
**Submonoid.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mk_le_mk {s t : Subsemigroup M} (h_one) (h_one') : mk s h_one <= mk t h_on
e' ↔ s <= t
参数：h_one；h_one'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk {s t : Subsemigroup M} (h_one) (h_one') : mk s h_one ≤ mk t h_one' ↔ s ≤ t :=
  Iff.rfl

/-- Two submonoids are equal if they have the same elements. -/
@[to_additive (attr := ext) /-- Two `AddSubmonoid`s are equal if they have the same elements. -/]
/-
**Submonoid.ext** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) : S = T
参数：h : forall x, x in S ↔ x in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q

--- 原说明 ---
Two submonoids are equal if they have the same elements.
-/
theorem ext {S T : Submonoid M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy a submonoid replacing `carrier` with a set that is equal to it. -/
@[to_additive /-- Copy an additive submonoid replacing `carrier` with a set that is equal to it. -/]
/-
**Submonoid.copy** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：{M : Type u_1} → [inst : MulOneClass M] → (S : Submonoid M) → (s : Set M) 
→ s = ↑S → Submonoid M
参数：S : Submonoid M；s : Set M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy a submonoid replacing `carrier` with a set that is equal to it.
-/
protected def copy (S : Submonoid M) (s : Set M) (hs : s = S) : Submonoid M where
  carrier := s
  one_mem' := show 1 ∈ s from hs.symm ▸ S.one_mem'
  mul_mem' := hs.symm ▸ S.mul_mem'

variable {S : Submonoid M}

@[to_additive (attr := simp, norm_cast)]
/-
**Submonoid.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s
参数：hs : s = S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl

@[to_additive]
/-
**Submonoid.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S
参数：hs : s = S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S)

/-- A submonoid contains the monoid's 1. -/
@[to_additive /-- An `AddSubmonoid` contains the monoid's 0. -/]
/-
**Submonoid.one_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoid M), 1 ∈ S
参数：S : Submonoid M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M

--- 原说明 ---
A submonoid contains the monoid's 1.
-/
protected theorem one_mem : (1 : M) ∈ S :=
  one_mem S

/-- A submonoid is closed under multiplication. -/
@[to_additive /-- An `AddSubmonoid` is closed under addition. -/]
/-
**Submonoid.mul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoid M) {x y : M}, x ∈ S
 → y ∈ S → x * y ∈ S
参数：S : Submonoid M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M

--- 原说明 ---
A submonoid is closed under multiplication.
-/
protected theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S :=
  mul_mem

/-- The submonoid `M` of the monoid `M`. -/
@[to_additive /-- The additive submonoid `M` of the `AddMonoid M`. -/]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submonoid `M` of the monoid `M`.
-/
instance : Top (Submonoid M) :=
  ⟨{  carrier := Set.univ
      one_mem' := Set.mem_univ 1
      mul_mem' := fun _ _ => Set.mem_univ _ }⟩

/-- The trivial submonoid `{1}` of a monoid `M`. -/
@[to_additive /-- The trivial `AddSubmonoid` `{0}` of an `AddMonoid` `M`. -/]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial submonoid `{1}` of a monoid `M`.
-/
instance : Bot (Submonoid M) :=
  ⟨{  carrier := {1}
      one_mem' := Set.mem_singleton 1
      mul_mem' := fun ha hb => by
        push _ ∈ _ at *
        rw [ha, hb, mul_one] }⟩

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Submonoid M) :=
  ⟨⊥⟩

@[to_additive (attr := simp)]
/-
**Submonoid.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_bot {x : M} : x in (⊥ : Submonoid M) ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem mem_bot {x : M} : x ∈ (⊥ : Submonoid M) ↔ x = 1 :=
  Set.mem_singleton_iff

@[to_additive (attr := simp)]
/-
**Submonoid.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_top (x : M) : x in (⊤ : Submonoid M)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top (x : M) : x ∈ (⊤ : Submonoid M) :=
  Set.mem_univ x

@[to_additive (attr := simp, norm_cast)]
/-
**Submonoid.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_top : ((⊤ : Submonoid M) : Set M) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : Submonoid M) : Set M) = Set.univ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Submonoid.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_bot : ((⊥ : Submonoid M) : Set M) = {1}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ((⊥ : Submonoid M) : Set M) = {1} :=
  rfl

@[to_additive (attr := simp)]
/-
**Submonoid.mk_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：mk_eq_top (toSubsemigroup : Subsemigroup M) (one_mem') : mk toSubsemigroup
 one_mem' = ⊤ ↔ toSubsemigroup = ⊤
参数：toSubsemigroup : Subsemigroup M；one_mem'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mk_eq_top (toSubsemigroup : Subsemigroup M) (one_mem') :
    mk toSubsemigroup one_mem' = ⊤ ↔ toSubsemigroup = ⊤ := by simp [← SetLike.coe_set_eq]

@[to_additive (attr := simp)]
/-
**Submonoid.mk_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：mk_eq_bot (toSubsemigroup : Subsemigroup M) (one_mem') : mk toSubsemigroup
 one_mem' = ⊥ ↔ (toSubsemigroup : Set M) = {1}
参数：toSubsemigroup : Subsemigroup M；one_mem'。
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
lemma mk_eq_bot (toSubsemigroup : Subsemigroup M) (one_mem') :
    mk toSubsemigroup one_mem' = ⊥ ↔ (toSubsemigroup : Set M) = {1} := by
  simp [← SetLike.coe_set_eq]

/-- The inf of two submonoids is their intersection. -/
@[to_additive /-- The inf of two `AddSubmonoid`s is their intersection. -/]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inf of two submonoids is their intersection.
-/
instance : Min (Submonoid M) :=
  ⟨fun S₁ S₂ =>
    { carrier := S₁ ∩ S₂
      one_mem' := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem' := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[to_additive (attr := simp, norm_cast)]
/-
**Submonoid.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_inf (p p' : Submonoid M) : ((p ⊓ p' : Submonoid M) : Set M) = (p : Set
 M) inter p'
参数：p p' : Submonoid M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (p p' : Submonoid M) : ((p ⊓ p' : Submonoid M) : Set M) = (p : Set M) ∩ p' :=
  rfl

@[to_additive (attr := simp, grind =)]
/-
**Submonoid.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_inf {p p' : Submonoid M} {x : M} : x in p ⊓ p' ↔ x in p ∧ x in p'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {p p' : Submonoid M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

@[to_additive (attr := simp)]
/-
**Submonoid.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：subsingleton_iff : Subsingleton (Submonoid M) ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.mem_bot`：mem_bot {x : M} : x in (⊥ : Submonoid M) ↔ x = 1
· 使用定理 `Submonoid.mem_top`：mem_top (x : M) : x in (⊤ : Submonoid M)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subsingleton_iff : Subsingleton (Submonoid M) ↔ Subsingleton M :=
  ⟨fun _ =>
    ⟨fun x y =>
      have : ∀ i : M, i = 1 := fun i =>
        mem_bot.mp <| Subsingleton.elim (⊤ : Submonoid M) ⊥ ▸ mem_top i
      (this x).trans (this y).symm⟩,
    fun _ ↦ ⟨fun x y ↦ Submonoid.ext fun i ↦ by simp [← Subsingleton.elim 1 i]⟩⟩

@[to_additive (attr := simp)]
/-
**Submonoid.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：nontrivial_iff : Nontrivial (Submonoid M) ↔ Nontrivial M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `Submonoid.subsingleton_iff`：subsingleton_iff : Subsingleton (Submonoid M
) ↔ Subsingleton M
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
theorem nontrivial_iff : Nontrivial (Submonoid M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans subsingleton_iff).trans
      not_nontrivial_iff_subsingleton.symm)

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton M] : Unique (Submonoid M) :=
  ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ (subsingleton_iff.mpr ‹_›) a _⟩

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial M] : Nontrivial (Submonoid M) :=
  nontrivial_iff.mpr ‹_›

end Submonoid

namespace MonoidHom

variable [MulOneClass N]

open Submonoid

/-- The submonoid of elements `x : M` such that `f x = g x` -/
@[to_additive /-- The additive submonoid of elements `x : M` such that `f x = g x` -/]
/-
**MonoidHom.eqLocusM** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：eqLocusM (f g : M ->* N) : Submonoid M where carrier
参数：f g : M ->* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submonoid of elements `x : M` such that `f x = g x`
-/
def eqLocusM (f g : M →* N) : Submonoid M where
  carrier := { x | f x = g x }
  one_mem' := by rw [Set.mem_ofPred_eq, f.map_one, g.map_one]
  mul_mem' (hx : _ = _) (hy : _ = _) := by simp [*]

@[to_additive (attr := simp)]
/-
**MonoidHom.mem_eqLocusM** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mem_eqLocusM {f g : M ->* N} {x : M} : x in f.eqLocusM g ↔ f x = g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_eqLocusM {f g : M →* N} {x : M} : x ∈ f.eqLocusM g ↔ f x = g x := Iff.rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.eqLocusM_same** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：eqLocusM_same (f : M ->* N) : f.eqLocusM f = ⊤
参数：f : M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `eq_self_iff_true`：∀ {α : Sort u_1} (a : α), a = a ↔ True
-/
theorem eqLocusM_same (f : M →* N) : f.eqLocusM f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

@[to_additive]
/-
**MonoidHom.eq_of_eqOn_topM** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：eq_of_eqOn_topM {f g : M ->* N} (h : Set.EqOn f g (⊤ : Submonoid M)) : f =
 g
参数：h : Set.EqOn f g (⊤ : Submonoid M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `trivial`：True
-/
theorem eq_of_eqOn_topM {f g : M →* N} (h : Set.EqOn f g (⊤ : Submonoid M)) : f = g :=
  ext fun _ => h trivial

end MonoidHom

end NonAssoc

namespace OneMemClass

variable {A M₁ : Type*} [SetLike A M₁] [One M₁] [hA : OneMemClass A M₁] (S' : A)

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits a zero. -/]
/-
**OneMemClass.one** 是 Mathlib 中的一个实例，位于命名空间 `OneMemClass`。
形式化陈述：one : One S'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s

--- 原说明 ---
A submonoid of a monoid inherits a 1.
-/
instance one : One S' :=
  ⟨⟨1, OneMemClass.one_mem S'⟩⟩

@[to_additive (attr := simp, norm_cast)]
/-
**OneMemClass.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `OneMemClass`。
形式化陈述：coe_one : ((1 : S') : M₁) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : S') : M₁) = 1 :=
  rfl

variable {S'}

@[to_additive (attr := simp, norm_cast)]
/-
**OneMemClass.coe_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `OneMemClass`。
形式化陈述：coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1 :=
  (Subtype.ext_iff.symm : (x : M₁) = (1 : S') ↔ x = 1)

variable (S')

@[to_additive]
/-
**OneMemClass.one_def** 是 Mathlib 中的一个定理，位于命名空间 `OneMemClass`。
形式化陈述：one_def : (1 : S') = ⟨1, OneMemClass.one_mem S'⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : S') = ⟨1, OneMemClass.one_mem S'⟩ :=
  rfl

end OneMemClass

variable {A : Type*} [MulOneClass M] [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

namespace SubmonoidClass

/-- A submonoid of a monoid inherits a power operator. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits a scalar multiplication. -/]
/-
**SubmonoidClass.instPow** 是 Mathlib 中的一个实例，位于命名空间 `SubmonoidClass`。
形式化陈述：instPow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] (S :
 A) : Pow S Nat
参数：S : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submonoid of a monoid inherits a power operator.
-/
instance instPow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] (S : A) : Pow S ℕ :=
  ⟨fun a n => ⟨a.1 ^ n, pow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]
/-
**SubmonoidClass.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `SubmonoidClass`。
形式化陈述：coe_pow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] {S :
 A} (x : S) (n : Nat) : ↑(x ^ n) = (x : M) ^ n
参数：x : S；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] {S : A} (x : S)
    (n : ℕ) : ↑(x ^ n) = (x : M) ^ n :=
  rfl

@[to_additive (attr := simp)]
/-
**SubmonoidClass.mk_pow** 是 Mathlib 中的一个定理，位于命名空间 `SubmonoidClass`。
形式化陈述：mk_pow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] {S : 
A} (x : M) (hx : x in S) (n : Nat) : (⟨x, hx⟩ : S) ^ n = ⟨x ^ n, pow_mem hx n⟩
参数：x : M；hx : x in S；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_pow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] {S : A} (x : M)
    (hx : x ∈ S) (n : ℕ) : (⟨x, hx⟩ : S) ^ n = ⟨x ^ n, pow_mem hx n⟩ :=
  rfl

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive
  /-- An `AddSubmonoid` of a unital additive magma inherits a unital additive magma structure. -/]
/-
**SubmonoidClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubmonoidClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 75) toMulOneClass {M : Type*} [MulOneClass M] {A : Type*} [SetLike A M]
    [SubmonoidClass A M] (S : A) : MulOneClass S := fast_instance%
  Subtype.coe_injective.mulOneClass Subtype.val rfl (fun _ _ => rfl)
/-
**SubmonoidClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubmonoidClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : A) [IsDedekindFiniteMonoid M] : IsDedekindFiniteMonoid S where
  mul_eq_one_symm eq := Subtype.ext (mul_eq_one_symm <| congr_arg (·.1) eq)

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits an `AddMonoid` structure. -/]
/-
**SubmonoidClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubmonoidClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submonoid of a monoid inherits a monoid structure.
-/
instance (priority := 75) toMonoid {M : Type*} [Monoid M] {A : Type*} [SetLike A M]
    [SubmonoidClass A M] (S : A) : Monoid S := fast_instance%
  Subtype.coe_injective.monoid Subtype.val rfl (fun _ _ => rfl) (fun _ _ => rfl)

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a `CommMonoid` is a `CommMonoid`. -/
@[to_additive /-- An `AddSubmonoid` of an `AddCommMonoid` is an `AddCommMonoid`. -/]
/-
**SubmonoidClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubmonoidClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submonoid of a `CommMonoid` is a `CommMonoid`.
-/
instance (priority := 75) toCommMonoid {M} [CommMonoid M] {A : Type*} [SetLike A M]
    [SubmonoidClass A M] (S : A) : CommMonoid S := fast_instance%
  Subtype.coe_injective.commMonoid Subtype.val rfl (fun _ _ => rfl) fun _ _ => rfl

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive /-- The natural monoid hom from an `AddSubmonoid` of `AddMonoid` `M` to `M`. -/]
/-
**SubmonoidClass.subtype** 是 Mathlib 中的一个定义，位于命名空间 `SubmonoidClass`。
形式化陈述：subtype : S' ->* M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural monoid hom from a submonoid of monoid `M` to `M`.
-/
def subtype : S' →* M where
  toFun := Subtype.val; map_one' := rfl; map_mul' _ _ := by simp

variable {S'} in
@[to_additive (attr := simp)]
/-
**SubmonoidClass.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `SubmonoidClass`。
形式化陈述：subtype_apply (x : S') : SubmonoidClass.subtype S' x = x
参数：x : S'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_apply (x : S') :
    SubmonoidClass.subtype S' x = x := rfl

@[to_additive]
/-
**SubmonoidClass.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `SubmonoidClass`。
形式化陈述：subtype_injective : Function.Injective (SubmonoidClass.subtype S')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective :
    Function.Injective (SubmonoidClass.subtype S') :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
/-
**SubmonoidClass.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `SubmonoidClass`。
形式化陈述：coe_subtype : (SubmonoidClass.subtype S' : S' -> M) = Subtype.val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype : (SubmonoidClass.subtype S' : S' → M) = Subtype.val :=
  rfl

end SubmonoidClass

namespace Submonoid

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

/-- A submonoid of a monoid inherits a multiplication. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits an addition. -/]
/-
**Submonoid.mul** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：mul : Mul S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submonoid of a monoid inherits a multiplication.
-/
instance mul : Mul S :=
  ⟨fun a b => ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits a zero. -/]
/-
**Submonoid.one** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：one : One S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S

--- 原说明 ---
A submonoid of a monoid inherits a 1.
-/
instance one : One S :=
  ⟨⟨_, S.one_mem⟩⟩

@[to_additive (attr := simp, norm_cast)]
/-
**Submonoid.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
参数：x y : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Submonoid.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_one : ((1 : S) : M) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : S) : M) = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**Submonoid.mk_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：mk_eq_one {a : M} {ha} : (⟨a, ha⟩ : S) = 1 ↔ a = 1
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
lemma mk_eq_one {a : M} {ha} : (⟨a, ha⟩ : S) = 1 ↔ a = 1 := by simp [← SetLike.coe_eq_coe]

@[to_additive (attr := simp)]
/-
**Submonoid.mk_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mk_mul_mk (x y : M) (hx : x in S) (hy : y in S) : (⟨x, hx⟩ : S) * ⟨y, hy⟩ 
= ⟨x * y, S.mul_mem hx hy⟩
参数：x y : M；hx : x in S；hy : y in S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mul_mk (x y : M) (hx : x ∈ S) (hy : y ∈ S) :
    (⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨x * y, S.mul_mem hx hy⟩ :=
  rfl

@[to_additive]
/-
**Submonoid.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mul_def (x y : S) : x * y = ⟨x * y, S.mul_mem x.2 y.2⟩
参数：x y : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (x y : S) : x * y = ⟨x * y, S.mul_mem x.2 y.2⟩ :=
  rfl

@[to_additive]
/-
**Submonoid.one_def** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：one_def : (1 : S) = ⟨1, S.one_mem⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : S) = ⟨1, S.one_mem⟩ :=
  rfl

/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive
  /-- An `AddSubmonoid` of a unital additive magma inherits a unital additive magma structure. -/]
/-
**Submonoid.toMulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：toMulOneClass {M : Type*} [MulOneClass M] (S : Submonoid M) : MulOneClass 
S
参数：S : Submonoid M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
instance toMulOneClass {M : Type*} [MulOneClass M] (S : Submonoid M) : MulOneClass S :=
  SubmonoidClass.toMulOneClass S

@[to_additive]
/-
**Submonoid.pow_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ {M : Type u_5} [inst : Monoid M] (S : Submonoid M) {x : M}, x ∈ S → ∀ (n
 : ℕ), x ^ n ∈ S
参数：S : Submonoid M；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
protected theorem pow_mem {M : Type*} [Monoid M] (S : Submonoid M) {x : M} (hx : x ∈ S) (n : ℕ) :
    x ^ n ∈ S :=
  pow_mem hx n

/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive /-- An `AddSubmonoid` of an `AddMonoid` inherits an `AddMonoid` structure. -/]
/-
**Submonoid.toMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：toMonoid {M : Type*} [Monoid M] (S : Submonoid M) : Monoid S
参数：S : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submonoid of a monoid inherits a monoid structure.
-/
instance toMonoid {M : Type*} [Monoid M] (S : Submonoid M) : Monoid S :=
  SubmonoidClass.toMonoid S

/-- A submonoid of a `CommMonoid` is a `CommMonoid`. -/
@[to_additive /-- An `AddSubmonoid` of an `AddCommMonoid` is an `AddCommMonoid`. -/]
/-
**Submonoid.toCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：toCommMonoid {M} [CommMonoid M] (S : Submonoid M) : CommMonoid S
参数：S : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submonoid of a `CommMonoid` is a `CommMonoid`.
-/
instance toCommMonoid {M} [CommMonoid M] (S : Submonoid M) : CommMonoid S :=
  SubmonoidClass.toCommMonoid S

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive /-- The natural monoid hom from an `AddSubmonoid` of `AddMonoid` `M` to `M`. -/]
/-
**Submonoid.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：subtype : S ->* M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural monoid hom from a submonoid of monoid `M` to `M`.
-/
def subtype : S →* M where
  toFun := Subtype.val; map_one' := rfl; map_mul' _ _ := by simp

@[to_additive (attr := simp)]
/-
**Submonoid.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：subtype_apply {s : Submonoid M} (x : s) : s.subtype x = x
参数：x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_apply {s : Submonoid M} (x : s) :
    s.subtype x = x := rfl

@[to_additive]
/-
**Submonoid.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：subtype_injective (s : Submonoid M) : Function.Injective s.subtype
参数：s : Submonoid M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective (s : Submonoid M) :
    Function.Injective s.subtype :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
/-
**Submonoid.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_subtype : ⇑S.subtype = Subtype.val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype : ⇑S.subtype = Subtype.val :=
  rfl

end Submonoid

