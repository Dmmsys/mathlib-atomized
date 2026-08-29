/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Set.CoeSort
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Nat.Notation

/-!
# Definition of the `Finite` typeclass

This file defines a typeclass `Finite` saying that `α : Sort*` is finite. A type is `Finite` if it
is equivalent to `Fin n` for some `n`. We also define `Infinite α` as a typeclass equivalent to
`¬Finite α`.

The `Finite` predicate has no computational relevance and, being `Prop`-valued, gets to enjoy proof
irrelevance -- it represents the mere fact that the type is finite. While the `Finite` class also
represents finiteness of a type, a key difference is that a `Fintype` instance represents finiteness
in a computable way: it gives a concrete algorithm to produce a `Finset` whose elements enumerate
the terms of the given type. As such, one generally relies on congruence lemmas when rewriting
expressions involving `Fintype` instances.

Every `Fintype` instance automatically gives a `Finite` instance, see `Fintype.finite`, but not vice
versa. Every `Fintype` instance should be computable since they are meant for computation. If it's
not possible to write a computable `Fintype` instance, one should prefer writing a `Finite` instance
instead.

## Main definitions

* `Finite α` denotes that `α` is a finite type.
* `Infinite α` denotes that `α` is an infinite type.
* `Set.Finite : Set α → Prop`
* `Set.Infinite : Set α → Prop`
* `Set.toFinite` to prove `Set.Finite` for a `Set` from a `Finite` instance.

## Implementation notes

This file defines both the type-level `Finite` class and the set-level `Set.Finite` definition.

The definition of `Finite α` is not just `Nonempty (Fintype α)` since `Fintype` requires
that `α : Type*`, and the definition in this module allows for `α : Sort*`. This means
we can write the instance `Finite.prop`.

A finite set is defined to be a set whose coercion to a type has a `Finite` instance.

There are two components to finiteness constructions. The first is `Fintype` instances for each
construction. This gives a way to actually compute a `Finset` that represents the set, and these
may be accessed using `set.toFinset`. This gets the `Finset` in the correct form, since otherwise
`Finset.univ : Finset s` is a `Finset` for the subtype for `s`. The second component is
"constructors" for `Set.Finite` that give proofs that `Fintype` instances exist classically given
other `Set.Finite` proofs. Unlike the `Fintype` instances, these *do not* use any decidability
instances since they do not compute anything.

## Tags

finite, fintype, finite sets
-/

@[expose] public section

assert_not_exists Finset MonoidWithZero IsOrderedRing

universe u v

open Function

variable {α β : Sort*}

/--
Definition of `inductive` / `inductive` 的定义

English:
class inductive
  parameters: Finite (α : Sort*)
  (no additional axioms)

中文:
类 inductive
  参数: Finite (α : Sort*)
  (无附加公理)
-/
class inductive Finite (α : Sort*) : Prop
  | intro {n : Nat} : α ≃ Fin n -> Finite _

/--
theorem `finite_iff_exists_equiv_fin` / 定理 `finite_iff_exists_equiv_fin`

English:
theorem finite_iff_exists_equiv_fin
  given: {α : Sort*}
  statement: Finite α ↔ exists n, Nonempty (α ≃ Fin n)
  proof: ⟨fun ⟨e⟩ => ⟨_, ⟨e⟩⟩, fun ⟨_, ⟨e⟩⟩ => ⟨e⟩⟩

中文:
定理 finite_iff_exists_equiv_fin
  条件: {α : Sort*}
  结论: Finite α ↔ 存在 n, Nonempty (α ≃ Fin n)
  证明: ⟨fun ⟨e⟩ => ⟨_, ⟨e⟩⟩, fun ⟨_, ⟨e⟩⟩ => ⟨e⟩⟩
-/
theorem finite_iff_exists_equiv_fin {α : Sort*} : Finite α ↔ exists n, Nonempty (α ≃ Fin n) :=
  ⟨fun ⟨e⟩ => ⟨_, ⟨e⟩⟩, fun ⟨_, ⟨e⟩⟩ => ⟨e⟩⟩

/--
theorem `Finite.exists_equiv_fin` / 定理 `Finite.exists_equiv_fin`

English:
theorem Finite.exists_equiv_fin
  given: (α : Sort*) [h : Finite α]
  statement: exists n : Nat, Nonempty (α ≃ Fin n)
  proof: finite_iff_exists_equiv_fin.mp h

中文:
定理 Finite.exists_equiv_fin
  条件: (α : Sort*) [h : Finite α]
  结论: 存在 n : 自然数, Nonempty (α ≃ Fin n)
  证明: finite_iff_exists_equiv_fin.mp h

Depends on / 依赖: finite_iff_exists_equiv_fin, finite_iff_exists_equiv_fin.mp
-/
theorem Finite.exists_equiv_fin (α : Sort*) [h : Finite α] : exists n : Nat, Nonempty (α ≃ Fin n) :=
  finite_iff_exists_equiv_fin.mp h

/--
theorem `Finite.of_equiv` / 定理 `Finite.of_equiv`

English:
theorem Finite.of_equiv
  given: (α : Sort*) [h : Finite α] (f : α ≃ β)
  statement: Finite β
  proof: let ⟨e⟩ := h; ⟨f.symm.trans e⟩

中文:
定理 Finite.of_equiv
  条件: (α : Sort*) [h : Finite α] (f : α ≃ β)
  结论: Finite β
  证明: let ⟨e⟩ := h; ⟨f.symm.trans e⟩

Depends on / 依赖: f.symm.trans
-/
theorem Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) : Finite β :=
  let ⟨e⟩ := h; ⟨f.symm.trans e⟩

/--
theorem `Equiv.finite_iff` / 定理 `Equiv.finite_iff`

English:
theorem Equiv.finite_iff
  given: (f : α ≃ β)
  statement: Finite α ↔ Finite β
  proof: ⟨fun _ => Finite.of_equiv _ f, fun _ => Finite.of_equiv _ f.symm⟩

中文:
定理 Equiv.finite_iff
  条件: (f : α ≃ β)
  结论: Finite α ↔ Finite β
  证明: ⟨fun _ => Finite.of_equiv _ f, fun _ => Finite.of_equiv _ f.symm⟩

Depends on / 依赖: Finite, Finite.of_equiv, f.symm, of_equiv
-/
theorem Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β :=
  ⟨fun _ => Finite.of_equiv _ f, fun _ => Finite.of_equiv _ f.symm⟩

/--
theorem `Function.Bijective.finite_iff` / 定理 `Function.Bijective.finite_iff`

English:
theorem Function.Bijective.finite_iff
  given: {f : α -> β} (h : Bijective f)
  statement: Finite α ↔ Finite β
  proof: (Equiv.ofBijective f h).finite_iff

中文:
定理 Function.Bijective.finite_iff
  条件: {f : α -> β} (h : Bijective f)
  结论: Finite α ↔ Finite β
  证明: (Equiv.ofBijective f h).finite_iff

Depends on / 依赖: Equiv.ofBijective, finite_iff, ofBijective
-/
theorem Function.Bijective.finite_iff {f : α -> β} (h : Bijective f) : Finite α ↔ Finite β :=
  (Equiv.ofBijective f h).finite_iff

/--
theorem `Finite.ofBijective` / 定理 `Finite.ofBijective`

English:
theorem Finite.ofBijective
  given: [Finite α] {f : α -> β} (h : Bijective f)
  statement: Finite β
  proof: h.finite_iff.mp ‹_›

中文:
定理 Finite.ofBijective
  条件: [Finite α] {f : α -> β} (h : Bijective f)
  结论: Finite β
  证明: h.finite_iff.mp ‹_›

Depends on / 依赖: finite_iff, h.finite_iff.mp
-/
theorem Finite.ofBijective [Finite α] {f : α -> β} (h : Bijective f) : Finite β :=
  h.finite_iff.mp ‹_›

variable (α) in
/--
theorem `Finite.nonempty_decidableEq` / 定理 `Finite.nonempty_decidableEq`

English:
theorem Finite.nonempty_decidableEq
  given: [Finite α]
  statement: Nonempty (DecidableEq α)
  proof: let ⟨_n, ⟨e⟩⟩ := Finite.exists_equiv_fin α; ⟨e.decidableEq⟩

中文:
定理 Finite.nonempty_decidableEq
  条件: [Finite α]
  结论: Nonempty (DecidableEq α)
  证明: let ⟨_n, ⟨e⟩⟩ := Finite.exists_equiv_fin α; ⟨e.decidableEq⟩

Depends on / 依赖: Finite, Finite.exists_equiv_fin, decidableEq, e.decidableEq, exists_equiv_fin
-/
theorem Finite.nonempty_decidableEq [Finite α] : Nonempty (DecidableEq α) :=
  let ⟨_n, ⟨e⟩⟩ := Finite.exists_equiv_fin α; ⟨e.decidableEq⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: α] : Finite (PLift α)
  body: Finite.of_equiv α Equiv.plift.symm

中文:
实例 [Finite
  签名: α] : Finite (PLift α)
  定义体: Finite.of_equiv α Equiv.plift.symm

Depends on / 依赖: Equiv.plift.symm, Finite, Finite.of_equiv, of_equiv
-/
instance [Finite α] : Finite (PLift α) :=
  Finite.of_equiv α Equiv.plift.symm

instance {α : Type v} [Finite α] : Finite (ULift.{u} α) :=
  Finite.of_equiv α Equiv.ulift.symm

/--
Definition of `Infinite` / `Infinite` 的定义

English:
class Infinite
  parameters: (α : Sort*)
  axioms and operations (1):
    - not_finite : ¬Finite α

中文:
类 Infinite
  参数: (α : Sort*)
  公理与运算 (1 个):
    - not_finite : ¬Finite α
-/
class Infinite (α : Sort*) : Prop where
  /-- assertion that `α` is `¬Finite` -/
  not_finite : ¬Finite α

@[simp, push]
/--
theorem `not_finite_iff_infinite` / 定理 `not_finite_iff_infinite`

English:
theorem not_finite_iff_infinite
  statement: ¬Finite α ↔ Infinite α
  proof: ⟨Infinite.mk, fun h => h.1⟩

@[simp, push]

中文:
定理 not_finite_iff_infinite
  结论: ¬Finite α ↔ Infinite α
  证明: ⟨Infinite.mk, fun h => h.1⟩

@[simp, push]

Depends on / 依赖: Infinite, Infinite.mk
-/
theorem not_finite_iff_infinite : ¬Finite α ↔ Infinite α :=
  ⟨Infinite.mk, fun h => h.1⟩

@[simp, push]
/--
theorem `not_infinite_iff_finite` / 定理 `not_infinite_iff_finite`

English:
theorem not_infinite_iff_finite
  statement: ¬Infinite α ↔ Finite α
  proof: not_finite_iff_infinite.not_right.symm

中文:
定理 not_infinite_iff_finite
  结论: ¬Infinite α ↔ Finite α
  证明: not_finite_iff_infinite.not_right.symm

Depends on / 依赖: not_finite_iff_infinite, not_finite_iff_infinite.not_right.symm, not_right
-/
theorem not_infinite_iff_finite : ¬Infinite α ↔ Finite α :=
  not_finite_iff_infinite.not_right.symm

/--
theorem `Equiv.infinite_iff` / 定理 `Equiv.infinite_iff`

English:
theorem Equiv.infinite_iff
  given: (e : α ≃ β)
  statement: Infinite α ↔ Infinite β
  proof: not_finite_iff_infinite.symm.trans e.finite_iff.not.trans not_finite_iff_infinite

中文:
定理 Equiv.infinite_iff
  条件: (e : α ≃ β)
  结论: Infinite α ↔ Infinite β
  证明: not_finite_iff_infinite.symm.trans e.finite_iff.not.trans not_finite_iff_infinite

Depends on / 依赖: e.finite_iff.not.trans, finite_iff, not_finite_iff_infinite, not_finite_iff_infinite.symm.trans
-/
theorem Equiv.infinite_iff (e : α ≃ β) : Infinite α ↔ Infinite β :=
not_finite_iff_infinite.symm.trans e.finite_iff.not.trans not_finite_iff_infinite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Infinite
  signature: α] : Infinite (PLift α)
  body: Equiv.plift.infinite_iff.2 ‹_›

中文:
实例 [Infinite
  签名: α] : Infinite (PLift α)
  定义体: Equiv.plift.infinite_iff.2 ‹_›

Depends on / 依赖: Equiv.plift.infinite_iff, infinite_iff
-/
instance [Infinite α] : Infinite (PLift α) :=
  Equiv.plift.infinite_iff.2 ‹_›

instance {α : Type v} [Infinite α] : Infinite (ULift.{u} α) :=
  Equiv.ulift.infinite_iff.2 ‹_›

/--
theorem `finite_or_infinite` / 定理 `finite_or_infinite`

English:
theorem finite_or_infinite
  given: (α : Sort*)
  statement: Finite α ∨ Infinite α
  proof: or_iff_not_imp_left.2 not_finite_iff_infinite.1

中文:
定理 finite_or_infinite
  条件: (α : Sort*)
  结论: Finite α ∨ Infinite α
  证明: or_iff_not_imp_left.2 not_finite_iff_infinite.1

Depends on / 依赖: not_finite_iff_infinite, or_iff_not_imp_left
-/
theorem finite_or_infinite (α : Sort*) : Finite α ∨ Infinite α :=
  or_iff_not_imp_left.2 not_finite_iff_infinite.1

/--
theorem `not_finite` / 定理 `not_finite`

English:
theorem not_finite
  given: (α : Sort*) [Infinite α] [Finite α]
  statement: False
  proof: @Infinite.not_finite α ‹_› ‹_›

中文:
定理 not_finite
  条件: (α : Sort*) [Infinite α] [Finite α]
  结论: False
  证明: @Infinite.not_finite α ‹_› ‹_›

Depends on / 依赖: Infinite, Infinite.not_finite, not_finite
-/
theorem not_finite (α : Sort*) [Infinite α] [Finite α] : False :=
  @Infinite.not_finite α ‹_› ‹_›

/--
theorem `Finite.false` / 定理 `Finite.false`

English:
theorem Finite.false
  given: [Infinite α] (_ : Finite α)
  statement: False
  proof: not_finite α

中文:
定理 Finite.false
  条件: [Infinite α] (_ : Finite α)
  结论: False
  证明: not_finite α
-/
protected theorem Finite.false [Infinite α] (_ : Finite α) : False :=
  not_finite α

/--
theorem `Infinite.false` / 定理 `Infinite.false`

English:
theorem Infinite.false
  given: [Finite α] (_ : Infinite α)
  statement: False
  proof: @Infinite.not_finite α ‹_› ‹_›

alias ⟨Finite.of_not_infinite, Finite.not_infinite⟩ := not_infinite_iff_finite

中文:
定理 Infinite.false
  条件: [Finite α] (_ : Infinite α)
  结论: False
  证明: @Infinite.not_finite α ‹_› ‹_›

alias ⟨Finite.of_not_infinite, Finite.not_infinite⟩ := not_infinite_iff_finite
-/
protected theorem Infinite.false [Finite α] (_ : Infinite α) : False :=
  @Infinite.not_finite α ‹_› ‹_›

alias ⟨Finite.of_not_infinite, Finite.not_infinite⟩ := not_infinite_iff_finite

/--
Instance `Bool.instFinite` / 实例 `Bool.instFinite`

English:
instance Bool.instFinite
  signature: : Finite Bool
  body: .intro finTwoEquiv.symm

中文:
实例 Bool.instFinite
  签名: : Finite 布尔
  定义体: .intro finTwoEquiv.symm

Depends on / 依赖: finTwoEquiv, finTwoEquiv.symm
-/
instance Bool.instFinite : Finite Bool := .intro finTwoEquiv.symm
/--
Instance `Prop.instFinite` / 实例 `Prop.instFinite`

English:
instance Prop.instFinite
  signature: : Finite Prop
  body: .of_equiv _ Equiv.propEquivBool.symm

中文:
实例 Prop.instFinite
  签名: : Finite 命题
  定义体: .of_equiv _ Equiv.propEquivBool.symm

Depends on / 依赖: Equiv.propEquivBool.symm, of_equiv, propEquivBool
-/
instance Prop.instFinite : Finite Prop := .of_equiv _ Equiv.propEquivBool.symm

section Set

/-!
### Finite sets
-/

variable {α : Type u} {β : Type v}

namespace Set

/--
Definition of `Finite` / `Finite` 的定义

English:
definition Finite
  signature: (s : Set α)
  body: Finite s

中文:
定义 Finite
  签名: (s : Set α)
  定义体: Finite s
-/
protected def Finite (s : Set α) : Prop := Finite s

-- The `protected` attribute does not take effect within the same namespace block.
end Set

namespace Set

/--
theorem `finite_coe_iff` / 定理 `finite_coe_iff`

English:
theorem finite_coe_iff
  given: {s : Set α}
  statement: Finite s ↔ s.Finite
  proof: .rfl

中文:
定理 finite_coe_iff
  条件: {s : Set α}
  结论: Finite s ↔ s.Finite
  证明: .rfl
-/
theorem finite_coe_iff {s : Set α} : Finite s ↔ s.Finite := .rfl

/--
theorem `toFinite` / 定理 `toFinite`

English:
theorem toFinite
  given: (s : Set α) [Finite s]
  statement: s.Finite
  proof: ‹_›

中文:
定理 toFinite
  条件: (s : Set α) [Finite s]
  结论: s.Finite
  证明: ‹_›
-/
theorem toFinite (s : Set α) [Finite s] : s.Finite := ‹_›

/--
theorem `Finite.to_subtype` / 定理 `Finite.to_subtype`

English:
theorem Finite.to_subtype
  given: {s : Set α} (h : s.Finite)
  statement: Finite s
  proof: h

中文:
定理 Finite.to_subtype
  条件: {s : Set α} (h : s.Finite)
  结论: Finite s
  证明: h
-/
protected theorem Finite.to_subtype {s : Set α} (h : s.Finite) : Finite s := h

/--
Definition of `Infinite` / `Infinite` 的定义

English:
definition Infinite
  signature: (s : Set α)
  body: ¬s.Finite

@[simp, push]

中文:
定义 Infinite
  签名: (s : Set α)
  定义体: ¬s.Finite

@[simp, push]
-/
protected def Infinite (s : Set α) : Prop :=
  ¬s.Finite

@[simp, push]
/--
theorem `not_finite` / 定理 `not_finite`

English:
theorem not_finite
  given: {s : Set α}
  statement: ¬s.Finite ↔ s.Infinite
  proof: .rfl

@[simp, push]

中文:
定理 not_finite
  条件: {s : Set α}
  结论: ¬s.Finite ↔ s.Infinite
  证明: .rfl

@[simp, push]
-/
theorem not_finite {s : Set α} : ¬s.Finite ↔ s.Infinite := .rfl

@[simp, push]
/--
theorem `not_infinite` / 定理 `not_infinite`

English:
theorem not_infinite
  given: {s : Set α}
  statement: ¬s.Infinite ↔ s.Finite
  proof: not_not

alias ⟨_, Finite.not_infinite⟩ := not_infinite

中文:
定理 not_infinite
  条件: {s : Set α}
  结论: ¬s.Infinite ↔ s.Finite
  证明: not_not

alias ⟨_, Finite.not_infinite⟩ := not_infinite

Depends on / 依赖: not_not
-/
theorem not_infinite {s : Set α} : ¬s.Infinite ↔ s.Finite :=
  not_not

alias ⟨_, Finite.not_infinite⟩ := not_infinite

/--
lemma `Infinite.not_finite` / 引理 `Infinite.not_finite`

English:
lemma Infinite.not_finite
  given: {s : Set α} (hs : s.Infinite)
  statement: ¬ s.Finite
  proof: hs

中文:
引理 Infinite.not_finite
  条件: {s : Set α} (hs : s.Infinite)
  结论: ¬ s.Finite
  证明: hs
-/
@[simp] lemma Infinite.not_finite {s : Set α} (hs : s.Infinite) : ¬ s.Finite := hs

attribute [simp] Finite.not_infinite

/--
theorem `finite_or_infinite` / 定理 `finite_or_infinite`

English:
theorem finite_or_infinite
  given: (s : Set α)
  statement: s.Finite ∨ s.Infinite
  proof: em _

中文:
定理 finite_or_infinite
  条件: (s : Set α)
  结论: s.Finite ∨ s.Infinite
  证明: em _
-/
protected theorem finite_or_infinite (s : Set α) : s.Finite ∨ s.Infinite :=
  em _

/--
theorem `infinite_or_finite` / 定理 `infinite_or_finite`

English:
theorem infinite_or_finite
  given: (s : Set α)
  statement: s.Infinite ∨ s.Finite
  proof: em' _

中文:
定理 infinite_or_finite
  条件: (s : Set α)
  结论: s.Infinite ∨ s.Finite
  证明: em' _
-/
protected theorem infinite_or_finite (s : Set α) : s.Infinite ∨ s.Finite :=
  em' _

end Set

/--
theorem `Equiv.set_finite_iff` / 定理 `Equiv.set_finite_iff`

English:
theorem Equiv.set_finite_iff
  given: {s : Set α} {t : Set β} (hst : s ≃ t)
  statement: s.Finite ↔ t.Finite
  proof: by
  simp_rw [← Set.finite_coe_iff, hst.finite_iff]

中文:
定理 Equiv.set_finite_iff
  条件: {s : Set α} {t : Set β} (hst : s ≃ t)
  结论: s.Finite ↔ t.Finite
  证明: by
  simp_rw [← Set.finite_coe_iff, hst.finite_iff]

Depends on / 依赖: Set.finite_coe_iff, finite_coe_iff, finite_iff, hst.finite_iff, simp_rw
-/
theorem Equiv.set_finite_iff {s : Set α} {t : Set β} (hst : s ≃ t) : s.Finite ↔ t.Finite := by
  simp_rw [← Set.finite_coe_iff, hst.finite_iff]

namespace Set

/-! ### Infinite sets -/

variable {s t : Set α}

/--
theorem `infinite_coe_iff` / 定理 `infinite_coe_iff`

English:
theorem infinite_coe_iff
  given: {s : Set α}
  statement: Infinite s ↔ s.Infinite
  proof: not_finite_iff_infinite.symm.trans finite_coe_iff.not

alias ⟨_, Infinite.to_subtype⟩ := infinite_coe_iff

中文:
定理 infinite_coe_iff
  条件: {s : Set α}
  结论: Infinite s ↔ s.Infinite
  证明: not_finite_iff_infinite.symm.trans finite_coe_iff.not

alias ⟨_, Infinite.to_subtype⟩ := infinite_coe_iff

Depends on / 依赖: finite_coe_iff, finite_coe_iff.not, not_finite_iff_infinite, not_finite_iff_infinite.symm.trans
-/
theorem infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infinite :=
  not_finite_iff_infinite.symm.trans finite_coe_iff.not

alias ⟨_, Infinite.to_subtype⟩ := infinite_coe_iff

end Set

end Set
