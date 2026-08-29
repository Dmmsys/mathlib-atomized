/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Tactic.Push.Attr

/-!
# Nontrivial types

A type is *nontrivial* if it contains at least two elements. This is useful in particular for rings
(where it is equivalent to the fact that zero is different from one) and for vector spaces
(where it is equivalent to the fact that the dimension is positive).

We introduce a typeclass `Nontrivial` formalizing this property.

Basic results about nontrivial types are in `Mathlib/Logic/Nontrivial/Basic.lean`.
-/

public section

variable {α : Type*} {β : Type*}

/--
Definition of `Nontrivial` / `Nontrivial` 的定义

English:
class Nontrivial
  parameters: (α : Type*)
  axioms and operations (1):
    - exists_pair_ne : exists x y : α, x != y

中文:
类 Nontrivial
  参数: (α : 类型)
  公理与运算 (1 个):
    - exists_pair_ne : 存在 x y : α, x != y
-/
class Nontrivial (α : Type*) : Prop where
  /-- In a nontrivial type, there exists a pair of distinct terms. -/
  exists_pair_ne : exists x y : α, x != y

/--
theorem `nontrivial_iff` / 定理 `nontrivial_iff`

English:
theorem nontrivial_iff
  statement: Nontrivial α ↔ exists x y : α, x != y
  proof: ⟨fun h => h.exists_pair_ne, fun h => ⟨h⟩⟩

中文:
定理 nontrivial_iff
  结论: Nontrivial α ↔ 存在 x y : α, x != y
  证明: ⟨fun h => h.exists_pair_ne, fun h => ⟨h⟩⟩

Depends on / 依赖: exists_pair_ne, h.exists_pair_ne
-/
theorem nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y :=
  ⟨fun h => h.exists_pair_ne, fun h => ⟨h⟩⟩

/--
theorem `exists_pair_ne` / 定理 `exists_pair_ne`

English:
theorem exists_pair_ne
  given: (α : Type*) [Nontrivial α]
  statement: exists x y : α, x != y
  proof: Nontrivial.exists_pair_ne

中文:
定理 exists_pair_ne
  条件: (α : 类型) [Nontrivial α]
  结论: 存在 x y : α, x != y
  证明: Nontrivial.exists_pair_ne

Depends on / 依赖: Nontrivial, Nontrivial.exists_pair_ne, exists_pair_ne
-/
theorem exists_pair_ne (α : Type*) [Nontrivial α] : exists x y : α, x != y :=
  Nontrivial.exists_pair_ne

/--
theorem `Function.Injective.nontrivial` / 定理 `Function.Injective.nontrivial`

English:
theorem Function.Injective.nontrivial
  statement: [Nontrivial α] {f : α -> β}
  proof: let ⟨x, y, h⟩ := exists_pair_ne α
  ⟨⟨f x, f y, hf.ne h⟩⟩

中文:
定理 Function.Injective.nontrivial
  结论: [Nontrivial α] {f : α -> β}
  证明: let ⟨x, y, h⟩ := exists_pair_ne α
  ⟨⟨f x, f y, hf.ne h⟩⟩
-/
protected theorem Function.Injective.nontrivial [Nontrivial α] {f : α -> β}
    (hf : Function.Injective f) : Nontrivial β :=
  let ⟨x, y, h⟩ := exists_pair_ne α
  ⟨⟨f x, f y, hf.ne h⟩⟩

/--
theorem `Function.Injective.exists_ne` / 定理 `Function.Injective.exists_ne`

English:
theorem Function.Injective.exists_ne
  statement: [Nontrivial α] {f : α -> β}
  proof: by
  rcases exists_pair_ne α with ⟨x₁, x₂, hx⟩
  by_cases h : f x₂ = y
  · exact ⟨x₁, (hf.ne_iff' h).2 hx⟩
  · exact ⟨x₂, h⟩

中文:
定理 Function.Injective.exists_ne
  结论: [Nontrivial α] {f : α -> β}
  证明: by
  rcases exists_pair_ne α with ⟨x₁, x₂, hx⟩
  by_cases h : f x₂ = y
  · exact ⟨x₁, (hf.ne_iff' h).2 hx⟩
  · exact ⟨x₂, h⟩
-/
protected theorem Function.Injective.exists_ne [Nontrivial α] {f : α -> β}
    (hf : Function.Injective f) (y : β) : exists x, f x != y := by
  rcases exists_pair_ne α with ⟨x₁, x₂, hx⟩
  by_cases h : f x₂ = y
  · exact ⟨x₁, (hf.ne_iff' h).2 hx⟩
  · exact ⟨x₂, h⟩

-- See Note [decidable namespace]
/--
theorem `Decidable.exists_ne` / 定理 `Decidable.exists_ne`

English:
theorem Decidable.exists_ne
  given: [Nontrivial α] [DecidableEq α] (x : α)
  statement: exists y, y != x
  proof: by
  rcases exists_pair_ne α with ⟨y, y', h⟩
  by_cases hx : x = y
  · rw [← hx] at h
    exact ⟨y', h.symm⟩
  · exact ⟨y, Ne.symm hx⟩

中文:
定理 Decidable.exists_ne
  条件: [Nontrivial α] [DecidableEq α] (x : α)
  结论: 存在 y, y != x
  证明: by
  rcases exists_pair_ne α with ⟨y, y', h⟩
  by_cases hx : x = y
  · rw [← hx] at h
    exact ⟨y', h.symm⟩
  · exact ⟨y, Ne.symm hx⟩
-/
protected theorem Decidable.exists_ne [Nontrivial α] [DecidableEq α] (x : α) : exists y, y != x := by
  rcases exists_pair_ne α with ⟨y, y', h⟩
  by_cases hx : x = y
  · rw [← hx] at h
    exact ⟨y', h.symm⟩
  · exact ⟨y, Ne.symm hx⟩

/--
theorem `exists_ne` / 定理 `exists_ne`

English:
theorem exists_ne
  given: [Nontrivial α] (x : α)
  statement: exists y, y != x
  proof: by
  classical
  exact Decidable.exists_ne x

中文:
定理 exists_ne
  条件: [Nontrivial α] (x : α)
  结论: 存在 y, y != x
  证明: by
  classical
  exact Decidable.exists_ne x

Depends on / 依赖: Decidable, Decidable.exists_ne, classical, exists_ne
-/
theorem exists_ne [Nontrivial α] (x : α) : exists y, y != x := by
  classical
  exact Decidable.exists_ne x

-- `x` and `y` are explicit here, as they are often needed to guide typechecking of `h`.
/--
theorem `nontrivial_of_ne` / 定理 `nontrivial_of_ne`

English:
theorem nontrivial_of_ne
  given: (x y : α) (h : x != y)
  statement: Nontrivial α
  proof: ⟨⟨x, y, h⟩⟩

中文:
定理 nontrivial_of_ne
  条件: (x y : α) (h : x != y)
  结论: Nontrivial α
  证明: ⟨⟨x, y, h⟩⟩
-/
theorem nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α :=
  ⟨⟨x, y, h⟩⟩

/--
theorem `nontrivial_iff_exists_ne` / 定理 `nontrivial_iff_exists_ne`

English:
theorem nontrivial_iff_exists_ne
  given: (x : α)
  statement: Nontrivial α ↔ exists y, y != x
  proof: ⟨fun h => @exists_ne α h x, fun ⟨_, hy⟩ => nontrivial_of_ne _ _ hy⟩

中文:
定理 nontrivial_iff_exists_ne
  条件: (x : α)
  结论: Nontrivial α ↔ 存在 y, y != x
  证明: ⟨fun h => @exists_ne α h x, fun ⟨_, hy⟩ => nontrivial_of_ne _ _ hy⟩

Depends on / 依赖: exists_ne, nontrivial_of_ne
-/
theorem nontrivial_iff_exists_ne (x : α) : Nontrivial α ↔ exists y, y != x :=
  ⟨fun h => @exists_ne α h x, fun ⟨_, hy⟩ => nontrivial_of_ne _ _ hy⟩

/--
theorem `Function.nontrivial_of_nontrivial` / 定理 `Function.nontrivial_of_nontrivial`

English:
theorem Function.nontrivial_of_nontrivial
  given: (α β : Type*) [Nontrivial (α -> β)]
  proof: by
  obtain ⟨f, g, h⟩ := exists_pair_ne (α -> β)
  rw [ne_eq]; rw [funext_iff]; rw [Classical.not_forall] at h
  obtain ⟨a, h⟩ := h
  exact nontrivial_of_ne _ _ h

中文:
定理 Function.nontrivial_of_nontrivial
  条件: (α β : 类型) [Nontrivial (α -> β)]
  证明: by
  obtain ⟨f, g, h⟩ := exists_pair_ne (α -> β)
  rw [ne_eq]; rw [funext_iff]; rw [Classical.not_forall] at h
  obtain ⟨a, h⟩ := h
  exact nontrivial_of_ne _ _ h

Depends on / 依赖: Classical, Classical.not_forall, exists_pair_ne, funext_iff, ne_eq, nontrivial_of_ne, not_forall
-/
theorem Function.nontrivial_of_nontrivial (α β : Type*) [Nontrivial (α -> β)] :
    Nontrivial β := by
  obtain ⟨f, g, h⟩ := exists_pair_ne (α -> β)
  rw [ne_eq]; rw [funext_iff]; rw [Classical.not_forall] at h
  obtain ⟨a, h⟩ := h
  exact nontrivial_of_ne _ _ h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial Prop
  body: ⟨⟨True, False, true_ne_false⟩⟩

中文:
实例 :
  签名: Nontrivial 命题
  定义体: ⟨⟨True, False, true_ne_false⟩⟩

Depends on / 依赖: true_ne_false
-/
instance : Nontrivial Prop :=
  ⟨⟨True, False, true_ne_false⟩⟩

/-- See Note [lower instance priority]

Note that since this and `instNonemptyOfInhabited` are the most "obvious" way to find a nonempty
instance if no direct instance can be found, we give this a higher priority than the usual `100`.
-/
instance (priority := 500) Nontrivial.to_nonempty [Nontrivial α] : Nonempty α :=
  let ⟨x, _⟩ := _root_.exists_pair_ne α
  ⟨x⟩

/--
theorem `subsingleton_iff` / 定理 `subsingleton_iff`

English:
theorem subsingleton_iff
  statement: Subsingleton α ↔ forall x y : α, x = y
  proof: ⟨by
    intro h
    exact Subsingleton.elim, fun h => ⟨h⟩⟩

@[push]

中文:
定理 subsingleton_iff
  结论: Subsingleton α ↔ 对任意 x y : α, x = y
  证明: ⟨by
    intro h
    exact Subsingleton.elim, fun h => ⟨h⟩⟩

@[push]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem subsingleton_iff : Subsingleton α ↔ forall x y : α, x = y :=
  ⟨by
    intro h
    exact Subsingleton.elim, fun h => ⟨h⟩⟩

@[push]
/--
theorem `not_nontrivial_iff_subsingleton` / 定理 `not_nontrivial_iff_subsingleton`

English:
theorem not_nontrivial_iff_subsingleton
  statement: ¬Nontrivial α ↔ Subsingleton α
  proof: by
  simp only [nontrivial_iff, subsingleton_iff, not_exists, Classical.not_not]

中文:
定理 not_nontrivial_iff_subsingleton
  结论: ¬Nontrivial α ↔ Subsingleton α
  证明: by
  simp only [nontrivial_iff, subsingleton_iff, not_exists, Classical.not_not]

Depends on / 依赖: Classical, Classical.not_not, nontrivial_iff, not_exists, not_not, subsingleton_iff
-/
theorem not_nontrivial_iff_subsingleton : ¬Nontrivial α ↔ Subsingleton α := by
  simp only [nontrivial_iff, subsingleton_iff, not_exists, Classical.not_not]

/--
theorem `not_nontrivial` / 定理 `not_nontrivial`

English:
theorem not_nontrivial
  given: (α) [Subsingleton α]
  statement: ¬Nontrivial α
  proof: fun ⟨⟨x, y, h⟩⟩ => h Subsingleton.elim x y

中文:
定理 not_nontrivial
  条件: (α) [Subsingleton α]
  结论: ¬Nontrivial α
  证明: fun ⟨⟨x, y, h⟩⟩ => h Subsingleton.elim x y

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem not_nontrivial (α) [Subsingleton α] : ¬Nontrivial α :=
fun ⟨⟨x, y, h⟩⟩ => h Subsingleton.elim x y

/--
theorem `not_subsingleton` / 定理 `not_subsingleton`

English:
theorem not_subsingleton
  given: (α) [Nontrivial α]
  statement: ¬Subsingleton α
  proof: fun _ => not_nontrivial _ ‹_›

@[push]

中文:
定理 not_subsingleton
  条件: (α) [Nontrivial α]
  结论: ¬Subsingleton α
  证明: fun _ => not_nontrivial _ ‹_›

@[push]

Depends on / 依赖: not_nontrivial
-/
theorem not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α :=
  fun _ => not_nontrivial _ ‹_›

@[push]
/--
lemma `not_subsingleton_iff_nontrivial` / 引理 `not_subsingleton_iff_nontrivial`

English:
lemma not_subsingleton_iff_nontrivial
  statement: ¬Subsingleton α ↔ Nontrivial α
  proof: by
  rw [← not_nontrivial_iff_subsingleton]; rw [Classical.not_not]

中文:
引理 not_subsingleton_iff_nontrivial
  结论: ¬Subsingleton α ↔ Nontrivial α
  证明: by
  rw [← not_nontrivial_iff_subsingleton]; rw [Classical.not_not]

Depends on / 依赖: Classical, Classical.not_not, not_nontrivial_iff_subsingleton, not_not
-/
lemma not_subsingleton_iff_nontrivial : ¬Subsingleton α ↔ Nontrivial α := by
  rw [← not_nontrivial_iff_subsingleton]; rw [Classical.not_not]

/--
theorem `subsingleton_or_nontrivial` / 定理 `subsingleton_or_nontrivial`

English:
theorem subsingleton_or_nontrivial
  given: (α : Type*)
  statement: Subsingleton α ∨ Nontrivial α
  proof: by
  rw [← not_nontrivial_iff_subsingleton]; rw [or_comm]
  exact Classical.em _

中文:
定理 subsingleton_or_nontrivial
  条件: (α : 类型)
  结论: Subsingleton α ∨ Nontrivial α
  证明: by
  rw [← not_nontrivial_iff_subsingleton]; rw [or_comm]
  exact Classical.em _

Depends on / 依赖: Classical, Classical.em, not_nontrivial_iff_subsingleton, or_comm
-/
theorem subsingleton_or_nontrivial (α : Type*) : Subsingleton α ∨ Nontrivial α := by
  rw [← not_nontrivial_iff_subsingleton]; rw [or_comm]
  exact Classical.em _

/--
theorem `false_of_nontrivial_of_subsingleton` / 定理 `false_of_nontrivial_of_subsingleton`

English:
theorem false_of_nontrivial_of_subsingleton
  given: (α : Type*) [Nontrivial α] [Subsingleton α]
  statement: False
  proof: not_nontrivial _ ‹_›

中文:
定理 false_of_nontrivial_of_subsingleton
  条件: (α : 类型) [Nontrivial α] [Subsingleton α]
  结论: False
  证明: not_nontrivial _ ‹_›

Depends on / 依赖: not_nontrivial
-/
theorem false_of_nontrivial_of_subsingleton (α : Type*) [Nontrivial α] [Subsingleton α] : False :=
  not_nontrivial _ ‹_›

/--
theorem `Function.Surjective.nontrivial` / 定理 `Function.Surjective.nontrivial`

English:
theorem Function.Surjective.nontrivial
  statement: [Nontrivial β] {f : α -> β}
  proof: by
  rcases exists_pair_ne β with ⟨x, y, h⟩
  rcases hf x with ⟨x', hx'⟩
  rcases hf y with ⟨y', hy'⟩
  have : x' != y' := by
    refine fun H => h ?_
    rw [← hx']; rw [← hy']; rw [H]
  exact ⟨⟨x', y', this⟩⟩

中文:
定理 Function.Surjective.nontrivial
  结论: [Nontrivial β] {f : α -> β}
  证明: by
  rcases exists_pair_ne β with ⟨x, y, h⟩
  rcases hf x with ⟨x', hx'⟩
  rcases hf y with ⟨y', hy'⟩
  have : x' != y' := by
    refine fun H => h ?_
    rw [← hx']; rw [← hy']; rw [H]
  exact ⟨⟨x', y', this⟩⟩
-/
protected theorem Function.Surjective.nontrivial [Nontrivial β] {f : α -> β}
    (hf : Function.Surjective f) : Nontrivial α := by
  rcases exists_pair_ne β with ⟨x, y, h⟩
  rcases hf x with ⟨x', hx'⟩
  rcases hf y with ⟨y', hy'⟩
  have : x' != y' := by
    refine fun H => h ?_
    rw [← hx']; rw [← hy']; rw [H]
  exact ⟨⟨x', y', this⟩⟩

namespace Bool

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial Bool
  body: ⟨⟨true, false, nofun⟩⟩

中文:
实例 :
  签名: Nontrivial 布尔
  定义体: ⟨⟨true, false, nofun⟩⟩
-/
instance : Nontrivial Bool :=
  ⟨⟨true, false, nofun⟩⟩

end Bool

/--
theorem `NeZero.nontrivial` / 定理 `NeZero.nontrivial`

English:
theorem NeZero.nontrivial
  given: {α : Type*} [Zero α] (a : α) [NeZero a]
  statement: Nontrivial α
  proof: ⟨⟨a, 0, NeZero.ne a⟩⟩

中文:
定理 NeZero.nontrivial
  条件: {α : 类型} [Zero α] (a : α) [NeZero a]
  结论: Nontrivial α
  证明: ⟨⟨a, 0, NeZero.ne a⟩⟩

Depends on / 依赖: NeZero, NeZero.ne
-/
theorem NeZero.nontrivial {α : Type*} [Zero α] (a : α) [NeZero a] : Nontrivial α :=
  ⟨⟨a, 0, NeZero.ne a⟩⟩
