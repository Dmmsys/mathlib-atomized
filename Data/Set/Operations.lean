/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Kim Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/
module

public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.SProd
public import Mathlib.Data.Subtype
public import Mathlib.Order.Notation
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.Push.Attr

import Mathlib.Tactic.Attr.Register
import Aesop.BuiltinRules
import Aesop.Frontend.Tactic
import Aesop.Main

/-!
# Basic definitions about sets

In this file we define various operations on sets.
We also provide basic lemmas needed to unfold the definitions.
More advanced theorems about these definitions are located in other files in `Mathlib/Data/Set`.

## Main definitions

- complement of a set and set difference;
- `Set.preimage f s`, a.k.a. `f ⁻¹' s`: preimage of a set;
- `Set.range f`: the range of a function;
  it is more general than `f '' univ` because it allows functions from `Sort*`;
- `s ×ˢ t`: product of `s : Set α` and `t : Set β` as a set in `α × β`;
- `Set.diagonal`: the diagonal in `α × α`;
- `Set.offDiag s`: the part of `s ×ˢ s` that is off the diagonal;
- `Set.pi`: indexed product of a family of sets `∀ i, Set (α i)`,
  as a set in `∀ i, α i`;
- `Set.EqOn f g s`: the predicate saying that two functions are equal on a set;
- `Set.MapsTo f s t`: the predicate saying that `f` sends all points of `s` to `t`;
- `Set.MapsTo.restrict`: restrict `f : α → β` to `f' : s → t` provided that `Set.MapsTo f s t`;
- `Set.restrictPreimage`: restrict `f : α → β` to `f' : (f ⁻¹' t) → t`;
- `Set.InjOn`: the predicate saying that `f` is injective on a set;
- `Set.SurjOn f s t`: the predicate saying that `t ⊆ f '' s`;
- `Set.BijOn f s t`: the predicate saying that `f` is injective on `s` and `f '' s = t`;
- `Set.graphOn`: the graph of a function on a set;
- `Set.LeftInvOn`, `Set.RightInvOn`, `Set.InvOn`:
  the predicates saying that `f'` is a left, right or two-sided inverse of `f` on `s`, `t`, or both;
- `Set.image2`: the image of a pair of sets under a binary operation,
  mostly useful to define pointwise algebraic operations on sets;
- `Set.seq`: monadic `seq` operation on sets;
  we don't use monadic notation to ensure support for maps between different universes.

## Notation

- `f '' s`: image of a set;
- `f ⁻¹' s`: preimage of a set;
- `s ×ˢ t`: the product of sets;
- `s ∪ t`: the union of two sets;
- `s ∩ t`: the intersection of two sets;
- `sᶜ`: the complement of a set;
- `s \ t`: the difference of two sets.

## Keywords

set, image, preimage
-/

@[expose] public section

universe u v w

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ### Lemmas about `mem` and `Set.ofPred` -/

@[simp, mfld_simps, push]
/--
theorem `mem_ofPred_eq` / 定理 `mem_ofPred_eq`

English:
theorem mem_ofPred_eq
  given: {x : α} {p : α -> Prop}
  statement: (x in {y | p y}) = p x
  proof: rfl

@[deprecated (since := "2026-07-09")] alias mem_setOf_eq := mem_ofPred_eq

grind_pattern mem_ofPred_eq => x in Set.ofPred p

中文:
定理 mem_ofPred_eq
  条件: {x : α} {p : α -> 命题}
  结论: (x in {y | p y}) = p x
  证明: rfl

@[deprecated (since := "2026-07-09")] alias mem_setOf_eq := mem_ofPred_eq

grind_pattern mem_ofPred_eq => x in Set.ofPred p
-/
theorem mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p y}) = p x := rfl

@[deprecated (since := "2026-07-09")] alias mem_setOf_eq := mem_ofPred_eq

grind_pattern mem_ofPred_eq => x in Set.ofPred p

/--
theorem `eq_mem_ofPred` / 定理 `eq_mem_ofPred`

English:
theorem eq_mem_ofPred
  given: (p : α -> Prop)
  statement: p = (· in {a | p a})
  proof: rfl

@[deprecated (since := "2026-07-09")] alias eq_mem_setOf := eq_mem_ofPred

中文:
定理 eq_mem_ofPred
  条件: (p : α -> 命题)
  结论: p = (· in {a | p a})
  证明: rfl

@[deprecated (since := "2026-07-09")] alias eq_mem_setOf := eq_mem_ofPred
-/
theorem eq_mem_ofPred (p : α -> Prop) : p = (· in {a | p a}) := rfl

@[deprecated (since := "2026-07-09")] alias eq_mem_setOf := eq_mem_ofPred

/--
theorem `mem_ofPred` / 定理 `mem_ofPred`

English:
theorem mem_ofPred
  given: {a : α} {p : α -> Prop}
  statement: a in { x | p x } ↔ p a
  proof: Iff.rfl

@[deprecated (since := "2026-07-09")] alias mem_setOf := mem_ofPred

中文:
定理 mem_ofPred
  条件: {a : α} {p : α -> 命题}
  结论: a in { x | p x } ↔ p a
  证明: Iff.rfl

@[deprecated (since := "2026-07-09")] alias mem_setOf := mem_ofPred

Depends on / 依赖: Iff.rfl
-/
theorem mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ p a := Iff.rfl

@[deprecated (since := "2026-07-09")] alias mem_setOf := mem_ofPred

/-- If `h : a ∈ {x | p x}` then `h.out : p x`. These are definitionally equal, but this can
nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
argument to `simp`. -/
alias ⟨_root_.Membership.mem.out, _⟩ := mem_ofPred

/--
theorem `notMem_ofPred_iff` / 定理 `notMem_ofPred_iff`

English:
theorem notMem_ofPred_iff
  given: {a : α} {p : α -> Prop}
  statement: a ∉ { x | p x } ↔ ¬p a
  proof: Iff.rfl

@[deprecated (since := "2026-07-09")] alias notMem_setOf_iff := notMem_ofPred_iff

中文:
定理 notMem_ofPred_iff
  条件: {a : α} {p : α -> 命题}
  结论: a ∉ { x | p x } ↔ ¬p a
  证明: Iff.rfl

@[deprecated (since := "2026-07-09")] alias notMem_setOf_iff := notMem_ofPred_iff

Depends on / 依赖: Iff.rfl
-/
theorem notMem_ofPred_iff {a : α} {p : α -> Prop} : a ∉ { x | p x } ↔ ¬p a := Iff.rfl

@[deprecated (since := "2026-07-09")] alias notMem_setOf_iff := notMem_ofPred_iff

/--
theorem `ofPred_mem_eq` / 定理 `ofPred_mem_eq`

English:
theorem ofPred_mem_eq
  given: {s : Set α}
  statement: { x | x in s } = s
  proof: rfl

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq := ofPred_mem_eq

@[simp, mfld_simps, grind ←, push]

中文:
定理 ofPred_mem_eq
  条件: {s : 集合 α}
  结论: { x | x in s } = s
  证明: rfl

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq := ofPred_mem_eq

@[simp, mfld_simps, grind ←, push]
-/
@[simp] theorem ofPred_mem_eq {s : Set α} : { x | x in s } = s := rfl

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq := ofPred_mem_eq

@[simp, mfld_simps, grind ←, push]
/--
theorem `mem_univ` / 定理 `mem_univ`

English:
theorem mem_univ
  given: (x : α)
  statement: x in @univ α
  proof: trivial

中文:
定理 mem_univ
  条件: (x : α)
  结论: x in @univ α
  证明: trivial
-/
theorem mem_univ (x : α) : x in @univ α := trivial


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Compl (Set α)
  body: ⟨fun s => {x | x ∉ s}⟩

@[simp, grind =, push]

中文:
实例 :
  签名: 补集 (集合 α)
  定义体: ⟨fun s => {x | x ∉ s}⟩

@[simp, grind =, push]
-/
instance : Compl (Set α) := ⟨fun s => {x | x ∉ s}⟩

@[simp, grind =, push]
/--
theorem `mem_compl_iff` / 定理 `mem_compl_iff`

English:
theorem mem_compl_iff
  given: (s : Set α) (x : α)
  statement: x in sᶜ ↔ x ∉ s
  proof: Iff.rfl

中文:
定理 mem_compl_iff
  条件: (s : 集合 α) (x : α)
  结论: x in sᶜ ↔ x ∉ s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s := Iff.rfl

/--
theorem `sdiff_eq` / 定理 `sdiff_eq`

English:
theorem sdiff_eq
  given: (s t : Set α)
  statement: s \ t = s inter tᶜ
  proof: rfl

@[deprecated (since := "2026-06-03")] alias diff_eq := sdiff_eq

@[simp, grind =, push]

中文:
定理 sdiff_eq
  条件: (s t : 集合 α)
  结论: s \ t = s inter tᶜ
  证明: rfl

@[deprecated (since := "2026-06-03")] alias diff_eq := sdiff_eq

@[simp, grind =, push]
-/
theorem sdiff_eq (s t : Set α) : s \ t = s inter tᶜ := rfl

@[deprecated (since := "2026-06-03")] alias diff_eq := sdiff_eq

@[simp, grind =, push]
/--
theorem `mem_sdiff` / 定理 `mem_sdiff`

English:
theorem mem_sdiff
  given: {s t : Set α} (x : α)
  statement: x in s \ t ↔ x in s ∧ x ∉ t
  proof: Iff.rfl

@[deprecated (since := "2026-06-03")] alias mem_diff := mem_sdiff

中文:
定理 mem_sdiff
  条件: {s t : 集合 α} (x : α)
  结论: x in s \ t ↔ x in s ∧ x ∉ t
  证明: Iff.rfl

@[deprecated (since := "2026-06-03")] alias mem_diff := mem_sdiff

Depends on / 依赖: Iff.rfl
-/
theorem mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x ∉ t := Iff.rfl

@[deprecated (since := "2026-06-03")] alias mem_diff := mem_sdiff

/--
theorem `mem_sdiff_of_mem` / 定理 `mem_sdiff_of_mem`

English:
theorem mem_sdiff_of_mem
  given: {s t : Set α} {x : α} (h1 : x in s) (h2 : x ∉ t)
  statement: x in s \ t
  proof: ⟨h1, h2⟩

@[deprecated (since := "2026-06-03")] alias mem_diff_of_mem := mem_sdiff_of_mem

中文:
定理 mem_sdiff_of_mem
  条件: {s t : 集合 α} {x : α} (h1 : x in s) (h2 : x ∉ t)
  结论: x in s \ t
  证明: ⟨h1, h2⟩

@[deprecated (since := "2026-06-03")] alias mem_diff_of_mem := mem_sdiff_of_mem

Depends on / 依赖: infer_instance, invApp
-/
theorem mem_sdiff_of_mem {s t : Set α} {x : α} (h1 : x in s) (h2 : x ∉ t) : x in s \ t := ⟨h1, h2⟩

@[deprecated (since := "2026-06-03")] alias mem_diff_of_mem := mem_sdiff_of_mem

/-- The preimage of `s : Set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
@[implicit_reducible]
/--
Definition of `preimage` / `preimage` 的定义

English:
definition preimage
  signature: (f : α -> β) (s : Set β)
  body: {x | f x in s}

中文:
定义 原像
  签名: (f : α -> β) (s : 集合 β)
  定义体: {x | f x in s}
-/
def preimage (f : α -> β) (s : Set β) : Set α := {x | f x in s}

/-- `f ⁻¹' t` denotes the preimage of `t : Set β` under the function `f : α → β`. -/
infixr:80 " ⁻¹' " => preimage

@[simp, mfld_simps, grind =, push]
/--
theorem `mem_preimage` / 定理 `mem_preimage`

English:
theorem mem_preimage
  given: {f : α -> β} {s : Set β} {a : α}
  statement: a in f ⁻¹' s ↔ f a in s
  proof: Iff.rfl

中文:
定理 mem_preimage
  条件: {f : α -> β} {s : 集合 β} {a : α}
  结论: a in f ⁻¹' s ↔ f a in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f ⁻¹' s ↔ f a in s := Iff.rfl

/-- `f '' s` denotes the image of `s : Set α` under the function `f : α → β`. -/
infixr:80 " '' " => image

@[simp, grind =, push]
/--
theorem `mem_image` / 定理 `mem_image`

English:
theorem mem_image
  given: (f : α -> β) (s : Set α) (y : β)
  statement: y in f '' s ↔ exists x in s, f x = y
  proof: Iff.rfl

@[mfld_simps]

中文:
定理 mem_image
  条件: (f : α -> β) (s : 集合 α) (y : β)
  结论: y in f '' s ↔ 存在 x in s, f x = y
  证明: Iff.rfl

@[mfld_simps]

Depends on / 依赖: Iff.rfl
-/
theorem mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s ↔ exists x in s, f x = y :=
  Iff.rfl

@[mfld_simps]
/--
theorem `mem_image_of_mem` / 定理 `mem_image_of_mem`

English:
theorem mem_image_of_mem
  given: (f : α -> β) {x : α} {a : Set α} (h : x in a)
  statement: f x in f '' a
  proof: ⟨_, h, rfl⟩

中文:
定理 mem_image_of_mem
  条件: (f : α -> β) {x : α} {a : 集合 α} (h : x in a)
  结论: f x in f '' a
  证明: ⟨_, h, rfl⟩
-/
theorem mem_image_of_mem (f : α -> β) {x : α} {a : Set α} (h : x in a) : f x in f '' a :=
  ⟨_, h, rfl⟩

/--
Definition of `imageFactorization` / `imageFactorization` 的定义

English:
definition imageFactorization
  signature: (f : α -> β) (s : Set α)
  body: fun p =>
  ⟨f p.1, mem_image_of_mem f p.2⟩

中文:
定义 imageFactorization
  签名: (f : α -> β) (s : 集合 α)
  定义体: fun p =>
  ⟨f p.1, mem_image_of_mem f p.2⟩
-/
def imageFactorization (f : α -> β) (s : Set α) : s -> f '' s := fun p =>
  ⟨f p.1, mem_image_of_mem f p.2⟩

/--
Definition of `kernImage` / `kernImage` 的定义

English:
definition kernImage
  signature: (f : α -> β) (s : Set α)
  body: {y | forall ⦃x⦄, f x = y -> x in s}

中文:
定义 kernImage
  签名: (f : α -> β) (s : 集合 α)
  定义体: {y | forall ⦃x⦄, f x = y -> x in s}
-/
def kernImage (f : α -> β) (s : Set α) : Set β := {y | forall ⦃x⦄, f x = y -> x in s}

/--
lemma `subset_kernImage_iff` / 引理 `subset_kernImage_iff`

English:
lemma subset_kernImage_iff
  given: {s : Set β} {t : Set α} {f : α -> β}
  statement: s subseteq kernImage f t ↔ f ⁻¹' s subseteq t
  proof: ⟨fun h _ hx => h hx rfl,
    fun h _ hx y hy => h (show f y in s from hy.symm ▸ hx)⟩

中文:
引理 subset_kernImage_iff
  条件: {s : 集合 β} {t : 集合 α} {f : α -> β}
  结论: s subseteq kernImage f t ↔ f ⁻¹' s subseteq t
  证明: ⟨fun h _ hx => h hx rfl,
    fun h _ hx y hy => h (show f y in s from hy.symm ▸ hx)⟩

Depends on / 依赖: hy.symm
-/
lemma subset_kernImage_iff {s : Set β} {t : Set α} {f : α -> β} : s subseteq kernImage f t ↔ f ⁻¹' s subseteq t :=
  ⟨fun h _ hx => h hx rfl,
    fun h _ hx y hy => h (show f y in s from hy.symm ▸ hx)⟩

section Range

variable {ι : Sort*} {f : ι -> α}

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (f : ι -> α)
  body: {x | exists y, f y = x}

中文:
定义 range
  签名: (f : ι -> α)
  定义体: {x | exists y, f y = x}
-/
def range (f : ι -> α) : Set α := {x | exists y, f y = x}

/--
theorem `mem_range` / 定理 `mem_range`

English:
theorem mem_range
  given: {x : α}
  statement: x in range f ↔ exists y, f y = x
  proof: Iff.rfl

中文:
定理 mem_range
  条件: {x : α}
  结论: x in range f ↔ 存在 y, f y = x
  证明: Iff.rfl
-/
@[simp, grind =, push] theorem mem_range {x : α} : x in range f ↔ exists y, f y = x := Iff.rfl

/--
theorem `mem_range_self` / 定理 `mem_range_self`

English:
theorem mem_range_self
  given: (i : ι)
  statement: f i in range f
  proof: ⟨i, rfl⟩

中文:
定理 mem_range_self
  条件: (i : ι)
  结论: f i in range f
  证明: ⟨i, rfl⟩
-/
@[mfld_simps] theorem mem_range_self (i : ι) : f i in range f := ⟨i, rfl⟩

/--
Definition of `rangeFactorization` / `rangeFactorization` 的定义

English:
definition rangeFactorization
  signature: (f : ι -> α)
  body: fun i => ⟨f i, mem_range_self i⟩

中文:
定义 rangeFactorization
  签名: (f : ι -> α)
  定义体: fun i => ⟨f i, mem_range_self i⟩

Depends on / 依赖: mem_range_self
-/
def rangeFactorization (f : ι -> α) : ι -> range f := fun i => ⟨f i, mem_range_self i⟩

/--
lemma `rangeFactorization_injective` / 引理 `rangeFactorization_injective`

English:
lemma rangeFactorization_injective
  proof: by
  simp [Function.Injective, rangeFactorization]

中文:
引理 rangeFactorization_injective
  证明: by
  simp [Function.Injective, rangeFactorization]
-/
@[simp] lemma rangeFactorization_injective :
    (Set.rangeFactorization f).Injective ↔ f.Injective := by
  simp [Function.Injective, rangeFactorization]

/--
lemma `rangeFactorization_surjective` / 引理 `rangeFactorization_surjective`

English:
lemma rangeFactorization_surjective
  statement: (rangeFactorization f).Surjective
  proof: fun ⟨_, i, rfl⟩ => ⟨i, rfl⟩

中文:
引理 rangeFactorization_surjective
  结论: (rangeFactorization f).满射
  证明: fun ⟨_, i, rfl⟩ => ⟨i, rfl⟩

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.ofRestrict, X.toPresheafedSpace, ofRestrict, toPresheafedSpace
-/
@[simp] lemma rangeFactorization_surjective : (rangeFactorization f).Surjective :=
  fun ⟨_, i, rfl⟩ => ⟨i, rfl⟩

/--
lemma `rangeFactorization_bijective` / 引理 `rangeFactorization_bijective`

English:
lemma rangeFactorization_bijective
  proof: by simp [Function.Bijective]

中文:
引理 rangeFactorization_bijective
  证明: by simp [Function.Bijective]

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion, infer_instance, of_isIso
-/
@[simp] lemma rangeFactorization_bijective :
    (Set.rangeFactorization f).Bijective ↔ f.Injective := by simp [Function.Bijective]

/--
lemma `rangeFactorization_eq_rangeFactorization_iff` / 引理 `rangeFactorization_eq_rangeFactorization_iff`

English:
lemma rangeFactorization_eq_rangeFactorization_iff
  statement: {ι : Sort*} {α : Type*} {f : ι -> α}
  proof: by
  simp [Set.rangeFactorization]

中文:
引理 rangeFactorization_eq_rangeFactorization_iff
  结论: {ι : 类型层*} {α : 类型} {f : ι -> α}
  证明: by
  simp [Set.rangeFactorization]
-/
@[simp] lemma rangeFactorization_eq_rangeFactorization_iff {ι : Sort*} {α : Type*} {f : ι -> α}
    (a b : ι) : Set.rangeFactorization f a = Set.rangeFactorization f b ↔ f a = f b := by
  simp [Set.rangeFactorization]

/--
lemma `rangeFactorization_eq_iff` / 引理 `rangeFactorization_eq_iff`

English:
lemma rangeFactorization_eq_iff
  given: {ι : Sort*} {α : Type*} {f : ι -> α} (a : ι) (b : Set.range f)
  proof: by
  rw [Set.rangeFactorization]; rw [← b.coe_eta b.2]; rw [Subtype.ext_iff]

中文:
引理 rangeFactorization_eq_iff
  条件: {ι : 类型层*} {α : 类型} {f : ι -> α} (a : ι) (b : 集合.range f)
  证明: by
  rw [Set.rangeFactorization]; rw [← b.coe_eta b.2]; rw [Subtype.ext_iff]

Depends on / 依赖: Set.rangeFactorization, Subtype, Subtype.ext_iff, b.coe_eta, coe_eta, ext_iff, rangeFactorization
-/
lemma rangeFactorization_eq_iff {ι : Sort*} {α : Type*} {f : ι -> α} (a : ι) (b : Set.range f) :
    Set.rangeFactorization f a = b ↔ f a = b := by
  rw [Set.rangeFactorization]; rw [← b.coe_eta b.2]; rw [Subtype.ext_iff]

end Range

/--
Definition of `rangeSplitting` / `rangeSplitting` 的定义

English:
definition rangeSplitting
  signature: (f : α -> β)
  body: fun x => x.2.choose

中文:
定义 rangeSplitting
  签名: (f : α -> β)
  定义体: fun x => x.2.choose
-/
noncomputable def rangeSplitting (f : α -> β) : range f -> α := fun x => x.2.choose

-- This cannot be a `@[simp]` lemma because the head of the left-hand side is a variable.
/--
theorem `apply_rangeSplitting` / 定理 `apply_rangeSplitting`

English:
theorem apply_rangeSplitting
  given: (f : α -> β) (x : range f)
  statement: f (rangeSplitting f x) = x
  proof: x.2.choose_spec

@[simp]

中文:
定理 apply_rangeSplitting
  条件: (f : α -> β) (x : range f)
  结论: f (rangeSplitting f x) = x
  证明: x.2.choose_spec

@[simp]

Depends on / 依赖: choose_spec
-/
theorem apply_rangeSplitting (f : α -> β) (x : range f) : f (rangeSplitting f x) = x :=
  x.2.choose_spec

@[simp]
/--
theorem `comp_rangeSplitting` / 定理 `comp_rangeSplitting`

English:
theorem comp_rangeSplitting
  given: (f : α -> β)
  statement: f ∘ rangeSplitting f = Subtype.val
  proof: by
  ext
  simp only [Function.comp_apply]
  apply apply_rangeSplitting

中文:
定理 comp_rangeSplitting
  条件: (f : α -> β)
  结论: f ∘ rangeSplitting f = 子类型.val
  证明: by
  ext
  simp only [Function.comp_apply]
  apply apply_rangeSplitting

Depends on / 依赖: Function, Function.comp_apply, apply_rangeSplitting, comp_apply
-/
theorem comp_rangeSplitting (f : α -> β) : f ∘ rangeSplitting f = Subtype.val := by
  ext
  simp only [Function.comp_apply]
  apply apply_rangeSplitting

/--
lemma `Subtype.range_coind` / 引理 `Subtype.range_coind`

English:
lemma Subtype.range_coind
  given: (f : α -> β) {p : β -> Prop} (h : forall (a : α), p (f a))
  proof: by
  simp [Set.ext_iff, Subtype.ext_iff]

中文:
引理 子类型.range_coind
  条件: (f : α -> β) {p : β -> 命题} (h : 对任意 (a : α), p (f a))
  证明: by
  simp [Set.ext_iff, Subtype.ext_iff]

Depends on / 依赖: Set.ext_iff, Subtype, Subtype.ext_iff, ext_iff
-/
lemma Subtype.range_coind (f : α -> β) {p : β -> Prop} (h : forall (a : α), p (f a)) :
    range (Subtype.coind f h) = Subtype.val ⁻¹' range f := by
  simp [Set.ext_iff, Subtype.ext_iff]

section Prod

/--
theorem `prodMk_mem_set_prod_eq` / 定理 `prodMk_mem_set_prod_eq`

English:
theorem prodMk_mem_set_prod_eq
  statement: ((a, b) in s ×ˢ t) = (a in s ∧ b in t)
  proof: rfl

中文:
定理 prodMk_mem_set_prod_eq
  结论: ((a, b) in s ×ˢ t) = (a in s ∧ b in t)
  证明: rfl
-/
theorem prodMk_mem_set_prod_eq : ((a, b) in s ×ˢ t) = (a in s ∧ b in t) :=
  rfl

/--
theorem `mk_mem_prod` / 定理 `mk_mem_prod`

English:
theorem mk_mem_prod
  given: (ha : a in s) (hb : b in t)
  statement: (a, b) in s ×ˢ t
  proof: ⟨ha, hb⟩

中文:
定理 mk_mem_prod
  条件: (ha : a in s) (hb : b in t)
  结论: (a, b) in s ×ˢ t
  证明: ⟨ha, hb⟩
-/
theorem mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×ˢ t := ⟨ha, hb⟩

/--
theorem `prod_image_left` / 定理 `prod_image_left`

English:
theorem prod_image_left
  given: (f : α -> γ) (s : Set α) (t : Set β)
  proof: by
  aesop

中文:
定理 prod_image_left
  条件: (f : α -> γ) (s : 集合 α) (t : 集合 β)
  证明: by
  aesop
-/
theorem prod_image_left (f : α -> γ) (s : Set α) (t : Set β) :
    (f '' s) ×ˢ t = (fun x => (f x.1, x.2)) '' s ×ˢ t := by
  aesop

/--
theorem `prod_image_right` / 定理 `prod_image_right`

English:
theorem prod_image_right
  given: (f : α -> γ) (s : Set α) (t : Set β)
  proof: by
  aesop

中文:
定理 prod_image_right
  条件: (f : α -> γ) (s : 集合 α) (t : 集合 β)
  证明: by
  aesop
-/
theorem prod_image_right (f : α -> γ) (s : Set α) (t : Set β) :
    t ×ˢ (f '' s) = (fun x => (x.1, f x.2)) '' t ×ˢ s := by
  aesop

end Prod

section Diagonal

/--
Definition of `diagonal` / `diagonal` 的定义

English:
definition diagonal
  signature: (α : Type*)
  body: {p | p.1 = p.2}

中文:
定义 diagonal
  签名: (α : 类型)
  定义体: {p | p.1 = p.2}
-/
def diagonal (α : Type*) : Set (α × α) := {p | p.1 = p.2}

/--
theorem `mem_diagonal` / 定理 `mem_diagonal`

English:
theorem mem_diagonal
  given: (x : α)
  statement: (x, x) in diagonal α
  proof: rfl

中文:
定理 mem_diagonal
  条件: (x : α)
  结论: (x, x) in diagonal α
  证明: rfl
-/
theorem mem_diagonal (x : α) : (x, x) in diagonal α := rfl

/--
theorem `mem_diagonal_iff` / 定理 `mem_diagonal_iff`

English:
theorem mem_diagonal_iff
  given: {x : α × α}
  statement: x in diagonal α ↔ x.1 = x.2
  proof: .rfl

中文:
定理 mem_diagonal_iff
  条件: {x : α × α}
  结论: x in diagonal α ↔ x.1 = x.2
  证明: .rfl
-/
@[simp, grind =, push] theorem mem_diagonal_iff {x : α × α} : x in diagonal α ↔ x.1 = x.2 := .rfl

/--
Definition of `offDiag` / `offDiag` 的定义

English:
definition offDiag
  signature: (s : Set α)
  body: {x | x.1 in s ∧ x.2 in s ∧ x.1 != x.2}

@[simp, grind =, push]

中文:
定义 offDiag
  签名: (s : 集合 α)
  定义体: {x | x.1 in s ∧ x.2 in s ∧ x.1 != x.2}

@[simp, grind =, push]
-/
def offDiag (s : Set α) : Set (α × α) := {x | x.1 in s ∧ x.2 in s ∧ x.1 != x.2}

@[simp, grind =, push]
/--
theorem `mem_offDiag` / 定理 `mem_offDiag`

English:
theorem mem_offDiag
  given: {x : α × α} {s : Set α}
  statement: x in s.offDiag ↔ x.1 in s ∧ x.2 in s ∧ x.1 != x.2
  proof: Iff.rfl

中文:
定理 mem_offDiag
  条件: {x : α × α} {s : 集合 α}
  结论: x in s.offDiag ↔ x.1 in s ∧ x.2 in s ∧ x.1 != x.2
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_offDiag {x : α × α} {s : Set α} : x in s.offDiag ↔ x.1 in s ∧ x.2 in s ∧ x.1 != x.2 :=
  Iff.rfl

end Diagonal

section Pi

variable {ι : Type*} {α : ι -> Type*}

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (s : Set ι) (t : forall i, Set (α i))
  body: {f | forall i in s, f i in t i}

中文:
定义 pi
  签名: (s : 集合 ι) (t : 对任意 i, 集合 (α i))
  定义体: {f | forall i in s, f i in t i}
-/
def pi (s : Set ι) (t : forall i, Set (α i)) : Set (forall i, α i) := {f | forall i in s, f i in t i}

variable {s : Set ι} {t : forall i, Set (α i)} {f : forall i, α i}

/--
theorem `mem_pi` / 定理 `mem_pi`

English:
theorem mem_pi
  statement: f in s.pi t ↔ forall i in s, f i in t i
  proof: .rfl

中文:
定理 mem_pi
  结论: f in s.pi t ↔ 对任意 i in s, f i in t i
  证明: .rfl
-/
@[simp, grind =, push] theorem mem_pi : f in s.pi t ↔ forall i in s, f i in t i := .rfl

/--
theorem `mem_univ_pi` / 定理 `mem_univ_pi`

English:
theorem mem_univ_pi
  statement: f in pi univ t ↔ forall i, f i in t i
  proof: by simp

中文:
定理 mem_univ_pi
  结论: f in pi univ t ↔ 对任意 i, f i in t i
  证明: by simp
-/
theorem mem_univ_pi : f in pi univ t ↔ forall i, f i in t i := by simp

end Pi

/--
Definition of `EqOn` / `EqOn` 的定义

English:
definition EqOn
  signature: (f₁ f₂ : α -> β) (s : Set α)
  body: forall ⦃x⦄, x in s -> f₁ x = f₂ x

中文:
定义 EqOn
  签名: (f₁ f₂ : α -> β) (s : 集合 α)
  定义体: forall ⦃x⦄, x in s -> f₁ x = f₂ x
-/
def EqOn (f₁ f₂ : α -> β) (s : Set α) : Prop := forall ⦃x⦄, x in s -> f₁ x = f₂ x

/--
Definition of `MapsTo` / `MapsTo` 的定义

English:
definition MapsTo
  signature: (f : α -> β) (s : Set α) (t : Set β)
  body: forall ⦃x⦄, x in s -> f x in t

中文:
定义 映射到
  签名: (f : α -> β) (s : 集合 α) (t : 集合 β)
  定义体: forall ⦃x⦄, x in s -> f x in t
-/
def MapsTo (f : α -> β) (s : Set α) (t : Set β) : Prop := forall ⦃x⦄, x in s -> f x in t

/--
theorem `mapsTo_image` / 定理 `mapsTo_image`

English:
theorem mapsTo_image
  given: (f : α -> β) (s : Set α)
  statement: MapsTo f s (f '' s)
  proof: fun _ => mem_image_of_mem f

中文:
定理 mapsTo_image
  条件: (f : α -> β) (s : 集合 α)
  结论: 映射到 f s (f '' s)
  证明: fun _ => mem_image_of_mem f

Depends on / 依赖: mem_image_of_mem
-/
theorem mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f '' s) := fun _ => mem_image_of_mem f

/--
theorem `mapsTo_preimage` / 定理 `mapsTo_preimage`

English:
theorem mapsTo_preimage
  given: (f : α -> β) (t : Set β)
  statement: MapsTo f (f ⁻¹' t) t
  proof: fun _ => id

中文:
定理 mapsTo_preimage
  条件: (f : α -> β) (t : 集合 β)
  结论: 映射到 f (f ⁻¹' t) t
  证明: fun _ => id
-/
theorem mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f (f ⁻¹' t) t := fun _ => id

/--
Definition of `MapsTo.restrict` / `MapsTo.restrict` 的定义

English:
definition MapsTo.restrict
  signature: (f : α -> β) (s : Set α) (t : Set β) (h : MapsTo f s t)
  body: Subtype.map f h

中文:
定义 映射到.restrict
  签名: (f : α -> β) (s : 集合 α) (t : 集合 β) (h : 映射到 f s t)
  定义体: Subtype.map f h

Depends on / 依赖: Subtype, Subtype.map
-/
def MapsTo.restrict (f : α -> β) (s : Set α) (t : Set β) (h : MapsTo f s t) : s -> t :=
  Subtype.map f h

/-- The restriction of a function onto the preimage of a set. -/
@[simps!]
/--
Definition of `restrictPreimage` / `restrictPreimage` 的定义

English:
definition restrictPreimage
  signature: (t : Set β) (f : α -> β)
  body: (Set.mapsTo_preimage f t).restrict _ _ _

中文:
定义 restrictPreimage
  签名: (t : 集合 β) (f : α -> β)
  定义体: (Set.mapsTo_preimage f t).restrict _ _ _

Depends on / 依赖: Set.mapsTo_preimage, mapsTo_preimage, restrict
-/
def restrictPreimage (t : Set β) (f : α -> β) : f ⁻¹' t -> t :=
  (Set.mapsTo_preimage f t).restrict _ _ _

/--
Definition of `InjOn` / `InjOn` 的定义

English:
definition InjOn
  signature: (f : α -> β) (s : Set α)
  body: forall ⦃x₁ : α⦄, x₁ in s -> forall ⦃x₂ : α⦄, x₂ in s -> f x₁ = f x₂ -> x₁ = x₂

中文:
定义 单射限制
  签名: (f : α -> β) (s : 集合 α)
  定义体: forall ⦃x₁ : α⦄, x₁ in s -> forall ⦃x₂ : α⦄, x₂ in s -> f x₁ = f x₂ -> x₁ = x₂
-/
def InjOn (f : α -> β) (s : Set α) : Prop :=
  forall ⦃x₁ : α⦄, x₁ in s -> forall ⦃x₂ : α⦄, x₂ in s -> f x₁ = f x₂ -> x₁ = x₂

/--
Definition of `graphOn` / `graphOn` 的定义

English:
definition graphOn
  signature: (f : α -> β) (s : Set α)
  body: (fun x => (x, f x)) '' s

中文:
定义 graphOn
  签名: (f : α -> β) (s : 集合 α)
  定义体: (fun x => (x, f x)) '' s
-/
def graphOn (f : α -> β) (s : Set α) : Set (α × β) := (fun x => (x, f x)) '' s

/--
Definition of `SurjOn` / `SurjOn` 的定义

English:
definition SurjOn
  signature: (f : α -> β) (s : Set α) (t : Set β)
  body: t subseteq f '' s

中文:
定义 满射限制
  签名: (f : α -> β) (s : 集合 α) (t : 集合 β)
  定义体: t subseteq f '' s

Depends on / 依赖: subseteq
-/
def SurjOn (f : α -> β) (s : Set α) (t : Set β) : Prop := t subseteq f '' s

/--
Definition of `BijOn` / `BijOn` 的定义

English:
definition BijOn
  signature: (f : α -> β) (s : Set α) (t : Set β)
  body: MapsTo f s t ∧ InjOn f s ∧ SurjOn f s t

中文:
定义 双射限制
  签名: (f : α -> β) (s : 集合 α) (t : 集合 β)
  定义体: MapsTo f s t ∧ InjOn f s ∧ SurjOn f s t

Depends on / 依赖: MapsTo, SurjOn
-/
def BijOn (f : α -> β) (s : Set α) (t : Set β) : Prop := MapsTo f s t ∧ InjOn f s ∧ SurjOn f s t

/--
Definition of `LeftInvOn` / `LeftInvOn` 的定义

English:
definition LeftInvOn
  signature: (g : β -> α) (f : α -> β) (s : Set α)
  body: forall ⦃x⦄, x in s -> g (f x) = x

中文:
定义 LeftInvOn
  签名: (g : β -> α) (f : α -> β) (s : 集合 α)
  定义体: forall ⦃x⦄, x in s -> g (f x) = x

Depends on / 依赖: infer_instance, invApp
-/
def LeftInvOn (g : β -> α) (f : α -> β) (s : Set α) : Prop := forall ⦃x⦄, x in s -> g (f x) = x

/--
Definition of `RightInvOn` / `RightInvOn` 的定义

English:
abbreviation RightInvOn
  signature: (g : β -> α) (f : α -> β) (t : Set β)
  body: LeftInvOn f g t

中文:
缩写 RightInvOn
  签名: (g : β -> α) (f : α -> β) (t : 集合 β)
  定义体: LeftInvOn f g t

Depends on / 依赖: LeftInvOn
-/
abbrev RightInvOn (g : β -> α) (f : α -> β) (t : Set β) : Prop := LeftInvOn f g t

/--
Definition of `InvOn` / `InvOn` 的定义

English:
definition InvOn
  signature: (g : β -> α) (f : α -> β) (s : Set α) (t : Set β)
  body: LeftInvOn g f s ∧ RightInvOn g f t

中文:
定义 InvOn
  签名: (g : β -> α) (f : α -> β) (s : 集合 α) (t : 集合 β)
  定义体: LeftInvOn g f s ∧ RightInvOn g f t

Depends on / 依赖: LeftInvOn, RightInvOn
-/
def InvOn (g : β -> α) (f : α -> β) (s : Set α) (t : Set β) : Prop :=
  LeftInvOn g f s ∧ RightInvOn g f t

section image2

/--
Definition of `image2` / `image2` 的定义

English:
definition image2
  signature: (f : α -> β -> γ) (s : Set α) (t : Set β)
  body: {c | exists a in s, exists b in t, f a b = c}

中文:
定义 image2
  签名: (f : α -> β -> γ) (s : 集合 α) (t : 集合 β)
  定义体: {c | exists a in s, exists b in t, f a b = c}
-/
def image2 (f : α -> β -> γ) (s : Set α) (t : Set β) : Set γ := {c | exists a in s, exists b in t, f a b = c}

variable {f : α -> β -> γ} {s : Set α} {t : Set β} {a : α} {b : β} {c : γ}

/--
theorem `mem_image2` / 定理 `mem_image2`

English:
theorem mem_image2
  statement: c in image2 f s t ↔ exists a in s, exists b in t, f a b = c
  proof: .rfl

中文:
定理 mem_image2
  结论: c in image2 f s t ↔ 存在 a in s, 存在 b in t, f a b = c
  证明: .rfl
-/
@[simp, grind =] theorem mem_image2 : c in image2 f s t ↔ exists a in s, exists b in t, f a b = c := .rfl

/--
theorem `mem_image2_of_mem` / 定理 `mem_image2_of_mem`

English:
theorem mem_image2_of_mem
  given: (ha : a in s) (hb : b in t)
  statement: f a b in image2 f s t
  proof: ⟨a, ha, b, hb, rfl⟩

中文:
定理 mem_image2_of_mem
  条件: (ha : a in s) (hb : b in t)
  结论: f a b in image2 f s t
  证明: ⟨a, ha, b, hb, rfl⟩
-/
theorem mem_image2_of_mem (ha : a in s) (hb : b in t) : f a b in image2 f s t :=
  ⟨a, ha, b, hb, rfl⟩

end image2

/--
Definition of `seq` / `seq` 的定义

English:
definition seq
  signature: (s : Set (α -> β)) (t : Set α)
  body: image2 (fun f => f) s t

@[simp, grind =]

中文:
定义 seq
  签名: (s : 集合 (α -> β)) (t : 集合 α)
  定义体: image2 (fun f => f) s t

@[simp, grind =]

Depends on / 依赖: image2
-/
def seq (s : Set (α -> β)) (t : Set α) : Set β := image2 (fun f => f) s t

@[simp, grind =]
/--
theorem `mem_seq_iff` / 定理 `mem_seq_iff`

English:
theorem mem_seq_iff
  given: {s : Set (α -> β)} {t : Set α} {b : β}
  proof: Iff.rfl

中文:
定理 mem_seq_iff
  条件: {s : 集合 (α -> β)} {t : 集合 α} {b : β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_seq_iff {s : Set (α -> β)} {t : Set α} {b : β} :
    b in seq s t ↔ exists f in s, exists a in t, (f : α -> β) a = b :=
  Iff.rfl

/--
lemma `seq_eq_image2` / 引理 `seq_eq_image2`

English:
lemma seq_eq_image2
  given: (s : Set (α -> β)) (t : Set α)
  statement: seq s t = image2 (fun f a => f a) s t
  proof: rfl

中文:
引理 seq_eq_image2
  条件: (s : 集合 (α -> β)) (t : 集合 α)
  结论: seq s t = image2 (fun f a => f a) s t
  证明: rfl
-/
lemma seq_eq_image2 (s : Set (α -> β)) (t : Set α) : seq s t = image2 (fun f a => f a) s t := rfl

end Set
