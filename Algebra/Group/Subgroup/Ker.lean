/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Tactic.ApplyFun

import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Kernel and range of group homomorphisms

We define and prove results about the kernel and range of group homomorphisms.

Special thanks goes to Amelia Livingston and Yury Kudryashov for their help and inspiration.

## Main definitions

Notation used here:

- `G N` are `Group`s

- `x` is an element of type `G`

- `f g : N →* G` are group homomorphisms

Definitions in the file:

* `MonoidHom.range f` : the range of the group homomorphism `f` is a subgroup

* `MonoidHom.ker f` : the kernel of a group homomorphism `f` is the subgroup of elements `x : G`
  such that `f x = 1`

* `MonoidHom.eqLocus f g` : given group homomorphisms `f`, `g`, the elements of `G` such that
  `f x = g x` form a subgroup of `G`

## Implementation notes

Subgroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subgroup's underlying set.

## Tags
subgroup, subgroups
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Multiset Ring

open Function
open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']
variable {A : Type*} [AddGroup A]

namespace MonoidHom

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

open Subgroup

/-- The range of a monoid homomorphism from a group is a subgroup. -/
@[to_additive /-- The range of an `AddMonoidHom` from an `AddGroup` is an `AddSubgroup`. -/]
/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (f : G ->* N)
  body: Subgroup.copy ((⊤ : Subgroup G).map f) (Set.range f) (by simp)

@[to_additive]

中文:
定义 range
  签名: (f : G ->* N)
  定义体: Subgroup.copy ((⊤ : Subgroup G).map f) (Set.range f) (by simp)

@[to_additive]

Depends on / 依赖: Set.range, Subgroup, Subgroup.copy
-/
def range (f : G ->* N) : Subgroup N :=
  Subgroup.copy ((⊤ : Subgroup G).map f) (Set.range f) (by simp)

@[to_additive]
/--
lemma `subsingleton_coe_range` / 引理 `subsingleton_coe_range`

English:
lemma subsingleton_coe_range
  given: [Subsingleton G] (f : G ->* N)
  statement: (f.range : Set N).Subsingleton
  proof: Set.subsingleton_range f

@[to_additive (attr := simp)]

中文:
引理 subsingleton_coe_range
  条件: [子单例 G] (f : G ->* N)
  结论: (f.range : 集合 N).子单例
  证明: Set.subsingleton_range f

@[to_additive (attr := simp)]

Depends on / 依赖: Set.subsingleton_range, subsingleton_range
-/
lemma subsingleton_coe_range [Subsingleton G] (f : G ->* N) : (f.range : Set N).Subsingleton :=
  Set.subsingleton_range f

@[to_additive (attr := simp)]
/--
theorem `coe_range` / 定理 `coe_range`

English:
theorem coe_range
  given: (f : G ->* N)
  statement: (f.range : Set N) = Set.range f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_range
  条件: (f : G ->* N)
  结论: (f.range : 集合 N) = 集合.range f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_range (f : G ->* N) : (f.range : Set N) = Set.range f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_range` / 定理 `mem_range`

English:
theorem mem_range
  given: {f : G ->* N} {y : N}
  statement: y in f.range ↔ exists x, f x = y
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_range
  条件: {f : G ->* N} {y : N}
  结论: y in f.range ↔ 存在 x, f x = y
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_range {f : G ->* N} {y : N} : y in f.range ↔ exists x, f x = y :=
  Iff.rfl

@[to_additive]
/--
theorem `range_eq_map` / 定理 `range_eq_map`

English:
theorem range_eq_map
  given: (f : G ->* N)
  statement: f.range = (⊤ : Subgroup G).map f
  proof: by ext; simp

@[to_additive (attr := simp)]

中文:
定理 range_eq_map
  条件: (f : G ->* N)
  结论: f.range = (⊤ : 子群 G).map f
  证明: by ext; simp

@[to_additive (attr := simp)]
-/
theorem range_eq_map (f : G ->* N) : f.range = (⊤ : Subgroup G).map f := by ext; simp

@[to_additive (attr := simp)]
/--
theorem `comap_range_self` / 定理 `comap_range_self`

English:
theorem comap_range_self
  given: (f : G ->* N)
  statement: f.range.comap f = ⊤
  proof: by
  ext
  simp

@[to_additive]

中文:
定理 comap_range_self
  条件: (f : G ->* N)
  结论: f.range.comap f = ⊤
  证明: by
  ext
  simp

@[to_additive]
-/
theorem comap_range_self (f : G ->* N) : f.range.comap f = ⊤ := by
  ext
  simp

@[to_additive]
/--
Instance `_root_.Subgroup.range_isMulCommutative` / 实例 `_root_.Subgroup.range_isMulCommutative`

English:
instance _root_.Subgroup.range_isMulCommutative
  signature: {G : Type*} [Group G] [IsMulCommutative G]
  body: range_eq_map f ▸ Subgroup.map_isMulCommutative ⊤ f

@[to_additive (attr := simp)]

中文:
实例 _root_.子群.range_isMulCommutative
  签名: {G : 类型} [群 G] [是MulCommutative G]
  定义体: range_eq_map f ▸ Subgroup.map_isMulCommutative ⊤ f

@[to_additive (attr := simp)]

Depends on / 依赖: Subgroup, Subgroup.map_isMulCommutative, map_isMulCommutative, range_eq_map
-/
instance _root_.Subgroup.range_isMulCommutative {G : Type*} [Group G] [IsMulCommutative G]
    {N : Type*} [Group N] (f : G ->* N) :
    IsMulCommutative f.range :=
  range_eq_map f ▸ Subgroup.map_isMulCommutative ⊤ f

@[to_additive (attr := simp)]
/--
theorem `domRestrict_range` / 定理 `domRestrict_range`

English:
theorem domRestrict_range
  given: (f : G ->* N)
  statement: (f.domRestrict K).range = K.map f
  proof: by
  simp_rw [SetLike.ext_iff, mem_range, mem_map, domRestrict_apply, SetLike.exists,
    exists_prop, forall_const]

@[deprecated (since := "2026-07-19")] alias restrict_range := domRestrict_range
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_range := _root_.AddMonoidHom.domRestrict_range

中文:
定理 domRestrict_range
  条件: (f : G ->* N)
  结论: (f.domRestrict K).range = K.map f
  证明: by
  simp_rw [SetLike.ext_iff, mem_range, mem_map, domRestrict_apply, SetLike.exists,
    exists_prop, forall_const]

@[deprecated (since := "2026-07-19")] alias restrict_range := domRestrict_range
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_range := _root_.AddMonoidHom.domRestrict_range

Depends on / 依赖: SetLike, SetLike.exists, SetLike.ext_iff, domRestrict_apply, exists_prop, ext_iff, forall_const, mem_map, mem_range, simp_rw
-/
theorem domRestrict_range (f : G ->* N) : (f.domRestrict K).range = K.map f := by
  simp_rw [SetLike.ext_iff, mem_range, mem_map, domRestrict_apply, SetLike.exists,
    exists_prop, forall_const]

@[deprecated (since := "2026-07-19")] alias restrict_range := domRestrict_range
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_range := _root_.AddMonoidHom.domRestrict_range

/-- The canonical surjective group homomorphism `G →* f(G)` induced by a group
homomorphism `G →* N`. -/
@[to_additive
      /-- The canonical surjective `AddGroup` homomorphism `G →+ f(G)` induced by a group
      homomorphism `G →+ N`. -/]
/--
Definition of `rangeRestrict` / `rangeRestrict` 的定义

English:
definition rangeRestrict
  signature: (f : G ->* N)
  body: codRestrict f _ fun x => ⟨x, rfl⟩

@[to_additive (attr := simp)]

中文:
定义 rangeRestrict
  签名: (f : G ->* N)
  定义体: codRestrict f _ fun x => ⟨x, rfl⟩

@[to_additive (attr := simp)]

Depends on / 依赖: codRestrict
-/
def rangeRestrict (f : G ->* N) : G ->* f.range :=
  codRestrict f _ fun x => ⟨x, rfl⟩

@[to_additive (attr := simp)]
/--
theorem `coe_rangeRestrict` / 定理 `coe_rangeRestrict`

English:
theorem coe_rangeRestrict
  given: (f : G ->* N) (g : G)
  statement: (f.rangeRestrict g : N) = f g
  proof: rfl

@[to_additive]

中文:
定理 coe_rangeRestrict
  条件: (f : G ->* N) (g : G)
  结论: (f.rangeRestrict g : N) = f g
  证明: rfl

@[to_additive]
-/
theorem coe_rangeRestrict (f : G ->* N) (g : G) : (f.rangeRestrict g : N) = f g :=
  rfl

@[to_additive]
/--
theorem `coe_comp_rangeRestrict` / 定理 `coe_comp_rangeRestrict`

English:
theorem coe_comp_rangeRestrict
  given: (f : G ->* N)
  proof: rfl

@[to_additive]

中文:
定理 coe_comp_rangeRestrict
  条件: (f : G ->* N)
  证明: rfl

@[to_additive]
-/
theorem coe_comp_rangeRestrict (f : G ->* N) :
    ((↑) : f.range -> N) ∘ (⇑f.rangeRestrict : G -> f.range) = f :=
  rfl

@[to_additive]
/--
theorem `subtype_comp_rangeRestrict` / 定理 `subtype_comp_rangeRestrict`

English:
theorem subtype_comp_rangeRestrict
  given: (f : G ->* N)
  statement: f.range.subtype.comp f.rangeRestrict = f
  proof: ext f.coe_rangeRestrict

@[to_additive]

中文:
定理 subtype_comp_rangeRestrict
  条件: (f : G ->* N)
  结论: f.range.subtype.comp f.rangeRestrict = f
  证明: ext f.coe_rangeRestrict

@[to_additive]

Depends on / 依赖: coe_rangeRestrict, f.coe_rangeRestrict
-/
theorem subtype_comp_rangeRestrict (f : G ->* N) : f.range.subtype.comp f.rangeRestrict = f :=
ext f.coe_rangeRestrict

@[to_additive]
/--
theorem `rangeRestrict_surjective` / 定理 `rangeRestrict_surjective`

English:
theorem rangeRestrict_surjective
  given: (f : G ->* N)
  statement: Function.Surjective f.rangeRestrict
  proof: fun ⟨_, g, rfl⟩ => ⟨g, rfl⟩

@[to_additive (attr := simp)]

中文:
定理 rangeRestrict_surjective
  条件: (f : G ->* N)
  结论: 函数.满射 f.rangeRestrict
  证明: fun ⟨_, g, rfl⟩ => ⟨g, rfl⟩

@[to_additive (attr := simp)]
-/
theorem rangeRestrict_surjective (f : G ->* N) : Function.Surjective f.rangeRestrict :=
  fun ⟨_, g, rfl⟩ => ⟨g, rfl⟩

@[to_additive (attr := simp)]
/--
lemma `rangeRestrict_injective_iff` / 引理 `rangeRestrict_injective_iff`

English:
lemma rangeRestrict_injective_iff
  given: {f : G ->* N}
  statement: Injective f.rangeRestrict ↔ Injective f
  proof: by
  convert! Set.injective_codRestrict _

@[to_additive]

中文:
引理 rangeRestrict_injective_iff
  条件: {f : G ->* N}
  结论: 单射 f.rangeRestrict ↔ 单射 f
  证明: by
  convert! Set.injective_codRestrict _

@[to_additive]

Depends on / 依赖: Set.injective_codRestrict, convert, injective_codRestrict
-/
lemma rangeRestrict_injective_iff {f : G ->* N} : Injective f.rangeRestrict ↔ Injective f := by
  convert! Set.injective_codRestrict _

@[to_additive]
/--
theorem `map_range` / 定理 `map_range`

English:
theorem map_range
  given: (g : N ->* P) (f : G ->* N)
  statement: f.range.map g = (g.comp f).range
  proof: by
  rw [range_eq_map]; rw [range_eq_map]; exact (⊤ : Subgroup G).map_map g f

@[to_additive]

中文:
定理 map_range
  条件: (g : N ->* P) (f : G ->* N)
  结论: f.range.map g = (g.comp f).range
  证明: by
  rw [range_eq_map]; rw [range_eq_map]; exact (⊤ : Subgroup G).map_map g f

@[to_additive]

Depends on / 依赖: Subgroup, map_map, range_eq_map
-/
theorem map_range (g : N ->* P) (f : G ->* N) : f.range.map g = (g.comp f).range := by
  rw [range_eq_map]; rw [range_eq_map]; exact (⊤ : Subgroup G).map_map g f

@[to_additive]
/--
lemma `range_comp` / 引理 `range_comp`

English:
lemma range_comp
  given: (g : N ->* P) (f : G ->* N)
  statement: (g.comp f).range = f.range.map g
  proof: (map_range ..).symm

@[to_additive]

中文:
引理 range_comp
  条件: (g : N ->* P) (f : G ->* N)
  结论: (g.comp f).range = f.range.map g
  证明: (map_range ..).symm

@[to_additive]

Depends on / 依赖: map_range
-/
lemma range_comp (g : N ->* P) (f : G ->* N) : (g.comp f).range = f.range.map g := (map_range ..).symm

@[to_additive]
/--
theorem `range_eq_top` / 定理 `range_eq_top`

English:
theorem range_eq_top
  given: {N} [Group N] {f : G ->* N}
  proof: SetLike.ext'_iff.trans Iff.trans (by rw [coe_range, coe_top]) Set.range_eq_univ

中文:
定理 range_eq_top
  条件: {N} [群 N] {f : G ->* N}
  证明: SetLike.ext'_iff.trans Iff.trans (by rw [coe_range, coe_top]) Set.range_eq_univ

Depends on / 依赖: Iff.trans, Set.range_eq_univ, SetLike, SetLike.ext, _iff, _iff.trans, coe_range, coe_top, range_eq_univ
-/
theorem range_eq_top {N} [Group N] {f : G ->* N} :
    f.range = (⊤ : Subgroup N) ↔ Function.Surjective f :=
SetLike.ext'_iff.trans Iff.trans (by rw [coe_range, coe_top]) Set.range_eq_univ

/-- The range of a surjective monoid homomorphism is the whole of the codomain. -/
@[to_additive (attr := simp)
  /-- The range of a surjective `AddMonoid` homomorphism is the whole of the codomain. -/]
/--
theorem `range_eq_top_of_surjective` / 定理 `range_eq_top_of_surjective`

English:
theorem range_eq_top_of_surjective
  given: {N} [Group N] (f : G ->* N) (hf : Function.Surjective f)
  proof: range_eq_top.2 hf

@[to_additive (attr := simp)]

中文:
定理 range_eq_top_of_surjective
  条件: {N} [群 N] (f : G ->* N) (hf : 函数.满射 f)
  证明: range_eq_top.2 hf

@[to_additive (attr := simp)]

Depends on / 依赖: range_eq_top
-/
theorem range_eq_top_of_surjective {N} [Group N] (f : G ->* N) (hf : Function.Surjective f) :
    f.range = (⊤ : Subgroup N) :=
  range_eq_top.2 hf

@[to_additive (attr := simp)]
/--
theorem `range_one` / 定理 `range_one`

English:
theorem range_one
  statement: (1 : G ->* N).range = ⊥
  proof: SetLike.ext fun x => by simpa using @comm _ (· = ·) _ 1 x

@[to_additive (attr := simp)]

中文:
定理 range_one
  结论: (1 : G ->* N).range = ⊥
  证明: SetLike.ext fun x => by simpa using @comm _ (· = ·) _ 1 x

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem range_one : (1 : G ->* N).range = ⊥ :=
  SetLike.ext fun x => by simpa using @comm _ (· = ·) _ 1 x

@[to_additive (attr := simp)]
/--
theorem `_root_.Subgroup.range_subtype` / 定理 `_root_.Subgroup.range_subtype`

English:
theorem _root_.Subgroup.range_subtype
  given: (H : Subgroup G)
  statement: H.subtype.range = H
  proof: SetLike.coe_injective (coe_range _).trans Subtype.range_coe

@[to_additive]
alias _root_.Subgroup.subtype_range := Subgroup.range_subtype

@[to_additive (attr := simp)]

中文:
定理 _root_.子群.range_subtype
  条件: (H : 子群 G)
  结论: H.subtype.range = H
  证明: SetLike.coe_injective (coe_range _).trans Subtype.range_coe

@[to_additive]
alias _root_.Subgroup.subtype_range := Subgroup.range_subtype

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.coe_injective, Subtype, Subtype.range_coe, coe_injective, coe_range, range_coe
-/
theorem _root_.Subgroup.range_subtype (H : Subgroup G) : H.subtype.range = H :=
SetLike.coe_injective (coe_range _).trans Subtype.range_coe

@[to_additive]
alias _root_.Subgroup.subtype_range := Subgroup.range_subtype

@[to_additive (attr := simp)]
/--
theorem `_root_.Subgroup.inclusion_range` / 定理 `_root_.Subgroup.inclusion_range`

English:
theorem _root_.Subgroup.inclusion_range
  given: {H K : Subgroup G} (h_le : H <= K)
  proof: Subgroup.ext fun g => Set.ext_iff.mp (Set.range_inclusion h_le) g

@[to_additive]

中文:
定理 _root_.子群.inclusion_range
  条件: {H K : 子群 G} (h_le : H <= K)
  证明: Subgroup.ext fun g => Set.ext_iff.mp (Set.range_inclusion h_le) g

@[to_additive]

Depends on / 依赖: Set.ext_iff.mp, Set.range_inclusion, Subgroup, Subgroup.ext, ext_iff, h_le, range_inclusion
-/
theorem _root_.Subgroup.inclusion_range {H K : Subgroup G} (h_le : H <= K) :
    (inclusion h_le).range = H.subgroupOf K :=
  Subgroup.ext fun g => Set.ext_iff.mp (Set.range_inclusion h_le) g

@[to_additive]
/--
theorem `subgroupOf_range_eq_of_le` / 定理 `subgroupOf_range_eq_of_le`

English:
theorem subgroupOf_range_eq_of_le
  statement: {G₁ G₂ : Type*} [Group G₁] [Group G₂] {K : Subgroup G₂}
  proof: by
  ext k
  refine exists_congr ?_
  simp [Subtype.ext_iff]

中文:
定理 subgroupOf_range_eq_of_le
  结论: {G₁ G₂ : 类型} [群 G₁] [群 G₂] {K : 子群 G₂}
  证明: by
  ext k
  refine exists_congr ?_
  simp [Subtype.ext_iff]

Depends on / 依赖: Subtype, Subtype.ext_iff, exists_congr, ext_iff
-/
theorem subgroupOf_range_eq_of_le {G₁ G₂ : Type*} [Group G₁] [Group G₂] {K : Subgroup G₂}
    (f : G₁ ->* G₂) (h : f.range <= K) :
    f.range.subgroupOf K = (f.codRestrict K fun x => h ⟨x, rfl⟩).range := by
  ext k
  refine exists_congr ?_
  simp [Subtype.ext_iff]

/-- Computable alternative to `MonoidHom.ofInjective`. -/
@[to_additive /-- Computable alternative to `AddMonoidHom.ofInjective`. -/]
/--
Definition of `ofLeftInverse` / `ofLeftInverse` 的定义

English:
definition ofLeftInverse
  signature: {f : G ->* N} {g : N ->* G} (h : Function.LeftInverse g f)
  body: { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.subtype
    left_inv := h
    right_inv := by
      rintro ⟨x, y, rfl⟩
      solve_by_elim }

@[to_additive (attr := simp)]

中文:
定义 ofLeftInverse
  签名: {f : G ->* N} {g : N ->* G} (h : 函数.左逆 g f)
  定义体: { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.subtype
    left_inv := h
    right_inv := by
      rintro ⟨x, y, rfl⟩
      solve_by_elim }

@[to_additive (attr := simp)]

Depends on / 依赖: f.range.subtype, f.rangeRestrict, invFun, left_inv, rangeRestrict, right_inv, solve_by_elim, subtype
-/
def ofLeftInverse {f : G ->* N} {g : N ->* G} (h : Function.LeftInverse g f) : G ≃* f.range :=
  { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.subtype
    left_inv := h
    right_inv := by
      rintro ⟨x, y, rfl⟩
      solve_by_elim }

@[to_additive (attr := simp)]
/--
theorem `ofLeftInverse_apply` / 定理 `ofLeftInverse_apply`

English:
theorem ofLeftInverse_apply
  given: {f : G ->* N} {g : N ->* G} (h : Function.LeftInverse g f) (x : G)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 ofLeftInverse_apply
  条件: {f : G ->* N} {g : N ->* G} (h : 函数.左逆 g f) (x : G)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem ofLeftInverse_apply {f : G ->* N} {g : N ->* G} (h : Function.LeftInverse g f) (x : G) :
    ↑(ofLeftInverse h x) = f x :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `ofLeftInverse_symm_apply` / 定理 `ofLeftInverse_symm_apply`

English:
theorem ofLeftInverse_symm_apply
  statement: {f : G ->* N} {g : N ->* G} (h : Function.LeftInverse g f)
  proof: rfl

中文:
定理 ofLeftInverse_symm_apply
  结论: {f : G ->* N} {g : N ->* G} (h : 函数.左逆 g f)
  证明: rfl
-/
theorem ofLeftInverse_symm_apply {f : G ->* N} {g : N ->* G} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse h).symm x = g x :=
  rfl

/-- The range of an injective group homomorphism is isomorphic to its domain. -/
@[to_additive /-- The range of an injective additive group homomorphism is isomorphic to its
domain. -/]
/--
Definition of `ofInjective` / `ofInjective` 的定义

English:
definition ofInjective
  signature: {f : G ->* N} (hf : Function.Injective f)
  body: MulEquiv.ofBijective (f.codRestrict f.range fun x => ⟨x, rfl⟩)
    ⟨fun _ _ h => hf (Subtype.ext_iff.mp h), by
      rintro ⟨x, y, rfl⟩
      exact ⟨y, rfl⟩⟩

@[to_additive]

中文:
定义 ofInjective
  签名: {f : G ->* N} (hf : 函数.单射 f)
  定义体: MulEquiv.ofBijective (f.codRestrict f.range fun x => ⟨x, rfl⟩)
    ⟨fun _ _ h => hf (Subtype.ext_iff.mp h), by
      rintro ⟨x, y, rfl⟩
      exact ⟨y, rfl⟩⟩

@[to_additive]

Depends on / 依赖: MulEquiv, MulEquiv.ofBijective, Subtype, Subtype.ext_iff.mp, codRestrict, ext_iff, f.codRestrict, f.range, ofBijective
-/
noncomputable def ofInjective {f : G ->* N} (hf : Function.Injective f) : G ≃* f.range :=
  MulEquiv.ofBijective (f.codRestrict f.range fun x => ⟨x, rfl⟩)
    ⟨fun _ _ h => hf (Subtype.ext_iff.mp h), by
      rintro ⟨x, y, rfl⟩
      exact ⟨y, rfl⟩⟩

@[to_additive]
/--
theorem `ofInjective_apply` / 定理 `ofInjective_apply`

English:
theorem ofInjective_apply
  given: {f : G ->* N} (hf : Function.Injective f) {x : G}
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 ofInjective_apply
  条件: {f : G ->* N} (hf : 函数.单射 f) {x : G}
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem ofInjective_apply {f : G ->* N} (hf : Function.Injective f) {x : G} :
    ↑(ofInjective hf x) = f x :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `apply_ofInjective_symm` / 定理 `apply_ofInjective_symm`

English:
theorem apply_ofInjective_symm
  given: {f : G ->* N} (hf : Function.Injective f) (x : f.range)
  proof: Subtype.ext_iff.1 (ofInjective hf).apply_symm_apply x

@[simp]

中文:
定理 apply_ofInjective_symm
  条件: {f : G ->* N} (hf : 函数.单射 f) (x : f.range)
  证明: Subtype.ext_iff.1 (ofInjective hf).apply_symm_apply x

@[simp]

Depends on / 依赖: Subtype, Subtype.ext_iff, apply_symm_apply, ext_iff, ofInjective
-/
theorem apply_ofInjective_symm {f : G ->* N} (hf : Function.Injective f) (x : f.range) :
    f ((ofInjective hf).symm x) = x :=
Subtype.ext_iff.1 (ofInjective hf).apply_symm_apply x

@[simp]
/--
theorem `coe_toAdditive_range` / 定理 `coe_toAdditive_range`

English:
theorem coe_toAdditive_range
  given: (f : G ->* G')
  proof: rfl

@[simp]

中文:
定理 coe_toAdditive_range
  条件: (f : G ->* G')
  证明: rfl

@[simp]
-/
theorem coe_toAdditive_range (f : G ->* G') :
    (MonoidHom.toAdditive f).range = Subgroup.toAddSubgroup f.range := rfl

@[simp]
/--
theorem `coe_toMultiplicative_range` / 定理 `coe_toMultiplicative_range`

English:
theorem coe_toMultiplicative_range
  given: {A A' : Type*} [AddGroup A] [AddGroup A'] (f : A ->+ A')
  proof: rfl

中文:
定理 coe_toMultiplicative_range
  条件: {A A' : 类型} [加法群 A] [加法群 A'] (f : A ->+ A')
  证明: rfl
-/
theorem coe_toMultiplicative_range {A A' : Type*} [AddGroup A] [AddGroup A'] (f : A ->+ A') :
    (AddMonoidHom.toMultiplicative f).range = AddSubgroup.toSubgroup f.range := rfl

section Ker

variable {M : Type*} [MulOneClass M]

/-- The multiplicative kernel of a monoid homomorphism is the subgroup of elements `x : G` such that
`f x = 1` -/
@[to_additive
      /-- The additive kernel of an `AddMonoid` homomorphism is the `AddSubgroup` of elements
      such that `f x = 0` -/]
/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: (f : G ->* M)
  body: { MonoidHom.mker f with
    inv_mem' := fun {x} (hx : f x = 1) =>
      calc
        f x⁻¹ = f x * f x⁻¹ := by rw [hx, one_mul]
        _ = 1 := by rw [← map_mul, mul_inv_cancel, map_one] }

@[to_additive (attr := simp)]

中文:
定义 ker
  签名: (f : G ->* M)
  定义体: { MonoidHom.mker f with
    inv_mem' := fun {x} (hx : f x = 1) =>
      calc
        f x⁻¹ = f x * f x⁻¹ := by rw [hx, one_mul]
        _ = 1 := by rw [← map_mul, mul_inv_cancel, map_one] }

@[to_additive (attr := simp)]

Depends on / 依赖: MonoidHom, MonoidHom.mker, inv_mem, map_mul, map_one, mul_inv_cancel, one_mul
-/
def ker (f : G ->* M) : Subgroup G :=
  { MonoidHom.mker f with
    inv_mem' := fun {x} (hx : f x = 1) =>
      calc
        f x⁻¹ = f x * f x⁻¹ := by rw [hx, one_mul]
        _ = 1 := by rw [← map_mul, mul_inv_cancel, map_one] }

@[to_additive (attr := simp)]
/--
theorem `ker_toSubmonoid` / 定理 `ker_toSubmonoid`

English:
theorem ker_toSubmonoid
  given: (f : G ->* M)
  statement: f.ker.toSubmonoid = MonoidHom.mker f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 ker_toSubmonoid
  条件: (f : G ->* M)
  结论: f.ker.toSubmonoid = 幺半群态射.mker f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem ker_toSubmonoid (f : G ->* M) : f.ker.toSubmonoid = MonoidHom.mker f := rfl

@[to_additive (attr := simp)]
/--
theorem `mem_ker` / 定理 `mem_ker`

English:
theorem mem_ker
  given: {f : G ->* M} {x : G}
  statement: x in f.ker ↔ f x = 1
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_ker
  条件: {f : G ->* M} {x : G}
  结论: x in f.ker ↔ f x = 1
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1 :=
  Iff.rfl

@[to_additive]
/--
theorem `div_mem_ker_iff` / 定理 `div_mem_ker_iff`

English:
theorem div_mem_ker_iff
  given: (f : G ->* M) {x y : G}
  statement: x / y in ker f ↔ f x = f y
  proof: by
  constructor <;> intro h
  · rw [← div_mul_cancel x y, map_mul, mem_ker.mp h, one_mul]
  · rw [mem_ker, div_eq_mul_inv, map_mul, h, ← map_mul, mul_inv_cancel, map_one]

@[to_additive]

中文:
定理 div_mem_ker_iff
  条件: (f : G ->* M) {x y : G}
  结论: x / y in ker f ↔ f x = f y
  证明: by
  constructor <;> intro h
  · rw [← div_mul_cancel x y, map_mul, mem_ker.mp h, one_mul]
  · rw [mem_ker, div_eq_mul_inv, map_mul, h, ← map_mul, mul_inv_cancel, map_one]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, div_mul_cancel, map_mul, map_one, mem_ker, mem_ker.mp, mul_inv_cancel, one_mul
-/
theorem div_mem_ker_iff (f : G ->* M) {x y : G} : x / y in ker f ↔ f x = f y := by
  constructor <;> intro h
  · rw [← div_mul_cancel x y, map_mul, mem_ker.mp h, one_mul]
  · rw [mem_ker, div_eq_mul_inv, map_mul, h, ← map_mul, mul_inv_cancel, map_one]

@[to_additive]
/--
theorem `coe_ker` / 定理 `coe_ker`

English:
theorem coe_ker
  given: (f : G ->* M)
  statement: (f.ker : Set G) = (f : G -> M) ⁻¹' {1}
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_ker
  条件: (f : G ->* M)
  结论: (f.ker : 集合 G) = (f : G -> M) ⁻¹' {1}
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_ker (f : G ->* M) : (f.ker : Set G) = (f : G -> M) ⁻¹' {1} :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `ker_toHomUnits` / 定理 `ker_toHomUnits`

English:
theorem ker_toHomUnits
  given: {M} [Monoid M] (f : G ->* M)
  statement: f.toHomUnits.ker = f.ker
  proof: by
  ext x
  simp [mem_ker, Units.ext_iff]

@[to_additive]

中文:
定理 ker_toHomUnits
  条件: {M} [幺半群 M] (f : G ->* M)
  结论: f.toHomUnits.ker = f.ker
  证明: by
  ext x
  simp [mem_ker, Units.ext_iff]

@[to_additive]

Depends on / 依赖: Units.ext_iff, ext_iff, mem_ker
-/
theorem ker_toHomUnits {M} [Monoid M] (f : G ->* M) : f.toHomUnits.ker = f.ker := by
  ext x
  simp [mem_ker, Units.ext_iff]

@[to_additive]
/--
theorem `eq_iff` / 定理 `eq_iff`

English:
theorem eq_iff
  given: (f : G ->* M) {x y : G}
  statement: f x = f y ↔ y⁻¹ * x in f.ker
  proof: by
  constructor <;> intro h
  · rw [mem_ker, map_mul, h, ← map_mul, inv_mul_cancel, map_one]
  · rw [← one_mul x, ← mul_inv_cancel y, mul_assoc, map_mul, mem_ker.1 h, mul_one]

@[to_additive]

中文:
定理 eq_iff
  条件: (f : G ->* M) {x y : G}
  结论: f x = f y ↔ y⁻¹ * x in f.ker
  证明: by
  constructor <;> intro h
  · rw [mem_ker, map_mul, h, ← map_mul, inv_mul_cancel, map_one]
  · rw [← one_mul x, ← mul_inv_cancel y, mul_assoc, map_mul, mem_ker.1 h, mul_one]

@[to_additive]

Depends on / 依赖: inv_mul_cancel, map_mul, map_one, mem_ker, mul_assoc, mul_inv_cancel, mul_one, one_mul
-/
theorem eq_iff (f : G ->* M) {x y : G} : f x = f y ↔ y⁻¹ * x in f.ker := by
  constructor <;> intro h
  · rw [mem_ker, map_mul, h, ← map_mul, inv_mul_cancel, map_one]
  · rw [← one_mul x, ← mul_inv_cancel y, mul_assoc, map_mul, mem_ker.1 h, mul_one]

@[to_additive]
/--
Instance `decidableMemKer` / 实例 `decidableMemKer`

English:
instance decidableMemKer
  signature: [DecidableEq M] (f : G ->* M)
  body: fun x =>
  decidable_of_iff (f x = 1) f.mem_ker

@[to_additive]

中文:
实例 decidableMemKer
  签名: [DecidableEq M] (f : G ->* M)
  定义体: fun x =>
  decidable_of_iff (f x = 1) f.mem_ker

@[to_additive]
-/
instance decidableMemKer [DecidableEq M] (f : G ->* M) : DecidablePred (· in f.ker) := fun x =>
  decidable_of_iff (f x = 1) f.mem_ker

@[to_additive]
/--
theorem `comap_ker` / 定理 `comap_ker`

English:
theorem comap_ker
  given: {P : Type*} [MulOneClass P] (g : N ->* P) (f : G ->* N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 comap_ker
  条件: {P : 类型} [MulOne类 P] (g : N ->* P) (f : G ->* N)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem comap_ker {P : Type*} [MulOneClass P] (g : N ->* P) (f : G ->* N) :
    g.ker.comap f = (g.comp f).ker :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comap_bot` / 定理 `comap_bot`

English:
theorem comap_bot
  given: (f : G ->* N)
  statement: (⊥ : Subgroup N).comap f = f.ker
  proof: rfl

@[to_additive]

中文:
定理 comap_bot
  条件: (f : G ->* N)
  结论: (⊥ : 子群 N).comap f = f.ker
  证明: rfl

@[to_additive]
-/
theorem comap_bot (f : G ->* N) : (⊥ : Subgroup N).comap f = f.ker :=
  rfl

@[to_additive]
/--
theorem `ker_le_comap` / 定理 `ker_le_comap`

English:
theorem ker_le_comap
  given: (f : G ->* N) (H : Subgroup N)
  statement: f.ker <= H.comap f
  proof: comap_mono bot_le

@[to_additive (attr := simp)]

中文:
定理 ker_le_comap
  条件: (f : G ->* N) (H : 子群 N)
  结论: f.ker <= H.comap f
  证明: comap_mono bot_le

@[to_additive (attr := simp)]

Depends on / 依赖: bot_le, comap_mono
-/
theorem ker_le_comap (f : G ->* N) (H : Subgroup N) : f.ker <= H.comap f :=
  comap_mono bot_le

@[to_additive (attr := simp)]
/--
theorem `ker_domRestrict` / 定理 `ker_domRestrict`

English:
theorem ker_domRestrict
  given: (f : G ->* M)
  statement: (f.domRestrict K).ker = f.ker.subgroupOf K
  proof: rfl

@[deprecated (since := "2026-07-19")] alias ker_restrict := ker_domRestrict
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.ker_restrict := _root_.AddMonoidHom.ker_domRestrict

@[to_additive (attr := simp)]

中文:
定理 ker_domRestrict
  条件: (f : G ->* M)
  结论: (f.domRestrict K).ker = f.ker.subgroupOf K
  证明: rfl

@[deprecated (since := "2026-07-19")] alias ker_restrict := ker_domRestrict
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.ker_restrict := _root_.AddMonoidHom.ker_domRestrict

@[to_additive (attr := simp)]
-/
theorem ker_domRestrict (f : G ->* M) : (f.domRestrict K).ker = f.ker.subgroupOf K :=
  rfl

@[deprecated (since := "2026-07-19")] alias ker_restrict := ker_domRestrict
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.ker_restrict := _root_.AddMonoidHom.ker_domRestrict

@[to_additive (attr := simp)]
/--
theorem `ker_codRestrict` / 定理 `ker_codRestrict`

English:
theorem ker_codRestrict
  statement: {S} [SetLike S N] [SubmonoidClass S N] (f : G ->* N) (s : S)
  proof: SetLike.ext fun _x => Subtype.ext_iff

@[to_additive (attr := simp)]

中文:
定理 ker_codRestrict
  结论: {S} [集合状 S N] [子幺半群类 S N] (f : G ->* N) (s : S)
  证明: SetLike.ext fun _x => Subtype.ext_iff

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.ext, Subtype, Subtype.ext_iff, ext_iff
-/
theorem ker_codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : G ->* N) (s : S)
    (h : forall x, f x in s) : (f.codRestrict s h).ker = f.ker :=
  SetLike.ext fun _x => Subtype.ext_iff

@[to_additive (attr := simp)]
/--
theorem `ker_rangeRestrict` / 定理 `ker_rangeRestrict`

English:
theorem ker_rangeRestrict
  given: (f : G ->* N)
  statement: ker (rangeRestrict f) = ker f
  proof: ker_codRestrict _ _ _

@[to_additive (attr := simp)]

中文:
定理 ker_rangeRestrict
  条件: (f : G ->* N)
  结论: ker (rangeRestrict f) = ker f
  证明: ker_codRestrict _ _ _

@[to_additive (attr := simp)]

Depends on / 依赖: ker_codRestrict
-/
theorem ker_rangeRestrict (f : G ->* N) : ker (rangeRestrict f) = ker f :=
  ker_codRestrict _ _ _

@[to_additive (attr := simp)]
/--
theorem `ker_one` / 定理 `ker_one`

English:
theorem ker_one
  statement: (1 : G ->* M).ker = ⊤
  proof: SetLike.ext fun _x => eq_self_iff_true _

@[to_additive (attr := simp)]

中文:
定理 ker_one
  结论: (1 : G ->* M).ker = ⊤
  证明: SetLike.ext fun _x => eq_self_iff_true _

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.ext, eq_self_iff_true
-/
theorem ker_one : (1 : G ->* M).ker = ⊤ :=
  SetLike.ext fun _x => eq_self_iff_true _

@[to_additive (attr := simp)]
/--
theorem `ker_id` / 定理 `ker_id`

English:
theorem ker_id
  statement: (MonoidHom.id G).ker = ⊥
  proof: rfl

中文:
定理 ker_id
  结论: (幺半群态射.id G).ker = ⊥
  证明: rfl

Depends on / 依赖: Set.image_univ.symm, Set.range, Submonoid, image_univ
-/
theorem ker_id : (MonoidHom.id G).ker = ⊥ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ker_eq_top_iff` / 定理 `ker_eq_top_iff`

English:
theorem ker_eq_top_iff
  given: {f : G ->* M}
  statement: f.ker = ⊤ ↔ f = 1
  proof: by
  simp [ker, ← top_le_iff, SetLike.le_def, f.ext_iff]

中文:
定理 ker_eq_top_iff
  条件: {f : G ->* M}
  结论: f.ker = ⊤ ↔ f = 1
  证明: by
  simp [ker, ← top_le_iff, SetLike.le_def, f.ext_iff]
-/
@[to_additive] theorem ker_eq_top_iff {f : G ->* M} : f.ker = ⊤ ↔ f = 1 := by
  simp [ker, ← top_le_iff, SetLike.le_def, f.ext_iff]

/--
theorem `range_eq_bot_iff` / 定理 `range_eq_bot_iff`

English:
theorem range_eq_bot_iff
  given: {f : G ->* G'}
  statement: f.range = ⊥ ↔ f = 1
  proof: by
  rw [← le_bot_iff]; rw [f.range_eq_map]; rw [map_le_iff_le_comap]; rw [top_le_iff]; rw [comap_bot]; rw [ker_eq_top_iff]

@[to_additive]

中文:
定理 range_eq_bot_iff
  条件: {f : G ->* G'}
  结论: f.range = ⊥ ↔ f = 1
  证明: by
  rw [← le_bot_iff]; rw [f.range_eq_map]; rw [map_le_iff_le_comap]; rw [top_le_iff]; rw [comap_bot]; rw [ker_eq_top_iff]

@[to_additive]
-/
@[to_additive] theorem range_eq_bot_iff {f : G ->* G'} : f.range = ⊥ ↔ f = 1 := by
  rw [← le_bot_iff]; rw [f.range_eq_map]; rw [map_le_iff_le_comap]; rw [top_le_iff]; rw [comap_bot]; rw [ker_eq_top_iff]

@[to_additive]
/--
theorem `ker_eq_bot_iff` / 定理 `ker_eq_bot_iff`

English:
theorem ker_eq_bot_iff
  given: (f : G ->* M)
  statement: f.ker = ⊥ ↔ Function.Injective f
  proof: ⟨fun h x y hxy => by rwa [eq_iff, h, mem_bot, inv_mul_eq_one, eq_comm] at hxy, fun h =>
    bot_unique fun _ hx => h (hx.trans f.map_one.symm)⟩

@[to_additive]

中文:
定理 ker_eq_bot_iff
  条件: (f : G ->* M)
  结论: f.ker = ⊥ ↔ 函数.单射 f
  证明: ⟨fun h x y hxy => by rwa [eq_iff, h, mem_bot, inv_mul_eq_one, eq_comm] at hxy, fun h =>
    bot_unique fun _ hx => h (hx.trans f.map_one.symm)⟩

@[to_additive]

Depends on / 依赖: bot_unique, eq_comm, eq_iff, f.map_one.symm, hx.trans, inv_mul_eq_one, map_one, mem_bot
-/
theorem ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Function.Injective f :=
  ⟨fun h x y hxy => by rwa [eq_iff, h, mem_bot, inv_mul_eq_one, eq_comm] at hxy, fun h =>
    bot_unique fun _ hx => h (hx.trans f.map_one.symm)⟩

@[to_additive]
/--
theorem `ker_eq_bot` / 定理 `ker_eq_bot`

English:
theorem ker_eq_bot
  given: (f : G ->* M) (hf : Function.Injective f)
  statement: f.ker = ⊥
  proof: f.ker_eq_bot_iff.mpr hf

中文:
定理 ker_eq_bot
  条件: (f : G ->* M) (hf : 函数.单射 f)
  结论: f.ker = ⊥
  证明: f.ker_eq_bot_iff.mpr hf

Depends on / 依赖: f.ker_eq_bot_iff.mpr, ker_eq_bot_iff
-/
theorem ker_eq_bot (f : G ->* M) (hf : Function.Injective f) : f.ker = ⊥ :=
  f.ker_eq_bot_iff.mpr hf

/-- The kernel of a homomorphism composed with an isomorphism is equal to the kernel of
the homomorphism mapped by the inverse isomorphism. -/
@[to_additive (attr := simp)]
/--
lemma `ker_comp_mulEquiv` / 引理 `ker_comp_mulEquiv`

English:
lemma ker_comp_mulEquiv
  given: {P : Type*} [MulOneClass P] (g : N ->* P) (iso : G ≃* N)
  proof: by
  rw [← comap_ker]; rw [comap_equiv_eq_map_symm]

中文:
引理 ker_comp_mulEquiv
  条件: {P : 类型} [MulOne类 P] (g : N ->* P) (iso : G ≃* N)
  证明: by
  rw [← comap_ker]; rw [comap_equiv_eq_map_symm]

Depends on / 依赖: comap_equiv_eq_map_symm, comap_ker
-/
lemma ker_comp_mulEquiv {P : Type*} [MulOneClass P] (g : N ->* P) (iso : G ≃* N) :
    (g.comp iso).ker = map (iso.symm : N ->* G) g.ker := by
  rw [← comap_ker]; rw [comap_equiv_eq_map_symm]

/-- Composing with an injective homomorphism on the codomain does not change the kernel. -/
@[to_additive]
/--
lemma `ker_comp_of_injective` / 引理 `ker_comp_of_injective`

English:
lemma ker_comp_of_injective
  statement: {P : Type*} [MulOneClass P] (f : G ->* N) (g : N ->* P)
  proof: by
  rw [← comap_ker]; rw [g.ker_eq_bot hg]; rw [comap_bot]

中文:
引理 ker_comp_of_injective
  结论: {P : 类型} [MulOne类 P] (f : G ->* N) (g : N ->* P)
  证明: by
  rw [← comap_ker]; rw [g.ker_eq_bot hg]; rw [comap_bot]

Depends on / 依赖: comap_bot, comap_ker, g.ker_eq_bot, ker_eq_bot
-/
lemma ker_comp_of_injective {P : Type*} [MulOneClass P] (f : G ->* N) (g : N ->* P)
    (hg : Function.Injective g) : (g.comp f).ker = f.ker := by
  rw [← comap_ker]; rw [g.ker_eq_bot hg]; rw [comap_bot]

/-- Composing with an isomorphism on the codomain does not change the kernel. -/
@[to_additive (attr := simp)]
/--
lemma `ker_mulEquiv_comp` / 引理 `ker_mulEquiv_comp`

English:
lemma ker_mulEquiv_comp
  given: {P : Type*} [MulOneClass P] (f : G ->* N) (iso : N ≃* P)
  proof: ker_comp_of_injective f iso.toMonoidHom iso.injective

@[to_additive (attr := simp)]

中文:
引理 ker_mulEquiv_comp
  条件: {P : 类型} [MulOne类 P] (f : G ->* N) (iso : N ≃* P)
  证明: ker_comp_of_injective f iso.toMonoidHom iso.injective

@[to_additive (attr := simp)]

Depends on / 依赖: injective, iso.injective, iso.toMonoidHom, ker_comp_of_injective, toMonoidHom
-/
lemma ker_mulEquiv_comp {P : Type*} [MulOneClass P] (f : G ->* N) (iso : N ≃* P) :
    ((iso : N ->* P).comp f).ker = f.ker :=
  ker_comp_of_injective f iso.toMonoidHom iso.injective

@[to_additive (attr := simp)]
/--
theorem `_root_.Subgroup.ker_subtype` / 定理 `_root_.Subgroup.ker_subtype`

English:
theorem _root_.Subgroup.ker_subtype
  given: (H : Subgroup G)
  statement: H.subtype.ker = ⊥
  proof: H.subtype.ker_eq_bot Subtype.coe_injective

@[to_additive (attr := simp)]

中文:
定理 _root_.子群.ker_subtype
  条件: (H : 子群 G)
  结论: H.subtype.ker = ⊥
  证明: H.subtype.ker_eq_bot Subtype.coe_injective

@[to_additive (attr := simp)]

Depends on / 依赖: H.subtype.ker_eq_bot, Subtype, Subtype.coe_injective, coe_injective, ker_eq_bot, subtype
-/
theorem _root_.Subgroup.ker_subtype (H : Subgroup G) : H.subtype.ker = ⊥ :=
  H.subtype.ker_eq_bot Subtype.coe_injective

@[to_additive (attr := simp)]
/--
theorem `_root_.Subgroup.ker_inclusion` / 定理 `_root_.Subgroup.ker_inclusion`

English:
theorem _root_.Subgroup.ker_inclusion
  given: {H K : Subgroup G} (h : H <= K)
  statement: (inclusion h).ker = ⊥
  proof: (inclusion h).ker_eq_bot (Set.inclusion_injective h)

@[to_additive ker_prod]

中文:
定理 _root_.子群.ker_inclusion
  条件: {H K : 子群 G} (h : H <= K)
  结论: (inclusion h).ker = ⊥
  证明: (inclusion h).ker_eq_bot (Set.inclusion_injective h)

@[to_additive ker_prod]

Depends on / 依赖: Set.inclusion_injective, inclusion, inclusion_injective, ker_eq_bot
-/
theorem _root_.Subgroup.ker_inclusion {H K : Subgroup G} (h : H <= K) : (inclusion h).ker = ⊥ :=
  (inclusion h).ker_eq_bot (Set.inclusion_injective h)

@[to_additive ker_prod]
/--
theorem `ker_prod` / 定理 `ker_prod`

English:
theorem ker_prod
  given: {M N : Type*} [MulOneClass M] [MulOneClass N] (f : G ->* M) (g : G ->* N)
  proof: SetLike.ext fun _ => Prod.mk_eq_one

@[to_additive]

中文:
定理 ker_prod
  条件: {M N : 类型} [MulOne类 M] [MulOne类 N] (f : G ->* M) (g : G ->* N)
  证明: SetLike.ext fun _ => Prod.mk_eq_one

@[to_additive]

Depends on / 依赖: Prod.mk_eq_one, SetLike, SetLike.ext, mk_eq_one
-/
theorem ker_prod {M N : Type*} [MulOneClass M] [MulOneClass N] (f : G ->* M) (g : G ->* N) :
    (f.prod g).ker = f.ker ⊓ g.ker :=
  SetLike.ext fun _ => Prod.mk_eq_one

@[to_additive]
/--
theorem `range_le_ker_iff` / 定理 `range_le_ker_iff`

English:
theorem range_le_ker_iff
  given: (f : G ->* G') (g : G' ->* M)
  statement: f.range <= g.ker ↔ g.comp f = 1
  proof: ⟨fun h => ext fun x => h ⟨x, rfl⟩, by rintro h _ ⟨y, rfl⟩; exact DFunLike.congr_fun h y⟩

@[to_additive]

中文:
定理 range_le_ker_iff
  条件: (f : G ->* G') (g : G' ->* M)
  结论: f.range <= g.ker ↔ g.comp f = 1
  证明: ⟨fun h => ext fun x => h ⟨x, rfl⟩, by rintro h _ ⟨y, rfl⟩; exact DFunLike.congr_fun h y⟩

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
theorem range_le_ker_iff (f : G ->* G') (g : G' ->* M) : f.range <= g.ker ↔ g.comp f = 1 :=
  ⟨fun h => ext fun x => h ⟨x, rfl⟩, by rintro h _ ⟨y, rfl⟩; exact DFunLike.congr_fun h y⟩

@[to_additive]
instance (priority := 100) normal_ker (f : G ->* M) : f.ker.Normal :=
  ⟨fun x hx y => by
    rw [mem_ker]; rw [map_mul]; rw [map_mul]; rw [mem_ker.1 hx]; rw [mul_one]; rw [map_mul_eq_one f (mul_inv_cancel y)]⟩

@[simp]
/--
theorem `coe_toAdditive_ker` / 定理 `coe_toAdditive_ker`

English:
theorem coe_toAdditive_ker
  given: (f : G ->* G')
  proof: rfl

@[simp]

中文:
定理 coe_toAdditive_ker
  条件: (f : G ->* G')
  证明: rfl

@[simp]
-/
theorem coe_toAdditive_ker (f : G ->* G') :
    (MonoidHom.toAdditive f).ker = Subgroup.toAddSubgroup f.ker := rfl

@[simp]
/--
theorem `coe_toMultiplicative_ker` / 定理 `coe_toMultiplicative_ker`

English:
theorem coe_toMultiplicative_ker
  given: {A A' : Type*} [AddGroup A] [AddZeroClass A'] (f : A ->+ A')
  proof: rfl

中文:
定理 coe_toMultiplicative_ker
  条件: {A A' : 类型} [加法群 A] [加法零类 A'] (f : A ->+ A')
  证明: rfl
-/
theorem coe_toMultiplicative_ker {A A' : Type*} [AddGroup A] [AddZeroClass A'] (f : A ->+ A') :
    (AddMonoidHom.toMultiplicative f).ker = AddSubgroup.toSubgroup f.ker := rfl

end Ker

section EqLocus

variable {M : Type*} [Monoid M]

/-- The subgroup of elements `x : G` such that `f x = g x` -/
@[to_additive /-- The additive subgroup of elements `x : G` such that `f x = g x` -/]
/--
Definition of `eqLocus` / `eqLocus` 的定义

English:
definition eqLocus
  signature: (f g : G ->* M)
  body: { eqLocusM f g with inv_mem' := eq_on_inv f g }

@[to_additive (attr := simp)]

中文:
定义 eqLocus
  签名: (f g : G ->* M)
  定义体: { eqLocusM f g with inv_mem' := eq_on_inv f g }

@[to_additive (attr := simp)]

Depends on / 依赖: eqLocusM, eq_on_inv, inv_mem
-/
def eqLocus (f g : G ->* M) : Subgroup G :=
  { eqLocusM f g with inv_mem' := eq_on_inv f g }

@[to_additive (attr := simp)]
/--
theorem `eqLocus_same` / 定理 `eqLocus_same`

English:
theorem eqLocus_same
  given: (f : G ->* N)
  statement: f.eqLocus f = ⊤
  proof: SetLike.ext fun _ => eq_self_iff_true _

中文:
定理 eqLocus_same
  条件: (f : G ->* N)
  结论: f.eqLocus f = ⊤
  证明: SetLike.ext fun _ => eq_self_iff_true _

Depends on / 依赖: SetLike, SetLike.ext, eq_self_iff_true
-/
theorem eqLocus_same (f : G ->* N) : f.eqLocus f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

/-- If two monoid homomorphisms are equal on a set, then they are equal on its subgroup closure. -/
@[to_additive
      /-- If two monoid homomorphisms are equal on a set, then they are equal on its subgroup
      closure. -/]
/--
theorem `eqOn_closure` / 定理 `eqOn_closure`

English:
theorem eqOn_closure
  given: {f g : G ->* M} {s : Set G} (h : Set.EqOn f g s)
  statement: Set.EqOn f g (closure s)
  proof: show closure s <= f.eqLocus g from (closure_le _).2 h

@[to_additive]

中文:
定理 eqOn_closure
  条件: {f g : G ->* M} {s : 集合 G} (h : 集合.EqOn f g s)
  结论: 集合.EqOn f g (closure s)
  证明: show closure s <= f.eqLocus g from (closure_le _).2 h

@[to_additive]

Depends on / 依赖: closure, closure_le, eqLocus, f.eqLocus
-/
theorem eqOn_closure {f g : G ->* M} {s : Set G} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s <= f.eqLocus g from (closure_le _).2 h

@[to_additive]
/--
theorem `eq_of_eqOn_top` / 定理 `eq_of_eqOn_top`

English:
theorem eq_of_eqOn_top
  given: {f g : G ->* M} (h : Set.EqOn f g (⊤ : Subgroup G))
  statement: f = g
  proof: ext fun _x => h trivial

@[to_additive]

中文:
定理 eq_of_eqOn_top
  条件: {f g : G ->* M} (h : 集合.EqOn f g (⊤ : 子群 G))
  结论: f = g
  证明: ext fun _x => h trivial

@[to_additive]
-/
theorem eq_of_eqOn_top {f g : G ->* M} (h : Set.EqOn f g (⊤ : Subgroup G)) : f = g :=
  ext fun _x => h trivial

@[to_additive]
/--
theorem `eq_of_eqOn_dense` / 定理 `eq_of_eqOn_dense`

English:
theorem eq_of_eqOn_dense
  given: {s : Set G} (hs : closure s = ⊤) {f g : G ->* M} (h : s.EqOn f g)
  statement: f = g
  proof: eq_of_eqOn_top hs ▸ eqOn_closure h

中文:
定理 eq_of_eqOn_dense
  条件: {s : 集合 G} (hs : closure s = ⊤) {f g : G ->* M} (h : s.EqOn f g)
  结论: f = g
  证明: eq_of_eqOn_top hs ▸ eqOn_closure h

Depends on / 依赖: eqOn_closure, eq_of_eqOn_top
-/
theorem eq_of_eqOn_dense {s : Set G} (hs : closure s = ⊤) {f g : G ->* M} (h : s.EqOn f g) : f = g :=
eq_of_eqOn_top hs ▸ eqOn_closure h

end EqLocus

end MonoidHom

namespace Subgroup

variable {N : Type*} [Group N] (H : Subgroup G)

@[to_additive]
/--
theorem `map_eq_bot_iff` / 定理 `map_eq_bot_iff`

English:
theorem map_eq_bot_iff
  given: {f : G ->* N}
  statement: H.map f = ⊥ ↔ H <= f.ker
  proof: (gc_map_comap f).l_eq_bot

@[to_additive]

中文:
定理 map_eq_bot_iff
  条件: {f : G ->* N}
  结论: H.map f = ⊥ ↔ H <= f.ker
  证明: (gc_map_comap f).l_eq_bot

@[to_additive]

Depends on / 依赖: gc_map_comap, l_eq_bot
-/
theorem map_eq_bot_iff {f : G ->* N} : H.map f = ⊥ ↔ H <= f.ker :=
  (gc_map_comap f).l_eq_bot

@[to_additive]
/--
theorem `map_eq_bot_iff_of_injective` / 定理 `map_eq_bot_iff_of_injective`

English:
theorem map_eq_bot_iff_of_injective
  given: {f : G ->* N} (hf : Function.Injective f)
  proof: by rw [map_eq_bot_iff, f.ker_eq_bot hf, le_bot_iff]

@[to_additive (attr := simp)]

中文:
定理 map_eq_bot_iff_of_injective
  条件: {f : G ->* N} (hf : 函数.单射 f)
  证明: by rw [map_eq_bot_iff, f.ker_eq_bot hf, le_bot_iff]

@[to_additive (attr := simp)]

Depends on / 依赖: f.ker_eq_bot, ker_eq_bot, le_bot_iff, map_eq_bot_iff
-/
theorem map_eq_bot_iff_of_injective {f : G ->* N} (hf : Function.Injective f) :
    H.map f = ⊥ ↔ H = ⊥ := by rw [map_eq_bot_iff, f.ker_eq_bot hf, le_bot_iff]

@[to_additive (attr := simp)]
/--
theorem `map_ker_self` / 定理 `map_ker_self`

English:
theorem map_ker_self
  given: (f : G ->* N)
  statement: f.ker.map f = ⊥
  proof: by
  rw [map_eq_bot_iff]

中文:
定理 map_ker_self
  条件: (f : G ->* N)
  结论: f.ker.map f = ⊥
  证明: by
  rw [map_eq_bot_iff]

Depends on / 依赖: map_eq_bot_iff
-/
theorem map_ker_self (f : G ->* N) : f.ker.map f = ⊥ := by
  rw [map_eq_bot_iff]

open MonoidHom

variable (f : G ->* N)

@[to_additive]
/--
theorem `map_le_range` / 定理 `map_le_range`

English:
theorem map_le_range
  given: (H : Subgroup G)
  statement: map f H <= f.range
  proof: (range_eq_map f).symm ▸ map_mono le_top

@[to_additive]

中文:
定理 map_le_range
  条件: (H : 子群 G)
  结论: map f H <= f.range
  证明: (range_eq_map f).symm ▸ map_mono le_top

@[to_additive]

Depends on / 依赖: le_top, map_mono, range_eq_map
-/
theorem map_le_range (H : Subgroup G) : map f H <= f.range :=
  (range_eq_map f).symm ▸ map_mono le_top

@[to_additive]
/--
theorem `map_subtype_le` / 定理 `map_subtype_le`

English:
theorem map_subtype_le
  given: {H : Subgroup G} (K : Subgroup H)
  statement: K.map H.subtype <= H
  proof: (K.map_le_range H.subtype).trans_eq H.range_subtype

@[to_additive]

中文:
定理 map_subtype_le
  条件: {H : 子群 G} (K : 子群 H)
  结论: K.map H.subtype <= H
  证明: (K.map_le_range H.subtype).trans_eq H.range_subtype

@[to_additive]

Depends on / 依赖: H.range_subtype, H.subtype, K.map_le_range, map_le_range, range_subtype, subtype, trans_eq
-/
theorem map_subtype_le {H : Subgroup G} (K : Subgroup H) : K.map H.subtype <= H :=
  (K.map_le_range H.subtype).trans_eq H.range_subtype

@[to_additive]
/--
theorem `ker_le_comap` / 定理 `ker_le_comap`

English:
theorem ker_le_comap
  given: (H : Subgroup N)
  statement: f.ker <= comap f H
  proof: comap_bot f ▸ comap_mono bot_le

@[to_additive]

中文:
定理 ker_le_comap
  条件: (H : 子群 N)
  结论: f.ker <= comap f H
  证明: comap_bot f ▸ comap_mono bot_le

@[to_additive]

Depends on / 依赖: bot_le, comap_bot, comap_mono
-/
theorem ker_le_comap (H : Subgroup N) : f.ker <= comap f H :=
  comap_bot f ▸ comap_mono bot_le

@[to_additive]
/--
theorem `map_comap_eq` / 定理 `map_comap_eq`

English:
theorem map_comap_eq
  given: (H : Subgroup N)
  statement: map f (comap f H) = f.range ⊓ H
  proof: SetLike.ext' by
    rw [coe_map]; rw [coe_comap]; rw [Set.image_preimage_eq_inter_range]; rw [coe_inf]; rw [coe_range]; rw [Set.inter_comm]

@[to_additive]

中文:
定理 map_comap_eq
  条件: (H : 子群 N)
  结论: map f (comap f H) = f.range ⊓ H
  证明: SetLike.ext' by
    rw [coe_map]; rw [coe_comap]; rw [Set.image_preimage_eq_inter_range]; rw [coe_inf]; rw [coe_range]; rw [Set.inter_comm]

@[to_additive]

Depends on / 依赖: Set.image_preimage_eq_inter_range, Set.inter_comm, SetLike, SetLike.ext, coe_comap, coe_inf, coe_map, coe_range, image_preimage_eq_inter_range, inter_comm
-/
theorem map_comap_eq (H : Subgroup N) : map f (comap f H) = f.range ⊓ H :=
SetLike.ext' by
    rw [coe_map]; rw [coe_comap]; rw [Set.image_preimage_eq_inter_range]; rw [coe_inf]; rw [coe_range]; rw [Set.inter_comm]

@[to_additive]
/--
theorem `comap_map_eq` / 定理 `comap_map_eq`

English:
theorem comap_map_eq
  given: (H : Subgroup G)
  statement: comap f (map f H) = H ⊔ f.ker
  proof: by
  refine le_antisymm ?_ (sup_le (le_comap_map _ _) (ker_le_comap _ _))
  intro x hx; simp only [mem_map, mem_comap] at hx
  rcases hx with ⟨y, hy, hy'⟩
  rw [← mul_inv_cancel_left y x]
  exact mul_mem_sup hy (by simp [mem_ker, hy'])

@[to_additive]

中文:
定理 comap_map_eq
  条件: (H : 子群 G)
  结论: comap f (map f H) = H ⊔ f.ker
  证明: by
  refine le_antisymm ?_ (sup_le (le_comap_map _ _) (ker_le_comap _ _))
  intro x hx; simp only [mem_map, mem_comap] at hx
  rcases hx with ⟨y, hy, hy'⟩
  rw [← mul_inv_cancel_left y x]
  exact mul_mem_sup hy (by simp [mem_ker, hy'])

@[to_additive]

Depends on / 依赖: ker_le_comap, le_antisymm, le_comap_map, mem_comap, mem_ker, mem_map, mul_inv_cancel_left, mul_mem_sup, sup_le
-/
theorem comap_map_eq (H : Subgroup G) : comap f (map f H) = H ⊔ f.ker := by
  refine le_antisymm ?_ (sup_le (le_comap_map _ _) (ker_le_comap _ _))
  intro x hx; simp only [mem_map, mem_comap] at hx
  rcases hx with ⟨y, hy, hy'⟩
  rw [← mul_inv_cancel_left y x]
  exact mul_mem_sup hy (by simp [mem_ker, hy'])

@[to_additive]
/--
theorem `map_comap_eq_self` / 定理 `map_comap_eq_self`

English:
theorem map_comap_eq_self
  given: {f : G ->* N} {H : Subgroup N} (h : H <= f.range)
  proof: by
  rwa [map_comap_eq, inf_eq_right]

@[to_additive]

中文:
定理 map_comap_eq_self
  条件: {f : G ->* N} {H : 子群 N} (h : H <= f.range)
  证明: by
  rwa [map_comap_eq, inf_eq_right]

@[to_additive]

Depends on / 依赖: inf_eq_right, map_comap_eq
-/
theorem map_comap_eq_self {f : G ->* N} {H : Subgroup N} (h : H <= f.range) :
    map f (comap f H) = H := by
  rwa [map_comap_eq, inf_eq_right]

@[to_additive]
/--
theorem `map_comap_eq_self_of_surjective` / 定理 `map_comap_eq_self_of_surjective`

English:
theorem map_comap_eq_self_of_surjective
  given: {f : G ->* N} (h : Function.Surjective f) (H : Subgroup N)
  proof: map_comap_eq_self (range_eq_top.2 h ▸ le_top)

@[to_additive]

中文:
定理 map_comap_eq_self_of_surjective
  条件: {f : G ->* N} (h : 函数.满射 f) (H : 子群 N)
  证明: map_comap_eq_self (range_eq_top.2 h ▸ le_top)

@[to_additive]

Depends on / 依赖: le_top, map_comap_eq_self, range_eq_top
-/
theorem map_comap_eq_self_of_surjective {f : G ->* N} (h : Function.Surjective f) (H : Subgroup N) :
    map f (comap f H) = H :=
  map_comap_eq_self (range_eq_top.2 h ▸ le_top)

@[to_additive]
/--
theorem `comap_le_comap_of_le_range` / 定理 `comap_le_comap_of_le_range`

English:
theorem comap_le_comap_of_le_range
  given: {f : G ->* N} {K L : Subgroup N} (hf : K <= f.range)
  proof: ⟨(map_comap_eq_self hf).ge.trans ∘ map_le_iff_le_comap.mpr, comap_mono⟩

@[to_additive]

中文:
定理 comap_le_comap_of_le_range
  条件: {f : G ->* N} {K L : 子群 N} (hf : K <= f.range)
  证明: ⟨(map_comap_eq_self hf).ge.trans ∘ map_le_iff_le_comap.mpr, comap_mono⟩

@[to_additive]

Depends on / 依赖: comap_mono, ge.trans, map_comap_eq_self, map_le_iff_le_comap, map_le_iff_le_comap.mpr
-/
theorem comap_le_comap_of_le_range {f : G ->* N} {K L : Subgroup N} (hf : K <= f.range) :
    K.comap f <= L.comap f ↔ K <= L :=
  ⟨(map_comap_eq_self hf).ge.trans ∘ map_le_iff_le_comap.mpr, comap_mono⟩

@[to_additive]
/--
theorem `comap_le_comap_of_surjective` / 定理 `comap_le_comap_of_surjective`

English:
theorem comap_le_comap_of_surjective
  given: {f : G ->* N} {K L : Subgroup N} (hf : Function.Surjective f)
  proof: comap_le_comap_of_le_range (range_eq_top.2 hf ▸ le_top)

@[to_additive]

中文:
定理 comap_le_comap_of_surjective
  条件: {f : G ->* N} {K L : 子群 N} (hf : 函数.满射 f)
  证明: comap_le_comap_of_le_range (range_eq_top.2 hf ▸ le_top)

@[to_additive]

Depends on / 依赖: comap_le_comap_of_le_range, le_top, range_eq_top
-/
theorem comap_le_comap_of_surjective {f : G ->* N} {K L : Subgroup N} (hf : Function.Surjective f) :
    K.comap f <= L.comap f ↔ K <= L :=
  comap_le_comap_of_le_range (range_eq_top.2 hf ▸ le_top)

@[to_additive]
/--
theorem `comap_lt_comap_of_surjective` / 定理 `comap_lt_comap_of_surjective`

English:
theorem comap_lt_comap_of_surjective
  given: {f : G ->* N} {K L : Subgroup N} (hf : Function.Surjective f)
  proof: by simp_rw [lt_iff_le_not_ge, comap_le_comap_of_surjective hf]

@[to_additive]

中文:
定理 comap_lt_comap_of_surjective
  条件: {f : G ->* N} {K L : 子群 N} (hf : 函数.满射 f)
  证明: by simp_rw [lt_iff_le_not_ge, comap_le_comap_of_surjective hf]

@[to_additive]

Depends on / 依赖: comap_le_comap_of_surjective, lt_iff_le_not_ge, simp_rw
-/
theorem comap_lt_comap_of_surjective {f : G ->* N} {K L : Subgroup N} (hf : Function.Surjective f) :
    K.comap f < L.comap f ↔ K < L := by simp_rw [lt_iff_le_not_ge, comap_le_comap_of_surjective hf]

@[to_additive]
/--
theorem `comap_injective` / 定理 `comap_injective`

English:
theorem comap_injective
  given: {f : G ->* N} (h : Function.Surjective f)
  statement: Function.Injective (comap f)
  proof: fun K L => by simp only [le_antisymm_iff, comap_le_comap_of_surjective h, imp_self]

@[to_additive (attr := simp)]

中文:
定理 comap_injective
  条件: {f : G ->* N} (h : 函数.满射 f)
  结论: 函数.单射 (comap f)
  证明: fun K L => by simp only [le_antisymm_iff, comap_le_comap_of_surjective h, imp_self]

@[to_additive (attr := simp)]

Depends on / 依赖: comap_le_comap_of_surjective, imp_self, le_antisymm_iff
-/
theorem comap_injective {f : G ->* N} (h : Function.Surjective f) : Function.Injective (comap f) :=
  fun K L => by simp only [le_antisymm_iff, comap_le_comap_of_surjective h, imp_self]

@[to_additive (attr := simp)]
/--
theorem `comap_eq_ker` / 定理 `comap_eq_ker`

English:
theorem comap_eq_ker
  given: {f : G ->* N} {H : Subgroup N}
  statement: H.comap f = f.ker ↔ Disjoint H f.range
  proof: by
  rw [← H.ker_le_comap f |>.ge_iff_eq']; rw [← map_eq_bot_iff]; rw [map_comap_eq]; rw [disjoint_iff]; rw [inf_comm]

@[to_additive]

中文:
定理 comap_eq_ker
  条件: {f : G ->* N} {H : 子群 N}
  结论: H.comap f = f.ker ↔ Disjoint H f.range
  证明: by
  rw [← H.ker_le_comap f |>.ge_iff_eq']; rw [← map_eq_bot_iff]; rw [map_comap_eq]; rw [disjoint_iff]; rw [inf_comm]

@[to_additive]

Depends on / 依赖: H.ker_le_comap, disjoint_iff, ge_iff_eq, inf_comm, ker_le_comap, map_comap_eq, map_eq_bot_iff
-/
theorem comap_eq_ker {f : G ->* N} {H : Subgroup N} : H.comap f = f.ker ↔ Disjoint H f.range := by
  rw [← H.ker_le_comap f |>.ge_iff_eq']; rw [← map_eq_bot_iff]; rw [map_comap_eq]; rw [disjoint_iff]; rw [inf_comm]

@[to_additive]
/--
theorem `comap_eq_ker_of_surjective` / 定理 `comap_eq_ker_of_surjective`

English:
theorem comap_eq_ker_of_surjective
  given: {f : G ->* N} (hf : Surjective f) {H : Subgroup N}
  proof: by
  rw [comap_eq_ker]; rw [f.range_eq_top_of_surjective hf]; rw [disjoint_top]

@[to_additive]

中文:
定理 comap_eq_ker_of_surjective
  条件: {f : G ->* N} (hf : 满射 f) {H : 子群 N}
  证明: by
  rw [comap_eq_ker]; rw [f.range_eq_top_of_surjective hf]; rw [disjoint_top]

@[to_additive]

Depends on / 依赖: comap_eq_ker, disjoint_top, f.range_eq_top_of_surjective, range_eq_top_of_surjective
-/
theorem comap_eq_ker_of_surjective {f : G ->* N} (hf : Surjective f) {H : Subgroup N} :
    H.comap f = f.ker ↔ H = ⊥ := by
  rw [comap_eq_ker]; rw [f.range_eq_top_of_surjective hf]; rw [disjoint_top]

@[to_additive]
/--
theorem `comap_map_eq_self` / 定理 `comap_map_eq_self`

English:
theorem comap_map_eq_self
  given: {f : G ->* N} {H : Subgroup G} (h : f.ker <= H)
  proof: by
  rwa [comap_map_eq, sup_eq_left]

@[to_additive]

中文:
定理 comap_map_eq_self
  条件: {f : G ->* N} {H : 子群 G} (h : f.ker <= H)
  证明: by
  rwa [comap_map_eq, sup_eq_left]

@[to_additive]

Depends on / 依赖: comap_map_eq, sup_eq_left
-/
theorem comap_map_eq_self {f : G ->* N} {H : Subgroup G} (h : f.ker <= H) :
    comap f (map f H) = H := by
  rwa [comap_map_eq, sup_eq_left]

@[to_additive]
/--
theorem `comap_map_eq_self_of_injective` / 定理 `comap_map_eq_self_of_injective`

English:
theorem comap_map_eq_self_of_injective
  given: {f : G ->* N} (h : Function.Injective f) (H : Subgroup G)
  proof: comap_map_eq_self ((ker_eq_bot _ h).symm ▸ bot_le)

@[to_additive]

中文:
定理 comap_map_eq_self_of_injective
  条件: {f : G ->* N} (h : 函数.单射 f) (H : 子群 G)
  证明: comap_map_eq_self ((ker_eq_bot _ h).symm ▸ bot_le)

@[to_additive]

Depends on / 依赖: bot_le, comap_map_eq_self, ker_eq_bot
-/
theorem comap_map_eq_self_of_injective {f : G ->* N} (h : Function.Injective f) (H : Subgroup G) :
    comap f (map f H) = H :=
  comap_map_eq_self ((ker_eq_bot _ h).symm ▸ bot_le)

@[to_additive]
/--
theorem `map_le_map_iff` / 定理 `map_le_map_iff`

English:
theorem map_le_map_iff
  given: {f : G ->* N} {H K : Subgroup G}
  statement: H.map f <= K.map f ↔ H <= K ⊔ f.ker
  proof: by
  rw [map_le_iff_le_comap]; rw [comap_map_eq]

@[to_additive]

中文:
定理 map_le_map_iff
  条件: {f : G ->* N} {H K : 子群 G}
  结论: H.map f <= K.map f ↔ H <= K ⊔ f.ker
  证明: by
  rw [map_le_iff_le_comap]; rw [comap_map_eq]

@[to_additive]

Depends on / 依赖: comap_map_eq, map_le_iff_le_comap
-/
theorem map_le_map_iff {f : G ->* N} {H K : Subgroup G} : H.map f <= K.map f ↔ H <= K ⊔ f.ker := by
  rw [map_le_iff_le_comap]; rw [comap_map_eq]

@[to_additive]
/--
theorem `map_le_map_iff'` / 定理 `map_le_map_iff'`

English:
theorem map_le_map_iff'
  given: {f : G ->* N} {H K : Subgroup G}
  proof: by
  simp only [map_le_map_iff, sup_le_iff, le_sup_right, and_true]

@[to_additive]

中文:
定理 map_le_map_iff'
  条件: {f : G ->* N} {H K : 子群 G}
  证明: by
  simp only [map_le_map_iff, sup_le_iff, le_sup_right, and_true]

@[to_additive]

Depends on / 依赖: and_true, le_sup_right, map_le_map_iff, sup_le_iff
-/
theorem map_le_map_iff' {f : G ->* N} {H K : Subgroup G} :
    H.map f <= K.map f ↔ H ⊔ f.ker <= K ⊔ f.ker := by
  simp only [map_le_map_iff, sup_le_iff, le_sup_right, and_true]

@[to_additive]
/--
theorem `map_eq_map_iff` / 定理 `map_eq_map_iff`

English:
theorem map_eq_map_iff
  given: {f : G ->* N} {H K : Subgroup G}
  proof: by simp only [le_antisymm_iff, map_le_map_iff']

@[to_additive]

中文:
定理 map_eq_map_iff
  条件: {f : G ->* N} {H K : 子群 G}
  证明: by simp only [le_antisymm_iff, map_le_map_iff']

@[to_additive]

Depends on / 依赖: le_antisymm_iff, map_le_map_iff
-/
theorem map_eq_map_iff {f : G ->* N} {H K : Subgroup G} :
    H.map f = K.map f ↔ H ⊔ f.ker = K ⊔ f.ker := by simp only [le_antisymm_iff, map_le_map_iff']

@[to_additive]
/--
theorem `map_eq_range_iff` / 定理 `map_eq_range_iff`

English:
theorem map_eq_range_iff
  given: {f : G ->* N} {H : Subgroup G}
  proof: by
  rw [f.range_eq_map]; rw [map_eq_map_iff]; rw [codisjoint_iff]; rw [top_sup_eq]

@[to_additive]

中文:
定理 map_eq_range_iff
  条件: {f : G ->* N} {H : 子群 G}
  证明: by
  rw [f.range_eq_map]; rw [map_eq_map_iff]; rw [codisjoint_iff]; rw [top_sup_eq]

@[to_additive]

Depends on / 依赖: codisjoint_iff, f.range_eq_map, map_eq_map_iff, range_eq_map, top_sup_eq
-/
theorem map_eq_range_iff {f : G ->* N} {H : Subgroup G} :
    H.map f = f.range ↔ Codisjoint H f.ker := by
  rw [f.range_eq_map]; rw [map_eq_map_iff]; rw [codisjoint_iff]; rw [top_sup_eq]

@[to_additive]
/--
theorem `map_le_map_iff_of_injective` / 定理 `map_le_map_iff_of_injective`

English:
theorem map_le_map_iff_of_injective
  given: {f : G ->* N} (hf : Function.Injective f) {H K : Subgroup G}
  proof: by rw [map_le_iff_le_comap, comap_map_eq_self_of_injective hf]

@[to_additive (attr := simp)]

中文:
定理 map_le_map_iff_of_injective
  条件: {f : G ->* N} (hf : 函数.单射 f) {H K : 子群 G}
  证明: by rw [map_le_iff_le_comap, comap_map_eq_self_of_injective hf]

@[to_additive (attr := simp)]

Depends on / 依赖: comap_map_eq_self_of_injective, map_le_iff_le_comap
-/
theorem map_le_map_iff_of_injective {f : G ->* N} (hf : Function.Injective f) {H K : Subgroup G} :
    H.map f <= K.map f ↔ H <= K := by rw [map_le_iff_le_comap, comap_map_eq_self_of_injective hf]

@[to_additive (attr := simp)]
/--
theorem `map_subtype_le_map_subtype` / 定理 `map_subtype_le_map_subtype`

English:
theorem map_subtype_le_map_subtype
  given: {G' : Subgroup G} {H K : Subgroup G'}
  proof: map_le_map_iff_of_injective G'.subtype_injective

中文:
定理 map_subtype_le_map_subtype
  条件: {G' : 子群 G} {H K : 子群 G'}
  证明: map_le_map_iff_of_injective G'.subtype_injective

Depends on / 依赖: map_le_map_iff_of_injective, subtype_injective
-/
theorem map_subtype_le_map_subtype {G' : Subgroup G} {H K : Subgroup G'} :
    H.map G'.subtype <= K.map G'.subtype ↔ H <= K :=
  map_le_map_iff_of_injective G'.subtype_injective

set_option backward.isDefEq.respectTransparency false in
/-- Subgroups of the subgroup `H` are considered as subgroups that are less than or equal to
`H`. -/
@[to_additive (attr := simps apply_coe) /-- Additive subgroups of the subgroup `H` are considered as
additive subgroups that are less than or equal to `H`. -/]
/--
Definition of `MapSubtype.orderIso` / `MapSubtype.orderIso` 的定义

English:
definition MapSubtype.orderIso
  signature: (H : Subgroup G)
  body: ⟨H'.map H.subtype, map_subtype_le H'⟩
  invFun sH' := sH'.1.subgroupOf H
  left_inv H' := comap_map_eq_self_of_injective H.subtype_injective H'
  right_inv sH' := Subtype.ext (map_subgroupOf_eq_of_le sH'.2)
  map_rel_iff' := by simp

@[to_additive (attr := simp)]

中文:
定义 MapSubtype.orderIso
  签名: (H : 子群 G)
  定义体: ⟨H'.map H.subtype, map_subtype_le H'⟩
  invFun sH' := sH'.1.subgroupOf H
  left_inv H' := comap_map_eq_self_of_injective H.subtype_injective H'
  right_inv sH' := Subtype.ext (map_subgroupOf_eq_of_le sH'.2)
  map_rel_iff' := by simp

@[to_additive (attr := simp)]

Depends on / 依赖: H.subtype, map_subtype_le, subtype
-/
def MapSubtype.orderIso (H : Subgroup G) : Subgroup ↥H ≃o { H' : Subgroup G // H' <= H } where
  toFun H' := ⟨H'.map H.subtype, map_subtype_le H'⟩
  invFun sH' := sH'.1.subgroupOf H
  left_inv H' := comap_map_eq_self_of_injective H.subtype_injective H'
  right_inv sH' := Subtype.ext (map_subgroupOf_eq_of_le sH'.2)
  map_rel_iff' := by simp

@[to_additive (attr := simp)]
/--
lemma `MapSubtype.orderIso_symm_apply` / 引理 `MapSubtype.orderIso_symm_apply`

English:
lemma MapSubtype.orderIso_symm_apply
  given: (H : Subgroup G) (sH' : { H' : Subgroup G // H' <= H })
  proof: rfl

@[to_additive]

中文:
引理 MapSubtype.orderIso_symm_apply
  条件: (H : 子群 G) (sH' : { H' : 子群 G // H' <= H })
  证明: rfl

@[to_additive]
-/
lemma MapSubtype.orderIso_symm_apply (H : Subgroup G) (sH' : { H' : Subgroup G // H' <= H }) :
    (MapSubtype.orderIso H).symm sH' = sH'.1.subgroupOf H :=
  rfl

@[to_additive]
/--
lemma `«forall»` / 引理 `«forall»`

English:
lemma «forall»
  given: {H : Subgroup G} {P : Subgroup H -> Prop}
  proof: by
  simp [(MapSubtype.orderIso H).forall_congr_left]

@[to_additive]

中文:
引理 «对任意»
  条件: {H : 子群 G} {P : 子群 H -> 命题}
  证明: by
  simp [(MapSubtype.orderIso H).forall_congr_left]

@[to_additive]
-/
protected lemma «forall» {H : Subgroup G} {P : Subgroup H -> Prop} :
    (forall H' : Subgroup H, P H') ↔ (forall H' <= H, P (H'.subgroupOf H)) := by
  simp [(MapSubtype.orderIso H).forall_congr_left]

@[to_additive]
/--
theorem `map_lt_map_iff_of_injective` / 定理 `map_lt_map_iff_of_injective`

English:
theorem map_lt_map_iff_of_injective
  given: {f : G ->* N} (hf : Function.Injective f) {H K : Subgroup G}
  proof: lt_iff_lt_of_le_iff_le' (map_le_map_iff_of_injective hf) (map_le_map_iff_of_injective hf)

@[to_additive (attr := simp)]

中文:
定理 map_lt_map_iff_of_injective
  条件: {f : G ->* N} (hf : 函数.单射 f) {H K : 子群 G}
  证明: lt_iff_lt_of_le_iff_le' (map_le_map_iff_of_injective hf) (map_le_map_iff_of_injective hf)

@[to_additive (attr := simp)]

Depends on / 依赖: lt_iff_lt_of_le_iff_le, map_le_map_iff_of_injective
-/
theorem map_lt_map_iff_of_injective {f : G ->* N} (hf : Function.Injective f) {H K : Subgroup G} :
    H.map f < K.map f ↔ H < K :=
  lt_iff_lt_of_le_iff_le' (map_le_map_iff_of_injective hf) (map_le_map_iff_of_injective hf)

@[to_additive (attr := simp)]
/--
theorem `map_subtype_lt_map_subtype` / 定理 `map_subtype_lt_map_subtype`

English:
theorem map_subtype_lt_map_subtype
  given: {G' : Subgroup G} {H K : Subgroup G'}
  proof: map_lt_map_iff_of_injective G'.subtype_injective

@[to_additive]

中文:
定理 map_subtype_lt_map_subtype
  条件: {G' : 子群 G} {H K : 子群 G'}
  证明: map_lt_map_iff_of_injective G'.subtype_injective

@[to_additive]

Depends on / 依赖: map_lt_map_iff_of_injective, subtype_injective
-/
theorem map_subtype_lt_map_subtype {G' : Subgroup G} {H K : Subgroup G'} :
    H.map G'.subtype < K.map G'.subtype ↔ H < K :=
  map_lt_map_iff_of_injective G'.subtype_injective

@[to_additive]
/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : G ->* N} (h : Function.Injective f)
  statement: Function.Injective (map f)
  proof: Function.LeftInverse.injective comap_map_eq_self_of_injective h

@[to_additive]

中文:
定理 map_injective
  条件: {f : G ->* N} (h : 函数.单射 f)
  结论: 函数.单射 (map f)
  证明: Function.LeftInverse.injective comap_map_eq_self_of_injective h

@[to_additive]

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, comap_map_eq_self_of_injective, injective
-/
theorem map_injective {f : G ->* N} (h : Function.Injective f) : Function.Injective (map f) :=
Function.LeftInverse.injective comap_map_eq_self_of_injective h

@[to_additive]
/--
theorem `map_subtype_inj` / 定理 `map_subtype_inj`

English:
theorem map_subtype_inj
  given: {H : Subgroup G} {K L : Subgroup H}
  proof: (map_injective H.subtype_injective).eq_iff

中文:
定理 map_subtype_inj
  条件: {H : 子群 G} {K L : 子群 H}
  证明: (map_injective H.subtype_injective).eq_iff

Depends on / 依赖: H.subtype_injective, eq_iff, map_injective, subtype_injective
-/
theorem map_subtype_inj {H : Subgroup G} {K L : Subgroup H} :
    K.map H.subtype = L.map H.subtype ↔ K = L :=
  (map_injective H.subtype_injective).eq_iff

/-- Given `f(A) = f(B)`, `ker f ≤ A`, and `ker f ≤ B`, deduce that `A = B`. -/
@[to_additive /-- Given `f(A) = f(B)`, `ker f ≤ A`, and `ker f ≤ B`, deduce that `A = B`. -/]
/--
theorem `map_injective_of_ker_le` / 定理 `map_injective_of_ker_le`

English:
theorem map_injective_of_ker_le
  statement: {H K : Subgroup G} (hH : f.ker <= H) (hK : f.ker <= K)
  proof: by
  apply_fun comap f at hf
  rwa [comap_map_eq, comap_map_eq, sup_of_le_left hH, sup_of_le_left hK] at hf

@[to_additive]

中文:
定理 map_injective_of_ker_le
  结论: {H K : 子群 G} (hH : f.ker <= H) (hK : f.ker <= K)
  证明: by
  apply_fun comap f at hf
  rwa [comap_map_eq, comap_map_eq, sup_of_le_left hH, sup_of_le_left hK] at hf

@[to_additive]

Depends on / 依赖: apply_fun, comap_map_eq, sup_of_le_left
-/
theorem map_injective_of_ker_le {H K : Subgroup G} (hH : f.ker <= H) (hK : f.ker <= K)
    (hf : map f H = map f K) : H = K := by
  apply_fun comap f at hf
  rwa [comap_map_eq, comap_map_eq, sup_of_le_left hH, sup_of_le_left hK] at hf

@[to_additive]
/--
theorem `ker_subgroupMap` / 定理 `ker_subgroupMap`

English:
theorem ker_subgroupMap
  statement: (f.subgroupMap H).ker = f.ker.subgroupOf H
  proof: ext fun _ => Subtype.ext_iff

@[to_additive]

中文:
定理 ker_subgroupMap
  结论: (f.subgroupMap H).ker = f.ker.subgroupOf H
  证明: ext fun _ => Subtype.ext_iff

@[to_additive]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem ker_subgroupMap : (f.subgroupMap H).ker = f.ker.subgroupOf H :=
  ext fun _ => Subtype.ext_iff

@[to_additive]
/--
theorem `closure_preimage_eq_top` / 定理 `closure_preimage_eq_top`

English:
theorem closure_preimage_eq_top
  given: (s : Set G)
  statement: closure ((closure s).subtype ⁻¹' s) = ⊤
  proof: by
  simp

@[to_additive]

中文:
定理 closure_preimage_eq_top
  条件: (s : 集合 G)
  结论: closure ((closure s).subtype ⁻¹' s) = ⊤
  证明: by
  simp

@[to_additive]
-/
theorem closure_preimage_eq_top (s : Set G) : closure ((closure s).subtype ⁻¹' s) = ⊤ := by
  simp

@[to_additive]
/--
theorem `comap_sup_eq_of_le_range` / 定理 `comap_sup_eq_of_le_range`

English:
theorem comap_sup_eq_of_le_range
  given: {H K : Subgroup N} (hH : H <= f.range) (hK : K <= f.range)
  proof: map_injective_of_ker_le f ((ker_le_comap f H).trans le_sup_left) (ker_le_comap f (H ⊔ K))
    (by
      rw [map_comap_eq]; rw [map_sup]; rw [map_comap_eq]; rw [map_comap_eq]; rw [inf_eq_right.mpr hH]; rw [inf_eq_right.mpr hK]; rw [inf_eq_right.mpr (sup_le hH hK)])

@[to_additive]

中文:
定理 comap_sup_eq_of_le_range
  条件: {H K : 子群 N} (hH : H <= f.range) (hK : K <= f.range)
  证明: map_injective_of_ker_le f ((ker_le_comap f H).trans le_sup_left) (ker_le_comap f (H ⊔ K))
    (by
      rw [map_comap_eq]; rw [map_sup]; rw [map_comap_eq]; rw [map_comap_eq]; rw [inf_eq_right.mpr hH]; rw [inf_eq_right.mpr hK]; rw [inf_eq_right.mpr (sup_le hH hK)])

@[to_additive]

Depends on / 依赖: inf_eq_right, inf_eq_right.mpr, ker_le_comap, le_sup_left, map_comap_eq, map_injective_of_ker_le, map_sup, sup_le
-/
theorem comap_sup_eq_of_le_range {H K : Subgroup N} (hH : H <= f.range) (hK : K <= f.range) :
    comap f H ⊔ comap f K = comap f (H ⊔ K) :=
  map_injective_of_ker_le f ((ker_le_comap f H).trans le_sup_left) (ker_le_comap f (H ⊔ K))
    (by
      rw [map_comap_eq]; rw [map_sup]; rw [map_comap_eq]; rw [map_comap_eq]; rw [inf_eq_right.mpr hH]; rw [inf_eq_right.mpr hK]; rw [inf_eq_right.mpr (sup_le hH hK)])

@[to_additive]
/--
theorem `comap_sup_eq` / 定理 `comap_sup_eq`

English:
theorem comap_sup_eq
  given: (H K : Subgroup N) (hf : Function.Surjective f)
  proof: comap_sup_eq_of_le_range f (range_eq_top.2 hf ▸ le_top) (range_eq_top.2 hf ▸ le_top)

@[to_additive]

中文:
定理 comap_sup_eq
  条件: (H K : 子群 N) (hf : 函数.满射 f)
  证明: comap_sup_eq_of_le_range f (range_eq_top.2 hf ▸ le_top) (range_eq_top.2 hf ▸ le_top)

@[to_additive]

Depends on / 依赖: comap_sup_eq_of_le_range, le_top, range_eq_top
-/
theorem comap_sup_eq (H K : Subgroup N) (hf : Function.Surjective f) :
    comap f H ⊔ comap f K = comap f (H ⊔ K) :=
  comap_sup_eq_of_le_range f (range_eq_top.2 hf ▸ le_top) (range_eq_top.2 hf ▸ le_top)

@[to_additive]
/--
theorem `subgroupOf_sup` / 定理 `subgroupOf_sup`

English:
theorem subgroupOf_sup
  given: {A A' B : Subgroup G} (hA : A <= B) (hA' : A' <= B)
  proof: by
  refine
    map_injective_of_ker_le B.subtype (ker_le_comap _ _)
      (le_trans (ker_le_comap B.subtype _) le_sup_left) ?_
  simp only [subgroupOf, map_comap_eq, map_sup, range_subtype]
  rw [inf_of_le_right (sup_le hA hA')]; rw [inf_of_le_right hA']; rw [inf_of_le_right hA]

@[to_additive]

中文:
定理 subgroupOf_sup
  条件: {A A' B : 子群 G} (hA : A <= B) (hA' : A' <= B)
  证明: by
  refine
    map_injective_of_ker_le B.subtype (ker_le_comap _ _)
      (le_trans (ker_le_comap B.subtype _) le_sup_left) ?_
  simp only [subgroupOf, map_comap_eq, map_sup, range_subtype]
  rw [inf_of_le_right (sup_le hA hA')]; rw [inf_of_le_right hA']; rw [inf_of_le_right hA]

@[to_additive]

Depends on / 依赖: B.subtype, inf_of_le_right, ker_le_comap, le_sup_left, le_trans, map_comap_eq, map_injective_of_ker_le, map_sup, range_subtype, subgroupOf, subtype, sup_le
-/
theorem subgroupOf_sup {A A' B : Subgroup G} (hA : A <= B) (hA' : A' <= B) :
    (A ⊔ A').subgroupOf B = A.subgroupOf B ⊔ A'.subgroupOf B := by
  refine
    map_injective_of_ker_le B.subtype (ker_le_comap _ _)
      (le_trans (ker_le_comap B.subtype _) le_sup_left) ?_
  simp only [subgroupOf, map_comap_eq, map_sup, range_subtype]
  rw [inf_of_le_right (sup_le hA hA')]; rw [inf_of_le_right hA']; rw [inf_of_le_right hA]

@[to_additive]
/--
theorem `codisjoint_subgroupOf_sup` / 定理 `codisjoint_subgroupOf_sup`

English:
theorem codisjoint_subgroupOf_sup
  given: (H K : Subgroup G)
  proof: by
  rw [codisjoint_iff]; rw [← subgroupOf_sup]; rw [subgroupOf_self]
  exacts [le_sup_left, le_sup_right]

中文:
定理 codisjoint_subgroupOf_sup
  条件: (H K : 子群 G)
  证明: by
  rw [codisjoint_iff]; rw [← subgroupOf_sup]; rw [subgroupOf_self]
  exacts [le_sup_left, le_sup_right]

Depends on / 依赖: codisjoint_iff, exacts, le_sup_left, le_sup_right, subgroupOf_self, subgroupOf_sup
-/
theorem codisjoint_subgroupOf_sup (H K : Subgroup G) :
    Codisjoint (H.subgroupOf (H ⊔ K)) (K.subgroupOf (H ⊔ K)) := by
  rw [codisjoint_iff]; rw [← subgroupOf_sup]; rw [subgroupOf_self]
  exacts [le_sup_left, le_sup_right]

variable {M : Type*} [CommGroup M]

@[to_additive]
/--
lemma `subgroupOf_map_powMonoidHom_eq_range` / 引理 `subgroupOf_map_powMonoidHom_eq_range`

English:
lemma subgroupOf_map_powMonoidHom_eq_range
  given: (S : Subgroup M) (n : Nat)
  proof: by
  ext : 1
  simp [mem_subgroupOf]
  grind

中文:
引理 subgroupOf_map_powMonoidHom_eq_range
  条件: (S : 子群 M) (n : 自然数)
  证明: by
  ext : 1
  simp [mem_subgroupOf]
  grind

Depends on / 依赖: mem_subgroupOf
-/
lemma subgroupOf_map_powMonoidHom_eq_range (S : Subgroup M) (n : Nat) :
    (map (powMonoidHom n) S).subgroupOf S = (powMonoidHom n).range := by
  ext : 1
  simp [mem_subgroupOf]
  grind

end Subgroup

namespace MulEquiv

@[to_additive (attr := simp)]
/--
lemma `range_eq_top` / 引理 `range_eq_top`

English:
lemma range_eq_top
  given: (e : G ≃* G')
  statement: (e : G ->* G').range = ⊤
  proof: MonoidHom.range_eq_top.mpr e.surjective

中文:
引理 range_eq_top
  条件: (e : G ≃* G')
  结论: (e : G ->* G').range = ⊤
  证明: MonoidHom.range_eq_top.mpr e.surjective

Depends on / 依赖: MonoidHom, MonoidHom.range_eq_top.mpr, e.surjective, range_eq_top, surjective
-/
lemma range_eq_top (e : G ≃* G') : (e : G ->* G').range = ⊤ :=
  MonoidHom.range_eq_top.mpr e.surjective

variable {M N : Type*} [CommGroup M] [CommGroup N]

open MonoidHom in
@[to_additive]
/--
lemma `map_range_powMonoidHom` / 引理 `map_range_powMonoidHom`

English:
lemma map_range_powMonoidHom
  given: (e : M ≃* N) (n : Nat)
  proof: by
  have H : (e : M ->* N).comp (powMonoidHom n) = (powMonoidHom n).comp e := by ext : 1; simp
  rw [map_range]; rw [H]; rw [range_comp]; rw [e.range_eq_top]; rw [← range_eq_map]

中文:
引理 map_range_powMonoidHom
  条件: (e : M ≃* N) (n : 自然数)
  证明: by
  have H : (e : M ->* N).comp (powMonoidHom n) = (powMonoidHom n).comp e := by ext : 1; simp
  rw [map_range]; rw [H]; rw [range_comp]; rw [e.range_eq_top]; rw [← range_eq_map]

Depends on / 依赖: e.range_eq_top, map_range, powMonoidHom, range.map, range_comp, range_eq_map, range_eq_top
-/
lemma map_range_powMonoidHom (e : M ≃* N) (n : Nat) :
    (powMonoidHom (α := M) n).range.map e = (powMonoidHom (α := N) n).range := by
  have H : (e : M ->* N).comp (powMonoidHom n) = (powMonoidHom n).comp e := by ext : 1; simp
  rw [map_range]; rw [H]; rw [range_comp]; rw [e.range_eq_top]; rw [← range_eq_map]

end MulEquiv
