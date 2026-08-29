/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli, Junyan Xu
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.CategoryTheory.Groupoid.VertexGroup
public import Mathlib.CategoryTheory.Groupoid.Basic
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Data.Set.Lattice

/-!
# Subgroupoid

This file defines subgroupoids as `structure`s containing the subsets of arrows and their
stability under composition and inversion.
Also defined are:

* containment of subgroupoids is a complete lattice;
* images and preimages of subgroupoids under a functor;
* the notion of normality of subgroupoids and its stability under intersection and preimage;
* compatibility of the above with `CategoryTheory.Groupoid.vertexGroup`.


## Main definitions

Given a type `C` with associated `groupoid C` instance.

* `CategoryTheory.Subgroupoid C` is the type of subgroupoids of `C`
* `CategoryTheory.Subgroupoid.IsNormal` is the property that the subgroupoid is stable under
  conjugation by arbitrary arrows, _and_ that all identity arrows are contained in the subgroupoid.
* `CategoryTheory.Subgroupoid.comap` is the "preimage" map of subgroupoids along a functor.
* `CategoryTheory.Subgroupoid.map` is the "image" map of subgroupoids along a functor _injective on
  objects_.
* `CategoryTheory.Subgroupoid.vertexSubgroup` is the subgroup of the *vertex group* at a given
  vertex `v`, assuming `v` is contained in the `CategoryTheory.Subgroupoid` (meaning, by definition,
  that the arrow `𝟙 v` is contained in the subgroupoid).

## Implementation details

The structure of this file is copied from/inspired by `Mathlib/Algebra/Group/Subgroup/Basic.lean`
and `Mathlib/Combinatorics/SimpleGraph/Subgraph.lean`.

## TODO

* Equivalent inductive characterization of generated (normal) subgroupoids.
* Characterization of normal subgroupoids as kernels.
* Prove that `CategoryTheory.Subgroupoid.full` and `CategoryTheory.Subgroupoid.disconnect` preserve
  intersections (and `CategoryTheory.Subgroupoid.disconnect` also unions)

## Tags

category theory, groupoid, subgroupoid
-/

@[expose] public section


namespace CategoryTheory

open Set Groupoid

universe u v

variable {C : Type u} [Groupoid C]

/-- A subgroupoid of `C` consists of a choice of arrows for each pair of vertices, closed
under composition and inverses.
-/
@[ext]
/--
Definition of `Subgroupoid` / `Subgroupoid` 的定义

English:
structure Subgroupoid
  parameters: (C : Type u) [Groupoid C]
  axioms and operations (3):
    - arrows : forall c d : C, Set (c ⟶ d)
    - inv : forall {c d} {p : c ⟶ d}, p in arrows c d -> Groupoid.inv p in arrows d c
    - mul : forall {c d e} {p}, p in arrows c d -> forall {q}, q in arrows d e -> p ≫ q in arrows c e

中文:
结构 Subgroupoid
  参数: (C : 类型u) [Groupoid C]
  公理与运算 (3 个):
    - arrows : 对任意 c d : C, Set (c ⟶ d)
    - inv : 对任意 {c d} {p : c ⟶ d}, p in arrows c d -> Groupoid.inv p in arrows d c
    - mul : 对任意 {c d e} {p}, p in arrows c d -> 对任意 {q}, q in arrows d e -> p ≫ q in arrows c e
-/
structure Subgroupoid (C : Type u) [Groupoid C] where
  /-- The arrow choice for each pair of vertices -/
  arrows : forall c d : C, Set (c ⟶ d)
  protected inv : forall {c d} {p : c ⟶ d}, p in arrows c d -> Groupoid.inv p in arrows d c
  protected mul : forall {c d e} {p}, p in arrows c d -> forall {q}, q in arrows d e -> p ≫ q in arrows c e

namespace Subgroupoid

variable (S : Subgroupoid C)

/--
theorem `inv_mem_iff` / 定理 `inv_mem_iff`

English:
theorem inv_mem_iff
  given: {c d : C} (f : c ⟶ d)
  proof: by
  constructor
  · intro h
    simpa only [inv_eq_inv, IsIso.inv_inv] using S.inv h
  · apply S.inv

中文:
定理 inv_mem_iff
  条件: {c d : C} (f : c ⟶ d)
  证明: by
  constructor
  · intro h
    simpa only [inv_eq_inv, IsIso.inv_inv] using S.inv h
  · apply S.inv

Depends on / 依赖: I.regularMono, IsIso.inv_inv, IsRegularMono, NormalMono, S.inv, inv_eq_inv, inv_inv, regularMono
-/
theorem inv_mem_iff {c d : C} (f : c ⟶ d) :
    Groupoid.inv f in S.arrows d c ↔ f in S.arrows c d := by
  constructor
  · intro h
    simpa only [inv_eq_inv, IsIso.inv_inv] using S.inv h
  · apply S.inv

/--
theorem `mul_mem_cancel_left` / 定理 `mul_mem_cancel_left`

English:
theorem mul_mem_cancel_left
  given: {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hf : f in S.arrows c d)
  proof: by
  constructor
  · rintro h
    suffices Groupoid.inv f ≫ f ≫ g in S.arrows d e by
      simpa only [inv_eq_inv, IsIso.inv_hom_id_assoc] using this
    apply S.mul (S.inv hf) h
  · apply S.mul hf

中文:
定理 mul_mem_cancel_left
  条件: {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hf : f in S.arrows c d)
  证明: by
  constructor
  · rintro h
    suffices Groupoid.inv f ≫ f ≫ g in S.arrows d e by
      simpa only [inv_eq_inv, IsIso.inv_hom_id_assoc] using this
    apply S.mul (S.inv hf) h
  · apply S.mul hf

Depends on / 依赖: Groupoid, Groupoid.inv, IsIso.inv_hom_id_assoc, S.arrows, S.inv, S.mul, arrows, inv_eq_inv, inv_hom_id_assoc
-/
theorem mul_mem_cancel_left {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hf : f in S.arrows c d) :
    f ≫ g in S.arrows c e ↔ g in S.arrows d e := by
  constructor
  · rintro h
    suffices Groupoid.inv f ≫ f ≫ g in S.arrows d e by
      simpa only [inv_eq_inv, IsIso.inv_hom_id_assoc] using this
    apply S.mul (S.inv hf) h
  · apply S.mul hf

/--
theorem `mul_mem_cancel_right` / 定理 `mul_mem_cancel_right`

English:
theorem mul_mem_cancel_right
  given: {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hg : g in S.arrows d e)
  proof: by
  constructor
  · rintro h
    suffices (f ≫ g) ≫ Groupoid.inv g in S.arrows c d by
      simpa only [inv_eq_inv, IsIso.hom_inv_id, Category.comp_id, Category.assoc] using this
    apply S.mul h (S.inv hg)
  · exact fun hf => S.mul hf hg

中文:
定理 mul_mem_cancel_right
  条件: {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hg : g in S.arrows d e)
  证明: by
  constructor
  · rintro h
    suffices (f ≫ g) ≫ Groupoid.inv g in S.arrows c d by
      simpa only [inv_eq_inv, IsIso.hom_inv_id, Category.comp_id, Category.assoc] using this
    apply S.mul h (S.inv hg)
  · exact fun hf => S.mul hf hg

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Groupoid, Groupoid.inv, IsIso.hom_inv_id, S.arrows, S.inv, S.mul, arrows, comp_id, hom_inv_id, inv_eq_inv
-/
theorem mul_mem_cancel_right {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hg : g in S.arrows d e) :
    f ≫ g in S.arrows c e ↔ f in S.arrows c d := by
  constructor
  · rintro h
    suffices (f ≫ g) ≫ Groupoid.inv g in S.arrows c d by
      simpa only [inv_eq_inv, IsIso.hom_inv_id, Category.comp_id, Category.assoc] using this
    apply S.mul h (S.inv hg)
  · exact fun hf => S.mul hf hg

/--
Definition of `objs` / `objs` 的定义

English:
definition objs
  signature: : Set C
  body: {c : C | (S.arrows c c).Nonempty}

中文:
定义 objs
  签名: : Set C
  定义体: {c : C | (S.arrows c c).Nonempty}

Depends on / 依赖: Nonempty, S.arrows, arrows
-/
def objs : Set C :=
  {c : C | (S.arrows c c).Nonempty}

/--
theorem `mem_objs_of_src` / 定理 `mem_objs_of_src`

English:
theorem mem_objs_of_src
  given: {c d : C} {f : c ⟶ d} (h : f in S.arrows c d)
  statement: c in S.objs
  proof: ⟨f ≫ Groupoid.inv f, S.mul h (S.inv h)⟩

中文:
定理 mem_objs_of_src
  条件: {c d : C} {f : c ⟶ d} (h : f in S.arrows c d)
  结论: c in S.objs
  证明: ⟨f ≫ Groupoid.inv f, S.mul h (S.inv h)⟩

Depends on / 依赖: Groupoid, Groupoid.inv, S.inv, S.mul
-/
theorem mem_objs_of_src {c d : C} {f : c ⟶ d} (h : f in S.arrows c d) : c in S.objs :=
  ⟨f ≫ Groupoid.inv f, S.mul h (S.inv h)⟩

/--
theorem `mem_objs_of_tgt` / 定理 `mem_objs_of_tgt`

English:
theorem mem_objs_of_tgt
  given: {c d : C} {f : c ⟶ d} (h : f in S.arrows c d)
  statement: d in S.objs
  proof: ⟨Groupoid.inv f ≫ f, S.mul (S.inv h) h⟩

中文:
定理 mem_objs_of_tgt
  条件: {c d : C} {f : c ⟶ d} (h : f in S.arrows c d)
  结论: d in S.objs
  证明: ⟨Groupoid.inv f ≫ f, S.mul (S.inv h) h⟩

Depends on / 依赖: Groupoid, Groupoid.inv, S.inv, S.mul
-/
theorem mem_objs_of_tgt {c d : C} {f : c ⟶ d} (h : f in S.arrows c d) : d in S.objs :=
  ⟨Groupoid.inv f ≫ f, S.mul (S.inv h) h⟩

/--
theorem `id_mem_of_nonempty_isotropy` / 定理 `id_mem_of_nonempty_isotropy`

English:
theorem id_mem_of_nonempty_isotropy
  given: (c : C)
  statement: c in objs S -> 𝟙 c in S.arrows c c
  proof: by
  rintro ⟨γ, hγ⟩
  convert! S.mul hγ (S.inv hγ)
  simp only [inv_eq_inv, IsIso.hom_inv_id]

中文:
定理 id_mem_of_nonempty_isotropy
  条件: (c : C)
  结论: c in objs S -> 𝟙 c in S.arrows c c
  证明: by
  rintro ⟨γ, hγ⟩
  convert! S.mul hγ (S.inv hγ)
  simp only [inv_eq_inv, IsIso.hom_inv_id]

Depends on / 依赖: IsIso.hom_inv_id, IsNormalMonoCategory, S.inv, S.mul, convert, hom_inv_id, inv_eq_inv, regularMonoCategoryOfNormalMonoCategory
-/
theorem id_mem_of_nonempty_isotropy (c : C) : c in objs S -> 𝟙 c in S.arrows c c := by
  rintro ⟨γ, hγ⟩
  convert! S.mul hγ (S.inv hγ)
  simp only [inv_eq_inv, IsIso.hom_inv_id]

/--
theorem `id_mem_of_src` / 定理 `id_mem_of_src`

English:
theorem id_mem_of_src
  given: {c d : C} {f : c ⟶ d} (h : f in S.arrows c d)
  statement: 𝟙 c in S.arrows c c
  proof: id_mem_of_nonempty_isotropy S c (mem_objs_of_src S h)

中文:
定理 id_mem_of_src
  条件: {c d : C} {f : c ⟶ d} (h : f in S.arrows c d)
  结论: 𝟙 c in S.arrows c c
  证明: id_mem_of_nonempty_isotropy S c (mem_objs_of_src S h)

Depends on / 依赖: id_mem_of_nonempty_isotropy, mem_objs_of_src
-/
theorem id_mem_of_src {c d : C} {f : c ⟶ d} (h : f in S.arrows c d) : 𝟙 c in S.arrows c c :=
  id_mem_of_nonempty_isotropy S c (mem_objs_of_src S h)

/--
theorem `id_mem_of_tgt` / 定理 `id_mem_of_tgt`

English:
theorem id_mem_of_tgt
  given: {c d : C} {f : c ⟶ d} (h : f in S.arrows c d)
  statement: 𝟙 d in S.arrows d d
  proof: id_mem_of_nonempty_isotropy S d (mem_objs_of_tgt S h)

中文:
定理 id_mem_of_tgt
  条件: {c d : C} {f : c ⟶ d} (h : f in S.arrows c d)
  结论: 𝟙 d in S.arrows d d
  证明: id_mem_of_nonempty_isotropy S d (mem_objs_of_tgt S h)

Depends on / 依赖: id_mem_of_nonempty_isotropy, mem_objs_of_tgt
-/
theorem id_mem_of_tgt {c d : C} {f : c ⟶ d} (h : f in S.arrows c d) : 𝟙 d in S.arrows d d :=
  id_mem_of_nonempty_isotropy S d (mem_objs_of_tgt S h)

/-- A subgroupoid seen as a quiver on vertex set `C` -/
@[instance_reducible]
/--
Definition of `asWideQuiver` / `asWideQuiver` 的定义

English:
definition asWideQuiver
  signature: : Quiver C
  body: ⟨fun c d => S.arrows c d⟩

中文:
定义 asWideQuiver
  签名: : Quiver C
  定义体: ⟨fun c d => S.arrows c d⟩

Depends on / 依赖: I.regularEpi, IsRegularEpi, NormalEpi, S.arrows, arrows, regularEpi
-/
def asWideQuiver : Quiver C :=
  ⟨fun c d => S.arrows c d⟩

/-- The coercion of a subgroupoid as a groupoid -/
@[simps comp_coe, simps -isSimp inv_coe]
/--
Instance `coe` / 实例 `coe`

English:
instance coe
  signature: : Groupoid S.objs where
  body: S.arrows a.val b.val
  id a := ⟨𝟙 a.val, id_mem_of_nonempty_isotropy S a.val a.prop⟩
  comp p q := ⟨p.val ≫ q.val, S.mul p.prop q.prop⟩
  inv p := ⟨Groupoid.inv p.val, S.inv p.prop⟩

@[simp]

中文:
实例 coe
  签名: : Groupoid S.objs where
  定义体: S.arrows a.val b.val
  id a := ⟨𝟙 a.val, id_mem_of_nonempty_isotropy S a.val a.prop⟩
  comp p q := ⟨p.val ≫ q.val, S.mul p.prop q.prop⟩
  inv p := ⟨Groupoid.inv p.val, S.inv p.prop⟩

@[simp]

Depends on / 依赖: S.arrows, a.val, arrows, b.val
-/
instance coe : Groupoid S.objs where
  Hom a b := S.arrows a.val b.val
  id a := ⟨𝟙 a.val, id_mem_of_nonempty_isotropy S a.val a.prop⟩
  comp p q := ⟨p.val ≫ q.val, S.mul p.prop q.prop⟩
  inv p := ⟨Groupoid.inv p.val, S.inv p.prop⟩

@[simp]
/--
theorem `coe_inv_coe'` / 定理 `coe_inv_coe'`

English:
theorem coe_inv_coe'
  given: {c d : S.objs} (p : c ⟶ d)
  proof: by
  simp only [← inv_eq_inv, coe_inv_coe]

中文:
定理 coe_inv_coe'
  条件: {c d : S.objs} (p : c ⟶ d)
  证明: by
  simp only [← inv_eq_inv, coe_inv_coe]

Depends on / 依赖: coe_inv_coe, inv_eq_inv
-/
theorem coe_inv_coe' {c d : S.objs} (p : c ⟶ d) :
    (CategoryTheory.inv p).val = CategoryTheory.inv p.val := by
  simp only [← inv_eq_inv, coe_inv_coe]

/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: : S.objs ⥤ C where
  body: c.val
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

中文:
定义 hom
  签名: : S.objs ⥤ C where
  定义体: c.val
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

Depends on / 依赖: c.val
-/
def hom : S.objs ⥤ C where
  obj c := c.val
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

/--
theorem `hom.inj_on_objects` / 定理 `hom.inj_on_objects`

English:
theorem hom.inj_on_objects
  statement: Function.Injective (hom S).obj
  proof: by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
  simp only [Subtype.mk_eq_mk]; exact hcd

中文:
定理 hom.inj_on_objects
  结论: Function.Injective (hom S).obj
  证明: by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
  simp only [Subtype.mk_eq_mk]; exact hcd

Depends on / 依赖: Subtype, Subtype.mk_eq_mk, mk_eq_mk
-/
theorem hom.inj_on_objects : Function.Injective (hom S).obj := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
  simp only [Subtype.mk_eq_mk]; exact hcd

/--
theorem `hom.faithful` / 定理 `hom.faithful`

English:
theorem hom.faithful
  statement: forall c d, Function.Injective fun f : c ⟶ d => (hom S).map f
  proof: by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ ⟨f, hf⟩ ⟨g, hg⟩ hfg; exact Subtype.ext hfg

中文:
定理 hom.faithful
  结论: 对任意 c d, Function.Injective fun f : c ⟶ d => (hom S).map f
  证明: by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ ⟨f, hf⟩ ⟨g, hg⟩ hfg; exact Subtype.ext hfg

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem hom.faithful : forall c d, Function.Injective fun f : c ⟶ d => (hom S).map f := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ ⟨f, hf⟩ ⟨g, hg⟩ hfg; exact Subtype.ext hfg

/--
Definition of `vertexSubgroup` / `vertexSubgroup` 的定义

English:
definition vertexSubgroup
  signature: {c : C} (hc : c in S.objs)
  body: S.arrows c c
  mul_mem' hf hg := S.mul hf hg
  one_mem' := id_mem_of_nonempty_isotropy _ _ hc
  inv_mem' hf := S.inv hf

中文:
定义 vertexSubgroup
  签名: {c : C} (hc : c in S.objs)
  定义体: S.arrows c c
  mul_mem' hf hg := S.mul hf hg
  one_mem' := id_mem_of_nonempty_isotropy _ _ hc
  inv_mem' hf := S.inv hf

Depends on / 依赖: S.arrows, arrows
-/
def vertexSubgroup {c : C} (hc : c in S.objs) : Subgroup (c ⟶ c) where
  carrier := S.arrows c c
  mul_mem' hf hg := S.mul hf hg
  one_mem' := id_mem_of_nonempty_isotropy _ _ hc
  inv_mem' hf := S.inv hf

/--
Definition of `toSet` / `toSet` 的定义

English:
definition toSet
  signature: (S : Subgroupoid C)
  body: {F | F.2.2 in S.arrows F.1 F.2.1}

中文:
定义 toSet
  签名: (S : Subgroupoid C)
  定义体: {F | F.2.2 in S.arrows F.1 F.2.1}
-/
@[coe] def toSet (S : Subgroupoid C) : Set (Σ c d : C, c ⟶ d) :=
  {F | F.2.2 in S.arrows F.1 F.2.1}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Subgroupoid C) (Σ c d : C, c ⟶ d)
  body: toSet
  coe_injective := fun ⟨S, _, _⟩ ⟨T, _, _⟩ h => by ext c d f; apply Set.ext_iff.1 h ⟨c, d, f⟩

中文:
实例 :
  签名: SetLike (Subgroupoid C) (Σ c d : C, c ⟶ d)
  定义体: toSet
  coe_injective := fun ⟨S, _, _⟩ ⟨T, _, _⟩ h => by ext c d f; apply Set.ext_iff.1 h ⟨c, d, f⟩

Depends on / 依赖: IsNormalEpiCategory, regularEpiCategoryOfNormalEpiCategory
-/
instance : SetLike (Subgroupoid C) (Σ c d : C, c ⟶ d) where
  coe := toSet
  coe_injective := fun ⟨S, _, _⟩ ⟨T, _, _⟩ h => by ext c d f; apply Set.ext_iff.1 h ⟨c, d, f⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Subgroupoid C)
  body: .ofSetLike (Subgroupoid C) (Σ c d : C, c ⟶ d)

中文:
实例 :
  签名: PartialOrder (Subgroupoid C)
  定义体: .ofSetLike (Subgroupoid C) (Σ c d : C, c ⟶ d)

Depends on / 依赖: Subgroupoid, ofSetLike
-/
instance : PartialOrder (Subgroupoid C) := .ofSetLike (Subgroupoid C) (Σ c d : C, c ⟶ d)

/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: (S : Subgroupoid C) (F : Σ c d, c ⟶ d)
  statement: F in S ↔ F.2.2 in S.arrows F.1 F.2.1
  proof: Iff.rfl

中文:
定理 mem_iff
  条件: (S : Subgroupoid C) (F : Σ c d, c ⟶ d)
  结论: F in S ↔ F.2.2 in S.arrows F.1 F.2.1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_iff (S : Subgroupoid C) (F : Σ c d, c ⟶ d) : F in S ↔ F.2.2 in S.arrows F.1 F.2.1 :=
  Iff.rfl

/--
theorem `le_iff` / 定理 `le_iff`

English:
theorem le_iff
  given: (S T : Subgroupoid C)
  statement: S <= T ↔ forall {c d}, S.arrows c d subseteq T.arrows c d
  proof: by
  rw [SetLike.le_def]; rw [Sigma.forall]; exact forall_congr' fun c => Sigma.forall

中文:
定理 le_iff
  条件: (S T : Subgroupoid C)
  结论: S <= T ↔ 对任意 {c d}, S.arrows c d subseteq T.arrows c d
  证明: by
  rw [SetLike.le_def]; rw [Sigma.forall]; exact forall_congr' fun c => Sigma.forall

Depends on / 依赖: HasEqualizers, SetLike, SetLike.le_def, Sigma.forall, forall_congr, hasEqualizers, le_def
-/
theorem le_iff (S T : Subgroupoid C) : S <= T ↔ forall {c d}, S.arrows c d subseteq T.arrows c d := by
  rw [SetLike.le_def]; rw [Sigma.forall]; exact forall_congr' fun c => Sigma.forall

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (Subgroupoid C)
  body: ⟨{ arrows := fun _ _ => Set.univ
      mul := by intros; trivial
      inv := by intros; trivial }⟩

中文:
实例 :
  签名: Top (Subgroupoid C)
  定义体: ⟨{ arrows := fun _ _ => Set.univ
      mul := by intros; trivial
      inv := by intros; trivial }⟩

Depends on / 依赖: Set.univ, arrows, intros
-/
instance : Top (Subgroupoid C) :=
  ⟨{ arrows := fun _ _ => Set.univ
      mul := by intros; trivial
      inv := by intros; trivial }⟩

/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: {c d : C} (f : c ⟶ d)
  statement: f in (⊤ : Subgroupoid C).arrows c d
  proof: trivial

中文:
定理 mem_top
  条件: {c d : C} (f : c ⟶ d)
  结论: f in (⊤ : Subgroupoid C).arrows c d
  证明: trivial
-/
theorem mem_top {c d : C} (f : c ⟶ d) : f in (⊤ : Subgroupoid C).arrows c d :=
  trivial

/--
theorem `mem_top_objs` / 定理 `mem_top_objs`

English:
theorem mem_top_objs
  given: (c : C)
  statement: c in (⊤ : Subgroupoid C).objs
  proof: by
  dsimp [Top.top, objs]
  simp only [univ_nonempty]

中文:
定理 mem_top_objs
  条件: (c : C)
  结论: c in (⊤ : Subgroupoid C).objs
  证明: by
  dsimp [Top.top, objs]
  simp only [univ_nonempty]

Depends on / 依赖: Top.top, univ_nonempty
-/
theorem mem_top_objs (c : C) : c in (⊤ : Subgroupoid C).objs := by
  dsimp [Top.top, objs]
  simp only [univ_nonempty]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (Subgroupoid C)
  body: ⟨{ arrows := fun _ _ => ∅
      mul := False.elim
      inv := False.elim }⟩

中文:
实例 :
  签名: Bot (Subgroupoid C)
  定义体: ⟨{ arrows := fun _ _ => ∅
      mul := False.elim
      inv := False.elim }⟩

Depends on / 依赖: False.elim, arrows
-/
instance : Bot (Subgroupoid C) :=
  ⟨{ arrows := fun _ _ => ∅
      mul := False.elim
      inv := False.elim }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Subgroupoid C)
  body: ⟨⊤⟩

中文:
实例 :
  签名: Inhabited (Subgroupoid C)
  定义体: ⟨⊤⟩
-/
instance : Inhabited (Subgroupoid C) :=
  ⟨⊤⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Subgroupoid C)
  body: ⟨fun S T =>
    { arrows := fun c d => S.arrows c d inter T.arrows c d
      inv := fun hp => ⟨S.inv hp.1, T.inv hp.2⟩
      mul := fun hp _ hq => ⟨S.mul hp.1 hq.1, T.mul hp.2 hq.2⟩ }⟩

中文:
实例 :
  签名: Min (Subgroupoid C)
  定义体: ⟨fun S T =>
    { arrows := fun c d => S.arrows c d inter T.arrows c d
      inv := fun hp => ⟨S.inv hp.1, T.inv hp.2⟩
      mul := fun hp _ hq => ⟨S.mul hp.1 hq.1, T.mul hp.2 hq.2⟩ }⟩

Depends on / 依赖: HasCoequalizers, S.arrows, S.inv, S.mul, T.arrows, T.inv, T.mul, arrows, hasCoequalizers
-/
instance : Min (Subgroupoid C) :=
  ⟨fun S T =>
    { arrows := fun c d => S.arrows c d inter T.arrows c d
      inv := fun hp => ⟨S.inv hp.1, T.inv hp.2⟩
      mul := fun hp _ hq => ⟨S.mul hp.1 hq.1, T.mul hp.2 hq.2⟩ }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Subgroupoid C)
  body: ⟨fun s =>
    { arrows := fun c d => ⋂ S in s, Subgroupoid.arrows S c d
      inv := fun hp => by rw [mem_iInter₂] at hp ⊢; exact fun S hS => S.inv (hp S hS)
      mul := fun hp _ hq => by
        rw [mem_iInter₂] at hp hq ⊢
        exact fun S hS => S.mul (hp S hS) (hq S hS) }⟩

中文:
实例 :
  签名: InfSet (Subgroupoid C)
  定义体: ⟨fun s =>
    { arrows := fun c d => ⋂ S in s, Subgroupoid.arrows S c d
      inv := fun hp => by rw [mem_iInter₂] at hp ⊢; exact fun S hS => S.inv (hp S hS)
      mul := fun hp _ hq => by
        rw [mem_iInter₂] at hp hq ⊢
        exact fun S hS => S.mul (hp S hS) (hq S hS) }⟩

Depends on / 依赖: S.inv, S.mul, Subgroupoid, Subgroupoid.arrows, arrows
-/
instance : InfSet (Subgroupoid C) :=
  ⟨fun s =>
    { arrows := fun c d => ⋂ S in s, Subgroupoid.arrows S c d
      inv := fun hp => by rw [mem_iInter₂] at hp ⊢; exact fun S hS => S.inv (hp S hS)
      mul := fun hp _ hq => by
        rw [mem_iInter₂] at hp hq ⊢
        exact fun S hS => S.mul (hp S hS) (hq S hS) }⟩

/--
theorem `mem_sInf_arrows` / 定理 `mem_sInf_arrows`

English:
theorem mem_sInf_arrows
  given: {s : Set (Subgroupoid C)} {c d : C} {p : c ⟶ d}
  proof: mem_iInter₂

中文:
定理 mem_sInf_arrows
  条件: {s : Set (Subgroupoid C)} {c d : C} {p : c ⟶ d}
  证明: mem_iInter₂
-/
theorem mem_sInf_arrows {s : Set (Subgroupoid C)} {c d : C} {p : c ⟶ d} :
    p in (sInf s).arrows c d ↔ forall S in s, p in S.arrows c d :=
  mem_iInter₂

/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {s : Set (Subgroupoid C)} {p : Σ c d : C, c ⟶ d}
  proof: mem_sInf_arrows

中文:
定理 mem_sInf
  条件: {s : Set (Subgroupoid C)} {p : Σ c d : C, c ⟶ d}
  证明: mem_sInf_arrows

Depends on / 依赖: mem_sInf_arrows
-/
theorem mem_sInf {s : Set (Subgroupoid C)} {p : Σ c d : C, c ⟶ d} :
    p in sInf s ↔ forall S in s, p in S :=
  mem_sInf_arrows

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Subgroupoid C)
  body: { completeLatticeOfInf (Subgroupoid C) (by
      refine fun s => ⟨fun S Ss F => ?_, fun T Tl F fT => ?_⟩ <;> simp only [mem_sInf]
      exacts [fun hp => hp S Ss, fun S Ss => Tl Ss fT]) with
    bot := ⊥
    bot_le := fun _ => empty_subset _
    top := ⊤
    le_top := fun _ => subset_univ _
    inf 

中文:
实例 :
  签名: CompleteLattice (Subgroupoid C)
  定义体: { completeLatticeOfInf (Subgroupoid C) (by
      refine fun s => ⟨fun S Ss F => ?_, fun T Tl F fT => ?_⟩ <;> simp only [mem_sInf]
      exacts [fun hp => hp S Ss, fun S Ss => Tl Ss fT]) with
    bot := ⊥
    bot_le := fun _ => empty_subset _
    top := ⊤
    le_top := fun _ => subset_univ _
    inf 

Depends on / 依赖: And.left, And.right, Subgroupoid, bot_le, completeLatticeOfInf, empty_subset, exacts, inf_le_left, inf_le_right, le_inf, le_top, mem_sInf, subset_univ
-/
instance : CompleteLattice (Subgroupoid C) :=
  { completeLatticeOfInf (Subgroupoid C) (by
      refine fun s => ⟨fun S Ss F => ?_, fun T Tl F fT => ?_⟩ <;> simp only [mem_sInf]
      exacts [fun hp => hp S Ss, fun S Ss => Tl Ss fT]) with
    bot := ⊥
    bot_le := fun _ => empty_subset _
    top := ⊤
    le_top := fun _ => subset_univ _
    inf := (· ⊓ ·)
    le_inf := fun _ _ _ RS RT _ pR => ⟨RS pR, RT pR⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

/--
theorem `le_objs` / 定理 `le_objs`

English:
theorem le_objs
  given: {S T : Subgroupoid C} (h : S <= T)
  statement: S.objs subseteq T.objs
  proof: fun s ⟨γ, hγ⟩ =>
  ⟨γ, @h ⟨s, s, γ⟩ hγ⟩

中文:
定理 le_objs
  条件: {S T : Subgroupoid C} (h : S <= T)
  结论: S.objs subseteq T.objs
  证明: fun s ⟨γ, hγ⟩ =>
  ⟨γ, @h ⟨s, s, γ⟩ hγ⟩
-/
theorem le_objs {S T : Subgroupoid C} (h : S <= T) : S.objs subseteq T.objs := fun s ⟨γ, hγ⟩ =>
  ⟨γ, @h ⟨s, s, γ⟩ hγ⟩

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {S T : Subgroupoid C} (h : S <= T)
  body: ⟨s.val, le_objs h s.prop⟩
  map f := ⟨f.val, @h ⟨_, _, f.val⟩ f.prop⟩
  map_id _ := rfl
  map_comp _ _ := rfl

中文:
定义 inclusion
  签名: {S T : Subgroupoid C} (h : S <= T)
  定义体: ⟨s.val, le_objs h s.prop⟩
  map f := ⟨f.val, @h ⟨_, _, f.val⟩ f.prop⟩
  map_id _ := rfl
  map_comp _ _ := rfl

Depends on / 依赖: le_objs, s.prop, s.val
-/
def inclusion {S T : Subgroupoid C} (h : S <= T) : S.objs ⥤ T.objs where
  obj s := ⟨s.val, le_objs h s.prop⟩
  map f := ⟨f.val, @h ⟨_, _, f.val⟩ f.prop⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/--
theorem `inclusion_inj_on_objects` / 定理 `inclusion_inj_on_objects`

English:
theorem inclusion_inj_on_objects
  given: {S T : Subgroupoid C} (h : S <= T)
  proof: fun ⟨s, hs⟩ ⟨t, ht⟩ => by
  simpa only [inclusion, Subtype.mk_eq_mk] using id

中文:
定理 inclusion_inj_on_objects
  条件: {S T : Subgroupoid C} (h : S <= T)
  证明: fun ⟨s, hs⟩ ⟨t, ht⟩ => by
  simpa only [inclusion, Subtype.mk_eq_mk] using id

Depends on / 依赖: Subtype, Subtype.mk_eq_mk, inclusion, mk_eq_mk
-/
theorem inclusion_inj_on_objects {S T : Subgroupoid C} (h : S <= T) :
    Function.Injective (inclusion h).obj := fun ⟨s, hs⟩ ⟨t, ht⟩ => by
  simpa only [inclusion, Subtype.mk_eq_mk] using id

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `inclusion_faithful` / 定理 `inclusion_faithful`

English:
theorem inclusion_faithful
  given: {S T : Subgroupoid C} (h : S <= T) (s t : S.objs)
  proof: fun ⟨f, hf⟩ ⟨g, hg⟩ => by
  -- Porting note: was `...; simpa only [Subtype.mk_eq_mk] using id`
  dsimp only [inclusion]; rw [Subtype.mk_eq_mk, Subtype.mk_eq_mk]; exact id

中文:
定理 inclusion_faithful
  条件: {S T : Subgroupoid C} (h : S <= T) (s t : S.objs)
  证明: fun ⟨f, hf⟩ ⟨g, hg⟩ => by
  -- Porting note: was `...; simpa only [Subtype.mk_eq_mk] using id`
  dsimp only [inclusion]; rw [Subtype.mk_eq_mk, Subtype.mk_eq_mk]; exact id
-/
theorem inclusion_faithful {S T : Subgroupoid C} (h : S <= T) (s t : S.objs) :
    Function.Injective fun f : s ⟶ t => (inclusion h).map f := fun ⟨f, hf⟩ ⟨g, hg⟩ => by
  -- Porting note: was `...; simpa only [Subtype.mk_eq_mk] using id`
  dsimp only [inclusion]; rw [Subtype.mk_eq_mk, Subtype.mk_eq_mk]; exact id

/--
theorem `inclusion_refl` / 定理 `inclusion_refl`

English:
theorem inclusion_refl
  given: {S : Subgroupoid C}
  statement: inclusion (le_refl S) = 𝟭 S.objs
  proof: Functor.hext (fun _ => rfl) fun _ _ _ => HEq.refl _

中文:
定理 inclusion_refl
  条件: {S : Subgroupoid C}
  结论: inclusion (le_refl S) = 𝟭 S.objs
  证明: Functor.hext (fun _ => rfl) fun _ _ _ => HEq.refl _

Depends on / 依赖: Functor, Functor.hext, HEq.refl
-/
theorem inclusion_refl {S : Subgroupoid C} : inclusion (le_refl S) = 𝟭 S.objs :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.refl _

/--
theorem `inclusion_trans` / 定理 `inclusion_trans`

English:
theorem inclusion_trans
  given: {R S T : Subgroupoid C} (k : R <= S) (h : S <= T)
  proof: rfl

中文:
定理 inclusion_trans
  条件: {R S T : Subgroupoid C} (k : R <= S) (h : S <= T)
  证明: rfl
-/
theorem inclusion_trans {R S T : Subgroupoid C} (k : R <= S) (h : S <= T) :
    inclusion (k.trans h) = inclusion k ⋙ inclusion h :=
  rfl

/--
theorem `inclusion_comp_embedding` / 定理 `inclusion_comp_embedding`

English:
theorem inclusion_comp_embedding
  given: {S T : Subgroupoid C} (h : S <= T)
  statement: inclusion h ⋙ T.hom = S.hom
  proof: rfl

中文:
定理 inclusion_comp_embedding
  条件: {S T : Subgroupoid C} (h : S <= T)
  结论: inclusion h ⋙ T.hom = S.hom
  证明: rfl
-/
theorem inclusion_comp_embedding {S T : Subgroupoid C} (h : S <= T) : inclusion h ⋙ T.hom = S.hom :=
  rfl

/--
Inductive type `Discrete.Arrows` / 归纳类型 `Discrete.Arrows`

English:
inductive Discrete.Arrows
  parameters: : forall c d : C, (c ⟶ d) -> Prop
  constructors (1):
    - id: (c : C) : Discrete.Arrows c c (𝟙 c)

中文:
归纳类型 Discrete.Arrows
  参数: : 对任意 c d : C, (c ⟶ d) -> 命题
  构造子 (1 个):
    - id: (c : C) : Discrete.Arrows c c (𝟙 c)
-/
inductive Discrete.Arrows : forall c d : C, (c ⟶ d) -> Prop
  | id (c : C) : Discrete.Arrows c c (𝟙 c)

/--
Definition of `discrete` / `discrete` 的定义

English:
definition discrete
  signature: : Subgroupoid C where
  body: {p | Discrete.Arrows c d p}
  inv := by rintro _ _ _ ⟨⟩; simp only [inv_eq_inv, IsIso.inv_id]; constructor
  mul := by rintro _ _ _ _ ⟨⟩ _ ⟨⟩; rw [Category.comp_id]; constructor

中文:
定义 discrete
  签名: : Subgroupoid C where
  定义体: {p | Discrete.Arrows c d p}
  inv := by rintro _ _ _ ⟨⟩; simp only [inv_eq_inv, IsIso.inv_id]; constructor
  mul := by rintro _ _ _ _ ⟨⟩ _ ⟨⟩; rw [Category.comp_id]; constructor

Depends on / 依赖: Arrows, Discrete, Discrete.Arrows
-/
def discrete : Subgroupoid C where
  arrows c d := {p | Discrete.Arrows c d p}
  inv := by rintro _ _ _ ⟨⟩; simp only [inv_eq_inv, IsIso.inv_id]; constructor
  mul := by rintro _ _ _ _ ⟨⟩ _ ⟨⟩; rw [Category.comp_id]; constructor

/--
theorem `mem_discrete_iff` / 定理 `mem_discrete_iff`

English:
theorem mem_discrete_iff
  given: {c d : C} (f : c ⟶ d)
  proof: ⟨by rintro ⟨⟩; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; constructor⟩

中文:
定理 mem_discrete_iff
  条件: {c d : C} (f : c ⟶ d)
  证明: ⟨by rintro ⟨⟩; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; constructor⟩
-/
theorem mem_discrete_iff {c d : C} (f : c ⟶ d) :
    f in discrete.arrows c d ↔ exists h : c = d, f = eqToHom h :=
  ⟨by rintro ⟨⟩; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; constructor⟩

/--
Definition of `IsWide` / `IsWide` 的定义

English:
structure IsWide
  parameters: : Prop where
  axioms and operations (1):
    - wide : forall c, 𝟙 c in S.arrows c c

中文:
结构 IsWide
  参数: : 命题 where
  公理与运算 (1 个):
    - wide : 对任意 c, 𝟙 c in S.arrows c c
-/
structure IsWide : Prop where
  wide : forall c, 𝟙 c in S.arrows c c

/--
theorem `isWide_iff_objs_eq_univ` / 定理 `isWide_iff_objs_eq_univ`

English:
theorem isWide_iff_objs_eq_univ
  statement: S.IsWide ↔ S.objs = Set.univ
  proof: by
  constructor
  · rintro h
    ext x; constructor <;> simp only [mem_univ, imp_true_iff, forall_true_left]
    apply mem_objs_of_src S (h.wide x)
  · rintro h
    refine ⟨fun c => ?_⟩
    obtain ⟨γ, γS⟩ := (le_of_eq h.symm : ⊤ subseteq S.objs) (Set.mem_univ c)
    exact id_mem_of_src S γS

中文:
定理 isWide_iff_objs_eq_univ
  结论: S.IsWide ↔ S.objs = Set.univ
  证明: by
  constructor
  · rintro h
    ext x; constructor <;> simp only [mem_univ, imp_true_iff, forall_true_left]
    apply mem_objs_of_src S (h.wide x)
  · rintro h
    refine ⟨fun c => ?_⟩
    obtain ⟨γ, γS⟩ := (le_of_eq h.symm : ⊤ subseteq S.objs) (Set.mem_univ c)
    exact id_mem_of_src S γS

Depends on / 依赖: S.objs, Set.mem_univ, forall_true_left, h.symm, h.wide, id_mem_of_src, imp_true_iff, le_of_eq, mem_objs_of_src, mem_univ, subseteq
-/
theorem isWide_iff_objs_eq_univ : S.IsWide ↔ S.objs = Set.univ := by
  constructor
  · rintro h
    ext x; constructor <;> simp only [mem_univ, imp_true_iff, forall_true_left]
    apply mem_objs_of_src S (h.wide x)
  · rintro h
    refine ⟨fun c => ?_⟩
    obtain ⟨γ, γS⟩ := (le_of_eq h.symm : ⊤ subseteq S.objs) (Set.mem_univ c)
    exact id_mem_of_src S γS

/--
theorem `IsWide.id_mem` / 定理 `IsWide.id_mem`

English:
theorem IsWide.id_mem
  given: {S : Subgroupoid C} (Sw : S.IsWide) (c : C)
  statement: 𝟙 c in S.arrows c c
  proof: Sw.wide c

中文:
定理 IsWide.id_mem
  条件: {S : Subgroupoid C} (Sw : S.IsWide) (c : C)
  结论: 𝟙 c in S.arrows c c
  证明: Sw.wide c

Depends on / 依赖: Sw.wide
-/
theorem IsWide.id_mem {S : Subgroupoid C} (Sw : S.IsWide) (c : C) : 𝟙 c in S.arrows c c :=
  Sw.wide c

/--
theorem `IsWide.eqToHom_mem` / 定理 `IsWide.eqToHom_mem`

English:
theorem IsWide.eqToHom_mem
  given: {S : Subgroupoid C} (Sw : S.IsWide) {c d : C} (h : c = d)
  proof: by cases h; simp only [eqToHom_refl]; apply Sw.id_mem c

中文:
定理 IsWide.eqToHom_mem
  条件: {S : Subgroupoid C} (Sw : S.IsWide) {c d : C} (h : c = d)
  证明: by cases h; simp only [eqToHom_refl]; apply Sw.id_mem c

Depends on / 依赖: Sw.id_mem, eqToHom_refl, id_mem
-/
theorem IsWide.eqToHom_mem {S : Subgroupoid C} (Sw : S.IsWide) {c d : C} (h : c = d) :
    eqToHom h in S.arrows c d := by cases h; simp only [eqToHom_refl]; apply Sw.id_mem c

/--
Definition of `IsNormal` / `IsNormal` 的定义

English:
structure IsNormal
  parameters: : Prop extends IsWide S where
  extends: IsWide S
  axioms and operations (1):
    - conj : forall {c d} (p : c ⟶ d) {γ : c ⟶ c}, γ in S.arrows c c -> Groupoid.inv p ≫ γ ≫ p in S.arrows d d

中文:
结构 IsNormal
  参数: : 命题 extends IsWide S where
  继承: IsWide S
  公理与运算 (1 个):
    - conj : 对任意 {c d} (p : c ⟶ d) {γ : c ⟶ c}, γ in S.arrows c c -> Groupoid.inv p ≫ γ ≫ p in S.arrows d d
-/
structure IsNormal : Prop extends IsWide S where
  conj : forall {c d} (p : c ⟶ d) {γ : c ⟶ c}, γ in S.arrows c c -> Groupoid.inv p ≫ γ ≫ p in S.arrows d d

/--
theorem `IsNormal.conj'` / 定理 `IsNormal.conj'`

English:
theorem IsNormal.conj'
  given: {S : Subgroupoid C} (Sn : IsNormal S)
  proof: fun p γ hs => by convert! Sn.conj (Groupoid.inv p) hs; simp

中文:
定理 IsNormal.conj'
  条件: {S : Subgroupoid C} (Sn : IsNormal S)
  证明: fun p γ hs => by convert! Sn.conj (Groupoid.inv p) hs; simp

Depends on / 依赖: Groupoid, Groupoid.inv, Sn.conj, convert
-/
theorem IsNormal.conj' {S : Subgroupoid C} (Sn : IsNormal S) :
    forall {c d} (p : d ⟶ c) {γ : c ⟶ c}, γ in S.arrows c c -> p ≫ γ ≫ Groupoid.inv p in S.arrows d d :=
  fun p γ hs => by convert! Sn.conj (Groupoid.inv p) hs; simp

/--
theorem `IsNormal.conjugation_bij` / 定理 `IsNormal.conjugation_bij`

English:
theorem IsNormal.conjugation_bij
  given: (Sn : IsNormal S) {c d} (p : c ⟶ d)
  proof: by
  refine ⟨fun γ γS => Sn.conj p γS, fun γ₁ _ γ₂ _ h => ?_, fun δ δS =>
    ⟨p ≫ δ ≫ Groupoid.inv p, Sn.conj' p δS, ?_⟩⟩
  · simpa only [inv_eq_inv, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc] using p ≫= h =≫ inv p
  · simp only [inv_eq_inv, Category.assoc, Is

中文:
定理 IsNormal.conjugation_bij
  条件: (Sn : IsNormal S) {c d} (p : c ⟶ d)
  证明: by
  refine ⟨fun γ γS => Sn.conj p γS, fun γ₁ _ γ₂ _ h => ?_, fun δ δS =>
    ⟨p ≫ δ ≫ Groupoid.inv p, Sn.conj' p δS, ?_⟩⟩
  · simpa only [inv_eq_inv, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc] using p ≫= h =≫ inv p
  · simp only [inv_eq_inv, Category.assoc, Is

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Groupoid, Groupoid.inv, IsIso.hom_inv_id, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id, IsIso.inv_hom_id_assoc, Sn.conj, comp_id, hom_inv_id, hom_inv_id_assoc, inv_eq_inv, inv_hom_id, inv_hom_id_assoc
-/
theorem IsNormal.conjugation_bij (Sn : IsNormal S) {c d} (p : c ⟶ d) :
    Set.BijOn (fun γ : c ⟶ c => Groupoid.inv p ≫ γ ≫ p) (S.arrows c c) (S.arrows d d) := by
  refine ⟨fun γ γS => Sn.conj p γS, fun γ₁ _ γ₂ _ h => ?_, fun δ δS =>
    ⟨p ≫ δ ≫ Groupoid.inv p, Sn.conj' p δS, ?_⟩⟩
  · simpa only [inv_eq_inv, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc] using p ≫= h =≫ inv p
  · simp only [inv_eq_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      IsIso.inv_hom_id_assoc]

/--
theorem `top_isNormal` / 定理 `top_isNormal`

English:
theorem top_isNormal
  statement: IsNormal (⊤ : Subgroupoid C)
  proof: { wide := fun _ => trivial
    conj := fun _ _ _ => trivial }

中文:
定理 top_isNormal
  结论: IsNormal (⊤ : Subgroupoid C)
  证明: { wide := fun _ => trivial
    conj := fun _ _ _ => trivial }
-/
theorem top_isNormal : IsNormal (⊤ : Subgroupoid C) :=
  { wide := fun _ => trivial
    conj := fun _ _ _ => trivial }

/--
theorem `sInf_isNormal` / 定理 `sInf_isNormal`

English:
theorem sInf_isNormal
  given: (s : Set <| Subgroupoid C) (sn : forall S in s, IsNormal S)
  statement: IsNormal (sInf s)
  proof: { wide := by simp_rw [sInf, mem_iInter₂]; exact fun c S Ss => (sn S Ss).wide c
    conj := by simp_rw [sInf, mem_iInter₂]; exact fun p γ hγ S Ss => (sn S Ss).conj p (hγ S Ss) }

中文:
定理 sInf_isNormal
  条件: (s : Set <| Subgroupoid C) (sn : 对任意 S in s, IsNormal S)
  结论: IsNormal (sInf s)
  证明: { wide := by simp_rw [sInf, mem_iInter₂]; exact fun c S Ss => (sn S Ss).wide c
    conj := by simp_rw [sInf, mem_iInter₂]; exact fun p γ hγ S Ss => (sn S Ss).conj p (hγ S Ss) }

Depends on / 依赖: simp_rw
-/
theorem sInf_isNormal (s : Set <| Subgroupoid C) (sn : forall S in s, IsNormal S) : IsNormal (sInf s) :=
  { wide := by simp_rw [sInf, mem_iInter₂]; exact fun c S Ss => (sn S Ss).wide c
    conj := by simp_rw [sInf, mem_iInter₂]; exact fun p γ hγ S Ss => (sn S Ss).conj p (hγ S Ss) }

/--
theorem `discrete_isNormal` / 定理 `discrete_isNormal`

English:
theorem discrete_isNormal
  statement: (@discrete C _).IsNormal
  proof: { wide := fun c => by constructor
    conj := fun f γ hγ => by
      cases hγ
      simp only [inv_eq_inv, Category.id_comp, IsIso.inv_hom_id]; constructor }

中文:
定理 discrete_isNormal
  结论: (@discrete C _).IsNormal
  证明: { wide := fun c => by constructor
    conj := fun f γ hγ => by
      cases hγ
      simp only [inv_eq_inv, Category.id_comp, IsIso.inv_hom_id]; constructor }

Depends on / 依赖: Category, Category.id_comp, IsIso.inv_hom_id, id_comp, inv_eq_inv, inv_hom_id
-/
theorem discrete_isNormal : (@discrete C _).IsNormal :=
  { wide := fun c => by constructor
    conj := fun f γ hγ => by
      cases hγ
      simp only [inv_eq_inv, Category.id_comp, IsIso.inv_hom_id]; constructor }

/--
theorem `IsNormal.vertexSubgroup` / 定理 `IsNormal.vertexSubgroup`

English:
theorem IsNormal.vertexSubgroup
  given: (Sn : IsNormal S) (c : C) (cS : c in S.objs)
  proof: by rw [mul_assoc]; exact Sn.conj' y hx

中文:
定理 IsNormal.vertexSubgroup
  条件: (Sn : IsNormal S) (c : C) (cS : c in S.objs)
  证明: by rw [mul_assoc]; exact Sn.conj' y hx

Depends on / 依赖: Sn.conj, mul_assoc
-/
theorem IsNormal.vertexSubgroup (Sn : IsNormal S) (c : C) (cS : c in S.objs) :
    (S.vertexSubgroup cS).Normal where
  conj_mem x hx y := by rw [mul_assoc]; exact Sn.conj' y hx

section GeneratedSubgroupoid

-- TODO: proof that generated is just "words in X" and generatedNormal is similarly
variable (X : forall c d : C, Set (c ⟶ d))

/--
Definition of `generated` / `generated` 的定义

English:
definition generated
  signature: : Subgroupoid C
  body: sInf {S : Subgroupoid C | forall c d, X c d subseteq S.arrows c d}

中文:
定义 generated
  签名: : Subgroupoid C
  定义体: sInf {S : Subgroupoid C | forall c d, X c d subseteq S.arrows c d}

Depends on / 依赖: S.arrows, Subgroupoid, arrows, subseteq
-/
def generated : Subgroupoid C :=
  sInf {S : Subgroupoid C | forall c d, X c d subseteq S.arrows c d}

/--
theorem `subset_generated` / 定理 `subset_generated`

English:
theorem subset_generated
  given: (c d : C)
  statement: X c d subseteq (generated X).arrows c d
  proof: by
  dsimp only [generated, sInf]
  simp only [subset_iInter₂_iff]
  exact fun S hS f fS => hS _ _ fS

中文:
定理 subset_generated
  条件: (c d : C)
  结论: X c d subseteq (generated X).arrows c d
  证明: by
  dsimp only [generated, sInf]
  simp only [subset_iInter₂_iff]
  exact fun S hS f fS => hS _ _ fS

Depends on / 依赖: generated
-/
theorem subset_generated (c d : C) : X c d subseteq (generated X).arrows c d := by
  dsimp only [generated, sInf]
  simp only [subset_iInter₂_iff]
  exact fun S hS f fS => hS _ _ fS

/--
Definition of `generatedNormal` / `generatedNormal` 的定义

English:
definition generatedNormal
  signature: : Subgroupoid C
  body: sInf {S : Subgroupoid C | (forall c d, X c d subseteq S.arrows c d) ∧ S.IsNormal}

中文:
定义 generatedNormal
  签名: : Subgroupoid C
  定义体: sInf {S : Subgroupoid C | (forall c d, X c d subseteq S.arrows c d) ∧ S.IsNormal}

Depends on / 依赖: IsNormal, S.IsNormal, S.arrows, Subgroupoid, arrows, subseteq
-/
def generatedNormal : Subgroupoid C :=
  sInf {S : Subgroupoid C | (forall c d, X c d subseteq S.arrows c d) ∧ S.IsNormal}

/--
theorem `generated_le_generatedNormal` / 定理 `generated_le_generatedNormal`

English:
theorem generated_le_generatedNormal
  statement: generated X <= generatedNormal X
  proof: by
  apply @sInf_le_sInf (Subgroupoid C) _
  exact fun S ⟨h, _⟩ => h

中文:
定理 generated_le_generatedNormal
  结论: generated X <= generatedNormal X
  证明: by
  apply @sInf_le_sInf (Subgroupoid C) _
  exact fun S ⟨h, _⟩ => h

Depends on / 依赖: Subgroupoid, sInf_le_sInf
-/
theorem generated_le_generatedNormal : generated X <= generatedNormal X := by
  apply @sInf_le_sInf (Subgroupoid C) _
  exact fun S ⟨h, _⟩ => h

/--
theorem `generatedNormal_isNormal` / 定理 `generatedNormal_isNormal`

English:
theorem generatedNormal_isNormal
  statement: (generatedNormal X).IsNormal
  proof: sInf_isNormal _ fun _ h => h.right

中文:
定理 generatedNormal_isNormal
  结论: (generatedNormal X).IsNormal
  证明: sInf_isNormal _ fun _ h => h.right

Depends on / 依赖: h.right, sInf_isNormal
-/
theorem generatedNormal_isNormal : (generatedNormal X).IsNormal :=
  sInf_isNormal _ fun _ h => h.right

/--
theorem `IsNormal.generatedNormal_le` / 定理 `IsNormal.generatedNormal_le`

English:
theorem IsNormal.generatedNormal_le
  given: {S : Subgroupoid C} (Sn : S.IsNormal)
  proof: by
  constructor
  · rintro h c d
    have h' := generated_le_generatedNormal X
    rw [le_iff] at h h'
    exact ((subset_generated X c d).trans (@h' c d)).trans (@h c d)
  · rintro h
    apply @sInf_le (Subgroupoid C) _
    exact ⟨h, Sn⟩

中文:
定理 IsNormal.generatedNormal_le
  条件: {S : Subgroupoid C} (Sn : S.IsNormal)
  证明: by
  constructor
  · rintro h c d
    have h' := generated_le_generatedNormal X
    rw [le_iff] at h h'
    exact ((subset_generated X c d).trans (@h' c d)).trans (@h c d)
  · rintro h
    apply @sInf_le (Subgroupoid C) _
    exact ⟨h, Sn⟩

Depends on / 依赖: Subgroupoid, generated_le_generatedNormal, le_iff, sInf_le, subset_generated
-/
theorem IsNormal.generatedNormal_le {S : Subgroupoid C} (Sn : S.IsNormal) :
    generatedNormal X <= S ↔ forall c d, X c d subseteq S.arrows c d := by
  constructor
  · rintro h c d
    have h' := generated_le_generatedNormal X
    rw [le_iff] at h h'
    exact ((subset_generated X c d).trans (@h' c d)).trans (@h c d)
  · rintro h
    apply @sInf_le (Subgroupoid C) _
    exact ⟨h, Sn⟩

end GeneratedSubgroupoid

section Hom

variable {D : Type*} [Groupoid D] (φ : C ⥤ D)

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (S : Subgroupoid D)
  body: {f : c ⟶ d | φ.map f in S.arrows (φ.obj c) (φ.obj d)}
  inv hp := by rw [mem_ofPred, inv_eq_inv, φ.map_inv, ← inv_eq_inv]; exact S.inv hp
  mul := by
    intros
    simp only [mem_ofPred, Functor.map_comp]
    apply S.mul <;> assumption

@[gcongr]

中文:
定义 comap
  签名: (S : Subgroupoid D)
  定义体: {f : c ⟶ d | φ.map f in S.arrows (φ.obj c) (φ.obj d)}
  inv hp := by rw [mem_ofPred, inv_eq_inv, φ.map_inv, ← inv_eq_inv]; exact S.inv hp
  mul := by
    intros
    simp only [mem_ofPred, Functor.map_comp]
    apply S.mul <;> assumption

@[gcongr]

Depends on / 依赖: S.arrows, arrows
-/
def comap (S : Subgroupoid D) : Subgroupoid C where
  arrows c d := {f : c ⟶ d | φ.map f in S.arrows (φ.obj c) (φ.obj d)}
  inv hp := by rw [mem_ofPred, inv_eq_inv, φ.map_inv, ← inv_eq_inv]; exact S.inv hp
  mul := by
    intros
    simp only [mem_ofPred, Functor.map_comp]
    apply S.mul <;> assumption

@[gcongr]
/--
theorem `comap_mono` / 定理 `comap_mono`

English:
theorem comap_mono
  given: (S T : Subgroupoid D)
  statement: S <= T -> comap φ S <= comap φ T
  proof: fun ST _ =>
  @ST ⟨_, _, _⟩

中文:
定理 comap_mono
  条件: (S T : Subgroupoid D)
  结论: S <= T -> comap φ S <= comap φ T
  证明: fun ST _ =>
  @ST ⟨_, _, _⟩
-/
theorem comap_mono (S T : Subgroupoid D) : S <= T -> comap φ S <= comap φ T := fun ST _ =>
  @ST ⟨_, _, _⟩

/--
theorem `isNormal_comap` / 定理 `isNormal_comap`

English:
theorem isNormal_comap
  given: {S : Subgroupoid D} (Sn : IsNormal S)
  statement: IsNormal (comap φ S) where
  proof: by rw [comap, mem_ofPred, Functor.map_id]; apply Sn.wide
  conj f γ hγ := by
    simp_rw [inv_eq_inv f, comap, mem_ofPred, Functor.map_comp, Functor.map_inv, ← inv_eq_inv]
    exact Sn.conj _ hγ

@[simp]

中文:
定理 isNormal_comap
  条件: {S : Subgroupoid D} (Sn : IsNormal S)
  结论: IsNormal (comap φ S) where
  证明: by rw [comap, mem_ofPred, Functor.map_id]; apply Sn.wide
  conj f γ hγ := by
    simp_rw [inv_eq_inv f, comap, mem_ofPred, Functor.map_comp, Functor.map_inv, ← inv_eq_inv]
    exact Sn.conj _ hγ

@[simp]

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_id, Functor.map_inv, Sn.conj, Sn.wide, inv_eq_inv, map_comp, map_id, map_inv, mem_ofPred, simp_rw
-/
theorem isNormal_comap {S : Subgroupoid D} (Sn : IsNormal S) : IsNormal (comap φ S) where
  wide c := by rw [comap, mem_ofPred, Functor.map_id]; apply Sn.wide
  conj f γ hγ := by
    simp_rw [inv_eq_inv f, comap, mem_ofPred, Functor.map_comp, Functor.map_inv, ← inv_eq_inv]
    exact Sn.conj _ hγ

@[simp]
/--
theorem `comap_comp` / 定理 `comap_comp`

English:
theorem comap_comp
  given: {E : Type*} [Groupoid E] (ψ : D ⥤ E)
  statement: comap (φ ⋙ ψ) = comap φ ∘ comap ψ
  proof: rfl

中文:
定理 comap_comp
  条件: {E : 类型} [Groupoid E] (ψ : D ⥤ E)
  结论: comap (φ ⋙ ψ) = comap φ ∘ comap ψ
  证明: rfl
-/
theorem comap_comp {E : Type*} [Groupoid E] (ψ : D ⥤ E) : comap (φ ⋙ ψ) = comap φ ∘ comap ψ :=
  rfl

/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: : Subgroupoid C
  body: comap φ discrete

中文:
定义 ker
  签名: : Subgroupoid C
  定义体: comap φ discrete

Depends on / 依赖: discrete
-/
def ker : Subgroupoid C :=
  comap φ discrete

/--
theorem `mem_ker_iff` / 定理 `mem_ker_iff`

English:
theorem mem_ker_iff
  given: {c d : C} (f : c ⟶ d)
  proof: mem_discrete_iff (φ.map f)

中文:
定理 mem_ker_iff
  条件: {c d : C} (f : c ⟶ d)
  证明: mem_discrete_iff (φ.map f)

Depends on / 依赖: mem_discrete_iff
-/
theorem mem_ker_iff {c d : C} (f : c ⟶ d) :
    f in (ker φ).arrows c d ↔ exists h : φ.obj c = φ.obj d, φ.map f = eqToHom h :=
  mem_discrete_iff (φ.map f)

/--
theorem `ker_isNormal` / 定理 `ker_isNormal`

English:
theorem ker_isNormal
  statement: (ker φ).IsNormal
  proof: isNormal_comap φ discrete_isNormal

@[simp]

中文:
定理 ker_isNormal
  结论: (ker φ).IsNormal
  证明: isNormal_comap φ discrete_isNormal

@[simp]

Depends on / 依赖: discrete_isNormal, isNormal_comap
-/
theorem ker_isNormal : (ker φ).IsNormal :=
  isNormal_comap φ discrete_isNormal

@[simp]
/--
theorem `ker_comp` / 定理 `ker_comp`

English:
theorem ker_comp
  given: {E : Type*} [Groupoid E] (ψ : D ⥤ E)
  statement: ker (φ ⋙ ψ) = comap φ (ker ψ)
  proof: rfl

中文:
定理 ker_comp
  条件: {E : 类型} [Groupoid E] (ψ : D ⥤ E)
  结论: ker (φ ⋙ ψ) = comap φ (ker ψ)
  证明: rfl
-/
theorem ker_comp {E : Type*} [Groupoid E] (ψ : D ⥤ E) : ker (φ ⋙ ψ) = comap φ (ker ψ) :=
  rfl

/--
Inductive type `Map.Arrows` / 归纳类型 `Map.Arrows`

English:
inductive Map.Arrows
  parameters: (hφ : Function.Injective φ.obj) (S : Subgroupoid C)
  constructors (1):
    - im: {c d : C} (f : c ⟶ d) (hf : f in S.arrows c d) : Map.Arrows hφ S (φ.obj c) (φ.obj d) (φ.map f)

中文:
归纳类型 Map.Arrows
  参数: (hφ : Function.Injective φ.obj) (S : Subgroupoid C)
  构造子 (1 个):
    - im: {c d : C} (f : c ⟶ d) (hf : f in S.arrows c d) : Map.Arrows hφ S (φ.obj c) (φ.obj d) (φ.map f)
-/
inductive Map.Arrows (hφ : Function.Injective φ.obj) (S : Subgroupoid C) : forall c d : D, (c ⟶ d) -> Prop
  | im {c d : C} (f : c ⟶ d) (hf : f in S.arrows c d) : Map.Arrows hφ S (φ.obj c) (φ.obj d) (φ.map f)

/--
theorem `Map.arrows_iff` / 定理 `Map.arrows_iff`

English:
theorem Map.arrows_iff
  given: (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d)
  proof: by
  constructor
  · rintro ⟨g, hg⟩; exact ⟨_, _, g, rfl, rfl, hg, eq_conj_eqToHom _⟩
  · rintro ⟨a, b, g, rfl, rfl, hg, rfl⟩; rw [← eq_conj_eqToHom]; constructor; exact hg

中文:
定理 Map.arrows_iff
  条件: (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d)
  证明: by
  constructor
  · rintro ⟨g, hg⟩; exact ⟨_, _, g, rfl, rfl, hg, eq_conj_eqToHom _⟩
  · rintro ⟨a, b, g, rfl, rfl, hg, rfl⟩; rw [← eq_conj_eqToHom]; constructor; exact hg

Depends on / 依赖: eq_conj_eqToHom
-/
theorem Map.arrows_iff (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d) :
    Map.Arrows φ hφ S c d f ↔
      exists (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d) (_hg : g in S.arrows a b),
        f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb := by
  constructor
  · rintro ⟨g, hg⟩; exact ⟨_, _, g, rfl, rfl, hg, eq_conj_eqToHom _⟩
  · rintro ⟨a, b, g, rfl, rfl, hg, rfl⟩; rw [← eq_conj_eqToHom]; constructor; exact hg

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (hφ : Function.Injective φ.obj) (S : Subgroupoid C)
  body: {x | Map.Arrows φ hφ S c d x}
  inv := by
    rintro _ _ _ ⟨⟩
    rw [inv_eq_inv]; rw [← Functor.map_inv]; rw [← inv_eq_inv]
    constructor; apply S.inv; assumption
  mul := by
    rintro _ _ _ _ ⟨f, hf⟩ q hq
    obtain ⟨c₃, c₄, g, he, rfl, hg, gq⟩ := (Map.arrows_iff φ hφ S q).mp hq
    cases hφ he

中文:
定义 map
  签名: (hφ : Function.Injective φ.obj) (S : Subgroupoid C)
  定义体: {x | Map.Arrows φ hφ S c d x}
  inv := by
    rintro _ _ _ ⟨⟩
    rw [inv_eq_inv]; rw [← Functor.map_inv]; rw [← inv_eq_inv]
    constructor; apply S.inv; assumption
  mul := by
    rintro _ _ _ _ ⟨f, hf⟩ q hq
    obtain ⟨c₃, c₄, g, he, rfl, hg, gq⟩ := (Map.arrows_iff φ hφ S q).mp hq
    cases hφ he

Depends on / 依赖: Arrows, Map.Arrows
-/
def map (hφ : Function.Injective φ.obj) (S : Subgroupoid C) : Subgroupoid D where
  arrows c d := {x | Map.Arrows φ hφ S c d x}
  inv := by
    rintro _ _ _ ⟨⟩
    rw [inv_eq_inv]; rw [← Functor.map_inv]; rw [← inv_eq_inv]
    constructor; apply S.inv; assumption
  mul := by
    rintro _ _ _ _ ⟨f, hf⟩ q hq
    obtain ⟨c₃, c₄, g, he, rfl, hg, gq⟩ := (Map.arrows_iff φ hφ S q).mp hq
    cases hφ he; rw [gq, ← eq_conj_eqToHom, ← φ.map_comp]
    constructor; exact S.mul hf hg

/--
theorem `mem_map_iff` / 定理 `mem_map_iff`

English:
theorem mem_map_iff
  given: (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d)
  proof: Map.arrows_iff φ hφ S f

中文:
定理 mem_map_iff
  条件: (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d)
  证明: Map.arrows_iff φ hφ S f

Depends on / 依赖: Map.arrows_iff, arrows_iff
-/
theorem mem_map_iff (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d) :
    f in (map φ hφ S).arrows c d ↔
      exists (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d) (_hg : g in S.arrows a b),
        f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb :=
  Map.arrows_iff φ hφ S f

/--
theorem `galoisConnection_map_comap` / 定理 `galoisConnection_map_comap`

English:
theorem galoisConnection_map_comap
  given: (hφ : Function.Injective φ.obj)
  proof: by
  rintro S T; simp_rw [le_iff]; constructor
  · exact fun h c d f fS => h (Map.Arrows.im f fS)
  · rintro h _ _ g ⟨a, gφS⟩
    exact h gφS

中文:
定理 galoisConnection_map_comap
  条件: (hφ : Function.Injective φ.obj)
  证明: by
  rintro S T; simp_rw [le_iff]; constructor
  · exact fun h c d f fS => h (Map.Arrows.im f fS)
  · rintro h _ _ g ⟨a, gφS⟩
    exact h gφS

Depends on / 依赖: Arrows, Map.Arrows.im, le_iff, simp_rw
-/
theorem galoisConnection_map_comap (hφ : Function.Injective φ.obj) :
    GaloisConnection (map φ hφ) (comap φ) := by
  rintro S T; simp_rw [le_iff]; constructor
  · exact fun h c d f fS => h (Map.Arrows.im f fS)
  · rintro h _ _ g ⟨a, gφS⟩
    exact h gφS

/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: (hφ : Function.Injective φ.obj) (S T : Subgroupoid C)
  proof: fun h => (galoisConnection_map_comap φ hφ).monotone_l h

中文:
定理 map_mono
  条件: (hφ : Function.Injective φ.obj) (S T : Subgroupoid C)
  证明: fun h => (galoisConnection_map_comap φ hφ).monotone_l h

Depends on / 依赖: galoisConnection_map_comap, monotone_l
-/
theorem map_mono (hφ : Function.Injective φ.obj) (S T : Subgroupoid C) :
    S <= T -> map φ hφ S <= map φ hφ T := fun h => (galoisConnection_map_comap φ hφ).monotone_l h

/--
theorem `le_comap_map` / 定理 `le_comap_map`

English:
theorem le_comap_map
  given: (hφ : Function.Injective φ.obj) (S : Subgroupoid C)
  proof: (galoisConnection_map_comap φ hφ).le_u_l S

中文:
定理 le_comap_map
  条件: (hφ : Function.Injective φ.obj) (S : Subgroupoid C)
  证明: (galoisConnection_map_comap φ hφ).le_u_l S

Depends on / 依赖: galoisConnection_map_comap, le_u_l
-/
theorem le_comap_map (hφ : Function.Injective φ.obj) (S : Subgroupoid C) :
    S <= comap φ (map φ hφ S) :=
  (galoisConnection_map_comap φ hφ).le_u_l S

/--
theorem `map_comap_le` / 定理 `map_comap_le`

English:
theorem map_comap_le
  given: (hφ : Function.Injective φ.obj) (T : Subgroupoid D)
  proof: (galoisConnection_map_comap φ hφ).l_u_le T

中文:
定理 map_comap_le
  条件: (hφ : Function.Injective φ.obj) (T : Subgroupoid D)
  证明: (galoisConnection_map_comap φ hφ).l_u_le T

Depends on / 依赖: galoisConnection_map_comap, l_u_le
-/
theorem map_comap_le (hφ : Function.Injective φ.obj) (T : Subgroupoid D) :
    map φ hφ (comap φ T) <= T :=
  (galoisConnection_map_comap φ hφ).l_u_le T

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  statement: (hφ : Function.Injective φ.obj) (S : Subgroupoid C)
  proof: (galoisConnection_map_comap φ hφ).le_iff_le

中文:
定理 map_le_iff_le_comap
  结论: (hφ : Function.Injective φ.obj) (S : Subgroupoid C)
  证明: (galoisConnection_map_comap φ hφ).le_iff_le

Depends on / 依赖: galoisConnection_map_comap, le_iff_le
-/
theorem map_le_iff_le_comap (hφ : Function.Injective φ.obj) (S : Subgroupoid C)
    (T : Subgroupoid D) : map φ hφ S <= T ↔ S <= comap φ T :=
  (galoisConnection_map_comap φ hφ).le_iff_le

/--
theorem `mem_map_objs_iff` / 定理 `mem_map_objs_iff`

English:
theorem mem_map_objs_iff
  given: (hφ : Function.Injective φ.obj) (d : D)
  proof: by
  dsimp [objs, map]
  constructor
  · rintro ⟨f, hf⟩
    change Map.Arrows φ hφ S d d f at hf; rw [Map.arrows_iff] at hf
    obtain ⟨c, d, g, ec, ed, eg, gS, eg⟩ := hf
    exact ⟨c, ⟨mem_objs_of_src S eg, ec⟩⟩
  · rintro ⟨c, ⟨γ, γS⟩, rfl⟩
    exact ⟨φ.map γ, ⟨γ, γS⟩⟩

@[simp]

中文:
定理 mem_map_objs_iff
  条件: (hφ : Function.Injective φ.obj) (d : D)
  证明: by
  dsimp [objs, map]
  constructor
  · rintro ⟨f, hf⟩
    change Map.Arrows φ hφ S d d f at hf; rw [Map.arrows_iff] at hf
    obtain ⟨c, d, g, ec, ed, eg, gS, eg⟩ := hf
    exact ⟨c, ⟨mem_objs_of_src S eg, ec⟩⟩
  · rintro ⟨c, ⟨γ, γS⟩, rfl⟩
    exact ⟨φ.map γ, ⟨γ, γS⟩⟩

@[simp]

Depends on / 依赖: Arrows, Map.Arrows, Map.arrows_iff, arrows_iff, mem_objs_of_src
-/
theorem mem_map_objs_iff (hφ : Function.Injective φ.obj) (d : D) :
    d in (map φ hφ S).objs ↔ exists c in S.objs, φ.obj c = d := by
  dsimp [objs, map]
  constructor
  · rintro ⟨f, hf⟩
    change Map.Arrows φ hφ S d d f at hf; rw [Map.arrows_iff] at hf
    obtain ⟨c, d, g, ec, ed, eg, gS, eg⟩ := hf
    exact ⟨c, ⟨mem_objs_of_src S eg, ec⟩⟩
  · rintro ⟨c, ⟨γ, γS⟩, rfl⟩
    exact ⟨φ.map γ, ⟨γ, γS⟩⟩

@[simp]
/--
theorem `map_objs_eq` / 定理 `map_objs_eq`

English:
theorem map_objs_eq
  given: (hφ : Function.Injective φ.obj)
  statement: (map φ hφ S).objs = φ.obj '' S.objs
  proof: by
  ext x; convert! mem_map_objs_iff S φ hφ x

中文:
定理 map_objs_eq
  条件: (hφ : Function.Injective φ.obj)
  结论: (map φ hφ S).objs = φ.obj '' S.objs
  证明: by
  ext x; convert! mem_map_objs_iff S φ hφ x

Depends on / 依赖: convert, mem_map_objs_iff
-/
theorem map_objs_eq (hφ : Function.Injective φ.obj) : (map φ hφ S).objs = φ.obj '' S.objs := by
  ext x; convert! mem_map_objs_iff S φ hφ x

/--
Definition of `im` / `im` 的定义

English:
definition im
  signature: (hφ : Function.Injective φ.obj)
  body: map φ hφ ⊤

中文:
定义 im
  签名: (hφ : Function.Injective φ.obj)
  定义体: map φ hφ ⊤
-/
def im (hφ : Function.Injective φ.obj) :=
  map φ hφ ⊤

/--
theorem `mem_im_iff` / 定理 `mem_im_iff`

English:
theorem mem_im_iff
  given: (hφ : Function.Injective φ.obj) {c d : D} (f : c ⟶ d)
  proof: by
  convert! Map.arrows_iff φ hφ ⊤ f; simp only [Top.top, mem_univ, exists_true_left]

中文:
定理 mem_im_iff
  条件: (hφ : Function.Injective φ.obj) {c d : D} (f : c ⟶ d)
  证明: by
  convert! Map.arrows_iff φ hφ ⊤ f; simp only [Top.top, mem_univ, exists_true_left]

Depends on / 依赖: Map.arrows_iff, Top.top, arrows_iff, convert, exists_true_left, mem_univ
-/
theorem mem_im_iff (hφ : Function.Injective φ.obj) {c d : D} (f : c ⟶ d) :
    f in (im φ hφ).arrows c d ↔
      exists (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d),
        f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb := by
  convert! Map.arrows_iff φ hφ ⊤ f; simp only [Top.top, mem_univ, exists_true_left]

/--
theorem `mem_im_objs_iff` / 定理 `mem_im_objs_iff`

English:
theorem mem_im_objs_iff
  given: (hφ : Function.Injective φ.obj) (d : D)
  proof: by
  simp only [im, mem_map_objs_iff, mem_top_objs, true_and]

中文:
定理 mem_im_objs_iff
  条件: (hφ : Function.Injective φ.obj) (d : D)
  证明: by
  simp only [im, mem_map_objs_iff, mem_top_objs, true_and]

Depends on / 依赖: mem_map_objs_iff, mem_top_objs, true_and
-/
theorem mem_im_objs_iff (hφ : Function.Injective φ.obj) (d : D) :
    d in (im φ hφ).objs ↔ exists c : C, φ.obj c = d := by
  simp only [im, mem_map_objs_iff, mem_top_objs, true_and]

/--
theorem `obj_surjective_of_im_eq_top` / 定理 `obj_surjective_of_im_eq_top`

English:
theorem obj_surjective_of_im_eq_top
  given: (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤)
  proof: by
  rintro d
  rw [← mem_im_objs_iff _ hφ]; rw [hφ']
  apply mem_top_objs

中文:
定理 obj_surjective_of_im_eq_top
  条件: (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤)
  证明: by
  rintro d
  rw [← mem_im_objs_iff _ hφ]; rw [hφ']
  apply mem_top_objs

Depends on / 依赖: mem_im_objs_iff, mem_top_objs
-/
theorem obj_surjective_of_im_eq_top (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤) :
    Function.Surjective φ.obj := by
  rintro d
  rw [← mem_im_objs_iff _ hφ]; rw [hφ']
  apply mem_top_objs

/--
theorem `isNormal_map` / 定理 `isNormal_map`

English:
theorem isNormal_map
  given: (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤) (Sn : S.IsNormal)
  proof: { wide := fun d => by
      obtain ⟨c, rfl⟩ := obj_surjective_of_im_eq_top φ hφ hφ' d
      change Map.Arrows φ hφ S _ _ (𝟙 _); rw [← Functor.map_id]
      constructor; exact Sn.wide c
    conj := fun {d d'} g δ hδ => by
      rw [mem_map_iff] at hδ
      obtain ⟨c, c', γ, cd, cd', γS, hγ⟩ := hδ; su

中文:
定理 isNormal_map
  条件: (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤) (Sn : S.IsNormal)
  证明: { wide := fun d => by
      obtain ⟨c, rfl⟩ := obj_surjective_of_im_eq_top φ hφ hφ' d
      change Map.Arrows φ hφ S _ _ (𝟙 _); rw [← Functor.map_id]
      constructor; exact Sn.wide c
    conj := fun {d d'} g δ hδ => by
      rw [mem_map_iff] at hδ
      obtain ⟨c, c', γ, cd, cd', γS, hγ⟩ := hδ; su

Depends on / 依赖: Arrows, Functor, Functor.map_id, Map.Arrows, Sn.wide, arrows, map_id, mem_im_iff, mem_im_objs_iff, mem_map_iff, mem_top_objs, obj_surjective_of_im_eq_top
-/
theorem isNormal_map (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤) (Sn : S.IsNormal) :
    (map φ hφ S).IsNormal :=
  { wide := fun d => by
      obtain ⟨c, rfl⟩ := obj_surjective_of_im_eq_top φ hφ hφ' d
      change Map.Arrows φ hφ S _ _ (𝟙 _); rw [← Functor.map_id]
      constructor; exact Sn.wide c
    conj := fun {d d'} g δ hδ => by
      rw [mem_map_iff] at hδ
      obtain ⟨c, c', γ, cd, cd', γS, hγ⟩ := hδ; subst_vars; cases hφ cd'
      have : d' in (im φ hφ).objs := by rw [hφ']; apply mem_top_objs
      rw [mem_im_objs_iff] at this
      obtain ⟨c', rfl⟩ := this
      have : g in (im φ hφ).arrows (φ.obj c) (φ.obj c') := by rw [hφ']; trivial
      rw [mem_im_iff] at this
      obtain ⟨b, b', f, hb, hb', _, hf⟩ := this; cases hφ hb; cases hφ hb'
      change Map.Arrows φ hφ S (φ.obj c') (φ.obj c') _
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp, inv_eq_inv]
      suffices Map.Arrows φ hφ S (φ.obj c') (φ.obj c') (φ.map <| Groupoid.inv f ≫ γ ≫ f) by
        simp only [inv_eq_inv, Functor.map_comp, Functor.map_inv] at this; exact this
      constructor; apply Sn.conj f γS }

end Hom

section Thin

/--
Definition of `IsThin` / `IsThin` 的定义

English:
abbreviation IsThin
  body: Quiver.IsThin S.objs

nonrec theorem isThin_iff : S.IsThin ↔ forall c : S.objs, Subsingleton (S.arrows c c) := isThin_iff _

中文:
缩写 IsThin
  定义体: Quiver.IsThin S.objs

nonrec theorem isThin_iff : S.IsThin ↔ forall c : S.objs, Subsingleton (S.arrows c c) := isThin_iff _

Depends on / 依赖: IsThin, Quiver, Quiver.IsThin, S.objs
-/
abbrev IsThin :=
  Quiver.IsThin S.objs

nonrec theorem isThin_iff : S.IsThin ↔ forall c : S.objs, Subsingleton (S.arrows c c) := isThin_iff _

end Thin

section Disconnected

/-- A subgroupoid `IsTotallyDisconnected` if it has only isotropy arrows. -/
nonrec abbrev IsTotallyDisconnected :=
  IsTotallyDisconnected S.objs

/--
theorem `isTotallyDisconnected_iff` / 定理 `isTotallyDisconnected_iff`

English:
theorem isTotallyDisconnected_iff
  proof: by
  constructor
  · rintro h c d ⟨f, fS⟩
exact congr_arg Subtype.val h ⟨c, mem_objs_of_src S fS⟩ ⟨d, mem_objs_of_tgt S fS⟩ ⟨f, fS⟩
  · rintro h ⟨c, hc⟩ ⟨d, hd⟩ ⟨f, fS⟩
    simp only [Subtype.mk_eq_mk]
    exact h c d ⟨f, fS⟩

中文:
定理 isTotallyDisconnected_iff
  证明: by
  constructor
  · rintro h c d ⟨f, fS⟩
exact congr_arg Subtype.val h ⟨c, mem_objs_of_src S fS⟩ ⟨d, mem_objs_of_tgt S fS⟩ ⟨f, fS⟩
  · rintro h ⟨c, hc⟩ ⟨d, hd⟩ ⟨f, fS⟩
    simp only [Subtype.mk_eq_mk]
    exact h c d ⟨f, fS⟩

Depends on / 依赖: Subtype, Subtype.mk_eq_mk, Subtype.val, congr_arg, mem_objs_of_src, mem_objs_of_tgt, mk_eq_mk
-/
theorem isTotallyDisconnected_iff :
    S.IsTotallyDisconnected ↔ forall c d, (S.arrows c d).Nonempty -> c = d := by
  constructor
  · rintro h c d ⟨f, fS⟩
exact congr_arg Subtype.val h ⟨c, mem_objs_of_src S fS⟩ ⟨d, mem_objs_of_tgt S fS⟩ ⟨f, fS⟩
  · rintro h ⟨c, hc⟩ ⟨d, hd⟩ ⟨f, fS⟩
    simp only [Subtype.mk_eq_mk]
    exact h c d ⟨f, fS⟩

/--
Definition of `disconnect` / `disconnect` 的定义

English:
definition disconnect
  signature: : Subgroupoid C where
  body: {f | c = d ∧ f in S.arrows c d}
  inv := by rintro _ _ _ ⟨rfl, h⟩; exact ⟨rfl, S.inv h⟩
  mul := by rintro _ _ _ _ ⟨rfl, h⟩ _ ⟨rfl, h'⟩; exact ⟨rfl, S.mul h h'⟩

中文:
定义 disconnect
  签名: : Subgroupoid C where
  定义体: {f | c = d ∧ f in S.arrows c d}
  inv := by rintro _ _ _ ⟨rfl, h⟩; exact ⟨rfl, S.inv h⟩
  mul := by rintro _ _ _ _ ⟨rfl, h⟩ _ ⟨rfl, h'⟩; exact ⟨rfl, S.mul h h'⟩

Depends on / 依赖: S.arrows, arrows
-/
def disconnect : Subgroupoid C where
  arrows c d := {f | c = d ∧ f in S.arrows c d}
  inv := by rintro _ _ _ ⟨rfl, h⟩; exact ⟨rfl, S.inv h⟩
  mul := by rintro _ _ _ _ ⟨rfl, h⟩ _ ⟨rfl, h'⟩; exact ⟨rfl, S.mul h h'⟩

/--
theorem `disconnect_le` / 定理 `disconnect_le`

English:
theorem disconnect_le
  statement: S.disconnect <= S
  proof: by rw [le_iff]; rintro _ _ _ ⟨⟩; assumption

中文:
定理 disconnect_le
  结论: S.disconnect <= S
  证明: by rw [le_iff]; rintro _ _ _ ⟨⟩; assumption

Depends on / 依赖: le_iff
-/
theorem disconnect_le : S.disconnect <= S := by rw [le_iff]; rintro _ _ _ ⟨⟩; assumption

/--
theorem `disconnect_normal` / 定理 `disconnect_normal`

English:
theorem disconnect_normal
  given: (Sn : S.IsNormal)
  statement: S.disconnect.IsNormal
  proof: { wide := fun c => ⟨rfl, Sn.wide c⟩
    conj := fun _ _ ⟨_, h'⟩ => ⟨rfl, Sn.conj _ h'⟩ }

@[simp]

中文:
定理 disconnect_normal
  条件: (Sn : S.IsNormal)
  结论: S.disconnect.IsNormal
  证明: { wide := fun c => ⟨rfl, Sn.wide c⟩
    conj := fun _ _ ⟨_, h'⟩ => ⟨rfl, Sn.conj _ h'⟩ }

@[simp]

Depends on / 依赖: Sn.conj, Sn.wide
-/
theorem disconnect_normal (Sn : S.IsNormal) : S.disconnect.IsNormal :=
  { wide := fun c => ⟨rfl, Sn.wide c⟩
    conj := fun _ _ ⟨_, h'⟩ => ⟨rfl, Sn.conj _ h'⟩ }

@[simp]
/--
theorem `mem_disconnect_objs_iff` / 定理 `mem_disconnect_objs_iff`

English:
theorem mem_disconnect_objs_iff
  given: {c : C}
  statement: c in S.disconnect.objs ↔ c in S.objs
  proof: ⟨fun ⟨γ, _, γS⟩ => ⟨γ, γS⟩, fun ⟨γ, γS⟩ => ⟨γ, rfl, γS⟩⟩

中文:
定理 mem_disconnect_objs_iff
  条件: {c : C}
  结论: c in S.disconnect.objs ↔ c in S.objs
  证明: ⟨fun ⟨γ, _, γS⟩ => ⟨γ, γS⟩, fun ⟨γ, γS⟩ => ⟨γ, rfl, γS⟩⟩
-/
theorem mem_disconnect_objs_iff {c : C} : c in S.disconnect.objs ↔ c in S.objs :=
  ⟨fun ⟨γ, _, γS⟩ => ⟨γ, γS⟩, fun ⟨γ, γS⟩ => ⟨γ, rfl, γS⟩⟩

/--
theorem `disconnect_objs` / 定理 `disconnect_objs`

English:
theorem disconnect_objs
  statement: S.disconnect.objs = S.objs
  proof: Set.ext fun _ => mem_disconnect_objs_iff _

中文:
定理 disconnect_objs
  结论: S.disconnect.objs = S.objs
  证明: Set.ext fun _ => mem_disconnect_objs_iff _

Depends on / 依赖: Set.ext, mem_disconnect_objs_iff
-/
theorem disconnect_objs : S.disconnect.objs = S.objs := Set.ext fun _ => mem_disconnect_objs_iff _

/--
theorem `disconnect_isTotallyDisconnected` / 定理 `disconnect_isTotallyDisconnected`

English:
theorem disconnect_isTotallyDisconnected
  statement: S.disconnect.IsTotallyDisconnected
  proof: by
  rw [isTotallyDisconnected_iff]; exact fun c d ⟨_, h, _⟩ => h

中文:
定理 disconnect_isTotallyDisconnected
  结论: S.disconnect.IsTotallyDisconnected
  证明: by
  rw [isTotallyDisconnected_iff]; exact fun c d ⟨_, h, _⟩ => h

Depends on / 依赖: isTotallyDisconnected_iff
-/
theorem disconnect_isTotallyDisconnected : S.disconnect.IsTotallyDisconnected := by
  rw [isTotallyDisconnected_iff]; exact fun c d ⟨_, h, _⟩ => h

end Disconnected

section Full

variable (D : Set C)

/--
Definition of `full` / `full` 的定义

English:
definition full
  signature: : Subgroupoid C where
  body: {_f | c in D ∧ d in D}
  inv := by rintro _ _ _ ⟨⟩; constructor <;> assumption
  mul := by rintro _ _ _ _ ⟨⟩ _ ⟨⟩; constructor <;> assumption

中文:
定义 full
  签名: : Subgroupoid C where
  定义体: {_f | c in D ∧ d in D}
  inv := by rintro _ _ _ ⟨⟩; constructor <;> assumption
  mul := by rintro _ _ _ _ ⟨⟩ _ ⟨⟩; constructor <;> assumption
-/
def full : Subgroupoid C where
  arrows c d := {_f | c in D ∧ d in D}
  inv := by rintro _ _ _ ⟨⟩; constructor <;> assumption
  mul := by rintro _ _ _ _ ⟨⟩ _ ⟨⟩; constructor <;> assumption

/--
theorem `full_objs` / 定理 `full_objs`

English:
theorem full_objs
  statement: (full D).objs = D
  proof: Set.ext fun _ => ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨𝟙 _, h, h⟩⟩

@[simp]

中文:
定理 full_objs
  结论: (full D).objs = D
  证明: Set.ext fun _ => ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨𝟙 _, h, h⟩⟩

@[simp]

Depends on / 依赖: Set.ext
-/
theorem full_objs : (full D).objs = D :=
  Set.ext fun _ => ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨𝟙 _, h, h⟩⟩

@[simp]
/--
theorem `mem_full_iff` / 定理 `mem_full_iff`

English:
theorem mem_full_iff
  given: {c d : C} {f : c ⟶ d}
  statement: f in (full D).arrows c d ↔ c in D ∧ d in D
  proof: Iff.rfl

@[simp]

中文:
定理 mem_full_iff
  条件: {c d : C} {f : c ⟶ d}
  结论: f in (full D).arrows c d ↔ c in D ∧ d in D
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_full_iff {c d : C} {f : c ⟶ d} : f in (full D).arrows c d ↔ c in D ∧ d in D :=
  Iff.rfl

@[simp]
/--
theorem `mem_full_objs_iff` / 定理 `mem_full_objs_iff`

English:
theorem mem_full_objs_iff
  given: {c : C}
  statement: c in (full D).objs ↔ c in D
  proof: by rw [full_objs]

@[simp]

中文:
定理 mem_full_objs_iff
  条件: {c : C}
  结论: c in (full D).objs ↔ c in D
  证明: by rw [full_objs]

@[simp]

Depends on / 依赖: full_objs
-/
theorem mem_full_objs_iff {c : C} : c in (full D).objs ↔ c in D := by rw [full_objs]

@[simp]
/--
theorem `full_empty` / 定理 `full_empty`

English:
theorem full_empty
  statement: full ∅ = (⊥ : Subgroupoid C)
  proof: by
  ext
  simp only [Bot.bot, mem_full_iff, mem_empty_iff_false, and_self_iff]

@[simp]

中文:
定理 full_empty
  结论: full ∅ = (⊥ : Subgroupoid C)
  证明: by
  ext
  simp only [Bot.bot, mem_full_iff, mem_empty_iff_false, and_self_iff]

@[simp]

Depends on / 依赖: Bot.bot, and_self_iff, mem_empty_iff_false, mem_full_iff
-/
theorem full_empty : full ∅ = (⊥ : Subgroupoid C) := by
  ext
  simp only [Bot.bot, mem_full_iff, mem_empty_iff_false, and_self_iff]

@[simp]
/--
theorem `full_univ` / 定理 `full_univ`

English:
theorem full_univ
  statement: full Set.univ = (⊤ : Subgroupoid C)
  proof: by
  ext
  simp only [mem_full_iff, mem_univ, and_self, mem_top]

中文:
定理 full_univ
  结论: full Set.univ = (⊤ : Subgroupoid C)
  证明: by
  ext
  simp only [mem_full_iff, mem_univ, and_self, mem_top]

Depends on / 依赖: and_self, mem_full_iff, mem_top, mem_univ
-/
theorem full_univ : full Set.univ = (⊤ : Subgroupoid C) := by
  ext
  simp only [mem_full_iff, mem_univ, and_self, mem_top]

/--
theorem `full_mono` / 定理 `full_mono`

English:
theorem full_mono
  given: {D E : Set C} (h : D <= E)
  statement: full D <= full E
  proof: by
  rw [le_iff]
  rintro c d f
  simp only [mem_full_iff]
  exact fun ⟨hc, hd⟩ => ⟨h hc, h hd⟩

中文:
定理 full_mono
  条件: {D E : Set C} (h : D <= E)
  结论: full D <= full E
  证明: by
  rw [le_iff]
  rintro c d f
  simp only [mem_full_iff]
  exact fun ⟨hc, hd⟩ => ⟨h hc, h hd⟩

Depends on / 依赖: le_iff, mem_full_iff
-/
theorem full_mono {D E : Set C} (h : D <= E) : full D <= full E := by
  rw [le_iff]
  rintro c d f
  simp only [mem_full_iff]
  exact fun ⟨hc, hd⟩ => ⟨h hc, h hd⟩

/--
theorem `full_arrow_eq_iff` / 定理 `full_arrow_eq_iff`

English:
theorem full_arrow_eq_iff
  given: {c d : (full D).objs} {f g : c ⟶ d}
  proof: Subtype.ext_iff

中文:
定理 full_arrow_eq_iff
  条件: {c d : (full D).objs} {f g : c ⟶ d}
  证明: Subtype.ext_iff

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem full_arrow_eq_iff {c d : (full D).objs} {f g : c ⟶ d} :
    f = g ↔ f.1 = g.1 :=
  Subtype.ext_iff

end Full

end Subgroupoid

end CategoryTheory
