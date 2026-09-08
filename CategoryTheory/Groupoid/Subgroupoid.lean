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
/-
**CategoryTheory.Subgroupoid** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [CategoryTheory.Groupoid C] → Type (max u u_1)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroupoid of `C` consists of a choice of arrows for each pair of vertices, c
losed
under composition and inverses.
-/
structure Subgroupoid (C : Type u) [Groupoid C] where
  /-- The arrow choice for each pair of vertices -/
  arrows : ∀ c d : C, Set (c ⟶ d)
  protected inv : ∀ {c d} {p : c ⟶ d}, p ∈ arrows c d → Groupoid.inv p ∈ arrows d c
  protected mul : ∀ {c d e} {p}, p ∈ arrows c d → ∀ {q}, q ∈ arrows d e → p ≫ q ∈ arrows c e

namespace Subgroupoid

variable (S : Subgroupoid C)

/-
**CategoryTheory.Subgroupoid.inv_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Subgroupoid`。
形式化陈述：inv_mem_iff {c d : C} (f : c ⟶ d) : Groupoid.inv f in S.arrows d c ↔ f in 
S.arrows c d
参数：f : c ⟶ d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.IsIso.of_groupoid`：∀ {C : Type u} [inst : CategoryTheory.
Groupoid C] {X Y : C} (f : X ⟶ Y), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.Groupoid.inv_eq_inv`：∀ {C : Type u} [inst : CategoryTheor
y.Groupoid C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Groupoid.inv f = CategoryT
heory.inv f
· 使用定理 `CategoryTheory.IsIso.inv_inv`：inv_inv [IsIso f] : inv (inv f) = f
· 使用定理 `CategoryTheory.Subgroupoid.inv`：∀ {C : Type u} [inst : CategoryTheory.Gr
oupoid C] (self : CategoryTheory.Subgroupoid C) {c d : C} {p : c ⟶ d},   p ∈ sel
f.arrows c d → Categ…
-/
theorem inv_mem_iff {c d : C} (f : c ⟶ d) :
    Groupoid.inv f ∈ S.arrows d c ↔ f ∈ S.arrows c d := by
  constructor
  · intro h
    simpa only [inv_eq_inv, IsIso.inv_inv] using S.inv h
  · apply S.inv
/-
**CategoryTheory.Subgroupoid.mul_mem_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Subgroupoid`。
形式化陈述：mul_mem_cancel_left {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hf : f in S.arrow
s c d) : f ≫ g in S.arrows c e ↔ g in S.arrows d e
参数：hf : f in S.arrows c d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.mul`：∀ {C : Type u} [inst : CategoryTheory.Gr
oupoid C] (self : CategoryTheory.Subgroupoid C) {c d e : C} {p : c ⟶ d},   p ∈ s
elf.arrows c d → ∀ {…
· 使用定理 `CategoryTheory.Subgroupoid.inv`：∀ {C : Type u} [inst : CategoryTheory.Gr
oupoid C] (self : CategoryTheory.Subgroupoid C) {c d : C} {p : c ⟶ d},   p ∈ sel
f.arrows c d → Categ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.IsIso.of_groupoid`：∀ {C : Type u} [inst : CategoryTheory.
Groupoid C] {X Y : C} (f : X ⟶ Y), CategoryTheory.IsIso f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Groupoid.inv_eq_inv`：∀ {C : Type u} [inst : CategoryTheor
y.Groupoid C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Groupoid.inv f = CategoryT
heory.inv f
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
-/
theorem mul_mem_cancel_left {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hf : f ∈ S.arrows c d) :
    f ≫ g ∈ S.arrows c e ↔ g ∈ S.arrows d e := by
  constructor
  · rintro h
    suffices Groupoid.inv f ≫ f ≫ g ∈ S.arrows d e by
      simpa only [inv_eq_inv, IsIso.inv_hom_id_assoc] using this
    apply S.mul (S.inv hf) h
  · apply S.mul hf
/-
**CategoryTheory.Subgroupoid.mul_mem_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Subgroupoid`。
形式化陈述：mul_mem_cancel_right {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hg : g in S.arro
ws d e) : f ≫ g in S.arrows c e ↔ f in S.arrows c d
参数：hg : g in S.arrows d e。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.mul`：∀ {C : Type u} [inst : CategoryTheory.Gr
oupoid C] (self : CategoryTheory.Subgroupoid C) {c d e : C} {p : c ⟶ d},   p ∈ s
elf.arrows c d → ∀ {…
· 使用定理 `CategoryTheory.Subgroupoid.inv`：∀ {C : Type u} [inst : CategoryTheory.Gr
oupoid C] (self : CategoryTheory.Subgroupoid C) {c d : C} {p : c ⟶ d},   p ∈ sel
f.arrows c d → Categ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.IsIso.of_groupoid`：∀ {C : Type u} [inst : CategoryTheory.
Groupoid C] {X Y : C} (f : X ⟶ Y), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.Groupoid.inv_eq_inv`：∀ {C : Type u} [inst : CategoryTheor
y.Groupoid C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Groupoid.inv f = CategoryT
heory.inv f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem mul_mem_cancel_right {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hg : g ∈ S.arrows d e) :
    f ≫ g ∈ S.arrows c e ↔ f ∈ S.arrows c d := by
  constructor
  · rintro h
    suffices (f ≫ g) ≫ Groupoid.inv g ∈ S.arrows c d by
      simpa only [inv_eq_inv, IsIso.hom_inv_id, Category.comp_id, Category.assoc] using this
    apply S.mul h (S.inv hg)
  · exact fun hf => S.mul hf hg

/-- The vertices of `C` on which `S` has non-trivial isotropy -/
/-
**CategoryTheory.Subgroupoid.objs** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subg
roupoid`。
形式化陈述：objs : Set C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vertices of `C` on which `S` has non-trivial isotropy
-/
def objs : Set C :=
  {c : C | (S.arrows c c).Nonempty}
/-
**CategoryTheory.Subgroupoid.mem_objs_of_src** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Subgroupoid`。
形式化陈述：mem_objs_of_src {c d : C} {f : c ⟶ d} (h : f in S.arrows c d) : c in S.obj
s
参数：h : f in S.arrows c d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.mul`：∀ {C : Type u} [inst : CategoryTheory.Gr
oupoid C] (self : CategoryTheory.Subgroupoid C) {c d e : C} {p : c ⟶ d},   p ∈ s
elf.arrows c d → ∀ {…
· 使用定理 `CategoryTheory.Subgroupoid.inv`：∀ {C : Type u} [inst : CategoryTheory.Gr
oupoid C] (self : CategoryTheory.Subgroupoid C) {c d : C} {p : c ⟶ d},   p ∈ sel
f.arrows c d → Categ…
-/
theorem mem_objs_of_src {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : c ∈ S.objs :=
  ⟨f ≫ Groupoid.inv f, S.mul h (S.inv h)⟩
/-
**CategoryTheory.Subgroupoid.mem_objs_of_tgt** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Subgroupoid`。
形式化陈述：mem_objs_of_tgt {c d : C} {f : c ⟶ d} (h : f in S.arrows c d) : d in S.obj
s
参数：h : f in S.arrows c d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.mul`：∀ {C : Type u} [inst : CategoryTheory.Gr
oupoid C] (self : CategoryTheory.Subgroupoid C) {c d e : C} {p : c ⟶ d},   p ∈ s
elf.arrows c d → ∀ {…
· 使用定理 `CategoryTheory.Subgroupoid.inv`：∀ {C : Type u} [inst : CategoryTheory.Gr
oupoid C] (self : CategoryTheory.Subgroupoid C) {c d : C} {p : c ⟶ d},   p ∈ sel
f.arrows c d → Categ…
-/
theorem mem_objs_of_tgt {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : d ∈ S.objs :=
  ⟨Groupoid.inv f ≫ f, S.mul (S.inv h) h⟩
/-
**CategoryTheory.Subgroupoid.id_mem_of_nonempty_isotropy** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Subgroupoid`。
形式化陈述：id_mem_of_nonempty_isotropy (c : C) : c in objs S -> 𝟙 c in S.arrows c c
参数：c : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.of_groupoid`：∀ {C : Type u} [inst : CategoryTheory.
Groupoid C] {X Y : C} (f : X ⟶ Y), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.Groupoid.inv_eq_inv`：∀ {C : Type u} [inst : CategoryTheor
y.Groupoid C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Groupoid.inv f = CategoryT
heory.inv f
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Subgroupoid.mul`：∀ {C : Type u} [inst : CategoryTheory.Gr
oupoid C] (self : CategoryTheory.Subgroupoid C) {c d e : C} {p : c ⟶ d},   p ∈ s
elf.arrows c d → ∀ {…
· 使用定理 `CategoryTheory.Subgroupoid.inv`：∀ {C : Type u} [inst : CategoryTheory.Gr
oupoid C] (self : CategoryTheory.Subgroupoid C) {c d : C} {p : c ⟶ d},   p ∈ sel
f.arrows c d → Categ…
-/
theorem id_mem_of_nonempty_isotropy (c : C) : c ∈ objs S → 𝟙 c ∈ S.arrows c c := by
  rintro ⟨γ, hγ⟩
  convert! S.mul hγ (S.inv hγ)
  simp only [inv_eq_inv, IsIso.hom_inv_id]
/-
**CategoryTheory.Subgroupoid.id_mem_of_src** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Subgroupoid`。
形式化陈述：id_mem_of_src {c d : C} {f : c ⟶ d} (h : f in S.arrows c d) : 𝟙 c in S.arr
ows c c
参数：h : f in S.arrows c d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.id_mem_of_nonempty_isotropy`：id_mem_of_nonemp
ty_isotropy (c : C) : c in objs S -> 𝟙 c in S.arrows c c
· 使用定理 `CategoryTheory.Subgroupoid.mem_objs_of_src`：mem_objs_of_src {c d : C} {f
 : c ⟶ d} (h : f in S.arrows c d) : c in S.objs
-/
theorem id_mem_of_src {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : 𝟙 c ∈ S.arrows c c :=
  id_mem_of_nonempty_isotropy S c (mem_objs_of_src S h)
/-
**CategoryTheory.Subgroupoid.id_mem_of_tgt** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Subgroupoid`。
形式化陈述：id_mem_of_tgt {c d : C} {f : c ⟶ d} (h : f in S.arrows c d) : 𝟙 d in S.arr
ows d d
参数：h : f in S.arrows c d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.id_mem_of_nonempty_isotropy`：id_mem_of_nonemp
ty_isotropy (c : C) : c in objs S -> 𝟙 c in S.arrows c c
· 使用定理 `CategoryTheory.Subgroupoid.mem_objs_of_tgt`：mem_objs_of_tgt {c d : C} {f
 : c ⟶ d} (h : f in S.arrows c d) : d in S.objs
-/
theorem id_mem_of_tgt {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : 𝟙 d ∈ S.arrows d d :=
  id_mem_of_nonempty_isotropy S d (mem_objs_of_tgt S h)

/-- A subgroupoid seen as a quiver on vertex set `C` -/
@[instance_reducible]
/-
**CategoryTheory.Subgroupoid.asWideQuiver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Subgroupoid`。
形式化陈述：asWideQuiver : Quiver C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroupoid seen as a quiver on vertex set `C`
-/
def asWideQuiver : Quiver C :=
  ⟨fun c d => S.arrows c d⟩

/-- The coercion of a subgroupoid as a groupoid -/
@[simps comp_coe, simps -isSimp inv_coe]
/-
**CategoryTheory.Subgroupoid.coe** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subgr
oupoid`。
形式化陈述：coe : Groupoid S.objs where Hom a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion of a subgroupoid as a groupoid
-/
instance coe : Groupoid S.objs where
  Hom a b := S.arrows a.val b.val
  id a := ⟨𝟙 a.val, id_mem_of_nonempty_isotropy S a.val a.prop⟩
  comp p q := ⟨p.val ≫ q.val, S.mul p.prop q.prop⟩
  inv p := ⟨Groupoid.inv p.val, S.inv p.prop⟩

@[simp]
/-
**CategoryTheory.Subgroupoid.coe_inv_coe'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Subgroupoid`。
形式化陈述：coe_inv_coe' {c d : S.objs} (p : c ⟶ d) : (CategoryTheory.inv p).val = Cat
egoryTheory.inv p.val
参数：p : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.IsGroupoid.all_isIso`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.IsGroupoid C] {X Y : C} (f : X ⟶ Y)
,   CategoryTheory.IsIso …
· 使用定理 `CategoryTheory.instIsGroupoid`：∀ {C : Type u} [inst : CategoryTheory.Gro
upoid C], CategoryTheory.IsGroupoid C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_inv_coe' {c d : S.objs} (p : c ⟶ d) :
    (CategoryTheory.inv p).val = CategoryTheory.inv p.val := by
  simp only [← inv_eq_inv, coe_inv_coe]

/-- The embedding of the coerced subgroupoid to its parent -/
/-
**CategoryTheory.Subgroupoid.hom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subgr
oupoid`。
形式化陈述：hom : S.objs ⥤ C where obj c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of the coerced subgroupoid to its parent
-/
def hom : S.objs ⥤ C where
  obj c := c.val
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl
/-
**CategoryTheory.Subgroupoid.hom.inj_on_objects** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Subgroupoid.hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Groupoid C] (S : CategoryTheory.Subg
roupoid C), Function.Injective S.hom.obj
参数：S : CategoryTheory.Subgroupoid C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom.inj_on_objects : Function.Injective (hom S).obj := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
  simp only [Subtype.mk_eq_mk]; exact hcd
/-
**CategoryTheory.Subgroupoid.hom.faithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Subgroupoid.hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Groupoid C] (S : CategoryTheory.Subg
roupoid C) (c d : ↑S.objs),   Function.Injective fun f => S.hom.map f
参数：S : CategoryTheory.Subgroupoid C；c d : ↑S.objs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem hom.faithful : ∀ c d, Function.Injective fun f : c ⟶ d => (hom S).map f := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ ⟨f, hf⟩ ⟨g, hg⟩ hfg; exact Subtype.ext hfg

/-- The subgroup of the vertex group at `c` given by the subgroupoid -/
/-
**CategoryTheory.Subgroupoid.vertexSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Subgroupoid`。
形式化陈述：vertexSubgroup {c : C} (hc : c in S.objs) : Subgroup (c ⟶ c) where carrier
参数：hc : c in S.objs。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.mul`：∀ {C : Type u} [inst : CategoryTheory.Gr
oupoid C] (self : CategoryTheory.Subgroupoid C) {c d e : C} {p : c ⟶ d},   p ∈ s
elf.arrows c d → ∀ {…
· 使用定理 `CategoryTheory.Subgroupoid.id_mem_of_nonempty_isotropy`：id_mem_of_nonemp
ty_isotropy (c : C) : c in objs S -> 𝟙 c in S.arrows c c
· 使用定理 `CategoryTheory.Subgroupoid.inv`：∀ {C : Type u} [inst : CategoryTheory.Gr
oupoid C] (self : CategoryTheory.Subgroupoid C) {c d : C} {p : c ⟶ d},   p ∈ sel
f.arrows c d → Categ…

--- 原说明 ---
The subgroup of the vertex group at `c` given by the subgroupoid
-/
def vertexSubgroup {c : C} (hc : c ∈ S.objs) : Subgroup (c ⟶ c) where
  carrier := S.arrows c c
  mul_mem' hf hg := S.mul hf hg
  one_mem' := id_mem_of_nonempty_isotropy _ _ hc
  inv_mem' hf := S.inv hf

/-- The set of all arrows of a subgroupoid, as a set in `Σ c d : C, c ⟶ d`. -/
/-
**CategoryTheory.Subgroupoid.toSet** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sub
groupoid`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Groupoid C] → CategoryTheory.Subgrou
poid C → Set ((c : C) × (d : C) × (c ⟶ d))
参数：(c : C) × (d : C) × (c ⟶ d)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of all arrows of a subgroupoid, as a set in `Σ c d : C, c ⟶ d`.
-/
@[coe] def toSet (S : Subgroupoid C) : Set (Σ c d : C, c ⟶ d) :=
  {F | F.2.2 ∈ S.arrows F.1 F.2.1}
/-
**CategoryTheory.Subgroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subgroup
oid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Subgroupoid C) (Σ c d : C, c ⟶ d) where
  coe := toSet
  coe_injective := fun ⟨S, _, _⟩ ⟨T, _, _⟩ h => by ext c d f; apply Set.ext_iff.1 h ⟨c, d, f⟩
/-
**CategoryTheory.Subgroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subgroup
oid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Subgroupoid C) := .ofSetLike (Subgroupoid C) (Σ c d : C, c ⟶ d)
/-
**CategoryTheory.Subgroupoid.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
ubgroupoid`。
形式化陈述：mem_iff (S : Subgroupoid C) (F : Σ c d, c ⟶ d) : F in S ↔ F.2.2 in S.arrow
s F.1 F.2.1
参数：S : Subgroupoid C；F : Σ c d, c ⟶ d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iff (S : Subgroupoid C) (F : Σ c d, c ⟶ d) : F ∈ S ↔ F.2.2 ∈ S.arrows F.1 F.2.1 :=
  Iff.rfl
/-
**CategoryTheory.Subgroupoid.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Su
bgroupoid`。
形式化陈述：le_iff (S T : Subgroupoid C) : S <= T ↔ forall {c d}, S.arrows c d subsete
q T.arrows c d
参数：S T : Subgroupoid C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Sigma.forall`：∀ {α : Type u_1} {β : α → Type u_4} {p : (a : α) × β a → P
rop},   (∀ (x : (a : α) × β a), p x) ↔ ∀ (a : α) (b : β a), p ⟨a, b⟩
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
-/
theorem le_iff (S T : Subgroupoid C) : S ≤ T ↔ ∀ {c d}, S.arrows c d ⊆ T.arrows c d := by
  rw [SetLike.le_def, Sigma.forall]; exact forall_congr' fun c => Sigma.forall
/-
**CategoryTheory.Subgroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subgroup
oid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (Subgroupoid C) :=
  ⟨{  arrows := fun _ _ => Set.univ
      mul := by intros; trivial
      inv := by intros; trivial }⟩
/-
**CategoryTheory.Subgroupoid.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
ubgroupoid`。
形式化陈述：mem_top {c d : C} (f : c ⟶ d) : f in (⊤ : Subgroupoid C).arrows c d
参数：f : c ⟶ d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem mem_top {c d : C} (f : c ⟶ d) : f ∈ (⊤ : Subgroupoid C).arrows c d :=
  trivial
/-
**CategoryTheory.Subgroupoid.mem_top_objs** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Subgroupoid`。
形式化陈述：mem_top_objs (c : C) : c in (⊤ : Subgroupoid C).objs
参数：c : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
-/
theorem mem_top_objs (c : C) : c ∈ (⊤ : Subgroupoid C).objs := by
  dsimp [Top.top, objs]
  simp only [univ_nonempty]
/-
**CategoryTheory.Subgroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subgroup
oid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (Subgroupoid C) :=
  ⟨{  arrows := fun _ _ => ∅
      mul := False.elim
      inv := False.elim }⟩
/-
**CategoryTheory.Subgroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subgroup
oid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Subgroupoid C) :=
  ⟨⊤⟩
/-
**CategoryTheory.Subgroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subgroup
oid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (Subgroupoid C) :=
  ⟨fun S T =>
    { arrows := fun c d => S.arrows c d ∩ T.arrows c d
      inv := fun hp ↦ ⟨S.inv hp.1, T.inv hp.2⟩
      mul := fun hp _ hq ↦ ⟨S.mul hp.1 hq.1, T.mul hp.2 hq.2⟩ }⟩
/-
**CategoryTheory.Subgroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subgroup
oid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (Subgroupoid C) :=
  ⟨fun s =>
    { arrows := fun c d => ⋂ S ∈ s, Subgroupoid.arrows S c d
      inv := fun hp ↦ by rw [mem_iInter₂] at hp ⊢; exact fun S hS => S.inv (hp S hS)
      mul := fun hp _ hq ↦ by
        rw [mem_iInter₂] at hp hq ⊢
        exact fun S hS => S.mul (hp S hS) (hq S hS) }⟩
/-
**CategoryTheory.Subgroupoid.mem_sInf_arrows** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Subgroupoid`。
形式化陈述：mem_sInf_arrows {s : Set (Subgroupoid C)} {c d : C} {p : c ⟶ d} : p in (sI
nf s).arrows c d ↔ forall S in s, p in S.arrows c d
参数：Subgroupoid C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_sInf_arrows {s : Set (Subgroupoid C)} {c d : C} {p : c ⟶ d} :
    p ∈ (sInf s).arrows c d ↔ ∀ S ∈ s, p ∈ S.arrows c d :=
  mem_iInter₂
/-
**CategoryTheory.Subgroupoid.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Subgroupoid`。
形式化陈述：mem_sInf {s : Set (Subgroupoid C)} {p : Σ c d : C, c ⟶ d} : p in sInf s ↔ 
forall S in s, p in S
参数：Subgroupoid C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.mem_sInf_arrows`：mem_sInf_arrows {s : Set (Su
bgroupoid C)} {c d : C} {p : c ⟶ d} : p in (sInf s).arrows c d ↔ forall S in s, 
p in S.arrows c d
-/
theorem mem_sInf {s : Set (Subgroupoid C)} {p : Σ c d : C, c ⟶ d} :
    p ∈ sInf s ↔ ∀ S ∈ s, p ∈ S :=
  mem_sInf_arrows
/-
**CategoryTheory.Subgroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subgroup
oid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Subgroupoid.le_objs** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
ubgroupoid`。
形式化陈述：le_objs {S T : Subgroupoid C} (h : S <= T) : S.objs subseteq T.objs
参数：h : S <= T。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_objs {S T : Subgroupoid C} (h : S ≤ T) : S.objs ⊆ T.objs := fun s ⟨γ, hγ⟩ =>
  ⟨γ, @h ⟨s, s, γ⟩ hγ⟩

/-- The functor associated to the embedding of subgroupoids -/
/-
**CategoryTheory.Subgroupoid.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Subgroupoid`。
形式化陈述：inclusion {S T : Subgroupoid C} (h : S <= T) : S.objs ⥤ T.objs where obj s
参数：h : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor associated to the embedding of subgroupoids
-/
def inclusion {S T : Subgroupoid C} (h : S ≤ T) : S.objs ⥤ T.objs where
  obj s := ⟨s.val, le_objs h s.prop⟩
  map f := ⟨f.val, @h ⟨_, _, f.val⟩ f.prop⟩
  map_id _ := rfl
  map_comp _ _ := rfl
/-
**CategoryTheory.Subgroupoid.inclusion_inj_on_objects** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Subgroupoid`。
形式化陈述：inclusion_inj_on_objects {S T : Subgroupoid C} (h : S <= T) : Function.Inj
ective (inclusion h).obj
参数：h : S <= T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem inclusion_inj_on_objects {S T : Subgroupoid C} (h : S ≤ T) :
    Function.Injective (inclusion h).obj := fun ⟨s, hs⟩ ⟨t, ht⟩ => by
  simpa only [inclusion, Subtype.mk_eq_mk] using id

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Subgroupoid.inclusion_faithful** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Subgroupoid`。
形式化陈述：inclusion_faithful {S T : Subgroupoid C} (h : S <= T) (s t : S.objs) : Fun
ction.Injective fun f : s ⟶ t => (inclusion h).map f
参数：h : S <= T；s t : S.objs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
-/
theorem inclusion_faithful {S T : Subgroupoid C} (h : S ≤ T) (s t : S.objs) :
    Function.Injective fun f : s ⟶ t => (inclusion h).map f := fun ⟨f, hf⟩ ⟨g, hg⟩ => by
  -- Porting note: was `...; simpa only [Subtype.mk_eq_mk] using id`
  dsimp only [inclusion]; rw [Subtype.mk_eq_mk, Subtype.mk_eq_mk]; exact id
/-
**CategoryTheory.Subgroupoid.inclusion_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Subgroupoid`。
形式化陈述：inclusion_refl {S : Subgroupoid C} : inclusion (le_refl S) = 𝟭 S.objs
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem inclusion_refl {S : Subgroupoid C} : inclusion (le_refl S) = 𝟭 S.objs :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.refl _
/-
**CategoryTheory.Subgroupoid.inclusion_trans** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Subgroupoid`。
形式化陈述：inclusion_trans {R S T : Subgroupoid C} (k : R <= S) (h : S <= T) : inclus
ion (k.trans h) = inclusion k ⋙ inclusion h
参数：k : R <= S；h : S <= T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem inclusion_trans {R S T : Subgroupoid C} (k : R ≤ S) (h : S ≤ T) :
    inclusion (k.trans h) = inclusion k ⋙ inclusion h :=
  rfl
/-
**CategoryTheory.Subgroupoid.inclusion_comp_embedding** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Subgroupoid`。
形式化陈述：inclusion_comp_embedding {S T : Subgroupoid C} (h : S <= T) : inclusion h 
⋙ T.hom = S.hom
参数：h : S <= T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_comp_embedding {S T : Subgroupoid C} (h : S ≤ T) : inclusion h ⋙ T.hom = S.hom :=
  rfl

/-- The family of arrows of the discrete groupoid -/
/-
**CategoryTheory.Subgroupoid.Discrete.Arrows** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.Subgroupoid.Discrete`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Groupoid C] → (c d : C) → (c ⟶ d) → 
Prop
参数：c d : C；c ⟶ d。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of arrows of the discrete groupoid
-/
inductive Discrete.Arrows : ∀ c d : C, (c ⟶ d) → Prop
  | id (c : C) : Discrete.Arrows c c (𝟙 c)

/-- The only arrows of the discrete groupoid are the identity arrows. -/
/-
**CategoryTheory.Subgroupoid.discrete** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Subgroupoid`。
形式化陈述：discrete : Subgroupoid C where arrows c d
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The only arrows of the discrete groupoid are the identity arrows.
-/
def discrete : Subgroupoid C where
  arrows c d := {p | Discrete.Arrows c d p}
  inv := by rintro _ _ _ ⟨⟩; simp only [inv_eq_inv, IsIso.inv_id]; constructor
  mul := by rintro _ _ _ _ ⟨⟩ _ ⟨⟩; rw [Category.comp_id]; constructor
/-
**CategoryTheory.Subgroupoid.mem_discrete_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Subgroupoid`。
形式化陈述：mem_discrete_iff {c d : C} (f : c ⟶ d) : f in discrete.arrows c d ↔ exists
 h : c = d, f = eqToHom h
参数：f : c ⟶ d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem mem_discrete_iff {c d : C} (f : c ⟶ d) :
    f ∈ discrete.arrows c d ↔ ∃ h : c = d, f = eqToHom h :=
  ⟨by rintro ⟨⟩; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; constructor⟩

/-- A subgroupoid is wide if its carrier set is all of `C`. -/
/-
**CategoryTheory.Subgroupoid.IsWide** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.
Subgroupoid`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Groupoid C] → CategoryTheory.Subgrou
poid C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroupoid is wide if its carrier set is all of `C`.
-/
structure IsWide : Prop where
  wide : ∀ c, 𝟙 c ∈ S.arrows c c
/-
**CategoryTheory.Subgroupoid.isWide_iff_objs_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Subgroupoid`。
形式化陈述：isWide_iff_objs_eq_univ : S.IsWide ↔ S.objs = Set.univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CategoryTheory.Subgroupoid.mem_objs_of_src`：mem_objs_of_src {c d : C} {f
 : c ⟶ d} (h : f in S.arrows c d) : c in S.objs
· 使用定理 `CategoryTheory.Subgroupoid.IsWide.wide`：∀ {C : Type u} [inst : CategoryT
heory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsWide → ∀ (c : C), Ca
tegoryTheory.CategoryStruct.…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `CategoryTheory.Subgroupoid.id_mem_of_src`：id_mem_of_src {c d : C} {f : c
 ⟶ d} (h : f in S.arrows c d) : 𝟙 c in S.arrows c c
-/
theorem isWide_iff_objs_eq_univ : S.IsWide ↔ S.objs = Set.univ := by
  constructor
  · rintro h
    ext x; constructor <;> simp only [mem_univ, imp_true_iff, forall_true_left]
    apply mem_objs_of_src S (h.wide x)
  · rintro h
    refine ⟨fun c => ?_⟩
    obtain ⟨γ, γS⟩ := (le_of_eq h.symm : ⊤ ⊆ S.objs) (Set.mem_univ c)
    exact id_mem_of_src S γS
/-
**CategoryTheory.Subgroupoid.IsWide.id_mem** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Subgroupoid.IsWide`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Groupoid C] {S : CategoryTheory.Subg
roupoid C},   S.IsWide → ∀ (c : C), CategoryTheory.CategoryStruct.id c ∈ S.arrow
s c c
参数：c : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.IsWide.wide`：∀ {C : Type u} [inst : CategoryT
heory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsWide → ∀ (c : C), Ca
tegoryTheory.CategoryStruct.…
-/
theorem IsWide.id_mem {S : Subgroupoid C} (Sw : S.IsWide) (c : C) : 𝟙 c ∈ S.arrows c c :=
  Sw.wide c
/-
**CategoryTheory.Subgroupoid.IsWide.eqToHom_mem** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Subgroupoid.IsWide`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Groupoid C] {S : CategoryTheory.Subg
roupoid C},   S.IsWide → ∀ {c d : C} (h : c = d), CategoryTheory.eqToHom h ∈ S.a
rrows c d
参数：h : c = d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.IsWide.id_mem`：∀ {C : Type u} [inst : Categor
yTheory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsWide → ∀ (c : C), 
CategoryTheory.CategoryStruct.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem IsWide.eqToHom_mem {S : Subgroupoid C} (Sw : S.IsWide) {c d : C} (h : c = d) :
    eqToHom h ∈ S.arrows c d := by cases h; simp only [eqToHom_refl]; apply Sw.id_mem c

/-- A subgroupoid is normal if it is wide and satisfies the expected stability under conjugacy. -/
/-
**CategoryTheory.Subgroupoid.IsNormal** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y.Subgroupoid`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Groupoid C] → CategoryTheory.Subgrou
poid C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroupoid is normal if it is wide and satisfies the expected stability under
 conjugacy.
-/
structure IsNormal : Prop extends IsWide S where
  conj : ∀ {c d} (p : c ⟶ d) {γ : c ⟶ c}, γ ∈ S.arrows c c → Groupoid.inv p ≫ γ ≫ p ∈ S.arrows d d
/-
**CategoryTheory.Subgroupoid.IsNormal.conj'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Subgroupoid.IsNormal`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Groupoid C] {S : CategoryTheory.Subg
roupoid C},   S.IsNormal →     ∀ {c d : C} (p : d ⟶ c) {γ : c ⟶ c},       γ ∈ S.
arrows c c →         CategoryTheory.CategoryStruct.comp p (CategoryTheory.Catego
ryStruct.comp γ (CategoryTheory.Groupoid.inv p)) ∈           S.arrows d d
参数：p : d ⟶ c；CategoryTheory.CategoryStruct.comp γ (CategoryTheory.Groupoid.inv p
)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.of_groupoid`：∀ {C : Type u} [inst : CategoryTheory.
Groupoid C] {X Y : C} (f : X ⟶ Y), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.Groupoid.inv_eq_inv`：∀ {C : Type u} [inst : CategoryTheor
y.Groupoid C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Groupoid.inv f = CategoryT
heory.inv f
· 使用定理 `CategoryTheory.IsIso.inv_inv`：inv_inv [IsIso f] : inv (inv f) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Subgroupoid.IsNormal.conj`：∀ {C : Type u} [inst : Categor
yTheory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsNormal →     ∀ {c 
d : C} (p : c ⟶ d) {γ : c ⟶ c}…
-/
theorem IsNormal.conj' {S : Subgroupoid C} (Sn : IsNormal S) :
    ∀ {c d} (p : d ⟶ c) {γ : c ⟶ c}, γ ∈ S.arrows c c → p ≫ γ ≫ Groupoid.inv p ∈ S.arrows d d :=
  fun p γ hs => by convert! Sn.conj (Groupoid.inv p) hs; simp
/-
**CategoryTheory.Subgroupoid.IsNormal.conjugation_bij** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Subgroupoid.IsNormal`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Groupoid C] (S : CategoryTheory.Subg
roupoid C),   S.IsNormal →     ∀ {c d : C} (p : c ⟶ d),       Set.BijOn         
(fun γ =>           CategoryTheory.CategoryStruct.comp (CategoryTheory.Groupoid.
inv p) (CategoryTheory.CategoryStruct.comp γ p))         (S.arrows c c) (S.arrow
s d d)
参数：S : CategoryTheory.Subgroupoid C；p : c ⟶ d；fun γ =>           CategoryTheory.
CategoryStruct.comp (CategoryTheory.Groupoid.inv p) (CategoryTheory.CategoryStru
ct.comp γ p)；S.arrows c c；S.arrows d d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.IsNormal.conj`：∀ {C : Type u} [inst : Categor
yTheory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsNormal →     ∀ {c 
d : C} (p : c ⟶ d) {γ : c ⟶ c}…
· 使用定理 `CategoryTheory.IsGroupoid.all_isIso`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.IsGroupoid C] {X Y : C} (f : X ⟶ Y)
,   CategoryTheory.IsIso …
· 使用定理 `CategoryTheory.instIsGroupoid`：∀ {C : Type u} [inst : CategoryTheory.Gro
upoid C], CategoryTheory.IsGroupoid C
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.IsIso.of_groupoid`：∀ {C : Type u} [inst : CategoryTheory.
Groupoid C] {X Y : C} (f : X ⟶ Y), CategoryTheory.IsIso f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Groupoid.inv_eq_inv`：∀ {C : Type u} [inst : CategoryTheor
y.Groupoid C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Groupoid.inv f = CategoryT
heory.inv f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Subgroupoid.IsNormal.conj'`：∀ {C : Type u} [inst : Catego
ryTheory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsNormal →     ∀ {c
 d : C} (p : d ⟶ c) {γ : c ⟶ c}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsNormal.conjugation_bij (Sn : IsNormal S) {c d} (p : c ⟶ d) :
    Set.BijOn (fun γ : c ⟶ c => Groupoid.inv p ≫ γ ≫ p) (S.arrows c c) (S.arrows d d) := by
  refine ⟨fun γ γS => Sn.conj p γS, fun γ₁ _ γ₂ _ h => ?_, fun δ δS =>
    ⟨p ≫ δ ≫ Groupoid.inv p, Sn.conj' p δS, ?_⟩⟩
  · simpa only [inv_eq_inv, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc] using p ≫= h =≫ inv p
  · simp only [inv_eq_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      IsIso.inv_hom_id_assoc]
/-
**CategoryTheory.Subgroupoid.top_isNormal** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Subgroupoid`。
形式化陈述：top_isNormal : IsNormal (⊤ : Subgroupoid C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem top_isNormal : IsNormal (⊤ : Subgroupoid C) :=
  { wide := fun _ => trivial
    conj := fun _ _ _ => trivial }
/-
**CategoryTheory.Subgroupoid.sInf_isNormal** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Subgroupoid`。
形式化陈述：sInf_isNormal (s : Set <| Subgroupoid C) (sn : forall S in s, IsNormal S) 
: IsNormal (sInf s)
参数：s : Set <| Subgroupoid C；sn : forall S in s, IsNormal S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Subgroupoid.IsWide.wide`：∀ {C : Type u} [inst : CategoryT
heory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsWide → ∀ (c : C), Ca
tegoryTheory.CategoryStruct.…
· 使用定理 `CategoryTheory.Subgroupoid.IsNormal.toIsWide`：∀ {C : Type u} [inst : Cat
egoryTheory.Groupoid C] {S : CategoryTheory.Subgroupoid C}, S.IsNormal → S.IsWid
e
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CategoryTheory.Subgroupoid.IsNormal.conj`：∀ {C : Type u} [inst : Categor
yTheory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsNormal →     ∀ {c 
d : C} (p : c ⟶ d) {γ : c ⟶ c}…
-/
theorem sInf_isNormal (s : Set <| Subgroupoid C) (sn : ∀ S ∈ s, IsNormal S) : IsNormal (sInf s) :=
  { wide := by simp_rw [sInf, mem_iInter₂]; exact fun c S Ss => (sn S Ss).wide c
    conj := by simp_rw [sInf, mem_iInter₂]; exact fun p γ hγ S Ss => (sn S Ss).conj p (hγ S Ss) }
/-
**CategoryTheory.Subgroupoid.discrete_isNormal** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Subgroupoid`。
形式化陈述：discrete_isNormal : (@discrete C _).IsNormal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.IsIso.of_groupoid`：∀ {C : Type u} [inst : CategoryTheory.
Groupoid C] {X Y : C} (f : X ⟶ Y), CategoryTheory.IsIso f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Groupoid.inv_eq_inv`：∀ {C : Type u} [inst : CategoryTheor
y.Groupoid C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Groupoid.inv f = CategoryT
heory.inv f
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem discrete_isNormal : (@discrete C _).IsNormal :=
  { wide := fun c => by constructor
    conj := fun f γ hγ => by
      cases hγ
      simp only [inv_eq_inv, Category.id_comp, IsIso.inv_hom_id]; constructor }
/-
**CategoryTheory.Subgroupoid.IsNormal.vertexSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Subgroupoid.IsNormal`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Groupoid C] (S : CategoryTheory.Subg
roupoid C),   S.IsNormal → ∀ (c : C) (cS : c ∈ S.objs), (S.vertexSubgroup cS).No
rmal
参数：S : CategoryTheory.Subgroupoid C；c : C；cS : c ∈ S.objs；S.vertexSubgroup cS。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `CategoryTheory.Subgroupoid.IsNormal.conj'`：∀ {C : Type u} [inst : Catego
ryTheory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsNormal →     ∀ {c
 d : C} (p : d ⟶ c) {γ : c ⟶ c}…
-/
theorem IsNormal.vertexSubgroup (Sn : IsNormal S) (c : C) (cS : c ∈ S.objs) :
    (S.vertexSubgroup cS).Normal where
  conj_mem x hx y := by rw [mul_assoc]; exact Sn.conj' y hx

section GeneratedSubgroupoid

-- TODO: proof that generated is just "words in X" and generatedNormal is similarly
variable (X : ∀ c d : C, Set (c ⟶ d))

/-- The subgroupoid generated by the set of arrows `X` -/
/-
**CategoryTheory.Subgroupoid.generated** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Subgroupoid`。
形式化陈述：generated : Subgroupoid C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroupoid generated by the set of arrows `X`
-/
def generated : Subgroupoid C :=
  sInf {S : Subgroupoid C | ∀ c d, X c d ⊆ S.arrows c d}
/-
**CategoryTheory.Subgroupoid.subset_generated** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Subgroupoid`。
形式化陈述：subset_generated (c d : C) : X c d subseteq (generated X).arrows c d
参数：c d : C。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_generated (c d : C) : X c d ⊆ (generated X).arrows c d := by
  dsimp only [generated, sInf]
  simp only [subset_iInter₂_iff]
  exact fun S hS f fS => hS _ _ fS

/-- The normal subgroupoid generated by the set of arrows `X` -/
/-
**CategoryTheory.Subgroupoid.generatedNormal** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Subgroupoid`。
形式化陈述：generatedNormal : Subgroupoid C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normal subgroupoid generated by the set of arrows `X`
-/
def generatedNormal : Subgroupoid C :=
  sInf {S : Subgroupoid C | (∀ c d, X c d ⊆ S.arrows c d) ∧ S.IsNormal}
/-
**CategoryTheory.Subgroupoid.generated_le_generatedNormal** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Subgroupoid`。
形式化陈述：generated_le_generatedNormal : generated X <= generatedNormal X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
-/
theorem generated_le_generatedNormal : generated X ≤ generatedNormal X := by
  apply @sInf_le_sInf (Subgroupoid C) _
  exact fun S ⟨h, _⟩ => h
/-
**CategoryTheory.Subgroupoid.generatedNormal_isNormal** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Subgroupoid`。
形式化陈述：generatedNormal_isNormal : (generatedNormal X).IsNormal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.sInf_isNormal`：sInf_isNormal (s : Set <| Subg
roupoid C) (sn : forall S in s, IsNormal S) : IsNormal (sInf s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem generatedNormal_isNormal : (generatedNormal X).IsNormal :=
  sInf_isNormal _ fun _ h => h.right
/-
**CategoryTheory.Subgroupoid.IsNormal.generatedNormal_le** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Subgroupoid.IsNormal`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Groupoid C] (X : (c d : C) → Set (c 
⟶ d)) {S : CategoryTheory.Subgroupoid C},   S.IsNormal → (CategoryTheory.Subgrou
poid.generatedNormal X ≤ S ↔ ∀ (c d : C), X c d ⊆ S.arrows c d)
参数：X : (c d : C) → Set (c ⟶ d)；CategoryTheory.Subgroupoid.generatedNormal X ≤ S 
↔ ∀ (c d : C), X c d ⊆ S.arrows c d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.generated_le_generatedNormal`：generated_le_ge
neratedNormal : generated X <= generatedNormal X
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `CategoryTheory.Subgroupoid.subset_generated`：subset_generated (c d : C) 
: X c d subseteq (generated X).arrows c d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subgroupoid.le_iff`：le_iff (S T : Subgroupoid C) : S <= T
 ↔ forall {c d}, S.arrows c d subseteq T.arrows c d
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem IsNormal.generatedNormal_le {S : Subgroupoid C} (Sn : S.IsNormal) :
    generatedNormal X ≤ S ↔ ∀ c d, X c d ⊆ S.arrows c d := by
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

/-- A functor between groupoid defines a map of subgroupoids in the reverse direction
by taking preimages.
-/
/-
**CategoryTheory.Subgroupoid.comap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sub
groupoid`。
形式化陈述：comap (S : Subgroupoid D) : Subgroupoid C where arrows c d
参数：S : Subgroupoid D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor between groupoid defines a map of subgroupoids in the reverse directio
n
by taking preimages.
-/
def comap (S : Subgroupoid D) : Subgroupoid C where
  arrows c d := {f : c ⟶ d | φ.map f ∈ S.arrows (φ.obj c) (φ.obj d)}
  inv hp := by rw [mem_ofPred, inv_eq_inv, φ.map_inv, ← inv_eq_inv]; exact S.inv hp
  mul := by
    intros
    simp only [mem_ofPred, Functor.map_comp]
    apply S.mul <;> assumption

@[gcongr]
/-
**CategoryTheory.Subgroupoid.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subgroupoid`。
形式化陈述：comap_mono (S T : Subgroupoid D) : S <= T -> comap φ S <= comap φ T
参数：S T : Subgroupoid D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_mono (S T : Subgroupoid D) : S ≤ T → comap φ S ≤ comap φ T := fun ST _ =>
  @ST ⟨_, _, _⟩
/-
**CategoryTheory.Subgroupoid.isNormal_comap** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Subgroupoid`。
形式化陈述：isNormal_comap {S : Subgroupoid D} (Sn : IsNormal S) : IsNormal (comap φ S
) where wide c
参数：Sn : IsNormal S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subgroupoid.comap.eq_1`：∀ {C : Type u} [inst : CategoryTh
eory.Groupoid C] {D : Type u_1} [inst_1 : CategoryTheory.Groupoid D]   (φ : Cate
goryTheory.Functor C D) (S …
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Subgroupoid.IsWide.wide`：∀ {C : Type u} [inst : CategoryT
heory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsWide → ∀ (c : C), Ca
tegoryTheory.CategoryStruct.…
· 使用定理 `CategoryTheory.Subgroupoid.IsNormal.toIsWide`：∀ {C : Type u} [inst : Cat
egoryTheory.Groupoid C] {S : CategoryTheory.Subgroupoid C}, S.IsNormal → S.IsWid
e
· 使用定理 `CategoryTheory.IsIso.of_groupoid`：∀ {C : Type u} [inst : CategoryTheory.
Groupoid C] {X Y : C} (f : X ⟶ Y), CategoryTheory.IsIso f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Groupoid.inv_eq_inv`：∀ {C : Type u} [inst : CategoryTheor
y.Groupoid C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Groupoid.inv f = CategoryT
heory.inv f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.Subgroupoid.IsNormal.conj`：∀ {C : Type u} [inst : Categor
yTheory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsNormal →     ∀ {c 
d : C} (p : c ⟶ d) {γ : c ⟶ c}…
-/
theorem isNormal_comap {S : Subgroupoid D} (Sn : IsNormal S) : IsNormal (comap φ S) where
  wide c := by rw [comap, mem_ofPred, Functor.map_id]; apply Sn.wide
  conj f γ hγ := by
    simp_rw [inv_eq_inv f, comap, mem_ofPred, Functor.map_comp, Functor.map_inv, ← inv_eq_inv]
    exact Sn.conj _ hγ

@[simp]
/-
**CategoryTheory.Subgroupoid.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subgroupoid`。
形式化陈述：comap_comp {E : Type*} [Groupoid E] (ψ : D ⥤ E) : comap (φ ⋙ ψ) = comap φ 
∘ comap ψ
参数：ψ : D ⥤ E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comp {E : Type*} [Groupoid E] (ψ : D ⥤ E) : comap (φ ⋙ ψ) = comap φ ∘ comap ψ :=
  rfl

/-- The kernel of a functor between subgroupoid is the preimage. -/
/-
**CategoryTheory.Subgroupoid.ker** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subgr
oupoid`。
形式化陈述：ker : Subgroupoid C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a functor between subgroupoid is the preimage.
-/
def ker : Subgroupoid C :=
  comap φ discrete
/-
**CategoryTheory.Subgroupoid.mem_ker_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Subgroupoid`。
形式化陈述：mem_ker_iff {c d : C} (f : c ⟶ d) : f in (ker φ).arrows c d ↔ exists h : φ
.obj c = φ.obj d, φ.map f = eqToHom h
参数：f : c ⟶ d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.mem_discrete_iff`：mem_discrete_iff {c d : C} 
(f : c ⟶ d) : f in discrete.arrows c d ↔ exists h : c = d, f = eqToHom h
-/
theorem mem_ker_iff {c d : C} (f : c ⟶ d) :
    f ∈ (ker φ).arrows c d ↔ ∃ h : φ.obj c = φ.obj d, φ.map f = eqToHom h :=
  mem_discrete_iff (φ.map f)
/-
**CategoryTheory.Subgroupoid.ker_isNormal** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Subgroupoid`。
形式化陈述：ker_isNormal : (ker φ).IsNormal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.isNormal_comap`：isNormal_comap {S : Subgroupo
id D} (Sn : IsNormal S) : IsNormal (comap φ S) where wide c
· 使用定理 `CategoryTheory.Subgroupoid.discrete_isNormal`：discrete_isNormal : (@disc
rete C _).IsNormal
-/
theorem ker_isNormal : (ker φ).IsNormal :=
  isNormal_comap φ discrete_isNormal

@[simp]
/-
**CategoryTheory.Subgroupoid.ker_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Subgroupoid`。
形式化陈述：ker_comp {E : Type*} [Groupoid E] (ψ : D ⥤ E) : ker (φ ⋙ ψ) = comap φ (ker
 ψ)
参数：ψ : D ⥤ E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ker_comp {E : Type*} [Groupoid E] (ψ : D ⥤ E) : ker (φ ⋙ ψ) = comap φ (ker ψ) :=
  rfl

/-- The family of arrows of the image of a subgroupoid under a functor injective on objects -/
/-
**CategoryTheory.Subgroupoid.Map.Arrows** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory.Subgroupoid.Map`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Groupoid C] →     {D : Type u_1} →
       [inst_1 : CategoryTheory.Groupoid D] →         (φ : CategoryTheory.Functo
r C D) →           Function.Injective φ.obj → CategoryTheory.Subgroupoid C → (c 
d : D) → (c ⟶ d) → Prop
参数：φ : CategoryTheory.Functor C D；c d : D；c ⟶ d。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of arrows of the image of a subgroupoid under a functor injective on 
objects
-/
inductive Map.Arrows (hφ : Function.Injective φ.obj) (S : Subgroupoid C) : ∀ c d : D, (c ⟶ d) → Prop
  | im {c d : C} (f : c ⟶ d) (hf : f ∈ S.arrows c d) : Map.Arrows hφ S (φ.obj c) (φ.obj d) (φ.map f)
/-
**CategoryTheory.Subgroupoid.Map.arrows_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Subgroupoid.Map`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Groupoid C] {D : Type u_1} [inst_1 :
 CategoryTheory.Groupoid D]   (φ : CategoryTheory.Functor C D) (hφ : Function.In
jective φ.obj) (S : CategoryTheory.Subgroupoid C) {c d : D}   (f : c ⟶ d),   Cat
egoryTheory.Subgroupoid.Map.Arrows φ hφ S c d f ↔     ∃ a b g,       ∃ (ha : φ.o
bj a = c) (hb : φ.obj b = d) (_ : g ∈ S.arrows a b),         f =           Categ
oryTheory.CategoryStruct.comp (CategoryTheory.eqToHom ⋯)             (CategoryTh
eory.CategoryStruct.comp (φ.map g) (CategoryTheory.eqToHom hb))
参数：φ : CategoryTheory.Functor C D；hφ : Function.Injective φ.obj；S : CategoryTheo
ry.Subgroupoid C；f : c ⟶ d；ha : φ.obj a = c；hb : φ.obj b = d；_ : g ∈ S.arrows a 
b；CategoryTheory.eqToHom ⋯；CategoryTheory.CategoryStruct.comp (φ.map g) (Categor
yTheory.eqToHom hb)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.eq_conj_eqToHom`：eq_conj_eqToHom {X Y : C} (f : X ⟶ Y) : 
f = eqToHom rfl ≫ f ≫ eqToHom rfl
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem Map.arrows_iff (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d) :
    Map.Arrows φ hφ S c d f ↔
      ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d) (_hg : g ∈ S.arrows a b),
        f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb := by
  constructor
  · rintro ⟨g, hg⟩; exact ⟨_, _, g, rfl, rfl, hg, eq_conj_eqToHom _⟩
  · rintro ⟨a, b, g, rfl, rfl, hg, rfl⟩; rw [← eq_conj_eqToHom]; constructor; exact hg

/-- The "forward" image of a subgroupoid under a functor injective on objects -/
/-
**CategoryTheory.Subgroupoid.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subgr
oupoid`。
形式化陈述：map (hφ : Function.Injective φ.obj) (S : Subgroupoid C) : Subgroupoid D wh
ere arrows c d
参数：hφ : Function.Injective φ.obj；S : Subgroupoid C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "forward" image of a subgroupoid under a functor injective on objects
-/
def map (hφ : Function.Injective φ.obj) (S : Subgroupoid C) : Subgroupoid D where
  arrows c d := {x | Map.Arrows φ hφ S c d x}
  inv := by
    rintro _ _ _ ⟨⟩
    rw [inv_eq_inv, ← Functor.map_inv, ← inv_eq_inv]
    constructor; apply S.inv; assumption
  mul := by
    rintro _ _ _ _ ⟨f, hf⟩ q hq
    obtain ⟨c₃, c₄, g, he, rfl, hg, gq⟩ := (Map.arrows_iff φ hφ S q).mp hq
    cases hφ he; rw [gq, ← eq_conj_eqToHom, ← φ.map_comp]
    constructor; exact S.mul hf hg
/-
**CategoryTheory.Subgroupoid.mem_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Subgroupoid`。
形式化陈述：mem_map_iff (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} 
(f : c ⟶ d) : f in (map φ hφ S).arrows c d ↔ exists (a b : C) (g : a ⟶ b) (ha : 
φ.obj a = c) (hb : φ.obj b = d) (_hg : g in S.arrows a b), f = eqToHom ha.symm ≫
 φ.map g ≫ eqToHom hb
参数：hφ : Function.Injective φ.obj；S : Subgroupoid C；f : c ⟶ d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.Map.arrows_iff`：∀ {C : Type u} [inst : Catego
ryTheory.Groupoid C] {D : Type u_1} [inst_1 : CategoryTheory.Groupoid D]   (φ : 
CategoryTheory.Functor C D) (hφ…
-/
theorem mem_map_iff (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d) :
    f ∈ (map φ hφ S).arrows c d ↔
      ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d) (_hg : g ∈ S.arrows a b),
        f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb :=
  Map.arrows_iff φ hφ S f
/-
**CategoryTheory.Subgroupoid.galoisConnection_map_comap** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Subgroupoid`。
形式化陈述：galoisConnection_map_comap (hφ : Function.Injective φ.obj) : GaloisConnect
ion (map φ hφ) (comap φ)
参数：hφ : Function.Injective φ.obj。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem galoisConnection_map_comap (hφ : Function.Injective φ.obj) :
    GaloisConnection (map φ hφ) (comap φ) := by
  rintro S T; simp_rw [le_iff]; constructor
  · exact fun h c d f fS => h (Map.Arrows.im f fS)
  · rintro h _ _ g ⟨a, gφS⟩
    exact h gφS
/-
**CategoryTheory.Subgroupoid.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Subgroupoid`。
形式化陈述：map_mono (hφ : Function.Injective φ.obj) (S T : Subgroupoid C) : S <= T ->
 map φ hφ S <= map φ hφ T
参数：hφ : Function.Injective φ.obj；S T : Subgroupoid C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `CategoryTheory.Subgroupoid.galoisConnection_map_comap`：galoisConnection_
map_comap (hφ : Function.Injective φ.obj) : GaloisConnection (map φ hφ) (comap φ
)
-/
theorem map_mono (hφ : Function.Injective φ.obj) (S T : Subgroupoid C) :
    S ≤ T → map φ hφ S ≤ map φ hφ T := fun h => (galoisConnection_map_comap φ hφ).monotone_l h
/-
**CategoryTheory.Subgroupoid.le_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Subgroupoid`。
形式化陈述：le_comap_map (hφ : Function.Injective φ.obj) (S : Subgroupoid C) : S <= co
map φ (map φ hφ S)
参数：hφ : Function.Injective φ.obj；S : Subgroupoid C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `CategoryTheory.Subgroupoid.galoisConnection_map_comap`：galoisConnection_
map_comap (hφ : Function.Injective φ.obj) : GaloisConnection (map φ hφ) (comap φ
)
-/
theorem le_comap_map (hφ : Function.Injective φ.obj) (S : Subgroupoid C) :
    S ≤ comap φ (map φ hφ S) :=
  (galoisConnection_map_comap φ hφ).le_u_l S
/-
**CategoryTheory.Subgroupoid.map_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Subgroupoid`。
形式化陈述：map_comap_le (hφ : Function.Injective φ.obj) (T : Subgroupoid D) : map φ h
φ (comap φ T) <= T
参数：hφ : Function.Injective φ.obj；T : Subgroupoid D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `CategoryTheory.Subgroupoid.galoisConnection_map_comap`：galoisConnection_
map_comap (hφ : Function.Injective φ.obj) : GaloisConnection (map φ hφ) (comap φ
)
-/
theorem map_comap_le (hφ : Function.Injective φ.obj) (T : Subgroupoid D) :
    map φ hφ (comap φ T) ≤ T :=
  (galoisConnection_map_comap φ hφ).l_u_le T
/-
**CategoryTheory.Subgroupoid.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Subgroupoid`。
形式化陈述：map_le_iff_le_comap (hφ : Function.Injective φ.obj) (S : Subgroupoid C) (T
 : Subgroupoid D) : map φ hφ S <= T ↔ S <= comap φ T
参数：hφ : Function.Injective φ.obj；S : Subgroupoid C；T : Subgroupoid D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_iff_le`：le_iff_le {a : α} {b : β} : l a <= b ↔ a <= 
u b
· 使用定理 `CategoryTheory.Subgroupoid.galoisConnection_map_comap`：galoisConnection_
map_comap (hφ : Function.Injective φ.obj) : GaloisConnection (map φ hφ) (comap φ
)
-/
theorem map_le_iff_le_comap (hφ : Function.Injective φ.obj) (S : Subgroupoid C)
    (T : Subgroupoid D) : map φ hφ S ≤ T ↔ S ≤ comap φ T :=
  (galoisConnection_map_comap φ hφ).le_iff_le
/-
**CategoryTheory.Subgroupoid.mem_map_objs_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Subgroupoid`。
形式化陈述：mem_map_objs_iff (hφ : Function.Injective φ.obj) (d : D) : d in (map φ hφ 
S).objs ↔ exists c in S.objs, φ.obj c = d
参数：hφ : Function.Injective φ.obj；d : D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subgroupoid.Map.arrows_iff`：∀ {C : Type u} [inst : Catego
ryTheory.Groupoid C] {D : Type u_1} [inst_1 : CategoryTheory.Groupoid D]   (φ : 
CategoryTheory.Functor C D) (hφ…
· 使用定理 `CategoryTheory.Subgroupoid.mem_objs_of_src`：mem_objs_of_src {c d : C} {f
 : c ⟶ d} (h : f in S.arrows c d) : c in S.objs
-/
theorem mem_map_objs_iff (hφ : Function.Injective φ.obj) (d : D) :
    d ∈ (map φ hφ S).objs ↔ ∃ c ∈ S.objs, φ.obj c = d := by
  dsimp [objs, map]
  constructor
  · rintro ⟨f, hf⟩
    change Map.Arrows φ hφ S d d f at hf; rw [Map.arrows_iff] at hf
    obtain ⟨c, d, g, ec, ed, eg, gS, eg⟩ := hf
    exact ⟨c, ⟨mem_objs_of_src S eg, ec⟩⟩
  · rintro ⟨c, ⟨γ, γS⟩, rfl⟩
    exact ⟨φ.map γ, ⟨γ, γS⟩⟩

@[simp]
/-
**CategoryTheory.Subgroupoid.map_objs_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Subgroupoid`。
形式化陈述：map_objs_eq (hφ : Function.Injective φ.obj) : (map φ hφ S).objs = φ.obj ''
 S.objs
参数：hφ : Function.Injective φ.obj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subgroupoid.mem_map_objs_iff`：mem_map_objs_iff (hφ : Func
tion.Injective φ.obj) (d : D) : d in (map φ hφ S).objs ↔ exists c in S.objs, φ.o
bj c = d
-/
theorem map_objs_eq (hφ : Function.Injective φ.obj) : (map φ hφ S).objs = φ.obj '' S.objs := by
  ext x; convert! mem_map_objs_iff S φ hφ x

/-- The image of a functor injective on objects -/
/-
**CategoryTheory.Subgroupoid.im** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subgro
upoid`。
形式化陈述：im (hφ : Function.Injective φ.obj)
参数：hφ : Function.Injective φ.obj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a functor injective on objects
-/
def im (hφ : Function.Injective φ.obj) :=
  map φ hφ ⊤
/-
**CategoryTheory.Subgroupoid.mem_im_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subgroupoid`。
形式化陈述：mem_im_iff (hφ : Function.Injective φ.obj) {c d : D} (f : c ⟶ d) : f in (i
m φ hφ).arrows c d ↔ exists (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj
 b = d), f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb
参数：hφ : Function.Injective φ.obj；f : c ⟶ d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `CategoryTheory.Subgroupoid.Map.arrows_iff`：∀ {C : Type u} [inst : Catego
ryTheory.Groupoid C] {D : Type u_1} [inst_1 : CategoryTheory.Groupoid D]   (φ : 
CategoryTheory.Functor C D) (hφ…
-/
theorem mem_im_iff (hφ : Function.Injective φ.obj) {c d : D} (f : c ⟶ d) :
    f ∈ (im φ hφ).arrows c d ↔
      ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d),
        f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb := by
  convert! Map.arrows_iff φ hφ ⊤ f; simp only [Top.top, mem_univ, exists_true_left]
/-
**CategoryTheory.Subgroupoid.mem_im_objs_iff** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Subgroupoid`。
形式化陈述：mem_im_objs_iff (hφ : Function.Injective φ.obj) (d : D) : d in (im φ hφ).o
bjs ↔ exists c : C, φ.obj c = d
参数：hφ : Function.Injective φ.obj；d : D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_im_objs_iff (hφ : Function.Injective φ.obj) (d : D) :
    d ∈ (im φ hφ).objs ↔ ∃ c : C, φ.obj c = d := by
  simp only [im, mem_map_objs_iff, mem_top_objs, true_and]
/-
**CategoryTheory.Subgroupoid.obj_surjective_of_im_eq_top** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Subgroupoid`。
形式化陈述：obj_surjective_of_im_eq_top (hφ : Function.Injective φ.obj) (hφ' : im φ hφ
 = ⊤) : Function.Surjective φ.obj
参数：hφ : Function.Injective φ.obj；hφ' : im φ hφ = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subgroupoid.mem_im_objs_iff`：mem_im_objs_iff (hφ : Functi
on.Injective φ.obj) (d : D) : d in (im φ hφ).objs ↔ exists c : C, φ.obj c = d
· 使用定理 `CategoryTheory.Subgroupoid.mem_top_objs`：mem_top_objs (c : C) : c in (⊤ 
: Subgroupoid C).objs
-/
theorem obj_surjective_of_im_eq_top (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤) :
    Function.Surjective φ.obj := by
  rintro d
  rw [← mem_im_objs_iff _ hφ, hφ']
  apply mem_top_objs
/-
**CategoryTheory.Subgroupoid.isNormal_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Subgroupoid`。
形式化陈述：isNormal_map (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤) (Sn : S.I
sNormal) : (map φ hφ S).IsNormal
参数：hφ : Function.Injective φ.obj；hφ' : im φ hφ = ⊤；Sn : S.IsNormal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.obj_surjective_of_im_eq_top`：obj_surjective_o
f_im_eq_top (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤) : Function.Surje
ctive φ.obj
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Subgroupoid.IsWide.wide`：∀ {C : Type u} [inst : CategoryT
heory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsWide → ∀ (c : C), Ca
tegoryTheory.CategoryStruct.…
· 使用定理 `CategoryTheory.Subgroupoid.IsNormal.toIsWide`：∀ {C : Type u} [inst : Cat
egoryTheory.Groupoid C] {S : CategoryTheory.Subgroupoid C}, S.IsNormal → S.IsWid
e
· 使用定理 `CategoryTheory.Subgroupoid.mem_map_iff`：mem_map_iff (hφ : Function.Injec
tive φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d) : f in (map φ hφ S).arrows
 c d ↔ exists (a b : C) (g :…
· 使用定理 `CategoryTheory.Subgroupoid.mem_top_objs`：mem_top_objs (c : C) : c in (⊤ 
: Subgroupoid C).objs
· 使用定理 `CategoryTheory.Subgroupoid.mem_im_objs_iff`：mem_im_objs_iff (hφ : Functi
on.Injective φ.obj) (d : D) : d in (im φ hφ).objs ↔ exists c : C, φ.obj c = d
· 使用定理 `CategoryTheory.Subgroupoid.mem_im_iff`：mem_im_iff (hφ : Function.Injecti
ve φ.obj) {c d : D} (f : c ⟶ d) : f in (im φ hφ).arrows c d ↔ exists (a b : C) (
g : a ⟶ b) (ha : φ.obj a = …
· 使用定理 `CategoryTheory.IsIso.of_groupoid`：∀ {C : Type u} [inst : CategoryTheory.
Groupoid C] {X Y : C} (f : X ⟶ Y), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.Subgroupoid.Map.Arrows.congr_simp`：∀ {C : Type u} [inst :
 CategoryTheory.Groupoid C] {D : Type u_1} [inst_1 : CategoryTheory.Groupoid D] 
  (φ φ_1 : CategoryTheory.Functor C D)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Groupoid.inv_eq_inv`：∀ {C : Type u} [inst : CategoryTheor
y.Groupoid C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Groupoid.inv f = CategoryT
heory.inv f
· 使用定理 `CategoryTheory.Subgroupoid.IsNormal.conj`：∀ {C : Type u} [inst : Categor
yTheory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsNormal →     ∀ {c 
d : C} (p : c ⟶ d) {γ : c ⟶ c}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
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
      have : d' ∈ (im φ hφ).objs := by rw [hφ']; apply mem_top_objs
      rw [mem_im_objs_iff] at this
      obtain ⟨c', rfl⟩ := this
      have : g ∈ (im φ hφ).arrows (φ.obj c) (φ.obj c') := by rw [hφ']; trivial
      rw [mem_im_iff] at this
      obtain ⟨b, b', f, hb, hb', _, hf⟩ := this; cases hφ hb; cases hφ hb'
      change Map.Arrows φ hφ S (φ.obj c') (φ.obj c') _
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp, inv_eq_inv]
      suffices Map.Arrows φ hφ S (φ.obj c') (φ.obj c') (φ.map <| Groupoid.inv f ≫ γ ≫ f) by
        simp only [inv_eq_inv, Functor.map_comp, Functor.map_inv] at this; exact this
      constructor; apply Sn.conj f γS }

end Hom

section Thin

/-- A subgroupoid is thin (`CategoryTheory.Subgroupoid.IsThin`) if it has at most one arrow between
any two vertices. -/
/-
**CategoryTheory.Subgroupoid.IsThin** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Subgroupoid`。
形式化陈述：IsThin
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroupoid is thin (`CategoryTheory.Subgroupoid.IsThin`) if it has at most on
e arrow between
any two vertices.
-/
abbrev IsThin :=
  Quiver.IsThin S.objs

nonrec theorem isThin_iff : S.IsThin ↔ ∀ c : S.objs, Subsingleton (S.arrows c c) := isThin_iff _

end Thin

section Disconnected

/-- A subgroupoid `IsTotallyDisconnected` if it has only isotropy arrows. -/
nonrec abbrev IsTotallyDisconnected :=
  IsTotallyDisconnected S.objs

/-
**CategoryTheory.Subgroupoid.isTotallyDisconnected_iff** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Subgroupoid`。
形式化陈述：isTotallyDisconnected_iff : S.IsTotallyDisconnected ↔ forall c d, (S.arrow
s c d).Nonempty -> c = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Subgroupoid.mem_objs_of_src`：mem_objs_of_src {c d : C} {f
 : c ⟶ d} (h : f in S.arrows c d) : c in S.objs
· 使用定理 `CategoryTheory.Subgroupoid.mem_objs_of_tgt`：mem_objs_of_tgt {c d : C} {f
 : c ⟶ d} (h : f in S.arrows c d) : d in S.objs
-/
theorem isTotallyDisconnected_iff :
    S.IsTotallyDisconnected ↔ ∀ c d, (S.arrows c d).Nonempty → c = d := by
  constructor
  · rintro h c d ⟨f, fS⟩
    exact congr_arg Subtype.val <| h ⟨c, mem_objs_of_src S fS⟩ ⟨d, mem_objs_of_tgt S fS⟩ ⟨f, fS⟩
  · rintro h ⟨c, hc⟩ ⟨d, hd⟩ ⟨f, fS⟩
    simp only [Subtype.mk_eq_mk]
    exact h c d ⟨f, fS⟩

/-- The isotropy subgroupoid of `S` -/
/-
**CategoryTheory.Subgroupoid.disconnect** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Subgroupoid`。
形式化陈述：disconnect : Subgroupoid C where arrows c d
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isotropy subgroupoid of `S`
-/
def disconnect : Subgroupoid C where
  arrows c d := {f | c = d ∧ f ∈ S.arrows c d}
  inv := by rintro _ _ _ ⟨rfl, h⟩; exact ⟨rfl, S.inv h⟩
  mul := by rintro _ _ _ _ ⟨rfl, h⟩ _ ⟨rfl, h'⟩; exact ⟨rfl, S.mul h h'⟩
/-
**CategoryTheory.Subgroupoid.disconnect_le** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Subgroupoid`。
形式化陈述：disconnect_le : S.disconnect <= S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subgroupoid.le_iff`：le_iff (S T : Subgroupoid C) : S <= T
 ↔ forall {c d}, S.arrows c d subseteq T.arrows c d
-/
theorem disconnect_le : S.disconnect ≤ S := by rw [le_iff]; rintro _ _ _ ⟨⟩; assumption
/-
**CategoryTheory.Subgroupoid.disconnect_normal** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Subgroupoid`。
形式化陈述：disconnect_normal (Sn : S.IsNormal) : S.disconnect.IsNormal
参数：Sn : S.IsNormal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.IsWide.wide`：∀ {C : Type u} [inst : CategoryT
heory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsWide → ∀ (c : C), Ca
tegoryTheory.CategoryStruct.…
· 使用定理 `CategoryTheory.Subgroupoid.IsNormal.toIsWide`：∀ {C : Type u} [inst : Cat
egoryTheory.Groupoid C] {S : CategoryTheory.Subgroupoid C}, S.IsNormal → S.IsWid
e
· 使用定理 `CategoryTheory.Subgroupoid.IsNormal.conj`：∀ {C : Type u} [inst : Categor
yTheory.Groupoid C] {S : CategoryTheory.Subgroupoid C},   S.IsNormal →     ∀ {c 
d : C} (p : c ⟶ d) {γ : c ⟶ c}…
-/
theorem disconnect_normal (Sn : S.IsNormal) : S.disconnect.IsNormal :=
  { wide := fun c => ⟨rfl, Sn.wide c⟩
    conj := fun _ _ ⟨_, h'⟩ => ⟨rfl, Sn.conj _ h'⟩ }

@[simp]
/-
**CategoryTheory.Subgroupoid.mem_disconnect_objs_iff** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Subgroupoid`。
形式化陈述：mem_disconnect_objs_iff {c : C} : c in S.disconnect.objs ↔ c in S.objs
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_disconnect_objs_iff {c : C} : c ∈ S.disconnect.objs ↔ c ∈ S.objs :=
  ⟨fun ⟨γ, _, γS⟩ => ⟨γ, γS⟩, fun ⟨γ, γS⟩ => ⟨γ, rfl, γS⟩⟩
/-
**CategoryTheory.Subgroupoid.disconnect_objs** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Subgroupoid`。
形式化陈述：disconnect_objs : S.disconnect.objs = S.objs
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CategoryTheory.Subgroupoid.mem_disconnect_objs_iff`：mem_disconnect_objs_
iff {c : C} : c in S.disconnect.objs ↔ c in S.objs
-/
theorem disconnect_objs : S.disconnect.objs = S.objs := Set.ext fun _ ↦ mem_disconnect_objs_iff _
/-
**CategoryTheory.Subgroupoid.disconnect_isTotallyDisconnected** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Subgroupoid`。
形式化陈述：disconnect_isTotallyDisconnected : S.disconnect.IsTotallyDisconnected
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subgroupoid.isTotallyDisconnected_iff`：isTotallyDisconnec
ted_iff : S.IsTotallyDisconnected ↔ forall c d, (S.arrows c d).Nonempty -> c = d
-/
theorem disconnect_isTotallyDisconnected : S.disconnect.IsTotallyDisconnected := by
  rw [isTotallyDisconnected_iff]; exact fun c d ⟨_, h, _⟩ => h

end Disconnected

section Full

variable (D : Set C)

/-- The full subgroupoid on a set `D : Set C` -/
/-
**CategoryTheory.Subgroupoid.full** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subg
roupoid`。
形式化陈述：full : Subgroupoid C where arrows c d
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subgroupoid on a set `D : Set C`
-/
def full : Subgroupoid C where
  arrows c d := {_f | c ∈ D ∧ d ∈ D}
  inv := by rintro _ _ _ ⟨⟩; constructor <;> assumption
  mul := by rintro _ _ _ _ ⟨⟩ _ ⟨⟩; constructor <;> assumption
/-
**CategoryTheory.Subgroupoid.full_objs** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Subgroupoid`。
形式化陈述：full_objs : (full D).objs = D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
theorem full_objs : (full D).objs = D :=
  Set.ext fun _ => ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨𝟙 _, h, h⟩⟩

@[simp]
/-
**CategoryTheory.Subgroupoid.mem_full_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Subgroupoid`。
形式化陈述：mem_full_iff {c d : C} {f : c ⟶ d} : f in (full D).arrows c d ↔ c in D ∧ d
 in D
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_full_iff {c d : C} {f : c ⟶ d} : f ∈ (full D).arrows c d ↔ c ∈ D ∧ d ∈ D :=
  Iff.rfl

@[simp]
/-
**CategoryTheory.Subgroupoid.mem_full_objs_iff** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Subgroupoid`。
形式化陈述：mem_full_objs_iff {c : C} : c in (full D).objs ↔ c in D
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subgroupoid.full_objs`：full_objs : (full D).objs = D
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_full_objs_iff {c : C} : c ∈ (full D).objs ↔ c ∈ D := by rw [full_objs]

@[simp]
/-
**CategoryTheory.Subgroupoid.full_empty** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subgroupoid`。
形式化陈述：full_empty : full ∅ = (⊥ : Subgroupoid C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.ext`：∀ {C : Type u} {inst : CategoryTheory.Gr
oupoid C} {x y : CategoryTheory.Subgroupoid C}, x.arrows = y.arrows → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem full_empty : full ∅ = (⊥ : Subgroupoid C) := by
  ext
  simp only [Bot.bot, mem_full_iff, mem_empty_iff_false, and_self_iff]

@[simp]
/-
**CategoryTheory.Subgroupoid.full_univ** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Subgroupoid`。
形式化陈述：full_univ : full Set.univ = (⊤ : Subgroupoid C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subgroupoid.ext`：∀ {C : Type u} {inst : CategoryTheory.Gr
oupoid C} {x y : CategoryTheory.Subgroupoid C}, x.arrows = y.arrows → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem full_univ : full Set.univ = (⊤ : Subgroupoid C) := by
  ext
  simp only [mem_full_iff, mem_univ, and_self, mem_top]
/-
**CategoryTheory.Subgroupoid.full_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Subgroupoid`。
形式化陈述：full_mono {D E : Set C} (h : D <= E) : full D <= full E
参数：h : D <= E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subgroupoid.le_iff`：le_iff (S T : Subgroupoid C) : S <= T
 ↔ forall {c d}, S.arrows c d subseteq T.arrows c d
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem full_mono {D E : Set C} (h : D ≤ E) : full D ≤ full E := by
  rw [le_iff]
  rintro c d f
  simp only [mem_full_iff]
  exact fun ⟨hc, hd⟩ => ⟨h hc, h hd⟩
/-
**CategoryTheory.Subgroupoid.full_arrow_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Subgroupoid`。
形式化陈述：full_arrow_eq_iff {c d : (full D).objs} {f g : c ⟶ d} : f = g ↔ f.1 = g.1
参数：full D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem full_arrow_eq_iff {c d : (full D).objs} {f g : c ⟶ d} :
    f = g ↔ f.1 = g.1 :=
  Subtype.ext_iff

end Full

end Subgroupoid

end CategoryTheory

