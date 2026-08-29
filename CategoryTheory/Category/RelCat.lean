/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Uni Marx
-/
module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Rel

/-!
# Basics on the category of relations

We define the category of types `CategoryTheory.RelCat` with binary relations as morphisms.
Associating each function with the relation defined by its graph yields a faithful and
essentially surjective functor `graphFunctor` that also characterizes all isomorphisms
(see `rel_iso_iff`).

By flipping the arguments to a relation, we construct an equivalence `opEquivalence` between
`RelCat` and its opposite.
-/

@[expose] public section

open SetRel

namespace CategoryTheory

universe u

/--
Definition of `RelCat` / `RelCat` 的定义

English:
definition RelCat
  body: Type u
deriving Inhabited

中文:
定义 RelCat
  定义体: Type u
deriving Inhabited
-/
def RelCat :=
  Type u
deriving Inhabited

namespace RelCat
variable {X Y Z : RelCat.{u}}

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : RelCat.{u})
  axioms and operations (2):
    - ofRel : :
    - rel : SetRel X Y

中文:
结构 态射
  参数: (X Y : RelCat.{u})
  公理与运算 (2 个):
    - ofRel : :
    - rel : SetRel X Y
-/
structure Hom (X Y : RelCat.{u}) : Type u where
  /-- Build a morphism `X ⟶ Y` for `X Y : RelCat` from a relation between `X` and `Y`. -/
  ofRel ::
  /-- The underlying relation between `X` and `Y` of a morphism `X ⟶ Y` for `X Y : RelCat`. -/
  rel : SetRel X Y

initialize_simps_projections Hom (as_prefix rel)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `instLargeCategory` / 实例 `instLargeCategory`

English:
instance instLargeCategory
  signature: : LargeCategory RelCat where
  body: Hom
  id _ := .ofRel .id
comp f g := .ofRel f.rel ○ g.rel

中文:
实例 instLargeCategory
  签名: : 大范畴 RelCat where
  定义体: Hom
  id _ := .ofRel .id
comp f g := .ofRel f.rel ○ g.rel
-/
instance instLargeCategory : LargeCategory RelCat where
  Hom := Hom
  id _ := .ofRel .id
comp f g := .ofRel f.rel ○ g.rel

namespace Hom

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: (f g : X ⟶ Y) (h : f.rel = g.rel)
  statement: f = g
  proof: by cases f; cases g; congr

中文:
引理 ext
  条件: (f g : X ⟶ Y) (h : f.rel = g.rel)
  结论: f = g
  证明: by cases f; cases g; congr
-/
@[ext] lemma ext (f g : X ⟶ Y) (h : f.rel = g.rel) : f = g := by cases f; cases g; congr

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `rel_id` / 引理 `rel_id`

English:
lemma rel_id
  given: (X : RelCat.{u})
  statement: rel (𝟙 X) = .id
  proof: rfl

中文:
引理 rel_id
  条件: (X : RelCat.{u})
  结论: rel (𝟙 X) = .id
  证明: rfl
-/
@[simp] protected lemma rel_id (X : RelCat.{u}) : rel (𝟙 X) = .id := rfl
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `rel_comp` / 引理 `rel_comp`

English:
lemma rel_comp
  given: (f : X ⟶ Y) (g : Y ⟶ Z)
  statement: (f ≫ g).rel = f.rel.comp g.rel
  proof: rfl

中文:
引理 rel_comp
  条件: (f : X ⟶ Y) (g : Y ⟶ Z)
  结论: (f ≫ g).rel = f.rel.comp g.rel
  证明: rfl
-/
@[simp] protected lemma rel_comp (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).rel = f.rel.comp g.rel := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `rel_id_apply₂` / 定理 `rel_id_apply₂`

English:
theorem rel_id_apply₂
  given: (x y : X)
  statement: x ~[rel (𝟙 X)] y ↔ x = y
  proof: .rfl

中文:
定理 rel_id_apply₂
  条件: (x y : X)
  结论: x ~[rel (𝟙 X)] y ↔ x = y
  证明: .rfl
-/
theorem rel_id_apply₂ (x y : X) : x ~[rel (𝟙 X)] y ↔ x = y := .rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `rel_comp_apply₂` / 定理 `rel_comp_apply₂`

English:
theorem rel_comp_apply₂
  given: (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (z : Z)
  proof: .rfl

中文:
定理 rel_comp_apply₂
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (z : Z)
  证明: .rfl
-/
theorem rel_comp_apply₂ (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (z : Z) :
    x ~[(f ≫ g).rel] z ↔ exists y, x ~[f.rel] y ∧ y ~[g.rel] z := .rfl

end Hom

set_option backward.isDefEq.respectTransparency.types false in
/-- The essentially surjective faithful embedding
from the category of types and functions into the category of types and relations. -/
@[simps obj map_rel]
/--
Definition of `graphFunctor` / `graphFunctor` 的定义

English:
definition graphFunctor
  signature: : Type u ⥤ RelCat.{u} where
  body: X
  map f := .ofRel (f : _ -> _).graph

中文:
定义 graphFunctor
  签名: : 类型u ⥤ RelCat.{u} where
  定义体: X
  map f := .ofRel (f : _ -> _).graph
-/
def graphFunctor : Type u ⥤ RelCat.{u} where
  obj X := X
  map f := .ofRel (f : _ -> _).graph

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `graphFunctor_faithful` / 实例 `graphFunctor_faithful`

English:
instance graphFunctor_faithful
  signature: : graphFunctor.Faithful where
  body: by
    ext
    simp [Function.graph_injective congr(($h).rel)]

中文:
实例 graphFunctor_faithful
  签名: : graphFunctor.忠实 where
  定义体: by
    ext
    simp [Function.graph_injective congr(($h).rel)]

Depends on / 依赖: Function, Function.graph_injective, graph_injective
-/
instance graphFunctor_faithful : graphFunctor.Faithful where
  map_injective h := by
    ext
    simp [Function.graph_injective congr(($h).rel)]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `graphFunctor_essSurj` / 实例 `graphFunctor_essSurj`

English:
instance graphFunctor_essSurj
  signature: : graphFunctor.EssSurj
  body: graphFunctor.essSurj_of_surj Function.surjective_id

中文:
实例 graphFunctor_essSurj
  签名: : graphFunctor.本质满射
  定义体: graphFunctor.essSurj_of_surj Function.surjective_id

Depends on / 依赖: Function, Function.surjective_id, essSurj_of_surj, graphFunctor, graphFunctor.essSurj_of_surj, surjective_id
-/
instance graphFunctor_essSurj : graphFunctor.EssSurj :=
    graphFunctor.essSurj_of_surj Function.surjective_id

set_option backward.isDefEq.respectTransparency false in
/--
theorem `rel_iso_iff` / 定理 `rel_iso_iff`

English:
theorem rel_iso_iff
  given: {X Y : RelCat} (r : X ⟶ Y)
  proof: by
  constructor
  · intro h
    have h1 := congr_fun₂ congr((· ~[($h.hom_inv_id).rel] ·))
    have h2 := congr_fun₂ congr((· ~[($h.inv_hom_id).rel] ·))
    simp only [RelCat.Hom.rel_comp_apply₂, RelCat.Hom.rel_id_apply₂, eq_iff_iff] at h1 h2
    obtain ⟨f, hf⟩ := Classical.axiomOfChoice (fun a => (

中文:
定理 rel_iso_iff
  条件: {X Y : RelCat} (r : X ⟶ Y)
  证明: by
  constructor
  · intro h
    have h1 := congr_fun₂ congr((· ~[($h.hom_inv_id).rel] ·))
    have h2 := congr_fun₂ congr((· ~[($h.inv_hom_id).rel] ·))
    simp only [RelCat.Hom.rel_comp_apply₂, RelCat.Hom.rel_id_apply₂, eq_iff_iff] at h1 h2
    obtain ⟨f, hf⟩ := Classical.axiomOfChoice (fun a => (

Depends on / 依赖: Classical, Classical.axiomOfChoice, RelCat, RelCat.Hom.rel_comp_apply, RelCat.Hom.rel_id_apply, axiomOfChoice, eq_iff_iff, f.hom, graphFunctor, graphFunctor.map, h.hom_inv_id, h.inv_hom_id, hom_inv_id, inv_hom_id
-/
theorem rel_iso_iff {X Y : RelCat} (r : X ⟶ Y) :
    IsIso (C := RelCat) r ↔ exists f : Iso (C := Type u) X Y, graphFunctor.map f.hom = r := by
  constructor
  · intro h
    have h1 := congr_fun₂ congr((· ~[($h.hom_inv_id).rel] ·))
    have h2 := congr_fun₂ congr((· ~[($h.inv_hom_id).rel] ·))
    simp only [RelCat.Hom.rel_comp_apply₂, RelCat.Hom.rel_id_apply₂, eq_iff_iff] at h1 h2
    obtain ⟨f, hf⟩ := Classical.axiomOfChoice (fun a => (h1 a a).mpr rfl)
    obtain ⟨g, hg⟩ := Classical.axiomOfChoice (fun a => (h2 a a).mpr rfl)
    suffices hif : IsIso (C := Type u) (↾f) by
      use asIso (↾f)
      ext ⟨x, y⟩
      exact ⟨by aesop, fun hxy => (h2 (f x) y).1 ⟨x, (hf x).2, hxy⟩⟩
    use ↾g
    constructor
    · ext x
      apply (h1 _ _).mp
      use f x, (hg _).2, (hf _).2
    · ext y
      apply (h2 _ _).mp
      use g y, (hf (g y)).2, (hg y).2
  · rintro ⟨f, rfl⟩
    apply graphFunctor.map_isIso

section Opposite
open Opposite

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `opFunctor` / `opFunctor` 的定义

English:
definition opFunctor
  signature: : RelCat ⥤ RelCatᵒᵖ where
  body: op X
map {_ _} r := .op .ofRel r.rel.inv

中文:
定义 opFunctor
  签名: : RelCat ⥤ RelCatᵒᵖ where
  定义体: op X
map {_ _} r := .op .ofRel r.rel.inv
-/
def opFunctor : RelCat ⥤ RelCatᵒᵖ where
  obj X := op X
map {_ _} r := .op .ofRel r.rel.inv

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `unopFunctor` / `unopFunctor` 的定义

English:
definition unopFunctor
  signature: : RelCatᵒᵖ ⥤ RelCat where
  body: unop X
  map {_ _} r := .ofRel r.unop.rel.inv

中文:
定义 unopFunctor
  签名: : RelCatᵒᵖ ⥤ RelCat where
  定义体: unop X
  map {_ _} r := .ofRel r.unop.rel.inv
-/
def unopFunctor : RelCatᵒᵖ ⥤ RelCat where
  obj X := unop X
  map {_ _} r := .ofRel r.unop.rel.inv

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `opFunctor_comp_unopFunctor_eq` / 定理 `opFunctor_comp_unopFunctor_eq`

English:
theorem opFunctor_comp_unopFunctor_eq
  proof: rfl

中文:
定理 opFunctor_comp_unopFunctor_eq
  证明: rfl
-/
@[simp] theorem opFunctor_comp_unopFunctor_eq :
    Functor.comp opFunctor unopFunctor = Functor.id _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `unopFunctor_comp_opFunctor_eq` / 定理 `unopFunctor_comp_opFunctor_eq`

English:
theorem unopFunctor_comp_opFunctor_eq
  proof: rfl

中文:
定理 unopFunctor_comp_opFunctor_eq
  证明: rfl
-/
@[simp] theorem unopFunctor_comp_opFunctor_eq :
    Functor.comp unopFunctor opFunctor = Functor.id _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `RelCat` is self-dual: The map that swaps the argument order of a
relation induces an equivalence between `RelCat` and its opposite. -/
@[simps]
/--
Definition of `opEquivalence` / `opEquivalence` 的定义

English:
definition opEquivalence
  signature: : RelCat ≌ RelCatᵒᵖ where
  body: opFunctor
  inverse := unopFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 opEquivalence
  签名: : RelCat ≌ RelCatᵒᵖ where
  定义体: opFunctor
  inverse := unopFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: opFunctor
-/
def opEquivalence : RelCat ≌ RelCatᵒᵖ where
  functor := opFunctor
  inverse := unopFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: opFunctor.IsEquivalence
  body: by
  change opEquivalence.functor.IsEquivalence
  infer_instance

中文:
实例 :
  签名: opFunctor.是等价
  定义体: by
  change opEquivalence.functor.IsEquivalence
  infer_instance

Depends on / 依赖: IsEquivalence, functor, infer_instance, opEquivalence, opEquivalence.functor.IsEquivalence
-/
instance : opFunctor.IsEquivalence := by
  change opEquivalence.functor.IsEquivalence
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: unopFunctor.IsEquivalence
  body: by
  change opEquivalence.inverse.IsEquivalence
  infer_instance

中文:
实例 :
  签名: unopFunctor.是等价
  定义体: by
  change opEquivalence.inverse.IsEquivalence
  infer_instance

Depends on / 依赖: IsEquivalence, infer_instance, inverse, opEquivalence, opEquivalence.inverse.IsEquivalence
-/
instance : unopFunctor.IsEquivalence := by
  change opEquivalence.inverse.IsEquivalence
  infer_instance

end Opposite

end RelCat

end CategoryTheory
