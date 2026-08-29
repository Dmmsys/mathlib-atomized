/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.SpreadingOut
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
/-!

# Rational maps between schemes

## Main definitions

* `AlgebraicGeometry.Scheme.PartialMap`: A partial map from `X` to `Y` (`X.PartialMap Y`) is
  a morphism into `Y` defined on a dense open subscheme of `X`.
* `AlgebraicGeometry.Scheme.PartialMap.equiv`:
  Two partial maps are equivalent if they are equal on a dense open subscheme.
* `AlgebraicGeometry.Scheme.RationalMap`:
  A rational map from `X` to `Y` (`X ⤏ Y`) is an equivalence class of partial maps.
* `AlgebraicGeometry.Scheme.RationalMap.equivFunctionFieldOver`:
  Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and `X` is integral,
  `S`-morphisms `Spec K(X) ⟶ Y` correspond bijectively to `S`-rational maps from `X` to `Y`.
* `AlgebraicGeometry.Scheme.RationalMap.toPartialMap`:
  If `X` is reduced and `Y` is separated, then any `f : X ⤏ Y` can be realized as a partial
  map on `f.domain`, the domain of definition of `f`.
-/

@[expose] public section

universe u

open CategoryTheory hiding Quotient

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

namespace Scheme

/--
Definition of `PartialMap` / `PartialMap` 的定义

English:
structure PartialMap
  parameters: (X Y : Scheme.{u})
  axioms and operations (3):
    - domain : X.Opens
    - dense_domain : Dense (domain : Set X)
    - hom : ↑domain ⟶ Y

中文:
结构 Partial映射
  参数: (X Y : 概形.{u})
  公理与运算 (3 个):
    - domain : X.Opens
    - dense_domain : 稠密 (domain : 集合 X)
    - hom : ↑domain ⟶ Y
-/
structure PartialMap (X Y : Scheme.{u}) where
  /-- The domain of definition of a partial map. -/
  domain : X.Opens
  dense_domain : Dense (domain : Set X)
  /-- The underlying morphism of a partial map. -/
  hom : ↑domain ⟶ Y

variable (S) in
/--
Definition of `PartialMap.IsOver` / `PartialMap.IsOver` 的定义

English:
abbreviation PartialMap.IsOver
  signature: [X.Over S] [Y.Over S] (f : X.PartialMap Y)
  body: f.hom.IsOver S

中文:
缩写 Partial映射.是Over
  签名: [X.Over S] [Y.Over S] (f : X.Partial映射 Y)
  定义体: f.hom.IsOver S

Depends on / 依赖: IsOver, f.hom.IsOver
-/
abbrev PartialMap.IsOver [X.Over S] [Y.Over S] (f : X.PartialMap Y) :=
  f.hom.IsOver S

namespace PartialMap

/--
lemma `ext_iff` / 引理 `ext_iff`

English:
lemma ext_iff
  given: (f g : X.PartialMap Y)
  proof: by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U, hU, f⟩ := f
    obtain ⟨V, hV, g⟩ := g
    rintro ⟨rfl : U = V, e⟩
    congr 1
    simpa using e

@[ext]

中文:
引理 ext_iff
  条件: (f g : X.Partial映射 Y)
  证明: by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U, hU, f⟩ := f
    obtain ⟨V, hV, g⟩ := g
    rintro ⟨rfl : U = V, e⟩
    congr 1
    simpa using e

@[ext]
-/
lemma ext_iff (f g : X.PartialMap Y) :
    f = g ↔ exists e : f.domain = g.domain, f.hom = (X.isoOfEq e).hom ≫ g.hom := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U, hU, f⟩ := f
    obtain ⟨V, hV, g⟩ := g
    rintro ⟨rfl : U = V, e⟩
    congr 1
    simpa using e

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: (f g : X.PartialMap Y) (e : f.domain = g.domain)
  proof: by
  rw [ext_iff]
  exact ⟨e, H⟩

中文:
引理 ext
  结论: (f g : X.Partial映射 Y) (e : f.domain = g.domain)
  证明: by
  rw [ext_iff]
  exact ⟨e, H⟩

Depends on / 依赖: ext_iff
-/
lemma ext (f g : X.PartialMap Y) (e : f.domain = g.domain)
    (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g := by
  rw [ext_iff]
  exact ⟨e, H⟩

/-- The restriction of a partial map to a smaller domain. -/
@[simps hom domain]
noncomputable
/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (f : X.PartialMap Y) (U : X.Opens)
  body: U
  dense_domain := hU
  hom := X.homOfLE hU' ≫ f.hom

中文:
定义 restrict
  签名: (f : X.Partial映射 Y) (U : X.Opens)
  定义体: U
  dense_domain := hU
  hom := X.homOfLE hU' ≫ f.hom
-/
def restrict (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U <= f.domain) : X.PartialMap Y where
  domain := U
  dense_domain := hU
  hom := X.homOfLE hU' ≫ f.hom

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `restrict_id` / 引理 `restrict_id`

English:
lemma restrict_id
  given: (f : X.PartialMap Y)
  statement: f.restrict f.domain f.dense_domain le_rfl = f
  proof: by
  ext1 <;> simp [restrict_domain]

中文:
引理 restrict_id
  条件: (f : X.Partial映射 Y)
  结论: f.restrict f.domain f.dense_domain le_rfl = f
  证明: by
  ext1 <;> simp [restrict_domain]

Depends on / 依赖: restrict_domain
-/
lemma restrict_id (f : X.PartialMap Y) : f.restrict f.domain f.dense_domain le_rfl = f := by
  ext1 <;> simp [restrict_domain]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `restrict_id_hom` / 引理 `restrict_id_hom`

English:
lemma restrict_id_hom
  given: (f : X.PartialMap Y)
  proof: by
  simp

中文:
引理 restrict_id_hom
  条件: (f : X.Partial映射 Y)
  证明: by
  simp
-/
lemma restrict_id_hom (f : X.PartialMap Y) :
    (f.restrict f.domain f.dense_domain le_rfl).hom = f.hom := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `restrict_restrict` / 引理 `restrict_restrict`

English:
lemma restrict_restrict
  statement: (f : X.PartialMap Y)
  proof: by
  ext1 <;> simp [restrict_domain]

中文:
引理 restrict_restrict
  结论: (f : X.Partial映射 Y)
  证明: by
  ext1 <;> simp [restrict_domain]

Depends on / 依赖: restrict_domain
-/
lemma restrict_restrict (f : X.PartialMap Y)
    (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U <= f.domain)
    (V : X.Opens) (hV : Dense (V : Set X)) (hV' : V <= U) :
    (f.restrict U hU hU').restrict V hV hV' = f.restrict V hV (hV'.trans hU') := by
  ext1 <;> simp [restrict_domain]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `restrict_restrict_hom` / 引理 `restrict_restrict_hom`

English:
lemma restrict_restrict_hom
  statement: (f : X.PartialMap Y)
  proof: by
  simp

中文:
引理 restrict_restrict_hom
  结论: (f : X.Partial映射 Y)
  证明: by
  simp
-/
lemma restrict_restrict_hom (f : X.PartialMap Y)
    (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U <= f.domain)
    (V : X.Opens) (hV : Dense (V : Set X)) (hV' : V <= U) :
    ((f.restrict U hU hU').restrict V hV hV').hom = (f.restrict V hV (hV'.trans hU')).hom := by
  simp

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.Over
  signature: S] [Y.Over S] (f

中文:
实例 [X.Over
  签名: S] [Y.Over S] (f
-/
instance [X.Over S] [Y.Over S] (f : X.PartialMap Y) [f.IsOver S]
    (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U <= f.domain) :
    (f.restrict U hU hU').IsOver S where

/-- The composition of a partial map and a morphism on the right. -/
@[simps]
/--
Definition of `compHom` / `compHom` 的定义

English:
definition compHom
  signature: (f : X.PartialMap Y) (g : Y ⟶ Z)
  body: f.domain
  dense_domain := f.dense_domain
  hom := f.hom ≫ g

中文:
定义 compHom
  签名: (f : X.Partial映射 Y) (g : Y ⟶ Z)
  定义体: f.domain
  dense_domain := f.dense_domain
  hom := f.hom ≫ g

Depends on / 依赖: domain, f.domain
-/
def compHom (f : X.PartialMap Y) (g : Y ⟶ Z) : X.PartialMap Z where
  domain := f.domain
  dense_domain := f.dense_domain
  hom := f.hom ≫ g

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `compHom_id` / 引理 `compHom_id`

English:
lemma compHom_id
  given: (f : X.PartialMap Y)
  statement: f.compHom (𝟙 Y) = f
  proof: by
  ext <;> simp

中文:
引理 compHom_id
  条件: (f : X.Partial映射 Y)
  结论: f.compHom (𝟙 Y) = f
  证明: by
  ext <;> simp
-/
lemma compHom_id (f : X.PartialMap Y) : f.compHom (𝟙 Y) = f := by
  ext <;> simp

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.Over
  signature: S] [Y.Over S] [Z.Over S] (f

中文:
实例 [X.Over
  签名: S] [Y.Over S] [Z.Over S] (f
-/
instance [X.Over S] [Y.Over S] [Z.Over S] (f : X.PartialMap Y) (g : Y ⟶ Z)
    [f.IsOver S] [g.IsOver S] : (f.compHom g).IsOver S where

/-- A scheme morphism as a partial map. -/
@[simps]
/--
Definition of `_root_.AlgebraicGeometry.Scheme.Hom.toPartialMap` / `_root_.AlgebraicGeometry.Scheme.Hom.toPartialMap` 的定义

English:
definition _root_.AlgebraicGeometry.Scheme.Hom.toPartialMap
  signature: (f : X ⟶ Y)
  body: ⟨⊤, dense_univ, X.topIso.hom ≫ f⟩

中文:
定义 _root_.AlgebraicGeometry.概形.态射.toPartialMap
  签名: (f : X ⟶ Y)
  定义体: ⟨⊤, dense_univ, X.topIso.hom ≫ f⟩

Depends on / 依赖: X.topIso.hom, dense_univ, topIso
-/
def _root_.AlgebraicGeometry.Scheme.Hom.toPartialMap (f : X ⟶ Y) :
    X.PartialMap Y := ⟨⊤, dense_univ, X.topIso.hom ≫ f⟩

set_option backward.defeqAttrib.useBackward true in
instance (f : X ⟶ Y) [IsDominant f] : IsDominant f.toPartialMap.hom := by
  dsimp
  have := Opens.isDominant_ι (X := X) (U := ⊤) dense_univ
  infer_instance

/--
lemma `_root_.AlgebraicGeometry.Scheme.Hom.toPartialMap_compHom` / 引理 `_root_.AlgebraicGeometry.Scheme.Hom.toPartialMap_compHom`

English:
lemma _root_.AlgebraicGeometry.Scheme.Hom.toPartialMap_compHom
  given: (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 _root_.AlgebraicGeometry.概形.态射.toPartialMap_compHom
  条件: (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma _root_.AlgebraicGeometry.Scheme.Hom.toPartialMap_compHom (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.toPartialMap.compHom g = (f ≫ g).toPartialMap := rfl

variable (X) in
/--
Definition of `id` / `id` 的定义

English:
abbreviation id
  signature: : X.PartialMap X
  body: (𝟙 X : X ⟶ X).toPartialMap

中文:
缩写 id
  签名: : X.Partial映射 X
  定义体: (𝟙 X : X ⟶ X).toPartialMap
-/
protected abbrev id : X.PartialMap X := (𝟙 X : X ⟶ X).toPartialMap

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `id_compHom` / 引理 `id_compHom`

English:
lemma id_compHom
  given: (f : X ⟶ Y)
  statement: (PartialMap.id X).compHom f = f.toPartialMap
  proof: by
  apply PartialMap.ext _ _ rfl
  simp

中文:
引理 id_compHom
  条件: (f : X ⟶ Y)
  结论: (Partial映射.id X).compHom f = f.toPartialMap
  证明: by
  apply PartialMap.ext _ _ rfl
  simp

Depends on / 依赖: PartialMap, PartialMap.ext
-/
lemma id_compHom (f : X ⟶ Y) : (PartialMap.id X).compHom f = f.toPartialMap := by
  apply PartialMap.ext _ _ rfl
  simp

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.Over
  signature: S] [Y.Over S] (f

中文:
实例 [X.Over
  签名: S] [Y.Over S] (f
-/
instance [X.Over S] [Y.Over S] (f : X ⟶ Y) [f.IsOver S] : f.toPartialMap.IsOver S where

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isOver_iff` / 引理 `isOver_iff`

English:
lemma isOver_iff
  given: [X.Over S] [Y.Over S] {f : X.PartialMap Y}
  proof: by
  simp

中文:
引理 isOver_iff
  条件: [X.Over S] [Y.Over S] {f : X.Partial映射 Y}
  证明: by
  simp
-/
lemma isOver_iff [X.Over S] [Y.Over S] {f : X.PartialMap Y} :
    f.IsOver S ↔ (f.compHom (Y ↘ S)).hom = f.domain.ι ≫ X ↘ S := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isOver_iff_eq_restrict` / 引理 `isOver_iff_eq_restrict`

English:
lemma isOver_iff_eq_restrict
  given: [X.Over S] [Y.Over S] {f : X.PartialMap Y}
  proof: by
  simp [PartialMap.ext_iff]

中文:
引理 isOver_iff_eq_restrict
  条件: [X.Over S] [Y.Over S] {f : X.Partial映射 Y}
  证明: by
  simp [PartialMap.ext_iff]

Depends on / 依赖: PartialMap, PartialMap.ext_iff, ext_iff
-/
lemma isOver_iff_eq_restrict [X.Over S] [Y.Over S] {f : X.PartialMap Y} :
    f.IsOver S ↔ f.compHom (Y ↘ S) = (X ↘ S).toPartialMap.restrict _ f.dense_domain (by simp) := by
  simp [PartialMap.ext_iff]

/-- If `x` is in the domain of a partial map `f`, then `f` restricts to a map from `Spec 𝒪_x`. -/
noncomputable
/--
Definition of `fromSpecStalkOfMem` / `fromSpecStalkOfMem` 的定义

English:
definition fromSpecStalkOfMem
  signature: (f : X.PartialMap Y) {x} (hx : x in f.domain)
  body: f.domain.fromSpecStalkOfMem x hx ≫ f.hom

中文:
定义 fromSpecStalkOfMem
  签名: (f : X.Partial映射 Y) {x} (hx : x in f.domain)
  定义体: f.domain.fromSpecStalkOfMem x hx ≫ f.hom

Depends on / 依赖: domain, f.domain.fromSpecStalkOfMem, f.hom, fromSpecStalkOfMem
-/
def fromSpecStalkOfMem (f : X.PartialMap Y) {x} (hx : x in f.domain) :
    Spec (X.presheaf.stalk x) ⟶ Y :=
  f.domain.fromSpecStalkOfMem x hx ≫ f.hom

/-- A partial map restricts to a map from `Spec K(X)`. -/
noncomputable
/--
Definition of `fromFunctionField` / `fromFunctionField` 的定义

English:
abbreviation fromFunctionField
  signature: [IrreducibleSpace X] (f : X.PartialMap Y)
  body: f.fromSpecStalkOfMem
    ((genericPoint_specializes _).mem_open f.domain.2 f.dense_domain.nonempty.choose_spec)

中文:
缩写 fromFunctionField
  签名: [不可约空间 X] (f : X.Partial映射 Y)
  定义体: f.fromSpecStalkOfMem
    ((genericPoint_specializes _).mem_open f.domain.2 f.dense_domain.nonempty.choose_spec)

Depends on / 依赖: choose_spec, dense_domain, domain, f.dense_domain.nonempty.choose_spec, f.domain, f.fromSpecStalkOfMem, fromSpecStalkOfMem, genericPoint_specializes, mem_open, nonempty
-/
abbrev fromFunctionField [IrreducibleSpace X] (f : X.PartialMap Y) :
    Spec X.functionField ⟶ Y :=
  f.fromSpecStalkOfMem
    ((genericPoint_specializes _).mem_open f.domain.2 f.dense_domain.nonempty.choose_spec)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `fromSpecStalkOfMem_restrict` / 引理 `fromSpecStalkOfMem_restrict`

English:
lemma fromSpecStalkOfMem_restrict
  statement: (f : X.PartialMap Y)
  proof: by
  dsimp only [fromSpecStalkOfMem, restrict, Scheme.Opens.fromSpecStalkOfMem]
  have e : ⟨x, hU' hx⟩ = X.homOfLE hU' ⟨x, hx⟩ := by
    rw [Scheme.homOfLE_base]
    rfl
  rw [Category.assoc]; rw [← SpecMap_stalkMap_fromSpecStalk_assoc]; rw [← SpecMap_stalkSpecializes_fromSpecStalk (Inseparable.of_e

中文:
引理 fromSpecStalkOfMem_restrict
  结论: (f : X.Partial映射 Y)
  证明: by
  dsimp only [fromSpecStalkOfMem, restrict, Scheme.Opens.fromSpecStalkOfMem]
  have e : ⟨x, hU' hx⟩ = X.homOfLE hU' ⟨x, hx⟩ := by
    rw [Scheme.homOfLE_base]
    rfl
  rw [Category.assoc]; rw [← SpecMap_stalkMap_fromSpecStalk_assoc]; rw [← SpecMap_stalkSpecializes_fromSpecStalk (Inseparable.of_e

Depends on / 依赖: Category, Category.assoc, Inseparable, Inseparable.of_eq, IsIso.comp_inv_eq, Iso.eq_inv_comp, Presheaf, Scheme, Scheme.Opens.fromSpecStalkOfMem, Scheme.homOfLE_base, Spec.map_comp, SpecMap_stalkMap_fromSpecStalk_assoc, SpecMap_stalkSpecializes_fromSpecStalk, TopCat, TopCat.Presheaf.stalkCongr_inv, X.homOfLE, comp_inv_eq, eq_inv_comp, fromSpecStalkOfMem, homOfLE
-/
lemma fromSpecStalkOfMem_restrict (f : X.PartialMap Y)
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U <= f.domain) {x} (hx : x in U) :
    (f.restrict U hU hU').fromSpecStalkOfMem hx = f.fromSpecStalkOfMem (hU' hx) := by
  dsimp only [fromSpecStalkOfMem, restrict, Scheme.Opens.fromSpecStalkOfMem]
  have e : ⟨x, hU' hx⟩ = X.homOfLE hU' ⟨x, hx⟩ := by
    rw [Scheme.homOfLE_base]
    rfl
  rw [Category.assoc]; rw [← SpecMap_stalkMap_fromSpecStalk_assoc]; rw [← SpecMap_stalkSpecializes_fromSpecStalk (Inseparable.of_eq e).specializes]; rw [← TopCat.Presheaf.stalkCongr_inv _ (Inseparable.of_eq e)]
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 3
  rw [Iso.eq_inv_comp]; rw [← Category.assoc]; rw [IsIso.comp_inv_eq]; rw [IsIso.eq_inv_comp]; rw [Hom.stalkMap_congr_hom _ _ (X.homOfLE_ι hU').symm]
  simp only [TopCat.Presheaf.stalkCongr_hom]
  rw [← Hom.stalkSpecializes_stalkMap_assoc]; rw [Hom.stalkMap_comp]

/--
lemma `fromFunctionField_restrict` / 引理 `fromFunctionField_restrict`

English:
lemma fromFunctionField_restrict
  statement: (f : X.PartialMap Y) [IrreducibleSpace X]
  proof: fromSpecStalkOfMem_restrict f _ _ _

中文:
引理 fromFunctionField_restrict
  结论: (f : X.Partial映射 Y) [不可约空间 X]
  证明: fromSpecStalkOfMem_restrict f _ _ _

Depends on / 依赖: fromSpecStalkOfMem_restrict
-/
lemma fromFunctionField_restrict (f : X.PartialMap Y) [IrreducibleSpace X]
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U <= f.domain) :
    (f.restrict U hU hU').fromFunctionField = f.fromFunctionField :=
  fromSpecStalkOfMem_restrict f _ _ _

/--
Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and
`X` is irreducible germ-injective at `x` (e.g. when `X` is integral),
any `S`-morphism `Spec 𝒪ₓ ⟶ Y` spreads out to a partial map from `X` to `Y`.
-/
noncomputable
/--
Definition of `ofFromSpecStalk` / `ofFromSpecStalk` 的定义

English:
definition ofFromSpecStalk
  signature: [IrreducibleSpace X] [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x]
  body: (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose
  domain := (spread_out_of_isGermInjective' sX sY φ h).choose
  dense_domain := (spread_out_of_isGermInjective' sX sY φ h).choose.2.dense
    ⟨_, (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose⟩

中文:
定义 ofFromSpecStalk
  签名: [不可约空间 X] [局部有限型 sY] {x : X} [X.是GermInjectiveAt x]
  定义体: (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose
  domain := (spread_out_of_isGermInjective' sX sY φ h).choose
  dense_domain := (spread_out_of_isGermInjective' sX sY φ h).choose.2.dense
    ⟨_, (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose⟩

Depends on / 依赖: choose_spec, choose_spec.choose_spec.choose, spread_out_of_isGermInjective
-/
def ofFromSpecStalk [IrreducibleSpace X] [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x]
    (φ : Spec (X.presheaf.stalk x) ⟶ Y) (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) : X.PartialMap Y where
  hom := (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose
  domain := (spread_out_of_isGermInjective' sX sY φ h).choose
  dense_domain := (spread_out_of_isGermInjective' sX sY φ h).choose.2.dense
    ⟨_, (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose⟩

/--
lemma `ofFromSpecStalk_comp` / 引理 `ofFromSpecStalk_comp`

English:
lemma ofFromSpecStalk_comp
  statement: [IrreducibleSpace X] [LocallyOfFiniteType sY]
  proof: (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose_spec.2

中文:
引理 ofFromSpecStalk_comp
  结论: [不可约空间 X] [局部有限型 sY]
  证明: (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose_spec.2

Depends on / 依赖: choose_spec, choose_spec.choose_spec.choose_spec, spread_out_of_isGermInjective
-/
lemma ofFromSpecStalk_comp [IrreducibleSpace X] [LocallyOfFiniteType sY]
    {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.presheaf.stalk x) ⟶ Y)
    (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) :
    (ofFromSpecStalk sX sY φ h).hom ≫ sY = (ofFromSpecStalk sX sY φ h).domain.ι ≫ sX :=
  (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose_spec.2

/--
lemma `mem_domain_ofFromSpecStalk` / 引理 `mem_domain_ofFromSpecStalk`

English:
lemma mem_domain_ofFromSpecStalk
  statement: [IrreducibleSpace X] [LocallyOfFiniteType sY]
  proof: (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose

中文:
引理 mem_domain_ofFromSpecStalk
  结论: [不可约空间 X] [局部有限型 sY]
  证明: (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose, spread_out_of_isGermInjective
-/
lemma mem_domain_ofFromSpecStalk [IrreducibleSpace X] [LocallyOfFiniteType sY]
    {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.presheaf.stalk x) ⟶ Y)
    (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) : x in (ofFromSpecStalk sX sY φ h).domain :=
  (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose

/--
lemma `fromSpecStalkOfMem_ofFromSpecStalk` / 引理 `fromSpecStalkOfMem_ofFromSpecStalk`

English:
lemma fromSpecStalkOfMem_ofFromSpecStalk
  statement: [IrreducibleSpace X] [LocallyOfFiniteType sY]
  proof: (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose_spec.1.symm

中文:
引理 fromSpecStalkOfMem_ofFromSpecStalk
  结论: [不可约空间 X] [局部有限型 sY]
  证明: (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose_spec.1.symm

Depends on / 依赖: choose_spec, choose_spec.choose_spec.choose_spec, spread_out_of_isGermInjective
-/
lemma fromSpecStalkOfMem_ofFromSpecStalk [IrreducibleSpace X] [LocallyOfFiniteType sY]
    {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.presheaf.stalk x) ⟶ Y)
    (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) :
    (ofFromSpecStalk sX sY φ h).fromSpecStalkOfMem (mem_domain_ofFromSpecStalk sX sY φ h) = φ :=
  (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose_spec.1.symm

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `fromSpecStalkOfMem_compHom` / 引理 `fromSpecStalkOfMem_compHom`

English:
lemma fromSpecStalkOfMem_compHom
  given: (f : X.PartialMap Y) (g : Y ⟶ Z) (x) (hx)
  proof: by
  simp [fromSpecStalkOfMem]

中文:
引理 fromSpecStalkOfMem_compHom
  条件: (f : X.Partial映射 Y) (g : Y ⟶ Z) (x) (hx)
  证明: by
  simp [fromSpecStalkOfMem]

Depends on / 依赖: f.fromSpecStalkOfMem, fromSpecStalkOfMem
-/
lemma fromSpecStalkOfMem_compHom (f : X.PartialMap Y) (g : Y ⟶ Z) (x) (hx) :
    (f.compHom g).fromSpecStalkOfMem (x := x) hx = f.fromSpecStalkOfMem hx ≫ g := by
  simp [fromSpecStalkOfMem]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `fromSpecStalkOfMem_toPartialMap` / 引理 `fromSpecStalkOfMem_toPartialMap`

English:
lemma fromSpecStalkOfMem_toPartialMap
  given: (f : X ⟶ Y) (x)
  proof: by
  simp [fromSpecStalkOfMem]

中文:
引理 fromSpecStalkOfMem_toPartialMap
  条件: (f : X ⟶ Y) (x)
  证明: by
  simp [fromSpecStalkOfMem]

Depends on / 依赖: X.fromSpecStalk, fromSpecStalk, fromSpecStalkOfMem
-/
lemma fromSpecStalkOfMem_toPartialMap (f : X ⟶ Y) (x) :
    f.toPartialMap.fromSpecStalkOfMem (x := x) trivial = X.fromSpecStalk x ≫ f := by
  simp [fromSpecStalkOfMem]

/-- Two partial maps are equivalent if they are equal on a dense open subscheme. -/
protected noncomputable
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: (f g : X.PartialMap Y)
  body: exists (W : X.Opens) (hW : Dense (W : Set X)) (hWl : W <= f.domain) (hWr : W <= g.domain),
    (f.restrict W hW hWl).hom = (g.restrict W hW hWr).hom

中文:
定义 equiv
  签名: (f g : X.Partial映射 Y)
  定义体: exists (W : X.Opens) (hW : Dense (W : Set X)) (hWl : W <= f.domain) (hWr : W <= g.domain),
    (f.restrict W hW hWl).hom = (g.restrict W hW hWr).hom

Depends on / 依赖: X.Opens, domain, f.domain, f.restrict, g.domain, g.restrict, restrict
-/
def equiv (f g : X.PartialMap Y) : Prop :=
  exists (W : X.Opens) (hW : Dense (W : Set X)) (hWl : W <= f.domain) (hWr : W <= g.domain),
    (f.restrict W hW hWl).hom = (g.restrict W hW hWr).hom

/--
lemma `equiv_of_restrict_eq` / 引理 `equiv_of_restrict_eq`

English:
lemma equiv_of_restrict_eq
  statement: (f g : X.PartialMap Y) {W₁ W₂ : X.Opens} {hW₁ : Dense (W₁ : Set X)}
  proof: by
  have e : W₁ = W₂ := congr($(H).domain)
  subst e
  exact ⟨W₁, hW₁, hW₁', hW₂', congr($(H).hom)⟩

中文:
引理 equiv_of_restrict_eq
  结论: (f g : X.Partial映射 Y) {W₁ W₂ : X.Opens} {hW₁ : 稠密 (W₁ : 集合 X)}
  证明: by
  have e : W₁ = W₂ := congr($(H).domain)
  subst e
  exact ⟨W₁, hW₁, hW₁', hW₂', congr($(H).hom)⟩

Depends on / 依赖: domain
-/
lemma equiv_of_restrict_eq (f g : X.PartialMap Y) {W₁ W₂ : X.Opens} {hW₁ : Dense (W₁ : Set X)}
    {hW₂ : Dense (W₂ : Set X)} {hW₁' : W₁ <= f.domain} {hW₂' : W₂ <= g.domain}
    (H : f.restrict W₁ hW₁ hW₁' = g.restrict W₂ hW₂ hW₂') : f.equiv g := by
  have e : W₁ = W₂ := congr($(H).domain)
  subst e
  exact ⟨W₁, hW₁, hW₁', hW₂', congr($(H).hom)⟩

set_option backward.isDefEq.respectTransparency false in
@[refl]
/--
lemma `equiv.refl` / 引理 `equiv.refl`

English:
lemma equiv.refl
  given: (f : X.PartialMap Y)
  statement: f.equiv f
  proof: ⟨f.domain, f.dense_domain, by simp⟩

@[symm]

中文:
引理 equiv.refl
  条件: (f : X.Partial映射 Y)
  结论: f.equiv f
  证明: ⟨f.domain, f.dense_domain, by simp⟩

@[symm]

Depends on / 依赖: dense_domain, domain, f.dense_domain, f.domain
-/
lemma equiv.refl (f : X.PartialMap Y) : f.equiv f :=
  ⟨f.domain, f.dense_domain, by simp⟩

@[symm]
/--
lemma `equiv.symm` / 引理 `equiv.symm`

English:
lemma equiv.symm
  given: {f g : X.PartialMap Y}
  statement: f.equiv g -> g.equiv f
  proof: by
  intro ⟨W, hW, hWl, hWr, e⟩
  exact ⟨W, hW, hWr, hWl, e.symm⟩

中文:
引理 equiv.symm
  条件: {f g : X.Partial映射 Y}
  结论: f.equiv g -> g.equiv f
  证明: by
  intro ⟨W, hW, hWl, hWr, e⟩
  exact ⟨W, hW, hWr, hWl, e.symm⟩

Depends on / 依赖: e.symm
-/
lemma equiv.symm {f g : X.PartialMap Y} : f.equiv g -> g.equiv f := by
  intro ⟨W, hW, hWl, hWr, e⟩
  exact ⟨W, hW, hWr, hWl, e.symm⟩

set_option backward.defeqAttrib.useBackward true in
@[trans]
/--
lemma `equiv.trans` / 引理 `equiv.trans`

English:
lemma equiv.trans
  given: {f g h : X.PartialMap Y}
  statement: f.equiv g -> g.equiv h -> f.equiv h
  proof: by
  intro ⟨W₁, hW₁, hW₁l, hW₁r, e₁⟩ ⟨W₂, hW₂, hW₂l, hW₂r, e₂⟩
  refine ⟨W₁ ⊓ W₂, hW₁.inter_of_isOpen_left hW₂ W₁.2, inf_le_left.trans hW₁l,
    inf_le_right.trans hW₂r, ?_⟩
  dsimp at e₁ e₂
  simp only [restrict_domain, restrict_hom, ← X.homOfLE_homOfLE (U := W₁ ⊓ W₂) inf_le_left hW₁l,
    Category

中文:
引理 equiv.trans
  条件: {f g h : X.Partial映射 Y}
  结论: f.equiv g -> g.equiv h -> f.equiv h
  证明: by
  intro ⟨W₁, hW₁, hW₁l, hW₁r, e₁⟩ ⟨W₂, hW₂, hW₂l, hW₂r, e₂⟩
  refine ⟨W₁ ⊓ W₂, hW₁.inter_of_isOpen_left hW₂ W₁.2, inf_le_left.trans hW₁l,
    inf_le_right.trans hW₂r, ?_⟩
  dsimp at e₁ e₂
  simp only [restrict_domain, restrict_hom, ← X.homOfLE_homOfLE (U := W₁ ⊓ W₂) inf_le_left hW₁l,
    Category

Depends on / 依赖: Category, Category.assoc, X.homOfLE_homOfLE, homOfLE_homOfLE, homOfLE_homOfLE_assoc, inf_le_left, inf_le_left.trans, inf_le_right, inf_le_right.trans, inter_of_isOpen_left, restrict_domain, restrict_hom
-/
lemma equiv.trans {f g h : X.PartialMap Y} : f.equiv g -> g.equiv h -> f.equiv h := by
  intro ⟨W₁, hW₁, hW₁l, hW₁r, e₁⟩ ⟨W₂, hW₂, hW₂l, hW₂r, e₂⟩
  refine ⟨W₁ ⊓ W₂, hW₁.inter_of_isOpen_left hW₂ W₁.2, inf_le_left.trans hW₁l,
    inf_le_right.trans hW₂r, ?_⟩
  dsimp at e₁ e₂
  simp only [restrict_domain, restrict_hom, ← X.homOfLE_homOfLE (U := W₁ ⊓ W₂) inf_le_left hW₁l,
    Category.assoc, e₁, ← X.homOfLE_homOfLE (U := W₁ ⊓ W₂) inf_le_right hW₂r, ← e₂]
  simp only [homOfLE_homOfLE_assoc]

/--
lemma `equivalence_rel` / 引理 `equivalence_rel`

English:
lemma equivalence_rel
  statement: Equivalence (@Scheme.PartialMap.equiv X Y) where
  proof: equiv.refl
  symm := equiv.symm
  trans := equiv.trans

中文:
引理 equivalence_rel
  结论: 等价 (@概形.Partial映射.equiv X Y) where
  证明: equiv.refl
  symm := equiv.symm
  trans := equiv.trans

Depends on / 依赖: equiv.refl
-/
lemma equivalence_rel : Equivalence (@Scheme.PartialMap.equiv X Y) where
  refl := equiv.refl
  symm := equiv.symm
  trans := equiv.trans

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Setoid (X.PartialMap Y)
  body: ⟨@PartialMap.equiv X Y, equivalence_rel⟩

中文:
实例 :
  签名: 集合等价关系 (X.Partial映射 Y)
  定义体: ⟨@PartialMap.equiv X Y, equivalence_rel⟩

Depends on / 依赖: PartialMap, PartialMap.equiv, equivalence_rel
-/
instance : Setoid (X.PartialMap Y) := ⟨@PartialMap.equiv X Y, equivalence_rel⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `restrict_equiv` / 引理 `restrict_equiv`

English:
lemma restrict_equiv
  statement: (f : X.PartialMap Y) (U : X.Opens)
  proof: ⟨U, hU, le_rfl, hU', by simp⟩

中文:
引理 restrict_equiv
  结论: (f : X.Partial映射 Y) (U : X.Opens)
  证明: ⟨U, hU, le_rfl, hU', by simp⟩

Depends on / 依赖: le_rfl
-/
lemma restrict_equiv (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U <= f.domain) : (f.restrict U hU hU').equiv f :=
  ⟨U, hU, le_rfl, hU', by simp⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `equiv_of_fromSpecStalkOfMem_eq` / 引理 `equiv_of_fromSpecStalkOfMem_eq`

English:
lemma equiv_of_fromSpecStalkOfMem_eq
  statement: [IrreducibleSpace X]
  proof: by
  have hdense : Dense ((f.domain ⊓ g.domain) : Set X) :=
    f.dense_domain.inter_of_isOpen_left g.dense_domain f.domain.2
  have := (isGermInjectiveAt_iff_of_isOpenImmersion (f := (f.domain ⊓ g.domain).ι)
    (x := ⟨x, hxf, hxg⟩)).mp ‹_›
  have := spread_out_unique_of_isGermInjective' (X := (f.d

中文:
引理 equiv_of_fromSpecStalkOfMem_eq
  结论: [不可约空间 X]
  证明: by
  have hdense : Dense ((f.domain ⊓ g.domain) : Set X) :=
    f.dense_domain.inter_of_isOpen_left g.dense_domain f.domain.2
  have := (isGermInjectiveAt_iff_of_isOpenImmersion (f := (f.domain ⊓ g.domain).ι)
    (x := ⟨x, hxf, hxg⟩)).mp ‹_›
  have := spread_out_unique_of_isGermInjective' (X := (f.d

Depends on / 依赖: X.homOfLE, dense_domain, domain, f.dense_domain.inter_of_isOpen_left, f.domain, f.hom, g.dense_domain, g.domain, g.hom, hdense, homOfLE, inf_le_left, inf_le_right, inter_of_isOpen_left, isGermInjectiveAt_iff_of_isOpenImmersion, spread_out_unique_of_isGermInjective, toScheme
-/
lemma equiv_of_fromSpecStalkOfMem_eq [IrreducibleSpace X]
    {x : X} [X.IsGermInjectiveAt x] (f g : X.PartialMap Y)
    (hxf : x in f.domain) (hxg : x in g.domain)
    (H : f.fromSpecStalkOfMem hxf = g.fromSpecStalkOfMem hxg) : f.equiv g := by
  have hdense : Dense ((f.domain ⊓ g.domain) : Set X) :=
    f.dense_domain.inter_of_isOpen_left g.dense_domain f.domain.2
  have := (isGermInjectiveAt_iff_of_isOpenImmersion (f := (f.domain ⊓ g.domain).ι)
    (x := ⟨x, hxf, hxg⟩)).mp ‹_›
  have := spread_out_unique_of_isGermInjective' (X := (f.domain ⊓ g.domain).toScheme)
    (X.homOfLE inf_le_left ≫ f.hom) (X.homOfLE inf_le_right ≫ g.hom) (x := ⟨x, hxf, hxg⟩) ?_
  · obtain ⟨U, hxU, e⟩ := this
    refine ⟨(f.domain ⊓ g.domain).ι ''ᵁ U, ((f.domain ⊓ g.domain).ι ''ᵁ U).2.dense
      ⟨_, ⟨_, hxU, rfl⟩⟩,
      ((Set.image_subset_range _ _).trans_eq (Subtype.range_val)).trans inf_le_left,
      ((Set.image_subset_range _ _).trans_eq (Subtype.range_val)).trans inf_le_right, ?_⟩
    rw [← cancel_epi (Scheme.Hom.isoImage _ _).hom]
    simp only [restrict_hom, ← Category.assoc] at e ⊢
    convert! e using 2 <;> rw [← cancel_mono (Scheme.Opens.ι _)] <;> simp
  · rw [← f.fromSpecStalkOfMem_restrict hdense inf_le_left ⟨hxf, hxg⟩,
      ← g.fromSpecStalkOfMem_restrict hdense inf_le_right ⟨hxf, hxg⟩] at H
    simpa only [fromSpecStalkOfMem, restrict_domain, Opens.fromSpecStalkOfMem, Spec.map_inv,
      restrict_hom, Category.assoc, IsIso.eq_inv_comp, IsIso.hom_inv_id_assoc] using H

set_option backward.isDefEq.respectTransparency false in
/--
lemma `equiv_iff_of_isSeparated_of_le` / 引理 `equiv_iff_of_isSeparated_of_le`

English:
lemma equiv_iff_of_isSeparated_of_le
  statement: [X.Over S] [Y.Over S] [IsReduced X]
  proof: by
  refine ⟨fun ⟨V, hV, hVl, hVr, e⟩ => ?_, fun e => ⟨_, _, _, _, e⟩⟩
  have : IsDominant (X.homOfLE (inf_le_left : W ⊓ V <= W)) :=
    Opens.isDominant_homOfLE (hW.inter_of_isOpen_left hV W.2) _
  apply ext_of_isDominant_of_isSeparated' S (X.homOfLE (inf_le_left : W ⊓ V <= W))
  simpa using congr(

中文:
引理 equiv_iff_of_isSeparated_of_le
  结论: [X.Over S] [Y.Over S] [是既约 X]
  证明: by
  refine ⟨fun ⟨V, hV, hVl, hVr, e⟩ => ?_, fun e => ⟨_, _, _, _, e⟩⟩
  have : IsDominant (X.homOfLE (inf_le_left : W ⊓ V <= W)) :=
    Opens.isDominant_homOfLE (hW.inter_of_isOpen_left hV W.2) _
  apply ext_of_isDominant_of_isSeparated' S (X.homOfLE (inf_le_left : W ⊓ V <= W))
  simpa using congr(

Depends on / 依赖: domain, f.domain, f.equiv, g.domain
-/
lemma equiv_iff_of_isSeparated_of_le [X.Over S] [Y.Over S] [IsReduced X]
    [IsSeparated (Y ↘ S)] {f g : X.PartialMap Y} [f.IsOver S] [g.IsOver S]
    {W : X.Opens} (hW : Dense (X := X) W) (hWl : W <= f.domain) (hWr : W <= g.domain) : f.equiv g ↔
      (f.restrict W hW hWl).hom = (g.restrict W hW hWr).hom := by
  refine ⟨fun ⟨V, hV, hVl, hVr, e⟩ => ?_, fun e => ⟨_, _, _, _, e⟩⟩
  have : IsDominant (X.homOfLE (inf_le_left : W ⊓ V <= W)) :=
    Opens.isDominant_homOfLE (hW.inter_of_isOpen_left hV W.2) _
  apply ext_of_isDominant_of_isSeparated' S (X.homOfLE (inf_le_left : W ⊓ V <= W))
  simpa using congr(X.homOfLE (inf_le_right : W ⊓ V <= V) ≫ $e)

/--
lemma `equiv_iff_of_isSeparated` / 引理 `equiv_iff_of_isSeparated`

English:
lemma equiv_iff_of_isSeparated
  statement: [X.Over S] [Y.Over S] [IsReduced X]
  proof: equiv_iff_of_isSeparated_of_le (S := S) _ _ _

中文:
引理 equiv_iff_of_isSeparated
  结论: [X.Over S] [Y.Over S] [是既约 X]
  证明: equiv_iff_of_isSeparated_of_le (S := S) _ _ _

Depends on / 依赖: equiv_iff_of_isSeparated_of_le
-/
lemma equiv_iff_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X]
    [IsSeparated (Y ↘ S)] {f g : X.PartialMap Y}
    [f.IsOver S] [g.IsOver S] : f.equiv g ↔
      (f.restrict _ (f.2.inter_of_isOpen_left g.2 f.domain.2) inf_le_left).hom =
      (g.restrict _ (f.2.inter_of_isOpen_left g.2 f.domain.2) inf_le_right).hom :=
  equiv_iff_of_isSeparated_of_le (S := S) _ _ _

set_option backward.defeqAttrib.useBackward true in
/--
lemma `equiv_iff_of_domain_eq_of_isSeparated` / 引理 `equiv_iff_of_domain_eq_of_isSeparated`

English:
lemma equiv_iff_of_domain_eq_of_isSeparated
  statement: [X.Over S] [Y.Over S] [IsReduced X]
  proof: by
  rw [equiv_iff_of_isSeparated_of_le (S := S) f.dense_domain le_rfl hfg.le]
  obtain ⟨Uf, _, f⟩ := f
  obtain ⟨Ug, _, g⟩ := g
  obtain rfl : Uf = Ug := hfg
  simp

中文:
引理 equiv_iff_of_domain_eq_of_isSeparated
  结论: [X.Over S] [Y.Over S] [是既约 X]
  证明: by
  rw [equiv_iff_of_isSeparated_of_le (S := S) f.dense_domain le_rfl hfg.le]
  obtain ⟨Uf, _, f⟩ := f
  obtain ⟨Ug, _, g⟩ := g
  obtain rfl : Uf = Ug := hfg
  simp

Depends on / 依赖: dense_domain, equiv_iff_of_isSeparated_of_le, f.dense_domain, hfg.le, le_rfl
-/
lemma equiv_iff_of_domain_eq_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X]
    [IsSeparated (Y ↘ S)] {f g : X.PartialMap Y} (hfg : f.domain = g.domain)
    [f.IsOver S] [g.IsOver S] : f.equiv g ↔ f = g := by
  rw [equiv_iff_of_isSeparated_of_le (S := S) f.dense_domain le_rfl hfg.le]
  obtain ⟨Uf, _, f⟩ := f
  obtain ⟨Ug, _, g⟩ := g
  obtain rfl : Uf = Ug := hfg
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `equiv_toPartialMap_iff_of_isSeparated` / 引理 `equiv_toPartialMap_iff_of_isSeparated`

English:
lemma equiv_toPartialMap_iff_of_isSeparated
  statement: [X.Over S] [Y.Over S] [IsReduced X]
  proof: by
  rw [equiv_iff_of_isSeparated (S := S)]; rw [← cancel_epi (X.isoOfEq (inf_top_eq f.domain)).hom]
  simp
  rfl

中文:
引理 equiv_toPartialMap_iff_of_isSeparated
  结论: [X.Over S] [Y.Over S] [是既约 X]
  证明: by
  rw [equiv_iff_of_isSeparated (S := S)]; rw [← cancel_epi (X.isoOfEq (inf_top_eq f.domain)).hom]
  simp
  rfl

Depends on / 依赖: X.isoOfEq, cancel_epi, domain, equiv_iff_of_isSeparated, f.domain, inf_top_eq, isoOfEq
-/
lemma equiv_toPartialMap_iff_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X]
    [IsSeparated (Y ↘ S)] {f : X.PartialMap Y} {g : X ⟶ Y}
    [f.IsOver S] [g.IsOver S] : f.equiv g.toPartialMap ↔
      f.hom = f.domain.ι ≫ g := by
  rw [equiv_iff_of_isSeparated (S := S)]; rw [← cancel_epi (X.isoOfEq (inf_top_eq f.domain)).hom]
  simp
  rfl

end PartialMap

/--
Definition of `RationalMap` / `RationalMap` 的定义

English:
definition RationalMap
  signature: (X Y : Scheme.{u})
  body: @Quotient (X.PartialMap Y) inferInstance

中文:
定义 RationalMap
  签名: (X Y : 概形.{u})
  定义体: @Quotient (X.PartialMap Y) inferInstance

Depends on / 依赖: PartialMap, Quotient, X.PartialMap
-/
def RationalMap (X Y : Scheme.{u}) : Type u :=
  @Quotient (X.PartialMap Y) inferInstance

/-- The notation for rational maps. -/
scoped[AlgebraicGeometry] infix:10 " ⤏ " => Scheme.RationalMap

/--
Definition of `PartialMap.toRationalMap` / `PartialMap.toRationalMap` 的定义

English:
definition PartialMap.toRationalMap
  signature: (f : X.PartialMap Y)
  body: Quotient.mk _ f

中文:
定义 Partial映射.toRationalMap
  签名: (f : X.Partial映射 Y)
  定义体: Quotient.mk _ f

Depends on / 依赖: Quotient, Quotient.mk
-/
def PartialMap.toRationalMap (f : X.PartialMap Y) : X ⤏ Y := Quotient.mk _ f

/--
Definition of `Hom.toRationalMap` / `Hom.toRationalMap` 的定义

English:
abbreviation Hom.toRationalMap
  signature: (f : X.Hom Y)
  body: f.toPartialMap.toRationalMap

中文:
缩写 态射.toRationalMap
  签名: (f : X.态射 Y)
  定义体: f.toPartialMap.toRationalMap

Depends on / 依赖: f.toPartialMap.toRationalMap, toPartialMap, toRationalMap
-/
abbrev Hom.toRationalMap (f : X.Hom Y) : X ⤏ Y := f.toPartialMap.toRationalMap

variable (X) in
/--
Definition of `RationalMap.id` / `RationalMap.id` 的定义

English:
abbreviation RationalMap.id
  signature: : X ⤏ X
  body: (PartialMap.id X).toRationalMap

中文:
缩写 RationalMap.id
  签名: : X ⤏ X
  定义体: (PartialMap.id X).toRationalMap

Depends on / 依赖: PartialMap, PartialMap.id, toRationalMap
-/
abbrev RationalMap.id : X ⤏ X := (PartialMap.id X).toRationalMap

variable (S) in
/--
Definition of `RationalMap.IsOver` / `RationalMap.IsOver` 的定义

English:
class RationalMap.IsOver
  parameters: [X.Over S] [Y.Over S] (f : X ⤏ Y)
  axioms and operations (1):
    - exists_partialMap_over : exists g : X.PartialMap Y, g.IsOver S ∧ g.toRationalMap = f

中文:
类 RationalMap.是Over
  参数: [X.Over S] [Y.Over S] (f : X ⤏ Y)
  公理与运算 (1 个):
    - exists_partialMap_over : 存在 g : X.Partial映射 Y, g.是Over S ∧ g.toRationalMap = f
-/
class RationalMap.IsOver [X.Over S] [Y.Over S] (f : X ⤏ Y) : Prop where
  exists_partialMap_over : exists g : X.PartialMap Y, g.IsOver S ∧ g.toRationalMap = f

/--
lemma `PartialMap.toRationalMap_surjective` / 引理 `PartialMap.toRationalMap_surjective`

English:
lemma PartialMap.toRationalMap_surjective
  statement: Function.Surjective (@toRationalMap X Y)
  proof: Quotient.exists_rep

中文:
引理 Partial映射.toRationalMap_surjective
  结论: 函数.满射 (@toRationalMap X Y)
  证明: Quotient.exists_rep

Depends on / 依赖: Quotient, Quotient.exists_rep, exists_rep
-/
lemma PartialMap.toRationalMap_surjective : Function.Surjective (@toRationalMap X Y) :=
  Quotient.exists_rep

/--
lemma `RationalMap.exists_rep` / 引理 `RationalMap.exists_rep`

English:
lemma RationalMap.exists_rep
  given: (f : X ⤏ Y)
  statement: exists g : X.PartialMap Y, g.toRationalMap = f
  proof: Quotient.exists_rep f

中文:
引理 RationalMap.存在_rep
  条件: (f : X ⤏ Y)
  结论: 存在 g : X.Partial映射 Y, g.toRationalMap = f
  证明: Quotient.exists_rep f

Depends on / 依赖: Quotient, Quotient.exists_rep, exists_rep
-/
lemma RationalMap.exists_rep (f : X ⤏ Y) : exists g : X.PartialMap Y, g.toRationalMap = f :=
  Quotient.exists_rep f

/--
lemma `PartialMap.toRationalMap_eq_iff` / 引理 `PartialMap.toRationalMap_eq_iff`

English:
lemma PartialMap.toRationalMap_eq_iff
  given: {f g : X.PartialMap Y}
  proof: Quotient.eq

中文:
引理 Partial映射.toRationalMap_eq_iff
  条件: {f g : X.Partial映射 Y}
  证明: Quotient.eq

Depends on / 依赖: Quotient, Quotient.eq
-/
lemma PartialMap.toRationalMap_eq_iff {f g : X.PartialMap Y} :
    f.toRationalMap = g.toRationalMap ↔ f.equiv g :=
  Quotient.eq

/--
Definition of `RationalMap.representative` / `RationalMap.representative` 的定义

English:
definition RationalMap.representative
  signature: (f : X ⤏ Y)
  body: f.exists_rep.choose

@[simp]

中文:
定义 RationalMap.representative
  签名: (f : X ⤏ Y)
  定义体: f.exists_rep.choose

@[simp]

Depends on / 依赖: exists_rep, f.exists_rep.choose
-/
noncomputable def RationalMap.representative (f : X ⤏ Y) : X.PartialMap Y :=
  f.exists_rep.choose

@[simp]
/--
lemma `RationalMap.toRationalMap_representative` / 引理 `RationalMap.toRationalMap_representative`

English:
lemma RationalMap.toRationalMap_representative
  given: (f : X ⤏ Y)
  proof: f.exists_rep.choose_spec

中文:
引理 RationalMap.toRationalMap_representative
  条件: (f : X ⤏ Y)
  证明: f.exists_rep.choose_spec

Depends on / 依赖: choose_spec, exists_rep, f.exists_rep.choose_spec
-/
lemma RationalMap.toRationalMap_representative (f : X ⤏ Y) :
    f.representative.toRationalMap = f :=
  f.exists_rep.choose_spec

/--
lemma `PartialMap.representative_toRationalMap_equiv` / 引理 `PartialMap.representative_toRationalMap_equiv`

English:
lemma PartialMap.representative_toRationalMap_equiv
  given: (f : X.PartialMap Y)
  proof: by
  rw [← PartialMap.toRationalMap_eq_iff]; rw [f.toRationalMap.toRationalMap_representative]

@[simp]

中文:
引理 Partial映射.representative_toRationalMap_equiv
  条件: (f : X.Partial映射 Y)
  证明: by
  rw [← PartialMap.toRationalMap_eq_iff]; rw [f.toRationalMap.toRationalMap_representative]

@[simp]

Depends on / 依赖: PartialMap, PartialMap.toRationalMap_eq_iff, f.toRationalMap.toRationalMap_representative, toRationalMap, toRationalMap_eq_iff, toRationalMap_representative
-/
lemma PartialMap.representative_toRationalMap_equiv (f : X.PartialMap Y) :
    f.toRationalMap.representative.equiv f := by
  rw [← PartialMap.toRationalMap_eq_iff]; rw [f.toRationalMap.toRationalMap_representative]

@[simp]
/--
lemma `PartialMap.restrict_toRationalMap` / 引理 `PartialMap.restrict_toRationalMap`

English:
lemma PartialMap.restrict_toRationalMap
  statement: (f : X.PartialMap Y) (U : X.Opens)
  proof: toRationalMap_eq_iff.mpr (f.restrict_equiv U hU hU')

中文:
引理 Partial映射.restrict_toRationalMap
  结论: (f : X.Partial映射 Y) (U : X.Opens)
  证明: toRationalMap_eq_iff.mpr (f.restrict_equiv U hU hU')

Depends on / 依赖: f.restrict_equiv, restrict_equiv, toRationalMap_eq_iff, toRationalMap_eq_iff.mpr
-/
lemma PartialMap.restrict_toRationalMap (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U <= f.domain) :
    (f.restrict U hU hU').toRationalMap = f.toRationalMap :=
  toRationalMap_eq_iff.mpr (f.restrict_equiv U hU hU')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.Over
  signature: S] [Y.Over S] (f
  body: ⟨f, ‹_›, rfl⟩

中文:
实例 [X.Over
  签名: S] [Y.Over S] (f
  定义体: ⟨f, ‹_›, rfl⟩
-/
instance [X.Over S] [Y.Over S] (f : X.PartialMap Y) [f.IsOver S] : f.toRationalMap.IsOver S :=
  ⟨f, ‹_›, rfl⟩

variable (S) in
/--
lemma `RationalMap.exists_partialMap_over` / 引理 `RationalMap.exists_partialMap_over`

English:
lemma RationalMap.exists_partialMap_over
  given: [X.Over S] [Y.Over S] (f : X ⤏ Y) [f.IsOver S]
  proof: IsOver.exists_partialMap_over

中文:
引理 RationalMap.存在_partialMap_over
  条件: [X.Over S] [Y.Over S] (f : X ⤏ Y) [f.是Over S]
  证明: IsOver.exists_partialMap_over

Depends on / 依赖: IsOver, IsOver.exists_partialMap_over, exists_partialMap_over
-/
lemma RationalMap.exists_partialMap_over [X.Over S] [Y.Over S] (f : X ⤏ Y) [f.IsOver S] :
    exists g : X.PartialMap Y, g.IsOver S ∧ g.toRationalMap = f :=
  IsOver.exists_partialMap_over

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `RationalMap.compHom` / `RationalMap.compHom` 的定义

English:
definition RationalMap.compHom
  signature: (f : X ⤏ Y) (g : Y ⟶ Z)
  body: by
  refine Quotient.map (PartialMap.compHom · g) ?_ f
  intro f₁ f₂ ⟨W, hW, hWl, hWr, e⟩
  refine ⟨W, hW, hWl, hWr, ?_⟩
  simp only [PartialMap.restrict_domain, PartialMap.restrict_hom, PartialMap.compHom_domain,
    PartialMap.compHom_hom] at e ⊢
  rw [reassoc_of% e]

@[simp]

中文:
定义 RationalMap.compHom
  签名: (f : X ⤏ Y) (g : Y ⟶ Z)
  定义体: by
  refine Quotient.map (PartialMap.compHom · g) ?_ f
  intro f₁ f₂ ⟨W, hW, hWl, hWr, e⟩
  refine ⟨W, hW, hWl, hWr, ?_⟩
  simp only [PartialMap.restrict_domain, PartialMap.restrict_hom, PartialMap.compHom_domain,
    PartialMap.compHom_hom] at e ⊢
  rw [reassoc_of% e]

@[simp]

Depends on / 依赖: PartialMap, PartialMap.compHom, PartialMap.compHom_domain, PartialMap.compHom_hom, PartialMap.restrict_domain, PartialMap.restrict_hom, Quotient, Quotient.map, compHom, compHom_domain, compHom_hom, reassoc_of, restrict_domain, restrict_hom
-/
def RationalMap.compHom (f : X ⤏ Y) (g : Y ⟶ Z) : X ⤏ Z := by
  refine Quotient.map (PartialMap.compHom · g) ?_ f
  intro f₁ f₂ ⟨W, hW, hWl, hWr, e⟩
  refine ⟨W, hW, hWl, hWr, ?_⟩
  simp only [PartialMap.restrict_domain, PartialMap.restrict_hom, PartialMap.compHom_domain,
    PartialMap.compHom_hom] at e ⊢
  rw [reassoc_of% e]

@[simp]
/--
lemma `RationalMap.compHom_toRationalMap` / 引理 `RationalMap.compHom_toRationalMap`

English:
lemma RationalMap.compHom_toRationalMap
  given: (f : X.PartialMap Y) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
引理 RationalMap.compHom_toRationalMap
  条件: (f : X.Partial映射 Y) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
lemma RationalMap.compHom_toRationalMap (f : X.PartialMap Y) (g : Y ⟶ Z) :
    (f.compHom g).toRationalMap = f.toRationalMap.compHom g := rfl

@[simp]
/--
lemma `RationalMap.id_compHom` / 引理 `RationalMap.id_compHom`

English:
lemma RationalMap.id_compHom
  given: (f : X ⟶ Y)
  proof: by
  rw [RationalMap.id]; rw [← compHom_toRationalMap]; rw [PartialMap.id_compHom]

中文:
引理 RationalMap.id_compHom
  条件: (f : X ⟶ Y)
  证明: by
  rw [RationalMap.id]; rw [← compHom_toRationalMap]; rw [PartialMap.id_compHom]

Depends on / 依赖: PartialMap, PartialMap.id_compHom, RationalMap, RationalMap.id, compHom_toRationalMap, id_compHom
-/
lemma RationalMap.id_compHom (f : X ⟶ Y) :
    (RationalMap.id X).compHom f = f.toRationalMap := by
  rw [RationalMap.id]; rw [← compHom_toRationalMap]; rw [PartialMap.id_compHom]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.Over
  signature: S] [Y.Over S] [Z.Over S] (f
  body: by
    obtain ⟨f, hf, rfl⟩ := f.exists_partialMap_over S
    exact ⟨f.compHom g, inferInstance, rfl⟩

中文:
实例 [X.Over
  签名: S] [Y.Over S] [Z.Over S] (f
  定义体: by
    obtain ⟨f, hf, rfl⟩ := f.exists_partialMap_over S
    exact ⟨f.compHom g, inferInstance, rfl⟩

Depends on / 依赖: compHom, exists_partialMap_over, f.compHom, f.exists_partialMap_over
-/
instance [X.Over S] [Y.Over S] [Z.Over S] (f : X ⤏ Y) (g : Y ⟶ Z)
    [f.IsOver S] [g.IsOver S] : (f.compHom g).IsOver S where
  exists_partialMap_over := by
    obtain ⟨f, hf, rfl⟩ := f.exists_partialMap_over S
    exact ⟨f.compHom g, inferInstance, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable (S) in
/--
lemma `PartialMap.exists_restrict_isOver` / 引理 `PartialMap.exists_restrict_isOver`

English:
lemma PartialMap.exists_restrict_isOver
  statement: [X.Over S] [Y.Over S] (f : X.PartialMap Y)
  proof: by
  obtain ⟨f', hf₁, hf₂⟩ := RationalMap.IsOver.exists_partialMap_over (S := S) (f := f.toRationalMap)
  obtain ⟨U, hU, hUl, hUr, e⟩ := PartialMap.toRationalMap_eq_iff.mp hf₂
  exact ⟨U, hU, hUr, by rw [IsOver, ← e]; infer_instance⟩

中文:
引理 Partial映射.存在_restrict_isOver
  结论: [X.Over S] [Y.Over S] (f : X.Partial映射 Y)
  证明: by
  obtain ⟨f', hf₁, hf₂⟩ := RationalMap.IsOver.exists_partialMap_over (S := S) (f := f.toRationalMap)
  obtain ⟨U, hU, hUl, hUr, e⟩ := PartialMap.toRationalMap_eq_iff.mp hf₂
  exact ⟨U, hU, hUr, by rw [IsOver, ← e]; infer_instance⟩

Depends on / 依赖: IsOver, PartialMap, PartialMap.toRationalMap_eq_iff.mp, RationalMap, RationalMap.IsOver.exists_partialMap_over, exists_partialMap_over, f.toRationalMap, infer_instance, toRationalMap, toRationalMap_eq_iff
-/
lemma PartialMap.exists_restrict_isOver [X.Over S] [Y.Over S] (f : X.PartialMap Y)
    [f.toRationalMap.IsOver S] : exists U hU hU', (f.restrict U hU hU').IsOver S := by
  obtain ⟨f', hf₁, hf₂⟩ := RationalMap.IsOver.exists_partialMap_over (S := S) (f := f.toRationalMap)
  obtain ⟨U, hU, hUl, hUr, e⟩ := PartialMap.toRationalMap_eq_iff.mp hf₂
  exact ⟨U, hU, hUr, by rw [IsOver, ← e]; infer_instance⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `RationalMap.isOver_iff` / 引理 `RationalMap.isOver_iff`

English:
lemma RationalMap.isOver_iff
  given: [X.Over S] [Y.Over S] {f : X ⤏ Y}
  proof: by
  constructor
  · intro h
    obtain ⟨g, hg, e⟩ := f.exists_partialMap_over S
    rw [← e]; rw [Hom.toRationalMap]; rw [← compHom_toRationalMap]; rw [PartialMap.isOver_iff_eq_restrict.mp hg]; rw [PartialMap.restrict_toRationalMap]
  · intro e
    obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjec

中文:
引理 RationalMap.isOver_iff
  条件: [X.Over S] [Y.Over S] {f : X ⤏ Y}
  证明: by
  constructor
  · intro h
    obtain ⟨g, hg, e⟩ := f.exists_partialMap_over S
    rw [← e]; rw [Hom.toRationalMap]; rw [← compHom_toRationalMap]; rw [PartialMap.isOver_iff_eq_restrict.mp hg]; rw [PartialMap.restrict_toRationalMap]
  · intro e
    obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjec

Depends on / 依赖: Hom.toRationalMap, PartialMap, PartialMap.isOver_iff_eq_restrict.mp, PartialMap.restrict_toRationalMap, PartialMap.toRationalMap_eq_iff.mp, PartialMap.toRationalMap_surjective, compHom_toRationalMap, exists_partialMap_over, f.exists_partialMap_over, f.restrict, isOver_iff_eq_restrict, restrict, restrict_toRationalMap, toRationalMap, toRationalMap_eq_iff, toRationalMap_surjective
-/
lemma RationalMap.isOver_iff [X.Over S] [Y.Over S] {f : X ⤏ Y} :
    f.IsOver S ↔ f.compHom (Y ↘ S) = (X ↘ S).toRationalMap := by
  constructor
  · intro h
    obtain ⟨g, hg, e⟩ := f.exists_partialMap_over S
    rw [← e]; rw [Hom.toRationalMap]; rw [← compHom_toRationalMap]; rw [PartialMap.isOver_iff_eq_restrict.mp hg]; rw [PartialMap.restrict_toRationalMap]
  · intro e
    obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjective f
    obtain ⟨U, hU, hUl, hUr, e⟩ := PartialMap.toRationalMap_eq_iff.mp e
    exact ⟨⟨f.restrict U hU hUl, by simpa using! e, by simp⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `PartialMap.isOver_toRationalMap_iff_of_isSeparated` / 引理 `PartialMap.isOver_toRationalMap_iff_of_isSeparated`

English:
lemma PartialMap.isOver_toRationalMap_iff_of_isSeparated
  statement: [X.Over S] [Y.Over S] [IsReduced X]
  proof: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  obtain ⟨U, hU, hU', H⟩ := f.exists_restrict_isOver (S := S)
  rw [isOver_iff]
  have : IsDominant (X.homOfLE hU') := Opens.isDominant_homOfLE hU _
  exact ext_of_isDominant (ι := X.homOfLE hU') (by simpa using H.1)

中文:
引理 Partial映射.isOver_toRationalMap_iff_of_isSeparated
  结论: [X.Over S] [Y.Over S] [是既约 X]
  证明: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  obtain ⟨U, hU, hU', H⟩ := f.exists_restrict_isOver (S := S)
  rw [isOver_iff]
  have : IsDominant (X.homOfLE hU') := Opens.isDominant_homOfLE hU _
  exact ext_of_isDominant (ι := X.homOfLE hU') (by simpa using H.1)

Depends on / 依赖: IsDominant, Opens.isDominant_homOfLE, X.homOfLE, exists_restrict_isOver, ext_of_isDominant, f.exists_restrict_isOver, homOfLE, isDominant_homOfLE, isOver_iff
-/
lemma PartialMap.isOver_toRationalMap_iff_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X]
    [S.IsSeparated] {f : X.PartialMap Y} :
    f.toRationalMap.IsOver S ↔ f.IsOver S := by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  obtain ⟨U, hU, hU', H⟩ := f.exists_restrict_isOver (S := S)
  rw [isOver_iff]
  have : IsDominant (X.homOfLE hU') := Opens.isDominant_homOfLE hU _
  exact ext_of_isDominant (ι := X.homOfLE hU') (by simpa using H.1)

section functionField

set_option backward.defeqAttrib.useBackward true in
/-- A rational map restricts to a map from `Spec K(X)`. -/
noncomputable
/--
Definition of `RationalMap.fromFunctionField` / `RationalMap.fromFunctionField` 的定义

English:
definition RationalMap.fromFunctionField
  signature: [IrreducibleSpace X] (f : X ⤏ Y)
  body: by
  refine Quotient.lift PartialMap.fromFunctionField ?_ f
  intro f g ⟨W, hW, hWl, hWr, e⟩
  have : f.restrict W hW hWl = g.restrict W hW hWr := by
    ext1
    · rfl
    rw [e]; simp
  rw [← f.fromFunctionField_restrict hW hWl]; rw [this]; rw [g.fromFunctionField_restrict]

@[simp]

中文:
定义 RationalMap.fromFunctionField
  签名: [不可约空间 X] (f : X ⤏ Y)
  定义体: by
  refine Quotient.lift PartialMap.fromFunctionField ?_ f
  intro f g ⟨W, hW, hWl, hWr, e⟩
  have : f.restrict W hW hWl = g.restrict W hW hWr := by
    ext1
    · rfl
    rw [e]; simp
  rw [← f.fromFunctionField_restrict hW hWl]; rw [this]; rw [g.fromFunctionField_restrict]

@[simp]

Depends on / 依赖: PartialMap, PartialMap.fromFunctionField, Quotient, Quotient.lift, f.fromFunctionField_restrict, f.restrict, fromFunctionField, fromFunctionField_restrict, g.fromFunctionField_restrict, g.restrict, restrict
-/
def RationalMap.fromFunctionField [IrreducibleSpace X] (f : X ⤏ Y) :
    Spec X.functionField ⟶ Y := by
  refine Quotient.lift PartialMap.fromFunctionField ?_ f
  intro f g ⟨W, hW, hWl, hWr, e⟩
  have : f.restrict W hW hWl = g.restrict W hW hWr := by
    ext1
    · rfl
    rw [e]; simp
  rw [← f.fromFunctionField_restrict hW hWl]; rw [this]; rw [g.fromFunctionField_restrict]

@[simp]
/--
lemma `RationalMap.fromFunctionField_toRationalMap` / 引理 `RationalMap.fromFunctionField_toRationalMap`

English:
lemma RationalMap.fromFunctionField_toRationalMap
  given: [IrreducibleSpace X] (f : X.PartialMap Y)
  proof: rfl

中文:
引理 RationalMap.fromFunctionField_toRationalMap
  条件: [不可约空间 X] (f : X.Partial映射 Y)
  证明: rfl
-/
lemma RationalMap.fromFunctionField_toRationalMap [IrreducibleSpace X] (f : X.PartialMap Y) :
    f.toRationalMap.fromFunctionField = f.fromFunctionField := rfl

/--
Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and `X` is integral,
any `S`-morphism `Spec K(X) ⟶ Y` spreads out to a rational map from `X` to `Y`.
-/
noncomputable
/--
Definition of `RationalMap.ofFunctionField` / `RationalMap.ofFunctionField` 的定义

English:
definition RationalMap.ofFunctionField
  signature: [IsIntegral X] [LocallyOfFiniteType sY]
  body: (PartialMap.ofFromSpecStalk sX sY f h).toRationalMap

中文:
定义 RationalMap.ofFunctionField
  签名: [是整 X] [局部有限型 sY]
  定义体: (PartialMap.ofFromSpecStalk sX sY f h).toRationalMap

Depends on / 依赖: PartialMap, PartialMap.ofFromSpecStalk, ofFromSpecStalk, toRationalMap
-/
def RationalMap.ofFunctionField [IsIntegral X] [LocallyOfFiniteType sY]
    (f : Spec X.functionField ⟶ Y) (h : f ≫ sY = X.fromSpecStalk _ ≫ sX) : X ⤏ Y :=
  (PartialMap.ofFromSpecStalk sX sY f h).toRationalMap

/--
lemma `RationalMap.fromFunctionField_ofFunctionField` / 引理 `RationalMap.fromFunctionField_ofFunctionField`

English:
lemma RationalMap.fromFunctionField_ofFunctionField
  statement: [IsIntegral X] [LocallyOfFiniteType sY]
  proof: PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY _ _

中文:
引理 RationalMap.fromFunctionField_ofFunctionField
  结论: [是整 X] [局部有限型 sY]
  证明: PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY _ _

Depends on / 依赖: PartialMap, PartialMap.fromSpecStalkOfMem_ofFromSpecStalk, fromSpecStalkOfMem_ofFromSpecStalk
-/
lemma RationalMap.fromFunctionField_ofFunctionField [IsIntegral X] [LocallyOfFiniteType sY]
    (f : Spec X.functionField ⟶ Y) (h : f ≫ sY = X.fromSpecStalk _ ≫ sX) :
    (ofFunctionField sX sY f h).fromFunctionField = f :=
  PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY _ _

/--
lemma `RationalMap.eq_of_fromFunctionField_eq` / 引理 `RationalMap.eq_of_fromFunctionField_eq`

English:
lemma RationalMap.eq_of_fromFunctionField_eq
  statement: [IsIntegral X] (f g : X.RationalMap Y)
  proof: by
  obtain ⟨f, rfl⟩ := f.exists_rep
  obtain ⟨g, rfl⟩ := g.exists_rep
  refine PartialMap.toRationalMap_eq_iff.mpr ?_
  exact PartialMap.equiv_of_fromSpecStalkOfMem_eq _ _ _ _ H

中文:
引理 RationalMap.eq_of_fromFunctionField_eq
  结论: [是整 X] (f g : X.RationalMap Y)
  证明: by
  obtain ⟨f, rfl⟩ := f.exists_rep
  obtain ⟨g, rfl⟩ := g.exists_rep
  refine PartialMap.toRationalMap_eq_iff.mpr ?_
  exact PartialMap.equiv_of_fromSpecStalkOfMem_eq _ _ _ _ H

Depends on / 依赖: PartialMap, PartialMap.equiv_of_fromSpecStalkOfMem_eq, PartialMap.toRationalMap_eq_iff.mpr, equiv_of_fromSpecStalkOfMem_eq, exists_rep, f.exists_rep, g.exists_rep, toRationalMap_eq_iff
-/
lemma RationalMap.eq_of_fromFunctionField_eq [IsIntegral X] (f g : X.RationalMap Y)
    (H : f.fromFunctionField = g.fromFunctionField) : f = g := by
  obtain ⟨f, rfl⟩ := f.exists_rep
  obtain ⟨g, rfl⟩ := g.exists_rep
  refine PartialMap.toRationalMap_eq_iff.mpr ?_
  exact PartialMap.equiv_of_fromSpecStalkOfMem_eq _ _ _ _ H

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and `X` is integral,
`S`-morphisms `Spec K(X) ⟶ Y` correspond bijectively to `S`-rational maps from `X` to `Y`.
-/
noncomputable
/--
Definition of `RationalMap.equivFunctionField` / `RationalMap.equivFunctionField` 的定义

English:
definition RationalMap.equivFunctionField
  signature: [IsIntegral X] [LocallyOfFiniteType sY]
  body: ⟨.ofFunctionField sX sY f f.2, PartialMap.toRationalMap_eq_iff.mpr
      ⟨_, PartialMap.dense_domain _, le_rfl, le_top, by simp [PartialMap.ofFromSpecStalk_comp]⟩⟩
  invFun f := ⟨f.1.fromFunctionField, by
    obtain ⟨f, hf⟩ := f
    obtain ⟨f, rfl⟩ := f.exists_rep
    simpa [fromFunctionField_toRati

中文:
定义 RationalMap.equivFunctionField
  签名: [是整 X] [局部有限型 sY]
  定义体: ⟨.ofFunctionField sX sY f f.2, PartialMap.toRationalMap_eq_iff.mpr
      ⟨_, PartialMap.dense_domain _, le_rfl, le_top, by simp [PartialMap.ofFromSpecStalk_comp]⟩⟩
  invFun f := ⟨f.1.fromFunctionField, by
    obtain ⟨f, hf⟩ := f
    obtain ⟨f, rfl⟩ := f.exists_rep
    simpa [fromFunctionField_toRati

Depends on / 依赖: PartialMap, PartialMap.toRationalMap_eq_iff.mpr, ofFunctionField, toRationalMap_eq_iff
-/
def RationalMap.equivFunctionField [IsIntegral X] [LocallyOfFiniteType sY] :
    { f : Spec X.functionField ⟶ Y // f ≫ sY = X.fromSpecStalk _ ≫ sX } ≃
      { f : X ⤏ Y // f.compHom sY = sX.toRationalMap } where
  toFun f := ⟨.ofFunctionField sX sY f f.2, PartialMap.toRationalMap_eq_iff.mpr
      ⟨_, PartialMap.dense_domain _, le_rfl, le_top, by simp [PartialMap.ofFromSpecStalk_comp]⟩⟩
  invFun f := ⟨f.1.fromFunctionField, by
    obtain ⟨f, hf⟩ := f
    obtain ⟨f, rfl⟩ := f.exists_rep
    simpa [fromFunctionField_toRationalMap] using! congr(RationalMap.fromFunctionField $hf)⟩
  left_inv f := Subtype.ext (RationalMap.fromFunctionField_ofFunctionField _ _ _ _)
  right_inv f := Subtype.ext (RationalMap.eq_of_fromFunctionField_eq
      (ofFunctionField sX sY f.1.fromFunctionField _) f
      (RationalMap.fromFunctionField_ofFunctionField _ _ _ _))

/--
Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and `X` is integral,
`S`-morphisms `Spec K(X) ⟶ Y` correspond bijectively to `S`-rational maps from `X` to `Y`.
-/
noncomputable
/--
Definition of `RationalMap.equivFunctionFieldOver` / `RationalMap.equivFunctionFieldOver` 的定义

English:
definition RationalMap.equivFunctionFieldOver
  signature: [X.Over S] [Y.Over S] [IsIntegral X]
  body: ((Equiv.subtypeEquivProp (by simp only [Hom.isOver_iff]; rfl)).trans
    (RationalMap.equivFunctionField (X ↘ S) (Y ↘ S))).trans
      (Equiv.subtypeEquivProp (by ext f; rw [RationalMap.isOver_iff]))

中文:
定义 RationalMap.equivFunctionFieldOver
  签名: [X.Over S] [Y.Over S] [是整 X]
  定义体: ((Equiv.subtypeEquivProp (by simp only [Hom.isOver_iff]; rfl)).trans
    (RationalMap.equivFunctionField (X ↘ S) (Y ↘ S))).trans
      (Equiv.subtypeEquivProp (by ext f; rw [RationalMap.isOver_iff]))

Depends on / 依赖: Equiv.subtypeEquivProp, Hom.isOver_iff, RationalMap, RationalMap.equivFunctionField, RationalMap.isOver_iff, equivFunctionField, isOver_iff, subtypeEquivProp
-/
def RationalMap.equivFunctionFieldOver [X.Over S] [Y.Over S] [IsIntegral X]
    [LocallyOfFiniteType (Y ↘ S)] :
    { f : Spec X.functionField ⟶ Y // f.IsOver S } ≃ { f : X ⤏ Y // f.IsOver S } :=
  ((Equiv.subtypeEquivProp (by simp only [Hom.isOver_iff]; rfl)).trans
    (RationalMap.equivFunctionField (X ↘ S) (Y ↘ S))).trans
      (Equiv.subtypeEquivProp (by ext f; rw [RationalMap.isOver_iff]))

end functionField

section domain

/--
Definition of `RationalMap.domain` / `RationalMap.domain` 的定义

English:
definition RationalMap.domain
  signature: (f : X ⤏ Y)
  body: sSup { PartialMap.domain g | (g) (_ : g.toRationalMap = f) }

中文:
定义 RationalMap.domain
  签名: (f : X ⤏ Y)
  定义体: sSup { PartialMap.domain g | (g) (_ : g.toRationalMap = f) }

Depends on / 依赖: PartialMap, PartialMap.domain, domain, g.toRationalMap, toRationalMap
-/
def RationalMap.domain (f : X ⤏ Y) : X.Opens :=
  sSup { PartialMap.domain g | (g) (_ : g.toRationalMap = f) }

/--
lemma `PartialMap.le_domain_toRationalMap` / 引理 `PartialMap.le_domain_toRationalMap`

English:
lemma PartialMap.le_domain_toRationalMap
  given: (f : X.PartialMap Y)
  proof: le_sSup ⟨f, rfl, rfl⟩

中文:
引理 Partial映射.le_domain_toRationalMap
  条件: (f : X.Partial映射 Y)
  证明: le_sSup ⟨f, rfl, rfl⟩

Depends on / 依赖: le_sSup
-/
lemma PartialMap.le_domain_toRationalMap (f : X.PartialMap Y) :
    f.domain <= f.toRationalMap.domain :=
  le_sSup ⟨f, rfl, rfl⟩

/--
lemma `RationalMap.mem_domain` / 引理 `RationalMap.mem_domain`

English:
lemma RationalMap.mem_domain
  given: {f : X ⤏ Y} {x}
  proof: TopologicalSpace.Opens.mem_sSup.trans (by simp [@and_comm (x in _)])

中文:
引理 RationalMap.mem_domain
  条件: {f : X ⤏ Y} {x}
  证明: TopologicalSpace.Opens.mem_sSup.trans (by simp [@and_comm (x in _)])

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens.mem_sSup.trans, and_comm, mem_sSup
-/
lemma RationalMap.mem_domain {f : X ⤏ Y} {x} :
    x in f.domain ↔ exists g : X.PartialMap Y, x in g.domain ∧ g.toRationalMap = f :=
  TopologicalSpace.Opens.mem_sSup.trans (by simp [@and_comm (x in _)])

/--
lemma `RationalMap.dense_domain` / 引理 `RationalMap.dense_domain`

English:
lemma RationalMap.dense_domain
  given: (f : X ⤏ Y)
  statement: Dense (X := X) f.domain
  proof: f.inductionOn (fun g => g.dense_domain.mono g.le_domain_toRationalMap)

中文:
引理 RationalMap.dense_domain
  条件: (f : X ⤏ Y)
  结论: 稠密 (X := X) f.domain
  证明: f.inductionOn (fun g => g.dense_domain.mono g.le_domain_toRationalMap)

Depends on / 依赖: domain, f.domain
-/
lemma RationalMap.dense_domain (f : X ⤏ Y) : Dense (X := X) f.domain :=
  f.inductionOn (fun g => g.dense_domain.mono g.le_domain_toRationalMap)

set_option backward.isDefEq.respectTransparency false in
/-- The open cover of the domain of `f : X ⤏ Y`,
consisting of all the domains of the partial maps in the equivalence class. -/
noncomputable
/--
Definition of `RationalMap.openCoverDomain` / `RationalMap.openCoverDomain` 的定义

English:
definition RationalMap.openCoverDomain
  signature: (f : X ⤏ Y)
  body: { PartialMap.domain g | (g) (_ : g.toRationalMap = f) }
  X U := U.1.toScheme
  f U := X.homOfLE (le_sSup U.2)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    use ⟨_, (TopologicalSpace.Opens.mem_sSup.mp x.2).choose_spec.1⟩
    exact ⟨⟨x.1, (Topological

中文:
定义 RationalMap.openCoverDomain
  签名: (f : X ⤏ Y)
  定义体: { PartialMap.domain g | (g) (_ : g.toRationalMap = f) }
  X U := U.1.toScheme
  f U := X.homOfLE (le_sSup U.2)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    use ⟨_, (TopologicalSpace.Opens.mem_sSup.mp x.2).choose_spec.1⟩
    exact ⟨⟨x.1, (Topological

Depends on / 依赖: PartialMap, PartialMap.domain, domain, g.toRationalMap, toRationalMap
-/
def RationalMap.openCoverDomain (f : X ⤏ Y) : f.domain.toScheme.OpenCover where
  I₀ := { PartialMap.domain g | (g) (_ : g.toRationalMap = f) }
  X U := U.1.toScheme
  f U := X.homOfLE (le_sSup U.2)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    use ⟨_, (TopologicalSpace.Opens.mem_sSup.mp x.2).choose_spec.1⟩
    exact ⟨⟨x.1, (TopologicalSpace.Opens.mem_sSup.mp x.2).choose_spec.2⟩, Subtype.ext (by simp)⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `f : X ⤏ Y` is a rational map from a reduced scheme to a separated scheme,
then `f` can be represented as a partial map on its domain of definition. -/
noncomputable
/--
Definition of `RationalMap.toPartialMap` / `RationalMap.toPartialMap` 的定义

English:
definition RationalMap.toPartialMap
  signature: [IsReduced X] [Y.IsSeparated] (f : X ⤏ Y)
  body: by
  refine ⟨f.domain, f.dense_domain, f.openCoverDomain.glueMorphisms
    (fun x => (X.isoOfEq x.2.choose_spec.2).inv ≫ x.2.choose.hom) ?_⟩
  intro x y
  let g (x : f.openCoverDomain.I₀) := x.2.choose
  have hg₁ (x) : (g x).toRationalMap = f := x.2.choose_spec.1
  have hg₂ (x) : (g x).domain = x.1 

中文:
定义 RationalMap.toPartialMap
  签名: [是既约 X] [Y.是分离] (f : X ⤏ Y)
  定义体: by
  refine ⟨f.domain, f.dense_domain, f.openCoverDomain.glueMorphisms
    (fun x => (X.isoOfEq x.2.choose_spec.2).inv ≫ x.2.choose.hom) ?_⟩
  intro x y
  let g (x : f.openCoverDomain.I₀) := x.2.choose
  have hg₁ (x) : (g x).toRationalMap = f := x.2.choose_spec.1
  have hg₂ (x) : (g x).domain = x.1 

Depends on / 依赖: IsPullback, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_, X.isoOfEq, cancel_epi, choose.hom, choose_spec, dense_domain, domain, f.dense_domain, f.domain, f.openCoverDomain.I, f.openCoverDomain.glueMorphisms, glueMorphisms, isPullback_opens_inf_le, isoOfEq, isoPullback, isoPullback.hom, isoPullback_hom_fst_assoc, isoPullback_hom_snd_
-/
def RationalMap.toPartialMap [IsReduced X] [Y.IsSeparated] (f : X ⤏ Y) : X.PartialMap Y := by
  refine ⟨f.domain, f.dense_domain, f.openCoverDomain.glueMorphisms
    (fun x => (X.isoOfEq x.2.choose_spec.2).inv ≫ x.2.choose.hom) ?_⟩
  intro x y
  let g (x : f.openCoverDomain.I₀) := x.2.choose
  have hg₁ (x) : (g x).toRationalMap = f := x.2.choose_spec.1
  have hg₂ (x) : (g x).domain = x.1 := x.2.choose_spec.2
  refine (cancel_epi (isPullback_opens_inf_le (le_sSup x.2) (le_sSup y.2)).isoPullback.hom).mp ?_
  simp only [openCoverDomain, IsPullback.isoPullback_hom_fst_assoc,
    IsPullback.isoPullback_hom_snd_assoc]
  change _ ≫ _ ≫ (g x).hom = _ ≫ _ ≫ (g y).hom
  simp_rw [← cancel_epi (X.isoOfEq congr($(hg₂ x) ⊓ $(hg₂ y))).hom, ← Category.assoc]
  convert! (PartialMap.equiv_iff_of_isSeparated (S := ⊤_ _) (f := g x) (g := g y)).mp ?_ using 1
  · dsimp; congr 1; simp [g, ← cancel_mono (Opens.ι _)]
  · dsimp; congr 1; simp [g, ← cancel_mono (Opens.ι _)]
  · rw [← PartialMap.toRationalMap_eq_iff, hg₁, hg₁]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `PartialMap.toPartialMap_toRationalMap_restrict` / 引理 `PartialMap.toPartialMap_toRationalMap_restrict`

English:
lemma PartialMap.toPartialMap_toRationalMap_restrict
  statement: [IsReduced X] [Y.IsSeparated]
  proof: by
  dsimp [RationalMap.toPartialMap]
  refine (f.toRationalMap.openCoverDomain.ι_glueMorphisms _ _ ⟨_, f, rfl, rfl⟩).trans ?_
  generalize_proofs _ _ H _
  have : H.choose = f := (equiv_iff_of_domain_eq_of_isSeparated (S := ⊤_ _) H.choose_spec.2).mp
    (toRationalMap_eq_iff.mp H.choose_spec.1)
  e

中文:
引理 Partial映射.toPartialMap_toRationalMap_restrict
  结论: [是既约 X] [Y.是分离]
  证明: by
  dsimp [RationalMap.toPartialMap]
  refine (f.toRationalMap.openCoverDomain.ι_glueMorphisms _ _ ⟨_, f, rfl, rfl⟩).trans ?_
  generalize_proofs _ _ H _
  have : H.choose = f := (equiv_iff_of_domain_eq_of_isSeparated (S := ⊤_ _) H.choose_spec.2).mp
    (toRationalMap_eq_iff.mp H.choose_spec.1)
  e

Depends on / 依赖: H.choose, H.choose_spec, RationalMap, RationalMap.toPartialMap, choose_spec, choose_spec.symm, equiv_iff_of_domain_eq_of_isSeparated, ext_iff, f.toRationalMap.openCoverDomain, generalize_proofs, openCoverDomain, this.symm, toPartialMap, toRationalMap, toRationalMap_eq_iff, toRationalMap_eq_iff.mp
-/
lemma PartialMap.toPartialMap_toRationalMap_restrict [IsReduced X] [Y.IsSeparated]
    (f : X.PartialMap Y) : (f.toRationalMap.toPartialMap.restrict _ f.dense_domain
      f.le_domain_toRationalMap).hom = f.hom := by
  dsimp [RationalMap.toPartialMap]
  refine (f.toRationalMap.openCoverDomain.ι_glueMorphisms _ _ ⟨_, f, rfl, rfl⟩).trans ?_
  generalize_proofs _ _ H _
  have : H.choose = f := (equiv_iff_of_domain_eq_of_isSeparated (S := ⊤_ _) H.choose_spec.2).mp
    (toRationalMap_eq_iff.mp H.choose_spec.1)
  exact ((ext_iff _ _).mp this.symm).choose_spec.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `RationalMap.toRationalMap_toPartialMap` / 引理 `RationalMap.toRationalMap_toPartialMap`

English:
lemma RationalMap.toRationalMap_toPartialMap
  statement: [IsReduced X] [Y.IsSeparated]
  proof: by
  obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjective f
  trans (f.toRationalMap.toPartialMap.restrict _
    f.dense_domain f.le_domain_toRationalMap).toRationalMap
  · simp
  · congr 1
    exact PartialMap.ext _ f rfl (by simpa using f.toPartialMap_toRationalMap_restrict)

中文:
引理 RationalMap.toRationalMap_toPartialMap
  结论: [是既约 X] [Y.是分离]
  证明: by
  obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjective f
  trans (f.toRationalMap.toPartialMap.restrict _
    f.dense_domain f.le_domain_toRationalMap).toRationalMap
  · simp
  · congr 1
    exact PartialMap.ext _ f rfl (by simpa using f.toPartialMap_toRationalMap_restrict)

Depends on / 依赖: PartialMap, PartialMap.ext, PartialMap.toRationalMap_surjective, dense_domain, f.dense_domain, f.le_domain_toRationalMap, f.toPartialMap_toRationalMap_restrict, f.toRationalMap.toPartialMap.restrict, le_domain_toRationalMap, restrict, toPartialMap, toPartialMap_toRationalMap_restrict, toRationalMap, toRationalMap_surjective
-/
lemma RationalMap.toRationalMap_toPartialMap [IsReduced X] [Y.IsSeparated]
    (f : X ⤏ Y) : f.toPartialMap.toRationalMap = f := by
  obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjective f
  trans (f.toRationalMap.toPartialMap.restrict _
    f.dense_domain f.le_domain_toRationalMap).toRationalMap
  · simp
  · congr 1
    exact PartialMap.ext _ f rfl (by simpa using f.toPartialMap_toRationalMap_restrict)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsReduced
  signature: X] [Y.IsSeparated] [S.IsSeparated] [X.Over S] [Y.Over S]
  body: by
  rw [← PartialMap.isOver_toRationalMap_iff_of_isSeparated]; rw [f.toRationalMap_toPartialMap]
  infer_instance

中文:
实例 [是既约
  签名: X] [Y.是分离] [S.是分离] [X.Over S] [Y.Over S]
  定义体: by
  rw [← PartialMap.isOver_toRationalMap_iff_of_isSeparated]; rw [f.toRationalMap_toPartialMap]
  infer_instance

Depends on / 依赖: PartialMap, PartialMap.isOver_toRationalMap_iff_of_isSeparated, f.toRationalMap_toPartialMap, infer_instance, isOver_toRationalMap_iff_of_isSeparated, toRationalMap_toPartialMap
-/
instance [IsReduced X] [Y.IsSeparated] [S.IsSeparated] [X.Over S] [Y.Over S]
    (f : X ⤏ Y) [f.IsOver S] : f.toPartialMap.IsOver S := by
  rw [← PartialMap.isOver_toRationalMap_iff_of_isSeparated]; rw [f.toRationalMap_toPartialMap]
  infer_instance

end domain

end Scheme

end AlgebraicGeometry
