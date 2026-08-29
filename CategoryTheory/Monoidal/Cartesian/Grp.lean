/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
public import Mathlib.CategoryTheory.Monoidal.Grp

/-!
# Yoneda embedding of `Grp C`

We show that group objects are exactly those whose yoneda presheaf is a presheaf of groups,
by constructing the yoneda embedding `Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{v}` and
showing that it is fully faithful and its (essential) image is the representable functors.
-/

@[expose] public section

assert_not_exists Field

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory
universe w v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {M G H X Y : C} [MonObj M] [GrpObj G] [GrpObj H]

variable (X) in
/-- If `X` represents a presheaf of monoids, then `X` is a monoid object. -/
@[to_additive (attr := instance_reducible)
/-- If `X` represents a presheaf of additive monoids, then `X` is an additive monoid object. -/]
/--
Definition of `GrpObj.ofRepresentableBy` / `GrpObj.ofRepresentableBy` 的定义

English:
definition GrpObj.ofRepresentableBy
  signature: (F : Cᵒᵖ ⥤ GrpCat.{w}) (α : (F ⋙ forget _).RepresentableBy X)
  body: MonObj.ofRepresentableBy X (F ⋙ forget₂ GrpCat MonCat) α
  inv := α.homEquiv'.symm (α.homEquiv (𝟙 _))⁻¹
  left_inv := by
    change lift (α.homEquiv'.symm (α.homEquiv (𝟙 X))⁻¹) (𝟙 X) ≫
      α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X)) =
        toUnit X ≫ α.homEquiv'.symm 1
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul, map_one]
    simp only [← α.homEquiv'_comp, lift_fst, Equiv.apply_symm_apply, lift_snd]
    exact inv_mul_cancel (α.homEquiv (𝟙 X))
  right_inv := by
    change lift (𝟙 X) (α.homEquiv'.symm (α.homEquiv' (𝟙 X))⁻¹) ≫
      α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X)) =
        toUnit X ≫ α.homEquiv'.symm 1
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul, map_one]
    simp only [← α.homEquiv'_comp]
    simp

中文:
定义 GrpObj.ofRepresentableBy
  签名: (F : Cᵒᵖ ⥤ 群范畴.{w}) (α : (F ⋙ forget _).可表示 X)
  定义体: MonObj.ofRepresentableBy X (F ⋙ forget₂ GrpCat MonCat) α
  inv := α.homEquiv'.symm (α.homEquiv (𝟙 _))⁻¹
  left_inv := by
    change lift (α.homEquiv'.symm (α.homEquiv (𝟙 X))⁻¹) (𝟙 X) ≫
      α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X)) =
        toUnit X ≫ α.homEquiv'.symm 1
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul, map_one]
    simp only [← α.homEquiv'_comp, lift_fst, Equiv.apply_symm_apply, lift_snd]
    exact inv_mul_cancel (α.homEquiv (𝟙 X))
  right_inv := by
    change lift (𝟙 X) (α.homEquiv'.symm (α.homEquiv' (𝟙 X))⁻¹) ≫
      α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X)) =
        toUnit X ≫ α.homEquiv'.symm 1
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul, map_one]
    simp only [← α.homEquiv'_comp]
    simp

Depends on / 依赖: GrpCat, MonCat, MonObj, MonObj.ofRepresentableBy, ofRepresentableBy
-/
def GrpObj.ofRepresentableBy (F : Cᵒᵖ ⥤ GrpCat.{w}) (α : (F ⋙ forget _).RepresentableBy X) :
    GrpObj X where
  __ := MonObj.ofRepresentableBy X (F ⋙ forget₂ GrpCat MonCat) α
  inv := α.homEquiv'.symm (α.homEquiv (𝟙 _))⁻¹
  left_inv := by
    change lift (α.homEquiv'.symm (α.homEquiv (𝟙 X))⁻¹) (𝟙 X) ≫
      α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X)) =
        toUnit X ≫ α.homEquiv'.symm 1
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul, map_one]
    simp only [← α.homEquiv'_comp, lift_fst, Equiv.apply_symm_apply, lift_snd]
    exact inv_mul_cancel (α.homEquiv (𝟙 X))
  right_inv := by
    change lift (𝟙 X) (α.homEquiv'.symm (α.homEquiv' (𝟙 X))⁻¹) ≫
      α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X)) =
        toUnit X ≫ α.homEquiv'.symm 1
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul, map_one]
    simp only [← α.homEquiv'_comp]
    simp

/-- If `G` is a group object, then `Hom(X, G)` has a group structure. -/
@[to_additive
/-- If `G` is an additive group object, then `Hom(X, G)` has an additive group structure. -/]
/--
Definition of `Hom.group` / `Hom.group` 的定义

English:
abbreviation Hom.group
  signature: : Group (X ⟶ G) where
  body: f ≫ ι
  inv_mul_cancel f := calc
    lift (f ≫ ι) f ≫ μ
    _ = (f ≫ lift ι (𝟙 G)) ≫ μ := by simp
    _ = toUnit X ≫ η := by rw [Category.assoc]; simp

scoped[CategoryTheory.MonObj] attribute [instance] Hom.group
scoped[CategoryTheory.AddMonObj] attribute [instance] Hom.addGroup

@[to_additive]

中文:
缩写 态射.group
  签名: : 群 (X ⟶ G) where
  定义体: f ≫ ι
  inv_mul_cancel f := calc
    lift (f ≫ ι) f ≫ μ
    _ = (f ≫ lift ι (𝟙 G)) ≫ μ := by simp
    _ = toUnit X ≫ η := by rw [Category.assoc]; simp

scoped[CategoryTheory.MonObj] attribute [instance] Hom.group
scoped[CategoryTheory.AddMonObj] attribute [instance] Hom.addGroup

@[to_additive]
-/
abbrev Hom.group : Group (X ⟶ G) where
  inv f := f ≫ ι
  inv_mul_cancel f := calc
    lift (f ≫ ι) f ≫ μ
    _ = (f ≫ lift ι (𝟙 G)) ≫ μ := by simp
    _ = toUnit X ≫ η := by rw [Category.assoc]; simp

scoped[CategoryTheory.MonObj] attribute [instance] Hom.group
scoped[CategoryTheory.AddMonObj] attribute [instance] Hom.addGroup

@[to_additive]
/--
lemma `Hom.inv_def` / 引理 `Hom.inv_def`

English:
lemma Hom.inv_def
  given: (f : X ⟶ G)
  statement: f⁻¹ = f ≫ ι
  proof: rfl

中文:
引理 态射.inv_def
  条件: (f : X ⟶ G)
  结论: f⁻¹ = f ≫ ι
  证明: rfl
-/
lemma Hom.inv_def (f : X ⟶ G) : f⁻¹ = f ≫ ι := rfl

variable (G) in
/-- If `G` is a group object, then `Hom(-, G)` is a presheaf of groups. -/
@[to_additive (attr := simps)
/-- If `G` is an additive group object, then `Hom(-, G)` is a presheaf of additive groups. -/]
/--
Definition of `yonedaGrpObj` / `yonedaGrpObj` 的定义

English:
definition yonedaGrpObj
  signature: : Cᵒᵖ ⥤ GrpCat.{v} where
  body: GrpCat.of (unop X ⟶ G)
  map φ := GrpCat.ofHom ((yonedaMonObj G).map φ).hom

中文:
定义 yonedaGrpObj
  签名: : Cᵒᵖ ⥤ 群范畴.{v} where
  定义体: GrpCat.of (unop X ⟶ G)
  map φ := GrpCat.ofHom ((yonedaMonObj G).map φ).hom

Depends on / 依赖: GrpCat, GrpCat.of
-/
def yonedaGrpObj : Cᵒᵖ ⥤ GrpCat.{v} where
  obj X := GrpCat.of (unop X ⟶ G)
  map φ := GrpCat.ofHom ((yonedaMonObj G).map φ).hom

variable (G) in
/-- If `G` is a monoid object, then `Hom(-, G)` as a presheaf of monoids is represented by `G`. -/
@[to_additive
/-- If `G` is an additive monoid object, then `Hom(-, G)` as a presheaf of additive monoids
is represented by `G`. -/]
/--
Definition of `yonedaGrpObjRepresentableBy` / `yonedaGrpObjRepresentableBy` 的定义

English:
definition yonedaGrpObjRepresentableBy
  signature: : (yonedaGrpObj G ⋙ forget _).RepresentableBy G
  body: Functor.representableByEquiv.symm (.refl _)

中文:
定义 yonedaGrpObjRepresentableBy
  签名: : (yonedaGrpObj G ⋙ forget _).可表示 G
  定义体: Functor.representableByEquiv.symm (.refl _)

Depends on / 依赖: Functor, Functor.representableByEquiv.symm, representableByEquiv
-/
def yonedaGrpObjRepresentableBy : (yonedaGrpObj G ⋙ forget _).RepresentableBy G :=
  Functor.representableByEquiv.symm (.refl _)

variable (G) in
@[to_additive]
/--
lemma `GrpObj.ofRepresentableBy_yonedaGrpObjRepresentableBy` / 引理 `GrpObj.ofRepresentableBy_yonedaGrpObjRepresentableBy`

English:
lemma GrpObj.ofRepresentableBy_yonedaGrpObjRepresentableBy
  proof: by
  ext; change lift (fst G G) (snd G G) ≫ μ = μ; rw [lift_fst_snd, Category.id_comp]

#adaptation_note

中文:
引理 GrpObj.ofRepresentableBy_yonedaGrpObjRepresentableBy
  证明: by
  ext; change lift (fst G G) (snd G G) ≫ μ = μ; rw [lift_fst_snd, Category.id_comp]

#adaptation_note

Depends on / 依赖: Category, Category.id_comp, id_comp, lift_fst_snd
-/
lemma GrpObj.ofRepresentableBy_yonedaGrpObjRepresentableBy :
    ofRepresentableBy G _ (yonedaGrpObjRepresentableBy G) = ‹GrpObj G› := by
  ext; change lift (fst G G) (snd G G) ≫ μ = μ; rw [lift_fst_snd, Category.id_comp]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
variable (X) in
/-- If `X` represents a presheaf of groups `F`, then `Hom(-, X)` is isomorphic to `F` as
a presheaf of groups. -/
@[to_additive (attr := simps! hom inv)
/-- If `X` represents a presheaf of additive groups `F`, then `Hom(-, X)` is isomorphic to `F` as
a presheaf of additive groups. -/]
/--
Definition of `yonedaGrpObjIsoOfRepresentableBy` / `yonedaGrpObjIsoOfRepresentableBy` 的定义

English:
definition yonedaGrpObjIsoOfRepresentableBy
  signature: (F : Cᵒᵖ ⥤ GrpCat.{v}) (α : (F ⋙ forget _).RepresentableBy X)
  body: GrpObj.ofRepresentableBy X F α
    yonedaGrpObj X ≅ F :=
  letI := GrpObj.ofRepresentableBy X F α
  NatIso.ofComponents (fun Y => MulEquiv.toGrpIso
    { toEquiv := α.homEquiv
      map_mul' :=
  ((yonedaMonObjIsoOfRepresentableBy X (F ⋙ forget₂ GrpCat MonCat) α).hom.app Y).hom.map_mul })
fun φ => GrpCat.hom_ext MonoidHom.ext α.homEquiv_comp φ.unop

中文:
定义 yonedaGrpObjIsoOfRepresentableBy
  签名: (F : Cᵒᵖ ⥤ 群范畴.{v}) (α : (F ⋙ forget _).可表示 X)
  定义体: GrpObj.ofRepresentableBy X F α
    yonedaGrpObj X ≅ F :=
  letI := GrpObj.ofRepresentableBy X F α
  NatIso.ofComponents (fun Y => MulEquiv.toGrpIso
    { toEquiv := α.homEquiv
      map_mul' :=
  ((yonedaMonObjIsoOfRepresentableBy X (F ⋙ forget₂ GrpCat MonCat) α).hom.app Y).hom.map_mul })
fun φ => GrpCat.hom_ext MonoidHom.ext α.homEquiv_comp φ.unop

Depends on / 依赖: GrpObj, GrpObj.ofRepresentableBy, isRegularEpiCategory_sheaf, ofRepresentableBy
-/
def yonedaGrpObjIsoOfRepresentableBy (F : Cᵒᵖ ⥤ GrpCat.{v}) (α : (F ⋙ forget _).RepresentableBy X) :
    letI := GrpObj.ofRepresentableBy X F α
    yonedaGrpObj X ≅ F :=
  letI := GrpObj.ofRepresentableBy X F α
  NatIso.ofComponents (fun Y => MulEquiv.toGrpIso
    { toEquiv := α.homEquiv
      map_mul' :=
  ((yonedaMonObjIsoOfRepresentableBy X (F ⋙ forget₂ GrpCat MonCat) α).hom.app Y).hom.map_mul })
fun φ => GrpCat.hom_ext MonoidHom.ext α.homEquiv_comp φ.unop

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The yoneda embedding of `Grp C` into presheaves of groups. -/
@[to_additive (attr := simps)
/-- The yoneda embedding of `AddGrp_C` into presheaves of additive groups. -/]
/--
Definition of `yonedaGrp` / `yonedaGrp` 的定义

English:
definition yonedaGrp
  signature: : Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{v} where
  body: yonedaGrpObj G.X
  map {G H} ψ := { app Y := GrpCat.ofHom ((yonedaMon.map ψ.hom).app Y).hom }

#adaptation_note

中文:
定义 yonedaGrp
  签名: : 群 C ⥤ Cᵒᵖ ⥤ 群范畴.{v} where
  定义体: yonedaGrpObj G.X
  map {G H} ψ := { app Y := GrpCat.ofHom ((yonedaMon.map ψ.hom).app Y).hom }

#adaptation_note

Depends on / 依赖: yonedaGrpObj
-/
def yonedaGrp : Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{v} where
  obj G := yonedaGrpObj G.X
  map {G H} ψ := { app Y := GrpCat.ofHom ((yonedaMon.map ψ.hom).app Y).hom }

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_additive (attr := reassoc)]
/--
lemma `yonedaGrp_naturality` / 引理 `yonedaGrp_naturality`

English:
lemma yonedaGrp_naturality
  given: (α : yonedaGrpObj G ⟶ yonedaGrpObj H) (f : X ⟶ Y) (g : Y ⟶ G)
  proof: congr($(α.naturality f.op) g)

中文:
引理 yonedaGrp_naturality
  条件: (α : yonedaGrpObj G ⟶ yonedaGrpObj H) (f : X ⟶ Y) (g : Y ⟶ G)
  证明: congr($(α.naturality f.op) g)

Depends on / 依赖: f.op, naturality
-/
lemma yonedaGrp_naturality (α : yonedaGrpObj G ⟶ yonedaGrpObj H) (f : X ⟶ Y) (g : Y ⟶ G) :
    α.app _ (f ≫ g) = f ≫ α.app _ g := congr($(α.naturality f.op) g)

/-- The yoneda embedding for `Grp C` is fully faithful. -/
@[to_additive
/-- The yoneda embedding for `AddGrp C` is fully faithful. -/]
/--
Definition of `yonedaGrpFullyFaithful` / `yonedaGrpFullyFaithful` 的定义

English:
definition yonedaGrpFullyFaithful
  signature: : yonedaGrp (C := C).FullyFaithful where
  body: Grp.homMk' (yonedaMonFullyFaithful.preimage ((Functor.whiskerRight α (forget₂ GrpCat MonCat))))
  map_preimage {G H} α := by
    ext X : 3
    exact congr(($(yonedaMonFullyFaithful.map_preimage (X := G.toMon) (Y := H.toMon)
      (Functor.whiskerRight α (forget₂ GrpCat MonCat))).app X).hom)
  preimage_map f := by
    ext
    congr
    apply yonedaMonFullyFaithful.preimage_map

@[to_additive]

中文:
定义 yonedaGrpFullyFaithful
  签名: : yonedaGrp (C := C).满忠实 where
  定义体: Grp.homMk' (yonedaMonFullyFaithful.preimage ((Functor.whiskerRight α (forget₂ GrpCat MonCat))))
  map_preimage {G H} α := by
    ext X : 3
    exact congr(($(yonedaMonFullyFaithful.map_preimage (X := G.toMon) (Y := H.toMon)
      (Functor.whiskerRight α (forget₂ GrpCat MonCat))).app X).hom)
  preimage_map f := by
    ext
    congr
    apply yonedaMonFullyFaithful.preimage_map

@[to_additive]

Depends on / 依赖: FullyFaithful
-/
def yonedaGrpFullyFaithful : yonedaGrp (C := C).FullyFaithful where
  preimage {G H} α :=
    Grp.homMk' (yonedaMonFullyFaithful.preimage ((Functor.whiskerRight α (forget₂ GrpCat MonCat))))
  map_preimage {G H} α := by
    ext X : 3
    exact congr(($(yonedaMonFullyFaithful.map_preimage (X := G.toMon) (Y := H.toMon)
      (Functor.whiskerRight α (forget₂ GrpCat MonCat))).app X).hom)
  preimage_map f := by
    ext
    congr
    apply yonedaMonFullyFaithful.preimage_map

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: yonedaGrp (C := C).Full
  body: yonedaGrpFullyFaithful.full
@[to_additive]

中文:
实例 :
  签名: yonedaGrp (C := C).满
  定义体: yonedaGrpFullyFaithful.full
@[to_additive]

Depends on / 依赖: yonedaGrpFullyFaithful, yonedaGrpFullyFaithful.full
-/
instance : yonedaGrp (C := C).Full := yonedaGrpFullyFaithful.full
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: yonedaGrp (C := C).Faithful
  body: yonedaGrpFullyFaithful.faithful

@[to_additive]

中文:
实例 :
  签名: yonedaGrp (C := C).忠实
  定义体: yonedaGrpFullyFaithful.faithful

@[to_additive]

Depends on / 依赖: Faithful, faithful, yonedaGrpFullyFaithful, yonedaGrpFullyFaithful.faithful
-/
instance : yonedaGrp (C := C).Faithful := yonedaGrpFullyFaithful.faithful

@[to_additive]
/--
lemma `essImage_yonedaGrp` / 引理 `essImage_yonedaGrp`

English:
lemma essImage_yonedaGrp
  proof: by
  ext F
  constructor
  · rintro ⟨G, ⟨α⟩⟩
    exact ⟨G.X, ⟨Functor.representableByEquiv.symm (Functor.isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    let := GrpObj.ofRepresentableBy X F e
    exact ⟨⟨X⟩, ⟨yonedaGrpObjIsoOfRepresentableBy X F e⟩⟩

@[to_additive (attr := reassoc)]

中文:
引理 essImage_yonedaGrp
  证明: by
  ext F
  constructor
  · rintro ⟨G, ⟨α⟩⟩
    exact ⟨G.X, ⟨Functor.representableByEquiv.symm (Functor.isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    let := GrpObj.ofRepresentableBy X F e
    exact ⟨⟨X⟩, ⟨yonedaGrpObjIsoOfRepresentableBy X F e⟩⟩

@[to_additive (attr := reassoc)]

Depends on / 依赖: Functor, Functor.isoWhiskerRight, Functor.representableByEquiv.symm, GrpObj, GrpObj.ofRepresentableBy, IsRepresentable, essImage, forget, isoWhiskerRight, ofRepresentableBy, representableByEquiv, yonedaGrpObjIsoOfRepresentableBy
-/
lemma essImage_yonedaGrp :
    yonedaGrp (C := C).essImage = fun F => (F ⋙ forget _).IsRepresentable := by
  ext F
  constructor
  · rintro ⟨G, ⟨α⟩⟩
    exact ⟨G.X, ⟨Functor.representableByEquiv.symm (Functor.isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    let := GrpObj.ofRepresentableBy X F e
    exact ⟨⟨X⟩, ⟨yonedaGrpObjIsoOfRepresentableBy X F e⟩⟩

@[to_additive (attr := reassoc)]
/--
lemma `GrpObj.inv_comp` / 引理 `GrpObj.inv_comp`

English:
lemma GrpObj.inv_comp
  given: (f : X ⟶ G) (g : G ⟶ H) [IsMonHom g]
  statement: f⁻¹ ≫ g = (f ≫ g)⁻¹
  proof: by
  simp [Hom.inv_def]

@[to_additive (attr := reassoc)]

中文:
引理 GrpObj.inv_comp
  条件: (f : X ⟶ G) (g : G ⟶ H) [是幺半群态射 g]
  结论: f⁻¹ ≫ g = (f ≫ g)⁻¹
  证明: by
  simp [Hom.inv_def]

@[to_additive (attr := reassoc)]

Depends on / 依赖: Hom.inv_def, inv_def
-/
lemma GrpObj.inv_comp (f : X ⟶ G) (g : G ⟶ H) [IsMonHom g] : f⁻¹ ≫ g = (f ≫ g)⁻¹ := by
  simp [Hom.inv_def]

@[to_additive (attr := reassoc)]
/--
lemma `GrpObj.div_comp` / 引理 `GrpObj.div_comp`

English:
lemma GrpObj.div_comp
  given: (f g : X ⟶ G) (h : G ⟶ H) [IsMonHom h]
  proof: ((yonedaGrp.map (Grp.homMk (A := .mk G) (B := .mk H) h)).app (op X)).hom.map_div f g

@[to_additive (attr := reassoc)]

中文:
引理 GrpObj.div_comp
  条件: (f g : X ⟶ G) (h : G ⟶ H) [是幺半群态射 h]
  证明: ((yonedaGrp.map (Grp.homMk (A := .mk G) (B := .mk H) h)).app (op X)).hom.map_div f g

@[to_additive (attr := reassoc)]

Depends on / 依赖: Grp.homMk, hom.map_div, map_div, yonedaGrp, yonedaGrp.map
-/
lemma GrpObj.div_comp (f g : X ⟶ G) (h : G ⟶ H) [IsMonHom h] :
    (f / g) ≫ h = (f ≫ h) / (g ≫ h) :=
  ((yonedaGrp.map (Grp.homMk (A := .mk G) (B := .mk H) h)).app (op X)).hom.map_div f g

@[to_additive (attr := reassoc)]
/--
lemma `GrpObj.zpow_comp` / 引理 `GrpObj.zpow_comp`

English:
lemma GrpObj.zpow_comp
  given: (f : X ⟶ G) (n : Int) (g : G ⟶ H) [IsMonHom g]
  proof: ((yonedaGrp.map (Grp.homMk (A := .mk G) (B := .mk H) g)).app (op X)).hom.map_zpow f n

@[to_additive (attr := reassoc)]

中文:
引理 GrpObj.zpow_comp
  条件: (f : X ⟶ G) (n : 整数) (g : G ⟶ H) [是幺半群态射 g]
  证明: ((yonedaGrp.map (Grp.homMk (A := .mk G) (B := .mk H) g)).app (op X)).hom.map_zpow f n

@[to_additive (attr := reassoc)]

Depends on / 依赖: Grp.homMk, hom.map_zpow, map_zpow, yonedaGrp, yonedaGrp.map
-/
lemma GrpObj.zpow_comp (f : X ⟶ G) (n : Int) (g : G ⟶ H) [IsMonHom g] :
    (f ^ n) ≫ g = (f ≫ g) ^ n :=
  ((yonedaGrp.map (Grp.homMk (A := .mk G) (B := .mk H) g)).app (op X)).hom.map_zpow f n

@[to_additive (attr := reassoc)]
/--
lemma `GrpObj.comp_inv` / 引理 `GrpObj.comp_inv`

English:
lemma GrpObj.comp_inv
  given: (f : X ⟶ Y) (g : Y ⟶ G)
  statement: f ≫ g⁻¹ = (f ≫ g)⁻¹
  proof: ((yonedaGrp.obj ⟨G⟩).map f.op).hom.map_inv g

@[to_additive (attr := reassoc)]

中文:
引理 GrpObj.comp_inv
  条件: (f : X ⟶ Y) (g : Y ⟶ G)
  结论: f ≫ g⁻¹ = (f ≫ g)⁻¹
  证明: ((yonedaGrp.obj ⟨G⟩).map f.op).hom.map_inv g

@[to_additive (attr := reassoc)]

Depends on / 依赖: f.op, hom.map_inv, map_inv, yonedaGrp, yonedaGrp.obj
-/
lemma GrpObj.comp_inv (f : X ⟶ Y) (g : Y ⟶ G) : f ≫ g⁻¹ = (f ≫ g)⁻¹ :=
  ((yonedaGrp.obj ⟨G⟩).map f.op).hom.map_inv g

@[to_additive (attr := reassoc)]
/--
lemma `GrpObj.comp_div` / 引理 `GrpObj.comp_div`

English:
lemma GrpObj.comp_div
  given: (f : X ⟶ Y) (g h : Y ⟶ G)
  statement: f ≫ (g / h) = f ≫ g / f ≫ h
  proof: ((yonedaGrp.obj ⟨G⟩).map f.op).hom.map_div g h

@[to_additive (attr := reassoc)]

中文:
引理 GrpObj.comp_div
  条件: (f : X ⟶ Y) (g h : Y ⟶ G)
  结论: f ≫ (g / h) = f ≫ g / f ≫ h
  证明: ((yonedaGrp.obj ⟨G⟩).map f.op).hom.map_div g h

@[to_additive (attr := reassoc)]

Depends on / 依赖: f.op, hom.map_div, map_div, yonedaGrp, yonedaGrp.obj
-/
lemma GrpObj.comp_div (f : X ⟶ Y) (g h : Y ⟶ G) : f ≫ (g / h) = f ≫ g / f ≫ h :=
  ((yonedaGrp.obj ⟨G⟩).map f.op).hom.map_div g h

@[to_additive (attr := reassoc)]
/--
lemma `GrpObj.comp_zpow` / 引理 `GrpObj.comp_zpow`

English:
lemma GrpObj.comp_zpow
  given: (f : X ⟶ Y) (g : Y ⟶ G)
  statement: forall n : Int, f ≫ g ^ n = (f ≫ g) ^ n

中文:
引理 GrpObj.comp_zpow
  条件: (f : X ⟶ Y) (g : Y ⟶ G)
  结论: 对任意 n : 整数, f ≫ g ^ n = (f ≫ g) ^ n
-/
lemma GrpObj.comp_zpow (f : X ⟶ Y) (g : Y ⟶ G) : forall n : Int, f ≫ g ^ n = (f ≫ g) ^ n
  | (n : Nat) => by simp [comp_pow]
  | .negSucc n => by simp [comp_pow, comp_inv]

@[to_additive]
/--
lemma `GrpObj.inv_eq_inv` / 引理 `GrpObj.inv_eq_inv`

English:
lemma GrpObj.inv_eq_inv
  statement: ι = (𝟙 G)⁻¹
  proof: by simp [Hom.inv_def]

@[to_additive (attr := reassoc (attr := simp))]

中文:
引理 GrpObj.inv_eq_inv
  结论: ι = (𝟙 G)⁻¹
  证明: by simp [Hom.inv_def]

@[to_additive (attr := reassoc (attr := simp))]

Depends on / 依赖: Hom.inv_def, inv_def
-/
lemma GrpObj.inv_eq_inv : ι = (𝟙 G)⁻¹ := by simp [Hom.inv_def]

@[to_additive (attr := reassoc (attr := simp))]
/--
lemma `GrpObj.one_inv` / 引理 `GrpObj.one_inv`

English:
lemma GrpObj.one_inv
  statement: η[G] ≫ ι = η
  proof: by simp [GrpObj.inv_eq_inv, GrpObj.comp_inv, one_eq_one]

中文:
引理 GrpObj.one_inv
  结论: η[G] ≫ ι = η
  证明: by simp [GrpObj.inv_eq_inv, GrpObj.comp_inv, one_eq_one]

Depends on / 依赖: GrpObj, GrpObj.comp_inv, GrpObj.inv_eq_inv, comp_inv, inv_eq_inv, one_eq_one
-/
lemma GrpObj.one_inv : η[G] ≫ ι = η := by simp [GrpObj.inv_eq_inv, GrpObj.comp_inv, one_eq_one]

open scoped _root_.CategoryTheory.Obj in
/-- If `G` is a group object and `F` is monoidal,
then `Hom(X, G) → Hom(F X, F G)` preserves inverses. -/
@[to_additive (attr := simp) /-- If `G` is an additive group object and `F` is monoidal,
then `Hom(X, G) → Hom(F X, F G)` preserves negation. -/]
/--
lemma `Functor.map_inv'` / 引理 `Functor.map_inv'`

English:
lemma Functor.map_inv'
  statement: {D : Type*} [Category* D] [CartesianMonoidalCategory D] (F : C ⥤ D)
  proof: by
  rw [eq_inv_iff_mul_eq_one]; rw [← Functor.map_mul]; rw [inv_mul_cancel]; rw [Functor.map_one]

中文:
引理 函子.map_inv'
  结论: {D : 类型} [范畴* D] [CartesianMonoidal范畴 D] (F : C ⥤ D)
  证明: by
  rw [eq_inv_iff_mul_eq_one]; rw [← Functor.map_mul]; rw [inv_mul_cancel]; rw [Functor.map_one]

Depends on / 依赖: Functor, Functor.map_mul, Functor.map_one, eq_inv_iff_mul_eq_one, inv_mul_cancel, map_mul, map_one
-/
lemma Functor.map_inv' {D : Type*} [Category* D] [CartesianMonoidalCategory D] (F : C ⥤ D)
    [F.Monoidal] {X G : C} (f : X ⟶ G) [GrpObj G] :
    F.map (f⁻¹) = (F.map f)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]; rw [← Functor.map_mul]; rw [inv_mul_cancel]; rw [Functor.map_one]

/-- Conjugation in `G` as a morphism. This is the map `(x, y) ↦ x * y * x⁻¹`,
see `CategoryTheory.GrpObj.lift_conj_eq_mul_mul_inv`. -/
@[to_additive
/-- Conjugation in `G` as a morphism. This is the map `(x, y) ↦ x + y + (-x)`,
see `CategoryTheory.AddGrpObj.lift_conj_eq_add_add_neg`. -/]
/--
Definition of `GrpObj.conj` / `GrpObj.conj` 的定义

English:
definition GrpObj.conj
  signature: (G : C) [GrpObj G]
  body: fst _ _ * snd _ _ * (fst _ _)⁻¹

@[to_additive (attr := reassoc (attr := simp))]

中文:
定义 GrpObj.conj
  签名: (G : C) [GrpObj G]
  定义体: fst _ _ * snd _ _ * (fst _ _)⁻¹

@[to_additive (attr := reassoc (attr := simp))]
-/
def GrpObj.conj (G : C) [GrpObj G] : G otimes G ⟶ G :=
  fst _ _ * snd _ _ * (fst _ _)⁻¹

@[to_additive (attr := reassoc (attr := simp))]
/--
lemma `GrpObj.lift_conj_eq_mul_mul_inv` / 引理 `GrpObj.lift_conj_eq_mul_mul_inv`

English:
lemma GrpObj.lift_conj_eq_mul_mul_inv
  given: {X G : C} [GrpObj G] (f₁ f₂ : X ⟶ G)
  proof: by
  simp [conj, comp_mul, comp_inv]

中文:
引理 GrpObj.lift_conj_eq_mul_mul_inv
  条件: {X G : C} [GrpObj G] (f₁ f₂ : X ⟶ G)
  证明: by
  simp [conj, comp_mul, comp_inv]

Depends on / 依赖: comp_inv, comp_mul
-/
lemma GrpObj.lift_conj_eq_mul_mul_inv {X G : C} [GrpObj G] (f₁ f₂ : X ⟶ G) :
    lift f₁ f₂ ≫ conj G = f₁ * f₂ * f₁⁻¹ := by
  simp [conj, comp_mul, comp_inv]

/-- The commutator of `G` as a morphism. This is the map `(x, y) ↦ x * y * x⁻¹ * y⁻¹`,
see `CategoryTheory.GrpObj.lift_commutator_eq_mul_mul_inv_inv`.
This morphism is constant with value `1` if and only if `G` is commutative
(see `CategoryTheory.isCommMonObj_iff_commutator_eq_toUnit_η`). -/
@[to_additive
/-- The commutator of `G` as a morphism. This is the map `(x, y) ↦ x + y + (-x) + (-y)`,
see `CategoryTheory.AddGrpObj.lift_commutator_eq_add_add_neg_neg`.
This morphism is constant with value `0` if and only if `G` is commutative
(see `CategoryTheory.isCommAddMonObj_iff_commutator_eq_toAddUnit_η`). -/]
/--
Definition of `GrpObj.commutator` / `GrpObj.commutator` 的定义

English:
definition GrpObj.commutator
  signature: (G : C) [GrpObj G]
  body: fst _ _ * snd _ _ * (fst _ _)⁻¹ * (snd _ _)⁻¹

@[to_additive (attr := reassoc (attr := simp))]

中文:
定义 GrpObj.commutator
  签名: (G : C) [GrpObj G]
  定义体: fst _ _ * snd _ _ * (fst _ _)⁻¹ * (snd _ _)⁻¹

@[to_additive (attr := reassoc (attr := simp))]
-/
def GrpObj.commutator (G : C) [GrpObj G] : G otimes G ⟶ G :=
  fst _ _ * snd _ _ * (fst _ _)⁻¹ * (snd _ _)⁻¹

@[to_additive (attr := reassoc (attr := simp))]
/--
lemma `GrpObj.lift_commutator_eq_mul_mul_inv_inv` / 引理 `GrpObj.lift_commutator_eq_mul_mul_inv_inv`

English:
lemma GrpObj.lift_commutator_eq_mul_mul_inv_inv
  given: {X G : C} [GrpObj G] (f₁ f₂ : X ⟶ G)
  proof: by
  simp [commutator, comp_mul, comp_inv]

@[to_additive (attr := reassoc (attr := simp))]

中文:
引理 GrpObj.lift_commutator_eq_mul_mul_inv_inv
  条件: {X G : C} [GrpObj G] (f₁ f₂ : X ⟶ G)
  证明: by
  simp [commutator, comp_mul, comp_inv]

@[to_additive (attr := reassoc (attr := simp))]

Depends on / 依赖: commutator, comp_inv, comp_mul
-/
lemma GrpObj.lift_commutator_eq_mul_mul_inv_inv {X G : C} [GrpObj G] (f₁ f₂ : X ⟶ G) :
    lift f₁ f₂ ≫ commutator G = f₁ * f₂ * f₁⁻¹ * f₂⁻¹ := by
  simp [commutator, comp_mul, comp_inv]

@[to_additive (attr := reassoc (attr := simp))]
/--
lemma `GrpObj.η_whiskerRight_commutator` / 引理 `GrpObj.η_whiskerRight_commutator`

English:
lemma GrpObj.η_whiskerRight_commutator
  statement: η ▷ G ≫ commutator G = toUnit _ ≫ η
  proof: by
  simp [commutator, comp_mul, comp_inv, one_eq_one]

@[to_additive (attr := reassoc (attr := simp))]

中文:
引理 GrpObj.η_whiskerRight_commutator
  结论: η ▷ G ≫ commutator G = toUnit _ ≫ η
  证明: by
  simp [commutator, comp_mul, comp_inv, one_eq_one]

@[to_additive (attr := reassoc (attr := simp))]

Depends on / 依赖: commutator, comp_inv, comp_mul, one_eq_one
-/
lemma GrpObj.η_whiskerRight_commutator : η ▷ G ≫ commutator G = toUnit _ ≫ η := by
  simp [commutator, comp_mul, comp_inv, one_eq_one]

@[to_additive (attr := reassoc (attr := simp))]
/--
lemma `GrpObj.whiskerLeft_η_commutator` / 引理 `GrpObj.whiskerLeft_η_commutator`

English:
lemma GrpObj.whiskerLeft_η_commutator
  statement: G ◁ η ≫ commutator G = toUnit _ ≫ η
  proof: by
  simp [commutator, comp_mul, comp_inv, one_eq_one]

中文:
引理 GrpObj.whiskerLeft_η_commutator
  结论: G ◁ η ≫ commutator G = toUnit _ ≫ η
  证明: by
  simp [commutator, comp_mul, comp_inv, one_eq_one]

Depends on / 依赖: commutator, comp_inv, comp_mul, one_eq_one
-/
lemma GrpObj.whiskerLeft_η_commutator : G ◁ η ≫ commutator G = toUnit _ ≫ η := by
  simp [commutator, comp_mul, comp_inv, one_eq_one]

variable [BraidedCategory C]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCommMonObj
  signature: G] : IsMonHom ι[G] where
  body: by simp [one_eq_one, ← Hom.inv_def]
  mul_hom := by simp [GrpObj.mul_inv_rev]

中文:
实例 [是交换MonObj
  签名: G] : 是幺半群态射 ι[G] where
  定义体: by simp [one_eq_one, ← Hom.inv_def]
  mul_hom := by simp [GrpObj.mul_inv_rev]

Depends on / 依赖: GrpObj, GrpObj.mul_inv_rev, Hom.inv_def, inv_def, mul_hom, mul_inv_rev, one_eq_one
-/
instance [IsCommMonObj G] : IsMonHom ι[G] where
  one_hom := by simp [one_eq_one, ← Hom.inv_def]
  mul_hom := by simp [GrpObj.mul_inv_rev]

attribute [local simp] Hom.inv_def in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCommMonObj
  signature: G] {f

中文:
实例 [是交换MonObj
  签名: G] {f
-/
instance [IsCommMonObj G] {f : M ⟶ G} [IsMonHom f] : IsMonHom f⁻¹ where

namespace Grp
variable {G H : Grp C} [IsCommMonObj H.X]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonObj H
  body: Grp.homMk η[H.toMon].hom
  mul := Grp.homMk μ[H.toMon].hom

@[to_additive (attr := simp)]

中文:
实例 :
  签名: MonObj H
  定义体: Grp.homMk η[H.toMon].hom
  mul := Grp.homMk μ[H.toMon].hom

@[to_additive (attr := simp)]

Depends on / 依赖: Grp.homMk, H.toMon
-/
instance : MonObj H where
  one := Grp.homMk η[H.toMon].hom
  mul := Grp.homMk μ[H.toMon].hom

@[to_additive (attr := simp)]
/--
lemma `hom_one` / 引理 `hom_one`

English:
lemma hom_one
  given: (H : Grp C) [IsCommMonObj H.X]
  statement: η[H].hom.hom = η[H.X]
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 hom_one
  条件: (H : 群 C) [是交换MonObj H.X]
  结论: η[H].hom.hom = η[H.X]
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma hom_one (H : Grp C) [IsCommMonObj H.X] : η[H].hom.hom = η[H.X] := rfl
@[to_additive (attr := simp)]
/--
lemma `hom_mul` / 引理 `hom_mul`

English:
lemma hom_mul
  given: (H : Grp C) [IsCommMonObj H.X]
  statement: μ[H].hom.hom = μ[H.X]
  proof: rfl

中文:
引理 hom_mul
  条件: (H : 群 C) [是交换MonObj H.X]
  结论: μ[H].hom.hom = μ[H.X]
  证明: rfl
-/
lemma hom_mul (H : Grp C) [IsCommMonObj H.X] : μ[H].hom.hom = μ[H.X] := rfl

namespace Hom

@[to_additive (attr := simp)]
/--
lemma `hom_one` / 引理 `hom_one`

English:
lemma hom_one
  statement: (1 : G ⟶ H).hom = 1
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 hom_one
  结论: (1 : G ⟶ H).hom = 1
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma hom_one : (1 : G ⟶ H).hom = 1 := rfl
@[to_additive (attr := simp)]
/--
lemma `hom_mul` / 引理 `hom_mul`

English:
lemma hom_mul
  given: (f g : G ⟶ H)
  statement: (f * g).hom = f.hom * g.hom
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 hom_mul
  条件: (f g : G ⟶ H)
  结论: (f * g).hom = f.hom * g.hom
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma hom_mul (f g : G ⟶ H) : (f * g).hom = f.hom * g.hom := rfl
@[to_additive (attr := simp)]
/--
lemma `hom_pow` / 引理 `hom_pow`

English:
lemma hom_pow
  given: (f : G ⟶ H) (n : Nat)
  statement: (f ^ n).hom = f.hom ^ n
  proof: by
  induction n with
  | zero => simp
  | succ n hn => simp [pow_succ, hn]

中文:
引理 hom_pow
  条件: (f : G ⟶ H) (n : 自然数)
  结论: (f ^ n).hom = f.hom ^ n
  证明: by
  induction n with
  | zero => simp
  | succ n hn => simp [pow_succ, hn]

Depends on / 依赖: pow_succ
-/
lemma hom_pow (f : G ⟶ H) (n : Nat) : (f ^ n).hom = f.hom ^ n := by
  induction n with
  | zero => simp
  | succ n hn => simp [pow_succ, hn]

end Hom

/-- A commutative group object is a group object in the category of group objects. -/
@[to_additive /-- A commutative additive group object is an additive group object in the category of
additive group objects. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GrpObj H
  body: Grp.homMk' { hom := ι[H.X] }

中文:
实例 :
  签名: GrpObj H
  定义体: Grp.homMk' { hom := ι[H.X] }

Depends on / 依赖: Grp.homMk
-/
instance : GrpObj H where inv := Grp.homMk' { hom := ι[H.X] }

namespace Hom

@[to_additive (attr := simp)]
/--
lemma `hom_hom_inv` / 引理 `hom_hom_inv`

English:
lemma hom_hom_inv
  given: (f : G ⟶ H)
  statement: f⁻¹.hom.hom = f.hom.hom⁻¹
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 hom_hom_inv
  条件: (f : G ⟶ H)
  结论: f⁻¹.hom.hom = f.hom.hom⁻¹
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma hom_hom_inv (f : G ⟶ H) : f⁻¹.hom.hom = f.hom.hom⁻¹ := rfl
@[to_additive (attr := simp)]
/--
lemma `hom_hom_div` / 引理 `hom_hom_div`

English:
lemma hom_hom_div
  given: (f g : G ⟶ H)
  statement: (f / g).hom.hom = f.hom.hom / g.hom.hom
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 hom_hom_div
  条件: (f g : G ⟶ H)
  结论: (f / g).hom.hom = f.hom.hom / g.hom.hom
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma hom_hom_div (f g : G ⟶ H) : (f / g).hom.hom = f.hom.hom / g.hom.hom := rfl
@[to_additive (attr := simp)]
/--
lemma `hom_hom_zpow` / 引理 `hom_hom_zpow`

English:
lemma hom_hom_zpow
  given: (f : G ⟶ H) (n : Int)
  statement: (f ^ n).hom.hom = f.hom.hom ^ n
  proof: by
  cases n <;> simp

中文:
引理 hom_hom_zpow
  条件: (f : G ⟶ H) (n : 整数)
  结论: (f ^ n).hom.hom = f.hom.hom ^ n
  证明: by
  cases n <;> simp
-/
lemma hom_hom_zpow (f : G ⟶ H) (n : Int) : (f ^ n).hom.hom = f.hom.hom ^ n := by
  cases n <;> simp

end Hom

attribute [local simp] mul_eq_mul comp_mul mul_comm mul_div_mul_comm in
/-- A commutative group object is a commutative group object in the category of group objects. -/
@[to_additive /-- A commutative additive group object is a commutative additive group object in the
category of additive group objects. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCommMonObj H

中文:
实例 :
  签名: 是交换MonObj H
-/
instance : IsCommMonObj H where

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCommMonObj
  signature: G.X] (f

中文:
实例 [是交换MonObj
  签名: G.X] (f
-/
instance [IsCommMonObj G.X] (f : G ⟶ H) : IsMonHom f where

end Grp

/-- If `G` is a commutative group object, then `Hom(X, G)` has a commutative group structure. -/
@[to_additive
/-- If `G` is a commutative additive group object, then `Hom(X, G)` has a commutative
additive group structure. -/]
/--
Definition of `Hom.commGroup` / `Hom.commGroup` 的定义

English:
abbreviation Hom.commGroup
  signature: [IsCommMonObj G]

中文:
缩写 态射.commGroup
  签名: [是交换MonObj G]
-/
abbrev Hom.commGroup [IsCommMonObj G] : CommGroup (X ⟶ G) where

scoped[CategoryTheory.MonObj] attribute [instance] Hom.commGroup
scoped[CategoryTheory.AddMonObj] attribute [instance] Hom.addCommGroup

section

@[to_additive]
/--
lemma `GrpObj.conj_eq_snd_of_isCommMonObj` / 引理 `GrpObj.conj_eq_snd_of_isCommMonObj`

English:
lemma GrpObj.conj_eq_snd_of_isCommMonObj
  given: [IsCommMonObj G]
  statement: conj G = snd G G
  proof: by
  simp [conj]

中文:
引理 GrpObj.conj_eq_snd_of_isCommMonObj
  条件: [是交换MonObj G]
  结论: conj G = snd G G
  证明: by
  simp [conj]
-/
lemma GrpObj.conj_eq_snd_of_isCommMonObj [IsCommMonObj G] : conj G = snd G G := by
  simp [conj]

open scoped IsMulCommutative in
/-- `G` is a commutative group object if and only if the commutator map `(x, y) ↦ x * y * x⁻¹ * y⁻¹`
is constant. -/
@[to_additive /-- `G` is a commutative additive group object if and only if the commutator map
`(x, y) ↦ x + y + (-x) + (-y)` is constant. -/]
/--
lemma `isCommMonObj_iff_commutator_eq_toUnit_η` / 引理 `isCommMonObj_iff_commutator_eq_toUnit_η`

English:
lemma isCommMonObj_iff_commutator_eq_toUnit_η
  proof: by
  rw [isCommMonObj_iff_isMulCommutative]
  refine ⟨fun h => ?_, fun heq X => ⟨⟨fun f g => ?_⟩⟩⟩
  · simp [GrpObj.commutator, one_eq_one]
  · simpa [one_eq_one, mul_inv_eq_iff_eq_mul] using congr(lift f g ≫ $heq)

中文:
引理 isCommMonObj_iff_commutator_eq_toUnit_η
  证明: by
  rw [isCommMonObj_iff_isMulCommutative]
  refine ⟨fun h => ?_, fun heq X => ⟨⟨fun f g => ?_⟩⟩⟩
  · simp [GrpObj.commutator, one_eq_one]
  · simpa [one_eq_one, mul_inv_eq_iff_eq_mul] using congr(lift f g ≫ $heq)

Depends on / 依赖: GrpObj, GrpObj.commutator, commutator, isCommMonObj_iff_isMulCommutative, mul_inv_eq_iff_eq_mul, one_eq_one
-/
lemma isCommMonObj_iff_commutator_eq_toUnit_η :
    IsCommMonObj G ↔ GrpObj.commutator G = toUnit _ ≫ η := by
  rw [isCommMonObj_iff_isMulCommutative]
  refine ⟨fun h => ?_, fun heq X => ⟨⟨fun f g => ?_⟩⟩⟩
  · simp [GrpObj.commutator, one_eq_one]
  · simpa [one_eq_one, mul_inv_eq_iff_eq_mul] using congr(lift f g ≫ $heq)

end

end CategoryTheory
