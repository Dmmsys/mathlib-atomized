/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Ext
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Tactic.Abel

/-!
# Basic facts about biproducts in preadditive categories.

In (or between) preadditive categories,

* Any biproduct satisfies the equality
  `total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`,
  or, in the binary case, `total : fst ≫ inl + snd ≫ inr = 𝟙 X`.

* Any (binary) `product` or (binary) `coproduct` is a (binary) `biproduct`.

* In any category (with zero morphisms), if `biprod.map f g` is an isomorphism,
  then both `f` and `g` are isomorphisms.

* If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
  so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
  via Gaussian elimination.

* As a corollary of the previous two facts,
  if we have an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  we can construct an isomorphism `X₂ ≅ Y₂`.

* If `f : W ⊞ X ⟶ Y ⊞ Z` is an isomorphism, either `𝟙 W = 0`,
  or at least one of the component maps `W ⟶ Y` and `W ⟶ Z` is nonzero.

* If `f : ⨁ S ⟶ ⨁ T` is an isomorphism,
  then every column (corresponding to a nonzero summand in the domain)
  has some nonzero matrix entry.

* A functor preserves a biproduct if and only if it preserves
  the corresponding product if and only if it preserves the corresponding coproduct.

There are connections between this material and the special case of the category whose morphisms are
matrices over a ring, in particular the Schur complement (see
`Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`). In particular, the declarations
`CategoryTheory.Biprod.isoElim`, `CategoryTheory.Biprod.gaussian`
and `Matrix.invertibleOfFromBlocks₁₁Invertible` are all closely related.

-/

@[expose] public section


open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

open CategoryTheory.Functor

open CategoryTheory.Preadditive

universe v v' u u'

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace Limits

section Fintype

variable {J : Type*} [Fintype J]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isBilimitOfTotal` / `isBilimitOfTotal` 的定义

English:
definition isBilimitOfTotal
  signature: {f : J -> C} (b : Bicone f) (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt)
  body: { lift := fun s => ∑ j : J, s.π.app ⟨j⟩ ≫ b.ι j
      uniq := fun s m h => by
        rw [← Category.comp_id m]
        dsimp
        rw [← total]; rw [comp_sum]
        apply Finset.sum_congr rfl
        intro j _
        have reassoced : m ≫ Bicone.π b j ≫ Bicone.ι b j = s.π.app ⟨j⟩ ≫ Bicone.ι b j

中文:
定义 isBilimitOfTotal
  签名: {f : J -> C} (b : Bicone f) (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt)
  定义体: { lift := fun s => ∑ j : J, s.π.app ⟨j⟩ ≫ b.ι j
      uniq := fun s m h => by
        rw [← Category.comp_id m]
        dsimp
        rw [← total]; rw [comp_sum]
        apply Finset.sum_congr rfl
        intro j _
        have reassoced : m ≫ Bicone.π b j ≫ Bicone.ι b j = s.π.app ⟨j⟩ ≫ Bicone.ι b j

Depends on / 依赖: Bicone, Bicone.toCone_, Category, Category.assoc, Category.comp_id, Finset, Finset.sum_congr, classical, comp_dite, comp_id, comp_sum, eq_whisker, isColimit, reassoced, sum_comp, sum_congr
-/
def isBilimitOfTotal {f : J -> C} (b : Bicone f) (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt) :
    b.IsBilimit where
  isLimit :=
    { lift := fun s => ∑ j : J, s.π.app ⟨j⟩ ≫ b.ι j
      uniq := fun s m h => by
        rw [← Category.comp_id m]
        dsimp
        rw [← total]; rw [comp_sum]
        apply Finset.sum_congr rfl
        intro j _
        have reassoced : m ≫ Bicone.π b j ≫ Bicone.ι b j = s.π.app ⟨j⟩ ≫ Bicone.ι b j := by
          simpa using eq_whisker (h ⟨j⟩) _
        rw [reassoced]
      fac := fun s j => by
        classical
        cases j
        simp only [sum_comp, Category.assoc, Bicone.toCone_π_app, b.ι_π, comp_dite]
        simp }
  isColimit :=
    { desc := fun s => ∑ j : J, b.π j ≫ s.ι.app ⟨j⟩
      uniq := fun s m h => by
        rw [← Category.id_comp m]
        dsimp
        rw [← total]; rw [sum_comp]
        apply Finset.sum_congr rfl
        intro j _
        simpa using b.π j ≫= h ⟨j⟩
      fac := fun s j => by
        classical
        cases j
        simp only [comp_sum, ← Category.assoc, Bicone.toCocone_ι_app, b.ι_π, dite_comp]
        simp }

/--
theorem `IsBilimit.total` / 定理 `IsBilimit.total`

English:
theorem IsBilimit.total
  given: {f : J -> C} {b : Bicone f} (i : b.IsBilimit)
  proof: i.isLimit.hom_ext fun j => by
    classical
    cases j
    simp [sum_comp, b.ι_π, comp_dite]

中文:
定理 是Bilimit.total
  条件: {f : J -> C} {b : Bicone f} (i : b.是Bilimit)
  证明: i.isLimit.hom_ext fun j => by
    classical
    cases j
    simp [sum_comp, b.ι_π, comp_dite]

Depends on / 依赖: classical, comp_dite, hom_ext, i.isLimit.hom_ext, isLimit, sum_comp
-/
theorem IsBilimit.total {f : J -> C} {b : Bicone f} (i : b.IsBilimit) :
    ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt :=
  i.isLimit.hom_ext fun j => by
    classical
    cases j
    simp [sum_comp, b.ι_π, comp_dite]

/--
theorem `hasBiproduct_of_total` / 定理 `hasBiproduct_of_total`

English:
theorem hasBiproduct_of_total
  statement: {f : J -> C} (b : Bicone f)
  proof: HasBiproduct.mk
    { bicone := b
      isBilimit := isBilimitOfTotal b total }

中文:
定理 hasBiproduct_of_total
  结论: {f : J -> C} (b : Bicone f)
  证明: HasBiproduct.mk
    { bicone := b
      isBilimit := isBilimitOfTotal b total }

Depends on / 依赖: HasBiproduct, HasBiproduct.mk, bicone, isBilimit, isBilimitOfTotal
-/
theorem hasBiproduct_of_total {f : J -> C} (b : Bicone f)
    (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt) : HasBiproduct f :=
  HasBiproduct.mk
    { bicone := b
      isBilimit := isBilimitOfTotal b total }

/--
Definition of `isBilimitOfIsLimit` / `isBilimitOfIsLimit` 的定义

English:
definition isBilimitOfIsLimit
  signature: {f : J -> C} (t : Bicone f) (ht : IsLimit t.toCone)
  body: isBilimitOfTotal _
    ht.hom_ext fun j => by
      classical
      cases j
      simp [sum_comp, t.ι_π, comp_dite]

中文:
定义 isBilimitOfIsLimit
  签名: {f : J -> C} (t : Bicone f) (ht : 是极限 t.toCone)
  定义体: isBilimitOfTotal _
    ht.hom_ext fun j => by
      classical
      cases j
      simp [sum_comp, t.ι_π, comp_dite]

Depends on / 依赖: classical, comp_dite, hom_ext, ht.hom_ext, isBilimitOfTotal, sum_comp
-/
def isBilimitOfIsLimit {f : J -> C} (t : Bicone f) (ht : IsLimit t.toCone) : t.IsBilimit :=
isBilimitOfTotal _
    ht.hom_ext fun j => by
      classical
      cases j
      simp [sum_comp, t.ι_π, comp_dite]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `biconeIsBilimitOfLimitConeOfIsLimit` / `biconeIsBilimitOfLimitConeOfIsLimit` 的定义

English:
definition biconeIsBilimitOfLimitConeOfIsLimit
  signature: {f : J -> C} {t : Cone (Discrete.functor f)}
  body: isBilimitOfIsLimit _ IsLimit.ofIsoLimit ht Cone.ext (Iso.refl _) (by simp)

中文:
定义 biconeIsBilimitOfLimitConeOfIsLimit
  签名: {f : J -> C} {t : 锥 (离散.functor f)}
  定义体: isBilimitOfIsLimit _ IsLimit.ofIsoLimit ht Cone.ext (Iso.refl _) (by simp)

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.ofIsoLimit, Iso.refl, isBilimitOfIsLimit, ofIsoLimit
-/
def biconeIsBilimitOfLimitConeOfIsLimit {f : J -> C} {t : Cone (Discrete.functor f)}
    (ht : IsLimit t) : (Bicone.ofLimitCone ht).IsBilimit :=
isBilimitOfIsLimit _ IsLimit.ofIsoLimit ht Cone.ext (Iso.refl _) (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isBilimitOfIsColimit` / `isBilimitOfIsColimit` 的定义

English:
definition isBilimitOfIsColimit
  signature: {f : J -> C} (t : Bicone f) (ht : IsColimit t.toCocone)
  body: isBilimitOfTotal _
    ht.hom_ext fun j => by
      classical
      cases j
      simp_rw [Bicone.toCocone_ι_app, comp_sum, ← Category.assoc, t.ι_π, dite_comp]
      simp

中文:
定义 isBilimitOfIsColimit
  签名: {f : J -> C} (t : Bicone f) (ht : 是余极限 t.toCocone)
  定义体: isBilimitOfTotal _
    ht.hom_ext fun j => by
      classical
      cases j
      simp_rw [Bicone.toCocone_ι_app, comp_sum, ← Category.assoc, t.ι_π, dite_comp]
      simp

Depends on / 依赖: Bicone, Bicone.toCocone_, Category, Category.assoc, classical, comp_sum, dite_comp, hom_ext, ht.hom_ext, isBilimitOfTotal, simp_rw
-/
def isBilimitOfIsColimit {f : J -> C} (t : Bicone f) (ht : IsColimit t.toCocone) : t.IsBilimit :=
isBilimitOfTotal _
    ht.hom_ext fun j => by
      classical
      cases j
      simp_rw [Bicone.toCocone_ι_app, comp_sum, ← Category.assoc, t.ι_π, dite_comp]
      simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `biconeIsBilimitOfColimitCoconeOfIsColimit` / `biconeIsBilimitOfColimitCoconeOfIsColimit` 的定义

English:
definition biconeIsBilimitOfColimitCoconeOfIsColimit
  signature: {f : J -> C} {t : Cocone (Discrete.functor f)}
  body: isBilimitOfIsColimit _ IsColimit.ofIsoColimit ht Cocone.ext (Iso.refl _) by
    simp

中文:
定义 biconeIsBilimitOfColimitCoconeOfIsColimit
  签名: {f : J -> C} {t : 余锥 (离散.functor f)}
  定义体: isBilimitOfIsColimit _ IsColimit.ofIsoColimit ht Cocone.ext (Iso.refl _) by
    simp

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, Iso.refl, isBilimitOfIsColimit, ofIsoColimit
-/
def biconeIsBilimitOfColimitCoconeOfIsColimit {f : J -> C} {t : Cocone (Discrete.functor f)}
    (ht : IsColimit t) : (Bicone.ofColimitCocone ht).IsBilimit :=
isBilimitOfIsColimit _ IsColimit.ofIsoColimit ht Cocone.ext (Iso.refl _) by
    simp

end Fintype

section Finite

variable {J : Type*} [Finite J]

/--
theorem `HasBiproduct.of_hasProduct` / 定理 `HasBiproduct.of_hasProduct`

English:
theorem HasBiproduct.of_hasProduct
  given: (f : J -> C) [HasProduct f]
  statement: HasBiproduct f
  proof: by
  cases nonempty_fintype J
  exact HasBiproduct.mk
    { bicone := _
      isBilimit := biconeIsBilimitOfLimitConeOfIsLimit (limit.isLimit _) }

中文:
定理 有Biproduct.of_hasProduct
  条件: (f : J -> C) [HasProduct f]
  结论: 有Biproduct f
  证明: by
  cases nonempty_fintype J
  exact HasBiproduct.mk
    { bicone := _
      isBilimit := biconeIsBilimitOfLimitConeOfIsLimit (limit.isLimit _) }

Depends on / 依赖: HasBiproduct, HasBiproduct.mk, bicone, biconeIsBilimitOfLimitConeOfIsLimit, isBilimit, isLimit, limit.isLimit, nonempty_fintype
-/
theorem HasBiproduct.of_hasProduct (f : J -> C) [HasProduct f] : HasBiproduct f := by
  cases nonempty_fintype J
  exact HasBiproduct.mk
    { bicone := _
      isBilimit := biconeIsBilimitOfLimitConeOfIsLimit (limit.isLimit _) }

/--
theorem `HasBiproduct.of_hasCoproduct` / 定理 `HasBiproduct.of_hasCoproduct`

English:
theorem HasBiproduct.of_hasCoproduct
  given: (f : J -> C) [HasCoproduct f]
  statement: HasBiproduct f
  proof: by
  cases nonempty_fintype J
  exact HasBiproduct.mk
    { bicone := _
      isBilimit := biconeIsBilimitOfColimitCoconeOfIsColimit (colimit.isColimit _) }

中文:
定理 有Biproduct.of_hasCoproduct
  条件: (f : J -> C) [HasCoproduct f]
  结论: 有Biproduct f
  证明: by
  cases nonempty_fintype J
  exact HasBiproduct.mk
    { bicone := _
      isBilimit := biconeIsBilimitOfColimitCoconeOfIsColimit (colimit.isColimit _) }

Depends on / 依赖: HasBiproduct, HasBiproduct.mk, bicone, biconeIsBilimitOfColimitCoconeOfIsColimit, colimit, colimit.isColimit, isBilimit, isColimit, nonempty_fintype
-/
theorem HasBiproduct.of_hasCoproduct (f : J -> C) [HasCoproduct f] : HasBiproduct f := by
  cases nonempty_fintype J
  exact HasBiproduct.mk
    { bicone := _
      isBilimit := biconeIsBilimitOfColimitCoconeOfIsColimit (colimit.isColimit _) }

end Finite

/--
theorem `HasFiniteBiproducts.of_hasFiniteProducts` / 定理 `HasFiniteBiproducts.of_hasFiniteProducts`

English:
theorem HasFiniteBiproducts.of_hasFiniteProducts
  given: [HasFiniteProducts C]
  statement: HasFiniteBiproducts C
  proof: ⟨fun _ => { has_biproduct := fun _ => HasBiproduct.of_hasProduct _ }⟩

中文:
定理 有FiniteBiproducts.of_hasFiniteProducts
  条件: [有FiniteProducts C]
  结论: 有FiniteBiproducts C
  证明: ⟨fun _ => { has_biproduct := fun _ => HasBiproduct.of_hasProduct _ }⟩

Depends on / 依赖: HasBiproduct, HasBiproduct.of_hasProduct, has_biproduct, of_hasProduct
-/
theorem HasFiniteBiproducts.of_hasFiniteProducts [HasFiniteProducts C] : HasFiniteBiproducts C :=
  ⟨fun _ => { has_biproduct := fun _ => HasBiproduct.of_hasProduct _ }⟩

/--
theorem `HasFiniteBiproducts.of_hasFiniteCoproducts` / 定理 `HasFiniteBiproducts.of_hasFiniteCoproducts`

English:
theorem HasFiniteBiproducts.of_hasFiniteCoproducts
  given: [HasFiniteCoproducts C]
  proof: ⟨fun _ => { has_biproduct := fun _ => HasBiproduct.of_hasCoproduct _ }⟩

中文:
定理 有FiniteBiproducts.of_hasFiniteCoproducts
  条件: [有FiniteCoproducts C]
  证明: ⟨fun _ => { has_biproduct := fun _ => HasBiproduct.of_hasCoproduct _ }⟩

Depends on / 依赖: HasBiproduct, HasBiproduct.of_hasCoproduct, has_biproduct, of_hasCoproduct
-/
theorem HasFiniteBiproducts.of_hasFiniteCoproducts [HasFiniteCoproducts C] :
    HasFiniteBiproducts C :=
  ⟨fun _ => { has_biproduct := fun _ => HasBiproduct.of_hasCoproduct _ }⟩

section HasBiproduct

variable {J : Type} [Fintype J] {f : J -> C} [HasBiproduct f]

/-- In any preadditive category, any biproduct satisfies
`∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
-/
@[simp]
/--
theorem `biproduct.total` / 定理 `biproduct.total`

English:
theorem biproduct.total
  statement: ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)
  proof: IsBilimit.total (biproduct.isBilimit _)

中文:
定理 biproduct.total
  结论: ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)
  证明: IsBilimit.total (biproduct.isBilimit _)

Depends on / 依赖: IsBilimit, IsBilimit.total, biproduct, biproduct.isBilimit, isBilimit
-/
theorem biproduct.total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f) :=
  IsBilimit.total (biproduct.isBilimit _)

/--
theorem `biproduct.lift_eq` / 定理 `biproduct.lift_eq`

English:
theorem biproduct.lift_eq
  given: {T : C} {g : forall j, T ⟶ f j}
  proof: by
  classical
  ext j
  simp only [sum_comp, biproduct.ι_π, comp_dite, biproduct.lift_π, Category.assoc, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id, if_true]

中文:
定理 biproduct.lift_eq
  条件: {T : C} {g : 对任意 j, T ⟶ f j}
  证明: by
  classical
  ext j
  simp only [sum_comp, biproduct.ι_π, comp_dite, biproduct.lift_π, Category.assoc, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id, if_true]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Finset, Finset.mem_univ, Finset.sum_dite_eq, biproduct, biproduct.lift_, classical, comp_dite, comp_id, comp_zero, eqToHom_refl, if_true, mem_univ, sum_comp, sum_dite_eq
-/
theorem biproduct.lift_eq {T : C} {g : forall j, T ⟶ f j} :
    biproduct.lift g = ∑ j, g j ≫ biproduct.ι f j := by
  classical
  ext j
  simp only [sum_comp, biproduct.ι_π, comp_dite, biproduct.lift_π, Category.assoc, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id, if_true]

/--
theorem `biproduct.desc_eq` / 定理 `biproduct.desc_eq`

English:
theorem biproduct.desc_eq
  given: {T : C} {g : forall j, f j ⟶ T}
  proof: by
  classical
  ext j
  simp [comp_sum, biproduct.ι_π_assoc, dite_comp]

@[reassoc]

中文:
定理 biproduct.desc_eq
  条件: {T : C} {g : 对任意 j, f j ⟶ T}
  证明: by
  classical
  ext j
  simp [comp_sum, biproduct.ι_π_assoc, dite_comp]

@[reassoc]

Depends on / 依赖: biproduct, classical, comp_sum, dite_comp
-/
theorem biproduct.desc_eq {T : C} {g : forall j, f j ⟶ T} :
    biproduct.desc g = ∑ j, biproduct.π f j ≫ g j := by
  classical
  ext j
  simp [comp_sum, biproduct.ι_π_assoc, dite_comp]

@[reassoc]
/--
theorem `biproduct.lift_desc` / 定理 `biproduct.lift_desc`

English:
theorem biproduct.lift_desc
  given: {T U : C} {g : forall j, T ⟶ f j} {h : forall j, f j ⟶ U}
  proof: by
  classical
  simp [biproduct.lift_eq, biproduct.desc_eq, comp_sum, sum_comp, biproduct.ι_π_assoc, comp_dite,
    dite_comp]

中文:
定理 biproduct.lift_desc
  条件: {T U : C} {g : 对任意 j, T ⟶ f j} {h : 对任意 j, f j ⟶ U}
  证明: by
  classical
  simp [biproduct.lift_eq, biproduct.desc_eq, comp_sum, sum_comp, biproduct.ι_π_assoc, comp_dite,
    dite_comp]

Depends on / 依赖: biproduct, biproduct.desc_eq, biproduct.lift_eq, classical, comp_dite, comp_sum, desc_eq, dite_comp, lift_eq, sum_comp
-/
theorem biproduct.lift_desc {T U : C} {g : forall j, T ⟶ f j} {h : forall j, f j ⟶ U} :
    biproduct.lift g ≫ biproduct.desc h = ∑ j : J, g j ≫ h j := by
  classical
  simp [biproduct.lift_eq, biproduct.desc_eq, comp_sum, sum_comp, biproduct.ι_π_assoc, comp_dite,
    dite_comp]

/--
theorem `biproduct.map_eq` / 定理 `biproduct.map_eq`

English:
theorem biproduct.map_eq
  given: [HasFiniteBiproducts C] {f g : J -> C} {h : forall j, f j ⟶ g j}
  proof: by
  classical
  ext
  simp [biproduct.ι_π, biproduct.ι_π_assoc, sum_comp, comp_dite, dite_comp]

@[reassoc]

中文:
定理 biproduct.map_eq
  条件: [有FiniteBiproducts C] {f g : J -> C} {h : 对任意 j, f j ⟶ g j}
  证明: by
  classical
  ext
  simp [biproduct.ι_π, biproduct.ι_π_assoc, sum_comp, comp_dite, dite_comp]

@[reassoc]

Depends on / 依赖: biproduct, classical, comp_dite, dite_comp, sum_comp
-/
theorem biproduct.map_eq [HasFiniteBiproducts C] {f g : J -> C} {h : forall j, f j ⟶ g j} :
    biproduct.map h = ∑ j : J, biproduct.π f j ≫ h j ≫ biproduct.ι g j := by
  classical
  ext
  simp [biproduct.ι_π, biproduct.ι_π_assoc, sum_comp, comp_dite, dite_comp]

@[reassoc]
/--
theorem `biproduct.lift_matrix` / 定理 `biproduct.lift_matrix`

English:
theorem biproduct.lift_matrix
  statement: {K : Type} [Finite K] [HasFiniteBiproducts C] {f : J -> C} {g : K -> C}
  proof: by
  ext
  simp [biproduct.lift_desc]

中文:
定理 biproduct.lift_matrix
  结论: {K : 类型} [有限 K] [有FiniteBiproducts C] {f : J -> C} {g : K -> C}
  证明: by
  ext
  simp [biproduct.lift_desc]

Depends on / 依赖: biproduct, biproduct.lift_desc, lift_desc
-/
theorem biproduct.lift_matrix {K : Type} [Finite K] [HasFiniteBiproducts C] {f : J -> C} {g : K -> C}
    {P} (x : forall j, P ⟶ f j) (m : forall j k, f j ⟶ g k) :
    biproduct.lift x ≫ biproduct.matrix m = biproduct.lift fun k => ∑ j, x j ≫ m j k := by
  ext
  simp [biproduct.lift_desc]

end HasBiproduct

section HasFiniteBiproducts

variable {J K : Type} [Finite J] {f : J -> C} [HasFiniteBiproducts C]

@[reassoc]
/--
theorem `biproduct.matrix_desc` / 定理 `biproduct.matrix_desc`

English:
theorem biproduct.matrix_desc
  statement: [Fintype K] {f : J -> C} {g : K -> C}
  proof: by
  ext
  simp [lift_desc]

中文:
定理 biproduct.matrix_desc
  结论: [有限类型 K] {f : J -> C} {g : K -> C}
  证明: by
  ext
  simp [lift_desc]

Depends on / 依赖: DecidableRel, lift_desc
-/
theorem biproduct.matrix_desc [Fintype K] {f : J -> C} {g : K -> C}
    (m : forall j k, f j ⟶ g k) {P} (x : forall k, g k ⟶ P) :
    biproduct.matrix m ≫ biproduct.desc x = biproduct.desc fun j => ∑ k, m j k ≫ x k := by
  ext
  simp [lift_desc]

variable [Finite K]

@[reassoc]
/--
theorem `biproduct.matrix_map` / 定理 `biproduct.matrix_map`

English:
theorem biproduct.matrix_map
  statement: {f : J -> C} {g : K -> C} {h : K -> C} (m : forall j k, f j ⟶ g k)
  proof: by
  ext
  simp

@[reassoc]

中文:
定理 biproduct.matrix_map
  结论: {f : J -> C} {g : K -> C} {h : K -> C} (m : 对任意 j k, f j ⟶ g k)
  证明: by
  ext
  simp

@[reassoc]

Depends on / 依赖: Digraph, Digraph.mk, Embedding, Embedding.injective, Fintype, Fintype.ofBijective, G.Adj, classical, injective, ofBijective
-/
theorem biproduct.matrix_map {f : J -> C} {g : K -> C} {h : K -> C} (m : forall j k, f j ⟶ g k)
    (n : forall k, g k ⟶ h k) :
    biproduct.matrix m ≫ biproduct.map n = biproduct.matrix fun j k => m j k ≫ n k := by
  ext
  simp

@[reassoc]
/--
theorem `biproduct.map_matrix` / 定理 `biproduct.map_matrix`

English:
theorem biproduct.map_matrix
  statement: {f : J -> C} {g : J -> C} {h : K -> C} (m : forall k, f k ⟶ g k)
  proof: by
  ext
  simp

中文:
定理 biproduct.map_matrix
  结论: {f : J -> C} {g : J -> C} {h : K -> C} (m : 对任意 k, f k ⟶ g k)
  证明: by
  ext
  simp
-/
theorem biproduct.map_matrix {f : J -> C} {g : J -> C} {h : K -> C} (m : forall k, f k ⟶ g k)
    (n : forall j k, g j ⟶ h k) :
    biproduct.map m ≫ biproduct.matrix n = biproduct.matrix fun j k => m j ≫ n j k := by
  ext
  simp

end HasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
/-- Reindex a categorical biproduct via an equivalence of the index types. -/
@[simps]
/--
Definition of `biproduct.reindex` / `biproduct.reindex` 的定义

English:
definition biproduct.reindex
  signature: {β γ : Type} [Finite β] (ε : β ≃ γ)
  body: biproduct.desc fun b => biproduct.ι f (ε b)
  inv := biproduct.lift fun b => biproduct.π f (ε b)
  hom_inv_id := by
    ext b b'
    by_cases h : b' = b
    · subst h; simp
    · have : ε b' != ε b := by simp [h]
      simp [biproduct.ι_π_ne _ h, biproduct.ι_π_ne _ this]
  inv_hom_id := by
    class

中文:
定义 biproduct.reindex
  签名: {β γ : 类型} [有限 β] (ε : β ≃ γ)
  定义体: biproduct.desc fun b => biproduct.ι f (ε b)
  inv := biproduct.lift fun b => biproduct.π f (ε b)
  hom_inv_id := by
    ext b b'
    by_cases h : b' = b
    · subst h; simp
    · have : ε b' != ε b := by simp [h]
      simp [biproduct.ι_π_ne _ h, biproduct.ι_π_ne _ this]
  inv_hom_id := by
    class

Depends on / 依赖: biproduct, biproduct.desc
-/
def biproduct.reindex {β γ : Type} [Finite β] (ε : β ≃ γ)
    (f : γ -> C) [HasBiproduct f] [HasBiproduct (f ∘ ε)] : ⨁ f ∘ ε ≅ ⨁ f where
  hom := biproduct.desc fun b => biproduct.ι f (ε b)
  inv := biproduct.lift fun b => biproduct.π f (ε b)
  hom_inv_id := by
    ext b b'
    by_cases h : b' = b
    · subst h; simp
    · have : ε b' != ε b := by simp [h]
      simp [biproduct.ι_π_ne _ h, biproduct.ι_π_ne _ this]
  inv_hom_id := by
    classical
    cases nonempty_fintype β
    ext g g'
    by_cases h : g' = g <;>
      simp [Preadditive.sum_comp, biproduct.lift_desc, biproduct.ι_π, comp_dite,
        ← Equiv.eq_symm_apply, h]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isBinaryBilimitOfTotal` / `isBinaryBilimitOfTotal` 的定义

English:
definition isBinaryBilimitOfTotal
  signature: {X Y : C} (b : BinaryBicone X Y)
  body: { lift := fun s =>
      (BinaryFan.fst s ≫ b.inl : s.pt ⟶ b.pt) + (BinaryFan.snd s ≫ b.inr : s.pt ⟶ b.pt)
      uniq := fun s m h => by
        have hₗ := h ⟨.left⟩
        have hᵣ := h ⟨.right⟩
        dsimp at hₗ hᵣ
        simpa [← hₗ, ← hᵣ] using m ≫= total.symm
      fac := fun s j => by rcase

中文:
定义 isBinaryBilimitOfTotal
  签名: {X Y : C} (b : BinaryBicone X Y)
  定义体: { lift := fun s =>
      (BinaryFan.fst s ≫ b.inl : s.pt ⟶ b.pt) + (BinaryFan.snd s ≫ b.inr : s.pt ⟶ b.pt)
      uniq := fun s m h => by
        have hₗ := h ⟨.left⟩
        have hᵣ := h ⟨.right⟩
        dsimp at hₗ hᵣ
        simpa [← hₗ, ← hᵣ] using m ≫= total.symm
      fac := fun s j => by rcase

Depends on / 依赖: BinaryCofan, BinaryCofan.inl, BinaryCofan.inr, BinaryFan, BinaryFan.fst, BinaryFan.snd, b.fst, b.inl, b.inr, b.pt, b.snd, isColimit, s.pt, total.symm
-/
def isBinaryBilimitOfTotal {X Y : C} (b : BinaryBicone X Y)
    (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) : b.IsBilimit where
  isLimit :=
    { lift := fun s =>
      (BinaryFan.fst s ≫ b.inl : s.pt ⟶ b.pt) + (BinaryFan.snd s ≫ b.inr : s.pt ⟶ b.pt)
      uniq := fun s m h => by
        have hₗ := h ⟨.left⟩
        have hᵣ := h ⟨.right⟩
        dsimp at hₗ hᵣ
        simpa [← hₗ, ← hᵣ] using m ≫= total.symm
      fac := fun s j => by rcases j with ⟨⟨⟩⟩ <;> simp }
  isColimit :=
    { desc := fun s =>
        (b.fst ≫ BinaryCofan.inl s : b.pt ⟶ s.pt) + (b.snd ≫ BinaryCofan.inr s : b.pt ⟶ s.pt)
      uniq := fun s m h => by
        have hₗ := h ⟨.left⟩
        have hᵣ := h ⟨.right⟩
        dsimp at hₗ hᵣ
        simpa [← hₗ, ← hᵣ] using total.symm =≫ m
      fac := fun s j => by rcases j with ⟨⟨⟩⟩ <;> simp }

/--
theorem `IsBilimit.binary_total` / 定理 `IsBilimit.binary_total`

English:
theorem IsBilimit.binary_total
  given: {X Y : C} {b : BinaryBicone X Y} (i : b.IsBilimit)
  proof: i.isLimit.hom_ext fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

中文:
定理 是Bilimit.binary_total
  条件: {X Y : C} {b : BinaryBicone X Y} (i : b.是Bilimit)
  证明: i.isLimit.hom_ext fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

Depends on / 依赖: hom_ext, i.isLimit.hom_ext, isLimit
-/
theorem IsBilimit.binary_total {X Y : C} {b : BinaryBicone X Y} (i : b.IsBilimit) :
    b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt :=
  i.isLimit.hom_ext fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

/--
theorem `hasBinaryBiproduct_of_total` / 定理 `hasBinaryBiproduct_of_total`

English:
theorem hasBinaryBiproduct_of_total
  statement: {X Y : C} (b : BinaryBicone X Y)
  proof: HasBinaryBiproduct.mk
    { bicone := b
      isBilimit := isBinaryBilimitOfTotal b total }

中文:
定理 hasBinaryBiproduct_of_total
  结论: {X Y : C} (b : BinaryBicone X Y)
  证明: HasBinaryBiproduct.mk
    { bicone := b
      isBilimit := isBinaryBilimitOfTotal b total }

Depends on / 依赖: HasBinaryBiproduct, HasBinaryBiproduct.mk, bicone, isBilimit, isBinaryBilimitOfTotal
-/
theorem hasBinaryBiproduct_of_total {X Y : C} (b : BinaryBicone X Y)
    (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) : HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk
    { bicone := b
      isBilimit := isBinaryBilimitOfTotal b total }

set_option backward.isDefEq.respectTransparency false in
/-- We can turn any limit cone over a pair into a bicone. -/
@[simps]
/--
Definition of `BinaryBicone.ofLimitCone` / `BinaryBicone.ofLimitCone` 的定义

English:
definition BinaryBicone.ofLimitCone
  signature: {X Y : C} {t : Cone (pair X Y)} (ht : IsLimit t)
  body: t.pt
  fst := t.π.app ⟨WalkingPair.left⟩
  snd := t.π.app ⟨WalkingPair.right⟩
  inl := BinaryFan.IsLimit.lift ht (𝟙 X) 0
  inr := BinaryFan.IsLimit.lift ht 0 (𝟙 Y)

中文:
定义 BinaryBicone.ofLimitCone
  签名: {X Y : C} {t : 锥 (pair X Y)} (ht : 是极限 t)
  定义体: t.pt
  fst := t.π.app ⟨WalkingPair.left⟩
  snd := t.π.app ⟨WalkingPair.right⟩
  inl := BinaryFan.IsLimit.lift ht (𝟙 X) 0
  inr := BinaryFan.IsLimit.lift ht 0 (𝟙 Y)

Depends on / 依赖: t.pt
-/
def BinaryBicone.ofLimitCone {X Y : C} {t : Cone (pair X Y)} (ht : IsLimit t) :
    BinaryBicone X Y where
  pt := t.pt
  fst := t.π.app ⟨WalkingPair.left⟩
  snd := t.π.app ⟨WalkingPair.right⟩
  inl := BinaryFan.IsLimit.lift ht (𝟙 X) 0
  inr := BinaryFan.IsLimit.lift ht 0 (𝟙 Y)

set_option backward.defeqAttrib.useBackward true in
/--
theorem `inl_of_isLimit` / 定理 `inl_of_isLimit`

English:
theorem inl_of_isLimit
  given: {X Y : C} {t : BinaryBicone X Y} (ht : IsLimit t.toCone)
  proof: by
  apply ht.uniq (BinaryFan.mk (𝟙 X) 0); rintro ⟨⟨⟩⟩ <;> simp

中文:
定理 inl_of_isLimit
  条件: {X Y : C} {t : BinaryBicone X Y} (ht : 是极限 t.toCone)
  证明: by
  apply ht.uniq (BinaryFan.mk (𝟙 X) 0); rintro ⟨⟨⟩⟩ <;> simp

Depends on / 依赖: BinaryFan, BinaryFan.mk, ht.uniq
-/
theorem inl_of_isLimit {X Y : C} {t : BinaryBicone X Y} (ht : IsLimit t.toCone) :
    t.inl = BinaryFan.IsLimit.lift ht (𝟙 X) 0 := by
  apply ht.uniq (BinaryFan.mk (𝟙 X) 0); rintro ⟨⟨⟩⟩ <;> simp

set_option backward.defeqAttrib.useBackward true in
/--
theorem `inr_of_isLimit` / 定理 `inr_of_isLimit`

English:
theorem inr_of_isLimit
  given: {X Y : C} {t : BinaryBicone X Y} (ht : IsLimit t.toCone)
  proof: by
  apply ht.uniq (BinaryFan.mk 0 (𝟙 Y)); rintro ⟨⟨⟩⟩ <;> simp

中文:
定理 inr_of_isLimit
  条件: {X Y : C} {t : BinaryBicone X Y} (ht : 是极限 t.toCone)
  证明: by
  apply ht.uniq (BinaryFan.mk 0 (𝟙 Y)); rintro ⟨⟨⟩⟩ <;> simp

Depends on / 依赖: BinaryFan, BinaryFan.mk, ht.uniq
-/
theorem inr_of_isLimit {X Y : C} {t : BinaryBicone X Y} (ht : IsLimit t.toCone) :
    t.inr = BinaryFan.IsLimit.lift ht 0 (𝟙 Y) := by
  apply ht.uniq (BinaryFan.mk 0 (𝟙 Y)); rintro ⟨⟨⟩⟩ <;> simp

/--
Definition of `isBinaryBilimitOfIsLimit` / `isBinaryBilimitOfIsLimit` 的定义

English:
definition isBinaryBilimitOfIsLimit
  signature: {X Y : C} (t : BinaryBicone X Y) (ht : IsLimit t.toCone)
  body: isBinaryBilimitOfTotal _ (by refine BinaryFan.IsLimit.hom_ext ht ?_ ?_ <;> simp)

中文:
定义 isBinaryBilimitOfIsLimit
  签名: {X Y : C} (t : BinaryBicone X Y) (ht : 是极限 t.toCone)
  定义体: isBinaryBilimitOfTotal _ (by refine BinaryFan.IsLimit.hom_ext ht ?_ ?_ <;> simp)

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.hom_ext, IsLimit, hom_ext, isBinaryBilimitOfTotal
-/
def isBinaryBilimitOfIsLimit {X Y : C} (t : BinaryBicone X Y) (ht : IsLimit t.toCone) :
    t.IsBilimit :=
  isBinaryBilimitOfTotal _ (by refine BinaryFan.IsLimit.hom_ext ht ?_ ?_ <;> simp)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `binaryBiconeIsBilimitOfLimitConeOfIsLimit` / `binaryBiconeIsBilimitOfLimitConeOfIsLimit` 的定义

English:
definition binaryBiconeIsBilimitOfLimitConeOfIsLimit
  signature: {X Y : C} {t : Cone (pair X Y)} (ht : IsLimit t)
  body: isBinaryBilimitOfTotal _ BinaryFan.IsLimit.hom_ext ht (by simp) (by simp)

中文:
定义 binaryBiconeIsBilimitOfLimitConeOfIsLimit
  签名: {X Y : C} {t : 锥 (pair X Y)} (ht : 是极限 t)
  定义体: isBinaryBilimitOfTotal _ BinaryFan.IsLimit.hom_ext ht (by simp) (by simp)

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.hom_ext, IsLimit, hom_ext, isBinaryBilimitOfTotal
-/
def binaryBiconeIsBilimitOfLimitConeOfIsLimit {X Y : C} {t : Cone (pair X Y)} (ht : IsLimit t) :
    (BinaryBicone.ofLimitCone ht).IsBilimit :=
isBinaryBilimitOfTotal _ BinaryFan.IsLimit.hom_ext ht (by simp) (by simp)

/--
theorem `HasBinaryBiproduct.of_hasBinaryProduct` / 定理 `HasBinaryBiproduct.of_hasBinaryProduct`

English:
theorem HasBinaryBiproduct.of_hasBinaryProduct
  given: (X Y : C) [HasBinaryProduct X Y]
  proof: HasBinaryBiproduct.mk
    { bicone := _
      isBilimit := binaryBiconeIsBilimitOfLimitConeOfIsLimit (limit.isLimit _) }

中文:
定理 有BinaryBiproduct.of_hasBinaryProduct
  条件: (X Y : C) [HasBinaryProduct X Y]
  证明: HasBinaryBiproduct.mk
    { bicone := _
      isBilimit := binaryBiconeIsBilimitOfLimitConeOfIsLimit (limit.isLimit _) }

Depends on / 依赖: HasBinaryBiproduct, HasBinaryBiproduct.mk, bicone, binaryBiconeIsBilimitOfLimitConeOfIsLimit, isBilimit, isLimit, limit.isLimit
-/
theorem HasBinaryBiproduct.of_hasBinaryProduct (X Y : C) [HasBinaryProduct X Y] :
    HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk
    { bicone := _
      isBilimit := binaryBiconeIsBilimitOfLimitConeOfIsLimit (limit.isLimit _) }

/--
theorem `HasBinaryBiproducts.of_hasBinaryProducts` / 定理 `HasBinaryBiproducts.of_hasBinaryProducts`

English:
theorem HasBinaryBiproducts.of_hasBinaryProducts
  given: [HasBinaryProducts C]
  statement: HasBinaryBiproducts C
  proof: { has_binary_biproduct := fun X Y => HasBinaryBiproduct.of_hasBinaryProduct X Y }

中文:
定理 有BinaryBiproducts.of_hasBinaryProducts
  条件: [HasBinaryProducts C]
  结论: 有BinaryBiproducts C
  证明: { has_binary_biproduct := fun X Y => HasBinaryBiproduct.of_hasBinaryProduct X Y }

Depends on / 依赖: HasBinaryBiproduct, HasBinaryBiproduct.of_hasBinaryProduct, has_binary_biproduct, of_hasBinaryProduct
-/
theorem HasBinaryBiproducts.of_hasBinaryProducts [HasBinaryProducts C] : HasBinaryBiproducts C :=
  { has_binary_biproduct := fun X Y => HasBinaryBiproduct.of_hasBinaryProduct X Y }

set_option backward.isDefEq.respectTransparency false in
/-- We can turn any colimit cocone over a pair into a bicone. -/
@[simps]
/--
Definition of `BinaryBicone.ofColimitCocone` / `BinaryBicone.ofColimitCocone` 的定义

English:
definition BinaryBicone.ofColimitCocone
  signature: {X Y : C} {t : Cocone (pair X Y)} (ht : IsColimit t)
  body: t.pt
  fst := BinaryCofan.IsColimit.desc ht (𝟙 X) 0
  snd := BinaryCofan.IsColimit.desc ht 0 (𝟙 Y)
  inl := t.ι.app ⟨WalkingPair.left⟩
  inr := t.ι.app ⟨WalkingPair.right⟩

中文:
定义 BinaryBicone.ofColimitCocone
  签名: {X Y : C} {t : 余锥 (pair X Y)} (ht : 是余极限 t)
  定义体: t.pt
  fst := BinaryCofan.IsColimit.desc ht (𝟙 X) 0
  snd := BinaryCofan.IsColimit.desc ht 0 (𝟙 Y)
  inl := t.ι.app ⟨WalkingPair.left⟩
  inr := t.ι.app ⟨WalkingPair.right⟩

Depends on / 依赖: t.pt
-/
def BinaryBicone.ofColimitCocone {X Y : C} {t : Cocone (pair X Y)} (ht : IsColimit t) :
    BinaryBicone X Y where
  pt := t.pt
  fst := BinaryCofan.IsColimit.desc ht (𝟙 X) 0
  snd := BinaryCofan.IsColimit.desc ht 0 (𝟙 Y)
  inl := t.ι.app ⟨WalkingPair.left⟩
  inr := t.ι.app ⟨WalkingPair.right⟩

set_option backward.defeqAttrib.useBackward true in
/--
theorem `fst_of_isColimit` / 定理 `fst_of_isColimit`

English:
theorem fst_of_isColimit
  given: {X Y : C} {t : BinaryBicone X Y} (ht : IsColimit t.toCocone)
  proof: by
  apply ht.uniq (BinaryCofan.mk (𝟙 X) 0)
  rintro ⟨⟨⟩⟩ <;> simp

中文:
定理 fst_of_isColimit
  条件: {X Y : C} {t : BinaryBicone X Y} (ht : 是余极限 t.toCocone)
  证明: by
  apply ht.uniq (BinaryCofan.mk (𝟙 X) 0)
  rintro ⟨⟨⟩⟩ <;> simp

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, ht.uniq
-/
theorem fst_of_isColimit {X Y : C} {t : BinaryBicone X Y} (ht : IsColimit t.toCocone) :
    t.fst = BinaryCofan.IsColimit.desc ht (𝟙 X) 0 := by
  apply ht.uniq (BinaryCofan.mk (𝟙 X) 0)
  rintro ⟨⟨⟩⟩ <;> simp

set_option backward.defeqAttrib.useBackward true in
/--
theorem `snd_of_isColimit` / 定理 `snd_of_isColimit`

English:
theorem snd_of_isColimit
  given: {X Y : C} {t : BinaryBicone X Y} (ht : IsColimit t.toCocone)
  proof: by
  apply ht.uniq (BinaryCofan.mk 0 (𝟙 Y))
  rintro ⟨⟨⟩⟩ <;> simp

中文:
定理 snd_of_isColimit
  条件: {X Y : C} {t : BinaryBicone X Y} (ht : 是余极限 t.toCocone)
  证明: by
  apply ht.uniq (BinaryCofan.mk 0 (𝟙 Y))
  rintro ⟨⟨⟩⟩ <;> simp

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, ht.uniq
-/
theorem snd_of_isColimit {X Y : C} {t : BinaryBicone X Y} (ht : IsColimit t.toCocone) :
    t.snd = BinaryCofan.IsColimit.desc ht 0 (𝟙 Y) := by
  apply ht.uniq (BinaryCofan.mk 0 (𝟙 Y))
  rintro ⟨⟨⟩⟩ <;> simp

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isBinaryBilimitOfIsColimit` / `isBinaryBilimitOfIsColimit` 的定义

English:
definition isBinaryBilimitOfIsColimit
  signature: {X Y : C} (t : BinaryBicone X Y) (ht : IsColimit t.toCocone)
  body: isBinaryBilimitOfTotal _ by
    refine BinaryCofan.IsColimit.hom_ext ht ?_ ?_ <;> simp

中文:
定义 isBinaryBilimitOfIsColimit
  签名: {X Y : C} (t : BinaryBicone X Y) (ht : 是余极限 t.toCocone)
  定义体: isBinaryBilimitOfTotal _ by
    refine BinaryCofan.IsColimit.hom_ext ht ?_ ?_ <;> simp

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.hom_ext, IsColimit, hom_ext, isBinaryBilimitOfTotal
-/
def isBinaryBilimitOfIsColimit {X Y : C} (t : BinaryBicone X Y) (ht : IsColimit t.toCocone) :
    t.IsBilimit :=
isBinaryBilimitOfTotal _ by
    refine BinaryCofan.IsColimit.hom_ext ht ?_ ?_ <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `binaryBiconeIsBilimitOfColimitCoconeOfIsColimit` / `binaryBiconeIsBilimitOfColimitCoconeOfIsColimit` 的定义

English:
definition binaryBiconeIsBilimitOfColimitCoconeOfIsColimit
  signature: {X Y : C} {t : Cocone (pair X Y)}
  body: isBinaryBilimitOfIsColimit (BinaryBicone.ofColimitCocone ht)
IsColimit.ofIsoColimit ht
      Cocone.ext (Iso.refl _) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp

中文:
定义 binaryBiconeIsBilimitOfColimitCoconeOfIsColimit
  签名: {X Y : C} {t : 余锥 (pair X Y)}
  定义体: isBinaryBilimitOfIsColimit (BinaryBicone.ofColimitCocone ht)
IsColimit.ofIsoColimit ht
      Cocone.ext (Iso.refl _) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp

Depends on / 依赖: BinaryBicone, BinaryBicone.ofColimitCocone, Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, Iso.refl, isBinaryBilimitOfIsColimit, ofColimitCocone, ofIsoColimit
-/
def binaryBiconeIsBilimitOfColimitCoconeOfIsColimit {X Y : C} {t : Cocone (pair X Y)}
    (ht : IsColimit t) : (BinaryBicone.ofColimitCocone ht).IsBilimit :=
isBinaryBilimitOfIsColimit (BinaryBicone.ofColimitCocone ht)
IsColimit.ofIsoColimit ht
      Cocone.ext (Iso.refl _) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp

/--
theorem `HasBinaryBiproduct.of_hasBinaryCoproduct` / 定理 `HasBinaryBiproduct.of_hasBinaryCoproduct`

English:
theorem HasBinaryBiproduct.of_hasBinaryCoproduct
  given: (X Y : C) [HasBinaryCoproduct X Y]
  proof: HasBinaryBiproduct.mk
    { bicone := _
      isBilimit := binaryBiconeIsBilimitOfColimitCoconeOfIsColimit (colimit.isColimit _) }

中文:
定理 有BinaryBiproduct.of_hasBinaryCoproduct
  条件: (X Y : C) [HasBinaryCoproduct X Y]
  证明: HasBinaryBiproduct.mk
    { bicone := _
      isBilimit := binaryBiconeIsBilimitOfColimitCoconeOfIsColimit (colimit.isColimit _) }

Depends on / 依赖: HasBinaryBiproduct, HasBinaryBiproduct.mk, bicone, binaryBiconeIsBilimitOfColimitCoconeOfIsColimit, colimit, colimit.isColimit, isBilimit, isColimit
-/
theorem HasBinaryBiproduct.of_hasBinaryCoproduct (X Y : C) [HasBinaryCoproduct X Y] :
    HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk
    { bicone := _
      isBilimit := binaryBiconeIsBilimitOfColimitCoconeOfIsColimit (colimit.isColimit _) }

/--
theorem `HasBinaryBiproducts.of_hasBinaryCoproducts` / 定理 `HasBinaryBiproducts.of_hasBinaryCoproducts`

English:
theorem HasBinaryBiproducts.of_hasBinaryCoproducts
  given: [HasBinaryCoproducts C]
  proof: { has_binary_biproduct := fun X Y => HasBinaryBiproduct.of_hasBinaryCoproduct X Y }

中文:
定理 有BinaryBiproducts.of_hasBinaryCoproducts
  条件: [HasBinaryCoproducts C]
  证明: { has_binary_biproduct := fun X Y => HasBinaryBiproduct.of_hasBinaryCoproduct X Y }

Depends on / 依赖: HasBinaryBiproduct, HasBinaryBiproduct.of_hasBinaryCoproduct, has_binary_biproduct, of_hasBinaryCoproduct
-/
theorem HasBinaryBiproducts.of_hasBinaryCoproducts [HasBinaryCoproducts C] :
    HasBinaryBiproducts C :=
  { has_binary_biproduct := fun X Y => HasBinaryBiproduct.of_hasBinaryCoproduct X Y }

section

variable {X Y : C} [HasBinaryBiproduct X Y]

/-- In any preadditive category, any binary biproduct satisfies
`biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y)`.
-/
@[simp]
/--
theorem `biprod.total` / 定理 `biprod.total`

English:
theorem biprod.total
  statement: biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y)
  proof: by
  ext <;> simp

中文:
定理 biprod.total
  结论: biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y)
  证明: by
  ext <;> simp
-/
theorem biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y) := by
  ext <;> simp

/--
theorem `biprod.lift_eq` / 定理 `biprod.lift_eq`

English:
theorem biprod.lift_eq
  given: {T : C} {f : T ⟶ X} {g : T ⟶ Y}
  proof: by ext <;> simp [add_comp]

中文:
定理 biprod.lift_eq
  条件: {T : C} {f : T ⟶ X} {g : T ⟶ Y}
  证明: by ext <;> simp [add_comp]

Depends on / 依赖: add_comp
-/
theorem biprod.lift_eq {T : C} {f : T ⟶ X} {g : T ⟶ Y} :
    biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr := by ext <;> simp [add_comp]

/--
theorem `biprod.desc_eq` / 定理 `biprod.desc_eq`

English:
theorem biprod.desc_eq
  given: {T : C} {f : X ⟶ T} {g : Y ⟶ T}
  proof: by ext <;> simp

@[reassoc (attr := simp)]

中文:
定理 biprod.desc_eq
  条件: {T : C} {f : X ⟶ T} {g : Y ⟶ T}
  证明: by ext <;> simp

@[reassoc (attr := simp)]
-/
theorem biprod.desc_eq {T : C} {f : X ⟶ T} {g : Y ⟶ T} :
    biprod.desc f g = biprod.fst ≫ f + biprod.snd ≫ g := by ext <;> simp

@[reassoc (attr := simp)]
/--
theorem `biprod.lift_desc` / 定理 `biprod.lift_desc`

English:
theorem biprod.lift_desc
  given: {T U : C} {f : T ⟶ X} {g : T ⟶ Y} {h : X ⟶ U} {i : Y ⟶ U}
  proof: by simp [biprod.lift_eq, biprod.desc_eq]

中文:
定理 biprod.lift_desc
  条件: {T U : C} {f : T ⟶ X} {g : T ⟶ Y} {h : X ⟶ U} {i : Y ⟶ U}
  证明: by simp [biprod.lift_eq, biprod.desc_eq]

Depends on / 依赖: biprod, biprod.desc_eq, biprod.lift_eq, desc_eq, lift_eq
-/
theorem biprod.lift_desc {T U : C} {f : T ⟶ X} {g : T ⟶ Y} {h : X ⟶ U} {i : Y ⟶ U} :
    biprod.lift f g ≫ biprod.desc h i = f ≫ h + g ≫ i := by simp [biprod.lift_eq, biprod.desc_eq]

/--
theorem `biprod.map_eq` / 定理 `biprod.map_eq`

English:
theorem biprod.map_eq
  given: [HasBinaryBiproducts C] {W X Y Z : C} {f : W ⟶ Y} {g : X ⟶ Z}
  proof: by
  ext <;> simp

中文:
定理 biprod.map_eq
  条件: [有BinaryBiproducts C] {W X Y Z : C} {f : W ⟶ Y} {g : X ⟶ Z}
  证明: by
  ext <;> simp
-/
theorem biprod.map_eq [HasBinaryBiproducts C] {W X Y Z : C} {f : W ⟶ Y} {g : X ⟶ Z} :
    biprod.map f g = biprod.fst ≫ f ≫ biprod.inl + biprod.snd ≫ g ≫ biprod.inr := by
  ext <;> simp

section

variable {Z : C}

/--
lemma `biprod.decomp_hom_to` / 引理 `biprod.decomp_hom_to`

English:
lemma biprod.decomp_hom_to
  given: (f : Z ⟶ X ⊞ Y)
  proof: ⟨f ≫ biprod.fst, f ≫ biprod.snd, by aesop⟩

中文:
引理 biprod.decomp_hom_to
  条件: (f : Z ⟶ X ⊞ Y)
  证明: ⟨f ≫ biprod.fst, f ≫ biprod.snd, by aesop⟩

Depends on / 依赖: biprod, biprod.fst, biprod.snd
-/
lemma biprod.decomp_hom_to (f : Z ⟶ X ⊞ Y) :
    exists f₁ f₂, f = f₁ ≫ biprod.inl + f₂ ≫ biprod.inr :=
  ⟨f ≫ biprod.fst, f ≫ biprod.snd, by aesop⟩

/--
lemma `biprod.ext_to_iff` / 引理 `biprod.ext_to_iff`

English:
lemma biprod.ext_to_iff
  given: {f g : Z ⟶ X ⊞ Y}
  proof: by
  aesop

中文:
引理 biprod.ext_to_iff
  条件: {f g : Z ⟶ X ⊞ Y}
  证明: by
  aesop
-/
lemma biprod.ext_to_iff {f g : Z ⟶ X ⊞ Y} :
    f = g ↔ f ≫ biprod.fst = g ≫ biprod.fst ∧ f ≫ biprod.snd = g ≫ biprod.snd := by
  aesop

/--
lemma `biprod.decomp_hom_from` / 引理 `biprod.decomp_hom_from`

English:
lemma biprod.decomp_hom_from
  given: (f : X ⊞ Y ⟶ Z)
  proof: ⟨biprod.inl ≫ f, biprod.inr ≫ f, by aesop⟩

中文:
引理 biprod.decomp_hom_from
  条件: (f : X ⊞ Y ⟶ Z)
  证明: ⟨biprod.inl ≫ f, biprod.inr ≫ f, by aesop⟩

Depends on / 依赖: biprod, biprod.inl, biprod.inr
-/
lemma biprod.decomp_hom_from (f : X ⊞ Y ⟶ Z) :
    exists f₁ f₂, f = biprod.fst ≫ f₁ + biprod.snd ≫ f₂ :=
  ⟨biprod.inl ≫ f, biprod.inr ≫ f, by aesop⟩

/--
lemma `biprod.ext_from_iff` / 引理 `biprod.ext_from_iff`

English:
lemma biprod.ext_from_iff
  given: {f g : X ⊞ Y ⟶ Z}
  proof: by
  aesop

中文:
引理 biprod.ext_from_iff
  条件: {f g : X ⊞ Y ⟶ Z}
  证明: by
  aesop
-/
lemma biprod.ext_from_iff {f g : X ⊞ Y ⟶ Z} :
    f = g ↔ biprod.inl ≫ f = biprod.inl ≫ g ∧ biprod.inr ≫ f = biprod.inr ≫ g := by
  aesop

end

set_option backward.isDefEq.respectTransparency false in
/-- Every split mono `f` with a cokernel induces a binary bicone with `f` as its `inl` and
the cokernel map as its `snd`.
We will show in `isBilimitBinaryBiconeOfIsSplitMonoOfCokernel` that this binary bicone is in
fact already a biproduct. -/
@[simps]
/--
Definition of `binaryBiconeOfIsSplitMonoOfCokernel` / `binaryBiconeOfIsSplitMonoOfCokernel` 的定义

English:
definition binaryBiconeOfIsSplitMonoOfCokernel
  signature: {X Y : C} {f : X ⟶ Y} [IsSplitMono f] {c : CokernelCofork f}
  body: Y
  fst := retraction f
  snd := c.π
  inl := f
  inr :=
    let c' : CokernelCofork (𝟙 Y - (𝟙 Y - retraction f ≫ f)) :=
      CokernelCofork.ofπ (Cofork.π c) (by simp)
    let i' : IsColimit c' := isCokernelEpiComp i (retraction f) (by simp)
    let i'' := isColimitCoforkOfCokernelCofork i'
    (sp

中文:
定义 binaryBiconeOfIsSplitMonoOfCokernel
  签名: {X Y : C} {f : X ⟶ Y} [是分裂单态射 f] {c : 余核余叉 f}
  定义体: Y
  fst := retraction f
  snd := c.π
  inl := f
  inr :=
    let c' : CokernelCofork (𝟙 Y - (𝟙 Y - retraction f ≫ f)) :=
      CokernelCofork.ofπ (Cofork.π c) (by simp)
    let i' : IsColimit c' := isCokernelEpiComp i (retraction f) (by simp)
    let i'' := isColimitCoforkOfCokernelCofork i'
    (sp
-/
def binaryBiconeOfIsSplitMonoOfCokernel {X Y : C} {f : X ⟶ Y} [IsSplitMono f] {c : CokernelCofork f}
    (i : IsColimit c) : BinaryBicone X c.pt where
  pt := Y
  fst := retraction f
  snd := c.π
  inl := f
  inr :=
    let c' : CokernelCofork (𝟙 Y - (𝟙 Y - retraction f ≫ f)) :=
      CokernelCofork.ofπ (Cofork.π c) (by simp)
    let i' : IsColimit c' := isCokernelEpiComp i (retraction f) (by simp)
    let i'' := isColimitCoforkOfCokernelCofork i'
    (splitEpiOfIdempotentOfIsColimitCofork C (by simp) i'').section_
  inl_fst := by simp
  inl_snd := by simp
  inr_fst := by
    dsimp only
    rw [splitEpiOfIdempotentOfIsColimitCofork_section_]; rw [isColimitCoforkOfCokernelCofork_desc]; rw [isCokernelEpiComp_desc]
    dsimp only [cokernelCoforkOfCofork_ofπ]
    let := epi_of_isColimit_cofork i
    apply zero_of_epi_comp c.π
    simp only [sub_comp, comp_sub, Category.comp_id, Category.assoc, IsSplitMono.id, sub_self,
      Cofork.IsColimit.π_desc_assoc, CokernelCofork.π_ofπ, IsSplitMono.id_assoc]
    apply sub_eq_zero_of_eq
    apply Category.id_comp
  inr_snd := by apply SplitEpi.id

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isBilimitBinaryBiconeOfIsSplitMonoOfCokernel` / `isBilimitBinaryBiconeOfIsSplitMonoOfCokernel` 的定义

English:
definition isBilimitBinaryBiconeOfIsSplitMonoOfCokernel
  signature: {X Y : C} {f : X ⟶ Y} [IsSplitMono f]
  body: isBinaryBilimitOfTotal _
    (by
      simp only [binaryBiconeOfIsSplitMonoOfCokernel_fst,
        binaryBiconeOfIsSplitMonoOfCokernel_inr,
        binaryBiconeOfIsSplitMonoOfCokernel_snd,
        splitEpiOfIdempotentOfIsColimitCofork_section_]
      dsimp only [binaryBiconeOfIsSplitMonoOfCokernel_p

中文:
定义 isBilimitBinaryBiconeOfIsSplitMonoOfCokernel
  签名: {X Y : C} {f : X ⟶ Y} [是分裂单态射 f]
  定义体: isBinaryBilimitOfTotal _
    (by
      simp only [binaryBiconeOfIsSplitMonoOfCokernel_fst,
        binaryBiconeOfIsSplitMonoOfCokernel_inr,
        binaryBiconeOfIsSplitMonoOfCokernel_snd,
        splitEpiOfIdempotentOfIsColimitCofork_section_]
      dsimp only [binaryBiconeOfIsSplitMonoOfCokernel_p

Depends on / 依赖: Cofork, Cofork.IsColimit, IsColimit, add_sub_cancel, binaryBiconeOfIsSplitMonoOfCokernel_fst, binaryBiconeOfIsSplitMonoOfCokernel_inl, binaryBiconeOfIsSplitMonoOfCokernel_inr, binaryBiconeOfIsSplitMonoOfCokernel_pt, binaryBiconeOfIsSplitMonoOfCokernel_snd, isBinaryBilimitOfTotal, isCokernelEpiComp_desc, isColimitCoforkOfCokernelCofork_desc, splitEpiOfIdempotentOfIsColimitCofork_section_
-/
def isBilimitBinaryBiconeOfIsSplitMonoOfCokernel {X Y : C} {f : X ⟶ Y} [IsSplitMono f]
    {c : CokernelCofork f} (i : IsColimit c) : (binaryBiconeOfIsSplitMonoOfCokernel i).IsBilimit :=
  isBinaryBilimitOfTotal _
    (by
      simp only [binaryBiconeOfIsSplitMonoOfCokernel_fst,
        binaryBiconeOfIsSplitMonoOfCokernel_inr,
        binaryBiconeOfIsSplitMonoOfCokernel_snd,
        splitEpiOfIdempotentOfIsColimitCofork_section_]
      dsimp only [binaryBiconeOfIsSplitMonoOfCokernel_pt]
      rw [isColimitCoforkOfCokernelCofork_desc]; rw [isCokernelEpiComp_desc]
      simp only [binaryBiconeOfIsSplitMonoOfCokernel_inl, Cofork.IsColimit.π_desc,
        cokernelCoforkOfCofork_π, Cofork.π_ofπ, add_sub_cancel])

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `BinaryBicone.isBilimitOfKernelInl` / `BinaryBicone.isBilimitOfKernelInl` 的定义

English:
definition BinaryBicone.isBilimitOfKernelInl
  signature: {X Y : C} (b : BinaryBicone X Y)
  body: isBinaryBilimitOfIsLimit _
    BinaryFan.IsLimit.mk _ (fun f g => f ≫ b.inl + g ≫ b.inr) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : ((m : T ⟶ b.pt) - (f ≫ b.inl + g ≫ b.inr)) ≫ b.fst = 0 := by
        simpa using sub_eq_zero.2 h₁
     

中文:
定义 BinaryBicone.isBilimitOfKernelInl
  签名: {X Y : C} (b : BinaryBicone X Y)
  定义体: isBinaryBilimitOfIsLimit _
    BinaryFan.IsLimit.mk _ (fun f g => f ≫ b.inl + g ≫ b.inr) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : ((m : T ⟶ b.pt) - (f ≫ b.inl + g ≫ b.inr)) ≫ b.fst = 0 := by
        simpa using sub_eq_zero.2 h₁
     

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.mk, Category, IsLimit, KernelFork, KernelFork.IsLimit.lift, b.fst, b.inl, b.inr, b.pt, b.snd, isBinaryBilimitOfIsLimit, sub_eq_zero
-/
def BinaryBicone.isBilimitOfKernelInl {X Y : C} (b : BinaryBicone X Y)
    (hb : IsLimit b.sndKernelFork) : b.IsBilimit :=
isBinaryBilimitOfIsLimit _
    BinaryFan.IsLimit.mk _ (fun f g => f ≫ b.inl + g ≫ b.inr) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : ((m : T ⟶ b.pt) - (f ≫ b.inl + g ≫ b.inr)) ≫ b.fst = 0 := by
        simpa using sub_eq_zero.2 h₁
      have h₂' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.snd = 0 := by simpa using sub_eq_zero.2 h₂
      obtain ⟨q : T ⟶ X, hq : q ≫ b.inl = m - (f ≫ b.inl + g ≫ b.inr)⟩ :=
        KernelFork.IsLimit.lift' hb _ h₂'
      rw [← sub_eq_zero]; rw [← hq]; rw [← Category.comp_id q]; rw [← b.inl_fst]; rw [← Category.assoc]; rw [hq]; rw [h₁']; rw [zero_comp]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `BinaryBicone.isBilimitOfKernelInr` / `BinaryBicone.isBilimitOfKernelInr` 的定义

English:
definition BinaryBicone.isBilimitOfKernelInr
  signature: {X Y : C} (b : BinaryBicone X Y)
  body: isBinaryBilimitOfIsLimit _
    BinaryFan.IsLimit.mk _ (fun f g => f ≫ b.inl + g ≫ b.inr) (fun f g => by simp)
    (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.fst = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : (m - (f ≫ b

中文:
定义 BinaryBicone.isBilimitOfKernelInr
  签名: {X Y : C} (b : BinaryBicone X Y)
  定义体: isBinaryBilimitOfIsLimit _
    BinaryFan.IsLimit.mk _ (fun f g => f ≫ b.inl + g ≫ b.inr) (fun f g => by simp)
    (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.fst = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : (m - (f ≫ b

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.mk, Category, Category.comp_id, IsLimit, KernelFork, KernelFork.IsLimit.lift, b.fst, b.inl, b.inr, b.snd, comp_id, isBinaryBilimitOfIsLimit, sub_eq_zero
-/
def BinaryBicone.isBilimitOfKernelInr {X Y : C} (b : BinaryBicone X Y)
    (hb : IsLimit b.fstKernelFork) : b.IsBilimit :=
isBinaryBilimitOfIsLimit _
    BinaryFan.IsLimit.mk _ (fun f g => f ≫ b.inl + g ≫ b.inr) (fun f g => by simp)
    (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.fst = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.snd = 0 := by simpa using sub_eq_zero.2 h₂
      obtain ⟨q : T ⟶ Y, hq : q ≫ b.inr = m - (f ≫ b.inl + g ≫ b.inr)⟩ :=
        KernelFork.IsLimit.lift' hb _ h₁'
      rw [← sub_eq_zero]; rw [← hq]; rw [← Category.comp_id q]; rw [← b.inr_snd]; rw [← Category.assoc]; rw [hq]; rw [h₂']; rw [zero_comp]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `BinaryBicone.isBilimitOfCokernelFst` / `BinaryBicone.isBilimitOfCokernelFst` 的定义

English:
definition BinaryBicone.isBilimitOfCokernelFst
  signature: {X Y : C} (b : BinaryBicone X Y)
  body: isBinaryBilimitOfIsColimit _
    BinaryCofan.IsColimit.mk _ (fun f g => b.fst ≫ f + b.snd ≫ g) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : b.inl ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : b.i

中文:
定义 BinaryBicone.isBilimitOfCokernelFst
  签名: {X Y : C} (b : BinaryBicone X Y)
  定义体: isBinaryBilimitOfIsColimit _
    BinaryCofan.IsColimit.mk _ (fun f g => b.fst ≫ f + b.snd ≫ g) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : b.inl ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : b.i

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.mk, Category, CokernelCofork, CokernelCofork.IsColimit.desc, IsColimit, b.fst, b.inl, b.inr, b.snd, isBinaryBilimitOfIsColimit, sub_eq_zero
-/
def BinaryBicone.isBilimitOfCokernelFst {X Y : C} (b : BinaryBicone X Y)
    (hb : IsColimit b.inrCokernelCofork) : b.IsBilimit :=
isBinaryBilimitOfIsColimit _
    BinaryCofan.IsColimit.mk _ (fun f g => b.fst ≫ f + b.snd ≫ g) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : b.inl ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : b.inr ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₂
      obtain ⟨q : X ⟶ T, hq : b.fst ≫ q = m - (b.fst ≫ f + b.snd ≫ g)⟩ :=
        CokernelCofork.IsColimit.desc' hb _ h₂'
      rw [← sub_eq_zero]; rw [← hq]; rw [← Category.id_comp q]; rw [← b.inl_fst]; rw [Category.assoc]; rw [hq]; rw [h₁']; rw [comp_zero]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `BinaryBicone.isBilimitOfCokernelSnd` / `BinaryBicone.isBilimitOfCokernelSnd` 的定义

English:
definition BinaryBicone.isBilimitOfCokernelSnd
  signature: {X Y : C} (b : BinaryBicone X Y)
  body: isBinaryBilimitOfIsColimit _
    BinaryCofan.IsColimit.mk _ (fun f g => b.fst ≫ f + b.snd ≫ g) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : b.inl ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : b.i

中文:
定义 BinaryBicone.isBilimitOfCokernelSnd
  签名: {X Y : C} (b : BinaryBicone X Y)
  定义体: isBinaryBilimitOfIsColimit _
    BinaryCofan.IsColimit.mk _ (fun f g => b.fst ≫ f + b.snd ≫ g) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : b.inl ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : b.i

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.mk, Category, CokernelCofork, CokernelCofork.IsColimit.desc, IsColimit, b.fst, b.inl, b.inr, b.snd, isBinaryBilimitOfIsColimit, sub_eq_zero
-/
def BinaryBicone.isBilimitOfCokernelSnd {X Y : C} (b : BinaryBicone X Y)
    (hb : IsColimit b.inlCokernelCofork) : b.IsBilimit :=
isBinaryBilimitOfIsColimit _
    BinaryCofan.IsColimit.mk _ (fun f g => b.fst ≫ f + b.snd ≫ g) (fun f g => by simp)
      (fun f g => by simp) fun {T} f g m h₁ h₂ => by
      dsimp at m
      have h₁' : b.inl ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₁
      have h₂' : b.inr ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₂
      obtain ⟨q : Y ⟶ T, hq : b.snd ≫ q = m - (b.fst ≫ f + b.snd ≫ g)⟩ :=
        CokernelCofork.IsColimit.desc' hb _ h₁'
      rw [← sub_eq_zero]; rw [← hq]; rw [← Category.id_comp q]; rw [← b.inr_snd]; rw [Category.assoc]; rw [hq]; rw [h₂']; rw [comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Every split epi `f` with a kernel induces a binary bicone with `f` as its `snd` and
the kernel map as its `inl`.
We will show in `isBilimitBinaryBiconeOfIsSplitEpiOfKernel` that this binary bicone is in fact
already a biproduct. -/
@[simps]
/--
Definition of `binaryBiconeOfIsSplitEpiOfKernel` / `binaryBiconeOfIsSplitEpiOfKernel` 的定义

English:
definition binaryBiconeOfIsSplitEpiOfKernel
  signature: {X Y : C} {f : X ⟶ Y} [IsSplitEpi f] {c : KernelFork f}
  body: { pt := X
    fst :=
      let c' : KernelFork (𝟙 X - (𝟙 X - f ≫ section_ f)) := KernelFork.ofι (Fork.ι c) (by simp)
      let i' : IsLimit c' := isKernelCompMono i (section_ f) (by simp)
      let i'' := isLimitForkOfKernelFork i'
      (splitMonoOfIdempotentOfIsLimitFork C (by simp) i'').retractio

中文:
定义 binaryBiconeOfIsSplitEpiOfKernel
  签名: {X Y : C} {f : X ⟶ Y} [是分裂满态射 f] {c : 核叉 f}
  定义体: { pt := X
    fst :=
      let c' : KernelFork (𝟙 X - (𝟙 X - f ≫ section_ f)) := KernelFork.ofι (Fork.ι c) (by simp)
      let i' : IsLimit c' := isKernelCompMono i (section_ f) (by simp)
      let i'' := isLimitForkOfKernelFork i'
      (splitMonoOfIdempotentOfIsLimitFork C (by simp) i'').retractio

Depends on / 依赖: IsLimit, KernelFork, KernelFork.of, SplitMono, SplitMono.id, inl_fst, inl_snd, inr_fst, isKernelCompMono, isKernelCompMono_lif, isLimitForkOfKernelFork, isLimitForkOfKernelFork_lift, retraction, section_, splitMonoOfIdempotentOfIsLimitFork, splitMonoOfIdempotentOfIsLimitFork_retraction
-/
def binaryBiconeOfIsSplitEpiOfKernel {X Y : C} {f : X ⟶ Y} [IsSplitEpi f] {c : KernelFork f}
    (i : IsLimit c) : BinaryBicone c.pt Y :=
  { pt := X
    fst :=
      let c' : KernelFork (𝟙 X - (𝟙 X - f ≫ section_ f)) := KernelFork.ofι (Fork.ι c) (by simp)
      let i' : IsLimit c' := isKernelCompMono i (section_ f) (by simp)
      let i'' := isLimitForkOfKernelFork i'
      (splitMonoOfIdempotentOfIsLimitFork C (by simp) i'').retraction
    snd := f
    inl := c.ι
    inr := section_ f
    inl_fst := by apply SplitMono.id
    inl_snd := by simp
    inr_fst := by
      dsimp only
      rw [splitMonoOfIdempotentOfIsLimitFork_retraction]; rw [isLimitForkOfKernelFork_lift]; rw [isKernelCompMono_lift]
      dsimp only [kernelForkOfFork_ι]
      let := mono_of_isLimit_fork i
      apply zero_of_comp_mono c.ι
      simp only [comp_sub, Category.comp_id, Category.assoc, sub_self, Fork.IsLimit.lift_ι,
        Fork.ι_ofι, IsSplitEpi.id_assoc]
    inr_snd := by simp }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isBilimitBinaryBiconeOfIsSplitEpiOfKernel` / `isBilimitBinaryBiconeOfIsSplitEpiOfKernel` 的定义

English:
definition isBilimitBinaryBiconeOfIsSplitEpiOfKernel
  signature: {X Y : C} {f : X ⟶ Y} [IsSplitEpi f]
  body: BinaryBicone.isBilimitOfKernelInl _ i.ofIsoLimit Fork.ext (Iso.refl _) (by simp)

中文:
定义 isBilimitBinaryBiconeOfIsSplitEpiOfKernel
  签名: {X Y : C} {f : X ⟶ Y} [是分裂满态射 f]
  定义体: BinaryBicone.isBilimitOfKernelInl _ i.ofIsoLimit Fork.ext (Iso.refl _) (by simp)

Depends on / 依赖: BinaryBicone, BinaryBicone.isBilimitOfKernelInl, Fork.ext, Iso.refl, i.ofIsoLimit, isBilimitOfKernelInl, ofIsoLimit
-/
def isBilimitBinaryBiconeOfIsSplitEpiOfKernel {X Y : C} {f : X ⟶ Y} [IsSplitEpi f]
    {c : KernelFork f} (i : IsLimit c) : (binaryBiconeOfIsSplitEpiOfKernel i).IsBilimit :=
BinaryBicone.isBilimitOfKernelInl _ i.ofIsoLimit Fork.ext (Iso.refl _) (by simp)

end

section

variable {X Y : C} (f g : X ⟶ Y)

/--
theorem `biprod.add_eq_lift_id_desc` / 定理 `biprod.add_eq_lift_id_desc`

English:
theorem biprod.add_eq_lift_id_desc
  given: [HasBinaryBiproduct X X]
  proof: by simp

中文:
定理 biprod.add_eq_lift_id_desc
  条件: [有BinaryBiproduct X X]
  证明: by simp
-/
theorem biprod.add_eq_lift_id_desc [HasBinaryBiproduct X X] :
    f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g := by simp

/--
theorem `biprod.add_eq_lift_desc_id` / 定理 `biprod.add_eq_lift_desc_id`

English:
theorem biprod.add_eq_lift_desc_id
  given: [HasBinaryBiproduct Y Y]
  proof: by simp

中文:
定理 biprod.add_eq_lift_desc_id
  条件: [有BinaryBiproduct Y Y]
  证明: by simp
-/
theorem biprod.add_eq_lift_desc_id [HasBinaryBiproduct Y Y] :
    f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y) := by simp

end

end Limits

open CategoryTheory.Limits

section

attribute [local ext] Preadditive

/--
Instance `subsingleton_preadditive_of_hasBinaryBiproducts` / 实例 `subsingleton_preadditive_of_hasBinaryBiproducts`

English:
instance subsingleton_preadditive_of_hasBinaryBiproducts
  signature: {C : Type u} [Category.{v} C]
  body: fun a b => by
    apply Preadditive.ext; funext X Y; apply AddCommGroup.ext; funext f g
    have h₁ := @biprod.add_eq_lift_id_desc _ _ a _ _ f g
      (by convert! (inferInstance : HasBinaryBiproduct X X); subsingleton)
    have h₂ := @biprod.add_eq_lift_id_desc _ _ b _ _ f g
      (by convert! (inf

中文:
实例 subsingleton_preadditive_of_hasBinaryBiproducts
  签名: {C : 类型u} [范畴.{v} C]
  定义体: fun a b => by
    apply Preadditive.ext; funext X Y; apply AddCommGroup.ext; funext f g
    have h₁ := @biprod.add_eq_lift_id_desc _ _ a _ _ f g
      (by convert! (inferInstance : HasBinaryBiproduct X X); subsingleton)
    have h₂ := @biprod.add_eq_lift_id_desc _ _ b _ _ f g
      (by convert! (inf

Depends on / 依赖: AddCommGroup, AddCommGroup.ext, Eq.trans, HasBinaryBiproduct, Preadditive, Preadditive.ext, add_eq_lift_id_desc, biprod, biprod.add_eq_lift_id_desc, convert, subsingleton
-/
instance subsingleton_preadditive_of_hasBinaryBiproducts {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] [HasBinaryBiproducts C] : Subsingleton (Preadditive C) where
  allEq := fun a b => by
    apply Preadditive.ext; funext X Y; apply AddCommGroup.ext; funext f g
    have h₁ := @biprod.add_eq_lift_id_desc _ _ a _ _ f g
      (by convert! (inferInstance : HasBinaryBiproduct X X); subsingleton)
    have h₂ := @biprod.add_eq_lift_id_desc _ _ b _ _ f g
      (by convert! (inferInstance : HasBinaryBiproduct X X); subsingleton)
    refine h₁.trans (Eq.trans ?_ h₂.symm)
    congr! 2 <;> subsingleton

end

section

variable [HasBinaryBiproducts.{v} C]
variable {X₁ X₂ Y₁ Y₂ : C}
variable (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂)

/--
Definition of `Biprod.ofComponents` / `Biprod.ofComponents` 的定义

English:
definition Biprod.ofComponents
  signature: : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂
  body: biprod.fst ≫ f₁₁ ≫ biprod.inl + biprod.fst ≫ f₁₂ ≫ biprod.inr + biprod.snd ≫ f₂₁ ≫ biprod.inl +
    biprod.snd ≫ f₂₂ ≫ biprod.inr

@[simp]

中文:
定义 Biprod.ofComponents
  签名: : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂
  定义体: biprod.fst ≫ f₁₁ ≫ biprod.inl + biprod.fst ≫ f₁₂ ≫ biprod.inr + biprod.snd ≫ f₂₁ ≫ biprod.inl +
    biprod.snd ≫ f₂₂ ≫ biprod.inr

@[simp]

Depends on / 依赖: biprod, biprod.fst, biprod.inl, biprod.inr, biprod.snd
-/
def Biprod.ofComponents : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂ :=
  biprod.fst ≫ f₁₁ ≫ biprod.inl + biprod.fst ≫ f₁₂ ≫ biprod.inr + biprod.snd ≫ f₂₁ ≫ biprod.inl +
    biprod.snd ≫ f₂₂ ≫ biprod.inr

@[simp]
/--
theorem `Biprod.inl_ofComponents` / 定理 `Biprod.inl_ofComponents`

English:
theorem Biprod.inl_ofComponents
  proof: by
  simp [Biprod.ofComponents]

@[simp]

中文:
定理 Biprod.inl_ofComponents
  证明: by
  simp [Biprod.ofComponents]

@[simp]

Depends on / 依赖: Biprod, Biprod.ofComponents, ofComponents
-/
theorem Biprod.inl_ofComponents :
    biprod.inl ≫ Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ = f₁₁ ≫ biprod.inl + f₁₂ ≫ biprod.inr := by
  simp [Biprod.ofComponents]

@[simp]
/--
theorem `Biprod.inr_ofComponents` / 定理 `Biprod.inr_ofComponents`

English:
theorem Biprod.inr_ofComponents
  proof: by
  simp [Biprod.ofComponents]

@[simp]

中文:
定理 Biprod.inr_ofComponents
  证明: by
  simp [Biprod.ofComponents]

@[simp]

Depends on / 依赖: Biprod, Biprod.ofComponents, ofComponents
-/
theorem Biprod.inr_ofComponents :
    biprod.inr ≫ Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ = f₂₁ ≫ biprod.inl + f₂₂ ≫ biprod.inr := by
  simp [Biprod.ofComponents]

@[simp]
/--
theorem `Biprod.ofComponents_fst` / 定理 `Biprod.ofComponents_fst`

English:
theorem Biprod.ofComponents_fst
  proof: by
  simp [Biprod.ofComponents]

@[simp]

中文:
定理 Biprod.ofComponents_fst
  证明: by
  simp [Biprod.ofComponents]

@[simp]

Depends on / 依赖: Biprod, Biprod.ofComponents, ofComponents
-/
theorem Biprod.ofComponents_fst :
    Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.fst = biprod.fst ≫ f₁₁ + biprod.snd ≫ f₂₁ := by
  simp [Biprod.ofComponents]

@[simp]
/--
theorem `Biprod.ofComponents_snd` / 定理 `Biprod.ofComponents_snd`

English:
theorem Biprod.ofComponents_snd
  proof: by
  simp [Biprod.ofComponents]

@[simp]

中文:
定理 Biprod.ofComponents_snd
  证明: by
  simp [Biprod.ofComponents]

@[simp]

Depends on / 依赖: Biprod, Biprod.ofComponents, ofComponents
-/
theorem Biprod.ofComponents_snd :
    Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.snd = biprod.fst ≫ f₁₂ + biprod.snd ≫ f₂₂ := by
  simp [Biprod.ofComponents]

@[simp]
/--
theorem `Biprod.ofComponents_eq` / 定理 `Biprod.ofComponents_eq`

English:
theorem Biprod.ofComponents_eq
  given: (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂)
  proof: by
  ext <;>
    simp only [Category.comp_id, biprod.inr_fst, biprod.inr_snd, biprod.inl_snd, add_zero, zero_add,
      Biprod.inl_ofComponents, Biprod.inr_ofComponents, Category.assoc,
      comp_zero, biprod.inl_fst, Preadditive.add_comp]

@[simp]

中文:
定理 Biprod.ofComponents_eq
  条件: (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂)
  证明: by
  ext <;>
    simp only [Category.comp_id, biprod.inr_fst, biprod.inr_snd, biprod.inl_snd, add_zero, zero_add,
      Biprod.inl_ofComponents, Biprod.inr_ofComponents, Category.assoc,
      comp_zero, biprod.inl_fst, Preadditive.add_comp]

@[simp]

Depends on / 依赖: Biprod, Biprod.inl_ofComponents, Biprod.inr_ofComponents, Category, Category.assoc, Category.comp_id, Preadditive, Preadditive.add_comp, add_comp, add_zero, biprod, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd, comp_id, comp_zero, inl_fst, inl_ofComponents, inl_snd
-/
theorem Biprod.ofComponents_eq (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) :
    Biprod.ofComponents (biprod.inl ≫ f ≫ biprod.fst) (biprod.inl ≫ f ≫ biprod.snd)
        (biprod.inr ≫ f ≫ biprod.fst) (biprod.inr ≫ f ≫ biprod.snd) =
      f := by
  ext <;>
    simp only [Category.comp_id, biprod.inr_fst, biprod.inr_snd, biprod.inl_snd, add_zero, zero_add,
      Biprod.inl_ofComponents, Biprod.inr_ofComponents, Category.assoc,
      comp_zero, biprod.inl_fst, Preadditive.add_comp]

@[simp]
/--
theorem `Biprod.ofComponents_comp` / 定理 `Biprod.ofComponents_comp`

English:
theorem Biprod.ofComponents_comp
  statement: {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂)
  proof: by
  dsimp [Biprod.ofComponents]
  ext <;>
    simp only [add_comp, comp_add, add_zero, zero_add, biprod.inl_fst,
      biprod.inl_snd, biprod.inr_fst, biprod.inr_snd, biprod.inl_fst_assoc, biprod.inl_snd_assoc,
      biprod.inr_fst_assoc, biprod.inr_snd_assoc, comp_zero, zero_comp, Category.assoc]

中文:
定理 Biprod.ofComponents_comp
  结论: {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂)
  证明: by
  dsimp [Biprod.ofComponents]
  ext <;>
    simp only [add_comp, comp_add, add_zero, zero_add, biprod.inl_fst,
      biprod.inl_snd, biprod.inr_fst, biprod.inr_snd, biprod.inl_fst_assoc, biprod.inl_snd_assoc,
      biprod.inr_fst_assoc, biprod.inr_snd_assoc, comp_zero, zero_comp, Category.assoc]

Depends on / 依赖: Biprod, Biprod.ofComponents, Category, Category.assoc, add_comp, add_zero, biprod, biprod.inl_fst, biprod.inl_fst_assoc, biprod.inl_snd, biprod.inl_snd_assoc, biprod.inr_fst, biprod.inr_fst_assoc, biprod.inr_snd, biprod.inr_snd_assoc, comp_add, comp_zero, inl_fst, inl_fst_assoc, inl_snd
-/
theorem Biprod.ofComponents_comp {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂)
    (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) (g₁₁ : Y₁ ⟶ Z₁) (g₁₂ : Y₁ ⟶ Z₂) (g₂₁ : Y₂ ⟶ Z₁)
    (g₂₂ : Y₂ ⟶ Z₂) :
    Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ Biprod.ofComponents g₁₁ g₁₂ g₂₁ g₂₂ =
      Biprod.ofComponents (f₁₁ ≫ g₁₁ + f₁₂ ≫ g₂₁) (f₁₁ ≫ g₁₂ + f₁₂ ≫ g₂₂) (f₂₁ ≫ g₁₁ + f₂₂ ≫ g₂₁)
        (f₂₁ ≫ g₁₂ + f₂₂ ≫ g₂₂) := by
  dsimp [Biprod.ofComponents]
  ext <;>
    simp only [add_comp, comp_add, add_zero, zero_add, biprod.inl_fst,
      biprod.inl_snd, biprod.inr_fst, biprod.inr_snd, biprod.inl_fst_assoc, biprod.inl_snd_assoc,
      biprod.inr_fst_assoc, biprod.inr_snd_assoc, comp_zero, zero_comp, Category.assoc]

/-- The unipotent upper triangular matrix
```
(1 r)
(0 1)
```
as an isomorphism.
-/
@[simps]
/--
Definition of `Biprod.unipotentUpper` / `Biprod.unipotentUpper` 的定义

English:
definition Biprod.unipotentUpper
  signature: {X₁ X₂ : C} (r : X₁ ⟶ X₂)
  body: Biprod.ofComponents (𝟙 _) r 0 (𝟙 _)
  inv := Biprod.ofComponents (𝟙 _) (-r) 0 (𝟙 _)

中文:
定义 Biprod.unipotentUpper
  签名: {X₁ X₂ : C} (r : X₁ ⟶ X₂)
  定义体: Biprod.ofComponents (𝟙 _) r 0 (𝟙 _)
  inv := Biprod.ofComponents (𝟙 _) (-r) 0 (𝟙 _)

Depends on / 依赖: Biprod, Biprod.ofComponents, ofComponents
-/
def Biprod.unipotentUpper {X₁ X₂ : C} (r : X₁ ⟶ X₂) : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ where
  hom := Biprod.ofComponents (𝟙 _) r 0 (𝟙 _)
  inv := Biprod.ofComponents (𝟙 _) (-r) 0 (𝟙 _)

/-- The unipotent lower triangular matrix
```
(1 0)
(r 1)
```
as an isomorphism.
-/
@[simps]
/--
Definition of `Biprod.unipotentLower` / `Biprod.unipotentLower` 的定义

English:
definition Biprod.unipotentLower
  signature: {X₁ X₂ : C} (r : X₂ ⟶ X₁)
  body: Biprod.ofComponents (𝟙 _) 0 r (𝟙 _)
  inv := Biprod.ofComponents (𝟙 _) 0 (-r) (𝟙 _)

中文:
定义 Biprod.unipotentLower
  签名: {X₁ X₂ : C} (r : X₂ ⟶ X₁)
  定义体: Biprod.ofComponents (𝟙 _) 0 r (𝟙 _)
  inv := Biprod.ofComponents (𝟙 _) 0 (-r) (𝟙 _)

Depends on / 依赖: Biprod, Biprod.ofComponents, ofComponents
-/
def Biprod.unipotentLower {X₁ X₂ : C} (r : X₂ ⟶ X₁) : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ where
  hom := Biprod.ofComponents (𝟙 _) 0 r (𝟙 _)
  inv := Biprod.ofComponents (𝟙 _) 0 (-r) (𝟙 _)

/--
Definition of `Biprod.gaussian'` / `Biprod.gaussian'` 的定义

English:
definition Biprod.gaussian'
  signature: [IsIso f₁₁]
  body: ⟨Biprod.unipotentLower (-f₂₁ ≫ inv f₁₁), Biprod.unipotentUpper (-inv f₁₁ ≫ f₁₂),
    f₂₂ - f₂₁ ≫ inv f₁₁ ≫ f₁₂, by ext <;> simp; abel⟩

中文:
定义 Biprod.gaussian'
  签名: [是同构 f₁₁]
  定义体: ⟨Biprod.unipotentLower (-f₂₁ ≫ inv f₁₁), Biprod.unipotentUpper (-inv f₁₁ ≫ f₁₂),
    f₂₂ - f₂₁ ≫ inv f₁₁ ≫ f₁₂, by ext <;> simp; abel⟩

Depends on / 依赖: Biprod, Biprod.unipotentLower, Biprod.unipotentUpper, unipotentLower, unipotentUpper
-/
def Biprod.gaussian' [IsIso f₁₁] :
    Σ' (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) (g₂₂ : X₂ ⟶ Y₂),
      L.hom ≫ Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ R.hom = biprod.map f₁₁ g₂₂ :=
  ⟨Biprod.unipotentLower (-f₂₁ ≫ inv f₁₁), Biprod.unipotentUpper (-inv f₁₁ ≫ f₁₂),
    f₂₂ - f₂₁ ≫ inv f₁₁ ≫ f₁₂, by ext <;> simp; abel⟩

/--
Definition of `Biprod.gaussian` / `Biprod.gaussian` 的定义

English:
definition Biprod.gaussian
  signature: (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) [IsIso (biprod.inl ≫ f ≫ biprod.fst)]
  body: by
  let :=
    Biprod.gaussian' (biprod.inl ≫ f ≫ biprod.fst) (biprod.inl ≫ f ≫ biprod.snd)
      (biprod.inr ≫ f ≫ biprod.fst) (biprod.inr ≫ f ≫ biprod.snd)
  rwa [Biprod.ofComponents_eq] at this

中文:
定义 Biprod.gaussian
  签名: (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) [是同构 (biprod.inl ≫ f ≫ biprod.fst)]
  定义体: by
  let :=
    Biprod.gaussian' (biprod.inl ≫ f ≫ biprod.fst) (biprod.inl ≫ f ≫ biprod.snd)
      (biprod.inr ≫ f ≫ biprod.fst) (biprod.inr ≫ f ≫ biprod.snd)
  rwa [Biprod.ofComponents_eq] at this

Depends on / 依赖: Biprod, Biprod.gaussian, Biprod.ofComponents_eq, biprod, biprod.fst, biprod.inl, biprod.inr, biprod.snd, gaussian, ofComponents_eq
-/
def Biprod.gaussian (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) [IsIso (biprod.inl ≫ f ≫ biprod.fst)] :
    Σ' (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) (g₂₂ : X₂ ⟶ Y₂),
      L.hom ≫ f ≫ R.hom = biprod.map (biprod.inl ≫ f ≫ biprod.fst) g₂₂ := by
  let :=
    Biprod.gaussian' (biprod.inl ≫ f ≫ biprod.fst) (biprod.inl ≫ f ≫ biprod.snd)
      (biprod.inr ≫ f ≫ biprod.fst) (biprod.inr ≫ f ≫ biprod.snd)
  rwa [Biprod.ofComponents_eq] at this

/--
Definition of `Biprod.isoElim'` / `Biprod.isoElim'` 的定义

English:
definition Biprod.isoElim'
  signature: [IsIso f₁₁] [IsIso (Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂)]
  body: by
  obtain ⟨L, R, g, w⟩ := Biprod.gaussian' f₁₁ f₁₂ f₂₁ f₂₂
  letI : IsIso (biprod.map f₁₁ g) := by
    rw [← w]
    infer_instance
  letI : IsIso g := isIso_right_of_isIso_biprod_map f₁₁ g
  exact asIso g

中文:
定义 Biprod.isoElim'
  签名: [是同构 f₁₁] [是同构 (Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂)]
  定义体: by
  obtain ⟨L, R, g, w⟩ := Biprod.gaussian' f₁₁ f₁₂ f₂₁ f₂₂
  letI : IsIso (biprod.map f₁₁ g) := by
    rw [← w]
    infer_instance
  letI : IsIso g := isIso_right_of_isIso_biprod_map f₁₁ g
  exact asIso g

Depends on / 依赖: Biprod, Biprod.gaussian, biprod, biprod.map, gaussian, infer_instance, isIso_right_of_isIso_biprod_map
-/
def Biprod.isoElim' [IsIso f₁₁] [IsIso (Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂)] : X₂ ≅ Y₂ := by
  obtain ⟨L, R, g, w⟩ := Biprod.gaussian' f₁₁ f₁₂ f₂₁ f₂₂
  letI : IsIso (biprod.map f₁₁ g) := by
    rw [← w]
    infer_instance
  letI : IsIso g := isIso_right_of_isIso_biprod_map f₁₁ g
  exact asIso g

/--
Definition of `Biprod.isoElim` / `Biprod.isoElim` 的定义

English:
definition Biprod.isoElim
  signature: (f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂) [IsIso (biprod.inl ≫ f.hom ≫ biprod.fst)]
  body: letI :
    IsIso
      (Biprod.ofComponents (biprod.inl ≫ f.hom ≫ biprod.fst) (biprod.inl ≫ f.hom ≫ biprod.snd)
        (biprod.inr ≫ f.hom ≫ biprod.fst) (biprod.inr ≫ f.hom ≫ biprod.snd)) := by
    simp only [Biprod.ofComponents_eq]
    infer_instance
  Biprod.isoElim' (biprod.inl ≫ f.hom ≫ biprod.

中文:
定义 Biprod.isoElim
  签名: (f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂) [是同构 (biprod.inl ≫ f.hom ≫ biprod.fst)]
  定义体: letI :
    IsIso
      (Biprod.ofComponents (biprod.inl ≫ f.hom ≫ biprod.fst) (biprod.inl ≫ f.hom ≫ biprod.snd)
        (biprod.inr ≫ f.hom ≫ biprod.fst) (biprod.inr ≫ f.hom ≫ biprod.snd)) := by
    simp only [Biprod.ofComponents_eq]
    infer_instance
  Biprod.isoElim' (biprod.inl ≫ f.hom ≫ biprod.

Depends on / 依赖: Biprod, Biprod.isoElim, Biprod.ofComponents, Biprod.ofComponents_eq, biprod, biprod.fst, biprod.inl, biprod.inr, biprod.snd, f.hom, infer_instance, isoElim, ofComponents, ofComponents_eq
-/
def Biprod.isoElim (f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂) [IsIso (biprod.inl ≫ f.hom ≫ biprod.fst)] : X₂ ≅ Y₂ :=
  letI :
    IsIso
      (Biprod.ofComponents (biprod.inl ≫ f.hom ≫ biprod.fst) (biprod.inl ≫ f.hom ≫ biprod.snd)
        (biprod.inr ≫ f.hom ≫ biprod.fst) (biprod.inr ≫ f.hom ≫ biprod.snd)) := by
    simp only [Biprod.ofComponents_eq]
    infer_instance
  Biprod.isoElim' (biprod.inl ≫ f.hom ≫ biprod.fst) (biprod.inl ≫ f.hom ≫ biprod.snd)
    (biprod.inr ≫ f.hom ≫ biprod.fst) (biprod.inr ≫ f.hom ≫ biprod.snd)

/--
theorem `Biprod.column_nonzero_of_iso` / 定理 `Biprod.column_nonzero_of_iso`

English:
theorem Biprod.column_nonzero_of_iso
  given: {W X Y Z : C} (f : W ⊞ X ⟶ Y ⊞ Z) [IsIso f]
  proof: by
  by_contra! ⟨nz, a₁, a₂⟩
  set x := biprod.inl ≫ f ≫ inv f ≫ biprod.fst
  have h₁ : x = 𝟙 W := by simp [x]
  have h₀ : x = 0 := by
    dsimp [x]
    rw [← Category.id_comp (inv f)]; rw [Category.assoc]; rw [← biprod.total]
    conv_lhs =>
      slice 2 3
      rw [comp_add]
    simp only [Catego

中文:
定理 Biprod.column_nonzero_of_iso
  条件: {W X Y Z : C} (f : W ⊞ X ⟶ Y ⊞ Z) [是同构 f]
  证明: by
  by_contra! ⟨nz, a₁, a₂⟩
  set x := biprod.inl ≫ f ≫ inv f ≫ biprod.fst
  have h₁ : x = 𝟙 W := by simp [x]
  have h₀ : x = 0 := by
    dsimp [x]
    rw [← Category.id_comp (inv f)]; rw [Category.assoc]; rw [← biprod.total]
    conv_lhs =>
      slice 2 3
      rw [comp_add]
    simp only [Catego

Depends on / 依赖: Category, Category.assoc, Category.id_comp, add_comp, add_zero, biprod, biprod.fst, biprod.inl, biprod.total, comp_add, comp_add_assoc, conv_lhs, id_comp, symm.trans, zero_comp
-/
theorem Biprod.column_nonzero_of_iso {W X Y Z : C} (f : W ⊞ X ⟶ Y ⊞ Z) [IsIso f] :
    𝟙 W = 0 ∨ biprod.inl ≫ f ≫ biprod.fst != 0 ∨ biprod.inl ≫ f ≫ biprod.snd != 0 := by
  by_contra! ⟨nz, a₁, a₂⟩
  set x := biprod.inl ≫ f ≫ inv f ≫ biprod.fst
  have h₁ : x = 𝟙 W := by simp [x]
  have h₀ : x = 0 := by
    dsimp [x]
    rw [← Category.id_comp (inv f)]; rw [Category.assoc]; rw [← biprod.total]
    conv_lhs =>
      slice 2 3
      rw [comp_add]
    simp only [Category.assoc]
    rw [comp_add_assoc]; rw [add_comp]
    conv_lhs =>
      congr
      next => skip
      slice 1 3
      rw [a₂]
    simp only [zero_comp, add_zero]
    conv_lhs =>
      slice 1 3
      rw [a₁]
    simp only [zero_comp]
  exact nz (h₁.symm.trans h₀)

end

/--
theorem `Biproduct.column_nonzero_of_iso'` / 定理 `Biproduct.column_nonzero_of_iso'`

English:
theorem Biproduct.column_nonzero_of_iso'
  statement: {σ τ : Type} [Finite τ] {S : σ -> C} [HasBiproduct S]
  proof: by
  cases nonempty_fintype τ
  intro z
  have reassoced {t : τ} {W : C} (h : _ ⟶ W) :
    biproduct.ι S s ≫ f ≫ biproduct.π T t ≫ h = 0 ≫ h := by grind
  set x := biproduct.ι S s ≫ f ≫ inv f ≫ biproduct.π S s
  have h₁ : x = 𝟙 (S s) := by simp [x]
  have h₀ : x = 0 := by
    dsimp [x]
    rw [← Cat

中文:
定理 Biproduct.column_nonzero_of_iso'
  结论: {σ τ : 类型} [有限 τ] {S : σ -> C} [有Biproduct S]
  证明: by
  cases nonempty_fintype τ
  intro z
  have reassoced {t : τ} {W : C} (h : _ ⟶ W) :
    biproduct.ι S s ≫ f ≫ biproduct.π T t ≫ h = 0 ≫ h := by grind
  set x := biproduct.ι S s ≫ f ≫ inv f ≫ biproduct.π S s
  have h₁ : x = 𝟙 (S s) := by simp [x]
  have h₀ : x = 0 := by
    dsimp [x]
    rw [← Cat

Depends on / 依赖: Category, Category.assoc, Category.id_comp, CategoryTheory, CategoryTheory.Limits.zero_comp, Finset, Finset.sum_const_zero, Limits, biproduct, biproduct.total, comp_sum_assoc, id_comp, nonempty_fintype, reassoced, sum_const_zero, symm.trans, zero_comp
-/
theorem Biproduct.column_nonzero_of_iso' {σ τ : Type} [Finite τ] {S : σ -> C} [HasBiproduct S]
    {T : τ -> C} [HasBiproduct T] (s : σ) (f : ⨁ S ⟶ ⨁ T) [IsIso f] :
    (forall t : τ, biproduct.ι S s ≫ f ≫ biproduct.π T t = 0) -> 𝟙 (S s) = 0 := by
  cases nonempty_fintype τ
  intro z
  have reassoced {t : τ} {W : C} (h : _ ⟶ W) :
    biproduct.ι S s ≫ f ≫ biproduct.π T t ≫ h = 0 ≫ h := by grind
  set x := biproduct.ι S s ≫ f ≫ inv f ≫ biproduct.π S s
  have h₁ : x = 𝟙 (S s) := by simp [x]
  have h₀ : x = 0 := by
    dsimp [x]
    rw [← Category.id_comp (inv f)]; rw [Category.assoc]; rw [← biproduct.total]
    simp only [comp_sum_assoc]
    grind [CategoryTheory.Limits.zero_comp, Finset.sum_const_zero]
  exact h₁.symm.trans h₀

/--
Definition of `Biproduct.columnNonzeroOfIso` / `Biproduct.columnNonzeroOfIso` 的定义

English:
definition Biproduct.columnNonzeroOfIso
  signature: {σ τ : Type} [Fintype τ] {S : σ -> C} [HasBiproduct S] {T : τ -> C}
  body: by
  classical
    apply truncSigmaOfExists
    have t := Biproduct.column_nonzero_of_iso'.{v} s f
    by_contra h
    simp only [not_exists_not] at h
    exact nz (t h)

中文:
定义 Biproduct.columnNonzeroOfIso
  签名: {σ τ : 类型} [有限类型 τ] {S : σ -> C} [有Biproduct S] {T : τ -> C}
  定义体: by
  classical
    apply truncSigmaOfExists
    have t := Biproduct.column_nonzero_of_iso'.{v} s f
    by_contra h
    simp only [not_exists_not] at h
    exact nz (t h)

Depends on / 依赖: Biproduct, Biproduct.column_nonzero_of_iso, classical, column_nonzero_of_iso, not_exists_not, truncSigmaOfExists
-/
def Biproduct.columnNonzeroOfIso {σ τ : Type} [Fintype τ] {S : σ -> C} [HasBiproduct S] {T : τ -> C}
    [HasBiproduct T] (s : σ) (nz : 𝟙 (S s) != 0) (f : ⨁ S ⟶ ⨁ T) [IsIso f] :
    Trunc (Σ' t : τ, biproduct.ι S s ≫ f ≫ biproduct.π T t != 0) := by
  classical
    apply truncSigmaOfExists
    have t := Biproduct.column_nonzero_of_iso'.{v} s f
    by_contra h
    simp only [not_exists_not] at h
    exact nz (t h)

section Preadditive

variable {D : Type u'} [Category.{v'} D] [Preadditive.{v'} D]
variable (F : C ⥤ D) [PreservesZeroMorphisms F]

namespace Limits

section Finite

variable {J : Type*} [Finite J]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesProduct_of_preservesBiproduct` / 引理 `preservesProduct_of_preservesBiproduct`

English:
lemma preservesProduct_of_preservesBiproduct
  given: {f : J -> C} [PreservesBiproduct f F]
  proof: let ⟨_⟩ := nonempty_fintype J
    ⟨IsLimit.ofIsoLimit
        ((IsLimit.postcomposeInvEquiv (Discrete.compNatIsoDiscrete _ _) _).symm
          (isBilimitOfPreserves F (biconeIsBilimitOfLimitConeOfIsLimit hc)).isLimit) <|
      Cone.ext (Iso.refl _) (by rintro ⟨⟩; simp)⟩

中文:
引理 preservesProduct_of_preservesBiproduct
  条件: {f : J -> C} [保持Biproduct f F]
  证明: let ⟨_⟩ := nonempty_fintype J
    ⟨IsLimit.ofIsoLimit
        ((IsLimit.postcomposeInvEquiv (Discrete.compNatIsoDiscrete _ _) _).symm
          (isBilimitOfPreserves F (biconeIsBilimitOfLimitConeOfIsLimit hc)).isLimit) <|
      Cone.ext (Iso.refl _) (by rintro ⟨⟩; simp)⟩

Depends on / 依赖: Cone.ext, Discrete, Discrete.compNatIsoDiscrete, IsLimit, IsLimit.ofIsoLimit, IsLimit.postcomposeInvEquiv, Iso.refl, biconeIsBilimitOfLimitConeOfIsLimit, compNatIsoDiscrete, isBilimitOfPreserves, isLimit, nonempty_fintype, ofIsoLimit, postcomposeInvEquiv
-/
lemma preservesProduct_of_preservesBiproduct {f : J -> C} [PreservesBiproduct f F] :
    PreservesLimit (Discrete.functor f) F where
  preserves hc :=
    let ⟨_⟩ := nonempty_fintype J
    ⟨IsLimit.ofIsoLimit
        ((IsLimit.postcomposeInvEquiv (Discrete.compNatIsoDiscrete _ _) _).symm
          (isBilimitOfPreserves F (biconeIsBilimitOfLimitConeOfIsLimit hc)).isLimit) <|
      Cone.ext (Iso.refl _) (by rintro ⟨⟩; simp)⟩

section

attribute [local instance] preservesProduct_of_preservesBiproduct

/--
lemma `preservesProductsOfShape_of_preservesBiproductsOfShape` / 引理 `preservesProductsOfShape_of_preservesBiproductsOfShape`

English:
lemma preservesProductsOfShape_of_preservesBiproductsOfShape
  given: [PreservesBiproductsOfShape J F]
  proof: preservesLimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

中文:
引理 preservesProductsOfShape_of_preservesBiproductsOfShape
  条件: [保持BiproductsOfShape J F]
  证明: preservesLimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

Depends on / 依赖: Discrete, Discrete.natIsoFunctor.symm, natIsoFunctor, preservesLimit_of_iso_diagram
-/
lemma preservesProductsOfShape_of_preservesBiproductsOfShape [PreservesBiproductsOfShape J F] :
    PreservesLimitsOfShape (Discrete J) F where
  preservesLimit {_} := preservesLimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesBiproduct_of_preservesProduct` / 引理 `preservesBiproduct_of_preservesProduct`

English:
lemma preservesBiproduct_of_preservesProduct
  given: {f : J -> C} [PreservesLimit (Discrete.functor f) F]
  proof: let ⟨_⟩ := nonempty_fintype J
⟨isBilimitOfIsLimit _
      IsLimit.ofIsoLimit
          ((IsLimit.postcomposeHomEquiv (Discrete.compNatIsoDiscrete _ _) (F.mapCone b.toCone)).symm
            (isLimitOfPreserves F hb.isLimit)) <|
        Cone.ext (Iso.refl _) (by rintro ⟨⟩; simp)⟩

中文:
引理 preservesBiproduct_of_preservesProduct
  条件: {f : J -> C} [保持极限 (离散.functor f) F]
  证明: let ⟨_⟩ := nonempty_fintype J
⟨isBilimitOfIsLimit _
      IsLimit.ofIsoLimit
          ((IsLimit.postcomposeHomEquiv (Discrete.compNatIsoDiscrete _ _) (F.mapCone b.toCone)).symm
            (isLimitOfPreserves F hb.isLimit)) <|
        Cone.ext (Iso.refl _) (by rintro ⟨⟩; simp)⟩

Depends on / 依赖: Cone.ext, Discrete, Discrete.compNatIsoDiscrete, F.mapCone, Finset, Finset.mem_univ, Finset.univ, IsLimit, IsLimit.ofIsoLimit, IsLimit.postcomposeHomEquiv, Iso.refl, b.toCone, compNatIsoDiscrete, hb.isLimit, isBilimitOfIsLimit, isLimit, isLimitOfPreserves, mapCone, mem_univ, nonempty_fintype
-/
lemma preservesBiproduct_of_preservesProduct {f : J -> C} [PreservesLimit (Discrete.functor f) F] :
    PreservesBiproduct f F where
  preserves {b} hb :=
    let ⟨_⟩ := nonempty_fintype J
⟨isBilimitOfIsLimit _
      IsLimit.ofIsoLimit
          ((IsLimit.postcomposeHomEquiv (Discrete.compNatIsoDiscrete _ _) (F.mapCone b.toCone)).symm
            (isLimitOfPreserves F hb.isLimit)) <|
        Cone.ext (Iso.refl _) (by rintro ⟨⟩; simp)⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesBiproduct_of_mono_biproductComparison` / 引理 `preservesBiproduct_of_mono_biproductComparison`

English:
lemma preservesBiproduct_of_mono_biproductComparison
  statement: {f : J -> C} [HasBiproduct f]
  proof: by
  have : HasProduct fun b => F.obj (f b) := by
    change HasProduct (F.obj ∘ f)
    infer_instance
  have that : piComparison F f =
      (F.mapIso (biproduct.isoProduct f)).inv ≫
        biproductComparison F f ≫ (biproduct.isoProduct _).hom := by
    ext j
    convert! piComparison_comp_π F f 

中文:
引理 preservesBiproduct_of_mono_biproductComparison
  结论: {f : J -> C} [有Biproduct f]
  证明: by
  have : HasProduct fun b => F.obj (f b) := by
    change HasProduct (F.obj ∘ f)
    infer_instance
  have that : piComparison F f =
      (F.mapIso (biproduct.isoProduct f)).inv ≫
        biproductComparison F f ≫ (biproduct.isoProduct _).hom := by
    ext j
    convert! piComparison_comp_π F f 

Depends on / 依赖: F.mapIso, F.obj, Function, Function.comp_def, Functor, Functor.map_comp, HasProduct, PreservesProduct, PreservesProduct.of_iso_comparison, biproduct, biproduct.isoProduct, biproductComparison, blocks, c.blocks, comp_def, convert, infer_instance, isIso_of_mono_of_isSplitEpi, isoProduct, mapIso
-/
lemma preservesBiproduct_of_mono_biproductComparison {f : J -> C} [HasBiproduct f]
    [HasBiproduct (F.obj ∘ f)] [Mono (biproductComparison F f)] : PreservesBiproduct f F := by
  have : HasProduct fun b => F.obj (f b) := by
    change HasProduct (F.obj ∘ f)
    infer_instance
  have that : piComparison F f =
      (F.mapIso (biproduct.isoProduct f)).inv ≫
        biproductComparison F f ≫ (biproduct.isoProduct _).hom := by
    ext j
    convert! piComparison_comp_π F f j; simp [← Function.comp_def, ← Functor.map_comp]
  have : IsIso (biproductComparison F f) := isIso_of_mono_of_isSplitEpi _
  have : IsIso (piComparison F f) := by
    rw [that]
    infer_instance
  have := PreservesProduct.of_iso_comparison F f
  apply preservesBiproduct_of_preservesProduct

/--
lemma `preservesBiproduct_of_epi_biproductComparison'` / 引理 `preservesBiproduct_of_epi_biproductComparison'`

English:
lemma preservesBiproduct_of_epi_biproductComparison'
  statement: {f : J -> C} [HasBiproduct f]
  proof: by
  have : Epi (splitEpiBiproductComparison F f).section_ := by simpa
  have : IsIso (biproductComparison F f) :=
    IsIso.of_epi_section' (splitEpiBiproductComparison F f)
  apply preservesBiproduct_of_mono_biproductComparison

中文:
引理 preservesBiproduct_of_epi_biproductComparison'
  结论: {f : J -> C} [有Biproduct f]
  证明: by
  have : Epi (splitEpiBiproductComparison F f).section_ := by simpa
  have : IsIso (biproductComparison F f) :=
    IsIso.of_epi_section' (splitEpiBiproductComparison F f)
  apply preservesBiproduct_of_mono_biproductComparison

Depends on / 依赖: IsIso.of_epi_section, biproductComparison, of_epi_section, preservesBiproduct_of_mono_biproductComparison, section_, splitEpiBiproductComparison
-/
lemma preservesBiproduct_of_epi_biproductComparison' {f : J -> C} [HasBiproduct f]
    [HasBiproduct (F.obj ∘ f)] [Epi (biproductComparison' F f)] : PreservesBiproduct f F := by
  have : Epi (splitEpiBiproductComparison F f).section_ := by simpa
  have : IsIso (biproductComparison F f) :=
    IsIso.of_epi_section' (splitEpiBiproductComparison F f)
  apply preservesBiproduct_of_mono_biproductComparison

/--
lemma `preservesBiproductsOfShape_of_preservesProductsOfShape` / 引理 `preservesBiproductsOfShape_of_preservesProductsOfShape`

English:
lemma preservesBiproductsOfShape_of_preservesProductsOfShape
  proof: preservesBiproduct_of_preservesProduct F

中文:
引理 preservesBiproductsOfShape_of_preservesProductsOfShape
  证明: preservesBiproduct_of_preservesProduct F

Depends on / 依赖: preservesBiproduct_of_preservesProduct
-/
lemma preservesBiproductsOfShape_of_preservesProductsOfShape
    [PreservesLimitsOfShape (Discrete J) F] :
    PreservesBiproductsOfShape J F where
  preserves {_} := preservesBiproduct_of_preservesProduct F

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesCoproduct_of_preservesBiproduct` / 引理 `preservesCoproduct_of_preservesBiproduct`

English:
lemma preservesCoproduct_of_preservesBiproduct
  given: {f : J -> C} [PreservesBiproduct f F]
  proof: let ⟨_⟩ := nonempty_fintype J
    ⟨IsColimit.ofIsoColimit
        ((IsColimit.precomposeHomEquiv (Discrete.compNatIsoDiscrete _ _) _).symm
          (isBilimitOfPreserves F (biconeIsBilimitOfColimitCoconeOfIsColimit hc)).isColimit) <|
      Cocone.ext (Iso.refl _) (by rintro ⟨⟩; simp)⟩

中文:
引理 preservesCoproduct_of_preservesBiproduct
  条件: {f : J -> C} [保持Biproduct f F]
  证明: let ⟨_⟩ := nonempty_fintype J
    ⟨IsColimit.ofIsoColimit
        ((IsColimit.precomposeHomEquiv (Discrete.compNatIsoDiscrete _ _) _).symm
          (isBilimitOfPreserves F (biconeIsBilimitOfColimitCoconeOfIsColimit hc)).isColimit) <|
      Cocone.ext (Iso.refl _) (by rintro ⟨⟩; simp)⟩

Depends on / 依赖: Cocone, Cocone.ext, Discrete, Discrete.compNatIsoDiscrete, IsColimit, IsColimit.ofIsoColimit, IsColimit.precomposeHomEquiv, Iso.refl, biconeIsBilimitOfColimitCoconeOfIsColimit, compNatIsoDiscrete, isBilimitOfPreserves, isColimit, nonempty_fintype, ofIsoColimit, precomposeHomEquiv
-/
lemma preservesCoproduct_of_preservesBiproduct {f : J -> C} [PreservesBiproduct f F] :
    PreservesColimit (Discrete.functor f) F where
  preserves {c} hc :=
    let ⟨_⟩ := nonempty_fintype J
    ⟨IsColimit.ofIsoColimit
        ((IsColimit.precomposeHomEquiv (Discrete.compNatIsoDiscrete _ _) _).symm
          (isBilimitOfPreserves F (biconeIsBilimitOfColimitCoconeOfIsColimit hc)).isColimit) <|
      Cocone.ext (Iso.refl _) (by rintro ⟨⟩; simp)⟩

section

attribute [local instance] preservesCoproduct_of_preservesBiproduct

/--
lemma `preservesCoproductsOfShape_of_preservesBiproductsOfShape` / 引理 `preservesCoproductsOfShape_of_preservesBiproductsOfShape`

English:
lemma preservesCoproductsOfShape_of_preservesBiproductsOfShape
  given: [PreservesBiproductsOfShape J F]
  proof: preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

中文:
引理 preservesCoproductsOfShape_of_preservesBiproductsOfShape
  条件: [保持BiproductsOfShape J F]
  证明: preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

Depends on / 依赖: Discrete, Discrete.natIsoFunctor.symm, natIsoFunctor, preservesColimit_of_iso_diagram
-/
lemma preservesCoproductsOfShape_of_preservesBiproductsOfShape [PreservesBiproductsOfShape J F] :
    PreservesColimitsOfShape (Discrete J) F where
  preservesColimit {_} := preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesBiproduct_of_preservesCoproduct` / 引理 `preservesBiproduct_of_preservesCoproduct`

English:
lemma preservesBiproduct_of_preservesCoproduct
  statement: {f : J -> C}
  proof: let ⟨_⟩ := nonempty_fintype J
⟨isBilimitOfIsColimit _
      IsColimit.ofIsoColimit
          ((IsColimit.precomposeInvEquiv (Discrete.compNatIsoDiscrete _ _)
                (F.mapCocone b.toCocone)).symm
            (isColimitOfPreserves F hb.isColimit)) <|
        Cocone.ext (Iso.refl _) (by rintr

中文:
引理 preservesBiproduct_of_preservesCoproduct
  结论: {f : J -> C}
  证明: let ⟨_⟩ := nonempty_fintype J
⟨isBilimitOfIsColimit _
      IsColimit.ofIsoColimit
          ((IsColimit.precomposeInvEquiv (Discrete.compNatIsoDiscrete _ _)
                (F.mapCocone b.toCocone)).symm
            (isColimitOfPreserves F hb.isColimit)) <|
        Cocone.ext (Iso.refl _) (by rintr

Depends on / 依赖: Cocone, Cocone.ext, Discrete, Discrete.compNatIsoDiscrete, F.mapCocone, IsColimit, IsColimit.ofIsoColimit, IsColimit.precomposeInvEquiv, Iso.refl, b.toCocone, compNatIsoDiscrete, hb.isColimit, isBilimitOfIsColimit, isColimit, isColimitOfPreserves, mapCocone, nonempty_fintype, ofIsoColimit, precomposeInvEquiv, toCocone
-/
lemma preservesBiproduct_of_preservesCoproduct {f : J -> C}
    [PreservesColimit (Discrete.functor f) F] :
    PreservesBiproduct f F where
  preserves {b} hb :=
    let ⟨_⟩ := nonempty_fintype J
⟨isBilimitOfIsColimit _
      IsColimit.ofIsoColimit
          ((IsColimit.precomposeInvEquiv (Discrete.compNatIsoDiscrete _ _)
                (F.mapCocone b.toCocone)).symm
            (isColimitOfPreserves F hb.isColimit)) <|
        Cocone.ext (Iso.refl _) (by rintro ⟨⟩; simp)⟩

/--
lemma `preservesBiproductsOfShape_of_preservesCoproductsOfShape` / 引理 `preservesBiproductsOfShape_of_preservesCoproductsOfShape`

English:
lemma preservesBiproductsOfShape_of_preservesCoproductsOfShape
  proof: preservesBiproduct_of_preservesCoproduct F

中文:
引理 preservesBiproductsOfShape_of_preservesCoproductsOfShape
  证明: preservesBiproduct_of_preservesCoproduct F

Depends on / 依赖: preservesBiproduct_of_preservesCoproduct
-/
lemma preservesBiproductsOfShape_of_preservesCoproductsOfShape
    [PreservesColimitsOfShape (Discrete J) F] : PreservesBiproductsOfShape J F where
  preserves {_} := preservesBiproduct_of_preservesCoproduct F

end Finite

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesBinaryProduct_of_preservesBinaryBiproduct` / 引理 `preservesBinaryProduct_of_preservesBinaryBiproduct`

English:
lemma preservesBinaryProduct_of_preservesBinaryBiproduct
  statement: {X Y : C}
  proof: ⟨IsLimit.ofIsoLimit
        ((IsLimit.postcomposeInvEquiv (diagramIsoPair _) _).symm
          (isBinaryBilimitOfPreserves F (binaryBiconeIsBilimitOfLimitConeOfIsLimit hc)).isLimit) <|
      Cone.ext (by dsimp; rfl) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp⟩

中文:
引理 preservesBinaryProduct_of_preservesBinaryBiproduct
  结论: {X Y : C}
  证明: ⟨IsLimit.ofIsoLimit
        ((IsLimit.postcomposeInvEquiv (diagramIsoPair _) _).symm
          (isBinaryBilimitOfPreserves F (binaryBiconeIsBilimitOfLimitConeOfIsLimit hc)).isLimit) <|
      Cone.ext (by dsimp; rfl) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp⟩

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, ofIsoLimit
-/
lemma preservesBinaryProduct_of_preservesBinaryBiproduct {X Y : C}
    [PreservesBinaryBiproduct X Y F] :
    PreservesLimit (pair X Y) F where
  preserves {c} hc := ⟨IsLimit.ofIsoLimit
        ((IsLimit.postcomposeInvEquiv (diagramIsoPair _) _).symm
          (isBinaryBilimitOfPreserves F (binaryBiconeIsBilimitOfLimitConeOfIsLimit hc)).isLimit) <|
      Cone.ext (by dsimp; rfl) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp⟩

section

attribute [local instance] preservesBinaryProduct_of_preservesBinaryBiproduct

/--
lemma `preservesBinaryProducts_of_preservesBinaryBiproducts` / 引理 `preservesBinaryProducts_of_preservesBinaryBiproducts`

English:
lemma preservesBinaryProducts_of_preservesBinaryBiproducts
  given: [PreservesBinaryBiproducts F]
  proof: preservesLimit_of_iso_diagram _ (diagramIsoPair _).symm

中文:
引理 preservesBinaryProducts_of_preservesBinaryBiproducts
  条件: [保持BinaryBiproducts F]
  证明: preservesLimit_of_iso_diagram _ (diagramIsoPair _).symm

Depends on / 依赖: diagramIsoPair, preservesLimit_of_iso_diagram
-/
lemma preservesBinaryProducts_of_preservesBinaryBiproducts [PreservesBinaryBiproducts F] :
    PreservesLimitsOfShape (Discrete WalkingPair) F where
  preservesLimit {_} := preservesLimit_of_iso_diagram _ (diagramIsoPair _).symm

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesBinaryBiproduct_of_preservesBinaryProduct` / 引理 `preservesBinaryBiproduct_of_preservesBinaryProduct`

English:
lemma preservesBinaryBiproduct_of_preservesBinaryProduct
  given: {X Y : C} [PreservesLimit (pair X Y) F]
  proof: ⟨isBinaryBilimitOfIsLimit _ IsLimit.ofIsoLimit
          ((IsLimit.postcomposeHomEquiv (diagramIsoPair _) (F.mapCone b.toCone)).symm
            (isLimitOfPreserves F hb.isLimit)) <|
        Cone.ext (by dsimp; rfl) fun j => by
          rcases j with ⟨⟨⟩⟩ <;> simp⟩

中文:
引理 preservesBinaryBiproduct_of_preservesBinaryProduct
  条件: {X Y : C} [保持极限 (pair X Y) F]
  证明: ⟨isBinaryBilimitOfIsLimit _ IsLimit.ofIsoLimit
          ((IsLimit.postcomposeHomEquiv (diagramIsoPair _) (F.mapCone b.toCone)).symm
            (isLimitOfPreserves F hb.isLimit)) <|
        Cone.ext (by dsimp; rfl) fun j => by
          rcases j with ⟨⟨⟩⟩ <;> simp⟩

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, isBinaryBilimitOfIsLimit, ofIsoLimit
-/
lemma preservesBinaryBiproduct_of_preservesBinaryProduct {X Y : C} [PreservesLimit (pair X Y) F] :
    PreservesBinaryBiproduct X Y F where
preserves {b} hb := ⟨isBinaryBilimitOfIsLimit _ IsLimit.ofIsoLimit
          ((IsLimit.postcomposeHomEquiv (diagramIsoPair _) (F.mapCone b.toCone)).symm
            (isLimitOfPreserves F hb.isLimit)) <|
        Cone.ext (by dsimp; rfl) fun j => by
          rcases j with ⟨⟨⟩⟩ <;> simp⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesBinaryBiproduct_of_mono_biprodComparison` / 引理 `preservesBinaryBiproduct_of_mono_biprodComparison`

English:
lemma preservesBinaryBiproduct_of_mono_biprodComparison
  statement: {X Y : C} [HasBinaryBiproduct X Y]
  proof: by
  have that :
    prodComparison F X Y =
      (F.mapIso (biprod.isoProd X Y)).inv ≫ biprodComparison F X Y ≫ (biprod.isoProd _ _).hom := by
    ext <;> simp [← Functor.map_comp]
  have : IsIso (biprodComparison F X Y) := isIso_of_mono_of_isSplitEpi _
  have : IsIso (prodComparison F X Y) := by
 

中文:
引理 preservesBinaryBiproduct_of_mono_biprodComparison
  结论: {X Y : C} [有BinaryBiproduct X Y]
  证明: by
  have that :
    prodComparison F X Y =
      (F.mapIso (biprod.isoProd X Y)).inv ≫ biprodComparison F X Y ≫ (biprod.isoProd _ _).hom := by
    ext <;> simp [← Functor.map_comp]
  have : IsIso (biprodComparison F X Y) := isIso_of_mono_of_isSplitEpi _
  have : IsIso (prodComparison F X Y) := by
 

Depends on / 依赖: F.mapIso, Functor, Functor.map_comp, PreservesLimitPair, PreservesLimitPair.of_iso_prod_comparison, biprod, biprod.isoProd, biprodComparison, infer_instance, isIso_of_mono_of_isSplitEpi, isoProd, mapIso, map_comp, of_iso_prod_comparison, preservesBinaryBiproduct_of_preservesBinaryProduct, prodComparison
-/
lemma preservesBinaryBiproduct_of_mono_biprodComparison {X Y : C} [HasBinaryBiproduct X Y]
    [HasBinaryBiproduct (F.obj X) (F.obj Y)] [Mono (biprodComparison F X Y)] :
    PreservesBinaryBiproduct X Y F := by
  have that :
    prodComparison F X Y =
      (F.mapIso (biprod.isoProd X Y)).inv ≫ biprodComparison F X Y ≫ (biprod.isoProd _ _).hom := by
    ext <;> simp [← Functor.map_comp]
  have : IsIso (biprodComparison F X Y) := isIso_of_mono_of_isSplitEpi _
  have : IsIso (prodComparison F X Y) := by
    rw [that]
    infer_instance
  have := PreservesLimitPair.of_iso_prod_comparison F X Y
  apply preservesBinaryBiproduct_of_preservesBinaryProduct

/--
lemma `preservesBinaryBiproduct_of_epi_biprodComparison'` / 引理 `preservesBinaryBiproduct_of_epi_biprodComparison'`

English:
lemma preservesBinaryBiproduct_of_epi_biprodComparison'
  statement: {X Y : C} [HasBinaryBiproduct X Y]
  proof: by
  have : Epi (splitEpiBiprodComparison F X Y).section_ := by simpa
  have : IsIso (biprodComparison F X Y) :=
    IsIso.of_epi_section' (splitEpiBiprodComparison F X Y)
  apply preservesBinaryBiproduct_of_mono_biprodComparison

中文:
引理 preservesBinaryBiproduct_of_epi_biprodComparison'
  结论: {X Y : C} [有BinaryBiproduct X Y]
  证明: by
  have : Epi (splitEpiBiprodComparison F X Y).section_ := by simpa
  have : IsIso (biprodComparison F X Y) :=
    IsIso.of_epi_section' (splitEpiBiprodComparison F X Y)
  apply preservesBinaryBiproduct_of_mono_biprodComparison

Depends on / 依赖: IsIso.of_epi_section, biprodComparison, of_epi_section, preservesBinaryBiproduct_of_mono_biprodComparison, section_, splitEpiBiprodComparison
-/
lemma preservesBinaryBiproduct_of_epi_biprodComparison' {X Y : C} [HasBinaryBiproduct X Y]
    [HasBinaryBiproduct (F.obj X) (F.obj Y)] [Epi (biprodComparison' F X Y)] :
    PreservesBinaryBiproduct X Y F := by
  have : Epi (splitEpiBiprodComparison F X Y).section_ := by simpa
  have : IsIso (biprodComparison F X Y) :=
    IsIso.of_epi_section' (splitEpiBiprodComparison F X Y)
  apply preservesBinaryBiproduct_of_mono_biprodComparison

/--
lemma `preservesBinaryBiproducts_of_preservesBinaryProducts` / 引理 `preservesBinaryBiproducts_of_preservesBinaryProducts`

English:
lemma preservesBinaryBiproducts_of_preservesBinaryProducts
  proof: preservesBinaryBiproduct_of_preservesBinaryProduct F

中文:
引理 preservesBinaryBiproducts_of_preservesBinaryProducts
  证明: preservesBinaryBiproduct_of_preservesBinaryProduct F

Depends on / 依赖: preservesBinaryBiproduct_of_preservesBinaryProduct
-/
lemma preservesBinaryBiproducts_of_preservesBinaryProducts
    [PreservesLimitsOfShape (Discrete WalkingPair) F] : PreservesBinaryBiproducts F where
  preserves {_} {_} := preservesBinaryBiproduct_of_preservesBinaryProduct F

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesBinaryCoproduct_of_preservesBinaryBiproduct` / 引理 `preservesBinaryCoproduct_of_preservesBinaryBiproduct`

English:
lemma preservesBinaryCoproduct_of_preservesBinaryBiproduct
  statement: {X Y : C}
  proof: ⟨IsColimit.ofIsoColimit
        ((IsColimit.precomposeHomEquiv (diagramIsoPair _) _).symm
          (isBinaryBilimitOfPreserves F
              (binaryBiconeIsBilimitOfColimitCoconeOfIsColimit hc)).isColimit) <|
      Cocone.ext (by dsimp; rfl) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp⟩

中文:
引理 preservesBinaryCoproduct_of_preservesBinaryBiproduct
  结论: {X Y : C}
  证明: ⟨IsColimit.ofIsoColimit
        ((IsColimit.precomposeHomEquiv (diagramIsoPair _) _).symm
          (isBinaryBilimitOfPreserves F
              (binaryBiconeIsBilimitOfColimitCoconeOfIsColimit hc)).isColimit) <|
      Cocone.ext (by dsimp; rfl) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp⟩

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, IsColimit.precomposeHomEquiv, binaryBiconeIsBilimitOfColimitCoconeOfIsColimit, diagramIsoPair, isBinaryBilimitOfPreserves, isColimit, ofIsoColimit, precomposeHomEquiv
-/
lemma preservesBinaryCoproduct_of_preservesBinaryBiproduct {X Y : C}
    [PreservesBinaryBiproduct X Y F] :
    PreservesColimit (pair X Y) F where
  preserves {c} hc :=
    ⟨IsColimit.ofIsoColimit
        ((IsColimit.precomposeHomEquiv (diagramIsoPair _) _).symm
          (isBinaryBilimitOfPreserves F
              (binaryBiconeIsBilimitOfColimitCoconeOfIsColimit hc)).isColimit) <|
      Cocone.ext (by dsimp; rfl) fun j => by
        rcases j with ⟨⟨⟩⟩ <;> simp⟩

section

attribute [local instance] preservesBinaryCoproduct_of_preservesBinaryBiproduct

/--
lemma `preservesBinaryCoproducts_of_preservesBinaryBiproducts` / 引理 `preservesBinaryCoproducts_of_preservesBinaryBiproducts`

English:
lemma preservesBinaryCoproducts_of_preservesBinaryBiproducts
  given: [PreservesBinaryBiproducts F]
  proof: preservesColimit_of_iso_diagram _ (diagramIsoPair _).symm

中文:
引理 preservesBinaryCoproducts_of_preservesBinaryBiproducts
  条件: [保持BinaryBiproducts F]
  证明: preservesColimit_of_iso_diagram _ (diagramIsoPair _).symm

Depends on / 依赖: diagramIsoPair, preservesColimit_of_iso_diagram
-/
lemma preservesBinaryCoproducts_of_preservesBinaryBiproducts [PreservesBinaryBiproducts F] :
    PreservesColimitsOfShape (Discrete WalkingPair) F where
  preservesColimit {_} := preservesColimit_of_iso_diagram _ (diagramIsoPair _).symm

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesBinaryBiproduct_of_preservesBinaryCoproduct` / 引理 `preservesBinaryBiproduct_of_preservesBinaryCoproduct`

English:
lemma preservesBinaryBiproduct_of_preservesBinaryCoproduct
  statement: {X Y : C}
  proof: ⟨isBinaryBilimitOfIsColimit _
      IsColimit.ofIsoColimit
          ((IsColimit.precomposeInvEquiv (diagramIsoPair _) (F.mapCocone b.toCocone)).symm
            (isColimitOfPreserves F hb.isColimit)) <|
        Cocone.ext (Iso.refl _) fun j => by
          rcases j with ⟨⟨⟩⟩ <;> simp⟩

中文:
引理 preservesBinaryBiproduct_of_preservesBinaryCoproduct
  结论: {X Y : C}
  证明: ⟨isBinaryBilimitOfIsColimit _
      IsColimit.ofIsoColimit
          ((IsColimit.precomposeInvEquiv (diagramIsoPair _) (F.mapCocone b.toCocone)).symm
            (isColimitOfPreserves F hb.isColimit)) <|
        Cocone.ext (Iso.refl _) fun j => by
          rcases j with ⟨⟨⟩⟩ <;> simp⟩

Depends on / 依赖: Cocone, Cocone.ext, F.mapCocone, IsColimit, IsColimit.ofIsoColimit, IsColimit.precomposeInvEquiv, Iso.refl, b.toCocone, diagramIsoPair, hb.isColimit, isBinaryBilimitOfIsColimit, isColimit, isColimitOfPreserves, mapCocone, ofIsoColimit, precomposeInvEquiv, toCocone
-/
lemma preservesBinaryBiproduct_of_preservesBinaryCoproduct {X Y : C}
    [PreservesColimit (pair X Y) F] :
    PreservesBinaryBiproduct X Y F where
  preserves {b} hb :=
⟨isBinaryBilimitOfIsColimit _
      IsColimit.ofIsoColimit
          ((IsColimit.precomposeInvEquiv (diagramIsoPair _) (F.mapCocone b.toCocone)).symm
            (isColimitOfPreserves F hb.isColimit)) <|
        Cocone.ext (Iso.refl _) fun j => by
          rcases j with ⟨⟨⟩⟩ <;> simp⟩

/--
lemma `preservesBinaryBiproducts_of_preservesBinaryCoproducts` / 引理 `preservesBinaryBiproducts_of_preservesBinaryCoproducts`

English:
lemma preservesBinaryBiproducts_of_preservesBinaryCoproducts
  proof: preservesBinaryBiproduct_of_preservesBinaryCoproduct F

中文:
引理 preservesBinaryBiproducts_of_preservesBinaryCoproducts
  证明: preservesBinaryBiproduct_of_preservesBinaryCoproduct F

Depends on / 依赖: preservesBinaryBiproduct_of_preservesBinaryCoproduct
-/
lemma preservesBinaryBiproducts_of_preservesBinaryCoproducts
    [PreservesColimitsOfShape (Discrete WalkingPair) F] : PreservesBinaryBiproducts F where
  preserves {_} {_} := preservesBinaryBiproduct_of_preservesBinaryCoproduct F

end Limits

end Preadditive

end CategoryTheory
