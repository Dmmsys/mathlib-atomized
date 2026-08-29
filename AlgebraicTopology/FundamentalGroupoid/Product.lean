/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.Homotopy.Product

/-!
# Fundamental groupoid preserves products

In this file, we give the following definitions/theorems:

  - `FundamentalGroupoidFunctor.piIso` An isomorphism between Π i, (π Xᵢ) and π (Πi, Xᵢ), whose
    inverse is precisely the product of the maps π (Π i, Xᵢ) → π (Xᵢ), each induced by
    the projection in `Top` Π i, Xᵢ → Xᵢ.

  - `FundamentalGroupoidFunctor.prodIso` An isomorphism between πX × πY and π (X × Y), whose
    inverse is precisely the product of the maps π (X × Y) → πX and π (X × Y) → Y, each induced by
    the projections X × Y → X and X × Y → Y

  - `FundamentalGroupoidFunctor.preservesProduct` A proof that the fundamental groupoid functor
    preserves all products.
-/

@[expose] public section


noncomputable section

open scoped FundamentalGroupoid CategoryTheory

namespace FundamentalGroupoidFunctor

universe u v

section Pi

variable {I : Type u} (X : I -> TopCat.{u})

/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: (i : I)
  body: πₘ (TopCat.ofHom ⟨_, continuous_apply i⟩)

中文:
定义 proj
  签名: (i : I)
  定义体: πₘ (TopCat.ofHom ⟨_, continuous_apply i⟩)

Depends on / 依赖: TopCat, TopCat.ofHom, continuous_apply
-/
def proj (i : I) : πₓ (TopCat.of (forall i, X i)) ⥤ πₓ (X i) :=
  πₘ (TopCat.ofHom ⟨_, continuous_apply i⟩)

/-- The projection map is precisely `Path.Homotopic.proj` interpreted as a functor -/
@[simp]
/--
theorem `proj_map` / 定理 `proj_map`

English:
theorem proj_map
  given: (i : I) (x₀ x₁ : πₓ (TopCat.of (forall i, X i))) (p : x₀ ⟶ x₁)
  proof: rfl

中文:
定理 proj_map
  条件: (i : I) (x₀ x₁ : πₓ (顶元素范畴.of (对任意 i, X i))) (p : x₀ ⟶ x₁)
  证明: rfl
-/
theorem proj_map (i : I) (x₀ x₁ : πₓ (TopCat.of (forall i, X i))) (p : x₀ ⟶ x₁) :
    (proj X i).map p = @Path.Homotopic.proj _ _ _ _ _ i p :=
  rfl

/-- The map taking the pi product of a family of fundamental groupoids to the fundamental
groupoid of the pi product. This is actually an isomorphism (see `piIso`)
-/
@[simps]
/--
Definition of `piToPiTop` / `piToPiTop` 的定义

English:
definition piToPiTop
  signature: : (forall i, πₓ (X i)) ⥤ πₓ (TopCat.of (forall i, X i)) where
  body: ⟨fun i => (g i).as⟩
  map p := Path.Homotopic.pi p
  map_id x := by
    change (Path.Homotopic.pi fun i => Path.Homotopic.Quotient.mk _) = _
    simp only [Path.Homotopic.pi_lift]
    rfl
  map_comp f g := (Path.Homotopic.comp_pi_eq_pi_comp f g).symm

中文:
定义 piToPiTop
  签名: : (对任意 i, πₓ (X i)) ⥤ πₓ (顶元素范畴.of (对任意 i, X i)) where
  定义体: ⟨fun i => (g i).as⟩
  map p := Path.Homotopic.pi p
  map_id x := by
    change (Path.Homotopic.pi fun i => Path.Homotopic.Quotient.mk _) = _
    simp only [Path.Homotopic.pi_lift]
    rfl
  map_comp f g := (Path.Homotopic.comp_pi_eq_pi_comp f g).symm
-/
def piToPiTop : (forall i, πₓ (X i)) ⥤ πₓ (TopCat.of (forall i, X i)) where
  obj g := ⟨fun i => (g i).as⟩
  map p := Path.Homotopic.pi p
  map_id x := by
    change (Path.Homotopic.pi fun i => Path.Homotopic.Quotient.mk _) = _
    simp only [Path.Homotopic.pi_lift]
    rfl
  map_comp f g := (Path.Homotopic.comp_pi_eq_pi_comp f g).symm

set_option backward.isDefEq.respectTransparency false in
/-- Shows `piToPiTop` is an isomorphism, whose inverse is precisely the pi product
of the induced projections. This shows that `fundamentalGroupoidFunctor` preserves products.
-/
@[simps]
/--
Definition of `piIso` / `piIso` 的定义

English:
definition piIso
  signature: : CategoryTheory.Grpd.of (forall i : I, πₓ (X i)) ≅ πₓ (TopCat.of (forall i, X i)) where
  body: piToPiTop X
  inv := CategoryTheory.Functor.pi' (proj X)
  hom_inv_id := by
    change piToPiTop X ⋙ CategoryTheory.Functor.pi' (proj X) = 𝟭 _
    apply CategoryTheory.Functor.ext ?_ ?_
    · intros; rfl
    · intros; ext; simp
  inv_hom_id := by
    change CategoryTheory.Functor.pi' (proj X) ⋙ piToPiTop X = 𝟭 _
    apply CategoryTheory.Functor.ext
    · intro _ _ f
      suffices Path.Homotopic.pi ((CategoryTheory.Functor.pi' (proj X)).map f) = f by simpa
      change Path.Homotopic.pi (fun i => (CategoryTheory.Functor.pi' (proj X)).map f i) = _
      simp
    · intros; rfl

中文:
定义 piIso
  签名: : 范畴论.Grpd.of (对任意 i : I, πₓ (X i)) ≅ πₓ (顶元素范畴.of (对任意 i, X i)) where
  定义体: piToPiTop X
  inv := CategoryTheory.Functor.pi' (proj X)
  hom_inv_id := by
    change piToPiTop X ⋙ CategoryTheory.Functor.pi' (proj X) = 𝟭 _
    apply CategoryTheory.Functor.ext ?_ ?_
    · intros; rfl
    · intros; ext; simp
  inv_hom_id := by
    change CategoryTheory.Functor.pi' (proj X) ⋙ piToPiTop X = 𝟭 _
    apply CategoryTheory.Functor.ext
    · intro _ _ f
      suffices Path.Homotopic.pi ((CategoryTheory.Functor.pi' (proj X)).map f) = f by simpa
      change Path.Homotopic.pi (fun i => (CategoryTheory.Functor.pi' (proj X)).map f i) = _
      simp
    · intros; rfl

Depends on / 依赖: piToPiTop
-/
def piIso : CategoryTheory.Grpd.of (forall i : I, πₓ (X i)) ≅ πₓ (TopCat.of (forall i, X i)) where
  hom := piToPiTop X
  inv := CategoryTheory.Functor.pi' (proj X)
  hom_inv_id := by
    change piToPiTop X ⋙ CategoryTheory.Functor.pi' (proj X) = 𝟭 _
    apply CategoryTheory.Functor.ext ?_ ?_
    · intros; rfl
    · intros; ext; simp
  inv_hom_id := by
    change CategoryTheory.Functor.pi' (proj X) ⋙ piToPiTop X = 𝟭 _
    apply CategoryTheory.Functor.ext
    · intro _ _ f
      suffices Path.Homotopic.pi ((CategoryTheory.Functor.pi' (proj X)).map f) = f by simpa
      change Path.Homotopic.pi (fun i => (CategoryTheory.Functor.pi' (proj X)).map f i) = _
      simp
    · intros; rfl

section Preserves

open CategoryTheory

/--
Definition of `coneDiscreteComp` / `coneDiscreteComp` 的定义

English:
definition coneDiscreteComp
  signature: :
  body: Limits.Cone.postcomposeEquivalence (Discrete.compNatIsoDiscrete X π)

中文:
定义 coneDiscreteComp
  签名: :
  定义体: Limits.Cone.postcomposeEquivalence (Discrete.compNatIsoDiscrete X π)

Depends on / 依赖: Discrete, Discrete.compNatIsoDiscrete, Limits, Limits.Cone.postcomposeEquivalence, compNatIsoDiscrete, postcomposeEquivalence
-/
def coneDiscreteComp :
    Limits.Cone (Discrete.functor X ⋙ π) ≌ Limits.Cone (Discrete.functor fun i => πₓ (X i)) :=
  Limits.Cone.postcomposeEquivalence (Discrete.compNatIsoDiscrete X π)

/--
theorem `coneDiscreteComp_obj_mapCone` / 定理 `coneDiscreteComp_obj_mapCone`

English:
theorem coneDiscreteComp_obj_mapCone
  proof: rfl

中文:
定理 coneDiscreteComp_obj_mapCone
  证明: rfl
-/
theorem coneDiscreteComp_obj_mapCone :
    (coneDiscreteComp X).functor.obj (Functor.mapCone π (TopCat.piFan X)) =
      Limits.Fan.mk (πₓ (TopCat.of (forall i, X i))) (proj X) :=
  rfl

/--
Definition of `piTopToPiCone` / `piTopToPiCone` 的定义

English:
definition piTopToPiCone
  signature: :
  body: CategoryTheory.Functor.pi' (proj X)

中文:
定义 piTopToPiCone
  签名: :
  定义体: CategoryTheory.Functor.pi' (proj X)

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.pi, Functor
-/
def piTopToPiCone :
    Limits.Fan.mk (πₓ (TopCat.of (forall i, X i))) (proj X) ⟶ Grpd.piLimitFan fun i : I => πₓ (X i) where
  hom := CategoryTheory.Functor.pi' (proj X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (piTopToPiCone X)
  body: haveI : IsIso (piTopToPiCone X).hom := (inferInstance : IsIso (piIso X).inv)
  Limits.Cone.cone_iso_of_hom_iso (piTopToPiCone X)

中文:
实例 :
  签名: 是同构 (piTopToPiCone X)
  定义体: haveI : IsIso (piTopToPiCone X).hom := (inferInstance : IsIso (piIso X).inv)
  Limits.Cone.cone_iso_of_hom_iso (piTopToPiCone X)

Depends on / 依赖: Limits, Limits.Cone.cone_iso_of_hom_iso, cone_iso_of_hom_iso, piTopToPiCone
-/
instance : IsIso (piTopToPiCone X) :=
  haveI : IsIso (piTopToPiCone X).hom := (inferInstance : IsIso (piIso X).inv)
  Limits.Cone.cone_iso_of_hom_iso (piTopToPiCone X)

/--
lemma `preservesProduct` / 引理 `preservesProduct`

English:
lemma preservesProduct
  statement: Limits.PreservesLimit (Discrete.functor X) π
  proof: by
  apply Limits.preservesLimit_of_preserves_limit_cone (TopCat.piFanIsLimit X)
  apply (Limits.IsLimit.ofConeEquiv (coneDiscreteComp X)).toFun
  simp only [coneDiscreteComp_obj_mapCone]
  apply Limits.IsLimit.ofIsoLimit _ (asIso (piTopToPiCone X)).symm
  exact Grpd.piLimitFanIsLimit _

中文:
引理 preservesProduct
  结论: Limits.保持极限 (离散.functor X) π
  证明: by
  apply Limits.preservesLimit_of_preserves_limit_cone (TopCat.piFanIsLimit X)
  apply (Limits.IsLimit.ofConeEquiv (coneDiscreteComp X)).toFun
  simp only [coneDiscreteComp_obj_mapCone]
  apply Limits.IsLimit.ofIsoLimit _ (asIso (piTopToPiCone X)).symm
  exact Grpd.piLimitFanIsLimit _

Depends on / 依赖: Grpd.piLimitFanIsLimit, IsLimit, Limits, Limits.IsLimit.ofConeEquiv, Limits.IsLimit.ofIsoLimit, Limits.preservesLimit_of_preserves_limit_cone, TopCat, TopCat.piFanIsLimit, coneDiscreteComp, coneDiscreteComp_obj_mapCone, ofConeEquiv, ofIsoLimit, piFanIsLimit, piLimitFanIsLimit, piTopToPiCone, preservesLimit_of_preserves_limit_cone
-/
lemma preservesProduct : Limits.PreservesLimit (Discrete.functor X) π := by
  apply Limits.preservesLimit_of_preserves_limit_cone (TopCat.piFanIsLimit X)
  apply (Limits.IsLimit.ofConeEquiv (coneDiscreteComp X)).toFun
  simp only [coneDiscreteComp_obj_mapCone]
  apply Limits.IsLimit.ofIsoLimit _ (asIso (piTopToPiCone X)).symm
  exact Grpd.piLimitFanIsLimit _

end Preserves

end Pi

section Prod

variable (A : TopCat.{u}) (B : TopCat.{v})

/--
Definition of `projLeft` / `projLeft` 的定义

English:
definition projLeft
  signature: : πₓ (TopCat.of (A × B)) ⥤ πₓ A
  body: FundamentalGroupoid.map .fst

中文:
定义 projLeft
  签名: : πₓ (顶元素范畴.of (A × B)) ⥤ πₓ A
  定义体: FundamentalGroupoid.map .fst

Depends on / 依赖: FundamentalGroupoid, FundamentalGroupoid.map
-/
def projLeft : πₓ (TopCat.of (A × B)) ⥤ πₓ A :=
  FundamentalGroupoid.map .fst

/--
Definition of `projRight` / `projRight` 的定义

English:
definition projRight
  signature: : πₓ (TopCat.of (A × B)) ⥤ πₓ B
  body: FundamentalGroupoid.map .snd

@[simp]

中文:
定义 projRight
  签名: : πₓ (顶元素范畴.of (A × B)) ⥤ πₓ B
  定义体: FundamentalGroupoid.map .snd

@[simp]

Depends on / 依赖: FundamentalGroupoid, FundamentalGroupoid.map
-/
def projRight : πₓ (TopCat.of (A × B)) ⥤ πₓ B :=
  FundamentalGroupoid.map .snd

@[simp]
/--
theorem `projLeft_map` / 定理 `projLeft_map`

English:
theorem projLeft_map
  given: (x₀ x₁ : πₓ (TopCat.of (A × B))) (p : x₀ ⟶ x₁)
  proof: rfl

@[simp]

中文:
定理 projLeft_map
  条件: (x₀ x₁ : πₓ (顶元素范畴.of (A × B))) (p : x₀ ⟶ x₁)
  证明: rfl

@[simp]
-/
theorem projLeft_map (x₀ x₁ : πₓ (TopCat.of (A × B))) (p : x₀ ⟶ x₁) :
    (projLeft A B).map p = Path.Homotopic.projLeft p :=
  rfl

@[simp]
/--
theorem `projRight_map` / 定理 `projRight_map`

English:
theorem projRight_map
  given: (x₀ x₁ : πₓ (TopCat.of (A × B))) (p : x₀ ⟶ x₁)
  proof: rfl

中文:
定理 projRight_map
  条件: (x₀ x₁ : πₓ (顶元素范畴.of (A × B))) (p : x₀ ⟶ x₁)
  证明: rfl
-/
theorem projRight_map (x₀ x₁ : πₓ (TopCat.of (A × B))) (p : x₀ ⟶ x₁) :
    (projRight A B).map p = Path.Homotopic.projRight p :=
  rfl

/--
The map taking the product of two fundamental groupoids to the fundamental groupoid of the product
of the two topological spaces. This is in fact an isomorphism (see `prodIso`).
-/
@[simps obj]
/--
Definition of `prodToProdTop` / `prodToProdTop` 的定义

English:
definition prodToProdTop
  signature: : πₓ A × πₓ B ⥤ πₓ (TopCat.of (A × B)) where
  body: ⟨g.fst.as, g.snd.as⟩
  map {x y} p :=
    match x, y, p with
    | (_, _), (_, _), (p₀, p₁) => @Path.Homotopic.prod _ _ (_) (_) _ _ _ _ p₀ p₁
  map_id := by
    rintro ⟨x₀, x₁⟩
    simp only
    rfl
  map_comp {x y z} f g :=
    match x, y, z, f, g with
    | (_, _), (_, _), (_, _), (f₀, f₁), (g₀, g₁) =>
      (Path.Homotopic.comp_prod_eq_prod_comp f₀ f₁ g₀ g₁).symm

中文:
定义 prodToProdTop
  签名: : πₓ A × πₓ B ⥤ πₓ (顶元素范畴.of (A × B)) where
  定义体: ⟨g.fst.as, g.snd.as⟩
  map {x y} p :=
    match x, y, p with
    | (_, _), (_, _), (p₀, p₁) => @Path.Homotopic.prod _ _ (_) (_) _ _ _ _ p₀ p₁
  map_id := by
    rintro ⟨x₀, x₁⟩
    simp only
    rfl
  map_comp {x y z} f g :=
    match x, y, z, f, g with
    | (_, _), (_, _), (_, _), (f₀, f₁), (g₀, g₁) =>
      (Path.Homotopic.comp_prod_eq_prod_comp f₀ f₁ g₀ g₁).symm

Depends on / 依赖: g.fst.as, g.snd.as
-/
def prodToProdTop : πₓ A × πₓ B ⥤ πₓ (TopCat.of (A × B)) where
  obj g := ⟨g.fst.as, g.snd.as⟩
  map {x y} p :=
    match x, y, p with
    | (_, _), (_, _), (p₀, p₁) => @Path.Homotopic.prod _ _ (_) (_) _ _ _ _ p₀ p₁
  map_id := by
    rintro ⟨x₀, x₁⟩
    simp only
    rfl
  map_comp {x y z} f g :=
    match x, y, z, f, g with
    | (_, _), (_, _), (_, _), (f₀, f₁), (g₀, g₁) =>
      (Path.Homotopic.comp_prod_eq_prod_comp f₀ f₁ g₀ g₁).symm

/--
theorem `prodToProdTop_map` / 定理 `prodToProdTop_map`

English:
theorem prodToProdTop_map
  given: {x₀ x₁ : πₓ A} {y₀ y₁ : πₓ B} (p₀ : x₀ ⟶ x₁) (p₁ : y₀ ⟶ y₁)
  proof: rfl

中文:
定理 prodToProdTop_map
  条件: {x₀ x₁ : πₓ A} {y₀ y₁ : πₓ B} (p₀ : x₀ ⟶ x₁) (p₁ : y₀ ⟶ y₁)
  证明: rfl
-/
theorem prodToProdTop_map {x₀ x₁ : πₓ A} {y₀ y₁ : πₓ B} (p₀ : x₀ ⟶ x₁) (p₁ : y₀ ⟶ y₁) :
    (prodToProdTop A B).map (X := (x₀, y₀)) (Y := (x₁, y₁)) (p₀, p₁) =
      Path.Homotopic.prod p₀ p₁ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Shows `prodToProdTop` is an isomorphism, whose inverse is precisely the product
of the induced left and right projections.
-/
@[simps]
/--
Definition of `prodIso` / `prodIso` 的定义

English:
definition prodIso
  signature: : CategoryTheory.Grpd.of (πₓ A × πₓ B) ≅ πₓ (TopCat.of (A × B)) where
  body: prodToProdTop A B
  inv := (projLeft A B).prod' (projRight A B)
  hom_inv_id := by
    change prodToProdTop A B ⋙ (projLeft A B).prod' (projRight A B) = 𝟭 _
    apply CategoryTheory.Functor.hext; · intros; ext <;> simp <;> rfl
    rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ ⟨f₀, f₁⟩
    have : Path.Homotopic.projLeft ((prodToProdTop A B).map (f₀, f₁)) = f₀ ∧
      Path.Homotopic.projRight ((prodToProdTop A B).map (f₀, f₁)) = f₁ :=
        And.intro (Path.Homotopic.projLeft_prod f₀ f₁) (Path.Homotopic.projRight_prod f₀ f₁)
    cat_disch
  inv_hom_id := by
    change (projLeft A B).prod' (projRight A B) ⋙ prodToProdTop A B = 𝟭 _
    apply CategoryTheory.Functor.hext
    · intros; apply FundamentalGroupoid.ext; apply Prod.ext <;> simp <;> rfl
    rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ f
    simpa [-Path.Homotopic.prod_projLeft_projRight] using! Path.Homotopic.prod_projLeft_projRight f

中文:
定义 prodIso
  签名: : 范畴论.Grpd.of (πₓ A × πₓ B) ≅ πₓ (顶元素范畴.of (A × B)) where
  定义体: prodToProdTop A B
  inv := (projLeft A B).prod' (projRight A B)
  hom_inv_id := by
    change prodToProdTop A B ⋙ (projLeft A B).prod' (projRight A B) = 𝟭 _
    apply CategoryTheory.Functor.hext; · intros; ext <;> simp <;> rfl
    rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ ⟨f₀, f₁⟩
    have : Path.Homotopic.projLeft ((prodToProdTop A B).map (f₀, f₁)) = f₀ ∧
      Path.Homotopic.projRight ((prodToProdTop A B).map (f₀, f₁)) = f₁ :=
        And.intro (Path.Homotopic.projLeft_prod f₀ f₁) (Path.Homotopic.projRight_prod f₀ f₁)
    cat_disch
  inv_hom_id := by
    change (projLeft A B).prod' (projRight A B) ⋙ prodToProdTop A B = 𝟭 _
    apply CategoryTheory.Functor.hext
    · intros; apply FundamentalGroupoid.ext; apply Prod.ext <;> simp <;> rfl
    rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ f
    simpa [-Path.Homotopic.prod_projLeft_projRight] using! Path.Homotopic.prod_projLeft_projRight f

Depends on / 依赖: prodToProdTop
-/
def prodIso : CategoryTheory.Grpd.of (πₓ A × πₓ B) ≅ πₓ (TopCat.of (A × B)) where
  hom := prodToProdTop A B
  inv := (projLeft A B).prod' (projRight A B)
  hom_inv_id := by
    change prodToProdTop A B ⋙ (projLeft A B).prod' (projRight A B) = 𝟭 _
    apply CategoryTheory.Functor.hext; · intros; ext <;> simp <;> rfl
    rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ ⟨f₀, f₁⟩
    have : Path.Homotopic.projLeft ((prodToProdTop A B).map (f₀, f₁)) = f₀ ∧
      Path.Homotopic.projRight ((prodToProdTop A B).map (f₀, f₁)) = f₁ :=
        And.intro (Path.Homotopic.projLeft_prod f₀ f₁) (Path.Homotopic.projRight_prod f₀ f₁)
    cat_disch
  inv_hom_id := by
    change (projLeft A B).prod' (projRight A B) ⋙ prodToProdTop A B = 𝟭 _
    apply CategoryTheory.Functor.hext
    · intros; apply FundamentalGroupoid.ext; apply Prod.ext <;> simp <;> rfl
    rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ f
    simpa [-Path.Homotopic.prod_projLeft_projRight] using! Path.Homotopic.prod_projLeft_projRight f

end Prod

end FundamentalGroupoidFunctor
