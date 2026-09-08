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

variable {I : Type u} (X : I → TopCat.{u})

/-- The projection map Π i, X i → X i induces a map π(Π i, X i) ⟶ π(X i).
-/
/-
**FundamentalGroupoidFunctor.proj** 是 Mathlib 中的一个定义，位于命名空间 `FundamentalGroupoid
Functor`。
形式化陈述：proj (i : I) : πₓ (TopCat.of (forall i, X i)) ⥤ πₓ (X i)
参数：i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection map Π i, X i → X i induces a map π(Π i, X i) ⟶ π(X i).
-/
def proj (i : I) : πₓ (TopCat.of (∀ i, X i)) ⥤ πₓ (X i) :=
  πₘ (TopCat.ofHom ⟨_, continuous_apply i⟩)

/-- The projection map is precisely `Path.Homotopic.proj` interpreted as a functor -/
@[simp]
/-
**FundamentalGroupoidFunctor.proj_map** 是 Mathlib 中的一个定理，位于命名空间 `FundamentalGrou
poidFunctor`。
形式化陈述：proj_map (i : I) (x₀ x₁ : πₓ (TopCat.of (forall i, X i))) (p : x₀ ⟶ x₁) : 
(proj X i).map p = @Path.Homotopic.proj _ _ _ _ _ i p
参数：i : I；x₀ x₁ : πₓ (TopCat.of (forall i, X i))；p : x₀ ⟶ x₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection map is precisely `Path.Homotopic.proj` interpreted as a functor
-/
theorem proj_map (i : I) (x₀ x₁ : πₓ (TopCat.of (∀ i, X i))) (p : x₀ ⟶ x₁) :
    (proj X i).map p = @Path.Homotopic.proj _ _ _ _ _ i p :=
  rfl

/-- The map taking the pi product of a family of fundamental groupoids to the fundamental
groupoid of the pi product. This is actually an isomorphism (see `piIso`)
-/
@[simps]
/-
**FundamentalGroupoidFunctor.piToPiTop** 是 Mathlib 中的一个定义，位于命名空间 `FundamentalGro
upoidFunctor`。
形式化陈述：piToPiTop : (forall i, πₓ (X i)) ⥤ πₓ (TopCat.of (forall i, X i)) where ob
j g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map taking the pi product of a family of fundamental groupoids to the fundam
ental
groupoid of the pi product. This is actually an isomorphism (see `piIso`)
-/
def piToPiTop : (∀ i, πₓ (X i)) ⥤ πₓ (TopCat.of (∀ i, X i)) where
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
/-
**FundamentalGroupoidFunctor.piIso** 是 Mathlib 中的一个定义，位于命名空间 `FundamentalGroupoi
dFunctor`。
形式化陈述：piIso : CategoryTheory.Grpd.of (forall i : I, πₓ (X i)) ≅ πₓ (TopCat.of (f
orall i, X i)) where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shows `piToPiTop` is an isomorphism, whose inverse is precisely the pi product
of the induced projections. This shows that `fundamentalGroupoidFunctor` preserv
es products.
-/
def piIso : CategoryTheory.Grpd.of (∀ i : I, πₓ (X i)) ≅ πₓ (TopCat.of (∀ i, X i)) where
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

/-- Equivalence between the categories of cones over the objects `π Xᵢ` written in two ways -/
/-
**FundamentalGroupoidFunctor.coneDiscreteComp** 是 Mathlib 中的一个定义，位于命名空间 `Fundame
ntalGroupoidFunctor`。
形式化陈述：coneDiscreteComp : Limits.Cone (Discrete.functor X ⋙ π) ≌ Limits.Cone (Dis
crete.functor fun i => πₓ (X i))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between the categories of cones over the objects `π Xᵢ` written in t
wo ways
-/
def coneDiscreteComp :
    Limits.Cone (Discrete.functor X ⋙ π) ≌ Limits.Cone (Discrete.functor fun i => πₓ (X i)) :=
  Limits.Cone.postcomposeEquivalence (Discrete.compNatIsoDiscrete X π)
/-
**FundamentalGroupoidFunctor.coneDiscreteComp_obj_mapCone** 是 Mathlib 中的一个定理，位于命
名空间 `FundamentalGroupoidFunctor`。
形式化陈述：coneDiscreteComp_obj_mapCone : (coneDiscreteComp X).functor.obj (Functor.m
apCone π (TopCat.piFan X)) = Limits.Fan.mk (πₓ (TopCat.of (forall i, X i))) (pro
j X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coneDiscreteComp_obj_mapCone :
    (coneDiscreteComp X).functor.obj (Functor.mapCone π (TopCat.piFan X)) =
      Limits.Fan.mk (πₓ (TopCat.of (∀ i, X i))) (proj X) :=
  rfl

/-- This is `piIso.inv` as a cone morphism (in fact, isomorphism) -/
/-
**FundamentalGroupoidFunctor.piTopToPiCone** 是 Mathlib 中的一个定义，位于命名空间 `Fundamenta
lGroupoidFunctor`。
形式化陈述：piTopToPiCone : Limits.Fan.mk (πₓ (TopCat.of (forall i, X i))) (proj X) ⟶ 
Grpd.piLimitFan fun i : I => πₓ (X i) where hom
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is `piIso.inv` as a cone morphism (in fact, isomorphism)
-/
def piTopToPiCone :
    Limits.Fan.mk (πₓ (TopCat.of (∀ i, X i))) (proj X) ⟶ Grpd.piLimitFan fun i : I => πₓ (X i) where
  hom := CategoryTheory.Functor.pi' (proj X)
/-
**FundamentalGroupoidFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `FundamentalGroupoidFunc
tor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (piTopToPiCone X) :=
  haveI : IsIso (piTopToPiCone X).hom := (inferInstance : IsIso (piIso X).inv)
  Limits.Cone.cone_iso_of_hom_iso (piTopToPiCone X)

/-- The fundamental groupoid functor preserves products -/
/-
**FundamentalGroupoidFunctor.preservesProduct** 是 Mathlib 中的一个引理，位于命名空间 `Fundame
ntalGroupoidFunctor`。
形式化陈述：preservesProduct : Limits.PreservesLimit (Discrete.functor X) π
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `FundamentalGroupoidFunctor.instIsIsoFanGrpdObjTopCatFundamentalGroupoidF
unctorPiTopToPiCone`：∀ {I : Type u} (X : I → TopCat), CategoryTheory.IsIso (Fund
amentalGroupoidFunctor.piTopToPiCone X)

--- 原说明 ---
The fundamental groupoid functor preserves products
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

/-- The induced map of the left projection map X × Y → X -/
/-
**FundamentalGroupoidFunctor.projLeft** 是 Mathlib 中的一个定义，位于命名空间 `FundamentalGrou
poidFunctor`。
形式化陈述：projLeft : πₓ (TopCat.of (A × B)) ⥤ πₓ A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map of the left projection map X × Y → X
-/
def projLeft : πₓ (TopCat.of (A × B)) ⥤ πₓ A :=
  FundamentalGroupoid.map .fst

/-- The induced map of the right projection map X × Y → Y -/
/-
**FundamentalGroupoidFunctor.projRight** 是 Mathlib 中的一个定义，位于命名空间 `FundamentalGro
upoidFunctor`。
形式化陈述：projRight : πₓ (TopCat.of (A × B)) ⥤ πₓ B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map of the right projection map X × Y → Y
-/
def projRight : πₓ (TopCat.of (A × B)) ⥤ πₓ B :=
  FundamentalGroupoid.map .snd

@[simp]
/-
**FundamentalGroupoidFunctor.projLeft_map** 是 Mathlib 中的一个定理，位于命名空间 `Fundamental
GroupoidFunctor`。
形式化陈述：projLeft_map (x₀ x₁ : πₓ (TopCat.of (A × B))) (p : x₀ ⟶ x₁) : (projLeft A 
B).map p = Path.Homotopic.projLeft p
参数：x₀ x₁ : πₓ (TopCat.of (A × B))；p : x₀ ⟶ x₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem projLeft_map (x₀ x₁ : πₓ (TopCat.of (A × B))) (p : x₀ ⟶ x₁) :
    (projLeft A B).map p = Path.Homotopic.projLeft p :=
  rfl

@[simp]
/-
**FundamentalGroupoidFunctor.projRight_map** 是 Mathlib 中的一个定理，位于命名空间 `Fundamenta
lGroupoidFunctor`。
形式化陈述：projRight_map (x₀ x₁ : πₓ (TopCat.of (A × B))) (p : x₀ ⟶ x₁) : (projRight 
A B).map p = Path.Homotopic.projRight p
参数：x₀ x₁ : πₓ (TopCat.of (A × B))；p : x₀ ⟶ x₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem projRight_map (x₀ x₁ : πₓ (TopCat.of (A × B))) (p : x₀ ⟶ x₁) :
    (projRight A B).map p = Path.Homotopic.projRight p :=
  rfl

/--
The map taking the product of two fundamental groupoids to the fundamental groupoid of the product
of the two topological spaces. This is in fact an isomorphism (see `prodIso`).
-/
@[simps obj]
/-
**FundamentalGroupoidFunctor.prodToProdTop** 是 Mathlib 中的一个定义，位于命名空间 `Fundamenta
lGroupoidFunctor`。
形式化陈述：prodToProdTop : πₓ A × πₓ B ⥤ πₓ (TopCat.of (A × B)) where obj g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map taking the product of two fundamental groupoids to the fundamental group
oid of the product
of the two topological spaces. This is in fact an isomorphism (see `prodIso`).
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
/-
**FundamentalGroupoidFunctor.prodToProdTop_map** 是 Mathlib 中的一个定理，位于命名空间 `Fundam
entalGroupoidFunctor`。
形式化陈述：prodToProdTop_map {x₀ x₁ : πₓ A} {y₀ y₁ : πₓ B} (p₀ : x₀ ⟶ x₁) (p₁ : y₀ ⟶ 
y₁) : (prodToProdTop A B).map (X
参数：p₀ : x₀ ⟶ x₁；p₁ : y₀ ⟶ y₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**FundamentalGroupoidFunctor.prodIso** 是 Mathlib 中的一个定义，位于命名空间 `FundamentalGroup
oidFunctor`。
形式化陈述：prodIso : CategoryTheory.Grpd.of (πₓ A × πₓ B) ≅ πₓ (TopCat.of (A × B)) wh
ere hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shows `prodToProdTop` is an isomorphism, whose inverse is precisely the product
of the induced left and right projections.
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

