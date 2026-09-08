/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Affine schemes

We define the category of `AffineScheme`s as the essential image of `Spec`.
We also define predicates about affine schemes and affine open sets.

## Main definitions

* `AlgebraicGeometry.AffineScheme`: The category of affine schemes.
* `AlgebraicGeometry.IsAffine`: A scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an
  isomorphism.
* `AlgebraicGeometry.Scheme.isoSpec`: The canonical isomorphism `X ≅ Spec Γ(X)` for an affine
  scheme.
* `AlgebraicGeometry.AffineScheme.equivCommRingCat`: The equivalence of categories
  `AffineScheme ≌ CommRingᵒᵖ` given by `AffineScheme.Spec : CommRingᵒᵖ ⥤ AffineScheme` and
  `AffineScheme.Γ : AffineSchemeᵒᵖ ⥤ CommRingCat`.
* `AlgebraicGeometry.IsAffineOpen`: An open subset of a scheme is affine if the open subscheme is
  affine.
* `AlgebraicGeometry.IsAffineOpen.fromSpec`: The immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`.

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open Spec (structureSheaf)

/-- The category of affine schemes -/
/-
**AlgebraicGeometry.AffineScheme** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：AffineScheme
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of affine schemes
-/
def AffineScheme :=
  Scheme.Spec.EssImageSubcategory
deriving Category

/-- A Scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an isomorphism. -/
/-
**AlgebraicGeometry.IsAffine** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeometry`。
形式化陈述：AlgebraicGeometry.Scheme → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an isomorphism.
-/
class IsAffine (X : Scheme) : Prop where
  affine : IsIso X.toSpecΓ

attribute [instance] IsAffine.affine
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Scheme.{u}) [IsAffine X] : IsIso (ΓSpec.adjunction.unit.app X) := @IsAffine.affine X _

/-- The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme. -/
@[simps! -isSimp hom]
/-
**AlgebraicGeometry.Scheme.isoSpec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.
Scheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) →   [AlgebraicGeometry.IsAffine X] → X ≅ Al
gebraicGeometry.Spec (X.presheaf.obj (Opposite.op ⊤))
参数：Opposite.op ⊤。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffine.affine`：∀ {X : AlgebraicGeometry.Scheme} [sel
f : AlgebraicGeometry.IsAffine X], CategoryTheory.IsIso X.toSpecΓ

--- 原说明 ---
The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme.
-/
def Scheme.isoSpec (X : Scheme) [IsAffine X] : X ≅ Spec Γ(X, ⊤) :=
  asIso X.toSpecΓ

@[reassoc]
/-
**AlgebraicGeometry.Scheme.isoSpec_hom_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} [inst : AlgebraicGeometry.IsAffine X] [
inst_1 : AlgebraicGeometry.IsAffine Y]   (f : X ⟶ Y),   CategoryTheory.CategoryS
truct.comp X.isoSpec.hom       (AlgebraicGeometry.Spec.map (AlgebraicGeometry.Sc
heme.Hom.appTop f)) =     CategoryTheory.CategoryStruct.comp f Y.isoSpec.hom
参数：f : X ⟶ Y；AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.Hom.appTop f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_naturality`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp f Y.toSpecΓ =     Cate
goryTheory.CategoryStruct.comp X.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Scheme.isoSpec_hom_naturality {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    X.isoSpec.hom ≫ Spec.map (f.appTop) = f ≫ Y.isoSpec.hom := by
  simp only [isoSpec, asIso_hom, Scheme.toSpecΓ_naturality]

@[reassoc]
/-
**AlgebraicGeometry.Scheme.isoSpec_inv_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} [inst : AlgebraicGeometry.IsAffine X] [
inst_1 : AlgebraicGeometry.IsAffine Y]   (f : X ⟶ Y),   CategoryTheory.CategoryS
truct.comp (AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.Hom.appTop f)) 
      Y.isoSpec.inv =     CategoryTheory.CategoryStruct.comp X.isoSpec.inv f
参数：f : X ⟶ Y；AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.Hom.appTop f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `AlgebraicGeometry.IsAffine.affine`：∀ {X : AlgebraicGeometry.Scheme} [sel
f : AlgebraicGeometry.IsAffine X], CategoryTheory.IsIso X.toSpecΓ
· 使用定理 `AlgebraicGeometry.Scheme.isoSpec.eq_1`：∀ (X : AlgebraicGeometry.Scheme) 
[inst : AlgebraicGeometry.IsAffine X], X.isoSpec = CategoryTheory.asIso X.toSpec
Γ
· 使用定理 `CategoryTheory.asIso_hom`：asIso_hom (f : X ⟶ Y) [IsIso f] : (asIso f).ho
m = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_naturality_assoc`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) {Z : AlgebraicGeometry.Scheme}   (h : AlgebraicGeometr
y.Spec (Y.presheaf.obj (Opposite.op ⊤))…
· 使用定理 `CategoryTheory.asIso_inv`：asIso_inv (f : X ⟶ Y) [IsIso f] : (asIso f).in
v = inv f
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem Scheme.isoSpec_inv_naturality {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Spec.map (f.appTop) ≫ Y.isoSpec.inv = X.isoSpec.inv ≫ f := by
  rw [Iso.eq_inv_comp, isoSpec, asIso_hom, ← Scheme.toSpecΓ_naturality_assoc, isoSpec,
    asIso_inv, IsIso.hom_inv_id, Category.comp_id]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.toSpecΓ_isoSpec_inv (X : Scheme.{u}) [IsAffine X] :
    X.toSpecΓ ≫ X.isoSpec.inv = 𝟙 _ :=
  X.isoSpec.hom_inv_id

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.isoSpec_inv_toSpec** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.isoSpec_inv_toSpecΓ (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv ≫ X.toSpecΓ = 𝟙 _ :=
  X.isoSpec.inv_hom_id

/-- Construct an affine scheme from a scheme and the information that it is affine.
Also see `AffineScheme.of` for a typeclass version. -/
@[simps]
/-
**AlgebraicGeometry.AffineScheme.mk** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry
.AffineScheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → AlgebraicGeometry.IsAffine X → AlgebraicG
eometry.AffineScheme
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an affine scheme from a scheme and the information that it is affine.
Also see `AffineScheme.of` for a typeclass version.
-/
def AffineScheme.mk (X : Scheme) (_ : IsAffine X) : AffineScheme :=
  ⟨X, ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩

/-- Construct an affine scheme from a scheme. Also see `AffineScheme.mk` for a non-typeclass
version. -/
/-
**AlgebraicGeometry.AffineScheme.of** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry
.AffineScheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → [h : AlgebraicGeometry.IsAffine X] → Alge
braicGeometry.AffineScheme
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an affine scheme from a scheme. Also see `AffineScheme.mk` for a non-t
ypeclass
version.
-/
def AffineScheme.of (X : Scheme) [h : IsAffine X] : AffineScheme :=
  AffineScheme.mk X h

/-- Type check a morphism of schemes as a morphism in `AffineScheme`. -/
/-
**AlgebraicGeometry.AffineScheme.ofHom** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.AffineScheme`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} →   [inst : AlgebraicGeometry.IsAffine X]
 →     [inst_1 : AlgebraicGeometry.IsAffine Y] →       (X ⟶ Y) → (AlgebraicGeome
try.AffineScheme.of X ⟶ AlgebraicGeometry.AffineScheme.of Y)
参数：X ⟶ Y；AlgebraicGeometry.AffineScheme.of X ⟶ AlgebraicGeometry.AffineScheme.of
 Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type check a morphism of schemes as a morphism in `AffineScheme`.
-/
def AffineScheme.ofHom {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    AffineScheme.of X ⟶ AffineScheme.of Y :=
  InducedCategory.homMk f

@[simp]
/-
**AlgebraicGeometry.essImage_Spec** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：essImage_Spec {X : Scheme} : Scheme.Spec.essImage X ↔ IsAffine X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.essImage.unit_isIso`：∀ {C : Type u₁} {D : Type u₂
} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {i : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.mem_essImage_of_unit_isIso`：mem_essImage_of_un
it_isIso (A : C) [IsIso (h.unit.app A)] : R.essImage A
· 使用定理 `AlgebraicGeometry.instIsIsoSchemeAppUnitOppositeCommRingCatAdjunctionOfI
sAffine`：∀ (X : AlgebraicGeometry.Scheme) [AlgebraicGeometry.IsAffine X],   Cate
goryTheory.IsIso (AlgebraicGeometry.ΓSpec.adjunction.unit.app X)
-/
theorem essImage_Spec {X : Scheme} : Scheme.Spec.essImage X ↔ IsAffine X :=
  ⟨fun h => ⟨Functor.essImage.unit_isIso h⟩,
    fun _ => ΓSpec.adjunction.mem_essImage_of_unit_isIso _⟩
/-
**AlgebraicGeometry.isAffine_affineScheme** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：isAffine_affineScheme (X : AffineScheme.{u}) : IsAffine X.obj
参数：X : AffineScheme.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.essImage.unit_isIso`：∀ {C : Type u₁} {D : Type u₂
} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {i : CategoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
instance isAffine_affineScheme (X : AffineScheme.{u}) : IsAffine X.obj :=
  ⟨Functor.essImage.unit_isIso X.property⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : CommRingCatᵒᵖ) : IsAffine (Scheme.Spec.obj R) :=
  AlgebraicGeometry.isAffine_affineScheme ⟨_, Scheme.Spec.obj_mem_essImage R⟩
/-
**AlgebraicGeometry.isAffine_Spec** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isAffine_Spec (R : CommRingCat) : IsAffine (Spec R)
参数：R : CommRingCat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.obj_mem_essImage`：obj_mem_essImage (F : D ⥤ C) (Y
 : D) : essImage F (F.obj Y)
-/
instance isAffine_Spec (R : CommRingCat) : IsAffine (Spec R) :=
  AlgebraicGeometry.isAffine_affineScheme ⟨_, Scheme.Spec.obj_mem_essImage (op R)⟩
/-
**AlgebraicGeometry.IsAffine.of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry.IsAffine`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f] [h
 : AlgebraicGeometry.IsAffine Y],   AlgebraicGeometry.IsAffine X
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.essImage_Spec`：essImage_Spec {X : Scheme} : Scheme.Spe
c.essImage X ↔ IsAffine X
· 使用定理 `CategoryTheory.Functor.essImage.ofIso`：∀ {C : Type u₁} {D : Type u₂} [in
st : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {F : CategoryTheor…
-/
theorem IsAffine.of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] [h : IsAffine Y] : IsAffine X := by
  rw [← essImage_Spec] at h ⊢; exact Functor.essImage.ofIso (asIso f).symm h
/-
**AlgebraicGeometry.IsAffine.iff_of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.IsAffine`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 AlgebraicGeometry.IsAffine X ↔ AlgebraicGeometry.IsAffine Y
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
-/
theorem IsAffine.iff_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsAffine X ↔ IsAffine Y :=
  ⟨fun _ ↦ .of_isIso (inv f), fun _ ↦ .of_isIso f⟩

/-- If `f : X ⟶ Y` is a morphism between affine schemes, the corresponding arrow is isomorphic
to the arrow of the morphism on prime spectra induced by the map on global sections. -/
noncomputable
/-
**AlgebraicGeometry.arrowIsoSpec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def arrowIsoSpecΓOfIsAffine {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Arrow.mk f ≅ Arrow.mk (Spec.map f.appTop) :=
  Arrow.isoMk X.isoSpec Y.isoSpec (ΓSpec.adjunction.unit_naturality _)

/-- If `f : A ⟶ B` is a ring homomorphism, the corresponding arrow is isomorphic
to the arrow of the morphism induced on global sections by the map on prime spectra. -/
/-
**AlgebraicGeometry.arrowIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : A ⟶ B` is a ring homomorphism, the corresponding arrow is isomorphic
to the arrow of the morphism induced on global sections by the map on prime spec
tra.
-/
def arrowIsoΓSpecOfIsAffine {A B : CommRingCat} (f : A ⟶ B) :
    Arrow.mk f ≅ Arrow.mk ((Spec.map f).appTop) :=
  Arrow.isoMk (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
    (Scheme.ΓSpecIso_inv_naturality f).symm
/-
**AlgebraicGeometry.Scheme.isoSpec_Spec** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.Scheme`。
形式化陈述：∀ (R : CommRingCat),   (AlgebraicGeometry.Spec R).isoSpec = AlgebraicGeome
try.Scheme.Spec.mapIso (AlgebraicGeometry.Scheme.ΓSpecIso R).op
参数：R : CommRingCat；AlgebraicGeometry.Spec R；AlgebraicGeometry.Scheme.ΓSpecIso R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.SpecMap_ΓSpecIso_hom`：SpecMap_ΓSpecIso_hom (R : CommRi
ngCat.{u}) : Spec.map ((Scheme.ΓSpecIso R).hom) = (Spec R).toSpecΓ
-/
theorem Scheme.isoSpec_Spec (R : CommRingCat.{u}) :
    (Spec R).isoSpec = Scheme.Spec.mapIso (Scheme.ΓSpecIso R).op :=
  Iso.ext (SpecMap_ΓSpecIso_hom R).symm
/-
**AlgebraicGeometry.Scheme.isoSpec_Spec_hom** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：∀ (R : CommRingCat),   (AlgebraicGeometry.Spec R).isoSpec.hom = AlgebraicG
eometry.Spec.map (AlgebraicGeometry.Scheme.ΓSpecIso R).hom
参数：R : CommRingCat；AlgebraicGeometry.Spec R；AlgebraicGeometry.Scheme.ΓSpecIso R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.SpecMap_ΓSpecIso_hom`：SpecMap_ΓSpecIso_hom (R : CommRi
ngCat.{u}) : Spec.map ((Scheme.ΓSpecIso R).hom) = (Spec R).toSpecΓ
-/
@[simp] theorem Scheme.isoSpec_Spec_hom (R : CommRingCat.{u}) :
    (Spec R).isoSpec.hom = Spec.map (Scheme.ΓSpecIso R).hom :=
  (SpecMap_ΓSpecIso_hom R).symm
/-
**AlgebraicGeometry.Scheme.isoSpec_Spec_inv** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：∀ (R : CommRingCat),   (AlgebraicGeometry.Spec R).isoSpec.inv = AlgebraicG
eometry.Spec.map (AlgebraicGeometry.Scheme.ΓSpecIso R).inv
参数：R : CommRingCat；AlgebraicGeometry.Spec R；AlgebraicGeometry.Scheme.ΓSpecIso R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.isoSpec_Spec`：∀ (R : CommRingCat),   (Algebraic
Geometry.Spec R).isoSpec = AlgebraicGeometry.Scheme.Spec.mapIso (AlgebraicGeomet
ry.Scheme.ΓSpecIso R).op
-/
@[simp] theorem Scheme.isoSpec_Spec_inv (R : CommRingCat.{u}) :
    (Spec R).isoSpec.inv = Spec.map (Scheme.ΓSpecIso R).inv :=
  congr($(isoSpec_Spec R).inv)
/-
**AlgebraicGeometry.ext_of_isAffine** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry
`。
形式化陈述：ext_of_isAffine {X Y : Scheme} [IsAffine Y] {f g : X ⟶ Y} (e : f.appTop = 
g.appTop) : f = g
参数：e : f.appTop = g.appTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `AlgebraicGeometry.IsAffine.affine`：∀ {X : AlgebraicGeometry.Scheme} [sel
f : AlgebraicGeometry.IsAffine X], CategoryTheory.IsIso X.toSpecΓ
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_naturality`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp f Y.toSpecΓ =     Cate
goryTheory.CategoryStruct.comp X.…
-/
lemma ext_of_isAffine {X Y : Scheme} [IsAffine Y] {f g : X ⟶ Y} (e : f.appTop = g.appTop) :
    f = g := by
  rw [← cancel_mono Y.toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, e]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : MorphismProperty Scheme.{u}) {S : Scheme.{u}} (𝒰 : S.AffineCover P) (i : 𝒰.I₀) :
    IsAffine (𝒰.cover.X i) :=
  inferInstanceAs <| IsAffine (Spec _)

/-- `Scheme.Γ.rightOp : Scheme ⥤ CommRingCatᵒᵖ` preserves limits of diagrams consisting of
affine schemes. -/
/-
**AlgebraicGeometry.preservesLimit_rightOp_** 是 Mathlib 中的一个实例，位于命名空间 `Algebraic
Geometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Scheme.Γ.rightOp : Scheme ⥤ CommRingCatᵒᵖ` preserves limits of diagrams consist
ing of
affine schemes.
-/
instance preservesLimit_rightOp_Γ.{v, w}
    {I : Type w} [Category.{v} I] (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] :
    PreservesLimit D Scheme.Γ.rightOp := by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  have (i : _) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  suffices PreservesLimit ((D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec) Scheme.Γ.rightOp from
    preservesLimit_of_iso_diagram _ (asIso α).symm
  have := monadicCreatesLimits.{v, w} Scheme.Spec.{u}
  suffices PreservesLimit (D ⋙ Scheme.Γ.rightOp) (Scheme.Spec ⋙ Scheme.Γ.rightOp) from
    preservesLimit_comp_of_createsLimit _ _
  exact preservesLimit_of_natIso _ (NatIso.op Scheme.SpecΓIdentity)

/-- `Scheme.Γ : Schemeᵒᵖ ⥤ CommRingCat` preserves colimits of diagrams consisting of
affine schemes. -/
/-
**AlgebraicGeometry.preservesColimit_** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Scheme.Γ : Schemeᵒᵖ ⥤ CommRingCat` preserves colimits of diagrams consisting of
affine schemes.
-/
instance preservesColimit_Γ.{v, w}
    {I : Type w} [Category.{v} I] (D : I ⥤ Scheme.{u}ᵒᵖ) [∀ i, IsAffine (D.obj i).unop] :
    PreservesColimit D Scheme.Γ := by
  have (i : _) : IsAffine (D.leftOp.obj i) := Functor.leftOp_obj D _ ▸ inferInstance
  exact preservesColimit_of_rightOp D Scheme.Γ

namespace AffineScheme

/-- The `Spec` functor into the category of affine schemes. -/
/-
**AlgebraicGeometry.AffineScheme.Spec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.AffineScheme`。
形式化陈述：Spec : CommRingCatᵒᵖ ⥤ AffineScheme
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Spec` functor into the category of affine schemes.
-/
def Spec : CommRingCatᵒᵖ ⥤ AffineScheme :=
  Scheme.Spec.toEssImage

/-! We copy over instances from `Scheme.Spec.toEssImage`. -/

/-
**AlgebraicGeometry.AffineScheme.Spec_full** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.AffineScheme`。
形式化陈述：Spec_full : Spec.Full
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Full.toEssImage`：∀ {C : Type u₁} {D : Type u₂} [i
nst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   (F : CategoryTheor…
· 使用定理 `AlgebraicGeometry.Spec.full`：AlgebraicGeometry.Scheme.Spec.Full

--- 原说明 ---
We copy over instances from `Scheme.Spec.toEssImage`.
-/
instance Spec_full : Spec.Full := Functor.Full.toEssImage _
/-
**AlgebraicGeometry.AffineScheme.Spec_faithful** 是 Mathlib 中的一个实例，位于命名空间 `Algebr
aicGeometry.AffineScheme`。
形式化陈述：Spec_faithful : Spec.Faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Faithful.toEssImage`：∀ {C : Type u₁} {D : Type u₂
} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `AlgebraicGeometry.Spec.faithful`：AlgebraicGeometry.Scheme.Spec.Faithful
-/
instance Spec_faithful : Spec.Faithful := Functor.Faithful.toEssImage _
/-
**AlgebraicGeometry.AffineScheme.Spec_essSurj** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
icGeometry.AffineScheme`。
形式化陈述：Spec_essSurj : Spec.EssSurj
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.toEssImage`：∀ {C : Type u₁} {D : Type u₂}
 [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
-/
instance Spec_essSurj : Spec.EssSurj := Functor.EssSurj.toEssImage (F := _)

/-- The forgetful functor `AffineScheme ⥤ Scheme`. -/
@[simps!]
/-
**AlgebraicGeometry.AffineScheme.forgetToScheme** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.AffineScheme`。
形式化陈述：forgetToScheme : AffineScheme ⥤ Scheme
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor `AffineScheme ⥤ Scheme`.
-/
def forgetToScheme : AffineScheme ⥤ Scheme :=
  Scheme.Spec.essImage.ι

/-! We copy over instances from `Scheme.Spec.essImageInclusion`. -/

/-
**AlgebraicGeometry.AffineScheme.forgetToScheme_full** 是 Mathlib 中的一个实例，位于命名空间 `
AlgebraicGeometry.AffineScheme`。
形式化陈述：forgetToScheme_full : forgetToScheme.Full
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We copy over instances from `Scheme.Spec.essImageInclusion`.
-/
instance forgetToScheme_full : forgetToScheme.Full :=
  inferInstanceAs Scheme.Spec.essImage.ι.Full
/-
**AlgebraicGeometry.AffineScheme.forgetToScheme_faithful** 是 Mathlib 中的一个实例，位于命名
空间 `AlgebraicGeometry.AffineScheme`。
形式化陈述：forgetToScheme_faithful : forgetToScheme.Faithful
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forgetToScheme_faithful : forgetToScheme.Faithful :=
  inferInstanceAs Scheme.Spec.essImage.ι.Faithful

/-- The global section functor of an affine scheme. -/
/-
**AlgebraicGeometry.AffineScheme.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.A
ffineScheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The global section functor of an affine scheme.
-/
def Γ : AffineSchemeᵒᵖ ⥤ CommRingCat :=
  forgetToScheme.op ⋙ Scheme.Γ

/-- The category of affine schemes is equivalent to the category of commutative rings. -/
/-
**AlgebraicGeometry.AffineScheme.equivCommRingCat** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.AffineScheme`。
形式化陈述：equivCommRingCat : AffineScheme ≌ CommRingCatᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of affine schemes is equivalent to the category of commutative ring
s.
-/
def equivCommRingCat : AffineScheme ≌ CommRingCatᵒᵖ :=
  equivEssImageOfReflective.symm
/-
**AlgebraicGeometry.AffineScheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.A
ffineScheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Γ.{u}.rightOp.IsEquivalence := equivCommRingCat.isEquivalence_functor
/-
**AlgebraicGeometry.AffineScheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.A
ffineScheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Γ.{u}.rightOp.op.IsEquivalence := equivCommRingCat.op.isEquivalence_functor
/-
**AlgebraicGeometry.AffineScheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.A
ffineScheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ΓIsEquiv : Γ.{u}.IsEquivalence :=
  inferInstanceAs (Γ.{u}.rightOp.op ⋙ (opOpEquivalence _).functor).IsEquivalence
/-
**AlgebraicGeometry.AffineScheme.hasColimits** 是 Mathlib 中的一个实例，位于命名空间 `Algebrai
cGeometry.AffineScheme`。
形式化陈述：hasColimits : HasColimits AffineScheme.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.has_colimits_of_equivalence`：has_colimits_of_e
quivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfSize.{v, u} D] : HasColim
itsOfSize.{v, u} C
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Adjunction.has_limits_of_equivalence`：has_limits_of_equiv
alence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfSize.{v, u} C] : HasLimitsOfSiz
e.{v, u} D
-/
instance hasColimits : HasColimits AffineScheme.{u} :=
  haveI := Adjunction.has_limits_of_equivalence.{u} Γ.{u}
  Adjunction.has_colimits_of_equivalence.{u} (opOpEquivalence AffineScheme.{u}).inverse
/-
**AlgebraicGeometry.AffineScheme.hasLimits** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.AffineScheme`。
形式化陈述：hasLimits : HasLimits AffineScheme.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.has_colimits_of_equivalence`：has_colimits_of_e
quivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfSize.{v, u} D] : HasColim
itsOfSize.{v, u} C
· 使用定理 `CategoryTheory.Adjunction.has_limits_of_equivalence`：has_limits_of_equiv
alence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfSize.{v, u} C] : HasLimitsOfSiz
e.{v, u} D
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
instance hasLimits : HasLimits AffineScheme.{u} := by
  have := Adjunction.has_colimits_of_equivalence Γ.{u}
  have : HasLimits AffineScheme.{u}ᵒᵖᵒᵖ := Limits.hasLimits_op_of_hasColimits
  exact Adjunction.has_limits_of_equivalence (opOpEquivalence AffineScheme.{u}).inverse
/-
**AlgebraicGeometry.AffineScheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.A
ffineScheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance Γ_preservesLimits : PreservesLimits Γ.{u}.rightOp := inferInstance
/-
**AlgebraicGeometry.AffineScheme.forgetToScheme_preservesLimits** 是 Mathlib 中的一个
实例，位于命名空间 `AlgebraicGeometry.AffineScheme`。
形式化陈述：forgetToScheme_preservesLimits : PreservesLimits forgetToScheme
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimits_of_natIso`：preservesLimits_of_natI
so {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize.{w, w'} F] : PreservesLimits
OfSize.{w, w'} G where preservesLimit…
· 使用定理 `CategoryTheory.Limits.comp_preservesLimits`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ℰ :…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.instIsRightAdjointOfMonadicRightAdjoint`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   (R : CategoryTheor…
-/
noncomputable instance forgetToScheme_preservesLimits : PreservesLimits forgetToScheme := by
  apply +allowSynthFailures @preservesLimits_of_natIso _ _ _ _ _ _
    (Functor.isoWhiskerRight equivCommRingCat.unitIso forgetToScheme).symm
  change PreservesLimits (equivCommRingCat.functor ⋙ Scheme.Spec)
  infer_instance

/-- The forgetful functor `AffineScheme ⥤ Scheme` creates small limits. -/
/-
**AlgebraicGeometry.AffineScheme.createsLimitsForgetToScheme** 是 Mathlib 中的一个实例，
位于命名空间 `AlgebraicGeometry.AffineScheme`。
形式化陈述：createsLimitsForgetToScheme : CreatesLimits forgetToScheme.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…

--- 原说明 ---
The forgetful functor `AffineScheme ⥤ Scheme` creates small limits.
-/
instance createsLimitsForgetToScheme : CreatesLimits forgetToScheme.{u} :=
  ⟨⟨createsLimitOfReflectsIsomorphismsOfPreserves⟩⟩

end AffineScheme

/-- An open subset of a scheme is affine if the open subscheme is affine. -/
/-
**AlgebraicGeometry.IsAffineOpen** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：IsAffineOpen {X : Scheme} (U : X.Opens) : Prop
参数：U : X.Opens。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open subset of a scheme is affine if the open subscheme is affine.
-/
def IsAffineOpen {X : Scheme} (U : X.Opens) : Prop :=
  IsAffine U

/-- The set of affine opens as a subset of `opens X`. -/
/-
**AlgebraicGeometry.Scheme.affineOpens** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → Set X.Opens
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of affine opens as a subset of `opens X`.
-/
def Scheme.affineOpens (X : Scheme) : Set X.Opens :=
  {U : X.Opens | IsAffineOpen U}
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Y : Scheme.{u}} (U : Y.affineOpens) : IsAffine U :=
  U.property

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.isAffineOpen_opensRange** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：isAffineOpen_opensRange {X Y : Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpe
nImmersion f] : IsAffineOpen f.opensRange
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.ofRestrict`：∀ {U : TopCat} (X : Algebr
aicGeometry.Scheme) {f : U ⟶ TopCat.of ↥X}   (h : Topology.IsOpenEmbedding ⇑(Cat
egoryTheory.ConcreteCategory.hom f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
theorem isAffineOpen_opensRange {X Y : Scheme} [IsAffine X] (f : X ⟶ Y)
    [H : IsOpenImmersion f] : IsAffineOpen f.opensRange := by
  refine .of_isIso (IsOpenImmersion.isoOfRangeEq f (Y.ofRestrict _) ?_).inv
  exact Subtype.range_val.symm
/-
**AlgebraicGeometry.isAffineOpen_top** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometr
y`。
形式化陈述：isAffineOpen_top (X : Scheme) [IsAffine X] : IsAffineOpen (⊤ : X.Opens)
参数：X : Scheme。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `AlgebraicGeometry.isAffineOpen_opensRange`：isAffineOpen_opensRange {X Y 
: Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen f.open
sRange
-/
theorem isAffineOpen_top (X : Scheme) [IsAffine X] : IsAffineOpen (⊤ : X.Opens) := by
  convert! isAffineOpen_opensRange (𝟙 X)
  ext1
  exact Set.range_id.symm
/-
**AlgebraicGeometry.exists_isAffineOpen_mem_and_subset** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry`。
形式化陈述：exists_isAffineOpen_mem_and_subset {X : Scheme.{u}} {x : X} {U : X.Opens} 
(hxU : x in U) : exists W : X.Opens, IsAffineOpen W ∧ x in W ∧ W.1 subseteq U
参数：hxU : x in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset`：exist
s_affine_mem_range_and_range_subset {X : Scheme.{u}} {x : X} {U : X.Opens} (hxU 
: x in U) : exists R, exists (f : Spec R ⟶ X), IsOpenIm…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AlgebraicGeometry.isAffineOpen_opensRange`：isAffineOpen_opensRange {X Y 
: Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen f.open
sRange
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem exists_isAffineOpen_mem_and_subset {X : Scheme.{u}} {x : X}
    {U : X.Opens} (hxU : x ∈ U) : ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W.1 ⊆ U := by
  obtain ⟨R, f, hf⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset hxU
  exact ⟨Scheme.Hom.opensRange f (H := hf.1),
    ⟨AlgebraicGeometry.isAffineOpen_opensRange f (H := hf.1), hf.2.1, hf.2.2⟩⟩
/-
**AlgebraicGeometry.Scheme.exists_Spec_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (x : ↥X), ∃ R f, ∃ (_ : AlgebraicGeometry
.IsOpenImmersion f), ∃ y, f y = x
参数：x : ↥X；_ : AlgebraicGeometry.IsOpenImmersion f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.AffineOpenCover.instIsOpenImmersionF`：∀ {X : Al
gebraicGeometry.Scheme} (𝒰 : X.AffineOpenCover) (j : 𝒰.I₀), AlgebraicGeometry.Is
OpenImmersion (𝒰.f j)
· 使用定理 `AlgebraicGeometry.Scheme.AffineCover.covers`：∀ {P : CategoryTheory.Morph
ismProperty AlgebraicGeometry.Scheme} {S : AlgebraicGeometry.Scheme}   (self : A
lgebraicGeometry.Scheme.AffineCov…
-/
lemma Scheme.exists_Spec_apply_eq {X : Scheme.{u}} (x : X) :
    ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ X) (_ : IsOpenImmersion f) (y : Spec R),
    f.base y = x :=
  ⟨X.affineOpenCover.X _, X.affineOpenCover.f _, inferInstance, X.affineOpenCover.covers x⟩
/-
**AlgebraicGeometry.Scheme.isAffine_affineCover** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) (i : X.affineCover.I₀), AlgebraicGeometry
.IsAffine (X.affineCover.X i)
参数：X : AlgebraicGeometry.Scheme；i : X.affineCover.I₀；X.affineCover.X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
-/
instance Scheme.isAffine_affineCover (X : Scheme) (i : X.affineCover.I₀) :
    IsAffine (X.affineCover.X i) :=
  isAffine_Spec _
/-
**AlgebraicGeometry.Scheme.isAffine_affineBasisCover** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) (i : X.affineBasisCover.I₀), AlgebraicGeo
metry.IsAffine (X.affineBasisCover.X i)
参数：X : AlgebraicGeometry.Scheme；i : X.affineBasisCover.I₀；X.affineBasisCover.X i
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
-/
instance Scheme.isAffine_affineBasisCover (X : Scheme) (i : X.affineBasisCover.I₀) :
    IsAffine (X.affineBasisCover.X i) :=
  isAffine_Spec _
/-
**AlgebraicGeometry.Scheme.isAffine_affineOpenCover** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) (𝒰 : X.AffineOpenCover) (i : 𝒰.I₀), Algeb
raicGeometry.IsAffine (𝒰.openCover.X i)
参数：X : AlgebraicGeometry.Scheme；𝒰 : X.AffineOpenCover；i : 𝒰.I₀；𝒰.openCover.X i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Scheme.isAffine_affineOpenCover (X : Scheme) (𝒰 : X.AffineOpenCover) (i : 𝒰.I₀) :
    IsAffine (𝒰.openCover.X i) :=
  inferInstanceAs (IsAffine (Spec (𝒰.X i)))
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Scheme) [CompactSpace X] (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] (i) :
    IsAffine (𝒰.finiteSubcover.X i) :=
  inferInstanceAs (IsAffine (𝒰.X _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X} [IsAffine X] (i) :
    IsAffine ((Scheme.coverOfIsIso (P := @IsOpenImmersion) (𝟙 X)).X i) := by
  dsimp; infer_instance
/-
**AlgebraicGeometry.Scheme.isBasis_affineOpens** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme), TopologicalSpace.Opens.IsBasis X.affineO
pens
参数：X : AlgebraicGeometry.Scheme。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.isBasis_iff_nbhd`：isBasis_iff_nbhd {B : Set (Open
s α)} : IsBasis B ↔ forall {U : Opens α} {x}, x in U -> exists U' in B, x in U' 
∧ U' <= U
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.affineBasisCover_is_basis`：affineBasisCover_is_
basis (X : Scheme.{u}) : TopologicalSpace.IsTopologicalBasis {x : Set X | exists
 a : X.affineBasisCover.I₀, x = Set.rang…
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen`：∀ {α : Type u} [t : Topologi
calSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalBasis
 b → s ∈ b → IsOpen s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.isAffineOpen_opensRange`：isAffineOpen_opensRange {X Y 
: Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen f.open
sRange
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineBasisCover`：∀ (X : AlgebraicGeom
etry.Scheme) (i : X.affineBasisCover.I₀), AlgebraicGeometry.IsAffine (X.affineBa
sisCover.X i)
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
-/
theorem Scheme.isBasis_affineOpens (X : Scheme) : Opens.IsBasis X.affineOpens := by
  rw [Opens.isBasis_iff_nbhd]
  rintro U x (hU : x ∈ (U : Set X))
  obtain ⟨S, hS, hxS, hSU⟩ := X.affineBasisCover_is_basis.exists_subset_of_mem_open hU U.isOpen
  refine ⟨⟨S, X.affineBasisCover_is_basis.isOpen hS⟩, ?_, hxS, hSU⟩
  rcases hS with ⟨i, rfl⟩
  exact isAffineOpen_opensRange _
/-
**AlgebraicGeometry.iSup_affineOpens_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：iSup_affineOpens_eq_top (X : Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) 
= ⊤
参数：X : Scheme。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `TopologicalSpace.IsTopologicalBasis.sUnion_eq`：∀ {α : Type u} [t : Topol
ogicalSpace α] {s : Set (Set α)}, TopologicalSpace.IsTopologicalBasis s → ⋃₀ s =
 Set.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
-/
theorem iSup_affineOpens_eq_top (X : Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤ := by
  apply Opens.ext
  rw [Opens.coe_iSup]
  apply IsTopologicalBasis.sUnion_eq
  rw [← Set.image_eq_range]
  exact X.isBasis_affineOpens
/-
**AlgebraicGeometry.Scheme.map_PrimeSpectrum_basicOpen_of_affine** 是 Mathlib 中的一
个定理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) [inst : AlgebraicGeometry.IsAffine X] (f 
: ↑(X.presheaf.obj (Opposite.op ⊤))),   (TopologicalSpace.Opens.map X.isoSpec.ho
m.base).obj (PrimeSpectrum.basicOpen f) = X.basicOpen f
参数：X : AlgebraicGeometry.Scheme；f : ↑(X.presheaf.obj (Opposite.op ⊤))；Topologica
lSpace.Opens.map X.isoSpec.hom.base；PrimeSpectrum.basicOpen f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_preimage_basicOpen`：∀ (X : AlgebraicGeo
metry.Scheme) (r : ↑(X.presheaf.obj (Opposite.op ⊤))),   (TopologicalSpace.Opens
.map X.toSpecΓ.base).obj (PrimeSpectrum.b…
-/
theorem Scheme.map_PrimeSpectrum_basicOpen_of_affine
    (X : Scheme) [IsAffine X] (f : Γ(X, ⊤)) :
    X.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f :=
  Scheme.toSpecΓ_preimage_basicOpen _ _
/-
**AlgebraicGeometry.isBasis_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry`。
形式化陈述：isBasis_basicOpen (X : Scheme) [IsAffine X] : Opens.IsBasis (Set.range (X.
basicOpen : Γ(X, ⊤) -> X.Opens))
参数：X : Scheme。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.coe_inj`：coe_inj {U V : Opens α} : (U : Set α) = 
V ↔ U = V
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `TopologicalSpace.Opens.IsBasis.of_isInducing`：∀ {α : Type u_2} {β : Type
 u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   {B : Set (Topo
logicalSpace.Opens β)},   Topologi…
· 使用定理 `PrimeSpectrum.isBasis_basic_opens`：isBasis_basic_opens : TopologicalSpac
e.Opens.IsBasis (Set.range (@basicOpen R _))
-/
theorem isBasis_basicOpen (X : Scheme) [IsAffine X] :
    Opens.IsBasis (Set.range (X.basicOpen : Γ(X, ⊤) → X.Opens)) := by
  convert!
    PrimeSpectrum.isBasis_basic_opens.of_isInducing
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso X.isoSpec)).isInducing using 1
  ext V
  simp only [Set.mem_range, exists_exists_eq_and, Set.mem_ofPred,
    ← Opens.coe_inj (V := V), ← Scheme.toSpecΓ_preimage_basicOpen]
  rfl

/-- The canonical map `U ⟶ Spec Γ(X, U)` for an open `U ⊆ X`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Opens.toSpec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Scheme.Opens.toSpecΓ {X : Scheme.{u}} (U : X.Opens) :
    U.toScheme ⟶ Spec Γ(X, U) :=
  U.toScheme.toSpecΓ ≫ Spec.map U.topIso.inv

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Opens.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Opens.toSpecΓ_SpecMap_presheaf_map {X : Scheme} (U V : X.Opens) (h : U ≤ V) :
    U.toSpecΓ ≫ Spec.map (X.presheaf.map (homOfLE h).op) = X.homOfLE h ≫ V.toSpecΓ := by
  delta Scheme.Opens.toSpecΓ
  simp [← Spec.map_comp, ← X.presheaf.map_comp, toSpecΓ_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] -- not simp because simp can prove this.
/-
**AlgebraicGeometry.Scheme.Opens.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top {X : Scheme} (U : X.Opens) :
    U.toSpecΓ ≫ Spec.map (X.presheaf.map (homOfLE le_top).op) = U.ι ≫ X.toSpecΓ := by
  delta Scheme.Opens.toSpecΓ
  simp [← Spec.map_comp, ← X.presheaf.map_comp, toSpecΓ_naturality]

@[simp]
/-
**AlgebraicGeometry.Scheme.Opens.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Opens.toSpecΓ_top {X : Scheme} :
    (⊤ : X.Opens).toSpecΓ = (⊤ : X.Opens).ι ≫ X.toSpecΓ := by
  simp [Scheme.Opens.toSpecΓ, toSpecΓ_naturality]; rfl

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.Opens.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Opens.toSpecΓ_appTop {X : Scheme.{u}} (U : X.Opens) :
    U.toSpecΓ.appTop = (Scheme.ΓSpecIso Γ(X, U)).hom ≫ U.topIso.inv := by
  simp [Scheme.Opens.toSpecΓ]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Opens.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Opens.toSpecΓ_naturality {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) :
    (f ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (f.app U) = f ∣_ U ≫ U.toSpecΓ := by
  simp only [toSpecΓ, topIso, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv,
    eqToHom_op, Hom.app_eq_appLE, Category.assoc, ← Spec.map_comp, Hom.appLE_map,
    toSpecΓ_naturality_assoc, TopologicalSpace.Opens.map_top, morphismRestrict_appLE, Hom.map_appLE]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Opens.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Opens.toSpecΓ_SpecMap_appLE
    {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (hUV) :
    V.toSpecΓ ≫ Spec.map (f.appLE U V hUV) = f.resLE U V hUV ≫ U.toSpecΓ := by
  simp [Hom.appLE, Hom.resLE]

namespace IsAffineOpen

variable {X Y : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))

set_option backward.isDefEq.respectTransparency.types false in
attribute [-simp] eqToHom_op in
/-- The isomorphism `U ≅ Spec Γ(X, U)` for an affine `U`. -/
@[simps! -isSimp inv]
/-
**AlgebraicGeometry.IsAffineOpen.isoSpec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.IsAffineOpen`。
形式化陈述：isoSpec : ↑U ≅ Spec Γ(X, U)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `U ≅ Spec Γ(X, U)` for an affine `U`.
-/
def isoSpec :
    ↑U ≅ Spec Γ(X, U) :=
  haveI : IsAffine U := hU
  U.toScheme.isoSpec ≪≫ Scheme.Spec.mapIso U.topIso.symm.op
/-
**AlgebraicGeometry.IsAffineOpen.isoSpec_hom** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.IsAffineOpen`。
形式化陈述：isoSpec_hom : hU.isoSpec.hom = U.toSpecΓ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoSpec_hom : hU.isoSpec.hom = U.toSpecΓ := rfl

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.IsAffineOpen.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.IsAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSpecΓ_isoSpec_inv : U.toSpecΓ ≫ hU.isoSpec.inv = 𝟙 _ := hU.isoSpec.hom_inv_id

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.IsAffineOpen.isoSpec_inv_toSpec** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.IsAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoSpec_inv_toSpecΓ : hU.isoSpec.inv ≫ U.toSpecΓ = 𝟙 _ := hU.isoSpec.inv_hom_id

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open IsLocalRing in
/-
**AlgebraicGeometry.IsAffineOpen.isoSpec_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.IsAffineOpen`。
形式化陈述：isoSpec_hom_apply (x : U) : hU.isoSpec.hom x = Spec.map (X.presheaf.germ U
 x x.2) (closedPoint _)
参数：x : U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用定理 `trivial`：True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用引理 `AlgebraicGeometry.Scheme.Opens.germ_stalkIso_hom`：germ_stalkIso_hom {X :
 Scheme.{u}} (U : X.Opens) {V : U.toScheme.Opens} (x : U) (hx : x in V) : U.toSc
heme.presheaf.germ V x hx ≫ (U.stalkIs…
· 使用定理 `TopCat.Presheaf.germ_res_assoc`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X : TopCat}   (
F : TopCat.Presheaf …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `IsLocalRing.comap_closedPoint`：comap_closedPoint {S : Type v} [CommSemir
ing S] [IsLocalRing S] (f : R ->+* S) [IsLocalHom f] : PrimeSpectrum.comap f (cl
osedPoint S) = clos…
· 使用定理 `isLocalHom_of_isIso`：isLocalHom_of_isIso {R S : CommRingCat} (f : R ⟶ S)
 [IsIso f] : IsLocalHom f.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma isoSpec_hom_apply (x : U) :
    hU.isoSpec.hom x = Spec.map (X.presheaf.germ U x x.2) (closedPoint _) := by
  dsimp [IsAffineOpen.isoSpec_hom, Scheme.isoSpec_hom, Scheme.toSpecΓ_apply, Scheme.Opens.toSpecΓ,
    TopCat.Presheaf.Γgerm]
  rw [← Scheme.Hom.comp_apply, ← Spec.map_comp,
    (Iso.eq_comp_inv _).mpr (Scheme.Opens.germ_stalkIso_hom U (V := ⊤) x trivial),
    X.presheaf.germ_res_assoc, Spec.map_comp, Scheme.Hom.comp_apply]
  congr 1
  exact IsLocalRing.comap_closedPoint (U.stalkIso x).inv.hom

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsAffineOpen.isoSpec_hom_appTop** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.IsAffineOpen`。
形式化陈述：isoSpec_hom_appTop : hU.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X, U)).hom
 ≫ U.topIso.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.op_inv`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.inv = α.inv.op
· 使用定理 `AlgebraicGeometry.Scheme.Opens.topIso_inv`：∀ {X : AlgebraicGeometry.Sche
me} (U : X.Opens), U.topIso.inv = X.presheaf.map (CategoryTheory.eqToHom ⋯).op
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_appTop`：∀ (X : AlgebraicGeometry.Scheme
),   AlgebraicGeometry.Scheme.Hom.appTop X.toSpecΓ =     (AlgebraicGeometry.Sche
me.ΓSpecIso (X.presheaf.obj (…
· 使用引理 `AlgebraicGeometry.Scheme.ΓSpecIso_naturality`：ΓSpecIso_naturality {R S :
 CommRingCat.{u}} (f : R ⟶ S) : (Spec.map f).appTop ≫ (ΓSpecIso S).hom = (ΓSpecI
so R).hom ≫ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isoSpec_hom_appTop :
    hU.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X, U)).hom ≫ U.topIso.inv := by
  simp [isoSpec, Scheme.isoSpec]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.IsAffineOpen.isoSpec_inv_appTop** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.IsAffineOpen`。
形式化陈述：isoSpec_inv_appTop : hU.isoSpec.inv.appTop = U.topIso.hom ≫ (Scheme.ΓSpecI
so Γ(X, U)).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIsoCommRingCatApp`：∀ {X Y : Algebraic
Geometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f] (U : Y.Opens),   CategoryT
heory.IsIso (AlgebraicGeometry.Scheme.Hom.…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_appTop`：comp_appTop {X Y Z : Scheme} (
f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).appTop = g.appTop ≫ f.appTop
· 使用引理 `AlgebraicGeometry.IsAffineOpen.isoSpec_hom_appTop`：isoSpec_hom_appTop : 
hU.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X, U)).hom ≫ U.topIso.inv
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Opens.topIso_hom`：∀ {X : AlgebraicGeometry.Sche
me} (U : X.Opens), U.topIso.hom = X.presheaf.map (CategoryTheory.eqToHom ⋯).op
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用引理 `AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality`：ΓSpecIso_inv_naturalit
y {R S : CommRingCat.{u}} (f : R ⟶ S) : f ≫ (ΓSpecIso S).inv = (ΓSpecIso R).inv 
≫ (Spec.map f).appTop
· 使用定理 `AlgebraicGeometry.Scheme.Opens.topIso_inv`：∀ {X : AlgebraicGeometry.Sche
me} (U : X.Opens), U.topIso.inv = X.presheaf.map (CategoryTheory.eqToHom ⋯).op
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.ΓSpecIso_naturality_assoc`：∀ {R S : CommRingCat
} (f : R ⟶ S) {Z : CommRingCat} (h : S ⟶ Z),   CategoryTheory.CategoryStruct.com
p (AlgebraicGeometry.Scheme.Hom.appTop (…
· 使用定理 `CategoryTheory.eqToHom_map_comp`：eqToHom_map_comp (F : C ⥤ D) {X Y Z : C
} (p : X = Y) (q : Y = Z) : F.map (eqToHom p) ≫ F.map (eqToHom q) = F.map (eqToH
om <| p.trans q)
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma isoSpec_inv_appTop :
    hU.isoSpec.inv.appTop = U.topIso.hom ≫ (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [← cancel_mono hU.isoSpec.hom.appTop, ← Scheme.Hom.comp_appTop, isoSpec_hom_appTop]
  simp
  rfl

/-- The open immersion `Spec Γ(X, U) ⟶ X` for an affine `U`. -/
/-
**AlgebraicGeometry.IsAffineOpen.fromSpec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.IsAffineOpen`。
形式化陈述：fromSpec : Spec Γ(X, U) ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The open immersion `Spec Γ(X, U) ⟶ X` for an affine `U`.
-/
def fromSpec :
    Spec Γ(X, U) ⟶ X :=
  haveI : IsAffine U := hU
  hU.isoSpec.inv ≫ U.ι
/-
**AlgebraicGeometry.IsAffineOpen.isOpenImmersion_fromSpec** 是 Mathlib 中的一个实例，位于命
名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：isOpenImmersion_fromSpec : IsOpenImmersion hU.fromSpec
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
-/
instance isOpenImmersion_fromSpec :
    IsOpenImmersion hU.fromSpec := by
  delta fromSpec
  infer_instance

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.IsAffineOpen.isoSpec_inv_** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.IsAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoSpec_inv_ι : hU.isoSpec.inv ≫ U.ι = hU.fromSpec := rfl

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.IsAffineOpen.isoSpec_hom_fromSpec** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.IsAffineOpen`。
形式化陈述：isoSpec_hom_fromSpec : hU.isoSpec.hom ≫ hU.fromSpec = U.ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isoSpec_hom_fromSpec : hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
  simp [← cancel_epi hU.isoSpec.inv]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.IsAffineOpen.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.IsAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSpecΓ_fromSpec : U.toSpecΓ ≫ hU.fromSpec = U.ι := toSpecΓ_isoSpec_inv_assoc _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.IsAffineOpen.range_fromSpec** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.IsAffineOpen`。
形式化陈述：range_fromSpec : Set.range hU.fromSpec = U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `TopCat.epi_iff_surjective`：epi_iff_surjective {X Y : TopCat.{u}} (f : X 
⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `AlgebraicGeometry.instIsIsoSchemeMapOfCommRingCat`：∀ {R S : CommRingCat}
 (f : R ⟶ S) [CategoryTheory.IsIso f], CategoryTheory.IsIso (AlgebraicGeometry.S
pec.map f)
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem range_fromSpec :
    Set.range hU.fromSpec = U := by
  delta IsAffineOpen.fromSpec; dsimp [IsAffineOpen.isoSpec_inv]
  rw [Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ]
  · exact Subtype.range_coe
  rw [← TopCat.coe_comp, ← TopCat.epi_iff_surjective]
  infer_instance

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.IsAffineOpen.fromSpec_toSpec** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.IsAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromSpec_toSpecΓ {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ X.toSpecΓ = Spec.map (X.presheaf.map (homOfLE le_top).op) := by
  rw [fromSpec, Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
    isoSpec_inv_toSpecΓ_assoc]

@[simp]
/-
**AlgebraicGeometry.IsAffineOpen.opensRange_fromSpec** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.IsAffineOpen`。
形式化陈述：opensRange_fromSpec : hU.fromSpec.opensRange = U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `AlgebraicGeometry.IsAffineOpen.range_fromSpec`：range_fromSpec : Set.rang
e hU.fromSpec = U
-/
theorem opensRange_fromSpec : hU.fromSpec.opensRange = U := Opens.ext (range_fromSpec hU)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.IsAffineOpen.map_fromSpec** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.IsAffineOpen`。
形式化陈述：map_fromSpec {V : X.Opens} (hV : IsAffineOpen V) (f : op U ⟶ op V) : Spec.
map (X.presheaf.map f) ≫ hU.fromSpec = hV.fromSpec
参数：hV : IsAffineOpen V；f : op U ⟶ op V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.Scheme.ι_image_homOfLE_le_ι_image`：∀ {X : AlgebraicGeo
metry.Scheme} {U V : X.Opens} (e : U ≤ V) (W : (↑V).Opens),   (AlgebraicGeometry
.Scheme.Hom.opensFunctor U.ι).obj ((Topol…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec.eq_1`：∀ {X : AlgebraicGeometry.S
cheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U),   hU.fromSpec = Ca
tegoryTheory.CategoryStruct.comp h…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isoSpec_inv`：∀ {X : AlgebraicGeometry.Sch
eme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U),   hU.isoSpec.inv =  
   CategoryTheory.CategoryStruct…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.isoSpec_inv_naturality_assoc`：∀ {X Y : Algebrai
cGeometry.Scheme} [inst : AlgebraicGeometry.IsAffine X] [inst_1 : AlgebraicGeome
try.IsAffine Y]   (f : X ⟶ Y) {Z : Algebrai…
· 使用定理 `AlgebraicGeometry.Spec.map_comp_assoc`：∀ {R S T : CommRingCat} (f : R ⟶ 
S) (g : S ⟶ T) {Z : AlgebraicGeometry.Scheme} (h : AlgebraicGeometry.Spec R ⟶ Z)
,   CategoryTheory.Category…
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_appTop`：∀ {X : AlgebraicGeometry.Scheme
} {U V : X.Opens} (e : U ≤ V),   AlgebraicGeometry.Scheme.Hom.appTop (X.homOfLE 
e) = X.presheaf.map (Category…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem map_fromSpec {V : X.Opens} (hV : IsAffineOpen V) (f : op U ⟶ op V) :
    Spec.map (X.presheaf.map f) ≫ hU.fromSpec = hV.fromSpec := by
  have : IsAffine U := hU
  have : IsAffine _ := hV
  conv_rhs =>
    rw [fromSpec, ← X.homOfLE_ι (V := U) f.unop.le, isoSpec_inv, Category.assoc,
      ← Scheme.isoSpec_inv_naturality_assoc,
      ← Spec.map_comp_assoc, Scheme.homOfLE_appTop, ← Functor.map_comp]
  rw [fromSpec, isoSpec_inv, Category.assoc, ← Spec.map_comp_assoc, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：SpecMap_appLE_fromSpec (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens} (hU : IsAff
ineOpen U) (hV : IsAffineOpen V) (i : V <= f ⁻¹ᵁ U) : Spec.map (f.appLE U V i) ≫
 hU.fromSpec = hV.fromSpec ≫ f
参数：f : X ⟶ Y；hU : IsAffineOpen U；hV : IsAffineOpen V；i : V <= f ⁻¹ᵁ U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isoSpec_inv`：∀ {X : AlgebraicGeometry.Sch
eme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U),   hU.isoSpec.inv =  
   CategoryTheory.CategoryStruct…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
· 使用定理 `AlgebraicGeometry.Scheme.isoSpec_inv_naturality_assoc`：∀ {X Y : Algebrai
cGeometry.Scheme} [inst : AlgebraicGeometry.IsAffine X] [inst_1 : AlgebraicGeome
try.IsAffine Y]   (f : X ⟶ Y) {Z : Algebrai…
· 使用定理 `AlgebraicGeometry.Spec.map_comp_assoc`：∀ {R S T : CommRingCat} (f : R ⟶ 
S) (g : S ⟶ T) {Z : AlgebraicGeometry.Scheme} (h : AlgebraicGeometry.Spec R ⟶ Z)
,   CategoryTheory.Category…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_appTop`：comp_appTop {X Y Z : Scheme} (
f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).appTop = g.appTop ≫ f.appTop
· 使用定理 `AlgebraicGeometry.image_morphismRestrict_preimage`：image_morphismRestric
t_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ⁻¹ᵁ U
).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι '…
· 使用定理 `AlgebraicGeometry.morphismRestrict_appTop`：morphismRestrict_appTop {X Y 
: Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : (f ∣_ U).appTop = f.app (U.ι ''ᵁ ⊤) ≫ 
X.presheaf.map (eqToHom (image_…
· 使用定理 `AlgebraicGeometry.Scheme.ι_image_homOfLE_le_ι_image`：∀ {X : AlgebraicGeo
metry.Scheme} {U V : X.Opens} (e : U ≤ V) (W : (↑V).Opens),   (AlgebraicGeometry
.Scheme.Hom.opensFunctor U.ι).obj ((Topol…
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_appTop`：∀ {X : AlgebraicGeometry.Scheme
} {U V : X.Opens} (e : U ≤ V),   AlgebraicGeometry.Scheme.Hom.appTop (X.homOfLE 
e) = X.presheaf.map (Category…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_map`：appLE_map (e : V <= f ⁻¹ᵁ U) (i 
: op V ⟶ op V') : f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.tra
ns e)
· 使用引理 `AlgebraicGeometry.Scheme.Hom.map_appLE`：map_appLE (e : V <= f ⁻¹ᵁ U) (i 
: op U' ⟶ op U) : Y.presheaf.map i ≫ f.appLE U V e = f.appLE U' V (e.trans ((Ope
ns.map f.base).map i.unop).l…
-/
lemma SpecMap_appLE_fromSpec (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : V ≤ f ⁻¹ᵁ U) :
    Spec.map (f.appLE U V i) ≫ hU.fromSpec = hV.fromSpec ≫ f := by
  have : IsAffine U := hU
  simp only [IsAffineOpen.fromSpec, Category.assoc, isoSpec_inv]
  simp_rw [← Scheme.homOfLE_ι _ i]
  rw [Category.assoc, ← morphismRestrict_ι,
    ← Category.assoc _ (f ∣_ U) U.ι, ← @Scheme.isoSpec_inv_naturality_assoc,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, Scheme.Hom.comp_appTop, morphismRestrict_appTop,
    Scheme.homOfLE_appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map,
    Scheme.Hom.appLE_map, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
/-
**AlgebraicGeometry.IsAffineOpen.fromSpec_top** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.IsAffineOpen`。
形式化陈述：fromSpec_top [IsAffine X] : (isAffineOpen_top X).fromSpec = X.isoSpec.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec.eq_1`：∀ {X : AlgebraicGeometry.S
cheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U),   hU.fromSpec = Ca
tegoryTheory.CategoryStruct.comp h…
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Opens.toSpecΓ_top`：∀ {X : AlgebraicGeometry.Sch
eme}, ⊤.toSpecΓ = CategoryTheory.CategoryStruct.comp ⊤.ι X.toSpecΓ
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_isoSpec_inv`：∀ (X : AlgebraicGeometry.S
cheme) [inst : AlgebraicGeometry.IsAffine X],   CategoryTheory.CategoryStruct.co
mp X.toSpecΓ X.isoSpec.inv = Categ…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSpec_top [IsAffine X] : (isAffineOpen_top X).fromSpec = X.isoSpec.inv := by
  rw [fromSpec, Iso.inv_comp_eq]
  simp [isoSpec_hom]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.IsAffineOpen.fromSpec_app_of_le** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.IsAffineOpen`。
形式化陈述：fromSpec_app_of_le (V : X.Opens) (h : U <= V) : hU.fromSpec.app V = X.pres
heaf.map (homOfLE h).op ≫ (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec _).presheaf.map 
(homOfLE le_top).op
参数：V : X.Opens；h : U <= V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec.eq_1`：∀ {X : AlgebraicGeometry.S
cheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U),   hU.fromSpec = Ca
tegoryTheory.CategoryStruct.comp h…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_app`：comp_app {X Y Z : Scheme} (f : X 
⟶ Y) (g : Y ⟶ Z) (U) : (f ≫ g).app U = g.app U ≫ f.app _
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_app`：ι_app (V) : U.ι.app V = X.presheaf
.map (homOfLE (x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.app_eq`：app_eq {X Y : Scheme} (f : X ⟶ Y) {
U V : Y.Opens} (e : U = V) : f.app U = Y.presheaf.map (eqToHom e.symm).op ≫ f.ap
p V ≫ X.presheaf.map (eqT…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appTop.eq_1`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y),   AlgebraicGeometry.Scheme.Hom.appTop f = AlgebraicGeometry.Sc
heme.Hom.app f ⊤
· 使用引理 `AlgebraicGeometry.IsAffineOpen.isoSpec_inv_appTop`：isoSpec_inv_appTop : 
hU.isoSpec.inv.appTop = U.topIso.hom ≫ (Scheme.ΓSpecIso Γ(X, U)).inv
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Opens.topIso_hom`：∀ {X : AlgebraicGeometry.Sche
me} (U : X.Opens), U.topIso.hom = X.presheaf.map (CategoryTheory.eqToHom ⋯).op
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
-/
lemma fromSpec_app_of_le (V : X.Opens) (h : U ≤ V) :
    hU.fromSpec.app V = X.presheaf.map (homOfLE h).op ≫
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec _).presheaf.map (homOfLE le_top).op := by
  have : U.ι ⁻¹ᵁ V = ⊤ := eq_top_iff.mpr fun x _ ↦ h x.2
  rw [IsAffineOpen.fromSpec, Scheme.Hom.comp_app, Scheme.Opens.ι_app, Scheme.Hom.app_eq _ this,
    ← Scheme.Hom.appTop, IsAffineOpen.isoSpec_inv_appTop]
  simp only [Scheme.Opens.toScheme_presheaf_map, Scheme.Opens.topIso_hom,
    Category.assoc, ← X.presheaf.map_comp_assoc]
  rfl

include hU in
/-
**AlgebraicGeometry.IsAffineOpen.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.IsAffineOpen`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens}, AlgebraicGeometry.IsAffine
Open U → IsCompact ↑U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `AlgebraicGeometry.IsAffineOpen.range_fromSpec`：range_fromSpec : Set.rang
e hU.fromSpec = U
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
-/
protected theorem isCompact :
    IsCompact (U : Set X) := by
  convert! @IsCompact.image _ _ _ _ Set.univ hU.fromSpec PrimeSpectrum.compactSpace.1 (by fun_prop)
  convert! hU.range_fromSpec.symm
  exact Set.image_univ
/-
**AlgebraicGeometry.IsAffineOpen._root_.AlgebraicGeometry.Scheme.Hom.isAffineOpe
n_iff_of_isOpenImmersion** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.IsAffineOp
en`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion
    (f : X ⟶ Y) [H : IsOpenImmersion f] {U : X.Opens} :
    IsAffineOpen (f ''ᵁ U) ↔ IsAffineOpen U :=
  IsAffine.iff_of_isIso (IsOpenImmersion.isoOfRangeEq (U.ι ≫ f) (f ''ᵁ U).ι
    (by simp [Scheme.Hom.comp_base, Set.range_comp])).inv

include hU in
/-
**AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：image_of_isOpenImmersion (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpe
n (f ''ᵁ U)
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion`：∀ {X Y
 : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion 
f] {U : X.Opens},   AlgebraicGeometry.IsAffineOpen ((A…
-/
theorem image_of_isOpenImmersion (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsAffineOpen (f ''ᵁ U) := by
  rwa [f.isAffineOpen_iff_of_isOpenImmersion]
/-
**AlgebraicGeometry.IsAffineOpen.preimage_of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.IsAffineOpen`。
形式化陈述：preimage_of_isIso {U : Y.Opens} (hU : IsAffineOpen U) (f : X ⟶ Y) [IsIso f
] : IsAffineOpen (f ⁻¹ᵁ U)
参数：hU : IsAffineOpen U；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `AlgebraicGeometry.instIsIsoSchemeMorphismRestrict`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f] (U : Y.Opens), CategoryTheory
.IsIso (f ∣_ U)
-/
theorem preimage_of_isIso {U : Y.Opens} (hU : IsAffineOpen U) (f : X ⟶ Y) [IsIso f] :
    IsAffineOpen (f ⁻¹ᵁ U) :=
  haveI : IsAffine _ := hU
  .of_isIso (f ∣_ U)
/-
**AlgebraicGeometry.IsAffineOpen.preimage_of_isOpenImmersion** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：preimage_of_isOpenImmersion {U : Y.Opens} (hU : IsAffineOpen U) (f : X ⟶ Y
) [IsOpenImmersion f] (hU' : U <= f.opensRange) : IsAffineOpen (f ⁻¹ᵁ U)
参数：hU : IsAffineOpen U；f : X ⟶ Y；hU' : U <= f.opensRange。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion`：∀ {X Y
 : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion 
f] {U : X.Opens},   AlgebraicGeometry.IsAffineOpen ((A…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`：image_pre
image_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
-/
theorem preimage_of_isOpenImmersion {U : Y.Opens} (hU : IsAffineOpen U)
    (f : X ⟶ Y) [IsOpenImmersion f] (hU' : U ≤ f.opensRange) :
    IsAffineOpen (f ⁻¹ᵁ U) := by
  rwa [← f.isAffineOpen_iff_of_isOpenImmersion, f.image_preimage_eq_opensRange_inf,
    inf_eq_right.mpr hU']

/-- The affine open sets of an open subscheme corresponds to
the affine open sets containing in the image. -/
@[simps]
/-
**AlgebraicGeometry.IsAffineOpen._root_.AlgebraicGeometry.IsOpenImmersion.affine
OpensEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine open sets of an open subscheme corresponds to
the affine open sets containing in the image.
-/
def _root_.AlgebraicGeometry.IsOpenImmersion.affineOpensEquiv (f : X ⟶ Y) [H : IsOpenImmersion f] :
    X.affineOpens ≃o { U : Y.affineOpens // U ≤ f.opensRange } where
  toFun U := ⟨⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩, Set.image_subset_range _ _⟩
  invFun U := ⟨f ⁻¹ᵁ U, U.1.2.preimage_of_isOpenImmersion _ U.2⟩
  left_inv _ := Subtype.ext (f.preimage_image_eq _)
  right_inv U := Subtype.ext (Subtype.ext (Opens.ext (Set.image_preimage_eq_of_subset U.2)))
  map_rel_iff' := f.image_le_image_iff _ _

/-- The affine open sets of an open subscheme
corresponds to the affine open sets containing in the subset. -/
@[simps! apply_coe_coe]
/-
**AlgebraicGeometry.IsAffineOpen._root_.AlgebraicGeometry.affineOpensRestrict** 
是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine open sets of an open subscheme
corresponds to the affine open sets containing in the subset.
-/
def _root_.AlgebraicGeometry.affineOpensRestrict {X : Scheme.{u}} (U : X.Opens) :
    U.toScheme.affineOpens ≃ { V : X.affineOpens // V ≤ U } :=
  (IsOpenImmersion.affineOpensEquiv U.ι).toEquiv.trans (Equiv.subtypeEquivProp (by simp))

@[simp]
/-
**AlgebraicGeometry.IsAffineOpen._root_.AlgebraicGeometry.affineOpensRestrict_sy
mm_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgebraicGeometry.affineOpensRestrict_symm_apply_coe
    {X : Scheme.{u}} (U : X.Opens) (V) :
    ((affineOpensRestrict U).symm V).1 = U.ι ⁻¹ᵁ V := rfl
/-
**AlgebraicGeometry.IsAffineOpen.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.I
sAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) _root_.AlgebraicGeometry.Scheme.compactSpace_of_isAffine
    (X : Scheme) [IsAffine X] :
    CompactSpace X :=
  ⟨(isAffineOpen_top X).isCompact⟩

@[simp]
/-
**AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_self** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：fromSpec_preimage_self : hU.fromSpec ⁻¹ᵁ U = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.opensRange_fromSpec`：opensRange_fromSpec 
: hU.fromSpec.opensRange = U
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_opensRange`：preimage_opensRange {X
 Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] : f ⁻¹ᵁ f.opensRange = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fromSpec_preimage_self :
    hU.fromSpec ⁻¹ᵁ U = ⊤ := by
  simp_rw [← hU.opensRange_fromSpec, Scheme.Hom.preimage_opensRange]
/-
**AlgebraicGeometry.IsAffineOpen.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.I
sAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ΓSpecIso_hom_fromSpec_app :
    (Scheme.ΓSpecIso Γ(X, U)).hom ≫ hU.fromSpec.app U =
      (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op := by
  change _ = (Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
  simp [IsAffineOpen.fromSpec_app_of_le]

@[elementwise]
/-
**AlgebraicGeometry.IsAffineOpen.fromSpec_app_self** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.IsAffineOpen`。
形式化陈述：fromSpec_app_self : hU.fromSpec.app U = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (S
pec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_self`：fromSpec_preimage
_self : hU.fromSpec ⁻¹ᵁ U = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.ΓSpecIso_hom_fromSpec_app`：ΓSpecIso_hom_f
romSpec_app : (Scheme.ΓSpecIso Γ(X, U)).hom ≫ hU.fromSpec.app U = (Spec Γ(X, U))
.presheaf.map (eqToHom hU.fromSpec_preimage_se…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
theorem fromSpec_app_self :
    hU.fromSpec.app U = (Scheme.ΓSpecIso Γ(X, U)).inv ≫
      (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op := by
  rw [← hU.ΓSpecIso_hom_fromSpec_app, Iso.inv_hom_id_assoc]
/-
**AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen'** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：fromSpec_preimage_basicOpen' : hU.fromSpec ⁻¹ᵁ X.basicOpen f = (Spec Γ(X, 
U)).basicOpen ((Scheme.ΓSpecIso Γ(X, U)).inv f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.preimage_basicOpen`：preimage_basicOpen {X Y : S
cheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) : f ⁻¹ᵁ Y.basicOpen r = X.bas
icOpen (f.app U r)
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_self`：fromSpec_preimage
_self : hU.fromSpec ⁻¹ᵁ U = ⊤
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_app_self`：fromSpec_app_self : hU
.fromSpec.app U = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map (e
qToHom hU.fromSpec_preimage_self).op
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res_eq`：basicOpen_res_eq (i : op U ⟶ 
op V) [IsIso i] : X.basicOpen (X.presheaf.map i f) = X.basicOpen f
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
-/
theorem fromSpec_preimage_basicOpen' :
    hU.fromSpec ⁻¹ᵁ X.basicOpen f = (Spec Γ(X, U)).basicOpen ((Scheme.ΓSpecIso Γ(X, U)).inv f) := by
  rw [Scheme.preimage_basicOpen, hU.fromSpec_app_self]
  exact Scheme.basicOpen_res_eq _ _ (eqToHom hU.fromSpec_preimage_self).op
/-
**AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：fromSpec_preimage_basicOpen : hU.fromSpec ⁻¹ᵁ X.basicOpen f = PrimeSpectru
m.basicOpen f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen'`：fromSpec_pr
eimage_basicOpen' : hU.fromSpec ⁻¹ᵁ X.basicOpen f = (Spec Γ(X, U)).basicOpen ((S
cheme.ΓSpecIso Γ(X, U)).inv f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.basicOpen_eq_of_affine`：basicOpen_eq_of_affine {R : Co
mmRingCat} (f : R) : (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv f) = PrimeSpect
rum.basicOpen f
-/
theorem fromSpec_preimage_basicOpen :
    hU.fromSpec ⁻¹ᵁ X.basicOpen f = PrimeSpectrum.basicOpen f := by
  rw [fromSpec_preimage_basicOpen', ← basicOpen_eq_of_affine]
/-
**AlgebraicGeometry.IsAffineOpen.fromSpec_image_basicOpen** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：fromSpec_image_basicOpen : hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f = X.b
asicOpen f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen`：fromSpec_pre
image_basicOpen : hU.fromSpec ⁻¹ᵁ X.basicOpen f = PrimeSpectrum.basicOpen f
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `AlgebraicGeometry.IsAffineOpen.range_fromSpec`：range_fromSpec : Set.rang
e hU.fromSpec = U
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
-/
theorem fromSpec_image_basicOpen :
    hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f := by
  rw [← hU.fromSpec_preimage_basicOpen]
  ext1
  change hU.fromSpec '' hU.fromSpec ⁻¹' (X.basicOpen f : Set X) = _
  rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left, hU.range_fromSpec]
  exact Scheme.basicOpen_le _ _

@[simp]
/-
**AlgebraicGeometry.IsAffineOpen.basicOpen_fromSpec_app** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：basicOpen_fromSpec_app : (Spec Γ(X, U)).basicOpen (hU.fromSpec.app U f) = 
PrimeSpectrum.basicOpen f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen`：fromSpec_pre
image_basicOpen : hU.fromSpec ⁻¹ᵁ X.basicOpen f = PrimeSpectrum.basicOpen f
· 使用定理 `AlgebraicGeometry.Scheme.preimage_basicOpen`：preimage_basicOpen {X Y : S
cheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) : f ⁻¹ᵁ Y.basicOpen r = X.bas
icOpen (f.app U r)
-/
theorem basicOpen_fromSpec_app :
    (Spec Γ(X, U)).basicOpen (hU.fromSpec.app U f) = PrimeSpectrum.basicOpen f := by
  rw [← hU.fromSpec_preimage_basicOpen, Scheme.preimage_basicOpen]

set_option backward.isDefEq.respectTransparency.types false in
include hU in
/-
**AlgebraicGeometry.IsAffineOpen.basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.IsAffineOpen`。
形式化陈述：basicOpen : IsAffineOpen (X.basicOpen f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_image_basicOpen`：fromSpec_image_
basicOpen : hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion`：∀ {X Y
 : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion 
f] {U : X.Opens},   AlgebraicGeometry.IsAffineOpen ((A…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `PrimeSpectrum.localization_away_comap_range`：localization_away_comap_ran
ge (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S]
 : Set.range (comap (algebraMap R…
· 使用定理 `AlgebraicGeometry.isAffineOpen_opensRange`：isAffineOpen_opensRange {X Y 
: Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen f.open
sRange
-/
theorem basicOpen :
    IsAffineOpen (X.basicOpen f) := by
  rw [← hU.fromSpec_image_basicOpen, Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion]
  convert!
    isAffineOpen_opensRange
      (Spec.map (CommRingCat.ofHom <| algebraMap Γ(X, U) (Localization.Away f)))
  exact Opens.ext (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm
/-
**AlgebraicGeometry.IsAffineOpen.Spec_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.IsAffineOpen`。
形式化陈述：Spec_basicOpen {R : CommRingCat} (f : R) : IsAffineOpen (X
参数：f : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `AlgebraicGeometry.basicOpen_eq_of_affine`：basicOpen_eq_of_affine {R : Co
mmRingCat} (f : R) : (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv f) = PrimeSpect
rum.basicOpen f
-/
lemma Spec_basicOpen {R : CommRingCat} (f : R) :
    IsAffineOpen (X := Spec R) (PrimeSpectrum.basicOpen f) :=
  basicOpen_eq_of_affine f ▸ (isAffineOpen_top (Spec <| .of R)).basicOpen _
/-
**AlgebraicGeometry.IsAffineOpen.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.I
sAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsAffine X] (r : Γ(X, ⊤)) : IsAffine (X.basicOpen r) :=
  (isAffineOpen_top X).basicOpen _

include hU in
/-
**AlgebraicGeometry.IsAffineOpen.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.I
sAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_basicOpen_preimage (r : Γ(X, ⊤)) :
    IsAffineOpen ((X.basicOpen r).ι ⁻¹ᵁ U) := by
  apply (X.basicOpen r).ι.isAffineOpen_iff_of_isOpenImmersion.mp
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm,
    ← Scheme.basicOpen_res _ _ (homOfLE le_top).op]
  exact hU.basicOpen _

set_option backward.isDefEq.respectTransparency false in
include hU in
/-
**AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.IsAffineOpen`。
形式化陈述：exists_basicOpen_le {V : X.Opens} (x : V) (h : ↑x in U) : exists f : Γ(X, 
U), X.basicOpen f <= V ∧ ↑x in X.basicOpen f
参数：x : V；h : ↑x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.isBasis_basicOpen`：isBasis_basicOpen (X : Scheme) [IsA
ffine X] : Opens.IsBasis (Set.range (X.basicOpen : Γ(X, ⊤) -> X.Opens))
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Opens.mem_basicOpen_toScheme`：∀ {X : AlgebraicG
eometry.Scheme} {U : X.Opens} {V : (↑U).Opens} {r : ↑((↑U).presheaf.obj (Opposit
e.op V))} {x : ↥U},   x ∈ (↑U).basicOpen r …
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.image_basicOpen`：image_basicOpen {U : X.Opens} 
(r : Γ(X, U)) : f ''ᵁ X.basicOpen r = Y.basicOpen ((f.appIso U).inv r)
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_appIso`：ι_appIso (V) : U.ι.appIso V = I
so.refl _
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_mono`：image_mono {U V : X.Opens} (e :
 U <= V) : f ''ᵁ U <= f ''ᵁ V
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_preimage_le`：image_preimage_le (U : Y
.Opens) : f ''ᵁ f ⁻¹ᵁ U <= U
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Opens.topIso_hom`：∀ {X : AlgebraicGeometry.Sche
me} (U : X.Opens), U.topIso.hom = X.presheaf.map (CategoryTheory.eqToHom ⋯).op
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res_eq`：basicOpen_res_eq (i : op U ⟶ 
op V) [IsIso i] : X.basicOpen (X.presheaf.map i f) = X.basicOpen f
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem exists_basicOpen_le {V : X.Opens} (x : V) (h : ↑x ∈ U) :
    ∃ f : Γ(X, U), X.basicOpen f ≤ V ∧ ↑x ∈ X.basicOpen f := by
  have : IsAffine _ := hU
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, h₁, h₂ : _ ≤ U.ι ⁻¹ᵁ V⟩ :=
    (isBasis_basicOpen U).exists_subset_of_mem_open (x.2 : (⟨x, h⟩ : U) ∈ _) (U.ι ⁻¹ᵁ V).isOpen
  replace h₁ : x.1 ∈ X.basicOpen r := by simpa [U.mem_basicOpen_toScheme] using! h₁
  replace h₂ : X.basicOpen r ≤ V := by
    simpa [Scheme.image_basicOpen] using! (U.ι.image_mono h₂).trans (U.ι.image_preimage_le _)
  exact ⟨U.topIso.hom.hom r, by simp [Scheme.Opens.toScheme_presheaf_obj, h₁, h₂]⟩

set_option backward.isDefEq.respectTransparency.types false in
noncomputable
/-
**AlgebraicGeometry.IsAffineOpen.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.I
sAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : CommRingCat} {U} : Algebra R Γ(Spec R, U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).presheaf.obj _))

@[simp]
/-
**AlgebraicGeometry.IsAffineOpen.algebraMap_Spec_obj** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.IsAffineOpen`。
形式化陈述：algebraMap_Spec_obj {R : CommRingCat} {U} : algebraMap R Γ(Spec R, U) = ((
Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op).hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma algebraMap_Spec_obj {R : CommRingCat} {U} : algebraMap R Γ(Spec R, U) =
    ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsAffineOpen.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.I
sAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : CommRingCat} {f : R} :
    IsLocalization.Away f Γ(Spec R, PrimeSpectrum.basicOpen f) :=
  inferInstanceAs (IsLocalization.Away f
    ((Spec.structureSheaf R).obj.obj (op <| PrimeSpectrum.basicOpen f)))

/-- Given an affine open U and some `f : U`,
this is the canonical map `Γ(𝒪ₓ, D(f)) ⟶ Γ(Spec 𝒪ₓ(U), D(f))`
This is an isomorphism, as witnessed by an `IsIso` instance. -/
/-
**AlgebraicGeometry.IsAffineOpen.basicOpenSectionsToAffine** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：basicOpenSectionsToAffine : Γ(X, X.basicOpen f) ⟶ Γ(Spec Γ(X, U), PrimeSpe
ctrum.basicOpen f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an affine open U and some `f : U`,
this is the canonical map `Γ(𝒪ₓ, D(f)) ⟶ Γ(Spec 𝒪ₓ(U), D(f))`
This is an isomorphism, as witnessed by an `IsIso` instance.
-/
def basicOpenSectionsToAffine :
    Γ(X, X.basicOpen f) ⟶ Γ(Spec Γ(X, U), PrimeSpectrum.basicOpen f) :=
  hU.fromSpec.app (X.basicOpen f) ≫
    (Spec Γ(X, U)).presheaf.map (eqToHom (hU.fromSpec_preimage_basicOpen f).symm).op

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsAffineOpen.basicOpenSectionsToAffine_isIso** 是 Mathlib 中的一
个实例，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：basicOpenSectionsToAffine_isIso : IsIso (basicOpenSectionsToAffine hU f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsIso.comp_isIso'`：comp_isIso' (_ : IsIso f) (_ : IsIso h
) : IsIso (f ≫ h)
· 使用引理 `AlgebraicGeometry.Scheme.Hom.isIso_app`：isIso_app (V : Y.Opens) (hV : V 
<= f.opensRange) : IsIso (f.app V)
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.opensRange_fromSpec`：opensRange_fromSpec 
: hU.fromSpec.opensRange = U
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
-/
instance basicOpenSectionsToAffine_isIso :
    IsIso (basicOpenSectionsToAffine hU f) :=
  (hU.fromSpec.isIso_app _ (hU.opensRange_fromSpec.symm ▸ X.basicOpen_le f)).comp_isIso'
    inferInstance

set_option backward.isDefEq.respectTransparency.types false in
include hU in
/-
**AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：isLocalization_basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalization.isLocalization_iff_of_ringEquiv`：isLocalization_iff_of_ri
ngEquiv (h : S ≃+* P) : IsLocalization M S ↔ haveI
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Algebra.algebra_ext`：algebra_ext {R : Type*} [CommSemiring R] {A : Type*
} [Semiring A] (P Q : Algebra R A) (h : forall r : R, (haveI
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.naturality_assoc`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) {U U' : Y.Opens} (i : Opposite.op U' ⟶ Opposite.op U) {Z :
 CommRingCat}   (h : X.presheaf.obj…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_self`：fromSpec_preimage
_self : hU.fromSpec ⁻¹ᵁ U = ⊤
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_app_self`：fromSpec_app_self : hU
.fromSpec.app U = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map (e
qToHom hU.fromSpec_preimage_self).op
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen`：∀ (R : Typ
e u) [inst : CommRing R] (r : R),   IsLocalization.Away r ↑((AlgebraicGeometry.S
pec.structureSheaf R).obj.obj (Opposite.op (PrimeS…
-/
theorem isLocalization_basicOpen :
    IsLocalization.Away f Γ(X, X.basicOpen f) := by
  apply
    (IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers f)
      (asIso <| basicOpenSectionsToAffine hU f).commRingCatIsoToRingEquiv).mpr
  convert! StructureSheaf.IsLocalization.to_basicOpen _ f using 1
  apply Algebra.algebra_ext
  intro _
  congr 1
  dsimp [CommRingCat.ofHom, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
    basicOpenSectionsToAffine]
  rw [hU.fromSpec.naturality_assoc, hU.fromSpec_app_self]
  rfl
/-
**AlgebraicGeometry.IsAffineOpen._root_.AlgebraicGeometry.isLocalization_away_of
_isAffine** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.AlgebraicGeometry.isLocalization_away_of_isAffine
    [IsAffine X] (r : Γ(X, ⊤)) :
    IsLocalization.Away r Γ(X, X.basicOpen r) :=
  isLocalization_basicOpen (isAffineOpen_top X) r
/-
**AlgebraicGeometry.IsAffineOpen.appLE_eq_away_map** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.IsAffineOpen`。
形式化陈述：appLE_eq_away_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAff
ineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (e) (r : Γ(Y, U)) : letI
参数：f : X ⟶ Y；hU : IsAffineOpen U；hV : IsAffineOpen V；e；r : Γ(Y, U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.Away.map.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (
S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] {P : Type u_3}   
[inst_3 : CommSemi…
· 使用引理 `CommRingCat.hom_ofHom`：hom_ofHom {R S : Type u} [CommRing R] [CommRing S
] (f : R ->+* S) : (ofHom f).hom = f
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_map`：appLE_map (e : V <= f ⁻¹ᵁ U) (i 
: op V ⟶ op V') : f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.tra
ns e)
· 使用引理 `AlgebraicGeometry.Scheme.Hom.map_appLE`：map_appLE (e : V <= f ⁻¹ᵁ U) (i 
: op U' ⟶ op U) : Y.presheaf.map i ≫ f.appLE U V e = f.appLE U' V (e.trans ((Ope
ns.map f.base).map i.unop).l…
-/
lemma appLE_eq_away_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e) (r : Γ(Y, U)) :
    letI := hU.isLocalization_basicOpen r
    letI := hV.isLocalization_basicOpen (f.appLE U V e r)
    f.appLE (Y.basicOpen r) (X.basicOpen (f.appLE U V e r)) (by simp [Scheme.Hom.appLE]) =
        CommRingCat.ofHom (IsLocalization.Away.map _ _ (f.appLE U V e).hom r) := by
  let := hU.isLocalization_basicOpen r
  let := hV.isLocalization_basicOpen (f.appLE U V e r)
  ext : 1
  apply IsLocalization.ringHom_ext (.powers r)
  rw [IsLocalization.Away.map, CommRingCat.hom_ofHom, IsLocalization.map_comp,
    RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.IsAffineOpen.app_basicOpen_eq_away_map** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：app_basicOpen_eq_away_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU
 : IsAffineOpen U) (h : IsAffineOpen (f ⁻¹ᵁ U)) (r : Γ(Y, U)) : haveI
参数：f : X ⟶ Y；hU : IsAffineOpen U；h : IsAffineOpen (f ⁻¹ᵁ U)；r : Γ(Y, U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.Away.map.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (
S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] {P : Type u_3}   
[inst_3 : CommSemi…
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用引理 `CommRingCat.hom_ofHom`：hom_ofHom {R S : Type u} [CommRing R] [CommRing S
] (f : R ->+* S) : (ofHom f).hom = f
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Opposite.op_injective`：op_injective : Function.Injective (op : α -> αᵒᵖ)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma app_basicOpen_eq_away_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (h : IsAffineOpen (f ⁻¹ᵁ U)) (r : Γ(Y, U)) :
    haveI := hU.isLocalization_basicOpen r
    haveI := h.isLocalization_basicOpen (f.app U r)
    f.app (Y.basicOpen r) =
      (CommRingCat.ofHom
        (IsLocalization.Away.map Γ(Y, Y.basicOpen r) Γ(X, X.basicOpen (f.app U r)) (f.app U).hom r)
        ≫ X.presheaf.map (eqToHom (by simp)).op) := by
  have := hU.isLocalization_basicOpen r
  have := h.isLocalization_basicOpen (f.app U r)
  ext : 1
  apply IsLocalization.ringHom_ext (.powers r)
  rw [IsLocalization.Away.map, CommRingCat.hom_comp, RingHom.comp_assoc, CommRingCat.hom_ofHom,
    IsLocalization.map_comp, RingHom.algebraMap_toAlgebra,
    RingHom.algebraMap_toAlgebra, ← RingHom.comp_assoc, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, ← X.presheaf.map_comp]
  simp

set_option backward.defeqAttrib.useBackward true in
/-- `f.app (Y.basicOpen r)` is isomorphic to map induced on localizations
`Γ(Y, Y.basicOpen r) ⟶ Γ(X, X.basicOpen (f.app U r))` -/
/-
**AlgebraicGeometry.IsAffineOpen.appBasicOpenIsoAwayMap** 是 Mathlib 中的一个定义，位于命名空
间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：appBasicOpenIsoAwayMap {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : 
IsAffineOpen U) (h : IsAffineOpen (f ⁻¹ᵁ U)) (r : Γ(Y, U)) : haveI
参数：f : X ⟶ Y；hU : IsAffineOpen U；h : IsAffineOpen (f ⁻¹ᵁ U)；r : Γ(Y, U)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)

--- 原说明 ---
`f.app (Y.basicOpen r)` is isomorphic to map induced on localizations
`Γ(Y, Y.basicOpen r) ⟶ Γ(X, X.basicOpen (f.app U r))`
-/
def appBasicOpenIsoAwayMap {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (h : IsAffineOpen (f ⁻¹ᵁ U)) (r : Γ(Y, U)) :
    haveI := hU.isLocalization_basicOpen r
    haveI := h.isLocalization_basicOpen (f.app U r)
    Arrow.mk (f.app (Y.basicOpen r)) ≅
      Arrow.mk (CommRingCat.ofHom (IsLocalization.Away.map Γ(Y, Y.basicOpen r)
        Γ(X, X.basicOpen (f.app U r)) (f.app U).hom r)) :=
  Arrow.isoMk (Iso.refl _) (X.presheaf.mapIso (eqToIso (by simp)).op) <| by
    simp [hU.app_basicOpen_eq_away_map f h]
    rfl

include hU in
/-
**AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：isLocalization_of_eq_basicOpen {V : X.Opens} (i : V ⟶ U) (e : V = X.basicO
pen f) : @IsLocalization.Away _ _ f Γ(X, V) _ (X.presheaf.map i.op).hom.toAlgebr
a
参数：i : V ⟶ U；e : V = X.basicOpen f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isLocalization_of_eq_basicOpen {V : X.Opens} (i : V ⟶ U) (e : V = X.basicOpen f) :
    @IsLocalization.Away _ _ f Γ(X, V) _ (X.presheaf.map i.op).hom.toAlgebra := by
  subst e; exact isLocalization_basicOpen hU f
/-
**AlgebraicGeometry.IsAffineOpen._root_.AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于
命名空间 `AlgebraicGeometry.IsAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.AlgebraicGeometry.Γ_restrict_isLocalization
    (X : Scheme.{u}) [IsAffine X] (r : Γ(X, ⊤)) :
    IsLocalization.Away r Γ(X.basicOpen r, ⊤) :=
  (isAffineOpen_top X).isLocalization_of_eq_basicOpen r _ (Opens.isOpenEmbedding_obj_top _)

include hU in
/-
**AlgebraicGeometry.IsAffineOpen.basicOpen_basicOpen_is_basicOpen** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：basicOpen_basicOpen_is_basicOpen (g : Γ(X, X.basicOpen f)) : exists f' : Γ
(X, U), X.basicOpen f' = X.basicOpen g
参数：g : Γ(X, X.basicOpen f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `IsLocalization.surj''`：surj'' (z : S) : exists (r : R) (m : M), z = r • 
(toInvSubmonoid M S m : S)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_mul`：basicOpen_mul : X.basicOpen (f *
 g) = X.basicOpen f ⊓ X.basicOpen g
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_of_isUnit`：basicOpen_of_isUnit {f : Γ
(X, U)} (hf : IsUnit f) : X.basicOpen f = U
· 使用定理 `Submonoid.leftInv_le_isUnit`：leftInv_le_isUnit : S.leftInv <= IsUnit.sub
monoid M
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem basicOpen_basicOpen_is_basicOpen (g : Γ(X, X.basicOpen f)) :
    ∃ f' : Γ(X, U), X.basicOpen f' = X.basicOpen g := by
  have := isLocalization_basicOpen hU f
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.surj'' (Submonoid.powers f) g
  use f * x
  rw [Algebra.smul_def, Scheme.basicOpen_mul, Scheme.basicOpen_mul, RingHom.algebraMap_toAlgebra,
    Scheme.basicOpen_res]
  refine (inf_eq_left.mpr (inf_le_left.trans_eq (Scheme.basicOpen_of_isUnit _ ?_).symm)).symm
  exact
    Submonoid.leftInv_le_isUnit _
      (IsLocalization.toInvSubmonoid (Submonoid.powers f) (Γ(X, X.basicOpen f))
        _).prop

include hU in
/-
**AlgebraicGeometry.IsAffineOpen._root_.AlgebraicGeometry.exists_basicOpen_le_af
fine_inter** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgebraicGeometry.exists_basicOpen_le_affine_inter
    {V : X.Opens} (hV : IsAffineOpen V) (x : X) (hx : x ∈ U ⊓ V) :
    ∃ (f : Γ(X, U)) (g : Γ(X, V)), X.basicOpen f = X.basicOpen g ∧ x ∈ X.basicOpen f := by
  obtain ⟨f, hf₁, hf₂⟩ := hU.exists_basicOpen_le ⟨x, hx.2⟩ hx.1
  obtain ⟨g, hg₁, hg₂⟩ := hV.exists_basicOpen_le ⟨x, hf₂⟩ hx.2
  obtain ⟨f', hf'⟩ :=
    basicOpen_basicOpen_is_basicOpen hU f (X.presheaf.map (homOfLE hf₁ : _ ⟶ V).op g)
  replace hf' := (hf'.trans (RingedSpace.basicOpen_res _ _ _)).trans (inf_eq_right.mpr hg₁)
  exact ⟨f', g, hf', hf'.symm ▸ hg₂⟩

/-- The prime ideal of `𝒪ₓ(U)` corresponding to a point `x : U`. -/
/-
**AlgebraicGeometry.IsAffineOpen.primeIdealOf** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.IsAffineOpen`。
形式化陈述：primeIdealOf (x : U) : PrimeSpectrum Γ(X, U)
参数：x : U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prime ideal of `𝒪ₓ(U)` corresponding to a point `x : U`.
-/
noncomputable def primeIdealOf (x : U) :
    PrimeSpectrum Γ(X, U) :=
  hU.isoSpec.hom x

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsAffineOpen.fromSpec_primeIdealOf** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：fromSpec_primeIdealOf (x : U) : hU.fromSpec (hU.primeIdealOf x) = x.1
参数：x : U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
theorem fromSpec_primeIdealOf (x : U) :
    hU.fromSpec (hU.primeIdealOf x) = x.1 := by
  dsimp only [IsAffineOpen.fromSpec, Subtype.coe_mk, IsAffineOpen.primeIdealOf]
  rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
  rfl

open IsLocalRing in
/-
**AlgebraicGeometry.IsAffineOpen.primeIdealOf_eq_map_closedPoint** 是 Mathlib 中的一
个定理，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：primeIdealOf_eq_map_closedPoint (x : U) : hU.primeIdealOf x = Spec.map (X.
presheaf.germ _ x x.2) (closedPoint _)
参数：x : U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsAffineOpen.isoSpec_hom_apply`：isoSpec_hom_apply (x :
 U) : hU.isoSpec.hom x = Spec.map (X.presheaf.germ U x x.2) (closedPoint _)
-/
theorem primeIdealOf_eq_map_closedPoint (x : U) :
    hU.primeIdealOf x = Spec.map (X.presheaf.germ _ x x.2) (closedPoint _) :=
  hU.isoSpec_hom_apply _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：comap_primeIdealOf_appLE {f : X ⟶ Y} {x : X} (U : Y.Opens) (hU : IsAffineO
pen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V <= f ⁻¹ᵁ U) (hx : x in V) : 
(hV.primeIdealOf ⟨x, hx⟩).comap (f.appLE U V hVU).hom = hU.primeIdealOf ⟨f x, hV
U hx⟩
参数：U : Y.Opens；hU : IsAffineOpen U；V : X.Opens；hV : IsAffineOpen V；hVU : V <= f 
⁻¹ᵁ U；hx : x in V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE`：∀ {X Y : Algebraic
Geometry.Scheme} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)   (hUV : V ≤ (Topologic
alSpace.Opens.map f.base).obj U),   Catego…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `AlgebraicGeometry.Scheme.Hom.coe_resLE_apply`：coe_resLE_apply (x : V) : 
(f.resLE U V e x).1 = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comap_primeIdealOf_appLE {f : X ⟶ Y} {x : X} (U : Y.Opens)
      (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    (hV.primeIdealOf ⟨x, hx⟩).comap (f.appLE U V hVU).hom = hU.primeIdealOf ⟨f x, hVU hx⟩ := by
  change Spec.map (f.appLE U V hVU) (hV.primeIdealOf ⟨x, hx⟩) = (hU.primeIdealOf ⟨f x, hVU hx⟩)
  simp only [IsAffineOpen.primeIdealOf, ← Scheme.Hom.comp_apply, IsAffineOpen.isoSpec_hom,
    Scheme.Opens.toSpecΓ_SpecMap_appLE]
  simp only [Scheme.Hom.comp_apply]
  congr 1
  apply Subtype.ext
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-- If a point `x : U` is a closed point, then its corresponding prime ideal is maximal. -/
/-
**AlgebraicGeometry.IsAffineOpen.primeIdealOf_isMaximal_of_isClosed** 是 Mathlib 
中的一个定理，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：primeIdealOf_isMaximal_of_isClosed (x : U) (hx : IsClosed {(x : X)}) : (hU
.primeIdealOf x).asIdeal.IsMaximal
参数：x : U；hx : IsClosed {(x : X)}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding'`：isOpenEmbedding' (U : Opens α) 
: IsOpenEmbedding (Subtype.val : U -> α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.isClosed_singleton_iff_isMaximal`：isClosed_singleton_iff_i
sMaximal (x : PrimeSpectrum R) : IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asId
eal.IsMaximal
· 使用定理 `AlgebraicGeometry.IsAffineOpen.primeIdealOf.eq_1`：∀ {X : AlgebraicGeomet
ry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) (x : ↥U),   hU.
primeIdealOf x = hU.isoSpec.hom x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Topology.IsClosedEmbedding.isClosed_iff_image_isClosed`：∀ {X : Type u_1}
 {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpa
ce Y],   Topology.IsClosedEmbedding f → ∀ {s…
· 使用引理 `IsHomeomorph.isClosedEmbedding`：isClosedEmbedding : IsClosedEmbedding f
· 使用引理 `TopCat.isIso_iff_isHomeomorph`：isIso_iff_isHomeomorph {X Y : TopCat.{u}}
 (f : X ⟶ Y) : IsIso f ↔ IsHomeomorph f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
If a point `x : U` is a closed point, then its corresponding prime ideal is maxi
mal.
-/
theorem primeIdealOf_isMaximal_of_isClosed (x : U) (hx : IsClosed {(x : X)}) :
    (hU.primeIdealOf x).asIdeal.IsMaximal := by
  have hx₀ : IsClosed {x} := by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective]
      using hx.preimage U.isOpenEmbedding'.continuous
  apply (hU.primeIdealOf x).isClosed_singleton_iff_isMaximal.mp
  rw [primeIdealOf, ← Set.image_singleton]
  refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed <|
    IsHomeomorph.isClosedEmbedding ?_).mp hx₀
  apply (TopCat.isIso_iff_isHomeomorph _).mp
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsAffineOpen.isLocalization_stalk'** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：isLocalization_stalk' (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y in U
) : @IsLocalization.AtPrime (R
参数：y : PrimeSpectrum Γ(X, U)；hy : hU.fromSpec y in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] (x 
: ↥X),   CategoryTheory.IsIso (AlgebraicGeometry.Sch…
· 使用定理 `IsLocalization.isLocalization_iff_of_ringEquiv`：isLocalization_iff_of_ri
ngEquiv (h : S ≃+* P) : IsLocalization M S ↔ haveI
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_self`：fromSpec_preimage
_self : hU.fromSpec ⁻¹ᵁ U = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.germ_stalkMap`：germ_stalkMap (U : Y.Opens) 
(x : X) (hx : f x in U) : Y.presheaf.germ U (f x) hx ≫ f.stalkMap x = f.app U ≫ 
X.presheaf.germ (f ⁻¹ᵁ U) x hx
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_app_self`：fromSpec_app_self : hU
.fromSpec.app U = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map (e
qToHom hU.fromSpec_preimage_self).op
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `TopCat.Presheaf.germ_res'`：germ_res' (F : X.Presheaf C) {U V : Opens X} 
(i : op V ⟶ op U) (x : X) (hx : x in U) : F.map i ≫ F.germ U x hx = F.germ V x (
i.unop.le hx)
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`：∀ (R : Type u)
 [inst : CommRing R] (p : PrimeSpectrum R),   IsLocalization.AtPrime (↑((Algebra
icGeometry.Spec.structureSheaf R).presheaf.sta…
-/
theorem isLocalization_stalk' (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y ∈ U) :
    @IsLocalization.AtPrime
      (R := Γ(X, U))
      (S := X.presheaf.stalk <| hU.fromSpec y) _ _
      ((TopCat.Presheaf.algebra_section_stalk X.presheaf _)) y.asIdeal _ := by
  apply
    (@IsLocalization.isLocalization_iff_of_ringEquiv (R := Γ(X, U))
      (S := X.presheaf.stalk (hU.fromSpec y)) _ y.asIdeal.primeCompl _
      (TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩) _ _
      (asIso <| hU.fromSpec.stalkMap y).commRingCatIsoToRingEquiv).mpr
  convert StructureSheaf.IsLocalization.to_stalk Γ(X, U) y
  delta IsLocalization.AtPrime StructureSheaf.stalkAlgebra
  congr!
  simp [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, IsAffineOpen.fromSpec_app_self]
  rfl
/-
**AlgebraicGeometry.IsAffineOpen.isLocalization_stalk** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.IsAffineOpen`。
形式化陈述：isLocalization_stalk (x : U) : IsLocalization.AtPrime (X.presheaf.stalk x)
 (hU.primeIdealOf x).asIdeal
参数：x : U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_primeIdealOf`：fromSpec_primeIdea
lOf (x : U) : hU.fromSpec (hU.primeIdealOf x) = x.1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk'`：isLocalization_sta
lk' (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y in U) : @IsLocalization.AtPr
ime (R
-/
theorem isLocalization_stalk (x : U) :
    IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asIdeal := by
  rcases x with ⟨x, hx⟩
  set y := hU.primeIdealOf ⟨x, hx⟩ with hy
  have : hU.fromSpec y = x := hy ▸ hU.fromSpec_primeIdealOf ⟨x, hx⟩
  clear_value y
  subst this
  exact hU.isLocalization_stalk' y hx
/-
**AlgebraicGeometry.IsAffineOpen.stalkMap_injective** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.IsAffineOpen`。
形式化陈述：stalkMap_injective (f : X ⟶ Y) {U : Opens Y} (hU : IsAffineOpen U) (x : X)
 (hx : f x in U) (h : forall g, f.stalkMap x (Y.presheaf.germ U (f x) hx g) = 0 
-> Y.presheaf.germ U (f x) hx g = 0) : Function.Injective (f.stalkMap x)
参数：f : X ⟶ Y；hU : IsAffineOpen U；x : X；hx : f x in U；h : forall g, f.stalkMap x 
(Y.presheaf.germ U (f x) hx g) = 0 -> Y.presheaf.germ U (f x) hx g = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.injective_of_map_algebraMap_zero`：injective_of_map_algebr
aMap_zero {T} [CommRing T] (f : S ->+* T) (h : forall x, f (algebraMap R S x) = 
0 -> algebraMap R S x = 0) : Function…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`：isLocalization_stal
k (x : U) : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asId
eal
-/
lemma stalkMap_injective (f : X ⟶ Y) {U : Opens Y} (hU : IsAffineOpen U) (x : X)
    (hx : f x ∈ U)
    (h : ∀ g, f.stalkMap x (Y.presheaf.germ U (f x) hx g) = 0 →
      Y.presheaf.germ U (f x) hx g = 0) :
    Function.Injective (f.stalkMap x) := by
  let := Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
  apply (hU.isLocalization_stalk ⟨f x, hx⟩).injective_of_map_algebraMap_zero
  exact h

set_option backward.isDefEq.respectTransparency.types false in
include hU in
/-
**AlgebraicGeometry.IsAffineOpen.mem_ideal_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.IsAffineOpen`。
形式化陈述：mem_ideal_iff {s : Γ(X, U)} {I : Ideal Γ(X, U)} : s in I ↔ forall (x : X) 
(h : x in U), X.presheaf.germ U x h s in I.map (X.presheaf.germ U x h).hom
参数：X, U；X, U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk'`：isLocalization_sta
lk' (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y in U) : @IsLocalization.AtPr
ime (R
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submodule.mem_of_localization_maximal`：Submodule.mem_of_localization_max
imal (m : M) (N : Submodule R M) (h : forall (P : Ideal R) [P.IsMaximal], f P m 
in N.localized₀ P.primeComp…
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.localized₀_eq_restrictScalars_map`：Ideal.localized₀_eq_restrictSca
lars_map (I : Ideal R) : Submodule.localized₀ p (Algebra.linearMap R S) I = (I.m
ap (algebraMap R S)).restrict…
-/
lemma mem_ideal_iff {s : Γ(X, U)} {I : Ideal Γ(X, U)} :
    s ∈ I ↔ ∀ (x : X) (h : x ∈ U), X.presheaf.germ U x h s ∈ I.map (X.presheaf.germ U x h).hom := by
  refine ⟨fun hs x hxU ↦ Ideal.mem_map_of_mem _ hs, fun H ↦ ?_⟩
  let (x : _) : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec x)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf _
  have (P : Ideal Γ(X, U)) [hP : P.IsPrime] : IsLocalization.AtPrime _ P :=
      hU.isLocalization_stalk' ⟨P, hP⟩ (hU.isoSpec.inv _).2
  refine Submodule.mem_of_localization_maximal
      (fun P hP ↦ X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩))
      (fun P hP ↦ Algebra.linearMap _ _) _ _ ?_
  intro P hP
  rw [Ideal.localized₀_eq_restrictScalars_map]
  exact H _ _

include hU in
/-
**AlgebraicGeometry.IsAffineOpen.ideal_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.IsAffineOpen`。
形式化陈述：ideal_le_iff {I J : Ideal Γ(X, U)} : I <= J ↔ forall (x : X) (h : x in U),
 I.map (X.presheaf.germ U x h).hom <= J.map (X.presheaf.germ U x h).hom
参数：X, U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `AlgebraicGeometry.IsAffineOpen.mem_ideal_iff`：mem_ideal_iff {s : Γ(X, U)
} {I : Ideal Γ(X, U)} : s in I ↔ forall (x : X) (h : x in U), X.presheaf.germ U 
x h s in I.map (X.presheaf.germ U …
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
-/
lemma ideal_le_iff {I J : Ideal Γ(X, U)} :
    I ≤ J ↔ ∀ (x : X) (h : x ∈ U),
      I.map (X.presheaf.germ U x h).hom ≤ J.map (X.presheaf.germ U x h).hom :=
  ⟨fun h _ _ ↦ Ideal.map_mono h,
    fun H _ hs ↦ hU.mem_ideal_iff.mpr fun x hx ↦ H x hx (Ideal.mem_map_of_mem _ hs)⟩

include hU in
/-
**AlgebraicGeometry.IsAffineOpen.ideal_ext_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.IsAffineOpen`。
形式化陈述：ideal_ext_iff {I J : Ideal Γ(X, U)} : I = J ↔ forall (x : X) (h : x in U),
 I.map (X.presheaf.germ U x h).hom = J.map (X.presheaf.germ U x h).hom
参数：X, U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.IsAffineOpen.ideal_le_iff`：ideal_le_iff {I J : Ideal Γ
(X, U)} : I <= J ↔ forall (x : X) (h : x in U), I.map (X.presheaf.germ U x h).ho
m <= J.map (X.presheaf.germ U x h…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ideal_ext_iff {I J : Ideal Γ(X, U)} :
    I = J ↔ ∀ (x : X) (h : x ∈ U),
      I.map (X.presheaf.germ U x h).hom = J.map (X.presheaf.germ U x h).hom := by
  simp_rw [le_antisymm_iff, hU.ideal_le_iff, forall_and]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given affine opens `x ∈ V ⊆ f⁻¹(U)`, the stalk map of `f` at `x` is isomorphic to
`Localization.localRingHom` of `f.appLE U V`. -/
/-
**AlgebraicGeometry.IsAffineOpen.arrowStalkMapIso** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.IsAffineOpen`。
形式化陈述：arrowStalkMapIso (f : X ⟶ Y) {x : X} (U : Y.Opens) (hU : IsAffineOpen U) (
V : X.Opens) (hV : IsAffineOpen V) (hVU : V <= f ⁻¹ᵁ U) (hx : x in V) : Arrow.mk
 (f.stalkMap x) ≅ Arrow.mk (CommRingCat.ofHom <| Localization.localRingHom _ _ (
f.appLE U V hVU).hom congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU
 hx).1).symm)
参数：f : X ⟶ Y；U : Y.Opens；hU : IsAffineOpen U；V : X.Opens；hV : IsAffineOpen V；hVU
 : V <= f ⁻¹ᵁ U；hx : x in V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given affine opens `x ∈ V ⊆ f⁻¹(U)`, the stalk map of `f` at `x` is isomorphic t
o
`Localization.localRingHom` of `f.appLE U V`.
-/
def arrowStalkMapIso (f : X ⟶ Y) {x : X} (U : Y.Opens)
      (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
      (hx : x ∈ V) :
    Arrow.mk (f.stalkMap x) ≅ Arrow.mk (CommRingCat.ofHom <|
      Localization.localRingHom _ _ (f.appLE U V hVU).hom
        congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm) := by
  let := Y.presheaf.algebra_section_stalk ⟨f x, hVU hx⟩
  have := hU.isLocalization_stalk ⟨f x, hVU hx⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  refine Arrow.isoMk' _ _ ?_ ?_ ?_
  · exact ((IsLocalization.algEquiv (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal.primeCompl
      (Y.presheaf.stalk (f x))
      (Localization.AtPrime (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal)).toCommRingCatIso:)
  · exact ((IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (X.presheaf.stalk x)
      (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal)).toCommRingCatIso:)
  · rw [← Iso.comp_inv_eq]
    ext1
    apply IsLocalization.ringHom_ext
      (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal.primeCompl
    ext a
    dsimp [← AlgEquiv.symm_toRingEquiv]
    simp only [IsLocalization.map_eq, RingHom.id_apply, Localization.localRingHom_to_map,
      RingHomCompTriple.comp_apply]
    simp only [RingHom.algebraMap_toAlgebra, Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE,
      homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      X.presheaf.germ_res_apply]

/-- The basic open set of a section `f` on an affine open as an `X.affineOpens`. -/
@[simps]
/-
**AlgebraicGeometry.IsAffineOpen._root_.AlgebraicGeometry.Scheme.affineBasicOpen
** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basic open set of a section `f` on an affine open as an `X.affineOpens`.
-/
def _root_.AlgebraicGeometry.Scheme.affineBasicOpen
    (X : Scheme) {U : X.affineOpens} (f : Γ(X, U)) : X.affineOpens :=
  ⟨X.basicOpen f, U.prop.basicOpen f⟩
/-
**AlgebraicGeometry.IsAffineOpen._root_.AlgebraicGeometry.Scheme.affineBasicOpen
_le** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgebraicGeometry.Scheme.affineBasicOpen_le
    (X : Scheme) {V : X.affineOpens} (f : Γ(X, V.1)) : X.affineBasicOpen f ≤ V :=
  X.basicOpen_le f

include hU in
/--
In an affine open set `U`, a family of basic open covers `U` iff the sections span `Γ(X, U)`.
See `iSup_basicOpen_of_span_eq_top` for the inverse direction without the affine-ness assumption.
-/
/-
**AlgebraicGeometry.IsAffineOpen.iSup_basicOpen_eq_self_iff** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：iSup_basicOpen_eq_self_iff {s : Set Γ(X, U)} : ⨆ f : s, X.basicOpen (f : Γ
(X, U)) = U ↔ Ideal.span s = ⊤
参数：X, U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.range_fromSpec`：range_fromSpec : Set.rang
e hU.fromSpec = U
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `TopologicalSpace.Opens.iSup_def`：iSup_def {ι} (s : ι -> Opens α) : ⨆ i, 
s i = ⟨⋃ i, s i, isOpen_iUnion fun i => (s i).2⟩
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen`：fromSpec_pre
image_basicOpen : hU.fromSpec ⁻¹ᵁ X.basicOpen f = PrimeSpectrum.basicOpen f
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_self`：fromSpec_preimage
_self : hU.fromSpec ⁻¹ᵁ U = ⊤
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `Set.compl_univ_iff`：compl_univ_iff {s : Set α} : sᶜ = univ ↔ s = ∅
· 使用定理 `PrimeSpectrum.zeroLocus_iUnion`：zeroLocus_iUnion {ι : Sort*} (s : ι -> S
et R) : zeroLocus (⋃ i, s i) = ⋂ i, zeroLocus (s i)
· 使用定理 `PrimeSpectrum.zeroLocus_empty_iff_eq_top`：zeroLocus_empty_iff_eq_top {I 
: Ideal R} : zeroLocus (I : Set R) = ∅ ↔ I = ⊤
· 使用定理 `PrimeSpectrum.zeroLocus_span`：zeroLocus_span (s : Set R) : zeroLocus (Id
eal.span s : Set R) = zeroLocus s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
In an affine open set `U`, a family of basic open covers `U` iff the sections sp
an `Γ(X, U)`.
See `iSup_basicOpen_of_span_eq_top` for the inverse direction without the affine
-ness assumption.
-/
theorem iSup_basicOpen_eq_self_iff {s : Set Γ(X, U)} :
    ⨆ f : s, X.basicOpen (f : Γ(X, U)) = U ↔ Ideal.span s = ⊤ := by
  trans ⋃ i : s, (PrimeSpectrum.basicOpen i.1).1 = Set.univ
  · trans hU.fromSpec ⁻¹' (⨆ f : s, X.basicOpen (f : Γ(X, U))).1 = hU.fromSpec ⁻¹' U.1
    · refine ⟨fun h => by rw [h], ?_⟩
      intro h
      apply_fun Set.image hU.fromSpec at h
      rw [Set.image_preimage_eq_inter_range, Set.image_preimage_eq_inter_range, hU.range_fromSpec]
        at h
      simp only [Set.inter_self, Opens.carrier_eq_coe, Set.inter_eq_right] at h
      ext1
      refine Set.Subset.antisymm ?_ h
      simp only [Set.iUnion_subset_iff, SetCoe.forall, Opens.coe_iSup]
      intro x _
      exact X.basicOpen_le x
    · simp only [Opens.iSup_def, Set.preimage_iUnion]
      congr! 1
      · refine congr_arg (Set.iUnion ·) ?_
        ext1 x
        exact congr_arg Opens.carrier (hU.fromSpec_preimage_basicOpen _)
      · exact congr_arg Opens.carrier hU.fromSpec_preimage_self
  · simp only [Opens.carrier_eq_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
    rw [← Set.compl_iInter, Set.compl_univ_iff, ← PrimeSpectrum.zeroLocus_iUnion, ←
      PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_span]
    simp only [Set.iUnion_singleton_eq_range, Subtype.range_val_subtype, Set.ofPred_mem_eq]

include hU in
/-
**AlgebraicGeometry.IsAffineOpen.self_le_iSup_basicOpen_iff** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：self_le_iSup_basicOpen_iff {s : Set Γ(X, U)} : (U <= ⨆ f : s, X.basicOpen 
f.1) ↔ Ideal.span s = ⊤
参数：X, U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.iSup_basicOpen_eq_self_iff`：iSup_basicOpe
n_eq_self_iff {s : Set Γ(X, U)} : ⨆ f : s, X.basicOpen (f : Γ(X, U)) = U ↔ Ideal
.span s = ⊤
· 使用定理 `comm`：comm [Std.Symm r] {a b : α} : r a b ↔ r b a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem self_le_iSup_basicOpen_iff {s : Set Γ(X, U)} :
    (U ≤ ⨆ f : s, X.basicOpen f.1) ↔ Ideal.span s = ⊤ := by
  rw [← hU.iSup_basicOpen_eq_self_iff, @comm _ Eq]
  refine ⟨fun h => le_antisymm h ?_, le_of_eq⟩
  simp only [iSup_le_iff, SetCoe.forall]
  intro x _
  exact X.basicOpen_le x

end IsAffineOpen

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine open cover given by a covering family of affine opens. -/
@[simps I₀ X f]
/-
**AlgebraicGeometry.Scheme.AffineOpenCover.ofIsOpenCover** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.AffineOpenCover`。
形式化陈述：{X : AlgebraicGeometry.Scheme} →   {ι : Type u_1} →     (U : ι → X.Opens) 
→       TopologicalSpace.IsOpenCover U → (∀ (i : ι), AlgebraicGeometry.IsAffineO
pen (U i)) → X.AffineOpenCover
参数：U : ι → X.Opens；∀ (i : ι), AlgebraicGeometry.IsAffineOpen (U i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine open cover given by a covering family of affine opens.
-/
def Scheme.AffineOpenCover.ofIsOpenCover {X : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
    (hU : IsOpenCover U) (hU' : ∀ i, IsAffineOpen (U i)) :
    AffineOpenCover X where
  I₀ := ι
  X i := Γ(X, U i)
  f i := (hU' i).fromSpec
  idx x := (hU.exists_mem x).choose
  covers x :=
    ⟨(hU' _).isoSpec.hom ⟨_, (hU.exists_mem x).choose_spec⟩, by simp [← Scheme.Hom.comp_apply]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open _root_.PrimeSpectrum in
/-- The restriction of `Spec.map f` to a basic open `D(r)` is isomorphic to `Spec.map` of the
localization of `f` away from `r`. -/
/-
**AlgebraicGeometry.SpecMapRestrictBasicOpenIso** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：SpecMapRestrictBasicOpenIso {R S : CommRingCat} (f : R ⟶ S) (r : R) : Arro
w.mk (Spec.map f ∣_ (PrimeSpectrum.basicOpen r)) ≅ Arrow.mk (Spec.map <| CommRin
gCat.ofHom (Localization.awayMap f.hom r))
参数：f : R ⟶ S；r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of `Spec.map f` to a basic open `D(r)` is isomorphic to `Spec.ma
p` of the
localization of `f` away from `r`.
-/
noncomputable def SpecMapRestrictBasicOpenIso {R S : CommRingCat} (f : R ⟶ S) (r : R) :
    Arrow.mk (Spec.map f ∣_ (PrimeSpectrum.basicOpen r)) ≅
      Arrow.mk (Spec.map <| CommRingCat.ofHom (Localization.awayMap f.hom r)) := by
  refine Arrow.isoMk ?_ ?_ ?_
  · exact (Spec _).isoOfEq (comap_basicOpen _ _) ≪≫ basicOpenIsoSpecAway (f.hom r)
  · exact basicOpenIsoSpecAway r
  · have hcomp : CommRingCat.ofHom (algebraMap R (Localization.Away r)) ≫
        CommRingCat.ofHom (Localization.awayMap f.hom r) =
        f ≫ CommRingCat.ofHom (algebraMap S (Localization.Away (f.hom r))) := by
      ext x
      simp [Localization.awayMap, IsLocalization.Away.map]
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap R _)))]
    simp only [Arrow.mk_hom, Category.assoc, ← Spec.map_comp]
    simp [hcomp]
/-
**AlgebraicGeometry.stalkMap_injective_of_isAffine** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry`。
形式化陈述：stalkMap_injective_of_isAffine {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] (x 
: X) (h : forall g, f.stalkMap x (Y.presheaf.Γgerm (f x) g) = 0 -> Y.presheaf.Γg
erm (f x) g = 0) : Function.Injective (f.stalkMap x)
参数：f : X ⟶ Y；x : X；h : forall g, f.stalkMap x (Y.presheaf.Γgerm (f x) g) = 0 -> 
Y.presheaf.Γgerm (f x) g = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsAffineOpen.stalkMap_injective`：stalkMap_injective (f
 : X ⟶ Y) {U : Opens Y} (hU : IsAffineOpen U) (x : X) (hx : f x in U) (h : foral
l g, f.stalkMap x (Y.presheaf.germ U (f…
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `trivial`：True
-/
lemma stalkMap_injective_of_isAffine {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] (x : X)
    (h : ∀ g, f.stalkMap x (Y.presheaf.Γgerm (f x) g) = 0 → Y.presheaf.Γgerm (f x) g = 0) :
    Function.Injective (f.stalkMap x) :=
  (isAffineOpen_top Y).stalkMap_injective f x trivial h

set_option backward.isDefEq.respectTransparency.types false in
/--
Given a spanning set of `Γ(X, U)`, the corresponding basic open sets cover `U`.
See `IsAffineOpen.basicOpen_union_eq_self_iff` for the inverse direction for affine open sets.
-/
/-
**AlgebraicGeometry.iSup_basicOpen_of_span_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry`。
形式化陈述：iSup_basicOpen_of_span_eq_top {X : Scheme} (U) (s : Set Γ(X, U)) (hs : Ide
al.span s = ⊤) : (⨆ i in s, X.basicOpen i) = U
参数：U；s : Set Γ(X, U)；hs : Ideal.span s = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用引理 `SetLike.mem_of_subset`：mem_of_subset {s : Set B} (hp : s subseteq p) {x 
: B} (hx : x in s) : x in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.iSup_basicOpen_eq_self_iff`：iSup_basicOpe
n_eq_self_iff {s : Set Γ(X, U)} : ⨆ f : s, X.basicOpen (f : Γ(X, U)) = U ↔ Ideal
.span s = ⊤
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biUnion_and'`：biUnion_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iUnion_iUnion_eq_right`：iUnion_iUnion_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋃ (x) (h : b = x), s x h = s b rfl
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.subset_iUnion₂`：subset_iUnion₂ {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : s i j subseteq ⋃ (i') (j'), s i' j'

--- 原说明 ---
Given a spanning set of `Γ(X, U)`, the corresponding basic open sets cover `U`.
See `IsAffineOpen.basicOpen_union_eq_self_iff` for the inverse direction for aff
ine open sets.
-/
lemma iSup_basicOpen_of_span_eq_top {X : Scheme} (U) (s : Set Γ(X, U))
    (hs : Ideal.span s = ⊤) : (⨆ i ∈ s, X.basicOpen i) = U := by
  apply le_antisymm
  · rw [iSup₂_le_iff]
    exact fun i _ ↦ X.basicOpen_le i
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    refine SetLike.mem_of_subset ?_ hxV
    rw [← (hV.iSup_basicOpen_eq_self_iff (s := X.presheaf.map (homOfLE hVU).op '' s)).mpr
      (by rw [← Ideal.map_span, hs, Ideal.map_top])]
    simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Set.iUnion_coe_set, Set.mem_image,
      Set.iUnion_exists, Set.biUnion_and', Set.iUnion_iUnion_eq_right, Scheme.basicOpen_res,
      Opens.coe_inf, Opens.coe_mk, Set.iUnion_subset_iff]
    exact fun i hi ↦ (Set.inter_subset_right.trans
      (Set.subset_iUnion₂ (s := fun x _ ↦ (X.basicOpen x : Set X)) i hi))

/-- Let `P` be a predicate on the affine open sets of `X` satisfying
1. If `P` holds on `U`, then `P` holds on the basic open set of every section on `U`.
2. If `P` holds for a family of basic open sets covering `U`, then `P` holds for `U`.
3. There exists an affine open cover of `X` each satisfying `P`.

Then `P` holds for every affine open of `X`.

This is also known as the **Affine communication lemma** in [*The rising sea*][RisingSea]. -/
@[elab_as_elim]
/-
**AlgebraicGeometry.of_affine_open_cover** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：of_affine_open_cover {X : Scheme} {P : X.affineOpens -> Prop} {ι} (U : ι -
> X.affineOpens) (iSup_U : (⨆ i, U i : X.Opens) = ⊤) (V : X.affineOpens) (basicO
pen : forall (U : X.affineOpens) (f : Γ(X, U)), P U -> P (X.affineBasicOpen f)) 
(openCover : forall (U : X.affineOpens) (s : Finset (Γ(X, U))) (_ : Ideal.span (
s : Set (Γ(X, U))) = ⊤), (forall f : s, P (X.affineBasicOpen f.1)) -> P U) (hU :
 forall i, P (U i)) : P V
参数：U : ι -> X.affineOpens；iSup_U : (⨆ i, U i : X.Opens) = ⊤；V : X.affineOpens；ba
sicOpen : forall (U : X.affineOpens) (f : Γ(X, U)), P U -> P (X.affineBasicOpen 
f)；openCover : forall (U : X.affineOpens) (s : Finset (Γ(X, U))) (_ : Ideal.span
 (s : Set (Γ(X, U))) = ⊤), (forall f : s, P (X.affineBasicOpen f.1)) -> P U；hU :
 forall i, P (U i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.mem_iSup`：mem_iSup {ι} {x : α} {s : ι -> Opens α}
 : x in iSup s ↔ exists i, x in s i
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `AlgebraicGeometry.exists_basicOpen_le_affine_inter`：∀ {X : AlgebraicGeom
etry.Scheme} {U : X.Opens},   AlgebraicGeometry.IsAffineOpen U →     ∀ {V : X.Op
ens},       AlgebraicGeometry.IsAffineOp…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsAffineOpen.self_le_iSup_basicOpen_iff`：self_le_iSup_
basicOpen_iff {s : Set Γ(X, U)} : (U <= ⨆ f : s, X.basicOpen f.1) ↔ Ideal.span s
 = ⊤
· 使用定理 `iSup_range'`：iSup_range' (g : β -> α) (f : ι -> β) : ⨆ b : range f, g b 
= ⨆ i, g (f i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.span_eq_top_iff_finite`：span_eq_top_iff_finite (s : Set α) : span 
s = ⊤ ↔ exists s' : Finset α, ↑s' subseteq s ∧ span (s' : Set α) = ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Let `P` be a predicate on the affine open sets of `X` satisfying
1. If `P` holds on `U`, then `P` holds on the basic open set of every section on
 `U`.
2. If `P` holds for a family of basic open sets covering `U`, then `P` holds for
 `U`.
3. There exists an affine open cover of `X` each satisfying `P`.

Then `P` holds for every affine open of `X`.

This is also known as the **Affine communication lemma** in [*The rising sea*][R
isingSea].
-/
theorem of_affine_open_cover {X : Scheme} {P : X.affineOpens → Prop}
    {ι} (U : ι → X.affineOpens) (iSup_U : (⨆ i, U i : X.Opens) = ⊤)
    (V : X.affineOpens)
    (basicOpen : ∀ (U : X.affineOpens) (f : Γ(X, U)), P U → P (X.affineBasicOpen f))
    (openCover :
      ∀ (U : X.affineOpens) (s : Finset (Γ(X, U)))
        (_ : Ideal.span (s : Set (Γ(X, U))) = ⊤),
        (∀ f : s, P (X.affineBasicOpen f.1)) → P U)
    (hU : ∀ i, P (U i)) : P V := by
  have : ∀ (x : V.1), ∃ f : Γ(X, V), ↑x ∈ X.basicOpen f ∧ P (X.affineBasicOpen f) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (iSup_U.ge (Set.mem_univ x))
    obtain ⟨f, g, e, hf⟩ := exists_basicOpen_le_affine_inter V.prop (U i).prop x ⟨x.prop, hi⟩
    refine ⟨f, hf, ?_⟩
    convert! basicOpen _ g (hU i) using 1
    ext1
    exact e
  choose f hf₁ hf₂ using this
  suffices Ideal.span (Set.range f) = ⊤ by
    obtain ⟨t, ht₁, ht₂⟩ := (Ideal.span_eq_top_iff_finite _).mp this
    apply openCover V t ht₂
    rintro ⟨i, hi⟩
    obtain ⟨x, rfl⟩ := ht₁ hi
    exact hf₂ x
  rw [← V.prop.self_le_iSup_basicOpen_iff]
  intro x hx
  rw [iSup_range', Opens.mem_iSup]
  exact ⟨_, hf₁ ⟨x, hx⟩⟩

/-- If `φ` is a monomorphism in `CommRingCat`, it is not in general true that `Spec φ` is epi.
(`ℤ ⊆ ℤ[1/2]` but `Spec ℤ[1/2] ⟶ Spec ℤ` is not epi, since epi open immersions are isomorphisms)
But if the range of `f g : Spec R ⟶ X` are contained in an common affine open `U`, one can still
cancel `Spec.map φ ≫ f = Spec.map φ ≫ g` to get `f = g`. -/
/-
**AlgebraicGeometry.eq_of_SpecMap_comp_eq_of_isAffineOpen** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry`。
形式化陈述：eq_of_SpecMap_comp_eq_of_isAffineOpen {R S : CommRingCat} {X : Scheme} (φ 
: R ⟶ S) (hφ : Function.Injective φ) {f g : Spec R ⟶ X} (U : X.Opens) (hU : IsAf
fineOpen U) (hUf : f ⁻¹ᵁ U = ⊤) (hUg : g ⁻¹ᵁ U = ⊤) (H : Spec.map φ ≫ f = Spec.m
ap φ ≫ g) : f = g
参数：φ : R ⟶ S；hφ : Function.Injective φ；U : X.Opens；hU : IsAffineOpen U；hUf : f ⁻
¹ᵁ U = ⊤；hUg : g ⁻¹ᵁ U = ⊤；H : Spec.map φ ≫ f = Spec.map φ ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.mono_of_injective`：mono_of_injective {X 
Y : C} (f : X ⟶ Y) (i : Function.Injective f) : Mono f
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Opens.range_ι`：range_ι : Set.range U.ι = U
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.lift_fac`：lift_fac (H' : Set.range g s
ubseteq Set.range f) : lift f g H' ≫ f = g
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `AlgebraicGeometry.Spec.map_injective`：∀ {R S : CommRingCat}, Function.In
jective AlgebraicGeometry.Spec.map
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Spec.homEquiv_apply`：∀ {R S : CommRingCat} (f : Algebr
aicGeometry.Spec S ⟶ AlgebraicGeometry.Spec R),   AlgebraicGeometry.Spec.homEqui
v f = AlgebraicGeometry.Spe…
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用定理 `AlgebraicGeometry.Spec.map_preimage`：∀ {R S : CommRingCat} (f : Algebrai
cGeometry.Spec S ⟶ AlgebraicGeometry.Spec R),   AlgebraicGeometry.Spec.map (Alge
braicGeometry.Spec.preima…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `φ` is a monomorphism in `CommRingCat`, it is not in general true that `Spec 
φ` is epi.
(`ℤ ⊆ ℤ[1/2]` but `Spec ℤ[1/2] ⟶ Spec ℤ` is not epi, since epi open immersions a
re isomorphisms)
But if the range of `f g : Spec R ⟶ X` are contained in an common affine open `U
`, one can still
cancel `Spec.map φ ≫ f = Spec.map φ ≫ g` to get `f = g`.
-/
lemma eq_of_SpecMap_comp_eq_of_isAffineOpen {R S : CommRingCat} {X : Scheme}
    (φ : R ⟶ S) (hφ : Function.Injective φ)
    {f g : Spec R ⟶ X} (U : X.Opens) (hU : IsAffineOpen U) (hUf : f ⁻¹ᵁ U = ⊤) (hUg : g ⁻¹ᵁ U = ⊤)
    (H : Spec.map φ ≫ f = Spec.map φ ≫ g) : f = g := by
  have : Mono φ := ConcreteCategory.mono_of_injective _ hφ
  rw [← IsOpenImmersion.lift_fac U.ι f (by simpa [Set.range_subset_iff] using fun x hx ↦ hUf.ge hx),
    ← IsOpenImmersion.lift_fac U.ι g (by simpa [Set.range_subset_iff] using fun x hx ↦ hUg.ge hx)]
  congr 1
  rw [← cancel_mono hU.isoSpec.hom, ← Spec.homEquiv.injective.eq_iff,
    ← cancel_mono φ, ← Spec.map_injective.eq_iff]
  simp [← cancel_mono U.ι, H]

section ZeroLocus

namespace Scheme

open ConcreteCategory

variable (X : Scheme.{u})

/-- On a scheme `X`, the preimage of the zero locus of the prime spectrum
of `Γ(X, ⊤)` under `X.toSpecΓ : X ⟶ Spec Γ(X, ⊤)` agrees with the associated zero locus on `X`. -/
/-
**AlgebraicGeometry.Scheme.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.S
cheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On a scheme `X`, the preimage of the zero locus of the prime spectrum
of `Γ(X, ⊤)` under `X.toSpecΓ : X ⟶ Spec Γ(X, ⊤)` agrees with the associated zer
o locus on `X`.
-/
lemma toSpecΓ_preimage_zeroLocus (s : Set Γ(X, ⊤)) :
    X.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus s = X.zeroLocus s :=
  LocallyRingedSpace.toΓSpec_preimage_zeroLocus_eq s

set_option backward.isDefEq.respectTransparency.types false in
/-- If `X` is affine, the image of the zero locus of global sections of `X` under `X.isoSpec`
is the zero locus in terms of the prime spectrum of `Γ(X, ⊤)`. -/
/-
**AlgebraicGeometry.Scheme.isoSpec_image_zeroLocus** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme`。
形式化陈述：isoSpec_image_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) : X.isoSpec.hom '' 
X.zeroLocus s = PrimeSpectrum.zeroLocus s
参数：s : Set Γ(X, ⊤)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.toSpecΓ_preimage_zeroLocus`：toSpecΓ_preimage_ze
roLocus (s : Set Γ(X, ⊤)) : X.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus s = X.zeroLocu
s s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `CategoryTheory.ConcreteCategory.bijective_of_isIso`：bijective_of_isIso {
X Y : C} (f : X ⟶ Y) [IsIso f] : Function.Bijective f
· 使用定理 `AlgebraicGeometry.IsAffine.affine`：∀ {X : AlgebraicGeometry.Scheme} [sel
f : AlgebraicGeometry.IsAffine X], CategoryTheory.IsIso X.toSpecΓ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `X` is affine, the image of the zero locus of global sections of `X` under `X
.isoSpec`
is the zero locus in terms of the prime spectrum of `Γ(X, ⊤)`.
-/
lemma isoSpec_image_zeroLocus [IsAffine X]
    (s : Set Γ(X, ⊤)) :
    X.isoSpec.hom '' X.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  rw [← X.toSpecΓ_preimage_zeroLocus]
  simp [Scheme.isoSpec, Set.image_preimage_eq (h := (bijective_of_isIso _).surjective)]
/-
**AlgebraicGeometry.Scheme.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.S
cheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSpecΓ_image_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) :
    X.toSpecΓ '' X.zeroLocus s = PrimeSpectrum.zeroLocus s :=
  X.isoSpec_image_zeroLocus _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.isoSpec_inv_preimage_zeroLocus** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：isoSpec_inv_preimage_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) : X.isoSpec.
inv ⁻¹' X.zeroLocus s = PrimeSpectrum.zeroLocus s
参数：s : Set Γ(X, ⊤)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.toSpecΓ_preimage_zeroLocus`：toSpecΓ_preimage_ze
roLocus (s : Set Γ(X, ⊤)) : X.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus s = X.zeroLocu
s s
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_base`：comp_base {X Y Z : Scheme} (f : 
X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base
· 使用定理 `AlgebraicGeometry.Scheme.isoSpec_inv_toSpecΓ`：∀ (X : AlgebraicGeometry.S
cheme) [inst : AlgebraicGeometry.IsAffine X],   CategoryTheory.CategoryStruct.co
mp X.isoSpec.inv X.toSpecΓ =     C…
-/
lemma isoSpec_inv_preimage_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) :
    X.isoSpec.inv ⁻¹' X.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  rw [← toSpecΓ_preimage_zeroLocus, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
    X.isoSpec_inv_toSpecΓ]
  rfl
/-
**AlgebraicGeometry.Scheme.isoSpec_inv_image_zeroLocus** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.Scheme`。
形式化陈述：isoSpec_inv_image_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) : X.isoSpec.inv
 '' PrimeSpectrum.zeroLocus s = X.zeroLocus s
参数：s : Set Γ(X, ⊤)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.isoSpec_inv_preimage_zeroLocus`：isoSpec_inv_pre
image_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) : X.isoSpec.inv ⁻¹' X.zeroLocus s
 = PrimeSpectrum.zeroLocus s
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `CategoryTheory.ConcreteCategory.bijective_of_isIso`：bijective_of_isIso {
X Y : C} (f : X ⟶ Y) [IsIso f] : Function.Bijective f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma isoSpec_inv_image_zeroLocus [IsAffine X] (s : Set Γ(X, ⊤)) :
    X.isoSpec.inv '' PrimeSpectrum.zeroLocus s = X.zeroLocus s := by
  rw [← isoSpec_inv_preimage_zeroLocus, Set.image_preimage_eq]
  exact (bijective_of_isIso X.isoSpec.inv.base).surjective

/-- If `X` is an affine scheme, every closed set of `X` is the zero locus
of a set of global sections. -/
/-
**AlgebraicGeometry.Scheme.eq_zeroLocus_of_isClosed_of_isAffine** 是 Mathlib 中的一个
引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：eq_zeroLocus_of_isClosed_of_isAffine [IsAffine X] (s : Set X) : IsClosed s
 ↔ exists I : Ideal Γ(X, ⊤), s = X.zeroLocus (U
参数：s : Set X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.isClosed_iff_zeroLocus_ideal`：isClosed_iff_zeroLocus_ideal
 (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ exists I : Ideal R, Z = zeroLocus I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `CategoryTheory.ConcreteCategory.bijective_of_isIso`：bijective_of_isIso {
X Y : C} (f : X ⟶ Y) [IsIso f] : Function.Bijective f
· 使用引理 `AlgebraicGeometry.Scheme.zeroLocus_isClosed`：zeroLocus_isClosed {U : X.O
pens} (s : Set Γ(X, U)) : IsClosed (X.zeroLocus s)

--- 原说明 ---
If `X` is an affine scheme, every closed set of `X` is the zero locus
of a set of global sections.
-/
lemma eq_zeroLocus_of_isClosed_of_isAffine [IsAffine X] (s : Set X) :
    IsClosed s ↔ ∃ I : Ideal Γ(X, ⊤), s = X.zeroLocus (U := ⊤) I := by
  refine ⟨fun hs ↦ ?_, ?_⟩
  · let Z : Set (Spec Γ(X, ⊤)) := X.toΓSpecFun '' s
    have hZ : IsClosed Z := (X.isoSpec.hom.homeomorph).isClosedMap _ hs
    obtain ⟨I, (hI : Z = _)⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hZ
    use I
    simp only [← Scheme.toSpecΓ_preimage_zeroLocus, ← hI, Z]
    symm
    exact Set.preimage_image_eq _ (bijective_of_isIso X.isoSpec.hom.base).injective
  · rintro ⟨I, rfl⟩
    exact zeroLocus_isClosed X I.carrier

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Opens.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Opens.toSpecΓ_preimage_basicOpen {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, U)) :
    U.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen r = U.ι ⁻¹ᵁ X.basicOpen r := by
  dsimp [toSpecΓ]
  simp only [Scheme.toSpecΓ_preimage_basicOpen, preimage_basicOpen, ι_app, homOfLE_leOfHom]
  rw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.ι_preimage_self.symm).op,
    ← ConcreteCategory.comp_apply]
  congr 3
  simp [← Functor.map_comp]
  rfl

open Set.Notation in
/-
**AlgebraicGeometry.Scheme.Opens.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Opens.toSpecΓ_preimage_zeroLocus {X : Scheme.{u}} (U : X.Opens) (s : Set Γ(X, U)) :
    U.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus s = U.1 ↓∩ X.zeroLocus s := by
  ext x
  refine .trans (forall₂_congr fun y hy ↦ ?_) Set.mem_iInter₂.symm
  exact iff_not_comm.mp congr(x ∈ $(Opens.toSpecΓ_preimage_basicOpen U y)).to_iff.symm

end Scheme

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_zeroLocus** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsA
ffineOpen U)   (s : Set ↑(X.presheaf.obj (Opposite.op U))), ⇑hU.fromSpec ⁻¹' X.z
eroLocus s = PrimeSpectrum.zeroLocus s
参数：hU : AlgebraicGeometry.IsAffineOpen U；s : Set ↑(X.presheaf.obj (Opposite.op U
))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_image_basicOpen`：fromSpec_image_
basicOpen : hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f
-/
lemma IsAffineOpen.fromSpec_preimage_zeroLocus {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U)) :
    hU.fromSpec ⁻¹' X.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  ext x
  suffices (∀ f ∈ s, ¬f ∉ x.asIdeal) ↔ s ⊆ x.asIdeal by
    simpa [← hU.fromSpec_image_basicOpen, -not_not] using! this
  simp_rw [not_not]
  rfl
/-
**AlgebraicGeometry.IsAffineOpen.fromSpec_image_zeroLocus** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsA
ffineOpen U)   (s : Set ↑(X.presheaf.obj (Opposite.op U))), ⇑hU.fromSpec '' Prim
eSpectrum.zeroLocus s = X.zeroLocus s ∩ ↑U
参数：hU : AlgebraicGeometry.IsAffineOpen U；s : Set ↑(X.presheaf.obj (Opposite.op U
))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_zeroLocus`：∀ {X : Algeb
raicGeometry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)   (s 
: Set ↑(X.presheaf.obj (Opposite.op U))), ⇑hU.fr…
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `AlgebraicGeometry.IsAffineOpen.range_fromSpec`：range_fromSpec : Set.rang
e hU.fromSpec = U
-/
lemma IsAffineOpen.fromSpec_image_zeroLocus {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U)) :
    hU.fromSpec '' PrimeSpectrum.zeroLocus s = X.zeroLocus s ∩ U := by
  rw [← hU.fromSpec_preimage_zeroLocus, Set.image_preimage_eq_inter_range, range_fromSpec]

set_option backward.isDefEq.respectTransparency false in
open Set.Notation in
/-
**AlgebraicGeometry.Scheme.zeroLocus_inf** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) {U : X.Opens} (I J : Ideal ↑(X.presheaf.o
bj (Opposite.op U))),   X.zeroLocus ↑(I ⊓ J) = X.zeroLocus ↑I ∪ X.zeroLocus ↑J
参数：X : AlgebraicGeometry.Scheme；I J : Ideal ↑(X.presheaf.obj (Opposite.op U))；I 
⊓ J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Opens.toSpecΓ_preimage_zeroLocus`：∀ {X : Algebr
aicGeometry.Scheme} (U : X.Opens) (s : Set ↑(X.presheaf.obj (Opposite.op U))),  
 ⇑U.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus s = Sub…
· 使用定理 `PrimeSpectrum.zeroLocus_inf`：zeroLocus_inf (I J : Ideal R) : zeroLocus (
(I ⊓ J : Ideal R) : Set R) = zeroLocus I union zeroLocus J
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `codisjoint_iff_compl_le_left`：codisjoint_iff_compl_le_left : Codisjoint 
x y ↔ yᶜ <= x
· 使用引理 `AlgebraicGeometry.Scheme.codisjoint_zeroLocus`：codisjoint_zeroLocus {U :
 X.Opens} (s : Set Γ(X, U)) : Codisjoint (X.zeroLocus s) U
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Scheme.zeroLocus_inf (X : Scheme.{u}) {U : X.Opens} (I J : Ideal Γ(X, U)) :
    X.zeroLocus (U := U) ↑(I ⊓ J) = X.zeroLocus (U := U) I ∪ X.zeroLocus (U := U) J := by
  suffices U.1 ↓∩ (X.zeroLocus (U := U) ↑(I ⊓ J)) =
      U.1 ↓∩ (X.zeroLocus (U := U) I ∪ X.zeroLocus (U := U) J) by
    ext x
    by_cases hxU : x ∈ U
    · simpa [hxU] using congr(⟨x, hxU⟩ ∈ $this)
    · simp only [Submodule.coe_inf, Set.mem_union,
        codisjoint_iff_compl_le_left.mp (X.codisjoint_zeroLocus (U := U) (I ∩ J)) hxU,
        codisjoint_iff_compl_le_left.mp (X.codisjoint_zeroLocus (U := U) I) hxU, true_or]
  simp only [← U.toSpecΓ_preimage_zeroLocus, PrimeSpectrum.zeroLocus_inf I J,
    Set.preimage_union]
/-
**AlgebraicGeometry.Scheme.zeroLocus_biInf** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens} {ι : Type u_1} (I : ι → Ide
al ↑(X.presheaf.obj (Opposite.op U)))   {t : Set ι}, t.Finite → X.zeroLocus ↑(⨅ 
i ∈ t, I i) = (⋃ i ∈ t, X.zeroLocus ↑(I i)) ∪ (↑U)ᶜ
参数：I : ι → Ideal ↑(X.presheaf.obj (Opposite.op U))；⨅ i ∈ t, I i；⋃ i ∈ t, X.zeroL
ocus ↑(I i)；↑U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iInf_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α], ⨅ 
x, ⊤ = ⊤
· 使用引理 `AlgebraicGeometry.Scheme.zeroLocus_univ`：zeroLocus_univ {U : X.Opens} : 
X.zeroLocus (U
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
· 使用定理 `Set.union_assoc`：union_assoc (a b c : Set α) : a union b union c = a uni
on (b union c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Submodule.coe_iInf`：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i)
 : Set M) = ⋂ i, ↑(p i)
· 使用定理 `Set.iInter_iInter_eq_or_left`：iInter_iInter_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋂ (x) (h), s x h = s b (Or.inl
 rfl) inter ⋂ (x) …
-/
lemma Scheme.zeroLocus_biInf
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι → Ideal Γ(X, U)) {t : Set ι} (ht : t.Finite) :
    X.zeroLocus (U := U) ↑(⨅ i ∈ t, I i) = (⋃ i ∈ t, X.zeroLocus (U := U) (I i)) ∪ (↑U)ᶜ := by
  refine ht.induction_on _ (by simp) fun {i t} hit ht IH ↦ ?_
  simp only [Set.mem_insert_iff, Set.iUnion_iUnion_eq_or_left, ← IH, ← zeroLocus_inf,
    Submodule.coe_inf, Set.union_assoc]
  congr!
  simp
/-
**AlgebraicGeometry.Scheme.zeroLocus_biInf_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens} {ι : Type u_1} (I : ι → Ide
al ↑(X.presheaf.obj (Opposite.op U)))   {t : Set ι}, t.Finite → t.Nonempty → X.z
eroLocus ↑(⨅ i ∈ t, I i) = ⋃ i ∈ t, X.zeroLocus ↑(I i)
参数：I : ι → Ideal ↑(X.presheaf.obj (Opposite.op U))；⨅ i ∈ t, I i；I i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.zeroLocus_biInf`：∀ {X : AlgebraicGeometry.Schem
e} {U : X.Opens} {ι : Type u_1} (I : ι → Ideal ↑(X.presheaf.obj (Opposite.op U))
)   {t : Set ι}, t.Finite → X.…
· 使用定理 `Set.union_eq_left`：union_eq_left {s t : Set α} : s union t = s ↔ t subse
teq s
· 使用定理 `Set.mem_iUnion₂_of_mem`：mem_iUnion₂_of_mem {s : forall i, κ i -> Set α} 
{a : α} {i : ι} (j : κ i) (ha : a in s i j) : a in ⋃ (i) (j), s i j
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `codisjoint_iff_compl_le_left`：codisjoint_iff_compl_le_left : Codisjoint 
x y ↔ yᶜ <= x
· 使用引理 `AlgebraicGeometry.Scheme.codisjoint_zeroLocus`：codisjoint_zeroLocus {U :
 X.Opens} (s : Set Γ(X, U)) : Codisjoint (X.zeroLocus s) U
-/
lemma Scheme.zeroLocus_biInf_of_nonempty
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι → Ideal Γ(X, U)) {t : Set ι} (ht : t.Finite) (ht' : t.Nonempty) :
    X.zeroLocus (U := U) ↑(⨅ i ∈ t, I i) = ⋃ i ∈ t, X.zeroLocus (U := U) (I i) := by
  rw [zeroLocus_biInf I ht, Set.union_eq_left]
  obtain ⟨i, hi⟩ := ht'
  exact fun x hx ↦ Set.mem_iUnion₂_of_mem hi
    (codisjoint_iff_compl_le_left.mp (X.codisjoint_zeroLocus (U := U) (I i)) hx)
/-
**AlgebraicGeometry.Scheme.zeroLocus_iInf** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens} {ι : Type u_1} (I : ι → Ide
al ↑(X.presheaf.obj (Opposite.op U)))   [Finite ι], X.zeroLocus ↑(⨅ i, I i) = (⋃
 i, X.zeroLocus ↑(I i)) ∪ (↑U)ᶜ
参数：I : ι → Ideal ↑(X.presheaf.obj (Opposite.op U))；⨅ i, I i；⋃ i, X.zeroLocus ↑(I
 i)；↑U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.coe_iInf`：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i)
 : Set M) = ⋂ i, ↑(p i)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `AlgebraicGeometry.Scheme.zeroLocus_biInf`：∀ {X : AlgebraicGeometry.Schem
e} {U : X.Opens} {ι : Type u_1} (I : ι → Ideal ↑(X.presheaf.obj (Opposite.op U))
)   {t : Set ι}, t.Finite → X.…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
lemma Scheme.zeroLocus_iInf
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι → Ideal Γ(X, U)) [Finite ι] :
    X.zeroLocus (U := U) ↑(⨅ i, I i) = (⋃ i, X.zeroLocus (U := U) (I i)) ∪ (↑U)ᶜ := by
  simpa using zeroLocus_biInf I Set.finite_univ
/-
**AlgebraicGeometry.Scheme.zeroLocus_iInf_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens} {ι : Type u_1} (I : ι → Ide
al ↑(X.presheaf.obj (Opposite.op U)))   [Finite ι] [Nonempty ι], X.zeroLocus ↑(⨅
 i, I i) = ⋃ i, X.zeroLocus ↑(I i)
参数：I : ι → Ideal ↑(X.presheaf.obj (Opposite.op U))；⨅ i, I i；I i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.coe_iInf`：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i)
 : Set M) = ⋂ i, ↑(p i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `AlgebraicGeometry.Scheme.zeroLocus_biInf_of_nonempty`：∀ {X : AlgebraicGe
ometry.Scheme} {U : X.Opens} {ι : Type u_1} (I : ι → Ideal ↑(X.presheaf.obj (Opp
osite.op U)))   {t : Set ι}, t.Finite → t.…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
lemma Scheme.zeroLocus_iInf_of_nonempty
    {X : Scheme.{u}} {U : X.Opens} {ι : Type*}
    (I : ι → Ideal Γ(X, U)) [Finite ι] [Nonempty ι] :
    X.zeroLocus (U := U) ↑(⨅ i, I i) = ⋃ i, X.zeroLocus (U := U) (I i) := by
  simpa using zeroLocus_biInf_of_nonempty I Set.finite_univ

end ZeroLocus

section Factorization

variable {X : Scheme.{u}} {A : CommRingCat}

/-- Given `f : X ⟶ Spec A` and some ideal `I ≤ ker(A ⟶ Γ(X, ⊤))`,
this is the lift to `X ⟶ Spec (A ⧸ I)`. -/
/-
**AlgebraicGeometry.Scheme.Hom.liftQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme.Hom`。
形式化陈述：{X : AlgebraicGeometry.Scheme} →   {A : CommRingCat} →     (f : X.Hom (Alg
ebraicGeometry.Spec A)) →       (I : Ideal ↑A) →         I ≤             RingHom
.ker               (CommRingCat.Hom.hom                 (CategoryTheory.Category
Struct.comp (AlgebraicGeometry.Scheme.ΓSpecIso A).inv f.appTop)) →           (X 
⟶ AlgebraicGeometry.Spec (CommRingCat.of (↑A ⧸ I)))
参数：f : X.Hom (AlgebraicGeometry.Spec A)；I : Ideal ↑A；CommRingCat.Hom.hom        
         (CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Scheme.ΓSpecIso 
A).inv f.appTop)；X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (↑A ⧸ I))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : X ⟶ Spec A` and some ideal `I ≤ ker(A ⟶ Γ(X, ⊤))`,
this is the lift to `X ⟶ Spec (A ⧸ I)`.
-/
def Scheme.Hom.liftQuotient (f : X.Hom (Spec A)) (I : Ideal A)
    (hI : I ≤ RingHom.ker ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom) :
    X ⟶ Spec <| .of (A ⧸ I) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.lift _ ((Scheme.ΓSpecIso _).inv ≫ f.appTop).hom hI))

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.liftQuotient_comp** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Scheme.Hom`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {A : CommRingCat} (f : X.Hom (AlgebraicGe
ometry.Spec A)) (I : Ideal ↑A)   (hI :     I ≤       RingHom.ker         (CommRi
ngCat.Hom.hom (CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Scheme.ΓSpe
cIso A).inv f.appTop))),   CategoryTheory.CategoryStruct.comp (f.liftQuotient I 
hI)       (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
 =     f
参数：f : X.Hom (AlgebraicGeometry.Spec A)；I : Ideal ↑A；hI :     I ≤       RingHom.
ker         (CommRingCat.Hom.hom (CategoryTheory.CategoryStruct.comp (AlgebraicG
eometry.Scheme.ΓSpecIso A).inv f.appTop))；f.liftQuotient I hI；AlgebraicGeometry.
Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.liftQuotient.eq_1`：∀ {X : AlgebraicGeometry
.Scheme} {A : CommRingCat} (f : X.Hom (AlgebraicGeometry.Spec A)) (I : Ideal ↑A)
   (hI :     I ≤       RingHom.ker  …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用引理 `CommRingCat.ofHom_comp`：ofHom_comp {R S T : Type u} [CommRing R] [CommRi
ng S] [CommRing T] (f : R ->+* S) (g : S ->+* T) : ofHom (g.comp f) = ofHom f ≫ 
ofHom g
· 使用引理 `Ideal.Quotient.lift_comp_mk`：lift_comp_mk (f : R ->+* S) (H : forall a :
 R, a in I -> f a = 0) : (lift I f H).comp (mk I) = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.SpecMap_ΓSpecIso_hom`：SpecMap_ΓSpecIso_hom (R : CommRi
ngCat.{u}) : Spec.map ((Scheme.ΓSpecIso R).hom) = (Spec R).toSpecΓ
· 使用定理 `AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv`：toSpecΓ_SpecMap_ΓSpecIso
_inv (R : CommRingCat.{u}) : (Spec R).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso R).inv
 = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Scheme.Hom.liftQuotient_comp (f : X.Hom (Spec A)) (I : Ideal A)
    (hI : I ≤ RingHom.ker ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom) :
    f.liftQuotient I hI ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) = f := by
  rw [Scheme.Hom.liftQuotient, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.lift_comp_mk]
  simp only [CommRingCat.hom_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, ←
    Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom]
  simp

/-- If `X ⟶ Spec A` is a morphism of schemes, then `Spec` of `A ⧸ specTargetImage f`
is the scheme-theoretic image of `f`. For this quotient as an object of `CommRingCat` see
`specTargetImage` below. -/
/-
**AlgebraicGeometry.specTargetImageIdeal** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：specTargetImageIdeal (f : X ⟶ Spec A) : Ideal A
参数：f : X ⟶ Spec A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `X ⟶ Spec A` is a morphism of schemes, then `Spec` of `A ⧸ specTargetImage f`
is the scheme-theoretic image of `f`. For this quotient as an object of `CommRin
gCat` see
`specTargetImage` below.
-/
def specTargetImageIdeal (f : X ⟶ Spec A) : Ideal A :=
  (RingHom.ker <| (((ΓSpec.adjunction).homEquiv X (op A)).symm f).unop.hom)

/-- If `X ⟶ Spec A` is a morphism of schemes, then `Spec` of `specTargetImage f` is the
scheme-theoretic image of `f` and `f` factors as
`specTargetImageFactorization f ≫ Spec.map (specTargetImageRingHom f)`
(see `specTargetImageFactorization_comp`). -/
/-
**AlgebraicGeometry.specTargetImage** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry
`。
形式化陈述：specTargetImage (f : X ⟶ Spec A) : CommRingCat
参数：f : X ⟶ Spec A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X ⟶ Spec A` is a morphism of schemes, then `Spec` of `specTargetImage f` is 
the
scheme-theoretic image of `f` and `f` factors as
`specTargetImageFactorization f ≫ Spec.map (specTargetImageRingHom f)`
(see `specTargetImageFactorization_comp`).
-/
def specTargetImage (f : X ⟶ Spec A) : CommRingCat :=
  CommRingCat.of (A ⧸ specTargetImageIdeal f)

/-- If `f : X ⟶ Spec A` is a morphism of schemes, then `f` factors via
the inclusion of `Spec (specTargetImage f)` into `X`. -/
/-
**AlgebraicGeometry.specTargetImageFactorization** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry`。
形式化陈述：specTargetImageFactorization (f : X ⟶ Spec A) : X ⟶ Spec (specTargetImage 
f)
参数：f : X ⟶ Spec A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Spec A` is a morphism of schemes, then `f` factors via
the inclusion of `Spec (specTargetImage f)` into `X`.
-/
def specTargetImageFactorization (f : X ⟶ Spec A) : X ⟶ Spec (specTargetImage f) :=
  f.liftQuotient _ le_rfl

/-- If `f : X ⟶ Spec A` is a morphism of schemes, the induced morphism on spectra of
`specTargetImageRingHom f` is the inclusion of the scheme-theoretic image of `f` into `Spec A`. -/
/-
**AlgebraicGeometry.specTargetImageRingHom** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry`。
形式化陈述：specTargetImageRingHom (f : X ⟶ Spec A) : A ⟶ specTargetImage f
参数：f : X ⟶ Spec A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Spec A` is a morphism of schemes, the induced morphism on spectra of
`specTargetImageRingHom f` is the inclusion of the scheme-theoretic image of `f`
 into `Spec A`.
-/
def specTargetImageRingHom (f : X ⟶ Spec A) : A ⟶ specTargetImage f :=
  CommRingCat.ofHom (Ideal.Quotient.mk (specTargetImageIdeal f))

variable (f : X ⟶ Spec A)
/-
**AlgebraicGeometry.specTargetImageRingHom_surjective** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry`。
形式化陈述：specTargetImageRingHom_surjective : Function.Surjective (specTargetImageRi
ngHom f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
-/
lemma specTargetImageRingHom_surjective : Function.Surjective (specTargetImageRingHom f) :=
  Ideal.Quotient.mk_surjective

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.specTargetImageFactorization_app_injective** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：specTargetImageFactorization_app_injective : Function.Injective (specTarge
tImageFactorization f).appTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.ΓSpec_adjunction_homEquiv_eq`：ΓSpec_adjunction_homEqui
v_eq {X : Scheme.{u}} {B : CommRingCat} (φ : B ⟶ Γ(X, ⊤)) : ((ΓSpec.adjunction.h
omEquiv X (op B)) φ.op).appTop = (Sc…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
· 使用定理 `RingHom.kerLift_injective`：kerLift_injective : Function.Injective (kerLi
ft f)
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ConcreteCategory.isIso_iff_bijective`：isIso_iff_bijective
 [(forget C).ReflectsIsomorphisms] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Function.Bi
jective f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma specTargetImageFactorization_app_injective :
    Function.Injective <| (specTargetImageFactorization f).appTop := by
  let φ : A ⟶ Γ(X, ⊤) := (((ΓSpec.adjunction).homEquiv X (op A)).symm f).unop
  let φ' : specTargetImage f ⟶ Scheme.Γ.obj (op X) := CommRingCat.ofHom (RingHom.kerLift φ.hom)
  change Function.Injective <| ((ΓSpec.adjunction.homEquiv X _) φ'.op).appTop
  rw [ΓSpec_adjunction_homEquiv_eq]
  apply (RingHom.kerLift_injective φ.hom).comp
  exact ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso _).hom).mp inferInstance).injective

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.specTargetImageFactorization_comp** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry`。
形式化陈述：specTargetImageFactorization_comp : specTargetImageFactorization f ≫ Spec.
map (specTargetImageRingHom f) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.liftQuotient_comp`：∀ {X : AlgebraicGeometry
.Scheme} {A : CommRingCat} (f : X.Hom (AlgebraicGeometry.Spec A)) (I : Ideal ↑A)
   (hI :     I ≤       RingHom.ker  …
-/
lemma specTargetImageFactorization_comp :
    specTargetImageFactorization f ≫ Spec.map (specTargetImageRingHom f) = f :=
  f.liftQuotient_comp _ _

end Factorization

section Stalks

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) (x : PrimeSpectrum R)

set_option backward.isDefEq.respectTransparency.types false in
variable (R) (x : PrimeSpectrum R) in
/-- The stalk of `Spec R` at `x` is isomorphic to `Rₚ`,
where `p` is the prime corresponding to `x`. -/
noncomputable
/-
**AlgebraicGeometry.Spec.stalkIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.S
pec`。
形式化陈述：(R : CommRingCat) →   (x : PrimeSpectrum ↑R) → (AlgebraicGeometry.Spec R).
presheaf.stalk x ≅ CommRingCat.of (Localization.AtPrime x.asIdeal)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Spec.stalkIso : (Spec R).presheaf.stalk x ≅ .of (Localization.AtPrime x.asIdeal) :=
  (StructureSheaf.stalkIso ..).toCommRingCatIso.symm

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Spec.algebraMap_stalkIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Spec`。
形式化陈述：∀ {R : CommRingCat} (x : PrimeSpectrum ↑R),   CategoryTheory.CategoryStruc
t.comp (CommRingCat.ofHom (algebraMap (↑R) (Localization.AtPrime x.asIdeal)))   
    (AlgebraicGeometry.Spec.stalkIso R x).inv =     CategoryTheory.CategoryStruc
t.comp (AlgebraicGeometry.Scheme.ΓSpecIso R).inv       ((AlgebraicGeometry.Spec 
R).presheaf.germ ⊤ x trivial)
参数：x : PrimeSpectrum ↑R；CommRingCat.ofHom (algebraMap (↑R) (Localization.AtPrime
 x.asIdeal))；AlgebraicGeometry.Spec.stalkIso R x；AlgebraicGeometry.Scheme.ΓSpecI
so R；(AlgebraicGeometry.Spec R).presheaf.germ ⊤ x trivial。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `trivial`：True
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`：∀ (R : Type u)
 [inst : CommRing R] (p : PrimeSpectrum R),   IsLocalization.AtPrime (↑((Algebra
icGeometry.Spec.structureSheaf R).presheaf.sta…
-/
lemma Spec.algebraMap_stalkIso_inv :
    CommRingCat.ofHom (algebraMap R _) ≫ (stalkIso R x).inv =
      (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial := by
  ext s : 2
  exact (IsLocalization.algEquiv _ ((structureSheaf R).presheaf.stalk _) _).symm.commutes s

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Spec.germ_stalkMapIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Spec`。
形式化陈述：∀ {R : CommRingCat} (x : PrimeSpectrum ↑R),   CategoryTheory.CategoryStruc
t.comp ((AlgebraicGeometry.Spec R).presheaf.germ ⊤ x trivial)       (AlgebraicGe
ometry.Spec.stalkIso R x).hom =     CategoryTheory.CategoryStruct.comp (Algebrai
cGeometry.Scheme.ΓSpecIso R).hom       (CommRingCat.ofHom (algebraMap (↑R) (Loca
lization.AtPrime x.asIdeal)))
参数：x : PrimeSpectrum ↑R；(AlgebraicGeometry.Spec R).presheaf.germ ⊤ x trivial；Alg
ebraicGeometry.Spec.stalkIso R x；AlgebraicGeometry.Scheme.ΓSpecIso R；CommRingCat
.ofHom (algebraMap (↑R) (Localization.AtPrime x.asIdeal))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `trivial`：True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Spec.germ_stalkMapIso_hom :
    (Spec R).presheaf.germ ⊤ _ trivial ≫ (stalkIso R x).hom =
      (Scheme.ΓSpecIso R).hom ≫ CommRingCat.ofHom (algebraMap R _) := by
  simp [← Iso.inv_comp_eq, ← Spec.algebraMap_stalkIso_inv_assoc]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Variant of `AlgebraicGeometry.localRingHom_comp_stalkIso` for `Spec.map`. -/
@[elementwise]
/-
**AlgebraicGeometry.Scheme.localRingHom_comp_stalkIso** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme`。
形式化陈述：∀ {R S : CommRingCat} (f : R ⟶ S) (p : PrimeSpectrum ↑S),   CategoryTheory
.CategoryStruct.comp       (AlgebraicGeometry.Spec.stalkIso R (PrimeSpectrum.com
ap (CommRingCat.Hom.hom f) p)).hom       (CategoryTheory.CategoryStruct.comp    
     (CommRingCat.ofHom           (Localization.localRingHom (PrimeSpectrum.coma
p (CommRingCat.Hom.hom f) p).asIdeal p.asIdeal             (CommRingCat.Hom.hom 
f) ⋯))         (AlgebraicGeometry.Spec.stalkIso S p).inv) =     AlgebraicGeometr
y.Scheme.Hom.stalkMap (AlgebraicGeometry.Spec.map f) p
参数：f : R ⟶ S；p : PrimeSpectrum ↑S；AlgebraicGeometry.Spec.stalkIso R (PrimeSpectr
um.comap (CommRingCat.Hom.hom f) p)；CategoryTheory.CategoryStruct.comp         (
CommRingCat.ofHom           (Localization.localRingHom (PrimeSpectrum.comap (Com
mRingCat.Hom.hom f) p).asIdeal p.asIdeal             (CommRingCat.Hom.hom f) ⋯))
         (AlgebraicGeometry.Spec.stalkIso S p).inv；AlgebraicGeometry.Spec.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.localRingHom_comp_stalkIso`：localRingHom_comp_stalkIso
 {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) : CommRingCat.ofHom (
stalkIso R (PrimeSpectrum.comap f.…

--- 原说明 ---
Variant of `AlgebraicGeometry.localRingHom_comp_stalkIso` for `Spec.map`.
-/
lemma Scheme.localRingHom_comp_stalkIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    (Spec.stalkIso R (p.comap f.hom)).hom ≫
      (CommRingCat.ofHom <| Localization.localRingHom
        (PrimeSpectrum.comap f.hom p).asIdeal p.asIdeal f.hom rfl) ≫
      (Spec.stalkIso S p).inv = (Spec.map f).stalkMap p :=
  AlgebraicGeometry.localRingHom_comp_stalkIso f p

set_option backward.isDefEq.respectTransparency false in
/-- Given a morphism of rings `f : R ⟶ S`, the stalk map of `Spec S ⟶ Spec R` at
a prime of `S` is isomorphic to the localized ring homomorphism. -/
/-
**AlgebraicGeometry.Scheme.arrowStalkMapSpecIso** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：{R S : CommRingCat} →   (f : R ⟶ S) →     (p : PrimeSpectrum ↑S) →       C
ategoryTheory.Arrow.mk (AlgebraicGeometry.Scheme.Hom.stalkMap (AlgebraicGeometry
.Spec.map f) p) ≅         CategoryTheory.Arrow.mk           (CommRingCat.ofHom  
           (Localization.localRingHom (PrimeSpectrum.comap (CommRingCat.Hom.hom 
f) p).asIdeal p.asIdeal               (CommRingCat.Hom.hom f) ⋯))
参数：f : R ⟶ S；p : PrimeSpectrum ↑S；AlgebraicGeometry.Scheme.Hom.stalkMap (Algebra
icGeometry.Spec.map f) p；CommRingCat.ofHom             (Localization.localRingHo
m (PrimeSpectrum.comap (CommRingCat.Hom.hom f) p).asIdeal p.asIdeal             
  (CommRingCat.Hom.hom f) ⋯)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism of rings `f : R ⟶ S`, the stalk map of `Spec S ⟶ Spec R` at
a prime of `S` is isomorphic to the localized ring homomorphism.
-/
def Scheme.arrowStalkMapSpecIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    Arrow.mk ((Spec.map f).stalkMap p) ≅ Arrow.mk (CommRingCat.ofHom <| Localization.localRingHom
      (p.comap f.hom).asIdeal p.asIdeal f.hom rfl) := Arrow.isoMk
  (Spec.stalkIso R (p.comap f.hom))
  (Spec.stalkIso S p) <| by
    rw [← Scheme.localRingHom_comp_stalkIso]
    simp

end Stalks
end AlgebraicGeometry

