/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Justus Springer
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# $Spec$ as a functor to locally ringed spaces.

We define the functor $Spec$ from commutative rings to locally ringed spaces.

## Implementation notes

We define $Spec$ in three consecutive steps, each with more structure than the last:

1. `Spec.toTop`, valued in the category of topological spaces,
2. `Spec.toSheafedSpace`, valued in the category of sheafed spaces and
3. `Spec.toLocallyRingedSpace`, valued in the category of locally ringed spaces.

Additionally, we provide `Spec.toPresheafedSpace` as a composition of `Spec.toSheafedSpace` with
a forgetful functor.

## Related results

The adjunction `Γ ⊣ Spec` is constructed in `Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean`.

-/

@[expose] public section


-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

noncomputable section

universe u v

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

open Spec (structureSheaf)

/-- The spectrum of a commutative ring, as a topological space.
-/
/-
**AlgebraicGeometry.Spec.topObj** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Spe
c`。
形式化陈述：CommRingCat → TopCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The spectrum of a commutative ring, as a topological space.
-/
def Spec.topObj (R : CommRingCat.{u}) : TopCat :=
  TopCat.of (PrimeSpectrum R)
/-
**AlgebraicGeometry.Spec.topObj_forget** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Spec`。
形式化陈述：∀ {R : CommRingCat}, CategoryTheory.ToType (AlgebraicGeometry.Spec.topObj 
R) = PrimeSpectrum ↑R
参数：AlgebraicGeometry.Spec.topObj R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem Spec.topObj_forget {R} : ToType (Spec.topObj R) = PrimeSpectrum R :=
  rfl

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of topological spaces.
-/
/-
**AlgebraicGeometry.Spec.topMap** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Spe
c`。
形式化陈述：{R S : CommRingCat} → (R ⟶ S) → (AlgebraicGeometry.Spec.topObj S ⟶ Algebra
icGeometry.Spec.topObj R)
参数：R ⟶ S；AlgebraicGeometry.Spec.topObj S ⟶ AlgebraicGeometry.Spec.topObj R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map of a ring homomorphism on the ring spectra, as a morphism of top
ological spaces.
-/
def Spec.topMap {R S : CommRingCat.{u}} (f : R ⟶ S) : Spec.topObj S ⟶ Spec.topObj R :=
  TopCat.ofHom ⟨_, PrimeSpectrum.continuous_comap f.hom⟩

@[simp]
/-
**AlgebraicGeometry.Spec.topMap_id** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.
Spec`。
形式化陈述：∀ (R : CommRingCat),   AlgebraicGeometry.Spec.topMap (CategoryTheory.Categ
oryStruct.id R) =     CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec.t
opObj R)
参数：R : CommRingCat；CategoryTheory.CategoryStruct.id R；AlgebraicGeometry.Spec.top
Obj R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Spec.topMap_id (R : CommRingCat.{u}) : Spec.topMap (𝟙 R) = 𝟙 (Spec.topObj R) :=
  rfl

@[simp]
/-
**AlgebraicGeometry.Spec.topMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometr
y.Spec`。
形式化陈述：∀ {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T),   AlgebraicGeometry.Spec.
topMap (CategoryTheory.CategoryStruct.comp f g) =     CategoryTheory.CategoryStr
uct.comp (AlgebraicGeometry.Spec.topMap g) (AlgebraicGeometry.Spec.topMap f)
参数：f : R ⟶ S；g : S ⟶ T；CategoryTheory.CategoryStruct.comp f g；AlgebraicGeometry.
Spec.topMap g；AlgebraicGeometry.Spec.topMap f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Spec.topMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.topMap (f ≫ g) = Spec.topMap g ≫ Spec.topMap f :=
  rfl

-- Porting note: `simps!` generate some garbage lemmas, so choose manually,
-- if more is needed, add them here
/-- The spectrum, as a contravariant functor from commutative rings to topological spaces.
-/
@[simps!]
/-
**AlgebraicGeometry.Spec.toTop** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Spec
`。
形式化陈述：CategoryTheory.Functor CommRingCatᵒᵖ TopCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The spectrum, as a contravariant functor from commutative rings to topological s
paces.
-/
def Spec.toTop : CommRingCat.{u}ᵒᵖ ⥤ TopCat where
  obj R := Spec.topObj (unop R)
  map {_ _} f := Spec.topMap f.unop

/-- The spectrum of a commutative ring, as a `SheafedSpace`.
-/
@[simps]
/-
**AlgebraicGeometry.Spec.sheafedSpaceObj** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Spec`。
形式化陈述：CommRingCat → AlgebraicGeometry.SheafedSpace CommRingCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The spectrum of a commutative ring, as a `SheafedSpace`.
-/
def Spec.sheafedSpaceObj (R : CommRingCat.{u}) : SheafedSpace CommRingCat where
  carrier := Spec.topObj R
  presheaf := (structureSheaf R).1
  IsSheaf := (structureSheaf R).2

set_option backward.isDefEq.respectTransparency.types false in
/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of sheafed spaces.
-/
@[simps hom_base hom_c_app]
/-
**AlgebraicGeometry.Spec.sheafedSpaceMap** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Spec`。
形式化陈述：{R S : CommRingCat} → (R ⟶ S) → (AlgebraicGeometry.Spec.sheafedSpaceObj S 
⟶ AlgebraicGeometry.Spec.sheafedSpaceObj R)
参数：R ⟶ S；AlgebraicGeometry.Spec.sheafedSpaceObj S ⟶ AlgebraicGeometry.Spec.sheaf
edSpaceObj R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map of a ring homomorphism on the ring spectra, as a morphism of she
afed spaces.
-/
def Spec.sheafedSpaceMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Spec.sheafedSpaceObj S ⟶ Spec.sheafedSpaceObj R where
  hom.base := Spec.topMap f
  hom.c :=
    { app := fun U => CommRingCat.ofHom <|
        comap f.hom (unop U) ((TopologicalSpace.Opens.map (Spec.topMap f)).obj (unop U)) fun _ => id
      naturality := fun {_ _} _ => by ext; rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Spec.sheafedSpaceMap_id** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry.Spec`。
形式化陈述：∀ {R : CommRingCat},   AlgebraicGeometry.Spec.sheafedSpaceMap (CategoryThe
ory.CategoryStruct.id R) =     CategoryTheory.CategoryStruct.id (AlgebraicGeomet
ry.Spec.sheafedSpaceObj R)
参数：CategoryTheory.CategoryStruct.id R；AlgebraicGeometry.Spec.sheafedSpaceObj R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.SheafedSpace.ext`：ext {X Y : SheafedSpace C} (α β : X 
⟶ Y) (w : α.hom.base = β.hom.base) (h : α.hom.c ≫ whiskerRight (eqToHom (by rw [
w])) _ = β.hom.c) : α = …
· 使用定理 `AlgebraicGeometry.Spec.topMap_id`：∀ (R : CommRingCat),   AlgebraicGeomet
ry.Spec.topMap (CategoryTheory.CategoryStruct.id R) =     CategoryTheory.Categor
yStruct.id (AlgebraicG…
· 使用引理 `TopCat.Presheaf.ext`：ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P 
⟶ Q} (w : forall U : Opens X, f.app (op U) = g.app (op U)) : f = g
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.map_id_obj`：map_id_obj (U : Opens X) : (map (𝟙 X)
).obj U = U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.StructureSheaf.comap_id`：comap_id {U V : Opens (PrimeS
pectrum.Top R)} (hUV : U = V) : (comap (RingHom.id R) U V fun p hpV => by rwa [h
UV, PrimeSpectrum.comap_id]) = …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `AlgebraicGeometry.PresheafedSpace.id_c_app`：id_c_app (X : PresheafedSpac
e C) (U) : (𝟙 X : X ⟶ X).c.app U = X.presheaf.map (𝟙 U)
-/
theorem Spec.sheafedSpaceMap_id {R : CommRingCat.{u}} :
    Spec.sheafedSpaceMap (𝟙 R) = 𝟙 (Spec.sheafedSpaceObj R) := by
  ext : 1
  · exact Spec.topMap_id R
  · ext
    dsimp
    rw [comap_id (by simp)]
    simp
    rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Spec.sheafedSpaceMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Spec`。
形式化陈述：∀ {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T),   AlgebraicGeometry.Spec.
sheafedSpaceMap (CategoryTheory.CategoryStruct.comp f g) =     CategoryTheory.Ca
tegoryStruct.comp (AlgebraicGeometry.Spec.sheafedSpaceMap g)       (AlgebraicGeo
metry.Spec.sheafedSpaceMap f)
参数：f : R ⟶ S；g : S ⟶ T；CategoryTheory.CategoryStruct.comp f g；AlgebraicGeometry.
Spec.sheafedSpaceMap g；AlgebraicGeometry.Spec.sheafedSpaceMap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.SheafedSpace.ext`：ext {X Y : SheafedSpace C} (α β : X 
⟶ Y) (w : α.hom.base = β.hom.base) (h : α.hom.c ≫ whiskerRight (eqToHom (by rw [
w])) _ = β.hom.c) : α = …
· 使用定理 `AlgebraicGeometry.Spec.topMap_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) 
(g : S ⟶ T),   AlgebraicGeometry.Spec.topMap (CategoryTheory.CategoryStruct.comp
 f g) =     CategoryTheo…
· 使用引理 `TopCat.Presheaf.ext`：ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P 
⟶ Q} (w : forall U : Opens X, f.app (op U) = g.app (op U)) : f = g
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
· 使用定理 `AlgebraicGeometry.Spec.sheafedSpaceMap_hom_c_app`：∀ {R S : CommRingCat} 
(f : R ⟶ S)   (U : (TopologicalSpace.Opens ↑↑(AlgebraicGeometry.Spec.sheafedSpac
eObj R).toPresheafedSpace)ᵒᵖ),   (Alge…
· 使用定理 `CategoryTheory.Functor.whiskerRight_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `AlgebraicGeometry.StructureSheaf.comap_comp`：comap_comp (f : R ->+* S) (
g : S ->+* P) (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S)
) (W : Opens (PrimeSpectrum.Top P…
-/
theorem Spec.sheafedSpaceMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.sheafedSpaceMap (f ≫ g) = Spec.sheafedSpaceMap g ≫ Spec.sheafedSpaceMap f := by
  ext : 1
  · exact Spec.topMap_comp f g
  · ext
    -- Porting note: was one liner
    -- `dsimp, rw category_theory.functor.map_id, rw category.comp_id, erw comap_comp f g, refl`
    rw [NatTrans.comp_app, sheafedSpaceMap_hom_c_app, Functor.whiskerRight_app, eqToHom_refl]
    erw [(sheafedSpaceObj T).presheaf.map_id]
    dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [comap_comp]
    rfl

/-- Spec, as a contravariant functor from commutative rings to sheafed spaces.
-/
@[simps]
/-
**AlgebraicGeometry.Spec.toSheafedSpace** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.Spec`。
形式化陈述：CategoryTheory.Functor CommRingCatᵒᵖ (AlgebraicGeometry.SheafedSpace CommR
ingCat)
参数：AlgebraicGeometry.SheafedSpace CommRingCat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Spec, as a contravariant functor from commutative rings to sheafed spaces.
-/
def Spec.toSheafedSpace : CommRingCat.{u}ᵒᵖ ⥤ SheafedSpace CommRingCat where
  obj R := Spec.sheafedSpaceObj (unop R)
  map f := Spec.sheafedSpaceMap f.unop
  map_comp f g := by simp [Spec.sheafedSpaceMap_comp]

/-- Spec, as a contravariant functor from commutative rings to presheafed spaces.
-/
/-
**AlgebraicGeometry.Spec.toPresheafedSpace** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Spec`。
形式化陈述：CategoryTheory.Functor CommRingCatᵒᵖ (AlgebraicGeometry.PresheafedSpace Co
mmRingCat)
参数：AlgebraicGeometry.PresheafedSpace CommRingCat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Spec, as a contravariant functor from commutative rings to presheafed spaces.
-/
def Spec.toPresheafedSpace : CommRingCat.{u}ᵒᵖ ⥤ PresheafedSpace CommRingCat :=
  Spec.toSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace

@[simp]
/-
**AlgebraicGeometry.Spec.toPresheafedSpace_obj** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Spec`。
形式化陈述：∀ (R : CommRingCatᵒᵖ),   AlgebraicGeometry.Spec.toPresheafedSpace.obj R = 
    (AlgebraicGeometry.Spec.sheafedSpaceObj (Opposite.unop R)).toPresheafedSpace
参数：R : CommRingCatᵒᵖ；AlgebraicGeometry.Spec.sheafedSpaceObj (Opposite.unop R)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Spec.toPresheafedSpace_obj (R : CommRingCat.{u}ᵒᵖ) :
    Spec.toPresheafedSpace.obj R = (Spec.sheafedSpaceObj (unop R)).toPresheafedSpace :=
  rfl
/-
**AlgebraicGeometry.Spec.toPresheafedSpace_obj_op** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Spec`。
形式化陈述：∀ (R : CommRingCat),   AlgebraicGeometry.Spec.toPresheafedSpace.obj (Oppos
ite.op R) =     (AlgebraicGeometry.Spec.sheafedSpaceObj R).toPresheafedSpace
参数：R : CommRingCat；Opposite.op R；AlgebraicGeometry.Spec.sheafedSpaceObj R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Spec.toPresheafedSpace_obj_op (R : CommRingCat.{u}) :
    Spec.toPresheafedSpace.obj (op R) = (Spec.sheafedSpaceObj R).toPresheafedSpace :=
  rfl

@[simp]
/-
**AlgebraicGeometry.Spec.toPresheafedSpace_map** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Spec`。
形式化陈述：∀ (R S : CommRingCatᵒᵖ) (f : R ⟶ S),   AlgebraicGeometry.Spec.toPresheafed
Space.map f = (AlgebraicGeometry.Spec.sheafedSpaceMap f.unop).hom
参数：R S : CommRingCatᵒᵖ；f : R ⟶ S；AlgebraicGeometry.Spec.sheafedSpaceMap f.unop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Spec.toPresheafedSpace_map (R S : CommRingCat.{u}ᵒᵖ) (f : R ⟶ S) :
    Spec.toPresheafedSpace.map f = (Spec.sheafedSpaceMap f.unop).hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Spec.toPresheafedSpace_map_op** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Spec`。
形式化陈述：∀ (R S : CommRingCat) (f : R ⟶ S),   AlgebraicGeometry.Spec.toPresheafedSp
ace.map f.op = (AlgebraicGeometry.Spec.sheafedSpaceMap f).hom
参数：R S : CommRingCat；f : R ⟶ S；AlgebraicGeometry.Spec.sheafedSpaceMap f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Spec.toPresheafedSpace_map_op (R S : CommRingCat.{u}) (f : R ⟶ S) :
    Spec.toPresheafedSpace.map f.op = (Spec.sheafedSpaceMap f).hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Spec.basicOpen_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Spec`。
形式化陈述：∀ {X : AlgebraicGeometry.RingedSpace} {R : CommRingCat} {α β : X ⟶ Algebra
icGeometry.Spec.sheafedSpaceObj R}   (w : α.hom.base = β.hom.base),   (∀ (r : ↑R
),       let U := PrimeSpectrum.basicOpen r;       CategoryTheory.CategoryStruct
.comp           (CategoryTheory.CategoryStruct.comp             (CommRingCat.ofH
om               (algebraMap (↑R) ((AlgebraicGeometry.structureSheafInType ↑R ↑R
).obj.obj (Opposite.op U))))             (α.hom.c.app (Opposite.op U)))         
  (X.presheaf.map (CategoryTheory.eqToHom ⋯)) =         CategoryTheory.CategoryS
truct.comp           (CommRingCat.ofHom (algebraMap (↑R) ((AlgebraicGeometry.str
uctureSheafInType ↑R ↑R).obj.obj (Opposite.op U))))           (β.hom.c.app (Oppo
site.op U))) →     α = β
参数：w : α.hom.base = β.hom.base；∀ (r : ↑R),       let U := PrimeSpectrum.basicOpe
n r;       CategoryTheory.CategoryStruct.comp           (CategoryTheory.Category
Struct.comp             (CommRingCat.ofHom               (algebraMap (↑R) ((Alge
braicGeometry.structureSheafInType ↑R ↑R).obj.obj (Opposite.op U))))            
 (α.hom.c.app (Opposite.op U)))           (X.presheaf.map (CategoryTheory.eqToHo
m ⋯)) =         CategoryTheory.CategoryStruct.comp           (CommRingCat.ofHom 
(algebraMap (↑R) ((AlgebraicGeometry.structureSheafInType ↑R ↑R).obj.obj (Opposi
te.op U))))           (β.hom.c.app (Opposite.op U))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.SheafedSpace.ext`：ext {X Y : SheafedSpace C} (α β : X 
⟶ Y) (w : α.hom.base = β.hom.base) (h : α.hom.c ≫ whiskerRight (eqToHom (by rw [
w])) _ = β.hom.c) : α = …
· 使用定理 `TopCat.Sheaf.hom_ext`：hom_ext (h : Opens.IsBasis (Set.range B)) {α β : F
 ⟶ F'.1} (he : forall i, α.app (op (B i)) = β.app (op (B i))) : α = β
· 使用定理 `PrimeSpectrum.isBasis_basic_opens`：isBasis_basic_opens : TopologicalSpac
e.Opens.IsBasis (Set.range (@basicOpen R _))
· 使用定理 `CategoryTheory.Epi.left_cancellation`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.Epi f] {Z : 
C}   (g h : Y ⟶ Z), Catego…
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_app`：eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C
) : (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
theorem Spec.basicOpen_hom_ext {X : RingedSpace.{u}} {R : CommRingCat.{u}}
    {α β : X ⟶ Spec.sheafedSpaceObj R} (w : α.hom.base = β.hom.base)
    (h : ∀ r : R,
      let U := PrimeSpectrum.basicOpen r
      ((CommRingCat.ofHom (algebraMap R _)) ≫ α.hom.c.app (op U)) ≫
        X.presheaf.map (eqToHom (by rw [w])) =
        CommRingCat.ofHom (algebraMap _ _) ≫ β.hom.c.app (op U)) :
    α = β := by
  ext : 1
  · exact w
  · apply ((TopCat.Sheaf.pushforward _ β.hom.base).obj X.sheaf).hom_ext _
      PrimeSpectrum.isBasis_basic_opens
    intro r
    apply (StructureSheaf.to_basicOpen_epi R r).1
    simpa using! h r

set_option backward.isDefEq.respectTransparency.types false in
-- `simps!` generates some garbage lemmas, so choose manually,
-- if more is needed, add them here
/-- The spectrum of a commutative ring, as a `LocallyRingedSpace`. -/
@[simps! toSheafedSpace presheaf]
/-
**AlgebraicGeometry.Spec.locallyRingedSpaceObj** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.Spec`。
形式化陈述：CommRingCat → AlgebraicGeometry.LocallyRingedSpace
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The spectrum of a commutative ring, as a `LocallyRingedSpace`.
-/
def Spec.locallyRingedSpaceObj (R : CommRingCat.{u}) : LocallyRingedSpace where
  __ := Spec.sheafedSpaceObj R
  isLocalRing x := (stalkIso R x).toRingEquiv.isLocalRing
/-
**AlgebraicGeometry.Spec.locallyRingedSpaceObj_sheaf** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Spec`。
形式化陈述：∀ (R : CommRingCat), (AlgebraicGeometry.Spec.locallyRingedSpaceObj R).shea
f = AlgebraicGeometry.Spec.structureSheaf ↑R
参数：R : CommRingCat；AlgebraicGeometry.Spec.locallyRingedSpaceObj R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Spec.locallyRingedSpaceObj_sheaf (R : CommRingCat.{u}) :
    (Spec.locallyRingedSpaceObj R).sheaf = structureSheaf R := rfl
/-
**AlgebraicGeometry.Spec.locallyRingedSpaceObj_sheaf'** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Spec`。
形式化陈述：∀ (R : Type u) [inst : CommRing R],   (AlgebraicGeometry.Spec.locallyRinge
dSpaceObj (CommRingCat.of R)).sheaf = AlgebraicGeometry.Spec.structureSheaf R
参数：R : Type u；AlgebraicGeometry.Spec.locallyRingedSpaceObj (CommRingCat.of R)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Spec.locallyRingedSpaceObj_sheaf' (R : Type u) [CommRing R] :
    (Spec.locallyRingedSpaceObj <| CommRingCat.of R).sheaf = structureSheaf R := rfl
/-
**AlgebraicGeometry.Spec.locallyRingedSpaceObj_presheaf_map** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.Spec`。
形式化陈述：∀ (R : CommRingCat)   {U V : (TopologicalSpace.Opens ↑↑(AlgebraicGeometry.
Spec.locallyRingedSpaceObj R).toPresheafedSpace)ᵒᵖ} (i : U ⟶ V),   (AlgebraicGeo
metry.Spec.locallyRingedSpaceObj R).presheaf.map i = (AlgebraicGeometry.Spec.str
uctureSheaf ↑R).obj.map i
参数：R : CommRingCat；TopologicalSpace.Opens ↑↑(AlgebraicGeometry.Spec.locallyRinge
dSpaceObj R).toPresheafedSpace；i : U ⟶ V；AlgebraicGeometry.Spec.locallyRingedSpa
ceObj R；AlgebraicGeometry.Spec.structureSheaf ↑R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Spec.locallyRingedSpaceObj_presheaf_map (R : CommRingCat.{u}) {U V} (i : U ⟶ V) :
    (Spec.locallyRingedSpaceObj R).presheaf.map i =
    (structureSheaf R).1.map i := rfl
/-
**AlgebraicGeometry.Spec.locallyRingedSpaceObj_presheaf'** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.Spec`。
形式化陈述：∀ (R : Type u) [inst : CommRing R],   (AlgebraicGeometry.Spec.locallyRinge
dSpaceObj (CommRingCat.of R)).presheaf =     (AlgebraicGeometry.Spec.structureSh
eaf R).obj
参数：R : Type u；AlgebraicGeometry.Spec.locallyRingedSpaceObj (CommRingCat.of R)；Al
gebraicGeometry.Spec.structureSheaf R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Spec.locallyRingedSpaceObj_presheaf' (R : Type u) [CommRing R] :
    (Spec.locallyRingedSpaceObj <| CommRingCat.of R).presheaf = (structureSheaf R).1 := rfl
/-
**AlgebraicGeometry.Spec.locallyRingedSpaceObj_presheaf_map'** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Spec`。
形式化陈述：∀ (R : Type u) [inst : CommRing R]   {U V :     (TopologicalSpace.Opens ↑↑
(AlgebraicGeometry.Spec.locallyRingedSpaceObj (CommRingCat.of R)).toPresheafedSp
ace)ᵒᵖ}   (i : U ⟶ V),   (AlgebraicGeometry.Spec.locallyRingedSpaceObj (CommRing
Cat.of R)).presheaf.map i =     (AlgebraicGeometry.Spec.structureSheaf R).obj.ma
p i
参数：R : Type u；TopologicalSpace.Opens ↑↑(AlgebraicGeometry.Spec.locallyRingedSpac
eObj (CommRingCat.of R)).toPresheafedSpace；i : U ⟶ V；AlgebraicGeometry.Spec.loca
llyRingedSpaceObj (CommRingCat.of R)；AlgebraicGeometry.Spec.structureSheaf R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Spec.locallyRingedSpaceObj_presheaf_map' (R : Type u) [CommRing R] {U V} (i : U ⟶ V) :
    (Spec.locallyRingedSpaceObj <| CommRingCat.of R).presheaf.map i =
    (structureSheaf R).1.map i := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[elementwise]
/-
**AlgebraicGeometry.stalkMap_toStalk** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometr
y`。
形式化陈述：stalkMap_toStalk {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S)
 : toStalk R (PrimeSpectrum.comap f.hom p) ≫ (Spec.sheafedSpaceMap f).hom.stalkM
ap p = f ≫ toStalk S p
参数：f : R ⟶ S；p : PrimeSpectrum S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.StructureSheaf.algebraMap_germ`：∀ {R : Type u} [inst :
 CommRing R] (U : TopologicalSpace.Opens ↑(AlgebraicGeometry.PrimeSpectrum.Top R
))   (x : ↑(AlgebraicGeometry.PrimeSpe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap_germ`：stalkMap_germ {X Y : Pr
esheafedSpace.{_, _, v} C} (α : X ⟶ Y) (U : Opens Y) (x : X) (hx : α x in U) : Y
.presheaf.germ U (α x) hx ≫ α.stalkMa…
· 使用定理 `AlgebraicGeometry.Spec.sheafedSpaceMap_hom_c_app`：∀ {R S : CommRingCat} 
(f : R ⟶ S)   (U : (TopologicalSpace.Opens ↑↑(AlgebraicGeometry.Spec.sheafedSpac
eObj R).toPresheafedSpace)ᵒᵖ),   (Alge…
· 使用引理 `PrimeSpectrum.continuous_comap`：continuous_comap (f : R ->+* S) : Contin
uous (comap f)
· 使用定理 `AlgebraicGeometry.StructureSheaf.toOpen_comp_comap_assoc`：∀ {R : Type u}
 [inst : CommRing R] {S : Type u} [inst_1 : CommRing S] (f : R →+* S)   (U : Top
ologicalSpace.Opens ↑(AlgebraicGeometry.PrimeS…
-/
theorem stalkMap_toStalk {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    toStalk R (PrimeSpectrum.comap f.hom p) ≫ (Spec.sheafedSpaceMap f).hom.stalkMap p =
      f ≫ toStalk S p := by
  rw [← algebraMap_germ ⊤ p trivial, ← algebraMap_germ ⊤ (PrimeSpectrum.comap f.hom p) trivial,
    Category.assoc]
  erw [PresheafedSpace.stalkMap_germ (Spec.sheafedSpaceMap f).hom ⊤ p trivial]
  rw [Spec.sheafedSpaceMap_hom_c_app]
  erw [toOpen_comp_comap_assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Under the isomorphisms `stalkIso`, the map `stalkMap (Spec.sheafedSpaceMap f) p` corresponds
to the induced local ring homomorphism `Localization.localRingHom`.
-/
@[elementwise]
/-
**AlgebraicGeometry.localRingHom_comp_stalkIso** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry`。
形式化陈述：localRingHom_comp_stalkIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeS
pectrum S) : CommRingCat.ofHom (stalkIso R (PrimeSpectrum.comap f.hom p)).symm.t
oRingHom ≫ (CommRingCat.ofHom (Localization.localRingHom (PrimeSpectrum.comap f.
hom p).asIdeal p.asIdeal f.hom rfl)) ≫ CommRingCat.ofHom (stalkIso S p).toRingHo
m = (Spec.sheafedSpaceMap f).hom.stalkMap p
参数：f : R ⟶ S；p : PrimeSpectrum S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `Localization.localRingHom_unique`：localRingHom_unique (J : Ideal P) [J.I
sPrime] (f : R ->+* P) (hIJ : I = J.comap f) {j : Localization.AtPrime I ->+* Lo
calization.AtPrime J} …
· 使用定理 `PrimeSpectrum.comap_asIdeal`：comap_asIdeal (y : PrimeSpectrum S) : (coma
p f y).asIdeal = Ideal.comap f y.asIdeal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `AlgebraicGeometry.stalkMap_toStalk_apply`：∀ {R S : CommRingCat} (f : R ⟶
 S) (p : PrimeSpectrum ↑S) (x : ↑R),   (CategoryTheory.ConcreteCategory.hom     
    (AlgebraicGeometry.Preshea…

--- 原说明 ---
Under the isomorphisms `stalkIso`, the map `stalkMap (Spec.sheafedSpaceMap f) p`
 corresponds
to the induced local ring homomorphism `Localization.localRingHom`.
-/
theorem localRingHom_comp_stalkIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    CommRingCat.ofHom (stalkIso R (PrimeSpectrum.comap f.hom p)).symm.toRingHom ≫
      (CommRingCat.ofHom (Localization.localRingHom (PrimeSpectrum.comap f.hom p).asIdeal p.asIdeal
          f.hom rfl)) ≫
        CommRingCat.ofHom (stalkIso S p).toRingHom =
      (Spec.sheafedSpaceMap f).hom.stalkMap p :=
  (stalkIso R (PrimeSpectrum.comap f.hom p)).toCommRingCatIso.symm.eq_inv_comp.mp <|
    (stalkIso S p).toCommRingCatIso.symm.comp_inv_eq.mpr <| CommRingCat.hom_ext <|
      Localization.localRingHom_unique _ _ _ (PrimeSpectrum.comap_asIdeal _ _) fun x => by
  dsimp [-RingEquiv.symm_mk]
  simp only [AlgEquiv.commutes, RingEquiv.symm_apply_eq, AlgEquiv.coe_ringEquiv]
  exact stalkMap_toStalk_apply f p x

set_option backward.isDefEq.respectTransparency false in
/--
The induced map of a ring homomorphism on the prime spectra, as a morphism of locally ringed spaces.
-/
@[simps! toHom]
/-
**AlgebraicGeometry.Spec.locallyRingedSpaceMap** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.Spec`。
形式化陈述：{R S : CommRingCat} →   (R ⟶ S) → (AlgebraicGeometry.Spec.locallyRingedSpa
ceObj S ⟶ AlgebraicGeometry.Spec.locallyRingedSpaceObj R)
参数：R ⟶ S；AlgebraicGeometry.Spec.locallyRingedSpaceObj S ⟶ AlgebraicGeometry.Spec
.locallyRingedSpaceObj R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map of a ring homomorphism on the prime spectra, as a morphism of lo
cally ringed spaces.
-/
def Spec.locallyRingedSpaceMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Spec.locallyRingedSpaceObj S ⟶ Spec.locallyRingedSpaceObj R :=
  LocallyRingedSpace.Hom.mk (Spec.sheafedSpaceMap f).hom fun p =>
    IsLocalHom.mk fun a ha => by
    rw [← localRingHom_comp_stalkIso] at ha
    dsimp at ha
    have : IsLocalHom (stalkIso S p) := isLocalHom_equiv _
    have : IsLocalHom (stalkIso R (p.comap f.hom)).symm := isLocalHom_equiv _
    exact ((ha.of_map (stalkIso S p)).of_map _).of_map (stalkIso R (p.comap f.hom)).symm

@[simp]
/-
**AlgebraicGeometry.Spec.locallyRingedSpaceMap_id** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Spec`。
形式化陈述：∀ (R : CommRingCat),   AlgebraicGeometry.Spec.locallyRingedSpaceMap (Categ
oryTheory.CategoryStruct.id R) =     CategoryTheory.CategoryStruct.id (Algebraic
Geometry.Spec.locallyRingedSpaceObj R)
参数：R : CommRingCat；CategoryTheory.CategoryStruct.id R；AlgebraicGeometry.Spec.loc
allyRingedSpaceObj R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.Hom.ext'`：∀ {X Y : AlgebraicGeometr
y.LocallyRingedSpace} {f g : X ⟶ Y}, f.toHom = g.toHom → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Spec.locallyRingedSpaceMap_toHom`：∀ {R S : CommRingCat
} (f : R ⟶ S),   (AlgebraicGeometry.Spec.locallyRingedSpaceMap f).toHom = (Algeb
raicGeometry.Spec.sheafedSpaceMap f).hom
· 使用定理 `AlgebraicGeometry.Spec.sheafedSpaceMap_id`：∀ {R : CommRingCat},   Algebr
aicGeometry.Spec.sheafedSpaceMap (CategoryTheory.CategoryStruct.id R) =     Cate
goryTheory.CategoryStruct.id (A…
-/
theorem Spec.locallyRingedSpaceMap_id (R : CommRingCat.{u}) :
    Spec.locallyRingedSpaceMap (𝟙 R) = 𝟙 (Spec.locallyRingedSpaceObj R) :=
  LocallyRingedSpace.Hom.ext' <| by
    rw [Spec.locallyRingedSpaceMap_toHom, Spec.sheafedSpaceMap_id]; rfl
/-
**AlgebraicGeometry.Spec.locallyRingedSpaceMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Spec`。
形式化陈述：∀ {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T),   AlgebraicGeometry.Spec.
locallyRingedSpaceMap (CategoryTheory.CategoryStruct.comp f g) =     CategoryThe
ory.CategoryStruct.comp (AlgebraicGeometry.Spec.locallyRingedSpaceMap g)       (
AlgebraicGeometry.Spec.locallyRingedSpaceMap f)
参数：f : R ⟶ S；g : S ⟶ T；CategoryTheory.CategoryStruct.comp f g；AlgebraicGeometry.
Spec.locallyRingedSpaceMap g；AlgebraicGeometry.Spec.locallyRingedSpaceMap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.Hom.ext'`：∀ {X Y : AlgebraicGeometr
y.LocallyRingedSpace} {f g : X ⟶ Y}, f.toHom = g.toHom → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Spec.locallyRingedSpaceMap_toHom`：∀ {R S : CommRingCat
} (f : R ⟶ S),   (AlgebraicGeometry.Spec.locallyRingedSpaceMap f).toHom = (Algeb
raicGeometry.Spec.sheafedSpaceMap f).hom
· 使用定理 `AlgebraicGeometry.Spec.sheafedSpaceMap_comp`：∀ {R S T : CommRingCat} (f 
: R ⟶ S) (g : S ⟶ T),   AlgebraicGeometry.Spec.sheafedSpaceMap (CategoryTheory.C
ategoryStruct.comp f g) =     Cat…
-/
theorem Spec.locallyRingedSpaceMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.locallyRingedSpaceMap (f ≫ g) =
      Spec.locallyRingedSpaceMap g ≫ Spec.locallyRingedSpaceMap f :=
  LocallyRingedSpace.Hom.ext' <| by
    rw [Spec.locallyRingedSpaceMap_toHom, Spec.sheafedSpaceMap_comp]; rfl

/-- Spec, as a contravariant functor from commutative rings to locally ringed spaces.
-/
@[simps]
/-
**AlgebraicGeometry.Spec.toLocallyRingedSpace** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Spec`。
形式化陈述：CategoryTheory.Functor CommRingCatᵒᵖ AlgebraicGeometry.LocallyRingedSpace
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Spec, as a contravariant functor from commutative rings to locally ringed spaces
.
-/
def Spec.toLocallyRingedSpace : CommRingCat.{u}ᵒᵖ ⥤ LocallyRingedSpace where
  obj R := Spec.locallyRingedSpaceObj (unop R)
  map f := Spec.locallyRingedSpaceMap f.unop
  map_id R := by dsimp; rw [Spec.locallyRingedSpaceMap_id]
  map_comp f g := by dsimp; rw [Spec.locallyRingedSpaceMap_comp]

section SpecΓ

open AlgebraicGeometry.LocallyRingedSpace

set_option backward.isDefEq.respectTransparency.types false in
/-- The counit morphism `R ⟶ Γ(Spec R)` given by `AlgebraicGeometry.StructureSheaf.toOpen`. -/
/-
**AlgebraicGeometry.toSpec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit morphism `R ⟶ Γ(Spec R)` given by `AlgebraicGeometry.StructureSheaf.t
oOpen`.
-/
def toSpecΓ (R : CommRingCat.{u}) : R ⟶ Γ.obj (op (Spec.toLocallyRingedSpace.obj (op R))) :=
  CommRingCat.ofHom (algebraMap _ _)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.isIso_toSpec** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_toSpecΓ (R : CommRingCat.{u}) : IsIso (toSpecΓ R) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr algebraMap_obj_top_bijective

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**AlgebraicGeometry.Spec_** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Spec_Γ_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ toSpecΓ S = toSpecΓ R ≫ Γ.map (Spec.toLocallyRingedSpace.map f.op).op := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` failed to pick up one of the three lemmas
  ext : 2
  refine Subtype.ext <| funext fun x' => ?_; symm
  erw [comap_apply]
  apply Localization.localRingHom_to_map

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The counit (`SpecΓIdentity.inv.op`) of the adjunction `Γ ⊣ Spec` is an isomorphism. -/
@[simps! hom_app inv_app]
/-
**AlgebraicGeometry.LocallyRingedSpace.Spec** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit (`SpecΓIdentity.inv.op`) of the adjunction `Γ ⊣ Spec` is an isomorphi
sm.
-/
def LocallyRingedSpace.SpecΓIdentity : Spec.toLocallyRingedSpace.rightOp ⋙ Γ ≅ 𝟭 _ :=
  Iso.symm <| NatIso.ofComponents.{u, u, u + 1, u + 1} (fun R ↦ asIso (toSpecΓ R) :)
    fun {X Y} f => by convert! Spec_Γ_naturality (R := X) (S := Y) f

end SpecΓ

set_option backward.isDefEq.respectTransparency false in
/-- The stalk map of `Spec M⁻¹R ⟶ Spec R` is an iso for each `p : Spec M⁻¹R`. -/
/-
**AlgebraicGeometry.isIso_SpecMap_stakMap_localization** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry`。
形式化陈述：isIso_SpecMap_stakMap_localization (R : CommRingCat.{u}) (M : Submonoid R)
 (x : PrimeSpectrum (Localization M)) : IsIso ((Spec.toPresheafedSpace.map (Comm
RingCat.ofHom (algebraMap R (Localization M))).op).stalkMap x)
参数：R : CommRingCat.{u}；M : Submonoid R；x : PrimeSpectrum (Localization M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.localRingHom_comp_stalkIso`：localRingHom_comp_stalkIso
 {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) : CommRingCat.ofHom (
stalkIso R (PrimeSpectrum.comap f.…
· 使用定理 `CategoryTheory.ConcreteCategory.isIso_iff_bijective`：isIso_iff_bijective
 [(forget C).ReflectsIsomorphisms] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Function.Bi
jective f
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
The stalk map of `Spec M⁻¹R ⟶ Spec R` is an iso for each `p : Spec M⁻¹R`.
-/
theorem isIso_SpecMap_stakMap_localization (R : CommRingCat.{u}) (M : Submonoid R)
    (x : PrimeSpectrum (Localization M)) :
    IsIso
      ((Spec.toPresheafedSpace.map
        (CommRingCat.ofHom (algebraMap R (Localization M))).op).stalkMap x) := by
  dsimp only [Spec.toPresheafedSpace_map, Quiver.Hom.unop_op]
  rw [← localRingHom_comp_stalkIso, ConcreteCategory.isIso_iff_bijective]
  dsimp
  simp only [EquivLike.bijective_comp]
  refine (stalkIso (Localization M) x).bijective.comp ?_
  suffices
    IsIso (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M
        x.asIdeal).toRingEquiv.toCommRingCatIso.hom by
    rwa [ConcreteCategory.isIso_iff_bijective] at this
  infer_instance

namespace StructureSheaf

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum R)

set_option backward.isDefEq.respectTransparency.types false in
/-- For an algebra `f : R →+* S`, this is the ring homomorphism `S →+* (f∗ 𝒪ₛ)ₚ` for a `p : Spec R`.
This is shown to be the localization at `p` in `isLocalizedModule_toPushforwardStalkAlgHom`.
-/
/-
**AlgebraicGeometry.StructureSheaf.toPushforwardStalk** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.StructureSheaf`。
形式化陈述：toPushforwardStalk : S ⟶ (Spec.topMap f _* (structureSheaf S).1).stalk p
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
For an algebra `f : R →+* S`, this is the ring homomorphism `S →+* (f∗ 𝒪ₛ)ₚ` for
 a `p : Spec R`.
This is shown to be the localization at `p` in `isLocalizedModule_toPushforwardS
talkAlgHom`.
-/
def toPushforwardStalk : S ⟶ (Spec.topMap f _* (structureSheaf S).1).stalk p :=
  CommRingCat.ofHom (algebraMap _ _) ≫
    @TopCat.Presheaf.germ _ _ _ _ (Spec.topMap f _* (structureSheaf S).1) ⊤ p trivial

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.StructureSheaf.toPushforwardStalk_comp** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：toPushforwardStalk_comp : f ≫ StructureSheaf.toPushforwardStalk f p = Stru
ctureSheaf.toStalk R p ≫ (TopCat.Presheaf.stalkFunctor _ _).map (Spec.sheafedSpa
ceMap f).hom.c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.StructureSheaf.toStalk.eq_1`：∀ (R : Type u) [inst : Co
mmRing R] (x : ↑(AlgebraicGeometry.PrimeSpectrum.Top R)),   AlgebraicGeometry.St
ructureSheaf.toStalk R x =     Cate…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `TopCat.Presheaf.stalkFunctor_map_germ`：stalkFunctor_map_germ {F G : X.Pr
esheaf C} (U : Opens X) (x : X) (hx : x in U) (f : F ⟶ G) : F.germ U x hx ≫ (sta
lkFunctor C x).map f = f.ap…
· 使用定理 `AlgebraicGeometry.Spec_Γ_naturality_assoc`：∀ {R S : CommRingCat} (f : R 
⟶ S) {Z : CommRingCat}   (h :     AlgebraicGeometry.LocallyRingedSpace.Γ.obj    
     (Opposite.op (AlgebraicGeo…
-/
theorem toPushforwardStalk_comp :
    f ≫ StructureSheaf.toPushforwardStalk f p =
      StructureSheaf.toStalk R p ≫
        (TopCat.Presheaf.stalkFunctor _ _).map (Spec.sheafedSpaceMap f).hom.c := by
  rw [StructureSheaf.toStalk, Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  exact Spec_Γ_naturality_assoc f _
/-
**AlgebraicGeometry.StructureSheaf.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.StructureSheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra R ((Spec.topMap f _* (structureSheaf S).1).stalk p) :=
  (f ≫ StructureSheaf.toPushforwardStalk f p).hom.toAlgebra
/-
**AlgebraicGeometry.StructureSheaf.algebraMap_pushforward_stalk** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：algebraMap_pushforward_stalk : algebraMap R ((Spec.topMap f _* (structureS
heaf S).1).stalk p) = (f ≫ StructureSheaf.toPushforwardStalk f p).hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_pushforward_stalk :
    algebraMap R ((Spec.topMap f _* (structureSheaf S).1).stalk p) =
      (f ≫ StructureSheaf.toPushforwardStalk f p).hom :=
  rfl

variable (R S)
variable [Algebra R S]

set_option backward.isDefEq.respectTransparency.types false in
/--
This is the `AlgHom` version of `toPushforwardStalk`, which is the map `S ⟶ (f∗ 𝒪ₛ)ₚ` for some
algebra `R ⟶ S` and some `p : Spec R`.
-/
@[simps!]
/-
**AlgebraicGeometry.StructureSheaf.toPushforwardStalkAlgHom** 是 Mathlib 中的一个定义，位
于命名空间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：toPushforwardStalkAlgHom : S ->ₐ[R] (Spec.topMap (CommRingCat.ofHom (algeb
raMap R S)) _* (structureSheaf S).1).stalk p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the `AlgHom` version of `toPushforwardStalk`, which is the map `S ⟶ (f∗ 
𝒪ₛ)ₚ` for some
algebra `R ⟶ S` and some `p : Spec R`.
-/
def toPushforwardStalkAlgHom :
    S →ₐ[R] (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).stalk p :=
  { (StructureSheaf.toPushforwardStalk (CommRingCat.ofHom (algebraMap R S)) p).hom with
    commutes' := fun _ => rfl }

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.StructureSheaf.isLocalizedModule_toPushforwardStalkAlgHom_au
x** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：isLocalizedModule_toPushforwardStalkAlgHom_aux (y) : exists x : S × p.asId
eal.primeCompl, x.2 • y = toPushforwardStalkAlgHom R S p x.1
参数：y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `TopCat.Presheaf.exists_germ_eq`：exists_germ_eq (F : X.Presheaf C) {x : X
} (t : ToType (stalk.{v, u} F x)) : exists (U : Opens X) (m : x in U) (s : ToTyp
e (F.obj (op U))), F…
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `PrimeSpectrum.isTopologicalBasis_basic_opens`：isTopologicalBasis_basic_o
pens : TopologicalSpace.IsTopologicalBasis (Set.range fun r : R => (basicOpen r 
: Set (PrimeSpectrum R)))
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopCat.Presheaf.germ_res_apply`：germ_res_apply (F : X.Presheaf C) {U V :
 Opens X} (i : U ⟶ V) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) : F.germ
 U x hx (F.map i.op …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen`：∀ (R : Typ
e u) [inst : CommRing R] (r : R),   IsLocalization.Away r ↑((AlgebraicGeometry.S
pec.structureSheaf R).obj.obj (Opposite.op (PrimeS…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `AlgebraicGeometry.StructureSheaf.algebraMap_pushforward_stalk`：algebraMa
p_pushforward_stalk : algebraMap R ((Spec.topMap f _* (structureSheaf S).1).stal
k p) = (f ≫ StructureSheaf.toPushforwardStalk f p).…
· 使用定理 `trivial`：True
· 使用定理 `AlgebraicGeometry.StructureSheaf.toPushforwardStalk.eq_1`：∀ {R S : CommR
ingCat} (f : R ⟶ S) (p : PrimeSpectrum ↑R),   AlgebraicGeometry.StructureSheaf.t
oPushforwardStalk f p =     CategoryTheory.Cat…
· 使用引理 `CommRingCat.comp_apply`：comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T) (r : R) : (f ≫ g) r = g (f r)
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem isLocalizedModule_toPushforwardStalkAlgHom_aux (y) :
    ∃ x : S × p.asIdeal.primeCompl, x.2 • y = toPushforwardStalkAlgHom R S p x.1 := by
  obtain ⟨U, hp, s, e⟩ := TopCat.Presheaf.exists_germ_eq _ y
  obtain ⟨_, ⟨r, rfl⟩, hpr : p ∈ PrimeSpectrum.basicOpen r, hrU : PrimeSpectrum.basicOpen r ≤ U⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p ∈ U from hp) U.2
  change PrimeSpectrum.basicOpen r ≤ U at hrU
  replace e :=
    ((Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).germ_res_apply
      (homOfLE hrU) p hpr _).trans e
  set s' := (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).map
      (homOfLE hrU).op s with h
  replace e : ((Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).obj).germ _
      p hpr) s' = y := by
    rw [h]; exact e
  clear_value s'; clear! U
  obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hsn⟩ :=
    @IsLocalization.surj _ _ _ _ _ _
      (StructureSheaf.IsLocalization.to_basicOpen S <| algebraMap R S r) s'
  refine ⟨⟨s, ⟨r, hpr⟩ ^ n⟩, ?_⟩
  rw [Submonoid.smul_def, Algebra.smul_def, algebraMap_pushforward_stalk, toPushforwardStalk,
    CommRingCat.comp_apply, CommRingCat.comp_apply]
  iterate 2
    erw [← (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).germ_res_apply
      (homOfLE le_top) p hpr]
  rw [← e]
  let f := TopCat.Presheaf.germ (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _*
      (structureSheaf S).obj) _ p hpr
  rw [← map_mul, mul_comm]
  dsimp only [Subtype.coe_mk] at hsn
  rw [← map_pow (algebraMap R S)] at hsn
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.StructureSheaf.isLocalizedModule_toPushforwardStalkAlgHom** 
是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.StructureSheaf`。
形式化陈述：isLocalizedModule_toPushforwardStalkAlgHom : IsLocalizedModule p.asIdeal.p
rimeCompl (toPushforwardStalkAlgHom R S p).toLinearMap
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.mkOfAlgebra`：mkOfAlgebra {R S S' : Type*} [CommSemirin
g R] [Ring S] [Ring S'] [Algebra R S] [Algebra R S'] (M : Submonoid R) (f : S ->
ₐ[R] S') (h₁ : fora…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.StructureSheaf.algebraMap_pushforward_stalk`：algebraMa
p_pushforward_stalk : algebraMap R ((Spec.topMap f _* (structureSheaf S).1).stal
k p) = (f ≫ StructureSheaf.toPushforwardStalk f p).…
· 使用定理 `AlgebraicGeometry.StructureSheaf.toPushforwardStalk_comp`：toPushforwardS
talk_comp : f ≫ StructureSheaf.toPushforwardStalk f p = StructureSheaf.toStalk R
 p ≫ (TopCat.Presheaf.stalkFunctor _ _).map (S…
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`：∀ (R : Type u)
 [inst : CommRing R] (p : PrimeSpectrum R),   IsLocalization.AtPrime (↑((Algebra
icGeometry.Spec.structureSheaf R).presheaf.sta…
· 使用定理 `AlgebraicGeometry.StructureSheaf.isLocalizedModule_toPushforwardStalkAlg
Hom_aux`：isLocalizedModule_toPushforwardStalkAlgHom_aux (y) : exists x : S × p.a
sIdeal.primeCompl, x.2 • y = toPushforwardStalkAlgHom R S p x.1
· 使用定理 `TopCat.Presheaf.germ_eq`：germ_eq (F : X.Presheaf C) {U V : Opens X} (x :
 X) (mU : x in U) (mV : x in V) (s : ToType (F.obj (op U))) (t : ToType (F.obj (
op V))) (h : …
· 使用定理 `trivial`：True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用引理 `CommRingCat.comp_apply`：comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T) (r : R) : (f ≫ g) r = g (f r)
· 使用定理 `AlgebraicGeometry.StructureSheaf.toPushforwardStalk.eq_1`：∀ {R S : CommR
ingCat} (f : R ⟶ S) (p : PrimeSpectrum ↑R),   AlgebraicGeometry.StructureSheaf.t
oPushforwardStalk f p =     CategoryTheory.Cat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `AlgebraicGeometry.StructureSheaf.toPushforwardStalkAlgHom_apply`：∀ (R S 
: CommRingCat) (p : PrimeSpectrum ↑R) [inst : Algebra ↑R ↑S] (x : ↑(CommRingCat.
of ↑S)),   (AlgebraicGeometry.StructureSheaf.toPushfo…
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `PrimeSpectrum.isTopologicalBasis_basic_opens`：isTopologicalBasis_basic_o
pens : TopologicalSpace.IsTopologicalBasis (Set.range fun r : R => (basicOpen r 
: Set (PrimeSpectrum R)))
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen`：∀ (R : Typ
e u) [inst : CommRing R] (r : R),   IsLocalization.Away r ↑((AlgebraicGeometry.S
pec.structureSheaf R).obj.obj (Opposite.op (PrimeS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalization.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.mk'_eq_zero_iff`：∀ {R : Type u_1} [inst : CommSemiring R]
 {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra 
R S] [inst_3 : IsLoc…
（共 35 条，此处仅展示前 30 条）
-/
instance isLocalizedModule_toPushforwardStalkAlgHom :
    IsLocalizedModule p.asIdeal.primeCompl (toPushforwardStalkAlgHom R S p).toLinearMap := by
  apply IsLocalizedModule.mkOfAlgebra
  · intro x hx; rw [algebraMap_pushforward_stalk, toPushforwardStalk_comp]
    change IsUnit ((TopCat.Presheaf.stalkFunctor CommRingCat p).map
      (Spec.sheafedSpaceMap (CommRingCat.ofHom (algebraMap ↑R ↑S))).hom.c _)
    exact (IsLocalization.map_units ((structureSheaf R).presheaf.stalk p) ⟨x, hx⟩).map _
  · apply isLocalizedModule_toPushforwardStalkAlgHom_aux
  · intro x hx
    rw [toPushforwardStalkAlgHom_apply,
      ← (toPushforwardStalk (CommRingCat.ofHom (algebraMap ↑R ↑S)) p).hom.map_zero,
      toPushforwardStalk] at hx
    rw [CommRingCat.comp_apply, map_zero] at hx
    obtain ⟨U, hpU, i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq (C := CommRingCat) _ _ _ _ _ _ hx
    obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p ∈ U.1 from hpU)
        U.2
    apply_fun (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).map
        (homOfLE hrU).op at e
    have : algebraMap S ((structureSheaf S).presheaf.obj _) x = 0 := e
    have :=
      (@IsLocalization.mk'_one _ _ _ _ _ _
            (StructureSheaf.IsLocalization.to_basicOpen S <| algebraMap R S r) x).trans
        this
    obtain ⟨⟨_, n, rfl⟩, e⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp this
    refine ⟨⟨r, hpr⟩ ^ n, ?_⟩
    rw [Submonoid.smul_def, Algebra.smul_def, SubmonoidClass.coe_pow, map_pow]
    exact e

end StructureSheaf

end AlgebraicGeometry

