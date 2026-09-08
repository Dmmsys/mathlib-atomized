/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.EqToHom

/-!

# Prelax functors

This file defines lax prefunctors and prelax functors between bicategories. The point of these
definitions is to provide some common API that will be helpful in the development of both lax and
oplax functors.

## Main definitions

`PrelaxFunctorStruct B C`:

A PrelaxFunctorStruct `F` between quivers `B` and `C`, such that both have been equipped with quiver
structures on the hom-types, consists of
* a function between objects `F.obj : B → C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,

`PrelaxFunctor B C`:

A prelax functor `F` between bicategories `B` and `C` is a `PrelaxFunctorStruct` such that the
associated prefunctors between the hom types are all functors. In other words, it is a
`PrelaxFunctorStruct` that satisfies
* `F.map₂ (𝟙 f) = 𝟙 (F.map f)`,
* `F.map₂ (η ≫ θ) = F.map₂ η ≫ F.map₂ θ`.

`mkOfHomFunctor`: constructs a `PrelaxFunctor` from a map on objects and functors between the
corresponding hom types.

-/

@[expose] public section

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section

variable (B : Type u₁) [Quiver.{v₁} B] [∀ a b : B, Quiver.{w₁} (a ⟶ b)]
variable (C : Type u₂) [Quiver.{v₂} C] [∀ a b : C, Quiver.{w₂} (a ⟶ b)]
variable {D : Type u₃} [Quiver.{v₃} D] [∀ a b : D, Quiver.{w₃} (a ⟶ b)]

/-- A `PrelaxFunctorStruct` between bicategories consists of functions between objects,
1-morphisms, and 2-morphisms. This structure will be extended to define `PrelaxFunctor`.
-/
/-
**CategoryTheory.PrelaxFunctorStruct** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory
`。
形式化陈述：(B : Type u₁) →   [inst : Quiver B] →     [(a b : B) → Quiver (a ⟶ b)] →  
     (C : Type u₂) →         [inst : Quiver C] → [(a b : C) → Quiver (a ⟶ b)] → 
Type (max (max (max (max (max u₁ u₂) v₁) v₂) w₁) w₂)
参数：max (max (max (max u₁ u₂) v₁) v₂) w₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PrelaxFunctorStruct` between bicategories consists of functions between objec
ts,
1-morphisms, and 2-morphisms. This structure will be extended to define `PrelaxF
unctor`.
-/
structure PrelaxFunctorStruct extends Prefunctor B C where
  /-- The action of a lax prefunctor on 2-morphisms. -/
  map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g)

initialize_simps_projections PrelaxFunctorStruct (+toPrefunctor, -obj, -map)

/-- The prefunctor between the underlying quivers. -/
add_decl_doc PrelaxFunctorStruct.toPrefunctor

variable {B} {C}

namespace PrelaxFunctorStruct

/-- Construct a lax prefunctor from a map on objects, and prefunctors between the corresponding
hom types. -/
@[simps]
/-
**CategoryTheory.PrelaxFunctorStruct.mkOfHomPrefunctors** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.PrelaxFunctorStruct`。
形式化陈述：mkOfHomPrefunctors (F : B -> C) (F' : (a : B) -> (b : B) -> Prefunctor (a 
⟶ b) (F a ⟶ F b)) : PrelaxFunctorStruct B C where obj
参数：F : B -> C；F' : (a : B) -> (b : B) -> Prefunctor (a ⟶ b) (F a ⟶ F b)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a lax prefunctor from a map on objects, and prefunctors between the co
rresponding
hom types.
-/
def mkOfHomPrefunctors (F : B → C) (F' : (a : B) → (b : B) → Prefunctor (a ⟶ b) (F a ⟶ F b)) :
    PrelaxFunctorStruct B C where
  obj := F
  map {a b} := (F' a b).obj
  map₂ {a b} := (F' a b).map

/-- The identity lax prefunctor. -/
@[simps]
/-
**CategoryTheory.PrelaxFunctorStruct.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.PrelaxFunctorStruct`。
形式化陈述：id (B : Type u₁) [Quiver.{v₁} B] [forall a b : B, Quiver.{w₁} (a ⟶ b)] : P
relaxFunctorStruct B B
参数：B : Type u₁；a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity lax prefunctor.
-/
def id (B : Type u₁) [Quiver.{v₁} B] [∀ a b : B, Quiver.{w₁} (a ⟶ b)] :
    PrelaxFunctorStruct B B :=
  { Prefunctor.id B with map₂ := fun η => η }
/-
**CategoryTheory.PrelaxFunctorStruct.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
PrelaxFunctorStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (PrelaxFunctorStruct B B) :=
  ⟨PrelaxFunctorStruct.id B⟩

/-- Composition of lax prefunctors. -/
@[simps]
/-
**CategoryTheory.PrelaxFunctorStruct.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.PrelaxFunctorStruct`。
形式化陈述：comp (F : PrelaxFunctorStruct B C) (G : PrelaxFunctorStruct C D) : PrelaxF
unctorStruct B D where toPrefunctor
参数：F : PrelaxFunctorStruct B C；G : PrelaxFunctorStruct C D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of lax prefunctors.
-/
def comp (F : PrelaxFunctorStruct B C) (G : PrelaxFunctorStruct C D) : PrelaxFunctorStruct B D where
  toPrefunctor := F.toPrefunctor.comp G.toPrefunctor
  map₂ := fun η => G.map₂ (F.map₂ η)

end PrelaxFunctorStruct

end

/-- A prelax functor between bicategories is a lax prefunctor such that `map₂` is a functor.
This structure will be extended to define `LaxFunctor` and `OplaxFunctor`.
-/
/-
**CategoryTheory.PrelaxFunctor** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：PrelaxFunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicateg
ory.{w₂, v₂} C] extends PrelaxFunctorStruct B C where /-- Prelax functors preser
ve identity 2-morphisms. -/ map₂_id : forall {a b : B} (f : a ⟶ b), map₂ (𝟙 f) =
 𝟙 (map f)
参数：B : Type u₁；C : Type u₂。
继承自：PrelaxFunctorStruct B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prelax functor between bicategories is a lax prefunctor such that `map₂` is a 
functor.
This structure will be extended to define `LaxFunctor` and `OplaxFunctor`.
-/
structure PrelaxFunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C]
    extends PrelaxFunctorStruct B C where
  /-- Prelax functors preserve identity 2-morphisms. -/
  map₂_id : ∀ {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) := by aesop -- TODO: why not cat_disch?
  /-- Prelax functors preserve compositions of 2-morphisms. -/
  map₂_comp : ∀ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h),
      map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := by cat_disch

namespace PrelaxFunctor

initialize_simps_projections PrelaxFunctor (+toPrelaxFunctorStruct, -obj, -map, -map₂)

attribute [simp] map₂_id
attribute [reassoc] map₂_comp
attribute [simp] map₂_comp

/-- The underlying lax prefunctor. -/
add_decl_doc PrelaxFunctor.toPrelaxFunctorStruct

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

/-- Construct a prelax functor from a map on objects, and functors between the corresponding
hom types. -/
@[simps]
/-
**CategoryTheory.PrelaxFunctor.mkOfHomFunctors** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.PrelaxFunctor`。
形式化陈述：mkOfHomFunctors (F : B -> C) (F' : (a : B) -> (b : B) -> (a ⟶ b) ⥤ (F a ⟶ 
F b)) : PrelaxFunctor B C where toPrelaxFunctorStruct
参数：F : B -> C；F' : (a : B) -> (b : B) -> (a ⟶ b) ⥤ (F a ⟶ F b)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a prelax functor from a map on objects, and functors between the corre
sponding
hom types.
-/
def mkOfHomFunctors (F : B → C) (F' : (a : B) → (b : B) → (a ⟶ b) ⥤ (F a ⟶ F b)) :
    PrelaxFunctor B C where
  toPrelaxFunctorStruct := PrelaxFunctorStruct.mkOfHomPrefunctors F fun a b => (F' a b).toPrefunctor
  map₂_id {a b} := (F' a b).map_id
  map₂_comp {a b} := (F' a b).map_comp

/-- The identity prelax functor. -/
@[simps]
/-
**CategoryTheory.PrelaxFunctor.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Prel
axFunctor`。
形式化陈述：id (B : Type u₁) [Bicategory.{w₁, v₁} B] : PrelaxFunctor B B where toPrela
xFunctorStruct
参数：B : Type u₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity prelax functor.
-/
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : PrelaxFunctor B B where
  toPrelaxFunctorStruct := PrelaxFunctorStruct.id B
/-
**CategoryTheory.PrelaxFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Prelax
Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (PrelaxFunctor B B) :=
  ⟨PrelaxFunctor.id B⟩

variable (F : PrelaxFunctor B C)

/-- Composition of prelax functors. -/
@[simps]
/-
**CategoryTheory.PrelaxFunctor.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pr
elaxFunctor`。
形式化陈述：comp (G : PrelaxFunctor C D) : PrelaxFunctor B D where toPrelaxFunctorStru
ct
参数：G : PrelaxFunctor C D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of prelax functors.
-/
def comp (G : PrelaxFunctor C D) : PrelaxFunctor B D where
  toPrelaxFunctorStruct := PrelaxFunctorStruct.comp F.toPrelaxFunctorStruct G.toPrelaxFunctorStruct

/-- Function between 1-morphisms as a functor. -/
@[simps]
/-
**CategoryTheory.PrelaxFunctor.mapFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.PrelaxFunctor`。
形式化陈述：mapFunctor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) where obj f
参数：a b : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Function between 1-morphisms as a functor.
-/
def mapFunctor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) where
  obj f := F.map f
  map η := F.map₂ η

@[simp]
/-
**CategoryTheory.PrelaxFunctor.mkOfHomFunctors_mapFunctor** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.PrelaxFunctor`。
形式化陈述：mkOfHomFunctors_mapFunctor (F : B -> C) (F' : (a : B) -> (b : B) -> (a ⟶ b
) ⥤ (F a ⟶ F b)) (a b : B) : (mkOfHomFunctors F F').mapFunctor a b = F' a b
参数：F : B -> C；F' : (a : B) -> (b : B) -> (a ⟶ b) ⥤ (F a ⟶ F b)；a b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkOfHomFunctors_mapFunctor (F : B → C) (F' : (a : B) → (b : B) → (a ⟶ b) ⥤ (F a ⟶ F b))
    (a b : B) : (mkOfHomFunctors F F').mapFunctor a b = F' a b :=
  rfl

section

variable {a b : B}

/-- A prelax functor `F` sends 2-isomorphisms `η : f ≅ g` to 2-isomorphisms
`F.map f ≅ F.map g`. -/
@[simps! -isSimp]
/-
**CategoryTheory.PrelaxFunctor.map** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.P
relaxFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prelax functor `F` sends 2-isomorphisms `η : f ≅ g` to 2-isomorphisms
`F.map f ≅ F.map g`.
-/
abbrev map₂Iso {f g : a ⟶ b} (η : f ≅ g) : F.map f ≅ F.map g :=
  (F.mapFunctor a b).mapIso η
/-
**CategoryTheory.PrelaxFunctor.map** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pre
laxFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance map₂_isIso {f g : a ⟶ b} (η : f ⟶ g) [IsIso η] : IsIso (F.map₂ η) :=
  (F.map₂Iso (asIso η)).isIso_hom

@[simp]
/-
**CategoryTheory.PrelaxFunctor.map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pre
laxFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_inv {f g : a ⟶ b} (η : f ⟶ g) [IsIso η] : F.map₂ (inv η) = inv (F.map₂ η) := by
  apply IsIso.eq_inv_of_hom_inv_id
  simp [← F.map₂_comp η (inv η)]
/-
**CategoryTheory.PrelaxFunctor.map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pre
laxFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_iso_inv {f g : a ⟶ b} (η : f ≅ g) :
    F.map₂ η.inv = inv (F.map₂ η.hom) := by
  rw [← F.map₂_inv, IsIso.Iso.inv_hom]

@[reassoc, simp]
/-
**CategoryTheory.PrelaxFunctor.map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pre
laxFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_hom_inv {f g : a ⟶ b} (η : f ≅ g) :
    F.map₂ η.hom ≫ F.map₂ η.inv = 𝟙 (F.map f) := by
  rw [← F.map₂_comp, Iso.hom_inv_id, F.map₂_id]

@[reassoc]
/-
**CategoryTheory.PrelaxFunctor.map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pre
laxFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_hom_inv_isIso {f g : a ⟶ b} (η : f ⟶ g) [IsIso η] :
    F.map₂ η ≫ F.map₂ (inv η) = 𝟙 (F.map f) := by
  simp

@[reassoc, simp]
/-
**CategoryTheory.PrelaxFunctor.map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pre
laxFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_inv_hom {f g : a ⟶ b} (η : f ≅ g) :
    F.map₂ η.inv ≫ F.map₂ η.hom = 𝟙 (F.map g) := by
  rw [← F.map₂_comp, Iso.inv_hom_id, F.map₂_id]

@[reassoc]
/-
**CategoryTheory.PrelaxFunctor.map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pre
laxFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_inv_hom_isIso {f g : a ⟶ b} (η : f ⟶ g) [IsIso η] :
    F.map₂ (inv η) ≫ F.map₂ η = 𝟙 (F.map g) := by
  simp

end

/-
**CategoryTheory.PrelaxFunctor.map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pre
laxFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_eqToHom {x y : B} (f g : x ⟶ y) (hfg : f = g) :
    F.map₂ (eqToHom hfg) = eqToHom (by rw [← hfg]) := by
  subst hfg
  simp

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.PrelaxFunctor.map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pre
laxFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂Iso_eqToIso {x y : B} (f g : x ⟶ y) (hfg : f = g) :
    F.map₂Iso (eqToIso hfg) = eqToIso (by rw [← hfg]) := by
  subst hfg
  simp

end PrelaxFunctor

end CategoryTheory

