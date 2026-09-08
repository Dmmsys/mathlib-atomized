/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Linear Functors

An additive functor between two `R`-linear categories is called *linear*
if the induced map on hom types is a morphism of `R`-modules.

## Implementation details

`Functor.Linear` is a `Prop`-valued class, defined by saying that
for every two objects `X` and `Y`, the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of `R`-modules.

-/

@[expose] public section


namespace CategoryTheory

variable (R : Type*) [Semiring R] {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  (F : C ⥤ D)

/-- An additive functor `F` is `R`-linear provided `F.map` is an `R`-module morphism. -/
/-
**CategoryTheory.Functor.Linear** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：(R : Type u_1) →   [inst : Semiring R] →     {C : Type u_2} →       {D : T
ype u_3} →         [inst_1 : CategoryTheory.Category.{v_1, u_2} C] →           [
inst_2 : CategoryTheory.Category.{v_2, u_3} D] →             [inst_3 : CategoryT
heory.Preadditive C] →               [inst_4 : CategoryTheory.Preadditive D] →  
               [CategoryTheory.Linear R C] → [CategoryTheory.Linear R D] → Categ
oryTheory.Functor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive functor `F` is `R`-linear provided `F.map` is an `R`-module morphism
.
-/
class Functor.Linear : Prop where
  /-- the functor induces a linear map on morphisms -/
  map_smul : ∀ {X Y : C} (f : X ⟶ Y) (r : R), F.map (r • f) = r • F.map f := by cat_disch
/-
**CategoryTheory.Functor.linear_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：∀ (R : Type u_1) [inst : Semiring R] {C : Type u_2} {D : Type u_3} [inst_1
 : CategoryTheory.Category.{v_1, u_2} C]   [inst_2 : CategoryTheory.Category.{v_
2, u_3} D] [inst_3 : CategoryTheory.Preadditive C]   [inst_4 : CategoryTheory.Pr
eadditive D] [inst_5 : CategoryTheory.Linear R C] [inst_6 : CategoryTheory.Linea
r R D]   (F : CategoryTheory.Functor C D),   CategoryTheory.Functor.Linear R F ↔
     ∀ (X : C) (r : R), F.map (r • CategoryTheory.CategoryStruct.id X) = r • Cat
egoryTheory.CategoryStruct.id (F.obj X)
参数：R : Type u_1；F : CategoryTheory.Functor C D；X : C；r : R；r • CategoryTheory.Ca
tegoryStruct.id X；F.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.Linear.map_smul`：∀ {R : Type u_1} {inst : Semirin
g R} {C : Type u_2} {D : Type u_3} {inst_1 : CategoryTheory.Category.{v_1, u_2} 
C}   {inst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma Functor.linear_iff (F : C ⥤ D) :
    Functor.Linear R F ↔ ∀ (X : C) (r : R), F.map (r • 𝟙 X) = r • 𝟙 (F.obj X) := by
  constructor
  · intro h X r
    rw [h.map_smul, F.map_id]
  · refine fun h => ⟨fun {X Y} f r => ?_⟩
    have : r • f = (r • 𝟙 X) ≫ f := by simp
    rw [this, F.map_comp, h, Linear.smul_comp, Category.id_comp]

section Linear

namespace Functor

section

variable {R} [Linear R F]

@[simp]
/-
**CategoryTheory.Functor.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：map_smul {X Y : C} (r : R) (f : X ⟶ Y) : F.map (r • f) = r • F.map f
参数：r : R；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Linear.map_smul`：∀ {R : Type u_1} {inst : Semirin
g R} {C : Type u_2} {D : Type u_3} {inst_1 : CategoryTheory.Category.{v_1, u_2} 
C}   {inst_2 : CategoryTheor…
-/
theorem map_smul {X Y : C} (r : R) (f : X ⟶ Y) : F.map (r • f) = r • F.map f :=
  Functor.Linear.map_smul _ _

@[simp]
/-
**CategoryTheory.Functor.map_units_smul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：map_units_smul {X Y : C} (r : Rˣ) (f : X ⟶ Y) : F.map (r • f) = r • F.map 
f
参数：r : Rˣ；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_smul`：map_smul {X Y : C} (r : R) (f : X ⟶ Y) 
: F.map (r • f) = r • F.map f
-/
theorem map_units_smul {X Y : C} (r : Rˣ) (f : X ⟶ Y) : F.map (r • f) = r • F.map f := by
  apply map_smul
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Linear R (𝟭 C) where

section

variable {E : Type*} [Category* E] [Preadditive E] [CategoryTheory.Linear R E] (G : D ⥤ E)

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Linear R G] : Linear R (F ⋙ G) where

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.linear_of_full_essSurj_comp** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：linear_of_full_essSurj_comp [F.Full] [F.EssSurj] [Functor.Linear R (F ⋙ G)
] : Functor.Linear R G
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_smul`：map_smul {X Y : C} (r : R) (f : X ⟶ Y) 
: F.map (r • f) = r • F.map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.Linear.comp_smul`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
-/
lemma linear_of_full_essSurj_comp [F.Full] [F.EssSurj] [Functor.Linear R (F ⋙ G)] :
    Functor.Linear R G := by
  refine ⟨fun {X Y} f r ↦ ?_⟩
  obtain ⟨X', Y', eX, eY, f', rfl⟩ :
      ∃ (X' Y' : C) (eX : F.obj X' ≅ X) (eY : F.obj Y' ≅ Y)
        (f' : X' ⟶ Y'), f = eX.inv ≫ F.map f' ≫ eY.hom := by
    obtain ⟨f', hf'⟩ :=
      F.map_surjective ((F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso Y).inv)
    exact ⟨_, _, F.objObjPreimageIso X, F.objObjPreimageIso Y, f', by cat_disch⟩
  simpa only [comp_map, map_smul, Linear.smul_comp, Linear.comp_smul, ← G.map_comp]
    using G.map eX.inv ≫= ((F ⋙ G).map_smul r f') =≫ G.map eY.hom
/-
**CategoryTheory.Functor.linear_comp_iff_of_full_of_essSurj** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：linear_comp_iff_of_full_of_essSurj [F.Full] [F.EssSurj] : Functor.Linear R
 (F ⋙ G) ↔ Functor.Linear R G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.linear_of_full_essSurj_comp`：linear_of_full_essSu
rj_comp [F.Full] [F.EssSurj] [Functor.Linear R (F ⋙ G)] : Functor.Linear R G
· 使用定理 `CategoryTheory.Functor.instLinearComp`：∀ {R : Type u_1} [inst : Semiring
 R] {C : Type u_2} {D : Type u_3} [inst_1 : CategoryTheory.Category.{v_1, u_2} C
]   [inst_2 : CategoryTheor…
-/
lemma linear_comp_iff_of_full_of_essSurj [F.Full] [F.EssSurj] :
    Functor.Linear R (F ⋙ G) ↔ Functor.Linear R G :=
  ⟨fun _ ↦ linear_of_full_essSurj_comp F G, fun _ ↦ inferInstance⟩

end

variable (R) [F.Additive]

/-- `F.mapLinearMap` is an `R`-linear map whose underlying function is `F.map`. -/
@[simps]
/-
**CategoryTheory.Functor.mapLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：mapLinearMap {X Y : C} : (X ⟶ Y) ->ₗ[R] F.obj X ⟶ F.obj Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_smul`：map_smul {X Y : C} (r : R) (f : X ⟶ Y) 
: F.map (r • f) = r • F.map f

--- 原说明 ---
`F.mapLinearMap` is an `R`-linear map whose underlying function is `F.map`.
-/
def mapLinearMap {X Y : C} : (X ⟶ Y) →ₗ[R] F.obj X ⟶ F.obj Y :=
  { F.mapAddHom with map_smul' := fun r f => F.map_smul r f }
/-
**CategoryTheory.Functor.coe_mapLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：coe_mapLinearMap {X Y : C} : ⇑(F.mapLinearMap R : (X ⟶ Y) ->ₗ[R] _) = F.ma
p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mapLinearMap {X Y : C} : ⇑(F.mapLinearMap R : (X ⟶ Y) →ₗ[R] _) = F.map := rfl

end

variable {F} in
/-
**CategoryTheory.Functor.linear_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：linear_of_iso {G : C ⥤ D} (e : F ≅ G) [F.Linear R] : G.Linear R
参数：e : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_smul`：map_smul {X Y : C} (r : R) (f : X ⟶ Y) 
: F.map (r • f) = r • F.map f
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Linear.comp_smul`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma linear_of_iso {G : C ⥤ D} (e : F ≅ G) [F.Linear R] : G.Linear R := by
  exact
    { map_smul := fun f r => by
        simp only [← NatIso.naturality_1 e (r • f), F.map_smul, Linear.smul_comp,
          NatTrans.naturality, Linear.comp_smul, Iso.inv_hom_id_app_assoc] }

section InducedCategory

/-
**CategoryTheory.Functor.inducedFunctorLinear** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：∀ (R : Type u_1) [inst : Semiring R] {C : Type u_2} {D : Type u_3} [inst_1
 : CategoryTheory.Category.{v_2, u_3} D]   [inst_2 : CategoryTheory.Preadditive 
D] [inst_3 : CategoryTheory.Linear R D] (F : C → D),   CategoryTheory.Functor.Li
near R (CategoryTheory.inducedFunctor F)
参数：R : Type u_1；F : C → D；CategoryTheory.inducedFunctor F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inducedFunctorLinear (F : C → D) : Functor.Linear R (inducedFunctor F) where

end InducedCategory

/-
**CategoryTheory.Functor.fullSubcategoryInclusionLinear** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：∀ (R : Type u_1) [inst : Semiring R] {C : Type u_4} [inst_1 : CategoryTheo
ry.Category.{v_3, u_4} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : Ca
tegoryTheory.Linear R C] (Z : CategoryTheory.ObjectProperty C),   CategoryTheory
.Functor.Linear R Z.ι
参数：R : Type u_1；Z : CategoryTheory.ObjectProperty C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fullSubcategoryInclusionLinear {C : Type*} [Category* C] [Preadditive C]
    [CategoryTheory.Linear R C] (Z : ObjectProperty C) : Z.ι.Linear R where

section

variable {R} [Additive F]

/-
**CategoryTheory.Functor.natLinear** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：natLinear : F.Linear Nat where map_smul f r
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
-/
instance natLinear : F.Linear ℕ where
  map_smul f r := F.mapAddHom.map_nsmul r f
/-
**CategoryTheory.Functor.intLinear** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：intLinear : F.Linear Int where map_smul f r
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_zsmul`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup
 α] [inst_1 : SubtractionMonoid β] (f : α →+ β) (n : ℤ) (g : α),   f (n • g) = n
 • f g
-/
instance intLinear : F.Linear ℤ where
  map_smul f r := F.mapAddHom.map_zsmul r f

variable [CategoryTheory.Linear ℚ C] [CategoryTheory.Linear ℚ D]
/-
**CategoryTheory.Functor.ratLinear** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：ratLinear : F.Linear Rat where map_smul f r
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
instance ratLinear : F.Linear ℚ where
  map_smul f r := F.mapAddHom.toRatLinearMap.map_smul r f

end

end Functor

namespace Equivalence

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Equivalence.inverseLinear** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Equivalence`。
形式化陈述：inverseLinear (e : C ≌ D) [e.functor.Linear R] : e.inverse.Linear R where 
map_smul r f
参数：e : C ≌ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Equivalence.fun_inv_map`：fun_inv_map (e : C ≌ D) (X Y : D
) (f : X ⟶ Y) : e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitI
nv.app Y
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.Linear.comp_smul`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.Functor.map_smul`：map_smul {X Y : C} (r : R) (f : X ⟶ Y) 
: F.map (r • f) = r • F.map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance inverseLinear (e : C ≌ D) [e.functor.Linear R] : e.inverse.Linear R where
  map_smul r f := by
    apply e.functor.map_injective
    simp

end Equivalence

end Linear

end CategoryTheory

