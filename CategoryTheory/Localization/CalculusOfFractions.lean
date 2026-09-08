/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Opposite

/-!
# Calculus of fractions

Following the definitions by [Gabriel and Zisman][gabriel-zisman-1967],
given a morphism property `W : MorphismProperty C` on a category `C`,
we introduce the class `W.HasLeftCalculusOfFractions`. The main
result `Localization.exists_leftFraction` is that if `L : C ⥤ D`
is a localization functor for `W`, then for any morphism `L.obj X ⟶ L.obj Y` in `D`,
there exists an auxiliary object `Y' : C` and morphisms `g : X ⟶ Y'` and `s : Y ⟶ Y'`,
with `W s`, such that the given morphism is a sort of fraction `g / s`,
or more precisely of the form `L.map g ≫ (Localization.isoOfHom L W s hs).inv`.
We also show that the functor `L.mapArrow : Arrow C ⥤ Arrow D` is essentially surjective.

Similar results are obtained when `W` has a right calculus of fractions.

## References

* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*][gabriel-zisman-1967]

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

open Category

namespace MorphismProperty

/-- A left fraction from `X : C` to `Y : C` for `W : MorphismProperty C` consists of the
datum of an object `Y' : C` and maps `f : X ⟶ Y'` and `s : Y ⟶ Y'` such that `W s`. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] → Categor
yTheory.MorphismProperty C → C → C → Type (max u_1 v_1)
参数：max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A left fraction from `X : C` to `Y : C` for `W : MorphismProperty C` consists of
 the
datum of an object `Y' : C` and maps `f : X ⟶ Y'` and `s : Y ⟶ Y'` such that `W 
s`.
-/
structure LeftFraction (W : MorphismProperty C) (X Y : C) where
  /-- the auxiliary object of a left fraction -/
  {Y' : C}
  /-- the numerator of a left fraction -/
  f : X ⟶ Y'
  /-- the denominator of a left fraction -/
  s : Y ⟶ Y'
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s

namespace LeftFraction

variable (W : MorphismProperty C) {X Y : C}

/-- The left fraction from `X` to `Y` given by a morphism `f : X ⟶ Y`. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.LeftFraction.ofHom** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：ofHom (f : X ⟶ Y) [W.ContainsIdentities] : W.LeftFraction X Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)

--- 原说明 ---
The left fraction from `X` to `Y` given by a morphism `f : X ⟶ Y`.
-/
def ofHom (f : X ⟶ Y) [W.ContainsIdentities] :
    W.LeftFraction X Y := mk f (𝟙 Y) (W.id_mem Y)

variable {W}

/-- The left fraction from `X` to `Y` given by a morphism `s : Y ⟶ X` such that `W s`. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.LeftFraction.ofInv** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：ofInv (s : Y ⟶ X) (hs : W s) : W.LeftFraction X Y
参数：s : Y ⟶ X；hs : W s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left fraction from `X` to `Y` given by a morphism `s : Y ⟶ X` such that `W s
`.
-/
def ofInv (s : Y ⟶ X) (hs : W s) :
    W.LeftFraction X Y := mk (𝟙 X) s hs
/-
**CategoryTheory.MorphismProperty.LeftFraction.** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.MorphismProperty.LeftFraction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {L : C ⥤ D} [L.IsLocalization W] (z : W.LeftFraction X Y) :
    IsIso (L.map z.s) :=
  Localization.inverts L W _ z.hs

/-- If `φ : W.LeftFraction X Y` and `L` is a functor which inverts `W`, this is the
induced morphism `L.obj X ⟶ L.obj Y` -/
/-
**CategoryTheory.MorphismProperty.LeftFraction.map** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：map (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : L.obj X
 ⟶ L.obj Y
参数：φ : W.LeftFraction X Y；L : C ⥤ D；hL : W.IsInvertedBy L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ : W.LeftFraction X Y` and `L` is a functor which inverts `W`, this is the
induced morphism `L.obj X ⟶ L.obj Y`
-/
noncomputable def map (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.obj X ⟶ L.obj Y :=
  have := hL _ φ.hs
  L.map φ.f ≫ inv (L.map φ.s)

@[reassoc (attr := simp)]
/-
**CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：map_comp_map_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L
) : φ.map L hL ≫ L.map φ.s = L.map φ.f
参数：φ : W.LeftFraction X Y；L : C ⥤ D；hL : W.IsInvertedBy L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_map_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    φ.map L hL ≫ L.map φ.s = L.map φ.f := by
  let := hL _ φ.hs
  simp [map]

variable (W)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.LeftFraction.map_ofHom** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：map_ofHom (f : X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdent
ities] : (ofHom W f).map L hL = L.map f
参数：f : X ⟶ Y；L : C ⥤ D；hL : W.IsInvertedBy L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.IsIso.inv_id`：inv_id : inv (𝟙 X) = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_ofHom (f : X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities] :
    (ofHom W f).map L hL = L.map f := by
  simp [map]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MorphismProperty.LeftFraction.map_ofInv_hom_id** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：map_ofInv_hom_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L
) : (ofInv s hs).map L hL ≫ L.map s = 𝟙 _
参数：s : Y ⟶ X；hs : W s；L : C ⥤ D；hL : W.IsInvertedBy L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_ofInv_hom_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    (ofInv s hs).map L hL ≫ L.map s = 𝟙 _ := by
  let := hL _ hs
  simp [map]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MorphismProperty.LeftFraction.map_hom_ofInv_id** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：map_hom_ofInv_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L
) : L.map s ≫ (ofInv s hs).map L hL = 𝟙 _
参数：s : Y ⟶ X；hs : W s；L : C ⥤ D；hL : W.IsInvertedBy L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_hom_ofInv_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.map s ≫ (ofInv s hs).map L hL = 𝟙 _ := by
  let := hL _ hs
  simp [map]

variable {W}
/-
**CategoryTheory.MorphismProperty.LeftFraction.cases** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：cases (α : W.LeftFraction X Y) : exists (Y' : C) (f : X ⟶ Y') (s : Y ⟶ Y')
 (hs : W s), α = LeftFraction.mk f s hs
参数：α : W.LeftFraction X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …
-/
lemma cases (α : W.LeftFraction X Y) :
    ∃ (Y' : C) (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s), α = LeftFraction.mk f s hs :=
  ⟨_, _, _, _, rfl⟩

end LeftFraction

/-- A right fraction from `X : C` to `Y : C` for `W : MorphismProperty C` consists of the
datum of an object `X' : C` and maps `s : X' ⟶ X` and `f : X' ⟶ Y` such that `W s`. -/
/-
**CategoryTheory.MorphismProperty.RightFraction** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] → Categor
yTheory.MorphismProperty C → C → C → Type (max u_1 v_1)
参数：max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A right fraction from `X : C` to `Y : C` for `W : MorphismProperty C` consists o
f the
datum of an object `X' : C` and maps `s : X' ⟶ X` and `f : X' ⟶ Y` such that `W 
s`.
-/
structure RightFraction (W : MorphismProperty C) (X Y : C) where
  /-- the auxiliary object of a right fraction -/
  {X' : C}
  /-- the denominator of a right fraction -/
  s : X' ⟶ X
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s
  /-- the numerator of a right fraction -/
  f : X' ⟶ Y

namespace RightFraction

variable (W : MorphismProperty C)
variable {X Y : C}

/-- The right fraction from `X` to `Y` given by a morphism `f : X ⟶ Y`. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.RightFraction.ofHom** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.MorphismProperty.RightFraction`。
形式化陈述：ofHom (f : X ⟶ Y) [W.ContainsIdentities] : W.RightFraction X Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)

--- 原说明 ---
The right fraction from `X` to `Y` given by a morphism `f : X ⟶ Y`.
-/
def ofHom (f : X ⟶ Y) [W.ContainsIdentities] :
    W.RightFraction X Y := mk (𝟙 X) (W.id_mem X) f

variable {W}

/-- The right fraction from `X` to `Y` given by a morphism `s : Y ⟶ X` such that `W s`. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.RightFraction.ofInv** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.MorphismProperty.RightFraction`。
形式化陈述：ofInv (s : Y ⟶ X) (hs : W s) : W.RightFraction X Y
参数：s : Y ⟶ X；hs : W s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right fraction from `X` to `Y` given by a morphism `s : Y ⟶ X` such that `W 
s`.
-/
def ofInv (s : Y ⟶ X) (hs : W s) :
    W.RightFraction X Y := mk s hs (𝟙 Y)
/-
**CategoryTheory.MorphismProperty.RightFraction.** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.MorphismProperty.RightFraction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {L : C ⥤ D} [L.IsLocalization W] (z : W.RightFraction X Y) :
    IsIso (L.map z.s) :=
  Localization.inverts L W _ z.hs

/-- If `φ : W.RightFraction X Y` and `L` is a functor which inverts `W`, this is the
induced morphism `L.obj X ⟶ L.obj Y` -/
/-
**CategoryTheory.MorphismProperty.RightFraction.map** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MorphismProperty.RightFraction`。
形式化陈述：map (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : L.obj 
X ⟶ L.obj Y
参数：φ : W.RightFraction X Y；L : C ⥤ D；hL : W.IsInvertedBy L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ : W.RightFraction X Y` and `L` is a functor which inverts `W`, this is the
induced morphism `L.obj X ⟶ L.obj Y`
-/
noncomputable def map (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.obj X ⟶ L.obj Y :=
  have := hL _ φ.hs
  inv (L.map φ.s) ≫ L.map φ.f

@[reassoc (attr := simp)]
/-
**CategoryTheory.MorphismProperty.RightFraction.map_s_comp_map** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.MorphismProperty.RightFraction`。
形式化陈述：map_s_comp_map (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy 
L) : L.map φ.s ≫ φ.map L hL = L.map φ.f
参数：φ : W.RightFraction X Y；L : C ⥤ D；hL : W.IsInvertedBy L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.RightFraction X…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_s_comp_map (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.map φ.s ≫ φ.map L hL = L.map φ.f := by
  let := hL _ φ.hs
  simp [map]

variable (W)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.MorphismProperty.RightFraction.map_ofHom** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.MorphismProperty.RightFraction`。
形式化陈述：map_ofHom (f : X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdent
ities] : (ofHom W f).map L hL = L.map f
参数：f : X ⟶ Y；L : C ⥤ D；hL : W.IsInvertedBy L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.IsIso.inv_id`：inv_id : inv (𝟙 X) = 𝟙 X
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_ofHom (f : X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities] :
    (ofHom W f).map L hL = L.map f := by
  simp [map]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MorphismProperty.RightFraction.map_ofInv_hom_id** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.MorphismProperty.RightFraction`。
形式化陈述：map_ofInv_hom_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L
) : (ofInv s hs).map L hL ≫ L.map s = 𝟙 _
参数：s : Y ⟶ X；hs : W s；L : C ⥤ D；hL : W.IsInvertedBy L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_ofInv_hom_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    (ofInv s hs).map L hL ≫ L.map s = 𝟙 _ := by
  let := hL _ hs
  simp [map]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MorphismProperty.RightFraction.map_hom_ofInv_id** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.MorphismProperty.RightFraction`。
形式化陈述：map_hom_ofInv_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L
) : L.map s ≫ (ofInv s hs).map L hL = 𝟙 _
参数：s : Y ⟶ X；hs : W s；L : C ⥤ D；hL : W.IsInvertedBy L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_hom_ofInv_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.map s ≫ (ofInv s hs).map L hL = 𝟙 _ := by
  let := hL _ hs
  simp [map]

variable {W}
/-
**CategoryTheory.MorphismProperty.RightFraction.cases** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MorphismProperty.RightFraction`。
形式化陈述：cases (α : W.RightFraction X Y) : exists (X' : C) (s : X' ⟶ X) (hs : W s) 
(f : X' ⟶ Y), α = RightFraction.mk s hs f
参数：α : W.RightFraction X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.RightFraction X…
-/
lemma cases (α : W.RightFraction X Y) :
    ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : X' ⟶ Y), α = RightFraction.mk s hs f :=
  ⟨_, _, _, _, rfl⟩

end RightFraction

variable (W : MorphismProperty C)

/-- A multiplicative morphism property `W` has left calculus of fractions if
any right fraction can be turned into a left fraction and that two morphisms
that can be equalized by precomposition with a morphism in `W` can also
be equalized by postcomposition with a morphism in `W`. -/
/-
**CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions** 是 Mathlib 中的一个归纳类
型，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → CategoryT
heory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiplicative morphism property `W` has left calculus of fractions if
any right fraction can be turned into a left fraction and that two morphisms
that can be equalized by precomposition with a morphism in `W` can also
be equalized by postcomposition with a morphism in `W`.
-/
class HasLeftCalculusOfFractions : Prop extends W.IsMultiplicative where
  exists_leftFraction ⦃X Y : C⦄ (φ : W.RightFraction X Y) :
    ∃ (ψ : W.LeftFraction X Y), φ.f ≫ ψ.s = φ.s ≫ ψ.f
  ext : ∀ ⦃X' X Y : C⦄ (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X) (_ : W s)
    (_ : s ≫ f₁ = s ≫ f₂), ∃ (Y' : C) (t : Y ⟶ Y') (_ : W t), f₁ ≫ t = f₂ ≫ t

/-- A multiplicative morphism property `W` has right calculus of fractions if
any left fraction can be turned into a right fraction and that two morphisms
that can be equalized by postcomposition with a morphism in `W` can also
be equalized by precomposition with a morphism in `W`. -/
/-
**CategoryTheory.MorphismProperty.HasRightCalculusOfFractions** 是 Mathlib 中的一个归纳
类型，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → CategoryT
heory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiplicative morphism property `W` has right calculus of fractions if
any left fraction can be turned into a right fraction and that two morphisms
that can be equalized by postcomposition with a morphism in `W` can also
be equalized by precomposition with a morphism in `W`.
-/
class HasRightCalculusOfFractions : Prop extends W.IsMultiplicative where
  exists_rightFraction ⦃X Y : C⦄ (φ : W.LeftFraction X Y) :
    ∃ (ψ : W.RightFraction X Y), ψ.s ≫ φ.f = ψ.f ≫ φ.s
  ext : ∀ ⦃X Y Y' : C⦄ (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y') (_ : W s)
    (_ : f₁ ≫ s = f₂ ≫ s), ∃ (X' : C) (t : X' ⟶ X) (_ : W t), t ≫ f₁ = t ≫ f₂

variable {W}
/-
**CategoryTheory.MorphismProperty.RightFraction.exists_leftFraction** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.RightFraction`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Catego
ryTheory.MorphismProperty C}   [W.HasLeftCalculusOfFractions] {X Y : C} (φ : W.R
ightFraction X Y),   ∃ ψ, CategoryTheory.CategoryStruct.comp φ.f ψ.s = CategoryT
heory.CategoryStruct.comp φ.s ψ.f
参数：φ : W.RightFraction X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions.exists_leftFr
action`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : Cate
goryTheory.MorphismProperty C}   [self : W.HasLeftCalculusOfFraction…
-/
lemma RightFraction.exists_leftFraction [W.HasLeftCalculusOfFractions] {X Y : C}
    (φ : W.RightFraction X Y) : ∃ (ψ : W.LeftFraction X Y), φ.f ≫ ψ.s = φ.s ≫ ψ.f :=
  HasLeftCalculusOfFractions.exists_leftFraction φ

/-- A choice of a left fraction deduced from a right fraction for a morphism property `W`
when `W` has left calculus of fractions. -/
/-
**CategoryTheory.MorphismProperty.RightFraction.leftFraction** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.MorphismProperty.RightFraction`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
: CategoryTheory.MorphismProperty C} →       [W.HasLeftCalculusOfFractions] → {X
 Y : C} → W.RightFraction X Y → W.LeftFraction X Y
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.exists_leftFraction`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.Mo
rphismProperty C}   [W.HasLeftCalculusOfFractions] {X Y…

--- 原说明 ---
A choice of a left fraction deduced from a right fraction for a morphism propert
y `W`
when `W` has left calculus of fractions.
-/
noncomputable def RightFraction.leftFraction [W.HasLeftCalculusOfFractions] {X Y : C}
    (φ : W.RightFraction X Y) : W.LeftFraction X Y :=
  φ.exists_leftFraction.choose

@[reassoc]
/-
**CategoryTheory.MorphismProperty.RightFraction.leftFraction_fac** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.MorphismProperty.RightFraction`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Catego
ryTheory.MorphismProperty C}   [inst_1 : W.HasLeftCalculusOfFractions] {X Y : C}
 (φ : W.RightFraction X Y),   CategoryTheory.CategoryStruct.comp φ.f φ.leftFract
ion.s = CategoryTheory.CategoryStruct.comp φ.s φ.leftFraction.f
参数：φ : W.RightFraction X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.exists_leftFraction`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.Mo
rphismProperty C}   [W.HasLeftCalculusOfFractions] {X Y…
-/
lemma RightFraction.leftFraction_fac [W.HasLeftCalculusOfFractions] {X Y : C}
    (φ : W.RightFraction X Y) : φ.f ≫ φ.leftFraction.s = φ.s ≫ φ.leftFraction.f :=
  φ.exists_leftFraction.choose_spec
/-
**CategoryTheory.MorphismProperty.LeftFraction.exists_rightFraction** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Catego
ryTheory.MorphismProperty C}   [W.HasRightCalculusOfFractions] {X Y : C} (φ : W.
LeftFraction X Y),   ∃ ψ, CategoryTheory.CategoryStruct.comp ψ.s φ.f = CategoryT
heory.CategoryStruct.comp ψ.f φ.s
参数：φ : W.LeftFraction X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.HasRightCalculusOfFractions.exists_right
Fraction`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : Ca
tegoryTheory.MorphismProperty C}   [self : W.HasRightCalculusOfFractio…
-/
lemma LeftFraction.exists_rightFraction [W.HasRightCalculusOfFractions] {X Y : C}
    (φ : W.LeftFraction X Y) : ∃ (ψ : W.RightFraction X Y), ψ.s ≫ φ.f = ψ.f ≫ φ.s :=
  HasRightCalculusOfFractions.exists_rightFraction φ

/-- A choice of a right fraction deduced from a left fraction for a morphism property `W`
when `W` has right calculus of fractions. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction.rightFraction** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
: CategoryTheory.MorphismProperty C} →       [W.HasRightCalculusOfFractions] → {
X Y : C} → W.LeftFraction X Y → W.RightFraction X Y
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.exists_rightFraction`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.Mo
rphismProperty C}   [W.HasRightCalculusOfFractions] {X …

--- 原说明 ---
A choice of a right fraction deduced from a left fraction for a morphism propert
y `W`
when `W` has right calculus of fractions.
-/
noncomputable def LeftFraction.rightFraction [W.HasRightCalculusOfFractions] {X Y : C}
    (φ : W.LeftFraction X Y) : W.RightFraction X Y :=
  φ.exists_rightFraction.choose

@[reassoc]
/-
**CategoryTheory.MorphismProperty.LeftFraction.rightFraction_fac** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Catego
ryTheory.MorphismProperty C}   [inst_1 : W.HasRightCalculusOfFractions] {X Y : C
} (φ : W.LeftFraction X Y),   CategoryTheory.CategoryStruct.comp φ.rightFraction
.s φ.f = CategoryTheory.CategoryStruct.comp φ.rightFraction.f φ.s
参数：φ : W.LeftFraction X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.exists_rightFraction`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.Mo
rphismProperty C}   [W.HasRightCalculusOfFractions] {X …
-/
lemma LeftFraction.rightFraction_fac [W.HasRightCalculusOfFractions] {X Y : C}
    (φ : W.LeftFraction X Y) : φ.rightFraction.s ≫ φ.f = φ.rightFraction.f ≫ φ.s :=
  φ.exists_rightFraction.choose_spec

/-- The equivalence relation on left fractions for a morphism property `W`. -/
/-
**CategoryTheory.MorphismProperty.LeftFractionRel** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：LeftFractionRel {X Y : C} (z₁ z₂ : W.LeftFraction X Y) : Prop
参数：z₁ z₂ : W.LeftFraction X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence relation on left fractions for a morphism property `W`.
-/
def LeftFractionRel {X Y : C} (z₁ z₂ : W.LeftFraction X Y) : Prop :=
  ∃ (Z : C) (t₁ : z₁.Y' ⟶ Z) (t₂ : z₂.Y' ⟶ Z) (_ : z₁.s ≫ t₁ = z₂.s ≫ t₂)
    (_ : z₁.f ≫ t₁ = z₂.f ≫ t₂), W (z₁.s ≫ t₁)

namespace LeftFractionRel

/-
**CategoryTheory.MorphismProperty.LeftFractionRel.refl** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MorphismProperty.LeftFractionRel`。
形式化陈述：refl {X Y : C} (z : W.LeftFraction X Y) : LeftFractionRel z z
参数：z : W.LeftFraction X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …
-/
lemma refl {X Y : C} (z : W.LeftFraction X Y) : LeftFractionRel z z :=
  ⟨z.Y', 𝟙 _, 𝟙 _, rfl, rfl, by simpa only [Category.comp_id] using z.hs⟩
/-
**CategoryTheory.MorphismProperty.LeftFractionRel.symm** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MorphismProperty.LeftFractionRel`。
形式化陈述：symm {X Y : C} {z₁ z₂ : W.LeftFraction X Y} (h : LeftFractionRel z₁ z₂) : 
LeftFractionRel z₂ z₁
参数：h : LeftFractionRel z₁ z₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma symm {X Y : C} {z₁ z₂ : W.LeftFraction X Y} (h : LeftFractionRel z₁ z₂) :
    LeftFractionRel z₂ z₁ := by
  obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
  exact ⟨Z, t₂, t₁, hst.symm, hft.symm, by simpa only [← hst] using ht⟩
/-
**CategoryTheory.MorphismProperty.LeftFractionRel.trans** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty.LeftFractionRel`。
形式化陈述：trans {X Y : C} {z₁ z₂ z₃ : W.LeftFraction X Y} [HasLeftCalculusOfFraction
s W] (h₁₂ : LeftFractionRel z₁ z₂) (h₂₃ : LeftFractionRel z₂ z₃) : LeftFractionR
el z₁ z₃
参数：h₁₂ : LeftFractionRel z₁ z₂；h₂₃ : LeftFractionRel z₂ z₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions.exists_leftFr
action`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : Cate
goryTheory.MorphismProperty C}   [self : W.HasLeftCalculusOfFraction…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions.ext`：∀ {C : T
ype u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : CategoryTheory.Morph
ismProperty C}   [self : W.HasLeftCalculusOfFraction…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions.toIsMultiplic
ative`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasLeftCalculusOfFraction…
-/
lemma trans {X Y : C} {z₁ z₂ z₃ : W.LeftFraction X Y}
    [HasLeftCalculusOfFractions W]
    (h₁₂ : LeftFractionRel z₁ z₂) (h₂₃ : LeftFractionRel z₂ z₃) :
    LeftFractionRel z₁ z₃ := by
  obtain ⟨Z₄, t₁, t₂, hst, hft, ht⟩ := h₁₂
  obtain ⟨Z₅, u₂, u₃, hsu, hfu, hu⟩ := h₂₃
  obtain ⟨⟨v₄, v₅, hv₅⟩, fac⟩ := HasLeftCalculusOfFractions.exists_leftFraction
    (RightFraction.mk (z₁.s ≫ t₁) ht (z₃.s ≫ u₃))
  simp only [Category.assoc] at fac
  have eq : z₂.s ≫ u₂ ≫ v₅ = z₂.s ≫ t₂ ≫ v₄ := by
    simpa only [← reassoc_of% hsu, reassoc_of% hst] using fac
  obtain ⟨Z₇, w, hw, fac'⟩ := HasLeftCalculusOfFractions.ext _ _ _ z₂.hs eq
  simp only [Category.assoc] at fac'
  refine ⟨Z₇, t₁ ≫ v₄ ≫ w, u₃ ≫ v₅ ≫ w, ?_, ?_, ?_⟩
  · rw [reassoc_of% fac]
  · rw [reassoc_of% hft, ← fac', reassoc_of% hfu]
  · rw [← reassoc_of% fac, ← reassoc_of% hsu, ← Category.assoc]
    exact W.comp_mem _ _ hu (W.comp_mem _ _ hv₅ hw)

end LeftFractionRel

section

variable (W)

/-
**CategoryTheory.MorphismProperty.equivalenceLeftFractionRel** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：equivalenceLeftFractionRel [W.HasLeftCalculusOfFractions] (X Y : C) : @_ro
ot_.Equivalence (W.LeftFraction X Y) LeftFractionRel where refl
参数：X Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.LeftFractionRel.refl`：refl {X Y : C} (z 
: W.LeftFraction X Y) : LeftFractionRel z z
· 使用引理 `CategoryTheory.MorphismProperty.LeftFractionRel.symm`：symm {X Y : C} {z₁
 z₂ : W.LeftFraction X Y} (h : LeftFractionRel z₁ z₂) : LeftFractionRel z₂ z₁
· 使用引理 `CategoryTheory.MorphismProperty.LeftFractionRel.trans`：trans {X Y : C} {
z₁ z₂ z₃ : W.LeftFraction X Y} [HasLeftCalculusOfFractions W] (h₁₂ : LeftFractio
nRel z₁ z₂) (h₂₃ : LeftFractionRel z₂ z₃) :…
-/
lemma equivalenceLeftFractionRel [W.HasLeftCalculusOfFractions] (X Y : C) :
    @_root_.Equivalence (W.LeftFraction X Y) LeftFractionRel where
  refl := LeftFractionRel.refl
  symm := LeftFractionRel.symm
  trans := LeftFractionRel.trans

variable {W}

namespace LeftFraction

open HasLeftCalculusOfFractions

/-- Auxiliary definition for the composition of left fractions. -/
@[simp]
/-
**CategoryTheory.MorphismProperty.LeftFraction.comp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：comp {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) : Loc
alization.Hom W X Z
参数：z₁ : W.LeftFraction X Y；z₂ : W.LeftFraction Y Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …

--- 原说明 ---
Auxiliary definition for the composition of left fractions.
-/
def comp₀ [W.HasLeftCalculusOfFractions] {X Y Z : C}
    (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) (z₃ : W.LeftFraction z₁.Y' z₂.Y') :
    W.LeftFraction X Z :=
  mk (z₁.f ≫ z₃.f) (z₂.s ≫ z₃.s) (W.comp_mem _ _ z₂.hs z₃.hs)

/-- The equivalence class of `z₁.comp₀ z₂ z₃` does not depend on the choice of `z₃` provided
they satisfy the compatibility `z₂.f ≫ z₃.s = z₁.s ≫ z₃.f`. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction.comp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：comp {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) : Loc
alization.Hom W X Z
参数：z₁ : W.LeftFraction X Y；z₂ : W.LeftFraction Y Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …

--- 原说明 ---
The equivalence class of `z₁.comp₀ z₂ z₃` does not depend on the choice of `z₃` 
provided
they satisfy the compatibility `z₂.f ≫ z₃.s = z₁.s ≫ z₃.f`.
-/
lemma comp₀_rel [W.HasLeftCalculusOfFractions]
    {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
    (z₃ z₃' : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f)
    (h₃' : z₂.f ≫ z₃'.s = z₁.s ≫ z₃'.f) :
    LeftFractionRel (z₁.comp₀ z₂ z₃) (z₁.comp₀ z₂ z₃') := by
  obtain ⟨z₄, fac⟩ := exists_leftFraction (RightFraction.mk z₃.s z₃.hs z₃'.s)
  dsimp at fac
  have eq : z₁.s ≫ z₃.f ≫ z₄.f = z₁.s ≫ z₃'.f ≫ z₄.s := by
    rw [← reassoc_of% h₃, ← reassoc_of% h₃', fac]
  obtain ⟨Y, t, ht, fac'⟩ := HasLeftCalculusOfFractions.ext _ _ _ z₁.hs eq
  simp only [assoc] at fac'
  refine ⟨Y, z₄.f ≫ t, z₄.s ≫ t, ?_, ?_, ?_⟩
  · simp only [comp₀, assoc, reassoc_of% fac]
  · simp only [comp₀, assoc, fac']
  · simp only [comp₀, assoc, ← reassoc_of% fac]
    exact W.comp_mem _ _ z₂.hs (W.comp_mem _ _ z₃'.hs (W.comp_mem _ _ z₄.hs ht))

variable (W) in
/-- The morphisms in the constructed localized category for a morphism property `W`
that has left calculus of fractions are equivalence classes of left fractions. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] → Categor
yTheory.MorphismProperty C → C → C → Type (max u_1 v_1)
参数：max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphisms in the constructed localized category for a morphism property `W`
that has left calculus of fractions are equivalence classes of left fractions.
-/
def Localization.Hom (X Y : C) :=
  Quot (LeftFractionRel : W.LeftFraction X Y → W.LeftFraction X Y → Prop)

/-- The morphism in the constructed localized category that is induced by a left fraction. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.mk** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
: CategoryTheory.MorphismProperty C} →       {X Y : C} → W.LeftFraction X Y → Ca
tegoryTheory.MorphismProperty.LeftFraction.Localization.Hom W X Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism in the constructed localized category that is induced by a left fra
ction.
-/
def Localization.Hom.mk {X Y : C} (z : W.LeftFraction X Y) : Localization.Hom W X Y :=
  Quot.mk _ z
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.mk_surjective** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localizati
on.Hom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Catego
ryTheory.MorphismProperty C} {X Y : C}   (f : CategoryTheory.MorphismProperty.Le
ftFraction.Localization.Hom W X Y),   ∃ z, f = CategoryTheory.MorphismProperty.L
eftFraction.Localization.Hom.mk z
参数：f : CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom W X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Localization.Hom.mk_surjective {X Y : C} (f : Localization.Hom W X Y) :
    ∃ (z : W.LeftFraction X Y), f = mk z := by
  obtain ⟨z⟩ := f
  exact ⟨z, rfl⟩

variable [W.HasLeftCalculusOfFractions]

/-- Auxiliary definition towards the definition of the composition of morphisms
in the constructed localized category for a morphism property that has
left calculus of fractions. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction.comp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：comp {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) : Loc
alization.Hom W X Z
参数：z₁ : W.LeftFraction X Y；z₂ : W.LeftFraction Y Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …

--- 原说明 ---
Auxiliary definition towards the definition of the composition of morphisms
in the constructed localized category for a morphism property that has
left calculus of fractions.
-/
noncomputable def comp
    {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) :
    Localization.Hom W X Z :=
  Localization.Hom.mk (z₁.comp₀ z₂ (RightFraction.mk z₁.s z₁.hs z₂.f).leftFraction)
/-
**CategoryTheory.MorphismProperty.LeftFraction.comp_eq** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：comp_eq {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) (z
₃ : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f) : z₁.comp z₂ = 
Localization.Hom.mk (z₁.comp₀ z₂ z₃)
参数：z₁ : W.LeftFraction X Y；z₂ : W.LeftFraction Y Z；z₃ : W.LeftFraction z₁.Y' z₂.
Y'；h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.comp₀_rel`：comp₀_rel [W.Has
LeftCalculusOfFractions] {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFract
ion Y Z) (z₃ z₃' : W.LeftFraction z₁.Y' z₂.Y…
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.leftFraction_fac`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.Morph
ismProperty C}   [inst_1 : W.HasLeftCalculusOfFracti…
-/
lemma comp_eq {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
    (z₃ : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f) :
    z₁.comp z₂ = Localization.Hom.mk (z₁.comp₀ z₂ z₃) :=
  Quot.sound (LeftFraction.comp₀_rel _ _ _ _
    (RightFraction.leftFraction_fac (RightFraction.mk z₁.s z₁.hs z₂.f)) h₃)

namespace Localization

/-- Composition of morphisms in the constructed localized category
for a morphism property that has left calculus of fractions. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.comp** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
: CategoryTheory.MorphismProperty C} →       [W.HasLeftCalculusOfFractions] →   
      {X Y Z : C} →           CategoryTheory.MorphismProperty.LeftFraction.Local
ization.Hom W X Y →             CategoryTheory.MorphismProperty.LeftFraction.Loc
alization.Hom W Y Z →               CategoryTheory.MorphismProperty.LeftFraction
.Localization.Hom W X Z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms in the constructed localized category
for a morphism property that has left calculus of fractions.
-/
noncomputable def Hom.comp {X Y Z : C} (z₁ : Hom W X Y) (z₂ : Hom W Y Z) : Hom W X Z := by
  refine Quot.lift₂ (fun a b => a.comp b) ?_ ?_ z₁ z₂
  · rintro a b₁ b₂ ⟨U, t₁, t₂, hst, hft, ht⟩
    obtain ⟨z₁, fac₁⟩ := exists_leftFraction (RightFraction.mk a.s a.hs b₁.f)
    obtain ⟨z₂, fac₂⟩ := exists_leftFraction (RightFraction.mk a.s a.hs b₂.f)
    obtain ⟨w₁, fac₁'⟩ := exists_leftFraction (RightFraction.mk z₁.s z₁.hs t₁)
    obtain ⟨w₂, fac₂'⟩ := exists_leftFraction (RightFraction.mk z₂.s z₂.hs t₂)
    obtain ⟨u, fac₃⟩ := exists_leftFraction (RightFraction.mk w₁.s w₁.hs w₂.s)
    dsimp at fac₁ fac₂ fac₁' fac₂' fac₃ ⊢
    have eq : a.s ≫ z₁.f ≫ w₁.f ≫ u.f = a.s ≫ z₂.f ≫ w₂.f ≫ u.s := by
      rw [← reassoc_of% fac₁, ← reassoc_of% fac₂, ← reassoc_of% fac₁', ← reassoc_of% fac₂',
        reassoc_of% hft, fac₃]
    obtain ⟨Z, p, hp, fac₄⟩ := HasLeftCalculusOfFractions.ext _ _ _ a.hs eq
    simp only [assoc] at fac₄
    rw [comp_eq _ _ z₁ fac₁, comp_eq _ _ z₂ fac₂]
    apply Quot.sound
    refine ⟨Z, w₁.f ≫ u.f ≫ p, w₂.f ≫ u.s ≫ p, ?_, ?_, ?_⟩
    · dsimp
      simp only [assoc, ← reassoc_of% fac₁', ← reassoc_of% fac₂',
        reassoc_of% hst, reassoc_of% fac₃]
    · dsimp
      simp only [assoc, fac₄]
    · dsimp
      simp only [assoc]
      rw [← reassoc_of% fac₁', ← reassoc_of% fac₃, ← assoc]
      exact W.comp_mem _ _ ht (W.comp_mem _ _ w₂.hs (W.comp_mem _ _ u.hs hp))
  · rintro a₁ a₂ b ⟨U, t₁, t₂, hst, hft, ht⟩
    obtain ⟨z₁, fac₁⟩ := exists_leftFraction (RightFraction.mk a₁.s a₁.hs b.f)
    obtain ⟨z₂, fac₂⟩ := exists_leftFraction (RightFraction.mk a₂.s a₂.hs b.f)
    obtain ⟨w₁, fac₁'⟩ := exists_leftFraction (RightFraction.mk (a₁.s ≫ t₁) ht (b.f ≫ z₁.s))
    obtain ⟨w₂, fac₂'⟩ := exists_leftFraction (RightFraction.mk (a₂.s ≫ t₂)
      (show W _ by rw [← hst]; exact ht) (b.f ≫ z₂.s))
    let p₁ : W.LeftFraction X Z := LeftFraction.mk (a₁.f ≫ t₁ ≫ w₁.f) (b.s ≫ z₁.s ≫ w₁.s)
      (W.comp_mem _ _ b.hs (W.comp_mem _ _ z₁.hs w₁.hs))
    let p₂ : W.LeftFraction X Z := LeftFraction.mk (a₂.f ≫ t₂ ≫ w₂.f) (b.s ≫ z₂.s ≫ w₂.s)
      (W.comp_mem _ _ b.hs (W.comp_mem _ _ z₂.hs w₂.hs))
    dsimp at fac₁ fac₂ fac₁' fac₂' ⊢
    simp only [assoc] at fac₁' fac₂'
    rw [comp_eq _ _ z₁ fac₁, comp_eq _ _ z₂ fac₂]
    apply Quot.sound
    refine LeftFractionRel.trans ?_ ((?_ : LeftFractionRel p₁ p₂).trans ?_)
    · have eq : a₁.s ≫ z₁.f ≫ w₁.s = a₁.s ≫ t₁ ≫ w₁.f := by rw [← fac₁', reassoc_of% fac₁]
      obtain ⟨Z, u, hu, fac₃⟩ := HasLeftCalculusOfFractions.ext _ _ _ a₁.hs eq
      simp only [assoc] at fac₃
      refine ⟨Z, w₁.s ≫ u, u, ?_, ?_, ?_⟩
      · dsimp [p₁]
        simp only [assoc]
      · dsimp [p₁]
        simp only [assoc, fac₃]
      · dsimp
        simp only [assoc]
        exact W.comp_mem _ _ b.hs (W.comp_mem _ _ z₁.hs (W.comp_mem _ _ w₁.hs hu))
    · obtain ⟨q, fac₃⟩ := exists_leftFraction (RightFraction.mk (z₁.s ≫ w₁.s)
        (W.comp_mem _ _ z₁.hs w₁.hs) (z₂.s ≫ w₂.s))
      dsimp at fac₃
      simp only [assoc] at fac₃
      have eq : a₁.s ≫ t₁ ≫ w₁.f ≫ q.f = a₁.s ≫ t₁ ≫ w₂.f ≫ q.s := by
        rw [← reassoc_of% fac₁', ← fac₃, reassoc_of% hst, reassoc_of% fac₂']
      obtain ⟨Z, u, hu, fac₄⟩ := HasLeftCalculusOfFractions.ext _ _ _ a₁.hs eq
      simp only [assoc] at fac₄
      refine ⟨Z, q.f ≫ u, q.s ≫ u, ?_, ?_, ?_⟩
      · simp only [p₁, p₂, assoc, reassoc_of% fac₃]
      · rw [assoc, assoc, assoc, assoc, fac₄, reassoc_of% hft]
      · simp only [p₁, assoc, ← reassoc_of% fac₃]
        exact W.comp_mem _ _ b.hs (W.comp_mem _ _ z₂.hs
          (W.comp_mem _ _ w₂.hs (W.comp_mem _ _ q.hs hu)))
    · have eq : a₂.s ≫ z₂.f ≫ w₂.s = a₂.s ≫ t₂ ≫ w₂.f := by
        rw [← fac₂', reassoc_of% fac₂]
      obtain ⟨Z, u, hu, fac₄⟩ := HasLeftCalculusOfFractions.ext _ _ _ a₂.hs eq
      simp only [assoc] at fac₄
      refine ⟨Z, u, w₂.s ≫ u, ?_, ?_, ?_⟩
      · dsimp [p₁, p₂]
        simp only [assoc]
      · dsimp [p₁, p₂]
        simp only [assoc, fac₄]
      · dsimp [p₁, p₂]
        simp only [assoc]
        exact W.comp_mem _ _ b.hs (W.comp_mem _ _ z₂.hs (W.comp_mem _ _ w₂.hs hu))
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.comp_eq** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom
`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Catego
ryTheory.MorphismProperty C}   [inst_1 : W.HasLeftCalculusOfFractions] {X Y Z : 
C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z),   (CategoryTheory.Morphi
smProperty.LeftFraction.Localization.Hom.mk z₁).comp       (CategoryTheory.Morph
ismProperty.LeftFraction.Localization.Hom.mk z₂) =     z₁.comp z₂
参数：z₁ : W.LeftFraction X Y；z₂ : W.LeftFraction Y Z；CategoryTheory.MorphismProper
ty.LeftFraction.Localization.Hom.mk z₁；CategoryTheory.MorphismProperty.LeftFract
ion.Localization.Hom.mk z₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.comp_eq {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) :
    Hom.comp (mk z₁) (mk z₂) = z₁.comp z₂ := rfl

end Localization

/-- The constructed localized category for a morphism property
that has left calculus of fractions. -/
@[nolint unusedArguments]
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：Localization (_ : MorphismProperty C)
参数：_ : MorphismProperty C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructed localized category for a morphism property
that has left calculus of fractions.
-/
def Localization (_ : MorphismProperty C) := C

namespace Localization

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Category (Localization W) where
  Hom X Y := Localization.Hom W X Y
  id _ := Localization.Hom.mk (ofHom W (𝟙 _))
  comp f g := f.comp g
  comp_id := by
    rintro (X Y : C) f
    obtain ⟨z, rfl⟩ := Hom.mk_surjective f
    rw [Hom.comp_eq, comp_eq z (ofHom W (𝟙 Y)) (ofInv z.s z.hs) (by simp)]
    dsimp [comp₀]
    simp only [comp_id, id_comp]
  id_comp := by
    rintro (X Y : C) f
    obtain ⟨z, rfl⟩ := Hom.mk_surjective f
    rw [Hom.comp_eq, comp_eq (ofHom W (𝟙 X)) z (ofHom W z.f) (by simp)]
    dsimp
    simp only [id_comp, comp_id]
  assoc := by
    rintro (X₁ X₂ X₃ X₄ : C) f₁ f₂ f₃
    obtain ⟨z₁, rfl⟩ := Hom.mk_surjective f₁
    obtain ⟨z₂, rfl⟩ := Hom.mk_surjective f₂
    obtain ⟨z₃, rfl⟩ := Hom.mk_surjective f₃
    rw [Hom.comp_eq z₁ z₂, Hom.comp_eq z₂ z₃]
    obtain ⟨z₁₂, fac₁₂⟩ := exists_leftFraction (RightFraction.mk z₁.s z₁.hs z₂.f)
    obtain ⟨z₂₃, fac₂₃⟩ := exists_leftFraction (RightFraction.mk z₂.s z₂.hs z₃.f)
    obtain ⟨z', fac⟩ := exists_leftFraction (RightFraction.mk z₁₂.s z₁₂.hs z₂₃.f)
    dsimp at fac₁₂ fac₂₃ fac
    rw [comp_eq z₁ z₂ z₁₂ fac₁₂, comp_eq z₂ z₃ z₂₃ fac₂₃, comp₀, comp₀,
      Hom.comp_eq, Hom.comp_eq,
      comp_eq _ z₃ (mk z'.f (z₂₃.s ≫ z'.s) (W.comp_mem _ _ z₂₃.hs z'.hs))
        (by dsimp; rw [assoc, reassoc_of% fac₂₃, fac]),
      comp_eq z₁ _ (mk (z₁₂.f ≫ z'.f) z'.s z'.hs)
        (by dsimp; rw [assoc, ← reassoc_of% fac₁₂, fac])]
    simp

set_option backward.defeqAttrib.useBackward true in
variable (W) in
/-- The localization functor to the constructed localized category for a morphism property
that has left calculus of fractions. -/
@[simps obj]
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.Q** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization`。
形式化陈述：Q : C ⥤ Localization W where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization functor to the constructed localized category for a morphism pr
operty
that has left calculus of fractions.
-/
noncomputable def Q : C ⥤ Localization W where
  obj X := X
  map f := Hom.mk (ofHom W f)
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    change _ = Hom.comp _ _
    rw [Hom.comp_eq, comp_eq (ofHom W f) (ofHom W g) (ofHom W g) (by simp)]
    simp only [ofHom, comp₀, comp_id]

/-- The morphism on `Localization W` that is induced by a left fraction. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk** 是 Mathlib 中的
一个缩写定义，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization`。
形式化陈述：homMk {X Y : C} (f : W.LeftFraction X Y) : (Q W).obj X ⟶ (Q W).obj Y
参数：f : W.LeftFraction X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism on `Localization W` that is induced by a left fraction.
-/
noncomputable abbrev homMk {X Y : C} (f : W.LeftFraction X Y) : (Q W).obj X ⟶ (Q W).obj Y :=
  Hom.mk f
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_eq_hom_mk** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization
`。
形式化陈述：homMk_eq_hom_mk {X Y : C} (f : W.LeftFraction X Y) : homMk f = Hom.mk f
参数：f : W.LeftFraction X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_eq_hom_mk {X Y : C} (f : W.LeftFraction X Y) : homMk f = Hom.mk f := rfl

variable (W)
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.Q_map** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization`。
形式化陈述：Q_map {X Y : C} (f : X ⟶ Y) : (Q W).map f = homMk (ofHom W f)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Q_map {X Y : C} (f : X ⟶ Y) : (Q W).map f = homMk (ofHom W f) := rfl

variable {W}

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_comp_homMk** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localizatio
n`。
形式化陈述：homMk_comp_homMk {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFractio
n Y Z) (z₃ : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f) : homM
k z₁ ≫ homMk z₂ = homMk (z₁.comp₀ z₂ z₃)
参数：z₁ : W.LeftFraction X Y；z₂ : W.LeftFraction Y Z；z₃ : W.LeftFraction z₁.Y' z₂.
Y'；h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.comp_eq`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheor
y.MorphismProperty C}   [inst_1 : W.HasLeftCalculusOfFracti…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.comp_eq`：comp_eq {X Y Z : C
} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) (z₃ : W.LeftFraction z₁.Y'
 z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f) :…
-/
lemma homMk_comp_homMk {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
    (z₃ : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f) :
    homMk z₁ ≫ homMk z₂ = homMk (z₁.comp₀ z₂ z₃) := by
  change Hom.comp _ _ = _
  rw [Hom.comp_eq, comp_eq z₁ z₂ z₃ h₃]
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_eq_of_leftFrac
tionRel** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.
Localization`。
形式化陈述：homMk_eq_of_leftFractionRel {X Y : C} (z₁ z₂ : W.LeftFraction X Y) (h : Le
ftFractionRel z₁ z₂) : homMk z₁ = homMk z₂
参数：z₁ z₂ : W.LeftFraction X Y；h : LeftFractionRel z₁ z₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_eq_of_leftFractionRel {X Y : C} (z₁ z₂ : W.LeftFraction X Y)
    (h : LeftFractionRel z₁ z₂) :
    homMk z₁ = homMk z₂ :=
  Quot.sound h
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_eq_iff_leftFra
ctionRel** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction
.Localization`。
形式化陈述：homMk_eq_iff_leftFractionRel {X Y : C} (z₁ z₂ : W.LeftFraction X Y) : homM
k z₁ = homMk z₂ ↔ LeftFractionRel z₁ z₂
参数：z₁ z₂ : W.LeftFraction X Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equivalence.quot_mk_eq_iff`：Equivalence.quot_mk_eq_iff {α : Type*} {r : 
α -> α -> Prop} (h : Equivalence r) (x y : α) : Quot.mk r x = Quot.mk r y ↔ r x 
y
· 使用引理 `CategoryTheory.MorphismProperty.equivalenceLeftFractionRel`：equivalenceL
eftFractionRel [W.HasLeftCalculusOfFractions] (X Y : C) : @_root_.Equivalence (W
.LeftFraction X Y) LeftFractionRel where refl
-/
lemma homMk_eq_iff_leftFractionRel {X Y : C} (z₁ z₂ : W.LeftFraction X Y) :
    homMk z₁ = homMk z₂ ↔ LeftFractionRel z₁ z₂ :=
  @Equivalence.quot_mk_eq_iff _ _ (equivalenceLeftFractionRel W X Y) _ _

/-- The morphism in `Localization W` that is the formal inverse of a morphism
which belongs to `W`. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.Qinv** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization`。
形式化陈述：Qinv {X Y : C} (s : X ⟶ Y) (hs : W s) : (Q W).obj Y ⟶ (Q W).obj X
参数：s : X ⟶ Y；hs : W s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism in `Localization W` that is the formal inverse of a morphism
which belongs to `W`.
-/
noncomputable def Qinv {X Y : C} (s : X ⟶ Y) (hs : W s) : (Q W).obj Y ⟶ (Q W).obj X :=
  homMk (ofInv s hs)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.Q_map_comp_Qinv** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization
`。
形式化陈述：Q_map_comp_Qinv {X Y Y' : C} (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) : (Q W).
map f ≫ Qinv s hs = homMk (mk f s hs)
参数：f : X ⟶ Y'；s : Y ⟶ Y'；hs : W s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions.toIsMultiplic
ative`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasLeftCalculusOfFraction…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_comp_hom
Mk`：homMk_comp_homMk {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction 
Y Z) (z₃ : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.mk.congr_simp`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismP
roperty C} {X Y Y' : C}   (f f_1 : X ⟶ Y'),   f …
-/
lemma Q_map_comp_Qinv {X Y Y' : C} (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (Q W).map f ≫ Qinv s hs = homMk (mk f s hs) := by
  dsimp only [Q_map, Qinv]
  rw [homMk_comp_homMk (ofHom W f) (ofInv s hs) (ofHom W (𝟙 _)) (by simp)]
  simp

set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism in `Localization W` that is induced by a morphism in `W`. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.Qiso** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization`。
形式化陈述：Qiso {X Y : C} (s : X ⟶ Y) (hs : W s) : (Q W).obj X ≅ (Q W).obj Y where ho
m
参数：s : X ⟶ Y；hs : W s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism in `Localization W` that is induced by a morphism in `W`.
-/
noncomputable def Qiso {X Y : C} (s : X ⟶ Y) (hs : W s) : (Q W).obj X ≅ (Q W).obj Y where
  hom := (Q W).map s
  inv := Qinv s hs
  hom_inv_id := by
    rw [Q_map_comp_Qinv]
    apply homMk_eq_of_leftFractionRel
    exact ⟨_, 𝟙 Y, s, by simp, by simp, by simpa using hs⟩
  inv_hom_id := by
    dsimp only [Qinv, Q_map]
    rw [homMk_comp_homMk (ofInv s hs) (ofHom W s) (ofHom W (𝟙 Y)) (by simp)]
    apply homMk_eq_of_leftFractionRel
    exact ⟨_, 𝟙 Y, 𝟙 Y, by simp, by simp, by simpa using W.id_mem Y⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.Qiso_hom_inv_id** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization
`。
形式化陈述：Qiso_hom_inv_id {X Y : C} (s : X ⟶ Y) (hs : W s) : (Q W).map s ≫ Qinv s hs
 = 𝟙 _
参数：s : X ⟶ Y；hs : W s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma Qiso_hom_inv_id {X Y : C} (s : X ⟶ Y) (hs : W s) :
    (Q W).map s ≫ Qinv s hs = 𝟙 _ := (Qiso s hs).hom_inv_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.Qiso_inv_hom_id** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization
`。
形式化陈述：Qiso_inv_hom_id {X Y : C} (s : X ⟶ Y) (hs : W s) : Qinv s hs ≫ (Q W).map s
 = 𝟙 _
参数：s : X ⟶ Y；hs : W s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma Qiso_inv_hom_id {X Y : C} (s : X ⟶ Y) (hs : W s) :
    Qinv s hs ≫ (Q W).map s = 𝟙 _ := (Qiso s hs).inv_hom_id
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (s : X ⟶ Y) (hs : W s) : IsIso (Qinv s hs) :=
  inferInstanceAs <| IsIso (Qiso s hs).inv

section

variable {E : Type*} [Category* E]

/-- The image by a functor which inverts `W` of an equivalence class of left fractions. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.map** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
: CategoryTheory.MorphismProperty C} →       {E : Type u_3} →         [inst_1 : 
CategoryTheory.Category.{v_3, u_3} E] →           {X Y : C} →             Catego
ryTheory.MorphismProperty.LeftFraction.Localization.Hom W X Y →               (F
 : CategoryTheory.Functor C E) → W.IsInvertedBy F → (F.obj X ⟶ F.obj Y)
参数：F : CategoryTheory.Functor C E；F.obj X ⟶ F.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image by a functor which inverts `W` of an equivalence class of left fractio
ns.
-/
noncomputable def Hom.map {X Y : C} (f : Hom W X Y) (F : C ⥤ E) (hF : W.IsInvertedBy F) :
    F.obj X ⟶ F.obj Y :=
  Quot.lift (fun f => f.map F hF) (by
    intro a₁ a₂ ⟨Z, t₁, t₂, hst, hft, h⟩
    have := hF _ h
    rw [← cancel_mono (F.map (a₁.s ≫ t₁)), F.map_comp, map_comp_map_s_assoc,
      ← F.map_comp, ← F.map_comp, hst, hft, F.map_comp,
      F.map_comp, map_comp_map_s_assoc]) f

@[simp]
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.map_mk** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom`
。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {E : Type u
_3}   [inst_1 : CategoryTheory.Category.{v_3, u_3} E] {W : CategoryTheory.Morphi
smProperty C} {X Y : C}   (f : W.LeftFraction X Y) (F : CategoryTheory.Functor C
 E) (hF : W.IsInvertedBy F),   (CategoryTheory.MorphismProperty.LeftFraction.Loc
alization.Hom.mk f).map F hF = f.map F hF
参数：f : W.LeftFraction X Y；F : CategoryTheory.Functor C E；hF : W.IsInvertedBy F；C
ategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.mk f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.map_mk {W} {X Y : C} (f : LeftFraction W X Y) (F : C ⥤ E) (hF : W.IsInvertedBy F) :
    Hom.map (Hom.mk f) F hF = f.map F hF := rfl

namespace StrictUniversalPropertyFixedTarget

variable (W)

/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.StrictUniversalPrope
rtyFixedTarget.inverts** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismPropert
y.LeftFraction.Localization.StrictUniversalPropertyFixedTarget`。
形式化陈述：inverts : W.IsInvertedBy (Q W)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverts : W.IsInvertedBy (Q W) := fun _ _ s hs =>
  inferInstanceAs <| IsIso (Qiso s hs).hom

variable {W}

set_option backward.isDefEq.respectTransparency false in
/-- The functor `Localization W ⥤ E` that is induced by a functor `C ⥤ E` which inverts `W`,
when `W` has a left calculus of fractions. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.StrictUniversalPrope
rtyFixedTarget.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.L
eftFraction.Localization.StrictUniversalPropertyFixedTarget`。
形式化陈述：lift (F : C ⥤ E) (hF : W.IsInvertedBy F) : Localization W ⥤ E where obj X
参数：F : C ⥤ E；hF : W.IsInvertedBy F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Localization W ⥤ E` that is induced by a functor `C ⥤ E` which inve
rts `W`,
when `W` has a left calculus of fractions.
-/
noncomputable def lift (F : C ⥤ E) (hF : W.IsInvertedBy F) :
    Localization W ⥤ E where
  obj X := F.obj X
  map {_ _ : C} f := f.map F hF
  map_id := by
    intro (X : C)
    change (Hom.mk (ofHom W (𝟙 X))).map F hF = _
    rw [Hom.map_mk, map_ofHom, F.map_id]
  map_comp := by
    rintro (X Y Z : C) f g
    obtain ⟨f, rfl⟩ := Hom.mk_surjective f
    obtain ⟨g, rfl⟩ := Hom.mk_surjective g
    dsimp
    obtain ⟨z, fac⟩ := HasLeftCalculusOfFractions.exists_leftFraction
      (RightFraction.mk f.s f.hs g.f)
    rw [homMk_comp_homMk f g z fac, Hom.map_mk]
    dsimp at fac ⊢
    have := hF _ g.hs
    have := hF _ z.hs
    rw [← cancel_mono (F.map g.s), assoc, map_comp_map_s,
      ← cancel_mono (F.map z.s), assoc, assoc, ← F.map_comp,
      ← F.map_comp, map_comp_map_s, fac]
    dsimp
    rw [F.map_comp, F.map_comp, map_comp_map_s_assoc]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.StrictUniversalPrope
rtyFixedTarget.fac** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.Le
ftFraction.Localization.StrictUniversalPropertyFixedTarget`。
形式化陈述：fac (F : C ⥤ E) (hF : W.IsInvertedBy F) : Q W ⋙ lift F hF = F
参数：F : C ⥤ E；hF : W.IsInvertedBy F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions.toIsMultiplic
ative`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasLeftCalculusOfFraction…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Q_map`：Q_map {
X Y : C} (f : X ⟶ Y) : (Q W).map f = homMk (ofHom W f)
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.map_mk`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {E : Type u_3}   [i
nst_1 : CategoryTheory.Category.{v_3, u_3} E] {W : Categor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_ofHom`：map_ofHom (f : X
 ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities] : (ofHom W f).m
ap L hL = L.map f
-/
lemma fac (F : C ⥤ E) (hF : W.IsInvertedBy F) : Q W ⋙ lift F hF = F :=
  Functor.ext (fun _ => rfl) (fun X Y f => by
    dsimp [lift]
    rw [Q_map, Hom.map_mk, id_comp, comp_id, map_ofHom])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.StrictUniversalPrope
rtyFixedTarget.uniq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.L
eftFraction.Localization.StrictUniversalPropertyFixedTarget`。
形式化陈述：uniq (F₁ F₂ : Localization W ⥤ E) (h : Q W ⋙ F₁ = Q W ⋙ F₂) : F₁ = F₂
参数：F₁ F₂ : Localization W ⥤ E；h : Q W ⋙ F₁ = Q W ⋙ F₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.mk_surject
ive`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Categor
yTheory.MorphismProperty C} {X Y : C}   (f : CategoryTheory.Morph…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Q_map_comp_Qin
v`：Q_map_comp_Qinv {X Y Y' : C} (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) : (Q W).map
 f ≫ Qinv s hs = homMk (mk f s hs)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.congr_hom`：congr_hom {F G : C ⥤ D} (h : F = G) {X
 Y} (f : X ⟶ Y) : F.map f = eqToHom (congr_obj h X) ≫ G.map f ≫ eqToHom (congr_o
bj h Y).symm
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.StrictUniversa
lPropertyFixedTarget.inverts`：inverts : W.IsInvertedBy (Q W)
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.instIsSplitEpiMap`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   {X Y : C} (f : X ⟶…
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Qiso_hom_inv_i
d`：Qiso_hom_inv_id {X Y : C} (s : X ⟶ Y) (hs : W s) : (Q W).map s ≫ Qinv s hs = 
𝟙 _
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma uniq (F₁ F₂ : Localization W ⥤ E) (h : Q W ⋙ F₁ = Q W ⋙ F₂) : F₁ = F₂ :=
  Functor.ext (fun X => Functor.congr_obj h X) (by
    rintro (X Y : C) f
    obtain ⟨f, rfl⟩ := Hom.mk_surjective f
    rw [show Hom.mk f = homMk (mk f.f f.s f.hs) by rfl,
      ← Q_map_comp_Qinv f.f f.s f.hs, F₁.map_comp, F₂.map_comp, assoc]
    erw [Functor.congr_hom h f.f]
    rw [assoc, assoc]
    congr 2
    have := inverts W _ f.hs
    rw [← cancel_epi (F₂.map ((Q W).map f.s)), ← F₂.map_comp_assoc,
      Qiso_hom_inv_id, Functor.map_id, id_comp]
    erw [Functor.congr_hom h.symm f.s]
    dsimp
    rw [assoc, assoc, eqToHom_trans_assoc, eqToHom_refl, id_comp, ← F₁.map_comp,
      Qiso_hom_inv_id]
    dsimp
    rw [F₁.map_id, comp_id])

end StrictUniversalPropertyFixedTarget

variable (W)

open StrictUniversalPropertyFixedTarget in
/-- The universal property of the localization for the constructed localized category
when there is a left calculus of fractions. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.strictUniversalPrope
rtyFixedTarget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.LeftFr
action.Localization`。
形式化陈述：strictUniversalPropertyFixedTarget (E : Type*) [Category* E] : Localizatio
n.StrictUniversalPropertyFixedTarget (Q W) W E where inverts
参数：E : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.StrictUniversa
lPropertyFixedTarget.inverts`：inverts : W.IsInvertedBy (Q W)
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.StrictUniversa
lPropertyFixedTarget.fac`：fac (F : C ⥤ E) (hF : W.IsInvertedBy F) : Q W ⋙ lift F
 hF = F
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.StrictUniversa
lPropertyFixedTarget.uniq`：uniq (F₁ F₂ : Localization W ⥤ E) (h : Q W ⋙ F₁ = Q W
 ⋙ F₂) : F₁ = F₂

--- 原说明 ---
The universal property of the localization for the constructed localized categor
y
when there is a left calculus of fractions.
-/
noncomputable def strictUniversalPropertyFixedTarget (E : Type*) [Category* E] :
    Localization.StrictUniversalPropertyFixedTarget (Q W) W E where
  inverts := inverts W
  lift := lift
  fac := fac
  uniq := uniq
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Q W).IsLocalization W :=
  Functor.IsLocalization.mk' _ _
    (strictUniversalPropertyFixedTarget W _)
    (strictUniversalPropertyFixedTarget W _)

end

/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_eq** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization`。
形式化陈述：homMk_eq {X Y : C} (f : LeftFraction W X Y) : homMk f = f.map (Q W) (Local
ization.inverts _ W)
参数：f : LeftFraction W X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.instIsLocaliza
tionQ`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (W : Categ
oryTheory.MorphismProperty C)   [inst_1 : W.HasLeftCalculusOfFracti…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Q_map_comp_Qin
v`：Q_map_comp_Qinv {X Y Y' : C} (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) : (Q W).map
 f ≫ Qinv s hs = homMk (mk f s hs)
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.instIsIsoMapSOfIsLocalizati
on`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C
]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {W : Categor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Qiso_inv_hom_i
d`：Qiso_inv_hom_id {X Y : C} (s : X ⟶ Y) (hs : W s) : Qinv s hs ≫ (Q W).map s = 
𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s`：map_comp_ma
p_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : φ.map L hL ≫ 
L.map φ.s = L.map φ.f
-/
lemma homMk_eq {X Y : C} (f : LeftFraction W X Y) :
    homMk f = f.map (Q W) (Localization.inverts _ W) := by
  rw [← Q_map_comp_Qinv f.f f.s f.hs, ← cancel_mono ((Q W).map f.s),
    assoc, Qiso_inv_hom_id, comp_id, map_comp_map_s]
/-
**CategoryTheory.MorphismProperty.LeftFraction.Localization.map_eq_iff** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction.Localization`。
形式化陈述：map_eq_iff {X Y : C} (f g : LeftFraction W X Y) : f.map (LeftFraction.Loca
lization.Q W) (Localization.inverts _ _) = g.map (LeftFraction.Localization.Q W)
 (Localization.inverts _ _) ↔ LeftFractionRel f g
参数：f g : LeftFraction W X Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.instIsLocaliza
tionQ`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (W : Categ
oryTheory.MorphismProperty C)   [inst_1 : W.HasLeftCalculusOfFracti…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.map_mk`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {E : Type u_3}   [i
nst_1 : CategoryTheory.Category.{v_3, u_3} E] {W : Categor…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_eq_iff_l
eftFractionRel`：homMk_eq_iff_leftFractionRel {X Y : C} (z₁ z₂ : W.LeftFraction X
 Y) : homMk z₁ = homMk z₂ ↔ LeftFractionRel z₁ z₂
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_eq`：homM
k_eq {X Y : C} (f : LeftFraction W X Y) : homMk f = f.map (Q W) (Localization.in
verts _ W)
-/
lemma map_eq_iff {X Y : C} (f g : LeftFraction W X Y) :
    f.map (LeftFraction.Localization.Q W) (Localization.inverts _ _) =
        g.map (LeftFraction.Localization.Q W) (Localization.inverts _ _) ↔
      LeftFractionRel f g := by
  simp only [← Hom.map_mk _ (Q W)]
  constructor
  · intro h
    rw [← homMk_eq_iff_leftFractionRel, homMk_eq, homMk_eq]
    exact h
  · intro h
    congr 1
    exact Quot.sound h

end Localization

section

/-
**CategoryTheory.MorphismProperty.LeftFraction.map_eq** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：map_eq {W} {X Y : C} (φ : W.LeftFraction X Y) (L : C ⥤ D) [L.IsLocalizatio
n W] : φ.map L (Localization.inverts L W) = L.map φ.f ≫ (Localization.isoOfHom L
 W φ.s φ.hs).inv
参数：φ : W.LeftFraction X Y；L : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
-/
lemma map_eq {W} {X Y : C} (φ : W.LeftFraction X Y) (L : C ⥤ D) [L.IsLocalization W] :
    φ.map L (Localization.inverts L W) =
      L.map φ.f ≫ (Localization.isoOfHom L W φ.s φ.hs).inv := rfl
/-
**CategoryTheory.MorphismProperty.LeftFraction.map_compatibility** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：map_compatibility {W} {X Y : C} (φ : W.LeftFraction X Y) {E : Type*} [Cate
gory* E] (L₁ : C ⥤ D) (L₂ : C ⥤ E) [L₁.IsLocalization W] [L₂.IsLocalization W] :
 (Localization.uniq L₁ L₂ W).functor.map (φ.map L₁ (Localization.inverts L₁ W)) 
= (Localization.compUniqFunctor L₁ L₂ W).hom.app X ≫ φ.map L₂ (Localization.inve
rts L₂ W) ≫ (Localization.compUniqFunctor L₁ L₂ W).inv.app Y
参数：φ : W.LeftFraction X Y；L₁ : C ⥤ D；L₂ : C ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.instIsIsoMapSOfIsLocalizati
on`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C
]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {W : Categor…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s`：map_comp_ma
p_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : φ.map L hL ≫ 
L.map φ.s = L.map φ.f
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma map_compatibility {W} {X Y : C}
    (φ : W.LeftFraction X Y) {E : Type*} [Category* E]
    (L₁ : C ⥤ D) (L₂ : C ⥤ E) [L₁.IsLocalization W] [L₂.IsLocalization W] :
    (Localization.uniq L₁ L₂ W).functor.map (φ.map L₁ (Localization.inverts L₁ W)) =
      (Localization.compUniqFunctor L₁ L₂ W).hom.app X ≫
        φ.map L₂ (Localization.inverts L₂ W) ≫
        (Localization.compUniqFunctor L₁ L₂ W).inv.app Y := by
  let e := Localization.compUniqFunctor L₁ L₂ W
  rw [← cancel_mono (e.hom.app Y), assoc, assoc, e.inv_hom_id_app, comp_id,
    ← cancel_mono (L₂.map φ.s), assoc, assoc, map_comp_map_s, ← e.hom.naturality]
  simpa [← Functor.map_comp_assoc, map_comp_map_s] using e.hom.naturality φ.f
/-
**CategoryTheory.MorphismProperty.LeftFraction.map_eq_of_map_eq** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：map_eq_of_map_eq {W} {X Y : C} (φ₁ φ₂ : W.LeftFraction X Y) {E : Type*} [C
ategory* E] (L₁ : C ⥤ D) (L₂ : C ⥤ E) [L₁.IsLocalization W] [L₂.IsLocalization W
] (h : φ₁.map L₁ (Localization.inverts L₁ W) = φ₂.map L₁ (Localization.inverts L
₁ W)) : φ₁.map L₂ (Localization.inverts L₂ W) = φ₂.map L₂ (Localization.inverts 
L₂ W)
参数：φ₁ φ₂ : W.LeftFraction X Y；L₁ : C ⥤ D；L₂ : C ⥤ E；h : φ₁.map L₁ (Localization.
inverts L₁ W) = φ₂.map L₁ (Localization.inverts L₁ W)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_compatibility`：map_comp
atibility {W} {X Y : C} (φ : W.LeftFraction X Y) {E : Type*} [Category* E] (L₁ :
 C ⥤ D) (L₂ : C ⥤ E) [L₁.IsLocalization W] [L₂.IsLoc…
-/
lemma map_eq_of_map_eq {W} {X Y : C}
    (φ₁ φ₂ : W.LeftFraction X Y) {E : Type*} [Category* E]
    (L₁ : C ⥤ D) (L₂ : C ⥤ E) [L₁.IsLocalization W] [L₂.IsLocalization W]
    (h : φ₁.map L₁ (Localization.inverts L₁ W) = φ₂.map L₁ (Localization.inverts L₁ W)) :
    φ₁.map L₂ (Localization.inverts L₂ W) = φ₂.map L₂ (Localization.inverts L₂ W) := by
  apply (Localization.uniq L₂ L₁ W).functor.map_injective
  rw [map_compatibility φ₁ L₂ L₁, map_compatibility φ₂ L₂ L₁, h]
/-
**CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_eq_map** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：map_comp_map_eq_map {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFrac
tion Y Z) (z₃ : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f) (L 
: C ⥤ D) [L.IsLocalization W] : z₁.map L (Localization.inverts L W) ≫ z₂.map L (
Localization.inverts L W) = (z₁.comp₀ z₂ z₃).map L (Localization.inverts L W)
参数：z₁ : W.LeftFraction X Y；z₂ : W.LeftFraction Y Z；z₃ : W.LeftFraction z₁.Y' z₂.
Y'；h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f；L : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.instIsIsoMapSOfIsLocalizati
on`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C
]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {W : Categor…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s`：map_comp_ma
p_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : φ.map L hL ≫ 
L.map φ.s = L.map φ.f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s_assoc`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] {W : Categor…
-/
lemma map_comp_map_eq_map {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
    (z₃ : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f)
    (L : C ⥤ D) [L.IsLocalization W] :
    z₁.map L (Localization.inverts L W) ≫ z₂.map L (Localization.inverts L W) =
      (z₁.comp₀ z₂ z₃).map L (Localization.inverts L W) := by
  have : IsIso (L.map (z₂.s ≫ z₃.s)) := by
    rw [L.map_comp]
    infer_instance
  dsimp [LeftFraction.comp₀]
  rw [← cancel_mono (L.map (z₂.s ≫ z₃.s)), map_comp_map_s,
    L.map_comp, assoc, map_comp_map_s_assoc, ← L.map_comp, h₃,
    L.map_comp, map_comp_map_s_assoc, L.map_comp]

end

end LeftFraction

end

end MorphismProperty

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

section

variable [W.HasLeftCalculusOfFractions]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Localization.exists_leftFraction** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Localization`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) [inst_2 : L.IsLocalization W] [
W.HasLeftCalculusOfFractions] {X Y : C}   (f : L.obj X ⟶ L.obj Y), ∃ φ, f = φ.ma
p L ⋯
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；f : L.ob
j X ⟶ L.obj Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.instIsLocaliza
tionQ`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (W : Categ
oryTheory.MorphismProperty C)   [inst_1 : W.HasLeftCalculusOfFracti…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.mk_surject
ive`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Categor
yTheory.MorphismProperty C} {X Y : C}   (f : CategoryTheory.Morph…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_eq_hom_m
k`：homMk_eq_hom_mk {X Y : C} (f : W.LeftFraction X Y) : homMk f = Hom.mk f
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_eq`：homM
k_eq {X Y : C} (f : LeftFraction W X Y) : homMk f = f.map (Q W) (Localization.in
verts _ W)
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_compatibility`：map_comp
atibility {W} {X Y : C} (φ : W.LeftFraction X Y) {E : Type*} [Category* E] (L₁ :
 C ⥤ D) (L₂ : C ⥤ E) [L₁.IsLocalization W] [L₂.IsLoc…
-/
lemma Localization.exists_leftFraction {X Y : C} (f : L.obj X ⟶ L.obj Y) :
    ∃ (φ : W.LeftFraction X Y), f = φ.map L (Localization.inverts L W) := by
  let E := Localization.uniq (MorphismProperty.LeftFraction.Localization.Q W) L W
  let e : _ ⋙ E.functor ≅ L := Localization.compUniqFunctor _ _ _
  obtain ⟨f', rfl⟩ : ∃ (f' : E.functor.obj X ⟶ E.functor.obj Y),
      f = e.inv.app _ ≫ f' ≫ e.hom.app _ := ⟨e.hom.app _ ≫ f ≫ e.inv.app _, by simp⟩
  obtain ⟨g, rfl⟩ := E.functor.map_surjective f'
  obtain ⟨g, rfl⟩ := MorphismProperty.LeftFraction.Localization.Hom.mk_surjective g
  refine ⟨g, ?_⟩
  rw [← MorphismProperty.LeftFraction.Localization.homMk_eq_hom_mk,
    MorphismProperty.LeftFraction.Localization.homMk_eq g,
    g.map_compatibility (MorphismProperty.LeftFraction.Localization.Q W) L,
    assoc, assoc, Iso.inv_hom_id_app, comp_id, Iso.inv_hom_id_app_assoc]
/-
**CategoryTheory.MorphismProperty.LeftFraction.map_eq_iff** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) [inst_2 : L.IsLocalization W] [
W.HasLeftCalculusOfFractions] {X Y : C}   (φ ψ : W.LeftFraction X Y), φ.map L ⋯ 
= ψ.map L ⋯ ↔ CategoryTheory.MorphismProperty.LeftFractionRel φ ψ
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；φ ψ : W.
LeftFraction X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.instIsLocaliza
tionQ`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (W : Categ
oryTheory.MorphismProperty C)   [inst_1 : W.HasLeftCalculusOfFracti…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.map_eq_iff`：ma
p_eq_iff {X Y : C} (f g : LeftFraction W X Y) : f.map (LeftFraction.Localization
.Q W) (Localization.inverts _ _) = g.map (LeftFraction.Loc…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_eq_of_map_eq`：map_eq_of
_map_eq {W} {X Y : C} (φ₁ φ₂ : W.LeftFraction X Y) {E : Type*} [Category* E] (L₁
 : C ⥤ D) (L₂ : C ⥤ E) [L₁.IsLocalization W] [L₂.Is…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.map_mk`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {E : Type u_3}   [i
nst_1 : CategoryTheory.Category.{v_3, u_3} E] {W : Categor…
-/
lemma MorphismProperty.LeftFraction.map_eq_iff
    {X Y : C} (φ ψ : W.LeftFraction X Y) :
    φ.map L (Localization.inverts _ _) = ψ.map L (Localization.inverts _ _) ↔
      LeftFractionRel φ ψ := by
  constructor
  · intro h
    rw [← MorphismProperty.LeftFraction.Localization.map_eq_iff]
    apply map_eq_of_map_eq _ _ _ _ h
  · intro h
    simp only [← Localization.Hom.map_mk _ L (Localization.inverts _ _)]
    congr 1
    exact Quot.sound h

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.map_eq_iff_postcomp** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) [L.IsLocalization W] [W.HasLeft
CalculusOfFractions] {X Y : C} (f₁ f₂ : X ⟶ Y),   L.map f₁ = L.map f₂ ↔     ∃ Z 
s, ∃ (_ : W s), CategoryTheory.CategoryStruct.comp f₁ s = CategoryTheory.Categor
yStruct.comp f₂ s
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；f₁ f₂ : 
X ⟶ Y；_ : W s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions.toIsMultiplic
ative`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasLeftCalculusOfFraction…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.map_eq_iff`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_ofHom`：map_ofHom (f : X
 ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities] : (ofHom W f).m
ap L hL = L.map f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MorphismProperty.map_eq_iff_postcomp {X Y : C} (f₁ f₂ : X ⟶ Y) :
    L.map f₁ = L.map f₂ ↔ ∃ (Z : C) (s : Y ⟶ Z) (_ : W s), f₁ ≫ s = f₂ ≫ s := by
  constructor
  · intro h
    rw [← LeftFraction.map_ofHom W _ L (Localization.inverts _ _),
      ← LeftFraction.map_ofHom W _ L (Localization.inverts _ _),
      LeftFraction.map_eq_iff] at h
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
    dsimp at t₁ t₂ hst hft ht
    grind
  · rintro ⟨Z, s, hs, fac⟩
    simp only [← cancel_mono (Localization.isoOfHom L W s hs).hom,
      Localization.isoOfHom_hom, ← L.map_comp, fac]

set_option backward.defeqAttrib.useBackward true in
include W in
/-
**CategoryTheory.Localization.essSurj_mapArrow** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Localization`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) [L.IsLocalization W] [W.HasLeft
CalculusOfFractions], L.mapArrow.EssSurj
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Localization.exists_leftFraction`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s`：map_comp_ma
p_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : φ.map L hL ≫ 
L.map φ.s = L.map φ.f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Localization.essSurj_mapArrow :
    L.mapArrow.EssSurj where
  mem_essImage f := by
    have := Localization.essSurj L W
    obtain ⟨X, ⟨eX⟩⟩ : ∃ (X : C), Nonempty (L.obj X ≅ f.left) :=
      ⟨_, ⟨L.objObjPreimageIso f.left⟩⟩
    obtain ⟨Y, ⟨eY⟩⟩ : ∃ (Y : C), Nonempty (L.obj Y ≅ f.right) :=
      ⟨_, ⟨L.objObjPreimageIso f.right⟩⟩
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L W (eX.hom ≫ f.hom ≫ eY.inv)
    refine ⟨Arrow.mk φ.f, ⟨Iso.symm ?_⟩⟩
    refine Arrow.isoMk eX.symm (eY.symm ≪≫ Localization.isoOfHom L W φ.s φ.hs) ?_
    dsimp
    simp only [← cancel_epi eX.hom, Iso.hom_inv_id_assoc, reassoc_of% hφ,
      MorphismProperty.LeftFraction.map_comp_map_s]

end


namespace MorphismProperty

variable {W}

/-- The right fraction in the opposite category corresponding to a left fraction. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.LeftFraction.op** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
: CategoryTheory.MorphismProperty C} →       {X Y : C} → W.LeftFraction X Y → W.
op.RightFraction (Opposite.op Y) (Opposite.op X)
参数：Opposite.op Y；Opposite.op X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …

--- 原说明 ---
The right fraction in the opposite category corresponding to a left fraction.
-/
def LeftFraction.op {X Y : C} (φ : W.LeftFraction X Y) :
    W.op.RightFraction (Opposite.op Y) (Opposite.op X) where
  X' := Opposite.op φ.Y'
  s := φ.s.op
  hs := φ.hs
  f := φ.f.op

/-- The left fraction in the opposite category corresponding to a right fraction. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.RightFraction.op** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MorphismProperty.RightFraction`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
: CategoryTheory.MorphismProperty C} →       {X Y : C} → W.RightFraction X Y → W
.op.LeftFraction (Opposite.op Y) (Opposite.op X)
参数：Opposite.op Y；Opposite.op X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.RightFraction X…

--- 原说明 ---
The left fraction in the opposite category corresponding to a right fraction.
-/
def RightFraction.op {X Y : C} (φ : W.RightFraction X Y) :
    W.op.LeftFraction (Opposite.op Y) (Opposite.op X) where
  Y' := Opposite.op φ.X'
  s := φ.s.op
  hs := φ.hs
  f := φ.f.op

/-- The right fraction corresponding to a left fraction in the opposite category. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.LeftFraction.unop** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
: CategoryTheory.MorphismProperty Cᵒᵖ} →       {X Y : Cᵒᵖ} → W.LeftFraction X Y 
→ W.unop.RightFraction (Opposite.unop Y) (Opposite.unop X)
参数：Opposite.unop Y；Opposite.unop X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right fraction corresponding to a left fraction in the opposite category.
-/
def LeftFraction.unop {W : MorphismProperty Cᵒᵖ}
    {X Y : Cᵒᵖ} (φ : W.LeftFraction X Y) :
    W.unop.RightFraction (Opposite.unop Y) (Opposite.unop X) where
  X' := Opposite.unop φ.Y'
  s := φ.s.unop
  hs := φ.hs
  f := φ.f.unop

/-- The left fraction corresponding to a right fraction in the opposite category. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.RightFraction.unop** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MorphismProperty.RightFraction`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
: CategoryTheory.MorphismProperty Cᵒᵖ} →       {X Y : Cᵒᵖ} → W.RightFraction X Y
 → W.unop.LeftFraction (Opposite.unop Y) (Opposite.unop X)
参数：Opposite.unop Y；Opposite.unop X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left fraction corresponding to a right fraction in the opposite category.
-/
def RightFraction.unop {W : MorphismProperty Cᵒᵖ}
    {X Y : Cᵒᵖ} (φ : W.RightFraction X Y) :
    W.unop.LeftFraction (Opposite.unop Y) (Opposite.unop X) where
  Y' := Opposite.unop φ.X'
  s := φ.s.unop
  hs := φ.hs
  f := φ.f.unop

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.RightFraction.op_map** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MorphismProperty.RightFraction`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {W : CategoryTheory.Morphi
smProperty C} {X Y : C}   (φ : W.RightFraction X Y) (L : CategoryTheory.Functor 
C D) (hL : W.IsInvertedBy L), (φ.map L hL).op = φ.op.map L.op ⋯
参数：φ : W.RightFraction X Y；L : CategoryTheory.Functor C D；hL : W.IsInvertedBy L；
φ.map L hL。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.op`：op {W : MorphismPropert
y C} {L : C ⥤ D} (h : W.IsInvertedBy L) : W.op.IsInvertedBy L.op
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.op_inv`：op_inv {X Y : C} (f : X ⟶ Y) [IsIso f] : (inv f).
op = inv f.op
-/
lemma RightFraction.op_map
    {X Y : C} (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    (φ.map L hL).op = φ.op.map L.op hL.op := by
  dsimp [map, LeftFraction.map]
  rw [op_inv]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.LeftFraction.op_map** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {W : CategoryTheory.Morphi
smProperty C} {X Y : C}   (φ : W.LeftFraction X Y) (L : CategoryTheory.Functor C
 D) (hL : W.IsInvertedBy L), (φ.map L hL).op = φ.op.map L.op ⋯
参数：φ : W.LeftFraction X Y；L : CategoryTheory.Functor C D；hL : W.IsInvertedBy L；φ
.map L hL。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.op`：op {W : MorphismPropert
y C} {L : C ⥤ D} (h : W.IsInvertedBy L) : W.op.IsInvertedBy L.op
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.op_inv`：op_inv {X Y : C} (f : X ⟶ Y) [IsIso f] : (inv f).
op = inv f.op
-/
lemma LeftFraction.op_map
    {X Y : C} (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    (φ.map L hL).op = φ.op.map L.op hL.op := by
  dsimp [map, RightFraction.map]
  rw [op_inv]
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : W.HasLeftCalculusOfFractions] : W.op.HasRightCalculusOfFractions where
  exists_rightFraction X Y φ := by
    obtain ⟨ψ, eq⟩ := h.exists_leftFraction φ.unop
    exact ⟨ψ.op, Quiver.Hom.unop_inj eq⟩
  ext X Y Y' f₁ f₂ s hs eq := by
    obtain ⟨X', t, ht, fac⟩ := h.ext f₁.unop f₂.unop s.unop hs (Quiver.Hom.op_inj eq)
    exact ⟨Opposite.op X', t.op, ht, Quiver.Hom.unop_inj fac⟩
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : W.HasRightCalculusOfFractions] : W.op.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ := by
    obtain ⟨ψ, eq⟩ := h.exists_rightFraction φ.unop
    exact ⟨ψ.op, Quiver.Hom.unop_inj eq⟩
  ext X' X Y f₁ f₂ s hs eq := by
    obtain ⟨Y', t, ht, fac⟩ := h.ext f₁.unop f₂.unop s.unop hs (Quiver.Hom.op_inj eq)
    exact ⟨Opposite.op Y', t.op, ht, Quiver.Hom.unop_inj fac⟩
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (W : MorphismProperty Cᵒᵖ) [h : W.HasLeftCalculusOfFractions] :
    W.unop.HasRightCalculusOfFractions where
  exists_rightFraction X Y φ := by
    obtain ⟨ψ, eq⟩ := h.exists_leftFraction φ.op
    exact ⟨ψ.unop, Quiver.Hom.op_inj eq⟩
  ext X Y Y' f₁ f₂ s hs eq := by
    obtain ⟨X', t, ht, fac⟩ := h.ext f₁.op f₂.op s.op hs (Quiver.Hom.unop_inj eq)
    exact ⟨Opposite.unop X', t.unop, ht, Quiver.Hom.op_inj fac⟩
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (W : MorphismProperty Cᵒᵖ) [h : W.HasRightCalculusOfFractions] :
    W.unop.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ := by
    obtain ⟨ψ, eq⟩ := h.exists_rightFraction φ.op
    exact ⟨ψ.unop, Quiver.Hom.op_inj eq⟩
  ext X' X Y f₁ f₂ s hs eq := by
    obtain ⟨Y', t, ht, fac⟩ := h.ext f₁.op f₂.op s.op hs (Quiver.Hom.unop_inj eq)
    exact ⟨Opposite.unop Y', t.unop, ht, Quiver.Hom.op_inj fac⟩

/-- The equivalence relation on right fractions for a morphism property `W`. -/
/-
**CategoryTheory.MorphismProperty.RightFractionRel** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：RightFractionRel {X Y : C} (z₁ z₂ : W.RightFraction X Y) : Prop
参数：z₁ z₂ : W.RightFraction X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence relation on right fractions for a morphism property `W`.
-/
def RightFractionRel {X Y : C} (z₁ z₂ : W.RightFraction X Y) : Prop :=
  ∃ (Z : C) (t₁ : Z ⟶ z₁.X') (t₂ : Z ⟶ z₂.X') (_ : t₁ ≫ z₁.s = t₂ ≫ z₂.s)
    (_ : t₁ ≫ z₁.f = t₂ ≫ z₂.f), W (t₁ ≫ z₁.s)
/-
**CategoryTheory.MorphismProperty.RightFractionRel.op** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MorphismProperty.RightFractionRel`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Catego
ryTheory.MorphismProperty C} {X Y : C}   {z₁ z₂ : W.RightFraction X Y},   Catego
ryTheory.MorphismProperty.RightFractionRel z₁ z₂ → CategoryTheory.MorphismProper
ty.LeftFractionRel z₁.op z₂.op
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
-/
lemma RightFractionRel.op {X Y : C} {z₁ z₂ : W.RightFraction X Y}
    (h : RightFractionRel z₁ z₂) : LeftFractionRel z₁.op z₂.op := by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.op Z, t₁.op, t₂.op, Quiver.Hom.unop_inj hs,
    Quiver.Hom.unop_inj hf, ht⟩
/-
**CategoryTheory.MorphismProperty.RightFractionRel.unop** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.MorphismProperty.RightFractionRel`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Catego
ryTheory.MorphismProperty Cᵒᵖ} {X Y : Cᵒᵖ}   {z₁ z₂ : W.RightFraction X Y},   Ca
tegoryTheory.MorphismProperty.RightFractionRel z₁ z₂ →     CategoryTheory.Morphi
smProperty.LeftFractionRel z₁.unop z₂.unop
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
-/
lemma RightFractionRel.unop {W : MorphismProperty Cᵒᵖ} {X Y : Cᵒᵖ}
    {z₁ z₂ : W.RightFraction X Y}
    (h : RightFractionRel z₁ z₂) : LeftFractionRel z₁.unop z₂.unop := by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.unop Z, t₁.unop, t₂.unop, Quiver.Hom.op_inj hs,
    Quiver.Hom.op_inj hf, ht⟩
/-
**CategoryTheory.MorphismProperty.LeftFractionRel.op** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MorphismProperty.LeftFractionRel`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Catego
ryTheory.MorphismProperty C} {X Y : C}   {z₁ z₂ : W.LeftFraction X Y},   Categor
yTheory.MorphismProperty.LeftFractionRel z₁ z₂ → CategoryTheory.MorphismProperty
.RightFractionRel z₁.op z₂.op
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
-/
lemma LeftFractionRel.op {X Y : C} {z₁ z₂ : W.LeftFraction X Y}
    (h : LeftFractionRel z₁ z₂) : RightFractionRel z₁.op z₂.op := by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.op Z, t₁.op, t₂.op, Quiver.Hom.unop_inj hs,
    Quiver.Hom.unop_inj hf, ht⟩
/-
**CategoryTheory.MorphismProperty.LeftFractionRel.unop** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MorphismProperty.LeftFractionRel`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Catego
ryTheory.MorphismProperty Cᵒᵖ} {X Y : Cᵒᵖ}   {z₁ z₂ : W.LeftFraction X Y},   Cat
egoryTheory.MorphismProperty.LeftFractionRel z₁ z₂ →     CategoryTheory.Morphism
Property.RightFractionRel z₁.unop z₂.unop
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
-/
lemma LeftFractionRel.unop {W : MorphismProperty Cᵒᵖ} {X Y : Cᵒᵖ}
    {z₁ z₂ : W.LeftFraction X Y}
    (h : LeftFractionRel z₁ z₂) : RightFractionRel z₁.unop z₂.unop := by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.unop Z, t₁.unop, t₂.unop, Quiver.Hom.op_inj hs,
    Quiver.Hom.op_inj hf, ht⟩
/-
**CategoryTheory.MorphismProperty.leftFractionRel_op_iff** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.MorphismProperty`。
形式化陈述：leftFractionRel_op_iff {X Y : C} (z₁ z₂ : W.RightFraction X Y) : LeftFract
ionRel z₁.op z₂.op ↔ RightFractionRel z₁ z₂
参数：z₁ z₂ : W.RightFraction X Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFractionRel.unop`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismPropert
y Cᵒᵖ} {X Y : Cᵒᵖ}   {z₁ z₂ : W.LeftFracti…
· 使用定理 `CategoryTheory.MorphismProperty.RightFractionRel.op`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty
 C} {X Y : C}   {z₁ z₂ : W.RightFraction …
-/
lemma leftFractionRel_op_iff
    {X Y : C} (z₁ z₂ : W.RightFraction X Y) :
    LeftFractionRel z₁.op z₂.op ↔ RightFractionRel z₁ z₂ :=
  ⟨fun h => h.unop, fun h => h.op⟩
/-
**CategoryTheory.MorphismProperty.rightFractionRel_op_iff** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：rightFractionRel_op_iff {X Y : C} (z₁ z₂ : W.LeftFraction X Y) : RightFrac
tionRel z₁.op z₂.op ↔ LeftFractionRel z₁ z₂
参数：z₁ z₂ : W.LeftFraction X Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RightFractionRel.unop`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProper
ty Cᵒᵖ} {X Y : Cᵒᵖ}   {z₁ z₂ : W.RightFract…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFractionRel.op`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty 
C} {X Y : C}   {z₁ z₂ : W.LeftFraction X…
-/
lemma rightFractionRel_op_iff
    {X Y : C} (z₁ z₂ : W.LeftFraction X Y) :
    RightFractionRel z₁.op z₂.op ↔ LeftFractionRel z₁ z₂ :=
  ⟨fun h => h.unop, fun h => h.op⟩

namespace RightFractionRel

/-
**CategoryTheory.MorphismProperty.RightFractionRel.refl** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty.RightFractionRel`。
形式化陈述：refl {X Y : C} (z : W.RightFraction X Y) : RightFractionRel z z
参数：z : W.RightFraction X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFractionRel.unop`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismPropert
y Cᵒᵖ} {X Y : Cᵒᵖ}   {z₁ z₂ : W.LeftFracti…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFractionRel.refl`：refl {X Y : C} (z 
: W.LeftFraction X Y) : LeftFractionRel z z
-/
lemma refl {X Y : C} (z : W.RightFraction X Y) : RightFractionRel z z :=
  (LeftFractionRel.refl z.op).unop
/-
**CategoryTheory.MorphismProperty.RightFractionRel.symm** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty.RightFractionRel`。
形式化陈述：symm {X Y : C} {z₁ z₂ : W.RightFraction X Y} (h : RightFractionRel z₁ z₂) 
: RightFractionRel z₂ z₁
参数：h : RightFractionRel z₁ z₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFractionRel.unop`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismPropert
y Cᵒᵖ} {X Y : Cᵒᵖ}   {z₁ z₂ : W.LeftFracti…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFractionRel.symm`：symm {X Y : C} {z₁
 z₂ : W.LeftFraction X Y} (h : LeftFractionRel z₁ z₂) : LeftFractionRel z₂ z₁
· 使用定理 `CategoryTheory.MorphismProperty.RightFractionRel.op`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty
 C} {X Y : C}   {z₁ z₂ : W.RightFraction …
-/
lemma symm {X Y : C} {z₁ z₂ : W.RightFraction X Y} (h : RightFractionRel z₁ z₂) :
    RightFractionRel z₂ z₁ :=
  h.op.symm.unop
/-
**CategoryTheory.MorphismProperty.RightFractionRel.trans** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.MorphismProperty.RightFractionRel`。
形式化陈述：trans {X Y : C} {z₁ z₂ z₃ : W.RightFraction X Y} [HasRightCalculusOfFracti
ons W] (h₁₂ : RightFractionRel z₁ z₂) (h₂₃ : RightFractionRel z₂ z₃) : RightFrac
tionRel z₁ z₃
参数：h₁₂ : RightFractionRel z₁ z₂；h₂₃ : RightFractionRel z₂ z₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFractionRel.unop`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismPropert
y Cᵒᵖ} {X Y : Cᵒᵖ}   {z₁ z₂ : W.LeftFracti…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFractionRel.trans`：trans {X Y : C} {
z₁ z₂ z₃ : W.LeftFraction X Y} [HasLeftCalculusOfFractions W] (h₁₂ : LeftFractio
nRel z₁ z₂) (h₂₃ : LeftFractionRel z₂ z₃) :…
· 使用定理 `CategoryTheory.MorphismProperty.instHasLeftCalculusOfFractionsOppositeOp
OfHasRightCalculusOfFractions`：∀ {C : Type u_1} [inst : CategoryTheory.Category.
{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}   [h : W.HasRightCalculusO
fFractions]…
· 使用定理 `CategoryTheory.MorphismProperty.RightFractionRel.op`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty
 C} {X Y : C}   {z₁ z₂ : W.RightFraction …
-/
lemma trans {X Y : C} {z₁ z₂ z₃ : W.RightFraction X Y}
    [HasRightCalculusOfFractions W]
    (h₁₂ : RightFractionRel z₁ z₂) (h₂₃ : RightFractionRel z₂ z₃) :
    RightFractionRel z₁ z₃ :=
  (h₁₂.op.trans h₂₃.op).unop

end RightFractionRel

/-
**CategoryTheory.MorphismProperty.equivalenceRightFractionRel** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：equivalenceRightFractionRel (X Y : C) [HasRightCalculusOfFractions W] : @_
root_.Equivalence (W.RightFraction X Y) RightFractionRel where refl
参数：X Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.RightFractionRel.refl`：refl {X Y : C} (z
 : W.RightFraction X Y) : RightFractionRel z z
· 使用引理 `CategoryTheory.MorphismProperty.RightFractionRel.symm`：symm {X Y : C} {z
₁ z₂ : W.RightFraction X Y} (h : RightFractionRel z₁ z₂) : RightFractionRel z₂ z
₁
· 使用引理 `CategoryTheory.MorphismProperty.RightFractionRel.trans`：trans {X Y : C} 
{z₁ z₂ z₃ : W.RightFraction X Y} [HasRightCalculusOfFractions W] (h₁₂ : RightFra
ctionRel z₁ z₂) (h₂₃ : RightFractionRel z₂ z…
-/
lemma equivalenceRightFractionRel (X Y : C) [HasRightCalculusOfFractions W] :
    @_root_.Equivalence (W.RightFraction X Y) RightFractionRel where
  refl := RightFractionRel.refl
  symm := RightFractionRel.symm
  trans := RightFractionRel.trans

end MorphismProperty

section

variable [W.HasRightCalculusOfFractions]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Localization.exists_rightFraction** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Localization`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) [inst_2 : L.IsLocalization W] [
W.HasRightCalculusOfFractions] {X Y : C}   (f : L.obj X ⟶ L.obj Y), ∃ φ, f = φ.m
ap L ⋯
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；f : L.ob
j X ⟶ L.obj Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Functor.IsLocalization.op`：∀ {C : Type u_1} {D : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Localization.exists_leftFraction`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.MorphismProperty.instHasLeftCalculusOfFractionsOppositeOp
OfHasRightCalculusOfFractions`：∀ {C : Type u_1} [inst : CategoryTheory.Category.
{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}   [h : W.HasRightCalculusO
fFractions]…
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.op`：op {W : MorphismPropert
y C} {L : C ⥤ D} (h : W.IsInvertedBy L) : W.op.IsInvertedBy L.op
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.op_map`：∀ {C : Type u_1} {
D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Category
Theory.Category.{v_2, u_2} D] {W : Categor…
-/
lemma Localization.exists_rightFraction {X Y : C} (f : L.obj X ⟶ L.obj Y) :
    ∃ (φ : W.RightFraction X Y), f = φ.map L (Localization.inverts L W) := by
  obtain ⟨φ, eq⟩ := Localization.exists_leftFraction L.op W.op f.op
  refine ⟨φ.unop, Quiver.Hom.op_inj ?_⟩
  rw [eq, MorphismProperty.RightFraction.op_map]
  rfl
/-
**CategoryTheory.MorphismProperty.RightFraction.map_eq_iff** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.MorphismProperty.RightFraction`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) [inst_2 : L.IsLocalization W] [
W.HasRightCalculusOfFractions] {X Y : C}   (φ ψ : W.RightFraction X Y), φ.map L 
⋯ = ψ.map L ⋯ ↔ CategoryTheory.MorphismProperty.RightFractionRel φ ψ
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；φ ψ : W.
RightFraction X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.leftFractionRel_op_iff`：leftFractionRel_
op_iff {X Y : C} (z₁ z₂ : W.RightFraction X Y) : LeftFractionRel z₁.op z₂.op ↔ R
ightFractionRel z₁ z₂
· 使用定理 `CategoryTheory.Functor.IsLocalization.op`：∀ {C : Type u_1} {D : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.map_eq_iff`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.MorphismProperty.instHasLeftCalculusOfFractionsOppositeOp
OfHasRightCalculusOfFractions`：∀ {C : Type u_1} [inst : CategoryTheory.Category.
{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}   [h : W.HasRightCalculusO
fFractions]…
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.op`：op {W : MorphismPropert
y C} {L : C ⥤ D} (h : W.IsInvertedBy L) : W.op.IsInvertedBy L.op
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.op_map`：∀ {C : Type u_1} {
D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Category
Theory.Category.{v_2, u_2} D] {W : Categor…
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
-/
lemma MorphismProperty.RightFraction.map_eq_iff
    {X Y : C} (φ ψ : W.RightFraction X Y) :
    φ.map L (Localization.inverts _ _) = ψ.map L (Localization.inverts _ _) ↔
      RightFractionRel φ ψ := by
  rw [← leftFractionRel_op_iff, ← LeftFraction.map_eq_iff L.op W.op φ.op ψ.op,
    ← φ.op_map L (Localization.inverts _ _), ← ψ.op_map L (Localization.inverts _ _)]
  constructor
  · apply Quiver.Hom.unop_inj
  · apply Quiver.Hom.op_inj

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.map_eq_iff_precomp** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) [L.IsLocalization W] [W.HasRigh
tCalculusOfFractions] {Y Z : C}   (f₁ f₂ : Y ⟶ Z),   L.map f₁ = L.map f₂ ↔     ∃
 X s, ∃ (_ : W s), CategoryTheory.CategoryStruct.comp s f₁ = CategoryTheory.Cate
goryStruct.comp s f₂
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；f₁ f₂ : 
Y ⟶ Z；_ : W s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `CategoryTheory.MorphismProperty.HasRightCalculusOfFractions.toIsMultipli
cative`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : Cate
goryTheory.MorphismProperty C}   [self : W.HasRightCalculusOfFractio…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.map_eq_iff`：∀ {C : Type u_
1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.RightFraction.map_ofHom`：map_ofHom (f : 
X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities] : (ofHom W f).
map L hL = L.map f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MorphismProperty.map_eq_iff_precomp {Y Z : C} (f₁ f₂ : Y ⟶ Z) :
    L.map f₁ = L.map f₂ ↔ ∃ (X : C) (s : X ⟶ Y) (_ : W s), s ≫ f₁ = s ≫ f₂ := by
  constructor
  · intro h
    rw [← RightFraction.map_ofHom W _ L (Localization.inverts _ _),
      ← RightFraction.map_ofHom W _ L (Localization.inverts _ _),
      RightFraction.map_eq_iff] at h
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
    dsimp at t₁ t₂ hst hft ht
    grind
  · rintro ⟨Z, s, hs, fac⟩
    simp only [← cancel_epi (Localization.isoOfHom L W s hs).hom,
      Localization.isoOfHom_hom, ← L.map_comp, fac]

include W in
/-
**CategoryTheory.Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Localization`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) [L.IsLocalization W] [W.HasRigh
tCalculusOfFractions], L.mapArrow.EssSurj
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj_mapArrow`：∀ {C : Type u_1} {D : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Functor.IsLocalization.op`：∀ {C : Type u_1} {D : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.MorphismProperty.instHasLeftCalculusOfFractionsOppositeOp
OfHasRightCalculusOfFractions`：∀ {C : Type u_1} [inst : CategoryTheory.Category.
{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}   [h : W.HasRightCalculusO
fFractions]…
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Arrow.Hom.w`：∀ {T : Type u} [inst : CategoryTheory.Catego
ry.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : f ⟶ g),   CategoryTheory.Categ
oryStruct.comp (…
-/
lemma Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions :
    L.mapArrow.EssSurj where
  mem_essImage f := by
    have := Localization.essSurj_mapArrow L.op W.op
    obtain ⟨g, ⟨e⟩⟩ : ∃ (g : _), Nonempty (L.op.mapArrow.obj g ≅ Arrow.mk f.hom.op) :=
      ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
    exact ⟨Arrow.mk g.hom.unop, ⟨Arrow.isoMk (Arrow.rightFunc.mapIso e.symm).unop
      (Arrow.leftFunc.mapIso e.symm).unop (Quiver.Hom.op_inj e.inv.w.symm)⟩⟩

end

end CategoryTheory

