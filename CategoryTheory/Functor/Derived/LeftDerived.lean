/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Left derived functors

In this file, given a functor `F : C ⥤ H`, and `L : C ⥤ D` that is a
localization functor for `W : MorphismProperty C`, we define
`F.totalLeftDerived L W : D ⥤ H` as the right Kan extension of `F`
along `L`: it is defined if the type class `F.HasLeftDerivedFunctor W`
asserting the existence of a right Kan extension is satisfied.
(The name `totalLeftDerived` is to avoid name-collision with
`Functor.leftDerived` which are the left derived functors in
the context of abelian categories.)

Given `LF : D ⥤ H` and `α : L ⋙ LF ⟶ F`, we also introduce a type class
`F.IsLeftDerivedFunctor α W` saying that `α` is a right Kan extension of `F`
along the localization functor `L`.

(This file was obtained by dualizing the results in the file
`Mathlib.CategoryTheory.Functor.Derived.RightDerived`.)

## References

* https://ncatlab.org/nlab/show/derived+functor

-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C C' D D' H H' : Type _} [Category* C] [Category* C']
  [Category* D] [Category* D'] [Category* H] [Category* H']
  (LF'' LF' LF : D ⥤ H) {F F' F'' : C ⥤ H} (e : F ≅ F') {L : C ⥤ D}
  (α'' : L ⋙ LF'' ⟶ F'') (α' : L ⋙ LF' ⟶ F') (α : L ⋙ LF ⟶ F) (α'₂ : L ⋙ LF' ⟶ F)
  (W : MorphismProperty C)

/-- A functor `LF : D ⥤ H` is a left derived functor of `F : C ⥤ H`
if it is equipped with a natural transformation `α : L ⋙ LF ⟶ F`
which makes it a right Kan extension of `F` along `L`,
where `L : C ⥤ D` is a localization functor for `W : MorphismProperty C`. -/
/-
**CategoryTheory.Functor.IsLeftDerivedFunctor** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     {H : Type u_3} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_3, u_2} D] →           [inst_2 : CategoryTheory.Category.{v_5, u_3} H] →      
       (LF : CategoryTheory.Functor D H) →               {F : CategoryTheory.Fun
ctor C H} →                 {L : CategoryTheory.Functor C D} →                  
 (L.comp LF ⟶ F) → (W : CategoryTheory.MorphismProperty C) → [L.IsLocalization W
] → Prop
参数：LF : CategoryTheory.Functor D H；L.comp LF ⟶ F；W : CategoryTheory.MorphismProp
erty C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `LF : D ⥤ H` is a left derived functor of `F : C ⥤ H`
if it is equipped with a natural transformation `α : L ⋙ LF ⟶ F`
which makes it a right Kan extension of `F` along `L`,
where `L : C ⥤ D` is a localization functor for `W : MorphismProperty C`.
-/
class IsLeftDerivedFunctor (LF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D} (α : L ⋙ LF ⟶ F)
    (W : MorphismProperty C) [L.IsLocalization W] : Prop where
  isRightKanExtension (LF α) : LF.IsRightKanExtension α
/-
**CategoryTheory.Functor.isLeftDerivedFunctor_iff_isRightKanExtension** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isLeftDerivedFunctor_iff_isRightKanExtension [L.IsLocalization W] : LF.IsL
eftDerivedFunctor α W ↔ LF.IsRightKanExtension α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLeftDerivedFunctor.isRightKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …
-/
lemma isLeftDerivedFunctor_iff_isRightKanExtension [L.IsLocalization W] :
    LF.IsLeftDerivedFunctor α W ↔ LF.IsRightKanExtension α := by
  constructor
  · exact fun _ => IsLeftDerivedFunctor.isRightKanExtension LF α W
  · exact fun h => ⟨h⟩

variable {RF RF'} in
/-
**CategoryTheory.Functor.isLeftDerivedFunctor_iff_of_iso** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：isLeftDerivedFunctor_iff_of_iso (α' : L ⋙ LF' ⟶ F) (W : MorphismProperty C
) [L.IsLocalization W] (e : LF ≅ LF') (comm : whiskerLeft L e.hom ≫ α' = α) : LF
.IsLeftDerivedFunctor α W ↔ LF'.IsLeftDerivedFunctor α' W
参数：α' : L ⋙ LF' ⟶ F；W : MorphismProperty C；e : LF ≅ LF'；comm : whiskerLeft L e.h
om ≫ α' = α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.isRightKanExtension_iff_of_iso`：isRightKanExtensi
on_iff_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F
' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : whiskerLe…
-/
lemma isLeftDerivedFunctor_iff_of_iso (α' : L ⋙ LF' ⟶ F) (W : MorphismProperty C)
    [L.IsLocalization W] (e : LF ≅ LF') (comm : whiskerLeft L e.hom ≫ α' = α) :
    LF.IsLeftDerivedFunctor α W ↔ LF'.IsLeftDerivedFunctor α' W := by
  simp only [isLeftDerivedFunctor_iff_isRightKanExtension]
  exact isRightKanExtension_iff_of_iso e _ _ comm

section

variable [L.IsLocalization W] [LF.IsLeftDerivedFunctor α W]

/-- Constructor for natural transformations to a left derived functor. -/
/-
**CategoryTheory.Functor.leftDerivedLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：leftDerivedLift (G : D ⥤ H) (β : L ⋙ G ⟶ F) : G ⟶ LF
参数：G : D ⥤ H；β : L ⋙ G ⟶ F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLeftDerivedFunctor.isRightKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …

--- 原说明 ---
Constructor for natural transformations to a left derived functor.
-/
noncomputable def leftDerivedLift (G : D ⥤ H) (β : L ⋙ G ⟶ F) : G ⟶ LF :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension α G β

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.leftDerived_fac** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：leftDerived_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) : whiskerLeft L (LF.leftDerive
dLift α W G β) ≫ α = β
参数：G : D ⥤ H；β : L ⋙ G ⟶ F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLeftDerivedFunctor.isRightKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …
· 使用引理 `CategoryTheory.Functor.liftOfIsRightKanExtension_fac`：liftOfIsRightKanEx
tension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) : whiskerLeft L (F'.liftOfIsRightKanExte
nsion α G β) ≫ α = β
-/
lemma leftDerived_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) :
    whiskerLeft L (LF.leftDerivedLift α W G β) ≫ α = β :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension_fac α G β

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.leftDerived_fac_app** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：leftDerived_fac_app (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C) : (LF.leftDerivedL
ift α W G β).app (L.obj X) ≫ α.app X = β.app X
参数：G : D ⥤ H；β : L ⋙ G ⟶ F；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLeftDerivedFunctor.isRightKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …
· 使用引理 `CategoryTheory.Functor.liftOfIsRightKanExtension_fac_app`：liftOfIsRightK
anExtension_fac_app (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C) : (F'.liftOfIsRightKanEx
tension α G β).app (L.obj X) ≫ α.app X = β.app…
-/
lemma leftDerived_fac_app (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C) :
    (LF.leftDerivedLift α W G β).app (L.obj X) ≫ α.app X = β.app X :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension_fac_app α G β X

include W in
/-
**CategoryTheory.Functor.leftDerived_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：leftDerived_ext (G : D ⥤ H) (γ₁ γ₂ : G ⟶ LF) (hγ : whiskerLeft L γ₁ ≫ α = 
whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂
参数：G : D ⥤ H；γ₁ γ₂ : G ⟶ LF；hγ : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLeftDerivedFunctor.isRightKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isRightKanExtension`：hom_ext_of_isRigh
tKanExtension {G : D ⥤ H} (γ₁ γ₂ : G ⟶ F') (hγ : whiskerLeft L γ₁ ≫ α = whiskerL
eft L γ₂ ≫ α) : γ₁ = γ₂
-/
lemma leftDerived_ext (G : D ⥤ H) (γ₁ γ₂ : G ⟶ LF)
    (hγ : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂ :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.hom_ext_of_isRightKanExtension α γ₁ γ₂ hγ

/-- The natural transformation `LF' ⟶ LF` on left derived functors that is
induced by a natural transformation `F' ⟶ F`. -/
/-
**CategoryTheory.Functor.leftDerivedNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor`。
形式化陈述：leftDerivedNatTrans (τ : F' ⟶ F) : LF' ⟶ LF
参数：τ : F' ⟶ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `LF' ⟶ LF` on left derived functors that is
induced by a natural transformation `F' ⟶ F`.
-/
noncomputable def leftDerivedNatTrans (τ : F' ⟶ F) : LF' ⟶ LF :=
  LF.leftDerivedLift α W LF' (α' ≫ τ)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.leftDerivedNatTrans_fac** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：leftDerivedNatTrans_fac (τ : F' ⟶ F) : whiskerLeft L (leftDerivedNatTrans 
LF' LF α' α W τ) ≫ α = α' ≫ τ
参数：τ : F' ⟶ F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.leftDerived_fac`：leftDerived_fac (G : D ⥤ H) (β :
 L ⋙ G ⟶ F) : whiskerLeft L (LF.leftDerivedLift α W G β) ≫ α = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftDerivedNatTrans_fac (τ : F' ⟶ F) :
    whiskerLeft L (leftDerivedNatTrans LF' LF α' α W τ) ≫ α = α' ≫ τ := by
  dsimp only [leftDerivedNatTrans]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.leftDerivedNatTrans_app** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：leftDerivedNatTrans_app (τ : F' ⟶ F) (X : C) : (leftDerivedNatTrans LF' LF
 α' α W τ).app (L.obj X) ≫ α.app X = α'.app X ≫ τ.app X
参数：τ : F' ⟶ F；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.leftDerived_fac_app`：leftDerived_fac_app (G : D ⥤
 H) (β : L ⋙ G ⟶ F) (X : C) : (LF.leftDerivedLift α W G β).app (L.obj X) ≫ α.app
 X = β.app X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftDerivedNatTrans_app (τ : F' ⟶ F) (X : C) :
    (leftDerivedNatTrans LF' LF α' α W τ).app (L.obj X) ≫ α.app X =
    α'.app X ≫ τ.app X := by
  dsimp only [leftDerivedNatTrans]
  simp

@[simp]
/-
**CategoryTheory.Functor.leftDerivedNatTrans_id** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：leftDerivedNatTrans_id : leftDerivedNatTrans LF LF α α W (𝟙 F) = 𝟙 LF
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.leftDerived_ext`：leftDerived_ext (G : D ⥤ H) (γ₁ 
γ₂ : G ⟶ LF) (hγ : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.leftDerivedNatTrans_fac`：leftDerivedNatTrans_fac 
(τ : F' ⟶ F) : whiskerLeft L (leftDerivedNatTrans LF' LF α' α W τ) ≫ α = α' ≫ τ
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftDerivedNatTrans_id :
    leftDerivedNatTrans LF LF α α W (𝟙 F) = 𝟙 LF :=
  leftDerived_ext LF α W _ _ _ (by simp)

variable [LF'.IsLeftDerivedFunctor α' W]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.leftDerivedNatTrans_comp** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：leftDerivedNatTrans_comp (τ' : F'' ⟶ F') (τ : F' ⟶ F) : leftDerivedNatTran
s LF'' LF' α'' α' W τ' ≫ leftDerivedNatTrans LF' LF α' α W τ = leftDerivedNatTra
ns LF'' LF α'' α W (τ' ≫ τ)
参数：τ' : F'' ⟶ F'；τ : F' ⟶ F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.leftDerived_ext`：leftDerived_ext (G : D ⥤ H) (γ₁ 
γ₂ : G ⟶ LF) (hγ : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.leftDerivedNatTrans_fac`：leftDerivedNatTrans_fac 
(τ : F' ⟶ F) : whiskerLeft L (leftDerivedNatTrans LF' LF α' α W τ) ≫ α = α' ≫ τ
· 使用定理 `CategoryTheory.Functor.leftDerivedNatTrans_fac_assoc`：∀ {C : Type u_1} {
D : Type u_3} {H : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [in
st_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftDerivedNatTrans_comp (τ' : F'' ⟶ F') (τ : F' ⟶ F) :
    leftDerivedNatTrans LF'' LF' α'' α' W τ' ≫ leftDerivedNatTrans LF' LF α' α W τ =
    leftDerivedNatTrans LF'' LF α'' α W (τ' ≫ τ) :=
  leftDerived_ext LF α W _ _ _ (by simp)

/-- The natural isomorphism `LF' ≅ LF` on left derived functors that is
induced by a natural isomorphism `F' ≅ F`. -/
@[simps]
/-
**CategoryTheory.Functor.leftDerivedNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：leftDerivedNatIso (τ : F' ≅ F) : LF' ≅ LF where hom
参数：τ : F' ≅ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `LF' ≅ LF` on left derived functors that is
induced by a natural isomorphism `F' ≅ F`.
-/
noncomputable def leftDerivedNatIso (τ : F' ≅ F) :
    LF' ≅ LF where
  hom := leftDerivedNatTrans LF' LF α' α W τ.hom
  inv := leftDerivedNatTrans LF LF' α α' W τ.inv

/-- Uniqueness (up to a natural isomorphism) of the left derived functor. -/
/-
**CategoryTheory.Functor.leftDerivedUnique** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Functor`。
形式化陈述：leftDerivedUnique [LF'.IsLeftDerivedFunctor α'₂ W] : LF ≅ LF'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uniqueness (up to a natural isomorphism) of the left derived functor.
-/
noncomputable abbrev leftDerivedUnique [LF'.IsLeftDerivedFunctor α'₂ W] : LF ≅ LF' :=
  leftDerivedNatIso LF LF' α α'₂ W (Iso.refl F)
/-
**CategoryTheory.Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isLeftDerivedFunctor_iff_isIso_leftDerivedLift (G : D ⥤ H) (β : L ⋙ G ⟶ F)
 : G.IsLeftDerivedFunctor β W ↔ IsIso (LF.leftDerivedLift α W G β)
参数：G : D ⥤ H；β : L ⋙ G ⟶ F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.isLeftDerivedFunctor_iff_isRightKanExtension`：isL
eftDerivedFunctor_iff_isRightKanExtension [L.IsLocalization W] : LF.IsLeftDerive
dFunctor α W ↔ LF.IsRightKanExtension α
· 使用定理 `CategoryTheory.Functor.IsLeftDerivedFunctor.isRightKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …
· 使用引理 `CategoryTheory.Functor.isRightKanExtension_iff_isIso`：isRightKanExtensio
n_iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F'' ⟶ F') {L : C ⥤ D} {F : C ⥤ H} (α
 : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Functor.leftDerived_fac`：leftDerived_fac (G : D ⥤ H) (β :
 L ⋙ G ⟶ F) : whiskerLeft L (LF.leftDerivedLift α W G β) ≫ α = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isLeftDerivedFunctor_iff_isIso_leftDerivedLift (G : D ⥤ H) (β : L ⋙ G ⟶ F) :
    G.IsLeftDerivedFunctor β W ↔ IsIso (LF.leftDerivedLift α W G β) := by
  rw [isLeftDerivedFunctor_iff_isRightKanExtension]
  have := IsLeftDerivedFunctor.isRightKanExtension _ α W
  exact isRightKanExtension_iff_isIso _ α _ (by simp)

end

variable (F)

/-- A functor `F : C ⥤ H` has a left derived functor with respect to
`W : MorphismProperty C` if it has a right Kan extension along
`W.Q : C ⥤ W.Localization` (or any localization functor `L : C ⥤ D`
for `W`, see `hasLeftDerivedFunctor_iff`). -/
/-
**CategoryTheory.Functor.HasLeftDerivedFunctor** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：{C : Type u_1} →   {H : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_5, u_2} H] →         Ca
tegoryTheory.Functor C H → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ H` has a left derived functor with respect to
`W : MorphismProperty C` if it has a right Kan extension along
`W.Q : C ⥤ W.Localization` (or any localization functor `L : C ⥤ D`
for `W`, see `hasLeftDerivedFunctor_iff`).
-/
class HasLeftDerivedFunctor : Prop where
  hasRightKanExtension' : HasRightKanExtension W.Q F

variable (L)
variable [L.IsLocalization W]
/-
**CategoryTheory.Functor.hasLeftDerivedFunctor_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：hasLeftDerivedFunctor_iff : F.HasLeftDerivedFunctor W ↔ HasRightKanExtensi
on L F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.HasLeftDerivedFunctor.hasRightKanExtension'`：∀ {C
 : Type u_1} {H : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {ins
t_1 : CategoryTheory.Category.{v_5, u_2} H} {F : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.hasRightExtension_iff_postcomp₁`：hasRightExtensio
n_iff_postcomp₁ (e : L ⋙ G ≅ L') (F : C ⥤ H) : HasRightKanExtension L' F ↔ HasRi
ghtKanExtension L F
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasLeftDerivedFunctor_iff :
    F.HasLeftDerivedFunctor W ↔ HasRightKanExtension L F := by
  have : HasLeftDerivedFunctor F W ↔ HasRightKanExtension W.Q F :=
    ⟨fun h => h.hasRightKanExtension', fun h => ⟨h⟩⟩
  rw [this, hasRightExtension_iff_postcomp₁ (Localization.compUniqFunctor W.Q L W) F]

variable {F}

include e in
/-
**CategoryTheory.Functor.hasLeftDerivedFunctor_iff_of_iso** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：hasLeftDerivedFunctor_iff_of_iso : HasLeftDerivedFunctor F W ↔ HasLeftDeri
vedFunctor F' W
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.hasLeftDerivedFunctor_iff`：hasLeftDerivedFunctor_
iff : F.HasLeftDerivedFunctor W ↔ HasRightKanExtension L F
· 使用引理 `CategoryTheory.Functor.hasRightExtension_iff_of_iso₂`：hasRightExtension_
iff_of_iso₂ : HasRightKanExtension L F ↔ HasRightKanExtension L F'
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasLeftDerivedFunctor_iff_of_iso :
    HasLeftDerivedFunctor F W ↔ HasLeftDerivedFunctor F' W := by
  rw [hasLeftDerivedFunctor_iff F W.Q W, hasLeftDerivedFunctor_iff F' W.Q W,
    hasRightExtension_iff_of_iso₂ W.Q e]

variable (F)
/-
**CategoryTheory.Functor.HasLeftDerivedFunctor.hasRightKanExtension** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Functor.HasLeftDerivedFunctor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_3} {H : Type u_2} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} D] [inst_2 : C
ategoryTheory.Category.{v_5, u_2} H]   (F : CategoryTheory.Functor C H) (L : Cat
egoryTheory.Functor C D) (W : CategoryTheory.MorphismProperty C)   [L.IsLocaliza
tion W] [F.HasLeftDerivedFunctor W], L.HasRightKanExtension F
参数：F : CategoryTheory.Functor C H；L : CategoryTheory.Functor C D；W : CategoryThe
ory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.hasLeftDerivedFunctor_iff`：hasLeftDerivedFunctor_
iff : F.HasLeftDerivedFunctor W ↔ HasRightKanExtension L F
-/
lemma HasLeftDerivedFunctor.hasRightKanExtension [HasLeftDerivedFunctor F W] :
    HasRightKanExtension L F := by
  simpa only [← hasLeftDerivedFunctor_iff F L W]

variable {F L W}
/-
**CategoryTheory.Functor.HasLeftDerivedFunctor.mk'** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor.HasLeftDerivedFunctor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_3} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_5, u_3} H]   (LF : CategoryTheory.Functor D H) {F : Ca
tegoryTheory.Functor C H} {L : CategoryTheory.Functor C D}   (α : L.comp LF ⟶ F)
 {W : CategoryTheory.MorphismProperty C} [inst_3 : L.IsLocalization W]   [LF.IsL
eftDerivedFunctor α W], F.HasLeftDerivedFunctor W
参数：LF : CategoryTheory.Functor D H；α : L.comp LF ⟶ F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLeftDerivedFunctor.isRightKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …
· 使用引理 `CategoryTheory.Functor.hasLeftDerivedFunctor_iff`：hasLeftDerivedFunctor_
iff : F.HasLeftDerivedFunctor W ↔ HasRightKanExtension L F
· 使用定理 `CategoryTheory.Functor.HasRightKanExtension.mk`：∀ {C : Type u_1} {H : Ty
pe u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_3, u_3} …
-/
lemma HasLeftDerivedFunctor.mk' [LF.IsLeftDerivedFunctor α W] :
    HasLeftDerivedFunctor F W := by
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  simpa only [hasLeftDerivedFunctor_iff F L W] using HasRightKanExtension.mk LF α

section

variable (F) [F.HasLeftDerivedFunctor W] (L W)

/-- Given a functor `F : C ⥤ H`, and a localization functor `L : C ⥤ D` for `W`,
this is the left derived functor `D ⥤ H` of `F`, i.e. the right Kan extension
of `F` along `L`. -/
/-
**CategoryTheory.Functor.totalLeftDerived** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：totalLeftDerived : D ⥤ H
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.HasLeftDerivedFunctor.hasRightKanExtension`：∀ {C 
: Type u_1} {D : Type u_3} {H : Type u_2} [inst : CategoryTheory.Category.{v_1, 
u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} …

--- 原说明 ---
Given a functor `F : C ⥤ H`, and a localization functor `L : C ⥤ D` for `W`,
this is the left derived functor `D ⥤ H` of `F`, i.e. the right Kan extension
of `F` along `L`.
-/
noncomputable def totalLeftDerived : D ⥤ H :=
  have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtension L F

/-- The canonical natural transformation `L ⋙ F.totalLeftDerived L W ⟶ F`. -/
/-
**CategoryTheory.Functor.totalLeftDerivedCounit** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：totalLeftDerivedCounit : L ⋙ F.totalLeftDerived L W ⟶ F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.HasLeftDerivedFunctor.hasRightKanExtension`：∀ {C 
: Type u_1} {D : Type u_3} {H : Type u_2} [inst : CategoryTheory.Category.{v_1, 
u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} …

--- 原说明 ---
The canonical natural transformation `L ⋙ F.totalLeftDerived L W ⟶ F`.
-/
noncomputable def totalLeftDerivedCounit : L ⋙ F.totalLeftDerived L W ⟶ F :=
  have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtensionCounit L F
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (F.totalLeftDerived L W).IsLeftDerivedFunctor
    (F.totalLeftDerivedCounit L W) W where
  isRightKanExtension := by
    dsimp [totalLeftDerived, totalLeftDerivedCounit]
    infer_instance

end

end Functor

end CategoryTheory

