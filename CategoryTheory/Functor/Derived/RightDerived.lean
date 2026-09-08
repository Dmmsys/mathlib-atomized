/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Right derived functors

In this file, given a functor `F : C ⥤ H`, and `L : C ⥤ D` that is a
localization functor for `W : MorphismProperty C`, we define
`F.totalRightDerived L W : D ⥤ H` as the left Kan extension of `F`
along `L`: it is defined if the type class `F.HasRightDerivedFunctor W`
asserting the existence of a left Kan extension is satisfied.
(The name `totalRightDerived` is to avoid name-collision with
`Functor.rightDerived` which are the right derived functors in
the context of abelian categories.)

Given `RF : D ⥤ H` and `α : F ⟶ L ⋙ RF`, we also introduce a type class
`F.IsRightDerivedFunctor α W` saying that `α` is a left Kan extension of `F`
along the localization functor `L`.

## TODO

- refactor `Functor.rightDerived` (and `Functor.leftDerived`) when the necessary
  material enters mathlib: derived categories, injective/projective derivability
  structures, existence of derived functors from derivability structures.

## References

* https://ncatlab.org/nlab/show/derived+functor

-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C C' D D' H H' : Type _} [Category* C] [Category* C']
  [Category* D] [Category* D'] [Category* H] [Category* H']
  (RF RF' RF'' : D ⥤ H) {F F' F'' : C ⥤ H} (e : F ≅ F') {L : C ⥤ D}
  (α : F ⟶ L ⋙ RF) (α' : F' ⟶ L ⋙ RF') (α'' : F'' ⟶ L ⋙ RF'') (α'₂ : F ⟶ L ⋙ RF')
  (W : MorphismProperty C)

/-- A functor `RF : D ⥤ H` is a right derived functor of `F : C ⥤ H`
if it is equipped with a natural transformation `α : F ⟶ L ⋙ RF`
which makes it a left Kan extension of `F` along `L`,
where `L : C ⥤ D` is a localization functor for `W : MorphismProperty C`. -/
/-
**CategoryTheory.Functor.IsRightDerivedFunctor** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     {H : Type u_3} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_3, u_2} D] →           [inst_2 : CategoryTheory.Category.{v_5, u_3} H] →      
       (RF : CategoryTheory.Functor D H) →               {F : CategoryTheory.Fun
ctor C H} →                 {L : CategoryTheory.Functor C D} →                  
 (F ⟶ L.comp RF) → (W : CategoryTheory.MorphismProperty C) → [L.IsLocalization W
] → Prop
参数：RF : CategoryTheory.Functor D H；F ⟶ L.comp RF；W : CategoryTheory.MorphismProp
erty C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `RF : D ⥤ H` is a right derived functor of `F : C ⥤ H`
if it is equipped with a natural transformation `α : F ⟶ L ⋙ RF`
which makes it a left Kan extension of `F` along `L`,
where `L : C ⥤ D` is a localization functor for `W : MorphismProperty C`.
-/
class IsRightDerivedFunctor (RF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D} (α : F ⟶ L ⋙ RF)
    (W : MorphismProperty C) [L.IsLocalization W] : Prop where
  isLeftKanExtension (RF α) : RF.IsLeftKanExtension α
/-
**CategoryTheory.Functor.isRightDerivedFunctor_iff_isLeftKanExtension** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isRightDerivedFunctor_iff_isLeftKanExtension [L.IsLocalization W] : RF.IsR
ightDerivedFunctor α W ↔ RF.IsLeftKanExtension α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsRightDerivedFunctor.isLeftKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …
-/
lemma isRightDerivedFunctor_iff_isLeftKanExtension [L.IsLocalization W] :
    RF.IsRightDerivedFunctor α W ↔ RF.IsLeftKanExtension α := by
  constructor
  · exact fun _ => IsRightDerivedFunctor.isLeftKanExtension RF α W
  · exact fun h => ⟨h⟩

variable {RF RF'} in
/-
**CategoryTheory.Functor.isRightDerivedFunctor_iff_of_iso** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：isRightDerivedFunctor_iff_of_iso (α' : F ⟶ L ⋙ RF') (W : MorphismProperty 
C) [L.IsLocalization W] (e : RF ≅ RF') (comm : α ≫ whiskerLeft L e.hom = α') : R
F.IsRightDerivedFunctor α W ↔ RF'.IsRightDerivedFunctor α' W
参数：α' : F ⟶ L ⋙ RF'；W : MorphismProperty C；e : RF ≅ RF'；comm : α ≫ whiskerLeft L
 e.hom = α'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.isLeftKanExtension_iff_of_iso`：isLeftKanExtension
_iff_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙
 F') (α' : F ⟶ L ⋙ F'') (comm : α ≫ whiske…
-/
lemma isRightDerivedFunctor_iff_of_iso (α' : F ⟶ L ⋙ RF') (W : MorphismProperty C)
    [L.IsLocalization W] (e : RF ≅ RF') (comm : α ≫ whiskerLeft L e.hom = α') :
    RF.IsRightDerivedFunctor α W ↔ RF'.IsRightDerivedFunctor α' W := by
  simp only [isRightDerivedFunctor_iff_isLeftKanExtension]
  exact isLeftKanExtension_iff_of_iso e _ _ comm

section

variable [L.IsLocalization W] [RF.IsRightDerivedFunctor α W]

/-- Constructor for natural transformations from a right derived functor. -/
/-
**CategoryTheory.Functor.rightDerivedDesc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：rightDerivedDesc (G : D ⥤ H) (β : F ⟶ L ⋙ G) : RF ⟶ G
参数：G : D ⥤ H；β : F ⟶ L ⋙ G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsRightDerivedFunctor.isLeftKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …

--- 原说明 ---
Constructor for natural transformations from a right derived functor.
-/
noncomputable def rightDerivedDesc (G : D ⥤ H) (β : F ⟶ L ⋙ G) : RF ⟶ G :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension α G β

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.rightDerived_fac** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：rightDerived_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (RF.right
DerivedDesc α W G β) = β
参数：G : D ⥤ H；β : F ⟶ L ⋙ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsRightDerivedFunctor.isLeftKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac`：descOfIsLeftKanExte
nsion_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (F'.descOfIsLeftKanExt
ension α G β) = β
-/
lemma rightDerived_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    α ≫ whiskerLeft L (RF.rightDerivedDesc α W G β) = β :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension_fac α G β

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.rightDerived_fac_app** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：rightDerived_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) : α.app X ≫ (RF.r
ightDerivedDesc α W G β).app (L.obj X) = β.app X
参数：G : D ⥤ H；β : F ⟶ L ⋙ G；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsRightDerivedFunctor.isLeftKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac_app`：descOfIsLeftKan
Extension_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) : α.app X ≫ (F'.descOfIsLe
ftKanExtension α G β).app (L.obj X) = β.app X
-/
lemma rightDerived_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) :
    α.app X ≫ (RF.rightDerivedDesc α W G β).app (L.obj X) = β.app X :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension_fac_app α G β X

include W in
/-
**CategoryTheory.Functor.rightDerived_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：rightDerived_ext (G : D ⥤ H) (γ₁ γ₂ : RF ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ =
 α ≫ whiskerLeft L γ₂) : γ₁ = γ₂
参数：G : D ⥤ H；γ₁ γ₂ : RF ⟶ G；hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiskerLeft L γ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsRightDerivedFunctor.isLeftKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
-/
lemma rightDerived_ext (G : D ⥤ H) (γ₁ γ₂ : RF ⟶ G)
    (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiskerLeft L γ₂) : γ₁ = γ₂ :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.hom_ext_of_isLeftKanExtension α γ₁ γ₂ hγ

/-- The natural transformation `RF ⟶ RF'` on right derived functors that is
induced by a natural transformation `F ⟶ F'`. -/
/-
**CategoryTheory.Functor.rightDerivedNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：rightDerivedNatTrans (τ : F ⟶ F') : RF ⟶ RF'
参数：τ : F ⟶ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `RF ⟶ RF'` on right derived functors that is
induced by a natural transformation `F ⟶ F'`.
-/
noncomputable def rightDerivedNatTrans (τ : F ⟶ F') : RF ⟶ RF' :=
  RF.rightDerivedDesc α W RF' (τ ≫ α')

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.rightDerivedNatTrans_fac** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：rightDerivedNatTrans_fac (τ : F ⟶ F') : α ≫ whiskerLeft L (rightDerivedNat
Trans RF RF' α α' W τ) = τ ≫ α'
参数：τ : F ⟶ F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.rightDerived_fac`：rightDerived_fac (G : D ⥤ H) (β
 : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (RF.rightDerivedDesc α W G β) = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightDerivedNatTrans_fac (τ : F ⟶ F') :
    α ≫ whiskerLeft L (rightDerivedNatTrans RF RF' α α' W τ) = τ ≫ α' := by
  dsimp only [rightDerivedNatTrans]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.rightDerivedNatTrans_app** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：rightDerivedNatTrans_app (τ : F ⟶ F') (X : C) : α.app X ≫ (rightDerivedNat
Trans RF RF' α α' W τ).app (L.obj X) = τ.app X ≫ α'.app X
参数：τ : F ⟶ F'；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.rightDerived_fac_app`：rightDerived_fac_app (G : D
 ⥤ H) (β : F ⟶ L ⋙ G) (X : C) : α.app X ≫ (RF.rightDerivedDesc α W G β).app (L.o
bj X) = β.app X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightDerivedNatTrans_app (τ : F ⟶ F') (X : C) :
    α.app X ≫ (rightDerivedNatTrans RF RF' α α' W τ).app (L.obj X) =
    τ.app X ≫ α'.app X := by
  dsimp only [rightDerivedNatTrans]
  simp

@[simp]
/-
**CategoryTheory.Functor.rightDerivedNatTrans_id** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：rightDerivedNatTrans_id : rightDerivedNatTrans RF RF α α W (𝟙 F) = 𝟙 RF
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.rightDerived_ext`：rightDerived_ext (G : D ⥤ H) (γ
₁ γ₂ : RF ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiskerLeft L γ₂) : γ₁ = γ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.rightDerivedNatTrans_fac`：rightDerivedNatTrans_fa
c (τ : F ⟶ F') : α ≫ whiskerLeft L (rightDerivedNatTrans RF RF' α α' W τ) = τ ≫ 
α'
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightDerivedNatTrans_id :
    rightDerivedNatTrans RF RF α α W (𝟙 F) = 𝟙 RF :=
  rightDerived_ext RF α W _ _ _ (by simp)

variable [RF'.IsRightDerivedFunctor α' W]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.rightDerivedNatTrans_comp** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：rightDerivedNatTrans_comp (τ : F ⟶ F') (τ' : F' ⟶ F'') : rightDerivedNatTr
ans RF RF' α α' W τ ≫ rightDerivedNatTrans RF' RF'' α' α'' W τ' = rightDerivedNa
tTrans RF RF'' α α'' W (τ ≫ τ')
参数：τ : F ⟶ F'；τ' : F' ⟶ F''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.rightDerived_ext`：rightDerived_ext (G : D ⥤ H) (γ
₁ γ₂ : RF ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiskerLeft L γ₂) : γ₁ = γ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.rightDerivedNatTrans_fac_assoc`：∀ {C : Type u_1} 
{D : Type u_3} {H : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [i
nst_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.rightDerivedNatTrans_fac`：rightDerivedNatTrans_fa
c (τ : F ⟶ F') : α ≫ whiskerLeft L (rightDerivedNatTrans RF RF' α α' W τ) = τ ≫ 
α'
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightDerivedNatTrans_comp (τ : F ⟶ F') (τ' : F' ⟶ F'') :
    rightDerivedNatTrans RF RF' α α' W τ ≫ rightDerivedNatTrans RF' RF'' α' α'' W τ' =
    rightDerivedNatTrans RF RF'' α α'' W (τ ≫ τ') :=
  rightDerived_ext RF α W _ _ _ (by simp)

/-- The natural isomorphism `RF ≅ RF'` on right derived functors that is
induced by a natural isomorphism `F ≅ F'`. -/
@[simps]
/-
**CategoryTheory.Functor.rightDerivedNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：rightDerivedNatIso (τ : F ≅ F') : RF ≅ RF' where hom
参数：τ : F ≅ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `RF ≅ RF'` on right derived functors that is
induced by a natural isomorphism `F ≅ F'`.
-/
noncomputable def rightDerivedNatIso (τ : F ≅ F') :
    RF ≅ RF' where
  hom := rightDerivedNatTrans RF RF' α α' W τ.hom
  inv := rightDerivedNatTrans RF' RF α' α W τ.inv

/-- Uniqueness (up to a natural isomorphism) of the right derived functor. -/
/-
**CategoryTheory.Functor.rightDerivedUnique** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：rightDerivedUnique [RF'.IsRightDerivedFunctor α'₂ W] : RF ≅ RF'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uniqueness (up to a natural isomorphism) of the right derived functor.
-/
noncomputable abbrev rightDerivedUnique [RF'.IsRightDerivedFunctor α'₂ W] : RF ≅ RF' :=
  rightDerivedNatIso RF RF' α α'₂ W (Iso.refl F)
/-
**CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isRightDerivedFunctor_iff_isIso_rightDerivedDesc (G : D ⥤ H) (β : F ⟶ L ⋙ 
G) : G.IsRightDerivedFunctor β W ↔ IsIso (RF.rightDerivedDesc α W G β)
参数：G : D ⥤ H；β : F ⟶ L ⋙ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.isRightDerivedFunctor_iff_isLeftKanExtension`：isR
ightDerivedFunctor_iff_isLeftKanExtension [L.IsLocalization W] : RF.IsRightDeriv
edFunctor α W ↔ RF.IsLeftKanExtension α
· 使用定理 `CategoryTheory.Functor.IsRightDerivedFunctor.isLeftKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …
· 使用引理 `CategoryTheory.Functor.isLeftKanExtension_iff_isIso`：isLeftKanExtension_
iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F' ⟶ F'') {L : C ⥤ D} {F : C ⥤ H} (α :
 F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'') (comm : α…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Functor.rightDerived_fac`：rightDerived_fac (G : D ⥤ H) (β
 : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (RF.rightDerivedDesc α W G β) = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isRightDerivedFunctor_iff_isIso_rightDerivedDesc (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    G.IsRightDerivedFunctor β W ↔ IsIso (RF.rightDerivedDesc α W G β) := by
  rw [isRightDerivedFunctor_iff_isLeftKanExtension]
  have := IsRightDerivedFunctor.isLeftKanExtension _ α W
  exact isLeftKanExtension_iff_isIso _ α _ (by simp)

end

variable (F)

/-- A functor `F : C ⥤ H` has a right derived functor with respect to
`W : MorphismProperty C` if it has a left Kan extension along
`W.Q : C ⥤ W.Localization` (or any localization functor `L : C ⥤ D`
for `W`, see `hasRightDerivedFunctor_iff`). -/
/-
**CategoryTheory.Functor.HasRightDerivedFunctor** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：{C : Type u_1} →   {H : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_5, u_2} H] →         Ca
tegoryTheory.Functor C H → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ H` has a right derived functor with respect to
`W : MorphismProperty C` if it has a left Kan extension along
`W.Q : C ⥤ W.Localization` (or any localization functor `L : C ⥤ D`
for `W`, see `hasRightDerivedFunctor_iff`).
-/
class HasRightDerivedFunctor : Prop where
  hasLeftKanExtension' : HasLeftKanExtension W.Q F

variable (L)
variable [L.IsLocalization W]
/-
**CategoryTheory.Functor.hasRightDerivedFunctor_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：hasRightDerivedFunctor_iff : F.HasRightDerivedFunctor W ↔ HasLeftKanExtens
ion L F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.HasRightDerivedFunctor.hasLeftKanExtension'`：∀ {C
 : Type u_1} {H : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {ins
t_1 : CategoryTheory.Category.{v_5, u_2} H} {F : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.hasLeftExtension_iff_postcomp₁`：hasLeftExtension_
iff_postcomp₁ (e : L ⋙ G ≅ L') (F : C ⥤ H) : HasLeftKanExtension L' F ↔ HasLeftK
anExtension L F
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasRightDerivedFunctor_iff :
    F.HasRightDerivedFunctor W ↔ HasLeftKanExtension L F := by
  have : HasRightDerivedFunctor F W ↔ HasLeftKanExtension W.Q F :=
    ⟨fun h => h.hasLeftKanExtension', fun h => ⟨h⟩⟩
  rw [this, hasLeftExtension_iff_postcomp₁ (Localization.compUniqFunctor W.Q L W) F]

variable {F}

include e in
/-
**CategoryTheory.Functor.hasRightDerivedFunctor_iff_of_iso** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：hasRightDerivedFunctor_iff_of_iso : HasRightDerivedFunctor F W ↔ HasRightD
erivedFunctor F' W
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.hasRightDerivedFunctor_iff`：hasRightDerivedFuncto
r_iff : F.HasRightDerivedFunctor W ↔ HasLeftKanExtension L F
· 使用引理 `CategoryTheory.Functor.hasLeftExtension_iff_of_iso₂`：hasLeftExtension_if
f_of_iso₂ : HasLeftKanExtension L F ↔ HasLeftKanExtension L F'
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasRightDerivedFunctor_iff_of_iso :
    HasRightDerivedFunctor F W ↔ HasRightDerivedFunctor F' W := by
  rw [hasRightDerivedFunctor_iff F W.Q W, hasRightDerivedFunctor_iff F' W.Q W,
    hasLeftExtension_iff_of_iso₂ W.Q e]

variable (F)
/-
**CategoryTheory.Functor.HasRightDerivedFunctor.hasLeftKanExtension** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Functor.HasRightDerivedFunctor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_3} {H : Type u_2} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} D] [inst_2 : C
ategoryTheory.Category.{v_5, u_2} H]   (F : CategoryTheory.Functor C H) (L : Cat
egoryTheory.Functor C D) (W : CategoryTheory.MorphismProperty C)   [L.IsLocaliza
tion W] [F.HasRightDerivedFunctor W], L.HasLeftKanExtension F
参数：F : CategoryTheory.Functor C H；L : CategoryTheory.Functor C D；W : CategoryThe
ory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.hasRightDerivedFunctor_iff`：hasRightDerivedFuncto
r_iff : F.HasRightDerivedFunctor W ↔ HasLeftKanExtension L F
-/
lemma HasRightDerivedFunctor.hasLeftKanExtension [HasRightDerivedFunctor F W] :
    HasLeftKanExtension L F := by
  simpa only [← hasRightDerivedFunctor_iff F L W]

variable {F L W}
/-
**CategoryTheory.Functor.HasRightDerivedFunctor.mk'** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Functor.HasRightDerivedFunctor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {H : Type u_3} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_5, u_3} H]   (RF : CategoryTheory.Functor D H) {F : Ca
tegoryTheory.Functor C H} {L : CategoryTheory.Functor C D}   (α : F ⟶ L.comp RF)
 {W : CategoryTheory.MorphismProperty C} [inst_3 : L.IsLocalization W]   [RF.IsR
ightDerivedFunctor α W], F.HasRightDerivedFunctor W
参数：RF : CategoryTheory.Functor D H；α : F ⟶ L.comp RF。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsRightDerivedFunctor.isLeftKanExtension`：∀ {C : 
Type u_1} {D : Type u_2} {H : Type u_3} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_2} …
· 使用引理 `CategoryTheory.Functor.hasRightDerivedFunctor_iff`：hasRightDerivedFuncto
r_iff : F.HasRightDerivedFunctor W ↔ HasLeftKanExtension L F
· 使用定理 `CategoryTheory.Functor.HasLeftKanExtension.mk`：∀ {C : Type u_1} {H : Typ
e u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : 
CategoryTheory.Category.{v_3, u_3} …
-/
lemma HasRightDerivedFunctor.mk' [RF.IsRightDerivedFunctor α W] :
    HasRightDerivedFunctor F W := by
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  simpa only [hasRightDerivedFunctor_iff F L W] using HasLeftKanExtension.mk RF α

section

variable (F) [F.HasRightDerivedFunctor W] (L W)

/-- Given a functor `F : C ⥤ H`, and a localization functor `L : C ⥤ D` for `W`,
this is the right derived functor `D ⥤ H` of `F`, i.e. the left Kan extension
of `F` along `L`. -/
/-
**CategoryTheory.Functor.totalRightDerived** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：totalRightDerived : D ⥤ H
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.HasRightDerivedFunctor.hasLeftKanExtension`：∀ {C 
: Type u_1} {D : Type u_3} {H : Type u_2} [inst : CategoryTheory.Category.{v_1, 
u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} …

--- 原说明 ---
Given a functor `F : C ⥤ H`, and a localization functor `L : C ⥤ D` for `W`,
this is the right derived functor `D ⥤ H` of `F`, i.e. the left Kan extension
of `F` along `L`.
-/
noncomputable def totalRightDerived : D ⥤ H :=
  have := HasRightDerivedFunctor.hasLeftKanExtension F L W
  leftKanExtension L F

/-- The canonical natural transformation `F ⟶ L ⋙ F.totalRightDerived L W`. -/
/-
**CategoryTheory.Functor.totalRightDerivedUnit** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：totalRightDerivedUnit : F ⟶ L ⋙ F.totalRightDerived L W
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.HasRightDerivedFunctor.hasLeftKanExtension`：∀ {C 
: Type u_1} {D : Type u_3} {H : Type u_2} [inst : CategoryTheory.Category.{v_1, 
u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} …

--- 原说明 ---
The canonical natural transformation `F ⟶ L ⋙ F.totalRightDerived L W`.
-/
noncomputable def totalRightDerivedUnit : F ⟶ L ⋙ F.totalRightDerived L W :=
  have := HasRightDerivedFunctor.hasLeftKanExtension F L W
  leftKanExtensionUnit L F
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (F.totalRightDerived L W).IsRightDerivedFunctor
    (F.totalRightDerivedUnit L W) W where
  isLeftKanExtension := by
    dsimp [totalRightDerived, totalRightDerivedUnit]
    infer_instance

end

end Functor

end CategoryTheory

