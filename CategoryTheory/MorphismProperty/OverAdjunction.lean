/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Adjunction of pushforward and pullback in `P.Over Q X`

Under suitable assumptions on `P`, `Q` and `f`,
a morphism `f : X ⟶ Y` defines two functors:

- `Over.map`: post-composition with `f`
- `Over.pullback`: base-change along `f`

such that `Over.map` is the left adjoint to `Over.pullback`.
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

open Limits

variable {T : Type*} [Category* T] (P Q : MorphismProperty T) [Q.IsMultiplicative]
variable {X Y Z : T}

section Over

section Map

variable {P} [P.IsStableUnderComposition]

/-- If `P` is stable under composition and `f : X ⟶ Y` satisfies `P`,
this is the functor `P.Over Q X ⥤ P.Over Q Y` given by composing with `f`. -/
@[simps! obj_left obj_hom map_left]
/-
**CategoryTheory.MorphismProperty.Over.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
: CategoryTheory.MorphismProperty T} →       (Q : CategoryTheory.MorphismPropert
y T) →         [inst_1 : Q.IsMultiplicative] →           {X Y : T} →            
 [P.IsStableUnderComposition] → {f : X ⟶ Y} → P f → CategoryTheory.Functor (P.Ov
er Q X) (P.Over Q Y)
参数：Q : CategoryTheory.MorphismProperty T；P.Over Q X；P.Over Q Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is stable under composition and `f : X ⟶ Y` satisfies `P`,
this is the functor `P.Over Q X ⥤ P.Over Q Y` given by composing with `f`.
-/
def Over.map {f : X ⟶ Y} (hPf : P f) : P.Over Q X ⥤ P.Over Q Y :=
  Comma.mapRight _ (Discrete.natTrans fun _ ↦ f) <| fun X ↦ P.comp_mem _ _ X.prop hPf

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.Over.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MorphismProperty.Over`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P : Catego
ryTheory.MorphismProperty T}   (Q : CategoryTheory.MorphismProperty T) [inst_1 :
 Q.IsMultiplicative] {X Y Z : T}   [inst_2 : P.IsStableUnderComposition] {f : X 
⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g),   CategoryTheory.MorphismProperty.Over.m
ap Q ⋯ =     (CategoryTheory.MorphismProperty.Over.map Q hf).comp (CategoryTheor
y.MorphismProperty.Over.map Q hg)
参数：Q : CategoryTheory.MorphismProperty T；hf : P f；hg : P g；CategoryTheory.Morphi
smProperty.Over.map Q hf；CategoryTheory.MorphismProperty.Over.map Q hg。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.MorphismProperty.Comma.Hom.prop_hom_left`：∀ {A : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} B] {T : Type u_…
· 使用定理 `CategoryTheory.MorphismProperty.Comma.Hom.prop_hom_right`：∀ {A : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} B] {T : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MorphismProperty.Comma.mk.congr_simp`：∀ {A : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryT
heory.Category.{v_2, u_2} B] {T : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.MorphismProperty.Over.Hom.ext`：∀ {T : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} T] {P Q : CategoryTheory.MorphismProperty T} {
X : T}   [inst_1 : Q.IsMultiplicat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.MorphismProperty.Comma.eqToHom_left`：eqToHom_left {X Y : 
P.Comma L R Q W} (h : X = Y) : (eqToHom h).left = eqToHom (by rw [h])
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma Over.map_comp {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) :
    map Q (P.comp_mem f g hf hg) = map Q hf ⋙ map Q hg := by
  fapply Functor.ext
  · simp [map, Comma.mapRight, CategoryTheory.Comma.mapRight, Comma.lift]
  · intro U V k
    ext
    simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Promote an equality to an isomorphism of `Over.map` functors. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Over.mapCongr** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
: CategoryTheory.MorphismProperty T} →       (Q : CategoryTheory.MorphismPropert
y T) →         [inst_1 : Q.IsMultiplicative] →           [inst_2 : P.IsStableUnd
erComposition] →             [Q.RespectsIso] →               {X Y : T} →        
         {f g : X ⟶ Y} →                   (hfg : f = g) →                     (
hf : P f) →                       CategoryTheory.MorphismProperty.Over.map Q hf 
≅ CategoryTheory.MorphismProperty.Over.map Q ⋯
参数：Q : CategoryTheory.MorphismProperty T；hfg : f = g；hf : P f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promote an equality to an isomorphism of `Over.map` functors.
-/
def Over.mapCongr [Q.RespectsIso] {X Y : T} {f g : X ⟶ Y} (hfg : f = g) (hf : P f) :
    Over.map Q hf ≅ Over.map (f := g) Q (by cat_disch) :=
  NatIso.ofComponents (fun Y ↦ Over.isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.overlappingInstances false in
/-- `Over.map` preserves identities. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Over.mapId** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
: CategoryTheory.MorphismProperty T} →       (Q : CategoryTheory.MorphismPropert
y T) →         [inst_1 : Q.IsMultiplicative] →           [inst_2 : P.IsStableUnd
erComposition] →             [inst_3 : P.IsMultiplicative] →               [Q.Re
spectsIso] →                 (X : T) →                   (f : optParam (X ⟶ X) (
CategoryTheory.CategoryStruct.id X)) →                     (hf :                
         autoParam (f = CategoryTheory.CategoryStruct.id X)                     
      CategoryTheory.MorphismProperty.Over.mapId._auto_1) →                     
  CategoryTheory.MorphismProperty.Over.map Q ⋯ ≅ CategoryTheory.Functor.id (P.Ov
er Q X)
参数：Q : CategoryTheory.MorphismProperty T；X : T；f : optParam (X ⟶ X) (CategoryThe
ory.CategoryStruct.id X)；hf :                         autoParam (f = CategoryThe
ory.CategoryStruct.id X)                           CategoryTheory.MorphismProper
ty.Over.mapId._auto_1；P.Over Q X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Over.map` preserves identities.
-/
def Over.mapId [P.IsMultiplicative] [Q.RespectsIso] (X : T) (f : X ⟶ X := 𝟙 X)
    (hf : f = 𝟙 X := by cat_disch) :
    Over.map (f := f) (P := P) Q (by subst hf; exact P.id_mem X) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun Y ↦ Over.isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `Over.map` commutes with composition. -/
@[simps! hom_app_left inv_app_left]
/-
**CategoryTheory.MorphismProperty.Over.mapComp** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
: CategoryTheory.MorphismProperty T} →       (Q : CategoryTheory.MorphismPropert
y T) →         [inst_1 : Q.IsMultiplicative] →           {X Y Z : T} →          
   [inst_2 : P.IsStableUnderComposition] →               {f : X ⟶ Y} →          
       (hf : P f) →                   {g : Y ⟶ Z} →                     (hg : P 
g) →                       [Q.RespectsIso] →                         (fg : optPa
ram (X ⟶ Z) (CategoryTheory.CategoryStruct.comp f g)) →                         
  (hfg :                               autoParam (fg = CategoryTheory.CategorySt
ruct.comp f g)                                 CategoryTheory.MorphismProperty.O
ver.mapComp._auto_1) →                             CategoryTheory.MorphismProper
ty.Over.map Q ⋯ ≅                               (CategoryTheory.MorphismProperty
.Over.map Q hf).comp                                 (CategoryTheory.MorphismPro
perty.Over.map Q hg)
参数：Q : CategoryTheory.MorphismProperty T；hf : P f；hg : P g；fg : optParam (X ⟶ Z)
 (CategoryTheory.CategoryStruct.comp f g)；hfg :                               au
toParam (fg = CategoryTheory.CategoryStruct.comp f g)                           
      CategoryTheory.MorphismProperty.Over.mapComp._auto_1；CategoryTheory.Morphi
smProperty.Over.map Q hf；CategoryTheory.MorphismProperty.Over.map Q hg。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Over.map` commutes with composition.
-/
def Over.mapComp {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) [Q.RespectsIso]
    (fg : X ⟶ Z := f ≫ g) (hfg : fg = f ≫ g := by cat_disch) :
    map (f := fg) Q (by subst hfg; exact P.comp_mem f g hf hg) ≅ map Q hf ⋙ map Q hg :=
  NatIso.ofComponents (fun X ↦ Over.isoMk (Iso.refl _))

end Map

section Pullback

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) [P.HasPullbacksAlong f] (A : P.Over Q Y) : HasPullback A.hom f :=
  HasPullbacksAlong.hasPullback A.hom A.prop

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z)
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g]
    (A : P.Over Q Z) : HasPullback (pullback.snd A.hom g) f :=
  HasPullbacksAlong.hasPullback (pullback.snd A.hom g)
  (IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback A.hom g) A.prop)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- If `P` and `Q` are stable under base change and pullbacks along `f` exist for morphisms in `P`,
this is the functor `P.Over Q Y ⥤ P.Over Q X` given by base change along `f`. -/
@[simps! obj_left obj_hom map_left]
/-
**CategoryTheory.MorphismProperty.Over.pullback** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     (P 
Q : CategoryTheory.MorphismProperty T) →       [inst_1 : Q.IsMultiplicative] →  
       {X Y : T} →           (f : X ⟶ Y) →             [P.HasPullbacksAlong f] →
               [P.IsStableUnderBaseChangeAlong f] →                 [Q.IsStableU
nderBaseChange] → CategoryTheory.Functor (P.Over Q Y) (P.Over Q X)
参数：P Q : CategoryTheory.MorphismProperty T；f : X ⟶ Y；P.Over Q Y；P.Over Q X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbackHomDiscretePUnitOfHasPull
backsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q 
: CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPullb…

--- 原说明 ---
If `P` and `Q` are stable under base change and pullbacks along `f` exist for mo
rphisms in `P`,
this is the functor `P.Over Q Y ⥤ P.Over Q X` given by base change along `f`.
-/
noncomputable def Over.pullback (f : X ⟶ Y) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] [Q.IsStableUnderBaseChange] :
    P.Over Q Y ⥤ P.Over Q X where
  obj A := Over.mk Q (Limits.pullback.snd A.hom f)
    (pullback_snd A.hom f A.prop)
  map {A B} g := Over.homMk (pullback.lift (pullback.fst A.hom f ≫ g.left)
    (pullback.snd A.hom f) (by simp [pullback.condition])) (by simp)
    (pullbackLift_fst_snd _ _ g.prop_hom_left)

variable {P} {Q}

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- `Over.pullback` commutes with composition. -/
@[simps! hom_app_left inv_app_left]
/-
**CategoryTheory.MorphismProperty.Over.pullbackComp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q : CategoryTheory.MorphismProperty T} →       [inst_1 : Q.IsMultiplicative] →  
       {X Y Z : T} →           (f : X ⟶ Y) →             (g : Y ⟶ Z) →          
     [inst_2 : P.IsStableUnderBaseChangeAlong f] →                 [inst_3 : P.I
sStableUnderBaseChangeAlong g] →                   [inst_4 : P.HasPullbacksAlong
 f] →                     [inst_5 : P.HasPullbacksAlong g] →                    
   [Q.RespectsIso] →                         [inst_7 : Q.IsStableUnderBaseChange
] →                           (fg : optParam (X ⟶ Z) (CategoryTheory.CategoryStr
uct.comp f g)) →                             (hfg :                             
    autoParam (fg = CategoryTheory.CategoryStruct.comp f g)                     
              CategoryTheory.MorphismProperty.Over.pullbackComp._auto_1) →      
                         CategoryTheory.MorphismProperty.Over.pullback P Q fg ≅ 
                                (CategoryTheory.MorphismProperty.Over.pullback P
 Q g).comp                                   (CategoryTheory.MorphismProperty.Ov
er.pullback P Q f)
参数：f : X ⟶ Y；g : Y ⟶ Z；fg : optParam (X ⟶ Z) (CategoryTheory.CategoryStruct.comp
 f g)；hfg :                                 autoParam (fg = CategoryTheory.Categ
oryStruct.comp f g)                                   CategoryTheory.MorphismPro
perty.Over.pullbackComp._auto_1；CategoryTheory.MorphismProperty.Over.pullback P 
Q g；CategoryTheory.MorphismProperty.Over.pullback P Q f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbackHomDiscretePUnitOfHasPull
backsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q 
: CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPullb…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbackSndHomDiscretePUnitOfHasP
ullbacksAlongOfIsStableUnderBaseChangeAlong`：∀ {T : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} T] (P Q : CategoryTheory.MorphismProperty T) {X Y Z : T
}   (f : X ⟶ Y) (g : Y ⟶ …

--- 原说明 ---
`Over.pullback` commutes with composition.
-/
noncomputable def Over.pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z)
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g] [Q.RespectsIso] [Q.IsStableUnderBaseChange]
    (fg : X ⟶ Z := f ≫ g) (hfg : fg = f ≫ g := by cat_disch) :
    haveI : P.HasPullbacksAlong fg := by subst hfg; infer_instance
    haveI : P.IsStableUnderBaseChangeAlong fg := by subst hfg; infer_instance
    Over.pullback P Q fg ≅ Over.pullback P Q g ⋙ Over.pullback P Q f :=
  haveI : P.HasPullbacksAlong fg := by subst hfg; infer_instance
  NatIso.ofComponents fun X ↦
    haveI : HasPullback X.hom fg := HasPullbacksAlong.hasPullback _ X.prop
    Over.isoMk (pullback.congrHom rfl hfg ≪≫ (pullbackLeftPullbackSndIso X.hom g f).symm) (by simp)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.Over.pullbackComp_left_fst_fst** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.MorphismProperty.Over`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P Q : Cate
goryTheory.MorphismProperty T}   [inst_1 : Q.IsMultiplicative] {X Y Z : T} (f : 
X ⟶ Y) (g : Y ⟶ Z) [inst_2 : P.IsStableUnderBaseChangeAlong f]   [inst_3 : P.IsS
tableUnderBaseChangeAlong g] [inst_4 : P.HasPullbacksAlong f] [inst_5 : P.HasPul
lbacksAlong g]   [inst_6 : Q.RespectsIso] [inst_7 : Q.IsStableUnderBaseChange] (
A : P.Over Q Z),   CategoryTheory.CategoryStruct.comp       ((CategoryTheory.Mor
phismProperty.Over.pullbackComp f g (CategoryTheory.CategoryStruct.comp f g) ⋯).
hom.app           A).left       (CategoryTheory.CategoryStruct.comp         (Cat
egoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.snd A.hom g) f) 
        (CategoryTheory.Limits.pullback.fst A.hom g)) =     CategoryTheory.Limit
s.pullback.fst A.hom (CategoryTheory.CategoryStruct.comp f g)
参数：f : X ⟶ Y；g : Y ⟶ Z；A : P.Over Q Z；(CategoryTheory.MorphismProperty.Over.pull
backComp f g (CategoryTheory.CategoryStruct.comp f g) ⋯).hom.app           A；Cat
egoryTheory.CategoryStruct.comp         (CategoryTheory.Limits.pullback.fst (Cat
egoryTheory.Limits.pullback.snd A.hom g) f)         (CategoryTheory.Limits.pullb
ack.fst A.hom g)；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbackHomDiscretePUnitOfHasPull
backsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q 
: CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPullb…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbackSndHomDiscretePUnitOfHasP
ullbacksAlongOfIsStableUnderBaseChangeAlong`：∀ {T : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} T] (P Q : CategoryTheory.MorphismProperty T) {X Y Z : T
}   (f : X ⟶ Y) (g : Y ⟶ …
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksAlongCompOfIsStableUnder
BaseChangeAlong`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : C
ategoryTheory.MorphismProperty C) {X Y Z : C} (f : X ⟶ Y)   (g : Y ⟶ Z) [P.Is…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.map_id`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.pullbackLeftPullbackSndIso_inv_fst`：pullbackLeftPu
llbackSndIso_inv_fst : (pullbackLeftPullbackSndIso f g g').inv ≫ pullback.fst _ 
_ ≫ pullback.fst _ _ = pullback.fst _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Over.pullbackComp_left_fst_fst (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderBaseChangeAlong f]
    [P.IsStableUnderBaseChangeAlong g] [P.HasPullbacksAlong f] [P.HasPullbacksAlong g]
    [Q.RespectsIso] [Q.IsStableUnderBaseChange] (A : P.Over Q Z) :
    ((Over.pullbackComp f g).hom.app A).left ≫ pullback.fst (pullback.snd A.hom g) f ≫
    pullback.fst A.hom g = pullback.fst A.hom (f ≫ g) := by
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- If `f = g`, then base change along `f` is naturally isomorphic to base change along `g`. -/
/-
**CategoryTheory.MorphismProperty.Over.pullbackCongr** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q : CategoryTheory.MorphismProperty T} →       [inst_1 : Q.IsMultiplicative] →  
       {X Y : T} →           {f : X ⟶ Y} →             [inst_2 : P.HasPullbacksA
long f] →               [inst_3 : P.IsStableUnderBaseChangeAlong f] →           
      [inst_4 : Q.IsStableUnderBaseChange] →                   {g : X ⟶ Y} →    
                 (h : f = g) →                       CategoryTheory.MorphismProp
erty.Over.pullback P Q f ≅                         CategoryTheory.MorphismProper
ty.Over.pullback P Q g
参数：h : f = g。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morphi
smProperty C}   [P.IsStableUnderBaseChange], P.RespectsIs…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbackHomDiscretePUnitOfHasPull
backsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q 
: CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPullb…

--- 原说明 ---
If `f = g`, then base change along `f` is naturally isomorphic to base change al
ong `g`.
-/
noncomputable def Over.pullbackCongr {f : X ⟶ Y} [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] [Q.IsStableUnderBaseChange] {g : X ⟶ Y} (h : f = g) :
    haveI : P.HasPullbacksAlong g := by subst h; infer_instance
    haveI : P.IsStableUnderBaseChangeAlong g := by subst h; infer_instance
    Over.pullback P Q f ≅ Over.pullback P Q g :=
  haveI : P.HasPullbacksAlong g := by subst h; infer_instance
  NatIso.ofComponents fun X ↦
    haveI : HasPullback X.hom g := HasPullbacksAlong.hasPullback _ X.prop
    Over.isoMk (pullback.congrHom rfl h)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MorphismProperty.Over.pullbackCongr_hom_app_left_fst** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.Over`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P Q : Cate
goryTheory.MorphismProperty T}   [inst_1 : Q.IsMultiplicative] {X Y : T} {f : X 
⟶ Y} [inst_2 : P.HasPullbacksAlong f] {g : X ⟶ Y}   [inst_3 : P.IsStableUnderBas
eChangeAlong f] [inst_4 : Q.IsStableUnderBaseChange] (h : f = g) (A : P.Over Q Y
),   CategoryTheory.CategoryStruct.comp ((CategoryTheory.MorphismProperty.Over.p
ullbackCongr h).hom.app A).left       (CategoryTheory.Limits.pullback.fst A.hom 
g) =     CategoryTheory.Limits.pullback.fst A.hom f
参数：h : f = g；A : P.Over Q Y；(CategoryTheory.MorphismProperty.Over.pullbackCongr 
h).hom.app A；CategoryTheory.Limits.pullback.fst A.hom g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbackHomDiscretePUnitOfHasPull
backsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q 
: CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.map_id`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Over.pullbackCongr_hom_app_left_fst {f : X ⟶ Y} [P.HasPullbacksAlong f] {g : X ⟶ Y}
    [P.IsStableUnderBaseChangeAlong f] [Q.IsStableUnderBaseChange] (h : f = g) (A : P.Over Q Y) :
    haveI : P.HasPullbacksAlong g := by subst h; infer_instance
    ((Over.pullbackCongr h).hom.app A).left ≫ pullback.fst A.hom g = pullback.fst A.hom f := by
  subst h
  simp [pullbackCongr]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural map between pullback functors induced by `pullback.map`. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.Over.pullbackMapHomPullback** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q : CategoryTheory.MorphismProperty T} →       [inst_1 : Q.IsMultiplicative] →  
       [inst_2 : P.IsStableUnderComposition] →           {X Y Z : T} →          
   (f : X ⟶ Y) →               (hPf : P f) →                 Q f →              
     (g : Y ⟶ Z) →                     [inst_3 : P.IsStableUnderBaseChangeAlong 
f] →                       [inst_4 : P.IsStableUnderBaseChangeAlong g] →        
                 [inst_5 : Q.IsStableUnderBaseChange] →                         
  [inst_6 : CategoryTheory.Limits.HasPullbacks T] →                             
(fg : optParam (X ⟶ Z) (CategoryTheory.CategoryStruct.comp f g)) →              
                 (hfg :                                   autoParam (CategoryThe
ory.CategoryStruct.comp f g = fg)                                     CategoryTh
eory.MorphismProperty.Over.pullbackMapHomPullback._auto_1) →                    
             (CategoryTheory.MorphismProperty.Over.pullback P Q fg).comp        
                             (CategoryTheory.MorphismProperty.Over.map Q hPf) ⟶ 
                                  CategoryTheory.MorphismProperty.Over.pullback 
P Q g
参数：f : X ⟶ Y；hPf : P f；g : Y ⟶ Z；fg : optParam (X ⟶ Z) (CategoryTheory.CategoryS
truct.comp f g)；hfg :                                   autoParam (CategoryTheor
y.CategoryStruct.comp f g = fg)                                     CategoryTheo
ry.MorphismProperty.Over.pullbackMapHomPullback._auto_1；CategoryTheory.MorphismP
roperty.Over.pullback P Q fg；CategoryTheory.MorphismProperty.Over.map Q hPf。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map between pullback functors induced by `pullback.map`.
-/
noncomputable def Over.pullbackMapHomPullback [P.IsStableUnderComposition]
    {X Y Z : T} (f : X ⟶ Y) (hPf : P f) (hQf : Q f) (g : Y ⟶ Z)
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    [Q.IsStableUnderBaseChange] [HasPullbacks T]
    (fg : X ⟶ Z := f ≫ g) (hfg : f ≫ g = fg := by cat_disch) :
    haveI : P.IsStableUnderBaseChangeAlong fg := by subst hfg; infer_instance
    Over.pullback P Q fg ⋙ Over.map (f := f) _ hPf ⟶
      Over.pullback P Q g where
  app A :=
    Over.homMk (pullback.map _ _ _ _ (𝟙 A.left) f (𝟙 Z) (by simp) (by cat_disch))
    (by simp) (Q.pullbackMap (Q.id_mem _) hQf (by simp) (by cat_disch))

/-- `MorphismProperty.Over.pullback` commutes with `MorphismProperty.Over.forget`. -/
@[simps!]
noncomputable
/-
**CategoryTheory.MorphismProperty.Over.pullbackCompForgetIso** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q : CategoryTheory.MorphismProperty T} →       [inst_1 : Q.IsMultiplicative] →  
       {X Y : T} →           (f : X ⟶ Y) →             [inst_2 : CategoryTheory.
Limits.HasPullbacksAlong f] →               [inst_3 : P.IsStableUnderBaseChangeA
long f] →                 [inst_4 : Q.IsStableUnderBaseChange] →                
   (CategoryTheory.MorphismProperty.Over.pullback P Q f).comp                   
    (CategoryTheory.MorphismProperty.Over.forget P Q X) ≅                     (C
ategoryTheory.MorphismProperty.Over.forget P Q Y).comp (CategoryTheory.Over.pull
back f)
参数：f : X ⟶ Y；CategoryTheory.MorphismProperty.Over.pullback P Q f；CategoryTheory.
MorphismProperty.Over.forget P Q X；CategoryTheory.MorphismProperty.Over.forget P
 Q Y；CategoryTheory.Over.pullback f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksAlongOfHasPullbacksAlong
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.M
orphismProperty C) {X Y : C} (f : X ⟶ Y)   [CategoryTheory.Lim…
-/
def Over.pullbackCompForgetIso {X Y : T} (f : X ⟶ Y) [HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] [Q.IsStableUnderBaseChange] :
    Over.pullback P Q f ⋙ Over.forget _ _ _ ≅
      Over.forget _ _ _ ⋙ CategoryTheory.Over.pullback f :=
  Iso.refl _

end Pullback

section Adjunction

variable [P.IsStableUnderComposition] [Q.IsStableUnderBaseChange]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- `P.Over.map` is left adjoint to `P.Over.pullback` if pullbacks of morphisms satisfying `P`
exist along `f` and are also in `P`, and `f` is in both `P` and `Q`. -/
@[simps! unit_app counit_app]
/-
**CategoryTheory.MorphismProperty.Over.mapPullbackAdj** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     (P 
Q : CategoryTheory.MorphismProperty T) →       [inst_1 : Q.IsMultiplicative] →  
       {X Y : T} →           [inst_2 : P.IsStableUnderComposition] →            
 [inst_3 : Q.IsStableUnderBaseChange] →               (f : X ⟶ Y) →             
    [inst_4 : P.HasPullbacksAlong f] →                   [inst_5 : P.IsStableUnd
erBaseChangeAlong f] →                     [Q.HasOfPostcompProperty Q] →        
               (hPf : P f) →                         Q f →                      
     (CategoryTheory.MorphismProperty.Over.map Q hPf ⊣                          
   CategoryTheory.MorphismProperty.Over.pullback P Q f)
参数：P Q : CategoryTheory.MorphismProperty T；f : X ⟶ Y；hPf : P f；CategoryTheory.Mo
rphismProperty.Over.map Q hPf ⊣                             CategoryTheory.Morph
ismProperty.Over.pullback P Q f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbackHomDiscretePUnitOfHasPull
backsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q 
: CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPullb…

--- 原说明 ---
`P.Over.map` is left adjoint to `P.Over.pullback` if pullbacks of morphisms sati
sfying `P`
exist along `f` and are also in `P`, and `f` is in both `P` and `Q`.
-/
noncomputable def Over.mapPullbackAdj (f : X ⟶ Y) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] [Q.HasOfPostcompProperty Q] (hPf : P f) (hQf : Q f) :
    Over.map Q hPf ⊣ Over.pullback P Q f where
  unit.app A := Over.homMk (pullback.lift (𝟙 _) A.hom (by simp)) (by simp) <| by
    apply Q.of_postcomp (W' := Q)
    · exact Q.pullback_fst _ _ hQf
    · simpa using Q.of_isIso _
  unit.naturality A B g := by ext; apply pullback.hom_ext <;> simp
  counit.app A := Over.homMk (pullback.fst _ _) pullback.condition (Q.pullback_fst _ _ hQf)
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] (hPf : P f) :
    (MorphismProperty.Over.map ⊤ hPf).IsLeftAdjoint :=
  (Over.mapPullbackAdj P ⊤ f hPf trivial).isLeftAdjoint
/-
**CategoryTheory.MorphismProperty.isRightAdjoint_pullback** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isRightAdjoint_pullback (f : X ⟶ Y) [P.HasPullbacksAlong f] [P.IsStableUnd
erBaseChangeAlong f] (hPf : P f) : (MorphismProperty.Over.pullback P ⊤ f).IsRigh
tAdjoint
参数：f : X ⟶ Y；hPf : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.isRightAdjoint`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeTop`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderBaseChange
· 使用定理 `CategoryTheory.MorphismProperty.instHasOfPostcompPropertyTop`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.MorphismPrope
rty C),   ⊤.HasOfPostcompProperty W
· 使用定理 `trivial`：True
-/
lemma isRightAdjoint_pullback (f : X ⟶ Y) [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    (hPf : P f) :
    (MorphismProperty.Over.pullback P ⊤ f).IsRightAdjoint :=
  (Over.mapPullbackAdj P ⊤ f hPf trivial).isRightAdjoint

end Adjunction

end Over

section Under

section Map

variable {P} [P.IsStableUnderComposition]

/-- If `P` is stable under composition and `f : X ⟶ Y` satisfies `P`,
this is the functor `P.Under Q Y ⥤ P.Under Q X` given by composing with `f`. -/
@[simps! obj_right obj_hom map_right]
/-
**CategoryTheory.MorphismProperty.Under.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.MorphismProperty.Under`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
: CategoryTheory.MorphismProperty T} →       (Q : CategoryTheory.MorphismPropert
y T) →         [inst_1 : Q.IsMultiplicative] →           {X Y : T} →            
 [P.IsStableUnderComposition] → {f : X ⟶ Y} → P f → CategoryTheory.Functor (P.Un
der Q Y) (P.Under Q X)
参数：Q : CategoryTheory.MorphismProperty T；P.Under Q Y；P.Under Q X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is stable under composition and `f : X ⟶ Y` satisfies `P`,
this is the functor `P.Under Q Y ⥤ P.Under Q X` given by composing with `f`.
-/
def Under.map {f : X ⟶ Y} (hPf : P f) : P.Under Q Y ⥤ P.Under Q X :=
  Comma.mapLeft _ (Discrete.natTrans fun _ ↦ f) <| fun X ↦ P.comp_mem _ _ hPf X.prop

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.Under.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MorphismProperty.Under`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P : Catego
ryTheory.MorphismProperty T}   (Q : CategoryTheory.MorphismProperty T) [inst_1 :
 Q.IsMultiplicative] {X Y Z : T}   [inst_2 : P.IsStableUnderComposition] {f : X 
⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g),   CategoryTheory.MorphismProperty.Under.
map Q ⋯ =     (CategoryTheory.MorphismProperty.Under.map Q hg).comp (CategoryThe
ory.MorphismProperty.Under.map Q hf)
参数：Q : CategoryTheory.MorphismProperty T；hf : P f；hg : P g；CategoryTheory.Morphi
smProperty.Under.map Q hg；CategoryTheory.MorphismProperty.Under.map Q hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.MorphismProperty.Comma.Hom.prop_hom_left`：∀ {A : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} B] {T : Type u_…
· 使用定理 `CategoryTheory.MorphismProperty.Comma.Hom.prop_hom_right`：∀ {A : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} B] {T : Type u_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MorphismProperty.Comma.mk.congr_simp`：∀ {A : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryT
heory.Category.{v_2, u_2} B] {T : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.MorphismProperty.Under.Hom.ext`：∀ {T : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} T] {P Q : CategoryTheory.MorphismProperty T} 
{X : T}   [inst_1 : Q.IsMultiplicat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.MorphismProperty.Comma.eqToHom_right`：eqToHom_right {X Y 
: P.Comma L R Q W} (h : X = Y) : (eqToHom h).right = eqToHom (by rw [h])
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma Under.map_comp {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) :
    map Q (P.comp_mem f g hf hg) = map Q hg ⋙ map Q hf := by
  fapply Functor.ext
  · simp [map, Comma.mapLeft, CategoryTheory.Comma.mapLeft, Comma.lift]
  · intro U V k
    ext
    simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Promote an equality to an isomorphism of `Under.map` functors. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Under.mapCongr** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.MorphismProperty.Under`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
: CategoryTheory.MorphismProperty T} →       (Q : CategoryTheory.MorphismPropert
y T) →         [inst_1 : Q.IsMultiplicative] →           [inst_2 : P.IsStableUnd
erComposition] →             [Q.RespectsIso] →               {X Y : T} →        
         {f g : X ⟶ Y} →                   (hfg : f = g) →                     (
hf : P f) →                       CategoryTheory.MorphismProperty.Under.map Q hf
 ≅ CategoryTheory.MorphismProperty.Under.map Q ⋯
参数：Q : CategoryTheory.MorphismProperty T；hfg : f = g；hf : P f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promote an equality to an isomorphism of `Under.map` functors.
-/
def Under.mapCongr [Q.RespectsIso] {X Y : T} {f g : X ⟶ Y} (hfg : f = g) (hf : P f) :
    Under.map Q hf ≅ Under.map (f := g) Q (by cat_disch) :=
  NatIso.ofComponents (fun Y ↦ Under.isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.overlappingInstances false in
/-- `Under.map` preserves identities. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Under.mapId** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MorphismProperty.Under`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
: CategoryTheory.MorphismProperty T} →       (Q : CategoryTheory.MorphismPropert
y T) →         [inst_1 : Q.IsMultiplicative] →           [inst_2 : P.IsStableUnd
erComposition] →             [inst_3 : P.IsMultiplicative] →               [Q.Re
spectsIso] →                 (X : T) →                   (f : optParam (X ⟶ X) (
CategoryTheory.CategoryStruct.id X)) →                     (hf :                
         autoParam (f = CategoryTheory.CategoryStruct.id X)                     
      CategoryTheory.MorphismProperty.Under.mapId._auto_1) →                    
   CategoryTheory.MorphismProperty.Under.map Q ⋯ ≅ CategoryTheory.Functor.id (P.
Under Q X)
参数：Q : CategoryTheory.MorphismProperty T；X : T；f : optParam (X ⟶ X) (CategoryThe
ory.CategoryStruct.id X)；hf :                         autoParam (f = CategoryThe
ory.CategoryStruct.id X)                           CategoryTheory.MorphismProper
ty.Under.mapId._auto_1；P.Under Q X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Under.map` preserves identities.
-/
def Under.mapId [P.IsMultiplicative] [Q.RespectsIso] (X : T) (f : X ⟶ X := 𝟙 X)
    (hf : f = 𝟙 X := by cat_disch) :
    Under.map (f := f) (P := P) Q (by subst hf; exact P.id_mem X) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun Y ↦ Under.isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `Under.map` commutes with composition. -/
@[simps! hom_app_left]
/-
**CategoryTheory.MorphismProperty.Under.mapComp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.MorphismProperty.Under`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
: CategoryTheory.MorphismProperty T} →       (Q : CategoryTheory.MorphismPropert
y T) →         [inst_1 : Q.IsMultiplicative] →           {X Y Z : T} →          
   [inst_2 : P.IsStableUnderComposition] →               {f : X ⟶ Y} →          
       (hf : P f) →                   {g : Y ⟶ Z} →                     (hg : P 
g) →                       [Q.RespectsIso] →                         (fg : optPa
ram (X ⟶ Z) (CategoryTheory.CategoryStruct.comp f g)) →                         
  (hfg :                               autoParam (fg = CategoryTheory.CategorySt
ruct.comp f g)                                 CategoryTheory.MorphismProperty.U
nder.mapComp._auto_1) →                             CategoryTheory.MorphismPrope
rty.Under.map Q ⋯ ≅                               (CategoryTheory.MorphismProper
ty.Under.map Q hg).comp                                 (CategoryTheory.Morphism
Property.Under.map Q hf)
参数：Q : CategoryTheory.MorphismProperty T；hf : P f；hg : P g；fg : optParam (X ⟶ Z)
 (CategoryTheory.CategoryStruct.comp f g)；hfg :                               au
toParam (fg = CategoryTheory.CategoryStruct.comp f g)                           
      CategoryTheory.MorphismProperty.Under.mapComp._auto_1；CategoryTheory.Morph
ismProperty.Under.map Q hg；CategoryTheory.MorphismProperty.Under.map Q hf。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Under.map` commutes with composition.
-/
def Under.mapComp {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) [Q.RespectsIso]
    (fg : X ⟶ Z := f ≫ g) (hfg : fg = f ≫ g := by cat_disch) :
    map (f := fg) Q (by subst hfg; exact P.comp_mem f g hf hg) ≅ map Q hg ⋙ map Q hf :=
  NatIso.ofComponents (fun X ↦ Under.isoMk (Iso.refl _))

end Map

section Pushout

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) [P.HasPushoutsAlong f] (A : P.Under Q X) : HasPushout A.hom f :=
  HasPushoutsAlong.hasPushout A.hom A.prop

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z} (f : Y ⟶ X) (g : Z ⟶ Y)
    [P.HasPushoutsAlong f] [P.HasPushoutsAlong g] [P.IsStableUnderCobaseChangeAlong g]
    (A : P.Under Q Z) : HasPushout (pushout.inr A.hom g) f :=
  HasPushoutsAlong.hasPushout (pushout.inr A.hom g)
  (IsStableUnderCobaseChangeAlong.of_isPushout (IsPushout.of_hasPushout A.hom g).flip A.prop)

set_option backward.isDefEq.respectTransparency false in
/-- If `P` and `Q` are stable under cobase change and pushouts along `f` exist for morphisms in `P`,
this is the functor `P.Under Q X ⥤ P.Under Q Y` given by cobase change along `f`. -/
@[simps! obj_right obj_hom map_right]
/-
**CategoryTheory.MorphismProperty.Under.pushout** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.MorphismProperty.Under`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     (P 
Q : CategoryTheory.MorphismProperty T) →       [inst_1 : Q.IsMultiplicative] →  
       {X Y : T} →           (f : X ⟶ Y) →             [P.HasPushoutsAlong f] → 
              [P.IsStableUnderCobaseChangeAlong f] →                 [Q.IsStable
UnderCobaseChange] → CategoryTheory.Functor (P.Under Q X) (P.Under Q Y)
参数：P Q : CategoryTheory.MorphismProperty T；f : X ⟶ Y；P.Under Q X；P.Under Q Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutHomDiscretePUnitOfHasPusho
utsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q : 
CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPusho…

--- 原说明 ---
If `P` and `Q` are stable under cobase change and pushouts along `f` exist for m
orphisms in `P`,
this is the functor `P.Under Q X ⥤ P.Under Q Y` given by cobase change along `f`
.
-/
noncomputable def Under.pushout (f : X ⟶ Y) [P.HasPushoutsAlong f]
    [P.IsStableUnderCobaseChangeAlong f] [Q.IsStableUnderCobaseChange] :
    P.Under Q X ⥤ P.Under Q Y where
  obj A := Under.mk Q (Limits.pushout.inr A.hom f)
    (pushout_inr A.hom f A.prop)
  map {A B} g := Under.homMk (pushout.desc (g.right ≫ pushout.inl _ _)
    (pushout.inr _ _) (by simp [pushout.condition])) (by simp)
    (pushoutDesc_inl_inr _ (by simp) g.prop_hom_right)
  map_comp _ _ := by ext; apply pushout.hom_ext <;> simp

variable {P} {Q}

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- `Under.pushout` commutes with composition. -/
@[simps! hom_app_right inv_app_right]
/-
**CategoryTheory.MorphismProperty.Under.pushoutComp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MorphismProperty.Under`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q : CategoryTheory.MorphismProperty T} →       [inst_1 : Q.IsMultiplicative] →  
       {X Y Z : T} →           (f : X ⟶ Y) →             (g : Y ⟶ Z) →          
     [inst_2 : P.IsStableUnderCobaseChangeAlong f] →                 [inst_3 : P
.IsStableUnderCobaseChangeAlong g] →                   [inst_4 : P.HasPushoutsAl
ong f] →                     [inst_5 : P.HasPushoutsAlong g] →                  
     [Q.RespectsIso] →                         [inst_7 : Q.IsStableUnderCobaseCh
ange] →                           (fg : optParam (X ⟶ Z) (CategoryTheory.Categor
yStruct.comp f g)) →                             (hfg :                         
        autoParam (fg = CategoryTheory.CategoryStruct.comp f g)                 
                  CategoryTheory.MorphismProperty.Under.pushoutComp._auto_1) →  
                             CategoryTheory.MorphismProperty.Under.pushout P Q f
g ≅                                 (CategoryTheory.MorphismProperty.Under.pusho
ut P Q f).comp                                   (CategoryTheory.MorphismPropert
y.Under.pushout P Q g)
参数：f : X ⟶ Y；g : Y ⟶ Z；fg : optParam (X ⟶ Z) (CategoryTheory.CategoryStruct.comp
 f g)；hfg :                                 autoParam (fg = CategoryTheory.Categ
oryStruct.comp f g)                                   CategoryTheory.MorphismPro
perty.Under.pushoutComp._auto_1；CategoryTheory.MorphismProperty.Under.pushout P 
Q f；CategoryTheory.MorphismProperty.Under.pushout P Q g。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutHomDiscretePUnitOfHasPusho
utsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q : 
CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPusho…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutInrHomDiscretePUnitOfHasPu
shoutsAlongOfIsStableUnderCobaseChangeAlong`：∀ {T : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} T] (P Q : CategoryTheory.MorphismProperty T) {X Y Z : T
}   (f : Y ⟶ X) (g : Z ⟶ …

--- 原说明 ---
`Under.pushout` commutes with composition.
-/
noncomputable def Under.pushoutComp (f : X ⟶ Y) (g : Y ⟶ Z)
    [P.IsStableUnderCobaseChangeAlong f] [P.IsStableUnderCobaseChangeAlong g]
    [P.HasPushoutsAlong f] [P.HasPushoutsAlong g] [Q.RespectsIso] [Q.IsStableUnderCobaseChange]
    (fg : X ⟶ Z := f ≫ g) (hfg : fg = f ≫ g := by cat_disch) :
    haveI : P.HasPushoutsAlong fg := by subst hfg; infer_instance
    haveI : P.IsStableUnderCobaseChangeAlong fg := by subst hfg; infer_instance
    Under.pushout P Q fg ≅ Under.pushout P Q f ⋙ Under.pushout P Q g :=
  haveI : P.HasPushoutsAlong fg := by subst hfg; infer_instance
  NatIso.ofComponents fun X ↦
    haveI : HasPushout X.hom fg := HasPushoutsAlong.hasPushout _ X.prop
    Under.isoMk (pushout.congrHom rfl hfg ≪≫ (pushoutLeftPushoutInrIso X.hom f g).symm) (by simp)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- If `f = g`, then cobase change along `f` is naturally isomorphic to cobase change along `g`. -/
/-
**CategoryTheory.MorphismProperty.Under.pushoutCongr** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MorphismProperty.Under`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q : CategoryTheory.MorphismProperty T} →       [inst_1 : Q.IsMultiplicative] →  
       {X Y : T} →           {f : X ⟶ Y} →             [inst_2 : P.HasPushoutsAl
ong f] →               [inst_3 : P.IsStableUnderCobaseChangeAlong f] →          
       [inst_4 : Q.IsStableUnderCobaseChange] →                   {g : X ⟶ Y} → 
                    (h : f = g) →                       CategoryTheory.MorphismP
roperty.Under.pushout P Q f ≅                         CategoryTheory.MorphismPro
perty.Under.pushout P Q g
参数：h : f = g。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.respectsIso`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morp
hismProperty C}   [P.IsStableUnderCobaseChange], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutHomDiscretePUnitOfHasPusho
utsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q : 
CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPusho…

--- 原说明 ---
If `f = g`, then cobase change along `f` is naturally isomorphic to cobase chang
e along `g`.
-/
noncomputable def Under.pushoutCongr {f : X ⟶ Y} [P.HasPushoutsAlong f]
    [P.IsStableUnderCobaseChangeAlong f] [Q.IsStableUnderCobaseChange] {g : X ⟶ Y} (h : f = g) :
    haveI : P.HasPushoutsAlong g := by subst h; infer_instance
    haveI : P.IsStableUnderCobaseChangeAlong g := by subst h; infer_instance
    Under.pushout P Q f ≅ Under.pushout P Q g :=
  haveI : P.HasPushoutsAlong g := by subst h; infer_instance
  NatIso.ofComponents fun X ↦
    haveI : HasPushout X.hom g := HasPushoutsAlong.hasPushout _ X.prop
    Under.isoMk (pushout.congrHom rfl h)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MorphismProperty.Under.pushoutCongr_hom_app_left_fst** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.Under`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P Q : Cate
goryTheory.MorphismProperty T}   [inst_1 : Q.IsMultiplicative] {X Y : T} {f : X 
⟶ Y} [inst_2 : P.HasPushoutsAlong f] {g : X ⟶ Y}   [inst_3 : P.IsStableUnderCoba
seChangeAlong f] [inst_4 : Q.IsStableUnderCobaseChange] (h : f = g) (A : P.Under
 Q X),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pushout.inl A
.hom f)       ((CategoryTheory.MorphismProperty.Under.pushoutCongr h).hom.app A)
.right =     CategoryTheory.Limits.pushout.inl A.hom g
参数：h : f = g；A : P.Under Q X；CategoryTheory.Limits.pushout.inl A.hom f；(Category
Theory.MorphismProperty.Under.pushoutCongr h).hom.app A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutHomDiscretePUnitOfHasPusho
utsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q : 
CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPusho…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pushout.map_id`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : CategoryT
heory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Under.pushoutCongr_hom_app_left_fst {f : X ⟶ Y} [P.HasPushoutsAlong f] {g : X ⟶ Y}
    [P.IsStableUnderCobaseChangeAlong f] [Q.IsStableUnderCobaseChange] (h : f = g)
    (A : P.Under Q X) :
    haveI : P.HasPushoutsAlong g := by subst h; infer_instance
    pushout.inl _ _ ≫ ((Under.pushoutCongr h).hom.app A).right = pushout.inl _ _ := by
  subst h
  simp [pushoutCongr]

/-- `MorphismProperty.Under.pushout` commutes with `MorphismProperty.Under.forget`. -/
@[simps!]
noncomputable
/-
**CategoryTheory.MorphismProperty.Under.pushoutCompForgetIso** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.MorphismProperty.Under`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q : CategoryTheory.MorphismProperty T} →       [inst_1 : Q.IsMultiplicative] →  
       {X Y : T} →           (f : X ⟶ Y) →             [inst_2 : CategoryTheory.
Limits.HasPushoutsAlong f] →               [inst_3 : P.IsStableUnderCobaseChange
Along f] →                 [inst_4 : Q.IsStableUnderCobaseChange] →             
      (CategoryTheory.MorphismProperty.Under.pushout P Q f).comp                
       (CategoryTheory.MorphismProperty.Under.forget P Q Y) ≅                   
  (CategoryTheory.MorphismProperty.Under.forget P Q X).comp (CategoryTheory.Unde
r.pushout f)
参数：f : X ⟶ Y；CategoryTheory.MorphismProperty.Under.pushout P Q f；CategoryTheory.
MorphismProperty.Under.forget P Q Y；CategoryTheory.MorphismProperty.Under.forget
 P Q X；CategoryTheory.Under.pushout f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutsAlongOfHasPushoutsAlong`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Mor
phismProperty C) {X Y : C} (f : X ⟶ Y)   [CategoryTheory.Lim…
-/
def Under.pushoutCompForgetIso {X Y : T} (f : X ⟶ Y) [HasPushoutsAlong f]
    [P.IsStableUnderCobaseChangeAlong f] [Q.IsStableUnderCobaseChange] :
    Under.pushout P Q f ⋙ Under.forget _ _ _ ≅
      Under.forget _ _ _ ⋙ CategoryTheory.Under.pushout f :=
  Iso.refl _

end Pushout

section Adjunction

variable [P.IsStableUnderComposition] [Q.IsStableUnderCobaseChange]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
attribute [local instance] hasPushouts_symmetry_of_hasPushoutsAlong in
/-- `P.Under.pushout` is left adjoint to `P.Under.map` if pushouts of morphisms satisfying `P`
exist along `f` and are also in `P`, and `f` is in both `P` and `Q`. -/
@[simps! unit_app counit_app]
/-
**CategoryTheory.MorphismProperty.Under.mapPushoutAdj** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.MorphismProperty.Under`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     (P 
Q : CategoryTheory.MorphismProperty T) →       [inst_1 : Q.IsMultiplicative] →  
       {X Y : T} →           [inst_2 : P.IsStableUnderComposition] →            
 [inst_3 : Q.IsStableUnderCobaseChange] →               (f : X ⟶ Y) →           
      [inst_4 : P.HasPushoutsAlong f] →                   [inst_5 : P.IsStableUn
derCobaseChangeAlong f] →                     [Q.HasOfPrecompProperty Q] →      
                 (hPf : P f) →                         Q f →                    
       (CategoryTheory.MorphismProperty.Under.pushout P Q f ⊣                   
          CategoryTheory.MorphismProperty.Under.map Q hPf)
参数：P Q : CategoryTheory.MorphismProperty T；f : X ⟶ Y；hPf : P f；CategoryTheory.Mo
rphismProperty.Under.pushout P Q f ⊣                             CategoryTheory.
MorphismProperty.Under.map Q hPf。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutHomDiscretePUnitOfHasPusho
utsAlong`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q : 
CategoryTheory.MorphismProperty T) {X Y : T}   (f : X ⟶ Y) [P.HasPusho…

--- 原说明 ---
`P.Under.pushout` is left adjoint to `P.Under.map` if pushouts of morphisms sati
sfying `P`
exist along `f` and are also in `P`, and `f` is in both `P` and `Q`.
-/
noncomputable def Under.mapPushoutAdj (f : X ⟶ Y) [P.HasPushoutsAlong f]
    [P.IsStableUnderCobaseChangeAlong f] [Q.HasOfPrecompProperty Q] (hPf : P f) (hQf : Q f) :
    Under.pushout P Q f ⊣ Under.map Q hPf where
  unit.app A := Under.homMk (pushout.inl _ _) pushout.condition (Q.pushout_inl _ _ hQf)
  counit.app A := Under.homMk (pushout.desc (𝟙 _) A.hom (by simp)) (by simp) <| by
    apply Q.of_precomp (W' := Q)
    · exact Q.pushout_inl _ _ hQf
    · simpa using Q.of_isIso _
  counit.naturality A B g := by ext; apply pushout.hom_ext <;> simp
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) [P.HasPushoutsAlong f] [P.IsStableUnderCobaseChangeAlong f] (hPf : P f) :
    (MorphismProperty.Under.map ⊤ hPf).IsRightAdjoint :=
  (Under.mapPushoutAdj P ⊤ f hPf trivial).isRightAdjoint
/-
**CategoryTheory.MorphismProperty.isLeftAdjoint_pushout** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty`。
形式化陈述：isLeftAdjoint_pushout (f : X ⟶ Y) [P.HasPushoutsAlong f] [P.IsStableUnderC
obaseChangeAlong f] (hPf : P f) : (MorphismProperty.Under.pushout P ⊤ f).IsLeftA
djoint
参数：f : X ⟶ Y；hPf : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.isLeftAdjoint`：isLeftAdjoint (adj : F ⊣ G) : F
.IsLeftAdjoint
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderCobaseChangeTop`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderCobaseChange
· 使用定理 `CategoryTheory.MorphismProperty.instHasOfPrecompPropertyTop`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.MorphismProper
ty C),   ⊤.HasOfPrecompProperty W
· 使用定理 `trivial`：True
-/
lemma isLeftAdjoint_pushout (f : X ⟶ Y) [P.HasPushoutsAlong f] [P.IsStableUnderCobaseChangeAlong f]
    (hPf : P f) :
    (MorphismProperty.Under.pushout P ⊤ f).IsLeftAdjoint :=
  (Under.mapPushoutAdj P ⊤ f hPf trivial).isLeftAdjoint

end Adjunction

end Under

end CategoryTheory.MorphismProperty

