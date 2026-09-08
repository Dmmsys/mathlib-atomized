/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# Pulling back connected colimits

If `c` is a cocone over a functor `J ⥤ C` and `f : X ⟶ c.pt`, then for every `j : J` we can take
the pullback of `c.ι.app j` and `f`. This gives a new cocone with cone point `X`. We show that if
`c` is a colimit cocone, then this is again a colimit cocone as long as `J` is connected and `C`
has exact colimits of shape `J`.

From this we deduce a `hom_ext` principle for morphisms factoring through a colimit. Usually, we
only get `hom_ext` for morphisms *from* a colimit, so this is something a bit special.

The connectedness assumption on `J` is necessary: take `C` to be the category of abelian groups,
let `f : ℤ → ℤ ⊕ ℤ` be the diagonal map, and let `g := 𝟙 (ℤ ⊕ ℤ)`. Then the hypotheses of
`IsColimit.pullback_zero_ext` are satisfied, but `f ≫ g` is not zero.

-/

@[expose] public section

universe w' w v u

namespace CategoryTheory.Limits

variable {J : Type w} [Category.{w'} J] [IsConnected J] {C : Type u} [Category.{v} C]

set_option backward.defeqAttrib.useBackward true in
/--
If `c` is a cocone over a functor `J ⥤ C` and `f : X ⟶ c.pt`, then for every `j : J` we can take
the pullback of `c.ι.app j` and `f`. This gives a new cocone with cone point `X`, and this cocone
is again a colimit cocone as long as `J` is connected and `C` has exact colimits of shape `J`.
-/
/-
**CategoryTheory.Limits.IsColimit.pullbackOfHasExactColimitsOfShape** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Limits.IsColimit`。
形式化陈述：{J : Type w} →   [inst : CategoryTheory.Category.{w', w} J] →     [Categor
yTheory.IsConnected J] →       {C : Type u} →         [inst_2 : CategoryTheory.C
ategory.{v, u} C] →           [inst_3 : CategoryTheory.Limits.HasPullbacks C] → 
            [inst_4 : CategoryTheory.Limits.HasColimitsOfShape J C] →           
    [CategoryTheory.HasExactColimitsOfShape J C] →                 {F : Category
Theory.Functor J C} →                   {c : CategoryTheory.Limits.Cocone F} →  
                   CategoryTheory.Limits.IsColimit c →                       {X 
: C} →                         (f : X ⟶ c.pt) →                           Catego
ryTheory.Limits.IsColimit                             { pt := X,                
               ι := CategoryTheory.Limits.pullback.snd c.ι ((CategoryTheory.Func
tor.const J).map f) }
参数：f : X ⟶ c.pt；(CategoryTheory.Functor.const J).map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a cocone over a functor `J ⥤ C` and `f : X ⟶ c.pt`, then for every `j 
: J` we can take
the pullback of `c.ι.app j` and `f`. This gives a new cocone with cone point `X`
, and this cocone
is again a colimit cocone as long as `J` is connected and `C` has exact colimits
 of shape `J`.
-/
noncomputable def IsColimit.pullbackOfHasExactColimitsOfShape [HasPullbacks C]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] {F : J ⥤ C} {c : Cocone F}
    (hc : IsColimit c) {X : C} (f : X ⟶ c.pt) :
    IsColimit (Cocone.mk _ (pullback.snd c.ι ((Functor.const J).map f))) := by
  suffices IsIso (colimMap (pullback.snd c.ι ((Functor.const J).map f))) from
    Cocone.isColimitOfIsIsoColimMapι _
  have hpull := colim.map_isPullback (IsPullback.of_hasPullback c.ι ((Functor.const J).map f))
  dsimp only [colim_obj, colim_map] at hpull
  have := hc.isIso_colimMap_ι
  apply hpull.isIso_snd_of_isIso

set_option backward.isDefEq.respectTransparency false in
/-- Detecting equality of morphisms factoring through a connected colimit by pulling back along
the inclusions of the colimit. -/
/-
**CategoryTheory.Limits.IsColimit.pullback_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.IsColimit`。
形式化陈述：∀ {J : Type w} [inst : CategoryTheory.Category.{w', w} J] [CategoryTheory.
IsConnected J] {C : Type u}   [inst_2 : CategoryTheory.Category.{v, u} C] [inst_
3 : CategoryTheory.Limits.HasPullbacks C]   [inst_4 : CategoryTheory.Limits.HasC
olimitsOfShape J C] [CategoryTheory.HasExactColimitsOfShape J C]   {F : Category
Theory.Functor J C} {c : CategoryTheory.Limits.Cocone F} (hc : CategoryTheory.Li
mits.IsColimit c)   {X Y : C} {f : X ⟶ c.pt} {g h : c.pt ⟶ Y},   (∀ (j : J),    
   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd (c.ι.a
pp j) f)           (CategoryTheory.CategoryStruct.comp f g) =         CategoryTh
eory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd (c.ι.app j) f)     
      (CategoryTheory.CategoryStruct.comp f h)) →     CategoryTheory.CategoryStr
uct.comp f g = CategoryTheory.CategoryStruct.comp f h
参数：hc : CategoryTheory.Limits.IsColimit c；∀ (j : J),       CategoryTheory.Catego
ryStruct.comp (CategoryTheory.Limits.pullback.snd (c.ι.app j) f)           (Cate
goryTheory.CategoryStruct.comp f g) =         CategoryTheory.CategoryStruct.comp
 (CategoryTheory.Limits.pullback.snd (c.ι.app j) f)           (CategoryTheory.Ca
tegoryStruct.comp f h)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullbackObjIso_inv_comp_snd_assoc`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   {F G H : CategoryT…

--- 原说明 ---
Detecting equality of morphisms factoring through a connected colimit by pulling
 back along
the inclusions of the colimit.
-/
theorem IsColimit.pullback_hom_ext [HasPullbacks C] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) {X Y : C}
    {f : X ⟶ c.pt} {g h : c.pt ⟶ Y}
    (hf : ∀ j, pullback.snd (c.ι.app j) f ≫ f ≫ g = pullback.snd (c.ι.app j) f ≫ f ≫ h) :
    f ≫ g = f ≫ h := by
  refine (hc.pullbackOfHasExactColimitsOfShape f).hom_ext (fun j => ?_)
  rw [← cancel_epi (pullbackObjIso _ _ _).inv]
  simpa using! hf j

/-- Detecting vanishing of a morphism factoring through a connected colimit by pulling back along
the inclusions of the colimit. -/
/-
**CategoryTheory.Limits.IsColimit.pullback_zero_ext** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.IsColimit`。
形式化陈述：∀ {J : Type w} [inst : CategoryTheory.Category.{w', w} J] [CategoryTheory.
IsConnected J] {C : Type u}   [inst_2 : CategoryTheory.Category.{v, u} C] [inst_
3 : CategoryTheory.Limits.HasZeroMorphisms C]   [inst_4 : CategoryTheory.Limits.
HasPullbacks C] [inst_5 : CategoryTheory.Limits.HasColimitsOfShape J C]   [Categ
oryTheory.HasExactColimitsOfShape J C] {F : CategoryTheory.Functor J C} {c : Cat
egoryTheory.Limits.Cocone F}   (hc : CategoryTheory.Limits.IsColimit c) {X Y : C
} {f : X ⟶ c.pt} {g : c.pt ⟶ Y},   (∀ (j : J),       CategoryTheory.CategoryStru
ct.comp (CategoryTheory.Limits.pullback.snd (c.ι.app j) f)           (CategoryTh
eory.CategoryStruct.comp f g) =         0) →     CategoryTheory.CategoryStruct.c
omp f g = 0
参数：hc : CategoryTheory.Limits.IsColimit c；∀ (j : J),       CategoryTheory.Catego
ryStruct.comp (CategoryTheory.Limits.pullback.snd (c.ι.app j) f)           (Cate
goryTheory.CategoryStruct.comp f g) =         0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.IsColimit.pullback_hom_ext`：∀ {J : Type w} [inst :
 CategoryTheory.Category.{w', w} J] [CategoryTheory.IsConnected J] {C : Type u} 
  [inst_2 : CategoryTheory.Category.{v…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)

--- 原说明 ---
Detecting vanishing of a morphism factoring through a connected colimit by pulli
ng back along
the inclusions of the colimit.
-/
theorem IsColimit.pullback_zero_ext [HasZeroMorphisms C] [HasPullbacks C] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) {X Y : C}
    {f : X ⟶ c.pt} {g : c.pt ⟶ Y} (hf : ∀ j, pullback.snd (c.ι.app j) f ≫ f ≫ g = 0) :
    f ≫ g = 0 := by
  suffices f ≫ g = f ≫ 0 by simpa
  exact hc.pullback_hom_ext (by simpa using hf)

set_option backward.defeqAttrib.useBackward true in
/--
If `c` is a cone over a functor `J ⥤ C` and `f : c.pt ⟶ X`, then for every `j : J` we can take
the pushout of `c.π.app j` and `f`. This gives a new cone with cone point `X`, and this cone is
again a limit cone as long as `J` is connected and `C` has exact limits of shape `J`.
-/
/-
**CategoryTheory.Limits.IsLimit.pushoutOfHasExactLimitsOfShape** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Limits.IsLimit`。
形式化陈述：{J : Type w} →   [inst : CategoryTheory.Category.{w', w} J] →     [Categor
yTheory.IsConnected J] →       {C : Type u} →         [inst_2 : CategoryTheory.C
ategory.{v, u} C] →           [inst_3 : CategoryTheory.Limits.HasPushouts C] →  
           [inst_4 : CategoryTheory.Limits.HasLimitsOfShape J C] →              
 [CategoryTheory.HasExactLimitsOfShape J C] →                 {F : CategoryTheor
y.Functor J C} →                   {c : CategoryTheory.Limits.Cone F} →         
            CategoryTheory.Limits.IsLimit c →                       {X : C} →   
                      (f : c.pt ⟶ X) →                           CategoryTheory.
Limits.IsLimit                             { pt := X,                           
    π := CategoryTheory.Limits.pushout.inr c.π ((CategoryTheory.Functor.const J)
.map f) }
参数：f : c.pt ⟶ X；(CategoryTheory.Functor.const J).map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a cone over a functor `J ⥤ C` and `f : c.pt ⟶ X`, then for every `j : 
J` we can take
the pushout of `c.π.app j` and `f`. This gives a new cone with cone point `X`, a
nd this cone is
again a limit cone as long as `J` is connected and `C` has exact limits of shape
 `J`.
-/
noncomputable def IsLimit.pushoutOfHasExactLimitsOfShape [HasPushouts C]
    [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] {F : J ⥤ C} {c : Cone F}
    (hc : IsLimit c) {X : C} (f : c.pt ⟶ X) :
    IsLimit (Cone.mk _ (pushout.inr c.π ((Functor.const J).map f))) := by
  suffices IsIso (limMap (pushout.inr c.π ((Functor.const J).map f))) from
    Cone.isLimitOfIsIsoLimMapπ _
  have hpush := lim.map_isPushout (IsPushout.of_hasPushout c.π ((Functor.const J).map f))
  dsimp only [lim_obj, lim_map] at hpush
  have := hc.isIso_limMap_π
  apply hpush.isIso_inr_of_isIso

set_option backward.isDefEq.respectTransparency false in
/-- Detecting equality of morphisms factoring through a connected limit by pushing out along
the projections of the limit. -/
/-
**CategoryTheory.Limits.IsLimit.pushout_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.IsLimit`。
形式化陈述：∀ {J : Type w} [inst : CategoryTheory.Category.{w', w} J] [CategoryTheory.
IsConnected J] {C : Type u}   [inst_2 : CategoryTheory.Category.{v, u} C] [inst_
3 : CategoryTheory.Limits.HasPushouts C]   [inst_4 : CategoryTheory.Limits.HasLi
mitsOfShape J C] [CategoryTheory.HasExactLimitsOfShape J C]   {F : CategoryTheor
y.Functor J C} {c : CategoryTheory.Limits.Cone F} (hc : CategoryTheory.Limits.Is
Limit c) {X Y : C}   {g h : Y ⟶ c.pt} {f : c.pt ⟶ X},   (∀ (j : J),       Catego
ryTheory.CategoryStruct.comp g           (CategoryTheory.CategoryStruct.comp f (
CategoryTheory.Limits.pushout.inr (c.π.app j) f)) =         CategoryTheory.Categ
oryStruct.comp h           (CategoryTheory.CategoryStruct.comp f (CategoryTheory
.Limits.pushout.inr (c.π.app j) f))) →     CategoryTheory.CategoryStruct.comp g 
f = CategoryTheory.CategoryStruct.comp h f
参数：hc : CategoryTheory.Limits.IsLimit c；∀ (j : J),       CategoryTheory.Category
Struct.comp g           (CategoryTheory.CategoryStruct.comp f (CategoryTheory.Li
mits.pushout.inr (c.π.app j) f)) =         CategoryTheory.CategoryStruct.comp h 
          (CategoryTheory.CategoryStruct.comp f (CategoryTheory.Limits.pushout.i
nr (c.π.app j) f))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
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
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.inr_comp_pushoutObjIso_hom`：inr_comp_pushoutObjIso
_hom (f : F ⟶ G) (g : F ⟶ H) (d : D) : (pushout.inr f g).app d ≫ (pushoutObjIso 
f g d).hom = pushout.inr (f.app d) (g.…

--- 原说明 ---
Detecting equality of morphisms factoring through a connected limit by pushing o
ut along
the projections of the limit.
-/
theorem IsLimit.pushout_hom_ext [HasPushouts C] [HasLimitsOfShape J C]
    [HasExactLimitsOfShape J C] {F : J ⥤ C} {c : Cone F} (hc : IsLimit c) {X Y : C}
    {g h : Y ⟶ c.pt} {f : c.pt ⟶ X}
    (hf : ∀ j, g ≫ f ≫ pushout.inr (c.π.app j) f = h ≫ f ≫ pushout.inr (c.π.app j) f) :
    g ≫ f = h ≫ f := by
  refine (hc.pushoutOfHasExactLimitsOfShape f).hom_ext (fun j => ?_)
  rw [← cancel_mono (pushoutObjIso _ _ _).hom]
  simpa using! hf j

/-- Detecting vanishing of a morphism factoring through a connected limit by pushing out along the
projections of the limit. -/
/-
**CategoryTheory.Limits.IsLimit.pushout_zero_ext** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.IsLimit`。
形式化陈述：∀ {J : Type w} [inst : CategoryTheory.Category.{w', w} J] [CategoryTheory.
IsConnected J] {C : Type u}   [inst_2 : CategoryTheory.Category.{v, u} C] [inst_
3 : CategoryTheory.Limits.HasZeroMorphisms C]   [inst_4 : CategoryTheory.Limits.
HasPushouts C] [inst_5 : CategoryTheory.Limits.HasLimitsOfShape J C]   [Category
Theory.HasExactLimitsOfShape J C] {F : CategoryTheory.Functor J C} {c : Category
Theory.Limits.Cone F}   (hc : CategoryTheory.Limits.IsLimit c) {X Y : C} {g : Y 
⟶ c.pt} {f : c.pt ⟶ X},   (∀ (j : J),       CategoryTheory.CategoryStruct.comp g
           (CategoryTheory.CategoryStruct.comp f (CategoryTheory.Limits.pushout.
inr (c.π.app j) f)) =         0) →     CategoryTheory.CategoryStruct.comp g f = 
0
参数：hc : CategoryTheory.Limits.IsLimit c；∀ (j : J),       CategoryTheory.Category
Struct.comp g           (CategoryTheory.CategoryStruct.comp f (CategoryTheory.Li
mits.pushout.inr (c.π.app j) f)) =         0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.IsLimit.pushout_hom_ext`：∀ {J : Type w} [inst : Ca
tegoryTheory.Category.{w', w} J] [CategoryTheory.IsConnected J] {C : Type u}   [
inst_2 : CategoryTheory.Category.{v…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)

--- 原说明 ---
Detecting vanishing of a morphism factoring through a connected limit by pushing
 out along the
projections of the limit.
-/
theorem IsLimit.pushout_zero_ext [HasZeroMorphisms C] [HasPushouts C] [HasLimitsOfShape J C]
    [HasExactLimitsOfShape J C] {F : J ⥤ C} {c : Cone F} (hc : IsLimit c) {X Y : C}
    {g : Y ⟶ c.pt} {f : c.pt ⟶ X} (hf : ∀ j, g ≫ f ≫ pushout.inr (c.π.app j) f = 0) :
    g ≫ f = 0 := by
  suffices g ≫ f = 0 ≫ f by simpa
  exact hc.pushout_hom_ext (by simpa using hf)

end CategoryTheory.Limits

