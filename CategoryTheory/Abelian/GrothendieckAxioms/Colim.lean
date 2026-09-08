/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Exactness of colimits

In this file, we shall study exactness properties of colimits.
First, we translate the assumption that `colim : (J ⥤ C) ⥤ C`
preserves monomorphisms (resp. preserves epimorphisms, resp. is exact)
into statements involving arbitrary cocones instead of the ones
given by the colimit API. We also show that when an inductive system
involves only monomorphisms, then the "inclusion" morphism
into the colimit is also a monomorphism (assuming `J`
is filtered and `C` satisfies AB5).

-/

@[expose] public section

universe v' v u' u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : Type u'} [Category.{v'} J]

namespace Limits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Assume that `colim : (J ⥤ C) ⥤ C` preserves monomorphisms, and
`φ : X₁ ⟶ X₂` is a monomorphism in `J ⥤ C`, then if `f : c₁.pt ⟶ c₂.pt` is a morphism
between the points of colimit cocones for `X₁` and `X₂` in such a way that `f`
identifies to `colim.map φ`, then `f` is a monomorphism. -/
/-
**CategoryTheory.Limits.colim.map_mono'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.colim`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} J]   [inst_2 : CategoryTheory.Limits.Has
ColimitsOfShape J C] [CategoryTheory.Limits.colim.PreservesMonomorphisms]   {X₁ 
X₂ : CategoryTheory.Functor J C} (φ : X₁ ⟶ X₂) [CategoryTheory.Mono φ] {c₁ : Cat
egoryTheory.Limits.Cocone X₁}   (hc₁ : CategoryTheory.Limits.IsColimit c₁) {c₂ :
 CategoryTheory.Limits.Cocone X₂}   (hc₂ : CategoryTheory.Limits.IsColimit c₂) (
f : c₁.pt ⟶ c₂.pt),   (∀ (j : J),       CategoryTheory.CategoryStruct.comp (c₁.ι
.app j) f = CategoryTheory.CategoryStruct.comp (φ.app j) (c₂.ι.app j)) →     Cat
egoryTheory.Mono f
参数：φ : X₁ ⟶ X₂；hc₁ : CategoryTheory.Limits.IsColimit c₁；hc₂ : CategoryTheory.Lim
its.IsColimit c₂；f : c₁.pt ⟶ c₂.pt；∀ (j : J),       CategoryTheory.CategoryStruc
t.comp (c₁.ι.app j) f = CategoryTheory.CategoryStruct.comp (φ.app j) (c₂.ι.app j
)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.monomorphisms`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.mo
nomorphisms C).RespectsIso
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom_assoc`
：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst
_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.colimit.cocone_ι`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…

--- 原说明 ---
Assume that `colim : (J ⥤ C) ⥤ C` preserves monomorphisms, and
`φ : X₁ ⟶ X₂` is a monomorphism in `J ⥤ C`, then if `f : c₁.pt ⟶ c₂.pt` is a mor
phism
between the points of colimit cocones for `X₁` and `X₂` in such a way that `f`
identifies to `colim.map φ`, then `f` is a monomorphism.
-/
lemma colim.map_mono' [HasColimitsOfShape J C]
    [(colim : (J ⥤ C) ⥤ C).PreservesMonomorphisms]
    {X₁ X₂ : J ⥤ C} (φ : X₁ ⟶ X₂) [Mono φ]
    {c₁ : Cocone X₁} (hc₁ : IsColimit c₁) {c₂ : Cocone X₂} (hc₂ : IsColimit c₂)
    (f : c₁.pt ⟶ c₂.pt) (hf : ∀ j, c₁.ι.app j ≫ f = φ.app j ≫ c₂.ι.app j) : Mono f := by
  refine ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff ?_).2
    ((inferInstance : Mono (colim.map φ)))
  exact Arrow.isoMk
    (IsColimit.coconePointUniqueUpToIso hc₁ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₂ (colimit.isColimit _))
    (hc₁.hom_ext (fun j ↦ by
      dsimp
      rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
        colimit.cocone_ι, ι_colimMap, reassoc_of% (hf j),
        IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι]))

set_option backward.isDefEq.respectTransparency false in
/-- Assume that `φ : X₁ ⟶ X₂` is a natural transformation in `J ⥤ C` which
consists of epimorphisms, then if `f : c₁.pt ⟶ c₂.pt` is a morphism
between the points of cocones `c₁` and `c₂` for `X₁` and `X₂`, in such
a way that `c₂` is colimit and `f` is compatible with `φ`, then `f` is an epimorphism. -/
/-
**CategoryTheory.Limits.colim.map_epi'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.colim`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} J]   {X₁ X₂ : CategoryTheory.Functor J C
} (φ : X₁ ⟶ X₂) [∀ (j : J), CategoryTheory.Epi (φ.app j)]   (c₁ : CategoryTheory
.Limits.Cocone X₁) {c₂ : CategoryTheory.Limits.Cocone X₂}   (hc₂ : CategoryTheor
y.Limits.IsColimit c₂) (f : c₁.pt ⟶ c₂.pt),   (∀ (j : J),       CategoryTheory.C
ategoryStruct.comp (c₁.ι.app j) f = CategoryTheory.CategoryStruct.comp (φ.app j)
 (c₂.ι.app j)) →     CategoryTheory.Epi f
参数：φ : X₁ ⟶ X₂；j : J；φ.app j；c₁ : CategoryTheory.Limits.Cocone X₁；hc₂ : Category
Theory.Limits.IsColimit c₂；f : c₁.pt ⟶ c₂.pt；∀ (j : J),       CategoryTheory.Cat
egoryStruct.comp (c₁.ι.app j) f = CategoryTheory.CategoryStruct.comp (φ.app j) (
c₂.ι.app j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h

--- 原说明 ---
Assume that `φ : X₁ ⟶ X₂` is a natural transformation in `J ⥤ C` which
consists of epimorphisms, then if `f : c₁.pt ⟶ c₂.pt` is a morphism
between the points of cocones `c₁` and `c₂` for `X₁` and `X₂`, in such
a way that `c₂` is colimit and `f` is compatible with `φ`, then `f` is an epimor
phism.
-/
lemma colim.map_epi'
    {X₁ X₂ : J ⥤ C} (φ : X₁ ⟶ X₂) [∀ j, Epi (φ.app j)]
    (c₁ : Cocone X₁) {c₂ : Cocone X₂} (hc₂ : IsColimit c₂)
    (f : c₁.pt ⟶ c₂.pt) (hf : ∀ j, c₁.ι.app j ≫ f = φ.app j ≫ c₂.ι.app j) : Epi f where
  left_cancellation {Z} g₁ g₂ h := hc₂.hom_ext (fun j ↦ by
    rw [← cancel_epi (φ.app j), ← reassoc_of% hf, h, reassoc_of% hf])

attribute [local instance] IsFiltered.isConnected

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Assume that a functor `X : J ⥤ C` maps any morphism to a monomorphism,
that `J` is filtered. Then the "inclusion" map `c.ι.app j₀` of a colimit cocone for `X`
is a monomorphism if `colim : (Under j₀ ⥤ C) ⥤ C` preserves monomorphisms
(e.g. when `C` satisfies AB5). -/
/-
**CategoryTheory.Limits.IsColimit.mono_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assume that a functor `X : J ⥤ C` maps any morphism to a monomorphism,
that `J` is filtered. Then the "inclusion" map `c.ι.app j₀` of a colimit cocone 
for `X`
is a monomorphism if `colim : (Under j₀ ⥤ C) ⥤ C` preserves monomorphisms
(e.g. when `C` satisfies AB5).
-/
lemma IsColimit.mono_ι_app_of_isFiltered
    {X : J ⥤ C} [∀ (j j' : J) (φ : j ⟶ j'), Mono (X.map φ)]
    {c : Cocone X} (hc : IsColimit c) [IsFiltered J] (j₀ : J)
    [HasColimitsOfShape (Under j₀) C]
    [(colim : (Under j₀ ⥤ C) ⥤ C).PreservesMonomorphisms] :
    Mono (c.ι.app j₀) := by
  let f : (Functor.const _).obj (X.obj j₀) ⟶ Under.forget j₀ ⋙ X :=
    { app j := X.map j.hom
      naturality _ _ g := by
        dsimp
        simp only [Category.id_comp, ← X.map_comp, Under.w] }
  have := NatTrans.mono_of_mono_app f
  exact colim.map_mono' f (isColimitConstCocone _ _)
    ((Functor.Final.isColimitWhiskerEquiv _ _).symm hc) (c.ι.app j₀) (by cat_disch)

section

variable [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] [HasZeroMorphisms C]
  (S : ShortComplex (J ⥤ C)) (hS : S.Exact)
  {c₁ : Cocone S.X₁} (hc₁ : IsColimit c₁) (c₂ : Cocone S.X₂) (hc₂ : IsColimit c₂)
  (c₃ : Cocone S.X₃) (hc₃ : IsColimit c₃)
  (f : c₁.pt ⟶ c₂.pt) (g : c₂.pt ⟶ c₃.pt)
  (hf : ∀ j, c₁.ι.app j ≫ f = S.f.app j ≫ c₂.ι.app j)
  (hg : ∀ j, c₂.ι.app j ≫ g = S.g.app j ≫ c₃.ι.app j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given `S : ShortComplex (J ⥤ C)` and (colimit) cocones for `S.X₁`, `S.X₂`,
`S.X₃` equipped with suitable data, this is the induced
short complex `c₁.pt ⟶ c₂.pt ⟶ c₃.pt`. -/
@[simps]
/-
**CategoryTheory.Limits.colim.mapShortComplex** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.colim`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v', u'} J] →         [inst_2 : C
ategoryTheory.Limits.HasZeroMorphisms C] →           (S : CategoryTheory.ShortCo
mplex (CategoryTheory.Functor J C)) →             {c₁ : CategoryTheory.Limits.Co
cone S.X₁} →               CategoryTheory.Limits.IsColimit c₁ →                 
(c₂ : CategoryTheory.Limits.Cocone S.X₂) →                   (c₃ : CategoryTheor
y.Limits.Cocone S.X₃) →                     (f : c₁.pt ⟶ c₂.pt) →               
        (g : c₂.pt ⟶ c₃.pt) →                         (∀ (j : J),               
              CategoryTheory.CategoryStruct.comp (c₁.ι.app j) f =               
                CategoryTheory.CategoryStruct.comp (S.f.app j) (c₂.ι.app j)) →  
                         (∀ (j : J),                               CategoryTheor
y.CategoryStruct.comp (c₂.ι.app j) g =                                 CategoryT
heory.CategoryStruct.comp (S.g.app j) (c₃.ι.app j)) →                           
  CategoryTheory.ShortComplex C
参数：S : CategoryTheory.ShortComplex (CategoryTheory.Functor J C)；c₂ : CategoryThe
ory.Limits.Cocone S.X₂；c₃ : CategoryTheory.Limits.Cocone S.X₃；f : c₁.pt ⟶ c₂.pt；
g : c₂.pt ⟶ c₃.pt；∀ (j : J),                             CategoryTheory.Category
Struct.comp (c₁.ι.app j) f =                               CategoryTheory.Catego
ryStruct.comp (S.f.app j) (c₂.ι.app j)；∀ (j : J),                               
CategoryTheory.CategoryStruct.comp (c₂.ι.app j) g =                             
    CategoryTheory.CategoryStruct.comp (S.g.app j) (c₃.ι.app j)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `S : ShortComplex (J ⥤ C)` and (colimit) cocones for `S.X₁`, `S.X₂`,
`S.X₃` equipped with suitable data, this is the induced
short complex `c₁.pt ⟶ c₂.pt ⟶ c₃.pt`.
-/
def colim.mapShortComplex : ShortComplex C :=
  ShortComplex.mk f g (hc₁.hom_ext (fun j ↦ by
    rw [reassoc_of% (hf j), hg j, comp_zero, ← NatTrans.comp_app_assoc, S.zero,
      zero_app, zero_comp]))

variable {S c₂ c₃}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc₂ hc₃ hS in
/-- Assuming `HasExactColimitsOfShape J C`, this lemma rephrases the exactness
of the functor `colim : (J ⥤ C) ⥤ C` by saying that if `S : ShortComplex (J ⥤ C)`
is exact, then the short complex obtained by taking the colimits is exact,
where we allow the replacement of the chosen colimit cocones of the
colimit API by arbitrary colimit cocones. -/
/-
**CategoryTheory.Limits.colim.exact_mapShortComplex** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.colim`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} J]   [inst_2 : CategoryTheory.Limits.Has
ColimitsOfShape J C] [CategoryTheory.HasExactColimitsOfShape J C]   [inst_4 : Ca
tegoryTheory.Limits.HasZeroMorphisms C] {S : CategoryTheory.ShortComplex (Catego
ryTheory.Functor J C)},   S.Exact →     ∀ {c₁ : CategoryTheory.Limits.Cocone S.X
₁} (hc₁ : CategoryTheory.Limits.IsColimit c₁)       {c₂ : CategoryTheory.Limits.
Cocone S.X₂} (hc₂ : CategoryTheory.Limits.IsColimit c₂)       {c₃ : CategoryTheo
ry.Limits.Cocone S.X₃} (hc₃ : CategoryTheory.Limits.IsColimit c₃) (f : c₁.pt ⟶ c
₂.pt)       (g : c₂.pt ⟶ c₃.pt)       (hf :         ∀ (j : J),           Categor
yTheory.CategoryStruct.comp (c₁.ι.app j) f =             CategoryTheory.Category
Struct.comp (S.f.app j) (c₂.ι.app j))       (hg :         ∀ (j : J),           C
ategoryTheory.CategoryStruct.comp (c₂.ι.app j) g =             CategoryTheory.Ca
tegoryStruct.comp (S.g.app j) (c₃.ι.app j)),       (CategoryTheory.Limits.colim.
mapShortComplex S hc₁ c₂ c₃ f g hf hg).Exact
参数：CategoryTheory.Functor J C；hc₁ : CategoryTheory.Limits.IsColimit c₁；hc₂ : Cat
egoryTheory.Limits.IsColimit c₂；hc₃ : CategoryTheory.Limits.IsColimit c₃；f : c₁.
pt ⟶ c₂.pt；g : c₂.pt ⟶ c₃.pt；hf :         ∀ (j : J),           CategoryTheory.Ca
tegoryStruct.comp (c₁.ι.app j) f =             CategoryTheory.CategoryStruct.com
p (S.f.app j) (c₂.ι.app j)；hg :         ∀ (j : J),           CategoryTheory.Cate
goryStruct.comp (c₂.ι.app j) g =             CategoryTheory.CategoryStruct.comp 
(S.g.app j) (c₃.ι.app j)；CategoryTheory.Limits.colim.mapShortComplex S hc₁ c₂ c₃
 f g hf hg。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_isLeftAdjoint`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Limits.instIsLeftAdjointFunctorColim`：∀ {J : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.C
ategory.{v, u} C]   [inst_2 : CategoryThe…
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_of_iso`：exact_iff_of_iso (e : S₁ ≅
 S₂) : S₁.Exact ↔ S₂.Exact
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom_assoc`
：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst
_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.colimit.cocone_ι`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.ShortComplex.Exact.map`：∀ {C : Type u_1} {D : Type u_2} [
inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category
.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.preservesFiniteLimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
Assuming `HasExactColimitsOfShape J C`, this lemma rephrases the exactness
of the functor `colim : (J ⥤ C) ⥤ C` by saying that if `S : ShortComplex (J ⥤ C)
`
is exact, then the short complex obtained by taking the colimits is exact,
where we allow the replacement of the chosen colimit cocones of the
colimit API by arbitrary colimit cocones.
-/
lemma colim.exact_mapShortComplex :
    (mapShortComplex S hc₁ c₂ c₃ f g hf hg).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 (hS.map colim)
  refine ShortComplex.isoMk
    (IsColimit.coconePointUniqueUpToIso hc₁ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₂ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₃ (colimit.isColimit _))
    (hc₁.hom_ext (fun j ↦ ?_)) (hc₂.hom_ext (fun j ↦ ?_))
  · dsimp
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
      colimit.cocone_ι, ι_colimMap, reassoc_of% (hf j),
      IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι]
  · dsimp
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
      colimit.cocone_ι, ι_colimMap, reassoc_of% (hg j),
      IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι]

end

end Limits

namespace MorphismProperty

open Limits

open MorphismProperty

variable (J C) in
/-
**CategoryTheory.MorphismProperty.isStableUnderColimitsOfShape_monomorphisms** 是
 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isStableUnderColimitsOfShape_monomorphisms [HasColimitsOfShape J C] [(coli
m : (J ⥤ C) ⥤ C).PreservesMonomorphisms] : (monomorphisms C).IsStableUnderColimi
tsOfShape J where condition X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
参数：colim : (J ⥤ C) ⥤ C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.mono_of_mono_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.colim.map_mono'`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {J : Type u'} [inst_1 : CategoryTheory.Category.{v', u'}
 J]   [inst_2 : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance isStableUnderColimitsOfShape_monomorphisms
    [HasColimitsOfShape J C] [(colim : (J ⥤ C) ⥤ C).PreservesMonomorphisms] :
    (monomorphisms C).IsStableUnderColimitsOfShape J where
  condition X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ := by
    have (j : J) : Mono (f.app j) := hf _
    have := NatTrans.mono_of_mono_app f
    apply colim.map_mono' f hc₁ hc₂ φ (by simp [hφ])
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasCoproducts.{u'} C] [AB4OfSize.{u'} C] :
    IsStableUnderCoproducts.{u'} (monomorphisms C) where
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFilteredColimitsOfSize.{v', u'} C] [AB5OfSize.{v', u'} C] :
    IsStableUnderFilteredColimits.{v', u'} (monomorphisms C) where
  isStableUnderColimitsOfShape J _ _ := by infer_instance

end MorphismProperty

end CategoryTheory

