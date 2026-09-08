/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preservation of Kan extensions

Given functors `F : A ⥤ B`, `L : B ⥤ C`, and `G : B ⥤ D`,
we introduce a typeclass `G.PreservesLeftKanExtension F L` which encodes the fact that
the left Kan extension of `F` along `L` is preserved by the functor `G`.

When the Kan extension is pointwise, it suffices that `G` preserves (co)limits of the relevant
diagrams.

We introduce the dual typeclass `G.PreservesRightKanExtension`.

-/

@[expose] public section

namespace CategoryTheory.Functor

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  (G : B ⥤ D) (F : A ⥤ B) (L : A ⥤ C)

noncomputable section

section LeftKanExtension

/-- `G.PreservesLeftKanExtension F L` asserts that `G` preserves all left Kan extensions
of `F` along `L`. See `PreservesLeftKanExtension.mk_of_preserves_isLeftKanExtension` for a
constructor taking a single left Kan extension as input. -/
/-
**CategoryTheory.Functor.PreservesLeftKanExtension** 是 Mathlib 中的一个归纳类型，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {C : Type u_3} →       {D : Type u
_4} →         [inst : CategoryTheory.Category.{v_1, u_1} A] →           [inst_1 
: CategoryTheory.Category.{v_2, u_2} B] →             [inst_2 : CategoryTheory.C
ategory.{v_3, u_3} C] →               [inst_3 : CategoryTheory.Category.{v_4, u_
4} D] →                 CategoryTheory.Functor B D → CategoryTheory.Functor A B 
→ CategoryTheory.Functor A C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.PreservesLeftKanExtension F L` asserts that `G` preserves all left Kan extens
ions
of `F` along `L`. See `PreservesLeftKanExtension.mk_of_preserves_isLeftKanExtens
ion` for a
constructor taking a single left Kan extension as input.
-/
class PreservesLeftKanExtension where
  preserves : ∀ (F' : C ⥤ B) (α : F ⟶ L ⋙ F') [IsLeftKanExtension F' α],
    IsLeftKanExtension (F' ⋙ G) <| whiskerRight α G ≫ (Functor.associator _ _ _).hom

/-- Alternative constructor for `PreservesLeftKanExtension`, phrased in terms of
`LeftExtension.IsUniversal` instead. See `PreservesLeftKanExtension.mk_of_preserves_isUniversal`
for a similar constructor taking as input a single `LeftExtension`. -/
/-
**CategoryTheory.Functor.PreservesLeftKanExtension.mk'** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor.PreservesLeftKanExtension`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} [inst : Cate
goryTheory.Category.{v_1, u_1} A]   [inst_1 : CategoryTheory.Category.{v_2, u_2}
 B] [inst_2 : CategoryTheory.Category.{v_3, u_3} C]   [inst_3 : CategoryTheory.C
ategory.{v_4, u_4} D] (G : CategoryTheory.Functor B D) (F : CategoryTheory.Funct
or A B)   (L : CategoryTheory.Functor A C),   (∀ {E : L.LeftExtension F} (a : Ca
tegoryTheory.StructuredArrow.IsUniversal E),       Nonempty         (CategoryThe
ory.StructuredArrow.IsUniversal           ((CategoryTheory.Functor.LeftExtension
.postcompose₂ L F G).obj E))) →     G.PreservesLeftKanExtension F L
参数：G : CategoryTheory.Functor B D；F : CategoryTheory.Functor A B；L : CategoryThe
ory.Functor A C；∀ {E : L.LeftExtension F} (a : CategoryTheory.StructuredArrow.Is
Universal E),       Nonempty         (CategoryTheory.StructuredArrow.IsUniversal
           ((CategoryTheory.Functor.LeftExtension.postcompose₂ L F G).obj E))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLeftKanExtension.nonempty_isUniversal`：∀ {C : T
ype u_1} {H : Type u_3} {D : Type u_4} {inst : CategoryTheory.Category.{v_1, u_1
} C}   {inst_1 : CategoryTheory.Category.{v_3, u_3} …

--- 原说明 ---
Alternative constructor for `PreservesLeftKanExtension`, phrased in terms of
`LeftExtension.IsUniversal` instead. See `PreservesLeftKanExtension.mk_of_preser
ves_isUniversal`
for a similar constructor taking as input a single `LeftExtension`.
-/
lemma PreservesLeftKanExtension.mk'
    (preserves : ∀ {E : LeftExtension L F}, E.IsUniversal →
      Nonempty (LeftExtension.postcompose₂ L F G |>.obj E).IsUniversal) :
    G.PreservesLeftKanExtension F L where
  preserves _ _ h :=
    ⟨⟨Limits.IsInitial.equivOfIso
        (LeftExtension.postcompose₂ObjMkIso _ _) <| (preserves h.nonempty_isUniversal.some).some⟩⟩

/-- Show that `G` preserves left Kan extensions if it maps some left Kan extension to a left
Kan extension. -/
/-
**CategoryTheory.Functor.PreservesLeftKanExtension.mk_of_preserves_isLeftKanExte
nsion** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.PreservesLeftKanExtensio
n`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} [inst : Cate
goryTheory.Category.{v_1, u_1} A]   [inst_1 : CategoryTheory.Category.{v_2, u_2}
 B] [inst_2 : CategoryTheory.Category.{v_3, u_3} C]   [inst_3 : CategoryTheory.C
ategory.{v_4, u_4} D] (G : CategoryTheory.Functor B D) (F : CategoryTheory.Funct
or A B)   (L : CategoryTheory.Functor A C) (F' : CategoryTheory.Functor C B) (α 
: F ⟶ L.comp F') [F'.IsLeftKanExtension α],   (F'.comp G).IsLeftKanExtension    
   (CategoryTheory.CategoryStruct.comp (CategoryTheory.Functor.whiskerRight α G)
 (L.associator F' G).hom) →     G.PreservesLeftKanExtension F L
参数：G : CategoryTheory.Functor B D；F : CategoryTheory.Functor A B；L : CategoryThe
ory.Functor A C；F' : CategoryTheory.Functor C B；α : F ⟶ L.comp F'；F'.comp G；Cate
goryTheory.CategoryStruct.comp (CategoryTheory.Functor.whiskerRight α G) (L.asso
ciator F' G).hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isLeftKanExtension_of_iso`：isLeftKanExtension_of_
iso {F' : D ⥤ H} {F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L
 ⋙ F') (α' : F ⟶ L ⋙ F'') (comm : α ≫ …
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.leftKanExtensionUnique_hom`：∀ {C : Type u_1} {H :
 Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac_app`：descOfIsLeftKan
Extension_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) : α.app X ≫ (F'.descOfIsLe
ftKanExtension α G β).app (L.obj X) = β.app X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Show that `G` preserves left Kan extensions if it maps some left Kan extension t
o a left
Kan extension.
-/
lemma PreservesLeftKanExtension.mk_of_preserves_isLeftKanExtension
    (F' : C ⥤ B) (α : F ⟶ L ⋙ F') [IsLeftKanExtension F' α]
    (h : IsLeftKanExtension (F' ⋙ G) <| whiskerRight α G ≫ (Functor.associator _ _ _).hom) :
    G.PreservesLeftKanExtension F L :=
  .mk fun F'' α' h ↦
    isLeftKanExtension_of_iso
      (isoWhiskerRight (leftKanExtensionUnique F' α F'' α') G)
      (whiskerRight α G ≫ (Functor.associator _ _ _).hom)
      (whiskerRight α' G ≫ (Functor.associator _ _ _).hom)
      (by ext x; simp [← G.map_comp])

/-- Show that `G` preserves left Kan extensions if it maps some left Kan extension to a left
Kan extension, phrased in terms of `IsUniversal`. -/
/-
**CategoryTheory.Functor.PreservesLeftKanExtension.mk_of_preserves_isUniversal**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.PreservesLeftKanExtension`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} [inst : Cate
goryTheory.Category.{v_1, u_1} A]   [inst_1 : CategoryTheory.Category.{v_2, u_2}
 B] [inst_2 : CategoryTheory.Category.{v_3, u_3} C]   [inst_3 : CategoryTheory.C
ategory.{v_4, u_4} D] (G : CategoryTheory.Functor B D) (F : CategoryTheory.Funct
or A B)   (L : CategoryTheory.Functor A C) (E : L.LeftExtension F) (hE : Categor
yTheory.StructuredArrow.IsUniversal E),   Nonempty       (CategoryTheory.Structu
redArrow.IsUniversal ((CategoryTheory.Functor.LeftExtension.postcompose₂ L F G).
obj E)) →     G.PreservesLeftKanExtension F L
参数：G : CategoryTheory.Functor B D；F : CategoryTheory.Functor A B；L : CategoryThe
ory.Functor A C；E : L.LeftExtension F；hE : CategoryTheory.StructuredArrow.IsUniv
ersal E；CategoryTheory.StructuredArrow.IsUniversal ((CategoryTheory.Functor.Left
Extension.postcompose₂ L F G).obj E)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesLeftKanExtension.mk'`：∀ {A : Type u_1} {
B : Type u_2} {C : Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1
, u_1} A]   [inst_1 : CategoryTheory.Categ…

--- 原说明 ---
Show that `G` preserves left Kan extensions if it maps some left Kan extension t
o a left
Kan extension, phrased in terms of `IsUniversal`.
-/
lemma PreservesLeftKanExtension.mk_of_preserves_isUniversal (E : LeftExtension L F)
    (hE : E.IsUniversal) (h : Nonempty (LeftExtension.postcompose₂ L F G |>.obj E).IsUniversal) :
    G.PreservesLeftKanExtension F L :=
  .mk' G F L fun hE' ↦
    ⟨Limits.IsInitial.equivOfIso
      (LeftExtension.postcompose₂ L F G|>.mapIso <| Limits.IsInitial.uniqueUpToIso hE hE') h.some⟩

attribute [instance] PreservesLeftKanExtension.preserves

/-- `G.PreservesLeftKanExtensionAt F L c` asserts that `G` preserves all pointwise left Kan
extensions of `F` along `L` at the point `c`. -/
/-
**CategoryTheory.Functor.PreservesPointwiseLeftKanExtensionAt** 是 Mathlib 中的一个归纳
类型，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {C : Type u_3} →       {D : Type u
_4} →         [inst : CategoryTheory.Category.{v_1, u_1} A] →           [inst_1 
: CategoryTheory.Category.{v_2, u_2} B] →             [inst_2 : CategoryTheory.C
ategory.{v_3, u_3} C] →               [inst_3 : CategoryTheory.Category.{v_4, u_
4} D] →                 CategoryTheory.Functor B D → CategoryTheory.Functor A B 
→ CategoryTheory.Functor A C → C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.PreservesLeftKanExtensionAt F L c` asserts that `G` preserves all pointwise l
eft Kan
extensions of `F` along `L` at the point `c`.
-/
class PreservesPointwiseLeftKanExtensionAt (c : C) where
  /-- `G` preserves every pointwise extensions of `F` along `L` at `c`. -/
  preserves : ∀ (E : LeftExtension L F), E.IsPointwiseLeftKanExtensionAt c →
    Nonempty ((LeftExtension.postcompose₂ L F G |>.obj E).IsPointwiseLeftKanExtensionAt c)

/-- `G.PreservesLeftKanExtension F L` asserts that `G` preserves all pointwise left Kan extensions
of `F` along `L`. -/
/-
**CategoryTheory.Functor.PreservesPointwiseLeftKanExtension** 是 Mathlib 中的一个缩写定义
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：PreservesPointwiseLeftKanExtension
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.PreservesLeftKanExtension F L` asserts that `G` preserves all pointwise left 
Kan extensions
of `F` along `L`.
-/
abbrev PreservesPointwiseLeftKanExtension := ∀ c : C, PreservesPointwiseLeftKanExtensionAt G F L c

variable {F L} in
/-- Given a pointwise left Kan extension of `F` along `L` at `c`, exhibits
`(LeftExtension.whiskerRight L F G).obj E` as a pointwise left Kan extension of `F ⋙ G` along
`L` at `c`. -/
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.postcompose
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeft
KanExtensionAt`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {C : Type u_3} →       {D : Type u
_4} →         [inst : CategoryTheory.Category.{v_1, u_1} A] →           [inst_1 
: CategoryTheory.Category.{v_2, u_2} B] →             [inst_2 : CategoryTheory.C
ategory.{v_3, u_3} C] →               [inst_3 : CategoryTheory.Category.{v_4, u_
4} D] →                 (G : CategoryTheory.Functor B D) →                   {F 
: CategoryTheory.Functor A B} →                     {L : CategoryTheory.Functor 
A C} →                       {c : C} →                         [G.PreservesPoint
wiseLeftKanExtensionAt F L c] →                           {E : L.LeftExtension F
} →                             E.IsPointwiseLeftKanExtensionAt c →             
                  ((CategoryTheory.Functor.LeftExtension.postcompose₂ L F G).obj
                                     E).IsPointwiseLeftKanExtensionAt           
                      c
参数：G : CategoryTheory.Functor B D；(CategoryTheory.Functor.LeftExtension.postcomp
ose₂ L F G).obj                                     E。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesPointwiseLeftKanExtensionAt.preserves`：∀
 {A : Type u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} {inst : CategoryThe
ory.Category.{v_1, u_1} A}   {inst_1 : CategoryTheory.Categ…

--- 原说明 ---
Given a pointwise left Kan extension of `F` along `L` at `c`, exhibits
`(LeftExtension.whiskerRight L F G).obj E` as a pointwise left Kan extension of 
`F ⋙ G` along
`L` at `c`.
-/
def LeftExtension.IsPointwiseLeftKanExtensionAt.postcompose {c : C}
    [PreservesPointwiseLeftKanExtensionAt G F L c]
    {E : LeftExtension L F} (hE : E.IsPointwiseLeftKanExtensionAt c) :
    LeftExtension.postcompose₂ L F G |>.obj E |>.IsPointwiseLeftKanExtensionAt c :=
  PreservesPointwiseLeftKanExtensionAt.preserves E hE |>.some

variable {F L} in
/-- Given a pointwise left Kan extension of `F` along `L`, exhibits
`(LeftExtension.whiskerRight L F G).obj E` as a pointwise left Kan extension of `F ⋙ G` along
`L`. -/
/-
**CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.postcompose**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKa
nExtension`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {C : Type u_3} →       {D : Type u
_4} →         [inst : CategoryTheory.Category.{v_1, u_1} A] →           [inst_1 
: CategoryTheory.Category.{v_2, u_2} B] →             [inst_2 : CategoryTheory.C
ategory.{v_3, u_3} C] →               [inst_3 : CategoryTheory.Category.{v_4, u_
4} D] →                 (G : CategoryTheory.Functor B D) →                   {F 
: CategoryTheory.Functor A B} →                     {L : CategoryTheory.Functor 
A C} →                       [G.PreservesPointwiseLeftKanExtension F L] →       
                  {E : L.LeftExtension F} →                           E.IsPointw
iseLeftKanExtension →                             ((CategoryTheory.Functor.LeftE
xtension.postcompose₂ L F G).obj                                 E).IsPointwiseL
eftKanExtension
参数：G : CategoryTheory.Functor B D；(CategoryTheory.Functor.LeftExtension.postcomp
ose₂ L F G).obj                                 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a pointwise left Kan extension of `F` along `L`, exhibits
`(LeftExtension.whiskerRight L F G).obj E` as a pointwise left Kan extension of 
`F ⋙ G` along
`L`.
-/
def LeftExtension.IsPointwiseLeftKanExtension.postcompose
    [PreservesPointwiseLeftKanExtension G F L]
    {E : LeftExtension L F} (hE : E.IsPointwiseLeftKanExtension) :
    LeftExtension.postcompose₂ L F G |>.obj E |>.IsPointwiseLeftKanExtension := fun c ↦
  (hE c).postcompose G

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The cocone at a point of the whiskering right by `G` of an extension is isomorphic to the
action of `G` on the cocone at that point for the original extension. -/
@[simps!]
/-
**CategoryTheory.Functor.LeftExtension.coconeAtWhiskerRightIso** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Functor.LeftExtension`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {C : Type u_3} →       {D : Type u
_4} →         [inst : CategoryTheory.Category.{v_1, u_1} A] →           [inst_1 
: CategoryTheory.Category.{v_2, u_2} B] →             [inst_2 : CategoryTheory.C
ategory.{v_3, u_3} C] →               [inst_3 : CategoryTheory.Category.{v_4, u_
4} D] →                 (G : CategoryTheory.Functor B D) →                   (F 
: CategoryTheory.Functor A B) →                     (L : CategoryTheory.Functor 
A C) →                       (E : L.LeftExtension F) →                         (
c : C) →                           ((CategoryTheory.Functor.LeftExtension.postco
mpose₂ L F G).obj E).coconeAt c ≅                             G.mapCocone (E.coc
oneAt c)
参数：G : CategoryTheory.Functor B D；F : CategoryTheory.Functor A B；L : CategoryThe
ory.Functor A C；E : L.LeftExtension F；c : C；(CategoryTheory.Functor.LeftExtensio
n.postcompose₂ L F G).obj E；E.coconeAt c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone at a point of the whiskering right by `G` of an extension is isomorph
ic to the
action of `G` on the cocone at that point for the original extension.
-/
def LeftExtension.coconeAtWhiskerRightIso (E : LeftExtension L F) (c : C) :
    (LeftExtension.postcompose₂ L F G |>.obj E).coconeAt c ≅ G.mapCocone (E.coconeAt c) :=
  Limits.Cocone.ext (Iso.refl _)

/-- If `G` preserves any pointwise left Kan extension of `F` along `L` at `c`, then it preserves
all of them. -/
/-
**CategoryTheory.Functor.PreservesPointwiseLeftKanExtensionAt.mk'** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Functor.PreservesPointwiseLeftKanExtensionAt`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} [inst : Cate
goryTheory.Category.{v_1, u_1} A]   [inst_1 : CategoryTheory.Category.{v_2, u_2}
 B] [inst_2 : CategoryTheory.Category.{v_3, u_3} C]   [inst_3 : CategoryTheory.C
ategory.{v_4, u_4} D] (G : CategoryTheory.Functor B D) (F : CategoryTheory.Funct
or A B)   (L : CategoryTheory.Functor A C) (c : C) {E : L.LeftExtension F} (hE :
 E.IsPointwiseLeftKanExtensionAt c)   (hGE : ((CategoryTheory.Functor.LeftExtens
ion.postcompose₂ L F G).obj E).IsPointwiseLeftKanExtensionAt c),   G.PreservesPo
intwiseLeftKanExtensionAt F L c
参数：G : CategoryTheory.Functor B D；F : CategoryTheory.Functor A B；L : CategoryThe
ory.Functor A C；c : C；hE : E.IsPointwiseLeftKanExtensionAt c；hGE : ((CategoryThe
ory.Functor.LeftExtension.postcompose₂ L F G).obj E).IsPointwiseLeftKanExtension
At c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves any pointwise left Kan extension of `F` along `L` at `c`, then 
it preserves
all of them.
-/
lemma PreservesPointwiseLeftKanExtensionAt.mk' (c : C) {E : LeftExtension L F}
    (hE : E.IsPointwiseLeftKanExtensionAt c)
    (hGE : (LeftExtension.postcompose₂ L F G |>.obj E).IsPointwiseLeftKanExtensionAt c) :
    G.PreservesPointwiseLeftKanExtensionAt F L c where
  preserves E' hE' :=
    ⟨Limits.IsColimit.ofIsoColimit hGE <|
      (E.coconeAtWhiskerRightIso G F L c) ≪≫
        (Limits.Cocone.functoriality _ _).mapIso (hE.uniqueUpToIso hE') ≪≫
        (E'.coconeAtWhiskerRightIso G F L c).symm⟩
/-
**CategoryTheory.Functor.hasLeftKanExtension_of_preserves** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：hasLeftKanExtension_of_preserves [L.HasLeftKanExtension F] [PreservesLeftK
anExtension G F L] : L.HasLeftKanExtension (F ⋙ G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.HasLeftKanExtension.mk`：∀ {C : Type u_1} {H : Typ
e u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : 
CategoryTheory.Category.{v_3, u_3} …
· 使用定理 `CategoryTheory.Functor.PreservesLeftKanExtension.preserves`：∀ {A : Type 
u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} {inst : CategoryTheory.Categor
y.{v_1, u_1} A}   {inst_1 : CategoryTheory.Categ…
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionLeftKanExtensionLeftKanExte
nsionUnit`：∀ {C : Type u_1} {H : Type u_3} {D : Type u_4} [inst : CategoryTheory
.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} …
-/
instance hasLeftKanExtension_of_preserves [L.HasLeftKanExtension F]
    [PreservesLeftKanExtension G F L] : L.HasLeftKanExtension (F ⋙ G) :=
  @HasLeftKanExtension.mk _ _ _ _ _ _ _ _ _ _ <|
    letI : (L.leftKanExtension F).IsLeftKanExtension <| L.leftKanExtensionUnit F := by
      infer_instance
    PreservesLeftKanExtension.preserves (L.leftKanExtension F) (L.leftKanExtensionUnit F)
/-
**CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_preserves** 是 Mathlib 中
的一个实例，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseLeftKanExtension_of_preserves [L.HasPointwiseLeftKanExtension 
F] [PreservesPointwiseLeftKanExtension G F L] : L.HasPointwiseLeftKanExtension (
F ⋙ G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.hasPoin
twiseLeftKanExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_
2} …
-/
instance hasPointwiseLeftKanExtension_of_preserves [L.HasPointwiseLeftKanExtension F]
    [PreservesPointwiseLeftKanExtension G F L] : L.HasPointwiseLeftKanExtension (F ⋙ G) :=
  (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
    L F |>.postcompose G).hasPointwiseLeftKanExtension

/-- Extract an isomorphism `(leftKanExtension L F) ⋙ G ≅ leftKanExtension L (F ⋙ G)` when `G`
preserves left Kan extensions. -/
/-
**CategoryTheory.Functor.leftKanExtensionCompIsoOfPreserves** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：leftKanExtensionCompIsoOfPreserves [PreservesLeftKanExtension G F L] [L.Ha
sLeftKanExtension F] : L.leftKanExtension F ⋙ G ≅ L.leftKanExtension (F ⋙ G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract an isomorphism `(leftKanExtension L F) ⋙ G ≅ leftKanExtension L (F ⋙ G)`
 when `G`
preserves left Kan extensions.
-/
def leftKanExtensionCompIsoOfPreserves [PreservesLeftKanExtension G F L]
    [L.HasLeftKanExtension F] :
    L.leftKanExtension F ⋙ G ≅ L.leftKanExtension (F ⋙ G) :=
  leftKanExtensionUnique
    (L.leftKanExtension F ⋙ G)
    (whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
    (L.leftKanExtension <| F ⋙ G)
    (L.leftKanExtensionUnit <| F ⋙ G)

section

variable [PreservesLeftKanExtension G F L] [L.HasLeftKanExtension F]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.leftKanExtensionCompIsoOfPreserves_hom_fac** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：leftKanExtensionCompIsoOfPreserves_hom_fac : whiskerRight (L.leftKanExtens
ionUnit F) G ≫ (Functor.associator _ _ _).hom ≫ whiskerLeft L (leftKanExtensionC
ompIsoOfPreserves G F L).hom = (L.leftKanExtensionUnit <| F ⋙ G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.leftKanExtensionUnique_hom`：∀ {C : Type u_1} {H :
 Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} …
· 使用定理 `CategoryTheory.Functor.PreservesLeftKanExtension.preserves`：∀ {A : Type 
u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} {inst : CategoryTheory.Categor
y.{v_1, u_1} A}   {inst_1 : CategoryTheory.Categ…
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionLeftKanExtensionLeftKanExte
nsionUnit`：∀ {C : Type u_1} {H : Type u_3} {D : Type u_4} [inst : CategoryTheory
.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac`：descOfIsLeftKanExte
nsion_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (F'.descOfIsLeftKanExt
ension α G β) = β
-/
lemma leftKanExtensionCompIsoOfPreserves_hom_fac :
    whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom ≫
      whiskerLeft L (leftKanExtensionCompIsoOfPreserves G F L).hom =
    (L.leftKanExtensionUnit <| F ⋙ G) := by
  simpa [leftKanExtensionCompIsoOfPreserves] using
    descOfIsLeftKanExtension_fac
      (α := whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
      (β := L.leftKanExtensionUnit (F ⋙ G))

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.leftKanExtensionCompIsoOfPreserves_hom_fac_app** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：leftKanExtensionCompIsoOfPreserves_hom_fac_app (a : A) : G.map ((L.leftKan
ExtensionUnit F).app a) ≫ (G.leftKanExtensionCompIsoOfPreserves F L).hom.app (L.
obj a) = (L.leftKanExtensionUnit (F ⋙ G)).app a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.Functor.leftKanExtensionCompIsoOfPreserves_hom_fac`：leftK
anExtensionCompIsoOfPreserves_hom_fac : whiskerRight (L.leftKanExtensionUnit F) 
G ≫ (Functor.associator _ _ _).hom ≫ whiskerLeft L (lef…
-/
lemma leftKanExtensionCompIsoOfPreserves_hom_fac_app (a : A) :
    G.map ((L.leftKanExtensionUnit F).app a) ≫
      (G.leftKanExtensionCompIsoOfPreserves F L).hom.app (L.obj a) =
    (L.leftKanExtensionUnit (F ⋙ G)).app a := by
  simpa [-leftKanExtensionCompIsoOfPreserves_hom_fac] using
    NatTrans.congr_app (leftKanExtensionCompIsoOfPreserves_hom_fac G F L) a

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.leftKanExtensionCompIsoOfPreserves_inv_fac** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：leftKanExtensionCompIsoOfPreserves_inv_fac : (L.leftKanExtensionUnit <| F 
⋙ G) ≫ whiskerLeft L (leftKanExtensionCompIsoOfPreserves G F L).inv = whiskerRig
ht (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.leftKanExtensionUnique_inv`：∀ {C : Type u_1} {H :
 Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac`：descOfIsLeftKanExte
nsion_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (F'.descOfIsLeftKanExt
ension α G β) = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftKanExtensionCompIsoOfPreserves_inv_fac :
    (L.leftKanExtensionUnit <| F ⋙ G) ≫
      whiskerLeft L (leftKanExtensionCompIsoOfPreserves G F L).inv =
    whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom := by
  simp [leftKanExtensionCompIsoOfPreserves]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.leftKanExtensionCompIsoOfPreserves_inv_fac_app** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：leftKanExtensionCompIsoOfPreserves_inv_fac_app (a : A) : (L.leftKanExtensi
onUnit (F ⋙ G)).app a ≫ (G.leftKanExtensionCompIsoOfPreserves F L).inv.app (L.ob
j a) = G.map ((L.leftKanExtensionUnit F).app a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.Functor.leftKanExtensionCompIsoOfPreserves_inv_fac`：leftK
anExtensionCompIsoOfPreserves_inv_fac : (L.leftKanExtensionUnit <| F ⋙ G) ≫ whis
kerLeft L (leftKanExtensionCompIsoOfPreserves G F L).in…
-/
lemma leftKanExtensionCompIsoOfPreserves_inv_fac_app (a : A) :
    (L.leftKanExtensionUnit (F ⋙ G)).app a ≫
      (G.leftKanExtensionCompIsoOfPreserves F L).inv.app (L.obj a) =
    G.map ((L.leftKanExtensionUnit F).app a) := by
  simpa [-leftKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (leftKanExtensionCompIsoOfPreserves_inv_fac G F L) a

end

/-- A functor that preserves the colimit of `CostructuredArrow.proj L c ⋙ F` preserves
the pointwise left Kan extension of `F` along `L` at `c`. -/
/-
**CategoryTheory.Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit*
* 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesPointwiseLeftKanExtensionAtOfPreservesColimit (c : C) [Limits.Pre
servesColimit (CostructuredArrow.proj L c ⋙ F) G] : G.PreservesPointwiseLeftKanE
xtensionAt F L c where preserves E p
参数：c : C；CostructuredArrow.proj L c ⋙ F。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimit.preserves`：∀ {C : Type u₁} {inst 
: CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
A functor that preserves the colimit of `CostructuredArrow.proj L c ⋙ F` preserv
es
the pointwise left Kan extension of `F` along `L` at `c`.
-/
instance preservesPointwiseLeftKanExtensionAtOfPreservesColimit (c : C)
    [Limits.PreservesColimit (CostructuredArrow.proj L c ⋙ F) G] :
    G.PreservesPointwiseLeftKanExtensionAt F L c where
  preserves E p :=
    ⟨Limits.IsColimit.ofIsoColimit
      (Limits.PreservesColimit.preserves p).some
      (E.coconeAtWhiskerRightIso G _ _ c).symm⟩

/-- If there is a pointwise left Kan extension of `F` along `L`, and if `G` preserves them,
then `G` preserves left Kan extensions of `F` along `L`. -/
/-
**CategoryTheory.Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwis
e** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise [HasPointwiseLeft
KanExtension L F] [G.PreservesPointwiseLeftKanExtension F L] : G.PreservesLeftKa
nExtension F L where preserves F' α _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftK
anExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheo
ry.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …

--- 原说明 ---
If there is a pointwise left Kan extension of `F` along `L`, and if `G` preserve
s them,
then `G` preserves left Kan extensions of `F` along `L`.
-/
instance preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise
    [HasPointwiseLeftKanExtension L F] [G.PreservesPointwiseLeftKanExtension F L] :
    G.PreservesLeftKanExtension F L where
  preserves F' α _ :=
    (LeftExtension.isPointwiseLeftKanExtensionEquivOfIso (LeftExtension.postcompose₂ObjMkIso G α) <|
      (isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α).postcompose G).isLeftKanExtension

/-- Extract an isomorphism
`(pointwiseLeftKanExtension L F) ⋙ G ≅ pointwiseLeftKanExtension L (F ⋙ G)` when `G` preserves
left Kan extensions. -/
/-
**CategoryTheory.Functor.pointwiseLeftKanExtensionCompIsoOfPreserves** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseLeftKanExtensionCompIsoOfPreserves [PreservesPointwiseLeftKanExte
nsion G F L] [L.HasPointwiseLeftKanExtension F] : L.pointwiseLeftKanExtension F 
⋙ G ≅ L.pointwiseLeftKanExtension (F ⋙ G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract an isomorphism
`(pointwiseLeftKanExtension L F) ⋙ G ≅ pointwiseLeftKanExtension L (F ⋙ G)` when
 `G` preserves
left Kan extensions.
-/
def pointwiseLeftKanExtensionCompIsoOfPreserves
    [PreservesPointwiseLeftKanExtension G F L]
    [L.HasPointwiseLeftKanExtension F] :
    L.pointwiseLeftKanExtension F ⋙ G ≅ L.pointwiseLeftKanExtension (F ⋙ G) :=
  leftKanExtensionUnique
    (L.pointwiseLeftKanExtension F ⋙ G)
    (whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
    (L.pointwiseLeftKanExtension <| F ⋙ G)
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G)

section

variable [PreservesPointwiseLeftKanExtension G F L] [L.HasPointwiseLeftKanExtension F]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac : whiskerRight (L.poin
twiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom ≫ whiskerLeft L 
(pointwiseLeftKanExtensionCompIsoOfPreserves G F L).hom = (L.pointwiseLeftKanExt
ensionUnit <| F ⋙ G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.leftKanExtensionUnique_hom`：∀ {C : Type u_1} {H :
 Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} …
· 使用定理 `CategoryTheory.Functor.PreservesLeftKanExtension.preserves`：∀ {A : Type 
u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} {inst : CategoryTheory.Categor
y.{v_1, u_1} A}   {inst_1 : CategoryTheory.Categ…
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionPointwiseLeftKanExtensionPo
intwiseLeftKanExtensionUnit`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [ins
t : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v
_2, u_2} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac`：descOfIsLeftKanExte
nsion_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (F'.descOfIsLeftKanExt
ension α G β) = β
-/
lemma pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac :
    whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom ≫
      whiskerLeft L (pointwiseLeftKanExtensionCompIsoOfPreserves G F L).hom =
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G) := by
  simpa [pointwiseLeftKanExtensionCompIsoOfPreserves] using
    descOfIsLeftKanExtension_fac
      (α := whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
      (β := L.pointwiseLeftKanExtensionUnit <| F ⋙ G)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Functor.pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac_app
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac_app (a : A) : G.map ((
L.pointwiseLeftKanExtensionUnit F).app a) ≫ (G.pointwiseLeftKanExtensionCompIsoO
fPreserves F L).hom.app (L.obj a) = (L.pointwiseLeftKanExtensionUnit <| F ⋙ G).a
pp a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.Functor.pointwiseLeftKanExtensionCompIsoOfPreserves_hom_f
ac`：pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac : whiskerRight (L.pointw
iseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom ≫ …
-/
lemma pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac_app (a : A) :
    G.map ((L.pointwiseLeftKanExtensionUnit F).app a) ≫
      (G.pointwiseLeftKanExtensionCompIsoOfPreserves F L).hom.app (L.obj a) =
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G).app a := by
  simpa [-pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac] using
    NatTrans.congr_app (pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac G F L) a

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac : (L.pointwiseLeftKanE
xtensionUnit <| F ⋙ G) ≫ whiskerLeft L (pointwiseLeftKanExtensionCompIsoOfPreser
ves G F L).inv = whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.a
ssociator _ _ _).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.leftKanExtensionUnique_inv`：∀ {C : Type u_1} {H :
 Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac`：descOfIsLeftKanExte
nsion_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (F'.descOfIsLeftKanExt
ension α G β) = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac :
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G) ≫
      whiskerLeft L (pointwiseLeftKanExtensionCompIsoOfPreserves G F L).inv =
    whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom := by
  simp [pointwiseLeftKanExtensionCompIsoOfPreserves]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Functor.pointwiseLeftKanExtensionCompIsoOfPreserves_fac_app** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseLeftKanExtensionCompIsoOfPreserves_fac_app (a : A) : (L.pointwise
LeftKanExtensionUnit <| F ⋙ G).app a ≫ (G.pointwiseLeftKanExtensionCompIsoOfPres
erves F L).inv.app (L.obj a) = G.map (L.pointwiseLeftKanExtensionUnit F |>.app a
)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.Functor.pointwiseLeftKanExtensionCompIsoOfPreserves_inv_f
ac`：pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac : (L.pointwiseLeftKanExt
ensionUnit <| F ⋙ G) ≫ whiskerLeft L (pointwiseLeftKanExtensionC…
-/
lemma pointwiseLeftKanExtensionCompIsoOfPreserves_fac_app (a : A) :
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G).app a ≫
      (G.pointwiseLeftKanExtensionCompIsoOfPreserves F L).inv.app (L.obj a) =
    G.map (L.pointwiseLeftKanExtensionUnit F |>.app a) := by
  simpa [-pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac G F L) a

end

/-- `G.PreservesLeftKanExtensions L` means that `G : B ⥤ D` preserves all left Kan extensions along
`L : A ⥤ C` of every functor `A ⥤ B`. -/
/-
**CategoryTheory.Functor.PreservesLeftKanExtensions** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：PreservesLeftKanExtensions
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.PreservesLeftKanExtensions L` means that `G : B ⥤ D` preserves all left Kan e
xtensions along
`L : A ⥤ C` of every functor `A ⥤ B`.
-/
abbrev PreservesLeftKanExtensions := ∀ (F : A ⥤ B), G.PreservesLeftKanExtension F L

/-- `G.PreservesPointwiseLeftKanExtensions L` means that `G : B ⥤ D` preserves all pointwise left
Kan extensions along `L : A ⥤ C` of every functor `A ⥤ B`. -/
/-
**CategoryTheory.Functor.PreservesPointwiseLeftKanExtensions** 是 Mathlib 中的一个缩写定
义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：PreservesPointwiseLeftKanExtensions
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.PreservesPointwiseLeftKanExtensions L` means that `G : B ⥤ D` preserves all p
ointwise left
Kan extensions along `L : A ⥤ C` of every functor `A ⥤ B`.
-/
abbrev PreservesPointwiseLeftKanExtensions :=
  ∀ (F : A ⥤ B), G.PreservesPointwiseLeftKanExtension F L

set_option backward.defeqAttrib.useBackward true in
/-- Commuting a functor that preserves left Kan extensions with the `lan` functor. -/
@[simps!]
/-
**CategoryTheory.Functor.lanCompIsoOfPreserves** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：lanCompIsoOfPreserves [G.PreservesLeftKanExtensions L] [forall F : A ⥤ B, 
HasLeftKanExtension L F] [forall F : A ⥤ D, HasLeftKanExtension L F] : L.lan ⋙ (
whiskeringRight _ _ _).obj G ≅ (whiskeringRight _ _ _).obj G ⋙ L.lan
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Commuting a functor that preserves left Kan extensions with the `lan` functor.
-/
def lanCompIsoOfPreserves [G.PreservesLeftKanExtensions L]
    [∀ F : A ⥤ B, HasLeftKanExtension L F]
    [∀ F : A ⥤ D, HasLeftKanExtension L F] :
    L.lan ⋙ (whiskeringRight _ _ _).obj G ≅ (whiskeringRight _ _ _).obj G ⋙ L.lan :=
  NatIso.ofComponents (fun F ↦ leftKanExtensionCompIsoOfPreserves _ _ _)
    (fun {F F'} η ↦ by
      apply hom_ext_of_isLeftKanExtension (L.leftKanExtension F ⋙ G)
        (whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
      dsimp [lan]
      ext
      simp [← G.map_comp_assoc])

end LeftKanExtension

section RightKanExtension

/-- `G.PreservesRightKanExtension F L` asserts that `G` preserves all right Kan extensions
of `F` along `L`. See `PreservesRightKanExtension.mk_of_preserves_isRightKanExtension` for a
constructor taking a single right Kan extension as input. -/
/-
**CategoryTheory.Functor.PreservesRightKanExtension** 是 Mathlib 中的一个归纳类型，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {C : Type u_3} →       {D : Type u
_4} →         [inst : CategoryTheory.Category.{v_1, u_1} A] →           [inst_1 
: CategoryTheory.Category.{v_2, u_2} B] →             [inst_2 : CategoryTheory.C
ategory.{v_3, u_3} C] →               [inst_3 : CategoryTheory.Category.{v_4, u_
4} D] →                 CategoryTheory.Functor B D → CategoryTheory.Functor A B 
→ CategoryTheory.Functor A C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.PreservesRightKanExtension F L` asserts that `G` preserves all right Kan exte
nsions
of `F` along `L`. See `PreservesRightKanExtension.mk_of_preserves_isRightKanExte
nsion` for a
constructor taking a single right Kan extension as input.
-/
class PreservesRightKanExtension where
  preserves : ∀ (F' : C ⥤ B) (α : L ⋙ F' ⟶ F) [IsRightKanExtension F' α],
    IsRightKanExtension (F' ⋙ G) <| (Functor.associator _ _ _).inv ≫ whiskerRight α G

/-- Alternative constructor for `PreservesRightKanExtension`, phrased in terms of
`RightExtension.IsUniversal` instead. See `PreservesRightKanExtension.mk_of_preserves_isUniversal`
for a similar constructor taking as input a single `RightExtension`. -/
/-
**CategoryTheory.Functor.PreservesRightKanExtension.mk'** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Functor.PreservesRightKanExtension`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} [inst : Cate
goryTheory.Category.{v_1, u_1} A]   [inst_1 : CategoryTheory.Category.{v_2, u_2}
 B] [inst_2 : CategoryTheory.Category.{v_3, u_3} C]   [inst_3 : CategoryTheory.C
ategory.{v_4, u_4} D] (G : CategoryTheory.Functor B D) (F : CategoryTheory.Funct
or A B)   (L : CategoryTheory.Functor A C),   (∀ {E : L.RightExtension F} (a : C
ategoryTheory.CostructuredArrow.IsUniversal E),       Nonempty         (Category
Theory.CostructuredArrow.IsUniversal           ((CategoryTheory.Functor.RightExt
ension.postcompose₂ L F G).obj E))) →     G.PreservesRightKanExtension F L
参数：G : CategoryTheory.Functor B D；F : CategoryTheory.Functor A B；L : CategoryThe
ory.Functor A C；∀ {E : L.RightExtension F} (a : CategoryTheory.CostructuredArrow
.IsUniversal E),       Nonempty         (CategoryTheory.CostructuredArrow.IsUniv
ersal           ((CategoryTheory.Functor.RightExtension.postcompose₂ L F G).obj 
E))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsRightKanExtension.nonempty_isUniversal`：∀ {C : 
Type u_1} {H : Type u_3} {D : Type u_4} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_3, u_3} …

--- 原说明 ---
Alternative constructor for `PreservesRightKanExtension`, phrased in terms of
`RightExtension.IsUniversal` instead. See `PreservesRightKanExtension.mk_of_pres
erves_isUniversal`
for a similar constructor taking as input a single `RightExtension`.
-/
lemma PreservesRightKanExtension.mk'
    (preserves : ∀ {E : RightExtension L F}, E.IsUniversal →
      Nonempty (RightExtension.postcompose₂ L F G |>.obj E).IsUniversal) :
    G.PreservesRightKanExtension F L where
  preserves _ _ h :=
    ⟨⟨Limits.IsTerminal.equivOfIso
        (RightExtension.postcompose₂ObjMkIso _ _) <| (preserves h.nonempty_isUniversal.some).some⟩⟩

set_option backward.defeqAttrib.useBackward true in
/-- Show that `G` preserves right Kan extensions if it maps some right Kan extension to a right
Kan extension. -/
/-
**CategoryTheory.Functor.PreservesRightKanExtension.mk_of_preserves_isRightKanEx
tension** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.PreservesRightKanExten
sion`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} [inst : Cate
goryTheory.Category.{v_1, u_1} A]   [inst_1 : CategoryTheory.Category.{v_2, u_2}
 B] [inst_2 : CategoryTheory.Category.{v_3, u_3} C]   [inst_3 : CategoryTheory.C
ategory.{v_4, u_4} D] (G : CategoryTheory.Functor B D) (F : CategoryTheory.Funct
or A B)   (L : CategoryTheory.Functor A C) (F' : CategoryTheory.Functor C B) (α 
: L.comp F' ⟶ F) [F'.IsRightKanExtension α],   (F'.comp G).IsRightKanExtension  
     (CategoryTheory.CategoryStruct.comp (L.associator F' G).inv (CategoryTheory
.Functor.whiskerRight α G)) →     G.PreservesRightKanExtension F L
参数：G : CategoryTheory.Functor B D；F : CategoryTheory.Functor A B；L : CategoryThe
ory.Functor A C；F' : CategoryTheory.Functor C B；α : L.comp F' ⟶ F；F'.comp G；Cate
goryTheory.CategoryStruct.comp (L.associator F' G).inv (CategoryTheory.Functor.w
hiskerRight α G)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isRightKanExtension_of_iso`：isRightKanExtension_o
f_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F) (
α' : L ⋙ F'' ⟶ F) (comm : whiskerLeft L…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.rightKanExtensionUnique_hom`：∀ {C : Type u_1} {H 
: Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Functor.liftOfIsRightKanExtension_fac_app`：liftOfIsRightK
anExtension_fac_app (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C) : (F'.liftOfIsRightKanEx
tension α G β).app (L.obj X) ≫ α.app X = β.app…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Show that `G` preserves right Kan extensions if it maps some right Kan extension
 to a right
Kan extension.
-/
lemma PreservesRightKanExtension.mk_of_preserves_isRightKanExtension
    (F' : C ⥤ B) (α : L ⋙ F' ⟶ F) [IsRightKanExtension F' α]
    (h : IsRightKanExtension (F' ⋙ G) <| (Functor.associator _ _ _).inv ≫ whiskerRight α G) :
    G.PreservesRightKanExtension F L :=
  .mk fun F'' α' h ↦
    isRightKanExtension_of_iso
      (isoWhiskerRight (rightKanExtensionUnique F' α F'' α') G)
      ((Functor.associator _ _ _).inv ≫ whiskerRight α G)
      ((Functor.associator _ _ _).inv ≫ whiskerRight α' G)
      (by ext x; simp [← G.map_comp])

/-- Show that `G` preserves right Kan extensions if it maps some right Kan extension to a left
Kan extension, phrased in terms of `IsUniversal`. -/
/-
**CategoryTheory.Functor.PreservesRightKanExtension.mk_of_preserves_isUniversal*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.PreservesRightKanExtension`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} [inst : Cate
goryTheory.Category.{v_1, u_1} A]   [inst_1 : CategoryTheory.Category.{v_2, u_2}
 B] [inst_2 : CategoryTheory.Category.{v_3, u_3} C]   [inst_3 : CategoryTheory.C
ategory.{v_4, u_4} D] (G : CategoryTheory.Functor B D) (F : CategoryTheory.Funct
or A B)   (L : CategoryTheory.Functor A C) (E : L.RightExtension F) (hE : Catego
ryTheory.CostructuredArrow.IsUniversal E),   Nonempty       (CategoryTheory.Cost
ructuredArrow.IsUniversal         ((CategoryTheory.Functor.RightExtension.postco
mpose₂ L F G).obj E)) →     G.PreservesRightKanExtension F L
参数：G : CategoryTheory.Functor B D；F : CategoryTheory.Functor A B；L : CategoryThe
ory.Functor A C；E : L.RightExtension F；hE : CategoryTheory.CostructuredArrow.IsU
niversal E；CategoryTheory.CostructuredArrow.IsUniversal         ((CategoryTheory
.Functor.RightExtension.postcompose₂ L F G).obj E)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesRightKanExtension.mk'`：∀ {A : Type u_1} 
{B : Type u_2} {C : Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_
1, u_1} A]   [inst_1 : CategoryTheory.Categ…

--- 原说明 ---
Show that `G` preserves right Kan extensions if it maps some right Kan extension
 to a left
Kan extension, phrased in terms of `IsUniversal`.
-/
lemma PreservesRightKanExtension.mk_of_preserves_isUniversal (E : RightExtension L F)
    (hE : E.IsUniversal) (h : Nonempty (RightExtension.postcompose₂ L F G |>.obj E).IsUniversal) :
    G.PreservesRightKanExtension F L :=
  .mk' G F L fun hE' ↦
    ⟨Limits.IsTerminal.equivOfIso
      (RightExtension.postcompose₂ L F G |>.mapIso
        <| Limits.IsTerminal.uniqueUpToIso hE hE') h.some⟩

attribute [instance] PreservesRightKanExtension.preserves

/-- `G.PreservesRightKanExtensionAt F L c` asserts that `G` preserves all right pointwise right Kan
extensions of `F` along `L` at `c`. -/
/-
**CategoryTheory.Functor.PreservesPointwiseRightKanExtensionAt** 是 Mathlib 中的一个归
纳类型，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {C : Type u_3} →       {D : Type u
_4} →         [inst : CategoryTheory.Category.{v_1, u_1} A] →           [inst_1 
: CategoryTheory.Category.{v_2, u_2} B] →             [inst_2 : CategoryTheory.C
ategory.{v_3, u_3} C] →               [inst_3 : CategoryTheory.Category.{v_4, u_
4} D] →                 CategoryTheory.Functor B D → CategoryTheory.Functor A B 
→ CategoryTheory.Functor A C → C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.PreservesRightKanExtensionAt F L c` asserts that `G` preserves all right poin
twise right Kan
extensions of `F` along `L` at `c`.
-/
class PreservesPointwiseRightKanExtensionAt (c : C) where
  /-- `G` preserves every pointwise extensions of `F` along `L` at `c`. -/
  preserves : ∀ (E : RightExtension L F), E.IsPointwiseRightKanExtensionAt c →
    Nonempty ((RightExtension.postcompose₂ L F G |>.obj E).IsPointwiseRightKanExtensionAt c)

/-- `G.PreservesRightKanExtensions L` asserts that `G` preserves all pointwise right Kan
extensions of `F` along `L` for every `F`. -/
/-
**CategoryTheory.Functor.PreservesPointwiseRightKanExtension** 是 Mathlib 中的一个缩写定
义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：PreservesPointwiseRightKanExtension
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.PreservesRightKanExtensions L` asserts that `G` preserves all pointwise right
 Kan
extensions of `F` along `L` for every `F`.
-/
abbrev PreservesPointwiseRightKanExtension := ∀ c : C, PreservesPointwiseRightKanExtensionAt G F L c

variable {F L} in
/-- Given a pointwise right Kan extension of `F` along `L` at `c`, exhibits
`(RightExtension.whiskerRight L F G).obj E` as a pointwise right Kan extension of `F ⋙ G` along
`L` at `c`. -/
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtensionAt.postcompo
se** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.RightExtension.IsPointwiseR
ightKanExtensionAt`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {C : Type u_3} →       {D : Type u
_4} →         [inst : CategoryTheory.Category.{v_1, u_1} A] →           [inst_1 
: CategoryTheory.Category.{v_2, u_2} B] →             [inst_2 : CategoryTheory.C
ategory.{v_3, u_3} C] →               [inst_3 : CategoryTheory.Category.{v_4, u_
4} D] →                 (G : CategoryTheory.Functor B D) →                   {F 
: CategoryTheory.Functor A B} →                     {L : CategoryTheory.Functor 
A C} →                       {c : C} →                         [G.PreservesPoint
wiseRightKanExtensionAt F L c] →                           {E : L.RightExtension
 F} →                             E.IsPointwiseRightKanExtensionAt c →          
                     ((CategoryTheory.Functor.RightExtension.postcompose₂ L F G)
.obj                                     E).IsPointwiseRightKanExtensionAt      
                           c
参数：G : CategoryTheory.Functor B D；(CategoryTheory.Functor.RightExtension.postcom
pose₂ L F G).obj                                     E。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesPointwiseRightKanExtensionAt.preserves`：
∀ {A : Type u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} {inst : CategoryTh
eory.Category.{v_1, u_1} A}   {inst_1 : CategoryTheory.Categ…

--- 原说明 ---
Given a pointwise right Kan extension of `F` along `L` at `c`, exhibits
`(RightExtension.whiskerRight L F G).obj E` as a pointwise right Kan extension o
f `F ⋙ G` along
`L` at `c`.
-/
def RightExtension.IsPointwiseRightKanExtensionAt.postcompose {c : C}
    [PreservesPointwiseRightKanExtensionAt G F L c]
    {E : RightExtension L F} (hE : E.IsPointwiseRightKanExtensionAt c) :
    RightExtension.postcompose₂ L F G |>.obj E |>.IsPointwiseRightKanExtensionAt c :=
  PreservesPointwiseRightKanExtensionAt.preserves E hE |>.some

variable {F L} in
/-- Given a pointwise right Kan extension of `F` along `L`, exhibits
`(RightExtension.whiskerRight L F G).obj E` as a pointwise right Kan extension of `F ⋙ G` at `L`. -/
/-
**CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension.postcompose
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.RightExtension.IsPointwiseRig
htKanExtension`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {C : Type u_3} →       {D : Type u
_4} →         [inst : CategoryTheory.Category.{v_1, u_1} A] →           [inst_1 
: CategoryTheory.Category.{v_2, u_2} B] →             [inst_2 : CategoryTheory.C
ategory.{v_3, u_3} C] →               [inst_3 : CategoryTheory.Category.{v_4, u_
4} D] →                 (G : CategoryTheory.Functor B D) →                   {F 
: CategoryTheory.Functor A B} →                     {L : CategoryTheory.Functor 
A C} →                       [G.PreservesPointwiseRightKanExtension F L] →      
                   {E : L.RightExtension F} →                           E.IsPoin
twiseRightKanExtension →                             ((CategoryTheory.Functor.Ri
ghtExtension.postcompose₂ L F G).obj                                 E).IsPointw
iseRightKanExtension
参数：G : CategoryTheory.Functor B D；(CategoryTheory.Functor.RightExtension.postcom
pose₂ L F G).obj                                 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a pointwise right Kan extension of `F` along `L`, exhibits
`(RightExtension.whiskerRight L F G).obj E` as a pointwise right Kan extension o
f `F ⋙ G` at `L`.
-/
def RightExtension.IsPointwiseRightKanExtension.postcompose
    [PreservesPointwiseRightKanExtension G F L]
    {E : RightExtension L F} (hE : E.IsPointwiseRightKanExtension) :
    RightExtension.postcompose₂ L F G |>.obj E |>.IsPointwiseRightKanExtension := fun c ↦
  (hE c).postcompose G

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The cone at a point of the whiskering right by `G` of an extension is isomorphic to the
action of `G` on the cone at that point for the original extension. -/
@[simps!]
/-
**CategoryTheory.Functor.RightExtension.coneAtWhiskerRightIso** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Functor.RightExtension`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {C : Type u_3} →       {D : Type u
_4} →         [inst : CategoryTheory.Category.{v_1, u_1} A] →           [inst_1 
: CategoryTheory.Category.{v_2, u_2} B] →             [inst_2 : CategoryTheory.C
ategory.{v_3, u_3} C] →               [inst_3 : CategoryTheory.Category.{v_4, u_
4} D] →                 (G : CategoryTheory.Functor B D) →                   (F 
: CategoryTheory.Functor A B) →                     (L : CategoryTheory.Functor 
A C) →                       (E : L.RightExtension F) →                         
(c : C) →                           ((CategoryTheory.Functor.RightExtension.post
compose₂ L F G).obj E).coneAt c ≅                             G.mapCone (E.coneA
t c)
参数：G : CategoryTheory.Functor B D；F : CategoryTheory.Functor A B；L : CategoryThe
ory.Functor A C；E : L.RightExtension F；c : C；(CategoryTheory.Functor.RightExtens
ion.postcompose₂ L F G).obj E；E.coneAt c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone at a point of the whiskering right by `G` of an extension is isomorphic
 to the
action of `G` on the cone at that point for the original extension.
-/
def RightExtension.coneAtWhiskerRightIso (E : RightExtension L F) (c : C) :
    (RightExtension.postcompose₂ L F G |>.obj E).coneAt c ≅ G.mapCone (E.coneAt c) :=
  Limits.Cone.ext (Iso.refl _)

/-- If `G` preserves any pointwise right Kan extension of `F` along `L` at `c`, then it preserves
all of them. -/
/-
**CategoryTheory.Functor.PreservesPointwiseRightKanExtensionAt.mk'** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Functor.PreservesPointwiseRightKanExtensionAt`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} [inst : Cate
goryTheory.Category.{v_1, u_1} A]   [inst_1 : CategoryTheory.Category.{v_2, u_2}
 B] [inst_2 : CategoryTheory.Category.{v_3, u_3} C]   [inst_3 : CategoryTheory.C
ategory.{v_4, u_4} D] (G : CategoryTheory.Functor B D) (F : CategoryTheory.Funct
or A B)   (L : CategoryTheory.Functor A C) (c : C) {E : L.RightExtension F} (hE 
: E.IsPointwiseRightKanExtensionAt c)   (hGE : ((CategoryTheory.Functor.RightExt
ension.postcompose₂ L F G).obj E).IsPointwiseRightKanExtensionAt c),   G.Preserv
esPointwiseRightKanExtensionAt F L c
参数：G : CategoryTheory.Functor B D；F : CategoryTheory.Functor A B；L : CategoryThe
ory.Functor A C；c : C；hE : E.IsPointwiseRightKanExtensionAt c；hGE : ((CategoryTh
eory.Functor.RightExtension.postcompose₂ L F G).obj E).IsPointwiseRightKanExtens
ionAt c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves any pointwise right Kan extension of `F` along `L` at `c`, then
 it preserves
all of them.
-/
lemma PreservesPointwiseRightKanExtensionAt.mk' (c : C) {E : RightExtension L F}
    (hE : E.IsPointwiseRightKanExtensionAt c)
    (hGE : (RightExtension.postcompose₂ L F G |>.obj E).IsPointwiseRightKanExtensionAt c) :
    G.PreservesPointwiseRightKanExtensionAt F L c where
  preserves E' hE' :=
    ⟨Limits.IsLimit.ofIsoLimit hGE <|
      (E.coneAtWhiskerRightIso G F L c) ≪≫
        (Limits.Cone.functoriality _ _).mapIso (hE.uniqueUpToIso hE') ≪≫
        (E'.coneAtWhiskerRightIso G F L c).symm⟩
/-
**CategoryTheory.Functor.hasRightKanExtension_of_preserves** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：hasRightKanExtension_of_preserves [L.HasRightKanExtension F] [PreservesRig
htKanExtension G F L] : L.HasRightKanExtension (F ⋙ G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.HasRightKanExtension.mk`：∀ {C : Type u_1} {H : Ty
pe u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_3, u_3} …
· 使用定理 `CategoryTheory.Functor.PreservesRightKanExtension.preserves`：∀ {A : Type
 u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} {inst : CategoryTheory.Catego
ry.{v_1, u_1} A}   {inst_1 : CategoryTheory.Categ…
· 使用定理 `CategoryTheory.Functor.instIsRightKanExtensionRightKanExtensionRightKanE
xtensionCounit`：∀ {C : Type u_1} {H : Type u_3} {D : Type u_4} [inst : CategoryT
heory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} …
-/
instance hasRightKanExtension_of_preserves [L.HasRightKanExtension F]
    [PreservesRightKanExtension G F L] : L.HasRightKanExtension (F ⋙ G) :=
  @HasRightKanExtension.mk _ _ _ _ _ _ _ _ _ _ <|
    letI : (L.rightKanExtension F).IsRightKanExtension <| L.rightKanExtensionCounit F := by
      infer_instance
    PreservesRightKanExtension.preserves (L.rightKanExtension F) (L.rightKanExtensionCounit F)
/-
**CategoryTheory.Functor.hasPointwiseRightKanExtension_of_preserves** 是 Mathlib 
中的一个实例，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasPointwiseRightKanExtension_of_preserves [L.HasPointwiseRightKanExtensio
n F] [PreservesPointwiseRightKanExtension G F L] : L.HasPointwiseRightKanExtensi
on (F ⋙ G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension.hasPo
intwiseRightKanExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst :
 CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2,
 u_2} …
-/
instance hasPointwiseRightKanExtension_of_preserves [L.HasPointwiseRightKanExtension F]
    [PreservesPointwiseRightKanExtension G F L] : L.HasPointwiseRightKanExtension (F ⋙ G) :=
  (pointwiseRightKanExtensionIsPointwiseRightKanExtension
    L F |>.postcompose G).hasPointwiseRightKanExtension

/-- Extract an isomorphism `rightKanExtension L F ⋙ G ≅ rightKanExtension L (F ⋙ G)` when `G`
preserves right Kan extensions. -/
/-
**CategoryTheory.Functor.rightKanExtensionCompIsoOfPreserves** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：rightKanExtensionCompIsoOfPreserves [PreservesRightKanExtension G F L] [L.
HasRightKanExtension F] : L.rightKanExtension F ⋙ G ≅ L.rightKanExtension (F ⋙ G
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract an isomorphism `rightKanExtension L F ⋙ G ≅ rightKanExtension L (F ⋙ G)`
 when `G`
preserves right Kan extensions.
-/
def rightKanExtensionCompIsoOfPreserves [PreservesRightKanExtension G F L]
    [L.HasRightKanExtension F] :
    L.rightKanExtension F ⋙ G ≅ L.rightKanExtension (F ⋙ G) :=
  rightKanExtensionUnique
    (L.rightKanExtension F ⋙ G)
    ((Functor.associator _ _ _).inv ≫ whiskerRight (L.rightKanExtensionCounit F) G)
    (L.rightKanExtension <| F ⋙ G)
    (L.rightKanExtensionCounit <| F ⋙ G)

section

variable [PreservesRightKanExtension G F L] [L.HasRightKanExtension F]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.rightKanExtensionCompIsoOfPreserves_hom_fac** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：rightKanExtensionCompIsoOfPreserves_hom_fac : whiskerLeft L (rightKanExten
sionCompIsoOfPreserves G F L).hom ≫ (L.rightKanExtensionCounit <| F ⋙ G) = (Func
tor.associator _ _ _).inv ≫ whiskerRight (L.rightKanExtensionCounit F) G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.rightKanExtensionUnique_hom`：∀ {C : Type u_1} {H 
: Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.liftOfIsRightKanExtension_fac`：liftOfIsRightKanEx
tension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) : whiskerLeft L (F'.liftOfIsRightKanExte
nsion α G β) ≫ α = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightKanExtensionCompIsoOfPreserves_hom_fac :
    whiskerLeft L (rightKanExtensionCompIsoOfPreserves G F L).hom ≫
      (L.rightKanExtensionCounit <| F ⋙ G) =
    (Functor.associator _ _ _).inv ≫ whiskerRight (L.rightKanExtensionCounit F) G := by
  simp [rightKanExtensionCompIsoOfPreserves]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.rightKanExtensionCompIsoOfPreserves_hom_fac_app** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：rightKanExtensionCompIsoOfPreserves_hom_fac_app (a : A) : (G.rightKanExten
sionCompIsoOfPreserves F L).hom.app (L.obj a) ≫ (L.rightKanExtensionCounit (F ⋙ 
G)).app a = G.map (L.rightKanExtensionCounit F |>.app a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.rightKanExtensionUnique_hom`：∀ {C : Type u_1} {H 
: Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.liftOfIsRightKanExtension_fac_app`：liftOfIsRightK
anExtension_fac_app (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C) : (F'.liftOfIsRightKanEx
tension α G β).app (L.obj X) ≫ α.app X = β.app…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightKanExtensionCompIsoOfPreserves_hom_fac_app (a : A) :
    (G.rightKanExtensionCompIsoOfPreserves F L).hom.app (L.obj a) ≫
      (L.rightKanExtensionCounit (F ⋙ G)).app a =
    G.map (L.rightKanExtensionCounit F |>.app a) := by
  simp [rightKanExtensionCompIsoOfPreserves]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.rightKanExtensionCompIsoOfPreserves_inv_fac** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：rightKanExtensionCompIsoOfPreserves_inv_fac : whiskerLeft L (rightKanExten
sionCompIsoOfPreserves G F L).inv ≫ ((Functor.associator _ _ _).inv ≫ whiskerRig
ht (L.rightKanExtensionCounit F) G) = (L.rightKanExtensionCounit <| F ⋙ G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.rightKanExtensionUnique_inv`：∀ {C : Type u_1} {H 
: Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.liftOfIsRightKanExtension_fac`：liftOfIsRightKanEx
tension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) : whiskerLeft L (F'.liftOfIsRightKanExte
nsion α G β) ≫ α = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightKanExtensionCompIsoOfPreserves_inv_fac :
    whiskerLeft L (rightKanExtensionCompIsoOfPreserves G F L).inv ≫
      ((Functor.associator _ _ _).inv ≫ whiskerRight (L.rightKanExtensionCounit F) G) =
    (L.rightKanExtensionCounit <| F ⋙ G) := by
  simp [rightKanExtensionCompIsoOfPreserves]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.rightKanExtensionCompIsoOfPreserves_inv_fac_app** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：rightKanExtensionCompIsoOfPreserves_inv_fac_app (a : A) : (G.rightKanExten
sionCompIsoOfPreserves F L).inv.app (L.obj a) ≫ G.map (L.rightKanExtensionCounit
 F |>.app a) = (L.rightKanExtensionCounit (F ⋙ G)).app a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.Functor.rightKanExtensionCompIsoOfPreserves_inv_fac`：righ
tKanExtensionCompIsoOfPreserves_inv_fac : whiskerLeft L (rightKanExtensionCompIs
oOfPreserves G F L).inv ≫ ((Functor.associator _ _ _).in…
-/
lemma rightKanExtensionCompIsoOfPreserves_inv_fac_app (a : A) :
    (G.rightKanExtensionCompIsoOfPreserves F L).inv.app (L.obj a) ≫
      G.map (L.rightKanExtensionCounit F |>.app a) =
    (L.rightKanExtensionCounit (F ⋙ G)).app a := by
  simpa [-rightKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (rightKanExtensionCompIsoOfPreserves_inv_fac G F L) a

end

/-- A functor that preserves the limit of `(StructuredArrow.proj L c ⋙ F)` preserves
the pointwise right Kan extension of `F` along `L` at c. -/
/-
**CategoryTheory.Functor.preservesPointwiseRightKanExtensionAtOfPreservesLimit**
 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesPointwiseRightKanExtensionAtOfPreservesLimit (c : C) [Limits.Pres
ervesLimit (StructuredArrow.proj c L ⋙ F) G] : G.PreservesPointwiseRightKanExten
sionAt F L c where preserves E p
参数：c : C；StructuredArrow.proj c L ⋙ F。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimit.preserves`：∀ {C : Type u₁} {inst : 
CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
A functor that preserves the limit of `(StructuredArrow.proj L c ⋙ F)` preserves
the pointwise right Kan extension of `F` along `L` at c.
-/
instance preservesPointwiseRightKanExtensionAtOfPreservesLimit (c : C)
    [Limits.PreservesLimit (StructuredArrow.proj c L ⋙ F) G] :
    G.PreservesPointwiseRightKanExtensionAt F L c where
  preserves E p :=
    ⟨Limits.IsLimit.ofIsoLimit
      (Limits.PreservesLimit.preserves p).some
      (E.coneAtWhiskerRightIso G _ _ c).symm⟩

/-- If there is a pointwise right Kan extension of `F` along `L`, and if `G` preserves them,
then `G` preserves right Kan extensions of `F` along `L`. -/
/-
**CategoryTheory.Functor.preservesPointwiseRKEOfHasPointwiseAndPreservesPointwis
e** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：preservesPointwiseRKEOfHasPointwiseAndPreservesPointwise [HasPointwiseRigh
tKanExtension L F] [G.PreservesPointwiseRightKanExtension F L] : G.PreservesRigh
tKanExtension F L where preserves F' α _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension.isRig
htKanExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryT
heory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …

--- 原说明 ---
If there is a pointwise right Kan extension of `F` along `L`, and if `G` preserv
es them,
then `G` preserves right Kan extensions of `F` along `L`.
-/
instance preservesPointwiseRKEOfHasPointwiseAndPreservesPointwise
    [HasPointwiseRightKanExtension L F] [G.PreservesPointwiseRightKanExtension F L] :
    G.PreservesRightKanExtension F L where
  preserves F' α _ :=
    (RightExtension.isPointwiseRightKanExtensionEquivOfIso
      (RightExtension.postcompose₂ObjMkIso G α) <|
        (isPointwiseRightKanExtensionOfIsRightKanExtension F' α).postcompose G).isRightKanExtension

/-- Extract an isomorphism
`L.pointwiseRightKanExtension F ⋙ G ≅ L.pointwiseRightKanExtension (F ⋙ G)` when `G` preserves
right Kan extensions. -/
/-
**CategoryTheory.Functor.pointwiseRightKanExtensionCompIsoOfPreserves** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseRightKanExtensionCompIsoOfPreserves [PreservesPointwiseRightKanEx
tension G F L] [L.HasPointwiseRightKanExtension F] : L.pointwiseRightKanExtensio
n F ⋙ G ≅ L.pointwiseRightKanExtension (F ⋙ G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract an isomorphism
`L.pointwiseRightKanExtension F ⋙ G ≅ L.pointwiseRightKanExtension (F ⋙ G)` when
 `G` preserves
right Kan extensions.
-/
def pointwiseRightKanExtensionCompIsoOfPreserves
    [PreservesPointwiseRightKanExtension G F L]
    [L.HasPointwiseRightKanExtension F] :
    L.pointwiseRightKanExtension F ⋙ G ≅ L.pointwiseRightKanExtension (F ⋙ G) :=
  rightKanExtensionUnique
    (L.pointwiseRightKanExtension F ⋙ G)
    ((Functor.associator _ _ _).inv ≫ whiskerRight (L.pointwiseRightKanExtensionCounit F) G)
    (L.pointwiseRightKanExtension <| F ⋙ G)
    (L.pointwiseRightKanExtensionCounit <| F ⋙ G)

section

variable [PreservesPointwiseRightKanExtension G F L]
    [L.HasPointwiseRightKanExtension F]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac : whiskerLeft L (poin
twiseRightKanExtensionCompIsoOfPreserves G F L).hom ≫ (L.pointwiseRightKanExtens
ionCounit <| F ⋙ G) = (Functor.associator _ _ _).inv ≫ whiskerRight (L.pointwise
RightKanExtensionCounit F) G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.rightKanExtensionUnique_hom`：∀ {C : Type u_1} {H 
: Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.liftOfIsRightKanExtension_fac`：liftOfIsRightKanEx
tension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) : whiskerLeft L (F'.liftOfIsRightKanExte
nsion α G β) ≫ α = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac :
    whiskerLeft L (pointwiseRightKanExtensionCompIsoOfPreserves G F L).hom ≫
      (L.pointwiseRightKanExtensionCounit <| F ⋙ G) =
    (Functor.associator _ _ _).inv ≫ whiskerRight (L.pointwiseRightKanExtensionCounit F) G := by
  simp [pointwiseRightKanExtensionCompIsoOfPreserves]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Functor.pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac_ap
p** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac_app (a : A) : (G.poin
twiseRightKanExtensionCompIsoOfPreserves F L).hom.app (L.obj a) ≫ (L.pointwiseRi
ghtKanExtensionCounit <| F ⋙ G).app a = G.map (L.pointwiseRightKanExtensionCouni
t F |>.app a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.Functor.pointwiseRightKanExtensionCompIsoOfPreserves_hom_
fac`：pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac : whiskerLeft L (point
wiseRightKanExtensionCompIsoOfPreserves G F L).hom ≫ (L.pointwise…
-/
lemma pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac_app (a : A) :
    (G.pointwiseRightKanExtensionCompIsoOfPreserves F L).hom.app (L.obj a) ≫
      (L.pointwiseRightKanExtensionCounit <| F ⋙ G).app a =
    G.map (L.pointwiseRightKanExtensionCounit F |>.app a) := by
  simpa [-pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac] using
    NatTrans.congr_app (pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac G F L) a

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac : whiskerLeft L (poin
twiseRightKanExtensionCompIsoOfPreserves G F L).inv ≫ (Functor.associator _ _ _)
.inv ≫ whiskerRight (L.pointwiseRightKanExtensionCounit F) G = (L.pointwiseRight
KanExtensionCounit <| F ⋙ G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.rightKanExtensionUnique_inv`：∀ {C : Type u_1} {H 
: Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.liftOfIsRightKanExtension_fac`：liftOfIsRightKanEx
tension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) : whiskerLeft L (F'.liftOfIsRightKanExte
nsion α G β) ≫ α = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac :
    whiskerLeft L (pointwiseRightKanExtensionCompIsoOfPreserves G F L).inv ≫
      (Functor.associator _ _ _).inv ≫ whiskerRight (L.pointwiseRightKanExtensionCounit F) G =
    (L.pointwiseRightKanExtensionCounit <| F ⋙ G) := by
  simp [pointwiseRightKanExtensionCompIsoOfPreserves]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Functor.pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac_ap
p** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac_app (a : A) : (G.poin
twiseRightKanExtensionCompIsoOfPreserves F L).inv.app (L.obj a) ≫ G.map (L.point
wiseRightKanExtensionCounit F |>.app a) = (L.pointwiseRightKanExtensionCounit <|
 F ⋙ G).app a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用引理 `CategoryTheory.Functor.pointwiseRightKanExtensionCompIsoOfPreserves_inv_
fac`：pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac : whiskerLeft L (point
wiseRightKanExtensionCompIsoOfPreserves G F L).inv ≫ (Functor.ass…
-/
lemma pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac_app (a : A) :
    (G.pointwiseRightKanExtensionCompIsoOfPreserves F L).inv.app (L.obj a) ≫
      G.map (L.pointwiseRightKanExtensionCounit F |>.app a) =
    (L.pointwiseRightKanExtensionCounit <| F ⋙ G).app a := by
  simpa [-pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac G F L) a

end

/-- `G.PreservesRightKanExtensions L` means that `G : B ⥤ D` preserves all right Kan extensions
along `L : A ⥤ C` of every functor `A ⥤ B`. -/
/-
**CategoryTheory.Functor.PreservesRightKanExtensions** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：PreservesRightKanExtensions
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.PreservesRightKanExtensions L` means that `G : B ⥤ D` preserves all right Kan
 extensions
along `L : A ⥤ C` of every functor `A ⥤ B`.
-/
abbrev PreservesRightKanExtensions := ∀ (F : A ⥤ B), G.PreservesRightKanExtension F L

/-- `G.PreservesPointwiseRightKanExtensions L` means that `G : B ⥤ D` preserves all pointwise right
Kan extensions along `L : A ⥤ C` of every functor `A ⥤ B`. -/
/-
**CategoryTheory.Functor.PreservesPointwiseRightKanExtensions** 是 Mathlib 中的一个缩写
定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：PreservesPointwiseRightKanExtensions
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.PreservesPointwiseRightKanExtensions L` means that `G : B ⥤ D` preserves all 
pointwise right
Kan extensions along `L : A ⥤ C` of every functor `A ⥤ B`.
-/
abbrev PreservesPointwiseRightKanExtensions :=
  ∀ (F : A ⥤ B), G.PreservesPointwiseRightKanExtension F L

set_option backward.defeqAttrib.useBackward true in
/-- Commuting a functor that preserves right Kan extensions with the `ran` functor. -/
@[simps!]
/-
**CategoryTheory.Functor.ranCompIsoOfPreserves** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：ranCompIsoOfPreserves [G.PreservesRightKanExtensions L] [forall F : A ⥤ B,
 HasRightKanExtension L F] [forall F : A ⥤ D, HasRightKanExtension L F] : L.ran 
⋙ (whiskeringRight _ _ _).obj G ≅ (whiskeringRight _ _ _).obj G ⋙ L.ran
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Commuting a functor that preserves right Kan extensions with the `ran` functor.
-/
def ranCompIsoOfPreserves [G.PreservesRightKanExtensions L]
    [∀ F : A ⥤ B, HasRightKanExtension L F] [∀ F : A ⥤ D, HasRightKanExtension L F] :
    L.ran ⋙ (whiskeringRight _ _ _).obj G ≅ (whiskeringRight _ _ _).obj G ⋙ L.ran :=
  NatIso.ofComponents (fun F ↦ rightKanExtensionCompIsoOfPreserves _ _ _)
    (fun {F F'} η ↦ by
      apply hom_ext_of_isRightKanExtension
        (L.rightKanExtension <| F' ⋙ G)
        (L.rightKanExtensionCounit <| F' ⋙ G)
      dsimp [ran]
      ext
      simp only [comp_obj, Category.assoc, rightKanExtensionCompIsoOfPreserves_hom_fac,
        NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_inv_app, Category.id_comp,
        liftOfIsRightKanExtension_fac, rightKanExtensionCompIsoOfPreserves_hom_fac_assoc,
        ← G.map_comp]
      simp)

end RightKanExtension

end

end CategoryTheory.Functor

