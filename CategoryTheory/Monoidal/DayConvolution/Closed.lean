/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.DayConvolution
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.End

/-! # Internal homs for day convolution

Given a category `V` that is monoidal closed, a category `C` that
is monoidal, a functor `C ⥤ V`, and given the data of suitable day convolutions
and suitable ends of profunctors `c c₁ c₂ ↦ ihom (F c₁) (·.obj (c₂ ⊗ c))`,
we prove that the data of the units of the left Kan extensions that define
day convolutions and the data of the canonical morphisms to the aforementioned
ends can be organised as data that exhibit `F` as monoidal closed in `C ⥤ V` for
the Day convolution monoidal structure.

## TODOs
* When `LawfulDayConvolutionMonoidalStruct` (https://github.com/leanprover-community/mathlib4/issues/26820) lands, transport the
  constructions here to produce actual `CategoryTheory.MonoidalClosed` instances.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.MonoidalCategory
open scoped ExternalProduct
open Opposite Limits

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
  [MonoidalCategory C] [MonoidalCategory V] [MonoidalClosed V]

/-- Given `F : C ⥤ V`, this is the functor
`G ↦ c c₁ c₂ ↦ ihom (F c₁) (G.obj (c₂ ⊗ c))`.
The internal hom functor for Day convolution `[F, -]` is naturally isomorphic
to the functor `G ↦ c ↦ end_ (c₁ c₂ ↦ ihom (F c₁) (G.obj (c₂ ⊗ c)))`, hence
this definition. -/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.dayConvolutionInternalHomDiagramFunctor** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：dayConvolutionInternalHomDiagramFunctor (F : C ⥤ V) : (C ⥤ V) ⥤ C ⥤ Cᵒᵖ ⥤ 
C ⥤ V where obj G
参数：F : C ⥤ V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : C ⥤ V`, this is the functor
`G ↦ c c₁ c₂ ↦ ihom (F c₁) (G.obj (c₂ ⊗ c))`.
The internal hom functor for Day convolution `[F, -]` is naturally isomorphic
to the functor `G ↦ c ↦ end_ (c₁ c₂ ↦ ihom (F c₁) (G.obj (c₂ ⊗ c)))`, hence
this definition.
-/
def dayConvolutionInternalHomDiagramFunctor (F : C ⥤ V) :
    (C ⥤ V) ⥤ C ⥤ Cᵒᵖ ⥤ C ⥤ V where
  obj G :=
    { obj c := Functor.whiskeringLeft₂ _ |>.obj F.op |>.obj
        (tensorRight c ⋙ G) |>.obj MonoidalClosed.internalHom
      map {c c'} f := Functor.whiskeringLeft₂ _ |>.obj F.op |>.map
        (Functor.whiskerRight (curriedTensor C |>.flip.map f) G) |>.app
          MonoidalClosed.internalHom }
  map {G G'} η :=
    { app c := Functor.whiskeringLeft₂ _ |>.obj F.op |>.map
        (Functor.whiskerLeft _ η) |>.app MonoidalClosed.internalHom
      naturality {c c'} f := by
        ext j k
        dsimp
        simpa [-NatTrans.naturality] using!
          congr_arg (ihom <| F.obj <| unop j).map (η.naturality <| k ◁ f) }

/-- `DayConvolutionInternalHom F G H` asserts that `H` is the value at `G` of
an internal hom functor of `F` for the Day convolution monoidal structure.
This is phrased as the data of a limit `CategoryTheory.Wedge`
(i.e an end) on `internalHomDiagramFunctor F|>.obj G|>.obj c` and
`c`, with tip `(H.obj G).obj c` and a compatibility condition asserting that
the functoriality of `H` identifies to the functoriality of ends. -/
/-
**CategoryTheory.MonoidalCategory.DayConvolutionInternalHom** 是 Mathlib 中的一个结构，位
于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：DayConvolutionInternalHom (F : C ⥤ V) (G : C ⥤ V) (H : C ⥤ V) where /-- Th
e canonical projections maps -/ π (c j : C) : H.obj c ⟶ (ihom <| F.obj j).obj (G
.obj <| j otimes c) /-- The projections maps assemble into a wedge. -/ hπ (c : C
) ⦃i j : C⦄ (f : i ⟶ j) : π c i ≫ (ihom (F.obj i)).map (G.map <| f ▷ c) = π c j 
≫ (MonoidalClosed.pre <| F.map f).app (G.obj <| j otimes c) /-- The wedge define
d by `π` and `hπ` is a limit wedge, i.e `H.obj c` is an end of `internalHomDiagr
amFunctor F G|>.obj c`. -/
参数：F : C ⥤ V；G : C ⥤ V；H : C ⥤ V；c j : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DayConvolutionInternalHom F G H` asserts that `H` is the value at `G` of
an internal hom functor of `F` for the Day convolution monoidal structure.
This is phrased as the data of a limit `CategoryTheory.Wedge`
(i.e an end) on `internalHomDiagramFunctor F|>.obj G|>.obj c` and
`c`, with tip `(H.obj G).obj c` and a compatibility condition asserting that
the functoriality of `H` identifies to the functoriality of ends.
-/
structure DayConvolutionInternalHom (F : C ⥤ V) (G : C ⥤ V) (H : C ⥤ V) where
  /-- The canonical projections maps -/
  π (c j : C) : H.obj c ⟶ (ihom <| F.obj j).obj (G.obj <| j ⊗ c)
  /-- The projections maps assemble into a wedge. -/
  hπ (c : C) ⦃i j : C⦄ (f : i ⟶ j) :
    π c i ≫ (ihom (F.obj i)).map (G.map <| f ▷ c) =
    π c j ≫ (MonoidalClosed.pre <| F.map f).app (G.obj <| j ⊗ c)
  /-- The wedge defined by `π` and `hπ` is a limit wedge, i.e `H.obj c` is
  an end of `internalHomDiagramFunctor F G|>.obj c`. -/
  isLimitWedge (c : C) :
    IsLimit <| Wedge.mk
      (F := dayConvolutionInternalHomDiagramFunctor F |>.obj G |>.obj c)
      (H.obj c) (π c) (hπ c)
  /-- The functoriality of `H.obj G` identifies (through
  `Wedge.IsLimit.hom_ext`) with the functoriality on ends induced by
  functoriality of `internalHomDiagramFunctor F|>.obj G`. -/
  map_comp_π {c c' : C} (f : c ⟶ c') (j : C) :
    H.map f ≫ π c' j = π c j ≫ (ihom <| F.obj j).map (G.map <| j ◁ f)

namespace DayConvolutionInternalHom

open scoped DayConvolution

attribute [reassoc (attr := simp)] map_comp_π
attribute [reassoc] hπ

variable {F : C ⥤ V} {G : C ⥤ V} {H : C ⥤ V}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If we have a map `G ⟶ G'` and a `DayConvolutionInternalHom F G' H'`, then
there is a unique map `H ⟶ H'` induced by functoriality of ends and functoriality
of `internalHomDiagramFunctor F`. -/
/-
**CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.map** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom`。
形式化陈述：map (ℌ : DayConvolutionInternalHom F G H) {G' : C ⥤ V} {H' : C ⥤ V} (f : G
 ⟶ G') (ℌ' : DayConvolutionInternalHom F G' H') : H ⟶ H' where app c
参数：ℌ : DayConvolutionInternalHom F G H；f : G ⟶ G'；ℌ' : DayConvolutionInternalHom
 F G' H'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.hπ`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…

--- 原说明 ---
If we have a map `G ⟶ G'` and a `DayConvolutionInternalHom F G' H'`, then
there is a unique map `H ⟶ H'` induced by functoriality of ends and functorialit
y
of `internalHomDiagramFunctor F`.
-/
def map (ℌ : DayConvolutionInternalHom F G H) {G' : C ⥤ V} {H' : C ⥤ V}
    (f : G ⟶ G') (ℌ' : DayConvolutionInternalHom F G' H') :
    H ⟶ H' where
  app c := Wedge.IsLimit.lift (ℌ'.isLimitWedge c)
    (fun j ↦ (ℌ.π c j) ≫
      (dayConvolutionInternalHomDiagramFunctor
        F |>.map f |>.app c |>.app (op j) |>.app j))
    (fun ⦃j j'⦄ φ ↦ by
      have := congrArg (fun t ↦ t.app j') <|
        dayConvolutionInternalHomDiagramFunctor
          F |>.map f |>.app c |>.naturality φ.op
      dsimp at this ⊢
      rw [Category.assoc, ← (ihom (F.obj j)).map_comp, ← f.naturality,
        Functor.map_comp, reassoc_of% ℌ.hπ]
      simp)
  naturality {c c'} f := by
    apply Wedge.IsLimit.hom_ext (ℌ'.isLimitWedge c')
    intro j
    dsimp
    simp only [Category.assoc, map_comp_π]
    rw [← Wedge.mk_ι
        (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c')
        (H'.obj c') (ℌ'.π c') (ℌ'.hπ c'),
      ← Wedge.mk_ι
        (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c)
        (H'.obj c) (ℌ'.π c) (ℌ'.hπ c),
      Wedge.IsLimit.lift_ι (ℌ'.isLimitWedge c'),
      Wedge.IsLimit.lift_ι_assoc (ℌ'.isLimitWedge c)]
    simp [← Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.map_app_comp_** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_app_comp_π (ℌ : DayConvolutionInternalHom F G H)
    {G' : C ⥤ V} {H' : C ⥤ V} (f : G ⟶ G')
    (ℌ' : DayConvolutionInternalHom F G' H') (c : C) (j : C) :
    (ℌ.map f ℌ').app c ≫ ℌ'.π c j =
    ℌ.π c j ≫ (ihom <| F.obj j).map (f.app <| j ⊗ c) := by
  dsimp [map]
  rw [← Wedge.mk_ι
      (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c)
      (H'.obj c) (ℌ'.π c) (ℌ'.hπ c),
    Wedge.IsLimit.lift_ι (ℌ'.isLimitWedge c)]

section ev

variable [DayConvolution F H] (ℌ : DayConvolutionInternalHom F G H)

set_option backward.defeqAttrib.useBackward true in
/-- Given `ℌ : DayConvolutionInternalHom F H`, if we think of `H.obj G`
as the internal hom `[F, G]`, then this is the transformation
corresponding to the component at `G` of the "evaluation" natural morphism
`F ⊛ [F, _] ⟶ 𝟭`. -/
/-
**CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.ev_app** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom`。
形式化陈述：ev_app : F ⊛ H ⟶ G
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given `ℌ : DayConvolutionInternalHom F H`, if we think of `H.obj G`
as the internal hom `[F, G]`, then this is the transformation
corresponding to the component at `G` of the "evaluation" natural morphism
`F ⊛ [F, _] ⟶ 𝟭`.
-/
def ev_app : F ⊛ H ⟶ G :=
  DayConvolution.corepresentableBy F H |>.homEquiv.symm <|
    { app x := MonoidalClosed.uncurry <| ℌ.π x.2 x.1
      naturality {x y} f := by
        have := congrArg (fun t ↦ F.obj x.1 ◁ t) <| ℌ.hπ x.2 f.1
        dsimp at this ⊢
        simp only [whiskerLeft_comp] at this
        simp only [Category.assoc, MonoidalClosed.uncurry_eq, Functor.id_obj,
          ← whiskerLeft_comp_assoc, map_comp_π]
        simp only [whiskerLeft_comp, Category.assoc, ihom.ev_naturality,
          Functor.comp_obj, curriedTensor_obj_obj, Functor.id_obj,
          ← whisker_exchange_assoc, tensorHom_def, Functor.map_comp,
          ← ihom.ev_naturality_assoc]
        rw [reassoc_of% this]
        simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.unit_app_ev_app_app*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionInterna
lHom`。
形式化陈述：unit_app_ev_app_app (x y : C) : ((DayConvolution.unit F H).app (x, y) ≫ (ℌ
.ev_app).app (x otimes y)) = MonoidalClosed.uncurry (ℌ.π y x)
参数：x y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac_app`：descOfIsLeftKan
Extension_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) : α.app X ≫ (F'.descOfIsLe
ftKanExtension α G β).app (L.obj X) = β.app X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unit_app_ev_app_app (x y : C) :
    ((DayConvolution.unit F H).app (x, y) ≫ (ℌ.ev_app).app (x ⊗ y)) =
    MonoidalClosed.uncurry (ℌ.π y x) := by
  have := Functor.descOfIsLeftKanExtension_fac_app (F ⊛ H)
    (DayConvolution.unit F H) G
  dsimp at this
  simp [this, ev_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.ev_naturality_app** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionInternalH
om`。
形式化陈述：ev_naturality_app {G' H' : C ⥤ V} (ℌ' : DayConvolutionInternalHom F G' H')
 [DayConvolution F H'] (η : G ⟶ G') : DayConvolution.map (𝟙 F) (ℌ.map η ℌ') ≫ ℌ'
.ev_app = ℌ.ev_app ≫ η
参数：ℌ' : DayConvolutionInternalHom F G' H'；η : G ⟶ G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
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
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app_assoc`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.unit_app_ev_ap
p_app`：unit_app_ev_app_app (x y : C) : ((DayConvolution.unit F H).app (x, y) ≫ (
ℌ.ev_app).app (x otimes y)) = MonoidalClosed.uncurry (ℌ.π y x)
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_eq`：uncurry_eq (g : Y ⟶ A ⟶[C] X) 
: uncurry g = (A ◁ g) ≫ (ihom.ev A).app X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.map_app_comp_π
`：map_app_comp_π (ℌ : DayConvolutionInternalHom F G H) {G' : C ⥤ V} {H' : C ⥤ V}
 (f : G ⟶ G') (ℌ' : DayConvolutionInternalHom F G' H') (c : C)…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ihom.ev_naturality`：ev_naturality {X Y : C} (f : X ⟶ Y) :
 A ◁ (ihom A).map f ≫ (ev A).app Y = (ev A).app X ≫ f
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.unit_app_ev_ap
p_app_assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Ty
pe u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ev_naturality_app {G' H' : C ⥤ V} (ℌ' : DayConvolutionInternalHom F G' H')
    [DayConvolution F H'] (η : G ⟶ G') :
    DayConvolution.map (𝟙 F) (ℌ.map η ℌ') ≫ ℌ'.ev_app = ℌ.ev_app ≫ η := by
  apply DayConvolution.corepresentableBy F H |>.homEquiv.injective
  dsimp
  ext ⟨x, y⟩
  simp [MonoidalClosed.uncurry_eq, ← whiskerLeft_comp_assoc]

end ev

section coev

variable {G : C ⥤ V} [DayConvolution F G]
    (ℌ : DayConvolutionInternalHom F (F ⊛ G) H)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given `ℌ : DayConvolutionInternalHom F H`, if we think of `H.obj G`
as the internal hom `[F, G]`, then this is the transformation
corresponding to the component at `G` of the "coevaluation" natural morphism
`𝟭 ⟶ [F, F ⊛ _]`. -/
/-
**CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.coev_app** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom`。
形式化陈述：coev_app : G ⟶ H where app c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `ℌ : DayConvolutionInternalHom F H`, if we think of `H.obj G`
as the internal hom `[F, G]`, then this is the transformation
corresponding to the component at `G` of the "coevaluation" natural morphism
`𝟭 ⟶ [F, F ⊛ _]`.
-/
def coev_app : G ⟶ H where
  app c :=
    Wedge.IsLimit.lift (ℌ.isLimitWedge c)
      (fun c' => MonoidalClosed.curry <|
        (DayConvolution.unit F G).app (c', c))
        (fun {c' c''} f => by
          have := DayConvolution.unit_naturality F G f (𝟙 c)
          simp only [Functor.map_id, tensorHom_id] at this
          replace this := congrArg MonoidalClosed.curry this
          simp only [MonoidalClosed.curry_natural_right] at this
          dsimp
          rw [← this]
          simp [MonoidalClosed.curry_eq])
  naturality {c c'} f := by
    dsimp
    apply Wedge.IsLimit.hom_ext <| ℌ.isLimitWedge c'
    intro (j : C)
    simp only [multicospanIndexEnd_left,
      dayConvolutionInternalHomDiagramFunctor_obj_obj_obj_obj, Multifork.ofι_pt,
      Wedge.mk_ι, Category.assoc, map_comp_π]
    rw [← Wedge.mk_ι
        (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c)
        (H.obj c) (ℌ.π c) (ℌ.hπ c),
      ← Wedge.mk_ι
        (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c')
        (H.obj c') (ℌ.π c') (ℌ.hπ c'),
      Wedge.IsLimit.lift_ι_assoc, Wedge.IsLimit.lift_ι]
    have := DayConvolution.unit_naturality F G (𝟙 j) f
    simp only [Functor.map_id, id_tensorHom] at this
    replace this := congrArg MonoidalClosed.curry this
    simp only [MonoidalClosed.curry_natural_right] at this
    rw [← this]
    simp [MonoidalClosed.curry_eq]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.coev_app_** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coev_app_π (c j : C) :
    ℌ.coev_app.app c ≫ ℌ.π c j =
    MonoidalClosed.curry ((DayConvolution.unit F G).app (j, c)) := by
  dsimp [coev_app]
  rw [← Wedge.mk_ι
      (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c)
      (H.obj c) (ℌ.π c) (ℌ.hπ c),
    Wedge.IsLimit.lift_ι]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.coev_naturality_app*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionInterna
lHom`。
形式化陈述：coev_naturality_app {G' H' : C ⥤ V} [DayConvolution F G'] (η : G ⟶ G') (ℌ'
 : DayConvolutionInternalHom F (F ⊛ G') H') : η ≫ ℌ'.coev_app = ℌ.coev_app ≫ ℌ.m
ap (DayConvolution.map (𝟙 _) η) ℌ'
参数：η : G ⟶ G'；ℌ' : DayConvolutionInternalHom F (F ⊛ G') H'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.Wedge.IsLimit.hom_ext`：hom_ext (hc : IsLimit c) {X
 : C} {f g : X ⟶ c.pt} (h : forall j, f ≫ c.ι j = g ≫ c.ι j) : f = g
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.hπ`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_injective`：uncurry_injective : Fun
ction.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.coev_app_π`：co
ev_app_π (c j : C) : ℌ.coev_app.app c ≫ ℌ.π c j = MonoidalClosed.curry ((DayConv
olution.unit F G).app (j, c))
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.map_app_comp_π
`：map_app_comp_π (ℌ : DayConvolutionInternalHom F G H) {G' : C ⥤ V} {H' : C ⥤ V}
 (f : G ⟶ G') (ℌ' : DayConvolutionInternalHom F G' H') (c : C)…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.coev_app_π_ass
oc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_natural_right`：uncurry_natural_rig
ht (f : X ⟶ A ⟶[C] Y) (g : Y ⟶ Y') : uncurry (f ≫ (ihom _).map g) = uncurry f ≫ 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app`：unit_ap
p_map_app : (unit F G).app (x, y) ≫ (map f g).app (x otimes y : C) = (f.app x ot
imesₘ g.app y) ≫ (unit F' G').app (x, y)
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_natural_left`：uncurry_natural_left
 (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) : uncurry (f ≫ g) = _ ◁ f ≫ uncurry g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coev_naturality_app {G' H' : C ⥤ V} [DayConvolution F G'] (η : G ⟶ G')
    (ℌ' : DayConvolutionInternalHom F (F ⊛ G') H') :
    η ≫ ℌ'.coev_app =
    ℌ.coev_app ≫ ℌ.map (DayConvolution.map (𝟙 _) η) ℌ' := by
  ext c
  dsimp
  apply Wedge.IsLimit.hom_ext <| ℌ'.isLimitWedge c
  intro j
  apply MonoidalClosed.uncurry_injective
  dsimp
  simp only [Category.assoc, coev_app_π, Functor.comp_obj, tensor_obj,
    map_app_comp_π, coev_app_π_assoc, MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.uncurry_curry, DayConvolution.unit_app_map_app,
    NatTrans.id_app, id_tensorHom]
  simp [MonoidalClosed.uncurry_natural_left]

end coev

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.left_triangle_compon
ents** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionIn
ternalHom`。
形式化陈述：left_triangle_components (G : C ⥤ V) [DayConvolution F G] (ℌ : DayConvolut
ionInternalHom F (F ⊛ G) H) [DayConvolution F H] : DayConvolution.map (𝟙 F) ℌ.co
ev_app ≫ ℌ.ev_app = 𝟙 (F ⊛ G)
参数：G : C ⥤ V；ℌ : DayConvolutionInternalHom F (F ⊛ G) H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.MonoidalClosed.curry_injective`：curry_injective : Functio
n.Injective (curry : (A otimes Y ⟶ X) -> (Y ⟶ A ⟶[C] X))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app_assoc`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.unit_app_ev_ap
p_app`：unit_app_ev_app_app (x y : C) : ((DayConvolution.unit F H).app (x, y) ≫ (
ℌ.ev_app).app (x otimes y)) = MonoidalClosed.uncurry (ℌ.π y x)
· 使用定理 `CategoryTheory.MonoidalClosed.curry_natural_left`：curry_natural_left (f 
: X ⟶ X') (g : A otimes X' ⟶ Y) : curry (_ ◁ f ≫ g) = f ≫ curry g
· 使用定理 `CategoryTheory.MonoidalClosed.curry_uncurry`：curry_uncurry (f : X ⟶ A ⟶[
C] Y) : curry (uncurry f) = f
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.coev_app_π`：co
ev_app_π (c j : C) : ℌ.coev_app.app c ≫ ℌ.π c j = MonoidalClosed.curry ((DayConv
olution.unit F G).app (j, c))
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem left_triangle_components (G : C ⥤ V) [DayConvolution F G]
    (ℌ : DayConvolutionInternalHom F (F ⊛ G) H) [DayConvolution F H] :
    DayConvolution.map (𝟙 F) ℌ.coev_app ≫ ℌ.ev_app = 𝟙 (F ⊛ G) := by
  apply DayConvolution.corepresentableBy F G |>.homEquiv.injective
  dsimp
  ext ⟨x, y⟩
  apply MonoidalClosed.curry_injective
  simp [MonoidalClosed.curry_natural_left]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.right_triangle_compo
nents** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionI
nternalHom`。
形式化陈述：right_triangle_components (G : C ⥤ V) [DayConvolution F H] (ℌ : DayConvolu
tionInternalHom F G H) {H' : C ⥤ V} (ℌ' : DayConvolutionInternalHom F (F ⊛ H) H'
) : ℌ'.coev_app ≫ ℌ'.map ℌ.ev_app ℌ = 𝟙 H
参数：G : C ⥤ V；ℌ : DayConvolutionInternalHom F G H；ℌ' : DayConvolutionInternalHom 
F (F ⊛ H) H'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.Wedge.IsLimit.hom_ext`：hom_ext (hc : IsLimit c) {X
 : C} {f g : X ⟶ c.pt} (h : forall j, f ≫ c.ι j = g ≫ c.ι j) : f = g
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.hπ`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_injective`：uncurry_injective : Fun
ction.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.map_app_comp_π
`：map_app_comp_π (ℌ : DayConvolutionInternalHom F G H) {G' : C ⥤ V} {H' : C ⥤ V}
 (f : G ⟶ G') (ℌ' : DayConvolutionInternalHom F G' H') (c : C)…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.coev_app_π_ass
oc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_natural_right`：uncurry_natural_rig
ht (f : X ⟶ A ⟶[C] Y) (g : Y ⟶ Y') : uncurry (f ≫ (ihom _).map g) = uncurry f ≫ 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.unit_app_ev_ap
p_app`：unit_app_ev_app_app (x y : C) : ((DayConvolution.unit F H).app (x, y) ≫ (
ℌ.ev_app).app (x otimes y)) = MonoidalClosed.uncurry (ℌ.π y x)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem right_triangle_components (G : C ⥤ V) [DayConvolution F H]
    (ℌ : DayConvolutionInternalHom F G H) {H' : C ⥤ V}
    (ℌ' : DayConvolutionInternalHom F (F ⊛ H) H') :
    ℌ'.coev_app ≫ ℌ'.map ℌ.ev_app ℌ = 𝟙 H := by
  ext c
  apply Wedge.IsLimit.hom_ext <| ℌ.isLimitWedge c
  intro j
  apply MonoidalClosed.uncurry_injective
  simp [MonoidalClosed.uncurry_natural_right]

end DayConvolutionInternalHom

end

end CategoryTheory.MonoidalCategory

