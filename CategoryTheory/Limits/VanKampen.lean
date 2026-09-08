/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!

# Universal colimits and van Kampen colimits

## Main definitions
- `CategoryTheory.IsUniversalColimit`: A (colimit) cocone over a diagram `F : J ⥤ C` is universal
  if it is stable under pullbacks.
- `CategoryTheory.IsVanKampenColimit`: A (colimit) cocone over a diagram `F : J ⥤ C` is van
  Kampen if for every cocone `c'` over the pullback of the diagram `F' : J ⥤ C'`,
  `c'` is colimiting iff `c'` is the pullback of `c`.

## References
- https://ncatlab.org/nlab/show/van+Kampen+colimit
- [Stephen Lack and Paweł Sobociński, Adhesive Categories][adhesive2004]

-/

@[expose] public section


open CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory

universe v' u' v u

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {K : Type*} [Category* K] {D : Type*} [Category* D]

/-- A (colimit) cocone over a diagram `F : J ⥤ C` is universal if it is stable under pullbacks. -/
/-
**CategoryTheory.IsUniversalColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：IsUniversalColimit {F : J ⥤ C} (c : Cocone F) : Prop
参数：c : Cocone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (colimit) cocone over a diagram `F : J ⥤ C` is universal if it is stable under
 pullbacks.
-/
def IsUniversalColimit {F : J ⥤ C} (c : Cocone F) : Prop :=
  ∀ ⦃F' : J ⥤ C⦄ (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (_ : α ≫ c.ι = c'.ι ≫ (Functor.const J).map f) (_ : NatTrans.Equifibered α),
    (∀ j : J, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)) → Nonempty (IsColimit c')

/-- A (colimit) cocone over a diagram `F : J ⥤ C` is van Kampen if for every cocone `c'` over the
pullback of the diagram `F' : J ⥤ C'`, `c'` is colimiting iff `c'` is the pullback of `c`.

TODO: Show that this is iff the functor `C ⥤ Catᵒᵖ` sending `x` to `C/x` preserves it.
TODO: Show that this is iff the inclusion functor `C ⥤ Span(C)` preserves it.
-/
/-
**CategoryTheory.IsVanKampenColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：IsVanKampenColimit {F : J ⥤ C} (c : Cocone F) : Prop
参数：c : Cocone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (colimit) cocone over a diagram `F : J ⥤ C` is van Kampen if for every cocone 
`c'` over the
pullback of the diagram `F' : J ⥤ C'`, `c'` is colimiting iff `c'` is the pullba
ck of `c`.

TODO: Show that this is iff the functor `C ⥤ Catᵒᵖ` sending `x` to `C/x` preserv
es it.
TODO: Show that this is iff the inclusion functor `C ⥤ Span(C)` preserves it.
-/
def IsVanKampenColimit {F : J ⥤ C} (c : Cocone F) : Prop :=
  ∀ ⦃F' : J ⥤ C⦄ (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (_ : α ≫ c.ι = c'.ι ≫ (Functor.const J).map f) (_ : NatTrans.Equifibered α),
    Nonempty (IsColimit c') ↔ ∀ j : J, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)
/-
**CategoryTheory.IsVanKampenColimit.isUniversal** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.IsVanKampenColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} {c
 : CategoryTheory.Limits.Cocone F},   CategoryTheory.IsVanKampenColimit c → Cate
goryTheory.IsUniversalColimit c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem IsVanKampenColimit.isUniversal {F : J ⥤ C} {c : Cocone F} (H : IsVanKampenColimit c) :
    IsUniversalColimit c :=
  fun _ c' α f h hα => (H c' α f h hα).mpr

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A universal colimit is a colimit. -/
/-
**CategoryTheory.IsUniversalColimit.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.IsUniversalColimit`。
形式化陈述：{J : Type v'} →   [inst : CategoryTheory.Category.{u', v'} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         {F : Catego
ryTheory.Functor J C} →           {c : CategoryTheory.Limits.Cocone F} → Categor
yTheory.IsUniversalColimit c → CategoryTheory.Limits.IsColimit c
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A universal colimit is a colimit.
-/
noncomputable def IsUniversalColimit.isColimit {F : J ⥤ C} {c : Cocone F}
    (h : IsUniversalColimit c) : IsColimit c := by
  refine ((h c (𝟙 F) (𝟙 c.pt :) (by rw [Functor.map_id, Category.comp_id, Category.id_comp])
    (.of_isIso _)) fun j => ?_).some
  have : IsIso (𝟙 c.pt) := inferInstance
  exact IsPullback.of_vert_isIso ⟨by simp⟩

/-- A van Kampen colimit is a colimit. -/
/-
**CategoryTheory.IsVanKampenColimit.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.IsVanKampenColimit`。
形式化陈述：{J : Type v'} →   [inst : CategoryTheory.Category.{u', v'} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         {F : Catego
ryTheory.Functor J C} →           {c : CategoryTheory.Limits.Cocone F} → Categor
yTheory.IsVanKampenColimit c → CategoryTheory.Limits.IsColimit c
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsVanKampenColimit.isUniversal`：∀ {J : Type v'} [inst : C
ategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Categor
y.{v, u} C]   {F : CategoryTheory.F…

--- 原说明 ---
A van Kampen colimit is a colimit.
-/
noncomputable def IsVanKampenColimit.isColimit {F : J ⥤ C} {c : Cocone F}
    (h : IsVanKampenColimit c) : IsColimit c :=
  h.isUniversal.isColimit

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsInitial.isVanKampenColimit** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.IsInitial`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasStrictInitialObjects C] {X : C}   (h : CategoryTheory.Limits.IsInitial 
X), CategoryTheory.IsVanKampenColimit (CategoryTheory.Limits.asEmptyCocone X)
参数：h : CategoryTheory.Limits.IsInitial X；CategoryTheory.Limits.asEmptyCocone X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
· 使用定理 `CategoryTheory.Limits.IsInitial.isIso_to`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Limits.HasStrictInitialObjects C] {I 
: C}   (hI : CategoryTheory.Li…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsInitial.isVanKampenColimit [HasStrictInitialObjects C] {X : C} (h : IsInitial X) :
    IsVanKampenColimit (asEmptyCocone X) := by
  intro F' c' α f hf hα
  have : F' = Functor.empty C := by apply Functor.hext <;> rintro ⟨⟨⟩⟩
  subst this
  have := h.isIso_to f
  refine ⟨by rintro _ ⟨⟨⟩⟩,
    fun _ => ⟨IsColimit.ofIsoColimit h (Cocone.ext (asIso f).symm <| by rintro ⟨⟨⟩⟩)⟩⟩

section Functor

/-
**CategoryTheory.IsUniversalColimit.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.IsUniversalColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} {c
 c' : CategoryTheory.Limits.Cocone F},   CategoryTheory.IsUniversalColimit c → ∀
 (e : c ≅ c'), CategoryTheory.IsUniversalColimit c'
参数：e : c ≅ c'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.CoconeMorphism.w`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃,
 u₃} C]   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso`：of_vert_isIso [IsIso snd] [IsIs
o f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.Limits.instIsIsoHomHomCocone`：∀ {J : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category
.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsUniversalColimit.of_iso {F : J ⥤ C} {c c' : Cocone F} (hc : IsUniversalColimit c)
    (e : c ≅ c') : IsUniversalColimit c' := by
  intro F' c'' α f h hα H
  have : c'.ι ≫ (Functor.const J).map e.inv.hom = c.ι := by
    ext j
    exact e.inv.2 j
  apply hc c'' α (f ≫ e.inv.1) (by rw [Functor.map_comp, ← reassoc_of% h, this]) hα
  intro j
  rw [← Category.comp_id (α.app j)]
  exact (H j).paste_vert (IsPullback.of_vert_isIso ⟨by simp⟩)
/-
**CategoryTheory.IsVanKampenColimit.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.IsVanKampenColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functor J C} {c
 c' : CategoryTheory.Limits.Cocone F},   CategoryTheory.IsVanKampenColimit c → ∀
 (e : c ≅ c'), CategoryTheory.IsVanKampenColimit c'
参数：e : c ≅ c'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.CoconeMorphism.w`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃,
 u₃} C]   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.IsPullback.paste_vert_iff`：paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂
₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ 
⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ …
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso`：of_vert_isIso [IsIso snd] [IsIs
o f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
-/
theorem IsVanKampenColimit.of_iso {F : J ⥤ C} {c c' : Cocone F} (H : IsVanKampenColimit c)
    (e : c ≅ c') : IsVanKampenColimit c' := by
  intro F' c'' α f h hα
  have : c'.ι ≫ (Functor.const J).map e.inv.hom = c.ι := by
    ext j
    exact e.inv.2 j
  rw [H c'' α (f ≫ e.inv.1) (by rw [Functor.map_comp, ← reassoc_of% h, this]) hα]
  apply forall_congr'
  intro j
  conv_lhs => rw [← Category.comp_id (α.app j)]
  have : IsIso e.inv.hom := Functor.map_isIso (Cocone.forget _) e.inv
  exact (IsPullback.of_vert_isIso ⟨by simp⟩).paste_vert_iff (NatTrans.congr_app h j).symm

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsVanKampenColimit.precompose_isIso** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.IsVanKampenColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F G : CategoryTheory.Functor J C} 
(α : F ⟶ G) [CategoryTheory.IsIso α] {c : CategoryTheory.Limits.Cocone G},   Cat
egoryTheory.IsVanKampenColimit c →     CategoryTheory.IsVanKampenColimit ((Categ
oryTheory.Limits.Cocone.precompose α).obj c)
参数：α : F ⟶ G；(CategoryTheory.Limits.Cocone.precompose α).obj c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.Equifibered.comp`：∀ {J : Type u_1} {C : Type u_3
} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_3} C] {F G H : Cat…
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_isIso`：∀ {J : Type u_1} {C : Type
 u_3} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_3} C] {F G : Categ…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso`：of_vert_isIso [IsIso snd] [IsIs
o f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPullback.paste_vert_iff`：paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂
₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ 
⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ …
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsVanKampenColimit.precompose_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
    {c : Cocone G} (hc : IsVanKampenColimit c) :
    IsVanKampenColimit ((Cocone.precompose α).obj c) := by
  intro F' c' α' f e hα
  refine (hc c' (α' ≫ α) f ((Category.assoc _ _ _).trans e) (hα.comp (.of_isIso _))).trans ?_
  apply forall_congr'
  intro j
  simp only [NatTrans.comp_app, Cocone.precompose_obj_ι]
  have : IsPullback (α.app j ≫ c.ι.app j) (α.app j) (𝟙 _) (c.ι.app j) :=
    IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  rw [← IsPullback.paste_vert_iff this _, Category.comp_id]
  exact (congr_app e j).symm

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsUniversalColimit.precompose_isIso** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.IsUniversalColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F G : CategoryTheory.Functor J C} 
(α : F ⟶ G) [CategoryTheory.IsIso α] {c : CategoryTheory.Limits.Cocone G},   Cat
egoryTheory.IsUniversalColimit c →     CategoryTheory.IsUniversalColimit ((Categ
oryTheory.Limits.Cocone.precompose α).obj c)
参数：α : F ⟶ G；(CategoryTheory.Limits.Cocone.precompose α).obj c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.Equifibered.comp`：∀ {J : Type u_1} {C : Type u_3
} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_3} C] {F G H : Cat…
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_isIso`：∀ {J : Type u_1} {C : Type
 u_3} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_3} C] {F G : Categ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso`：of_vert_isIso [IsIso snd] [IsIs
o f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
-/
theorem IsUniversalColimit.precompose_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
    {c : Cocone G} (hc : IsUniversalColimit c) :
    IsUniversalColimit ((Cocone.precompose α).obj c) := by
  intro F' c' α' f e hα H
  apply (hc c' (α' ≫ α) f ((Category.assoc _ _ _).trans e) (hα.comp (.of_isIso _)))
  intro j
  simp only [NatTrans.comp_app]
  rw [← Category.comp_id f]
  exact (H j).paste_vert (IsPullback.of_vert_isIso ⟨Category.comp_id _⟩)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.IsVanKampenColimit.precompose_isIso_iff** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.IsVanKampenColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {F G : CategoryTheory.Functor J C} 
(α : F ⟶ G) [CategoryTheory.IsIso α] {c : CategoryTheory.Limits.Cocone G},   Cat
egoryTheory.IsVanKampenColimit ((CategoryTheory.Limits.Cocone.precompose α).obj 
c) ↔     CategoryTheory.IsVanKampenColimit c
参数：α : F ⟶ G；(CategoryTheory.Limits.Cocone.precompose α).obj c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsVanKampenColimit.of_iso`：∀ {J : Type v'} [inst : Catego
ryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.IsVanKampenColimit.precompose_isIso`：∀ {J : Type v'} [ins
t : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Ca
tegory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsVanKampenColimit.precompose_isIso_iff {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
    {c : Cocone G} : IsVanKampenColimit ((Cocone.precompose α).obj c) ↔ IsVanKampenColimit c :=
  ⟨fun hc ↦ IsVanKampenColimit.of_iso (IsVanKampenColimit.precompose_isIso (inv α) hc)
    (Cocone.ext (Iso.refl _) (by simp)),
    IsVanKampenColimit.precompose_isIso α⟩
/-
**CategoryTheory.IsUniversalColimit.of_mapCocone** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.IsUniversalColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {D : Type u_2} [inst_2 : CategoryTh
eory.Category.{v_2, u_2} D] (G : CategoryTheory.Functor C D)   {F : CategoryTheo
ry.Functor J C} {c : CategoryTheory.Limits.Cocone F}   [CategoryTheory.Limits.Pr
eservesLimitsOfShape CategoryTheory.Limits.WalkingCospan G]   [CategoryTheory.Li
mits.ReflectsColimitsOfShape J G],   CategoryTheory.IsUniversalColimit (G.mapCoc
one c) → CategoryTheory.IsUniversalColimit c
参数：G : CategoryTheory.Functor C D；G.mapCocone c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.NatTrans.Equifibered.whiskerRight`：∀ {J : Type u_1} {C : 
Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1
 : CategoryTheory.Category.{v_2, u_3} …
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.IsPullback.map`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
-/
theorem IsUniversalColimit.of_mapCocone (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
    [PreservesLimitsOfShape WalkingCospan G] [ReflectsColimitsOfShape J G]
    (hc : IsUniversalColimit (G.mapCocone c)) : IsUniversalColimit c :=
  fun F' c' α f h hα H ↦
    ⟨isColimitOfReflects _ (hc (G.mapCocone c') (whiskerRight α G) (G.map f)
    (by ext j; simpa using! G.congr_map (NatTrans.congr_app h j))
    (hα.whiskerRight G) (fun j ↦ (H j).map G)).some⟩
/-
**CategoryTheory.IsVanKampenColimit.of_mapCocone** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.IsVanKampenColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {D : Type u_2} [inst_2 : CategoryTh
eory.Category.{v_2, u_2} D] (G : CategoryTheory.Functor C D)   {F : CategoryTheo
ry.Functor J C} {c : CategoryTheory.Limits.Cocone F}   [∀ (i j : J) (X : C) (f :
 X ⟶ F.obj j) (g : i ⟶ j),       CategoryTheory.Limits.PreservesLimit (CategoryT
heory.Limits.cospan f (F.map g)) G]   [∀ (i : J) (X : C) (f : X ⟶ c.pt),       C
ategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.cospan f (c.ι.app i))
 G]   [CategoryTheory.Limits.ReflectsLimitsOfShape CategoryTheory.Limits.Walking
Cospan G]   [CategoryTheory.Limits.PreservesColimitsOfShape J G] [CategoryTheory
.Limits.ReflectsColimitsOfShape J G],   CategoryTheory.IsVanKampenColimit (G.map
Cocone c) → CategoryTheory.IsVanKampenColimit c
参数：G : CategoryTheory.Functor C D；i j : J；X : C；f : X ⟶ F.obj j；g : i ⟶ j；Catego
ryTheory.Limits.cospan f (F.map g)；i : J；X : C；f : X ⟶ c.pt；CategoryTheory.Limit
s.cospan f (c.ι.app i)；G.mapCocone c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.NatTrans.Equifibered.whiskerRight`：∀ {J : Type u_1} {C : 
Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1
 : CategoryTheory.Category.{v_2, u_3} …
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `CategoryTheory.IsPullback.map_iff`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : 
Y ⟶ Z} {D : Type u_1} […
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsVanKampenColimit.of_mapCocone (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
    [∀ (i j : J) (X : C) (f : X ⟶ F.obj j) (g : i ⟶ j), PreservesLimit (cospan f (F.map g)) G]
    [∀ (i : J) (X : C) (f : X ⟶ c.pt), PreservesLimit (cospan f (c.ι.app i)) G]
    [ReflectsLimitsOfShape WalkingCospan G]
    [PreservesColimitsOfShape J G]
    [ReflectsColimitsOfShape J G]
    (H : IsVanKampenColimit (G.mapCocone c)) : IsVanKampenColimit c := by
  intro F' c' α f h hα
  refine (Iff.trans ?_ (H (G.mapCocone c') (whiskerRight α G) (G.map f)
      (by ext j; simpa using! G.congr_map (NatTrans.congr_app h j))
      (hα.whiskerRight G))).trans (forall_congr' fun j => ?_)
  · exact ⟨fun h => ⟨isColimitOfPreserves G h.some⟩, fun h => ⟨isColimitOfReflects G h.some⟩⟩
  · exact IsPullback.map_iff G (NatTrans.congr_app h.symm j)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsVanKampenColimit.mapCocone_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.IsVanKampenColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {D : Type u_2} [inst_2 : CategoryTh
eory.Category.{v_2, u_2} D] (G : CategoryTheory.Functor C D)   {F : CategoryTheo
ry.Functor J C} {c : CategoryTheory.Limits.Cocone F} [G.IsEquivalence],   Catego
ryTheory.IsVanKampenColimit (G.mapCocone c) ↔ CategoryTheory.IsVanKampenColimit 
c
参数：G : CategoryTheory.Functor C D；G.mapCocone c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsVanKampenColimit.of_mapCocone`：∀ {J : Type v'} [inst : 
CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {D : Type u_2} [inst_…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instReflectsFiniteLimitsOfReflectsLimits`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.IsVanKampenColimit.precompose_isIso_iff`：∀ {J : Type v'} 
[inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheor
y.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.IsVanKampenColimit.of_iso`：∀ {J : Type v'} [inst : Catego
ryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatIso.hcomp_inv`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   {E : Type u₃} [ins…
· 使用引理 `CategoryTheory.Functor.id_hcomp`：id_hcomp (F : C ⥤ D) {G H : D ⥤ E} (α :
 G ⟶ H) : 𝟙 F ◫ α = whiskerLeft F α
· 使用定理 `CategoryTheory.Functor.inv_fun_map`：inv_fun_map (F : C ⥤ D) [IsEquivalen
ce F] (X Y : C) (f : X ⟶ Y) : F.inv.map (F.map f) = F.asEquivalence.unitInv.app 
X ≫ f ≫ F.asEquivalence.…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsVanKampenColimit.mapCocone_iff (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
    [G.IsEquivalence] : IsVanKampenColimit (G.mapCocone c) ↔ IsVanKampenColimit c :=
  ⟨IsVanKampenColimit.of_mapCocone G, fun hc ↦ by
    let e : F ⋙ G ⋙ Functor.inv G ≅ F := NatIso.hcomp (Iso.refl F) G.asEquivalence.unitIso.symm
    apply IsVanKampenColimit.of_mapCocone G.inv
    apply (IsVanKampenColimit.precompose_isIso_iff e.inv).mp
    exact hc.of_iso (Cocone.ext (G.asEquivalence.unitIso.app c.pt) (fun j => (by simp [e])))⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsUniversalColimit.whiskerEquivalence** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.IsUniversalColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {K : Type u_3} [inst_2 : CategoryTh
eory.Category.{v_3, u_3} K] (e : J ≌ K) {F : CategoryTheory.Functor K C}   {c : 
CategoryTheory.Limits.Cocone F},   CategoryTheory.IsUniversalColimit c →     Cat
egoryTheory.IsUniversalColimit (CategoryTheory.Limits.Cocone.whisker e.functor c
)
参数：e : J ≌ K；CategoryTheory.Limits.Cocone.whisker e.functor c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
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
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Equivalence.invFunIdAssoc_hom_app`：invFunIdAssoc_hom_app 
(e : C ≌ D) (F : D ⥤ E) (X : D) : (invFunIdAssoc e F).hom.app X = F.map (e.couni
t.app X)
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.Equifibered.comp`：∀ {J : Type u_1} {C : Type u_3
} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_3} C] {F G H : Cat…
· 使用定理 `CategoryTheory.NatTrans.Equifibered.whiskerLeft`：∀ {J : Type u_1} {K : T
ype u_2} {C : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 
: CategoryTheory.Category.{v_2, u_3} …
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_isIso`：∀ {J : Type u_1} {C : Type
 u_3} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_3} C] {F G : Categ…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso`：of_vert_isIso [IsIso snd] [IsIs
o f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
-/
theorem IsUniversalColimit.whiskerEquivalence {K : Type*} [Category* K] (e : J ≌ K)
    {F : K ⥤ C} {c : Cocone F} (hc : IsUniversalColimit c) :
    IsUniversalColimit (c.whisker e.functor) := by
  intro F' c' α f e' hα H
  convert!
    hc (c'.whisker e.inverse) (whiskerLeft e.inverse α ≫ (e.invFunIdAssoc F).hom) f ?_
      ((hα.whiskerLeft _).comp (.of_isIso _)) ?_ using 1
  · exact (IsColimit.whiskerEquivalenceEquiv e.symm).nonempty_congr
  · convert! congr_arg (whiskerLeft e.inverse) e'
    ext
    simp
  · intro k
    rw [← Category.comp_id f]
    refine (H (e.inverse.obj k)).paste_vert ?_
    exact IsPullback.of_vert_isIso ⟨by simp⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.IsUniversalColimit.whiskerEquivalence_iff** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.IsUniversalColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {K : Type u_3} [inst_2 : CategoryTh
eory.Category.{v_3, u_3} K] (e : J ≌ K) {F : CategoryTheory.Functor K C}   {c : 
CategoryTheory.Limits.Cocone F},   CategoryTheory.IsUniversalColimit (CategoryTh
eory.Limits.Cocone.whisker e.functor c) ↔     CategoryTheory.IsUniversalColimit 
c
参数：e : J ≌ K；CategoryTheory.Limits.Cocone.whisker e.functor c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsUniversalColimit.of_iso`：∀ {J : Type v'} [inst : Catego
ryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.IsUniversalColimit.precompose_isIso`：∀ {J : Type v'} [ins
t : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Ca
tegory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.IsUniversalColimit.whiskerEquivalence`：∀ {J : Type v'} [i
nst : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {K : Type u_3} [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Equivalence.invFunIdAssoc_inv_app`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsUniversalColimit.whiskerEquivalence_iff {K : Type*} [Category* K] (e : J ≌ K)
    {F : K ⥤ C} {c : Cocone F} :
    IsUniversalColimit (c.whisker e.functor) ↔ IsUniversalColimit c :=
  ⟨fun hc ↦ ((hc.whiskerEquivalence e.symm).precompose_isIso (e.invFunIdAssoc F).inv).of_iso
      (Cocone.ext (Iso.refl _) (by simp)), IsUniversalColimit.whiskerEquivalence e⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsVanKampenColimit.whiskerEquivalence** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.IsVanKampenColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {K : Type u_3} [inst_2 : CategoryTh
eory.Category.{v_3, u_3} K] (e : J ≌ K) {F : CategoryTheory.Functor K C}   {c : 
CategoryTheory.Limits.Cocone F},   CategoryTheory.IsVanKampenColimit c →     Cat
egoryTheory.IsVanKampenColimit (CategoryTheory.Limits.Cocone.whisker e.functor c
)
参数：e : J ≌ K；CategoryTheory.Limits.Cocone.whisker e.functor c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Equivalence.invFunIdAssoc_hom_app`：invFunIdAssoc_hom_app 
(e : C ≌ D) (F : D ⥤ E) (X : D) : (invFunIdAssoc e F).hom.app X = F.map (e.couni
t.app X)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso`：of_vert_isIso [IsIso snd] [IsIs
o f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Equivalence.functor_unit_comp`：functor_unit_comp (e : C ≌
 D) (X : C) : dsimp% e.functor.map (e.unit.app X) ≫ e.counit.app (e.functor.obj 
X) = 𝟙 (e.functor.obj X)
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.NatTrans.Equifibered.comp`：∀ {J : Type u_1} {C : Type u_3
} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_3} C] {F G H : Cat…
· 使用定理 `CategoryTheory.NatTrans.Equifibered.whiskerLeft`：∀ {J : Type u_1} {K : T
ype u_2} {C : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 
: CategoryTheory.Category.{v_2, u_3} …
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_isIso`：∀ {J : Type u_1} {C : Type
 u_3} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_3} C] {F G : Categ…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
theorem IsVanKampenColimit.whiskerEquivalence {K : Type*} [Category* K] (e : J ≌ K)
    {F : K ⥤ C} {c : Cocone F} (hc : IsVanKampenColimit c) :
    IsVanKampenColimit (c.whisker e.functor) := by
  intro F' c' α f e' hα
  convert!
    hc (c'.whisker e.inverse) (whiskerLeft e.inverse α ≫ (e.invFunIdAssoc F).hom) f ?_
      ((hα.whiskerLeft _).comp (.of_isIso _)) using 1
  · exact (IsColimit.whiskerEquivalenceEquiv e.symm).nonempty_congr
  · simp only [Functor.const_obj_obj, Functor.comp_obj, Cocone.whisker_pt, Cocone.whisker_ι,
      whiskerLeft_app, NatTrans.comp_app, Equivalence.invFunIdAssoc_hom_app, Functor.id_obj]
    constructor
    · intro H k
      rw [← Category.comp_id f]
      refine (H (e.inverse.obj k)).paste_vert ?_
      have : IsIso (𝟙 (Cocone.whisker e.functor c).pt) := inferInstance
      exact IsPullback.of_vert_isIso ⟨by simp⟩
    · intro H j
      have : α.app j
          = F'.map (e.unit.app _) ≫ α.app _ ≫ F.map (e.counit.app (e.functor.obj j)) := by
        simp [← Functor.map_comp]
      rw [← Category.id_comp f, this]
      refine IsPullback.paste_vert ?_ (H (e.functor.obj j))
      exact IsPullback.of_vert_isIso ⟨by simp⟩
  · ext k
    simpa using congr_app e' (e.inverse.obj k)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.IsVanKampenColimit.whiskerEquivalence_iff** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.IsVanKampenColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {K : Type u_3} [inst_2 : CategoryTh
eory.Category.{v_3, u_3} K] (e : J ≌ K) {F : CategoryTheory.Functor K C}   {c : 
CategoryTheory.Limits.Cocone F},   CategoryTheory.IsVanKampenColimit (CategoryTh
eory.Limits.Cocone.whisker e.functor c) ↔     CategoryTheory.IsVanKampenColimit 
c
参数：e : J ≌ K；CategoryTheory.Limits.Cocone.whisker e.functor c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsVanKampenColimit.of_iso`：∀ {J : Type v'} [inst : Catego
ryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.IsVanKampenColimit.precompose_isIso`：∀ {J : Type v'} [ins
t : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Ca
tegory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.IsVanKampenColimit.whiskerEquivalence`：∀ {J : Type v'} [i
nst : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {K : Type u_3} [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Equivalence.invFunIdAssoc_inv_app`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsVanKampenColimit.whiskerEquivalence_iff {K : Type*} [Category* K] (e : J ≌ K)
    {F : K ⥤ C} {c : Cocone F} :
    IsVanKampenColimit (c.whisker e.functor) ↔ IsVanKampenColimit c :=
  ⟨fun hc ↦ ((hc.whiskerEquivalence e.symm).precompose_isIso (e.invFunIdAssoc F).inv).of_iso
      (Cocone.ext (Iso.refl _) (by simp)), IsVanKampenColimit.whiskerEquivalence e⟩
/-
**CategoryTheory.isVanKampenColimit_of_evaluation** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：isVanKampenColimit_of_evaluation [HasPullbacks D] [HasColimitsOfShape J D]
 (F : J ⥤ C ⥤ D) (c : Cocone F) (hc : forall x : C, IsVanKampenColimit (((evalua
tion C D).obj x).mapCocone c)) : IsVanKampenColimit c
参数：F : J ⥤ C ⥤ D；c : Cocone F；hc : forall x : C, IsVanKampenColimit (((evaluatio
n C D).obj x).mapCocone c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.NatTrans.Equifibered.whiskerRight`：∀ {J : Type u_1} {C : 
Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1
 : CategoryTheory.Category.{v_2, u_3} …
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.IsPullback.map`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
-/
theorem isVanKampenColimit_of_evaluation [HasPullbacks D] [HasColimitsOfShape J D] (F : J ⥤ C ⥤ D)
    (c : Cocone F) (hc : ∀ x : C, IsVanKampenColimit (((evaluation C D).obj x).mapCocone c)) :
    IsVanKampenColimit c := by
  intro F' c' α f e hα
  have := fun x => hc x (((evaluation C D).obj x).mapCocone c') (whiskerRight α _)
      (((evaluation C D).obj x).map f)
      (by
        ext y
        dsimp
        exact NatTrans.congr_app (NatTrans.congr_app e y) x)
      (hα.whiskerRight _)
  constructor
  · rintro ⟨hc'⟩ j
    refine ⟨⟨(NatTrans.congr_app e j).symm⟩, ⟨evaluationJointlyReflectsLimits _ ?_⟩⟩
    refine fun x => (isLimitMapConePullbackConeEquiv _ _).symm ?_
    exact ((this x).mp ⟨isColimitOfPreserves _ hc'⟩ _).isLimit
  · exact fun H => ⟨evaluationJointlyReflectsColimits _ fun x =>
      ((this x).mpr fun j => (H j).map ((evaluation C D).obj x)).some⟩

end Functor

section reflective

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsUniversalColimit.map_reflective** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.IsUniversalColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {D : Type u_2} [inst_2 : CategoryTh
eory.Category.{v_2, u_2} D] {Gl : CategoryTheory.Functor C D}   {Gr : CategoryTh
eory.Functor D C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful] {F : CategoryTheory.Fu
nctor J D}   {c : CategoryTheory.Limits.Cocone (F.comp Gr)},   CategoryTheory.Is
UniversalColimit c →     ∀ [∀ (X : D) (f : X ⟶ Gl.obj c.pt), CategoryTheory.Limi
ts.HasPullback (Gr.map f) (adj.unit.app c.pt)]       [∀ (X : D) (f : X ⟶ Gl.obj 
c.pt),           CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.cos
pan (Gr.map f) (adj.unit.app c.pt)) Gl],       CategoryTheory.IsUniversalColimit
 (Gl.mapCocone c)
参数：adj : Gl ⊣ Gr；F.comp Gr；X : D；f : X ⟶ Gl.obj c.pt；Gr.map f；adj.unit.app c.pt；
X : D；f : X ⟶ Gl.obj c.pt；CategoryTheory.Limits.cospan (Gr.map f) (adj.unit.app 
c.pt)；Gl.mapCocone c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`：rightAdjoint_pre
servesLimits : PreservesLimitsOfSize.{v, u} G where preservesLimitsOfShape
· 使用引理 `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`：leftAdjoint_pre
servesColimits : PreservesColimitsOfSize.{v, u} F where preservesColimitsOfShape
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `CategoryTheory.NatTrans.Equifibered.comp`：∀ {J : Type u_1} {C : Type u_3
} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_3} C] {F G H : Cat…
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_isIso`：∀ {J : Type u_1} {C : Type
 u_3} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_3} C] {F G : Categ…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_inv_hom_id`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} {f : Y ⟶ X} [inst_1 : CategoryTheory.IsIso
 f]   {g : X ⟶ Y}, CategoryTheo…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality_assoc`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Adjunction.unit_naturality`：unit_naturality {X Y : C} (f 
: X ⟶ Y) : dsimp% adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components_assoc`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   {F : CategoryTheor…
（共 59 条，此处仅展示前 30 条）
-/
theorem IsUniversalColimit.map_reflective
    {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful]
    {F : J ⥤ D} {c : Cocone (F ⋙ Gr)}
    (H : IsUniversalColimit c)
    [∀ X (f : X ⟶ Gl.obj c.pt), HasPullback (Gr.map f) (adj.unit.app c.pt)]
    [∀ X (f : X ⟶ Gl.obj c.pt), PreservesLimit (cospan (Gr.map f) (adj.unit.app c.pt)) Gl] :
    IsUniversalColimit (Gl.mapCocone c) := by
  have := adj.rightAdjoint_preservesLimits
  have : PreservesColimitsOfSize.{u', v'} Gl := adj.leftAdjoint_preservesColimits
  intro F' c' α f h hα hc'
  have : HasPullback (Gl.map (Gr.map f)) (Gl.map (adj.unit.app c.pt)) :=
    ⟨⟨_, isLimitPullbackConeMapOfIsLimit _ pullback.condition
      (IsPullback.of_hasPullback _ _).isLimit⟩⟩
  let α' := α ≫ (Functor.associator _ _ _).hom ≫ whiskerLeft F adj.counit ≫ F.rightUnitor.hom
  have hα' : NatTrans.Equifibered α' := hα.comp (.of_isIso _)
  have hadj : ∀ X, Gl.map (adj.unit.app X) = inv (adj.counit.app _) := by
    intro X
    apply IsIso.eq_inv_of_inv_hom_id
    exact adj.left_triangle_components _
  have : ∀ X, IsIso (Gl.map (adj.unit.app X)) := by
    simp_rw [hadj]
    infer_instance
  have hα'' : ∀ j, Gl.map (Gr.map <| α'.app j) = adj.counit.app _ ≫ α.app j := by
    intro j
    rw [← cancel_mono (adj.counit.app <| F.obj j)]
    dsimp [α']
    simp only [Category.comp_id, Adjunction.counit_naturality_assoc, Category.id_comp,
      Adjunction.counit_naturality, Category.assoc, Functor.map_comp]
  have hc'' : ∀ j, α.app j ≫ Gl.map (c.ι.app j) = c'.ι.app j ≫ f := NatTrans.congr_app h
  let β := isoWhiskerLeft F' (asIso adj.counit) ≪≫ F'.rightUnitor
  let c'' : Cocone (F' ⋙ Gr) := by
    refine
    { pt := pullback (Gr.map f) (adj.unit.app _)
      ι := { app := fun j ↦ pullback.lift (Gr.map <| c'.ι.app j) (Gr.map (α'.app j) ≫ c.ι.app j) ?_
             naturality := ?_ } }
    · rw [← Gr.map_comp, ← hc'']
      simp_all [← adj.unit_naturality]
    · intro i j g
      dsimp [α']
      ext
      all_goals simp only [Category.comp_id, Category.id_comp, Category.assoc,
        ← Functor.map_comp, pullback.lift_fst, pullback.lift_snd, ← Functor.map_comp_assoc]
      · congr 1
        exact c'.w _
      · rw [α.naturality_assoc]
        dsimp
        rw [adj.counit_naturality, ← Category.assoc, Gr.map_comp_assoc]
        congr 1
        exact c.w _
  let cf : (Cocone.precompose β.hom).obj c' ⟶ Gl.mapCocone c'' := by
    refine { hom := pullback.lift ?_ f ?_ ≫ (PreservesPullback.iso _ _ _).inv, w := ?_ }
    · exact inv <| adj.counit.app c'.pt
    · simp [← cancel_mono (adj.counit.app <| Gl.obj c.pt)]
    · intro j
      rw [← Category.assoc, Iso.comp_inv_eq]
      ext
      all_goals simp only [c'', PreservesPullback.iso_hom_fst, PreservesPullback.iso_hom_snd,
          pullback.lift_fst, pullback.lift_snd, Category.assoc,
          Functor.mapCocone_ι_app, ← Gl.map_comp]
      · dsimp [β]
        simp only [IsIso.comp_inv_eq, adj.counit_naturality, Category.comp_id]
      · rw [Gl.map_comp, hα'', Category.assoc, hc'']
        dsimp [β]
        rw [Category.comp_id, Category.assoc]
  have :
      cf.hom ≫ (PreservesPullback.iso _ _ _).hom ≫ pullback.fst _ _ ≫ adj.counit.app _ = 𝟙 _ := by
    simp only [cf, IsIso.inv_hom_id, Iso.inv_hom_id_assoc, Category.assoc,
      pullback.lift_fst_assoc]
  have : IsIso cf := by
    apply @Cocone.cocone_iso_of_hom_iso (i := ?_)
    rw [← IsIso.eq_comp_inv] at this
    rw [this]
    infer_instance
  have ⟨Hc''⟩ := H c'' (whiskerRight α' Gr) (pullback.snd _ _) ?_ (hα'.whiskerRight Gr) ?_
  · exact ⟨IsColimit.precomposeHomEquiv β c' <|
      (isColimitOfPreserves Gl Hc'').ofIsoColimit (asIso cf).symm⟩
  · ext j
    dsimp [c'']
    simp only [pullback.lift_snd]
  · intro j
    apply IsPullback.of_right _ _ (IsPullback.of_hasPullback _ _)
    · dsimp [α', c'']
      simp only [Category.comp_id, Category.id_comp, Category.assoc, Functor.map_comp,
        pullback.lift_fst]
      rw [← Category.comp_id (Gr.map f)]
      refine ((hc' j).map Gr).paste_vert (IsPullback.of_vert_isIso ⟨?_⟩)
      rw [← adj.unit_naturality, Category.comp_id, ← Category.assoc,
        ← Category.id_comp (Gr.map ((Gl.mapCocone c).ι.app j))]
      congr 1
      rw [← cancel_mono (Gr.map (adj.counit.app (F.obj j)))]
      dsimp
      simp only [Category.comp_id, Adjunction.right_triangle_components, Category.id_comp,
        Category.assoc]
    · dsimp [c'']
      simp only [pullback.lift_snd]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsVanKampenColimit.map_reflective** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.IsVanKampenColimit`。
形式化陈述：∀ {J : Type v'} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {D : Type u_2} [inst_2 : CategoryTh
eory.Category.{v_2, u_2} D] [CategoryTheory.Limits.HasColimitsOfShape J C]   {Gl
 : CategoryTheory.Functor C D} {Gr : CategoryTheory.Functor D C} (adj : Gl ⊣ Gr)
 [Gr.Full] [Gr.Faithful]   {F : CategoryTheory.Functor J D} {c : CategoryTheory.
Limits.Cocone (F.comp Gr)},   CategoryTheory.IsVanKampenColimit c →     ∀ [∀ (X 
: D) (f : X ⟶ Gl.obj c.pt), CategoryTheory.Limits.HasPullback (Gr.map f) (adj.un
it.app c.pt)]       [∀ (X : D) (f : X ⟶ Gl.obj c.pt),           CategoryTheory.L
imits.PreservesLimit (CategoryTheory.Limits.cospan (Gr.map f) (adj.unit.app c.pt
)) Gl]       [∀ (X : C) (i : J) (f : X ⟶ c.pt),           CategoryTheory.Limits.
PreservesLimit (CategoryTheory.Limits.cospan f (c.ι.app i)) Gl],       CategoryT
heory.IsVanKampenColimit (Gl.mapCocone c)
参数：adj : Gl ⊣ Gr；F.comp Gr；X : D；f : X ⟶ Gl.obj c.pt；Gr.map f；adj.unit.app c.pt；
X : D；f : X ⟶ Gl.obj c.pt；CategoryTheory.Limits.cospan (Gr.map f) (adj.unit.app 
c.pt)；X : C；i : J；f : X ⟶ c.pt；CategoryTheory.Limits.cospan f (c.ι.app i)；Gl.map
Cocone c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`：rightAdjoint_pre
servesLimits : PreservesLimitsOfSize.{v, u} G where preservesLimitsOfShape
· 使用引理 `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`：leftAdjoint_pre
servesColimits : PreservesColimitsOfSize.{v, u} F where preservesColimitsOfShape
· 使用定理 `CategoryTheory.NatTrans.Equifibered.comp`：∀ {J : Type u_1} {C : Type u_3
} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_3} C] {F G H : Cat…
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_isIso`：∀ {J : Type u_1} {C : Type
 u_3} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_3} C] {F G : Categ…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality_assoc`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 54 条，此处仅展示前 30 条）
-/
theorem IsVanKampenColimit.map_reflective [HasColimitsOfShape J C]
    {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful]
    {F : J ⥤ D} {c : Cocone (F ⋙ Gr)} (H : IsVanKampenColimit c)
    [∀ X (f : X ⟶ Gl.obj c.pt), HasPullback (Gr.map f) (adj.unit.app c.pt)]
    [∀ X (f : X ⟶ Gl.obj c.pt), PreservesLimit (cospan (Gr.map f) (adj.unit.app c.pt)) Gl]
    [∀ X i (f : X ⟶ c.pt), PreservesLimit (cospan f (c.ι.app i)) Gl] :
    IsVanKampenColimit (Gl.mapCocone c) := by
  have := adj.rightAdjoint_preservesLimits
  have : PreservesColimitsOfSize.{u', v'} Gl := adj.leftAdjoint_preservesColimits
  intro F' c' α f h hα
  refine ⟨?_, H.isUniversal.map_reflective adj c' α f h hα⟩
  intro ⟨hc'⟩ j
  let α' := α ≫ (Functor.associator _ _ _).hom ≫ whiskerLeft F adj.counit ≫ F.rightUnitor.hom
  have hα' : NatTrans.Equifibered α' := hα.comp (.of_isIso _)
  have hα'' : ∀ j, Gl.map (Gr.map <| α'.app j) = adj.counit.app _ ≫ α.app j := by
    intro j
    rw [← cancel_mono (adj.counit.app <| F.obj j)]
    dsimp [α']
    simp only [Category.comp_id, Adjunction.counit_naturality_assoc, Category.id_comp,
      Adjunction.counit_naturality, Category.assoc, Functor.map_comp]
  let β := isoWhiskerLeft F' (asIso adj.counit) ≪≫ F'.rightUnitor
  let hl := (IsColimit.precomposeHomEquiv β c').symm hc'
  let hr := isColimitOfPreserves Gl (colimit.isColimit <| F' ⋙ Gr)
  have : α.app j = β.inv.app _ ≫ Gl.map (Gr.map <| α'.app j) := by
    rw [hα'']
    simp [β]
  rw [this]
  have : f = (hl.coconePointUniqueUpToIso hr).hom ≫
    Gl.map (colimit.desc _ ⟨_, whiskerRight α' Gr ≫ c.2⟩) := by
    symm
    convert!
      @IsColimit.coconePointUniqueUpToIso_hom_desc _ _ _ _ ((F' ⋙ Gr) ⋙ Gl)
        (Gl.mapCocone ⟨_, (whiskerRight α' Gr ≫ c.2 :)⟩) _ _ hl hr using 2
    · apply hr.hom_ext
      intro j
      rw [hr.fac, Functor.mapCocone_ι_app, ← Gl.map_comp, colimit.cocone_ι, colimit.ι_desc]
      rfl
    · clear_value α'
      apply hl.hom_ext
      intro j
      rw [hl.fac]
      dsimp [β]
      simp only [Category.comp_id, hα'', Category.assoc, Gl.map_comp]
      congr 1
      exact (NatTrans.congr_app h j).symm
  rw [this]
  have := ((H (colimit.cocone <| F' ⋙ Gr) (whiskerRight α' Gr)
    (colimit.desc _ ⟨_, whiskerRight α' Gr ≫ c.2⟩) ?_ (hα'.whiskerRight Gr)).mp
    ⟨(getColimitCocone <| F' ⋙ Gr).2⟩ j).map Gl
  · convert! IsPullback.paste_vert _ this
    refine IsPullback.of_vert_isIso ⟨?_⟩
    rw [← IsIso.inv_comp_eq, ← Category.assoc, NatIso.inv_inv_app]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom hl hr _
  · clear_value α'
    ext j
    simp

end reflective

section Initial

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.hasStrictInitial_of_isUniversal** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory`。
形式化陈述：hasStrictInitial_of_isUniversal [HasInitial C] (H : IsUniversalColimit (Bi
naryCofan.mk (𝟙 (⊥_ C)) (𝟙 (⊥_ C)))) : HasStrictInitialObjects C
参数：H : IsUniversalColimit (BinaryCofan.mk (𝟙 (⊥_ C)) (𝟙 (⊥_ C)))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasStrictInitialObjects_of_initial_is_strict`：hasS
trictInitialObjects_of_initial_is_strict [HasInitial C] (h : forall (A) (f : A ⟶
 ⊥_ C), IsIso f) : HasStrictInitialObjects C
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
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_discrete`：∀ {C : Type u_3} {ι : T
ype u_5} [inst : CategoryTheory.Category.{v_2, u_3} C]   {F G : CategoryTheory.F
unctor (CategoryTheory.Discrete ι) C}…
· 使用定理 `CategoryTheory.IsPullback.of_horiz_isIso`：of_horiz_isIso [IsIso fst] [Is
Iso g] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
-/
theorem hasStrictInitial_of_isUniversal [HasInitial C]
    (H : IsUniversalColimit (BinaryCofan.mk (𝟙 (⊥_ C)) (𝟙 (⊥_ C)))) : HasStrictInitialObjects C :=
  hasStrictInitialObjects_of_initial_is_strict
    (by
      intro A f
      suffices IsColimit (BinaryCofan.mk (𝟙 A) (𝟙 A)) by
        obtain ⟨l, h₁, h₂⟩ := Limits.BinaryCofan.IsColimit.desc' this (f ≫ initial.to A) (𝟙 A)
        rcases (Category.id_comp _).symm.trans h₂ with rfl
        exact ⟨⟨_, ((Category.id_comp _).symm.trans h₁).symm, initialIsInitial.hom_ext _ _⟩⟩
      refine (H (BinaryCofan.mk (𝟙 _) (𝟙 _)) (mapPair f f) f (by ext ⟨⟨⟩⟩ <;> simp)
        (.of_discrete _) ?_).some
      rintro ⟨⟨⟩⟩ <;> dsimp <;>
        exact IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩)
/-
**CategoryTheory.isVanKampenColimit_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory`。
形式化陈述：isVanKampenColimit_of_isEmpty [HasStrictInitialObjects C] [IsEmpty J] {F :
 J ⥤ C} (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c
参数：c : Cocone F；hc : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsEmptyDiscrete`：∀ (α : Type u_1) [IsEmpty α], IsEmpt
y (CategoryTheory.Discrete α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.IsInitial.isVanKampenColimit`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasStrictInitialObjects C] 
{X : C}   (h : CategoryTheory.Lim…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.IsVanKampenColimit.whiskerEquivalence_iff`：∀ {J : Type v'
} [inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   {K : Type u_3} [inst_…
· 使用定理 `CategoryTheory.IsVanKampenColimit.of_iso`：∀ {J : Type v'} [inst : Catego
ryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.IsVanKampenColimit.precompose_isIso`：∀ {J : Type v'} [ins
t : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Ca
tegory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem isVanKampenColimit_of_isEmpty [HasStrictInitialObjects C] [IsEmpty J] {F : J ⥤ C}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c := by
  have : IsInitial c.pt := by
    have := (IsColimit.precomposeInvEquiv (Functor.uniqueFromEmpty _) _).symm
      (hc.whiskerEquivalence (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J))
    exact IsColimit.ofIsoColimit this (Cocone.ext (Iso.refl c.pt) (fun {X} ↦ isEmptyElim X))
  replace this := IsInitial.isVanKampenColimit this
  apply (IsVanKampenColimit.whiskerEquivalence_iff
    (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J)).mp
  exact (this.precompose_isIso (Functor.uniqueFromEmpty
    ((equivalenceOfIsEmpty (Discrete PEmpty.{1}) J).functor ⋙ F)).hom).of_iso
    (Cocone.ext (Iso.refl _) (by simp))

end Initial

section BinaryCoproduct

variable {X Y : C}

/-
**CategoryTheory.BinaryCofan.isVanKampen_iff** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.BinaryCofan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (c : Ca
tegoryTheory.Limits.BinaryCofan X Y),   CategoryTheory.IsVanKampenColimit c ↔   
  ∀ {X' Y' : C} (c' : CategoryTheory.Limits.BinaryCofan X' Y') (αX : X' ⟶ X) (αY
 : Y' ⟶ Y) (f : c'.pt ⟶ c.pt),       CategoryTheory.CategoryStruct.comp αX c.inl
 = CategoryTheory.CategoryStruct.comp c'.inl f →         CategoryTheory.Category
Struct.comp αY c.inr = CategoryTheory.CategoryStruct.comp c'.inr f →           (
Nonempty (CategoryTheory.Limits.IsColimit c') ↔             CategoryTheory.IsPul
lback c'.inl αX f c.inl ∧ CategoryTheory.IsPullback c'.inr αY f c.inr)
参数：c : CategoryTheory.Limits.BinaryCofan X Y；c' : CategoryTheory.Limits.BinaryCo
fan X' Y'；αX : X' ⟶ X；αY : Y' ⟶ Y；f : c'.pt ⟶ c.pt；Nonempty (CategoryTheory.Limi
ts.IsColimit c') ↔             CategoryTheory.IsPullback c'.inl αX f c.inl ∧ Cat
egoryTheory.IsPullback c'.inr αY f c.inr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_discrete`：∀ {C : Type u_3} {ι : T
ype u_5} [inst : CategoryTheory.Category.{v_2, u_3} C]   {F G : CategoryTheory.F
unctor (CategoryTheory.Discrete ι) C}…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem BinaryCofan.isVanKampen_iff (c : BinaryCofan X Y) :
    IsVanKampenColimit c ↔
      ∀ {X' Y' : C} (c' : BinaryCofan X' Y') (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f : c'.pt ⟶ c.pt)
        (_ : αX ≫ c.inl = c'.inl ≫ f) (_ : αY ≫ c.inr = c'.inr ≫ f),
        Nonempty (IsColimit c') ↔ IsPullback c'.inl αX f c.inl ∧ IsPullback c'.inr αY f c.inr := by
  constructor
  · introv H hαX hαY
    rw [H c' (mapPair αX αY) f (by ext ⟨⟨⟩⟩ <;> dsimp <;> assumption) (.of_discrete _)]
    constructor
    · intro H
      exact ⟨H _, H _⟩
    · rintro H ⟨⟨⟩⟩
      exacts [H.1, H.2]
  · introv H F' hα h
    let X' := F'.obj ⟨WalkingPair.left⟩
    let Y' := F'.obj ⟨WalkingPair.right⟩
    have : F' = pair X' Y' := by
      apply Functor.hext
      · rintro ⟨⟨⟩⟩ <;> rfl
      · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp [X', Y']
    clear_value X' Y'
    subst this
    change BinaryCofan X' Y' at c'
    rw [H c' _ _ _ (NatTrans.congr_app hα ⟨WalkingPair.left⟩)
        (NatTrans.congr_app hα ⟨WalkingPair.right⟩)]
    constructor
    · rintro H ⟨⟨⟩⟩
      exacts [H.1, H.2]
    · intro H
      exact ⟨H _, H _⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.BinaryCofan.isVanKampen_mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.BinaryCofan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (c : Ca
tegoryTheory.Limits.BinaryCofan X Y)   (cofans : (X Y : C) → CategoryTheory.Limi
ts.BinaryCofan X Y)   (colimits : (X Y : C) → CategoryTheory.Limits.IsColimit (c
ofans X Y))   (cones : {X Y Z : C} → (f : X ⟶ Z) → (g : Y ⟶ Z) → CategoryTheory.
Limits.PullbackCone f g)   (limits : {X Y Z : C} → (f : X ⟶ Z) → (g : Y ⟶ Z) → C
ategoryTheory.Limits.IsLimit (cones f g)),   (∀ {X' Y' : C} (αX : X' ⟶ X) (αY : 
Y' ⟶ Y) (f : (cofans X' Y').pt ⟶ c.pt),       CategoryTheory.CategoryStruct.comp
 αX c.inl = CategoryTheory.CategoryStruct.comp (cofans X' Y').inl f →         Ca
tegoryTheory.CategoryStruct.comp αY c.inr = CategoryTheory.CategoryStruct.comp (
cofans X' Y').inr f →           CategoryTheory.IsPullback (cofans X' Y').inl αX 
f c.inl ∧             CategoryTheory.IsPullback (cofans X' Y').inr αY f c.inr) →
     ∀       (h₂ :         {Z : C} →           (f : Z ⟶ c.pt) →             Cate
goryTheory.Limits.IsColimit               (CategoryTheory.Limits.BinaryCofan.mk 
(cones f c.inl).fst (cones f c.inr).fst)),       CategoryTheory.IsVanKampenColim
it c
参数：c : CategoryTheory.Limits.BinaryCofan X Y；cofans : (X Y : C) → CategoryTheory
.Limits.BinaryCofan X Y；colimits : (X Y : C) → CategoryTheory.Limits.IsColimit (
cofans X Y)；cones : {X Y Z : C} → (f : X ⟶ Z) → (g : Y ⟶ Z) → CategoryTheory.Lim
its.PullbackCone f g；limits : {X Y Z : C} → (f : X ⟶ Z) → (g : Y ⟶ Z) → Category
Theory.Limits.IsLimit (cones f g)；∀ {X' Y' : C} (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f :
 (cofans X' Y').pt ⟶ c.pt),       CategoryTheory.CategoryStruct.comp αX c.inl = 
CategoryTheory.CategoryStruct.comp (cofans X' Y').inl f →         CategoryTheory
.CategoryStruct.comp αY c.inr = CategoryTheory.CategoryStruct.comp (cofans X' Y'
).inr f →           CategoryTheory.IsPullback (cofans X' Y').inl αX f c.inl ∧   
          CategoryTheory.IsPullback (cofans X' Y').inr αY f c.inr；h₂ :         {
Z : C} →           (f : Z ⟶ c.pt) →             CategoryTheory.Limits.IsColimit 
              (CategoryTheory.Limits.BinaryCofan.mk (cones f c.inl).fst (cones f
 c.inr).fst)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.BinaryCofan.isVanKampen_iff`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y : C} (c : CategoryTheory.Limits.BinaryCofan X 
Y),   CategoryTheory.IsVanKampen…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_inv_assoc`
：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst
_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso`：of_vert_isIso [IsIso snd] [IsIs
o f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
theorem BinaryCofan.isVanKampen_mk {X Y : C} (c : BinaryCofan X Y)
    (cofans : ∀ X Y : C, BinaryCofan X Y) (colimits : ∀ X Y, IsColimit (cofans X Y))
    (cones : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), PullbackCone f g)
    (limits : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), IsLimit (cones f g))
    (h₁ : ∀ {X' Y' : C} (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f : (cofans X' Y').pt ⟶ c.pt)
      (_ : αX ≫ c.inl = (cofans X' Y').inl ≫ f) (_ : αY ≫ c.inr = (cofans X' Y').inr ≫ f),
      IsPullback (cofans X' Y').inl αX f c.inl ∧ IsPullback (cofans X' Y').inr αY f c.inr)
    (h₂ : ∀ {Z : C} (f : Z ⟶ c.pt),
      IsColimit (BinaryCofan.mk (cones f c.inl).fst (cones f c.inr).fst)) :
    IsVanKampenColimit c := by
  rw [BinaryCofan.isVanKampen_iff]
  introv hX hY
  constructor
  · rintro ⟨h⟩
    let e := h.coconePointUniqueUpToIso (colimits _ _)
    obtain ⟨hl, hr⟩ := h₁ αX αY (e.inv ≫ f) (by simp [e, hX]) (by simp [e, hY])
    constructor
    · rw [← Category.id_comp αX, ← Iso.hom_inv_id_assoc e f]
      have : IsIso (𝟙 X') := inferInstance
      have : c'.inl ≫ e.hom = 𝟙 X' ≫ (cofans X' Y').inl := by
        dsimp [e]
        simp
      exact (IsPullback.of_vert_isIso ⟨this⟩).paste_vert hl
    · rw [← Category.id_comp αY, ← Iso.hom_inv_id_assoc e f]
      have : IsIso (𝟙 Y') := inferInstance
      have : c'.inr ≫ e.hom = 𝟙 Y' ≫ (cofans X' Y').inr := by
        dsimp [e]
        simp
      exact (IsPullback.of_vert_isIso ⟨this⟩).paste_vert hr
  · rintro ⟨H₁, H₂⟩
    refine ⟨IsColimit.ofIsoColimit ?_ <| (isoBinaryCofanMk _).symm⟩
    let e₁ : X' ≅ _ := H₁.isLimit.conePointUniqueUpToIso (limits _ _)
    let e₂ : Y' ≅ _ := H₂.isLimit.conePointUniqueUpToIso (limits _ _)
    have he₁ : c'.inl = e₁.hom ≫ (cones f c.inl).fst := by simp [e₁]
    have he₂ : c'.inr = e₂.hom ≫ (cones f c.inr).fst := by simp [e₂]
    rw [he₁, he₂]
    exact (BinaryCofan.mk _ _).isColimitCompRightIso e₂.hom
      ((BinaryCofan.mk _ _).isColimitCompLeftIso e₁.hom (h₂ f))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.BinaryCofan.mono_inr_of_isVanKampen** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.BinaryCofan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasInitial C] {X Y : C}   {c : CategoryTheory.Limits.BinaryCofan X Y}, Cat
egoryTheory.IsVanKampenColimit c → CategoryTheory.Mono c.inr
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.mono_of_isLimitMkIdId`：mono_of_isLimi
tMkIdId (f : X ⟶ Y) (t : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f)) : Mono
 f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
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
· 使用定理 `CategoryTheory.Limits.initial.to_comp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasInitial C] {P Q : 
C}   (f : P ⟶ Q),   Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_discrete`：∀ {C : Type u_3} {ι : T
ype u_5} [inst : CategoryTheory.Category.{v_2, u_3} C]   {F G : CategoryTheory.F
unctor (CategoryTheory.Discrete ι) C}…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.BinaryCofan.isColimit_iff_isIso_inr`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (h : CategoryTheory.Limits
.IsInitial X)   (c : CategoryTheory.Limits.Bina…
-/
theorem BinaryCofan.mono_inr_of_isVanKampen [HasInitial C] {X Y : C} {c : BinaryCofan X Y}
    (h : IsVanKampenColimit c) : Mono c.inr := by
  refine PullbackCone.mono_of_isLimitMkIdId _ (IsPullback.isLimit ?_)
  refine (h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr ?_
      (.of_discrete _)).mp ⟨?_⟩ ⟨WalkingPair.right⟩
  · ext ⟨⟨⟩⟩ <;> simp
  · exact ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.BinaryCofan.isPullback_initial_to_of_isVanKampen** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.BinaryCofan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1
 : CategoryTheory.Limits.HasInitial C]   {c : CategoryTheory.Limits.BinaryCofan 
X Y},   CategoryTheory.IsVanKampenColimit c →     CategoryTheory.IsPullback     
  (CategoryTheory.Limits.initial.to         ((CategoryTheory.Limits.pair X Y).ob
j { as := CategoryTheory.Limits.WalkingPair.left }))       (CategoryTheory.Limit
s.initial.to         ((CategoryTheory.Limits.pair X Y).obj { as := CategoryTheor
y.Limits.WalkingPair.right }))       c.inl c.inr
参数：CategoryTheory.Limits.initial.to         ((CategoryTheory.Limits.pair X Y).ob
j { as := CategoryTheory.Limits.WalkingPair.left })；CategoryTheory.Limits.initia
l.to         ((CategoryTheory.Limits.pair X Y).obj { as := CategoryTheory.Limits
.WalkingPair.right })。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
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
· 使用定理 `CategoryTheory.Limits.initial.to_comp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasInitial C] {P Q : 
C}   (f : P ⟶ Q),   Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_discrete`：∀ {C : Type u_3} {ι : T
ype u_5} [inst : CategoryTheory.Category.{v_2, u_3} C]   {F G : CategoryTheory.F
unctor (CategoryTheory.Discrete ι) C}…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.BinaryCofan.isColimit_iff_isIso_inr`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (h : CategoryTheory.Limits
.IsInitial X)   (c : CategoryTheory.Limits.Bina…
-/
theorem BinaryCofan.isPullback_initial_to_of_isVanKampen [HasInitial C] {c : BinaryCofan X Y}
    (h : IsVanKampenColimit c) : IsPullback (initial.to _) (initial.to _) c.inl c.inr := by
  refine ((h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr ?_
      (.of_discrete _)).mp ⟨?_⟩ ⟨WalkingPair.left⟩).flip
  · ext ⟨⟨⟩⟩ <;> simp
  · exact ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some

end BinaryCoproduct

section FiniteCoproducts

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.isUniversalColimit_extendCofan** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory`。
形式化陈述：isUniversalColimit_extendCofan {n : Nat} (f : Fin (n + 1) -> C) {c₁ : Cofa
n fun i : Fin n => f i.succ} {c₂ : BinaryCofan (f 0) c₁.pt} (t₁ : IsUniversalCol
imit c₁) (t₂ : IsUniversalColimit c₂) [forall {Z} (i : Z ⟶ c₂.pt), HasPullback c
₂.inr i] : IsUniversalColimit (extendCofan c₁ c₂)
参数：f : Fin (n + 1) -> C；f 0；t₁ : IsUniversalColimit c₁；t₂ : IsUniversalColimit c
₂；i : Z ⟶ c₂.pt。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_discrete`：∀ {C : Type u_3} {ι : T
ype u_5} [inst : CategoryTheory.Category.{v_2, u_3} C]   {F G : CategoryTheory.F
unctor (CategoryTheory.Discrete ι) C}…
· 使用定理 `CategoryTheory.IsPullback.of_right`：of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : 
C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ 
: X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ …
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isUniversalColimit_extendCofan {n : ℕ} (f : Fin (n + 1) → C)
    {c₁ : Cofan fun i : Fin n ↦ f i.succ} {c₂ : BinaryCofan (f 0) c₁.pt}
    (t₁ : IsUniversalColimit c₁) (t₂ : IsUniversalColimit c₂)
    [∀ {Z} (i : Z ⟶ c₂.pt), HasPullback c₂.inr i] :
    IsUniversalColimit (extendCofan c₁ c₂) := by
  intro F c α i e hα H
  let F' : Fin (n + 1) → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor F' := by
    apply Functor.hext
    · exact fun i ↦ rfl
    · rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
      simp [F']
  have t₁' := @t₁ (Discrete.functor (fun j ↦ F.obj ⟨j.succ⟩))
    (Cofan.mk (pullback c₂.inr i) fun j ↦ pullback.lift (α.app _ ≫ c₁.inj _) (c.ι.app _) ?_)
    (Discrete.natTrans fun i ↦ α.app _) (pullback.fst _ _) ?_ (.of_discrete _) ?_
  rotate_left
  · simpa only [Functor.const_obj_obj, pair_obj_right, Discrete.functor_obj, Category.assoc,
      extendCofan_pt, Functor.const_obj_obj, NatTrans.comp_app, extendCofan_ι_app,
      Fin.cases_succ, Functor.const_map_app] using! congr_app e ⟨j.succ⟩
  · ext j
    dsimp
    simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Cofan.inj]
  · intro j
    simp only [pair_obj_right, Functor.const_obj_obj, Discrete.functor_obj,
      Cofan.mk_pt, Cofan.mk_ι_app, Discrete.natTrans_app]
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback (BinaryCofan.inr c₂) i).flip
    · simp only [Functor.const_obj_obj, pair_obj_right, limit.lift_π,
        PullbackCone.mk_pt, PullbackCone.mk_π_app]
      exact H _
    · simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Cofan.inj]
  obtain ⟨H₁⟩ := t₁'
  have t₂' := @t₂ (pair (F.obj ⟨0⟩) (pullback c₂.inr i))
    (BinaryCofan.mk (c.ι.app ⟨0⟩) (pullback.snd _ _)) (mapPair (α.app _) (pullback.fst _ _)) i ?_
    (.of_discrete _) ?_
  rotate_left
  · ext ⟨⟨⟩⟩
    · simpa [mapPair] using! congr_app e ⟨0⟩
    · simpa using! pullback.condition
  · rintro ⟨⟨⟩⟩
    · simp only [pair_obj_right, Functor.const_obj_obj, pair_obj_left, BinaryCofan.mk_pt,
        BinaryCofan.ι_app_left, BinaryCofan.mk_inl, mapPair_left]
      exact H ⟨0⟩
    · simp only [pair_obj_right, Functor.const_obj_obj, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
        BinaryCofan.mk_inr, mapPair_right]
      exact (IsPullback.of_hasPullback (BinaryCofan.inr c₂) i).flip
  obtain ⟨H₂⟩ := t₂'
  clear_value F'
  subst this
  refine ⟨IsColimit.ofIsoColimit (extendCofanIsColimit
    (fun i ↦ (Discrete.functor F').obj ⟨i⟩) H₁ H₂) <| Cocone.ext (Iso.refl _) ?_⟩
  dsimp
  rintro ⟨j⟩
  simp only [limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app, Category.comp_id]
  induction j using Fin.inductionOn
  · simp only [Fin.cases_zero]
  · simp only [Fin.cases_succ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.isVanKampenColimit_extendCofan** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory`。
形式化陈述：isVanKampenColimit_extendCofan {n : Nat} (f : Fin (n + 1) -> C) {c₁ : Cofa
n fun i : Fin n => f i.succ} {c₂ : BinaryCofan (f 0) c₁.pt} (t₁ : IsVanKampenCol
imit c₁) (t₂ : IsVanKampenColimit c₂) [forall {Z} (i : Z ⟶ c₂.pt), HasPullback c
₂.inr i] [HasFiniteCoproducts C] : IsVanKampenColimit (extendCofan c₁ c₂)
参数：f : Fin (n + 1) -> C；f 0；t₁ : IsVanKampenColimit c₁；t₂ : IsVanKampenColimit c
₂；i : Z ⟶ c₂.pt。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_discrete`：∀ {C : Type u_3} {ι : T
ype u_5} [inst : CategoryTheory.Category.{v_2, u_3} C]   {F G : CategoryTheory.F
unctor (CategoryTheory.Discrete ι) C}…
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsColimit.uniq`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u
₃} C]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.IsPullback.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ 
X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
 {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…
· 使用定理 `CategoryTheory.isUniversalColimit_extendCofan`：isUniversalColimit_extend
Cofan {n : Nat} (f : Fin (n + 1) -> C) {c₁ : Cofan fun i : Fin n => f i.succ} {c
₂ : BinaryCofan (f 0) c₁.pt} (t₁ : …
· 使用定理 `CategoryTheory.IsVanKampenColimit.isUniversal`：∀ {J : Type v'} [inst : C
ategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Categor
y.{v, u} C]   {F : CategoryTheory.F…
-/
theorem isVanKampenColimit_extendCofan {n : ℕ} (f : Fin (n + 1) → C)
    {c₁ : Cofan fun i : Fin n ↦ f i.succ} {c₂ : BinaryCofan (f 0) c₁.pt}
    (t₁ : IsVanKampenColimit c₁) (t₂ : IsVanKampenColimit c₂)
    [∀ {Z} (i : Z ⟶ c₂.pt), HasPullback c₂.inr i]
    [HasFiniteCoproducts C] :
    IsVanKampenColimit (extendCofan c₁ c₂) := by
  intro F c α i e hα
  refine ⟨?_, isUniversalColimit_extendCofan f t₁.isUniversal t₂.isUniversal c α i e hα⟩
  intro ⟨Hc⟩ ⟨j⟩
  have t₂' := (@t₂ (pair (F.obj ⟨0⟩) (∐ fun (j : Fin n) ↦ F.obj ⟨j.succ⟩))
    (BinaryCofan.mk (P := c.pt) (c.ι.app _) (Sigma.desc fun b ↦ c.ι.app _))
    (mapPair (α.app _) (Sigma.desc fun b ↦ α.app _ ≫ c₁.inj _)) i ?_ (.of_discrete _)).mp ⟨?_⟩
  rotate_left
  · ext ⟨⟨⟩⟩
    · simpa only [pair_obj_left, Functor.const_obj_obj, pair_obj_right, Discrete.functor_obj,
        NatTrans.comp_app, mapPair_left, BinaryCofan.ι_app_left, BinaryCofan.mk_pt,
        BinaryCofan.mk_inl, Functor.const_map_app, extendCofan_pt,
        extendCofan_ι_app, Fin.cases_zero] using! congr_app e ⟨0⟩
    · dsimp
      ext j
      simpa only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app,
        Category.assoc, extendCofan_pt, Functor.const_obj_obj, NatTrans.comp_app, extendCofan_ι_app,
        Fin.cases_succ, Functor.const_map_app] using! congr_app e ⟨j.succ⟩
  · let F' : Fin (n + 1) → C := F.obj ∘ Discrete.mk
    have : F = Discrete.functor F' := by
      apply Functor.hext
      · exact fun i ↦ rfl
      · rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
        simp [F']
    clear_value F'
    subst this
    apply BinaryCofan.IsColimit.mk _ (fun {T} f₁ f₂ ↦ Hc.desc (Cofan.mk T (Fin.cases f₁
      (fun i ↦ Sigma.ι (fun (j : Fin n) ↦ (Discrete.functor F').obj ⟨j.succ⟩) _ ≫ f₂))))
    · intro T f₁ f₂
      simp only [Discrete.functor_obj, pair_obj_left, BinaryCofan.mk_pt, Functor.const_obj_obj,
        BinaryCofan.mk_inl, IsColimit.fac, Cofan.mk_pt, Cofan.mk_ι_app,
        Fin.cases_zero]
    · intro T f₁ f₂
      simp only [Discrete.functor_obj, pair_obj_right, BinaryCofan.mk_pt, Functor.const_obj_obj,
        BinaryCofan.mk_inr]
      ext j
      simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt,
        Cofan.mk_ι_app, IsColimit.fac, Fin.cases_succ]
    · intro T f₁ f₂ f₃ m₁ m₂
      simp only [Discrete.functor_obj_eq_as, pair_obj_left, BinaryCofan.mk_pt, const_obj_obj,
        BinaryCofan.mk_inl, pair_obj_right, BinaryCofan.mk_inr] at m₁ m₂ ⊢
      refine Hc.uniq (Cofan.mk T (Fin.cases f₁
        (fun i ↦ Sigma.ι (fun (j : Fin n) ↦ (Discrete.functor F').obj ⟨j.succ⟩) _ ≫ f₂))) _ ?_
      intro ⟨j⟩
      simp only [Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app]
      induction j using Fin.inductionOn
      · simp only [Fin.cases_zero, m₁]
      · simp only [← m₂, colimit.ι_desc_assoc, Discrete.functor_obj,
          Cofan.mk_pt, Cofan.mk_ι_app, Fin.cases_succ]
  induction j using Fin.inductionOn with
  | zero => exact t₂' ⟨WalkingPair.left⟩
  | succ j _ =>
    have t₁' := (@t₁ (Discrete.functor (fun j ↦ F.obj ⟨j.succ⟩)) (Cofan.mk _ _) (Discrete.natTrans
      fun i ↦ α.app _) (Sigma.desc (fun j ↦ α.app _ ≫ c₁.inj _)) ?_
      (.of_discrete _)).mp ⟨coproductIsCoproduct _⟩ ⟨j⟩
    rotate_left
    · ext ⟨j⟩
      dsimp
      rw [colimit.ι_desc]
      rfl
    simpa [Functor.const_obj_obj, Discrete.functor_obj, extendCofan_pt, extendCofan_ι_app,
      Fin.cases_succ, BinaryCofan.mk_pt, colimit.cocone_x, Cofan.mk_pt, Cofan.mk_ι_app,
      BinaryCofan.ι_app_right, BinaryCofan.mk_inr, colimit.ι_desc,
      Discrete.natTrans_app] using! t₁'.paste_horiz (t₂' ⟨WalkingPair.right⟩)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.isPullback_of_cofan_isVanKampen** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory`。
形式化陈述：isPullback_of_cofan_isVanKampen [HasInitial C] {ι : Type*} {X : ι -> C} {c
 : Cofan X} (hc : IsVanKampenColimit c) (i j : ι) [DecidableEq ι] : IsPullback (
P
参数：hc : IsVanKampenColimit c；i j : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.initial.to_comp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasInitial C] {P Q : 
C}   (f : P ⟶ Q),   Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_discrete`：∀ {C : Type u_3} {ι : T
ype u_5} [inst : CategoryTheory.Category.{v_2, u_3} C]   {F G : CategoryTheory.F
unctor (CategoryTheory.Discrete ι) C}…
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用定理 `CategoryTheory.IsIso.eq_inv_comp`：eq_inv_comp (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
theorem isPullback_of_cofan_isVanKampen [HasInitial C] {ι : Type*} {X : ι → C}
    {c : Cofan X} (hc : IsVanKampenColimit c) (i j : ι) [DecidableEq ι] :
    IsPullback (P := (if j = i then X i else ⊥_ C))
      (if h : j = i then eqToHom (if_pos h) else eqToHom (if_neg h) ≫ initial.to (X i))
      (if h : j = i then eqToHom ((if_pos h).trans (congr_arg X h.symm))
        else eqToHom (if_neg h) ≫ initial.to (X j))
      (Cofan.inj c i) (Cofan.inj c j) := by
  refine (hc (Cofan.mk (X i) (f := fun k ↦ if k = i then X i else ⊥_ C)
    (fun k ↦ if h : k = i then (eqToHom <| if_pos h) else (eqToHom <| if_neg h) ≫ initial.to _))
    (Discrete.natTrans (fun k ↦ if h : k.1 = i then (eqToHom <| (if_pos h).trans
      (congr_arg X h.symm)) else (eqToHom <| if_neg h) ≫ initial.to _))
    (c.inj i) ?_ (.of_discrete _)).mp ⟨?_⟩ ⟨j⟩
  · ext ⟨k⟩
    simp only [Discrete.functor_obj, Functor.const_obj_obj, NatTrans.comp_app,
      Discrete.natTrans_app, Cofan.mk_pt, Cofan.mk_ι_app, Functor.const_map_app]
    split
    · subst ‹k = i›; rfl
    · simp
  · refine Cofan.IsColimit.mk _ (fun t ↦ (eqToHom (if_pos rfl).symm) ≫ t.inj i) ?_ ?_
    · intro t j
      simp only [Cofan.mk_pt, cofan_mk_inj]
      split
      · subst ‹j = i›; simp
      · rw [Category.assoc, ← IsIso.eq_inv_comp]
        exact initialIsInitial.hom_ext _ _
    · intro t m hm
      simp [← hm i]
/-
**CategoryTheory.isPullback_initial_to_of_cofan_isVanKampen** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory`。
形式化陈述：isPullback_initial_to_of_cofan_isVanKampen [HasInitial C] {ι : Type*} {F :
 Discrete ι ⥤ C} {c : Cocone F} (hc : IsVanKampenColimit c) (i j : Discrete ι) (
hi : i != j) : IsPullback (initial.to _) (initial.to _) (c.ι.app i) (c.ι.app j)
参数：hc : IsVanKampenColimit c；i j : Discrete ι；hi : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `CategoryTheory.Discrete.ext`：∀ {α : Type u₁} {x y : CategoryTheory.Discr
ete α}, x.as = y.as → x = y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Lean.Meta.FastSubsingleton.helim`：∀ {α β : Sort u} [Meta.FastSubsingleto
n α], α = β → ∀ (a : α) (b : β), a ≍ b
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.isPullback_of_cofan_isVanKampen`：isPullback_of_cofan_isVa
nKampen [HasInitial C] {ι : Type*} {X : ι -> C} {c : Cofan X} (hc : IsVanKampenC
olimit c) (i j : ι) [DecidableEq ι] …
-/
theorem isPullback_initial_to_of_cofan_isVanKampen [HasInitial C] {ι : Type*} {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsVanKampenColimit c) (i j : Discrete ι) (hi : i ≠ j) :
    IsPullback (initial.to _) (initial.to _) (c.ι.app i) (c.ι.app j) := by
  classical
  let f : ι → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  have : ∀ i, Subsingleton (⊥_ C ⟶ (Discrete.functor f).obj i) := inferInstance
  convert! isPullback_of_cofan_isVanKampen hc i.as j.as
  exact (if_neg (mt Discrete.ext hi.symm)).symm

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.mono_of_cofan_isVanKampen** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：mono_of_cofan_isVanKampen [HasInitial C] {ι : Type*} {F : Discrete ι ⥤ C} 
{c : Cocone F} (hc : IsVanKampenColimit c) (i : Discrete ι) : Mono (c.ι.app i)
参数：hc : IsVanKampenColimit c；i : Discrete ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.PullbackCone.mono_of_isLimitMkIdId`：mono_of_isLimi
tMkIdId (f : X ⟶ Y) (t : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f)) : Mono
 f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso`：of_vert_isIso [IsIso snd] [IsIs
o f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.isPullback_of_cofan_isVanKampen`：isPullback_of_cofan_isVa
nKampen [HasInitial C] {ι : Type*} {X : ι -> C} {c : Cofan X} (hc : IsVanKampenC
olimit c) (i j : ι) [DecidableEq ι] …
-/
theorem mono_of_cofan_isVanKampen [HasInitial C] {ι : Type*} {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsVanKampenColimit c) (i : Discrete ι) : Mono (c.ι.app i) := by
  classical
  let f : ι → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  refine PullbackCone.mono_of_isLimitMkIdId _ (IsPullback.isLimit ?_)
  nth_rw 1 [← Category.id_comp (c.ι.app i)]
  convert! IsPullback.paste_vert _ (isPullback_of_cofan_isVanKampen hc i.as i.as)
  swap
  · exact (eqToHom (if_pos rfl).symm)
  · simp
  · exact IsPullback.of_vert_isIso ⟨by simp⟩

end FiniteCoproducts

section CoproductsPullback

variable {ι ι' : Type*} {S : C}
variable {B : C} {X : ι → C} {a : Cofan X} (hau : IsUniversalColimit a) (f : ∀ i, X i ⟶ S)
  (u : a.pt ⟶ S) (v : B ⟶ S)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
include hau in
/-- Pullbacks distribute over universal coproducts on the left: This is the isomorphism
`∐ (B ×[S] Xᵢ) ≅ B ×[S] (∐ Xᵢ)`. -/
/-
**CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_pullbackCone_left** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsUniversalColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {S
 B : C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   CategoryTheory.IsUn
iversalColimit a →     ∀ (f : (i : ι) → X i ⟶ S) (u : a.pt ⟶ S) (v : B ⟶ S) (s :
 (i : ι) → CategoryTheory.Limits.PullbackCone v (f i))       (hs : (i : ι) → Cat
egoryTheory.Limits.IsLimit (s i)) (t : CategoryTheory.Limits.PullbackCone v u)  
     (ht : CategoryTheory.Limits.IsLimit t) (d : CategoryTheory.Limits.Cofan fun
 i => (s i).pt) (e : d.pt ≅ t.pt),       autoParam (∀ (i : ι), CategoryTheory.Ca
tegoryStruct.comp (a.inj i) u = f i)           CategoryTheory.IsUniversalColimit
.nonempty_isColimit_of_pullbackCone_left._auto_1 →         autoParam            
 (∀ (i : ι),               CategoryTheory.CategoryStruct.comp (d.inj i) (Categor
yTheory.CategoryStruct.comp e.hom t.fst) = (s i).fst)             CategoryTheory
.IsUniversalColimit.nonempty_isColimit_of_pullbackCone_left._auto_3 →           
autoParam               (∀ (i : ι),                 CategoryTheory.CategoryStruc
t.comp (d.inj i) (CategoryTheory.CategoryStruct.comp e.hom t.snd) =             
      CategoryTheory.CategoryStruct.comp (s i).snd (a.inj i))               Cate
goryTheory.IsUniversalColimit.nonempty_isColimit_of_pullbackCone_left._auto_5 → 
            Nonempty (CategoryTheory.Limits.IsColimit d)
参数：f : (i : ι) → X i ⟶ S；u : a.pt ⟶ S；v : B ⟶ S；s : (i : ι) → CategoryTheory.Lim
its.PullbackCone v (f i)；hs : (i : ι) → CategoryTheory.Limits.IsLimit (s i)；t : 
CategoryTheory.Limits.PullbackCone v u；ht : CategoryTheory.Limits.IsLimit t；d : 
CategoryTheory.Limits.Cofan fun i => (s i).pt；e : d.pt ≅ t.pt；∀ (i : ι), Categor
yTheory.CategoryStruct.comp (a.inj i) u = f i；∀ (i : ι),               CategoryT
heory.CategoryStruct.comp (d.inj i) (CategoryTheory.CategoryStruct.comp e.hom t.
fst) = (s i).fst；∀ (i : ι),                 CategoryTheory.CategoryStruct.comp (
d.inj i) (CategoryTheory.CategoryStruct.comp e.hom t.snd) =                   Ca
tegoryTheory.CategoryStruct.comp (s i).snd (a.inj i)；CategoryTheory.Limits.IsCol
imit d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t : 
CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_snd`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_discrete`：∀ {C : Type u_3} {ι : T
ype u_5} [inst : CategoryTheory.Category.{v_2, u_3} C]   {F G : CategoryTheory.F
unctor (CategoryTheory.Discrete ι) C}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cofan.inj.eq_1`：∀ {β : Type w} {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {f : β → C} (p : CategoryTheory.Limits.Cofan
 f)   (j : β), p.inj j = p…
· 使用定理 `CategoryTheory.IsPullback.of_right`：of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : 
C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ 
: X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsPullback.of_isLimit`：of_isLimit {c : PullbackCone f g} 
(h : Limits.IsLimit c) : IsPullback c.fst c.snd f g

--- 原说明 ---
Pullbacks distribute over universal coproducts on the left: This is the isomorph
ism
`∐ (B ×[S] Xᵢ) ≅ B ×[S] (∐ Xᵢ)`.
-/
lemma IsUniversalColimit.nonempty_isColimit_of_pullbackCone_left
    (s : ∀ i, PullbackCone v (f i)) (hs : ∀ i, IsLimit (s i))
    (t : PullbackCone v u) (ht : IsLimit t) (d : Cofan (fun i : ι ↦ (s i).pt)) (e : d.pt ≅ t.pt)
    (hu : ∀ i, a.inj i ≫ u = f i := by cat_disch)
    (he₁ : ∀ i, d.inj i ≫ e.hom ≫ t.fst = (s i).fst := by cat_disch)
    (he₂ : ∀ i, d.inj i ≫ e.hom ≫ t.snd = (s i).snd ≫ a.inj i := by cat_disch) :
    Nonempty (IsColimit d) := by
  let iso : d ≅ (Cofan.mk _ fun i : ι ↦ PullbackCone.IsLimit.lift ht
      (s i).fst ((s i).snd ≫ a.inj i) (by simp [hu, (s i).condition])) :=
    Cofan.ext e <| fun p ↦ PullbackCone.IsLimit.hom_ext ht (by simp [he₁]) (by simp [he₂])
  rw [(IsColimit.equivIsoColimit iso).nonempty_congr]
  refine hau _ (Discrete.natTrans fun i ↦ (s i.as).snd) t.snd ?_ (.of_discrete _) fun j ↦ ?_
  · ext; simp [Cofan.inj]
  · simp only [Discrete.functor_obj_eq_as, Cofan.mk_pt, Functor.const_obj_obj, Cofan.mk_ι_app,
      Discrete.natTrans_app]
    rw [← Cofan.inj]
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_isLimit ht)
    simpa [hu] using (IsPullback.of_isLimit (hs j.1))

section

variable {P : ι → C} (q₁ : ∀ i, P i ⟶ B) (q₂ : ∀ i, P i ⟶ X i)
  (hP : ∀ i, IsPullback (q₁ i) (q₂ i) v (f i))

include hau hP in
/-- Pullbacks distribute over universal coproducts on the left: This is the isomorphism
`∐ (B ×[S] Xᵢ) ≅ B ×[S] (∐ Xᵢ)`. -/
/-
**CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_isPullback_left** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.IsUniversalColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {S
 B : C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   CategoryTheory.IsUn
iversalColimit a →     ∀ (f : (i : ι) → X i ⟶ S) (u : a.pt ⟶ S) (v : B ⟶ S) {P :
 ι → C} (q₁ : (i : ι) → P i ⟶ B)       (q₂ : (i : ι) → P i ⟶ X i),       (∀ (i :
 ι), CategoryTheory.IsPullback (q₁ i) (q₂ i) v (f i)) →         ∀ {Z : C} {p₁ : 
Z ⟶ B} {p₂ : Z ⟶ a.pt},           CategoryTheory.IsPullback p₁ p₂ v u →         
    ∀ (d : CategoryTheory.Limits.Cofan P) (e : d.pt ≅ Z),               autoPara
m (∀ (i : ι), CategoryTheory.CategoryStruct.comp (a.inj i) u = f i)             
      CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_isPullback_left._a
uto_1 →                 autoParam                     (∀ (i : ι),               
        CategoryTheory.CategoryStruct.comp (d.inj i) (CategoryTheory.CategoryStr
uct.comp e.hom p₁) = q₁ i)                     CategoryTheory.IsUniversalColimit
.nonempty_isColimit_of_isPullback_left._auto_3 →                   autoParam    
                   (∀ (i : ι),                         CategoryTheory.CategorySt
ruct.comp (d.inj i) (CategoryTheory.CategoryStruct.comp e.hom p₂) =             
              CategoryTheory.CategoryStruct.comp (q₂ i) (a.inj i))              
         CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_isPullback_left
._auto_5 →                     Nonempty (CategoryTheory.Limits.IsColimit d)
参数：f : (i : ι) → X i ⟶ S；u : a.pt ⟶ S；v : B ⟶ S；q₁ : (i : ι) → P i ⟶ B；q₂ : (i :
 ι) → P i ⟶ X i；∀ (i : ι), CategoryTheory.IsPullback (q₁ i) (q₂ i) v (f i)；d : C
ategoryTheory.Limits.Cofan P；e : d.pt ≅ Z；∀ (i : ι), CategoryTheory.CategoryStru
ct.comp (a.inj i) u = f i；∀ (i : ι),                       CategoryTheory.Catego
ryStruct.comp (d.inj i) (CategoryTheory.CategoryStruct.comp e.hom p₁) = q₁ i；∀ (
i : ι),                         CategoryTheory.CategoryStruct.comp (d.inj i) (Ca
tegoryTheory.CategoryStruct.comp e.hom p₂) =                           CategoryT
heory.CategoryStruct.comp (q₂ i) (a.inj i)；CategoryTheory.Limits.IsColimit d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_pullbackCone_lef
t`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {S B 
: C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   Categ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Pullbacks distribute over universal coproducts on the left: This is the isomorph
ism
`∐ (B ×[S] Xᵢ) ≅ B ×[S] (∐ Xᵢ)`.
-/
lemma IsUniversalColimit.nonempty_isColimit_of_isPullback_left
    {Z : C} {p₁ : Z ⟶ B} {p₂ : Z ⟶ a.pt} (h : IsPullback p₁ p₂ v u)
    (d : Cofan P) (e : d.pt ≅ Z)
    (hu : ∀ i, a.inj i ≫ u = f i := by cat_disch)
    (he₁ : ∀ i, d.inj i ≫ e.hom ≫ p₁ = q₁ i := by cat_disch)
    (he₂ : ∀ i, d.inj i ≫ e.hom ≫ p₂ = q₂ i ≫ a.inj i := by cat_disch) :
    Nonempty (IsColimit d) :=
  hau.nonempty_isColimit_of_pullbackCone_left f u v (fun i ↦ (hP i).cone)
    (fun i ↦ (hP i).isLimit) h.cone h.isLimit d e

set_option backward.isDefEq.respectTransparency false in
include hau hP in
/-- Pullbacks distribute over universal coproducts on the left: This is the isomorphism
`∐ (B ×[S] Xᵢ) ≅ B ×[S] (∐ Xᵢ)`. -/
/-
**CategoryTheory.IsUniversalColimit.isPullback_of_isColimit_left** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.IsUniversalColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {S
 B : C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   CategoryTheory.IsUn
iversalColimit a →     ∀ (f : (i : ι) → X i ⟶ S) (u : a.pt ⟶ S) (v : B ⟶ S) {P :
 ι → C} (q₁ : (i : ι) → P i ⟶ B)       (q₂ : (i : ι) → P i ⟶ X i),       (∀ (i :
 ι), CategoryTheory.IsPullback (q₁ i) (q₂ i) v (f i)) →         ∀ {d : CategoryT
heory.Limits.Cofan P} (hd : CategoryTheory.Limits.IsColimit d),           autoPa
ram (∀ (i : ι), CategoryTheory.CategoryStruct.comp (a.inj i) u = f i)           
    CategoryTheory.IsUniversalColimit.isPullback_of_isColimit_left._auto_1 →    
         ∀ [CategoryTheory.Limits.HasPullback v u],               CategoryTheory
.IsPullback (CategoryTheory.Limits.Cofan.IsColimit.desc hd q₁)                 (
CategoryTheory.Limits.Cofan.IsColimit.desc hd fun x =>                   Categor
yTheory.CategoryStruct.comp (q₂ x) (a.inj x))                 v u
参数：f : (i : ι) → X i ⟶ S；u : a.pt ⟶ S；v : B ⟶ S；q₁ : (i : ι) → P i ⟶ B；q₂ : (i :
 ι) → P i ⟶ X i；∀ (i : ι), CategoryTheory.IsPullback (q₁ i) (q₂ i) v (f i)；hd : 
CategoryTheory.Limits.IsColimit d；∀ (i : ι), CategoryTheory.CategoryStruct.comp 
(a.inj i) u = f i；CategoryTheory.Limits.Cofan.IsColimit.desc hd q₁；CategoryTheor
y.Limits.Cofan.IsColimit.desc hd fun x =>                   CategoryTheory.Categ
oryStruct.comp (q₂ x) (a.inj x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_isPullback_left`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {S B : 
C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   Categ…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用引理 `CategoryTheory.IsPullback.of_iso`：of_iso (h : IsPullback fst snd f g) {P
' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} 
(e₁ : P ≅ P') (e₂ : X …
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheo…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso_hom_desc`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…

--- 原说明 ---
Pullbacks distribute over universal coproducts on the left: This is the isomorph
ism
`∐ (B ×[S] Xᵢ) ≅ B ×[S] (∐ Xᵢ)`.
-/
lemma IsUniversalColimit.isPullback_of_isColimit_left {d : Cofan P} (hd : IsColimit d)
    (hu : ∀ i, a.inj i ≫ u = f i := by cat_disch)
    [HasPullback v u] :
    IsPullback (Cofan.IsColimit.desc hd q₁) (Cofan.IsColimit.desc hd (q₂ · ≫ a.inj _))
      v u := by
  let c : Cofan P := Cofan.mk (pullback v u)
    fun i ↦ pullback.lift (q₁ i) (q₂ i ≫ a.inj i) (by simp [(hP i).w, hu])
  obtain ⟨hc⟩ := hau.nonempty_isColimit_of_isPullback_left f u
    v q₁ q₂ hP (IsPullback.of_hasPullback _ _) c (Iso.refl _)
  refine (IsPullback.of_hasPullback v u).of_iso
      ?_ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact hc.coconePointUniqueUpToIso hd
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_fst _ _ _
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_snd _ _ _

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
include hau in
/-- Pullbacks distribute over universal coproducts on the right: This is the isomorphism
`∐ (Xᵢ ×[S] B) ≅ (∐ Xᵢ) ×[S] B`. -/
/-
**CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_pullbackCone_right** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsUniversalColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {S
 B : C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   CategoryTheory.IsUn
iversalColimit a →     ∀ (f : (i : ι) → X i ⟶ S) (u : a.pt ⟶ S) (v : B ⟶ S) (s :
 (i : ι) → CategoryTheory.Limits.PullbackCone (f i) v)       (hs : (i : ι) → Cat
egoryTheory.Limits.IsLimit (s i)) (t : CategoryTheory.Limits.PullbackCone u v)  
     (ht : CategoryTheory.Limits.IsLimit t) (d : CategoryTheory.Limits.Cofan fun
 i => (s i).pt) (e : d.pt ≅ t.pt),       autoParam (∀ (i : ι), CategoryTheory.Ca
tegoryStruct.comp (a.inj i) u = f i)           CategoryTheory.IsUniversalColimit
.nonempty_isColimit_of_pullbackCone_right._auto_1 →         autoParam           
  (∀ (i : ι),               CategoryTheory.CategoryStruct.comp (d.inj i) (Catego
ryTheory.CategoryStruct.comp e.hom t.fst) =                 CategoryTheory.Categ
oryStruct.comp (s i).fst (a.inj i))             CategoryTheory.IsUniversalColimi
t.nonempty_isColimit_of_pullbackCone_right._auto_3 →           autoParam        
       (∀ (i : ι),                 CategoryTheory.CategoryStruct.comp (d.inj i) 
(CategoryTheory.CategoryStruct.comp e.hom t.snd) =                   (s i).snd) 
              CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_pullbackCo
ne_right._auto_5 →             Nonempty (CategoryTheory.Limits.IsColimit d)
参数：f : (i : ι) → X i ⟶ S；u : a.pt ⟶ S；v : B ⟶ S；s : (i : ι) → CategoryTheory.Lim
its.PullbackCone (f i) v；hs : (i : ι) → CategoryTheory.Limits.IsLimit (s i)；t : 
CategoryTheory.Limits.PullbackCone u v；ht : CategoryTheory.Limits.IsLimit t；d : 
CategoryTheory.Limits.Cofan fun i => (s i).pt；e : d.pt ≅ t.pt；∀ (i : ι), Categor
yTheory.CategoryStruct.comp (a.inj i) u = f i；∀ (i : ι),               CategoryT
heory.CategoryStruct.comp (d.inj i) (CategoryTheory.CategoryStruct.comp e.hom t.
fst) =                 CategoryTheory.CategoryStruct.comp (s i).fst (a.inj i)；∀ 
(i : ι),                 CategoryTheory.CategoryStruct.comp (d.inj i) (CategoryT
heory.CategoryStruct.comp e.hom t.snd) =                   (s i).snd；CategoryThe
ory.Limits.IsColimit d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t : 
CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_snd`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.NatTrans.Equifibered.of_discrete`：∀ {C : Type u_3} {ι : T
ype u_5} [inst : CategoryTheory.Category.{v_2, u_3} C]   {F G : CategoryTheory.F
unctor (CategoryTheory.Discrete ι) C}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cofan.inj.eq_1`：∀ {β : Type w} {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {f : β → C} (p : CategoryTheory.Limits.Cofan
 f)   (j : β), p.inj j = p…
· 使用定理 `CategoryTheory.IsPullback.of_right`：of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : 
C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ 
: X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ …
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_isLimit`：of_isLimit {c : PullbackCone f g} 
(h : Limits.IsLimit c) : IsPullback c.fst c.snd f g

--- 原说明 ---
Pullbacks distribute over universal coproducts on the right: This is the isomorp
hism
`∐ (Xᵢ ×[S] B) ≅ (∐ Xᵢ) ×[S] B`.
-/
lemma IsUniversalColimit.nonempty_isColimit_of_pullbackCone_right
    (s : ∀ i, PullbackCone (f i) v) (hs : ∀ i, IsLimit (s i))
    (t : PullbackCone u v) (ht : IsLimit t) (d : Cofan (fun i : ι ↦ (s i).pt)) (e : d.pt ≅ t.pt)
    (hu : ∀ i, a.inj i ≫ u = f i := by cat_disch)
    (he₁ : ∀ i, d.inj i ≫ e.hom ≫ t.fst = (s i).fst ≫ a.inj i := by cat_disch)
    (he₂ : ∀ i, d.inj i ≫ e.hom ≫ t.snd = (s i).snd := by cat_disch) :
    Nonempty (IsColimit d) := by
  let iso : d ≅ (Cofan.mk _ fun i : ι ↦ PullbackCone.IsLimit.lift ht
      ((s i).fst ≫ a.inj i) ((s i).snd) (by simp [hu, (s i).condition])) :=
    Cofan.ext e <| fun p ↦ PullbackCone.IsLimit.hom_ext ht (by simp [he₁]) (by simp [he₂])
  rw [(IsColimit.equivIsoColimit iso).nonempty_congr]
  refine hau _ (Discrete.natTrans fun i ↦ (s i.as).fst) t.fst ?_ (.of_discrete _) fun j ↦ ?_
  · ext; simp [Cofan.inj]
  · simp only [Discrete.functor_obj_eq_as, Cofan.mk_pt, Functor.const_obj_obj, Cofan.mk_ι_app,
      Discrete.natTrans_app]
    rw [← Cofan.inj]
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_isLimit ht).flip
    simpa [hu] using (IsPullback.of_isLimit (hs j.1)).flip

section

variable {P : ι → C} (q₁ : ∀ i, P i ⟶ X i) (q₂ : ∀ i, P i ⟶ B)
  (hP : ∀ i, IsPullback (q₁ i) (q₂ i) (f i) v)

include hau hP in
/-- Pullbacks distribute over universal coproducts on the right: This is the isomorphism
`∐ (Xᵢ ×[S] B) ≅ (∐ Xᵢ) ×[S] B`. -/
/-
**CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_isPullback_right** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.IsUniversalColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {S
 B : C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   CategoryTheory.IsUn
iversalColimit a →     ∀ (f : (i : ι) → X i ⟶ S) (u : a.pt ⟶ S) (v : B ⟶ S) {P :
 ι → C} (q₁ : (i : ι) → P i ⟶ X i)       (q₂ : (i : ι) → P i ⟶ B),       (∀ (i :
 ι), CategoryTheory.IsPullback (q₁ i) (q₂ i) (f i) v) →         ∀ {Z : C} {p₁ : 
Z ⟶ a.pt} {p₂ : Z ⟶ B},           CategoryTheory.IsPullback p₁ p₂ u v →         
    ∀ (d : CategoryTheory.Limits.Cofan P) (e : d.pt ≅ Z),               autoPara
m (∀ (i : ι), CategoryTheory.CategoryStruct.comp (a.inj i) u = f i)             
      CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_isPullback_right._
auto_1 →                 autoParam                     (∀ (i : ι),              
         CategoryTheory.CategoryStruct.comp (d.inj i) (CategoryTheory.CategorySt
ruct.comp e.hom p₁) =                         CategoryTheory.CategoryStruct.comp
 (q₁ i) (a.inj i))                     CategoryTheory.IsUniversalColimit.nonempt
y_isColimit_of_isPullback_right._auto_3 →                   autoParam           
            (∀ (i : ι),                         CategoryTheory.CategoryStruct.co
mp (d.inj i) (CategoryTheory.CategoryStruct.comp e.hom p₂) =                    
       q₂ i)                       CategoryTheory.IsUniversalColimit.nonempty_is
Colimit_of_isPullback_right._auto_5 →                     Nonempty (CategoryTheo
ry.Limits.IsColimit d)
参数：f : (i : ι) → X i ⟶ S；u : a.pt ⟶ S；v : B ⟶ S；q₁ : (i : ι) → P i ⟶ X i；q₂ : (i
 : ι) → P i ⟶ B；∀ (i : ι), CategoryTheory.IsPullback (q₁ i) (q₂ i) (f i) v；d : C
ategoryTheory.Limits.Cofan P；e : d.pt ≅ Z；∀ (i : ι), CategoryTheory.CategoryStru
ct.comp (a.inj i) u = f i；∀ (i : ι),                       CategoryTheory.Catego
ryStruct.comp (d.inj i) (CategoryTheory.CategoryStruct.comp e.hom p₁) =         
                CategoryTheory.CategoryStruct.comp (q₁ i) (a.inj i)；∀ (i : ι),  
                       CategoryTheory.CategoryStruct.comp (d.inj i) (CategoryThe
ory.CategoryStruct.comp e.hom p₂) =                           q₂ i；CategoryTheor
y.Limits.IsColimit d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_pullbackCone_rig
ht`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {S B
 : C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   Categ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Pullbacks distribute over universal coproducts on the right: This is the isomorp
hism
`∐ (Xᵢ ×[S] B) ≅ (∐ Xᵢ) ×[S] B`.
-/
lemma IsUniversalColimit.nonempty_isColimit_of_isPullback_right
    {Z : C} {p₁ : Z ⟶ a.pt} {p₂ : Z ⟶ B} (h : IsPullback p₁ p₂ u v)
    (d : Cofan P) (e : d.pt ≅ Z)
    (hu : ∀ i, a.inj i ≫ u = f i := by cat_disch)
    (he₁ : ∀ i, d.inj i ≫ e.hom ≫ p₁ = q₁ i ≫ a.inj i := by cat_disch)
    (he₂ : ∀ i, d.inj i ≫ e.hom ≫ p₂ = q₂ i := by cat_disch) :
    Nonempty (IsColimit d) :=
  hau.nonempty_isColimit_of_pullbackCone_right f u v (fun i ↦ (hP i).cone)
    (fun i ↦ (hP i).isLimit) h.cone h.isLimit d e

set_option backward.isDefEq.respectTransparency false in
include hau hP in
/-- Pullbacks distribute over universal coproducts on the right: This is the isomorphism
`∐ (Xᵢ ×[S] B) ≅ (∐ Xᵢ) ×[S] B`. -/
/-
**CategoryTheory.IsUniversalColimit.isPullback_of_isColimit_right** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.IsUniversalColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {S
 B : C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   CategoryTheory.IsUn
iversalColimit a →     ∀ (f : (i : ι) → X i ⟶ S) (u : a.pt ⟶ S) (v : B ⟶ S) {P :
 ι → C} (q₁ : (i : ι) → P i ⟶ X i)       (q₂ : (i : ι) → P i ⟶ B),       (∀ (i :
 ι), CategoryTheory.IsPullback (q₁ i) (q₂ i) (f i) v) →         ∀ {d : CategoryT
heory.Limits.Cofan P} (hd : CategoryTheory.Limits.IsColimit d),           autoPa
ram (∀ (i : ι), CategoryTheory.CategoryStruct.comp (a.inj i) u = f i)           
    CategoryTheory.IsUniversalColimit.isPullback_of_isColimit_right._auto_1 →   
          ∀ [CategoryTheory.Limits.HasPullback u v],               CategoryTheor
y.IsPullback                 (CategoryTheory.Limits.Cofan.IsColimit.desc hd fun 
x =>                   CategoryTheory.CategoryStruct.comp (q₁ x) (a.inj x))     
            (CategoryTheory.Limits.Cofan.IsColimit.desc hd q₂) u v
参数：f : (i : ι) → X i ⟶ S；u : a.pt ⟶ S；v : B ⟶ S；q₁ : (i : ι) → P i ⟶ X i；q₂ : (i
 : ι) → P i ⟶ B；∀ (i : ι), CategoryTheory.IsPullback (q₁ i) (q₂ i) (f i) v；hd : 
CategoryTheory.Limits.IsColimit d；∀ (i : ι), CategoryTheory.CategoryStruct.comp 
(a.inj i) u = f i；CategoryTheory.Limits.Cofan.IsColimit.desc hd fun x =>        
           CategoryTheory.CategoryStruct.comp (q₁ x) (a.inj x)；CategoryTheory.Li
mits.Cofan.IsColimit.desc hd q₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_isPullback_right
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {S B :
 C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   Categ…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用引理 `CategoryTheory.IsPullback.of_iso`：of_iso (h : IsPullback fst snd f g) {P
' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} 
(e₁ : P ≅ P') (e₂ : X …
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso_hom_desc`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…

--- 原说明 ---
Pullbacks distribute over universal coproducts on the right: This is the isomorp
hism
`∐ (Xᵢ ×[S] B) ≅ (∐ Xᵢ) ×[S] B`.
-/
lemma IsUniversalColimit.isPullback_of_isColimit_right {d : Cofan P} (hd : IsColimit d)
    (hu : ∀ i, a.inj i ≫ u = f i := by cat_disch)
    [HasPullback u v] :
    IsPullback (Cofan.IsColimit.desc hd (q₁ · ≫ a.inj _)) (Cofan.IsColimit.desc hd q₂)
      u v := by
  let c : Cofan P := Cofan.mk (pullback u v)
    fun i ↦ pullback.lift (q₁ i ≫ a.inj i) (q₂ i) (by simp [(hP i).w, hu])
  obtain ⟨hc⟩ := hau.nonempty_isColimit_of_isPullback_right f u
    v q₁ q₂ hP (IsPullback.of_hasPullback _ _) c (Iso.refl _)
  refine (IsPullback.of_hasPullback u v).of_iso
      ?_ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact hc.coconePointUniqueUpToIso hd
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_fst _ _ _
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_snd _ _ _

end

variable {Y : ι' → C} {b : Cofan Y} (hbu : IsUniversalColimit b)
  (f : ∀ i, X i ⟶ S) (g : ∀ i, Y i ⟶ S) (u : a.pt ⟶ S) (v : b.pt ⟶ S)
  [∀ i, HasPullback (f i) v]

set_option backward.isDefEq.respectTransparency false in
include hau hbu in
/-- Pullbacks distribute over universal coproducts in both arguments: This is the isomorphism
`∐ (Xᵢ ×[S] Xⱼ) ≅ (∐ Xᵢ) ×[S] (∐ Xⱼ)`. -/
/-
**CategoryTheory.IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsUniversalColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {ι
' : Type u_4} {S : C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   Categ
oryTheory.IsUniversalColimit a →     ∀ {Y : ι' → C} {b : CategoryTheory.Limits.C
ofan Y},       CategoryTheory.IsUniversalColimit b →         ∀ (f : (i : ι) → X 
i ⟶ S) (g : (i : ι') → Y i ⟶ S) (u : a.pt ⟶ S) (v : b.pt ⟶ S)           [∀ (i : 
ι), CategoryTheory.Limits.HasPullback (f i) v]           (s : (i : ι) → (j : ι')
 → CategoryTheory.Limits.PullbackCone (f i) (g j))           (hs : (i : ι) → (j 
: ι') → CategoryTheory.Limits.IsLimit (s i j)) (t : CategoryTheory.Limits.Pullba
ckCone u v)           (ht : CategoryTheory.Limits.IsLimit t) {d : CategoryTheory
.Limits.Cofan fun p => (s p.1 p.2).pt}           (e : d.pt ≅ t.pt),           au
toParam (∀ (i : ι), CategoryTheory.CategoryStruct.comp (a.inj i) u = f i)       
        CategoryTheory.IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCon
e._auto_1 →             autoParam (∀ (i : ι'), CategoryTheory.CategoryStruct.com
p (b.inj i) v = g i)                 CategoryTheory.IsUniversalColimit.nonempty_
isColimit_prod_of_pullbackCone._auto_3 →               autoParam                
   (∀ (i : ι) (j : ι'),                     CategoryTheory.CategoryStruct.comp (
d.inj (i, j)) (CategoryTheory.CategoryStruct.comp e.hom t.fst) =                
       CategoryTheory.CategoryStruct.comp (s (i, j).1 (i, j).2).fst (a.inj (i, j
).1))                   CategoryTheory.IsUniversalColimit.nonempty_isColimit_pro
d_of_pullbackCone._auto_5 →                 autoParam                     (∀ (i 
: ι) (j : ι'),                       CategoryTheory.CategoryStruct.comp (d.inj (
i, j))                           (CategoryTheory.CategoryStruct.comp e.hom t.snd
) =                         CategoryTheory.CategoryStruct.comp (s (i, j).1 (i, j
).2).snd (b.inj (i, j).2))                     CategoryTheory.IsUniversalColimit
.nonempty_isColimit_prod_of_pullbackCone._auto_7 →                   Nonempty (C
ategoryTheory.Limits.IsColimit d)
参数：f : (i : ι) → X i ⟶ S；g : (i : ι') → Y i ⟶ S；u : a.pt ⟶ S；v : b.pt ⟶ S；i : ι；
f i；s : (i : ι) → (j : ι') → CategoryTheory.Limits.PullbackCone (f i) (g j)；hs :
 (i : ι) → (j : ι') → CategoryTheory.Limits.IsLimit (s i j)；t : CategoryTheory.L
imits.PullbackCone u v；ht : CategoryTheory.Limits.IsLimit t；s p.1 p.2；e : d.pt ≅
 t.pt；∀ (i : ι), CategoryTheory.CategoryStruct.comp (a.inj i) u = f i；∀ (i : ι')
, CategoryTheory.CategoryStruct.comp (b.inj i) v = g i；∀ (i : ι) (j : ι'),      
               CategoryTheory.CategoryStruct.comp (d.inj (i, j)) (CategoryTheory
.CategoryStruct.comp e.hom t.fst) =                       CategoryTheory.Categor
yStruct.comp (s (i, j).1 (i, j).2).fst (a.inj (i, j).1)；∀ (i : ι) (j : ι'),     
                  CategoryTheory.CategoryStruct.comp (d.inj (i, j))             
              (CategoryTheory.CategoryStruct.comp e.hom t.snd) =                
         CategoryTheory.CategoryStruct.comp (s (i, j).1 (i, j).2).snd (b.inj (i,
 j).2)；CategoryTheory.Limits.IsColimit d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t : 
CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_snd`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_pullbackCone_lef
t`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {S B 
: C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   Categ…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.IsUniversalColimit.nonempty_isColimit_of_pullbackCone_rig
ht`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {S B
 : C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   Categ…

--- 原说明 ---
Pullbacks distribute over universal coproducts in both arguments: This is the is
omorphism
`∐ (Xᵢ ×[S] Xⱼ) ≅ (∐ Xᵢ) ×[S] (∐ Xⱼ)`.
-/
lemma IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone
    (s : ∀ (i : ι) (j : ι'), PullbackCone (f i) (g j))
    (hs : ∀ i j, IsLimit (s i j)) (t : PullbackCone u v) (ht : IsLimit t)
    {d : Cofan (fun p : ι × ι' ↦ (s p.1 p.2).pt)} (e : d.pt ≅ t.pt)
    (hu : ∀ i, a.inj i ≫ u = f i := by cat_disch)
    (hv : ∀ i, b.inj i ≫ v = g i := by cat_disch)
    (he₁ : ∀ i j, d.inj (i, j) ≫ e.hom ≫ t.fst = (s _ _).fst ≫ a.inj _ := by cat_disch)
    (he₂ : ∀ i j, d.inj (i, j) ≫ e.hom ≫ t.snd = (s _ _).snd ≫ b.inj _ := by cat_disch) :
    Nonempty (IsColimit d) := by
  let c (i : ι) : Cofan (fun j : ι' ↦ (s i j).pt) :=
    Cofan.mk (pullback (f i) v) fun j ↦ pullback.lift (s i j).fst ((s i j).snd ≫ b.inj j)
      (by simp [hv, (s i j).condition])
  let c' : Cofan (fun i : ι ↦ (c i).pt) :=
    Cofan.mk t.pt fun i ↦
      PullbackCone.IsLimit.lift ht (pullback.fst _ _ ≫ a.inj i) (pullback.snd _ _)
      (by simp [hu, pullback.condition])
  let iso : d ≅ Cofan.mk c'.pt fun p : ι × ι' ↦ (c p.1).inj p.2 ≫ c'.inj _ := by
    refine Cofan.ext e <| fun p ↦ PullbackCone.IsLimit.hom_ext ht ?_ ?_
    · simp [c', c, he₁]
    · simp [c', c, he₂]
  rw [(IsColimit.equivIsoColimit iso).nonempty_congr]
  refine ⟨Cofan.IsColimit.prod c (fun i ↦ Nonempty.some ?_) c' (Nonempty.some ?_)⟩
  · exact hbu.nonempty_isColimit_of_pullbackCone_left _ v _ _ (hs i) (pullback.cone _ _)
      (pullback.isLimit _ _) _ (Iso.refl _)
  · exact hau.nonempty_isColimit_of_pullbackCone_right _ u _ _ (fun _ ↦ pullback.isLimit _ _)
      t ht _ (Iso.refl _)

include hau hbu in
/-- Pullbacks distribute over universal coproducts in both arguments: This is the isomorphism
`∐ (Xᵢ ×[S] Xⱼ) ≅ (∐ Xᵢ) ×[S] (∐ Xⱼ)`. -/
/-
**CategoryTheory.IsUniversalColimit.nonempty_isColimit_prod_of_isPullback** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.IsUniversalColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {ι
' : Type u_4} {S : C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   Categ
oryTheory.IsUniversalColimit a →     ∀ {Y : ι' → C} {b : CategoryTheory.Limits.C
ofan Y},       CategoryTheory.IsUniversalColimit b →         ∀ (f : (i : ι) → X 
i ⟶ S) (g : (i : ι') → Y i ⟶ S) (u : a.pt ⟶ S) (v : b.pt ⟶ S)           [∀ (i : 
ι), CategoryTheory.Limits.HasPullback (f i) v] {P : ι × ι' → C}           {q₁ : 
(i : ι) → (j : ι') → P (i, j) ⟶ X i} {q₂ : (i : ι) → (j : ι') → P (i, j) ⟶ Y j},
           (∀ (i : ι) (j : ι'), CategoryTheory.IsPullback (q₁ i j) (q₂ i j) (f i
) (g j)) →             ∀ {Z : C} {p₁ : Z ⟶ a.pt} {p₂ : Z ⟶ b.pt},               
CategoryTheory.IsPullback p₁ p₂ u v →                 ∀ {d : CategoryTheory.Limi
ts.Cofan P} (e : d.pt ≅ Z),                   autoParam (∀ (i : ι), CategoryTheo
ry.CategoryStruct.comp (a.inj i) u = f i)                       CategoryTheory.I
sUniversalColimit.nonempty_isColimit_prod_of_isPullback._auto_1 →               
      autoParam (∀ (i : ι'), CategoryTheory.CategoryStruct.comp (b.inj i) v = g 
i)                         CategoryTheory.IsUniversalColimit.nonempty_isColimit_
prod_of_isPullback._auto_3 →                       autoParam                    
       (∀ (i : ι) (j : ι'),                             CategoryTheory.CategoryS
truct.comp (d.inj (i, j))                                 (CategoryTheory.Catego
ryStruct.comp e.hom p₁) =                               CategoryTheory.CategoryS
truct.comp (q₁ i j) (a.inj i))                           CategoryTheory.IsUniver
salColimit.nonempty_isColimit_prod_of_isPullback._auto_5 →                      
   autoParam                             (∀ (i : ι) (j : ι'),                   
            CategoryTheory.CategoryStruct.comp (d.inj (i, j))                   
                (CategoryTheory.CategoryStruct.comp e.hom p₂) =                 
                CategoryTheory.CategoryStruct.comp (q₂ i j) (b.inj j))          
                   CategoryTheory.IsUniversalColimit.nonempty_isColimit_prod_of_
isPullback._auto_7 →                           Nonempty (CategoryTheory.Limits.I
sColimit d)
参数：f : (i : ι) → X i ⟶ S；g : (i : ι') → Y i ⟶ S；u : a.pt ⟶ S；v : b.pt ⟶ S；i : ι；
f i；i : ι；j : ι'；i, j；i : ι；j : ι'；i, j；∀ (i : ι) (j : ι'), CategoryTheory.IsPul
lback (q₁ i j) (q₂ i j) (f i) (g j)；e : d.pt ≅ Z；∀ (i : ι), CategoryTheory.Categ
oryStruct.comp (a.inj i) u = f i；∀ (i : ι'), CategoryTheory.CategoryStruct.comp 
(b.inj i) v = g i；∀ (i : ι) (j : ι'),                             CategoryTheory
.CategoryStruct.comp (d.inj (i, j))                                 (CategoryThe
ory.CategoryStruct.comp e.hom p₁) =                               CategoryTheory
.CategoryStruct.comp (q₁ i j) (a.inj i)；∀ (i : ι) (j : ι'),                     
          CategoryTheory.CategoryStruct.comp (d.inj (i, j))                     
              (CategoryTheory.CategoryStruct.comp e.hom p₂) =                   
              CategoryTheory.CategoryStruct.comp (q₂ i j) (b.inj j)；CategoryTheo
ry.Limits.IsColimit d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCon
e`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {ι' :
 Type u_4} {S : C} {X : ι → C}   {a : CategoryTheory.Limits.Cof…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Pullbacks distribute over universal coproducts in both arguments: This is the is
omorphism
`∐ (Xᵢ ×[S] Xⱼ) ≅ (∐ Xᵢ) ×[S] (∐ Xⱼ)`.
-/
lemma IsUniversalColimit.nonempty_isColimit_prod_of_isPullback
    {P : ι × ι' → C} {q₁ : ∀ i j, P (i, j) ⟶ X i} {q₂ : ∀ i j, P (i, j) ⟶ Y j}
    (hP : ∀ i j, IsPullback (q₁ i j) (q₂ i j) (f i) (g j))
    {Z : C} {p₁ : Z ⟶ a.pt} {p₂ : Z ⟶ b.pt} (h : IsPullback p₁ p₂ u v)
    {d : Cofan P} (e : d.pt ≅ Z)
    (hu : ∀ i, a.inj i ≫ u = f i := by cat_disch)
    (hv : ∀ i, b.inj i ≫ v = g i := by cat_disch)
    (he₁ : ∀ i j, d.inj (i, j) ≫ e.hom ≫ p₁ = q₁ _ _ ≫ a.inj _ := by cat_disch)
    (he₂ : ∀ i j, d.inj (i, j) ≫ e.hom ≫ p₂ = q₂ _ _ ≫ b.inj _ := by cat_disch) :
    Nonempty (IsColimit d) :=
  IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone hau hbu f g u v
    (fun i j ↦ (hP i j).cone) (fun i j ↦ (hP i j).isLimit) h.cone h.isLimit e

set_option backward.isDefEq.respectTransparency false in
include hau hbu in
/-
**CategoryTheory.IsUniversalColimit.isPullback_prod_of_isColimit** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.IsUniversalColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {ι
' : Type u_4} {S : C} {X : ι → C}   {a : CategoryTheory.Limits.Cofan X},   Categ
oryTheory.IsUniversalColimit a →     ∀ {Y : ι' → C} {b : CategoryTheory.Limits.C
ofan Y},       CategoryTheory.IsUniversalColimit b →         ∀ (f : (i : ι) → X 
i ⟶ S) (g : (i : ι') → Y i ⟶ S) (u : a.pt ⟶ S) (v : b.pt ⟶ S)           [∀ (i : 
ι), CategoryTheory.Limits.HasPullback (f i) v] [CategoryTheory.Limits.HasPullbac
k u v]           {P : ι × ι' → C} {q₁ : (i : ι) → (j : ι') → P (i, j) ⟶ X i} {q₂
 : (i : ι) → (j : ι') → P (i, j) ⟶ Y j},           (∀ (i : ι) (j : ι'), Category
Theory.IsPullback (q₁ i j) (q₂ i j) (f i) (g j)) →             ∀ (d : CategoryTh
eory.Limits.Cofan P) (hd : CategoryTheory.Limits.IsColimit d),               aut
oParam (∀ (i : ι), CategoryTheory.CategoryStruct.comp (a.inj i) u = f i)        
           CategoryTheory.IsUniversalColimit.isPullback_prod_of_isColimit._auto_
1 →                 autoParam (∀ (i : ι'), CategoryTheory.CategoryStruct.comp (b
.inj i) v = g i)                     CategoryTheory.IsUniversalColimit.isPullbac
k_prod_of_isColimit._auto_3 →                   CategoryTheory.IsPullback       
              (CategoryTheory.Limits.Cofan.IsColimit.desc hd fun p =>           
            CategoryTheory.CategoryStruct.comp (q₁ p.1 p.2) (a.inj p.1))        
             (CategoryTheory.Limits.Cofan.IsColimit.desc hd fun p =>            
           CategoryTheory.CategoryStruct.comp (q₂ p.1 p.2) (b.inj p.2))         
            u v
参数：f : (i : ι) → X i ⟶ S；g : (i : ι') → Y i ⟶ S；u : a.pt ⟶ S；v : b.pt ⟶ S；i : ι；
f i；i : ι；j : ι'；i, j；i : ι；j : ι'；i, j；∀ (i : ι) (j : ι'), CategoryTheory.IsPul
lback (q₁ i j) (q₂ i j) (f i) (g j)；d : CategoryTheory.Limits.Cofan P；hd : Categ
oryTheory.Limits.IsColimit d；∀ (i : ι), CategoryTheory.CategoryStruct.comp (a.in
j i) u = f i；∀ (i : ι'), CategoryTheory.CategoryStruct.comp (b.inj i) v = g i；Ca
tegoryTheory.Limits.Cofan.IsColimit.desc hd fun p =>                       Categ
oryTheory.CategoryStruct.comp (q₁ p.1 p.2) (a.inj p.1)；CategoryTheory.Limits.Cof
an.IsColimit.desc hd fun p =>                       CategoryTheory.CategoryStruc
t.comp (q₂ p.1 p.2) (b.inj p.2)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsUniversalColimit.nonempty_isColimit_prod_of_isPullback`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_3} {ι' : T
ype u_4} {S : C} {X : ι → C}   {a : CategoryTheory.Limits.Cof…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用引理 `CategoryTheory.IsPullback.of_iso`：of_iso (h : IsPullback fst snd f g) {P
' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} 
(e₁ : P ≅ P') (e₂ : X …
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheo…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso_hom_desc`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
lemma IsUniversalColimit.isPullback_prod_of_isColimit [HasPullback u v]
    {P : ι × ι' → C} {q₁ : ∀ i j, P (i, j) ⟶ X i} {q₂ : ∀ i j, P (i, j) ⟶ Y j}
    (hP : ∀ i j, IsPullback (q₁ i j) (q₂ i j) (f i) (g j)) (d : Cofan P) (hd : IsColimit d)
    (hu : ∀ i, a.inj i ≫ u = f i := by cat_disch)
    (hv : ∀ i, b.inj i ≫ v = g i := by cat_disch) :
    IsPullback
      (Cofan.IsColimit.desc hd (fun p ↦ q₁ p.1 p.2 ≫ a.inj _))
      (Cofan.IsColimit.desc hd (fun p ↦ q₂ p.1 p.2 ≫ b.inj _)) u v := by
  let c : Cofan P := Cofan.mk (pullback u v)
    fun p ↦ pullback.lift (q₁ p.1 p.2 ≫ a.inj p.1) (q₂ p.1 p.2 ≫ b.inj _)
      (by simp [(hP p.1 p.2).w, hu, hv])
  obtain ⟨hc⟩ := hau.nonempty_isColimit_prod_of_isPullback hbu f g u
    v hP (IsPullback.of_hasPullback _ _) (d := c) (Iso.refl _)
  refine (IsPullback.of_hasPullback u v).of_iso
      ?_ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact hc.coconePointUniqueUpToIso hd
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_fst _ _ _
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
    simpa [Cofan.inj, Cofan.IsColimit.desc] using! pullback.lift_snd _ _ _

end CoproductsPullback

end CategoryTheory

