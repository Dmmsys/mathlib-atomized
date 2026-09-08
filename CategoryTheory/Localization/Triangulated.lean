/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.ComposableArrows
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Shift.Localization

/-! # Localization of triangulated categories

If `L : C ⥤ D` is a localization functor for a class of morphisms `W` that is compatible
with the triangulation on the category `C` and admits a left calculus of fractions,
it is shown in this file that `D` can be equipped with a pretriangulated category structure,
and that it is triangulated.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Pretriangulated Localization

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
  [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasShift D ℤ] [L.CommShift ℤ]

namespace MorphismProperty

/-- Given `W` is a class of morphisms in a pretriangulated category `C`, this is the condition
that `W` is compatible with the triangulation on `C`. -/
/-
**CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation** 是 Mathlib 中的一个
归纳类型，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.HasShift C ℤ] →       [inst_2 : CategoryTheory.Preadditive
 C] →         [inst_3 : CategoryTheory.Limits.HasZeroObject C] →           [inst
_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] →             [Categ
oryTheory.Pretriangulated C] → CategoryTheory.MorphismProperty C → Prop
参数：n : ℤ；CategoryTheory.shiftFunctor C n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `W` is a class of morphisms in a pretriangulated category `C`, this is the
 condition
that `W` is compatible with the triangulation on `C`.
-/
class IsCompatibleWithTriangulation (W : MorphismProperty C) : Prop
    extends W.IsCompatibleWithShift ℤ where
  compatible_with_triangulation (T₁ T₂ : Triangle C)
    (_ : T₁ ∈ distTriang C) (_ : T₂ ∈ distTriang C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (_ : W a) (_ : W b)
    (_ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
      ∃ (c : T₁.obj₃ ⟶ T₂.obj₃) (_ : W c),
        (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧ (T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃)

export IsCompatibleWithTriangulation (compatible_with_triangulation)

end MorphismProperty

namespace Functor

/-- Given a functor `C ⥤ D` from a pretriangulated category, this is the set of
triangles in `D` that are in the essential image of distinguished triangles of `C`. -/
/-
**CategoryTheory.Functor.essImageDistTriang** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：essImageDistTriang : Set (Triangle D)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `C ⥤ D` from a pretriangulated category, this is the set of
triangles in `D` that are in the essential image of distinguished triangles of `
C`.
-/
def essImageDistTriang : Set (Triangle D) :=
  {T | ∃ (T' : Triangle C) (_ : T ≅ L.mapTriangle.obj T'), T' ∈ distTriang C}
/-
**CategoryTheory.Functor.essImageDistTriang_mem_of_iso** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：essImageDistTriang_mem_of_iso {T₁ T₂ : Triangle D} (e : T₂ ≅ T₁) (h : T₁ i
n L.essImageDistTriang) : T₂ in L.essImageDistTriang
参数：e : T₂ ≅ T₁；h : T₁ in L.essImageDistTriang。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma essImageDistTriang_mem_of_iso {T₁ T₂ : Triangle D} (e : T₂ ≅ T₁)
    (h : T₁ ∈ L.essImageDistTriang) : T₂ ∈ L.essImageDistTriang := by
  obtain ⟨T', e', hT'⟩ := h
  exact ⟨T', e ≪≫ e', hT'⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.contractible_mem_essImageDistTriang** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：contractible_mem_essImageDistTriang [EssSurj L] [HasZeroObject D] [HasZero
Morphisms D] [L.PreservesZeroMorphisms] (X : D) : contractibleTriangle X in L.es
sImageDistTriang
参数：X : D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Pretriangulated.contractible_distinguished`：∀ {C : Type u
} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZ
eroObject C}   {inst_2 : CategoryTheory.HasShif…
-/
lemma contractible_mem_essImageDistTriang [EssSurj L] [HasZeroObject D]
    [HasZeroMorphisms D] [L.PreservesZeroMorphisms] (X : D) :
    contractibleTriangle X ∈ L.essImageDistTriang := by
  refine ⟨contractibleTriangle (L.objPreimage X), ?_, contractible_distinguished _⟩
  exact ((contractibleTriangleFunctor D).mapIso (L.objObjPreimageIso X)).symm ≪≫
    Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) L.mapZeroObject.symm (by simp) (by simp) (by simp)
/-
**CategoryTheory.Functor.rotate_essImageDistTriang** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：rotate_essImageDistTriang [Preadditive D] [L.Additive] [forall (n : Int), 
(shiftFunctor D n).Additive] (T : Triangle D) : T in L.essImageDistTriang ↔ T.ro
tate in L.essImageDistTriang
参数：n : Int；shiftFunctor D n；T : Triangle D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.rot_of_distTriang`：rot_of_distTriang (T :
 Triangle C) (H : T in distTriang C) : T.rotate in distTriang C
· 使用定理 `CategoryTheory.Pretriangulated.inv_rot_of_distTriang`：inv_rot_of_distTri
ang (T : Triangle C) (H : T in distTriang C) : T.invRotate in distTriang C
-/
lemma rotate_essImageDistTriang [Preadditive D] [L.Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] (T : Triangle D) :
    T ∈ L.essImageDistTriang ↔ T.rotate ∈ L.essImageDistTriang := by
  constructor
  · rintro ⟨T', e', hT'⟩
    exact ⟨T'.rotate, (rotate D).mapIso e' ≪≫ L.mapTriangleRotateIso.app T',
      rot_of_distTriang T' hT'⟩
  · rintro ⟨T', e', hT'⟩
    exact ⟨T'.invRotate, (triangleRotation D).unitIso.app T ≪≫ (invRotate D).mapIso e' ≪≫
      L.mapTriangleInvRotateIso.app T', inv_rot_of_distTriang T' hT'⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.complete_distinguished_essImageDistTriang_morphism** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：complete_distinguished_essImageDistTriang_morphism (H : forall (T₁' T₂' : 
Triangle C) (_ : T₁' in distTriang C) (_ : T₂' in distTriang C) (a : L.obj (T₁'.
obj₁) ⟶ L.obj (T₂'.obj₁)) (b : L.obj (T₁'.obj₂) ⟶ L.obj (T₂'.obj₂)) (_ : L.map T
₁'.mor₁ ≫ b = a ≫ L.map T₂'.mor₁), exists (φ : L.mapTriangle.obj T₁' ⟶ L.mapTria
ngle.obj T₂'), φ.hom₁ = a ∧ φ.hom₂ = b) (T₁ T₂ : Triangle D) (hT₁ : T₁ in Functo
r.essImageDistTriang L) (hT₂ : T₂ in L.essImageDistTriang) (a : T₁.obj₁ ⟶ T₂.obj
₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
参数：H : forall (T₁' T₂' : Triangle C) (_ : T₁' in distTriang C) (_ : T₂' in distT
riang C) (a : L.obj (T₁'.obj₁) ⟶ L.obj (T₂'.obj₁)) (b : L.obj (T₁'.obj₂) ⟶ L.obj
 (T₂'.obj₂)) (_ : L.map T₁'.mor₁ ≫ b = a ≫ L.map T₂'.mor₁), exists (φ : L.mapTri
angle.obj T₁' ⟶ L.mapTriangle.obj T₂'), φ.hom₁ = a ∧ φ.hom₂ = b；T₁ T₂ : Triangle
 D；hT₁ : T₁ in Functor.essImageDistTriang L；hT₂ : T₂ in L.essImageDistTriang；a :
 T₁.obj₁ ⟶ T₂.obj₁；b : T₁.obj₂ ⟶ T₂.obj₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.TriangleMorphism.comm₁`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {T₁ T₂ : CategoryTheory.Pretriangulated.Tr…
· 使用定理 `CategoryTheory.Pretriangulated.TriangleMorphism.comm₂`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {T₁ T₂ : CategoryTheory.Pretriangulated.Tr…
· 使用定理 `CategoryTheory.Pretriangulated.TriangleMorphism.comm₃`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {T₁ T₂ : CategoryTheory.Pretriangulated.Tr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.hom_inv_id_triangle_hom₂_assoc`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]   {A 
B : CategoryTheory.Pretriangulated.Tria…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_triangle_hom₃`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]   {A B : Ca
tegoryTheory.Pretriangulated.Tria…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Pretriangulated.Triangle.instIsIsoHom₃`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {A B : CategoryTheory.Pretriangulated.Tria…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_triangle_hom₃_assoc`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]   {A 
B : CategoryTheory.Pretriangulated.Tria…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.preservesMonomorphisms_of_isRightAdjoint`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instIsEquivalenceShiftFunctor`：∀ (C : Type u) {A : Type u
_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddGroup A]   [inst_2 : 
CategoryTheory.HasShift C A] (i : …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Pretriangulated.Triangle.instIsIsoHom₁`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {A B : CategoryTheory.Pretriangulated.Tria…
（共 32 条，此处仅展示前 30 条）
-/
lemma complete_distinguished_essImageDistTriang_morphism
    (H : ∀ (T₁' T₂' : Triangle C) (_ : T₁' ∈ distTriang C) (_ : T₂' ∈ distTriang C)
      (a : L.obj (T₁'.obj₁) ⟶ L.obj (T₂'.obj₁)) (b : L.obj (T₁'.obj₂) ⟶ L.obj (T₂'.obj₂))
      (_ : L.map T₁'.mor₁ ≫ b = a ≫ L.map T₂'.mor₁),
      ∃ (φ : L.mapTriangle.obj T₁' ⟶ L.mapTriangle.obj T₂'), φ.hom₁ = a ∧ φ.hom₂ = b)
    (T₁ T₂ : Triangle D)
    (hT₁ : T₁ ∈ Functor.essImageDistTriang L) (hT₂ : T₂ ∈ L.essImageDistTriang)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨T₁', e₁, hT₁'⟩ := hT₁
  obtain ⟨T₂', e₂, hT₂'⟩ := hT₂
  have comm₁ := e₁.inv.comm₁
  have comm₁' := e₂.hom.comm₁
  have comm₂ := e₁.hom.comm₂
  have comm₂' := e₂.hom.comm₂
  have comm₃ := e₁.inv.comm₃
  have comm₃' := e₂.hom.comm₃
  dsimp at comm₁ comm₁' comm₂ comm₂' comm₃ comm₃'
  simp only [assoc] at comm₃
  obtain ⟨φ, hφ₁, hφ₂⟩ := H T₁' T₂' hT₁' hT₂' (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁)
    (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂)
    (by simp only [assoc, ← comm₁', ← reassoc_of% fac, ← reassoc_of% comm₁])
  have h₂ := φ.comm₂
  have h₃ := φ.comm₃
  dsimp at h₂ h₃
  simp only [assoc] at h₃
  refine ⟨e₁.hom.hom₃ ≫ φ.hom₃ ≫ e₂.inv.hom₃, ?_, ?_⟩
  · rw [reassoc_of% comm₂, reassoc_of% h₂, hφ₂, assoc, assoc,
      Iso.hom_inv_id_triangle_hom₂_assoc, ← reassoc_of% comm₂',
      Iso.hom_inv_id_triangle_hom₃, comp_id]
  · rw [assoc, assoc, ← cancel_epi e₁.inv.hom₃, ← reassoc_of% comm₃,
      Iso.inv_hom_id_triangle_hom₃_assoc, ← cancel_mono (e₂.hom.hom₁⟦(1 : ℤ)⟧'),
      assoc, assoc, assoc, assoc, assoc, ← Functor.map_comp, ← Functor.map_comp, ← hφ₁,
      h₃, comm₃', Iso.inv_hom_id_triangle_hom₃_assoc]

end Functor

namespace Triangulated

namespace Localization

variable (W : MorphismProperty C) [L.IsLocalization W]
  [W.HasLeftCalculusOfFractions]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include W in
/-
**CategoryTheory.Triangulated.Localization.distinguished_cocone_triangle** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.Localization`。
形式化陈述：distinguished_cocone_triangle {X Y : D} (f : X ⟶ Y) : exists (Z : D) (g : 
Y ⟶ Z) (h : Z ⟶ X⟦(1 : Int)⟧), Triangle.mk f g h in L.essImageDistTriang
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj_mapArrow`：∀ {C : Type u_1} {D : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Pretriangulated.distinguished_cocone_triangle`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.H
asZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Arrow.Hom.w`：∀ {T : Type u} [inst : CategoryTheory.Catego
ry.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : f ⟶ g),   CategoryTheory.Categ
oryStruct.comp (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma distinguished_cocone_triangle {X Y : D} (f : X ⟶ Y) :
    ∃ (Z : D) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ L.essImageDistTriang := by
  have := essSurj_mapArrow L W
  obtain ⟨φ, ⟨e⟩⟩ : ∃ (φ : Arrow C), Nonempty (L.mapArrow.obj φ ≅ Arrow.mk f) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
  obtain ⟨Z, g, h, H⟩ := Pretriangulated.distinguished_cocone_triangle φ.hom
  refine ⟨L.obj Z, e.inv.right ≫ L.map g,
    L.map h ≫ (L.commShiftIso (1 : ℤ)).hom.app _ ≫ e.hom.left⟦(1 : ℤ)⟧', _, ?_, H⟩
  refine Triangle.isoMk _ _ (Arrow.leftFunc.mapIso e.symm) (Arrow.rightFunc.mapIso e.symm)
    (Iso.refl _) e.inv.w.symm (by simp) ?_
  dsimp
  simp only [assoc, id_comp, ← Functor.map_comp, ← Arrow.comp_left, e.hom_inv_id, Arrow.id_left,
    Functor.mapArrow_obj, Arrow.mk_left, Functor.map_id, comp_id]

section
variable [W.IsCompatibleWithTriangulation]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include W in
/-
**CategoryTheory.Triangulated.Localization.complete_distinguished_triangle_morph
ism** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.Localization`。
形式化陈述：complete_distinguished_triangle_morphism (T₁ T₂ : Triangle D) (hT₁ : T₁ in
 L.essImageDistTriang) (hT₂ : T₂ in L.essImageDistTriang) (a : T₁.obj₁ ⟶ T₂.obj₁
) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) : exists c, T₁.mor₂ 
≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃
参数：T₁ T₂ : Triangle D；hT₁ : T₁ in L.essImageDistTriang；hT₂ : T₂ in L.essImageDis
tTriang；a : T₁.obj₁ ⟶ T₂.obj₁；b : T₁.obj₂ ⟶ T₂.obj₂；fac : T₁.mor₁ ≫ b = a ≫ T₂.m
or₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.complete_distinguished_essImageDistTriang_morphis
m`：complete_distinguished_essImageDistTriang_morphism (H : forall (T₁' T₂' : Tri
angle C) (_ : T₁' in distTriang C) (_ : T₂' in distTriang C) (a…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Localization.exists_leftFraction`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.exists_leftFraction`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.Mo
rphismProperty C}   [W.HasLeftCalculusOfFractions] {X Y…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.map_eq_iff_postcomp`：∀ {C : Type u_1} {D
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s`：map_comp_ma
p_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : φ.map L hL ≫ 
L.map φ.s = L.map φ.f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.instIsIsoMapSOfIsLocalizati
on`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C
]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {W : Categor…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s_assoc`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] {W : Categor…
· 使用定理 `CategoryTheory.Pretriangulated.distinguished_cocone_triangle`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.H
asZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions.toIsMultiplic
ative`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasLeftCalculusOfFraction…
· 使用定理 `CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation.compatible
_with_triangulation`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1}
 C} {inst_1 : CategoryTheory.HasShift C ℤ}   {inst_2 : CategoryTheory.Preadditiv
e…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Pretriangulated.Triangle.isIso_of_isIsos`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]
   {A B : CategoryTheory.Pretriangulated.Tria…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Pretriangulated.Triangle.instIsIsoHom₁`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {A B : CategoryTheory.Pretriangulated.Tria…
· 使用引理 `CategoryTheory.Pretriangulated.comp_hom₁`：comp_hom₁ {X Y Z : Triangle C}
 (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom₁ = f.hom₁ ≫ g.hom₁
（共 37 条，此处仅展示前 30 条）
-/
lemma complete_distinguished_triangle_morphism (T₁ T₂ : Triangle D)
    (hT₁ : T₁ ∈ L.essImageDistTriang) (hT₂ : T₂ ∈ L.essImageDistTriang)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  refine L.complete_distinguished_essImageDistTriang_morphism ?_ T₁ T₂ hT₁ hT₂ a b fac
  clear a b fac hT₁ hT₂ T₁ T₂
  intro T₁ T₂ hT₁ hT₂ a b fac
  obtain ⟨α, hα⟩ := exists_leftFraction L W a
  obtain ⟨β, hβ⟩ := (MorphismProperty.RightFraction.mk α.s α.hs T₂.mor₁).exists_leftFraction
  obtain ⟨γ, hγ⟩ := exists_leftFraction L W (b ≫ L.map β.s)
  dsimp at hβ
  obtain ⟨Z₂, σ, hσ, fac⟩ := (MorphismProperty.map_eq_iff_postcomp L W
    (α.f ≫ β.f ≫ γ.s) (T₁.mor₁ ≫ γ.f)).1 (by
      rw [← cancel_mono (L.map β.s), assoc, assoc, hγ, ← cancel_mono (L.map γ.s),
        assoc, assoc, assoc, hα, MorphismProperty.LeftFraction.map_comp_map_s,
        ← Functor.map_comp] at fac
      rw [fac, ← Functor.map_comp_assoc, hβ, Functor.map_comp, Functor.map_comp,
        Functor.map_comp, assoc, MorphismProperty.LeftFraction.map_comp_map_s_assoc])
  simp only [assoc] at fac
  obtain ⟨Y₃, g, h, hT₃⟩ := Pretriangulated.distinguished_cocone_triangle (β.f ≫ γ.s ≫ σ)
  let T₃ := Triangle.mk (β.f ≫ γ.s ≫ σ) g h
  change T₃ ∈ distTriang C at hT₃
  have hβγσ : W (β.s ≫ γ.s ≫ σ) := W.comp_mem _ _ β.hs (W.comp_mem _ _ γ.hs hσ)
  obtain ⟨ψ₃, hψ₃, hψ₁, hψ₂⟩ := MorphismProperty.compatible_with_triangulation
    T₂ T₃ hT₂ hT₃ α.s (β.s ≫ γ.s ≫ σ) α.hs hβγσ (by dsimp [T₃]; rw [reassoc_of% hβ])
  let ψ : T₂ ⟶ T₃ := Triangle.homMk _ _ α.s (β.s ≫ γ.s ≫ σ) ψ₃
    (by dsimp [T₃]; rw [reassoc_of% hβ]) hψ₁ hψ₂
  have : IsIso (L.mapTriangle.map ψ) := Triangle.isIso_of_isIsos _
    (inverts L W α.s α.hs) (inverts L W _ hβγσ) (inverts L W ψ₃ hψ₃)
  refine ⟨L.mapTriangle.map (completeDistinguishedTriangleMorphism T₁ T₃ hT₁ hT₃ α.f
      (γ.f ≫ σ) fac.symm) ≫ inv (L.mapTriangle.map ψ), ?_, ?_⟩
  · rw [← cancel_mono (L.mapTriangle.map ψ).hom₁, ← comp_hom₁, assoc, IsIso.inv_hom_id, comp_id]
    dsimp [ψ]
    rw [hα, MorphismProperty.LeftFraction.map_comp_map_s]
  · rw [← cancel_mono (L.mapTriangle.map ψ).hom₂, ← comp_hom₂, assoc, IsIso.inv_hom_id, comp_id]
    dsimp [ψ]
    simp only [Functor.map_comp, reassoc_of% hγ,
      MorphismProperty.LeftFraction.map_comp_map_s_assoc]

variable [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [L.Additive]

/-- The pretriangulated structure on the localized category. -/
@[instance_reducible]
/-
**CategoryTheory.Triangulated.Localization.pretriangulated** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Triangulated.Localization`。
形式化陈述：pretriangulated : Pretriangulated D where distinguishedTriangles
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.essImageDistTriang_mem_of_iso`：essImageDistTriang
_mem_of_iso {T₁ T₂ : Triangle D} (e : T₂ ≅ T₁) (h : T₁ in L.essImageDistTriang) 
: T₂ in L.essImageDistTriang
· 使用引理 `CategoryTheory.Triangulated.Localization.distinguished_cocone_triangle`：
distinguished_cocone_triangle {X Y : D} (f : X ⟶ Y) : exists (Z : D) (g : Y ⟶ Z)
 (h : Z ⟶ X⟦(1 : Int)⟧), Triangle.mk f g h in L.essImageDist…
· 使用引理 `CategoryTheory.Functor.rotate_essImageDistTriang`：rotate_essImageDistTri
ang [Preadditive D] [L.Additive] [forall (n : Int), (shiftFunctor D n).Additive]
 (T : Triangle D) : T in L.essImageDis…
· 使用引理 `CategoryTheory.Triangulated.Localization.complete_distinguished_triangle
_morphism`：complete_distinguished_triangle_morphism (T₁ T₂ : Triangle D) (hT₁ : 
T₁ in L.essImageDistTriang) (hT₂ : T₂ in L.essImageDistTriang) (a : T₁.…

--- 原说明 ---
The pretriangulated structure on the localized category.
-/
def pretriangulated : Pretriangulated D where
  distinguishedTriangles := L.essImageDistTriang
  isomorphic_distinguished _ hT₁ _ e := L.essImageDistTriang_mem_of_iso e hT₁
  contractible_distinguished :=
    have := essSurj L W; L.contractible_mem_essImageDistTriang
  distinguished_cocone_triangle f := distinguished_cocone_triangle L W f
  rotate_distinguished_triangle := L.rotate_essImageDistTriang
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism L W
/-
**CategoryTheory.Triangulated.Localization.isTriangulated_functor** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.Triangulated.Localization`。
形式化陈述：isTriangulated_functor : letI : Pretriangulated D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isTriangulated_functor :
    letI : Pretriangulated D := pretriangulated L W; L.IsTriangulated :=
  letI : Pretriangulated D := pretriangulated L W
  ⟨fun T hT => ⟨T, Iso.refl _, hT⟩⟩

end

variable [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]

include W in
/-
**CategoryTheory.Triangulated.Localization.isTriangulated** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Triangulated.Localization`。
形式化陈述：isTriangulated [Pretriangulated D] [L.IsTriangulated] [IsTriangulated C] :
 IsTriangulated D
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.essSurj_mapComposableArrows`：essSurj_mapComp
osableArrows [W.HasLeftCalculusOfFractions] (n : Nat) : (L.mapComposableArrows n
).EssSurj
· 使用引理 `CategoryTheory.isTriangulated_of_essSurj_mapComposableArrows_two`：isTria
ngulated_of_essSurj_mapComposableArrows_two (F : C ⥤ D) [F.CommShift Int] [F.IsT
riangulated] [(F.mapComposableArrows 2).EssSurj] [IsTr…
-/
lemma isTriangulated [Pretriangulated D] [L.IsTriangulated] [IsTriangulated C] :
    IsTriangulated D := by
  have := essSurj_mapComposableArrows L W 2
  exact isTriangulated_of_essSurj_mapComposableArrows_two L

variable [W.IsCompatibleWithTriangulation]
/-
**CategoryTheory.Triangulated.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Triangulated.Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (shiftFunctor (W.Localization) n).Additive := by
  rw [Localization.functor_additive_iff W.Q W]
  exact Functor.additive_of_iso (W.Q.commShiftIso n)
/-
**CategoryTheory.Triangulated.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Triangulated.Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Pretriangulated W.Localization := pretriangulated W.Q W
/-
**CategoryTheory.Triangulated.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Triangulated.Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTriangulated C] : IsTriangulated W.Localization := isTriangulated W.Q W

section

variable [W.HasLocalization]

/-
**CategoryTheory.Triangulated.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Triangulated.Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (shiftFunctor (W.Localization') n).Additive := by
  rw [Localization.functor_additive_iff W.Q' W]
  exact Functor.additive_of_iso (W.Q'.commShiftIso n)
/-
**CategoryTheory.Triangulated.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Triangulated.Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Pretriangulated W.Localization' := pretriangulated W.Q' W
/-
**CategoryTheory.Triangulated.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Triangulated.Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTriangulated C] : IsTriangulated W.Localization' := isTriangulated W.Q' W

end

end Localization

end Triangulated

namespace Functor

variable [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] [L.mapArrow.EssSurj] [L.IsTriangulated]

/-
**CategoryTheory.Functor.distTriang_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：distTriang_iff (T : Triangle D) : (T in distTriang D) ↔ T in L.essImageDis
tTriang
参数：T : Triangle D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.distinguished_cocone_triangle`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.H
asZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.Pretriangulated.exists_iso_of_arrow_iso`：exists_iso_of_ar
row_iso (T₁ T₂ : Triangle C) (hT₁ : T₁ in distTriang C) (hT₂ : T₂ in distTriang 
C) (e : Arrow.mk T₁.mor₁ ≅ Arrow.mk T₂.mor₁)…
· 使用引理 `CategoryTheory.Functor.map_distinguished`：map_distinguished [F.IsTriangu
lated] (T : Triangle C) (hT : T in distTriang C) : F.mapTriangle.obj T in distTr
iang D
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
-/
lemma distTriang_iff (T : Triangle D) :
    (T ∈ distTriang D) ↔ T ∈ L.essImageDistTriang := by
  constructor
  · intro hT
    let f := L.mapArrow.objPreimage T.mor₁
    obtain ⟨Z, g : f.right ⟶ Z, h : Z ⟶ f.left⟦(1 : ℤ)⟧, mem⟩ :=
      Pretriangulated.distinguished_cocone_triangle f.hom
    exact ⟨_, (exists_iso_of_arrow_iso T _ hT (L.map_distinguished _ mem)
      (L.mapArrow.objObjPreimageIso T.mor₁).symm).choose, mem⟩
  · rintro ⟨T₀, e, hT₀⟩
    exact isomorphic_distinguished _ (L.map_distinguished _ hT₀) _ e

end Functor

end CategoryTheory

