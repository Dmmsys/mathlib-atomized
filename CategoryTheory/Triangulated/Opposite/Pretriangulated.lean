/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangle
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# The pretriangulated structure on the opposite category

In this file, we construct the pretriangulated structure
on the opposite category `Cᵒᵖ` of a pretriangulated category `C`.

The shift on `Cᵒᵖ` was constructed in `Mathlib.CategoryTheory.Triangulated.Opposite.Basic`,
and is such that shifting by `n : ℤ` on `Cᵒᵖ` corresponds to the shift by
`-n` on `C`. In `Mathlib.CategoryTheory.Triangulated.Opposite.Triangle`, we constructed
an equivalence `(Triangle C)ᵒᵖ ≌ Triangle Cᵒᵖ`, called
`Mathlib.CategoryTheory.Pretriangulated.triangleOpEquivalence`.

Here, we defined the notion of distinguished triangles in `Cᵒᵖ`, such that
`triangleOpEquivalence` sends distinguished triangles in `C` to distinguished triangles
in `Cᵒᵖ`. In other words, if `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` is a distinguished triangle in `C`,
then the triangle `op Z ⟶ op Y ⟶ op X ⟶ (op Z)⟦1⟧` that is deduced *without introducing signs*
shall be a distinguished triangle in `Cᵒᵖ`. This is equivalent to the definition
in [Verdier's thesis, p. 96][verdier1996] which would require that the triangle
`(op X)⟦-1⟧ ⟶ op Z ⟶ op Y ⟶ op X` (without signs) is *antidistinguished*.

In the file `Mathlib.Triangulated.Opposite.Triangulated`, we show that `Cᵒᵖ` is
triangulated if `C` is triangulated.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

variable (C : Type*) [Category* C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Pretriangulated

open Pretriangulated.Opposite

namespace Opposite

/-- A triangle in `Cᵒᵖ` shall be distinguished iff it corresponds to a distinguished
triangle in `C` via the equivalence `triangleOpEquivalence C : (Triangle C)ᵒᵖ ≌ Triangle Cᵒᵖ`. -/
/-
**CategoryTheory.Pretriangulated.Opposite.distinguishedTriangles** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Pretriangulated.Opposite`。
形式化陈述：distinguishedTriangles : Set (Triangle Cᵒᵖ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A triangle in `Cᵒᵖ` shall be distinguished iff it corresponds to a distinguished
triangle in `C` via the equivalence `triangleOpEquivalence C : (Triangle C)ᵒᵖ ≌ 
Triangle Cᵒᵖ`.
-/
def distinguishedTriangles : Set (Triangle Cᵒᵖ) :=
  {T | ((triangleOpEquivalence C).inverse.obj T).unop ∈ distTriang C}

variable {C}
/-
**CategoryTheory.Pretriangulated.Opposite.mem_distinguishedTriangles_iff** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated.Opposite`。
形式化陈述：mem_distinguishedTriangles_iff (T : Triangle Cᵒᵖ) : T in distinguishedTria
ngles C ↔ ((triangleOpEquivalence C).inverse.obj T).unop in distTriang C
参数：T : Triangle Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_distinguishedTriangles_iff (T : Triangle Cᵒᵖ) :
    T ∈ distinguishedTriangles C ↔
      ((triangleOpEquivalence C).inverse.obj T).unop ∈ distTriang C := by
  rfl
/-
**CategoryTheory.Pretriangulated.Opposite.mem_distinguishedTriangles_iff'** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated.Opposite`。
形式化陈述：mem_distinguishedTriangles_iff' (T : Triangle Cᵒᵖ) : T in distinguishedTri
angles C ↔ exists (T' : Triangle C) (_ : T' in distTriang C), Nonempty (T ≅ (tri
angleOpEquivalence C).functor.obj (Opposite.op T'))
参数：T : Triangle Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pretriangulated.Opposite.mem_distinguishedTriangles_iff`：
mem_distinguishedTriangles_iff (T : Triangle Cᵒᵖ) : T in distinguishedTriangles 
C ↔ ((triangleOpEquivalence C).inverse.obj T).unop in distTr…
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
-/
lemma mem_distinguishedTriangles_iff' (T : Triangle Cᵒᵖ) :
    T ∈ distinguishedTriangles C ↔
      ∃ (T' : Triangle C) (_ : T' ∈ distTriang C),
        Nonempty (T ≅ (triangleOpEquivalence C).functor.obj (Opposite.op T')) := by
  rw [mem_distinguishedTriangles_iff]
  constructor
  · intro hT
    exact ⟨_, hT, ⟨(triangleOpEquivalence C).counitIso.symm.app T⟩⟩
  · rintro ⟨T', hT', ⟨e⟩⟩
    refine isomorphic_distinguished _ hT' _ ?_
    exact Iso.unop ((triangleOpEquivalence C).unitIso.app (Opposite.op T') ≪≫
      (triangleOpEquivalence C).inverse.mapIso e.symm)
/-
**CategoryTheory.Pretriangulated.Opposite.isomorphic_distinguished** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Pretriangulated.Opposite`。
形式化陈述：isomorphic_distinguished (T₁ : Triangle Cᵒᵖ) (hT₁ : T₁ in distinguishedTri
angles C) (T₂ : Triangle Cᵒᵖ) (e : T₂ ≅ T₁) : T₂ in distinguishedTriangles C
参数：T₁ : Triangle Cᵒᵖ；hT₁ : T₁ in distinguishedTriangles C；T₂ : Triangle Cᵒᵖ；e : 
T₂ ≅ T₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
-/
lemma isomorphic_distinguished (T₁ : Triangle Cᵒᵖ)
    (hT₁ : T₁ ∈ distinguishedTriangles C) (T₂ : Triangle Cᵒᵖ) (e : T₂ ≅ T₁) :
    T₂ ∈ distinguishedTriangles C := by
  simp only [mem_distinguishedTriangles_iff] at hT₁ ⊢
  exact Pretriangulated.isomorphic_distinguished _ hT₁ _
    ((triangleOpEquivalence C).inverse.mapIso e).unop.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Up to rotation, the contractible triangle `X ⟶ X ⟶ 0 ⟶ X⟦1⟧` for `X : Cᵒᵖ` corresponds
to the contractible triangle for `X.unop` in `C`. -/
@[simps!]
/-
**CategoryTheory.Pretriangulated.Opposite.contractibleTriangleIso** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Pretriangulated.Opposite`。
形式化陈述：contractibleTriangleIso (X : Cᵒᵖ) : contractibleTriangle X ≅ (triangleOpEq
uivalence C).functor.obj (Opposite.op (contractibleTriangle X.unop).invRotate)
参数：X : Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Up to rotation, the contractible triangle `X ⟶ X ⟶ 0 ⟶ X⟦1⟧` for `X : Cᵒᵖ` corre
sponds
to the contractible triangle for `X.unop` in `C`.
-/
noncomputable def contractibleTriangleIso (X : Cᵒᵖ) :
    contractibleTriangle X ≅ (triangleOpEquivalence C).functor.obj
      (Opposite.op (contractibleTriangle X.unop).invRotate) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (IsZero.iso (isZero_zero _) (by
      dsimp
      rw [IsZero.iff_id_eq_zero]
      change (𝟙 ((0 : C)⟦(-1 : ℤ)⟧)).op = 0
      rw [← Functor.map_id, id_zero, Functor.map_zero, op_zero]))
    (by simp) (by simp) (by simp)
/-
**CategoryTheory.Pretriangulated.Opposite.contractible_distinguished** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated.Opposite`。
形式化陈述：contractible_distinguished (X : Cᵒᵖ) : contractibleTriangle X in distingui
shedTriangles C
参数：X : Cᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pretriangulated.Opposite.mem_distinguishedTriangles_iff'`
：mem_distinguishedTriangles_iff' (T : Triangle Cᵒᵖ) : T in distinguishedTriangle
s C ↔ exists (T' : Triangle C) (_ : T' in distTriang C), None…
· 使用定理 `CategoryTheory.Pretriangulated.inv_rot_of_distTriang`：inv_rot_of_distTri
ang (T : Triangle C) (H : T in distTriang C) : T.invRotate in distTriang C
· 使用定理 `CategoryTheory.Pretriangulated.contractible_distinguished`：∀ {C : Type u
} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZ
eroObject C}   {inst_2 : CategoryTheory.HasShif…
-/
lemma contractible_distinguished (X : Cᵒᵖ) :
    contractibleTriangle X ∈ distinguishedTriangles C := by
  rw [mem_distinguishedTriangles_iff']
  exact ⟨_, inv_rot_of_distTriang _ (Pretriangulated.contractible_distinguished X.unop),
    ⟨contractibleTriangleIso X⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Isomorphism expressing a compatibility of the equivalence `triangleOpEquivalence C`
with the rotation of triangles. -/
/-
**CategoryTheory.Pretriangulated.Opposite.rotateTriangleOpEquivalenceInverseObjR
otateUnopIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pretriangulated.Opposite`
。
形式化陈述：rotateTriangleOpEquivalenceInverseObjRotateUnopIso (T : Triangle Cᵒᵖ) : ((
triangleOpEquivalence C).inverse.obj T.rotate).unop.rotate ≅ ((triangleOpEquival
ence C).inverse.obj T).unop
参数：T : Triangle Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphism expressing a compatibility of the equivalence `triangleOpEquivalence
 C`
with the rotation of triangles.
-/
noncomputable def rotateTriangleOpEquivalenceInverseObjRotateUnopIso (T : Triangle Cᵒᵖ) :
    ((triangleOpEquivalence C).inverse.obj T.rotate).unop.rotate ≅
      ((triangleOpEquivalence C).inverse.obj T).unop :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (-((opShiftFunctorEquivalence C 1).unitIso.app T.obj₁).unop) (by simp)
        (Quiver.Hom.op_inj (by simp)) (by simp)
/-
**CategoryTheory.Pretriangulated.Opposite.rotate_distinguished_triangle** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated.Opposite`。
形式化陈述：rotate_distinguished_triangle (T : Triangle Cᵒᵖ) : T in distinguishedTrian
gles C ↔ T.rotate in distinguishedTriangles C
参数：T : Triangle Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Pretriangulated.rotate_distinguished_triangle`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.H
asZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.Pretriangulated.distinguished_iff_of_iso`：distinguished_i
ff_of_iso {T₁ T₂ : Triangle C} (e : T₁ ≅ T₂) : T₁ in distTriang C ↔ T₂ in distTr
iang C
-/
lemma rotate_distinguished_triangle (T : Triangle Cᵒᵖ) :
    T ∈ distinguishedTriangles C ↔ T.rotate ∈ distinguishedTriangles C := by
  simp only [mem_distinguishedTriangles_iff, Pretriangulated.rotate_distinguished_triangle
    ((triangleOpEquivalence C).inverse.obj (T.rotate)).unop]
  exact distinguished_iff_of_iso (rotateTriangleOpEquivalenceInverseObjRotateUnopIso T).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Pretriangulated.Opposite.distinguished_cocone_triangle** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated.Opposite`。
形式化陈述：distinguished_cocone_triangle {X Y : Cᵒᵖ} (f : X ⟶ Y) : exists (Z : Cᵒᵖ) (
g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : Int)⟧), Triangle.mk f g h in distinguishedTriangles C
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pretriangulated.distinguished_cocone_triangle₁`：distingui
shed_cocone_triangle₁ {Y Z : C} (g : Y ⟶ Z) : exists (X : C) (f : X ⟶ Y) (h : Z 
⟶ X⟦(1 : Int)⟧), Triangle.mk f g h in distTriang C
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
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
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Pretriangulated.shift_unop_opShiftFunctorEquivalence_coun
itIso_inv_app`：shift_unop_opShiftFunctorEquivalence_counitIso_inv_app (X : Cᵒᵖ) 
(n : Int) : ((opShiftFunctorEquivalence C n).counitIso.inv.app X).unop⟦n⟧' …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_unitIso_inv_nat
urality`：opShiftFunctorEquivalence_unitIso_inv_naturality (n : Int) {X Y : Cᵒᵖ} 
(f : X ⟶ Y) : (f⟦n⟧').unop⟦n⟧'.op ≫ (opShiftFunctorEquivalence C n).u…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
-/
lemma distinguished_cocone_triangle {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ∃ (Z : Cᵒᵖ) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles C := by
  obtain ⟨Z, g, h, H⟩ := Pretriangulated.distinguished_cocone_triangle₁ f.unop
  refine ⟨_, g.op, (opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op Z) ≫
    (shiftFunctor Cᵒᵖ (1 : ℤ)).map h.op, ?_⟩
  simp only [mem_distinguishedTriangles_iff]
  refine Pretriangulated.isomorphic_distinguished _ H _ ?_
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    (Quiver.Hom.op_inj (by simp [shift_unop_opShiftFunctorEquivalence_counitIso_inv_app]))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Pretriangulated.Opposite.complete_distinguished_triangle_morphi
sm** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated.Opposite`。
形式化陈述：complete_distinguished_triangle_morphism (T₁ T₂ : Triangle Cᵒᵖ) (hT₁ : T₁ 
in distinguishedTriangles C) (hT₂ : T₂ in distinguishedTriangles C) (a : T₁.obj₁
 ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) : exists 
(c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mo
r₃
参数：T₁ T₂ : Triangle Cᵒᵖ；hT₁ : T₁ in distinguishedTriangles C；hT₂ : T₂ in disting
uishedTriangles C；a : T₁.obj₁ ⟶ T₂.obj₁；b : T₁.obj₂ ⟶ T₂.obj₂；comm : T₁.mor₁ ≫ b
 = a ≫ T₂.mor₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism₁
`：complete_distinguished_triangle_morphism₁ (T₁ T₂ : Triangle C) (hT₁ : T₁ in di
stTriang C) (hT₂ : T₂ in distTriang C) (b : T₁.obj₂ ⟶ T₂.obj₂)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pretriangulated.Opposite.mem_distinguishedTriangles_iff`：
mem_distinguishedTriangles_iff (T : Triangle Cᵒᵖ) : T in distinguishedTriangles 
C ↔ ((triangleOpEquivalence C).inverse.obj T).unop in distTr…
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instIsEquivalenceShiftFunctor`：∀ (C : Type u) {A : Type u
_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddGroup A]   [inst_2 : 
CategoryTheory.HasShift C A] (i : …
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Quiver.Hom.unop_op`：Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop
 = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.unop_hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u_1}   [inst_1 : CategoryTheory.Cate
gory.{v_1, u_1} D] {F G : Category…
· 使用定理 `CategoryTheory.unop_comp_assoc`：unop_comp_assoc {X Y Z : Cᵒᵖ} {f : X ⟶ Y
} {g : Y ⟶ Z} {Z' : C} {h : unop X ⟶ Z'} : (f ≫ g).unop ≫ h = g.unop ≫ f.unop ≫ 
h
· 使用引理 `CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_unitIso_inv_nat
urality`：opShiftFunctorEquivalence_unitIso_inv_naturality (n : Int) {X Y : Cᵒᵖ} 
(f : X ⟶ Y) : (f⟦n⟧').unop⟦n⟧'.op ≫ (opShiftFunctorEquivalence C n).u…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_unitIso_hom_nat
urality`：opShiftFunctorEquivalence_unitIso_hom_naturality (n : Int) {X Y : Cᵒᵖ} 
(f : X ⟶ Y) : f ≫ (opShiftFunctorEquivalence C n).unitIso.hom.app Y =…
· 使用定理 `CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_unitIso_inv_nat
urality_assoc`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [i
nst_1 : CategoryTheory.HasShift C ℤ] (n : ℤ)   {X Y : Cᵒᵖ} (f : X ⟶ Y) {Z :…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma complete_distinguished_triangle_morphism (T₁ T₂ : Triangle Cᵒᵖ)
    (hT₁ : T₁ ∈ distinguishedTriangles C) (hT₂ : T₂ ∈ distinguishedTriangles C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  rw [mem_distinguishedTriangles_iff] at hT₁ hT₂
  obtain ⟨c, hc₁, hc₂⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism₁ _ _ hT₂ hT₁
      b.unop a.unop (Quiver.Hom.op_inj comm.symm)
  dsimp at c hc₁ hc₂
  replace hc₂ := ((opShiftFunctorEquivalence C 1).unitIso.hom.app T₂.obj₁).unop ≫= hc₂
  dsimp at hc₂
  simp only [assoc, Iso.unop_hom_inv_id_app_assoc] at hc₂
  refine ⟨c.op, Quiver.Hom.unop_inj hc₁.symm, Quiver.Hom.unop_inj ?_⟩
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [unop_comp, unop_comp, Functor.map_comp, Functor.map_comp,
    Quiver.Hom.unop_op, hc₂, ← unop_comp_assoc, ← unop_comp_assoc,
    ← opShiftFunctorEquivalence_unitIso_inv_naturality]
  simp

/-- The pretriangulated structure on the opposite category of
a pretriangulated category. It is a scoped instance, so that we need to
`open CategoryTheory.Pretriangulated.Opposite` in order to be able
to use it: the reason is that it relies on the definition of the shift
on the opposite category `Cᵒᵖ`, for which it is unclear whether it should
be a global instance or not. -/
/-
**CategoryTheory.Pretriangulated.Opposite.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Opposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pretriangulated structure on the opposite category of
a pretriangulated category. It is a scoped instance, so that we need to
`open CategoryTheory.Pretriangulated.Opposite` in order to be able
to use it: the reason is that it relies on the definition of the shift
on the opposite category `Cᵒᵖ`, for which it is unclear whether it should
be a global instance or not.
-/
noncomputable scoped instance : Pretriangulated Cᵒᵖ where
  distinguishedTriangles := distinguishedTriangles C
  isomorphic_distinguished := isomorphic_distinguished
  contractible_distinguished := contractible_distinguished
  distinguished_cocone_triangle := distinguished_cocone_triangle
  rotate_distinguished_triangle := rotate_distinguished_triangle
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism

end Opposite

variable {C}

/-
**CategoryTheory.Pretriangulated.mem_distTriang_op_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Pretriangulated`。
形式化陈述：mem_distTriang_op_iff (T : Triangle Cᵒᵖ) : (T in distTriang Cᵒᵖ) ↔ ((trian
gleOpEquivalence C).inverse.obj T).unop in distTriang C
参数：T : Triangle Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.instAdditiveOppositeShiftFunctor
Int`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Preadditive…
-/
lemma mem_distTriang_op_iff (T : Triangle Cᵒᵖ) :
    (T ∈ distTriang Cᵒᵖ) ↔ ((triangleOpEquivalence C).inverse.obj T).unop ∈ distTriang C := by
  rfl
/-
**CategoryTheory.Pretriangulated.mem_distTriang_op_iff'** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Pretriangulated`。
形式化陈述：mem_distTriang_op_iff' (T : Triangle Cᵒᵖ) : (T in distTriang Cᵒᵖ) ↔ exists
 (T' : Triangle C) (_ : T' in distTriang C), Nonempty (T ≅ (triangleOpEquivalenc
e C).functor.obj (Opposite.op T'))
参数：T : Triangle Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pretriangulated.Opposite.mem_distinguishedTriangles_iff'`
：mem_distinguishedTriangles_iff' (T : Triangle Cᵒᵖ) : T in distinguishedTriangle
s C ↔ exists (T' : Triangle C) (_ : T' in distTriang C), None…
-/
lemma mem_distTriang_op_iff' (T : Triangle Cᵒᵖ) :
    (T ∈ distTriang Cᵒᵖ) ↔ ∃ (T' : Triangle C) (_ : T' ∈ distTriang C),
      Nonempty (T ≅ (triangleOpEquivalence C).functor.obj (Opposite.op T')) :=
  Opposite.mem_distinguishedTriangles_iff' T
/-
**CategoryTheory.Pretriangulated.op_distinguished** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Pretriangulated`。
形式化陈述：op_distinguished (T : Triangle C) (hT : T in distTriang C) : ((triangleOpE
quivalence C).functor.obj (Opposite.op T)) in distTriang Cᵒᵖ
参数：T : Triangle C；hT : T in distTriang C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.instAdditiveOppositeShiftFunctor
Int`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Preadditive…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pretriangulated.mem_distTriang_op_iff'`：mem_distTriang_op
_iff' (T : Triangle Cᵒᵖ) : (T in distTriang Cᵒᵖ) ↔ exists (T' : Triangle C) (_ :
 T' in distTriang C), Nonempty (T ≅ (triang…
-/
lemma op_distinguished (T : Triangle C) (hT : T ∈ distTriang C) :
    ((triangleOpEquivalence C).functor.obj (Opposite.op T)) ∈ distTriang Cᵒᵖ := by
  rw [mem_distTriang_op_iff']
  exact ⟨T, hT, ⟨Iso.refl _⟩⟩
/-
**CategoryTheory.Pretriangulated.unop_distinguished** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Pretriangulated`。
形式化陈述：unop_distinguished (T : Triangle Cᵒᵖ) (hT : T in distTriang Cᵒᵖ) : ((trian
gleOpEquivalence C).inverse.obj T).unop in distTriang C
参数：T : Triangle Cᵒᵖ；hT : T in distTriang Cᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.instAdditiveOppositeShiftFunctor
Int`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Preadditive…
-/
lemma unop_distinguished (T : Triangle Cᵒᵖ) (hT : T ∈ distTriang Cᵒᵖ) :
    ((triangleOpEquivalence C).inverse.obj T).unop ∈ distTriang C := hT

end Pretriangulated

namespace Functor

open Pretriangulated.Opposite Pretriangulated

variable {C}

/-
**CategoryTheory.Functor.map_distinguished_op_exact** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：map_distinguished_op_exact {A : Type*} [Category* A] [Abelian A] (F : Cᵒᵖ 
⥤ A) [F.IsHomological] (T : Triangle C) (hT : T in distTriang C) : ((shortComple
xOfDistTriangle T hT).op.map F).Exact
参数：F : Cᵒᵖ ⥤ A；T : Triangle C；hT : T in distTriang C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.instAdditiveOppositeShiftFunctor
Int`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Preadditive…
· 使用引理 `CategoryTheory.Functor.map_distinguished_exact`：map_distinguished_exact 
[F.IsHomological] (T : Triangle C) (hT : T in distTriang C) : ((shortComplexOfDi
stTriangle T hT).map F).Exact
· 使用引理 `CategoryTheory.Pretriangulated.op_distinguished`：op_distinguished (T : T
riangle C) (hT : T in distTriang C) : ((triangleOpEquivalence C).functor.obj (Op
posite.op T)) in distTriang Cᵒᵖ
-/
lemma map_distinguished_op_exact {A : Type*} [Category* A] [Abelian A] (F : Cᵒᵖ ⥤ A)
    [F.IsHomological] (T : Triangle C) (hT : T ∈ distTriang C) :
    ((shortComplexOfDistTriangle T hT).op.map F).Exact :=
  F.map_distinguished_exact _ (op_distinguished T hT)

end Functor

end CategoryTheory

