/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-!
# Action of the flip of a bifunctor on homological complexes

Given `K₁ : HomologicalComplex C₁ c₁`, `K₂ : HomologicalComplex C₂ c₂`,
a bifunctor `F : C₁ ⥤ C₂ ⥤ D`, and a complex shape `c` with
`[TotalComplexShape c₁ c₂ c]` and `[TotalComplexShape c₂ c₁ c]`, we define
an isomorphism `mapBifunctor K₂ K₁ F.flip c ≅ mapBifunctor K₁ K₂ F c`
under the additional assumption `[TotalComplexShapeSymmetry c₁ c₂ c]`.

-/

@[expose] public section

open CategoryTheory Limits

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

namespace HomologicalComplex

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (φ₁ : K₁ ⟶ L₁)
  (K₂ L₂ : HomologicalComplex C₂ c₂) (φ₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
  [TotalComplexShapeSymmetry c₁ c₂ c]

/-
**HomologicalComplex.hasMapBifunctor_flip_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homolog
icalComplex`。
形式化陈述：hasMapBifunctor_flip_iff : HasMapBifunctor K₂ K₁ F.flip c ↔ HasMapBifuncto
r K₁ K₂ F c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex₂.flip_hasTotal_iff`：flip_hasTotal_iff : K.flip.HasTot
al c ↔ K.HasTotal c
-/
lemma hasMapBifunctor_flip_iff :
    HasMapBifunctor K₂ K₁ F.flip c ↔ HasMapBifunctor K₁ K₂ F c :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).flip_hasTotal_iff c

variable [DecidableEq J] [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasMapBifunctor K₂ K₁ F.flip c := by
  rw [hasMapBifunctor_flip_iff]
  infer_instance

/-- The canonical isomorphism `mapBifunctor K₂ K₁ F.flip c ≅ mapBifunctor K₁ K₂ F c`. -/
/-
**HomologicalComplex.mapBifunctorFlipIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalC
omplex`。
形式化陈述：mapBifunctorFlipIso : mapBifunctor K₂ K₁ F.flip c ≅ mapBifunctor K₁ K₂ F c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `mapBifunctor K₂ K₁ F.flip c ≅ mapBifunctor K₁ K₂ F c`
.
-/
noncomputable def mapBifunctorFlipIso :
    mapBifunctor K₂ K₁ F.flip c ≅ mapBifunctor K₁ K₂ F c :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).totalFlipIso c

@[reassoc (attr := simp)]
/-
**HomologicalComplex.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_mapBifunctorFlipIso_hom (i₁ : I₁) (i₂ : I₂) (j : J) (hj : c₂.π c₁ c (i₂, i₁) = j) :
    ιMapBifunctor K₂ K₁ F.flip c i₂ i₁ j hj ≫ (mapBifunctorFlipIso K₁ K₂ F c).hom.f j =
      c₁.σ c₂ c i₁ i₂ • ιMapBifunctor K₁ K₂ F c i₁ i₂ j
        (by rw [← ComplexShape.π_symm c₁ c₂ c i₁ i₂, hj]) :=
  HomologicalComplex₂.ιTotal_totalFlipIso_f_hom
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂) c i₁ i₂ j hj

@[reassoc (attr := simp)]
/-
**HomologicalComplex.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_mapBifunctorFlipIso_inv (i₁ : I₁) (i₂ : I₂) (j : J) (hj : c₁.π c₂ c (i₁, i₂) = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j hj ≫ (mapBifunctorFlipIso K₁ K₂ F c).inv.f j =
      c₁.σ c₂ c i₁ i₂ • ιMapBifunctor K₂ K₁ F.flip c i₂ i₁ j
        (by rw [ComplexShape.π_symm c₁ c₂ c i₁ i₂, hj]) :=
  HomologicalComplex₂.ιTotal_totalFlipIso_f_inv
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂) c i₁ i₂ j hj
/-
**HomologicalComplex.mapBifunctorFlipIso_flip** 是 Mathlib 中的一个引理，位于命名空间 `Homolog
icalComplex`。
形式化陈述：mapBifunctorFlipIso_flip [TotalComplexShapeSymmetry c₂ c₁ c] [TotalComplex
ShapeSymmetrySymmetry c₁ c₂ c] : mapBifunctorFlipIso K₂ K₁ F.flip c = (mapBifunc
torFlipIso K₁ K₂ F c).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex₂.flip_totalFlipIso`：flip_totalFlipIso : K.flip.totalF
lipIso c = (K.totalFlipIso c).symm
-/
lemma mapBifunctorFlipIso_flip
    [TotalComplexShapeSymmetry c₂ c₁ c] [TotalComplexShapeSymmetrySymmetry c₁ c₂ c] :
    mapBifunctorFlipIso K₂ K₁ F.flip c = (mapBifunctorFlipIso K₁ K₂ F c).symm :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).flip_totalFlipIso c

set_option backward.isDefEq.respectTransparency false in
variable {K₁ K₂ L₁ L₂} in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.mapBifunctorFlipIso_hom_naturality** 是 Mathlib 中的一个引理，位于命名空
间 `HomologicalComplex`。
形式化陈述：mapBifunctorFlipIso_hom_naturality : mapBifunctorMap φ₂ φ₁ F.flip c ≫ (map
BifunctorFlipIso L₁ L₂ F c).hom = (mapBifunctorFlipIso K₁ K₂ F c).hom ≫ mapBifun
ctorMap φ₁ φ₂ F c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `CategoryTheory.Functor.instPreservesZeroMorphismsFlipOfObj`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.instPreservesZeroMorphismsObjFlip`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `HomologicalComplex.instHasMapBifunctorFlip`：∀ {C₁ : Type u_1} {C₂ : Type
 u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : 
CategoryTheory.Category.{v_2, u_…
· 使用引理 `HomologicalComplex.mapBifunctor.hom_ext`：hom_ext {Y : D} {j : J} {f g : 
(mapBifunctor K₁ K₂ F c).X j ⟶ Y} (h : forall (i₁ : I₁) (i₂ : I₂) (h : ComplexSh
ape.π c₁ c₂ c ⟨i₁, i₂⟩ = j), …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.ι_mapBifunctorMap_assoc`：∀ {C₁ : Type u_1} {C₂ : Type
 u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : 
CategoryTheory.Category.{v_2, u_…
· 使用引理 `HomologicalComplex.ι_mapBifunctorFlipIso_hom`：ι_mapBifunctorFlipIso_hom 
(i₁ : I₁) (i₂ : I₂) (j : J) (hj : c₂.π c₁ c (i₂, i₁) = j) : ιMapBifunctor K₂ K₁ 
F.flip c i₂ i₁ j hj ≫ (mapBifuncto…
· 使用引理 `CategoryTheory.Linear.comp_units_smul`：comp_units_smul {X Y Z : C} (f : 
X ⟶ Y) (r : Rˣ) (g : Y ⟶ Z) : f ≫ (r • g) = r • f ≫ g
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `HomologicalComplex.ι_mapBifunctorFlipIso_hom_assoc`：∀ {C₁ : Type u_1} {C
₂ : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [i
nst_1 : CategoryTheory.Category.{v_2, u_…
· 使用引理 `CategoryTheory.Linear.units_smul_comp`：units_smul_comp {X Y Z : C} (r : 
Rˣ) (f : X ⟶ Y) (g : Y ⟶ Z) : (r • f) ≫ g = r • f ≫ g
· 使用引理 `HomologicalComplex.ι_mapBifunctorMap`：ι_mapBifunctorMap (i₁ : I₁) (i₂ : 
I₂) (j : J) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) : ιMapBifunctor K₁ K₂ F c 
i₁ i₂ j h ≫ (mapBifunctorM…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapBifunctorFlipIso_hom_naturality :
      mapBifunctorMap φ₂ φ₁ F.flip c ≫ (mapBifunctorFlipIso L₁ L₂ F c).hom =
    (mapBifunctorFlipIso K₁ K₂ F c).hom ≫ mapBifunctorMap φ₁ φ₂ F c := by
  cat_disch

end HomologicalComplex

