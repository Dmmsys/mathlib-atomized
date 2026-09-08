/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Local

/-!
# Orthogonal of triangulated subcategories

Let `P` be a triangulated subcategory of a pretriangulated category `C`. We show
that `P.rightOrthogonal` (which consists of objects `Y` with no nonzero
map `X ⟶ Y` with `X` satisfying `P`) is a triangulated subcategory. The dual result
for `P.leftOrthogonal` is also obtained.

-/

public section

universe v v' u u'

namespace CategoryTheory

open Limits Pretriangulated

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (P : ObjectProperty C)

section

variable {M : Type*} [AddGroup M] [HasShift C M] [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsStableUnderShift M] : P.rightOrthogonal.IsStableUnderShift M where
  isStableUnderShiftBy n := ⟨fun Y hY X f hX ↦ by
    obtain ⟨g, rfl⟩ := ((shiftEquiv C n).symm.toAdjunction.homEquiv _ _).surjective f
    simp [hY g (P.le_shift (-n) _ hX), Adjunction.homEquiv_unit]⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsStableUnderShift M] : P.leftOrthogonal.IsStableUnderShift M where
  isStableUnderShiftBy n := ⟨fun X hX Y f hY ↦ by
    obtain ⟨g, rfl⟩ := ((shiftEquiv C n).toAdjunction.homEquiv _ _).symm.surjective f
    simp [hX g (P.le_shift (-n) _ hY), Adjunction.homEquiv_counit]⟩

end

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.rightOrthogonal.IsTriangulatedClosed₂ :=
  .mk' (fun T hT h₁ h₃ X f hX ↦ by
    obtain ⟨g, rfl⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hT f (h₃ _ hX)
    simp [h₁ g hX])
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.leftOrthogonal.IsTriangulatedClosed₂ :=
  .mk' (fun T hT h₁ h₃ Y f hY ↦ by
    obtain ⟨g, rfl⟩ := Pretriangulated.Triangle.yoneda_exact₂ T hT f (h₁ _ hY)
    simp [h₃ g hY])
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsStableUnderShift ℤ] : P.rightOrthogonal.IsTriangulated where
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsStableUnderShift ℤ] : P.leftOrthogonal.IsTriangulated where
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [P.IsTriangulated] : P.rightOrthogonal.IsTriangulated := inferInstance
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [P.IsTriangulated] : P.leftOrthogonal.IsTriangulated := inferInstance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.isLocal_trW** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：isLocal_trW [P.IsTriangulated] : P.trW.isLocal = P.rightOrthogonal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `CategoryTheory.ObjectProperty.trW.mk`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C]   
[inst_2 : CategoryTheory.H…
· 使用引理 `CategoryTheory.Pretriangulated.contractible_distinguished₁`：contractible
_distinguished₁ (X : C) : Triangle.mk (0 : 0 ⟶ X) (𝟙 X) 0 in distTriang C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Pretriangulated.Triangle.mk_mor₁`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ] {X Y Z 
: C} (f : X ⟶ Y)   (g : Y ⟶ Z) (h : Z…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂`：yoneda_exact₂ {X 
: C} (f : T.obj₂ ⟶ X) (hf : T.mor₁ ≫ f = 0) : exists (g : T.obj₃ ⟶ X), f = T.mor
₂ ≫ g
· 使用定理 `CategoryTheory.Pretriangulated.Triangle.mk_mor₂`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ] {X Y Z 
: C} (f : X ⟶ Y)   (g : Y ⟶ Z) (h : Z…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `CategoryTheory.Pretriangulated.inv_rot_of_distTriang`：inv_rot_of_distTri
ang (T : Triangle C) (H : T in distTriang C) : T.invRotate in distTriang C
· 使用引理 `CategoryTheory.ObjectProperty.le_shift`：le_shift (a : A) [P.IsStableUnde
rShiftBy a] : P <= P.shift a
· 使用定理 `CategoryTheory.ObjectProperty.IsStableUnderShift.isStableUnderShiftBy`：∀
 {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P : CategoryTheor
y.ObjectProperty C} {A : Type u_2}   {inst_1 : AddMonoid A}…
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…
-/
lemma isLocal_trW [P.IsTriangulated] :
    P.trW.isLocal = P.rightOrthogonal := by
  ext Y
  refine ⟨fun hY X f hX ↦ ?_, fun hY X₁ X₂ f ⟨X₃, g, h, hT, hX₃⟩ ↦ ⟨?_, fun α ↦ ?_⟩⟩
  · exact (hY _ (trW.mk P (contractible_distinguished₁ X) hX)).injective (by simp)
  · suffices ∀ (α : X₂ ⟶ Y), f ≫ α = 0 → α = 0 from fun α₁ α₂ hα ↦ by
      simpa [sub_eq_zero] using this (α₁ - α₂) (by simpa [sub_eq_zero] using hα)
    intro α hα
    obtain ⟨β, rfl⟩ := Triangle.yoneda_exact₂ _ hT α hα
    simp [hY β hX₃]
  · obtain ⟨β, rfl⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT)
      α (hY _ (P.le_shift _ _ hX₃))
    exact ⟨β, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.isColocal_trW** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：isColocal_trW [P.IsTriangulated] : P.trW.isColocal = P.leftOrthogonal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `CategoryTheory.ObjectProperty.trW.mk`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C]   
[inst_2 : CategoryTheory.H…
· 使用引理 `CategoryTheory.Pretriangulated.contractible_distinguished₂`：contractible
_distinguished₂ (X : C) : Triangle.mk (0 : X ⟶ 0) 0 (𝟙 (X⟦1⟧)) in distTriang C
· 使用引理 `CategoryTheory.ObjectProperty.le_shift`：le_shift (a : A) [P.IsStableUnde
rShiftBy a] : P <= P.shift a
· 使用定理 `CategoryTheory.ObjectProperty.IsStableUnderShift.isStableUnderShiftBy`：∀
 {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P : CategoryTheor
y.ObjectProperty C} {A : Type u_2}   {inst_1 : AddMonoid A}…
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pretriangulated.Triangle.mk_mor₁`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ] {X Y Z 
: C} (f : X ⟶ Y)   (g : Y ⟶ Z) (h : Z…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ObjectProperty.trW_iff'`：trW_iff' [P.IsStableUnderShift I
nt] {Y Z : C} (g : Y ⟶ Z) : P.trW g ↔ exists (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 :
 Int)⟧) (_ : Triangle.mk f g…
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂`：coyoneda_exact₂
 {X : C} (f : X ⟶ T.obj₂) (hf : f ≫ T.mor₂ = 0) : exists (g : X ⟶ T.obj₁), f = g
 ≫ T.mor₁
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `CategoryTheory.Pretriangulated.rot_of_distTriang`：rot_of_distTriang (T :
 Triangle C) (H : T in distTriang C) : T.rotate in distTriang C
-/
lemma isColocal_trW [P.IsTriangulated] :
    P.trW.isColocal = P.leftOrthogonal := by
  ext X
  refine ⟨fun hX Y f hY ↦ ?_, fun hX Y₂ Y₃ h hh ↦ ?_⟩
  · exact (hX _ (trW.mk P (contractible_distinguished₂ Y) (P.le_shift _ _ hY))).injective (by simp)
  · rw [trW_iff'] at hh
    obtain ⟨Y₁, f, g, hT, hY₁⟩ := hh
    refine ⟨?_, fun α ↦ ?_⟩
    · suffices ∀ (α : X ⟶ Y₂), α ≫ h = 0 → α = 0 from fun α₁ α₂ hα ↦ by
        simpa [sub_eq_zero] using this (α₁ - α₂) (by simpa [sub_eq_zero])
      intro α hα
      obtain ⟨β, rfl⟩ := Triangle.coyoneda_exact₂ _ hT α hα
      simp [hX β hY₁]
    · obtain ⟨β, rfl⟩ := Triangle.coyoneda_exact₂ _ (rot_of_distTriang _ hT)
        α (hX _ (P.le_shift _ _ hY₁))
      exact ⟨β, rfl⟩

variable {P} in
/-
**CategoryTheory.ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.rightOrthogonal`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {P : CategoryTheory.ObjectProperty 
C} [inst_2 : CategoryTheory.Limits.HasZeroObject C]   [inst_3 : CategoryTheory.H
asShift C ℤ] [inst_4 : CategoryTheory.Preadditive C]   [inst_5 : ∀ (n : ℤ), (Cat
egoryTheory.shiftFunctor C n).Additive] [inst_6 : CategoryTheory.Pretriangulated
 C]   [P.IsTriangulated] [CategoryTheory.IsTriangulated C] {Y : C},   P.rightOrt
hogonal Y → ∀ (L : CategoryTheory.Functor C D) [L.IsLocalization P.trW] (X : C),
 Function.Bijective L.map
参数：n : ℤ；CategoryTheory.shiftFunctor C n；L : CategoryTheory.Functor C D；X : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.map_eq_iff_precomp`：∀ {C : Type u_1} {D 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.ObjectProperty.instHasRightCalculusOfFractionsTrWOfIsTria
ngulatedOfIsTriangulated`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1,
 u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C]   [inst_2 : CategoryTh
eory.H…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.isLocal_trW`：isLocal_trW [P.IsTriangulated
] : P.trW.isLocal = P.rightOrthogonal
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Localization.exists_rightFraction`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.RightFraction X…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.instIsIsoMapSOfIsLocalizat
ion`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} 
C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {W : Categor…
· 使用引理 `CategoryTheory.MorphismProperty.RightFraction.map_s_comp_map`：map_s_comp
_map (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : L.map φ.s ≫
 φ.map L hL = L.map φ.f
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma rightOrthogonal.map_bijective_of_isTriangulated
    [P.IsTriangulated] [IsTriangulated C] {Y : C} (hY : P.rightOrthogonal Y)
    (L : C ⥤ D) [L.IsLocalization P.trW] (X : C) :
    Function.Bijective (L.map : (X ⟶ Y) → _) := by
  rw [← isLocal_trW] at hY
  refine ⟨fun f₁ f₂ hf ↦ ?_, fun g ↦ ?_⟩
  · rw [MorphismProperty.map_eq_iff_precomp L P.trW] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    exact (hY _ hs).1 eq
  · obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.trW g
    obtain ⟨α, hα⟩ := (hY _ φ.hs).2 φ.f
    refine ⟨α, ?_⟩
    rw [hφ, ← cancel_epi (L.map φ.s), MorphismProperty.RightFraction.map_s_comp_map,
      ← hα, Functor.map_comp]

variable {P} in
/-
**CategoryTheory.ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.leftOrthogonal`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {P : CategoryTheory.ObjectProperty 
C} [inst_2 : CategoryTheory.Limits.HasZeroObject C]   [inst_3 : CategoryTheory.H
asShift C ℤ] [inst_4 : CategoryTheory.Preadditive C]   [inst_5 : ∀ (n : ℤ), (Cat
egoryTheory.shiftFunctor C n).Additive] [inst_6 : CategoryTheory.Pretriangulated
 C]   [P.IsTriangulated] [CategoryTheory.IsTriangulated C] {X : C},   P.leftOrth
ogonal X → ∀ (L : CategoryTheory.Functor C D) [L.IsLocalization P.trW] (Y : C), 
Function.Bijective L.map
参数：n : ℤ；CategoryTheory.shiftFunctor C n；L : CategoryTheory.Functor C D；Y : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.map_eq_iff_postcomp`：∀ {C : Type u_1} {D
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.ObjectProperty.instHasLeftCalculusOfFractionsTrWOfIsTrian
gulatedOfIsTriangulated`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, 
u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C]   [inst_2 : CategoryThe
ory.H…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.isColocal_trW`：isColocal_trW [P.IsTriangul
ated] : P.trW.isColocal = P.leftOrthogonal
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Localization.exists_leftFraction`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …
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
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.instIsIsoMapSOfIsLocalizati
on`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C
]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {W : Categor…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s`：map_comp_ma
p_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : φ.map L hL ≫ 
L.map φ.s = L.map φ.f
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma leftOrthogonal.map_bijective_of_isTriangulated
    [P.IsTriangulated] [IsTriangulated C] {X : C} (hX : P.leftOrthogonal X)
    (L : C ⥤ D) [L.IsLocalization P.trW] (Y : C) :
    Function.Bijective (L.map : (X ⟶ Y) → _) := by
  rw [← isColocal_trW] at hX
  refine ⟨fun f₁ f₂ hf ↦ ?_, fun g ↦ ?_⟩
  · rw [MorphismProperty.map_eq_iff_postcomp L P.trW] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    exact (hX _ hs).1 eq
  · obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.trW g
    obtain ⟨α, hα⟩ := (hX _ φ.hs).2 φ.f
    refine ⟨α, ?_⟩
    rw [hφ, ← cancel_mono (L.map φ.s), MorphismProperty.LeftFraction.map_comp_map_s,
      ← hα, Functor.map_comp]

end ObjectProperty

end CategoryTheory

