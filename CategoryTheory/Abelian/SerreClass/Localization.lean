/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive

/-!
# Localization with respect to a Serre class

The main definition in this file is `ObjectProperty.SerreClassLocalization.abelian`
which shows that if `L : C ⥤ D` is a localization functor with respect to
the class of morphisms `P.isoModSerre` for a Serre class `P : ObjectProperty C`
in the abelian category `C`, then `D` is an abelian category.

We also show that a functor `G : D ⥤ E` to an abelian category is exact iff
the composition `L ⋙ G` is.

-/

@[expose] public section

universe v'' v' v u'' u' u

namespace CategoryTheory

open Limits

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D]
  (L : C ⥤ D) (P : ObjectProperty C) [P.IsSerreClass]
  {E : Type u''} [Category.{v''} E] [Abelian E]

/-
**CategoryTheory.ObjectProperty.exists_epiModSerre_comp_eq_zero_iff** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：exists_epiModSerre_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) : (exists (X' : 
C) (s : X' ⟶ X) (_ : P.epiModSerre s), s ≫ f = 0) ↔ P (Abelian.image f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.ObjectProperty.instIsMultiplicativeEpiModSerre`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian
 C]   (P : CategoryTheory.ObjectProperty C) [inst_2…
· 使用引理 `CategoryTheory.ObjectProperty.epiModSerre_of_epi`：epiModSerre_of_epi {X 
Y : C} (f : X ⟶ Y) [Epi f] : P.epiModSerre f
· 使用定理 `CategoryTheory.Abelian.instEpiFactorThruImage`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {P Q : C} (f
 : P ⟶ Q),   CategoryTheory.Epi (Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.epiModSerre_zero_iff`：epiModSerre_zero_iff
 (X Y : C) : P.epiModSerre (0 : X ⟶ Y) ↔ P Y
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphisms_1`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProper
ty C)   [P.IsClosedUnderQuotients], P.IsClosedUnder…
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toIsClosedUnderQuotients`：∀ {
C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.A
belian C}   {P : CategoryTheory.ObjectProperty C} [self :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
-/
lemma exists_epiModSerre_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∃ (X' : C) (s : X' ⟶ X) (_ : P.epiModSerre s), s ≫ f = 0) ↔
      P (Abelian.image f) := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨X', s, hs, eq⟩
    have := P.epiModSerre.comp_mem s (Abelian.factorThruImage f) hs
      (epiModSerre_of_epi _ _)
    rwa [show s ≫ Abelian.factorThruImage f = 0 by cat_disch,
      epiModSerre_zero_iff] at this
  · exact ⟨_, kernel.ι f, P.prop_of_iso (Abelian.coimageIsoImage f).symm hf, by simp⟩
/-
**CategoryTheory.ObjectProperty.exists_isoModSerre_comp_eq_zero_iff** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：exists_isoModSerre_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) : (exists (X' : 
C) (s : X' ⟶ X) (_ : P.isoModSerre s), s ≫ f = 0) ↔ P (Abelian.image f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.exists_epiModSerre_comp_eq_zero_iff`：exist
s_epiModSerre_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) : (exists (X' : C) (s : X' 
⟶ X) (_ : P.epiModSerre s), s ≫ f = 0) ↔ P (Abelian.ima…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphisms_1`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProper
ty C)   [P.IsClosedUnderQuotients], P.IsClosedUnder…
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toIsClosedUnderQuotients`：∀ {
C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.A
belian C}   {P : CategoryTheory.ObjectProperty C} [self :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_isoModSerre_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∃ (X' : C) (s : X' ⟶ X) (_ : P.isoModSerre s), s ≫ f = 0) ↔
      P (Abelian.image f) := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    rw [← exists_epiModSerre_comp_eq_zero_iff P]
    exact ⟨Y', s, hs.2, eq⟩
  · refine ⟨_, kernel.ι f, ?_, by simp⟩
    simpa only [isoModSerre_iff_of_mono] using!
      P.prop_of_iso (Abelian.coimageIsoImage f).symm hf
/-
**CategoryTheory.ObjectProperty.exists_comp_monoModSerre_eq_zero_iff** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：exists_comp_monoModSerre_eq_zero_iff {X Y : C} (f : X ⟶ Y) : (exists (Y' :
 C) (s : Y ⟶ Y') (_ : P.monoModSerre s), f ≫ s = 0) ↔ P (Abelian.image f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphisms_1`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProper
ty C)   [P.IsClosedUnderQuotients], P.IsClosedUnder…
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toIsClosedUnderQuotients`：∀ {
C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.A
belian C}   {P : CategoryTheory.ObjectProperty C} [self :…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.ObjectProperty.instIsMultiplicativeMonoModSerre`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   (P : CategoryTheory.ObjectProperty C) [inst_2…
· 使用引理 `CategoryTheory.ObjectProperty.monoModSerre_of_mono`：monoModSerre_of_mono
 {X Y : C} (f : X ⟶ Y) [Mono f] : P.monoModSerre f
· 使用定理 `CategoryTheory.Abelian.instMonoFactorThruCoimage`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {P Q : C}
 (f : P ⟶ Q),   CategoryTheory.Mono (C…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.monoModSerre_zero_iff`：monoModSerre_zero_i
ff (X Y : C) : P.monoModSerre (0 : X ⟶ Y) ↔ P X
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
] {X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
-/
lemma exists_comp_monoModSerre_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∃ (Y' : C) (s : Y ⟶ Y') (_ : P.monoModSerre s), f ≫ s = 0) ↔
      P (Abelian.image f) := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    apply P.prop_of_iso (Abelian.coimageIsoImage f)
    have := P.monoModSerre.comp_mem (Abelian.factorThruCoimage f) s
      (monoModSerre_of_mono _ _) hs
    rwa [show Abelian.factorThruCoimage f ≫ s = 0 by cat_disch,
      monoModSerre_zero_iff] at this
  · exact ⟨_, cokernel.π f, hf, by simp⟩
/-
**CategoryTheory.ObjectProperty.exists_comp_isoModSerre_eq_zero_iff** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：exists_comp_isoModSerre_eq_zero_iff {X Y : C} (f : X ⟶ Y) : (exists (Y' : 
C) (s : Y ⟶ Y') (_ : P.isoModSerre s), f ≫ s = 0) ↔ P (Abelian.image f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.exists_comp_monoModSerre_eq_zero_iff`：exis
ts_comp_monoModSerre_eq_zero_iff {X Y : C} (f : X ⟶ Y) : (exists (Y' : C) (s : Y
 ⟶ Y') (_ : P.monoModSerre s), f ≫ s = 0) ↔ P (Abelian.i…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `CategoryTheory.ObjectProperty.isoModSerre_iff_of_epi`：isoModSerre_iff_of
_epi {X Y : C} (f : X ⟶ Y) [Epi f] : P.isoModSerre f ↔ P.monoModSerre f
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_comp_isoModSerre_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∃ (Y' : C) (s : Y ⟶ Y') (_ : P.isoModSerre s), f ≫ s = 0) ↔
      P (Abelian.image f) := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    rw [← exists_comp_monoModSerre_eq_zero_iff P]
    exact ⟨Y', s, hs.1, eq⟩
  · refine ⟨_, cokernel.π f, by rwa [isoModSerre_iff_of_epi], by simp⟩

variable {P} in
/-
**CategoryTheory.ObjectProperty.monoModSerre.isoModSerre_factorThruImage** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.monoModSerre`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   {P : CategoryTheory.ObjectProperty C} [inst_2 : P.IsSerreCl
ass] {X Y : C} {f : X ⟶ Y},   P.monoModSerre f → P.isoModSerre (CategoryTheory.A
belian.factorThruImage f)
参数：CategoryTheory.Abelian.factorThruImage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isoModSerre_iff_of_epi`：isoModSerre_iff_of
_epi {X Y : C} (f : X ⟶ Y) [Epi f] : P.isoModSerre f ↔ P.monoModSerre f
· 使用定理 `CategoryTheory.Abelian.instEpiFactorThruImage`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {P Q : C} (f
 : P ⟶ Q),   CategoryTheory.Epi (Ca…
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphisms_1`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProper
ty C)   [P.IsClosedUnderQuotients], P.IsClosedUnder…
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toIsClosedUnderQuotients`：∀ {
C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.A
belian C}   {P : CategoryTheory.ObjectProperty C} [self :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.instIsIsoMapOfMono`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
-/
lemma monoModSerre.isoModSerre_factorThruImage
    {X Y : C} {f : X ⟶ Y} (hf : P.monoModSerre f) :
    P.isoModSerre (Abelian.factorThruImage f) := by
  rw [isoModSerre_iff_of_epi]
  exact P.prop_of_iso
    (asIso (kernel.map _ f (𝟙 _) (Abelian.image.ι f) (by simp))).symm hf

variable {P} in
/-
**CategoryTheory.ObjectProperty.epiModSerre.isoModSerre_image_** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma epiModSerre.isoModSerre_image_ι
    {X Y : C} {f : X ⟶ Y} (hf : P.epiModSerre f) :
    P.isoModSerre (Abelian.image.ι f) := by
  rw [isoModSerre_iff_of_mono]
  dsimp [epiModSerre] at hf ⊢
  exact P.prop_of_iso
    (asIso (cokernel.map f _ (Abelian.factorThruImage f) (𝟙 Y) (by simp))) hf

namespace SerreClassLocalization

/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.isoModSerre.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ :=
    ⟨{s := pushout.inl φ.f φ.s
      f := pushout.inr φ.f φ.s,
      hs := MorphismProperty.pushout_inl _ _ φ.hs}, pushout.condition⟩
  ext X' X Y f₁ f₂ s hs eq := by
    refine ⟨_, cokernel.π (f₁ - f₂), ?_, ?_⟩
    · rw [isoModSerre_iff_of_epi]
      exact (exists_isoModSerre_comp_eq_zero_iff P _).1 ⟨_, s, hs, by simpa [sub_eq_zero]⟩
    · simpa only [Preadditive.sub_comp, sub_eq_zero] using cokernel.condition (f₁ - f₂)
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.isoModSerre.HasRightCalculusOfFractions where
  exists_rightFraction X Y φ :=
    ⟨{s := pullback.fst φ.f φ.s
      f := pullback.snd φ.f φ.s,
      hs := MorphismProperty.pullback_fst _ _ φ.hs}, pullback.condition⟩
  ext X Y Y' f₁ f₂ s hs eq := by
    refine ⟨_, kernel.ι (f₁ - f₂), ?_, ?_⟩
    · rw [isoModSerre_iff_of_mono]
      exact P.prop_of_iso (Abelian.coimageIsoImage (f₁ - f₂)).symm
        ((exists_comp_isoModSerre_eq_zero_iff P _).1 ⟨_ ,s, hs, by simpa [sub_eq_zero]⟩)
    · simpa only [Preadditive.comp_sub, sub_eq_zero] using kernel.condition (f₁ - f₂)
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.** 是 Mathlib 中的一个示例，位于命名空
间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example : Preadditive P.isoModSerre.Localization := inferInstance
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.** 是 Mathlib 中的一个示例，位于命名空
间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example : P.isoModSerre.Q.Additive := inferInstance

variable [L.IsLocalization P.isoModSerre] [Preadditive D] [L.Additive]

include L P
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.isZero_obj_iff** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：isZero_obj_iff (X : C) : IsZero (L.obj X) ↔ P X
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.MorphismProperty.map_eq_iff_precomp`：∀ {C : Type u_1} {D 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.ObjectProperty.SerreClassLocalization.instHasRightCalculu
sOfFractionsIsoModSerre`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C
] [inst_1 : CategoryTheory.Abelian C]   (P : CategoryTheory.ObjectProperty C) [i
nst_2…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma isZero_obj_iff (X : C) :
    IsZero (L.obj X) ↔ P X := by
  simp only [IsZero.iff_id_eq_zero, ← L.map_id, ← L.map_zero,
    MorphismProperty.map_eq_iff_precomp L P.isoModSerre,
    Category.comp_id, comp_zero, exists_prop, exists_eq_right]
  refine ⟨?_, fun _ ↦ ⟨X, by simpa⟩⟩
  rintro ⟨Y, h⟩
  simpa using h.2
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.map_eq_zero_iff** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：map_eq_zero_iff {X Y : C} (f : X ⟶ Y) : L.map f = 0 ↔ P (Abelian.image f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.MorphismProperty.map_eq_iff_precomp`：∀ {C : Type u_1} {D 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.ObjectProperty.SerreClassLocalization.instHasRightCalculu
sOfFractionsIsoModSerre`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C
] [inst_1 : CategoryTheory.Abelian C]   (P : CategoryTheory.ObjectProperty C) [i
nst_2…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.ObjectProperty.exists_isoModSerre_comp_eq_zero_iff`：exist
s_isoModSerre_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) : (exists (X' : C) (s : X' 
⟶ X) (_ : P.isoModSerre s), s ≫ f = 0) ↔ P (Abelian.ima…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    L.map f = 0 ↔ P (Abelian.image f) := by
  rw [← L.map_zero, MorphismProperty.map_eq_iff_precomp L P.isoModSerre]
  simp [← exists_isoModSerre_comp_eq_zero_iff P]
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.map_comp_eq_zero_iff_of_e
pi_mono** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocal
ization`。
形式化陈述：map_comp_eq_zero_iff_of_epi_mono {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y) [Epi 
f] [Mono g] : L.map f ≫ L.map g = 0 ↔ P Z
参数：f : X ⟶ Z；g : Z ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.map_eq_zero_iff`：ma
p_eq_zero_iff {X Y : C} (f : X ⟶ Y) : L.map f = 0 ↔ P (Abelian.image f)
· 使用定理 `CategoryTheory.strongEpi_of_epi`：strongEpi_of_epi [StrongEpiCategory C] 
(f : P ⟶ Q) [Epi f] : StrongEpi f
· 使用定理 `CategoryTheory.strongEpiCategory_of_regularEpiCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularEpiCategory
 C],   CategoryTheory.StrongEpiCategory C
· 使用定理 `CategoryTheory.regularEpiCategoryOfNormalEpiCategory`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   [CategoryTheory.IsNormalEp…
· 使用定理 `CategoryTheory.Abelian.toIsNormalEpiCategory`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheo
ry.IsNormalEpiCategory C
· 使用引理 `CategoryTheory.ObjectProperty.prop_iff_of_iso`：prop_iff_of_iso [IsClosed
UnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphisms_1`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProper
ty C)   [P.IsClosedUnderQuotients], P.IsClosedUnder…
· 使用定理 `CategoryTheory.ObjectProperty.IsSerreClass.toIsClosedUnderQuotients`：∀ {
C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.A
belian C}   {P : CategoryTheory.ObjectProperty C} [self :…
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
-/
lemma map_comp_eq_zero_iff_of_epi_mono {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y)
    [Epi f] [Mono g] :
    L.map f ≫ L.map g = 0 ↔ P Z := by
  rw [← L.map_comp, map_eq_zero_iff L P]
  have := strongEpi_of_epi f
  exact P.prop_iff_of_iso (Abelian.imageIsoImage _ ≪≫ (image.isoStrongEpiMono f g rfl).symm)
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.mono_map_tfae** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：mono_map_tfae {X Y : C} (f : X ⟶ Y) : List.TFAE [Mono (L.map f), P.monoMod
Serre f, forall ⦃Z : C⦄ (z : Z ⟶ X), L.map z ≫ L.map f = 0 -> L.map z = 0]
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.map_comp_eq_zero_if
f_of_epi_mono`：map_comp_eq_zero_iff_of_epi_mono {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶
 Y) [Epi f] [Mono g] : L.map f ≫ L.map g = 0 ↔ P Z
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.map_eq_zero_iff`：ma
p_eq_zero_iff {X Y : C} (f : X ⟶ Y) : L.map f = 0 ↔ P (Abelian.image f)
· 使用引理 `CategoryTheory.ObjectProperty.exists_comp_monoModSerre_eq_zero_iff`：exis
ts_comp_monoModSerre_eq_zero_iff {X Y : C} (f : X ⟶ Y) : (exists (Y' : C) (s : Y
 ⟶ Y') (_ : P.monoModSerre s), f ≫ s = 0) ↔ P (Abelian.i…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.ObjectProperty.instIsMultiplicativeMonoModSerre`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   (P : CategoryTheory.ObjectProperty C) [inst_2…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Preadditive.mono_iff_cancel_zero`：mono_iff_cancel_zero {Q
 R : C} (f : Q ⟶ R) : Mono f ↔ forall (P : C) (g : P ⟶ Q), g ≫ f = 0 -> g = 0
（共 40 条，此处仅展示前 30 条）
-/
lemma mono_map_tfae {X Y : C} (f : X ⟶ Y) :
    List.TFAE [Mono (L.map f),
      P.monoModSerre f,
      ∀ ⦃Z : C⦄ (z : Z ⟶ X), L.map z ≫ L.map f = 0 → L.map z = 0] := by
  have := Localization.essSurj L P.isoModSerre
  tfae_have 1 → 2 := fun _ ↦ by
    have hf : L.map (kernel.ι f) = 0 := by
      rw [← cancel_mono (L.map f), zero_comp, ← L.map_comp,
        kernel.condition, L.map_zero]
    simpa [hf] using! map_comp_eq_zero_iff_of_epi_mono L P (𝟙 _) (kernel.ι f)
  tfae_have 2 → 3 := fun hf ↦ by
    intro Z z hz
    rw [← L.map_comp] at hz
    rw [map_eq_zero_iff L P, ← exists_comp_monoModSerre_eq_zero_iff P] at hz ⊢
    obtain ⟨W, s, hs, eq⟩ := hz
    exact ⟨W, f ≫ s, MorphismProperty.comp_mem _ _ _ hf hs, by simpa using! eq⟩
  tfae_have 3 → 1 := fun hf ↦ by
    rw [Preadditive.mono_iff_cancel_zero]
    intro W z hz
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.isoModSerre
      ((L.objObjPreimageIso W).hom ≫ z)
    rw [← cancel_epi (L.objObjPreimageIso W).hom, comp_zero, hφ,
      ← cancel_epi (L.map φ.s), comp_zero,
      MorphismProperty.RightFraction.map_s_comp_map]
    apply hf φ.f
    have : L.map φ.s ≫ (L.objObjPreimageIso W).hom ≫ z = L.map φ.f := by cat_disch
    rw [← this, Category.assoc, Category.assoc, hz, comp_zero, comp_zero]
  tfae_finish
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.mono_map_iff** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：mono_map_iff {X Y : C} (f : X ⟶ Y) : Mono (L.map f) ↔ P.monoModSerre f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.mono_map_tfae`：mono
_map_tfae {X Y : C} (f : X ⟶ Y) : List.TFAE [Mono (L.map f), P.monoModSerre f, f
orall ⦃Z : C⦄ (z : Z ⟶ X), L.map z ≫ L.map f = 0 -> L.ma…
-/
lemma mono_map_iff {X Y : C} (f : X ⟶ Y) :
    Mono (L.map f) ↔ P.monoModSerre f :=
  (mono_map_tfae L P f).out 0 1
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.epi_map_tfae** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：epi_map_tfae {X Y : C} (f : X ⟶ Y) : List.TFAE [Epi (L.map f), P.epiModSer
re f, forall ⦃Z : C⦄ (z : Y ⟶ Z), L.map f ≫ L.map z = 0 -> L.map z = 0]
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.map_comp_eq_zero_if
f_of_epi_mono`：map_comp_eq_zero_iff_of_epi_mono {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶
 Y) [Epi f] [Mono g] : L.map f ≫ L.map g = 0 ↔ P Z
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.map_eq_zero_iff`：ma
p_eq_zero_iff {X Y : C} (f : X ⟶ Y) : L.map f = 0 ↔ P (Abelian.image f)
· 使用引理 `CategoryTheory.ObjectProperty.exists_epiModSerre_comp_eq_zero_iff`：exist
s_epiModSerre_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) : (exists (X' : C) (s : X' 
⟶ X) (_ : P.epiModSerre s), s ≫ f = 0) ↔ P (Abelian.ima…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.ObjectProperty.instIsMultiplicativeEpiModSerre`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian
 C]   (P : CategoryTheory.ObjectProperty C) [inst_2…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Preadditive.epi_iff_cancel_zero`：epi_iff_cancel_zero {P Q
 : C} (f : P ⟶ Q) : Epi f ↔ forall (R : C) (g : Q ⟶ R), f ≫ g = 0 -> g = 0
（共 46 条，此处仅展示前 30 条）
-/
lemma epi_map_tfae {X Y : C} (f : X ⟶ Y) :
    List.TFAE [Epi (L.map f),
      P.epiModSerre f,
      ∀ ⦃Z : C⦄ (z : Y ⟶ Z), L.map f ≫ L.map z = 0 → L.map z = 0] := by
  have := Localization.essSurj L P.isoModSerre
  tfae_have 1 → 2 := fun _ ↦ by
    have hf : L.map (cokernel.π f) = 0 := by
      rw [← cancel_epi (L.map f), comp_zero, ← L.map_comp,
        cokernel.condition, L.map_zero]
    simpa [hf] using! map_comp_eq_zero_iff_of_epi_mono L P (cokernel.π f) (𝟙 _)
  tfae_have 2 → 3 := fun hf ↦ by
    intro Z z hz
    rw [← L.map_comp] at hz
    rw [map_eq_zero_iff L P, ← exists_epiModSerre_comp_eq_zero_iff P] at hz ⊢
    obtain ⟨W, s, hs, eq⟩ := hz
    refine ⟨_, s ≫ f, MorphismProperty.comp_mem _ _ _ hs hf, by simpa⟩
  tfae_have 3 → 1 := fun hf ↦ by
    rw [Preadditive.epi_iff_cancel_zero]
    intro W z hz
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.isoModSerre
      (z ≫ (L.objObjPreimageIso W).inv)
    rw [← cancel_mono (L.objObjPreimageIso W).inv, zero_comp, hφ,
      ← cancel_mono (L.map φ.s), zero_comp,
      MorphismProperty.LeftFraction.map_comp_map_s]
    apply hf φ.f
    have : L.map φ.f = z ≫ (L.objObjPreimageIso W).inv ≫ L.map φ.s := by
      simp [reassoc_of% hφ]
    rw [this, reassoc_of% hz, zero_comp]
  tfae_finish
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.epi_map_iff** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：epi_map_iff {X Y : C} (f : X ⟶ Y) : Epi (L.map f) ↔ P.epiModSerre f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.epi_map_tfae`：epi_m
ap_tfae {X Y : C} (f : X ⟶ Y) : List.TFAE [Epi (L.map f), P.epiModSerre f, foral
l ⦃Z : C⦄ (z : Y ⟶ Z), L.map f ≫ L.map z = 0 -> L.map z…
-/
lemma epi_map_iff {X Y : C} (f : X ⟶ Y) :
    Epi (L.map f) ↔ P.epiModSerre f :=
  (epi_map_tfae L P f).out 0 1
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.inverseImage_monomorphism
s** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalizatio
n`。
形式化陈述：inverseImage_monomorphisms : (MorphismProperty.monomorphisms _).inverseIma
ge L = P.monoModSerre
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.mono_map_iff`：mono_
map_iff {X Y : C} (f : X ⟶ Y) : Mono (L.map f) ↔ P.monoModSerre f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inverseImage_monomorphisms :
    (MorphismProperty.monomorphisms _).inverseImage L = P.monoModSerre := by
  ext
  simp [mono_map_iff L P]
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.inverseImage_epimorphisms
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization
`。
形式化陈述：inverseImage_epimorphisms : (MorphismProperty.epimorphisms _).inverseImage
 L = P.epiModSerre
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.epi_map_iff`：epi_ma
p_iff {X Y : C} (f : X ⟶ Y) : Epi (L.map f) ↔ P.epiModSerre f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inverseImage_epimorphisms :
    (MorphismProperty.epimorphisms _).inverseImage L = P.epiModSerre := by
  ext
  simp [epi_map_iff L P]
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.preservesMonomorphisms** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：preservesMonomorphisms : L.PreservesMonomorphisms where preserves f _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.mono_map_iff`：mono_
map_iff {X Y : C} (f : X ⟶ Y) : Mono (L.map f) ↔ P.monoModSerre f
· 使用引理 `CategoryTheory.ObjectProperty.monoModSerre_of_mono`：monoModSerre_of_mono
 {X Y : C} (f : X ⟶ Y) [Mono f] : P.monoModSerre f
-/
lemma preservesMonomorphisms : L.PreservesMonomorphisms where
  preserves f _ := by simpa only [mono_map_iff _ P] using P.monoModSerre_of_mono f
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.preservesEpimorphisms** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：preservesEpimorphisms : L.PreservesEpimorphisms where preserves f _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.epi_map_iff`：epi_ma
p_iff {X Y : C} (f : X ⟶ Y) : Epi (L.map f) ↔ P.epiModSerre f
· 使用引理 `CategoryTheory.ObjectProperty.epiModSerre_of_epi`：epiModSerre_of_epi {X 
Y : C} (f : X ⟶ Y) [Epi f] : P.epiModSerre f
-/
lemma preservesEpimorphisms : L.PreservesEpimorphisms where
  preserves f _ := by simpa only [epi_map_iff _ P] using P.epiModSerre_of_epi f

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.mono_iff** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：mono_iff {X Y : D} (f : X ⟶ Y) : Mono f ↔ exists (X' Y' : C) (f' : X' ⟶ Y'
) (_ : Mono f'), Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.preservesMonomorphi
sms`：preservesMonomorphisms : L.PreservesMonomorphisms where preserves f _
· 使用定理 `CategoryTheory.Localization.essSurj_mapArrow`：∀ {C : Type u_1} {D : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.ObjectProperty.SerreClassLocalization.instHasLeftCalculus
OfFractionsIsoModSerre`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
 [inst_1 : CategoryTheory.Abelian C]   (P : CategoryTheory.ObjectProperty C) [in
st_2…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.ObjectProperty.monoModSerre.isoModSerre_factorThruImage`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheor
y.Abelian C]   {P : CategoryTheory.ObjectProperty C} [inst_2…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.mono_map_iff`：mono_
map_iff {X Y : C} (f : X ⟶ Y) : Mono (L.map f) ↔ P.monoModSerre f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_iso_iff`：arrow_iso_iff (P : Morphi
smProperty C) [RespectsIso P] {f g : Arrow C} (e : f ≅ g) : P f.hom ↔ P g.hom
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.monomorphisms`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.mo
nomorphisms C).RespectsIso
· 使用定理 `CategoryTheory.MorphismProperty.monomorphisms.infer_property`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [hf : Categ
oryTheory.Mono f],   CategoryTheory.MorphismProper…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
-/
lemma mono_iff {X Y : D} (f : X ⟶ Y) :
    Mono f ↔ ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : Mono f'),
      Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk f) := by
  have := preservesMonomorphisms L P
  have := Localization.essSurj_mapArrow L P.isoModSerre
  refine ⟨fun _ ↦ ?_, ?_⟩
  · suffices ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (_ : Mono (L.map f)),
      ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : Mono f'),
          Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk (L.map f)) by
        let e := L.mapArrow.objObjPreimageIso (Arrow.mk f)
        obtain ⟨X', Y', f', _, ⟨e'⟩⟩ := this _
          (((MorphismProperty.monomorphisms D).arrow_iso_iff e).2 (.infer_property f))
        exact ⟨_, _, f', inferInstance, ⟨e' ≪≫ e⟩⟩
    intro X Y f hf
    rw [mono_map_iff L P] at hf
    refine ⟨_, _, Abelian.image.ι f, inferInstance, ⟨Iso.symm ?_⟩⟩
    have := Localization.inverts L P.isoModSerre _ hf.isoModSerre_factorThruImage
    exact Arrow.isoMk (asIso (L.map (Abelian.factorThruImage f))) (Iso.refl _)
      (by simp [← L.map_comp])
  · rintro ⟨X', Y', f', _, ⟨e⟩⟩
    exact ((MorphismProperty.monomorphisms D).arrow_mk_iso_iff e).1
      (by simpa using inferInstanceAs (Mono (L.map f')))

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.epi_iff** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：epi_iff {X Y : D} (f : X ⟶ Y) : Epi f ↔ exists (X' Y' : C) (f' : X' ⟶ Y') 
(_ : Epi f'), Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.preservesEpimorphis
ms`：preservesEpimorphisms : L.PreservesEpimorphisms where preserves f _
· 使用定理 `CategoryTheory.Localization.essSurj_mapArrow`：∀ {C : Type u_1} {D : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.ObjectProperty.SerreClassLocalization.instHasLeftCalculus
OfFractionsIsoModSerre`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
 [inst_1 : CategoryTheory.Abelian C]   (P : CategoryTheory.ObjectProperty C) [in
st_2…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Abelian.instEpiFactorThruImage`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {P Q : C} (f
 : P ⟶ Q),   CategoryTheory.Epi (Ca…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.ObjectProperty.epiModSerre.isoModSerre_image_ι`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian
 C]   {P : CategoryTheory.ObjectProperty C} [inst_2…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.epi_map_iff`：epi_ma
p_iff {X Y : C} (f : X ⟶ Y) : Epi (L.map f) ↔ P.epiModSerre f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_iso_iff`：arrow_iso_iff (P : Morphi
smProperty C) [RespectsIso P] {f g : Arrow C} (e : f ≅ g) : P f.hom ↔ P g.hom
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.epimorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.epi
morphisms C).RespectsIso
· 使用定理 `CategoryTheory.MorphismProperty.epimorphisms.infer_property`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [hf : Catego
ryTheory.Epi f],   CategoryTheory.MorphismPropert…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
-/
lemma epi_iff {X Y : D} (f : X ⟶ Y) :
    Epi f ↔ ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : Epi f'),
      Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk f) := by
  have := preservesEpimorphisms L P
  have := Localization.essSurj_mapArrow L P.isoModSerre
  refine ⟨fun _ ↦ ?_, ?_⟩
  · suffices ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (_ : Epi (L.map f)),
      ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : Epi f'),
          Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk (L.map f)) by
        let e := L.mapArrow.objObjPreimageIso (Arrow.mk f)
        obtain ⟨X', Y', f', _, ⟨e'⟩⟩ := this _
          (((MorphismProperty.epimorphisms D).arrow_iso_iff e).2 (.infer_property f))
        exact ⟨_, _, f', inferInstance, ⟨e' ≪≫ e⟩⟩
    intro X Y f hf
    rw [epi_map_iff L P] at hf
    refine ⟨_, _, Abelian.factorThruImage f, inferInstance, ⟨?_⟩⟩
    have := Localization.inverts L P.isoModSerre _ hf.isoModSerre_image_ι
    refine Arrow.isoMk (Iso.refl _) (asIso (L.map (Abelian.image.ι f))) (by simp [← L.map_comp])
  · rintro ⟨X', Y', f', _, ⟨e⟩⟩
    exact ((MorphismProperty.epimorphisms D).arrow_mk_iso_iff e).1
      (by simpa using inferInstanceAs (Epi (L.map f')))

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.preservesKernel** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：preservesKernel {X Y : C} (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) 
L
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.preservesMonomorphi
sms`：preservesMonomorphisms : L.PreservesMonomorphisms where preserves f _
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.map_eq_zero_iff`：ma
p_eq_zero_iff {X Y : C} (f : X ⟶ Y) : L.map f = 0 ↔ P (Abelian.image f)
· 使用引理 `CategoryTheory.ObjectProperty.exists_isoModSerre_comp_eq_zero_iff`：exist
s_isoModSerre_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) : (exists (X' : C) (s : X' 
⟶ X) (_ : P.isoModSerre s), s ≫ f = 0) ↔ P (Abelian.ima…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Localization.exists_rightFraction`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.ObjectProperty.SerreClassLocalization.instHasRightCalculu
sOfFractionsIsoModSerre`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C
] [inst_1 : CategoryTheory.Abelian C]   (P : CategoryTheory.ObjectProperty C) [i
nst_2…
· 使用引理 `CategoryTheory.MorphismProperty.RightFraction.map_s_comp_map`：map_s_comp
_map (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : L.map φ.s ≫
 φ.map L hL = L.map φ.f
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.instIsIsoMapSOfIsLocalizat
ion`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} 
C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {W : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
（共 38 条，此处仅展示前 30 条）
-/
lemma preservesKernel {X Y : C} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) L := by
  have := preservesMonomorphisms L P
  have := Localization.essSurj L P.isoModSerre
  suffices ∀ (W : D) (z : W ⟶ L.obj X) (hz : z ≫ L.map f = 0),
      ∃ (l : W ⟶ L.obj (kernel f)), l ≫ L.map (kernel.ι f) = z from
    preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
      ((KernelFork.isLimitMapConeEquiv _ L).2
        (Fork.IsLimit.ofExistsUnique
          (fun s ↦ existsUnique_of_exists_of_unique
            (this _ _ (KernelFork.condition s))
            (fun _ _ h₁ h₂ ↦ by simpa [cancel_mono] using h₁.trans h₂.symm))))
  intro W w hw
  wlog hw' : ∃ (Z : C) (hZ : W = L.obj Z) (z : Z ⟶ X), w = eqToHom hZ ≫ L.map z
      generalizing W
  · obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.isoModSerre
      ((L.objObjPreimageIso W).hom ≫ w)
    rw [← cancel_epi (L.map φ.s),
      MorphismProperty.RightFraction.map_s_comp_map] at hφ
    obtain ⟨l, hl⟩ := this _ (L.map φ.f) (by
      rw [← hφ, Category.assoc, Category.assoc, hw, comp_zero, comp_zero]) ⟨_, rfl, by simp⟩
    exact ⟨(L.objObjPreimageIso W).inv ≫ inv (L.map φ.s) ≫ l, by simp [hl, ← hφ]⟩
  obtain ⟨Z, rfl, z, rfl⟩ := hw'
  simp only [eqToHom_refl, Category.id_comp, ← L.map_comp, map_eq_zero_iff L P,
    ← exists_isoModSerre_comp_eq_zero_iff P] at hw
  obtain ⟨Z', t, ht, fac⟩ := hw
  have := Localization.inverts L P.isoModSerre t ht
  rw [← Category.assoc] at fac
  exact ⟨inv (L.map t) ≫ L.map (kernel.lift _ _ fac), by simp [← Functor.map_comp]⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.preservesCokernel** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：preservesCokernel {X Y : C} (f : X ⟶ Y) : PreservesColimit (parallelPair f
 0) L
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.preservesEpimorphis
ms`：preservesEpimorphisms : L.PreservesEpimorphisms where preserves f _
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.map_eq_zero_iff`：ma
p_eq_zero_iff {X Y : C} (f : X ⟶ Y) : L.map f = 0 ↔ P (Abelian.image f)
· 使用引理 `CategoryTheory.ObjectProperty.exists_comp_isoModSerre_eq_zero_iff`：exist
s_comp_isoModSerre_eq_zero_iff {X Y : C} (f : X ⟶ Y) : (exists (Y' : C) (s : Y ⟶
 Y') (_ : P.isoModSerre s), f ≫ s = 0) ↔ P (Abelian.ima…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Localization.exists_leftFraction`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.ObjectProperty.SerreClassLocalization.instHasLeftCalculus
OfFractionsIsoModSerre`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
 [inst_1 : CategoryTheory.Abelian C]   (P : CategoryTheory.ObjectProperty C) [in
st_2…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s`：map_comp_ma
p_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : φ.map L hL ≫ 
L.map φ.s = L.map φ.f
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
（共 44 条，此处仅展示前 30 条）
-/
lemma preservesCokernel {X Y : C} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) L := by
  have := preservesEpimorphisms L P
  have := Localization.essSurj L P.isoModSerre
  suffices ∀ (W : D) (z : L.obj Y ⟶ W) (hz : L.map f ≫ z = 0),
      ∃ (l : L.obj (cokernel f) ⟶ W), L.map (cokernel.π f) ≫ l = z from
    preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
      ((CokernelCofork.isColimitMapCoconeEquiv _ L).2
        (Cofork.IsColimit.ofExistsUnique
          (fun s ↦ existsUnique_of_exists_of_unique
            (this _ _ (CokernelCofork.condition s))
            (fun _ _ h₁ h₂ ↦ by simpa [cancel_epi] using h₁.trans h₂.symm))))
  intro W w hw
  wlog hw' : ∃ (Z : C) (hZ : L.obj Z = W) (z : Y ⟶ Z), w = L.map z ≫ eqToHom hZ
      generalizing W
  · obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.isoModSerre
      (w ≫ (L.objObjPreimageIso W).inv)
    rw [← cancel_mono (L.map φ.s), Category.assoc,
      MorphismProperty.LeftFraction.map_comp_map_s] at hφ
    obtain ⟨l, hl⟩ := this _ (L.map φ.f) (by rw [← hφ, reassoc_of% hw, zero_comp]) ⟨_, rfl, by simp⟩
    exact ⟨l ≫ inv (L.map φ.s) ≫ (L.objObjPreimageIso W).hom, by simp [reassoc_of% hl, ← hφ]⟩
  obtain ⟨Z, rfl, z, rfl⟩ := hw'
  simp only [eqToHom_refl, Category.comp_id, ← L.map_comp,
    map_eq_zero_iff L P, ← exists_comp_isoModSerre_eq_zero_iff P] at hw
  obtain ⟨Z', t, ht, fac⟩ := hw
  rw [Category.assoc] at fac
  have := Localization.inverts L P.isoModSerre t ht
  exact ⟨L.map (cokernel.desc _ _ fac) ≫ inv (L.map t), by simp [← L.map_comp_assoc]⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.hasKernels** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：hasKernels : HasKernels D where has_limit f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Localization.essSurj_mapArrow`：∀ {C : Type u_1} {D : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.ObjectProperty.SerreClassLocalization.instHasLeftCalculus
OfFractionsIsoModSerre`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
 [inst_1 : CategoryTheory.Abelian C]   (P : CategoryTheory.ObjectProperty C) [in
st_2…
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.preservesKernel`：pr
eservesKernel {X Y : C} (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) L
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Arrow.rightFunc_map`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C]   {Y X : CategoryTheory.Comma (CategoryTheory.Functor.id C)
 (CategoryTheory.Functor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Arrow.leftFunc_map`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C]   {X Y : CategoryTheory.Comma (CategoryTheory.Functor.id C) 
(CategoryTheory.Functor…
· 使用定理 `CategoryTheory.Arrow.w_mk_right`：w_mk_right {f : Arrow T} {X Y : T} {g :
 X ⟶ Y} (sq : f ⟶ mk g) : dsimp% sq.left ≫ g = f.hom ≫ sq.right
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hasKernels : HasKernels D where
  has_limit f := by
    obtain ⟨g, ⟨e⟩⟩ :=
      (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
    have := preservesKernel L P g.hom
    have : HasLimit (parallelPair (L.map g.hom) 0) :=
      ⟨_, (KernelFork.isLimitMapConeEquiv _ L).1
        (isLimitOfPreserves L (kernelIsKernel g.hom))⟩
    exact hasLimit_of_iso (show parallelPair (L.map g.hom) 0 ≅ _ from
      parallelPair.ext (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e))

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.hasCokernels** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：hasCokernels : HasCokernels D where has_colimit f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Localization.essSurj_mapArrow`：∀ {C : Type u_1} {D : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.ObjectProperty.SerreClassLocalization.instHasLeftCalculus
OfFractionsIsoModSerre`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
 [inst_1 : CategoryTheory.Abelian C]   (P : CategoryTheory.ObjectProperty C) [in
st_2…
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.preservesCokernel`：
preservesCokernel {X Y : C} (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) L
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Arrow.rightFunc_map`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C]   {Y X : CategoryTheory.Comma (CategoryTheory.Functor.id C)
 (CategoryTheory.Functor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Arrow.leftFunc_map`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C]   {X Y : CategoryTheory.Comma (CategoryTheory.Functor.id C) 
(CategoryTheory.Functor…
· 使用定理 `CategoryTheory.Arrow.w_mk_right`：w_mk_right {f : Arrow T} {X Y : T} {g :
 X ⟶ Y} (sq : f ⟶ mk g) : dsimp% sq.left ≫ g = f.hom ≫ sq.right
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma hasCokernels : HasCokernels D where
  has_colimit f := by
    obtain ⟨g, ⟨e⟩⟩ :=
      (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
    have := preservesCokernel L P g.hom
    have : HasColimit (parallelPair (L.map g.hom) 0) :=
      ⟨_, (CokernelCofork.isColimitMapCoconeEquiv _ L).1
        (isColimitOfPreserves L (cokernelIsCokernel g.hom))⟩
    exact hasColimit_of_iso (show _ ≅ parallelPair (L.map g.hom) 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso e.symm) (Arrow.rightFunc.mapIso e.symm))
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.hasEqualizers** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：hasEqualizers : HasEqualizers D
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.hasKernels`：hasKern
els : HasKernels D where has_limit f
· 使用定理 `CategoryTheory.Preadditive.hasEqualizer_of_hasKernel`：hasEqualizer_of_ha
sKernel [HasKernel (f - g)] : HasEqualizer f g
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.hasEqualizers_of_hasLimit_parallelPair`：hasEqualiz
ers_of_hasLimit_parallelPair [forall {X Y : C} {f g : X ⟶ Y}, HasLimit (parallel
Pair f g)] : HasEqualizers C
-/
lemma hasEqualizers : HasEqualizers D :=
  have := hasKernels L P
  have {X Y : D} (f g : X ⟶ Y) : HasEqualizer f g :=
    Preadditive.hasEqualizer_of_hasKernel _ _
  hasEqualizers_of_hasLimit_parallelPair _
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.hasCoequalizers** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：hasCoequalizers : HasCoequalizers D
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.hasCokernels`：hasCo
kernels : HasCokernels D where has_colimit f
· 使用定理 `CategoryTheory.Preadditive.hasCoequalizer_of_hasCokernel`：hasCoequalizer
_of_hasCokernel [HasCokernel (f - g)] : HasCoequalizer f g
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.hasCoequalizers_of_hasColimit_parallelPair`：hasCoe
qualizers_of_hasColimit_parallelPair [forall {X Y : C} {f g : X ⟶ Y}, HasColimit
 (parallelPair f g)] : HasCoequalizers C
-/
lemma hasCoequalizers : HasCoequalizers D :=
  have := hasCokernels L P
  have {X Y : D} (f g : X ⟶ Y) : HasCoequalizer f g :=
    Preadditive.hasCoequalizer_of_hasCokernel _ _
  hasCoequalizers_of_hasColimit_parallelPair _
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.hasFiniteProducts** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：hasFiniteProducts : HasFiniteProducts D
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用引理 `CategoryTheory.Functor.hasFiniteProducts_of_additive_of_essSurj`：hasFini
teProducts_of_additive_of_essSurj [HasFiniteProducts C] [Additive F] [EssSurj F]
 : HasFiniteProducts D
· 使用定理 `CategoryTheory.Abelian.has_finite_products`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory
.Limits.HasFiniteProducts C
-/
lemma hasFiniteProducts : HasFiniteProducts D :=
  have := Localization.essSurj L P.isoModSerre
  L.hasFiniteProducts_of_additive_of_essSurj
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.isNormalMonoCategory** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：isNormalMonoCategory : IsNormalMonoCategory D where normalMonoOfMono f hf
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.mono_iff`：mono_iff 
{X Y : D} (f : X ⟶ Y) : Mono f ↔ exists (X' Y' : C) (f' : X' ⟶ Y') (_ : Mono f')
, Nonempty (Arrow.mk (L.map f') ≅ Arrow.mk f)
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.preservesKernel`：pr
eservesKernel {X Y : C} (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NormalMono.w`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {X Y : C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
 {f : X ⟶ Y} [sel…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isNormalMonoCategory : IsNormalMonoCategory D where
  normalMonoOfMono f hf := by
    rw [mono_iff L P] at hf
    obtain ⟨X', Y', f', _, ⟨e⟩⟩ := hf
    let hf' := normalMonoOfMono f'
    have := preservesKernel L P hf'.g
    refine ⟨NormalMono.ofArrowIso ?_ e⟩
    exact {
      Z := L.obj hf'.Z
      g := L.map hf'.g
      w := by rw [← L.map_comp]; simp [hf'.w]
      isLimit :=
        (KernelFork.isLimitMapConeEquiv _ L).1
          (isLimitOfPreserves L hf'.isLimit) }
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.isNormalEpiCategory** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：isNormalEpiCategory : IsNormalEpiCategory D where normalEpiOfEpi f hf
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.epi_iff`：epi_iff {X
 Y : D} (f : X ⟶ Y) : Epi f ↔ exists (X' Y' : C) (f' : X' ⟶ Y') (_ : Epi f'), No
nempty (Arrow.mk (L.map f') ≅ Arrow.mk f)
· 使用定理 `CategoryTheory.Abelian.toIsNormalEpiCategory`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheo
ry.IsNormalEpiCategory C
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.preservesCokernel`：
preservesCokernel {X Y : C} (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NormalEpi.w`：∀ {C : Type u₁} {inst : CategoryTheory.Categ
ory.{v₁, u₁} C} {X Y : C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} 
{f : X ⟶ Y} [sel…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isNormalEpiCategory : IsNormalEpiCategory D where
  normalEpiOfEpi f hf := by
    rw [epi_iff L P] at hf
    obtain ⟨X', Y', f', _, ⟨e⟩⟩ := hf
    let hf' := normalEpiOfEpi f'
    have := preservesCokernel L P hf'.g
    refine ⟨NormalEpi.ofArrowIso ?_ e⟩
    exact {
      W := L.obj hf'.W
      g := L.map hf'.g
      w := by rw [← L.map_comp]; simp [hf'.w]
      isColimit :=
        (CokernelCofork.isColimitMapCoconeEquiv _ L).1
          (isColimitOfPreserves L hf'.isColimit) }

/-- If `L : C ⥤ D` is a localization functor with respect to a Serre class `P` in
the abelian category `C`, then `D` is an abelian category.
Note that we assume that `D` has already been equipped with a preadditive structure,
and that `L` is additive. Otherwise, see the results in the file
`Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean`
which applies because `P.isoModSerre` has a calculus of left and right fractions. -/
@[stacks 02MS, instance_reducible]
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.abelian** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：abelian : Abelian D
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.hasFiniteProducts`：
hasFiniteProducts : HasFiniteProducts D
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.hasKernels`：hasKern
els : HasKernels D where has_limit f
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.hasCokernels`：hasCo
kernels : HasCokernels D where has_colimit f
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.isNormalMonoCategor
y`：isNormalMonoCategory : IsNormalMonoCategory D where normalMonoOfMono f hf
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.isNormalEpiCategory
`：isNormalEpiCategory : IsNormalEpiCategory D where normalEpiOfEpi f hf

--- 原说明 ---
If `L : C ⥤ D` is a localization functor with respect to a Serre class `P` in
the abelian category `C`, then `D` is an abelian category.
Note that we assume that `D` has already been equipped with a preadditive struct
ure,
and that `L` is additive. Otherwise, see the results in the file
`Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean`
which applies because `P.isoModSerre` has a calculus of left and right fractions
.
-/
def abelian : Abelian D := by
  have := hasFiniteProducts L P
  have := hasKernels L P
  have := hasCokernels L P
  have := isNormalMonoCategory L P
  have := isNormalEpiCategory L P
  constructor
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.hasZeroObject** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：hasZeroObject : HasZeroObject D
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
-/
lemma hasZeroObject : HasZeroObject D :=
  have := abelian L P
  Abelian.hasZeroObject
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.preservesFiniteLimits** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：preservesFiniteLimits : PreservesFiniteLimits L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Functor.preservesFiniteLimits_tfae`：preservesFiniteLimits
_tfae : List.TFAE [ forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact
 ∧ Mono (F.map S.f), forall (S : ShortC…
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.preservesKernel`：pr
eservesKernel {X Y : C} (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) L
-/
lemma preservesFiniteLimits : PreservesFiniteLimits L := by
  let := abelian L P
  rw [((Functor.preservesFiniteLimits_tfae L).out 3 2 :)]
  intro _ _ f
  exact preservesKernel L P f
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.preservesFiniteColimits**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：preservesFiniteColimits : PreservesFiniteColimits L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Functor.preservesFiniteColimits_tfae`：preservesFiniteColi
mits_tfae : List.TFAE [ forall (S : ShortComplex C), S.ShortExact -> (S.map F).E
xact ∧ Epi (F.map S.g), forall (S : Short…
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.preservesCokernel`：
preservesCokernel {X Y : C} (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) L
-/
lemma preservesFiniteColimits : PreservesFiniteColimits L := by
  let := abelian L P
  rw [((Functor.preservesFiniteColimits_tfae L).out 3 2 :)]
  intro _ _ f
  exact preservesCokernel L P f
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.isIso_map_iff** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：isIso_map_iff {X Y : C} (f : X ⟶ Y) : IsIso (L.map f) ↔ P.isoModSerre f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isIso_iff_mono_and_epi`：isIso_iff_mono_and_epi [Balanced 
C] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Mono f ∧ Epi f
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.mono_map_iff`：mono_
map_iff {X Y : C} (f : X ⟶ Y) : Mono (L.map f) ↔ P.monoModSerre f
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.epi_map_iff`：epi_ma
p_iff {X Y : C} (f : X ⟶ Y) : Epi (L.map f) ↔ P.epiModSerre f
· 使用引理 `CategoryTheory.ObjectProperty.isoModSerre_iff`：isoModSerre_iff {X Y : C}
 (f : X ⟶ Y) : P.isoModSerre f ↔ P.monoModSerre f ∧ P.epiModSerre f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isIso_map_iff {X Y : C} (f : X ⟶ Y) :
    IsIso (L.map f) ↔ P.isoModSerre f := by
  let := abelian L P
  rw [isIso_iff_mono_and_epi, mono_map_iff L P, epi_map_iff L P, isoModSerre_iff]
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.inverseImage_isomorphisms
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization
`。
形式化陈述：inverseImage_isomorphisms : (MorphismProperty.isomorphisms _).inverseImage
 L = P.isoModSerre
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.isIso_map_iff`：isIs
o_map_iff {X Y : C} (f : X ⟶ Y) : IsIso (L.map f) ↔ P.isoModSerre f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inverseImage_isomorphisms :
    (MorphismProperty.isomorphisms _).inverseImage L = P.isoModSerre := by
  ext
  simp [isIso_map_iff L P]

variable (G : D ⥤ E)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.preservesFiniteLimits_com
p_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocaliz
ation`。
形式化陈述：preservesFiniteLimits_comp_iff : PreservesFiniteLimits (L ⋙ G) ↔ Preserves
FiniteLimits G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.preservesFiniteLimi
ts`：preservesFiniteLimits : PreservesFiniteLimits L
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Localization.functor_additive_iff`：functor_additive_iff {
E : Type*} [Category* E] [Preadditive E] [Preadditive D] [L.Additive] (G : D ⥤ E
) : G.Additive ↔ (L ⋙ G).Additive
· 使用定理 `CategoryTheory.ObjectProperty.SerreClassLocalization.instHasLeftCalculus
OfFractionsIsoModSerre`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
 [inst_1 : CategoryTheory.Abelian C]   (P : CategoryTheory.ObjectProperty C) [in
st_2…
· 使用引理 `CategoryTheory.Functor.additive_of_preserves_binary_products`：additive_o
f_preserves_binary_products [HasBinaryProducts C] [PreservesLimitsOfShape (Discr
ete WalkingPair) F] [F.PreservesZeroMorphisms] : F…
· 使用定理 `CategoryTheory.Abelian.has_finite_products`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory
.Limits.HasFiniteProducts C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_obje
ct`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Functor.preservesFiniteLimits_tfae`：preservesFiniteLimits
_tfae : List.TFAE [ forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact
 ∧ Mono (F.map S.f), forall (S : ShortC…
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Localization.essSurj_mapArrow`：∀ {C : Type u_1} {D : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] (L : Categor…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Arrow.rightFunc_map`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C]   {Y X : CategoryTheory.Comma (CategoryTheory.Functor.id C)
 (CategoryTheory.Functor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 36 条，此处仅展示前 30 条）
-/
lemma preservesFiniteLimits_comp_iff :
    PreservesFiniteLimits (L ⋙ G) ↔ PreservesFiniteLimits G := by
  let := abelian L P
  have := preservesFiniteLimits L P
  refine ⟨fun _ ↦ ?_, fun _ ↦ comp_preservesFiniteLimits _ _⟩
  have := (Localization.functor_additive_iff L P.isoModSerre G).mpr
    (L ⋙ G).additive_of_preserves_binary_products
  refine ((Functor.preservesFiniteLimits_tfae G).out 2 3).mp (fun _ _ f ↦ ?_)
  obtain ⟨f', ⟨iso⟩⟩ :=
    (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
  have : PreservesLimit (parallelPair (L.map f'.hom) 0) G :=
    preservesLimit_of_preserves_limit_cone
      (KernelFork.isLimitMapConeEquiv _ _
        (isLimitOfPreserves L (kernelIsKernel f'.hom)))
          ((KernelFork.isLimitMapConeEquiv _ G).symm
            (KernelFork.isLimitMapConeEquiv _ (L ⋙ G)
              (isLimitOfPreserves (L ⋙ G) (kernelIsKernel f'.hom))))
  exact preservesLimit_of_iso_diagram G
    (show parallelPair (L.map f'.hom) 0 ≅ parallelPair f 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso iso) (Arrow.rightFunc.mapIso iso))

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.preservesFiniteColimits_c
omp_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocal
ization`。
形式化陈述：preservesFiniteColimits_comp_iff : PreservesFiniteColimits (L ⋙ G) ↔ Prese
rvesFiniteColimits G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.preservesFiniteColi
mits`：preservesFiniteColimits : PreservesFiniteColimits L
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Localization.functor_additive_iff`：functor_additive_iff {
E : Type*} [Category* E] [Preadditive E] [Preadditive D] [L.Additive] (G : D ⥤ E
) : G.Additive ↔ (L ⋙ G).Additive
· 使用定理 `CategoryTheory.ObjectProperty.SerreClassLocalization.instHasLeftCalculus
OfFractionsIsoModSerre`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
 [inst_1 : CategoryTheory.Abelian C]   (P : CategoryTheory.ObjectProperty C) [in
st_2…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_initial_objec
t`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [in
st_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoprod
ucts`：preservesBinaryBiproducts_of_preservesBinaryCoproducts [PreservesColimitsO
fShape (Discrete WalkingPair) F] : PreservesBinaryBiproducts F whe…
· 使用定理 `CategoryTheory.Functor.additive_of_preservesBinaryBiproducts`：additive_o
f_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F] [
PreservesBinaryBiproducts F] : Additive F where ma…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Functor.preservesFiniteColimits_tfae`：preservesFiniteColi
mits_tfae : List.TFAE [ forall (S : ShortComplex C), S.ShortExact -> (S.map F).E
xact ∧ Epi (F.map S.g), forall (S : Short…
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Localization.essSurj_mapArrow`：∀ {C : Type u_1} {D : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] (L : Categor…
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Arrow.rightFunc_map`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C]   {Y X : CategoryTheory.Comma (CategoryTheory.Functor.id C)
 (CategoryTheory.Functor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 36 条，此处仅展示前 30 条）
-/
lemma preservesFiniteColimits_comp_iff :
    PreservesFiniteColimits (L ⋙ G) ↔ PreservesFiniteColimits G := by
  let := abelian L P
  have := preservesFiniteColimits L P
  refine ⟨fun _ ↦ ?_, fun _ ↦ comp_preservesFiniteColimits _ _⟩
  have := (Localization.functor_additive_iff L P.isoModSerre G).mpr (by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (L ⋙ G)
    exact Functor.additive_of_preservesBinaryBiproducts _)
  refine ((Functor.preservesFiniteColimits_tfae G).out 2 3).mp (fun _ _ f ↦ ?_)
  obtain ⟨f', ⟨iso⟩⟩ :=
    (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
  have : PreservesColimit (parallelPair (L.map f'.hom) 0) G :=
    preservesColimit_of_preserves_colimit_cocone
      (CokernelCofork.isColimitMapCoconeEquiv _ _
        (isColimitOfPreserves L (cokernelIsCokernel f'.hom)))
          ((CokernelCofork.isColimitMapCoconeEquiv _ G).symm
            (CokernelCofork.isColimitMapCoconeEquiv _ (L ⋙ G)
              (isColimitOfPreserves (L ⋙ G) (cokernelIsCokernel f'.hom))))
  exact preservesColimit_of_iso_diagram G
    (show parallelPair (L.map f'.hom) 0 ≅ parallelPair f 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso iso) (Arrow.rightFunc.mapIso iso))
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.exactFunctor_comp_iff** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：exactFunctor_comp_iff : exactFunctor _ _ (L ⋙ G) ↔ exactFunctor _ _ G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.preservesFiniteLimi
ts_comp_iff`：preservesFiniteLimits_comp_iff : PreservesFiniteLimits (L ⋙ G) ↔ Pr
eservesFiniteLimits G
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.preservesFiniteColi
mits_comp_iff`：preservesFiniteColimits_comp_iff : PreservesFiniteColimits (L ⋙ G
) ↔ PreservesFiniteColimits G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma exactFunctor_comp_iff :
    exactFunctor _ _ (L ⋙ G) ↔ exactFunctor _ _ G := by
  simp [preservesFiniteLimits_comp_iff L P, preservesFiniteColimits_comp_iff L P]

variable (E)

set_option backward.defeqAttrib.useBackward true in
/-- When `L : C ⥤ D` is a localization functor with respect to a Serre class
in the abelian category `C`, this is the functor `(D ⥤ₑ E) ⥤ C ⥤ₑ E`
obtained by precomposition with `L`. -/
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.whiskeringLeft** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：whiskeringLeft : (D ⥤ₑ E) ⥤ C ⥤ₑ E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `L : C ⥤ D` is a localization functor with respect to a Serre class
in the abelian category `C`, this is the functor `(D ⥤ₑ E) ⥤ C ⥤ₑ E`
obtained by precomposition with `L`.
-/
def whiskeringLeft : (D ⥤ₑ E) ⥤ C ⥤ₑ E :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (Functor.whiskeringLeft _ _ _).obj L) (fun G ↦ by
      dsimp
      simpa only [exactFunctor_comp_iff L P] using G.property)

@[simp]
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.whiskeringLeft_obj_obj** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：whiskeringLeft_obj_obj (G : D ⥤ₑ E) : ((whiskeringLeft L P E).obj G).obj =
 L ⋙ G.obj
参数：G : D ⥤ₑ E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskeringLeft_obj_obj (G : D ⥤ₑ E) :
    ((whiskeringLeft L P E).obj G).obj = L ⋙ G.obj := rfl

/-- When `L : C ⥤ D` is a localization functor with respect to a Serre class
in the abelian category `C`, the functor `whiskeringLeft L P E: (D ⥤ₑ E) ⥤ C ⥤ₑ E`
is fully faithful. -/
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.fullyFaithfulWhiskeringLe
ft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalizati
on`。
形式化陈述：fullyFaithfulWhiskeringLeft : (whiskeringLeft L P E).FullyFaithful
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `L : C ⥤ D` is a localization functor with respect to a Serre class
in the abelian category `C`, the functor `whiskeringLeft L P E: (D ⥤ₑ E) ⥤ C ⥤ₑ 
E`
is fully faithful.
-/
noncomputable def fullyFaithfulWhiskeringLeft :
    (whiskeringLeft L P E).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
    ((exactFunctor D E).fullyFaithfulι.comp
      (Localization.fullyFaithfulWhiskeringLeft L P.isoModSerre E))
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (whiskeringLeft L P E).Faithful :=
  (fullyFaithfulWhiskeringLeft L P E).faithful
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (whiskeringLeft L P E).Full :=
  (fullyFaithfulWhiskeringLeft L P E).full

/-- Let `L : C ⥤ D` be a localization functor with respect to a Serre class `P`
in the abelian category `C`. If `G : C ⥤ₑ E` is an exact functor to an abelian
category, it "factors" through `D` (i.e. it is in the essential image of
`whiskeringLeft L P E : (D ⥤ₑ E) ⥤ C ⥤ₑ E`) iff `G` inverts the class
of morphisms `P.isoModSerre`. -/
/-
**CategoryTheory.ObjectProperty.SerreClassLocalization.essImage_whiskeringLeft**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.SerreClassLocalization`。
形式化陈述：essImage_whiskeringLeft : (whiskeringLeft L P E).essImage = fun G => P.iso
ModSerre.IsInvertedBy G.obj
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.iff_of_iso`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory
.Category.{v', u'} D]   (W : CategoryTheory.M…
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.of_comp`：of_comp {C₁ C₂ C₃ 
: Type*} [Category* C₁] [Category* C₂] [Category* C₃] (W : MorphismProperty C₁) 
(F : C₁ ⥤ C₂) (hF : W.IsInvertedBy F) (G :…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用引理 `CategoryTheory.ObjectProperty.SerreClassLocalization.exactFunctor_comp_i
ff`：exactFunctor_comp_iff : exactFunctor _ _ (L ⋙ G) ↔ exactFunctor _ _ G
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
· 使用定理 `CategoryTheory.instIsClosedUnderIsomorphismsFunctorExactFunctor`：∀ (C : 
Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D],   (CategoryTheory.e…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj

--- 原说明 ---
Let `L : C ⥤ D` be a localization functor with respect to a Serre class `P`
in the abelian category `C`. If `G : C ⥤ₑ E` is an exact functor to an abelian
category, it "factors" through `D` (i.e. it is in the essential image of
`whiskeringLeft L P E : (D ⥤ₑ E) ⥤ C ⥤ₑ E`) iff `G` inverts the class
of morphisms `P.isoModSerre`.
-/
lemma essImage_whiskeringLeft :
    (whiskeringLeft L P E).essImage =
      fun G ↦ P.isoModSerre.IsInvertedBy G.obj := by
  ext F
  refine ⟨?_, fun hF ↦ ?_⟩
  · rintro ⟨G, ⟨e⟩⟩
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso _
      (show L ⋙ G.obj ≅ F.obj from (ObjectProperty.ι _).mapIso e)]
    exact MorphismProperty.IsInvertedBy.of_comp _ _ (Localization.inverts L _) _
  · refine ⟨⟨Localization.lift F.obj hF L, ?_⟩,
      ⟨ObjectProperty.isoMk _ (Localization.fac F.obj hF L)⟩⟩
    rw [← exactFunctor_comp_iff L P]
    exact ObjectProperty.prop_of_iso _ (Localization.fac F.obj hF L).symm F.property

end SerreClassLocalization

end ObjectProperty

end CategoryTheory

