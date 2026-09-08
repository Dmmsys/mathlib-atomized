/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties

/-!
# Epimorphisms with an injective kernel

In this file, we define the class of morphisms `epiWithInjectiveKernel` in an
abelian category. We show that this property of morphisms is multiplicative.

This shall be used in the file `Mathlib/Algebra/Homology/Factorizations/Basic.lean` in
order to define morphisms of cochain complexes which satisfy this property
degreewise.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

variable {C : Type*} [Category* C] [Abelian C]

namespace Abelian

/-- The class of morphisms in an abelian category that are epimorphisms
and have an injective kernel. -/
/-
**CategoryTheory.Abelian.epiWithInjectiveKernel** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Abelian`。
形式化陈述：epiWithInjectiveKernel : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of morphisms in an abelian category that are epimorphisms
and have an injective kernel.
-/
def epiWithInjectiveKernel : MorphismProperty C :=
  fun _ _ f => Epi f ∧ Injective (kernel f)

/-- A morphism `g : X ⟶ Y` is epi with an injective kernel iff there exists a morphism
`f : I ⟶ X` with `I` injective such that `f ≫ g = 0` and
the short complex `I ⟶ X ⟶ Y` has a splitting. -/
/-
**CategoryTheory.Abelian.epiWithInjectiveKernel_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Abelian`。
形式化陈述：epiWithInjectiveKernel_iff {X Y : C} (g : X ⟶ Y) : epiWithInjectiveKernel 
g ↔ exists (I : C) (_ : Injective I) (f : I ⟶ X) (w : f ≫ g = 0), Nonempty (Shor
tComplex.mk f g w).Splitting
参数：g : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
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
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `CategoryTheory.Injective.comp_factorThru`：comp_factorThru {J X Y : C} [I
njective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : f ≫ factorThru g f = g
· 使用定理 `CategoryTheory.ShortComplex.Splitting.s_g`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S :
 CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.ShortComplex.Splitting.shortExact`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   {S : CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsRegularEpi`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {B X : C} {f : X ⟶ B} [h : CategoryTheory.IsR
egularEpi f],   CategoryTheory.Effe…
· 使用定理 `CategoryTheory.instIsRegularEpiOfIsSplitEpi`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplitEp
i f],   CategoryTheory.IsRegularE…
· 使用定理 `CategoryTheory.Injective.of_iso`：of_iso {P Q : C} (i : P ≅ Q) (hP : Inje
ctive P) : Injective Q

--- 原说明 ---
A morphism `g : X ⟶ Y` is epi with an injective kernel iff there exists a morphi
sm
`f : I ⟶ X` with `I` injective such that `f ≫ g = 0` and
the short complex `I ⟶ X ⟶ Y` has a splitting.
-/
lemma epiWithInjectiveKernel_iff {X Y : C} (g : X ⟶ Y) :
    epiWithInjectiveKernel g ↔ ∃ (I : C) (_ : Injective I) (f : I ⟶ X) (w : f ≫ g = 0),
      Nonempty (ShortComplex.mk f g w).Splitting := by
  constructor
  · rintro ⟨_, _⟩
    let S := ShortComplex.mk (kernel.ι g) g (by simp)
    exact ⟨_, inferInstance, _, S.zero,
      ⟨ShortComplex.Splitting.ofExactOfRetraction S
        (S.exact_of_f_is_kernel (kernelIsKernel g)) (Injective.factorThru (𝟙 _) (kernel.ι g))
        (by simp [S]) inferInstance⟩⟩
  · rintro ⟨I, _, f, w, ⟨σ⟩⟩
    have : IsSplitEpi g := ⟨σ.s, σ.s_g⟩
    let e : I ≅ kernel g :=
      IsLimit.conePointUniqueUpToIso σ.shortExact.fIsKernel (limit.isLimit _)
    exact ⟨inferInstance, Injective.of_iso e inferInstance⟩
/-
**CategoryTheory.Abelian.epiWithInjectiveKernel_of_iso** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Abelian`。
形式化陈述：epiWithInjectiveKernel_of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] : epiWithInj
ectiveKernel f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.epiWithInjectiveKernel_iff`：epiWithInjectiveKerne
l_iff {X Y : C} (g : X ⟶ Y) : epiWithInjectiveKernel g ↔ exists (I : C) (_ : Inj
ective I) (f : I ⟶ X) (w : f ≫ g = 0), …
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
-/
lemma epiWithInjectiveKernel_of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    epiWithInjectiveKernel f := by
  rw [epiWithInjectiveKernel_iff]
  exact ⟨0, inferInstance, 0, by simp,
    ⟨ShortComplex.Splitting.ofIsZeroOfIsIso _ (isZero_zero C) (by assumption)⟩⟩
/-
**CategoryTheory.Abelian.epiWithInjectiveKernel_iff_of_isZero** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Abelian`。
形式化陈述：epiWithInjectiveKernel_iff_of_isZero {X Y : C} (f : X ⟶ Y) (hY : IsZero Y)
 : epiWithInjectiveKernel f ↔ Injective X
参数：f : X ⟶ Y；hY : IsZero Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `CategoryTheory.Limits.IsZero.epi`：epi (h : IsZero X) {Y : C} (f : Y ⟶ X)
 : Epi f where left_cancellation _ _ _
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `CategoryTheory.Injective.iso_iff`：iso_iff {P Q : C} (i : P ≅ Q) : Inject
ive P ↔ Injective Q
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma epiWithInjectiveKernel_iff_of_isZero {X Y : C} (f : X ⟶ Y) (hY : IsZero Y) :
    epiWithInjectiveKernel f ↔ Injective X := by
  simp only [epiWithInjectiveKernel, hY.epi f, true_and]
  exact Injective.iso_iff
    { hom := kernel.ι f
      inv := kernel.lift _ (𝟙 X) (hY.eq_of_tgt _ _) }
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (epiWithInjectiveKernel : MorphismProperty C).IsMultiplicative where
  id_mem _ := epiWithInjectiveKernel_of_iso _
  comp_mem {X Y Z} g₁ g₂ hg₁ hg₂ := by
    rw [epiWithInjectiveKernel_iff] at hg₁ hg₂ ⊢
    obtain ⟨I₁, _, f₁, w₁, ⟨σ₁⟩⟩ := hg₁
    obtain ⟨I₂, _, f₂, w₂, ⟨σ₂⟩⟩ := hg₂
    refine ⟨I₁ ⊞ I₂, inferInstance, biprod.fst ≫ f₁ + biprod.snd ≫ f₂ ≫ σ₁.s, ?_, ⟨?_⟩⟩
    · ext
      · simp [reassoc_of% w₁]
      · simp [reassoc_of% σ₁.s_g, w₂]
    · exact
        { r := σ₁.r ≫ biprod.inl + g₁ ≫ σ₂.r ≫ biprod.inr
          s := σ₂.s ≫ σ₁.s
          f_r := by
            ext
            · simp [σ₁.f_r]
            · simp [reassoc_of% w₁]
            · simp
            · simp [reassoc_of% σ₁.s_g, σ₂.f_r]
          s_g := by simp [reassoc_of% σ₁.s_g, σ₂.s_g]
          id := by
            dsimp
            have h := g₁ ≫= σ₂.id =≫ σ₁.s
            simp only [add_comp, assoc, comp_add, id_comp] at h
            rw [← σ₁.id, ← h]
            simp only [comp_add, add_comp, assoc, BinaryBicone.inl_fst_assoc,
              BinaryBicone.inr_fst_assoc, zero_comp, comp_zero, add_zero,
              BinaryBicone.inl_snd_assoc, BinaryBicone.inr_snd_assoc, zero_add]
            abel }

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (epiWithInjectiveKernel (C := C)).IsStableUnderRetracts where
  of_retract := by
    rintro X' Y' X Y f' f r ⟨_, hf⟩
    have : Epi f' :=
      (MorphismProperty.epimorphisms C).of_retract r (.infer_property _)
    let r' : Retract (kernel f') (kernel f) :=
      { i := kernel.map _ _ r.i.left r.i.right (Arrow.w r.i).symm
        r := kernel.map _ _ r.r.left r.r.right (Arrow.w r.r).symm
        retract := by ext; simp }
    exact ⟨inferInstance, r'.injective⟩
/-
**CategoryTheory.Abelian.epiWithInjectiveKernel.hasLiftingProperty** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Abelian.epiWithInjectiveKernel`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Abelian C] {X Y : C}   {p : X ⟶ Y},   CategoryTheory.Abelian.epiWi
thInjectiveKernel p →     ∀ {A B : C} (i : A ⟶ B) [CategoryTheory.Mono i], Categ
oryTheory.HasLiftingProperty i p
参数：i : A ⟶ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.epiWithInjectiveKernel_iff`：epiWithInjectiveKerne
l_iff {X Y : C} (g : X ⟶ Y) : epiWithInjectiveKernel g ↔ exists (I : C) (_ : Inj
ective I) (f : I ⟶ X) (w : f ≫ g = 0), …
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用引理 `CategoryTheory.Injective.hasLiftingProperty_of_isZero`：hasLiftingPropert
y_of_isZero {A B I Z : C} (i : A ⟶ B) [Mono i] [Injective I] (p : I ⟶ Z) (hZ : I
sZero Z) : HasLiftingProperty i p where sq_…
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ShortComplex.Splitting.f_r`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S :
 CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.ShortComplex.Splitting.s_r`：s_r (s : S.Splitting) : s.s ≫
 s.r = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.ShortComplex.Splitting.s_g`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S :
 CategoryTheory.ShortComplex C}…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.Splitting.id`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
-/
lemma epiWithInjectiveKernel.hasLiftingProperty
    {X Y : C} {p : X ⟶ Y} (hp : epiWithInjectiveKernel p)
    {A B : C} (i : A ⟶ B) [Mono i] :
    HasLiftingProperty i p := by
  suffices (MorphismProperty.monomorphisms C).rlp p from this _ inferInstance
  rw [epiWithInjectiveKernel_iff] at hp
  obtain ⟨I, _, s, hs, ⟨σ⟩⟩ := hp
  have hI : (MorphismProperty.monomorphisms C).rlp (0 : I ⟶ 0) :=
    fun _ _ _ _ ↦ Injective.hasLiftingProperty_of_isZero _ _ (isZero_zero C)
  refine MorphismProperty.of_isPullback (f' := σ.r) (f := 0) ⟨by simp, ⟨?_⟩⟩ hI
  refine PullbackCone.IsLimit.mk _ (fun t ↦ t.fst ≫ s + t.snd ≫ σ.s)
    (fun t ↦ by simp [dsimp% σ.f_r]) (fun t ↦ by simp [hs, dsimp% σ.s_g]) (fun t m hm₁ hm₂ ↦ ?_)
  simp [← hm₁, ← hm₂, ← Preadditive.comp_add, dsimp% σ.id]

end Abelian

end CategoryTheory

