/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor

/-!
# Functorial resolutions give derivability structures

In this file, we provide a constructor for right derivability structures.
We assume that `Φ : LocalizerMorphism W₁ W₂` is given by
a fully faithful functor `Φ.functor : C₁ ⥤ C₂` and that we have a resolution
functor `ρ : C₂ ⥤ C₁` with a natural transformation `i : 𝟭 C₂ ⟶ ρ ⋙ Φ.functor`
such that `W₂ (i.app X₂)` for any `X₂ : C₂`. If we assume
that `W₁` is induced by `W₂`, that `W₂` is multiplicative and has
the two-out-of-three property, then `Φ` is a right derivability structure.

-/

@[expose] public section

namespace CategoryTheory

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)
  {ρ : C₂ ⥤ C₁} (i : 𝟭 C₂ ⟶ ρ ⋙ Φ.functor) (hi : ∀ X₂, W₂ (i.app X₂))
  (hW₁ : W₁ = W₂.inverseImage Φ.functor)

include hi in
/-
**CategoryTheory.LocalizerMorphism.hasRightResolutions_arrow_of_functorial_resol
utions** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：hasRightResolutions_arrow_of_functorial_resolutions : Φ.arrow.HasRightReso
lutions
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma hasRightResolutions_arrow_of_functorial_resolutions :
    Φ.arrow.HasRightResolutions :=
  fun f ↦
    ⟨{ X₁ := Arrow.mk (ρ.map f.hom)
       w := Arrow.homMk (i.app _) (i.app _) (i.naturality f.hom).symm
       hw := ⟨hi _, hi _⟩ }⟩

namespace functorialRightResolutions
open CategoryTheory.Functor

variable {Φ i}

/-- If `Φ : LocalizerMorphism W₁ W₂` corresponds to a class `W₁` that is
the inverse image of `W₂` by the functor `Φ.functor` and that we
have functorial right resolutions, then this is a morphism of localizers
in the other direction. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.functorialRightResolutions.localizerMorphismI
nv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.LocalizerMorphism.functorialRightRe
solutions`。
形式化陈述：localizerMorphismInv [W₂.HasTwoOutOfThreeProperty] : LocalizerMorphism W₂ 
W₁ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Φ : LocalizerMorphism W₁ W₂` corresponds to a class `W₁` that is
the inverse image of `W₂` by the functor `Φ.functor` and that we
have functorial right resolutions, then this is a morphism of localizers
in the other direction.
-/
def localizerMorphismInv [W₂.HasTwoOutOfThreeProperty] :
    LocalizerMorphism W₂ W₁ where
  functor := ρ
  map := by
    rw [hW₁]
    intro X Y f hf
    have := i.naturality f
    dsimp at this
    simp only [MorphismProperty.inverseImage_iff]
    rw [← W₂.precomp_iff _ _ (hi X), ← this]
    exact W₂.comp_mem _ _ hf (hi Y)

variable [Φ.functor.Full] [Φ.functor.Faithful]

variable (i) in
/-- If `Φ : LocalizerMorphism W₁ W₂` corresponds to a class `W₁` that is
induced by `W₂` via the fully faithful functor `Φ.functor` and we
have functorial right resolutions given by a functor `ρ : C₂ ⥤ C₁`, then
this is the natural transformation `𝟭 C₁ ⟶ Φ.functor ⋙ ρ` induced
by `i : 𝟭 C₂ ⟶ ρ ⋙ Φ.functor`. -/
/-
**CategoryTheory.LocalizerMorphism.functorialRightResolutions.** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.LocalizerMorphism.functorialRightResolutions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Φ : LocalizerMorphism W₁ W₂` corresponds to a class `W₁` that is
induced by `W₂` via the fully faithful functor `Φ.functor` and we
have functorial right resolutions given by a functor `ρ : C₂ ⥤ C₁`, then
this is the natural transformation `𝟭 C₁ ⟶ Φ.functor ⋙ ρ` induced
by `i : 𝟭 C₂ ⟶ ρ ⋙ Φ.functor`.
-/
noncomputable def ι : 𝟭 C₁ ⟶ Φ.functor ⋙ ρ :=
  ((whiskeringRight C₁ C₁ C₂).obj Φ.functor).preimage (whiskerLeft Φ.functor i)

@[simp]
/-
**CategoryTheory.LocalizerMorphism.functorialRightResolutions.** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.LocalizerMorphism.functorialRightResolutions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Φ_functor_map_ι_app (X₁ : C₁) :
    Φ.functor.map ((ι i).app X₁) = i.app (Φ.functor.obj X₁) :=
  NatTrans.congr_app (((whiskeringRight C₁ C₁ C₂).obj Φ.functor).map_preimage
    (X := 𝟭 C₁) (Y := Φ.functor ⋙ ρ) (whiskerLeft Φ.functor i)) X₁

include hW₁ hi in
/-
**CategoryTheory.LocalizerMorphism.functorialRightResolutions.W** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.LocalizerMorphism.functorialRightResolutions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma W₁_ι_app (X₁ : C₁) : W₁ ((ι i).app X₁) := by
  simpa [hW₁] using hi (Φ.functor.obj X₁)

end functorialRightResolutions

variable [Φ.functor.Full] [Φ.functor.Faithful] [W₂.HasTwoOutOfThreeProperty]

open functorialRightResolutions
include hi hW₁

/-
**CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_functorial_right_re
solutions** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isLocalizedEquivalence_of_functorial_right_resolutions : Φ.IsLocalizedEqui
valence
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_unit_of_unit`
：isLocalizedEquivalence_of_unit_of_unit (Ψ : LocalizerMorphism W₂ W₁) (ε₁ : 𝟭 C₁
 ⟶ Φ.functor ⋙ Ψ.functor) (ε₂ : 𝟭 C₂ ⟶ Ψ.functor ⋙ Φ.functor)…
· 使用引理 `CategoryTheory.LocalizerMorphism.functorialRightResolutions.W₁_ι_app`：W₁
_ι_app (X₁ : C₁) : W₁ ((ι i).app X₁)
-/
lemma isLocalizedEquivalence_of_functorial_right_resolutions :
    Φ.IsLocalizedEquivalence :=
  Φ.isLocalizedEquivalence_of_unit_of_unit (localizerMorphismInv hi hW₁) (ι i) i
    (W₁_ι_app hi hW₁) hi

variable [W₂.IsMultiplicative]
/-
**CategoryTheory.LocalizerMorphism.isConnected_rightResolution_of_functorial_res
olutions** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isConnected_rightResolution_of_functorial_resolutions (X₂ : C₂) : letI : W
₁.IsMultiplicative
参数：X₂ : C₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instInverseImage`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : Cate
goryTheory.Category.{v', u'} D]   {P : CategoryTheory.M…
· 使用定理 `CategoryTheory.zigzag_isPreconnected`：zigzag_isPreconnected (h : forall 
j₁ j₂ : J, Zigzag j₁ j₂) : IsPreconnected J
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toIsStableUnder
Composition`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Is…
· 使用定理 `CategoryTheory.LocalizerMorphism.RightResolution.hw`：∀ {C₁ : Type u_1} {
C₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
· 使用定理 `CategoryTheory.Zigzag.of_hom`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₁ ⟶ j₂), CategoryTheory.Zigzag j₁ j₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.LocalizerMorphism.functorialRightResolutions.Φ_functor_ma
p_ι_app`：Φ_functor_map_ι_app (X₁ : C₁) : Φ.functor.map ((ι i).app X₁) = i.app (Φ
.functor.obj X₁)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Zigzag.of_inv`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₂ ⟶ j₁), CategoryTheory.Zigzag j₁ j₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma isConnected_rightResolution_of_functorial_resolutions (X₂ : C₂) :
    letI : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
    IsConnected (Φ.RightResolution X₂) := by
  have : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
  have : Nonempty (Φ.RightResolution X₂) := ⟨{ hw := hi X₂, .. }⟩
  have : IsPreconnected (Φ.RightResolution X₂) :=
    zigzag_isPreconnected (fun R₀ R₄ ↦
      calc
        Zigzag R₀ { hw := W₂.comp_mem _ _ R₀.hw (hi _), .. } :=
          Zigzag.of_hom { f := (ι i).app R₀.X₁ }
        Zigzag (J := Φ.RightResolution X₂) _ { hw := hi X₂, .. } :=
          Zigzag.of_inv
            { f := ρ.map R₀.w
              comm := (i.naturality R₀.w).symm }
        Zigzag (J := Φ.RightResolution X₂) _ { hw := W₂.comp_mem _ _ R₄.hw (hi _), .. } :=
          Zigzag.of_hom
            { f := ρ.map R₄.w
              comm := (i.naturality R₄.w).symm }
        Zigzag _ R₄ := Zigzag.of_inv { f := (ι i).app R₄.X₁ })
  constructor
/-
**CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_of_functorial_re
solutions** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isRightDerivabilityStructure_of_functorial_resolutions : Φ.IsRightDerivabi
lityStructure
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instInverseImage`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : Cate
goryTheory.Category.{v', u'} D]   {P : CategoryTheory.M…
· 使用引理 `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_functorial_ri
ght_resolutions`：isLocalizedEquivalence_of_functorial_right_resolutions : Φ.IsLo
calizedEquivalence
· 使用引理 `CategoryTheory.LocalizerMorphism.hasRightResolutions_arrow_of_functorial
_resolutions`：hasRightResolutions_arrow_of_functorial_resolutions : Φ.arrow.HasR
ightResolutions
· 使用引理 `CategoryTheory.LocalizerMorphism.isConnected_rightResolution_of_functori
al_resolutions`：isConnected_rightResolution_of_functorial_resolutions (X₂ : C₂) 
: letI : W₁.IsMultiplicative
· 使用引理 `CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure.mk'`：mk' [
Φ.IsLocalizedEquivalence] : Φ.IsRightDerivabilityStructure
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
-/
lemma isRightDerivabilityStructure_of_functorial_resolutions :
    Φ.IsRightDerivabilityStructure := by
  have : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
  have := Φ.isLocalizedEquivalence_of_functorial_right_resolutions i hi hW₁
  have := Φ.hasRightResolutions_arrow_of_functorial_resolutions i hi
  have := Φ.isConnected_rightResolution_of_functorial_resolutions i hi hW₁
  apply IsRightDerivabilityStructure.mk'

end LocalizerMorphism

end CategoryTheory

