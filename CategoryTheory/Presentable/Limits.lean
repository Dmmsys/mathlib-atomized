/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-!
# Colimits of presentable objects

In this file, we show that `κ`-accessible functors (to the category of types)
are stable under limits indexed by a category `K` such that
`HasCardinalLT (Arrow K) κ`.
In particular, `κ`-presentable objects are stable by colimits indexed
by a category `K` such that `HasCardinalLT (Arrow K) κ`.

-/

@[expose] public section

universe w w' v' v u' u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C]

namespace Functor

namespace Accessible

namespace Limits

section

variable {K : Type u'} [Category.{v'} K] {F : K ⥤ C ⥤ Type w'}
  (c : Cone F) (hc : ∀ (Y : C), IsLimit (((evaluation _ _).obj Y).mapCone c))
  (κ : Cardinal.{w}) [Fact κ.IsRegular]
  (hK : HasCardinalLT (Arrow K) κ)
  {J : Type w} [SmallCategory J] [IsCardinalFiltered J κ]
  {X : J ⥤ C} (cX : Cocone X)
  (hF : ∀ (k : K), IsColimit ((F.obj k).mapCocone cX))

namespace isColimitMapCocone

include hc hF hK

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.Accessible.Limits.isColimitMapCocone.surjective** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.Accessible.Limits.isColimitMapCocone`
。
形式化陈述：surjective (x : c.pt.obj cX.pt) : exists (j : J) (x' : c.pt.obj (X.obj j))
, x = (c.pt.mapCocone cX).ι.app j x'
参数：x : c.pt.obj cX.pt。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`：jointly_sur
jective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t) (x : t.pt
) : exists j y, t.ι.app j y = x
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `CategoryTheory.hasCardinalLT_of_hasCardinalLT_arrow`：hasCardinalLT_of_ha
sCardinalLT_arrow {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} (h : HasCardi
nalLT (Arrow C) κ) : HasCardinalLT C κ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`：isColimit
_eq_iff' {t : Cocone F} (ht : IsColimit t) {i : J} (x y : F.obj i) : t.ι.app i x
 = t.ι.app i y ↔ exists (j : _) (f : i ⟶ j), F.map …
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.IsCardinalFiltered.coeq_condition`：coeq_condition (k : K)
 : f k ≫ coeqHom f hK = toCoeq f hK
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.Types.isLimitEquivSections_apply`：isLimitEquivSect
ions_apply {c : Cone F} (t : IsLimit c) (j : J) (x : c.pt) : (isLimitEquivSectio
ns t x : forall j, F.obj j) j = c.π.app j x
· 使用定理 `CategoryTheory.Limits.Types.isLimitEquivSections_symm_apply`：isLimitEqui
vSections_symm_apply {c : Cone F} (t : IsLimit c) (x : F.sections) (j : J) : dsi
mp% c.π.app j ((isLimitEquivSections t).symm x) =…
-/
lemma surjective (x : c.pt.obj cX.pt) :
    ∃ (j : J) (x' : c.pt.obj (X.obj j)), x = (c.pt.mapCocone cX).ι.app j x' := by
  have := isFiltered_of_isCardinalFiltered J κ
  obtain ⟨y, hy⟩ := (Types.isLimitEquivSections (hc cX.pt)).symm.surjective x
  obtain ⟨j₀, z, hz⟩ : ∃ (j₀ : J) (z : (k : K) → (F.obj k).obj (X.obj j₀)),
      ∀ (k : K), y.1 k = (F.obj k).map (cX.ι.app j₀) (z k) := by
    have H (k : K) := Types.jointly_surjective_of_isColimit (hF k) (y.1 k)
    let j (k : K) : J := (H k).choose
    let z (k : K) : (F.obj k).obj (X.obj (j k)) := (H k).choose_spec.choose
    have hz (k : K) : (F.obj k).map (cX.ι.app (j k)) (z k) = y.1 k :=
      (H k).choose_spec.choose_spec
    exact ⟨IsCardinalFiltered.max j (hasCardinalLT_of_hasCardinalLT_arrow hK),
      fun k ↦ (F.obj k).map (X.map (IsCardinalFiltered.toMax j _ k)) (z k),
        fun k ↦ by rw [← hz, ← comp_apply, ← Functor.map_comp, cX.w]; rfl⟩
  obtain ⟨j₁, α, hα⟩ : ∃ (j₁ : J) (α : j₀ ⟶ j₁), ∀ ⦃k k' : K⦄ (φ : k ⟶ k'),
      (F.obj k').map (X.map α) ((F.map φ).app _ (z k)) =
        (F.obj k').map (X.map α) (z k') := by
    have H {k k' : K} (φ : k ⟶ k') :=
      (Types.FilteredColimit.isColimit_eq_iff' (ht := hF k')
        (x := (F.map φ).app _ (z k)) (y := z k')).1 (by
          dsimp at hz ⊢
          simpa only [← NatTrans.naturality_apply, ← hz] using! y.2 φ)
    let j {k k' : K} (φ : k ⟶ k') : J := (H φ).choose
    let g {k k' : K} (φ : k ⟶ k') : j₀ ⟶ j φ := (H φ).choose_spec.choose
    have hg {k k' : K} (φ : k ⟶ k') :
        (F.obj k').map (X.map (g φ)) ((F.map φ).app _ (z k)) =
          (F.obj k').map (X.map (g φ)) (z k') := (H φ).choose_spec.choose_spec
    obtain ⟨j₁, α, β, hα⟩ : ∃ (j₁ : J) (α : j₀ ⟶ j₁)
        (β : ∀ ⦃k k' : K⦄ (φ : k ⟶ k'), j φ ⟶ j₁),
        ∀ ⦃k k' : K⦄ (φ : k ⟶ k'), α = g φ ≫ β φ := by
      let j'' (f : Arrow K) : J := j f.hom
      let ψ (f : Arrow K) : j₀ ⟶ IsCardinalFiltered.max j'' hK :=
        g f.hom ≫ IsCardinalFiltered.toMax j'' hK f
      refine ⟨IsCardinalFiltered.coeq ψ hK, IsCardinalFiltered.toCoeq ψ hK,
        fun k k' φ ↦ IsCardinalFiltered.toMax j'' hK φ ≫ IsCardinalFiltered.coeqHom ψ hK,
        fun k k' φ ↦ ?_⟩
      simpa [ψ] using! (IsCardinalFiltered.coeq_condition ψ hK (Arrow.mk φ)).symm
    exact ⟨j₁, α, fun k k' φ ↦ by simp [hα φ, hg]⟩
  let s : (F ⋙ (evaluation C (Type w')).obj (X.obj j₁)).sections :=
    { val k := (F.obj k).map (X.map α) (z k)
      property {k k'} φ := by
        dsimp
        rw [NatTrans.naturality_apply, ← hα φ] }
  refine ⟨j₁, (Types.isLimitEquivSections (hc (X.obj j₁))).symm s, ?_⟩
  apply (Types.isLimitEquivSections (hc cX.pt)).injective
  rw [← hy, Equiv.apply_symm_apply]
  ext k
  have h₁ := Types.isLimitEquivSections_apply (hc cX.pt) k
    (c.pt.map (cX.ι.app j₁) ((Types.isLimitEquivSections (hc (X.obj j₁))).symm s))
  have h₂ := Types.isLimitEquivSections_symm_apply (hc (X.obj j₁)) s k
  dsimp at h₁ h₂ ⊢
  rw [h₁, hz, NatTrans.naturality_apply, h₂, ← comp_apply, ← Functor.map_comp, cX.w]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.Accessible.Limits.isColimitMapCocone.injective** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Functor.Accessible.Limits.isColimitMapCocone`。
形式化陈述：injective (j : J) (x₁ x₂ : c.pt.obj (X.obj j)) (h : c.pt.map (cX.ι.app j) 
x₁ = c.pt.map (cX.ι.app j) x₂) : exists (j' : J) (α : j ⟶ j'), c.pt.map (X.map α
) x₁ = c.pt.map (X.map α) x₂
参数：j : J；x₁ x₂ : c.pt.obj (X.obj j)；h : c.pt.map (cX.ι.app j) x₁ = c.pt.map (cX.
ι.app j) x₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`：isColimit
_eq_iff' {t : Cocone F} (ht : IsColimit t) {i : J} (x y : F.obj i) : t.ι.app i x
 = t.ι.app i y ↔ exists (j : _) (f : i ⟶ j), F.map …
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `CategoryTheory.hasCardinalLT_of_hasCardinalLT_arrow`：hasCardinalLT_of_ha
sCardinalLT_arrow {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} (h : HasCardi
nalLT (Arrow C) κ) : HasCardinalLT C κ
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Types.isLimitEquivSections_symm_apply`：isLimitEqui
vSections_symm_apply {c : Cone F} (t : IsLimit c) (x : F.sections) (j : J) : dsi
mp% c.π.app j ((isLimitEquivSections t).symm x) =…
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用引理 `CategoryTheory.IsCardinalFiltered.coeq_condition`：coeq_condition (k : K)
 : f k ≫ coeqHom f hK = toCoeq f hK
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
-/
lemma injective (j : J) (x₁ x₂ : c.pt.obj (X.obj j))
    (h : c.pt.map (cX.ι.app j) x₁ = c.pt.map (cX.ι.app j) x₂) :
    ∃ (j' : J) (α : j ⟶ j'),
    c.pt.map (X.map α) x₁ = c.pt.map (X.map α) x₂ := by
  have := isFiltered_of_isCardinalFiltered J κ
  let y₁ := Types.isLimitEquivSections (hc (X.obj j)) x₁
  let y₂ := Types.isLimitEquivSections (hc (X.obj j)) x₂
  have hy₁ : (Types.isLimitEquivSections (hc (X.obj j))).symm y₁ = x₁ := by simp [y₁]
  have hy₂ : (Types.isLimitEquivSections (hc (X.obj j))).symm y₂ = x₂ := by simp [y₂]
  have H (k : K) := (Types.FilteredColimit.isColimit_eq_iff' (ht := hF k)
    (x := y₁.1 k) (y := y₂.1 k)).1 (by
      simp only [y₁, y₂, Types.isLimitEquivSections_apply]
      dsimp at h ⊢
      simp only [← NatTrans.naturality_apply, h])
  let j₁ (k : K) : J := (H k).choose
  let f (k : K) : j ⟶ j₁ k := (H k).choose_spec.choose
  have hf (k : K) : (F.obj k).map (X.map (f k)) (y₁.1 k) =
      (F.obj k).map (X.map (f k)) (y₂.1 k) :=
    (H k).choose_spec.choose_spec
  have hK' := hasCardinalLT_of_hasCardinalLT_arrow hK
  let ψ (k : K) : j ⟶ IsCardinalFiltered.max j₁ hK' :=
    f k ≫ IsCardinalFiltered.toMax j₁ hK' k
  refine ⟨IsCardinalFiltered.coeq ψ hK', IsCardinalFiltered.toCoeq ψ hK', ?_⟩
  apply (Types.isLimitEquivSections (hc _)).injective
  ext k
  simp only [Types.isLimitEquivSections_apply, ← hy₁, ← hy₂]
  have h₁ := Types.isLimitEquivSections_symm_apply (hc (X.obj j)) y₁ k
  have h₂ := Types.isLimitEquivSections_symm_apply (hc (X.obj j)) y₂ k
  dsimp at h₁ h₂ ⊢
  simp [h₁, h₂, ← IsCardinalFiltered.coeq_condition ψ hK' k, ψ, hf]

end isColimitMapCocone

/-- Auxiliary definition for `isCardinalAccessible_of_isLimit`. -/
/-
**CategoryTheory.Functor.Accessible.Limits.isColimitMapCocone** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Functor.Accessible.Limits`。
形式化陈述：isColimitMapCocone : IsColimit (c.pt.mapCocone cX)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用引理 `CategoryTheory.Functor.Accessible.Limits.isColimitMapCocone.surjective`：
surjective (x : c.pt.obj cX.pt) : exists (j : J) (x' : c.pt.obj (X.obj j)), x = 
(c.pt.mapCocone cX).ι.app j x'
· 使用引理 `CategoryTheory.Functor.Accessible.Limits.isColimitMapCocone.injective`：i
njective (j : J) (x₁ x₂ : c.pt.obj (X.obj j)) (h : c.pt.map (cX.ι.app j) x₁ = c.
pt.map (cX.ι.app j) x₂) : exists (j' : J) (α : j ⟶ j'), c.p…

--- 原说明 ---
Auxiliary definition for `isCardinalAccessible_of_isLimit`.
-/
noncomputable def isColimitMapCocone : IsColimit (c.pt.mapCocone cX) := by
  have := isFiltered_of_isCardinalFiltered J κ
  apply Types.FilteredColimit.isColimitOf'
  · exact isColimitMapCocone.surjective c hc κ hK cX hF
  · exact isColimitMapCocone.injective c hc κ hK cX hF

end

end Limits

end Accessible

/-
**CategoryTheory.Functor.isCardinalAccessible_of_isLimit** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：isCardinalAccessible_of_isLimit {K : Type u'} [Category.{v'} K] {F : K ⥤ C
 ⥤ Type w'} (c : Cone F) (hc : IsLimit c) (κ : Cardinal.{w}) [Fact κ.IsRegular] 
[HasLimitsOfShape K (Type w')] (hK : HasCardinalLT (Arrow K) κ) [forall k, (F.ob
j k).IsCardinalAccessible κ] : c.pt.IsCardinalAccessible κ where preservesColimi
tOfShape {J _ _}
参数：c : Cone F；hc : IsLimit c；κ : Cardinal.{w}；Type w'；hK : HasCardinalLT (Arrow 
K) κ；F.obj k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesColimitsOfShape_of_isCardinalAccessible`
：preservesColimitsOfShape_of_isCardinalAccessible [F.IsCardinalAccessible κ] (J 
: Type w) [SmallCategory J] [IsCardinalFiltered J κ] : Preser…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
lemma isCardinalAccessible_of_isLimit {K : Type u'} [Category.{v'} K] {F : K ⥤ C ⥤ Type w'}
    (c : Cone F) (hc : IsLimit c) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasLimitsOfShape K (Type w')] (hK : HasCardinalLT (Arrow K) κ)
    [∀ k, (F.obj k).IsCardinalAccessible κ] :
    c.pt.IsCardinalAccessible κ where
  preservesColimitOfShape {J _ _} := ⟨fun {X} ↦ ⟨fun {cX} hcX ↦ by
    have := fun k ↦ preservesColimitsOfShape_of_isCardinalAccessible (F.obj k) κ J
    exact ⟨Accessible.Limits.isColimitMapCocone c
      (fun Y ↦ isLimitOfPreserves ((evaluation C (Type w')).obj Y) hc) κ hK cX
      (fun k ↦ isColimitOfPreserves (F.obj k) hcX)⟩⟩⟩

end Functor

set_option backward.defeqAttrib.useBackward true in
/-- In case `C` is locally `w`-small, use `isCardinalPresentable_of_isColimit`. -/
/-
**CategoryTheory.isCardinalPresentable_of_isColimit'** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory`。
形式化陈述：isCardinalPresentable_of_isColimit' {K : Type u'} [Category.{v'} K] {Y : K
 ⥤ C} (c : Cocone Y) (hc : IsColimit c) (κ : Cardinal.{w}) [Fact κ.IsRegular] [H
asLimitsOfShape Kᵒᵖ (Type v)] (hK : HasCardinalLT (Arrow K) κ) [forall k, IsCard
inalPresentable (Y.obj k) κ] : IsCardinalPresentable c.pt κ
参数：c : Cocone Y；hc : IsColimit c；κ : Cardinal.{w}；Type v；hK : HasCardinalLT (Arr
ow K) κ；Y.obj k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isCardinalAccessible_of_isLimit`：isCardinalAccess
ible_of_isLimit {K : Type u'} [Category.{v'} K] {F : K ⥤ C ⥤ Type w'} (c : Cone 
F) (hc : IsLimit c) (κ : Cardinal.{w}) [Fact…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
In case `C` is locally `w`-small, use `isCardinalPresentable_of_isColimit`.
-/
lemma isCardinalPresentable_of_isColimit'
    {K : Type u'} [Category.{v'} K] {Y : K ⥤ C}
    (c : Cocone Y) (hc : IsColimit c) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasLimitsOfShape Kᵒᵖ (Type v)] (hK : HasCardinalLT (Arrow K) κ)
    [∀ k, IsCardinalPresentable (Y.obj k) κ] :
    IsCardinalPresentable c.pt κ := by
  have (k : Kᵒᵖ) : ((Y.op ⋙ coyoneda).obj k).IsCardinalAccessible κ := by
    dsimp; infer_instance
  exact Functor.isCardinalAccessible_of_isLimit
    (coyoneda.mapCone c.op) (isLimitOfPreserves _ hc.op) κ (by simpa)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.isCardinalPresentable_of_isColimit** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory`。
形式化陈述：isCardinalPresentable_of_isColimit [LocallySmall.{w} C] {K : Type u'} [Cat
egory.{v'} K] [HasLimitsOfShape Kᵒᵖ (Type w)] {Y : K ⥤ C} (c : Cocone Y) (hc : I
sColimit c) (κ : Cardinal.{w}) [Fact κ.IsRegular] (hK : HasCardinalLT (Arrow K) 
κ) [forall k, IsCardinalPresentable (Y.obj k) κ] : IsCardinalPresentable c.pt κ
参数：Type w；c : Cocone Y；hc : IsColimit c；κ : Cardinal.{w}；hK : HasCardinalLT (Arr
ow K) κ；Y.obj k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isCardinalPresentable_iff_of_isEquivalence`：isCardinalPre
sentable_iff_of_isEquivalence {C' : Type u₃} [Category.{v₃} C'] (F : C ⥤ C') [F.
IsEquivalence] : IsCardinalPresentable (F.obj X…
· 使用引理 `CategoryTheory.isCardinalPresentable_of_isColimit'`：isCardinalPresentabl
e_of_isColimit' {K : Type u'} [Category.{v'} K] {Y : K ⥤ C} (c : Cocone Y) (hc :
 IsColimit c) (κ : Cardinal.{w}) [Fact κ…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
lemma isCardinalPresentable_of_isColimit [LocallySmall.{w} C]
    {K : Type u'} [Category.{v'} K] [HasLimitsOfShape Kᵒᵖ (Type w)] {Y : K ⥤ C}
    (c : Cocone Y) (hc : IsColimit c) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hK : HasCardinalLT (Arrow K) κ)
    [∀ k, IsCardinalPresentable (Y.obj k) κ] :
    IsCardinalPresentable c.pt κ := by
  let e := ShrinkHoms.equivalence.{w} C
  have (k : K) : IsCardinalPresentable ((Y ⋙ e.functor).obj k) κ := by
    dsimp; infer_instance
  rw [← isCardinalPresentable_iff_of_isEquivalence c.pt κ e.functor]
  exact isCardinalPresentable_of_isColimit' _
    (isColimitOfPreserves e.functor hc) κ hK

variable (C) in
/-
**CategoryTheory.isClosedUnderColimitsOfShape_isCardinalPresentable** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isClosedUnderColimitsOfShape_isCardinalPresentable [LocallySmall.{w} C] {κ
 : Cardinal.{w}} [Fact κ.IsRegular] {J : Type u'} [Category.{v'} J] [HasLimitsOf
Shape Jᵒᵖ (Type w)] (hJ : HasCardinalLT (Arrow J) κ) : (isCardinalPresentable C 
κ).IsClosedUnderColimitsOfShape J where colimitsOfShape_le
参数：Type w；hJ : HasCardinalLT (Arrow J) κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…
· 使用引理 `CategoryTheory.isCardinalPresentable_of_isColimit`：isCardinalPresentable
_of_isColimit [LocallySmall.{w} C] {K : Type u'} [Category.{v'} K] [HasLimitsOfS
hape Kᵒᵖ (Type w)] {Y : K ⥤ C} (c : Coc…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma isClosedUnderColimitsOfShape_isCardinalPresentable [LocallySmall.{w} C]
    {κ : Cardinal.{w}} [Fact κ.IsRegular]
    {J : Type u'} [Category.{v'} J] [HasLimitsOfShape Jᵒᵖ (Type w)]
    (hJ : HasCardinalLT (Arrow J) κ) :
    (isCardinalPresentable C κ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨hX⟩
    have := hX.prop_diag_obj
    simp only [isCardinalPresentable_iff] at this ⊢
    exact isCardinalPresentable_of_isColimit _ hX.isColimit κ hJ

end CategoryTheory

