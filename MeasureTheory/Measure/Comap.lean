/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Pullback of a measure

In this file we define the pullback `MeasureTheory.Measure.comap f μ`
of a measure `μ` along an injective map `f`
such that the image of any measurable set under `f` is a null-measurable set.
If `f` does not have these properties, then we define `comap f μ` to be zero.

In the future, we may decide to redefine `comap f μ` so that it gives meaningful results, e.g.,
for covering maps like `(↑) : ℝ → AddCircle (1 : ℝ)`.
-/

@[expose] public section

open Function Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureTheory

namespace Measure

variable {α β γ : Type*} {s : Set α}

open scoped Classical in
/-- Pullback of a `Measure` as a linear map. If `f` sends each measurable set to a measurable
set, then for each measurable set `s` we have `comapₗ f μ s = μ (f '' s)`.

Note that if `f` is not injective, this definition assigns `Set.univ` measure zero.

If the linearity is not needed, please use `comap` instead, which works for a larger class of
functions. `comapₗ` is an auxiliary definition and most lemmas deal with comap. -/
/-
**MeasureTheory.Measure.comap** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：comap [MeasurableSpace α] [MeasurableSpace β] (f : α -> β) (μ : Measure β)
 : Measure α
参数：f : α -> β；μ : Measure β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback of a `Measure` as a linear map. If `f` sends each measurable set to a m
easurable
set, then for each measurable set `s` we have `comapₗ f μ s = μ (f '' s)`.

Note that if `f` is not injective, this definition assigns `Set.univ` measure ze
ro.

If the linearity is not needed, please use `comap` instead, which works for a la
rger class of
functions. `comapₗ` is an auxiliary definition and most lemmas deal with comap.
-/
def comapₗ [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Measure β →ₗ[ℝ≥0∞] Measure α :=
  if hf : Injective f ∧ ∀ s, MeasurableSet s → MeasurableSet (f '' s) then
    liftLinear (OuterMeasure.comap f) fun μ s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_sdiff hf.1]
      apply le_toOuterMeasure_caratheodory
      exact hf.2 s hs
  else 0

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.Measure.comap** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：comap [MeasurableSpace α] [MeasurableSpace β] (f : α -> β) (μ : Measure β)
 : Measure α
参数：f : α -> β；μ : Measure β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comapₗ_apply {_ : MeasurableSpace α} {_ : MeasurableSpace β} (f : α → β)
    (hfi : Injective f) (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β)
    (hs : MeasurableSet s) : comapₗ f μ s = μ (f '' s) := by
  rw [comapₗ, dif_pos, liftLinear_apply _ hs, OuterMeasure.comap_apply, coe_toOuterMeasure]
  exact ⟨hfi, hf⟩

open scoped Classical in
/-- Pullback of a `Measure`. If `f` sends each measurable set to a null-measurable set,
then for each measurable set `s` we have `comap f μ s = μ (f '' s)`.

Note that if `f` is not injective, this definition assigns `Set.univ` measure zero. -/
/-
**MeasureTheory.Measure.comap** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：comap [MeasurableSpace α] [MeasurableSpace β] (f : α -> β) (μ : Measure β)
 : Measure α
参数：f : α -> β；μ : Measure β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback of a `Measure`. If `f` sends each measurable set to a null-measurable s
et,
then for each measurable set `s` we have `comap f μ s = μ (f '' s)`.

Note that if `f` is not injective, this definition assigns `Set.univ` measure ze
ro.
-/
def comap [MeasurableSpace α] [MeasurableSpace β] (f : α → β) (μ : Measure β) : Measure α :=
  if hf : Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ then
    (OuterMeasure.comap f μ.toOuterMeasure).toMeasure fun s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_sdiff hf.1]
      exact (measure_inter_add_sdiff₀ _ (hf.2 s hs)).symm
  else 0

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {f : α → β} {g : β → γ}
/-
**MeasureTheory.Measure.comap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：comap_apply (f : α -> β) (hfi : Injective f) (hf : forall s, MeasurableSet
 s -> MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) : comap f μ
 s = μ (f '' s)
参数：f : α -> β；hfi : Injective f；hf : forall s, MeasurableSet s -> MeasurableSet 
(f '' s)；μ : Measure β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.comap_apply₀`：comap_apply₀ (f : α -> β) (μ : Measu
re β) (hfi : Injective f) (hf : forall s, MeasurableSet s -> NullMeasurableSet (
f '' s) μ) (hs : NullMea…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem comap_apply₀ (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    (hs : NullMeasurableSet s (comap f μ)) : comap f μ s = μ (f '' s) := by
  rw [comap, dif_pos (And.intro hfi hf)] at hs ⊢
  rw [toMeasure_apply₀ _ _ hs, OuterMeasure.comap_apply, coe_toOuterMeasure]
/-
**MeasureTheory.Measure.comap_undef** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：comap_undef {μ : Measure β} (h : ¬ (Injective f ∧ forall s, MeasurableSet 
s -> NullMeasurableSet (f '' s) μ)) : comap f μ = 0
参数：h : ¬ (Injective f ∧ forall s, MeasurableSet s -> NullMeasurableSet (f '' s) 
μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma comap_undef {μ : Measure β}
    (h : ¬ (Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)) :
    comap f μ = 0 := dif_neg h
/-
**MeasureTheory.Measure.le_comap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：le_comap_apply (f : α -> β) (μ : Measure β) (hfi : Injective f) (hf : fora
ll s, MeasurableSet s -> NullMeasurableSet (f '' s) μ) (s : Set α) : μ (f '' s) 
<= comap f μ s
参数：f : α -> β；μ : Measure β；hfi : Injective f；hf : forall s, MeasurableSet s -> 
NullMeasurableSet (f '' s) μ；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.comap.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst 
: MeasurableSpace α] [inst_1 : MeasurableSpace β] (f : α → β)   (μ : MeasureTheo
ry.Measure β),   Measu…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `MeasureTheory.le_toMeasure_apply`：le_toMeasure_apply (m : OuterMeasure α
) (h : ms <= m.caratheodory) (s : Set α) : m s <= m.toMeasure h s
-/
theorem le_comap_apply (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ) (s : Set α) :
    μ (f '' s) ≤ comap f μ s := by
  rw [comap, dif_pos (And.intro hfi hf)]
  exact le_toMeasure_apply _ _ _
/-
**MeasureTheory.Measure.comap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：comap_apply (f : α -> β) (hfi : Injective f) (hf : forall s, MeasurableSet
 s -> MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) : comap f μ
 s = μ (f '' s)
参数：f : α -> β；hfi : Injective f；hf : forall s, MeasurableSet s -> MeasurableSet 
(f '' s)；μ : Measure β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.comap_apply₀`：comap_apply₀ (f : α -> β) (μ : Measu
re β) (hfi : Injective f) (hf : forall s, MeasurableSet s -> NullMeasurableSet (
f '' s) μ) (hs : NullMea…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem comap_apply (f : α → β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    comap f μ s = μ (f '' s) :=
  comap_apply₀ f μ hfi (fun s hs => (hf s hs).nullMeasurableSet) hs.nullMeasurableSet
/-
**MeasureTheory.Measure.comap_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：comap_apply_le (f : α -> β) (μ : Measure β) (hs : NullMeasurableSet s (μ.c
omap f)) : μ.comap f s <= μ (f '' s)
参数：f : α -> β；μ : Measure β；hs : NullMeasurableSet s (μ.comap f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.comap_apply₀`：comap_apply₀ (f : α -> β) (μ : Measu
re β) (hfi : Injective f) (hf : forall s, MeasurableSet s -> NullMeasurableSet (
f '' s) μ) (hs : NullMea…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.Measure.comap_undef`：comap_undef {μ : Measure β} (h : ¬ (I
njective f ∧ forall s, MeasurableSet s -> NullMeasurableSet (f '' s) μ)) : comap
 f μ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem comap_apply_le (f : α → β) (μ : Measure β) (hs : NullMeasurableSet s (μ.comap f)) :
    μ.comap f s ≤ μ (f '' s) := by
  by_cases hf : Injective f ∧ ∀ t, MeasurableSet t → NullMeasurableSet (f '' t) μ
  · rw [comap_apply₀ _ _ hf.1 hf.2 hs]
  · simp [comap_undef hf]
/-
**MeasureTheory.Measure.comap** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：comap [MeasurableSpace α] [MeasurableSpace β] (f : α -> β) (μ : Measure β)
 : Measure α
参数：f : α -> β；μ : Measure β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comapₗ_eq_comap (f : α → β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    comapₗ f μ s = comap f μ s :=
  (comapₗ_apply f hfi hf μ hs).trans (comap_apply f hfi hf μ hs).symm
/-
**MeasureTheory.Measure.measure_image_eq_zero_of_comap_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_image_eq_zero_of_comap_eq_zero (f : α -> β) (μ : Measure β) (hfi :
 Injective f) (hf : forall s, MeasurableSet s -> NullMeasurableSet (f '' s) μ) {
s : Set α} (hs : comap f μ s = 0) : μ (f '' s) = 0
参数：f : α -> β；μ : Measure β；hfi : Injective f；hf : forall s, MeasurableSet s -> 
NullMeasurableSet (f '' s) μ；hs : comap f μ s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.Measure.le_comap_apply`：le_comap_apply (f : α -> β) (μ : M
easure β) (hfi : Injective f) (hf : forall s, MeasurableSet s -> NullMeasurableS
et (f '' s) μ) (s : Set α)…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem measure_image_eq_zero_of_comap_eq_zero (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ) {s : Set α} (hs : comap f μ s = 0) :
    μ (f '' s) = 0 := by
  rw [← nonpos_iff_eq_zero]
  exact (le_comap_apply f μ hfi hf s).trans hs.le

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.Measure.ae_eq_image_of_ae_eq_comap** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：ae_eq_image_of_ae_eq_comap (f : α -> β) (μ : Measure β) (hfi : Injective f
) (hf : forall s, MeasurableSet s -> NullMeasurableSet (f '' s) μ) {s t : Set α}
 (hst : s =ᵐ[comap f μ] t) : f '' s =ᵐ[μ] f '' t
参数：f : α -> β；μ : Measure β；hfi : Injective f；hf : forall s, MeasurableSet s -> 
NullMeasurableSet (f '' s) μ；hst : s =ᵐ[comap f μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b
· 使用定理 `Decidable.not_iff`：∀ {b a : Prop} [Decidable b], ¬(a ↔ b) ↔ (¬a ↔ b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `MeasureTheory.Measure.measure_image_eq_zero_of_comap_eq_zero`：measure_im
age_eq_zero_of_comap_eq_zero (f : α -> β) (μ : Measure β) (hfi : Injective f) (h
f : forall s, MeasurableSet s -> NullMeasurableSet…
-/
theorem ae_eq_image_of_ae_eq_comap (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    {s t : Set α} (hst : s =ᵐ[comap f μ] t) : f '' s =ᵐ[μ] f '' t := by
  rw [EventuallyEq, ae_iff] at hst ⊢
  have h_eq_α : { a : α | ¬s a = t a } = s \ t ∪ t \ s := by
    ext1 x
    simp only [eq_iff_iff, mem_ofPred_eq, mem_union, Set.mem_sdiff]
    tauto
  have h_eq_β : { a : β | ¬(f '' s) a = (f '' t) a } = f '' s \ f '' t ∪ f '' t \ f '' s := by
    ext1 x
    simp only [eq_iff_iff, mem_ofPred_eq, mem_union, Set.mem_sdiff]
    tauto
  rw [← Set.image_sdiff hfi, ← Set.image_sdiff hfi, ← Set.image_union] at h_eq_β
  rw [h_eq_β]
  rw [h_eq_α] at hst
  exact measure_image_eq_zero_of_comap_eq_zero f μ hfi hf hst
/-
**MeasureTheory.Measure.NullMeasurableSet.image** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {mα : MeasurableSpace α} {mβ :
 MeasurableSpace β} (f : α → β)   (μ : MeasureTheory.Measure β),   Function.Inje
ctive f →     (∀ (s : Set α), MeasurableSet s → MeasureTheory.NullMeasurableSet 
(f '' s) μ) →       MeasureTheory.NullMeasurableSet s (MeasureTheory.Measure.com
ap f μ) → MeasureTheory.NullMeasurableSet (f '' s) μ
参数：f : α → β；μ : MeasureTheory.Measure β；∀ (s : Set α), MeasurableSet s → Measur
eTheory.NullMeasurableSet (f '' s) μ；MeasureTheory.Measure.comap f μ；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.NullMeasurableSet.toMeasurable_ae_eq`：toMeasurable_ae_eq (
h : NullMeasurableSet s μ) : toMeasurable μ s =ᵐ[μ] s
· 使用定理 `MeasureTheory.Measure.ae_eq_image_of_ae_eq_comap`：ae_eq_image_of_ae_eq_c
omap (f : α -> β) (μ : Measure β) (hfi : Injective f) (hf : forall s, Measurable
Set s -> NullMeasurableSet (f '' s) μ)…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem NullMeasurableSet.image (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    (hs : NullMeasurableSet s (μ.comap f)) : NullMeasurableSet (f '' s) μ := by
  refine ⟨toMeasurable μ (f '' toMeasurable (μ.comap f) s), measurableSet_toMeasurable _ _, ?_⟩
  refine EventuallyEq.trans ?_ (NullMeasurableSet.toMeasurable_ae_eq ?_).symm
  swap
  · exact hf _ (measurableSet_toMeasurable _ _)
  have h : toMeasurable (comap f μ) s =ᵐ[comap f μ] s :=
    NullMeasurableSet.toMeasurable_ae_eq hs
  exact ae_eq_image_of_ae_eq_comap f μ hfi hf h.symm
/-
**MeasureTheory.Measure.comap_preimage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：comap_preimage (f : α -> β) (μ : Measure β) (hf : Injective f) (hf' : Meas
urable f) (h : forall t, MeasurableSet t -> NullMeasurableSet (f '' t) μ) {s : S
et β} (hs : MeasurableSet s) : μ.comap f (f ⁻¹' s) = μ (s inter range f)
参数：f : α -> β；μ : Measure β；hf : Injective f；hf' : Measurable f；h : forall t, Me
asurableSet t -> NullMeasurableSet (f '' t) μ；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.comap_apply₀`：comap_apply₀ (f : α -> β) (μ : Measu
re β) (hfi : Injective f) (hf : forall s, MeasurableSet s -> NullMeasurableSet (
f '' s) μ) (hs : NullMea…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
-/
theorem comap_preimage (f : α → β) (μ : Measure β) (hf : Injective f) (hf' : Measurable f)
    (h : ∀ t, MeasurableSet t → NullMeasurableSet (f '' t) μ) {s : Set β} (hs : MeasurableSet s) :
    μ.comap f (f ⁻¹' s) = μ (s ∩ range f) := by
  rw [comap_apply₀ _ _ hf h (hf' hs).nullMeasurableSet, image_preimage_eq_inter_range]
/-
**MeasureTheory.Measure.comap_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (f : α → β),   MeasureTheory.Measure.comap f 0 = 0
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `MeasureTheory.OuterMeasure.toMeasure.congr_simp`：∀ {α : Type u_1} [ms : 
MeasurableSpace α] (m m_1 : MeasureTheory.OuterMeasure α) (e_m : m = m_1)   (h :
 ms ≤ m.caratheodory), m.toMeasure h …
· 使用定理 `MeasureTheory.OuterMeasure.toMeasure_zero`：∀ {α : Type u_1} [ms : Measur
ableSpace α] (h : ms ≤ MeasureTheory.OuterMeasure.caratheodory 0),   MeasureTheo
ry.OuterMeasure.toMeasure 0 h =…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
@[simp] lemma comap_zero (f : α → β) : (0 : Measure β).comap f = 0 := by
  by_cases hf : Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) (0 : Measure β)
  · simp [comap, hf]
  · simp [comap, hf]

@[simp]
/-
**MeasureTheory.Measure.comap_id** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：comap_id (μ : Measure β) : comap (fun x => x) μ = μ
参数：μ : Measure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.comap_apply`：comap_apply (f : α -> β) (hfi : Injec
tive f) (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure 
β) (hs : MeasurableSet …
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma comap_id (μ : Measure β) : comap (fun x ↦ x) μ = μ := by
  ext s hs
  rw [comap_apply, image_id']
  · exact injective_id
  all_goals simp [*]
/-
**MeasureTheory.Measure.comap_comap** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：comap_comap (hf' : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (h
g : Injective g) (hg' : forall s, MeasurableSet s -> MeasurableSet (g '' s)) (μ 
: Measure γ) : comap f (comap g μ) = comap (g ∘ f) μ
参数：hf' : forall s, MeasurableSet s -> MeasurableSet (f '' s)；hg : Injective g；hg
' : forall s, MeasurableSet s -> MeasurableSet (g '' s)；μ : Measure γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.comap_apply`：comap_apply (f : α -> β) (hfi : Injec
tive f) (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure 
β) (hs : MeasurableSet …
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `MeasureTheory.Measure.comap.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst 
: MeasurableSpace α] [inst_1 : MeasurableSpace β] (f : α → β)   (μ : MeasureTheo
ry.Measure β),   Measu…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
-/
lemma comap_comap (hf' : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (hg : Injective g)
    (hg' : ∀ s, MeasurableSet s → MeasurableSet (g '' s)) (μ : Measure γ) :
    comap f (comap g μ) = comap (g ∘ f) μ := by
  by_cases hf : Injective f
  · ext s hs
    rw [comap_apply _ hf hf' _ hs, comap_apply _ hg hg' _ (hf' _ hs),
      comap_apply _ (hg.comp hf) (fun t ht ↦ image_comp g f _ ▸ hg' _ <| hf' _ ht) _ hs, image_comp]
  · rw [comap, dif_neg <| mt And.left hf, comap, dif_neg fun h ↦ hf h.1.of_comp]
/-
**MeasureTheory.Measure.comap_smul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：comap_smul {μ : Measure β} (c : Real>=0∞) : comap f (c • μ) = c • comap f 
μ
参数：c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.Measure.comap_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : 
MeasurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure
.comap f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasureTheory.Measure.comap_apply₀`：comap_apply₀ (f : α -> β) (μ : Measu
re β) (hfi : Injective f) (hf : forall s, MeasurableSet s -> NullMeasurableSet (
f '' s) μ) (hs : NullMea…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `MeasureTheory.nullMeasurableSet_smul_measure_iff`：nullMeasurableSet_smul
_measure_iff {c : Real>=0∞} (hc : c != 0) : NullMeasurableSet s (c • μ) ↔ NullMe
asurableSet s μ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasureTheory.Measure.comap_undef`：comap_undef {μ : Measure β} (h : ¬ (I
njective f ∧ forall s, MeasurableSet s -> NullMeasurableSet (f '' s) μ)) : comap
 f μ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma comap_smul {μ : Measure β} (c : ℝ≥0∞) : comap f (c • μ) = c • comap f μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  by_cases h : Function.Injective f ∧ ∀ s : Set α, MeasurableSet s → NullMeasurableSet (f '' s) μ
  · ext s hs
    rw [comap_apply₀ f _ h.1 _ hs.nullMeasurableSet, smul_apply, smul_apply,
      comap_apply₀ f μ h.1 h.2 hs.nullMeasurableSet]
    simpa [nullMeasurableSet_smul_measure_iff hc] using h.2
  · have h' : ¬ (Function.Injective f ∧
        ∀ (s : Set α), MeasurableSet s → NullMeasurableSet (f '' s) (c • μ)) := by
      simpa [nullMeasurableSet_smul_measure_iff hc] using h
    simp [comap_undef, h, h']

end Measure

end MeasureTheory

open MeasureTheory Measure

variable {α β : Type*} {ma : MeasurableSpace α} {mb : MeasurableSpace β}

/-
**MeasurableEmbedding.comap_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasurableEmbedding.comap_add {f : α -> β} (hf : MeasurableEmbedding f) (μ
 ν : Measure β) : (μ + ν).comap f = μ.comap f + ν.comap f
参数：hf : MeasurableEmbedding f；μ ν : Measure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.comapₗ_eq_comap`：comapₗ_eq_comap (f : α -> β) (hfi
 : Injective f) (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : 
Measure β) (hs : Measurable…
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEmbedding.measurableSet_image`：measurableSet_image (hf : Measu
rableEmbedding f) : MeasurableSet (f '' s) ↔ MeasurableSet s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MeasurableEmbedding.comap_add {f : α → β} (hf : MeasurableEmbedding f) (μ ν : Measure β) :
    (μ + ν).comap f = μ.comap f + ν.comap f := by
  ext s hs
  simp only [← comapₗ_eq_comap _ hf.injective (fun _ ↦ hf.measurableSet_image.mpr) _ hs,
    map_add, add_apply]

namespace MeasurableEquiv

/-
**MeasurableEquiv.comap_symm** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：comap_symm {μ : Measure α} (e : α ≃ᵐ β) : μ.comap e.symm = μ.map e
参数：e : α ≃ᵐ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `MeasureTheory.Measure.comap_apply`：comap_apply (f : α -> β) (hfi : Injec
tive f) (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure 
β) (hs : MeasurableSet …
· 使用定理 `MeasurableEquiv.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : Measu
rableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   Function.Injective ⇑e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEquiv.measurableSet_image`：measurableSet_image (e : α ≃ᵐ β) : 
MeasurableSet (e '' s) ↔ MeasurableSet s
· 使用引理 `MeasurableEquiv.image_symm`：image_symm (e : α ≃ᵐ β) (s : Set β) : e.symm
 '' s = e ⁻¹' s
-/
lemma comap_symm {μ : Measure α} (e : α ≃ᵐ β) : μ.comap e.symm = μ.map e := by
  ext s hs
  rw [e.map_apply, Measure.comap_apply _ e.symm.injective _ _ hs, image_symm]
  exact fun t ht ↦ e.symm.measurableSet_image.mpr ht
/-
**MeasurableEquiv.map_symm** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：map_symm {μ : Measure α} (e : β ≃ᵐ α) : μ.map e.symm = μ.comap e
参数：e : β ≃ᵐ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasurableEquiv.comap_symm`：comap_symm {μ : Measure α} (e : α ≃ᵐ β) : μ.
comap e.symm = μ.map e
· 使用定理 `MeasurableEquiv.symm_symm`：symm_symm (e : α ≃ᵐ β) : e.symm.symm = e
-/
lemma map_symm {μ : Measure α} (e : β ≃ᵐ α) : μ.map e.symm = μ.comap e := by
  rw [← comap_symm, symm_symm]

end MeasurableEquiv

/-
**MeasureTheory.Measure.comap_swap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasureTheory.Measure.comap_swap (μ : Measure (α × β)) : μ.comap .swap = μ
.map .swap
参数：μ : Measure (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasurableEquiv.comap_symm`：comap_symm {μ : Measure α} (e : α ≃ᵐ β) : μ.
comap e.symm = μ.map e
-/
lemma MeasureTheory.Measure.comap_swap (μ : Measure (α × β)) : μ.comap .swap = μ.map .swap :=
  (MeasurableEquiv.prodComm ..).comap_symm
