/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Tactic.FunProp

/-!
# Measurable embeddings and equivalences

A measurable equivalence between measurable spaces is an equivalence
which respects the σ-algebras, that is, for which both directions of
the equivalence are measurable functions.

## Main definitions

* `MeasurableEmbedding`: a map `f : α → β` is called a *measurable embedding* if it is injective,
  measurable, and sends measurable sets to measurable sets.
* `MeasurableEquiv`: an equivalence `α ≃ β` is a *measurable equivalence* if its forward and inverse
  functions are measurable.

We prove a multitude of elementary lemmas about these, and one more substantial theorem:

* `MeasurableEmbedding.schroederBernstein`: the **measurable Schröder-Bernstein Theorem**: given
  measurable embeddings `α → β` and `β → α`, we can find a measurable equivalence `α ≃ᵐ β`.

## Notation

* We write `α ≃ᵐ β` for measurable equivalences between the measurable spaces `α` and `β`.
  This should not be confused with `≃ₘ` which is used for diffeomorphisms between manifolds.

## Tags

measurable equivalence, measurable embedding
-/

@[expose] public section


open Set Function Equiv MeasureTheory

universe uι

variable {α β γ δ δ' : Type*} {ι : Sort uι} {s t u : Set α}

/-- A map `f : α → β` is called a *measurable embedding* if it is injective, measurable, and sends
measurable sets to measurable sets. The latter assumption can be replaced with “`f` has measurable
inverse `g : Set.range f → α`”, see `MeasurableEmbedding.measurable_rangeSplitting`,
`MeasurableEmbedding.of_measurable_inverse_range`, and
`MeasurableEmbedding.of_measurable_inverse`.

One more interpretation: `f` is a measurable embedding if it defines a measurable equivalence to its
range and the range is a measurable set. One implication is formalized as
`MeasurableEmbedding.equivRange`; the other one follows from
`MeasurableEquiv.measurableEmbedding`, `MeasurableEmbedding.subtype_coe`, and
`MeasurableEmbedding.comp`. -/
/-
**MeasurableEmbedding** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [MeasurableSpace α] → [MeasurableSpace β
] → (α → β) → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f : α → β` is called a *measurable embedding* if it is injective, measura
ble, and sends
measurable sets to measurable sets. The latter assumption can be replaced with “
`f` has measurable
inverse `g : Set.range f → α`”, see `MeasurableEmbedding.measurable_rangeSplitti
ng`,
`MeasurableEmbedding.of_measurable_inverse_range`, and
`MeasurableEmbedding.of_measurable_inverse`.

One more interpretation: `f` is a measurable embedding if it defines a measurabl
e equivalence to its
range and the range is a measurable set. One implication is formalized as
`MeasurableEmbedding.equivRange`; the other one follows from
`MeasurableEquiv.measurableEmbedding`, `MeasurableEmbedding.subtype_coe`, and
`MeasurableEmbedding.comp`.
-/
structure MeasurableEmbedding [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop where
  /-- A measurable embedding is injective. -/
  protected injective : Injective f
  /-- A measurable embedding is a measurable function. -/
  protected measurable : Measurable f
  /-- The image of a measurable set under a measurable embedding is a measurable set. -/
  protected measurableSet_image' : ∀ ⦃s⦄, MeasurableSet s → MeasurableSet (f '' s)

attribute [fun_prop] MeasurableEmbedding.measurable

namespace MeasurableEmbedding

variable {mα : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {g : β → γ}

/-
**MeasurableEmbedding.measurableSet_image** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableE
mbedding`。
形式化陈述：measurableSet_image (hf : MeasurableEmbedding f) : MeasurableSet (f '' s) 
↔ MeasurableSet s
参数：hf : MeasurableEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
· 使用定理 `MeasurableEmbedding.measurableSet_image'`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measura
bleEmbedding f → ∀ ⦃s : Set α⦄…
-/
theorem measurableSet_image (hf : MeasurableEmbedding f) :
    MeasurableSet (f '' s) ↔ MeasurableSet s :=
  ⟨fun h => by simpa only [hf.injective.preimage_image] using hf.measurable h, fun h =>
    hf.measurableSet_image' h⟩
/-
**MeasurableEmbedding.id** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEmbedding`。
形式化陈述：id : MeasurableEmbedding (id : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem id : MeasurableEmbedding (id : α → α) :=
  ⟨injective_id, measurable_id, fun s hs => by rwa [image_id]⟩
/-
**MeasurableEmbedding.comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEmbedding`。
形式化陈述：comp (hg : MeasurableEmbedding g) (hf : MeasurableEmbedding f) : Measurabl
eEmbedding (g ∘ f)
参数：hg : MeasurableEmbedding g；hf : MeasurableEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `MeasurableEmbedding.measurableSet_image`：measurableSet_image (hf : Measu
rableEmbedding f) : MeasurableSet (f '' s) ↔ MeasurableSet s
-/
theorem comp (hg : MeasurableEmbedding g) (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (g ∘ f) :=
  ⟨hg.injective.comp hf.injective, hg.measurable.comp hf.measurable, fun s hs => by
    rwa [image_comp, hg.measurableSet_image, hf.measurableSet_image]⟩
/-
**MeasurableEmbedding.subtype_coe** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEmbedding
`。
形式化陈述：subtype_coe (hs : MeasurableSet s) : MeasurableEmbedding ((↑) : s -> α) wh
ere injective
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
· 使用定理 `MeasurableSet.subtype_image`：MeasurableSet.subtype_image {s : Set α} {t 
: Set s} (hs : MeasurableSet s) : MeasurableSet t -> MeasurableSet (((↑) : s -> 
α) '' t)
-/
theorem subtype_coe (hs : MeasurableSet s) : MeasurableEmbedding ((↑) : s → α) where
  injective := Subtype.coe_injective
  measurable := measurable_subtype_coe
  measurableSet_image' := fun _ => MeasurableSet.subtype_image hs
/-
**MeasurableEmbedding.measurableSet_range** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableE
mbedding`。
形式化陈述：measurableSet_range (hf : MeasurableEmbedding f) : MeasurableSet (range f)
参数：hf : MeasurableEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `MeasurableEmbedding.measurableSet_image'`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measura
bleEmbedding f → ∀ ⦃s : Set α⦄…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
theorem measurableSet_range (hf : MeasurableEmbedding f) : MeasurableSet (range f) := by
  rw [← image_univ]
  exact hf.measurableSet_image' MeasurableSet.univ
/-
**MeasurableEmbedding.measurableSet_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Measurab
leEmbedding`。
形式化陈述：measurableSet_preimage (hf : MeasurableEmbedding f) {s : Set β} : Measurab
leSet (f ⁻¹' s) ↔ MeasurableSet (s inter range f)
参数：hf : MeasurableEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `MeasurableEmbedding.measurableSet_image`：measurableSet_image (hf : Measu
rableEmbedding f) : MeasurableSet (f '' s) ↔ MeasurableSet s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measurableSet_preimage (hf : MeasurableEmbedding f) {s : Set β} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet (s ∩ range f) := by
  rw [← image_preimage_eq_inter_range, hf.measurableSet_image]
/-
**MeasurableEmbedding.measurable_rangeSplitting** 是 Mathlib 中的一个定理，位于命名空间 `Measu
rableEmbedding`。
形式化陈述：measurable_rangeSplitting (hf : MeasurableEmbedding f) : Measurable (range
Splitting f)
参数：hf : MeasurableEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_rangeSplitting`：preimage_rangeSplitting {f : α -> β} (hf : 
Injective f) : preimage (rangeSplitting f) = image (rangeFactorization f)
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEmbedding.measurableSet_image`：measurableSet_image (hf : Measu
rableEmbedding f) : MeasurableSet (f '' s) ↔ MeasurableSet s
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `MeasurableEmbedding.measurableSet_range`：measurableSet_range (hf : Measu
rableEmbedding f) : MeasurableSet (range f)
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.coe_comp_rangeFactorization`：coe_comp_rangeFactorization (f : ι -> β
) : (↑) ∘ rangeFactorization f = f
-/
theorem measurable_rangeSplitting (hf : MeasurableEmbedding f) :
    Measurable (rangeSplitting f) := fun s hs => by
  rwa [preimage_rangeSplitting hf.injective,
    ← (subtype_coe hf.measurableSet_range).measurableSet_image, ← image_comp,
    coe_comp_rangeFactorization, hf.measurableSet_image]
/-
**MeasurableEmbedding.measurable_extend** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEmb
edding`。
形式化陈述：measurable_extend (hf : MeasurableEmbedding f) {g : α -> γ} {g' : β -> γ} 
(hg : Measurable g) (hg' : Measurable g') : Measurable (extend f g g')
参数：hf : MeasurableEmbedding f；hg : Measurable g；hg' : Measurable g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_restrict_of_restrict_compl`：measurable_of_restrict_of_rest
rict_compl {f : α -> β} {s : Set α} (hs : MeasurableSet s) (h₁ : Measurable (s.d
omRestrict f)) (h₂ : Measurabl…
· 使用定理 `MeasurableEmbedding.measurableSet_range`：measurableSet_range (hf : Measu
rableEmbedding f) : MeasurableSet (range f)
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.domRestrict_extend_range`：domRestrict_extend_range (f : α -> β) (g :
 α -> γ) (g' : β -> γ) : (range f).domRestrict (extend f g g') = fun x => g x.co
e_prop.choose
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableEmbedding.measurable_rangeSplitting`：measurable_rangeSplitting
 (hf : MeasurableEmbedding f) : Measurable (rangeSplitting f)
· 使用定理 `Set.domRestrict_extend_compl_range`：domRestrict_extend_compl_range (f : 
α -> β) (g : α -> γ) (g' : β -> γ) : (range f)ᶜ.domRestrict (extend f g g') = g'
 ∘ Subtype.val
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
-/
theorem measurable_extend (hf : MeasurableEmbedding f) {g : α → γ} {g' : β → γ} (hg : Measurable g)
    (hg' : Measurable g') : Measurable (extend f g g') := by
  refine measurable_of_restrict_of_restrict_compl hf.measurableSet_range ?_ ?_
  · rw [domRestrict_extend_range]
    simpa only [rangeSplitting] using! hg.comp hf.measurable_rangeSplitting
  · rw [domRestrict_extend_compl_range]
    exact hg'.comp measurable_subtype_coe
/-
**MeasurableEmbedding.exists_measurable_extend** 是 Mathlib 中的一个定理，位于命名空间 `Measur
ableEmbedding`。
形式化陈述：exists_measurable_extend (hf : MeasurableEmbedding f) {g : α -> γ} (hg : M
easurable g) (hne : β -> Nonempty γ) : exists g' : β -> γ, Measurable g' ∧ g' ∘ 
f = g
参数：hf : MeasurableEmbedding f；hg : Measurable g；hne : β -> Nonempty γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.measurable_extend`：measurable_extend (hf : Measurabl
eEmbedding f) {g : α -> γ} {g' : β -> γ} (hg : Measurable g) (hg' : Measurable g
') : Measurable (extend f g…
· 使用定理 `measurable_const'`：measurable_const' {f : β -> α} (hf : forall x y, f x 
= f y) : Measurable f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
-/
theorem exists_measurable_extend (hf : MeasurableEmbedding f) {g : α → γ} (hg : Measurable g)
    (hne : β → Nonempty γ) : ∃ g' : β → γ, Measurable g' ∧ g' ∘ f = g :=
  ⟨extend f g fun x => Classical.choice (hne x),
    hf.measurable_extend hg (measurable_const' fun _ _ => rfl),
    funext fun _ => hf.injective.extend_apply _ _ _⟩
/-
**MeasurableEmbedding.measurable_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableE
mbedding`。
形式化陈述：measurable_comp_iff (hg : MeasurableEmbedding g) : Measurable (g ∘ f) ↔ Me
asurable f
参数：hg : MeasurableEmbedding g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableEmbedding.measurable_rangeSplitting`：measurable_rangeSplitting
 (hf : MeasurableEmbedding f) : Measurable (rangeSplitting f)
· 使用定理 `Measurable.subtype_mk`：Measurable.subtype_mk {p : β -> Prop} {f : α -> β
} (hf : Measurable f) {h : forall x, p (f x)} : Measurable fun x => (⟨f x, h x⟩ 
: Subtype p…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.RightInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse f g → g ∘ f = id
· 使用定理 `Set.rightInverse_rangeSplitting`：rightInverse_rangeSplitting {f : α -> β
} (h : Injective f) : RightInverse (rangeFactorization f) (rangeSplitting f)
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
-/
theorem measurable_comp_iff (hg : MeasurableEmbedding g) : Measurable (g ∘ f) ↔ Measurable f := by
  refine ⟨fun H => ?_, hg.measurable.comp⟩
  suffices Measurable ((rangeSplitting g ∘ rangeFactorization g) ∘ f) by
    rwa [(rightInverse_rangeSplitting hg.injective).comp_eq_id] at this
  exact hg.measurable_rangeSplitting.comp H.subtype_mk
/-
**MeasurableEmbedding.natCast** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEmbedding`。
形式化陈述：natCast {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [AddM
onoidWithOne α] [CharZero α] : MeasurableEmbedding (Nat.cast : Nat -> α) where i
njective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `measurable_from_nat`：measurable_from_nat {f : Nat -> α} : Measurable f
· 使用定理 `Set.Countable.measurableSet`：Set.Countable.measurableSet {s : Set α} (hs
 : s.Countable) : MeasurableSet s
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `instCountableNat`：Countable ℕ
-/
lemma natCast {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [AddMonoidWithOne α] [CharZero α] :
    MeasurableEmbedding (Nat.cast : ℕ → α) where
  injective := Nat.cast_injective
  measurable := measurable_from_nat
  measurableSet_image' := fun _ _ =>
    ((Set.countable_range (Nat.cast : ℕ → α)).mono
      (Set.image_subset_range _ _)).measurableSet

end MeasurableEmbedding

section gluing
variable {α₁ α₂ α₃ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mα₁ : MeasurableSpace α₁} {mα₂ : MeasurableSpace α₂} {mα₃ : MeasurableSpace α₃}
  {i₁ : α₁ → α} {i₂ : α₂ → α} {i₃ : α₃ → α} {s : Set α} {f : α → β}

/-
**MeasurableSet.of_union_range_cover** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasurableSet.of_union_range_cover (hi₁ : MeasurableEmbedding i₁) (hi₂ : M
easurableEmbedding i₂) (h : univ subseteq range i₁ union range i₂) (hs₁ : Measur
ableSet (i₁ ⁻¹' s)) (hs₂ : MeasurableSet (i₂ ⁻¹' s)) : MeasurableSet s
参数：hi₁ : MeasurableEmbedding i₁；hi₂ : MeasurableEmbedding i₂；h : univ subseteq r
ange i₁ union range i₂；hs₁ : MeasurableSet (i₁ ⁻¹' s)；hs₂ : MeasurableSet (i₂ ⁻¹
' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_preimage_eq_range_inter`：image_preimage_eq_range_inter {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = range f inter t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableEmbedding.measurableSet_image'`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measura
bleEmbedding f → ∀ ⦃s : Set α⦄…
-/
lemma MeasurableSet.of_union_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (h : univ ⊆ range i₁ ∪ range i₂)
    (hs₁ : MeasurableSet (i₁ ⁻¹' s)) (hs₂ : MeasurableSet (i₂ ⁻¹' s)) : MeasurableSet s := by
  convert! (hi₁.measurableSet_image' hs₁).union (hi₂.measurableSet_image' hs₂)
  simp [image_preimage_eq_range_inter, ← union_inter_distrib_right, univ_subset_iff.1 h]
/-
**MeasurableSet.of_union** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MeasurableSet.of_union₃_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (hi₃ : MeasurableEmbedding i₃)
    (h : univ ⊆ range i₁ ∪ range i₂ ∪ range i₃) (hs₁ : MeasurableSet (i₁ ⁻¹' s))
    (hs₂ : MeasurableSet (i₂ ⁻¹' s)) (hs₃ : MeasurableSet (i₃ ⁻¹' s)) : MeasurableSet s := by
  convert!
    (hi₁.measurableSet_image' hs₁).union (hi₂.measurableSet_image' hs₂) |>.union
      (hi₃.measurableSet_image' hs₃)
  simp [image_preimage_eq_range_inter, ← union_inter_distrib_right, univ_subset_iff.1 h]
/-
**Measurable.of_union_range_cover** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.of_union_range_cover (hi₁ : MeasurableEmbedding i₁) (hi₂ : Meas
urableEmbedding i₂) (h : univ subseteq range i₁ union range i₂) (hf₁ : Measurabl
e (f ∘ i₁)) (hf₂ : Measurable (f ∘ i₂)) : Measurable f
参数：hi₁ : MeasurableEmbedding i₁；hi₂ : MeasurableEmbedding i₂；h : univ subseteq r
ange i₁ union range i₂；hf₁ : Measurable (f ∘ i₁)；hf₂ : Measurable (f ∘ i₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasurableSet.of_union_range_cover`：MeasurableSet.of_union_range_cover (
hi₁ : MeasurableEmbedding i₁) (hi₂ : MeasurableEmbedding i₂) (h : univ subseteq 
range i₁ union range i₂)…
-/
lemma Measurable.of_union_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (h : univ ⊆ range i₁ ∪ range i₂)
    (hf₁ : Measurable (f ∘ i₁)) (hf₂ : Measurable (f ∘ i₂)) : Measurable f :=
  fun _s hs ↦ .of_union_range_cover hi₁ hi₂ h (hf₁ hs) (hf₂ hs)
/-
**Measurable.of_union** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Measurable.of_union₃_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (hi₃ : MeasurableEmbedding i₃)
    (h : univ ⊆ range i₁ ∪ range i₂ ∪ range i₃) (hf₁ : Measurable (f ∘ i₁))
    (hf₂ : Measurable (f ∘ i₂)) (hf₃ : Measurable (f ∘ i₃)) : Measurable f :=
  fun _s hs ↦ .of_union₃_range_cover hi₁ hi₂ hi₃ h (hf₁ hs) (hf₂ hs) (hf₃ hs)

end gluing

/-
**MeasurableSet.exists_measurable_proj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.exists_measurable_proj {_ : MeasurableSpace α} (hs : Measura
bleSet s) (hne : s.Nonempty) : exists f : α -> s, Measurable f ∧ forall x : s, f
 x = x
参数：hs : MeasurableSet s；hne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.exists_measurable_extend`：exists_measurable_extend (
hf : MeasurableEmbedding f) {g : α -> γ} (hg : Measurable g) (hne : β -> Nonempt
y γ) : exists g' : β -> γ, Measura…
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem MeasurableSet.exists_measurable_proj {_ : MeasurableSpace α}
    (hs : MeasurableSet s) (hne : s.Nonempty) : ∃ f : α → s, Measurable f ∧ ∀ x : s, f x = x :=
  let ⟨f, hfm, hf⟩ :=
    (MeasurableEmbedding.subtype_coe hs).exists_measurable_extend measurable_id fun _ =>
      hne.to_subtype
  ⟨f, hfm, congr_fun hf⟩

/-- Equivalences between measurable spaces. Main application is the simplification of measurability
statements along measurable equivalences. -/
/-
**MeasurableEquiv** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：MeasurableEquiv (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] exte
nds α ≃ β where /-- The forward function of a measurable equivalence is measurab
le. -/ measurable_toFun : Measurable toEquiv
参数：α β : Type*。
继承自：α ≃ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalences between measurable spaces. Main application is the simplification o
f measurability
statements along measurable equivalences.
-/
structure MeasurableEquiv (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] extends α ≃ β where
  /-- The forward function of a measurable equivalence is measurable. -/
  measurable_toFun : Measurable toEquiv := by measurability
  /-- The inverse function of a measurable equivalence is measurable. -/
  measurable_invFun : Measurable toEquiv.symm := by measurability

@[inherit_doc]
infixl:25 " ≃ᵐ " => MeasurableEquiv

namespace MeasurableEquiv

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-
**MeasurableEquiv.toEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：toEquiv_injective : Injective (toEquiv : α ≃ᵐ β -> α ≃ β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toEquiv_injective : Injective (toEquiv : α ≃ᵐ β → α ≃ β) := by
  rintro ⟨e₁, _, _⟩ ⟨e₂, _, _⟩ (rfl : e₁ = e₂)
  rfl
/-
**MeasurableEquiv.instEquivLike** 是 Mathlib 中的一个实例，位于命名空间 `MeasurableEquiv`。
形式化陈述：instEquivLike : EquivLike (α ≃ᵐ β) α β where coe e
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance instEquivLike : EquivLike (α ≃ᵐ β) α β where
  coe e := e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.toEquiv.left_inv
  right_inv e := e.toEquiv.right_inv
  coe_injective' _ _ he _ := toEquiv_injective <| DFunLike.ext' he

@[simp]
/-
**MeasurableEquiv.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_toEquiv (e : α ≃ᵐ β) : (e.toEquiv : α -> β) = e
参数：e : α ≃ᵐ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEquiv (e : α ≃ᵐ β) : (e.toEquiv : α → β) = e :=
  rfl

@[fun_prop]
/-
**MeasurableEquiv.measurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
参数：e : α ≃ᵐ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.measurable_toFun`：∀ {α : Type u_6} {β : Type u_7} [inst 
: MeasurableSpace α] [inst_1 : MeasurableSpace β] (self : α ≃ᵐ β),   Measurable 
⇑self.toEquiv
-/
protected theorem measurable (e : α ≃ᵐ β) : Measurable (e : α → β) :=
  e.measurable_toFun

@[simp]
/-
**MeasurableEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) : ((⟨e, h1
, h2⟩ : α ≃ᵐ β) : α -> β) = e
参数：e : α ≃ β；h1 : Measurable e；h2 : Measurable e.symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) :
    ((⟨e, h1, h2⟩ : α ≃ᵐ β) : α → β) = e :=
  rfl

/-- Any measurable space is equivalent to itself. -/
/-
**MeasurableEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：refl (α : Type*) [MeasurableSpace α] : α ≃ᵐ α where toEquiv
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Any measurable space is equivalent to itself.
-/
def refl (α : Type*) [MeasurableSpace α] : α ≃ᵐ α where
  toEquiv := Equiv.refl α
/-
**MeasurableEquiv.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `MeasurableEquiv`。
形式化陈述：instInhabited : Inhabited (α ≃ᵐ α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (α ≃ᵐ α) := ⟨refl α⟩

/-- The composition of equivalences between measurable spaces. -/
/-
**MeasurableEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : α ≃ᵐ γ where toEquiv
参数：ab : α ≃ᵐ β；bc : β ≃ᵐ γ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The composition of equivalences between measurable spaces.
-/
def trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : α ≃ᵐ γ where
  toEquiv := ab.toEquiv.trans bc.toEquiv
  measurable_toFun := bc.measurable_toFun.comp ab.measurable_toFun
  measurable_invFun := ab.measurable_invFun.comp bc.measurable_invFun
/-
**MeasurableEquiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : ⇑(ab.trans bc) = bc ∘ ab
参数：ab : α ≃ᵐ β；bc : β ≃ᵐ γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : ⇑(ab.trans bc) = bc ∘ ab := rfl

/-- The inverse of an equivalence between measurable spaces. -/
/-
**MeasurableEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm (ab : α ≃ᵐ β) : β ≃ᵐ α where toEquiv
参数：ab : α ≃ᵐ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MeasurableEquiv.measurable_invFun`：∀ {α : Type u_6} {β : Type u_7} [inst
 : MeasurableSpace α] [inst_1 : MeasurableSpace β] (self : α ≃ᵐ β),   Measurable
 ⇑self.symm

--- 原说明 ---
The inverse of an equivalence between measurable spaces.
-/
def symm (ab : α ≃ᵐ β) : β ≃ᵐ α where
  toEquiv := ab.toEquiv.symm
  measurable_toFun := ab.measurable_invFun

@[simp]
/-
**MeasurableEquiv.coe_toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_toEquiv_symm (e : α ≃ᵐ β) : (e.toEquiv.symm : β -> α) = e.symm
参数：e : α ≃ᵐ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_toEquiv_symm (e : α ≃ᵐ β) : (e.toEquiv.symm : β → α) = e.symm :=
  rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
/-
**MeasurableEquiv.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv.Simps`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [inst : MeasurableSpace α] → [inst_1 : M
easurableSpace β] → α ≃ᵐ β → α → β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
  because it is a composition of multiple projections.
-/
def Simps.apply (h : α ≃ᵐ β) : α → β := h

/-- See Note [custom simps projection] -/
/-
**MeasurableEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv.Si
mps`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [inst : MeasurableSpace α] → [inst_1 : M
easurableSpace β] → α ≃ᵐ β → β → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (h : α ≃ᵐ β) : β → α := h.symm

initialize_simps_projections MeasurableEquiv (toFun → apply, invFun → symm_apply)
/-
**MeasurableEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {e₁ e₂ : α ≃ᵐ β},   ⇑e₁ = ⇑e₂ → e₁ = e₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
@[ext] theorem ext {e₁ e₂ : α ≃ᵐ β} (h : (e₁ : α → β) = e₂) : e₁ = e₂ := DFunLike.ext' h

@[simp]
/-
**MeasurableEquiv.symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) : (⟨e, h1
, h2⟩ : α ≃ᵐ β).symm = ⟨e.symm, h2, h1⟩
参数：e : α ≃ β；h1 : Measurable e；h2 : Measurable e.symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) :
    (⟨e, h1, h2⟩ : α ≃ᵐ β).symm = ⟨e.symm, h2, h1⟩ :=
  rfl

attribute [simps! apply toEquiv] trans refl

@[simp]
/-
**MeasurableEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_symm (e : α ≃ᵐ β) : e.symm.symm = e
参数：e : α ≃ᵐ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (e : α ≃ᵐ β) : e.symm.symm = e := rfl
/-
**MeasurableEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_bijective : Function.Bijective (MeasurableEquiv.symm : (α ≃ᵐ β) -> β 
≃ᵐ α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `MeasurableEquiv.symm_symm`：symm_symm (e : α ≃ᵐ β) : e.symm.symm = e
-/
theorem symm_bijective :
    Function.Bijective (MeasurableEquiv.symm : (α ≃ᵐ β) → β ≃ᵐ α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**MeasurableEquiv.symm_refl** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_refl (α : Type*) [MeasurableSpace α] : (refl α).symm = refl α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_refl (α : Type*) [MeasurableSpace α] : (refl α).symm = refl α :=
  rfl

@[simp]
/-
**MeasurableEquiv.symm_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e = id
参数：e : α ≃ᵐ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e = id :=
  funext e.left_inv

@[simp]
/-
**MeasurableEquiv.self_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm = id
参数：e : α ≃ᵐ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm = id :=
  funext e.right_inv

@[simp]
/-
**MeasurableEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：apply_symm_apply (e : α ≃ᵐ β) (y : β) : e (e.symm y) = y
参数：e : α ≃ᵐ β；y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem apply_symm_apply (e : α ≃ᵐ β) (y : β) : e (e.symm y) = y :=
  e.right_inv y

@[simp]
/-
**MeasurableEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_apply_apply (e : α ≃ᵐ β) (x : α) : e.symm (e x) = x
参数：e : α ≃ᵐ β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem symm_apply_apply (e : α ≃ᵐ β) (x : α) : e.symm (e x) = x :=
  e.left_inv x

@[simp]
/-
**MeasurableEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_trans_self (e : α ≃ᵐ β) : e.symm.trans e = refl β
参数：e : α ≃ᵐ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableS
pace α] [inst_1 : MeasurableSpace β] {e₁ e₂ : α ≃ᵐ β},   ⇑e₁ = ⇑e₂ → e₁ = e₂
· 使用定理 `MeasurableEquiv.self_comp_symm`：self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm
 = id
-/
theorem symm_trans_self (e : α ≃ᵐ β) : e.symm.trans e = refl β :=
  ext e.self_comp_symm

@[simp]
/-
**MeasurableEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：self_trans_symm (e : α ≃ᵐ β) : e.trans e.symm = refl α
参数：e : α ≃ᵐ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableS
pace α] [inst_1 : MeasurableSpace β] {e₁ e₂ : α ≃ᵐ β},   ⇑e₁ = ⇑e₂ → e₁ = e₂
· 使用定理 `MeasurableEquiv.symm_comp_self`：symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e
 = id
-/
theorem self_trans_symm (e : α ≃ᵐ β) : e.trans e.symm = refl α :=
  ext e.symm_comp_self

@[simp]
/-
**MeasurableEquiv.trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：trans_symm (e₁ : α ≃ᵐ β) (e₂ : β ≃ᵐ γ) : (e₁.trans e₂).symm = e₂.symm.tran
s (e₁.symm)
参数：e₁ : α ≃ᵐ β；e₂ : β ≃ᵐ γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_symm (e₁ : α ≃ᵐ β) (e₂ : β ≃ᵐ γ) : (e₁.trans e₂).symm = e₂.symm.trans (e₁.symm) :=
  rfl
/-
**MeasurableEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_apply_eq (e : α ≃ᵐ β) {x y} : e.symm x = y ↔ x = e y
参数：e : α ≃ᵐ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq (e : α ≃ᵐ β) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq
/-
**MeasurableEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：eq_symm_apply (e : α ≃ᵐ β) {x y} : y = e.symm x ↔ e y = x
参数：e : α ≃ᵐ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply (e : α ≃ᵐ β) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply
/-
**MeasurableEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] (e : α ≃ᵐ β),   Function.Surjective ⇑e
参数：e : α ≃ᵐ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
protected theorem surjective (e : α ≃ᵐ β) : Surjective e :=
  e.toEquiv.surjective
/-
**MeasurableEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] (e : α ≃ᵐ β),   Function.Bijective ⇑e
参数：e : α ≃ᵐ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
protected theorem bijective (e : α ≃ᵐ β) : Bijective e :=
  e.toEquiv.bijective
/-
**MeasurableEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] (e : α ≃ᵐ β),   Function.Injective ⇑e
参数：e : α ≃ᵐ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem injective (e : α ≃ᵐ β) : Injective e :=
  e.toEquiv.injective

@[simp]
/-
**MeasurableEquiv.symm_preimage_preimage** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEq
uiv`。
形式化陈述：symm_preimage_preimage (e : α ≃ᵐ β) (s : Set β) : e.symm ⁻¹' e ⁻¹' s = s
参数：e : α ≃ᵐ β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_preimage_preimage`：symm_preimage_preimage {α β} (e : α ≃ β) (
s : Set β) : e.symm ⁻¹' e ⁻¹' s = s
-/
theorem symm_preimage_preimage (e : α ≃ᵐ β) (s : Set β) : e.symm ⁻¹' e ⁻¹' s = s :=
  e.toEquiv.symm_preimage_preimage s
/-
**MeasurableEquiv.image_eq_preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEq
uiv`。
形式化陈述：image_eq_preimage_symm (e : α ≃ᵐ β) (s : Set α) : e '' s = e.symm ⁻¹' s
参数：e : α ≃ᵐ β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem image_eq_preimage_symm (e : α ≃ᵐ β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage_symm s
/-
**MeasurableEquiv.preimage_symm** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：preimage_symm (e : α ≃ᵐ β) (s : Set α) : e.symm ⁻¹' s = e '' s
参数：e : α ≃ᵐ β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEquiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ᵐ
 β) (s : Set α) : e '' s = e.symm ⁻¹' s
-/
lemma preimage_symm (e : α ≃ᵐ β) (s : Set α) : e.symm ⁻¹' s = e '' s :=
  (image_eq_preimage_symm ..).symm
/-
**MeasurableEquiv.image_symm** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：image_symm (e : α ≃ᵐ β) (s : Set β) : e.symm '' s = e ⁻¹' s
参数：e : α ≃ᵐ β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_symm_eq_preimage`：image_symm_eq_preimage (e : α ≃ β) (s : Se
t β) : e.symm '' s = e ⁻¹' s
-/
lemma image_symm (e : α ≃ᵐ β) (s : Set β) : e.symm '' s = e ⁻¹' s := image_symm_eq_preimage ..
/-
**MeasurableEquiv.eq_image_iff_symm_image_eq** 是 Mathlib 中的一个引理，位于命名空间 `Measurab
leEquiv`。
形式化陈述：eq_image_iff_symm_image_eq (e : α ≃ᵐ β) (s : Set β) (t : Set α) : s = e ''
 t ↔ e.symm '' s = t
参数：e : α ≃ᵐ β；s : Set β；t : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEquiv.coe_toEquiv`：coe_toEquiv (e : α ≃ᵐ β) : (e.toEquiv : α -
> β) = e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_image_iff_symm_image_eq`：eq_image_iff_symm_image_eq {α β} (e : 
α ≃ β) (s : Set α) (t : Set β) : t = e '' s ↔ e.symm '' t = s
· 使用定理 `MeasurableEquiv.coe_toEquiv_symm`：coe_toEquiv_symm (e : α ≃ᵐ β) : (e.toE
quiv.symm : β -> α) = e.symm
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eq_image_iff_symm_image_eq (e : α ≃ᵐ β) (s : Set β) (t : Set α) :
    s = e '' t ↔ e.symm '' s = t := by
  rw [← coe_toEquiv, Equiv.eq_image_iff_symm_image_eq, coe_toEquiv_symm]

@[simp]
/-
**MeasurableEquiv.image_preimage** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：image_preimage (e : α ≃ᵐ β) (s : Set β) : e '' e ⁻¹' s = s
参数：e : α ≃ᵐ β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEquiv.coe_toEquiv`：coe_toEquiv (e : α ≃ᵐ β) : (e.toEquiv : α -
> β) = e
· 使用定理 `Equiv.image_preimage`：image_preimage {α β} (e : α ≃ β) (s : Set β) : e '
' e ⁻¹' s = s
-/
lemma image_preimage (e : α ≃ᵐ β) (s : Set β) : e '' e ⁻¹' s = s := by
  rw [← coe_toEquiv, Equiv.image_preimage]

@[simp]
/-
**MeasurableEquiv.preimage_image** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：preimage_image (e : α ≃ᵐ β) (s : Set α) : e ⁻¹' e '' s = s
参数：e : α ≃ᵐ β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEquiv.coe_toEquiv`：coe_toEquiv (e : α ≃ᵐ β) : (e.toEquiv : α -
> β) = e
· 使用定理 `Equiv.preimage_image`：preimage_image {α β} (e : α ≃ β) (s : Set α) : e ⁻
¹' e '' s = s
-/
lemma preimage_image (e : α ≃ᵐ β) (s : Set α) : e ⁻¹' e '' s = s := by
  rw [← coe_toEquiv, Equiv.preimage_image]

@[simp]
/-
**MeasurableEquiv.measurableSet_preimage** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEq
uiv`。
形式化陈述：measurableSet_preimage (e : α ≃ᵐ β) {s : Set β} : MeasurableSet (e ⁻¹' s) 
↔ MeasurableSet s
参数：e : α ≃ᵐ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.symm_preimage_preimage`：symm_preimage_preimage (e : α ≃ᵐ
 β) (s : Set β) : e.symm ⁻¹' e ⁻¹' s = s
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
-/
theorem measurableSet_preimage (e : α ≃ᵐ β) {s : Set β} :
    MeasurableSet (e ⁻¹' s) ↔ MeasurableSet s :=
  ⟨fun h => by simpa only [symm_preimage_preimage] using e.symm.measurable h, fun h =>
    e.measurable h⟩

@[simp]
/-
**MeasurableEquiv.measurableSet_image** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv
`。
形式化陈述：measurableSet_image (e : α ≃ᵐ β) : MeasurableSet (e '' s) ↔ MeasurableSet 
s
参数：e : α ≃ᵐ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ᵐ
 β) (s : Set α) : e '' s = e.symm ⁻¹' s
· 使用定理 `MeasurableEquiv.measurableSet_preimage`：measurableSet_preimage (e : α ≃ᵐ
 β) {s : Set β} : MeasurableSet (e ⁻¹' s) ↔ MeasurableSet s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measurableSet_image (e : α ≃ᵐ β) : MeasurableSet (e '' s) ↔ MeasurableSet s := by
  rw [image_eq_preimage_symm, measurableSet_preimage]
/-
**MeasurableEquiv.map_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] (e : α ≃ᵐ β),   MeasurableSpace.map (⇑e) inst = inst_1
参数：e : α ≃ᵐ β；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Measurable.le_map`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpace
 α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → m₂ ≤ MeasurableSpace.
map f m…
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasurableEquiv.measurableSet_preimage`：measurableSet_preimage (e : α ≃ᵐ
 β) {s : Set β} : MeasurableSet (e ⁻¹' s) ↔ MeasurableSet s
-/
@[simp] theorem map_eq (e : α ≃ᵐ β) : MeasurableSpace.map e ‹_› = ‹_› :=
  e.measurable.le_map.antisymm' fun _s ↦ e.measurableSet_preimage.1

/-- A measurable equivalence is a measurable embedding. -/
/-
**MeasurableEquiv.measurableEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] (e : α ≃ᵐ β),   MeasurableEmbedding ⇑e
参数：e : α ≃ᵐ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : Measu
rableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   Function.Injective ⇑e
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEquiv.measurableSet_image`：measurableSet_image (e : α ≃ᵐ β) : 
MeasurableSet (e '' s) ↔ MeasurableSet s

--- 原说明 ---
A measurable equivalence is a measurable embedding.
-/
protected theorem measurableEmbedding (e : α ≃ᵐ β) : MeasurableEmbedding e where
  injective := e.injective
  measurable := e.measurable
  measurableSet_image' := fun _ => e.measurableSet_image.2

/-- Equal measurable spaces are equivalent. -/
/-
**MeasurableEquiv.cast** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：{α β : Type u_6} → [i₁ : MeasurableSpace α] → [i₂ : MeasurableSpace β] → α
 = β → i₁ ≍ i₂ → α ≃ᵐ β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equal measurable spaces are equivalent.
-/
protected def cast {α β} [i₁ : MeasurableSpace α] [i₂ : MeasurableSpace β] (h : α = β)
    (hi : i₁ ≍ i₂) : α ≃ᵐ β where
  toEquiv := Equiv.cast h

/-- Measurable equivalence between `ULift α` and `α`. -/
/-
**MeasurableEquiv.ulift.** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Measurable equivalence between `ULift α` and `α`.
-/
def ulift.{u, v} {α : Type u} [MeasurableSpace α] : ULift.{v, u} α ≃ᵐ α :=
  ⟨Equiv.ulift, measurable_down, measurable_up⟩
/-
**MeasurableEquiv.measurable_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {f : β → γ} (e : α ≃
ᵐ β), Measurable (f ∘ ⇑e) ↔ Measurable f
参数：e : α ≃ᵐ β；f ∘ ⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.symm_trans_self`：symm_trans_self (e : α ≃ᵐ β) : e.symm.t
rans e = refl β
· 使用定理 `MeasurableEquiv.coe_toEquiv`：coe_toEquiv (e : α ≃ᵐ β) : (e.toEquiv : α -
> β) = e
-/
protected theorem measurable_comp_iff {f : β → γ} (e : α ≃ᵐ β) :
    Measurable (f ∘ e) ↔ Measurable f :=
  Iff.intro
    (fun hfe => by
      have : Measurable (f ∘ (e.symm.trans e).toEquiv) := hfe.comp e.symm.measurable
      rwa [coe_toEquiv, symm_trans_self] at this)
    fun h => h.comp e.measurable

/-- Any two types with unique elements are measurably equivalent. -/
/-
**MeasurableEquiv.ofUniqueOfUnique** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：ofUniqueOfUnique (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [Un
ique α] [Unique β] : α ≃ᵐ β where toEquiv
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any two types with unique elements are measurably equivalent.
-/
def ofUniqueOfUnique (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [Unique α] [Unique β] :
    α ≃ᵐ β where
  toEquiv := ofUnique α β

variable [MeasurableSpace δ] in
/-- Products of equivalent measurable spaces are equivalent. -/
/-
**MeasurableEquiv.prodCongr** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：prodCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α × γ ≃ᵐ β × δ where toEquiv
参数：ab : α ≃ᵐ β；cd : γ ≃ᵐ δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Products of equivalent measurable spaces are equivalent.
-/
def prodCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α × γ ≃ᵐ β × δ where
  toEquiv := .prodCongr ab.toEquiv cd.toEquiv

/-- Products of measurable spaces are symmetric. -/
/-
**MeasurableEquiv.prodComm** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：prodComm : α × β ≃ᵐ β × α where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Products of measurable spaces are symmetric.
-/
def prodComm : α × β ≃ᵐ β × α where
  toEquiv := .prodComm α β

set_option backward.defeqAttrib.useBackward true in
/-- Products of measurable spaces are associative. -/
/-
**MeasurableEquiv.prodAssoc** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：prodAssoc : (α × β) × γ ≃ᵐ α × β × γ where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Products of measurable spaces are associative.
-/
def prodAssoc : (α × β) × γ ≃ᵐ α × β × γ where
  toEquiv := .prodAssoc α β γ
  measurable_toFun := by eta_expand; dsimp; measurability
  measurable_invFun := by eta_expand; dsimp; measurability

/-- `PUnit` is a left identity for product of measurable spaces up to a measurable equivalence. -/
/-
**MeasurableEquiv.punitProd** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：punitProd : PUnit × α ≃ᵐ α where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)

--- 原说明 ---
`PUnit` is a left identity for product of measurable spaces up to a measurable e
quivalence.
-/
def punitProd : PUnit × α ≃ᵐ α where
  toEquiv := Equiv.punitProd α
  measurable_toFun := measurable_snd
  measurable_invFun := measurable_prodMk_left

/-- `PUnit` is a right identity for product of measurable spaces up to a measurable equivalence. -/
/-
**MeasurableEquiv.prodPUnit** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：prodPUnit : α × PUnit ≃ᵐ α where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)

--- 原说明 ---
`PUnit` is a right identity for product of measurable spaces up to a measurable 
equivalence.
-/
def prodPUnit : α × PUnit ≃ᵐ α where
  toEquiv := Equiv.prodPUnit α
  measurable_toFun := measurable_fst
  measurable_invFun := measurable_prodMk_right

variable [MeasurableSpace δ] in
/-- Sums of measurable spaces are symmetric. -/
/-
**MeasurableEquiv.sumCongr** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：sumCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α oplus γ ≃ᵐ β oplus δ where toEqui
v
参数：ab : α ≃ᵐ β；cd : γ ≃ᵐ δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sums of measurable spaces are symmetric.
-/
def sumCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α ⊕ γ ≃ᵐ β ⊕ δ where
  toEquiv := .sumCongr ab.toEquiv cd.toEquiv
  measurable_toFun := ab.measurable.sumMap cd.measurable
  measurable_invFun := ab.symm.measurable.sumMap cd.symm.measurable

/-- `s ×ˢ t ≃ (s × t)` as measurable spaces. -/
/-
**MeasurableEquiv.Set.prod** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv.Set`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : MeasurableSpace α] → [inst
_1 : MeasurableSpace β] → (s : Set α) → (t : Set β) → ↑(s ×ˢ t) ≃ᵐ ↑s × ↑t
参数：s : Set α；t : Set β；s ×ˢ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s ×ˢ t ≃ (s × t)` as measurable spaces.
-/
def Set.prod (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ᵐ s × t where
  toEquiv := Equiv.Set.prod s t
  measurable_toFun := .prodMk (by measurability) (by measurability)
  measurable_invFun := Measurable.subtype_mk <| by fun_prop

/-- `univ α ≃ α` as measurable spaces. -/
/-
**MeasurableEquiv.Set.univ** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv.Set`。
形式化陈述：(α : Type u_6) → [inst : MeasurableSpace α] → ↑Set.univ ≃ᵐ α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`univ α ≃ α` as measurable spaces.
-/
def Set.univ (α : Type*) [MeasurableSpace α] : (univ : Set α) ≃ᵐ α where
  toEquiv := Equiv.Set.univ α
  measurable_toFun := measurable_id.subtype_val
  measurable_invFun := measurable_id.subtype_mk

/-- `{a} ≃ Unit` as measurable spaces. -/
/-
**MeasurableEquiv.Set.singleton** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv.Set`。
形式化陈述：{α : Type u_1} → [inst : MeasurableSpace α] → (a : α) → ↑{a} ≃ᵐ Unit
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`{a} ≃ Unit` as measurable spaces.
-/
def Set.singleton (a : α) : ({a} : Set α) ≃ᵐ Unit where
  toEquiv := Equiv.Set.singleton a

/-- `α` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
/-
**MeasurableEquiv.Set.rangeInl** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv.Set`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [inst : MeasurableSpace α] → [inst_1 : M
easurableSpace β] → ↑(Set.range Sum.inl) ≃ᵐ α
参数：Set.range Sum.inl。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`α` is equivalent to its image in `α ⊕ β` as measurable spaces.
-/
def Set.rangeInl : (range Sum.inl : Set (α ⊕ β)) ≃ᵐ α where
  toEquiv := Equiv.Set.rangeInl α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine ⟨_, hs.inl_image, Set.ext ?_⟩
    simp
  measurable_invFun := Measurable.subtype_mk measurable_inl

/-- `β` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
/-
**MeasurableEquiv.Set.rangeInr** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv.Set`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [inst : MeasurableSpace α] → [inst_1 : M
easurableSpace β] → ↑(Set.range Sum.inr) ≃ᵐ β
参数：Set.range Sum.inr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`β` is equivalent to its image in `α ⊕ β` as measurable spaces.
-/
def Set.rangeInr : (range Sum.inr : Set (α ⊕ β)) ≃ᵐ β where
  toEquiv := Equiv.Set.rangeInr α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine ⟨_, hs.inr_image, Set.ext ?_⟩
    simp
  measurable_invFun := Measurable.subtype_mk measurable_inr

/-- Products distribute over sums (on the right) as measurable spaces. -/
/-
**MeasurableEquiv.sumProdDistrib** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：sumProdDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [Measurable
Space γ] : (α oplus β) × γ ≃ᵐ (α × γ) oplus (β × γ) where toEquiv
参数：α β γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Products distribute over sums (on the right) as measurable spaces.
-/
def sumProdDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    (α ⊕ β) × γ ≃ᵐ (α × γ) ⊕ (β × γ) where
  toEquiv := .sumProdDistrib α β γ
  measurable_toFun := by
    refine
      measurable_of_measurable_union_cover (range Sum.inl ×ˢ (univ : Set γ))
        (range Sum.inr ×ˢ (univ : Set γ)) (measurableSet_range_inl.prod MeasurableSet.univ)
        (measurableSet_range_inr.prod MeasurableSet.univ)
        (by rintro ⟨a | b, c⟩ <;> simp [Set.prod_eq]) ?_ ?_
    · refine (Set.prod (range Sum.inl) univ).symm.measurable_comp_iff.1 ?_
      refine (prodCongr Set.rangeInl (Set.univ _)).symm.measurable_comp_iff.1 ?_
      exact measurable_inl
    · refine (Set.prod (range Sum.inr) univ).symm.measurable_comp_iff.1 ?_
      refine (prodCongr Set.rangeInr (Set.univ _)).symm.measurable_comp_iff.1 ?_
      exact measurable_inr
  measurable_invFun :=
    measurable_fun_sum ((measurable_inl.comp measurable_fst).prodMk measurable_snd)
      ((measurable_inr.comp measurable_fst).prodMk measurable_snd)

/-- Products distribute over sums (on the left) as measurable spaces. -/
/-
**MeasurableEquiv.prodSumDistrib** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：prodSumDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [Measurable
Space γ] : α × (β oplus γ) ≃ᵐ (α × β) oplus (α × γ)
参数：α β γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Products distribute over sums (on the left) as measurable spaces.
-/
def prodSumDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    α × (β ⊕ γ) ≃ᵐ (α × β) ⊕ (α × γ) :=
  prodComm.trans <| (sumProdDistrib _ _ _).trans <| sumCongr prodComm prodComm

/-- Products distribute over sums as measurable spaces. -/
/-
**MeasurableEquiv.sumProdSum** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：sumProdSum (α β γ δ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSp
ace γ] [MeasurableSpace δ] : (α oplus β) × (γ oplus δ) ≃ᵐ ((α × γ) oplus (α × δ)
) oplus ((β × γ) oplus (β × δ))
参数：α β γ δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Products distribute over sums as measurable spaces.
-/
def sumProdSum (α β γ δ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] : (α ⊕ β) × (γ ⊕ δ) ≃ᵐ ((α × γ) ⊕ (α × δ)) ⊕ ((β × γ) ⊕ (β × δ)) :=
  (sumProdDistrib _ _ _).trans <| sumCongr (prodSumDistrib _ _ _) (prodSumDistrib _ _ _)

variable {π π' : δ' → Type*} [∀ x, MeasurableSpace (π x)] [∀ x, MeasurableSpace (π' x)]

/-- The type of functions `f : ∀ a, β a` such that for all `a` we have `p a (f a)` is measurably
equivalent to the type of functions `∀ a, {b : β a // p a b}`. -/
/-
**MeasurableEquiv.subtypePiEquivPi** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：subtypePiEquivPi {p : (a : δ') -> π a -> Prop} : { f : (a : δ') -> π a // 
forall (a : δ'), p a (f a) } ≃ᵐ ((a : δ') -> { b : π a // p a b }) where toEquiv
参数：a : δ'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of functions `f : ∀ a, β a` such that for all `a` we have `p a (f a)` i
s measurably
equivalent to the type of functions `∀ a, {b : β a // p a b}`.
-/
def subtypePiEquivPi {p : (a : δ') → π a → Prop} :
    { f : (a : δ') → π a // ∀ (a : δ'), p a (f a) } ≃ᵐ ((a : δ') → { b : π a // p a b }) where
  toEquiv := .subtypePiEquivPi
  measurable_toFun := measurable_pi_lambda _ (fun a =>
    ((measurable_pi_apply a).comp measurable_subtype_coe).subtype_mk)
  measurable_invFun := (measurable_pi_lambda _ (fun a =>
    measurable_subtype_coe.comp (measurable_pi_apply a))).subtype_mk

/-- A family of measurable equivalences `Π a, β₁ a ≃ᵐ β₂ a` generates a measurable equivalence
  between `Π a, β₁ a` and `Π a, β₂ a`. -/
/-
**MeasurableEquiv.piCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：piCongrRight (e : forall a, π a ≃ᵐ π' a) : (forall a, π a) ≃ᵐ forall a, π'
 a where toEquiv
参数：e : forall a, π a ≃ᵐ π' a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of measurable equivalences `Π a, β₁ a ≃ᵐ β₂ a` generates a measurable e
quivalence
  between `Π a, β₁ a` and `Π a, β₂ a`.
-/
def piCongrRight (e : ∀ a, π a ≃ᵐ π' a) : (∀ a, π a) ≃ᵐ ∀ a, π' a where
  toEquiv := .piCongrRight fun a => (e a).toEquiv
  measurable_toFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_toFun.comp (measurable_pi_apply i)
  measurable_invFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_invFun.comp (measurable_pi_apply i)

variable (π) in
/-- Moving a dependent type along an equivalence of coordinates, as a measurable equivalence. -/
/-
**MeasurableEquiv.piCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：piCongrLeft (f : δ ≃ δ') : (forall b, π (f b)) ≃ᵐ forall a, π a where __
参数：f : δ ≃ δ'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Moving a dependent type along an equivalence of coordinates, as a measurable equ
ivalence.
-/
def piCongrLeft (f : δ ≃ δ') : (∀ b, π (f b)) ≃ᵐ ∀ a, π a where
  __ := Equiv.piCongrLeft π f
  measurable_invFun := by
    rw [measurable_pi_iff]
    exact fun i => measurable_pi_apply (f i)
/-
**MeasurableEquiv.coe_piCongrLeft** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_piCongrLeft (f : δ ≃ δ') : ⇑(MeasurableEquiv.piCongrLeft π f) = f.piCo
ngrLeft π
参数：f : δ ≃ δ'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_piCongrLeft (f : δ ≃ δ') :
    ⇑(MeasurableEquiv.piCongrLeft π f) = f.piCongrLeft π := by rfl
/-
**MeasurableEquiv.piCongrLeft_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableE
quiv`。
形式化陈述：piCongrLeft_apply_apply {ι ι' : Type*} (e : ι ≃ ι') {β : ι' -> Type*} [for
all i', MeasurableSpace (β i')] (x : (i : ι) -> β (e i)) (i : ι) : piCongrLeft (
fun i' => β i') e x (e i) = x i
参数：e : ι ≃ ι'；β i'；x : (i : ι) -> β (e i)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.piCongrLeft.eq_1`：∀ {δ : Type u_4} {δ' : Type u_5} (π : 
δ' → Type u_6) [inst : (x : δ') → MeasurableSpace (π x)] (f : δ ≃ δ'),   Measura
bleEquiv.piCongrLeft π…
· 使用定理 `MeasurableEquiv.coe_mk`：coe_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Mea
surable e.symm) : ((⟨e, h1, h2⟩ : α ≃ᵐ β) : α -> β) = e
· 使用引理 `Equiv.piCongrLeft_apply_apply`：piCongrLeft_apply_apply (f : forall a, P 
(e a)) (a : α) : (piCongrLeft P e) f (e a) = f a
-/
lemma piCongrLeft_apply_apply {ι ι' : Type*} (e : ι ≃ ι') {β : ι' → Type*}
    [∀ i', MeasurableSpace (β i')] (x : (i : ι) → β (e i)) (i : ι) :
    piCongrLeft (fun i' ↦ β i') e x (e i) = x i := by
  rw [piCongrLeft, coe_mk, Equiv.piCongrLeft_apply_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism `(γ → α × β) ≃ (γ → α) × (γ → β)` as a measurable equivalence. -/
/-
**MeasurableEquiv.arrowProdEquivProdArrow** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableE
quiv`。
形式化陈述：arrowProdEquivProdArrow (α β γ : Type*) [MeasurableSpace α] [MeasurableSpa
ce β] : (γ -> α × β) ≃ᵐ (γ -> α) × (γ -> β) where __
参数：α β γ : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(γ → α × β) ≃ (γ → α) × (γ → β)` as a measurable equivalence.
-/
def arrowProdEquivProdArrow (α β γ : Type*) [MeasurableSpace α] [MeasurableSpace β] :
    (γ → α × β) ≃ᵐ (γ → α) × (γ → β) where
  __ := Equiv.arrowProdEquivProdArrow γ _ _
  measurable_toFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    fun_prop
  measurable_invFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    fun_prop

/-- The measurable equivalence `(α₁ → β₁) ≃ᵐ (α₂ → β₂)` induced by `α₁ ≃ α₂` and `β₁ ≃ᵐ β₂`. -/
/-
**MeasurableEquiv.arrowCongr'** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [MeasurableSpace β₁] [MeasurableSpace β₂
] (hα : α₁ ≃ α₂) (hβ : β₁ ≃ᵐ β₂) : (α₁ -> β₁) ≃ᵐ (α₂ -> β₂) where __
参数：hα : α₁ ≃ α₂；hβ : β₁ ≃ᵐ β₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The measurable equivalence `(α₁ → β₁) ≃ᵐ (α₂ → β₂)` induced by `α₁ ≃ α₂` and `β₁
 ≃ᵐ β₂`.
-/
def arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [MeasurableSpace β₁] [MeasurableSpace β₂]
    (hα : α₁ ≃ α₂) (hβ : β₁ ≃ᵐ β₂) :
    (α₁ → β₁) ≃ᵐ (α₂ → β₂) where
  __ := Equiv.arrowCongr' hα hβ
  measurable_toFun _ h := by
    exact MeasurableSet.preimage h <|
      measurable_pi_iff.mpr fun _ ↦ hβ.measurable.comp (measurable_pi_apply _)
  measurable_invFun _ h := by
    exact MeasurableSet.preimage h <|
      measurable_pi_iff.mpr fun _ ↦ hβ.symm.measurable.comp (measurable_pi_apply _)

/-- Pi-types are measurably equivalent to iterated products. -/
@[simps! -fullyApplied]
/-
**MeasurableEquiv.piMeasurableEquivTProd** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEq
uiv`。
形式化陈述：piMeasurableEquivTProd [DecidableEq δ'] {l : List δ'} (hnd : l.Nodup) (h :
 forall i, i in l) : (forall i, π i) ≃ᵐ List.TProd π l where toEquiv
参数：hnd : l.Nodup；h : forall i, i in l。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_tProd_mk`：measurable_tProd_mk (l : List δ) : Measurable (@TPr
od.mk δ X l)
· 使用定理 `measurable_tProd_elim'`：measurable_tProd_elim' [DecidableEq δ] {l : List
 δ} (h : forall i, i in l) : Measurable (TProd.elim' h : TProd X l -> forall i, 
X i)

--- 原说明 ---
Pi-types are measurably equivalent to iterated products.
-/
def piMeasurableEquivTProd [DecidableEq δ'] {l : List δ'} (hnd : l.Nodup) (h : ∀ i, i ∈ l) :
    (∀ i, π i) ≃ᵐ List.TProd π l where
  toEquiv := List.TProd.piEquivTProd hnd h
  measurable_toFun := measurable_tProd_mk l
  measurable_invFun := measurable_tProd_elim' h

variable (π) in
/-- The measurable equivalence `(∀ i, π i) ≃ᵐ π ⋆` when the domain of `π` only contains `⋆` -/
@[simps! -fullyApplied]
/-
**MeasurableEquiv.piUnique** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：piUnique [Unique δ'] : (forall i, π i) ≃ᵐ π default where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The measurable equivalence `(∀ i, π i) ≃ᵐ π ⋆` when the domain of `π` only conta
ins `⋆`
-/
def piUnique [Unique δ'] : (∀ i, π i) ≃ᵐ π default where
  toEquiv := Equiv.piUnique π

/-- If `α` has a unique term, then the type of function `α → β` is measurably equivalent to `β`. -/
@[simps! -fullyApplied]
/-
**MeasurableEquiv.funUnique** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：funUnique (α β : Type*) [Unique α] [MeasurableSpace β] : (α -> β) ≃ᵐ β
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` has a unique term, then the type of function `α → β` is measurably equiva
lent to `β`.
-/
def funUnique (α β : Type*) [Unique α] [MeasurableSpace β] : (α → β) ≃ᵐ β :=
  MeasurableEquiv.piUnique _

/-- The space `Π i : Fin 2, α i` is measurably equivalent to `α 0 × α 1`. -/
@[simps! -fullyApplied]
/-
**MeasurableEquiv.piFinTwo** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：piFinTwo (α : Fin 2 -> Type*) [forall i, MeasurableSpace (α i)] : (forall 
i, α i) ≃ᵐ α 0 × α 1 where toEquiv
参数：α : Fin 2 -> Type*；α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space `Π i : Fin 2, α i` is measurably equivalent to `α 0 × α 1`.
-/
def piFinTwo (α : Fin 2 → Type*) [∀ i, MeasurableSpace (α i)] : (∀ i, α i) ≃ᵐ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  measurable_invFun := measurable_pi_iff.2 <| Fin.forall_fin_two.2 ⟨measurable_fst, measurable_snd⟩

/-- The space `Fin 2 → α` is measurably equivalent to `α × α`. -/
@[simps! -fullyApplied]
/-
**MeasurableEquiv.finTwoArrow** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：finTwoArrow : (Fin 2 -> α) ≃ᵐ α × α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space `Fin 2 → α` is measurably equivalent to `α × α`.
-/
def finTwoArrow : (Fin 2 → α) ≃ᵐ α × α :=
  piFinTwo fun _ => α

/-- Measurable equivalence between `Π j : Fin (n + 1), α j` and
`α i × Π j : Fin n, α (Fin.succAbove i j)`.

Measurable version of `Fin.insertNthEquiv`. -/
@[simps! -fullyApplied]
/-
**MeasurableEquiv.piFinSuccAbove** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：piFinSuccAbove {n : Nat} (α : Fin (n + 1) -> Type*) [forall i, MeasurableS
pace (α i)] (i : Fin (n + 1)) : (forall j, α j) ≃ᵐ α i × forall j, α (i.succAbov
e j) where toEquiv
参数：α : Fin (n + 1) -> Type*；α i；i : Fin (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Measurable equivalence between `Π j : Fin (n + 1), α j` and
`α i × Π j : Fin n, α (Fin.succAbove i j)`.

Measurable version of `Fin.insertNthEquiv`.
-/
def piFinSuccAbove {n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, MeasurableSpace (α i)]
    (i : Fin (n + 1)) : (∀ j, α j) ≃ᵐ α i × ∀ j, α (i.succAbove j) where
  toEquiv := (Fin.insertNthEquiv α i).symm
  measurable_toFun := (measurable_pi_apply i).prodMk <| measurable_pi_iff.2 fun _ =>
    measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 <| i.forall_iff_succAbove.2
    ⟨by simp [measurable_fst], fun j => by simpa using! (measurable_pi_apply _).comp measurable_snd⟩

variable (π)

/-- Measurable equivalence between (dependent) functions on a type and pairs of functions on
`{i // p i}` and `{i // ¬p i}`. See also `Equiv.piEquivPiSubtypeProd`. -/
@[simps! -fullyApplied]
/-
**MeasurableEquiv.piEquivPiSubtypeProd** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEqui
v`。
形式化陈述：piEquivPiSubtypeProd (p : δ' -> Prop) [DecidablePred p] : (forall i, π i) 
≃ᵐ (forall i : Subtype p, π i) × forall i : { i // ¬p i }, π i where toEquiv
参数：p : δ' -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Measurable equivalence between (dependent) functions on a type and pairs of func
tions on
`{i // p i}` and `{i // ¬p i}`. See also `Equiv.piEquivPiSubtypeProd`.
-/
def piEquivPiSubtypeProd (p : δ' → Prop) [DecidablePred p] :
    (∀ i, π i) ≃ᵐ (∀ i : Subtype p, π i) × ∀ i : { i // ¬p i }, π i where
  toEquiv := .piEquivPiSubtypeProd p π

set_option backward.defeqAttrib.useBackward true in
/-- The measurable equivalence between the pi type over a sum type and a product of pi-types.
This is similar to `MeasurableEquiv.piEquivPiSubtypeProd`. -/
/-
**MeasurableEquiv.sumPiEquivProdPi** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：sumPiEquivProdPi (α : δ oplus δ' -> Type*) [forall i, MeasurableSpace (α i
)] : (forall i, α i) ≃ᵐ (forall i, α (.inl i)) × forall i', α (.inr i') where __
参数：α : δ oplus δ' -> Type*；α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The measurable equivalence between the pi type over a sum type and a product of 
pi-types.
This is similar to `MeasurableEquiv.piEquivPiSubtypeProd`.
-/
def sumPiEquivProdPi (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
    (∀ i, α i) ≃ᵐ (∀ i, α (.inl i)) × ∀ i', α (.inr i') where
  __ := Equiv.sumPiEquivProdPi α
  measurable_toFun := by eta_expand; dsimp; measurability
  measurable_invFun := by
    rw [measurable_pi_iff]; rintro (i | i)
    · exact measurable_pi_iff.1 measurable_fst _
    · exact measurable_pi_iff.1 measurable_snd _
/-
**MeasurableEquiv.coe_sumPiEquivProdPi** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEqui
v`。
形式化陈述：coe_sumPiEquivProdPi (α : δ oplus δ' -> Type*) [forall i, MeasurableSpace 
(α i)] : ⇑(MeasurableEquiv.sumPiEquivProdPi α) = Equiv.sumPiEquivProdPi α
参数：α : δ oplus δ' -> Type*；α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sumPiEquivProdPi (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
    ⇑(MeasurableEquiv.sumPiEquivProdPi α) = Equiv.sumPiEquivProdPi α := by rfl
/-
**MeasurableEquiv.coe_sumPiEquivProdPi_symm** 是 Mathlib 中的一个定理，位于命名空间 `Measurabl
eEquiv`。
形式化陈述：coe_sumPiEquivProdPi_symm (α : δ oplus δ' -> Type*) [forall i, MeasurableS
pace (α i)] : ⇑(MeasurableEquiv.sumPiEquivProdPi α).symm = (Equiv.sumPiEquivProd
Pi α).symm
参数：α : δ oplus δ' -> Type*；α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sumPiEquivProdPi_symm (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
    ⇑(MeasurableEquiv.sumPiEquivProdPi α).symm = (Equiv.sumPiEquivProdPi α).symm := by rfl

/-- The measurable equivalence for (dependent) functions on an Option type
  `(∀ i : Option δ, α i) ≃ᵐ (∀ (i : δ), α i) × α none`. -/
/-
**MeasurableEquiv.piOptionEquivProd** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：piOptionEquivProd {δ : Type*} (α : Option δ -> Type*) [forall i, Measurabl
eSpace (α i)] : (forall i, α i) ≃ᵐ (forall (i : δ), α i) × α none
参数：α : Option δ -> Type*；α i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The measurable equivalence for (dependent) functions on an Option type
  `(∀ i : Option δ, α i) ≃ᵐ (∀ (i : δ), α i) × α none`.
-/
def piOptionEquivProd {δ : Type*} (α : Option δ → Type*) [∀ i, MeasurableSpace (α i)] :
    (∀ i, α i) ≃ᵐ (∀ (i : δ), α i) × α none :=
  let e : Option δ ≃ δ ⊕ Unit := Equiv.optionEquivSumPUnit δ
  let em1 : ((i : δ ⊕ Unit) → α (e.symm i)) ≃ᵐ ((a : Option δ) → α a) :=
    MeasurableEquiv.piCongrLeft α e.symm
  let em2 : ((i : δ ⊕ Unit) → α (e.symm i)) ≃ᵐ ((i : δ) → α (e.symm (Sum.inl i)))
      × ((i' : Unit) → α (e.symm (Sum.inr i'))) :=
    MeasurableEquiv.sumPiEquivProdPi (fun i ↦ α (e.symm i))
  let em3 : ((i : δ) → α (e.symm (Sum.inl i))) × ((i' : Unit) → α (e.symm (Sum.inr i')))
      ≃ᵐ ((i : δ) → α (some i)) × α none :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl ((i : δ) → α (e.symm (Sum.inl i))))
      (MeasurableEquiv.piUnique fun i ↦ α (e.symm (Sum.inr i)))
  em1.symm.trans <| em2.trans em3

/-- The measurable equivalence `(∀ i : s, π i) × (∀ i : t, π i) ≃ᵐ (∀ i : s ∪ t, π i)`
  for disjoint finsets `s` and `t`. `Equiv.piFinsetUnion` as a measurable equivalence. -/
/-
**MeasurableEquiv.piFinsetUnion** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：piFinsetUnion [DecidableEq δ'] {s t : Finset δ'} (h : Disjoint s t) : ((fo
rall i : s, π i) × forall i : t, π i) ≃ᵐ forall i : (s union t : Finset δ'), π i
参数：h : Disjoint s t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The measurable equivalence `(∀ i : s, π i) × (∀ i : t, π i) ≃ᵐ (∀ i : s ∪ t, π i
)`
  for disjoint finsets `s` and `t`. `Equiv.piFinsetUnion` as a measurable equiva
lence.
-/
def piFinsetUnion [DecidableEq δ'] {s t : Finset δ'} (h : Disjoint s t) :
    ((∀ i : s, π i) × ∀ i : t, π i) ≃ᵐ ∀ i : (s ∪ t : Finset δ'), π i :=
  letI e := Finset.union s t h
  MeasurableEquiv.sumPiEquivProdPi (fun b ↦ π (e b)) |>.symm.trans <|
    .piCongrLeft (fun i : ↥(s ∪ t) ↦ π i) e

/-- If `s` is a measurable set in a measurable space, that space is equivalent
to the sum of `s` and `sᶜ`. -/
/-
**MeasurableEquiv.sumCompl** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：sumCompl {s : Set α} [DecidablePred (· in s)] (hs : MeasurableSet s) : s o
plus (sᶜ : Set α) ≃ᵐ α where toEquiv
参数：· in s；hs : MeasurableSet s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a measurable set in a measurable space, that space is equivalent
to the sum of `s` and `sᶜ`.
-/
def sumCompl {s : Set α} [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    s ⊕ (sᶜ : Set α) ≃ᵐ α where
  toEquiv := .sumCompl (· ∈ s)
  measurable_toFun := measurable_subtype_coe.sumElim measurable_subtype_coe
  measurable_invFun := Measurable.dite measurable_inl measurable_inr hs

/-- Convert a measurable involutive function `f` to a measurable permutation with
`toFun = invFun = f`. See also `Function.Involutive.toPerm`. -/
@[simps toEquiv]
/-
**MeasurableEquiv.ofInvolutive** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：ofInvolutive (f : α -> α) (hf : Involutive f) (hf' : Measurable f) : α ≃ᵐ 
α where toEquiv
参数：f : α -> α；hf : Involutive f；hf' : Measurable f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a measurable involutive function `f` to a measurable permutation with
`toFun = invFun = f`. See also `Function.Involutive.toPerm`.
-/
def ofInvolutive (f : α → α) (hf : Involutive f) (hf' : Measurable f) : α ≃ᵐ α where
  toEquiv := hf.toPerm
/-
**MeasurableEquiv.ofInvolutive_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`
。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] (f : α → α) (hf : Function.Inv
olutive f) (hf' : Measurable f) (a : α),   (MeasurableEquiv.ofInvolutive f hf hf
') a = f a
参数：f : α → α；hf : Function.Involutive f；hf' : Measurable f；a : α；MeasurableEquiv
.ofInvolutive f hf hf'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofInvolutive_apply (f : α → α) (hf : Involutive f) (hf' : Measurable f) (a : α) :
    ofInvolutive f hf hf' a = f a := rfl
/-
**MeasurableEquiv.ofInvolutive_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] (f : α → α) (hf : Function.Inv
olutive f) (hf' : Measurable f),   (MeasurableEquiv.ofInvolutive f hf hf').symm 
= MeasurableEquiv.ofInvolutive f hf hf'
参数：f : α → α；hf : Function.Involutive f；hf' : Measurable f；MeasurableEquiv.ofInv
olutive f hf hf'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofInvolutive_symm (f : α → α) (hf : Involutive f) (hf' : Measurable f) :
    (ofInvolutive f hf hf').symm = ofInvolutive f hf hf' := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `Set.ofPred` as a `MeasurableEquiv`. -/
@[simps]
/-
**MeasurableEquiv.setOfPred** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：{α : Type u_8} → (α → Prop) ≃ᵐ Set α
参数：α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Set.ofPred` as a `MeasurableEquiv`.
-/
protected def setOfPred {α : Type*} : (α → Prop) ≃ᵐ Set α where
  toFun p := {a | p a}
  invFun s a := a ∈ s

@[deprecated (since := "2026-07-09")]
protected alias setOf := MeasurableEquiv.setOfPred

@[deprecated (since := "2026-07-09")]
alias setOf_apply := MeasurableEquiv.setOfPred_apply

@[deprecated (since := "2026-07-09")]
alias setOf_symm_apply := MeasurableEquiv.setOfPred_symm_apply
/-
**MeasurableEquiv.coe_setOfPred** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：∀ {α : Type u_8}, ⇑MeasurableEquiv.setOfPred = Set.ofPred
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_setOfPred {α : Type*} :
    ⇑MeasurableEquiv.setOfPred = Set.ofPred (α := α) := rfl

@[deprecated (since := "2026-07-09")]
alias coe_setOf := coe_setOfPred

end MeasurableEquiv

namespace MeasurableEmbedding

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {g : β → α}

/-
**MeasurableEmbedding.comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {f : α → β},   MeasurableEmbedding f → MeasurableSpace.comap f ins
t_1 = inst
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
· 使用定理 `MeasurableEmbedding.measurableSet_image'`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measura
bleEmbedding f → ∀ ⦃s : Set α⦄…
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
-/
@[simp] theorem comap_eq (hf : MeasurableEmbedding f) : MeasurableSpace.comap f ‹_› = ‹_› :=
  hf.measurable.comap_le.antisymm fun _s h ↦
    ⟨_, hf.measurableSet_image' h, hf.injective.preimage_image _⟩
/-
**MeasurableEmbedding.iff_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEmbeddin
g`。
形式化陈述：iff_comap_eq : MeasurableEmbedding f ↔ Injective f ∧ MeasurableSpace.comap
 f ‹_› = ‹_› ∧ MeasurableSet (range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `MeasurableEmbedding.comap_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : Me
asurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbedding
 f → MeasurableSpa…
· 使用定理 `MeasurableEmbedding.measurableSet_range`：measurableSet_range (hf : Measu
rableEmbedding f) : MeasurableSet (range f)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `comap_measurable`：comap_measurable {m : MeasurableSpace β} (f : α -> β) 
: Measurable[m.comap f] f
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
-/
theorem iff_comap_eq :
    MeasurableEmbedding f ↔
      Injective f ∧ MeasurableSpace.comap f ‹_› = ‹_› ∧ MeasurableSet (range f) :=
  ⟨fun hf ↦ ⟨hf.injective, hf.comap_eq, hf.measurableSet_range⟩, fun hf ↦
    { injective := hf.1
      measurable := by rw [← hf.2.1]; exact comap_measurable f
      measurableSet_image' := by
        rw [← hf.2.1]
        rintro _ ⟨s, hs, rfl⟩
        simpa only [image_preimage_eq_inter_range] using hs.inter hf.2.2 }⟩

/-- A set is equivalent to its image under a function `f` as measurable spaces,
  if `f` is a measurable embedding -/
/-
**MeasurableEmbedding.equivImage** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEmbedding`
。
形式化陈述：equivImage (s : Set α) (hf : MeasurableEmbedding f) : s ≃ᵐ f '' s where to
Equiv
参数：s : Set α；hf : MeasurableEmbedding f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…

--- 原说明 ---
A set is equivalent to its image under a function `f` as measurable spaces,
  if `f` is a measurable embedding
-/
noncomputable def equivImage (s : Set α) (hf : MeasurableEmbedding f) : s ≃ᵐ f '' s where
  toEquiv := Equiv.Set.image f s hf.injective
  measurable_toFun := (hf.measurable.comp measurable_id.subtype_val).subtype_mk
  measurable_invFun := by
    rintro t ⟨u, hu, rfl⟩
    simpa [preimage_preimage, Set.image_symm_preimage hf.injective]
      using measurable_subtype_coe (hf.measurableSet_image' hu)

/-- The domain of `f` is equivalent to its range as measurable spaces,
  if `f` is a measurable embedding -/
/-
**MeasurableEmbedding.equivRange** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEmbedding`
。
形式化陈述：equivRange (hf : MeasurableEmbedding f) : α ≃ᵐ range f
参数：hf : MeasurableEmbedding f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The domain of `f` is equivalent to its range as measurable spaces,
  if `f` is a measurable embedding
-/
noncomputable def equivRange (hf : MeasurableEmbedding f) : α ≃ᵐ range f :=
  (MeasurableEquiv.Set.univ _).symm.trans <|
    (hf.equivImage univ).trans <| MeasurableEquiv.cast (by rw [image_univ]) (by rw [image_univ])
/-
**MeasurableEmbedding.of_measurable_inverse_on_range** 是 Mathlib 中的一个定理，位于命名空间 `
MeasurableEmbedding`。
形式化陈述：of_measurable_inverse_on_range {g : range f -> α} (hf₁ : Measurable f) (hf
₂ : MeasurableSet (range f)) (hg : Measurable g) (H : LeftInverse g (rangeFactor
ization f)) : MeasurableEmbedding f
参数：hf₁ : Measurable f；hf₂ : MeasurableSet (range f)；hg : Measurable g；H : LeftIn
verse g (rangeFactorization f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.rightInverse_of_surjective`：∀ {α : Sort u_1} {β : S
ort u_2} {f : α → β} {g : β → α},   Function.LeftInverse f g → Function.Surjecti
ve g → Function.RightInverse f g
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
· 使用定理 `Measurable.subtype_mk`：Measurable.subtype_mk {p : β -> Prop} {f : α -> β
} (hf : Measurable f) {h : forall x, p (f x)} : Measurable fun x => (⟨f x, h x⟩ 
: Subtype p…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `MeasurableEmbedding.comp`：comp (hg : MeasurableEmbedding g) (hf : Measur
ableEmbedding f) : MeasurableEmbedding (g ∘ f)
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
-/
theorem of_measurable_inverse_on_range {g : range f → α} (hf₁ : Measurable f)
    (hf₂ : MeasurableSet (range f)) (hg : Measurable g) (H : LeftInverse g (rangeFactorization f)) :
    MeasurableEmbedding f := by
  set e : α ≃ᵐ range f :=
    ⟨⟨rangeFactorization f, g, H, H.rightInverse_of_surjective rangeFactorization_surjective⟩,
      hf₁.subtype_mk, hg⟩
  exact (MeasurableEmbedding.subtype_coe hf₂).comp e.measurableEmbedding
/-
**MeasurableEmbedding.of_measurable_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Measurabl
eEmbedding`。
形式化陈述：of_measurable_inverse (hf₁ : Measurable f) (hf₂ : MeasurableSet (range f))
 (hg : Measurable g) (H : LeftInverse g f) : MeasurableEmbedding f
参数：hf₁ : Measurable f；hf₂ : MeasurableSet (range f)；hg : Measurable g；H : LeftIn
verse g f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.of_measurable_inverse_on_range`：of_measurable_invers
e_on_range {g : range f -> α} (hf₁ : Measurable f) (hf₂ : MeasurableSet (range f
)) (hg : Measurable g) (H : LeftInverse …
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
-/
theorem of_measurable_inverse (hf₁ : Measurable f) (hf₂ : MeasurableSet (range f))
    (hg : Measurable g) (H : LeftInverse g f) : MeasurableEmbedding f :=
  of_measurable_inverse_on_range hf₁ hf₂ (hg.comp measurable_subtype_coe) H

/-- The **measurable Schröder-Bernstein Theorem**: given measurable embeddings
`α → β` and `β → α`, we can find a measurable equivalence `α ≃ᵐ β`. -/
/-
**MeasurableEmbedding.schroederBernstein** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEm
bedding`。
形式化陈述：schroederBernstein {f : α -> β} {g : β -> α} (hf : MeasurableEmbedding f) 
(hg : MeasurableEmbedding g) : α ≃ᵐ β
参数：hf : MeasurableEmbedding f；hg : MeasurableEmbedding g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.measurableSet_image'`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measura
bleEmbedding f → ∀ ⦃s : Set α⦄…

--- 原说明 ---
The **measurable Schröder-Bernstein Theorem**: given measurable embeddings
`α → β` and `β → α`, we can find a measurable equivalence `α ≃ᵐ β`.
-/
noncomputable def schroederBernstein {f : α → β} {g : β → α} (hf : MeasurableEmbedding f)
    (hg : MeasurableEmbedding g) : α ≃ᵐ β := by
  let F : Set α → Set α := fun A => (g '' (f '' A)ᶜ)ᶜ
  -- We follow the proof of the usual SB theorem in mathlib,
  -- the crux of which is finding a fixed point of this F.
  -- However, we must find this fixed point manually instead of invoking Knaster-Tarski
  -- in order to make sure it is measurable.
  suffices Σ' A : Set α, MeasurableSet A ∧ F A = A by
    classical
    rcases this with ⟨A, Ameas, Afp⟩
    let B := f '' A
    have Bmeas : MeasurableSet B := hf.measurableSet_image' Ameas
    refine (MeasurableEquiv.sumCompl Ameas).symm.trans
      (MeasurableEquiv.trans ?_ (MeasurableEquiv.sumCompl Bmeas))
    apply MeasurableEquiv.sumCongr (hf.equivImage _)
    have : Aᶜ = g '' Bᶜ := by
      apply compl_injective
      rw [← Afp]
      simp [F, B]
    rw [this]
    exact (hg.equivImage _).symm
  have Fmono : ∀ {A B}, A ⊆ B → F A ⊆ F B := fun h =>
    compl_subset_compl.mpr <| Set.image_mono <| compl_subset_compl.mpr <| Set.image_mono h
  let X : ℕ → Set α := fun n => F^[n] univ
  refine ⟨iInter X, ?_, ?_⟩
  · refine MeasurableSet.iInter fun n ↦ ?_
    induction n with
    | zero => exact MeasurableSet.univ
    | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply]
      exact (hg.measurableSet_image' (hf.measurableSet_image' ih).compl).compl
  apply subset_antisymm
  · apply subset_iInter
    intro n
    cases n
    · exact subset_univ _
    rw [Function.iterate_succ', Function.comp_apply]
    exact Fmono (iInter_subset _ _)
  rintro x hx ⟨y, hy, rfl⟩
  rw [mem_iInter] at hx
  apply hy
  rw [hf.injective.injOn.image_iInter_eq]
  rw [mem_iInter]
  intro n
  specialize hx n.succ
  rw [Function.iterate_succ', Function.comp_apply] at hx
  by_contra h
  apply hx
  exact ⟨y, h, rfl⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MeasurableEmbedding.equivRange_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEmbe
dding`。
形式化陈述：equivRange_apply (hf : MeasurableEmbedding f) (x : α) : hf.equivRange x = 
⟨f x, mem_range_self x⟩
参数：hf : MeasurableEmbedding f；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `trivial`：True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `MeasurableEquiv.trans_apply`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : Measurab
leSpace γ] (ab : …
· 使用定理 `Equiv.Set.univ_symm_apply`：∀ (α : Type u_3) (a : α), (Equiv.Set.univ α).
symm a = ⟨a, trivial⟩
· 使用定理 `Equiv.Set.image_apply`：∀ {α : Type u_3} {β : Type u_4} (f : α → β) (s : 
Set α) (H : Function.Injective f) (p : ↑s),   (Equiv.Set.image f s H) p = ⟨f ↑p,
 ⋯⟩
· 使用定理 `set_coe_cast`：∀ {α : Type u} {s t : Set α} (H' : s = t) (H : ↑s = ↑t) (x
 : ↑s), cast H x = ⟨↑x, ⋯⟩
-/
lemma equivRange_apply (hf : MeasurableEmbedding f) (x : α) :
    hf.equivRange x = ⟨f x, mem_range_self x⟩ := by
  simp [MeasurableEmbedding.equivRange, MeasurableEquiv.cast, MeasurableEquiv.Set.univ,
    MeasurableEmbedding.equivImage]

@[simp]
/-
**MeasurableEmbedding.equivRange_symm_apply_mk** 是 Mathlib 中的一个引理，位于命名空间 `Measur
ableEmbedding`。
形式化陈述：equivRange_symm_apply_mk (hf : MeasurableEmbedding f) (x : α) : hf.equivRa
nge.symm ⟨f x, mem_range_self x⟩ = x
参数：hf : MeasurableEmbedding f；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEquiv.symm_apply_apply`：symm_apply_apply (e : α ≃ᵐ β) (x : α) 
: e.symm (e x) = x
· 使用引理 `MeasurableEmbedding.equivRange_apply`：equivRange_apply (hf : MeasurableE
mbedding f) (x : α) : hf.equivRange x = ⟨f x, mem_range_self x⟩
-/
lemma equivRange_symm_apply_mk (hf : MeasurableEmbedding f) (x : α) :
    hf.equivRange.symm ⟨f x, mem_range_self x⟩ = x := by
  nth_rw 3 [← hf.equivRange.symm_apply_apply x]
  rw [hf.equivRange_apply]

/-- The left-inverse of a `MeasurableEmbedding` -/
protected noncomputable
/-
**MeasurableEmbedding.invFun** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEmbedding`。
形式化陈述：invFun [Nonempty α] (hf : MeasurableEmbedding f) (x : β) : α
参数：hf : MeasurableEmbedding f；x : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def invFun [Nonempty α] (hf : MeasurableEmbedding f) (x : β) : α :=
  open scoped Classical in
  if hx : x ∈ range f then hf.equivRange.symm ⟨x, hx⟩ else (Nonempty.some inferInstance)

@[fun_prop]
/-
**MeasurableEmbedding.measurable_invFun** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEmb
edding`。
形式化陈述：measurable_invFun [Nonempty α] (hf : MeasurableEmbedding f) : Measurable (
hf.invFun : β -> α)
参数：hf : MeasurableEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.dite`：Measurable.dite [forall x, Decidable (x in s)] {f : s -
> β} (hf : Measurable f) {g : (sᶜ : Set α) -> β} (hg : Measurable g) (hs : Measu
rable…
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasurableEmbedding.measurableSet_range`：measurableSet_range (hf : Measu
rableEmbedding f) : MeasurableSet (range f)
-/
lemma measurable_invFun [Nonempty α] (hf : MeasurableEmbedding f) :
    Measurable (hf.invFun : β → α) :=
  open scoped Classical in
  Measurable.dite (by fun_prop) measurable_const hf.measurableSet_range
/-
**MeasurableEmbedding.leftInverse_invFun** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEm
bedding`。
形式化陈述：leftInverse_invFun [Nonempty α] (hf : MeasurableEmbedding f) : hf.invFun.L
eftInverse f
参数：hf : MeasurableEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用引理 `MeasurableEmbedding.equivRange_symm_apply_mk`：equivRange_symm_apply_mk (
hf : MeasurableEmbedding f) (x : α) : hf.equivRange.symm ⟨f x, mem_range_self x⟩
 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftInverse_invFun [Nonempty α] (hf : MeasurableEmbedding f) : hf.invFun.LeftInverse f := by
  intro x
  simp [MeasurableEmbedding.invFun]

end MeasurableEmbedding

/-
**MeasurableSpace.comap_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSpace.comap_compl {m' : MeasurableSpace β} [BooleanAlgebra β] (h
 : Measurable (compl : β -> β)) (f : α -> β) : MeasurableSpace.comap (fun a => (
f a)ᶜ) inferInstance = MeasurableSpace.comap f inferInstance
参数：h : Measurable (compl : β -> β)；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `MeasurableSpace.comap_comp`：comap_comp {f : β -> α} {g : γ -> β} : (m.co
map f).comap g = m.comap (f ∘ g)
· 使用定理 `MeasurableEmbedding.comap_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : Me
asurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbedding
 f → MeasurableSpa…
· 使用定理 `compl_involutive`：compl_involutive : Function.Involutive (compl : α -> α
)
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
-/
theorem MeasurableSpace.comap_compl {m' : MeasurableSpace β} [BooleanAlgebra β]
    (h : Measurable (compl : β → β)) (f : α → β) :
    MeasurableSpace.comap (fun a => (f a)ᶜ) inferInstance =
      MeasurableSpace.comap f inferInstance := by
  rw [← Function.comp_def, ← MeasurableSpace.comap_comp]
  congr
  exact (MeasurableEquiv.ofInvolutive _ compl_involutive h).measurableEmbedding.comap_eq
/-
**MeasurableSpace.comap_not** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop),   MeasurableSpace.comap (fun a => ¬p a) i
nferInstance = MeasurableSpace.comap p inferInstance
参数：p : α → Prop；fun a => ¬p a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.comap_compl`：MeasurableSpace.comap_compl {m' : Measurabl
eSpace β} [BooleanAlgebra β] (h : Measurable (compl : β -> β)) (f : α -> β) : Me
asurableSpace.com…
· 使用定理 `MeasurableSpace.measurableSet_top`：∀ {α : Type u_1} {s : Set α}, Measura
bleSet s
-/
@[simp] theorem MeasurableSpace.comap_not (p : α → Prop) :
    MeasurableSpace.comap (fun a ↦ ¬p a) inferInstance = MeasurableSpace.comap p inferInstance :=
  MeasurableSpace.comap_compl (fun _ _ ↦ measurableSet_top) _

section curry

/-! ### Currying as a measurable equivalence -/

namespace MeasurableEquiv

/-- The currying operation `Function.curry` as a measurable equivalence.
See `MeasurableEquiv.curry` for the non-dependent version. -/
@[simps!]
/-
**MeasurableEquiv.piCurry** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：piCurry {ι : Type*} {κ : ι -> Type*} (X : (i : ι) -> κ i -> Type*) [forall
 i j, MeasurableSpace (X i j)] : ((p : (i : ι) × κ i) -> X p.1 p.2) ≃ᵐ ((i : ι) 
-> (j : κ i) -> X i j) where toEquiv
参数：X : (i : ι) -> κ i -> Type*；X i j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The currying operation `Function.curry` as a measurable equivalence.
See `MeasurableEquiv.curry` for the non-dependent version.
-/
def piCurry {ι : Type*} {κ : ι → Type*} (X : (i : ι) → κ i → Type*)
    [∀ i j, MeasurableSpace (X i j)] :
    ((p : (i : ι) × κ i) → X p.1 p.2) ≃ᵐ ((i : ι) → (j : κ i) → X i j) where
  toEquiv := Equiv.piCurry X
/-
**MeasurableEquiv.coe_piCurry** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_piCurry {ι : Type*} {κ : ι -> Type*} (X : (i : ι) -> κ i -> Type*) [fo
rall i j, MeasurableSpace (X i j)] : ⇑(piCurry X) = Sigma.curry
参数：X : (i : ι) -> κ i -> Type*；X i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_piCurry {ι : Type*} {κ : ι → Type*} (X : (i : ι) → κ i → Type*)
    [∀ i j, MeasurableSpace (X i j)] : ⇑(piCurry X) = Sigma.curry := rfl
/-
**MeasurableEquiv.coe_piCurry_symm** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_piCurry_symm {ι : Type*} {κ : ι -> Type*} (X : (i : ι) -> κ i -> Type*
) [forall i j, MeasurableSpace (X i j)] : ⇑(piCurry X).symm = Sigma.uncurry
参数：X : (i : ι) -> κ i -> Type*；X i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_piCurry_symm {ι : Type*} {κ : ι → Type*} (X : (i : ι) → κ i → Type*)
    [∀ i j, MeasurableSpace (X i j)] : ⇑(piCurry X).symm = Sigma.uncurry := rfl

/-- The currying operation `Sigma.curry` as a measurable equivalence.
See `MeasurableEquiv.piCurry` for the dependent version. -/
@[simps!]
/-
**MeasurableEquiv.curry** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：curry (ι κ X : Type*) [MeasurableSpace X] : (ι × κ -> X) ≃ᵐ (ι -> κ -> X) 
where toEquiv
参数：ι κ X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The currying operation `Sigma.curry` as a measurable equivalence.
See `MeasurableEquiv.piCurry` for the dependent version.
-/
def curry (ι κ X : Type*) [MeasurableSpace X] : (ι × κ → X) ≃ᵐ (ι → κ → X) where
  toEquiv := Equiv.curry ι κ X
/-
**MeasurableEquiv.coe_curry** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_curry (ι κ X : Type*) [MeasurableSpace X] : ⇑(curry ι κ X) = Function.
curry
参数：ι κ X : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_curry (ι κ X : Type*) [MeasurableSpace X] : ⇑(curry ι κ X) = Function.curry := rfl
/-
**MeasurableEquiv.coe_curry_symm** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_curry_symm (ι κ X : Type*) [MeasurableSpace X] : ⇑(curry ι κ X).symm =
 Function.uncurry
参数：ι κ X : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_curry_symm (ι κ X : Type*) [MeasurableSpace X] :
    ⇑(curry ι κ X).symm = Function.uncurry := rfl

end MeasurableEquiv

end curry

