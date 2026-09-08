/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Field.Pointwise
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Generalized polar coordinate change

Consider an `n`-dimensional normed space `E` and an additive Haar measure `μ` on `E`.
Then `μ.toSphere` is the measure on the unit sphere
such that `μ.toSphere s` equals `n • μ (Set.Ioo 0 1 • s)`.

If `n ≠ 0`, then `μ` can be represented (up to `homeomorphUnitSphereProd`)
as the product of `μ.toSphere`
and the Lebesgue measure on `(0, +∞)` taken with density `fun r ↦ r ^ n`.

One can think about this fact as a version of polar coordinate change formula
for a general nontrivial normed space.

In this file we provide a way to rewrite integrals and integrability
of functions that depend on the norm only in terms of integral over `(0, +∞)`.
We also provide a positive lower estimate on the `(Measure.toSphere μ)`-measure
of a ball of radius `ε > 0` on the unit sphere.
-/

@[expose] public section

open Set Function Metric MeasurableSpace intervalIntegral
open scoped Pointwise ENNReal NNReal

local notation "dim" => Module.finrank ℝ

noncomputable section
namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]

namespace Measure

/-- If `μ` is an additive Haar measure on a normed space `E`,
then `μ.toSphere` is the measure on the unit sphere in `E`
such that `μ.toSphere s = Module.finrank ℝ E • μ (Set.Ioo (0 : ℝ) 1 • s)`. -/
/-
**MeasureTheory.Measure.toSphere** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：toSphere (μ : Measure E) : Measure (sphere (0 : E) 1)
参数：μ : Measure E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` is an additive Haar measure on a normed space `E`,
then `μ.toSphere` is the measure on the unit sphere in `E`
such that `μ.toSphere s = Module.finrank ℝ E • μ (Set.Ioo (0 : ℝ) 1 • s)`.
-/
def toSphere (μ : Measure E) : Measure (sphere (0 : E) 1) :=
  dim E • ((μ.comap (Subtype.val ∘ (homeomorphUnitSphereProd E).symm)).restrict
    (univ ×ˢ Iio ⟨1, mem_Ioi.2 one_pos⟩)).fst

variable (μ : Measure E)
/-
**MeasureTheory.Measure.toSphere_apply_aux** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：toSphere_apply_aux (s : Set (sphere (0 : E) 1)) (r : Ioi (0 : Real)) : μ (
(↑) '' (homeomorphUnitSphereProd E ⁻¹' s ×ˢ Iio r)) = μ (Ioo (0 : Real) r • ((↑)
 '' s))
参数：s : Set (sphere (0 : E) 1)；r : Ioi (0 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image2_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : 
Set α} {t : Set β}, Set.image2 (fun x1 x2 => x1 • x2) s t = s • t
· 使用定理 `Set.image2_image_right`：image2_image_right (f : α -> γ -> δ) (g : β -> γ
) : image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t
· 使用定理 `Homeomorph.image_symm`：image_symm (h : X ≃ₜ Y) : image h.symm = preimage
 h
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用引理 `Set.image_subtype_val_Ioi_Iio`：image_subtype_val_Ioi_Iio {a : α} (b : Io
i a) : Subtype.val '' Iio b = Ioo a b
· 使用定理 `Set.image2_image_left`：image2_image_left (f : γ -> β -> δ) (g : α -> γ) 
: image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t
· 使用定理 `Set.image2_swap`：image2_swap (s : Set α) (t : Set β) : image2 f s t = im
age2 (fun a b => f b a) t s
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
-/
theorem toSphere_apply_aux (s : Set (sphere (0 : E) 1)) (r : Ioi (0 : ℝ)) :
    μ ((↑) '' (homeomorphUnitSphereProd E ⁻¹' s ×ˢ Iio r)) = μ (Ioo (0 : ℝ) r • ((↑) '' s)) := by
  rw [← image2_smul, image2_image_right, ← Homeomorph.image_symm, image_image,
    ← image_subtype_val_Ioi_Iio, image2_image_left, image2_swap, ← image_prod]
  rfl

variable [BorelSpace E]
/-
**MeasureTheory.Measure.toSphere_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：toSphere_apply' {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) : μ.to
Sphere s = dim E * μ (Ioo (0 : Real) 1 • ((↑) '' s))
参数：sphere (0 : E) 1；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.toSphere.eq_1`：∀ {E : Type u_1} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : MeasurableSpace E]   (μ : Measu
reTheory.Measure E),   μ.…
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用定理 `MeasureTheory.Measure.fst_apply`：fst_apply {s : Set α} (hs : MeasurableS
et s) : ρ.fst s = ρ (Prod.fst ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用定理 `MeasurableEmbedding.comp`：comp (hg : MeasurableEmbedding g) (hf : Measur
ableEmbedding f) : MeasurableEmbedding (g ∘ f)
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `Homeomorph.measurableEmbedding`：Homeomorph.measurableEmbedding (h : γ ≃ₜ
 γ₂) : MeasurableEmbedding h
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.Subtype.secondCountableTopology`：∀ {α : Type u} [t : To
pologicalSpace α] (s : Set α) [SecondCountableTopology α], SecondCountableTopolo
gy ↑s
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Homeomorph.image_symm`：image_symm (h : X ≃ₜ Y) : image h.symm = preimage
 h
· 使用定理 `Set.univ_prod`：univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹
' t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.prod_eq`：prod_eq (s : Set α) (t : Set β) : s ×ˢ t = Prod.fst ⁻¹' s i
nter Prod.snd ⁻¹' t
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `MeasureTheory.Measure.toSphere_apply_aux`：toSphere_apply_aux (s : Set (s
phere (0 : E) 1)) (r : Ioi (0 : Real)) : μ ((↑) '' (homeomorphUnitSphereProd E ⁻
¹' s ×ˢ Iio r)) = μ (Ioo (0 : …
-/
theorem toSphere_apply' {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) :
    μ.toSphere s = dim E * μ (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  rw [toSphere, smul_apply, fst_apply hs, restrict_apply (measurable_fst hs),
    ((MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl).comp
      (Homeomorph.measurableEmbedding _)).comap_apply,
    image_comp, Homeomorph.image_symm, univ_prod, ← Set.prod_eq, nsmul_eq_mul, toSphere_apply_aux]
/-
**MeasureTheory.Measure.toSphere_apply_univ'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：toSphere_apply_univ' : μ.toSphere univ = dim E * μ (ball 0 1 \ {0})
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.toSphere_apply'`：toSphere_apply' {s : Set (sphere 
(0 : E) 1)} (hs : MeasurableSet s) : μ.toSphere s = dim E * μ (Ioo (0 : Real) 1 
• ((↑) '' s))
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用引理 `Ioo_smul_sphere_zero`：Ioo_smul_sphere_zero {a b r : Real} (ha : 0 <= a) 
(hr : 0 < r) : Ioo a b • sphere (0 : E) r = ball 0 (b * r) \ closedBall 0 (a * r
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Metric.closedBall_zero`：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, M
etric.closedBall x 0 = {x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSphere_apply_univ' : μ.toSphere univ = dim E * μ (ball 0 1 \ {0}) := by
  rw [μ.toSphere_apply' .univ, image_univ, Subtype.range_coe, Ioo_smul_sphere_zero] <;> simp
/-
**MeasureTheory.Measure.toSphere.instIsOpenPosMeasure** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure.toSphere`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : MeasurableSpace E]   (μ : MeasureTheory.Measure E) [BorelSpace E] [Fin
iteDimensional ℝ E] [μ.IsOpenPosMeasure], μ.toSphere.IsOpenPosMeasure
参数：μ : MeasureTheory.Measure E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instDiscreteTopologySubtype`：∀ {X : Type u} {p : X → Prop} [inst : Topol
ogicalSpace X] [DiscreteTopology X], DiscreteTopology (Subtype p)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.apply_eq_zero_of_isEmpty`：apply_eq_zero_of_isEmpty
 [IsEmpty α] {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) : μ s = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasureTheory.Measure.toSphere_apply'`：toSphere_apply' {s : Set (sphere 
(0 : E) 1)} (hs : MeasurableSet s) : μ.toSphere s = dim E * μ (Ioo (0 : Real) 1 
• ((↑) '' s))
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
（共 46 条，此处仅展示前 30 条）
-/
instance toSphere.instIsOpenPosMeasure [FiniteDimensional ℝ E] [μ.IsOpenPosMeasure] :
    μ.toSphere.IsOpenPosMeasure where
  open_pos := by
    nontriviality E using not_nonempty_iff_eq_empty
    rintro U hUo hU
    rw [μ.toSphere_apply' hUo.measurableSet]
    apply mul_ne_zero (by simp [Module.finrank_pos.ne'])
    exact isOpen_Ioo.smul_sphere one_ne_zero (by simp) hUo |>.measure_ne_zero _ (by simpa)

variable [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]

@[simp]
/-
**MeasureTheory.Measure.toSphere_apply_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：toSphere_apply_univ : μ.toSphere univ = dim E * μ (ball 0 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.apply_eq_zero_of_isEmpty`：apply_eq_zero_of_isEmpty
 [IsEmpty α] {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) : μ s = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.finrank_eq_zero_of_subsingleton`：finrank_eq_zero_of_subsingleton 
[Module.Free R M] [Subsingleton M] : Module.finrank R M = 0
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.toSphere_apply_univ'`：toSphere_apply_univ' : μ.toS
phere univ = dim E * μ (ball 0 1 \ {0})
· 使用定理 `MeasureTheory.measure_sdiff_null`：measure_sdiff_null (ht : μ t = 0) : μ 
(s \ t) = μ s
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass`：∀ {G : Type u
_1} [inst : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace 
G]   [IsTopologicalAddGroup G] [BorelSpace G] […
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `instPerfectSpaceOfT1SpaceOfConnectedSpaceOfNontrivial`：∀ {α : Type u_1} 
[inst : TopologicalSpace α] [T1Space α] [ConnectedSpace α] [Nontrivial α], Perfe
ctSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
（共 31 条，此处仅展示前 30 条）
-/
theorem toSphere_apply_univ : μ.toSphere univ = dim E * μ (ball 0 1) := by
  nontriviality E
  rw [toSphere_apply_univ', measure_sdiff_null (measure_singleton _)]

@[simp]
/-
**MeasureTheory.Measure.toSphere_real_apply_univ** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：toSphere_real_apply_univ : μ.toSphere.real univ = dim E * μ.real (ball 0 1
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.toSphere_apply_univ`：toSphere_apply_univ : μ.toSph
ere univ = dim E * μ (ball 0 1)
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `ENNReal.toReal_natCast`：toReal_natCast (n : Nat) : (n : Real>=0∞).toReal
 = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSphere_real_apply_univ : μ.toSphere.real univ = dim E * μ.real (ball 0 1) := by
  simp [measureReal_def]
/-
**MeasureTheory.Measure.toSphere_eq_zero_iff_finrank** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：toSphere_eq_zero_iff_finrank : μ.toSphere = 0 ↔ dim E = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `MeasureTheory.Measure.toSphere_apply_univ`：toSphere_apply_univ : μ.toSph
ere univ = dim E * μ (ball 0 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u
_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace 
G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toSphere_eq_zero_iff_finrank : μ.toSphere = 0 ↔ dim E = 0 := by
  rw [← measure_univ_eq_zero, toSphere_apply_univ]
  simp [IsOpen.measure_ne_zero]
/-
**MeasureTheory.Measure.toSphere_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：toSphere_eq_zero_iff : μ.toSphere = 0 ↔ Subsingleton E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.toSphere_eq_zero_iff_finrank`：toSphere_eq_zero_iff
_finrank : μ.toSphere = 0 ↔ dim E = 0
· 使用定理 `Module.finrank_zero_iff`：Module.finrank_zero_iff [IsDomain R] [IsTorsion
Free R M] : finrank R M = 0 ↔ Subsingleton M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
-/
theorem toSphere_eq_zero_iff : μ.toSphere = 0 ↔ Subsingleton E :=
  μ.toSphere_eq_zero_iff_finrank.trans Module.finrank_zero_iff

@[simp]
/-
**MeasureTheory.Measure.toSphere_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：toSphere_ne_zero [Nontrivial E] : μ.toSphere != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem toSphere_ne_zero [Nontrivial E] : μ.toSphere ≠ 0 := by
  simp [toSphere_eq_zero_iff, not_subsingleton]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFiniteMeasure μ.toSphere where
  measure_univ_lt_top := by
    rw [toSphere_apply_univ']
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) <|
      measure_ball_lt_top.trans_le' <| measure_mono sdiff_subset

/-- The measure on `(0, +∞)` that has density `(· ^ n)` with respect to the Lebesgue measure. -/
/-
**MeasureTheory.Measure.volumeIoiPow** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：volumeIoiPow (n : Nat) : Measure (Ioi (0 : Real))
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The measure on `(0, +∞)` that has density `(· ^ n)` with respect to the Lebesgue
 measure.
-/
def volumeIoiPow (n : ℕ) : Measure (Ioi (0 : ℝ)) :=
  .withDensity (.comap Subtype.val volume) fun r ↦ .ofReal (r.1 ^ n)
/-
**MeasureTheory.Measure.volumeIoiPow_apply_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：volumeIoiPow_apply_Iio (n : Nat) (x : Ioi (0 : Real)) : volumeIoiPow n (Ii
o x) = ENNReal.ofReal (x.1 ^ (n + 1) / (n + 1))
参数：n : Nat；x : Ioi (0 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.volumeIoiPow.eq_1`：∀ (n : ℕ),   MeasureTheory.Meas
ure.volumeIoiPow n =     (MeasureTheory.Measure.comap Subtype.val MeasureTheory.
volume).withDensity fun r => …
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `measurableSet_Iio`：measurableSet_Iio [ClosedIciTopology α] : MeasurableS
et (Iio a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `Subtype.instOrderClosedTopology`：∀ {α : Type u} [inst : TopologicalSpace
 α] [inst_1 : Preorder α] [t : OrderClosedTopology α] {p : α → Prop},   OrderClo
sedTopology (Subtype …
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.setLIntegral_subtype`：setLIntegral_subtype {s : Set α} (hs
 : MeasurableSet s) (t : Set s) (f : α -> Real>=0∞) : ∫⁻ x in t, f x ∂(μ.comap (
↑)) = ∫⁻ x in (↑) '' t, …
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用引理 `Set.image_subtype_val_Ioi_Iio`：image_subtype_val_Ioi_Iio {a : α} (b : Io
i a) : Subtype.val '' Iio b = Ioo a b
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ioc`：Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `intervalIntegral.intervalIntegrable_pow`：intervalIntegrable_pow : Interv
alIntegrable (fun x => x ^ n) μ a b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
（共 40 条，此处仅展示前 30 条）
-/
lemma volumeIoiPow_apply_Iio (n : ℕ) (x : Ioi (0 : ℝ)) :
    volumeIoiPow n (Iio x) = ENNReal.ofReal (x.1 ^ (n + 1) / (n + 1)) := by
  have hr₀ : 0 ≤ x.1 := le_of_lt x.2
  rw [volumeIoiPow, withDensity_apply _ measurableSet_Iio,
    setLIntegral_subtype measurableSet_Ioi _ fun a : ℝ ↦ .ofReal (a ^ n),
    image_subtype_val_Ioi_Iio, restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_pow _).1, ← integral_of_le hr₀]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact pow_nonneg hy.1.le _

/-- The intervals `(0, k + 1)` have finite measure `MeasureTheory.Measure.volumeIoiPow _`
and cover the whole open ray `(0, +∞)`. -/
/-
**MeasureTheory.Measure.finiteSpanningSetsIn_volumeIoiPow_range_Iio** 是 Mathlib 
中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：finiteSpanningSetsIn_volumeIoiPow_range_Iio (n : Nat) : FiniteSpanningSets
In (volumeIoiPow n) (range Iio) where set k
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intervals `(0, k + 1)` have finite measure `MeasureTheory.Measure.volumeIoiP
ow _`
and cover the whole open ray `(0, +∞)`.
-/
def finiteSpanningSetsIn_volumeIoiPow_range_Iio (n : ℕ) :
    FiniteSpanningSetsIn (volumeIoiPow n) (range Iio) where
  set k := Iio ⟨k + 1, mem_Ioi.2 k.cast_add_one_pos⟩
  set_mem _ := mem_range_self _
  finite k := by simp [volumeIoiPow_apply_Iio]
  spanning := iUnion_eq_univ_iff.2 fun x ↦ ⟨⌊x.1⌋₊, Nat.lt_floor_add_one x.1⟩
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : SigmaFinite (volumeIoiPow n) :=
  (finiteSpanningSetsIn_volumeIoiPow_range_Iio n).sigmaFinite

/-- The homeomorphism `homeomorphUnitSphereProd E` sends an additive Haar measure `μ`
to the product of `μ.toSphere` and `MeasureTheory.Measure.volumeIoiPow (dim E - 1)`,
where `dim E = Module.finrank ℝ E` is the dimension of `E`. -/
/-
**MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measurePreserving_homeomorphUnitSphereProd : MeasurePreserving (homeomorph
UnitSphereProd E) (μ.comap (↑)) (μ.toSphere.prod (volumeIoiPow (dim E - 1)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.finrank_eq_zero_of_subsingleton`：finrank_eq_zero_of_subsingleton 
[Module.Free R M] [Subsingleton M] : Module.finrank R M = 0
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Homeomorph.measurable`：∀ {α : Type u_1} {γ : Type u_3} [inst : Topologic
alSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]   [inst_3 : Top
ologicalSpa…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.Subtype.secondCountableTopology`：∀ {α : Type u} [t : To
pologicalSpace α] (s : Set α) [SecondCountableTopology α], SecondCountableTopolo
gy ↑s
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_eq_generateFrom`：prod_eq_generateFrom {μ : Me
asure α} {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)} (hC : generateFrom 
C = ‹_›) (hD : generateFrom D = …
· 使用定理 `MeasurableSpace.generateFrom_measurableSet`：generateFrom_measurableSet [
MeasurableSpace α] : generateFrom {s : Set α | MeasurableSet s} = ‹_›
· 使用定理 `borel_eq_generateFrom_Iio`：borel_eq_generateFrom_Iio : borel α = .genera
teFrom (range Iio)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `BorelSpace.measurable_eq`：∀ {α : Type u_6} {inst : TopologicalSpace α} {
inst_1 : MeasurableSpace α} [self : BorelSpace α], inst_1 = borel α
· 使用定理 `MeasurableSpace.isPiSystem_measurableSet`：isPiSystem_measurableSet {α : 
Type*} [MeasurableSpace α] : IsPiSystem { s : Set α | MeasurableSet s }
· 使用定理 `isPiSystem_Iio`：isPiSystem_Iio : IsPiSystem (range Iio : Set (Set α))
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureElemSphereOfNatRealToSphere`：∀ 
{E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 
: MeasurableSpace E]   (μ : MeasureTheory.Measure E) [Bore…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
（共 73 条，此处仅展示前 30 条）

--- 原说明 ---
The homeomorphism `homeomorphUnitSphereProd E` sends an additive Haar measure `μ
`
to the product of `μ.toSphere` and `MeasureTheory.Measure.volumeIoiPow (dim E - 
1)`,
where `dim E = Module.finrank ℝ E` is the dimension of `E`.
-/
theorem measurePreserving_homeomorphUnitSphereProd :
    MeasurePreserving (homeomorphUnitSphereProd E) (μ.comap (↑))
      (μ.toSphere.prod (volumeIoiPow (dim E - 1))) := by
  nontriviality E
  refine ⟨(homeomorphUnitSphereProd E).measurable, .symm ?_⟩
  refine prod_eq_generateFrom generateFrom_measurableSet
    ((borel_eq_generateFrom_Iio _).symm.trans BorelSpace.measurable_eq.symm)
    isPiSystem_measurableSet isPiSystem_Iio
    μ.toSphere.toFiniteSpanningSetsIn (finiteSpanningSetsIn_volumeIoiPow_range_Iio _)
    fun s hs ↦ forall_mem_range.2 fun r ↦ ?_
  have : Ioo (0 : ℝ) r = r.1 • Ioo (0 : ℝ) 1 := by simp [LinearOrderedField.smul_Ioo r.2.out]
  have hpos : 0 < dim E := Module.finrank_pos
  rw [(Homeomorph.measurableEmbedding _).map_apply, toSphere_apply' _ hs, volumeIoiPow_apply_Iio,
    comap_subtype_coe_apply (measurableSet_singleton _).compl, toSphere_apply_aux, this,
    smul_assoc, μ.addHaar_smul_of_nonneg r.2.out.le, Nat.sub_add_cancel hpos, Nat.cast_pred hpos,
    sub_add_cancel, mul_right_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul, mul_div_cancel₀]
  exacts [(Nat.cast_pos.2 hpos).ne', Nat.cast_nonneg _]

/-- An auxiliary lemma for `toSphereBallBound_mul_measure_unitBall_le_toSphere_ball`.
The estimate in this lemma is highly suboptimal.
For a non-private lemma, we should aim for a more precise and a more general fact
(e.g., an estimate on the radius of a ball centered at `t • x`
that is guaranteed to be a subset of the cone. -/
/-
**MeasureTheory.Measure.ball_subset_sector_of_small_epsilon** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary lemma for `toSphereBallBound_mul_measure_unitBall_le_toSphere_ball`
.
The estimate in this lemma is highly suboptimal.
For a non-private lemma, we should aim for a more precise and a more general fac
t
(e.g., an estimate on the radius of a ball centered at `t • x`
that is guaranteed to be a subset of the cone.
-/
private lemma ball_subset_sector_of_small_epsilon
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (hx : ‖x‖ = 1) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 2) :
    ball ((1 - ε / 4) • x) (ε / 4) ⊆
      Ioo (0 : ℝ) 1 • (ball x ε ∩ sphere (0 : E) 1) := by
  intro y hy
  rw [mem_ball] at hy
  have habs : |1 - ε / 4| = 1 - ε / 4 := abs_of_nonneg (by linarith)
  -- Note that $y ≠ 0$.
  have hy₀ : y ≠ 0 := by
    rintro rfl
    have : 1 - ε / 4 < ε / 4 := by simpa [norm_smul, habs, hx] using hy
    linarith
  have hy₁ : ‖y‖ < 1 := calc
    ‖y‖ ≤ dist y ((1 - ε / 4) • x) + ‖(1 - ε / 4) • x‖ := by
      simpa using dist_triangle y ((1 - ε / 4) • x) 0
    _ < ε / 4 + ‖(1 - ε / 4) • x‖ := by gcongr
    _ = 1 := by simp [norm_smul, habs, hx]
  -- Let $u = y / \|y\|$. We show $\|u - x\| < \epsilon$.
  set u : E := ‖y‖⁻¹ • y
  have hu₁ : ‖u‖ = 1 := by simp [u, hy₀, norm_smul]
  refine ⟨‖y‖, ⟨by simpa, hy₁⟩, u, ⟨?_, by simpa⟩, by simp [u, hy₀]⟩
  rw [mem_ball]
  have hyx := calc
    dist y x ≤ dist y ((1 - ε / 4) • x) + dist ((1 - ε / 4) • x) x := dist_triangle ..
    _ < ε / 4 + dist ((1 - ε / 4) • x) x := by gcongr
    _ = ε / 4 + ε / 4 := by simp [sub_smul, norm_smul, hx, abs_of_pos hε]
    _ = ε / 2 := by ring
  have huy : dist u y ≤ dist x y := by
    have H : u - y = (1 - ‖y‖) • u := by simp [u, hy₀, sub_smul]
    simpa [dist_eq_norm_sub, H, norm_smul, abs_of_nonneg, hy₁.le, hu₁, hx]
      using dist_triangle x y 0
  linarith [dist_triangle u y x, dist_comm x y]

/-- Lower estimate on the measure of the `ε`-cone in an `n`-dimensional normed space
divided by the measure of the ball. -/
@[irreducible]
/-
**MeasureTheory.Measure.toSphereBallBound** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：toSphereBallBound (n : Nat) (ε : Real) : Real>=0
参数：n : Nat；ε : Real。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lower estimate on the measure of the `ε`-cone in an `n`-dimensional normed space
divided by the measure of the ball.
-/
noncomputable def toSphereBallBound (n : ℕ) (ε : ℝ) : ℝ≥0 :=
  if n ≠ 0 ∧ 0 < ε then n * ((min (Real.toNNReal ε) 2) / 4) ^ n else 1
/-
**MeasureTheory.Measure.toSphereBallBound_pos** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：toSphereBallBound_pos (n : Nat) (ε : Real) : 0 < toSphereBallBound n ε
参数：n : Nat；ε : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `Real.toNNReal_pos`：toNNReal_pos {r : Real} : 0 < Real.toNNReal r ↔ 0 < r
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem toSphereBallBound_pos (n : ℕ) (ε : ℝ) : 0 < toSphereBallBound n ε := by
  unfold toSphereBallBound
  split_ifs with h
  · cases h
    positivity
  · positivity

/-- A ball of radius `ε` on the unit sphere in a real normed space
has measure at least `toSphereBallBound n ε * μ (ball 0 1)`,
where `n` is the dimension of the space,
`toSphereBallBound n ε` is a lower estimate that depends only on the dimension and `ε`,
which is positive for positive `n` and `ε`. -/
/-
**MeasureTheory.Measure.toSphereBallBound_mul_measure_unitBall_le_toSphere_ball*
* 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：toSphereBallBound_mul_measure_unitBall_le_toSphere_ball {ε : Real} (hε : 0
 < ε) (x : sphere (0 : E) 1) : toSphereBallBound (Module.finrank Real E) ε * μ (
ball 0 1) <= μ.toSphere (ball x ε)
参数：hε : 0 < ε；x : sphere (0 : E) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_of_mem_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {r
 : ℝ} (x : ↑(Metric.sphere 0 r)), ‖↑x‖ = r
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `MeasureTheory.Measure.toSphere_apply'`：toSphere_apply' {s : Set (sphere 
(0 : E) 1)} (hs : MeasurableSet s) : μ.toSphere s = dim E * μ (Ioo (0 : Real) 1 
• ((↑) '' s))
· 使用定理 `measurableSet_ball`：measurableSet_ball : MeasurableSet (Metric.ball x ε)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Subtype.image_ball`：image_ball {p : α -> Prop} (a : {a // p a}) (r : Rea
l) : Subtype.val '' (ball a r) = ball a.1 r inter {a | p a}
· 使用定理 `Set.ofPred_mem_eq`：∀ {α : Type u} {s : Set α}, {x | x ∈ s} = s
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `_private.Mathlib.MeasureTheory.Constructions.HaarToSphere.0.MeasureTheor
y.Measure.ball_subset_sector_of_small_epsilon`：∀ {E : Type u_2} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] (x : E),   ‖x‖ = 1 →     ∀ (ε : ℝ),    
   0 < ε → ε ≤ 2 → Metric.b…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
A ball of radius `ε` on the unit sphere in a real normed space
has measure at least `toSphereBallBound n ε * μ (ball 0 1)`,
where `n` is the dimension of the space,
`toSphereBallBound n ε` is a lower estimate that depends only on the dimension a
nd `ε`,
which is positive for positive `n` and `ε`.
-/
theorem toSphereBallBound_mul_measure_unitBall_le_toSphere_ball {ε : ℝ}
    (hε : 0 < ε) (x : sphere (0 : E) 1) :
    toSphereBallBound (Module.finrank ℝ E) ε * μ (ball 0 1) ≤ μ.toSphere (ball x ε) := by
  have : Nontrivial E := ⟨⟨x, 0, ne_of_apply_ne Norm.norm (by simp)⟩⟩
  wlog hε₂ : ε ≤ 2 generalizing ε
  · trans μ.toSphere (ball x (min ε 2))
    · simpa [Real.toNNReal_monotone.map_min, toSphereBallBound]
        using this (ε := min ε 2) (by simp [hε]) (by simp)
    · gcongr
      simp
  rw [μ.toSphere_apply' measurableSet_ball, Subtype.image_ball, ofPred_mem_eq]
  grw [← ball_subset_sector_of_small_epsilon] <;> try assumption
  · have hdim : Module.finrank ℝ E ≠ 0 := Module.finrank_pos.ne'
    have : min (ENNReal.ofReal ε) 2 = ENNReal.ofReal ε := by simpa
    simp (disch := positivity) [μ.addHaar_ball_of_pos (r := ε / 4), ENNReal.ofReal_div_of_pos,
      toSphereBallBound, mul_assoc, ENNReal.ofNNReal_toNNReal, this, hdim, hε]
  · simp

/-- A ball of radius `ε` on the unit sphere in a real normed space
has measure at least `toSphereBallBound n ε * μ (ball 0 1)`,
where `n` is the dimension of the space,
`toSphereBallBound n ε` is a lower estimate that depends only on the dimension and `ε`,
which is positive for positive `n` and `ε`.

This is a version stated in terms `MeasureTheory.Measure.real`. -/
/-
**MeasureTheory.Measure.toSphereBallBound_mul_measureReal_unitBall_le_toSphere_b
all** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball {ε : Real} (hε
 : 0 < ε) (x : sphere (0 : E) 1) : toSphereBallBound (Module.finrank Real E) ε *
 μ.real (ball 0 1) <= μ.toSphere.real (ball x ε)
参数：hε : 0 < ε；x : sphere (0 : E) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.real.eq_1`：∀ {α : Type u_6} {m : MeasurableSpace α
} (μ : MeasureTheory.Measure α) (s : Set α), μ.real s = (μ s).toReal
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureElemSphereOfNatRealToSphere`：∀ 
{E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 
: MeasurableSpace E]   (μ : MeasureTheory.Measure E) [Bore…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.Measure.toSphereBallBound_mul_measure_unitBall_le_toSphere
_ball`：toSphereBallBound_mul_measure_unitBall_le_toSphere_ball {ε : Real} (hε : 
0 < ε) (x : sphere (0 : E) 1) : toSphereBallBound (Module.finrank R…
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `ENNReal.coe_toReal`：∀ (r : NNReal), (↑r).toReal = ↑r

--- 原说明 ---
A ball of radius `ε` on the unit sphere in a real normed space
has measure at least `toSphereBallBound n ε * μ (ball 0 1)`,
where `n` is the dimension of the space,
`toSphereBallBound n ε` is a lower estimate that depends only on the dimension a
nd `ε`,
which is positive for positive `n` and `ε`.

This is a version stated in terms `MeasureTheory.Measure.real`.
-/
theorem toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball
    {ε : ℝ} (hε : 0 < ε) (x : sphere (0 : E) 1) :
    toSphereBallBound (Module.finrank ℝ E) ε * μ.real (ball 0 1) ≤
      μ.toSphere.real (ball x ε) := by
  grw [Measure.real, Measure.real, ← toSphereBallBound_mul_measure_unitBall_le_toSphere_ball μ hε,
    ENNReal.toReal_mul, ENNReal.coe_toReal]
  simp

end Measure

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Nontrivial E] (μ : Measure E) [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]

/-
**MeasureTheory.integrable_fun_norm_addHaar** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：integrable_fun_norm_addHaar {f : Real -> F} : Integrable (f ‖·‖) μ ↔ Integ
rableOn (fun y : Real => y ^ (dim E - 1) • f y) (Ioi 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.integrable_comp_emb`：∀ {α : Type u_1} {δ
 : Type u_4} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   [inst : MeasurableSpace δ] [inst_1 : …
· 使用定理 `MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`：measur
ePreserving_homeomorphUnitSphereProd : MeasurePreserving (homeomorphUnitSpherePr
od E) (μ.comap (↑)) (μ.toSphere.prod (volumeIoiPow (di…
· 使用引理 `Homeomorph.measurableEmbedding`：Homeomorph.measurableEmbedding (h : γ ≃ₜ
 γ₂) : MeasurableEmbedding h
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.Subtype.secondCountableTopology`：∀ {α : Type u} [t : To
pologicalSpace α] (s : Set α) [SecondCountableTopology α], SecondCountableTopolo
gy ↑s
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.restrict_compl_singleton`：restrict_compl_singleton (a : α)
 : μ.restrict ({a}ᶜ) = μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass`：∀ {G : Type u
_1} [inst : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace 
G]   [IsTopologicalAddGroup G] [BorelSpace G] […
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `instPerfectSpaceOfT1SpaceOfConnectedSpaceOfNontrivial`：∀ {α : Type u_1} 
[inst : TopologicalSpace α] [T1Space α] [ConnectedSpace α] [Nontrivial α], Perfe
ctSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `NormedSpace.instPathConnectedSpace`：∀ {E : Type u_1} [inst : SeminormedA
ddCommGroup E] [NormedSpace ℝ E], PathConnectedSpace E
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.integrableOn_iff_comap_subtypeVal`：integrableOn_iff_comap_
subtypeVal (hs : MeasurableSet s) : IntegrableOn f s μ ↔ Integrable (f ∘ (↑) : s
 -> ε) (μ.comap (↑))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
（共 67 条，此处仅展示前 30 条）
-/
lemma integrable_fun_norm_addHaar {f : ℝ → F} :
    Integrable (f ‖·‖) μ ↔ IntegrableOn (fun y : ℝ ↦ y ^ (dim E - 1) • f y) (Ioi 0) := by
  have := μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb (g := f ∘ (↑) ∘ Prod.snd)
    (Homeomorph.measurableEmbedding _)
  simp only [comp_def, homeomorphUnitSphereProd_apply_snd_coe] at this
  rw [← restrict_compl_singleton (μ := μ) 0, ← IntegrableOn,
    integrableOn_iff_comap_subtypeVal (by measurability), comp_def, this,
    Integrable.comp_snd_iff (β := Ioi 0) (f := (f <| Subtype.val ·)),
    integrableOn_iff_comap_subtypeVal, comp_def, Measure.volumeIoiPow,
    integrable_withDensity_iff_integrable_smul', integrable_congr]
  · refine .of_forall ?_
    rintro ⟨x, hx : 0 < x⟩
    simp (disch := positivity) [ENNReal.toReal_ofReal]
  · fun_prop
  · simp
  · measurability
  · simp
/-
**MeasureTheory.integrableOn_fun_norm_addHaar** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：integrableOn_fun_norm_addHaar {f : Real -> F} {r : Real} : IntegrableOn (f
un x : E => f ‖x‖) (ball (0 : E) r) μ ↔ IntegrableOn (fun y => y ^ (Module.finra
nk Real E - 1) • f y) (Ioo 0 r)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `measurableSet_ball`：measurableSet_ball : MeasurableSet (Metric.ball x ε)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.integrable_fun_norm_addHaar`：integrable_fun_norm_addHaar {
f : Real -> F} : Integrable (f ‖·‖) μ ↔ IntegrableOn (fun y : Real => y ^ (dim E
 - 1) • f y) (Ioi 0)
· 使用定理 `MeasureTheory.integrableOn_congr_fun`：integrableOn_congr_fun (hst : EqOn
 f g s) (hs : MeasurableSet s) : IntegrableOn f s μ ↔ IntegrableOn g s μ
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
（共 45 条，此处仅展示前 30 条）
-/
lemma integrableOn_fun_norm_addHaar {f : ℝ → F} {r : ℝ} :
    IntegrableOn (fun x : E => f ‖x‖) (ball (0 : E) r) μ ↔
    IntegrableOn (fun y ↦ y ^ (Module.finrank ℝ E - 1) • f y) (Ioo 0 r) := by
  calc
    _ ↔ Integrable (fun x ↦ (Iio r).indicator f ‖x‖) μ := by
      rw [← integrable_indicator_iff measurableSet_ball]
      apply integrable_congr
      filter_upwards with x
      simp [indicator]
    _ ↔ IntegrableOn ((Ioo 0 r).indicator fun y ↦ y ^ (Module.finrank ℝ E - 1) • f y) (Ioi 0) := by
      rw [integrable_fun_norm_addHaar μ (f := indicator (Iio r) f),
        integrableOn_congr_fun _ measurableSet_Ioi]
      intro x (hx : 0 < x)
      by_cases hxr : x < r <;> simp [hxr, hx]
    _ ↔ Integrable ((Ioo 0 r).indicator fun y ↦ y ^ (Module.finrank ℝ E - 1) • f y) := by
      rw [MeasureTheory.integrableOn_iff_integrable_of_support_subset]
      intro x hx
      simp only [support_indicator, mem_inter_iff, mem_Ioo, Function.mem_support, ne_eq,
        smul_eq_zero, pow_eq_zero_iff', not_or, not_and, Decidable.not_not] at hx
      refine mem_Ioi.mpr hx.1.1
    _ ↔ IntegrableOn (fun y ↦ y ^ (Module.finrank ℝ E - 1) • f y) (Ioo 0 r) volume := by
      rw [← integrable_indicator_iff measurableSet_Ioo, ← integrableOn_univ]
/-
**MeasureTheory.integral_fun_norm_addHaar** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integral_fun_norm_addHaar (f : Real -> F) : ∫ x, f (‖x‖) ∂μ = dim E • μ.re
al (ball 0 1) • ∫ y in Ioi (0 : Real), y ^ (dim E - 1) • f y
参数：f : Real -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_subtype_comap`：integral_subtype_comap {α} [Measur
ableSpace α] {μ : Measure α} {s : Set α} (hs : MeasurableSet s) (f : α -> G) : ∫
 x : s, f (x : α) ∂(Measur…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `MeasureTheory.restrict_compl_singleton`：restrict_compl_singleton (a : α)
 : μ.restrict ({a}ᶜ) = μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass`：∀ {G : Type u
_1} [inst : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace 
G]   [IsTopologicalAddGroup G] [BorelSpace G] […
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instPerfectSpaceOfT1SpaceOfConnectedSpaceOfNontrivial`：∀ {α : Type u_1} 
[inst : TopologicalSpace α] [T1Space α] [ConnectedSpace α] [Nontrivial α], Perfe
ctSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `NormedSpace.instPathConnectedSpace`：∀ {E : Type u_1} [inst : SeminormedA
ddCommGroup E] [NormedSpace ℝ E], PathConnectedSpace E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `homeomorphUnitSphereProd_apply_snd_coe`：∀ (E : Type u_1) [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] (x : ↑{0}ᶜ),   ↑((homeomorphUnitSphere
Prod E) x).2 = ‖↑x‖
（共 66 条，此处仅展示前 30 条）
-/
lemma integral_fun_norm_addHaar (f : ℝ → F) :
    ∫ x, f (‖x‖) ∂μ = dim E • μ.real (ball 0 1) • ∫ y in Ioi (0 : ℝ), y ^ (dim E - 1) • f y :=
  calc
    ∫ x, f (‖x‖) ∂μ = ∫ x : ({(0)}ᶜ : Set E), f (‖x.1‖) ∂(μ.comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl fun x ↦ f (‖x‖),
        restrict_compl_singleton]
    _ = ∫ x, f x.2 ∂μ.toSphere.prod (.volumeIoiPow (dim E - 1)) := by
      simpa using μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _) (f ∘ Subtype.val ∘ Prod.snd)
    _ = μ.toSphere.real univ • ∫ x : Ioi (0 : ℝ), f x ∂.volumeIoiPow (dim E - 1) :=
      integral_fun_snd (f ∘ Subtype.val)
    _ = _ := by
      simp only [Measure.volumeIoiPow, ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul, μ.toSphere_real_apply_univ,
        ← nsmul_eq_mul, smul_assoc,
        integral_subtype_comap measurableSet_Ioi fun a ↦ Real.toNNReal (a ^ (dim E - 1)) • f a,
        setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_]
      · rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _)]
      · exact (measurable_subtype_coe.pow_const _).real_toNNReal

end MeasureTheory

