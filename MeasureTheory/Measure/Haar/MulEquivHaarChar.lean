/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Scaling Haar measure by a continuous isomorphism

If `G` is a locally compact topological group and `μ` is a regular Haar measure
on `G`, then an isomorphism `φ : G ≃ₜ* G` scales this measure by some positive
real constant which we call `mulEquivHaarChar φ`.

## Main definitions

* `mulEquivHaarChar φ`: the positive real such that `(mulEquivHaarChar φ) • map φ μ = μ`
  for `μ` a regular Haar measure.
* `addEquivAddHaarChar φ`: the additive version.

-/

@[expose] public section

open MeasureTheory.Measure

open scoped NNReal Pointwise ENNReal

namespace MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- If `φ : G ≃ₜ* G` then `mulEquivHaarChar φ` is the positive real factor by which
`φ` scales Haar measures on `G`. -/
@[to_additive /-- If `φ : A ≃ₜ+ A` then `addEquivAddHaarChar φ` is the positive
real factor by which `φ` scales Haar measures on `A`. -/]
/-
**MeasureTheory.mulEquivHaarChar** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：mulEquivHaarChar (φ : G ≃ₜ* G) : Real>=0
参数：φ : G ≃ₜ* G。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def mulEquivHaarChar (φ : G ≃ₜ* G) : ℝ≥0 :=
  haarScalarFactor haar (haar.map φ)

@[to_additive]
/-
**MeasureTheory.mulEquivHaarChar_pos** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：mulEquivHaarChar_pos (φ : G ≃ₜ* G) : 0 < mulEquivHaarChar φ
参数：φ : G ≃ₜ* G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_pos_of_isHaarMeasure`：haarScalarF
actor_pos_of_isHaarMeasure (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ
'] : 0 < haarScalarFactor μ' μ
-/
lemma mulEquivHaarChar_pos (φ : G ≃ₜ* G) : 0 < mulEquivHaarChar φ :=
  haarScalarFactor_pos_of_isHaarMeasure _ _

@[to_additive]
/-
**MeasureTheory.mulEquivHaarChar_eq** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：mulEquivHaarChar_eq (μ : Measure G) [IsHaarMeasure μ] [Regular μ] (φ : G ≃
ₜ* G) : mulEquivHaarChar φ = haarScalarFactor μ (μ.map φ)
参数：μ : Measure G；φ : G ≃ₜ* G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用引理 `MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_regular`：isMulLeftIn
variant_eq_smul_of_regular [LocallyCompactSpace G] (μ' μ : Measure G) [IsHaarMea
sure μ] [IsMulLeftInvariant μ'] [Regular μ] [Regu…
· 使用定理 `ContinuousMulEquiv.isHaarMeasure_map`：∀ {G : Type u_1} [inst : Measurabl
eSpace G] [inst_1 : Group G] [inst_2 : TopologicalSpace G]   (μ : MeasureTheory.
Measure G) [μ.IsHaarMeasur…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_smul`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [inst : SMul R ENNReal]
   [inst_1 : IsScala…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.haarScalarFactor.congr_simp`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : Group G] [inst_2 : IsTopologicalGroup G]   [in
st_3 : MeasurableSpace G] [inst_4 : Bor…
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_smul_smul`：haarScalarFactor_smul_
smul [LocallyCompactSpace G] (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasu
reOnCompacts μ'] [IsMulLeftInvariant μ…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_pos_of_isHaarMeasure`：haarScalarF
actor_pos_of_isHaarMeasure (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ
'] : 0 < haarScalarFactor μ' μ
-/
lemma mulEquivHaarChar_eq (μ : Measure G) [IsHaarMeasure μ]
    [Regular μ] (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ = haarScalarFactor μ (μ.map φ) := by
  have smul := isMulLeftInvariant_eq_smul_of_regular haar μ
  unfold mulEquivHaarChar
  conv =>
    enter [1, 1]
    rw [smul]
  conv =>
    enter [1, 2, 2]
    rw [smul]
  simp_rw [MeasureTheory.Measure.map_smul]
  exact haarScalarFactor_smul_smul _ _ (haarScalarFactor_pos_of_isHaarMeasure haar μ).ne'

@[to_additive addEquivAddHaarChar_smul_map]
/-
**MeasureTheory.mulEquivHaarChar_smul_map** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：mulEquivHaarChar_smul_map (μ : Measure G) [IsHaarMeasure μ] [Regular μ] (φ
 : G ≃ₜ* G) : mulEquivHaarChar φ • μ.map φ = μ
参数：μ : Measure G；φ : G ≃ₜ* G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `ContinuousMulEquiv.isHaarMeasure_map`：∀ {G : Type u_1} [inst : Measurabl
eSpace G] [inst_1 : Group G] [inst_2 : TopologicalSpace G]   (μ : MeasureTheory.
Measure G) [μ.IsHaarMeasur…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.mulEquivHaarChar_eq`：mulEquivHaarChar_eq (μ : Measure G) [
IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) : mulEquivHaarChar φ = haarScalarFact
or μ (μ.map φ)
· 使用定理 `MeasureTheory.Measure.Regular.map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α
]   [BorelSpace α] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用引理 `MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_regular`：isMulLeftIn
variant_eq_smul_of_regular [LocallyCompactSpace G] (μ' μ : Measure G) [IsHaarMea
sure μ] [IsMulLeftInvariant μ'] [Regular μ] [Regu…
-/
lemma mulEquivHaarChar_smul_map (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ • μ.map φ = μ := by
  rw [mulEquivHaarChar_eq μ φ]
  have : Regular (map φ μ) := Regular.map φ.toHomeomorph
  exact (isMulLeftInvariant_eq_smul_of_regular μ (map φ μ)).symm

@[to_additive addEquivAddHaarChar_smul_eq_comap]
/-
**MeasureTheory.mulEquivHaarChar_smul_eq_comap** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：mulEquivHaarChar_smul_eq_comap (μ : Measure G) [IsHaarMeasure μ] [Regular 
μ] (φ : G ≃ₜ* G) : (mulEquivHaarChar φ) • μ = μ.comap φ
参数：μ : Measure G；φ : G ≃ₜ* G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasurableEquiv.map_symm`：map_symm {μ : Measure α} (e : β ≃ᵐ α) : μ.map 
e.symm = μ.comap e
· 使用定理 `MeasureTheory.Measure.Regular.map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α
]   [BorelSpace α] [ins…
· 使用引理 `MeasureTheory.mulEquivHaarChar_smul_map`：mulEquivHaarChar_smul_map (μ : 
Measure G) [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) : mulEquivHaarChar φ • μ.
map φ = μ
· 使用定理 `ContinuousMulEquiv.isHaarMeasure_map`：∀ {G : Type u_1} [inst : Measurabl
eSpace G] [inst_1 : Group G] [inst_2 : TopologicalSpace G]   (μ : MeasureTheory.
Measure G) [μ.IsHaarMeasur…
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `HomeomorphClass.instContinuousMapClass`：∀ {F : Type u_5} {α : Type u_6} 
{β : Type u_7} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst
_2 : EquivLike F α β] [Homeo…
· 使用定理 `ContinuousMulEquiv.instHomeomorphClass`：∀ {M : Type u_1} {N : Type u_2} 
[inst : TopologicalSpace M] [inst_1 : TopologicalSpace N] [inst_2 : Mul M]   [in
st_3 : Mul N], HomeomorphCla…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousMulEquiv.self_comp_symm`：self_comp_symm (e : M ≃ₜ* N) : e ∘ e.
symm = id
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulEquivHaarChar_smul_eq_comap (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) :
    (mulEquivHaarChar φ) • μ = μ.comap φ := by
  let e := φ.toHomeomorph.toMeasurableEquiv
  rw [show ⇑φ = ⇑e from rfl, ← e.map_symm, show ⇑e.symm = ⇑φ.symm from rfl]
  have : (map (φ.symm) μ).Regular := Regular.map φ.symm.toHomeomorph
  rw [← mulEquivHaarChar_smul_map (map φ.symm μ) φ, map_map]
  · simp
  · fun_prop
  · fun_prop

@[to_additive addEquivAddHaarChar_smul_integral_map]
/-
**MeasureTheory.mulEquivHaarChar_smul_integral_map** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
形式化陈述：mulEquivHaarChar_smul_integral_map (μ : Measure G) [IsHaarMeasure μ] [Regu
lar μ] {f : G -> Real} (φ : G ≃ₜ* G) : mulEquivHaarChar φ • ∫ a, f a ∂(μ.map φ) 
= ∫ a, f a ∂μ
参数：μ : Measure G；φ : G ≃ₜ* G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.mulEquivHaarChar_smul_map`：mulEquivHaarChar_smul_map (μ : 
Measure G) [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) : mulEquivHaarChar φ • μ.
map φ = μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_smul_nnreal_measure`：integral_smul_nnreal_measure
 (f : α -> G) (c : Real>=0) : ∫ x, f x ∂(c • μ) = c • ∫ x, f x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulEquivHaarChar_smul_integral_map (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] {f : G → ℝ} (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ • ∫ a, f a ∂(μ.map φ) = ∫ a, f a ∂μ := by
  nth_rw 2 [← mulEquivHaarChar_smul_map μ φ]
  simp

@[to_additive integral_comap_eq_addEquivAddHaarChar_smul]
/-
**MeasureTheory.integral_comap_eq_mulEquivHaarChar_smul** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：integral_comap_eq_mulEquivHaarChar_smul (μ : Measure G) [IsHaarMeasure μ] 
[Regular μ] {f : G -> Real} (φ : G ≃ₜ* G) : ∫ a, f a ∂(μ.comap φ) = mulEquivHaar
Char φ • ∫ a, f a ∂μ
参数：μ : Measure G；φ : G ≃ₜ* G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMulEquiv.isHaarMeasure_map`：∀ {G : Type u_1} [inst : Measurabl
eSpace G] [inst_1 : Group G] [inst_2 : TopologicalSpace G]   (μ : MeasureTheory.
Measure G) [μ.IsHaarMeasur…
· 使用定理 `MeasureTheory.Measure.Regular.map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α
]   [BorelSpace α] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasurableEquiv.map_symm`：map_symm {μ : Measure α} (e : β ≃ᵐ α) : μ.map 
e.symm = μ.comap e
· 使用引理 `MeasureTheory.mulEquivHaarChar_smul_integral_map`：mulEquivHaarChar_smul_
integral_map (μ : Measure G) [IsHaarMeasure μ] [Regular μ] {f : G -> Real} (φ : 
G ≃ₜ* G) : mulEquivHaarChar φ • ∫ a, f…
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulEquivClass.apply_coe_symm_apply`：∀ {α : Type u_9} {β : Type u_10} [in
st : Mul α] [inst_1 : Mul β] {F : Type u_11} [inst_2 : EquivLike F α β]   [inst_
3 : MulEquivClass F α β]…
· 使用定理 `ContinuousMulEquiv.instMulEquivClass`：∀ {M : Type u_1} {N : Type u_2} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace N] [inst_2 : Mul M]   [inst
_3 : Mul N], MulEquivClass…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
-/
lemma integral_comap_eq_mulEquivHaarChar_smul (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] {f : G → ℝ} (φ : G ≃ₜ* G) :
    ∫ a, f a ∂(μ.comap φ) = mulEquivHaarChar φ • ∫ a, f a ∂μ := by
  let e := φ.toHomeomorph.toMeasurableEquiv
  change ∫ a, f a ∂(comap e μ) = mulEquivHaarChar φ • ∫ a, f a ∂μ
  have : (map (e.symm) μ).IsHaarMeasure := φ.symm.isHaarMeasure_map μ
  have : (map (e.symm) μ).Regular := Regular.map φ.symm.toHomeomorph
  rw [← e.map_symm, ← mulEquivHaarChar_smul_integral_map (map e.symm μ) φ,
    map_map (by exact φ.toHomeomorph.toMeasurableEquiv.measurable) e.symm.measurable]
  -- congr -- breaks to_additive
  rw [show ⇑φ ∘ ⇑e.symm = id by ext; simp [e]]
  simp

@[to_additive addEquivAddHaarChar_smul_preimage]
/-
**MeasureTheory.mulEquivHaarChar_smul_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：mulEquivHaarChar_smul_preimage (μ : Measure G) [IsHaarMeasure μ] [Regular 
μ] {X : Set G} (φ : G ≃ₜ* G) : mulEquivHaarChar φ • μ (φ ⁻¹' X) = μ X
参数：μ : Measure G；φ : G ≃ₜ* G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.mulEquivHaarChar_smul_map`：mulEquivHaarChar_smul_map (μ : 
Measure G) [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) : mulEquivHaarChar φ • μ.
map φ = μ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
-/
lemma mulEquivHaarChar_smul_preimage
    (μ : Measure G) [IsHaarMeasure μ] [Regular μ] {X : Set G} (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ • μ (φ ⁻¹' X) = μ X := by
  nth_rw 2 [← mulEquivHaarChar_smul_map μ φ]
  simp only [Measure.smul_apply, nnreal_smul_coe_apply]
  exact congr_arg _ <| (MeasurableEquiv.map_apply φ.toMeasurableEquiv X).symm

@[to_additive (attr := simp)]
/-
**MeasureTheory.mulEquivHaarChar_refl** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：mulEquivHaarChar_refl : mulEquivHaarChar (ContinuousMulEquiv.refl G) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_id'`：map_id' : map (fun x => x) μ = μ
· 使用定理 `MeasureTheory.Measure.haarScalarFactor.congr_simp`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : Group G] [inst_2 : IsTopologicalGroup G]   [in
st_3 : MeasurableSpace G] [inst_4 : Bor…
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_self`：haarScalarFactor_self (μ : 
Measure G) [IsHaarMeasure μ] : haarScalarFactor μ μ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulEquivHaarChar_refl :
    mulEquivHaarChar (ContinuousMulEquiv.refl G) = 1 := by
  simp [mulEquivHaarChar, Function.id_def]

@[to_additive]
/-
**MeasureTheory.mulEquivHaarChar_trans** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：mulEquivHaarChar_trans {φ ψ : G ≃ₜ* G} : mulEquivHaarChar (ψ.trans φ) = mu
lEquivHaarChar ψ * mulEquivHaarChar φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMulEquiv.isHaarMeasure_map`：∀ {G : Type u_1} [inst : Measurabl
eSpace G] [inst_1 : Group G] [inst_2 : TopologicalSpace G]   (μ : MeasureTheory.
Measure G) [μ.IsHaarMeasur…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.mulEquivHaarChar_eq`：mulEquivHaarChar_eq (μ : Measure G) [
IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) : mulEquivHaarChar φ = haarScalarFact
or μ (μ.map φ)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `HomeomorphClass.instContinuousMapClass`：∀ {F : Type u_5} {α : Type u_6} 
{β : Type u_7} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst
_2 : EquivLike F α β] [Homeo…
· 使用定理 `ContinuousMulEquiv.instHomeomorphClass`：∀ {M : Type u_1} {N : Type u_2} 
[inst : TopologicalSpace M] [inst_1 : TopologicalSpace N] [inst_2 : Mul M]   [in
st_3 : Mul N], HomeomorphCla…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.haarScalarFactor.congr_simp`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : Group G] [inst_2 : IsTopologicalGroup G]   [in
st_3 : MeasurableSpace G] [inst_4 : Bor…
· 使用定理 `MeasureTheory.Measure.Regular.map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α
]   [BorelSpace α] [ins…
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_eq_mul`：haarScalarFactor_eq_mul (
μ' μ ν : Measure G) [IsHaarMeasure μ] [IsHaarMeasure ν] [IsFiniteMeasureOnCompac
ts μ'] [IsMulLeftInvariant μ'] : ha…
-/
lemma mulEquivHaarChar_trans {φ ψ : G ≃ₜ* G} :
    mulEquivHaarChar (ψ.trans φ) = mulEquivHaarChar ψ * mulEquivHaarChar φ := by
  rw [mulEquivHaarChar_eq haar ψ, mulEquivHaarChar_eq haar (ψ.trans φ)]
  have hφ : Measurable φ := by fun_prop
  have hψ : Measurable ψ := by fun_prop
  simp_rw [ContinuousMulEquiv.coe_trans, ← map_map hφ hψ]
  have h_reg : (haar.map ψ).Regular := Regular.map ψ.toHomeomorph
  rw [MeasureTheory.Measure.haarScalarFactor_eq_mul haar (haar.map ψ),
    ← mulEquivHaarChar_eq (haar.map ψ)]

@[to_additive]
/-
**MeasureTheory.mulEquivHaarChar_symm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：mulEquivHaarChar_symm {φ : G ≃ₜ* G} : mulEquivHaarChar φ.symm = (mulEquivH
aarChar φ)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.mulEquivHaarChar.congr_simp`：∀ {G : Type u_1} [inst : Grou
p G] [inst_1 : TopologicalSpace G] [inst_2 : MeasurableSpace G] [inst_3 : BorelS
pace G]   [inst_4 : IsTopologic…
· 使用定理 `ContinuousMulEquiv.self_trans_symm`：self_trans_symm (e : M ≃ₜ* N) : e.tr
ans e.symm = refl M
· 使用引理 `MeasureTheory.mulEquivHaarChar_refl`：mulEquivHaarChar_refl : mulEquivHaa
rChar (ContinuousMulEquiv.refl G) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulEquivHaarChar_symm {φ : G ≃ₜ* G} :
    mulEquivHaarChar φ.symm = (mulEquivHaarChar φ)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  simp [← mulEquivHaarChar_trans]

open TopologicalSpace Set in
@[to_additive addEquivAddHaarChar_eq_one_of_compactSpace]
/-
**MeasureTheory.mulEquivHaarChar_eq_one_of_compactSpace** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：mulEquivHaarChar_eq_one_of_compactSpace [CompactSpace G] (φ : G ≃ₜ* G) : m
ulEquivHaarChar φ = 1
参数：φ : G ≃ₜ* G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `MeasureTheory.Measure.haarMeasure_self`：haarMeasure_self {K₀ : PositiveC
ompacts G} : haarMeasure K₀ K₀ = 1
· 使用定理 `ContinuousMulEquiv.isHaarMeasure_map`：∀ {G : Type u_1} [inst : Measurabl
eSpace G] [inst_1 : Group G] [inst_2 : TopologicalSpace G]   (μ : MeasureTheory.
Measure G) [μ.IsHaarMeasur…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用引理 `MeasureTheory.mulEquivHaarChar_eq`：mulEquivHaarChar_eq (μ : Measure G) [
IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) : mulEquivHaarChar φ = haarScalarFact
or μ (μ.map φ)
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `HomeomorphClass.instContinuousMapClass`：∀ {F : Type u_5} {α : Type u_6} 
{β : Type u_7} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst
_2 : EquivLike F α β] [Homeo…
· 使用定理 `ContinuousMulEquiv.instHomeomorphClass`：∀ {M : Type u_1} {N : Type u_2} 
[inst : TopologicalSpace M] [inst_1 : TopologicalSpace N] [inst_2 : Mul M]   [in
st_3 : Mul N], HomeomorphCla…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.isMulInvariant_eq_smul_of_compactSpace`：isMulInvar
iant_eq_smul_of_compactSpace [CompactSpace G] (μ' μ : Measure G) [IsHaarMeasure 
μ] [IsMulLeftInvariant μ'] [IsFiniteMeasureOnCompa…
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
lemma mulEquivHaarChar_eq_one_of_compactSpace [CompactSpace G] (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ = 1 := by
  set μ := haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts G)
  have hμ : μ univ = 1 := haarMeasure_self
  rw [mulEquivHaarChar_eq μ]
  suffices (μ.haarScalarFactor (map φ μ) : ℝ≥0∞) = 1 by exact_mod_cast this
  calc
    _ = μ.haarScalarFactor (map φ μ) • (1 : ℝ≥0∞) := by rw [ENNReal.smul_def, smul_eq_mul, mul_one]
    _ = μ.haarScalarFactor (map φ μ) • (map φ μ univ) := by
          rw [map_apply (map_continuous φ).measurable .univ, Set.preimage_univ, hμ]
    _ = μ univ := by
          conv_rhs => rw [isMulInvariant_eq_smul_of_compactSpace μ (map φ μ), Measure.smul_apply]
    _ = 1 := hμ

end MeasureTheory

