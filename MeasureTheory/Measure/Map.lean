/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Pushforward of a measure

In this file we define the pushforward `MeasureTheory.Measure.map f μ`
of a measure `μ` along an almost everywhere measurable map `f`.
If `f` is not a.e. measurable, then we define `map f μ` to be zero.

## Main definitions

* `MeasureTheory.Measure.map f μ`: map of the measure `μ` along the map `f`.

## Main statements

* `map_apply`: for `s` a measurable set, `μ.map f s = μ (f ⁻¹' s)`
* `map_map`: `(μ.map f).map g = μ.map (g ∘ f)`

-/

@[expose] public section

variable {α β γ : Type*}

open Set Function ENNReal NNReal
open Filter hiding map

namespace MeasureTheory

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {s : Set α}

namespace Measure

/-- Lift a linear map between `OuterMeasure` spaces such that for each measure `μ` every measurable
set is Carathéodory-measurable w.r.t. `f μ` to a linear map between `Measure` spaces. -/
noncomputable
/-
**MeasureTheory.Measure.liftLinear** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：liftLinear [MeasurableSpace β] (f : OuterMeasure α ->ₗ[Real>=0∞] OuterMeas
ure β) (hf : forall μ : Measure α, ‹_› <= (f μ.toOuterMeasure).caratheodory) : M
easure α ->ₗ[Real>=0∞] Measure β where toFun μ
参数：f : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure β；hf : forall μ : Measure α, ‹_
› <= (f μ.toOuterMeasure).caratheodory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def liftLinear [MeasurableSpace β] (f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β)
    (hf : ∀ μ : Measure α, ‹_› ≤ (f μ.toOuterMeasure).caratheodory) :
    Measure α →ₗ[ℝ≥0∞] Measure β where
  toFun μ := (f μ.toOuterMeasure).toMeasure (hf μ)
  map_add' μ₁ μ₂ := ext fun s hs => by
    simp only [map_add, coe_add, Pi.add_apply, toMeasure_apply, add_toOuterMeasure,
      FunLike.coe_add, hs]
  map_smul' c μ := ext fun s hs => by
    simp only [map_smulₛₗ, Pi.smul_apply, toMeasure_apply, smul_toOuterMeasure (R := ℝ≥0∞),
      FunLike.coe_smul, smul_apply, hs]
/-
**MeasureTheory.Measure.liftLinear_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：liftLinear_apply {f : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure β} (hf) {s
 : Set β} (hs : MeasurableSet s) : liftLinear f hf μ s = f μ.toOuterMeasure s
参数：hf；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.toMeasure_apply`：toMeasure_apply (m : OuterMeasure α) (h :
 ms <= m.caratheodory) {s : Set α} (hs : MeasurableSet s) : m.toMeasure h s = m 
s
-/
lemma liftLinear_apply₀ {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) {s : Set β}
    (hs : NullMeasurableSet s (liftLinear f hf μ)) : liftLinear f hf μ s = f μ.toOuterMeasure s :=
  toMeasure_apply₀ _ (hf μ) hs

@[simp]
/-
**MeasureTheory.Measure.liftLinear_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：liftLinear_apply {f : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure β} (hf) {s
 : Set β} (hs : MeasurableSet s) : liftLinear f hf μ s = f μ.toOuterMeasure s
参数：hf；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.toMeasure_apply`：toMeasure_apply (m : OuterMeasure α) (h :
 ms <= m.caratheodory) {s : Set α} (hs : MeasurableSet s) : m.toMeasure h s = m 
s
-/
theorem liftLinear_apply {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) {s : Set β}
    (hs : MeasurableSet s) : liftLinear f hf μ s = f μ.toOuterMeasure s :=
  toMeasure_apply _ (hf μ) hs
/-
**MeasureTheory.Measure.le_liftLinear_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：le_liftLinear_apply {f : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure β} (hf)
 (s : Set β) : f μ.toOuterMeasure s <= liftLinear f hf μ s
参数：hf；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.le_toMeasure_apply`：le_toMeasure_apply (m : OuterMeasure α
) (h : ms <= m.caratheodory) (s : Set α) : m s <= m.toMeasure h s
-/
theorem le_liftLinear_apply {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) (s : Set β) :
    f μ.toOuterMeasure s ≤ liftLinear f hf μ s :=
  le_toMeasure_apply _ (hf μ) s

open scoped Classical in
/-- The pushforward of a measure as a linear map. It is defined to be `0` if `f` is not
a measurable function. -/
noncomputable
/-
**MeasureTheory.Measure.map** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：{α : Type u_4} →   {β : Type u_5} →     [inst : MeasurableSpace α] →      
 [inst_1 : MeasurableSpace β] → (α → β) → MeasureTheory.Measure α → MeasureTheor
y.Measure β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapₗ [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Measure α →ₗ[ℝ≥0∞] Measure β :=
  if hf : Measurable f then
    liftLinear (OuterMeasure.map f) fun μ _s hs t =>
      le_toOuterMeasure_caratheodory μ _ (hf hs) (f ⁻¹' t)
  else 0

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.Measure.map** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：{α : Type u_4} →   {β : Type u_5} →     [inst : MeasurableSpace α] →      
 [inst_1 : MeasurableSpace β] → (α → β) → MeasureTheory.Measure α → MeasureTheor
y.Measure β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapₗ_congr {f g : α → β} (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    mapₗ f μ = mapₗ g μ := by
  ext1 s hs
  simpa only [mapₗ, hf, hg, hs, dif_pos, liftLinear_apply, OuterMeasure.map_apply]
    using! measure_congr (h.preimage s)

open scoped Classical in
/-- The pushforward of a measure. It is defined to be `0` if `f` is not an almost everywhere
measurable function. -/
noncomputable
irreducible_def map [MeasurableSpace α] [MeasurableSpace β] (f : α → β) (μ : Measure α) :
    Measure β :=
  if hf : AEMeasurable f μ then mapₗ (hf.mk f) μ else 0

/-
**MeasureTheory.Measure.map** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：{α : Type u_4} →   {β : Type u_5} →     [inst : MeasurableSpace α] →      
 [inst_1 : MeasurableSpace β] → (α → β) → MeasureTheory.Measure α → MeasureTheor
y.Measure β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapₗ_mk_apply_of_aemeasurable {f : α → β} (hf : AEMeasurable f μ) :
    mapₗ (hf.mk f) μ = map f μ := by simp [map, hf]
/-
**MeasureTheory.Measure.map** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：{α : Type u_4} →   {β : Type u_5} →     [inst : MeasurableSpace α] →      
 [inst_1 : MeasurableSpace β] → (α → β) → MeasureTheory.Measure α → MeasureTheor
y.Measure β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapₗ_apply_of_measurable {f : α → β} (hf : Measurable f) (μ : Measure α) :
    mapₗ f μ = map f μ := by
  simp only [← mapₗ_mk_apply_of_aemeasurable hf.aemeasurable]
  exact mapₗ_congr hf hf.aemeasurable.measurable_mk hf.aemeasurable.ae_eq_mk

@[simp]
/-
**MeasureTheory.Measure.map_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (μ ν : MeasureTheory.Measure α)   {f : α → β},   Measurable f → MeasureT
heory.Measure.map f (μ + ν) = MeasureTheory.Measure.map f μ + MeasureTheory.Meas
ure.map f ν
参数：μ ν : MeasureTheory.Measure α；μ + ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.mapₗ_apply_of_measurable`：mapₗ_apply_of_measurable
 {f : α -> β} (hf : Measurable f) (μ : Measure α) : mapₗ f μ = map f μ
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_add (μ ν : Measure α) {f : α → β} (hf : Measurable f) :
    (μ + ν).map f = μ.map f + ν.map f := by simp [← mapₗ_apply_of_measurable hf]

@[simp]
/-
**MeasureTheory.Measure.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (f : α → β),   MeasureTheory.Measure.map f 0 = 0
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_def`：∀ {α : Type u_4} {β : Type u_5} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] (f : α → β)   (μ : MeasureTheory.
Measure α),   Measu…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
protected theorem map_zero (f : α → β) : (0 : Measure α).map f = 0 := by
  by_cases hf : AEMeasurable f (0 : Measure α) <;> simp [map, hf]

@[simp]
/-
**MeasureTheory.Measure.map_of_not_aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：map_of_not_aemeasurable {f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f
 μ) : μ.map f = 0
参数：hf : ¬AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_def`：∀ {α : Type u_4} {β : Type u_5} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] (f : α → β)   (μ : MeasureTheory.
Measure α),   Measu…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_of_not_aemeasurable {f : α → β} {μ : Measure α} (hf : ¬AEMeasurable f μ) :
    μ.map f = 0 := by simp [map, hf]
/-
**MeasureTheory.Measure._root_.AEMeasurable.of_map_ne_zero** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AEMeasurable.of_map_ne_zero {f : α → β} {μ : Measure α} (hf : μ.map f ≠ 0) :
    AEMeasurable f μ := not_imp_comm.1 map_of_not_aemeasurable hf
/-
**MeasureTheory.Measure.map_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：map_congr {f g : α -> β} (h : f =ᵐ[μ] g) : Measure.map f μ = Measure.map g
 μ
参数：h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.congr`：congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMe
asurable g μ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.mapₗ_mk_apply_of_aemeasurable`：mapₗ_mk_apply_of_ae
measurable {f : α -> β} (hf : AEMeasurable f μ) : mapₗ (hf.mk f) μ = map f μ
· 使用定理 `MeasureTheory.Measure.mapₗ_congr`：mapₗ_congr {f g : α -> β} (hf : Measur
able f) (hg : Measurable g) (h : f =ᵐ[μ] g) : mapₗ f μ = mapₗ g μ
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `aemeasurable_congr`：aemeasurable_congr (h : f =ᵐ[μ] g) : AEMeasurable f 
μ ↔ AEMeasurable g μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_congr {f g : α → β} (h : f =ᵐ[μ] g) : Measure.map f μ = Measure.map g μ := by
  by_cases hf : AEMeasurable f μ
  · have hg : AEMeasurable g μ := hf.congr h
    simp only [← mapₗ_mk_apply_of_aemeasurable hf, ← mapₗ_mk_apply_of_aemeasurable hg]
    exact
      mapₗ_congr hf.measurable_mk hg.measurable_mk (hf.ae_eq_mk.symm.trans (h.trans hg.ae_eq_mk))
  · have hg : ¬AEMeasurable g μ := by simpa [← aemeasurable_congr h] using hf
    simp [map_of_not_aemeasurable, hf, hg]

@[simp]
/-
**MeasureTheory.Measure.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {R : Type u_4} [inst : SMul R ENNReal]   [inst_1 : IsScalarTower R ENNRe
al ENNReal] (c : R) (μ : MeasureTheory.Measure α) (f : α → β),   MeasureTheory.M
easure.map f (c • μ) = c • MeasureTheory.Measure.map f μ
参数：c : R；μ : MeasureTheory.Measure α；f : α → β；c • μ。
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
· 使用定理 `MeasureTheory.Measure.map_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure.m
ap f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.Measure.ae_ennreal_smul_measure_iff`：ae_ennreal_smul_measu
re_iff {c : Real>=0∞} {p : α -> Prop} (hc : c != 0) {μ : Measure α} : (forallᵐ x
 ∂c • μ, p x) ↔ forallᵐ x ∂μ, p x
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `MeasureTheory.Measure.mapₗ_mk_apply_of_aemeasurable`：mapₗ_mk_apply_of_ae
measurable {f : α -> β} (hf : AEMeasurable f μ) : mapₗ (hf.mk f) μ = map f μ
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `MeasureTheory.Measure.mapₗ_congr`：mapₗ_congr {f g : α -> β} (hf : Measur
able f) (hg : Measurable g) (h : f =ᵐ[μ] g) : mapₗ f μ = mapₗ g μ
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
protected theorem map_smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (c : R) (μ : Measure α) (f : α → β) : (c • μ).map f = c • μ.map f := by
  suffices ∀ c : ℝ≥0∞, (c • μ).map f = c • μ.map f by simpa using this (c • 1)
  clear c; intro c
  rcases eq_or_ne c 0 with (rfl | hc); · simp
  by_cases hf : AEMeasurable f μ
  · have hfc : AEMeasurable f (c • μ) :=
      ⟨hf.mk f, hf.measurable_mk, (ae_ennreal_smul_measure_iff hc).2 hf.ae_eq_mk⟩
    simp only [← mapₗ_mk_apply_of_aemeasurable hf, ← mapₗ_mk_apply_of_aemeasurable hfc, map_smulₛₗ,
      RingHom.id_apply]
    congr 1
    apply mapₗ_congr hfc.measurable_mk hf.measurable_mk
    exact .trans ((ae_ennreal_smul_measure_iff hc).1 hfc.ae_eq_mk.symm) hf.ae_eq_mk
  · have hfc : ¬AEMeasurable f (c • μ) := by
      intro hfc
      exact hf ⟨hfc.mk f, hfc.measurable_mk, (ae_ennreal_smul_measure_iff hc).1 hfc.ae_eq_mk⟩
    simp [map_of_not_aemeasurable hf, map_of_not_aemeasurable hfc]

variable {f : α → β}
/-
**MeasureTheory.Measure.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：map_apply (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) : μ.map f
 s = μ (f ⁻¹' s)
参数：hf : Measurable f；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
lemma map_apply₀ {f : α → β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : NullMeasurableSet s (map f μ)) : μ.map f s = μ (f ⁻¹' s) := by
  rw [map, dif_pos hf, mapₗ, dif_pos hf.measurable_mk] at hs ⊢
  rw [liftLinear_apply₀ _ hs, measure_congr (hf.ae_eq_mk.preimage s)]
  rfl

/-- We can evaluate the pushforward on measurable sets. For non-measurable sets, see
  `MeasureTheory.Measure.le_map_apply` and `MeasurableEquiv.map_apply`. -/
@[simp]
/-
**MeasureTheory.Measure.map_apply_of_aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：map_apply_of_aemeasurable (hf : AEMeasurable f μ) {s : Set β} (hs : Measur
ableSet s) : μ.map f s = μ (f ⁻¹' s)
参数：hf : AEMeasurable f μ；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.map_apply₀`：map_apply₀ {f : α -> β} (hf : AEMeasur
able f μ) {s : Set β} (hs : NullMeasurableSet s (map f μ)) : μ.map f s = μ (f ⁻¹
' s)
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ

--- 原说明 ---
We can evaluate the pushforward on measurable sets. For non-measurable sets, see
  `MeasureTheory.Measure.le_map_apply` and `MeasurableEquiv.map_apply`.
-/
theorem map_apply_of_aemeasurable (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :
    μ.map f s = μ (f ⁻¹' s) := map_apply₀ hf hs.nullMeasurableSet

@[simp]
/-
**MeasureTheory.Measure.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：map_apply (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) : μ.map f
 s = μ (f ⁻¹' s)
参数：hf : Measurable f；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem map_apply (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    μ.map f s = μ (f ⁻¹' s) :=
  map_apply_of_aemeasurable hf.aemeasurable hs
/-
**MeasureTheory.Measure.map_toOuterMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：map_toOuterMeasure (hf : AEMeasurable f μ) : (μ.map f).toOuterMeasure = (O
uterMeasure.map f μ.toOuterMeasure).trim
参数：hf : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.trimmed`：trimmed (μ : Measure α) : μ.toOuterMeasur
e.trim = μ.toOuterMeasure
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq_trim_iff`：trim_eq_trim_iff {m₁ m₂ : O
uterMeasure α} : m₁.trim = m₂.trim ↔ forall s, MeasurableSet s -> m₁ s = m₂ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_toOuterMeasure (hf : AEMeasurable f μ) :
    (μ.map f).toOuterMeasure = (OuterMeasure.map f μ.toOuterMeasure).trim := by
  rw [← trimmed, OuterMeasure.trim_eq_trim_iff]
  intro s hs
  simp [hf, hs]
/-
**MeasureTheory.Measure.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μ : MeasureTheory.Measure α}   {f : α → β}, AEMeasurable f μ → (Measure
Theory.Measure.map f μ = 0 ↔ μ = 0)
参数：MeasureTheory.Measure.map f μ = 0 ↔ μ = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma map_eq_zero_iff (hf : AEMeasurable f μ) : μ.map f = 0 ↔ μ = 0 := by
  simp_rw [← measure_univ_eq_zero, map_apply_of_aemeasurable hf .univ, preimage_univ]
/-
**MeasureTheory.Measure.map** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：{α : Type u_4} →   {β : Type u_5} →     [inst : MeasurableSpace α] →      
 [inst_1 : MeasurableSpace β] → (α → β) → MeasureTheory.Measure α → MeasureTheor
y.Measure β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mapₗ_eq_zero_iff (hf : Measurable f) : Measure.mapₗ f μ = 0 ↔ μ = 0 := by
  rw [mapₗ_apply_of_measurable hf, map_eq_zero_iff hf.aemeasurable]

/-- If `map f μ = μ`, then the measure of the preimage of any null measurable set `s`
is equal to the measure of `s`.
Note that this lemma does not assume (a.e.) measurability of `f`. -/
/-
**MeasureTheory.Measure.measure_preimage_of_map_eq_self** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.Measure`。
形式化陈述：measure_preimage_of_map_eq_self {f : α -> α} (hf : map f μ = μ) {s : Set α
} (hs : NullMeasurableSet s μ) : μ (f ⁻¹' s) = μ s
参数：hf : map f μ = μ；hs : NullMeasurableSet s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.map_apply₀`：map_apply₀ {f : α -> β} (hf : AEMeasur
able f μ) {s : Set β} (hs : NullMeasurableSet s (map f μ)) : μ.map f s = μ (f ⁻¹
' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `map f μ = μ`, then the measure of the preimage of any null measurable set `s
`
is equal to the measure of `s`.
Note that this lemma does not assume (a.e.) measurability of `f`.
-/
lemma measure_preimage_of_map_eq_self {f : α → α} (hf : map f μ = μ)
    {s : Set α} (hs : NullMeasurableSet s μ) : μ (f ⁻¹' s) = μ s := by
  if hfm : AEMeasurable f μ then
    rw [← map_apply₀ hfm, hf]
    rwa [hf]
  else
    rw [map_of_not_aemeasurable hfm] at hf
    simp [← hf]
/-
**MeasureTheory.Measure.map_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：map_ne_zero_iff (hf : AEMeasurable f μ) : μ.map f != 0 ↔ μ != 0
参数：hf : AEMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MeasureTheory.Measure.map_eq_zero_iff`：∀ {α : Type u_1} {β : Type u_2} {
mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Measure α}  
 {f : α → β}, AEMeasurable …
-/
lemma map_ne_zero_iff (hf : AEMeasurable f μ) : μ.map f ≠ 0 ↔ μ ≠ 0 := (map_eq_zero_iff hf).not
/-
**MeasureTheory.Measure.map** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：{α : Type u_4} →   {β : Type u_5} →     [inst : MeasurableSpace α] →      
 [inst_1 : MeasurableSpace β] → (α → β) → MeasureTheory.Measure α → MeasureTheor
y.Measure β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapₗ_ne_zero_iff (hf : Measurable f) : Measure.mapₗ f μ ≠ 0 ↔ μ ≠ 0 :=
  (mapₗ_eq_zero_iff hf).not

@[simp]
/-
**MeasureTheory.Measure.map_id** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`
。
形式化陈述：map_id : map id μ = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem map_id : map id μ = μ :=
  ext fun _ => map_apply measurable_id

@[simp]
/-
**MeasureTheory.Measure.map_id'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：map_id' : map (fun x => x) μ = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
-/
theorem map_id' : map (fun x => x) μ = μ :=
  map_id

/-- Mapping a measure twice is the same as mapping the measure with the composition. This version is
for measurable functions. See `map_map_of_aemeasurable` when they are just ae measurable. -/
/-
**MeasureTheory.Measure.map_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：map_map {g : β -> γ} {f : α -> β} (hg : Measurable g) (hf : Measurable f) 
: (μ.map f).map g = μ.map (g ∘ f)
参数：hg : Measurable g；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Mapping a measure twice is the same as mapping the measure with the composition.
 This version is
for measurable functions. See `map_map_of_aemeasurable` when they are just ae me
asurable.
-/
theorem map_map {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    (μ.map f).map g = μ.map (g ∘ f) :=
  ext fun s hs => by simp [hf, hg, hs, hg hs, hg.comp hf, ← preimage_comp]

@[gcongr, mono]
/-
**MeasureTheory.Measure.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：map_mono {f : α -> β} (h : μ <= ν) (hf : Measurable f) : μ.map f <= ν.map 
f
参数：h : μ <= ν；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem map_mono {f : α → β} (h : μ ≤ ν) (hf : Measurable f) : μ.map f ≤ ν.map f :=
  le_iff.2 fun s hs ↦ by simp [hf.aemeasurable, hs, h _]

/-- Even if `s` is not measurable, we can bound `map f μ s` from below.
  See also `MeasurableEquiv.map_apply`. -/
/-
**MeasureTheory.Measure.le_map_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：le_map_apply {f : α -> β} (hf : AEMeasurable f μ) (s : Set β) : μ (f ⁻¹' s
) <= μ.map f s
参数：hf : AEMeasurable f μ；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s

--- 原说明 ---
Even if `s` is not measurable, we can bound `map f μ s` from below.
  See also `MeasurableEquiv.map_apply`.
-/
theorem le_map_apply {f : α → β} (hf : AEMeasurable f μ) (s : Set β) : μ (f ⁻¹' s) ≤ μ.map f s :=
  calc
    μ (f ⁻¹' s) ≤ μ (f ⁻¹' toMeasurable (μ.map f) s) := by gcongr; apply subset_toMeasurable
    _ = μ.map f (toMeasurable (μ.map f) s) :=
      (map_apply_of_aemeasurable hf <| measurableSet_toMeasurable _ _).symm
    _ = μ.map f s := measure_toMeasurable _
/-
**MeasureTheory.Measure.le_map_apply_image** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：le_map_apply_image {f : α -> β} (hf : AEMeasurable f μ) (s : Set α) : μ s 
<= μ.map f (f '' s)
参数：hf : AEMeasurable f μ；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `MeasureTheory.Measure.le_map_apply`：le_map_apply {f : α -> β} (hf : AEMe
asurable f μ) (s : Set β) : μ (f ⁻¹' s) <= μ.map f s
-/
theorem le_map_apply_image {f : α → β} (hf : AEMeasurable f μ) (s : Set α) :
    μ s ≤ μ.map f (f '' s) :=
  (measure_mono (subset_preimage_image f s)).trans (le_map_apply hf _)

/-- Even if `s` is not measurable, `map f μ s = 0` implies that `μ (f ⁻¹' s) = 0`. -/
/-
**MeasureTheory.Measure.preimage_null_of_map_null** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：preimage_null_of_map_null {f : α -> β} (hf : AEMeasurable f μ) {s : Set β}
 (hs : μ.map f s = 0) : μ (f ⁻¹' s) = 0
参数：hf : AEMeasurable f μ；hs : μ.map f s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.Measure.le_map_apply`：le_map_apply {f : α -> β} (hf : AEMe
asurable f μ) (s : Set β) : μ (f ⁻¹' s) <= μ.map f s

--- 原说明 ---
Even if `s` is not measurable, `map f μ s = 0` implies that `μ (f ⁻¹' s) = 0`.
-/
theorem preimage_null_of_map_null {f : α → β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : μ.map f s = 0) : μ (f ⁻¹' s) = 0 :=
  nonpos_iff_eq_zero.mp <| (le_map_apply hf s).trans_eq hs
/-
**MeasureTheory.Measure.tendsto_ae_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：tendsto_ae_map {f : α -> β} (hf : AEMeasurable f μ) : Tendsto f (ae μ) (ae
 (μ.map f))
参数：hf : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.preimage_null_of_map_null`：preimage_null_of_map_nu
ll {f : α -> β} (hf : AEMeasurable f μ) {s : Set β} (hs : μ.map f s = 0) : μ (f 
⁻¹' s) = 0
-/
theorem tendsto_ae_map {f : α → β} (hf : AEMeasurable f μ) : Tendsto f (ae μ) (ae (μ.map f)) :=
  fun _ hs => preimage_null_of_map_null hf hs

end Measure

open Measure

/-
**MeasureTheory.mem_ae_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：mem_ae_map_iff {f : α -> β} (hf : AEMeasurable f μ) {s : Set β} (hs : Meas
urableSet s) : s in ae (μ.map f) ↔ f ⁻¹' s in ae μ
参数：hf : AEMeasurable f μ；hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_ae_map_iff {f : α → β} (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :
    s ∈ ae (μ.map f) ↔ f ⁻¹' s ∈ ae μ := by
  simp only [mem_ae_iff, map_apply_of_aemeasurable hf hs.compl, preimage_compl]
/-
**MeasureTheory.mem_ae_of_mem_ae_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：mem_ae_of_mem_ae_map {f : α -> β} (hf : AEMeasurable f μ) {s : Set β} (hs 
: s in ae (μ.map f)) : f ⁻¹' s in ae μ
参数：hf : AEMeasurable f μ；hs : s in ae (μ.map f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `MeasureTheory.Measure.tendsto_ae_map`：tendsto_ae_map {f : α -> β} (hf : 
AEMeasurable f μ) : Tendsto f (ae μ) (ae (μ.map f))
-/
theorem mem_ae_of_mem_ae_map {f : α → β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : s ∈ ae (μ.map f)) : f ⁻¹' s ∈ ae μ :=
  (tendsto_ae_map hf).eventually hs
/-
**MeasureTheory.ae_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_map_iff {f : α -> β} (hf : AEMeasurable f μ) {p : β -> Prop} (hp : Meas
urableSet { x | p x }) : (forallᵐ y ∂μ.map f, p y) ↔ forallᵐ x ∂μ, p (f x)
参数：hf : AEMeasurable f μ；hp : MeasurableSet { x | p x }。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.mem_ae_map_iff`：mem_ae_map_iff {f : α -> β} (hf : AEMeasur
able f μ) {s : Set β} (hs : MeasurableSet s) : s in ae (μ.map f) ↔ f ⁻¹' s in ae
 μ
-/
theorem ae_map_iff {f : α → β} (hf : AEMeasurable f μ) {p : β → Prop}
    (hp : MeasurableSet { x | p x }) : (∀ᵐ y ∂μ.map f, p y) ↔ ∀ᵐ x ∂μ, p (f x) :=
  mem_ae_map_iff hf hp
/-
**MeasureTheory.ae_of_ae_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_of_ae_map {f : α -> β} (hf : AEMeasurable f μ) {p : β -> Prop} (h : for
allᵐ y ∂μ.map f, p y) : forallᵐ x ∂μ, p (f x)
参数：hf : AEMeasurable f μ；h : forallᵐ y ∂μ.map f, p y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.mem_ae_of_mem_ae_map`：mem_ae_of_mem_ae_map {f : α -> β} (h
f : AEMeasurable f μ) {s : Set β} (hs : s in ae (μ.map f)) : f ⁻¹' s in ae μ
-/
theorem ae_of_ae_map {f : α → β} (hf : AEMeasurable f μ) {p : β → Prop} (h : ∀ᵐ y ∂μ.map f, p y) :
    ∀ᵐ x ∂μ, p (f x) :=
  mem_ae_of_mem_ae_map hf h
/-
**MeasureTheory.ae_map_mem_range** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_map_mem_range {m0 : MeasurableSpace α} (f : α -> β) (hf : MeasurableSet
 (range f)) (μ : Measure α) : forallᵐ x ∂μ.map f, x in range f
参数：f : α -> β；hf : MeasurableSet (range f)；μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.mem_ae_map_iff`：mem_ae_map_iff {f : α -> β} (hf : AEMeasur
able f μ) {s : Set β} (hs : MeasurableSet s) : s in ae (μ.map f) ↔ f ⁻¹' s in ae
 μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
-/
theorem ae_map_mem_range {m0 : MeasurableSpace α} (f : α → β) (hf : MeasurableSet (range f))
    (μ : Measure α) : ∀ᵐ x ∂μ.map f, x ∈ range f := by
  by_cases h : AEMeasurable f μ
  · change range f ∈ ae (μ.map f)
    rw [mem_ae_map_iff h hf]
    filter_upwards using mem_range_self
  · simp [map_of_not_aemeasurable h]

end MeasureTheory

namespace MeasurableEmbedding

open MeasureTheory Measure

variable {m0 : MeasurableSpace α} {m1 : MeasurableSpace β} {f : α → β} {μ ν : Measure α}

nonrec theorem map_apply (hf : MeasurableEmbedding f) (μ : Measure α) (s : Set β) :
    μ.map f s = μ (f ⁻¹' s) := by
  refine le_antisymm ?_ (le_map_apply hf.measurable.aemeasurable s)
  set t := f '' toMeasurable μ (f ⁻¹' s) ∪ (range f)ᶜ
  have htm : MeasurableSet t :=
    (hf.measurableSet_image.2 <| measurableSet_toMeasurable _ _).union
      hf.measurableSet_range.compl
  have hst : s ⊆ t := by
    rw [subset_union_compl_iff_inter_subset, ← image_preimage_eq_inter_range]
    exact image_mono (subset_toMeasurable _ _)
  have hft : f ⁻¹' t = toMeasurable μ (f ⁻¹' s) := by
    rw [preimage_union, preimage_compl, preimage_range, compl_univ, union_empty,
      hf.injective.preimage_image]
  calc
    μ.map f s ≤ μ.map f t := by gcongr
    _ = μ (f ⁻¹' s) := by rw [map_apply hf.measurable htm, hft, measure_toMeasurable]

/-
**MeasurableEmbedding.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEmbeddi
ng`。
形式化陈述：map_injective (hf : MeasurableEmbedding f) : Function.Injective (Measure.m
ap f)
参数：hf : MeasurableEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `MeasurableEmbedding.map_apply`：∀ {α : Type u_1} {β : Type u_2} {m0 : Mea
surableSpace α} {m1 : MeasurableSpace β} {f : α → β},   MeasurableEmbedding f → 
∀ (μ : MeasureTheor…
-/
theorem map_injective (hf : MeasurableEmbedding f) : Function.Injective (Measure.map f) := by
  intro μ ν h
  ext s hs
  rw [← Set.preimage_image_eq s hf.injective, ← hf.map_apply, ← hf.map_apply]
  congr

end MeasurableEmbedding

namespace MeasurableEquiv

/-! Interactions of measurable equivalences and measures -/

open Equiv MeasureTheory MeasureTheory.Measure

variable {_ : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- If we map a measure along a measurable equivalence, we can compute the measure on all sets
  (not just the measurable ones). -/
/-
**MeasurableEquiv.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : MeasurableSpace α} [inst : Measurable
Space β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ β) (s : Set β), (MeasureTheor
y.Measure.map (⇑f) μ) s = μ (⇑f ⁻¹' s)
参数：f : α ≃ᵐ β；s : Set β；MeasureTheory.Measure.map (⇑f) μ；⇑f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.map_apply`：∀ {α : Type u_1} {β : Type u_2} {m0 : Mea
surableSpace α} {m1 : MeasurableSpace β} {f : α → β},   MeasurableEmbedding f → 
∀ (μ : MeasureTheor…
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e

--- 原说明 ---
If we map a measure along a measurable equivalence, we can compute the measure o
n all sets
  (not just the measurable ones).
-/
protected theorem map_apply (f : α ≃ᵐ β) (s : Set β) : μ.map f s = μ (f ⁻¹' s) :=
  f.measurableEmbedding.map_apply _ _

@[simp]
/-
**MeasurableEquiv.map_symm_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：map_symm_map (e : α ≃ᵐ β) : (μ.map e).map e.symm = μ
参数：e : α ≃ᵐ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `MeasurableEquiv.symm_comp_self`：symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e
 = id
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_symm_map (e : α ≃ᵐ β) : (μ.map e).map e.symm = μ := by
  simp [map_map e.symm.measurable e.measurable]

@[simp]
/-
**MeasurableEquiv.map_map_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：map_map_symm (e : α ≃ᵐ β) : (ν.map e.symm).map e = ν
参数：e : α ≃ᵐ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `MeasurableEquiv.self_comp_symm`：self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm
 = id
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_map_symm (e : α ≃ᵐ β) : (ν.map e.symm).map e = ν := by
  simp [map_map e.measurable e.symm.measurable]
/-
**MeasurableEquiv.map_measurableEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `Measu
rableEquiv`。
形式化陈述：map_measurableEquiv_injective (e : α ≃ᵐ β) : Injective (Measure.map e)
参数：e : α ≃ᵐ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.map_symm_map`：map_symm_map (e : α ≃ᵐ β) : (μ.map e).map 
e.symm = μ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_measurableEquiv_injective (e : α ≃ᵐ β) : Injective (Measure.map e) := by
  intro μ₁ μ₂ hμ
  apply_fun Measure.map e.symm at hμ
  simpa [map_symm_map e] using hμ
/-
**MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `
MeasurableEquiv`。
形式化陈述：map_apply_eq_iff_map_symm_apply_eq (e : α ≃ᵐ β) : μ.map e = ν ↔ μ = ν.map 
e.symm
参数：e : α ≃ᵐ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MeasurableEquiv.map_measurableEquiv_injective`：map_measurableEquiv_injec
tive (e : α ≃ᵐ β) : Injective (Measure.map e)
· 使用定理 `MeasurableEquiv.map_map_symm`：map_map_symm (e : α ≃ᵐ β) : (ν.map e.symm)
.map e = ν
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_apply_eq_iff_map_symm_apply_eq (e : α ≃ᵐ β) : μ.map e = ν ↔ μ = ν.map e.symm := by
  rw [← (map_measurableEquiv_injective e).eq_iff, map_map_symm]
/-
**MeasurableEquiv.map_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：map_ae (f : α ≃ᵐ β) (μ : Measure α) : Filter.map f (ae μ) = ae (map f μ)
参数：f : α ≃ᵐ β；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_ae (f : α ≃ᵐ β) (μ : Measure α) : Filter.map f (ae μ) = ae (map f μ) := by
  ext s
  simp_rw [mem_map, mem_ae_iff, ← preimage_compl, f.map_apply]

end MeasurableEquiv

