/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.ProductMeasure

/-!
# Independence of an infinite family of random variables

In this file we provide several results about independence of arbitrary families of random
variables, relying on `Measure.infinitePi`.

## Implementation note

There are several possible measurability assumptions:
* The map `ω ↦ (Xᵢ(ω))ᵢ` is measurable.
* For all `i`, the map `ω ↦ Xᵢ(ω)` is measurable.
* The map `ω ↦ (Xᵢ(ω))ᵢ` is almost everywhere measurable.
* For all `i`, the map `ω ↦ Xᵢ(ω)` is almost everywhere measurable.

Although the first two options are equivalent, the last two are not if the index set is not
countable.
-/

public section

open MeasureTheory Measure ProbabilityTheory

namespace ProbabilityTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓧 : ι → Type*} {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} {X : Π i, Ω → 𝓧 i}

/-- If random variables are independent then their joint distribution is the product measure. This
is a version where the random variable `ω ↦ (Xᵢ(ω))ᵢ` is almost everywhere measurable.
See `iIndepFun.map_fun_eq_infinitePi_map₀'` for a version which only assumes that
each `Xᵢ` is almost everywhere measurable and that `ι` is countable. -/
/-
**ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {𝓧 : ι → Type u_3}   {m𝓧 : (i : ι) → MeasurableSpace (𝓧 i)} {X : (i
 : ι) → Ω → 𝓧 i},   (∀ (i : ι), Measurable (X i)) →     ProbabilityTheory.iIndep
Fun X P →       MeasureTheory.Measure.map (fun ω i => X i ω) P =         Measure
Theory.Measure.infinitePi fun i => MeasureTheory.Measure.map (X i) P
参数：i : ι；𝓧 i；i : ι；∀ (i : ι), Measurable (X i)；fun ω i => X i ω；X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map₀`：∀ {ι : Type u_1}
 {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {𝓧 : ι → 
Type u_3}   {m𝓧 : (i : ι) → MeasurableSpace …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a

--- 原说明 ---
If random variables are independent then their joint distribution is the product
 measure. This
is a version where the random variable `ω ↦ (Xᵢ(ω))ᵢ` is almost everywhere measu
rable.
See `iIndepFun.map_fun_eq_infinitePi_map₀'` for a version which only assumes tha
t
each `Xᵢ` is almost everywhere measurable and that `ι` is countable.
-/
lemma iIndepFun.map_fun_eq_infinitePi_map₀ (mX : AEMeasurable (fun ω i ↦ X i ω) P)
    (h : iIndepFun X P) :
    P.map (fun ω i ↦ X i ω) = infinitePi (fun i ↦ P.map (X i)) := by
  have := h.isProbabilityMeasure
  have _ i := isProbabilityMeasure_map (mX.eval i)
  refine eq_infinitePi _ fun s t ht ↦ ?_
  rw [iIndepFun_iff_finset] at h
  have : (s : Set ι).pi t = s.restrict ⁻¹' (Set.univ.pi fun i ↦ t i) := by ext; simp
  rw [this, ← map_apply, AEMeasurable.map_map_of_aemeasurable]
  · have : s.restrict ∘ (fun ω i ↦ X i ω) = fun ω i ↦ s.restrict X i ω := by ext; simp
    rw [this, (h s).map_fun_eq_pi_map, pi_pi]
    · simp only [Finset.restrict]
      rw [s.prod_coe_sort fun i ↦ P.map (X i) (t i)]
    exact fun i ↦ mX.eval i
  any_goals fun_prop
  · exact mX
  · exact .univ_pi fun i ↦ ht i

/-- Random variables are independent iff their joint distribution is the product measure. This
is a version where the random variable `ω ↦ (Xᵢ(ω))ᵢ` is almost everywhere measurable.
See `iIndepFun_iff_map_fun_eq_infinitePi_map₀'` for a version which only assumes that
each `Xᵢ` is almost everywhere measurable and that `ι` is countable. -/
/-
**ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：iIndepFun_iff_map_fun_eq_infinitePi_map [IsProbabilityMeasure P] (mX : for
all i, Measurable (X i)) : iIndepFun X P ↔ P.map (fun ω i => X i ω) = infinitePi
 (fun i => P.map (X i))
参数：mX : forall i, Measurable (X i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map₀`：iIndepFun_if
f_map_fun_eq_infinitePi_map₀ [IsProbabilityMeasure P] (mX : AEMeasurable (fun ω 
i => X i ω) P) : iIndepFun X P ↔ P.map (fun ω i …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a

--- 原说明 ---
Random variables are independent iff their joint distribution is the product mea
sure. This
is a version where the random variable `ω ↦ (Xᵢ(ω))ᵢ` is almost everywhere measu
rable.
See `iIndepFun_iff_map_fun_eq_infinitePi_map₀'` for a version which only assumes
 that
each `Xᵢ` is almost everywhere measurable and that `ι` is countable.
-/
lemma iIndepFun_iff_map_fun_eq_infinitePi_map₀ [IsProbabilityMeasure P]
    (mX : AEMeasurable (fun ω i ↦ X i ω) P) :
    iIndepFun X P ↔ P.map (fun ω i ↦ X i ω) = infinitePi (fun i ↦ P.map (X i)) where
  mp h := h.map_fun_eq_infinitePi_map₀ mX
  mpr h := by
    have _ i := isProbabilityMeasure_map (mX.eval i)
    rw [iIndepFun_iff_finset]
    intro s
    rw [iIndepFun_iff_map_fun_eq_pi_map]
    · have : s.restrict ∘ (fun ω i ↦ X i ω) = fun ω i ↦ s.restrict X i ω := by ext; simp
      rw [← this, ← AEMeasurable.map_map_of_aemeasurable, h, infinitePi_map_restrict]
      · simp
      · fun_prop
      exact mX
    exact fun i ↦ mX.eval i

/-- If random variables are independent then their joint distribution is the product measure. This
is an `AEMeasurable` version of `iIndepFun.map_fun_eq_infinitePi_map`, which is why it requires
`ι` to be countable. -/
/-
**ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {𝓧 : ι → Type u_3}   {m𝓧 : (i : ι) → MeasurableSpace (𝓧 i)} {X : (i
 : ι) → Ω → 𝓧 i},   (∀ (i : ι), Measurable (X i)) →     ProbabilityTheory.iIndep
Fun X P →       MeasureTheory.Measure.map (fun ω i => X i ω) P =         Measure
Theory.Measure.infinitePi fun i => MeasureTheory.Measure.map (X i) P
参数：i : ι；𝓧 i；i : ι；∀ (i : ι), Measurable (X i)；fun ω i => X i ω；X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map₀`：∀ {ι : Type u_1}
 {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {𝓧 : ι → 
Type u_3}   {m𝓧 : (i : ι) → MeasurableSpace …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a

--- 原说明 ---
If random variables are independent then their joint distribution is the product
 measure. This
is an `AEMeasurable` version of `iIndepFun.map_fun_eq_infinitePi_map`, which is 
why it requires
`ι` to be countable.
-/
lemma iIndepFun.map_fun_eq_infinitePi_map₀' [Countable ι] (mX : ∀ i, AEMeasurable (X i) P)
    (h : iIndepFun X P) :
    P.map (fun ω i ↦ X i ω) = infinitePi (fun i ↦ P.map (X i)) :=
  h.map_fun_eq_infinitePi_map₀ <| aemeasurable_pi_iff.2 mX

/-- Random variables are independent iff their joint distribution is the product measure. This is
an `AEMeasurable` version of `iIndepFun_iff_map_fun_eq_infinitePi_map`, which is why it requires
`ι` to be countable. -/
/-
**ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：iIndepFun_iff_map_fun_eq_infinitePi_map [IsProbabilityMeasure P] (mX : for
all i, Measurable (X i)) : iIndepFun X P ↔ P.map (fun ω i => X i ω) = infinitePi
 (fun i => P.map (X i))
参数：mX : forall i, Measurable (X i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map₀`：iIndepFun_if
f_map_fun_eq_infinitePi_map₀ [IsProbabilityMeasure P] (mX : AEMeasurable (fun ω 
i => X i ω) P) : iIndepFun X P ↔ P.map (fun ω i …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a

--- 原说明 ---
Random variables are independent iff their joint distribution is the product mea
sure. This is
an `AEMeasurable` version of `iIndepFun_iff_map_fun_eq_infinitePi_map`, which is
 why it requires
`ι` to be countable.
-/
lemma iIndepFun_iff_map_fun_eq_infinitePi_map₀' [IsProbabilityMeasure P] [Countable ι]
    (mX : ∀ i, AEMeasurable (X i) P) :
    iIndepFun X P ↔ P.map (fun ω i ↦ X i ω) = infinitePi (fun i ↦ P.map (X i)) :=
  iIndepFun_iff_map_fun_eq_infinitePi_map₀ <| aemeasurable_pi_iff.2 mX

/-- If random variables are independent then their joint distribution is the product measure. -/
/-
**ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {𝓧 : ι → Type u_3}   {m𝓧 : (i : ι) → MeasurableSpace (𝓧 i)} {X : (i
 : ι) → Ω → 𝓧 i},   (∀ (i : ι), Measurable (X i)) →     ProbabilityTheory.iIndep
Fun X P →       MeasureTheory.Measure.map (fun ω i => X i ω) P =         Measure
Theory.Measure.infinitePi fun i => MeasureTheory.Measure.map (X i) P
参数：i : ι；𝓧 i；i : ι；∀ (i : ι), Measurable (X i)；fun ω i => X i ω；X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map₀`：∀ {ι : Type u_1}
 {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {𝓧 : ι → 
Type u_3}   {m𝓧 : (i : ι) → MeasurableSpace …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a

--- 原说明 ---
If random variables are independent then their joint distribution is the product
 measure.
-/
lemma iIndepFun.map_fun_eq_infinitePi_map (mX : ∀ i, Measurable (X i)) (h : iIndepFun X P) :
    P.map (fun ω i ↦ X i ω) = infinitePi (fun i ↦ P.map (X i)) :=
  h.map_fun_eq_infinitePi_map₀ <| measurable_pi_iff.2 mX |>.aemeasurable

/-- Random variables are independent iff their joint distribution is the product measure. -/
/-
**ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：iIndepFun_iff_map_fun_eq_infinitePi_map [IsProbabilityMeasure P] (mX : for
all i, Measurable (X i)) : iIndepFun X P ↔ P.map (fun ω i => X i ω) = infinitePi
 (fun i => P.map (X i))
参数：mX : forall i, Measurable (X i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map₀`：iIndepFun_if
f_map_fun_eq_infinitePi_map₀ [IsProbabilityMeasure P] (mX : AEMeasurable (fun ω 
i => X i ω) P) : iIndepFun X P ↔ P.map (fun ω i …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a

--- 原说明 ---
Random variables are independent iff their joint distribution is the product mea
sure.
-/
lemma iIndepFun_iff_map_fun_eq_infinitePi_map [IsProbabilityMeasure P]
    (mX : ∀ i, Measurable (X i)) :
    iIndepFun X P ↔ P.map (fun ω i ↦ X i ω) = infinitePi (fun i ↦ P.map (X i)) :=
  iIndepFun_iff_map_fun_eq_infinitePi_map₀ <| measurable_pi_iff.2 mX |>.aemeasurable
/-
**ProbabilityTheory.iIndepFun.hasLaw_infinitePi** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.iIndepFun`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {𝓧 : ι → Type u_3}   {m𝓧 : (i : ι) → MeasurableSpace (𝓧 i)} {X : (i
 : ι) → Ω → 𝓧 i} {μ : (i : ι) → MeasureTheory.Measure (𝓧 i)},   (∀ (i : ι), Prob
abilityTheory.HasLaw (X i) (μ i) P) →     ProbabilityTheory.iIndepFun X P →     
  AEMeasurable (fun ω i => X i ω) P →         ProbabilityTheory.HasLaw (fun ω i 
=> X i ω) (MeasureTheory.Measure.infinitePi μ) P
参数：i : ι；𝓧 i；i : ι；i : ι；𝓧 i；∀ (i : ι), ProbabilityTheory.HasLaw (X i) (μ i) P；f
un ω i => X i ω；fun ω i => X i ω；MeasureTheory.Measure.infinitePi μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.isProbabilityMeasure`：∀ {Ω : Type u_1} {ι : 
Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type 
u_10}   {m : (i : ι) → MeasurableSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map₀`：iIndepFun_if
f_map_fun_eq_infinitePi_map₀ [IsProbabilityMeasure P] (mX : AEMeasurable (fun ω 
i => X i ω) P) : iIndepFun X P ↔ P.map (fun ω i …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iIndepFun.hasLaw_infinitePi {μ : (i : ι) → Measure (𝓧 i)} (hX : ∀ i, HasLaw (X i) (μ i) P)
    (h1 : iIndepFun X P) (h2 : AEMeasurable (fun ω i ↦ X i ω) P) :
    HasLaw (fun ω i ↦ X i ω) (infinitePi μ) P where
  aemeasurable := h2
  map_eq := by
    have := h1.isProbabilityMeasure
    rw [(iIndepFun_iff_map_fun_eq_infinitePi_map₀ h2).1 h1]
    simp_rw [fun i ↦ (hX i).map_eq]
/-
**ProbabilityTheory.iIndepFun_iff_hasLaw_Pi_infinitePi** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：iIndepFun_iff_hasLaw_Pi_infinitePi [IsProbabilityMeasure P] {μ : (i : ι) -
> Measure (𝓧 i)} (hX : forall i, HasLaw (X i) (μ i) P) (hm : AEMeasurable (fun ω
 i => X i ω) P) : iIndepFun X P ↔ HasLaw (fun ω i => X i ω) (infinitePi μ) P whe
re mp h
参数：i : ι；𝓧 i；hX : forall i, HasLaw (X i) (μ i) P；hm : AEMeasurable (fun ω i => X
 i ω) P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.hasLaw_infinitePi`：∀ {ι : Type u_1} {Ω : Typ
e u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {𝓧 : ι → Type u_3}
   {m𝓧 : (i : ι) → MeasurableSpace …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map₀`：iIndepFun_if
f_map_fun_eq_infinitePi_map₀ [IsProbabilityMeasure P] (mX : AEMeasurable (fun ω 
i => X i ω) P) : iIndepFun X P ↔ P.map (fun ω i …
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iIndepFun_iff_hasLaw_Pi_infinitePi [IsProbabilityMeasure P] {μ : (i : ι) → Measure (𝓧 i)}
    (hX : ∀ i, HasLaw (X i) (μ i) P) (hm : AEMeasurable (fun ω i ↦ X i ω) P) :
    iIndepFun X P ↔ HasLaw (fun ω i ↦ X i ω) (infinitePi μ) P where
  mp h := h.hasLaw_infinitePi hX hm
  mpr h := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀ hm, h.map_eq]
    simp_rw [fun i ↦ (hX i).map_eq]

/-- Given random variables `X i : Ω i → 𝓧 i`, they are independent when viewed as random
variables defined on the product space `Π i, Ω i`. -/
/-
**ProbabilityTheory.iIndepFun_infinitePi** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：iIndepFun_infinitePi {Ω : ι -> Type*} {mΩ : forall i, MeasurableSpace (Ω i
)} {P : (i : ι) -> Measure (Ω i)} [forall i, IsProbabilityMeasure (P i)] {X : (i
 : ι) -> Ω i -> 𝓧 i} (mX : forall i, Measurable (X i)) : iIndepFun (fun i ω => X
 i (ω i)) (infinitePi P)
参数：Ω i；i : ι；Ω i；P i；i : ι；mX : forall i, Measurable (X i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map`：iIndepFun_iff
_map_fun_eq_infinitePi_map [IsProbabilityMeasure P] (mX : forall i, Measurable (
X i)) : iIndepFun X P ↔ P.map (fun ω i => X i ω…
· 使用定理 `MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi`：∀ {ι : T
ype u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpace (X i)} (μ : (i : ι) 
→ MeasureTheory.Measure (X i))   [hμ : ∀ (i : ι), Me…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用引理 `MeasureTheory.Measure.infinitePi_map_pi`：infinitePi_map_pi {Y : ι -> Typ
e*} [forall i, MeasurableSpace (Y i)] {f : (i : ι) -> X i -> Y i} (hf : forall i
, Measurable (f i)) : (infini…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.infinitePi_map_eval`：infinitePi_map_eval (i : ι) :
 (infinitePi μ).map (fun x => x i) = μ i
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)

--- 原说明 ---
Given random variables `X i : Ω i → 𝓧 i`, they are independent when viewed as ra
ndom
variables defined on the product space `Π i, Ω i`.
-/
lemma iIndepFun_infinitePi {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)] {X : (i : ι) → Ω i → 𝓧 i}
    (mX : ∀ i, Measurable (X i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (infinitePi P) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop), infinitePi_map_pi _ mX]
  congrm infinitePi fun i ↦ ?_
  rw [← infinitePi_map_eval P i, map_map (mX i) (by fun_prop), Function.comp_def]
/-
**ProbabilityTheory._root_.MeasureTheory.Measure.infinitePi_map_eval_prod** 是 Ma
thlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.Measure.infinitePi_map_eval_prod {Ω : ι → Type*}
    {mΩ : ∀ i, MeasurableSpace (Ω i)} {P : ∀ i, Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (P i)] {i j : ι} (hij : i ≠ j) :
    (infinitePi P).map (fun ω ↦ (ω i, ω j)) = (P i).prod (P j) := by
  rw [IndepFun.map_prod_eq_prod_map_map]; rotate_right
  · exact iIndepFun_infinitePi (X := fun x ω ↦ ω) (by fun_prop) |>.indepFun hij
  · simp [infinitePi_map_eval]
  all_goals exact Measurable.aemeasurable (by fun_prop)
/-
**ProbabilityTheory._root_.MeasureTheory.Measure.map_infinitePi_infinitePi_of_in
j** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj {α : Type*} {Ω : ι → Type*}
    {mΩ : ∀ i, MeasurableSpace (Ω i)} {P : ∀ i, Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (P i)] {f : α → ι} (hf : Function.Injective f) :
    (infinitePi P).map (fun ω i ↦ ω (f i)) = infinitePi (fun i ↦ P (f i)) := by
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map <| by fun_prop).mp ?_]
  · simp [infinitePi_map_eval]
  exact .precomp hf <| iIndepFun_infinitePi (X := fun x ω ↦ ω) <| by fun_prop

section curry

section dependent

variable {κ : ι → Type*} {𝓧 : (i : ι) → κ i → Type*} {m𝓧 : ∀ i j, MeasurableSpace (𝓧 i j)}

/-- Consider `((Xᵢⱼ)ⱼ)ᵢ` a family of families of random variables.
Assume that for any `i`, the random variables `(Xᵢⱼ)ⱼ` are independent.
Assume furthermore that the random variables `((Xᵢⱼ)ⱼ)ᵢ` are independent.
Then the random variables `(Xᵢⱼ)` indexed by pairs `(i, j)` are independent.

This is a dependent version of `iIndepFun_uncurry'`. -/
/-
**ProbabilityTheory.iIndepFun_uncurry** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：iIndepFun_uncurry {X : (i : ι) -> (j : κ i) -> Ω -> 𝓧 i j} (mX : forall i 
j, Measurable (X i j)) (h1 : iIndepFun (fun i ω => (X i · ω)) P) (h2 : forall i,
 iIndepFun (X i) P) : iIndepFun (fun (p : (i : ι) × (κ i)) ω => X p.1 p.2 ω) P
参数：i : ι；j : κ i；mX : forall i j, Measurable (X i j)；h1 : iIndepFun (fun i ω => 
(X i · ω)) P；h2 : forall i, iIndepFun (X i) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.isProbabilityMeasure`：∀ {Ω : Type u_1} {ι : 
Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type 
u_10}   {m : (i : ι) → MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.piCurry_apply`：∀ {ι : Type u_6} {κ : ι → Type u_7} (X : 
(i : ι) → κ i → Type u_8)   [inst : (i : ι) → (j : κ i) → MeasurableSpace (X i j
)] (f : (x : (i : ι…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map`：iIndepFun_iff
_map_fun_eq_infinitePi_map [IsProbabilityMeasure P] (mX : forall i, Measurable (
X i)) : iIndepFun X P ↔ P.map (fun ω i => X i ω…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MeasurableEquiv.map_measurableEquiv_injective`：map_measurableEquiv_injec
tive (e : α ≃ᵐ β) : Injective (Measure.map e)
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.infinitePi_map_piCurry`：infinitePi_map_piCurry : (
infinitePi fun p : (i : ι) × κ i => μ p.1 p.2).map (piCurry X) = infinitePi fun 
i : ι => infinitePi fun j : κ i =>…

--- 原说明 ---
Consider `((Xᵢⱼ)ⱼ)ᵢ` a family of families of random variables.
Assume that for any `i`, the random variables `(Xᵢⱼ)ⱼ` are independent.
Assume furthermore that the random variables `((Xᵢⱼ)ⱼ)ᵢ` are independent.
Then the random variables `(Xᵢⱼ)` indexed by pairs `(i, j)` are independent.

This is a dependent version of `iIndepFun_uncurry'`.
-/
lemma iIndepFun_uncurry {X : (i : ι) → (j : κ i) → Ω → 𝓧 i j} (mX : ∀ i j, Measurable (X i j))
    (h1 : iIndepFun (fun i ω ↦ (X i · ω)) P) (h2 : ∀ i, iIndepFun (X i) P) :
    iIndepFun (fun (p : (i : ι) × (κ i)) ω ↦ X p.1 p.2 ω) P := by
  have := h1.isProbabilityMeasure
  have : ∀ i j, IsProbabilityMeasure (P.map (X i j)) :=
    fun i j ↦ isProbabilityMeasure_map (mX i j).aemeasurable
  have : ∀ i, IsProbabilityMeasure (P.map (fun ω ↦ (X i · ω))) :=
    fun i ↦ isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  have : (MeasurableEquiv.piCurry 𝓧) ∘ (fun ω p ↦ X p.1 p.2 ω) = fun ω i j ↦ X i j ω := by
    ext; simp [Sigma.curry]
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop),
    ← (MeasurableEquiv.piCurry 𝓧).map_measurableEquiv_injective.eq_iff,
    map_map (by fun_prop) (by fun_prop), this,
    (iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 h1,
    infinitePi_map_piCurry (fun i j ↦ P.map (X i j))]
  congrm infinitePi fun i ↦ ?_
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 (h2 i)]

/-- Given random variables `X i j : Ω i j → 𝓧 i j`, they are independent when viewed as random
variables defined on the product space `Π i, Π j, Ω i j`. -/
/-
**ProbabilityTheory.iIndepFun_uncurry_infinitePi** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：iIndepFun_uncurry_infinitePi {Ω : (i : ι) -> κ i -> Type*} {mΩ : forall i 
j, MeasurableSpace (Ω i j)} {X : (i : ι) -> (j : κ i) -> Ω i j -> 𝓧 i j} (μ : (i
 : ι) -> (j : κ i) -> Measure (Ω i j)) [forall i j, IsProbabilityMeasure (μ i j)
] (mX : forall i j, Measurable (X i j)) : iIndepFun (fun (p : (i : ι) × κ i) (ω 
: Π i, Π j, Ω i j) => X p.1 p.2 (ω p.1 p.2)) (infinitePi (fun i => infinitePi (μ
 i)))
参数：i : ι；Ω i j；i : ι；j : κ i；μ : (i : ι) -> (j : κ i) -> Measure (Ω i j)；μ i j；m
X : forall i j, Measurable (X i j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.iIndepFun_uncurry`：iIndepFun_uncurry {X : (i : ι) -> (
j : κ i) -> Ω -> 𝓧 i j} (mX : forall i j, Measurable (X i j)) (h1 : iIndepFun (f
un i ω => (X i · ω)) P) (…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用引理 `ProbabilityTheory.iIndepFun_infinitePi`：iIndepFun_infinitePi {Ω : ι -> T
ype*} {mΩ : forall i, MeasurableSpace (Ω i)} {P : (i : ι) -> Measure (Ω i)} [for
all i, IsProbabilityMeasure …
· 使用定理 `MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi`：∀ {ι : T
ype u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpace (X i)} (μ : (i : ι) 
→ MeasureTheory.Measure (X i))   [hμ : ∀ (i : ι), Me…
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map`：iIndepFun_iff
_map_fun_eq_infinitePi_map [IsProbabilityMeasure P] (mX : forall i, Measurable (
X i)) : iIndepFun X P ↔ P.map (fun ω i => X i ω…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用引理 `MeasureTheory.Measure.infinitePi_map_pi`：infinitePi_map_pi {Y : ι -> Typ
e*} [forall i, MeasurableSpace (Y i)] {f : (i : ι) -> X i -> Y i} (hf : forall i
, Measurable (f i)) : (infini…
· 使用引理 `MeasureTheory.Measure.infinitePi_map_eval`：infinitePi_map_eval (i : ι) :
 (infinitePi μ).map (fun x => x i) = μ i
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Given random variables `X i j : Ω i j → 𝓧 i j`, they are independent when viewed
 as random
variables defined on the product space `Π i, Π j, Ω i j`.
-/
lemma iIndepFun_uncurry_infinitePi {Ω : (i : ι) → κ i → Type*} {mΩ : ∀ i j, MeasurableSpace (Ω i j)}
    {X : (i : ι) → (j : κ i) → Ω i j → 𝓧 i j}
    (μ : (i : ι) → (j : κ i) → Measure (Ω i j)) [∀ i j, IsProbabilityMeasure (μ i j)]
    (mX : ∀ i j, Measurable (X i j)) :
    iIndepFun (fun (p : (i : ι) × κ i) (ω : Π i, Π j, Ω i j) ↦ X p.1 p.2 (ω p.1 p.2))
      (infinitePi (fun i ↦ infinitePi (μ i))) := by
  refine iIndepFun_uncurry (P := infinitePi (fun i ↦ infinitePi (μ i)))
    (X := fun i j ω ↦ X i j (ω i j)) (by fun_prop) ?_ fun i ↦ ?_
  · exact iIndepFun_infinitePi (P := fun i ↦ infinitePi (μ i))
      (X := fun i u j ↦ X i j (u j)) (by fun_prop)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  change map ((fun f ↦ f i) ∘ (fun ω i j ↦ X i j (ω i j)))
    (infinitePi fun i ↦ infinitePi (μ i)) = _
  rw [← map_map (by fun_prop) (by fun_prop),
    infinitePi_map_pi (X := fun i ↦ (j : κ i) → Ω i j) (μ := fun i ↦ infinitePi (μ i))
      (f := fun i f j ↦ X i j (f j)), @infinitePi_map_eval .., infinitePi_map_pi]
  · congrm infinitePi fun j ↦ ?_
    change _ = map (((fun f ↦ f j) ∘ (fun f ↦ f i)) ∘ (fun ω i j ↦ X i j (ω i j)))
      (infinitePi fun i ↦ infinitePi (μ i))
    rw [← map_map (by fun_prop) (by fun_prop), infinitePi_map_pi (X := fun i ↦ (j : κ i) → Ω i j)
        (μ := fun i ↦ infinitePi (μ i)) (f := fun i f j ↦ X i j (f j)),
        ← map_map (by fun_prop) (by fun_prop),
        @infinitePi_map_eval .., infinitePi_map_pi, @infinitePi_map_eval ..]
    any_goals fun_prop
    · exact fun _ ↦ isProbabilityMeasure_map (by fun_prop)
    · exact fun _ ↦ isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  any_goals fun_prop
  exact fun _ ↦ isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

end dependent

section nondependent

variable {κ : Type*} {𝓧 : ι → κ → Type*} {m𝓧 : ∀ i j, MeasurableSpace (𝓧 i j)}

/-- Consider `((Xᵢⱼ)ⱼ)ᵢ` a family of families of random variables.
Assume that for any `i`, the random variables `(Xᵢⱼ)ⱼ` are independent.
Assume furthermore that the random variables `((Xᵢⱼ)ⱼ)ᵢ` are independent.
Then the random variables `(Xᵢⱼ)` indexed by pairs `(i, j)` are independent.

This is a non-dependent version of `iIndepFun_uncurry`. -/
/-
**ProbabilityTheory.iIndepFun_uncurry'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：iIndepFun_uncurry' {X : (i : ι) -> (j : κ) -> Ω -> 𝓧 i j} (mX : forall i j
, Measurable (X i j)) (h1 : iIndepFun (fun i ω => (X i · ω)) P) (h2 : forall i, 
iIndepFun (X i) P) : iIndepFun (fun (p : ι × κ) ω => X p.1 p.2 ω) P
参数：i : ι；j : κ；mX : forall i j, Measurable (X i j)；h1 : iIndepFun (fun i ω => (X
 i · ω)) P；h2 : forall i, iIndepFun (X i) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.of_precomp`：∀ {Ω : Type u_1} {ι : Type u_2} 
{x : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ι' : Type u_6} {g : ι' → 
ι}   {β : ι → Type u_7} {m :…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用引理 `ProbabilityTheory.iIndepFun_uncurry`：iIndepFun_uncurry {X : (i : ι) -> (
j : κ i) -> Ω -> 𝓧 i j} (mX : forall i j, Measurable (X i j)) (h1 : iIndepFun (f
un i ω => (X i · ω)) P) (…

--- 原说明 ---
Consider `((Xᵢⱼ)ⱼ)ᵢ` a family of families of random variables.
Assume that for any `i`, the random variables `(Xᵢⱼ)ⱼ` are independent.
Assume furthermore that the random variables `((Xᵢⱼ)ⱼ)ᵢ` are independent.
Then the random variables `(Xᵢⱼ)` indexed by pairs `(i, j)` are independent.

This is a non-dependent version of `iIndepFun_uncurry`.
-/
lemma iIndepFun_uncurry' {X : (i : ι) → (j : κ) → Ω → 𝓧 i j} (mX : ∀ i j, Measurable (X i j))
    (h1 : iIndepFun (fun i ω ↦ (X i · ω)) P) (h2 : ∀ i, iIndepFun (X i) P) :
    iIndepFun (fun (p : ι × κ) ω ↦ X p.1 p.2 ω) P :=
  (iIndepFun_uncurry mX h1 h2).of_precomp (Equiv.sigmaEquivProd ι κ).surjective

/-- Given random variables `X i j : Ω i j → 𝓧 i j`, they are independent when viewed as random
variables defined on the product space `Π i, Π j, Ω i j`. -/
/-
**ProbabilityTheory.iIndepFun_uncurry_infinitePi'** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：iIndepFun_uncurry_infinitePi' {Ω : ι -> κ -> Type*} {mΩ : forall i j, Meas
urableSpace (Ω i j)} {X : (i : ι) -> (j : κ) -> Ω i j -> 𝓧 i j} (μ : (i : ι) -> 
(j : κ) -> Measure (Ω i j)) [forall i j, IsProbabilityMeasure (μ i j)] (mX : for
all i j, Measurable (X i j)) : iIndepFun (fun (p : ι × κ) (ω : Π i, Π j, Ω i j) 
=> X p.1 p.2 (ω p.1 p.2)) (infinitePi (fun i => infinitePi (μ i)))
参数：Ω i j；i : ι；j : κ；μ : (i : ι) -> (j : κ) -> Measure (Ω i j)；μ i j；mX : forall
 i j, Measurable (X i j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.of_precomp`：∀ {Ω : Type u_1} {ι : Type u_2} 
{x : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ι' : Type u_6} {g : ι' → 
ι}   {β : ι → Type u_7} {m :…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用引理 `ProbabilityTheory.iIndepFun_uncurry_infinitePi`：iIndepFun_uncurry_infini
tePi {Ω : (i : ι) -> κ i -> Type*} {mΩ : forall i j, MeasurableSpace (Ω i j)} {X
 : (i : ι) -> (j : κ i) -> Ω i j -> …

--- 原说明 ---
Given random variables `X i j : Ω i j → 𝓧 i j`, they are independent when viewed
 as random
variables defined on the product space `Π i, Π j, Ω i j`.
-/
lemma iIndepFun_uncurry_infinitePi' {Ω : ι → κ → Type*} {mΩ : ∀ i j, MeasurableSpace (Ω i j)}
    {X : (i : ι) → (j : κ) → Ω i j → 𝓧 i j}
    (μ : (i : ι) → (j : κ) → Measure (Ω i j)) [∀ i j, IsProbabilityMeasure (μ i j)]
    (mX : ∀ i j, Measurable (X i j)) :
    iIndepFun (fun (p : ι × κ) (ω : Π i, Π j, Ω i j) ↦ X p.1 p.2 (ω p.1 p.2))
      (infinitePi (fun i ↦ infinitePi (μ i))) :=
  (iIndepFun_uncurry_infinitePi μ mX).of_precomp (Equiv.sigmaEquivProd ι κ).surjective

end nondependent

end curry

end ProbabilityTheory

