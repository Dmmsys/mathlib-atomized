/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Cusp form submodule and IsCuspForm predicate

This file defines the inclusion of cusp forms into modular forms as a linear map, the cusp form
submodule of modular forms, and the `IsCuspForm` predicate. It also provides a direct constructor
`ModularForm.toCuspForm` for building cusp forms from modular forms with vanishing constant
q-expansion coefficient (for `𝒮ℒ`).

## Main definitions

* `CuspForm.toModularFormₗ`: the inclusion `CuspForm Γ k →ₗ[ℂ] ModularForm Γ k`.
* `ModularForm.cuspFormSubmodule`: the submodule of `ModularForm Γ k` consisting of cusp forms.
* `ModularForm.IsCuspForm`: predicate that a modular form lies in the cusp form submodule.
* `ModularForm.toCuspForm`: builds a `CuspForm 𝒮ℒ k` from a `ModularForm` whose q-expansion
  has vanishing constant term.

## Main results

* `CuspForm.toModularFormₗ_injective`: the inclusion is injective.
* `CuspForm.equivCuspFormSubmodule`: `CuspForm Γ k ≃ₗ[ℂ] cuspFormSubmodule Γ k`.
* `ModularForm.isCuspForm_iff_coeffZero_eq_zero`: for `𝒮ℒ`, `IsCuspForm` is equivalent to the
  q-expansion having vanishing constant term.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm Complex SlashInvariantForm SlashInvariantFormClass
  ModularFormClass MatrixGroups OnePoint Filter Topology

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

namespace CuspForm

/-- The inclusion of cusp forms into modular forms, as a ℂ-linear map. -/
/-
**CuspForm.toModularForm** 是 Mathlib 中的一个定义，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of cusp forms into modular forms, as a ℂ-linear map.
-/
def toModularFormₗ [Γ.HasDetOne] : CuspForm Γ k →ₗ[ℂ] ModularForm Γ k where
  toFun := ModularFormClass.modularForm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/-
**CuspForm.toModularForm** 是 Mathlib 中的一个引理，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toModularFormₗ_apply [Γ.HasDetOne] (f : CuspForm Γ k) (z : ℍ) :
    (toModularFormₗ f) z = f z := rfl
/-
**CuspForm.toModularForm** 是 Mathlib 中的一个引理，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toModularFormₗ_eq_coe [Γ.HasDetOne] (f : CuspForm Γ k) :
    toModularFormₗ f = (f : ModularForm Γ k) := rfl
/-
**CuspForm.toModularForm** 是 Mathlib 中的一个引理，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toModularFormₗ_injective [Γ.HasDetOne] :
    Function.Injective (toModularFormₗ : CuspForm Γ k → ModularForm Γ k) :=
  fun _ _ h ↦ DFunLike.ext _ _ fun z ↦ DFunLike.congr_fun h z

end CuspForm

namespace ModularForm

/-- The submodule of `ModularForm Γ k` consisting of cusp forms, defined as the range of
the inclusion `CuspForm.toModularFormₗ`. -/
/-
**ModularForm.cuspFormSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：cuspFormSubmodule (Γ : Subgroup (GL (Fin 2) Real)) (k : Int) [Γ.HasDetOne]
 : Submodule Complex (ModularForm Γ k)
参数：Γ : Subgroup (GL (Fin 2) Real)；k : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule of `ModularForm Γ k` consisting of cusp forms, defined as the rang
e of
the inclusion `CuspForm.toModularFormₗ`.
-/
def cuspFormSubmodule (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) [Γ.HasDetOne] :
    Submodule ℂ (ModularForm Γ k) :=
  LinearMap.range CuspForm.toModularFormₗ

/-- A modular form is a cusp form if it lies in the cusp form submodule. -/
/-
**ModularForm.IsCuspForm** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：IsCuspForm [Γ.HasDetOne] (f : ModularForm Γ k) : Prop
参数：f : ModularForm Γ k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A modular form is a cusp form if it lies in the cusp form submodule.
-/
def IsCuspForm [Γ.HasDetOne] (f : ModularForm Γ k) : Prop :=
  f ∈ cuspFormSubmodule Γ k

@[simp]
/-
**ModularForm.mem_cuspFormSubmodule_iff** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：mem_cuspFormSubmodule_iff [Γ.HasDetOne] {f : ModularForm Γ k} : f in cuspF
ormSubmodule Γ k ↔ IsCuspForm f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_cuspFormSubmodule_iff [Γ.HasDetOne] {f : ModularForm Γ k} :
    f ∈ cuspFormSubmodule Γ k ↔ IsCuspForm f := Iff.rfl

/-- The cusp form submodule is linearly equivalent to the type of cusp forms. -/
/-
**ModularForm.CuspForm.equivCuspFormSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Modular
Form.CuspForm`。
形式化陈述：(Γ : Subgroup (GL (Fin 2) ℝ)) → (k : ℤ) → [inst : Γ.HasDetOne] → CuspForm 
Γ k ≃ₗ[ℂ] ↥(ModularForm.cuspFormSubmodule Γ k)
参数：GL (Fin 2) ℝ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CuspForm.toModularFormₗ_injective`：toModularFormₗ_injective [Γ.HasDetOne
] : Function.Injective (toModularFormₗ : CuspForm Γ k -> ModularForm Γ k)

--- 原说明 ---
The cusp form submodule is linearly equivalent to the type of cusp forms.
-/
def CuspForm.equivCuspFormSubmodule (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) [Γ.HasDetOne] :
    CuspForm Γ k ≃ₗ[ℂ] cuspFormSubmodule Γ k :=
  LinearEquiv.ofInjective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

/-- The underlying modular form (via `toModularFormₗ`) of a `CuspForm` is itself a cusp form. -/
/-
**ModularForm.CuspForm.isCuspForm_toModularForm** 是 Mathlib 中的一个引理，位于命名空间 `Modul
arForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying modular form (via `toModularFormₗ`) of a `CuspForm` is itself a c
usp form.
-/
lemma CuspForm.isCuspForm_toModularFormₗ {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (f : CuspForm Γ k) : ModularForm.IsCuspForm f.toModularFormₗ := by
  simp [← mem_cuspFormSubmodule_iff, ModularForm.cuspFormSubmodule]

/-- A modular form is a cusp form if and only if it vanishes at every cusp. This is the
general characterization valid for any subgroup. -/
/-
**ModularForm.isCuspForm_iff** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：isCuspForm_iff [Γ.HasDetOne] (f : ModularForm Γ k) : IsCuspForm f ↔ forall
 {c}, IsCusp c Γ -> c.IsZeroAt f k
参数：f : ModularForm Γ k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CuspForm.zero_at_cusps'`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (self :
 CuspForm Γ k) {c : OnePoint ℝ}, IsCusp c Γ → c.IsZeroAt self.toFun k
· 使用定理 `SlashInvariantForm.slash_action_eqn`：slash_action_eqn [SlashInvariantFor
mClass F Γ k] (f : F) (γ) (hγ : γ in Γ) : ↑f ∣[k] γ = ⇑f
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …
· 使用定理 `ModularForm.instModularFormClass`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ
), ModularFormClass (ModularForm Γ k) Γ k
· 使用定理 `ModularForm.holo'`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (self : Modul
arForm Γ k), MDiff ⇑self.toSlashInvariantForm

--- 原说明 ---
A modular form is a cusp form if and only if it vanishes at every cusp. This is 
the
general characterization valid for any subgroup.
-/
lemma isCuspForm_iff [Γ.HasDetOne] (f : ModularForm Γ k) :
    IsCuspForm f ↔ ∀ {c}, IsCusp c Γ → c.IsZeroAt f k :=
  ⟨fun ⟨g, hg⟩ _ ↦ hg ▸ g.zero_at_cusps', fun h ↦ ⟨⟨f, f.holo', h⟩, rfl⟩⟩

/-- A modular form with `valueAtInfty f = 0` is zero at infinity. -/
/-
**ModularForm.isZeroAtImInfty_of_valueAtInfty_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 
`ModularForm`。
形式化陈述：isZeroAtImInfty_of_valueAtInfty_eq_zero {F : Type*} [FunLike F ℍ Complex] 
[DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] [Fact (IsCusp ∞ Γ)] [ModularFormClas
s F Γ k] (f : F) (h : valueAtInfty f = 0) : IsZeroAtImInfty f
参数：IsCusp ∞ Γ；f : F；h : valueAtInfty f = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Subgroup.strictWidthInfty_pos_iff`：strictWidthInfty_pos_iff [DiscreteTop
ology 𝒢.strictPeriods] [𝒢.HasDetPlusMinusOne] : 0 < 𝒢.strictWidthInfty ↔ IsCusp 
∞ 𝒢
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `Subgroup.strictWidthInfty_mem_strictPeriods`：strictWidthInfty_mem_strict
Periods : 𝒢.strictWidthInfty in 𝒢.strictPeriods
· 使用定理 `ModularFormClass.analyticAt_cuspFunction_zero`：∀ {k : ℤ} {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F
)   [ModularFormClass F Γ k], 0 < h…
· 使用定理 `SlashInvariantFormClass.periodic_comp_ofComplex`：periodic_comp_ofComplex
 [SlashInvariantFormClass F Γ k] (hΓ : h in Γ.strictPeriods) : Periodic (f ∘ ofC
omplex) h
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `UpperHalfPlane.cuspFunction_apply_zero`：cuspFunction_apply_zero {f : ℍ -
> Complex} (hh : 0 < h) (hfanalytic : AnalyticAt Complex (cuspFunction h f) 0) (
hfper : Periodic (f ∘ UpperH…
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `SlashInvariantFormClass.eq_cuspFunction`：∀ {k : ℤ} {F : Type u_1} [inst 
: FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F)   [S
lashInvariantFormClass F Γ k]…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用引理 `UpperHalfPlane.qParam_tendsto_atImInfty`：qParam_tendsto_atImInfty {h : R
eal} (hh : 0 < h) : Tendsto (fun τ : ℍ => 𝕢 h τ) atImInfty (nhds 0)

--- 原说明 ---
A modular form with `valueAtInfty f = 0` is zero at infinity.
-/
lemma isZeroAtImInfty_of_valueAtInfty_eq_zero {F : Type*} [FunLike F ℍ ℂ]
    [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] [Fact (IsCusp ∞ Γ)] [ModularFormClass F Γ k]
    (f : F) (h : valueAtInfty f = 0) : IsZeroAtImInfty f := by
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have hΓ : Γ.strictWidthInfty ∈ Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  have hanal := ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
  have hper := periodic_comp_ofComplex f hΓ
  simp_rw [IsZeroAtImInfty, ZeroAtFilter, ← h, ← cuspFunction_apply_zero hh hanal hper]
  exact (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)).congr
    (fun τ ↦ SlashInvariantFormClass.eq_cuspFunction f τ hΓ hh.ne')

section SL2Z

variable {k : ℤ}

/-- An `𝒮ℒ` modular form with vanishing q-expansion constant term vanishes at every cusp. -/
/-
**ModularForm.isZeroAt_of_coeffZero_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `ModularFo
rm`。
形式化陈述：isZeroAt_of_coeffZero_eq_zero (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f)
.coeff 0 = 0) {c : OnePoint Real} (hc : IsCusp c 𝒮ℒ) : c.IsZeroAt f k
参数：f : ModularForm 𝒮ℒ k；h : (qExpansion 1 f).coeff 0 = 0；hc : IsCusp c 𝒮ℒ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `OnePoint.isZeroAt_iff_forall_SL2Z`：isZeroAt_iff_forall_SL2Z (hc : IsCusp
 c 𝒮ℒ) : IsZeroAt c f k ↔ forall γ : SL(2, Int), mapGL Real γ • ∞ = c -> IsZeroA
tImInfty (f ∣[k] γ)
· 使用引理 `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`：Subgroup.IsArithmetic.isCu
sp_iff_isCusp_SL2Z (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmetic] {c : OnePoi
nt Real} : IsCusp c 𝒢 ↔ IsCusp c 𝒮…
· 使用定理 `Subgroup.instIsArithmeticRangeSpecialLinearGroupFinOfNatNatIntGeneralLin
earGroupRealMapGL`：(Matrix.SpecialLinearGroup.mapGL ℝ).range.IsArithmetic
· 使用定理 `SlashInvariantForm.slash_action_eq'`：∀ {Γ : outParam (Subgroup (GL (Fin 
2) ℝ))} {k : outParam ℤ} (self : SlashInvariantForm Γ k),   ∀ γ ∈ Γ, SlashAction
.map k γ self.toFun = sel…
· 使用引理 `ModularForm.isZeroAtImInfty_of_valueAtInfty_eq_zero`：isZeroAtImInfty_of_
valueAtInfty_eq_zero {F : Type*} [FunLike F ℍ Complex] [DiscreteTopology Γ] [Γ.H
asDetPlusMinusOne] [Fact (IsCusp ∞ Γ)] [M…
· 使用定理 `Subgroup.instHasDetPlusMinusOneFinOfNatNatRealOfIsArithmetic`：∀ {Γ : Sub
group (GL (Fin 2) ℝ)} [h : Γ.IsArithmetic], Γ.HasDetPlusMinusOne
· 使用定理 `instFactIsCuspInftyRealOfIsArithmetic`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} [
Γ.IsArithmetic], Fact (IsCusp OnePoint.infty Γ)
· 使用定理 `ModularForm.instModularFormClass`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ
), ModularFormClass (ModularForm Γ k) Γ k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `UpperHalfPlane.qExpansion_coeff_zero`：qExpansion_coeff_zero {f : ℍ -> Co
mplex} (hh : 0 < h) (hfanalytic : AnalyticAt Complex (cuspFunction h f) 0) (hfpe
r : Periodic (f ∘ UpperHal…
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ModularFormClass.analyticAt_cuspFunction_zero`：∀ {k : ℤ} {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F
)   [ModularFormClass F Γ k], 0 < h…
· 使用引理 `one_mem_strictPeriods_SL`：one_mem_strictPeriods_SL : (1 : Real) in (𝒮ℒ).
strictPeriods
· 使用定理 `SlashInvariantFormClass.periodic_comp_ofComplex`：periodic_comp_ofComplex
 [SlashInvariantFormClass F Γ k] (hΓ : h in Γ.strictPeriods) : Periodic (f ∘ ofC
omplex) h
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …

--- 原说明 ---
An `𝒮ℒ` modular form with vanishing q-expansion constant term vanishes at every 
cusp.
-/
lemma isZeroAt_of_coeffZero_eq_zero (f : ModularForm 𝒮ℒ k)
    (h : (qExpansion 1 f).coeff 0 = 0) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsZeroAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  rw [show (⇑f ∣[k] γ) = ⇑f from f.slash_action_eq' _ ⟨γ, rfl⟩]
  exact isZeroAtImInfty_of_valueAtInfty_eq_zero f <| by
    rwa [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL)
      (periodic_comp_ofComplex f one_mem_strictPeriods_SL)]

/-- Build a `CuspForm 𝒮ℒ k` from a `ModularForm 𝒮ℒ k` whose q-expansion has vanishing
constant term. The resulting cusp form has the same underlying function. -/
/-
**ModularForm.toCuspForm** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：toCuspForm (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0) : Cus
pForm 𝒮ℒ k
参数：f : ModularForm 𝒮ℒ k；h : (qExpansion 1 f).coeff 0 = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ModularForm.isZeroAt_of_coeffZero_eq_zero`：isZeroAt_of_coeffZero_eq_zero
 (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0) {c : OnePoint Real} (
hc : IsCusp c 𝒮ℒ) : c.IsZeroAt …

--- 原说明 ---
Build a `CuspForm 𝒮ℒ k` from a `ModularForm 𝒮ℒ k` whose q-expansion has vanishin
g
constant term. The resulting cusp form has the same underlying function.
-/
def toCuspForm (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0) : CuspForm 𝒮ℒ k :=
  { f with zero_at_cusps' := isZeroAt_of_coeffZero_eq_zero f h }

@[simp]
/-
**ModularForm.toCuspForm_apply** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：toCuspForm_apply (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0)
 (z : ℍ) : (toCuspForm f h) z = f z
参数：f : ModularForm 𝒮ℒ k；h : (qExpansion 1 f).coeff 0 = 0；z : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toCuspForm_apply (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0)
    (z : ℍ) : (toCuspForm f h) z = f z := rfl

/-- For `𝒮ℒ` modular forms, `IsCuspForm` is equivalent to the q-expansion having vanishing
constant term. -/
/-
**ModularForm.isCuspForm_iff_coeffZero_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Modula
rForm`。
形式化陈述：isCuspForm_iff_coeffZero_eq_zero (f : ModularForm 𝒮ℒ k) : IsCuspForm f ↔ (
qExpansion 1 f).coeff 0 = 0
参数：f : ModularForm 𝒮ℒ k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `UpperHalfPlane.qExpansion_coeff_zero`：qExpansion_coeff_zero {f : ℍ -> Co
mplex} (hh : 0 < h) (hfanalytic : AnalyticAt Complex (cuspFunction h f) 0) (hfpe
r : Periodic (f ∘ UpperHal…
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ModularFormClass.analyticAt_cuspFunction_zero`：∀ {k : ℤ} {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F
)   [ModularFormClass F Γ k], 0 < h…
· 使用定理 `ModularForm.instModularFormClass`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ
), ModularFormClass (ModularForm Γ k) Γ k
· 使用引理 `one_mem_strictPeriods_SL`：one_mem_strictPeriods_SL : (1 : Real) in (𝒮ℒ).
strictPeriods
· 使用定理 `SlashInvariantFormClass.periodic_comp_ofComplex`：periodic_comp_ofComplex
 [SlashInvariantFormClass F Γ k] (hΓ : h in Γ.strictPeriods) : Periodic (f ∘ ofC
omplex) h
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …
· 使用定理 `UpperHalfPlane.IsZeroAtImInfty.valueAtInfty_eq_zero`：∀ {f : UpperHalfPla
ne → ℂ}, UpperHalfPlane.IsZeroAtImInfty f → UpperHalfPlane.valueAtInfty f = 0
· 使用引理 `CuspFormClass.zero_at_infty`：CuspFormClass.zero_at_infty [CuspFormClass 
F Γ k] [Fact (IsCusp ∞ Γ)] : IsZeroAtImInfty f
· 使用定理 `CuspFormClass.cuspForm`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ), CuspFor
mClass (CuspForm Γ k) Γ k
· 使用定理 `instFactIsCuspInftyRealOfIsArithmetic`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} [
Γ.IsArithmetic], Fact (IsCusp OnePoint.infty Γ)
· 使用定理 `Subgroup.instIsArithmeticRangeSpecialLinearGroupFinOfNatNatIntGeneralLin
earGroupRealMapGL`：(Matrix.SpecialLinearGroup.mapGL ℝ).range.IsArithmetic
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ModularForm.isCuspForm_iff`：isCuspForm_iff [Γ.HasDetOne] (f : ModularFor
m Γ k) : IsCuspForm f ↔ forall {c}, IsCusp c Γ -> c.IsZeroAt f k
· 使用引理 `ModularForm.isZeroAt_of_coeffZero_eq_zero`：isZeroAt_of_coeffZero_eq_zero
 (f : ModularForm 𝒮ℒ k) (h : (qExpansion 1 f).coeff 0 = 0) {c : OnePoint Real} (
hc : IsCusp c 𝒮ℒ) : c.IsZeroAt …

--- 原说明 ---
For `𝒮ℒ` modular forms, `IsCuspForm` is equivalent to the q-expansion having van
ishing
constant term.
-/
lemma isCuspForm_iff_coeffZero_eq_zero (f : ModularForm 𝒮ℒ k) :
    IsCuspForm f ↔ (qExpansion 1 f).coeff 0 = 0 := by
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun h ↦ (isCuspForm_iff f).mpr (isZeroAt_of_coeffZero_eq_zero f h)⟩
  rw [← hg, qExpansion_coeff_zero one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL)
    (periodic_comp_ofComplex _ one_mem_strictPeriods_SL)]
  exact (CuspFormClass.zero_at_infty g).valueAtInfty_eq_zero

/-- Subtracting `(qExpansion 1 f).coeff 0 • g` from `f` (where `g` has constant qExpansion 1)
gives a cusp form. -/
/-
**ModularForm.sub_smul_isCuspForm** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：sub_smul_isCuspForm (f g : ModularForm 𝒮ℒ k) (hg : (qExpansion 1 g).coeff 
0 = 1) : ModularForm.IsCuspForm (f - (qExpansion 1 f).coeff 0 • g)
参数：f g : ModularForm 𝒮ℒ k；hg : (qExpansion 1 g).coeff 0 = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModularForm.isCuspForm_iff_coeffZero_eq_zero`：isCuspForm_iff_coeffZero_e
q_zero (f : ModularForm 𝒮ℒ k) : IsCuspForm f ↔ (qExpansion 1 f).coeff 0 = 0
· 使用定理 `FunLike.coe_sub`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Sub F] [inst_2 : Sub β]   [IsSubApply F α β] (f g : F),
 ⇑(f …
· 使用定理 `ModularForm.instIsSubApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup (GL (Fi
n 2) ℝ)} {k : ℤ}, IsSubApply (ModularForm Γ k) UpperHalfPlane ℂ
· 使用定理 `ModularForm.qExpansion_sub`：∀ {F : Type u_1} [inst : FunLike F UpperHalf
Plane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} {G : Type u_2}   [inst_1 : FunLik
e G UpperHalfPla…
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `one_mem_strictPeriods_SL`：one_mem_strictPeriods_SL : (1 : Real) in (𝒮ℒ).
strictPeriods
· 使用定理 `ModularForm.instModularFormClass`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ
), ModularFormClass (ModularForm Γ k) Γ k
· 使用定理 `FunLike.coe_smul`：coe_smul [SMul M F] [SMul M β] [IsSMulApply M F α β] (
n : M) (f : F) : ↑(n • f) = n • (f : α -> β)
· 使用定理 `ModularForm.instIsSMulApplyℂ`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {α
 : Type u_1} [inst : SMul α ℂ] [inst_1 : IsScalarTower α ℂ ℂ]   [inst_2 : Γ.HasD
etOne], IsSMulAppl…
· 使用定理 `ModularForm.qExpansion_smul`：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F 
UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ},   0 < h →     h ∈ Γ.str
ictPeriods →     …
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `PowerSeries.coeff_smul`：coeff_smul {S : Type*} [Semiring S] [Module R S]
 (n : Nat) (φ : PowerSeries S) (a : R) : coeff n (a • φ) = a • coeff n φ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Subtracting `(qExpansion 1 f).coeff 0 • g` from `f` (where `g` has constant qExp
ansion 1)
gives a cusp form.
-/
lemma sub_smul_isCuspForm (f g : ModularForm 𝒮ℒ k)
    (hg : (qExpansion 1 g).coeff 0 = 1) :
    ModularForm.IsCuspForm (f - (qExpansion 1 f).coeff 0 • g) := by
  rw [isCuspForm_iff_coeffZero_eq_zero, FunLike.coe_sub,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, map_sub, PowerSeries.coeff_smul]
  simp [hg]

end SL2Z

end ModularForm

