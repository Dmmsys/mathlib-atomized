/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Wanyi He, Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Submodule.Pointwise

/-!
# Categorical constructions for `IsSMulRegular`
-/

@[expose] public section

universe u v w

variable {R : Type u} [CommRing R] (M : ModuleCat.{v} R)

open CategoryTheory Abelian Pointwise

/-
**LinearMap.exact_lsmul_mkQ_smul_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.exact_lsmul_mkQ_smul_top (M : Type v) [AddCommGroup M] [Module R
 M] (r : R) : Function.Exact (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).m
kQ
参数：M : Type v；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma LinearMap.exact_lsmul_mkQ_smul_top (M : Type v) [AddCommGroup M] [Module R M] (r : R) :
    Function.Exact (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).mkQ := by
  intro x
  simp [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_smul_pointwise_iff_exists]

@[deprecated (since := "2026-04-13")]
alias LinearMap.exact_smul_id_smul_top_mkQ := LinearMap.exact_lsmul_mkQ_smul_top

namespace ModuleCat

/-- The short (exact) complex `M → M → M⧸xM` obtain from the scalar multiple of `x : R` on `M`. -/
@[simps!]
/-
**ModuleCat.smulShortComplex** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：smulShortComplex (r : R) : ShortComplex (ModuleCat R)
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short (exact) complex `M → M → M⧸xM` obtain from the scalar multiple of `x :
 R` on `M`.
-/
def smulShortComplex (r : R) : ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).mkQ
    (LinearMap.exact_lsmul_mkQ_smul_top M r).linearMap_comp_eq_zero

@[simp]
/-
**ModuleCat.smulShortComplex_f_eq_smul_id** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：smulShortComplex_f_eq_smul_id (r : R) : (M.smulShortComplex r).f = r • 𝟙 M
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smulShortComplex_f_eq_smul_id (r : R) : (M.smulShortComplex r).f = r • 𝟙 M := rfl
/-
**ModuleCat.smulShortComplex_exact** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：smulShortComplex_exact (r : R) : (smulShortComplex M r).Exact
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.shortComplex_exact`：ModuleCat.shortComplex_exact (S : ShortCom
plex (ModuleCat.{v} R)) (exac : Function.Exact S.f S.g) : S.Exact
· 使用引理 `LinearMap.exact_lsmul_mkQ_smul_top`：LinearMap.exact_lsmul_mkQ_smul_top (
M : Type v) [AddCommGroup M] [Module R M] (r : R) : Function.Exact (LinearMap.ls
mul _ M r) (r • (⊤ : Sub…
-/
lemma smulShortComplex_exact (r : R) : (smulShortComplex M r).Exact :=
  ModuleCat.shortComplex_exact _ (LinearMap.exact_lsmul_mkQ_smul_top M r)
/-
**ModuleCat.smulShortComplex_g_epi** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：smulShortComplex_g_epi (r : R) : Epi (smulShortComplex M r).g
参数：r : R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
-/
instance smulShortComplex_g_epi (r : R) : Epi (smulShortComplex M r).g := by
  simpa [smulShortComplex, ModuleCat.epi_iff_surjective] using Submodule.mkQ_surjective _

end ModuleCat

variable {M} in
/-
**IsSMulRegular.smulShortComplex_shortExact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSMulRegular.smulShortComplex_shortExact {r : R} (reg : IsSMulRegular M r
) : (ModuleCat.smulShortComplex M r).ShortExact where exact
参数：reg : IsSMulRegular M r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.smulShortComplex_exact`：smulShortComplex_exact (r : R) : (smul
ShortComplex M r).Exact
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
-/
lemma IsSMulRegular.smulShortComplex_shortExact {r : R} (reg : IsSMulRegular M r) :
    (ModuleCat.smulShortComplex M r).ShortExact where
  exact := ModuleCat.smulShortComplex_exact M r
  mono_f := by simpa [ModuleCat.smulShortComplex, ModuleCat.mono_iff_injective] using! reg
