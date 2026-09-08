/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone, Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Polish

/-!
# Properties of the extended logarithm and exponential

We prove that `log` and `exp` define order isomorphisms between `ℝ≥0∞` and `EReal`.

## Main Definitions
- `ENNReal.logOrderIso`: The order isomorphism between `ℝ≥0∞` and `EReal` defined by `log`
  and `exp`.
- `EReal.expOrderIso`: The order isomorphism between `EReal` and `ℝ≥0∞` defined by `exp`
  and `log`.
- `ENNReal.logHomeomorph`: `log` as a homeomorphism.
- `EReal.expHomeomorph`: `exp` as a homeomorphism.

## Main Results
- `EReal.log_exp`, `ENNReal.exp_log`: `log` and `exp` are inverses of each other.
- `EReal.exp_nmul`, `EReal.exp_mul`: `exp` satisfies the identities `exp (n * x) = (exp x) ^ n`
  and `exp (x * y) = (exp x) ^ y`.
- `EReal` is a Polish space.

## Tags
ENNReal, EReal, logarithm, exponential
-/

@[expose] public section

open EReal ENNReal Topology
section LogExp

/-
**EReal.log_exp** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x : EReal), x.exp.log = x
参数：x : EReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.log_zero`：ENNReal.log 0 = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EReal.exp_coe`：∀ (x : ℝ), (↑x).exp = ENNReal.ofReal (Real.exp x)
· 使用引理 `ENNReal.log_ofReal`：log_ofReal (x : Real) : log (ENNReal.ofReal x) = if 
x <= 0 then ⊥ else ↑(Real.log x)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
-/
@[simp] lemma EReal.log_exp (x : EReal) : log (exp x) = x := by
  induction x
  · simp
  · rw [exp_coe, log_ofReal, if_neg (not_le.mpr (Real.exp_pos _)), Real.log_exp]
  · simp
/-
**ENNReal.exp_log** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (x : ENNReal), x.log.exp = x
参数：x : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.log_zero`：ENNReal.log 0 = ⊥
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用引理 `ENNReal.log_ofReal_of_pos`：log_ofReal_of_pos {x : Real} (hx : 0 < x) : l
og (ENNReal.ofReal x) = Real.log x
· 使用定理 `EReal.exp_coe`：∀ (x : ℝ), (↑x).exp = ENNReal.ofReal (Real.exp x)
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
-/
@[simp] lemma ENNReal.exp_log (x : ℝ≥0∞) : exp (log x) = x := by
  by_cases hx_top : x = ∞
  · simp [hx_top]
  by_cases hx_zero : x = 0
  · simp [hx_zero]
  have hx_pos : 0 < x.toReal := ENNReal.toReal_pos hx_zero hx_top
  rw [← ENNReal.ofReal_toReal hx_top, log_ofReal_of_pos hx_pos, exp_coe, Real.exp_log hx_pos]

end LogExp

section Exp
namespace EReal

/-
**EReal.exp_nmul** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：exp_nmul (x : EReal) (n : Nat) : exp (n * x) = (exp x) ^ n
参数：x : EReal；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.log_pow`：log_pow {x : Real>=0∞} {n : Nat} : log (x ^ n) = n * lo
g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `EReal.log_exp`：∀ (x : EReal), x.exp.log = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exp_nmul (x : EReal) (n : ℕ) : exp (n * x) = (exp x) ^ n := by
  simp_rw [← log_eq_iff, log_pow, log_exp]
/-
**EReal.exp_mul** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：exp_mul (x : EReal) (y : Real) : exp (x * y) = (exp x) ^ y
参数：x : EReal；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.log_eq_iff`：log_eq_iff {x y : Real>=0∞} : log x = log y ↔ x = y
· 使用定理 `ENNReal.log_rpow`：log_rpow {x : Real>=0∞} {y : Real} : log (x ^ y) = y *
 log x
· 使用定理 `EReal.log_exp`：∀ (x : EReal), x.exp.log = x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma exp_mul (x : EReal) (y : ℝ) : exp (x * y) = (exp x) ^ y := by
  rw [← log_eq_iff, log_rpow, log_exp, log_exp, mul_comm]

end EReal
end Exp

namespace ENNReal

/-
**ENNReal.rpow_eq_exp_mul_log** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：rpow_eq_exp_mul_log (x : Real>=0∞) (y : Real) : x ^ y = exp (y * log x)
参数：x : Real>=0∞；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.log_rpow`：log_rpow {x : Real>=0∞} {y : Real} : log (x ^ y) = y *
 log x
· 使用定理 `ENNReal.exp_log`：∀ (x : ENNReal), x.log.exp = x
-/
lemma rpow_eq_exp_mul_log (x : ℝ≥0∞) (y : ℝ) : x ^ y = exp (y * log x) := by
  rw [← log_rpow, exp_log]

@[deprecated (since := "2026-07-15")] alias _root_.EReal.ENNReal.rpow_eq_exp_mul_log :=
  rpow_eq_exp_mul_log

section OrderIso

set_option backward.isDefEq.respectTransparency false in
/-- `ENNReal.log` and its inverse `EReal.exp` are an order isomorphism between `ℝ≥0∞` and
`EReal`. -/
noncomputable
/-
**ENNReal.logOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：logOrderIso : Real>=0∞ ≃o EReal where toFun
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.exp_log`：∀ (x : ENNReal), x.log.exp = x
· 使用定理 `EReal.log_exp`：∀ (x : EReal), x.exp.log = x
-/
def logOrderIso : ℝ≥0∞ ≃o EReal where
  toFun := log
  invFun := exp
  left_inv x := exp_log x
  right_inv x := log_exp x
  map_rel_iff' := by simp only [Equiv.coe_fn_mk, log_le_log_iff, forall_const]
/-
**ENNReal.logOrderIso_apply** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (x : ENNReal), ENNReal.logOrderIso x = x.log
参数：x : ENNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma logOrderIso_apply (x : ℝ≥0∞) : logOrderIso x = log x := rfl

/-- `EReal.exp` and its inverse `ENNReal.log` are an order isomorphism between `EReal` and
`ℝ≥0∞`. -/
noncomputable
/-
**ENNReal._root_.EReal.expOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.EReal.expOrderIso := logOrderIso.symm
/-
**ENNReal._root_.EReal.expOrderIso_apply** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.EReal.expOrderIso_apply (x : EReal) : expOrderIso x = exp x := rfl
/-
**ENNReal.logOrderIso_symm** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ENNReal.logOrderIso.symm = EReal.expOrderIso
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma logOrderIso_symm : logOrderIso.symm = expOrderIso := rfl
/-
**ENNReal._root_.EReal.expOrderIso_symm** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.EReal.expOrderIso_symm : expOrderIso.symm = logOrderIso := rfl

end OrderIso

section Continuity

/-- `log` as a homeomorphism. -/
/-
**ENNReal.logHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：logHomeomorph : Real>=0∞ ≃ₜ EReal
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal

--- 原说明 ---
`log` as a homeomorphism.
-/
noncomputable def logHomeomorph : ℝ≥0∞ ≃ₜ EReal := logOrderIso.toHomeomorph
/-
**ENNReal.logHomeomorph_apply** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (x : ENNReal), ENNReal.logHomeomorph x = x.log
参数：x : ENNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma logHomeomorph_apply (x : ℝ≥0∞) : logHomeomorph x = log x := rfl

/-- `exp` as a homeomorphism. -/
/-
**ENNReal._root_.EReal.expHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`exp` as a homeomorphism.
-/
noncomputable def _root_.EReal.expHomeomorph : EReal ≃ₜ ℝ≥0∞ := expOrderIso.toHomeomorph
/-
**ENNReal._root_.EReal.expHomeomorph_apply** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.EReal.expHomeomorph_apply (x : EReal) : expHomeomorph x = exp x := rfl
/-
**ENNReal.logHomeomorph_symm** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ENNReal.logHomeomorph.symm = EReal.expHomeomorph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma logHomeomorph_symm : logHomeomorph.symm = expHomeomorph := rfl
/-
**ENNReal._root_.EReal.expHomeomorph_symm** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.EReal.expHomeomorph_symm : expHomeomorph.symm = logHomeomorph := rfl

@[continuity, fun_prop]
/-
**ENNReal.continuous_log** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：continuous_log : Continuous log
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.continuous`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α]
 [inst_1 : Preorder β] [inst_2 : TopologicalSpace α]   [inst_3 : TopologicalSpac
e β] [Ord…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
-/
lemma continuous_log : Continuous log := logOrderIso.continuous

@[continuity, fun_prop]
/-
**ENNReal.continuous_exp** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：continuous_exp : Continuous exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.continuous`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α]
 [inst_1 : Preorder β] [inst_2 : TopologicalSpace α]   [inst_3 : TopologicalSpac
e β] [Ord…
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
-/
lemma continuous_exp : Continuous exp := expOrderIso.continuous
/-
**ENNReal._root_.EReal.tendsto_exp_nhds_top_nhds_top** 是 Mathlib 中的一个引理，位于命名空间 `
ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.EReal.tendsto_exp_nhds_top_nhds_top : Filter.Tendsto exp (𝓝 ⊤) (𝓝 ⊤) :=
  continuous_exp.tendsto ⊤
/-
**ENNReal._root_.EReal.tendsto_exp_nhds_zero_nhds_one** 是 Mathlib 中的一个引理，位于命名空间 
`ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.EReal.tendsto_exp_nhds_zero_nhds_one : Filter.Tendsto exp (𝓝 0) (𝓝 1) := by
  convert! continuous_exp.tendsto 0
  simp
/-
**ENNReal._root_.EReal.tendsto_exp_nhds_bot_nhds_zero** 是 Mathlib 中的一个引理，位于命名空间 
`ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.EReal.tendsto_exp_nhds_bot_nhds_zero : Filter.Tendsto exp (𝓝 ⊥) (𝓝 0) :=
  continuous_exp.tendsto ⊥
/-
**ENNReal.tendsto_rpow_atTop_of_one_lt_base** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_rpow_atTop_of_one_lt_base {b : Real>=0∞} (hb : 1 < b) : Filter.Ten
dsto (b ^ · : Real -> Real>=0∞) Filter.atTop (𝓝 ⊤)
参数：hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ENNReal.rpow_eq_exp_mul_log`：rpow_eq_exp_mul_log (x : Real>=0∞) (y : Rea
l) : x ^ y = exp (y * log x)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `EReal.tendsto_exp_nhds_top_nhds_top`：Filter.Tendsto EReal.exp (nhds ⊤) (
nhds ⊤)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.top_mul_of_pos`：top_mul_of_pos {x : EReal} (h : 0 < x) : ⊤ * x = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.zero_lt_log_iff`：∀ {x : ENNReal}, 0 < x.log ↔ 1 < x
· 使用定理 `EReal.Tendsto.mul_const`：∀ {α : Type u_2} {f : Filter α} {m : α → EReal}
 {a b : EReal},   Filter.Tendsto m f (nhds a) → a ≠ 0 ∨ b ≠ ⊥ → a ≠ 0 ∨ b ≠ ⊤ → 
Filter.Tendst…
· 使用引理 `EReal.tendsto_coe_atTop`：tendsto_coe_atTop : Tendsto Real.toEReal atTop 
(𝓝 ⊤)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma tendsto_rpow_atTop_of_one_lt_base {b : ℝ≥0∞} (hb : 1 < b) :
    Filter.Tendsto (b ^ · : ℝ → ℝ≥0∞) Filter.atTop (𝓝 ⊤) := by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_top_nhds_top.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atTop _ _
  · rw [EReal.top_mul_of_pos (zero_lt_log_iff.2 hb)]
  all_goals simp
/-
**ENNReal.tendsto_rpow_atTop_of_base_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_rpow_atTop_of_base_lt_one {b : Real>=0∞} (hb : b < 1) : Filter.Ten
dsto (b ^ · : Real -> Real>=0∞) Filter.atTop (𝓝 0)
参数：hb : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ENNReal.rpow_eq_exp_mul_log`：rpow_eq_exp_mul_log (x : Real>=0∞) (y : Rea
l) : x ^ y = exp (y * log x)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `EReal.tendsto_exp_nhds_bot_nhds_zero`：Filter.Tendsto EReal.exp (nhds ⊥) 
(nhds 0)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.top_mul_of_neg`：top_mul_of_neg {x : EReal} (h : x < 0) : ⊤ * x = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.log_lt_zero_iff`：∀ {x : ENNReal}, x.log < 0 ↔ x < 1
· 使用定理 `EReal.Tendsto.mul_const`：∀ {α : Type u_2} {f : Filter α} {m : α → EReal}
 {a b : EReal},   Filter.Tendsto m f (nhds a) → a ≠ 0 ∨ b ≠ ⊥ → a ≠ 0 ∨ b ≠ ⊤ → 
Filter.Tendst…
· 使用引理 `EReal.tendsto_coe_atTop`：tendsto_coe_atTop : Tendsto Real.toEReal atTop 
(𝓝 ⊤)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma tendsto_rpow_atTop_of_base_lt_one {b : ℝ≥0∞} (hb : b < 1) :
    Filter.Tendsto (b ^ · : ℝ → ℝ≥0∞) Filter.atTop (𝓝 0) := by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_bot_nhds_zero.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atTop _ _
  · rw [EReal.top_mul_of_neg (log_lt_zero_iff.2 hb)]
  all_goals simp
/-
**ENNReal.tendsto_rpow_atBot_of_one_lt_base** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_rpow_atBot_of_one_lt_base {b : Real>=0∞} (hb : 1 < b) : Filter.Ten
dsto (b ^ · : Real -> Real>=0∞) Filter.atBot (𝓝 0)
参数：hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ENNReal.rpow_eq_exp_mul_log`：rpow_eq_exp_mul_log (x : Real>=0∞) (y : Rea
l) : x ^ y = exp (y * log x)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `EReal.tendsto_exp_nhds_bot_nhds_zero`：Filter.Tendsto EReal.exp (nhds ⊥) 
(nhds 0)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.bot_mul_of_pos`：bot_mul_of_pos {x : EReal} (h : 0 < x) : ⊥ * x = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.zero_lt_log_iff`：∀ {x : ENNReal}, 0 < x.log ↔ 1 < x
· 使用定理 `EReal.Tendsto.mul_const`：∀ {α : Type u_2} {f : Filter α} {m : α → EReal}
 {a b : EReal},   Filter.Tendsto m f (nhds a) → a ≠ 0 ∨ b ≠ ⊥ → a ≠ 0 ∨ b ≠ ⊤ → 
Filter.Tendst…
· 使用引理 `EReal.tendsto_coe_atBot`：tendsto_coe_atBot : Tendsto Real.toEReal atBot 
(𝓝 ⊥)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma tendsto_rpow_atBot_of_one_lt_base {b : ℝ≥0∞} (hb : 1 < b) :
    Filter.Tendsto (b ^ · : ℝ → ℝ≥0∞) Filter.atBot (𝓝 0) := by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_bot_nhds_zero.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atBot _ _
  · rw [EReal.bot_mul_of_pos (zero_lt_log_iff.2 hb)]
  all_goals simp
/-
**ENNReal.tendsto_rpow_atBot_of_base_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：tendsto_rpow_atBot_of_base_lt_one {b : Real>=0∞} (hb : b < 1) : Filter.Ten
dsto (b ^ · : Real -> Real>=0∞) Filter.atBot (𝓝 ⊤)
参数：hb : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ENNReal.rpow_eq_exp_mul_log`：rpow_eq_exp_mul_log (x : Real>=0∞) (y : Rea
l) : x ^ y = exp (y * log x)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `EReal.tendsto_exp_nhds_top_nhds_top`：Filter.Tendsto EReal.exp (nhds ⊤) (
nhds ⊤)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.bot_mul_of_neg`：bot_mul_of_neg {x : EReal} (h : x < 0) : ⊥ * x = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.log_lt_zero_iff`：∀ {x : ENNReal}, x.log < 0 ↔ x < 1
· 使用定理 `EReal.Tendsto.mul_const`：∀ {α : Type u_2} {f : Filter α} {m : α → EReal}
 {a b : EReal},   Filter.Tendsto m f (nhds a) → a ≠ 0 ∨ b ≠ ⊥ → a ≠ 0 ∨ b ≠ ⊤ → 
Filter.Tendst…
· 使用引理 `EReal.tendsto_coe_atBot`：tendsto_coe_atBot : Tendsto Real.toEReal atBot 
(𝓝 ⊥)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma tendsto_rpow_atBot_of_base_lt_one {b : ℝ≥0∞} (hb : b < 1) :
    Filter.Tendsto (b ^ · : ℝ → ℝ≥0∞) Filter.atBot (𝓝 ⊤) := by
  simp_rw [ENNReal.rpow_eq_exp_mul_log]
  refine EReal.tendsto_exp_nhds_top_nhds_top.comp ?_
  convert! EReal.Tendsto.mul_const tendsto_coe_atBot _ _
  · rw [EReal.bot_mul_of_neg (log_lt_zero_iff.2 hb)]
  all_goals simp

end Continuity

section Measurability

@[fun_prop]
/-
**ENNReal.measurable_log** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：measurable_log : Measurable log
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `ENNReal.continuous_log`：continuous_log : Continuous log
-/
lemma measurable_log : Measurable log := continuous_log.measurable

@[fun_prop]
/-
**ENNReal._root_.EReal.measurable_exp** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.EReal.measurable_exp : Measurable exp := continuous_exp.measurable

@[fun_prop]
/-
**ENNReal._root_.Measurable.ennreal_log** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Measurable.ennreal_log {α : Type*} {_ : MeasurableSpace α}
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x ↦ log (f x) := measurable_log.comp hf

@[fun_prop]
/-
**ENNReal._root_.Measurable.ereal_exp** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Measurable.ereal_exp {α : Type*} {_ : MeasurableSpace α}
    {f : α → EReal} (hf : Measurable f) :
    Measurable fun x ↦ exp (f x) := measurable_exp.comp hf

end Measurability

end ENNReal

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PolishSpace EReal := ENNReal.logOrderIso.symm.toHomeomorph.isClosedEmbedding.polishSpace
