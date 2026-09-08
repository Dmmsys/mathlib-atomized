/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Sequences

/-!
# Continuity of the norm on (semi)normed groups

## Tags

normed group
-/

public section

variable {α ι κ E F G : Type*}

open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G]

open Finset

section ContinuousENorm

variable {E : Type*} [TopologicalSpace E] [ContinuousENorm E]

@[continuity, fun_prop]
/-
**continuous_enorm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_enorm : Continuous fun a : E => ‖a‖ₑ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousENorm.continuous_enorm`：∀ {E : Type u_8} {inst : TopologicalSp
ace E} [self : ContinuousENorm E], Continuous enorm
-/
lemma continuous_enorm : Continuous fun a : E ↦ ‖a‖ₑ := ContinuousENorm.continuous_enorm

variable {X : Type*} [TopologicalSpace X] {f : X → E} {s : Set X} {a : X}

@[fun_prop]
/-
**Continuous.enorm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.enorm : Continuous f -> Continuous (‖f ·‖ₑ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用引理 `continuous_enorm`：continuous_enorm : Continuous fun a : E => ‖a‖ₑ
-/
lemma Continuous.enorm : Continuous f → Continuous (‖f ·‖ₑ) :=
  continuous_enorm.comp
/-
**ContinuousAt.enorm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.enorm {a : X} (h : ContinuousAt f a) : ContinuousAt (‖f ·‖ₑ) 
a
参数：h : ContinuousAt f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp'`：ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : Contin
uousAt g (f x)) (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用引理 `Continuous.enorm`：Continuous.enorm : Continuous f -> Continuous (‖f ·‖ₑ)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
-/
lemma ContinuousAt.enorm {a : X} (h : ContinuousAt f a) : ContinuousAt (‖f ·‖ₑ) a := by fun_prop

@[fun_prop]
/-
**ContinuousWithinAt.enorm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.enorm {s : Set X} {a : X} (h : ContinuousWithinAt f s a
) : ContinuousWithinAt (‖f ·‖ₑ) s a
参数：h : ContinuousWithinAt f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `ContinuousENorm.continuous_enorm`：∀ {E : Type u_8} {inst : TopologicalSp
ace E} [self : ContinuousENorm E], Continuous enorm
-/
lemma ContinuousWithinAt.enorm {s : Set X} {a : X} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (‖f ·‖ₑ) s a :=
  (ContinuousENorm.continuous_enorm.continuousWithinAt).comp (t := Set.univ) h
    (fun _ _ ↦ by trivial)

@[fun_prop]
/-
**ContinuousOn.enorm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.enorm (h : ContinuousOn f s) : ContinuousOn (‖f ·‖ₑ) s
参数：h : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousENorm.continuous_enorm`：∀ {E : Type u_8} {inst : TopologicalSp
ace E} [self : ContinuousENorm E], Continuous enorm
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
lemma ContinuousOn.enorm (h : ContinuousOn f s) : ContinuousOn (‖f ·‖ₑ) s :=
  (ContinuousENorm.continuous_enorm.continuousOn).comp (t := Set.univ) h <| Set.mapsTo_univ _ _

end ContinuousENorm

@[to_additive]
/-
**tendsto_iff_norm_inv_mul_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_iff_norm_inv_mul_tendsto_zero {f : α -> E} {a : Filter α} {b : E} 
: Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖(f e)⁻¹ * b‖) a (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_iff_norm_inv_mul_tendsto_zero {f : α → E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖(f e)⁻¹ * b‖) a (𝓝 0) := by
  simp only [← dist_eq_norm_inv_mul, ← tendsto_iff_dist_tendsto_zero]

@[to_additive]
/-
**tendsto_one_iff_norm_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_one_iff_norm_tendsto_zero {f : α -> E} {a : Filter α} : Tendsto f 
a (𝓝 1) ↔ Tendsto (‖f ·‖) a (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `tendsto_iff_norm_inv_mul_tendsto_zero`：tendsto_iff_norm_inv_mul_tendsto_
zero {f : α -> E} {a : Filter α} {b : E} : Tendsto f a (𝓝 b) ↔ Tendsto (fun e =>
 ‖(f e)⁻¹ * b‖) a (𝓝 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_one_iff_norm_tendsto_zero {f : α → E} {a : Filter α} :
    Tendsto f a (𝓝 1) ↔ Tendsto (‖f ·‖) a (𝓝 0) :=
  tendsto_iff_norm_inv_mul_tendsto_zero.trans <| by simp

@[to_additive]
/-
**tendsto_iff_enorm_inv_mul_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_iff_enorm_inv_mul_tendsto_zero {f : α -> E} {a : Filter α} {b : E}
 : Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖(f e)⁻¹ * b‖ₑ) a (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_iff_enorm_inv_mul_tendsto_zero {f : α → E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖(f e)⁻¹ * b‖ₑ) a (𝓝 0) := by
  simp only [← edist_eq_enorm_inv_mul, ← tendsto_iff_edist_tendsto_0]

@[to_additive]
/-
**tendsto_one_iff_enorm_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_one_iff_enorm_tendsto_zero {f : α -> E} {a : Filter α} : Tendsto f
 a (𝓝 1) ↔ Tendsto (‖f ·‖ₑ) a (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `tendsto_iff_enorm_inv_mul_tendsto_zero`：tendsto_iff_enorm_inv_mul_tendst
o_zero {f : α -> E} {a : Filter α} {b : E} : Tendsto f a (𝓝 b) ↔ Tendsto (fun e 
=> ‖(f e)⁻¹ * b‖ₑ) a (𝓝 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `enorm_inv'`：enorm_inv' (a : E) : ‖a⁻¹‖ₑ = ‖a‖ₑ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_one_iff_enorm_tendsto_zero {f : α → E} {a : Filter α} :
    Tendsto f a (𝓝 1) ↔ Tendsto (‖f ·‖ₑ) a (𝓝 0) :=
  tendsto_iff_enorm_inv_mul_tendsto_zero.trans <| by simp

@[to_additive (attr := simp 1100)]
/-
**comap_norm_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_norm_nhds_one : comap norm (𝓝 0) = 𝓝 (1 : E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `nhds_comap_dist`：nhds_comap_dist (a : α) : ((𝓝 (0 : Real)).comap (dist ·
 a)) = 𝓝 a
-/
theorem comap_norm_nhds_one : comap norm (𝓝 0) = 𝓝 (1 : E) := by
  simpa only [dist_one_right] using nhds_comap_dist (1 : E)

/-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a real
function `a` which tends to `0`, then `f` tends to `1` (neutral element of `SeminormedGroup`).
In this pair of lemmas (`squeeze_one_norm'` and `squeeze_one_norm`), following a convention of
similar lemmas in `Topology.MetricSpace.Basic` and `Topology.Algebra.Order`, the `'` version is
phrased using "eventually" and the non-`'` version is phrased absolutely. -/
@[to_additive /-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by
a real function `a` which tends to `0`, then `f` tends to `0`. In this pair of lemmas
(`squeeze_zero_norm'` and `squeeze_zero_norm`), following a convention of similar lemmas in
`Topology.MetricSpace.Pseudo.Defs` and `Topology.Algebra.Order`, the `'` version is phrased using
"eventually" and the non-`'` version is phrased absolutely. -/]
/-
**squeeze_one_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：squeeze_one_norm' {f : α -> E} {a : α -> Real} {t₀ : Filter α} (h : forall
ᶠ n in t₀, ‖f n‖ <= a n) (h' : Tendsto a t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 1)
参数：h : forallᶠ n in t₀, ‖f n‖ <= a n；h' : Tendsto a t₀ (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_one_iff_norm_tendsto_zero`：tendsto_one_iff_norm_tendsto_zero {f 
: α -> E} {a : Filter α} : Tendsto f a (𝓝 1) ↔ Tendsto (‖f ·‖) a (𝓝 0)
· 使用引理 `squeeze_zero'`：squeeze_zero' {α} {f g : α -> Real} {t₀ : Filter α} (hf :
 forallᶠ t in t₀, 0 <= f t) (hft : forallᶠ t in t₀, f t <= g t) (g0 : Tendsto g 
t₀ …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
-/
theorem squeeze_one_norm' {f : α → E} {a : α → ℝ} {t₀ : Filter α} (h : ∀ᶠ n in t₀, ‖f n‖ ≤ a n)
    (h' : Tendsto a t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 1) :=
  tendsto_one_iff_norm_tendsto_zero.2 <|
    squeeze_zero' (Eventually.of_forall fun _n => norm_nonneg' _) h h'

/-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real function `a` which
tends to `0`, then `f` tends to `1`. -/
@[to_additive /-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real
function `a` which tends to `0`, then `f` tends to `0`. -/]
/-
**squeeze_one_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：squeeze_one_norm {f : α -> E} {a : α -> Real} {t₀ : Filter α} (h : forall 
n, ‖f n‖ <= a n) : Tendsto a t₀ (𝓝 0) -> Tendsto f t₀ (𝓝 1)
参数：h : forall n, ‖f n‖ <= a n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `squeeze_one_norm'`：squeeze_one_norm' {f : α -> E} {a : α -> Real} {t₀ : 
Filter α} (h : forallᶠ n in t₀, ‖f n‖ <= a n) (h' : Tendsto a t₀ (𝓝 0)) : Tendst
o f t₀ …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem squeeze_one_norm {f : α → E} {a : α → ℝ} {t₀ : Filter α} (h : ∀ n, ‖f n‖ ≤ a n) :
    Tendsto a t₀ (𝓝 0) → Tendsto f t₀ (𝓝 1) :=
  squeeze_one_norm' <| Eventually.of_forall h

@[to_additive]
/-
**tendsto_norm_inv_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_norm_inv_mul_self (x : E) : Tendsto (fun a => ‖a⁻¹ * x‖) (𝓝 x) (𝓝 
0)
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `Filter.Tendsto.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetri
cSpace α] {f g : β → α} {x : Filter β} {a b : α},   Filter.Tendsto f x (nhds a) 
→     Fil…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem tendsto_norm_inv_mul_self (x : E) : Tendsto (fun a => ‖a⁻¹ * x‖) (𝓝 x) (𝓝 0) := by
  simpa [dist_eq_norm_inv_mul] using
    tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (x : E)) (𝓝 x) _)

@[to_additive]
/-
**tendsto_norm_inv_mul_self_nhdsGE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_norm_inv_mul_self_nhdsGE (x : E) : Tendsto (fun a => ‖a⁻¹ * x‖) (𝓝
 x) (𝓝[>=] 0)
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `tendsto_norm_inv_mul_self`：tendsto_norm_inv_mul_self (x : E) : Tendsto (
fun a => ‖a⁻¹ * x‖) (𝓝 x) (𝓝 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem tendsto_norm_inv_mul_self_nhdsGE (x : E) : Tendsto (fun a ↦ ‖a⁻¹ * x‖) (𝓝 x) (𝓝[≥] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_norm_inv_mul_self x, by simp⟩

@[to_additive tendsto_norm]
/-
**tendsto_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_norm' {x : E} : Tendsto (fun a => ‖a‖) (𝓝 x) (𝓝 ‖x‖)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `Filter.Tendsto.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetri
cSpace α] {f g : β → α} {x : Filter β} {a b : α},   Filter.Tendsto f x (nhds a) 
→     Fil…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem tendsto_norm' {x : E} : Tendsto (fun a => ‖a‖) (𝓝 x) (𝓝 ‖x‖) := by
  simpa using tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (1 : E)) _ _)

/-- See `tendsto_norm_one` for a version with pointed neighborhoods. -/
@[to_additive /-- See `tendsto_norm_zero` for a version with pointed neighborhoods. -/]
/-
**tendsto_norm_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_norm_one : Tendsto (fun a : E => ‖a‖) (𝓝 1) (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `tendsto_norm_inv_mul_self`：tendsto_norm_inv_mul_self (x : E) : Tendsto (
fun a => ‖a⁻¹ * x‖) (𝓝 x) (𝓝 0)

--- 原说明 ---
See `tendsto_norm_one` for a version with pointed neighborhoods.
-/
theorem tendsto_norm_one : Tendsto (fun a : E => ‖a‖) (𝓝 1) (𝓝 0) := by
  simpa using tendsto_norm_inv_mul_self (1 : E)

@[to_additive (attr := continuity, fun_prop) continuous_norm]
/-
**continuous_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_norm' : Continuous fun a : E => ‖a‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem continuous_norm' : Continuous fun a : E => ‖a‖ := by
  simpa using continuous_id.dist (continuous_const : Continuous fun _a => (1 : E))

@[to_additive (attr := continuity, fun_prop) continuous_nnnorm]
/-
**continuous_nnnorm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_nnnorm' : Continuous fun a : E => ‖a‖₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `continuous_norm'`：continuous_norm' : Continuous fun a : E => ‖a‖
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
-/
theorem continuous_nnnorm' : Continuous fun a : E => ‖a‖₊ :=
  continuous_norm'.subtype_mk _

end SeminormedGroup

section Instances

@[to_additive]
/-
**SeminormedGroup.toContinuousENorm** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SeminormedGroup.toContinuousENorm [SeminormedGroup E] : ContinuousENorm E 
where continuous_enorm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SeminormedGroup.toContinuousENorm [SeminormedGroup E] : ContinuousENorm E where
  continuous_enorm := ENNReal.isOpenEmbedding_coe.continuous.comp continuous_nnnorm'

@[to_additive]
/-
**NormedGroup.toENormedMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NormedGroup.toENormedMonoid {F : Type*} [NormedGroup F] : ENormedMonoid F 
where enorm_zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance NormedGroup.toENormedMonoid {F : Type*} [NormedGroup F] : ENormedMonoid F where
  enorm_zero := by simp [enorm_eq_nnnorm]
  enorm_eq_zero := by simp [enorm_eq_nnnorm]
  enorm_mul_le := by simp [enorm_eq_nnnorm, ← coe_add, nnnorm_mul_le']

@[to_additive]
/-
**NormedCommGroup.toENormedCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NormedCommGroup.toENormedCommMonoid [NormedCommGroup E] : ENormedCommMonoi
d E where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance NormedCommGroup.toENormedCommMonoid [NormedCommGroup E] : ENormedCommMonoid E where
  __ := NormedGroup.toENormedMonoid
  __ := ‹NormedCommGroup E›

end Instances

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E} {a : E}

set_option linter.docPrime false in
@[to_additive Inseparable.norm_eq_norm]
/-
**Inseparable.norm_eq_norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Inseparable.norm_eq_norm' {u v : E} (h : Inseparable u v) : ‖u‖ = ‖v‖
参数：h : Inseparable u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Inseparable.map`：map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y
· 使用定理 `continuous_norm'`：continuous_norm' : Continuous fun a : E => ‖a‖
-/
theorem Inseparable.norm_eq_norm' {u v : E} (h : Inseparable u v) : ‖u‖ = ‖v‖ :=
  h.map continuous_norm' |>.eq

set_option linter.docPrime false in
@[to_additive Inseparable.nnnorm_eq_nnnorm]
/-
**Inseparable.nnnorm_eq_nnnorm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Inseparable.nnnorm_eq_nnnorm' {u v : E} (h : Inseparable u v) : ‖u‖₊ = ‖v‖
₊
参数：h : Inseparable u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `Inseparable.map`：map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y
· 使用定理 `continuous_nnnorm'`：continuous_nnnorm' : Continuous fun a : E => ‖a‖₊
-/
theorem Inseparable.nnnorm_eq_nnnorm' {u v : E} (h : Inseparable u v) : ‖u‖₊ = ‖v‖₊ :=
  h.map continuous_nnnorm' |>.eq
/-
**Inseparable.enorm_eq_enorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Inseparable.enorm_eq_enorm {E : Type*} [TopologicalSpace E] [ContinuousENo
rm E] {u v : E} (h : Inseparable u v) : ‖u‖ₑ = ‖v‖ₑ
参数：h : Inseparable u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `ENNReal.instT4Space`：T4Space ENNReal
· 使用定理 `Inseparable.map`：map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y
· 使用引理 `continuous_enorm`：continuous_enorm : Continuous fun a : E => ‖a‖ₑ
-/
theorem Inseparable.enorm_eq_enorm {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {u v : E} (h : Inseparable u v) : ‖u‖ₑ = ‖v‖ₑ :=
  h.map continuous_enorm |>.eq

@[to_additive]
/-
**mem_closure_one_iff_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_one_iff_norm {x : E} : x in closure ({1} : Set E) ↔ ‖x‖ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Metric.closedBall_zero'`：closedBall_zero' (x : α) : closedBall x 0 = clo
sure {x}
· 使用定理 `mem_closedBall_one_iff`：mem_closedBall_one_iff : a in closedBall (1 : E)
 r ↔ ‖a‖ <= r
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closure_one_iff_norm {x : E} : x ∈ closure ({1} : Set E) ↔ ‖x‖ = 0 := by
  rw [← closedBall_zero', mem_closedBall_one_iff, (norm_nonneg' x).ge_iff_eq']

@[to_additive]
/-
**closure_one_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_one_eq : closure ({1} : Set E) = { x | ‖x‖ = 0 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `mem_closure_one_iff_norm`：mem_closure_one_iff_norm {x : E} : x in closur
e ({1} : Set E) ↔ ‖x‖ = 0
-/
theorem closure_one_eq : closure ({1} : Set E) = { x | ‖x‖ = 0 } :=
  Set.ext fun _x => mem_closure_one_iff_norm

section

variable {l : Filter α} {f : α → E}

@[to_additive Filter.Tendsto.norm]
/-
**Filter.Tendsto.norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.norm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ‖f x‖) l 
(𝓝 ‖a‖)
参数：h : Tendsto f l (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_norm'`：tendsto_norm' {x : E} : Tendsto (fun a => ‖a‖) (𝓝 x) (𝓝 ‖
x‖)
-/
theorem Filter.Tendsto.norm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ‖f x‖) l (𝓝 ‖a‖) :=
  tendsto_norm'.comp h

@[to_additive Filter.Tendsto.nnnorm]
/-
**Filter.Tendsto.nnnorm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.nnnorm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ‖f x‖₊)
 l (𝓝 ‖a‖₊)
参数：h : Tendsto f l (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_nnnorm'`：continuous_nnnorm' : Continuous fun a : E => ‖a‖₊
-/
theorem Filter.Tendsto.nnnorm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ‖f x‖₊) l (𝓝 ‖a‖₊) :=
  Tendsto.comp continuous_nnnorm'.continuousAt h


end

section

variable [TopologicalSpace α] {f : α → E} {s : Set α} {a : α}

@[to_additive (attr := fun_prop) Continuous.norm]
/-
**Continuous.norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.norm' : Continuous f -> Continuous fun x => ‖f x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_norm'`：continuous_norm' : Continuous fun a : E => ‖a‖
-/
theorem Continuous.norm' : Continuous f → Continuous fun x => ‖f x‖ :=
  continuous_norm'.comp

@[to_additive (attr := fun_prop) Continuous.nnnorm]
/-
**Continuous.nnnorm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.nnnorm' : Continuous f -> Continuous fun x => ‖f x‖₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_nnnorm'`：continuous_nnnorm' : Continuous fun a : E => ‖a‖₊
-/
theorem Continuous.nnnorm' : Continuous f → Continuous fun x => ‖f x‖₊ :=
  continuous_nnnorm'.comp

end
end SeminormedGroup

section ContinuousENorm

variable [TopologicalSpace E] [ContinuousENorm E] {a : E} {l : Filter α} {f : α → E}

/-
**Filter.Tendsto.enorm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.enorm (h : Tendsto f l (𝓝 a)) : Tendsto (‖f ·‖ₑ) l (𝓝 ‖a‖ₑ)
参数：h : Tendsto f l (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用引理 `continuous_enorm`：continuous_enorm : Continuous fun a : E => ‖a‖ₑ
-/
lemma Filter.Tendsto.enorm (h : Tendsto f l (𝓝 a)) : Tendsto (‖f ·‖ₑ) l (𝓝 ‖a‖ₑ) :=
  .comp continuous_enorm.continuousAt h

end ContinuousENorm

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E} {a : E}

section

variable [TopologicalSpace α] {f : α → E} {s : Set α} {a : α}

@[to_additive (attr := fun_prop) ContinuousAt.norm]
/-
**ContinuousAt.norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.norm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x =>
 ‖f x‖) a
参数：h : ContinuousAt f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.norm'`：Filter.Tendsto.norm' (h : Tendsto f l (𝓝 a)) : Ten
dsto (fun x => ‖f x‖) l (𝓝 ‖a‖)
-/
theorem ContinuousAt.norm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x => ‖f x‖) a :=
  Tendsto.norm' h

@[to_additive (attr := fun_prop) ContinuousAt.nnnorm]
/-
**ContinuousAt.nnnorm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.nnnorm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x 
=> ‖f x‖₊) a
参数：h : ContinuousAt f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.nnnorm'`：Filter.Tendsto.nnnorm' (h : Tendsto f l (𝓝 a)) :
 Tendsto (fun x => ‖f x‖₊) l (𝓝 ‖a‖₊)
-/
theorem ContinuousAt.nnnorm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x => ‖f x‖₊) a :=
  Tendsto.nnnorm' h

@[to_additive ContinuousWithinAt.norm]
/-
**ContinuousWithinAt.norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.norm' {s : Set α} {a : α} (h : ContinuousWithinAt f s a
) : ContinuousWithinAt (fun x => ‖f x‖) s a
参数：h : ContinuousWithinAt f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.norm'`：Filter.Tendsto.norm' (h : Tendsto f l (𝓝 a)) : Ten
dsto (fun x => ‖f x‖) l (𝓝 ‖a‖)
-/
theorem ContinuousWithinAt.norm' {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => ‖f x‖) s a :=
  Tendsto.norm' h

@[to_additive ContinuousWithinAt.nnnorm]
/-
**ContinuousWithinAt.nnnorm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.nnnorm' {s : Set α} {a : α} (h : ContinuousWithinAt f s
 a) : ContinuousWithinAt (fun x => ‖f x‖₊) s a
参数：h : ContinuousWithinAt f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.nnnorm'`：Filter.Tendsto.nnnorm' (h : Tendsto f l (𝓝 a)) :
 Tendsto (fun x => ‖f x‖₊) l (𝓝 ‖a‖₊)
-/
theorem ContinuousWithinAt.nnnorm' {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => ‖f x‖₊) s a :=
  Tendsto.nnnorm' h

@[to_additive (attr := fun_prop) ContinuousOn.norm]
/-
**ContinuousOn.norm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.norm' {s : Set α} (h : ContinuousOn f s) : ContinuousOn (fun 
x => ‖f x‖) s
参数：h : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.norm'`：ContinuousWithinAt.norm' {s : Set α} {a : α} (
h : ContinuousWithinAt f s a) : ContinuousWithinAt (fun x => ‖f x‖) s a
-/
theorem ContinuousOn.norm' {s : Set α} (h : ContinuousOn f s) : ContinuousOn (fun x => ‖f x‖) s :=
  fun x hx => (h x hx).norm'

@[to_additive (attr := fun_prop) ContinuousOn.nnnorm]
/-
**ContinuousOn.nnnorm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.nnnorm' {s : Set α} (h : ContinuousOn f s) : ContinuousOn (fu
n x => ‖f x‖₊) s
参数：h : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.nnnorm'`：ContinuousWithinAt.nnnorm' {s : Set α} {a : 
α} (h : ContinuousWithinAt f s a) : ContinuousWithinAt (fun x => ‖f x‖₊) s a
-/
theorem ContinuousOn.nnnorm' {s : Set α} (h : ContinuousOn f s) :
    ContinuousOn (fun x => ‖f x‖₊) s := fun x hx => (h x hx).nnnorm'

end

/-- If `‖y‖ → ∞`, then we can assume `y ≠ x` for any fixed `x`. -/
@[to_additive eventually_ne_of_tendsto_norm_atTop /-- If `‖y‖→∞`, then we can assume `y≠x` for any
fixed `x` -/]
/-
**eventually_ne_of_tendsto_norm_atTop'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_ne_of_tendsto_norm_atTop' {l : Filter α} {f : α -> E} (h : Tend
sto (fun y => ‖f y‖) l atTop) (x : E) : forallᶠ y in l, f y != x
参数：h : Tendsto (fun y => ‖f y‖) l atTop；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually_ne_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
theorem eventually_ne_of_tendsto_norm_atTop' {l : Filter α} {f : α → E}
    (h : Tendsto (fun y => ‖f y‖) l atTop) (x : E) : ∀ᶠ y in l, f y ≠ x :=
  (h.eventually_ne_atTop _).mono fun _x => ne_of_apply_ne norm

@[to_additive]
/-
**SeminormedGroup.mem_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeminormedGroup.mem_closure_iff : a in closure s ↔ forall ε, 0 < ε -> exis
ts b in s, ‖a⁻¹ * b‖ < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem SeminormedGroup.mem_closure_iff :
    a ∈ closure s ↔ ∀ ε, 0 < ε → ∃ b ∈ s, ‖a⁻¹ * b‖ < ε := by
  simp [Metric.mem_closure_iff, dist_eq_norm_inv_mul]

@[to_additive]
/-
**SeminormedGroup.tendstoUniformlyOn_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeminormedGroup.tendstoUniformlyOn_one {f : ι -> κ -> G} {s : Set κ} {l : 
Filter ι} : TendstoUniformlyOn f 1 l s ↔ forall ε > 0, forallᶠ i in l, forall x 
in s, ‖f i x‖ < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `dist_one_left`：dist_one_left (a : E) : dist 1 a = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem SeminormedGroup.tendstoUniformlyOn_one {f : ι → κ → G} {s : Set κ} {l : Filter ι} :
    TendstoUniformlyOn f 1 l s ↔ ∀ ε > 0, ∀ᶠ i in l, ∀ x ∈ s, ‖f i x‖ < ε := by
  simp only [tendstoUniformlyOn_iff, Pi.one_apply, dist_one_left]

@[to_additive]
/-
**SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one** 是 
Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one 
{f : ι -> κ -> G} {l : Filter ι} {l' : Filter κ} : UniformCauchySeqOnFilter f l 
l' ↔ TendstoUniformlyOnFilter (fun n : ι × ι => fun z => (f n.fst z)⁻¹ * f n.snd
 z) 1 (l ×ˢ l) l'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_uniformity_iff`：Filter.HasBasis.mem_uniformity_iff {
p : β -> Prop} {s : β -> SetRel α α} (h : (𝓤 α).HasBasis p s) {t : SetRel α α} :
 t in 𝓤 α ↔ exists i, p …
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one {f : ι → κ → G}
    {l : Filter ι} {l' : Filter κ} :
    UniformCauchySeqOnFilter f l l' ↔ TendstoUniformlyOnFilter
      (fun n : ι × ι => fun z => (f n.fst z)⁻¹ * f n.snd z) 1 (l ×ˢ l) l' := by
  refine ⟨fun hf u hu => ?_, fun hf u hu => ?_⟩
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine
      (hf { p : G × G | dist p.fst p.snd < ε } <| dist_mem_uniformity hε).mono fun x hx =>
        H 1 ((f x.fst.fst x.snd)⁻¹ * f x.fst.snd x.snd) ?_
    simpa [dist_eq_norm_inv_mul, norm_div_rev] using hx
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine
      (hf { p : G × G | dist p.fst p.snd < ε } <| dist_mem_uniformity hε).mono fun x hx =>
        H (f x.fst.fst x.snd) (f x.fst.snd x.snd) ?_
    simpa [dist_eq_norm_inv_mul, norm_div_rev] using hx

@[to_additive]
/-
**SeminormedGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_one** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：SeminormedGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_one {f : ι -> κ 
-> G} {s : Set κ} {l : Filter ι} : UniformCauchySeqOn f l s ↔ TendstoUniformlyOn
 (fun n : ι × ι => fun z => (f n.fst z)⁻¹ * f n.snd z) 1 (l ×ˢ l) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`：tendstoUniformlyOn_iff_
tendstoUniformlyOnFilter : TendstoUniformlyOn F f p s ↔ TendstoUniformlyOnFilter
 F f p (𝓟 s)
· 使用定理 `uniformCauchySeqOn_iff_uniformCauchySeqOnFilter`：uniformCauchySeqOn_iff_
uniformCauchySeqOnFilter : UniformCauchySeqOn F p s ↔ UniformCauchySeqOnFilter F
 p (𝓟 s)
· 使用定理 `SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_on
e`：SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one {f 
: ι -> κ -> G} {l : Filter ι} {l' : Filter κ} : UniformCauchySe…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem SeminormedGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_one {f : ι → κ → G} {s : Set κ}
    {l : Filter ι} :
    UniformCauchySeqOn f l s ↔
      TendstoUniformlyOn (fun n : ι × ι => fun z => (f n.fst z)⁻¹ * f n.snd z) 1 (l ×ˢ l) s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter,
    uniformCauchySeqOn_iff_uniformCauchySeqOnFilter,
    SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one]

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a b : E} {r : ℝ}

@[to_additive]
/-
**tendsto_iff_norm_div_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_iff_norm_div_tendsto_zero {f : α -> E} {a : Filter α} {b : E} : Te
ndsto f a (𝓝 b) ↔ Tendsto (fun e => ‖f e / b‖) a (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_iff_norm_div_tendsto_zero {f : α → E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖f e / b‖) a (𝓝 0) := by
  simp only [← dist_eq_norm_div, ← tendsto_iff_dist_tendsto_zero]

@[to_additive]
/-
**tendsto_iff_enorm_div_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_iff_enorm_div_tendsto_zero {f : α -> E} {a : Filter α} {b : E} : T
endsto f a (𝓝 b) ↔ Tendsto (fun e => ‖f e / b‖ₑ) a (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_iff_enorm_div_tendsto_zero {f : α → E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖f e / b‖ₑ) a (𝓝 0) := by
  simp only [← edist_eq_enorm_div, ← tendsto_iff_edist_tendsto_0]

@[to_additive]
/-
**SeminormedCommGroup.mem_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeminormedCommGroup.mem_closure_iff {s : Set E} : a in closure s ↔ forall 
ε, 0 < ε -> exists b in s, ‖a / b‖ < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm_div`：dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem SeminormedCommGroup.mem_closure_iff {s : Set E} :
    a ∈ closure s ↔ ∀ ε, 0 < ε → ∃ b ∈ s, ‖a / b‖ < ε := by
  simp [Metric.mem_closure_iff, dist_eq_norm_div]

@[to_additive]
/-
**tendsto_norm_div_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_norm_div_self (x : E) : Tendsto (fun a => ‖a / x‖) (𝓝 x) (𝓝 0)
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm_div`：dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `Filter.Tendsto.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetri
cSpace α] {f g : β → α} {x : Filter β} {a b : α},   Filter.Tendsto f x (nhds a) 
→     Fil…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem tendsto_norm_div_self (x : E) : Tendsto (fun a => ‖a / x‖) (𝓝 x) (𝓝 0) := by
  simpa [dist_eq_norm_div] using
    tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (x : E)) (𝓝 x) _)

@[to_additive]
/-
**tendsto_norm_div_self_nhdsGE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_norm_div_self_nhdsGE (x : E) : Tendsto (fun a => ‖a / x‖) (𝓝 x) (𝓝
[>=] 0)
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `tendsto_norm_div_self`：tendsto_norm_div_self (x : E) : Tendsto (fun a =>
 ‖a / x‖) (𝓝 x) (𝓝 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem tendsto_norm_div_self_nhdsGE (x : E) : Tendsto (fun a ↦ ‖a / x‖) (𝓝 x) (𝓝[≥] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_norm_div_self x, by simp⟩

open Finset

@[to_additive]
/-
**controlled_prod_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：controlled_prod_of_mem_closure {s : Subgroup E} (hg : a in closure (s : Se
t E)) {b : Nat -> Real} (b_pos : forall n, 0 < b n) : exists v : Nat -> E, Tends
to (fun n => ∏ i in range (n + 1), v i) atTop (𝓝 a) ∧ (forall n, v n in s) ∧ ‖(v
 0)⁻¹ * a‖ < b 0 ∧ forall n, 0 < n -> ‖v n‖ < b n
参数：hg : a in closure (s : Set E)；b_pos : forall n, 0 < b n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_seq_limit`：mem_closure_iff_seq_limit [FrechetUrysohnSpac
e X] {s : Set X} {a : X} : a in closure s ↔ exists x : Nat -> X, (forall n : Nat
, x n in s) ∧ T…
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.tendsto_atTop'`：tendsto_atTop' : Tendsto f atTop l ↔ forall s in 
l, exists a, forall b, a <= b -> f b in s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_add_atTop_nat`：tendsto_add_atTop_nat (k : Nat) : Tendsto 
(fun a => a + k) atTop atTop
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `CauchySeq.subseq_mem`：CauchySeq.subseq_mem {V : Nat -> SetRel α α} (hV :
 forall n, V n in 𝓤 α) {u : Nat -> α} (hu : CauchySeq u) : exists φ : Nat -> Nat
, StrictMo…
· 使用定理 `Filter.Tendsto.cauchySeq`：Filter.Tendsto.cauchySeq [SemilatticeSup β] [N
onempty β] {f : β -> α} {x} (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
· 使用定理 `StrictMono.tendsto_atTop`：∀ {φ : ℕ → ℕ}, StrictMono φ → Filter.Tendsto φ
 Filter.atTop Filter.atTop
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Finset.prod_range_succ'`：∀ {M : Type u_4} [inst : CommMonoid M] (f : ℕ →
 M) (n : ℕ),   ∏ k ∈ Finset.range (n + 1), f k = (∏ k ∈ Finset.range n, f (k + 1
)) * f 0
· 使用定理 `Finset.prod_range_induction`：prod_range_induction (f s : Nat -> M) (base
 : s 0 = 1) (n : Nat) (step : forall k < n, s (k + 1) = s k * f k) : ∏ k in Fins
et.range n, f k =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
（共 50 条，此处仅展示前 30 条）
-/
theorem controlled_prod_of_mem_closure {s : Subgroup E} (hg : a ∈ closure (s : Set E)) {b : ℕ → ℝ}
    (b_pos : ∀ n, 0 < b n) :
    ∃ v : ℕ → E,
      Tendsto (fun n => ∏ i ∈ range (n + 1), v i) atTop (𝓝 a) ∧
        (∀ n, v n ∈ s) ∧ ‖(v 0)⁻¹ * a‖ < b 0 ∧ ∀ n, 0 < n → ‖v n‖ < b n := by
  obtain ⟨u : ℕ → E, u_in : ∀ n, u n ∈ s, lim_u : Tendsto u atTop (𝓝 a)⟩ :=
    mem_closure_iff_seq_limit.mp hg
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀, ‖(u n)⁻¹ * a‖ < b 0 :=
    haveI : { x | ‖x⁻¹ * a‖ < b 0 } ∈ 𝓝 a := by
      simp_rw [← dist_eq_norm_inv_mul]
      exact Metric.ball_mem_nhds _ (b_pos _)
    Filter.tendsto_atTop'.mp lim_u _ this
  set z : ℕ → E := fun n => u (n + n₀)
  have lim_z : Tendsto z atTop (𝓝 a) := lim_u.comp (tendsto_add_atTop_nat n₀)
  have mem_𝓤 : ∀ n, { p : E × E | ‖p.1⁻¹ * p.2‖ < b (n + 1) } ∈ 𝓤 E := fun n => by
    simpa [← dist_eq_norm_inv_mul] using Metric.dist_mem_uniformity (b_pos <| n + 1)
  obtain ⟨φ : ℕ → ℕ, φ_extr : StrictMono φ, hφ : ∀ n, ‖(z (φ (n + 1)))⁻¹ * z (φ n)‖ < b (n + 1)⟩ :=
    lim_z.cauchySeq.subseq_mem mem_𝓤
  set w : ℕ → E := z ∘ φ
  have hw : Tendsto w atTop (𝓝 a) := lim_z.comp φ_extr.tendsto_atTop
  set v : ℕ → E := fun i => if i = 0 then w 0 else (w (i - 1))⁻¹ * w i
  refine ⟨v, ?_, ?_, hn₀ _ (n₀.le_add_left _), ?_⟩
  · apply hw.congr (fun n ↦ ?_)
    rw [Finset.prod_range_succ']
    have : ∏ k ∈ range n, v (k + 1) = (v 0)⁻¹ * w n := by
      apply prod_range_induction _ _ (by simp [v]) _ (fun k hk ↦ ?_)
      simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, add_tsub_cancel_right, v]
      group
    simp [this]
  · rintro ⟨⟩
    · change w 0 ∈ s
      apply u_in
    · exact s.mul_mem (s.inv_mem (u_in _)) (u_in _)
  · intro l hl
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := Nat.exists_eq_succ_of_ne_zero hl.ne'
    rw [← norm_inv']
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right,
      mul_inv_rev, inv_inv, v]
    apply hφ

@[to_additive]
/-
**controlled_prod_of_mem_closure_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：controlled_prod_of_mem_closure_range {j : E ->* F} {b : F} (hb : b in clos
ure (j.range : Set F)) {f : Nat -> Real} (b_pos : forall n, 0 < f n) : exists a 
: Nat -> E, Tendsto (fun n => ∏ i in range (n + 1), j (a i)) atTop (𝓝 b) ∧ ‖(j (
a 0))⁻¹ * b‖ < f 0 ∧ forall n, 0 < n -> ‖j (a n)‖ < f n
参数：hb : b in closure (j.range : Set F)；b_pos : forall n, 0 < f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `controlled_prod_of_mem_closure`：controlled_prod_of_mem_closure {s : Subg
roup E} (hg : a in closure (s : Set E)) {b : Nat -> Real} (b_pos : forall n, 0 <
 b n) : exists v : N…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem controlled_prod_of_mem_closure_range {j : E →* F} {b : F}
    (hb : b ∈ closure (j.range : Set F)) {f : ℕ → ℝ} (b_pos : ∀ n, 0 < f n) :
    ∃ a : ℕ → E,
      Tendsto (fun n => ∏ i ∈ range (n + 1), j (a i)) atTop (𝓝 b) ∧
        ‖(j (a 0))⁻¹ * b‖ < f 0 ∧ ∀ n, 0 < n → ‖j (a n)‖ < f n := by
  obtain ⟨v, sum_v, v_in, hv₀, hv_pos⟩ := controlled_prod_of_mem_closure hb b_pos
  choose g hg using v_in
  exact
    ⟨g, by simpa [← hg] using sum_v, by simpa [hg 0] using hv₀,
      fun n hn => by simpa [hg] using hv_pos n hn⟩

end SeminormedCommGroup

section NormedGroup

variable [NormedGroup E] {a b : E}

/-- See `tendsto_norm_one` for a version with full neighborhoods. -/
@[to_additive /-- See `tendsto_norm_zero` for a version with full neighborhoods. -/]
/-
**tendsto_norm_nhdsNE_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_norm_nhdsNE_one : Tendsto (norm : E -> Real) (𝓝[!=] 1) (𝓝[>] 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `tendsto_norm_one`：tendsto_norm_one : Tendsto (fun a : E => ‖a‖) (𝓝 1) (𝓝
 0)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal_principal`：tendsto_principal_principal {f : α -
> β} {s : Set α} {t : Set β} : Tendsto f (𝓟 s) (𝓟 t) ↔ forall a in s, f a in t
· 使用引理 `norm_pos_iff'`：norm_pos_iff' : 0 < ‖a‖ ↔ a != 1

--- 原说明 ---
See `tendsto_norm_one` for a version with full neighborhoods.
-/
lemma tendsto_norm_nhdsNE_one : Tendsto (norm : E → ℝ) (𝓝[≠] 1) (𝓝[>] 0) :=
  tendsto_norm_one.inf <| tendsto_principal_principal.2 fun _ hx ↦ norm_pos_iff'.2 hx

@[to_additive]
/-
**tendsto_norm_inv_mul_self_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_norm_inv_mul_self_nhdsNE (a : E) : Tendsto (fun x => ‖x⁻¹ * a‖) (𝓝
[!=] a) (𝓝[>] 0)
参数：a : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `tendsto_norm_inv_mul_self`：tendsto_norm_inv_mul_self (x : E) : Tendsto (
fun a => ‖a⁻¹ * x‖) (𝓝 x) (𝓝 0)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal_principal`：tendsto_principal_principal {f : α -
> β} {s : Set α} {t : Set β} : Tendsto f (𝓟 s) (𝓟 t) ↔ forall a in s, f a in t
· 使用引理 `norm_pos_iff'`：norm_pos_iff' : 0 < ‖a‖ ↔ a != 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem tendsto_norm_inv_mul_self_nhdsNE (a : E) :
    Tendsto (fun x => ‖x⁻¹ * a‖) (𝓝[≠] a) (𝓝[>] 0) := by
  apply (tendsto_norm_inv_mul_self a).inf
  apply tendsto_principal_principal.2 (fun _x hx => norm_pos_iff'.2 ?_)
  simpa [inv_mul_eq_one] using hx

variable (E)

/-- In a normed group, the pullback under the norm of `𝓝[>] 0` is the punctured neighborhood
of `1`. -/
@[to_additive comap_norm_nhdsGT_zero
/-- In a normed additive group, the pullback under the norm of `𝓝[>] 0` is the punctured
neighborhood of `0`. -/]
/-
**comap_norm_nhdsGT_zero'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：comap_norm_nhdsGT_zero' : comap norm (𝓝[>] 0) = 𝓝[!=] (1 : E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `comap_norm_nhds_one`：comap_norm_nhds_one : comap norm (𝓝 0) = 𝓝 (1 : E)
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comap_norm_nhdsGT_zero' : comap norm (𝓝[>] 0) = 𝓝[≠] (1 : E) := by
  simp [nhdsWithin, comap_norm_nhds_one, Set.preimage, Set.compl_def]

@[to_additive]
/-
**tendsto_norm_div_self_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_norm_div_self_nhdsNE {E : Type*} [NormedCommGroup E] (a : E) : Ten
dsto (fun x => ‖x / a‖) (𝓝[!=] a) (𝓝[>] 0)
参数：a : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tendsto_norm_inv_mul_self_nhdsNE`：tendsto_norm_inv_mul_self_nhdsNE (a : 
E) : Tendsto (fun x => ‖x⁻¹ * a‖) (𝓝[!=] a) (𝓝[>] 0)
-/
theorem tendsto_norm_div_self_nhdsNE {E : Type*} [NormedCommGroup E] (a : E) :
    Tendsto (fun x => ‖x / a‖) (𝓝[≠] a) (𝓝[>] 0) := by
  simp_rw [← norm_inv_mul]
  exact tendsto_norm_inv_mul_self_nhdsNE a

end NormedGroup

