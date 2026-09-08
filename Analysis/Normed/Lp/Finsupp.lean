/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.MetricSpace.Basic

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic.Positivity.Finset

/-!
# Direct sum of metric spaces

This files endows the direct sum `ι →₀ X` of `ι`-many copies of a metric space `X` with the
L^p metric.

## TODO

Allow the L^∞ metric too. Currently, there is no easy way to perform the proofs:
`match` on `ℝ≥0∞` exposes the underlying `Option` and `induction p using ENNReal.recTopCoe` in the
`EMetricSpace` instance chokes on the `PseudoEMetricSpace` one.
-/

open scoped ENNReal NNReal

public section

namespace Finsupp
variable {ι X : Type*} [Zero X] {p : ℝ≥0} [Fact (1 ≤ p)]

/-- The L^1 extended metric on `ι`-many copies of a metric space `X` -/
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The L^1 extended metric on `ι`-many copies of a metric space `X`
-/
noncomputable instance [PseudoEMetricSpace X] : PseudoEMetricSpace (WithLp p <| ι →₀ X) where
  edist f g :=
  ((f.ofLp.zipWith edist (edist_self _) g.ofLp).sum fun i r ↦ r ^ (p : ℝ)) ^ (p⁻¹ : ℝ)
  edist_self f := by
    have : 0 < p := zero_lt_one.trans_le Fact.out
    simp [sum, *]
  edist_comm f g := by
    simp only [sum, zipWith_apply, edist_comm]
    congr 2
    ext i
    simp [edist_comm]
  edist_triangle f g h := by
    classical
    have : 0 < p := zero_lt_one.trans_le Fact.out
    let s := f.ofLp.support ∪ g.ofLp.support ∪ h.ofLp.support
    rw [sum_of_support_subset (s := s) _ (by grind [support_zipWith]) _ (by simp [*]),
      sum_of_support_subset (s := s) _ (by grind [support_zipWith]) _ (by simp [*]),
      sum_of_support_subset (s := s) _ (by grind [support_zipWith]) _ (by simp [*])]
    simp only [zipWith_apply, ← one_div]
    grw [← ENNReal.Lp_add_le _ _ _ (mod_cast Fact.out)]
    gcongr
    exact edist_triangle ..
/-
**Finsupp.edist_def** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：edist_def [PseudoEMetricSpace X] {p : Real>=0} [Fact (1 <= p)] (f g : With
Lp p <| ι ->₀ X) : edist f g = ((f.ofLp.zipWith edist (edist_self _) g.ofLp).sum
 fun _i r => r ^ (p : Real)) ^ (p⁻¹ : Real)
参数：1 <= p；f g : WithLp p <| ι ->₀ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edist_def [PseudoEMetricSpace X] {p : ℝ≥0} [Fact (1 ≤ p)]
    (f g : WithLp p <| ι →₀ X) :
    edist f g =
      ((f.ofLp.zipWith edist (edist_self _) g.ofLp).sum fun _i r ↦ r ^ (p : ℝ)) ^ (p⁻¹ : ℝ) := rfl

/-- The L^1 extended metric on `ι`-many copies of a metric space `X` -/
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The L^1 extended metric on `ι`-many copies of a metric space `X`
-/
noncomputable instance [EMetricSpace X] : EMetricSpace (WithLp p <| ι →₀ X) where
  eq_of_edist_eq_zero {f g} hfg := by simp_all [edist_def, sum, WithLp.ext_iff, DFunLike.ext_iff]

/-- The L^1 metric on `ι`-many copies of a metric space `X` -/
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The L^1 metric on `ι`-many copies of a metric space `X`
-/
noncomputable instance [PseudoMetricSpace X] : PseudoMetricSpace (WithLp p <| ι →₀ X) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g ↦ ((f.ofLp.zipWith dist (dist_self _) g.ofLp).sum fun i r ↦ r ^ (p : ℝ)) ^ (p⁻¹ : ℝ))
    (fun f g ↦ by dsimp [sum]; positivity) fun f g ↦ by
      simp only [edist_def, sum, zipWith_apply, ← coe_nnreal_ennreal_nndist, NNReal.zero_le_coe,
        ← ENNReal.coe_rpow_of_nonneg, ← ENNReal.ofNNReal_finsetSum, inv_nonneg, ← coe_nndist,
        ← NNReal.coe_rpow, ← NNReal.coe_sum, ENNReal.ofReal_coe_nnreal, ENNReal.coe_inj]
      congr! 2
      ext i
      simp [← coe_nndist, ← coe_nnreal_ennreal_nndist]
/-
**Finsupp.dist_def** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：dist_def [PseudoMetricSpace X] (f g : WithLp p <| ι ->₀ X) : dist f g = ((
f.ofLp.zipWith dist (dist_self _) g.ofLp).sum fun _i r => r ^ (p : Real)) ^ (p⁻¹
 : Real)
参数：f g : WithLp p <| ι ->₀ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dist_def [PseudoMetricSpace X] (f g : WithLp p <| ι →₀ X) :
    dist f g =
      ((f.ofLp.zipWith dist (dist_self _) g.ofLp).sum fun _i r ↦ r ^ (p : ℝ)) ^ (p⁻¹ : ℝ) := rfl
/-
**Finsupp.nndist_def** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：nndist_def [PseudoMetricSpace X] (f g : WithLp p <| ι ->₀ X) : nndist f g 
= ((f.ofLp.zipWith nndist (nndist_self _) g.ofLp).sum fun _i r => r ^ (p : Real)
) ^ (p⁻¹ : Real)
参数：f g : WithLp p <| ι ->₀ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `nndist_self`：∀ {α : Type u} [inst : PseudoMetricSpace α] (a : α), nndist
 a a = 0
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nndist_def [PseudoMetricSpace X] (f g : WithLp p <| ι →₀ X) :
    nndist f g =
      ((f.ofLp.zipWith nndist (nndist_self _) g.ofLp).sum fun _i r ↦ r ^ (p : ℝ)) ^ (p⁻¹ : ℝ) := by
  ext
  simp only [coe_nndist, dist_def, sum, zipWith_apply, NNReal.coe_sum, NNReal.coe_rpow]
  congr 2
  ext i
  simp [← coe_nndist]

/-- The L^1 metric on `ι`-many copies of a metric space `X` -/
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The L^1 metric on `ι`-many copies of a metric space `X`
-/
noncomputable instance [MetricSpace X] : MetricSpace (WithLp p <| ι →₀ X) :=
  EMetricSpace.toMetricSpaceOfDist
    (fun f g ↦ ((f.ofLp.zipWith dist (dist_self _) g.ofLp).sum fun i r ↦ r ^ (p : ℝ)) ^ (p⁻¹ : ℝ))
    (fun f g ↦ by dsimp [sum]; positivity) fun f g ↦ by rw [edist_dist, dist_def]

end Finsupp

