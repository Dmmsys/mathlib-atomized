/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.UniformSpace.CompleteSeparated
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Antilipschitz functions

We say that a map `f : α → β` between two (extended) metric spaces is
`AntilipschitzWith K`, `K ≥ 0`, if for all `x, y` we have `edist x y ≤ K * edist (f x) (f y)`.
For a metric space, the latter inequality is equivalent to `dist x y ≤ K * dist (f x) (f y)`.

## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjunction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. We do not require `0 < K` in the definition, mostly because
we do not have a `posreal` type.
-/

@[expose] public section

open Bornology Filter Set Topology
open scoped NNReal ENNReal Uniformity

variable {α β γ : Type*}

/-- We say that `f : α → β` is `AntilipschitzWith K` if for any two points `x`, `y` we have
`edist x y ≤ K * edist (f x) (f y)`. This can also be used as a predicate for bounded below
linear operators, see `antilipschitzWith_iff_exists_mul_le_norm`. -/
/-
**AntilipschitzWith** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AntilipschitzWith [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : Real>
=0) (f : α -> β)
参数：K : Real>=0；f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `f : α → β` is `AntilipschitzWith K` if for any two points `x`, `y` 
we have
`edist x y ≤ K * edist (f x) (f y)`. This can also be used as a predicate for bo
unded below
linear operators, see `antilipschitzWith_iff_exists_mul_le_norm`.
-/
def AntilipschitzWith [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) (f : α → β) :=
  ∀ x y, edist x y ≤ K * edist (f x) (f y)
/-
**AntilipschitzWith.edist_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoEMetricSpace α] [inst_1 : Ps
eudoMetricSpace β] {K : NNReal} {f : α → β},   AntilipschitzWith K f → ∀ (x y : 
α), edist x y < ⊤
参数：x y : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
-/
protected lemma AntilipschitzWith.edist_lt_top [PseudoEMetricSpace α] [PseudoMetricSpace β]
    {K : ℝ≥0} {f : α → β} (h : AntilipschitzWith K f) (x y : α) : edist x y < ⊤ :=
  (h x y).trans_lt <| ENNReal.mul_lt_top ENNReal.coe_lt_top (edist_lt_top _ _)
/-
**AntilipschitzWith.edist_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntilipschitzWith.edist_ne_top [PseudoEMetricSpace α] [PseudoMetricSpace β
] {K : Real>=0} {f : α -> β} (h : AntilipschitzWith K f) (x y : α) : edist x y !
= ⊤
参数：h : AntilipschitzWith K f；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `AntilipschitzWith.edist_lt_top`：∀ {α : Type u_1} {β : Type u_2} [inst : 
PseudoEMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},  
 AntilipschitzWith K…
-/
theorem AntilipschitzWith.edist_ne_top [PseudoEMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {f : α → β} (h : AntilipschitzWith K f) (x y : α) : edist x y ≠ ⊤ :=
  (h.edist_lt_top x y).ne

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0} {f : α → β}

/-
**antilipschitzWith_iff_le_mul_nndist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antilipschitzWith_iff_le_mul_nndist : AntilipschitzWith K f ↔ forall x y, 
nndist x y <= K * nndist (f x) (f y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem antilipschitzWith_iff_le_mul_nndist :
    AntilipschitzWith K f ↔ ∀ x y, nndist x y ≤ K * nndist (f x) (f y) := by
  simp only [AntilipschitzWith, edist_nndist]
  norm_cast

alias ⟨AntilipschitzWith.le_mul_nndist, AntilipschitzWith.of_le_mul_nndist⟩ :=
  antilipschitzWith_iff_le_mul_nndist
/-
**antilipschitzWith_iff_le_mul_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antilipschitzWith_iff_le_mul_dist : AntilipschitzWith K f ↔ forall x y, di
st x y <= K * dist (f x) (f y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem antilipschitzWith_iff_le_mul_dist :
    AntilipschitzWith K f ↔ ∀ x y, dist x y ≤ K * dist (f x) (f y) := by
  simp only [antilipschitzWith_iff_le_mul_nndist, dist_nndist]
  norm_cast

alias ⟨AntilipschitzWith.le_mul_dist, AntilipschitzWith.of_le_mul_dist⟩ :=
  antilipschitzWith_iff_le_mul_dist

namespace AntilipschitzWith

/-
**AntilipschitzWith.mul_le_nndist** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：mul_le_nndist (hf : AntilipschitzWith K f) (x y : α) : K⁻¹ * nndist x y <=
 nndist (f x) (f y)
参数：hf : AntilipschitzWith K f；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `NNReal.div_le_of_le_mul'`：div_le_of_le_mul' {a b c : Real>=0} (h : a <= 
b * c) : a / b <= c
· 使用定理 `AntilipschitzWith.le_mul_nndist`：∀ {α : Type u_1} {β : Type u_2} [inst :
 PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},  
 AntilipschitzWith K …
-/
theorem mul_le_nndist (hf : AntilipschitzWith K f) (x y : α) :
    K⁻¹ * nndist x y ≤ nndist (f x) (f y) := by
  simpa only [div_eq_inv_mul] using NNReal.div_le_of_le_mul' (hf.le_mul_nndist x y)
/-
**AntilipschitzWith.mul_le_dist** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：mul_le_dist (hf : AntilipschitzWith K f) (x y : α) : (K⁻¹ * dist x y : Rea
l) <= dist (f x) (f y)
参数：hf : AntilipschitzWith K f；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.mul_le_nndist`：mul_le_nndist (hf : AntilipschitzWith K
 f) (x y : α) : K⁻¹ * nndist x y <= nndist (f x) (f y)
-/
theorem mul_le_dist (hf : AntilipschitzWith K f) (x y : α) :
    (K⁻¹ * dist x y : ℝ) ≤ dist (f x) (f y) := mod_cast hf.mul_le_nndist x y

end AntilipschitzWith

end Metric

namespace AntilipschitzWith

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
variable {K : ℝ≥0} {f : α → β}

open Metric

-- uses neither `f` nor `hf`
/-- Extract the constant from `hf : AntilipschitzWith K f`. This is useful, e.g.,
if `K` is given by a long formula, and we want to reuse this value. -/
@[nolint unusedArguments]
/-
**AntilipschitzWith.k** 是 Mathlib 中的一个定义，位于命名空间 `AntilipschitzWith`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : PseudoEMetricSpace α] →   
    [inst_1 : PseudoEMetricSpace β] → {K : NNReal} → {f : α → β} → Antilipschitz
With K f → NNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the constant from `hf : AntilipschitzWith K f`. This is useful, e.g.,
if `K` is given by a long formula, and we want to reuse this value.
-/
protected def k (_hf : AntilipschitzWith K f) : ℝ≥0 := K
/-
**AntilipschitzWith.injective** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} [inst : EMetricSpace α] [inst_1 : PseudoEM
etricSpace β] {K : NNReal} {f : α → β},   AntilipschitzWith K f → Function.Injec
tive f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
protected theorem injective {α : Type*} {β : Type*} [EMetricSpace α] [PseudoEMetricSpace β]
    {K : ℝ≥0} {f : α → β} (hf : AntilipschitzWith K f) : Function.Injective f := fun x y h => by
  simpa only [h, edist_self, mul_zero, edist_le_zero] using hf x y
/-
**AntilipschitzWith.mul_le_edist** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：mul_le_edist (hf : AntilipschitzWith K f) (x y : α) : (K : Real>=0∞)⁻¹ * e
dist x y <= edist (f x) (f y)
参数：hf : AntilipschitzWith K f；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.div_le_of_le_mul'`：div_le_of_le_mul' (h : a <= b * c) : a / b <=
 c
-/
theorem mul_le_edist (hf : AntilipschitzWith K f) (x y : α) :
    (K : ℝ≥0∞)⁻¹ * edist x y ≤ edist (f x) (f y) := by
  rw [mul_comm, ← div_eq_mul_inv]
  exact ENNReal.div_le_of_le_mul' (hf x y)
/-
**AntilipschitzWith.ediam_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWi
th`。
形式化陈述：ediam_preimage_le (hf : AntilipschitzWith K f) (s : Set β) : ediam (f ⁻¹' 
s) <= K * ediam s
参数：hf : AntilipschitzWith K f；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.ediam_le`：ediam_le {d : Real>=0∞} (h : forall x in s, forall y in
 s, edist x y <= d) : ediam s <= d
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
-/
theorem ediam_preimage_le (hf : AntilipschitzWith K f) (s : Set β) :
    ediam (f ⁻¹' s) ≤ K * ediam s :=
  ediam_le fun x hx y hy => by grw [hf x y, edist_le_ediam_of_mem (mem_preimage.1 hx) hy]
/-
**AntilipschitzWith.le_mul_ediam_image** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzW
ith`。
形式化陈述：le_mul_ediam_image (hf : AntilipschitzWith K f) (s : Set α) : ediam s <= K
 * ediam (f '' s)
参数：hf : AntilipschitzWith K f；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.ediam_mono`：ediam_mono (h : s subseteq t) : ediam s <= ediam t
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `AntilipschitzWith.ediam_preimage_le`：ediam_preimage_le (hf : Antilipschi
tzWith K f) (s : Set β) : ediam (f ⁻¹' s) <= K * ediam s
-/
theorem le_mul_ediam_image (hf : AntilipschitzWith K f) (s : Set α) :
    ediam s ≤ K * ediam (f '' s) :=
  (ediam_mono (subset_preimage_image _ _)).trans (hf.ediam_preimage_le (f '' s))
/-
**AntilipschitzWith.id** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoEMetricSpace α], AntilipschitzWith 1 id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
protected theorem id : AntilipschitzWith 1 (id : α → α) := fun x y => by
  simp only [ENNReal.coe_one, one_mul, id, le_refl]
/-
**AntilipschitzWith.comp** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：comp {Kg : Real>=0} {g : β -> γ} (hg : AntilipschitzWith Kg g) {Kf : Real>
=0} {f : α -> β} (hf : AntilipschitzWith Kf f) : AntilipschitzWith (Kf * Kg) (g 
∘ f)
参数：hg : AntilipschitzWith Kg g；hf : AntilipschitzWith Kf f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_right_mono`：mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·
)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem comp {Kg : ℝ≥0} {g : β → γ} (hg : AntilipschitzWith Kg g) {Kf : ℝ≥0} {f : α → β}
    (hf : AntilipschitzWith Kf f) : AntilipschitzWith (Kf * Kg) (g ∘ f) := fun x y =>
  calc
    edist x y ≤ Kf * edist (f x) (f y) := hf x y
    _ ≤ Kf * (Kg * edist (g (f x)) (g (f y))) := mul_right_mono (hg _ _)
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]; rfl
/-
**AntilipschitzWith.domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：domRestrict (hf : AntilipschitzWith K f) (s : Set α) : AntilipschitzWith K
 (s.domRestrict f)
参数：hf : AntilipschitzWith K f；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict (hf : AntilipschitzWith K f) (s : Set α) :
    AntilipschitzWith K (s.domRestrict f) := fun x y => hf x y

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
/-
**AntilipschitzWith.codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：codRestrict (hf : AntilipschitzWith K f) {s : Set β} (hs : forall x, f x i
n s) : AntilipschitzWith K (s.codRestrict f hs)
参数：hf : AntilipschitzWith K f；hs : forall x, f x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem codRestrict (hf : AntilipschitzWith K f) {s : Set β} (hs : ∀ x, f x ∈ s) :
    AntilipschitzWith K (s.codRestrict f hs) := fun x y => hf x y
/-
**AntilipschitzWith.to_rightInvOn'** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`
。
形式化陈述：to_rightInvOn' {s : Set α} (hf : AntilipschitzWith K (s.domRestrict f)) {g
 : β -> α} {t : Set β} (g_maps : MapsTo g t s) (g_inv : RightInvOn g f t) : Lips
chitzWith K (t.domRestrict g)
参数：hf : AntilipschitzWith K (s.domRestrict f)；g_maps : MapsTo g t s；g_inv : Righ
tInvOn g f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem to_rightInvOn' {s : Set α} (hf : AntilipschitzWith K (s.domRestrict f)) {g : β → α}
    {t : Set β} (g_maps : MapsTo g t s) (g_inv : RightInvOn g f t) :
    LipschitzWith K (t.domRestrict g) := fun x y => by
  simpa only [domRestrict_apply, g_inv x.mem, g_inv y.mem, Subtype.edist_mk_mk]
    using! hf ⟨g x, g_maps x.mem⟩ ⟨g y, g_maps y.mem⟩
/-
**AntilipschitzWith.to_rightInvOn** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：to_rightInvOn (hf : AntilipschitzWith K f) {g : β -> α} {t : Set β} (h : R
ightInvOn g f t) : LipschitzWith K (t.domRestrict g)
参数：hf : AntilipschitzWith K f；h : RightInvOn g f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.to_rightInvOn'`：to_rightInvOn' {s : Set α} (hf : Antil
ipschitzWith K (s.domRestrict f)) {g : β -> α} {t : Set β} (g_maps : MapsTo g t 
s) (g_inv : RightInvOn…
· 使用定理 `AntilipschitzWith.domRestrict`：domRestrict (hf : AntilipschitzWith K f) 
(s : Set α) : AntilipschitzWith K (s.domRestrict f)
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem to_rightInvOn (hf : AntilipschitzWith K f) {g : β → α} {t : Set β} (h : RightInvOn g f t) :
    LipschitzWith K (t.domRestrict g) := (hf.domRestrict univ).to_rightInvOn' (mapsTo_univ g t) h
/-
**AntilipschitzWith.to_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith
`。
形式化陈述：to_rightInverse (hf : AntilipschitzWith K f) {g : β -> α} (hg : Function.R
ightInverse g f) : LipschitzWith K g
参数：hf : AntilipschitzWith K f；hg : Function.RightInverse g f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem to_rightInverse (hf : AntilipschitzWith K f) {g : β → α} (hg : Function.RightInverse g f) :
    LipschitzWith K g := by
  intro x y
  have := hf (g x) (g y)
  rwa [hg x, hg y] at this
/-
**AntilipschitzWith.comap_uniformity_le** 是 Mathlib 中的一个定理，位于命名空间 `Antilipschitz
With`。
形式化陈述：comap_uniformity_le (hf : AntilipschitzWith K f) : (𝓤 β).comap (Prod.map f
 f) <= 𝓤 α
参数：hf : AntilipschitzWith K f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }
· 使用定理 `ENNReal.mul_pos`：mul_pos (ha : a != 0) (hb : b != 0) : 0 < a * b
· 使用定理 `ENNReal.inv_ne_zero`：∀ {a : ENNReal}, a⁻¹ ≠ 0 ↔ a ≠ ⊤
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.mul_lt_of_lt_div`：mul_lt_of_lt_div (h : a < b / c) : a * c < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem comap_uniformity_le (hf : AntilipschitzWith K f) : (𝓤 β).comap (Prod.map f f) ≤ 𝓤 α := by
  refine ((uniformity_basis_edist.comap _).le_basis_iff uniformity_basis_edist).2 fun ε h₀ => ?_
  refine ⟨(↑K)⁻¹ * ε, ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top) h₀.ne', ?_⟩
  refine fun x hx => (hf x.1 x.2).trans_lt ?_
  rw [mul_comm, ← div_eq_mul_inv] at hx
  rw [mul_comm]
  exact ENNReal.mul_lt_of_lt_div hx
/-
**AntilipschitzWith.isUniformInducing** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWi
th`。
形式化陈述：isUniformInducing (hf : AntilipschitzWith K f) (hfc : UniformContinuous f)
 : IsUniformInducing f
参数：hf : AntilipschitzWith K f；hfc : UniformContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AntilipschitzWith.comap_uniformity_le`：comap_uniformity_le (hf : Antilip
schitzWith K f) : (𝓤 β).comap (Prod.map f f) <= 𝓤 α
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
-/
theorem isUniformInducing (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    IsUniformInducing f :=
  ⟨le_antisymm hf.comap_uniformity_le hfc.le_comap⟩
/-
**AntilipschitzWith.isUniformEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `AntilipschitzW
ith`。
形式化陈述：isUniformEmbedding {α β : Type*} [EMetricSpace α] [PseudoEMetricSpace β] {
K : Real>=0} {f : α -> β} (hf : AntilipschitzWith K f) (hfc : UniformContinuous 
f) : IsUniformEmbedding f
参数：hf : AntilipschitzWith K f；hfc : UniformContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.isUniformInducing`：isUniformInducing (hf : Antilipschi
tzWith K f) (hfc : UniformContinuous f) : IsUniformInducing f
· 使用定理 `AntilipschitzWith.injective`：∀ {α : Type u_4} {β : Type u_5} [inst : EMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Antilip
schitzWith K f → …
-/
lemma isUniformEmbedding {α β : Type*} [EMetricSpace α] [PseudoEMetricSpace β] {K : ℝ≥0} {f : α → β}
    (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) : IsUniformEmbedding f :=
  ⟨hf.isUniformInducing hfc, hf.injective⟩
/-
**AntilipschitzWith.comap_nhds_le** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：comap_nhds_le (hf : AntilipschitzWith K f) (x : α) : (𝓝 (f x)).comap f <= 
𝓝 x
参数：hf : AntilipschitzWith K f；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)
· 使用定理 `AntilipschitzWith.comap_uniformity_le`：comap_uniformity_le (hf : Antilip
schitzWith K f) : (𝓤 β).comap (Prod.map f f) <= 𝓤 α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
-/
theorem comap_nhds_le (hf : AntilipschitzWith K f) (x : α) : (𝓝 (f x)).comap f ≤ 𝓝 x := by
  simp only [nhds_eq_comap_uniformity]
  grw [← hf.comap_uniformity_le]
  simp [comap_comap, Function.comp_def]
/-
**AntilipschitzWith.isInducing** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：isInducing (hf : AntilipschitzWith K f) (hfc : Continuous f) : IsInducing 
f
参数：hf : AntilipschitzWith K f；hfc : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.isInducing_iff_nhds`：isInducing_iff_nhds : IsInducing f ↔ foral
l x, 𝓝 x = comap f (𝓝 (f x))
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `AntilipschitzWith.comap_nhds_le`：comap_nhds_le (hf : AntilipschitzWith K
 f) (x : α) : (𝓝 (f x)).comap f <= 𝓝 x
-/
theorem isInducing (hf : AntilipschitzWith K f) (hfc : Continuous f) : IsInducing f :=
  isInducing_iff_nhds.mpr fun x ↦ le_antisymm (hfc.tendsto x).le_comap <| hf.comap_nhds_le _
/-
**AntilipschitzWith.isEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `AntilipschitzWith`。
形式化陈述：isEmbedding {α β : Type*} [EMetricSpace α] [PseudoEMetricSpace β] {K : Rea
l>=0} {f : α -> β} (hf : AntilipschitzWith K f) (hfc : Continuous f) : IsEmbeddi
ng f
参数：hf : AntilipschitzWith K f；hfc : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space X] {f : X → Y},   To
pology.IsInducing f →…
· 使用定理 `EMetricSpace.instT0Space`：∀ {γ : Type w} [inst : EMetricSpace γ], T0Spac
e γ
· 使用定理 `AntilipschitzWith.isInducing`：isInducing (hf : AntilipschitzWith K f) (h
fc : Continuous f) : IsInducing f
-/
lemma isEmbedding {α β : Type*} [EMetricSpace α] [PseudoEMetricSpace β] {K : ℝ≥0} {f : α → β}
    (hf : AntilipschitzWith K f) (hfc : Continuous f) : IsEmbedding f :=
  hf.isInducing hfc |>.isEmbedding
/-
**AntilipschitzWith.isComplete_range** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWit
h`。
形式化陈述：isComplete_range [CompleteSpace α] (hf : AntilipschitzWith K f) (hfc : Uni
formContinuous f) : IsComplete (range f)
参数：hf : AntilipschitzWith K f；hfc : UniformContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUniformInducing.isComplete_range`：IsUniformInducing.isComplete_range [
CompleteSpace α] (hf : IsUniformInducing f) : IsComplete (range f)
· 使用定理 `AntilipschitzWith.isUniformInducing`：isUniformInducing (hf : Antilipschi
tzWith K f) (hfc : UniformContinuous f) : IsUniformInducing f
-/
theorem isComplete_range [CompleteSpace α] (hf : AntilipschitzWith K f)
    (hfc : UniformContinuous f) : IsComplete (range f) :=
  (hf.isUniformInducing hfc).isComplete_range
/-
**AntilipschitzWith.isClosed_range** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`
。
形式化陈述：isClosed_range {α β : Type*} [PseudoEMetricSpace α] [EMetricSpace β] [Comp
leteSpace α] {f : α -> β} {K : Real>=0} (hf : AntilipschitzWith K f) (hfc : Unif
ormContinuous f) : IsClosed (range f)
参数：hf : AntilipschitzWith K f；hfc : UniformContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsComplete.isClosed`：IsComplete.isClosed [UniformSpace α] [T0Space α] {s
 : Set α} (h : IsComplete s) : IsClosed s
· 使用定理 `EMetricSpace.instT0Space`：∀ {γ : Type w} [inst : EMetricSpace γ], T0Spac
e γ
· 使用定理 `AntilipschitzWith.isComplete_range`：isComplete_range [CompleteSpace α] (
hf : AntilipschitzWith K f) (hfc : UniformContinuous f) : IsComplete (range f)
-/
theorem isClosed_range {α β : Type*} [PseudoEMetricSpace α] [EMetricSpace β] [CompleteSpace α]
    {f : α → β} {K : ℝ≥0} (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    IsClosed (range f) :=
  (hf.isComplete_range hfc).isClosed
/-
**AntilipschitzWith.isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWi
th`。
形式化陈述：isClosedEmbedding {α : Type*} {β : Type*} [EMetricSpace α] [EMetricSpace β
] {K : Real>=0} {f : α -> β} [CompleteSpace α] (hf : AntilipschitzWith K f) (hfc
 : UniformContinuous f) : IsClosedEmbedding f
参数：hf : AntilipschitzWith K f；hfc : UniformContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用引理 `AntilipschitzWith.isUniformEmbedding`：isUniformEmbedding {α β : Type*} [
EMetricSpace α] [PseudoEMetricSpace β] {K : Real>=0} {f : α -> β} (hf : Antilips
chitzWith K f) (hfc : Unif…
· 使用定理 `AntilipschitzWith.isClosed_range`：isClosed_range {α β : Type*} [PseudoEM
etricSpace α] [EMetricSpace β] [CompleteSpace α] {f : α -> β} {K : Real>=0} (hf 
: AntilipschitzWith K …
-/
theorem isClosedEmbedding {α : Type*} {β : Type*} [EMetricSpace α] [EMetricSpace β] {K : ℝ≥0}
    {f : α → β} [CompleteSpace α] (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    IsClosedEmbedding f :=
  { (hf.isUniformEmbedding hfc).isEmbedding with isClosed_range := hf.isClosed_range hfc }
/-
**AntilipschitzWith.subtype_coe** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：subtype_coe (s : Set α) : AntilipschitzWith 1 ((↑) : s -> α)
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.domRestrict`：domRestrict (hf : AntilipschitzWith K f) 
(s : Set α) : AntilipschitzWith K (s.domRestrict f)
· 使用定理 `AntilipschitzWith.id`：∀ {α : Type u_1} [inst : PseudoEMetricSpace α], An
tilipschitzWith 1 id
-/
theorem subtype_coe (s : Set α) : AntilipschitzWith 1 ((↑) : s → α) :=
  AntilipschitzWith.id.domRestrict s

@[nontriviality]
/-
**AntilipschitzWith.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith
`。
形式化陈述：of_subsingleton [Subsingleton α] {K : Real>=0} : AntilipschitzWith K f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem of_subsingleton [Subsingleton α] {K : ℝ≥0} : AntilipschitzWith K f := fun x y => by
  simp only [Subsingleton.elim x y, edist_self, zero_le]

/-- If `f : α → β` is `0`-antilipschitz, then `α` is a `subsingleton`. -/
/-
**AntilipschitzWith.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} [inst : EMetricSpace α] [inst_1 : PseudoEM
etricSpace β] {f : α → β},   AntilipschitzWith 0 f → Subsingleton α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `edist_le_zero`：edist_le_zero {x y : γ} : edist x y <= 0 ↔ x = y
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0

--- 原说明 ---
If `f : α → β` is `0`-antilipschitz, then `α` is a `subsingleton`.
-/
protected theorem subsingleton {α β} [EMetricSpace α] [PseudoEMetricSpace β] {f : α → β}
    (h : AntilipschitzWith 0 f) : Subsingleton α :=
  ⟨fun x y => edist_le_zero.1 <| (h x y).trans_eq <| zero_mul _⟩

/-- If `f : α → β` is `K`-antilipschitz and `α` is nontrivial, `K` is positive. -/
/-
**AntilipschitzWith.pos** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：∀ {β : Type u_2} [inst : PseudoEMetricSpace β] {K : NNReal} {α : Type u_4}
 [inst_1 : EMetricSpace α] [Nontrivial α]   {f : α → β}, AntilipschitzWith K f →
 0 < K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `AntilipschitzWith.subsingleton`：∀ {α : Type u_4} {β : Type u_5} [inst : 
EMetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   AntilipschitzWith
 0 f → Subsingleton …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_zero_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
If `f : α → β` is `K`-antilipschitz and `α` is nontrivial, `K` is positive.
-/
protected theorem pos {α} [EMetricSpace α] [Nontrivial α] {f : α → β}
    (hf : AntilipschitzWith K f) : 0 < K := by
  by_contra! h₀
  obtain rfl : K = 0 := by rwa [le_zero_iff] at h₀
  exact not_subsingleton α hf.subsingleton

end AntilipschitzWith

namespace AntilipschitzWith

open Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]
variable {K : ℝ≥0} {f : α → β}

/-
**AntilipschitzWith.isBounded_preimage** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzW
ith`。
形式化陈述：isBounded_preimage (hf : AntilipschitzWith K f) {s : Set β} (hs : IsBounde
d s) : IsBounded (f ⁻¹' s)
参数：hf : AntilipschitzWith K f；hs : IsBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.isBounded_iff_ediam_ne_top`：isBounded_iff_ediam_ne_top : IsBounde
d s ↔ ediam s != ⊤
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `Bornology.IsBounded.ediam_ne_top`：∀ {α : Type u} {s : Set α} [inst : Pse
udoMetricSpace α], Bornology.IsBounded s → Metric.ediam s ≠ ⊤
· 使用定理 `AntilipschitzWith.ediam_preimage_le`：ediam_preimage_le (hf : Antilipschi
tzWith K f) (s : Set β) : ediam (f ⁻¹' s) <= K * ediam s
-/
theorem isBounded_preimage (hf : AntilipschitzWith K f) {s : Set β} (hs : IsBounded s) :
    IsBounded (f ⁻¹' s) :=
  isBounded_iff_ediam_ne_top.2 <| ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hs.ediam_ne_top) (hf.ediam_preimage_le _)
/-
**AntilipschitzWith.tendsto_cobounded** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWi
th`。
形式化陈述：tendsto_cobounded (hf : AntilipschitzWith K f) : Tendsto f (cobounded α) (
cobounded β)
参数：hf : AntilipschitzWith K f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `AntilipschitzWith.isBounded_preimage`：isBounded_preimage (hf : Antilipsc
hitzWith K f) {s : Set β} (hs : IsBounded s) : IsBounded (f ⁻¹' s)
-/
theorem tendsto_cobounded (hf : AntilipschitzWith K f) : Tendsto f (cobounded α) (cobounded β) :=
  compl_surjective.forall.2 fun _ ↦ hf.isBounded_preimage

/-- The image of a proper space under an expanding onto map is proper. -/
/-
**AntilipschitzWith.properSpace** 是 Mathlib 中的一个定理，位于命名空间 `AntilipschitzWith`。
形式化陈述：∀ {β : Type u_2} [inst : PseudoMetricSpace β] {α : Type u_4} [inst_1 : Met
ricSpace α] {K : NNReal} {f : α → β}   [ProperSpace α], AntilipschitzWith K f → 
Continuous f → Function.Surjective f → ProperSpace β
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
· 使用定理 `AntilipschitzWith.isBounded_preimage`：isBounded_preimage (hf : Antilipsc
hitzWith K f) {s : Set β} (hs : IsBounded s) : IsBounded (f ⁻¹' s)
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.isCompact_iff_isClosed_bounded`：isCompact_iff_isClosed_bounded {α
 : Type*} {s : Set α} [MetricSpace α] [ProperSpace α] : IsCompact s ↔ IsClosed s
 ∧ IsBounded s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)

--- 原说明 ---
The image of a proper space under an expanding onto map is proper.
-/
protected theorem properSpace {α : Type*} [MetricSpace α] {K : ℝ≥0} {f : α → β} [ProperSpace α]
    (hK : AntilipschitzWith K f) (f_cont : Continuous f) (hf : Function.Surjective f) :
    ProperSpace β := by
  refine ⟨fun x₀ r => ?_⟩
  let K := f ⁻¹' closedBall x₀ r
  have A : IsClosed K := isClosed_closedBall.preimage f_cont
  have B : IsBounded K := hK.isBounded_preimage isBounded_closedBall
  have : IsCompact K := isCompact_iff_isClosed_bounded.2 ⟨A, B⟩
  convert! this.image f_cont
  exact (hf.image_preimage _).symm
/-
**AntilipschitzWith.isBounded_of_image2_left** 是 Mathlib 中的一个定理，位于命名空间 `Antilips
chitzWith`。
形式化陈述：isBounded_of_image2_left (f : α -> β -> γ) {K₁ : Real>=0} (hf : forall b, 
AntilipschitzWith K₁ fun a => f a b) {s : Set α} {t : Set β} (hst : IsBounded (S
et.image2 f s t)) : IsBounded s ∨ IsBounded t
参数：f : α -> β -> γ；hf : forall b, AntilipschitzWith K₁ fun a => f a b；hst : IsBo
unded (Set.image2 f s t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Bornology.nonempty_of_not_isBounded`：nonempty_of_not_isBounded (h : ¬IsB
ounded s) : s.Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AntilipschitzWith.isBounded_preimage`：isBounded_preimage (hf : Antilipsc
hitzWith K f) {s : Set β} (hs : IsBounded s) : IsBounded (f ⁻¹' s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_singleton_right`：image2_singleton_right : image2 f s {b} = (f
un a => f a b) '' s
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem isBounded_of_image2_left (f : α → β → γ) {K₁ : ℝ≥0}
    (hf : ∀ b, AntilipschitzWith K₁ fun a => f a b) {s : Set α} {t : Set β}
    (hst : IsBounded (Set.image2 f s t)) : IsBounded s ∨ IsBounded t := by
  contrapose! hst
  obtain ⟨b, hb⟩ : t.Nonempty := nonempty_of_not_isBounded hst.2
  have : ¬IsBounded (Set.image2 f s {b}) := by
    intro h
    apply hst.1
    rw [Set.image2_singleton_right] at h
    replace h := (hf b).isBounded_preimage h
    exact h.subset (subset_preimage_image _ _)
  exact mt (IsBounded.subset · (image2_subset subset_rfl (singleton_subset_iff.mpr hb))) this
/-
**AntilipschitzWith.isBounded_of_image2_right** 是 Mathlib 中的一个定理，位于命名空间 `Antilip
schitzWith`。
形式化陈述：isBounded_of_image2_right {f : α -> β -> γ} {K₂ : Real>=0} (hf : forall a,
 AntilipschitzWith K₂ (f a)) {s : Set α} {t : Set β} (hst : IsBounded (Set.image
2 f s t)) : IsBounded s ∨ IsBounded t
参数：hf : forall a, AntilipschitzWith K₂ (f a)；hst : IsBounded (Set.image2 f s t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `AntilipschitzWith.isBounded_of_image2_left`：isBounded_of_image2_left (f 
: α -> β -> γ) {K₁ : Real>=0} (hf : forall b, AntilipschitzWith K₁ fun a => f a 
b) {s : Set α} {t : Set β} (hst …
· 使用定理 `Set.image2_swap`：image2_swap (s : Set α) (t : Set β) : image2 f s t = im
age2 (fun a b => f b a) t s
-/
theorem isBounded_of_image2_right {f : α → β → γ} {K₂ : ℝ≥0} (hf : ∀ a, AntilipschitzWith K₂ (f a))
    {s : Set α} {t : Set β} (hst : IsBounded (Set.image2 f s t)) : IsBounded s ∨ IsBounded t :=
  Or.symm <| isBounded_of_image2_left (flip f) hf <| image2_swap f s t ▸ hst

end AntilipschitzWith

/-
**LipschitzWith.to_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.to_rightInverse [PseudoEMetricSpace α] [PseudoEMetricSpace β
] {K : Real>=0} {f : α -> β} (hf : LipschitzWith K f) {g : β -> α} (hg : Functio
n.RightInverse g f) : AntilipschitzWith K g
参数：hf : LipschitzWith K f；hg : Function.RightInverse g f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem LipschitzWith.to_rightInverse [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : ℝ≥0}
    {f : α → β} (hf : LipschitzWith K f) {g : β → α} (hg : Function.RightInverse g f) :
    AntilipschitzWith K g := fun x y => by simpa only [hg _] using hf (g x) (g y)
