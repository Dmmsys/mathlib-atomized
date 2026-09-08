/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Sébastien Gouëzel, Jireh Loreaux
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Normed.Lp.WithLp

/-!
# `L^p` distance on products of two metric spaces

Given two metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a parameter `p : ℝ≥0∞`, that also induce
the product topology. We define them in this file. For `0 < p < ∞`, the distance on `α × β`
is given by
$$
d(x, y) = \left(d(x_1, y_1)^p + d(x_2, y_2)^p\right)^{1/p}.
$$
For `p = ∞` the distance is the supremum of the distances and `p = 0` the distance is the
cardinality of the elements that are not equal.

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Prod-type, named
`WithLp p (α × β)`. The assumption `[Fact (1 ≤ p)]` is required for the metric and normed space
instances.

We ensure that the topology, bornology and uniform structure on `WithLp p (α × β)` are (defeq to)
the product topology, product bornology and product uniformity, to be able to use freely continuity
statements for the coordinate functions, for instance.

If you wish to endow a type synonym of `α × β` with the `L^p` distance, you can use
`pseudoMetricSpaceToProd` and the declarations below that one.


## Implementation notes

This file is a straight-forward adaptation of `Mathlib/Analysis/Normed/Lp/PiLp.lean`.

## TODO

TODO: the results about uniformity and bornology in the `Aux` section should be using the tools in
`Mathlib.Topology.MetricSpace.Bilipschitz`, so that they can be inlined in the next section and
the only remaining results are about `Lipschitz` and `Antilipschitz`.

-/

@[expose] public section

open Real Set Filter RCLike Bornology Uniformity Topology NNReal ENNReal

noncomputable section

variable (p : ℝ≥0∞) (𝕜 α β : Type*)

namespace WithLp

section algebra

/- Register simplification lemmas for the applications of `WithLp p (α × β)` elements, as the usual
lemmas for `Prod` will not trigger. -/

variable {p 𝕜 α β}
variable [Semiring 𝕜] [AddCommGroup α] [AddCommGroup β]
variable (x y : WithLp p (α × β)) (c : 𝕜)

/-- The projection on the first coordinate in `WithLp`. -/
/-
**WithLp.fst** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：{p : ENNReal} → {α : Type u_2} → {β : Type u_3} → WithLp p (α × β) → α
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection on the first coordinate in `WithLp`.
-/
protected def fst (x : WithLp p (α × β)) : α := (ofLp x).fst

/-- The projection on the second coordinate in `WithLp`. -/
/-
**WithLp.snd** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：{p : ENNReal} → {α : Type u_2} → {β : Type u_3} → WithLp p (α × β) → β
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection on the second coordinate in `WithLp`.
-/
protected def snd (x : WithLp p (α × β)) : β := (ofLp x).snd

@[simp]
/-
**WithLp.zero_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：zero_fst : (0 : WithLp p (α × β)).fst = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_fst : (0 : WithLp p (α × β)).fst = 0 :=
  rfl

@[simp]
/-
**WithLp.zero_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：zero_snd : (0 : WithLp p (α × β)).snd = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_snd : (0 : WithLp p (α × β)).snd = 0 :=
  rfl

@[simp]
/-
**WithLp.add_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：add_fst : (x + y).fst = x.fst + y.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_fst : (x + y).fst = x.fst + y.fst :=
  rfl

@[simp]
/-
**WithLp.add_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：add_snd : (x + y).snd = x.snd + y.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_snd : (x + y).snd = x.snd + y.snd :=
  rfl

@[simp]
/-
**WithLp.sub_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：sub_fst : (x - y).fst = x.fst - y.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_fst : (x - y).fst = x.fst - y.fst :=
  rfl

@[simp]
/-
**WithLp.sub_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：sub_snd : (x - y).snd = x.snd - y.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_snd : (x - y).snd = x.snd - y.snd :=
  rfl

@[simp]
/-
**WithLp.neg_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：neg_fst : (-x).fst = -x.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_fst : (-x).fst = -x.fst :=
  rfl

@[simp]
/-
**WithLp.neg_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：neg_snd : (-x).snd = -x.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_snd : (-x).snd = -x.snd :=
  rfl

variable [Module 𝕜 α] [Module 𝕜 β]

@[simp]
/-
**WithLp.smul_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：smul_fst : (c • x).fst = c • x.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_fst : (c • x).fst = c • x.fst :=
  rfl

@[simp]
/-
**WithLp.smul_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：smul_snd : (c • x).snd = c • x.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_snd : (c • x).snd = c • x.snd :=
  rfl

variable (p 𝕜 α β)

/-- `WithLp.fst` as a linear map. -/
@[simps]
/-
**WithLp.fst** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：{p : ENNReal} → {α : Type u_2} → {β : Type u_3} → WithLp p (α × β) → α
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithLp.fst` as a linear map.
-/
def fstₗ : WithLp p (α × β) →ₗ[𝕜] α where
  toFun := WithLp.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `WithLp.snd` as a linear map. -/
@[simps]
/-
**WithLp.snd** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：{p : ENNReal} → {α : Type u_2} → {β : Type u_3} → WithLp p (α × β) → β
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithLp.snd` as a linear map.
-/
def sndₗ : WithLp p (α × β) →ₗ[𝕜] β where
  toFun := WithLp.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end algebra

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

section equiv

variable {p α β}

/-
**WithLp.toLp_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ {p : ENNReal} {α : Type u_2} {β : Type u_3} (x : α × β), (WithLp.toLp p 
x).fst = x.1
参数：x : α × β；WithLp.toLp p x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLp_fst (x : α × β) : (toLp p x).fst = x.fst := rfl
/-
**WithLp.toLp_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ {p : ENNReal} {α : Type u_2} {β : Type u_3} (x : α × β), (WithLp.toLp p 
x).snd = x.2
参数：x : α × β；WithLp.toLp p x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLp_snd (x : α × β) : (toLp p x).snd = x.snd := rfl
/-
**WithLp.ofLp_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ {p : ENNReal} {α : Type u_2} {β : Type u_3} (x : WithLp p (α × β)), x.of
Lp.1 = x.fst
参数：x : WithLp p (α × β)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofLp_fst (x : WithLp p (α × β)) : (ofLp x).fst = x.fst := rfl
/-
**WithLp.ofLp_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ {p : ENNReal} {α : Type u_2} {β : Type u_3} (x : WithLp p (α × β)), x.of
Lp.2 = x.snd
参数：x : WithLp p (α × β)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofLp_snd (x : WithLp p (α × β)) : (ofLp x).snd = x.snd := rfl

end equiv

section DistNorm

/-!
### Definition of `edist`, `dist` and `norm` on `WithLp p (α × β)`

In this section we define the `edist`, `dist` and `norm` functions on `WithLp p (α × β)` without
assuming `[Fact (1 ≤ p)]` or metric properties of the spaces `α` and `β`. This allows us to provide
the rewrite lemmas for each of three cases `p = 0`, `p = ∞` and `0 < p.toReal`.
-/


section EDist

variable [EDist α] [EDist β]

/-- Endowing the space `WithLp p (α × β)` with the `L^p` edistance. We register this instance
separate from `WithLp.instProdPseudoEMetric` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future emetric-like structure on `WithLp p (α × β)` for
`p < 1` satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
/-
**WithLp.instProdEDist** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdEDist : EDist (WithLp p (α × β)) where edist f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Endowing the space `WithLp p (α × β)` with the `L^p` edistance. We register this
 instance
separate from `WithLp.instProdPseudoEMetric` since the latter requires the type 
class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future emetric-like structure on `WithL
p p (α × β)` for
`p < 1` satisfying a relaxed triangle inequality. The terminology for this varie
s throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*.
-/
instance instProdEDist : EDist (WithLp p (α × β)) where
  edist f g :=
    if _hp : p = 0 then
      (if edist f.fst g.fst = 0 then 0 else 1) + (if edist f.snd g.snd = 0 then 0 else 1)
    else if p = ∞ then
      edist f.fst g.fst ⊔ edist f.snd g.snd
    else
      (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

variable {p α β}

@[simp]
/-
**WithLp.prod_edist_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_edist_eq_card (f g : WithLp 0 (α × β)) : edist f g = (if edist f.fst 
g.fst = 0 then 0 else 1) + (if edist f.snd g.snd = 0 then 0 else 1)
参数：f g : WithLp 0 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem prod_edist_eq_card (f g : WithLp 0 (α × β)) :
    edist f g =
      (if edist f.fst g.fst = 0 then 0 else 1) + (if edist f.snd g.snd = 0 then 0 else 1) := by
  convert! if_pos rfl
/-
**WithLp.prod_edist_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_edist_eq_add (hp : 0 < p.toReal) (f g : WithLp p (α × β)) : edist f g
 = (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal
)
参数：hp : 0 < p.toReal；f g : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem prod_edist_eq_add (hp : 0 < p.toReal) (f g : WithLp p (α × β)) :
    edist f g = (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)
/-
**WithLp.prod_edist_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_edist_eq_sup (f g : WithLp ∞ (α × β)) : edist f g = edist f.fst g.fst
 ⊔ edist f.snd g.snd
参数：f g : WithLp ∞ (α × β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_edist_eq_sup (f g : WithLp ∞ (α × β)) :
    edist f g = edist f.fst g.fst ⊔ edist f.snd g.snd := rfl

end EDist

section EDistProp

variable {α β}
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β]

/-- The distance from one point to itself is always zero.

This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it separate
from `WithLp.instProdPseudoEMetricSpace` so it can be used also for `p < 1`. -/
/-
**WithLp.prod_edist_self** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_edist_self (f : WithLp p (α × β)) : edist f f = 0
参数：f : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.prod_edist_eq_card`：prod_edist_eq_card (f g : WithLp 0 (α × β)) :
 edist f g = (if edist f.fst g.fst = 0 then 0 else 1) + (if edist f.snd g.snd = 
0 then 0 else 1…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `WithLp.prod_edist_eq_add`：prod_edist_eq_add (hp : 0 < p.toReal) (f g : W
ithLp p (α × β)) : edist f g = (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd
 ^ p.toReal) ^…
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R

--- 原说明 ---
The distance from one point to itself is always zero.

This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it 
separate
from `WithLp.instProdPseudoEMetricSpace` so it can be used also for `p < 1`.
-/
theorem prod_edist_self (f : WithLp p (α × β)) : edist f f = 0 := by
  rcases p.trichotomy with (rfl | rfl | h)
  · classical
    simp
  · simp [prod_edist_eq_sup]
  · simp [prod_edist_eq_add h, ENNReal.zero_rpow_of_pos h,
      ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]

/-- The distance is symmetric.

This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it separate
from `WithLp.instProdPseudoEMetricSpace` so it can be used also for `p < 1`. -/
/-
**WithLp.prod_edist_comm** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_edist_comm (f g : WithLp p (α × β)) : edist f g = edist g f
参数：f g : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.prod_edist_eq_card`：prod_edist_eq_card (f g : WithLp 0 (α × β)) :
 edist f g = (if edist f.fst g.fst = 0 then 0 else 1) + (if edist f.snd g.snd = 
0 then 0 else 1…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithLp.prod_edist_eq_add`：prod_edist_eq_add (hp : 0 < p.toReal) (f g : W
ithLp p (α × β)) : edist f g = (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd
 ^ p.toReal) ^…

--- 原说明 ---
The distance is symmetric.

This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it 
separate
from `WithLp.instProdPseudoEMetricSpace` so it can be used also for `p < 1`.
-/
theorem prod_edist_comm (f g : WithLp p (α × β)) : edist f g = edist g f := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [prod_edist_eq_card, edist_comm]
  · simp only [prod_edist_eq_sup, edist_comm]
  · simp only [prod_edist_eq_add h, edist_comm]

end EDistProp

section Dist

variable [Dist α] [Dist β]

/-- Endowing the space `WithLp p (α × β)` with the `L^p` distance. We register this instance
separate from `WithLp.instProdPseudoMetricSpace` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future metric-like structure on `WithLp p (α × β)` for
`p < 1` satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
/-
**WithLp.instProdDist** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdDist : Dist (WithLp p (α × β)) where dist f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Endowing the space `WithLp p (α × β)` with the `L^p` distance. We register this 
instance
separate from `WithLp.instProdPseudoMetricSpace` since the latter requires the t
ype class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future metric-like structure on `WithLp
 p (α × β)` for
`p < 1` satisfying a relaxed triangle inequality. The terminology for this varie
s throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*.
-/
instance instProdDist : Dist (WithLp p (α × β)) where
  dist f g :=
    if _hp : p = 0 then
      (if dist f.fst g.fst = 0 then 0 else 1) + (if dist f.snd g.snd = 0 then 0 else 1)
    else if p = ∞ then
      dist f.fst g.fst ⊔ dist f.snd g.snd
    else
      (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

variable {p α β}
/-
**WithLp.prod_dist_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_dist_eq_card (f g : WithLp 0 (α × β)) : dist f g = (if dist f.fst g.f
st = 0 then 0 else 1) + (if dist f.snd g.snd = 0 then 0 else 1)
参数：f g : WithLp 0 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem prod_dist_eq_card (f g : WithLp 0 (α × β)) : dist f g =
    (if dist f.fst g.fst = 0 then 0 else 1) + (if dist f.snd g.snd = 0 then 0 else 1) := by
  convert! if_pos rfl
/-
**WithLp.prod_dist_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_dist_eq_add (hp : 0 < p.toReal) (f g : WithLp p (α × β)) : dist f g =
 (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)
参数：hp : 0 < p.toReal；f g : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem prod_dist_eq_add (hp : 0 < p.toReal) (f g : WithLp p (α × β)) :
    dist f g = (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)
/-
**WithLp.prod_dist_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_dist_eq_sup (f g : WithLp ∞ (α × β)) : dist f g = dist f.fst g.fst ⊔ 
dist f.snd g.snd
参数：f g : WithLp ∞ (α × β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_dist_eq_sup (f g : WithLp ∞ (α × β)) :
    dist f g = dist f.fst g.fst ⊔ dist f.snd g.snd := rfl

end Dist

section Norm

variable [Norm α] [Norm β]

/-- Endowing the space `WithLp p (α × β)` with the `L^p` norm. We register this instance
separate from `WithLp.instProdSeminormedAddCommGroup` since the latter requires the type class
hypothesis `[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future norm-like structure on `WithLp p (α × β)` for
`p < 1` satisfying a relaxed triangle inequality. These are called *quasi-norms*. -/
/-
**WithLp.instProdNorm** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdNorm : Norm (WithLp p (α × β)) where norm f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Endowing the space `WithLp p (α × β)` with the `L^p` norm. We register this inst
ance
separate from `WithLp.instProdSeminormedAddCommGroup` since the latter requires 
the type class
hypothesis `[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future norm-like structure on `WithLp p
 (α × β)` for
`p < 1` satisfying a relaxed triangle inequality. These are called *quasi-norms*
.
-/
instance instProdNorm : Norm (WithLp p (α × β)) where
  norm f :=
    if _hp : p = 0 then
      (if ‖f.fst‖ = 0 then 0 else 1) + (if ‖f.snd‖ = 0 then 0 else 1)
    else if p = ∞ then
      ‖f.fst‖ ⊔ ‖f.snd‖
    else
      (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)

variable {p α β}

@[simp]
/-
**WithLp.prod_norm_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_norm_eq_card (f : WithLp 0 (α × β)) : ‖f‖ = (if ‖f.fst‖ = 0 then 0 el
se 1) + (if ‖f.snd‖ = 0 then 0 else 1)
参数：f : WithLp 0 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem prod_norm_eq_card (f : WithLp 0 (α × β)) :
    ‖f‖ = (if ‖f.fst‖ = 0 then 0 else 1) + (if ‖f.snd‖ = 0 then 0 else 1) := by
  convert! if_pos rfl
/-
**WithLp.prod_norm_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_norm_eq_sup (f : WithLp ∞ (α × β)) : ‖f‖ = ‖f.fst‖ ⊔ ‖f.snd‖
参数：f : WithLp ∞ (α × β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_norm_eq_sup (f : WithLp ∞ (α × β)) : ‖f‖ = ‖f.fst‖ ⊔ ‖f.snd‖ := rfl
/-
**WithLp.prod_norm_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_norm_eq_add (hp : 0 < p.toReal) (f : WithLp p (α × β)) : ‖f‖ = (‖f.fs
t‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)
参数：hp : 0 < p.toReal；f : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem prod_norm_eq_add (hp : 0 < p.toReal) (f : WithLp p (α × β)) :
    ‖f‖ = (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

end Norm

end DistNorm

section Aux

/-!
### The uniformity on finite `L^p` products is the product uniformity

In this section, we put the `L^p` edistance on `WithLp p (α × β)`, and we check that the uniformity
coming from this edistance coincides with the product uniformity, by showing that the canonical
map to the Prod type (with the `L^∞` distance) is a uniform embedding, as it is both Lipschitz and
antiLipschitz.

We only register this emetric space structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.

TODO: the results about uniformity and bornology should be using the tools in
`Mathlib.Topology.MetricSpace.Bilipschitz`, so that they can be inlined in the next section and
the only remaining results are about `Lipschitz` and `Antilipschitz`.
-/


variable [hp : Fact (1 ≤ p)]

/-- Endowing the space `WithLp p (α × β)` with the `L^p` pseudoemetric structure. This definition is
not satisfactory, as it does not register the fact that the topology and the uniform structure
coincide with the product one. Therefore, we do not register it as an instance. Using this as a
temporary pseudoemetric space instance, we will show that the uniform structure is equal (but not
defeq) to the product one, and then register an instance in which we replace the uniform structure
by the product one using this pseudoemetric space and `PseudoEMetricSpace.replaceUniformity`. -/
@[instance_reducible]
/-
**WithLp.prodPseudoEMetricAux** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：prodPseudoEMetricAux [PseudoEMetricSpace α] [PseudoEMetricSpace β] : Pseud
oEMetricSpace (WithLp p (α × β)) where edist_self
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WithLp.prod_edist_self`：prod_edist_self (f : WithLp p (α × β)) : edist f
 f = 0
· 使用定理 `WithLp.prod_edist_comm`：prod_edist_comm (f g : WithLp p (α × β)) : edist
 f g = edist g f

--- 原说明 ---
Endowing the space `WithLp p (α × β)` with the `L^p` pseudoemetric structure. Th
is definition is
not satisfactory, as it does not register the fact that the topology and the uni
form structure
coincide with the product one. Therefore, we do not register it as an instance. 
Using this as a
temporary pseudoemetric space instance, we will show that the uniform structure 
is equal (but not
defeq) to the product one, and then register an instance in which we replace the
 uniform structure
by the product one using this pseudoemetric space and `PseudoEMetricSpace.replac
eUniformity`.
-/
def prodPseudoEMetricAux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    PseudoEMetricSpace (WithLp p (α × β)) where
  edist_self := prod_edist_self p
  edist_comm := prod_edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
    · simp only [prod_edist_eq_sup]
      exact sup_le ((edist_triangle _ g.fst _).trans <| add_le_add le_sup_left le_sup_left)
        ((edist_triangle _ g.snd _).trans <| add_le_add le_sup_right le_sup_right)
    · simp only [prod_edist_eq_add (zero_lt_one.trans_le hp)]
      calc
        (edist f.fst h.fst ^ p.toReal + edist f.snd h.snd ^ p.toReal) ^ (1 / p.toReal) ≤
            ((edist f.fst g.fst + edist g.fst h.fst) ^ p.toReal +
              (edist f.snd g.snd + edist g.snd h.snd) ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr <;> apply edist_triangle
        _ ≤
            (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) +
              (edist g.fst h.fst ^ p.toReal + edist g.snd h.snd ^ p.toReal) ^ (1 / p.toReal) := by
          have := ENNReal.Lp_add_le {0, 1}
            (if · = 0 then edist f.fst g.fst else edist f.snd g.snd)
            (if · = 0 then edist g.fst h.fst else edist g.snd h.snd) hp
          simp only [Finset.mem_singleton, not_false_eq_true, Finset.sum_insert,
            Finset.sum_singleton, reduceCtorEq] at this
          exact this

attribute [local instance] WithLp.prodPseudoEMetricAux

variable {α β}

/-- An auxiliary lemma used twice in the proof of `WithLp.prodPseudoMetricAux` below. Not intended
for use outside this file. -/
/-
**WithLp.prod_sup_edist_ne_top_aux** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_sup_edist_ne_top_aux [PseudoMetricSpace α] [PseudoMetricSpace β] (f g
 : WithLp ∞ (α × β)) : edist f.fst g.fst ⊔ edist f.snd g.snd != ⊤
参数：f g : WithLp ∞ (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PseudoMetricSpace.edist_dist`：∀ {α : Type u} [self : PseudoMetricSpace α
] (x y : α), PseudoMetricSpace.edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
An auxiliary lemma used twice in the proof of `WithLp.prodPseudoMetricAux` below
. Not intended
for use outside this file.
-/
theorem prod_sup_edist_ne_top_aux [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f g : WithLp ∞ (α × β)) :
    edist f.fst g.fst ⊔ edist f.snd g.snd ≠ ⊤ :=
  ne_of_lt <| by simp [edist, PseudoMetricSpace.edist_dist]

variable (α β)

/-- Endowing the space `WithLp p (α × β)` with the `L^p` pseudometric structure. This definition is
not satisfactory, as it does not register the fact that the topology, the uniform structure, and the
bornology coincide with the product ones. Therefore, we do not register it as an instance. Using
this as a temporary pseudoemetric space instance, we will show that the uniform structure is equal
(but not defeq) to the product one, and then register an instance in which we replace the uniform
structure and the bornology by the product ones using this pseudometric space,
`PseudoMetricSpace.replaceUniformity`, and `PseudoMetricSpace.replaceBornology`.

See note [reducible non-instances] -/
/-
**WithLp.prodPseudoMetricAux** 是 Mathlib 中的一个缩写定义，位于命名空间 `WithLp`。
形式化陈述：prodPseudoMetricAux [PseudoMetricSpace α] [PseudoMetricSpace β] : PseudoMe
tricSpace (WithLp p (α × β))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Endowing the space `WithLp p (α × β)` with the `L^p` pseudometric structure. Thi
s definition is
not satisfactory, as it does not register the fact that the topology, the unifor
m structure, and the
bornology coincide with the product ones. Therefore, we do not register it as an
 instance. Using
this as a temporary pseudoemetric space instance, we will show that the uniform 
structure is equal
(but not defeq) to the product one, and then register an instance in which we re
place the uniform
structure and the bornology by the product ones using this pseudometric space,
`PseudoMetricSpace.replaceUniformity`, and `PseudoMetricSpace.replaceBornology`.

See note [reducible non-instances]
-/
abbrev prodPseudoMetricAux [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (WithLp p (α × β)) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · simp [prod_dist_eq_sup]
      · simp only [dist, one_div, dite_eq_ite]
        split_ifs with hp' <;> positivity)
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · refine ENNReal.eq_of_forall_le_nnreal_iff fun r ↦ ?_
      simp [prod_edist_eq_sup, prod_dist_eq_sup]
    · have : 0 < p.toReal := by rw [ENNReal.toReal_pos_iff_ne_top]; rintro rfl; norm_num at h
      simp only [prod_edist_eq_add, edist_dist, one_div, prod_dist_eq_add, this]
      rw [← ENNReal.ofReal_rpow_of_nonneg, ENNReal.ofReal_add, ← ENNReal.ofReal_rpow_of_nonneg,
        ← ENNReal.ofReal_rpow_of_nonneg] <;> simp [Real.rpow_nonneg, add_nonneg]

attribute [local instance] WithLp.prodPseudoMetricAux

variable {α β} in
/-
**WithLp.edist_proj_le_edist_aux** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem edist_proj_le_edist_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    (x y : WithLp p (α × β)) :
    edist x.fst y.fst ≤ edist x y ∧ edist x.snd y.snd ≤ edist x y := by
  rcases p.dichotomy with (rfl | h)
  · simp [prod_edist_eq_sup]
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (zero_lt_one.trans_le h).ne'
    rw [prod_edist_eq_add (zero_lt_one.trans_le h)]
    constructor
    · calc
        edist x.fst y.fst ≤ (edist x.fst y.fst ^ p.toReal) ^ (1 / p.toReal) := by
          simp only [← ENNReal.rpow_mul, cancel, ENNReal.rpow_one, le_refl]
        _ ≤ (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr
          simp only [self_le_add_right]
    · calc
        edist x.snd y.snd ≤ (edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          simp only [← ENNReal.rpow_mul, cancel, ENNReal.rpow_one, le_refl]
        _ ≤ (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr
          simp only [self_le_add_left]
/-
**WithLp.prod_lipschitzWith_ofLp_aux** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma prod_lipschitzWith_ofLp_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith 1 (@ofLp p (α × β)) := by
  intro x y
  change max _ _ ≤ _
  rw [ENNReal.coe_one, one_mul, sup_le_iff]
  exact edist_proj_le_edist_aux p x y
/-
**WithLp.prod_antilipschitzWith_ofLp_aux** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma prod_antilipschitzWith_ofLp_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith ((2 : ℝ≥0) ^ (1 / p).toReal) (@ofLp p (α × β)) := by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp [edist]
  · have pos : 0 < p.toReal := by positivity
    have nonneg : 0 ≤ 1 / p.toReal := by positivity
    have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (ne_of_gt pos)
    rw [prod_edist_eq_add pos, ENNReal.toReal_div 1 p]
    simp only [edist, ENNReal.toReal_one]
    calc
      (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) ≤
          (edist (ofLp x) (ofLp y) ^ p.toReal +
          edist (ofLp x) (ofLp y) ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr <;> simp [edist]
      _ = (2 ^ (1 / p.toReal) : ℝ≥0) * edist (ofLp x) (ofLp y) := by
        simp only [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ nonneg, ← ENNReal.rpow_mul, cancel,
          ENNReal.rpow_one, ENNReal.coe_rpow_of_nonneg _ nonneg, coe_ofNat]
/-
**WithLp.isUniformInducing_ofLp_aux** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isUniformInducing_ofLp_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    IsUniformInducing (@ofLp p (α × β)) :=
  (prod_antilipschitzWith_ofLp_aux p α β).isUniformInducing
    (prod_lipschitzWith_ofLp_aux p α β).uniformContinuous

set_option backward.privateInPublic true in
/-
**WithLp.prod_uniformity_aux** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma prod_uniformity_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    𝓤 (WithLp p (α × β)) = 𝓤[UniformSpace.comap ofLp inferInstance] := by
  rw [← (isUniformInducing_ofLp_aux p α β).comap_uniformity]
  rfl
/-
**WithLp.instProdBornology** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdBornology (p : Real>=0∞) (α β : Type*) [Bornology α] [Bornology β]
 : Bornology (WithLp p (α × β))
参数：p : Real>=0∞；α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instProdBornology (p : ℝ≥0∞) (α β : Type*) [Bornology α] [Bornology β] :
    Bornology (WithLp p (α × β)) := Bornology.induced ofLp

set_option backward.privateInPublic true in
/-
**WithLp.prod_cobounded_aux** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma prod_cobounded_aux [PseudoMetricSpace α] [PseudoMetricSpace β] :
    @cobounded _ PseudoMetricSpace.toBornology = cobounded (WithLp p (α × β)) :=
  le_antisymm (prod_antilipschitzWith_ofLp_aux p α β).tendsto_cobounded.le_comap
      (prod_lipschitzWith_ofLp_aux p α β).comap_cobounded_le

end Aux

/-! ### Instances on `L^p` products -/

section TopologicalSpace

variable [TopologicalSpace α] [TopologicalSpace β]

/-
**WithLp.instProdTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdTopologicalSpace : TopologicalSpace (WithLp p (α × β))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instProdTopologicalSpace : TopologicalSpace (WithLp p (α × β)) :=
  instTopologicalSpaceProd.induced ofLp

@[continuity, fun_prop]
/-
**WithLp.prod_continuous_toLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：prod_continuous_toLp : Continuous (@toLp p (α × β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
lemma prod_continuous_toLp : Continuous (@toLp p (α × β)) :=
  continuous_induced_rng.2 continuous_id

@[continuity, fun_prop]
/-
**WithLp.prod_continuous_ofLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：prod_continuous_ofLp : Continuous (@ofLp p (α × β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
lemma prod_continuous_ofLp : Continuous (@ofLp p (α × β)) := continuous_induced_dom

/-- `WithLp.equiv` as a homeomorphism. -/
/-
**WithLp.homeomorphProd** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：homeomorphProd : WithLp p (α × β) ≃ₜ α × β where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithLp.equiv` as a homeomorphism.
-/
def homeomorphProd : WithLp p (α × β) ≃ₜ α × β where
  toEquiv := WithLp.equiv p (α × β)

@[simp]
/-
**WithLp.toEquiv_homeomorphProd** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：toEquiv_homeomorphProd : (homeomorphProd p α β).toEquiv = WithLp.equiv p (
α × β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEquiv_homeomorphProd : (homeomorphProd p α β).toEquiv = WithLp.equiv p (α × β) := rfl

@[fun_prop]
/-
**WithLp.continuous_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) (α : Type u_2) (β : Type u_3) [inst : TopologicalSpace α] 
[inst_1 : TopologicalSpace β],   Continuous WithLp.fst
参数：p : ENNReal；α : Type u_2；β : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用引理 `WithLp.prod_continuous_ofLp`：prod_continuous_ofLp : Continuous (@ofLp p 
(α × β))
-/
protected lemma continuous_fst : Continuous (@WithLp.fst p α β) :=
  continuous_fst.comp <| prod_continuous_ofLp ..

@[fun_prop]
/-
**WithLp.continuous_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) (α : Type u_2) (β : Type u_3) [inst : TopologicalSpace α] 
[inst_1 : TopologicalSpace β],   Continuous WithLp.snd
参数：p : ENNReal；α : Type u_2；β : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用引理 `WithLp.prod_continuous_ofLp`：prod_continuous_ofLp : Continuous (@ofLp p 
(α × β))
-/
protected lemma continuous_snd : Continuous (@WithLp.snd p α β) :=
  continuous_snd.comp <| prod_continuous_ofLp ..

variable [T0Space α] [T0Space β]
/-
**WithLp.instProdT0Space** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdT0Space : T0Space (WithLp p (α × β))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t0Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T0Space X] (h : X ≃ₜ Y),   T0Space Y
-/
instance instProdT0Space : T0Space (WithLp p (α × β)) :=
  (homeomorphProd p α β).symm.t0Space

variable [SecondCountableTopology α] [SecondCountableTopology β]
/-
**WithLp.secondCountableTopology** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：secondCountableTopology : SecondCountableTopology (WithLp p (α × β))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.secondCountableTopology`：∀ {X : Type u_1} {Y : Type u_2} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [SecondCountableTopology Y
]   (h : X ≃ₜ Y), Second…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
-/
instance secondCountableTopology : SecondCountableTopology (WithLp p (α × β)) :=
  (homeomorphProd p α β).secondCountableTopology

end TopologicalSpace

section UniformSpace

variable [UniformSpace α] [UniformSpace β]

/-
**WithLp.instProdUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdUniformSpace : UniformSpace (WithLp p (α × β))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instProdUniformSpace : UniformSpace (WithLp p (α × β)) :=
  instUniformSpaceProd.comap ofLp

@[fun_prop]
/-
**WithLp.prod_uniformContinuous_toLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：prod_uniformContinuous_toLp : UniformContinuous (@toLp p (α × β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_comap'`：uniformContinuous_comap' {f : γ -> β} {g : α -
> γ} [v : UniformSpace β] [u : UniformSpace α] (h : UniformContinuous (f ∘ g)) :
 @UniformConti…
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
lemma prod_uniformContinuous_toLp : UniformContinuous (@toLp p (α × β)) :=
  uniformContinuous_comap' uniformContinuous_id

@[fun_prop]
/-
**WithLp.prod_uniformContinuous_ofLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：prod_uniformContinuous_ofLp : UniformContinuous (@ofLp p (α × β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_comap`：uniformContinuous_comap {f : α -> β} [u : Unifo
rmSpace β] : @UniformContinuous α β (UniformSpace.comap f u) u f
-/
lemma prod_uniformContinuous_ofLp : UniformContinuous (@ofLp p (α × β)) :=
  uniformContinuous_comap

/-- `WithLp.equiv` as a uniform isomorphism. -/
/-
**WithLp.uniformEquivProd** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：uniformEquivProd : WithLp p (α × β) ≃ᵤ α × β where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WithLp.prod_uniformContinuous_ofLp`：prod_uniformContinuous_ofLp : Unifor
mContinuous (@ofLp p (α × β))
· 使用引理 `WithLp.prod_uniformContinuous_toLp`：prod_uniformContinuous_toLp : Unifor
mContinuous (@toLp p (α × β))

--- 原说明 ---
`WithLp.equiv` as a uniform isomorphism.
-/
def uniformEquivProd : WithLp p (α × β) ≃ᵤ α × β where
  toEquiv := WithLp.equiv p (α × β)
  uniformContinuous_toFun := prod_uniformContinuous_ofLp p α β
  uniformContinuous_invFun := prod_uniformContinuous_toLp p α β

@[simp]
/-
**WithLp.toHomeomorph_uniformEquivProd** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：toHomeomorph_uniformEquivProd : (uniformEquivProd p α β).toHomeomorph = ho
meomorphProd p α β
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toHomeomorph_uniformEquivProd :
    (uniformEquivProd p α β).toHomeomorph = homeomorphProd p α β := rfl

@[simp]
/-
**WithLp.toEquiv_uniformEquivProd** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：toEquiv_uniformEquivProd : (uniformEquivProd p α β).toEquiv = WithLp.equiv
 p (α × β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEquiv_uniformEquivProd : (uniformEquivProd p α β).toEquiv = WithLp.equiv p (α × β) := rfl

variable [CompleteSpace α] [CompleteSpace β]
/-
**WithLp.instProdCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdCompleteSpace : CompleteSpace (WithLp p (α × β))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `UniformEquiv.completeSpace_iff`：completeSpace_iff (h : α ≃ᵤ β) : Complet
eSpace α ↔ CompleteSpace β
-/
instance instProdCompleteSpace : CompleteSpace (WithLp p (α × β)) :=
  (uniformEquivProd p α β).completeSpace_iff.2 inferInstance

end UniformSpace

section ContinuousLinearEquiv

variable [TopologicalSpace α] [TopologicalSpace β]
variable [Semiring 𝕜] [AddCommGroup α] [AddCommGroup β]
variable [Module 𝕜 α] [Module 𝕜 β]

/-- `WithLp.equiv` as a continuous linear equivalence. -/
-- This is not specific to products and should be generalised!
@[simps!]
/-
**WithLp.prodContinuousLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：prodContinuousLinearEquiv : WithLp p (α × β) ≃L[𝕜] α × β where toLinearEqu
iv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WithLp.prod_continuous_ofLp`：prod_continuous_ofLp : Continuous (@ofLp p 
(α × β))
· 使用引理 `WithLp.prod_continuous_toLp`：prod_continuous_toLp : Continuous (@toLp p 
(α × β))
-/
def prodContinuousLinearEquiv : WithLp p (α × β) ≃L[𝕜] α × β where
  toLinearEquiv := WithLp.linearEquiv _ _ _
  continuous_toFun := prod_continuous_ofLp p α β
  continuous_invFun := prod_continuous_toLp p α β

@[simp]
/-
**WithLp.prodContinuousLinearEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`
。
形式化陈述：prodContinuousLinearEquiv_symm_apply (x : α × β) : (prodContinuousLinearEq
uiv p 𝕜 α β).symm x = toLp p x
参数：x : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prodContinuousLinearEquiv_symm_apply (x : α × β) :
    (prodContinuousLinearEquiv p 𝕜 α β).symm x = toLp p x := rfl

/-- `WithLp.fst` as a continuous linear map. -/
@[simps! coe apply]
/-
**WithLp.fstL** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：fstL : WithLp p (α × β) ->L[𝕜] α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithLp.fst` as a continuous linear map.
-/
def fstL : WithLp p (α × β) →L[𝕜] α where
  __ := fstₗ ..

/-- `WithLp.snd` as a continuous linear map. -/
@[simps! coe apply]
/-
**WithLp.sndL** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：sndL : WithLp p (α × β) ->L[𝕜] β where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithLp.snd` as a continuous linear map.
-/
def sndL : WithLp p (α × β) →L[𝕜] β where
  __ := sndₗ ..

end ContinuousLinearEquiv

/-! Throughout the rest of the file, we assume `1 ≤ p`. -/
variable [hp : Fact (1 ≤ p)]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `PseudoEMetricSpace` instance on the product of two pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
/-
**WithLp.instProdPseudoEMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdPseudoEMetricSpace [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
 PseudoEMetricSpace (WithLp p (α × β))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PseudoEMetricSpace` instance on the product of two pseudoemetric spaces, using 
the
`L^p` pseudoedistance, and having as uniformity the product uniformity.
-/
instance instProdPseudoEMetricSpace [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    PseudoEMetricSpace (WithLp p (α × β)) :=
  (prodPseudoEMetricAux p α β).replaceUniformity (prod_uniformity_aux p α β).symm

/-- `EMetricSpace` instance on the product of two emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
/-
**WithLp.instProdEMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdEMetricSpace [EMetricSpace α] [EMetricSpace β] : EMetricSpace (Wit
hLp p (α × β))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`EMetricSpace` instance on the product of two emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity.
-/
instance instProdEMetricSpace [EMetricSpace α] [EMetricSpace β] : EMetricSpace (WithLp p (α × β)) :=
  EMetricSpace.ofT0PseudoEMetricSpace (WithLp p (α × β))

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `PseudoMetricSpace` instance on the product of two pseudometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
/-
**WithLp.instProdPseudoMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdPseudoMetricSpace [PseudoMetricSpace α] [PseudoMetricSpace β] : Ps
eudoMetricSpace (WithLp p (α × β))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PseudoMetricSpace` instance on the product of two pseudometric spaces, using th
e
`L^p` distance, and having as uniformity the product uniformity.
-/
instance instProdPseudoMetricSpace [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (WithLp p (α × β)) :=
  ((prodPseudoMetricAux p α β).replaceUniformity
    (prod_uniformity_aux p α β).symm).replaceBornology
    fun s => Filter.ext_iff.1 (prod_cobounded_aux p α β).symm sᶜ

/-- `MetricSpace` instance on the product of two metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/
/-
**WithLp.instProdMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdMetricSpace [MetricSpace α] [MetricSpace β] : MetricSpace (WithLp 
p (α × β))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MetricSpace` instance on the product of two metric spaces, using the `L^p` dist
ance,
and having as uniformity the product uniformity.
-/
instance instProdMetricSpace [MetricSpace α] [MetricSpace β] : MetricSpace (WithLp p (α × β)) :=
  MetricSpace.ofT0PseudoMetricSpace _

variable {p α β}
/-
**WithLp.prod_nndist_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_nndist_eq_add [PseudoMetricSpace α] [PseudoMetricSpace β] (hp : p != 
∞) (x y : WithLp p (α × β)) : nndist x y = (nndist x.fst y.fst ^ p.toReal + nndi
st x.snd y.snd ^ p.toReal) ^ (1 / p.toReal)
参数：hp : p != ∞；x y : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `WithLp.prod_dist_eq_add`：prod_dist_eq_add (hp : 0 < p.toReal) (f g : Wit
hLp p (α × β)) : dist f g = (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.
toReal) ^ (1 …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toReal_pos_iff_ne_top`：toReal_pos_iff_ne_top (p : Real>=0∞) [Fac
t (1 <= p)] : 0 < p.toReal ↔ p != ∞
-/
theorem prod_nndist_eq_add [PseudoMetricSpace α] [PseudoMetricSpace β]
    (hp : p ≠ ∞) (x y : WithLp p (α × β)) :
    nndist x y = (nndist x.fst y.fst ^ p.toReal + nndist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) :=
  NNReal.eq <| by
    push_cast
    exact prod_dist_eq_add (p.toReal_pos_iff_ne_top.mpr hp) _ _
/-
**WithLp.prod_nndist_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_nndist_eq_sup [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : With
Lp ∞ (α × β)) : nndist x y = nndist x.fst y.fst ⊔ nndist x.snd y.snd
参数：x y : WithLp ∞ (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_max`：coe_max (x y : Real>=0) : ((max x y : Real>=0) : Real) =
 max (x : Real) (y : Real)
· 使用定理 `WithLp.prod_dist_eq_sup`：prod_dist_eq_sup (f g : WithLp ∞ (α × β)) : dis
t f g = dist f.fst g.fst ⊔ dist f.snd g.snd
-/
theorem prod_nndist_eq_sup [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp ∞ (α × β)) :
    nndist x y = nndist x.fst y.fst ⊔ nndist x.snd y.snd :=
  NNReal.eq <| by
    push_cast
    exact prod_dist_eq_sup _ _
/-
**WithLp.edist_fst_le** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：edist_fst_le [PseudoEMetricSpace α] [PseudoEMetricSpace β] (x y : WithLp p
 (α × β)) : edist x.fst y.fst <= edist x y
参数：x y : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `_private.Mathlib.Analysis.Normed.Lp.ProdLp.0.WithLp.edist_proj_le_edist_
aux`：∀ (p : ENNReal) {α : Type u_2} {β : Type u_3} [hp : Fact (1 ≤ p)] [inst : P
seudoEMetricSpace α]   [inst_1 : PseudoEMetricSpace β] (x y : Wit…
-/
theorem edist_fst_le [PseudoEMetricSpace α] [PseudoEMetricSpace β] (x y : WithLp p (α × β)) :
    edist x.fst y.fst ≤ edist x y :=
  (edist_proj_le_edist_aux p x y).1
/-
**WithLp.edist_snd_le** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：edist_snd_le [PseudoEMetricSpace α] [PseudoEMetricSpace β] (x y : WithLp p
 (α × β)) : edist x.snd y.snd <= edist x y
参数：x y : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.Analysis.Normed.Lp.ProdLp.0.WithLp.edist_proj_le_edist_
aux`：∀ (p : ENNReal) {α : Type u_2} {β : Type u_3} [hp : Fact (1 ≤ p)] [inst : P
seudoEMetricSpace α]   [inst_1 : PseudoEMetricSpace β] (x y : Wit…
-/
theorem edist_snd_le [PseudoEMetricSpace α] [PseudoEMetricSpace β] (x y : WithLp p (α × β)) :
    edist x.snd y.snd ≤ edist x y :=
  (edist_proj_le_edist_aux p x y).2
/-
**WithLp.nndist_fst_le** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：nndist_fst_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p 
(α × β)) : nndist x.fst y.fst <= nndist x y
参数：x y : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.edist_fst_le`：edist_fst_le [PseudoEMetricSpace α] [PseudoEMetricS
pace β] (x y : WithLp p (α × β)) : edist x.fst y.fst <= edist x y
-/
theorem nndist_fst_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β)) :
    nndist x.fst y.fst ≤ nndist x y := by
  simpa [← coe_nnreal_ennreal_nndist] using edist_fst_le x y
/-
**WithLp.nndist_snd_le** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：nndist_snd_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p 
(α × β)) : nndist x.snd y.snd <= nndist x y
参数：x y : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.edist_snd_le`：edist_snd_le [PseudoEMetricSpace α] [PseudoEMetricS
pace β] (x y : WithLp p (α × β)) : edist x.snd y.snd <= edist x y
-/
theorem nndist_snd_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β)) :
    nndist x.snd y.snd ≤ nndist x y := by
  simpa [← coe_nnreal_ennreal_nndist] using edist_snd_le x y
/-
**WithLp.dist_fst_le** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：dist_fst_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α
 × β)) : dist x.fst y.fst <= dist x y
参数：x y : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithLp.nndist_fst_le`：nndist_fst_le [PseudoMetricSpace α] [PseudoMetricS
pace β] (x y : WithLp p (α × β)) : nndist x.fst y.fst <= nndist x y
-/
theorem dist_fst_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β)) :
    dist x.fst y.fst ≤ dist x y :=
  nndist_fst_le x y
/-
**WithLp.dist_snd_le** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：dist_snd_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α
 × β)) : dist x.snd y.snd <= dist x y
参数：x y : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithLp.nndist_snd_le`：nndist_snd_le [PseudoMetricSpace α] [PseudoMetricS
pace β] (x y : WithLp p (α × β)) : nndist x.snd y.snd <= nndist x y
-/
theorem dist_snd_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β)) :
    dist x.snd y.snd ≤ dist x y :=
  nndist_snd_le x y

variable (p α β)
/-
**WithLp.prod_lipschitzWith_ofLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：prod_lipschitzWith_ofLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] : Li
pschitzWith 1 (@ofLp p (α × β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.Normed.Lp.ProdLp.0.WithLp.prod_lipschitzWith_o
fLp_aux`：∀ (p : ENNReal) (α : Type u_2) (β : Type u_3) [hp : Fact (1 ≤ p)] [inst
 : PseudoEMetricSpace α]   [inst_1 : PseudoEMetricSpace β], Lipschitz…
-/
lemma prod_lipschitzWith_ofLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith 1 (@ofLp p (α × β)) :=
  prod_lipschitzWith_ofLp_aux p α β
/-
**WithLp.prod_antilipschitzWith_toLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：prod_antilipschitzWith_toLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] 
: AntilipschitzWith 1 (@toLp p (α × β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.to_rightInverse`：LipschitzWith.to_rightInverse [PseudoEMet
ricSpace α] [PseudoEMetricSpace β] {K : Real>=0} {f : α -> β} (hf : LipschitzWit
h K f) {g : β -> α}…
· 使用引理 `WithLp.prod_lipschitzWith_ofLp`：prod_lipschitzWith_ofLp [PseudoEMetricSp
ace α] [PseudoEMetricSpace β] : LipschitzWith 1 (@ofLp p (α × β))
· 使用引理 `WithLp.ofLp_toLp`：ofLp_toLp (x : V) : ofLp (toLp p x) = x
-/
lemma prod_antilipschitzWith_toLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith 1 (@toLp p (α × β)) :=
  (prod_lipschitzWith_ofLp p α β).to_rightInverse (ofLp_toLp p)
/-
**WithLp.prod_antilipschitzWith_ofLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：prod_antilipschitzWith_ofLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] 
: AntilipschitzWith ((2 : Real>=0) ^ (1 / p).toReal) (@ofLp p (α × β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.Normed.Lp.ProdLp.0.WithLp.prod_antilipschitzWi
th_ofLp_aux`：∀ (p : ENNReal) (α : Type u_2) (β : Type u_3) [hp : Fact (1 ≤ p)] [
inst : PseudoEMetricSpace α]   [inst_1 : PseudoEMetricSpace β], Antilipsc…
-/
lemma prod_antilipschitzWith_ofLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith ((2 : ℝ≥0) ^ (1 / p).toReal) (@ofLp p (α × β)) :=
  prod_antilipschitzWith_ofLp_aux p α β
/-
**WithLp.prod_lipschitzWith_toLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：prod_lipschitzWith_toLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] : Li
pschitzWith ((2 : Real>=0) ^ (1 / p).toReal) (@toLp p (α × β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.to_rightInverse`：to_rightInverse (hf : AntilipschitzWi
th K f) {g : β -> α} (hg : Function.RightInverse g f) : LipschitzWith K g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WithLp.prod_antilipschitzWith_ofLp`：prod_antilipschitzWith_ofLp [PseudoE
MetricSpace α] [PseudoEMetricSpace β] : AntilipschitzWith ((2 : Real>=0) ^ (1 / 
p).toReal) (@ofLp p (α ×…
· 使用引理 `WithLp.ofLp_toLp`：ofLp_toLp (x : V) : ofLp (toLp p x) = x
-/
lemma prod_lipschitzWith_toLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith ((2 : ℝ≥0) ^ (1 / p).toReal) (@toLp p (α × β)) :=
  (prod_antilipschitzWith_ofLp p α β).to_rightInverse (ofLp_toLp p)
/-
**WithLp.prod_isometry_ofLp_infty** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：prod_isometry_ofLp_infty [PseudoEMetricSpace α] [PseudoEMetricSpace β] : I
sometry (@ofLp ∞ (α × β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `WithLp.prod_lipschitzWith_ofLp`：prod_lipschitzWith_ofLp [PseudoEMetricSp
ace α] [PseudoEMetricSpace β] : LipschitzWith 1 (@ofLp p (α × β))
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.div_top`：∀ {a : ENNReal}, a / ⊤ = 0
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用引理 `WithLp.prod_antilipschitzWith_ofLp`：prod_antilipschitzWith_ofLp [PseudoE
MetricSpace α] [PseudoEMetricSpace β] : AntilipschitzWith ((2 : Real>=0) ^ (1 / 
p).toReal) (@ofLp p (α ×…
-/
lemma prod_isometry_ofLp_infty [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    Isometry (@ofLp ∞ (α × β)) :=
  fun x y =>
  le_antisymm (by simpa only [ENNReal.coe_one, one_mul] using prod_lipschitzWith_ofLp ∞ α β x y)
    (by
      simpa only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero, ENNReal.coe_one,
        one_mul] using prod_antilipschitzWith_ofLp ∞ α β x y)

/-- Seminormed group instance on the product of two normed groups, using the `L^p`
norm. -/
/-
**WithLp.instProdSeminormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdSeminormedAddCommGroup [SeminormedAddCommGroup α] [SeminormedAddCo
mmGroup β] : SeminormedAddCommGroup (WithLp p (α × β)) where dist_eq x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Seminormed group instance on the product of two normed groups, using the `L^p`
norm.
-/
instance instProdSeminormedAddCommGroup [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] :
    SeminormedAddCommGroup (WithLp p (α × β)) where
  dist_eq x y := by
    rcases p.dichotomy with (rfl | h)
    · simp only [prod_dist_eq_sup, prod_norm_eq_sup, dist_eq_norm, ← norm_neg_add]
      rfl
    · simp only [prod_dist_eq_add (zero_lt_one.trans_le h),
        prod_norm_eq_add (zero_lt_one.trans_le h), dist_eq_norm, ← norm_neg_add]
      rfl

@[fun_prop]
/-
**WithLp.isUniformInducing_toLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：isUniformInducing_toLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] : IsU
niformInducing (@toLp p (α × β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.isUniformInducing`：isUniformInducing (hf : Antilipschi
tzWith K f) (hfc : UniformContinuous f) : IsUniformInducing f
· 使用引理 `WithLp.prod_antilipschitzWith_toLp`：prod_antilipschitzWith_toLp [PseudoE
MetricSpace α] [PseudoEMetricSpace β] : AntilipschitzWith 1 (@toLp p (α × β))
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WithLp.prod_lipschitzWith_toLp`：prod_lipschitzWith_toLp [PseudoEMetricSp
ace α] [PseudoEMetricSpace β] : LipschitzWith ((2 : Real>=0) ^ (1 / p).toReal) (
@toLp p (α × β))
-/
lemma isUniformInducing_toLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    IsUniformInducing (@toLp p (α × β)) :=
  (prod_antilipschitzWith_toLp p α β).isUniformInducing
    (prod_lipschitzWith_toLp p α β).uniformContinuous

section
variable {β p}

/-
**WithLp.enorm_fst_le** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：enorm_fst_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : Wi
thLp p (α × β)) : ‖x.fst‖ₑ <= ‖x‖ₑ
参数：x : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `WithLp.edist_fst_le`：edist_fst_le [PseudoEMetricSpace α] [PseudoEMetricS
pace β] (x y : WithLp p (α × β)) : edist x.fst y.fst <= edist x y
-/
theorem enorm_fst_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.fst‖ₑ ≤ ‖x‖ₑ := by
  simpa using edist_fst_le x 0
/-
**WithLp.enorm_snd_le** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：enorm_snd_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : Wi
thLp p (α × β)) : ‖x.snd‖ₑ <= ‖x‖ₑ
参数：x : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `WithLp.edist_snd_le`：edist_snd_le [PseudoEMetricSpace α] [PseudoEMetricS
pace β] (x y : WithLp p (α × β)) : edist x.snd y.snd <= edist x y
-/
theorem enorm_snd_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.snd‖ₑ ≤ ‖x‖ₑ := by
  simpa using edist_snd_le x 0
/-
**WithLp.nnnorm_fst_le** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：nnnorm_fst_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : W
ithLp p (α × β)) : ‖x.fst‖₊ <= ‖x‖₊
参数：x : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nndist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E
), nndist a 0 = ‖a‖₊
· 使用定理 `WithLp.nndist_fst_le`：nndist_fst_le [PseudoMetricSpace α] [PseudoMetricS
pace β] (x y : WithLp p (α × β)) : nndist x.fst y.fst <= nndist x y
-/
theorem nnnorm_fst_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.fst‖₊ ≤ ‖x‖₊ := by
  simpa using nndist_fst_le x 0
/-
**WithLp.nnnorm_snd_le** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：nnnorm_snd_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : W
ithLp p (α × β)) : ‖x.snd‖₊ <= ‖x‖₊
参数：x : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nndist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E
), nndist a 0 = ‖a‖₊
· 使用定理 `WithLp.nndist_snd_le`：nndist_snd_le [PseudoMetricSpace α] [PseudoMetricS
pace β] (x y : WithLp p (α × β)) : nndist x.snd y.snd <= nndist x y
-/
theorem nnnorm_snd_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.snd‖₊ ≤ ‖x‖₊ := by
  simpa using nndist_snd_le x 0
/-
**WithLp.norm_fst_le** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：norm_fst_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : Wit
hLp p (α × β)) : ‖x.fst‖ <= ‖x‖
参数：x : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `WithLp.dist_fst_le`：dist_fst_le [PseudoMetricSpace α] [PseudoMetricSpace
 β] (x y : WithLp p (α × β)) : dist x.fst y.fst <= dist x y
-/
theorem norm_fst_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.fst‖ ≤ ‖x‖ := by
  simpa using dist_fst_le x 0
/-
**WithLp.norm_snd_le** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：norm_snd_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : Wit
hLp p (α × β)) : ‖x.snd‖ <= ‖x‖
参数：x : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `WithLp.dist_snd_le`：dist_snd_le [PseudoMetricSpace α] [PseudoMetricSpace
 β] (x y : WithLp p (α × β)) : dist x.snd y.snd <= dist x y
-/
theorem norm_snd_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.snd‖ ≤ ‖x‖ := by
  simpa using dist_snd_le x 0

end

/-- normed group instance on the product of two normed groups, using the `L^p` norm. -/
/-
**WithLp.instProdNormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdNormedAddCommGroup [NormedAddCommGroup α] [NormedAddCommGroup β] :
 NormedAddCommGroup (WithLp p (α × β))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
normed group instance on the product of two normed groups, using the `L^p` norm.
-/
instance instProdNormedAddCommGroup [NormedAddCommGroup α] [NormedAddCommGroup β] :
    NormedAddCommGroup (WithLp p (α × β)) :=
  { instProdSeminormedAddCommGroup p α β with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
/-
**WithLp.** 是 Mathlib 中的一个示例，位于命名空间 `WithLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [NormedAddCommGroup α] [NormedAddCommGroup β] :
    (instProdNormedAddCommGroup p α β).toMetricSpace.toUniformSpace.toTopologicalSpace =
    instProdTopologicalSpace p α β :=
  rfl
/-
**WithLp.** 是 Mathlib 中的一个示例，位于命名空间 `WithLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [NormedAddCommGroup α] [NormedAddCommGroup β] :
    (instProdNormedAddCommGroup p α β).toMetricSpace.toUniformSpace = instProdUniformSpace p α β :=
  rfl
/-
**WithLp.** 是 Mathlib 中的一个示例，位于命名空间 `WithLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [NormedAddCommGroup α] [NormedAddCommGroup β] :
    (instProdNormedAddCommGroup p α β).toMetricSpace.toBornology = instProdBornology p α β :=
  rfl

section norm_of

variable {p α β}

/-
**WithLp.prod_norm_eq_of_nat** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_norm_eq_of_nat [Norm α] [Norm β] (n : Nat) (h : p = n) (f : WithLp p 
(α × β)) : ‖f‖ = (‖f.fst‖ ^ n + ‖f.snd‖ ^ n) ^ (1 / (n : Real))
参数：n : Nat；h : p = n；f : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toReal_pos_iff_ne_top`：toReal_pos_iff_ne_top (p : Real>=0∞) [Fac
t (1 <= p)] : 0 < p.toReal ↔ p != ∞
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `ENNReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : Real>=0∞) != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.prod_norm_eq_add`：prod_norm_eq_add (hp : 0 < p.toReal) (f : WithL
p p (α × β)) : ‖f‖ = (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `ENNReal.toReal_natCast`：toReal_natCast (n : Nat) : (n : Real>=0∞).toReal
 = n
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_norm_eq_of_nat [Norm α] [Norm β] (n : ℕ) (h : p = n) (f : WithLp p (α × β)) :
    ‖f‖ = (‖f.fst‖ ^ n + ‖f.snd‖ ^ n) ^ (1 / (n : ℝ)) := by
  have := p.toReal_pos_iff_ne_top.mpr (ne_of_eq_of_ne h <| ENNReal.natCast_ne_top n)
  simp only [one_div, h, Real.rpow_natCast, ENNReal.toReal_natCast,
    prod_norm_eq_add this]

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
/-
**WithLp.prod_nnnorm_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_nnnorm_eq_add (hp : p != ∞) (f : WithLp p (α × β)) : ‖f‖₊ = (‖f.fst‖₊
 ^ p.toReal + ‖f.snd‖₊ ^ p.toReal) ^ (1 / p.toReal)
参数：hp : p != ∞；f : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.prod_norm_eq_add`：prod_norm_eq_add (hp : 0 < p.toReal) (f : WithL
p p (α × β)) : ‖f‖ = (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toReal_pos_iff_ne_top`：toReal_pos_iff_ne_top (p : Real>=0∞) [Fac
t (1 <= p)] : 0 < p.toReal ↔ p != ∞
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_nnnorm_eq_add (hp : p ≠ ∞) (f : WithLp p (α × β)) :
    ‖f‖₊ = (‖f.fst‖₊ ^ p.toReal + ‖f.snd‖₊ ^ p.toReal) ^ (1 / p.toReal) := by
  ext
  simp [prod_norm_eq_add (p.toReal_pos_iff_ne_top.mpr hp)]
/-
**WithLp.prod_nnnorm_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_nnnorm_eq_sup (f : WithLp ∞ (α × β)) : ‖f‖₊ = ‖f.fst‖₊ ⊔ ‖f.snd‖₊
参数：f : WithLp ∞ (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
-/
theorem prod_nnnorm_eq_sup (f : WithLp ∞ (α × β)) : ‖f‖₊ = ‖f.fst‖₊ ⊔ ‖f.snd‖₊ := by
  ext
  norm_cast
/-
**WithLp.prod_nnnorm_ofLp** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SeminormedAddCommGroup α] [inst_1 
: SeminormedAddCommGroup β]   (f : WithLp ⊤ (α × β)), ‖f.ofLp‖₊ = ‖f‖₊
参数：f : WithLp ⊤ (α × β)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.prod_nnnorm_eq_sup`：prod_nnnorm_eq_sup (f : WithLp ∞ (α × β)) : ‖
f‖₊ = ‖f.fst‖₊ ⊔ ‖f.snd‖₊
· 使用定理 `Prod.nnnorm_def`：∀ {E : Type u_2} {F : Type u_3} [inst : SeminormedAddGr
oup E] [inst_1 : SeminormedAddGroup F] (x : E × F),   ‖x‖₊ = max ‖x.1‖₊ ‖x.2‖₊
· 使用定理 `WithLp.ofLp_fst`：∀ {p : ENNReal} {α : Type u_2} {β : Type u_3} (x : With
Lp p (α × β)), x.ofLp.1 = x.fst
· 使用定理 `WithLp.ofLp_snd`：∀ {p : ENNReal} {α : Type u_2} {β : Type u_3} (x : With
Lp p (α × β)), x.ofLp.2 = x.snd
-/
@[simp] lemma prod_nnnorm_ofLp (f : WithLp ∞ (α × β)) : ‖ofLp f‖₊ = ‖f‖₊ := by
  rw [prod_nnnorm_eq_sup, Prod.nnnorm_def, ofLp_fst, ofLp_snd]
/-
**WithLp.prod_nnnorm_toLp** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SeminormedAddCommGroup α] [inst_1 
: SeminormedAddCommGroup β] (f : α × β),   ‖WithLp.toLp ⊤ f‖₊ = ‖f‖₊
参数：f : α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `WithLp.prod_nnnorm_ofLp`：∀ {α : Type u_2} {β : Type u_3} [inst : Seminor
medAddCommGroup α] [inst_1 : SeminormedAddCommGroup β]   (f : WithLp ⊤ (α × β)),
 ‖f.ofLp‖₊ = …
-/
@[simp] lemma prod_nnnorm_toLp (f : α × β) : ‖toLp ⊤ f‖₊ = ‖f‖₊ :=
  (prod_nnnorm_ofLp _).symm
/-
**WithLp.prod_norm_ofLp** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SeminormedAddCommGroup α] [inst_1 
: SeminormedAddCommGroup β]   (f : WithLp ⊤ (α × β)), ‖f.ofLp‖ = ‖f‖
参数：f : WithLp ⊤ (α × β)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `WithLp.prod_nnnorm_ofLp`：∀ {α : Type u_2} {β : Type u_3} [inst : Seminor
medAddCommGroup α] [inst_1 : SeminormedAddCommGroup β]   (f : WithLp ⊤ (α × β)),
 ‖f.ofLp‖₊ = …
-/
@[simp] lemma prod_norm_ofLp (f : WithLp ∞ (α × β)) : ‖ofLp f‖ = ‖f‖ :=
  congr_arg NNReal.toReal <| prod_nnnorm_ofLp f
/-
**WithLp.prod_norm_toLp** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SeminormedAddCommGroup α] [inst_1 
: SeminormedAddCommGroup β] (f : α × β),   ‖WithLp.toLp ⊤ f‖ = ‖f‖
参数：f : α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithLp.prod_norm_ofLp`：∀ {α : Type u_2} {β : Type u_3} [inst : Seminorme
dAddCommGroup α] [inst_1 : SeminormedAddCommGroup β]   (f : WithLp ⊤ (α × β)), ‖
f.ofLp‖ = ‖…
-/
@[simp] lemma prod_norm_toLp (f : α × β) : ‖toLp ⊤ f‖ = ‖f‖ :=
  (prod_norm_ofLp _).symm

section L1

set_option backward.isDefEq.respectTransparency false in
/-
**WithLp.prod_norm_eq_of_L1** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_norm_eq_of_L1 (x : WithLp 1 (α × β)) : ‖x‖ = ‖x.fst‖ + ‖x.snd‖
参数：x : WithLp 1 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.prod_norm_eq_add`：prod_norm_eq_add (hp : 0 < p.toReal) (f : WithL
p p (α × β)) : ‖f‖ = (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_norm_eq_of_L1 (x : WithLp 1 (α × β)) :
    ‖x‖ = ‖x.fst‖ + ‖x.snd‖ := by
  simp [prod_norm_eq_add]
/-
**WithLp.prod_nnnorm_eq_of_L1** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_nnnorm_eq_of_L1 (x : WithLp 1 (α × β)) : ‖x‖₊ = ‖x.fst‖₊ + ‖x.snd‖₊
参数：x : WithLp 1 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `WithLp.prod_norm_eq_of_L1`：prod_norm_eq_of_L1 (x : WithLp 1 (α × β)) : ‖
x‖ = ‖x.fst‖ + ‖x.snd‖
-/
theorem prod_nnnorm_eq_of_L1 (x : WithLp 1 (α × β)) :
    ‖x‖₊ = ‖x.fst‖₊ + ‖x.snd‖₊ :=
  NNReal.eq <| by
    push_cast
    exact prod_norm_eq_of_L1 x
/-
**WithLp.prod_dist_eq_of_L1** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_dist_eq_of_L1 (x y : WithLp 1 (α × β)) : dist x y = dist x.fst y.fst 
+ dist x.snd y.snd
参数：x y : WithLp 1 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithLp.prod_norm_eq_of_L1`：prod_norm_eq_of_L1 (x : WithLp 1 (α × β)) : ‖
x‖ = ‖x.fst‖ + ‖x.snd‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_dist_eq_of_L1 (x y : WithLp 1 (α × β)) :
    dist x y = dist x.fst y.fst + dist x.snd y.snd := by
  simp_rw [dist_eq_norm, prod_norm_eq_of_L1, sub_fst, sub_snd]
/-
**WithLp.prod_nndist_eq_of_L1** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_nndist_eq_of_L1 (x y : WithLp 1 (α × β)) : nndist x y = nndist x.fst 
y.fst + nndist x.snd y.snd
参数：x y : WithLp 1 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `WithLp.prod_dist_eq_of_L1`：prod_dist_eq_of_L1 (x y : WithLp 1 (α × β)) :
 dist x y = dist x.fst y.fst + dist x.snd y.snd
-/
theorem prod_nndist_eq_of_L1 (x y : WithLp 1 (α × β)) :
    nndist x y = nndist x.fst y.fst + nndist x.snd y.snd :=
  NNReal.eq <| by
    push_cast
    exact prod_dist_eq_of_L1 _ _

set_option backward.isDefEq.respectTransparency false in
/-
**WithLp.prod_edist_eq_of_L1** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_edist_eq_of_L1 (x y : WithLp 1 (α × β)) : edist x y = edist x.fst y.f
st + edist x.snd y.snd
参数：x y : WithLp 1 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.prod_edist_eq_add`：prod_edist_eq_add (hp : 0 < p.toReal) (f g : W
ithLp p (α × β)) : edist f g = (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd
 ^ p.toReal) ^…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_edist_eq_of_L1 (x y : WithLp 1 (α × β)) :
    edist x y = edist x.fst y.fst + edist x.snd y.snd := by
  simp [prod_edist_eq_add]

end L1

section L2

/-
**WithLp.prod_norm_eq_of_L2** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_norm_eq_of_L2 (x : WithLp 2 (α × β)) : ‖x‖ = √(‖x.fst‖ ^ 2 + ‖x.snd‖ 
^ 2)
参数：x : WithLp 2 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.prod_norm_eq_of_nat`：prod_norm_eq_of_nat [Norm α] [Norm β] (n : N
at) (h : p = n) (f : WithLp p (α × β)) : ‖f‖ = (‖f.fst‖ ^ n + ‖f.snd‖ ^ n) ^ (1 
/ (n : Real))
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Real.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem prod_norm_eq_of_L2 (x : WithLp 2 (α × β)) :
    ‖x‖ = √(‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) := by
  rw [prod_norm_eq_of_nat 2 (by norm_cast) _, Real.sqrt_eq_rpow]
  norm_cast
/-
**WithLp.prod_nnnorm_eq_of_L2** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_nnnorm_eq_of_L2 (x : WithLp 2 (α × β)) : ‖x‖₊ = NNReal.sqrt (‖x.fst‖₊
 ^ 2 + ‖x.snd‖₊ ^ 2)
参数：x : WithLp 2 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.coe_sqrt`：coe_sqrt {x : Real>=0} : (NNReal.sqrt x : Real) = √(x : R
eal)
· 使用定理 `WithLp.prod_norm_eq_of_L2`：prod_norm_eq_of_L2 (x : WithLp 2 (α × β)) : ‖
x‖ = √(‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2)
-/
theorem prod_nnnorm_eq_of_L2 (x : WithLp 2 (α × β)) :
    ‖x‖₊ = NNReal.sqrt (‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2) :=
  NNReal.eq <| by
    push_cast
    exact prod_norm_eq_of_L2 x
/-
**WithLp.prod_norm_sq_eq_of_L2** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_norm_sq_eq_of_L2 (x : WithLp 2 (α × β)) : ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.
snd‖ ^ 2
参数：x : WithLp 2 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.prod_nnnorm_eq_of_L2`：prod_nnnorm_eq_of_L2 (x : WithLp 2 (α × β))
 : ‖x‖₊ = NNReal.sqrt (‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2)
· 使用定理 `NNReal.sq_sqrt`：∀ (x : NNReal), NNReal.sqrt x ^ 2 = x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem prod_norm_sq_eq_of_L2 (x : WithLp 2 (α × β)) : ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 := by
  suffices ‖x‖₊ ^ 2 = ‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2 by
    simpa only [NNReal.coe_sum] using! congr_arg ((↑) : ℝ≥0 → ℝ) this
  rw [prod_nnnorm_eq_of_L2, NNReal.sq_sqrt]
/-
**WithLp.prod_dist_eq_of_L2** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_dist_eq_of_L2 (x y : WithLp 2 (α × β)) : dist x y = √(dist x.fst y.fs
t ^ 2 + dist x.snd y.snd ^ 2)
参数：x y : WithLp 2 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithLp.prod_norm_eq_of_L2`：prod_norm_eq_of_L2 (x : WithLp 2 (α × β)) : ‖
x‖ = √(‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_dist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    dist x y = √(dist x.fst y.fst ^ 2 + dist x.snd y.snd ^ 2) := by
  simp_rw [dist_eq_norm, prod_norm_eq_of_L2, sub_fst, sub_snd]
/-
**WithLp.prod_nndist_eq_of_L2** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_nndist_eq_of_L2 (x y : WithLp 2 (α × β)) : nndist x y = NNReal.sqrt (
nndist x.fst y.fst ^ 2 + nndist x.snd y.snd ^ 2)
参数：x y : WithLp 2 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.coe_sqrt`：coe_sqrt {x : Real>=0} : (NNReal.sqrt x : Real) = √(x : R
eal)
· 使用定理 `WithLp.prod_dist_eq_of_L2`：prod_dist_eq_of_L2 (x y : WithLp 2 (α × β)) :
 dist x y = √(dist x.fst y.fst ^ 2 + dist x.snd y.snd ^ 2)
-/
theorem prod_nndist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    nndist x y = NNReal.sqrt (nndist x.fst y.fst ^ 2 + nndist x.snd y.snd ^ 2) :=
  NNReal.eq <| by
    push_cast
    exact prod_dist_eq_of_L2 _ _
/-
**WithLp.prod_edist_eq_of_L2** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_edist_eq_of_L2 (x y : WithLp 2 (α × β)) : edist x y = (edist x.fst y.
fst ^ 2 + edist x.snd y.snd ^ 2) ^ (1 / 2 : Real)
参数：x y : WithLp 2 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.prod_edist_eq_add`：prod_edist_eq_add (hp : 0 < p.toReal) (f g : W
ithLp p (α × β)) : edist f g = (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd
 ^ p.toReal) ^…
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用引理 `ENNReal.rpow_ofNat`：rpow_ofNat (x : Real>=0∞) (n : Nat) [n.AtLeastTwo] :
 x ^ (ofNat(n) : Real) = x ^ (OfNat.ofNat n)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_edist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    edist x y = (edist x.fst y.fst ^ 2 + edist x.snd y.snd ^ 2) ^ (1 / 2 : ℝ) := by
  simp [prod_edist_eq_add]

end L2

end norm_of

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

section Single

/-
**WithLp.nnnorm_toLp_inl** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) (α : Type u_2) (β : Type u_3) [hp : Fact (1 ≤ p)] [inst : 
SeminormedAddCommGroup α]   [inst_1 : SeminormedAddCommGroup β] (x : α), ‖WithLp
.toLp p (x, 0)‖₊ = ‖x‖₊
参数：p : ENNReal；α : Type u_2；β : Type u_3；1 ≤ p；x : α；x, 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `WithLp.prod_nnnorm_eq_sup`：prod_nnnorm_eq_sup (f : WithLp ∞ (α × β)) : ‖
f‖₊ = ‖f.fst‖₊ ⊔ ‖f.snd‖₊
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `WithLp.prod_nnnorm_eq_add`：prod_nnnorm_eq_add (hp : p != ∞) (f : WithLp 
p (α × β)) : ‖f‖₊ = (‖f.fst‖₊ ^ p.toReal + ‖f.snd‖₊ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNReal.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x 
= 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
-/
@[simp] lemma nnnorm_toLp_inl (x : α) : ‖toLp p (x, (0 : β))‖₊ = ‖x‖₊ := by
  induction p generalizing hp with
  | top =>
    simp [prod_nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : ℝ) ≠ 0 := mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 ≤ (p : ℝ≥0∞))).ne'
    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]
/-
**WithLp.nnnorm_toLp_inr** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：∀ (p : ENNReal) (α : Type u_2) (β : Type u_3) [hp : Fact (1 ≤ p)] [inst : 
SeminormedAddCommGroup α]   [inst_1 : SeminormedAddCommGroup β] (y : β), ‖WithLp
.toLp p (0, y)‖₊ = ‖y‖₊
参数：p : ENNReal；α : Type u_2；β : Type u_3；1 ≤ p；y : β；0, y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `WithLp.prod_nnnorm_eq_sup`：prod_nnnorm_eq_sup (f : WithLp ∞ (α × β)) : ‖
f‖₊ = ‖f.fst‖₊ ⊔ ‖f.snd‖₊
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `WithLp.prod_nnnorm_eq_add`：prod_nnnorm_eq_add (hp : p != ∞) (f : WithLp 
p (α × β)) : ‖f‖₊ = (‖f.fst‖₊ ^ p.toReal + ‖f.snd‖₊ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNReal.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x 
= 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
-/
@[simp] lemma nnnorm_toLp_inr (y : β) : ‖toLp p ((0 : α), y)‖₊ = ‖y‖₊ := by
  induction p generalizing hp with
  | top =>
    simp [prod_nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : ℝ) ≠ 0 := mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 ≤ (p : ℝ≥0∞))).ne'
    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]

@[simp]
/-
**WithLp.norm_toLp_fst** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：norm_toLp_fst (x : α) : ‖toLp p (x, (0 : β))‖ = ‖x‖
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `WithLp.nnnorm_toLp_inl`：∀ (p : ENNReal) (α : Type u_2) (β : Type u_3) [h
p : Fact (1 ≤ p)] [inst : SeminormedAddCommGroup α]   [inst_1 : SeminormedAddCom
mGroup β] (x…
-/
lemma norm_toLp_fst (x : α) : ‖toLp p (x, (0 : β))‖ = ‖x‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_toLp_inl p α β x

@[simp]
/-
**WithLp.norm_toLp_snd** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：norm_toLp_snd (y : β) : ‖toLp p ((0 : α), y)‖ = ‖y‖
参数：y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `WithLp.nnnorm_toLp_inr`：∀ (p : ENNReal) (α : Type u_2) (β : Type u_3) [h
p : Fact (1 ≤ p)] [inst : SeminormedAddCommGroup α]   [inst_1 : SeminormedAddCom
mGroup β] (y…
-/
lemma norm_toLp_snd (y : β) : ‖toLp p ((0 : α), y)‖ = ‖y‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_toLp_inr p α β y

@[simp]
/-
**WithLp.nndist_toLp_fst** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：nndist_toLp_fst (x₁ x₂ : α) : nndist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0
)) = nndist x₁ x₂
参数：x₁ x₂ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nndist_eq_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), nndist a b = ‖a - b‖₊
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithLp.toLp_sub`：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V] 
(x y : V),   WithLp.toLp p (x - y) = WithLp.toLp p x - WithLp.toLp p y
· 使用定理 `Prod.mk_sub_mk`：∀ {G : Type u_8} {H : Type u_9} [inst : Sub G] [inst_1 :
 Sub H] (x₁ x₂ : G) (y₁ y₂ : H),   (x₁, y₁) - (x₂, y₂) = (x₁ - x₂, y₁ - y₂)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `WithLp.nnnorm_toLp_inl`：∀ (p : ENNReal) (α : Type u_2) (β : Type u_3) [h
p : Fact (1 ≤ p)] [inst : SeminormedAddCommGroup α]   [inst_1 : SeminormedAddCom
mGroup β] (x…
-/
lemma nndist_toLp_fst (x₁ x₂ : α) :
    nndist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0)) = nndist x₁ x₂ := by
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← toLp_sub, Prod.mk_sub_mk, sub_zero,
    nnnorm_toLp_inl]

@[simp]
/-
**WithLp.nndist_toLp_snd** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：nndist_toLp_snd (y₁ y₂ : β) : nndist (toLp p ((0 : α), y₁)) (toLp p (0, y₂
)) = nndist y₁ y₂
参数：y₁ y₂ : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nndist_eq_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), nndist a b = ‖a - b‖₊
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithLp.toLp_sub`：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V] 
(x y : V),   WithLp.toLp p (x - y) = WithLp.toLp p x - WithLp.toLp p y
· 使用定理 `Prod.mk_sub_mk`：∀ {G : Type u_8} {H : Type u_9} [inst : Sub G] [inst_1 :
 Sub H] (x₁ x₂ : G) (y₁ y₂ : H),   (x₁, y₁) - (x₂, y₂) = (x₁ - x₂, y₁ - y₂)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `WithLp.nnnorm_toLp_inr`：∀ (p : ENNReal) (α : Type u_2) (β : Type u_3) [h
p : Fact (1 ≤ p)] [inst : SeminormedAddCommGroup α]   [inst_1 : SeminormedAddCom
mGroup β] (y…
-/
lemma nndist_toLp_snd (y₁ y₂ : β) :
    nndist (toLp p ((0 : α), y₁)) (toLp p (0, y₂)) = nndist y₁ y₂ := by
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← toLp_sub, Prod.mk_sub_mk, sub_zero,
    nnnorm_toLp_inr]

@[simp]
/-
**WithLp.dist_toLp_fst** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：dist_toLp_fst (x₁ x₂ : α) : dist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0)) =
 dist x₁ x₂
参数：x₁ x₂ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `WithLp.nndist_toLp_fst`：nndist_toLp_fst (x₁ x₂ : α) : nndist (toLp p (x₁
, (0 : β))) (toLp p (x₂, 0)) = nndist x₁ x₂
-/
lemma dist_toLp_fst (x₁ x₂ : α) : dist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0)) = dist x₁ x₂ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nndist_toLp_fst p α β x₁ x₂

@[simp]
/-
**WithLp.dist_toLp_snd** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：dist_toLp_snd (y₁ y₂ : β) : dist (toLp p ((0 : α), y₁)) (toLp p (0, y₂)) =
 dist y₁ y₂
参数：y₁ y₂ : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `WithLp.nndist_toLp_snd`：nndist_toLp_snd (y₁ y₂ : β) : nndist (toLp p ((0
 : α), y₁)) (toLp p (0, y₂)) = nndist y₁ y₂
-/
lemma dist_toLp_snd (y₁ y₂ : β) :
    dist (toLp p ((0 : α), y₁)) (toLp p (0, y₂)) = dist y₁ y₂ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nndist_toLp_snd p α β y₁ y₂

@[simp]
/-
**WithLp.edist_toLp_fst** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：edist_toLp_fst (x₁ x₂ : α) : edist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0))
 = edist x₁ x₂
参数：x₁ x₂ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用引理 `WithLp.nndist_toLp_fst`：nndist_toLp_fst (x₁ x₂ : α) : nndist (toLp p (x₁
, (0 : β))) (toLp p (x₂, 0)) = nndist x₁ x₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edist_toLp_fst (x₁ x₂ : α) : edist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0)) = edist x₁ x₂ := by
  simp only [edist_nndist, nndist_toLp_fst p α β x₁ x₂]

@[simp]
/-
**WithLp.edist_toLp_snd** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：edist_toLp_snd (y₁ y₂ : β) : edist (toLp p ((0 : α), y₁)) (toLp p (0, y₂))
 = edist y₁ y₂
参数：y₁ y₂ : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用引理 `WithLp.nndist_toLp_snd`：nndist_toLp_snd (y₁ y₂ : β) : nndist (toLp p ((0
 : α), y₁)) (toLp p (0, y₂)) = nndist y₁ y₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edist_toLp_snd (y₁ y₂ : β) :
    edist (toLp p ((0 : α), y₁)) (toLp p (0, y₂)) = edist y₁ y₂ := by
  simp only [edist_nndist, nndist_toLp_snd p α β y₁ y₂]

end Single

section IsBoundedSMul
variable [SeminormedRing 𝕜] [Module 𝕜 α] [Module 𝕜 β] [IsBoundedSMul 𝕜 α] [IsBoundedSMul 𝕜 β]

/-
**WithLp.instProdIsBoundedSMul** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdIsBoundedSMul : IsBoundedSMul 𝕜 (WithLp p (α × β))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.of_nnnorm_smul_le`：IsBoundedSMul.of_nnnorm_smul_le (h : fo
rall (r : α) (x : β), ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊) : IsBoundedSMul α β
· 使用定理 `ENNReal.dichotomy`：∀ (p : ENNReal) [Fact (1 ≤ p)], p = ⊤ ∨ 1 ≤ p.toReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_pos_iff_ne_top`：toReal_pos_iff_ne_top (p : Real>=0∞) [Fac
t (1 <= p)] : 0 < p.toReal ↔ p != ∞
· 使用定理 `WithLp.prod_nnnorm_eq_add`：prod_nnnorm_eq_add (hp : p != ∞) (f : WithLp 
p (α × β)) : ‖f‖₊ = (‖f.fst‖₊ ^ p.toReal + ‖f.snd‖₊ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `NNReal.rpow_inv_le_iff`：rpow_inv_le_iff {x y : Real>=0} {z : Real} (hz :
 0 < z) : x ^ z⁻¹ <= y ↔ x <= y ^ z
· 使用定理 `NNReal.mul_rpow`：mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^
 z * y ^ z
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `NNReal.rpow_le_rpow`：∀ {x y : NNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤ y
 ^ z
· 使用定理 `nnnorm_smul_le`：nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
instance instProdIsBoundedSMul : IsBoundedSMul 𝕜 (WithLp p (α × β)) :=
  .of_nnnorm_smul_le fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · simp only [← prod_nnnorm_ofLp, ofLp_smul]
      exact norm_smul_le _ _
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p ≠ ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [prod_nnnorm_eq_add hpt, prod_nnnorm_eq_add hpt, one_div, NNReal.rpow_inv_le_iff hp0,
        NNReal.mul_rpow, ← NNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', NNReal.rpow_one, mul_add,
        ← NNReal.mul_rpow, ← NNReal.mul_rpow]
      gcongr <;> exact nnnorm_smul_le _ _

variable {𝕜 p α β}

/-- The canonical map `WithLp.equiv` between `WithLp ∞ (α × β)` and `α × β` as a linear isometric
equivalence. -/
/-
**WithLp.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `WithLp.equiv` between `WithLp ∞ (α × β)` and `α × β` as a lin
ear isometric
equivalence.
-/
def prodEquivₗᵢ : WithLp ∞ (α × β) ≃ₗᵢ[𝕜] α × β where
  __ := WithLp.equiv ∞ _
  map_add' _f _g := rfl
  map_smul' _c _f := rfl
  norm_map' x := prod_norm_toLp (ofLp x)


end IsBoundedSMul

/-
**WithLp.instProdNormSMulClass** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdNormSMulClass [SeminormedRing 𝕜] [Module 𝕜 α] [Module 𝕜 β] [NormSM
ulClass 𝕜 α] [NormSMulClass 𝕜 β] : NormSMulClass 𝕜 (WithLp p (α × β))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormSMulClass.of_nnnorm_smul`：NormSMulClass.of_nnnorm_smul (h : forall (
r : α) (x : β), ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊) : NormSMulClass α β where norm_smul r b
· 使用定理 `ENNReal.dichotomy`：∀ (p : ENNReal) [Fact (1 ≤ p)], p = ⊤ ∨ 1 ≤ p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_pos_iff_ne_top`：toReal_pos_iff_ne_top (p : Real>=0∞) [Fac
t (1 <= p)] : 0 < p.toReal ↔ p != ∞
· 使用定理 `WithLp.prod_nnnorm_eq_add`：prod_nnnorm_eq_add (hp : p != ∞) (f : WithLp 
p (α × β)) : ‖f‖₊ = (‖f.fst‖₊ ^ p.toReal + ‖f.snd‖₊ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `NNReal.rpow_inv_eq_iff`：rpow_inv_eq_iff {x y : Real>=0} {z : Real} (hz :
 z != 0) : x ^ z⁻¹ = y ↔ x = y ^ z
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.mul_rpow`：mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^
 z * y ^ z
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `WithLp.smul_fst`：smul_fst : (c • x).fst = c • x.fst
· 使用定理 `WithLp.smul_snd`：smul_snd : (c • x).snd = c • x.snd
-/
instance instProdNormSMulClass [SeminormedRing 𝕜] [Module 𝕜 α] [Module 𝕜 β]
    [NormSMulClass 𝕜 α] [NormSMulClass 𝕜 β] : NormSMulClass 𝕜 (WithLp p (α × β)) :=
  .of_nnnorm_smul fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · simp only [← prod_nnnorm_ofLp, WithLp.ofLp_smul, nnnorm_smul]
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p ≠ ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [prod_nnnorm_eq_add hpt, prod_nnnorm_eq_add hpt, one_div, NNReal.rpow_inv_eq_iff hp0.ne',
        NNReal.mul_rpow, ← NNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', NNReal.rpow_one, mul_add,
        ← NNReal.mul_rpow, ← NNReal.mul_rpow, smul_fst, smul_snd, nnnorm_smul, nnnorm_smul]

section SeminormedAddCommGroup

open ENNReal

variable {p : ℝ≥0∞} {α β}

/-- Projection on `WithLp p (α × β)` with range `α` and kernel `β` -/
/-
**WithLp.idemFst** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：idemFst : AddMonoid.End (WithLp p (α × β)) where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projection on `WithLp p (α × β)` with range `α` and kernel `β`
-/
def idemFst : AddMonoid.End (WithLp p (α × β)) where
  toFun x := toLp p (x.fst, 0)
  map_zero' := by simp
  map_add' := by simp [← toLp_add]

/-- Projection on `WithLp p (α × β)` with range `β` and kernel `α` -/
/-
**WithLp.idemSnd** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：idemSnd : AddMonoid.End (WithLp p (α × β)) where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projection on `WithLp p (α × β)` with range `β` and kernel `α`
-/
def idemSnd : AddMonoid.End (WithLp p (α × β)) where
  toFun x := toLp p (0, x.snd)
  map_zero' := by simp
  map_add' := by simp [← toLp_add]
/-
**WithLp.idemFst_apply** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：idemFst_apply (x : WithLp p (α × β)) : idemFst x = toLp p (x.fst, 0)
参数：x : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma idemFst_apply (x : WithLp p (α × β)) : idemFst x = toLp p (x.fst, 0) := rfl
/-
**WithLp.idemSnd_apply** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：idemSnd_apply (x : WithLp p (α × β)) : idemSnd x = toLp p (0, x.snd)
参数：x : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma idemSnd_apply (x : WithLp p (α × β)) : idemSnd x = toLp p (0, x.snd) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**WithLp.idemFst_add_idemSnd** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：idemFst_add_idemSnd : idemFst + idemSnd = (1 : AddMonoid.End (WithLp p (α 
× β)))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.add_apply`：∀ {M : Type u_2} {N : Type u_3} [inst : AddZeroC
lass M] [inst_1 : AddCommMonoid N] (f g : M →+ N) (x : M),   (f + g) x = f x + g
 x
· 使用引理 `WithLp.idemFst_apply`：idemFst_apply (x : WithLp p (α × β)) : idemFst x =
 toLp p (x.fst, 0)
· 使用引理 `WithLp.idemSnd_apply`：idemSnd_apply (x : WithLp p (α × β)) : idemSnd x =
 toLp p (0, x.snd)
· 使用定理 `AddMonoid.End.coe_one`：∀ (M : Type u_4) [inst : AddZero M], ⇑1 = id
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithLp.toLp_add`：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V] 
(x y : V),   WithLp.toLp p (x + y) = WithLp.toLp p x + WithLp.toLp p y
· 使用定理 `Prod.mk_add_mk`：∀ {M : Type u_8} {N : Type u_9} [inst : Add M] [inst_1 :
 Add N] (a₁ a₂ : M) (b₁ b₂ : N),   (a₁, b₁) + (a₂, b₂) = (a₁ + a₂, b₁ + b₂)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma idemFst_add_idemSnd :
    idemFst + idemSnd = (1 : AddMonoid.End (WithLp p (α × β))) := AddMonoidHom.ext
  fun x => by
    rw [AddMonoidHom.add_apply, idemFst_apply, idemSnd_apply, AddMonoid.End.coe_one, id_eq,
      ← toLp_add, Prod.mk_add_mk, zero_add, add_zero]
    rfl
/-
**WithLp.idemFst_compl** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：idemFst_compl : (1 : AddMonoid.End (WithLp p (α × β))) - idemFst = idemSnd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithLp.idemFst_add_idemSnd`：idemFst_add_idemSnd : idemFst + idemSnd = (1
 : AddMonoid.End (WithLp p (α × β)))
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
-/
lemma idemFst_compl : (1 : AddMonoid.End (WithLp p (α × β))) - idemFst = idemSnd := by
  rw [← idemFst_add_idemSnd, add_sub_cancel_left]
/-
**WithLp.idemSnd_compl** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：idemSnd_compl : (1 : AddMonoid.End (WithLp p (α × β))) - idemSnd = idemFst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithLp.idemFst_add_idemSnd`：idemFst_add_idemSnd : idemFst + idemSnd = (1
 : AddMonoid.End (WithLp p (α × β)))
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
lemma idemSnd_compl : (1 : AddMonoid.End (WithLp p (α × β))) - idemSnd = idemFst := by
  rw [← idemFst_add_idemSnd, add_sub_cancel_right]
/-
**WithLp.prod_norm_eq_idemFst_sup_idemSnd** 是 Mathlib 中的一个定理，位于命名空间 `WithLp`。
形式化陈述：prod_norm_eq_idemFst_sup_idemSnd (x : WithLp ∞ (α × β)) : ‖x‖ = max ‖idemF
st x‖ ‖idemSnd x‖
参数：x : WithLp ∞ (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.prod_norm_eq_sup`：prod_norm_eq_sup (f : WithLp ∞ (α × β)) : ‖f‖ =
 ‖f.fst‖ ⊔ ‖f.snd‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithLp.norm_toLp_fst`：norm_toLp_fst (x : α) : ‖toLp p (x, (0 : β))‖ = ‖x
‖
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用引理 `WithLp.norm_toLp_snd`：norm_toLp_snd (y : β) : ‖toLp p ((0 : α), y)‖ = ‖y
‖
-/
theorem prod_norm_eq_idemFst_sup_idemSnd (x : WithLp ∞ (α × β)) :
    ‖x‖ = max ‖idemFst x‖ ‖idemSnd x‖ := by
  rw [WithLp.prod_norm_eq_sup, ← WithLp.norm_toLp_fst ∞ α β x.fst,
    ← WithLp.norm_toLp_snd ∞ α β x.snd]
  rfl
/-
**WithLp.prod_norm_eq_add_idemFst** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：prod_norm_eq_add_idemFst [Fact (1 <= p)] (hp : 0 < p.toReal) (x : WithLp p
 (α × β)) : ‖x‖ = (‖idemFst x‖ ^ p.toReal + ‖idemSnd x‖ ^ p.toReal) ^ (1 / p.toR
eal)
参数：1 <= p；hp : 0 < p.toReal；x : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.prod_norm_eq_add`：prod_norm_eq_add (hp : 0 < p.toReal) (f : WithL
p p (α × β)) : ‖f‖ = (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithLp.norm_toLp_fst`：norm_toLp_fst (x : α) : ‖toLp p (x, (0 : β))‖ = ‖x
‖
· 使用引理 `WithLp.norm_toLp_snd`：norm_toLp_snd (y : β) : ‖toLp p ((0 : α), y)‖ = ‖y
‖
-/
lemma prod_norm_eq_add_idemFst [Fact (1 ≤ p)] (hp : 0 < p.toReal) (x : WithLp p (α × β)) :
    ‖x‖ = (‖idemFst x‖ ^ p.toReal + ‖idemSnd x‖ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [WithLp.prod_norm_eq_add hp, ← WithLp.norm_toLp_fst p α β x.fst,
    ← WithLp.norm_toLp_snd p α β x.snd]
  rfl
/-
**WithLp.prod_norm_eq_idemFst_of_L1** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：prod_norm_eq_idemFst_of_L1 (x : WithLp 1 (α × β)) : ‖x‖ = ‖idemFst x‖ + ‖i
demSnd x‖
参数：x : WithLp 1 (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithLp.prod_norm_eq_add_idemFst`：prod_norm_eq_add_idemFst [Fact (1 <= p)
] (hp : 0 < p.toReal) (x : WithLp p (α × β)) : ‖x‖ = (‖idemFst x‖ ^ p.toReal + ‖
idemSnd x‖ ^ p.toReal…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `lt_of_lt_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_one`：ENNReal.toReal 1 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_norm_eq_idemFst_of_L1 (x : WithLp 1 (α × β)) : ‖x‖ = ‖idemFst x‖ + ‖idemSnd x‖ := by
  rw [prod_norm_eq_add_idemFst (lt_of_lt_of_eq zero_lt_one toReal_one.symm)]
  simp only [toReal_one, Real.rpow_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]

end SeminormedAddCommGroup

section NormedSpace

/-- The product of two normed spaces is a normed space, with the `L^p` norm. -/
/-
**WithLp.instProdNormedSpace** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instProdNormedSpace [NormedField 𝕜] [NormedSpace 𝕜 α] [NormedSpace 𝕜 β] : 
NormedSpace 𝕜 (WithLp p (α × β)) where norm_smul_le
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two normed spaces is a normed space, with the `L^p` norm.
-/
instance instProdNormedSpace [NormedField 𝕜] [NormedSpace 𝕜 α] [NormedSpace 𝕜 β] :
    NormedSpace 𝕜 (WithLp p (α × β)) where
  norm_smul_le := norm_smul_le

end NormedSpace

section toProd

/-!
### `L^p` distance on a product space

In this section we define a pseudometric space structure on `α × β`, as well as a seminormed
group structure. These are meant to be used to put the desired instances on type synonyms
of `α × β`. See for instance `TrivSqZeroExt.instL1SeminormedAddCommGroup`.
-/

variable (α β : Type*)

-- This prevents Lean from elaborating terms of `α × β` with an unintended norm.
attribute [-instance] Prod.toNorm

/-- This definition allows to endow `α × β` with the Lp distance with the uniformity and bornology
being defeq to the product ones. It is useful to endow a type synonym of `a × β` with the
Lp distance. -/
/-
**WithLp.pseudoMetricSpaceToProd** 是 Mathlib 中的一个缩写定义，位于命名空间 `WithLp`。
形式化陈述：pseudoMetricSpaceToProd [PseudoMetricSpace α] [PseudoMetricSpace β] : Pseu
doMetricSpace (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This definition allows to endow `α × β` with the Lp distance with the uniformity
 and bornology
being defeq to the product ones. It is useful to endow a type synonym of `a × β`
 with the
Lp distance.
-/
abbrev pseudoMetricSpaceToProd [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (α × β) :=
  (isUniformInducing_toLp p α β).comapPseudoMetricSpace.replaceBornology
    fun s => Filter.ext_iff.1
      (le_antisymm (prod_antilipschitzWith_toLp p α β).tendsto_cobounded.le_comap
        (prod_lipschitzWith_toLp p α β).comap_cobounded_le) sᶜ
/-
**WithLp.dist_pseudoMetricSpaceToProd** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：dist_pseudoMetricSpaceToProd [PseudoMetricSpace α] [PseudoMetricSpace β] (
x y : α × β) : @dist _ (pseudoMetricSpaceToProd p α β).toDist x y = dist (toLp p
 x) (toLp p y)
参数：x y : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dist_pseudoMetricSpaceToProd [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : α × β) :
    @dist _ (pseudoMetricSpaceToProd p α β).toDist x y = dist (toLp p x) (toLp p y) := rfl

/-- This definition allows to endow `α × β` with the Lp norm with the uniformity and bornology
being defeq to the product ones. It is useful to endow a type synonym of `a × β` with the
Lp norm. -/
/-
**WithLp.seminormedAddCommGroupToProd** 是 Mathlib 中的一个缩写定义，位于命名空间 `WithLp`。
形式化陈述：seminormedAddCommGroupToProd [SeminormedAddCommGroup α] [SeminormedAddComm
Group β] : SeminormedAddCommGroup (α × β) where norm x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This definition allows to endow `α × β` with the Lp norm with the uniformity and
 bornology
being defeq to the product ones. It is useful to endow a type synonym of `a × β`
 with the
Lp norm.
-/
abbrev seminormedAddCommGroupToProd [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] :
    SeminormedAddCommGroup (α × β) where
  norm x := ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToProd p α β
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToProd, SeminormedAddCommGroup.dist_eq, toLp_add, toLp_neg]
/-
**WithLp.norm_seminormedAddCommGroupToProd** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：norm_seminormedAddCommGroupToProd [SeminormedAddCommGroup α] [SeminormedAd
dCommGroup β] (x : α × β) : @Norm.norm _ (seminormedAddCommGroupToProd p α β).to
Norm x = ‖toLp p x‖
参数：x : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_seminormedAddCommGroupToProd [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
    (x : α × β) :
    @Norm.norm _ (seminormedAddCommGroupToProd p α β).toNorm x = ‖toLp p x‖ := rfl
/-
**WithLp.nnnorm_seminormedAddCommGroupToProd** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：nnnorm_seminormedAddCommGroupToProd [SeminormedAddCommGroup α] [Seminormed
AddCommGroup β] (x : α × β) : @NNNorm.nnnorm _ (seminormedAddCommGroupToProd p α
 β).toSeminormedAddGroup.toNNNorm x = ‖toLp p x‖₊
参数：x : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnnorm_seminormedAddCommGroupToProd [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
    (x : α × β) :
    @NNNorm.nnnorm _ (seminormedAddCommGroupToProd p α β).toSeminormedAddGroup.toNNNorm x =
    ‖toLp p x‖₊ := rfl
/-
**WithLp.isBoundedSMulSeminormedAddCommGroupToProd** 是 Mathlib 中的一个引理，位于命名空间 `Wi
thLp`。
形式化陈述：isBoundedSMulSeminormedAddCommGroupToProd [SeminormedAddCommGroup α] [Semi
normedAddCommGroup β] {R : Type*} [SeminormedRing R] [Module R α] [Module R β] [
IsBoundedSMul R α] [IsBoundedSMul R β] : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `dist_smul_pair`：dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • 
y₂) <= dist x 0 * dist y₁ y₂
· 使用定理 `dist_pair_smul`：dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ •
 y) <= dist x₁ x₂ * dist y 0
-/
lemma isBoundedSMulSeminormedAddCommGroupToProd
    [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] {R : Type*} [SeminormedRing R]
    [Module R α] [Module R β] [IsBoundedSMul R α] [IsBoundedSMul R β] :
    letI := pseudoMetricSpaceToProd p α β
    IsBoundedSMul R (α × β) := by
  let := pseudoMetricSpaceToProd p α β
  refine ⟨fun x y z ↦ ?_, fun x y z ↦ ?_⟩
  · simpa [dist_pseudoMetricSpaceToProd] using dist_smul_pair x (toLp p y) (toLp p z)
  · simpa [dist_pseudoMetricSpaceToProd] using dist_pair_smul x y (toLp p z)
/-
**WithLp.normSMulClassSeminormedAddCommGroupToProd** 是 Mathlib 中的一个引理，位于命名空间 `Wi
thLp`。
形式化陈述：normSMulClassSeminormedAddCommGroupToProd [SeminormedAddCommGroup α] [Semi
normedAddCommGroup β] {R : Type*} [SeminormedRing R] [Module R α] [Module R β] [
NormSMulClass R α] [NormSMulClass R β] : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
-/
lemma normSMulClassSeminormedAddCommGroupToProd
    [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] {R : Type*} [SeminormedRing R]
    [Module R α] [Module R β] [NormSMulClass R α] [NormSMulClass R β] :
    letI := seminormedAddCommGroupToProd p α β
    NormSMulClass R (α × β) := by
  let := seminormedAddCommGroupToProd p α β
  exact ⟨fun x y ↦ norm_smul x (toLp p y)⟩

/-- This definition allows to endow `α × β` with a normed space structure corresponding to
the Lp norm. It is useful for type synonyms of `α × β`. -/
/-
**WithLp.normedSpaceSeminormedAddCommGroupToProd** 是 Mathlib 中的一个缩写定义，位于命名空间 `Wi
thLp`。
形式化陈述：normedSpaceSeminormedAddCommGroupToProd [SeminormedAddCommGroup α] [Semino
rmedAddCommGroup β] {R : Type*} [NormedField R] [NormedSpace R α] [NormedSpace R
 β] : letI
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This definition allows to endow `α × β` with a normed space structure correspond
ing to
the Lp norm. It is useful for type synonyms of `α × β`.
-/
abbrev normedSpaceSeminormedAddCommGroupToProd
    [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] {R : Type*} [NormedField R]
    [NormedSpace R α] [NormedSpace R β] :
    letI := seminormedAddCommGroupToProd p α β
    NormedSpace R (α × β) := by
  letI := seminormedAddCommGroupToProd p α β
  exact ⟨fun x y ↦ norm_smul_le x (toLp p y)⟩

/-- This definition allows to endow `α × β` with the Lp norm with the uniformity and bornology
being defeq to the product ones. It is useful to endow a type synonym of `α × β` with the
Lp norm. -/
/-
**WithLp.normedAddCommGroupToProd** 是 Mathlib 中的一个缩写定义，位于命名空间 `WithLp`。
形式化陈述：normedAddCommGroupToProd [NormedAddCommGroup α] [NormedAddCommGroup β] : N
ormedAddCommGroup (α × β) where norm x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This definition allows to endow `α × β` with the Lp norm with the uniformity and
 bornology
being defeq to the product ones. It is useful to endow a type synonym of `α × β`
 with the
Lp norm.
-/
abbrev normedAddCommGroupToProd [NormedAddCommGroup α] [NormedAddCommGroup β] :
    NormedAddCommGroup (α × β) where
  norm x := ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToProd p α β
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToProd, SeminormedAddCommGroup.dist_eq, toLp_add, toLp_neg]
  eq_of_dist_eq_zero {x y} h := by
    rw [dist_pseudoMetricSpaceToProd] at h
    exact toLp_injective p (eq_of_dist_eq_zero h)

end toProd

end WithLp

variable (γ : Type*) {α' β' : Type*}

section Isometry

variable [hp : Fact (1 ≤ p)] [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
  [PseudoEMetricSpace α'] [PseudoEMetricSpace β']

variable {α β} in
/-- The `L^p` product of two isometries is an isometry. -/
/-
**Isometry.withLpProdMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Isometry.withLpProdMap {f : α -> α'} (hf : Isometry f) {g : β -> β'} (hg :
 Isometry g) : Isometry (WithLp.map p (Prod.map f g))
参数：hf : Isometry f；hg : Isometry g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `WithLp.prod_edist_eq_add`：prod_edist_eq_add (hp : 0 < p.toReal) (f g : W
ithLp p (α × β)) : edist f g = (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd
 ^ p.toReal) ^…
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹

--- 原说明 ---
The `L^p` product of two isometries is an isometry.
-/
theorem Isometry.withLpProdMap {f : α → α'} (hf : Isometry f) {g : β → β'} (hg : Isometry g) :
    Isometry (WithLp.map p (Prod.map f g)) := by
  intro _ _
  rcases p.trichotomy with rfl | rfl | hp
  · absurd hp.elim; simp
  · simp [WithLp.prod_edist_eq_sup, hf.edist_eq, hg.edist_eq]
  · simp [WithLp.prod_edist_eq_add hp, hf.edist_eq, hg.edist_eq]

namespace IsometryEquiv

variable {α β} in
/-- The `L^p` product of two isometric equivalences. -/
@[simps! apply symm_apply]
/-
**IsometryEquiv.withLpProdCongr** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：withLpProdCongr (f : α ≃ᵢ α') (g : β ≃ᵢ β') : WithLp p (α × β) ≃ᵢ WithLp p
 (α' × β') where __
参数：f : α ≃ᵢ α'；g : β ≃ᵢ β'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `L^p` product of two isometric equivalences.
-/
def withLpProdCongr (f : α ≃ᵢ α') (g : β ≃ᵢ β') : WithLp p (α × β) ≃ᵢ WithLp p (α' × β') where
  __ := WithLp.congr p (f.toEquiv.prodCongr g.toEquiv)
  isometry_toFun := f.isometry.withLpProdMap p g.isometry

/-- Commutativity of the `L^p` product as an isometric equivalence. -/
/-
**IsometryEquiv.withLpProdComm** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：withLpProdComm : WithLp p (α × β) ≃ᵢ WithLp p (β × α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Commutativity of the `L^p` product as an isometric equivalence.
-/
def withLpProdComm : WithLp p (α × β) ≃ᵢ WithLp p (β × α) where
  __ := WithLp.congr p (Equiv.prodComm α β)
  isometry_toFun _ _ := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp [WithLp.prod_edist_eq_sup, max_comm]
    · simp [WithLp.prod_edist_eq_add hp, add_comm]

@[simp]
/-
**IsometryEquiv.withLpProdComm_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：withLpProdComm_apply (x : WithLp p (α × β)) : withLpProdComm p α β x = .to
Lp p (x.snd, x.fst)
参数：x : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem withLpProdComm_apply (x : WithLp p (α × β)) :
    withLpProdComm p α β x = .toLp p (x.snd, x.fst) :=
  rfl

@[simp]
/-
**IsometryEquiv.withLpProdComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：withLpProdComm_symm : (withLpProdComm p α β).symm = withLpProdComm p β α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem withLpProdComm_symm : (withLpProdComm p α β).symm = withLpProdComm p β α :=
  rfl

/-- Associativity of the `L^p` product as an isometric equivalence. -/
@[simps apply symm_apply]
/-
**IsometryEquiv.withLpProdAssoc** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：withLpProdAssoc : WithLp p (WithLp p (α × β) × γ) ≃ᵢ WithLp p (α × WithLp 
p (β × γ)) where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Associativity of the `L^p` product as an isometric equivalence.
-/
def withLpProdAssoc : WithLp p (WithLp p (α × β) × γ) ≃ᵢ WithLp p (α × WithLp p (β × γ)) where
  toFun x := .toLp p (x.fst.fst, .toLp p (x.fst.snd, x.snd))
  invFun x := .toLp p (.toLp p (x.fst, x.snd.fst), x.snd.snd)
  isometry_toFun _ _ := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp [WithLp.prod_edist_eq_sup, max_assoc]
    · simp [WithLp.prod_edist_eq_add hp, ENNReal.rpow_inv_rpow hp.ne', add_assoc]

/-- Right identity of the `L^p` product as an isometric equivalence. -/
@[simps! apply symm_apply]
/-
**IsometryEquiv.withLpProdUnique** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：withLpProdUnique [Unique β] : WithLp p (α × β) ≃ᵢ α where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Right identity of the `L^p` product as an isometric equivalence.
-/
def withLpProdUnique [Unique β] : WithLp p (α × β) ≃ᵢ α where
  __ := (WithLp.equiv _ _).trans (Equiv.prodUnique _ _)
  isometry_toFun x y : edist x.fst y.fst = edist x y := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp_rw [WithLp.prod_edist_eq_sup, Unique.eq_default, edist_self, max_zero]
    · simp_rw [WithLp.prod_edist_eq_add hp, Unique.eq_default, edist_self,
        ENNReal.zero_rpow_of_pos hp, add_zero, one_div, ENNReal.rpow_rpow_inv hp.ne']
/-
**IsometryEquiv.coe_withLpProdUnique** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：coe_withLpProdUnique [Unique β] : ⇑(withLpProdUnique p α β) = WithLp.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_withLpProdUnique [Unique β] : ⇑(withLpProdUnique p α β) = WithLp.fst :=
  rfl

/-- Left identity of the `L^p` product as an isometric equivalence. -/
@[simps! apply symm_apply]
/-
**IsometryEquiv.withLpUniqueProd** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：withLpUniqueProd [Unique α] : WithLp p (α × β) ≃ᵢ β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left identity of the `L^p` product as an isometric equivalence.
-/
def withLpUniqueProd [Unique α] : WithLp p (α × β) ≃ᵢ β :=
  (withLpProdComm p α β).trans (withLpProdUnique p β α)
/-
**IsometryEquiv.coe_withLpUniqueProd** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：coe_withLpUniqueProd [Unique α] : ⇑(withLpUniqueProd p α β) = WithLp.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_withLpUniqueProd [Unique α] : ⇑(withLpUniqueProd p α β) = WithLp.snd :=
  rfl

end IsometryEquiv

end Isometry

section Linear

variable [hp : Fact (1 ≤ p)] [Semiring 𝕜]
  [SeminormedAddCommGroup α] [Module 𝕜 α]
  [SeminormedAddCommGroup β] [Module 𝕜 β]
  [SeminormedAddCommGroup γ] [Module 𝕜 γ]
  [SeminormedAddCommGroup α'] [Module 𝕜 α']
  [SeminormedAddCommGroup β'] [Module 𝕜 β']

variable {𝕜 α β} in
/-- The `L^p` product of two linear isometries. -/
@[simps! apply]
/-
**LinearIsometry.withLpProdMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearIsometry.withLpProdMap (f : α ->ₗᵢ[𝕜] α') (g : β ->ₗᵢ[𝕜] β') : WithL
p p (α × β) ->ₗᵢ[𝕜] WithLp p (α' × β') where __
参数：f : α ->ₗᵢ[𝕜] α'；g : β ->ₗᵢ[𝕜] β'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `L^p` product of two linear isometries.
-/
def LinearIsometry.withLpProdMap (f : α →ₗᵢ[𝕜] α') (g : β →ₗᵢ[𝕜] β') :
    WithLp p (α × β) →ₗᵢ[𝕜] WithLp p (α' × β') where
  __ := (f.toLinearMap.prodMap g.toLinearMap).withLpMap p
  norm_map' := (f.isometry.withLpProdMap p g.isometry).norm_map_of_map_zero
    ((f.toLinearMap.prodMap g.toLinearMap).withLpMap p).map_zero

namespace LinearIsometryEquiv

variable {𝕜 α β} in
/-- The `L^p` product of two linear isometric equivalences. -/
@[simps! apply symm_apply]
/-
**LinearIsometryEquiv.withLpProdCongr** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryE
quiv`。
形式化陈述：withLpProdCongr (f : α ≃ₗᵢ[𝕜] α') (g : β ≃ₗᵢ[𝕜] β') : WithLp p (α × β) ≃ₗᵢ
[𝕜] WithLp p (α' × β') where __
参数：f : α ≃ₗᵢ[𝕜] α'；g : β ≃ₗᵢ[𝕜] β'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `L^p` product of two linear isometric equivalences.
-/
def withLpProdCongr (f : α ≃ₗᵢ[𝕜] α') (g : β ≃ₗᵢ[𝕜] β') :
    WithLp p (α × β) ≃ₗᵢ[𝕜] WithLp p (α' × β') where
  __ := (f.toLinearEquiv.prodCongr g.toLinearEquiv).withLpCongr p
  norm_map' := (f.toLinearIsometry.withLpProdMap p g.toLinearIsometry).norm_map

/-- Commutativity of the `L^p` product as a linear isometric equivalence. -/
/-
**LinearIsometryEquiv.withLpProdComm** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEq
uiv`。
形式化陈述：withLpProdComm : WithLp p (α × β) ≃ₗᵢ[𝕜] WithLp p (β × α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Commutativity of the `L^p` product as a linear isometric equivalence.
-/
def withLpProdComm : WithLp p (α × β) ≃ₗᵢ[𝕜] WithLp p (β × α) where
  __ := (LinearEquiv.prodComm 𝕜 α β).withLpCongr p
  norm_map' := (IsometryEquiv.withLpProdComm p α β).isometry.norm_map_of_map_zero rfl

@[simp]
/-
**LinearIsometryEquiv.withLpProdComm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsom
etryEquiv`。
形式化陈述：withLpProdComm_apply (x : WithLp p (α × β)) : withLpProdComm p 𝕜 α β x = W
ithLp.toLp p (x.snd, x.fst)
参数：x : WithLp p (α × β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem withLpProdComm_apply (x : WithLp p (α × β)) :
    withLpProdComm p 𝕜 α β x = WithLp.toLp p (x.snd, x.fst) :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.withLpProdComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsome
tryEquiv`。
形式化陈述：withLpProdComm_symm : (withLpProdComm p 𝕜 α β).symm = withLpProdComm p 𝕜 β
 α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem withLpProdComm_symm : (withLpProdComm p 𝕜 α β).symm = withLpProdComm p 𝕜 β α :=
  rfl

/-- Associativity of the `L^p` product as a linear isometric equivalence. -/
@[simps! apply symm_apply]
/-
**LinearIsometryEquiv.withLpProdAssoc** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryE
quiv`。
形式化陈述：withLpProdAssoc : WithLp p (WithLp p (α × β) × γ) ≃ₗᵢ[𝕜] WithLp p (α × Wit
hLp p (β × γ)) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Associativity of the `L^p` product as a linear isometric equivalence.
-/
def withLpProdAssoc : WithLp p (WithLp p (α × β) × γ) ≃ₗᵢ[𝕜] WithLp p (α × WithLp p (β × γ)) where
  __ := (IsometryEquiv.withLpProdAssoc p α β γ).toEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := (IsometryEquiv.withLpProdAssoc p α β γ).isometry.norm_map_of_map_zero rfl

/-- Right identity of the `L^p` product as a linear isometric equivalence. -/
@[simps! apply symm_apply]
/-
**LinearIsometryEquiv.withLpProdUnique** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry
Equiv`。
形式化陈述：withLpProdUnique [Unique β] : WithLp p (α × β) ≃ₗᵢ[𝕜] α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right identity of the `L^p` product as a linear isometric equivalence.
-/
def withLpProdUnique [Unique β] : WithLp p (α × β) ≃ₗᵢ[𝕜] α where
  __ := (WithLp.linearEquiv _ _ _).trans LinearEquiv.prodUnique
  norm_map' := (IsometryEquiv.withLpProdUnique _ _ _).isometry.norm_map_of_map_zero rfl
/-
**LinearIsometryEquiv.coe_withLpProdUnique** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsom
etryEquiv`。
形式化陈述：coe_withLpProdUnique [Unique β] : ⇑(withLpProdUnique p 𝕜 α β) = WithLp.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_withLpProdUnique [Unique β] : ⇑(withLpProdUnique p 𝕜 α β) = WithLp.fst :=
  rfl

/-- Left identity of the `L^p` product as a linear isometric equivalence. -/
@[simps! apply symm_apply]
/-
**LinearIsometryEquiv.withLpUniqueProd** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry
Equiv`。
形式化陈述：withLpUniqueProd [Unique α] : WithLp p (α × β) ≃ₗᵢ[𝕜] β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left identity of the `L^p` product as a linear isometric equivalence.
-/
def withLpUniqueProd [Unique α] : WithLp p (α × β) ≃ₗᵢ[𝕜] β :=
  (withLpProdComm p 𝕜 α β).trans (withLpProdUnique p 𝕜 β α)
/-
**LinearIsometryEquiv.coe_withLpUniqueProd** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsom
etryEquiv`。
形式化陈述：coe_withLpUniqueProd [Unique α] : ⇑(withLpUniqueProd p 𝕜 α β) = WithLp.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_withLpUniqueProd [Unique α] : ⇑(withLpUniqueProd p 𝕜 α β) = WithLp.snd :=
  rfl

end LinearIsometryEquiv

end Linear

