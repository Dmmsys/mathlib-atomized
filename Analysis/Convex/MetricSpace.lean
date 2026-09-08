/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
public import Mathlib.Geometry.Convex.ConvexSpace.Module

/-!

# Convex spaces with compatible metric structure

A convex space has a compatible metric structure if `dist(∑ tᵢ xᵢ, ∑ tᵢ yᵢ) ≤ ∑ tᵢ dist(xᵢ, yᵢ)`.
This is what one would expect from the triangle inequality.

Note that there is a separate notion of
[convex metric spaces](https://en.wikipedia.org/wiki/Convex_metric_space) in the literature
that has little to do with this definition.

## Main results

- `Convexity.IsConvexDist`: The (`Prop`-valued) class of convex spaces with
  compatible metric structure.
- `Convexity.continuous_convexCombPair`: Binary convex combination is continuous.
- `Convexity.IsConvexDist.of_convex`:
  Convex subspaces of normed spaces are convex metric spaces.

## TODO

- Equip `StdSimplex` with a topology and show the analogous continuity result for n-ary
  convex combinations.
- Tidy up the imports with `Mathlib.Geometric.Convex.ConvexSpace.AffineSpace`.
- Define convex functions with domain a convex space, and redefine `IsConvexDist` as saying that
  `dist : X × X → ℝ` is convex.
-/

public section

namespace Convexity

open ConvexSpace

variable {I X : Type*}

variable (X) in
/-- A convex metric space is a real convex space with a compatible metric structure.
Concretely, we ask for `dist(∑ tᵢ xᵢ, ∑ tᵢ yᵢ) ≤ ∑ tᵢ dist(xᵢ, yᵢ)`,
which is what one would expect from the triangle inequality.

In particular, convex subsets of normed affine spaces are convex metric spaces.

Note that there is a separate notion of
[convex metric spaces](https://en.wikipedia.org/wiki/Convex_metric_space) in the literature
that has little to do with this definition. -/
/-
**Convexity.IsConvexDist** 是 Mathlib 中的一个归纳类型，位于命名空间 `Convexity`。
形式化陈述：(X : Type u_2) → [inst₁ : Convexity.ConvexSpace ℝ X] → [inst₂ : MetricSpac
e X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convex metric space is a real convex space with a compatible metric structure.
Concretely, we ask for `dist(∑ tᵢ xᵢ, ∑ tᵢ yᵢ) ≤ ∑ tᵢ dist(xᵢ, yᵢ)`,
which is what one would expect from the triangle inequality.

In particular, convex subsets of normed affine spaces are convex metric spaces.

Note that there is a separate notion of
[convex metric spaces](https://en.wikipedia.org/wiki/Convex_metric_space) in the
 literature
that has little to do with this definition.
-/
class IsConvexDist [inst₁ : ConvexSpace ℝ X] [inst₂ : MetricSpace X] : Prop where
  /-- Use `dist_iConvexComb_le` instead. -/
  dist_iConvexComb_fst_snd_le [inst₁] [inst₂] (f : StdSimplex ℝ (X × X)) :
    dist (f.iConvexComb Prod.fst) (f.iConvexComb Prod.snd) ≤ f.iConvexComb fun x ↦ dist x.1 x.2

@[deprecated (since := "2026-05-15")] alias IsConvexMetricSpace := IsConvexDist

variable [ConvexSpace ℝ X] [MetricSpace X] [IsConvexDist X]

/-- `dist(∑ tᵢ xᵢ, ∑ tᵢ yᵢ) ≤ ∑ tᵢ dist(xᵢ, yᵢ)` -/
/-
**Convexity.dist_iConvexComb_le** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：dist_iConvexComb_le {ι : Type*} (f : StdSimplex Real ι) (x y : ι -> X) : d
ist (f.iConvexComb x) (f.iConvexComb y) <= f.iConvexComb fun i => dist (x i) (y 
i)
参数：f : StdSimplex Real ι；x y : ι -> X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.iConvexComb_eq_sum`：iConvexComb_eq_sum (w : StdSimplex R I) (f
 : I -> M) : w.iConvexComb f = w.weights.sum fun i r => r • f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Convexity.iConvexComb_map`：∀ {R : Type u_1} {M : Type u_3} {I : Type u_6
} {J : Type u_7} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStr
ictOrderedRing …
· 使用定理 `Convexity.iConvexComb_congr`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Convexity.IsConvexDist.dist_iConvexComb_fst_snd_le`：∀ {X : Type u_2} [in
st₁ : Convexity.ConvexSpace ℝ X] [inst₂ : MetricSpace X] [self : Convexity.IsCon
vexDist X]   (f : Convexity.StdSimplex ℝ…

--- 原说明 ---
`dist(∑ tᵢ xᵢ, ∑ tᵢ yᵢ) ≤ ∑ tᵢ dist(xᵢ, yᵢ)`
-/
lemma dist_iConvexComb_le {ι : Type*} (f : StdSimplex ℝ ι) (x y : ι → X) :
    dist (f.iConvexComb x) (f.iConvexComb y) ≤ f.iConvexComb fun i ↦ dist (x i) (y i) := by
  simpa [iConvexComb_map, Finsupp.sum_mapDomain_index, add_mul]
    using IsConvexDist.dist_iConvexComb_fst_snd_le (f.map fun i ↦ (x i, y i))

@[deprecated (since := "2026-05-15")] alias dist_convexCombination_right_le := dist_iConvexComb_le
/-
**Convexity.dist_iConvexComb_left_le** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：dist_iConvexComb_left_le (f : StdSimplex Real I) (g : I -> X) (x : X) : di
st (f.iConvexComb g) x <= f.iConvexComb fun i => dist (g i) x
参数：f : StdSimplex Real I；g : I -> X；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.iConvexComb_eq_sum`：iConvexComb_eq_sum (w : StdSimplex R I) (f
 : I -> M) : w.iConvexComb f = w.weights.sum fun i r => r • f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Convexity.iConvexComb_const`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用引理 `Convexity.dist_iConvexComb_le`：dist_iConvexComb_le {ι : Type*} (f : StdS
implex Real ι) (x y : ι -> X) : dist (f.iConvexComb x) (f.iConvexComb y) <= f.iC
onvexComb fun i => …
-/
lemma dist_iConvexComb_left_le (f : StdSimplex ℝ I) (g : I → X) (x : X) :
    dist (f.iConvexComb g) x ≤ f.iConvexComb fun i ↦ dist (g i) x := by
  simpa using dist_iConvexComb_le f g (fun _ ↦ x)
/-
**Convexity.dist_iConvexComb_right_le** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：dist_iConvexComb_right_le (x : X) (f : StdSimplex Real I) (g : I -> X) : d
ist x (f.iConvexComb g) <= f.iConvexComb fun i => dist x (g i)
参数：x : X；f : StdSimplex Real I；g : I -> X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.iConvexComb_eq_sum`：iConvexComb_eq_sum (w : StdSimplex R I) (f
 : I -> M) : w.iConvexComb f = w.weights.sum fun i r => r • f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.iConvexComb_const`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用引理 `Convexity.dist_iConvexComb_le`：dist_iConvexComb_le {ι : Type*} (f : StdS
implex Real ι) (x y : ι -> X) : dist (f.iConvexComb x) (f.iConvexComb y) <= f.iC
onvexComb fun i => …
-/
lemma dist_iConvexComb_right_le (x : X) (f : StdSimplex ℝ I) (g : I → X) :
    dist x (f.iConvexComb g) ≤ f.iConvexComb fun i ↦ dist x (g i) := by
  simpa using dist_iConvexComb_le f (fun _ ↦ x) g
/-
**Convexity.dist_sConvexComb_left_le** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：dist_sConvexComb_left_le (f : StdSimplex Real X) (x : X) : dist f.sConvexC
omb x <= f.iConvexComb (dist · x)
参数：f : StdSimplex Real X；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.iConvexComb_eq_sum`：iConvexComb_eq_sum (w : StdSimplex R I) (f
 : I -> M) : w.iConvexComb f = w.weights.sum fun i r => r • f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Convexity.iConvexComb_congr`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用定理 `Convexity.iConvexComb_id'`：∀ {R : Type u_1} {M : Type u_3} [inst : Parti
alOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Co
nvexity.ConvexS…
· 使用引理 `Convexity.dist_iConvexComb_left_le`：dist_iConvexComb_left_le (f : StdSim
plex Real I) (g : I -> X) (x : X) : dist (f.iConvexComb g) x <= f.iConvexComb fu
n i => dist (g i) x
-/
lemma dist_sConvexComb_left_le (f : StdSimplex ℝ X) (x : X) :
    dist f.sConvexComb x ≤ f.iConvexComb (dist · x) := by
  simpa using dist_iConvexComb_left_le f id x
/-
**Convexity.dist_sConvexComb_right_le** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：dist_sConvexComb_right_le (x : X) (f : StdSimplex Real X) : dist x f.sConv
exComb <= f.iConvexComb (dist x)
参数：x : X；f : StdSimplex Real X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.iConvexComb_eq_sum`：iConvexComb_eq_sum (w : StdSimplex R I) (f
 : I -> M) : w.iConvexComb f = w.weights.sum fun i r => r • f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Convexity.iConvexComb_congr`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用定理 `Convexity.iConvexComb_id'`：∀ {R : Type u_1} {M : Type u_3} [inst : Parti
alOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Co
nvexity.ConvexS…
· 使用引理 `Convexity.dist_iConvexComb_right_le`：dist_iConvexComb_right_le (x : X) (
f : StdSimplex Real I) (g : I -> X) : dist x (f.iConvexComb g) <= f.iConvexComb 
fun i => dist x (g i)
-/
lemma dist_sConvexComb_right_le (x : X) (f : StdSimplex ℝ X) :
    dist x f.sConvexComb ≤ f.iConvexComb (dist x) := by
  simpa using dist_iConvexComb_right_le x f id

@[simp]
/-
**Convexity.dist_convexCombPair_left** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：dist_convexCombPair_left {s t : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s +
 t = 1) (x y : X) : dist (convexCombPair s t hs ht h x y) x = t * dist x y
参数：hs : 0 <= s；ht : 0 <= t；h : s + t = 1；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.convexCombPair.eq_1`：∀ {R : Type u_1} {M : Type u_3} [inst : P
artialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [inst_3 
: Convexity.ConvexS…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Convexity.dist_sConvexComb_left_le`：dist_sConvexComb_left_le (f : StdSim
plex Real X) (x : X) : dist f.sConvexComb x <= f.iConvexComb (dist · x)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Convexity.iConvexComb_eq_sum`：iConvexComb_eq_sum (w : StdSimplex R I) (f
 : I -> M) : w.iConvexComb f = w.weights.sum fun i r => r • f i
· 使用定理 `Convexity.StdSimplex.weights_duple`：∀ {R : Type u} [inst : PartialOrder 
R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R] (x y : 
M)   {s t : R} (hs : 0 ≤…
· 使用定理 `Finsupp.sum_add_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : DecidableEq α] [inst_1 : AddZeroClass M]   [inst_2 : AddCommMonoid N] {f 
g : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_sub_iff_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a = b - c ↔ c + a = b
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
（共 36 条，此处仅展示前 30 条）
-/
lemma dist_convexCombPair_left
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : X) :
    dist (convexCombPair s t hs ht h x y) x = t * dist x y := by
  classical
  suffices H : ∀ {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : X),
      dist (convexCombPair s t hs ht h x y) x ≤ t * dist x y by
    refine (H ..).antisymm ?_
    conv_lhs => rw [eq_sub_iff_add_eq'.mpr h, sub_mul, one_mul]
    grw [sub_le_iff_le_add, dist_comm x y, ← H ht hs ((add_comm _ _).trans h) y x, dist_comm,
      convexCombPair_symm, ← dist_triangle_left]
  intro s t hs ht h x y
  grw [convexCombPair, dist_sConvexComb_left_le]
  simp [iConvexComb_eq_sum, Finsupp.sum_add_index, add_mul, dist_comm y x]

@[simp]
/-
**Convexity.dist_convexCombPair_right** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：dist_convexCombPair_right {s t : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s 
+ t = 1) (x y : X) : dist (convexCombPair s t hs ht h x y) y = s * dist x y
参数：hs : 0 <= s；ht : 0 <= t；h : s + t = 1；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.convexCombPair_symm`：convexCombPair_symm {x y : M} : convexCom
bPair s t hs ht h x y = convexCombPair t s ht hs ((add_comm _ _).trans h) y x
· 使用引理 `Convexity.dist_convexCombPair_left`：dist_convexCombPair_left {s t : Real
} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : X) : dist (convexCombPair s
 t hs ht h x y) x = t * …
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
-/
lemma dist_convexCombPair_right
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : X) :
    dist (convexCombPair s t hs ht h x y) y = s * dist x y := by
  rw [convexCombPair_symm, dist_convexCombPair_left, dist_comm]

@[simp]
/-
**Convexity.dist_left_convexCombPair** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：dist_left_convexCombPair {s t : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s +
 t = 1) (x y : X) : dist x (convexCombPair s t hs ht h x y) = t * dist x y
参数：hs : 0 <= s；ht : 0 <= t；h : s + t = 1；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用引理 `Convexity.dist_convexCombPair_left`：dist_convexCombPair_left {s t : Real
} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : X) : dist (convexCombPair s
 t hs ht h x y) x = t * …
-/
lemma dist_left_convexCombPair
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : X) :
    dist x (convexCombPair s t hs ht h x y) = t * dist x y := by
  rw [dist_comm, dist_convexCombPair_left]

@[simp]
/-
**Convexity.dist_right_convexCombPair** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：dist_right_convexCombPair {s t : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s 
+ t = 1) (x y : X) : dist y (convexCombPair s t hs ht h x y) = s * dist x y
参数：hs : 0 <= s；ht : 0 <= t；h : s + t = 1；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用引理 `Convexity.dist_convexCombPair_right`：dist_convexCombPair_right {s t : Re
al} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : X) : dist (convexCombPair
 s t hs ht h x y) y = s *…
-/
lemma dist_right_convexCombPair
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : X) :
    dist y (convexCombPair s t hs ht h x y) = s * dist x y := by
  rw [dist_comm, dist_convexCombPair_right]

/-- `dist(sx + (1-s)y, s'x + (1-s')y) = |s - s'| dist(x, y)`.

See `dist_convexCombPair_convexCombPair_le`
for the version where the weights are fixed and the points change. -/
/-
**Convexity.dist_convexCombPair_convexCombPair** 是 Mathlib 中的一个引理，位于命名空间 `Convex
ity`。
形式化陈述：dist_convexCombPair_convexCombPair {s t s' t' : Real} (hs : 0 <= s) (ht : 
0 <= t) (h : s + t = 1) (hs' : 0 <= s') (ht' : 0 <= t') (h' : s' + t' = 1) (x y 
: X) : dist (convexCombPair s t hs ht h x y) (convexCombPair s' t' hs' ht' h' x 
y) = |s - s'| * dist x y
参数：hs : 0 <= s；ht : 0 <= t；h : s + t = 1；hs' : 0 <= s'；ht' : 0 <= t'；h' : s' + t
' = 1；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.equivFunOnFinite_symm_apply_apply`：∀ {α : Type u_1} {M : Type u_
4} [inst : Zero M] [inst_1 : Finite α] (f : α → M) (a : α),   (Finsupp.equivFunO
nFinite.symm f) a = f a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
`dist(sx + (1-s)y, s'x + (1-s')y) = |s - s'| dist(x, y)`.

See `dist_convexCombPair_convexCombPair_le`
for the version where the weights are fixed and the points change.
-/
lemma dist_convexCombPair_convexCombPair
    {s t s' t' : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1)
    (hs' : 0 ≤ s') (ht' : 0 ≤ t') (h' : s' + t' = 1) (x y : X) :
    dist (convexCombPair s t hs ht h x y) (convexCombPair s' t' hs' ht' h' x y) =
      |s - s'| * dist x y := by
  wlog hss' : s' ≤ s generalizing s t s' t'
  · rw [dist_comm, this, abs_sub_comm]; exact le_of_not_ge hss'
  suffices dist (convexCombPair s t hs ht h x y) (convexCombPair s' t' hs' ht' h' x y) ≤
      |s - s'| * dist x y by
    refine this.antisymm ?_
    nth_grw 2 [← abs_dist_sub_le (z := x)]
    have : |t - t'| = |s - s'| := by
      rw [eq_sub_iff_add_eq.mpr h, eq_sub_iff_add_eq.mpr h']; simp [abs_sub_comm t t']
    simp [← sub_mul, this]
  let f : StdSimplex ℝ (Fin 3) :=
  { weights := Finsupp.equivFunOnFinite.symm ![s', s - s', t]
    nonneg i := by fin_cases i <;> simp [*]
    total := by simp [Finsupp.sum_fintype, Fin.sum_univ_succ, ← add_assoc, h] }
  convert dist_iConvexComb_le f ![x, x, y] ![x, y, y] using 1
  swap; · simp [Finsupp.sum_fintype, Fin.sum_univ_succ, f, hss', iConvexComb_eq_sum]
  congr 1
  · delta convexCombPair
    congr 1
    ext a
    simp [StdSimplex.duple, StdSimplex.map, Finsupp.mapDomain,
      Finsupp.sum_fintype, Fin.sum_univ_succ, f, ← add_assoc]
  · delta convexCombPair
    congr 1
    ext a
    simp [StdSimplex.duple, StdSimplex.map, Finsupp.mapDomain,
      Finsupp.sum_fintype, Fin.sum_univ_succ, f, show t' = s - s' + t by grind]

/-- `dist(sx + (1-s)y, sx' + (1-s)y') ≤ s dist(x, x') + (1-s) dist(y, y')`.

See `dist_convexCombPair_convexCombPair`
for the version where the points are fixed and the weights change. -/
/-
**Convexity.dist_convexCombPair_convexCombPair_le** 是 Mathlib 中的一个引理，位于命名空间 `Con
vexity`。
形式化陈述：dist_convexCombPair_convexCombPair_le {s t : Real} (hs : 0 <= s) (ht : 0 <
= t) (h : s + t = 1) (x y x' y' : X) : dist (convexCombPair s t hs ht h x y) (co
nvexCombPair s t hs ht h x' y') <= s * dist x x' + t * dist y y'
参数：hs : 0 <= s；ht : 0 <= t；h : s + t = 1；x y x' y' : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.convexCombPair_def`：convexCombPair_def (p q : M) : convexCombP
air s t hs ht h p q = (StdSimplex.duple 0 1 hs ht h).iConvexComb ![p, q]
· 使用定理 `Convexity.iConvexComb_congr`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Convexity.iConvexComb_eq_sum`：iConvexComb_eq_sum (w : StdSimplex R I) (f
 : I -> M) : w.iConvexComb f = w.weights.sum fun i r => r • f i
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用引理 `Convexity.dist_iConvexComb_le`：dist_iConvexComb_le {ι : Type*} (f : StdS
implex Real ι) (x y : ι -> X) : dist (f.iConvexComb x) (f.iConvexComb y) <= f.iC
onvexComb fun i => …

--- 原说明 ---
`dist(sx + (1-s)y, sx' + (1-s)y') ≤ s dist(x, x') + (1-s) dist(y, y')`.

See `dist_convexCombPair_convexCombPair`
for the version where the points are fixed and the weights change.
-/
lemma dist_convexCombPair_convexCombPair_le
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y x' y' : X) :
    dist (convexCombPair s t hs ht h x y) (convexCombPair s t hs ht h x' y') ≤
      s * dist x x' + t * dist y y' := by
  convert dist_iConvexComb_le (.duple (M := Fin 2) 0 1 hs ht h) ![x, y] ![x', y']
  · simp [convexCombPair_def]
  · simp [convexCombPair_def]
  · simp [Finsupp.sum_fintype, Fin.sum_univ_succ, StdSimplex.duple, iConvexComb_eq_sum]

/-- The convex combination `(t, p, q) ↦ t • p + (1 - t) • q` is continuous on `[0, 1] × X × X`
for a convex metric space `X`. -/
/-
**Convexity.continuous_convexCombPair** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：continuous_convexCombPair : Continuous fun x : Set.Icc (0 : Real) 1 × (X ×
 X) => convexCombPair (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_prod_of_continuous_lipschitzWith'`：continuous_prod_of_continu
ous_lipschitzWith' [TopologicalSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpa
ce γ] (f : α × β -> γ) (K : Real>=…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Convexity.dist_convexCombPair_convexCombPair_le`：dist_convexCombPair_con
vexCombPair_le {s t : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y x' 
y' : X) : dist (convexCombPair s t hs…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Prod.dist_eq`：Prod.dist_eq {x y : α × β} : dist x y = max (dist x.1 y.1)
 (dist x.2 y.2)
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Convexity.dist_convexCombPair_convexCombPair`：dist_convexCombPair_convex
CombPair {s t s' t' : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (hs' : 0
 <= s') (ht' : 0 <= t') (h' : s' +…
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖

--- 原说明 ---
The convex combination `(t, p, q) ↦ t • p + (1 - t) • q` is continuous on `[0, 1
] × X × X`
for a convex metric space `X`.
-/
lemma continuous_convexCombPair :
    Continuous fun x : Set.Icc (0 : ℝ) 1 × (X × X) ↦ convexCombPair (R := ℝ)
      ↑x.1 (1 - ↑x.1) x.1.prop.left (by simpa using x.1.prop.right) (add_sub_cancel ..)
      x.2.1 x.2.2 := by
  apply continuous_prod_of_continuous_lipschitzWith' (K := 1)
  · intro i x y
    simp only [← coe_nnreal_ennreal_nndist, ENNReal.coe_one, one_mul, ENNReal.coe_le_coe,
      NNReal.toReal_le, coe_nndist]
    grw [dist_convexCombPair_convexCombPair_le, Prod.dist_eq]
    nth_grw 1 [le_max_left (dist x.1 y.1) (dist x.2 y.2)]
    swap; · simpa using i.prop.left
    nth_grw 2 [le_max_right (dist x.1 y.1) (dist x.2 y.2)]
    swap; · simpa using i.prop.right
    rw [← add_mul, add_sub_cancel, one_mul]
  · intro b
    refine LipschitzWith.continuous (K := nndist b.1 b.2) fun x y ↦ ?_
    rw [mul_comm]
    simp [← coe_nnreal_ennreal_nndist, ← ENNReal.coe_mul, NNReal.toReal_le,
      dist_convexCombPair_convexCombPair, Subtype.dist_eq, dist_eq_norm]

@[deprecated (since := "2026-05-15")] alias continuous_convexComboPair := continuous_convexCombPair
/-
**Convexity.continuous_convexCombPair_of_isBounded** 是 Mathlib 中的一个引理，位于命名空间 `Co
nvexity`。
形式化陈述：continuous_convexCombPair_of_isBounded {T : Type*} [TopologicalSpace T] (f
 : T -> Real) (hf : Continuous f) (hf0 : forall t, 0 <= f t) (hf1 : forall t, f 
t <= 1) (x y : T -> X) (hx : ContinuousOn x (f ⁻¹' {0}ᶜ)) (hy : ContinuousOn y (
f ⁻¹' {1}ᶜ)) (hx' : Bornology.IsBounded (Set.range x)) (hy' : Bornology.IsBounde
d (Set.range y)) : Continuous fun i => convexCombPair (f i) (1 - f i) (hf0 _) (b
y simpa using hf1 _) (add_sub_cancel ..) (x i) (y i)
参数：f : T -> Real；hf : Continuous f；hf0 : forall t, 0 <= f t；hf1 : forall t, f t 
<= 1；x y : T -> X；hx : ContinuousOn x (f ⁻¹' {0}ᶜ)；hy : ContinuousOn y (f ⁻¹' {1
}ᶜ)；hx' : Bornology.IsBounded (Set.range x)；hy' : Bornology.IsBounded (Set.range
 y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isBounded_iff_eventually`：isBounded_iff_eventually {s : Set α} : 
IsBounded s ↔ forallᶠ C in atTop, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> di
st x y <= C
· 使用定理 `Bornology.IsBounded.union`：∀ {α : Type u_2} {x : Bornology α} {s t : Set
 α},   Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s ∪ 
t)
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Topology.IsOpenEmbedding.continuousAt_iff`：∀ {X : Type u_1} {Y : Type u_
2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 
: TopologicalSpace Y] [inst_2 :…
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Continuous.comp₃`：Continuous.comp₃ {g : X × Y × Z -> ε} (hg : Continuous
 g) {e : W -> X} (he : Continuous e) {f : W -> Y} (hf : Continuous f) {k : W -> 
Z} (hk…
· 使用引理 `Convexity.continuous_convexCombPair`：continuous_convexCombPair : Continu
ous fun x : Set.Icc (0 : Real) 1 × (X × X) => convexCombPair (R
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
（共 139 条，此处仅展示前 30 条）
-/
lemma continuous_convexCombPair_of_isBounded
    {T : Type*} [TopologicalSpace T] (f : T → ℝ) (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1) (x y : T → X)
    (hx : ContinuousOn x (f ⁻¹' {0}ᶜ)) (hy : ContinuousOn y (f ⁻¹' {1}ᶜ))
    (hx' : Bornology.IsBounded (Set.range x)) (hy' : Bornology.IsBounded (Set.range y)) :
    Continuous fun i ↦ convexCombPair (f i) (1 - f i) (hf0 _) (by simpa using hf1 _)
      (add_sub_cancel ..) (x i) (y i) := by
  obtain ⟨D, hD, hD'⟩ := ((Metric.isBounded_iff_eventually.mp (hx'.union hy')).and
    (Filter.eventually_gt_atTop 0)).exists
  replace hD := fun t₁ t₂ ↦ hD (.inl (Set.mem_range_self t₁)) (.inr (Set.mem_range_self t₂))
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : f t ∈ Set.Ioo 0 1
  · exact ((isOpen_Ioo.preimage hf).isOpenEmbedding_subtypeVal.continuousAt_iff
      (x := ⟨t, ht⟩)).mp ((continuous_convexCombPair (X := X)).comp₃ (W := f ⁻¹' Set.Ioo 0 1)
      (e := fun i ↦ ⟨f i, Set.Ioo_subset_Icc_self i.prop⟩) (f := x ∘ (↑)) (k := y ∘ (↑))
      (by fun_prop) (hx.comp_continuous continuous_subtype_val (by simp_all; grind))
      (hy.comp_continuous continuous_subtype_val (by simp_all; grind))).continuousAt
  obtain ht | ht : f t = 0 ∨ f t = 1 := by
    simpa [le_antisymm_iff, hf0, hf1, -not_and, not_and_or] using ht
  · simp only [ContinuousAt, ht, sub_zero, convexCombPair_zero]
    rw [Metric.nhds_basis_ball.tendsto_right_iff]
    intro r hr
    filter_upwards [hy.continuousAt ((hf.isOpen_preimage _ isClosed_singleton.isOpen_compl).mem_nhds
      (x := t) (by simp [*])) (Metric.ball_mem_nhds _ (show 0 < r / 3 by simpa)),
      hf.tendsto' _ _ ht (Metric.ball_mem_nhds _ (show 0 < r / D / 3 by simp [*]))] with j hj hj'
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hj hj' ⊢
    grw [dist_triangle _ (convexCombPair (f j) (1 - f j) (hf0 _) (by simpa using hf1 _)
      (add_sub_cancel ..) (x j) (y t)), dist_convexCombPair_convexCombPair_le]
    simp only [dist_self, mul_zero, zero_add, dist_convexCombPair_right]
    grw [sub_le_self _ (hf0 _), hj, hD, (le_abs_self _).trans hj'.le]
    · field_simp; norm_num
    · exact hf0 _
  · simp only [ContinuousAt, ht, sub_self, convexCombPair_one]
    rw [Metric.nhds_basis_ball.tendsto_right_iff]
    intro r hr
    filter_upwards [hx.continuousAt ((hf.isOpen_preimage _ isClosed_singleton.isOpen_compl).mem_nhds
      (x := t) (by simp [*])) (Metric.ball_mem_nhds _ (show 0 < r / 3 by simpa)),
      hf.tendsto' _ _ ht (Metric.ball_mem_nhds _ (show 0 < r / D / 3 by simp [*]))] with j hj hj'
    simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hj hj' ⊢
    grw [dist_triangle _ (convexCombPair (f j) (1 - f j) (hf0 _) (by simpa using hf1 _)
      (add_sub_cancel ..) (x t) (y j)), dist_convexCombPair_convexCombPair_le]
    simp only [dist_self, mul_zero, add_zero, dist_convexCombPair_left]
    grw [abs_sub_comm, ← le_abs_self] at hj'
    grw [hj.le, hj'.le, hf1, hD]
    · field_simp; norm_num
    · exact hf0 _

/-- When `X` is a bounded convex metric space, to check continuity of
`t ↦ f(t) • x(t) + (1 - f(t)) • y(t)` it suffices to show that `f` is continuous,
`x` is continuous away from `f(t) = 0`, and `y` is continuous away from `f(t) = 1`. -/
/-
**Convexity.continuous_convexCombPair'** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：continuous_convexCombPair' [BoundedSpace X] {T : Type*} [TopologicalSpace 
T] (f : T -> Real) (hf : Continuous f) (hf0 : forall t, 0 <= f t) (hf1 : forall 
t, f t <= 1) (x y : T -> X) (hx : ContinuousOn x (f ⁻¹' {0}ᶜ)) (hy : ContinuousO
n y (f ⁻¹' {1}ᶜ)) : Continuous fun i => convexCombPair (f i) (1 - f i) (hf0 _) (
by simpa using hf1 _) (add_sub_cancel ..) (x i) (y i)
参数：f : T -> Real；hf : Continuous f；hf0 : forall t, 0 <= f t；hf1 : forall t, f t 
<= 1；x y : T -> X；hx : ContinuousOn x (f ⁻¹' {0}ᶜ)；hy : ContinuousOn y (f ⁻¹' {1
}ᶜ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Convexity.continuous_convexCombPair_of_isBounded`：continuous_convexCombP
air_of_isBounded {T : Type*} [TopologicalSpace T] (f : T -> Real) (hf : Continuo
us f) (hf0 : forall t, 0 <= f t) (hf1 …
· 使用定理 `Bornology.IsBounded.all`：∀ {α : Type u_2} [inst : Bornology α] [BoundedS
pace α] (s : Set α), Bornology.IsBounded s

--- 原说明 ---
When `X` is a bounded convex metric space, to check continuity of
`t ↦ f(t) • x(t) + (1 - f(t)) • y(t)` it suffices to show that `f` is continuous
,
`x` is continuous away from `f(t) = 0`, and `y` is continuous away from `f(t) = 
1`.
-/
lemma continuous_convexCombPair' [BoundedSpace X]
    {T : Type*} [TopologicalSpace T] (f : T → ℝ) (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1) (x y : T → X)
    (hx : ContinuousOn x (f ⁻¹' {0}ᶜ)) (hy : ContinuousOn y (f ⁻¹' {1}ᶜ)) :
    Continuous fun i ↦ convexCombPair (f i) (1 - f i) (hf0 _) (by simpa using hf1 _)
      (add_sub_cancel ..) (x i) (y i) :=
  continuous_convexCombPair_of_isBounded f hf hf0 hf1 x y hx hy (.all _) (.all _)

@[deprecated (since := "2026-05-15")]
alias continuous_convexComboPair' := continuous_convexCombPair'

attribute [local instance] AddTorsor.toConvexSpace in
/-
**Convexity.** 是 Mathlib 中的一个实例，位于命名空间 `Convexity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {V P : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] :
    IsConvexDist P where
  dist_iConvexComb_fst_snd_le f := by
    let p : P := Nonempty.some inferInstance
    simp only [AddTorsor.iConvexComb_eq_affineCombination]
    rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ f.total p,
      Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ f.total p]
    suffices ‖f.weights.sum fun a b ↦ b • (a.1 -ᵥ a.2)‖ ≤
      f.weights.sum fun a b ↦ b * ‖a.1 -ᵥ a.2‖ by
      simpa [dist_eq_norm_vsub, Finsupp.sum, ← Finset.sum_sub_distrib, ← smul_sub]
    grw [Finsupp.sum, Finsupp.sum, norm_sum_le]
    simp [norm_smul, abs_eq_self.mpr (f.nonneg _)]
/-
**Convexity.IsConvexDist.subtype** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvexDi
st`。
形式化陈述：∀ {X : Type u_2} [inst : Convexity.ConvexSpace ℝ X] [inst_1 : MetricSpace 
X] [Convexity.IsConvexDist X] (s : Set X)   (hs : Convexity.IsConvexSet ℝ s), Co
nvexity.IsConvexDist ↑s
参数：s : Set X；hs : Convexity.IsConvexSet ℝ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.subtypeVal_iConvexComb`：subtypeVal_iConvexComb (s : Set X) (hs
 : IsConvexSet R s) (w : StdSimplex R I) (f : I -> s) : letI : ConvexSpace R s
· 使用定理 `Convexity.iConvexComb_map`：∀ {R : Type u_1} {M : Type u_3} {I : Type u_6
} {J : Type u_7} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStr
ictOrderedRing …
· 使用定理 `Convexity.iConvexComb_congr`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Convexity.iConvexComb_eq_sum`：iConvexComb_eq_sum (w : StdSimplex R I) (f
 : I -> M) : w.iConvexComb f = w.weights.sum fun i r => r • f i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Convexity.IsConvexDist.dist_iConvexComb_fst_snd_le`：∀ {X : Type u_2} [in
st₁ : Convexity.ConvexSpace ℝ X] [inst₂ : MetricSpace X] [self : Convexity.IsCon
vexDist X]   (f : Convexity.StdSimplex ℝ…
-/
instance IsConvexDist.subtype (s : Set X) (hs : IsConvexSet ℝ s) :
    letI : ConvexSpace ℝ s := .subtype s hs
    IsConvexDist s := by
  let : ConvexSpace ℝ s := .subtype s hs
  refine ⟨fun f ↦ ?_⟩
  convert dist_iConvexComb_fst_snd_le (X := X) (f.map fun x ↦ (x.1, x.2)) <;>
    simp [Subtype.dist_eq, Finsupp.sum_mapDomain_index, add_mul]
/-
**Convexity.IsConvexDist.submodule** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvex
Dist`。
形式化陈述：∀ {F : Type u_3} {M : Type u_4} [inst : AddCommGroup M] [inst_1 : MetricSp
ace M] [inst_2 : _root_.Module ℝ M]   [inst_3 : Convexity.ConvexSpace ℝ M] [inst
_4 : Convexity.IsModuleConvexSpace ℝ M] [Convexity.IsConvexDist M]   [inst_6 : S
etLike F M] [inst_7 : AddSubmonoidClass F M] [inst_8 : SMulMemClass F ℝ M] {S : 
F},   Convexity.IsConvexDist ↥S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsConvexDist.subtype`：∀ {X : Type u_2} [inst : Convexity.Conve
xSpace ℝ X] [inst_1 : MetricSpace X] [Convexity.IsConvexDist X] (s : Set X)   (h
s : Convexity.IsConv…
· 使用定理 `Convexity.isConvexSet_coe`：∀ {F : Type u_1} {R : Type u_2} {M : Type u_3
} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRing 
R] [inst_3 : Ad…
-/
instance IsConvexDist.submodule {F M : Type*} [AddCommGroup M] [MetricSpace M]
    [Module ℝ M] [ConvexSpace ℝ M] [IsModuleConvexSpace ℝ M] [IsConvexDist M]
    [SetLike F M] [AddSubmonoidClass F M] [SMulMemClass F ℝ M] {S : F} :
    IsConvexDist S := .subtype _ _

end Convexity

