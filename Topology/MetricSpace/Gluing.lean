/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Group
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Metric space gluing

Gluing two metric spaces along a common subset. Formally, we are given

```
     Φ
  Z ---> X
  |
  |Ψ
  v
  Y
```
where `hΦ : Isometry Φ` and `hΨ : Isometry Ψ`.
We want to complete the square by a space `GlueSpace hΦ hΨ` and two isometries
`toGlueL hΦ hΨ` and `toGlueR hΦ hΨ` that make the square commute.
We start by defining a predistance on the disjoint union `X ⊕ Y`, for which
points `Φ p` and `Ψ p` are at distance 0. The (quotient) metric space associated
to this predistance is the desired space.

This is an instance of a more general construction, where `Φ` and `Ψ` do not have to be isometries,
but the distances in the image almost coincide, up to `2ε` say. Then one can almost glue the two
spaces so that the images of a point under `Φ` and `Ψ` are `ε`-close. If `ε > 0`, this yields a
metric space structure on `X ⊕ Y`, without the need to take a quotient. In particular,
this gives a natural metric space structure on `X ⊕ Y`, where the basepoints
are at distance 1, say, and the distances between other points are obtained by going through the two
basepoints.
(We also register the same metric space structure on a general disjoint union `Σ i, E i`).

We also define the inductive limit of metric spaces. Given
```
     f 0        f 1        f 2        f 3
X 0 -----> X 1 -----> X 2 -----> X 3 -----> ...
```
where the `X n` are metric spaces and `f n` isometric embeddings, we define the inductive
limit of the `X n`, also known as the increasing union of the `X n` in this context, if we
identify `X n` and `X (n+1)` through `f n`. This is a metric space in which all `X n` embed
isometrically and in a way compatible with `f n`.

-/

@[expose] public section

noncomputable section

universe u v w

open Function Set Uniformity Topology

namespace Metric

section ApproxGluing

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [MetricSpace X] [MetricSpace Y] {Φ : Z → X} {Ψ : Z → Y} {ε : ℝ}

/-- Define a predistance on `X ⊕ Y`, for which `Φ p` and `Ψ p` are at distance `ε` -/
/-
**Metric.glueDist** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：{X : Type u} →   {Y : Type v} → {Z : Type w} → [MetricSpace X] → [MetricSp
ace Y] → (Z → X) → (Z → Y) → ℝ → X ⊕ Y → X ⊕ Y → ℝ
参数：Z → X；Z → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a predistance on `X ⊕ Y`, for which `Φ p` and `Ψ p` are at distance `ε`
-/
def glueDist (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : X ⊕ Y → X ⊕ Y → ℝ
  | .inl x, .inl y => dist x y
  | .inr x, .inr y => dist x y
  | .inl x, .inr y => (⨅ p, dist x (Φ p) + dist y (Ψ p)) + ε
  | .inr x, .inl y => (⨅ p, dist y (Φ p) + dist x (Ψ p)) + ε

set_option backward.privateInPublic true in
/-
**Metric.glueDist_self** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem glueDist_self (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : ∀ x, glueDist Φ Ψ ε x x = 0
  | .inl _ => dist_self _
  | .inr _ => dist_self _
/-
**Metric.glueDist_glued_points** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：glueDist_glued_points [Nonempty Z] (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (p
 : Z) : glueDist Φ Ψ ε (.inl (Φ p)) (.inr (Ψ p)) = ε
参数：Φ : Z -> X；Ψ : Z -> Y；ε : Real；p : Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem glueDist_glued_points [Nonempty Z] (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (p : Z) :
    glueDist Φ Ψ ε (.inl (Φ p)) (.inr (Ψ p)) = ε := by
  have : ⨅ q, dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) = 0 := by
    have A : ∀ q, 0 ≤ dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) := fun _ => by positivity
    refine le_antisymm ?_ (le_ciInf A)
    have : 0 = dist (Φ p) (Φ p) + dist (Ψ p) (Ψ p) := by simp
    rw [this]
    exact ciInf_le ⟨0, forall_mem_range.2 A⟩ p
  simp only [glueDist, this, zero_add]

set_option backward.privateInPublic true in
/-
**Metric.glueDist_comm** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem glueDist_comm (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) :
    ∀ x y, glueDist Φ Ψ ε x y = glueDist Φ Ψ ε y x
  | .inl _, .inl _ => dist_comm _ _
  | .inr _, .inr _ => dist_comm _ _
  | .inl _, .inr _ => rfl
  | .inr _, .inl _ => rfl
/-
**Metric.glueDist_swap** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {X : Type u} {Y : Type v} {Z : Type w} [inst : MetricSpace X] [inst_1 : 
MetricSpace Y] (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ)   (x y : X ⊕ Y), Metric.glueDist 
Ψ Φ ε x.swap y.swap = Metric.glueDist Φ Ψ ε x y
参数：Φ : Z → X；Ψ : Z → Y；ε : ℝ；x y : X ⊕ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem glueDist_swap (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) :
    ∀ x y, glueDist Ψ Φ ε x.swap y.swap = glueDist Φ Ψ ε x y
  | .inl _, .inl _ => rfl
  | .inr _, .inr _ => rfl
  | .inl _, .inr _ => by simp only [glueDist, Sum.swap_inl, Sum.swap_inr, add_comm]
  | .inr _, .inl _ => by simp only [glueDist, Sum.swap_inl, Sum.swap_inr, add_comm]
/-
**Metric.le_glueDist_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：le_glueDist_inl_inr (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (x y) : ε <= glue
Dist Φ Ψ ε (.inl x) (.inr y)
参数：Φ : Z -> X；Ψ : Z -> Y；ε : Real；x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Real.iInf_nonneg`：iInf_nonneg (hf : forall i, 0 <= f i) : 0 <= iInf f
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
theorem le_glueDist_inl_inr (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (x y) :
    ε ≤ glueDist Φ Ψ ε (.inl x) (.inr y) :=
  le_add_of_nonneg_left <| Real.iInf_nonneg fun _ => by positivity
/-
**Metric.le_glueDist_inr_inl** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：le_glueDist_inr_inl (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (x y) : ε <= glue
Dist Φ Ψ ε (.inr x) (.inl y)
参数：Φ : Z -> X；Ψ : Z -> Y；ε : Real；x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Topology.MetricSpace.Gluing.0.Metric.glueDist_comm`：∀ {
X : Type u} {Y : Type v} {Z : Type w} [inst : MetricSpace X] [inst_1 : MetricSpa
ce Y] (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ)   (x y : X ⊕ Y), Me…
· 使用定理 `Metric.le_glueDist_inl_inr`：le_glueDist_inl_inr (Φ : Z -> X) (Ψ : Z -> Y
) (ε : Real) (x y) : ε <= glueDist Φ Ψ ε (.inl x) (.inr y)
-/
theorem le_glueDist_inr_inl (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (x y) :
    ε ≤ glueDist Φ Ψ ε (.inr x) (.inl y) := by
  rw [glueDist_comm]; apply le_glueDist_inl_inr

section
variable [Nonempty Z]

/-
**Metric.glueDist_triangle_inl_inr_inr** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem glueDist_triangle_inl_inr_inr (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (x : X) (y z : Y) :
    glueDist Φ Ψ ε (.inl x) (.inr z) ≤
      glueDist Φ Ψ ε (.inl x) (.inr y) + glueDist Φ Ψ ε (.inr y) (.inr z) := by
  simp only [glueDist]
  rw [add_right_comm, add_le_add_iff_right]
  refine le_ciInf_add fun p => ciInf_le_of_le ⟨0, ?_⟩ p ?_
  · exact forall_mem_range.2 fun _ => by positivity
  · linarith [dist_triangle_left z (Ψ p) y]
/-
**Metric.glueDist_triangle_inl_inr_inl** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem glueDist_triangle_inl_inr_inl (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ)
    (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2 * ε) (x : X) (y : Y) (z : X) :
    glueDist Φ Ψ ε (.inl x) (.inl z) ≤
      glueDist Φ Ψ ε (.inl x) (.inr y) + glueDist Φ Ψ ε (.inr y) (.inl z) := by
  simp_rw [glueDist, add_add_add_comm _ ε, add_assoc]
  refine le_ciInf_add fun p => ?_
  rw [add_left_comm, add_assoc, ← two_mul]
  refine le_ciInf_add fun q => ?_
  rw [dist_comm z]
  linarith [dist_triangle4 x (Φ p) (Φ q) z, dist_triangle_left (Ψ p) (Ψ q) y, (abs_le.1 (H p q)).2]

set_option backward.privateInPublic true in
/-
**Metric.glueDist_triangle** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem glueDist_triangle (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ)
    (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2 * ε) :
    ∀ x y z, glueDist Φ Ψ ε x z ≤ glueDist Φ Ψ ε x y + glueDist Φ Ψ ε y z
  | .inl _, .inl _, .inl _ => dist_triangle _ _ _
  | .inr _, .inr _, .inr _ => dist_triangle _ _ _
  | .inr x, .inl y, .inl z => by
    simp only [← glueDist_swap Φ]
    apply glueDist_triangle_inl_inr_inr
  | .inr x, .inr y, .inl z => by
    simpa only [glueDist_comm, add_comm] using glueDist_triangle_inl_inr_inr _ _ _ z y x
  | .inl x, .inl y, .inr z => by
    simpa only [← glueDist_swap Φ, glueDist_comm, add_comm, Sum.swap_inl, Sum.swap_inr]
      using glueDist_triangle_inl_inr_inr Ψ Φ ε z y x
  | .inl _, .inr _, .inr _ => glueDist_triangle_inl_inr_inr ..
  | .inl x, .inr y, .inl z => glueDist_triangle_inl_inr_inl Φ Ψ ε H x y z
  | .inr x, .inl y, .inr z => by
    simp only [← glueDist_swap Φ]
    apply glueDist_triangle_inl_inr_inl
    simpa only [abs_sub_comm]

end

set_option backward.privateInPublic true in
/-
**Metric.eq_of_glueDist_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem eq_of_glueDist_eq_zero (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (ε0 : 0 < ε) :
    ∀ p q : X ⊕ Y, glueDist Φ Ψ ε p q = 0 → p = q
  | .inl x, .inl y, h => by rw [eq_of_dist_eq_zero h]
  | .inl x, .inr y, h => by exfalso; linarith [le_glueDist_inl_inr Φ Ψ ε x y]
  | .inr x, .inl y, h => by exfalso; linarith [le_glueDist_inr_inl Φ Ψ ε x y]
  | .inr x, .inr y, h => by rw [eq_of_dist_eq_zero h]
/-
**Metric.Sum.mem_uniformity_iff_glueDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Sum`。
形式化陈述：∀ {X : Type u} {Y : Type v} {Z : Type w} [inst : MetricSpace X] [inst_1 : 
MetricSpace Y] {Φ : Z → X} {Ψ : Z → Y}   {ε : ℝ},   0 < ε →     ∀ (s : Set ((X ⊕
 Y) × (X ⊕ Y))),       s ∈ uniformity (X ⊕ Y) ↔ ∃ δ > 0, ∀ (a b : X ⊕ Y), Metric
.glueDist Φ Ψ ε a b < δ → (a, b) ∈ s
参数：s : Set ((X ⊕ Y) × (X ⊕ Y))；X ⊕ Y；a b : X ⊕ Y；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Metric.le_glueDist_inl_inr`：le_glueDist_inl_inr (Φ : Z -> X) (Ψ : Z -> Y
) (ε : Real) (x y) : ε <= glueDist Φ Ψ ε (.inl x) (.inr y)
· 使用定理 `Metric.le_glueDist_inr_inl`：le_glueDist_inr_inl (Φ : Z -> X) (Ψ : Z -> Y
) (ε : Real) (x y) : ε <= glueDist Φ Ψ ε (.inr x) (.inl y)
-/
theorem Sum.mem_uniformity_iff_glueDist (hε : 0 < ε) (s : Set ((X ⊕ Y) × (X ⊕ Y))) :
    s ∈ 𝓤 (X ⊕ Y) ↔ ∃ δ > 0, ∀ a b, glueDist Φ Ψ ε a b < δ → (a, b) ∈ s := by
  simp only [Sum.uniformity, Filter.mem_sup, Filter.mem_map, mem_uniformity_dist, mem_preimage]
  constructor
  · rintro ⟨⟨δX, δX0, hX⟩, δY, δY0, hY⟩
    refine ⟨min (min δX δY) ε, lt_min (lt_min δX0 δY0) hε, ?_⟩
    rintro (a | a) (b | b) h <;> simp only [lt_min_iff] at h
    · exact hX h.1.1
    · exact absurd h.2 (le_glueDist_inl_inr _ _ _ _ _).not_gt
    · exact absurd h.2 (le_glueDist_inr_inl _ _ _ _ _).not_gt
    · exact hY h.1.2
  · rintro ⟨ε, ε0, H⟩
    constructor <;> exact ⟨ε, ε0, fun _ _ h => H _ _ h⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given two maps `Φ` and `Ψ` intro metric spaces `X` and `Y` such that the distances between
`Φ p` and `Φ q`, and between `Ψ p` and `Ψ q`, coincide up to `2 ε` where `ε > 0`, one can almost
glue the two spaces `X` and `Y` along the images of `Φ` and `Ψ`, so that `Φ p` and `Ψ p` are
at distance `ε`. -/
@[instance_reducible]
/-
**Metric.glueMetricApprox** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：glueMetricApprox [Nonempty Z] (Φ : Z -> X) (Ψ : Z -> Y) (ε : Real) (ε0 : 0
 < ε) (H : forall p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| <= 2 * ε) : MetricS
pace (X oplus Y) where dist
参数：Φ : Z -> X；Ψ : Z -> Y；ε : Real；ε0 : 0 < ε；H : forall p q, |dist (Φ p) (Φ q) -
 dist (Ψ p) (Ψ q)| <= 2 * ε。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Topology.MetricSpace.Gluing.0.Metric.glueDist_self`：∀ {
X : Type u} {Y : Type v} {Z : Type w} [inst : MetricSpace X] [inst_1 : MetricSpa
ce Y] (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ)   (x : X ⊕ Y), Metr…
· 使用定理 `_private.Mathlib.Topology.MetricSpace.Gluing.0.Metric.glueDist_comm`：∀ {
X : Type u} {Y : Type v} {Z : Type w} [inst : MetricSpace X] [inst_1 : MetricSpa
ce Y] (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ)   (x y : X ⊕ Y), Me…
· 使用定理 `_private.Mathlib.Topology.MetricSpace.Gluing.0.Metric.glueDist_triangle`
：∀ {X : Type u} {Y : Type v} {Z : Type w} [inst : MetricSpace X] [inst_1 : Metri
cSpace Y] [Nonempty Z] (Φ : Z → X)   (Ψ : Z → Y) (ε : ℝ),   (…
· 使用定理 `_private.Mathlib.Topology.MetricSpace.Gluing.0.Metric.eq_of_glueDist_eq_
zero`：∀ {X : Type u} {Y : Type v} {Z : Type w} [inst : MetricSpace X] [inst_1 : 
MetricSpace Y] (Φ : Z → X) (Ψ : Z → Y)   (ε : ℝ), 0 < ε → ∀ (p q :…

--- 原说明 ---
Given two maps `Φ` and `Ψ` intro metric spaces `X` and `Y` such that the distanc
es between
`Φ p` and `Φ q`, and between `Ψ p` and `Ψ q`, coincide up to `2 ε` where `ε > 0`
, one can almost
glue the two spaces `X` and `Y` along the images of `Φ` and `Ψ`, so that `Φ p` a
nd `Ψ p` are
at distance `ε`.
-/
def glueMetricApprox [Nonempty Z] (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (ε0 : 0 < ε)
    (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2 * ε) : MetricSpace (X ⊕ Y) where
  dist := glueDist Φ Ψ ε
  dist_self := glueDist_self Φ Ψ ε
  dist_comm := glueDist_comm Φ Ψ ε
  dist_triangle := glueDist_triangle Φ Ψ ε H
  eq_of_dist_eq_zero := eq_of_glueDist_eq_zero Φ Ψ ε ε0 _ _
  toUniformSpace := Sum.instUniformSpace
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ <| Sum.mem_uniformity_iff_glueDist ε0

end ApproxGluing

section Sum

/-!
### Metric on `X ⊕ Y`

A particular case of the previous construction is when one uses basepoints in `X` and `Y` and one
glues only along the basepoints, putting them at distance 1. We give a direct definition of
the distance, without `iInf`, as it is easier to use in applications, and show that it is equal to
the gluing distance defined above to take advantage of the lemmas we have already proved.
-/
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [MetricSpace X] [MetricSpace Y]

/-- Distance on a disjoint union. There are many (noncanonical) ways to put a distance compatible
with each factor.
If the two spaces are bounded, one can say for instance that each point in the first is at distance
`diam X + diam Y + 1` of each point in the second.
Instead, we choose a construction that works for unbounded spaces, but requires basepoints,
chosen arbitrarily.
We embed isometrically each factor, set the basepoints at distance 1,
arbitrarily, and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
/-
**Metric.Sum.dist** 是 Mathlib 中的一个定义，位于命名空间 `Metric.Sum`。
形式化陈述：{X : Type u} → {Y : Type v} → [MetricSpace X] → [MetricSpace Y] → X ⊕ Y → 
X ⊕ Y → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Distance on a disjoint union. There are many (noncanonical) ways to put a distan
ce compatible
with each factor.
If the two spaces are bounded, one can say for instance that each point in the f
irst is at distance
`diam X + diam Y + 1` of each point in the second.
Instead, we choose a construction that works for unbounded spaces, but requires 
basepoints,
chosen arbitrarily.
We embed isometrically each factor, set the basepoints at distance 1,
arbitrarily, and say that the distance from `a` to `b` is the sum of the distanc
es of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance b
y default.
-/
protected def Sum.dist : X ⊕ Y → X ⊕ Y → ℝ
  | .inl a, .inl a' => dist a a'
  | .inr b, .inr b' => dist b b'
  | .inl a, .inr b => dist a (Nonempty.some ⟨a⟩) + 1 + dist (Nonempty.some ⟨b⟩) b
  | .inr b, .inl a => dist b (Nonempty.some ⟨b⟩) + 1 + dist (Nonempty.some ⟨a⟩) a
/-
**Metric.Sum.dist_eq_glueDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Sum`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : MetricSpace X] [inst_1 : MetricSpace Y
] {p q : X ⊕ Y} (x : X) (y : Y),   Metric.Sum.dist p q = Metric.glueDist (fun x_
1 => ⋯.some) (fun x => ⋯.some) 1 p q
参数：x : X；y : Y；fun x_1 => ⋯.some；fun x => ⋯.some。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ciInf_unique`：∀ {α : Type u_1} {ι : Sort u_4} [inst : ConditionallyCompl
etePartialOrderInf α] [inst_1 : Unique ι] {s : ι → α},   ⨅ i, s i = s default
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Sum.dist_eq_glueDist {p q : X ⊕ Y} (x : X) (y : Y) :
    Sum.dist p q =
      glueDist (fun _ : Unit => Nonempty.some ⟨x⟩) (fun _ : Unit => Nonempty.some ⟨y⟩) 1 p q := by
  cases p <;> cases q <;> first | rfl | simp [Sum.dist, glueDist, dist_comm, add_comm,
    add_left_comm, add_assoc]

set_option backward.privateInPublic true in
/-
**Metric.Sum.dist_comm** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem Sum.dist_comm (x y : X ⊕ Y) : Sum.dist x y = Sum.dist y x := by
  cases x <;> cases y <;> simp [Sum.dist, _root_.dist_comm, add_comm, add_left_comm]
/-
**Metric.Sum.one_le_dist_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Sum`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : MetricSpace X] [inst_1 : MetricSpace Y
] {x : X} {y : Y},   1 ≤ Metric.Sum.dist (Sum.inl x) (Sum.inr y)
参数：Sum.inl x；Sum.inr y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Sum.dist.eq_3`：∀ {X : Type u} {Y : Type v} [inst : MetricSpace X]
 [inst_1 : MetricSpace Y] (x_2 : X) (y : Y),   Metric.Sum.dist (Sum.inl x_2) (Su
m.inr y) =…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem Sum.one_le_dist_inl_inr {x : X} {y : Y} : 1 ≤ Sum.dist (.inl x) (.inr y) := by
  grw [Sum.dist, ← le_add_of_nonneg_right dist_nonneg, ← le_add_of_nonneg_left dist_nonneg]
/-
**Metric.Sum.one_le_dist_inr_inl** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Sum`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : MetricSpace X] [inst_1 : MetricSpace Y
] {x : X} {y : Y},   1 ≤ Metric.Sum.dist (Sum.inr y) (Sum.inl x)
参数：Sum.inr y；Sum.inl x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Topology.MetricSpace.Gluing.0.Metric.Sum.dist_comm`：∀ {
X : Type u} {Y : Type v} [inst : MetricSpace X] [inst_1 : MetricSpace Y] (x y : 
X ⊕ Y),   Metric.Sum.dist x y = Metric.Sum.dist y x
· 使用定理 `Metric.Sum.one_le_dist_inl_inr`：∀ {X : Type u} {Y : Type v} [inst : Metr
icSpace X] [inst_1 : MetricSpace Y] {x : X} {y : Y},   1 ≤ Metric.Sum.dist (Sum.
inl x) (Sum.inr y)
-/
theorem Sum.one_le_dist_inr_inl {x : X} {y : Y} : 1 ≤ Sum.dist (.inr y) (.inl x) := by
  rw [Sum.dist_comm]; exact Sum.one_le_dist_inl_inr

set_option backward.privateInPublic true in
/-
**Metric.Sum.mem_uniformity** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem Sum.mem_uniformity (s : Set ((X ⊕ Y) × (X ⊕ Y))) :
    s ∈ 𝓤 (X ⊕ Y) ↔ ∃ ε > 0, ∀ a b, Sum.dist a b < ε → (a, b) ∈ s := by
  constructor
  · rintro ⟨hsX, hsY⟩
    rcases mem_uniformity_dist.1 hsX with ⟨εX, εX0, hX⟩
    rcases mem_uniformity_dist.1 hsY with ⟨εY, εY0, hY⟩
    refine ⟨min (min εX εY) 1, lt_min (lt_min εX0 εY0) zero_lt_one, ?_⟩
    rintro (a | a) (b | b) h
    · exact hX (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_left _ _)))
    · cases not_le_of_gt (lt_of_lt_of_le h (min_le_right _ _)) Sum.one_le_dist_inl_inr
    · cases not_le_of_gt (lt_of_lt_of_le h (min_le_right _ _)) Sum.one_le_dist_inr_inl
    · exact hY (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_right _ _)))
  · rintro ⟨ε, ε0, H⟩
    constructor <;> rw [Filter.mem_map, mem_uniformity_dist] <;> exact ⟨ε, ε0, fun _ _ h => H _ _ h⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The distance on the disjoint union indeed defines a metric space. All the distance properties
follow from our choice of the distance. The harder work is to show that the uniform structure
defined by the distance coincides with the disjoint union uniform structure. -/
@[instance_reducible]
/-
**Metric.metricSpaceSum** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：metricSpaceSum : MetricSpace (X oplus Y) where dist
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Topology.MetricSpace.Gluing.0.Metric.Sum.dist_comm`：∀ {
X : Type u} {Y : Type v} [inst : MetricSpace X] [inst_1 : MetricSpace Y] (x y : 
X ⊕ Y),   Metric.Sum.dist x y = Metric.Sum.dist y x

--- 原说明 ---
The distance on the disjoint union indeed defines a metric space. All the distan
ce properties
follow from our choice of the distance. The harder work is to show that the unif
orm structure
defined by the distance coincides with the disjoint union uniform structure.
-/
def metricSpaceSum : MetricSpace (X ⊕ Y) where
  dist := Sum.dist
  dist_self x := by cases x <;> simp only [Sum.dist, dist_self]
  dist_comm := Sum.dist_comm
  dist_triangle
    | .inl p, .inl q, .inl r => dist_triangle p q r
    | .inl p, .inr q, _ => by
      simp only [Sum.dist_eq_glueDist p q]
      exact glueDist_triangle _ _ _ (by simp) _ _ _
    | _, .inl q, .inr r => by
      simp only [Sum.dist_eq_glueDist q r]
      exact glueDist_triangle _ _ _ (by simp) _ _ _
    | .inr p, _, .inl r => by
      simp only [Sum.dist_eq_glueDist r p]
      exact glueDist_triangle _ _ _ (by simp) _ _ _
    | .inr p, .inr q, .inr r => dist_triangle p q r
  eq_of_dist_eq_zero {p q} h := by
    rcases p with p | p <;> rcases q with q | q
    · rw [eq_of_dist_eq_zero h]
    · exact eq_of_glueDist_eq_zero _ _ _ one_pos _ _ ((Sum.dist_eq_glueDist p q).symm.trans h)
    · exact eq_of_glueDist_eq_zero _ _ _ one_pos _ _ ((Sum.dist_eq_glueDist q p).symm.trans h)
    · rw [eq_of_dist_eq_zero h]
  toUniformSpace := Sum.instUniformSpace
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ Sum.mem_uniformity

attribute [local instance] metricSpaceSum
/-
**Metric.Sum.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Sum`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : MetricSpace X] [inst_1 : MetricSpace Y
] {x y : X ⊕ Y},   dist x y = Metric.Sum.dist x y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sum.dist_eq {x y : X ⊕ Y} : dist x y = Sum.dist x y := rfl

/-- The left injection of a space in a disjoint union is an isometry -/
/-
**Metric.isometry_inl** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isometry_inl : Isometry (Sum.inl : X -> X oplus Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…

--- 原说明 ---
The left injection of a space in a disjoint union is an isometry
-/
theorem isometry_inl : Isometry (Sum.inl : X → X ⊕ Y) :=
  Isometry.of_dist_eq fun _ _ => rfl

/-- The right injection of a space in a disjoint union is an isometry -/
/-
**Metric.isometry_inr** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isometry_inr : Isometry (Sum.inr : Y -> X oplus Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…

--- 原说明 ---
The right injection of a space in a disjoint union is an isometry
-/
theorem isometry_inr : Isometry (Sum.inr : Y → X ⊕ Y) :=
  Isometry.of_dist_eq fun _ _ => rfl

end Sum

namespace Sigma

/- Copy of the previous paragraph, but for arbitrary disjoint unions instead of the disjoint union
of two spaces. I.e., work with sigma types instead of sum types. -/
variable {ι : Type*} {E : ι → Type*} [∀ i, MetricSpace (E i)]

open scoped Classical in
/-- Distance on a disjoint union. There are many (noncanonical) ways to put a distance compatible
with each factor.
We choose a construction that works for unbounded spaces, but requires basepoints,
chosen arbitrarily.
We embed isometrically each factor, set the basepoints at distance 1, arbitrarily,
and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
/-
**Metric.Sigma.dist** 是 Mathlib 中的一个定义，位于命名空间 `Metric.Sigma`。
形式化陈述：{ι : Type u_1} → {E : ι → Type u_2} → [(i : ι) → MetricSpace (E i)] → (i :
 ι) × E i → (i : ι) × E i → ℝ
参数：i : ι；E i；i : ι；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Distance on a disjoint union. There are many (noncanonical) ways to put a distan
ce compatible
with each factor.
We choose a construction that works for unbounded spaces, but requires basepoint
s,
chosen arbitrarily.
We embed isometrically each factor, set the basepoints at distance 1, arbitraril
y,
and say that the distance from `a` to `b` is the sum of the distances of `a` and
 `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance b
y default.
-/
protected def dist : (Σ i, E i) → (Σ i, E i) → ℝ
  | ⟨i, x⟩, ⟨j, y⟩ =>
    if h : i = j then
      haveI : E j = E i := by rw [h]
      Dist.dist x (cast this y)
    else Dist.dist x (Nonempty.some ⟨x⟩) + 1 + Dist.dist (Nonempty.some ⟨y⟩) y

/-- A `Dist` instance on the disjoint union `Σ i, E i`.
We embed isometrically each factor, set the basepoints at distance 1, arbitrarily,
and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
@[instance_reducible]
/-
**Metric.Sigma.instDist** 是 Mathlib 中的一个定义，位于命名空间 `Metric.Sigma`。
形式化陈述：instDist : Dist (Σ i, E i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Dist` instance on the disjoint union `Σ i, E i`.
We embed isometrically each factor, set the basepoints at distance 1, arbitraril
y,
and say that the distance from `a` to `b` is the sum of the distances of `a` and
 `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance b
y default.
-/
def instDist : Dist (Σ i, E i) :=
  ⟨Sigma.dist⟩

attribute [local instance] Sigma.instDist

@[simp]
/-
**Metric.Sigma.dist_same** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Sigma`。
形式化陈述：dist_same (i : ι) (x y : E i) : dist (Sigma.mk i x) ⟨i, y⟩ = dist x y
参数：i : ι；x y : E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_same (i : ι) (x y : E i) : dist (Sigma.mk i x) ⟨i, y⟩ = dist x y := by
  simp [Dist.dist, Sigma.dist]

@[simp]
/-
**Metric.Sigma.dist_ne** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Sigma`。
形式化陈述：dist_ne {i j : ι} (h : i != j) (x : E i) (y : E j) : dist (⟨i, x⟩ : Σ k, E
 k) ⟨j, y⟩ = dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨y⟩) y
参数：h : i != j；x : E i；y : E j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem dist_ne {i j : ι} (h : i ≠ j) (x : E i) (y : E j) :
    dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩ = dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨y⟩) y :=
  dif_neg h
/-
**Metric.Sigma.one_le_dist_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Sigma`。
形式化陈述：one_le_dist_of_ne {i j : ι} (h : i != j) (x : E i) (y : E j) : 1 <= dist (
⟨i, x⟩ : Σ k, E k) ⟨j, y⟩
参数：h : i != j；x : E i；y : E j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Sigma.dist_ne`：dist_ne {i j : ι} (h : i != j) (x : E i) (y : E j)
 : dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩ = dist x (Nonempty.some ⟨x⟩) + 1 + dist (None
mpty.some …
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 35 条，此处仅展示前 30 条）
-/
theorem one_le_dist_of_ne {i j : ι} (h : i ≠ j) (x : E i) (y : E j) :
    1 ≤ dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩ := by
  rw [Sigma.dist_ne h x y]
  linarith [@dist_nonneg _ _ x (Nonempty.some ⟨x⟩), @dist_nonneg _ _ (Nonempty.some ⟨y⟩) y]
/-
**Metric.Sigma.fst_eq_of_dist_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Sigma`。
形式化陈述：fst_eq_of_dist_lt_one (x y : Σ i, E i) (h : dist x y < 1) : x.1 = y.1
参数：x y : Σ i, E i；h : dist x y < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Metric.Sigma.one_le_dist_of_ne`：one_le_dist_of_ne {i j : ι} (h : i != j)
 (x : E i) (y : E j) : 1 <= dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem fst_eq_of_dist_lt_one (x y : Σ i, E i) (h : dist x y < 1) : x.1 = y.1 := by
  cases x; cases y
  contrapose! h
  apply one_le_dist_of_ne h
/-
**Metric.Sigma.dist_triangle** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Sigma`。
形式化陈述：∀ {ι : Type u_1} {E : ι → Type u_2} [inst : (i : ι) → MetricSpace (E i)] (
x y z : (i : ι) × E i),   dist x z ≤ dist x y + dist y z
参数：i : ι；E i；x y z : (i : ι) × E i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Sigma.dist_same`：dist_same (i : ι) (x y : E i) : dist (Sigma.mk i
 x) ⟨i, y⟩ = dist x y
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `Metric.Sigma.dist_ne`：dist_ne {i j : ι} (h : i != j) (x : E i) (y : E j)
 : dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩ = dist x (Nonempty.some ⟨x⟩) + 1 + dist (None
mpty.some …
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `_private.Mathlib.Topology.MetricSpace.Gluing.0.Metric.Sigma.dist_triangl
e._abel_1_1`：∀ {ι : Type u_2} {E : ι → Type u_1} [inst : (i : ι) → MetricSpace (
E i)] (i : ι) (x : E i) (k : ι) (z : E k) (y : E i),   dist x y + dist y …
· 使用定理 `_private.Mathlib.Topology.MetricSpace.Gluing.0.Metric.Sigma.dist_triangl
e._abel_1_2`：∀ {ι : Type u_2} {E : ι → Type u_1} [inst : (i : ι) → MetricSpace (
E i)] (i : ι) (x : E i) (j : ι) (y z : E j),   dist x ⋯.some + 1 + (dist …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem dist_triangle (x y z : Σ i, E i) : dist x z ≤ dist x y + dist y z := by
  rcases x with ⟨i, x⟩; rcases y with ⟨j, y⟩; rcases z with ⟨k, z⟩
  rcases eq_or_ne i k with (rfl | hik)
  · rcases eq_or_ne i j with (rfl | hij)
    · simpa using dist_triangle x y z
    · simp only [Sigma.dist_same, Sigma.dist_ne hij, Sigma.dist_ne hij.symm]
      calc
        dist x z ≤ dist x (Nonempty.some ⟨x⟩) + 0 + 0 + (0 + 0 + dist (Nonempty.some ⟨z⟩) z) := by
          simpa only [zero_add, add_zero] using dist_triangle _ _ _
        _ ≤ _ := by apply_rules [add_le_add, le_rfl, dist_nonneg, zero_le_one]
  · rcases eq_or_ne i j with (rfl | hij)
    · simp only [Sigma.dist_ne hik, Sigma.dist_same]
      calc
        dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z ≤
            dist x y + dist y (Nonempty.some ⟨y⟩) + 1 + dist (Nonempty.some ⟨z⟩) z := by
          apply_rules [add_le_add, le_rfl, dist_triangle]
        _ = _ := by abel
    · rcases eq_or_ne j k with (rfl | hjk)
      · simp only [Sigma.dist_ne hij, Sigma.dist_same]
        calc
          dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z ≤
              dist x (Nonempty.some ⟨x⟩) + 1 + (dist (Nonempty.some ⟨z⟩) y + dist y z) := by
            apply_rules [add_le_add, le_rfl, dist_triangle]
          _ = _ := by abel
      · simp only [hik, hij, hjk, Sigma.dist_ne, Ne, not_false_iff]
        calc
          dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z =
              dist x (Nonempty.some ⟨x⟩) + 1 + 0 + (0 + 0 + dist (Nonempty.some ⟨z⟩) z) := by
            simp only [add_zero, zero_add]
          _ ≤ _ := by apply_rules [add_le_add, zero_le_one, dist_nonneg, le_rfl]
/-
**Metric.Sigma.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Sigma`。
形式化陈述：∀ {ι : Type u_1} {E : ι → Type u_2} [inst : (i : ι) → MetricSpace (E i)] (
s : Set ((i : ι) × E i)),   IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ (y : (i : ι) × E i), 
dist x y < ε → y ∈ s
参数：i : ι；E i；s : Set ((i : ι) × E i)；y : (i : ι) × E i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `isOpen_sigma_iff`：isOpen_sigma_iff {s : Set (Sigma σ)} : IsOpen s ↔ fora
ll i, IsOpen (Sigma.mk i ⁻¹' s)
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.mem_ball'`：mem_ball' : y in ball x ε ↔ dist x y < ε
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Sigma.dist_same`：dist_same (i : ι) (x y : E i) : dist (Sigma.mk i
 x) ⟨i, y⟩ = dist x y
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Metric.Sigma.one_le_dist_of_ne`：one_le_dist_of_ne {i j : ι} (h : i != j)
 (x : E i) (y : E j) : 1 <= dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
-/
protected theorem isOpen_iff (s : Set (Σ i, E i)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s := by
  constructor
  · rintro hs ⟨i, x⟩ hx
    obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, ball x ε ⊆ Sigma.mk i ⁻¹' s :=
      Metric.isOpen_iff.1 (isOpen_sigma_iff.1 hs i) x hx
    refine ⟨min ε 1, lt_min εpos zero_lt_one, ?_⟩
    rintro ⟨j, y⟩ hy
    rcases eq_or_ne i j with (rfl | hij)
    · simp only [Sigma.dist_same, lt_min_iff] at hy
      exact hε (mem_ball'.2 hy.1)
    · apply (lt_irrefl (1 : ℝ) _).elim
      calc
        1 ≤ Sigma.dist ⟨i, x⟩ ⟨j, y⟩ := Sigma.one_le_dist_of_ne hij _ _
        _ < 1 := hy.trans_le (min_le_right _ _)
  · refine fun H => isOpen_sigma_iff.2 fun i => Metric.isOpen_iff.2 fun x hx => ?_
    obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, ∀ y, dist (⟨i, x⟩ : Σ j, E j) y < ε → y ∈ s :=
      H ⟨i, x⟩ hx
    refine ⟨ε, εpos, fun y hy => ?_⟩
    apply hε ⟨i, y⟩
    rw [Sigma.dist_same]
    exact mem_ball'.1 hy

/-- A metric space structure on the disjoint union `Σ i, E i`.
We embed isometrically each factor, set the basepoints at distance 1, arbitrarily,
and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
@[instance_reducible]
/-
**Metric.Sigma.metricSpace** 是 Mathlib 中的一个定义，位于命名空间 `Metric.Sigma`。
形式化陈述：{ι : Type u_1} → {E : ι → Type u_2} → [(i : ι) → MetricSpace (E i)] → Metr
icSpace ((i : ι) × E i)
参数：i : ι；E i；(i : ι) × E i。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.Sigma.dist_triangle`：∀ {ι : Type u_1} {E : ι → Type u_2} [inst : 
(i : ι) → MetricSpace (E i)] (x y z : (i : ι) × E i),   dist x z ≤ dist x y + di
st y z
· 使用定理 `Metric.Sigma.isOpen_iff`：∀ {ι : Type u_1} {E : ι → Type u_2} [inst : (i 
: ι) → MetricSpace (E i)] (s : Set ((i : ι) × E i)),   IsOpen s ↔ ∀ x ∈ s, ∃ ε >
 0, ∀ (y : (i…

--- 原说明 ---
A metric space structure on the disjoint union `Σ i, E i`.
We embed isometrically each factor, set the basepoints at distance 1, arbitraril
y,
and say that the distance from `a` to `b` is the sum of the distances of `a` and
 `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance b
y default.
-/
protected def metricSpace : MetricSpace (Σ i, E i) := by
  refine MetricSpace.ofDistTopology Sigma.dist ?_ ?_ Sigma.dist_triangle Sigma.isOpen_iff ?_
  · rintro ⟨i, x⟩
    simp [Sigma.dist]
  · rintro ⟨i, x⟩ ⟨j, y⟩
    rcases eq_or_ne i j with (rfl | h)
    · simp [Sigma.dist, dist_comm]
    · simp only [Sigma.dist, dist_comm, h, h.symm, not_false_iff, dif_neg]
      abel
  · rintro ⟨i, x⟩ ⟨j, y⟩
    rcases eq_or_ne i j with (rfl | hij)
    · simp [Sigma.dist]
    · intro h
      apply (lt_irrefl (1 : ℝ) _).elim
      calc
        1 ≤ Sigma.dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩ := Sigma.one_le_dist_of_ne hij _ _
        _ < 1 := by rw [h]; exact zero_lt_one

attribute [local instance] Sigma.metricSpace

open Topology

open Filter

/-- The injection of a space in a disjoint union is an isometry -/
/-
**Metric.Sigma.isometry_mk** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Sigma`。
形式化陈述：isometry_mk (i : ι) : Isometry (Sigma.mk i : E i -> Σ k, E k)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.Sigma.dist_same`：dist_same (i : ι) (x y : E i) : dist (Sigma.mk i
 x) ⟨i, y⟩ = dist x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The injection of a space in a disjoint union is an isometry
-/
theorem isometry_mk (i : ι) : Isometry (Sigma.mk i : E i → Σ k, E k) :=
  Isometry.of_dist_eq fun x y => by simp

/-- A disjoint union of complete metric spaces is complete. -/
/-
**Metric.Sigma.completeSpace** 是 Mathlib 中的一个定理，位于命名空间 `Metric.Sigma`。
形式化陈述：∀ {ι : Type u_1} {E : ι → Type u_2} [inst : (i : ι) → MetricSpace (E i)] [
∀ (i : ι), CompleteSpace (E i)],   CompleteSpace ((i : ι) × E i)
参数：i : ι；E i；i : ι；E i；(i : ι) × E i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `IsUniformInducing.isComplete_range`：IsUniformInducing.isComplete_range [
CompleteSpace α] (hf : IsUniformInducing f) : IsComplete (range f)
· 使用定理 `Isometry.isUniformInducing`：isUniformInducing (hf : Isometry f) : IsUnif
ormInducing f
· 使用定理 `Metric.Sigma.isometry_mk`：isometry_mk (i : ι) : Isometry (Sigma.mk i : E
 i -> Σ k, E k)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.Sigma.fst_eq_of_dist_lt_one`：fst_eq_of_dist_lt_one (x y : Σ i, E 
i) (h : dist x y < 1) : x.1 = y.1
· 使用定理 `completeSpace_of_isComplete_univ`：completeSpace_of_isComplete_univ (h : 
IsComplete (univ : Set α)) : CompleteSpace α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.iUnion_of_singleton`：iUnion_of_singleton (α : Type*) : (⋃ x, {x} : S
et α) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isComplete_iUnion_separated`：isComplete_iUnion_separated {ι : Sort*} {s 
: ι -> Set α} (hs : forall i, IsComplete (s i)) {U : SetRel α α} (hU : U in 𝓤 α)
 (hd : forall (i …
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
A disjoint union of complete metric spaces is complete.
-/
protected theorem completeSpace [∀ i, CompleteSpace (E i)] : CompleteSpace (Σ i, E i) := by
  set s : ι → Set (Σ i, E i) := fun i => Sigma.fst ⁻¹' {i}
  set U := { p : (Σ k, E k) × Σ k, E k | dist p.1 p.2 < 1 }
  have hc : ∀ i, IsComplete (s i) := fun i => by
    simp only [s, ← range_sigmaMk]
    exact (isometry_mk i).isUniformInducing.isComplete_range
  have hd : ∀ (i j), ∀ x ∈ s i, ∀ y ∈ s j, (x, y) ∈ U → i = j := fun i j x hx y hy hxy =>
    (Eq.symm hx).trans ((fst_eq_of_dist_lt_one _ _ hxy).trans hy)
  refine completeSpace_of_isComplete_univ ?_
  convert! isComplete_iUnion_separated hc (dist_mem_uniformity zero_lt_one) hd
  simp only [s, ← preimage_iUnion, iUnion_of_singleton, preimage_univ]

end Sigma

section Gluing

-- Exact gluing of two metric spaces along isometric subsets.
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [Nonempty Z] [MetricSpace Z] [MetricSpace X] [MetricSpace Y] {Φ : Z → X} {Ψ : Z → Y}
  {ε : ℝ}

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given two isometric embeddings `Φ : Z → X` and `Ψ : Z → Y`, we define a pseudometric space
/-
**Metric.on** 是 Mathlib 中的一个结构，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure on `X ⊕ Y` by declaring that `Φ x` and `Ψ x` are at distance `0`. -/
@[instance_reducible]
/-
**Metric.gluePremetric** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：gluePremetric (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : PseudoMetricSpace (X o
plus Y) where dist
参数：hΦ : Isometry Φ；hΨ : Isometry Ψ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two isometric embeddings `Φ : Z → X` and `Ψ : Z → Y`, we define a pseudome
tric space
structure on `X ⊕ Y` by declaring that `Φ x` and `Ψ x` are at distance `0`.
-/
def gluePremetric (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : PseudoMetricSpace (X ⊕ Y) where
  dist := glueDist Φ Ψ 0
  dist_self := glueDist_self Φ Ψ 0
  dist_comm := glueDist_comm Φ Ψ 0
  dist_triangle := glueDist_triangle Φ Ψ 0 fun p q => by rw [hΦ.dist_eq, hΨ.dist_eq]; simp

/-- Given two isometric embeddings `Φ : Z → X` and `Ψ : Z → Y`, we define a
space `GlueSpace hΦ hΨ` by identifying in `X ⊕ Y` the points `Φ x` and `Ψ x`. -/
/-
**Metric.GlueSpace** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：GlueSpace (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Type _
参数：hΦ : Isometry Φ；hΨ : Isometry Ψ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two isometric embeddings `Φ : Z → X` and `Ψ : Z → Y`, we define a
space `GlueSpace hΦ hΨ` by identifying in `X ⊕ Y` the points `Φ x` and `Ψ x`.
-/
def GlueSpace (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Type _ :=
  @SeparationQuotient _ (gluePremetric hΦ hΨ).toUniformSpace.toTopologicalSpace
/-
**Metric.** 是 Mathlib 中的一个实例，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : MetricSpace (GlueSpace hΦ hΨ) :=
  inferInstanceAs <| MetricSpace <|
    @SeparationQuotient _ (gluePremetric hΦ hΨ).toUniformSpace.toTopologicalSpace

/-- The canonical map from `X` to the space obtained by gluing isometric subsets in `X` and `Y`. -/
/-
**Metric.toGlueL** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：toGlueL (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (x : X) : GlueSpace hΦ hΨ
参数：hΦ : Isometry Φ；hΨ : Isometry Ψ；x : X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
The canonical map from `X` to the space obtained by gluing isometric subsets in 
`X` and `Y`.
-/
def toGlueL (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (x : X) : GlueSpace hΦ hΨ :=
  Quotient.mk'' (.inl x)

/-- The canonical map from `Y` to the space obtained by gluing isometric subsets in `X` and `Y`. -/
/-
**Metric.toGlueR** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：toGlueR (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (y : Y) : GlueSpace hΦ hΨ
参数：hΦ : Isometry Φ；hΨ : Isometry Ψ；y : Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
The canonical map from `Y` to the space obtained by gluing isometric subsets in 
`X` and `Y`.
-/
def toGlueR (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (y : Y) : GlueSpace hΦ hΨ :=
  Quotient.mk'' (.inr y)
/-
**Metric.inhabitedLeft** 是 Mathlib 中的一个实例，位于命名空间 `Metric`。
形式化陈述：inhabitedLeft (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited X] : Inhabite
d (GlueSpace hΦ hΨ)
参数：hΦ : Isometry Φ；hΨ : Isometry Ψ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedLeft (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited X] :
    Inhabited (GlueSpace hΦ hΨ) :=
  ⟨toGlueL _ _ default⟩
/-
**Metric.inhabitedRight** 是 Mathlib 中的一个实例，位于命名空间 `Metric`。
形式化陈述：inhabitedRight (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited Y] : Inhabit
ed (GlueSpace hΦ hΨ)
参数：hΦ : Isometry Φ；hΨ : Isometry Ψ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedRight (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited Y] :
    Inhabited (GlueSpace hΦ hΨ) :=
  ⟨toGlueR _ _ default⟩
/-
**Metric.toGlue_commute** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：toGlue_commute (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : toGlueL hΦ hΨ ∘ Φ = t
oGlueR hΦ hΨ ∘ Ψ
参数：hΦ : Isometry Φ；hΨ : Isometry Ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeparationQuotient.mk_eq_mk`：mk_eq_mk : mk x = mk y ↔ (x ~ᵢ y)
· 使用定理 `Metric.inseparable_iff`：Metric.inseparable_iff {x y : α} : Inseparable x
 y ↔ dist x y = 0
· 使用定理 `Metric.glueDist_glued_points`：glueDist_glued_points [Nonempty Z] (Φ : Z 
-> X) (Ψ : Z -> Y) (ε : Real) (p : Z) : glueDist Φ Ψ ε (.inl (Φ p)) (.inr (Ψ p))
 = ε
-/
theorem toGlue_commute (hΦ : Isometry Φ) (hΨ : Isometry Ψ) :
    toGlueL hΦ hΨ ∘ Φ = toGlueR hΦ hΨ ∘ Ψ := by
  let i : PseudoMetricSpace (X ⊕ Y) := gluePremetric hΦ hΨ
  let _ := i.toUniformSpace.toTopologicalSpace
  funext
  simp only [comp, toGlueL, toGlueR]
  refine SeparationQuotient.mk_eq_mk.2 (Metric.inseparable_iff.2 ?_)
  exact glueDist_glued_points Φ Ψ 0 _
/-
**Metric.toGlueL_isometry** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：toGlueL_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Isometry (toGlueL h
Φ hΨ)
参数：hΦ : Isometry Φ；hΨ : Isometry Ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
-/
theorem toGlueL_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Isometry (toGlueL hΦ hΨ) :=
  Isometry.of_dist_eq fun _ _ => rfl
/-
**Metric.toGlueR_isometry** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：toGlueR_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Isometry (toGlueR h
Φ hΨ)
参数：hΦ : Isometry Φ；hΨ : Isometry Ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
-/
theorem toGlueR_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Isometry (toGlueR hΦ hΨ) :=
  Isometry.of_dist_eq fun _ _ => rfl

end Gluing --section

section InductiveLimit

/-!
### Inductive limit of metric spaces

In this section, we define the inductive limit of

```
     f 0        f 1        f 2        f 3
X 0 -----> X 1 -----> X 2 -----> X 3 -----> ...
```

where the `X n` are metric spaces and f n isometric embeddings. We do it by defining a premetric
space structure on `Σ n, X n`, where the predistance `dist x y` is obtained by pushing `x` and `y`
in a common `X k` using composition by the `f n`, and taking the distance there. This does not
depend on the choice of `k` as the `f n` are isometries. The metric space associated to this
premetric space is the desired inductive limit.
-/

open Nat

variable {X : ℕ → Type u} [∀ n, MetricSpace (X n)] {f : ∀ n, X n → X (n + 1)}

/-- Predistance on the disjoint union `Σ n, X n`. -/
/-
**Metric.inductiveLimitDist** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：inductiveLimitDist (f : forall n, X n -> X (n + 1)) (x y : Σ n, X n) : Rea
l
参数：f : forall n, X n -> X (n + 1)；x y : Σ n, X n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predistance on the disjoint union `Σ n, X n`.
-/
def inductiveLimitDist (f : ∀ n, X n → X (n + 1)) (x y : Σ n, X n) : ℝ :=
  dist (leRecOn (le_max_left x.1 y.1) (f _) x.2 : X (max x.1 y.1))
    (leRecOn (le_max_right x.1 y.1) (f _) y.2 : X (max x.1 y.1))

/-- The predistance on the disjoint union `Σ n, X n` can be computed in any `X k` for large
enough `k`. -/
/-
**Metric.inductiveLimitDist_eq_dist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：inductiveLimitDist_eq_dist (I : forall n, Isometry (f n)) (x y : Σ n, X n)
 : forall m (hx : x.1 <= m) (hy : y.1 <= m), inductiveLimitDist f x y = dist (le
RecOn hx (f _) x.2 : X m) (leRecOn hy (f _) y.2 : X m) | 0, hx, hy => by obtain 
⟨i, x⟩
参数：I : forall n, Isometry (f n)；x y : Σ n, X n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predistance on the disjoint union `Σ n, X n` can be computed in any `X k` fo
r large
enough `k`.
-/
theorem inductiveLimitDist_eq_dist (I : ∀ n, Isometry (f n)) (x y : Σ n, X n) :
    ∀ m (hx : x.1 ≤ m) (hy : y.1 ≤ m), inductiveLimitDist f x y =
      dist (leRecOn hx (f _) x.2 : X m) (leRecOn hy (f _) y.2 : X m)
  | 0, hx, hy => by
    obtain ⟨i, x⟩ := x; obtain ⟨j, y⟩ := y
    obtain rfl : i = 0 := nonpos_iff_eq_zero.1 hx
    obtain rfl : j = 0 := nonpos_iff_eq_zero.1 hy
    rfl
  | (m + 1), hx, hy => by
    by_cases h : max x.1 y.1 = (m + 1)
    · generalize m + 1 = m' at *
      subst m'
      rfl
    · have : max x.1 y.1 ≤ succ m := by simp [hx, hy]
      have : max x.1 y.1 ≤ m := by simpa [h] using of_le_succ this
      have xm : x.1 ≤ m := le_trans (le_max_left _ _) this
      have ym : y.1 ≤ m := le_trans (le_max_right _ _) this
      rw [leRecOn_succ xm, leRecOn_succ ym, (I m).dist_eq]
      exact inductiveLimitDist_eq_dist I x y m xm ym

/-- Premetric space structure on `Σ n, X n`. -/
@[instance_reducible]
/-
**Metric.inductivePremetric** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：inductivePremetric (I : forall n, Isometry (f n)) : PseudoMetricSpace (Σ n
, X n) where dist
参数：I : forall n, Isometry (f n)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Premetric space structure on `Σ n, X n`.
-/
def inductivePremetric (I : ∀ n, Isometry (f n)) : PseudoMetricSpace (Σ n, X n) where
  dist := inductiveLimitDist f
  dist_self x := by simp [inductiveLimitDist]
  dist_comm x y := by
    let m := max x.1 y.1
    have hx : x.1 ≤ m := le_max_left _ _
    have hy : y.1 ≤ m := le_max_right _ _
    rw [inductiveLimitDist_eq_dist I x y m hx hy, inductiveLimitDist_eq_dist I y x m hy hx,
      dist_comm]
  dist_triangle x y z := by
    let m := max (max x.1 y.1) z.1
    have hx : x.1 ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
    have hy : y.1 ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
    have hz : z.1 ≤ m := le_max_right _ _
    calc
      inductiveLimitDist f x z = dist (leRecOn hx (f _) x.2 : X m) (leRecOn hz (f _) z.2 : X m) :=
        inductiveLimitDist_eq_dist I x z m hx hz
      _ ≤ dist (leRecOn hx (f _) x.2 : X m) (leRecOn hy (f _) y.2 : X m) +
            dist (leRecOn hy (f _) y.2 : X m) (leRecOn hz (f _) z.2 : X m) :=
        (dist_triangle _ _ _)
      _ = inductiveLimitDist f x y + inductiveLimitDist f y z := by
        rw [inductiveLimitDist_eq_dist I x y m hx hy, inductiveLimitDist_eq_dist I y z m hy hz]

/-- The type giving the inductive limit in a metric space context. -/
/-
**Metric.InductiveLimit** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：InductiveLimit (I : forall n, Isometry (f n)) : Type _
参数：I : forall n, Isometry (f n)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type giving the inductive limit in a metric space context.
-/
def InductiveLimit (I : ∀ n, Isometry (f n)) : Type _ :=
  @SeparationQuotient _ (inductivePremetric I).toUniformSpace.toTopologicalSpace
/-
**Metric.** 是 Mathlib 中的一个实例，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {I : ∀ (n : ℕ), Isometry (f n)} : MetricSpace (InductiveLimit (f := f) I) :=
  inferInstanceAs <| MetricSpace <|
    @SeparationQuotient _ (inductivePremetric I).toUniformSpace.toTopologicalSpace

/-- Mapping each `X n` to the inductive limit. -/
/-
**Metric.toInductiveLimit** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：toInductiveLimit (I : forall n, Isometry (f n)) (n : Nat) (x : X n) : Metr
ic.InductiveLimit I
参数：I : forall n, Isometry (f n)；n : Nat；x : X n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
Mapping each `X n` to the inductive limit.
-/
def toInductiveLimit (I : ∀ n, Isometry (f n)) (n : ℕ) (x : X n) : Metric.InductiveLimit I :=
  Quotient.mk'' (Sigma.mk n x)
/-
**Metric.** 是 Mathlib 中的一个实例，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : ∀ n, Isometry (f n)) [Inhabited (X 0)] : Inhabited (InductiveLimit I) :=
  ⟨toInductiveLimit _ 0 default⟩

/-- The map `toInductiveLimit n` mapping `X n` to the inductive limit is an isometry. -/
/-
**Metric.toInductiveLimit_isometry** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：toInductiveLimit_isometry (I : forall n, Isometry (f n)) (n : Nat) : Isome
try (toInductiveLimit I n)
参数：I : forall n, Isometry (f n)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.inductiveLimitDist_eq_dist`：inductiveLimitDist_eq_dist (I : foral
l n, Isometry (f n)) (x y : Σ n, X n) : forall m (hx : x.1 <= m) (hy : y.1 <= m)
, inductiveLimitDist f …
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用引理 `Nat.leRecOn_self`：leRecOn_self {C : Nat -> Sort*} {n} {next : forall {k}
, C k -> C (k + 1)} (x : C n) : (leRecOn n.le_refl next x : C n) = x

--- 原说明 ---
The map `toInductiveLimit n` mapping `X n` to the inductive limit is an isometry
.
-/
theorem toInductiveLimit_isometry (I : ∀ n, Isometry (f n)) (n : ℕ) :
    Isometry (toInductiveLimit I n) :=
  Isometry.of_dist_eq fun x y => by
    change inductiveLimitDist f ⟨n, x⟩ ⟨n, y⟩ = dist x y
    rw [inductiveLimitDist_eq_dist I ⟨n, x⟩ ⟨n, y⟩ n (le_refl n) (le_refl n), leRecOn_self,
      leRecOn_self]

/-- The maps `toInductiveLimit n` are compatible with the maps `f n`. -/
/-
**Metric.toInductiveLimit_commute** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：toInductiveLimit_commute (I : forall n, Isometry (f n)) (n : Nat) : toIndu
ctiveLimit I n.succ ∘ f n = toInductiveLimit I n
参数：I : forall n, Isometry (f n)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeparationQuotient.mk_eq_mk`：mk_eq_mk : mk x = mk y ↔ (x ~ᵢ y)
· 使用定理 `Metric.inseparable_iff`：Metric.inseparable_iff {x y : α} : Inseparable x
 y ↔ dist x y = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.inductiveLimitDist_eq_dist`：inductiveLimitDist_eq_dist (I : foral
l n, Isometry (f n)) (x y : Σ n, X n) : forall m (hx : x.1 <= m) (hy : y.1 <= m)
, inductiveLimitDist f …
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用引理 `Nat.leRecOn_self`：leRecOn_self {C : Nat -> Sort*} {n} {next : forall {k}
, C k -> C (k + 1)} (x : C n) : (leRecOn n.le_refl next x : C n) = x
· 使用引理 `Nat.leRecOn_succ`：leRecOn_succ {C : Nat -> Sort*} {n m} (h1 : n <= m) {h
2 : n <= m + 1} {next} (x : C n) : (leRecOn h2 next x : C (m + 1)) = next (leRec
On h1 …
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0

--- 原说明 ---
The maps `toInductiveLimit n` are compatible with the maps `f n`.
-/
theorem toInductiveLimit_commute (I : ∀ n, Isometry (f n)) (n : ℕ) :
    toInductiveLimit I n.succ ∘ f n = toInductiveLimit I n := by
  let h := inductivePremetric I
  let _ := h.toUniformSpace.toTopologicalSpace
  funext x
  simp only [comp, toInductiveLimit]
  refine SeparationQuotient.mk_eq_mk.2 (Metric.inseparable_iff.2 ?_)
  change inductiveLimitDist f ⟨n.succ, f n x⟩ ⟨n, x⟩ = 0
  rw [inductiveLimitDist_eq_dist I ⟨n.succ, f n x⟩ ⟨n, x⟩ n.succ, leRecOn_self,
    leRecOn_succ, leRecOn_self, dist_self]
  · rfl
  · rfl
  · exact le_succ _
/-
**Metric.dense_iUnion_range_toInductiveLimit** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：dense_iUnion_range_toInductiveLimit {X : Nat -> Type u} [(n : Nat) -> Metr
icSpace (X n)] {f : (n : Nat) -> X n -> X (n + 1)} (I : forall (n : Nat), Isomet
ry (f n)) : Dense (⋃ i, range (toInductiveLimit I i))
参数：n : Nat；X n；n : Nat；n + 1；I : forall (n : Nat), Isometry (f n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `dense_univ`：dense_univ : Dense (univ : Set X)
-/
theorem dense_iUnion_range_toInductiveLimit
    {X : ℕ → Type u} [(n : ℕ) → MetricSpace (X n)]
    {f : (n : ℕ) → X n → X (n + 1)}
    (I : ∀ (n : ℕ), Isometry (f n)) :
    Dense (⋃ i, range (toInductiveLimit I i)) := by
  refine dense_univ.mono ?_
  rintro ⟨n, x⟩ _
  refine mem_iUnion.2 ⟨n, mem_range.2 ⟨x, rfl⟩⟩
/-
**Metric.separableSpaceInductiveLimit_of_separableSpace** 是 Mathlib 中的一个定理，位于命名空
间 `Metric`。
形式化陈述：separableSpaceInductiveLimit_of_separableSpace {X : Nat -> Type u} [(n : N
at) -> MetricSpace (X n)] [hs : (n : Nat) -> TopologicalSpace.SeparableSpace (X 
n)] {f : (n : Nat) -> X n -> X (n + 1)} (I : forall (n : Nat), Isometry (f n)) :
 TopologicalSpace.SeparableSpace (Metric.InductiveLimit I)
参数：n : Nat；X n；n : Nat；X n；n : Nat；n + 1；I : forall (n : Nat), Isometry (f n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.countable_iUnion`：countable_iUnion {t : ι -> Set α} [Countable ι] (h
t : forall i, (t i).Countable) : (⋃ i, t i).Countable
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Dense.of_closure`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense (closure s) → Dense s
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `Continuous.range_subset_closure_image_dense`：Continuous.range_subset_clo
sure_image_dense {f : X -> Y} (hf : Continuous f) (hs : Dense s) : range f subse
teq closure (f '' s)
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `Metric.toInductiveLimit_isometry`：toInductiveLimit_isometry (I : forall 
n, Isometry (f n)) (n : Nat) : Isometry (toInductiveLimit I n)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Metric.dense_iUnion_range_toInductiveLimit`：dense_iUnion_range_toInducti
veLimit {X : Nat -> Type u} [(n : Nat) -> MetricSpace (X n)] {f : (n : Nat) -> X
 n -> X (n + 1)} (I : forall (n …
· 使用定理 `TopologicalSpace.exists_countable_dense`：exists_countable_dense [Separab
leSpace α] : exists s : Set α, s.Countable ∧ Dense s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem separableSpaceInductiveLimit_of_separableSpace
    {X : ℕ → Type u} [(n : ℕ) → MetricSpace (X n)]
    [hs : (n : ℕ) → TopologicalSpace.SeparableSpace (X n)] {f : (n : ℕ) → X n → X (n + 1)}
    (I : ∀ (n : ℕ), Isometry (f n)) :
    TopologicalSpace.SeparableSpace (Metric.InductiveLimit I) := by
  choose hsX hcX hdX using (fun n ↦ TopologicalSpace.exists_countable_dense (X n))
  let s := ⋃ (i : ℕ), (toInductiveLimit I i '' (hsX i))
  refine ⟨s, countable_iUnion (fun n => (hcX n).image _), ?_⟩
  refine .of_closure <| (dense_iUnion_range_toInductiveLimit I).mono <| iUnion_subset fun i ↦ ?_
  calc
    range (toInductiveLimit I i) ⊆ closure (toInductiveLimit I i '' (hsX i)) :=
      (toInductiveLimit_isometry I i |>.continuous).range_subset_closure_image_dense (hdX i)
    _ ⊆ closure s := closure_mono <| subset_iUnion (fun j ↦ toInductiveLimit I j '' hsX j) i

end InductiveLimit --section

end Metric --namespace

