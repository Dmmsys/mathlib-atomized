/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Data.ENNReal.Lemmas
public import Mathlib.Topology.Bornology.Constructions
public import Mathlib.Topology.EMetricSpace.Pi
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Product of pseudometric spaces

This file constructs the infinity distance on finite products of pseudometric spaces.
-/

@[expose] public section

open Bornology Filter Metric Set
open scoped NNReal Topology

variable {α β : Type*} [PseudoMetricSpace α]

open Finset

variable {X : β → Type*} [Fintype β] [∀ b, PseudoMetricSpace (X b)]

/-- A finite product of pseudometric spaces is a pseudometric space, with the sup distance. -/
/-
**pseudoMetricSpacePi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：pseudoMetricSpacePi : PseudoMetricSpace (forall b, X b)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite product of pseudometric spaces is a pseudometric space, with the sup di
stance.
-/
instance pseudoMetricSpacePi : PseudoMetricSpace (∀ b, X b) := by
  /- we construct the instance from the pseudoemetric space instance to avoid checking again that
    the uniformity is the same as the product uniformity, but we register nevertheless a nice
    formula for the distance -/
  let i := PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g : ∀ b, X b => ((sup univ fun b => nndist (f b) (g b) : ℝ≥0) : ℝ))
    (fun f g => NNReal.zero_le_coe)
    (fun f g => by simp [edist_pi_def])
  refine i.replaceBornology fun s => ?_
  simp only [isBounded_iff_eventually, ← forall_isBounded_image_eval_iff,
    forall_mem_image, ← Filter.eventually_all, @dist_nndist (X _)]
  refine eventually_congr ((eventually_ge_atTop 0).mono fun C hC ↦ ?_)
  lift C to ℝ≥0 using hC
  refine ⟨fun H x hx y hy ↦ NNReal.coe_le_coe.2 <| Finset.sup_le fun b _ ↦ H b hx hy,
    fun H b x hx y hy ↦ NNReal.coe_le_coe.2 ?_⟩
  exact Finset.sup_le_iff.1 (NNReal.coe_le_coe.1 <| H hx hy) b (Finset.mem_univ b)
/-
**nndist_pi_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nndist_pi_def (f g : forall b, X b) : nndist f g = sup univ fun b => nndis
t (f b) (g b)
参数：f g : forall b, X b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nndist_pi_def (f g : ∀ b, X b) : nndist f g = sup univ fun b => nndist (f b) (g b) := rfl
/-
**dist_pi_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_pi_def (f g : forall b, X b) : dist f g = (sup univ fun b => nndist (
f b) (g b) : Real>=0)
参数：f g : forall b, X b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dist_pi_def (f g : ∀ b, X b) : dist f g = (sup univ fun b => nndist (f b) (g b) : ℝ≥0) := rfl
/-
**nndist_pi_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nndist_pi_le_iff {f g : forall b, X b} {r : Real>=0} : nndist f g <= r ↔ f
orall b, nndist (f b) (g b) <= r
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nndist_pi_le_iff {f g : ∀ b, X b} {r : ℝ≥0} :
    nndist f g ≤ r ↔ ∀ b, nndist (f b) (g b) ≤ r := by simp [nndist_pi_def]
/-
**nndist_pi_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nndist_pi_lt_iff {f g : forall b, X b} {r : Real>=0} (hr : 0 < r) : nndist
 f g < r ↔ forall b, nndist (f b) (g b) < r
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nndist_pi_lt_iff {f g : ∀ b, X b} {r : ℝ≥0} (hr : 0 < r) :
    nndist f g < r ↔ ∀ b, nndist (f b) (g b) < r := by
  simp [nndist_pi_def, Finset.sup_lt_iff hr]
/-
**nndist_pi_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nndist_pi_eq_iff {f g : forall b, X b} {r : Real>=0} (hr : 0 < r) : nndist
 f g = r ↔ (exists i, nndist (f i) (g i) = r) ∧ forall b, nndist (f b) (g b) <= 
r
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_iff_le_not_lt`：eq_iff_le_not_lt : a = b ↔ a <= b ∧ ¬a < b
· 使用引理 `nndist_pi_lt_iff`：nndist_pi_lt_iff {f g : forall b, X b} {r : Real>=0} (
hr : 0 < r) : nndist f g < r ↔ forall b, nndist (f b) (g b) < r
· 使用引理 `nndist_pi_le_iff`：nndist_pi_le_iff {f g : forall b, X b} {r : Real>=0} :
 nndist f g <= r ↔ forall b, nndist (f b) (g b) <= r
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
-/
lemma nndist_pi_eq_iff {f g : ∀ b, X b} {r : ℝ≥0} (hr : 0 < r) :
    nndist f g = r ↔ (∃ i, nndist (f i) (g i) = r) ∧ ∀ b, nndist (f b) (g b) ≤ r := by
  rw [eq_iff_le_not_lt, nndist_pi_lt_iff hr, nndist_pi_le_iff, not_forall, and_comm]
  simp_rw [not_lt, and_congr_left_iff, le_antisymm_iff]
  intro h
  refine exists_congr fun b => ?_
  apply (and_iff_right <| h _).symm
/-
**dist_pi_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_pi_lt_iff {f g : forall b, X b} {r : Real} (hr : 0 < r) : dist f g < 
r ↔ forall b, dist (f b) (g b) < r
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `nndist_pi_lt_iff`：nndist_pi_lt_iff {f g : forall b, X b} {r : Real>=0} (
hr : 0 < r) : nndist f g < r ↔ forall b, nndist (f b) (g b) < r
-/
lemma dist_pi_lt_iff {f g : ∀ b, X b} {r : ℝ} (hr : 0 < r) :
    dist f g < r ↔ ∀ b, dist (f b) (g b) < r := by
  lift r to ℝ≥0 using hr.le
  exact nndist_pi_lt_iff hr
/-
**dist_pi_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_pi_le_iff {f g : forall b, X b} {r : Real} (hr : 0 <= r) : dist f g <
= r ↔ forall b, dist (f b) (g b) <= r
参数：hr : 0 <= r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `nndist_pi_le_iff`：nndist_pi_le_iff {f g : forall b, X b} {r : Real>=0} :
 nndist f g <= r ↔ forall b, nndist (f b) (g b) <= r
-/
lemma dist_pi_le_iff {f g : ∀ b, X b} {r : ℝ} (hr : 0 ≤ r) :
    dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r := by
  lift r to ℝ≥0 using hr
  exact nndist_pi_le_iff
/-
**dist_pi_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_pi_eq_iff {f g : forall b, X b} {r : Real} (hr : 0 < r) : dist f g = 
r ↔ (exists i, dist (f i) (g i) = r) ∧ forall b, dist (f b) (g b) <= r
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `nndist_pi_eq_iff`：nndist_pi_eq_iff {f g : forall b, X b} {r : Real>=0} (
hr : 0 < r) : nndist f g = r ↔ (exists i, nndist (f i) (g i) = r) ∧ forall b, nn
dist (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dist_pi_eq_iff {f g : ∀ b, X b} {r : ℝ} (hr : 0 < r) :
    dist f g = r ↔ (∃ i, dist (f i) (g i) = r) ∧ ∀ b, dist (f b) (g b) ≤ r := by
  lift r to ℝ≥0 using hr.le
  simp_rw [← coe_nndist, NNReal.coe_inj, nndist_pi_eq_iff hr, NNReal.coe_le_coe]
/-
**dist_pi_le_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_pi_le_iff' [Nonempty β] {f g : forall b, X b} {r : Real} : dist f g <
= r ↔ forall b, dist (f b) (g b) <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `dist_pi_le_iff`：dist_pi_le_iff {f g : forall b, X b} {r : Real} (hr : 0 
<= r) : dist f g <= r ↔ forall b, dist (f b) (g b) <= r
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
lemma dist_pi_le_iff' [Nonempty β] {f g : ∀ b, X b} {r : ℝ} :
    dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r := by
  by_cases hr : 0 ≤ r
  · exact dist_pi_le_iff hr
  · exact iff_of_false (fun h => hr <| dist_nonneg.trans h) fun h =>
      hr <| dist_nonneg.trans <| h <| Classical.arbitrary _
/-
**dist_pi_const_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_pi_const_le (a b : α) : (dist (fun _ : β => a) fun _ => b) <= dist a 
b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `dist_pi_le_iff`：dist_pi_le_iff {f g : forall b, X b} {r : Real} (hr : 0 
<= r) : dist f g <= r ↔ forall b, dist (f b) (g b) <= r
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma dist_pi_const_le (a b : α) : (dist (fun _ : β => a) fun _ => b) ≤ dist a b :=
  (dist_pi_le_iff dist_nonneg).2 fun _ => le_rfl
/-
**nndist_pi_const_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nndist_pi_const_le (a b : α) : (nndist (fun _ : β => a) fun _ => b) <= nnd
ist a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `nndist_pi_le_iff`：nndist_pi_le_iff {f g : forall b, X b} {r : Real>=0} :
 nndist f g <= r ↔ forall b, nndist (f b) (g b) <= r
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma nndist_pi_const_le (a b : α) : (nndist (fun _ : β => a) fun _ => b) ≤ nndist a b :=
  nndist_pi_le_iff.2 fun _ => le_rfl

@[simp]
/-
**dist_pi_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_pi_const [Nonempty β] (a b : α) : (dist (fun _ : β => a) fun _ => b) 
= dist a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `edist_pi_const`：edist_pi_const [Nonempty β] (a b : α) : (edist (fun _ : 
β => a) fun _ => b) = edist a b
-/
lemma dist_pi_const [Nonempty β] (a b : α) : (dist (fun _ : β => a) fun _ => b) = dist a b := by
  simpa only [dist_edist] using congr_arg ENNReal.toReal (edist_pi_const a b)

@[simp]
/-
**nndist_pi_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nndist_pi_const [Nonempty β] (a b : α) : (nndist (fun _ : β => a) fun _ =>
 b) = nndist a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `dist_pi_const`：dist_pi_const [Nonempty β] (a b : α) : (dist (fun _ : β =
> a) fun _ => b) = dist a b
-/
lemma nndist_pi_const [Nonempty β] (a b : α) : (nndist (fun _ : β => a) fun _ => b) = nndist a b :=
  NNReal.eq <| dist_pi_const a b
/-
**nndist_le_pi_nndist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nndist_le_pi_nndist (f g : forall b, X b) (b : β) : nndist (f b) (g b) <= 
nndist f g
参数：f g : forall b, X b；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `edist_le_pi_edist`：edist_le_pi_edist [forall b, EDist (X b)] (f g : fora
ll b, X b) (b : β) : edist (f b) (g b) <= edist f g
-/
lemma nndist_le_pi_nndist (f g : ∀ b, X b) (b : β) : nndist (f b) (g b) ≤ nndist f g := by
  rw [← ENNReal.coe_le_coe, ← edist_nndist, ← edist_nndist]
  exact edist_le_pi_edist f g b
/-
**dist_le_pi_dist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_le_pi_dist (f g : forall b, X b) (b : β) : dist (f b) (g b) <= dist f
 g
参数：f g : forall b, X b；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `nndist_le_pi_nndist`：nndist_le_pi_nndist (f g : forall b, X b) (b : β) :
 nndist (f b) (g b) <= nndist f g
-/
lemma dist_le_pi_dist (f g : ∀ b, X b) (b : β) : dist (f b) (g b) ≤ dist f g := by
  simp only [dist_nndist, NNReal.coe_le_coe, nndist_le_pi_nndist f g b]

/-- An open ball in a product space is a product of open balls. See also `ball_pi'`
for a version assuming `Nonempty β` instead of `0 < r`. -/
/-
**ball_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ball_pi (x : forall b, X b) {r : Real} (hr : 0 < r) : ball x r = Set.pi un
iv fun b => ball (x b) r
参数：x : forall b, X b；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `dist_pi_lt_iff`：dist_pi_lt_iff {f g : forall b, X b} {r : Real} (hr : 0 
< r) : dist f g < r ↔ forall b, dist (f b) (g b) < r
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An open ball in a product space is a product of open balls. See also `ball_pi'`
for a version assuming `Nonempty β` instead of `0 < r`.
-/
lemma ball_pi (x : ∀ b, X b) {r : ℝ} (hr : 0 < r) :
    ball x r = Set.pi univ fun b => ball (x b) r := by
  ext p
  simp [dist_pi_lt_iff hr]

/-- An open ball in a product space is a product of open balls. See also `ball_pi`
for a version assuming `0 < r` instead of `Nonempty β`. -/
/-
**ball_pi'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ball_pi' [Nonempty β] (x : forall b, X b) (r : Real) : ball x r = Set.pi u
niv fun b => ball (x b) r
参数：x : forall b, X b；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用引理 `ball_pi`：ball_pi (x : forall b, X b) {r : Real} (hr : 0 < r) : ball x r 
= Set.pi univ fun b => ball (x b) r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.ball_eq_empty`：ball_eq_empty : ball x ε = ∅ ↔ ε <= 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.univ_pi_empty`：univ_pi_empty [h : Nonempty ι] : pi univ (fun _ => ∅ 
: forall i, Set (α i)) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An open ball in a product space is a product of open balls. See also `ball_pi`
for a version assuming `0 < r` instead of `Nonempty β`.
-/
lemma ball_pi' [Nonempty β] (x : ∀ b, X b) (r : ℝ) :
    ball x r = Set.pi univ fun b => ball (x b) r :=
  (lt_or_ge 0 r).elim (ball_pi x) fun hr => by simp [ball_eq_empty.2 hr]

/-- A closed ball in a product space is a product of closed balls. See also `closedBall_pi'`
for a version assuming `Nonempty β` instead of `0 ≤ r`. -/
/-
**closedBall_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：closedBall_pi (x : forall b, X b) {r : Real} (hr : 0 <= r) : closedBall x 
r = Set.pi univ fun b => closedBall (x b) r
参数：x : forall b, X b；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `dist_pi_le_iff`：dist_pi_le_iff {f g : forall b, X b} {r : Real} (hr : 0 
<= r) : dist f g <= r ↔ forall b, dist (f b) (g b) <= r
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A closed ball in a product space is a product of closed balls. See also `closedB
all_pi'`
for a version assuming `Nonempty β` instead of `0 ≤ r`.
-/
lemma closedBall_pi (x : ∀ b, X b) {r : ℝ} (hr : 0 ≤ r) :
    closedBall x r = Set.pi univ fun b => closedBall (x b) r := by
  ext p
  simp [dist_pi_le_iff hr]

/-- A closed ball in a product space is a product of closed balls. See also `closedBall_pi`
for a version assuming `0 ≤ r` instead of `Nonempty β`. -/
/-
**closedBall_pi'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：closedBall_pi' [Nonempty β] (x : forall b, X b) (r : Real) : closedBall x 
r = Set.pi univ fun b => closedBall (x b) r
参数：x : forall b, X b；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用引理 `closedBall_pi`：closedBall_pi (x : forall b, X b) {r : Real} (hr : 0 <= r
) : closedBall x r = Set.pi univ fun b => closedBall (x b) r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.closedBall_eq_empty`：closedBall_eq_empty : closedBall x ε = ∅ ↔ ε
 < 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.univ_pi_empty`：univ_pi_empty [h : Nonempty ι] : pi univ (fun _ => ∅ 
: forall i, Set (α i)) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A closed ball in a product space is a product of closed balls. See also `closedB
all_pi`
for a version assuming `0 ≤ r` instead of `Nonempty β`.
-/
lemma closedBall_pi' [Nonempty β] (x : ∀ b, X b) (r : ℝ) :
    closedBall x r = Set.pi univ fun b => closedBall (x b) r :=
  (le_or_gt 0 r).elim (closedBall_pi x) fun hr => by simp [closedBall_eq_empty.2 hr]

/-- A sphere in a product space is a union of spheres on each component restricted to the closed
ball. -/
/-
**sphere_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sphere_pi (x : forall b, X b) {r : Real} (h : 0 < r ∨ Nonempty β) : sphere
 x r = (⋃ i : β, Function.eval i ⁻¹' sphere (x i) r) inter closedBall x r
参数：x : forall b, X b；h : 0 < r ∨ Nonempty β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.sphere_eq_empty_of_neg`：sphere_eq_empty_of_neg (hε : ε < 0) : sph
ere x ε = ∅
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Metric.closedBall_of_neg`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x
 : α} {ε : ℝ}, ε < 0 → Metric.closedBall x ε = ∅
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Metric.closedBall_eq_sphere_of_nonpos`：closedBall_eq_sphere_of_nonpos (h
ε : ε <= 0) : closedBall x ε = sphere x ε
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Set.subset_iUnion_of_subset`：subset_iUnion_of_subset {s : Set α} {t : ι 
-> Set α} (i : ι) (h : s subseteq t i) : s subseteq ⋃ i, t i
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `dist_pi_le_iff`：dist_pi_le_iff {f g : forall b, X b} {r : Real} (hr : 0 
<= r) : dist f g <= r ↔ forall b, dist (f b) (g b) <= r
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `dist_pi_eq_iff`：dist_pi_eq_iff {f g : forall b, X b} {r : Real} (hr : 0 
< r) : dist f g = r ↔ (exists i, dist (f i) (g i) = r) ∧ forall b, dist (f b) (g
 b) …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A sphere in a product space is a union of spheres on each component restricted t
o the closed
ball.
-/
lemma sphere_pi (x : ∀ b, X b) {r : ℝ} (h : 0 < r ∨ Nonempty β) :
    sphere x r = (⋃ i : β, Function.eval i ⁻¹' sphere (x i) r) ∩ closedBall x r := by
  obtain hr | rfl | hr := lt_trichotomy r 0
  · simp [hr]
  · rw [closedBall_eq_sphere_of_nonpos le_rfl, eq_comm, Set.inter_eq_right]
    let := h.resolve_left (lt_irrefl _)
    inhabit β
    refine subset_iUnion_of_subset default ?_
    intro x hx
    replace hx := hx.le
    rw [dist_pi_le_iff le_rfl] at hx
    exact le_antisymm (hx default) dist_nonneg
  · ext
    simp [dist_pi_eq_iff hr, dist_pi_le_iff hr.le]

@[simp]
/-
**Fin.nndist_insertNth_insertNth** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fin.nndist_insertNth_insertNth {n : Nat} {α : Fin (n + 1) -> Type*} [foral
l i, PseudoMetricSpace (α i)] (i : Fin (n + 1)) (x y : α i) (f g : forall j, α (
i.succAbove j)) : nndist (i.insertNth x f) (i.insertNth y g) = max (nndist x y) 
(nndist f g)
参数：n + 1；α i；i : Fin (n + 1)；x y : α i；f g : forall j, α (i.succAbove j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.forall_iff_succAbove`：forall_iff_succAbove {P : Fin (n + 1) -> Prop}
 (p : Fin (n + 1)) : (forall i, P i) ↔ P p ∧ forall i, P (p.succAbove i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Fin.nndist_insertNth_insertNth {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, PseudoMetricSpace (α i)] (i : Fin (n + 1)) (x y : α i) (f g : ∀ j, α (i.succAbove j)) :
    nndist (i.insertNth x f) (i.insertNth y g) = max (nndist x y) (nndist f g) :=
  eq_of_forall_ge_iff fun c => by simp [nndist_pi_le_iff, i.forall_iff_succAbove]

@[simp]
/-
**Fin.dist_insertNth_insertNth** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fin.dist_insertNth_insertNth {n : Nat} {α : Fin (n + 1) -> Type*} [forall 
i, PseudoMetricSpace (α i)] (i : Fin (n + 1)) (x y : α i) (f g : forall j, α (i.
succAbove j)) : dist (i.insertNth x f) (i.insertNth y g) = max (dist x y) (dist 
f g)
参数：n + 1；α i；i : Fin (n + 1)；x y : α i；f g : forall j, α (i.succAbove j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.nndist_insertNth_insertNth`：Fin.nndist_insertNth_insertNth {n : Nat}
 {α : Fin (n + 1) -> Type*} [forall i, PseudoMetricSpace (α i)] (i : Fin (n + 1)
) (x y : α i) (f g :…
· 使用定理 `NNReal.coe_max`：coe_max (x y : Real>=0) : ((max x y : Real>=0) : Real) =
 max (x : Real) (y : Real)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Fin.dist_insertNth_insertNth {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, PseudoMetricSpace (α i)] (i : Fin (n + 1)) (x y : α i) (f g : ∀ j, α (i.succAbove j)) :
    dist (i.insertNth x f) (i.insertNth y g) = max (dist x y) (dist f g) := by
  simp only [dist_nndist, Fin.nndist_insertNth_insertNth, NNReal.coe_max]

/-- The (sup metric) nonnegative distance between `Pi.single i a` and `Pi.single j b` for
`i ≠ j` is `max (nndist a 0) (nndist b 0)`. -/
/-
**nndist_single_single** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nndist_single_single {Y : Type*} [PseudoMetricSpace Y] [Zero Y] [Decidable
Eq β] (i j : β) (a b : Y) (h : i != j) : nndist (Pi.single i a : β -> Y) (Pi.sin
gle j b) = max (nndist a 0) (nndist b 0)
参数：i j : β；a b : Y；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `nndist_pi_le_iff`：nndist_pi_le_iff {f g : forall b, X b} {r : Real>=0} :
 nndist f g <= r ↔ forall b, nndist (f b) (g b) <= r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `nndist_comm`：nndist_comm (x y : α) : nndist x y = nndist y x
· 使用定理 `nndist_self`：∀ {α : Type u} [inst : PseudoMetricSpace α] (a : α), nndist
 a a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `nndist_le_pi_nndist`：nndist_le_pi_nndist (f g : forall b, X b) (b : β) :
 nndist (f b) (g b) <= nndist f g
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…

--- 原说明 ---
The (sup metric) nonnegative distance between `Pi.single i a` and `Pi.single j b
` for
`i ≠ j` is `max (nndist a 0) (nndist b 0)`.
-/
lemma nndist_single_single {Y : Type*} [PseudoMetricSpace Y] [Zero Y] [DecidableEq β]
    (i j : β) (a b : Y) (h : i ≠ j) :
    nndist (Pi.single i a : β → Y) (Pi.single j b) = max (nndist a 0) (nndist b 0) := by
  refine le_antisymm (nndist_pi_le_iff.2 fun k ↦ ?_) (max_le ?_ ?_)
  · simp only [Pi.single_apply]
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all [nndist_comm]
  · simpa [h] using nndist_le_pi_nndist (Pi.single i a : β → Y) (Pi.single j b) i
  · simpa [h, nndist_comm] using nndist_le_pi_nndist (Pi.single i a : β → Y) (Pi.single j b) j

/-- The (sup metric) distance between `Pi.single i a` and `Pi.single j b` for
`i ≠ j` is `max (dist a 0) (dist b 0)`. -/
/-
**dist_single_single** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_single_single {Y : Type*} [PseudoMetricSpace Y] [Zero Y] [DecidableEq
 β] (i j : β) (a b : Y) (h : i != j) : dist (Pi.single i a : β -> Y) (Pi.single 
j b) = max (dist a 0) (dist b 0)
参数：i j : β；a b : Y；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nndist_single_single`：nndist_single_single {Y : Type*} [PseudoMetricSpac
e Y] [Zero Y] [DecidableEq β] (i j : β) (a b : Y) (h : i != j) : nndist (Pi.sing
le i a : β…
· 使用定理 `NNReal.coe_max`：coe_max (x y : Real>=0) : ((max x y : Real>=0) : Real) =
 max (x : Real) (y : Real)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The (sup metric) distance between `Pi.single i a` and `Pi.single j b` for
`i ≠ j` is `max (dist a 0) (dist b 0)`.
-/
lemma dist_single_single {Y : Type*} [PseudoMetricSpace Y] [Zero Y] [DecidableEq β]
    (i j : β) (a b : Y) (h : i ≠ j) :
    dist (Pi.single i a : β → Y) (Pi.single j b) = max (dist a 0) (dist b 0) := by
  simp only [dist_nndist, nndist_single_single i j a b h, NNReal.coe_max]
