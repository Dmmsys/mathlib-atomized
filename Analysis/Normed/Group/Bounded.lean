/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Order.Filter.Pointwise

/-!
# Boundedness in normed groups

This file rephrases metric boundedness in terms of norms.

## Tags

normed group
-/

public section

open Filter Metric Bornology
open scoped Pointwise Topology

variable {α E F G : Type*}

section SeminormedGroup
variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E}

@[to_additive (attr := simp) comap_norm_atTop]
/-
**comap_norm_atTop'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：comap_norm_atTop' : comap norm atTop = cobounded E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_one_right`：dist_one_right (a : E) : dist a 1 = ‖a‖
· 使用定理 `Metric.comap_dist_right_atTop`：comap_dist_right_atTop (c : α) : comap (d
ist · c) atTop = cobounded α
-/
lemma comap_norm_atTop' : comap norm atTop = cobounded E := by
  simpa only [dist_one_right] using comap_dist_right_atTop (1 : E)

@[to_additive Filter.HasBasis.cobounded_of_norm]
/-
**Filter.HasBasis.cobounded_of_norm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.cobounded_of_norm' {ι : Sort*} {p : ι -> Prop} {s : ι -> S
et Real} (h : HasBasis atTop p s) : HasBasis (cobounded E) p fun i => norm ⁻¹' s
 i
参数：h : HasBasis atTop p s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用引理 `comap_norm_atTop'`：comap_norm_atTop' : comap norm atTop = cobounded E
-/
lemma Filter.HasBasis.cobounded_of_norm' {ι : Sort*} {p : ι → Prop} {s : ι → Set ℝ}
    (h : HasBasis atTop p s) : HasBasis (cobounded E) p fun i ↦ norm ⁻¹' s i :=
  comap_norm_atTop' (E := E) ▸ h.comap _

@[to_additive Filter.hasBasis_cobounded_norm]
/-
**Filter.hasBasis_cobounded_norm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.hasBasis_cobounded_norm' : HasBasis (cobounded E) (fun _ => True) (
{x | · <= ‖x‖})
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.HasBasis.cobounded_of_norm'`：Filter.HasBasis.cobounded_of_norm' {
ι : Sort*} {p : ι -> Prop} {s : ι -> Set Real} (h : HasBasis atTop p s) : HasBas
is (cobounded E) p fun i…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma Filter.hasBasis_cobounded_norm' : HasBasis (cobounded E) (fun _ ↦ True) ({x | · ≤ ‖x‖}) :=
  atTop_basis.cobounded_of_norm'

@[to_additive (attr := simp) tendsto_norm_atTop_iff_cobounded]
/-
**tendsto_norm_atTop_iff_cobounded'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_norm_atTop_iff_cobounded' {f : α -> E} {l : Filter α} : Tendsto (‖
f ·‖) l atTop ↔ Tendsto f l (cobounded E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `comap_norm_atTop'`：comap_norm_atTop' : comap norm atTop = cobounded E
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma tendsto_norm_atTop_iff_cobounded' {f : α → E} {l : Filter α} :
    Tendsto (‖f ·‖) l atTop ↔ Tendsto f l (cobounded E) := by
  rw [← comap_norm_atTop', tendsto_comap_iff]; rfl

@[to_additive tendsto_norm_cobounded_atTop]
/-
**tendsto_norm_cobounded_atTop'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_norm_cobounded_atTop' : Tendsto norm (cobounded E) atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `tendsto_norm_atTop_iff_cobounded'`：tendsto_norm_atTop_iff_cobounded' {f 
: α -> E} {l : Filter α} : Tendsto (‖f ·‖) l atTop ↔ Tendsto f l (cobounded E)
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
lemma tendsto_norm_cobounded_atTop' : Tendsto norm (cobounded E) atTop :=
  tendsto_norm_atTop_iff_cobounded'.2 tendsto_id

@[to_additive eventually_cobounded_le_norm]
/-
**eventually_cobounded_le_norm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventually_cobounded_le_norm' (a : Real) : forallᶠ x in cobounded E, a <= 
‖x‖
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually_ge_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用引理 `tendsto_norm_cobounded_atTop'`：tendsto_norm_cobounded_atTop' : Tendsto n
orm (cobounded E) atTop
-/
lemma eventually_cobounded_le_norm' (a : ℝ) : ∀ᶠ x in cobounded E, a ≤ ‖x‖ :=
  tendsto_norm_cobounded_atTop'.eventually_ge_atTop a

@[to_additive tendsto_norm_cocompact_atTop]
/-
**tendsto_norm_cocompact_atTop'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_norm_cocompact_atTop' [ProperSpace E] : Tendsto norm (cocompact E)
 atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `tendsto_norm_cobounded_atTop'`：tendsto_norm_cobounded_atTop' : Tendsto n
orm (cobounded E) atTop
· 使用定理 `Metric.cobounded_eq_cocompact`：Metric.cobounded_eq_cocompact [ProperSpac
e α] : cobounded α = cocompact α
-/
lemma tendsto_norm_cocompact_atTop' [ProperSpace E] : Tendsto norm (cocompact E) atTop :=
  cobounded_eq_cocompact (α := E) ▸ tendsto_norm_cobounded_atTop'

@[to_additive (attr := simp)]
/-
**Filter.inv_cobounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.inv_cobounded : (cobounded E)⁻¹ = cobounded E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Filter.inv_cobounded : (cobounded E)⁻¹ = cobounded E := by
  simp only [← comap_norm_atTop', ← Filter.comap_inv, comap_comap, Function.comp_def, norm_inv']

/-- In a (semi)normed group, inversion `x ↦ x⁻¹` tends to infinity at infinity. -/
@[to_additive /-- In a (semi)normed group, negation `x ↦ -x` tends to infinity at infinity. -/]
/-
**Filter.tendsto_inv_cobounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.tendsto_inv_cobounded : Tendsto Inv.inv (cobounded E) (cobounded E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Filter.inv_cobounded`：Filter.inv_cobounded : (cobounded E)⁻¹ = cobounded
 E

--- 原说明 ---
In a (semi)normed group, inversion `x ↦ x⁻¹` tends to infinity at infinity.
-/
theorem Filter.tendsto_inv_cobounded : Tendsto Inv.inv (cobounded E) (cobounded E) :=
  inv_cobounded.le

@[to_additive isBounded_iff_forall_norm_le]
/-
**isBounded_iff_forall_norm_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isBounded_iff_forall_norm_le' : Bornology.IsBounded s ↔ exists C, forall x
 in s, ‖x‖ <= C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Metric.isBounded_iff_subset_closedBall`：isBounded_iff_subset_closedBall 
(c : α) : IsBounded s ↔ exists r, s subseteq closedBall c r
-/
lemma isBounded_iff_forall_norm_le' : Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C := by
  simpa only [Set.subset_def, mem_closedBall_one_iff] using isBounded_iff_subset_closedBall (1 : E)

alias ⟨Bornology.IsBounded.exists_norm_le', _⟩ := isBounded_iff_forall_norm_le'

alias ⟨Bornology.IsBounded.exists_norm_le, _⟩ := isBounded_iff_forall_norm_le

attribute [to_additive existing exists_norm_le] Bornology.IsBounded.exists_norm_le'

@[to_additive exists_pos_norm_le]
/-
**Bornology.IsBounded.exists_pos_norm_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Bornology.IsBounded.exists_pos_norm_le' (hs : IsBounded s) : exists R > 0,
 forall x in s, ‖x‖ <= R
参数：hs : IsBounded s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.exists_norm_le'`：∀ {E : Type u_2} [inst : Seminormed
Group E] {s : Set E}, Bornology.IsBounded s → ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
lemma Bornology.IsBounded.exists_pos_norm_le' (hs : IsBounded s) : ∃ R > 0, ∀ x ∈ s, ‖x‖ ≤ R :=
  let ⟨R₀, hR₀⟩ := hs.exists_norm_le'
  ⟨max R₀ 1, by positivity, fun x hx => (hR₀ x hx).trans <| le_max_left _ _⟩

@[to_additive Bornology.IsBounded.exists_pos_norm_lt]
/-
**Bornology.IsBounded.exists_pos_norm_lt'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Bornology.IsBounded.exists_pos_norm_lt' (hs : IsBounded s) : exists R > 0,
 forall x in s, ‖x‖ < R
参数：hs : IsBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Bornology.IsBounded.exists_pos_norm_le'`：Bornology.IsBounded.exists_pos_
norm_le' (hs : IsBounded s) : exists R > 0, forall x in s, ‖x‖ <= R
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
-/
lemma Bornology.IsBounded.exists_pos_norm_lt' (hs : IsBounded s) : ∃ R > 0, ∀ x ∈ s, ‖x‖ < R :=
  let ⟨R, hR₀, hR⟩ := hs.exists_pos_norm_le'
  ⟨R + 1, by positivity, fun x hx ↦ (hR x hx).trans_lt (lt_add_one _)⟩

@[to_additive]
/-
**NormedCommGroup.cauchySeq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NormedCommGroup.cauchySeq_iff [Nonempty α] [SemilatticeSup α] {u : α -> E}
 : CauchySeq u ↔ forall ε > 0, exists N, forall m, N <= m -> forall n, N <= n ->
 ‖(u m)⁻¹ * u n‖ < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm_inv_mul`：dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ *
 b‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma NormedCommGroup.cauchySeq_iff [Nonempty α] [SemilatticeSup α] {u : α → E} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → ‖(u m)⁻¹ * u n‖ < ε := by
  simp [Metric.cauchySeq_iff, dist_eq_norm_inv_mul]

@[to_additive IsCompact.exists_bound_of_continuousOn]
/-
**IsCompact.exists_bound_of_continuousOn'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.exists_bound_of_continuousOn' [TopologicalSpace α] {s : Set α} (
hs : IsCompact s) {f : α -> E} (hf : ContinuousOn f s) : exists C, forall x in s
, ‖f x‖ <= C
参数：hs : IsCompact s；hf : ContinuousOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isBounded_iff_forall_norm_le'`：isBounded_iff_forall_norm_le' : Bornology
.IsBounded s ↔ exists C, forall x in s, ‖x‖ <= C
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
-/
lemma IsCompact.exists_bound_of_continuousOn' [TopologicalSpace α] {s : Set α} (hs : IsCompact s)
    {f : α → E} (hf : ContinuousOn f s) : ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C :=
  (isBounded_iff_forall_norm_le'.1 (hs.image_of_continuousOn hf).isBounded).imp fun _C hC _x hx =>
    hC _ <| Set.mem_image_of_mem _ hx

@[to_additive]
/-
**HasCompactMulSupport.exists_bound_of_continuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasCompactMulSupport.exists_bound_of_continuous [TopologicalSpace α] {f : 
α -> E} (hf : HasCompactMulSupport f) (h'f : Continuous f) : exists C, forall x,
 ‖f x‖ <= C
参数：hf : HasCompactMulSupport f；h'f : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Bornology.IsBounded.exists_norm_le'`：∀ {E : Type u_2} [inst : Seminormed
Group E] {s : Set E}, Bornology.IsBounded s → ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `HasCompactMulSupport.isCompact_range`：isCompact_range [TopologicalSpace 
β] (h : HasCompactMulSupport f) (hf : Continuous f) : IsCompact (range f)
-/
lemma HasCompactMulSupport.exists_bound_of_continuous [TopologicalSpace α]
    {f : α → E} (hf : HasCompactMulSupport f) (h'f : Continuous f) : ∃ C, ∀ x, ‖f x‖ ≤ C := by
  simpa using (hf.isCompact_range h'f).isBounded.exists_norm_le'

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to one
and a bounded function tends to one. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `‖op x y‖ ≤ A * ‖x‖ * ‖y‖` for some constant A instead of
multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
@[to_additive /-- A helper lemma used to prove that the (scalar or usual) product of a function that
tends to zero and a bounded function tends to zero. This lemma is formulated for any binary
operation `op : E → F → G` with an estimate `‖op x y‖ ≤ A * ‖x‖ * ‖y‖` for some constant A instead
of multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/]
/-
**Filter.Tendsto.op_one_isBoundedUnder_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.op_one_isBoundedUnder_le' {f : α -> E} {g : α -> F} {l : Fi
lter α} (hf : Tendsto f l (𝓝 1)) (hg : IsBoundedUnder (· <= ·) l (Norm.norm ∘ g)
) (op : E -> F -> G) (h_op : exists A, forall x y, ‖op x y‖ <= A * ‖x‖ * ‖y‖) : 
Tendsto (fun x => op (f x) (g x)) l (𝓝 1)
参数：hf : Tendsto f l (𝓝 1)；hg : IsBoundedUnder (· <= ·) l (Norm.norm ∘ g)；op : E 
-> F -> G；h_op : exists A, forall x y, ‖op x y‖ <= A * ‖x‖ * ‖y‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedGroup.tendsto_nhds_one`：NormedGroup.tendsto_nhds_one {f : α -> E} 
{l : Filter α} : Tendsto f l (𝓝 1) ↔ forall ε > 0, forallᶠ x in l, ‖f x‖ < ε
· 使用定理 `exists_pos_mul_lt`：exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : exist
s c : α, 0 < c ∧ b * c < a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
-/
lemma Filter.Tendsto.op_one_isBoundedUnder_le' {f : α → E} {g : α → F} {l : Filter α}
    (hf : Tendsto f l (𝓝 1)) (hg : IsBoundedUnder (· ≤ ·) l (Norm.norm ∘ g)) (op : E → F → G)
    (h_op : ∃ A, ∀ x y, ‖op x y‖ ≤ A * ‖x‖ * ‖y‖) : Tendsto (fun x => op (f x) (g x)) l (𝓝 1) := by
  obtain ⟨A, h_op⟩ := h_op
  rcases hg with ⟨C, hC⟩; rw [eventually_map] at hC
  rw [NormedGroup.tendsto_nhds_one] at hf ⊢
  intro ε ε₀
  rcases exists_pos_mul_lt ε₀ (A * C) with ⟨δ, δ₀, hδ⟩
  filter_upwards [hf δ δ₀, hC] with i hf hg
  refine (h_op _ _).trans_lt ?_
  rcases le_total A 0 with hA | hA
  · exact (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hA <| norm_nonneg' _) <|
      norm_nonneg' _).trans_lt ε₀
  calc
    A * ‖f i‖ * ‖g i‖ ≤ A * δ * C := by gcongr; exact hg
    _ = A * C * δ := mul_right_comm _ _ _
    _ < ε := hδ

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to one
and a bounded function tends to one. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `‖op x y‖ ≤ ‖x‖ * ‖y‖` instead of multiplication so that it
can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
@[to_additive /-- A helper lemma used to prove that the (scalar or usual) product of a function that
tends to zero and a bounded function tends to zero. This lemma is formulated for any binary
operation `op : E → F → G` with an estimate `‖op x y‖ ≤ ‖x‖ * ‖y‖` instead of multiplication so
that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/]
/-
**Filter.Tendsto.op_one_isBoundedUnder_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.op_one_isBoundedUnder_le {f : α -> E} {g : α -> F} {l : Fil
ter α} (hf : Tendsto f l (𝓝 1)) (hg : IsBoundedUnder (· <= ·) l (Norm.norm ∘ g))
 (op : E -> F -> G) (h_op : forall x y, ‖op x y‖ <= ‖x‖ * ‖y‖) : Tendsto (fun x 
=> op (f x) (g x)) l (𝓝 1)
参数：hf : Tendsto f l (𝓝 1)；hg : IsBoundedUnder (· <= ·) l (Norm.norm ∘ g)；op : E 
-> F -> G；h_op : forall x y, ‖op x y‖ <= ‖x‖ * ‖y‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.op_one_isBoundedUnder_le'`：Filter.Tendsto.op_one_isBounde
dUnder_le' {f : α -> E} {g : α -> F} {l : Filter α} (hf : Tendsto f l (𝓝 1)) (hg
 : IsBoundedUnder (· <= ·) l (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem Filter.Tendsto.op_one_isBoundedUnder_le {f : α → E} {g : α → F} {l : Filter α}
    (hf : Tendsto f l (𝓝 1)) (hg : IsBoundedUnder (· ≤ ·) l (Norm.norm ∘ g)) (op : E → F → G)
    (h_op : ∀ x y, ‖op x y‖ ≤ ‖x‖ * ‖y‖) : Tendsto (fun x => op (f x) (g x)) l (𝓝 1) :=
  hf.op_one_isBoundedUnder_le' hg op ⟨1, fun x y => (one_mul ‖x‖).symm ▸ h_op x y⟩

@[to_additive tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding]
/-
**tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding'** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding' {X : Type*} [Topolo
gicalSpace X] [DiscreteTopology X] [ProperSpace E] {e : X -> E} (he : Topology.I
sClosedEmbedding e) : Tendsto (norm ∘ e) cofinite atTop
参数：he : Topology.IsClosedEmbedding e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.cocompact_eq_cofinite`：cocompact_eq_cofinite (X : Type*) [Topolog
icalSpace X] [DiscreteTopology X] : cocompact X = cofinite
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `tendsto_norm_cocompact_atTop'`：tendsto_norm_cocompact_atTop' [ProperSpac
e E] : Tendsto norm (cocompact E) atTop
· 使用定理 `Topology.IsClosedEmbedding.tendsto_cocompact`：Topology.IsClosedEmbedding
.tendsto_cocompact (hf : IsClosedEmbedding f) : Tendsto f (Filter.cocompact X) (
Filter.cocompact Y)
-/
lemma tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding' {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] [ProperSpace E] {e : X → E}
    (he : Topology.IsClosedEmbedding e) : Tendsto (norm ∘ e) cofinite atTop := by
  rw [← Filter.cocompact_eq_cofinite X]
  apply tendsto_norm_cocompact_atTop'.comp (Topology.IsClosedEmbedding.tendsto_cocompact he)

end SeminormedGroup

section NormedAddGroup
variable [NormedAddGroup E] [TopologicalSpace α] {f : α → E}

/-
**Continuous.bounded_above_of_compact_support** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.bounded_above_of_compact_support (hf : Continuous f) (h : HasCo
mpactSupport f) : exists C, forall x, ‖f x‖ <= C
参数：hf : Continuous f；h : HasCompactSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Continuous.bddAbove_range_of_hasCompactSupport`：∀ {α : Type u_2} {β : Ty
pe u_3} [inst : LinearOrder α] [inst_1 : TopologicalSpace α] [inst_2 : Topologic
alSpace β]   [ClosedIciTopology α] […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `HasCompactSupport.norm`：∀ {α : Type u_2} {E : Type u_5} [inst : NormedAd
dGroup E] [inst_1 : TopologicalSpace α] {f : α → E},   HasCompactSupport f → Has
CompactSuppo…
-/
lemma Continuous.bounded_above_of_compact_support (hf : Continuous f) (h : HasCompactSupport f) :
    ∃ C, ∀ x, ‖f x‖ ≤ C := by
  simpa [bddAbove_def] using hf.norm.bddAbove_range_of_hasCompactSupport h.norm

end NormedAddGroup

section NormedAddGroupSource
variable [NormedAddGroup α] {f : α → E}

@[to_additive]
/-
**HasCompactMulSupport.exists_pos_le_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasCompactMulSupport.exists_pos_le_norm [One E] (hf : HasCompactMulSupport
 f) : exists R : Real, 0 < R ∧ forall x : α, R <= ‖x‖ -> f x = 1
参数：hf : HasCompactMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `exists_compact_iff_hasCompactMulSupport`：exists_compact_iff_hasCompactMu
lSupport [R1Space α] : (exists K : Set α, IsCompact K ∧ forall x, x ∉ K -> f x =
 1) ↔ HasCompactMulSupport f
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Bornology.IsBounded.exists_pos_norm_le`：∀ {E : Type u_2} [inst : Seminor
medAddGroup E] {s : Set E}, Bornology.IsBounded s → ∃ R > 0, ∀ x ∈ s, ‖x‖ ≤ R
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `lt_add_of_le_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [AddLeftStrictMono α] {a b c : α},   b ≤ c → 0 < a → b < c + a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma HasCompactMulSupport.exists_pos_le_norm [One E] (hf : HasCompactMulSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : α, R ≤ ‖x‖ → f x = 1 := by
  obtain ⟨K, ⟨hK1, hK2⟩⟩ := exists_compact_iff_hasCompactMulSupport.mpr hf
  obtain ⟨S, hS, hS'⟩ := hK1.isBounded.exists_pos_norm_le
  refine ⟨S + 1, by positivity, fun x hx => hK2 x ((mt <| hS' x) ?_)⟩
  contrapose! hx
  exact lt_add_of_le_of_pos hx zero_lt_one

end NormedAddGroupSource

