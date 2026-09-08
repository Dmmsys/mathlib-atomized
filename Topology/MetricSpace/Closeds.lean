/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.UniformSpace.Closeds

/-!
# Closed subsets

This file defines the metric and emetric space structure on the types of closed subsets and nonempty
compact subsets of a metric or emetric space.

The Hausdorff distance induces an emetric space structure on the type of closed subsets
of an emetric space, called `Closeds`. Its completeness, resp. compactness, resp.
second-countability, follow from the corresponding properties of the original space.

In a metric space, the type of nonempty compact subsets (called `NonemptyCompacts`) also
inherits a metric space structure from the Hausdorff distance, as the Hausdorff edistance is
always finite in this context.
-/

public section

noncomputable section

open Set Function TopologicalSpace Filter Topology ENNReal

namespace Metric

variable {α : Type*} [PseudoEMetricSpace α]

/-
**Metric.mem_hausdorffEntourage_of_hausdorffEDist_lt** 是 Mathlib 中的一个定理，位于命名空间 `
Metric`。
形式化陈述：mem_hausdorffEntourage_of_hausdorffEDist_lt {s t : Set α} {δ : Real>=0∞} (
h : hausdorffEDist s t < δ) : (s, t) in hausdorffEntourage {p | edist p.1 p.2 < 
δ}
参数：h : hausdorffEDist s t < δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hausdorffEntourage.eq_1`：∀ {α : Type u_1} (U : SetRel α α), hausdorffEnt
ourage U = {x | x.1 ⊆ U.preimage x.2 ∧ x.2 ⊆ U.image x.1}
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用定理 `Metric.hausdorffEDist_def`：∀ {α : Type u_2} [inst : PseudoEMetricSpace α
] (s t : Set α),   Metric.hausdorffEDist s t = max (⨆ x ∈ s, Metric.infEDist x t
) (⨆ y ∈ t, Met…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mem_hausdorffEntourage_of_hausdorffEDist_lt {s t : Set α} {δ : ℝ≥0∞}
    (h : hausdorffEDist s t < δ) : (s, t) ∈ hausdorffEntourage {p | edist p.1 p.2 < δ} := by
  rw [hausdorffEDist, max_lt_iff] at h
  rw [hausdorffEntourage, Set.mem_ofPred]
  conv => enter [2, 2, 1, 1, _]; rw [edist_comm]
  have {s t : Set α} (h : ⨆ x ∈ s, infEDist x t < δ) :
      s ⊆ SetRel.preimage {p | edist p.1 p.2 < δ} t := by
    intro x hx
    simpa only [infEDist, iInf_lt_iff, exists_prop] using! (le_iSup₂ x hx).trans_lt h
  exact ⟨this h.1, this h.2⟩
/-
**Metric.hausdorffEDist_le_of_mem_hausdorffEntourage** 是 Mathlib 中的一个定理，位于命名空间 `
Metric`。
形式化陈述：hausdorffEDist_le_of_mem_hausdorffEntourage {s t : Set α} {δ : Real>=0∞} (
h : (s, t) in hausdorffEntourage {p | edist p.1 p.2 <= δ}) : hausdorffEDist s t 
<= δ
参数：h : (s, t) in hausdorffEntourage {p | edist p.1 p.2 <= δ}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_def`：∀ {α : Type u_2} [inst : PseudoEMetricSpace α
] (s t : Set α),   Metric.hausdorffEDist s t = max (⨆ x ∈ s, Metric.infEDist x t
) (⨆ y ∈ t, Met…
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `hausdorffEntourage.eq_1`：∀ {α : Type u_1} (U : SetRel α α), hausdorffEnt
ourage U = {x | x.1 ⊆ U.preimage x.2 ∧ x.2 ⊆ U.image x.1}
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem hausdorffEDist_le_of_mem_hausdorffEntourage {s t : Set α} {δ : ℝ≥0∞}
    (h : (s, t) ∈ hausdorffEntourage {p | edist p.1 p.2 ≤ δ}) : hausdorffEDist s t ≤ δ := by
  rw [hausdorffEDist, max_le_iff]
  rw [hausdorffEntourage, Set.mem_ofPred] at h
  conv at h => enter [2, 2, 1, 1, _]; rw [edist_comm]
  have {s t : Set α} (h : s ⊆ SetRel.preimage {p | edist p.1 p.2 ≤ δ} t) :
      ⨆ x ∈ s, infEDist x t ≤ δ := by
    rw [iSup₂_le_iff]
    intro x hx
    obtain ⟨y, hy, hxy⟩ := h hx
    exact iInf₂_le_of_le y hy hxy
  exact ⟨this h.1, this h.2⟩

/-- The Hausdorff pseudo emetric on the powerset of a pseudo emetric space.
See note [reducible non-instances]. -/
/-
**Metric._root_.PseudoEMetricSpace.hausdorff** 是 Mathlib 中的一个缩写定义，位于命名空间 `Metric
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Hausdorff pseudo emetric on the powerset of a pseudo emetric space.
See note [reducible non-instances].
-/
protected abbrev _root_.PseudoEMetricSpace.hausdorff : PseudoEMetricSpace (Set α) where
  edist s t := hausdorffEDist s t
  edist_self _ := hausdorffEDist_self
  edist_comm _ _ := hausdorffEDist_comm
  edist_triangle _ _ _ := hausdorffEDist_triangle
  toUniformSpace := .hausdorff α
  uniformity_edist := by
    refine le_antisymm
      (le_iInf₂ fun ε hε => Filter.le_principal_iff.mpr ?_)
      (uniformity_basis_edist.lift' monotone_hausdorffEntourage |>.ge_iff.mpr fun ε hε =>
        Filter.mem_iInf_of_mem ε <| Filter.mem_iInf_of_mem hε fun _ =>
        mem_hausdorffEntourage_of_hausdorffEDist_lt)
    obtain ⟨δ, hδ, hδε⟩ := exists_between hε
    filter_upwards [Filter.mem_lift' (uniformity_basis_edist_le.mem_of_mem hδ)]
      with _ h using hδε.trans_le' <| hausdorffEDist_le_of_mem_hausdorffEntourage h

end Metric

namespace TopologicalSpace

open Metric

variable {α β : Type*} [EMetricSpace α] [EMetricSpace β] {s : Set α}

namespace Closeds

/-- In emetric spaces, the Hausdorff edistance defines an emetric space structure
on the type of closed subsets -/
/-
**TopologicalSpace.Closeds.instEMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `Topologic
alSpace.Closeds`。
形式化陈述：instEMetricSpace : EMetricSpace (Closeds α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In emetric spaces, the Hausdorff edistance defines an emetric space structure
on the type of closed subsets
-/
instance instEMetricSpace : EMetricSpace (Closeds α) where
  __ := PseudoEMetricSpace.hausdorff.induced SetLike.coe
  eq_of_edist_eq_zero {s t} h := Closeds.ext <| (s.isClosed.hausdorffEDist_zero_iff t.isClosed).1 h

/-- The edistance to a closed set depends continuously on the point and the set -/
/-
**TopologicalSpace.Closeds.continuous_infEDist** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gicalSpace.Closeds`。
形式化陈述：continuous_infEDist : Continuous fun p : α × Closeds α => infEDist p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_le_add_edist`：continuous_of_le_add_edist {f : α -> Real>=0
∞} (C : Real>=0∞) (hC : C != ∞) (h : forall x y, f x <= f y + C * edist x y) : C
ontinuous f
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Metric.infEDist_le_infEDist_add_hausdorffEDist`：infEDist_le_infEDist_add
_hausdorffEDist : infEDist x t <= infEDist x s + hausdorffEDist s t
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Metric.infEDist_le_infEDist_add_edist`：infEDist_le_infEDist_add_edist : 
infEDist x s <= infEDist y s + edist x y
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Metric.hausdorffEDist_comm`：hausdorffEDist_comm : hausdorffEDist s t = h
ausdorffEDist t s
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
The edistance to a closed set depends continuously on the point and the set
-/
theorem continuous_infEDist :
    Continuous fun p : α × Closeds α => infEDist p.1 p.2 := by
  refine continuous_of_le_add_edist 2 (by simp) ?_
  rintro ⟨x, s⟩ ⟨y, t⟩
  calc
    infEDist x s ≤ infEDist x t + hausdorffEDist (t : Set α) s :=
      infEDist_le_infEDist_add_hausdorffEDist
    _ ≤ infEDist y t + edist x y + hausdorffEDist (t : Set α) s := by
      gcongr; apply infEDist_le_infEDist_add_edist
    _ = infEDist y t + (edist x y + hausdorffEDist (s : Set α) t) := by
      rw [add_assoc, hausdorffEDist_comm]
    _ ≤ infEDist y t + (edist (x, s) (y, t) + edist (x, s) (y, t)) := by
      gcongr <;> apply_rules [le_max_left, le_max_right]
    _ = infEDist y t + 2 * edist (x, s) (y, t) := by rw [← mul_two, mul_comm]

/-- By definition, the edistance on `Closeds α` is given by the Hausdorff edistance -/
/-
**TopologicalSpace.Closeds.edist_eq** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Closeds`。
形式化陈述：edist_eq {s t : Closeds α} : edist s t = hausdorffEDist (s : Set α) t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
By definition, the edistance on `Closeds α` is given by the Hausdorff edistance
-/
theorem edist_eq {s t : Closeds α} : edist s t = hausdorffEDist (s : Set α) t :=
  rfl

/-- In a complete space, the type of closed subsets is complete for the Hausdorff edistance. -/
/-
**TopologicalSpace.Closeds.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 `Topologi
calSpace.Closeds`。
形式化陈述：instCompleteSpace [CompleteSpace α] : CompleteSpace (Closeds α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `ENNReal.pow_ne_top`：pow_ne_top (ha : a != ∞) : a ^ n != ∞
· 使用定理 `ENNReal.Finiteness.inv_ne_top`：∀ {a : ENNReal}, a ≠ 0 → a⁻¹ ≠ ⊤
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `EMetric.complete_of_convergent_controlled_sequences`：complete_of_converg
ent_controlled_sequences (B : Nat -> Real>=0∞) (hB : forall n, 0 < B n) (H : for
all u : Nat -> α, (forall N n m : Nat, N …
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Metric.exists_edist_lt_of_hausdorffEDist_lt`：exists_edist_lt_of_hausdorf
fEDist_lt {r : Real>=0∞} (h : x in s) (H : hausdorffEDist s t < r) : exists y in
 t, edist x y < r
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.inv_pow`：∀ {a : ENNReal} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
In a complete space, the type of closed subsets is complete for the Hausdorff ed
istance.
-/
instance instCompleteSpace [CompleteSpace α] : CompleteSpace (Closeds α) := by
  /- We will show that, if a sequence of sets `s n` satisfies
    `edist (s n) (s (n+1)) < 2^{-n}`, then it converges. This is enough to guarantee
    completeness, by a standard completeness criterion.
    We use the shorthand `B n = 2^{-n}` in ennreal. -/
  let B : ℕ → ℝ≥0∞ := fun n => 2⁻¹ ^ n
  have B_pos : ∀ n, (0 : ℝ≥0∞) < B n := by simp [B, ENNReal.pow_pos]
  have B_ne_top : ∀ n, B n ≠ ⊤ := by finiteness
  /- Consider a sequence of closed sets `s n` with `edist (s n) (s (n+1)) < B n`.
    We will show that it converges. The limit set is `t0 = ⋂n, closure (⋃m≥n, s m)`.
    We will have to show that a point in `s n` is close to a point in `t0`, and a point
    in `t0` is close to a point in `s n`. The completeness then follows from a
    standard criterion. -/
  refine EMetric.complete_of_convergent_controlled_sequences B B_pos fun s hs => ?_
  let t0 := ⋂ n, closure (⋃ m ≥ n, s m : Set α)
  let t : Closeds α := ⟨t0, isClosed_iInter fun _ => isClosed_closure⟩
  use t
  -- The inequality is written this way to agree with `edist_le_of_edist_le_geometric_of_tendsto₀`
  have I1 : ∀ n, ∀ x ∈ s n, ∃ y ∈ t0, edist x y ≤ 2 * B n := by
    /- This is the main difficulty of the proof. Starting from `x ∈ s n`, we want
           to find a point in `t0` which is close to `x`. Define inductively a sequence of
           points `z m` with `z n = x` and `z m ∈ s m` and `edist (z m) (z (m+1)) ≤ B m`. This is
           possible since the Hausdorff distance between `s m` and `s (m+1)` is at most `B m`.
           This sequence is a Cauchy sequence, therefore converging as the space is complete, to
           a limit which satisfies the required properties. -/
    intro n x hx
    obtain ⟨z, hz₀, hz⟩ :
      ∃ z : ∀ l, s (n + l), (z 0 : α) = x ∧ ∀ k, edist (z k : α) (z (k + 1) : α) ≤ B n / 2 ^ k := by
      -- We prove existence of the sequence by induction.
      have : ∀ (l) (z : s (n + l)), ∃ z' : s (n + l + 1), edist (z : α) z' ≤ B n / 2 ^ l := by
        intro l z
        obtain ⟨z', z'_mem, hz'⟩ : ∃ z' ∈ s (n + l + 1), edist (z : α) z' < B n / 2 ^ l := by
          refine exists_edist_lt_of_hausdorffEDist_lt (s := s (n + l)) z.2 ?_
          simp only [ENNReal.inv_pow, div_eq_mul_inv]
          rw [← pow_add]
          apply hs <;> simp
        exact ⟨⟨z', z'_mem⟩, le_of_lt hz'⟩
      use fun k => Nat.recOn k ⟨x, hx⟩ fun l z => (this l z).choose
      simp only [Nat.add_zero, Nat.rec_zero, true_and]
      exact fun k => (this k _).choose_spec
    -- it follows from the previous bound that `z` is a Cauchy sequence
    have : CauchySeq fun k => (z k : α) := cauchySeq_of_edist_le_geometric_two (B n) (B_ne_top n) hz
    -- therefore, it converges
    rcases cauchySeq_tendsto_of_complete this with ⟨y, y_lim⟩
    use y
    -- the limit point `y` will be the desired point, in `t0` and close to our initial point `x`.
    -- First, we check it belongs to `t0`.
    have : y ∈ t0 :=
      mem_iInter.2 fun k =>
        mem_closure_of_tendsto y_lim
          (by
            simp only [exists_prop, Set.mem_iUnion, Filter.eventually_atTop]
            exact ⟨k, fun m hm => ⟨n + m, by lia, (z m).2⟩⟩)
    use this
    -- Then, we check that `y` is close to `x = z n`. This follows from the fact that `y`
    -- is the limit of `z k`, and the distance between `z n` and `z k` has already been estimated.
    rw [← hz₀]
    exact edist_le_of_edist_le_geometric_two_of_tendsto₀ (B n) hz y_lim
  have I2 : ∀ n, ∀ x ∈ t0, ∃ y ∈ s n, edist x y ≤ 2 * B n := by
    /- For the (much easier) reverse inequality, we start from a point `x ∈ t0` and we want
            to find a point `y ∈ s n` which is close to `x`.
            `x` belongs to `t0`, the intersection of the closures. In particular, it is well
            approximated by a point `z` in `⋃m≥n, s m`, say in `s m`. Since `s m` and
            `s n` are close, this point is itself well approximated by a point `y` in `s n`,
            as required. -/
    intro n x xt0
    have : x ∈ closure (⋃ m ≥ n, s m : Set α) := by apply mem_iInter.1 xt0 n
    obtain ⟨z : α, hz, Dxz : edist x z < B n⟩ := EMetric.mem_closure_iff.1 this (B n) (B_pos n)
    simp only [exists_prop, Set.mem_iUnion] at hz
    obtain ⟨m : ℕ, m_ge_n : m ≥ n, hm : z ∈ (s m : Set α)⟩ := hz
    have : hausdorffEDist (s m : Set α) (s n) < B n := hs n m n m_ge_n (le_refl n)
    obtain ⟨y : α, hy : y ∈ (s n : Set α), Dzy : edist z y < B n⟩ :=
      exists_edist_lt_of_hausdorffEDist_lt hm this
    exact
      ⟨y, hy,
        calc
          edist x y ≤ edist x z + edist z y := edist_triangle _ _ _
          _ ≤ B n + B n := by gcongr
          _ = 2 * B n := (two_mul _).symm
          ⟩
  -- Deduce from the above inequalities that the distance between `s n` and `t0` is at most `2 B n`.
  have main : ∀ n : ℕ, edist (s n) t ≤ 2 * B n := fun n =>
    hausdorffEDist_le_of_mem_edist (I1 n) (I2 n)
  -- from this, the convergence of `s n` to `t0` follows.
  refine EMetric.tendsto_atTop.2 fun ε εpos => ?_
  have : Tendsto (fun n => 2 * B n) atTop (𝓝 (2 * 0)) :=
    ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one <|
      by simp) (Or.inr <| by simp)
  rw [mul_zero] at this
  obtain ⟨N, hN⟩ : ∃ N, ∀ b ≥ N, ε > 2 * B b :=
    ((tendsto_order.1 this).2 ε εpos).exists_forall_of_atTop
  exact ⟨N, fun n hn => lt_of_le_of_lt (main n) (hN n hn)⟩
/-
**TopologicalSpace.Closeds.isometry_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
icalSpace.Closeds`。
形式化陈述：isometry_singleton : Isometry ({·} : α -> Closeds α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.hausdorffEDist_singleton`：hausdorffEDist_singleton : hausdorffEDi
st {x} {y} = edist x y
-/
theorem isometry_singleton : Isometry ({·} : α → Closeds α) :=
  fun _ _ => hausdorffEDist_singleton
/-
**TopologicalSpace.Closeds.lipschitz_sup** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.Closeds`。
形式化陈述：lipschitz_sup : LipschitzWith 1 fun p : Closeds α × Closeds α => p.1 ⊔ p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_edist_le`：∀ {α : Type u} {β : Type v} [inst : PseudoEMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   (∀ (x y : α), edist 
(f x) (f y) ≤ e…
· 使用定理 `Metric.hausdorffEDist_union_le`：hausdorffEDist_union_le {s₁ s₂ t₁ t₂ : S
et α} : hausdorffEDist (s₁ union s₂) (t₁ union t₂) <= max (hausdorffEDist s₁ t₁)
 (hausdorffEDist s₂ …
-/
theorem lipschitz_sup : LipschitzWith 1 fun p : Closeds α × Closeds α => p.1 ⊔ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_union_le
/-
**TopologicalSpace.Closeds.lipschitz_prod** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.Closeds`。
形式化陈述：lipschitz_prod : LipschitzWith 1 fun p : Closeds α × Closeds β => p.1 ×ˢ p
.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_edist_le`：∀ {α : Type u} {β : Type v} [inst : PseudoEMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   (∀ (x y : α), edist 
(f x) (f y) ≤ e…
· 使用定理 `Metric.hausdorffEDist_prod_le`：hausdorffEDist_prod_le {s₁ t₁ : Set α} {s
₂ t₂ : Set β} : hausdorffEDist (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) <= max (hausdorffEDist s₁ t
₁) (hausdorffEDist …
-/
theorem lipschitz_prod : LipschitzWith 1 fun p : Closeds α × Closeds β => p.1 ×ˢ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_prod_le

end Closeds

namespace Compacts

/-- In an emetric space, the type of compact subsets is an emetric space,
where the edistance is the Hausdorff edistance -/
/-
**TopologicalSpace.Compacts.instEMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `Topologi
calSpace.Compacts`。
形式化陈述：instEMetricSpace : EMetricSpace (Compacts α) where /- Since the topology o
n `Compacts` is not defeq to the one induced by `UniformSpace.hausdorff`, we rep
lace the uniformity by `Compacts.uniformSpace`, which has the right topology. -/
 __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In an emetric space, the type of compact subsets is an emetric space,
where the edistance is the Hausdorff edistance
-/
instance instEMetricSpace : EMetricSpace (Compacts α) where
  /- Since the topology on `Compacts` is not defeq to the one induced by
  `UniformSpace.hausdorff`, we replace the uniformity by `Compacts.uniformSpace`, which has
  the right topology. -/
  __ := (PseudoEMetricSpace.hausdorff.induced SetLike.coe).replaceUniformity <| by rfl
  eq_of_edist_eq_zero {s t} h := Compacts.ext <| by
    have : closure (s : Set α) = closure t := hausdorffEDist_zero_iff_closure_eq_closure.1 h
    rwa [s.isCompact.isClosed.closure_eq, t.isCompact.isClosed.closure_eq] at this
/-
**TopologicalSpace.Compacts.edist_eq** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace
.Compacts`。
形式化陈述：edist_eq {s t : Compacts α} : edist s t = hausdorffEDist (s : Set α) t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_eq {s t : Compacts α} : edist s t = hausdorffEDist (s : Set α) t :=
  rfl
/-
**TopologicalSpace.Compacts.isometry_toCloseds** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gicalSpace.Compacts`。
形式化陈述：isometry_toCloseds : Isometry (Compacts.toCloseds (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem isometry_toCloseds : Isometry (Compacts.toCloseds (α := α)) :=
  fun _ _ => rfl
/-
**TopologicalSpace.Compacts.isometry_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gicalSpace.Compacts`。
形式化陈述：isometry_singleton : Isometry ({·} : α -> Compacts α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.hausdorffEDist_singleton`：hausdorffEDist_singleton : hausdorffEDi
st {x} {y} = edist x y
-/
theorem isometry_singleton : Isometry ({·} : α → Compacts α) :=
  fun _ _ => hausdorffEDist_singleton
/-
**TopologicalSpace.Compacts.lipschitz_sup** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.Compacts`。
形式化陈述：lipschitz_sup : LipschitzWith 1 fun p : Compacts α × Compacts α => p.1 ⊔ p
.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_edist_le`：∀ {α : Type u} {β : Type v} [inst : PseudoEMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   (∀ (x y : α), edist 
(f x) (f y) ≤ e…
· 使用定理 `Metric.hausdorffEDist_union_le`：hausdorffEDist_union_le {s₁ s₂ t₁ t₂ : S
et α} : hausdorffEDist (s₁ union s₂) (t₁ union t₂) <= max (hausdorffEDist s₁ t₁)
 (hausdorffEDist s₂ …
-/
theorem lipschitz_sup :
    LipschitzWith 1 fun p : Compacts α × Compacts α => p.1 ⊔ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_union_le
/-
**TopologicalSpace.Compacts.lipschitz_prod** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.Compacts`。
形式化陈述：lipschitz_prod : LipschitzWith 1 fun p : Compacts α × Compacts β => p.1 ×ˢ
 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_edist_le`：∀ {α : Type u} {β : Type v} [inst : PseudoEMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   (∀ (x y : α), edist 
(f x) (f y) ≤ e…
· 使用定理 `Metric.hausdorffEDist_prod_le`：hausdorffEDist_prod_le {s₁ t₁ : Set α} {s
₂ t₂ : Set β} : hausdorffEDist (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) <= max (hausdorffEDist s₁ t
₁) (hausdorffEDist …
-/
theorem lipschitz_prod :
    LipschitzWith 1 fun p : Compacts α × Compacts β => p.1 ×ˢ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_prod_le

end Compacts

namespace NonemptyCompacts

/-- In an emetric space, the type of non-empty compact subsets is an emetric space,
where the edistance is the Hausdorff edistance -/
/-
**TopologicalSpace.NonemptyCompacts.instEMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `
TopologicalSpace.NonemptyCompacts`。
形式化陈述：instEMetricSpace : EMetricSpace (NonemptyCompacts α) where /- Since the to
pology on `NonemptyCompacts` is not defeq to the one induced by `UniformSpace.ha
usdorff`, we replace the uniformity by `NonemptyCompacts.uniformSpace`, which ha
s the right topology. -/ __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In an emetric space, the type of non-empty compact subsets is an emetric space,
where the edistance is the Hausdorff edistance
-/
instance instEMetricSpace : EMetricSpace (NonemptyCompacts α) where
  /- Since the topology on `NonemptyCompacts` is not defeq to the one induced by
  `UniformSpace.hausdorff`, we replace the uniformity by `NonemptyCompacts.uniformSpace`, which has
  the right topology. -/
  __ := (PseudoEMetricSpace.hausdorff.induced SetLike.coe).replaceUniformity <| by rfl
  eq_of_edist_eq_zero {s t} h := NonemptyCompacts.ext <| by
    have : closure (s : Set α) = closure t := hausdorffEDist_zero_iff_closure_eq_closure.1 h
    rwa [s.isCompact.isClosed.closure_eq, t.isCompact.isClosed.closure_eq] at this

/-- `NonemptyCompacts.toCloseds` is an isometry -/
/-
**TopologicalSpace.NonemptyCompacts.isometry_toCloseds** 是 Mathlib 中的一个定理，位于命名空间
 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：isometry_toCloseds : Isometry (@NonemptyCompacts.toCloseds α _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α

--- 原说明 ---
`NonemptyCompacts.toCloseds` is an isometry
-/
theorem isometry_toCloseds : Isometry (@NonemptyCompacts.toCloseds α _ _) :=
  fun _ _ => rfl
/-
**TopologicalSpace.NonemptyCompacts.isometry_toCompacts** 是 Mathlib 中的一个定理，位于命名空
间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：isometry_toCompacts : Isometry (NonemptyCompacts.toCompacts (α
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isometry_toCompacts : Isometry (NonemptyCompacts.toCompacts (α := α)) :=
  fun _ _ => rfl

/-- The range of `NonemptyCompacts.toCloseds` is closed in a complete space -/
@[deprecated
  "Use `TopologicalSpace.NonemptyCompacts.isClosedEmbedding_toCloseds.isClosed_range` instead"
  (since := "2026-01-28")]
/-
**TopologicalSpace.NonemptyCompacts.isClosed_in_closeds** 是 Mathlib 中的一个定理，位于命名空
间 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：isClosed_in_closeds [CompleteSpace α] : IsClosed (range <| @NonemptyCompac
ts.toCloseds α _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `TopologicalSpace.NonemptyCompacts.isClosedEmbedding_toCloseds`：isClosedE
mbedding_toCloseds [T2Space α] [CompleteSpace α] : IsClosedEmbedding (toCloseds 
(α
-/
theorem isClosed_in_closeds [CompleteSpace α] :
    IsClosed (range <| @NonemptyCompacts.toCloseds α _ _) :=
  NonemptyCompacts.isClosedEmbedding_toCloseds.isClosed_range
/-
**TopologicalSpace.NonemptyCompacts.isometry_singleton** 是 Mathlib 中的一个定理，位于命名空间
 `TopologicalSpace.NonemptyCompacts`。
形式化陈述：isometry_singleton : Isometry ({·} : α -> NonemptyCompacts α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.hausdorffEDist_singleton`：hausdorffEDist_singleton : hausdorffEDi
st {x} {y} = edist x y
-/
theorem isometry_singleton : Isometry ({·} : α → NonemptyCompacts α) :=
  fun _ _ => hausdorffEDist_singleton
/-
**TopologicalSpace.NonemptyCompacts.lipschitz_sup** 是 Mathlib 中的一个定理，位于命名空间 `Top
ologicalSpace.NonemptyCompacts`。
形式化陈述：lipschitz_sup : LipschitzWith 1 fun p : NonemptyCompacts α × NonemptyCompa
cts α => p.1 ⊔ p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_edist_le`：∀ {α : Type u} {β : Type v} [inst : PseudoEMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   (∀ (x y : α), edist 
(f x) (f y) ≤ e…
· 使用定理 `Metric.hausdorffEDist_union_le`：hausdorffEDist_union_le {s₁ s₂ t₁ t₂ : S
et α} : hausdorffEDist (s₁ union s₂) (t₁ union t₂) <= max (hausdorffEDist s₁ t₁)
 (hausdorffEDist s₂ …
-/
theorem lipschitz_sup :
    LipschitzWith 1 fun p : NonemptyCompacts α × NonemptyCompacts α => p.1 ⊔ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_union_le
/-
**TopologicalSpace.NonemptyCompacts.lipschitz_prod** 是 Mathlib 中的一个定理，位于命名空间 `To
pologicalSpace.NonemptyCompacts`。
形式化陈述：lipschitz_prod : LipschitzWith 1 fun p : NonemptyCompacts α × NonemptyComp
acts β => p.1 ×ˢ p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_edist_le`：∀ {α : Type u} {β : Type v} [inst : PseudoEMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   (∀ (x y : α), edist 
(f x) (f y) ≤ e…
· 使用定理 `Metric.hausdorffEDist_prod_le`：hausdorffEDist_prod_le {s₁ t₁ : Set α} {s
₂ t₂ : Set β} : hausdorffEDist (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) <= max (hausdorffEDist s₁ t
₁) (hausdorffEDist …
-/
theorem lipschitz_prod :
    LipschitzWith 1 fun p : NonemptyCompacts α × NonemptyCompacts β => p.1 ×ˢ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_prod_le

end NonemptyCompacts

end TopologicalSpace

namespace EMetric

open Metric

@[deprecated (since := "2026-01-08")]
alias mem_hausdorffEntourage_of_hausdorffEdist_lt :=
  mem_hausdorffEntourage_of_hausdorffEDist_lt

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_le_of_mem_hausdorffEntourage := hausdorffEDist_le_of_mem_hausdorffEntourage

@[deprecated (since := "2026-01-08")]
alias continuous_infEdist_hausdorffEdist :=
  TopologicalSpace.Closeds.continuous_infEDist

@[deprecated (since := "2026-01-08")]
alias Closeds.edist_eq := TopologicalSpace.Closeds.edist_eq

@[deprecated (since := "2026-01-08")]
alias Closeds.isometry_singleton := TopologicalSpace.Closeds.isometry_singleton

@[deprecated (since := "2026-01-08")]
alias Closeds.lipschitz_sup := TopologicalSpace.Closeds.lipschitz_sup

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.isometry_toCloseds :=
  TopologicalSpace.NonemptyCompacts.isometry_toCloseds

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.isClosed_in_closeds :=
  TopologicalSpace.NonemptyCompacts.isClosed_in_closeds

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.isometry_singleton :=
  TopologicalSpace.NonemptyCompacts.isometry_singleton

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.lipschitz_sup :=
  TopologicalSpace.NonemptyCompacts.lipschitz_sup

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.lipschitz_prod :=
  TopologicalSpace.NonemptyCompacts.lipschitz_prod

end EMetric --namespace

namespace Metric

section

variable {α : Type*} [MetricSpace α]

/-- `NonemptyCompacts α` inherits a metric space structure, as the Hausdorff
edistance between two such sets is finite. -/
/-
**Metric.NonemptyCompacts.instMetricSpace** 是 Mathlib 中的一个定义，位于命名空间 `Metric.None
mptyCompacts`。
形式化陈述：{α : Type u_1} → [inst : MetricSpace α] → MetricSpace (TopologicalSpace.No
nemptyCompacts α)
参数：TopologicalSpace.NonemptyCompacts α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonemptyCompacts α` inherits a metric space structure, as the Hausdorff
edistance between two such sets is finite.
-/
instance NonemptyCompacts.instMetricSpace : MetricSpace (NonemptyCompacts α) :=
  EMetricSpace.toMetricSpace fun x y =>
    hausdorffEDist_ne_top_of_nonempty_of_bounded x.nonempty y.nonempty x.isCompact.isBounded
      y.isCompact.isBounded

/-- The distance on `NonemptyCompacts α` is the Hausdorff distance, by construction -/
/-
**Metric.NonemptyCompacts.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Metric.NonemptyComp
acts`。
形式化陈述：∀ {α : Type u_1} [inst : MetricSpace α] {x y : TopologicalSpace.NonemptyCo
mpacts α},   dist x y = Metric.hausdorffDist ↑x ↑y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distance on `NonemptyCompacts α` is the Hausdorff distance, by construction
-/
theorem NonemptyCompacts.dist_eq {x y : NonemptyCompacts α} :
    dist x y = hausdorffDist (x : Set α) y :=
  rfl
/-
**Metric.lipschitz_infDist_set** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：lipschitz_infDist_set (x : α) : LipschitzWith 1 fun s : NonemptyCompacts α
 => infDist x s
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_le_add`：∀ {α : Type u} [inst : PseudoMetricSpace α] {f 
: α → ℝ}, (∀ (x y : α), f x ≤ f y + dist x y) → LipschitzWith 1 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Metric.infDist_le_infDist_add_hausdorffDist`：infDist_le_infDist_add_haus
dorffDist (fin : hausdorffEDist s t != ⊤) : infDist x t <= infDist x s + hausdor
ffDist s t
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
-/
theorem lipschitz_infDist_set (x : α) : LipschitzWith 1 fun s : NonemptyCompacts α => infDist x s :=
  LipschitzWith.of_le_add fun s t => by
    rw [dist_comm]
    exact infDist_le_infDist_add_hausdorffDist (edist_ne_top t s)
/-
**Metric.lipschitz_infDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：lipschitz_infDist : LipschitzWith 2 fun p : α × NonemptyCompacts α => infD
ist p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `LipschitzWith.uncurry`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : 
PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricS
pace γ] {f …
· 使用定理 `Metric.lipschitz_infDist_pt`：lipschitz_infDist_pt : LipschitzWith 1 (inf
Dist · s)
· 使用定理 `Metric.lipschitz_infDist_set`：lipschitz_infDist_set (x : α) : LipschitzW
ith 1 fun s : NonemptyCompacts α => infDist x s
-/
theorem lipschitz_infDist : LipschitzWith 2 fun p : α × NonemptyCompacts α => infDist p.1 p.2 := by
  rw [← one_add_one_eq_two]
  exact LipschitzWith.uncurry
    (fun s : NonemptyCompacts α => lipschitz_infDist_pt (s : Set α)) lipschitz_infDist_set
/-
**Metric.uniformContinuous_infDist_Hausdorff_dist** 是 Mathlib 中的一个定理，位于命名空间 `Met
ric`。
形式化陈述：uniformContinuous_infDist_Hausdorff_dist : UniformContinuous fun p : α × N
onemptyCompacts α => infDist p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.lipschitz_infDist`：lipschitz_infDist : LipschitzWith 2 fun p : α 
× NonemptyCompacts α => infDist p.1 p.2
-/
theorem uniformContinuous_infDist_Hausdorff_dist :
    UniformContinuous fun p : α × NonemptyCompacts α => infDist p.1 p.2 :=
  lipschitz_infDist.uniformContinuous

end --section

end Metric --namespace

