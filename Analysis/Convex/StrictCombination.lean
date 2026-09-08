/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Convex combinations in strictly convex sets and spaces.

This file proves lemmas about convex combinations of points in strictly convex sets and strictly
convex spaces.

-/

public section


open Finset Metric

variable {R V P ι : Type*}

section Set

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [TopologicalSpace V] [AddCommGroup V]
variable [Module R V]

/-
**StrictConvex.centerMass_mem_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictConvex.centerMass_mem_interior {s : Set V} {t : Finset ι} {w : ι -> 
R} {z : ι -> V} (hs : StrictConvex R s) : (forall i in t, 0 <= w i) -> forall i 
j, i in t -> j in t -> z i != z j -> w i != 0 -> w j != 0 -> (forall i in t, z i
 in s) -> t.centerMass w z in interior s
参数：hs : StrictConvex R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.centerMass_insert`：Finset.centerMass_insert [DecidableEq ι] (ha :
 i ∉ t) (hw : ∑ j in t, w j != 0) : (insert i t).centerMass w z = (w i / (w i + 
∑ j in t, w j)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `lt_of_lt_of_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
（共 49 条，此处仅展示前 30 条）
-/
lemma StrictConvex.centerMass_mem_interior {s : Set V} {t : Finset ι} {w : ι → R} {z : ι → V}
    (hs : StrictConvex R s) :
    (∀ i ∈ t, 0 ≤ w i) → ∀ i j, i ∈ t → j ∈ t → z i ≠ z j → w i ≠ 0 → w j ≠ 0 →
      (∀ i ∈ t, z i ∈ s) → t.centerMass w z ∈ interior s := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ht =>
    intro h₀ i' j' hi' hj' hi'j' hi'0 hj'0 hmem
    have zi : z i ∈ s := hmem _ (mem_insert_self _ _)
    have hs₀ : ∀ j ∈ t, 0 ≤ w j := fun j hj => h₀ j <| mem_insert_of_mem hj
    by_cases hsum_t : ∑ j ∈ t, w j = 0
    · have ws : ∀ j ∈ t, w j = 0 := (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t
      have h : i' ∈ t ∨ j' ∈ t := by grind
      exfalso
      rcases h with h | h
      · exact hi'0 (ws _ h)
      · exact hj'0 (ws _ h)
    rw [Finset.centerMass_insert _ _ _ hi hsum_t]
    by_cases hi : w i = 0
    · simp only [hi, zero_add, zero_div, zero_smul, ne_eq, hsum_t, not_false_eq_true, div_self,
        one_smul]
      grind
    by_cases hzi : z i = t.centerMass w z
    · have hwi : w i + ∑ j ∈ t, w j ≠ 0 := by
        refine LT.lt.ne' ?_
        have hwi : 0 < w i := by grind
        grw [← hwi, ← sum_nonneg hs₀, add_zero]
      simp only [hzi, ← add_smul, ← add_div, ne_eq, hwi, not_false_eq_true, div_self, one_smul]
      by_cases! hijt : ∃ i'' j'', i'' ∈ t ∧ j'' ∈ t ∧ z i'' ≠ z j'' ∧ w i'' ≠ 0 ∧ w j'' ≠ 0
      · grind
      · exfalso
        obtain ⟨i'', hi'', hwi''⟩ : ∃ i'' ∈ t, w i'' ≠ 0 := by grind
        have hijt' : ∀ j'', j'' ∈ t → w j'' ≠ 0 → z j'' = Function.const _ (z i'') j'' := by
          grind
        have hi : i = i' ∨ i = j' := by grind
        have hzi'' : t.centerMass w z = z i'' := by
          rw [t.centerMass_congr_fun hijt', t.centerMass_const hsum_t]
        grind
    · exact strictConvex_iff_div.1 hs zi
        (hs.convex.centerMass_mem hs₀ (lt_of_le_of_ne (sum_nonneg hs₀) (Ne.symm hsum_t))
          (fun j hj ↦ hmem j (mem_insert_of_mem hj))) hzi (by grind)
        ((sum_nonneg hs₀).lt_of_ne' hsum_t)
/-
**StrictConvex.sum_mem_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictConvex.sum_mem_interior {s : Set V} {t : Finset ι} {w : ι -> R} {z :
 ι -> V} (hs : StrictConvex R s) (h0 : forall i in t, 0 <= w i) (h1 : ∑ i in t, 
w i = 1) {i j : ι} (hi : i in t) (hj : j in t) (hij : z i != z j) (hi0 : w i != 
0) (hj0 : w j != 0) (hz : forall i in t, z i in s) : ∑ k in t, w k • z k in inte
rior s
参数：hs : StrictConvex R s；h0 : forall i in t, 0 <= w i；h1 : ∑ i in t, w i = 1；hi 
: i in t；hj : j in t；hij : z i != z j；hi0 : w i != 0；hj0 : w j != 0；hz : forall 
i in t, z i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.centerMass_eq_of_sum_1`：Finset.centerMass_eq_of_sum_1 (hw : ∑ i i
n t, w i = 1) : t.centerMass w z = ∑ i in t, w i • z i
· 使用引理 `StrictConvex.centerMass_mem_interior`：StrictConvex.centerMass_mem_interi
or {s : Set V} {t : Finset ι} {w : ι -> R} {z : ι -> V} (hs : StrictConvex R s) 
: (forall i in t, 0 <= w i…
-/
lemma StrictConvex.sum_mem_interior {s : Set V} {t : Finset ι} {w : ι → R} {z : ι → V}
    (hs : StrictConvex R s) (h0 : ∀ i ∈ t, 0 ≤ w i) (h1 : ∑ i ∈ t, w i = 1) {i j : ι}
    (hi : i ∈ t) (hj : j ∈ t) (hij : z i ≠ z j) (hi0 : w i ≠ 0) (hj0 : w j ≠ 0)
    (hz : ∀ i ∈ t, z i ∈ s) : ∑ k ∈ t, w k • z k ∈ interior s := by
  rw [← t.centerMass_eq_of_sum_1 _ h1]
  exact hs.centerMass_mem_interior h0 i j hi hj hij hi0 hj0 hz

end Set

section Space

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [StrictConvexSpace ℝ V]

/-
**centerMass_mem_ball_of_strictConvexSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：centerMass_mem_ball_of_strictConvexSpace {t : Finset ι} {w : ι -> Real} {p
 : V} {r : Real} {z : ι -> V} (h0 : forall i in t, 0 <= w i) {i j : ι} (hi : i i
n t) (hj : j in t) (hij : z i != z j) (hi0 : w i != 0) (hj0 : w j != 0) (hz : fo
rall i in t, z i in closedBall p r) : t.centerMass w z in ball p r
参数：h0 : forall i in t, 0 <= w i；hi : i in t；hj : j in t；hij : z i != z j；hi0 : w
 i != 0；hj0 : w j != 0；hz : forall i in t, z i in closedBall p r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.ball_zero`：ball_zero : ball x 0 = ∅
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Metric.closedBall_zero`：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, M
etric.closedBall x 0 = {x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `interior_closedBall`：interior_closedBall (x : E) {r : Real} (hr : r != 0
) : interior (closedBall x r) = ball x r
· 使用引理 `StrictConvex.centerMass_mem_interior`：StrictConvex.centerMass_mem_interi
or {s : Set V} {t : Finset ι} {w : ι -> R} {z : ι -> V} (hs : StrictConvex R s) 
: (forall i in t, 0 <= w i…
· 使用定理 `strictConvex_closedBall`：strictConvex_closedBall [StrictConvexSpace 𝕜 E]
 (x : E) (r : Real) : StrictConvex 𝕜 (closedBall x r)
-/
lemma centerMass_mem_ball_of_strictConvexSpace {t : Finset ι} {w : ι → ℝ} {p : V} {r : ℝ}
    {z : ι → V} (h0 : ∀ i ∈ t, 0 ≤ w i) {i j : ι} (hi : i ∈ t) (hj : j ∈ t) (hij : z i ≠ z j)
    (hi0 : w i ≠ 0) (hj0 : w j ≠ 0) (hz : ∀ i ∈ t, z i ∈ closedBall p r) :
    t.centerMass w z ∈ ball p r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp_all
  · rw [← interior_closedBall _ hr]
    exact (strictConvex_closedBall _ _ _).centerMass_mem_interior h0 i j hi hj hij hi0 hj0 hz
/-
**sum_mem_ball_of_strictConvexSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sum_mem_ball_of_strictConvexSpace {t : Finset ι} {w : ι -> Real} {p : V} {
r : Real} {z : ι -> V} (h0 : forall i in t, 0 <= w i) (h1 : ∑ i in t, w i = 1) {
i j : ι} (hi : i in t) (hj : j in t) (hij : z i != z j) (hi0 : w i != 0) (hj0 : 
w j != 0) (hz : forall i in t, z i in closedBall p r) : ∑ k in t, w k • z k in b
all p r
参数：h0 : forall i in t, 0 <= w i；h1 : ∑ i in t, w i = 1；hi : i in t；hj : j in t；h
ij : z i != z j；hi0 : w i != 0；hj0 : w j != 0；hz : forall i in t, z i in closedB
all p r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.centerMass_eq_of_sum_1`：Finset.centerMass_eq_of_sum_1 (hw : ∑ i i
n t, w i = 1) : t.centerMass w z = ∑ i in t, w i • z i
· 使用引理 `centerMass_mem_ball_of_strictConvexSpace`：centerMass_mem_ball_of_strictC
onvexSpace {t : Finset ι} {w : ι -> Real} {p : V} {r : Real} {z : ι -> V} (h0 : 
forall i in t, 0 <= w i) {i j …
-/
lemma sum_mem_ball_of_strictConvexSpace {t : Finset ι} {w : ι → ℝ} {p : V} {r : ℝ} {z : ι → V}
    (h0 : ∀ i ∈ t, 0 ≤ w i) (h1 : ∑ i ∈ t, w i = 1) {i j : ι} (hi : i ∈ t) (hj : j ∈ t)
    (hij : z i ≠ z j) (hi0 : w i ≠ 0) (hj0 : w j ≠ 0) (hz : ∀ i ∈ t, z i ∈ closedBall p r) :
    ∑ k ∈ t, w k • z k ∈ ball p r := by
  rw [← t.centerMass_eq_of_sum_1 _ h1]
  exact centerMass_mem_ball_of_strictConvexSpace h0 hi hj hij hi0 hj0 hz
/-
**norm_sum_lt_of_strictConvexSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_sum_lt_of_strictConvexSpace {t : Finset ι} {w : ι -> Real} {r : Real}
 {z : ι -> V} (h0 : forall i in t, 0 <= w i) (h1 : ∑ i in t, w i = 1) {i j : ι} 
(hi : i in t) (hj : j in t) (hij : z i != z j) (hi0 : w i != 0) (hj0 : w j != 0)
 (hz : forall i in t, ‖z i‖ <= r) : ‖∑ k in t, w k • z k‖ < r
参数：h0 : forall i in t, 0 <= w i；h1 : ∑ i in t, w i = 1；hi : i in t；hj : j in t；h
ij : z i != z j；hi0 : w i != 0；hj0 : w j != 0；hz : forall i in t, ‖z i‖ <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r
· 使用引理 `sum_mem_ball_of_strictConvexSpace`：sum_mem_ball_of_strictConvexSpace {t 
: Finset ι} {w : ι -> Real} {p : V} {r : Real} {z : ι -> V} (h0 : forall i in t,
 0 <= w i) (h1 : ∑ i in…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma norm_sum_lt_of_strictConvexSpace {t : Finset ι} {w : ι → ℝ} {r : ℝ} {z : ι → V}
    (h0 : ∀ i ∈ t, 0 ≤ w i) (h1 : ∑ i ∈ t, w i = 1) {i j : ι} (hi : i ∈ t) (hj : j ∈ t)
    (hij : z i ≠ z j) (hi0 : w i ≠ 0) (hj0 : w j ≠ 0) (hz : ∀ i ∈ t, ‖z i‖ ≤ r) :
    ‖∑ k ∈ t, w k • z k‖ < r := by
  simp_rw [← mem_closedBall_zero_iff] at hz
  rw [← mem_ball_zero_iff]
  exact sum_mem_ball_of_strictConvexSpace h0 h1 hi hj hij hi0 hj0 hz

variable [PseudoMetricSpace P] [NormedAddTorsor V P]
/-
**dist_affineCombination_lt_of_strictConvexSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_affineCombination_lt_of_strictConvexSpace {t : Finset ι} {w : ι -> Re
al} {p₀ : P} {r : Real} {p : ι -> P} (h0 : forall i in t, 0 <= w i) (h1 : ∑ i in
 t, w i = 1) {i j : ι} (hi : i in t) (hj : j in t) (hij : p i != p j) (hi0 : w i
 != 0) (hj0 : w j != 0) (hp : forall i in t, dist (p i) p₀ <= r) : dist (t.affin
eCombination Real p w) p₀ < r
参数：h0 : forall i in t, 0 <= w i；h1 : ∑ i in t, w i = 1；hi : i in t；hj : j in t；h
ij : p i != p j；hi0 : w i != 0；hj0 : w j != 0；hp : forall i in t, dist (p i) p₀ 
<= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one`：affi
neCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι -> k) (p : ι -> P
) (h : ∑ i in s, w i = 1) (b : P) : s.affineCombination …
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `dist_vadd_left`：dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ‖v‖
· 使用引理 `norm_sum_lt_of_strictConvexSpace`：norm_sum_lt_of_strictConvexSpace {t : 
Finset ι} {w : ι -> Real} {r : Real} {z : ι -> V} (h0 : forall i in t, 0 <= w i)
 (h1 : ∑ i in t, w i =…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
-/
lemma dist_affineCombination_lt_of_strictConvexSpace {t : Finset ι} {w : ι → ℝ} {p₀ : P} {r : ℝ}
    {p : ι → P} (h0 : ∀ i ∈ t, 0 ≤ w i) (h1 : ∑ i ∈ t, w i = 1) {i j : ι} (hi : i ∈ t)
    (hj : j ∈ t) (hij : p i ≠ p j) (hi0 : w i ≠ 0) (hj0 : w j ≠ 0)
    (hp : ∀ i ∈ t, dist (p i) p₀ ≤ r) :
    dist (t.affineCombination ℝ p w) p₀ < r := by
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ h1 p₀,
    weightedVSubOfPoint_apply, dist_vadd_left]
  simp_rw [dist_eq_norm_vsub] at hp
  exact norm_sum_lt_of_strictConvexSpace h0 h1 hi hj (by simpa using hij) hi0 hj0 hp

namespace Affine

namespace Simplex

/-
**Affine.Simplex.dist_lt_of_mem_closedInterior_of_strictConvexSpace** 是 Mathlib 
中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：dist_lt_of_mem_closedInterior_of_strictConvexSpace {n : Nat} (s : Simplex 
Real P n) {r : Real} {p₀ p : P} (hp : p in s.closedInterior) (hp' : forall i, p 
!= s.points i) (hr : forall i, dist (s.points i) p₀ <= r) : dist p p₀ < r
参数：s : Simplex Real P n；hp : p in s.closedInterior；hp' : forall i, p != s.points
 i；hr : forall i, dist (s.points i) p₀ <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用引理 `dist_affineCombination_lt_of_strictConvexSpace`：dist_affineCombination_l
t_of_strictConvexSpace {t : Finset ι} {w : ι -> Real} {p₀ : P} {r : Real} {p : ι
 -> P} (h0 : forall i in t, 0 <= w i…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
-/
lemma dist_lt_of_mem_closedInterior_of_strictConvexSpace {n : ℕ} (s : Simplex ℝ P n) {r : ℝ}
    {p₀ p : P} (hp : p ∈ s.closedInterior) (hp' : ∀ i, p ≠ s.points i)
    (hr : ∀ i, dist (s.points i) p₀ ≤ r) : dist p p₀ < r := by
  rcases hp with ⟨w, hw, hw01, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! hij
    simp_all
  obtain ⟨j, hij, hj⟩ : ∃ j, i ≠ j ∧ w j ≠ 0 := by
    by_contra! hij
    apply hp' i
    rw [← Finset.univ.affineCombination_piSingle ℝ s.points (Finset.mem_univ i)]
    congr 1
    ext j
    obtain rfl | hj := eq_or_ne i j
    · simp only [Pi.single_eq_same]
      rw [← hw, eq_comm]
      exact sum_eq_single i (fun k _ hk ↦ hij k hk.symm) (by simp)
    · rw [Pi.single_eq_of_ne' hj]
      exact hij j hj
  exact dist_affineCombination_lt_of_strictConvexSpace (fun k _ ↦ (hw01 k).1) hw
    (Finset.mem_univ i) (Finset.mem_univ j) (s.independent.injective.ne hij) hi hj (fun k _ ↦ hr k)
/-
**Affine.Simplex.dist_lt_of_mem_interior_of_strictConvexSpace** 是 Mathlib 中的一个引理
，位于命名空间 `Affine.Simplex`。
形式化陈述：dist_lt_of_mem_interior_of_strictConvexSpace {n : Nat} (s : Simplex Real P
 n) {r : Real} {p₀ p : P} (hp : p in s.interior) (hr : forall i, dist (s.points 
i) p₀ <= r) : dist p p₀ < r
参数：s : Simplex Real P n；hp : p in s.interior；hr : forall i, dist (s.points i) p₀
 <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.dist_lt_of_mem_closedInterior_of_strictConvexSpace`：dist_
lt_of_mem_closedInterior_of_strictConvexSpace {n : Nat} (s : Simplex Real P n) {
r : Real} {p₀ p : P} (hp : p in s.closedInterior) (hp' …
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用引理 `Affine.Simplex.interior_subset_closedInterior`：interior_subset_closedInt
erior {n : Nat} (s : Simplex k P n) : s.interior subseteq s.closedInterior
· 使用引理 `Affine.Simplex.point_notMem_interior`：point_notMem_interior {n : Nat} (s
 : Simplex k P n) (i : Fin (n + 1)) : s.points i ∉ s.interior
-/
lemma dist_lt_of_mem_interior_of_strictConvexSpace {n : ℕ} (s : Simplex ℝ P n) {r : ℝ}
    {p₀ p : P} (hp : p ∈ s.interior) (hr : ∀ i, dist (s.points i) p₀ ≤ r) : dist p p₀ < r :=
  s.dist_lt_of_mem_closedInterior_of_strictConvexSpace
    (Set.mem_of_mem_of_subset hp s.interior_subset_closedInterior)
    (fun i h ↦ s.point_notMem_interior i (h ▸ hp)) hr

end Simplex

end Affine

end Space

