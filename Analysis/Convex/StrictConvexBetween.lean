/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Betweenness in affine spaces for strictly convex spaces

This file proves results about betweenness for points in an affine space for a strictly convex
space.

-/

@[expose] public section

open Metric
open scoped Convex

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [StrictConvexSpace ℝ V]

section PseudoMetricSpace
variable [PseudoMetricSpace P] [NormedAddTorsor V P]

/-
**Sbtw.dist_lt_max_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sbtw.dist_lt_max_dist (p : P) {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃) : di
st p₂ p < max (dist p₁ p) (dist p₃ p)
参数：p : P；h : Sbtw Real p₁ p₂ p₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sbtw.left_ne_right`：Sbtw.left_ne_right {x y z : P} (h : Sbtw R x y z) : 
x != z
· 使用定理 `Set.mem_insert_iff`：mem_insert_iff {x a : α} {s : Set α} : x in insert a
 s ↔ x = a ∨ x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `insert_endpoints_openSegment`：insert_endpoints_openSegment (x y : E) : i
nsert x (insert y (openSegment 𝕜 x y)) = [x -[𝕜] y]
· 使用定理 `affineSegment_eq_segment`：affineSegment_eq_segment (x y : V) : affineSeg
ment R x y = segment R x y
· 使用定理 `Wbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `wbtw_vsub_const_iff`：wbtw_vsub_const_iff {x y z : P} (p : P) : Wbtw R (x
 -ᵥ p) (y -ᵥ p) (z -ᵥ p) ↔ Wbtw R x y z
· 使用定理 `Sbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用定理 `vsub_left_cancel_iff`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] {p₁ p₂ p : P}, p₁ -ᵥ p = p₂ -ᵥ p ↔ p₁ = p₂
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `openSegment_eq_image`：openSegment_eq_image (x y : E) : openSegment 𝕜 x y
 = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Ioo (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_combo_lt_of_ne`：norm_combo_lt_of_ne (hx : ‖x‖ <= r) (hy : ‖y‖ <= r)
 (hne : x != y) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : ‖a • x + b • y‖ < 
r
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `_private.Mathlib.Analysis.Convex.StrictConvexBetween.0.Sbtw.dist_lt_max_
dist._abel_1_1`：∀ (r : ℝ), 1 - r + r = 1
-/
theorem Sbtw.dist_lt_max_dist (p : P) {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) :
    dist p₂ p < max (dist p₁ p) (dist p₃ p) := by
  have hp₁p₃ : p₁ -ᵥ p ≠ p₃ -ᵥ p := by simpa using h.left_ne_right
  rw [Sbtw, ← wbtw_vsub_const_iff p, Wbtw, affineSegment_eq_segment, ← insert_endpoints_openSegment,
    Set.mem_insert_iff, Set.mem_insert_iff] at h
  rcases h with ⟨h | h | h, hp₂p₁, hp₂p₃⟩
  · rw [vsub_left_cancel_iff] at h
    exact False.elim (hp₂p₁ h)
  · rw [vsub_left_cancel_iff] at h
    exact False.elim (hp₂p₃ h)
  · rw [openSegment_eq_image, Set.mem_image] at h
    rcases h with ⟨r, ⟨hr0, hr1⟩, hr⟩
    simp_rw [@dist_eq_norm_vsub V, ← hr]
    exact
      norm_combo_lt_of_ne (le_max_left _ _) (le_max_right _ _) hp₁p₃ (sub_pos.2 hr1) hr0 (by abel)
/-
**Wbtw.dist_le_max_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Wbtw.dist_le_max_dist (p : P) {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃) : di
st p₂ p <= max (dist p₁ p) (dist p₃ p)
参数：p : P；h : Wbtw Real p₁ p₂ p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Sbtw.dist_lt_max_dist`：Sbtw.dist_lt_max_dist (p : P) {p₁ p₂ p₃ : P} (h :
 Sbtw Real p₁ p₂ p₃) : dist p₂ p < max (dist p₁ p) (dist p₃ p)
-/
theorem Wbtw.dist_le_max_dist (p : P) {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) :
    dist p₂ p ≤ max (dist p₁ p) (dist p₃ p) := by
  by_cases hp₁ : p₂ = p₁; · simp [hp₁]
  by_cases hp₃ : p₂ = p₃; · simp [hp₃]
  have hs : Sbtw ℝ p₁ p₂ p₃ := ⟨h, hp₁, hp₃⟩
  exact (hs.dist_lt_max_dist _).le

/-- Given three collinear points, two (not equal) with distance `r` from `p` and one with
distance at most `r` from `p`, the third point is weakly between the other two points. -/
/-
**Collinear.wbtw_of_dist_eq_of_dist_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Collinear.wbtw_of_dist_eq_of_dist_le {p p₁ p₂ p₃ : P} {r : Real} (h : Coll
inear Real ({p₁, p₂, p₃} : Set P)) (hp₁ : dist p₁ p = r) (hp₂ : dist p₂ p <= r) 
(hp₃ : dist p₃ p = r) (hp₁p₃ : p₁ != p₃) : Wbtw Real p₁ p₂ p₃
参数：h : Collinear Real ({p₁, p₂, p₃} : Set P)；hp₁ : dist p₁ p = r；hp₂ : dist p₂ p
 <= r；hp₃ : dist p₃ p = r；hp₁p₃ : p₁ != p₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Collinear.wbtw_or_wbtw_or_wbtw`：Collinear.wbtw_or_wbtw_or_wbtw {x y z : 
P} (h : Collinear R ({x, y, z} : Set P)) : Wbtw R x y z ∨ Wbtw R y z x ∨ Wbtw R 
z x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Sbtw.dist_lt_max_dist`：Sbtw.dist_lt_max_dist (p : P) {p₁ p₂ p₃ : P} (h :
 Sbtw Real p₁ p₂ p₃) : dist p₂ p < max (dist p₁ p) (dist p₃ p)
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `lt_self_iff_false`：lt_self_iff_false (x : α) : x < x ↔ False
· 使用定理 `lt_max_iff`：lt_max_iff : a < max b c ↔ a < b ∨ a < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p

--- 原说明 ---
Given three collinear points, two (not equal) with distance `r` from `p` and one
 with
distance at most `r` from `p`, the third point is weakly between the other two p
oints.
-/
theorem Collinear.wbtw_of_dist_eq_of_dist_le {p p₁ p₂ p₃ : P} {r : ℝ}
    (h : Collinear ℝ ({p₁, p₂, p₃} : Set P)) (hp₁ : dist p₁ p = r) (hp₂ : dist p₂ p ≤ r)
    (hp₃ : dist p₃ p = r) (hp₁p₃ : p₁ ≠ p₃) : Wbtw ℝ p₁ p₂ p₃ := by
  rcases h.wbtw_or_wbtw_or_wbtw with (hw | hw | hw)
  · exact hw
  · by_cases hp₃p₂ : p₃ = p₂
    · simp [hp₃p₂]
    have hs : Sbtw ℝ p₂ p₃ p₁ := ⟨hw, hp₃p₂, hp₁p₃.symm⟩
    have hs' := hs.dist_lt_max_dist p
    rw [hp₁, hp₃, lt_max_iff, lt_self_iff_false, or_false] at hs'
    exact False.elim (hp₂.not_gt hs')
  · by_cases hp₁p₂ : p₁ = p₂
    · simp [hp₁p₂]
    have hs : Sbtw ℝ p₃ p₁ p₂ := ⟨hw, hp₁p₃, hp₁p₂⟩
    have hs' := hs.dist_lt_max_dist p
    rw [hp₁, hp₃, lt_max_iff, lt_self_iff_false, false_or] at hs'
    exact False.elim (hp₂.not_gt hs')

/-- Given three collinear points, two (not equal) with distance `r` from `p` and one with
distance less than `r` from `p`, the third point is strictly between the other two points. -/
/-
**Collinear.sbtw_of_dist_eq_of_dist_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Collinear.sbtw_of_dist_eq_of_dist_lt {p p₁ p₂ p₃ : P} {r : Real} (h : Coll
inear Real ({p₁, p₂, p₃} : Set P)) (hp₁ : dist p₁ p = r) (hp₂ : dist p₂ p < r) (
hp₃ : dist p₃ p = r) (hp₁p₃ : p₁ != p₃) : Sbtw Real p₁ p₂ p₃
参数：h : Collinear Real ({p₁, p₂, p₃} : Set P)；hp₁ : dist p₁ p = r；hp₂ : dist p₂ p
 < r；hp₃ : dist p₃ p = r；hp₁p₃ : p₁ != p₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Collinear.wbtw_of_dist_eq_of_dist_le`：Collinear.wbtw_of_dist_eq_of_dist_
le {p p₁ p₂ p₃ : P} {r : Real} (h : Collinear Real ({p₁, p₂, p₃} : Set P)) (hp₁ 
: dist p₁ p = r) (hp₂ : di…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b

--- 原说明 ---
Given three collinear points, two (not equal) with distance `r` from `p` and one
 with
distance less than `r` from `p`, the third point is strictly between the other t
wo points.
-/
theorem Collinear.sbtw_of_dist_eq_of_dist_lt {p p₁ p₂ p₃ : P} {r : ℝ}
    (h : Collinear ℝ ({p₁, p₂, p₃} : Set P)) (hp₁ : dist p₁ p = r) (hp₂ : dist p₂ p < r)
    (hp₃ : dist p₃ p = r) (hp₁p₃ : p₁ ≠ p₃) : Sbtw ℝ p₁ p₂ p₃ := by
  refine ⟨h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂.le hp₃ hp₁p₃, ?_, ?_⟩
  · rintro rfl
    exact hp₂.ne hp₁
  · rintro rfl
    exact hp₂.ne hp₃

end PseudoMetricSpace

section MetricSpace
variable [MetricSpace P] [NormedAddTorsor V P] {a b c : P}

/-- In a strictly convex space, the triangle inequality turns into an equality if and only if the
middle point belongs to the segment joining two other points. -/
/-
**dist_add_dist_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_add_dist_eq_iff : dist a b + dist b c = dist a c ↔ Wbtw Real a b c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm'`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b :
 E), dist a b = ‖b - a‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_add_sub_cancel'`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G
), a - b + (c - a) = c - b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `vsub_left_injective`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p : P), Function.Injective fun x => x -ᵥ p
· 使用定理 `dist_vsub_cancel_right`：dist_vsub_cancel_right (x y z : P) : dist (x -ᵥ 
z) (y -ᵥ z) = dist x y

--- 原说明 ---
In a strictly convex space, the triangle inequality turns into an equality if an
d only if the
middle point belongs to the segment joining two other points.
-/
lemma dist_add_dist_eq_iff : dist a b + dist b c = dist a c ↔ Wbtw ℝ a b c := by
  have :
      dist (a -ᵥ a) (b -ᵥ a) + dist (b -ᵥ a) (c -ᵥ a) = dist (a -ᵥ a) (c -ᵥ a) ↔
        b -ᵥ a ∈ segment ℝ (a -ᵥ a) (c -ᵥ a) := by
    simp only [mem_segment_iff_sameRay, sameRay_iff_norm_add, dist_eq_norm', sub_add_sub_cancel',
      eq_comm]
  simp_rw [dist_vsub_cancel_right, ← affineSegment_eq_segment, ← affineSegment_vsub_const_image]
    at this
  rwa [(vsub_left_injective _).mem_set_image] at this

/-- The strict triangle inequality. -/
/-
**dist_lt_dist_add_dist_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_lt_dist_add_dist_iff {a b c : P} : dist a c < dist a b + dist b c ↔ ¬
 Wbtw Real a b c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ne_iff_lt_iff_le`：ne_iff_lt_iff_le : (a != b ↔ a < b) ↔ a <= b
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `dist_add_dist_eq_iff`：dist_add_dist_eq_iff : dist a b + dist b c = dist 
a c ↔ Wbtw Real a b c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The strict triangle inequality.
-/
theorem dist_lt_dist_add_dist_iff {a b c : P} :
    dist a c < dist a b + dist b c ↔ ¬ Wbtw ℝ a b c := by
  rw [← ne_iff_lt_iff_le.mpr (dist_triangle _ _ _), not_iff_not, eq_comm, dist_add_dist_eq_iff]

end MetricSpace

variable {E F PE PF : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E]
  [NormedSpace ℝ F] [StrictConvexSpace ℝ E] [MetricSpace PE] [MetricSpace PF] [NormedAddTorsor E PE]
  [NormedAddTorsor F PF] {r : ℝ} {f : PF → PE} {x y z : PE}

set_option backward.isDefEq.respectTransparency false in
/-
**eq_lineMap_of_dist_eq_mul_of_dist_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_lineMap_of_dist_eq_mul_of_dist_eq_mul (hxy : dist x y = r * dist x z) (
hyz : dist y z = (1 - r) * dist x z) : y = AffineMap.lineMap x z r
参数：hxy : dist x y = r * dist x z；hyz : dist y z = (1 - r) * dist x z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mem_segment_iff_wbtw`：mem_segment_iff_wbtw {x y z : V} : y in segment R 
x z ↔ Wbtw R x y z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `dist_add_dist_eq_iff`：dist_add_dist_eq_iff : dist a b + dist b c = dist 
a c ↔ Wbtw Real a b c
· 使用定理 `dist_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], dist 0 = norm
· 使用定理 `dist_vsub_cancel_right`：dist_vsub_cancel_right (x y z : P) : dist (x -ᵥ 
z) (y -ᵥ z) = dist x y
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineMap.lineMap_same`：lineMap_same (p : P1) : lineMap p p = const k k 
p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `segment_same`：segment_same (x : E) : [x -[𝕜] x] = {x}
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `dist_ne_zero`：dist_ne_zero {x y : γ} : dist x y != 0 ↔ x != y
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
（共 32 条，此处仅展示前 30 条）
-/
lemma eq_lineMap_of_dist_eq_mul_of_dist_eq_mul (hxy : dist x y = r * dist x z)
    (hyz : dist y z = (1 - r) * dist x z) : y = AffineMap.lineMap x z r := by
  have : y -ᵥ x ∈ [(0 : E) -[ℝ] z -ᵥ x] := by
    rw [mem_segment_iff_wbtw, ← dist_add_dist_eq_iff, dist_zero, dist_vsub_cancel_right,
      ← dist_eq_norm_vsub', ← dist_eq_norm_vsub', hxy, hyz, ← add_mul, add_sub_cancel,
      one_mul]
  obtain rfl | hne := eq_or_ne x z
  · obtain rfl : y = x := by simpa
    simp
  · rw [← dist_ne_zero] at hne
    obtain ⟨a, b, _, hb, _, H⟩ := this
    rw [smul_zero, zero_add] at H
    have H' := congr_arg norm H
    rw [norm_smul, Real.norm_of_nonneg hb, ← dist_eq_norm_vsub', ← dist_eq_norm_vsub', hxy,
      mul_left_inj' hne] at H'
    rw [AffineMap.lineMap_apply, ← H', H, vsub_vadd]
/-
**eq_midpoint_of_dist_eq_half** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_midpoint_of_dist_eq_half (hx : dist x y = dist x z / 2) (hy : dist y z 
= dist x z / 2) : y = midpoint Real x z
参数：hx : dist x y = dist x z / 2；hy : dist y z = dist x z / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `eq_lineMap_of_dist_eq_mul_of_dist_eq_mul`：eq_lineMap_of_dist_eq_mul_of_d
ist_eq_mul (hxy : dist x y = r * dist x z) (hyz : dist y z = (1 - r) * dist x z)
 : y = AffineMap.lineMap x z r
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `sub_half`：sub_half (a : K) : a - a / 2 = a / 2
-/
lemma eq_midpoint_of_dist_eq_half (hx : dist x y = dist x z / 2) (hy : dist y z = dist x z / 2) :
    y = midpoint ℝ x z := by
  apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
  · rwa [invOf_eq_inv, ← div_eq_inv_mul]
  · rwa [invOf_eq_inv, ← one_div, sub_half, one_div, ← div_eq_inv_mul]

namespace Isometry

/-- An isometry of `NormedAddTorsor`s for real normed spaces, strictly convex in the case of the
codomain, is an affine isometry.  Unlike Mazur-Ulam, this does not require the isometry to be
surjective. -/
/-
**Isometry.affineIsometryOfStrictConvexSpace** 是 Mathlib 中的一个定义，位于命名空间 `Isometry
`。
形式化陈述：affineIsometryOfStrictConvexSpace (hi : Isometry f) : PF ->ᵃⁱ[Real] PE
参数：hi : Isometry f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isometry of `NormedAddTorsor`s for real normed spaces, strictly convex in the
 case of the
codomain, is an affine isometry.  Unlike Mazur-Ulam, this does not require the i
sometry to be
surjective.
-/
noncomputable def affineIsometryOfStrictConvexSpace (hi : Isometry f) : PF →ᵃⁱ[ℝ] PE :=
  { AffineMap.ofMapMidpoint f
      (fun x y => by
        apply eq_midpoint_of_dist_eq_half
        · rw [hi.dist_eq, hi.dist_eq]
          simp only [dist_left_midpoint, Real.norm_of_nonneg zero_le_two, div_eq_inv_mul]
        · rw [hi.dist_eq, hi.dist_eq]
          simp only [dist_midpoint_right, Real.norm_of_nonneg zero_le_two, div_eq_inv_mul])
      hi.continuous with
    norm_map := fun x => by simp [AffineMap.ofMapMidpoint, ← dist_eq_norm_vsub E, hi.dist_eq] }
/-
**Isometry.coe_affineIsometryOfStrictConvexSpace** 是 Mathlib 中的一个定理，位于命名空间 `Isom
etry`。
形式化陈述：∀ {E : Type u_3} {F : Type u_4} {PE : Type u_5} {PF : Type u_6} [inst : No
rmedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ E]
 [inst_3 : NormedSpace ℝ F] [inst_4 : StrictConvexSpace ℝ E]   [inst_5 : MetricS
pace PE] [inst_6 : MetricSpace PF] [inst_7 : NormedAddTorsor E PE] [inst_8 : Nor
medAddTorsor F PF]   {f : PF → PE} (hi : Isometry f), ⇑hi.affineIsometryOfStrict
ConvexSpace = f
参数：hi : Isometry f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_affineIsometryOfStrictConvexSpace (hi : Isometry f) :
    ⇑hi.affineIsometryOfStrictConvexSpace = f := rfl
/-
**Isometry.affineIsometryOfStrictConvexSpace_apply** 是 Mathlib 中的一个定理，位于命名空间 `Is
ometry`。
形式化陈述：∀ {E : Type u_3} {F : Type u_4} {PE : Type u_5} {PF : Type u_6} [inst : No
rmedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ E]
 [inst_3 : NormedSpace ℝ F] [inst_4 : StrictConvexSpace ℝ E]   [inst_5 : MetricS
pace PE] [inst_6 : MetricSpace PF] [inst_7 : NormedAddTorsor E PE] [inst_8 : Nor
medAddTorsor F PF]   {f : PF → PE} (hi : Isometry f) (p : PF), hi.affineIsometry
OfStrictConvexSpace p = f p
参数：hi : Isometry f；p : PF。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma affineIsometryOfStrictConvexSpace_apply (hi : Isometry f) (p : PF) :
    hi.affineIsometryOfStrictConvexSpace p = f p := rfl

end Isometry

