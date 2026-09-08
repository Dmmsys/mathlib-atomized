/-
Copyright (c) 2025 Chu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chu Zheng
-/
module

public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Topology.MetricSpace.Similarity
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

/-!
# Triangle Similarity

This file contains theorems about similarity of triangles, including conditions
for similarity based on sides and angles.

-/

public section

open scoped Congruent EuclideanGeometry

open Similar NNReal Affine

namespace EuclideanGeometry

variable {ι V₁ V₂ P₁ P₂ : Type*}
  [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
  [InnerProductSpace ℝ V₁] [InnerProductSpace ℝ V₂]
  [MetricSpace P₁] [MetricSpace P₂]
  [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
  {v₁ : ι → P₁} {v₂ : ι → P₂}
  {a b c : P₁} {a' b' c' : P₂}

/-- If two triangles have two pairs equal angles, then the triangles are similar. -/
/-
**EuclideanGeometry.similar_of_angle_angle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanG
eometry`。
形式化陈述：similar_of_angle_angle (h_not_col : ¬ Collinear Real {a, b, c}) (h₁ : ∠ a 
b c = ∠ a' b' c') (h₂ : ∠ b c a = ∠ b' c' a') : ![a, b, c] ∼ ![a', b', c']
参数：h_not_col : ¬ Collinear Real {a, b, c}；h₁ : ∠ a b c = ∠ a' b' c'；h₂ : ∠ b c a
 = ∠ b' c' a'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `EuclideanGeometry.angle_lt_pi_div_two_of_angle_eq_pi_div_two`：angle_lt_p
i_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p
₃ != p₂) : ∠ p₂ p₃ p₁ < π / 2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne₂₃_of_not_collinear`：ne₂₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collin
ear k ({p₁, p₂, p₃} : Set P)) : p₂ != p₃
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ne₁₂_of_not_collinear`：ne₁₂_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collin
ear k ({p₁, p₂, p₃} : Set P)) : p₁ != p₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `EuclideanGeometry.angle_add_angle_add_angle_eq_pi`：angle_add_angle_add_a
ngle_eq_pi {p₁ p₂ : P} (p₃ : P) (h : p₂ != p₁) : ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ 
p₁ p₂ = π
· 使用定理 `EuclideanGeometry.law_sin`：∀ {V : Type u_1} {P : Type u_2} [inst : Norme
dAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [in
st_3 : NormedAd…
· 使用定理 `Similar.reverse_of_three`：reverse_of_three (h : ![a, b, c] ∼ ![a', b', c
']) : ![c, b, a] ∼ ![c', b', a']
· 使用定理 `Similar.comm_left`：comm_left (h : ![a, b, c] ∼ ![a', b', c']) : ![b, a, 
c] ∼ ![b', a', c']
· 使用定理 `similar_of_side_side`：∀ {P₁ : Type u_3} {P₂ : Type u_4} [inst : PseudoMe
tricSpace P₁] [inst_1 : PseudoMetricSpace P₂] {a b c : P₁}   {a' b' c' : P₂},   
dist a b ≠…
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `eq_div_iff_mul_eq`：eq_div_iff_mul_eq (hc : c != 0) : a = b / c ↔ a * c =
 b

--- 原说明 ---
If two triangles have two pairs equal angles, then the triangles are similar.
-/
theorem similar_of_angle_angle (h_not_col : ¬ Collinear ℝ {a, b, c}) (h₁ : ∠ a b c = ∠ a' b' c')
    (h₂ : ∠ b c a = ∠ b' c' a') :
    ![a, b, c] ∼ ![a', b', c'] := by
  have hne_pi_div_two : ∠ a b c ≠ Real.pi / 2 ∨ ∠ b c a ≠ Real.pi / 2 := by
    by_contra! hq
    have := angle_lt_pi_div_two_of_angle_eq_pi_div_two hq.1 (ne₂₃_of_not_collinear h_not_col).symm
    grind
  have not_all_eq : a' ≠ b' ∨ b' ≠ c' ∨ a' ≠ c' := by grind [angle_self_left]
  have h_not_col' : ¬ Collinear ℝ {a', b', c'} := by
    grind only [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, angle_self_right,
      angle_self_left, Set.insert_comm, Set.pair_comm]
  have h_pos1 : 0 < dist a b := by simp [dist_pos, ne₁₂_of_not_collinear h_not_col]
  have h_pos1' : 0 < dist a' b' := by simp [dist_pos, ne₁₂_of_not_collinear h_not_col']
  have h_pos2 : 0 < dist b c := by simp [dist_pos, ne₂₃_of_not_collinear h_not_col]
  have h_pos2' : 0 < dist b' c' := by simp [dist_pos, ne₂₃_of_not_collinear h_not_col']
  have h₃ : ∠ c a b = ∠ c' a' b' := by
    have hsum := angle_add_angle_add_angle_eq_pi c (ne₁₂_of_not_collinear h_not_col)
    have hsum' := angle_add_angle_add_angle_eq_pi c' (ne₁₂_of_not_collinear h_not_col')
    grind [angle_comm]
  have h_sin_ne1 : Real.sin (∠ b c a) ≠ 0 := by
    grind only [sin_ne_zero_of_not_collinear, Set.pair_comm, Set.insert_comm]
  have h_sin_ne2 : Real.sin (∠ c a b) ≠ 0 := by
    grind only [sin_ne_zero_of_not_collinear, Set.pair_comm, Set.insert_comm]
  have h_sin1 := law_sin c a b
  have h_sin1' := law_sin c' a' b'
  rw [← eq_div_iff_mul_eq (by positivity)] at h_sin1 h_sin1'
  rw [← h₃, ← h₂] at h_sin1'
  rw [h_sin1', mul_div_assoc, mul_div_assoc, mul_right_inj' h_sin_ne1,
    div_eq_div_iff (by positivity) (by positivity), mul_comm] at h_sin1
  have h_sin2 := law_sin a b c
  have h_sin2' := law_sin a' b' c'
  rw [← eq_div_iff_mul_eq (by positivity)] at h_sin2 h_sin2'
  rw [← h₁, ← h₃] at h_sin2'
  rw [h_sin2', mul_div_assoc, mul_div_assoc, mul_right_inj' h_sin_ne2,
    div_eq_div_iff (by positivity) (by positivity), mul_comm] at h_sin2
  apply Similar.reverse_of_three
  apply Similar.comm_left
  exact similar_of_side_side (by positivity) (by positivity) h_sin2 h_sin1.symm

/-- If two triangles have proportional adjacent sides and an equal included angle, then the
triangles are similar. -/
/-
**EuclideanGeometry.similar_of_side_angle_side** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
形式化陈述：similar_of_side_angle_side (h_not_col : ¬ Collinear Real {a, b, c}) (h_not
_col' : ¬ Collinear Real {a', b', c'}) (h : ∠ a b c = ∠ a' b' c') (hd : dist a b
 * dist b' c' = dist b c * dist a' b') : ![a, b, c] ∼ ![a', b', c']
参数：h_not_col : ¬ Collinear Real {a, b, c}；h_not_col' : ¬ Collinear Real {a', b',
 c'}；h : ∠ a b c = ∠ a' b' c'；hd : dist a b * dist b' c' = dist b c * dist a' b'
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ne₁₂_of_not_collinear`：ne₁₂_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collin
ear k ({p₁, p₂, p₃} : Set P)) : p₁ != p₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ne₂₃_of_not_collinear`：ne₂₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collin
ear k ({p₁, p₂, p₃} : Set P)) : p₂ != p₃
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.law_cos`：∀ {V : Type u_1} {P : Type u_2} [inst : Norme
dAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [in
st_3 : NormedAd…
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用引理 `similar_iff_exists_pos_pairwise_dist_eq`：similar_iff_exists_pos_pairwise
_dist_eq : Similar v₁ v₂ ↔ (exists r : Real, 0 < r ∧ Pairwise fun i₁ i₂ => (dist
 (v₁ i₁) (v₁ i₂) = r * dist (…
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用引理 `pow_left_inj₀`：pow_left_inj₀ [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b)
 (hn : n != 0) : a ^ n = b ^ n ↔ a = b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
If two triangles have proportional adjacent sides and an equal included angle, t
hen the
triangles are similar.
-/
theorem similar_of_side_angle_side (h_not_col : ¬ Collinear ℝ {a, b, c})
    (h_not_col' : ¬ Collinear ℝ {a', b', c'}) (h : ∠ a b c = ∠ a' b' c')
    (hd : dist a b * dist b' c' = dist b c * dist a' b') :
    ![a, b, c] ∼ ![a', b', c'] := by
  have dist_a'b' : dist a' b' ≠ 0 := by simp [ne₁₂_of_not_collinear h_not_col']
  have dist_b'c' : dist b' c' ≠ 0 := by simp [ne₂₃_of_not_collinear h_not_col']
  rw [← div_eq_div_iff dist_a'b' dist_b'c'] at hd
  set k := (dist a b / dist a' b') with hk
  have k_pos : 0 < k := by
    rw [hk]
    apply div_pos
    · simp [dist_pos, ne₁₂_of_not_collinear h_not_col]
    · simp [dist_pos, ne₁₂_of_not_collinear h_not_col']
  have h_ab : dist a b = k * dist a' b' := by grind
  have h_bc : dist b c = k * dist b' c' := by grind
  have hcos := law_cos a b c
  rw [dist_comm b _, dist_comm b' _] at h_bc
  rw [h_ab, h_bc] at hcos
  field_simp at hcos
  rw [h] at hcos
  have hcos' := law_cos a' b' c'
  field_simp at hcos'
  rw [← hcos', ← mul_pow] at hcos
  have dist_ac_pos : 0 < dist a c := by grind [dist_pos, ne₁₃_of_not_collinear]
  have k_dist_a'c' : 0 ≤ k * dist a' c' := by positivity
  rw [pow_left_inj₀ (le_of_lt dist_ac_pos) k_dist_a'c' (by norm_num), dist_comm a _,
    dist_comm a' _] at hcos
  rw [dist_comm c _, dist_comm c' _] at h_bc
  rw [similar_iff_exists_pos_pairwise_dist_eq]
  use k
  refine ⟨k_pos, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> try {rw [dist_self, dist_self, mul_zero]}
  all_goals simp; grind [dist_comm]

/-- For two similar triangles, the corresponding angles are equal. -/
/-
**EuclideanGeometry._root_.Similar.angle_eq** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean
Geometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For two similar triangles, the corresponding angles are equal.
-/
theorem _root_.Similar.angle_eq (h : ![a, b, c] ∼ ![a', b', c']) :
    ∠ a b c = ∠ a' b' c' := by
  rw [similar_iff_exists_pos_dist_eq] at h
  rcases h with ⟨r, hr_pos, hdist⟩
  have h_ab : dist a b = r * dist a' b' := hdist 0 1
  have h_cb : dist c b = r * dist c' b' := hdist 2 1
  have h_ac : dist a c = r * dist a' c' := hdist 0 2
  have h_cos := law_cos a b c
  rw [h_ab, h_cb, h_ac] at h_cos
  field_simp at h_cos
  have h_cos' := law_cos a' b' c'
  field_simp at h_cos'
  rw [h_cos', sub_right_inj] at h_cos
  by_cases heq : dist a' b' * dist c' b' * 2 = 0
  · rw [mul_eq_zero_iff_right (by norm_num), mul_eq_zero] at heq
    rcases heq with h1 | h2
    · have h_dist_ab : dist a b = 0 := by grind
      rw [dist_eq_zero] at h_dist_ab h1
      simp_rw [h_dist_ab, h1, angle_self_left]
    · have h_dist_cb : dist c b = 0 := by grind
      rw [dist_eq_zero] at h_dist_cb h2
      simp_rw [h_dist_cb, h2, angle_self_right]
  rw [mul_right_inj' heq] at h_cos
  apply Real.injOn_cos at h_cos
  repeat grind [angle_nonneg, angle_le_pi]

/-- In two similar triangles, all three corresponding angles are equal. -/
/-
**EuclideanGeometry._root_.Similar.angle_eq_all** 是 Mathlib 中的一个定理，位于命名空间 `Eucli
deanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In two similar triangles, all three corresponding angles are equal.
-/
theorem _root_.Similar.angle_eq_all (h : ![a, b, c] ∼ ![a', b', c']) :
    ∠ a b c = ∠ a' b' c' ∧ ∠ b c a = ∠ b' c' a' ∧ ∠ c a b = ∠ c' a' b' :=
  ⟨h.angle_eq, h.comm_left.comm_right.angle_eq, h.comm_right.comm_left.angle_eq⟩

end EuclideanGeometry

