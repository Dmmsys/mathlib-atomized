/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Chu Zheng
-/
module

public import Mathlib.Topology.MetricSpace.Congruence
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Triangle

/-!
# Triangle congruence

This file proves the classical triangle congruence criteria for (possibly degenerate) triangles
in real inner product spaces and Euclidean affine spaces.
We prove SSS, SAS, ASA, and AAS congruence.

## Implementation notes

Side–Side–Side (SSS) congruence is proved using the definition of `Congruent`.
Side–Angle–Side (SAS) congruence is proved via the law of cosines.
Angle–Side–Angle (ASA) congruence is reduced to SAS using the law of sines.
Angle–Angle–Side (AAS) congruence uses the fact that the sum of the angles in a triangle equals π,
then reduces to ASA.

## References

* https://en.wikipedia.org/wiki/Congruence_(geometry)

-/

public section

open scoped Congruent

namespace EuclideanGeometry

variable {ι V₁ V₂ P₁ P₂ : Type*}
  [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
  [InnerProductSpace ℝ V₁] [InnerProductSpace ℝ V₂]
  [MetricSpace P₁] [MetricSpace P₂]
  [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
  {v₁ : ι → P₁} {v₂ : ι → P₂}
  {a b c : P₁} {a' b' c' : P₂}

/-
**EuclideanGeometry.triangle_congruent_iff_dist_eq** 是 Mathlib 中的一个引理，位于命名空间 `Eu
clideanGeometry`。
形式化陈述：triangle_congruent_iff_dist_eq {t₁ : Fin 3 -> P₁} {t₂ : Fin 3 -> P₂} : t₁ 
≅ t₂ ↔ forall (i j : Fin 3), dist (t₁ i) (t₁ j) = dist (t₂ i) (t₂ j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `congruent_iff_dist_eq`：congruent_iff_dist_eq : Congruent v₁ v₂ ↔ forall 
i₁ i₂, dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂)
-/
lemma triangle_congruent_iff_dist_eq {t₁ : Fin 3 → P₁} {t₂ : Fin 3 → P₂} :
    t₁ ≅ t₂ ↔ ∀ (i j : Fin 3), dist (t₁ i) (t₁ j) = dist (t₂ i) (t₂ j) := congruent_iff_dist_eq

/-- **Side–Side–Side (SSS) congruence**
If all three corresponding sides of two triangles are equal, then the triangles are congruent.
This holds even if the triangles are degenerate. -/
/-
**EuclideanGeometry.side_side_side** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`
。
形式化陈述：side_side_side (hd₁ : dist a b = dist a' b') (hd₂ : dist b c = dist b' c')
 (hd₃ : dist c a = dist c' a') : ![a, b, c] ≅ ![a', b', c']
参数：hd₁ : dist a b = dist a' b'；hd₂ : dist b c = dist b' c'；hd₃ : dist c a = dist
 c' a'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.triangle_congruent_iff_dist_eq`：triangle_congruent_iff
_dist_eq {t₁ : Fin 3 -> P₁} {t₂ : Fin 3 -> P₂} : t₁ ≅ t₂ ↔ forall (i j : Fin 3),
 dist (t₁ i) (t₁ j) = dist (t₂ i) (t₂ …
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
**Side–Side–Side (SSS) congruence**
If all three corresponding sides of two triangles are equal, then the triangles 
are congruent.
This holds even if the triangles are degenerate.
-/
theorem side_side_side (hd₁ : dist a b = dist a' b') (hd₂ : dist b c = dist b' c')
    (hd₃ : dist c a = dist c' a') :
    ![a, b, c] ≅ ![a', b', c'] := by
  rw [triangle_congruent_iff_dist_eq]
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [dist_comm]

/-- **Side–Angle–Side (SAS) congruence**
If two triangles have two sides and the included angle equal, then the triangles are congruent.
This holds even if the triangles are degenerate. -/
/-
**EuclideanGeometry.side_angle_side** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
`。
形式化陈述：side_angle_side (h : ∠ a b c = ∠ a' b' c') (hd₁ : dist a b = dist a' b') (
hd₂ : dist b c = dist b' c') : ![a, b, c] ≅ ![a', b', c']
参数：h : ∠ a b c = ∠ a' b' c'；hd₁ : dist a b = dist a' b'；hd₂ : dist b c = dist b'
 c'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.side_side_side`：side_side_side (hd₁ : dist a b = dist 
a' b') (hd₂ : dist b c = dist b' c') (hd₃ : dist c a = dist c' a') : ![a, b, c] 
≅ ![a', b', c']
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.law_cos`：∀ {V : Type u_1} {P : Type u_2} [inst : Norme
dAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [in
st_3 : NormedAd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Side–Angle–Side (SAS) congruence**
If two triangles have two sides and the included angle equal, then the triangles
 are congruent.
This holds even if the triangles are degenerate.
-/
theorem side_angle_side (h : ∠ a b c = ∠ a' b' c') (hd₁ : dist a b = dist a' b')
    (hd₂ : dist b c = dist b' c') : ![a, b, c] ≅ ![a', b', c'] := by
  apply side_side_side hd₁ hd₂
  rw [dist_comm, dist_comm c' a', ← sq_eq_sq₀ (by positivity) (by positivity), pow_two, pow_two,
    EuclideanGeometry.law_cos a b c, EuclideanGeometry.law_cos a' b' c']
  simp [h, hd₁, hd₂, dist_comm]

/-- **Angle–Side–Angle (ASA) congruence**
If two triangles have two equal angles and the included side equal, then the triangles are
congruent. We require that one of the triangles is non-degenerate, the non-collinearity of the
other is then implied by the given equalities.
-/
/-
**EuclideanGeometry.angle_side_angle** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y`。
形式化陈述：angle_side_angle (h : ¬Collinear Real {a, b, c}) (ha₁ : ∠ a b c = ∠ a' b' 
c') (hd : dist b c = dist b' c') (ha₂ : ∠ b c a = ∠ b' c' a') : ![a, b, c] ≅ ![a
', b', c']
参数：h : ¬Collinear Real {a, b, c}；ha₁ : ∠ a b c = ∠ a' b' c'；hd : dist b c = dist
 b' c'；ha₂ : ∠ b c a = ∠ b' c' a'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.angle_add_angle_add_angle_eq_pi`：angle_add_angle_add_a
ngle_eq_pi {p₁ p₂ : P} (p₃ : P) (h : p₂ != p₁) : ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ 
p₁ p₂ = π
· 使用定理 `ne₁₃_of_not_collinear`：ne₁₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collin
ear k ({p₁, p₂, p₃} : Set P)) : p₁ != p₃
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_comm`：insert_comm (a b : α) (s : Set α) : insert a (insert b 
s) = insert b (insert a s)
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle`：dist_eq_dist
_mul_sin_angle_div_sin_angle {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} :
 Set P)) : dist p₁ p₂ = dist p₃ p₁ * Real.sin (∠…
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `EuclideanGeometry.side_angle_side`：side_angle_side (h : ∠ a b c = ∠ a' b
' c') (hd₁ : dist a b = dist a' b') (hd₂ : dist b c = dist b' c') : ![a, b, c] ≅
 ![a', b', c']

--- 原说明 ---
**Angle–Side–Angle (ASA) congruence**
If two triangles have two equal angles and the included side equal, then the tri
angles are
congruent. We require that one of the triangles is non-degenerate, the non-colli
nearity of the
other is then implied by the given equalities.
-/
theorem angle_side_angle (h : ¬Collinear ℝ {a, b, c}) (ha₁ : ∠ a b c = ∠ a' b' c')
    (hd : dist b c = dist b' c') (ha₂ : ∠ b c a = ∠ b' c' a') : ![a, b, c] ≅ ![a', b', c'] := by
  have h' : ¬Collinear ℝ {a', b', c'} := by
    grind only [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, angle_self_right,
      angle_self_left, dist_eq_zero, Set.insert_comm, Set.pair_comm]
  have ha₃ := angle_add_angle_add_angle_eq_pi b (ne₁₃_of_not_collinear h)
  have ha₃' := angle_add_angle_add_angle_eq_pi b' (ne₁₃_of_not_collinear h')
  simp only [← ha₃', ha₁, ha₂, angle_comm b' c' a', add_right_cancel_iff] at ha₃
  have h_bac : ¬Collinear ℝ {b, a, c} := by simpa [Set.insert_comm] using h
  have h_bac' : ¬Collinear ℝ {b', a', c'} := by simpa [Set.insert_comm] using h'
  have dist_ab_eq : dist a b = dist a' b' := by
    rw [dist_comm a b, dist_comm a' b', dist_eq_dist_mul_sin_angle_div_sin_angle h_bac,
      dist_eq_dist_mul_sin_angle_div_sin_angle h_bac', dist_comm c b, dist_comm c' b', hd,
      angle_comm, ha₂, angle_comm b' c' a', angle_comm b a c, ha₃, angle_comm b' a' c']
  exact side_angle_side ha₁ dist_ab_eq hd

/-- **Angle–Angle–Side (AAS) congruence**
If two triangles have two equal angles and a non-included side equal, then the triangles are
congruent. We require that one of the triangles is non-degenerate, the non-collinearity of the
other is then implied by the given equalities. -/
/-
**EuclideanGeometry.angle_angle_side** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y`。
形式化陈述：angle_angle_side (h : ¬Collinear Real {a, b, c}) (ha₁ : ∠ a b c = ∠ a' b' 
c') (ha₂ : ∠ b c a = ∠ b' c' a') (hd : dist c a = dist c' a') : ![a, b, c] ≅ ![a
', b', c']
参数：h : ¬Collinear Real {a, b, c}；ha₁ : ∠ a b c = ∠ a' b' c'；ha₂ : ∠ b c a = ∠ b'
 c' a'；hd : dist c a = dist c' a'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.angle_add_angle_add_angle_eq_pi`：angle_add_angle_add_a
ngle_eq_pi {p₁ p₂ : P} (p₃ : P) (h : p₂ != p₁) : ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ 
p₁ p₂ = π
· 使用定理 `ne₁₃_of_not_collinear`：ne₁₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collin
ear k ({p₁, p₂, p₃} : Set P)) : p₁ != p₃
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用定理 `Set.insert_comm`：insert_comm (a b : α) (s : Set α) : insert a (insert b 
s) = insert b (insert a s)
· 使用定理 `EuclideanGeometry.angle_side_angle`：angle_side_angle (h : ¬Collinear Rea
l {a, b, c}) (ha₁ : ∠ a b c = ∠ a' b' c') (hd : dist b c = dist b' c') (ha₂ : ∠ 
b c a = ∠ b' c' a') : ![…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Congruent.dist_eq`：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {v₁ 
: ι → P₁} {v₂ : ι → P₂} [inst : PseudoMetricSpace P₁]   [inst_1 : PseudoMetricSp
ace P₂]…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
**Angle–Angle–Side (AAS) congruence**
If two triangles have two equal angles and a non-included side equal, then the t
riangles are
congruent. We require that one of the triangles is non-degenerate, the non-colli
nearity of the
other is then implied by the given equalities.
-/
theorem angle_angle_side (h : ¬Collinear ℝ {a, b, c}) (ha₁ : ∠ a b c = ∠ a' b' c')
    (ha₂ : ∠ b c a = ∠ b' c' a') (hd : dist c a = dist c' a') : ![a, b, c] ≅ ![a', b', c'] := by
  have ha₃ := angle_add_angle_add_angle_eq_pi b (ne₁₃_of_not_collinear h)
  have h' : ¬Collinear ℝ {a', b', c'} := by
    grind only [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, angle_self_right,
      angle_self_left, dist_eq_zero, Set.insert_comm, Set.pair_comm]
  have ha₃' := angle_add_angle_add_angle_eq_pi b' (ne₁₃_of_not_collinear h')
  simp only [← ha₃', ha₁, ha₂, angle_comm b' c' a', add_right_cancel_iff] at ha₃
  have h_bca : ¬Collinear ℝ {b, c, a} := by rwa [Set.insert_comm, Set.pair_comm] at h
  have h1 := angle_side_angle h_bca ha₂ hd ha₃
  exact angle_side_angle h ha₁ (h1.dist_eq 0 1) ha₂

include V₁ V₂

/-- Corresponding angles are equal for congruent triangles. -/
/-
**EuclideanGeometry.angle_eq_of_congruent** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGe
ometry`。
形式化陈述：angle_eq_of_congruent (h : v₁ ≅ v₂) (i j k : ι) : ∠ (v₁ i) (v₁ j) (v₁ k) =
 ∠ (v₂ i) (v₂ j) (v₂ k)
参数：h : v₁ ≅ v₂；i j k : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_
two`：real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
 (x y : F) : ⟪x, y⟫_Real = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x …
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Congruent.dist_eq`：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {v₁ 
: ι → P₁} {v₂ : ι → P₂} [inst : PseudoMetricSpace P₁]   [inst_1 : PseudoMetricSp
ace P₂]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Corresponding angles are equal for congruent triangles.
-/
theorem angle_eq_of_congruent (h : v₁ ≅ v₂) (i j k : ι) :
    ∠ (v₁ i) (v₁ j) (v₁ k) = ∠ (v₂ i) (v₂ j) (v₂ k) := by
  unfold EuclideanGeometry.angle
  unfold InnerProductGeometry.angle
  simp_rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub, h.dist_eq]

end EuclideanGeometry

