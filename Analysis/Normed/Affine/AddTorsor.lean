/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Topology.Instances.RealVectorSpace


/-!
# Torsors of normed space actions.

This file contains lemmas about normed additive torsors over normed spaces.
-/

@[expose] public section


noncomputable section

open NNReal Topology

open Filter

variable {V P W Q : Type*} [SeminormedAddCommGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]
  [NormedAddCommGroup W] [MetricSpace Q] [NormedAddTorsor W Q]

section NormedSpace

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]

open AffineMap

@[simp]
/-
**dist_center_homothety** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_center_homothety (p₁ p₂ : P) (c : 𝕜) : dist p₁ (homothety p₁ c p₂) = 
‖c‖ * dist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_vadd_right`：dist_vadd_right (v : V) (x : P) : dist x (v +ᵥ x) = ‖v‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_center_homothety (p₁ p₂ : P) (c : 𝕜) :
    dist p₁ (homothety p₁ c p₂) = ‖c‖ * dist p₁ p₂ := by
  simp [homothety_def, norm_smul, ← dist_eq_norm_vsub, dist_comm]

@[simp]
/-
**nndist_center_homothety** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_center_homothety (p₁ p₂ : P) (c : 𝕜) : nndist p₁ (homothety p₁ c p₂
) = ‖c‖₊ * nndist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_center_homothety`：dist_center_homothety (p₁ p₂ : P) (c : 𝕜) : dist 
p₁ (homothety p₁ c p₂) = ‖c‖ * dist p₁ p₂
-/
theorem nndist_center_homothety (p₁ p₂ : P) (c : 𝕜) :
    nndist p₁ (homothety p₁ c p₂) = ‖c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_center_homothety _ _ _

@[simp]
/-
**dist_homothety_center** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_homothety_center (p₁ p₂ : P) (c : 𝕜) : dist (homothety p₁ c p₂) p₁ = 
‖c‖ * dist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_center_homothety`：dist_center_homothety (p₁ p₂ : P) (c : 𝕜) : dist 
p₁ (homothety p₁ c p₂) = ‖c‖ * dist p₁ p₂
-/
theorem dist_homothety_center (p₁ p₂ : P) (c : 𝕜) :
    dist (homothety p₁ c p₂) p₁ = ‖c‖ * dist p₁ p₂ := by rw [dist_comm, dist_center_homothety]

@[simp]
/-
**nndist_homothety_center** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_homothety_center (p₁ p₂ : P) (c : 𝕜) : nndist (homothety p₁ c p₂) p
₁ = ‖c‖₊ * nndist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_homothety_center`：dist_homothety_center (p₁ p₂ : P) (c : 𝕜) : dist 
(homothety p₁ c p₂) p₁ = ‖c‖ * dist p₁ p₂
-/
theorem nndist_homothety_center (p₁ p₂ : P) (c : 𝕜) :
    nndist (homothety p₁ c p₂) p₁ = ‖c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_homothety_center _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**dist_lineMap_lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_lineMap_lineMap (p₁ p₂ : P) (c₁ c₂ : 𝕜) : dist (lineMap p₁ p₂ c₁) (li
neMap p₁ p₂ c₂) = dist c₁ c₂ * dist p₁ p₂
参数：p₁ p₂ : P；c₁ c₂ : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `vadd_vsub_vadd_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : Add
Group G] [T : AddTorsor G P] (v₁ v₂ : G) (p : P),   (v₁ +ᵥ p) -ᵥ (v₂ +ᵥ p) = v₁ 
- v₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_lineMap_lineMap (p₁ p₂ : P) (c₁ c₂ : 𝕜) :
    dist (lineMap p₁ p₂ c₁) (lineMap p₁ p₂ c₂) = dist c₁ c₂ * dist p₁ p₂ := by
  rw [dist_comm p₁ p₂]
  simp only [lineMap_apply, dist_eq_norm_vsub, vadd_vsub_vadd_cancel_right,
    ← sub_smul, norm_smul, vsub_eq_sub]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**nndist_lineMap_lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_lineMap_lineMap (p₁ p₂ : P) (c₁ c₂ : 𝕜) : nndist (lineMap p₁ p₂ c₁)
 (lineMap p₁ p₂ c₂) = nndist c₁ c₂ * nndist p₁ p₂
参数：p₁ p₂ : P；c₁ c₂ : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_lineMap_lineMap`：dist_lineMap_lineMap (p₁ p₂ : P) (c₁ c₂ : 𝕜) : dis
t (lineMap p₁ p₂ c₁) (lineMap p₁ p₂ c₂) = dist c₁ c₂ * dist p₁ p₂
-/
theorem nndist_lineMap_lineMap (p₁ p₂ : P) (c₁ c₂ : 𝕜) :
    nndist (lineMap p₁ p₂ c₁) (lineMap p₁ p₂ c₂) = nndist c₁ c₂ * nndist p₁ p₂ :=
  NNReal.eq <| dist_lineMap_lineMap _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**lipschitzWith_lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzWith_lineMap (p₁ p₂ : P) : LipschitzWith (nndist p₁ p₂) (lineMap 
p₁ p₂ : 𝕜 -> P)
参数：p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   (∀ (x 
y : α), dist (f x)…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_lineMap_lineMap`：dist_lineMap_lineMap (p₁ p₂ : P) (c₁ c₂ : 𝕜) : dis
t (lineMap p₁ p₂ c₁) (lineMap p₁ p₂ c₂) = dist c₁ c₂ * dist p₁ p₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem lipschitzWith_lineMap (p₁ p₂ : P) : LipschitzWith (nndist p₁ p₂) (lineMap p₁ p₂ : 𝕜 → P) :=
  LipschitzWith.of_dist_le_mul fun c₁ c₂ =>
    ((dist_lineMap_lineMap p₁ p₂ c₁ c₂).trans (mul_comm _ _)).le

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**dist_lineMap_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_lineMap_left (p₁ p₂ : P) (c : 𝕜) : dist (lineMap p₁ p₂ c) p₁ = ‖c‖ * 
dist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `dist_lineMap_lineMap`：dist_lineMap_lineMap (p₁ p₂ : P) (c₁ c₂ : 𝕜) : dis
t (lineMap p₁ p₂ c₁) (lineMap p₁ p₂ c₂) = dist c₁ c₂ * dist p₁ p₂
-/
theorem dist_lineMap_left (p₁ p₂ : P) (c : 𝕜) : dist (lineMap p₁ p₂ c) p₁ = ‖c‖ * dist p₁ p₂ := by
  simpa only [lineMap_apply_zero, dist_zero_right] using dist_lineMap_lineMap p₁ p₂ c 0

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**nndist_lineMap_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_lineMap_left (p₁ p₂ : P) (c : 𝕜) : nndist (lineMap p₁ p₂ c) p₁ = ‖c
‖₊ * nndist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_lineMap_left`：dist_lineMap_left (p₁ p₂ : P) (c : 𝕜) : dist (lineMap
 p₁ p₂ c) p₁ = ‖c‖ * dist p₁ p₂
-/
theorem nndist_lineMap_left (p₁ p₂ : P) (c : 𝕜) :
    nndist (lineMap p₁ p₂ c) p₁ = ‖c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_lineMap_left _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**dist_left_lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_left_lineMap (p₁ p₂ : P) (c : 𝕜) : dist p₁ (lineMap p₁ p₂ c) = ‖c‖ * 
dist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_lineMap_left`：dist_lineMap_left (p₁ p₂ : P) (c : 𝕜) : dist (lineMap
 p₁ p₂ c) p₁ = ‖c‖ * dist p₁ p₂
-/
theorem dist_left_lineMap (p₁ p₂ : P) (c : 𝕜) : dist p₁ (lineMap p₁ p₂ c) = ‖c‖ * dist p₁ p₂ :=
  (dist_comm _ _).trans (dist_lineMap_left _ _ _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**nndist_left_lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_left_lineMap (p₁ p₂ : P) (c : 𝕜) : nndist p₁ (lineMap p₁ p₂ c) = ‖c
‖₊ * nndist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_left_lineMap`：dist_left_lineMap (p₁ p₂ : P) (c : 𝕜) : dist p₁ (line
Map p₁ p₂ c) = ‖c‖ * dist p₁ p₂
-/
theorem nndist_left_lineMap (p₁ p₂ : P) (c : 𝕜) :
    nndist p₁ (lineMap p₁ p₂ c) = ‖c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_left_lineMap _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**dist_lineMap_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_lineMap_right (p₁ p₂ : P) (c : 𝕜) : dist (lineMap p₁ p₂ c) p₂ = ‖1 - 
c‖ * dist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm'`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b :
 E), dist a b = ‖b - a‖
· 使用定理 `dist_lineMap_lineMap`：dist_lineMap_lineMap (p₁ p₂ : P) (c₁ c₂ : 𝕜) : dis
t (lineMap p₁ p₂ c₁) (lineMap p₁ p₂ c₂) = dist c₁ c₂ * dist p₁ p₂
-/
theorem dist_lineMap_right (p₁ p₂ : P) (c : 𝕜) :
    dist (lineMap p₁ p₂ c) p₂ = ‖1 - c‖ * dist p₁ p₂ := by
  simpa only [lineMap_apply_one, dist_eq_norm'] using dist_lineMap_lineMap p₁ p₂ c 1

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**nndist_lineMap_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_lineMap_right (p₁ p₂ : P) (c : 𝕜) : nndist (lineMap p₁ p₂ c) p₂ = ‖
1 - c‖₊ * nndist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_lineMap_right`：dist_lineMap_right (p₁ p₂ : P) (c : 𝕜) : dist (lineM
ap p₁ p₂ c) p₂ = ‖1 - c‖ * dist p₁ p₂
-/
theorem nndist_lineMap_right (p₁ p₂ : P) (c : 𝕜) :
    nndist (lineMap p₁ p₂ c) p₂ = ‖1 - c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_lineMap_right _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**dist_right_lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_right_lineMap (p₁ p₂ : P) (c : 𝕜) : dist p₂ (lineMap p₁ p₂ c) = ‖1 - 
c‖ * dist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_lineMap_right`：dist_lineMap_right (p₁ p₂ : P) (c : 𝕜) : dist (lineM
ap p₁ p₂ c) p₂ = ‖1 - c‖ * dist p₁ p₂
-/
theorem dist_right_lineMap (p₁ p₂ : P) (c : 𝕜) : dist p₂ (lineMap p₁ p₂ c) = ‖1 - c‖ * dist p₁ p₂ :=
  (dist_comm _ _).trans (dist_lineMap_right _ _ _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**nndist_right_lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_right_lineMap (p₁ p₂ : P) (c : 𝕜) : nndist p₂ (lineMap p₁ p₂ c) = ‖
1 - c‖₊ * nndist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_right_lineMap`：dist_right_lineMap (p₁ p₂ : P) (c : 𝕜) : dist p₂ (li
neMap p₁ p₂ c) = ‖1 - c‖ * dist p₁ p₂
-/
theorem nndist_right_lineMap (p₁ p₂ : P) (c : 𝕜) :
    nndist p₂ (lineMap p₁ p₂ c) = ‖1 - c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_right_lineMap _ _ _

@[simp]
/-
**dist_homothety_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_homothety_self (p₁ p₂ : P) (c : 𝕜) : dist (homothety p₁ c p₂) p₂ = ‖1
 - c‖ * dist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.homothety_eq_lineMap`：homothety_eq_lineMap (c : P1) (r : k) (p
 : P1) : homothety c r p = lineMap c p r
· 使用定理 `dist_lineMap_right`：dist_lineMap_right (p₁ p₂ : P) (c : 𝕜) : dist (lineM
ap p₁ p₂ c) p₂ = ‖1 - c‖ * dist p₁ p₂
-/
theorem dist_homothety_self (p₁ p₂ : P) (c : 𝕜) :
    dist (homothety p₁ c p₂) p₂ = ‖1 - c‖ * dist p₁ p₂ := by
  rw [homothety_eq_lineMap, dist_lineMap_right]

@[simp]
/-
**nndist_homothety_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_homothety_self (p₁ p₂ : P) (c : 𝕜) : nndist (homothety p₁ c p₂) p₂ 
= ‖1 - c‖₊ * nndist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_homothety_self`：dist_homothety_self (p₁ p₂ : P) (c : 𝕜) : dist (hom
othety p₁ c p₂) p₂ = ‖1 - c‖ * dist p₁ p₂
-/
theorem nndist_homothety_self (p₁ p₂ : P) (c : 𝕜) :
    nndist (homothety p₁ c p₂) p₂ = ‖1 - c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_homothety_self _ _ _

@[simp]
/-
**dist_self_homothety** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_self_homothety (p₁ p₂ : P) (c : 𝕜) : dist p₂ (homothety p₁ c p₂) = ‖1
 - c‖ * dist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_homothety_self`：dist_homothety_self (p₁ p₂ : P) (c : 𝕜) : dist (hom
othety p₁ c p₂) p₂ = ‖1 - c‖ * dist p₁ p₂
-/
theorem dist_self_homothety (p₁ p₂ : P) (c : 𝕜) :
    dist p₂ (homothety p₁ c p₂) = ‖1 - c‖ * dist p₁ p₂ := by rw [dist_comm, dist_homothety_self]

@[simp]
/-
**nndist_self_homothety** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_self_homothety (p₁ p₂ : P) (c : 𝕜) : nndist p₂ (homothety p₁ c p₂) 
= ‖1 - c‖₊ * nndist p₁ p₂
参数：p₁ p₂ : P；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_self_homothety`：dist_self_homothety (p₁ p₂ : P) (c : 𝕜) : dist p₂ (
homothety p₁ c p₂) = ‖1 - c‖ * dist p₁ p₂
-/
theorem nndist_self_homothety (p₁ p₂ : P) (c : 𝕜) :
    nndist p₂ (homothety p₁ c p₂) = ‖1 - c‖₊ * nndist p₁ p₂ :=
  NNReal.eq <| dist_self_homothety _ _ _

section invertibleTwo

variable [Invertible (2 : 𝕜)]

@[simp]
/-
**dist_left_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_left_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ 
* dist p₁ p₂
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ri
ng R] [inst_1 : Invertible 2] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Modul
e R…
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_lineMap_left`：dist_lineMap_left (p₁ p₂ : P) (c : 𝕜) : dist (lineMap
 p₁ p₂ c) p₁ = ‖c‖ * dist p₁ p₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
-/
theorem dist_left_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂ := by
  rw [midpoint, dist_comm, dist_lineMap_left, invOf_eq_inv, ← norm_inv]

@[simp]
/-
**nndist_left_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_left_midpoint (p₁ p₂ : P) : nndist p₁ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)
‖₊⁻¹ * nndist p₁ p₂
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_left_midpoint`：dist_left_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜
 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
-/
theorem nndist_left_midpoint (p₁ p₂ : P) :
    nndist p₁ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖₊⁻¹ * nndist p₁ p₂ :=
  NNReal.eq <| dist_left_midpoint _ _

@[simp]
/-
**dist_midpoint_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_midpoint_left (p₁ p₂ : P) : dist (midpoint 𝕜 p₁ p₂) p₁ = ‖(2 : 𝕜)‖⁻¹ 
* dist p₁ p₂
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_left_midpoint`：dist_left_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜
 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
-/
theorem dist_midpoint_left (p₁ p₂ : P) : dist (midpoint 𝕜 p₁ p₂) p₁ = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂ := by
  rw [dist_comm, dist_left_midpoint]

@[simp]
/-
**nndist_midpoint_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_midpoint_left (p₁ p₂ : P) : nndist (midpoint 𝕜 p₁ p₂) p₁ = ‖(2 : 𝕜)
‖₊⁻¹ * nndist p₁ p₂
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_midpoint_left`：dist_midpoint_left (p₁ p₂ : P) : dist (midpoint 𝕜 p₁
 p₂) p₁ = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
-/
theorem nndist_midpoint_left (p₁ p₂ : P) :
    nndist (midpoint 𝕜 p₁ p₂) p₁ = ‖(2 : 𝕜)‖₊⁻¹ * nndist p₁ p₂ :=
  NNReal.eq <| dist_midpoint_left _ _

@[simp]
/-
**dist_midpoint_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_midpoint_right (p₁ p₂ : P) : dist (midpoint 𝕜 p₁ p₂) p₂ = ‖(2 : 𝕜)‖⁻¹
 * dist p₁ p₂
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_comm`：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
· 使用定理 `dist_midpoint_left`：dist_midpoint_left (p₁ p₂ : P) : dist (midpoint 𝕜 p₁
 p₂) p₁ = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
-/
theorem dist_midpoint_right (p₁ p₂ : P) :
    dist (midpoint 𝕜 p₁ p₂) p₂ = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂ := by
  rw [midpoint_comm, dist_midpoint_left, dist_comm]

@[simp]
/-
**nndist_midpoint_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_midpoint_right (p₁ p₂ : P) : nndist (midpoint 𝕜 p₁ p₂) p₂ = ‖(2 : 𝕜
)‖₊⁻¹ * nndist p₁ p₂
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_midpoint_right`：dist_midpoint_right (p₁ p₂ : P) : dist (midpoint 𝕜 
p₁ p₂) p₂ = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
-/
theorem nndist_midpoint_right (p₁ p₂ : P) :
    nndist (midpoint 𝕜 p₁ p₂) p₂ = ‖(2 : 𝕜)‖₊⁻¹ * nndist p₁ p₂ :=
  NNReal.eq <| dist_midpoint_right _ _

@[simp]
/-
**dist_right_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_right_midpoint (p₁ p₂ : P) : dist p₂ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹
 * dist p₁ p₂
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_midpoint_right`：dist_midpoint_right (p₁ p₂ : P) : dist (midpoint 𝕜 
p₁ p₂) p₂ = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
-/
theorem dist_right_midpoint (p₁ p₂ : P) :
    dist p₂ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂ := by
  rw [dist_comm, dist_midpoint_right]

@[simp]
/-
**nndist_right_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_right_midpoint (p₁ p₂ : P) : nndist p₂ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜
)‖₊⁻¹ * nndist p₁ p₂
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_right_midpoint`：dist_right_midpoint (p₁ p₂ : P) : dist p₂ (midpoint
 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
-/
theorem nndist_right_midpoint (p₁ p₂ : P) :
    nndist p₂ (midpoint 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖₊⁻¹ * nndist p₁ p₂ :=
  NNReal.eq <| dist_right_midpoint _ _

/-- The midpoint of the segment AB is the same distance from A as it is from B. -/
/-
**dist_left_midpoint_eq_dist_right_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_left_midpoint_eq_dist_right_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 
𝕜 p₁ p₂) = dist p₂ (midpoint 𝕜 p₁ p₂)
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_left_midpoint`：dist_left_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜
 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂
· 使用定理 `dist_right_midpoint`：dist_right_midpoint (p₁ p₂ : P) : dist p₂ (midpoint
 𝕜 p₁ p₂) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂

--- 原说明 ---
The midpoint of the segment AB is the same distance from A as it is from B.
-/
theorem dist_left_midpoint_eq_dist_right_midpoint (p₁ p₂ : P) :
    dist p₁ (midpoint 𝕜 p₁ p₂) = dist p₂ (midpoint 𝕜 p₁ p₂) := by
  rw [dist_left_midpoint p₁ p₂, dist_right_midpoint p₁ p₂]
/-
**dist_midpoint_midpoint_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P) : dist (midpoint 𝕜 p₁ p₂) (mi
dpoint 𝕜 p₃ p₄) <= (dist p₁ p₃ + dist p₂ p₄) / ‖(2 : 𝕜)‖
参数：p₁ p₂ p₃ p₄ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `midpoint_vsub_midpoint`：midpoint_vsub_midpoint (p₁ p₂ p₃ p₄ : P) : midpo
int R p₁ p₂ -ᵥ midpoint R p₃ p₄ = midpoint R (p₁ -ᵥ p₃) (p₂ -ᵥ p₄)
· 使用定理 `midpoint_eq_smul_add`：midpoint_eq_smul_add (x y : V) : midpoint R x y = 
(⅟2 : R) • (x + y)
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem dist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P) :
    dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₃ p₄) ≤ (dist p₁ p₃ + dist p₂ p₄) / ‖(2 : 𝕜)‖ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, midpoint_vsub_midpoint]
  rw [midpoint_eq_smul_add, norm_smul, invOf_eq_inv, norm_inv, ← div_eq_inv_mul]
  grw [norm_add_le]
/-
**nndist_midpoint_midpoint_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P) : nndist (midpoint 𝕜 p₁ p₂)
 (midpoint 𝕜 p₃ p₄) <= (nndist p₁ p₃ + nndist p₂ p₄) / ‖(2 : 𝕜)‖₊
参数：p₁ p₂ p₃ p₄ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `dist_midpoint_midpoint_le'`：dist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P)
 : dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₃ p₄) <= (dist p₁ p₃ + dist p₂ p₄) / ‖(2
 : 𝕜)‖
-/
theorem nndist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P) :
    nndist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₃ p₄) ≤ (nndist p₁ p₃ + nndist p₂ p₄) / ‖(2 : 𝕜)‖₊ :=
  dist_midpoint_midpoint_le' _ _ _ _

end invertibleTwo

/-
**dist_pointReflection_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : SeminormedAddCommGroup V] [inst_1 
: PseudoMetricSpace P]   [inst_2 : NormedAddTorsor V P] (p q : P), dist ((Equiv.
pointReflection p) q) p = dist p q
参数：p q : P；(Equiv.pointReflection p) q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Equiv.pointReflection_vsub_left`：pointReflection_vsub_left (x y : P) : p
ointReflection x y -ᵥ x = x -ᵥ y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem dist_pointReflection_left (p q : P) :
    dist (Equiv.pointReflection p q) p = dist p q := by
  simp [dist_eq_norm_vsub V, Equiv.pointReflection_vsub_left (G := V)]
/-
**dist_left_pointReflection** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : SeminormedAddCommGroup V] [inst_1 
: PseudoMetricSpace P]   [inst_2 : NormedAddTorsor V P] (p q : P), dist p ((Equi
v.pointReflection p) q) = dist p q
参数：p q : P；(Equiv.pointReflection p) q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_pointReflection_left`：∀ {V : Type u_1} {P : Type u_2} [inst : Semin
ormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTorsor 
V P] (p q : P),…
-/
@[simp] theorem dist_left_pointReflection (p q : P) :
    dist p (Equiv.pointReflection p q) = dist p q :=
  (dist_comm _ _).trans (dist_pointReflection_left _ _)

variable (𝕜) in
/-
**dist_pointReflection_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_pointReflection_right (p q : P) : dist (Equiv.pointReflection p q) q 
= ‖(2 : 𝕜)‖ * dist p q
参数：p q : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Equiv.pointReflection_vsub_right`：pointReflection_vsub_right (x y : P) :
 pointReflection x y -ᵥ y = 2 • (x -ᵥ y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_pointReflection_right (p q : P) :
    dist (Equiv.pointReflection p q) q = ‖(2 : 𝕜)‖ * dist p q := by
  simp [dist_eq_norm_vsub V, Equiv.pointReflection_vsub_right (G := V), ← Nat.cast_smul_eq_nsmul 𝕜,
    norm_smul]

variable (𝕜) in
/-
**dist_right_pointReflection** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_right_pointReflection (p q : P) : dist q (Equiv.pointReflection p q) 
= ‖(2 : 𝕜)‖ * dist p q
参数：p q : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_pointReflection_right`：dist_pointReflection_right (p q : P) : dist 
(Equiv.pointReflection p q) q = ‖(2 : 𝕜)‖ * dist p q
-/
theorem dist_right_pointReflection (p q : P) :
    dist q (Equiv.pointReflection p q) = ‖(2 : 𝕜)‖ * dist p q :=
  (dist_comm _ _).trans (dist_pointReflection_right 𝕜 _ _)

set_option backward.isDefEq.respectTransparency false in
/-
**antilipschitzWith_lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antilipschitzWith_lineMap {p₁ p₂ : Q} (h : p₁ != p₂) : AntilipschitzWith (
nndist p₁ p₂)⁻¹ (lineMap p₁ p₂ : 𝕜 -> Q)
参数：h : p₁ != p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.of_le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst 
: PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β}, 
  (∀ (x y : α), dist x…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_lineMap_lineMap`：dist_lineMap_lineMap (p₁ p₂ : P) (c₁ c₂ : 𝕜) : dis
t (lineMap p₁ p₂ c₁) (lineMap p₁ p₂ c₂) = dist c₁ c₂ * dist p₁ p₂
· 使用定理 `NNReal.coe_inv`：∀ (r : NNReal), ↑r⁻¹ = (↑r)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_nndist`：dist_nndist (x y : α) : dist x y = nndist x y
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dist_ne_zero`：dist_ne_zero {x y : γ} : dist x y != 0 ↔ x != y
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem antilipschitzWith_lineMap {p₁ p₂ : Q} (h : p₁ ≠ p₂) :
    AntilipschitzWith (nndist p₁ p₂)⁻¹ (lineMap p₁ p₂ : 𝕜 → Q) :=
  AntilipschitzWith.of_le_mul_dist fun c₁ c₂ => by
    rw [dist_lineMap_lineMap, NNReal.coe_inv, ← dist_nndist, mul_left_comm,
      inv_mul_cancel₀ (dist_ne_zero.2 h), mul_one]

end NormedSpace

variable [NormedSpace ℝ V] [NormedSpace ℝ W]

/-
**dist_midpoint_midpoint_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) : dist (midpoint Real p₁ p₂) (
midpoint Real p₃ p₄) <= (dist p₁ p₃ + dist p₂ p₄) / 2
参数：p₁ p₂ p₃ p₄ : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖ = OfNa
t.ofNat n
· 使用定理 `dist_midpoint_midpoint_le'`：dist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P)
 : dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₃ p₄) <= (dist p₁ p₃ + dist p₂ p₄) / ‖(2
 : 𝕜)‖
-/
theorem dist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) :
    dist (midpoint ℝ p₁ p₂) (midpoint ℝ p₃ p₄) ≤ (dist p₁ p₃ + dist p₂ p₄) / 2 := by
  simpa using dist_midpoint_midpoint_le' (𝕜 := ℝ) p₁ p₂ p₃ p₄
/-
**nndist_midpoint_midpoint_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) : nndist (midpoint Real p₁ p
₂) (midpoint Real p₃ p₄) <= (nndist p₁ p₃ + nndist p₂ p₄) / 2
参数：p₁ p₂ p₃ p₄ : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_midpoint_midpoint_le`：dist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) :
 dist (midpoint Real p₁ p₂) (midpoint Real p₃ p₄) <= (dist p₁ p₃ + dist p₂ p₄) /
 2
-/
theorem nndist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) :
    nndist (midpoint ℝ p₁ p₂) (midpoint ℝ p₃ p₄) ≤ (nndist p₁ p₃ + nndist p₂ p₄) / 2 :=
  dist_midpoint_midpoint_le _ _ _ _

/-- A continuous map between two normed affine spaces is an affine map provided that
it sends midpoints to midpoints. -/
/-
**AffineMap.ofMapMidpoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AffineMap.ofMapMidpoint (f : P -> Q) (h : forall x y, f (midpoint Real x y
) = midpoint Real (f x) (f y)) (hfc : Continuous f) : P ->ᵃ[Real] Q
参数：f : P -> Q；h : forall x y, f (midpoint Real x y) = midpoint Real (f x) (f y)；
hfc : Continuous f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous map between two normed affine spaces is an affine map provided that
it sends midpoints to midpoints.
-/
def AffineMap.ofMapMidpoint (f : P → Q) (h : ∀ x y, f (midpoint ℝ x y) = midpoint ℝ (f x) (f y))
    (hfc : Continuous f) : P →ᵃ[ℝ] Q :=
  let c := Classical.arbitrary P
  AffineMap.mk' f (↑((AddMonoidHom.ofMapMidpoint ℝ ℝ
    ((AffineEquiv.vaddConst ℝ (f <| c)).symm ∘ f ∘ AffineEquiv.vaddConst ℝ c) (by simp)
    fun x y => by simp [h]).toRealLinearMap <| by
        apply_rules [Continuous.vadd, Continuous.vsub, continuous_const, hfc.comp, continuous_id]))
    c fun p => by simp

end

section

open Dilation

variable {𝕜 E : Type*} [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E]
variable [Module 𝕜 E] [NormSMulClass 𝕜 E] {P : Type*} [PseudoMetricSpace P] [NormedAddTorsor E P]

-- TODO: reimplement this as a `ContinuousAffineEquiv`.
/-- Scaling by an element `k` of the scalar ring as a `DilationEquiv` with ratio `‖k‖₊`, mapping
from a normed space to a normed torsor over that space sending `0` to `c`. -/
@[simps]
/-
**DilationEquiv.smulTorsor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DilationEquiv.smulTorsor (c : P) {k : 𝕜} (hk : k != 0) : E ≃ᵈ P where toFu
n
参数：c : P；hk : k != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scaling by an element `k` of the scalar ring as a `DilationEquiv` with ratio `‖k
‖₊`, mapping
from a normed space to a normed torsor over that space sending `0` to `c`.
-/
def DilationEquiv.smulTorsor (c : P) {k : 𝕜} (hk : k ≠ 0) : E ≃ᵈ P where
  toFun := (k • · +ᵥ c)
  invFun := k⁻¹ • (· -ᵥ c)
  left_inv x := by simp [inv_smul_smul₀ hk]
  right_inv p := by simp [smul_inv_smul₀ hk]
  edist_eq' := ⟨‖k‖₊, nnnorm_ne_zero_iff.mpr hk, fun x y ↦ by
    rw [show edist (k • x +ᵥ c) (k • y +ᵥ c) = _ from (IsometryEquiv.vaddConst c).isometry ..]
    exact edist_smul₀ ..⟩

-- Cannot be @[simp] because `x` and `y` cannot be inferred by `simp`.
/-
**DilationEquiv.smulTorsor_ratio** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DilationEquiv.smulTorsor_ratio {c : P} {k : 𝕜} (hk : k != 0) {x y : E} (h 
: dist x y != 0) : ratio (smulTorsor c hk) = ‖k‖₊
参数：hk : k != 0；h : dist x y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instDilationClassOfDilationEquivClass`：∀ (F : Type u_1) (X : outParam (T
ype u_2)) (Y : outParam (Type u_3)) [inst : PseudoEMetricSpace X]   [inst_1 : Ps
eudoEMetricSpace Y] [inst_2…
· 使用定理 `DilationEquiv.instDilationEquivClass`：∀ {X : Type u_1} {Y : Type u_2} [i
nst : PseudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y],   DilationEquivClas
s (X ≃ᵈ Y) X Y
· 使用定理 `Dilation.ratio_unique_of_dist_ne_zero`：ratio_unique_of_dist_ne_zero {α β
} {F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β] [Dilat
ionClass F α β] {f : F} {x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DilationEquiv.smulTorsor_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : 
NormedDivisionRing 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root_.Mod
ule 𝕜 E] [inst_3 : N…
· 使用定理 `dist_vadd_cancel_right`：dist_vadd_cancel_right (v₁ v₂ : V) (x : P) : dis
t (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma DilationEquiv.smulTorsor_ratio {c : P} {k : 𝕜} (hk : k ≠ 0) {x y : E}
    (h : dist x y ≠ 0) : ratio (smulTorsor c hk) = ‖k‖₊ :=
  Eq.symm <| ratio_unique_of_dist_ne_zero h <| by simp [dist_eq_norm, ← smul_sub, norm_smul]

@[simp]
/-
**DilationEquiv.smulTorsor_preimage_ball** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DilationEquiv.smulTorsor_preimage_ball {c : P} {k : 𝕜} (hk : k != 0) : smu
lTorsor c hk ⁻¹' (Metric.ball c ‖k‖) = Metric.ball (0 : E) 1
参数：hk : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DilationEquiv.smulTorsor_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : 
NormedDivisionRing 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root_.Mod
ule 𝕜 E] [inst_3 : N…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_vadd_left`：dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ‖v‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma DilationEquiv.smulTorsor_preimage_ball {c : P} {k : 𝕜} (hk : k ≠ 0) :
    smulTorsor c hk ⁻¹' (Metric.ball c ‖k‖) = Metric.ball (0 : E) 1 := by
  aesop (add simp norm_smul)

end

