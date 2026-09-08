/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Properties of pointwise addition of sets in normed groups

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/

public section


open Metric Set Pointwise Topology

variable {E : Type*}

section SeminormedGroup

variable [SeminormedGroup E] {s t : Set E}

-- note: we can't use `LipschitzOnWith.isBounded_image2` here without adding `[IsIsometricSMul E E]`
@[to_additive]
/-
**Bornology.IsBounded.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bornology.IsBounded.mul (hs : IsBounded s) (ht : IsBounded t) : IsBounded 
(s * t)
参数：hs : IsBounded s；ht : IsBounded t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.exists_norm_le'`：∀ {E : Type u_2} [inst : Seminormed
Group E] {s : Set E}, Bornology.IsBounded s → ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isBounded_iff_forall_norm_le'`：isBounded_iff_forall_norm_le' : Bornology
.IsBounded s ↔ exists C, forall x in s, ‖x‖ <= C
· 使用定理 `norm_mul_le_of_le'`：norm_mul_le_of_le' (h₁ : ‖a₁‖ <= r₁) (h₂ : ‖a₂‖ <= r
₂) : ‖a₁ * a₂‖ <= r₁ + r₂
-/
theorem Bornology.IsBounded.mul (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s * t) := by
  obtain ⟨Rs, hRs⟩ : ∃ R, ∀ x ∈ s, ‖x‖ ≤ R := hs.exists_norm_le'
  obtain ⟨Rt, hRt⟩ : ∃ R, ∀ x ∈ t, ‖x‖ ≤ R := ht.exists_norm_le'
  refine isBounded_iff_forall_norm_le'.2 ⟨Rs + Rt, ?_⟩
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact norm_mul_le_of_le' (hRs x hx) (hRt y hy)

@[to_additive]
/-
**Bornology.IsBounded.of_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bornology.IsBounded.of_mul (hst : IsBounded (s * t)) : IsBounded s ∨ IsBou
nded t
参数：hst : IsBounded (s * t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `AntilipschitzWith.isBounded_of_image2_left`：isBounded_of_image2_left (f 
: α -> β -> γ) {K₁ : Real>=0} (hf : forall b, AntilipschitzWith K₁ fun a => f a 
b) {s : Set α} {t : Set β} (hst …
· 使用定理 `Isometry.antilipschitz`：antilipschitz (h : Isometry f) : AntilipschitzWi
th 1 f
· 使用定理 `isometry_mul_left`：isometry_mul_left [Mul M] [PseudoEMetricSpace M] [IsI
sometricSMul M M] (a : M) : Isometry (a * ·)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_swap`：image2_swap (s : Set α) (t : Set β) : image2 f s t = im
age2 (fun a b => f b a) t s
-/
theorem Bornology.IsBounded.of_mul (hst : IsBounded (s * t)) : IsBounded s ∨ IsBounded t := by
  symm
  exact AntilipschitzWith.isBounded_of_image2_left _ (fun x => (isometry_mul_left x).antilipschitz)
    (by rwa [image2_swap])

@[to_additive]
/-
**Bornology.IsBounded.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bornology.IsBounded.inv : IsBounded s -> IsBounded s⁻¹
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_inv'`：norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖
-/
theorem Bornology.IsBounded.inv : IsBounded s → IsBounded s⁻¹ := by
  simp_rw [isBounded_iff_forall_norm_le', ← image_inv_eq_inv, forall_mem_image, norm_inv']
  exact id

@[to_additive]
/-
**Bornology.IsBounded.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bornology.IsBounded.div (hs : IsBounded s) (ht : IsBounded t) : IsBounded 
(s / t)
参数：hs : IsBounded s；ht : IsBounded t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.mul`：Bornology.IsBounded.mul (hs : IsBounded s) (ht 
: IsBounded t) : IsBounded (s * t)
· 使用定理 `Bornology.IsBounded.inv`：Bornology.IsBounded.inv : IsBounded s -> IsBoun
ded s⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem Bornology.IsBounded.div (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s / t) :=
  div_eq_mul_inv s t ▸ hs.mul ht.inv

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] {δ : ℝ} {s : Set E} {x y : E}

section EMetric

open EMetric

@[to_additive (attr := simp)]
/-
**infEDist_inv_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infEDist_inv_inv (x : E) (s : Set E) : infEDist x⁻¹ s⁻¹ = infEDist x s
参数：x : E；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Metric.infEDist_image`：infEDist_image (hΦ : Isometry Φ) : infEDist (Φ x)
 (Φ '' t) = infEDist x t
· 使用定理 `isometry_inv`：isometry_inv [PseudoEMetricSpace G] [IsIsometricSMul G G] 
[IsIsometricSMul Gᵐᵒᵖ G] : Isometry (Inv.inv : G -> G)
-/
theorem infEDist_inv_inv (x : E) (s : Set E) : infEDist x⁻¹ s⁻¹ = infEDist x s := by
  rw [← image_inv_eq_inv, infEDist_image isometry_inv]

@[deprecated (since := "2026-01-08")]
alias infEdist_neg_neg := infEDist_neg_neg

@[to_additive existing, deprecated (since := "2026-01-08")]
alias infEdist_inv_inv := infEDist_inv_inv


@[to_additive]
/-
**infEDist_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infEDist_inv (x : E) (s : Set E) : infEDist x⁻¹ s = infEDist x s⁻¹
参数：x : E；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `infEDist_inv_inv`：infEDist_inv_inv (x : E) (s : Set E) : infEDist x⁻¹ s⁻
¹ = infEDist x s
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem infEDist_inv (x : E) (s : Set E) : infEDist x⁻¹ s = infEDist x s⁻¹ := by
  rw [← infEDist_inv_inv, inv_inv]

@[deprecated (since := "2026-01-08")]
alias infEdist_neg := infEDist_neg

@[to_additive existing, deprecated (since := "2026-01-08")]
alias infEdist_inv := infEDist_inv

@[to_additive]
/-
**ediam_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ediam_mul_le (x y : Set E) : ediam (x * y) <= ediam x + ediam y
参数：x y : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `LipschitzOnWith.ediam_image2_le`：ediam_image2_le (f : α -> β -> γ) {K₁ K
₂ : Real>=0} (s : Set α) (t : Set β) (hf₁ : forall b in t, LipschitzOnWith K₁ (f
 · b) s) (hf₂ : foral…
· 使用定理 `LipschitzWith.lipschitzOnWith`：∀ {α : Type u} {β : Type v} [inst : Pseud
oEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β}   {s :
 Set α}, LipschitzW…
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `isometry_mul_right`：isometry_mul_right [Mul M] [PseudoEMetricSpace M] [I
sIsometricSMul Mᵐᵒᵖ M] (a : M) : Isometry fun x => x * a
· 使用定理 `isometry_mul_left`：isometry_mul_left [Mul M] [PseudoEMetricSpace M] [IsI
sometricSMul M M] (a : M) : Isometry (a * ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ediam_mul_le (x y : Set E) : ediam (x * y) ≤ ediam x + ediam y :=
  (LipschitzOnWith.ediam_image2_le (· * ·) _ _
        (fun _ _ => (isometry_mul_right _).lipschitz.lipschitzOnWith) fun _ _ =>
        (isometry_mul_left _).lipschitz.lipschitzOnWith).trans_eq <|
    by simp only [ENNReal.coe_one, one_mul]

end EMetric

variable (δ s x y)

@[to_additive (attr := simp)]
/-
**inv_thickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_thickening : (thickening δ s)⁻¹ = thickening δ s⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem inv_thickening : (thickening δ s)⁻¹ = thickening δ s⁻¹ := by
  simp_rw [thickening, ← infEDist_inv]
  rfl

@[to_additive (attr := simp)]
/-
**inv_cthickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_cthickening : (cthickening δ s)⁻¹ = cthickening δ s⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem inv_cthickening : (cthickening δ s)⁻¹ = cthickening δ s⁻¹ := by
  simp_rw [cthickening, ← infEDist_inv]
  rfl

@[to_additive (attr := simp)]
/-
**inv_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_ball : (ball x δ)⁻¹ = ball x⁻¹ δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.preimage_ball`：preimage_ball (h : α ≃ᵢ β) (x : β) (r : Rea
l) : h ⁻¹' Metric.ball x r = Metric.ball (h.symm x) r
-/
theorem inv_ball : (ball x δ)⁻¹ = ball x⁻¹ δ := (IsometryEquiv.inv E).preimage_ball x δ

@[to_additive (attr := simp)]
/-
**inv_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_closedBall : (closedBall x δ)⁻¹ = closedBall x⁻¹ δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.preimage_closedBall`：preimage_closedBall (h : α ≃ᵢ β) (x :
 β) (r : Real) : h ⁻¹' Metric.closedBall x r = Metric.closedBall (h.symm x) r
-/
theorem inv_closedBall : (closedBall x δ)⁻¹ = closedBall x⁻¹ δ :=
  (IsometryEquiv.inv E).preimage_closedBall x δ

@[to_additive (attr := simp)]
/-
**inv_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_sphere : (sphere x δ)⁻¹ = sphere x⁻¹ δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.preimage_sphere`：preimage_sphere (h : α ≃ᵢ β) (x : β) (r :
 Real) : h ⁻¹' Metric.sphere x r = Metric.sphere (h.symm x) r
-/
theorem inv_sphere : (sphere x δ)⁻¹ = sphere x⁻¹ δ :=
  (IsometryEquiv.inv E).preimage_sphere x δ

@[to_additive]
/-
**singleton_mul_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_mul_ball : {x} * ball y δ = ball (x * y) δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_mul`：singleton_mul : {a} * t = (a * ·) '' t
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `preimage_mul_ball`：preimage_mul_ball (a b : E) (r : Real) : (b * ·) ⁻¹' 
ball a r = ball (a / b) r
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_mul_ball : {x} * ball y δ = ball (x * y) δ := by
  simp only [preimage_mul_ball, image_mul_left, singleton_mul, div_inv_eq_mul, mul_comm y x]

@[to_additive]
/-
**singleton_div_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_div_ball : {x} / ball y δ = ball (x / y) δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_ball`：inv_ball : (ball x δ)⁻¹ = ball x⁻¹ δ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `singleton_mul_ball`：singleton_mul_ball : {x} * ball y δ = ball (x * y) δ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_div_ball : {x} / ball y δ = ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_ball, singleton_mul_ball]

@[to_additive]
/-
**ball_mul_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_mul_singleton : ball x δ * {y} = ball (x * y) δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `singleton_mul_ball`：singleton_mul_ball : {x} * ball y δ = ball (x * y) δ
-/
theorem ball_mul_singleton : ball x δ * {y} = ball (x * y) δ := by
  rw [mul_comm, singleton_mul_ball, mul_comm y]

@[to_additive]
/-
**ball_div_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_div_singleton : ball x δ / {y} = ball (x / y) δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inv_singleton`：inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ball_mul_singleton`：ball_mul_singleton : ball x δ * {y} = ball (x * y) δ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ball_div_singleton : ball x δ / {y} = ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_singleton, ball_mul_singleton]

@[to_additive]
/-
**singleton_mul_ball_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_mul_ball_one : {x} * ball 1 δ = ball x δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_mul`：singleton_mul : {a} * t = (a * ·) '' t
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `preimage_mul_ball`：preimage_mul_ball (a b : E) (r : Real) : (b * ·) ⁻¹' 
ball a r = ball (a / b) r
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_mul_ball_one : {x} * ball 1 δ = ball x δ := by simp

@[to_additive]
/-
**singleton_div_ball_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_div_ball_one : {x} / ball 1 δ = ball x δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `singleton_div_ball`：singleton_div_ball : {x} / ball y δ = ball (x / y) δ
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem singleton_div_ball_one : {x} / ball 1 δ = ball x δ := by
  rw [singleton_div_ball, div_one]

@[to_additive]
/-
**ball_one_mul_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_one_mul_singleton : ball 1 δ * {x} = ball x δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mul_singleton`：mul_singleton : s * {b} = (· * b) '' s
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `Metric.preimage_mul_right_ball`：preimage_mul_right_ball [IsIsometricSMul
 Gᵐᵒᵖ G] (a b : G) (r : Real) : (fun x => x * a) ⁻¹' ball b r = ball (b / a) r
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ball_one_mul_singleton : ball 1 δ * {x} = ball x δ := by simp

@[to_additive]
/-
**ball_one_div_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_one_div_singleton : ball 1 δ / {x} = ball x⁻¹ δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ball_div_singleton`：ball_div_singleton : ball x δ / {y} = ball (x / y) δ
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem ball_one_div_singleton : ball 1 δ / {x} = ball x⁻¹ δ := by
  rw [ball_div_singleton, one_div]

@[to_additive]
/-
**smul_ball_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_ball_one : x • ball (1 : E) δ = ball x δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.smul_ball`：smul_ball (c : G) (x : X) (r : Real) : c • ball x r = 
ball (c • x) r
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem smul_ball_one : x • ball (1 : E) δ = ball x δ := by
  rw [smul_ball, smul_eq_mul, mul_one]

@[to_additive (attr := simp 1100)]
/-
**singleton_mul_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_mul_closedBall : {x} * closedBall y δ = closedBall (x * y) δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_mul`：singleton_mul : {a} * t = (a * ·) '' t
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Metric.smul_closedBall`：smul_closedBall (c : G) (x : X) (r : Real) : c •
 closedBall x r = closedBall (c • x) r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_mul_closedBall : {x} * closedBall y δ = closedBall (x * y) δ := by
  simp_rw [singleton_mul, ← smul_eq_mul, image_smul, smul_closedBall]

@[to_additive (attr := simp 1100)]
/-
**singleton_div_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_div_closedBall : {x} / closedBall y δ = closedBall (x / y) δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_closedBall`：inv_closedBall : (closedBall x δ)⁻¹ = closedBall x⁻¹ δ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `singleton_mul_closedBall`：singleton_mul_closedBall : {x} * closedBall y 
δ = closedBall (x * y) δ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_div_closedBall : {x} / closedBall y δ = closedBall (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_closedBall, singleton_mul_closedBall]

@[to_additive (attr := simp 1100)]
/-
**closedBall_mul_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedBall_mul_singleton : closedBall x δ * {y} = closedBall (x * y) δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `singleton_mul_closedBall`：singleton_mul_closedBall : {x} * closedBall y 
δ = closedBall (x * y) δ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closedBall_mul_singleton : closedBall x δ * {y} = closedBall (x * y) δ := by
  simp [mul_comm _ {y}, mul_comm y]

@[to_additive (attr := simp 1100)]
/-
**closedBall_div_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedBall_div_singleton : closedBall x δ / {y} = closedBall (x / y) δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.inv_singleton`：inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹}
· 使用定理 `closedBall_mul_singleton`：closedBall_mul_singleton : closedBall x δ * {y
} = closedBall (x * y) δ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closedBall_div_singleton : closedBall x δ / {y} = closedBall (x / y) δ := by
  simp [div_eq_mul_inv]

@[to_additive]
/-
**singleton_mul_closedBall_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_mul_closedBall_one : {x} * closedBall 1 δ = closedBall x δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `singleton_mul_closedBall`：singleton_mul_closedBall : {x} * closedBall y 
δ = closedBall (x * y) δ
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_mul_closedBall_one : {x} * closedBall 1 δ = closedBall x δ := by simp

@[to_additive]
/-
**singleton_div_closedBall_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_div_closedBall_one : {x} / closedBall 1 δ = closedBall x δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `singleton_div_closedBall`：singleton_div_closedBall : {x} / closedBall y 
δ = closedBall (x / y) δ
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem singleton_div_closedBall_one : {x} / closedBall 1 δ = closedBall x δ := by
  rw [singleton_div_closedBall, div_one]

@[to_additive]
/-
**closedBall_one_mul_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedBall_one_mul_singleton : closedBall 1 δ * {x} = closedBall x δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closedBall_mul_singleton`：closedBall_mul_singleton : closedBall x δ * {y
} = closedBall (x * y) δ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closedBall_one_mul_singleton : closedBall 1 δ * {x} = closedBall x δ := by simp

@[to_additive]
/-
**closedBall_one_div_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedBall_one_div_singleton : closedBall 1 δ / {x} = closedBall x⁻¹ δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closedBall_div_singleton`：closedBall_div_singleton : closedBall x δ / {y
} = closedBall (x / y) δ
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closedBall_one_div_singleton : closedBall 1 δ / {x} = closedBall x⁻¹ δ := by simp

@[to_additive (attr := simp 1100)]
/-
**smul_closedBall_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_closedBall_one : x • closedBall (1 : E) δ = closedBall x δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.smul_closedBall`：smul_closedBall (c : G) (x : X) (r : Real) : c •
 closedBall x r = closedBall (c • x) r
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_closedBall_one : x • closedBall (1 : E) δ = closedBall x δ := by simp

@[to_additive (attr := simp 1100)]
/-
**singleton_mul_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_mul_sphere : {x} * sphere y δ = sphere (x * y) δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_mul`：singleton_mul : {a} * t = (a * ·) '' t
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Metric.smul_sphere`：smul_sphere (c : G) (x : X) (r : Real) : c • sphere 
x r = sphere (c • x) r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_mul_sphere : {x} * sphere y δ = sphere (x * y) δ := by
  simp_rw [singleton_mul, ← smul_eq_mul, image_smul, smul_sphere]

@[to_additive (attr := simp 1100)]
/-
**singleton_div_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_div_sphere : {x} / sphere y δ = sphere (x / y) δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_sphere`：inv_sphere : (sphere x δ)⁻¹ = sphere x⁻¹ δ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `singleton_mul_sphere`：singleton_mul_sphere : {x} * sphere y δ = sphere (
x * y) δ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_div_sphere : {x} / sphere y δ = sphere (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_sphere, singleton_mul_sphere]

@[to_additive (attr := simp 1100)]
/-
**sphere_mul_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sphere_mul_singleton : sphere x δ * {y} = sphere (x * y) δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `singleton_mul_sphere`：singleton_mul_sphere : {x} * sphere y δ = sphere (
x * y) δ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sphere_mul_singleton : sphere x δ * {y} = sphere (x * y) δ := by
  simp [mul_comm _ {y}, mul_comm y]

@[to_additive (attr := simp 1100)]
/-
**sphere_div_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sphere_div_singleton : sphere x δ / {y} = sphere (x / y) δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.inv_singleton`：inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹}
· 使用定理 `sphere_mul_singleton`：sphere_mul_singleton : sphere x δ * {y} = sphere (
x * y) δ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sphere_div_singleton : sphere x δ / {y} = sphere (x / y) δ := by
  simp [div_eq_mul_inv]

@[to_additive]
/-
**singleton_mul_sphere_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_mul_sphere_one : {x} * sphere 1 δ = sphere x δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `singleton_mul_sphere`：singleton_mul_sphere : {x} * sphere y δ = sphere (
x * y) δ
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_mul_sphere_one : {x} * sphere 1 δ = sphere x δ := by simp

@[to_additive]
/-
**singleton_div_sphere_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_div_sphere_one : {x} / sphere 1 δ = sphere x δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `singleton_div_sphere`：singleton_div_sphere : {x} / sphere y δ = sphere (
x / y) δ
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem singleton_div_sphere_one : {x} / sphere 1 δ = sphere x δ := by
  rw [singleton_div_sphere, div_one]

@[to_additive]
/-
**sphere_one_mul_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sphere_one_mul_singleton : sphere 1 δ * {x} = sphere x δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sphere_mul_singleton`：sphere_mul_singleton : sphere x δ * {y} = sphere (
x * y) δ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sphere_one_mul_singleton : sphere 1 δ * {x} = sphere x δ := by simp

@[to_additive]
/-
**sphere_one_div_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sphere_one_div_singleton : sphere 1 δ / {x} = sphere x⁻¹ δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sphere_div_singleton`：sphere_div_singleton : sphere x δ / {y} = sphere (
x / y) δ
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sphere_one_div_singleton : sphere 1 δ / {x} = sphere x⁻¹ δ := by simp

@[to_additive (attr := simp 1100)]
/-
**smul_sphere_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_sphere_one : x • sphere (1 : E) δ = sphere x δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.smul_sphere`：smul_sphere (c : G) (x : X) (r : Real) : c • sphere 
x r = sphere (c • x) r
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_sphere_one : x • sphere (1 : E) δ = sphere x δ := by simp

@[to_additive]
/-
**mul_ball_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_ball_one : s * ball 1 δ = thickening δ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.thickening_eq_biUnion_ball`：thickening_eq_biUnion_ball {δ : Real}
 {E : Set X} : thickening δ E = ⋃ x in E, ball x δ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `singleton_mul_ball`：singleton_mul_ball : {x} * ball y δ = ball (x * y) δ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.iUnion₂_mul`：iUnion₂_mul (s : forall i, κ i -> Set α) (t : Set α) : 
(⋃ (i) (j), s i j) * t = ⋃ (i) (j), s i j * t
-/
theorem mul_ball_one : s * ball 1 δ = thickening δ s := by
  rw [thickening_eq_biUnion_ball]
  convert! iUnion₂_mul (fun x (_ : x ∈ s) => { x }) (ball (1 : E) δ)
  · exact s.biUnion_of_singleton.symm
  ext x
  simp_rw [singleton_mul_ball, mul_one]

@[to_additive]
/-
**div_ball_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_ball_one : s / ball 1 δ = thickening δ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_ball`：inv_ball : (ball x δ)⁻¹ = ball x⁻¹ δ
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_ball_one`：mul_ball_one : s * ball 1 δ = thickening δ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_ball_one : s / ball 1 δ = thickening δ s := by simp [div_eq_mul_inv, mul_ball_one]

@[to_additive]
/-
**ball_mul_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_mul_one : ball 1 δ * s = thickening δ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_ball_one`：mul_ball_one : s * ball 1 δ = thickening δ s
-/
theorem ball_mul_one : ball 1 δ * s = thickening δ s := by rw [mul_comm, mul_ball_one]

@[to_additive]
/-
**ball_div_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_div_one : ball 1 δ / s = thickening δ s⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ball_mul_one`：ball_mul_one : ball 1 δ * s = thickening δ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ball_div_one : ball 1 δ / s = thickening δ s⁻¹ := by simp [div_eq_mul_inv, ball_mul_one]

@[to_additive (attr := simp)]
/-
**mul_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_ball : s * ball x δ = x • thickening δ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_ball_one`：smul_ball_one : x • ball (1 : E) δ = ball x δ
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `mul_ball_one`：mul_ball_one : s * ball 1 δ = thickening δ s
-/
theorem mul_ball : s * ball x δ = x • thickening δ s := by
  rw [← smul_ball_one, mul_smul_comm, mul_ball_one]

@[to_additive (attr := simp)]
/-
**div_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_ball : s / ball x δ = x⁻¹ • thickening δ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_ball`：inv_ball : (ball x δ)⁻¹ = ball x⁻¹ δ
· 使用定理 `mul_ball`：mul_ball : s * ball x δ = x • thickening δ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_ball : s / ball x δ = x⁻¹ • thickening δ s := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**ball_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_mul : ball x δ * s = x • thickening δ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_ball`：mul_ball : s * ball x δ = x • thickening δ s
-/
theorem ball_mul : ball x δ * s = x • thickening δ s := by rw [mul_comm, mul_ball]

@[to_additive (attr := simp)]
/-
**ball_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_div : ball x δ / s = x • thickening δ s⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ball_mul`：ball_mul : ball x δ * s = x • thickening δ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ball_div : ball x δ / s = x • thickening δ s⁻¹ := by simp [div_eq_mul_inv]

variable {δ s x y}

@[to_additive]
/-
**IsCompact.mul_closedBall_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.mul_closedBall_one (hs : IsCompact s) (hδ : 0 <= δ) : s * closed
Ball (1 : E) δ = cthickening δ s
参数：hs : IsCompact s；hδ : 0 <= δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.cthickening_eq_biUnion_closedBall`：∀ {α : Type u_2} [inst : Ps
eudoMetricSpace α] {δ : ℝ} {E : Set α},   IsCompact E → 0 ≤ δ → Metric.cthickeni
ng δ E = ⋃ x ∈ E, Metric.closedBa…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm_div`：dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsCompact.mul_closedBall_one (hs : IsCompact s) (hδ : 0 ≤ δ) :
    s * closedBall (1 : E) δ = cthickening δ s := by
  rw [hs.cthickening_eq_biUnion_closedBall hδ]
  ext x
  simp only [mem_mul, dist_eq_norm_div, exists_prop, mem_iUnion, mem_closedBall,
    ← eq_div_iff_mul_eq'', div_one, exists_eq_right]

@[to_additive]
/-
**IsCompact.div_closedBall_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.div_closedBall_one (hs : IsCompact s) (hδ : 0 <= δ) : s / closed
Ball 1 δ = cthickening δ s
参数：hs : IsCompact s；hδ : 0 <= δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_closedBall`：inv_closedBall : (closedBall x δ)⁻¹ = closedBall x⁻¹ δ
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `IsCompact.mul_closedBall_one`：IsCompact.mul_closedBall_one (hs : IsCompa
ct s) (hδ : 0 <= δ) : s * closedBall (1 : E) δ = cthickening δ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsCompact.div_closedBall_one (hs : IsCompact s) (hδ : 0 ≤ δ) :
    s / closedBall 1 δ = cthickening δ s := by simp [div_eq_mul_inv, hs.mul_closedBall_one hδ]

@[to_additive]
/-
**IsCompact.closedBall_one_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.closedBall_one_mul (hs : IsCompact s) (hδ : 0 <= δ) : closedBall
 1 δ * s = cthickening δ s
参数：hs : IsCompact s；hδ : 0 <= δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsCompact.mul_closedBall_one`：IsCompact.mul_closedBall_one (hs : IsCompa
ct s) (hδ : 0 <= δ) : s * closedBall (1 : E) δ = cthickening δ s
-/
theorem IsCompact.closedBall_one_mul (hs : IsCompact s) (hδ : 0 ≤ δ) :
    closedBall 1 δ * s = cthickening δ s := by rw [mul_comm, hs.mul_closedBall_one hδ]

@[to_additive]
/-
**IsCompact.closedBall_one_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.closedBall_one_div (hs : IsCompact s) (hδ : 0 <= δ) : closedBall
 1 δ / s = cthickening δ s⁻¹
参数：hs : IsCompact s；hδ : 0 <= δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsCompact.mul_closedBall_one`：IsCompact.mul_closedBall_one (hs : IsCompa
ct s) (hδ : 0 <= δ) : s * closedBall (1 : E) δ = cthickening δ s
· 使用定理 `IsCompact.inv`：IsCompact.inv (hs : IsCompact s) : IsCompact s⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `SeminormedCommGroup.toIsTopologicalGroup`：∀ {E : Type u_2} [inst : Semin
ormedCommGroup E], IsTopologicalGroup E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsCompact.closedBall_one_div (hs : IsCompact s) (hδ : 0 ≤ δ) :
    closedBall 1 δ / s = cthickening δ s⁻¹ := by
  simp [div_eq_mul_inv, mul_comm, hs.inv.mul_closedBall_one hδ]

@[to_additive]
/-
**IsCompact.mul_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.mul_closedBall (hs : IsCompact s) (hδ : 0 <= δ) (x : E) : s * cl
osedBall x δ = x • cthickening δ s
参数：hs : IsCompact s；hδ : 0 <= δ；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_closedBall_one`：smul_closedBall_one : x • closedBall (1 : E) δ = cl
osedBall x δ
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `IsCompact.mul_closedBall_one`：IsCompact.mul_closedBall_one (hs : IsCompa
ct s) (hδ : 0 <= δ) : s * closedBall (1 : E) δ = cthickening δ s
-/
theorem IsCompact.mul_closedBall (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    s * closedBall x δ = x • cthickening δ s := by
  rw [← smul_closedBall_one, mul_smul_comm, hs.mul_closedBall_one hδ]

@[to_additive]
/-
**IsCompact.div_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.div_closedBall (hs : IsCompact s) (hδ : 0 <= δ) (x : E) : s / cl
osedBall x δ = x⁻¹ • cthickening δ s
参数：hs : IsCompact s；hδ : 0 <= δ；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_closedBall`：inv_closedBall : (closedBall x δ)⁻¹ = closedBall x⁻¹ δ
· 使用定理 `IsCompact.mul_closedBall`：IsCompact.mul_closedBall (hs : IsCompact s) (h
δ : 0 <= δ) (x : E) : s * closedBall x δ = x • cthickening δ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsCompact.div_closedBall (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    s / closedBall x δ = x⁻¹ • cthickening δ s := by
  simp [div_eq_mul_inv, hs.mul_closedBall hδ]

@[to_additive]
/-
**IsCompact.closedBall_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.closedBall_mul (hs : IsCompact s) (hδ : 0 <= δ) (x : E) : closed
Ball x δ * s = x • cthickening δ s
参数：hs : IsCompact s；hδ : 0 <= δ；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsCompact.mul_closedBall`：IsCompact.mul_closedBall (hs : IsCompact s) (h
δ : 0 <= δ) (x : E) : s * closedBall x δ = x • cthickening δ s
-/
theorem IsCompact.closedBall_mul (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    closedBall x δ * s = x • cthickening δ s := by rw [mul_comm, hs.mul_closedBall hδ]

@[to_additive]
/-
**IsCompact.closedBall_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.closedBall_div (hs : IsCompact s) (hδ : 0 <= δ) (x : E) : closed
Ball x δ * s = x • cthickening δ s
参数：hs : IsCompact s；hδ : 0 <= δ；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.closedBall_mul`：IsCompact.closedBall_mul (hs : IsCompact s) (h
δ : 0 <= δ) (x : E) : closedBall x δ * s = x • cthickening δ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsCompact.closedBall_div (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    closedBall x δ * s = x • cthickening δ s := by
  simp [hs.closedBall_mul hδ]

end SeminormedCommGroup

