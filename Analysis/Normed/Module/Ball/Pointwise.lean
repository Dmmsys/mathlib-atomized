/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Pointwise
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Properties of pointwise scalar multiplication of sets in normed spaces.

We explore the relationships between scalar multiplication of sets in vector spaces, and the norm.
Notably, we express arbitrary balls as rescaling of other balls, and we show that the
multiplication of bounded sets remain bounded.
-/

public section

open Metric Set
open scoped Pointwise Topology

variable {𝕜 E : Type*}

section SMulZeroClass

variable [SeminormedAddCommGroup 𝕜] [SeminormedAddCommGroup E]
variable [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E]

/-
**ediam_smul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ediam_smul_le (c : 𝕜) (s : Set E) : ediam (c • s) <= ‖c‖₊ • ediam s
参数：c : 𝕜；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.ediam_image_le`：ediam_image_le (hf : LipschitzWith K f) (s
 : Set α) : Metric.ediam (f '' s) <= K * Metric.ediam s
· 使用定理 `lipschitzWith_smul`：lipschitzWith_smul (s : α) : LipschitzWith ‖s‖₊ (s •
 · : β -> β)
-/
theorem ediam_smul_le (c : 𝕜) (s : Set E) : ediam (c • s) ≤ ‖c‖₊ • ediam s :=
  (lipschitzWith_smul c).ediam_image_le s

end SMulZeroClass

section DivisionRing

variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E]
variable [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-
**ediam_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ediam_smul [SMul M X] [IsIsometricSMul M X] (c : M) (s : Set X) : Metric.e
diam (c • s) = Metric.ediam s
参数：c : M；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.ediam_image`：ediam_image (hf : Isometry f) (s : Set α) : Metric
.ediam (f '' s) = Metric.ediam s
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
theorem ediam_smul₀ (c : 𝕜) (s : Set E) : ediam (c • s) = ‖c‖₊ • ediam s := by
  refine le_antisymm (ediam_smul_le c s) ?_
  obtain rfl | hc := eq_or_ne c 0
  · obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    simp [zero_smul_set hs, ← Set.singleton_zero]
  · have := (lipschitzWith_smul c⁻¹).ediam_image_le (c • s)
    rwa [← smul_eq_mul, ← ENNReal.smul_def, Set.image_smul, inv_smul_smul₀ hc s, nnnorm_inv,
      le_inv_smul_iff_of_pos (nnnorm_pos.2 hc)] at this
/-
**diam_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：diam_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M) (
s : Set X) : Metric.diam (c • s) = Metric.diam s
参数：c : M；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.diam_image`：diam_image (hf : Isometry f) (s : Set α) : Metric.d
iam (f '' s) = Metric.diam s
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
theorem diam_smul₀ (c : 𝕜) (x : Set E) : diam (c • x) = ‖c‖ * diam x := by
  simp_rw [diam, ediam_smul₀, ENNReal.toReal_smul, NNReal.smul_def, coe_nnnorm, smul_eq_mul]
/-
**infEDist_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem infEDist_smul₀ {c : 𝕜} (hc : c ≠ 0) (s : Set E) (x : E) :
    infEDist (c • x) (c • s) = ‖c‖₊ • infEDist x s := by
  simp_rw [infEDist]
  have : Function.Surjective ((c • ·) : E → E) :=
    Function.RightInverse.surjective (smul_inv_smul₀ hc)
  trans ⨅ (y) (_ : y ∈ s), ‖c‖₊ • edist x y
  · refine (this.iInf_congr _ fun y => ?_).symm
    simp_rw [smul_mem_smul_set_iff₀ hc, edist_smul₀]
  · have : (‖c‖₊ : ENNReal) ≠ 0 := by simp [hc]
    simp_rw [ENNReal.smul_def, smul_eq_mul, ENNReal.mul_iInf_of_ne this ENNReal.coe_ne_top]

@[deprecated (since := "2026-01-08")] alias infEdist_smul₀ := infEDist_smul₀
/-
**infDist_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem infDist_smul₀ {c : 𝕜} (hc : c ≠ 0) (s : Set E) (x : E) :
    Metric.infDist (c • x) (c • s) = ‖c‖ * Metric.infDist x s := by
  simp_rw [Metric.infDist, infEDist_smul₀ hc s, ENNReal.toReal_smul, NNReal.smul_def, coe_nnnorm,
    smul_eq_mul]

end DivisionRing


variable [NormedField 𝕜]

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-
**smul_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_ball {c : 𝕜} (hc : c != 0) (x : E) (r : Real) : c • ball x r = ball (
c • x) (‖c‖ * r)
参数：hc : c != 0；x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_smul₀`：dist_smul₀ (s : α) (x y : β) : dist (s • x) (s • y) = ‖s‖ * 
dist x y
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem smul_ball {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) : c • ball x r = ball (c • x) (‖c‖ * r) := by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hc]
  conv_lhs => rw [← inv_smul_smul₀ hc x]
  simp [← div_eq_inv_mul, div_lt_iff₀ (norm_pos_iff.2 hc), mul_comm _ r, dist_smul₀]
/-
**smul_unitBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_unitBall {c : 𝕜} (hc : c != 0) : c • ball (0 : E) (1 : Real) = ball (
0 : E) ‖c‖
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_ball`：smul_ball {c : 𝕜} (hc : c != 0) (x : E) (r : Real) : c • ball
 x r = ball (c • x) (‖c‖ * r)
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem smul_unitBall {c : 𝕜} (hc : c ≠ 0) : c • ball (0 : E) (1 : ℝ) = ball (0 : E) ‖c‖ := by
  rw [_root_.smul_ball hc, smul_zero, mul_one]
/-
**smul_sphere'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_sphere' {c : 𝕜} (hc : c != 0) (x : E) (r : Real) : c • sphere x r = s
phere (c • x) (‖c‖ * r)
参数：hc : c != 0；x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_smul₀`：dist_smul₀ (s : α) (x y : β) : dist (s • x) (s • y) = ‖s‖ * 
dist x y
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem smul_sphere' {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) :
    c • sphere x r = sphere (c • x) (‖c‖ * r) := by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hc]
  conv_lhs => rw [← inv_smul_smul₀ hc x]
  simp only [mem_sphere, dist_smul₀, norm_inv, ← div_eq_inv_mul, div_eq_iff (norm_pos_iff.2 hc).ne',
    mul_comm r]
/-
**smul_closedBall'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_closedBall' {c : 𝕜} (hc : c != 0) (x : E) (r : Real) : c • closedBall
 x r = closedBall (c • x) (‖c‖ * r)
参数：hc : c != 0；x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.smul_set_union`：smul_set_union : a • (t₁ union t₂) = a • t₁ union a 
• t₂
· 使用定理 `smul_ball`：smul_ball {c : 𝕜} (hc : c != 0) (x : E) (r : Real) : c • ball
 x r = ball (c • x) (‖c‖ * r)
· 使用定理 `smul_sphere'`：smul_sphere' {c : 𝕜} (hc : c != 0) (x : E) (r : Real) : c 
• sphere x r = sphere (c • x) (‖c‖ * r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_closedBall' {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) :
    c • closedBall x r = closedBall (c • x) (‖c‖ * r) := by
  simp only [← ball_union_sphere, Set.smul_set_union, _root_.smul_ball hc, smul_sphere' hc]
/-
**set_smul_sphere_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：set_smul_sphere_zero {s : Set 𝕜} (hs : 0 ∉ s) (r : Real) : s • sphere (0 :
 E) r = (‖·‖) ⁻¹' ((‖·‖ * r) '' s)
参数：hs : 0 ∉ s；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_smul_left_image`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul
 α β] {s : Set α} {t : Set β}, ⋃ a ∈ s, a • t = s • t
· 使用引理 `Set.iUnion₂_congr`：iUnion₂_congr {s t : forall i, κ i -> Set α} (h : for
all i j, s i j = t i j) : ⋃ (i) (j), s i j = ⋃ (i) (j), t i j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_sphere'`：smul_sphere' {c : 𝕜} (hc : c != 0) (x : E) (r : Real) : c 
• sphere x r = sphere (c • x) (‖c‖ * r)
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem set_smul_sphere_zero {s : Set 𝕜} (hs : 0 ∉ s) (r : ℝ) :
    s • sphere (0 : E) r = (‖·‖) ⁻¹' ((‖·‖ * r) '' s) :=
  calc
    s • sphere (0 : E) r = ⋃ c ∈ s, c • sphere (0 : E) r := iUnion_smul_left_image.symm
    _ = ⋃ c ∈ s, sphere (0 : E) (‖c‖ * r) := iUnion₂_congr fun c hc ↦ by
      rw [smul_sphere' (ne_of_mem_of_not_mem hc hs), smul_zero]
    _ = (‖·‖) ⁻¹' ((‖·‖ * r) '' s) := by ext; simp [eq_comm]

/-- Image of a bounded set in a normed space under scalar multiplication by a constant is
bounded. See also `Bornology.IsBounded.smul` for a similar lemma about an isometric action. -/
/-
**Bornology.IsBounded.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bornology.IsBounded.smul [PseudoMetricSpace X] [SMul G X] [IsIsometricSMul
 G X] {s : Set X} (hs : IsBounded s) (c : G) : IsBounded (c • s)
参数：hs : IsBounded s；c : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.isBounded_image`：isBounded_image (hf : LipschitzWith K f) 
{s : Set α} (hs : IsBounded s) : IsBounded (f '' s)
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …

--- 原说明 ---
Image of a bounded set in a normed space under scalar multiplication by a consta
nt is
bounded. See also `Bornology.IsBounded.smul` for a similar lemma about an isomet
ric action.
-/
theorem Bornology.IsBounded.smul₀ {s : Set E} (hs : IsBounded s) (c : 𝕜) : IsBounded (c • s) :=
  (lipschitzWith_smul c).isBounded_image hs

/-- If `s` is a bounded set, then for small enough `r`, the set `{x} + r • s` is contained in any
fixed neighborhood of `x`. -/
/-
**eventually_singleton_add_smul_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_singleton_add_smul_subset {x : E} {s : Set E} (hs : Bornology.I
sBounded s) {u : Set E} (hu : u in 𝓝 x) : forallᶠ r in 𝓝 (0 : 𝕜), {x} + r • s su
bseteq u
参数：hs : Bornology.IsBounded s；hu : u in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `Bornology.IsBounded.subset_closedBall_lt`：∀ {α : Type u} {s : Set α} [in
st : PseudoMetricSpace α],   Bornology.IsBounded s → ∀ (a : ℝ) (c : α), ∃ r, a <
 r ∧ s ⊆ Metric.closedBall c r
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.singleton_add`：∀ {α : Type u_2} [inst : Add α] {t : Set α} {a : α}, 
{a} + t = (fun x => a + x) '' t
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `mem_closedBall_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E} {r : ℝ}, a ∈ Metric.closedBall 0 r ↔ ‖a‖ ≤ r
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
If `s` is a bounded set, then for small enough `r`, the set `{x} + r • s` is con
tained in any
fixed neighborhood of `x`.
-/
theorem eventually_singleton_add_smul_subset {x : E} {s : Set E} (hs : Bornology.IsBounded s)
    {u : Set E} (hu : u ∈ 𝓝 x) : ∀ᶠ r in 𝓝 (0 : 𝕜), {x} + r • s ⊆ u := by
  obtain ⟨ε, εpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ closedBall x ε ⊆ u := nhds_basis_closedBall.mem_iff.1 hu
  obtain ⟨R, Rpos, hR⟩ : ∃ R : ℝ, 0 < R ∧ s ⊆ closedBall 0 R := hs.subset_closedBall_lt 0 0
  have : Metric.closedBall (0 : 𝕜) (ε / R) ∈ 𝓝 (0 : 𝕜) := closedBall_mem_nhds _ (div_pos εpos Rpos)
  filter_upwards [this] with r hr
  simp only [image_add_left, singleton_add]
  intro y hy
  obtain ⟨z, zs, hz⟩ : ∃ z : E, z ∈ s ∧ r • z = -x + y := by simpa [mem_smul_set] using hy
  have I : ‖r • z‖ ≤ ε :=
    calc
      ‖r • z‖ = ‖r‖ * ‖z‖ := norm_smul _ _
      _ ≤ ε / R * R := by
        gcongr
        exacts [mem_closedBall_zero_iff.1 hr, mem_closedBall_zero_iff.1 (hR zs)]
      _ = ε := by field
  have : y = x + r • z := by simp only [hz, add_neg_cancel_left]
  apply hε
  simpa only [this, dist_eq_norm, add_sub_cancel_left, mem_closedBall] using I

variable [NormedSpace ℝ E] {x y z : E} {δ ε : ℝ}

/-- In a real normed space, the image of the unit ball under scalar multiplication by a positive
constant `r` is the ball of radius `r`. -/
/-
**smul_unitBall_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_unitBall_of_pos {r : Real} (hr : 0 < r) : r • ball (0 : E) 1 = ball (
0 : E) r
参数：hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_unitBall`：smul_unitBall {c : 𝕜} (hc : c != 0) : c • ball (0 : E) (1
 : Real) = ball (0 : E) ‖c‖
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
In a real normed space, the image of the unit ball under scalar multiplication b
y a positive
constant `r` is the ball of radius `r`.
-/
theorem smul_unitBall_of_pos {r : ℝ} (hr : 0 < r) : r • ball (0 : E) 1 = ball (0 : E) r := by
  rw [smul_unitBall hr.ne', Real.norm_of_nonneg hr.le]
/-
**Ioo_smul_sphere_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ioo_smul_sphere_zero {a b r : Real} (ha : 0 <= a) (hr : 0 < r) : Ioo a b •
 sphere (0 : E) r = ball 0 (b * r) \ closedBall 0 (a * r)
参数：ha : 0 <= a；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `set_smul_sphere_zero`：set_smul_sphere_zero {s : Set 𝕜} (hs : 0 ∉ s) (r :
 Real) : s • sphere (0 : E) r = (‖·‖) ⁻¹' ((‖·‖ * r) '' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `Set.image_mul_right_Ioo`：image_mul_right_Ioo (a b : G₀) (h : 0 < c) : (f
un x => x * c) '' Ioo a b = Ioo (a * c) (b * c)
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Ioo_smul_sphere_zero {a b r : ℝ} (ha : 0 ≤ a) (hr : 0 < r) :
    Ioo a b • sphere (0 : E) r = ball 0 (b * r) \ closedBall 0 (a * r) := by
  have : EqOn (‖·‖) id (Ioo a b) := fun x hx ↦ abs_of_pos (ha.trans_lt hx.1)
  rw [set_smul_sphere_zero (by simp [ha.not_gt]), ← image_image (· * r), this.image_eq, image_id,
    image_mul_right_Ioo _ _ hr]
  ext x; simp [and_comm]

-- This is also true for `ℚ`-normed spaces
/-
**exists_dist_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_dist_eq (x z : E) {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hab : a
 + b = 1) : exists y, dist x y = b * dist x z ∧ dist y z = a * dist x z
参数：x z : E；ha : 0 <= a；hb : 0 <= b；hab : a + b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `add_sub_add_left_eq_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c + a - (c + b) = a - b
· 使用定理 `norm_smul_of_nonneg`：norm_smul_of_nonneg {t : Real} (ht : 0 <= t) (x : E
) : ‖t • x‖ = t * ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem exists_dist_eq (x z : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ∃ y, dist x y = b * dist x z ∧ dist y z = a * dist x z := by
  use a • x + b • z
  nth_rw 1 [← one_smul ℝ x]
  nth_rw 4 [← one_smul ℝ z]
  simp [dist_eq_norm, ← hab, add_smul, ← smul_sub, norm_smul_of_nonneg, ha, hb]
/-
**exists_dist_le_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_dist_le_le (hδ : 0 <= δ) (hε : 0 <= ε) (h : dist x z <= ε + δ) : ex
ists y, dist x y <= δ ∧ dist y z <= ε
参数：hδ : 0 <= δ；hε : 0 <= ε；h : dist x z <= ε + δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `div_mul_comm`：div_mul_comm : a / b * c = c / b * a
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_le_one`：div_le_one (hb : 0 < b) : a / b <= 1 ↔ a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `exists_dist_eq`：exists_dist_eq (x z : E) {a b : Real} (ha : 0 <= a) (hb 
: 0 <= b) (hab : a + b = 1) : exists y, dist x y = b * dist x z ∧ dist y z = a *
 dis…
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem exists_dist_le_le (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (h : dist x z ≤ ε + δ) :
    ∃ y, dist x y ≤ δ ∧ dist y z ≤ ε := by
  obtain rfl | hε' := hε.eq_or_lt
  · exact ⟨z, by rwa [zero_add] at h, (dist_self _).le⟩
  have hεδ := add_pos_of_pos_of_nonneg hε' hδ
  refine (exists_dist_eq x z (div_nonneg hε <| add_nonneg hε hδ)
    (div_nonneg hδ <| add_nonneg hε hδ) <| by
      rw [← add_div, div_self hεδ.ne']).imp
    fun y hy => ?_
  rw [hy.1, hy.2, div_mul_comm, div_mul_comm ε]
  rw [← div_le_one hεδ] at h
  exact ⟨mul_le_of_le_one_left hδ h, mul_le_of_le_one_left hε h⟩

-- This is also true for `ℚ`-normed spaces
/-
**exists_dist_le_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_dist_le_lt (hδ : 0 <= δ) (hε : 0 < ε) (h : dist x z < ε + δ) : exis
ts y, dist x y <= δ ∧ dist y z < ε
参数：hδ : 0 <= δ；hε : 0 < ε；h : dist x z < ε + δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `div_mul_comm`：div_mul_comm : a / b * c = c / b * a
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_lt_of_lt_one_left`：mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 
0 < b) (h : a < 1) : a * b < b
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `exists_dist_eq`：exists_dist_eq (x z : E) {a b : Real} (ha : 0 <= a) (hb 
: 0 <= b) (hab : a + b = 1) : exists y, dist x y = b * dist x z ∧ dist y z = a *
 dis…
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem exists_dist_le_lt (hδ : 0 ≤ δ) (hε : 0 < ε) (h : dist x z < ε + δ) :
    ∃ y, dist x y ≤ δ ∧ dist y z < ε := by
  refine (exists_dist_eq x z (div_nonneg hε.le <| add_nonneg hε.le hδ)
    (div_nonneg hδ <| add_nonneg hε.le hδ) <| by
      rw [← add_div, div_self (add_pos_of_pos_of_nonneg hε hδ).ne']).imp
    fun y hy => ?_
  rw [hy.1, hy.2, div_mul_comm, div_mul_comm ε]
  rw [← div_lt_one (add_pos_of_pos_of_nonneg hε hδ)] at h
  exact ⟨mul_le_of_le_one_left hδ h.le, mul_lt_of_lt_one_left hε h⟩

-- This is also true for `ℚ`-normed spaces
/-
**exists_dist_lt_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_dist_lt_le (hδ : 0 < δ) (hε : 0 <= ε) (h : dist x z < ε + δ) : exis
ts y, dist x y < δ ∧ dist y z <= ε
参数：hδ : 0 < δ；hε : 0 <= ε；h : dist x z < ε + δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_dist_le_lt`：exists_dist_le_lt (hδ : 0 <= δ) (hε : 0 < ε) (h : dis
t x z < ε + δ) : exists y, dist x y <= δ ∧ dist y z < ε
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem exists_dist_lt_le (hδ : 0 < δ) (hε : 0 ≤ ε) (h : dist x z < ε + δ) :
    ∃ y, dist x y < δ ∧ dist y z ≤ ε := by
  obtain ⟨y, yz, xy⟩ :=
    exists_dist_le_lt hε hδ (show dist z x < δ + ε by simpa only [dist_comm, add_comm] using h)
  exact ⟨y, by simp [dist_comm x y, dist_comm y z, *]⟩

-- This is also true for `ℚ`-normed spaces
/-
**exists_dist_lt_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_dist_lt_lt (hδ : 0 < δ) (hε : 0 < ε) (h : dist x z < ε + δ) : exist
s y, dist x y < δ ∧ dist y z < ε
参数：hδ : 0 < δ；hε : 0 < ε；h : dist x z < ε + δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `div_mul_comm`：div_mul_comm : a / b * c = c / b * a
· 使用定理 `mul_lt_of_lt_one_left`：mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 
0 < b) (h : a < 1) : a * b < b
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `exists_dist_eq`：exists_dist_eq (x z : E) {a b : Real} (ha : 0 <= a) (hb 
: 0 <= b) (hab : a + b = 1) : exists y, dist x y = b * dist x z ∧ dist y z = a *
 dis…
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem exists_dist_lt_lt (hδ : 0 < δ) (hε : 0 < ε) (h : dist x z < ε + δ) :
    ∃ y, dist x y < δ ∧ dist y z < ε := by
  refine (exists_dist_eq x z (div_nonneg hε.le <| add_nonneg hε.le hδ.le)
    (div_nonneg hδ.le <| add_nonneg hε.le hδ.le) <| by
      rw [← add_div, div_self (add_pos hε hδ).ne']).imp
    fun y hy => ?_
  rw [hy.1, hy.2, div_mul_comm, div_mul_comm ε]
  rw [← div_lt_one (add_pos hε hδ)] at h
  exact ⟨mul_lt_of_lt_one_left hδ h, mul_lt_of_lt_one_left hε h⟩

-- This is also true for `ℚ`-normed spaces
/-
**disjoint_ball_ball_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_ball_ball_iff (hδ : 0 < δ) (hε : 0 < ε) : Disjoint (ball x δ) (ba
ll y ε) ↔ δ + ε <= dist x y
参数：hδ : 0 < δ；hε : 0 < ε。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `exists_dist_lt_lt`：exists_dist_lt_lt (hδ : 0 < δ) (hε : 0 < ε) (h : dist
 x z < ε + δ) : exists y, dist x y < δ ∧ dist y z < ε
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Metric.ball_disjoint_ball`：ball_disjoint_ball (h : δ + ε <= dist x y) : 
Disjoint (ball x δ) (ball y ε)
-/
theorem disjoint_ball_ball_iff (hδ : 0 < δ) (hε : 0 < ε) :
    Disjoint (ball x δ) (ball y ε) ↔ δ + ε ≤ dist x y := by
  refine ⟨fun h => le_of_not_gt fun hxy => ?_, ball_disjoint_ball⟩
  rw [add_comm] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_lt_lt hδ hε hxy
  rw [dist_comm] at hxz
  exact h.le_bot ⟨hxz, hzy⟩

-- This is also true for `ℚ`-normed spaces
/-
**disjoint_ball_closedBall_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_ball_closedBall_iff (hδ : 0 < δ) (hε : 0 <= ε) : Disjoint (ball x
 δ) (closedBall y ε) ↔ δ + ε <= dist x y
参数：hδ : 0 < δ；hε : 0 <= ε。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `exists_dist_lt_le`：exists_dist_lt_le (hδ : 0 < δ) (hε : 0 <= ε) (h : dis
t x z < ε + δ) : exists y, dist x y < δ ∧ dist y z <= ε
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Metric.ball_disjoint_closedBall`：ball_disjoint_closedBall (h : δ + ε <= 
dist x y) : Disjoint (ball x δ) (closedBall y ε)
-/
theorem disjoint_ball_closedBall_iff (hδ : 0 < δ) (hε : 0 ≤ ε) :
    Disjoint (ball x δ) (closedBall y ε) ↔ δ + ε ≤ dist x y := by
  refine ⟨fun h => le_of_not_gt fun hxy => ?_, ball_disjoint_closedBall⟩
  rw [add_comm] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_lt_le hδ hε hxy
  rw [dist_comm] at hxz
  exact h.le_bot ⟨hxz, hzy⟩

-- This is also true for `ℚ`-normed spaces
/-
**disjoint_closedBall_ball_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_closedBall_ball_iff (hδ : 0 <= δ) (hε : 0 < ε) : Disjoint (closed
Ball x δ) (ball y ε) ↔ δ + ε <= dist x y
参数：hδ : 0 <= δ；hε : 0 < ε。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `disjoint_ball_closedBall_iff`：disjoint_ball_closedBall_iff (hδ : 0 < δ) 
(hε : 0 <= ε) : Disjoint (ball x δ) (closedBall y ε) ↔ δ + ε <= dist x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_closedBall_ball_iff (hδ : 0 ≤ δ) (hε : 0 < ε) :
    Disjoint (closedBall x δ) (ball y ε) ↔ δ + ε ≤ dist x y := by
  rw [disjoint_comm, disjoint_ball_closedBall_iff hε hδ, add_comm, dist_comm]
/-
**disjoint_closedBall_closedBall_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_closedBall_closedBall_iff (hδ : 0 <= δ) (hε : 0 <= ε) : Disjoint 
(closedBall x δ) (closedBall y ε) ↔ δ + ε < dist x y
参数：hδ : 0 <= δ；hε : 0 <= ε。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `exists_dist_le_le`：exists_dist_le_le (hδ : 0 <= δ) (hε : 0 <= ε) (h : di
st x z <= ε + δ) : exists y, dist x y <= δ ∧ dist y z <= ε
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Metric.closedBall_disjoint_closedBall`：closedBall_disjoint_closedBall (h
 : δ + ε < dist x y) : Disjoint (closedBall x δ) (closedBall y ε)
-/
theorem disjoint_closedBall_closedBall_iff (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    Disjoint (closedBall x δ) (closedBall y ε) ↔ δ + ε < dist x y := by
  refine ⟨fun h => lt_of_not_ge fun hxy => ?_, closedBall_disjoint_closedBall⟩
  rw [add_comm] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_le_le hδ hε hxy
  rw [dist_comm] at hxz
  exact h.le_bot ⟨hxz, hzy⟩

open EMetric ENNReal

@[simp]
/-
**infEDist_thickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infEDist_thickening (hδ : 0 < δ) (s : Set E) (x : E) : infEDist x (thicken
ing δ s) = infEDist x s - ENNReal.ofReal δ
参数：hδ : 0 < δ；s : Set E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infEDist_zero_of_mem`：infEDist_zero_of_mem (h : x in s) : infEDis
t x s = 0
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `Metric.infEDist_le_infEDist_thickening_add`：infEDist_le_infEDist_thicken
ing_add : infEDist x s <= infEDist x (thickening δ s) + ENNReal.ofReal δ
· 使用定理 `ENNReal.le_sub_of_add_le_right`：le_sub_of_add_le_right (hb : b != ∞) : a
 + b <= c -> a <= c - b
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `Metric.le_infEDist`：le_infEDist {d} : d <= infEDist x s ↔ forall y in s,
 d <= edist x y
· 使用定理 `le_of_forall_gt`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ (
c : α), a < c → b < c) → b ≤ a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Metric.infEDist_ne_top`：infEDist_ne_top (h : s.Nonempty) : infEDist x s 
!= ∞
· 使用定理 `Metric.self_subset_thickening`：self_subset_thickening {δ : Real} (δ_pos 
: 0 < δ) (E : Set α) : E subseteq thickening δ E
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_pos_of_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRi
ghtStrictMono α] {a b : α}, b < a → 0 < a - b
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
（共 45 条，此处仅展示前 30 条）
-/
theorem infEDist_thickening (hδ : 0 < δ) (s : Set E) (x : E) :
    infEDist x (thickening δ s) = infEDist x s - ENNReal.ofReal δ := by
  obtain hs | hs := lt_or_ge (infEDist x s) (ENNReal.ofReal δ)
  · rw [infEDist_zero_of_mem, tsub_eq_zero_of_le hs.le]
    exact hs
  refine (tsub_le_iff_right.2 infEDist_le_infEDist_thickening_add).antisymm' ?_
  refine le_sub_of_add_le_right ofReal_ne_top ?_
  refine le_infEDist.2 fun z hz => le_of_forall_gt fun r h => ?_
  cases r with
  | top =>
    exact add_lt_top.2 ⟨lt_top_iff_ne_top.2 <| infEDist_ne_top ⟨z, self_subset_thickening hδ _ hz⟩,
      ofReal_lt_top⟩
  | coe r =>
    have hr : 0 < ↑r - δ := by
      refine sub_pos_of_lt ?_
      have := hs.trans_lt ((infEDist_le_edist_of_mem hz).trans_lt h)
      rw [ofReal_eq_coe_nnreal hδ.le] at this
      exact mod_cast this
    rw [edist_lt_coe, ← dist_lt_coe, ← add_sub_cancel δ ↑r] at h
    obtain ⟨y, hxy, hyz⟩ := exists_dist_lt_lt hr hδ h
    refine (ENNReal.add_lt_add_right ofReal_ne_top <|
      infEDist_lt_iff.2 ⟨_, mem_thickening_iff.2 ⟨_, hz, hyz⟩, edist_lt_ofReal.2 hxy⟩).trans_le ?_
    rw [← ofReal_add hr.le hδ.le, sub_add_cancel, ofReal_coe_nnreal]

@[deprecated (since := "2026-01-08")]
alias infEdist_thickening := infEDist_thickening

@[simp]
/-
**thickening_thickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickening_thickening (hε : 0 < ε) (hδ : 0 < δ) (s : Set E) : thickening ε
 (thickening δ s) = thickening (ε + δ) s
参数：hε : 0 < ε；hδ : 0 < δ；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Metric.thickening_thickening_subset`：thickening_thickening_subset (ε δ :
 Real) (s : Set α) : thickening ε (thickening δ s) subseteq thickening (ε + δ) s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_dist_lt_lt`：exists_dist_lt_lt (hδ : 0 < δ) (hε : 0 < ε) (h : dist
 x z < ε + δ) : exists y, dist x y < δ ∧ dist y z < ε
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem thickening_thickening (hε : 0 < ε) (hδ : 0 < δ) (s : Set E) :
    thickening ε (thickening δ s) = thickening (ε + δ) s :=
  (thickening_thickening_subset _ _ _).antisymm fun x => by
    simp_rw [mem_thickening_iff]
    rintro ⟨z, hz, hxz⟩
    rw [add_comm] at hxz
    obtain ⟨y, hxy, hyz⟩ := exists_dist_lt_lt hε hδ hxz
    exact ⟨y, ⟨_, hz, hyz⟩, hxy⟩

@[simp]
/-
**cthickening_thickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cthickening_thickening (hε : 0 <= ε) (hδ : 0 < δ) (s : Set E) : cthickenin
g ε (thickening δ s) = cthickening (ε + δ) s
参数：hε : 0 <= ε；hδ : 0 < δ；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Metric.cthickening_thickening_subset`：cthickening_thickening_subset (hε 
: 0 <= ε) (δ : Real) (s : Set α) : cthickening ε (thickening δ s) subseteq cthic
kening (ε + δ) s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `infEDist_thickening`：infEDist_thickening (hδ : 0 < δ) (s : Set E) (x : E
) : infEDist x (thickening δ s) = infEDist x s - ENNReal.ofReal δ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
-/
theorem cthickening_thickening (hε : 0 ≤ ε) (hδ : 0 < δ) (s : Set E) :
    cthickening ε (thickening δ s) = cthickening (ε + δ) s :=
  (cthickening_thickening_subset hε _ _).antisymm fun x => by
    simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ.le, infEDist_thickening hδ]
    exact tsub_le_iff_right.2

-- Note: `interior (cthickening δ s) ≠ thickening δ s` in general
@[simp]
/-
**closure_thickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_thickening (hδ : 0 < δ) (s : Set E) : closure (thickening δ s) = c
thickening δ s
参数：hδ : 0 < δ；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.cthickening_zero`：cthickening_zero (E : Set α) : cthickening 0 E 
= closure E
· 使用定理 `cthickening_thickening`：cthickening_thickening (hε : 0 <= ε) (hδ : 0 < δ
) (s : Set E) : cthickening ε (thickening δ s) = cthickening (ε + δ) s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem closure_thickening (hδ : 0 < δ) (s : Set E) :
    closure (thickening δ s) = cthickening δ s := by
  rw [← cthickening_zero, cthickening_thickening le_rfl hδ, zero_add]

@[simp]
/-
**infEDist_cthickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infEDist_cthickening (δ : Real) (s : Set E) (x : E) : infEDist x (cthicken
ing δ s) = infEDist x s - ENNReal.ofReal δ
参数：δ : Real；s : Set E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.cthickening_of_nonpos`：cthickening_of_nonpos {δ : Real} (hδ : δ <
= 0) (E : Set α) : cthickening δ E = closure E
· 使用定理 `Metric.infEDist_closure`：infEDist_closure : infEDist x (closure s) = inf
EDist x s
· 使用定理 `ENNReal.ofReal_of_nonpos`：∀ {p : ℝ}, p ≤ 0 → ENNReal.ofReal p = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_thickening`：closure_thickening (hδ : 0 < δ) (s : Set E) : closur
e (thickening δ s) = cthickening δ s
· 使用定理 `infEDist_thickening`：infEDist_thickening (hδ : 0 < δ) (s : Set E) (x : E
) : infEDist x (thickening δ s) = infEDist x s - ENNReal.ofReal δ
-/
theorem infEDist_cthickening (δ : ℝ) (s : Set E) (x : E) :
    infEDist x (cthickening δ s) = infEDist x s - ENNReal.ofReal δ := by
  obtain hδ | hδ := le_or_gt δ 0
  · rw [cthickening_of_nonpos hδ, infEDist_closure, ofReal_of_nonpos hδ, tsub_zero]
  · rw [← closure_thickening hδ, infEDist_closure, infEDist_thickening hδ]

@[deprecated (since := "2026-01-08")]
alias infEdist_cthickening := infEDist_cthickening

@[simp]
/-
**thickening_cthickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickening_cthickening (hε : 0 < ε) (hδ : 0 <= δ) (s : Set E) : thickening
 ε (cthickening δ s) = thickening (ε + δ) s
参数：hε : 0 < ε；hδ : 0 <= δ；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.cthickening_zero`：cthickening_zero (E : Set α) : cthickening 0 E 
= closure E
· 使用定理 `Metric.thickening_closure`：thickening_closure : thickening δ (closure s)
 = thickening δ s
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_thickening`：closure_thickening (hδ : 0 < δ) (s : Set E) : closur
e (thickening δ s) = cthickening δ s
· 使用定理 `thickening_thickening`：thickening_thickening (hε : 0 < ε) (hδ : 0 < δ) (
s : Set E) : thickening ε (thickening δ s) = thickening (ε + δ) s
-/
theorem thickening_cthickening (hε : 0 < ε) (hδ : 0 ≤ δ) (s : Set E) :
    thickening ε (cthickening δ s) = thickening (ε + δ) s := by
  obtain rfl | hδ := hδ.eq_or_lt
  · rw [cthickening_zero, thickening_closure, add_zero]
  · rw [← closure_thickening hδ, thickening_closure, thickening_thickening hε hδ]

@[simp]
/-
**cthickening_cthickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cthickening_cthickening (hε : 0 <= ε) (hδ : 0 <= δ) (s : Set E) : cthicken
ing ε (cthickening δ s) = cthickening (ε + δ) s
参数：hε : 0 <= ε；hδ : 0 <= δ；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Metric.cthickening_cthickening_subset`：cthickening_cthickening_subset (h
ε : 0 <= ε) (hδ : 0 <= δ) (s : Set α) : cthickening ε (cthickening δ s) subseteq
 cthickening (ε + δ) s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `infEDist_cthickening`：infEDist_cthickening (δ : Real) (s : Set E) (x : E
) : infEDist x (cthickening δ s) = infEDist x s - ENNReal.ofReal δ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
-/
theorem cthickening_cthickening (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (s : Set E) :
    cthickening ε (cthickening δ s) = cthickening (ε + δ) s :=
  (cthickening_cthickening_subset hε hδ _).antisymm fun x => by
    simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ, infEDist_cthickening]
    exact tsub_le_iff_right.2

@[simp]
/-
**thickening_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickening_ball (hε : 0 < ε) (hδ : 0 < δ) (x : E) : thickening ε (ball x δ
) = ball x (ε + δ)
参数：hε : 0 < ε；hδ : 0 < δ；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.thickening_singleton`：thickening_singleton (δ : Real) (x : X) : t
hickening δ ({x} : Set X) = ball x δ
· 使用定理 `thickening_thickening`：thickening_thickening (hε : 0 < ε) (hδ : 0 < δ) (
s : Set E) : thickening ε (thickening δ s) = thickening (ε + δ) s
-/
theorem thickening_ball (hε : 0 < ε) (hδ : 0 < δ) (x : E) :
    thickening ε (ball x δ) = ball x (ε + δ) := by
  rw [← thickening_singleton, thickening_thickening hε hδ, thickening_singleton]

@[simp]
/-
**thickening_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：thickening_closedBall (hε : 0 < ε) (hδ : 0 <= δ) (x : E) : thickening ε (c
losedBall x δ) = ball x (ε + δ)
参数：hε : 0 < ε；hδ : 0 <= δ；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.cthickening_singleton`：cthickening_singleton {α : Type*} [PseudoM
etricSpace α] (x : α) {δ : Real} (hδ : 0 <= δ) : cthickening δ ({x} : Set α) = c
losedBall x δ
· 使用定理 `thickening_cthickening`：thickening_cthickening (hε : 0 < ε) (hδ : 0 <= δ
) (s : Set E) : thickening ε (cthickening δ s) = thickening (ε + δ) s
· 使用定理 `Metric.thickening_singleton`：thickening_singleton (δ : Real) (x : X) : t
hickening δ ({x} : Set X) = ball x δ
-/
theorem thickening_closedBall (hε : 0 < ε) (hδ : 0 ≤ δ) (x : E) :
    thickening ε (closedBall x δ) = ball x (ε + δ) := by
  rw [← cthickening_singleton _ hδ, thickening_cthickening hε hδ, thickening_singleton]

@[simp]
/-
**cthickening_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cthickening_ball (hε : 0 <= ε) (hδ : 0 < δ) (x : E) : cthickening ε (ball 
x δ) = closedBall x (ε + δ)
参数：hε : 0 <= ε；hδ : 0 < δ；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.thickening_singleton`：thickening_singleton (δ : Real) (x : X) : t
hickening δ ({x} : Set X) = ball x δ
· 使用定理 `cthickening_thickening`：cthickening_thickening (hε : 0 <= ε) (hδ : 0 < δ
) (s : Set E) : cthickening ε (thickening δ s) = cthickening (ε + δ) s
· 使用定理 `Metric.cthickening_singleton`：cthickening_singleton {α : Type*} [PseudoM
etricSpace α] (x : α) {δ : Real} (hδ : 0 <= δ) : cthickening δ ({x} : Set α) = c
losedBall x δ
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem cthickening_ball (hε : 0 ≤ ε) (hδ : 0 < δ) (x : E) :
    cthickening ε (ball x δ) = closedBall x (ε + δ) := by
  rw [← thickening_singleton, cthickening_thickening hε hδ,
      cthickening_singleton _ (add_nonneg hε hδ.le)]

@[simp]
/-
**cthickening_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cthickening_closedBall (hε : 0 <= ε) (hδ : 0 <= δ) (x : E) : cthickening ε
 (closedBall x δ) = closedBall x (ε + δ)
参数：hε : 0 <= ε；hδ : 0 <= δ；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.cthickening_singleton`：cthickening_singleton {α : Type*} [PseudoM
etricSpace α] (x : α) {δ : Real} (hδ : 0 <= δ) : cthickening δ ({x} : Set α) = c
losedBall x δ
· 使用定理 `cthickening_cthickening`：cthickening_cthickening (hε : 0 <= ε) (hδ : 0 <
= δ) (s : Set E) : cthickening ε (cthickening δ s) = cthickening (ε + δ) s
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem cthickening_closedBall (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (x : E) :
    cthickening ε (closedBall x δ) = closedBall x (ε + δ) := by
  rw [← cthickening_singleton _ hδ, cthickening_cthickening hε hδ,
      cthickening_singleton _ (add_nonneg hε hδ)]
/-
**ball_add_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_add_ball (hε : 0 < ε) (hδ : 0 < δ) (a b : E) : ball a ε + ball b δ = 
ball (a + b) (ε + δ)
参数：hε : 0 < ε；hδ : 0 < δ；a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ball_add`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] (δ : ℝ) (s 
: Set E) (x : E),   Metric.ball x δ + s = x +ᵥ Metric.thickening δ s
· 使用定理 `thickening_ball`：thickening_ball (hε : 0 < ε) (hδ : 0 < δ) (x : E) : thi
ckening ε (ball x δ) = ball x (ε + δ)
· 使用定理 `Metric.vadd_ball`：∀ {G : Type v} {X : Type w} [inst : PseudoMetricSpace 
X] [inst_1 : AddGroup G] [inst_2 : AddAction G X]   [IsIsometricVAdd G X] (c : G
) (x :…
· 使用定理 `NormedAddGroup.to_isIsometricVAdd`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E], IsIsometricVAdd E E
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
-/
theorem ball_add_ball (hε : 0 < ε) (hδ : 0 < δ) (a b : E) :
    ball a ε + ball b δ = ball (a + b) (ε + δ) := by
  rw [ball_add, thickening_ball hε hδ b, Metric.vadd_ball, vadd_eq_add]
/-
**ball_sub_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_sub_ball (hε : 0 < ε) (hδ : 0 < δ) (a b : E) : ball a ε - ball b δ = 
ball (a - b) (ε + δ)
参数：hε : 0 < ε；hδ : 0 < δ；a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_ball`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] (δ : ℝ) (x 
: E), -Metric.ball x δ = Metric.ball (-x) δ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ball_add_ball`：ball_add_ball (hε : 0 < ε) (hδ : 0 < δ) (a b : E) : ball 
a ε + ball b δ = ball (a + b) (ε + δ)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ball_sub_ball (hε : 0 < ε) (hδ : 0 < δ) (a b : E) :
    ball a ε - ball b δ = ball (a - b) (ε + δ) := by
  simp_rw [sub_eq_add_neg, neg_ball, ball_add_ball hε hδ]
/-
**ball_add_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_add_closedBall (hε : 0 < ε) (hδ : 0 <= δ) (a b : E) : ball a ε + clos
edBall b δ = ball (a + b) (ε + δ)
参数：hε : 0 < ε；hδ : 0 <= δ；a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ball_add`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] (δ : ℝ) (s 
: Set E) (x : E),   Metric.ball x δ + s = x +ᵥ Metric.thickening δ s
· 使用定理 `thickening_closedBall`：thickening_closedBall (hε : 0 < ε) (hδ : 0 <= δ) 
(x : E) : thickening ε (closedBall x δ) = ball x (ε + δ)
· 使用定理 `Metric.vadd_ball`：∀ {G : Type v} {X : Type w} [inst : PseudoMetricSpace 
X] [inst_1 : AddGroup G] [inst_2 : AddAction G X]   [IsIsometricVAdd G X] (c : G
) (x :…
· 使用定理 `NormedAddGroup.to_isIsometricVAdd`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E], IsIsometricVAdd E E
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
-/
theorem ball_add_closedBall (hε : 0 < ε) (hδ : 0 ≤ δ) (a b : E) :
    ball a ε + closedBall b δ = ball (a + b) (ε + δ) := by
  rw [ball_add, thickening_closedBall hε hδ b, Metric.vadd_ball, vadd_eq_add]
/-
**ball_sub_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_sub_closedBall (hε : 0 < ε) (hδ : 0 <= δ) (a b : E) : ball a ε - clos
edBall b δ = ball (a - b) (ε + δ)
参数：hε : 0 < ε；hδ : 0 <= δ；a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_closedBall`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] (δ : 
ℝ) (x : E), -Metric.closedBall x δ = Metric.closedBall (-x) δ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ball_add_closedBall`：ball_add_closedBall (hε : 0 < ε) (hδ : 0 <= δ) (a b
 : E) : ball a ε + closedBall b δ = ball (a + b) (ε + δ)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ball_sub_closedBall (hε : 0 < ε) (hδ : 0 ≤ δ) (a b : E) :
    ball a ε - closedBall b δ = ball (a - b) (ε + δ) := by
  simp_rw [sub_eq_add_neg, neg_closedBall, ball_add_closedBall hε hδ]
/-
**closedBall_add_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedBall_add_ball (hε : 0 <= ε) (hδ : 0 < δ) (a b : E) : closedBall a ε 
+ ball b δ = ball (a + b) (ε + δ)
参数：hε : 0 <= ε；hδ : 0 < δ；a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ball_add_closedBall`：ball_add_closedBall (hε : 0 < ε) (hδ : 0 <= δ) (a b
 : E) : ball a ε + closedBall b δ = ball (a + b) (ε + δ)
-/
theorem closedBall_add_ball (hε : 0 ≤ ε) (hδ : 0 < δ) (a b : E) :
    closedBall a ε + ball b δ = ball (a + b) (ε + δ) := by
  rw [add_comm, ball_add_closedBall hδ hε b, add_comm, add_comm δ]
/-
**closedBall_sub_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedBall_sub_ball (hε : 0 <= ε) (hδ : 0 < δ) (a b : E) : closedBall a ε 
- ball b δ = ball (a - b) (ε + δ)
参数：hε : 0 <= ε；hδ : 0 < δ；a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_ball`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] (δ : ℝ) (x 
: E), -Metric.ball x δ = Metric.ball (-x) δ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `closedBall_add_ball`：closedBall_add_ball (hε : 0 <= ε) (hδ : 0 < δ) (a b
 : E) : closedBall a ε + ball b δ = ball (a + b) (ε + δ)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closedBall_sub_ball (hε : 0 ≤ ε) (hδ : 0 < δ) (a b : E) :
    closedBall a ε - ball b δ = ball (a - b) (ε + δ) := by
  simp_rw [sub_eq_add_neg, neg_ball, closedBall_add_ball hε hδ]
/-
**closedBall_add_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedBall_add_closedBall [ProperSpace E] (hε : 0 <= ε) (hδ : 0 <= δ) (a b
 : E) : closedBall a ε + closedBall b δ = closedBall (a + b) (ε + δ)
参数：hε : 0 <= ε；hδ : 0 <= δ；a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.add_closedBall`：∀ {E : Type u_1} [inst : SeminormedAddCommGrou
p E] {δ : ℝ} {s : Set E},   IsCompact s → 0 ≤ δ → ∀ (x : E), s + Metric.closedBa
ll x δ = x +ᵥ …
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `cthickening_closedBall`：cthickening_closedBall (hε : 0 <= ε) (hδ : 0 <= 
δ) (x : E) : cthickening ε (closedBall x δ) = closedBall x (ε + δ)
· 使用定理 `Metric.vadd_closedBall`：∀ {G : Type v} {X : Type w} [inst : PseudoMetric
Space X] [inst_1 : AddGroup G] [inst_2 : AddAction G X]   [IsIsometricVAdd G X] 
(c : G) (x :…
· 使用定理 `NormedAddGroup.to_isIsometricVAdd`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E], IsIsometricVAdd E E
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem closedBall_add_closedBall [ProperSpace E] (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (a b : E) :
    closedBall a ε + closedBall b δ = closedBall (a + b) (ε + δ) := by
  rw [(isCompact_closedBall _ _).add_closedBall hδ b, cthickening_closedBall hδ hε a,
    Metric.vadd_closedBall, vadd_eq_add, add_comm, add_comm δ]
/-
**closedBall_sub_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedBall_sub_closedBall [ProperSpace E] (hε : 0 <= ε) (hδ : 0 <= δ) (a b
 : E) : closedBall a ε - closedBall b δ = closedBall (a - b) (ε + δ)
参数：hε : 0 <= ε；hδ : 0 <= δ；a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_closedBall`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] (δ : 
ℝ) (x : E), -Metric.closedBall x δ = Metric.closedBall (-x) δ
· 使用定理 `closedBall_add_closedBall`：closedBall_add_closedBall [ProperSpace E] (hε
 : 0 <= ε) (hδ : 0 <= δ) (a b : E) : closedBall a ε + closedBall b δ = closedBal
l (a + b) (ε + …
-/
theorem closedBall_sub_closedBall [ProperSpace E] (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (a b : E) :
    closedBall a ε - closedBall b δ = closedBall (a - b) (ε + δ) := by
  rw [sub_eq_add_neg, neg_closedBall, closedBall_add_closedBall hε hδ, sub_eq_add_neg]

end SeminormedAddCommGroup

section NormedAddCommGroup

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-
**smul_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_closedBall (c : 𝕜) (x : E) {r : Real} (hr : 0 <= r) : c • closedBall 
x r = closedBall (c • x) (‖c‖ * r)
参数：c : 𝕜；x : E；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Metric.closedBall_zero`：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, M
etric.closedBall x 0 = {x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_closedBall'`：smul_closedBall' {c : 𝕜} (hc : c != 0) (x : E) (r : Re
al) : c • closedBall x r = closedBall (c • x) (‖c‖ * r)
-/
theorem smul_closedBall (c : 𝕜) (x : E) {r : ℝ} (hr : 0 ≤ r) :
    c • closedBall x r = closedBall (c • x) (‖c‖ * r) := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp [hr, zero_smul_set, Set.singleton_zero, nonempty_closedBall]
  · exact smul_closedBall' hc x r
/-
**smul_unitClosedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_unitClosedBall (c : 𝕜) : c • closedBall (0 : E) (1 : Real) = closedBa
ll (0 : E) ‖c‖
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_closedBall`：smul_closedBall (c : 𝕜) (x : E) {r : Real} (hr : 0 <= r
) : c • closedBall x r = closedBall (c • x) (‖c‖ * r)
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem smul_unitClosedBall (c : 𝕜) : c • closedBall (0 : E) (1 : ℝ) = closedBall (0 : E) ‖c‖ := by
  rw [_root_.smul_closedBall _ _ zero_le_one, smul_zero, mul_one]

variable [NormedSpace ℝ E]

/-- In a real normed space, the image of the unit closed ball under multiplication by a nonnegative
number `r` is the closed ball of radius `r` with center at the origin. -/
/-
**smul_unitClosedBall_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_unitClosedBall_of_nonneg {r : Real} (hr : 0 <= r) : r • closedBall (0
 : E) 1 = closedBall (0 : E) r
参数：hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_unitClosedBall`：smul_unitClosedBall (c : 𝕜) : c • closedBall (0 : E
) (1 : Real) = closedBall (0 : E) ‖c‖
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r

--- 原说明 ---
In a real normed space, the image of the unit closed ball under multiplication b
y a nonnegative
number `r` is the closed ball of radius `r` with center at the origin.
-/
theorem smul_unitClosedBall_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    r • closedBall (0 : E) 1 = closedBall (0 : E) r := by
  rw [smul_unitClosedBall, Real.norm_of_nonneg hr]
/-
**smul_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_sphere [Nontrivial E] (c : 𝕜) (x : E) {r : Real} (hr : 0 <= r) : c • 
sphere x r = sphere (c • x) (‖c‖ * r)
参数：c : 𝕜；x : E；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Metric.sphere_zero`：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, Metri
c.sphere x 0 = {x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_sphere'`：smul_sphere' {c : 𝕜} (hc : c != 0) (x : E) (r : Real) : c 
• sphere x r = sphere (c • x) (‖c‖ * r)
-/
theorem smul_sphere [Nontrivial E] (c : 𝕜) (x : E) {r : ℝ} (hr : 0 ≤ r) :
    c • sphere x r = sphere (c • x) (‖c‖ * r) := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp [zero_smul_set, Set.singleton_zero, hr]
  · exact smul_sphere' hc x r

/-- Any ball `Metric.ball x r`, `0 < r` is the image of the unit ball under `fun y ↦ x + r • y`. -/
/-
**affinity_unitBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affinity_unitBall {r : Real} (hr : 0 < r) (x : E) : x +ᵥ r • ball (0 : E) 
1 = ball x r
参数：hr : 0 < r；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_unitBall_of_pos`：smul_unitBall_of_pos {r : Real} (hr : 0 < r) : r •
 ball (0 : E) 1 = ball (0 : E) r
· 使用定理 `vadd_ball_zero`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] (δ : 
ℝ) (x : E), x +ᵥ Metric.ball 0 δ = Metric.ball x δ

--- 原说明 ---
Any ball `Metric.ball x r`, `0 < r` is the image of the unit ball under `fun y ↦
 x + r • y`.
-/
theorem affinity_unitBall {r : ℝ} (hr : 0 < r) (x : E) : x +ᵥ r • ball (0 : E) 1 = ball x r := by
  rw [smul_unitBall_of_pos hr, vadd_ball_zero]

/-- Any closed ball `Metric.closedBall x r`, `0 ≤ r` is the image of the unit closed ball under
`fun y ↦ x + r • y`. -/
/-
**affinity_unitClosedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affinity_unitClosedBall {r : Real} (hr : 0 <= r) (x : E) : x +ᵥ r • closed
Ball (0 : E) 1 = closedBall x r
参数：hr : 0 <= r；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_unitClosedBall`：smul_unitClosedBall (c : 𝕜) : c • closedBall (0 : E
) (1 : Real) = closedBall (0 : E) ‖c‖
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `vadd_closedBall_zero`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E]
 (δ : ℝ) (x : E), x +ᵥ Metric.closedBall 0 δ = Metric.closedBall x δ

--- 原说明 ---
Any closed ball `Metric.closedBall x r`, `0 ≤ r` is the image of the unit closed
 ball under
`fun y ↦ x + r • y`.
-/
theorem affinity_unitClosedBall {r : ℝ} (hr : 0 ≤ r) (x : E) :
    x +ᵥ r • closedBall (0 : E) 1 = closedBall x r := by
  rw [smul_unitClosedBall, Real.norm_of_nonneg hr, vadd_closedBall_zero]

end NormedAddCommGroup

