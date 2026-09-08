/-
Copyright (c) 2024 Yaël Dillies, Kalle Kytölä, Kin Yau James Wong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kalle Kytölä, Kin Yau James Wong
-/
module

public import Mathlib.Probability.Kernel.Composition.CompNotation

/-!
# Proper kernels

This file defines properness of measure kernels.

For two σ-algebras `𝓑 ≤ 𝓧`, a `𝓑, 𝓧`-kernel `π : X → Measure X` is proper if
`∫ x, g x * f x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀)` for all `x₀ : X`, `𝓧`-measurable function `f`
and `𝓑`-measurable function `g`.

By the standard machine, this is equivalent to having that, for all `B ∈ 𝓑`, `π` restricted to `B`
is the same as `π` times the indicator of `B`.

This should be thought of as the condition under which one can meaningfully restrict a kernel to an
event.

## TODO

Prove the `integral` versions of the `lintegral` lemmas below
-/

public section

open MeasureTheory ENNReal NNReal Set
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {A B : Set X}
  {f g : X → ℝ≥0∞} {x₀ : X}

/-- For two σ-algebras `𝓑 ≤ 𝓧` on a space `X`, a `𝓑, 𝓧`-kernel `π : X → Measure X` is proper if
`∫ x, g x * f x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀)` for all `x₀ : X`, `𝓧`-measurable function `f`
and `𝓑`-measurable function `g`.

By the standard machine, this is equivalent to having that, for all `B ∈ 𝓑`, `π` restricted to `B`
is the same as `π` times the indicator of `B`.

To avoid assuming `𝓑 ≤ 𝓧` in the definition, we replace `𝓑` by `𝓑 ⊓ 𝓧` in the restriction. -/
/-
**ProbabilityTheory.Kernel.IsProper** 是 Mathlib 中的一个结构，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：IsProper (π : Kernel[𝓑, 𝓧] X X) : Prop where restrict_eq_indicator_smul' :
 forall ⦃B : Set X⦄ (hB : MeasurableSet[𝓑 ⊓ 𝓧] B) (x : X), π.restrict (inf_le_ri
ght (b
参数：π : Kernel[𝓑, 𝓧] X X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For two σ-algebras `𝓑 ≤ 𝓧` on a space `X`, a `𝓑, 𝓧`-kernel `π : X → Measure X` i
s proper if
`∫ x, g x * f x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀)` for all `x₀ : X`, `𝓧`-measura
ble function `f`
and `𝓑`-measurable function `g`.

By the standard machine, this is equivalent to having that, for all `B ∈ 𝓑`, `π`
 restricted to `B`
is the same as `π` times the indicator of `B`.

To avoid assuming `𝓑 ≤ 𝓧` in the definition, we replace `𝓑` by `𝓑 ⊓ 𝓧` in the re
striction.
-/
structure IsProper (π : Kernel[𝓑, 𝓧] X X) : Prop where
  restrict_eq_indicator_smul' :
    ∀ ⦃B : Set X⦄ (hB : MeasurableSet[𝓑 ⊓ 𝓧] B) (x : X),
      π.restrict (inf_le_right (b := 𝓧) _ hB) x = B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x • π x
/-
**ProbabilityTheory.Kernel.isProper_iff_restrict_eq_indicator_smul** 是 Mathlib 中
的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：isProper_iff_restrict_eq_indicator_smul (h𝓑𝓧 : 𝓑 <= 𝓧) : IsProper π ↔ fora
ll ⦃B : Set X⦄ (hB : MeasurableSet[𝓑] B) (x : X), π.restrict (h𝓑𝓧 _ hB) x = B.in
dicator (fun _ => (1 : Real>=0∞)) x • π x
参数：h𝓑𝓧 : 𝓑 <= 𝓧。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
-/
lemma isProper_iff_restrict_eq_indicator_smul (h𝓑𝓧 : 𝓑 ≤ 𝓧) :
    IsProper π ↔ ∀ ⦃B : Set X⦄ (hB : MeasurableSet[𝓑] B) (x : X),
      π.restrict (h𝓑𝓧 _ hB) x = B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x • π x := by
  refine ⟨fun ⟨h⟩ ↦ ?_, fun h ↦ ⟨?_⟩⟩ <;> simpa +instances only [inf_eq_left.2 h𝓑𝓧] using h
/-
**ProbabilityTheory.Kernel.isProper_iff_inter_eq_indicator_mul** 是 Mathlib 中的一个引
理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：isProper_iff_inter_eq_indicator_mul (h𝓑𝓧 : 𝓑 <= 𝓧) : IsProper π ↔ forall ⦃
A : Set X⦄ (_hA : MeasurableSet[𝓧] A) ⦃B : Set X⦄ (_hB : MeasurableSet[𝓑] B) (x 
: X), π x (A inter B) = B.indicator 1 x * π x A
参数：h𝓑𝓧 : 𝓑 <= 𝓧。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `ProbabilityTheory.Kernel.isProper_iff_restrict_eq_indicator_smul`：isProp
er_iff_restrict_eq_indicator_smul (h𝓑𝓧 : 𝓑 <= 𝓧) : IsProper π ↔ forall ⦃B : Set 
X⦄ (hB : MeasurableSet[𝓑] B) (x : X), π.restrict (h𝓑𝓧 …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `ProbabilityTheory.Kernel.restrict_apply`：restrict_apply (κ : Kernel α β)
 (hs : MeasurableSet s) (a : α) : κ.restrict hs a = (κ a).restrict s
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isProper_iff_inter_eq_indicator_mul (h𝓑𝓧 : 𝓑 ≤ 𝓧) :
    IsProper π ↔
      ∀ ⦃A : Set X⦄ (_hA : MeasurableSet[𝓧] A) ⦃B : Set X⦄ (_hB : MeasurableSet[𝓑] B) (x : X),
        π x (A ∩ B) = B.indicator 1 x * π x A := by
  calc
    _ ↔ ∀ ⦃A : Set X⦄ (_hA : MeasurableSet[𝓧] A) ⦃B : Set X⦄ (hB : MeasurableSet[𝓑] B) (x : X),
          π.restrict (h𝓑𝓧 _ hB) x A = B.indicator 1 x * π x A := by
      simp [isProper_iff_restrict_eq_indicator_smul h𝓑𝓧, Measure.ext_iff]; aesop
    _ ↔ _ := by congr! 5 with A hA B hB x; rw [restrict_apply, Measure.restrict_apply hA]

alias ⟨IsProper.restrict_eq_indicator_smul, IsProper.of_restrict_eq_indicator_smul⟩ :=
  isProper_iff_restrict_eq_indicator_smul

alias ⟨IsProper.inter_eq_indicator_mul, IsProper.of_inter_eq_indicator_mul⟩ :=
  isProper_iff_inter_eq_indicator_mul
/-
**ProbabilityTheory.Kernel.IsProper.setLIntegral_eq_comp** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.Kernel.IsProper`。
形式化陈述：∀ {X : Type u_1} {𝓑 𝓧 : MeasurableSpace X} {π : ProbabilityTheory.Kernel X
 X} {A B : Set X},   π.IsProper →     𝓑 ≤ 𝓧 →       ∀ {μ : MeasureTheory.Measure
 X},         MeasurableSet A → MeasurableSet B → ∫⁻ (a : X) in B, (π a) A ∂μ = (
μ.bind ⇑π) (A ∩ B)
参数：a : X；π a；μ.bind ⇑π；A ∩ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用引理 `ProbabilityTheory.Kernel.measurable`：measurable (κ : Kernel α β) : Measu
rable κ
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.Kernel.IsProper.inter_eq_indicator_mul`：∀ {X : Type u_
1} {𝓑 𝓧 : MeasurableSpace X} {π : ProbabilityTheory.Kernel X X},   𝓑 ≤ 𝓧 →     π
.IsProper →       ∀ ⦃A : Set X⦄,         Measu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
-/
lemma IsProper.setLIntegral_eq_comp (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧) {μ : Measure[𝓧] X}
    (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) :
    ∫⁻ a in B, π a A ∂μ = (π ∘ₘ μ) (A ∩ B) := by
  rw [Measure.bind_apply (by measurability) (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable]
  simp only [hπ.inter_eq_indicator_mul h𝓑𝓧 hA hB, ← indicator_mul_const, Pi.one_apply, one_mul]
  rw [← lintegral_indicator (h𝓑𝓧 _ hB)]
  rfl

/-- Auxiliary lemma for `IsProper.lintegral_mul` and
`IsProper.setLIntegral_eq_indicator_mul_lintegral`. -/
/-
**ProbabilityTheory.Kernel.IsProper.lintegral_indicator_mul_indicator** 是 Mathli
b 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for `IsProper.lintegral_mul` and
`IsProper.setLIntegral_eq_indicator_mul_lintegral`.
-/
private lemma IsProper.lintegral_indicator_mul_indicator (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) :
    ∫⁻ x, B.indicator 1 x * A.indicator 1 x ∂(π x₀) =
      B.indicator 1 x₀ * ∫⁻ x, A.indicator 1 x ∂(π x₀) := by
  simp_rw [← inter_indicator_mul]
  rw [lintegral_indicator ((h𝓑𝓧 _ hB).inter hA), lintegral_indicator hA]
  simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    Pi.one_apply, one_mul]
  rw [← hπ.inter_eq_indicator_mul h𝓑𝓧 hA hB, inter_comm]

/-- Auxiliary lemma for `IsProper.lintegral_mul` and
`IsProper.setLIntegral_eq_indicator_mul_lintegral`. -/
/-
**ProbabilityTheory.Kernel.IsProper.lintegral_indicator_mul** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory.Kernel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for `IsProper.lintegral_mul` and
`IsProper.setLIntegral_eq_indicator_mul_lintegral`.
-/
private lemma IsProper.lintegral_indicator_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hf : Measurable[𝓧] f) (hB : MeasurableSet[𝓑] B) :
    ∫⁻ x, B.indicator 1 x * f x ∂(π x₀) = B.indicator 1 x₀ * ∫⁻ x, f x ∂(π x₀) := by
  refine hf.ennreal_induction ?_ ?_ ?_
  · rintro c A hA
    simp_rw [← smul_indicator_one_apply, mul_smul_comm, smul_eq_mul]
    rw [lintegral_const_mul, lintegral_const_mul, hπ.lintegral_indicator_mul_indicator h𝓑𝓧 hA hB,
      mul_left_comm] <;> measurability
  · rintro f₁ f₂ - _ _ hf₁ hf₂
    simp only [Pi.add_apply, mul_add]
    rw [lintegral_add_right, lintegral_add_right, hf₁, hf₂, mul_add] <;> measurability
  · rintro f' hf'_meas hf'_mono hf'
    simp_rw [ENNReal.mul_iSup]
    rw [lintegral_iSup (by measurability), lintegral_iSup hf'_meas hf'_mono, ENNReal.mul_iSup]
    · simp_rw [hf']
    · exact hf'_mono.const_mul zero_le
/-
**ProbabilityTheory.Kernel.IsProper.setLIntegral_eq_indicator_mul_lintegral** 是 
Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.Kernel.IsProper`。
形式化陈述：∀ {X : Type u_1} {𝓑 𝓧 : MeasurableSpace X} {π : ProbabilityTheory.Kernel X
 X} {B : Set X} {f : X → ENNReal},   π.IsProper →     𝓑 ≤ 𝓧 →       Measurable f
 → MeasurableSet B → ∀ (x₀ : X), ∫⁻ (x : X) in B, f x ∂π x₀ = B.indicator 1 x₀ *
 ∫⁻ (x : X), f x ∂π x₀
参数：x₀ : X；x : X；x : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Probability.Kernel.Proper.0.ProbabilityTheory.Kernel.Is
Proper.lintegral_indicator_mul`：∀ {X : Type u_1} {𝓑 𝓧 : MeasurableSpace X} {π : 
ProbabilityTheory.Kernel X X} {B : Set X} {f : X → ENNReal} {x₀ : X},   π.IsProp
er →     𝓑 ≤…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsProper.setLIntegral_eq_indicator_mul_lintegral (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hf : Measurable[𝓧] f) (hB : MeasurableSet[𝓑] B) (x₀ : X) :
    ∫⁻ x in B, f x ∂(π x₀) = B.indicator 1 x₀ * ∫⁻ x, f x ∂(π x₀) := by
  simp [← hπ.lintegral_indicator_mul h𝓑𝓧 hf hB, ← indicator_mul_left,
    lintegral_indicator (h𝓑𝓧 _ hB)]
/-
**ProbabilityTheory.Kernel.IsProper.setLIntegral_inter_eq_indicator_mul_setLInte
gral** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.Kernel.IsProper`。
形式化陈述：∀ {X : Type u_1} {𝓑 𝓧 : MeasurableSpace X} {π : ProbabilityTheory.Kernel X
 X} {A B : Set X} {f : X → ENNReal},   π.IsProper →     𝓑 ≤ 𝓧 →       Measurable
 f →         MeasurableSet A →           MeasurableSet B → ∀ (x₀ : X), ∫⁻ (x : X
) in A ∩ B, f x ∂π x₀ = B.indicator 1 x₀ * ∫⁻ (x : X) in A, f x ∂π x₀
参数：x₀ : X；x : X；x : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `ProbabilityTheory.Kernel.IsProper.setLIntegral_eq_indicator_mul_lintegra
l`：∀ {X : Type u_1} {𝓑 𝓧 : MeasurableSpace X} {π : ProbabilityTheory.Kernel X X}
 {B : Set X} {f : X → ENNReal},   π.IsProper →     𝓑 ≤ 𝓧 →     …
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用引理 `MeasureTheory.setLIntegral_indicator`：setLIntegral_indicator {s t : Set 
α} (hs : MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a in t, s.indicator f a ∂μ = 
∫⁻ a in s inter t, f a ∂μ
-/
lemma IsProper.setLIntegral_inter_eq_indicator_mul_setLIntegral (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hf : Measurable[𝓧] f) (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) (x₀ : X) :
    ∫⁻ x in A ∩ B, f x ∂(π x₀) = B.indicator 1 x₀ * ∫⁻ x in A, f x ∂(π x₀) := by
  rw [← lintegral_indicator hA, ← hπ.setLIntegral_eq_indicator_mul_lintegral h𝓑𝓧 _ hB,
    setLIntegral_indicator] <;> measurability
/-
**ProbabilityTheory.Kernel.IsProper.lintegral_mul** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel.IsProper`。
形式化陈述：∀ {X : Type u_1} {𝓑 𝓧 : MeasurableSpace X} {π : ProbabilityTheory.Kernel X
 X} {f g : X → ENNReal},   π.IsProper →     𝓑 ≤ 𝓧 → Measurable f → Measurable g 
→ ∀ (x₀ : X), ∫⁻ (x : X), g x * f x ∂π x₀ = g x₀ * ∫⁻ (x : X), f x ∂π x₀
参数：x₀ : X；x : X；x : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.ennreal_induction`：Measurable.ennreal_induction {motive : (α 
-> Real>=0∞) -> Prop} (indicator : forall (c : Real>=0∞) ⦃s⦄, MeasurableSet s ->
 motive (Set.indic…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.lintegral_const_mul`：lintegral_const_mul (r : Real>=0∞) {f
 : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)
· 使用定理 `_private.Mathlib.Probability.Kernel.Proper.0.ProbabilityTheory.Kernel.Is
Proper.lintegral_indicator_mul`：∀ {X : Type u_1} {𝓑 𝓧 : MeasurableSpace X} {π : 
ProbabilityTheory.Kernel X X} {B : Set X} {f : X → ENNReal} {x₀ : X},   π.IsProp
er →     𝓑 ≤…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `MeasureTheory.lintegral_add_right`：lintegral_add_right (f : α -> Real>=0
∞) {g : α -> Real>=0∞} (hg : Measurable g) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ +
 ∫⁻ a, g a ∂μ
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `ENNReal.iSup_mul`：iSup_mul (f : ι -> Real>=0∞) (a : Real>=0∞) : (⨆ i, f 
i) * a = ⨆ i, f i * a
· 使用定理 `MeasureTheory.lintegral_iSup`：lintegral_iSup {f : Nat -> α -> Real>=0∞} 
(hf : forall n, Measurable (f n)) (h_mono : Monotone f) : ∫⁻ a, ⨆ n, f n a ∂μ = 
⨆ n, ∫⁻ a, f n a ∂…
· 使用引理 `Monotone.mul_const`：Monotone.mul_const [MulPosMono M₀] (hf : Monotone f)
 (ha : 0 <= a) : Monotone fun x => f x * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Pi.instCanonicallyOrderedAddForall`：∀ {ι : Type u_6} {Z : ι → Type u_7} 
[inst : (i : ι) → AddMonoid (Z i)] [inst_1 : (i : ι) → PartialOrder (Z i)]   [∀ 
(i : ι), CanonicallyOrde…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsProper.lintegral_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hf : Measurable[𝓧] f)
    (hg : Measurable[𝓑] g) (x₀ : X) :
    ∫⁻ x, g x * f x ∂(π x₀) = g x₀ * ∫⁻ x, f x ∂(π x₀) := by
  refine hg.ennreal_induction ?_ ?_ ?_
  · rintro c A hA
    simp_rw [← smul_indicator_one_apply, smul_mul_assoc, smul_eq_mul]
    rw [lintegral_const_mul, hπ.lintegral_indicator_mul h𝓑𝓧 hf hA]
    · measurability
  · rintro g₁ g₂ - _ hg₂_meas hg₁ hg₂
    simp only [Pi.add_apply, add_mul]
    rw [lintegral_add_right, hg₁, hg₂]
    · exact (hg₂_meas.mono h𝓑𝓧 le_rfl).mul hf
  · rintro g' hg'_meas hg'_mono hg'
    simp_rw [ENNReal.iSup_mul]
    rw [lintegral_iSup (fun n ↦ ((hg'_meas _).mono h𝓑𝓧 le_rfl).fun_mul hf)
      (hg'_mono.mul_const zero_le)]
    simp_rw [hg']

end ProbabilityTheory.Kernel

