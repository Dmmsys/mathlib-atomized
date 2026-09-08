/-
Copyright (c) 2026 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# `L^p`-seminorms on `count` and `dirac`
-/

public section

open MeasureTheory Measure ENNReal Set Filter
variable {α ε : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε} {p : ℝ≥0∞} {x : α}

namespace MeasureTheory

@[simp]
/-
**MeasureTheory.eLpNorm_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_dirac (f : α -> ε) (i : α) (hp : p != 0) : eLpNorm f p (dirac i) =
 ‖f i‖ₑ
参数：f : α -> ε；i : α；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `csInf_Ici`：csInf_Ici {α : Type*} [ConditionallyCompletePartialOrderInf α
] {a : α} : sInf (Ici a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.lintegral_dirac`：lintegral_dirac [MeasurableSingletonClass
 α] (a : α) (f : α -> Real>=0∞) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.rpow_rpow_inv`：∀ {y : ℝ}, y ≠ 0 → ∀ (x : ENNReal), (x ^ y) ^ y⁻¹
 = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma eLpNorm_dirac (f : α → ε) (i : α) (hp : p ≠ 0) :
    eLpNorm f p (dirac i) = ‖f i‖ₑ := by
  simp_rw [eLpNorm, if_neg hp]
  split_ifs
  · simp [eLpNormEssSup, essSup, limsup, limsSup, Set.Ici_def]
  · simp [eLpNorm', ENNReal.toReal_eq_zero_iff, *]
/-
**MeasureTheory.enorm_le_eLpNorm_count** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：enorm_le_eLpNorm_count (f : α -> ε) (i : α) (hp : p != 0) : ‖f i‖ₑ <= eLpN
orm f p count
参数：f : α -> ε；i : α；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.eLpNorm_dirac`：eLpNorm_dirac (f : α -> ε) (i : α) (hp : p 
!= 0) : eLpNorm f p (dirac i) = ‖f i‖ₑ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.restrict_singleton`：restrict_singleton (μ : Measur
e α) (a : α) : μ.restrict {a} = μ {a} • dirac a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.count_singleton'`：count_singleton' {a : α} (ha : M
easurableSet ({a} : Set α)) : count ({a} : Set α) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.eLpNorm_restrict_le`：eLpNorm_restrict_le (f : α -> ε') (p 
: Real>=0∞) (μ : Measure α) (s : Set α) : eLpNorm f p (μ.restrict s) <= eLpNorm 
f p μ
-/
lemma enorm_le_eLpNorm_count (f : α → ε) (i : α) (hp : p ≠ 0) :
    ‖f i‖ₑ ≤ eLpNorm f p count := by
  calc
    ‖f i‖ₑ = eLpNorm f p (dirac i) := by rw [eLpNorm_dirac f i hp]
      _ = eLpNorm f p (count.restrict {i}) := by simp
      _ ≤ eLpNorm f p count := eLpNorm_restrict_le ..

omit [MeasurableSingletonClass α] in
/-
**MeasureTheory.eLpNorm_count_lt_top_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：eLpNorm_count_lt_top_of_lt [Finite α] (h : forall i, ‖f i‖ₑ < ∞) : eLpNorm
 f p .count < ∞
参数：h : forall i, ‖f i‖ₑ < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNorm_mono_enorm`：eLpNorm_mono_enorm {f : α -> ε} {g : α
 -> ε'} (h : forall x, ‖f x‖ₑ <= ‖g x‖ₑ) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `MeasureTheory.MemLp.eLpNorm_lt_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
· 使用定理 `MeasureTheory.memLp_const_enorm`：memLp_const_enorm {c : ε'} (hc : ‖c‖ₑ !
= ⊤) [IsFiniteMeasure μ] : MemLp (fun _ : α => c) p μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.Measure.count.isFiniteMeasure`：∀ {α : Type u_1} [inst : Me
asurableSpace α] [Finite α], MeasureTheory.IsFiniteMeasure MeasureTheory.Measure
.count
-/
lemma eLpNorm_count_lt_top_of_lt [Finite α] (h : ∀ i, ‖f i‖ₑ < ∞) : eLpNorm f p .count < ∞ := by
  have := Fintype.ofFinite α
  refine (eLpNorm_mono_enorm (g := fun _ ↦ Finset.univ.sup (‖f ·‖ₑ)) ?_).trans_lt ?_
  · exact fun x ↦ Finset.le_sup (f := (‖f ·‖ₑ)) (Finset.mem_univ x)
  · exact (memLp_const_enorm <| by simp [h, LT.lt.ne]).eLpNorm_lt_top
/-
**MeasureTheory.eLpNorm_count_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_count_lt_top [Finite α] (hp : p != 0) : eLpNorm f p .count < ∞ ↔ f
orall i, ‖f i‖ₑ < ∞
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `MeasureTheory.enorm_le_eLpNorm_count`：enorm_le_eLpNorm_count (f : α -> ε
) (i : α) (hp : p != 0) : ‖f i‖ₑ <= eLpNorm f p count
· 使用引理 `MeasureTheory.eLpNorm_count_lt_top_of_lt`：eLpNorm_count_lt_top_of_lt [Fi
nite α] (h : forall i, ‖f i‖ₑ < ∞) : eLpNorm f p .count < ∞
-/
lemma eLpNorm_count_lt_top [Finite α] (hp : p ≠ 0) :
    eLpNorm f p .count < ∞ ↔ ∀ i, ‖f i‖ₑ < ∞ :=
  ⟨fun h i ↦ (enorm_le_eLpNorm_count f i hp).trans_lt h, eLpNorm_count_lt_top_of_lt⟩

end MeasureTheory

