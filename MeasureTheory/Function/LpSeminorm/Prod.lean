/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# ℒp spaces and products

-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α β ε : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [TopologicalSpace ε] [ContinuousENorm ε]
  {μ : Measure α} {ν : Measure β} {p : ℝ≥0∞}

/-
**MeasureTheory.MemLp.comp_fst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ε : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε
] {μ : MeasureTheory.Measure α} {p : ENNReal} {f : α → ε},   MeasureTheory.MemLp
 f p μ →     ∀ (ν : MeasureTheory.Measure β) [MeasureTheory.IsFiniteMeasure ν], 
MeasureTheory.MemLp (fun x => f x.1) p (μ.prod ν)
参数：ν : MeasureTheory.Measure β；fun x => f x.1；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.MemLp.smul_measure`：∀ {α : Type u_1} {m0 : MeasurableSpace
 α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topolog
icalSpace ε] [inst_1 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_map_measure_iff`：memLp_map_measure_iff (hg : AEStron
glyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) : MemLp g p (Measure.
map f μ) ↔ MemLp (g ∘ f) …
· 使用定理 `MeasureTheory.Measure.map_fst_prod`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α
}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
-/
lemma MemLp.comp_fst {f : α → ε} (hf : MemLp f p μ) (ν : Measure β) [IsFiniteMeasure ν] :
    MemLp (fun x ↦ f x.1) p (μ.prod ν) := by
  have hf' : MemLp f p (ν .univ • μ) := hf.smul_measure (by simp)
  change MemLp (f ∘ Prod.fst) p (μ.prod ν)
  rw [← memLp_map_measure_iff ?_ (by fun_prop)]
  · simpa using hf'
  · simpa using hf'.1
/-
**MeasureTheory.MemLp.comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ε : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε
] {ν : MeasureTheory.Measure β} {p : ENNReal} {f : β → ε},   MeasureTheory.MemLp
 f p ν →     ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ] [
MeasureTheory.SFinite ν],       MeasureTheory.MemLp (fun x => f x.2) p (μ.prod ν
)
参数：μ : MeasureTheory.Measure α；fun x => f x.2；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.MemLp.smul_measure`：∀ {α : Type u_1} {m0 : MeasurableSpace
 α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topolog
icalSpace ε] [inst_1 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_map_measure_iff`：memLp_map_measure_iff (hg : AEStron
glyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) : MemLp g p (Measure.
map f μ) ↔ MemLp (g ∘ f) …
· 使用定理 `MeasureTheory.Measure.map_snd_prod`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α
}   {ν : MeasureTheory.M…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
-/
lemma MemLp.comp_snd {f : β → ε} (hf : MemLp f p ν) (μ : Measure α) [IsFiniteMeasure μ]
    [SFinite ν] :
    MemLp (fun x ↦ f x.2) p (μ.prod ν) := by
  have hf' : MemLp f p (μ .univ • ν) := hf.smul_measure (by simp)
  change MemLp (f ∘ Prod.snd) p (μ.prod ν)
  rw [← memLp_map_measure_iff ?_ (by fun_prop)]
  · simpa using hf'
  · simpa using hf'.1

end MeasureTheory

