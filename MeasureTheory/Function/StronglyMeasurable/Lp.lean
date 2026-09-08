/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Finitely strongly measurable functions in `Lp`

Functions in `Lp` for `0 < p < ∞` are finitely strongly measurable.

## Main statements

* `MemLp.aefinStronglyMeasurable`: if `MemLp f p μ` with `0 < p < ∞`, then
  `AEFinStronglyMeasurable f μ`.
* `Lp.finStronglyMeasurable`: for `0 < p < ∞`, `Lp` functions are finitely strongly measurable.

## References

* [Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.][Hytonen_VanNeerven_Veraar_Wies_2016]

-/

public section


open MeasureTheory Filter TopologicalSpace Function

open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

variable {α G : Type*} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup G]
  {f : α → G}

/-
**MeasureTheory.MemLp.finStronglyMeasurable_of_stronglyMeasurable** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {G : Type u_2} {p : ENNReal} {m0 : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup G] {f : α → G},   Measur
eTheory.MemLp f p μ →     MeasureTheory.StronglyMeasurable f → p ≠ 0 → p ≠ ⊤ → M
easureTheory.FinStronglyMeasurable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.separableSpace_range_union_singleton`：s
eparableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalSpace β]
 [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `MeasureTheory.SimpleFunc.memLp_approxOn_range`：memLp_approxOn_range [Bor
elSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (
range f union {0} : Set E)] (hf : M…
· 使用定理 `MeasureTheory.SimpleFunc.measure_support_lt_top_of_memLp`：measure_suppor
t_lt_top_of_memLp (f : α ->ₛ E) (hf : MemLp f p μ) (hp_ne_zero : p != 0) (hp_ne_
top : p != ∞) : μ (support f) < ∞
· 使用定理 `MeasureTheory.SimpleFunc.tendsto_approxOn`：tendsto_approxOn {f : β -> α}
 (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s) [SeparableSpace s] {x :
 β} (hx : f x in closure s) : T…
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem MemLp.finStronglyMeasurable_of_stronglyMeasurable (hf : MemLp f p μ)
    (hf_meas : StronglyMeasurable f) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    FinStronglyMeasurable f μ := by
  borelize G
  have : SeparableSpace (Set.range f ∪ {0} : Set G) :=
    hf_meas.separableSpace_range_union_singleton
  let fs := SimpleFunc.approxOn f hf_meas.measurable (Set.range f ∪ {0}) 0 (by simp)
  refine ⟨fs, ?_, ?_⟩
  · have h_fs_Lp : ∀ n, MemLp (fs n) p μ :=
      SimpleFunc.memLp_approxOn_range hf_meas.measurable hf
    exact fun n => (fs n).measure_support_lt_top_of_memLp (h_fs_Lp n) hp_ne_zero hp_ne_top
  · intro x
    apply SimpleFunc.tendsto_approxOn
    apply subset_closure
    simp
/-
**MeasureTheory.MemLp.aefinStronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.MemLp`。
形式化陈述：∀ {α : Type u_1} {G : Type u_2} {p : ENNReal} {m0 : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup G] {f : α → G},   Measur
eTheory.MemLp f p μ → p ≠ 0 → p ≠ ⊤ → MeasureTheory.AEFinStronglyMeasurable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `MeasureTheory.MemLp.finStronglyMeasurable_of_stronglyMeasurable`：∀ {α : 
Type u_1} {G : Type u_2} {p : ENNReal} {m0 : MeasurableSpace α} {μ : MeasureTheo
ry.Measure α}   [inst : NormedAddCommGroup G] {f : α …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_congr_ae`：memLp_congr_ae [TopologicalSpace ε] {f g :
 α -> ε} (hfg : f =ᵐ[μ] g) : MemLp f p μ ↔ MemLp g p μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
-/
theorem MemLp.aefinStronglyMeasurable (hf : MemLp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    AEFinStronglyMeasurable f μ :=
  ⟨hf.aestronglyMeasurable.mk f,
    ((memLp_congr_ae hf.aestronglyMeasurable.ae_eq_mk).mp
          hf).finStronglyMeasurable_of_stronglyMeasurable
      hf.aestronglyMeasurable.stronglyMeasurable_mk hp_ne_zero hp_ne_top,
    hf.aestronglyMeasurable.ae_eq_mk⟩
/-
**MeasureTheory.Integrable.aefinStronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {G : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} [inst : NormedAddCommGroup G]   {f : α → G}, MeasureTheory.Integrab
le f μ → MeasureTheory.AEFinStronglyMeasurable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.aefinStronglyMeasurable`：∀ {α : Type u_1} {G : Type 
u_2} {p : ENNReal} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [ins
t : NormedAddCommGroup G] {f : α …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
theorem Integrable.aefinStronglyMeasurable (hf : Integrable f μ) : AEFinStronglyMeasurable f μ :=
  (memLp_one_iff_integrable.mpr hf).aefinStronglyMeasurable one_ne_zero ENNReal.coe_ne_top
/-
**MeasureTheory.Lp.finStronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Lp`。
形式化陈述：∀ {α : Type u_1} {G : Type u_2} {p : ENNReal} {m0 : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup G] (f : ↥(MeasureTheory.
Lp G p μ)),   p ≠ 0 → p ≠ ⊤ → MeasureTheory.FinStronglyMeasurable (↑↑f) μ
参数：f : ↥(MeasureTheory.Lp G p μ)；↑↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.finStronglyMeasurable_of_stronglyMeasurable`：∀ {α : 
Type u_1} {G : Type u_2} {p : ENNReal} {m0 : MeasurableSpace α} {μ : MeasureTheo
ry.Measure α}   [inst : NormedAddCommGroup G] {f : α …
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
-/
theorem Lp.finStronglyMeasurable (f : Lp G p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    FinStronglyMeasurable f μ :=
  (Lp.memLp f).finStronglyMeasurable_of_stronglyMeasurable (Lp.stronglyMeasurable f) hp_ne_zero
    hp_ne_top

end MeasureTheory

