/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.ConditionalProbability

/-!
# Kernel associated with a conditional expectation

We define `condExpKernel μ m`, a kernel from `Ω` to `Ω` such that for all integrable functions `f`,
`μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condExpKernel μ m ω)`.

This kernel is defined if `Ω` is a standard Borel space. In general, `μ⟦s | m⟧` maps a measurable
set `s` to a function `Ω → ℝ≥0∞`, and for all `s` that map is unique up to a `μ`-null set. For all
`a`, the map from sets to `ℝ≥0∞` that we obtain that way verifies some of the properties of a
measure, but the fact that the `μ`-null set depends on `s` can prevent us from finding versions of
the conditional expectation that combine into a true measure. The standard Borel space assumption
on `Ω` allows us to do so.

## Main definitions

* `condExpKernel μ m`: kernel such that `μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condExpKernel μ m ω)`.

## Main statements

* `condExp_ae_eq_integral_condExpKernel`: `μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condExpKernel μ m ω)`.

-/

@[expose] public section


open MeasureTheory Set Filter TopologicalSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

section AuxLemmas

variable {Ω F : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → F}

/-
**ProbabilityTheory._root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_
id** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_id [TopologicalSpace F]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable[m.prod mΩ] (fun x : Ω × Ω => f x.2)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ) := hf.comp_snd_map_prodMk id
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.comp_snd_map_prod_id** 是 Mat
hlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.comp_snd_map_prod_id [NormedAddCommGroup F]
    (hf : Integrable f μ) : Integrable (fun x : Ω × Ω => f x.2)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ) :=
  hf.comp_snd_map_prodMk id

end AuxLemmas

variable {Ω F : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

open scoped Classical in
/-- Kernel associated with the conditional expectation with respect to a σ-algebra. It satisfies
`μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condExpKernel μ m ω)`.
It is defined as the conditional distribution of the identity given the identity, where the second
identity is understood as a map from `Ω` with the σ-algebra `mΩ` to `Ω` with σ-algebra `m ⊓ mΩ`.
We use `m ⊓ mΩ` instead of `m` to ensure that it is a sub-σ-algebra of `mΩ`. We then use
`Kernel.comap` to get a kernel from `m` to `mΩ` instead of from `m ⊓ mΩ` to `mΩ`. -/
noncomputable irreducible_def condExpKernel (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) : @Kernel Ω Ω m mΩ :=
  if _h : Nonempty Ω then
    Kernel.comap (@condDistrib Ω Ω Ω mΩ _ _ mΩ (m ⊓ mΩ) id id μ _) id
      (measurable_id'' (inf_le_left : m ⊓ mΩ ≤ m))
  else 0

/-
**ProbabilityTheory.condExpKernel_eq** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：condExpKernel_eq (μ : Measure Ω) [IsFiniteMeasure μ] [h : Nonempty Ω] (m :
 MeasurableSpace Ω) : condExpKernel (mΩ
参数：μ : Measure Ω；m : MeasurableSpace Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `measurable_id''`：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= m
α) : @Measurable α α mα m id
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.condExpKernel_def`：∀ {Ω : Type u_3} [mΩ : MeasurableSp
ace Ω] [inst : StandardBorelSpace Ω] (μ : MeasureTheory.Measure Ω)   [inst_1 : M
easureTheory.IsFiniteMeas…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma condExpKernel_eq (μ : Measure Ω) [IsFiniteMeasure μ] [h : Nonempty Ω]
    (m : MeasurableSpace Ω) :
    condExpKernel (mΩ := mΩ) μ m = Kernel.comap (@condDistrib Ω Ω Ω mΩ _ _ mΩ (m ⊓ mΩ) id id μ _) id
      (measurable_id'' (inf_le_left : m ⊓ mΩ ≤ m)) := by
  simp [condExpKernel, h]
/-
**ProbabilityTheory.condExpKernel_apply_eq_condDistrib** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：condExpKernel_apply_eq_condDistrib [Nonempty Ω] {ω : Ω} : condExpKernel μ 
m ω = @condDistrib Ω Ω Ω mΩ _ _ mΩ (m ⊓ mΩ) id id μ _ (id ω)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `measurable_id''`：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= m
α) : @Measurable α α mα m id
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用引理 `ProbabilityTheory.condExpKernel_eq`：condExpKernel_eq (μ : Measure Ω) [Is
FiniteMeasure μ] [h : Nonempty Ω] (m : MeasurableSpace Ω) : condExpKernel (mΩ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma condExpKernel_apply_eq_condDistrib [Nonempty Ω] {ω : Ω} :
    condExpKernel μ m ω = @condDistrib Ω Ω Ω mΩ _ _ mΩ (m ⊓ mΩ) id id μ _ (id ω) := by
  simp [condExpKernel_eq, Kernel.comap_apply]
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMarkovKernel (condExpKernel μ m) := by
  rcases isEmpty_or_nonempty Ω with h | h
  · exact ⟨fun a ↦ (IsEmpty.false a).elim⟩
  · simpa [condExpKernel, h] using by infer_instance
/-
**ProbabilityTheory.compProd_trim_condExpKernel** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：compProd_trim_condExpKernel (hm : m <= mΩ) : (μ.trim hm) otimesₘ condExpKe
rnel μ m = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ
参数：hm : m <= mΩ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.eq_zero_of_isEmpty`：eq_zero_of_isEmpty [IsEmpty α]
 {_m : MeasurableSpace α} (μ : Measure α) : μ = 0
· 使用定理 `MeasureTheory.Measure.trim.congr_simp`：∀ {α : Type u_1} {m m0 : Measurab
leSpace α} (μ μ_1 : MeasureTheory.Measure α),   μ = μ_1 → ∀ (hm : m ≤ m0), μ.tri
m hm = μ_1.trim hm
· 使用定理 `MeasureTheory.zero_trim`：zero_trim (hm : m <= m0) : (0 : Measure α).trim
 hm = (0 : @Measure α m)
· 使用定理 `ProbabilityTheory.condExpKernel.congr_simp`：∀ {Ω : Type u_3} [mΩ : Measu
rableSpace Ω] [inst : StandardBorelSpace Ω] (μ μ_1 : MeasureTheory.Measure Ω)   
(e_μ : μ = μ_1) [inst_1 : Measur…
· 使用定理 `MeasureTheory.Measure.compProd_zero_left`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kerne
l α β),   MeasureTheory.Measur…
· 使用定理 `MeasureTheory.Measure.map_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure.m
ap f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `measurable_id''`：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= m
α) : @Measurable α α mα m id
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用引理 `ProbabilityTheory.condExpKernel_eq`：condExpKernel_eq (μ : Measure Ω) [Is
FiniteMeasure μ] [h : Nonempty Ω] (m : MeasurableSpace Ω) : condExpKernel (mΩ
· 使用引理 `MeasureTheory.trim_eq_map`：trim_eq_map (hm : m <= m0) : μ.trim hm = @Mea
sure.map _ _ _ m id μ
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `ProbabilityTheory.compProd_map_condDistrib`：compProd_map_condDistrib (hY
 : AEMeasurable Y μ) : (μ.map X) otimesₘ condDistrib Y X μ = μ.map fun a => (X a
, Y a)
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
lemma compProd_trim_condExpKernel (hm : m ≤ mΩ) :
    (μ.trim hm) ⊗ₘ condExpKernel μ m
      = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ := by
  rcases isEmpty_or_nonempty Ω with h | h
  · simp [Measure.eq_zero_of_isEmpty μ]
  rw [condExpKernel_eq, trim_eq_map hm]
  have : m ⊓ mΩ = m := inf_of_le_left hm
  refine (congrArg _ (Kernel.ext fun a => Measure.ext fun s hs => ?_)).trans
    (compProd_map_condDistrib measurable_id.aemeasurable)
  simp only [Kernel.coe_comap, Function.comp_apply, id_eq]
  congr
/-
**ProbabilityTheory.condExpKernel_comp_trim** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：condExpKernel_comp_trim (hm : m <= mΩ) : condExpKernel μ m ∘ₘ μ.trim hm = 
μ
参数：hm : m <= mΩ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.snd_compProd`：snd_compProd (μ : Measure α) [SFinit
e μ] (κ : Kernel α β) [IsSFiniteKernel κ] : (μ otimesₘ κ).snd = κ ∘ₘ μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
· 使用引理 `ProbabilityTheory.compProd_trim_condExpKernel`：compProd_trim_condExpKern
el (hm : m <= mΩ) : (μ.trim hm) otimesₘ condExpKernel μ m = @Measure.map Ω (Ω × 
Ω) mΩ (m.prod mΩ) Function.diag μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.snd_map_prodMk`：snd_map_prodMk {X : α -> β} {Y : α
 -> γ} {μ : Measure α} (hX : Measurable X) : (μ.map fun a => (X a, Y a)).snd = μ
.map Y
· 使用定理 `measurable_id''`：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= m
α) : @Measurable α α mα m id
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
-/
lemma condExpKernel_comp_trim (hm : m ≤ mΩ) : condExpKernel μ m ∘ₘ μ.trim hm = μ := by
  rw [← Measure.snd_compProd, compProd_trim_condExpKernel]
  exact (@Measure.snd_map_prodMk Ω Ω Ω mΩ m mΩ id id μ (measurable_id'' hm)).trans Measure.map_id

section Measurability

variable [NormedAddCommGroup F] {f : Ω → F}

/-
**ProbabilityTheory.measurable_condExpKernel** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：measurable_condExpKernel {s : Set Ω} (hs : MeasurableSet s) : Measurable[m
] fun ω => condExpKernel μ m ω s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
-/
theorem measurable_condExpKernel {s : Set Ω} (hs : MeasurableSet s) :
    Measurable[m] fun ω => condExpKernel μ m ω s :=
  (condExpKernel μ m).measurable_coe hs
/-
**ProbabilityTheory.stronglyMeasurable_condExpKernel** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：stronglyMeasurable_condExpKernel {s : Set Ω} (hs : MeasurableSet s) : Stro
nglyMeasurable[m] fun ω => condExpKernel μ m ω s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ProbabilityTheory.measurable_condExpKernel`：measurable_condExpKernel {s 
: Set Ω} (hs : MeasurableSet s) : Measurable[m] fun ω => condExpKernel μ m ω s
-/
theorem stronglyMeasurable_condExpKernel {s : Set Ω} (hs : MeasurableSet s) :
    StronglyMeasurable[m] fun ω => condExpKernel μ m ω s :=
  Measurable.stronglyMeasurable (measurable_condExpKernel hs)
/-
**ProbabilityTheory._root_.MeasureTheory.StronglyMeasurable.integral_condExpKern
el'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.StronglyMeasurable.integral_condExpKernel' [NormedSpace ℝ F]
    (hf : StronglyMeasurable f) :
    StronglyMeasurable[m ⊓ mΩ] (fun ω ↦ ∫ y, f y ∂condExpKernel μ m ω) := by
  nontriviality Ω
  simp_rw [condExpKernel_apply_eq_condDistrib]
  exact (hf.comp_measurable measurable_snd).integral_condDistrib
/-
**ProbabilityTheory._root_.MeasureTheory.StronglyMeasurable.integral_condExpKern
el** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.StronglyMeasurable.integral_condExpKernel [NormedSpace ℝ F]
    (hf : StronglyMeasurable f) :
    StronglyMeasurable[m] (fun ω ↦ ∫ y, f y ∂condExpKernel μ m ω) :=
  hf.integral_condExpKernel'.mono inf_le_left
/-
**ProbabilityTheory._root_.MeasureTheory.AEStronglyMeasurable.integral_condExpKe
rnel** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condExpKernel [NormedSpace ℝ F]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun ω => ∫ y, f y ∂condExpKernel μ m ω) μ := by
  nontriviality Ω
  simp_rw [condExpKernel_apply_eq_condDistrib]
  exact AEStronglyMeasurable.integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
    hf.comp_snd_map_prod_id
/-
**ProbabilityTheory.aestronglyMeasurable_integral_condExpKernel** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：aestronglyMeasurable_integral_condExpKernel [NormedSpace Real F] (hf : AES
tronglyMeasurable f μ) : AEStronglyMeasurable[m] (fun ω => ∫ y, f y ∂condExpKern
el μ m ω) μ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `measurable_id''`：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= m
α) : @Measurable α α mα m id
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.condExpKernel_eq`：condExpKernel_eq (μ : Measure Ω) [Is
FiniteMeasure μ] [h : Nonempty Ω] (m : MeasurableSpace Ω) : condExpKernel (mΩ
· 使用定理 `ProbabilityTheory.aestronglyMeasurable_integral_condDistrib`：aestronglyM
easurable_integral_condDistrib (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (
hf : AEStronglyMeasurable f (μ.map fun a => (X a,…
· 使用定理 `aemeasurable_id''`：aemeasurable_id'' (μ : Measure α) {m : MeasurableSpac
e α} (hm : m <= m0) : @AEMeasurable α α m m0 id μ
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_id`：∀ {Ω : Type u_1
} {F : Type u_2} {m mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f : Ω
 → F}   [inst : TopologicalSpace F],   Measur…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.mono`：mono {m'} (hm : m <= m') (hf : 
AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m'] f μ
· 使用定理 `MeasurableSpace.comap_id`：comap_id : m.comap id = m
-/
theorem aestronglyMeasurable_integral_condExpKernel [NormedSpace ℝ F]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable[m] (fun ω => ∫ y, f y ∂condExpKernel μ m ω) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  have h := aestronglyMeasurable_integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id hf.comp_snd_map_prod_id
  rw [MeasurableSpace.comap_id] at h
  exact h.mono inf_le_left
/-
**ProbabilityTheory.aestronglyMeasurable_trim_condExpKernel** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：aestronglyMeasurable_trim_condExpKernel (hm : m <= mΩ) (hf : AEStronglyMea
surable f μ) : forallᵐ ω ∂(μ.trim hm), f =ᵐ[condExpKernel μ m ω] hf.mk f
参数：hm : m <= mΩ；hf : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.ae_ae_of_ae_comp`：ae_ae_of_ae_comp {p : β -> Prop}
 (h : forallᵐ ω ∂(κ ∘ₘ μ), p ω) : forallᵐ ω' ∂μ, forallᵐ ω ∂(κ ω'), p ω
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.condExpKernel_comp_trim`：condExpKernel_comp_trim (hm :
 m <= mΩ) : condExpKernel μ m ∘ₘ μ.trim hm = μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
lemma aestronglyMeasurable_trim_condExpKernel (hm : m ≤ mΩ) (hf : AEStronglyMeasurable f μ) :
    ∀ᵐ ω ∂(μ.trim hm), f =ᵐ[condExpKernel μ m ω] hf.mk f := by
  refine Measure.ae_ae_of_ae_comp ?_
  rw [condExpKernel_comp_trim hm]
  exact hf.ae_eq_mk

end Measurability

section Integrability

variable [NormedAddCommGroup F] {f : Ω → F}

/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.condExpKernel_ae** 是 Mathlib
 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.condExpKernel_ae (hf_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Integrable f (condExpKernel μ m ω) := by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.condDistrib_ae (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) aemeasurable_id
      hf_int.comp_snd_map_prod_id using 1
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.integral_norm_condExpKernel*
* 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.integral_norm_condExpKernel (hf_int : Integrable f μ) :
    Integrable (fun ω => ∫ y, ‖f y‖ ∂condExpKernel μ m ω) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.integral_norm_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ))
      aemeasurable_id hf_int.comp_snd_map_prod_id using 1
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.norm_integral_condExpKernel*
* 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.norm_integral_condExpKernel [NormedSpace ℝ F]
    (hf_int : Integrable f μ) :
    Integrable (fun ω => ‖∫ y, f y ∂condExpKernel μ m ω‖) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.norm_integral_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ))
      aemeasurable_id hf_int.comp_snd_map_prod_id using 1
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.integral_condExpKernel** 是 M
athlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.integral_condExpKernel [NormedSpace ℝ F]
    (hf_int : Integrable f μ) :
    Integrable (fun ω => ∫ y, f y ∂condExpKernel μ m ω) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.integral_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ))
      aemeasurable_id hf_int.comp_snd_map_prod_id using 1
/-
**ProbabilityTheory.integrable_toReal_condExpKernel** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory`。
形式化陈述：integrable_toReal_condExpKernel {s : Set Ω} (hs : MeasurableSet s) : Integ
rable (fun ω => (condExpKernel μ m ω).real s) μ
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `measurable_id''`：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= m
α) : @Measurable α α mα m id
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.condExpKernel_eq`：condExpKernel_eq (μ : Measure Ω) [Is
FiniteMeasure μ] [h : Nonempty Ω] (m : MeasurableSpace Ω) : condExpKernel (mΩ
· 使用定理 `ProbabilityTheory.integrable_toReal_condDistrib`：integrable_toReal_condD
istrib (hX : AEMeasurable X μ) (hs : MeasurableSet s) : Integrable (fun a => (co
ndDistrib Y X μ (X a)).real s) μ
· 使用定理 `aemeasurable_id''`：aemeasurable_id'' (μ : Measure α) {m : MeasurableSpac
e α} (hm : m <= m0) : @AEMeasurable α α m m0 id μ
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem integrable_toReal_condExpKernel {s : Set Ω} (hs : MeasurableSet s) :
    Integrable (fun ω => (condExpKernel μ m ω).real s) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  exact integrable_toReal_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ ≤ mΩ)) hs

end Integrability

/-
**ProbabilityTheory.condExpKernel_ae_eq_condExp'** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：condExpKernel_ae_eq_condExp' {s : Set Ω} (hs : MeasurableSet s) : (fun ω =
> (condExpKernel μ m ω).real s) =ᵐ[μ] μ⟦s | m ⊓ mΩ⟧
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `MeasureTheory.Measure.eq_zero_of_isEmpty`：eq_zero_of_isEmpty [IsEmpty α]
 {_m : MeasurableSpace α} (μ : Measure α) : μ = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.condExpKernel.congr_simp`：∀ {Ω : Type u_3} [mΩ : Measu
rableSpace Ω] [inst : StandardBorelSpace Ω] (μ μ_1 : MeasureTheory.Measure Ω)   
(e_μ : μ = μ_1) [inst_1 : Measur…
· 使用定理 `trivial`：True
· 使用定理 `ProbabilityTheory.condDistrib_ae_eq_condExp`：condDistrib_ae_eq_condExp (
hX : Measurable X) (hY : Measurable Y) (hs : MeasurableSet s) : (fun a => (condD
istrib Y X μ (X a)).real s) =ᵐ[μ]…
· 使用定理 `measurable_id''`：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= m
α) : @Measurable α α mα m id
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用引理 `ProbabilityTheory.condExpKernel_apply_eq_condDistrib`：condExpKernel_appl
y_eq_condDistrib [Nonempty Ω] {ω : Ω} : condExpKernel μ m ω = @condDistrib Ω Ω Ω
 mΩ _ _ mΩ (m ⊓ mΩ) id id μ _ (id ω)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasurableSpace.comap_id`：comap_id : m.comap id = m
-/
lemma condExpKernel_ae_eq_condExp' {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω ↦ (condExpKernel μ m ω).real s) =ᵐ[μ] μ⟦s | m ⊓ mΩ⟧ := by
  rcases isEmpty_or_nonempty Ω with h | h
  · have : μ = 0 := Measure.eq_zero_of_isEmpty μ
    simpa [this] using! trivial
  have h := condDistrib_ae_eq_condExp (μ := μ)
    (measurable_id'' (inf_le_right : m ⊓ mΩ ≤ mΩ)) measurable_id hs
  simp only [id_eq, MeasurableSpace.comap_id, preimage_id_eq] at h
  simp_rw [condExpKernel_apply_eq_condDistrib]
  exact h
/-
**ProbabilityTheory.condExpKernel_ae_eq_condExp** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：condExpKernel_ae_eq_condExp (hm : m <= mΩ) {s : Set Ω} (hs : MeasurableSet
 s) : (fun ω => (condExpKernel μ m ω).real s) =ᵐ[μ] μ⟦s | m⟧
参数：hm : m <= mΩ；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.condExpKernel_ae_eq_condExp'`：condExpKernel_ae_eq_cond
Exp' {s : Set Ω} (hs : MeasurableSet s) : (fun ω => (condExpKernel μ m ω).real s
) =ᵐ[μ] μ⟦s | m ⊓ mΩ⟧
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
lemma condExpKernel_ae_eq_condExp
    (hm : m ≤ mΩ) {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω ↦ (condExpKernel μ m ω).real s) =ᵐ[μ] μ⟦s | m⟧ :=
  (condExpKernel_ae_eq_condExp' hs).trans (by rw [inf_of_le_left hm])
/-
**ProbabilityTheory.condExpKernel_ae_eq_trim_condExp** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：condExpKernel_ae_eq_trim_condExp (hm : m <= mΩ) {s : Set Ω} (hs : Measurab
leSet s) : (fun ω => (condExpKernel μ m ω).real s) =ᵐ[μ.trim hm] μ⟦s | m⟧
参数：hm : m <= mΩ；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_eq_trim_iff`：ae_eq_trim_iff (hm : m 
<= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : f =ᵐ[μ.tr
im hm] g ↔ f =ᵐ[μ] g
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `ProbabilityTheory.measurable_condExpKernel`：measurable_condExpKernel {s 
: Set Ω} (hs : MeasurableSet s) : Measurable[m] fun ω => condExpKernel μ m ω s
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用引理 `ProbabilityTheory.condExpKernel_ae_eq_condExp`：condExpKernel_ae_eq_condE
xp (hm : m <= mΩ) {s : Set Ω} (hs : MeasurableSet s) : (fun ω => (condExpKernel 
μ m ω).real s) =ᵐ[μ] μ⟦s | m⟧
-/
lemma condExpKernel_ae_eq_trim_condExp
    (hm : m ≤ mΩ) {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω ↦ (condExpKernel μ m ω).real s) =ᵐ[μ.trim hm] μ⟦s | m⟧ := by
  simp_rw [measureReal_def]
  rw [(measurable_condExpKernel hs).ennreal_toReal.stronglyMeasurable.ae_eq_trim_iff hm
    stronglyMeasurable_condExp]
  exact condExpKernel_ae_eq_condExp hm hs
/-
**ProbabilityTheory.condDistrib_apply_ae_eq_condExpKernel_map** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：condDistrib_apply_ae_eq_condExpKernel_map {β γ : Type*} {mβ : MeasurableSp
ace β} {mγ : MeasurableSpace γ} [StandardBorelSpace β] [Nonempty β] {X : Ω -> β}
 {Y : Ω -> γ} (hX : Measurable X) (hY : Measurable Y) {s : Set β} (hs : Measurab
leSet s) : (fun a => condDistrib X Y μ (Y a) s) =ᵐ[μ] fun a => (condExpKernel μ 
(mγ.comap Y)).map X a s
参数：hX : Measurable X；hY : Measurable Y；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.map_apply'`：map_apply' (κ : Kernel α β) (hf : M
easurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) : map κ f a s = κ a (f ⁻
¹' s)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.condExpKernel_ae_eq_condExp`：condExpKernel_ae_eq_condE
xp (hm : m <= mΩ) {s : Set Ω} (hs : MeasurableSet s) : (fun ω => (condExpKernel 
μ m ω).real s) =ᵐ[μ] μ⟦s | m⟧
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `ProbabilityTheory.condDistrib_ae_eq_condExp`：condDistrib_ae_eq_condExp (
hX : Measurable X) (hY : Measurable Y) (hs : MeasurableSet s) : (fun a => (condD
istrib Y X μ (X a)).real s) =ᵐ[μ]…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measureReal_eq_measureReal_iff`：measureReal_eq_measureReal
_iff {m : MeasurableSpace β} {ν : Measure β} {t : Set β} (h₁ : μ s != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondDistrib`：∀ {α : Type u_1} {β : T
ype u_2} {Ω : Type u_3} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace 
Ω]   [inst_2 : Nonempty Ω] {mα : Meas…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
-/
lemma condDistrib_apply_ae_eq_condExpKernel_map {β γ : Type*} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} [StandardBorelSpace β] [Nonempty β] {X : Ω → β} {Y : Ω → γ}
    (hX : Measurable X) (hY : Measurable Y) {s : Set β} (hs : MeasurableSet s) :
    (fun a ↦ condDistrib X Y μ (Y a) s)
      =ᵐ[μ] fun a ↦ (condExpKernel μ (mγ.comap Y)).map X a s := by
  simp_rw [Kernel.map_apply' _ hX _ hs]
  filter_upwards [condDistrib_ae_eq_condExp hY hX (μ := μ) hs,
    condExpKernel_ae_eq_condExp hY.comap_le (μ := μ) (hX hs)] with a ha₁ ha₂
  rw [← measureReal_eq_measureReal_iff, ha₁, ha₂]
/-
**ProbabilityTheory.condExp_ae_eq_integral_condExpKernel'** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：condExp_ae_eq_integral_condExpKernel' [NormedAddCommGroup F] {f : Ω -> F} 
[NormedSpace Real F] [CompleteSpace F] (hf_int : Integrable f μ) : μ[f | m ⊓ mΩ]
 =ᵐ[μ] fun ω => ∫ y, f y ∂condExpKernel μ m ω
参数：hf_int : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `MeasureTheory.Measure.eq_zero_of_isEmpty`：eq_zero_of_isEmpty [IsEmpty α]
 {_m : MeasurableSpace α} (μ : Measure α) : μ = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.condExpKernel.congr_simp`：∀ {Ω : Type u_3} [mΩ : Measu
rableSpace Ω] [inst : StandardBorelSpace Ω] (μ μ_1 : MeasureTheory.Measure Ω)   
(e_μ : μ = μ_1) [inst_1 : Measur…
· 使用定理 `trivial`：True
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用引理 `ProbabilityTheory.condExpKernel_apply_eq_condDistrib`：condExpKernel_appl
y_eq_condDistrib [Nonempty Ω] {ω : Ω} : condExpKernel μ m ω = @condDistrib Ω Ω Ω
 mΩ _ _ mΩ (m ⊓ mΩ) id id μ _ (id ω)
· 使用定理 `ProbabilityTheory.condExp_ae_eq_integral_condDistrib_id`：condExp_ae_eq_i
ntegral_condDistrib_id [NormedSpace Real F] [CompleteSpace F] {X : Ω -> β} {μ : 
Measure Ω} [IsFiniteMeasure μ] (hX : Measurab…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasurableSpace.comap_id`：comap_id : m.comap id = m
-/
theorem condExp_ae_eq_integral_condExpKernel' [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] (hf_int : Integrable f μ) :
    μ[f | m ⊓ mΩ] =ᵐ[μ] fun ω => ∫ y, f y ∂condExpKernel μ m ω := by
  rcases isEmpty_or_nonempty Ω with h | h
  · have : μ = 0 := Measure.eq_zero_of_isEmpty μ
    simpa [this] using! trivial
  have hX : @Measurable Ω Ω mΩ (m ⊓ mΩ) id := measurable_id.mono le_rfl (inf_le_right : m ⊓ mΩ ≤ mΩ)
  simp_rw [condExpKernel_apply_eq_condDistrib]
  have h := condExp_ae_eq_integral_condDistrib_id hX hf_int
  simpa only [MeasurableSpace.comap_id, id_eq] using! h

/-- The conditional expectation of `f` with respect to a σ-algebra `m` is almost everywhere equal to
the integral `∫ y, f y ∂(condExpKernel μ m ω)`. -/
/-
**ProbabilityTheory.condExp_ae_eq_integral_condExpKernel** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory`。
形式化陈述：condExp_ae_eq_integral_condExpKernel [NormedAddCommGroup F] {f : Ω -> F} [
NormedSpace Real F] [CompleteSpace F] (hm : m <= mΩ) (hf_int : Integrable f μ) :
 μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂condExpKernel μ m ω
参数：hm : m <= mΩ；hf_int : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `ProbabilityTheory.condExp_ae_eq_integral_condExpKernel'`：condExp_ae_eq_i
ntegral_condExpKernel' [NormedAddCommGroup F] {f : Ω -> F} [NormedSpace Real F] 
[CompleteSpace F] (hf_int : Integrable f μ) :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f

--- 原说明 ---
The conditional expectation of `f` with respect to a σ-algebra `m` is almost eve
rywhere equal to
the integral `∫ y, f y ∂(condExpKernel μ m ω)`.
-/
theorem condExp_ae_eq_integral_condExpKernel [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] (hm : m ≤ mΩ) (hf_int : Integrable f μ) :
    μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂condExpKernel μ m ω :=
  ((condExp_ae_eq_integral_condExpKernel' hf_int).symm.trans (by rw [inf_of_le_left hm])).symm

/-- Auxiliary lemma for `condExp_ae_eq_trim_integral_condExpKernel`. -/
/-
**ProbabilityTheory.condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasura
ble** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable [NormedAdd
CommGroup F] {f : Ω -> F} [NormedSpace Real F] [CompleteSpace F] (hm : m <= mΩ) 
(hf : StronglyMeasurable f) (hf_int : Integrable f μ) : μ[f | m] =ᵐ[μ.trim hm] f
un ω => ∫ y, f y ∂condExpKernel μ m ω
参数：hm : m <= mΩ；hf : StronglyMeasurable f；hf_int : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable`：ae_eq
_trim_of_stronglyMeasurable (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : 
StronglyMeasurable[m] g) (hfg : f =ᵐ[μ] g) : f =ᵐ[μ.tri…
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.StronglyMeasurable.integral_condExpKernel`：∀ {Ω : Type u_1
} {F : Type u_2} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : Standa
rdBorelSpace Ω]   {μ : MeasureTheory.Measure …
· 使用定理 `ProbabilityTheory.condExp_ae_eq_integral_condExpKernel`：condExp_ae_eq_in
tegral_condExpKernel [NormedAddCommGroup F] {f : Ω -> F} [NormedSpace Real F] [C
ompleteSpace F] (hm : m <= mΩ) (hf_int : Int…

--- 原说明 ---
Auxiliary lemma for `condExp_ae_eq_trim_integral_condExpKernel`.
-/
theorem condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable
    [NormedAddCommGroup F] {f : Ω → F} [NormedSpace ℝ F] [CompleteSpace F]
    (hm : m ≤ mΩ) (hf : StronglyMeasurable f) (hf_int : Integrable f μ) :
    μ[f | m] =ᵐ[μ.trim hm] fun ω ↦ ∫ y, f y ∂condExpKernel μ m ω := by
  refine StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm ?_ ?_ ?_
  · exact stronglyMeasurable_condExp
  · exact hf.integral_condExpKernel
  · exact condExp_ae_eq_integral_condExpKernel hm hf_int

/-- The conditional expectation of `f` with respect to a σ-algebra `m` is
(`μ.trim hm`)-almost everywhere equal to the integral `∫ y, f y ∂(condExpKernel μ m ω)`. -/
/-
**ProbabilityTheory.condExp_ae_eq_trim_integral_condExpKernel** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：condExp_ae_eq_trim_integral_condExpKernel [NormedAddCommGroup F] {f : Ω ->
 F} [NormedSpace Real F] [CompleteSpace F] (hm : m <= mΩ) (hf_int : Integrable f
 μ) : μ[f | m] =ᵐ[μ.trim hm] fun ω => ∫ y, f y ∂condExpKernel μ m ω
参数：hm : m <= mΩ；hf_int : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `MeasureTheory.condExp_congr_ae_trim`：condExp_congr_ae_trim (hm : m <= m₀
) (hfg : f =ᵐ[μ] g) : μ[f | m] =ᵐ[μ.trim hm] μ[g | m]
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `ProbabilityTheory.condExp_ae_eq_trim_integral_condExpKernel_of_stronglyM
easurable`：condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable [Norm
edAddCommGroup F] {f : Ω -> F} [NormedSpace Real F] [CompleteSpace F] (…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.aestronglyMeasurable_trim_condExpKernel`：aestronglyMea
surable_trim_condExpKernel (hm : m <= mΩ) (hf : AEStronglyMeasurable f μ) : fora
llᵐ ω ∂(μ.trim hm), f =ᵐ[condExpKernel μ m ω] h…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ

--- 原说明 ---
The conditional expectation of `f` with respect to a σ-algebra `m` is
(`μ.trim hm`)-almost everywhere equal to the integral `∫ y, f y ∂(condExpKernel 
μ m ω)`.
-/
theorem condExp_ae_eq_trim_integral_condExpKernel [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] (hm : m ≤ mΩ) (hf_int : Integrable f μ) :
    μ[f | m] =ᵐ[μ.trim hm] fun ω ↦ ∫ y, f y ∂condExpKernel μ m ω := by
  refine (condExp_congr_ae_trim hm hf_int.1.ae_eq_mk).trans ?_
  refine (condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable hm
    hf_int.1.stronglyMeasurable_mk ?_).trans ?_
  · rwa [integrable_congr hf_int.1.ae_eq_mk.symm]
  filter_upwards [aestronglyMeasurable_trim_condExpKernel hm hf_int.1] with ω hω
  rw [integral_congr_ae hω]

section Cond

/-! ### Relation between conditional expectation, conditional kernel and the conditional measure. -/

open MeasurableSpace

variable {s t : Set Ω} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [StandardBorelSpace Ω]

/-
**ProbabilityTheory.condExp_generateFrom_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：condExp_generateFrom_singleton (hs : MeasurableSet s) {f : Ω -> F} (hf : I
ntegrable f μ) : μ[f | generateFrom {s}] =ᵐ[μ.restrict s] fun _ => ∫ x, f x ∂μ[|
s]
参数：hs : MeasurableSet s；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
· 使用定理 `MeasureTheory.ae_eq_trans`：ae_eq_trans {f g h : α -> β} (h₁ : f =ᵐ[μ] g)
 (h₂ : g =ᵐ[μ] h) : f =ᵐ[μ] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_restrict_ae_eq_restrict`：condExp_restrict_ae_eq_re
strict (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs_m : MeasurableSet[m] s) (hf_
int : Integrable f μ) : (μ.restrict…
· 使用引理 `MeasurableSpace.generateFrom_singleton_le`：generateFrom_singleton_le {m 
: MeasurableSpace α} {s : Set α} (hs : MeasurableSet s) : MeasurableSpace.genera
teFrom {s} <= m
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`：ae_eq_condExp_of_f
orall_setIntegral_eq (hm : m <= m₀) [SigmaFinite (μ.trim hm)] {f g : α -> E} (hf
 : Integrable f μ) (hg_int_finite : forall…
· 使用定理 `MeasureTheory.Integrable.restrict`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]   [
inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.integrableOn_const_iff`：integrableOn_const_iff {C : ε'} (h
C : ‖C‖ₑ != ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.measurableSet_generateFrom_singleton_iff`：measurableSet_ge
nerateFrom_singleton_iff {s t : Set α} : MeasurableSet[MeasurableSpace.generateF
rom {s}] t ↔ t = ∅ ∨ t = s ∨ t = sᶜ ∨ t = un…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_empty`：restrict_empty : μ.restrict ∅ = 0
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
（共 49 条，此处仅展示前 30 条）
-/
lemma condExp_generateFrom_singleton (hs : MeasurableSet s) {f : Ω → F} (hf : Integrable f μ) :
    μ[f | generateFrom {s}] =ᵐ[μ.restrict s] fun _ ↦ ∫ x, f x ∂μ[|s] := by
  by_cases hμs : μ s = 0
  · rw [Measure.restrict_eq_zero.2 hμs]
    rfl
  refine ae_eq_trans (condExp_restrict_ae_eq_restrict
    (generateFrom_singleton_le hs)
    (measurableSet_generateFrom rfl) hf).symm ?_
  · refine (ae_eq_condExp_of_forall_setIntegral_eq (generateFrom_singleton_le hs) hf.restrict ?_ ?_
      stronglyMeasurable_const.aestronglyMeasurable).symm
    · rintro t - -
      rw [integrableOn_const_iff]
      exact Or.inr <| measure_lt_top (μ.restrict s) t
    · rintro t ht -
      obtain (h | h | h | h) := measurableSet_generateFrom_singleton_iff.1 ht
      · simp [h]
      · simp only [h, cond, integral_smul_measure, ENNReal.toReal_inv, integral_const,
        MeasurableSet.univ, measureReal_restrict_apply, univ_inter, measureReal_restrict_apply_self,
        ← measureReal_def]
        rw [smul_inv_smul₀, Measure.restrict_restrict hs, inter_self]
        exact ENNReal.toReal_ne_zero.2 ⟨hμs, measure_ne_top _ _⟩
      · simp only [h, integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
          measureReal_restrict_apply hs.compl, compl_inter_self, measureReal_empty, zero_smul,
          ((Measure.restrict_apply_eq_zero hs.compl).2 <| compl_inter_self s ▸ measure_empty),
          setIntegral_measure_zero]
      · simp only [h, Measure.restrict_univ, cond, integral_smul_measure, ENNReal.toReal_inv, ←
        measureReal_def, integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter]
        rw [smul_inv_smul₀]
        exact (measureReal_ne_zero_iff (by finiteness)).2 hμs
/-
**ProbabilityTheory.condExp_set_generateFrom_singleton** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：condExp_set_generateFrom_singleton (hs : MeasurableSet s) (ht : Measurable
Set t) : μ⟦t | generateFrom {s}⟧ =ᵐ[μ.restrict s] fun _ => μ[|s].real t
参数：hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_indicator_one`：integral_indicator_one ⦃s : Set X⦄
 (hs : MeasurableSet s) : ∫ x, s.indicator 1 x ∂μ = μ.real s
· 使用引理 `ProbabilityTheory.condExp_generateFrom_singleton`：condExp_generateFrom_s
ingleton (hs : MeasurableSet s) {f : Ω -> F} (hf : Integrable f μ) : μ[f | gener
ateFrom {s}] =ᵐ[μ.restrict s] fun _ =>…
· 使用定理 `MeasureTheory.Integrable.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {mα
 : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topolo
gicalSpace ε'] [inst_1 :…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
-/
lemma condExp_set_generateFrom_singleton (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ⟦t | generateFrom {s}⟧ =ᵐ[μ.restrict s] fun _ ↦ μ[|s].real t := by
  rw [← integral_indicator_one ht]
  exact condExp_generateFrom_singleton hs <| Integrable.indicator (integrable_const 1) ht
/-
**ProbabilityTheory.condExpKernel_singleton_ae_eq_cond** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：condExpKernel_singleton_ae_eq_cond [StandardBorelSpace Ω] (hs : Measurable
Set s) (ht : MeasurableSet t) : forallᵐ ω ∂μ.restrict s, condExpKernel μ (genera
teFrom {s}) ω t = μ[t | s]
参数：hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.ae_restrict_le`：ae_restrict_le : ae (μ.restrict s) <= ae μ
· 使用引理 `ProbabilityTheory.condExpKernel_ae_eq_condExp`：condExpKernel_ae_eq_condE
xp (hm : m <= mΩ) {s : Set Ω} (hs : MeasurableSet s) : (fun ω => (condExpKernel 
μ m ω).real s) =ᵐ[μ] μ⟦s | m⟧
· 使用引理 `MeasurableSpace.generateFrom_singleton_le`：generateFrom_singleton_le {m 
: MeasurableSpace α} {s : Set α} (hs : MeasurableSet s) : MeasurableSpace.genera
teFrom {s} <= m
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.condExp_set_generateFrom_singleton`：condExp_set_genera
teFrom_singleton (hs : MeasurableSet s) (ht : MeasurableSet t) : μ⟦t | generateF
rom {s}⟧ =ᵐ[μ.restrict s] fun _ => μ[|s].r…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_eq_toReal_iff'`：toReal_eq_toReal_iff' {x y : Real>=0∞} (h
x : x != ⊤) (hy : y != ⊤) : x.toReal = y.toReal ↔ x = y
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondExpKernel`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [inst : StandardBorelSpace Ω]   {μ 
: MeasureTheory.Measure Ω} [inst_1 : Me…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `ProbabilityTheory.instIsZeroOrProbabilityMeasureCond`：∀ {Ω : Type u_1} {
m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {s : Set Ω},   MeasureTheor
y.IsZeroOrProbabilityMeasure μ[|s]
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
-/
lemma condExpKernel_singleton_ae_eq_cond [StandardBorelSpace Ω] (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    ∀ᵐ ω ∂μ.restrict s,
      condExpKernel μ (generateFrom {s}) ω t = μ[t | s] := by
  have : (fun ω ↦ (condExpKernel μ (generateFrom {s}) ω).real t) =ᵐ[μ.restrict s]
      μ⟦t | generateFrom {s}⟧ :=
    ae_restrict_le <| condExpKernel_ae_eq_condExp
      (generateFrom_singleton_le hs) ht
  filter_upwards [condExp_set_generateFrom_singleton hs ht, this] with ω hω₁ hω₂
  rwa [hω₁, measureReal_def, measureReal_def,
    ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ t) (measure_ne_top _ t)] at hω₂

end Cond

end ProbabilityTheory

