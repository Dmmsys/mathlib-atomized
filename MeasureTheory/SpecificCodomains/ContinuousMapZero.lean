/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.ContinuousMap.ContinuousMapZero
public import Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap

/-!
# Specific results about `ContinuousMapZero`-valued integration

In this file, we collect a few results regarding integrability, on a measure space `(X, μ)`,
of a `C(Y, E)₀`-valued function, where `Y` is a compact topological space with a distinguished `0`,
and `E` is a normed group.

The structure of this file is largely similar to that of
`Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap`, which contains a more detailed
module docstring.

-/

public section

open MeasureTheory

namespace ContinuousMapZero

variable {X Y : Type*} [MeasurableSpace X] {μ : Measure X} [TopologicalSpace Y]
variable {E : Type*} [NormedAddCommGroup E]

/-- A natural criterion for `HasFiniteIntegral` of a `C(Y, E)₀`-valued function is the existence
of some positive function with finite integral such that `∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x`.
Note that there is no dominated convergence here (hence no first-countability assumption
on `Y`). We are just using the properties of Banach-space-valued integration. -/
/-
**ContinuousMapZero.hasFiniteIntegral_of_bound** 是 Mathlib 中的一个引理，位于命名空间 `Contin
uousMapZero`。
形式化陈述：hasFiniteIntegral_of_bound [CompactSpace Y] [Zero Y] (f : X -> C(Y, E)₀) (
bound : X -> Real) (bound_int : HasFiniteIntegral bound μ) (bound_ge : forallᵐ x
 ∂μ, forall y : Y, ‖f x y‖ <= bound x) : HasFiniteIntegral f μ
参数：f : X -> C(Y, E)₀；bound : X -> Real；bound_int : HasFiniteIntegral bound μ；bou
nd_ge : forallᵐ x ∂μ, forall y : Y, ‖f x y‖ <= bound x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono'`：∀ {α : Type u_1} {β : Type u_2} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup 
β]   {f : α → β} {g : α → ℝ…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousMap.norm_le`：norm_le {C : Real} (C0 : (0 : Real) <= C) : ‖f‖ <
= C ↔ forall x : α, ‖f x‖ <= C

--- 原说明 ---
A natural criterion for `HasFiniteIntegral` of a `C(Y, E)₀`-valued function is t
he existence
of some positive function with finite integral such that `∀ᵐ x ∂μ, ∀ y : Y, ‖f x
 y‖ ≤ bound x`.
Note that there is no dominated convergence here (hence no first-countability as
sumption
on `Y`). We are just using the properties of Banach-space-valued integration.
-/
lemma hasFiniteIntegral_of_bound [CompactSpace Y] [Zero Y] (f : X → C(Y, E)₀) (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral f μ := by
  have bound_nonneg : 0 ≤ᵐ[μ] bound := by
    filter_upwards [bound_ge] with x bound_x using le_trans (norm_nonneg _) (bound_x 0)
  refine .mono' bound_int ?_
  filter_upwards [bound_ge, bound_nonneg] with x bound_ge_x bound_nonneg_x
  exact ContinuousMap.norm_le _ bound_nonneg_x |>.mpr bound_ge_x

/-- A variant of `ContinuousMapZero.hasFiniteIntegral_of_bound` spelled in terms of
`ContinuousMapZero.mkD`. -/
/-
**ContinuousMapZero.hasFiniteIntegral_mkD_of_bound** 是 Mathlib 中的一个引理，位于命名空间 `Co
ntinuousMapZero`。
形式化陈述：hasFiniteIntegral_mkD_of_bound [CompactSpace Y] [Zero Y] (f : X -> Y -> E)
 (g : C(Y, E)₀) (f_ae_cont : forallᵐ x ∂μ, Continuous (f x)) (f_ae_zero : forall
ᵐ x ∂μ, f x 0 = 0) (bound : X -> Real) (bound_int : HasFiniteIntegral bound μ) (
bound_ge : forallᵐ x ∂μ, forall y : Y, ‖f x y‖ <= bound x) : HasFiniteIntegral (
fun x => mkD (f x) g) μ
参数：f : X -> Y -> E；g : C(Y, E)₀；f_ae_cont : forallᵐ x ∂μ, Continuous (f x)；f_ae_
zero : forallᵐ x ∂μ, f x 0 = 0；bound : X -> Real；bound_int : HasFiniteIntegral b
ound μ；bound_ge : forallᵐ x ∂μ, forall y : Y, ‖f x y‖ <= bound x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ContinuousMapZero.hasFiniteIntegral_of_bound`：hasFiniteIntegral_of_bound
 [CompactSpace Y] [Zero Y] (f : X -> C(Y, E)₀) (bound : X -> Real) (bound_int : 
HasFiniteIntegral bound μ) (bound_…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMapZero.mkD_apply_of_continuous`：mkD_apply_of_continuous [Zero
 X] {f : X -> R} {g : C(X, R)₀} {x : X} (hf : Continuous f) (hf₀ : f 0 = 0) : mk
D f g x = f x

--- 原说明 ---
A variant of `ContinuousMapZero.hasFiniteIntegral_of_bound` spelled in terms of
`ContinuousMapZero.mkD`.
-/
lemma hasFiniteIntegral_mkD_of_bound [CompactSpace Y] [Zero Y] (f : X → Y → E) (g : C(Y, E)₀)
    (f_ae_cont : ∀ᵐ x ∂μ, Continuous (f x))
    (f_ae_zero : ∀ᵐ x ∂μ, f x 0 = 0)
    (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral (fun x ↦ mkD (f x) g) μ := by
  refine hasFiniteIntegral_of_bound _ bound bound_int ?_
  filter_upwards [bound_ge, f_ae_cont, f_ae_zero] with x bound_ge_x cont_x zero_x
  simpa only [mkD_apply_of_continuous cont_x zero_x] using bound_ge_x

/-- A variant of `ContinuousMapZero.hasFiniteIntegral_mkD_of_bound` for a family of
functions which are continuous on a compact set. -/
/-
**ContinuousMapZero.hasFiniteIntegral_mkD_restrict_of_bound** 是 Mathlib 中的一个引理，位
于命名空间 `ContinuousMapZero`。
形式化陈述：hasFiniteIntegral_mkD_restrict_of_bound {s : Set Y} [CompactSpace s] [Zero
 s] (f : X -> Y -> E) (g : C(s, E)₀) (f_ae_contOn : forallᵐ x ∂μ, ContinuousOn (
f x) s) (f_ae_zero : forallᵐ x ∂μ, f x (0 : s) = 0) (bound : X -> Real) (bound_i
nt : HasFiniteIntegral bound μ) (bound_ge : forallᵐ x ∂μ, forall y in s, ‖f x y‖
 <= bound x) : HasFiniteIntegral (fun x => mkD (s.domRestrict (f x)) g) μ
参数：f : X -> Y -> E；g : C(s, E)₀；f_ae_contOn : forallᵐ x ∂μ, ContinuousOn (f x) s
；f_ae_zero : forallᵐ x ∂μ, f x (0 : s) = 0；bound : X -> Real；bound_int : HasFini
teIntegral bound μ；bound_ge : forallᵐ x ∂μ, forall y in s, ‖f x y‖ <= bound x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ContinuousMapZero.hasFiniteIntegral_mkD_of_bound`：hasFiniteIntegral_mkD_
of_bound [CompactSpace Y] [Zero Y] (f : X -> Y -> E) (g : C(Y, E)₀) (f_ae_cont :
 forallᵐ x ∂μ, Continuous (f x)) (f_ae…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
A variant of `ContinuousMapZero.hasFiniteIntegral_mkD_of_bound` for a family of
functions which are continuous on a compact set.
-/
lemma hasFiniteIntegral_mkD_restrict_of_bound {s : Set Y} [CompactSpace s] [Zero s]
    (f : X → Y → E) (g : C(s, E)₀)
    (f_ae_contOn : ∀ᵐ x ∂μ, ContinuousOn (f x) s)
    (f_ae_zero : ∀ᵐ x ∂μ, f x (0 : s) = 0)
    (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y ∈ s, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral (fun x ↦ mkD (s.domRestrict (f x)) g) μ := by
  refine hasFiniteIntegral_mkD_of_bound _ _ ?_ f_ae_zero bound bound_int ?_
  · simpa [← continuousOn_iff_continuous_domRestrict]
  · simpa
/-
**ContinuousMapZero.aeStronglyMeasurable_mkD_of_uncurry** 是 Mathlib 中的一个引理，位于命名空
间 `ContinuousMapZero`。
形式化陈述：aeStronglyMeasurable_mkD_of_uncurry [CompactSpace Y] [Zero Y] [Topological
Space X] [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(Y, E))] (f
 : X -> Y -> E) (g : C(Y, E)₀) (f_cont : Continuous (Function.uncurry f)) (f_zer
o : forallᵐ x ∂μ, f x 0 = 0) : AEStronglyMeasurable (fun x => mkD (f x) g) μ
参数：C(Y, E)；f : X -> Y -> E；g : C(Y, E)₀；f_cont : Continuous (Function.uncurry f)
；f_zero : forallᵐ x ∂μ, f x 0 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsEmbedding.aestronglyMeasurable_comp_iff`：∀ {α : Type u_1} {β 
: Type u_2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpac
e γ]   {m₀ : MeasurableSpace α} {μ : Mea…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `ContinuousMapZero.isEmbedding_toContinuousMap`：isEmbedding_toContinuousM
ap : IsEmbedding ((↑) : C(X, R)₀ -> C(X, R)) where eq_induced
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `aestronglyMeasurable_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f g 
: α → β}, f =ᵐ[μ…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `ContinuousMapZero.mkD_eq_mkD_of_map_zero`：mkD_eq_mkD_of_map_zero [Zero X
] (f : X -> R) (g : C(X, R)₀) (f_zero : f 0 = 0) : mkD f g = ContinuousMap.mkD f
 g
· 使用引理 `ContinuousMap.aeStronglyMeasurable_mkD_of_uncurry`：aeStronglyMeasurable_
mkD_of_uncurry [CompactSpace Y] [TopologicalSpace X] [OpensMeasurableSpace X] [S
econdCountableTopologyEither X (C(Y, E)…
-/
lemma aeStronglyMeasurable_mkD_of_uncurry [CompactSpace Y] [Zero Y] [TopologicalSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(Y, E))]
    (f : X → Y → E) (g : C(Y, E)₀) (f_cont : Continuous (Function.uncurry f))
    (f_zero : ∀ᵐ x ∂μ, f x 0 = 0) :
    AEStronglyMeasurable (fun x ↦ mkD (f x) g) μ := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
  refine aestronglyMeasurable_congr ?_ |>.mp <|
    ContinuousMap.aeStronglyMeasurable_mkD_of_uncurry f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

open Set in
/-
**ContinuousMapZero.aeStronglyMeasurable_restrict_mkD_of_uncurry** 是 Mathlib 中的一
个引理，位于命名空间 `ContinuousMapZero`。
形式化陈述：aeStronglyMeasurable_restrict_mkD_of_uncurry [CompactSpace Y] [Zero Y] {s 
: Set X} [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopologyE
ither X (C(Y, E))] (hs : MeasurableSet s) (f : X -> Y -> E) (g : C(Y, E)₀) (f_co
nt : ContinuousOn (Function.uncurry f) (s ×ˢ univ)) (f_zero : forallᵐ x ∂(μ.rest
rict s), f x 0 = 0) : AEStronglyMeasurable (fun x => mkD (f x) g) (μ.restrict s)
参数：C(Y, E)；hs : MeasurableSet s；f : X -> Y -> E；g : C(Y, E)₀；f_cont : Continuous
On (Function.uncurry f) (s ×ˢ univ)；f_zero : forallᵐ x ∂(μ.restrict s), f x 0 = 
0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsEmbedding.aestronglyMeasurable_comp_iff`：∀ {α : Type u_1} {β 
: Type u_2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpac
e γ]   {m₀ : MeasurableSpace α} {μ : Mea…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `ContinuousMapZero.isEmbedding_toContinuousMap`：isEmbedding_toContinuousM
ap : IsEmbedding ((↑) : C(X, R)₀ -> C(X, R)) where eq_induced
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `aestronglyMeasurable_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f g 
: α → β}, f =ᵐ[μ…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `ContinuousMapZero.mkD_eq_mkD_of_map_zero`：mkD_eq_mkD_of_map_zero [Zero X
] (f : X -> R) (g : C(X, R)₀) (f_zero : f 0 = 0) : mkD f g = ContinuousMap.mkD f
 g
· 使用引理 `ContinuousMap.aeStronglyMeasurable_restrict_mkD_of_uncurry`：aeStronglyMe
asurable_restrict_mkD_of_uncurry [CompactSpace Y] {s : Set X} [TopologicalSpace 
X] [OpensMeasurableSpace X] [SecondCountableTopo…
-/
lemma aeStronglyMeasurable_restrict_mkD_of_uncurry [CompactSpace Y] [Zero Y] {s : Set X}
    [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(Y, E))]
    (hs : MeasurableSet s) (f : X → Y → E) (g : C(Y, E)₀)
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ univ))
    (f_zero : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0) :
    AEStronglyMeasurable (fun x ↦ mkD (f x) g) (μ.restrict s) := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
  refine aestronglyMeasurable_congr ?_ |>.mp <|
    ContinuousMap.aeStronglyMeasurable_restrict_mkD_of_uncurry hs f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

open Set in
/-
**ContinuousMapZero.aeStronglyMeasurable_mkD_restrict_of_uncurry** 是 Mathlib 中的一
个引理，位于命名空间 `ContinuousMapZero`。
形式化陈述：aeStronglyMeasurable_mkD_restrict_of_uncurry {t : Set Y} [CompactSpace t] 
[Zero t] [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopologyE
ither X (C(t, E))] (f : X -> Y -> E) (g : C(t, E)₀) (f_cont : ContinuousOn (Func
tion.uncurry f) (univ ×ˢ t)) (f_zero : forallᵐ x ∂μ, f x (0 : t) = 0) : AEStrong
lyMeasurable (fun x => mkD (t.domRestrict (f x)) g) μ
参数：C(t, E)；f : X -> Y -> E；g : C(t, E)₀；f_cont : ContinuousOn (Function.uncurry 
f) (univ ×ˢ t)；f_zero : forallᵐ x ∂μ, f x (0 : t) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsEmbedding.aestronglyMeasurable_comp_iff`：∀ {α : Type u_1} {β 
: Type u_2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpac
e γ]   {m₀ : MeasurableSpace α} {μ : Mea…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `ContinuousMapZero.isEmbedding_toContinuousMap`：isEmbedding_toContinuousM
ap : IsEmbedding ((↑) : C(X, R)₀ -> C(X, R)) where eq_induced
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `aestronglyMeasurable_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f g 
: α → β}, f =ᵐ[μ…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `ContinuousMapZero.mkD_eq_mkD_of_map_zero`：mkD_eq_mkD_of_map_zero [Zero X
] (f : X -> R) (g : C(X, R)₀) (f_zero : f 0 = 0) : mkD f g = ContinuousMap.mkD f
 g
· 使用引理 `ContinuousMap.aeStronglyMeasurable_mkD_restrict_of_uncurry`：aeStronglyMe
asurable_mkD_restrict_of_uncurry {t : Set Y} [CompactSpace t] [TopologicalSpace 
X] [OpensMeasurableSpace X] [SecondCountableTopo…
-/
lemma aeStronglyMeasurable_mkD_restrict_of_uncurry {t : Set Y} [CompactSpace t] [Zero t]
    [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(t, E))]
    (f : X → Y → E) (g : C(t, E)₀) (f_cont : ContinuousOn (Function.uncurry f) (univ ×ˢ t))
    (f_zero : ∀ᵐ x ∂μ, f x (0 : t) = 0) :
    AEStronglyMeasurable (fun x ↦ mkD (t.domRestrict (f x)) g) μ := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
  refine aestronglyMeasurable_congr ?_ |>.mp <|
    ContinuousMap.aeStronglyMeasurable_mkD_restrict_of_uncurry f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

open Set in
/-
**ContinuousMapZero.aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry** 是 Ma
thlib 中的一个引理，位于命名空间 `ContinuousMapZero`。
形式化陈述：aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry {s : Set X} {t : Set
 Y} [CompactSpace t] [Zero t] [TopologicalSpace X] [OpensMeasurableSpace X] [Sec
ondCountableTopologyEither X (C(t, E))] (hs : MeasurableSet s) (f : X -> Y -> E)
 (g : C(t, E)₀) (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ t)) (f_zero : 
forallᵐ x ∂(μ.restrict s), f x (0 : t) = 0) : AEStronglyMeasurable (fun x => mkD
 (t.domRestrict (f x)) g) (μ.restrict s)
参数：C(t, E)；hs : MeasurableSet s；f : X -> Y -> E；g : C(t, E)₀；f_cont : Continuous
On (Function.uncurry f) (s ×ˢ t)；f_zero : forallᵐ x ∂(μ.restrict s), f x (0 : t)
 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsEmbedding.aestronglyMeasurable_comp_iff`：∀ {α : Type u_1} {β 
: Type u_2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpac
e γ]   {m₀ : MeasurableSpace α} {μ : Mea…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `ContinuousMapZero.isEmbedding_toContinuousMap`：isEmbedding_toContinuousM
ap : IsEmbedding ((↑) : C(X, R)₀ -> C(X, R)) where eq_induced
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `aestronglyMeasurable_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f g 
: α → β}, f =ᵐ[μ…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `ContinuousMapZero.mkD_eq_mkD_of_map_zero`：mkD_eq_mkD_of_map_zero [Zero X
] (f : X -> R) (g : C(X, R)₀) (f_zero : f 0 = 0) : mkD f g = ContinuousMap.mkD f
 g
· 使用引理 `ContinuousMap.aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry`：aeS
tronglyMeasurable_restrict_mkD_restrict_of_uncurry {s : Set X} {t : Set Y} [Comp
actSpace t] [TopologicalSpace X] [OpensMeasurableSpace X]…
-/
lemma aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry {s : Set X} {t : Set Y}
    [CompactSpace t] [Zero t] [TopologicalSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopologyEither X (C(t, E))]
    (hs : MeasurableSet s) (f : X → Y → E) (g : C(t, E)₀)
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ t))
    (f_zero : ∀ᵐ x ∂(μ.restrict s), f x (0 : t) = 0) :
    AEStronglyMeasurable (fun x ↦ mkD (t.domRestrict (f x)) g) (μ.restrict s) := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
  refine aestronglyMeasurable_congr ?_ |>.mp <|
    ContinuousMap.aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs f g f_cont
  filter_upwards [f_zero] with x zero_x
  rw [mkD_eq_mkD_of_map_zero _ _ zero_x]

end ContinuousMapZero

