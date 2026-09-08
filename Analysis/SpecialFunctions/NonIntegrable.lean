/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Non-integrable functions

In this file we prove that the derivative of a function that tends to infinity is not interval
integrable, see `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter` and
`not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured`. Then we apply the
latter lemma to prove that the function `fun x => x⁻¹` is integrable on `a..b` if and only if
`a = b` or `0 ∉ [a, b]`.

## Main results

* `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured`: if `f` tends to infinity
  along `𝓝[≠] c` and `f' = O(g)` along the same filter, then `g` is not interval integrable on any
  nontrivial integral `a..b`, `c ∈ [a, b]`.

* `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter`: a version of
  `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured` that works for one-sided
  neighborhoods;

* `not_intervalIntegrable_of_sub_inv_isBigO_punctured`: if `1 / (x - c) = O(f)` as `x → c`, `x ≠ c`,
  then `f` is not interval integrable on any nontrivial interval `a..b`, `c ∈ [a, b]`;

* `intervalIntegrable_sub_inv_iff`, `intervalIntegrable_inv_iff`: integrability conditions for
  `(x - c)⁻¹` and `x⁻¹`.

## Tags

integrable function
-/

public section


open scoped MeasureTheory Topology Interval NNReal ENNReal

open MeasureTheory TopologicalSpace Set Filter Asymptotics intervalIntegral

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- If `f` is eventually differentiable along a nontrivial filter `l : Filter ℝ` that is generated
by convex sets, the norm of `f` tends to infinity along `l`, and `f' = O(g)` along `l`, where `f'`
is the derivative of `f`, then `g` is not integrable on any set `k` belonging to `l`.
Auxiliary version assuming that `E` is complete. -/
/-
**not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux [Complet
eSpace E] {f : Real -> E} {g : Real -> F} {k : Set Real} (l : Filter Real) [NeBo
t l] [TendstoIxxClass Icc l l] (hl : k in l) (hd : forallᶠ x in l, Differentiabl
eAt Real f x) (hf : Tendsto (fun x => ‖f x‖) l atTop) (hfg : deriv f =O[l] g) : 
¬IntegrableOn g k
参数：l : Filter Real；hl : k in l；hd : forallᶠ x in l, DifferentiableAt Real f x；hf
 : Tendsto (fun x => ‖f x‖) l atTop；hfg : deriv f =O[l] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_nonneg`：∀ {α : Type u_1} {E : Type u_3} {F' : 
Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g'
 : α → F'} {l : Filter…
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.Tendsto.uIcc`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder
 α] {l : Filter α} [Filter.TendstoIxxClass Set.Icc l l] {f g : β → α}   {lb : Fi
lter β}, …
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
· 使用定理 `Filter.Eventually.smallSets`：∀ {α : Type u_1} {l : Filter α} {p : α → Pr
op}, (∀ᶠ (x : α) in l, p x) → ∀ᶠ (s : Set α) in l.smallSets, ∀ x ∈ s, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_prod_self_iff`：mem_prod_self_iff {s} : s in la ×ˢ la ↔ exists
 t in la, t ×ˢ t subseteq s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `measurableSet_uIoc`：measurableSet_uIoc [ClosedIicTopology α] : Measurabl
eSet (uIoc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is eventually differentiable along a nontrivial filter `l : Filter ℝ` tha
t is generated
by convex sets, the norm of `f` tends to infinity along `l`, and `f' = O(g)` alo
ng `l`, where `f'`
is the derivative of `f`, then `g` is not integrable on any set `k` belonging to
 `l`.
Auxiliary version assuming that `E` is complete.
-/
theorem not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux
    [CompleteSpace E] {f : ℝ → E} {g : ℝ → F}
    {k : Set ℝ} (l : Filter ℝ) [NeBot l] [TendstoIxxClass Icc l l]
    (hl : k ∈ l) (hd : ∀ᶠ x in l, DifferentiableAt ℝ f x) (hf : Tendsto (fun x => ‖f x‖) l atTop)
    (hfg : deriv f =O[l] g) : ¬IntegrableOn g k := by
  intro hgi
  obtain ⟨C, hC₀, s, hsl, hsub, hfd, hg⟩ :
    ∃ (C : ℝ) (_ : 0 ≤ C), ∃ s ∈ l, (∀ x ∈ s, ∀ y ∈ s, [[x, y]] ⊆ k) ∧
      (∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ [[x, y]], DifferentiableAt ℝ f z) ∧
        ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ [[x, y]], ‖deriv f z‖ ≤ C * ‖g z‖ := by
    rcases hfg.exists_nonneg with ⟨C, C₀, hC⟩
    have h : ∀ᶠ x : ℝ × ℝ in l ×ˢ l,
        ∀ y ∈ [[x.1, x.2]], (DifferentiableAt ℝ f y ∧ ‖deriv f y‖ ≤ C * ‖g y‖) ∧ y ∈ k :=
      (tendsto_fst.uIcc tendsto_snd).eventually ((hd.and hC.bound).and hl).smallSets
    rcases mem_prod_self_iff.1 h with ⟨s, hsl, hs⟩
    simp only [prod_subset_iff, mem_ofPred_eq] at hs
    exact ⟨C, C₀, s, hsl, fun x hx y hy z hz => (hs x hx y hy z hz).2, fun x hx y hy z hz =>
      (hs x hx y hy z hz).1.1, fun x hx y hy z hz => (hs x hx y hy z hz).1.2⟩
  replace hgi : IntegrableOn (fun x ↦ C * ‖g x‖) k := by exact hgi.norm.smul C
  obtain ⟨c, hc, d, hd, hlt⟩ : ∃ c ∈ s, ∃ d ∈ s, (‖f c‖ + ∫ y in k, C * ‖g y‖) < ‖f d‖ := by
    rcases Filter.nonempty_of_mem hsl with ⟨c, hc⟩
    have : ∀ᶠ x in l, (‖f c‖ + ∫ y in k, C * ‖g y‖) < ‖f x‖ :=
      hf.eventually (eventually_gt_atTop _)
    exact ⟨c, hc, (this.and hsl).exists.imp fun d hd => ⟨hd.2, hd.1⟩⟩
  specialize hsub c hc d hd; specialize hfd c hc d hd
  replace hg : ∀ x ∈ Ι c d, ‖deriv f x‖ ≤ C * ‖g x‖ :=
    fun z hz => hg c hc d hd z ⟨hz.1.le, hz.2⟩
  have hg_ae : ∀ᵐ x ∂volume.restrict (Ι c d), ‖deriv f x‖ ≤ C * ‖g x‖ :=
    (ae_restrict_mem measurableSet_uIoc).mono hg
  have hsub' : Ι c d ⊆ k := Subset.trans Ioc_subset_Icc_self hsub
  have hfi : IntervalIntegrable (deriv f) volume c d := by
    rw [intervalIntegrable_iff]
    have : IntegrableOn (fun x ↦ C * ‖g x‖) (Ι c d) := IntegrableOn.mono hgi hsub' le_rfl
    exact Integrable.mono' this (aestronglyMeasurable_deriv _ _) hg_ae
  refine hlt.not_ge (sub_le_iff_le_add'.1 ?_)
  calc
    ‖f d‖ - ‖f c‖ ≤ ‖f d - f c‖ := norm_sub_norm_le _ _
    _ = ‖∫ x in c..d, deriv f x‖ := congr_arg _ (integral_deriv_eq_sub hfd hfi).symm
    _ = ‖∫ x in Ι c d, deriv f x‖ := norm_integral_eq_norm_integral_uIoc _
    _ ≤ ∫ x in Ι c d, ‖deriv f x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ι c d, C * ‖g x‖ :=
      setIntegral_mono_on hfi.norm.def' (hgi.mono_set hsub') measurableSet_uIoc hg
    _ ≤ ∫ x in k, C * ‖g x‖ := by
      apply setIntegral_mono_set hgi
        (ae_of_all _ fun x => mul_nonneg hC₀ (norm_nonneg _)) hsub'.eventuallyLE
/-
**not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter {f : Real ->
 E} {g : Real -> F} {k : Set Real} (l : Filter Real) [NeBot l] [TendstoIxxClass 
Icc l l] (hl : k in l) (hd : forallᶠ x in l, DifferentiableAt Real f x) (hf : Te
ndsto (fun x => ‖f x‖) l atTop) (hfg : deriv f =O[l] g) : ¬IntegrableOn g k
参数：l : Filter Real；hl : k in l；hd : forallᶠ x in l, DifferentiableAt Real f x；hf
 : Tendsto (fun x => ‖f x‖) l atTop；hfg : deriv f =O[l] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `ContinuousLinearMap.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Mo
dule 𝕜 E] [inst_3 : Topolo…
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isBigO_norm_norm`：isBigO_norm_norm : ((fun x => ‖f' x‖) =O[l
] fun x => ‖g' x‖) ↔ f' =O[l] g'
· 使用定理 `fderiv_comp_deriv`：fderiv_comp_deriv (hl : DifferentiableAt 𝕜 l (f x)) (
hf : DifferentiableAt 𝕜 f x) : deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F -> E) (de
riv f x…
· 使用定理 `ContinuousLinearMap.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] 
[inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `UniformSpace.Completion.instIsBoundedSMul`：∀ {α : Type u} [inst : Pseudo
MetricSpace α] {M : Type u_1} [inst_1 : Zero M] [inst_2 : Zero α] [inst_3 : SMul
 M α]   [inst_4 : PseudoMetricS…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.EventuallyEq.isBigO`：∀ {α : Type u_1} {E : Type u_3} [inst : Norm
 E] {l : Filter α} {f₁ f₂ : α → E}, f₁ =ᶠ[l] f₂ → f₁ =O[l] f₂
（共 31 条，此处仅展示前 30 条）
-/
theorem not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter
    {f : ℝ → E} {g : ℝ → F}
    {k : Set ℝ} (l : Filter ℝ) [NeBot l] [TendstoIxxClass Icc l l]
    (hl : k ∈ l) (hd : ∀ᶠ x in l, DifferentiableAt ℝ f x) (hf : Tendsto (fun x => ‖f x‖) l atTop)
    (hfg : deriv f =O[l] g) : ¬IntegrableOn g k := by
  let a : E →ₗᵢ[ℝ] UniformSpace.Completion E := UniformSpace.Completion.toComplₗᵢ
  let f' := a ∘ f
  have h'd : ∀ᶠ x in l, DifferentiableAt ℝ f' x := by
    filter_upwards [hd] with x hx using a.toContinuousLinearMap.differentiableAt.comp x hx
  have h'f : Tendsto (fun x => ‖f' x‖) l atTop := hf.congr (fun x ↦ by simp [f'])
  have h'fg : deriv f' =O[l] g := by
    apply IsBigO.trans _ hfg
    rw [← isBigO_norm_norm]
    suffices (fun x ↦ ‖deriv f' x‖) =ᶠ[l] (fun x ↦ ‖deriv f x‖) by exact this.isBigO
    filter_upwards [hd] with x hx
    have : deriv f' x = a (deriv f x) := by
      rw [fderiv_comp_deriv x _ hx]
      · have : fderiv ℝ a (f x) = a.toContinuousLinearMap := a.toContinuousLinearMap.fderiv
        simp only [this]
        rfl
      · exact a.toContinuousLinearMap.differentiableAt
    simp only [this]
    simp
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux l hl h'd h'f h'fg

/-- If `f` is eventually differentiable along a nontrivial filter `l : Filter ℝ` that is generated
by convex sets, the norm of `f` tends to infinity along `l`, and `f' = O(g)` along `l`, where `f'`
is the derivative of `f`, then `g` is not integrable on any interval `a..b` such that
`[a, b] ∈ l`. -/
/-
**not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter** 是 Mathli
b 中的一个定理，位于命名空间 ``。
形式化陈述：not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter {f : R
eal -> E} {g : Real -> F} {a b : Real} (l : Filter Real) [NeBot l] [TendstoIxxCl
ass Icc l l] (hl : [[a, b]] in l) (hd : forallᶠ x in l, DifferentiableAt Real f 
x) (hf : Tendsto (fun x => ‖f x‖) l atTop) (hfg : deriv f =O[l] g) : ¬IntervalIn
tegrable g volume a b
参数：l : Filter Real；hl : [[a, b]] in l；hd : forallᶠ x in l, DifferentiableAt Real
 f x；hf : Tendsto (fun x => ‖f x‖) l atTop；hfg : deriv f =O[l] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff'`：intervalIntegrable_iff' [NullSingletonClass μ] 
(h : ‖f (min a b)‖ₑ != ∞
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter`：not_integ
rableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter {f : Real -> E} {g : Real -
> F} {k : Set Real} (l : Filter Real) [NeBot l] [Te…

--- 原说明 ---
If `f` is eventually differentiable along a nontrivial filter `l : Filter ℝ` tha
t is generated
by convex sets, the norm of `f` tends to infinity along `l`, and `f' = O(g)` alo
ng `l`, where `f'`
is the derivative of `f`, then `g` is not integrable on any interval `a..b` such
 that
`[a, b] ∈ l`.
-/
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter {f : ℝ → E} {g : ℝ → F}
    {a b : ℝ} (l : Filter ℝ) [NeBot l] [TendstoIxxClass Icc l l] (hl : [[a, b]] ∈ l)
    (hd : ∀ᶠ x in l, DifferentiableAt ℝ f x) (hf : Tendsto (fun x => ‖f x‖) l atTop)
    (hfg : deriv f =O[l] g) : ¬IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff']
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter _ hl hd hf hfg

/-- If `a ≠ b`, `c ∈ [a, b]`, `f` is differentiable in the neighborhood of `c` within
`[a, b] \ {c}`, `‖f x‖ → ∞` as `x → c` within `[a, b] \ {c}`, and `f' = O(g)` along
`𝓝[[a, b] \ {c}] c`, where `f'` is the derivative of `f`, then `g` is not interval integrable on
`a..b`. -/
/-
**not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_sing
leton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_
singleton {f : Real -> E} {g : Real -> F} {a b c : Real} (hne : a != b) (hc : c 
in [[a, b]]) (h_deriv : forallᶠ x in 𝓝[[[a, b]] \ {c}] c, DifferentiableAt Real 
f x) (h_infty : Tendsto (fun x => ‖f x‖) (𝓝[[[a, b]] \ {c}] c) atTop) (hg : deri
v f =O[𝓝[[[a, b]] \ {c}] c] g) : ¬IntervalIntegrable g volume a b
参数：hne : a != b；hc : c in [[a, b]]；h_deriv : forallᶠ x in 𝓝[[[a, b]] \ {c}] c, D
ifferentiableAt Real f x；h_infty : Tendsto (fun x => ‖f x‖) (𝓝[[[a, b]] \ {c}] c
) atTop；hg : deriv f =O[𝓝[[[a, b]] \ {c}] c] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LT.lt.gt_or_lt`：gt_or_lt (h : a < b) (c : α) : a < c ∨ c < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `min_lt_max`：min_lt_max : min a b < max a b ↔ a != b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.OrdConnected.tendsto_Icc`：∀ {α : Type u_1} [inst : Preorder α] {s
 : Set α} [hs : s.OrdConnected],   Filter.TendstoIxxClass Set.Icc (Filter.princi
pal s) (Filter.princi…
· 使用定理 `Set.ordConnected_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iio a).OrdConnected
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iic_sdiff_right`：Iic_sdiff_right : Iic a \ {a} = Iio a
· 使用定理 `sdiff_mem_nhdsWithin_sdiff`：sdiff_mem_nhdsWithin_sdiff {x : α} {s t : Se
t α} (hs : s in 𝓝[t] x) (t' : Set α) : s \ t' in 𝓝[t \ t'] x
· 使用定理 `Icc_mem_nhdsLE_of_mem`：Icc_mem_nhdsLE_of_mem (H : b in Ioc a c) : Icc a 
c in 𝓝[<=] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Set.Ici_sdiff_left`：∀ {α : Type u_1} [inst : PartialOrder α] {a : α}, Se
t.Ici a \ {a} = Set.Ioi a
· 使用定理 `Icc_mem_nhdsGE_of_mem`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : LinearOrder α] [ClosedIciTopology α] {a b c : α},   b ∈ Set.Ico c a → Set.Ic
c c a ∈ nhd…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter`：not
_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter {f : Real -> E}
 {g : Real -> F} {a b : Real} (l : Filter Real) [NeBot l]…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `a ≠ b`, `c ∈ [a, b]`, `f` is differentiable in the neighborhood of `c` withi
n
`[a, b] \ {c}`, `‖f x‖ → ∞` as `x → c` within `[a, b] \ {c}`, and `f' = O(g)` al
ong
`𝓝[[a, b] \ {c}] c`, where `f'` is the derivative of `f`, then `g` is not interv
al integrable on
`a..b`.
-/
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton
    {f : ℝ → E} {g : ℝ → F} {a b c : ℝ} (hne : a ≠ b) (hc : c ∈ [[a, b]])
    (h_deriv : ∀ᶠ x in 𝓝[[[a, b]] \ {c}] c, DifferentiableAt ℝ f x)
    (h_infty : Tendsto (fun x => ‖f x‖) (𝓝[[[a, b]] \ {c}] c) atTop)
    (hg : deriv f =O[𝓝[[[a, b]] \ {c}] c] g) : ¬IntervalIntegrable g volume a b := by
  obtain ⟨l, hl, hl', hle, hmem⟩ :
    ∃ l : Filter ℝ, TendstoIxxClass Icc l l ∧ l.NeBot ∧ l ≤ 𝓝 c ∧ [[a, b]] \ {c} ∈ l := by
    rcases (min_lt_max.2 hne).gt_or_lt c with hlt | hlt
    · refine ⟨𝓝[<] c, inferInstance, inferInstance, inf_le_left, ?_⟩
      rw [← Iic_sdiff_right]
      exact sdiff_mem_nhdsWithin_sdiff (Icc_mem_nhdsLE_of_mem ⟨hlt, hc.2⟩) _
    · refine ⟨𝓝[>] c, inferInstance, inferInstance, inf_le_left, ?_⟩
      rw [← Ici_sdiff_left]
      exact sdiff_mem_nhdsWithin_sdiff (Icc_mem_nhdsGE_of_mem ⟨hc.1, hlt⟩) _
  have : l ≤ 𝓝[[[a, b]] \ {c}] c := le_inf hle (le_principal_iff.2 hmem)
  exact not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter l
    (mem_of_superset hmem sdiff_subset) (h_deriv.filter_mono this) (h_infty.mono_left this)
    (hg.mono this)

/-- If `f` is differentiable in a punctured neighborhood of `c`, `‖f x‖ → ∞` as `x → c` (more
formally, along the filter `𝓝[≠] c`), and `f' = O(g)` along `𝓝[≠] c`, where `f'` is the derivative
of `f`, then `g` is not interval integrable on any nontrivial interval `a..b` such that
`c ∈ [a, b]`. -/
/-
**not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured** 是 Mat
hlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured {f 
: Real -> E} {g : Real -> F} {a b c : Real} (h_deriv : forallᶠ x in 𝓝[!=] c, Dif
ferentiableAt Real f x) (h_infty : Tendsto (fun x => ‖f x‖) (𝓝[!=] c) atTop) (hg
 : deriv f =O[𝓝[!=] c] g) (hne : a != b) (hc : c in [[a, b]]) : ¬IntervalIntegra
ble g volume a b
参数：h_deriv : forallᶠ x in 𝓝[!=] c, DifferentiableAt Real f x；h_infty : Tendsto (
fun x => ‖f x‖) (𝓝[!=] c) atTop；hg : deriv f =O[𝓝[!=] c] g；hne : a != b；hc : c i
n [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdif
f_singleton`：not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within
_sdiff_singleton {f : Real -> E} {g : Real -> F} {a b c : Real} (hne : a …
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Asymptotics.IsBigO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} 
[inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f
 =O[l'] g → l…

--- 原说明 ---
If `f` is differentiable in a punctured neighborhood of `c`, `‖f x‖ → ∞` as `x →
 c` (more
formally, along the filter `𝓝[≠] c`), and `f' = O(g)` along `𝓝[≠] c`, where `f'`
 is the derivative
of `f`, then `g` is not interval integrable on any nontrivial interval `a..b` su
ch that
`c ∈ [a, b]`.
-/
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured {f : ℝ → E}
    {g : ℝ → F} {a b c : ℝ} (h_deriv : ∀ᶠ x in 𝓝[≠] c, DifferentiableAt ℝ f x)
    (h_infty : Tendsto (fun x => ‖f x‖) (𝓝[≠] c) atTop) (hg : deriv f =O[𝓝[≠] c] g) (hne : a ≠ b)
    (hc : c ∈ [[a, b]]) : ¬IntervalIntegrable g volume a b :=
  have : 𝓝[[[a, b]] \ {c}] c ≤ 𝓝[≠] c := nhdsWithin_mono _ inter_subset_right
  not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton hne hc
    (h_deriv.filter_mono this) (h_infty.mono_left this) (hg.mono this)

/-- If `f` grows in the punctured neighborhood of `c : ℝ` at least as fast as `1 / (x - c)`,
then it is not interval integrable on any nontrivial interval `a..b`, `c ∈ [a, b]`. -/
/-
**not_intervalIntegrable_of_sub_inv_isBigO_punctured** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：not_intervalIntegrable_of_sub_inv_isBigO_punctured {f : Real -> F} {a b c 
: Real} (hf : (fun x => (x - c)⁻¹) =O[𝓝[!=] c] f) (hne : a != b) (hc : c in [[a,
 b]]) : ¬IntervalIntegrable f volume a b
参数：hf : (fun x => (x - c)⁻¹) =O[𝓝[!=] c] f；hne : a != b；hc : c in [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `HasDerivAt.log`：HasDerivAt.log (hf : HasDerivAt f f' x) (hx : f x != 0) 
: HasDerivAt (fun y => log (f y)) (f' / f x) x
· 使用定理 `HasDerivAt.sub_const`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_abs_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto abs Filter.at
Bot Filter.atTop
· 使用定理 `Real.tendsto_log_nhdsNE_zero`：tendsto_log_nhdsNE_zero : Tendsto log (𝓝[!
=] 0) atBot
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `HasDerivAt.tendsto_nhdsNE`：HasDerivAt.tendsto_nhdsNE (h : HasDerivAt f f
' x) (hf' : f' != 0) : Tendsto f (𝓝[!=] x) (𝓝[!=] f x)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured`：
not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured {f : Real
 -> E} {g : Real -> F} {a b c : Real} (h_deriv : forallᶠ x i…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Asymptotics.IsBigO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α 
→ F}, f₁ =O[l] …
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f

--- 原说明 ---
If `f` grows in the punctured neighborhood of `c : ℝ` at least as fast as `1 / (
x - c)`,
then it is not interval integrable on any nontrivial interval `a..b`, `c ∈ [a, b
]`.
-/
theorem not_intervalIntegrable_of_sub_inv_isBigO_punctured {f : ℝ → F} {a b c : ℝ}
    (hf : (fun x => (x - c)⁻¹) =O[𝓝[≠] c] f) (hne : a ≠ b) (hc : c ∈ [[a, b]]) :
    ¬IntervalIntegrable f volume a b := by
  have A : ∀ᶠ x in 𝓝[≠] c, HasDerivAt (fun x => Real.log (x - c)) (x - c)⁻¹ x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using ((hasDerivAt_id x).sub_const c).log (sub_ne_zero.2 hx)
  have B : Tendsto (fun x => ‖Real.log (x - c)‖) (𝓝[≠] c) atTop := by
    refine tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsNE_zero.comp ?_)
    rw [← sub_self c]
    exact ((hasDerivAt_id c).sub_const c).tendsto_nhdsNE one_ne_zero
  exact not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured
    (A.mono fun x hx => hx.differentiableAt) B
    (hf.congr' (A.mono fun x hx => hx.deriv.symm) EventuallyEq.rfl) hne hc

/-- The function `fun x => (x - c)⁻¹` is integrable on `a..b` if and only if
`a = b` or `c ∉ [a, b]`. -/
@[simp]
/-
**intervalIntegrable_sub_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_sub_inv_iff {a b c : Real} : IntervalIntegrable (fun x 
=> (x - c)⁻¹) volume a b ↔ a = b ∨ c ∉ [[a, b]]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `not_intervalIntegrable_of_sub_inv_isBigO_punctured`：not_intervalIntegrab
le_of_sub_inv_isBigO_punctured {f : Real -> F} {a b c : Real} (hf : (fun x => (x
 - c)⁻¹) =O[𝓝[!=] c] f) (hne : a != b) (…
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `IntervalIntegrable.refl`：refl : IntervalIntegrable f μ a a
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
· 使用定理 `ContinuousOn.inv₀`：ContinuousOn.inv₀ (hf : ContinuousOn f s) (h0 : foral
l x in s, f x != 0) : ContinuousOn f⁻¹ s
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_sub_right`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1
 : Sub G] [ContinuousSub G] (a : G), Continuous fun x => x - a
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b

--- 原说明 ---
The function `fun x => (x - c)⁻¹` is integrable on `a..b` if and only if
`a = b` or `c ∉ [a, b]`.
-/
theorem intervalIntegrable_sub_inv_iff {a b c : ℝ} :
    IntervalIntegrable (fun x => (x - c)⁻¹) volume a b ↔ a = b ∨ c ∉ [[a, b]] := by
  constructor
  · refine fun h => or_iff_not_imp_left.2 fun hne hc => ?_
    exact not_intervalIntegrable_of_sub_inv_isBigO_punctured (isBigO_refl _ _) hne hc h
  · rintro (rfl | h₀)
    · exact IntervalIntegrable.refl
    refine ((continuous_sub_right c).continuousOn.inv₀ ?_).intervalIntegrable
    exact fun x hx => sub_ne_zero.2 <| ne_of_mem_of_not_mem hx h₀

/-- The function `fun x => x⁻¹` is integrable on `a..b` if and only if
`a = b` or `0 ∉ [a, b]`. -/
@[simp]
/-
**intervalIntegrable_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalIntegrable_inv_iff {a b : Real} : IntervalIntegrable (fun x => x⁻¹
) volume a b ↔ a = b ∨ (0 : Real) ∉ [[a, b]]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The function `fun x => x⁻¹` is integrable on `a..b` if and only if
`a = b` or `0 ∉ [a, b]`.
-/
theorem intervalIntegrable_inv_iff {a b : ℝ} :
    IntervalIntegrable (fun x => x⁻¹) volume a b ↔ a = b ∨ (0 : ℝ) ∉ [[a, b]] := by
  simp only [← intervalIntegrable_sub_inv_iff, sub_zero]

/-- The function `fun x ↦ x⁻¹` is not integrable on any interval `[a, +∞)`. -/
/-
**not_integrableOn_Ici_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_integrableOn_Ici_inv {a : Real} : ¬ IntegrableOn (fun x => x⁻¹) (Ici a
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Real.hasDerivAt_log`：hasDerivAt_log (hx : x != 0) : HasDerivAt log x⁻¹ x
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `tendsto_norm_atTop_atTop`：tendsto_norm_atTop_atTop : Tendsto (norm : Rea
l -> Real) atTop atTop
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
· 使用定理 `not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter`：not_integ
rableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter {f : Real -> E} {g : Real -
> F} {k : Set Real} (l : Filter Real) [NeBot l] [Te…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Filter.EventuallyEq.isBigO`：∀ {α : Type u_1} {E : Type u_3} [inst : Norm
 E] {l : Filter α} {f₁ f₂ : α → E}, f₁ =ᶠ[l] f₂ → f₁ =O[l] f₂
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'

--- 原说明 ---
The function `fun x ↦ x⁻¹` is not integrable on any interval `[a, +∞)`.
-/
theorem not_integrableOn_Ici_inv {a : ℝ} :
    ¬ IntegrableOn (fun x => x⁻¹) (Ici a) := by
  have A : ∀ᶠ x in atTop, HasDerivAt (fun x => Real.log x) x⁻¹ x := by
    filter_upwards [Ioi_mem_atTop 0] with x hx using Real.hasDerivAt_log (ne_of_gt hx)
  have B : Tendsto (fun x => ‖Real.log x‖) atTop atTop :=
    tendsto_norm_atTop_atTop.comp Real.tendsto_log_atTop
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter atTop (Ici_mem_atTop a)
    (A.mono (fun x hx ↦ hx.differentiableAt)) B
    (Filter.EventuallyEq.isBigO (A.mono (fun x hx ↦ hx.deriv)))

@[deprecated (since := "2026-01-30")] alias not_IntegrableOn_Ici_inv := not_integrableOn_Ici_inv

/-- The function `fun x ↦ x⁻¹` is not integrable on any interval `(a, +∞)`. -/
/-
**not_integrableOn_Ioi_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_integrableOn_Ioi_inv {a : Real} : ¬ IntegrableOn (·⁻¹) (Ioi a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.restrict_Ioi_eq_restrict_Ici`：restrict_Ioi_eq_restrict_Ici
 : μ.restrict (Ioi a) = μ.restrict (Ici a)
· 使用定理 `not_integrableOn_Ici_inv`：not_integrableOn_Ici_inv {a : Real} : ¬ Integr
ableOn (fun x => x⁻¹) (Ici a)

--- 原说明 ---
The function `fun x ↦ x⁻¹` is not integrable on any interval `(a, +∞)`.
-/
theorem not_integrableOn_Ioi_inv {a : ℝ} :
    ¬ IntegrableOn (·⁻¹) (Ioi a) := by
  simpa only [IntegrableOn, restrict_Ioi_eq_restrict_Ici] using not_integrableOn_Ici_inv

@[deprecated (since := "2026-01-30")] alias not_IntegrableOn_Ioi_inv := not_integrableOn_Ioi_inv
