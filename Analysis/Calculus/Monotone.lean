/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Covering.OneDim
public import Mathlib.Order.Monotone.Extension

/-!
# Differentiability of monotone functions

We show that a monotone function `f : ℝ → ℝ` is differentiable almost everywhere, in
`Monotone.ae_differentiableAt`. (We also give a version for a function monotone on a set, in
`MonotoneOn.ae_differentiableWithinAt`.)

If the function `f` is continuous, this follows directly from general differentiation of measure
theorems. Let `μ` be the Stieltjes measure associated to `f`. Then, almost everywhere,
`μ [x, y] / Leb [x, y]` (resp. `μ [y, x] / Leb [y, x]`) converges to the Radon-Nikodym derivative
of `μ` with respect to Lebesgue when `y` tends to `x` in `(x, +∞)` (resp. `(-∞, x)`), by
`VitaliFamily.ae_tendsto_rnDeriv`. As `μ [x, y] = f y - f x` and `Leb [x, y] = y - x`, this
gives differentiability right away.

When `f` is only monotone, the same argument works up to small adjustments, as the associated
Stieltjes measure satisfies `μ [x, y] = f (y^+) - f (x^-)` (the right and left limits of `f` at `y`
and `x` respectively). One argues that `f (x^-) = f x` almost everywhere (in fact away from a
countable set), and moreover `f ((y - (y-x)^2)^+) ≤ f y ≤ f (y^+)`. This is enough to deduce the
limit of `(f y - f x) / (y - x)` by a lower and upper approximation argument from the known
behavior of `μ [x, y]`.
-/

public section


open Set Filter Function Metric MeasureTheory MeasureTheory.Measure IsUnifLocDoublingMeasure

open scoped Topology

/-- If `(f y - f x) / (y - x)` converges to a limit as `y` tends to `x`, then the same goes if
`y` is shifted a little bit, i.e., `f (y + (y-x)^2) - f x) / (y - x)` converges to the same limit.
This lemma contains a slightly more general version of this statement (where one considers
convergence along some subfilter, typically `𝓝[<] x` or `𝓝[>] x`) tailored to the application
to almost everywhere differentiability of monotone functions. -/
/-
**tendsto_apply_add_mul_sq_div_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_apply_add_mul_sq_div_sub {f : Real -> Real} {x a c d : Real} {l : 
Filter Real} (hl : l <= 𝓝[!=] x) (hf : Tendsto (fun y => (f y - d) / (y - x)) l 
(𝓝 a)) (h' : Tendsto (fun y => y + c * (y - x) ^ 2) l l) : Tendsto (fun y => (f 
(y + c * (y - x) ^ 2) - d) / (y - x)) l (𝓝 a)
参数：hl : l <= 𝓝[!=] x；hf : Tendsto (fun y => (f y - d) / (y - x)) l (𝓝 a)；h' : Te
ndsto (fun y => y + c * (y - x) ^ 2) l l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.Tendsto.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [
inst_1 : Add M] [SeparatelyContinuousAdd M] {α : Type u_2} {f : α → M}   {x : Fi
lter α} {a : M…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Filter.Tendsto.sub_const`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] {c : G} {f : α → G}   {l : Filter α
}, Filter.Tend…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
（共 119 条，此处仅展示前 30 条）

--- 原说明 ---
If `(f y - f x) / (y - x)` converges to a limit as `y` tends to `x`, then the sa
me goes if
`y` is shifted a little bit, i.e., `f (y + (y-x)^2) - f x) / (y - x)` converges 
to the same limit.
This lemma contains a slightly more general version of this statement (where one
 considers
convergence along some subfilter, typically `𝓝[<] x` or `𝓝[>] x`) tailored to th
e application
to almost everywhere differentiability of monotone functions.
-/
theorem tendsto_apply_add_mul_sq_div_sub {f : ℝ → ℝ} {x a c d : ℝ} {l : Filter ℝ} (hl : l ≤ 𝓝[≠] x)
    (hf : Tendsto (fun y => (f y - d) / (y - x)) l (𝓝 a))
    (h' : Tendsto (fun y => y + c * (y - x) ^ 2) l l) :
    Tendsto (fun y => (f (y + c * (y - x) ^ 2) - d) / (y - x)) l (𝓝 a) := by
  have L : Tendsto (fun y => (y + c * (y - x) ^ 2 - x) / (y - x)) l (𝓝 1) := by
    have : Tendsto (fun y => 1 + c * (y - x)) l (𝓝 (1 + c * (x - x))) := by
      apply Tendsto.mono_left _ (hl.trans nhdsWithin_le_nhds)
      exact ((tendsto_id.sub_const x).const_mul c).const_add 1
    simp only [_root_.sub_self, add_zero, mul_zero] at this
    apply Tendsto.congr' (Eventually.filter_mono hl _) this
    filter_upwards [self_mem_nhdsWithin] with y hy
    field [sub_ne_zero.2 hy]
  have Z := (hf.comp h').mul L
  rw [mul_one] at Z
  apply Tendsto.congr' _ Z
  have : ∀ᶠ y in l, y + c * (y - x) ^ 2 ≠ x := by apply Tendsto.mono_right h' hl self_mem_nhdsWithin
  filter_upwards [this] with y hy
  simp [field]

/-- A Stieltjes function is almost everywhere differentiable, with derivative equal to the
Radon-Nikodym derivative of the associated Stieltjes measure with respect to Lebesgue. -/
/-
**StieltjesFunction.ae_hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StieltjesFunction.ae_hasDerivAt (f : StieltjesFunction Real) : forallᵐ x, 
HasDerivAt f (rnDeriv f.measure volume x).toReal x
参数：f : StieltjesFunction Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
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
· 使用定理 `Set.Countable.ae_notMem`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s : 
Set α},   s.Countable → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSingl
etonClass μ],…
· 使用定理 `StieltjesFunction.countable_leftLim_ne`：countable_leftLim_ne [OrderTopol
ogy R] (f : StieltjesFunction R) : Set.Countable {x | leftLim f x != f x}
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.Measure.isUnifLocDoublingMeasureOfIsAddHaarMeasure`：∀ {E :
 Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : Me
asurableSpace E] [BorelSpace E]   [FiniteDimensional ℝ…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `VitaliFamily.ae_tendsto_rnDeriv`：ae_tendsto_rnDeriv : forallᵐ x ∂μ, Tend
sto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (ρ.rnDeriv μ x))
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StieltjesFunction.measure_Icc`：measure_Icc (a b : R) : f.measure (Icc a 
b) = ofReal (f b - leftLim f a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
（共 163 条，此处仅展示前 30 条）

--- 原说明 ---
A Stieltjes function is almost everywhere differentiable, with derivative equal 
to the
Radon-Nikodym derivative of the associated Stieltjes measure with respect to Leb
esgue.
-/
theorem StieltjesFunction.ae_hasDerivAt (f : StieltjesFunction ℝ) :
    ∀ᵐ x, HasDerivAt f (rnDeriv f.measure volume x).toReal x := by
  /- Denote by `μ` the Stieltjes measure associated to `f`.
    The general theorem `VitaliFamily.ae_tendsto_rnDeriv` ensures that `μ [x, y] / (y - x)` tends
    to the Radon-Nikodym derivative as `y` tends to `x` from the right. As `μ [x,y] = f y - f (x^-)`
    and `f (x^-) = f x` almost everywhere, this gives differentiability on the right.
    On the left, `μ [y, x] / (x - y)` again tends to the Radon-Nikodym derivative.
    As `μ [y, x] = f x - f (y^-)`, this is not exactly the right result, so one uses a sandwiching
    argument to deduce the convergence for `(f x - f y) / (x - y)`. -/
  filter_upwards [VitaliFamily.ae_tendsto_rnDeriv (vitaliFamily (volume : Measure ℝ) 1) f.measure,
    rnDeriv_lt_top f.measure volume, f.countable_leftLim_ne.ae_notMem volume] with x hx h'x h''x
  -- Limit on the right, following from differentiation of measures
  have L1 :
    Tendsto (fun y => (f y - f x) / (y - x)) (𝓝[>] x) (𝓝 (rnDeriv f.measure volume x).toReal) := by
    apply Tendsto.congr' _
      ((ENNReal.tendsto_toReal h'x.ne).comp (hx.comp (Real.tendsto_Icc_vitaliFamily_right x)))
    filter_upwards [self_mem_nhdsWithin]
    rintro y (hxy : x < y)
    simp only [comp_apply, StieltjesFunction.measure_Icc, Real.volume_Icc, Classical.not_not.1 h''x]
    rw [← ENNReal.ofReal_div_of_pos (sub_pos.2 hxy), ENNReal.toReal_ofReal]
    exact div_nonneg (sub_nonneg.2 (f.mono hxy.le)) (sub_pos.2 hxy).le
  -- Limit on the left, following from differentiation of measures. Its form is not exactly the one
  -- we need, due to the appearance of a left limit.
  have L2 : Tendsto (fun y => (leftLim f y - f x) / (y - x)) (𝓝[<] x)
      (𝓝 (rnDeriv f.measure volume x).toReal) := by
    apply Tendsto.congr' _
      ((ENNReal.tendsto_toReal h'x.ne).comp (hx.comp (Real.tendsto_Icc_vitaliFamily_left x)))
    filter_upwards [self_mem_nhdsWithin]
    rintro y (hxy : y < x)
    simp only [comp_apply, StieltjesFunction.measure_Icc, Real.volume_Icc]
    rw [← ENNReal.ofReal_div_of_pos (sub_pos.2 hxy), ENNReal.toReal_ofReal, ← neg_neg (y - x),
      div_neg, neg_div', neg_sub, neg_sub]
    exact div_nonneg (sub_nonneg.2 (f.mono.leftLim_le hxy.le)) (sub_pos.2 hxy).le
  -- Shifting a little bit the limit on the left, by `(y - x)^2`.
  have L3 : Tendsto (fun y => (leftLim f (y + 1 * (y - x) ^ 2) - f x) / (y - x)) (𝓝[<] x)
      (𝓝 (rnDeriv f.measure volume x).toReal) := by
    apply tendsto_apply_add_mul_sq_div_sub (nhdsLT_le_nhdsNE x) L2
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · apply Tendsto.mono_left _ nhdsWithin_le_nhds
      have : Tendsto (fun y : ℝ => y + ↑1 * (y - x) ^ 2) (𝓝 x) (𝓝 (x + ↑1 * (x - x) ^ 2)) :=
        tendsto_id.add (((tendsto_id.sub_const x).pow 2).const_mul ↑1)
      simpa using this
    · filter_upwards [Ioo_mem_nhdsLT <| show x - 1 < x by simp]
      rintro y ⟨hy : x - 1 < y, h'y : y < x⟩
      rw [mem_Iio]
      nlinarith
  -- Deduce the correct limit on the left, by sandwiching.
  have L4 :
    Tendsto (fun y => (f y - f x) / (y - x)) (𝓝[<] x) (𝓝 (rnDeriv f.measure volume x).toReal) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' L3 L2
    · filter_upwards [self_mem_nhdsWithin]
      rintro y (hy : y < x)
      refine div_le_div_of_nonpos_of_le (by linarith) ((sub_le_sub_iff_right _).2 ?_)
      apply f.mono.le_leftLim
      have : ↑0 < (x - y) ^ 2 := sq_pos_of_pos (sub_pos.2 hy)
      linarith
    · filter_upwards [self_mem_nhdsWithin]
      rintro y (hy : y < x)
      refine div_le_div_of_nonpos_of_le (by linarith) ?_
      simpa only [sub_le_sub_iff_right] using f.mono.leftLim_le (le_refl y)
  -- prove the result by splitting into left and right limits.
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field, ← nhdsLT_sup_nhdsGT, tendsto_sup]
  exact ⟨L4, L1⟩

/-- A monotone function is almost everywhere differentiable, with derivative equal to the
Radon-Nikodym derivative of the associated Stieltjes measure with respect to Lebesgue. -/
/-
**Monotone.ae_hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.ae_hasDerivAt {f : Real -> Real} (hf : Monotone f) : forallᵐ x, H
asDerivAt f (rnDeriv hf.stieltjesFunction.measure volume x).toReal x
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
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
· 使用定理 `Set.Countable.ae_notMem`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s : 
Set α},   s.Countable → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSingl
etonClass μ],…
· 使用定理 `Monotone.countable_not_continuousAt`：Monotone.countable_not_continuousAt
 (hf : Monotone f) : Set.Countable {x | ¬ContinuousAt f x}
· 使用定理 `StieltjesFunction.ae_hasDerivAt`：StieltjesFunction.ae_hasDerivAt (f : St
ieltjesFunction Real) : forallᵐ x, HasDerivAt f (rnDeriv f.measure volume x).toR
eal x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.continuousAt_iff_leftLim_eq_rightLim`：continuousAt_iff_leftLim_
eq_rightLim : ContinuousAt f x ↔ leftLim f x = rightLim f x
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Monotone.leftLim_le`：leftLim_le (h : x <= y) : leftLim f x <= f y
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Monotone.le_rightLim`：le_rightLim (h : x <= y) : f x <= rightLim f y
· 使用定理 `tendsto_apply_add_mul_sq_div_sub`：tendsto_apply_add_mul_sq_div_sub {f : 
Real -> Real} {x a c d : Real} {l : Filter Real} (hl : l <= 𝓝[!=] x) (hf : Tends
to (fun y => (f y - d)…
· 使用定理 `nhdsGT_le_nhdsNE`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 :
 Preorder α] (a : α), nhdsWithin a (Set.Ioi a) ≤ nhdsWithin a {a}ᶜ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `slope_fun_def_field`：slope_fun_def_field (f : k -> k) (a : k) : slope f 
a = fun b => (f b - f a) / (b - a)
· 使用定理 `Filter.tendsto_sup`：tendsto_sup {f : α -> β} {x₁ x₂ : Filter α} {y : Fil
ter β} : Tendsto f (x₁ ⊔ x₂) y ↔ Tendsto f x₁ y ∧ Tendsto f x₂ y
· 使用定理 `nhdsLT_sup_nhdsGT`：nhdsLT_sup_nhdsGT (a : α) : 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[!=] a
（共 160 条，此处仅展示前 30 条）

--- 原说明 ---
A monotone function is almost everywhere differentiable, with derivative equal t
o the
Radon-Nikodym derivative of the associated Stieltjes measure with respect to Leb
esgue.
-/
theorem Monotone.ae_hasDerivAt {f : ℝ → ℝ} (hf : Monotone f) :
    ∀ᵐ x, HasDerivAt f (rnDeriv hf.stieltjesFunction.measure volume x).toReal x := by
  /- We already know that the Stieltjes function associated to `f` (i.e., `g : x ↦ f (x^+)`) is
    differentiable almost everywhere. We reduce to this statement by sandwiching values of `f` with
    values of `g`, by shifting with `(y - x)^2` (which has no influence on the relevant
    scale `y - x`.) -/
  filter_upwards [hf.stieltjesFunction.ae_hasDerivAt,
    hf.countable_not_continuousAt.ae_notMem volume] with x hx h'x
  have A : hf.stieltjesFunction x = f x := by
    rw [Classical.not_not, hf.continuousAt_iff_leftLim_eq_rightLim] at h'x
    apply le_antisymm _ (hf.le_rightLim (le_refl _))
    rw [← h'x]
    exact hf.leftLim_le (le_refl _)
  rw [hasDerivAt_iff_tendsto_slope, (nhdsLT_sup_nhdsGT x).symm, tendsto_sup,
    slope_fun_def_field, A] at hx
  -- prove differentiability on the right, by sandwiching with values of `g`
  have L1 : Tendsto (fun y => (f y - f x) / (y - x)) (𝓝[>] x)
      (𝓝 (rnDeriv hf.stieltjesFunction.measure volume x).toReal) := by
    -- limit of a helper function, with a small shift compared to `g`
    have : Tendsto (fun y => (hf.stieltjesFunction (y + -1 * (y - x) ^ 2) - f x) / (y - x)) (𝓝[>] x)
        (𝓝 (rnDeriv hf.stieltjesFunction.measure volume x).toReal) := by
      apply tendsto_apply_add_mul_sq_div_sub (nhdsGT_le_nhdsNE x) hx.2
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · apply Tendsto.mono_left _ nhdsWithin_le_nhds
        have : Tendsto (fun y : ℝ => y + -↑1 * (y - x) ^ 2) (𝓝 x) (𝓝 (x + -↑1 * (x - x) ^ 2)) :=
          tendsto_id.add (((tendsto_id.sub_const x).pow 2).const_mul (-1))
        simpa using this
      · filter_upwards [Ioo_mem_nhdsGT <| show x < x + 1 by simp]
        rintro y ⟨hy : x < y, h'y : y < x + 1⟩
        rw [mem_Ioi]
        nlinarith
    -- apply the sandwiching argument, with the helper function and `g`
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' this hx.2
    · filter_upwards [self_mem_nhdsWithin] with y hy
      rw [mem_Ioi, ← sub_pos] at hy
      gcongr
      exact hf.rightLim_le (by nlinarith)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      rw [mem_Ioi, ← sub_pos] at hy
      gcongr
      exact hf.le_rightLim le_rfl
  -- prove differentiability on the left, by sandwiching with values of `g`
  have L2 : Tendsto (fun y => (f y - f x) / (y - x)) (𝓝[<] x)
      (𝓝 (rnDeriv hf.stieltjesFunction.measure volume x).toReal) := by
    -- limit of a helper function, with a small shift compared to `g`
    have : Tendsto (fun y => (hf.stieltjesFunction (y + -1 * (y - x) ^ 2) - f x) / (y - x)) (𝓝[<] x)
        (𝓝 (rnDeriv hf.stieltjesFunction.measure volume x).toReal) := by
      apply tendsto_apply_add_mul_sq_div_sub (nhdsLT_le_nhdsNE x) hx.1
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · apply Tendsto.mono_left _ nhdsWithin_le_nhds
        have : Tendsto (fun y : ℝ => y + -↑1 * (y - x) ^ 2) (𝓝 x) (𝓝 (x + -↑1 * (x - x) ^ 2)) :=
          tendsto_id.add (((tendsto_id.sub_const x).pow 2).const_mul (-1))
        simpa using this
      · filter_upwards [Ioo_mem_nhdsLT <| show x - 1 < x by simp]
        rintro y hy
        rw [mem_Ioo] at hy
        rw [mem_Iio]
        nlinarith
    -- apply the sandwiching argument, with `g` and the helper function
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hx.1 this
    · filter_upwards [self_mem_nhdsWithin]
      rintro y hy
      rw [mem_Iio, ← sub_neg] at hy
      apply div_le_div_of_nonpos_of_le hy.le
      exact (sub_le_sub_iff_right _).2 (hf.le_rightLim (le_refl _))
    · filter_upwards [self_mem_nhdsWithin]
      rintro y hy
      rw [mem_Iio, ← sub_neg] at hy
      have : 0 < (y - x) ^ 2 := sq_pos_of_neg hy
      apply div_le_div_of_nonpos_of_le hy.le
      exact (sub_le_sub_iff_right _).2 (hf.rightLim_le (by linarith))
  -- conclude global differentiability
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field, ← nhdsLT_sup_nhdsGT, tendsto_sup]
  exact ⟨L2, L1⟩

/-- A monotone real function is differentiable Lebesgue-almost everywhere. -/
/-
**Monotone.ae_differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.ae_differentiableAt {f : Real -> Real} (hf : Monotone f) : forall
ᵐ x, DifferentiableAt Real f x
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
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
· 使用定理 `Monotone.ae_hasDerivAt`：Monotone.ae_hasDerivAt {f : Real -> Real} (hf : 
Monotone f) : forallᵐ x, HasDerivAt f (rnDeriv hf.stieltjesFunction.measure volu
me x).toReal…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x

--- 原说明 ---
A monotone real function is differentiable Lebesgue-almost everywhere.
-/
theorem Monotone.ae_differentiableAt {f : ℝ → ℝ} (hf : Monotone f) :
    ∀ᵐ x, DifferentiableAt ℝ f x := by
  filter_upwards [hf.ae_hasDerivAt] with x hx using hx.differentiableAt

/-- A real function which is monotone on a set is differentiable Lebesgue-almost everywhere on
this set. This version does not assume that `s` is measurable. For a formulation with
`volume.restrict s` assuming that `s` is measurable, see `MonotoneOn.ae_differentiableWithinAt`.
-/
/-
**MonotoneOn.ae_differentiableWithinAt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.ae_differentiableWithinAt_of_mem {f : Real -> Real} {s : Set Re
al} (hf : MonotoneOn f s) : forallᵐ x, x in s -> DifferentiableWithinAt Real f s
 x
参数：hf : MonotoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ae_of_mem_of_ae_of_mem_inter_Ioo`：ae_of_mem_of_ae_of_mem_inter_Ioo {μ : 
Measure Real} [NullSingletonClass μ] {s : Set Real} {p : Real -> Prop} (h : fora
ll a b, a in s -> b in…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MonotoneOn.exists_monotone_extension`：MonotoneOn.exists_monotone_extensi
on (h : MonotoneOn f s) (hl : BddBelow (f '' s)) (hu : BddAbove (f '' s)) : exis
ts g : α -> β, Monotone g …
· 使用定理 `MonotoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f s → s₂ ⊆ s → Monot
oneOn…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MonotoneOn.map_bddBelow`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β} {s t : Set α},   MonotoneOn f t → s ⊆ t → (lo
werBounds s ∩…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MonotoneOn.map_bddAbove`：map_bddAbove (Hf : MonotoneOn f t) (Hst : s sub
seteq t) : (upperBounds s inter t).Nonempty -> BddAbove (f '' s)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Monotone.ae_differentiableAt`：Monotone.ae_differentiableAt {f : Real -> 
Real} (hf : Monotone f) : forallᵐ x, DifferentiableAt Real f x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `DifferentiableWithinAt.congr_of_eventuallyEq`：DifferentiableWithinAt.con
gr_of_eventuallyEq (h : DifferentiableWithinAt 𝕜 f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (
hx : f₁ x = f x) : DifferentiableW…
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A real function which is monotone on a set is differentiable Lebesgue-almost eve
rywhere on
this set. This version does not assume that `s` is measurable. For a formulation
 with
`volume.restrict s` assuming that `s` is measurable, see `MonotoneOn.ae_differen
tiableWithinAt`.
-/
theorem MonotoneOn.ae_differentiableWithinAt_of_mem {f : ℝ → ℝ} {s : Set ℝ} (hf : MonotoneOn f s) :
    ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  /- We use a global monotone extension of `f`, and argue that this extension is differentiable
    almost everywhere. Such an extension need not exist (think of `1/x` on `(0, +∞)`), but it exists
    if one restricts first the function to a compact interval `[a, b]`. -/
  apply ae_of_mem_of_ae_of_mem_inter_Ioo
  intro a b as bs _
  obtain ⟨g, hg, gf⟩ : ∃ g : ℝ → ℝ, Monotone g ∧ EqOn f g (s ∩ Icc a b) :=
    (hf.mono inter_subset_left).exists_monotone_extension
      (hf.map_bddBelow inter_subset_left ⟨a, fun x hx => hx.2.1, as⟩)
      (hf.map_bddAbove inter_subset_left ⟨b, fun x hx => hx.2.2, bs⟩)
  filter_upwards [hg.ae_differentiableAt] with x hx
  intro h'x
  apply hx.differentiableWithinAt.congr_of_eventuallyEq _ (gf ⟨h'x.1, h'x.2.1.le, h'x.2.2.le⟩)
  have : Ioo a b ∈ 𝓝[s] x := nhdsWithin_le_nhds (Ioo_mem_nhds h'x.2.1 h'x.2.2)
  filter_upwards [self_mem_nhdsWithin, this] with y hy h'y
  exact gf ⟨hy, h'y.1.le, h'y.2.le⟩

/-- A real function which is monotone on a set is differentiable Lebesgue-almost everywhere on
this set. This version assumes that `s` is measurable and uses `volume.restrict s`.
For a formulation without measurability assumption,
see `MonotoneOn.ae_differentiableWithinAt_of_mem`. -/
/-
**MonotoneOn.ae_differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.ae_differentiableWithinAt {f : Real -> Real} {s : Set Real} (hf
 : MonotoneOn f s) (hs : MeasurableSet s) : forallᵐ x ∂volume.restrict s, Differ
entiableWithinAt Real f s x
参数：hf : MonotoneOn f s；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `MonotoneOn.ae_differentiableWithinAt_of_mem`：MonotoneOn.ae_differentiabl
eWithinAt_of_mem {f : Real -> Real} {s : Set Real} (hf : MonotoneOn f s) : foral
lᵐ x, x in s -> DifferentiableWit…

--- 原说明 ---
A real function which is monotone on a set is differentiable Lebesgue-almost eve
rywhere on
this set. This version assumes that `s` is measurable and uses `volume.restrict 
s`.
For a formulation without measurability assumption,
see `MonotoneOn.ae_differentiableWithinAt_of_mem`.
-/
theorem MonotoneOn.ae_differentiableWithinAt {f : ℝ → ℝ} {s : Set ℝ} (hf : MonotoneOn f s)
    (hs : MeasurableSet s) : ∀ᵐ x ∂volume.restrict s, DifferentiableWithinAt ℝ f s x := by
  rw [ae_restrict_iff' hs]
  exact hf.ae_differentiableWithinAt_of_mem
