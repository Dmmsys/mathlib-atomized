/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Bounding of integrals by asymptotics

We establish integrability of `f` from `f = O(g)`.

## Main results

* `Asymptotics.IsBigO.integrableAtFilter`: If `f = O[l] g` on measurably generated `l`,
  `f` is strongly measurable at `l`, and `g` is integrable at `l`, then `f` is integrable at `l`.
* `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_cocompact`: If `f` is locally integrable,
  and `f =O[cocompact] g` for some `g` integrable at `cocompact`, then `f` is integrable.
* `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atBot_atTop`: If `f` is locally integrable,
  and `f =O[atBot] g`, `f =O[atTop] g'` for some `g`, `g'` integrable `atBot` and `atTop`
  respectively, then `f` is integrable.
* `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant`:
  If `f` is locally integrable, `‖f(-x)‖ = ‖f(x)‖`, and `f =O[atTop] g` for some
  `g` integrable `atTop`, then `f` is integrable.
-/

public section

open Asymptotics MeasureTheory Set Filter

variable {α E F : Type*} [NormedAddCommGroup E] {f : α → E} {g : α → F} {a : α} {l : Filter α}

namespace Asymptotics

section Basic

variable [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}

/-- If `f = O[l] g` on measurably generated `l`, `f` is strongly measurable at `l`,
and `g` is integrable at `l`, then `f` is integrable at `l`. -/
/-
**Asymptotics.IsBigO.integrableAtFilter** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup 
E] {f : α → E} {g : α → F} {l : Filter α}   [inst_1 : MeasurableSpace α] [inst_2
 : NormedAddCommGroup F] {μ : MeasureTheory.Measure α} [l.IsMeasurablyGenerated]
,   f =O[l] g →     StronglyMeasurableAtFilter f l μ → MeasureTheory.IntegrableA
tFilter g l μ → MeasureTheory.IntegrableAtFilter f l μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
O[l] g → ∃ c, …
· 使用定理 `Filter.Eventually.exists_measurable_mem_of_smallSets`：∀ {α : Type u_1} [
inst : MeasurableSpace α] {f : Filter α} [f.IsMeasurablyGenerated] {p : Set α → 
Prop},   (∀ᶠ (s : Set α) in f.smallSets, p…
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Eventually.smallSets`：∀ {α : Type u_1} {l : Filter α} {p : α → Pr
op}, (∀ᶠ (x : α) in l, p x) → ∀ᶠ (s : Set α) in l.smallSets, ∀ x ∈ s, p x
· 使用定理 `StronglyMeasurableAtFilter.eventually`：∀ {α : Type u_1} {β : Type u_2} {
mα : MeasurableSpace α} [inst : TopologicalSpace β] {l : Filter α} {f : α → β}  
 {μ : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.IntegrableAtFilter.eventually`：∀ {α : Type u_1} {ε : Type 
u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst 
: TopologicalSpace ε] [inst_1 : C…
· 使用定理 `MeasureTheory.Integrable.mono`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup β] [inst_1…
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|

--- 原说明 ---
If `f = O[l] g` on measurably generated `l`, `f` is strongly measurable at `l`,
and `g` is integrable at `l`, then `f` is integrable at `l`.
-/
theorem IsBigO.integrableAtFilter [IsMeasurablyGenerated l]
    (hf : f =O[l] g) (hfm : StronglyMeasurableAtFilter f l μ) (hg : IntegrableAtFilter g l μ) :
    IntegrableAtFilter f l μ := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨s, hsl, hsm, hfg, hf, hg⟩ :=
    (hC.smallSets.and <| hfm.eventually.and hg.eventually).exists_measurable_mem_of_smallSets
  refine ⟨s, hsl, (hg.norm.const_mul C).mono hf ?_⟩
  refine (ae_restrict_mem hsm).mono fun x hx ↦ ?_
  exact (hfg x hx).trans (le_abs_self _)

/-- Variant of `MeasureTheory.Integrable.mono` taking `f =O[⊤] (g)` instead of `‖f(x)‖ ≤ ‖g(x)‖` -/
/-
**Asymptotics.IsBigO.integrable** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup 
E] {f : α → E} {g : α → F}   [inst_1 : MeasurableSpace α] [inst_2 : NormedAddCom
mGroup F] {μ : MeasureTheory.Measure α},   MeasureTheory.AEStronglyMeasurable f 
μ → f =O[⊤] g → MeasureTheory.Integrable g μ → MeasureTheory.Integrable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrableAtFilter_top`：integrableAtFilter_top [PseudoMetr
izableSpace ε'] {f : α -> ε'} : IntegrableAtFilter f ⊤ μ ↔ Integrable f μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Asymptotics.IsBigO.integrableAtFilter`：∀ {α : Type u_1} {E : Type u_2} {
F : Type u_3} [inst : NormedAddCommGroup E] {f : α → E} {g : α → F} {l : Filter 
α}   [inst_1 : MeasurableSp…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.restrict`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {f : α → β},   Measur…

--- 原说明 ---
Variant of `MeasureTheory.Integrable.mono` taking `f =O[⊤] (g)` instead of `‖f(x
)‖ ≤ ‖g(x)‖`
-/
theorem IsBigO.integrable (hfm : AEStronglyMeasurable f μ)
    (hf : f =O[⊤] g) (hg : Integrable g μ) : Integrable f μ := by
  rewrite [← integrableAtFilter_top] at *
  exact hf.integrableAtFilter ⟨univ, univ_mem, hfm.restrict⟩ hg

end Basic

variable {ι : Type*} [MeasurableSpace ι] {f : ι × α → E} {s : Set ι} {μ : Measure ι}

/-- Let `f : X x Y → Z`. If as `y` tends to `l`, `f(x, y) = O(g(y))` uniformly on `s : Set X`
of finite measure, then f is eventually (as `y` tends to `l`) integrable along `s`. -/
/-
**Asymptotics.IsBigO.eventually_integrableOn** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup 
E] {g : α → F} {l : Filter α} {ι : Type u_4}   [inst_1 : MeasurableSpace ι] {f :
 ι × α → E} {s : Set ι} {μ : MeasureTheory.Measure ι} [inst_2 : Norm F],   f =O[
Filter.principal s ×ˢ l] (g ∘ Prod.snd) →     (∀ᶠ (x : α) in l, MeasureTheory.AE
StronglyMeasurable (fun i => f (i, x)) (μ.restrict s)) →       MeasurableSet s →
 μ s < ⊤ → ∀ᶠ (x : α) in l, MeasureTheory.IntegrableOn (fun i => f (i, x)) s μ
参数：g ∘ Prod.snd；∀ᶠ (x : α) in l, MeasureTheory.AEStronglyMeasurable (fun i => f 
(i, x)) (μ.restrict s)；x : α；fun i => f (i, x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
O[l] g → ∃ c, …
· 使用定理 `Filter.Eventually.exists_mem`：∀ {α : Type u} {p : α → Prop} {f : Filter 
α}, (∀ᶠ (x : α) in f, p x) → ∃ v ∈ f, ∀ y ∈ v, p y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_apply_univ`：restrict_apply_univ (s : Set 
α) : μ.restrict s univ = μ s
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.self_mem_ae_restrict`：self_mem_ae_restrict {s} (hs : Measu
rableSet s) : s in ae (μ.restrict s)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Let `f : X x Y → Z`. If as `y` tends to `l`, `f(x, y) = O(g(y))` uniformly on `s
 : Set X`
of finite measure, then f is eventually (as `y` tends to `l`) integrable along `
s`.
-/
theorem IsBigO.eventually_integrableOn [Norm F]
    (hf : f =O[𝓟 s ×ˢ l] (g ∘ Prod.snd))
    (hfm : ∀ᶠ x in l, AEStronglyMeasurable (fun i ↦ f (i, x)) (μ.restrict s))
    (hs : MeasurableSet s) (hμ : μ s < ⊤) :
    ∀ᶠ x in l, IntegrableOn (fun i ↦ f (i, x)) s μ := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  obtain ⟨w, hwl, hw⟩ := hfm.exists_mem
  refine eventually_iff_exists_mem.mpr ⟨w ∩ v, inter_mem hwl hv, fun x hx ↦ ?_⟩
  have : IsFiniteMeasure (μ.restrict s) := ⟨Measure.restrict_apply_univ s ▸ hμ⟩
  refine Integrable.mono' (integrable_const (C * ‖g x‖)) (hw x hx.1) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict hs]
  intro y hy
  exact ht (y, x) <| huv ⟨hu hy, hx.2⟩

variable [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- Let `f : X x Y → Z`. If as `y` tends to `l`, `f(x, y) = O(g(y))` uniformly on `s : Set X`
of finite measure, then the integral of `f` along `s` is `O(g(y))`. -/
/-
**Asymptotics.IsBigO.set_integral_isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup 
E] {g : α → F} {l : Filter α} {ι : Type u_4}   [inst_1 : MeasurableSpace ι] {f :
 ι × α → E} {s : Set ι} {μ : MeasureTheory.Measure ι} [inst_2 : NormedSpace ℝ E]
   [inst_3 : NormedAddCommGroup F],   f =O[Filter.principal s ×ˢ l] (g ∘ Prod.sn
d) → μ s < ⊤ → (fun x => ∫ (i : ι) in s, f (i, x) ∂μ) =O[l] g
参数：g ∘ Prod.snd；fun x => ∫ (i : ι) in s, f (i, x) ∂μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
O[l] g → ∃ c, …
· 使用定理 `Filter.Eventually.exists_mem`：∀ {α : Type u} {p : α → Prop} {f : Filter 
α}, (∀ᶠ (x : α) in f, p x) → ∃ v ∈ f, ∀ y ∈ v, p y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `MeasureTheory.norm_setIntegral_le_of_norm_le_const`：norm_setIntegral_le_
of_norm_le_const {C : Real} (hs : μ s < ∞) (hC : forall x in s, ‖f x‖ <= C) : ‖∫
 x in s, f x ∂μ‖ <= C * μ.real s
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0

--- 原说明 ---
Let `f : X x Y → Z`. If as `y` tends to `l`, `f(x, y) = O(g(y))` uniformly on `s
 : Set X`
of finite measure, then the integral of `f` along `s` is `O(g(y))`.
-/
theorem IsBigO.set_integral_isBigO (hf : f =O[𝓟 s ×ˢ l] (g ∘ Prod.snd)) (hμ : μ s < ⊤) :
    (fun x ↦ ∫ i in s, f (i, x) ∂μ) =O[l] g := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := mem_prod_iff.mp htl
  refine isBigO_iff.mpr ⟨C * μ.real s, eventually_iff_exists_mem.mpr ⟨v, hv, fun x hx ↦ ?_⟩⟩
  calc
    _ ≤ C * ‖g x‖ * μ.real s :=
      norm_setIntegral_le_of_norm_le_const hμ fun y hy ↦ ht (y, x) <| huv ⟨hu hy, hx⟩
    _ = _ := by ring

end Asymptotics

variable [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup F]

namespace MeasureTheory

/-- If `f` is locally integrable, and `f =O[cocompact] g` for some `g` integrable at `cocompact`,
then `f` is integrable. -/
/-
**MeasureTheory.LocallyIntegrable.integrable_of_isBigO_cocompact** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.LocallyIntegrable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup 
E] {f : α → E} {g : α → F}   [inst_1 : TopologicalSpace α] [SecondCountableTopol
ogy α] [inst_3 : MeasurableSpace α] {μ : MeasureTheory.Measure α}   [inst_4 : No
rmedAddCommGroup F] [(Filter.cocompact α).IsMeasurablyGenerated],   MeasureTheor
y.LocallyIntegrable f μ →     f =O[Filter.cocompact α] g →       MeasureTheory.I
ntegrableAtFilter g (Filter.cocompact α) μ → MeasureTheory.Integrable f μ
参数：Filter.cocompact α；Filter.cocompact α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_iff_integrableAtFilter_cocompact`：integrable_if
f_integrableAtFilter_cocompact : Integrable f μ ↔ (IntegrableAtFilter f (cocompa
ct X) μ ∧ LocallyIntegrable f μ)
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Asymptotics.IsBigO.integrableAtFilter`：∀ {α : Type u_1} {E : Type u_2} {
F : Type u_3} [inst : NormedAddCommGroup E] {f : α → E} {g : α → F} {l : Filter 
α}   [inst_1 : MeasurableSp…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter`：∀ {α : Ty
pe u_1} {β : Type u_2} {mα : MeasurableSpace α} [inst : TopologicalSpace β] {l :
 Filter α} {f : α → β}   {μ : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.LocallyIntegrable.aestronglyMeasurable`：∀ {X : Type u_1} {
ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 :
 TopologicalSpace ε]   [inst_3 : Continuou…

--- 原说明 ---
If `f` is locally integrable, and `f =O[cocompact] g` for some `g` integrable at
 `cocompact`,
then `f` is integrable.
-/
theorem LocallyIntegrable.integrable_of_isBigO_cocompact [IsMeasurablyGenerated (cocompact α)]
    (hf : LocallyIntegrable f μ) (ho : f =O[cocompact α] g)
    (hg : IntegrableAtFilter g (cocompact α) μ) : Integrable f μ := by
  refine integrable_iff_integrableAtFilter_cocompact.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

section LinearOrder

variable [LinearOrder α] [CompactIccSpace α] {g' : α → F}

/-- If `f` is locally integrable, and `f =O[atBot] g`, `f =O[atTop] g'` for some
`g`, `g'` integrable at `atBot` and `atTop` respectively, then `f` is integrable. -/
/-
**MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atBot_atTop** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.LocallyIntegrable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup 
E] {f : α → E} {g : α → F}   [inst_1 : TopologicalSpace α] [SecondCountableTopol
ogy α] [inst_3 : MeasurableSpace α] {μ : MeasureTheory.Measure α}   [inst_4 : No
rmedAddCommGroup F] [inst_5 : LinearOrder α] [CompactIccSpace α] {g' : α → F}   
[Filter.atBot.IsMeasurablyGenerated] [Filter.atTop.IsMeasurablyGenerated],   Mea
sureTheory.LocallyIntegrable f μ →     f =O[Filter.atBot] g →       MeasureTheor
y.IntegrableAtFilter g Filter.atBot μ →         f =O[Filter.atTop] g' → MeasureT
heory.IntegrableAtFilter g' Filter.atTop μ → MeasureTheory.Integrable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_iff_integrableAtFilter_atBot_atTop`：integrable_
iff_integrableAtFilter_atBot_atTop [PseudoMetrizableSpace ε''] {f : X -> ε''} [L
inearOrder X] [CompactIccSpace X] : Integrable f …
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Asymptotics.IsBigO.integrableAtFilter`：∀ {α : Type u_1} {E : Type u_2} {
F : Type u_3} [inst : NormedAddCommGroup E] {f : α → E} {g : α → F} {l : Filter 
α}   [inst_1 : MeasurableSp…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter`：∀ {α : Ty
pe u_1} {β : Type u_2} {mα : MeasurableSpace α} [inst : TopologicalSpace β] {l :
 Filter α} {f : α → β}   {μ : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.LocallyIntegrable.aestronglyMeasurable`：∀ {X : Type u_1} {
ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 :
 TopologicalSpace ε]   [inst_3 : Continuou…

--- 原说明 ---
If `f` is locally integrable, and `f =O[atBot] g`, `f =O[atTop] g'` for some
`g`, `g'` integrable at `atBot` and `atTop` respectively, then `f` is integrable
.
-/
theorem LocallyIntegrable.integrable_of_isBigO_atBot_atTop
    [IsMeasurablyGenerated (atBot (α := α))] [IsMeasurablyGenerated (atTop (α := α))]
    (hf : LocallyIntegrable f μ)
    (ho : f =O[atBot] g) (hg : IntegrableAtFilter g atBot μ)
    (ho' : f =O[atTop] g') (hg' : IntegrableAtFilter g' atTop μ) : Integrable f μ := by
  refine integrable_iff_integrableAtFilter_atBot_atTop.mpr
    ⟨⟨ho.integrableAtFilter ?_ hg, ho'.integrableAtFilter ?_ hg'⟩, hf⟩
  all_goals exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

/-- If `f` is locally integrable on `(∞, a]`, and `f =O[atBot] g`, for some
`g` integrable at `atBot`, then `f` is integrable on `(∞, a]`. -/
/-
**MeasureTheory.LocallyIntegrableOn.integrableOn_of_isBigO_atBot** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.LocallyIntegrableOn`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup 
E] {f : α → E} {g : α → F} {a : α}   [inst_1 : TopologicalSpace α] [SecondCounta
bleTopology α] [inst_3 : MeasurableSpace α] {μ : MeasureTheory.Measure α}   [ins
t_4 : NormedAddCommGroup F] [inst_5 : LinearOrder α] [CompactIccSpace α] [Filter
.atBot.IsMeasurablyGenerated],   MeasureTheory.LocallyIntegrableOn f (Set.Iic a)
 μ →     f =O[Filter.atBot] g →       MeasureTheory.IntegrableAtFilter g Filter.
atBot μ → MeasureTheory.IntegrableOn f (Set.Iic a) μ
参数：Set.Iic a；Set.Iic a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrableOn_Iic_iff_integrableAtFilter_atBot`：integrableO
n_Iic_iff_integrableAtFilter_atBot [LinearOrder X] [CompactIccSpace X] : Integra
bleOn f (Iic a) μ ↔ IntegrableAtFilter f atBot μ …
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Asymptotics.IsBigO.integrableAtFilter`：∀ {α : Type u_1} {E : Type u_2} {
F : Type u_3} [inst : NormedAddCommGroup E] {f : α → E} {g : α → F} {l : Filter 
α}   [inst_1 : MeasurableSp…
· 使用定理 `Filter.Iic_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α), Set.
Iic a ∈ Filter.atBot
· 使用定理 `MeasureTheory.LocallyIntegrableOn.aestronglyMeasurable`：∀ {X : Type u_1}
 {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : TopologicalSpace ε]   [inst_3 : Continuou…

--- 原说明 ---
If `f` is locally integrable on `(∞, a]`, and `f =O[atBot] g`, for some
`g` integrable at `atBot`, then `f` is integrable on `(∞, a]`.
-/
theorem LocallyIntegrableOn.integrableOn_of_isBigO_atBot [IsMeasurablyGenerated (atBot (α := α))]
    (hf : LocallyIntegrableOn f (Iic a) μ) (ho : f =O[atBot] g)
    (hg : IntegrableAtFilter g atBot μ) : IntegrableOn f (Iic a) μ := by
  refine integrableOn_Iic_iff_integrableAtFilter_atBot.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact ⟨Iic a, Iic_mem_atBot a, hf.aestronglyMeasurable⟩

/-- If `f` is locally integrable on `[a, ∞)`, and `f =O[atTop] g`, for some
`g` integrable at `atTop`, then `f` is integrable on `[a, ∞)`. -/
/-
**MeasureTheory.LocallyIntegrableOn.integrableOn_of_isBigO_atTop** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.LocallyIntegrableOn`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup 
E] {f : α → E} {g : α → F} {a : α}   [inst_1 : TopologicalSpace α] [SecondCounta
bleTopology α] [inst_3 : MeasurableSpace α] {μ : MeasureTheory.Measure α}   [ins
t_4 : NormedAddCommGroup F] [inst_5 : LinearOrder α] [CompactIccSpace α] [Filter
.atTop.IsMeasurablyGenerated],   MeasureTheory.LocallyIntegrableOn f (Set.Ici a)
 μ →     f =O[Filter.atTop] g →       MeasureTheory.IntegrableAtFilter g Filter.
atTop μ → MeasureTheory.IntegrableOn f (Set.Ici a) μ
参数：Set.Ici a；Set.Ici a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrableOn_Ici_iff_integrableAtFilter_atTop`：integrableO
n_Ici_iff_integrableAtFilter_atTop [LinearOrder X] [CompactIccSpace X] : Integra
bleOn f (Ici a) μ ↔ IntegrableAtFilter f atTop μ …
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Asymptotics.IsBigO.integrableAtFilter`：∀ {α : Type u_1} {E : Type u_2} {
F : Type u_3} [inst : NormedAddCommGroup E] {f : α → E} {g : α → F} {l : Filter 
α}   [inst_1 : MeasurableSp…
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `MeasureTheory.LocallyIntegrableOn.aestronglyMeasurable`：∀ {X : Type u_1}
 {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : TopologicalSpace ε]   [inst_3 : Continuou…

--- 原说明 ---
If `f` is locally integrable on `[a, ∞)`, and `f =O[atTop] g`, for some
`g` integrable at `atTop`, then `f` is integrable on `[a, ∞)`.
-/
theorem LocallyIntegrableOn.integrableOn_of_isBigO_atTop [IsMeasurablyGenerated (atTop (α := α))]
    (hf : LocallyIntegrableOn f (Ici a) μ) (ho : f =O[atTop] g)
    (hg : IntegrableAtFilter g atTop μ) : IntegrableOn f (Ici a) μ := by
  refine integrableOn_Ici_iff_integrableAtFilter_atTop.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact ⟨Ici a, Ici_mem_atTop a, hf.aestronglyMeasurable⟩

/-- If `f` is locally integrable, `f` has a top element, and `f =O[atBot] g`, for some
`g` integrable at `atBot`, then `f` is integrable. -/
/-
**MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atBot** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.LocallyIntegrable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup 
E] {f : α → E} {g : α → F}   [inst_1 : TopologicalSpace α] [SecondCountableTopol
ogy α] [inst_3 : MeasurableSpace α] {μ : MeasureTheory.Measure α}   [inst_4 : No
rmedAddCommGroup F] [inst_5 : LinearOrder α] [CompactIccSpace α] [Filter.atBot.I
sMeasurablyGenerated]   [OrderTop α],   MeasureTheory.LocallyIntegrable f μ →   
  f =O[Filter.atBot] g → MeasureTheory.IntegrableAtFilter g Filter.atBot μ → Mea
sureTheory.Integrable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_iff_integrableAtFilter_atBot`：integrable_iff_in
tegrableAtFilter_atBot [LinearOrder X] [OrderTop X] [CompactIccSpace X] : Integr
able f μ ↔ IntegrableAtFilter f atBot μ ∧ L…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Asymptotics.IsBigO.integrableAtFilter`：∀ {α : Type u_1} {E : Type u_2} {
F : Type u_3} [inst : NormedAddCommGroup E] {f : α → E} {g : α → F} {l : Filter 
α}   [inst_1 : MeasurableSp…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter`：∀ {α : Ty
pe u_1} {β : Type u_2} {mα : MeasurableSpace α} [inst : TopologicalSpace β] {l :
 Filter α} {f : α → β}   {μ : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.LocallyIntegrable.aestronglyMeasurable`：∀ {X : Type u_1} {
ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 :
 TopologicalSpace ε]   [inst_3 : Continuou…

--- 原说明 ---
If `f` is locally integrable, `f` has a top element, and `f =O[atBot] g`, for so
me
`g` integrable at `atBot`, then `f` is integrable.
-/
theorem LocallyIntegrable.integrable_of_isBigO_atBot [IsMeasurablyGenerated (atBot (α := α))]
    [OrderTop α] (hf : LocallyIntegrable f μ) (ho : f =O[atBot] g)
    (hg : IntegrableAtFilter g atBot μ) : Integrable f μ := by
  refine integrable_iff_integrableAtFilter_atBot.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

/-- If `f` is locally integrable, `f` has a bottom element, and `f =O[atTop] g`, for some
`g` integrable at `atTop`, then `f` is integrable. -/
/-
**MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atTop** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.LocallyIntegrable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup 
E] {f : α → E} {g : α → F}   [inst_1 : TopologicalSpace α] [SecondCountableTopol
ogy α] [inst_3 : MeasurableSpace α] {μ : MeasureTheory.Measure α}   [inst_4 : No
rmedAddCommGroup F] [inst_5 : LinearOrder α] [CompactIccSpace α] [Filter.atTop.I
sMeasurablyGenerated]   [OrderBot α],   MeasureTheory.LocallyIntegrable f μ →   
  f =O[Filter.atTop] g → MeasureTheory.IntegrableAtFilter g Filter.atTop μ → Mea
sureTheory.Integrable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_iff_integrableAtFilter_atTop`：integrable_iff_in
tegrableAtFilter_atTop [LinearOrder X] [OrderBot X] [CompactIccSpace X] : Integr
able f μ ↔ IntegrableAtFilter f atTop μ ∧ L…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Asymptotics.IsBigO.integrableAtFilter`：∀ {α : Type u_1} {E : Type u_2} {
F : Type u_3} [inst : NormedAddCommGroup E] {f : α → E} {g : α → F} {l : Filter 
α}   [inst_1 : MeasurableSp…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter`：∀ {α : Ty
pe u_1} {β : Type u_2} {mα : MeasurableSpace α} [inst : TopologicalSpace β] {l :
 Filter α} {f : α → β}   {μ : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.LocallyIntegrable.aestronglyMeasurable`：∀ {X : Type u_1} {
ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 :
 TopologicalSpace ε]   [inst_3 : Continuou…

--- 原说明 ---
If `f` is locally integrable, `f` has a bottom element, and `f =O[atTop] g`, for
 some
`g` integrable at `atTop`, then `f` is integrable.
-/
theorem LocallyIntegrable.integrable_of_isBigO_atTop [IsMeasurablyGenerated (atTop (α := α))]
    [OrderBot α] (hf : LocallyIntegrable f μ) (ho : f =O[atTop] g)
    (hg : IntegrableAtFilter g atTop μ) : Integrable f μ := by
  refine integrable_iff_integrableAtFilter_atTop.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

end LinearOrder

section LinearOrderedAddCommGroup

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [CompactIccSpace α]

/-- If `f` is locally integrable, `‖f(-x)‖ = ‖f(x)‖`, and `f =O[atTop] g`, for some
`g` integrable at `atTop`, then `f` is integrable. -/
/-
**MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvari
ant** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.LocallyIntegrable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup 
E] {f : α → E} {g : α → F}   [inst_1 : TopologicalSpace α] [SecondCountableTopol
ogy α] [inst_3 : MeasurableSpace α] {μ : MeasureTheory.Measure α}   [inst_4 : No
rmedAddCommGroup F] [inst_5 : AddCommGroup α] [inst_6 : LinearOrder α] [IsOrdere
dAddMonoid α]   [CompactIccSpace α] [Filter.atTop.IsMeasurablyGenerated] [Measur
ableNeg α] [μ.IsNegInvariant],   MeasureTheory.LocallyIntegrable f μ →     norm 
∘ f =ᵐ[μ] norm ∘ f ∘ Neg.neg →       f =O[Filter.atTop] g → MeasureTheory.Integr
ableAtFilter g Filter.atTop μ → MeasureTheory.Integrable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_of_isBigO_atTop`：∀ {α : T
ype u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] {f : α → E}
 {g : α → F} {a : α}   [inst_1 : TopologicalSpace α]…
· 使用定理 `MeasureTheory.LocallyIntegrable.locallyIntegrableOn`：∀ {X : Type u_1} {ε
 : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : 
TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrableOn_univ`：integrableOn_univ : IntegrableOn f univ
 μ ↔ Integrable f μ
· 使用定理 `Set.Iic_union_Ici_of_le`：Iic_union_Ici_of_le (h : a <= b) : Iic b union 
Ici a = univ
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.map_neg_eq_self`：∀ {G : Type u_1} [inst : Measurab
leSpace G] [inst_1 : Neg G] (μ : MeasureTheory.Measure G) [μ.IsNegInvariant],   
MeasureTheory.Measure.map N…
· 使用定理 `MeasurableEmbedding.restrict_map`：restrict_map (μ : Measure α) (s : Set 
β) : (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f
· 使用定理 `measurableEmbedding_neg`：∀ {α : Type u_3} {m : MeasurableSpace α} [inst 
: InvolutiveNeg α] [MeasurableNeg α], MeasurableEmbedding Neg.neg
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.neg_Iic`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : PartialO
rder α] [IsOrderedAddMonoid α] (a : α),   -Set.Iic a = Set.Ici (-a)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasurableEmbedding.integrable_map_iff`：∀ {α : Type u_1} {δ : Type u_4} 
{ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : M
easurableSpace δ] [inst_1 : …
· 使用定理 `MeasureTheory.Integrable.congr'`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAd
dCommGroup β] [inst_1…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_aemeasurable`：comp_aemeasurable 
{γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Me
asure γ} (hg : AEStronglyMeasurable g (Mea…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.restrict`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {f : α → β},   Measur…
· 使用定理 `MeasureTheory.LocallyIntegrable.aestronglyMeasurable`：∀ {X : Type u_1} {
ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 :
 TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasurableNeg.measurable_neg`：∀ {G : Type u_2} {inst : Neg G} {inst_1 : 
MeasurableSpace G} [self : MeasurableNeg G], Measurable Neg.neg
· 使用定理 `Filter.EventuallyEq.restrict`：∀ {α : Type u_2} {δ : Type u_4} {m0 : Meas
urableSpace α} {μ : MeasureTheory.Measure α} {f g : α → δ} {s : Set α},   f =ᵐ[μ
] g → f =ᵐ[μ.restr…

--- 原说明 ---
If `f` is locally integrable, `‖f(-x)‖ = ‖f(x)‖`, and `f =O[atTop] g`, for some
`g` integrable at `atTop`, then `f` is integrable.
-/
theorem LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
    [IsMeasurablyGenerated (atTop (α := α))] [MeasurableNeg α] [μ.IsNegInvariant]
    (hf : LocallyIntegrable f μ) (hsymm : norm ∘ f =ᵐ[μ] norm ∘ f ∘ Neg.neg) (ho : f =O[atTop] g)
    (hg : IntegrableAtFilter g atTop μ) : Integrable f μ := by
  have h_int := (hf.locallyIntegrableOn (Ici 0)).integrableOn_of_isBigO_atTop ho hg
  rw [← integrableOn_univ, ← Iic_union_Ici_of_le le_rfl, integrableOn_union]
  refine ⟨?_, h_int⟩
  have h_map_neg : (μ.restrict (Ici 0)).map Neg.neg = μ.restrict (Iic 0) := by
    conv => rhs; rw [← Measure.map_neg_eq_self μ, measurableEmbedding_neg.restrict_map]
    simp
  rw [IntegrableOn, ← h_map_neg, measurableEmbedding_neg.integrable_map_iff]
  refine h_int.congr' ?_ hsymm.restrict
  refine AEStronglyMeasurable.comp_aemeasurable ?_ measurable_neg.aemeasurable
  exact h_map_neg ▸ hf.aestronglyMeasurable.restrict

end LinearOrderedAddCommGroup

end MeasureTheory

