/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Uniform integrability

This file contains the definitions for uniform integrability (both in the measure theory sense
as well as the probability theory sense). This file also contains the Vitali convergence theorem
which establishes a relation between uniform integrability, convergence in measure and
Lp convergence.

Uniform integrability plays a vital role in the theory of martingales and most notably is used to
formulate the martingale convergence theorem.

## Main definitions

* `MeasureTheory.UnifIntegrable`: uniform integrability in the measure theory sense.
  In particular, a sequence of functions `f` is uniformly integrable if for all `ε > 0`, there
  exists some `δ > 0` such that for all sets `s` of smaller measure than `δ`, the Lp-norm of
  `f i` restricted to `s` is smaller than `ε` for all `i`.
* `MeasureTheory.UniformIntegrable`: uniform integrability in the probability theory sense.
  In particular, a sequence of measurable functions `f` is uniformly integrable in the
  probability theory sense if it is uniformly integrable in the measure theory sense and
  has uniformly bounded Lp-norm.

## Main results

* `MeasureTheory.unifIntegrable_finite`: a finite sequence of Lp functions is uniformly
  integrable.
* `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`: a sequence of Lp functions which is uniformly
  integrable converges in Lp if they converge almost everywhere.
* `MeasureTheory.tendstoInMeasure_iff_tendsto_Lp_finite`: Vitali convergence theorem:
  a sequence of Lp functions converges in Lp if and only if it is uniformly integrable
  and converges in measure.

## Tags
uniformly integrable, uniformly absolutely continuous integral, Vitali convergence theorem
-/

@[expose] public section


noncomputable section

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]

/-- Uniform integrability in the measure theory sense.

A sequence of functions `f` is said to be uniformly integrable if for all `ε > 0`, there exists
some `δ > 0` such that for all sets `s` with measure less than `δ`, the Lp-norm of `f i`
restricted to `s` is less than `ε`.

Uniform integrability is also known as uniformly absolutely continuous integrals. -/
/-
**MeasureTheory.UnifIntegrable** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：UnifIntegrable {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>=0∞) (μ
 : Measure α) : Prop
参数：f : ι -> α -> β；p : Real>=0∞；μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uniform integrability in the measure theory sense.

A sequence of functions `f` is said to be uniformly integrable if for all `ε > 0
`, there exists
some `δ > 0` such that for all sets `s` with measure less than `δ`, the Lp-norm 
of `f i`
restricted to `s` is less than `ε`.

Uniform integrability is also known as uniformly absolutely continuous integrals
.
-/
def UnifIntegrable {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  ∀ ⦃ε : ℝ⦄ (_ : 0 < ε), ∃ (δ : ℝ) (_ : 0 < δ), ∀ i s,
    MeasurableSet s → μ s ≤ ENNReal.ofReal δ → eLpNorm (s.indicator (f i)) p μ ≤ ENNReal.ofReal ε

/-- In probability theory, a family of measurable functions is uniformly integrable if it is
uniformly integrable in the measure theory sense and is uniformly bounded. -/
/-
**MeasureTheory.UniformIntegrable** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：UniformIntegrable {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>=0∞)
 (μ : Measure α) : Prop
参数：f : ι -> α -> β；p : Real>=0∞；μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In probability theory, a family of measurable functions is uniformly integrable 
if it is
uniformly integrable in the measure theory sense and is uniformly bounded.
-/
def UniformIntegrable {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  (∀ i, AEStronglyMeasurable (f i) μ) ∧ UnifIntegrable f p μ ∧ ∃ C : ℝ≥0, ∀ i, eLpNorm (f i) p μ ≤ C

namespace UniformIntegrable

/-
**MeasureTheory.UniformIntegrable.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.UniformIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {f : ι → α → β} {p : 
ENNReal},   MeasureTheory.UniformIntegrable f p μ → ∀ (i : ι), MeasureTheory.AES
tronglyMeasurable (f i) μ
参数：i : ι；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
protected theorem aestronglyMeasurable {f : ι → α → β} {p : ℝ≥0∞} (hf : UniformIntegrable f p μ)
    (i : ι) : AEStronglyMeasurable (f i) μ :=
  hf.1 i
/-
**MeasureTheory.UniformIntegrable.unifIntegrable** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.UniformIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {f : ι → α → β} {p : 
ENNReal},   MeasureTheory.UniformIntegrable f p μ → MeasureTheory.UnifIntegrable
 f p μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem unifIntegrable {f : ι → α → β} {p : ℝ≥0∞} (hf : UniformIntegrable f p μ) :
    UnifIntegrable f p μ :=
  hf.2.1
/-
**MeasureTheory.UniformIntegrable.memLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.UniformIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {f : ι → α → β} {p : 
ENNReal},   MeasureTheory.UniformIntegrable f p μ → ∀ (i : ι), MeasureTheory.Mem
Lp (f i) p μ
参数：i : ι；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
-/
protected theorem memLp {f : ι → α → β} {p : ℝ≥0∞} (hf : UniformIntegrable f p μ) (i : ι) :
    MemLp (f i) p μ :=
  ⟨hf.1 i,
    let ⟨_, _, hC⟩ := hf.2
    lt_of_le_of_lt (hC i) ENNReal.coe_lt_top⟩

end UniformIntegrable

section UnifIntegrable

/-! ### `UnifIntegrable`

This section deals with uniform integrability in the measure theory sense. -/


namespace UnifIntegrable

variable {f g : ι → α → β} {p : ℝ≥0∞}

/-
**MeasureTheory.UnifIntegrable.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Unif
Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {f g : ι → α → β} {p 
: ENNReal},   MeasureTheory.UnifIntegrable f p μ →     MeasureTheory.UnifIntegra
ble g p μ →       1 ≤ p →         (∀ (i : ι), MeasureTheory.AEStronglyMeasurable
 (f i) μ) →           (∀ (i : ι), MeasureTheory.AEStronglyMeasurable (g i) μ) → 
MeasureTheory.UnifIntegrable (f + g) p μ
参数：∀ (i : ι), MeasureTheory.AEStronglyMeasurable (f i) μ；∀ (i : ι), MeasureTheor
y.AEStronglyMeasurable (g i) μ；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_add'`：∀ {α : Type u_1} {M : Type u_4} [inst : AddZeroClass
 M] (s : Set α) (f g : α → M),   s.indicator (f + g) = s.indicator f + s.indicat
or g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.eLpNorm_add_le`：eLpNorm_add_le (hf : AEStronglyMeasurable 
f μ) (hg : AEStronglyMeasurable g μ) (hp1 : 1 <= p) : eLpNorm (f + g) p μ <= eLp
Norm f p μ + eLpNo…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 : Z…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
-/
protected theorem add (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 ≤ p)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifIntegrable (f + g) p μ := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨δ₁, hδ₁_pos, hfδ₁⟩ := hf hε2
  obtain ⟨δ₂, hδ₂_pos, hgδ₂⟩ := hg hε2
  refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun i s hs hμs => ?_⟩
  simp_rw [Pi.add_apply, Set.indicator_add']
  refine (eLpNorm_add_le ((hf_meas i).indicator hs) ((hg_meas i).indicator hs) hp).trans ?_
  have hε_halves : ENNReal.ofReal ε = ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_add hε2.le hε2.le, add_halves]
  rw [hε_halves]
  exact add_le_add (hfδ₁ i s hs (hμs.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))))
    (hgδ₂ i s hs (hμs.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))))
/-
**MeasureTheory.UnifIntegrable.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Unif
Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {f : ι → α → β} {p : 
ENNReal},   MeasureTheory.UnifIntegrable f p μ → MeasureTheory.UnifIntegrable (-
f) p μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_neg'`：∀ {α : Type u_1} {G : Type u_6} [inst : AddGroup G] 
(s : Set α) (f : α → G), s.indicator (-f) = -s.indicator f
· 使用定理 `MeasureTheory.eLpNorm_neg`：eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : 
Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ
-/
protected theorem neg (hf : UnifIntegrable f p μ) : UnifIntegrable (-f) p μ := by
  simp_rw [UnifIntegrable, Pi.neg_apply, Set.indicator_neg', eLpNorm_neg]
  exact hf
/-
**MeasureTheory.UnifIntegrable.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Unif
Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {f g : ι → α → β} {p 
: ENNReal},   MeasureTheory.UnifIntegrable f p μ →     MeasureTheory.UnifIntegra
ble g p μ →       1 ≤ p →         (∀ (i : ι), MeasureTheory.AEStronglyMeasurable
 (f i) μ) →           (∀ (i : ι), MeasureTheory.AEStronglyMeasurable (g i) μ) → 
MeasureTheory.UnifIntegrable (f - g) p μ
参数：∀ (i : ι), MeasureTheory.AEStronglyMeasurable (f i) μ；∀ (i : ι), MeasureTheor
y.AEStronglyMeasurable (g i) μ；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.UnifIntegrable.add`：∀ {α : Type u_1} {β : Type u_2} {ι : T
ype u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedA
ddCommGroup β] {f g : …
· 使用定理 `MeasureTheory.UnifIntegrable.neg`：∀ {α : Type u_1} {β : Type u_2} {ι : T
ype u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedA
ddCommGroup β] {f : ι …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.neg`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
protected theorem sub (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 ≤ p)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifIntegrable (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hp hf_meas fun i => (hg_meas i).neg
/-
**MeasureTheory.UnifIntegrable.ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Un
ifIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {f g : ι → α → β} {p 
: ENNReal},   MeasureTheory.UnifIntegrable f p μ → (∀ (n : ι), f n =ᵐ[μ] g n) → 
MeasureTheory.UnifIntegrable g p μ
参数：∀ (n : ι), f n =ᵐ[μ] g n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem ae_eq (hf : UnifIntegrable f p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UnifIntegrable g p μ := by
  classical
  intro ε hε
  obtain ⟨δ, hδ_pos, hfδ⟩ := hf hε
  refine ⟨δ, hδ_pos, fun n s hs hμs => (le_of_eq <| eLpNorm_congr_ae ?_).trans (hfδ n s hs hμs)⟩
  filter_upwards [hfg n] with x hx
  simp_rw [Set.indicator_apply, hx]

/-- Uniform integrability is preserved by restriction of the functions to a set. -/
/-
**MeasureTheory.UnifIntegrable.indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.UnifIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {f : ι → α → β} {p : 
ENNReal},   MeasureTheory.UnifIntegrable f p μ → ∀ (E : Set α), MeasureTheory.Un
ifIntegrable (fun i => E.indicator (f i)) p μ
参数：E : Set α；fun i => E.indicator (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 (s t : Set α) (f : α → M),   s.indicator (t.indicator f) = (s ∩ t).indicator f
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.eLpNorm_indicator_le`：eLpNorm_indicator_le (f : α -> ε) : 
eLpNorm (s.indicator f) p μ <= eLpNorm f p μ

--- 原说明 ---
Uniform integrability is preserved by restriction of the functions to a set.
-/
protected theorem indicator (hf : UnifIntegrable f p μ) (E : Set α) :
    UnifIntegrable (fun i => E.indicator (f i)) p μ := fun ε hε ↦ by
  obtain ⟨δ, hδ_pos, hε⟩ := hf hε
  refine ⟨δ, hδ_pos, fun i s hs hμs ↦ ?_⟩
  calc
    eLpNorm (s.indicator (E.indicator (f i))) p μ
      = eLpNorm (E.indicator (s.indicator (f i))) p μ := by
      simp only [indicator_indicator, inter_comm]
    _ ≤ eLpNorm (s.indicator (f i)) p μ := eLpNorm_indicator_le _
    _ ≤ ENNReal.ofReal ε := hε _ _ hs hμs

/-- Uniform integrability is preserved by restriction of the measure to a set. -/
/-
**MeasureTheory.UnifIntegrable.restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.UnifIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {f : ι → α → β} {p : 
ENNReal},   MeasureTheory.UnifIntegrable f p μ → ∀ (E : Set α), MeasureTheory.Un
ifIntegrable f p (μ.restrict E)
参数：E : Set α；μ.restrict E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict`：eLpNorm_indicator_e
q_eLpNorm_restrict {f : α -> ε} {s : Set α} (hs : MeasurableSet s) : eLpNorm (s.
indicator f) p μ = eLpNorm f p (μ.restric…
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasureTheory.eLpNorm_mono_measure`：eLpNorm_mono_measure (f : α -> ε) (h
μν : ν <= μ) : eLpNorm f p ν <= eLpNorm f p μ
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)

--- 原说明 ---
Uniform integrability is preserved by restriction of the measure to a set.
-/
protected theorem restrict (hf : UnifIntegrable f p μ) (E : Set α) :
    UnifIntegrable f p (μ.restrict E) := fun ε hε ↦ by
  obtain ⟨δ, hδ_pos, hδε⟩ := hf hε
  refine ⟨δ, hδ_pos, fun i s hs hμs ↦ ?_⟩
  rw [μ.restrict_apply hs, ← measure_toMeasurable] at hμs
  calc
    eLpNorm (indicator s (f i)) p (μ.restrict E) = eLpNorm (f i) p (μ.restrict (s ∩ E)) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hs, μ.restrict_restrict hs]
    _ ≤ eLpNorm (f i) p (μ.restrict (toMeasurable μ (s ∩ E))) :=
      eLpNorm_mono_measure _ <| Measure.restrict_mono (subset_toMeasurable _ _) le_rfl
    _ = eLpNorm (indicator (toMeasurable μ (s ∩ E)) (f i)) p μ :=
      (eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_toMeasurable _ _)).symm
    _ ≤ ENNReal.ofReal ε := hδε i _ (measurableSet_toMeasurable _ _) hμs

end UnifIntegrable

/-
**MeasureTheory.unifIntegrable_zero_meas** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：unifIntegrable_zero_meas [MeasurableSpace α] {p : Real>=0∞} {f : ι -> α ->
 β} : UnifIntegrable f p (0 : Measure α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_measure_zero`：eLpNorm_measure_zero {f : α -> ε} : 
eLpNorm f p (0 : Measure α) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem unifIntegrable_zero_meas [MeasurableSpace α] {p : ℝ≥0∞} {f : ι → α → β} :
    UnifIntegrable f p (0 : Measure α) :=
  fun ε _ => ⟨1, one_pos, fun i s _ _ => by simp⟩
/-
**MeasureTheory.unifIntegrable_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：unifIntegrable_congr_ae {p : Real>=0∞} {f g : ι -> α -> β} (hfg : forall n
, f n =ᵐ[μ] g n) : UnifIntegrable f p μ ↔ UnifIntegrable g p μ
参数：hfg : forall n, f n =ᵐ[μ] g n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.UnifIntegrable.ae_eq`：∀ {α : Type u_1} {β : Type u_2} {ι :
 Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup β] {f g : …
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem unifIntegrable_congr_ae {p : ℝ≥0∞} {f g : ι → α → β} (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UnifIntegrable f p μ ↔ UnifIntegrable g p μ :=
  ⟨fun hf => hf.ae_eq hfg, fun hg => hg.ae_eq fun n => (hfg n).symm⟩
/-
**MeasureTheory.tendsto_indicator_ge** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_indicator_ge (f : α -> β) (x : α) : Tendsto (fun M : Nat => { x | 
(M : Real) <= ‖f x‖₊ }.indicator f x) atTop (𝓝 0)
参数：f : α -> β；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_of_eventually_const`：tendsto_atTop_of_eventually_const {ι 
: Type*} [Preorder ι] {u : ι -> X} {i₀ : ι} (h : forall i >= i₀, u i = x) : Tend
sto u atTop (𝓝 x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem tendsto_indicator_ge (f : α → β) (x : α) :
    Tendsto (fun M : ℕ => { x | (M : ℝ) ≤ ‖f x‖₊ }.indicator f x) atTop (𝓝 0) := by
  refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (‖f x‖₊ : ℝ) + 1) fun n hn => ?_
  rw [Set.indicator_of_notMem]
  simp only [not_le, Set.mem_ofPred_eq]
  refine lt_of_le_of_lt (Nat.le_ceil _) ?_
  refine lt_of_lt_of_le (lt_add_one _) ?_
  norm_cast

variable {p : ℝ≥0∞}

section

variable {f : α → β}

/-- This lemma is weaker than `MeasureTheory.MemLp.integral_indicator_norm_ge_nonneg_le`
as the latter provides `0 ≤ M` and does not require the measurability of `f`. -/
/-
**MeasureTheory.MemLp.integral_indicator_norm_ge_le** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β},   MeasureTheory.MemLp f
 1 μ →     MeasureTheory.StronglyMeasurable f →       ∀ {ε : ℝ}, 0 < ε → ∃ M, ∫⁻
 (x : α), ↑‖{x | M ≤ ↑‖f x‖₊}.indicator f x‖₊ ∂μ ≤ ENNReal.ofReal ε
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.tendsto_indicator_ge`：tendsto_indicator_ge (f : α -> β) (x
 : α) : Tendsto (fun M : Nat => { x | (M : Real) <= ‖f x‖₊ }.indicator f x) atTo
p (𝓝 0)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 : Z…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `MeasureTheory.StronglyMeasurable.measurableSet_le`：measurableSet_le (hf 
: StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : MeasurableSet[m] {a 
| f a <= g a}
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.coe_nnreal_real`：Measurable.coe_nnreal_real {f : α -> Real>=0
} (hf : Measurable f) : Measurable fun x => (f x : Real)
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `MeasureTheory.StronglyMeasurable.nnnorm`：∀ {α : Type u_1} {x : Measurabl
eSpace α} {β : Type u_5} [inst : SeminormedAddCommGroup β] {f : α → β},   Measur
eTheory.StronglyMeasurable f …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.tendsto_lintegral_norm_of_dominated_convergence`：tendsto_l
integral_norm_of_dominated_convergence (F_measurable : forall n, AEStronglyMeasu
rable (F n) μ) (bound_hasFiniteIntegral : HasFinite…
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ENNReal.tendsto_atTop_zero`：∀ {β : Type u_2} [Nonempty β] [inst : Semila
tticeSup β] {f : β → ENNReal},   Filter.Tendsto f Filter.atTop (nhds 0) ↔ ∀ ε > 
0, ∃ N, ∀ n ≥ N,…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
This lemma is weaker than `MeasureTheory.MemLp.integral_indicator_norm_ge_nonneg
_le`
as the latter provides `0 ≤ M` and does not require the measurability of `f`.
-/
theorem MemLp.integral_indicator_norm_ge_le (hf : MemLp f 1 μ) (hmeas : StronglyMeasurable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, (∫⁻ x, ‖{ x | M ≤ ‖f x‖₊ }.indicator f x‖₊ ∂μ) ≤ ENNReal.ofReal ε := by
  have htendsto :
      ∀ᵐ x ∂μ, Tendsto (fun M : ℕ => { x | (M : ℝ) ≤ ‖f x‖₊ }.indicator f x) atTop (𝓝 0) :=
    univ_mem' (id fun x => tendsto_indicator_ge f x)
  have hmeas : ∀ M : ℕ, AEStronglyMeasurable ({ x | (M : ℝ) ≤ ‖f x‖₊ }.indicator f) μ := by
    intro M
    apply hf.1.indicator
    apply StronglyMeasurable.measurableSet_le stronglyMeasurable_const
      hmeas.nnnorm.measurable.coe_nnreal_real.stronglyMeasurable
  have hbound : HasFiniteIntegral (fun x => ‖f x‖) μ := by
    rw [memLp_one_iff_integrable] at hf
    exact hf.norm.2
  have : Tendsto (fun n : ℕ ↦ ∫⁻ a, ENNReal.ofReal ‖{ x | n ≤ ‖f x‖₊ }.indicator f a - 0‖ ∂μ)
      atTop (𝓝 0) := by
    refine tendsto_lintegral_norm_of_dominated_convergence hmeas hbound ?_ htendsto
    refine fun n => univ_mem' (id fun x => ?_)
    by_cases hx : (n : ℝ) ≤ ‖f x‖
    · dsimp
      rwa [Set.indicator_of_mem]
    · dsimp
      rw [Set.indicator_of_notMem, norm_zero]
      · exact norm_nonneg _
      · assumption
  rw [ENNReal.tendsto_atTop_zero] at this
  obtain ⟨M, hM⟩ := this (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  simp only [sub_zero] at hM
  refine ⟨M, ?_⟩
  convert! hM M le_rfl
  simp only [coe_nnnorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
  rfl

/-- This lemma is superseded by `MeasureTheory.MemLp.integral_indicator_norm_ge_nonneg_le`
which does not require measurability. -/
/-
**MeasureTheory.MemLp.integral_indicator_norm_ge_nonneg_le_of_meas** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β},   MeasureTheory.MemLp f
 1 μ →     MeasureTheory.StronglyMeasurable f →       ∀ {ε : ℝ}, 0 < ε → ∃ M, 0 
≤ M ∧ ∫⁻ (x : α), ‖{x | M ≤ ↑‖f x‖₊}.indicator f x‖ₑ ∂μ ≤ ENNReal.ofReal ε
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.integral_indicator_norm_ge_le`：∀ {α : Type u_1} {β :
 Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedA
ddCommGroup β]   {f : α → β},   Measure…
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
This lemma is superseded by `MeasureTheory.MemLp.integral_indicator_norm_ge_nonn
eg_le`
which does not require measurability.
-/
theorem MemLp.integral_indicator_norm_ge_nonneg_le_of_meas (hf : MemLp f 1 μ)
    (hmeas : StronglyMeasurable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ (∫⁻ x, ‖{ x | M ≤ ‖f x‖₊ }.indicator f x‖ₑ ∂μ) ≤ ENNReal.ofReal ε :=
  let ⟨M, hM⟩ := hf.integral_indicator_norm_ge_le hmeas hε
  ⟨max M 0, le_max_right _ _, by simpa⟩
/-
**MeasureTheory.MemLp.integral_indicator_norm_ge_nonneg_le** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β},   MeasureTheory.MemLp f
 1 μ →     ∀ {ε : ℝ}, 0 < ε → ∃ M, 0 ≤ M ∧ ∫⁻ (x : α), ‖{x | M ≤ ↑‖f x‖₊}.indica
tor f x‖ₑ ∂μ ≤ ENNReal.ofReal ε
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_congr_ae`：memLp_congr_ae [TopologicalSpace ε] {f g :
 α -> ε} (hfg : f =ᵐ[μ] g) : MemLp f p μ ↔ MemLp g p μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.MemLp.integral_indicator_norm_ge_nonneg_le_of_meas`：∀ {α :
 Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
[inst : NormedAddCommGroup β]   {f : α → β},   Measure…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem MemLp.integral_indicator_norm_ge_nonneg_le (hf : MemLp f 1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ (∫⁻ x, ‖{ x | M ≤ ‖f x‖₊ }.indicator f x‖ₑ ∂μ) ≤ ENNReal.ofReal ε := by
  have hf_mk : MemLp (hf.1.mk f) 1 μ := (memLp_congr_ae hf.1.ae_eq_mk).mp hf
  obtain ⟨M, hM_pos, hfM⟩ :=
    hf_mk.integral_indicator_norm_ge_nonneg_le_of_meas hf.1.stronglyMeasurable_mk hε
  refine ⟨M, hM_pos, (le_of_eq ?_).trans hfM⟩
  refine lintegral_congr_ae ?_
  filter_upwards [hf.1.ae_eq_mk] with x hx
  simp only [Set.indicator_apply, coe_nnnorm, Set.mem_ofPred_eq, hx.symm]
/-
**MeasureTheory.MemLp.eLpNormEssSup_indicator_norm_ge_eq_zero** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β},   MeasureTheory.MemLp f
 ⊤ μ →     MeasureTheory.StronglyMeasurable f → ∃ M, MeasureTheory.eLpNormEssSup
 ({x | M ≤ ↑‖f x‖₊}.indicator f) μ = 0
参数：{x | M ≤ ↑‖f x‖₊}.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.eLpNorm_lt_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict`：eLpNorm
EssSup_indicator_eq_eLpNormEssSup_restrict (hs : MeasurableSet s) : eLpNormEssSu
p (s.indicator f) μ = eLpNormEssSup f (μ.restrict s)
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Measurable.subtype_coe`：Measurable.subtype_coe {p : β -> Prop} {f : α ->
 Subtype p} (hf : Measurable f) : Measurable fun a : α => (f a : β)
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.nnnorm`：∀ {α : Type u_1} {x : Measurabl
eSpace α} {β : Type u_5} [inst : SeminormedAddCommGroup β] {f : α → β},   Measur
eTheory.StronglyMeasurable f …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_lt_toReal`：toReal_lt_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal < b.toReal ↔ a < b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `ENNReal.coe_toReal`：∀ (r : NNReal), (↑r).toReal = ↑r
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `ENNReal.Finiteness.add_ne_top`：∀ {a b : ENNReal}, a ≠ ⊤ → b ≠ ⊤ → a + b 
≠ ⊤
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
（共 40 条，此处仅展示前 30 条）
-/
theorem MemLp.eLpNormEssSup_indicator_norm_ge_eq_zero (hf : MemLp f ∞ μ)
    (hmeas : StronglyMeasurable f) :
    ∃ M : ℝ, eLpNormEssSup ({ x | M ≤ ‖f x‖₊ }.indicator f) μ = 0 := by
  have hbdd : eLpNormEssSup f μ < ∞ := hf.eLpNorm_lt_top
  refine ⟨(eLpNorm f ∞ μ + 1).toReal, ?_⟩
  rw [eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict]
  · have : μ.restrict { x : α | (eLpNorm f ⊤ μ + 1).toReal ≤ ‖f x‖₊ } = 0 := by
      simp only [coe_nnnorm, eLpNorm_exponent_top, Measure.restrict_eq_zero]
      have : { x : α | (eLpNormEssSup f μ + 1).toReal ≤ ‖f x‖ } ⊆
          { x : α | eLpNormEssSup f μ < ‖f x‖₊ } := by
        intro x hx
        rw [Set.mem_ofPred_eq, ← ENNReal.toReal_lt_toReal hbdd.ne ENNReal.coe_lt_top.ne,
          ENNReal.coe_toReal, coe_nnnorm]
        refine lt_of_lt_of_le ?_ hx
        rw [ENNReal.toReal_lt_toReal hbdd.ne]
        · exact ENNReal.lt_add_right hbdd.ne one_ne_zero
        · finiteness
      rw [← nonpos_iff_eq_zero]
      refine (measure_mono this).trans ?_
      have hle := enorm_ae_le_eLpNormEssSup f μ
      simp_rw [ae_iff, not_le] at hle
      exact nonpos_iff_eq_zero.2 hle
    rw [this, eLpNormEssSup_measure_zero]
  exact measurableSet_le measurable_const hmeas.nnnorm.measurable.subtype_coe

/-- This lemma is slightly weaker than `MeasureTheory.MemLp.eLpNorm_indicator_norm_ge_pos_le` as the
latter provides `0 < M`. -/
/-
**MeasureTheory.MemLp.eLpNorm_indicator_norm_ge_le** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {p : ENNReal} {f : α → β},   Measure
Theory.MemLp f p μ →     MeasureTheory.StronglyMeasurable f →       ∀ {ε : ℝ}, 0
 < ε → ∃ M, MeasureTheory.eLpNorm ({x | M ≤ ↑‖f x‖₊}.indicator f) p μ ≤ ENNReal.
ofReal ε
参数：{x | M ≤ ↑‖f x‖₊}.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.MemLp.eLpNormEssSup_indicator_norm_ge_eq_zero`：∀ {α : Type
 u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst
 : NormedAddCommGroup β]   {f : α → β},   Measure…
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MemLp.integral_indicator_norm_ge_nonneg_le`：∀ {α : Type u_
1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : 
NormedAddCommGroup β]   {f : α → β},   Measure…
· 使用定理 `MeasureTheory.MemLp.norm_rpow`：∀ {α : Type u_1} {E : Type u_4} {m : Meas
urableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCo
mmGroup E] {f : α →…
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用引理 `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`：eLpNorm_eq_lintegr
al_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} : e
LpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ…
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用引理 `mul_one_div_cancel`：mul_one_div_cancel (h : a != 0) : a * (1 / a) = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `ENNReal.ofReal_rpow_of_pos`：ofReal_rpow_of_pos {x p : Real} (hx_pos : 0 
< x) : ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `enorm_indicator_eq_indicator_enorm`：enorm_indicator_eq_indicator_enorm :
 ‖indicator s f a‖ₑ = indicator s (fun a => ‖f a‖ₑ) a
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `Real.norm_rpow_of_nonneg`：norm_rpow_of_nonneg {x y : Real} (hx_nonneg : 
0 <= x) : ‖x ^ y‖ = ‖x‖ ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `Real.rpow_le_rpow_iff`：rpow_le_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z <= y ^ z ↔ x <= y
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
This lemma is slightly weaker than `MeasureTheory.MemLp.eLpNorm_indicator_norm_g
e_pos_le` as the
latter provides `0 < M`.
-/
theorem MemLp.eLpNorm_indicator_norm_ge_le (hf : MemLp f p μ) (hmeas : StronglyMeasurable f) {ε : ℝ}
    (hε : 0 < ε) : ∃ M : ℝ, eLpNorm ({ x | M ≤ ‖f x‖₊ }.indicator f) p μ ≤ ENNReal.ofReal ε := by
  by_cases hp_ne_zero : p = 0
  · exact ⟨1, by simp [hp_ne_zero]⟩
  by_cases hp_ne_top : p = ∞
  · subst hp_ne_top
    obtain ⟨M, hM⟩ := hf.eLpNormEssSup_indicator_norm_ge_eq_zero hmeas
    refine ⟨M, ?_⟩
    simp only [eLpNorm_exponent_top, hM, zero_le]
  obtain ⟨M, hM', hM⟩ := MemLp.integral_indicator_norm_ge_nonneg_le
    (μ := μ) (hf.norm_rpow hp_ne_zero hp_ne_top) (Real.rpow_pos_of_pos hε p.toReal)
  refine ⟨M ^ (1 / p.toReal), ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top, ← ENNReal.rpow_one (.ofReal ε)]
  conv_rhs => rw [← mul_one_div_cancel (ENNReal.toReal_pos hp_ne_zero hp_ne_top).ne.symm]
  rw [ENNReal.rpow_mul]
  gcongr
  rw [ENNReal.ofReal_rpow_of_pos hε]
  convert! hM using 3 with x
  rw [enorm_indicator_eq_indicator_enorm, enorm_indicator_eq_indicator_enorm]
  have hiff : M ^ (1 / p.toReal) ≤ ‖f x‖₊ ↔ M ≤ ‖‖f x‖ ^ p.toReal‖₊ := by
    rw [coe_nnnorm, coe_nnnorm, Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm,
      ← Real.rpow_le_rpow_iff hM' (by positivity)
        (one_div_pos.2 <| ENNReal.toReal_pos hp_ne_zero hp_ne_top), ← Real.rpow_mul (norm_nonneg _),
      mul_one_div_cancel (ENNReal.toReal_pos hp_ne_zero hp_ne_top).ne.symm, Real.rpow_one]
  by_cases hx : x ∈ { x : α | M ^ (1 / p.toReal) ≤ ‖f x‖₊ }
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem, Real.enorm_of_nonneg (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg, ofReal_norm]
    rw [Set.mem_ofPred_eq]
    rwa [← hiff]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
    · simp [ENNReal.toReal_pos hp_ne_zero hp_ne_top]
    · rw [Set.mem_ofPred_eq]
      rwa [← hiff]

/-- This lemma implies that a single function is uniformly integrable (in the probability sense). -/
/-
**MeasureTheory.MemLp.eLpNorm_indicator_norm_ge_pos_le** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {p : ENNReal} {f : α → β},   Measure
Theory.MemLp f p μ →     MeasureTheory.StronglyMeasurable f →       ∀ {ε : ℝ}, 0
 < ε → ∃ M, 0 < M ∧ MeasureTheory.eLpNorm ({x | M ≤ ↑‖f x‖₊}.indicator f) p μ ≤ 
ENNReal.ofReal ε
参数：{x | M ≤ ↑‖f x‖₊}.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.eLpNorm_indicator_norm_ge_le`：∀ {α : Type u_1} {β : 
Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAd
dCommGroup β]   {p : ENNReal} {f : α →…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.eLpNorm_mono`：eLpNorm_mono {f : α -> F} {g : α -> G} (h : 
forall x, ‖f x‖ <= ‖g x‖) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_indicator_eq_indicator_norm`：norm_indicator_eq_indicator_norm : ‖in
dicator s f a‖ = indicator s (fun a => ‖f a‖) a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.indicator_le_indicator_apply_of_subset`：∀ {α : Type u_2} {M : Type u
_3} [inst : Preorder M] [inst_1 : Zero M] {s t : Set α} {f : α → M} {a : α},   s
 ⊆ t → 0 ≤ f a → s.indicator f a…
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
This lemma implies that a single function is uniformly integrable (in the probab
ility sense).
-/
theorem MemLp.eLpNorm_indicator_norm_ge_pos_le (hf : MemLp f p μ) (hmeas : StronglyMeasurable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ eLpNorm ({ x | M ≤ ‖f x‖₊ }.indicator f) p μ ≤ ENNReal.ofReal ε := by
  obtain ⟨M, hM⟩ := hf.eLpNorm_indicator_norm_ge_le hmeas hε
  refine
    ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), le_trans (eLpNorm_mono fun x => ?_) hM⟩
  simp only [norm_indicator_eq_indicator_norm]
  grw [← le_max_left]

end

/-
**MeasureTheory.eLpNorm_indicator_le_of_bound** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：eLpNorm_indicator_le_of_bound {f : α -> β} (hp_top : p != ∞) {ε : Real} (h
ε : 0 < ε) {M : Real} (hf : forall x, ‖f x‖ < M) : exists (δ : Real) (_ : 0 < δ)
, forall s, MeasurableSet s -> μ s <= ENNReal.ofReal δ -> eLpNorm (s.indicator f
) p μ <= ENNReal.ofReal ε
参数：hp_top : p != ∞；hε : 0 < ε；hf : forall x, ‖f x‖ < M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_zero'`：∀ {α : Type u_1} (M : Type u_3) [inst : Zero M] {s 
: Set α}, s.indicator 0 = 0
· 使用定理 `MeasureTheory.eLpNorm_zero`：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用引理 `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict`：eLpNorm_indicator_e
q_eLpNorm_restrict {f : α -> ε} {s : Set α} (hs : MeasurableSet s) : eLpNorm (s.
indicator f) p μ = eLpNorm f p (μ.restric…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.eLpNorm_le_of_ae_bound`：eLpNorm_le_of_ae_bound {f : α -> F
} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : eLpNorm f p μ <= μ Set.univ ^ p.
toReal⁻¹ * ENNReal.ofReal …
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
（共 39 条，此处仅展示前 30 条）
-/
theorem eLpNorm_indicator_le_of_bound {f : α → β} (hp_top : p ≠ ∞) {ε : ℝ} (hε : 0 < ε) {M : ℝ}
    (hf : ∀ x, ‖f x‖ < M) :
    ∃ (δ : ℝ) (_ : 0 < δ), ∀ s, MeasurableSet s →
      μ s ≤ ENNReal.ofReal δ → eLpNorm (s.indicator f) p μ ≤ ENNReal.ofReal ε := by
  by_cases! hM : M ≤ 0
  · refine ⟨1, zero_lt_one, fun s _ _ => ?_⟩
    rw [(_ : f = 0)]
    · simp
    · ext x
      rw [Pi.zero_apply, ← norm_le_zero_iff]
      exact (lt_of_lt_of_le (hf x) hM).le
  refine ⟨(ε / M) ^ p.toReal, Real.rpow_pos_of_pos (div_pos hε hM) _, fun s hs hμ => ?_⟩
  by_cases hp : p = 0
  · simp [hp]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have haebdd : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ M := by
    filter_upwards
    exact fun x => (hf x).le
  refine le_trans (eLpNorm_le_of_ae_bound haebdd) ?_
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    ← ENNReal.le_div_iff_mul_le (Or.inl _) (Or.inl ENNReal.ofReal_ne_top)]
  · rw [ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hp hp_top)]
    refine le_trans hμ ?_
    rw [← ENNReal.ofReal_rpow_of_pos (div_pos hε hM)]
    gcongr
    rw [ENNReal.ofReal_div_of_pos hM]
  · simpa only [ENNReal.ofReal_eq_zero, not_le, Ne]

section

variable {f : α → β}

/-- Auxiliary lemma for `MeasureTheory.MemLp.eLpNorm_indicator_le`. -/
/-
**MeasureTheory.MemLp.eLpNorm_indicator_le'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {p : ENNReal} {f : α → β},   1 ≤ p →
     p ≠ ⊤ →       MeasureTheory.MemLp f p μ →         MeasureTheory.StronglyMea
surable f →           ∀ {ε : ℝ},             0 < ε →               ∃ δ,         
        ∃ (_ : 0 < δ),                   ∀ (s : Set α),                     Meas
urableSet s →                       μ s ≤ ENNReal.ofReal δ → MeasureTheory.eLpNo
rm (s.indicator f) p μ ≤ 2 * ENNReal.ofReal ε
参数：_ : 0 < δ；s : Set α；s.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.MemLp.eLpNorm_indicator_norm_ge_pos_le`：∀ {α : Type u_1} {
β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Norm
edAddCommGroup β]   {p : ENNReal} {f : α →…
· 使用定理 `MeasureTheory.eLpNorm_indicator_le_of_bound`：eLpNorm_indicator_le_of_bou
nd {f : α -> β} (hp_top : p != ∞) {ε : Real} (hε : 0 < ε) {M : Real} (hf : foral
l x, ‖f x‖ < M) : exists (δ : Rea…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_indicator_eq_indicator_norm`：norm_indicator_eq_indicator_norm : ‖in
dicator s f a‖ = indicator s (fun a => ‖f a‖) a
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict`：eLpNorm_indicator_e
q_eLpNorm_restrict {f : α -> ε} {s : Set α} (hs : MeasurableSet s) : eLpNorm (s.
indicator f) p μ = eLpNorm f p (μ.restric…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.eLpNorm_add_le`：eLpNorm_add_le (hf : AEStronglyMeasurable 
f μ) (hg : AEStronglyMeasurable g μ) (hp1 : 1 <= p) : eLpNorm (f + g) p μ <= eLp
Norm f p μ + eLpNo…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Measurable.subtype_coe`：Measurable.subtype_coe {p : β -> Prop} {f : α ->
 Subtype p} (hf : Measurable f) : Measurable fun a : α => (f a : β)
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma for `MeasureTheory.MemLp.eLpNorm_indicator_le`.
-/
theorem MemLp.eLpNorm_indicator_le' (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : MemLp f p μ)
    (hmeas : StronglyMeasurable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (_ : 0 < δ), ∀ s, MeasurableSet s → μ s ≤ ENNReal.ofReal δ →
      eLpNorm (s.indicator f) p μ ≤ 2 * ENNReal.ofReal ε := by
  obtain ⟨M, hMpos, hM⟩ := hf.eLpNorm_indicator_norm_ge_pos_le hmeas hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    eLpNorm_indicator_le_of_bound (f := { x | ‖f x‖ < M }.indicator f) hp_top hε (by
      intro x
      rw [norm_indicator_eq_indicator_norm, Set.indicator_apply]
      · split_ifs with h
        exacts [h, hMpos])
  refine ⟨δ, hδpos, fun s hs hμs => ?_⟩
  rw [(_ : f = { x : α | M ≤ ‖f x‖₊ }.indicator f + { x : α | ‖f x‖ < M }.indicator f)]
  · rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
    refine le_trans (eLpNorm_add_le ?_ ?_ hp_one) ?_
    · exact StronglyMeasurable.aestronglyMeasurable
        (hmeas.indicator (measurableSet_le measurable_const hmeas.nnnorm.measurable.subtype_coe))
    · exact StronglyMeasurable.aestronglyMeasurable
        (hmeas.indicator (measurableSet_lt hmeas.nnnorm.measurable.subtype_coe measurable_const))
    · rw [two_mul]
      refine add_le_add (le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self) hM) ?_
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
      exact hδ s hs hμs
  · ext x
    by_cases hx : M ≤ ‖f x‖
    · rw [Pi.add_apply, Set.indicator_of_mem, Set.indicator_of_notMem, add_zero] <;> simpa
    · rw [Pi.add_apply, Set.indicator_of_notMem, Set.indicator_of_mem, zero_add] <;>
        simpa using hx

/-- This lemma is superseded by `MeasureTheory.MemLp.eLpNorm_indicator_le` which does not require
measurability on `f`. -/
/-
**MeasureTheory.MemLp.eLpNorm_indicator_le_of_meas** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {p : ENNReal} {f : α → β},   1 ≤ p →
     p ≠ ⊤ →       MeasureTheory.MemLp f p μ →         MeasureTheory.StronglyMea
surable f →           ∀ {ε : ℝ},             0 < ε →               ∃ δ,         
        ∃ (_ : 0 < δ),                   ∀ (s : Set α),                     Meas
urableSet s →                       μ s ≤ ENNReal.ofReal δ → MeasureTheory.eLpNo
rm (s.indicator f) p μ ≤ ENNReal.ofReal ε
参数：_ : 0 < δ；s : Set α；s.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.MemLp.eLpNorm_indicator_le'`：∀ {α : Type u_1} {β : Type u_
2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGr
oup β]   {p : ENNReal} {f : α →…
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_div_of_pos`：ofReal_div_of_pos {x y : Real} (hy : 0 < y) :
 ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.ofReal y
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ENNReal.ofReal (O
fNat.ofNat n) = OfNat.ofNat n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.mul_div_cancel`：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * (b / a) =
 b
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
This lemma is superseded by `MeasureTheory.MemLp.eLpNorm_indicator_le` which doe
s not require
measurability on `f`.
-/
theorem MemLp.eLpNorm_indicator_le_of_meas (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : MemLp f p μ)
    (hmeas : StronglyMeasurable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (_ : 0 < δ), ∀ s, MeasurableSet s → μ s ≤ ENNReal.ofReal δ →
      eLpNorm (s.indicator f) p μ ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδpos, hδ⟩ := hf.eLpNorm_indicator_le' hp_one hp_top hmeas (half_pos hε)
  refine ⟨δ, hδpos, fun s hs hμs => le_trans (hδ s hs hμs) ?_⟩
  rw [ENNReal.ofReal_div_of_pos zero_lt_two, (by simp : ENNReal.ofReal 2 = 2),
      ENNReal.mul_div_cancel] <;>
    norm_num
/-
**MeasureTheory.MemLp.eLpNorm_indicator_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.MemLp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {p : ENNReal} {f : α → β},   1 ≤ p →
     p ≠ ⊤ →       MeasureTheory.MemLp f p μ →         ∀ {ε : ℝ},           0 < 
ε →             ∃ δ,               ∃ (_ : 0 < δ),                 ∀ (s : Set α),
                   MeasurableSet s →                     μ s ≤ ENNReal.ofReal δ 
→ MeasureTheory.eLpNorm (s.indicator f) p μ ≤ ENNReal.ofReal ε
参数：_ : 0 < δ；s : Set α；s.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.eLpNorm_indicator_le_of_meas`：∀ {α : Type u_1} {β : 
Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAd
dCommGroup β]   {p : ENNReal} {f : α →…
· 使用定理 `MeasureTheory.MemLp.ae_eq`：∀ {α : Type u_1} {ε : Type u_2} {m0 : Measura
bleSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε]   [inst
_1 : Topologica…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict`：eLpNorm_indicator_e
q_eLpNorm_restrict {f : α -> ε} {s : Set α} (hs : MeasurableSet s) : eLpNorm (s.
indicator f) p μ = eLpNorm f p (μ.restric…
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.EventuallyEq.restrict`：∀ {α : Type u_2} {δ : Type u_4} {m0 : Meas
urableSpace α} {μ : MeasureTheory.Measure α} {f g : α → δ} {s : Set α},   f =ᵐ[μ
] g → f =ᵐ[μ.restr…
-/
theorem MemLp.eLpNorm_indicator_le (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : MemLp f p μ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (δ : ℝ) (_ : 0 < δ), ∀ s, MeasurableSet s → μ s ≤ ENNReal.ofReal δ →
      eLpNorm (s.indicator f) p μ ≤ ENNReal.ofReal ε := by
  have hℒp := hf
  obtain ⟨⟨f', hf', heq⟩, _⟩ := hf
  obtain ⟨δ, hδpos, hδ⟩ := (hℒp.ae_eq heq).eLpNorm_indicator_le_of_meas hp_one hp_top hf' hε
  refine ⟨δ, hδpos, fun s hs hμs => ?_⟩
  convert! hδ s hs hμs using 1
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs, eLpNorm_indicator_eq_eLpNorm_restrict hs]
  exact eLpNorm_congr_ae heq.restrict

/-- A constant function is uniformly integrable. -/
/-
**MeasureTheory.unifIntegrable_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：unifIntegrable_const {g : α -> β} (hp : 1 <= p) (hp_ne_top : p != ∞) (hg :
 MemLp g p μ) : UnifIntegrable (fun _ : ι => g) p μ
参数：hp : 1 <= p；hp_ne_top : p != ∞；hg : MemLp g p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.eLpNorm_indicator_le`：∀ {α : Type u_1} {β : Type u_2
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGro
up β]   {p : ENNReal} {f : α →…

--- 原说明 ---
A constant function is uniformly integrable.
-/
theorem unifIntegrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : MemLp g p μ) :
    UnifIntegrable (fun _ : ι => g) p μ := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hgδ⟩ := hg.eLpNorm_indicator_le hp hp_ne_top hε
  exact ⟨δ, hδ_pos, fun _ => hgδ⟩

/-- A single function is uniformly integrable. -/
/-
**MeasureTheory.unifIntegrable_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：unifIntegrable_subsingleton [Subsingleton ι] (hp_one : 1 <= p) (hp_top : p
 != ∞) {f : ι -> α -> β} (hf : forall i, MemLp (f i) p μ) : UnifIntegrable f p μ
参数：hp_one : 1 <= p；hp_top : p != ∞；hf : forall i, MemLp (f i) p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.eLpNorm_indicator_le`：∀ {α : Type u_1} {β : Type u_2
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGro
up β]   {p : ENNReal} {f : α →…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
A single function is uniformly integrable.
-/
theorem unifIntegrable_subsingleton [Subsingleton ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : ι → α → β} (hf : ∀ i, MemLp (f i) p μ) : UnifIntegrable f p μ := by
  intro ε hε
  by_cases hι : Nonempty ι
  · obtain ⟨i⟩ := hι
    obtain ⟨δ, hδpos, hδ⟩ := (hf i).eLpNorm_indicator_le hp_one hp_top hε
    refine ⟨δ, hδpos, fun j s hs hμs => ?_⟩
    convert! hδ s hs hμs
  · exact ⟨1, zero_lt_one, fun i => False.elim <| hι <| Nonempty.intro i⟩

/-- This lemma is less general than `MeasureTheory.unifIntegrable_finite` which applies to
all sequences indexed by a finite type. -/
/-
**MeasureTheory.unifIntegrable_fin** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：unifIntegrable_fin (hp_one : 1 <= p) (hp_top : p != ∞) {n : Nat} {f : Fin 
n -> α -> β} (hf : forall i, MemLp (f i) p μ) : UnifIntegrable f p μ
参数：hp_one : 1 <= p；hp_top : p != ∞；hf : forall i, MemLp (f i) p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.unifIntegrable_subsingleton`：unifIntegrable_subsingleton [
Subsingleton ι] (hp_one : 1 <= p) (hp_top : p != ∞) {f : ι -> α -> β} (hf : fora
ll i, MemLp (f i) p μ) : UnifIn…
· 使用定理 `Fin.subsingleton_zero`：Subsingleton (Fin 0)
· 使用定理 `MeasureTheory.MemLp.eLpNorm_indicator_le`：∀ {α : Type u_1} {β : Type u_2
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGro
up β]   {p : ENNReal} {f : α →…
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Fin.is_le`：∀ {n : ℕ} (i : Fin (n + 1)), ↑i ≤ n

--- 原说明 ---
This lemma is less general than `MeasureTheory.unifIntegrable_finite` which appl
ies to
all sequences indexed by a finite type.
-/
theorem unifIntegrable_fin (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {n : ℕ} {f : Fin n → α → β}
    (hf : ∀ i, MemLp (f i) p μ) : UnifIntegrable f p μ := by
  revert f
  induction n with
  | zero => exact fun {f} hf ↦ unifIntegrable_subsingleton hp_one hp_top hf
  | succ n h =>
    intro f hfLp ε hε
    let g : Fin n → α → β := fun k => f k.castSucc
    have hgLp : ∀ i, MemLp (g i) p μ := fun i => hfLp i.castSucc
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := h hgLp hε
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := (hfLp (Fin.last n)).eLpNorm_indicator_le hp_one hp_top hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, fun i s hs hμs => ?_⟩
    by_cases! hi : i.val < n
    · rw [(_ : f i = g ⟨i.val, hi⟩)]
      · exact hδ₁ _ s hs (le_trans hμs <| ENNReal.ofReal_le_ofReal <| min_le_left _ _)
      · simp [g]
    · obtain rfl : i = Fin.last n := Fin.ext (le_antisymm (Fin.is_le i) hi)
      exact hδ₂ _ hs (le_trans hμs <| ENNReal.ofReal_le_ofReal <| min_le_right _ _)

/-- A finite sequence of Lp functions is uniformly integrable. -/
/-
**MeasureTheory.unifIntegrable_finite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：unifIntegrable_finite [Finite ι] (hp_one : 1 <= p) (hp_top : p != ∞) {f : 
ι -> α -> β} (hf : forall i, MemLp (f i) p μ) : UnifIntegrable f p μ
参数：hp_one : 1 <= p；hp_top : p != ∞；hf : forall i, MemLp (f i) p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MeasureTheory.unifIntegrable_fin`：unifIntegrable_fin (hp_one : 1 <= p) (
hp_top : p != ∞) {n : Nat} {f : Fin n -> α -> β} (hf : forall i, MemLp (f i) p μ
) : UnifIntegrable f p…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x

--- 原说明 ---
A finite sequence of Lp functions is uniformly integrable.
-/
theorem unifIntegrable_finite [Finite ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, MemLp (f i) p μ) : UnifIntegrable f p μ := by
  obtain ⟨n, hn⟩ := Finite.exists_equiv_fin ι
  intro ε hε
  let g : Fin n → α → β := f ∘ hn.some.symm
  have hg : ∀ i, MemLp (g i) p μ := fun _ => hf _
  obtain ⟨δ, hδpos, hδ⟩ := unifIntegrable_fin hp_one hp_top hg hε
  refine ⟨δ, hδpos, fun i s hs hμs => ?_⟩
  simpa [g] using hδ (hn.some i) s hs hμs

end

/-- A sequence of uniformly integrable functions which converges μ-a.e. converges in Lp. -/
/-
**MeasureTheory.tendsto_Lp_finite_of_tendsto_ae_of_meas** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：tendsto_Lp_finite_of_tendsto_ae_of_meas [IsFiniteMeasure μ] (hp : 1 <= p) 
(hp' : p != ∞) {f : Nat -> α -> β} {g : α -> β} (hf : forall n, StronglyMeasurab
le (f n)) (hg : StronglyMeasurable g) (hg' : MemLp g p μ) (hui : UnifIntegrable 
f p μ) (hfg : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Tendsto 
(fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)
参数：hp : 1 <= p；hp' : p != ∞；hf : forall n, StronglyMeasurable (f n)；hg : Strongl
yMeasurable g；hg' : MemLp g p μ；hui : UnifIntegrable f p μ；hfg : forallᵐ x ∂μ, T
endsto (fun n => f n x) atTop (𝓝 (g x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_atTop_zero`：∀ {β : Type u_2} [Nonempty β] [inst : Semila
tticeSup β] {f : β → ENNReal},   Filter.Tendsto f Filter.atTop (nhds 0) ↔ ∀ ε > 
0, ∃ N, ∀ n ≥ N,…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_measure_zero`：eLpNorm_measure_zero {f : α -> ε} : 
eLpNorm f p (0 : Measure α) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `MeasureTheory.measureUnivNNReal_pos`：measureUnivNNReal_pos [IsFiniteMeas
ure μ] (hμ : μ != 0) : 0 < measureUnivNNReal μ
· 使用定理 `MeasureTheory.MemLp.eLpNorm_indicator_le`：∀ {α : Type u_1} {β : Type u_2
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGro
up β]   {p : ENNReal} {f : α →…
· 使用定理 `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto'`：tendstoUniformlyOn_of_a
e_tendsto' [IsFiniteMeasure μ] (hf : forall n, StronglyMeasurable (f n)) (hg : S
tronglyMeasurable g) (hfg : forallᵐ x…
· 使用定理 `instCountableNat`：Countable ℕ
（共 96 条，此处仅展示前 30 条）

--- 原说明 ---
A sequence of uniformly integrable functions which converges μ-a.e. converges in
 Lp.
-/
theorem tendsto_Lp_finite_of_tendsto_ae_of_meas [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hg' : MemLp g p μ) (hui : UnifIntegrable f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases! h : ∞ ≤ ε
  · rw [top_le_iff] at h
    exact ⟨0, fun n _ => by simp [h]⟩
  by_cases hμ : μ = 0
  · exact ⟨0, fun n _ => by simp [hμ]⟩
  have hε' : 0 < ε.toReal / 3 := div_pos (ENNReal.toReal_pos hε.ne' h.ne) (by simp)
  have hdivp : 0 ≤ 1 / p.toReal := by positivity
  have hpow : 0 < measureUnivNNReal μ ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (measureUnivNNReal_pos hμ) _
  obtain ⟨δ₁, hδ₁, heLpNorm₁⟩ := hui hε'
  obtain ⟨δ₂, hδ₂, heLpNorm₂⟩ := hg'.eLpNorm_indicator_le hp hp' hε'
  obtain ⟨t, htm, ht₁, ht₂⟩ := tendstoUniformlyOn_of_ae_tendsto' hf hg hfg (lt_min hδ₁ hδ₂)
  rw [Metric.tendstoUniformlyOn_iff] at ht₂
  specialize ht₂ (ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)))
    (div_pos (ENNReal.toReal_pos (gt_iff_lt.1 hε).ne.symm h.ne) (mul_pos (by simp) hpow))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ht₂; clear ht₂
  refine ⟨N, fun n hn => ?_⟩
  rw [← t.indicator_self_add_compl (f n - g)]
  grw [eLpNorm_add_le (((hf n).sub hg).indicator htm).aestronglyMeasurable
    (((hf n).sub hg).indicator htm.compl).aestronglyMeasurable hp, sub_eq_add_neg,
    Set.indicator_add' t, Set.indicator_neg', eLpNorm_add_le
    ((hf n).indicator htm).aestronglyMeasurable (hg.indicator htm).neg.aestronglyMeasurable hp]
  have hnf : eLpNorm (t.indicator (f n)) p μ ≤ ENNReal.ofReal (ε.toReal / 3) := by
    refine heLpNorm₁ n t htm (le_trans ht₁ ?_)
    rw [ENNReal.ofReal_le_ofReal_iff hδ₁.le]
    exact min_le_left _ _
  have hng : eLpNorm (t.indicator g) p μ ≤ ENNReal.ofReal (ε.toReal / 3) := by
    refine heLpNorm₂ t htm (le_trans ht₁ ?_)
    rw [ENNReal.ofReal_le_ofReal_iff hδ₂.le]
    exact min_le_right _ _
  have hlt : eLpNorm (tᶜ.indicator (f n - g)) p μ ≤ ENNReal.ofReal (ε.toReal / 3) := by
    specialize hN n hn
    have : 0 ≤ ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)) := by positivity
    have := eLpNorm_indicator_sub_le_of_dist_bdd μ hp' htm.compl this fun x hx =>
      (dist_comm (g x) (f n x) ▸ (hN x hx).le :
        dist (f n x) (g x) ≤ ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)))
    refine le_trans this ?_
    rw [div_mul_eq_div_mul_one_div, ← ENNReal.ofReal_toReal (measure_lt_top μ tᶜ).ne,
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hdivp, ← ENNReal.ofReal_mul, mul_assoc]
    · refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hε'.le ?_)
      rw [mul_comm, mul_one_div, div_le_one]
      · gcongr
        refine (ENNReal.toReal_le_of_le_ofReal (measureUnivNNReal_pos hμ).le ?_)
        rw [ENNReal.ofReal_coe_nnreal, coe_measureUnivNNReal]
        exact measure_mono (Set.subset_univ _)
      · exact Real.rpow_pos_of_pos (measureUnivNNReal_pos hμ) _
    · positivity
  have : ENNReal.ofReal (ε.toReal / 3) = ε / 3 := by
    rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 3 by simp), ENNReal.ofReal_toReal h.ne]
    simp
  rw [this] at hnf hng hlt
  rw [eLpNorm_neg, ← ENNReal.add_thirds ε, ← sub_eq_add_neg]
  gcongr

/-- A sequence of uniformly integrable functions which converges μ-a.e. converges in Lp. -/
/-
**MeasureTheory.tendsto_Lp_finite_of_tendsto_ae** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：tendsto_Lp_finite_of_tendsto_ae [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p
 != ∞) {f : Nat -> α -> β} {g : α -> β} (hf : forall n, AEStronglyMeasurable (f 
n) μ) (hg : MemLp g p μ) (hui : UnifIntegrable f p μ) (hfg : forallᵐ x ∂μ, Tends
to (fun n => f n x) atTop (𝓝 (g x))) : Tendsto (fun n => eLpNorm (f n - g) p μ) 
atTop (𝓝 0)
参数：hp : 1 <= p；hp' : p != ∞；hf : forall n, AEStronglyMeasurable (f n) μ；hg : Mem
Lp g p μ；hui : UnifIntegrable f p μ；hfg : forallᵐ x ∂μ, Tendsto (fun n => f n x)
 atTop (𝓝 (g x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.EventuallyEq.sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f - f' =ᶠ[l] g - g'
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae_of_meas`：tendsto_Lp_finite
_of_tendsto_ae_of_meas [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞) {f : Nat
 -> α -> β} {g : α -> β} (hf : forall n, St…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `MeasureTheory.MemLp.ae_eq`：∀ {α : Type u_1} {ε : Type u_2} {m0 : Measura
bleSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε]   [inst
_1 : Topologica…
· 使用定理 `MeasureTheory.UnifIntegrable.ae_eq`：∀ {α : Type u_1} {β : Type u_2} {ι :
 Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup β] {f g : …
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
A sequence of uniformly integrable functions which converges μ-a.e. converges in
 Lp.
-/
theorem tendsto_Lp_finite_of_tendsto_ae [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ)
    (hui : UnifIntegrable f p μ) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  have : ∀ n, eLpNorm (f n - g) p μ = eLpNorm ((hf n).mk (f n) - hg.1.mk g) p μ :=
    fun n => eLpNorm_congr_ae ((hf n).ae_eq_mk.sub hg.1.ae_eq_mk)
  simp_rw [this]
  refine tendsto_Lp_finite_of_tendsto_ae_of_meas hp hp' (fun n => (hf n).stronglyMeasurable_mk)
    hg.1.stronglyMeasurable_mk (hg.ae_eq hg.1.ae_eq_mk) (hui.ae_eq fun n => (hf n).ae_eq_mk) ?_
  have h_ae_forall_eq : ∀ᵐ x ∂μ, ∀ n, f n x = (hf n).mk (f n) x := by
    rw [ae_all_iff]
    exact fun n => (hf n).ae_eq_mk
  filter_upwards [hfg, h_ae_forall_eq, hg.1.ae_eq_mk] with x hx_tendsto hxf_eq hxg_eq
  rw [← hxg_eq]
  convert! hx_tendsto using 1
  ext1 n
  exact (hxf_eq n).symm

variable {f : ℕ → α → β} {g : α → β}
/-
**MeasureTheory.unifIntegrable_of_tendsto_Lp_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：unifIntegrable_of_tendsto_Lp_zero (hp : 1 <= p) (hp' : p != ∞) (hf : foral
l n, MemLp (f n) p μ) (hf_tendsto : Tendsto (fun n => eLpNorm (f n) p μ) atTop (
𝓝 0)) : UnifIntegrable f p μ
参数：hp : 1 <= p；hp' : p != ∞；hf : forall n, MemLp (f n) p μ；hf_tendsto : Tendsto 
(fun n => eLpNorm (f n) p μ) atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_atTop_zero`：∀ {β : Type u_2} [Nonempty β] [inst : Semila
tticeSup β] {f : β → ENNReal},   Filter.Tendsto f Filter.atTop (nhds 0) ↔ ∀ ε > 
0, ∃ N, ∀ n ≥ N,…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.unifIntegrable_fin`：unifIntegrable_fin (hp_one : 1 <= p) (
hp_top : p != ∞) {n : Nat} {f : Fin n -> α -> β} (hf : forall i, MemLp (f i) p μ
) : UnifIntegrable f p…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `MeasureTheory.eLpNorm_indicator_le`：eLpNorm_indicator_le (f : α -> ε) : 
eLpNorm (s.indicator f) p μ <= eLpNorm f p μ
-/
theorem unifIntegrable_of_tendsto_Lp_zero (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, MemLp (f n) p μ)
    (hf_tendsto : Tendsto (fun n => eLpNorm (f n) p μ) atTop (𝓝 0)) : UnifIntegrable f p μ := by
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at hf_tendsto
  obtain ⟨N, hN⟩ := hf_tendsto (ENNReal.ofReal ε) (by simpa)
  let F : Fin N → α → β := fun n => f n
  have hF : ∀ n, MemLp (F n) p μ := fun n => hf n
  obtain ⟨δ₁, hδpos₁, hδ₁⟩ := unifIntegrable_fin hp hp' hF hε
  refine ⟨δ₁, hδpos₁, fun n s hs hμs => ?_⟩
  by_cases! hn : n < N
  · exact hδ₁ ⟨n, hn⟩ s hs hμs
  · exact (eLpNorm_indicator_le _).trans (hN n hn)

/-- Convergence in Lp implies uniform integrability. -/
/-
**MeasureTheory.unifIntegrable_of_tendsto_Lp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：unifIntegrable_of_tendsto_Lp (hp : 1 <= p) (hp' : p != ∞) (hf : forall n, 
MemLp (f n) p μ) (hg : MemLp g p μ) (hfg : Tendsto (fun n => eLpNorm (f n - g) p
 μ) atTop (𝓝 0)) : UnifIntegrable f p μ
参数：hp : 1 <= p；hp' : p != ∞；hf : forall n, MemLp (f n) p μ；hg : MemLp g p μ；hfg 
: Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.UnifIntegrable.add`：∀ {α : Type u_1} {β : Type u_2} {ι : T
ype u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedA
ddCommGroup β] {f g : …
· 使用定理 `MeasureTheory.unifIntegrable_const`：unifIntegrable_const {g : α -> β} (h
p : 1 <= p) (hp_ne_top : p != ∞) (hg : MemLp g p μ) : UnifIntegrable (fun _ : ι 
=> g) p μ
· 使用定理 `MeasureTheory.unifIntegrable_of_tendsto_Lp_zero`：unifIntegrable_of_tends
to_Lp_zero (hp : 1 <= p) (hp' : p != ∞) (hf : forall n, MemLp (f n) p μ) (hf_ten
dsto : Tendsto (fun n => eLpNorm (f n…
· 使用定理 `MeasureTheory.MemLp.sub`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} [inst : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measur
e α} {f g : α…
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Convergence in Lp implies uniform integrability.
-/
theorem unifIntegrable_of_tendsto_Lp (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, MemLp (f n) p μ)
    (hg : MemLp g p μ) (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)) :
    UnifIntegrable f p μ := by
  have : f = (fun _ => g) + fun n => f n - g := by ext1 n; simp
  rw [this]
  refine UnifIntegrable.add ?_ ?_ hp (fun _ => hg.aestronglyMeasurable)
      fun n => (hf n).1.sub hg.aestronglyMeasurable
  · exact unifIntegrable_const hp hp' hg
  · exact unifIntegrable_of_tendsto_Lp_zero hp hp' (fun n => (hf n).sub hg) hfg

/-- Forward direction of Vitali's convergence theorem: if `f` is a sequence of uniformly integrable
functions that converge in measure to some function `g` in a finite measure space, then `f`
converge in Lp to `g`. -/
/-
**MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：tendsto_Lp_finite_of_tendstoInMeasure [IsFiniteMeasure μ] (hp : 1 <= p) (h
p' : p != ∞) (hf : forall n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ) (h
ui : UnifIntegrable f p μ) (hfg : TendstoInMeasure μ f atTop g) : Tendsto (fun n
 => eLpNorm (f n - g) p μ) atTop (𝓝 0)
参数：hp : 1 <= p；hp' : p != ∞；hf : forall n, AEStronglyMeasurable (f n) μ；hg : Mem
Lp g p μ；hui : UnifIntegrable f p μ；hfg : TendstoInMeasure μ f atTop g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_of_subseq_tendsto`：tendsto_of_subseq_tendsto {ι : Type*} 
{x : ι -> α} {f : Filter α} {l : Filter ι} [l.IsCountablyGenerated] (hxy : foral
l ns : Nat -> ι, Tends…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`：∀ {α : Type u_1} {
E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Pseu
doEMetricSpace E]   {f : ℕ → α → E} {g : α…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`：tendsto_Lp_finite_of_tend
sto_ae [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞) {f : Nat -> α -> β} {g :
 α -> β} (hf : forall n, AEStrongly…

--- 原说明 ---
Forward direction of Vitali's convergence theorem: if `f` is a sequence of unifo
rmly integrable
functions that converge in measure to some function `g` in a finite measure spac
e, then `f`
converge in Lp to `g`.
-/
theorem tendsto_Lp_finite_of_tendstoInMeasure [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ) (hui : UnifIntegrable f p μ)
    (hfg : TendstoInMeasure μ f atTop g) : Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms'⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact ⟨ms,
    tendsto_Lp_finite_of_tendsto_ae hp hp' (fun _ => hf _) hg (fun ε hε =>
      let ⟨δ, hδ, hδ'⟩ := hui hε
      ⟨δ, hδ, fun i s hs hμs => hδ' _ s hs hμs⟩)
      hms'⟩

/-- **Vitali's convergence theorem**: A sequence of functions `f` converges to `g` in Lp if and
only if it is uniformly integrable and converges to `g` in measure. -/
/-
**MeasureTheory.tendstoInMeasure_iff_tendsto_Lp_finite** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：tendstoInMeasure_iff_tendsto_Lp_finite [IsFiniteMeasure μ] (hp : 1 <= p) (
hp' : p != ∞) (hf : forall n, MemLp (f n) p μ) (hg : MemLp g p μ) : TendstoInMea
sure μ f atTop g ∧ UnifIntegrable f p μ ↔ Tendsto (fun n => eLpNorm (f n - g) p 
μ) atTop (𝓝 0)
参数：hp : 1 <= p；hp' : p != ∞；hf : forall n, MemLp (f n) p μ；hg : MemLp g p μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure`：tendsto_Lp_finite_o
f_tendstoInMeasure [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞) (hf : forall
 n, AEStronglyMeasurable (f n) μ) (hg : M…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`：tendstoInMeasure_of_t
endsto_eLpNorm [NormedAddCommGroup E] {l : Filter ι} (hp_ne_zero : p != 0) (hf :
 forall n, AEStronglyMeasurable (f n) μ…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `MeasureTheory.unifIntegrable_of_tendsto_Lp`：unifIntegrable_of_tendsto_Lp
 (hp : 1 <= p) (hp' : p != ∞) (hf : forall n, MemLp (f n) p μ) (hg : MemLp g p μ
) (hfg : Tendsto (fun n => eLpNo…

--- 原说明 ---
**Vitali's convergence theorem**: A sequence of functions `f` converges to `g` i
n Lp if and
only if it is uniformly integrable and converges to `g` in measure.
-/
theorem tendstoInMeasure_iff_tendsto_Lp_finite [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ↔
      Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  ⟨fun h => tendsto_Lp_finite_of_tendstoInMeasure hp hp' (fun n => (hf n).1) hg h.2 h.1, fun h =>
    ⟨tendstoInMeasure_of_tendsto_eLpNorm (lt_of_lt_of_le zero_lt_one hp).ne.symm
        (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h,
      unifIntegrable_of_tendsto_Lp hp hp' hf hg h⟩⟩

/-- This lemma is superseded by `unifIntegrable_of` which do not require `C` to be positive. -/
/-
**MeasureTheory.unifIntegrable_of'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：unifIntegrable_of' (hp : 1 <= p) (hp' : p != ∞) {f : ι -> α -> β} (hf : fo
rall i, StronglyMeasurable (f i)) (h : forall ε : Real, 0 < ε -> exists C : Real
>=0, 0 < C ∧ forall i, eLpNorm ({ x | C <= ‖f i x‖₊ }.indicator (f i)) p μ <= EN
NReal.ofReal ε) : UnifIntegrable f p μ
参数：hp : 1 <= p；hp' : p != ∞；hf : forall i, StronglyMeasurable (f i)；h : forall ε
 : Real, 0 < ε -> exists C : Real>=0, 0 < C ∧ forall i, eLpNorm ({ x | C <= ‖f i
 x‖₊ }.indicator (f i)) p μ <= ENNReal.ofReal ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MeasureTheory.unifIntegrable_zero_meas`：unifIntegrable_zero_meas [Measur
ableSpace α] {p : Real>=0∞} {f : ι -> α -> β} : UnifIntegrable f p (0 : Measure 
α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_eq_zero_iff`：eLpNorm_eq_zero_iff {f : α -> ε} (hf 
: AEStronglyMeasurable f μ) (h0 : p != 0) : eLpNorm f p μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `indicator_meas_zero`：indicator_meas_zero (hs : μ s = 0) : indicator s f 
=ᵐ[μ] 0
（共 91 条，此处仅展示前 30 条）

--- 原说明 ---
This lemma is superseded by `unifIntegrable_of` which do not require `C` to be p
ositive.
-/
theorem unifIntegrable_of' (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, StronglyMeasurable (f i))
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, 0 < C ∧
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε) :
    UnifIntegrable f p μ := by
  have hpzero := (lt_of_lt_of_le zero_lt_one hp).ne.symm
  by_cases hμ : μ Set.univ = 0
  · rw [Measure.measure_univ_eq_zero] at hμ
    exact hμ.symm ▸ unifIntegrable_zero_meas
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := h (ε / 2) (half_pos hε)
  refine ⟨(ε / (2 * C)) ^ ENNReal.toReal p,
    Real.rpow_pos_of_pos (div_pos hε (mul_pos two_pos (NNReal.coe_pos.2 hCpos))) _,
    fun i s hs hμs => ?_⟩
  by_cases hμs' : μ s = 0
  · rw [(eLpNorm_eq_zero_iff ((hf i).indicator hs).aestronglyMeasurable hpzero).2
        (indicator_meas_zero hμs')]
    simp
  calc
    eLpNorm (Set.indicator s (f i)) p μ ≤
        eLpNorm (Set.indicator (s ∩ { x | C ≤ ‖f i x‖₊ }) (f i)) p μ +
          eLpNorm (Set.indicator (s ∩ { x | ‖f i x‖₊ < C }) (f i)) p μ := by
      refine le_trans (Eq.le ?_) (eLpNorm_add_le
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (hs.inter (stronglyMeasurable_const.measurableSet_le (hf i).nnnorm))))
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (hs.inter ((hf i).nnnorm.measurableSet_lt stronglyMeasurable_const))))
        hp)
      congr
      change _ = fun x => (s ∩ { x : α | C ≤ ‖f i x‖₊ }).indicator (f i) x +
        (s ∩ { x : α | ‖f i x‖₊ < C }).indicator (f i) x
      rw [← Set.indicator_union_of_disjoint]
      · rw [← Set.inter_union_distrib_left, (by ext; simp [le_or_gt] :
            { x : α | C ≤ ‖f i x‖₊ } ∪ { x : α | ‖f i x‖₊ < C } = Set.univ),
          Set.inter_univ]
      · refine (Disjoint.inf_right' _ ?_).inf_left' _
        rw [disjoint_iff_inf_le]
        rintro x ⟨hx₁, hx₂⟩
        rw [Set.mem_ofPred_eq] at hx₁ hx₂
        exact False.elim (hx₂.ne (eq_of_le_of_not_lt hx₁ (not_lt.2 hx₂.le)).symm)
    _ ≤ eLpNorm (Set.indicator { x | C ≤ ‖f i x‖₊ } (f i)) p μ +
        (C : ℝ≥0∞) * μ s ^ (1 / ENNReal.toReal p) := by
      refine add_le_add
        (eLpNorm_mono fun x => norm_indicator_le_of_subset Set.inter_subset_right _ _) ?_
      rw [← Set.indicator_indicator]
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
      have : ∀ᵐ x ∂μ.restrict s, ‖{ x : α | ‖f i x‖₊ < C }.indicator (f i) x‖ ≤ C := by
        filter_upwards
        simp_rw [norm_indicator_eq_indicator_norm]
        exact Set.indicator_le' (fun x (hx : _ < _) => hx.le) fun _ _ => NNReal.coe_nonneg _
      refine le_trans (eLpNorm_le_of_ae_bound this) ?_
      rw [mul_comm, Measure.restrict_apply' hs, Set.univ_inter, ENNReal.ofReal_coe_nnreal, one_div]
    _ ≤ ENNReal.ofReal (ε / 2) + C * ENNReal.ofReal (ε / (2 * C)) := by
      grw [hC i]
      gcongr
      rwa [one_div, ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hpzero hp'),
        ENNReal.ofReal_rpow_of_pos (div_pos hε (mul_pos two_pos (NNReal.coe_pos.2 hCpos)))]
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
      gcongr
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _), ← div_div,
        mul_div_cancel₀ _ (NNReal.coe_pos.2 hCpos).ne.symm]
    _ ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
/-
**MeasureTheory.unifIntegrable_of** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：unifIntegrable_of (hp : 1 <= p) (hp' : p != ∞) {f : ι -> α -> β} (hf : for
all i, AEStronglyMeasurable (f i) μ) (h : forall ε : Real, 0 < ε -> exists C : R
eal>=0, forall i, eLpNorm ({ x | C <= ‖f i x‖₊ }.indicator (f i)) p μ <= ENNReal
.ofReal ε) : UnifIntegrable f p μ
参数：hp : 1 <= p；hp' : p != ∞；hf : forall i, AEStronglyMeasurable (f i) μ；h : fora
ll ε : Real, 0 < ε -> exists C : Real>=0, forall i, eLpNorm ({ x | C <= ‖f i x‖₊
 }.indicator (f i)) p μ <= ENNReal.ofReal ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.UnifIntegrable.ae_eq`：∀ {α : Type u_1} {β : Type u_2} {ι :
 Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup β] {f g : …
· 使用定理 `MeasureTheory.unifIntegrable_of'`：unifIntegrable_of' (hp : 1 <= p) (hp' 
: p != ∞) {f : ι -> α -> β} (hf : forall i, StronglyMeasurable (f i)) (h : foral
l ε : Real, 0 < ε -> e…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.eLpNorm_mono`：eLpNorm_mono {f : α -> F} {g : α -> G} (h : 
forall x, ‖f x‖ <= ‖g x‖) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `norm_indicator_eq_indicator_norm`：norm_indicator_eq_indicator_norm : ‖in
dicator s f a‖ = indicator s (fun a => ‖f a‖) a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.indicator_le_indicator_apply_of_subset`：∀ {α : Type u_2} {M : Type u
_3} [inst : Preorder M] [inst_1 : Zero M] {s t : Set α} {f : α → M} {a : α},   s
 ⊆ t → 0 ≤ f a → s.indicator f a…
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem unifIntegrable_of (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0,
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε) :
    UnifIntegrable f p μ := by
  set g : ι → α → β := fun i => (hf i).choose
  refine
    (unifIntegrable_of' hp hp' (fun i => (Exists.choose_spec <| hf i).1) fun ε hε => ?_).ae_eq
      fun i => (Exists.choose_spec <| hf i).2.symm
  obtain ⟨C, hC⟩ := h ε hε
  have hCg : ∀ i, eLpNorm ({ x | C ≤ ‖g i x‖₊ }.indicator (g i)) p μ ≤ ENNReal.ofReal ε := by
    intro i
    refine le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)
    filter_upwards [(Exists.choose_spec <| hf i).2] with x hx
    by_cases hfx : x ∈ { x | C ≤ ‖f i x‖₊ }
    · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
      rwa [Set.mem_ofPred, hx] at hfx
    · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
      rwa [Set.mem_ofPred, hx] at hfx
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun i => le_trans (eLpNorm_mono fun x => ?_) (hCg i)⟩
  rw [norm_indicator_eq_indicator_norm, norm_indicator_eq_indicator_norm]
  grw [← le_max_left]

/-- If `fn` is `UnifIntegrable`, then the family of limits in probability of sequences of `fn` is
`UnifIntegrable`. -/
/-
**MeasureTheory.UnifIntegrable.unifIntegrable_of_tendstoInMeasure** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.UnifIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {p : ENNReal} {κ : Ty
pe u_4} (u : Filter κ) [u.NeBot] [u.IsCountablyGenerated]   {fn : ι → α → β},   
MeasureTheory.UnifIntegrable fn p μ →     (∀ (i : ι), MeasureTheory.AEStronglyMe
asurable (fn i) μ) → MeasureTheory.UnifIntegrable (fun f => ↑f) p μ
参数：u : Filter κ；∀ (i : ι), MeasureTheory.AEStronglyMeasurable (fn i) μ；fun f => 
↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.eLpNorm_le_of_tendstoInMeasure`：eLpNorm_le_of_tendstoInMea
sure {ι : Type*} [SeminormedAddGroup E] {u : Filter ι} [NeBot u] [IsCountablyGen
erated u] {f : ι -> α -> E} {g : α…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.TendstoInMeasure.indicator`：indicator {F : Type*} [PseudoE
MetricSpace F] [Zero F] {f : ι -> α -> F} {g : α -> F} (hg : TendstoInMeasure μ 
f l g) (s : Set α) : TendstoIn…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 : Z…

--- 原说明 ---
If `fn` is `UnifIntegrable`, then the family of limits in probability of sequenc
es of `fn` is
`UnifIntegrable`.
-/
lemma UnifIntegrable.unifIntegrable_of_tendstoInMeasure {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β} (hUI : UnifIntegrable fn p μ)
    (hfn : ∀ i, AEStronglyMeasurable (fn i) μ) :
    UnifIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      TendstoInMeasure μ (fn ∘ ni) u g}) ↦ f.1) p μ := by
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hUI hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht ht' => ?_⟩
  refine eLpNorm_le_of_tendstoInMeasure
    (Eventually.of_forall fun n => hδ' (s n) t ht ht') (hs.indicator t) ?_
  exact fun n => (hfn (s n)).indicator ht

/-- If `fn` is `UnifIntegrable`, then the family of a.e. limits of sequences of `fn` is
`UnifIntegrable`. -/
/-
**MeasureTheory.UnifIntegrable.unifIntegrable_of_ae_tendsto** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.UnifIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {p : ENNReal} {κ : Ty
pe u_4} (u : Filter κ) [u.NeBot] [u.IsCountablyGenerated]   {fn : ι → α → β},   
MeasureTheory.UnifIntegrable fn p μ →     (∀ (i : ι), MeasureTheory.AEStronglyMe
asurable (fn i) μ) → MeasureTheory.UnifIntegrable (fun f => ↑f) p μ
参数：u : Filter κ；∀ (i : ι), MeasureTheory.AEStronglyMeasurable (fn i) μ；fun f => 
↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto`：eLpNorm_le_of_ae_tendsto {ι :
 Type*} {u : Filter ι} [NeBot u] [IsCountablyGenerated u] {f : ι -> α -> E} {g :
 α -> E} {C : Real>=0∞} (bound …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.AEStronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 : Z…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `fn` is `UnifIntegrable`, then the family of a.e. limits of sequences of `fn`
 is
`UnifIntegrable`.
-/
lemma UnifIntegrable.unifIntegrable_of_ae_tendsto {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β} (hUI : UnifIntegrable fn p μ)
    (hfn : ∀ i, AEStronglyMeasurable (fn i) μ) :
    UnifIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ fn (ni n) x) u (𝓝 (g x))}) ↦ f.1) p μ := by
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hUI hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht ht' => ?_⟩
  refine Lp.eLpNorm_le_of_ae_tendsto
    (Eventually.of_forall (f := u) fun n => hδ' (s n) t ht ht') ?_ ?_
  · exact fun n => (hfn (s n)).indicator ht
  · filter_upwards [hs] with a ha
    by_cases memt : a ∈ t
    · simpa [memt]
    · simp [memt]

end UnifIntegrable

section UniformIntegrable

/-! `UniformIntegrable`

In probability theory, uniform integrability normally refers to the condition that a sequence
of function `(fₙ)` satisfies for all `ε > 0`, there exists some `C ≥ 0` such that
`∫ x in {|fₙ| ≥ C}, fₙ x ∂μ ≤ ε` for all `n`.

In this section, we will develop some API for `UniformIntegrable` and prove that
`UniformIntegrable` is equivalent to this definition of uniform integrability.
-/


variable {p : ℝ≥0∞} {f : ι → α → β}

/-
**MeasureTheory.uniformIntegrable_zero_meas** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：uniformIntegrable_zero_meas [MeasurableSpace α] : UniformIntegrable f p (0
 : Measure α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_zero_measure`：aestronglyMeasurable_ze
ro_measure (f : α -> β) : AEStronglyMeasurable[m] f (0 : Measure[m₀] α)
· 使用定理 `MeasureTheory.unifIntegrable_zero_meas`：unifIntegrable_zero_meas [Measur
ableSpace α] {p : Real>=0∞} {f : ι -> α -> β} : UnifIntegrable f p (0 : Measure 
α)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.eLpNorm_measure_zero`：eLpNorm_measure_zero {f : α -> ε} : 
eLpNorm f p (0 : Measure α) = 0
-/
theorem uniformIntegrable_zero_meas [MeasurableSpace α] : UniformIntegrable f p (0 : Measure α) :=
  ⟨fun _ => aestronglyMeasurable_zero_measure _, unifIntegrable_zero_meas, 0,
    fun _ => eLpNorm_measure_zero.le⟩
/-
**MeasureTheory.UniformIntegrable.ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.UniformIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {p : ENNReal} {f g : 
ι → α → β},   MeasureTheory.UniformIntegrable f p μ → (∀ (n : ι), f n =ᵐ[μ] g n)
 → MeasureTheory.UniformIntegrable g p μ
参数：∀ (n : ι), f n =ᵐ[μ] g n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.congr`：congr (hf : AEStronglyMeasurab
le[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.unifIntegrable_congr_ae`：unifIntegrable_congr_ae {p : Real
>=0∞} {f g : ι -> α -> β} (hfg : forall n, f n =ᵐ[μ] g n) : UnifIntegrable f p μ
 ↔ UnifIntegrable g p μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
-/
theorem UniformIntegrable.ae_eq {g : ι → α → β} (hf : UniformIntegrable f p μ)
    (hfg : ∀ n, f n =ᵐ[μ] g n) : UniformIntegrable g p μ := by
  obtain ⟨hfm, hunif, C, hC⟩ := hf
  refine ⟨fun i => (hfm i).congr (hfg i), (unifIntegrable_congr_ae hfg).1 hunif, C, fun i => ?_⟩
  rw [← eLpNorm_congr_ae (hfg i)]
  exact hC i
/-
**MeasureTheory.uniformIntegrable_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：uniformIntegrable_congr_ae {g : ι -> α -> β} (hfg : forall n, f n =ᵐ[μ] g 
n) : UniformIntegrable f p μ ↔ UniformIntegrable g p μ
参数：hfg : forall n, f n =ᵐ[μ] g n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.UniformIntegrable.ae_eq`：∀ {α : Type u_1} {β : Type u_2} {
ι : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : No
rmedAddCommGroup β] {p : EN…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem uniformIntegrable_congr_ae {g : ι → α → β} (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UniformIntegrable f p μ ↔ UniformIntegrable g p μ :=
  ⟨fun h => h.ae_eq hfg, fun h => h.ae_eq fun i => (hfg i).symm⟩

/-- A finite sequence of Lp functions is uniformly integrable in the probability sense. -/
/-
**MeasureTheory.uniformIntegrable_finite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：uniformIntegrable_finite [Finite ι] (hp_one : 1 <= p) (hp_top : p != ∞) (h
f : forall i, MemLp (f i) p μ) : UniformIntegrable f p μ
参数：hp_one : 1 <= p；hp_top : p != ∞；hf : forall i, MemLp (f i) p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.unifIntegrable_finite`：unifIntegrable_finite [Finite ι] (h
p_one : 1 <= p) (hp_top : p != ∞) {f : ι -> α -> β} (hf : forall i, MemLp (f i) 
p μ) : UnifIntegrable f p…
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Finset.max'_lt_iff`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset 
α) (H : s.Nonempty) {x : α}, s.max' H < x ↔ ∀ y ∈ s, y < x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩

--- 原说明 ---
A finite sequence of Lp functions is uniformly integrable in the probability sen
se.
-/
theorem uniformIntegrable_finite [Finite ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (hf : ∀ i, MemLp (f i) p μ) : UniformIntegrable f p μ := by
  cases nonempty_fintype ι
  refine ⟨fun n => (hf n).1, unifIntegrable_finite hp_one hp_top hf, ?_⟩
  by_cases hι : Nonempty ι
  · choose _ hf using hf
    set C := (Finset.univ.image fun i : ι => eLpNorm (f i) p μ).max'
      ⟨eLpNorm (f hι.some) p μ, Finset.mem_image.2 ⟨hι.some, Finset.mem_univ _, rfl⟩⟩
    refine ⟨C.toNNReal, fun i => ?_⟩
    rw [ENNReal.coe_toNNReal]
    · exact Finset.le_max' (α := ℝ≥0∞) _ _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    · refine ne_of_lt ((Finset.max'_lt_iff _ _).2 fun y hy => ?_)
      rw [Finset.mem_image] at hy
      obtain ⟨i, -, rfl⟩ := hy
      exact hf i
  · exact ⟨0, fun i => False.elim <| hι <| Nonempty.intro i⟩

/-- A single function is uniformly integrable in the probability sense. -/
/-
**MeasureTheory.uniformIntegrable_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：uniformIntegrable_subsingleton [Subsingleton ι] (hp_one : 1 <= p) (hp_top 
: p != ∞) (hf : forall i, MemLp (f i) p μ) : UniformIntegrable f p μ
参数：hp_one : 1 <= p；hp_top : p != ∞；hf : forall i, MemLp (f i) p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.uniformIntegrable_finite`：uniformIntegrable_finite [Finite
 ι] (hp_one : 1 <= p) (hp_top : p != ∞) (hf : forall i, MemLp (f i) p μ) : Unifo
rmIntegrable f p μ
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite

--- 原说明 ---
A single function is uniformly integrable in the probability sense.
-/
theorem uniformIntegrable_subsingleton [Subsingleton ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (hf : ∀ i, MemLp (f i) p μ) : UniformIntegrable f p μ :=
  uniformIntegrable_finite hp_one hp_top hf

/-- A constant sequence of functions is uniformly integrable in the probability sense. -/
/-
**MeasureTheory.uniformIntegrable_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：uniformIntegrable_const {g : α -> β} (hp : 1 <= p) (hp_ne_top : p != ∞) (h
g : MemLp g p μ) : UniformIntegrable (fun _ : ι => g) p μ
参数：hp : 1 <= p；hp_ne_top : p != ∞；hg : MemLp g p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.unifIntegrable_const`：unifIntegrable_const {g : α -> β} (h
p : 1 <= p) (hp_ne_top : p != ∞) (hg : MemLp g p μ) : UnifIntegrable (fun _ : ι 
=> g) p μ
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A constant sequence of functions is uniformly integrable in the probability sens
e.
-/
theorem uniformIntegrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : MemLp g p μ) :
    UniformIntegrable (fun _ : ι => g) p μ :=
  ⟨fun _ => hg.1, unifIntegrable_const hp hp_ne_top hg,
    ⟨(eLpNorm g p μ).toNNReal, fun _ => le_of_eq (ENNReal.coe_toNNReal hg.2.ne).symm⟩⟩

/-- This lemma is superseded by `uniformIntegrable_of` which only requires
`AEStronglyMeasurable`. -/
/-
**MeasureTheory.uniformIntegrable_of'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：uniformIntegrable_of' [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞) (hf
 : forall i, StronglyMeasurable (f i)) (h : forall ε : Real, 0 < ε -> exists C :
 Real>=0, forall i, eLpNorm ({ x | C <= ‖f i x‖₊ }.indicator (f i)) p μ <= ENNRe
al.ofReal ε) : UniformIntegrable f p μ
参数：hp : 1 <= p；hp' : p != ∞；hf : forall i, StronglyMeasurable (f i)；h : forall ε
 : Real, 0 < ε -> exists C : Real>=0, forall i, eLpNorm ({ x | C <= ‖f i x‖₊ }.i
ndicator (f i)) p μ <= ENNReal.ofReal ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.unifIntegrable_of`：unifIntegrable_of (hp : 1 <= p) (hp' : 
p != ∞) {f : ι -> α -> β} (hf : forall i, AEStronglyMeasurable (f i) μ) (h : for
all ε : Real, 0 < ε -…
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.eLpNorm_mono_enorm`：eLpNorm_mono_enorm {f : α -> ε} {g : α
 -> ε'} (h : forall x, ‖f x‖ₑ <= ‖g x‖ₑ) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.eLpNorm_add_le`：eLpNorm_add_le (hf : AEStronglyMeasurable 
f μ) (hg : AEStronglyMeasurable g μ) (hp1 : 1 <= p) : eLpNorm (f + g) p μ <= eLp
Norm f p μ + eLpNo…
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用引理 `MeasureTheory.StronglyMeasurable.measurableSet_lt`：measurableSet_lt (hf 
: StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : MeasurableSet[m] {a 
| f a < g a}
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.nnnorm`：∀ {α : Type u_1} {x : Measurabl
eSpace α} {β : Type u_5} [inst : SeminormedAddCommGroup β] {f : α → β},   Measur
eTheory.StronglyMeasurable f …
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用引理 `MeasureTheory.StronglyMeasurable.measurableSet_le`：measurableSet_le (hf 
: StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : MeasurableSet[m] {a 
| f a <= g a}
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `nnnorm_indicator_eq_indicator_nnnorm`：nnnorm_indicator_eq_indicator_nnno
rm : ‖indicator s f a‖₊ = indicator s (fun a => ‖f a‖₊) a
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
This lemma is superseded by `uniformIntegrable_of` which only requires
`AEStronglyMeasurable`.
-/
theorem uniformIntegrable_of' [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ i, StronglyMeasurable (f i))
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0,
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε) :
    UniformIntegrable f p μ := by
  refine ⟨fun i => (hf i).aestronglyMeasurable,
    unifIntegrable_of hp hp' (fun i => (hf i).aestronglyMeasurable) h, ?_⟩
  obtain ⟨C, hC⟩ := h 1 one_pos
  refine ⟨((C : ℝ≥0∞) * μ Set.univ ^ p.toReal⁻¹ + 1).toNNReal, fun i => ?_⟩
  calc
    eLpNorm (f i) p μ ≤
        eLpNorm ({ x : α | ‖f i x‖₊ < C }.indicator (f i)) p μ +
          eLpNorm ({ x : α | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ := by
      refine le_trans (eLpNorm_mono_enorm fun x => ?_) (eLpNorm_add_le
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator ((hf i).nnnorm.measurableSet_lt stronglyMeasurable_const)))
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (stronglyMeasurable_const.measurableSet_le (hf i).nnnorm))) hp)
      rw [Pi.add_apply, Set.indicator_apply]
      split_ifs with hx
      · rw [Set.indicator_of_notMem, add_zero]
        simpa using hx
      · rw [Set.indicator_of_mem, zero_add]
        simpa using hx
    _ ≤ (C : ℝ≥0∞) * μ Set.univ ^ p.toReal⁻¹ + 1 := by
      have : ∀ᵐ x ∂μ, ‖{ x : α | ‖f i x‖₊ < C }.indicator (f i) x‖₊ ≤ C := by
        filter_upwards
        simp_rw [nnnorm_indicator_eq_indicator_nnnorm]
        exact Set.indicator_le fun x (hx : _ < _) => hx.le
      refine add_le_add (le_trans (eLpNorm_le_of_ae_bound this) ?_) (ENNReal.ofReal_one ▸ hC i)
      simp_rw [NNReal.val_eq_coe, ENNReal.ofReal_coe_nnreal, mul_comm]
      exact le_rfl
    _ = ((C : ℝ≥0∞) * μ Set.univ ^ p.toReal⁻¹ + 1 : ℝ≥0∞).toNNReal := by
      rw [ENNReal.coe_toNNReal (by finiteness)]

/-- A sequence of functions `(fₙ)` is uniformly integrable in the probability sense if for all
`ε > 0`, there exists some `C` such that `∫ x in {|fₙ| ≥ C}, fₙ x ∂μ ≤ ε` for all `n`. -/
/-
**MeasureTheory.uniformIntegrable_of** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：uniformIntegrable_of [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞) (hf 
: forall i, AEStronglyMeasurable (f i) μ) (h : forall ε : Real, 0 < ε -> exists 
C : Real>=0, forall i, eLpNorm ({ x | C <= ‖f i x‖₊ }.indicator (f i)) p μ <= EN
NReal.ofReal ε) : UniformIntegrable f p μ
参数：hp : 1 <= p；hp' : p != ∞；hf : forall i, AEStronglyMeasurable (f i) μ；h : fora
ll ε : Real, 0 < ε -> exists C : Real>=0, forall i, eLpNorm ({ x | C <= ‖f i x‖₊
 }.indicator (f i)) p μ <= ENNReal.ofReal ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.UniformIntegrable.ae_eq`：∀ {α : Type u_1} {β : Type u_2} {
ι : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : No
rmedAddCommGroup β] {p : EN…
· 使用定理 `MeasureTheory.uniformIntegrable_of'`：uniformIntegrable_of' [IsFiniteMeas
ure μ] (hp : 1 <= p) (hp' : p != ∞) (hf : forall i, StronglyMeasurable (f i)) (h
 : forall ε : Real, 0 < ε…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0

--- 原说明 ---
A sequence of functions `(fₙ)` is uniformly integrable in the probability sense 
if for all
`ε > 0`, there exists some `C` such that `∫ x in {|fₙ| ≥ C}, fₙ x ∂μ ≤ ε` for al
l `n`.
-/
theorem uniformIntegrable_of [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0,
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε) :
    UniformIntegrable f p μ := by
  set g : ι → α → β := fun i => (hf i).choose
  have hgmeas : ∀ i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hf i).1
  have hgeq : ∀ i, g i =ᵐ[μ] f i := fun i => (Exists.choose_spec <| hf i).2.symm
  refine (uniformIntegrable_of' hp hp' hgmeas fun ε hε => ?_).ae_eq hgeq
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun i => le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)⟩
  filter_upwards [(Exists.choose_spec <| hf i).2] with x hx
  by_cases hfx : x ∈ { x | C ≤ ‖f i x‖₊ }
  · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
    rwa [Set.mem_ofPred, hx] at hfx
  · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
    rwa [Set.mem_ofPred, hx] at hfx

/-- This lemma is superseded by `UniformIntegrable.spec` which does not require measurability. -/
/-
**MeasureTheory.UniformIntegrable.spec'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.UniformIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {p : ENNReal} {f : ι 
→ α → β},   p ≠ 0 →     p ≠ ⊤ →       (∀ (i : ι), MeasureTheory.StronglyMeasurab
le (f i)) →         MeasureTheory.UniformIntegrable f p μ →           ∀ {ε : ℝ},
             0 < ε → ∃ C, ∀ (i : ι), MeasureTheory.eLpNorm ({x | C ≤ ‖f i x‖₊}.i
ndicator (f i)) p μ ≤ ENNReal.ofReal ε
参数：∀ (i : ι), MeasureTheory.StronglyMeasurable (f i)；i : ι；{x | C ≤ ‖f i x‖₊}.in
dicator (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_div_nonneg`：one_div_nonneg : 0 <= 1 / a ↔ 0 <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `MeasureTheory.le_eLpNorm_of_bddBelow`：le_eLpNorm_of_bddBelow (hp : p != 
0) (hp' : p != ∞) {f : α -> F} (C : Real>=0) {s : Set α} (hs : MeasurableSet s) 
(hf : forallᵐ x ∂μ, x in s…
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instSecondCountableTopology`：SecondCountableTopology NNReal
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.nnnorm`：∀ {α : Type u_1} {x : Measurabl
eSpace α} {β : Type u_5} [inst : SeminormedAddCommGroup β] {f : α → β},   Measur
eTheory.StronglyMeasurable f …
（共 73 条，此处仅展示前 30 条）

--- 原说明 ---
This lemma is superseded by `UniformIntegrable.spec` which does not require meas
urability.
-/
theorem UniformIntegrable.spec' (hp : p ≠ 0) (hp' : p ≠ ∞) (hf : ∀ i, StronglyMeasurable (f i))
    (hfu : UniformIntegrable f p μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε := by
  obtain ⟨-, hfu, M, hM⟩ := hfu
  obtain ⟨δ, hδpos, hδ⟩ := hfu hε
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, ∀ i, μ { x | C ≤ ‖f i x‖₊ } ≤ ENNReal.ofReal δ := by
    by_contra! hcon
    choose ℐ hℐ using hcon
    lift δ to ℝ≥0 using hδpos.le
    have : ∀ C : ℝ≥0, C • (δ : ℝ≥0∞) ^ (1 / p.toReal) ≤ eLpNorm (f (ℐ C)) p μ := by
      intro C
      calc
        C • (δ : ℝ≥0∞) ^ (1 / p.toReal) ≤ C • μ { x | C ≤ ‖f (ℐ C) x‖₊ } ^ (1 / p.toReal) := by
          rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
          simp_rw [ENNReal.ofReal_coe_nnreal] at hℐ
          refine mul_le_mul' le_rfl
            (ENNReal.rpow_le_rpow (hℐ C).le (one_div_nonneg.2 ENNReal.toReal_nonneg))
        _ ≤ eLpNorm ({ x | C ≤ ‖f (ℐ C) x‖₊ }.indicator (f (ℐ C))) p μ := by
          refine le_eLpNorm_of_bddBelow hp hp' _
            (measurableSet_le measurable_const (hf _).nnnorm.measurable)
            (Eventually.of_forall fun x hx => ?_)
          rwa [nnnorm_indicator_eq_indicator_nnnorm, Set.indicator_of_mem hx]
        _ ≤ eLpNorm (f (ℐ C)) p μ := eLpNorm_indicator_le _
    specialize this (2 * max M 1 * δ⁻¹ ^ (1 / p.toReal))
    rw [← ENNReal.coe_rpow_of_nonneg _ (one_div_nonneg.2 ENNReal.toReal_nonneg), ← ENNReal.coe_smul,
      smul_eq_mul, mul_assoc, NNReal.inv_rpow,
      inv_mul_cancel₀ (NNReal.rpow_pos (NNReal.coe_pos.1 hδpos)).ne.symm, mul_one, ENNReal.coe_mul,
      ← NNReal.inv_rpow] at this
    refine (lt_of_le_of_lt (le_trans
      (hM <| ℐ <| 2 * max M 1 * δ⁻¹ ^ (1 / p.toReal)) (le_max_left (M : ℝ≥0∞) 1))
        (lt_of_lt_of_le ?_ this)).ne rfl
    rw [← ENNReal.coe_one, ← ENNReal.coe_max, ← ENNReal.coe_mul, ENNReal.coe_lt_coe]
    exact lt_two_mul_self (lt_max_of_lt_right one_pos)
  exact ⟨C, fun i => hδ i _ (measurableSet_le measurable_const (hf i).nnnorm.measurable) (hC i)⟩
/-
**MeasureTheory.UniformIntegrable.spec** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
UniformIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {p : ENNReal} {f : ι 
→ α → β},   p ≠ 0 →     p ≠ ⊤ →       MeasureTheory.UniformIntegrable f p μ →   
      ∀ {ε : ℝ},           0 < ε → ∃ C, ∀ (i : ι), MeasureTheory.eLpNorm ({x | C
 ≤ ‖f i x‖₊}.indicator (f i)) p μ ≤ ENNReal.ofReal ε
参数：i : ι；{x | C ≤ ‖f i x‖₊}.indicator (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `MeasureTheory.UniformIntegrable.ae_eq`：∀ {α : Type u_1} {β : Type u_2} {
ι : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : No
rmedAddCommGroup β] {p : EN…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.UniformIntegrable.spec'`：∀ {α : Type u_1} {β : Type u_2} {
ι : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : No
rmedAddCommGroup β] {p : EN…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
-/
theorem UniformIntegrable.spec (hp : p ≠ 0) (hp' : p ≠ ∞) (hfu : UniformIntegrable f p μ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε := by
  set g : ι → α → β := fun i => (hfu.1 i).choose
  have hgmeas : ∀ i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hfu.1 i).1
  have hgunif : UniformIntegrable g p μ := hfu.ae_eq fun i => (Exists.choose_spec <| hfu.1 i).2
  obtain ⟨C, hC⟩ := hgunif.spec' hp hp' hgmeas hε
  refine ⟨C, fun i => le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)⟩
  filter_upwards [(Exists.choose_spec <| hfu.1 i).2] with x hx
  by_cases hfx : x ∈ { x | C ≤ ‖f i x‖₊ }
  · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
    rwa [Set.mem_ofPred, hx] at hfx
  · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
    rwa [Set.mem_ofPred, hx] at hfx

/-- The definition of uniform integrable in mathlib is equivalent to the definition commonly
found in literature. -/
/-
**MeasureTheory.uniformIntegrable_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：uniformIntegrable_iff [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞) : U
niformIntegrable f p μ ↔ (forall i, AEStronglyMeasurable (f i) μ) ∧ forall ε : R
eal, 0 < ε -> exists C : Real>=0, forall i, eLpNorm ({ x | C <= ‖f i x‖₊ }.indic
ator (f i)) p μ <= ENNReal.ofReal ε
参数：hp : 1 <= p；hp' : p != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.UniformIntegrable.spec`：∀ {α : Type u_1} {β : Type u_2} {ι
 : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup β] {p : EN…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MeasureTheory.uniformIntegrable_of`：uniformIntegrable_of [IsFiniteMeasur
e μ] (hp : 1 <= p) (hp' : p != ∞) (hf : forall i, AEStronglyMeasurable (f i) μ) 
(h : forall ε : Real, 0 …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The definition of uniform integrable in mathlib is equivalent to the definition 
commonly
found in literature.
-/
theorem uniformIntegrable_iff [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    UniformIntegrable f p μ ↔
      (∀ i, AEStronglyMeasurable (f i) μ) ∧
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0,
          ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε :=
  ⟨fun h => ⟨h.1, fun _ => h.spec (lt_of_lt_of_le zero_lt_one hp).ne.symm hp'⟩,
    fun h => uniformIntegrable_of hp hp' h.1 h.2⟩

/-- The averaging of a uniformly integrable sequence is also uniformly integrable. -/
/-
**MeasureTheory.uniformIntegrable_average** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：uniformIntegrable_average {E : Type*} [NormedAddCommGroup E] [NormedSpace 
Real E] (hp : 1 <= p) {f : Nat -> α -> E} (hf : UniformIntegrable f p μ) : Unifo
rmIntegrable (fun (n : Nat) => (n : Real)⁻¹ • (∑ i in Finset.range n, f i)) p μ
参数：hp : 1 <= p；hf : UniformIntegrable f p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_smul`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} {𝕜 : Type…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Finset.aestronglyMeasurable_sum`：∀ {α : Type u_1} {m₀ : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {M : Type u_5} [inst : AddCommMonoid M]   [inst
_1 : TopologicalSpace…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.indicator_sum`：∀ {ι : Type u_1} {κ : Type u_2} {β : Type u_4} [in
st : AddCommMonoid β] (s : Finset ι) (t : Set κ) (f : ι → κ → β),   t.indicator 
(∑ i ∈ s, …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.eLpNorm_sum_le`：eLpNorm_sum_le [ContinuousAdd ε'] {ι} {f :
 ι -> α -> ε'} {s : Finset ι} (hfs : forall i, i in s -> AEStronglyMeasurable (f
 i) μ) (hp1 : 1 <=…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 : Z…
· 使用引理 `Set.indicator_const_smul`：indicator_const_smul (s : Set α) (r : R) (f : 
α -> M) : indicator s (r • f ·) = (r • indicator s f ·)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Set.indicator_zero'`：∀ {α : Type u_1} (M : Type u_3) [inst : Zero M] {s 
: Set α}, s.indicator 0 = 0
· 使用定理 `MeasureTheory.eLpNorm_zero`：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.eLpNorm_const_smul`：eLpNorm_const_smul (c : 𝕜) (f : α -> F
) (p : Real>=0∞) (μ : Measure α) : eLpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
The averaging of a uniformly integrable sequence is also uniformly integrable.
-/
theorem uniformIntegrable_average
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hp : 1 ≤ p) {f : ℕ → α → E} (hf : UniformIntegrable f p μ) :
    UniformIntegrable (fun (n : ℕ) => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, f i)) p μ := by
  obtain ⟨hf₁, hf₂, hf₃⟩ := hf
  refine ⟨fun n => ?_, fun ε hε => ?_, ?_⟩
  · exact (Finset.aestronglyMeasurable_sum _ fun i _ => hf₁ i).const_smul _
  · obtain ⟨δ, hδ₁, hδ₂⟩ := hf₂ hε
    refine ⟨δ, hδ₁, fun n s hs hle => ?_⟩
    simp_rw [Finset.smul_sum, Finset.indicator_sum]
    refine le_trans (eLpNorm_sum_le (fun i _ => ((hf₁ i).const_smul _).indicator hs) hp) ?_
    have this i : s.indicator ((n : ℝ)⁻¹ • f i) = (↑n : ℝ)⁻¹ • s.indicator (f i) :=
      indicator_const_smul _ _ _
    obtain rfl | hn := eq_or_ne n 0
    · simp
    simp_rw [this, eLpNorm_const_smul, ← Finset.mul_sum]
    rw [enorm_inv (by positivity), Real.enorm_natCast, ← ENNReal.div_eq_inv_mul]
    refine ENNReal.div_le_of_le_mul' ?_
    simpa using Finset.sum_le_card_nsmul (.range n) _ _ fun i _ => hδ₂ _ _ hs hle
  · obtain ⟨C, hC⟩ := hf₃
    simp_rw [Finset.smul_sum]
    refine ⟨C, fun n => (eLpNorm_sum_le (fun i _ => (hf₁ i).const_smul _) hp).trans ?_⟩
    obtain rfl | hn := eq_or_ne n 0
    · simp
    simp_rw [eLpNorm_const_smul, ← Finset.mul_sum]
    rw [enorm_inv (by positivity), Real.enorm_natCast, ← ENNReal.div_eq_inv_mul]
    refine ENNReal.div_le_of_le_mul' ?_
    simpa using Finset.sum_le_card_nsmul (.range n) _ _ fun i _ => hC i

/-- The averaging of a uniformly integrable real-valued sequence is also uniformly integrable. -/
/-
**MeasureTheory.uniformIntegrable_average_real** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：uniformIntegrable_average_real (hp : 1 <= p) {f : Nat -> α -> Real} (hf : 
UniformIntegrable f p μ) : UniformIntegrable (fun n => (∑ i in Finset.range n, f
 i) / (n : α -> Real)) p μ
参数：hp : 1 <= p；hf : UniformIntegrable f p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.uniformIntegrable_average`：uniformIntegrable_average {E : 
Type*} [NormedAddCommGroup E] [NormedSpace Real E] (hp : 1 <= p) {f : Nat -> α -
> E} (hf : UniformIntegrable …

--- 原说明 ---
The averaging of a uniformly integrable real-valued sequence is also uniformly i
ntegrable.
-/
theorem uniformIntegrable_average_real (hp : 1 ≤ p) {f : ℕ → α → ℝ} (hf : UniformIntegrable f p μ) :
    UniformIntegrable (fun n => (∑ i ∈ Finset.range n, f i) / (n : α → ℝ)) p μ := by
  convert! uniformIntegrable_average hp hf using 2 with n
  ext x
  simp [div_eq_inv_mul]

/-- If `fn` is `UniformIntegrable`, then the family of limits in probability of sequences of `fn` is
`UniformIntegrable`. -/
/-
**MeasureTheory.UniformIntegrable.uniformIntegrable_of_tendstoInMeasure** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.UniformIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {p : ENNReal} {κ : Ty
pe u_4} (u : Filter κ) [u.NeBot] [u.IsCountablyGenerated]   {fn : ι → α → β}, Me
asureTheory.UniformIntegrable fn p μ → MeasureTheory.UniformIntegrable (fun f =>
 ↑f) p μ
参数：u : Filter κ；fun f => ↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.TendstoInMeasure.aestronglyMeasurable`：∀ {α : Type u_1} {ι
 : Type u_2} {E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   [inst : PseudoEMetricSpace E] {u : Fi…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.UnifIntegrable.unifIntegrable_of_tendstoInMeasure`：∀ {α : 
Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheo
ry.Measure α}   [inst : NormedAddCommGroup β] {p : EN…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `MeasureTheory.eLpNorm_le_of_tendstoInMeasure`：eLpNorm_le_of_tendstoInMea
sure {ι : Type*} [SeminormedAddGroup E] {u : Filter ι} [NeBot u] [IsCountablyGen
erated u] {f : ι -> α -> E} {g : α…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
If `fn` is `UniformIntegrable`, then the family of limits in probability of sequ
ences of `fn` is
`UniformIntegrable`.
-/
lemma UniformIntegrable.uniformIntegrable_of_tendstoInMeasure {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β} (hUI : UniformIntegrable fn p μ) :
    UniformIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      TendstoInMeasure μ (fn ∘ ni) u g}) ↦ f.1) p μ := by
  refine ⟨fun ⟨f, s, hs⟩ => ?_, hUI.2.1.unifIntegrable_of_tendstoInMeasure u (fun i => hUI.1 i), ?_⟩
  · exact hs.aestronglyMeasurable (fun n => hUI.1 (s n))
  · obtain ⟨C, hC⟩ := hUI.2.2
    exact ⟨C, fun ⟨f, s, hs⟩ => eLpNorm_le_of_tendstoInMeasure
      (Eventually.of_forall fun n => hC (s n)) hs (fun n => hUI.1 (s n))⟩

/-- Suppose `f` is a sequence of functions that converges in measure to `g`. If `f` is
`UniformIntegrable`, then `g` is in `Lp`. -/
/-
**MeasureTheory.UniformIntegrable.memLp_of_tendstoInMeasure** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.UniformIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {p : ENNReal} {κ : Type u_4} {u : Fi
lter κ} [u.NeBot] [u.IsCountablyGenerated] {f : κ → α → β} {g : α → β},   Measur
eTheory.UniformIntegrable f p μ → MeasureTheory.TendstoInMeasure μ f u g → Measu
reTheory.MemLp g p μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.UniformIntegrable.memLp`：∀ {α : Type u_1} {β : Type u_2} {
ι : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : No
rmedAddCommGroup β] {f : ι …
· 使用定理 `MeasureTheory.UniformIntegrable.uniformIntegrable_of_tendstoInMeasure`：∀
 {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   [inst : NormedAddCommGroup β] {p : EN…

--- 原说明 ---
Suppose `f` is a sequence of functions that converges in measure to `g`. If `f` 
is
`UniformIntegrable`, then `g` is in `Lp`.
-/
lemma UniformIntegrable.memLp_of_tendstoInMeasure {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β}
    (hUI : UniformIntegrable f p μ) (htends : TendstoInMeasure μ f u g) :
    MemLp g p μ := by
  simpa using (hUI.uniformIntegrable_of_tendstoInMeasure u).memLp ⟨g, ⟨fun n => n, htends⟩⟩

/-- Suppose `f` is a sequence of functions that converges in measure to `g`. If `f` is
`UniformIntegrable`, then `g` is integrable. -/
/-
**MeasureTheory.UniformIntegrable.integrable_of_tendstoInMeasure** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.UniformIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {κ : Type u_4} {u : Filter κ} [u.NeB
ot] [u.IsCountablyGenerated] {f : κ → α → β} {g : α → β},   MeasureTheory.Unifor
mIntegrable f 1 μ → MeasureTheory.TendstoInMeasure μ f u g → MeasureTheory.Integ
rable g μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.UniformIntegrable.memLp_of_tendstoInMeasure`：∀ {α : Type u
_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst :
 NormedAddCommGroup β]   {p : ENNReal} {κ : Typ…

--- 原说明 ---
Suppose `f` is a sequence of functions that converges in measure to `g`. If `f` 
is
`UniformIntegrable`, then `g` is integrable.
-/
lemma UniformIntegrable.integrable_of_tendstoInMeasure {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β}
    (hUI : UniformIntegrable f 1 μ) (htends : TendstoInMeasure μ f u g) :
    Integrable g μ :=
  memLp_one_iff_integrable.mp (hUI.memLp_of_tendstoInMeasure htends)

/-- If `fn` is `UniformIntegrable`, then the family of a.e. limits of sequences of `fn` is
`UniformIntegrable`. -/
/-
**MeasureTheory.UniformIntegrable.uniformIntegrable_of_ae_tendsto** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.UniformIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {p : ENNReal} {κ : Ty
pe u_4} (u : Filter κ) [u.NeBot] [u.IsCountablyGenerated]   {fn : ι → α → β}, Me
asureTheory.UniformIntegrable fn p μ → MeasureTheory.UniformIntegrable (fun f =>
 ↑f) p μ
参数：u : Filter κ；fun f => ↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `aestronglyMeasurable_of_tendsto_ae`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}  
 {ι : Type u_5} [Topolog…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.UnifIntegrable.unifIntegrable_of_ae_tendsto`：∀ {α : Type u
_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Mea
sure α}   [inst : NormedAddCommGroup β] {p : EN…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto`：eLpNorm_le_of_ae_tendsto {ι :
 Type*} {u : Filter ι} [NeBot u] [IsCountablyGenerated u] {f : ι -> α -> E} {g :
 α -> E} {C : Real>=0∞} (bound …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
If `fn` is `UniformIntegrable`, then the family of a.e. limits of sequences of `
fn` is
`UniformIntegrable`.
-/
lemma UniformIntegrable.uniformIntegrable_of_ae_tendsto {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β}
    (hUI : UniformIntegrable fn p μ) :
    UniformIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ fn (ni n) x) u (𝓝 (g x))}) ↦ f.1) p μ := by
  refine ⟨fun ⟨f, s, hs⟩ => ?_, hUI.2.1.unifIntegrable_of_ae_tendsto u (fun i => hUI.1 i), ?_⟩
  · exact aestronglyMeasurable_of_tendsto_ae u (fun n => hUI.1 (s n)) hs
  · obtain ⟨C, hC⟩ := hUI.2.2
    exact ⟨C, fun ⟨f, s, hs⟩ => Lp.eLpNorm_le_of_ae_tendsto
      (Eventually.of_forall fun n => hC (s n)) (fun n => hUI.1 (s n)) hs⟩

/-- Suppose `f` is a sequence of functions that converges a.e. to `g`. If `f` is
`UniformIntegrable`, then `g` is in `Lp`. -/
/-
**MeasureTheory.UniformIntegrable.memLp_of_ae_tendsto** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.UniformIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {p : ENNReal} {κ : Type u_4} {u : Fi
lter κ} [u.NeBot] [u.IsCountablyGenerated] {f : κ → α → β} {g : α → β},   Measur
eTheory.UniformIntegrable f p μ →     (∀ᵐ (x : α) ∂μ, Filter.Tendsto (fun n => f
 n x) u (nhds (g x))) → MeasureTheory.MemLp g p μ
参数：∀ᵐ (x : α) ∂μ, Filter.Tendsto (fun n => f n x) u (nhds (g x))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.UniformIntegrable.memLp`：∀ {α : Type u_1} {β : Type u_2} {
ι : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : No
rmedAddCommGroup β] {f : ι …
· 使用定理 `MeasureTheory.UniformIntegrable.uniformIntegrable_of_ae_tendsto`：∀ {α : 
Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheo
ry.Measure α}   [inst : NormedAddCommGroup β] {p : EN…

--- 原说明 ---
Suppose `f` is a sequence of functions that converges a.e. to `g`. If `f` is
`UniformIntegrable`, then `g` is in `Lp`.
-/
lemma UniformIntegrable.memLp_of_ae_tendsto {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β} (hUI : UniformIntegrable f p μ)
    (htends : ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ f n x) u (𝓝 (g x))) :
    MemLp g p μ := by
  simpa using (hUI.uniformIntegrable_of_ae_tendsto u).memLp ⟨g, ⟨fun n => n, htends⟩⟩

/-- Suppose `f` is a sequence of functions that converges a.e. to `g`. If `f` is
`UniformIntegrable`, then `g` is integrable. -/
/-
**MeasureTheory.UniformIntegrable.integrable_of_ae_tendsto** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.UniformIntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {κ : Type u_4} {u : Filter κ} [u.NeB
ot] [u.IsCountablyGenerated] {f : κ → α → β} {g : α → β},   MeasureTheory.Unifor
mIntegrable f 1 μ →     (∀ᵐ (x : α) ∂μ, Filter.Tendsto (fun n => f n x) u (nhds 
(g x))) → MeasureTheory.Integrable g μ
参数：∀ᵐ (x : α) ∂μ, Filter.Tendsto (fun n => f n x) u (nhds (g x))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.UniformIntegrable.memLp_of_ae_tendsto`：∀ {α : Type u_1} {β
 : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Norme
dAddCommGroup β]   {p : ENNReal} {κ : Typ…

--- 原说明 ---
Suppose `f` is a sequence of functions that converges a.e. to `g`. If `f` is
`UniformIntegrable`, then `g` is integrable.
-/
lemma UniformIntegrable.integrable_of_ae_tendsto {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β} (hUI : UniformIntegrable f 1 μ)
    (htends : ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ f n x) u (𝓝 (g x))) :
    Integrable g μ :=
  memLp_one_iff_integrable.mp (hUI.memLp_of_ae_tendsto htends)

end UniformIntegrable

end MeasureTheory

