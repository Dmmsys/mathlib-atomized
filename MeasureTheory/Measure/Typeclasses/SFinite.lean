/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Classes for s-finite measures

We introduce the following typeclasses for measures:

* `SFinite μ`: the measure `μ` can be written as a countable sum of finite measures;
* `SigmaFinite μ`: there exists a countable collection of sets that cover `univ`
  where `μ` is finite.
-/

@[expose] public section

namespace MeasureTheory

open Set Filter Function Measure MeasurableSpace NNReal ENNReal
open scoped Topology

variable {α β ι : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] {μ ν : Measure α}
  {s t : Set α} {a : α}

section SFinite

/-- A measure is called s-finite if it is a countable sum of finite measures. -/
/-
**MeasureTheory.SFinite** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：{α : Type u_1} → {m0 : MeasurableSpace α} → MeasureTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure is called s-finite if it is a countable sum of finite measures.
-/
class SFinite (μ : Measure α) : Prop where
  out' : ∃ m : ℕ → Measure α, (∀ n, IsFiniteMeasure (m n)) ∧ μ = Measure.sum m

/-- A sequence of finite measures such that `μ = sum (sfiniteSeq μ)` (see `sum_sfiniteSeq`). -/
/-
**MeasureTheory.sfiniteSeq** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：sfiniteSeq (μ : Measure α) [h : SFinite μ] : Nat -> Measure α
参数：μ : Measure α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SFinite.out'`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ
 : MeasureTheory.Measure α} [self : MeasureTheory.SFinite μ],   ∃ m, (∀ (n : ℕ),
 MeasureTheory.I…

--- 原说明 ---
A sequence of finite measures such that `μ = sum (sfiniteSeq μ)` (see `sum_sfini
teSeq`).
-/
noncomputable def sfiniteSeq (μ : Measure α) [h : SFinite μ] : ℕ → Measure α := h.1.choose
/-
**MeasureTheory.isFiniteMeasure_sfiniteSeq** 是 Mathlib 中的一个实例，位于命名空间 `MeasureThe
ory`。
形式化陈述：isFiniteMeasure_sfiniteSeq [h : SFinite μ] (n : Nat) : IsFiniteMeasure (sf
initeSeq μ n)
参数：n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.SFinite.out'`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ
 : MeasureTheory.Measure α} [self : MeasureTheory.SFinite μ],   ∃ m, (∀ (n : ℕ),
 MeasureTheory.I…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
instance isFiniteMeasure_sfiniteSeq [h : SFinite μ] (n : ℕ) : IsFiniteMeasure (sfiniteSeq μ n) :=
  h.1.choose_spec.1 n
/-
**MeasureTheory.sum_sfiniteSeq** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：sum_sfiniteSeq (μ : Measure α) [h : SFinite μ] : sum (sfiniteSeq μ) = μ
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SFinite.out'`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ
 : MeasureTheory.Measure α} [self : MeasureTheory.SFinite μ],   ∃ m, (∀ (n : ℕ),
 MeasureTheory.I…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma sum_sfiniteSeq (μ : Measure α) [h : SFinite μ] : sum (sfiniteSeq μ) = μ :=
  h.1.choose_spec.2.symm
/-
**MeasureTheory.sfiniteSeq_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：sfiniteSeq_le (μ : Measure α) [SFinite μ] (n : Nat) : sfiniteSeq μ n <= μ
参数：μ : Measure α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.Measure.le_sum`：le_sum (μ : ι -> Measure α) (i : ι) : μ i 
<= sum μ
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ
-/
lemma sfiniteSeq_le (μ : Measure α) [SFinite μ] (n : ℕ) : sfiniteSeq μ n ≤ μ :=
  (le_sum _ n).trans (sum_sfiniteSeq μ).le
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SFinite (0 : Measure α) := ⟨fun _ ↦ 0, inferInstance, by rw [Measure.sum_zero]⟩

@[simp]
/-
**MeasureTheory.sfiniteSeq_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：sfiniteSeq_zero (n : Nat) : sfiniteSeq (0 : Measure α) n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `MeasureTheory.instSFiniteOfNatMeasure`：∀ {α : Type u_1} {m0 : Measurable
Space α}, MeasureTheory.SFinite 0
· 使用引理 `MeasureTheory.sfiniteSeq_le`：sfiniteSeq_le (μ : Measure α) [SFinite μ] (
n : Nat) : sfiniteSeq μ n <= μ
-/
lemma sfiniteSeq_zero (n : ℕ) : sfiniteSeq (0 : Measure α) n = 0 :=
  bot_unique <| sfiniteSeq_le _ _

/-- A countable sum of finite measures is s-finite.
This lemma is superseded by the instance below. -/
/-
**MeasureTheory.sfinite_sum_of_countable** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：sfinite_sum_of_countable [Countable ι] (m : ι -> Measure α) [forall n, IsF
initeMeasure (m n)] : SFinite (Measure.sum m)
参数：m : ι -> Measure α；m n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Countable.exists_injective_nat`：Countable.exists_injective_nat (α : Sort
 u) [Countable α] : exists f : α -> Nat, Injective f
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.sum_extend_zero`：∀ {α : Type u_1} {m0 : Measurable
Space α} {ι : Type u_8} {ι' : Type u_9} {f : ι → ι'},   Function.Injective f →  
   ∀ (m : ι → MeasureTheory…

--- 原说明 ---
A countable sum of finite measures is s-finite.
This lemma is superseded by the instance below.
-/
lemma sfinite_sum_of_countable [Countable ι]
    (m : ι → Measure α) [∀ n, IsFiniteMeasure (m n)] : SFinite (Measure.sum m) := by
  obtain ⟨f, hf⟩ : ∃ f : ι → ℕ, Function.Injective f := Countable.exists_injective_nat ι
  refine ⟨_, fun n ↦ ?_, (sum_extend_zero hf m).symm⟩
  rcases em (n ∈ range f) with ⟨i, rfl⟩ | hn
  · rw [hf.extend_apply]
    infer_instance
  · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply]
    infer_instance
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Countable ι] (m : ι → Measure α) [∀ n, SFinite (m n)] : SFinite (Measure.sum m) := by
  change SFinite (Measure.sum (fun i ↦ m i))
  simp_rw [← sum_sfiniteSeq (m _), Measure.sum_sum]
  apply sfinite_sum_of_countable
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SFinite μ] [SFinite ν] : SFinite (μ + ν) := by
  have : ∀ b : Bool, SFinite (cond b μ ν) := by simp [*]
  simpa using (inferInstance : SFinite (.sum (cond · μ ν)))
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SFinite μ] (s : Set α) : SFinite (μ.restrict s) :=
  ⟨fun n ↦ (sfiniteSeq μ n).restrict s, fun n ↦ inferInstance,
    by rw [← restrict_sum_of_countable, sum_sfiniteSeq]⟩

variable (μ) in
/-- For an s-finite measure `μ`, there exists a finite measure `ν`
such that each of `μ` and `ν` is absolutely continuous with respect to the other.
-/
/-
**MeasureTheory.exists_isFiniteMeasure_absolutelyContinuous** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：exists_isFiniteMeasure_absolutelyContinuous [SFinite μ] : exists ν : Measu
re α, IsFiniteMeasure ν ∧ μ ≪ ν ∧ ν ≪ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.exists_pos_tsum_mul_lt_of_countable`：exists_pos_tsum_mul_lt_of_c
ountable {ε : Real>=0∞} (hε : ε != 0) {ι} [Countable ι] (w : ι -> Real>=0∞) (hw 
: forall i, w i != ∞) : exists δ …
· 使用定理 `ENNReal.top_ne_zero`：⊤ ≠ 0
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ
· 使用定理 `MeasureTheory.Measure.sum_apply_of_countable`：sum_apply_of_countable [Co
untable ι] (f : ι -> Measure α) (s : Set α) : sum f s = ∑' i, f i s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
For an s-finite measure `μ`, there exists a finite measure `ν`
such that each of `μ` and `ν` is absolutely continuous with respect to the other
.
-/
theorem exists_isFiniteMeasure_absolutelyContinuous [SFinite μ] :
    ∃ ν : Measure α, IsFiniteMeasure ν ∧ μ ≪ ν ∧ ν ≪ μ := by
  rcases ENNReal.exists_pos_tsum_mul_lt_of_countable top_ne_zero (sfiniteSeq μ · univ)
    fun _ ↦ measure_ne_top _ _ with ⟨c, hc₀, hc⟩
  have {s : Set α} : sum (fun n ↦ c n • sfiniteSeq μ n) s = 0 ↔ μ s = 0 := by
    conv_rhs => rw [← sum_sfiniteSeq μ, sum_apply_of_countable]
    simp [(hc₀ _).ne']
  refine ⟨.sum fun n ↦ c n • sfiniteSeq μ n, ⟨?_⟩, fun _ ↦ this.1, fun _ ↦ this.2⟩
  simpa [mul_comm] using hc

end SFinite

/-- A measure `μ` is called σ-finite if there is a countable collection of sets
`{ A i | i ∈ ℕ }` such that `μ (A i) < ∞` and `⋃ i, A i = s`. -/
/-
**MeasureTheory.SigmaFinite** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：{α : Type u_1} → {m0 : MeasurableSpace α} → MeasureTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` is called σ-finite if there is a countable collection of sets
`{ A i | i ∈ ℕ }` such that `μ (A i) < ∞` and `⋃ i, A i = s`.
-/
class SigmaFinite {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  out' : Nonempty (μ.FiniteSpanningSetsIn univ)
/-
**MeasureTheory.sigmaFinite_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：sigmaFinite_iff : SigmaFinite μ ↔ Nonempty (μ.FiniteSpanningSetsIn univ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SigmaFinite.out'`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [self : MeasureTheory.SigmaFinite μ],   Nonempty
 (μ.FiniteSpanningSe…
-/
theorem sigmaFinite_iff : SigmaFinite μ ↔ Nonempty (μ.FiniteSpanningSetsIn univ) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
/-
**MeasureTheory.SigmaFinite.out** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.SigmaFi
nite`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α},  
 MeasureTheory.SigmaFinite μ → Nonempty (μ.FiniteSpanningSetsIn Set.univ)
参数：μ.FiniteSpanningSetsIn Set.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SigmaFinite.out'`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [self : MeasureTheory.SigmaFinite μ],   Nonempty
 (μ.FiniteSpanningSe…
-/
theorem SigmaFinite.out (h : SigmaFinite μ) : Nonempty (μ.FiniteSpanningSetsIn univ) :=
  h.1

/-- If `μ` is σ-finite it has finite spanning sets in the collection of all measurable sets. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**MeasureTheory.Measure.toFiniteSpanningSetsIn** 是 Mathlib 中的一个定义，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：{α : Type u_1} →   {m0 : MeasurableSpace α} →     (μ : MeasureTheory.Measu
re α) → [h : MeasureTheory.SigmaFinite μ] → μ.FiniteSpanningSetsIn {s | Measurab
leSet s}
参数：μ : MeasureTheory.Measure α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SigmaFinite.out`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 {μ : MeasureTheory.Measure α},   MeasureTheory.SigmaFinite μ → Nonempty (μ.Fini
teSpanningSetsIn Se…
-/
noncomputable def Measure.toFiniteSpanningSetsIn (μ : Measure α) [h : SigmaFinite μ] :
    μ.FiniteSpanningSetsIn { s | MeasurableSet s } where
  set n := toMeasurable μ (h.out.some.set n)
  set_mem _ := measurableSet_toMeasurable _ _
  finite n := by
    rw [measure_toMeasurable]
    exact h.out.some.finite n
  spanning := eq_univ_of_subset (iUnion_mono fun _ => subset_toMeasurable _ _) h.out.some.spanning

/-- A noncomputable way to get a monotone collection of sets that span `univ` and have finite
  measure using `Classical.choose`. This definition satisfies monotonicity in addition to all other
  properties in `SigmaFinite`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**MeasureTheory.spanningSets** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：spanningSets (μ : Measure α) [SigmaFinite μ] (i : Nat) : Set α
参数：μ : Measure α；i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def spanningSets (μ : Measure α) [SigmaFinite μ] (i : ℕ) : Set α :=
  accumulate μ.toFiniteSpanningSetsIn.set i
/-
**MeasureTheory.monotone_spanningSets** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：monotone_spanningSets (μ : Measure α) [SigmaFinite μ] : Monotone (spanning
Sets μ)
参数：μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.monotone_accumulate`：monotone_accumulate [Preorder α] : Monotone (ac
cumulate s)
-/
theorem monotone_spanningSets (μ : Measure α) [SigmaFinite μ] : Monotone (spanningSets μ) :=
  monotone_accumulate

@[gcongr]
/-
**MeasureTheory.spanningSets_mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：spanningSets_mono [SigmaFinite μ] {m n : Nat} (hmn : m <= n) : spanningSet
s μ m subseteq spanningSets μ n
参数：hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.monotone_spanningSets`：monotone_spanningSets (μ : Measure 
α) [SigmaFinite μ] : Monotone (spanningSets μ)
-/
lemma spanningSets_mono [SigmaFinite μ] {m n : ℕ} (hmn : m ≤ n) :
    spanningSets μ m ⊆ spanningSets μ n := monotone_spanningSets _ hmn
/-
**MeasureTheory.measurableSet_spanningSets** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measurableSet_spanningSets (μ : Measure α) [SigmaFinite μ] (i : Nat) : Mea
surableSet (spanningSets μ i)
参数：μ : Measure α；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.set_mem`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self : 
μ.FiniteSpanningSetsIn C) (i : ℕ), self.…
-/
theorem measurableSet_spanningSets (μ : Measure α) [SigmaFinite μ] (i : ℕ) :
    MeasurableSet (spanningSets μ i) :=
  MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => μ.toFiniteSpanningSetsIn.set_mem j
/-
**MeasureTheory.measure_spanningSets_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measure_spanningSets_lt_top (μ : Measure α) [SigmaFinite μ] (i : Nat) : μ 
(spanningSets μ i) < ∞
参数：μ : Measure α；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_biUnion_lt_top`：measure_biUnion_lt_top {s : Set β}
 {f : β -> Set α} (hs : s.Finite) (hfin : forall i in s, μ (f i) < ∞) : μ (⋃ i i
n s, f i) < ∞
· 使用定理 `Set.finite_le_nat`：finite_le_nat (n : Nat) : Set.Finite { i | i <= n }
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.finite`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self : μ
.FiniteSpanningSetsIn C) (i : ℕ), μ (se…
-/
theorem measure_spanningSets_lt_top (μ : Measure α) [SigmaFinite μ] (i : ℕ) :
    μ (spanningSets μ i) < ∞ :=
  measure_biUnion_lt_top (finite_le_nat i) fun j _ => μ.toFiniteSpanningSetsIn.finite j

@[simp]
/-
**MeasureTheory.iUnion_spanningSets** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：iUnion_spanningSets (μ : Measure α) [SigmaFinite μ] : ⋃ i : Nat, spanningS
ets μ i = univ
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_accumulate`：iUnion_accumulate [Preorder α] : ⋃ x, accumulate 
s x = ⋃ x, s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.spanning`：∀ {α : Type u_1} {m
0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self :
 μ.FiniteSpanningSetsIn C), ⋃ i, self.set…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_spanningSets (μ : Measure α) [SigmaFinite μ] : ⋃ i : ℕ, spanningSets μ i = univ := by
  simp_rw [spanningSets, iUnion_accumulate, μ.toFiniteSpanningSetsIn.spanning]
/-
**MeasureTheory.isCountablySpanning_spanningSets** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：isCountablySpanning_spanningSets (μ : Measure α) [SigmaFinite μ] : IsCount
ablySpanning (range (spanningSets μ))
参数：μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
-/
theorem isCountablySpanning_spanningSets (μ : Measure α) [SigmaFinite μ] :
    IsCountablySpanning (range (spanningSets μ)) :=
  ⟨spanningSets μ, mem_range_self, iUnion_spanningSets μ⟩

open scoped Classical in
/-- `spanningSetsIndex μ x` is the least `n : ℕ` such that `x ∈ spanningSets μ n`. -/
/-
**MeasureTheory.spanningSetsIndex** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) : Nat
参数：μ : Measure α；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`spanningSetsIndex μ x` is the least `n : ℕ` such that `x ∈ spanningSets μ n`.
-/
noncomputable def spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) : ℕ :=
  Nat.find <| iUnion_eq_univ_iff.1 (iUnion_spanningSets μ) x
/-
**MeasureTheory.measurableSet_spanningSetsIndex** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：measurableSet_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] : Measurab
le (spanningSetsIndex μ)
参数：μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_find`：measurable_find {p : α -> Nat -> Prop} [forall x, Decid
ablePred (p x)] (hp : forall x, exists N, p x N) (hm : forall k, MeasurableSet {
 x | …
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
-/
theorem measurableSet_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] :
    Measurable (spanningSetsIndex μ) := by
  classical
  exact measurable_find _ <| measurableSet_spanningSets μ
/-
**MeasureTheory.preimage_spanningSetsIndex_singleton** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：preimage_spanningSetsIndex_singleton (μ : Measure α) [SigmaFinite μ] (n : 
Nat) : spanningSetsIndex μ ⁻¹' {n} = disjointed (spanningSets μ) n
参数：μ : Measure α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `preimage_find_eq_disjointed`：preimage_find_eq_disjointed (s : Nat -> Set
 α) (H : forall x, exists n, x in s n) [forall x n, Decidable (x in s n)] (n : N
at) : (fun x => N…
-/
theorem preimage_spanningSetsIndex_singleton (μ : Measure α) [SigmaFinite μ] (n : ℕ) :
    spanningSetsIndex μ ⁻¹' {n} = disjointed (spanningSets μ) n := by
  classical
  exact preimage_find_eq_disjointed _ _ _
/-
**MeasureTheory.spanningSetsIndex_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：spanningSetsIndex_eq_iff (μ : Measure α) [SigmaFinite μ] {x : α} {n : Nat}
 : spanningSetsIndex μ x = n ↔ x in disjointed (spanningSets μ) n
参数：μ : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `MeasureTheory.preimage_spanningSetsIndex_singleton`：preimage_spanningSet
sIndex_singleton (μ : Measure α) [SigmaFinite μ] (n : Nat) : spanningSetsIndex μ
 ⁻¹' {n} = disjointed (spanningSets μ) n
-/
theorem spanningSetsIndex_eq_iff (μ : Measure α) [SigmaFinite μ] {x : α} {n : ℕ} :
    spanningSetsIndex μ x = n ↔ x ∈ disjointed (spanningSets μ) n := by
  convert! Set.ext_iff.1 (preimage_spanningSetsIndex_singleton μ n) x
/-
**MeasureTheory.mem_disjointed_spanningSetsIndex** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：mem_disjointed_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) :
 x in disjointed (spanningSets μ) (spanningSetsIndex μ x)
参数：μ : Measure α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.spanningSetsIndex_eq_iff`：spanningSetsIndex_eq_iff (μ : Me
asure α) [SigmaFinite μ] {x : α} {n : Nat} : spanningSetsIndex μ x = n ↔ x in di
sjointed (spanningSets μ) n
-/
theorem mem_disjointed_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) :
    x ∈ disjointed (spanningSets μ) (spanningSetsIndex μ x) :=
  (spanningSetsIndex_eq_iff μ).1 rfl
/-
**MeasureTheory.mem_spanningSetsIndex** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：mem_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) : x in spann
ingSets μ (spanningSetsIndex μ x)
参数：μ : Measure α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjointed_subset`：disjointed_subset [Preorder ι] [LocallyFiniteOrderBot
 ι] (f : ι -> Set α) (i : ι) : disjointed f i subseteq f i
· 使用定理 `MeasureTheory.mem_disjointed_spanningSetsIndex`：mem_disjointed_spanningS
etsIndex (μ : Measure α) [SigmaFinite μ] (x : α) : x in disjointed (spanningSets
 μ) (spanningSetsIndex μ x)
-/
theorem mem_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) :
    x ∈ spanningSets μ (spanningSetsIndex μ x) :=
  disjointed_subset _ _ (mem_disjointed_spanningSetsIndex μ x)
/-
**MeasureTheory.mem_spanningSets_of_index_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：mem_spanningSets_of_index_le (μ : Measure α) [SigmaFinite μ] (x : α) {n : 
Nat} (hn : spanningSetsIndex μ x <= n) : x in spanningSets μ n
参数：μ : Measure α；x : α；hn : spanningSetsIndex μ x <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.monotone_spanningSets`：monotone_spanningSets (μ : Measure 
α) [SigmaFinite μ] : Monotone (spanningSets μ)
· 使用定理 `MeasureTheory.mem_spanningSetsIndex`：mem_spanningSetsIndex (μ : Measure 
α) [SigmaFinite μ] (x : α) : x in spanningSets μ (spanningSetsIndex μ x)
-/
theorem mem_spanningSets_of_index_le (μ : Measure α) [SigmaFinite μ] (x : α) {n : ℕ}
    (hn : spanningSetsIndex μ x ≤ n) : x ∈ spanningSets μ n :=
  monotone_spanningSets μ hn (mem_spanningSetsIndex μ x)
/-
**MeasureTheory.eventually_mem_spanningSets** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：eventually_mem_spanningSets (μ : Measure α) [SigmaFinite μ] (x : α) : fora
llᶠ n in atTop, x in spanningSets μ n
参数：μ : Measure α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.mem_spanningSets_of_index_le`：mem_spanningSets_of_index_le
 (μ : Measure α) [SigmaFinite μ] (x : α) {n : Nat} (hn : spanningSetsIndex μ x <
= n) : x in spanningSets μ n
-/
theorem eventually_mem_spanningSets (μ : Measure α) [SigmaFinite μ] (x : α) :
    ∀ᶠ n in atTop, x ∈ spanningSets μ n :=
  eventually_atTop.2 ⟨spanningSetsIndex μ x, fun _ => mem_spanningSets_of_index_le μ x⟩
/-
**MeasureTheory.measure_singleton_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measure_singleton_lt_top [SigmaFinite μ] : μ {a} < ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.measure_lt_top_mono`：measure_lt_top_mono (h : s subseteq t
) (ht : μ t < ∞) : μ s < ∞
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `MeasureTheory.mem_spanningSetsIndex`：mem_spanningSetsIndex (μ : Measure 
α) [SigmaFinite μ] (x : α) : x in spanningSets μ (spanningSetsIndex μ x)
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
-/
lemma measure_singleton_lt_top [SigmaFinite μ] : μ {a} < ∞ :=
  measure_lt_top_mono (singleton_subset_iff.2 <| mem_spanningSetsIndex ..)
    (measure_spanningSets_lt_top _ _)
/-
**MeasureTheory.sum_restrict_disjointed_spanningSets** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：sum_restrict_disjointed_spanningSets (μ ν : Measure α) [SigmaFinite ν] : s
um (fun n => μ.restrict (disjointed (spanningSets ν) n)) = μ
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_iUnion`：restrict_iUnion [Countable ι] {s 
: ι -> Set α} (hd : Pairwise (Disjoint on s)) (hm : forall i, MeasurableSet (s i
)) : μ.restrict (⋃ i, s i) …
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
· 使用定理 `MeasurableSet.disjointed`：∀ {α : Type u_1} {mα : MeasurableSpace α} {f :
 ℕ → Set α},   (∀ (i : ℕ), MeasurableSet (f i)) → ∀ (n : ℕ), MeasurableSet (disj
ointed f n)
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `iUnion_disjointed`：iUnion_disjointed [PartialOrder ι] [LocallyFiniteOrde
rBot ι] {f : ι -> Set α} : ⋃ i, disjointed f i = ⋃ i, f i
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
-/
theorem sum_restrict_disjointed_spanningSets (μ ν : Measure α) [SigmaFinite ν] :
    sum (fun n ↦ μ.restrict (disjointed (spanningSets ν) n)) = μ := by
  rw [← restrict_iUnion (disjoint_disjointed _)
      (MeasurableSet.disjointed (measurableSet_spanningSets _)),
    iUnion_disjointed, iUnion_spanningSets, restrict_univ]
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [SigmaFinite μ] : SFinite μ := by
  have : ∀ n, Fact (μ (disjointed (spanningSets μ) n) < ∞) :=
    fun n ↦ ⟨(measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top μ n)⟩
  exact ⟨⟨fun n ↦ μ.restrict (disjointed (spanningSets μ) n), fun n ↦ by infer_instance,
    (sum_restrict_disjointed_spanningSets μ μ).symm⟩⟩

namespace Measure

/-- A set in a σ-finite space has zero measure if and only if its intersection with
all members of the countable family of finite measure spanning sets has zero measure. -/
@[deprecated forall_measure_inter_isCountablySpanning_eq_zero (since := "2026-03-13")]
/-
**MeasureTheory.Measure.forall_measure_inter_spanningSets_eq_zero** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：forall_measure_inter_spanningSets_eq_zero [MeasurableSpace α] {μ : Measure
 α} [SigmaFinite μ] (s : Set α) : (forall n, μ (s inter spanningSets μ n) = 0) ↔
 μ s = 0
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `MeasureTheory.measure_iUnion_null_iff`：measure_iUnion_null_iff {ι : Sort
*} [Countable ι] {s : ι -> Set α} : μ (⋃ i, s i) = 0 ↔ forall i, μ (s i) = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A set in a σ-finite space has zero measure if and only if its intersection with
all members of the countable family of finite measure spanning sets has zero mea
sure.
-/
theorem forall_measure_inter_spanningSets_eq_zero [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] (s : Set α) : (∀ n, μ (s ∩ spanningSets μ n) = 0) ↔ μ s = 0 := by
  nth_rw 2 [show s = ⋃ n, s ∩ spanningSets μ n by
      rw [← inter_iUnion, iUnion_spanningSets, inter_univ]]
  rw [measure_iUnion_null_iff]

/-- A set in a σ-finite space has positive measure if and only if its intersection with
some member of the countable family of finite measure spanning sets has positive measure. -/
/-
**MeasureTheory.Measure.exists_measure_inter_spanningSets_pos** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：exists_measure_inter_spanningSets_pos [MeasurableSpace α] {μ : Measure α} 
[SigmaFinite μ] (s : Set α) : (exists n, 0 < μ (s inter spanningSets μ n)) ↔ 0 <
 μ s
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.forall_measure_inter_isCountablySpanning_eq_zero`：
forall_measure_inter_isCountablySpanning_eq_zero {C : Set (Set α)} (hC : IsCount
ablySpanning C) : (forall t in C, μ (s inter t) = 0) ↔ μ s =…
· 使用定理 `MeasureTheory.isCountablySpanning_spanningSets`：isCountablySpanning_span
ningSets (μ : Measure α) [SigmaFinite μ] : IsCountablySpanning (range (spanningS
ets μ))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A set in a σ-finite space has positive measure if and only if its intersection w
ith
some member of the countable family of finite measure spanning sets has positive
 measure.
-/
theorem exists_measure_inter_spanningSets_pos [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    (s : Set α) : (∃ n, 0 < μ (s ∩ spanningSets μ n)) ↔ 0 < μ s := by
  contrapose!
  rw [nonpos_iff_eq_zero, ← forall_measure_inter_isCountablySpanning_eq_zero
    (isCountablySpanning_spanningSets μ)]
  simp

/-- If the union of a.e.-disjoint null-measurable sets has finite measure, then there are only
finitely many members of the union whose measure exceeds any given positive number. -/
/-
**MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：finite_const_le_meas_of_disjoint_iUnion {ι : Type*} [MeasurableSpace α] (μ
 : Measure α) {ε : Real>=0∞} (ε_pos : 0 < ε) {As : ι -> Set α} (As_mble : forall
 i : ι, MeasurableSet (As i)) (As_disj : Pairwise (Disjoint on As)) (Union_As_fi
nite : μ (⋃ i, As i) != ∞) : Set.Finite { i : ι | ε <= μ (As i) }
参数：μ : Measure α；ε_pos : 0 < ε；As_mble : forall i : ι, MeasurableSet (As i)；As_d
isj : Pairwise (Disjoint on As)；Union_As_finite : μ (⋃ i, As i) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion₀`：finite_c
onst_le_meas_of_disjoint_iUnion₀ {ι : Type*} [MeasurableSpace α] (μ : Measure α)
 {ε : Real>=0∞} (ε_pos : 0 < ε) {As : ι -> Set α} (A…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t

--- 原说明 ---
If the union of a.e.-disjoint null-measurable sets has finite measure, then ther
e are only
finitely many members of the union whose measure exceeds any given positive numb
er.
-/
theorem finite_const_le_meas_of_disjoint_iUnion₀ {ι : Type*} [MeasurableSpace α] (μ : Measure α)
    {ε : ℝ≥0∞} (ε_pos : 0 < ε) {As : ι → Set α} (As_mble : ∀ i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) (Union_As_finite : μ (⋃ i, As i) ≠ ∞) :
    Set.Finite { i : ι | ε ≤ μ (As i) } :=
  ENNReal.finite_const_le_of_tsum_ne_top
    (ne_top_of_le_ne_top Union_As_finite (tsum_meas_le_meas_iUnion_of_disjoint₀ μ As_mble As_disj))
    ε_pos.ne'

/-- If the union of disjoint measurable sets has finite measure, then there are only
finitely many members of the union whose measure exceeds any given positive number. -/
/-
**MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：finite_const_le_meas_of_disjoint_iUnion {ι : Type*} [MeasurableSpace α] (μ
 : Measure α) {ε : Real>=0∞} (ε_pos : 0 < ε) {As : ι -> Set α} (As_mble : forall
 i : ι, MeasurableSet (As i)) (As_disj : Pairwise (Disjoint on As)) (Union_As_fi
nite : μ (⋃ i, As i) != ∞) : Set.Finite { i : ι | ε <= μ (As i) }
参数：μ : Measure α；ε_pos : 0 < ε；As_mble : forall i : ι, MeasurableSet (As i)；As_d
isj : Pairwise (Disjoint on As)；Union_As_finite : μ (⋃ i, As i) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion₀`：finite_c
onst_le_meas_of_disjoint_iUnion₀ {ι : Type*} [MeasurableSpace α] (μ : Measure α)
 {ε : Real>=0∞} (ε_pos : 0 < ε) {As : ι -> Set α} (A…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t

--- 原说明 ---
If the union of disjoint measurable sets has finite measure, then there are only
finitely many members of the union whose measure exceeds any given positive numb
er.
-/
theorem finite_const_le_meas_of_disjoint_iUnion {ι : Type*} [MeasurableSpace α] (μ : Measure α)
    {ε : ℝ≥0∞} (ε_pos : 0 < ε) {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) (Union_As_finite : μ (⋃ i, As i) ≠ ∞) :
    Set.Finite { i : ι | ε ≤ μ (As i) } :=
  finite_const_le_meas_of_disjoint_iUnion₀ μ ε_pos (fun i ↦ (As_mble i).nullMeasurableSet)
    (fun _ _ h ↦ Disjoint.aedisjoint (As_disj h)) Union_As_finite

/-- If all elements of an infinite set have measure uniformly separated from zero,
then the set has infinite measure. -/
/-
**MeasureTheory.Measure._root_.Set.Infinite.meas_eq_top** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If all elements of an infinite set have measure uniformly separated from zero,
then the set has infinite measure.
-/
theorem _root_.Set.Infinite.meas_eq_top [MeasurableSingletonClass α]
    {s : Set α} (hs : s.Infinite) (h' : ∃ ε, ε ≠ 0 ∧ ∀ x ∈ s, ε ≤ μ {x}) : μ s = ∞ := top_unique <|
  let ⟨ε, hne, hε⟩ := h'; have := hs.to_subtype
  calc
    ∞ = ∑' _ : s, ε := (ENNReal.tsum_const_eq_top_of_ne_zero hne).symm
    _ ≤ ∑' x : s, μ {x.1} := ENNReal.tsum_le_tsum fun x ↦ hε x x.2
    _ ≤ μ (⋃ x : s, {x.1}) := tsum_meas_le_meas_iUnion_of_disjoint _
      (fun _ ↦ MeasurableSet.singleton _) fun x y hne ↦ by simpa [Subtype.val_inj]
    _ = μ s := by simp

/-- If the union of a.e.-disjoint null-measurable sets has finite measure, then there are only
countably many members of the union whose measure is positive. -/
/-
**MeasureTheory.Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top {ι : Type*} {_ : Meas
urableSpace α} (μ : Measure α) {As : ι -> Set α} (As_mble : forall i : ι, Measur
ableSet (As i)) (As_disj : Pairwise (Disjoint on As)) (Union_As_finite : μ (⋃ i,
 As i) != ∞) : Set.Countable { i : ι | 0 < μ (As i) }
参数：μ : Measure α；As_mble : forall i : ι, MeasurableSet (As i)；As_disj : Pairwise
 (Disjoint on As)；Union_As_finite : μ (⋃ i, As i) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_t
op₀`：countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ {ι : Type*} {_ : Meas
urableSpace α} (μ : Measure α) {As : ι -> Set α} (As_mble : foral…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t

--- 原说明 ---
If the union of a.e.-disjoint null-measurable sets has finite measure, then ther
e are only
countably many members of the union whose measure is positive.
-/
theorem countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ {ι : Type*} {_ : MeasurableSpace α}
    (μ : Measure α) {As : ι → Set α} (As_mble : ∀ i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) (Union_As_finite : μ (⋃ i, As i) ≠ ∞) :
    Set.Countable { i : ι | 0 < μ (As i) } := by
  set posmeas := { i : ι | 0 < μ (As i) } with posmeas_def
  rcases exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ≥0∞) < 1) with
    ⟨as, _, as_mem, as_lim⟩
  set fairmeas := fun n : ℕ => { i : ι | as n ≤ μ (As i) }
  have countable_union : posmeas = ⋃ n, fairmeas n := by
    have fairmeas_eq : ∀ n, fairmeas n = (fun i => μ (As i)) ⁻¹' Ici (as n) := fun n => by
      simp only [fairmeas]
      rfl
    simpa only [fairmeas_eq, posmeas_def, ← preimage_iUnion,
      iUnion_Ici_eq_Ioi_of_lt_of_tendsto (fun n => (as_mem n).1) as_lim]
  rw [countable_union]
  refine countable_iUnion fun n => Finite.countable ?_
  exact finite_const_le_meas_of_disjoint_iUnion₀ μ (as_mem n).1 As_mble As_disj Union_As_finite

/-- If the union of disjoint measurable sets has finite measure, then there are only
countably many members of the union whose measure is positive. -/
/-
**MeasureTheory.Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top {ι : Type*} {_ : Meas
urableSpace α} (μ : Measure α) {As : ι -> Set α} (As_mble : forall i : ι, Measur
ableSet (As i)) (As_disj : Pairwise (Disjoint on As)) (Union_As_finite : μ (⋃ i,
 As i) != ∞) : Set.Countable { i : ι | 0 < μ (As i) }
参数：μ : Measure α；As_mble : forall i : ι, MeasurableSet (As i)；As_disj : Pairwise
 (Disjoint on As)；Union_As_finite : μ (⋃ i, As i) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_t
op₀`：countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ {ι : Type*} {_ : Meas
urableSpace α} (μ : Measure α) {As : ι -> Set α} (As_mble : foral…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t

--- 原说明 ---
If the union of disjoint measurable sets has finite measure, then there are only
countably many members of the union whose measure is positive.
-/
theorem countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top {ι : Type*} {_ : MeasurableSpace α}
    (μ : Measure α) {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) (Union_As_finite : μ (⋃ i, As i) ≠ ∞) :
    Set.Countable { i : ι | 0 < μ (As i) } :=
  countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ μ (fun i ↦ (As_mble i).nullMeasurableSet)
    ((fun _ _ h ↦ Disjoint.aedisjoint (As_disj h))) Union_As_finite

/-- In an s-finite space, among disjoint null-measurable sets, only countably many can have positive
measure. -/
/-
**MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：countable_meas_pos_of_disjoint_iUnion {ι : Type*} {_ : MeasurableSpace α} 
{μ : Measure α} [SFinite μ] {As : ι -> Set α} (As_mble : forall i : ι, Measurabl
eSet (As i)) (As_disj : Pairwise (Disjoint on As)) : Set.Countable { i : ι | 0 <
 μ (As i) }
参数：As_mble : forall i : ι, MeasurableSet (As i)；As_disj : Pairwise (Disjoint on 
As)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion₀`：countable_
meas_pos_of_disjoint_iUnion₀ {ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
 [SFinite μ] {As : ι -> Set α} (As_mble : forall i…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t

--- 原说明 ---
In an s-finite space, among disjoint null-measurable sets, only countably many c
an have positive
measure.
-/
theorem countable_meas_pos_of_disjoint_iUnion₀ {ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] {As : ι → Set α} (As_mble : ∀ i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) :
    Set.Countable { i : ι | 0 < μ (As i) } := by
  rw [← sum_sfiniteSeq μ] at As_disj As_mble ⊢
  have obs : { i : ι | 0 < sum (sfiniteSeq μ) (As i) }
      ⊆ ⋃ n, { i : ι | 0 < sfiniteSeq μ n (As i) } := by
    intro i hi
    by_contra con
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt, nonpos_iff_eq_zero] at *
    rw [sum_apply₀] at hi
    · simp_rw [con] at hi
      simp at hi
    · exact As_mble i
  apply Countable.mono obs
  refine countable_iUnion fun n ↦ ?_
  apply countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀
  · exact fun i ↦ (As_mble i).mono (le_sum _ _)
  · exact fun i j hij ↦ AEDisjoint.of_le (As_disj hij) (le_sum _ _)
  · exact measure_ne_top _ (⋃ i, As i)

/-- In an s-finite space, among disjoint measurable sets, only countably many can have positive
measure. -/
/-
**MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：countable_meas_pos_of_disjoint_iUnion {ι : Type*} {_ : MeasurableSpace α} 
{μ : Measure α} [SFinite μ] {As : ι -> Set α} (As_mble : forall i : ι, Measurabl
eSet (As i)) (As_disj : Pairwise (Disjoint on As)) : Set.Countable { i : ι | 0 <
 μ (As i) }
参数：As_mble : forall i : ι, MeasurableSet (As i)；As_disj : Pairwise (Disjoint on 
As)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion₀`：countable_
meas_pos_of_disjoint_iUnion₀ {ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
 [SFinite μ] {As : ι -> Set α} (As_mble : forall i…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t

--- 原说明 ---
In an s-finite space, among disjoint measurable sets, only countably many can ha
ve positive
measure.
-/
theorem countable_meas_pos_of_disjoint_iUnion {ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) : Set.Countable { i : ι | 0 < μ (As i) } :=
  countable_meas_pos_of_disjoint_iUnion₀ (fun i ↦ (As_mble i).nullMeasurableSet)
    ((fun _ _ h ↦ Disjoint.aedisjoint (As_disj h)))
/-
**MeasureTheory.Measure.countable_meas_level_set_pos** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：countable_meas_level_set_pos {α β : Type*} {_ : MeasurableSpace α} {μ : Me
asure α} [SFinite μ] [MeasurableSpace β] [MeasurableSingletonClass β] {g : α -> 
β} (g_mble : Measurable g) : Set.Countable { t : β | 0 < μ { a : α | g a = t } }
参数：g_mble : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.countable_meas_level_set_pos₀`：countable_meas_leve
l_set_pos₀ {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α} [SFinite μ] [Me
asurableSpace β] [MeasurableSingletonClas…
· 使用定理 `Measurable.nullMeasurable`：∀ {α : Type u_2} {β : Type u_3} [m : Measurab
leSpace α] [inst : MeasurableSpace β] {f : α → β}   {μ : MeasureTheory.Measure α
}, Measurable f…
-/
theorem countable_meas_level_set_pos₀ {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] [MeasurableSpace β] [MeasurableSingletonClass β] {g : α → β}
    (g_mble : NullMeasurable g μ) : Set.Countable { t : β | 0 < μ { a : α | g a = t } } := by
  have level_sets_disjoint : Pairwise (Disjoint on fun t : β => { a : α | g a = t }) :=
    fun s t hst => Disjoint.preimage g (disjoint_singleton.mpr hst)
  exact Measure.countable_meas_pos_of_disjoint_iUnion₀
    (fun b => g_mble (‹MeasurableSingletonClass β›.measurableSet_singleton b))
    ((fun _ _ h ↦ Disjoint.aedisjoint (level_sets_disjoint h)))
/-
**MeasureTheory.Measure.countable_meas_level_set_pos** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：countable_meas_level_set_pos {α β : Type*} {_ : MeasurableSpace α} {μ : Me
asure α} [SFinite μ] [MeasurableSpace β] [MeasurableSingletonClass β] {g : α -> 
β} (g_mble : Measurable g) : Set.Countable { t : β | 0 < μ { a : α | g a = t } }
参数：g_mble : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.countable_meas_level_set_pos₀`：countable_meas_leve
l_set_pos₀ {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α} [SFinite μ] [Me
asurableSpace β] [MeasurableSingletonClas…
· 使用定理 `Measurable.nullMeasurable`：∀ {α : Type u_2} {β : Type u_3} [m : Measurab
leSpace α] [inst : MeasurableSpace β] {f : α → β}   {μ : MeasureTheory.Measure α
}, Measurable f…
-/
theorem countable_meas_level_set_pos {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] [MeasurableSpace β] [MeasurableSingletonClass β] {g : α → β}
    (g_mble : Measurable g) : Set.Countable { t : β | 0 < μ { a : α | g a = t } } :=
  countable_meas_level_set_pos₀ g_mble.nullMeasurable
/-
**MeasureTheory.Measure.exists_ae_subset_biUnion_countable_of_isFiniteMeasure** 
是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_ae_subset_biUnion_countable_of_isFiniteMeasure [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : ∀ s ∈ C, MeasurableSet s) :
    ∃ D ⊆ C, D.Countable ∧ ∀ s ∈ C, s ≤ᵐ[μ] (⋃₀ D) := by
  let m := ⨆ D ∈ {D : Set (Set α) | D ⊆ C ∧ D.Countable}, μ (⋃₀ D)
  obtain ⟨D, D_mem, hD⟩ : ∃ D ∈ {D : Set (Set α) | D ⊆ C ∧ D.Countable}, μ (⋃₀ D) = m := by
    rcases eq_bot_or_bot_lt m with hm | hm
    · exact ⟨∅, by simp, by simp [hm]⟩
    obtain ⟨u, -, u_mem, u_lim⟩ :
        ∃ u : ℕ → ℝ≥0∞, StrictMono u ∧ (∀ n, u n ∈ Ioo 0 m) ∧ Tendsto u atTop (𝓝 m) :=
      exists_seq_strictMono_tendsto' hm
    have A n : ∃ D ∈ {D : Set (Set α) | D ⊆ C ∧ D.Countable}, u n < μ (⋃₀ D) :=
      lt_biSup_iff.1 (u_mem n).2
    choose! D D_mem huD using A
    have hD : ⋃ n, D n ∈ {D | D ⊆ C ∧ D.Countable} := by simp; grind
    refine ⟨⋃ n, D n, hD, ?_⟩
    apply le_antisymm (le_biSup (f := fun D ↦ μ (⋃₀ D)) hD)
    apply le_of_tendsto' u_lim (fun n ↦ (huD n).le.trans ?_)
    exact measure_mono (fun x hx ↦ by simp at hx ⊢; grind)
  refine ⟨D, by grind, by grind, fun s hs ↦ union_ae_eq_right_iff_ae_subset.mp ?_⟩
  symm
  apply ae_eq_of_ae_subset_of_measure_ge subset_union_right.eventuallyLE
  · rw [hD, show s ∪ ⋃₀ D = ⋃₀ (D ∪ {s}) by simp]
    apply le_biSup (f := fun D ↦ μ (⋃₀ D))
    simp [D_mem.2, insert_subset_iff, hs, D_mem.1]
  · exact (MeasurableSet.sUnion D_mem.2 (by grind)).nullMeasurableSet
  · simp

variable (μ) in
/-- Given a family of measurable sets, its measurable union is its union modulo sets of measure
zero. It is well defined up to measure 0. For instance, the measurable union of all the singleton
sets in `ℝ` is empty (while the usual union would be the whole space).
This lemma shows the existence of a measurable union, writing it as the union of a countable
subfamily. -/
/-
**MeasureTheory.Measure.exists_ae_subset_biUnion_countable** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.Measure`。
形式化陈述：exists_ae_subset_biUnion_countable [SFinite μ] {C : Set (Set α)} (hC : for
all s in C, MeasurableSet s) : exists D subseteq C, D.Countable ∧ forall s in C,
 s <=ᵐ[μ] (⋃₀ D)
参数：Set α；hC : forall s in C, MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `_private.Mathlib.MeasureTheory.Measure.Typeclasses.SFinite.0.MeasureTheo
ry.Measure.exists_ae_subset_biUnion_countable_of_isFiniteMeasure`：∀ {α : Type u_
1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.IsFinit
eMeasure μ]   {C : Set (Set α)}, (∀ s ∈ C, Mea…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.ae_sum_iff`：ae_sum_iff [Countable ι] {μ : ι -> Mea
sure α} {p : α -> Prop} : (forallᵐ x ∂sum μ, p x) ↔ forall i, forallᵐ x ∂μ i, p 
x
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `LE.le.eventuallyLE`：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} 
(h : s subseteq t) : s <=ᶠ[l] t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Given a family of measurable sets, its measurable union is its union modulo sets
 of measure
zero. It is well defined up to measure 0. For instance, the measurable union of 
all the singleton
sets in `ℝ` is empty (while the usual union would be the whole space).
This lemma shows the existence of a measurable union, writing it as the union of
 a countable
subfamily.
-/
lemma exists_ae_subset_biUnion_countable [SFinite μ]
    {C : Set (Set α)} (hC : ∀ s ∈ C, MeasurableSet s) :
    ∃ D ⊆ C, D.Countable ∧ ∀ s ∈ C, s ≤ᵐ[μ] (⋃₀ D) := by
  have A n : ∃ D ⊆ C, D.Countable ∧ ∀ s ∈ C, s ≤ᵐ[sfiniteSeq μ n] (⋃₀ D) :=
    exists_ae_subset_biUnion_countable_of_isFiniteMeasure hC
  choose D DC D_count hD using A
  refine ⟨⋃ n, D n, by simp [DC], by simp [D_count], fun s hs ↦ ?_⟩
  rw [← sum_sfiniteSeq μ]
  apply ae_sum_iff.2 (fun n ↦ (hD n s hs).trans ?_)
  exact LE.le.eventuallyLE (fun x hx ↦ by simp at hx ⊢; grind)

set_option backward.defeqAttrib.useBackward false in
/-- If a measure `μ` is the sum of a countable family `mₙ`, and a set `t` has finite measure for
each `mₙ`, then its measurable superset `toMeasurable μ t` (which has the same measure as `t`)
satisfies, for any measurable set `s`, the equality `μ (toMeasurable μ t ∩ s) = μ (t ∩ s)`. -/
/-
**MeasureTheory.Measure.measure_toMeasurable_inter_of_sum** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure`。
形式化陈述：measure_toMeasurable_inter_of_sum {s : Set α} (hs : MeasurableSet s) {t : 
Set α} {m : Nat -> Measure α} (hv : forall n, m n t != ∞) (hμ : μ = sum m) : μ (
toMeasurable μ t inter s) = μ (t inter s)
参数：hs : MeasurableSet s；hv : forall n, m n t != ∞；hμ : μ = sum m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.Measure.measure_toMeasurable_inter`：measure_toMeasurable_i
nter {s t : Set α} (hs : MeasurableSet s) (ht : μ t != ∞) : μ (toMeasurable μ t 
inter s) = μ (t inter s)
· 使用定理 `MeasureTheory.Measure.le_sum_apply`：le_sum_apply (f : ι -> Measure α) (s
 : Set α) : ∑' i, f i s <= sum f s
· 使用定理 `MeasureTheory.exists_measurable_superset`：exists_measurable_superset (μ 
: Measure α) (s : Set α) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = μ s
· 使用定理 `MeasureTheory.toMeasurable_def`：∀ {α : Type u_6} [inst : MeasurableSpace
 α] (μ : MeasureTheory.Measure α) (s : Set α),   MeasureTheory.toMeasurable μ s 
=     if h : ∃ t ⊇ s…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.ae_eq_set_inter`：ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s inter s' : Set α) =ᵐ[μ] (t inter t' : Set α)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If a measure `μ` is the sum of a countable family `mₙ`, and a set `t` has finite
 measure for
each `mₙ`, then its measurable superset `toMeasurable μ t` (which has the same m
easure as `t`)
satisfies, for any measurable set `s`, the equality `μ (toMeasurable μ t ∩ s) = 
μ (t ∩ s)`.
-/
theorem measure_toMeasurable_inter_of_sum {s : Set α} (hs : MeasurableSet s) {t : Set α}
    {m : ℕ → Measure α} (hv : ∀ n, m n t ≠ ∞) (hμ : μ = sum m) :
    μ (toMeasurable μ t ∩ s) = μ (t ∩ s) := by
  -- we show that there is a measurable superset of `t` satisfying the conclusion for any
  -- measurable set `s`. It is built for each measure `mₙ` using `toMeasurable`
  -- (which is well behaved for finite measure sets thanks to `measure_toMeasurable_inter`), and
  -- then taking the intersection over `n`.
  have A : ∃ t', t' ⊇ t ∧ MeasurableSet t' ∧ ∀ u, MeasurableSet u → μ (t' ∩ u) = μ (t ∩ u) := by
    let w n := toMeasurable (m n) t
    have T : t ⊆ ⋂ n, w n := subset_iInter (fun i ↦ subset_toMeasurable (m i) t)
    have M : MeasurableSet (⋂ n, w n) :=
      MeasurableSet.iInter (fun i ↦ measurableSet_toMeasurable (m i) t)
    refine ⟨⋂ n, w n, T, M, fun u hu ↦ ?_⟩
    refine le_antisymm ?_ (by gcongr)
    rw [hμ, sum_apply _ (M.inter hu)]
    apply le_trans _ (le_sum_apply _ _)
    apply ENNReal.tsum_le_tsum (fun i ↦ ?_)
    calc
    m i ((⋂ n, w n) ∩ u) ≤ m i (w i ∩ u) := by gcongr; apply iInter_subset
    _ = m i (t ∩ u) := measure_toMeasurable_inter hu (hv i)
  -- thanks to the definition of `toMeasurable`, the previous property will also be shared
  -- by `toMeasurable μ t`, which is enough to conclude the proof.
  rw [toMeasurable]
  split_ifs with ht
  · apply measure_congr
    exact ae_eq_set_inter ht.choose_spec.2.2 (ae_eq_refl _)
  · exact A.choose_spec.2.2 s hs

/-- If a set `t` is covered by a countable family of finite measure sets, then its measurable
superset `toMeasurable μ t` (which has the same measure as `t`) satisfies,
for any measurable set `s`, the equality `μ (toMeasurable μ t ∩ s) = μ (t ∩ s)`. -/
/-
**MeasureTheory.Measure.measure_toMeasurable_inter_of_cover** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_toMeasurable_inter_of_cover {s : Set α} (hs : MeasurableSet s) {t 
: Set α} {v : Nat -> Set α} (hv : t subseteq ⋃ n, v n) (h'v : forall n, μ (t int
er v n) != ∞) : μ (toMeasurable μ t inter s) = μ (t inter s)
参数：hs : MeasurableSet s；hv : t subseteq ⋃ n, v n；h'v : forall n, μ (t inter v n)
 != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `iUnion_disjointed`：iUnion_disjointed [PartialOrder ι] [LocallyFiniteOrde
rBot ι] {f : ι -> Set α} : ⋃ i, disjointed f i = ⋃ i, f i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.measure_toMeasurable_inter`：measure_toMeasurable_i
nter {s t : Set α} (hs : MeasurableSet s) (ht : μ t != ∞) : μ (toMeasurable μ t 
inter s) = μ (t inter s)
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `disjointed_le`：disjointed_le (f : ι -> α) : disjointed f <= f
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.disjointed`：∀ {α : Type u_1} {mα : MeasurableSpace α} {f :
 ℕ → Set α},   (∀ (i : ℕ), MeasurableSet (f i)) → ∀ (n : ℕ), MeasurableSet (disj
ointed f n)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
If a set `t` is covered by a countable family of finite measure sets, then its m
easurable
superset `toMeasurable μ t` (which has the same measure as `t`) satisfies,
for any measurable set `s`, the equality `μ (toMeasurable μ t ∩ s) = μ (t ∩ s)`.
-/
theorem measure_toMeasurable_inter_of_cover {s : Set α} (hs : MeasurableSet s) {t : Set α}
    {v : ℕ → Set α} (hv : t ⊆ ⋃ n, v n) (h'v : ∀ n, μ (t ∩ v n) ≠ ∞) :
    μ (toMeasurable μ t ∩ s) = μ (t ∩ s) := by
  -- we show that there is a measurable superset of `t` satisfying the conclusion for any
  -- measurable set `s`. It is built on each member of a spanning family using `toMeasurable`
  -- (which is well behaved for finite measure sets thanks to `measure_toMeasurable_inter`), and
  -- the desired property passes to the union.
  have A : ∃ t', t' ⊇ t ∧ MeasurableSet t' ∧ ∀ u, MeasurableSet u → μ (t' ∩ u) = μ (t ∩ u) := by
    let w n := toMeasurable μ (t ∩ v n)
    have hw : ∀ n, μ (w n) < ∞ := by
      intro n
      simp_rw [w, measure_toMeasurable]
      exact (h'v n).lt_top
    set t' := ⋃ n, toMeasurable μ (t ∩ disjointed w n) with ht'
    have tt' : t ⊆ t' :=
      calc
        t ⊆ ⋃ n, t ∩ disjointed w n := by
          rw [← inter_iUnion, iUnion_disjointed, inter_iUnion]
          intro x hx
          rcases mem_iUnion.1 (hv hx) with ⟨n, hn⟩
          refine mem_iUnion.2 ⟨n, ?_⟩
          have : x ∈ t ∩ v n := ⟨hx, hn⟩
          exact ⟨hx, subset_toMeasurable μ _ this⟩
        _ ⊆ ⋃ n, toMeasurable μ (t ∩ disjointed w n) :=
          iUnion_mono fun n => subset_toMeasurable _ _
    refine ⟨t', tt', MeasurableSet.iUnion fun n => measurableSet_toMeasurable μ _, fun u hu => ?_⟩
    apply le_antisymm _ (by gcongr)
    calc
      μ (t' ∩ u) ≤ ∑' n, μ (toMeasurable μ (t ∩ disjointed w n) ∩ u) := by
        rw [ht', iUnion_inter]
        exact measure_iUnion_le _
      _ = ∑' n, μ (t ∩ disjointed w n ∩ u) := by
        congr 1
        ext1 n
        apply measure_toMeasurable_inter hu
        apply ne_of_lt
        calc
          μ (t ∩ disjointed w n) ≤ μ (t ∩ w n) := by
            gcongr
            exact disjointed_le w n
          _ ≤ μ (w n) := measure_mono inter_subset_right
          _ < ∞ := hw n
      _ = ∑' n, μ.restrict (t ∩ u) (disjointed w n) := by
        congr 1
        ext1 n
        rw [restrict_apply, inter_comm t _, inter_assoc]
        refine MeasurableSet.disjointed (fun n => ?_) n
        exact measurableSet_toMeasurable _ _
      _ = μ.restrict (t ∩ u) (⋃ n, disjointed w n) := by
        rw [measure_iUnion]
        · exact disjoint_disjointed _
        · intro i
          refine MeasurableSet.disjointed (fun n => ?_) i
          exact measurableSet_toMeasurable _ _
      _ ≤ μ.restrict (t ∩ u) univ := measure_mono (subset_univ _)
      _ = μ (t ∩ u) := by rw [restrict_apply MeasurableSet.univ, univ_inter]
  -- thanks to the definition of `toMeasurable`, the previous property will also be shared
  -- by `toMeasurable μ t`, which is enough to conclude the proof.
  rw [toMeasurable]
  split_ifs with ht
  · apply measure_congr
    exact ae_eq_set_inter ht.choose_spec.2.2 (ae_eq_refl _)
  · exact A.choose_spec.2.2 s hs
/-
**MeasureTheory.Measure.restrict_toMeasurable_of_cover** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：restrict_toMeasurable_of_cover {s : Set α} {v : Nat -> Set α} (hv : s subs
eteq ⋃ n, v n) (h'v : forall n, μ (s inter v n) != ∞) : μ.restrict (toMeasurable
 μ s) = μ.restrict s
参数：hv : s subseteq ⋃ n, v n；h'v : forall n, μ (s inter v n) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.Measure.measure_toMeasurable_inter_of_cover`：measure_toMea
surable_inter_of_cover {s : Set α} (hs : MeasurableSet s) {t : Set α} {v : Nat -
> Set α} (hv : t subseteq ⋃ n, v n) (h'v : fora…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_toMeasurable_of_cover {s : Set α} {v : ℕ → Set α} (hv : s ⊆ ⋃ n, v n)
    (h'v : ∀ n, μ (s ∩ v n) ≠ ∞) : μ.restrict (toMeasurable μ s) = μ.restrict s :=
  ext fun t ht => by
    simp only [restrict_apply ht, inter_comm t, measure_toMeasurable_inter_of_cover ht hv h'v]

/-- The measurable superset `toMeasurable μ t` of `t` (which has the same measure as `t`)
satisfies, for any measurable set `s`, the equality `μ (toMeasurable μ t ∩ s) = μ (t ∩ s)`.
This only holds when `μ` is s-finite -- for example for σ-finite measures. For a version without
this assumption (but requiring that `t` has finite measure), see `measure_toMeasurable_inter`. -/
/-
**MeasureTheory.Measure.measure_toMeasurable_inter_of_sFinite** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_toMeasurable_inter_of_sFinite [SFinite μ] {s : Set α} (hs : Measur
ableSet s) (t : Set α) : μ (toMeasurable μ t inter s) = μ (t inter s)
参数：hs : MeasurableSet s；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measure_toMeasurable_inter_of_sum`：measure_toMeasu
rable_inter_of_sum {s : Set α} (hs : MeasurableSet s) {t : Set α} {m : Nat -> Me
asure α} (hv : forall n, m n t != ∞) (hμ : μ …
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ

--- 原说明 ---
The measurable superset `toMeasurable μ t` of `t` (which has the same measure as
 `t`)
satisfies, for any measurable set `s`, the equality `μ (toMeasurable μ t ∩ s) = 
μ (t ∩ s)`.
This only holds when `μ` is s-finite -- for example for σ-finite measures. For a
 version without
this assumption (but requiring that `t` has finite measure), see `measure_toMeas
urable_inter`.
-/
theorem measure_toMeasurable_inter_of_sFinite [SFinite μ] {s : Set α} (hs : MeasurableSet s)
    (t : Set α) : μ (toMeasurable μ t ∩ s) = μ (t ∩ s) :=
  measure_toMeasurable_inter_of_sum hs (fun _ ↦ measure_ne_top _ t) (sum_sfiniteSeq μ).symm

@[simp]
/-
**MeasureTheory.Measure.restrict_toMeasurable_of_sFinite** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Measure`。
形式化陈述：restrict_toMeasurable_of_sFinite [SFinite μ] (s : Set α) : μ.restrict (toM
easurable μ s) = μ.restrict s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.Measure.measure_toMeasurable_inter_of_sFinite`：measure_toM
easurable_inter_of_sFinite [SFinite μ] {s : Set α} (hs : MeasurableSet s) (t : S
et α) : μ (toMeasurable μ t inter s) = μ (t inter…
-/
theorem restrict_toMeasurable_of_sFinite [SFinite μ] (s : Set α) :
    μ.restrict (toMeasurable μ s) = μ.restrict s :=
  ext fun t ht => by
    rw [restrict_apply ht, inter_comm t, measure_toMeasurable_inter_of_sFinite ht,
      restrict_apply ht, inter_comm t]

/-- Auxiliary lemma for `iSup_restrict_spanningSets`. -/
/-
**MeasureTheory.Measure.iSup_restrict_spanningSets_of_measurableSet** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：iSup_restrict_spanningSets_of_measurableSet [SigmaFinite μ] (hs : Measurab
leSet s) : ⨆ i, μ.restrict (spanningSets μ i) s = μ s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_iUnion_apply_eq_iSup`：restrict_iUnion_app
ly_eq_iSup [Countable ι] {s : ι -> Set α} (hd : Directed (· subseteq ·) s) {t : 
Set α} (ht : MeasurableSet t) : μ.restric…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `MeasureTheory.monotone_spanningSets`：monotone_spanningSets (μ : Measure 
α) [SigmaFinite μ] : Monotone (spanningSets μ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ

--- 原说明 ---
Auxiliary lemma for `iSup_restrict_spanningSets`.
-/
theorem iSup_restrict_spanningSets_of_measurableSet [SigmaFinite μ] (hs : MeasurableSet s) :
    ⨆ i, μ.restrict (spanningSets μ i) s = μ s :=
  calc
    ⨆ i, μ.restrict (spanningSets μ i) s = μ.restrict (⋃ i, spanningSets μ i) s :=
      (restrict_iUnion_apply_eq_iSup (monotone_spanningSets μ).directed_le hs).symm
    _ = μ s := by rw [iUnion_spanningSets, restrict_univ]
/-
**MeasureTheory.Measure.iSup_restrict_spanningSets** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：iSup_restrict_spanningSets [SigmaFinite μ] (s : Set α) : ⨆ i, μ.restrict (
spanningSets μ i) s = μ s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `MeasureTheory.Measure.iSup_restrict_spanningSets_of_measurableSet`：iSup_
restrict_spanningSets_of_measurableSet [SigmaFinite μ] (hs : MeasurableSet s) : 
⨆ i, μ.restrict (spanningSets μ i) s = μ s
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.Measure.restrict_toMeasurable_of_sFinite`：restrict_toMeasu
rable_of_sFinite [SFinite μ] (s : Set α) : μ.restrict (toMeasurable μ s) = μ.res
trict s
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_restrict_spanningSets [SigmaFinite μ] (s : Set α) :
    ⨆ i, μ.restrict (spanningSets μ i) s = μ s := by
  rw [← measure_toMeasurable s,
    ← iSup_restrict_spanningSets_of_measurableSet (measurableSet_toMeasurable _ _)]
  simp_rw [restrict_apply' (measurableSet_spanningSets μ _), Set.inter_comm s,
    ← restrict_apply (measurableSet_spanningSets μ _), ← restrict_toMeasurable_of_sFinite s,
    restrict_apply (measurableSet_spanningSets μ _), Set.inter_comm _ (toMeasurable μ s)]

/-- In a σ-finite space, any measurable set of measure `> r` contains a measurable subset of
finite measure `> r`. -/
/-
**MeasureTheory.Measure.exists_subset_measure_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：exists_subset_measure_lt_top [SigmaFinite μ] {r : Real>=0∞} (hs : Measurab
leSet s) (h's : r < μ s) : exists t, MeasurableSet t ∧ t subseteq s ∧ r < μ t ∧ 
μ t < ∞
参数：hs : MeasurableSet s；h's : r < μ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iSup_iff`：lt_iSup_iff : a < iSup f ↔ exists i, a < f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.iSup_restrict_spanningSets`：iSup_restrict_spanning
Sets [SigmaFinite μ] (s : Set α) : ⨆ i, μ.restrict (spanningSets μ i) s = μ s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞

--- 原说明 ---
In a σ-finite space, any measurable set of measure `> r` contains a measurable s
ubset of
finite measure `> r`.
-/
theorem exists_subset_measure_lt_top [SigmaFinite μ] {r : ℝ≥0∞} (hs : MeasurableSet s)
    (h's : r < μ s) : ∃ t, MeasurableSet t ∧ t ⊆ s ∧ r < μ t ∧ μ t < ∞ := by
  rw [← iSup_restrict_spanningSets,
    @lt_iSup_iff _ _ _ r fun i : ℕ => μ.restrict (spanningSets μ i) s] at h's
  rcases h's with ⟨n, hn⟩
  simp only [restrict_apply hs] at hn
  refine
    ⟨s ∩ spanningSets μ n, hs.inter (measurableSet_spanningSets _ _), inter_subset_left, hn, ?_⟩
  exact (measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top _ _)

namespace FiniteSpanningSetsIn

variable {C D : Set (Set α)}

/-- If `μ` has finite spanning sets in `C` and `C ∩ {s | μ s < ∞} ⊆ D` then `μ` has finite spanning
sets in `D`. -/
/-
**MeasureTheory.Measure.FiniteSpanningSetsIn.mono'** 是 Mathlib 中的一个定义，位于命名空间 `Me
asureTheory.Measure.FiniteSpanningSetsIn`。
形式化陈述：{α : Type u_1} →   {m0 : MeasurableSpace α} →     {μ : MeasureTheory.Measu
re α} →       {C D : Set (Set α)} → μ.FiniteSpanningSetsIn C → C ∩ {s | μ s < ⊤}
 ⊆ D → μ.FiniteSpanningSetsIn D
参数：Set α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.finite`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self : μ
.FiniteSpanningSetsIn C) (i : ℕ), μ (se…
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.spanning`：∀ {α : Type u_1} {m
0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self :
 μ.FiniteSpanningSetsIn C), ⋃ i, self.set…

--- 原说明 ---
If `μ` has finite spanning sets in `C` and `C ∩ {s | μ s < ∞} ⊆ D` then `μ` has 
finite spanning
sets in `D`.
-/
protected def mono' (h : μ.FiniteSpanningSetsIn C) (hC : C ∩ { s | μ s < ∞ } ⊆ D) :
    μ.FiniteSpanningSetsIn D :=
  ⟨h.set, fun i => hC ⟨h.set_mem i, h.finite i⟩, h.finite, h.spanning⟩

/-- If `μ` has finite spanning sets in `C` and `C ⊆ D` then `μ` has finite spanning sets in `D`. -/
/-
**MeasureTheory.Measure.FiniteSpanningSetsIn.mono** 是 Mathlib 中的一个定义，位于命名空间 `Mea
sureTheory.Measure.FiniteSpanningSetsIn`。
形式化陈述：{α : Type u_1} →   {m0 : MeasurableSpace α} →     {μ : MeasureTheory.Measu
re α} → {C D : Set (Set α)} → μ.FiniteSpanningSetsIn C → C ⊆ D → μ.FiniteSpannin
gSetsIn D
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ` has finite spanning sets in `C` and `C ⊆ D` then `μ` has finite spanning 
sets in `D`.
-/
protected def mono (h : μ.FiniteSpanningSetsIn C) (hC : C ⊆ D) : μ.FiniteSpanningSetsIn D :=
  h.mono' fun _s hs => hC hs.1

/-- If `μ` has finite spanning sets in the collection of measurable sets `C`, then `μ` is σ-finite.
-/
/-
**MeasureTheory.Measure.FiniteSpanningSetsIn.sigmaFinite** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Measure.FiniteSpanningSetsIn`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C
 : Set (Set α)}   (h : μ.FiniteSpanningSetsIn C), MeasureTheory.SigmaFinite μ
参数：Set α；h : μ.FiniteSpanningSetsIn C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ

--- 原说明 ---
If `μ` has finite spanning sets in the collection of measurable sets `C`, then `
μ` is σ-finite.
-/
protected theorem sigmaFinite (h : μ.FiniteSpanningSetsIn C) : SigmaFinite μ :=
  ⟨⟨h.mono <| subset_univ C⟩⟩

/-- An extensionality for measures. It is `ext_of_generateFrom_of_iUnion` formulated in terms of
`FiniteSpanningSetsIn`. -/
/-
**MeasureTheory.Measure.FiniteSpanningSetsIn.ext** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure.FiniteSpanningSetsIn`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} 
{C : Set (Set α)},   m0 = MeasurableSpace.generateFrom C → IsPiSystem C → ∀ (h :
 μ.FiniteSpanningSetsIn C), (∀ s ∈ C, μ s = ν s) → μ = ν
参数：Set α；h : μ.FiniteSpanningSetsIn C；∀ s ∈ C, μ s = ν s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_generateFrom_of_iUnion`：ext_of_generateFrom
_of_iUnion (C : Set (Set α)) (B : Nat -> Set α) (hA : ‹_› = generateFrom C) (hC 
: IsPiSystem C) (h1B : ⋃ i, B i = univ) (…
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.spanning`：∀ {α : Type u_1} {m
0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self :
 μ.FiniteSpanningSetsIn C), ⋃ i, self.set…
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.set_mem`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self : 
μ.FiniteSpanningSetsIn C) (i : ℕ), self.…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.finite`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self : μ
.FiniteSpanningSetsIn C) (i : ℕ), μ (se…

--- 原说明 ---
An extensionality for measures. It is `ext_of_generateFrom_of_iUnion` formulated
 in terms of
`FiniteSpanningSetsIn`.
-/
protected theorem ext {ν : Measure α} {C : Set (Set α)} (hA : ‹_› = generateFrom C)
    (hC : IsPiSystem C) (h : μ.FiniteSpanningSetsIn C) (h_eq : ∀ s ∈ C, μ s = ν s) : μ = ν :=
  ext_of_generateFrom_of_iUnion C _ hA hC h.spanning h.set_mem (fun i => (h.finite i).ne) h_eq
/-
**MeasureTheory.Measure.FiniteSpanningSetsIn.isCountablySpanning** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.Measure.FiniteSpanningSetsIn`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C
 : Set (Set α)}   (h : μ.FiniteSpanningSetsIn C), IsCountablySpanning C
参数：Set α；h : μ.FiniteSpanningSetsIn C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.set_mem`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self : 
μ.FiniteSpanningSetsIn C) (i : ℕ), self.…
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.spanning`：∀ {α : Type u_1} {m
0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self :
 μ.FiniteSpanningSetsIn C), ⋃ i, self.set…
-/
protected theorem isCountablySpanning (h : μ.FiniteSpanningSetsIn C) : IsCountablySpanning C :=
  ⟨h.set, h.set_mem, h.spanning⟩

end FiniteSpanningSetsIn

/-
**MeasureTheory.Measure.sigmaFinite_of_countable** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：sigmaFinite_of_countable {S : Set (Set α)} (hc : S.Countable) (hμ : forall
 s in S, μ s < ∞) (hU : ⋃₀ S = univ) : SigmaFinite μ
参数：Set α；hc : S.Countable；hμ : forall s in S, μ s < ∞；hU : ⋃₀ S = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.exists_seq_cover_iff_countable`：exists_seq_cover_iff_countable {p : 
Set α -> Prop} (h : exists s, p s) : (exists s : Nat -> Set α, (forall n, p (s n
)) ∧ ⋃ n, s n = univ) ↔ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `trivial`：True
-/
theorem sigmaFinite_of_countable {S : Set (Set α)} (hc : S.Countable) (hμ : ∀ s ∈ S, μ s < ∞)
    (hU : ⋃₀ S = univ) : SigmaFinite μ := by
  obtain ⟨s, hμ, hs⟩ : ∃ s : ℕ → Set α, (∀ n, μ (s n) < ∞) ∧ ⋃ n, s n = univ :=
    (@exists_seq_cover_iff_countable _ (fun x => μ x < ∞) ⟨∅, by simp⟩).2 ⟨S, hc, hμ, hU⟩
  exact ⟨⟨⟨fun n => s n, fun _ => trivial, hμ, hs⟩⟩⟩

/-- Given measures `μ`, `ν` where `ν ≤ μ`, `FiniteSpanningSetsIn.ofLe` provides the induced
`FiniteSpanningSet` with respect to `ν` from a `FiniteSpanningSet` with respect to `μ`. -/
/-
**MeasureTheory.Measure.FiniteSpanningSetsIn.ofLE** 是 Mathlib 中的一个定义，位于命名空间 `Mea
sureTheory.Measure.FiniteSpanningSetsIn`。
形式化陈述：{α : Type u_1} →   {m0 : MeasurableSpace α} →     {μ ν : MeasureTheory.Mea
sure α} → ν ≤ μ → {C : Set (Set α)} → μ.FiniteSpanningSetsIn C → ν.FiniteSpannin
gSetsIn C
参数：Set α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.set_mem`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self : 
μ.FiniteSpanningSetsIn C) (i : ℕ), self.…
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.spanning`：∀ {α : Type u_1} {m
0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self :
 μ.FiniteSpanningSetsIn C), ⋃ i, self.set…

--- 原说明 ---
Given measures `μ`, `ν` where `ν ≤ μ`, `FiniteSpanningSetsIn.ofLe` provides the 
induced
`FiniteSpanningSet` with respect to `ν` from a `FiniteSpanningSet` with respect 
to `μ`.
-/
def FiniteSpanningSetsIn.ofLE (h : ν ≤ μ) {C : Set (Set α)} (S : μ.FiniteSpanningSetsIn C) :
    ν.FiniteSpanningSetsIn C where
  set := S.set
  set_mem := S.set_mem
  finite n := lt_of_le_of_lt (le_iff'.1 h _) (S.finite n)
  spanning := S.spanning
/-
**MeasureTheory.Measure.sigmaFinite_of_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：sigmaFinite_of_le (μ : Measure α) [hs : SigmaFinite μ] (h : ν <= μ) : Sigm
aFinite ν
参数：μ : Measure α；h : ν <= μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `MeasureTheory.SigmaFinite.out`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 {μ : MeasureTheory.Measure α},   MeasureTheory.SigmaFinite μ → Nonempty (μ.Fini
teSpanningSetsIn Se…
-/
theorem sigmaFinite_of_le (μ : Measure α) [hs : SigmaFinite μ] (h : ν ≤ μ) : SigmaFinite ν :=
  ⟨hs.out.map <| FiniteSpanningSetsIn.ofLE h⟩
/-
**MeasureTheory.Measure.add_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} (μ ν₁ ν₂ : MeasureTheory.Measure
 α) [MeasureTheory.SigmaFinite μ],   μ + ν₁ = μ + ν₂ ↔ ν₁ = ν₂
参数：μ ν₁ ν₂ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.ext_iff_of_iUnion_eq_univ`：ext_iff_of_iUnion_eq_un
iv [Countable ι] {s : ι -> Set α} (hs : ⋃ i, s i = univ) : μ = ν ↔ forall i, μ.r
estrict (s i) = ν.restrict (s i)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.add_right_inj`：add_right_inj (h : a != ∞) : a + b = a + c ↔ b = 
c
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma add_right_inj (μ ν₁ ν₂ : Measure α) [SigmaFinite μ] :
    μ + ν₁ = μ + ν₂ ↔ ν₁ = ν₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rw [ext_iff_of_iUnion_eq_univ (iUnion_spanningSets μ)]
  intro i
  ext s hs
  rw [← ENNReal.add_right_inj (measure_mono s.inter_subset_right |>.trans_lt <|
    measure_spanningSets_lt_top μ i).ne]
  simp only [ext_iff', coe_add, Pi.add_apply] at h
  simp [hs, h]
/-
**MeasureTheory.Measure.add_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} (μ ν₁ ν₂ : MeasureTheory.Measure
 α) [MeasureTheory.SigmaFinite μ],   ν₁ + μ = ν₂ + μ ↔ ν₁ = ν₂
参数：μ ν₁ ν₂ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.Measure.add_right_inj`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} (μ ν₁ ν₂ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ],   μ + 
ν₁ = μ + ν₂ ↔ ν₁ = ν₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma add_left_inj (μ ν₁ ν₂ : Measure α) [SigmaFinite μ] :
    ν₁ + μ = ν₂ + μ ↔ ν₁ = ν₂ := by rw [add_comm _ μ, add_comm _ μ, μ.add_right_inj]

end Measure

/-- Every finite measure is σ-finite. -/
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every finite measure is σ-finite.
-/
instance (priority := 100) IsFiniteMeasure.toSigmaFinite {_m0 : MeasurableSpace α} (μ : Measure α)
    [IsFiniteMeasure μ] : SigmaFinite μ :=
  ⟨⟨⟨fun _ => univ, fun _ => trivial, fun _ => measure_lt_top μ _, iUnion_const _⟩⟩⟩

/-- A measure on a countable space is sigma-finite iff it gives finite mass to every singleton.

See `measure_singleton_lt_top` for the forward direction without the countability assumption. -/
/-
**MeasureTheory.Measure.sigmaFinite_iff_measure_singleton_lt_top** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [C
ountable α],   MeasureTheory.SigmaFinite μ ↔ ∀ (a : α), μ {a} < ⊤
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.measure_singleton_lt_top`：measure_singleton_lt_top [SigmaF
inite μ] : μ {a} < ∞
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `exists_surjective_nat`：exists_surjective_nat (α : Sort u) [Nonempty α] [
Countable α] : exists f : Nat -> α, Surjective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A measure on a countable space is sigma-finite iff it gives finite mass to every
 singleton.

See `measure_singleton_lt_top` for the forward direction without the countabilit
y assumption.
-/
lemma Measure.sigmaFinite_iff_measure_singleton_lt_top [Countable α] :
    SigmaFinite μ ↔ ∀ a, μ {a} < ∞ where
  mp _ a := measure_singleton_lt_top
  mpr hμ := by
    cases isEmpty_or_nonempty α
    · rw [Subsingleton.elim μ 0]
      infer_instance
    · obtain ⟨f, hf⟩ := exists_surjective_nat α
      exact ⟨⟨⟨fun n ↦ {f n}, by simp, by simpa [hf.forall] using hμ, by simp [hf.range_eq]⟩⟩⟩
/-
**MeasureTheory.sigmaFinite_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：sigmaFinite_bot_iff (μ : @Measure α ⊥) : SigmaFinite μ ↔ IsFiniteMeasure μ
参数：μ : @Measure α ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
-/
theorem sigmaFinite_bot_iff (μ : @Measure α ⊥) : SigmaFinite μ ↔ IsFiniteMeasure μ := by
  refine ⟨fun h => ⟨?_⟩, fun h => by infer_instance⟩
  have : SigmaFinite μ := h
  let s := spanningSets μ
  have hs_univ : ⋃ i, s i = Set.univ := iUnion_spanningSets μ
  have hs_meas : ∀ i, MeasurableSet[⊥] (s i) := measurableSet_spanningSets μ
  simp_rw [MeasurableSpace.measurableSet_bot_iff] at hs_meas
  by_cases h_univ_empty : (Set.univ : Set α) = ∅
  · rw [h_univ_empty, measure_empty]
    exact ENNReal.zero_ne_top.lt_top
  obtain ⟨i, hsi⟩ : ∃ i, s i = Set.univ := by
    by_contra! h_not_univ
    have h_empty : ∀ i, s i = ∅ := by simpa [h_not_univ] using hs_meas
    simp only [h_empty, iUnion_empty] at hs_univ
    exact h_univ_empty hs_univ.symm
  rw [← hsi]
  exact measure_spanningSets_lt_top μ i
/-
**MeasureTheory.Restrict.sigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Re
strict`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [M
easureTheory.SigmaFinite μ] (s : Set α),   MeasureTheory.SigmaFinite (μ.restrict
 s)
参数：μ : MeasureTheory.Measure α；s : Set α；μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
-/
instance Restrict.sigmaFinite (μ : Measure α) [SigmaFinite μ] (s : Set α) :
    SigmaFinite (μ.restrict s) := by
  refine ⟨⟨⟨spanningSets μ, fun _ => trivial, fun i => ?_, iUnion_spanningSets μ⟩⟩⟩
  rw [Measure.restrict_apply (measurableSet_spanningSets μ i)]
  exact (measure_mono inter_subset_left).trans_lt (measure_spanningSets_lt_top μ i)
/-
**MeasureTheory.sum.sigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.sum`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {ι : Type u_4} [Finite ι] (μ : ι
 → MeasureTheory.Measure α)   [∀ (i : ι), MeasureTheory.SigmaFinite (μ i)], Meas
ureTheory.SigmaFinite (MeasureTheory.Measure.sum μ)
参数：μ : ι → MeasureTheory.Measure α；i : ι；μ i；MeasureTheory.Measure.sum μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `trivial`：True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `ENNReal.sum_lt_top`：∀ {α : Type u_1} {s : Finset α} {f : α → ENNReal}, ∑
 a ∈ s, f a < ⊤ ↔ ∀ a ∈ s, f a < ⊤
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `Set.iUnion_iInter_of_monotone`：iUnion_iInter_of_monotone {ι ι' α : Type*
} [Finite ι] [Preorder ι'] [IsDirectedOrder ι'] [Nonempty ι'] {s : ι -> ι' -> Se
t α} (hs : forall i…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.monotone_spanningSets`：monotone_spanningSets (μ : Measure 
α) [SigmaFinite μ] : Monotone (spanningSets μ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance sum.sigmaFinite {ι} [Finite ι] (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)] :
    SigmaFinite (sum μ) := by
  cases nonempty_fintype ι
  have : ∀ n, MeasurableSet (⋂ i : ι, spanningSets (μ i) n) := fun n =>
    MeasurableSet.iInter fun i => measurableSet_spanningSets (μ i) n
  refine ⟨⟨⟨fun n => ⋂ i, spanningSets (μ i) n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [sum_apply _ (this n), tsum_fintype, ENNReal.sum_lt_top]
    rintro i -
    exact (measure_mono <| iInter_subset _ i).trans_lt (measure_spanningSets_lt_top (μ i) n)
  · rw [iUnion_iInter_of_monotone]
    · simp_rw [iUnion_spanningSets, iInter_univ]
    exact fun i => monotone_spanningSets (μ i)
/-
**MeasureTheory.Add.sigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Add`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) 
[MeasureTheory.SigmaFinite μ]   [MeasureTheory.SigmaFinite ν], MeasureTheory.Sig
maFinite (μ + ν)
参数：μ ν : MeasureTheory.Measure α；μ + ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.sum_cond`：sum_cond (μ ν : Measure α) : (sum fun b 
=> cond b μ ν) = μ + ν
· 使用定理 `MeasureTheory.sum.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 {ι : Type u_4} [Finite ι] (μ : ι → MeasureTheory.Measure α)   [∀ (i : ι), Measu
reTheory.SigmaFinit…
-/
instance Add.sigmaFinite (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    SigmaFinite (μ + ν) := by
  rw [← sum_cond]
  refine @sum.sigmaFinite _ _ _ _ _ (Bool.rec ?_ ?_) <;> simpa
/-
**MeasureTheory.SMul.sigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.SMul`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [M
easureTheory.SigmaFinite μ] (c : NNReal),   MeasureTheory.SigmaFinite (c • μ)
参数：c : NNReal；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `trivial`：True
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
-/
instance SMul.sigmaFinite {μ : Measure α} [SigmaFinite μ] (c : ℝ≥0) :
    MeasureTheory.SigmaFinite (c • μ) where
  out' :=
  ⟨{  set := spanningSets μ
      set_mem := fun _ ↦ trivial
      finite := by
        intro i
        simp only [Measure.coe_smul, Pi.smul_apply, nnreal_smul_coe_apply]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_spanningSets_lt_top μ i)
      spanning := iUnion_spanningSets μ }⟩
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SigmaFinite (μ.restrict s)] [SigmaFinite (μ.restrict t)] :
    SigmaFinite (μ.restrict (s ∪ t)) := sigmaFinite_of_le _ (restrict_union_le _ _)
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SigmaFinite (μ.restrict s)] : SigmaFinite (μ.restrict (s ∩ t)) :=
  sigmaFinite_of_le (μ.restrict s) (restrict_mono_ae (ae_of_all _ Set.inter_subset_left))
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SigmaFinite (μ.restrict t)] : SigmaFinite (μ.restrict (s ∩ t)) :=
  sigmaFinite_of_le (μ.restrict t) (restrict_mono_ae (ae_of_all _ Set.inter_subset_right))
/-
**MeasureTheory.SigmaFinite.of_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Sigm
aFinite`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} [inst : Measurabl
eSpace β] (μ : MeasureTheory.Measure α)   {f : α → β},   AEMeasurable f μ → Meas
ureTheory.SigmaFinite (MeasureTheory.Measure.map f μ) → MeasureTheory.SigmaFinit
e μ
参数：μ : MeasureTheory.Measure α；MeasureTheory.Measure.map f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
-/
theorem SigmaFinite.of_map (μ : Measure α) {f : α → β} (hf : AEMeasurable f μ)
    (h : SigmaFinite (μ.map f)) : SigmaFinite μ :=
  ⟨⟨⟨fun n => f ⁻¹' spanningSets (μ.map f) n, fun _ => trivial, fun n => by
        simp only [← map_apply_of_aemeasurable hf, measurableSet_spanningSets,
          measure_spanningSets_lt_top],
        by rw [← preimage_iUnion, iUnion_spanningSets, preimage_univ]⟩⟩⟩
/-
**MeasureTheory._root_.MeasurableEmbedding.sigmaFinite_map** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEmbedding.sigmaFinite_map {f : α → β} (hf : MeasurableEmbedding f)
    [SigmaFinite μ] :
    SigmaFinite (μ.map f) := by
  refine ⟨fun n ↦ f '' (spanningSets μ n) ∪ (Set.range f)ᶜ, by simp, fun n ↦ ?_, ?_⟩
  · rw [hf.map_apply, Set.preimage_union]
    simp only [Set.preimage_compl, Set.preimage_range, Set.compl_univ, Set.union_empty,
      Set.preimage_image_eq _ hf.injective]
    exact measure_spanningSets_lt_top μ n
  · rw [← Set.iUnion_union, ← Set.image_iUnion, iUnion_spanningSets,
      Set.image_univ, Set.union_compl_self]
/-
**MeasureTheory._root_.MeasurableEquiv.sigmaFinite_map** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEquiv.sigmaFinite_map (f : α ≃ᵐ β) [SigmaFinite μ] :
    SigmaFinite (μ.map f) := f.measurableEmbedding.sigmaFinite_map

/-- Similar to `ae_of_forall_measure_lt_top_ae_restrict`, but where you additionally get the
  hypothesis that another σ-finite measure has finite values on `s`. -/
/-
**MeasureTheory.ae_of_forall_measure_lt_top_ae_restrict'** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：ae_of_forall_measure_lt_top_ae_restrict' {μ : Measure α} (ν : Measure α) [
SigmaFinite μ] [SigmaFinite ν] (P : α -> Prop) (h : forall s, MeasurableSet s ->
 μ s < ∞ -> ν s < ∞ -> forallᵐ x ∂μ.restrict s, P x) : forallᵐ x ∂μ, P x
参数：ν : Measure α；P : α -> Prop；h : forall s, MeasurableSet s -> μ s < ∞ -> ν s <
 ∞ -> forallᵐ x ∂μ.restrict s, P x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Add.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 (μ ν : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]   [MeasureTheory.
SigmaFinite ν], Mea…
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `self_le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] (a b : α), a ≤ a + b
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.mem_spanningSetsIndex`：mem_spanningSetsIndex (μ : Measure 
α) [SigmaFinite μ] (x : α) : x in spanningSets μ (spanningSetsIndex μ x)

--- 原说明 ---
Similar to `ae_of_forall_measure_lt_top_ae_restrict`, but where you additionally
 get the
  hypothesis that another σ-finite measure has finite values on `s`.
-/
theorem ae_of_forall_measure_lt_top_ae_restrict' {μ : Measure α} (ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] (P : α → Prop)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ν s < ∞ → ∀ᵐ x ∂μ.restrict s, P x) : ∀ᵐ x ∂μ, P x := by
  have : ∀ n, ∀ᵐ x ∂μ, x ∈ spanningSets (μ + ν) n → P x := by
    intro n
    have := h
      (spanningSets (μ + ν) n) (measurableSet_spanningSets _ _)
      ((self_le_add_right _ _).trans_lt (measure_spanningSets_lt_top (μ + ν) _))
      ((self_le_add_left _ _).trans_lt (measure_spanningSets_lt_top (μ + ν) _))
    exact (ae_restrict_iff' (measurableSet_spanningSets _ _)).mp this
  filter_upwards [ae_all_iff.2 this] with _ hx using hx _ (mem_spanningSetsIndex _ _)

/-- To prove something for almost all `x` w.r.t. a σ-finite measure, it is sufficient to show that
  this holds almost everywhere in sets where the measure has finite value. -/
/-
**MeasureTheory.ae_of_forall_measure_lt_top_ae_restrict** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：ae_of_forall_measure_lt_top_ae_restrict {μ : Measure α} [SigmaFinite μ] (P
 : α -> Prop) (h : forall s, MeasurableSet s -> μ s < ∞ -> forallᵐ x ∂μ.restrict
 s, P x) : forallᵐ x ∂μ, P x
参数：P : α -> Prop；h : forall s, MeasurableSet s -> μ s < ∞ -> forallᵐ x ∂μ.restri
ct s, P x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_of_forall_measure_lt_top_ae_restrict'`：ae_of_forall_mea
sure_lt_top_ae_restrict' {μ : Measure α} (ν : Measure α) [SigmaFinite μ] [SigmaF
inite ν] (P : α -> Prop) (h : forall s, Meas…

--- 原说明 ---
To prove something for almost all `x` w.r.t. a σ-finite measure, it is sufficien
t to show that
  this holds almost everywhere in sets where the measure has finite value.
-/
theorem ae_of_forall_measure_lt_top_ae_restrict {μ : Measure α} [SigmaFinite μ] (P : α → Prop)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∀ᵐ x ∂μ.restrict s, P x) : ∀ᵐ x ∂μ, P x :=
  ae_of_forall_measure_lt_top_ae_restrict' μ P fun s hs h2s _ => h s hs h2s
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SigmaFinite.of_isFiniteMeasureOnCompacts [TopologicalSpace α]
    [SigmaCompactSpace α] (μ : Measure α) [IsFiniteMeasureOnCompacts μ] : SigmaFinite μ :=
  ⟨⟨{   set := compactCovering α
        set_mem := fun _ => trivial
        finite := fun n => (isCompact_compactCovering α n).measure_lt_top
        spanning := iUnion_compactCovering α }⟩⟩

-- see Note [lower instance priority]
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) sigmaFinite_of_locallyFinite [TopologicalSpace α]
    [SecondCountableTopology α] [IsLocallyFiniteMeasure μ] : SigmaFinite μ := by
  choose s hsx hsμ using μ.finiteAt_nhds
  rcases TopologicalSpace.countable_cover_nhds hsx with ⟨t, htc, htU⟩
  refine Measure.sigmaFinite_of_countable (htc.image s) (forall_mem_image.2 fun x _ => hsμ x) ?_
  rwa [sUnion_image]

namespace Measure

section disjointed

/-- Given `S : μ.FiniteSpanningSetsIn {s | MeasurableSet s}`,
`FiniteSpanningSetsIn.disjointed` provides a `FiniteSpanningSetsIn {s | MeasurableSet s}`
such that its underlying sets are pairwise disjoint. -/
/-
**MeasureTheory.Measure.FiniteSpanningSetsIn.disjointed** 是 Mathlib 中的一个定义，位于命名空
间 `MeasureTheory.Measure.FiniteSpanningSetsIn`。
形式化陈述：{α : Type u_1} →   {m0 : MeasurableSpace α} →     {μ : MeasureTheory.Measu
re α} →       μ.FiniteSpanningSetsIn {s | MeasurableSet s} → μ.FiniteSpanningSet
sIn {s | MeasurableSet s}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `S : μ.FiniteSpanningSetsIn {s | MeasurableSet s}`,
`FiniteSpanningSetsIn.disjointed` provides a `FiniteSpanningSetsIn {s | Measurab
leSet s}`
such that its underlying sets are pairwise disjoint.
-/
protected def FiniteSpanningSetsIn.disjointed {μ : Measure α}
    (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s }) :
    μ.FiniteSpanningSetsIn { s | MeasurableSet s } :=
  ⟨disjointed S.set, MeasurableSet.disjointed S.set_mem, fun n =>
    lt_of_le_of_lt (measure_mono (disjointed_subset S.set n)) (S.finite _),
    S.spanning ▸ iUnion_disjointed⟩
/-
**MeasureTheory.Measure.FiniteSpanningSetsIn.disjointed_set_eq** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Measure.FiniteSpanningSetsIn`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
(S : μ.FiniteSpanningSetsIn {s | MeasurableSet s}), S.disjointed.set = disjointe
d S.set
参数：S : μ.FiniteSpanningSetsIn {s | MeasurableSet s}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem FiniteSpanningSetsIn.disjointed_set_eq {μ : Measure α}
    (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s }) : S.disjointed.set = disjointed S.set :=
  rfl
/-
**MeasureTheory.Measure.exists_eq_disjoint_finiteSpanningSetsIn** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：exists_eq_disjoint_finiteSpanningSetsIn (μ ν : Measure α) [SigmaFinite μ] 
[SigmaFinite ν] : exists (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s }) (T
 : ν.FiniteSpanningSetsIn { s | MeasurableSet s }), S.set = T.set ∧ Pairwise (Di
sjoint on S.set)
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Add.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 (μ ν : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]   [MeasureTheory.
SigmaFinite ν], Mea…
· 使用定理 `MeasureTheory.Measure.le_add_right`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν + ν'
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Measure.le_add_left`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν' + ν
· 使用定理 `disjoint_disjointed`：disjoint_disjointed (f : ι -> α) : Pairwise (Disjoi
nt on disjointed f)
-/
theorem exists_eq_disjoint_finiteSpanningSetsIn (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    ∃ (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s })
      (T : ν.FiniteSpanningSetsIn { s | MeasurableSet s }),
      S.set = T.set ∧ Pairwise (Disjoint on S.set) :=
  let S := (μ + ν).toFiniteSpanningSetsIn.disjointed
  ⟨S.ofLE (Measure.le_add_right le_rfl), S.ofLE (Measure.le_add_left le_rfl), rfl,
    disjoint_disjointed _⟩

end disjointed

end Measure

end MeasureTheory

