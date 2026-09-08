/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The “almost everywhere” filter of co-null sets.

If `μ` is an outer measure or a measure on `α`,
then `MeasureTheory.ae μ` is the filter of co-null sets: `s ∈ ae μ ↔ μ sᶜ = 0`.

In this file we define the filter and prove some basic theorems about it.

## Notation

- `∀ᵐ x ∂μ, p x`: the predicate `p` holds for `μ`-a.e. all `x`;
- `∃ᶠ x ∂μ, p x`: the predicate `p` holds on a set of nonzero measure;
- `f =ᵐ[μ] g`: `f x = g x` for `μ`-a.e. all `x`;
- `f ≤ᵐ[μ] g`: `f x ≤ g x` for `μ`-a.e. all `x`.

## Implementation details

All notation introduced in this file
reducibly unfolds to the corresponding definitions about filters,
so generic lemmas about `Filter.Eventually`, `Filter.EventuallyEq` etc. apply.
However, we restate some lemmas specifically for `ae`.

## Tags

outer measure, measure, almost everywhere
-/

@[expose] public section

open Filter Set
open scoped ENNReal

namespace MeasureTheory

variable {α β F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] {μ : F} {s t : Set α}

/-- The “almost everywhere” filter of co-null sets. -/
@[wikidata Q1139334]
/-
**MeasureTheory.ae** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：ae (μ : F) : Filter α
参数：μ : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0

--- 原说明 ---
The “almost everywhere” filter of co-null sets.
-/
def ae (μ : F) : Filter α :=
  .ofCountableUnion (μ · = 0) (fun _S hSc ↦ (measure_sUnion_null_iff hSc).2) fun _t ht _s hs ↦
    measure_mono_null hs ht
deriving CountableInterFilter

/-- `∀ᵐ a ∂μ, p a` means that `p a` for a.e. `a`, i.e. `p` holds true away from a null set.

This is notation for `Filter.Eventually p (MeasureTheory.ae μ)`. -/
notation3 "∀ᵐ "(...)" ∂"μ", "r:(scoped p => Filter.Eventually p <| MeasureTheory.ae μ) => r

/-- `∃ᵐ a ∂μ, p a` means that `p` holds `∂μ`-frequently,
i.e. `p` holds on a set of positive measure.

This is notation for `Filter.Frequently p (MeasureTheory.ae μ)`. -/
notation3 "∃ᵐ "(...)" ∂"μ", "r:(scoped P => Filter.Frequently P <| MeasureTheory.ae μ) => r

/-- `f =ᵐ[μ] g` means `f` and `g` are eventually equal along the a.e. filter,
i.e. `f=g` away from a null set.

This is notation for `Filter.EventuallyEq (MeasureTheory.ae μ) f g`. -/
notation3:50 f " =ᵐ[" μ:50 "] " g:50 => Filter.EventuallyEq (MeasureTheory.ae μ) f g

/-- `f ≤ᵐ[μ] g` means `f` is eventually less than `g` along the a.e. filter,
i.e. `f ≤ g` away from a null set.

This is notation for `Filter.EventuallyLE (MeasureTheory.ae μ) f g`. -/
notation3:50 f " ≤ᵐ[" μ:50 "] " g:50 => Filter.EventuallyLE (MeasureTheory.ae μ) f g

/-
**MeasureTheory.mem_ae_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ae_iff {s : Set α} : s ∈ ae μ ↔ μ sᶜ = 0 :=
  Iff.rfl
/-
**MeasureTheory.ae_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ { a | ¬p a } = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ae_iff {p : α → Prop} : (∀ᵐ a ∂μ, p a) ↔ μ { a | ¬p a } = 0 :=
  Iff.rfl
/-
**MeasureTheory.compl_mem_ae_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：compl_mem_ae_iff {s : Set α} : sᶜ in ae μ ↔ μ s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem compl_mem_ae_iff {s : Set α} : sᶜ ∈ ae μ ↔ μ s = 0 := by simp only [mem_ae_iff, compl_compl]
/-
**MeasureTheory.frequently_ae_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：frequently_ae_iff {p : α -> Prop} : (existsᵐ a ∂μ, p a) ↔ μ { a | p a } !=
 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MeasureTheory.compl_mem_ae_iff`：compl_mem_ae_iff {s : Set α} : sᶜ in ae 
μ ↔ μ s = 0
-/
theorem frequently_ae_iff {p : α → Prop} : (∃ᵐ a ∂μ, p a) ↔ μ { a | p a } ≠ 0 :=
  not_congr compl_mem_ae_iff
/-
**MeasureTheory.frequently_ae_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：frequently_ae_mem_iff {s : Set α} : (existsᵐ a ∂μ, a in s) ↔ μ s != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MeasureTheory.compl_mem_ae_iff`：compl_mem_ae_iff {s : Set α} : sᶜ in ae 
μ ↔ μ s = 0
-/
theorem frequently_ae_mem_iff {s : Set α} : (∃ᵐ a ∂μ, a ∈ s) ↔ μ s ≠ 0 :=
  not_congr compl_mem_ae_iff
/-
**MeasureTheory.measure_eq_zero_iff_ae_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：measure_eq_zero_iff_ae_notMem {s : Set α} : μ s = 0 ↔ forallᵐ a ∂μ, a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.compl_mem_ae_iff`：compl_mem_ae_iff {s : Set α} : sᶜ in ae 
μ ↔ μ s = 0
-/
theorem measure_eq_zero_iff_ae_notMem {s : Set α} : μ s = 0 ↔ ∀ᵐ a ∂μ, a ∉ s :=
  compl_mem_ae_iff.symm
/-
**MeasureTheory.ae_of_all** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_of_all {p : α -> Prop} (μ : F) : (forall a, p a) -> forallᵐ a ∂μ, p a
参数：μ : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem ae_of_all {p : α → Prop} (μ : F) : (∀ a, p a) → ∀ᵐ a ∂μ, p a :=
  Eventually.of_forall
/-
**MeasureTheory.ae_all_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_all_iff {ι : Sort*} [Countable ι] {p : α -> ι -> Prop} : (forallᵐ a ∂μ,
 forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_countable_forall`：eventually_countable_forall [Countable ι] {
p : α -> ι -> Prop} : (forallᶠ x in l, forall i, p x i) ↔ forall i, forallᶠ x in
 l, p x i
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
-/
theorem ae_all_iff {ι : Sort*} [Countable ι] {p : α → ι → Prop} :
    (∀ᵐ a ∂μ, ∀ i, p a i) ↔ ∀ i, ∀ᵐ a ∂μ, p a i :=
  eventually_countable_forall
/-
**MeasureTheory.all_ae_of** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：all_ae_of {ι : Sort*} {p : α -> ι -> Prop} (hp : forallᵐ a ∂μ, forall i, p
 a i) (i : ι) : forallᵐ a ∂μ, p a i
参数：hp : forallᵐ a ∂μ, forall i, p a i；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem all_ae_of {ι : Sort*} {p : α → ι → Prop} (hp : ∀ᵐ a ∂μ, ∀ i, p a i) (i : ι) :
    ∀ᵐ a ∂μ, p a i := by
  filter_upwards [hp] with a ha using ha i
/-
**MeasureTheory.ae_iff_of_countable** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_iff_of_countable [Countable α] {p : α -> Prop} : (forallᵐ x ∂μ, p x) ↔ 
forall x, μ {x} != 0 -> p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用引理 `MeasureTheory.measure_null_iff_singleton`：measure_null_iff_singleton (hs
 : s.Countable) : μ s = 0 ↔ forall x in s, μ {x} = 0
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
-/
lemma ae_iff_of_countable [Countable α] {p : α → Prop} : (∀ᵐ x ∂μ, p x) ↔ ∀ x, μ {x} ≠ 0 → p x := by
  rw [ae_iff, measure_null_iff_singleton]
  exacts [forall_congr' fun _ ↦ not_imp_comm, Set.to_countable _]
/-
**MeasureTheory.ae_ball_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_ball_iff {ι : Type*} {S : Set ι} (hS : S.Countable) {p : α -> forall i 
in S, Prop} : (forallᵐ x ∂μ, forall i (hi : i in S), p x i hi) ↔ forall i (hi : 
i in S), forallᵐ x ∂μ, p x i hi
参数：hS : S.Countable。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_countable_ball`：eventually_countable_ball {ι : Type*} {S : Se
t ι} (hS : S.Countable) {p : α -> forall i in S, Prop} : (forallᶠ x in l, forall
 i hi, p x i hi…
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
-/
theorem ae_ball_iff {ι : Type*} {S : Set ι} (hS : S.Countable) {p : α → ∀ i ∈ S, Prop} :
    (∀ᵐ x ∂μ, ∀ i (hi : i ∈ S), p x i hi) ↔ ∀ i (hi : i ∈ S), ∀ᵐ x ∂μ, p x i hi :=
  eventually_countable_ball hS
/-
**MeasureTheory.ae_eq_refl** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
lemma ae_eq_refl (f : α → β) : f =ᵐ[μ] f := EventuallyEq.rfl
/-
**MeasureTheory.ae_eq_rfl** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_rfl {f : α -> β} : f =ᵐ[μ] f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
lemma ae_eq_rfl {f : α → β} : f =ᵐ[μ] f := EventuallyEq.rfl
/-
**MeasureTheory.ae_eq_comm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_comm {f g : α -> β} : f =ᵐ[μ] g ↔ g =ᵐ[μ] f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.eventuallyEq_comm`：eventuallyEq_comm {f g : α -> β} {l : Filter α
} : f =ᶠ[l] g ↔ g =ᶠ[l] f
-/
lemma ae_eq_comm {f g : α → β} : f =ᵐ[μ] g ↔ g =ᵐ[μ] f := eventuallyEq_comm
/-
**MeasureTheory.ae_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_symm {f g : α -> β} (h : f =ᵐ[μ] g) : g =ᵐ[μ] f
参数：h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem ae_eq_symm {f g : α → β} (h : f =ᵐ[μ] g) : g =ᵐ[μ] f :=
  h.symm
/-
**MeasureTheory.ae_eq_trans** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_trans {f g h : α -> β} (h₁ : f =ᵐ[μ] g) (h₂ : g =ᵐ[μ] h) : f =ᵐ[μ] h
参数：h₁ : f =ᵐ[μ] g；h₂ : g =ᵐ[μ] h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
-/
theorem ae_eq_trans {f g h : α → β} (h₁ : f =ᵐ[μ] g) (h₂ : g =ᵐ[μ] h) : f =ᵐ[μ] h :=
  h₁.trans h₂
/-
**MeasureTheory.aeEq_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：aeEq_iff {f g : α -> β} : f =ᵐ[μ] g ↔ μ {x | f x != g x} = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma aeEq_iff {f g : α → β} : f =ᵐ[μ] g ↔ μ {x | f x ≠ g x} = 0 := by rfl
/-
**MeasureTheory._root_.Set.EqOn.aeEq** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.EqOn.aeEq {f g : α → β} (h : s.EqOn f g) (h2 : μ sᶜ = 0) : f =ᵐ[μ] g :=
  eventuallyEq_of_mem h2 h
/-
**MeasureTheory.ae_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {F : Type u_3} [inst : FunLike F (Set α) ENNReal] [inst_1
 : MeasureTheory.OuterMeasureClass F α]   {μ : F}, MeasureTheory.ae μ = ⊤ ↔ ∀ (a
 : α), μ {a} ≠ 0
参数：Set α；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_empty_iff`：compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
-/
@[simp] lemma ae_eq_top : ae μ = ⊤ ↔ ∀ a, μ {a} ≠ 0 := by
  simp only [Filter.ext_iff, mem_ae_iff, mem_top, ne_eq]
  refine ⟨fun h a ha ↦ by simpa [ha] using (h {a}ᶜ).1, fun h s ↦ ⟨fun hs ↦ ?_, ?_⟩⟩
  · rw [← compl_empty_iff, ← not_nonempty_iff_eq_empty]
    rintro ⟨a, ha⟩
    exact h _ <| measure_mono_null (singleton_subset_iff.2 ha) hs
  · rintro rfl
    simp
/-
**MeasureTheory.ae_le_of_ae_lt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_le_of_ae_lt {β : Type*} [Preorder β] {f g : α -> β} (h : forallᵐ x ∂μ, 
f x < g x) : f <=ᵐ[μ] g
参数：h : forallᵐ x ∂μ, f x < g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem ae_le_of_ae_lt {β : Type*} [Preorder β] {f g : α → β} (h : ∀ᵐ x ∂μ, f x < g x) :
    f ≤ᵐ[μ] g :=
  h.mono fun _ ↦ le_of_lt

@[simp]
/-
**MeasureTheory.ae_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.eventuallyEq_empty`：eventuallyEq_empty {s : Set α} {l : Filter α}
 : s =ᶠ[l] (∅ : Set α) ↔ forallᶠ x in l, x ∉ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0 :=
  eventuallyEq_empty.trans <| by simp only [ae_iff, Classical.not_not, ofPred_mem_eq]

-- The priority should be higher than `eventuallyEq_univ`.
@[simp high]
/-
**MeasureTheory.ae_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_univ : s =ᵐ[μ] (univ : Set α) ↔ μ sᶜ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventuallyEq_univ`：eventuallyEq_univ {s : Set α} {l : Filter α} :
 s =ᶠ[l] univ ↔ s in l
-/
theorem ae_eq_univ : s =ᵐ[μ] (univ : Set α) ↔ μ sᶜ = 0 :=
  eventuallyEq_univ
/-
**MeasureTheory.ae_le_set** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_le_set : s <=ᵐ[μ] t ↔ μ (s \ t) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ae_le_set : s ≤ᵐ[μ] t ↔ μ (s \ t) = 0 :=
  calc
    s ≤ᵐ[μ] t ↔ ∀ᵐ x ∂μ, x ∈ s → x ∈ t := Iff.rfl
    _ ↔ μ (s \ t) = 0 := by simp [ae_iff]; rfl
/-
**MeasureTheory.ae_le_set_inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_le_set_inter {s' t' : Set α} (h : s <=ᵐ[μ] t) (h' : s' <=ᵐ[μ] t') : (s 
inter s' : Set α) <=ᵐ[μ] (t inter t' : Set α)
参数：h : s <=ᵐ[μ] t；h' : s' <=ᵐ[μ] t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s ≤ᶠ[l] t → s' ≤ᶠ[l] t' → s ∩ s' ≤ᶠ[l] t ∩ t'
-/
theorem ae_le_set_inter {s' t' : Set α} (h : s ≤ᵐ[μ] t) (h' : s' ≤ᵐ[μ] t') :
    (s ∩ s' : Set α) ≤ᵐ[μ] (t ∩ t' : Set α) :=
  h.inter h'
/-
**MeasureTheory.ae_le_set_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_le_set_union {s' t' : Set α} (h : s <=ᵐ[μ] t) (h' : s' <=ᵐ[μ] t') : (s 
union s' : Set α) <=ᵐ[μ] (t union t' : Set α)
参数：h : s <=ᵐ[μ] t；h' : s' <=ᵐ[μ] t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.union`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s ≤ᶠ[l] t → s' ≤ᶠ[l] t' → s ∪ s' ≤ᶠ[l] t ∪ t'
-/
theorem ae_le_set_union {s' t' : Set α} (h : s ≤ᵐ[μ] t) (h' : s' ≤ᵐ[μ] t') :
    (s ∪ s' : Set α) ≤ᵐ[μ] (t ∪ t' : Set α) :=
  h.union h'

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.union_ae_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：union_ae_eq_right : (s union t : Set α) =ᵐ[μ] t ↔ μ (s \ t) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.union_sdiff_right`：union_sdiff_right {s t : Set α} : (s union t) \ t
 = s \ t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem union_ae_eq_right : (s ∪ t : Set α) =ᵐ[μ] t ↔ μ (s \ t) = 0 := by
  simp [eventuallyLE_antisymm_iff, ae_le_set, union_sdiff_right,
    sdiff_eq_empty.2 Set.subset_union_right]

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.sdiff_ae_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：sdiff_ae_eq_self : (s \ t : Set α) =ᵐ[μ] s ↔ μ (s inter t) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sdiff_sdiff_self`：sdiff_sdiff_self : (a \ b) \ a = ⊥
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sdiff_ae_eq_self : (s \ t : Set α) =ᵐ[μ] s ↔ μ (s ∩ t) = 0 := by
  simp [eventuallyLE_antisymm_iff, ae_le_set]

@[deprecated (since := "2026-06-03")] alias diff_ae_eq_self := sdiff_ae_eq_self
/-
**MeasureTheory.sdiff_null_ae_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：sdiff_null_ae_eq_self (ht : μ t = 0) : (s \ t : Set α) =ᵐ[μ] s
参数：ht : μ t = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.sdiff_ae_eq_self`：sdiff_ae_eq_self : (s \ t : Set α) =ᵐ[μ]
 s ↔ μ (s inter t) = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem sdiff_null_ae_eq_self (ht : μ t = 0) : (s \ t : Set α) =ᵐ[μ] s :=
  sdiff_ae_eq_self.mpr (measure_mono_null inter_subset_right ht)

@[deprecated (since := "2026-06-03")] alias diff_null_ae_eq_self := sdiff_null_ae_eq_self

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.ae_eq_set** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_set {s t : Set α} : s =ᵐ[μ] t ↔ μ (s \ t) = 0 ∧ μ (t \ s) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ae_eq_set {s t : Set α} : s =ᵐ[μ] t ↔ μ (s \ t) = 0 ∧ μ (t \ s) = 0 := by
  simp [eventuallyLE_antisymm_iff, ae_le_set]

open scoped symmDiff in
@[simp]
/-
**MeasureTheory.measure_symmDiff_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：measure_symmDiff_eq_zero_iff {s t : Set α} : μ (s ∆ t) = 0 ↔ s =ᵐ[μ] t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem measure_symmDiff_eq_zero_iff {s t : Set α} : μ (s ∆ t) = 0 ↔ s =ᵐ[μ] t := by
  simp [ae_eq_set, symmDiff_def]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MeasureTheory.ae_eq_set_compl_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_set_compl_compl {s t : Set α} : sᶜ =ᵐ[μ] tᶜ ↔ s =ᵐ[μ] t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `compl_symmDiff_compl`：compl_symmDiff_compl : aᶜ ∆ bᶜ = a ∆ b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ae_eq_set_compl_compl {s t : Set α} : sᶜ =ᵐ[μ] tᶜ ↔ s =ᵐ[μ] t := by
  simp only [← measure_symmDiff_eq_zero_iff, compl_symmDiff_compl]

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.ae_eq_set_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_set_compl {s t : Set α} : sᶜ =ᵐ[μ] t ↔ s =ᵐ[μ] tᶜ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_eq_set_compl_compl`：ae_eq_set_compl_compl {s t : Set α}
 : sᶜ =ᵐ[μ] tᶜ ↔ s =ᵐ[μ] t
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ae_eq_set_compl {s t : Set α} : sᶜ =ᵐ[μ] t ↔ s =ᵐ[μ] tᶜ := by
  rw [← ae_eq_set_compl_compl, compl_compl]
/-
**MeasureTheory.ae_eq_set_inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') : (s in
ter s' : Set α) =ᵐ[μ] (t inter t' : Set α)
参数：h : s =ᵐ[μ] t；h' : s' =ᵐ[μ] t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∩ s' =ᶠ[l] t ∩ t'
-/
theorem ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') :
    (s ∩ s' : Set α) =ᵐ[μ] (t ∩ t' : Set α) :=
  h.inter h'
/-
**MeasureTheory.ae_eq_set_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_set_union {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') : (s un
ion s' : Set α) =ᵐ[μ] (t union t' : Set α)
参数：h : s =ᵐ[μ] t；h' : s' =ᵐ[μ] t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.union`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∪ s' =ᶠ[l] t ∪ t'
-/
theorem ae_eq_set_union {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') :
    (s ∪ s' : Set α) =ᵐ[μ] (t ∪ t' : Set α) :=
  h.union h'
/-
**MeasureTheory.ae_eq_set_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_set_sdiff {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') : s \ s
' =ᵐ[μ] t \ t'
参数：h : s =ᵐ[μ] t；h' : s' =ᵐ[μ] t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.diff`：∀ {α : Type u} {s t s' t' : Set α} {l : Filter
 α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s \ s' =ᶠ[l] t \ t'
-/
theorem ae_eq_set_sdiff {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') :
    s \ s' =ᵐ[μ] t \ t' :=
  h.diff h'

@[deprecated (since := "2026-06-03")] alias ae_eq_set_diff := ae_eq_set_sdiff

open scoped symmDiff in
/-
**MeasureTheory.ae_eq_set_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_set_symmDiff {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') : s 
∆ s' =ᵐ[μ] t ∆ t'
参数：h : s =ᵐ[μ] t；h' : s' =ᵐ[μ] t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.symmDiff`：∀ {α : Type u} {s t s' t' : Set α} {l : Fi
lter α}, s =ᶠ[l] t → s' =ᶠ[l] t' → symmDiff s s' =ᶠ[l] symmDiff t t'
-/
theorem ae_eq_set_symmDiff {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') :
    s ∆ s' =ᵐ[μ] t ∆ t' :=
  h.symmDiff h'

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.union_ae_eq_univ_of_ae_eq_univ_left** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：union_ae_eq_univ_of_ae_eq_univ_left (h : s =ᵐ[μ] univ) : (s union t : Set 
α) =ᵐ[μ] univ
参数：h : s =ᵐ[μ] univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.ae_eq_set_union`：ae_eq_set_union {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s union s' : Set α) =ᵐ[μ] (t union t' : Set α)
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_union`：univ_union (s : Set α) : univ union s = univ
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem union_ae_eq_univ_of_ae_eq_univ_left (h : s =ᵐ[μ] univ) : (s ∪ t : Set α) =ᵐ[μ] univ :=
  (ae_eq_set_union h (ae_eq_refl t)).trans <| by rw [univ_union]
/-
**MeasureTheory.union_ae_eq_univ_of_ae_eq_univ_right** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：union_ae_eq_univ_of_ae_eq_univ_right (h : t =ᵐ[μ] univ) : (s union t : Set
 α) =ᵐ[μ] univ
参数：h : t =ᵐ[μ] univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_univ`：union_univ (s : Set α) : s union univ = univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.ae_eq_set_union`：ae_eq_set_union {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s union s' : Set α) =ᵐ[μ] (t union t' : Set α)
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
-/
theorem union_ae_eq_univ_of_ae_eq_univ_right (h : t =ᵐ[μ] univ) : (s ∪ t : Set α) =ᵐ[μ] univ := by
  convert! ae_eq_set_union (ae_eq_refl s) h
  rw [union_univ]
/-
**MeasureTheory.union_ae_eq_right_of_ae_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：union_ae_eq_right_of_ae_eq_empty (h : s =ᵐ[μ] (∅ : Set α)) : (s union t : 
Set α) =ᵐ[μ] t
参数：h : s =ᵐ[μ] (∅ : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.ae_eq_set_union`：ae_eq_set_union {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s union s' : Set α) =ᵐ[μ] (t union t' : Set α)
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
-/
theorem union_ae_eq_right_of_ae_eq_empty (h : s =ᵐ[μ] (∅ : Set α)) : (s ∪ t : Set α) =ᵐ[μ] t := by
  convert! ae_eq_set_union h (ae_eq_refl t)
  rw [empty_union]
/-
**MeasureTheory.union_ae_eq_left_of_ae_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：union_ae_eq_left_of_ae_eq_empty (h : t =ᵐ[μ] (∅ : Set α)) : (s union t : S
et α) =ᵐ[μ] s
参数：h : t =ᵐ[μ] (∅ : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.ae_eq_set_union`：ae_eq_set_union {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s union s' : Set α) =ᵐ[μ] (t union t' : Set α)
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
-/
theorem union_ae_eq_left_of_ae_eq_empty (h : t =ᵐ[μ] (∅ : Set α)) : (s ∪ t : Set α) =ᵐ[μ] s := by
  convert! ae_eq_set_union (ae_eq_refl s) h
  rw [union_empty]
/-
**MeasureTheory.inter_ae_eq_right_of_ae_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：inter_ae_eq_right_of_ae_eq_univ (h : s =ᵐ[μ] univ) : (s inter t : Set α) =
ᵐ[μ] t
参数：h : s =ᵐ[μ] univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.ae_eq_set_inter`：ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s inter s' : Set α) =ᵐ[μ] (t inter t' : Set α)
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
-/
theorem inter_ae_eq_right_of_ae_eq_univ (h : s =ᵐ[μ] univ) : (s ∩ t : Set α) =ᵐ[μ] t := by
  convert! ae_eq_set_inter h (ae_eq_refl t)
  rw [univ_inter]
/-
**MeasureTheory.inter_ae_eq_left_of_ae_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：inter_ae_eq_left_of_ae_eq_univ (h : t =ᵐ[μ] univ) : (s inter t : Set α) =ᵐ
[μ] s
参数：h : t =ᵐ[μ] univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.ae_eq_set_inter`：ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s inter s' : Set α) =ᵐ[μ] (t inter t' : Set α)
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
-/
theorem inter_ae_eq_left_of_ae_eq_univ (h : t =ᵐ[μ] univ) : (s ∩ t : Set α) =ᵐ[μ] s := by
  convert! ae_eq_set_inter (ae_eq_refl s) h
  rw [inter_univ]
/-
**MeasureTheory.inter_ae_eq_empty_of_ae_eq_empty_left** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：inter_ae_eq_empty_of_ae_eq_empty_left (h : s =ᵐ[μ] (∅ : Set α)) : (s inter
 t : Set α) =ᵐ[μ] (∅ : Set α)
参数：h : s =ᵐ[μ] (∅ : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.ae_eq_set_inter`：ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s inter s' : Set α) =ᵐ[μ] (t inter t' : Set α)
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
-/
theorem inter_ae_eq_empty_of_ae_eq_empty_left (h : s =ᵐ[μ] (∅ : Set α)) :
    (s ∩ t : Set α) =ᵐ[μ] (∅ : Set α) := by
  convert! ae_eq_set_inter h (ae_eq_refl t)
  rw [empty_inter]
/-
**MeasureTheory.inter_ae_eq_empty_of_ae_eq_empty_right** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：inter_ae_eq_empty_of_ae_eq_empty_right (h : t =ᵐ[μ] (∅ : Set α)) : (s inte
r t : Set α) =ᵐ[μ] (∅ : Set α)
参数：h : t =ᵐ[μ] (∅ : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.ae_eq_set_inter`：ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s inter s' : Set α) =ᵐ[μ] (t inter t' : Set α)
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
-/
theorem inter_ae_eq_empty_of_ae_eq_empty_right (h : t =ᵐ[μ] (∅ : Set α)) :
    (s ∩ t : Set α) =ᵐ[μ] (∅ : Set α) := by
  convert! ae_eq_set_inter (ae_eq_refl s) h
  rw [inter_empty]
/-
**MeasureTheory.ae_eq_set_biInter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_set_biInter {s : Set β} (hs : s.Countable) {t t' : β -> Set α} (h : 
forall b in s, t b =ᵐ[μ] t' b) : (⋂ b in s, t b : Set α) =ᵐ[μ] (⋂ b in s, t' b :
 Set α)
参数：hs : s.Countable；h : forall b in s, t b =ᵐ[μ] t' b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.countable_bInter`：∀ {α : Type u_2} {l : Filter α} [C
ountableInterFilter l] {ι : Type u_4} {S : Set ι},   S.Countable →     ∀ {s t : 
(i : ι) → i ∈ S → Set α}, …
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
-/
theorem ae_eq_set_biInter {s : Set β} (hs : s.Countable) {t t' : β → Set α}
    (h : ∀ b ∈ s, t b =ᵐ[μ] t' b) :
    (⋂ b ∈ s, t b : Set α) =ᵐ[μ] (⋂ b ∈ s, t' b : Set α) :=
  .countable_bInter hs h
/-
**MeasureTheory.ae_eq_set_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_set_biUnion {s : Set β} (hs : s.Countable) {t t' : β -> Set α} (h : 
forall b in s, t b =ᵐ[μ] t' b) : (⋃ b in s, t b : Set α) =ᵐ[μ] (⋃ b in s, t' b :
 Set α)
参数：hs : s.Countable；h : forall b in s, t b =ᵐ[μ] t' b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.countable_bUnion`：∀ {α : Type u_2} {l : Filter α} [C
ountableInterFilter l] {ι : Type u_4} {S : Set ι},   S.Countable →     ∀ {s t : 
(i : ι) → i ∈ S → Set α}, …
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
-/
theorem ae_eq_set_biUnion {s : Set β} (hs : s.Countable) {t t' : β → Set α}
    (h : ∀ b ∈ s, t b =ᵐ[μ] t' b) :
    (⋃ b ∈ s, t b : Set α) =ᵐ[μ] (⋃ b ∈ s, t' b : Set α) :=
  .countable_bUnion hs h

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**MeasureTheory._root_.Set.mulIndicator_ae_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.mulIndicator_ae_eq_one {M : Type*} [One M] {f : α → M} {s : Set α} :
    s.mulIndicator f =ᵐ[μ] 1 ↔ μ (s ∩ f.mulSupport) = 0 := by
  simp [EventuallyEq, eventually_iff, ae, compl_ofPred]; rfl

/-- If `s ⊆ t` modulo a set of measure `0`, then `μ s ≤ μ t`. -/
@[mono]
/-
**MeasureTheory.measure_mono_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_mono_ae (H : s <=ᵐ[μ] t) : μ s <= μ t
参数：H : s <=ᵐ[μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_le_set`：ae_le_set : s <=ᵐ[μ] t ↔ μ (s \ t) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
If `s ⊆ t` modulo a set of measure `0`, then `μ s ≤ μ t`.
-/
theorem measure_mono_ae (H : s ≤ᵐ[μ] t) : μ s ≤ μ t :=
  calc
    μ s ≤ μ (s ∪ t) := measure_mono subset_union_left
    _ = μ (t ∪ s \ t) := by rw [union_sdiff_self, Set.union_comm]
    _ ≤ μ t + μ (s \ t) := measure_union_le _ _
    _ = μ t := by rw [ae_le_set.1 H, add_zero]

alias _root_.Filter.EventuallyLE.measure_le := measure_mono_ae

/-- If two sets are equal modulo a set of measure zero, then `μ s = μ t`. -/
/-
**MeasureTheory.measure_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
参数：H : s =ᵐ[μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.EventuallyLE.measure_le`：∀ {α : Type u_1} {F : Type u_3} [inst : 
FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   {μ :
 F} {s t : Set α}, s…
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
If two sets are equal modulo a set of measure zero, then `μ s = μ t`.
-/
theorem measure_congr (H : s =ᵐ[μ] t) : μ s = μ t :=
  le_antisymm H.le.measure_le H.symm.le.measure_le

alias _root_.Filter.EventuallyEq.measure_eq := measure_congr
/-
**MeasureTheory.measure_mono_null_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_mono_null_ae (H : s <=ᵐ[μ] t) (ht : μ t = 0) : μ s = 0
参数：H : s <=ᵐ[μ] t；ht : μ t = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Filter.EventuallyLE.measure_le`：∀ {α : Type u_1} {F : Type u_3} [inst : 
FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   {μ :
 F} {s t : Set α}, s…
-/
theorem measure_mono_null_ae (H : s ≤ᵐ[μ] t) (ht : μ t = 0) : μ s = 0 :=
  nonpos_iff_eq_zero.1 <| ht ▸ H.measure_le

end MeasureTheory

