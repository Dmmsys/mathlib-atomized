/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Martingale.Basic

/-!
# Centering lemma for stochastic processes

Any `ℕ`-indexed stochastic process which is strongly adapted and integrable can be written as the
sum of a martingale and a predictable process. This result is also known as
**Doob's decomposition theorem**. From a process `f`, a filtration `ℱ` and a measure `μ`, we define
two processes `martingalePart f ℱ μ` and `predictablePart f ℱ μ`.

## Main definitions

* `MeasureTheory.predictablePart f ℱ μ`: a predictable process such that
  `f = predictablePart f ℱ μ + martingalePart f ℱ μ`
* `MeasureTheory.martingalePart f ℱ μ`: a martingale such that
  `f = predictablePart f ℱ μ + martingalePart f ℱ μ`

## Main statements

* `MeasureTheory.stronglyAdapted_predictablePart`: `(fun n => predictablePart f ℱ μ (n+1))`
  is strongly adapted.
  That is, `predictablePart` is predictable.
* `MeasureTheory.martingale_martingalePart`: `martingalePart f ℱ μ` is a martingale.

-/

@[expose] public section


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {f g : ℕ → Ω → E} {ℱ : Filtration ℕ m0}

/-- Any `ℕ`-indexed stochastic process can be written as the sum of a martingale and a predictable
process. This is the predictable process. See `martingalePart` for the martingale. -/
/-
**MeasureTheory.predictablePart** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：predictablePart {m0 : MeasurableSpace Ω} (f : Nat -> Ω -> E) (ℱ : Filtrati
on Nat m0) (μ : Measure Ω) : Nat -> Ω -> E
参数：f : Nat -> Ω -> E；ℱ : Filtration Nat m0；μ : Measure Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any `ℕ`-indexed stochastic process can be written as the sum of a martingale and
 a predictable
process. This is the predictable process. See `martingalePart` for the martingal
e.
-/
noncomputable def predictablePart {m0 : MeasurableSpace Ω} (f : ℕ → Ω → E) (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) : ℕ → Ω → E := fun n => ∑ i ∈ Finset.range n, μ[f (i + 1) - f i | ℱ i]

@[simp]
/-
**MeasureTheory.predictablePart_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：predictablePart_zero : predictablePart f ℱ μ 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem predictablePart_zero : predictablePart f ℱ μ 0 = 0 := by
  simp_rw [predictablePart, Finset.range_zero, Finset.sum_empty]
/-
**MeasureTheory.predictablePart_add_one** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：predictablePart_add_one (n : Nat) : predictablePart f ℱ μ (n + 1) = predic
tablePart f ℱ μ n + μ[f (n + 1) - f n | ℱ n]
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_add`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ →
 M) (n m : ℕ),   ∑ x ∈ Finset.range (n + m), f x = ∑ x ∈ Finset.range n, f x + ∑
 x ∈ Finse…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma predictablePart_add_one (n : ℕ) :
    predictablePart f ℱ μ (n + 1) =
      predictablePart f ℱ μ n + μ[f (n + 1) - f n | ℱ n] := by
  simp [predictablePart, Finset.sum_range_add]
/-
**MeasureTheory.predictablePart_smul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：predictablePart_smul [CompleteSpace E] (c : Real) (n : Nat) : predictableP
art (c • f) ℱ μ n =ᵐ[μ] c • predictablePart f ℱ μ n
参数：c : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eventuallyEq_sum`：∀ {ι : Type u_1} {X : Type u_6} {M : Type u_7} [inst :
 AddCommMonoid M] {s : Finset ι} {l : Filter X} {f g : ι → X → M},   (∀ i ∈ s, f
 i =ᶠ[…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma predictablePart_smul [CompleteSpace E] (c : ℝ) (n : ℕ) :
    predictablePart (c • f) ℱ μ n =ᵐ[μ] c • predictablePart f ℱ μ n := by
  simp only [predictablePart, Finset.smul_sum]
  refine eventuallyEq_sum fun i hi => ?_
  simp [← smul_sub, condExp_smul]
/-
**MeasureTheory.predictablePart_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：predictablePart_add [CompleteSpace E] (hfint : forall n, Integrable (f n) 
μ) (hgint : forall n, Integrable (g n) μ) (n : Nat) : predictablePart (f + g) ℱ 
μ n =ᵐ[μ] predictablePart f ℱ μ n + predictablePart g ℱ μ n
参数：hfint : forall n, Integrable (f n) μ；hgint : forall n, Integrable (g n) μ；n :
 Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eventuallyEq_sum`：∀ {ι : Type u_1} {X : Type u_6} {M : Type u_7} [inst :
 AddCommMonoid M] {s : Finset ι} {l : Filter X} {f g : ι → X → M},   (∀ i ∈ s, f
 i =ᶠ[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Abel.unfold_sub`：unfold_sub {α} [SubtractionMonoid α] (a 
b c : α) (h : a + -b = c) : a - b = c
· 使用引理 `Mathlib.Tactic.Abel.subst_into_addg`：subst_into_addg {α} [AddCommGroup α
] (l r tl tr t) (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r 
= t
· 使用定理 `Mathlib.Tactic.Abel.term_atomg`：term_atomg {α} [AddCommGroup α] (x : α) 
: x = termg 1 x 0
· 使用定理 `Mathlib.Tactic.Abel.term_add_constg`：term_add_constg {α} [AddCommGroup α
] (n x a k a') (h : a + k = a') : @termg α _ n x a + k = termg n x a'
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `Mathlib.Tactic.Abel.subst_into_negg`：subst_into_negg {α} [AddCommGroup α
] (a ta t : α) (pra : a = ta) (prt : -ta = t) : -a = t
· 使用定理 `Mathlib.Tactic.Abel.term_neg`：term_neg {α} [AddCommGroup α] (n x a n' a'
) (h₁ : -n = n') (h₂ : -a = a') : -@termg α _ n x a = termg n' x a'
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Mathlib.Tactic.Abel.termg_eq`：termg_eq {α : Type*} [AddCommGroup α] (n :
 Int) (x a : α) : termg n x a = n • x + a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `Mathlib.Tactic.Abel.const_add_termg`：const_add_termg {α} [AddCommGroup α
] (k n x a a') (h : k + a = a') : k + @termg α _ n x a = termg n x a'
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_add`：condExp_add (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m]
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
-/
lemma predictablePart_add [CompleteSpace E] (hfint : ∀ n, Integrable (f n) μ)
    (hgint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    predictablePart (f + g) ℱ μ n =ᵐ[μ] predictablePart f ℱ μ n + predictablePart g ℱ μ n := by
  simp only [predictablePart, ← Finset.sum_add_distrib]
  refine eventuallyEq_sum fun i hi => ?_
  calc
  _ =ᵐ[μ] μ[(f (i + 1) - f i) + (g (i + 1) - g i) | ℱ i] := by simp; abel_nf; rfl
  _ =ᵐ[μ] _ := by apply condExp_add ((hfint (i + 1)).sub (hfint i)) ((hgint (i + 1)).sub (hgint i))
/-
**MeasureTheory.Martingale.predictablePart_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Martingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheor
y.Measure Ω} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] {f : ℕ →
 Ω → E} {ℱ : MeasureTheory.Filtration ℕ m0} [CompleteSpace E],   MeasureTheory.M
artingale f ℱ μ → ∀ (n : ℕ), MeasureTheory.predictablePart f ℱ μ n =ᵐ[μ] 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.predictablePart.eq_1`：∀ {Ω : Type u_1} {E : Type u_2} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {m0 : MeasurableSpace Ω}   
(f : ℕ → Ω → E) (ℱ : Mea…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eventuallyEq_sum`：∀ {ι : Type u_1} {X : Type u_6} {M : Type u_7} [inst :
 AddCommMonoid M] {s : Finset ι} {l : Filter X} {f g : ι → X → M},   (∀ i ∈ s, f
 i =ᶠ[…
· 使用定理 `MeasureTheory.condExp_sub`：condExp_sub (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m]
· 使用定理 `MeasureTheory.Martingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} {ι 
: Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory.Me
asure Ω} [inst_1 : Normed…
· 使用定理 `Filter.EventuallyEq.sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f - f' =ᶠ[l] g - g'
· 使用定理 `MeasureTheory.Martingale.condExp_ae_eq`：condExp_ae_eq (hf : Martingale f
 ℱ μ) {i j : ι} (hij : i <= j) : μ[f j | ℱ i] =ᵐ[μ] f i
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma Martingale.predictablePart_eq_zero [CompleteSpace E] (hf : Martingale f ℱ μ) (n : ℕ) :
    predictablePart f ℱ μ n =ᵐ[μ] 0 := by
  rw [predictablePart, ← Finset.sum_const_zero (s := Finset.range n)]
  refine eventuallyEq_sum fun i hi => ?_
  calc
  _ =ᵐ[μ] μ[f (i + 1) | ℱ i] - μ[f i | ℱ i] := by
    simp [condExp_sub (hf.integrable (i + 1)) (hf.integrable i) (ℱ i)]
  _ =ᵐ[μ] f i - f i := (hf.condExp_ae_eq (Nat.le_succ i)).sub (hf.condExp_ae_eq le_rfl)
  _ =ᵐ[μ] 0 := by simp
/-
**MeasureTheory.Submartingale.monotone_predictablePart** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheor
y.Measure Ω} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] {f : ℕ →
 Ω → E} {ℱ : MeasureTheory.Filtration ℕ m0} [CompleteSpace E]   [inst_3 : Partia
lOrder E] [IsOrderedAddMonoid E],   MeasureTheory.Submartingale f ℱ μ → ∀ᵐ (ω : 
Ω) ∂μ, Monotone fun x => MeasureTheory.predictablePart f ℱ μ x ω
参数：ω : Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.Submartingale.condExp_sub_nonneg`：∀ {Ω : Type u_1} {E : Ty
pe u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : Measu
reTheory.Measure Ω} [inst_1 : Normed…
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.predictablePart_add_one`：predictablePart_add_one (n : Nat)
 : predictablePart f ℱ μ (n + 1) = predictablePart f ℱ μ n + μ[f (n + 1) - f n |
 ℱ n]
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `ge_imp_ge_of_le_of_le`：ge_imp_ge_of_le_of_le (h₁ : a <= c) (h₂ : d <= b)
 : a >= b -> c >= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma Submartingale.monotone_predictablePart
    [CompleteSpace E] [PartialOrder E] [IsOrderedAddMonoid E]
    (hf : Submartingale f ℱ μ) :
    ∀ᵐ ω ∂μ, Monotone (predictablePart f ℱ μ · ω) := by
  have := ae_all_iff.2 <| fun n : ℕ ↦ hf.condExp_sub_nonneg n.le_succ
  filter_upwards [this] with ω h
  simp only [Pi.zero_apply, Nat.succ_eq_add_one, ← ge_iff_le] at h
  refine monotone_nat_of_le_succ fun n ↦ (?_ : _ ≥ _)
  grw [predictablePart_add_one, Pi.add_apply, h n, add_zero]
/-
**MeasureTheory.Submartingale.predictablePart_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheor
y.Measure Ω} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] {f : ℕ →
 Ω → E} {ℱ : MeasureTheory.Filtration ℕ m0} [CompleteSpace E]   [inst_3 : Partia
lOrder E] [IsOrderedAddMonoid E],   MeasureTheory.Submartingale f ℱ μ → ∀ᵐ (ω : 
Ω) ∂μ, ∀ (n : ℕ), 0 ≤ MeasureTheory.predictablePart f ℱ μ n ω
参数：ω : Ω；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Submartingale.monotone_predictablePart`：∀ {Ω : Type u_1} {
E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : Nor
medAddCommGroup E]   [inst_1 : NormedSpace…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.predictablePart_zero`：predictablePart_zero : predictablePa
rt f ℱ μ 0 = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
lemma Submartingale.predictablePart_nonneg
    [CompleteSpace E] [PartialOrder E] [IsOrderedAddMonoid E]
    (hf : Submartingale f ℱ μ) :
    ∀ᵐ ω ∂μ, ∀ n, 0 ≤ predictablePart f ℱ μ n ω := by
  filter_upwards [hf.monotone_predictablePart] with ω hω n
  simpa [predictablePart_zero] using hω (Nat.zero_le n)
/-
**MeasureTheory.IsStronglyPredictable.predictablePart_eq** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.IsStronglyPredictable`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheor
y.Measure Ω} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] {f : ℕ →
 Ω → E} {ℱ : MeasureTheory.Filtration ℕ m0}   [MeasureTheory.SigmaFiniteFiltrati
on μ ℱ],   MeasureTheory.IsStronglyPredictable ℱ f →     (∀ (n : ℕ), MeasureTheo
ry.Integrable (f n) μ) → ∀ (n : ℕ), MeasureTheory.predictablePart f ℱ μ n =ᵐ[μ] 
f n - f 0
参数：∀ (n : ℕ), MeasureTheory.Integrable (f n) μ；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eventuallyEq_sum`：∀ {ι : Type u_1} {X : Type u_6} {M : Type u_7} [inst :
 AddCommMonoid M] {s : Finset ι} {l : Filter X} {f g : ι → X → M},   (∀ i ∈ s, f
 i =ᶠ[…
· 使用定理 `Eq.eventuallyEq`：∀ {α : Type u} {β : Type v} {l : Filter α} {f g : α → β
}, f = g → f =ᶠ[l] g
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.StronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Sub β
]   [ContinuousSub β],   M…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MeasureTheory.IsStronglyPredictable.measurable_add_one`：measurable_add_o
ne {𝓕 : Filtration Nat m} {u : Nat -> Ω -> E} (h𝓕 : IsStronglyPredictable 𝓕 u) (
n : Nat) : StronglyMeasurable[𝓕 n] (u (n + 1…
· 使用引理 `MeasureTheory.IsStronglyPredictable.stronglyAdapted`：stronglyAdapted {𝓕 
: Filtration ι m} {u : ι -> Ω -> E} (h𝓕 : IsStronglyPredictable 𝓕 u) : StronglyA
dapted 𝓕 u
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
-/
lemma IsStronglyPredictable.predictablePart_eq
    [SigmaFiniteFiltration μ ℱ] (hf : IsStronglyPredictable ℱ f)
    (hfint : ∀ n, Integrable (f n) μ) (n : ℕ) :
    predictablePart f ℱ μ n =ᵐ[μ] f n - f 0 := by
  simp only [predictablePart, ← Finset.sum_range_sub]
  exact eventuallyEq_sum fun i hi => (condExp_of_stronglyMeasurable (ℱ.le i)
    ((hf.measurable_add_one i).sub (hf.stronglyAdapted i))
    ((hfint (i + 1)).sub (hfint i))).eventuallyEq
/-
**MeasureTheory.stronglyAdapted_predictablePart** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：stronglyAdapted_predictablePart : StronglyAdapted ℱ fun n => predictablePa
rt f ℱ μ (n + 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.stronglyMeasurable_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : A
ddCommMonoid M] [inst_1 : TopologicalSpace M] [ContinuousAdd M]   {m : Measurabl
eSpace α} {ι : Type…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range_succ_iff`：mem_range_succ_iff {a b : Nat} : a in range b
.succ ↔ a <= b
-/
theorem stronglyAdapted_predictablePart :
    StronglyAdapted ℱ fun n => predictablePart f ℱ μ (n + 1) :=
  fun _ => Finset.stronglyMeasurable_sum _ fun _ hin =>
    stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range_succ_iff.mp hin))
/-
**MeasureTheory.isPredictable_predictablePart** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：isPredictable_predictablePart [SecondCountableTopology E] [MeasurableSpace
 E] [BorelSpace E] : IsStronglyPredictable ℱ (predictablePart f ℱ μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.IsStronglyPredictable.of_measurable_add_one`：of_measurable
_add_one {𝓕 : Filtration Nat m} {u : Nat -> Ω -> E} (h₀ : StronglyMeasurable[𝓕 0
] (u 0)) (h : forall n, StronglyMeasurable[𝓕 n]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.predictablePart_zero`：predictablePart_zero : predictablePa
rt f ℱ μ 0 = 0
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `measurable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace
 α] [inst_1 : MeasurableSpace β] [inst_2 : Zero α], Measurable 0
· 使用定理 `MeasureTheory.stronglyAdapted_predictablePart`：stronglyAdapted_predictab
lePart : StronglyAdapted ℱ fun n => predictablePart f ℱ μ (n + 1)
-/
lemma isPredictable_predictablePart [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] :
    IsStronglyPredictable ℱ (predictablePart f ℱ μ) :=
  IsStronglyPredictable.of_measurable_add_one (by measurability)
    fun n ↦ (stronglyAdapted_predictablePart n)
/-
**MeasureTheory.stronglyAdapted_predictablePart'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：stronglyAdapted_predictablePart' : StronglyAdapted ℱ fun n => predictableP
art f ℱ μ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.stronglyMeasurable_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : A
ddCommMonoid M] [inst_1 : TopologicalSpace M] [ContinuousAdd M]   {m : Measurabl
eSpace α} {ι : Type…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `Finset.mem_range_le`：mem_range_le {n x : Nat} (hx : x in range n) : x <=
 n
-/
theorem stronglyAdapted_predictablePart' : StronglyAdapted ℱ fun n => predictablePart f ℱ μ n :=
  fun _ => Finset.stronglyMeasurable_sum _ fun _ hin =>
    stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range_le hin))

/-- Any `ℕ`-indexed stochastic process can be written as the sum of a martingale and a predictable
process. This is the martingale. See `predictablePart` for the predictable process. -/
/-
**MeasureTheory.martingalePart** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：martingalePart {m0 : MeasurableSpace Ω} (f : Nat -> Ω -> E) (ℱ : Filtratio
n Nat m0) (μ : Measure Ω) : Nat -> Ω -> E
参数：f : Nat -> Ω -> E；ℱ : Filtration Nat m0；μ : Measure Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any `ℕ`-indexed stochastic process can be written as the sum of a martingale and
 a predictable
process. This is the martingale. See `predictablePart` for the predictable proce
ss.
-/
noncomputable def martingalePart {m0 : MeasurableSpace Ω} (f : ℕ → Ω → E) (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) : ℕ → Ω → E := fun n => f n - predictablePart f ℱ μ n

@[simp]
/-
**MeasureTheory.martingalePart_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：martingalePart_zero : martingalePart f ℱ μ 0 = f 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.predictablePart_zero`：predictablePart_zero : predictablePa
rt f ℱ μ 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma martingalePart_zero : martingalePart f ℱ μ 0 = f 0 := by
  simp [martingalePart]
/-
**MeasureTheory.martingalePart_smul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：martingalePart_smul [CompleteSpace E] (c : Real) (n : Nat) : martingalePar
t (c • f) ℱ μ n =ᵐ[μ] c • martingalePart f ℱ μ n
参数：c : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.predictablePart_smul`：predictablePart_smul [CompleteSpace 
E] (c : Real) (n : Nat) : predictablePart (c • f) ℱ μ n =ᵐ[μ] c • predictablePar
t f ℱ μ n
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
-/
lemma martingalePart_smul [CompleteSpace E] (c : ℝ) (n : ℕ) :
    martingalePart (c • f) ℱ μ n =ᵐ[μ] c • martingalePart f ℱ μ n := by
  filter_upwards [predictablePart_smul (f := f) c n] with ω hω
  simpa [martingalePart, smul_sub]
/-
**MeasureTheory.martingalePart_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：martingalePart_add [CompleteSpace E] (hfint : forall n, Integrable (f n) μ
) (hgint : forall n, Integrable (g n) μ) (n : Nat) : martingalePart (f + g) ℱ μ 
n =ᵐ[μ] martingalePart f ℱ μ n + martingalePart g ℱ μ n
参数：hfint : forall n, Integrable (f n) μ；hgint : forall n, Integrable (g n) μ；n :
 Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.predictablePart_add`：predictablePart_add [CompleteSpace E]
 (hfint : forall n, Integrable (f n) μ) (hgint : forall n, Integrable (g n) μ) (
n : Nat) : predictableP…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Probability.Martingale.Centering.0.MeasureTheory.martin
galePart_add._abel_1_2`：∀ {Ω : Type u_2} {E : Type u_1} {m0 : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} [inst : NormedAddCommGroup E]   [inst_1 : NormedS
pace…
-/
lemma martingalePart_add [CompleteSpace E] (hfint : ∀ n, Integrable (f n) μ)
    (hgint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    martingalePart (f + g) ℱ μ n =ᵐ[μ] martingalePart f ℱ μ n + martingalePart g ℱ μ n := by
  filter_upwards [predictablePart_add (ℱ := ℱ) hfint hgint n] with ω hω
  simp_all [martingalePart]
  abel
/-
**MeasureTheory.Martingale.martingalePart_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Martingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheor
y.Measure Ω} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] {f : ℕ →
 Ω → E} {ℱ : MeasureTheory.Filtration ℕ m0} [CompleteSpace E],   MeasureTheory.M
artingale f ℱ μ → ∀ (n : ℕ), MeasureTheory.martingalePart f ℱ μ n =ᵐ[μ] f n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Martingale.predictablePart_eq_zero`：∀ {Ω : Type u_1} {E : 
Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : NormedA
ddCommGroup E]   [inst_1 : NormedSpace…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Martingale.martingalePart_eq [CompleteSpace E] (hf : Martingale f ℱ μ) (n : ℕ) :
    martingalePart f ℱ μ n =ᵐ[μ] f n := by
  filter_upwards [hf.predictablePart_eq_zero n] with ω hω
  simp [martingalePart, hω]
/-
**MeasureTheory.IsPredictable.martingalePart_eq** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.IsPredictable`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheor
y.Measure Ω} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] {f : ℕ →
 Ω → E} {ℱ : MeasureTheory.Filtration ℕ m0}   [MeasureTheory.SigmaFiniteFiltrati
on μ ℱ],   MeasureTheory.IsStronglyPredictable ℱ f →     (∀ (n : ℕ), MeasureTheo
ry.Integrable (f n) μ) → ∀ (n : ℕ), MeasureTheory.martingalePart f ℱ μ n =ᵐ[μ] f
 0
参数：∀ (n : ℕ), MeasureTheory.Integrable (f n) μ；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.IsStronglyPredictable.predictablePart_eq`：∀ {Ω : Type u_1}
 {E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : N
ormedAddCommGroup E]   [inst_1 : NormedSpace…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `add_neg_cancel_comm_assoc`：∀ {G : Type u_1} [inst : AddCommGroup G] (a b
 : G), a + (b + -a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsPredictable.martingalePart_eq [SigmaFiniteFiltration μ ℱ] (hf : IsStronglyPredictable ℱ f)
    (hfint : ∀ n, Integrable (f n) μ) (n : ℕ) :
    martingalePart f ℱ μ n =ᵐ[μ] f 0 := by
  filter_upwards [hf.predictablePart_eq (μ := μ) hfint n] with ω hω
  simp [martingalePart, hω, sub_eq_add_neg]
/-
**MeasureTheory.martingalePart_add_predictablePart** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：martingalePart_add_predictablePart (ℱ : Filtration Nat m0) (μ : Measure Ω)
 (f : Nat -> Ω -> E) : martingalePart f ℱ μ + predictablePart f ℱ μ = f
参数：ℱ : Filtration Nat m0；μ : Measure Ω；f : Nat -> Ω -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem martingalePart_add_predictablePart (ℱ : Filtration ℕ m0) (μ : Measure Ω) (f : ℕ → Ω → E) :
    martingalePart f ℱ μ + predictablePart f ℱ μ = f :=
  sub_add_cancel _ _
/-
**MeasureTheory.martingalePart_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：martingalePart_eq_sum : martingalePart f ℱ μ = fun n => f 0 + ∑ i in Finse
t.range n, (f (i + 1) - f i - μ[f (i + 1) - f i | ℱ i])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.eq_sum_range_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (f : ℕ
 → G) (n : ℕ), f n = f 0 + ∑ i ∈ Finset.range n, (f (i + 1) - f i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub`：∀ {G : Type u_3} [inst : SubNegMonoid G] (a b c : G), a + (b - 
c) = a + b - c
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
-/
theorem martingalePart_eq_sum : martingalePart f ℱ μ = fun n =>
    f 0 + ∑ i ∈ Finset.range n, (f (i + 1) - f i - μ[f (i + 1) - f i | ℱ i]) := by
  unfold martingalePart predictablePart
  ext1 n
  rw [Finset.eq_sum_range_sub f n, ← add_sub, ← Finset.sum_sub_distrib]
/-
**MeasureTheory.stronglyAdapted_martingalePart** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：stronglyAdapted_martingalePart (hf : StronglyAdapted ℱ f) : StronglyAdapte
d ℱ (martingalePart f ℱ μ)
参数：hf : StronglyAdapted ℱ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyAdapted.sub`：∀ {Ω : Type u_1} {ι : Type u_2} {m : 
MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   {β :
 ι → Type u_3} [inst_1 …
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.stronglyAdapted_predictablePart'`：stronglyAdapted_predicta
blePart' : StronglyAdapted ℱ fun n => predictablePart f ℱ μ n
-/
theorem stronglyAdapted_martingalePart (hf : StronglyAdapted ℱ f) :
  StronglyAdapted ℱ (martingalePart f ℱ μ) := hf.sub stronglyAdapted_predictablePart'
/-
**MeasureTheory.integrable_martingalePart** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integrable_martingalePart [CompleteSpace E] (hf_int : forall n, Integrable
 (f n) μ) (n : Nat) : Integrable (martingalePart f ℱ μ n) μ
参数：hf_int : forall n, Integrable (f n) μ；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.martingalePart_eq_sum`：martingalePart_eq_sum : martingaleP
art f ℱ μ = fun n => f 0 + ∑ i in Finset.range n, (f (i + 1) - f i - μ[f (i + 1)
 - f i | ℱ i])
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.integrable_finsetSum'`：integrable_finsetSum' {ι} (s : Fins
et ι) {f : ι -> α -> ε'} (hf : forall i in s, Integrable (f i) μ) : Integrable (
∑ i in s, f i) μ
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
-/
theorem integrable_martingalePart [CompleteSpace E] (hf_int : ∀ n, Integrable (f n) μ) (n : ℕ) :
    Integrable (martingalePart f ℱ μ n) μ := by
  rw [martingalePart_eq_sum]
  fun_prop
/-
**MeasureTheory.martingale_martingalePart** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：martingale_martingalePart [CompleteSpace E] (hf : StronglyAdapted ℱ f) (hf
_int : forall n, Integrable (f n) μ) [SigmaFiniteFiltration μ ℱ] : Martingale (m
artingalePart f ℱ μ) ℱ μ
参数：hf : StronglyAdapted ℱ f；hf_int : forall n, Integrable (f n) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.stronglyAdapted_martingalePart`：stronglyAdapted_martingale
Part (hf : StronglyAdapted ℱ f) : StronglyAdapted ℱ (martingalePart f ℱ μ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.martingalePart_eq_sum`：martingalePart_eq_sum : martingaleP
art f ℱ μ = fun n => f 0 + ∑ i in Finset.range n, (f (i + 1) - f i - μ[f (i + 1)
 - f i | ℱ i])
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_add`：condExp_add (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m]
· 使用定理 `MeasureTheory.integrable_finsetSum'`：integrable_finsetSum' {ι} (s : Fins
et ι) {f : ι -> α -> ε'} (hf : forall i in s, Integrable (f i) μ) : Integrable (
∑ i in s, f i) μ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_finsetSum`：condExp_finsetSum {ι : Type*} {s : Fins
et ι} {f : ι -> α -> E} (hf : forall i in s, Integrable (f i) μ) (m : Measurable
Space α) : μ[∑ i in s…
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `eventuallyEq_sum`：∀ {ι : Type u_1} {X : Type u_6} {M : Type u_7} [inst :
 AddCommMonoid M] {s : Finset ι} {l : Filter X} {f g : ι → X → M},   (∀ i ∈ s, f
 i =ᶠ[…
· 使用定理 `MeasureTheory.condExp_sub`：condExp_sub (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m]
· 使用定理 `MeasureTheory.condExp_condExp_of_le`：condExp_condExp_of_le {m₁ m₂ m₀ : M
easurableSpace α} {μ : Measure α} (hm₁₂ : m₁ <= m₂) (hm₂ : m₂ <= m₀) [SigmaFinit
e (μ.trim hm₂)] : μ[μ[f |…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Filter.EventuallyEq.sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f - f' =ᶠ[l] g - g'
（共 44 条，此处仅展示前 30 条）
-/
theorem martingale_martingalePart [CompleteSpace E]
    (hf : StronglyAdapted ℱ f) (hf_int : ∀ n, Integrable (f n) μ)
    [SigmaFiniteFiltration μ ℱ] : Martingale (martingalePart f ℱ μ) ℱ μ := by
  refine ⟨stronglyAdapted_martingalePart hf, fun i j hij => ?_⟩
  -- ⊢ μ[martingalePart f ℱ μ j | ℱ i] =ᵐ[μ] martingalePart f ℱ μ i
  have h_eq_sum : μ[martingalePart f ℱ μ j | ℱ i] =ᵐ[μ]
      f 0 + ∑ k ∈ Finset.range j,
        (μ[f (k + 1) - f k | ℱ i] - μ[μ[f (k + 1) - f k | ℱ k] | ℱ i]) := by
    rw [martingalePart_eq_sum]
    refine (condExp_add (hf_int 0) (by fun_prop) _).trans ?_
    refine (EventuallyEq.rfl.add (condExp_finsetSum (fun i _ => by fun_prop) _)).trans ?_
    refine EventuallyEq.add ?_ ?_
    · rw [condExp_of_stronglyMeasurable (ℱ.le _) _ (hf_int 0)]
      · exact (hf 0).mono (ℱ.mono zero_le)
    · exact eventuallyEq_sum fun k _ => condExp_sub (by fun_prop) integrable_condExp _
  refine h_eq_sum.trans ?_
  have h_ge : ∀ k, i ≤ k →
      μ[f (k + 1) - f k | ℱ i] - μ[μ[f (k + 1) - f k | ℱ k] | ℱ i] =ᵐ[μ] 0 := by
    intro k hk
    have : μ[μ[f (k + 1) - f k | ℱ k] | ℱ i] =ᵐ[μ] μ[f (k + 1) - f k | ℱ i] :=
      condExp_condExp_of_le (ℱ.mono hk) (ℱ.le k)
    filter_upwards [this] with x hx
    rw [Pi.sub_apply, Pi.zero_apply, hx, sub_self]
  have h_lt : ∀ k, k < i → μ[f (k + 1) - f k | ℱ i] - μ[μ[f (k + 1) - f k | ℱ k] | ℱ i] =ᵐ[μ]
      f (k + 1) - f k - μ[f (k + 1) - f k | ℱ k] := by
    refine fun k hk => EventuallyEq.sub ?_ ?_
    · rw [condExp_of_stronglyMeasurable]
      · exact ((hf (k + 1)).mono (ℱ.mono (Nat.succ_le_of_lt hk))).sub ((hf k).mono (ℱ.mono hk.le))
      · exact (hf_int _).sub (hf_int _)
    · rw [condExp_of_stronglyMeasurable]
      · exact stronglyMeasurable_condExp.mono (ℱ.mono hk.le)
      · exact integrable_condExp
  rw [martingalePart_eq_sum]
  refine EventuallyEq.add EventuallyEq.rfl ?_
  rw [← Finset.sum_range_add_sum_Ico _ hij, ←
    add_zero (∑ i ∈ Finset.range i, (f (i + 1) - f i - μ[f (i + 1) - f i | ℱ i]))]
  refine (eventuallyEq_sum fun k hk => h_lt k (Finset.mem_range.mp hk)).add ?_
  refine (eventuallyEq_sum fun k hk => h_ge k (Finset.mem_Ico.mp hk).1).trans ?_
  simp only [Finset.sum_const_zero]
  rfl

-- The following two lemmas demonstrate the essential uniqueness of the decomposition
/-
**MeasureTheory.martingalePart_add_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：martingalePart_add_ae_eq [CompleteSpace E] [SigmaFiniteFiltration μ ℱ] {f 
g : Nat -> Ω -> E} (hf : Martingale f ℱ μ) (hg : StronglyAdapted ℱ fun n => g (n
 + 1)) (hg0 : g 0 = 0) (hgint : forall n, Integrable (g n) μ) (n : Nat) : martin
galePart (f + g) ℱ μ n =ᵐ[μ] f n
参数：hf : Martingale f ℱ μ；hg : StronglyAdapted ℱ fun n => g (n + 1)；hg0 : g 0 = 0
；hgint : forall n, Integrable (g n) μ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_sub_iff_add_eq_add`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b
 c d : G}, a - b = c - d ↔ a + d = c + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.martingalePart_add_predictablePart`：martingalePart_add_pre
dictablePart (ℱ : Filtration Nat m0) (μ : Measure Ω) (f : Nat -> Ω -> E) : marti
ngalePart f ℱ μ + predictablePart f ℱ …
· 使用定理 `MeasureTheory.StronglyAdapted.sub`：∀ {Ω : Type u_1} {ι : Type u_2} {m : 
MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   {β :
 ι → Type u_3} [inst_1 …
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.stronglyAdapted_predictablePart`：stronglyAdapted_predictab
lePart : StronglyAdapted ℱ fun n => predictablePart f ℱ μ (n + 1)
· 使用引理 `MeasureTheory.IsStronglyPredictable.of_measurable_add_one`：of_measurable
_add_one {𝓕 : Filtration Nat m} {u : Nat -> Ω -> E} (h₀ : StronglyMeasurable[𝓕 0
] (u 0)) (h : forall n, StronglyMeasurable[𝓕 n]…
· 使用定理 `MeasureTheory.stronglyMeasurable_zero`：∀ {α : Type u_1} {β : Type u_2} {
x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Zero β],   MeasureT
heory.StronglyMeasurable 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Martingale.sub`：sub (hf : Martingale f ℱ μ) (hg : Martinga
le g ℱ μ) : Martingale (f - g) ℱ μ
· 使用定理 `MeasureTheory.martingale_martingalePart`：martingale_martingalePart [Comp
leteSpace E] (hf : StronglyAdapted ℱ f) (hf_int : forall n, Integrable (f n) μ) 
[SigmaFiniteFiltration μ ℱ] :…
· 使用定理 `MeasureTheory.StronglyAdapted.add`：∀ {Ω : Type u_1} {ι : Type u_2} {m : 
MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   {β :
 ι → Type u_3} [inst_1 …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `MeasureTheory.Martingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type u_2
} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheo
ry.Measure Ω} [inst_1 : Normed…
· 使用引理 `MeasureTheory.IsStronglyPredictable.stronglyAdapted`：stronglyAdapted {𝓕 
: Filtration ι m} {u : ι -> Ω -> E} (h𝓕 : IsStronglyPredictable 𝓕 u) : StronglyA
dapted 𝓕 u
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `MeasureTheory.Martingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} {ι 
: Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory.Me
asure Ω} [inst_1 : Normed…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyEq_iff_sub`：eventuallyEq_iff_sub [AddGroup β] {f g : α 
-> β} {l : Filter α} : f =ᶠ[l] g ↔ f - g =ᶠ[l] 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Martingale.eq_zero_of_predictable`：∀ {Ω : Type u_1} {E : T
ype u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : NormedAd
dCommGroup E]   [inst_1 : NormedSpace…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
（共 40 条，此处仅展示前 30 条）
-/
theorem martingalePart_add_ae_eq [CompleteSpace E] [SigmaFiniteFiltration μ ℱ] {f g : ℕ → Ω → E}
    (hf : Martingale f ℱ μ) (hg : StronglyAdapted ℱ fun n => g (n + 1)) (hg0 : g 0 = 0)
    (hgint : ∀ n, Integrable (g n) μ) (n : ℕ) : martingalePart (f + g) ℱ μ n =ᵐ[μ] f n := by
  set h := f - martingalePart (f + g) ℱ μ with hhdef
  have hh : h = predictablePart (f + g) ℱ μ - g := by
    rw [hhdef, sub_eq_sub_iff_add_eq_add, add_comm (predictablePart (f + g) ℱ μ),
      martingalePart_add_predictablePart]
  have hhpred : StronglyAdapted ℱ fun n => h (n + 1) := by
    rw [hh]
    exact stronglyAdapted_predictablePart.sub hg
  have := (IsStronglyPredictable.of_measurable_add_one (hg0.symm ▸ stronglyMeasurable_zero) hg)
  have hhmgle : Martingale h ℱ μ := hf.sub (martingale_martingalePart
    (hf.stronglyAdapted.add this.stronglyAdapted) fun n => (hf.integrable n).add <| hgint n)
  refine (eventuallyEq_iff_sub.2 ?_).symm
  filter_upwards [hhmgle.eq_zero_of_predictable hhpred n] with ω hω
  unfold h at hω
  rw [Pi.sub_apply] at hω
  rw [hω, Pi.sub_apply, martingalePart]
  simp [hg0]
/-
**MeasureTheory.predictablePart_add_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：predictablePart_add_ae_eq [CompleteSpace E] [SigmaFiniteFiltration μ ℱ] {f
 g : Nat -> Ω -> E} (hf : Martingale f ℱ μ) (hg : StronglyAdapted ℱ fun n => g (
n + 1)) (hg0 : g 0 = 0) (hgint : forall n, Integrable (g n) μ) (n : Nat) : predi
ctablePart (f + g) ℱ μ n =ᵐ[μ] g n
参数：hf : Martingale f ℱ μ；hg : StronglyAdapted ℱ fun n => g (n + 1)；hg0 : g 0 = 0
；hgint : forall n, Integrable (g n) μ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.martingalePart_add_ae_eq`：martingalePart_add_ae_eq [Comple
teSpace E] [SigmaFiniteFiltration μ ℱ] {f g : Nat -> Ω -> E} (hf : Martingale f 
ℱ μ) (hg : StronglyAdapted ℱ…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `MeasureTheory.martingalePart_add_predictablePart`：martingalePart_add_pre
dictablePart (ℱ : Filtration Nat m0) (μ : Measure Ω) (f : Nat -> Ω -> E) : marti
ngalePart f ℱ μ + predictablePart f ℱ …
-/
theorem predictablePart_add_ae_eq [CompleteSpace E] [SigmaFiniteFiltration μ ℱ] {f g : ℕ → Ω → E}
    (hf : Martingale f ℱ μ) (hg : StronglyAdapted ℱ fun n => g (n + 1)) (hg0 : g 0 = 0)
    (hgint : ∀ n, Integrable (g n) μ) (n : ℕ) : predictablePart (f + g) ℱ μ n =ᵐ[μ] g n := by
  filter_upwards [martingalePart_add_ae_eq hf hg hg0 hgint n] with ω hω
  rw [← add_right_inj (f n ω)]
  conv_rhs => rw [← Pi.add_apply, ← Pi.add_apply, ← martingalePart_add_predictablePart ℱ μ (f + g)]
  rw [Pi.add_apply, Pi.add_apply, hω]

section Difference

/-
**MeasureTheory.predictablePart_bdd_difference** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：predictablePart_bdd_difference [CompleteSpace E] {R : Real} {f : Nat -> Ω 
-> E} (ℱ : Filtration Nat m0) (hbdd : forallᵐ ω ∂μ, forall i, ‖f (i + 1) ω - f i
 ω‖ <= R) : forallᵐ ω ∂μ, forall i, ‖predictablePart f ℱ μ (i + 1) ω - predictab
lePart f ℱ μ i ω‖ <= R
参数：ℱ : Filtration Nat m0；hbdd : forallᵐ ω ∂μ, forall i, ‖f (i + 1) ω - f i ω‖ <=
 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_range_succ_sub_sum`：∀ {M : Type u_4} (f : ℕ → M) {n : ℕ} [ins
t : AddCommGroup M],   ∑ i ∈ Finset.range (n + 1), f i - ∑ i ∈ Finset.range n, f
 i = f n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.ae_bdd_norm_condExp_of_ae_bdd_norm`：ae_bdd_norm_condExp_of
_ae_bdd_norm {R : Real} {f : α -> E} (hbdd : forallᵐ x ∂μ, ‖f x‖ <= R) : forallᵐ
 x ∂μ, ‖μ[f | m] x‖ <= R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem predictablePart_bdd_difference [CompleteSpace E] {R : ℝ} {f : ℕ → Ω → E}
    (ℱ : Filtration ℕ m0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, ‖f (i + 1) ω - f i ω‖ ≤ R) :
    ∀ᵐ ω ∂μ, ∀ i, ‖predictablePart f ℱ μ (i + 1) ω - predictablePart f ℱ μ i ω‖ ≤ R := by
  simp_rw [predictablePart, Finset.sum_apply, Finset.sum_range_succ_sub_sum]
  exact ae_all_iff.2 fun i => ae_bdd_norm_condExp_of_ae_bdd_norm <| ae_all_iff.1 hbdd i
/-
**MeasureTheory.martingalePart_bdd_difference** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：martingalePart_bdd_difference [CompleteSpace E] {R : Real} {f : Nat -> Ω -
> E} (ℱ : Filtration Nat m0) (hbdd : forallᵐ ω ∂μ, forall i, ‖f (i + 1) ω - f i 
ω‖ <= R) : forallᵐ ω ∂μ, forall i, ‖martingalePart f ℱ μ (i + 1) ω - martingaleP
art f ℱ μ i ω‖ <= 2 * R
参数：ℱ : Filtration Nat m0；hbdd : forallᵐ ω ∂μ, forall i, ‖f (i + 1) ω - f i ω‖ <=
 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.predictablePart_bdd_difference`：predictablePart_bdd_differ
ence [CompleteSpace E] {R : Real} {f : Nat -> Ω -> E} (ℱ : Filtration Nat m0) (h
bdd : forallᵐ ω ∂μ, forall i, ‖f (…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_sub_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a - b - (c - d) = a - c - (b - d)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_sub_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a - b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem martingalePart_bdd_difference [CompleteSpace E] {R : ℝ} {f : ℕ → Ω → E}
    (ℱ : Filtration ℕ m0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, ‖f (i + 1) ω - f i ω‖ ≤ R) :
    ∀ᵐ ω ∂μ, ∀ i, ‖martingalePart f ℱ μ (i + 1) ω - martingalePart f ℱ μ i ω‖ ≤ 2 * R := by
  filter_upwards [hbdd, predictablePart_bdd_difference ℱ hbdd] with ω hω₁ hω₂ i
  simpa [two_mul, martingalePart, sub_sub_sub_comm] using
    (norm_sub_le _ _).trans (add_le_add (hω₁ i) (hω₂ i))

end Difference

end MeasureTheory

