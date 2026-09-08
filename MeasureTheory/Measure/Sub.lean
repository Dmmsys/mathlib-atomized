/-
Copyright (c) 2022 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Subtraction of measures

In this file we define `μ - ν` to be the least measure `τ` such that `μ ≤ τ + ν`.
It is equivalent to `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
Compare with `ENNReal.instSub`.
Specifically, note that if you have `α = {1,2}`, and `μ {1} = 2`, `μ {2} = 0`, and
`ν {2} = 2`, `ν {1} = 0`, then `(μ - ν) {1, 2} = 2`. However, if `μ ≤ ν`, and
`ν univ ≠ ∞`, then `(μ - ν) + ν = μ`.
-/

@[expose] public section

open Set

namespace MeasureTheory

namespace Measure

/-- The measure `μ - ν` is defined to be the least measure `τ` such that `μ ≤ τ + ν`.
It is equivalent to `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
Compare with `ENNReal.instSub`.
Specifically, note that if you have `α = {1,2}`, and `μ {1} = 2`, `μ {2} = 0`, and
`ν {2} = 2`, `ν {1} = 0`, then `(μ - ν) {1, 2} = 2`. However, if `μ ≤ ν`, and
`ν univ ≠ ∞`, then `(μ - ν) + ν = μ`. -/
/-
**MeasureTheory.Measure.instSub** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：instSub {α : Type*} [MeasurableSpace α] : Sub (Measure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The measure `μ - ν` is defined to be the least measure `τ` such that `μ ≤ τ + ν`
.
It is equivalent to `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
Compare with `ENNReal.instSub`.
Specifically, note that if you have `α = {1,2}`, and `μ {1} = 2`, `μ {2} = 0`, a
nd
`ν {2} = 2`, `ν {1} = 0`, then `(μ - ν) {1, 2} = 2`. However, if `μ ≤ ν`, and
`ν univ ≠ ∞`, then `(μ - ν) + ν = μ`.
-/
noncomputable instance instSub {α : Type*} [MeasurableSpace α] : Sub (Measure α) :=
  ⟨fun μ ν => sInf { τ | μ ≤ τ + ν }⟩

variable {α : Type*} {m : MeasurableSpace α} {μ ν ξ : Measure α} {s : Set α}
/-
**MeasureTheory.Measure.sub_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：sub_def : μ - ν = sInf { d | μ <= d + ν }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_def : μ - ν = sInf { d | μ ≤ d + ν } := rfl
/-
**MeasureTheory.Measure.sub_le_of_le_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：sub_le_of_le_add {d} (h : μ <= d + ν) : μ - ν <= d
参数：h : μ <= d + ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem sub_le_of_le_add {d} (h : μ ≤ d + ν) : μ - ν ≤ d :=
  sInf_le h
/-
**MeasureTheory.Measure.sub_eq_zero_of_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：sub_eq_zero_of_le (h : μ <= ν) : μ - ν = 0
参数：h : μ <= ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.nonpos_iff_eq_zero'`：nonpos_iff_eq_zero' : μ <= 0 
↔ μ = 0
· 使用定理 `MeasureTheory.Measure.sub_le_of_le_add`：sub_le_of_le_add {d} (h : μ <= d
 + ν) : μ - ν <= d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem sub_eq_zero_of_le (h : μ ≤ ν) : μ - ν = 0 :=
  nonpos_iff_eq_zero'.1 <| sub_le_of_le_add <| by rwa [zero_add]
/-
**MeasureTheory.Measure.sub_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`
。
形式化陈述：sub_le : μ - ν <= μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.sub_le_of_le_add`：sub_le_of_le_add {d} (h : μ <= d
 + ν) : μ - ν <= d
· 使用定理 `MeasureTheory.Measure.le_add_right`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν + ν'
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem sub_le : μ - ν ≤ μ :=
  sub_le_of_le_add <| Measure.le_add_right le_rfl

@[simp]
/-
**MeasureTheory.Measure.sub_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：sub_top : μ - ⊤ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.sub_eq_zero_of_le`：sub_eq_zero_of_le (h : μ <= ν) 
: μ - ν = 0
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem sub_top : μ - ⊤ = 0 :=
  sub_eq_zero_of_le le_top

@[simp]
/-
**MeasureTheory.Measure.zero_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}, 0 
- μ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.sub_eq_zero_of_le`：sub_eq_zero_of_le (h : μ <= ν) 
: μ - ν = 0
· 使用定理 `MeasureTheory.Measure.zero_le`：∀ {α : Type u_1} {_m0 : MeasurableSpace α
} (μ : MeasureTheory.Measure α), 0 ≤ μ
-/
protected theorem zero_sub : 0 - μ = 0 :=
  sub_eq_zero_of_le μ.zero_le

@[simp]
/-
**MeasureTheory.Measure.sub_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}, μ 
- μ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.sub_eq_zero_of_le`：sub_eq_zero_of_le (h : μ <= ν) 
: μ - ν = 0
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
protected theorem sub_self : μ - μ = 0 :=
  sub_eq_zero_of_le le_rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MeasureTheory.Measure.sub_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}, μ 
- 0 = μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sub_def`：sub_def : μ - ν = sInf { d | μ <= d + ν }
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem sub_zero : μ - 0 = μ := by
  rw [sub_def]
  apply le_antisymm
  · simp [sInf_le]
  · simp

/-- This application lemma only works in special circumstances. Given knowledge of
when `μ ≤ ν` and `ν ≤ μ`, a more general application lemma can be written. -/
/-
**MeasureTheory.Measure.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：sub_apply [IsFiniteMeasure ν] (h₁ : MeasurableSet s) (h₂ : ν <= μ) : (μ - 
ν) s = μ s - ν s
参数：h₁ : MeasurableSet s；h₂ : ν <= μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ENNReal.tsum_sub`：tsum_sub {f : Nat -> Real>=0∞} {g : Nat -> Real>=0∞} (
h₁ : ∑' i, g i != ∞) (h₂ : g <= f) : ∑' i, (f i - g i) = ∑' i, f i - ∑' i, g i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasureTheory.Measure.ofMeasurable_apply`：ofMeasurable_apply {m : forall
 s : Set α, MeasurableSet s -> Real>=0∞} {m0 : m ∅ MeasurableSet.empty = 0} {mU 
: forall ⦃f : Nat -> Set α⦄ (h…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `MeasureTheory.Measure.sub_def`：sub_def : μ - ν = sInf { d | μ <= d + ν }
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `MeasureTheory.Measure.le_of_add_le_add_left`：∀ {α : Type u_1} {m0 : Meas
urableSpace α} {μ ν₁ ν₂ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasur
e μ],   μ + ν₁ ≤ μ + ν₂ → ν₁ ≤ ν₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x

--- 原说明 ---
This application lemma only works in special circumstances. Given knowledge of
when `μ ≤ ν` and `ν ≤ μ`, a more general application lemma can be written.
-/
theorem sub_apply [IsFiniteMeasure ν] (h₁ : MeasurableSet s) (h₂ : ν ≤ μ) :
    (μ - ν) s = μ s - ν s := by
  -- We begin by defining `measure_sub`, which will be equal to `(μ - ν)`.
  let measure_sub : Measure α := MeasureTheory.Measure.ofMeasurable
    (fun (t : Set α) (_ : MeasurableSet t) => μ t - ν t) (by simp)
    (fun g h_meas h_disj ↦ by
      simp only [measure_iUnion h_disj h_meas]
      rw [ENNReal.tsum_sub _ (h₂ <| g ·)]
      rw [← measure_iUnion h_disj h_meas]
      apply measure_ne_top)
  -- Now, we demonstrate `μ - ν = measure_sub`, and apply it.
  have h_measure_sub_add : ν + measure_sub = μ := by
    ext1 t h_t_measurable_set
    simp only [Pi.add_apply, coe_add]
    rw [MeasureTheory.Measure.ofMeasurable_apply _ h_t_measurable_set, add_comm,
      tsub_add_cancel_of_le (h₂ t)]
  have h_measure_sub_eq : μ - ν = measure_sub := by
    rw [MeasureTheory.Measure.sub_def]
    apply le_antisymm
    · apply sInf_le
      simp [add_comm, h_measure_sub_add]
    apply le_sInf
    intro d h_d
    rw [← h_measure_sub_add, mem_ofPred_eq, add_comm d] at h_d
    apply Measure.le_of_add_le_add_left h_d
  rw [h_measure_sub_eq]
  apply Measure.ofMeasurable_apply _ h₁
/-
**MeasureTheory.Measure.sub_add_cancel_of_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：sub_add_cancel_of_le [IsFiniteMeasure ν] (h₁ : ν <= μ) : μ - ν + ν = μ
参数：h₁ : ν <= μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `MeasureTheory.Measure.sub_apply`：sub_apply [IsFiniteMeasure ν] (h₁ : Mea
surableSet s) (h₂ : ν <= μ) : (μ - ν) s = μ s - ν s
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
-/
theorem sub_add_cancel_of_le [IsFiniteMeasure ν] (h₁ : ν ≤ μ) : μ - ν + ν = μ := by
  ext1 s h_s_meas
  rw [add_apply, sub_apply h_s_meas h₁, tsub_add_cancel_of_le (h₁ s)]

@[simp]
/-
**MeasureTheory.Measure.add_sub_cancel** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [
MeasureTheory.IsFiniteMeasure ν],   μ + ν - ν = μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sub_apply`：sub_apply [IsFiniteMeasure ν] (h₁ : Mea
surableSet s) (h₂ : ν <= μ) : (μ - ν) s = μ s - ν s
· 使用定理 `MeasureTheory.Measure.le_add_left`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν' + ν
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `ENNReal.add_sub_cancel_right`：∀ {a b : ENNReal}, b ≠ ⊤ → a + b - b = a
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
protected lemma add_sub_cancel [IsFiniteMeasure ν] : μ + ν - ν = μ := by
  ext1 s hs
  rw [sub_apply hs (Measure.le_add_left (le_refl _)), add_apply,
    ENNReal.add_sub_cancel_right (measure_ne_top ν s)]
/-
**MeasureTheory.Measure.restrict_sub_eq_restrict_sub_restrict** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：restrict_sub_eq_restrict_sub_restrict (h_meas_s : MeasurableSet s) : (μ - 
ν).restrict s = μ.restrict s - ν.restrict s
参数：h_meas_s : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sub_def`：sub_def : μ - ν = sInf { d | μ <= d + ν }
· 使用定理 `MeasureTheory.Measure.le_add_right`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν + ν'
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Measure.restrict_sInf_eq_sInf_restrict`：restrict_sInf_eq_s
Inf_restrict {m0 : MeasurableSpace α} {m : Set (Measure α)} (hm : m.Nonempty) (h
t : MeasurableSet t) : (sInf m).restrict t…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sInf_le_sInf_of_isCoinitialFor`：∀ {α : Type u_1} [inst : CompleteSemilat
ticeInf α] {s t : Set α}, IsCoinitialFor s t → sInf t ≤ sInf s
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canon
icallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.Measure.restrict_eq_self`：restrict_eq_self (h : s subseteq
 t) : μ.restrict t s = μ s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.add_top`：add_top : μ + ⊤ = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 47 条，此处仅展示前 30 条）
-/
theorem restrict_sub_eq_restrict_sub_restrict (h_meas_s : MeasurableSet s) :
    (μ - ν).restrict s = μ.restrict s - ν.restrict s := by
  repeat rw [sub_def]
  have h_nonempty : { d | μ ≤ d + ν }.Nonempty := ⟨μ, Measure.le_add_right le_rfl⟩
  rw [restrict_sInf_eq_sInf_restrict h_nonempty h_meas_s]
  apply le_antisymm
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    intro ν' h_ν'_in
    rw [mem_ofPred_eq] at h_ν'_in
    refine ⟨ν'.restrict s, ?_, restrict_le_self⟩
    refine ⟨ν' + (⊤ : Measure α).restrict sᶜ, ?_, ?_⟩
    · rw [mem_ofPred_eq, add_right_comm, Measure.le_iff]
      intro t h_meas_t
      repeat rw [← measure_inter_add_sdiff t h_meas_s]
      refine add_le_add ?_ ?_
      · rw [add_apply, add_apply]
        apply le_add_right _
        rw [← restrict_eq_self μ inter_subset_right,
          ← restrict_eq_self ν inter_subset_right]
        apply h_ν'_in
      · rw [add_apply, restrict_apply (h_meas_t.diff h_meas_s), sdiff_eq, inter_assoc, inter_self,
          ← add_apply]
        have h_mu_le_add_top : μ ≤ ν' + ν + ⊤ := by simp only [add_top, le_top]
        exact Measure.le_iff'.1 h_mu_le_add_top _
    · ext1 t h_meas_t
      simp [restrict_apply h_meas_t, restrict_apply (h_meas_t.inter h_meas_s), inter_assoc]
  · refine sInf_le_sInf_of_isCoinitialFor ?_
    refine forall_mem_image.2 fun t h_t_in => ⟨t.restrict s, ?_, le_rfl⟩
    rw [Set.mem_ofPred_eq, ← restrict_add]
    exact restrict_mono Subset.rfl h_t_in
/-
**MeasureTheory.Measure.sub_apply_eq_zero_of_restrict_le_restrict** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：sub_apply_eq_zero_of_restrict_le_restrict (h_le : μ.restrict s <= ν.restri
ct s) (h_meas_s : MeasurableSet s) : (μ - ν) s = 0
参数：h_le : μ.restrict s <= ν.restrict s；h_meas_s : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_apply_self`：restrict_apply_self (s : Set 
α) : (μ.restrict s) s = μ s
· 使用定理 `MeasureTheory.Measure.restrict_sub_eq_restrict_sub_restrict`：restrict_su
b_eq_restrict_sub_restrict (h_meas_s : MeasurableSet s) : (μ - ν).restrict s = μ
.restrict s - ν.restrict s
· 使用定理 `MeasureTheory.Measure.sub_eq_zero_of_le`：sub_eq_zero_of_le (h : μ <= ν) 
: μ - ν = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sub_apply_eq_zero_of_restrict_le_restrict (h_le : μ.restrict s ≤ ν.restrict s)
    (h_meas_s : MeasurableSet s) : (μ - ν) s = 0 := by
  rw [← restrict_apply_self, restrict_sub_eq_restrict_sub_restrict, sub_eq_zero_of_le] <;> simp [*]
/-
**MeasureTheory.Measure.isFiniteMeasure_sub** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：isFiniteMeasure_sub [IsFiniteMeasure μ] : IsFiniteMeasure (μ - ν)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isFiniteMeasure_of_le`：isFiniteMeasure_of_le (μ : Measure 
α) [IsFiniteMeasure μ] (h : ν <= μ) : IsFiniteMeasure ν
· 使用定理 `MeasureTheory.Measure.sub_le`：sub_le : μ - ν <= μ
-/
instance isFiniteMeasure_sub [IsFiniteMeasure μ] : IsFiniteMeasure (μ - ν) :=
  isFiniteMeasure_of_le μ sub_le

/-- See `sub_le_iff_le_add` for the case where both measures are finite, which does not need the
hypothesis `ν ≤ μ`. -/
/-
**MeasureTheory.Measure.sub_le_iff_le_add_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：sub_le_iff_le_add_of_le [IsFiniteMeasure ν] (h_le : ν <= μ) : μ - ν <= ξ ↔
 μ <= ξ + ν
参数：h_le : ν <= μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sub_add_cancel_of_le`：sub_add_cancel_of_le [IsFini
teMeasure ν] (h₁ : ν <= μ) : μ - ν + ν = μ
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.Measure.sub_le_of_le_add`：sub_le_of_le_add {d} (h : μ <= d
 + ν) : μ - ν <= d

--- 原说明 ---
See `sub_le_iff_le_add` for the case where both measures are finite, which does 
not need the
hypothesis `ν ≤ μ`.
-/
lemma sub_le_iff_le_add_of_le [IsFiniteMeasure ν] (h_le : ν ≤ μ) : μ - ν ≤ ξ ↔ μ ≤ ξ + ν := by
  refine ⟨fun h ↦ ?_, Measure.sub_le_of_le_add⟩
  simpa [sub_add_cancel_of_le h_le] using add_le_add_left h ν

end Measure

end MeasureTheory

