/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.IonescuTulcea.Maps

/-!
# Consecutive composition of kernels

This file is the first step towards Ionescu-Tulcea theorem, which allows for instance to construct
the product of an infinite family of probability measures. The idea of the statement is as follows:
consider a family of kernels `κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))`.
One can interpret `κ n` as a kernel which takes as an input the trajectory of a point started in
`X 0` and moving `X 0 → X 1 → X 2 → ... → X n` and which outputs the distribution of the next
position of the point in `X (n + 1)`. If `a b : ℕ` and `a < b`, we can compose the kernels,
and `κ a ⊗ₖ κ (a + 1) ⊗ₖ ... ⊗ₖ κ b` takes the trajectory up to time `a` as input and outputs
the distribution of the trajectory in `X (a + 1) × ... × X (b + 1)`.

The Ionescu-Tulcea theorem then tells us that these compositions can be extended into a kernel
`η : Kernel (Π i : Iic a, X i) → Π n > a, X n` which given the trajectory up to time `a` outputs
the distribution of the infinite trajectory started in `X (a + 1)`. In other words this theorem
makes sense of composing infinitely many kernels together.

To be able to even state the theorem we want to take the composition-product
(see `ProbabilityTheory.Kernel.compProd`) of consecutive kernels.
This however is not straightforward.

Consider `n : ℕ`. We cannot write `(κ n) ⊗ₖ (κ (n + 1))` directly, we need to first
introduce an equivalence to see `κ (n + 1)` as a kernel with codomain
`(Π i : Iic n, X i) × X (n + 1)`, and we get a `Kernel (Π i : Iic n, X i) (X (n + 1) × (X (n + 2))`.
However we want to do multiple composition at once, i.e. write
`(κ n) ⊗ₖ ... ⊗ₖ (κ m)` for `n < m`. This requires even more equivalences to make sense of, and at
the end of the day we get kernels which still cannot be composed together.

To tackle this issue, we decide here to only consider kernels of the form
`Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)`. In other words these kernels take as input
a trajectory up to time `a` and output the distribution of the full trajectory up to time `b`.
This is captured in the definition `partialTraj κ a b`
(`partialTraj` stands for "partial trajectory").
The advantage of this approach is that it allows us to write for instance
`partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c` (see `partialTraj_comp_partialTraj`.)

In this file we therefore define this family of kernels and prove some properties of it.
In particular we provide at the end of the file some results to compute the integral of a function
against `partialTraj κ a b`, taking inspiration from `MeasureTheory.lmarginal`.

## Main definitions

* `partialTraj κ a b`: Given the trajectory of a point up to time `a`, returns the distribution
  of the trajectory up to time `b`.
* `lmarginalPartialTraj κ a b f`: The integral of `f` against `partialTraj κ a b`.
  This is essentially the integral of `f` against `κ (a + 1) ⊗ₖ ... ⊗ₖ κ b` but seen as depending
  on all the variables, mimicking `MeasureTheory.lmarginal`. This allows to write
  `lmarginalPartialTraj κ b c (lmarginalPartialTraj κ a b f)`.

## Main statements

* `partialTraj_comp_partialTraj`: if `a ≤ b` and `b ≤ c` then
  `partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c`.
* `map_partialTraj_succ_self a`: the pushforward of `partialTraj κ a (a + 1)` along the point at
  time `a + 1` is the kernel `κ a`.
* `lmarginalPartialTraj_self` : if `a ≤ b` and `b ≤ c` then
  `lmarginalPartialTraj κ b c (lmarginalPartialTraj κ a b f) = lmarginalPartialTraj κ a c`.

## Tags

Ionescu-Tulcea theorem, composition of kernels
-/

@[expose] public section

open Finset Function MeasureTheory Preorder ProbabilityTheory

open scoped ENNReal

variable {X : ℕ → Type*} {mX : ∀ n, MeasurableSpace (X n)} {a b c : ℕ}
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))}

section partialTraj

/-! ### Definition of `partialTraj` -/

namespace ProbabilityTheory.Kernel

open MeasurableEquiv

variable (κ) in
/-- Given a family of kernels `κ n` from `X 0 × ... × X n` to `X (n + 1)` for all `n`,
construct a kernel from `X 0 × ... × X a` to `X 0 × ... × X b` by iterating `κ`.

The idea is that the input is some trajectory up to time `a`, and the output is the distribution
of the trajectory up to time `b`. In particular if `b ≤ a`, this is just a deterministic kernel
(see `partialTraj_le`). The name `partialTraj` stands for "partial trajectory".

This kernel can be extended into a kernel with codomain `Π n, X n` via the Ionescu-Tulcea theorem.
-/
/-
**ProbabilityTheory.Kernel.partialTraj** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：partialTraj (a b : Nat) : Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)
参数：a b : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_not_ge`：∀ {a b : ℕ}, ¬a ≥ b → a ≤ b

--- 原说明 ---
Given a family of kernels `κ n` from `X 0 × ... × X n` to `X (n + 1)` for all `n
`,
construct a kernel from `X 0 × ... × X a` to `X 0 × ... × X b` by iterating `κ`.

The idea is that the input is some trajectory up to time `a`, and the output is 
the distribution
of the trajectory up to time `b`. In particular if `b ≤ a`, this is just a deter
ministic kernel
(see `partialTraj_le`). The name `partialTraj` stands for "partial trajectory".

This kernel can be extended into a kernel with codomain `Π n, X n` via the Iones
cu-Tulcea theorem.
-/
noncomputable def partialTraj (a b : ℕ) : Kernel (Π i : Iic a, X i) (Π i : Iic b, X i) :=
  if h : b ≤ a then deterministic (frestrictLe₂ h) (measurable_frestrictLe₂ h)
  else @Nat.leRec a (fun b _ ↦ Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)) Kernel.id
    (fun k _ κ_k ↦ ((Kernel.id ×ₖ ((κ k).map (piSingleton k))) ∘ₖ κ_k).map (IicProdIoc k (k + 1)))
    b (Nat.le_of_not_ge h)

section Basic

/-- If `b ≤ a`, given the trajectory up to time `a`, the trajectory up to time `b` is
deterministic and is equal to the restriction of the trajectory up to time `a`. -/
/-
**ProbabilityTheory.Kernel.partialTraj_le** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：partialTraj_le (hba : b <= a) : partialTraj κ a b = deterministic (frestri
ctLe₂ hba) (measurable_frestrictLe₂ _)
参数：hba : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Preorder.measurable_frestrictLe₂`：measurable_frestrictLe₂ {a b : α} (hab
 : a <= b) : Measurable (frestrictLe₂ (π
· 使用定理 `Nat.le_of_not_ge`：∀ {a b : ℕ}, ¬a ≥ b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.partialTraj.eq_1`：∀ {X : ℕ → Type u_1} {mX : (n
 : ℕ) → MeasurableSpace (X n)}   (κ : (n : ℕ) → ProbabilityTheory.Kernel ((i : ↥
(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc

--- 原说明 ---
If `b ≤ a`, given the trajectory up to time `a`, the trajectory up to time `b` i
s
deterministic and is equal to the restriction of the trajectory up to time `a`.
-/
lemma partialTraj_le (hba : b ≤ a) :
    partialTraj κ a b = deterministic (frestrictLe₂ hba) (measurable_frestrictLe₂ _) := by
  rw [partialTraj, dif_pos hba]

@[simp]
/-
**ProbabilityTheory.Kernel.partialTraj_self** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：partialTraj_self (a : Nat) : partialTraj κ a a = Kernel.id
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Preorder.measurable_frestrictLe₂`：measurable_frestrictLe₂ {a b : α} (hab
 : a <= b) : Measurable (frestrictLe₂ (π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_le`：partialTraj_le (hba : b <= a) :
 partialTraj κ a b = deterministic (frestrictLe₂ hba) (measurable_frestrictLe₂ _
)
-/
lemma partialTraj_self (a : ℕ) : partialTraj κ a a = Kernel.id := by rw [partialTraj_le le_rfl]; rfl

@[simp]
/-
**ProbabilityTheory.Kernel.partialTraj_zero** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：partialTraj_zero : partialTraj κ a 0 = deterministic (frestrictLe₂ zero_le
) (measurable_frestrictLe₂ _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Preorder.measurable_frestrictLe₂`：measurable_frestrictLe₂ {a b : α} (hab
 : a <= b) : Measurable (frestrictLe₂ (π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_le`：partialTraj_le (hba : b <= a) :
 partialTraj κ a b = deterministic (frestrictLe₂ hba) (measurable_frestrictLe₂ _
)
-/
lemma partialTraj_zero :
    partialTraj κ a 0 = deterministic (frestrictLe₂ zero_le) (measurable_frestrictLe₂ _) := by
  rw [partialTraj_le zero_le]
/-
**ProbabilityTheory.Kernel.partialTraj_le_def** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：partialTraj_le_def (hab : a <= b) : partialTraj κ a b = @Nat.leRec a (fun 
b _ => Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)) Kernel.id (fun k _ κ_k => (
(Kernel.id ×ₖ ((κ k).map (piSingleton k))) ∘ₖ κ_k).map (IicProdIoc k (k + 1))) b
 hab
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_self`：partialTraj_self (a : Nat) : 
partialTraj κ a a = Kernel.id
· 使用引理 `Nat.leRec_self`：leRec_self {n} {motive : (m : Nat) -> n <= m -> Sort*} (
refl : motive n (Nat.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motiv
e k …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.le_of_not_ge`：∀ {a b : ℕ}, ¬a ≥ b → a ≤ b
· 使用定理 `ProbabilityTheory.Kernel.partialTraj.eq_1`：∀ {X : ℕ → Type u_1} {mX : (n
 : ℕ) → MeasurableSpace (X n)}   (κ : (n : ℕ) → ProbabilityTheory.Kernel ((i : ↥
(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma partialTraj_le_def (hab : a ≤ b) : partialTraj κ a b =
    @Nat.leRec a (fun b _ ↦ Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)) Kernel.id
    (fun k _ κ_k ↦ ((Kernel.id ×ₖ ((κ k).map (piSingleton k))) ∘ₖ κ_k).map (IicProdIoc k (k + 1)))
    b hab := by
  obtain rfl | hab := eq_or_lt_of_le hab
  · simp
  · rw [partialTraj, dif_neg (not_le.2 hab)]
/-
**ProbabilityTheory.Kernel.partialTraj_succ_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：partialTraj_succ_of_le (hab : a <= b) : partialTraj κ a (b + 1) = ((Kernel
.id ×ₖ ((κ b).map (piSingleton b))) ∘ₖ partialTraj κ a b).map (IicProdIoc b (b +
 1))
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_not_ge`：∀ {a b : ℕ}, ¬a ≥ b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.partialTraj.eq_1`：∀ {X : ℕ → Type u_1} {mX : (n
 : ℕ) → MeasurableSpace (X n)}   (κ : (n : ℕ) → ProbabilityTheory.Kernel ((i : ↥
(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.leRec_succ`：leRec_succ {n} {motive : (m : Nat) -> n <= m -> Sort*} (
refl : motive n (Nat.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motiv
e k …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.leRec_self`：leRec_self {n} {motive : (m : Nat) -> n <= m -> Sort*} (
refl : motive n (Nat.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motiv
e k …
· 使用定理 `ProbabilityTheory.Kernel.comp_id`：∀ {β : Type u_2} {γ : Type u_3} {mβ : 
MeasurableSpace β} {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel β γ), 
  κ.comp ProbabilityTh…
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_self`：partialTraj_self (a : Nat) : 
partialTraj κ a a = Kernel.id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.le_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n ≤ m.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_le_def`：partialTraj_le_def (hab : a
 <= b) : partialTraj κ a b = @Nat.leRec a (fun b _ => Kernel (Π i : Iic a, X i) 
(Π i : Iic b, X i)) Kernel.id (fu…
-/
lemma partialTraj_succ_of_le (hab : a ≤ b) : partialTraj κ a (b + 1) =
    ((Kernel.id ×ₖ ((κ b).map (piSingleton b))) ∘ₖ partialTraj κ a b).map
    (IicProdIoc b (b + 1)) := by
  rw [partialTraj, dif_neg (by lia)]
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ k hak hk => rw [Nat.leRec_succ, ← partialTraj_le_def]; lia
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a b : ℕ) : IsSFiniteKernel (partialTraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak => rw [partialTraj_succ_of_le hak]; infer_instance
  · rw [partialTraj_le hba]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ n, IsFiniteKernel (κ n)] (a b : ℕ) : IsFiniteKernel (partialTraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak => rw [partialTraj_succ_of_le hak]; infer_instance
  · rw [partialTraj_le hba]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ n, IsZeroOrMarkovKernel (κ n)] (a b : ℕ) :
    IsZeroOrMarkovKernel (partialTraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak => rw [partialTraj_succ_of_le hak]; infer_instance
  · rw [partialTraj_le hba]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ n, IsMarkovKernel (κ n)] (a b : ℕ) :
    IsMarkovKernel (partialTraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak =>
      rw [partialTraj_succ_of_le hak]
      have := IsMarkovKernel.map (κ k) (piSingleton k).measurable
      exact IsMarkovKernel.map _ measurable_IicProdIoc
  · rw [partialTraj_le hba]; infer_instance
/-
**ProbabilityTheory.Kernel.partialTraj_succ_self** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：partialTraj_succ_self (a : Nat) : partialTraj κ a (a + 1) = (Kernel.id ×ₖ 
((κ a).map (piSingleton a))).map (IicProdIoc a (a + 1))
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_succ_of_le`：partialTraj_succ_of_le 
(hab : a <= b) : partialTraj κ a (b + 1) = ((Kernel.id ×ₖ ((κ b).map (piSingleto
n b))) ∘ₖ partialTraj κ a b).map (Iic…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_self`：partialTraj_self (a : Nat) : 
partialTraj κ a a = Kernel.id
· 使用定理 `ProbabilityTheory.Kernel.comp_id`：∀ {β : Type u_2} {γ : Type u_3} {mβ : 
MeasurableSpace β} {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel β γ), 
  κ.comp ProbabilityTh…
-/
lemma partialTraj_succ_self (a : ℕ) :
    partialTraj κ a (a + 1) =
    (Kernel.id ×ₖ ((κ a).map (piSingleton a))).map (IicProdIoc a (a + 1)) := by
  rw [partialTraj_succ_of_le le_rfl, partialTraj_self, comp_id]
/-
**ProbabilityTheory.Kernel.partialTraj_succ_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory.Kernel`。
形式化陈述：partialTraj_succ_eq_comp (hab : a <= b) : partialTraj κ a (b + 1) = partia
lTraj κ b (b + 1) ∘ₖ partialTraj κ a b
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_succ_self`：partialTraj_succ_self (a
 : Nat) : partialTraj κ a (a + 1) = (Kernel.id ×ₖ ((κ a).map (piSingleton a))).m
ap (IicProdIoc a (a + 1))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.map_comp`：map_comp (κ : Kernel α β) (η : Kernel
 β γ) (f : γ -> δ) : (η ∘ₖ κ).map f = (η.map f) ∘ₖ κ
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_succ_of_le`：partialTraj_succ_of_le 
(hab : a <= b) : partialTraj κ a (b + 1) = ((Kernel.id ×ₖ ((κ b).map (piSingleto
n b))) ∘ₖ partialTraj κ a b).map (Iic…
-/
lemma partialTraj_succ_eq_comp (hab : a ≤ b) :
    partialTraj κ a (b + 1) = partialTraj κ b (b + 1) ∘ₖ partialTraj κ a b := by
  rw [partialTraj_succ_self, ← map_comp, partialTraj_succ_of_le hab]

/-- Given the trajectory up to time `a`, `partialTraj κ a b` gives the distribution of
the trajectory up to time `b`. Then plugging this into `partialTraj κ b c` gives
the distribution of the trajectory up to time `c`. -/
/-
**ProbabilityTheory.Kernel.partialTraj_comp_partialTraj** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.Kernel`。
形式化陈述：partialTraj_comp_partialTraj (hab : a <= b) (hbc : b <= c) : partialTraj κ
 b c ∘ₖ partialTraj κ a b = partialTraj κ a c
参数：hab : a <= b；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_self`：partialTraj_self (a : Nat) : 
partialTraj κ a a = Kernel.id
· 使用定理 `ProbabilityTheory.Kernel.id_comp`：∀ {α : Type u_1} {β : Type u_2} {mα : 
MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel α β), 
  ProbabilityTheory.Ke…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_succ_eq_comp`：partialTraj_succ_eq_c
omp (hab : a <= b) : partialTraj κ a (b + 1) = partialTraj κ b (b + 1) ∘ₖ partia
lTraj κ a b
· 使用定理 `ProbabilityTheory.Kernel.comp_assoc`：comp_assoc {δ : Type*} {mδ : Measur
ableSpace δ} (ξ : Kernel γ δ) (η : Kernel β γ) (κ : Kernel α β) : ξ ∘ₖ η ∘ₖ κ = 
ξ ∘ₖ (η ∘ₖ κ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
Given the trajectory up to time `a`, `partialTraj κ a b` gives the distribution 
of
the trajectory up to time `b`. Then plugging this into `partialTraj κ b c` gives
the distribution of the trajectory up to time `c`.
-/
theorem partialTraj_comp_partialTraj (hab : a ≤ b) (hbc : b ≤ c) :
    partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c := by
  induction c, hbc using Nat.le_induction with
  | base => simp
  | succ k h hk => rw [partialTraj_succ_eq_comp h, comp_assoc, hk,
      ← partialTraj_succ_eq_comp (hab.trans h)]

/-- This is a specific lemma used in the proof of `partialTraj_eq_prod`. It is the main rewrite step
and stating it as a separate lemma avoids using extensionality of kernels, which would generate
a lot of measurability subgoals. -/
/-
**ProbabilityTheory.Kernel.fst_prod_comp_id_prod** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.Kernel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a specific lemma used in the proof of `partialTraj_eq_prod`. It is the m
ain rewrite step
and stating it as a separate lemma avoids using extensionality of kernels, which
 would generate
a lot of measurability subgoals.
-/
private lemma fst_prod_comp_id_prod {X Y Z : Type*} {mX : MeasurableSpace X}
    {mY : MeasurableSpace Y} {mZ : MeasurableSpace Z} (κ : Kernel X Y) [IsSFiniteKernel κ]
    (η : Kernel (X × Y) Z) [IsSFiniteKernel η] :
    ((deterministic Prod.fst measurable_fst) ×ₖ η) ∘ₖ (Kernel.id ×ₖ κ) =
    Kernel.id ×ₖ (η ∘ₖ (Kernel.id ×ₖ κ)) := by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, lintegral_id_prod (Kernel.measurable_coe _ ms),
    deterministic_prod_apply' _ _ _ ms, id_prod_apply' _ _ ms,
    comp_apply' _ _ _ (measurable_prodMk_left ms),
    lintegral_id_prod (η.measurable_coe (measurable_prodMk_left ms))]

/-- This is a technical lemma saying that `partialTraj κ a b` consists of two independent parts, the
first one being the identity. It allows to compute integrals. -/
/-
**ProbabilityTheory.Kernel.partialTraj_eq_prod** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：partialTraj_eq_prod [forall n, IsSFiniteKernel (κ n)] (a b : Nat) : partia
lTraj κ a b = (Kernel.id ×ₖ (partialTraj κ a b).map (restrict₂ Ioc_subset_Iic_se
lf)).map (IicProdIoc a b)
参数：κ n；a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ioc_subset_Iic_self`：Ioc_subset_Iic_self : Ioc a b subseteq Iic b
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Preorder.measurable_frestrictLe₂`：measurable_frestrictLe₂ {a b : α} (hab
 : a <= b) : Measurable (frestrictLe₂ (π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_le`：partialTraj_le (hba : b <= a) :
 partialTraj κ a b = deterministic (frestrictLe₂ hba) (measurable_frestrictLe₂ _
)
· 使用引理 `IicProdIoc_le`：IicProdIoc_le {a b : ι} (hba : b <= a) : IicProdIoc (X
· 使用引理 `ProbabilityTheory.Kernel.map_comp_right`：map_comp_right (κ : Kernel α β)
 {f : β -> γ} (hf : Measurable f) {g : γ -> δ} (hg : Measurable g) : κ.map (g ∘ 
f) = (κ.map f).map g
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.fst_eq`：fst_eq (κ : Kernel α (β × γ)) : fst κ =
 map κ Prod.fst
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Finset.measurable_restrict₂`：Finset.measurable_restrict₂ {s t : Finset δ
} (hst : s subseteq t) : Measurable (Finset.restrict₂ (π
· 使用引理 `ProbabilityTheory.Kernel.deterministic_map`：deterministic_map {f : α -> 
β} (hf : Measurable f) {g : β -> γ} (hg : Measurable g) : (deterministic f hf).m
ap g = deterministic (g ∘ f) (hg…
· 使用定理 `ProbabilityTheory.Kernel.fst_prod`：∀ {α : Type u_1} {β : Type u_2} {mα :
 MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : MeasurableSp
ace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用引理 `ProbabilityTheory.Kernel.id_map`：id_map {f : α -> β} (hf : Measurable f)
 : Kernel.id.map f = deterministic f hf
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_self`：partialTraj_self (a : Nat) : 
partialTraj κ a a = Kernel.id
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用引理 `measurable_IicProdIoc`：measurable_IicProdIoc {m n : ι} : Measurable (Iic
ProdIoc (X
· 使用引理 `ProbabilityTheory.Kernel.prod_apply`：prod_apply (κ : Kernel α β) [IsSFin
iteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) : (κ ×ₖ η) a = (κ a).p
rod (η a)
· 使用引理 `IicProdIoc_self`：IicProdIoc_self (a : ι) : IicProdIoc (X
· 使用定理 `MeasureTheory.Measure.fst.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β]   (ρ : MeasureTheory.Measure (α 
× β)), ρ.fst = Measu…
· 使用引理 `MeasureTheory.Measure.fst_prod`：fst_prod [IsProbabilityMeasure ν] : (μ.p
rod ν).fst = μ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
（共 85 条，此处仅展示前 30 条）

--- 原说明 ---
This is a technical lemma saying that `partialTraj κ a b` consists of two indepe
ndent parts, the
first one being the identity. It allows to compute integrals.
-/
lemma partialTraj_eq_prod [∀ n, IsSFiniteKernel (κ n)] (a b : ℕ) :
    partialTraj κ a b =
    (Kernel.id ×ₖ (partialTraj κ a b).map (restrict₂ Ioc_subset_Iic_self)).map
    (IicProdIoc a b) := by
  obtain hba | hab := le_total b a
  · rw [partialTraj_le hba, IicProdIoc_le hba, map_comp_right, ← fst_eq, deterministic_map,
      fst_prod, id_map]
    all_goals fun_prop
  induction b, hab using Nat.le_induction with
  | base =>
    ext1 x
    rw [partialTraj_self, id_map, map_apply, prod_apply, IicProdIoc_self, ← Measure.fst,
    Measure.fst_prod]
    all_goals fun_prop
  | succ k h hk =>
    have : (IicProdIoc (X := X) k (k + 1)) ∘ (Prod.map (IicProdIoc a k) id) =
        (IicProdIoc (h.trans k.le_succ) ∘ (Prod.map id (IocProdIoc a k (k + 1)))) ∘
        prodAssoc := by
      ext x i
      simp only [IicProdIoc_def, MeasurableEquiv.IicProdIoc, MeasurableEquiv.coe_mk,
        Equiv.coe_fn_mk, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
        Nat.succ_eq_add_one, IocProdIoc]
      split_ifs <;> try rfl
      lia
    nth_rw 1 [← partialTraj_comp_partialTraj h k.le_succ, hk, partialTraj_succ_self, comp_map,
      comap_map_comm, comap_prod, id_comap, ← id_map, map_prod_eq, ← map_comp_right, this,
      map_comp_right, id_prod_eq, prodAssoc_prod, map_comp_right, ← map_prod_map, map_id,
      ← map_comp, map_apply_eq_iff_map_symm_apply_eq, fst_prod_comp_id_prod, ← map_comp_right,
      ← coe_IicProdIoc (h.trans k.le_succ), symm_comp_self, map_id,
      deterministic_congr IicProdIoc_comp_restrict₂.symm, ← deterministic_comp_deterministic,
      comp_deterministic_eq_comap, ← comap_prod, ← map_comp, ← comp_map, ← hk,
      ← partialTraj_comp_partialTraj h k.le_succ, partialTraj_succ_self, map_comp, map_comp,
      ← map_comp_right, ← id_map, map_prod_eq, ← map_comp_right]
    · rfl
    all_goals fun_prop

variable [∀ n, IsMarkovKernel (κ n)]

set_option backward.isDefEq.respectTransparency false in
/-- The pushforward of `partialTraj κ a (a + 1)` along the the point at time `a + 1` is `κ a`. -/
/-
**ProbabilityTheory.Kernel.map_partialTraj_succ_self** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：map_partialTraj_succ_self (a : Nat) : (partialTraj κ a (a + 1)).map (fun x
 => x ⟨a + 1, mem_Iic.2 le_rfl⟩) = κ a
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_succ_self`：partialTraj_succ_self (a
 : Nat) : partialTraj κ a (a + 1) = (Kernel.id ×ₖ ((κ a).map (piSingleton a))).m
ap (IicProdIoc a (a + 1))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.map_comp_right`：map_comp_right (κ : Kernel α β)
 {f : β -> γ} (hf : Measurable f) {g : γ -> δ} (hg : Measurable g) : κ.map (g ∘ 
f) = (κ.map f).map g
· 使用引理 `measurable_IicProdIoc`：measurable_IicProdIoc {m n : ι} : Measurable (Iic
ProdIoc (X
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `ProbabilityTheory.Kernel.snd_eq`：snd_eq (κ : Kernel α (β × γ)) : snd κ =
 map κ Prod.snd
· 使用定理 `ProbabilityTheory.Kernel.snd_prod`：∀ {α : Type u_1} {β : Type u_2} {mα :
 MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : MeasurableSp
ace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.map`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The pushforward of `partialTraj κ a (a + 1)` along the the point at time `a + 1`
 is `κ a`.
-/
lemma map_partialTraj_succ_self (a : ℕ) :
    (partialTraj κ a (a + 1)).map (fun x ↦ x ⟨a + 1, mem_Iic.2 le_rfl⟩) = κ a := by
  have hp : (fun x : Π n : Iic (a + 1), X n ↦ x ⟨a + 1, mem_Iic.2 le_rfl⟩) ∘ IicProdIoc a (a + 1) =
      (piSingleton a).symm ∘ Prod.snd := by
    ext
    simp [_root_.IicProdIoc, piSingleton]
  rw [partialTraj_succ_self, ← map_comp_right _ (by fun_prop) (by fun_prop), hp,
    map_comp_right _ (by fun_prop) (by fun_prop), ← snd_eq, snd_prod,
    ← map_comp_right _ (by fun_prop) (by fun_prop), symm_comp_self, map_id]
/-
**ProbabilityTheory.Kernel.partialTraj_succ_map_frestrictLe** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory.Kernel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma partialTraj_succ_map_frestrictLe₂ (a b : ℕ) :
    (partialTraj κ a (b + 1)).map (frestrictLe₂ b.le_succ) = partialTraj κ a b := by
  obtain hab | hba := le_or_gt a b
  · have := IsMarkovKernel.map (κ b) (piSingleton b).measurable
    rw [partialTraj_succ_eq_comp hab, map_comp, partialTraj_succ_self, ← map_comp_right,
      frestrictLe₂_comp_IicProdIoc, ← fst_eq, fst_prod, id_comp]
    all_goals fun_prop
  · rw [partialTraj_le (Nat.succ_le_of_lt hba), partialTraj_le hba.le, deterministic_map]
    · rfl
    · fun_prop

/-- If we restrict the distribution of the trajectory up to time `c` to times `≤ b` we get
the trajectory up to time `b`. -/
/-
**ProbabilityTheory.Kernel.partialTraj_map_frestrictLe** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we restrict the distribution of the trajectory up to time `c` to times `≤ b` 
we get
the trajectory up to time `b`.
-/
theorem partialTraj_map_frestrictLe₂ (a : ℕ) (hbc : b ≤ c) :
    (partialTraj κ a c).map (frestrictLe₂ hbc) = partialTraj κ a b := by
  induction c, hbc using Nat.le_induction with
  | base => exact map_id ..
  | succ k h hk =>
    rw [← hk, ← frestrictLe₂_comp_frestrictLe₂ h k.le_succ, map_comp_right,
      partialTraj_succ_map_frestrictLe₂]
    all_goals fun_prop
/-
**ProbabilityTheory.Kernel.partialTraj_map_frestrictLe** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory.Kernel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma partialTraj_map_frestrictLe₂_apply (x₀ : Π i : Iic a, X i) (hbc : b ≤ c) :
    (partialTraj κ a c x₀).map (frestrictLe₂ hbc) = partialTraj κ a b x₀ := by
  rw [← map_apply _ (by fun_prop), partialTraj_map_frestrictLe₂]

/-- Same as `partialTraj_comp_partialTraj` but only assuming `a ≤ b`. It requires Markov kernels. -/
/-
**ProbabilityTheory.Kernel.partialTraj_comp_partialTraj'** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory.Kernel`。
形式化陈述：partialTraj_comp_partialTraj' (c : Nat) (hab : a <= b) : partialTraj κ b c
 ∘ₖ partialTraj κ a b = partialTraj κ a c
参数：c : Nat；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.partialTraj_comp_partialTraj`：partialTraj_comp_
partialTraj (hab : a <= b) (hbc : b <= c) : partialTraj κ b c ∘ₖ partialTraj κ a
 b = partialTraj κ a c
· 使用定理 `Preorder.measurable_frestrictLe₂`：measurable_frestrictLe₂ {a b : α} (hab
 : a <= b) : Measurable (frestrictLe₂ (π
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_le`：partialTraj_le (hba : b <= a) :
 partialTraj κ a b = deterministic (frestrictLe₂ hba) (measurable_frestrictLe₂ _
)
· 使用定理 `ProbabilityTheory.Kernel.deterministic_comp_eq_map`：deterministic_comp_e
q_map (hf : Measurable f) (κ : Kernel α β) : deterministic f hf ∘ₖ κ = map κ f
· 使用定理 `ProbabilityTheory.Kernel.partialTraj_map_frestrictLe₂`：partialTraj_map_f
restrictLe₂ (a : Nat) (hbc : b <= c) : (partialTraj κ a c).map (frestrictLe₂ hbc
) = partialTraj κ a b

--- 原说明 ---
Same as `partialTraj_comp_partialTraj` but only assuming `a ≤ b`. It requires Ma
rkov kernels.
-/
lemma partialTraj_comp_partialTraj' (c : ℕ) (hab : a ≤ b) :
    partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c := by
  obtain hbc | hcb := le_total b c
  · rw [partialTraj_comp_partialTraj hab hbc]
  · rw [partialTraj_le hcb, deterministic_comp_eq_map, partialTraj_map_frestrictLe₂]

/-- Same as `partialTraj_comp_partialTraj` but only assuming `b ≤ c`. It requires Markov kernels. -/
/-
**ProbabilityTheory.Kernel.partialTraj_comp_partialTraj''** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory.Kernel`。
形式化陈述：partialTraj_comp_partialTraj'' {b c : Nat} (hcb : c <= b) : partialTraj κ 
b c ∘ₖ partialTraj κ a b = partialTraj κ a c
参数：hcb : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Preorder.measurable_frestrictLe₂`：measurable_frestrictLe₂ {a b : α} (hab
 : a <= b) : Measurable (frestrictLe₂ (π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_le`：partialTraj_le (hba : b <= a) :
 partialTraj κ a b = deterministic (frestrictLe₂ hba) (measurable_frestrictLe₂ _
)
· 使用定理 `ProbabilityTheory.Kernel.deterministic_comp_eq_map`：deterministic_comp_e
q_map (hf : Measurable f) (κ : Kernel α β) : deterministic f hf ∘ₖ κ = map κ f
· 使用定理 `ProbabilityTheory.Kernel.partialTraj_map_frestrictLe₂`：partialTraj_map_f
restrictLe₂ (a : Nat) (hbc : b <= c) : (partialTraj κ a c).map (frestrictLe₂ hbc
) = partialTraj κ a b

--- 原说明 ---
Same as `partialTraj_comp_partialTraj` but only assuming `b ≤ c`. It requires Ma
rkov kernels.
-/
lemma partialTraj_comp_partialTraj'' {b c : ℕ} (hcb : c ≤ b) :
    partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c := by
  rw [partialTraj_le hcb, deterministic_comp_eq_map, partialTraj_map_frestrictLe₂]

end Basic

section lmarginalPartialTraj

/-! ### Integrating against `partialTraj` -/

variable (κ)

/-- This function computes the integral of a function `f` against `partialTraj`,
and allows to view it as a function depending on all the variables.

This is inspired by `MeasureTheory.lmarginal`, to be able to write
`lmarginalPartialTraj κ b c (lmarginalPartialTraj κ a b f) = lmarginalPartialTraj κ a c`. -/
/-
**ProbabilityTheory.Kernel.lmarginalPartialTraj** 是 Mathlib 中的一个定义，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：lmarginalPartialTraj (a b : Nat) (f : (Π n, X n) -> Real>=0∞) (x₀ : Π n, X
 n) : Real>=0∞
参数：a b : Nat；f : (Π n, X n) -> Real>=0∞；x₀ : Π n, X n。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This function computes the integral of a function `f` against `partialTraj`,
and allows to view it as a function depending on all the variables.

This is inspired by `MeasureTheory.lmarginal`, to be able to write
`lmarginalPartialTraj κ b c (lmarginalPartialTraj κ a b f) = lmarginalPartialTra
j κ a c`.
-/
noncomputable def lmarginalPartialTraj (a b : ℕ) (f : (Π n, X n) → ℝ≥0∞) (x₀ : Π n, X n) : ℝ≥0∞ :=
  ∫⁻ z : (i : Iic b) → X i, f (updateFinset x₀ _ z) ∂(partialTraj κ a b (frestrictLe a x₀))

/-- If `b ≤ a`, then integrating `f` against `partialTraj κ a b` does nothing. -/
/-
**ProbabilityTheory.Kernel.lmarginalPartialTraj_le** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：lmarginalPartialTraj_le (hba : b <= a) {f : (Π n, X n) -> Real>=0∞} (mf : 
Measurable f) : lmarginalPartialTraj κ a b f = f
参数：hba : b <= a；Π n, X n；mf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.lmarginalPartialTraj.eq_1`：∀ {X : ℕ → Type u_1}
 {mX : (n : ℕ) → MeasurableSpace (X n)}   (κ : (n : ℕ) → ProbabilityTheory.Kerne
l ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `Preorder.measurable_frestrictLe₂`：measurable_frestrictLe₂ {a b : α} (hab
 : a <= b) : Measurable (frestrictLe₂ (π
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_le`：partialTraj_le (hba : b <= a) :
 partialTraj κ a b = deterministic (frestrictLe₂ hba) (measurable_frestrictLe₂ _
)
· 使用定理 `ProbabilityTheory.Kernel.lintegral_deterministic'`：lintegral_determinist
ic' {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Measurable g) (hf : Measurabl
e f) : ∫⁻ x, f x ∂deterministic g hg a …
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_updateFinset`：measurable_updateFinset [DecidableEq δ] {s : Fi
nset δ} {x : Π i, X i} : Measurable (updateFinset x s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `b ≤ a`, then integrating `f` against `partialTraj κ a b` does nothing.
-/
lemma lmarginalPartialTraj_le (hba : b ≤ a) {f : (Π n, X n) → ℝ≥0∞} (mf : Measurable f) :
    lmarginalPartialTraj κ a b f = f := by
  ext x₀
  rw [lmarginalPartialTraj, partialTraj_le hba, Kernel.lintegral_deterministic']
  · congr with i
    simp [updateFinset]
  · exact mf.comp measurable_updateFinset

variable {κ}
/-
**ProbabilityTheory.Kernel.lmarginalPartialTraj_mono** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：lmarginalPartialTraj_mono (a b : Nat) {f g : (Π n, X n) -> Real>=0∞} (hfg 
: f <= g) (x₀ : Π n, X n) : lmarginalPartialTraj κ a b f x₀ <= lmarginalPartialT
raj κ a b g x₀
参数：a b : Nat；Π n, X n；hfg : f <= g；x₀ : Π n, X n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
-/
lemma lmarginalPartialTraj_mono (a b : ℕ) {f g : (Π n, X n) → ℝ≥0∞} (hfg : f ≤ g) (x₀ : Π n, X n) :
    lmarginalPartialTraj κ a b f x₀ ≤ lmarginalPartialTraj κ a b g x₀ :=
  lintegral_mono fun _ ↦ hfg _

/-- Integrating `f` against `partialTraj κ a b x` is the same as integrating only over the variables
  from `x_{a+1}` to `x_b`. -/
/-
**ProbabilityTheory.Kernel.lmarginalPartialTraj_eq_lintegral_map** 是 Mathlib 中的一
个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：lmarginalPartialTraj_eq_lintegral_map [forall n, IsSFiniteKernel (κ n)] {f
 : (Π n, X n) -> Real>=0∞} (mf : Measurable f) (x₀ : Π n, X n) : lmarginalPartia
lTraj κ a b f x₀ = ∫⁻ x : (Π i : Ioc a b, X i), f (updateFinset x₀ _ x) ∂(partia
lTraj κ a b).map (restrict₂ Ioc_subset_Iic_self) (frestrictLe a x₀)
参数：κ n；Π n, X n；mf : Measurable f；x₀ : Π n, X n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ioc_subset_Iic_self`：Ioc_subset_Iic_self : Ioc a b subseteq Iic b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.lmarginalPartialTraj.eq_1`：∀ {X : ℕ → Type u_1}
 {mX : (n : ℕ) → MeasurableSpace (X n)}   (κ : (n : ℕ) → ProbabilityTheory.Kerne
l ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_eq_prod`：partialTraj_eq_prod [foral
l n, IsSFiniteKernel (κ n)] (a b : Nat) : partialTraj κ a b = (Kernel.id ×ₖ (par
tialTraj κ a b).map (restrict₂ Ioc…
· 使用定理 `ProbabilityTheory.Kernel.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} 
{mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Measura
bleSpace γ} {f : β → γ} (κ :…
· 使用引理 `measurable_IicProdIoc`：measurable_IicProdIoc {m n : ι} : Measurable (Iic
ProdIoc (X
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_updateFinset`：measurable_updateFinset [DecidableEq δ] {s : Fi
nset δ} {x : Π i, X i} : Measurable (updateFinset x s)
· 使用定理 `ProbabilityTheory.Kernel.lintegral_id_prod`：lintegral_id_prod {f : (α × 
β) -> Real>=0∞} (hf : Measurable f) (κ : Kernel α β) [IsSFiniteKernel κ] (a : α)
 : ∫⁻ p, f p ∂(Kernel.id ×ₖ κ) a…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.map`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.instIsSFiniteKernelForallValNatMemFinsetIicPart
ialTraj`：∀ {X : ℕ → Type u_1} {mX : (n : ℕ) → MeasurableSpace (X n)}   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc

--- 原说明 ---
Integrating `f` against `partialTraj κ a b x` is the same as integrating only ov
er the variables
  from `x_{a+1}` to `x_b`.
-/
lemma lmarginalPartialTraj_eq_lintegral_map [∀ n, IsSFiniteKernel (κ n)] {f : (Π n, X n) → ℝ≥0∞}
    (mf : Measurable f) (x₀ : Π n, X n) :
    lmarginalPartialTraj κ a b f x₀ =
    ∫⁻ x : (Π i : Ioc a b, X i), f (updateFinset x₀ _ x)
      ∂(partialTraj κ a b).map (restrict₂ Ioc_subset_Iic_self) (frestrictLe a x₀) := by
  nth_rw 1 [lmarginalPartialTraj, partialTraj_eq_prod, lintegral_map, lintegral_id_prod]
  · congrm ∫⁻ _, f (fun i ↦ ?_) ∂_
    simp only [updateFinset, mem_Iic, IicProdIoc_def,
      frestrictLe_apply, mem_Ioc]
    split_ifs <;> try rfl
    all_goals lia
  all_goals fun_prop

/-- Integrating `f` against `partialTraj κ a (a + 1)` is the same as integrating against `κ a`. -/
/-
**ProbabilityTheory.Kernel.lmarginalPartialTraj_succ** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：lmarginalPartialTraj_succ [forall n, IsSFiniteKernel (κ n)] (a : Nat) {f :
 (Π n, X n) -> Real>=0∞} (mf : Measurable f) (x₀ : Π n, X n) : lmarginalPartialT
raj κ a (a + 1) f x₀ = ∫⁻ x : X (a + 1), f (update x₀ _ x) ∂κ a (frestrictLe a x
₀)
参数：κ n；a : Nat；Π n, X n；mf : Measurable f；x₀ : Π n, X n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.lmarginalPartialTraj.eq_1`：∀ {X : ℕ → Type u_1}
 {mX : (n : ℕ) → MeasurableSpace (X n)}   (κ : (n : ℕ) → ProbabilityTheory.Kerne
l ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用引理 `ProbabilityTheory.Kernel.partialTraj_succ_self`：partialTraj_succ_self (a
 : Nat) : partialTraj κ a (a + 1) = (Kernel.id ×ₖ ((κ a).map (piSingleton a))).m
ap (IicProdIoc a (a + 1))
· 使用定理 `ProbabilityTheory.Kernel.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} 
{mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Measura
bleSpace γ} {f : β → γ} (κ :…
· 使用引理 `measurable_IicProdIoc`：measurable_IicProdIoc {m n : ι} : Measurable (Iic
ProdIoc (X
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_updateFinset`：measurable_updateFinset [DecidableEq δ] {s : Fi
nset δ} {x : Π i, X i} : Measurable (updateFinset x s)
· 使用定理 `ProbabilityTheory.Kernel.lintegral_id_prod`：lintegral_id_prod {f : (α × 
β) -> Real>=0∞} (hf : Measurable f) (κ : Kernel α β) [IsSFiniteKernel κ] (a : α)
 : ∫⁻ p, f p ∂(Kernel.id ×ₖ κ) a…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.map`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc

--- 原说明 ---
Integrating `f` against `partialTraj κ a (a + 1)` is the same as integrating aga
inst `κ a`.
-/
lemma lmarginalPartialTraj_succ [∀ n, IsSFiniteKernel (κ n)] (a : ℕ)
    {f : (Π n, X n) → ℝ≥0∞} (mf : Measurable f) (x₀ : Π n, X n) :
    lmarginalPartialTraj κ a (a + 1) f x₀ =
      ∫⁻ x : X (a + 1), f (update x₀ _ x) ∂κ a (frestrictLe a x₀) := by
  rw [lmarginalPartialTraj, partialTraj_succ_self, lintegral_map, lintegral_id_prod, lintegral_map]
  · congrm ∫⁻ x, f (fun i ↦ ?_) ∂_
    simp only [updateFinset, mem_Iic, IicProdIoc_def, frestrictLe_apply, piSingleton,
      MeasurableEquiv.coe_mk, update]
    split_ifs with h1 h2 h3 <;> try rfl
    all_goals lia
  all_goals fun_prop

@[fun_prop]
/-
**ProbabilityTheory.Kernel.measurable_lmarginalPartialTraj** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：measurable_lmarginalPartialTraj (a b : Nat) {f : (Π n, X n) -> Real>=0∞} (
hf : Measurable f) : Measurable (lmarginalPartialTraj κ a b f)
参数：a b : Nat；Π n, X n；hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Preorder.measurable_frestrictLe`：measurable_frestrictLe (a : α) : Measur
able (frestrictLe (π
· 使用定理 `Measurable.lintegral_kernel_prod_left`：∀ {α : Type u_1} {β : Type u_2} {
mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kernel α
 β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comap`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ :
 MeasurableSpace γ} {g : γ → α} (κ :…
· 使用定理 `ProbabilityTheory.Kernel.instIsSFiniteKernelForallValNatMemFinsetIicPart
ialTraj`：∀ {X : ℕ → Type u_1} {mX : (n : ℕ) → MeasurableSpace (X n)}   {κ : (n :
 ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_updateFinset'`：measurable_updateFinset' [DecidableEq δ] {s : 
Finset δ} : Measurable (fun p : (Π i, X i) × (Π i : s, X i) => updateFinset p.1 
s p.2)
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
-/
lemma measurable_lmarginalPartialTraj (a b : ℕ) {f : (Π n, X n) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (lmarginalPartialTraj κ a b f) := by
  unfold lmarginalPartialTraj
  let g : ((i : Iic b) → X i) × (Π n, X n) → ℝ≥0∞ := fun c ↦ f (updateFinset c.2 _ c.1)
  let η : Kernel (Π n, X n) (Π i : Iic b, X i) :=
    (partialTraj κ a b).comap (frestrictLe a) (measurable_frestrictLe _)
  change Measurable fun x₀ ↦ ∫⁻ z : (i : Iic b) → X i, g (z, x₀) ∂η x₀
  fun_prop

/-- Integrating `f` against `partialTraj κ a b` and then against `partialTraj κ b c` is the same
as integrating `f` against `partialTraj κ a c`. -/
/-
**ProbabilityTheory.Kernel.lmarginalPartialTraj_self** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：lmarginalPartialTraj_self (hab : a <= b) (hbc : b <= c) {f : (Π n, X n) ->
 Real>=0∞} (hf : Measurable f) : lmarginalPartialTraj κ a b (lmarginalPartialTra
j κ b c f) = lmarginalPartialTraj κ a c f
参数：hab : a <= b；hbc : b <= c；Π n, X n；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.lmarginalPartialTraj_le`：lmarginalPartialTraj_l
e (hba : b <= a) {f : (Π n, X n) -> Real>=0∞} (mf : Measurable f) : lmarginalPar
tialTraj κ a b f = f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `ProbabilityTheory.Kernel.measurable_lmarginalPartialTraj`：measurable_lma
rginalPartialTraj (a b : Nat) {f : (Π n, X n) -> Real>=0∞} (hf : Measurable f) :
 Measurable (lmarginalPartialTraj κ a b f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Function.restrict_updateFinset`：restrict_updateFinset {s : Finset ι} (x 
: Π i, π i) (y : Π i : s, π i) : s.restrict (updateFinset x s y) = y
· 使用引理 `Function.updateFinset_updateFinset_of_subset`：updateFinset_updateFinset_
of_subset {s t : Finset ι} (hst : s subseteq t) (x : Π i, π i) (y : Π i : s, π i
) (z : Π i : t, π i) : updateFinse…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.lintegral_comp`：lintegral_comp (η : Kernel β γ)
 (κ : Kernel α β) (a : α) {g : γ -> Real>=0∞} (hg : Measurable g) : ∫⁻ c, g c ∂(
η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_updateFinset`：measurable_updateFinset [DecidableEq δ] {s : Fi
nset δ} {x : Π i, X i} : Measurable (updateFinset x s)
· 使用定理 `ProbabilityTheory.Kernel.partialTraj_comp_partialTraj`：partialTraj_comp_
partialTraj (hab : a <= b) (hbc : b <= c) : partialTraj κ b c ∘ₖ partialTraj κ a
 b = partialTraj κ a c

--- 原说明 ---
Integrating `f` against `partialTraj κ a b` and then against `partialTraj κ b c`
 is the same
as integrating `f` against `partialTraj κ a c`.
-/
theorem lmarginalPartialTraj_self (hab : a ≤ b) (hbc : b ≤ c)
    {f : (Π n, X n) → ℝ≥0∞} (hf : Measurable f) :
    lmarginalPartialTraj κ a b (lmarginalPartialTraj κ b c f) = lmarginalPartialTraj κ a c f := by
  ext x₀
  obtain rfl | hab := eq_or_lt_of_le hab <;> obtain rfl | hbc := eq_or_lt_of_le hbc
  · rw [lmarginalPartialTraj_le κ le_rfl (measurable_lmarginalPartialTraj _ _ hf)]
  · rw [lmarginalPartialTraj_le κ le_rfl (measurable_lmarginalPartialTraj _ _ hf)]
  · rw [lmarginalPartialTraj_le κ le_rfl hf]
  simp_rw [lmarginalPartialTraj, frestrictLe, restrict_updateFinset,
    updateFinset_updateFinset_of_subset (Iic_subset_Iic.2 hbc.le)]
  rw [← lintegral_comp, partialTraj_comp_partialTraj hab.le hbc.le]
  fun_prop

end lmarginalPartialTraj

end ProbabilityTheory.Kernel

open ProbabilityTheory Kernel

namespace DependsOn

/-! ### Lemmas about `lmarginalPartialTraj` and `DependsOn` -/

/-- If `f` only depends on the variables up to rank `a` and `a ≤ b`, integrating `f` against
`partialTraj κ b c` does nothing. -/
/-
**DependsOn.lmarginalPartialTraj_of_le** 是 Mathlib 中的一个定理，位于命名空间 `DependsOn`。
形式化陈述：lmarginalPartialTraj_of_le [forall n, IsMarkovKernel (κ n)] (c : Nat) {f :
 (Π n, X n) -> Real>=0∞} (mf : Measurable f) (hf : DependsOn f (Iic a)) (hab : a
 <= b) : lmarginalPartialTraj κ b c f = f
参数：κ n；c : Nat；Π n, X n；mf : Measurable f；hf : DependsOn f (Iic a)；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.Ioc_subset_Iic_self`：Ioc_subset_Iic_self : Ioc a b subseteq Iic b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.lmarginalPartialTraj_eq_lintegral_map`：lmargina
lPartialTraj_eq_lintegral_map [forall n, IsSFiniteKernel (κ n)] {f : (Π n, X n) 
-> Real>=0∞} (mf : Measurable f) (x₀ : Π n, X n) : l…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `MeasureTheory.lintegral_eq_const`：lintegral_eq_const [IsProbabilityMeasu
re μ] {f : α -> Real>=0∞} {c : Real>=0∞} (hf : forallᵐ x ∂μ, f x = c) : ∫⁻ x, f 
x ∂μ = c
· 使用定理 `ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [self : ProbabilityTh…
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.map`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Me
asurableSpace γ} {f : β → γ} (κ :…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelForallValNatMemFinsetIicParti
alTrajOfHAddOfNat`：∀ {X : ℕ → Type u_1} {mX : (n : ℕ) → MeasurableSpace (X n)}  
 {κ : (n : ℕ) → ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → X ↑i) (X (n +…
· 使用定理 `Finset.measurable_restrict₂`：Finset.measurable_restrict₂ {s t : Finset δ
} (hst : s subseteq t) : Measurable (Finset.restrict₂ (π
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a

--- 原说明 ---
If `f` only depends on the variables up to rank `a` and `a ≤ b`, integrating `f`
 against
`partialTraj κ b c` does nothing.
-/
theorem lmarginalPartialTraj_of_le [∀ n, IsMarkovKernel (κ n)] (c : ℕ) {f : (Π n, X n) → ℝ≥0∞}
    (mf : Measurable f) (hf : DependsOn f (Iic a)) (hab : a ≤ b) :
    lmarginalPartialTraj κ b c f = f := by
  ext x
  rw [lmarginalPartialTraj_eq_lintegral_map mf]
  refine @lintegral_eq_const _ _ _ ?_ _ _ (ae_of_all _ fun y ↦ hf fun i hi ↦ ?_)
  · refine @IsMarkovKernel.isProbabilityMeasure _ _ _ _ _ ?_ _
    exact IsMarkovKernel.map _ (by fun_prop)
  · simp_all only [coe_Iic, Set.mem_Iic, Function.updateFinset, mem_Ioc, dite_eq_right_iff]
    lia

/-- If `f` only depends on the variables uo to rank `a`, integrating beyond rank `a` is the same
as integrating up to rank `a`. -/
/-
**DependsOn.lmarginalPartialTraj_const_right** 是 Mathlib 中的一个定理，位于命名空间 `DependsO
n`。
形式化陈述：lmarginalPartialTraj_const_right [forall n, IsMarkovKernel (κ n)] {d : Nat
} {f : (Π n, X n) -> Real>=0∞} (mf : Measurable f) (hf : DependsOn f (Iic a)) (h
ac : a <= c) (had : a <= d) : lmarginalPartialTraj κ b c f = lmarginalPartialTra
j κ b d f
参数：κ n；Π n, X n；mf : Measurable f；hf : DependsOn f (Iic a)；hac : a <= c；had : a 
<= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.lmarginalPartialTraj_self`：lmarginalPartialTraj
_self (hab : a <= b) (hbc : b <= c) {f : (Π n, X n) -> Real>=0∞} (hf : Measurabl
e f) : lmarginalPartialTraj κ a b (lmarg…
· 使用定理 `DependsOn.lmarginalPartialTraj_of_le`：lmarginalPartialTraj_of_le [forall
 n, IsMarkovKernel (κ n)] (c : Nat) {f : (Π n, X n) -> Real>=0∞} (mf : Measurabl
e f) (hf : DependsOn f (Ii…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a

--- 原说明 ---
If `f` only depends on the variables uo to rank `a`, integrating beyond rank `a`
 is the same
as integrating up to rank `a`.
-/
theorem lmarginalPartialTraj_const_right [∀ n, IsMarkovKernel (κ n)] {d : ℕ} {f : (Π n, X n) → ℝ≥0∞}
    (mf : Measurable f) (hf : DependsOn f (Iic a)) (hac : a ≤ c) (had : a ≤ d) :
    lmarginalPartialTraj κ b c f = lmarginalPartialTraj κ b d f := by
  wlog hcd : c ≤ d generalizing c d
  · rw [this had hac (le_of_not_ge hcd)]
  obtain hbc | hcb := le_total b c
  · rw [← lmarginalPartialTraj_self hbc hcd mf, hf.lmarginalPartialTraj_of_le d mf hac]
  · rw [hf.lmarginalPartialTraj_of_le c mf (hac.trans hcb),
      hf.lmarginalPartialTraj_of_le d mf (hac.trans hcb)]

/-- If `f` only depends on variables up to rank `b`, its integral from `a` to `b` only depends on
variables up to rank `a`. -/
/-
**DependsOn.dependsOn_lmarginalPartialTraj** 是 Mathlib 中的一个定理，位于命名空间 `DependsOn`
。
形式化陈述：dependsOn_lmarginalPartialTraj [forall n, IsSFiniteKernel (κ n)] (a : Nat)
 {f : (Π n, X n) -> Real>=0∞} (hf : DependsOn f (Iic b)) (mf : Measurable f) : D
ependsOn (lmarginalPartialTraj κ a b f) (Iic a)
参数：κ n；a : Nat；Π n, X n；hf : DependsOn f (Iic b)；mf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.lmarginalPartialTraj_le`：lmarginalPartialTraj_l
e (hba : b <= a) {f : (Π n, X n) -> Real>=0∞} (mf : Measurable f) : lmarginalPar
tialTraj κ a b f = f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `Finset.Ioc_subset_Iic_self`：Ioc_subset_Iic_self : Ioc a b subseteq Iic b
· 使用引理 `ProbabilityTheory.Kernel.lmarginalPartialTraj_eq_lintegral_map`：lmargina
lPartialTraj_eq_lintegral_map [forall n, IsSFiniteKernel (κ n)] {f : (Π n, X n) 
-> Real>=0∞} (mf : Measurable f) (x₀ : Π n, X n) : l…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `DependsOn.updateFinset`：∀ {ι : Type u_2} {π : ι → Type u_3} [inst : Deci
dableEq ι] {α : Type u_1} {f : ((i : ι) → π i) → α} {s : Set ι},   DependsOn f s
 → ∀ {t : Fi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_sdiff`：coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ :
 Set α)
· 使用定理 `Finset.Iic_sdiff_Ioc_self_of_le`：Iic_sdiff_Ioc_self_of_le (hab : a <= b)
 : Iic b \ Ioc a b = Iic a

--- 原说明 ---
If `f` only depends on variables up to rank `b`, its integral from `a` to `b` on
ly depends on
variables up to rank `a`.
-/
theorem dependsOn_lmarginalPartialTraj [∀ n, IsSFiniteKernel (κ n)] (a : ℕ) {f : (Π n, X n) → ℝ≥0∞}
    (hf : DependsOn f (Iic b)) (mf : Measurable f) :
    DependsOn (lmarginalPartialTraj κ a b f) (Iic a) := by
  intro x y hxy
  obtain hba | hab := le_total b a
  · rw [Kernel.lmarginalPartialTraj_le κ hba mf]
    exact hf fun i hi ↦ hxy i (Iic_subset_Iic.2 hba hi)
  rw [lmarginalPartialTraj_eq_lintegral_map mf, lmarginalPartialTraj_eq_lintegral_map mf]
  congrm ∫⁻ z : _, ?_ ∂(partialTraj κ a b).map _ (fun i ↦ ?_)
  · exact hxy i.1 i.2
  · refine hf.updateFinset _ ?_
    rwa [← coe_sdiff, Iic_sdiff_Ioc_self_of_le hab]

end DependsOn

end partialTraj

