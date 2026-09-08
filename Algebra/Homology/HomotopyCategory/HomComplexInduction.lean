/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# Construction of cochains by induction

Let `K` and `L` be cochain complexes in a preadditive category `C`.
We provide an API to construct a cochain in `Cochain K L d` in the following
situation. Assume that `X n : Set (Cochain K L d)` is a sequence of subsets
of `Cochain K L d`, and `φ n : X n → X (n + 1)` is a sequence of maps such
that for a certain `p₀ : ℕ` and any `x : X n`, `φ n x` and `x` coincide
up to the degree `p₀ + n`, then we construct a cochain
`InductionUp.limitSequence` in `Cochain K L d` which coincides with the
`n`th-iteration of `φ` evaluated on `x₀` up to the degree `p₀ + n` for any `n : ℕ`.

-/

@[expose] public section

universe v u

open CategoryTheory

namespace CochainComplex.HomComplex.Cochain

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : CochainComplex C ℤ}

/-- Given `p₀ : ℤ`, this is the condition on two cochains `α` and `β` in `Cochain K L N`
saying that `α.v p q _ = β.v p q _` when `p ≤ p₀`. -/
/-
**CochainComplex.HomComplex.Cochain.EqUpTo** 是 Mathlib 中的一个定义，位于命名空间 `CochainCom
plex.HomComplex.Cochain`。
形式化陈述：EqUpTo {n : Int} (α β : Cochain K L n) (p₀ : Int) : Prop
参数：α β : Cochain K L n；p₀ : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `p₀ : ℤ`, this is the condition on two cochains `α` and `β` in `Cochain K 
L N`
saying that `α.v p q _ = β.v p q _` when `p ≤ p₀`.
-/
def EqUpTo {n : ℤ} (α β : Cochain K L n) (p₀ : ℤ) : Prop :=
  ∀ (p q : ℤ) (hpq : p + n = q), p ≤ p₀ → α.v p q hpq = β.v p q hpq

namespace InductionUp

variable {d : ℤ} {X : ℕ → Set (Cochain K L d)} (φ : ∀ (n : ℕ), X n → X (n + 1))
  {p₀ : ℤ} (hφ : ∀ (n : ℕ) (x : X n), (φ n x).val.EqUpTo x.val (p₀ + n)) (x₀ : X 0)

/-- Assuming we have a sequence of subsets `X n : Set (Cochain K L d)` for all `n : ℕ`,
a sequence of maps `φ n : X n → X (n + 1)` for `n : ℕ`, and an element `x₀ : X 0`,
this is the dependent sequence in `∀ (n : ℕ), X n` obtained by evaluation iterations of `φ`
on `x₀`. -/
/-
**CochainComplex.HomComplex.Cochain.InductionUp.sequence** 是 Mathlib 中的一个定义，位于命名
空间 `CochainComplex.HomComplex.Cochain.InductionUp`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Preadditive C] →       {K L : CochainComplex C ℤ} →         {d :
 ℤ} →           {X : ℕ → Set (CochainComplex.HomComplex.Cochain K L d)} →       
      ((n : ℕ) → ↑(X n) → ↑(X (n + 1))) → ↑(X 0) → (n : ℕ) → ↑(X n)
参数：CochainComplex.HomComplex.Cochain K L d；(n : ℕ) → ↑(X n) → ↑(X (n + 1))；X 0；n
 : ℕ；X n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assuming we have a sequence of subsets `X n : Set (Cochain K L d)` for all `n : 
ℕ`,
a sequence of maps `φ n : X n → X (n + 1)` for `n : ℕ`, and an element `x₀ : X 0
`,
this is the dependent sequence in `∀ (n : ℕ), X n` obtained by evaluation iterat
ions of `φ`
on `x₀`.
-/
def sequence : ∀ n, X n
  | 0 => x₀
  | n + 1 => φ n (sequence n)

include hφ in
/-
**CochainComplex.HomComplex.Cochain.InductionUp.sequence_eqUpTo** 是 Mathlib 中的一个
引理，位于命名空间 `CochainComplex.HomComplex.Cochain.InductionUp`。
形式化陈述：sequence_eqUpTo (n₁ n₂ : Nat) (h : n₁ <= n₂) : (sequence φ x₀ n₁).val.EqUp
To (sequence φ x₀ n₂).val (p₀ + n₁)
参数：n₁ n₂ : Nat；h : n₁ <= n₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma sequence_eqUpTo (n₁ n₂ : ℕ) (h : n₁ ≤ n₂) :
    (sequence φ x₀ n₁).val.EqUpTo (sequence φ x₀ n₂).val (p₀ + n₁) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k generalizing n₁ with
  | zero => intro _ _ _ _; simp
  | succ k hk =>
    intro p q hpq hp
    rw [hk n₁ p q hpq hp, ← hφ (n₁ + k) (sequence φ x₀ (n₁ + k)) p q hpq (by lia)]
    dsimp [sequence]

/-- Assuming we have a sequence of subsets `X n : Set (Cochain K L d)` for all `n : ℕ`,
a sequence of maps `φ n : X n → X (n + 1)` for `n : ℕ`, and an element `x₀ : X 0`,
and under the assumption that for any `x : X n` the cochain `φ n x` coincides
with `x` up to the degree `p₀ + n`, this is a cochain in `Cochain K L d` which
can be understood as the "limit" of the sequence of cochains obtained by
evaluating iterations of `φ` on `x₀`. -/
@[nolint unusedArguments]
/-
**CochainComplex.HomComplex.Cochain.InductionUp.limitSequence** 是 Mathlib 中的一个定义
，位于命名空间 `CochainComplex.HomComplex.Cochain.InductionUp`。
形式化陈述：limitSequence (_ : forall (n : Nat) (x : X n), (φ n x).val.EqUpTo x.val (p
₀ + n)) (x₀ : X 0) : Cochain K L d
参数：_ : forall (n : Nat) (x : X n), (φ n x).val.EqUpTo x.val (p₀ + n)；x₀ : X 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assuming we have a sequence of subsets `X n : Set (Cochain K L d)` for all `n : 
ℕ`,
a sequence of maps `φ n : X n → X (n + 1)` for `n : ℕ`, and an element `x₀ : X 0
`,
and under the assumption that for any `x : X n` the cochain `φ n x` coincides
with `x` up to the degree `p₀ + n`, this is a cochain in `Cochain K L d` which
can be understood as the "limit" of the sequence of cochains obtained by
evaluating iterations of `φ` on `x₀`.
-/
def limitSequence (_ : ∀ (n : ℕ) (x : X n), (φ n x).val.EqUpTo x.val (p₀ + n)) (x₀ : X 0) :
    Cochain K L d :=
  Cochain.mk (fun p q hpq => (sequence φ x₀ (p - p₀).toNat).1.v p q hpq)
/-
**CochainComplex.HomComplex.Cochain.InductionUp.limitSequence_eqUpTo** 是 Mathlib
 中的一个引理，位于命名空间 `CochainComplex.HomComplex.Cochain.InductionUp`。
形式化陈述：limitSequence_eqUpTo (n : Nat) : (limitSequence φ hφ x₀).EqUpTo (sequence 
φ x₀ n).1 (p₀ + n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.InductionUp.sequence_eqUpTo`：sequence_
eqUpTo (n₁ n₂ : Nat) (h : n₁ <= n₂) : (sequence φ x₀ n₁).val.EqUpTo (sequence φ 
x₀ n₂).val (p₀ + n₁)
-/
lemma limitSequence_eqUpTo (n : ℕ) :
    (limitSequence φ hφ x₀).EqUpTo (sequence φ x₀ n).1 (p₀ + n) := by
  intro p q hpq hp
  exact sequence_eqUpTo φ hφ _ _ _ (by lia) _ _ _ (by lia)

end InductionUp

end CochainComplex.HomComplex.Cochain

