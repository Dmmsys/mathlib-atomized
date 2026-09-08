/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Satisfiability

/-!
# Equivalence of Formulas

## Main Definitions
- `FirstOrder.Language.Theory.Imp`: `φ ⟹[T] ψ` indicates that `φ` implies `ψ` in models of `T`.
- `FirstOrder.Language.Theory.Iff`: `φ ⇔[T] ψ` indicates that `φ` and `ψ` are equivalent formulas or
  sentences in models of `T`.

## TODO
- Define the quotient of `L.Formula α` modulo `⇔[T]` and its Boolean Algebra structure.

-/

@[expose] public section

universe u v w w'

open Cardinal CategoryTheory

open FirstOrder

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w} {n : ℕ}
variable {M : Type*} [Nonempty M] [L.Structure M] [M ⊨ T]

namespace Theory

/-- `φ ⟹[T] ψ` indicates that `φ` implies `ψ` in models of `T`. -/
/-
**FirstOrder.Language.Theory.Imp** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language.
Theory`。
形式化陈述：{L : FirstOrder.Language} → {α : Type w} → {n : ℕ} → L.Theory → L.BoundedF
ormula α n → L.BoundedFormula α n → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`φ ⟹[T] ψ` indicates that `φ` implies `ψ` in models of `T`.
-/
protected def Imp (T : L.Theory) (φ ψ : L.BoundedFormula α n) : Prop :=
  T ⊨ᵇ φ.imp ψ

@[inherit_doc FirstOrder.Language.Theory.Imp]
scoped[FirstOrder] notation:51 φ:50 " ⟹[" T "] " ψ:51 => Language.Theory.Imp T φ ψ

namespace Imp

@[refl]
/-
**FirstOrder.Language.Theory.Imp.refl** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Theory.Imp`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} {α : Type w} {n : ℕ} (φ : L.Bou
ndedFormula α n), T.Imp φ φ
参数：φ : L.BoundedFormula α n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem refl (φ : L.BoundedFormula α n) : φ ⟹[T] φ := fun _ _ _ => id
/-
**FirstOrder.Language.Theory.Imp.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language
.Theory.Imp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Refl (L.BoundedFormula α n) T.Imp := ⟨Imp.refl⟩

@[trans]
/-
**FirstOrder.Language.Theory.Imp.trans** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Theory.Imp`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} {α : Type w} {n : ℕ} {φ ψ θ : L
.BoundedFormula α n},   T.Imp φ ψ → T.Imp ψ θ → T.Imp φ θ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem trans {φ ψ θ : L.BoundedFormula α n} (h1 : φ ⟹[T] ψ) (h2 : ψ ⟹[T] θ) :
    φ ⟹[T] θ := fun M v xs => (h2 M v xs) ∘ (h1 M v xs)
/-
**FirstOrder.Language.Theory.Imp.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language
.Theory.Imp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTrans (L.BoundedFormula α n) T.Imp := ⟨fun _ _ _ => Imp.trans⟩

end Imp

section Imp

/-
**FirstOrder.Language.Theory.bot_imp** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.Langu
age.Theory`。
形式化陈述：bot_imp (φ : L.BoundedFormula α n) : ⊥ ⟹[T] φ
参数：φ : L.BoundedFormula α n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `false_implies`：∀ (p : Prop), (False → p) = True
-/
lemma bot_imp (φ : L.BoundedFormula α n) : ⊥ ⟹[T] φ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_bot, false_implies]
/-
**FirstOrder.Language.Theory.imp_top** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.Langu
age.Theory`。
形式化陈述：imp_top (φ : L.BoundedFormula α n) : φ ⟹[T] ⊤
参数：φ : L.BoundedFormula α n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma imp_top (φ : L.BoundedFormula α n) : φ ⟹[T] ⊤ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_top, implies_true]
/-
**FirstOrder.Language.Theory.imp_sup_left** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.
Language.Theory`。
形式化陈述：imp_sup_left (φ ψ : L.BoundedFormula α n) : φ ⟹[T] φ ⊔ ψ
参数：φ ψ : L.BoundedFormula α n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma imp_sup_left (φ ψ : L.BoundedFormula α n) : φ ⟹[T] φ ⊔ ψ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact Or.inl
/-
**FirstOrder.Language.Theory.imp_sup_right** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder
.Language.Theory`。
形式化陈述：imp_sup_right (φ ψ : L.BoundedFormula α n) : ψ ⟹[T] φ ⊔ ψ
参数：φ ψ : L.BoundedFormula α n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma imp_sup_right (φ ψ : L.BoundedFormula α n) : ψ ⟹[T] φ ⊔ ψ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact Or.inr
/-
**FirstOrder.Language.Theory.sup_imp** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.Langu
age.Theory`。
形式化陈述：sup_imp {φ ψ θ : L.BoundedFormula α n} (h₁ : φ ⟹[T] θ) (h₂ : ψ ⟹[T] θ) : φ
 ⊔ ψ ⟹[T] θ
参数：h₁ : φ ⟹[T] θ；h₂ : ψ ⟹[T] θ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
lemma sup_imp {φ ψ θ : L.BoundedFormula α n} (h₁ : φ ⟹[T] θ) (h₂ : ψ ⟹[T] θ) :
    φ ⊔ ψ ⟹[T] θ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact fun h => h.elim (h₁ M v xs) (h₂ M v xs)
/-
**FirstOrder.Language.Theory.sup_imp_iff** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.L
anguage.Theory`。
形式化陈述：sup_imp_iff {φ ψ θ : L.BoundedFormula α n} : (φ ⊔ ψ ⟹[T] θ) ↔ (φ ⟹[T] θ) ∧
 (ψ ⟹[T] θ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.Imp.trans`：∀ {L : FirstOrder.Language} {T : L
.Theory} {α : Type w} {n : ℕ} {φ ψ θ : L.BoundedFormula α n},   T.Imp φ ψ → T.Im
p ψ θ → T.Imp φ θ
· 使用引理 `FirstOrder.Language.Theory.imp_sup_left`：imp_sup_left (φ ψ : L.BoundedFo
rmula α n) : φ ⟹[T] φ ⊔ ψ
· 使用引理 `FirstOrder.Language.Theory.imp_sup_right`：imp_sup_right (φ ψ : L.Bounded
Formula α n) : ψ ⟹[T] φ ⊔ ψ
· 使用引理 `FirstOrder.Language.Theory.sup_imp`：sup_imp {φ ψ θ : L.BoundedFormula α 
n} (h₁ : φ ⟹[T] θ) (h₂ : ψ ⟹[T] θ) : φ ⊔ ψ ⟹[T] θ
-/
lemma sup_imp_iff {φ ψ θ : L.BoundedFormula α n} :
    (φ ⊔ ψ ⟹[T] θ) ↔ (φ ⟹[T] θ) ∧ (ψ ⟹[T] θ) :=
  ⟨fun h => ⟨(imp_sup_left _ _).trans h, (imp_sup_right _ _).trans h⟩,
    fun ⟨h₁, h₂⟩ => sup_imp h₁ h₂⟩
/-
**FirstOrder.Language.Theory.inf_imp_left** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.
Language.Theory`。
形式化陈述：inf_imp_left (φ ψ : L.BoundedFormula α n) : φ ⊓ ψ ⟹[T] φ
参数：φ ψ : L.BoundedFormula α n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma inf_imp_left (φ ψ : L.BoundedFormula α n) : φ ⊓ ψ ⟹[T] φ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact And.left
/-
**FirstOrder.Language.Theory.inf_imp_right** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder
.Language.Theory`。
形式化陈述：inf_imp_right (φ ψ : L.BoundedFormula α n) : φ ⊓ ψ ⟹[T] ψ
参数：φ ψ : L.BoundedFormula α n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma inf_imp_right (φ ψ : L.BoundedFormula α n) : φ ⊓ ψ ⟹[T] ψ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact And.right
/-
**FirstOrder.Language.Theory.imp_inf** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.Langu
age.Theory`。
形式化陈述：imp_inf {φ ψ θ : L.BoundedFormula α n} (h₁ : φ ⟹[T] ψ) (h₂ : φ ⟹[T] θ) : φ
 ⟹[T] ψ ⊓ θ
参数：h₁ : φ ⟹[T] ψ；h₂ : φ ⟹[T] θ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma imp_inf {φ ψ θ : L.BoundedFormula α n} (h₁ : φ ⟹[T] ψ) (h₂ : φ ⟹[T] θ) :
    φ ⟹[T] ψ ⊓ θ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact fun h => ⟨h₁ M v xs h, h₂ M v xs h⟩
/-
**FirstOrder.Language.Theory.imp_inf_iff** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.L
anguage.Theory`。
形式化陈述：imp_inf_iff {φ ψ θ : L.BoundedFormula α n} : (φ ⟹[T] ψ ⊓ θ) ↔ (φ ⟹[T] ψ) ∧
 (φ ⟹[T] θ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.Imp.trans`：∀ {L : FirstOrder.Language} {T : L
.Theory} {α : Type w} {n : ℕ} {φ ψ θ : L.BoundedFormula α n},   T.Imp φ ψ → T.Im
p ψ θ → T.Imp φ θ
· 使用引理 `FirstOrder.Language.Theory.inf_imp_left`：inf_imp_left (φ ψ : L.BoundedFo
rmula α n) : φ ⊓ ψ ⟹[T] φ
· 使用引理 `FirstOrder.Language.Theory.inf_imp_right`：inf_imp_right (φ ψ : L.Bounded
Formula α n) : φ ⊓ ψ ⟹[T] ψ
· 使用引理 `FirstOrder.Language.Theory.imp_inf`：imp_inf {φ ψ θ : L.BoundedFormula α 
n} (h₁ : φ ⟹[T] ψ) (h₂ : φ ⟹[T] θ) : φ ⟹[T] ψ ⊓ θ
-/
lemma imp_inf_iff {φ ψ θ : L.BoundedFormula α n} :
    (φ ⟹[T] ψ ⊓ θ) ↔ (φ ⟹[T] ψ) ∧ (φ ⟹[T] θ) :=
  ⟨fun h => ⟨h.trans (inf_imp_left _ _), h.trans (inf_imp_right _ _)⟩,
    fun ⟨h₁, h₂⟩ => imp_inf h₁ h₂⟩

end Imp

/-- Two (bounded) formulas are semantically equivalent over a theory `T` when they have the same
interpretation in every model of `T`. (This is also known as logical equivalence, which also has a
proof-theoretic definition.) -/
/-
**FirstOrder.Language.Theory.Iff** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language.
Theory`。
形式化陈述：{L : FirstOrder.Language} → {α : Type w} → {n : ℕ} → L.Theory → L.BoundedF
ormula α n → L.BoundedFormula α n → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two (bounded) formulas are semantically equivalent over a theory `T` when they h
ave the same
interpretation in every model of `T`. (This is also known as logical equivalence
, which also has a
proof-theoretic definition.)
-/
protected def Iff (T : L.Theory) (φ ψ : L.BoundedFormula α n) : Prop :=
  T ⊨ᵇ φ.iff ψ

@[inherit_doc FirstOrder.Language.Theory.Iff]
scoped[FirstOrder]
notation:51 φ:50 " ⇔[" T "] " ψ:51 => Language.Theory.Iff T φ ψ
/-
**FirstOrder.Language.Theory.iff_iff_imp_and_imp** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Theory`。
形式化陈述：iff_iff_imp_and_imp {φ ψ : L.BoundedFormula α n} : (φ ⇔[T] ψ) ↔ (φ ⟹[T] ψ)
 ∧ (ψ ⟹[T] φ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iff_iff_imp_and_imp {φ ψ : L.BoundedFormula α n} :
    (φ ⇔[T] ψ) ↔ (φ ⟹[T] ψ) ∧ (ψ ⟹[T] φ) := by
  simp only [Theory.Imp, ModelsBoundedFormula, BoundedFormula.realize_imp, ← forall_and,
    Theory.Iff, BoundedFormula.realize_iff, iff_iff_implies_and_implies]
/-
**FirstOrder.Language.Theory.imp_antisymm** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Theory`。
形式化陈述：imp_antisymm {φ ψ : L.BoundedFormula α n} (h₁ : φ ⟹[T] ψ) (h₂ : ψ ⟹[T] φ) 
: φ ⇔[T] ψ
参数：h₁ : φ ⟹[T] ψ；h₂ : ψ ⟹[T] φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Theory.iff_iff_imp_and_imp`：iff_iff_imp_and_imp {φ ψ
 : L.BoundedFormula α n} : (φ ⇔[T] ψ) ↔ (φ ⟹[T] ψ) ∧ (ψ ⟹[T] φ)
-/
theorem imp_antisymm {φ ψ : L.BoundedFormula α n} (h₁ : φ ⟹[T] ψ) (h₂ : ψ ⟹[T] φ) :
    φ ⇔[T] ψ :=
  iff_iff_imp_and_imp.2 ⟨h₁, h₂⟩

namespace Iff

/-
**FirstOrder.Language.Theory.Iff.mp** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langua
ge.Theory.Iff`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} {α : Type w} {n : ℕ} {φ ψ : L.B
oundedFormula α n}, T.Iff φ ψ → T.Imp φ ψ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Theory.iff_iff_imp_and_imp`：iff_iff_imp_and_imp {φ ψ
 : L.BoundedFormula α n} : (φ ⇔[T] ψ) ↔ (φ ⟹[T] ψ) ∧ (ψ ⟹[T] φ)
-/
protected theorem mp {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ) :
    φ ⟹[T] ψ := (iff_iff_imp_and_imp.1 h).1
/-
**FirstOrder.Language.Theory.Iff.mpr** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langu
age.Theory.Iff`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} {α : Type w} {n : ℕ} {φ ψ : L.B
oundedFormula α n}, T.Iff φ ψ → T.Imp ψ φ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Theory.iff_iff_imp_and_imp`：iff_iff_imp_and_imp {φ ψ
 : L.BoundedFormula α n} : (φ ⇔[T] ψ) ↔ (φ ⟹[T] ψ) ∧ (ψ ⟹[T] φ)
-/
protected theorem mpr {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ) :
    ψ ⟹[T] φ := (iff_iff_imp_and_imp.1 h).2

@[refl]
/-
**FirstOrder.Language.Theory.Iff.refl** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Theory.Iff`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} {α : Type w} {n : ℕ} (φ : L.Bou
ndedFormula α n), T.Iff φ φ
参数：φ : L.BoundedFormula α n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_iff`：realize_iff : (φ.iff ψ).
Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem refl (φ : L.BoundedFormula α n) : φ ⇔[T] φ :=
  fun M v xs => by rw [BoundedFormula.realize_iff]
/-
**FirstOrder.Language.Theory.Iff.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language
.Theory.Iff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Refl (L.BoundedFormula α n) T.Iff :=
  ⟨Iff.refl⟩

@[symm]
/-
**FirstOrder.Language.Theory.Iff.symm** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Theory.Iff`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} {α : Type w} {n : ℕ} {φ ψ : L.B
oundedFormula α n}, T.Iff φ ψ → T.Iff ψ φ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_iff`：realize_iff : (φ.iff ψ).
Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs)
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem symm {φ ψ : L.BoundedFormula α n}
    (h : φ ⇔[T] ψ) : ψ ⇔[T] φ := fun M v xs => by
  rw [BoundedFormula.realize_iff, Iff.comm, ← BoundedFormula.realize_iff]
  exact h M v xs
/-
**FirstOrder.Language.Theory.Iff.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language
.Theory.Iff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Symm (α := L.BoundedFormula α n) T.Iff :=
  ⟨fun _ _ => Iff.symm⟩

@[trans]
/-
**FirstOrder.Language.Theory.Iff.trans** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Theory.Iff`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} {α : Type w} {n : ℕ} {φ ψ θ : L
.BoundedFormula α n},   T.Iff φ ψ → T.Iff ψ θ → T.Iff φ θ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_iff`：realize_iff : (φ.iff ψ).
Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
protected theorem trans {φ ψ θ : L.BoundedFormula α n}
    (h1 : φ ⇔[T] ψ) (h2 : ψ ⇔[T] θ) :
    φ ⇔[T] θ := fun M v xs => by
  have h1' := h1 M v xs
  have h2' := h2 M v xs
  rw [BoundedFormula.realize_iff] at *
  exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩
/-
**FirstOrder.Language.Theory.Iff.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language
.Theory.Iff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTrans (L.BoundedFormula α n) T.Iff :=
  ⟨fun _ _ _ => Iff.trans⟩
/-
**FirstOrder.Language.Theory.Iff.realize_bd_iff** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Theory.Iff`。
形式化陈述：realize_bd_iff {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ) {v : α -> M} {x
s : Fin n -> M} : φ.Realize v xs ↔ ψ.Realize v xs
参数：h : φ ⇔[T] ψ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_iff`：realize_iff : (φ.iff ψ).
Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs)
· 使用定理 `FirstOrder.Language.Theory.ModelsBoundedFormula.realize_boundedFormula`：
∀ {L : FirstOrder.Language} {T : L.Theory} {α : Type w} {n : ℕ} {φ : L.BoundedFo
rmula α n},   T ⊨ᵇ φ → ∀ (M : Type u_1) [inst : L.Structure …
-/
theorem realize_bd_iff {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ)
    {v : α → M} {xs : Fin n → M} : φ.Realize v xs ↔ ψ.Realize v xs :=
  BoundedFormula.realize_iff.1 (h.realize_boundedFormula M)
/-
**FirstOrder.Language.Theory.Iff.realize_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Theory.Iff`。
形式化陈述：realize_iff {φ ψ : L.Formula α} {M : Type*} [Nonempty M] [L.Structure M] [
M ⊨ T] (h : φ ⇔[T] ψ) {v : α -> M} : φ.Realize v ↔ ψ.Realize v
参数：h : φ ⇔[T] ψ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.Iff.realize_bd_iff`：realize_bd_iff {φ ψ : L.B
oundedFormula α n} (h : φ ⇔[T] ψ) {v : α -> M} {xs : Fin n -> M} : φ.Realize v x
s ↔ ψ.Realize v xs
-/
theorem realize_iff {φ ψ : L.Formula α} {M : Type*} [Nonempty M]
    [L.Structure M] [M ⊨ T] (h : φ ⇔[T] ψ) {v : α → M} :
    φ.Realize v ↔ ψ.Realize v :=
  h.realize_bd_iff
/-
**FirstOrder.Language.Theory.Iff.models_sentence_iff** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Theory.Iff`。
形式化陈述：models_sentence_iff {φ ψ : L.Sentence} {M : Type*} [Nonempty M] [L.Structu
re M] [M ⊨ T] (h : φ ⇔[T] ψ) : M ⊨ φ ↔ M ⊨ ψ
参数：h : φ ⇔[T] ψ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.Iff.realize_iff`：realize_iff {φ ψ : L.Formula
 α} {M : Type*} [Nonempty M] [L.Structure M] [M ⊨ T] (h : φ ⇔[T] ψ) {v : α -> M}
 : φ.Realize v ↔ ψ.Realize v
-/
theorem models_sentence_iff {φ ψ : L.Sentence} {M : Type*} [Nonempty M]
    [L.Structure M] [M ⊨ T] (h : φ ⇔[T] ψ) :
    M ⊨ φ ↔ M ⊨ ψ :=
  h.realize_iff
/-
**FirstOrder.Language.Theory.Iff.all** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langu
age.Theory.Iff`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} {α : Type w} {n : ℕ} {φ ψ : L.B
oundedFormula α (n + 1)},   T.Iff φ ψ → T.Iff φ.all ψ.all
参数：n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `FirstOrder.Language.Theory.Iff.realize_bd_iff`：realize_bd_iff {φ ψ : L.B
oundedFormula α n} (h : φ ⇔[T] ψ) {v : α -> M} {xs : Fin n -> M} : φ.Realize v x
s ↔ ψ.Realize v xs
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
-/
protected theorem all {φ ψ : L.BoundedFormula α (n + 1)}
    (h : φ ⇔[T] ψ) : φ.all ⇔[T] ψ.all := by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_all]
  exact fun M v xs => forall_congr' fun a => h.realize_bd_iff
/-
**FirstOrder.Language.Theory.Iff.ex** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langua
ge.Theory.Iff`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} {α : Type w} {n : ℕ} {φ ψ : L.B
oundedFormula α (n + 1)},   T.Iff φ ψ → T.Iff φ.ex ψ.ex
参数：n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `FirstOrder.Language.Theory.Iff.realize_bd_iff`：realize_bd_iff {φ ψ : L.B
oundedFormula α n} (h : φ ⇔[T] ψ) {v : α -> M} {xs : Fin n -> M} : φ.Realize v x
s ↔ ψ.Realize v xs
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
-/
protected theorem ex {φ ψ : L.BoundedFormula α (n + 1)} (h : φ ⇔[T] ψ) :
    φ.ex ⇔[T] ψ.ex := by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_ex]
  exact fun M v xs => exists_congr fun a => h.realize_bd_iff
/-
**FirstOrder.Language.Theory.Iff.not** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langu
age.Theory.Iff`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} {α : Type w} {n : ℕ} {φ ψ : L.B
oundedFormula α n},   T.Iff φ ψ → T.Iff φ.not ψ.not
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `FirstOrder.Language.Theory.Iff.realize_bd_iff`：realize_bd_iff {φ ψ : L.B
oundedFormula α n} (h : φ ⇔[T] ψ) {v : α -> M} {xs : Fin n -> M} : φ.Realize v x
s ↔ ψ.Realize v xs
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
-/
protected theorem not {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ) :
    φ.not ⇔[T] ψ.not := by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_not]
  exact fun M v xs => not_congr h.realize_bd_iff
/-
**FirstOrder.Language.Theory.Iff.imp** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langu
age.Theory.Iff`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} {α : Type w} {n : ℕ} {φ ψ φ' ψ'
 : L.BoundedFormula α n},   T.Iff φ ψ → T.Iff φ' ψ' → T.Iff (φ.imp φ') (ψ.imp ψ'
)
参数：φ.imp φ'；ψ.imp ψ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imp_congr`：∀ {a b c d : Prop}, (a ↔ c) → (b ↔ d) → (a → b ↔ c → d)
· 使用定理 `FirstOrder.Language.Theory.Iff.realize_bd_iff`：realize_bd_iff {φ ψ : L.B
oundedFormula α n} (h : φ ⇔[T] ψ) {v : α -> M} {xs : Fin n -> M} : φ.Realize v x
s ↔ ψ.Realize v xs
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
-/
protected theorem imp {φ ψ φ' ψ' : L.BoundedFormula α n} (h : φ ⇔[T] ψ) (h' : φ' ⇔[T] ψ') :
    (φ.imp φ') ⇔[T] (ψ.imp ψ') := by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_imp]
  exact fun M v xs => imp_congr h.realize_bd_iff h'.realize_bd_iff

end Iff

/-- Semantic equivalence forms an equivalence relation on formulas. -/
@[instance_reducible]
/-
**FirstOrder.Language.Theory.iffSetoid** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lan
guage.Theory`。
形式化陈述：iffSetoid (T : L.Theory) : Setoid (L.BoundedFormula α n) where r
参数：T : L.Theory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Semantic equivalence forms an equivalence relation on formulas.
-/
def iffSetoid (T : L.Theory) : Setoid (L.BoundedFormula α n) where
  r := T.Iff
  iseqv := ⟨fun _ => refl _, fun {_ _} h => h.symm, fun {_ _ _} h1 h2 => h1.trans h2⟩

end Theory

namespace BoundedFormula

variable (φ ψ : L.BoundedFormula α n)

/-
**FirstOrder.Language.BoundedFormula.iff_not_not** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：iff_not_not : φ ⇔[T] φ.not.not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iff_not_not : φ ⇔[T] φ.not.not := fun M v xs => by
  simp
/-
**FirstOrder.Language.BoundedFormula.imp_iff_not_sup** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.BoundedFormula`。
形式化陈述：imp_iff_not_sup : (φ.imp ψ) ⇔[T] (φ.not ⊔ ψ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem imp_iff_not_sup : (φ.imp ψ) ⇔[T] (φ.not ⊔ ψ) :=
  fun M v xs => by simp [imp_iff_not_or]
/-
**FirstOrder.Language.BoundedFormula.sup_iff_not_inf_not** 是 Mathlib 中的一个定理，位于命名
空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：sup_iff_not_inf_not : (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup_iff_not_inf_not : (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not :=
  fun M v xs => by simp [imp_iff_not_or]
/-
**FirstOrder.Language.BoundedFormula.inf_iff_not_sup_not** 是 Mathlib 中的一个定理，位于命名
空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：inf_iff_not_sup_not : (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inf_iff_not_sup_not : (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not :=
  fun M v xs => by simp
/-
**FirstOrder.Language.BoundedFormula.all_iff_not_ex_not** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：all_iff_not_ex_not (φ : L.BoundedFormula α (n + 1)) : φ.all ⇔[T] φ.not.ex.
not
参数：φ : L.BoundedFormula α (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem all_iff_not_ex_not (φ : L.BoundedFormula α (n + 1)) :
    φ.all ⇔[T] φ.not.ex.not := fun M v xs => by simp
/-
**FirstOrder.Language.BoundedFormula.ex_iff_not_all_not** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：ex_iff_not_all_not (φ : L.BoundedFormula α (n + 1)) : φ.ex ⇔[T] φ.not.all.
not
参数：φ : L.BoundedFormula α (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ex_iff_not_all_not (φ : L.BoundedFormula α (n + 1)) :
    φ.ex ⇔[T] φ.not.all.not := fun M v xs => by simp
/-
**FirstOrder.Language.BoundedFormula.iff_all_liftAt** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.BoundedFormula`。
形式化陈述：iff_all_liftAt : φ ⇔[T] (φ.liftAt 1 n).all
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_iff`：realize_iff : (φ.iff ψ).
Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_all_liftAt_one_self`：realize_
all_liftAt_one_self {n : Nat} {φ : L.BoundedFormula α n} {v : α -> M} {xs : Fin 
n -> M} : (φ.liftAt 1 n).all.Realize v xs ↔ φ.Realiz…
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem iff_all_liftAt : φ ⇔[T] (φ.liftAt 1 n).all :=
  fun M v xs => by
  rw [realize_iff, realize_all_liftAt_one_self]
/-
**FirstOrder.Language.BoundedFormula.inf_not_iff_bot** 是 Mathlib 中的一个引理，位于命名空间 `
FirstOrder.Language.BoundedFormula`。
形式化陈述：inf_not_iff_bot : φ ⊓ ∼φ ⇔[T] ⊥
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inf_not_iff_bot :
    φ ⊓ ∼φ ⇔[T] ⊥ := fun M v xs => by
  simp only [realize_iff, realize_inf, realize_not, and_not_self, realize_bot]
/-
**FirstOrder.Language.BoundedFormula.sup_not_iff_top** 是 Mathlib 中的一个引理，位于命名空间 `
FirstOrder.Language.BoundedFormula`。
形式化陈述：sup_not_iff_top : φ ⊔ ∼φ ⇔[T] ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sup_not_iff_top :
    φ ⊔ ∼φ ⇔[T] ⊤ := fun M v xs => by
  simp only [realize_iff, realize_sup, realize_not, realize_top, or_not]

end BoundedFormula

namespace Formula

variable (φ ψ : L.Formula α)

/-
**FirstOrder.Language.Formula.iff_not_not** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Formula`。
形式化陈述：iff_not_not : φ ⇔[T] φ.not.not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.iff_not_not`：iff_not_not : φ ⇔[T] φ.n
ot.not
-/
theorem iff_not_not : φ ⇔[T] φ.not.not :=
  BoundedFormula.iff_not_not φ
/-
**FirstOrder.Language.Formula.imp_iff_not_sup** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Formula`。
形式化陈述：imp_iff_not_sup : (φ.imp ψ) ⇔[T] (φ.not ⊔ ψ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.imp_iff_not_sup`：imp_iff_not_sup : (φ
.imp ψ) ⇔[T] (φ.not ⊔ ψ)
-/
theorem imp_iff_not_sup : (φ.imp ψ) ⇔[T] (φ.not ⊔ ψ) :=
  BoundedFormula.imp_iff_not_sup φ ψ
/-
**FirstOrder.Language.Formula.sup_iff_not_inf_not** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Formula`。
形式化陈述：sup_iff_not_inf_not : (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.sup_iff_not_inf_not`：sup_iff_not_inf_
not : (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not
-/
theorem sup_iff_not_inf_not : (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not :=
  BoundedFormula.sup_iff_not_inf_not φ ψ
/-
**FirstOrder.Language.Formula.inf_iff_not_sup_not** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Formula`。
形式化陈述：inf_iff_not_sup_not : (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.inf_iff_not_sup_not`：inf_iff_not_sup_
not : (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not
-/
theorem inf_iff_not_sup_not : (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not :=
  BoundedFormula.inf_iff_not_sup_not φ ψ

end Formula

end Language

end FirstOrder

