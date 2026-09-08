/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.ModelTheory.Semantics

/-!
# Presburger arithmetic

This file defines the first-order language of Presburger arithmetic as (0,1,+).

## Main Definitions

- `FirstOrder.Language.presburger`: the language of Presburger arithmetic.

## TODO

- Generalize `presburger.sum` (maybe also `NatCast` and `SMul`) for classes like
  `FirstOrder.Language.IsOrdered`.
- Define the theory of Presburger arithmetic and prove its properties (quantifier elimination,
  completeness, etc).
-/

@[expose] public section

variable {α : Type*}

namespace FirstOrder

/-- The type of Presburger arithmetic functions, defined as (0, 1, +). -/
/-
**FirstOrder.presburgerFunc** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder`。
形式化陈述：ℕ → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of Presburger arithmetic functions, defined as (0, 1, +).
-/
inductive presburgerFunc : ℕ → Type
  | zero : presburgerFunc 0
  | one : presburgerFunc 0
  | add : presburgerFunc 2
  deriving DecidableEq

/-- The language of Presburger arithmetic, defined as (0, 1, +). -/
/-
**FirstOrder.Language.presburger** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language`
。
形式化陈述：FirstOrder.Language
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The language of Presburger arithmetic, defined as (0, 1, +).
-/
def Language.presburger : Language :=
  { Functions := presburgerFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

namespace Language.presburger

variable {t t₁ t₂ : presburger.Term α}

/-
**FirstOrder.Language.presburger.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language
.presburger`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (presburger.Term α) where
  zero := Constants.term .zero
/-
**FirstOrder.Language.presburger.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language
.presburger`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (presburger.Term α) where
  one := Constants.term .one
/-
**FirstOrder.Language.presburger.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language
.presburger`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (presburger.Term α) where
  add := Functions.apply₂ .add
/-
**FirstOrder.Language.presburger.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language
.presburger`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (presburger.Term α) where
  natCast := Nat.unaryCast
/-
**FirstOrder.Language.presburger.natCast_zero** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.presburger`。
形式化陈述：∀ {α : Type u_1}, ↑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] theorem natCast_zero : (0 : ℕ) = (0 : presburger.Term α) := rfl
/-
**FirstOrder.Language.presburger.natCast_succ** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.presburger`。
形式化陈述：∀ {α : Type u_1} (n : ℕ), ↑(n + 1) = ↑n + 1
参数：n : ℕ；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] theorem natCast_succ (n : ℕ) : (n + 1 : ℕ) = (n : presburger.Term α) + 1 := rfl
/-
**FirstOrder.Language.presburger.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language
.presburger`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ (presburger.Term α) where
  smul := nsmulRec
/-
**FirstOrder.Language.presburger.zero_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.presburger`。
形式化陈述：∀ {α : Type u_1} {t : FirstOrder.Language.presburger.Term α}, 0 • t = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem zero_nsmul : 0 • t = 0 := rfl
/-
**FirstOrder.Language.presburger.succ_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.presburger`。
形式化陈述：∀ {α : Type u_1} {t : FirstOrder.Language.presburger.Term α} {n : ℕ}, (n +
 1) • t = n • t + t
参数：n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem succ_nsmul {n : ℕ} : (n + 1) • t = n • t + t := rfl

/-- Summation over a finite set of terms in Presburger arithmetic.

It is defined via choice, so the result only makes sense when the structure satisfies
commutativity (see `realize_sum`). -/
/-
**FirstOrder.Language.presburger.sum** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age.presburger`。
形式化陈述：sum {β : Type*} (s : Finset β) (f : β -> presburger.Term α) : presburger.T
erm α
参数：s : Finset β；f : β -> presburger.Term α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Summation over a finite set of terms in Presburger arithmetic.

It is defined via choice, so the result only makes sense when the structure sati
sfies
commutativity (see `realize_sum`).
-/
noncomputable def sum {β : Type*} (s : Finset β) (f : β → presburger.Term α) : presburger.Term α :=
  (s.toList.map f).sum

variable {M : Type*} {v : α → M}

section

variable [Zero M] [One M] [Add M]

/-
**FirstOrder.Language.presburger.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language
.presburger`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : presburger.Structure M where
  funMap
  | .zero, _ => 0
  | .one, v => 1
  | .add, v => v 0 + v 1
/-
**FirstOrder.Language.presburger.funMap_zero** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.presburger`。
形式化陈述：∀ {M : Type u_2} [inst : Zero M] [inst_1 : One M] [inst_2 : Add M] {v : Fi
n 0 → M},   FirstOrder.Language.Structure.funMap FirstOrder.presburgerFunc.zero 
v = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem funMap_zero {v} :
    Structure.funMap (L := presburger) (M := M) presburgerFunc.zero v = 0 := rfl
/-
**FirstOrder.Language.presburger.funMap_one** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.presburger`。
形式化陈述：∀ {M : Type u_2} [inst : Zero M] [inst_1 : One M] [inst_2 : Add M] {v : Fi
n 0 → M},   FirstOrder.Language.Structure.funMap FirstOrder.presburgerFunc.one v
 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem funMap_one {v} :
    Structure.funMap (L := presburger) (M := M) presburgerFunc.one v = 1 := rfl
/-
**FirstOrder.Language.presburger.funMap_add** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.presburger`。
形式化陈述：∀ {M : Type u_2} [inst : Zero M] [inst_1 : One M] [inst_2 : Add M] {v : Fi
n 2 → M},   FirstOrder.Language.Structure.funMap FirstOrder.presburgerFunc.add v
 = v 0 + v 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem funMap_add {v} :
    Structure.funMap (L := presburger) (M := M) presburgerFunc.add v = v 0 + v 1 := rfl
/-
**FirstOrder.Language.presburger.realize_zero** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.presburger`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {v : α → M} [inst : Zero M] [inst_1 : One 
M] [inst_2 : Add M],   FirstOrder.Language.Term.realize v 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem realize_zero : Term.realize v (0 : presburger.Term α) = 0 := rfl
/-
**FirstOrder.Language.presburger.realize_one** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.presburger`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {v : α → M} [inst : Zero M] [inst_1 : One 
M] [inst_2 : Add M],   FirstOrder.Language.Term.realize v 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem realize_one : Term.realize v (1 : presburger.Term α) = 1 := rfl
/-
**FirstOrder.Language.presburger.realize_add** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.presburger`。
形式化陈述：∀ {α : Type u_1} {t₁ t₂ : FirstOrder.Language.presburger.Term α} {M : Type
 u_2} {v : α → M} [inst : Zero M]   [inst_1 : One M] [inst_2 : Add M],   FirstOr
der.Language.Term.realize v (t₁ + t₂) =     FirstOrder.Language.Term.realize v t
₁ + FirstOrder.Language.Term.realize v t₂
参数：t₁ + t₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem realize_add :
    Term.realize v (t₁ + t₂) = Term.realize v t₁ + Term.realize v t₂ := rfl

end

/-
**FirstOrder.Language.presburger.realize_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.presburger`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {v : α → M} [inst : AddMonoidWithOne M] {n
 : ℕ},   FirstOrder.Language.Term.realize v ↑n = ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
@[simp] theorem realize_natCast [AddMonoidWithOne M] {n : ℕ} :
    Term.realize v (n : presburger.Term α) = n := by
  induction n with simp [*]
/-
**FirstOrder.Language.presburger.realize_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.presburger`。
形式化陈述：∀ {α : Type u_1} {t : FirstOrder.Language.presburger.Term α} {M : Type u_2
} {v : α → M} [inst : AddMonoidWithOne M]   {n : ℕ}, FirstOrder.Language.Term.re
alize v (n • t) = n • FirstOrder.Language.Term.realize v t
参数：n • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m +
 n) • a = m • a + n • a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
@[simp] theorem realize_nsmul [AddMonoidWithOne M] {n : ℕ} :
    Term.realize v (n • t) = n • Term.realize v t := by
  induction n with simp [*, add_nsmul]
/-
**FirstOrder.Language.presburger.realize_sum** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.presburger`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {v : α → M} [inst : AddCommMonoidWithOne M
] {β : Type u_3} {s : Finset β}   {f : β → FirstOrder.Language.presburger.Term α
},   FirstOrder.Language.Term.realize v (FirstOrder.Language.presburger.sum s f)
 =     ∑ i ∈ s, FirstOrder.Language.Term.realize v (f i)
参数：FirstOrder.Language.presburger.sum s f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.toList_toFinset`：toList_toFinset [DecidableEq α] (s : Finset α) :
 s.toList.toFinset = s
· 使用定理 `List.sum_toFinset`：∀ {ι : Type u_1} {M : Type u_5} [inst : DecidableEq ι
] [inst_1 : AddCommMonoid M] (f : ι → M) {l : List ι},   l.Nodup → l.toFinset.su
m f = (…
· 使用定理 `Finset.nodup_toList`：nodup_toList (s : Finset α) : s.toList.Nodup
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
@[simp] theorem realize_sum [AddCommMonoidWithOne M]
    {β : Type*} {s : Finset β} {f : β → presburger.Term α} :
    Term.realize v (sum s f) = ∑ i ∈ s, Term.realize v (f i) := by
  classical
  simp only [sum]
  conv => rhs; rw [← s.toList_toFinset, List.sum_toFinset _ s.nodup_toList]
  generalize s.toList = l
  induction l with simp [*]

end FirstOrder.Language.presburger

