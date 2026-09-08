/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Equivalence

/-!
# Quantifier Complexity

This file defines quantifier complexity of first-order formulas, and constructs prenex normal forms.

## Main Definitions

- `FirstOrder.Language.BoundedFormula.IsAtomic` defines atomic formulas - those which are
  constructed only from terms and relations.
- `FirstOrder.Language.BoundedFormula.IsQF` defines quantifier-free formulas - those which are
  constructed only from atomic formulas and Boolean operations.
- `FirstOrder.Language.BoundedFormula.IsPrenex` defines when a formula is in prenex normal form -
  when it consists of a series of quantifiers applied to a quantifier-free formula.
- `FirstOrder.Language.BoundedFormula.toPrenex` constructs a prenex normal form of a given formula.


## Main Results

- `FirstOrder.Language.BoundedFormula.realize_toPrenex` shows that the prenex normal form of a
  formula has the same realization as the original formula.

-/

@[expose] public section

universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {α : Type u'} {β : Type v'}
variable {n l : ℕ} {φ : L.BoundedFormula α l}

open FirstOrder Structure Fin

namespace BoundedFormula

/-- An atomic formula is either equality or a relation symbol applied to terms.
Note that `⊥` and `⊤` are not considered atomic in this convention. -/
/-
**FirstOrder.Language.BoundedFormula.IsAtomic** 是 Mathlib 中的一个归纳类型，位于命名空间 `First
Order.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.BoundedFormula α n
 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An atomic formula is either equality or a relation symbol applied to terms.
Note that `⊥` and `⊤` are not considered atomic in this convention.
-/
inductive IsAtomic : L.BoundedFormula α n → Prop
  | equal (t₁ t₂ : L.Term (α ⊕ (Fin n))) : IsAtomic (t₁.bdEqual t₂)
  | rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) :
    IsAtomic (R.boundedFormula ts)
/-
**FirstOrder.Language.BoundedFormula.not_all_isAtomic** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.BoundedFormula`。
形式化陈述：not_all_isAtomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsAtomic
参数：φ : L.BoundedFormula α (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem not_all_isAtomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsAtomic := fun con => by
  cases con
/-
**FirstOrder.Language.BoundedFormula.not_ex_isAtomic** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.BoundedFormula`。
形式化陈述：not_ex_isAtomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsAtomic
参数：φ : L.BoundedFormula α (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem not_ex_isAtomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsAtomic := fun con => by cases con
/-
**FirstOrder.Language.BoundedFormula.IsAtomic.relabel** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.BoundedFormula.IsAtomic`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {β : Type v'} {n m : ℕ} {φ : L.B
oundedFormula α m},   φ.IsAtomic → ∀ (f : α → β ⊕ Fin n), (FirstOrder.Language.B
oundedFormula.relabel f φ).IsAtomic
参数：f : α → β ⊕ Fin n；FirstOrder.Language.BoundedFormula.relabel f φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsAtomic.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsAtomic)
    (f : α → β ⊕ (Fin n)) : (φ.relabel f).IsAtomic :=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _
/-
**FirstOrder.Language.BoundedFormula.IsAtomic.liftAt** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.BoundedFormula.IsAtomic`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {l : ℕ} {φ : L.BoundedFormula α 
l} {k m : ℕ},   φ.IsAtomic → (FirstOrder.Language.BoundedFormula.liftAt k m φ).I
sAtomic
参数：FirstOrder.Language.BoundedFormula.liftAt k m φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsAtomic.liftAt {k m : ℕ} (h : IsAtomic φ) : (φ.liftAt k m).IsAtomic :=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _
/-
**FirstOrder.Language.BoundedFormula.IsAtomic.castLE** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.BoundedFormula.IsAtomic`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n l : ℕ} {φ : L.BoundedFormula 
α l} {h : l ≤ n},   φ.IsAtomic → (FirstOrder.Language.BoundedFormula.castLE h φ)
.IsAtomic
参数：FirstOrder.Language.BoundedFormula.castLE h φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsAtomic.castLE {h : l ≤ n} (hφ : IsAtomic φ) : (φ.castLE h).IsAtomic :=
  IsAtomic.recOn hφ (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

/-- A quantifier-free formula is a formula defined without quantifiers. These are all equivalent
to Boolean combinations of atomic formulas. -/
/-
**FirstOrder.Language.BoundedFormula.IsQF** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrde
r.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.BoundedFormula α n
 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quantifier-free formula is a formula defined without quantifiers. These are al
l equivalent
to Boolean combinations of atomic formulas.
-/
inductive IsQF : L.BoundedFormula α n → Prop
  | falsum : IsQF falsum
  | of_isAtomic {φ :  L.BoundedFormula α n} (h : IsAtomic φ) : IsQF φ
  | imp {φ₁ φ₂ :  L.BoundedFormula α n} (h₁ : IsQF φ₁) (h₂ : IsQF φ₂) : IsQF (φ₁.imp φ₂)
/-
**FirstOrder.Language.BoundedFormula.IsAtomic.isQF** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.BoundedFormula.IsAtomic`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α 
n}, φ.IsAtomic → φ.IsQF
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsAtomic.isQF {φ : L.BoundedFormula α n} : IsAtomic φ → IsQF φ :=
  IsQF.of_isAtomic
/-
**FirstOrder.Language.BoundedFormula.isQF_bot** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.BoundedFormula`。
形式化陈述：isQF_bot : IsQF (⊥ : L.BoundedFormula α n)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isQF_bot : IsQF (⊥ : L.BoundedFormula α n) :=
  IsQF.falsum

namespace IsQF

/-
**FirstOrder.Language.BoundedFormula.IsQF.not** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.BoundedFormula.IsQF`。
形式化陈述：not {φ : L.BoundedFormula α n} (h : IsQF φ) : IsQF φ.not
参数：h : IsQF φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.isQF_bot`：isQF_bot : IsQF (⊥ : L.Boun
dedFormula α n)
-/
theorem not {φ : L.BoundedFormula α n} (h : IsQF φ) : IsQF φ.not :=
  h.imp isQF_bot
/-
**FirstOrder.Language.BoundedFormula.IsQF.top** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.BoundedFormula.IsQF`。
形式化陈述：top : IsQF (⊤ : L.BoundedFormula α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.not`：not {φ : L.BoundedFormula α
 n} (h : IsQF φ) : IsQF φ.not
· 使用定理 `FirstOrder.Language.BoundedFormula.isQF_bot`：isQF_bot : IsQF (⊥ : L.Boun
dedFormula α n)
-/
theorem top : IsQF (⊤ : L.BoundedFormula α n) := isQF_bot.not
/-
**FirstOrder.Language.BoundedFormula.IsQF.sup** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.BoundedFormula.IsQF`。
形式化陈述：sup {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsQF ψ) : IsQF (φ ⊔ ψ
)
参数：hφ : IsQF φ；hψ : IsQF ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.not`：not {φ : L.BoundedFormula α
 n} (h : IsQF φ) : IsQF φ.not
-/
theorem sup {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsQF ψ) : IsQF (φ ⊔ ψ) :=
  hφ.not.imp hψ
/-
**FirstOrder.Language.BoundedFormula.IsQF.inf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.BoundedFormula.IsQF`。
形式化陈述：inf {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsQF ψ) : IsQF (φ ⊓ ψ
)
参数：hφ : IsQF φ；hψ : IsQF ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.not`：not {φ : L.BoundedFormula α
 n} (h : IsQF φ) : IsQF φ.not
-/
theorem inf {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsQF ψ) : IsQF (φ ⊓ ψ) :=
  (hφ.imp hψ.not).not
/-
**FirstOrder.Language.BoundedFormula.IsQF.relabel** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.BoundedFormula.IsQF`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {β : Type v'} {n m : ℕ} {φ : L.B
oundedFormula α m},   φ.IsQF → ∀ (f : α → β ⊕ Fin n), (FirstOrder.Language.Bound
edFormula.relabel f φ).IsQF
参数：f : α → β ⊕ Fin n；FirstOrder.Language.BoundedFormula.relabel f φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.isQF_bot`：isQF_bot : IsQF (⊥ : L.Boun
dedFormula α n)
· 使用定理 `FirstOrder.Language.BoundedFormula.IsAtomic.isQF`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsAtomic → φ.IsQF
· 使用定理 `FirstOrder.Language.BoundedFormula.IsAtomic.relabel`：∀ {L : FirstOrder.L
anguage} {α : Type u'} {β : Type v'} {n m : ℕ} {φ : L.BoundedFormula α m},   φ.I
sAtomic → ∀ (f : α → β ⊕ Fin n), (FirstOr…
-/
protected theorem relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsQF) (f : α → β ⊕ (Fin n)) :
    (φ.relabel f).IsQF :=
  IsQF.recOn h isQF_bot (fun h => (h.relabel f).isQF) fun _ _ h1 h2 => h1.imp h2
/-
**FirstOrder.Language.BoundedFormula.IsQF.liftAt** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula.IsQF`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {l : ℕ} {φ : L.BoundedFormula α 
l} {k m : ℕ},   φ.IsQF → (FirstOrder.Language.BoundedFormula.liftAt k m φ).IsQF
参数：FirstOrder.Language.BoundedFormula.liftAt k m φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.isQF_bot`：isQF_bot : IsQF (⊥ : L.Boun
dedFormula α n)
· 使用定理 `FirstOrder.Language.BoundedFormula.IsAtomic.isQF`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsAtomic → φ.IsQF
· 使用定理 `FirstOrder.Language.BoundedFormula.IsAtomic.liftAt`：∀ {L : FirstOrder.La
nguage} {α : Type u'} {l : ℕ} {φ : L.BoundedFormula α l} {k m : ℕ},   φ.IsAtomic
 → (FirstOrder.Language.BoundedFormula.l…
-/
protected theorem liftAt {k m : ℕ} (h : IsQF φ) : (φ.liftAt k m).IsQF :=
  IsQF.recOn h isQF_bot (fun ih => ih.liftAt.isQF) fun _ _ ih1 ih2 => ih1.imp ih2
/-
**FirstOrder.Language.BoundedFormula.IsQF.castLE** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula.IsQF`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n l : ℕ} {φ : L.BoundedFormula 
α l} {h : l ≤ n},   φ.IsQF → (FirstOrder.Language.BoundedFormula.castLE h φ).IsQ
F
参数：FirstOrder.Language.BoundedFormula.castLE h φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.isQF_bot`：isQF_bot : IsQF (⊥ : L.Boun
dedFormula α n)
· 使用定理 `FirstOrder.Language.BoundedFormula.IsAtomic.isQF`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsAtomic → φ.IsQF
· 使用定理 `FirstOrder.Language.BoundedFormula.IsAtomic.castLE`：∀ {L : FirstOrder.La
nguage} {α : Type u'} {n l : ℕ} {φ : L.BoundedFormula α l} {h : l ≤ n},   φ.IsAt
omic → (FirstOrder.Language.BoundedFormu…
-/
protected theorem castLE {h : l ≤ n} (hφ : IsQF φ) : (φ.castLE h).IsQF :=
  IsQF.recOn hφ isQF_bot (fun ih => ih.castLE.isQF) fun _ _ ih1 ih2 => ih1.imp ih2

end IsQF

/-
**FirstOrder.Language.BoundedFormula.not_all_isQF** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.BoundedFormula`。
形式化陈述：not_all_isQF (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsQF
参数：φ : L.BoundedFormula α (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `FirstOrder.Language.BoundedFormula.not_all_isAtomic`：not_all_isAtomic (φ
 : L.BoundedFormula α (n + 1)) : ¬φ.all.IsAtomic
-/
theorem not_all_isQF (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsQF := fun con => by
  obtain - | con := con
  exact φ.not_all_isAtomic con
/-
**FirstOrder.Language.BoundedFormula.not_ex_isQF** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：not_ex_isQF (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsQF
参数：φ : L.BoundedFormula α (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `FirstOrder.Language.BoundedFormula.not_ex_isAtomic`：not_ex_isAtomic (φ :
 L.BoundedFormula α (n + 1)) : ¬φ.ex.IsAtomic
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `FirstOrder.Language.BoundedFormula.not_all_isQF`：not_all_isQF (φ : L.Bou
ndedFormula α (n + 1)) : ¬φ.all.IsQF
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem not_ex_isQF (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsQF := fun con => by
  obtain - | con | con := con
  · exact φ.not_ex_isAtomic con
  · exact not_all_isQF _ con

/-- Indicates that a bounded formula is in prenex normal form - that is, it consists of quantifiers
  applied to a quantifier-free formula. -/
/-
**FirstOrder.Language.BoundedFormula.IsPrenex** 是 Mathlib 中的一个归纳类型，位于命名空间 `First
Order.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.BoundedFormula α n
 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Indicates that a bounded formula is in prenex normal form - that is, it consists
 of quantifiers
  applied to a quantifier-free formula.
-/
inductive IsPrenex : ∀ {n}, L.BoundedFormula α n → Prop
  | of_isQF {n : ℕ} {φ : L.BoundedFormula α n} (h : IsQF φ) : IsPrenex φ
  | all {n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsPrenex φ) : IsPrenex φ.all
  | ex {n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsPrenex φ) : IsPrenex φ.ex
/-
**FirstOrder.Language.BoundedFormula.IsQF.isPrenex** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.BoundedFormula.IsQF`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α 
n}, φ.IsQF → φ.IsPrenex
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsQF.isPrenex {φ : L.BoundedFormula α n} : IsQF φ → IsPrenex φ :=
  IsPrenex.of_isQF
/-
**FirstOrder.Language.BoundedFormula.IsAtomic.isPrenex** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.BoundedFormula.IsAtomic`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α 
n}, φ.IsAtomic → φ.IsPrenex
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.isPrenex`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF → φ.IsPrenex
· 使用定理 `FirstOrder.Language.BoundedFormula.IsAtomic.isQF`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsAtomic → φ.IsQF
-/
theorem IsAtomic.isPrenex {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsPrenex φ :=
  h.isQF.isPrenex
/-
**FirstOrder.Language.BoundedFormula.IsPrenex.induction_on_all_not** 是 Mathlib 中
的一个定理，位于命名空间 `FirstOrder.Language.BoundedFormula.IsPrenex`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {P : {n : ℕ} → L.Bounded
Formula α n → Prop}   {φ : L.BoundedFormula α n},   φ.IsPrenex →     (∀ {m : ℕ} 
{ψ : L.BoundedFormula α m}, ψ.IsQF → P ψ) →       (∀ {m : ℕ} {ψ : L.BoundedFormu
la α (m + 1)}, P ψ → P ψ.all) →         (∀ {m : ℕ} {ψ : L.BoundedFormula α m}, P
 ψ → P ψ.not) → P φ
参数：∀ {m : ℕ} {ψ : L.BoundedFormula α m}, ψ.IsQF → P ψ；∀ {m : ℕ} {ψ : L.BoundedFo
rmula α (m + 1)}, P ψ → P ψ.all；∀ {m : ℕ} {ψ : L.BoundedFormula α m}, P ψ → P ψ.
not。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsPrenex.induction_on_all_not {P : ∀ {n}, L.BoundedFormula α n → Prop}
    {φ : L.BoundedFormula α n} (h : IsPrenex φ)
    (hq : ∀ {m} {ψ : L.BoundedFormula α m}, ψ.IsQF → P ψ)
    (ha : ∀ {m} {ψ : L.BoundedFormula α (m + 1)}, P ψ → P ψ.all)
    (hn : ∀ {m} {ψ : L.BoundedFormula α m}, P ψ → P ψ.not) : P φ :=
  IsPrenex.recOn h hq (fun _ => ha) fun _ ih => hn (ha (hn ih))
/-
**FirstOrder.Language.BoundedFormula.IsPrenex.relabel** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.BoundedFormula.IsPrenex`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {β : Type v'} {n m : ℕ} {φ : L.B
oundedFormula α m},   φ.IsPrenex → ∀ (f : α → β ⊕ Fin n), (FirstOrder.Language.B
oundedFormula.relabel f φ).IsPrenex
参数：f : α → β ⊕ Fin n；FirstOrder.Language.BoundedFormula.relabel f φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.isPrenex`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF → φ.IsPrenex
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.relabel`：∀ {L : FirstOrder.Langu
age} {α : Type u'} {β : Type v'} {n m : ℕ} {φ : L.BoundedFormula α m},   φ.IsQF 
→ ∀ (f : α → β ⊕ Fin n), (FirstOrder.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.relabel_all`：relabel_all (g : α -> β 
oplus (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) : φ.all.relabel g = (φ.relab
el g).all
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `FirstOrder.Language.BoundedFormula.relabel_ex`：relabel_ex (g : α -> β op
lus (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) : φ.ex.relabel g = (φ.relabel 
g).ex
-/
theorem IsPrenex.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsPrenex)
    (f : α → β ⊕ (Fin n)) : (φ.relabel f).IsPrenex :=
  IsPrenex.recOn h (fun h => (h.relabel f).isPrenex) (fun _ h => by simp [h.all])
    fun _ h => by simp [h.ex]
/-
**FirstOrder.Language.BoundedFormula.IsPrenex.castLE** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.BoundedFormula.IsPrenex`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {l : ℕ} {φ : L.BoundedFormula α 
l},   φ.IsPrenex → ∀ {n : ℕ} {h : l ≤ n}, (FirstOrder.Language.BoundedFormula.ca
stLE h φ).IsPrenex
参数：FirstOrder.Language.BoundedFormula.castLE h φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.isPrenex`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF → φ.IsPrenex
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.castLE`：∀ {L : FirstOrder.Langua
ge} {α : Type u'} {n l : ℕ} {φ : L.BoundedFormula α l} {h : l ≤ n},   φ.IsQF → (
FirstOrder.Language.BoundedFormula.c…
-/
theorem IsPrenex.castLE (hφ : IsPrenex φ) : ∀ {n} {h : l ≤ n}, (φ.castLE h).IsPrenex :=
  IsPrenex.recOn (motive := @fun l φ _ => ∀ (n : ℕ) (h : l ≤ n), (φ.castLE h).IsPrenex) hφ
    (@fun _ _ ih _ _ => ih.castLE.isPrenex)
    (@fun _ _ _ ih _ _ => (ih _ _).all)
    (@fun _ _ _ ih _ _ => (ih _ _).ex) _ _
/-
**FirstOrder.Language.BoundedFormula.IsPrenex.liftAt** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.BoundedFormula.IsPrenex`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {l : ℕ} {φ : L.BoundedFormula α 
l} {k m : ℕ},   φ.IsPrenex → (FirstOrder.Language.BoundedFormula.liftAt k m φ).I
sPrenex
参数：FirstOrder.Language.BoundedFormula.liftAt k m φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.isPrenex`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF → φ.IsPrenex
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.liftAt`：∀ {L : FirstOrder.Langua
ge} {α : Type u'} {l : ℕ} {φ : L.BoundedFormula α l} {k m : ℕ},   φ.IsQF → (Firs
tOrder.Language.BoundedFormula.liftA…
· 使用定理 `FirstOrder.Language.BoundedFormula.IsPrenex.castLE`：∀ {L : FirstOrder.La
nguage} {α : Type u'} {l : ℕ} {φ : L.BoundedFormula α l},   φ.IsPrenex → ∀ {n : 
ℕ} {h : l ≤ n}, (FirstOrder.Language.Bou…
-/
theorem IsPrenex.liftAt {k m : ℕ} (h : IsPrenex φ) : (φ.liftAt k m).IsPrenex :=
  IsPrenex.recOn h (fun ih => ih.liftAt.isPrenex) (fun _ ih => ih.castLE.all)
    fun _ ih => ih.castLE.ex

/-- An auxiliary operation to `FirstOrder.Language.BoundedFormula.toPrenex`.
  If `φ` is quantifier-free and `ψ` is in prenex normal form, then `φ.toPrenexImpRight ψ`
  is a prenex normal form for `φ.imp ψ`. -/
/-
**FirstOrder.Language.BoundedFormula.toPrenexImpRight** 是 Mathlib 中的一个定义，位于命名空间 
`FirstOrder.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.BoundedFormula α n
 → L.BoundedFormula α n → L.BoundedFormula α n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary operation to `FirstOrder.Language.BoundedFormula.toPrenex`.
  If `φ` is quantifier-free and `ψ` is in prenex normal form, then `φ.toPrenexIm
pRight ψ`
  is a prenex normal form for `φ.imp ψ`.
-/
def toPrenexImpRight : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n
  | n, φ, BoundedFormula.ex ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).ex
  | n, φ, all ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).all
  | _n, φ, ψ => φ.imp ψ
/-
**FirstOrder.Language.BoundedFormula.IsQF.toPrenexImpRight** 是 Mathlib 中的一个定理，位于
命名空间 `FirstOrder.Language.BoundedFormula.IsQF`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {φ ψ : L.BoundedFormula 
α n}, ψ.IsQF → φ.toPrenexImpRight ψ = φ.imp ψ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsQF.toPrenexImpRight {φ : L.BoundedFormula α n} :
    ∀ {ψ : L.BoundedFormula α n}, IsQF ψ → φ.toPrenexImpRight ψ = φ.imp ψ
  | _, IsQF.falsum => rfl
  | _, IsQF.of_isAtomic (IsAtomic.equal _ _) => rfl
  | _, IsQF.of_isAtomic (IsAtomic.rel _ _) => rfl
  | _, IsQF.imp IsQF.falsum _ => rfl
  | _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.equal _ _)) _ => rfl
  | _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.rel _ _)) _ => rfl
  | _, IsQF.imp (IsQF.imp _ _) _ => rfl
/-
**FirstOrder.Language.BoundedFormula.isPrenex_toPrenexImpRight** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：isPrenex_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ :
 IsPrenex ψ) : IsPrenex (φ.toPrenexImpRight ψ)
参数：hφ : IsQF φ；hψ : IsPrenex ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.toPrenexImpRight`：∀ {L : FirstOr
der.Language} {α : Type u'} {n : ℕ} {φ ψ : L.BoundedFormula α n}, ψ.IsQF → φ.toP
renexImpRight ψ = φ.imp ψ
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.isPrenex`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF → φ.IsPrenex
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.liftAt`：∀ {L : FirstOrder.Langua
ge} {α : Type u'} {l : ℕ} {φ : L.BoundedFormula α l} {k m : ℕ},   φ.IsQF → (Firs
tOrder.Language.BoundedFormula.liftA…
-/
theorem isPrenex_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImpRight ψ) := by
  induction hψ with
  | of_isQF hψ => rw [hψ.toPrenexImpRight]; exact (hφ.imp hψ).isPrenex
  | all _ ih1 => exact (ih1 hφ.liftAt).all
  | ex _ ih2 => exact (ih2 hφ.liftAt).ex

/-- An auxiliary operation to `FirstOrder.Language.BoundedFormula.toPrenex`.
  If `φ` and `ψ` are in prenex normal form, then `φ.toPrenexImp ψ`
  is a prenex normal form for `φ.imp ψ`. -/
/-
**FirstOrder.Language.BoundedFormula.toPrenexImp** 是 Mathlib 中的一个定义，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.BoundedFormula α n
 → L.BoundedFormula α n → L.BoundedFormula α n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary operation to `FirstOrder.Language.BoundedFormula.toPrenex`.
  If `φ` and `ψ` are in prenex normal form, then `φ.toPrenexImp ψ`
  is a prenex normal form for `φ.imp ψ`.
-/
def toPrenexImp : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n
  | n, BoundedFormula.ex φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).all
  | n, all φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).ex
  | _, φ, ψ => φ.toPrenexImpRight ψ
/-
**FirstOrder.Language.BoundedFormula.IsQF.toPrenexImp** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.BoundedFormula.IsQF`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {φ ψ : L.BoundedFormula 
α n},   φ.IsQF → φ.toPrenexImp ψ = φ.toPrenexImpRight ψ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsQF.toPrenexImp :
    ∀ {φ ψ : L.BoundedFormula α n}, φ.IsQF → φ.toPrenexImp ψ = φ.toPrenexImpRight ψ
  | _, _, IsQF.falsum => rfl
  | _, _, IsQF.of_isAtomic (IsAtomic.equal _ _) => rfl
  | _, _, IsQF.of_isAtomic (IsAtomic.rel _ _) => rfl
  | _, _, IsQF.imp IsQF.falsum _ => rfl
  | _, _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.equal _ _)) _ => rfl
  | _, _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.rel _ _)) _ => rfl
  | _, _, IsQF.imp (IsQF.imp _ _) _ => rfl
/-
**FirstOrder.Language.BoundedFormula.isPrenex_toPrenexImp** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：isPrenex_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : 
IsPrenex ψ) : IsPrenex (φ.toPrenexImp ψ)
参数：hφ : IsPrenex φ；hψ : IsPrenex ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.toPrenexImp`：∀ {L : FirstOrder.L
anguage} {α : Type u'} {n : ℕ} {φ ψ : L.BoundedFormula α n},   φ.IsQF → φ.toPren
exImp ψ = φ.toPrenexImpRight ψ
· 使用定理 `FirstOrder.Language.BoundedFormula.isPrenex_toPrenexImpRight`：isPrenex_t
oPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ) : I
sPrenex (φ.toPrenexImpRight ψ)
· 使用定理 `FirstOrder.Language.BoundedFormula.IsPrenex.liftAt`：∀ {L : FirstOrder.La
nguage} {α : Type u'} {l : ℕ} {φ : L.BoundedFormula α l} {k m : ℕ},   φ.IsPrenex
 → (FirstOrder.Language.BoundedFormula.l…
-/
theorem isPrenex_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImp ψ) := by
  induction hφ with
  | of_isQF hφ => rw [hφ.toPrenexImp]; exact isPrenex_toPrenexImpRight hφ hψ
  | all _ ih1 => exact (ih1 hψ.liftAt).ex
  | ex _ ih2 => exact (ih2 hψ.liftAt).all

/-- For any bounded formula `φ`, `φ.toPrenex` is a semantically-equivalent formula in prenex normal
  form. -/
/-
**FirstOrder.Language.BoundedFormula.toPrenex** 是 Mathlib 中的一个定义，位于命名空间 `FirstOr
der.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.BoundedFormula α n
 → L.BoundedFormula α n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any bounded formula `φ`, `φ.toPrenex` is a semantically-equivalent formula i
n prenex normal
  form.
-/
def toPrenex : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n
  | _, falsum => ⊥
  | _, equal t₁ t₂ => t₁.bdEqual t₂
  | _, rel R ts => rel R ts
  | _, imp f₁ f₂ => f₁.toPrenex.toPrenexImp f₂.toPrenex
  | _, all f => f.toPrenex.all
/-
**FirstOrder.Language.BoundedFormula.toPrenex_isPrenex** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.BoundedFormula`。
形式化陈述：toPrenex_isPrenex (φ : L.BoundedFormula α n) : φ.toPrenex.IsPrenex
参数：φ : L.BoundedFormula α n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.isPrenex`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF → φ.IsPrenex
· 使用定理 `FirstOrder.Language.BoundedFormula.isQF_bot`：isQF_bot : IsQF (⊥ : L.Boun
dedFormula α n)
· 使用定理 `FirstOrder.Language.BoundedFormula.IsAtomic.isPrenex`：∀ {L : FirstOrder.
Language} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsAtomic → φ.IsPre
nex
· 使用定理 `FirstOrder.Language.BoundedFormula.isPrenex_toPrenexImp`：isPrenex_toPren
exImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ) : IsPrene
x (φ.toPrenexImp ψ)
-/
theorem toPrenex_isPrenex (φ : L.BoundedFormula α n) : φ.toPrenex.IsPrenex :=
  BoundedFormula.recOn φ isQF_bot.isPrenex (fun _ _ => (IsAtomic.equal _ _).isPrenex)
    (fun _ _ => (IsAtomic.rel _ _).isPrenex) (fun _ _ h1 h2 => isPrenex_toPrenexImp h1 h2)
    fun _ => IsPrenex.all

variable [Nonempty M]
/-
**FirstOrder.Language.BoundedFormula.realize_toPrenexImpRight** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : 
IsPrenex ψ) {v : α -> M} {xs : Fin n -> M} : (φ.toPrenexImpRight ψ).Realize v xs
 ↔ (φ.imp ψ).Realize v xs
参数：hφ : IsQF φ；hψ : IsPrenex ψ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.toPrenexImpRight`：∀ {L : FirstOr
der.Language} {α : Type u'} {n : ℕ} {φ ψ : L.BoundedFormula α n}, ψ.IsQF → φ.toP
renexImpRight ψ = φ.imp ψ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.liftAt`：∀ {L : FirstOrder.Langua
ge} {α : Type u'} {l : ℕ} {φ : L.BoundedFormula α l} {k m : ℕ},   φ.IsQF → (Firs
tOrder.Language.BoundedFormula.liftA…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Fin.snoc_comp_castSucc`：snoc_comp_castSucc {α : Sort*} {a : α} {f : Fin 
n -> α} : (snoc f a : Fin (n + 1) -> α) ∘ castSucc = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.BoundedFormula.toPrenexImpRight.eq_def`：∀ {L : First
Order.Language} {α : Type u'} (x : ℕ) (x_1 x_2 : L.BoundedFormula α x),   x_1.to
PrenexImpRight x_2 =     match x, x_1, x_2 with …
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_ex`：realize_ex : θ.ex.Realize
 v xs ↔ exists a : M, θ.Realize v (Fin.snoc xs a)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem realize_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ)
    {v : α → M} {xs : Fin n → M} :
    (φ.toPrenexImpRight ψ).Realize v xs ↔ (φ.imp ψ).Realize v xs := by
  induction hψ with
  | of_isQF hψ => rw [hψ.toPrenexImpRight]
  | all _ ih =>
    refine _root_.trans (forall_congr' fun _ => ih hφ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    exact ⟨fun h1 a h2 => h1 h2 a, fun h1 h2 a => h1 a h2⟩
  | ex _ ih =>
    unfold toPrenexImpRight
    rw [realize_ex]
    refine _root_.trans (exists_congr fun _ => ih hφ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_ex]
    refine ⟨?_, fun h' => ?_⟩
    · rintro ⟨a, ha⟩ h
      exact ⟨a, ha h⟩
    · by_cases h : φ.Realize v xs
      · obtain ⟨a, ha⟩ := h' h
        exact ⟨a, fun _ => ha⟩
      · inhabit M
        exact ⟨default, fun h'' => (h h'').elim⟩
/-
**FirstOrder.Language.BoundedFormula.realize_toPrenexImp** 是 Mathlib 中的一个定理，位于命名
空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : I
sPrenex ψ) {v : α -> M} {xs : Fin n -> M} : (φ.toPrenexImp ψ).Realize v xs ↔ (φ.
imp ψ).Realize v xs
参数：hφ : IsPrenex φ；hψ : IsPrenex ψ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.toPrenexImp`：∀ {L : FirstOrder.L
anguage} {α : Type u'} {n : ℕ} {φ ψ : L.BoundedFormula α n},   φ.IsQF → φ.toPren
exImp ψ = φ.toPrenexImpRight ψ
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_toPrenexImpRight`：realize_toP
renexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ) {v : 
α -> M} {xs : Fin n -> M} : (φ.toPrenexImpRight ψ…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.BoundedFormula.toPrenexImp.eq_def`：∀ {L : FirstOrder
.Language} {α : Type u'} (x : ℕ) (x_1 x_2 : L.BoundedFormula α x),   x_1.toPrene
xImp x_2 =     match x, x_1, x_2 with     |…
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_ex`：realize_ex : θ.ex.Realize
 v xs ↔ exists a : M, θ.Realize v (Fin.snoc xs a)
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `FirstOrder.Language.BoundedFormula.IsPrenex.liftAt`：∀ {L : FirstOrder.La
nguage} {α : Type u'} {l : ℕ} {φ : L.BoundedFormula α l} {k m : ℕ},   φ.IsPrenex
 → (FirstOrder.Language.BoundedFormula.l…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Fin.snoc_comp_castSucc`：snoc_comp_castSucc {α : Sort*} {a : α} {f : Fin 
n -> α} : (snoc f a : Fin (n + 1) -> α) ∘ castSucc = f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `forall_imp_iff_exists_imp`：forall_imp_iff_exists_imp {α : Sort*} {p : α 
-> Prop} {b : Prop} [ha : Nonempty α] : (forall x, p x) -> b ↔ exists x, p x -> 
b
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ)
    {v : α → M} {xs : Fin n → M} : (φ.toPrenexImp ψ).Realize v xs ↔ (φ.imp ψ).Realize v xs := by
  revert ψ
  induction hφ with
  | of_isQF hφ =>
    intro ψ hψ
    rw [hφ.toPrenexImp]
    exact realize_toPrenexImpRight hφ hψ
  | all _ ih =>
    intro ψ hψ
    unfold toPrenexImp
    rw [realize_ex]
    refine _root_.trans (exists_congr fun _ => ih hψ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    exact Iff.symm forall_imp_iff_exists_imp
  | ex _ ih =>
    intro ψ hψ
    refine _root_.trans (forall_congr' fun _ => ih hψ.liftAt) ?_
    simp

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_toPrenex** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_toPrenex (φ : L.BoundedFormula α n) {v : α -> M} : forall {xs : Fi
n n -> M}, φ.toPrenex.Realize v xs ↔ φ.Realize v xs
参数：φ : L.BoundedFormula α n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.toPrenex.eq_4`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} (x : ℕ) (f₁ f₂ : L.BoundedFormula α x),   (f₁.imp f₂).toPren
ex = f₁.toPrenex.toPrenexImp f₂.toPren…
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_toPrenexImp`：realize_toPrenex
Imp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ) {v : α -> M
} {xs : Fin n -> M} : (φ.toPrenexImp ψ).Real…
· 使用定理 `FirstOrder.Language.BoundedFormula.toPrenex_isPrenex`：toPrenex_isPrenex 
(φ : L.BoundedFormula α n) : φ.toPrenex.IsPrenex
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_imp`：realize_imp : (φ.imp ψ).
Realize v xs ↔ φ.Realize v xs -> ψ.Realize v xs
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_all`：realize_all : (all θ).Re
alize v xs ↔ forall a : M, θ.Realize v (Fin.snoc xs a)
· 使用定理 `FirstOrder.Language.BoundedFormula.toPrenex.eq_5`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} (x : ℕ) (f : L.BoundedFormula α (x + 1)), f.all.toPrenex = f
.toPrenex.all
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
-/
theorem realize_toPrenex (φ : L.BoundedFormula α n) {v : α → M} :
    ∀ {xs : Fin n → M}, φ.toPrenex.Realize v xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp f1 f2 h1 h2 =>
    intros
    rw [toPrenex, realize_toPrenexImp f1.toPrenex_isPrenex f2.toPrenex_isPrenex, realize_imp,
      realize_imp, h1, h2]
  | all _ h =>
    intros
    rw [realize_all, toPrenex, realize_all]
    exact forall_congr' fun a => h
/-
**FirstOrder.Language.BoundedFormula.IsQF.induction_on_sup_not** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.BoundedFormula.IsQF`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {P : L.BoundedFormula α 
n → Prop} {φ : L.BoundedFormula α n},   φ.IsQF →     P ⊥ →       (∀ (ψ : L.Bound
edFormula α n), ψ.IsAtomic → P ψ) →         (∀ {φ₁ φ₂ : L.BoundedFormula α n}, P
 φ₁ → P φ₂ → P (φ₁ ⊔ φ₂)) →           (∀ {φ : L.BoundedFormula α n}, P φ → P φ.n
ot) →             (∀ {φ₁ φ₂ : L.BoundedFormula α n}, ∅.Iff φ₁ φ₂ → (P φ₁ ↔ P φ₂)
) → P φ
参数：∀ (ψ : L.BoundedFormula α n), ψ.IsAtomic → P ψ；∀ {φ₁ φ₂ : L.BoundedFormula α 
n}, P φ₁ → P φ₂ → P (φ₁ ⊔ φ₂)；∀ {φ : L.BoundedFormula α n}, P φ → P φ.not；∀ {φ₁ 
φ₂ : L.BoundedFormula α n}, ∅.Iff φ₁ φ₂ → (P φ₁ ↔ P φ₂)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.BoundedFormula.imp_iff_not_sup`：imp_iff_not_sup : (φ
.imp ψ) ⇔[T] (φ.not ⊔ ψ)
-/
theorem IsQF.induction_on_sup_not {P : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : IsQF φ) (hf : P (⊥ : L.BoundedFormula α n))
    (ha : ∀ ψ : L.BoundedFormula α n, IsAtomic ψ → P ψ)
    (hsup : ∀ {φ₁ φ₂}, P φ₁ → P φ₂ → P (φ₁ ⊔ φ₂)) (hnot : ∀ {φ}, P φ → P φ.not)
    (hse :
      ∀ {φ₁ φ₂ : L.BoundedFormula α n}, (φ₁ ⇔[∅] φ₂) → (P φ₁ ↔ P φ₂)) :
    P φ :=
  IsQF.recOn h hf @ha fun {φ₁ φ₂} _ _ h1 h2 =>
    (hse (φ₁.imp_iff_not_sup φ₂)).2 (hsup (hnot h1) h2)
/-
**FirstOrder.Language.BoundedFormula.IsQF.induction_on_inf_not** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.BoundedFormula.IsQF`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {P : L.BoundedFormula α 
n → Prop} {φ : L.BoundedFormula α n},   φ.IsQF →     P ⊥ →       (∀ (ψ : L.Bound
edFormula α n), ψ.IsAtomic → P ψ) →         (∀ {φ₁ φ₂ : L.BoundedFormula α n}, P
 φ₁ → P φ₂ → P (φ₁ ⊓ φ₂)) →           (∀ {φ : L.BoundedFormula α n}, P φ → P φ.n
ot) →             (∀ {φ₁ φ₂ : L.BoundedFormula α n}, ∅.Iff φ₁ φ₂ → (P φ₁ ↔ P φ₂)
) → P φ
参数：∀ (ψ : L.BoundedFormula α n), ψ.IsAtomic → P ψ；∀ {φ₁ φ₂ : L.BoundedFormula α 
n}, P φ₁ → P φ₂ → P (φ₁ ⊓ φ₂)；∀ {φ : L.BoundedFormula α n}, P φ → P φ.not；∀ {φ₁ 
φ₂ : L.BoundedFormula α n}, ∅.Iff φ₁ φ₂ → (P φ₁ ↔ P φ₂)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.induction_on_sup_not`：∀ {L : Fir
stOrder.Language} {α : Type u'} {n : ℕ} {P : L.BoundedFormula α n → Prop} {φ : L
.BoundedFormula α n},   φ.IsQF →     P ⊥ →       (…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.BoundedFormula.sup_iff_not_inf_not`：sup_iff_not_inf_
not : (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not
-/
theorem IsQF.induction_on_inf_not {P : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : IsQF φ) (hf : P (⊥ : L.BoundedFormula α n))
    (ha : ∀ ψ : L.BoundedFormula α n, IsAtomic ψ → P ψ)
    (hinf : ∀ {φ₁ φ₂}, P φ₁ → P φ₂ → P (φ₁ ⊓ φ₂)) (hnot : ∀ {φ}, P φ → P φ.not)
    (hse :
      ∀ {φ₁ φ₂ : L.BoundedFormula α n}, (φ₁ ⇔[∅] φ₂) → (P φ₁ ↔ P φ₂)) :
    P φ :=
  h.induction_on_sup_not hf ha
    (fun {φ₁ φ₂} h1 h2 =>
      (hse (φ₁.sup_iff_not_inf_not φ₂)).2 (hnot (hinf (hnot h1) (hnot h2))))
    (fun {_} => hnot) fun {_ _} => hse
/-
**FirstOrder.Language.BoundedFormula.iff_toPrenex** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.BoundedFormula`。
形式化陈述：iff_toPrenex (φ : L.BoundedFormula α n) : φ ⇔[∅] φ.toPrenex
参数：φ : L.BoundedFormula α n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_iff`：realize_iff : (φ.iff ψ).
Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_toPrenex`：realize_toPrenex (φ
 : L.BoundedFormula α n) {v : α -> M} : forall {xs : Fin n -> M}, φ.toPrenex.Rea
lize v xs ↔ φ.Realize v xs
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem iff_toPrenex (φ : L.BoundedFormula α n) :
    φ ⇔[∅] φ.toPrenex := fun M v xs => by
  rw [realize_iff, realize_toPrenex]
/-
**FirstOrder.Language.BoundedFormula.induction_on_all_ex** 是 Mathlib 中的一个定理，位于命名
空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：induction_on_all_ex {P : forall {m}, L.BoundedFormula α m -> Prop} (φ : L.
BoundedFormula α n) (hqf : forall {m} {ψ : L.BoundedFormula α m}, IsQF ψ -> P ψ)
 (hall : forall {m} {ψ : L.BoundedFormula α (m + 1)}, P ψ -> P ψ.all) (hex : for
all {m} {φ : L.BoundedFormula α (m + 1)}, P φ -> P φ.ex) (hse : forall {m} {φ₁ φ
₂ : L.BoundedFormula α m}, (φ₁ ⇔[∅] φ₂) -> (P φ₁ ↔ P φ₂)) : P φ
参数：φ : L.BoundedFormula α n；hqf : forall {m} {ψ : L.BoundedFormula α m}, IsQF ψ 
-> P ψ；hall : forall {m} {ψ : L.BoundedFormula α (m + 1)}, P ψ -> P ψ.all；hex : 
forall {m} {φ : L.BoundedFormula α (m + 1)}, P φ -> P φ.ex；hse : forall {m} {φ₁ 
φ₂ : L.BoundedFormula α m}, (φ₁ ⇔[∅] φ₂) -> (P φ₁ ↔ P φ₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.BoundedFormula.iff_toPrenex`：iff_toPrenex (φ : L.Bou
ndedFormula α n) : φ ⇔[∅] φ.toPrenex
· 使用定理 `FirstOrder.Language.BoundedFormula.toPrenex_isPrenex`：toPrenex_isPrenex 
(φ : L.BoundedFormula α n) : φ.toPrenex.IsPrenex
-/
theorem induction_on_all_ex {P : ∀ {m}, L.BoundedFormula α m → Prop} (φ : L.BoundedFormula α n)
    (hqf : ∀ {m} {ψ : L.BoundedFormula α m}, IsQF ψ → P ψ)
    (hall : ∀ {m} {ψ : L.BoundedFormula α (m + 1)}, P ψ → P ψ.all)
    (hex : ∀ {m} {φ : L.BoundedFormula α (m + 1)}, P φ → P φ.ex)
    (hse : ∀ {m} {φ₁ φ₂ : L.BoundedFormula α m},
      (φ₁ ⇔[∅] φ₂) → (P φ₁ ↔ P φ₂)) :
    P φ := by
  suffices h' : ∀ {m} {φ : L.BoundedFormula α m}, φ.IsPrenex → P φ from
    (hse φ.iff_toPrenex).2 (h' φ.toPrenex_isPrenex)
  intro m φ hφ
  induction hφ with
  | of_isQF hφ => exact hqf hφ
  | all _ hφ => exact hall hφ
  | ex _ hφ => exact hex hφ
/-
**FirstOrder.Language.BoundedFormula.induction_on_exists_not** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：induction_on_exists_not {P : forall {m}, L.BoundedFormula α m -> Prop} (φ 
: L.BoundedFormula α n) (hqf : forall {m} {ψ : L.BoundedFormula α m}, IsQF ψ -> 
P ψ) (hnot : forall {m} {φ : L.BoundedFormula α m}, P φ -> P φ.not) (hex : foral
l {m} {φ : L.BoundedFormula α (m + 1)}, P φ -> P φ.ex) (hse : forall {m} {φ₁ φ₂ 
: L.BoundedFormula α m}, (φ₁ ⇔[∅] φ₂) -> (P φ₁ ↔ P φ₂)) : P φ
参数：φ : L.BoundedFormula α n；hqf : forall {m} {ψ : L.BoundedFormula α m}, IsQF ψ 
-> P ψ；hnot : forall {m} {φ : L.BoundedFormula α m}, P φ -> P φ.not；hex : forall
 {m} {φ : L.BoundedFormula α (m + 1)}, P φ -> P φ.ex；hse : forall {m} {φ₁ φ₂ : L
.BoundedFormula α m}, (φ₁ ⇔[∅] φ₂) -> (P φ₁ ↔ P φ₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.induction_on_all_ex`：induction_on_all
_ex {P : forall {m}, L.BoundedFormula α m -> Prop} (φ : L.BoundedFormula α n) (h
qf : forall {m} {ψ : L.BoundedFormula α m}, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.BoundedFormula.all_iff_not_ex_not`：all_iff_not_ex_no
t (φ : L.BoundedFormula α (n + 1)) : φ.all ⇔[T] φ.not.ex.not
-/
theorem induction_on_exists_not {P : ∀ {m}, L.BoundedFormula α m → Prop} (φ : L.BoundedFormula α n)
    (hqf : ∀ {m} {ψ : L.BoundedFormula α m}, IsQF ψ → P ψ)
    (hnot : ∀ {m} {φ : L.BoundedFormula α m}, P φ → P φ.not)
    (hex : ∀ {m} {φ : L.BoundedFormula α (m + 1)}, P φ → P φ.ex)
    (hse : ∀ {m} {φ₁ φ₂ : L.BoundedFormula α m},
      (φ₁ ⇔[∅] φ₂) → (P φ₁ ↔ P φ₂)) :
    P φ :=
  φ.induction_on_all_ex (fun {_ _} => hqf)
    (fun {_ φ} hφ => (hse φ.all_iff_not_ex_not).2 (hnot (hex (hnot hφ))))
    (fun {_ _} => hex) fun {_ _ _} => hse

/-- A universal formula is a formula defined by applying only universal quantifiers to a
quantifier-free formula. -/
/-
**FirstOrder.Language.BoundedFormula.IsUniversal** 是 Mathlib 中的一个归纳类型，位于命名空间 `Fi
rstOrder.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.BoundedFormula α n
 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A universal formula is a formula defined by applying only universal quantifiers 
to a
quantifier-free formula.
-/
inductive IsUniversal : ∀ {n}, L.BoundedFormula α n → Prop
  | of_isQF {n : ℕ} {φ : L.BoundedFormula α n} (h : IsQF φ) : IsUniversal φ
  | all {n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsUniversal φ) : IsUniversal φ.all
/-
**FirstOrder.Language.BoundedFormula.IsQF.isUniversal** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.BoundedFormula.IsQF`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α 
n}, φ.IsQF → φ.IsUniversal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsQF.isUniversal {φ : L.BoundedFormula α n} : IsQF φ → IsUniversal φ :=
  IsUniversal.of_isQF
/-
**FirstOrder.Language.BoundedFormula.IsAtomic.isUniversal** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.BoundedFormula.IsAtomic`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α 
n}, φ.IsAtomic → φ.IsUniversal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.isUniversal`：∀ {L : FirstOrder.L
anguage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF → φ.IsUniversa
l
· 使用定理 `FirstOrder.Language.BoundedFormula.IsAtomic.isQF`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsAtomic → φ.IsQF
-/
lemma IsAtomic.isUniversal {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsUniversal φ :=
  h.isQF.isUniversal

/-- An existential formula is a formula defined by applying only existential quantifiers to a
quantifier-free formula. -/
/-
**FirstOrder.Language.BoundedFormula.IsExistential** 是 Mathlib 中的一个归纳类型，位于命名空间 `
FirstOrder.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.BoundedFormula α n
 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An existential formula is a formula defined by applying only existential quantif
iers to a
quantifier-free formula.
-/
inductive IsExistential : ∀ {n}, L.BoundedFormula α n → Prop
  | of_isQF {n : ℕ} {φ : L.BoundedFormula α n} (h : IsQF φ) : IsExistential φ
  | ex {n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsExistential φ) : IsExistential φ.ex
/-
**FirstOrder.Language.BoundedFormula.IsQF.isExistential** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.BoundedFormula.IsQF`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α 
n}, φ.IsQF → φ.IsExistential
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsQF.isExistential {φ : L.BoundedFormula α n} : IsQF φ → IsExistential φ :=
  IsExistential.of_isQF
/-
**FirstOrder.Language.BoundedFormula.IsAtomic.isExistential** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Language.BoundedFormula.IsAtomic`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α 
n}, φ.IsAtomic → φ.IsExistential
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.isExistential`：∀ {L : FirstOrder
.Language} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF → φ.IsExiste
ntial
· 使用定理 `FirstOrder.Language.BoundedFormula.IsAtomic.isQF`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsAtomic → φ.IsQF
-/
lemma IsAtomic.isExistential {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsExistential φ :=
  h.isQF.isExistential

section Preservation

variable {M : Type*} [L.Structure M] {N : Type*} [L.Structure N]
variable {F : Type*} [FunLike F M N]

/-
**FirstOrder.Language.BoundedFormula.IsAtomic.realize_comp_of_injective** 是 Math
lib 中的一个定理，位于命名空间 `FirstOrder.Language.BoundedFormula.IsAtomic`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {M : Type u_1} [inst : L
.Structure M] {N : Type u_2}   [inst_1 : L.Structure N] {F : Type u_3} [inst_2 :
 FunLike F M N] {φ : L.BoundedFormula α n},   φ.IsAtomic →     ∀ [L.HomClass F M
 N] {f : F},       Function.Injective ⇑f → ∀ {v : α → M} {xs : Fin n → M}, φ.Rea
lize v xs → φ.Realize (⇑f ∘ v) (⇑f ∘ xs)
参数：⇑f ∘ v；⇑f ∘ xs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.HomClass.realize_term`：∀ {L : FirstOrder.Language} {
M : Type w} {N : Type u_1} [inst : L.Structure M] [inst_1 : L.Structure N] {α : 
Type u'}   {F : Type u_4} [inst…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.HomClass.map_rel`：∀ {L : outParam FirstOrder.Languag
e} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {inst : 
FunLike F M N} {inst_1 : L…
-/
lemma IsAtomic.realize_comp_of_injective {φ : L.BoundedFormula α n} (hA : φ.IsAtomic)
    [L.HomClass F M N] {f : F} (hInj : Function.Injective f) {v : α → M} {xs : Fin n → M} :
    φ.Realize v xs → φ.Realize (f ∘ v) (f ∘ xs) := by
  induction hA with
  | equal t₁ t₂ => simp only [realize_bdEqual, ← Sum.comp_elim, HomClass.realize_term, hInj.eq_iff,
    imp_self]
  | rel R ts =>
    simp only [realize_rel, ← Sum.comp_elim, HomClass.realize_term]
    exact HomClass.map_rel f R (fun i => Term.realize (Sum.elim v xs) (ts i))
/-
**FirstOrder.Language.BoundedFormula.IsAtomic.realize_comp** 是 Mathlib 中的一个定理，位于
命名空间 `FirstOrder.Language.BoundedFormula.IsAtomic`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {M : Type u_1} [inst : L
.Structure M] {N : Type u_2}   [inst_1 : L.Structure N] {F : Type u_3} [inst_2 :
 FunLike F M N] {φ : L.BoundedFormula α n},   φ.IsAtomic →     ∀ [EmbeddingLike 
F M N] [L.HomClass F M N] (f : F) {v : α → M} {xs : Fin n → M},       φ.Realize 
v xs → φ.Realize (⇑f ∘ v) (⇑f ∘ xs)
参数：f : F；⇑f ∘ v；⇑f ∘ xs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsAtomic.realize_comp_of_injective`：∀
 {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {M : Type u_1} [inst : L.Struct
ure M] {N : Type u_2}   [inst_1 : L.Structure N] {F : Type …
· 使用定理 `EmbeddingLike.injective`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} 
[inst : FunLike F α β] [i : EmbeddingLike F α β] (f : F),   Function.Injective ⇑
f
-/
lemma IsAtomic.realize_comp {φ : L.BoundedFormula α n} (hA : φ.IsAtomic)
    [EmbeddingLike F M N] [L.HomClass F M N] (f : F) {v : α → M} {xs : Fin n → M} :
    φ.Realize v xs → φ.Realize (f ∘ v) (f ∘ xs) :=
  hA.realize_comp_of_injective (EmbeddingLike.injective f)

variable [EmbeddingLike F M N] [L.StrongHomClass F M N]
/-
**FirstOrder.Language.BoundedFormula.IsQF.realize_embedding** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Language.BoundedFormula.IsQF`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {M : Type u_1} [inst : L
.Structure M] {N : Type u_2}   [inst_1 : L.Structure N] {F : Type u_3} [inst_2 :
 FunLike F M N] [EmbeddingLike F M N] [L.StrongHomClass F M N]   {φ : L.BoundedF
ormula α n},   φ.IsQF → ∀ (f : F) {v : α → M} {xs : Fin n → M}, φ.Realize (⇑f ∘ 
v) (⇑f ∘ xs) ↔ φ.Realize v xs
参数：f : F；⇑f ∘ v；⇑f ∘ xs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.HomClass.realize_term`：∀ {L : FirstOrder.Language} {
M : Type w} {N : Type u_1} [inst : L.Structure M] [inst_1 : L.Structure N] {α : 
Type u'}   {F : Type u_4} [inst…
· 使用定理 `FirstOrder.Language.StrongHomClass.homClass`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] {F :
 Type u_3}   [inst_2 : FunLike F …
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `EmbeddingLike.injective`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} 
[inst : FunLike F α β] [i : EmbeddingLike F α β] (f : F),   Function.Injective ⇑
f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.StrongHomClass.map_rel`：∀ {L : outParam FirstOrder.L
anguage} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {i
nst : FunLike F M N} {inst_1 : L…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma IsQF.realize_embedding {φ : L.BoundedFormula α n} (hQF : φ.IsQF)
    (f : F) {v : α → M} {xs : Fin n → M} :
    φ.Realize (f ∘ v) (f ∘ xs) ↔ φ.Realize v xs := by
  induction hQF with
  | falsum => rfl
  | of_isAtomic hA => induction hA with
    | equal t₁ t₂ => simp only [realize_bdEqual, ← Sum.comp_elim, HomClass.realize_term,
        (EmbeddingLike.injective f).eq_iff]
    | rel R ts =>
      simp only [realize_rel, ← Sum.comp_elim, HomClass.realize_term]
      exact StrongHomClass.map_rel f R (fun i => Term.realize (Sum.elim v xs) (ts i))
  | imp _ _ ihφ ihψ => simp only [realize_imp, ihφ, ihψ]
/-
**FirstOrder.Language.BoundedFormula.IsUniversal.realize_embedding** 是 Mathlib 中
的一个定理，位于命名空间 `FirstOrder.Language.BoundedFormula.IsUniversal`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {M : Type u_1} [inst : L
.Structure M] {N : Type u_2}   [inst_1 : L.Structure N] {F : Type u_3} [inst_2 :
 FunLike F M N] [EmbeddingLike F M N] [L.StrongHomClass F M N]   {φ : L.BoundedF
ormula α n},   φ.IsUniversal → ∀ (f : F) {v : α → M} {xs : Fin n → M}, φ.Realize
 (⇑f ∘ v) (⇑f ∘ xs) → φ.Realize v xs
参数：f : F；⇑f ∘ v；⇑f ∘ xs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.realize_embedding`：∀ {L : FirstO
rder.Language} {α : Type u'} {n : ℕ} {M : Type u_1} [inst : L.Structure M] {N : 
Type u_2}   [inst_1 : L.Structure N] {F : Type …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.comp_snoc`：comp_snoc {α : Sort*} {β : Sort*} (g : α -> β) (q : Fin n
 -> α) (y : α) : g ∘ snoc q y = snoc (g ∘ q) (g y)
-/
lemma IsUniversal.realize_embedding {φ : L.BoundedFormula α n} (hU : φ.IsUniversal)
    (f : F) {v : α → M} {xs : Fin n → M} :
    φ.Realize (f ∘ v) (f ∘ xs) → φ.Realize v xs := by
  induction hU with
  | of_isQF hQF => simp [hQF.realize_embedding]
  | all _ ih =>
    simp only [realize_all, Nat.succ_eq_add_one]
    refine fun h a => ih ?_
    rw [Fin.comp_snoc]
    exact h (f a)
/-
**FirstOrder.Language.BoundedFormula.IsExistential.realize_embedding** 是 Mathlib
 中的一个定理，位于命名空间 `FirstOrder.Language.BoundedFormula.IsExistential`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type u'} {n : ℕ} {M : Type u_1} [inst : L
.Structure M] {N : Type u_2}   [inst_1 : L.Structure N] {F : Type u_3} [inst_2 :
 FunLike F M N] [EmbeddingLike F M N] [L.StrongHomClass F M N]   {φ : L.BoundedF
ormula α n},   φ.IsExistential → ∀ (f : F) {v : α → M} {xs : Fin n → M}, φ.Reali
ze v xs → φ.Realize (⇑f ∘ v) (⇑f ∘ xs)
参数：f : F；⇑f ∘ v；⇑f ∘ xs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.realize_embedding`：∀ {L : FirstO
rder.Language} {α : Type u'} {n : ℕ} {M : Type u_1} [inst : L.Structure M] {N : 
Type u_2}   [inst_1 : L.Structure N] {F : Type …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.comp_snoc`：comp_snoc {α : Sort*} {β : Sort*} (g : α -> β) (q : Fin n
 -> α) (y : α) : g ∘ snoc q y = snoc (g ∘ q) (g y)
-/
lemma IsExistential.realize_embedding {φ : L.BoundedFormula α n} (hE : φ.IsExistential)
    (f : F) {v : α → M} {xs : Fin n → M} :
    φ.Realize v xs → φ.Realize (f ∘ v) (f ∘ xs) := by
  induction hE with
  | of_isQF hQF => simp [hQF.realize_embedding]
  | ex _ ih =>
    simp only [realize_ex, Nat.succ_eq_add_one]
    refine fun ⟨a, ha⟩ => ⟨f a, ?_⟩
    rw [← Fin.comp_snoc]
    exact ih ha

end Preservation

end BoundedFormula

/-- A theory is universal when it is comprised only of universal sentences - these theories apply
also to substructures. -/
/-
**FirstOrder.Language.Theory.IsUniversal** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder
.Language.Theory`。
形式化陈述：{L : FirstOrder.Language} → L.Theory → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A theory is universal when it is comprised only of universal sentences - these t
heories apply
also to substructures.
-/
class Theory.IsUniversal (T : L.Theory) : Prop where
  isUniversal_of_mem : ∀ ⦃φ⦄, φ ∈ T → φ.IsUniversal
/-
**FirstOrder.Language.Theory.IsUniversal.models_of_embedding** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.Theory.IsUniversal`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} [inst : L.Structure M] {T : L.The
ory} [hT : T.IsUniversal] {N : Type u_1}   [inst_1 : L.Structure N] [N ⊨ T] (f :
 L.Embedding M N), M ⊨ T
参数：f : L.Embedding M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsUniversal.realize_embedding`：∀ {L :
 FirstOrder.Language} {α : Type u'} {n : ℕ} {M : Type u_1} [inst : L.Structure M
] {N : Type u_2}   [inst_1 : L.Structure N] {F : Type …
· 使用定理 `FirstOrder.Language.Theory.IsUniversal.isUniversal_of_mem`：∀ {L : FirstO
rder.Language} {T : L.Theory} [self : T.IsUniversal] ⦃φ : L.Sentence⦄,   φ ∈ T →
 FirstOrder.Language.BoundedFormula.IsUniversal…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `FirstOrder.Language.Theory.realize_sentence_of_mem`：∀ {L : FirstOrder.La
nguage} {M : Type w} [inst : L.Structure M] (T : L.Theory) [M ⊨ T] {φ : L.Senten
ce}, φ ∈ T → M ⊨ φ
-/
lemma Theory.IsUniversal.models_of_embedding {T : L.Theory} [hT : T.IsUniversal]
    {N : Type*} [L.Structure N] [N ⊨ T] (f : M ↪[L] N) : M ⊨ T := by
  simp only [model_iff]
  refine fun φ hφ => (hT.isUniversal_of_mem hφ).realize_embedding f (?_)
  rw [Subsingleton.elim (f ∘ default) default, Subsingleton.elim (f ∘ default) default]
  exact Theory.realize_sentence_of_mem T hφ
/-
**FirstOrder.Language.Substructure.models_of_isUniversal** 是 Mathlib 中的一个定理，位于命名
空间 `FirstOrder.Language.Substructure`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} [inst : L.Structure M] (S : L.Sub
structure M) (T : L.Theory) [T.IsUniversal]   [M ⊨ T], ↥S ⊨ T
参数：S : L.Substructure M；T : L.Theory。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.IsUniversal.models_of_embedding`：∀ {L : First
Order.Language} {M : Type w} [inst : L.Structure M] {T : L.Theory} [hT : T.IsUni
versal] {N : Type u_1}   [inst_1 : L.Structure N…
-/
instance Substructure.models_of_isUniversal
    (S : L.Substructure M) (T : L.Theory) [T.IsUniversal] [M ⊨ T] : S ⊨ T :=
  Theory.IsUniversal.models_of_embedding (Substructure.subtype S)
/-
**FirstOrder.Language.Theory.IsUniversal.insert** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Theory.IsUniversal`。
形式化陈述：∀ {L : FirstOrder.Language} {T : L.Theory} [hT : T.IsUniversal] {φ : L.Sen
tence},   FirstOrder.Language.BoundedFormula.IsUniversal φ → (insert φ T).IsUniv
ersal
参数：insert φ T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `FirstOrder.Language.Theory.IsUniversal.isUniversal_of_mem`：∀ {L : FirstO
rder.Language} {T : L.Theory} [self : T.IsUniversal] ⦃φ : L.Sentence⦄,   φ ∈ T →
 FirstOrder.Language.BoundedFormula.IsUniversal…
-/
lemma Theory.IsUniversal.insert
    {T : L.Theory} [hT : T.IsUniversal] {φ : L.Sentence} (hφ : φ.IsUniversal) :
    (insert φ T).IsUniversal := ⟨by
  simp only [Set.mem_insert_iff, forall_eq_or_imp, hφ, true_and]
  exact hT.isUniversal_of_mem⟩

namespace Relations

open BoundedFormula

/-
**FirstOrder.Language.Relations.isAtomic** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.L
anguage.Relations`。
形式化陈述：isAtomic (r : L.Relations l) (ts : Fin l -> L.Term (α oplus (Fin n))) : Is
Atomic (r.boundedFormula ts)
参数：r : L.Relations l；ts : Fin l -> L.Term (α oplus (Fin n))。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isAtomic (r : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) :
    IsAtomic (r.boundedFormula ts) := IsAtomic.rel r ts
/-
**FirstOrder.Language.Relations.isQF** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.Langu
age.Relations`。
形式化陈述：isQF (r : L.Relations l) (ts : Fin l -> L.Term (α oplus (Fin n))) : IsQF (
r.boundedFormula ts)
参数：r : L.Relations l；ts : Fin l -> L.Term (α oplus (Fin n))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsAtomic.isQF`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsAtomic → φ.IsQF
· 使用引理 `FirstOrder.Language.Relations.isAtomic`：isAtomic (r : L.Relations l) (ts
 : Fin l -> L.Term (α oplus (Fin n))) : IsAtomic (r.boundedFormula ts)
-/
lemma isQF (r : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) :
    IsQF (r.boundedFormula ts) := (r.isAtomic ts).isQF

variable (r : L.Relations 2)
/-
**FirstOrder.Language.Relations.isUniversal_reflexive** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.Relations`。
形式化陈述：∀ {L : FirstOrder.Language} (r : L.Relations 2), FirstOrder.Language.Bound
edFormula.IsUniversal r.reflexive
参数：r : L.Relations 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.isUniversal`：∀ {L : FirstOrder.L
anguage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF → φ.IsUniversa
l
· 使用引理 `FirstOrder.Language.Relations.isQF`：isQF (r : L.Relations l) (ts : Fin l
 -> L.Term (α oplus (Fin n))) : IsQF (r.boundedFormula ts)
-/
protected lemma isUniversal_reflexive : r.reflexive.IsUniversal :=
  (r.isQF _).isUniversal.all
/-
**FirstOrder.Language.Relations.isUniversal_irreflexive** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.Relations`。
形式化陈述：∀ {L : FirstOrder.Language} (r : L.Relations 2), FirstOrder.Language.Bound
edFormula.IsUniversal r.irreflexive
参数：r : L.Relations 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.isUniversal`：∀ {L : FirstOrder.L
anguage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF → φ.IsUniversa
l
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.not`：not {φ : L.BoundedFormula α
 n} (h : IsQF φ) : IsQF φ.not
· 使用定理 `FirstOrder.Language.BoundedFormula.IsAtomic.isQF`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsAtomic → φ.IsQF
· 使用引理 `FirstOrder.Language.Relations.isAtomic`：isAtomic (r : L.Relations l) (ts
 : Fin l -> L.Term (α oplus (Fin n))) : IsAtomic (r.boundedFormula ts)
-/
protected lemma isUniversal_irreflexive : r.irreflexive.IsUniversal :=
  (r.isAtomic _).isQF.not.isUniversal.all
/-
**FirstOrder.Language.Relations.isUniversal_symmetric** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.Relations`。
形式化陈述：∀ {L : FirstOrder.Language} (r : L.Relations 2), FirstOrder.Language.Bound
edFormula.IsUniversal r.symmetric
参数：r : L.Relations 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.isUniversal`：∀ {L : FirstOrder.L
anguage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF → φ.IsUniversa
l
· 使用引理 `FirstOrder.Language.Relations.isQF`：isQF (r : L.Relations l) (ts : Fin l
 -> L.Term (α oplus (Fin n))) : IsQF (r.boundedFormula ts)
-/
protected lemma isUniversal_symmetric : r.symmetric.IsUniversal :=
  ((r.isQF _).imp (r.isQF _)).isUniversal.all.all
/-
**FirstOrder.Language.Relations.isUniversal_antisymmetric** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.Relations`。
形式化陈述：∀ {L : FirstOrder.Language} (r : L.Relations 2), FirstOrder.Language.Bound
edFormula.IsUniversal r.antisymmetric
参数：r : L.Relations 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.isUniversal`：∀ {L : FirstOrder.L
anguage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF → φ.IsUniversa
l
· 使用引理 `FirstOrder.Language.Relations.isQF`：isQF (r : L.Relations l) (ts : Fin l
 -> L.Term (α oplus (Fin n))) : IsQF (r.boundedFormula ts)
· 使用定理 `FirstOrder.Language.BoundedFormula.IsAtomic.isQF`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsAtomic → φ.IsQF
-/
protected lemma isUniversal_antisymmetric : r.antisymmetric.IsUniversal :=
  ((r.isQF _).imp ((r.isQF _).imp (IsAtomic.equal _ _).isQF)).isUniversal.all.all
/-
**FirstOrder.Language.Relations.isUniversal_transitive** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Relations`。
形式化陈述：∀ {L : FirstOrder.Language} (r : L.Relations 2), FirstOrder.Language.Bound
edFormula.IsUniversal r.transitive
参数：r : L.Relations 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.isUniversal`：∀ {L : FirstOrder.L
anguage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF → φ.IsUniversa
l
· 使用引理 `FirstOrder.Language.Relations.isQF`：isQF (r : L.Relations l) (ts : Fin l
 -> L.Term (α oplus (Fin n))) : IsQF (r.boundedFormula ts)
-/
protected lemma isUniversal_transitive : r.transitive.IsUniversal :=
  ((r.isQF _).imp ((r.isQF _).imp (r.isQF _))).isUniversal.all.all.all
/-
**FirstOrder.Language.Relations.isUniversal_total** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Relations`。
形式化陈述：∀ {L : FirstOrder.Language} (r : L.Relations 2), FirstOrder.Language.Bound
edFormula.IsUniversal r.total
参数：r : L.Relations 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.isUniversal`：∀ {L : FirstOrder.L
anguage} {α : Type u'} {n : ℕ} {φ : L.BoundedFormula α n}, φ.IsQF → φ.IsUniversa
l
· 使用定理 `FirstOrder.Language.BoundedFormula.IsQF.sup`：sup {φ ψ : L.BoundedFormula
 α n} (hφ : IsQF φ) (hψ : IsQF ψ) : IsQF (φ ⊔ ψ)
· 使用引理 `FirstOrder.Language.Relations.isQF`：isQF (r : L.Relations l) (ts : Fin l
 -> L.Term (α oplus (Fin n))) : IsQF (r.boundedFormula ts)
-/
protected lemma isUniversal_total : r.total.IsUniversal :=
  ((r.isQF _).sup (r.isQF _)).isUniversal.all.all

end Relations

/-
**FirstOrder.Language.Formula.isAtomic_graph** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Formula`。
形式化陈述：∀ {L : FirstOrder.Language} {n : ℕ} (f : L.Functions n),   FirstOrder.Lang
uage.BoundedFormula.IsAtomic (FirstOrder.Language.Formula.graph f)
参数：f : L.Functions n；FirstOrder.Language.Formula.graph f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Formula.isAtomic_graph (f : L.Functions n) : (Formula.graph f).IsAtomic :=
  BoundedFormula.IsAtomic.equal _ _

end Language

end FirstOrder

