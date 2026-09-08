/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos Fernández, Xavier Généreux
-/
module

public import Mathlib.Algebra.SkewMonoidAlgebra.Basic
/-!
# Modifying skew monoid algebra at exactly one point

This file contains basic results on updating/erasing an element of a skew monoid algebra using
one point of the domain.
-/

@[expose] public section

noncomputable section

namespace SkewMonoidAlgebra

variable {k G H : Type*}

section erase

variable {M α : Type*} [AddCommMonoid M] (a a' : α) (b : M) (f : SkewMonoidAlgebra M α)

/--
Given an element `f` of a skew monoid algebra, `erase a f` is an element with the same coefficients
as `f` except at `a` where the coefficient is `0`.
If `a` is not in the support of `f` then `erase a f = f`. -/
/-
**SkewMonoidAlgebra.erase** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：{M : Type u_4} → {α : Type u_5} → [inst : AddCommMonoid M] → α → SkewMonoi
dAlgebra M α →+ SkewMonoidAlgebra M α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an element `f` of a skew monoid algebra, `erase a f` is an element with th
e same coefficients
as `f` except at `a` where the coefficient is `0`.
If `a` is not in the support of `f` then `erase a f = f`.
-/
@[simps] def erase : SkewMonoidAlgebra M α →+ SkewMonoidAlgebra M α where
  toFun f := ⟨f.coeff.erase a⟩
  map_zero' := by simp
  map_add' := by simp

@[deprecated (since := "2026-07-04")] alias erase_apply_toFinsupp := coeff_erase_apply

@[simp]
/-
**SkewMonoidAlgebra.support_erase** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：support_erase [DecidableEq α] : (f.erase a).support = f.support.erase a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SkewMonoidAlgebra.support_ofCoeff`：support_ofCoeff (p) : support (⟨p⟩ : 
SkewMonoidAlgebra k G) = p.support
· 使用定理 `Finsupp.support_erase`：support_erase [DecidableEq α] {a : α} {f : α ->₀ 
M} : (f.erase a).support = f.support.erase a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_erase [DecidableEq α] : (f.erase a).support = f.support.erase a := by
  ext; simp [erase]

@[deprecated Finsupp.erase_same (since := "2026-07-04")]
/-
**SkewMonoidAlgebra.coeff_erase_same** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：coeff_erase_same : (f.erase a).coeff a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.erase_same`：erase_same {a : α} {f : α ->₀ M} : (f.erase a) a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_erase_same : (f.erase a).coeff a = 0 := by
  simp [erase]

variable {a a'} in
@[deprecated Finsupp.erase_ne (since := "2026-07-04")]
/-
**SkewMonoidAlgebra.coeff_erase_ne** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：coeff_erase_ne (h : a' != a) : (f.erase a).coeff a' = f.coeff a'
参数：h : a' != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.erase_ne`：erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.e
rase a) a' = f a'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_erase_ne (h : a' ≠ a) : (f.erase a).coeff a' = f.coeff a' := by
  simp [erase, h]

@[simp]
/-
**SkewMonoidAlgebra.erase_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：erase_single : erase a (single a b) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.erase_single`：erase_single {a : α} {b : M} : erase a (single a b
) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem erase_single : erase a (single a b) = 0 := by
  simp [erase]
/-
**SkewMonoidAlgebra.single_add_erase** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：single_add_erase (a : α) (f : SkewMonoidAlgebra M α) : single a (f.coeff a
) + f.erase a = f
参数：a : α；f : SkewMonoidAlgebra M α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.ext`：ext {p q : SkewMonoidAlgebra k G} : (forall a, co
eff p a = coeff q a) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_add`：coeff_add (a b : SkewMonoidAlgebra k G) : (
a + b).coeff = a.coeff + b.coeff
· 使用定理 `SkewMonoidAlgebra.coeff_erase_apply`：∀ {M : Type u_4} {α : Type u_5} [in
st : AddCommMonoid M] (a : α) (f : SkewMonoidAlgebra M α),   ((SkewMonoidAlgebra
.erase a) f).coeff = Fins…
· 使用引理 `Finsupp.single_add_erase`：single_add_erase (a : ι) (f : ι ->₀ M) : singl
e a (f a) + f.erase a = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_add_erase (a : α) (f : SkewMonoidAlgebra M α) :
    single a (f.coeff a) + f.erase a = f := by
  ext; simp [ coeff_add, Finsupp.single_add_erase]

@[elab_as_elim]
/-
**SkewMonoidAlgebra.induction** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：induction {p : SkewMonoidAlgebra M α -> Prop} (f : SkewMonoidAlgebra M α) 
(h0 : p 0) (ha : forall (a b) (f : SkewMonoidAlgebra M α), a ∉ f.support -> b !=
 0 -> p f -> p (single a b + f)) : p f
参数：f : SkewMonoidAlgebra M α；h0 : p 0；ha : forall (a b) (f : SkewMonoidAlgebra M
 α), a ∉ f.support -> b != 0 -> p f -> p (single a b + f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SkewMonoidAlgebra.support_eq_empty`：support_eq_empty {p} : p.support = ∅
 ↔ (p : SkewMonoidAlgebra k G) = 0
· 使用定理 `SkewMonoidAlgebra.support_erase`：support_erase [DecidableEq α] : (f.eras
e a).support = f.support.erase a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.erase_cons`：erase_cons {s : Finset α} {a : α} (h : a ∉ s) : (s.co
ns a h).erase a = s
· 使用定理 `SkewMonoidAlgebra.single_add_erase`：single_add_erase (a : α) (f : SkewMo
noidAlgebra M α) : single a (f.coeff a) + f.erase a = f
-/
theorem induction {p : SkewMonoidAlgebra M α → Prop} (f : SkewMonoidAlgebra M α) (h0 : p 0)
    (ha : ∀ (a b) (f : SkewMonoidAlgebra M α), a ∉ f.support → b ≠ 0 → p f → p (single a b + f)) :
    p f :=
  suffices ∀ (s) (f : SkewMonoidAlgebra M α), f.support = s → p f from this _ _ rfl
  fun s ↦
  Finset.cons_induction_on s (fun f hf ↦ by rwa [support_eq_empty.1 hf]) fun a s has ih f hf ↦ by
    suffices p (single a (f.coeff a) + f.erase a) by rwa [single_add_erase] at this
    classical
    apply ha
    · rw [support_erase, Finset.mem_erase]
      exact fun H ↦ H.1 rfl
    · simp only [← mem_support_iff, hf, Finset.mem_cons_self]
    · apply ih
      rw [support_erase, hf, Finset.erase_cons]

end erase

section update

variable {M α : Type*} [AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a a' : α) (b : M)

/-- Replace the coefficient of an element `f` of a skew monoid algebra at a given point `a : α` by
a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the support of `f`.
Otherwise, if `a` was not in the `support` of `f`, it is added to it. -/
/-
**SkewMonoidAlgebra.update** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：{M : Type u_4} → {α : Type u_5} → [inst : AddCommMonoid M] → SkewMonoidAlg
ebra M α → α → M → SkewMonoidAlgebra M α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace the coefficient of an element `f` of a skew monoid algebra at a given po
int `a : α` by
a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the support of `f`.
Otherwise, if `a` was not in the `support` of `f`, it is added to it.
-/
@[simps coeff] def update : SkewMonoidAlgebra M α :=
  ⟨f.coeff.update a b⟩

@[deprecated (since := "2026-07-04")] alias update_toFinsupp := coeff_update

@[simp]
/-
**SkewMonoidAlgebra.update_self** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：update_self : f.update a (f.coeff a) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.ext`：ext {p q : SkewMonoidAlgebra k G} : (forall a, co
eff p a = coeff q a) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_update`：∀ {M : Type u_4} {α : Type u_5} [inst : 
AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a : α) (b : M),   (f.update a b).c
oeff = f.coeff.updat…
· 使用定理 `Finsupp.update_self`：update_self : f.update a (f a) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem update_self : f.update a (f.coeff a) = f := by ext; simp

@[simp]
/-
**SkewMonoidAlgebra.zero_update** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：zero_update : update 0 a b = single a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_update : update 0 a b = single a b := by
  simp [update]
/-
**SkewMonoidAlgebra.support_update** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：support_update [DecidableEq α] [DecidableEq M] : support (f.update a b) = 
if b = 0 then f.support.erase a else insert a f.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.support_ofCoeff`：support_ofCoeff (p) : support (⟨p⟩ : 
SkewMonoidAlgebra k G) = p.support
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finsupp.support_update_ne_zero`：support_update_ne_zero [DecidableEq α] (
h : b != 0) : support (f.update a b) = insert a f.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finsupp.support_update_zero`：support_update_zero [DecidableEq α] : suppo
rt (f.update a 0) = f.support.erase a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem support_update [DecidableEq α] [DecidableEq M] :
    support (f.update a b) = if b = 0 then f.support.erase a else insert a f.support := by
  aesop (add norm [update, Finsupp.support_update_ne_zero])

@[deprecated Finsupp.update_apply (since := "2026-07-04")]
/-
**SkewMonoidAlgebra.coeff_update_apply** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlge
bra`。
形式化陈述：coeff_update_apply [DecidableEq α] : (f.update a b).coeff a' = if a' = a t
hen b else f.coeff a'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_update`：∀ {M : Type u_4} {α : Type u_5} [inst : 
AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a : α) (b : M),   (f.update a b).c
oeff = f.coeff.updat…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_update_apply [DecidableEq α] :
    (f.update a b).coeff a' = if a' = a then b else f.coeff a' := by
  simp [coeff_update, Function.update_apply]

@[deprecated Finsupp.update_apply (since := "2026-07-04")]
/-
**SkewMonoidAlgebra.coeff_update_same** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgeb
ra`。
形式化陈述：coeff_update_same : (f.update a b).coeff a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_update_apply`：coeff_update_apply [DecidableEq α]
 : (f.update a b).coeff a' = if a' = a then b else f.coeff a'
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem coeff_update_same : (f.update a b).coeff a = b := by
  classical
  rw [f.coeff_update_apply, if_pos rfl]

variable {a a'} in
@[deprecated Finsupp.update_apply (since := "2026-07-04")]
/-
**SkewMonoidAlgebra.coeff_update_ne** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra
`。
形式化陈述：coeff_update_ne (h : a' != a) : (f.update a b).coeff a' = f.coeff a'
参数：h : a' != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_update_apply`：coeff_update_apply [DecidableEq α]
 : (f.update a b).coeff a' = if a' = a then b else f.coeff a'
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem coeff_update_ne (h : a' ≠ a) : (f.update a b).coeff a' = f.coeff a' := by
  classical
  rw [f.coeff_update_apply, if_neg h]
/-
**SkewMonoidAlgebra.update_eq_erase_add_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMo
noidAlgebra`。
形式化陈述：update_eq_erase_add_single : f.update a b = f.erase a + single a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.ext`：ext {p q : SkewMonoidAlgebra k G} : (forall a, co
eff p a = coeff q a) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SkewMonoidAlgebra.coeff_update`：∀ {M : Type u_4} {α : Type u_5} [inst : 
AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a : α) (b : M),   (f.update a b).c
oeff = f.coeff.updat…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `SkewMonoidAlgebra.coeff_add`：coeff_add (a b : SkewMonoidAlgebra k G) : (
a + b).coeff = a.coeff + b.coeff
· 使用定理 `SkewMonoidAlgebra.coeff_erase_apply`：∀ {M : Type u_4} {α : Type u_5} [in
st : AddCommMonoid M] (a : α) (f : SkewMonoidAlgebra M α),   ((SkewMonoidAlgebra
.erase a) f).coeff = Fins…
· 使用定理 `Finsupp.erase_same`：erase_same {a : α} {f : α ->₀ M} : (f.erase a) a = 0
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.erase_ne`：erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.e
rase a) a' = f a'
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem update_eq_erase_add_single : f.update a b = f.erase a + single a b := by
  classical ext x; by_cases hx : x = a <;> aesop (add norm coeff_single_apply)

@[simp]
/-
**SkewMonoidAlgebra.update_zero_eq_erase** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAl
gebra`。
形式化陈述：update_zero_eq_erase : f.update a 0 = f.erase a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.ext`：ext {p q : SkewMonoidAlgebra k G} : (forall a, co
eff p a = coeff q a) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SkewMonoidAlgebra.coeff_update`：∀ {M : Type u_4} {α : Type u_5} [inst : 
AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a : α) (b : M),   (f.update a b).c
oeff = f.coeff.updat…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用定理 `SkewMonoidAlgebra.coeff_erase_apply`：∀ {M : Type u_4} {α : Type u_5} [in
st : AddCommMonoid M] (a : α) (f : SkewMonoidAlgebra M α),   ((SkewMonoidAlgebra
.erase a) f).coeff = Fins…
· 使用定理 `Finsupp.erase_apply`：erase_apply [DecidableEq α] {a a' : α} {f : α ->₀ M
} : f.erase a a' = if a' = a then 0 else f a'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem update_zero_eq_erase : f.update a 0 = f.erase a := by
  classical ext; simp [coeff_erase_apply, Finsupp.erase_apply, Function.update_apply]

end update

end SkewMonoidAlgebra

