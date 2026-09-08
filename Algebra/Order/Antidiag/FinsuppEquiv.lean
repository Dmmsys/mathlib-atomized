/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

/-!

# Equivalence between `Finset.finsuppAntidiag` and `Sym`

This file collects further results about equivalence and cardinality related to
`Finset.finsuppAntidiag`. This file is separated from `Mathlib.Algebra.Order.Antidiag.Finsupp` to
reduce imports.

## Main declarations
* `Finset.finsuppAntidiagEquivSubtype`: `Finset.finsuppAntidiag s n` is equivalent to subtype of
  `s →₀ μ` whose sum is `n`.
* `Finset.finsuppAntidiagEquiv`: `Finset.finsuppAntidiag s n` is equivalent to `Sym s n` for
  natural number `n`.
* `Finset.card_finsuppAntidiag_nat_eq_choose` and `Finset.card_finsuppAntidiag_nat_eq_multichoose`:
  cardinality formula for `Finset.finsuppAntidiag s n` for natural number `n`.
-/

@[expose] public section

open Finsupp Function

variable {ι μ μ' : Type*}

namespace Finset
variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ}

set_option backward.isDefEq.respectTransparency false in
variable (s n) in
/-- The equivalence between `Finset.finsuppAntidiag s n` and the subtype of `s →₀ μ` whose sum is
`n`. -/
@[simps]
/-
**Finset.finsuppAntidiagEquivSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：finsuppAntidiagEquivSubtype : s.finsuppAntidiag n ≃ { P : s ->₀ μ // (P.su
m fun (_ : s) => id) = n } where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `Finset.finsuppAntidiag s n` and the subtype of `s →₀ μ`
 whose sum is
`n`.
-/
noncomputable def finsuppAntidiagEquivSubtype :
    s.finsuppAntidiag n ≃ { P : s →₀ μ // (P.sum fun (_ : s) ↦ id) = n } where
  toFun f := ⟨subtypeDomain (· ∈ s) f.val, by
    have hf := f.2
    rw [mem_finsuppAntidiag'] at hf
    simpa [sum, filter_mem_eq_inter, inter_eq_left.mpr hf.2] using hf.1⟩
  invFun f := ⟨extendDomain f.val, mem_finsuppAntidiag'.mpr
    ⟨by simpa [sum] using f.2, by simp [map_eq_image, image_subset_iff]⟩⟩
  left_inv f := by
    obtain ⟨hsum, hs⟩ := mem_finsuppAntidiag.mp f.prop
    ext1
    exact extendDomain_subtypeDomain _ hs
  right_inv f := by simp

variable (s) in
/-- The equivalence between `Finset.finsuppAntidiag s n` and `Sym s n`. -/
/-
**Finset.finsuppAntidiagEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：finsuppAntidiagEquiv (n : Nat) : s.finsuppAntidiag n ≃ Sym s n
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The equivalence between `Finset.finsuppAntidiag s n` and `Sym s n`.
-/
noncomputable def finsuppAntidiagEquiv (n : ℕ) : s.finsuppAntidiag n ≃ Sym s n :=
  (finsuppAntidiagEquivSubtype s n).trans (Sym.equivNatSum s n).symm

@[simp]
/-
**Finset.finsuppAntidiagEquiv_symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：finsuppAntidiagEquiv_symm_apply_apply (n : Nat) (f : Sym s n) (a : s) : ((
finsuppAntidiagEquiv s n).symm f).val a.val = f.toMultiset.count a
参数：n : Nat；f : Sym s n；a : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.finsuppAntidiagEquivSubtype_symm_apply_coe`：∀ {ι : Type u_1} {μ :
 Type u_2} [inst : DecidableEq ι] [inst_1 : AddCommMonoid μ] [inst_2 : Finset.Ha
sAntidiagonal μ]   [inst_3 : DecidableE…
· 使用定理 `Finsupp.extendDomain_apply`：∀ {α : Type u_1} {M : Type u_12} [inst : Zer
o M] {P : α → Prop} [inst_1 : DecidablePred P] (f : Subtype P →₀ M) (a : α),   f
.extendDomain a …
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsuppAntidiagEquiv_symm_apply_apply (n : ℕ) (f : Sym s n) (a : s) :
    ((finsuppAntidiagEquiv s n).symm f).val a.val = f.toMultiset.count a := by
  simp [finsuppAntidiagEquiv]

@[simp]
/-
**Finset.count_coe_finsuppAntidiagEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：count_coe_finsuppAntidiagEquiv_apply (n : Nat) (f : s.finsuppAntidiag n) (
a : s) : (finsuppAntidiagEquiv s n f).toMultiset.count a = f.val a
参数：n : Nat；f : s.finsuppAntidiag n；a : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `Finset.finsuppAntidiagEquivSubtype_apply_coe`：∀ {ι : Type u_1} {μ : Type
 u_2} [inst : DecidableEq ι] [inst_1 : AddCommMonoid μ] [inst_2 : Finset.HasAnti
diagonal μ]   [inst_3 : DecidableE…
· 使用定理 `Finsupp.count_toMultiset`：count_toMultiset [DecidableEq α] (f : α ->₀ Na
t) (a : α) : (toMultiset f).count a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_coe_finsuppAntidiagEquiv_apply (n : ℕ) (f : s.finsuppAntidiag n) (a : s) :
    (finsuppAntidiagEquiv s n f).toMultiset.count a = f.val a := by
  simp [finsuppAntidiagEquiv]
/-
**Finset.card_finsuppAntidiag_nat_eq_choose** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_finsuppAntidiag_nat_eq_choose (n : Nat) : #(s.finsuppAntidiag n) = (#
s + n - 1).choose n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eq_of_equiv_fintype`：Finset.card_eq_of_equiv_fintype {s : Fi
nset α} [Fintype β] (i : s ≃ β) : #s = Fintype.card β
· 使用定理 `Sym.card_sym_eq_choose`：card_sym_eq_choose {α : Type*} [Fintype α] (k : 
Nat) [Fintype (Sym α k)] : card (Sym α k) = (card α + k - 1).choose k
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_finsuppAntidiag_nat_eq_choose (n : ℕ) :
    #(s.finsuppAntidiag n) = (#s + n - 1).choose n := by
  simp [card_eq_of_equiv_fintype (finsuppAntidiagEquiv s n), Sym.card_sym_eq_choose]
/-
**Finset.card_finsuppAntidiag_nat_eq_multichoose** 是 Mathlib 中的一个定理，位于命名空间 `Fins
et`。
形式化陈述：card_finsuppAntidiag_nat_eq_multichoose (n : Nat) : #(s.finsuppAntidiag n)
 = (#s).multichoose n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eq_of_equiv_fintype`：Finset.card_eq_of_equiv_fintype {s : Fi
nset α} [Fintype β] (i : s ≃ β) : #s = Fintype.card β
· 使用定理 `Sym.card_sym_eq_multichoose`：card_sym_eq_multichoose (α : Type*) (k : Na
t) [Fintype α] [Fintype (Sym α k)] : card (Sym α k) = multichoose (card α) k
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_finsuppAntidiag_nat_eq_multichoose (n : ℕ) :
    #(s.finsuppAntidiag n) = (#s).multichoose n := by
  simp [card_eq_of_equiv_fintype (finsuppAntidiagEquiv s n), Sym.card_sym_eq_multichoose]

end Finset

