/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Seq.Basic

/-!
# Basic Translation Lemmas Between Functions Defined for Continued Fractions

## Summary

Some simple translation lemmas between the different definitions of functions defined in
`Algebra.ContinuedFractions.Basic`.
-/

public section


namespace GenContFract

section General

/-!
### Translations Between General Access Functions

Here we give some basic translations that hold by definition between the various methods that allow
us to access the numerators and denominators of a continued fraction.
-/


variable {α : Type*} {g : GenContFract α} {n : ℕ}

/-
**GenContFract.terminatedAt_iff_s_terminatedAt** 是 Mathlib 中的一个定理，位于命名空间 `GenCon
tFract`。
形式化陈述：terminatedAt_iff_s_terminatedAt : g.TerminatedAt n ↔ g.s.TerminatedAt n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem terminatedAt_iff_s_terminatedAt : g.TerminatedAt n ↔ g.s.TerminatedAt n := by rfl
/-
**GenContFract.terminatedAt_iff_s_none** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：terminatedAt_iff_s_none : g.TerminatedAt n ↔ g.s.get? n = none
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem terminatedAt_iff_s_none : g.TerminatedAt n ↔ g.s.get? n = none := by rfl
/-
**GenContFract.partNum_none_iff_s_none** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：partNum_none_iff_s_none : g.partNums.get? n = none ↔ g.s.get? n = none
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
· 使用定理 `Stream'.Seq.map_get?`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Strea
m'.Seq α) (n : ℕ),   (Stream'.Seq.map f s).get? n = Option.map f (s.get? n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem partNum_none_iff_s_none : g.partNums.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.get? n <;> simp [partNums, s_nth_eq]
/-
**GenContFract.terminatedAt_iff_partNum_none** 是 Mathlib 中的一个定理，位于命名空间 `GenContF
ract`。
形式化陈述：terminatedAt_iff_partNum_none : g.TerminatedAt n ↔ g.partNums.get? n = non
e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.terminatedAt_iff_s_none`：terminatedAt_iff_s_none : g.Termin
atedAt n ↔ g.s.get? n = none
· 使用定理 `GenContFract.partNum_none_iff_s_none`：partNum_none_iff_s_none : g.partNu
ms.get? n = none ↔ g.s.get? n = none
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem terminatedAt_iff_partNum_none : g.TerminatedAt n ↔ g.partNums.get? n = none := by
  rw [terminatedAt_iff_s_none, partNum_none_iff_s_none]
/-
**GenContFract.partDen_none_iff_s_none** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：partDen_none_iff_s_none : g.partDens.get? n = none ↔ g.s.get? n = none
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
· 使用定理 `Stream'.Seq.map_get?`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Strea
m'.Seq α) (n : ℕ),   (Stream'.Seq.map f s).get? n = Option.map f (s.get? n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem partDen_none_iff_s_none : g.partDens.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.get? n <;> simp [partDens, s_nth_eq]
/-
**GenContFract.terminatedAt_iff_partDen_none** 是 Mathlib 中的一个定理，位于命名空间 `GenContF
ract`。
形式化陈述：terminatedAt_iff_partDen_none : g.TerminatedAt n ↔ g.partDens.get? n = non
e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.terminatedAt_iff_s_none`：terminatedAt_iff_s_none : g.Termin
atedAt n ↔ g.s.get? n = none
· 使用定理 `GenContFract.partDen_none_iff_s_none`：partDen_none_iff_s_none : g.partDe
ns.get? n = none ↔ g.s.get? n = none
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem terminatedAt_iff_partDen_none : g.TerminatedAt n ↔ g.partDens.get? n = none := by
  rw [terminatedAt_iff_s_none, partDen_none_iff_s_none]
/-
**GenContFract.partNum_eq_s_a** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：partNum_eq_s_a {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) : g.partNum
s.get? n = some gp.a
参数：s_nth_eq : g.s.get? n = some gp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.Seq.map_get?`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Strea
m'.Seq α) (n : ℕ),   (Stream'.Seq.map f s).get? n = Option.map f (s.get? n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem partNum_eq_s_a {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) :
    g.partNums.get? n = some gp.a := by simp [partNums, s_nth_eq]
/-
**GenContFract.partDen_eq_s_b** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：partDen_eq_s_b {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) : g.partDen
s.get? n = some gp.b
参数：s_nth_eq : g.s.get? n = some gp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.Seq.map_get?`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Strea
m'.Seq α) (n : ℕ),   (Stream'.Seq.map f s).get? n = Option.map f (s.get? n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem partDen_eq_s_b {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) :
    g.partDens.get? n = some gp.b := by simp [partDens, s_nth_eq]
/-
**GenContFract.exists_s_a_of_partNum** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：exists_s_a_of_partNum {a : α} (nth_partNum_eq : g.partNums.get? n = some a
) : exists gp, g.s.get? n = some gp ∧ gp.a = a
参数：nth_partNum_eq : g.partNums.get? n = some a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.Seq.map_get?`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Strea
m'.Seq α) (n : ℕ),   (Stream'.Seq.map f s).get? n = Option.map f (s.get? n)
-/
theorem exists_s_a_of_partNum {a : α} (nth_partNum_eq : g.partNums.get? n = some a) :
    ∃ gp, g.s.get? n = some gp ∧ gp.a = a := by
  simpa [partNums, Stream'.Seq.map_get?] using nth_partNum_eq
/-
**GenContFract.exists_s_b_of_partDen** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：exists_s_b_of_partDen {b : α} (nth_partDen_eq : g.partDens.get? n = some b
) : exists gp, g.s.get? n = some gp ∧ gp.b = b
参数：nth_partDen_eq : g.partDens.get? n = some b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.Seq.map_get?`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Strea
m'.Seq α) (n : ℕ),   (Stream'.Seq.map f s).get? n = Option.map f (s.get? n)
-/
theorem exists_s_b_of_partDen {b : α}
    (nth_partDen_eq : g.partDens.get? n = some b) :
    ∃ gp, g.s.get? n = some gp ∧ gp.b = b := by
  simpa [partDens, Stream'.Seq.map_get?] using nth_partDen_eq

end General

section WithDivisionRing

/-!
### Translations Between Computational Functions

Here we give some basic translations that hold by definition for the computational methods of a
continued fraction.
-/


variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

/-
**GenContFract.nth_cont_eq_succ_nth_contAux** 是 Mathlib 中的一个定理，位于命名空间 `GenContFr
act`。
形式化陈述：nth_cont_eq_succ_nth_contAux : g.conts n = g.contsAux (n + 1)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nth_cont_eq_succ_nth_contAux : g.conts n = g.contsAux (n + 1) :=
  rfl
/-
**GenContFract.num_eq_conts_a** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：num_eq_conts_a : g.nums n = (g.conts n).a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem num_eq_conts_a : g.nums n = (g.conts n).a :=
  rfl
/-
**GenContFract.den_eq_conts_b** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：den_eq_conts_b : g.dens n = (g.conts n).b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem den_eq_conts_b : g.dens n = (g.conts n).b :=
  rfl
/-
**GenContFract.conv_eq_num_div_den** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：conv_eq_num_div_den : g.convs n = g.nums n / g.dens n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conv_eq_num_div_den : g.convs n = g.nums n / g.dens n :=
  rfl
/-
**GenContFract.conv_eq_conts_a_div_conts_b** 是 Mathlib 中的一个定理，位于命名空间 `GenContFra
ct`。
形式化陈述：conv_eq_conts_a_div_conts_b : g.convs n = (g.conts n).a / (g.conts n).b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conv_eq_conts_a_div_conts_b :
    g.convs n = (g.conts n).a / (g.conts n).b :=
  rfl
/-
**GenContFract.exists_conts_a_of_num** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：exists_conts_a_of_num {A : K} (nth_num_eq : g.nums n = A) : exists conts, 
g.conts n = conts ∧ conts.a = A
参数：nth_num_eq : g.nums n = A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem exists_conts_a_of_num {A : K} (nth_num_eq : g.nums n = A) :
    ∃ conts, g.conts n = conts ∧ conts.a = A := by simpa
/-
**GenContFract.exists_conts_b_of_den** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：exists_conts_b_of_den {B : K} (nth_denom_eq : g.dens n = B) : exists conts
, g.conts n = conts ∧ conts.b = B
参数：nth_denom_eq : g.dens n = B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem exists_conts_b_of_den {B : K} (nth_denom_eq : g.dens n = B) :
    ∃ conts, g.conts n = conts ∧ conts.b = B := by simpa

@[simp]
/-
**GenContFract.zeroth_contAux_eq_one_zero** 是 Mathlib 中的一个定理，位于命名空间 `GenContFrac
t`。
形式化陈述：zeroth_contAux_eq_one_zero : g.contsAux 0 = ⟨1, 0⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zeroth_contAux_eq_one_zero : g.contsAux 0 = ⟨1, 0⟩ :=
  rfl

@[simp]
/-
**GenContFract.first_contAux_eq_h_one** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：first_contAux_eq_h_one : g.contsAux 1 = ⟨g.h, 1⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem first_contAux_eq_h_one : g.contsAux 1 = ⟨g.h, 1⟩ :=
  rfl

@[simp]
/-
**GenContFract.zeroth_cont_eq_h_one** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：zeroth_cont_eq_h_one : g.conts 0 = ⟨g.h, 1⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zeroth_cont_eq_h_one : g.conts 0 = ⟨g.h, 1⟩ :=
  rfl

@[simp]
/-
**GenContFract.zeroth_num_eq_h** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：zeroth_num_eq_h : g.nums 0 = g.h
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zeroth_num_eq_h : g.nums 0 = g.h :=
  rfl

@[simp]
/-
**GenContFract.zeroth_den_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：zeroth_den_eq_one : g.dens 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zeroth_den_eq_one : g.dens 0 = 1 :=
  rfl

@[simp]
/-
**GenContFract.zeroth_conv_eq_h** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：zeroth_conv_eq_h : g.convs 0 = g.h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zeroth_conv_eq_h : g.convs 0 = g.h := by
  simp [conv_eq_num_div_den, num_eq_conts_a, den_eq_conts_b, div_one]
/-
**GenContFract.second_contAux_eq** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：second_contAux_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) : g.c
ontsAux 2 = ⟨gp.b * g.h + gp.a, gp.b⟩
参数：zeroth_s_eq : g.s.get? 0 = some gp。
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem second_contAux_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.contsAux 2 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  simp [zeroth_s_eq, contsAux, nextConts, nextDen, nextNum]
/-
**GenContFract.first_cont_eq** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：first_cont_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) : g.conts
 1 = ⟨gp.b * g.h + gp.a, gp.b⟩
参数：zeroth_s_eq : g.s.get? 0 = some gp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.second_contAux_eq`：second_contAux_eq {gp : Pair K} (zeroth_
s_eq : g.s.get? 0 = some gp) : g.contsAux 2 = ⟨gp.b * g.h + gp.a, gp.b⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem first_cont_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.conts 1 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  simp [nth_cont_eq_succ_nth_contAux, second_contAux_eq zeroth_s_eq]
/-
**GenContFract.first_num_eq** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：first_num_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) : g.nums 1
 = gp.b * g.h + gp.a
参数：zeroth_s_eq : g.s.get? 0 = some gp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.first_cont_eq`：first_cont_eq {gp : Pair K} (zeroth_s_eq : g
.s.get? 0 = some gp) : g.conts 1 = ⟨gp.b * g.h + gp.a, gp.b⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem first_num_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.nums 1 = gp.b * g.h + gp.a := by simp [num_eq_conts_a, first_cont_eq zeroth_s_eq]
/-
**GenContFract.first_den_eq** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：first_den_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) : g.dens 1
 = gp.b
参数：zeroth_s_eq : g.s.get? 0 = some gp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.first_cont_eq`：first_cont_eq {gp : Pair K} (zeroth_s_eq : g
.s.get? 0 = some gp) : g.conts 1 = ⟨gp.b * g.h + gp.a, gp.b⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem first_den_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.dens 1 = gp.b := by simp [den_eq_conts_b, first_cont_eq zeroth_s_eq]

@[simp]
/-
**GenContFract.zeroth_conv'Aux_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：∀ {K : Type u_1} [inst : DivisionRing K] {s : Stream'.Seq (GenContFract.Pa
ir K)}, GenContFract.convs'Aux s 0 = 0
参数：GenContFract.Pair K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zeroth_conv'Aux_eq_zero {s : Stream'.Seq <| Pair K} :
    convs'Aux s 0 = (0 : K) :=
  rfl

@[simp]
/-
**GenContFract.zeroth_conv'_eq_h** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：∀ {K : Type u_1} {g : GenContFract K} [inst : DivisionRing K], g.convs' 0 
= g.h
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zeroth_conv'_eq_h : g.convs' 0 = g.h := by simp [convs']
/-
**GenContFract.convs'Aux_succ_none** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：∀ {K : Type u_1} [inst : DivisionRing K] {s : Stream'.Seq (GenContFract.Pa
ir K)},   s.head = none → ∀ (n : ℕ), GenContFract.convs'Aux s (n + 1) = 0
参数：GenContFract.Pair K；n : ℕ；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convs'Aux_succ_none {s : Stream'.Seq (Pair K)} (h : s.head = none) (n : ℕ) :
    convs'Aux s (n + 1) = 0 := by simp [convs'Aux, h]
/-
**GenContFract.convs'Aux_succ_some** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：∀ {K : Type u_1} [inst : DivisionRing K] {s : Stream'.Seq (GenContFract.Pa
ir K)} {p : GenContFract.Pair K},   s.head = some p → ∀ (n : ℕ), GenContFract.co
nvs'Aux s (n + 1) = p.a / (p.b + GenContFract.convs'Aux s.tail n)
参数：GenContFract.Pair K；n : ℕ；n + 1；p.b + GenContFract.convs'Aux s.tail n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convs'Aux_succ_some {s : Stream'.Seq (Pair K)} {p : Pair K} (h : s.head = some p)
    (n : ℕ) : convs'Aux s (n + 1) = p.a / (p.b + convs'Aux s.tail n) := by
  simp [convs'Aux, h]

end WithDivisionRing

end GenContFract

