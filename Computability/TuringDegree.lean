/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
module

public import Mathlib.Computability.RecursiveIn
public import Mathlib.Order.Antisymmetrization

/-!
# Turing degrees

This file defines Turing reducibility and equivalence, proves that Turing equivalence is an
equivalence relation, and defines Turing degrees as the quotient under this relation.

## Main definitions

- `TuringReducible`: A relation defining Turing reducibility between partial functions.
- `TuringEquivalent`: An equivalence relation defining Turing equivalence between partial functions.
- `TuringDegree`: The type of Turing degrees, defined as the quotient of partial functions under
  `TuringEquivalent`.

## Notation

- `f ≤ᵀ g` : `f` is Turing reducible to `g`.
- `f ≡ᵀ g` : `f` is Turing equivalent to `g`.

## References

* [Odifreddi1989] Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers,
  Vol. I*. Springer-Verlag, 1989.

## Tags

Computability, Oracle, Turing Degrees, Reducibility, Equivalence Relation
-/

public section

open Primrec

variable {f g h : ℕ →. ℕ}

/--
`f` is Turing reducible to `g` if `f` is partial recursive given access to the oracle `g`
-/
/-
**TuringReducible** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：TuringReducible (f g : Nat ->. Nat) : Prop
参数：f g : Nat ->. Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is Turing reducible to `g` if `f` is partial recursive given access to the o
racle `g`
-/
abbrev TuringReducible (f g : ℕ →. ℕ) : Prop :=
  RecursiveIn {g} f

/--
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible to `f`.
-/
/-
**TuringEquivalent** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：TuringEquivalent (f g : Nat ->. Nat) : Prop
参数：f g : Nat ->. Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible 
to `f`.
-/
abbrev TuringEquivalent (f g : ℕ →. ℕ) : Prop :=
  AntisymmRel TuringReducible f g

@[inherit_doc] scoped[Computability] infix:50 " ≤ᵀ " => TuringReducible
@[inherit_doc] scoped[Computability] infix:50 " ≡ᵀ " => TuringEquivalent

open scoped Computability

/-- If a function is partial recursive, then it is recursive in every partial function. -/
/-
**Partrec.turingReducible** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Partrec.turingReducible (pF : Partrec f) : f <=ᵀ g
参数：pF : Partrec f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partrec.recursiveIn`：Partrec.recursiveIn [Primcodable α] [Primcodable σ]
 {f : α ->. σ} {O} (hf : Partrec f) : RecursiveIn O f

--- 原说明 ---
If a function is partial recursive, then it is recursive in every partial functi
on.
-/
lemma Partrec.turingReducible (pF : Partrec f) : f ≤ᵀ g :=
  pF.recursiveIn

/-- If a function is recursive in a constant partial function, then it is partial recursive. -/
/-
**TuringReducible.partrec_of_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TuringReducible.partrec_of_const {s} (hf : f <=ᵀ fun _ => s) : Partrec f
参数：hf : f <=ᵀ fun _ => s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RecursiveIn.partrec_of_const`：partrec_of_const {s} (hf : RecursiveIn {fu
n _ => s} f) : Partrec f

--- 原说明 ---
If a function is recursive in a constant partial function, then it is partial re
cursive.
-/
lemma TuringReducible.partrec_of_const {s} (hf : f ≤ᵀ fun _ => s) : Partrec f :=
  RecursiveIn.partrec_of_const hf

/-- A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`. -/
/-
**partrec_iff_forall_turingReducible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：partrec_iff_forall_turingReducible : Partrec f ↔ forall g, f <=ᵀ g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partrec.turingReducible`：Partrec.turingReducible (pF : Partrec f) : f <=
ᵀ g
· 使用引理 `TuringReducible.partrec_of_const`：TuringReducible.partrec_of_const {s} (
hf : f <=ᵀ fun _ => s) : Partrec f

--- 原说明 ---
A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`.
-/
theorem partrec_iff_forall_turingReducible : Partrec f ↔ ∀ g, f ≤ᵀ g :=
  ⟨fun hf _ => hf.turingReducible, fun hf => hf (fun _ => .none) |>.partrec_of_const⟩
/-
**TuringReducible.refl** 是 Mathlib 中的一个定理，位于命名空间 `TuringReducible`。
形式化陈述：∀ (f : ℕ →. ℕ), TuringReducible f f
参数：f : ℕ →. ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RecursiveIn.oracle`：oracle : forall g in O, RecursiveIn O g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem TuringReducible.refl (f : ℕ →. ℕ) : f ≤ᵀ f := .oracle _ <| by simp
/-
**TuringReducible.rfl** 是 Mathlib 中的一个定理，位于命名空间 `TuringReducible`。
形式化陈述：∀ {f : ℕ →. ℕ}, TuringReducible f f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TuringReducible.refl`：∀ (f : ℕ →. ℕ), TuringReducible f f
-/
protected theorem TuringReducible.rfl : f ≤ᵀ f := .refl _
/-
**TuringReducible.trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TuringReducible.trans (hg : f <=ᵀ g) (hh : g <=ᵀ h) : f <=ᵀ h
参数：hg : f <=ᵀ g；hh : g <=ᵀ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RecursiveIn.subst`：subst {O O'} {f : α ->. σ} (hf : RecursiveIn O f) (hO
 : forall g, g in O -> RecursiveIn O' g) : RecursiveIn O' f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem TuringReducible.trans (hg : f ≤ᵀ g) (hh : g ≤ᵀ h) : f ≤ᵀ h :=
  hg.subst (by simpa using hh)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl _ := .rfl
  trans := @TuringReducible.trans
/-
**TuringEquivalent.equivalence** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TuringEquivalent.equivalence : Equivalence TuringEquivalent
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.iseqv`：∀ {α : Sort u} [self : Setoid α], Equivalence ⇑self
· 使用定理 `instIsPreorderPFunNatTuringReducible`：IsPreorder (ℕ →. ℕ) TuringReducibl
e
-/
theorem TuringEquivalent.equivalence : Equivalence TuringEquivalent :=
  (AntisymmRel.setoid _ _).iseqv

@[refl]
/-
**TuringEquivalent.refl** 是 Mathlib 中的一个定理，位于命名空间 `TuringEquivalent`。
形式化陈述：∀ (f : ℕ →. ℕ), TuringEquivalent f f
参数：f : ℕ →. ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.refl`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ (
x : α), r x x
· 使用定理 `TuringEquivalent.equivalence`：TuringEquivalent.equivalence : Equivalence
 TuringEquivalent
-/
protected theorem TuringEquivalent.refl (f : ℕ →. ℕ) : f ≡ᵀ f :=
  Equivalence.refl equivalence f

@[symm]
/-
**TuringEquivalent.symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TuringEquivalent.symm {f g : Nat ->. Nat} (h : f ≡ᵀ g) : g ≡ᵀ f
参数：h : f ≡ᵀ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.symm`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ {
x y : α}, r x y → r y x
· 使用定理 `TuringEquivalent.equivalence`：TuringEquivalent.equivalence : Equivalence
 TuringEquivalent
-/
theorem TuringEquivalent.symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  Equivalence.symm equivalence h

@[trans]
/-
**TuringEquivalent.trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TuringEquivalent.trans (f g h : Nat ->. Nat) (h₁ : f ≡ᵀ g) (h₂ : g ≡ᵀ h) :
 f ≡ᵀ h
参数：f g h : Nat ->. Nat；h₁ : f ≡ᵀ g；h₂ : g ≡ᵀ h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.trans`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ 
{x y z : α}, r x y → r y z → r x z
· 使用定理 `TuringEquivalent.equivalence`：TuringEquivalent.equivalence : Equivalence
 TuringEquivalent
-/
theorem TuringEquivalent.trans (f g h : ℕ →. ℕ) (h₁ : f ≡ᵀ g) (h₂ : g ≡ᵀ h) : f ≡ᵀ h :=
  Equivalence.trans equivalence h₁ h₂

/--
Turing degrees are the equivalence classes of partial functions under Turing equivalence.
-/
/-
**TuringDegree** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：TuringDegree
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPreorderPFunNatTuringReducible`：IsPreorder (ℕ →. ℕ) TuringReducibl
e

--- 原说明 ---
Turing degrees are the equivalence classes of partial functions under Turing equ
ivalence.
-/
abbrev TuringDegree :=
  Antisymmetrization _ TuringReducible

set_option backward.privateInPublic true in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private instance : Preorder (ℕ →. ℕ) where
  le := TuringReducible
  le_refl := .refl
  le_trans _ _ _ := TuringReducible.trans
/-
**TuringDegree.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：TuringDegree.instPartialOrder : PartialOrder TuringDegree
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance TuringDegree.instPartialOrder : PartialOrder TuringDegree :=
  instPartialOrderAntisymmetrization
