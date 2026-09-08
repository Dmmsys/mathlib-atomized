/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
module

public import Mathlib.Computability.Partrec

/-!
# Oracle computability

This file defines oracle computability using partial recursive functions.

## Main definitions

* `Nat.RecursiveIn O f`: A partial function `f : ℕ →. ℕ` is partial recursive given access to
  oracles in the set `O`.
* `RecursiveIn O f`: Lifts `Nat.RecursiveIn` to partial functions between `Primcodable` types.
* `ComputableIn O f`: A total function `f : α → σ` is computable given access to oracles in `O`.

## Main results

* `Nat.Partrec.recursiveIn`: Every partial recursive function is recursive in any oracle set.
* `partrec_iff_forall_recursiveIn_singleton`: A function is partial recursive iff it is recursive
  in every singleton oracle set.
* `recursiveIn_empty_iff`: Being recursive in the empty set is equivalent to being
  partial recursive.
* `RecursiveIn.mono`: Monotonicity of `RecursiveIn` with respect to oracle sets.

## Implementation notes

The type of partial functions recursive in a set of oracles `O` is the smallest type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.

## References

* [Piergiorgio Odifreddi,
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural
  Numbers*][odifreddi1989]

## Tags

Computability, Oracle, Turing Degrees, Reducibility, Equivalence Relation
-/

@[expose] public section

open Encodable Primrec Nat.Partrec Part

variable {α β γ σ : Type*}

namespace Nat

/--
The type of partial functions recursive in a set of oracles `O` is the smallest type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.
-/
/-
**Nat.RecursiveIn** 是 Mathlib 中的一个归纳类型，位于命名空间 `Nat`。
形式化陈述：Set (ℕ →. ℕ) → (ℕ →. ℕ) → Prop
参数：ℕ →. ℕ；ℕ →. ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of partial functions recursive in a set of oracles `O` is the smallest 
type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O
`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.
-/
protected inductive RecursiveIn (O : Set (ℕ →. ℕ)) : (ℕ →. ℕ) → Prop
  | zero : Nat.RecursiveIn O fun _ => 0
  | succ : Nat.RecursiveIn O Nat.succ
  | left : Nat.RecursiveIn O fun n => (Nat.unpair n).1
  | right : Nat.RecursiveIn O fun n => (Nat.unpair n).2
  | oracle : ∀ g ∈ O, Nat.RecursiveIn O g
  | pair {f h : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) :
      Nat.RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
  | comp {f h : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) :
      Nat.RecursiveIn O fun n => h n >>= f
  | prec {f h : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) :
      Nat.RecursiveIn O fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) fun y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
  | rfind {f : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) :
      Nat.RecursiveIn O fun a =>
        Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)

end Nat

/-- A partial function `f : α →. σ` between `Primcodable` types is recursive in a set of oracles
`O` if its encoding as a function `ℕ →. ℕ` is `Nat.RecursiveIn O`. -/
/-
**RecursiveIn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RecursiveIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (Nat ->. Nat)) 
(f : α ->. σ) : Prop
参数：O : Set (Nat ->. Nat)；f : α ->. σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partial function `f : α →. σ` between `Primcodable` types is recursive in a se
t of oracles
`O` if its encoding as a function `ℕ →. ℕ` is `Nat.RecursiveIn O`.
-/
def RecursiveIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α →. σ) : Prop :=
  Nat.RecursiveIn O fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode
/-
**RecursiveIn.iff_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RecursiveIn.iff_nat {f : Nat ->. Nat} {O} : RecursiveIn O f ↔ Nat.Recursiv
eIn O f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.map_id'`：map_id' {f : α -> α} (H : forall x : α, f x = x) (o) : map
 f o = o
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma RecursiveIn.iff_nat {f : ℕ →. ℕ} {O} : RecursiveIn O f ↔ Nat.RecursiveIn O f := by
  simp [RecursiveIn, Part.map_id']

/-- A binary partial function is recursive in `O` if the curried form is. -/
/-
**RecursiveIn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RecursiveIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (Nat ->. Nat)) 
(f : α ->. σ) : Prop
参数：O : Set (Nat ->. Nat)；f : α ->. σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary partial function is recursive in `O` if the curried form is.
-/
def RecursiveIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β →. σ) : Prop :=
  RecursiveIn O (fun p : α × β => f p.1 p.2)

/-- A total function is computable in `O` if its constant lift is recursive in `O`. -/
/-
**ComputableIn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ComputableIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (Nat ->. Nat))
 (f : α -> σ) : Prop
参数：O : Set (Nat ->. Nat)；f : α -> σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A total function is computable in `O` if its constant lift is recursive in `O`.
-/
def ComputableIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α → σ) : Prop :=
  RecursiveIn O (fun a => Part.some (f a))

/-- A binary total function is computable in `O`. -/
/-
**ComputableIn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ComputableIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (Nat ->. Nat))
 (f : α -> σ) : Prop
参数：O : Set (Nat ->. Nat)；f : α -> σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary total function is computable in `O`.
-/
def ComputableIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β → σ) : Prop :=
  ComputableIn O (fun p : α × β => f p.1 p.2)

namespace Nat.RecursiveIn

variable {f g : ℕ →. ℕ}

/-
**Nat.RecursiveIn.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat.RecursiveIn`。
形式化陈述：of_eq {O} (hf : Nat.RecursiveIn O f) (H : forall n, f n = g n) : Nat.Recur
siveIn O g
参数：hf : Nat.RecursiveIn O f；H : forall n, f n = g n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem of_eq {O} (hf : Nat.RecursiveIn O f) (H : ∀ n, f n = g n) :
    Nat.RecursiveIn O g :=
  (funext H : f = g) ▸ hf
/-
**Nat.RecursiveIn.of_eq_tot** 是 Mathlib 中的一个定理，位于命名空间 `Nat.RecursiveIn`。
形式化陈述：of_eq_tot {g : Nat -> Nat} {O} (hf : Nat.RecursiveIn O f) (H : forall n, g
 n in f n) : Nat.RecursiveIn O g
参数：hf : Nat.RecursiveIn O f；H : forall n, g n in f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.RecursiveIn.of_eq`：of_eq {O} (hf : Nat.RecursiveIn O f) (H : forall 
n, f n = g n) : Nat.RecursiveIn O g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_some_iff`：eq_some_iff {a : α} {o : Part α} : o = some a ↔ a in o
-/
theorem of_eq_tot {g : ℕ → ℕ} {O} (hf : Nat.RecursiveIn O f)
    (H : ∀ n, g n ∈ f n) : Nat.RecursiveIn O g :=
  of_eq hf fun n => eq_some_iff.2 (H n)

/-- If every element of `O` is `Nat.RecursiveIn O'`, then any function which is
`Nat.RecursiveIn O` is also `Nat.RecursiveIn O'`. -/
/-
**Nat.RecursiveIn.subst** 是 Mathlib 中的一个定理，位于命名空间 `Nat.RecursiveIn`。
形式化陈述：subst {O O'} {f : Nat ->. Nat} (hf : Nat.RecursiveIn O f) (hO : forall g, 
g in O -> Nat.RecursiveIn O' g) : Nat.RecursiveIn O' f
参数：hf : Nat.RecursiveIn O f；hO : forall g, g in O -> Nat.RecursiveIn O' g。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If every element of `O` is `Nat.RecursiveIn O'`, then any function which is
`Nat.RecursiveIn O` is also `Nat.RecursiveIn O'`.
-/
theorem subst {O O'} {f : ℕ →. ℕ} (hf : Nat.RecursiveIn O f)
    (hO : ∀ g, g ∈ O → Nat.RecursiveIn O' g) : Nat.RecursiveIn O' f := by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g hg => exact hO g hg
  | pair _ _ ihf ihg => exact .pair ihf ihg
  | comp _ _ ihf ihg => exact .comp ihf ihg
  | prec _ _ ihf ihg => exact .prec ihf ihg
  | rfind _ ihf => exact .rfind ihf

/-- If every function in `O` is partial recursive,
then a function which is `Nat.RecursiveIn O` is also partial recursive. -/
/-
**Nat.RecursiveIn.partrec_of_oracle** 是 Mathlib 中的一个定理，位于命名空间 `Nat.RecursiveIn`。
形式化陈述：partrec_of_oracle {f : Nat ->. Nat} {O} (hO : forall g in O, Nat.Partrec g
) (hf : Nat.RecursiveIn O f) : Nat.Partrec f
参数：hO : forall g in O, Nat.Partrec g；hf : Nat.RecursiveIn O f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If every function in `O` is partial recursive,
then a function which is `Nat.RecursiveIn O` is also partial recursive.
-/
theorem partrec_of_oracle {f : ℕ →. ℕ} {O}
    (hO : ∀ g ∈ O, Nat.Partrec g) (hf : Nat.RecursiveIn O f) : Nat.Partrec f := by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g gIn => exact hO g gIn
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

end Nat.RecursiveIn

/-- If a function is partial recursive, then it is recursive in every partial function. -/
/-
**Nat.Partrec.recursiveIn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.Partrec.recursiveIn {f : Nat ->. Nat} {O} (pF : Nat.Partrec f) : Nat.R
ecursiveIn O f
参数：pF : Nat.Partrec f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function is partial recursive, then it is recursive in every partial functi
on.
-/
lemma Nat.Partrec.recursiveIn {f : ℕ →. ℕ} {O} (pF : Nat.Partrec f) :
    Nat.RecursiveIn O f := by
  induction pF with
  | zero | succ | left | right => constructor
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

/-- If a partial function is partial recursive, then it is `RecursiveIn` any oracle set. -/
/-
**Partrec.recursiveIn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Partrec.recursiveIn [Primcodable α] [Primcodable σ] {f : α ->. σ} {O} (hf 
: Partrec f) : RecursiveIn O f
参数：hf : Partrec f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.Partrec.recursiveIn`：Nat.Partrec.recursiveIn {f : Nat ->. Nat} {O} (
pF : Nat.Partrec f) : Nat.RecursiveIn O f

--- 原说明 ---
If a partial function is partial recursive, then it is `RecursiveIn` any oracle 
set.
-/
lemma Partrec.recursiveIn [Primcodable α] [Primcodable σ] {f : α →. σ} {O}
    (hf : Partrec f) : RecursiveIn O f :=
  Nat.Partrec.recursiveIn hf
/-
**Nat.Primrec.recursiveIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.Primrec.recursiveIn {O} {f : Nat -> Nat} (hf : Nat.Primrec f) : Nat.Re
cursiveIn O (fun n => f n)
参数：hf : Nat.Primrec f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.Partrec.recursiveIn`：Nat.Partrec.recursiveIn {f : Nat ->. Nat} {O} (
pF : Nat.Partrec f) : Nat.RecursiveIn O f
· 使用定理 `Nat.Partrec.of_primrec`：of_primrec {f : Nat -> Nat} (hf : Nat.Primrec f)
 : Nat.Partrec f
-/
theorem Nat.Primrec.recursiveIn {O} {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    Nat.RecursiveIn O (fun n => f n) :=
  Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec hf)
/-
**Computable.computableIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Computable.computableIn [Primcodable α] [Primcodable β] {f : α -> β} {O} (
hf : Computable f) : ComputableIn O f
参数：hf : Computable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partrec.recursiveIn`：Partrec.recursiveIn [Primcodable α] [Primcodable σ]
 {f : α ->. σ} {O} (hf : Partrec f) : RecursiveIn O f
· 使用定理 `Computable.partrec`：∀ {α : Type u_1} {σ : Type u_2} [inst : Primcodable 
α] [inst_1 : Primcodable σ] {f : α → σ}, Computable f → Partrec ↑f
-/
theorem Computable.computableIn [Primcodable α] [Primcodable β] {f : α → β} {O}
    (hf : Computable f) : ComputableIn O f :=
  hf.partrec.recursiveIn
/-
**Primrec.computableIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Primrec.computableIn [Primcodable α] [Primcodable σ] {f : α -> σ} {O} (hf 
: Primrec f) : ComputableIn O f
参数：hf : Primrec f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.computableIn`：Computable.computableIn [Primcodable α] [Primco
dable β] {f : α -> β} {O} (hf : Computable f) : ComputableIn O f
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
-/
theorem Primrec.computableIn [Primcodable α] [Primcodable σ]
    {f : α → σ} {O} (hf : Primrec f) : ComputableIn O f :=
  (Primrec.to_comp hf).computableIn

nonrec theorem Primrec₂.computableIn₂ [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} {O} (hf : Primrec₂ f) : ComputableIn₂ O f :=
  hf.computableIn
/-
**ComputableIn.recursiveIn** 是 Mathlib 中的一个定理，位于命名空间 `ComputableIn`。
形式化陈述：∀ {α : Type u_1} {σ : Type u_4} [inst : Primcodable α] [inst_1 : Primcodab
le σ] {f : α → σ} {O : Set (ℕ →. ℕ)},   ComputableIn O f → RecursiveIn O fun a =
> Part.some (f a)
参数：ℕ →. ℕ；f a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem ComputableIn.recursiveIn [Primcodable α] [Primcodable σ]
    {f : α → σ} {O} (hf : ComputableIn O f) :
    RecursiveIn O (fun a => Part.some (f a)) := hf
/-
**ComputableIn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ComputableIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (Nat ->. Nat))
 (f : α -> σ) : Prop
参数：O : Set (Nat ->. Nat)；f : α -> σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem ComputableIn₂.recursiveIn₂ [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} {O} (hf : ComputableIn₂ O f) :
    RecursiveIn₂ O fun a => (f a : β →. σ) := hf

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]
variable {f : α →. σ} {O : Set (ℕ →. ℕ)}

namespace RecursiveIn

/-
**RecursiveIn.of_eq** 是 Mathlib 中的一个引理，位于命名空间 `RecursiveIn`。
形式化陈述：of_eq {f g : α ->. σ} (hf : RecursiveIn O f) (H : forall x, f x = g x) : R
ecursiveIn O g
参数：hf : RecursiveIn O f；H : forall x, f x = g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma of_eq {f g : α →. σ} (hf : RecursiveIn O f)
    (H : ∀ x, f x = g x) : RecursiveIn O g :=
  (funext H : f = g) ▸ hf
/-
**RecursiveIn.of_eq_tot** 是 Mathlib 中的一个引理，位于命名空间 `RecursiveIn`。
形式化陈述：of_eq_tot {f : α ->. σ} {g : α -> σ} (hf : RecursiveIn O f) (H : forall n,
 g n in f n) : RecursiveIn O (g : α ->. σ)
参数：hf : RecursiveIn O f；H : forall n, g n in f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RecursiveIn.of_eq`：of_eq {f g : α ->. σ} (hf : RecursiveIn O f) (H : for
all x, f x = g x) : RecursiveIn O g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_some_iff`：eq_some_iff {a : α} {o : Part α} : o = some a ↔ a in o
-/
lemma of_eq_tot {f : α →. σ} {g : α → σ}
    (hf : RecursiveIn O f) (H : ∀ n, g n ∈ f n) : RecursiveIn O (g : α →. σ) :=
  of_eq hf fun n => eq_some_iff.2 (H n)
/-
**RecursiveIn.oracle** 是 Mathlib 中的一个引理，位于命名空间 `RecursiveIn`。
形式化陈述：oracle : forall g in O, RecursiveIn O g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RecursiveIn.iff_nat`：RecursiveIn.iff_nat {f : Nat ->. Nat} {O} : Recursi
veIn O f ↔ Nat.RecursiveIn O f
-/
lemma oracle : ∀ g ∈ O, RecursiveIn O g := by
  intro g hg; rw [iff_nat]; exact .oracle g hg
/-
**RecursiveIn.some** 是 Mathlib 中的一个定理，位于命名空间 `RecursiveIn`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α] {O : Set (ℕ →. ℕ)}, RecursiveIn O 
Part.some
参数：ℕ →. ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partrec.recursiveIn`：Partrec.recursiveIn [Primcodable α] [Primcodable σ]
 {f : α ->. σ} {O} (hf : Partrec f) : RecursiveIn O f
· 使用定理 `Partrec.some`：∀ {α : Type u_1} [inst : Primcodable α], Partrec Part.some
-/
protected theorem some : RecursiveIn O (Part.some : α →. α) :=
  Partrec.some.recursiveIn
/-
**RecursiveIn.none** 是 Mathlib 中的一个定理，位于命名空间 `RecursiveIn`。
形式化陈述：∀ {α : Type u_1} {σ : Type u_4} [inst : Primcodable α] [inst_1 : Primcodab
le σ] {O : Set (ℕ →. ℕ)},   RecursiveIn O fun x => Part.none
参数：ℕ →. ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partrec.recursiveIn`：Partrec.recursiveIn [Primcodable α] [Primcodable σ]
 {f : α ->. σ} {O} (hf : Partrec f) : RecursiveIn O f
· 使用定理 `Partrec.none`：none : Partrec fun _ : α => @Part.none σ
-/
protected theorem none : RecursiveIn O (fun _ : α => (Part.none : Part σ)) :=
  Partrec.none.recursiveIn

/-- If every element of `O` is `RecursiveIn O'`, then any function which is
`RecursiveIn O` is also `RecursiveIn O'`. -/
/-
**RecursiveIn.subst** 是 Mathlib 中的一个定理，位于命名空间 `RecursiveIn`。
形式化陈述：subst {O O'} {f : α ->. σ} (hf : RecursiveIn O f) (hO : forall g, g in O -
> RecursiveIn O' g) : RecursiveIn O' f
参数：hf : RecursiveIn O f；hO : forall g, g in O -> RecursiveIn O' g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.RecursiveIn.subst`：subst {O O'} {f : Nat ->. Nat} (hf : Nat.Recursiv
eIn O f) (hO : forall g, g in O -> Nat.RecursiveIn O' g) : Nat.RecursiveIn O' f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
If every element of `O` is `RecursiveIn O'`, then any function which is
`RecursiveIn O` is also `RecursiveIn O'`.
-/
theorem subst {O O'} {f : α →. σ} (hf : RecursiveIn O f)
    (hO : ∀ g, g ∈ O → RecursiveIn O' g) : RecursiveIn O' f :=
  Nat.RecursiveIn.subst hf (by simpa only [RecursiveIn.iff_nat] using hO)

/-- Monotonicity of `RecursiveIn` with respect to oracle sets. -/
@[gcongr]
/-
**RecursiveIn.mono** 是 Mathlib 中的一个定理，位于命名空间 `RecursiveIn`。
形式化陈述：mono {O₁ O₂} (hsub : O₁ subseteq O₂) (hf : RecursiveIn O₁ f) : RecursiveIn
 O₂ f
参数：hsub : O₁ subseteq O₂；hf : RecursiveIn O₁ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RecursiveIn.subst`：subst {O O'} {f : α ->. σ} (hf : RecursiveIn O f) (hO
 : forall g, g in O -> RecursiveIn O' g) : RecursiveIn O' f
· 使用引理 `RecursiveIn.oracle`：oracle : forall g in O, RecursiveIn O g

--- 原说明 ---
Monotonicity of `RecursiveIn` with respect to oracle sets.
-/
theorem mono {O₁ O₂} (hsub : O₁ ⊆ O₂) (hf : RecursiveIn O₁ f) : RecursiveIn O₂ f :=
  hf.subst (fun g hg => .oracle g (hsub hg))

/-- If every function in `O` is partial recursive,
then a function which is `RecursiveIn O` is also partial recursive. -/
/-
**RecursiveIn.partrec_of_oracle** 是 Mathlib 中的一个定理，位于命名空间 `RecursiveIn`。
形式化陈述：partrec_of_oracle (hO : forall g in O, Partrec g) (hf : RecursiveIn O f) :
 Partrec f
参数：hO : forall g in O, Partrec g；hf : RecursiveIn O f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.RecursiveIn.partrec_of_oracle`：partrec_of_oracle {f : Nat ->. Nat} {
O} (hO : forall g in O, Nat.Partrec g) (hf : Nat.RecursiveIn O f) : Nat.Partrec 
f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
If every function in `O` is partial recursive,
then a function which is `RecursiveIn O` is also partial recursive.
-/
theorem partrec_of_oracle
    (hO : ∀ g ∈ O, Partrec g) (hf : RecursiveIn O f) : Partrec f :=
  Nat.RecursiveIn.partrec_of_oracle (by simpa only [Partrec.nat_iff] using hO) hf

/-- If a function is recursive in a constant partial function, then it is partial recursive. -/
/-
**RecursiveIn.partrec_of_const** 是 Mathlib 中的一个引理，位于命名空间 `RecursiveIn`。
形式化陈述：partrec_of_const {s} (hf : RecursiveIn {fun _ => s} f) : Partrec f
参数：hf : RecursiveIn {fun _ => s} f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RecursiveIn.partrec_of_oracle`：partrec_of_oracle (hO : forall g in O, Pa
rtrec g) (hf : RecursiveIn O f) : Partrec f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Partrec.const'`：const' (s : Part σ) : Partrec fun _ : α => s

--- 原说明 ---
If a function is recursive in a constant partial function, then it is partial re
cursive.
-/
lemma partrec_of_const {s} (hf : RecursiveIn {fun _ => s} f) : Partrec f :=
  hf.partrec_of_oracle
    (fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact .const' s)

end RecursiveIn

@[simp]
/-
**recursiveIn_empty_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：recursiveIn_empty_iff : RecursiveIn {} f ↔ Partrec f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RecursiveIn.partrec_of_oracle`：partrec_of_oracle (hO : forall g in O, Pa
rtrec g) (hf : RecursiveIn O f) : Partrec f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_empty`：forall_mem_empty {p : α -> Prop} : (forall x in (∅
 : Set α), p x) ↔ True
· 使用引理 `Partrec.recursiveIn`：Partrec.recursiveIn [Primcodable α] [Primcodable σ]
 {f : α ->. σ} {O} (hf : Partrec f) : RecursiveIn O f
-/
lemma recursiveIn_empty_iff :
    RecursiveIn {} f ↔ Partrec f :=
  ⟨fun hf => hf.partrec_of_oracle (Set.forall_mem_empty.mpr ⟨⟩), fun hf => hf.recursiveIn⟩

/-- A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`. -/
/-
**partrec_iff_forall_recursiveIn_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：partrec_iff_forall_recursiveIn_singleton : Partrec f ↔ forall g, Recursive
In {g} f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Partrec.recursiveIn`：Partrec.recursiveIn [Primcodable α] [Primcodable σ]
 {f : α ->. σ} {O} (hf : Partrec f) : RecursiveIn O f
· 使用引理 `RecursiveIn.partrec_of_const`：partrec_of_const {s} (hf : RecursiveIn {fu
n _ => s} f) : Partrec f

--- 原说明 ---
A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`.
-/
theorem partrec_iff_forall_recursiveIn_singleton :
    Partrec f ↔ ∀ g, RecursiveIn {g} f :=
  ⟨fun hf _ => hf.recursiveIn, fun hf => (hf (fun _ => .none)).partrec_of_const⟩

namespace ComputableIn

/-
**ComputableIn.const** 是 Mathlib 中的一个定理，位于命名空间 `ComputableIn`。
形式化陈述：∀ {α : Type u_1} {σ : Type u_4} [inst : Primcodable α] [inst_1 : Primcodab
le σ] {O : Set (ℕ →. ℕ)} (s : σ),   ComputableIn O fun x => s
参数：ℕ →. ℕ；s : σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.computableIn`：Primrec.computableIn [Primcodable α] [Primcodable 
σ] {f : α -> σ} {O} (hf : Primrec f) : ComputableIn O f
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
-/
protected theorem const (s : σ) : ComputableIn O (fun _ : α => s) :=
  (Primrec.const s).computableIn
/-
**ComputableIn.id** 是 Mathlib 中的一个定理，位于命名空间 `ComputableIn`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α] {O : Set (ℕ →. ℕ)}, ComputableIn O
 id
参数：ℕ →. ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.computableIn`：Primrec.computableIn [Primcodable α] [Primcodable 
σ] {f : α -> σ} {O} (hf : Primrec f) : ComputableIn O f
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
-/
protected theorem id : ComputableIn O (@id α) :=
  Primrec.id.computableIn
/-
**ComputableIn.fst** 是 Mathlib 中的一个定理，位于命名空间 `ComputableIn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α] [inst_1 : Primcodab
le β] {O : Set (ℕ →. ℕ)},   ComputableIn O Prod.fst
参数：ℕ →. ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.computableIn`：Primrec.computableIn [Primcodable α] [Primcodable 
σ] {f : α -> σ} {O} (hf : Primrec f) : ComputableIn O f
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
-/
protected theorem fst : ComputableIn O (@Prod.fst α β) :=
  Primrec.fst.computableIn
/-
**ComputableIn.snd** 是 Mathlib 中的一个定理，位于命名空间 `ComputableIn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α] [inst_1 : Primcodab
le β] {O : Set (ℕ →. ℕ)},   ComputableIn O Prod.snd
参数：ℕ →. ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.computableIn`：Primrec.computableIn [Primcodable α] [Primcodable 
σ] {f : α -> σ} {O} (hf : Primrec f) : ComputableIn O f
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
-/
protected theorem snd : ComputableIn O (@Prod.snd α β) :=
  Primrec.snd.computableIn
/-
**ComputableIn.unpair** 是 Mathlib 中的一个定理，位于命名空间 `ComputableIn`。
形式化陈述：∀ {O : Set (ℕ →. ℕ)}, ComputableIn O Nat.unpair
参数：ℕ →. ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.computableIn`：Primrec.computableIn [Primcodable α] [Primcodable 
σ] {f : α -> σ} {O} (hf : Primrec f) : ComputableIn O f
· 使用定理 `Primrec.unpair`：unpair : Primrec Nat.unpair
-/
protected theorem unpair : ComputableIn O Nat.unpair :=
  Primrec.unpair.computableIn
/-
**ComputableIn.succ** 是 Mathlib 中的一个定理，位于命名空间 `ComputableIn`。
形式化陈述：∀ {O : Set (ℕ →. ℕ)}, ComputableIn O Nat.succ
参数：ℕ →. ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.computableIn`：Primrec.computableIn [Primcodable α] [Primcodable 
σ] {f : α -> σ} {O} (hf : Primrec f) : ComputableIn O f
· 使用定理 `Primrec.succ`：succ : Primrec Nat.succ
-/
protected theorem succ : ComputableIn O Nat.succ :=
  Primrec.succ.computableIn
/-
**ComputableIn.sumInl** 是 Mathlib 中的一个定理，位于命名空间 `ComputableIn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α] [inst_1 : Primcodab
le β] {O : Set (ℕ →. ℕ)},   ComputableIn O Sum.inl
参数：ℕ →. ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.computableIn`：Primrec.computableIn [Primcodable α] [Primcodable 
σ] {f : α -> σ} {O} (hf : Primrec f) : ComputableIn O f
· 使用定理 `Primrec.sumInl`：sumInl : Primrec (@Sum.inl α β)
-/
protected theorem sumInl : ComputableIn O (@Sum.inl α β) :=
  Primrec.sumInl.computableIn
/-
**ComputableIn.sumInr** 是 Mathlib 中的一个定理，位于命名空间 `ComputableIn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α] [inst_1 : Primcodab
le β] {O : Set (ℕ →. ℕ)},   ComputableIn O Sum.inr
参数：ℕ →. ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.computableIn`：Primrec.computableIn [Primcodable α] [Primcodable 
σ] {f : α -> σ} {O} (hf : Primrec f) : ComputableIn O f
· 使用定理 `Primrec.sumInr`：sumInr : Primrec (@Sum.inr α β)
-/
protected theorem sumInr : ComputableIn O (@Sum.inr α β) :=
  Primrec.sumInr.computableIn

end ComputableIn

