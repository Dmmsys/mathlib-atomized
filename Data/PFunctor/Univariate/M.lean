/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# M-types

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.
-/

@[expose] public section


universe u uA uB v w

open Nat Function

open List

variable (F : PFunctor.{uA, uB})

namespace PFunctor

namespace Approx

/-- `CofixA F n` is an `n` level approximation of an M-type -/
/-
**PFunctor.Approx.CofixA** 是 Mathlib 中的一个归纳类型，位于命名空间 `PFunctor.Approx`。
形式化陈述：PFunctor.{uA, uB} → ℕ → Type (max uA uB)
参数：max uA uB。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CofixA F n` is an `n` level approximation of an M-type
-/
inductive CofixA : ℕ → Type (max uA uB)
  | continue : CofixA 0
  | intro {n} : ∀ a, (F.B a → CofixA n) → CofixA (succ n)

/-- default inhabitant of `CofixA` -/
/-
**PFunctor.Approx.CofixA.default** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.Approx.Cofi
xA`。
形式化陈述：(F : PFunctor.{uA, uB}) → [Inhabited F.A] → (n : ℕ) → PFunctor.Approx.Cofi
xA F n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
default inhabitant of `CofixA`
-/
protected def CofixA.default [Inhabited F.A] : ∀ n, CofixA F n
  | 0 => CofixA.continue
  | succ n => CofixA.intro default fun _ => CofixA.default n
/-
**PFunctor.Approx.** 是 Mathlib 中的一个实例，位于命名空间 `PFunctor.Approx`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited F.A] {n} : Inhabited (CofixA F n) :=
  ⟨CofixA.default F n⟩
/-
**PFunctor.Approx.cofixA_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.Approx`。
形式化陈述：∀ (F : PFunctor.{uA, uB}) (x y : PFunctor.Approx.CofixA F 0), x = y
参数：F : PFunctor.{uA, uB}；x y : PFunctor.Approx.CofixA F 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cofixA_eq_zero : ∀ x y : CofixA F 0, x = y
  | CofixA.continue, CofixA.continue => rfl

variable {F}

/-- The label of the root of the tree for a non-trivial
approximation of the cofix of a pfunctor.
-/
/-
**PFunctor.Approx.head'** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.Approx`。
形式化陈述：{F : PFunctor.{uA, uB}} → {n : ℕ} → PFunctor.Approx.CofixA F n.succ → F.A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The label of the root of the tree for a non-trivial
approximation of the cofix of a pfunctor.
-/
def head' : ∀ {n}, CofixA F (succ n) → F.A
  | _, CofixA.intro i _ => i

/-- for a non-trivial approximation, return all the subtrees of the root -/
/-
**PFunctor.Approx.children'** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.Approx`。
形式化陈述：{F : PFunctor.{uA, uB}} →   {n : ℕ} → (x : PFunctor.Approx.CofixA F n.succ
) → F.B (PFunctor.Approx.head' x) → PFunctor.Approx.CofixA F n
参数：x : PFunctor.Approx.CofixA F n.succ；PFunctor.Approx.head' x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
for a non-trivial approximation, return all the subtrees of the root
-/
def children' : ∀ {n} (x : CofixA F (succ n)), F.B (head' x) → CofixA F n
  | _, CofixA.intro _ f => f
/-
**PFunctor.Approx.approx_eta** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.Approx`。
形式化陈述：approx_eta {n : Nat} (x : CofixA F (n + 1)) : x = CofixA.intro (head' x) (
children' x)
参数：x : CofixA F (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem approx_eta {n : ℕ} (x : CofixA F (n + 1)) : x = CofixA.intro (head' x) (children' x) := by
  cases x; rfl

/-- Relation between two approximations of the cofix of a pfunctor
that state they both contain the same data until one of them is truncated -/
/-
**PFunctor.Approx.Agree** 是 Mathlib 中的一个归纳类型，位于命名空间 `PFunctor.Approx`。
形式化陈述：{F : PFunctor.{uA, uB}} → {n : ℕ} → PFunctor.Approx.CofixA F n → PFunctor.
Approx.CofixA F (n + 1) → Prop
参数：n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Relation between two approximations of the cofix of a pfunctor
that state they both contain the same data until one of them is truncated
-/
inductive Agree : ∀ {n : ℕ}, CofixA F n → CofixA F (n + 1) → Prop
  | continu (x : CofixA F 0) (y : CofixA F 1) : Agree x y
  | intro {n} {a} (x : F.B a → CofixA F n) (x' : F.B a → CofixA F (n + 1)) :
    (∀ i : F.B a, Agree (x i) (x' i)) → Agree (CofixA.intro a x) (CofixA.intro a x')

/-- Given an infinite series of approximations `approx`,
`AllAgree approx` states that they are all consistent with each other.
-/
/-
**PFunctor.Approx.AllAgree** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.Approx`。
形式化陈述：AllAgree (x : forall n, CofixA F n)
参数：x : forall n, CofixA F n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an infinite series of approximations `approx`,
`AllAgree approx` states that they are all consistent with each other.
-/
def AllAgree (x : ∀ n, CofixA F n) :=
  ∀ n, Agree (x n) (x (succ n))

@[simp]
/-
**PFunctor.Approx.agree_trivial** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.Approx`。
形式化陈述：agree_trivial {x : CofixA F 0} {y : CofixA F 1} : Agree x y
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem agree_trivial {x : CofixA F 0} {y : CofixA F 1} : Agree x y := by constructor
/-
**PFunctor.Approx.agree_children** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.Approx`。
形式化陈述：agree_children {n : Nat} (x : CofixA F (succ n)) (y : CofixA F (succ n + 1
)) {i j} (h₀ : i ≍ j) (h₁ : Agree x y) : Agree (children' x i) (children' y j)
参数：x : CofixA F (succ n)；y : CofixA F (succ n + 1)；h₀ : i ≍ j；h₁ : Agree x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem agree_children {n : ℕ} (x : CofixA F (succ n)) (y : CofixA F (succ n + 1)) {i j}
    (h₀ : i ≍ j) (h₁ : Agree x y) : Agree (children' x i) (children' y j) := by
  obtain - | ⟨_, _, hagree⟩ := h₁; cases h₀
  apply hagree

/-- `truncate a` turns `a` into a more limited approximation -/
/-
**PFunctor.Approx.truncate** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.Approx`。
形式化陈述：{F : PFunctor.{uA, uB}} → {n : ℕ} → PFunctor.Approx.CofixA F (n + 1) → PFu
nctor.Approx.CofixA F n
参数：n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`truncate a` turns `a` into a more limited approximation
-/
def truncate : ∀ {n : ℕ}, CofixA F (n + 1) → CofixA F n
  | 0, CofixA.intro _ _ => CofixA.continue
  | succ _, CofixA.intro i f => CofixA.intro i <| truncate ∘ f
/-
**PFunctor.Approx.truncate_eq_of_agree** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.Appro
x`。
形式化陈述：truncate_eq_of_agree {n : Nat} (x : CofixA F n) (y : CofixA F (succ n)) (h
 : Agree x y) : truncate y = x
参数：x : CofixA F n；y : CofixA F (succ n)；h : Agree x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFunctor.Approx.truncate.eq_2`：∀ {F : PFunctor.{uA, uB}} (a : ℕ) (i : F.
A) (f : F.B i → PFunctor.Approx.CofixA F (a + 1)),   PFunctor.Approx.truncate (P
Functor.Approx.Cofi…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem truncate_eq_of_agree {n : ℕ} (x : CofixA F n) (y : CofixA F (succ n)) (h : Agree x y) :
    truncate y = x := by
  induction n with
  | zero =>
    cases x
    cases y
    rfl
  | succ n n_ih =>
    cases h with | intro f y h₁ =>
    simp only [truncate, Function.comp_def]
    congr with y
    exact n_ih _ _ (h₁ y)

variable {X : Type w}
variable (f : X → F X)

/-- `sCorec f i n` creates an approximation of height `n`
of the final coalgebra of `f` -/
/-
**PFunctor.Approx.sCorec** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.Approx`。
形式化陈述：{F : PFunctor.{uA, uB}} → {X : Type w} → (X → ↑F X) → X → (n : ℕ) → PFunct
or.Approx.CofixA F n
参数：X → ↑F X；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sCorec f i n` creates an approximation of height `n`
of the final coalgebra of `f`
-/
def sCorec : X → ∀ n, CofixA F n
  | _, 0 => CofixA.continue
  | j, succ _ => CofixA.intro (f j).1 fun i => sCorec ((f j).2 i) _
/-
**PFunctor.Approx.P_corec** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.Approx`。
形式化陈述：P_corec (i : X) (n : Nat) : Agree (sCorec f i n) (sCorec f i (succ n))
参数：i : X；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem P_corec (i : X) (n : ℕ) : Agree (sCorec f i n) (sCorec f i (succ n)) := by
  induction n generalizing i with
  | zero => constructor
  | succ n n_ih => exact .intro _ _ fun _ => n_ih _

/-- `Path F` provides indices to access internal nodes in `Corec F` -/
/-
**PFunctor.Approx.Path** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.Approx`。
形式化陈述：Path (F : PFunctor.{uA, uB})
参数：F : PFunctor.{uA, uB}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Path F` provides indices to access internal nodes in `Corec F`
-/
def Path (F : PFunctor.{uA, uB}) :=
  List F.Idx
/-
**PFunctor.Approx.Path.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.Approx.Path
`。
形式化陈述：{F : PFunctor.{uA, uB}} → Inhabited (PFunctor.Approx.Path F)
参数：PFunctor.Approx.Path F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Path.inhabited : Inhabited (Path F) :=
  ⟨[]⟩
/-
**PFunctor.Approx.CofixA.instSubsingleton** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.Ap
prox.CofixA`。
形式化陈述：∀ {F : PFunctor.{uA, uB}}, Subsingleton (PFunctor.Approx.CofixA F 0)
参数：PFunctor.Approx.CofixA F 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
instance CofixA.instSubsingleton : Subsingleton (CofixA F 0) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩
/-
**PFunctor.Approx.head_succ'** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.Approx`。
形式化陈述：head_succ' (n m : Nat) (x : forall n, CofixA F n) (Hconsistent : AllAgree 
x) : head' (x (succ n)) = head' (x (succ m))
参数：n m : Nat；x : forall n, CofixA F n；Hconsistent : AllAgree x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem head_succ' (n m : ℕ) (x : ∀ n, CofixA F n) (Hconsistent : AllAgree x) :
    head' (x (succ n)) = head' (x (succ m)) := by
  suffices ∀ n, head' (x (succ n)) = head' (x 1) by simp [this]
  intro n
  induction n with
  | zero => grind
  | succ n n_ih => grind +splitIndPred [Hconsistent (succ n), head']

end Approx

open Approx

/-- Internal definition for `M`. It is needed to avoid name clashes
between `M.mk` and `M.casesOn` and the declarations generated for
the structure -/
/-
**PFunctor.MIntl** 是 Mathlib 中的一个归纳类型，位于命名空间 `PFunctor`。
形式化陈述：PFunctor.{uA, uB} → Type (max uA uB)
参数：max uA uB。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Internal definition for `M`. It is needed to avoid name clashes
between `M.mk` and `M.casesOn` and the declarations generated for
the structure
-/
structure MIntl where
  /-- An `n`-th level approximation, for each depth `n` -/
  approx : ∀ n, CofixA F n
  /-- Each approximation agrees with the next -/
  consistent : AllAgree approx

/-- For polynomial functor `F`, `M F` is its final coalgebra -/
/-
**PFunctor.M** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor`。
形式化陈述：M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For polynomial functor `F`, `M F` is its final coalgebra
-/
def M :=
  MIntl F
/-
**PFunctor.M.default_consistent** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：∀ (F : PFunctor.{uA, uB}) [inst : Inhabited F.A] (n : ℕ), PFunctor.Approx.
Agree default default
参数：F : PFunctor.{uA, uB}；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem M.default_consistent [Inhabited F.A] : ∀ n, Agree (default : CofixA F n) default
  | 0 => Agree.continu _ _
  | succ n => Agree.intro _ _ fun _ => M.default_consistent n
/-
**PFunctor.MIntl.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.MIntl`。
形式化陈述：(F : PFunctor.{uA, uB}) → [Inhabited F.A] → Inhabited F.MIntl
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.M.default_consistent`：∀ (F : PFunctor.{uA, uB}) [inst : Inhabit
ed F.A] (n : ℕ), PFunctor.Approx.Agree default default
-/
instance MIntl.inhabited [Inhabited F.A] : Inhabited (MIntl F) :=
  ⟨{  approx := default
      consistent := M.default_consistent _ }⟩
/-
**PFunctor.M.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：(F : PFunctor.{uA, uB}) → [Inhabited F.A] → Inhabited F.M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance M.inhabited [Inhabited F.A] : Inhabited (M F) :=
  inferInstanceAs <| Inhabited (MIntl F)

namespace M

/-
**PFunctor.M.ext'** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：ext' (x y : M F) (H : forall i : Nat, x.approx i = y.approx i) : x = y
参数：x y : M F；H : forall i : Nat, x.approx i = y.approx i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext' (x y : M F) (H : ∀ i : ℕ, x.approx i = y.approx i) : x = y := by
  cases x
  cases y
  congr with n
  apply H

variable {X : Type*}
variable (f : X → F X)
variable {F}

/-- Corecursor for the M-type defined by `F`. -/
/-
**PFunctor.M.corec** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：{F : PFunctor.{uA, uB}} → {X : Type u_1} → (X → ↑F X) → X → F.M
参数：X → ↑F X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.Approx.P_corec`：P_corec (i : X) (n : Nat) : Agree (sCorec f i n
) (sCorec f i (succ n))

--- 原说明 ---
Corecursor for the M-type defined by `F`.
-/
protected def corec (i : X) : M F where
  approx := sCorec f i
  consistent := P_corec _ _

/-- given a tree generated by `F`, `head` gives us the first piece of data
it contains -/
/-
**PFunctor.M.head** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：head (x : M F)
参数：x : M F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
given a tree generated by `F`, `head` gives us the first piece of data
it contains
-/
def head (x : M F) :=
  head' (x.1 1)

/-- return all the subtrees of the root of a tree `x : M F` -/
/-
**PFunctor.M.children** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：children (x : M F) (i : F.B (head x)) : M F
参数：x : M F；i : F.B (head x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
return all the subtrees of the root of a tree `x : M F`
-/
def children (x : M F) (i : F.B (head x)) : M F :=
  have H := fun n : ℕ => @head_succ' _ n 0 x.1 x.2
  { approx := fun n => children' (x.1 _) (cast (congr_arg _ <| by simp only [head, H]) i)
    consistent := by
      intro n
      have P' := x.2 (succ n)
      apply agree_children _ _ _ P'
      trans i
      · apply cast_heq
      symm
      apply cast_heq }

/-- select a subtree using an `i : F.Idx` or return an arbitrary tree if
`i` designates no subtree of `x` -/
/-
**PFunctor.M.ichildren** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：ichildren [Inhabited (M F)] [DecidableEq F.A] (i : F.Idx) (x : M F) : M F
参数：M F；i : F.Idx；x : M F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
select a subtree using an `i : F.Idx` or return an arbitrary tree if
`i` designates no subtree of `x`
-/
def ichildren [Inhabited (M F)] [DecidableEq F.A] (i : F.Idx) (x : M F) : M F :=
  if H' : i.1 = head x then children x (cast (congr_arg _ <| by simp only [head, H']) i.2)
  else default
/-
**PFunctor.M.head_succ** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：head_succ (n m : Nat) (x : M F) : head' (x.approx (succ n)) = head' (x.app
rox (succ m))
参数：n m : Nat；x : M F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.Approx.head_succ'`：head_succ' (n m : Nat) (x : forall n, CofixA
 F n) (Hconsistent : AllAgree x) : head' (x (succ n)) = head' (x (succ m))
· 使用定理 `PFunctor.MIntl.consistent`：∀ {F : PFunctor.{uA, uB}} (self : F.MIntl), P
Functor.Approx.AllAgree self.approx
-/
theorem head_succ (n m : ℕ) (x : M F) : head' (x.approx (succ n)) = head' (x.approx (succ m)) :=
  head_succ' n m _ x.consistent
/-
**PFunctor.M.head_eq_head'** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：∀ {F : PFunctor.{uA, uB}} (x : F.M) (n : ℕ), x.head = PFunctor.Approx.head
' (x.approx (n + 1))
参数：x : F.M；n : ℕ；x.approx (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.Approx.head_succ'`：head_succ' (n m : Nat) (x : forall n, CofixA
 F n) (Hconsistent : AllAgree x) : head' (x (succ n)) = head' (x (succ m))
-/
theorem head_eq_head' : ∀ (x : M F) (n : ℕ), head x = head' (x.approx <| n + 1)
  | ⟨_, h⟩, _ => head_succ' _ _ _ h
/-
**PFunctor.M.head'_eq_head** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：∀ {F : PFunctor.{uA, uB}} (x : F.M) (n : ℕ), PFunctor.Approx.head' (x.appr
ox (n + 1)) = x.head
参数：x : F.M；n : ℕ；x.approx (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.Approx.head_succ'`：head_succ' (n m : Nat) (x : forall n, CofixA
 F n) (Hconsistent : AllAgree x) : head' (x (succ n)) = head' (x (succ m))
-/
theorem head'_eq_head : ∀ (x : M F) (n : ℕ), head' (x.approx <| n + 1) = head x
  | ⟨_, h⟩, _ => head_succ' _ _ _ h
/-
**PFunctor.M.truncate_approx** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：truncate_approx (x : M F) (n : Nat) : truncate (x.approx <| n + 1) = x.app
rox n
参数：x : M F；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.Approx.truncate_eq_of_agree`：truncate_eq_of_agree {n : Nat} (x 
: CofixA F n) (y : CofixA F (succ n)) (h : Agree x y) : truncate y = x
· 使用定理 `PFunctor.MIntl.consistent`：∀ {F : PFunctor.{uA, uB}} (self : F.MIntl), P
Functor.Approx.AllAgree self.approx
-/
theorem truncate_approx (x : M F) (n : ℕ) : truncate (x.approx <| n + 1) = x.approx n :=
  truncate_eq_of_agree _ _ (x.consistent _)

/-- unfold an M-type -/
/-
**PFunctor.M.dest** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：{F : PFunctor.{uA, uB}} → F.M → ↑F F.M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
unfold an M-type
-/
def dest : M F → F (M F)
  | x => ⟨head x, fun i => children x i⟩

namespace Approx

/-- generates the approximations needed for `M.mk` -/
/-
**PFunctor.M.Approx.sMk** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M.Approx`。
形式化陈述：{F : PFunctor.{uA, uB}} → ↑F F.M → (n : ℕ) → PFunctor.Approx.CofixA F n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
generates the approximations needed for `M.mk`
-/
protected def sMk (x : F (M F)) : ∀ n, CofixA F n
  | 0 => CofixA.continue
  | succ n => CofixA.intro x.1 fun i => (x.2 i).approx n
/-
**PFunctor.M.Approx.P_mk** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M.Approx`。
形式化陈述：∀ {F : PFunctor.{uA, uB}} (x : ↑F F.M), PFunctor.Approx.AllAgree (PFunctor
.M.Approx.sMk x)
参数：x : ↑F F.M；PFunctor.M.Approx.sMk x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.MIntl.consistent`：∀ {F : PFunctor.{uA, uB}} (self : F.MIntl), P
Functor.Approx.AllAgree self.approx
-/
protected theorem P_mk (x : F (M F)) : AllAgree (Approx.sMk x)
  | 0 => by constructor
  | succ n => by
    constructor
    introv
    apply (x.2 i).consistent

end Approx

/-- constructor for M-types -/
/-
**PFunctor.M.mk** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：{F : PFunctor.{uA, uB}} → ↑F F.M → F.M
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.M.Approx.P_mk`：∀ {F : PFunctor.{uA, uB}} (x : ↑F F.M), PFunctor
.Approx.AllAgree (PFunctor.M.Approx.sMk x)

--- 原说明 ---
constructor for M-types
-/
protected def mk (x : F (M F)) : M F where
  approx := Approx.sMk x
  consistent := Approx.P_mk x

/-- `Agree' n` relates two trees of type `M F` that
are the same up to depth `n` -/
/-
**PFunctor.M.Agree'** 是 Mathlib 中的一个归纳类型，位于命名空间 `PFunctor.M`。
形式化陈述：{F : PFunctor.{uA, uB}} → ℕ → F.M → F.M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Agree' n` relates two trees of type `M F` that
are the same up to depth `n`
-/
inductive Agree' : ℕ → M F → M F → Prop
  | trivial (x y : M F) : Agree' 0 x y
  | step {n : ℕ} {a} (x y : F.B a → M F) {x' y'} :
      x' = M.mk ⟨a, x⟩ → y' = M.mk ⟨a, y⟩ → (∀ i, Agree' n (x i) (y i)) → Agree' (succ n) x' y'

@[simp]
/-
**PFunctor.M.dest_mk** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：dest_mk (x : F (M F)) : dest (M.mk x) = x
参数：x : F (M F)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dest_mk (x : F (M F)) : dest (M.mk x) = x := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PFunctor.M.mk_dest** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：mk_dest (x : M F) : M.mk (dest x) = x
参数：x : M F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.M.ext'`：ext' (x y : M F) (H : forall i : Nat, x.approx i = y.ap
prox i) : x = y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `PFunctor.Approx.CofixA.instSubsingleton`：∀ {F : PFunctor.{uA, uB}}, Subs
ingleton (PFunctor.Approx.CofixA F 0)
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PFunctor.Approx.head_succ'`：head_succ' (n m : Nat) (x : forall n, CofixA
 F n) (Hconsistent : AllAgree x) : head' (x (succ n)) = head' (x (succ m))
· 使用定理 `PFunctor.MIntl.consistent`：∀ {F : PFunctor.{uA, uB}} (self : F.MIntl), P
Functor.Approx.AllAgree self.approx
· 使用定理 `PFunctor.Approx.head'.eq_1`：∀ {F : PFunctor.{uA, uB}} (x : ℕ) (i : F.A) 
(a : F.B i → PFunctor.Approx.CofixA F x),   PFunctor.Approx.head' (PFunctor.Appr
ox.CofixA.intro …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `cast_eq_iff_heq`：∀ {a a_1 : Sort u_1} {e : a = a_1} {a_2 : a} {a' : a_1}
, cast e a_2 = a' ↔ a_2 ≍ a'
-/
theorem mk_dest (x : M F) : M.mk (dest x) = x := by
  apply ext'
  intro n
  dsimp only [M.mk]
  induction n with
  | zero => apply @Subsingleton.elim _ CofixA.instSubsingleton
  | succ n => ?_
  dsimp only [Approx.sMk, dest, head]
  rcases h : x.approx (succ n) with - | ⟨hd, ch⟩
  have h' : hd = head' (x.approx 1) := by
    rw [← head_succ' n, h, head']
    apply x.consistent
  revert ch
  rw [h']
  intro ch h
  congr
  ext a
  dsimp only [children]
  generalize hh : cast _ a = a''
  rw [cast_eq_iff_heq] at hh
  revert a''
  rw [h]
  intro _ hh
  cases hh
  rfl
/-
**PFunctor.M.mk_inj** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：mk_inj {x y : F (M F)} (h : M.mk x = M.mk y) : x = y
参数：M F；h : M.mk x = M.mk y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PFunctor.M.dest_mk`：dest_mk (x : F (M F)) : dest (M.mk x) = x
-/
theorem mk_inj {x y : F (M F)} (h : M.mk x = M.mk y) : x = y := by rw [← dest_mk x, h, dest_mk]

/-- destructor for M-types -/
/-
**PFunctor.M.cases** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：{F : PFunctor.{uA, uB}} → {r : F.M → Sort w} → ((x : ↑F F.M) → r (PFunctor
.M.mk x)) → (x : F.M) → r x
参数：(x : ↑F F.M) → r (PFunctor.M.mk x)；x : F.M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
destructor for M-types
-/
protected def cases {r : M F → Sort w} (f : ∀ x : F (M F), r (M.mk x)) (x : M F) : r x :=
  suffices r (M.mk (dest x)) by
    rw [← mk_dest x]
    exact this
  f _

/-- destructor for M-types -/
/-
**PFunctor.M.casesOn** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：{F : PFunctor.{uA, uB}} → {r : F.M → Sort w} → (x : F.M) → ((x : ↑F F.M) →
 r (PFunctor.M.mk x)) → r x
参数：x : F.M；(x : ↑F F.M) → r (PFunctor.M.mk x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
destructor for M-types
-/
protected def casesOn {r : M F → Sort w} (x : M F) (f : ∀ x : F (M F), r (M.mk x)) : r x :=
  M.cases f x

/-- destructor for M-types, similar to `casesOn` but also
gives access directly to the root and subtrees on an M-type -/
/-
**PFunctor.M.casesOn'** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：{F : PFunctor.{uA, uB}} →   {r : F.M → Sort w} → (x : F.M) → ((a : F.A) → 
(f : F.B a → F.M) → r (PFunctor.M.mk ⟨a, f⟩)) → r x
参数：x : F.M；(a : F.A) → (f : F.B a → F.M) → r (PFunctor.M.mk ⟨a, f⟩)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
destructor for M-types, similar to `casesOn` but also
gives access directly to the root and subtrees on an M-type
-/
protected def casesOn' {r : M F → Sort w} (x : M F) (f : ∀ a f, r (M.mk ⟨a, f⟩)) : r x :=
  M.casesOn x (fun ⟨a, g⟩ => f a g)
/-
**PFunctor.M.approx_mk** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：approx_mk (a : F.A) (f : F.B a -> M F) (i : Nat) : (M.mk ⟨a, f⟩).approx (s
ucc i) = CofixA.intro a fun j => (f j).approx i
参数：a : F.A；f : F.B a -> M F；i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem approx_mk (a : F.A) (f : F.B a → M F) (i : ℕ) :
    (M.mk ⟨a, f⟩).approx (succ i) = CofixA.intro a fun j => (f j).approx i :=
  rfl

@[simp]
/-
**PFunctor.M.agree'_refl** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：∀ {F : PFunctor.{uA, uB}} {n : ℕ} (x : F.M), PFunctor.M.Agree' n x x
参数：x : F.M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem agree'_refl {n : ℕ} (x : M F) : Agree' n x x := by
  induction n generalizing x with | zero => ?_ | succ _ n_ih => ?_ <;>
  induction x using PFunctor.M.casesOn' <;> constructor <;> try rfl
  intro; apply n_ih
/-
**PFunctor.M.agree_iff_agree'** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：agree_iff_agree' {n : Nat} (x y : M F) : Agree (x.approx n) (y.approx <| n
 + 1) ↔ Agree' n x y
参数：x y : M F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PFunctor.M.mk_inj`：mk_inj {x y : F (M F)} (h : M.mk x = M.mk y) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem agree_iff_agree' {n : ℕ} (x y : M F) :
    Agree (x.approx n) (y.approx <| n + 1) ↔ Agree' n x y := by
  constructor <;> intro h
  · induction n generalizing x y with
    | zero => constructor
    | succ _ n_ih =>
      induction x using PFunctor.M.casesOn'
      induction y using PFunctor.M.casesOn'
      simp only [approx_mk] at h
      obtain - | ⟨_, _, hagree⟩ := h
      constructor <;> try rfl
      intro i
      apply n_ih
      apply hagree
  · induction n generalizing x y with
    | zero => constructor
    | succ _ n_ih =>
      obtain - | @⟨_, a, x', y'⟩ := h
      induction x using PFunctor.M.casesOn' with | _ x_a x_f
      induction y using PFunctor.M.casesOn' with | _ y_a y_f
      simp only [approx_mk]
      have h_a_1 := mk_inj ‹M.mk ⟨x_a, x_f⟩ = M.mk ⟨a, x'⟩›
      cases h_a_1
      replace h_a_2 := mk_inj ‹M.mk ⟨y_a, y_f⟩ = M.mk ⟨a, y'⟩›
      cases h_a_2
      constructor
      intro i
      apply n_ih
      simp [*]

@[simp]
/-
**PFunctor.M.cases_mk** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：cases_mk {r : M F -> Sort*} (x : F (M F)) (f : forall x : F (M F), r (M.mk
 x)) : PFunctor.M.cases f (M.mk x) = f x
参数：x : F (M F)；f : forall x : F (M F), r (M.mk x)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cases_mk {r : M F → Sort*} (x : F (M F)) (f : ∀ x : F (M F), r (M.mk x)) :
    PFunctor.M.cases f (M.mk x) = f x := rfl

@[simp]
/-
**PFunctor.M.casesOn_mk** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：casesOn_mk {r : M F -> Sort*} (x : F (M F)) (f : forall x : F (M F), r (M.
mk x)) : PFunctor.M.casesOn (M.mk x) f = f x
参数：x : F (M F)；f : forall x : F (M F), r (M.mk x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.M.cases_mk`：cases_mk {r : M F -> Sort*} (x : F (M F)) (f : fora
ll x : F (M F), r (M.mk x)) : PFunctor.M.cases f (M.mk x) = f x
-/
theorem casesOn_mk {r : M F → Sort*} (x : F (M F)) (f : ∀ x : F (M F), r (M.mk x)) :
    PFunctor.M.casesOn (M.mk x) f = f x :=
  cases_mk x f

@[simp]
/-
**PFunctor.M.casesOn_mk'** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：casesOn_mk' {r : M F -> Sort*} {a} (x : F.B a -> M F) (f : forall (a) (f :
 F.B a -> M F), r (M.mk ⟨a, f⟩)) : PFunctor.M.casesOn' (M.mk ⟨a, x⟩) f = f a x
参数：x : F.B a -> M F；f : forall (a) (f : F.B a -> M F), r (M.mk ⟨a, f⟩)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.M.cases_mk`：cases_mk {r : M F -> Sort*} (x : F (M F)) (f : fora
ll x : F (M F), r (M.mk x)) : PFunctor.M.cases f (M.mk x) = f x
-/
theorem casesOn_mk' {r : M F → Sort*} {a} (x : F.B a → M F)
    (f : ∀ (a) (f : F.B a → M F), r (M.mk ⟨a, f⟩)) :
    PFunctor.M.casesOn' (M.mk ⟨a, x⟩) f = f a x :=
  @cases_mk F r ⟨a, x⟩ (fun ⟨a, g⟩ => f a g)

/-- `IsPath p x` tells us if `p` is a valid path through `x` -/
/-
**PFunctor.M.IsPath** 是 Mathlib 中的一个归纳类型，位于命名空间 `PFunctor.M`。
形式化陈述：{F : PFunctor.{uA, uB}} → PFunctor.Approx.Path F → F.M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsPath p x` tells us if `p` is a valid path through `x`
-/
inductive IsPath : Path F → M F → Prop
  | nil (x : M F) : IsPath [] x
  | cons (xs : Path F) {a} (x : M F) (f : F.B a → M F) (i : F.B a) :
    x = M.mk ⟨a, f⟩ → IsPath xs (f i) → IsPath (⟨a, i⟩ :: xs) x
/-
**PFunctor.M.isPath_cons** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：isPath_cons {xs : Path F} {a a'} {f : F.B a -> M F} {i : F.B a'} : IsPath 
(⟨a', i⟩ :: xs) (M.mk ⟨a, f⟩) -> a = a'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `PFunctor.M.mk_inj`：mk_inj {x y : F (M F)} (h : M.mk x = M.mk y) : x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isPath_cons {xs : Path F} {a a'} {f : F.B a → M F} {i : F.B a'} :
    IsPath (⟨a', i⟩ :: xs) (M.mk ⟨a, f⟩) → a = a' := by
  generalize h : M.mk ⟨a, f⟩ = x
  rintro (_ | ⟨_, _, _, _, rfl, _⟩)
  cases mk_inj h
  rfl
/-
**PFunctor.M.isPath_cons'** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：isPath_cons' {xs : Path F} {a} {f : F.B a -> M F} {i : F.B a} : IsPath (⟨a
, i⟩ :: xs) (M.mk ⟨a, f⟩) -> IsPath xs (f i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `PFunctor.M.mk_inj`：mk_inj {x y : F (M F)} (h : M.mk x = M.mk y) : x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isPath_cons' {xs : Path F} {a} {f : F.B a → M F} {i : F.B a} :
    IsPath (⟨a, i⟩ :: xs) (M.mk ⟨a, f⟩) → IsPath xs (f i) := by
  generalize h : M.mk ⟨a, f⟩ = x
  rintro (_ | ⟨_, _, _, _, rfl, hp⟩)
  cases mk_inj h
  exact hp

/-- follow a path through a value of `M F` and return the subtree
found at the end of the path if it is a valid path for that value and
return a default tree -/
/-
**PFunctor.M.isubtree** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：isubtree [DecidableEq F.A] [Inhabited (M F)] : Path F -> M F -> M F | [], 
x => x | ⟨a, i⟩ :: ps, x => PFunctor.M.casesOn' (r
参数：M F。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
follow a path through a value of `M F` and return the subtree
found at the end of the path if it is a valid path for that value and
return a default tree
-/
def isubtree [DecidableEq F.A] [Inhabited (M F)] : Path F → M F → M F
  | [], x => x
  | ⟨a, i⟩ :: ps, x =>
    PFunctor.M.casesOn' (r := fun _ => M F) x (fun a' f =>
      if h : a = a' then
        isubtree ps (f <| cast (by rw [h]) i)
      else
        default (α := M F))

/-- similar to `isubtree` but returns the data at the end of the path instead
of the whole subtree -/
/-
**PFunctor.M.iselect** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：iselect [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) : M F -> F.A
参数：M F；ps : Path F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
similar to `isubtree` but returns the data at the end of the path instead
of the whole subtree
-/
def iselect [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) : M F → F.A := fun x : M F =>
  head <| isubtree ps x
/-
**PFunctor.M.iselect_eq_default** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：iselect_eq_default [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) (x : 
M F) (h : ¬IsPath ps x) : iselect ps x = head default
参数：M F；ps : Path F；x : M F；h : ¬IsPath ps x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PFunctor.M.casesOn_mk'`：casesOn_mk' {r : M F -> Sort*} {a} (x : F.B a ->
 M F) (f : forall (a) (f : F.B a -> M F), r (M.mk ⟨a, f⟩)) : PFunctor.M.casesOn'
 (M.mk ⟨a, x…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem iselect_eq_default [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) (x : M F)
    (h : ¬IsPath ps x) : iselect ps x = head default := by
  induction ps generalizing x with
  | nil =>
    exfalso
    apply h
    constructor
  | cons ps_hd ps_tail ps_ih =>
    obtain ⟨a, i⟩ := ps_hd
    induction x using PFunctor.M.casesOn' with | _ x_a x_f
    simp only [iselect, isubtree] at ps_ih ⊢
    by_cases h'' : a = x_a
    · subst x_a
      simp only [dif_pos, casesOn_mk']
      rw [ps_ih]
      intro h'
      apply h
      constructor <;> try rfl
      apply h'
    · simp [*]

@[simp]
/-
**PFunctor.M.head_mk** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：head_mk (x : F (M F)) : head (M.mk x) = x.1
参数：x : F (M F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFunctor.M.dest_mk`：dest_mk (x : F (M F)) : dest (M.mk x) = x
-/
theorem head_mk (x : F (M F)) : head (M.mk x) = x.1 :=
  Eq.symm <|
    calc
      x.1 = (dest (M.mk x)).1 := by rw [dest_mk]
      _ = head (M.mk x) := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**PFunctor.M.children_mk** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：children_mk {a} (x : F.B a -> M F) (i : F.B (head (M.mk ⟨a, x⟩))) : childr
en (M.mk ⟨a, x⟩) i = x (cast (by rw [head_mk]) i)
参数：x : F.B a -> M F；i : F.B (head (M.mk ⟨a, x⟩))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.M.ext'`：ext' (x y : M F) (H : forall i : Nat, x.approx i = y.ap
prox i) : x = y
-/
theorem children_mk {a} (x : F.B a → M F) (i : F.B (head (M.mk ⟨a, x⟩))) :
    children (M.mk ⟨a, x⟩) i = x (cast (by rw [head_mk]) i) := by apply ext'; intro n; rfl

@[simp]
/-
**PFunctor.M.ichildren_mk** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：ichildren_mk [DecidableEq F.A] [Inhabited (M F)] (x : F (M F)) (i : F.Idx)
 : ichildren i (M.mk x) = x.iget i
参数：M F；x : F (M F)；i : F.Idx。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
theorem ichildren_mk [DecidableEq F.A] [Inhabited (M F)] (x : F (M F)) (i : F.Idx) :
    ichildren i (M.mk x) = x.iget i := by
  dsimp only [ichildren, PFunctor.Obj.iget]
  congr with h

@[simp]
/-
**PFunctor.M.isubtree_cons** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：isubtree_cons [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) {a} (f : F
.B a -> M F) {i : F.B a} : isubtree (⟨_, i⟩ :: ps) (M.mk ⟨a, f⟩) = isubtree ps (
f i)
参数：M F；ps : Path F；f : F.B a -> M F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PFunctor.M.casesOn_mk'`：casesOn_mk' {r : M F -> Sort*} {a} (x : F.B a ->
 M F) (f : forall (a) (f : F.B a -> M F), r (M.mk ⟨a, f⟩)) : PFunctor.M.casesOn'
 (M.mk ⟨a, x…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem isubtree_cons [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) {a} (f : F.B a → M F)
    {i : F.B a} : isubtree (⟨_, i⟩ :: ps) (M.mk ⟨a, f⟩) = isubtree ps (f i) := by
  simp only [isubtree, dif_pos, isubtree, M.casesOn_mk']; rfl

@[simp]
/-
**PFunctor.M.iselect_nil** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：iselect_nil [DecidableEq F.A] [Inhabited (M F)] {a} (f : F.B a -> M F) : i
select nil (M.mk ⟨a, f⟩) = a
参数：M F；f : F.B a -> M F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iselect_nil [DecidableEq F.A] [Inhabited (M F)] {a} (f : F.B a → M F) :
    iselect nil (M.mk ⟨a, f⟩) = a := rfl

@[simp]
/-
**PFunctor.M.iselect_cons** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：iselect_cons [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) {a} (f : F.
B a -> M F) {i} : iselect (⟨a, i⟩ :: ps) (M.mk ⟨a, f⟩) = iselect ps (f i)
参数：M F；ps : Path F；f : F.B a -> M F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFunctor.M.isubtree_cons`：isubtree_cons [DecidableEq F.A] [Inhabited (M 
F)] (ps : Path F) {a} (f : F.B a -> M F) {i : F.B a} : isubtree (⟨_, i⟩ :: ps) (
M.mk ⟨a, f⟩) =…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iselect_cons [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) {a} (f : F.B a → M F) {i} :
    iselect (⟨a, i⟩ :: ps) (M.mk ⟨a, f⟩) = iselect ps (f i) := by simp only [iselect, isubtree_cons]
/-
**PFunctor.M.corec_def** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：corec_def {X} (f : X -> F X) (x₀ : X) : M.corec f x₀ = M.mk (F.map (M.core
c f) (f x₀))
参数：f : X -> F X；x₀ : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PFunctor.Approx.P_corec`：P_corec (i : X) (n : Nat) : Agree (sCorec f i n
) (sCorec f i (succ n))
-/
theorem corec_def {X} (f : X → F X) (x₀ : X) : M.corec f x₀ = M.mk (F.map (M.corec f) (f x₀)) := by
  dsimp only [M.corec, M.mk]
  congr with n
  rcases n with - | n
  · dsimp only [sCorec, Approx.sMk]
  · dsimp only [sCorec, Approx.sMk]
    cases f x₀
    dsimp only [PFunctor.map]
    congr
/-
**PFunctor.M.ext_aux** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：ext_aux [Inhabited (M F)] [DecidableEq F.A] {n : Nat} (x y z : M F) (hx : 
Agree' n z x) (hy : Agree' n z y) (hrec : forall ps : Path F, n = ps.length -> i
select ps x = iselect ps y) : x.approx (n + 1) = y.approx (n + 1)
参数：M F；x y z : M F；hx : Agree' n z x；hy : Agree' n z y；hrec : forall ps : Path F
, n = ps.length -> iselect ps x = iselect ps y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PFunctor.Approx.CofixA.intro.injEq`：∀ {F : PFunctor.{uA, uB}} {n : ℕ} (a
 : F.A) (a_1 : F.B a → PFunctor.Approx.CofixA F n) (a_2 : F.A)   (a_3 : F.B a_2 
→ PFunctor.Approx.CofixA…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `PFunctor.Approx.CofixA.instSubsingleton`：∀ {F : PFunctor.{uA, uB}}, Subs
ingleton (PFunctor.Approx.CofixA F 0)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `PFunctor.M.mk_inj`：mk_inj {x y : F (M F)} (h : M.mk x = M.mk y) : x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PFunctor.M.iselect_cons`：iselect_cons [DecidableEq F.A] [Inhabited (M F)
] (ps : Path F) {a} (f : F.B a -> M F) {i} : iselect (⟨a, i⟩ :: ps) (M.mk ⟨a, f⟩
) = iselect p…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext_aux [Inhabited (M F)] [DecidableEq F.A] {n : ℕ} (x y z : M F) (hx : Agree' n z x)
    (hy : Agree' n z y) (hrec : ∀ ps : Path F, n = ps.length → iselect ps x = iselect ps y) :
    x.approx (n + 1) = y.approx (n + 1) := by
  induction n generalizing x y z with
  | zero =>
    specialize hrec [] rfl
    induction x using PFunctor.M.casesOn'
    induction y using PFunctor.M.casesOn'
    simp only [iselect_nil] at hrec
    subst hrec
    simp only [approx_mk, heq_iff_eq, CofixA.intro.injEq,
      eq_iff_true_of_subsingleton, and_self]
  | succ n n_ih =>
    cases hx
    cases hy
    induction x using PFunctor.M.casesOn'
    induction y using PFunctor.M.casesOn'
    subst z
    iterate 3 (have := mk_inj ‹_›; cases this)
    rename_i n_ih a f₃ f₂ hAgree₂ _ _ h₂ _ _ f₁ h₁ hAgree₁ clr
    simp only [approx_mk]
    have := mk_inj h₁
    cases this; clear h₁
    have := mk_inj h₂
    cases this; clear h₂
    congr
    ext i
    apply n_ih
    · solve_by_elim
    · solve_by_elim
    introv h
    specialize hrec (⟨_, i⟩ :: ps) (congr_arg _ h)
    simp only [iselect_cons] at hrec
    exact hrec
/-
**PFunctor.M.ext** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：ext [Inhabited (M F)] [DecidableEq F.A] (x y : M F) (H : forall ps : Path 
F, iselect ps x = iselect ps y) : x = y
参数：M F；x y : M F；H : forall ps : Path F, iselect ps x = iselect ps y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.M.ext'`：ext' (x y : M F) (H : forall i : Nat, x.approx i = y.ap
prox i) : x = y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `PFunctor.Approx.CofixA.instSubsingleton`：∀ {F : PFunctor.{uA, uB}}, Subs
ingleton (PFunctor.Approx.CofixA F 0)
· 使用定理 `PFunctor.M.ext_aux`：ext_aux [Inhabited (M F)] [DecidableEq F.A] {n : Nat
} (x y z : M F) (hx : Agree' n z x) (hy : Agree' n z y) (hrec : forall ps : Path
 F, n = …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PFunctor.M.agree_iff_agree'`：agree_iff_agree' {n : Nat} (x y : M F) : Ag
ree (x.approx n) (y.approx <| n + 1) ↔ Agree' n x y
· 使用定理 `PFunctor.MIntl.consistent`：∀ {F : PFunctor.{uA, uB}} (self : F.MIntl), P
Functor.Approx.AllAgree self.approx
-/
theorem ext [Inhabited (M F)] [DecidableEq F.A] (x y : M F)
    (H : ∀ ps : Path F, iselect ps x = iselect ps y) :
    x = y := by
  apply ext'; intro i
  induction i with
  | zero => subsingleton
  | succ i i_ih =>
    apply ext_aux x y x
    · rw [← agree_iff_agree']
      apply x.consistent
    · rw [← agree_iff_agree', i_ih]
      apply y.consistent
    introv H'
    dsimp only [iselect] at H
    cases H'
    apply H ps

section Bisim

variable (R : M F → M F → Prop)

local infixl:50 " ~ " => R

/-- Bisimulation is the standard proof technique for equality between
infinite tree-like structures -/
/-
**PFunctor.M.IsBisimulation** 是 Mathlib 中的一个归纳类型，位于命名空间 `PFunctor.M`。
形式化陈述：{F : PFunctor.{uA, uB}} → (F.M → F.M → Prop) → Prop
参数：F.M → F.M → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bisimulation is the standard proof technique for equality between
infinite tree-like structures
-/
structure IsBisimulation : Prop where
  /-- The head of the trees are equal -/
  head : ∀ {a a'} {f f'}, M.mk ⟨a, f⟩ ~ M.mk ⟨a', f'⟩ → a = a'
  /-- The tails are equal -/
  tail : ∀ {a} {f f' : F.B a → M F}, M.mk ⟨a, f⟩ ~ M.mk ⟨a, f'⟩ → ∀ i : F.B a, f i ~ f' i

set_option backward.isDefEq.respectTransparency false in
/-
**PFunctor.M.nth_of_bisim** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：nth_of_bisim [Inhabited (M F)] [DecidableEq F.A] (bisim : IsBisimulation R
) (s₁ s₂) (ps : Path F) : (R s₁ s₂) -> IsPath ps s₁ ∨ IsPath ps s₂ -> iselect ps
 s₁ = iselect ps s₂ ∧ exists (a : _) (f f' : F.B a -> M F), isubtree ps s₁ = M.m
k ⟨a, f⟩ ∧ isubtree ps s₂ = M.mk ⟨a, f'⟩ ∧ forall i : F.B a, f i ~ f' i
参数：M F；bisim : IsBisimulation R；s₁ s₂；ps : Path F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.M.IsBisimulation.tail`：∀ {F : PFunctor.{uA, uB}} {R : F.M → F.M
 → Prop},   PFunctor.M.IsBisimulation R →     ∀ {a : F.A} {f f' : F.B a → F.M}, 
R (PFunctor.M.mk ⟨a,…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PFunctor.M.isubtree_cons`：isubtree_cons [DecidableEq F.A] [Inhabited (M 
F)] (ps : Path F) {a} (f : F.B a -> M F) {i : F.B a} : isubtree (⟨_, i⟩ :: ps) (
M.mk ⟨a, f⟩) =…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `PFunctor.M.isPath_cons'`：isPath_cons' {xs : Path F} {a} {f : F.B a -> M 
F} {i : F.B a} : IsPath (⟨a, i⟩ :: xs) (M.mk ⟨a, f⟩) -> IsPath xs (f i)
· 使用定理 `PFunctor.M.IsBisimulation.head`：∀ {F : PFunctor.{uA, uB}} {R : F.M → F.M
 → Prop},   PFunctor.M.IsBisimulation R →     ∀ {a a' : F.A} {f : F.B a → F.M} {
f' : F.B a' → F.M}, …
· 使用定理 `PFunctor.M.isPath_cons`：isPath_cons {xs : Path F} {a a'} {f : F.B a -> M
 F} {i : F.B a'} : IsPath (⟨a', i⟩ :: xs) (M.mk ⟨a, f⟩) -> a = a'
-/
theorem nth_of_bisim [Inhabited (M F)] [DecidableEq F.A]
    (bisim : IsBisimulation R) (s₁ s₂) (ps : Path F) :
    (R s₁ s₂) →
      IsPath ps s₁ ∨ IsPath ps s₂ →
        iselect ps s₁ = iselect ps s₂ ∧
          ∃ (a : _) (f f' : F.B a → M F),
            isubtree ps s₁ = M.mk ⟨a, f⟩ ∧
              isubtree ps s₂ = M.mk ⟨a, f'⟩ ∧ ∀ i : F.B a, f i ~ f' i := by
  intro h₀ hh
  induction s₁ using PFunctor.M.casesOn' with | _ a f
  induction s₂ using PFunctor.M.casesOn' with | _ a' f'
  obtain rfl : a = a' := bisim.head h₀
  induction ps generalizing a f f' with
  | nil =>
    exists rfl, a, f, f', rfl, rfl
    apply bisim.tail h₀
  | cons i ps ps_ih => ?_
  obtain ⟨a', i⟩ := i
  obtain rfl : a = a' := by rcases hh with hh | hh <;> cases isPath_cons hh <;> rfl
  dsimp only [iselect] at ps_ih ⊢
  have h₁ := bisim.tail h₀ i
  induction h : f i using PFunctor.M.casesOn' with | _ a₀ f₀
  induction h' : f' i using PFunctor.M.casesOn' with | _ a₁ f₁
  simp only [h, h', isubtree_cons] at ps_ih ⊢
  rw [h, h'] at h₁
  obtain rfl : a₀ = a₁ := bisim.head h₁
  apply ps_ih _ _ _ h₁
  rw [← h, ← h']
  apply Or.imp isPath_cons' isPath_cons' hh
/-
**PFunctor.M.eq_of_bisim** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：eq_of_bisim [Nonempty (M F)] (bisim : IsBisimulation R) : forall s₁ s₂, R 
s₁ s₂ -> s₁ = s₂
参数：M F；bisim : IsBisimulation R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.M.ext`：ext [Inhabited (M F)] [DecidableEq F.A] (x y : M F) (H :
 forall ps : Path F, iselect ps x = iselect ps y) : x = y
· 使用定理 `PFunctor.M.nth_of_bisim`：nth_of_bisim [Inhabited (M F)] [DecidableEq F.A
] (bisim : IsBisimulation R) (s₁ s₂) (ps : Path F) : (R s₁ s₂) -> IsPath ps s₁ ∨
 IsPath ps s₂…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PFunctor.M.iselect_eq_default`：iselect_eq_default [DecidableEq F.A] [Inh
abited (M F)] (ps : Path F) (x : M F) (h : ¬IsPath ps x) : iselect ps x = head d
efault
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_of_bisim [Nonempty (M F)] (bisim : IsBisimulation R) : ∀ s₁ s₂, R s₁ s₂ → s₁ = s₂ := by
  inhabit M F
  classical
  introv Hr; apply ext
  introv
  by_cases h : IsPath ps s₁ ∨ IsPath ps s₂
  · have H := nth_of_bisim R bisim _ _ ps Hr h
    exact H.left
  · rw [not_or] at h
    obtain ⟨h₀, h₁⟩ := h
    simp only [iselect_eq_default, *, not_false_iff]

end Bisim

universe u' v'

/-- corecursor for `M F` with swapped arguments -/
/-
**PFunctor.M.corecOn** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：corecOn {X : Type*} (x₀ : X) (f : X -> F X) : M F
参数：x₀ : X；f : X -> F X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
corecursor for `M F` with swapped arguments
-/
def corecOn {X : Type*} (x₀ : X) (f : X → F X) : M F :=
  M.corec f x₀

variable {P : PFunctor.{uA, uB}} {α : Type*}
/-
**PFunctor.M.dest_corec** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：dest_corec (g : α -> P α) (x : α) : M.dest (M.corec g x) = P.map (M.corec 
g) (g x)
参数：g : α -> P α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFunctor.M.corec_def`：corec_def {X} (f : X -> F X) (x₀ : X) : M.corec f 
x₀ = M.mk (F.map (M.corec f) (f x₀))
· 使用定理 `PFunctor.M.dest_mk`：dest_mk (x : F (M F)) : dest (M.mk x) = x
-/
theorem dest_corec (g : α → P α) (x : α) : M.dest (M.corec g x) = P.map (M.corec g) (g x) := by
  rw [corec_def, dest_mk]

set_option backward.isDefEq.respectTransparency false in
/-
**PFunctor.M.bisim** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：bisim (R : M P -> M P -> Prop) (h : forall x y, R x y -> exists a f f', M.
dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ forall i, R (f i) (f' i)) : forall x y, R
 x y -> x = y
参数：R : M P -> M P -> Prop；h : forall x y, R x y -> exists a f f', M.dest x = ⟨a,
 f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ forall i, R (f i) (f' i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.M.eq_of_bisim`：eq_of_bisim [Nonempty (M F)] (bisim : IsBisimula
tion R) : forall s₁ s₂, R s₁ s₂ -> s₁ = s₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem bisim (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f', M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ ∀ i, R (f i) (f' i)) :
    ∀ x y, R x y → x = y := by
  introv h'
  have := Inhabited.mk x.head
  apply eq_of_bisim R _ _ _ h'; clear h' x y
  constructor <;> introv ih <;> rcases h _ _ ih with ⟨a'', g, g', h₀, h₁, h₂⟩ <;> clear h
  · replace h₀ := congr_arg Sigma.fst h₀
    replace h₁ := congr_arg Sigma.fst h₁
    simp only [dest_mk] at h₀ h₁
    rw [h₀, h₁]
  · simp only [dest_mk] at h₀ h₁
    cases h₀
    cases h₁
    apply h₂
/-
**PFunctor.M.bisim'** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：bisim' {α : Type*} (Q : α -> Prop) (u v : α -> M P) (h : forall x, Q x -> 
exists a f f', M.dest (u x) = ⟨a, f⟩ ∧ M.dest (v x) = ⟨a, f'⟩ ∧ forall i, exists
 x', Q x' ∧ f i = u x' ∧ f' i = v x') : forall x, Q x -> u x = v x
参数：Q : α -> Prop；u v : α -> M P；h : forall x, Q x -> exists a f f', M.dest (u x)
 = ⟨a, f⟩ ∧ M.dest (v x) = ⟨a, f'⟩ ∧ forall i, exists x', Q x' ∧ f i = u x' ∧ f'
 i = v x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.M.bisim`：bisim (R : M P -> M P -> Prop) (h : forall x y, R x y 
-> exists a f f', M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ forall i, R (f i) (f'
 i)) :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bisim' {α : Type*} (Q : α → Prop) (u v : α → M P)
    (h : ∀ x, Q x → ∃ a f f',
          M.dest (u x) = ⟨a, f⟩
          ∧ M.dest (v x) = ⟨a, f'⟩
          ∧ ∀ i, ∃ x', Q x' ∧ f i = u x' ∧ f' i = v x') :
    ∀ x, Q x → u x = v x := fun x Qx =>
  let R := fun w z : M P => ∃ x', Q x' ∧ w = u x' ∧ z = v x'
  @M.bisim P R
    (fun _ _ ⟨x', Qx', xeq, yeq⟩ =>
      let ⟨a, f, f', ux'eq, vx'eq, h'⟩ := h x' Qx'
      ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
    _ _ ⟨x, Qx, rfl, rfl⟩

-- for the record, show M_bisim follows from _bisim'
/-
**PFunctor.M.bisim_equiv** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：bisim_equiv (R : M P -> M P -> Prop) (h : forall x y, R x y -> exists a f 
f', M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ forall i, R (f i) (f' i)) : forall 
x y, R x y -> x = y
参数：R : M P -> M P -> Prop；h : forall x y, R x y -> exists a f f', M.dest x = ⟨a,
 f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ forall i, R (f i) (f' i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.M.bisim'`：bisim' {α : Type*} (Q : α -> Prop) (u v : α -> M P) (
h : forall x, Q x -> exists a f f', M.dest (u x) = ⟨a, f⟩ ∧ M.dest (v x) = ⟨a, f
'⟩ ∧ fo…
-/
theorem bisim_equiv (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f', M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ ∀ i, R (f i) (f' i)) :
    ∀ x y, R x y → x = y := fun x y Rxy =>
  let Q : M P × M P → Prop := fun p => R p.fst p.snd
  bisim' Q Prod.fst Prod.snd
    (fun p Qp =>
      let ⟨a, f, f', hx, hy, h'⟩ := h p.fst p.snd Qp
      ⟨a, f, f', hx, hy, fun i => ⟨⟨f i, f' i⟩, h' i, rfl, rfl⟩⟩)
    ⟨x, y⟩ Rxy
/-
**PFunctor.M.corec_unique** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.M`。
形式化陈述：corec_unique (g : α -> P α) (f : α -> M P) (hyp : forall x, M.dest (f x) =
 P.map f (g x)) : f = M.corec g
参数：g : α -> P α；f : α -> M P；hyp : forall x, M.dest (f x) = P.map f (g x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PFunctor.M.bisim'`：bisim' {α : Type*} (Q : α -> Prop) (u v : α -> M P) (
h : forall x, Q x -> exists a f f', M.dest (u x) = ⟨a, f⟩ ∧ M.dest (v x) = ⟨a, f
'⟩ ∧ fo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFunctor.map_eq`：∀ (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} (
f : α → β) (a : P.A) (g : P.B a → α), P.map f ⟨a, g⟩ = ⟨a, f ∘ g⟩
· 使用定理 `PFunctor.M.dest_corec`：dest_corec (g : α -> P α) (x : α) : M.dest (M.cor
ec g x) = P.map (M.corec g) (g x)
· 使用定理 `trivial`：True
-/
theorem corec_unique (g : α → P α) (f : α → M P) (hyp : ∀ x, M.dest (f x) = P.map f (g x)) :
    f = M.corec g := by
  ext x
  apply bisim' (fun _ => True) _ _ _ _ trivial
  clear x
  intro x _
  rcases gxeq : g x with ⟨a, f'⟩
  have h₀ : M.dest (f x) = ⟨a, f ∘ f'⟩ := by rw [hyp, gxeq, PFunctor.map_eq]
  have h₁ : M.dest (M.corec g x) = ⟨a, M.corec g ∘ f'⟩ := by rw [dest_corec, gxeq, PFunctor.map_eq]
  refine ⟨_, _, _, h₀, h₁, ?_⟩
  intro i
  exact ⟨f' i, trivial, rfl, rfl⟩

/-- corecursor where the state of the computation can be sent downstream
in the form of a recursive call -/
/-
**PFunctor.M.corec** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：{F : PFunctor.{uA, uB}} → {X : Type u_1} → (X → ↑F X) → X → F.M
参数：X → ↑F X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.Approx.P_corec`：P_corec (i : X) (n : Nat) : Agree (sCorec f i n
) (sCorec f i (succ n))

--- 原说明 ---
corecursor where the state of the computation can be sent downstream
in the form of a recursive call
-/
def corec₁ {α : Type u} (F : ∀ X, (α → X) → α → P X) : α → M P :=
  M.corec (F _ id)

/-- corecursor where it is possible to return a fully formed value at any point
of the computation -/
/-
**PFunctor.M.corec'** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.M`。
形式化陈述：corec' {α : Type u} (F : forall {X : Type (max u uA uB)}, (α -> X) -> α ->
 M P oplus P X) (x : α) : M P
参数：F : forall {X : Type (max u uA uB)}, (α -> X) -> α -> M P oplus P X；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
corecursor where it is possible to return a fully formed value at any point
of the computation
-/
def corec' {α : Type u} (F : ∀ {X : Type (max u uA uB)}, (α → X) → α → M P ⊕ P X) (x : α) : M P :=
  corec₁
    (fun _ rec (a : M P ⊕ α) =>
      let y := Sum.bind a (F (rec ∘ Sum.inr))
      match y with
      | Sum.inr y => y
      | Sum.inl y => P.map (rec ∘ Sum.inl) (M.dest y))
    (@Sum.inr (M P) _ x)

end M

end PFunctor

