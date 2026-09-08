/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
module

public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.M

/-!
# The M construction as a multivariate polynomial functor.

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.

## Main definitions

* `M.mk`     - constructor
* `M.dest`   - destructor
* `M.corec`  - corecursor: useful for formulating infinite, productive computations
* `M.bisim`  - bisimulation: proof technique to show the equality of infinite objects

## Implementation notes

Dual view of M-types:

* `mp`: polynomial functor
* `M`: greatest fixed point of a polynomial functor

Specifically, we define the polynomial functor `mp` as:

* A := a possibly infinite tree-like structure without information in the nodes
* B := given the tree-like structure `t`, `B t` is a valid path
  from the root of `t` to any given node.

As a result `mp α` is made of a dataless tree and a function from
its valid paths to values of `α`

The difference with the polynomial functor of an initial algebra is
that `A` is a possibly infinite tree.

## Reference

* Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
  [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

@[expose] public section



universe u v

open MvFunctor

namespace MvPFunctor

open TypeVec

variable {n : ℕ} (P : MvPFunctor.{u} (n + 1))

/-- A path from the root of a tree to one of its node -/
/-
**MvPFunctor.M.Path** 是 Mathlib 中的一个归纳类型，位于命名空间 `MvPFunctor.M`。
形式化陈述：{n : ℕ} → (P : MvPFunctor.{u} (n + 1)) → P.last.M → Fin2 n → Type u
参数：P : MvPFunctor.{u} (n + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path from the root of a tree to one of its node
-/
inductive M.Path : P.last.M → Fin2 n → Type u
  | root (x : P.last.M)
          (a : P.A)
          (f : P.last.B a → P.last.M)
          (h : PFunctor.M.dest x = ⟨a, f⟩)
          (i : Fin2 n)
          (c : P.drop.B a i) : M.Path x i
  | child (x : P.last.M)
          (a : P.A)
          (f : P.last.B a → P.last.M)
          (h : PFunctor.M.dest x = ⟨a, f⟩)
          (j : P.last.B a)
          (i : Fin2 n)
          (c : M.Path (f j) i) : M.Path x i
/-
**MvPFunctor.M.Path.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.M.Path`。
形式化陈述：{n : ℕ} →   (P : MvPFunctor.{u} (n + 1)) →     (x : P.last.M) → {i : Fin2 
n} → [Inhabited (P.drop.B x.head i)] → Inhabited (MvPFunctor.M.Path P x i)
参数：P : MvPFunctor.{u} (n + 1)；x : P.last.M；P.drop.B x.head i；MvPFunctor.M.Path P
 x i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance M.Path.inhabited (x : P.last.M) {i} [Inhabited (P.drop.B x.head i)] :
    Inhabited (M.Path P x i) :=
  let a := PFunctor.M.head x
  let f := PFunctor.M.children x
  ⟨M.Path.root _ a f
      (PFunctor.M.casesOn' x
        (r := fun _ => PFunctor.M.dest x = ⟨a, f⟩)
        <| by
        intros; simp [a]; rfl)
      _ default⟩

/-- Polynomial functor of the M-type of `P`. `A` is a data-less
possibly infinite tree whereas, for a given `a : A`, `B a` is a valid
path in tree `a` so that `mp α` is made of a tree and a function
from its valid paths to the values it contains -/
/-
**MvPFunctor.mp** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：mp : MvPFunctor n where A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Polynomial functor of the M-type of `P`. `A` is a data-less
possibly infinite tree whereas, for a given `a : A`, `B a` is a valid
path in tree `a` so that `mp α` is made of a tree and a function
from its valid paths to the values it contains
-/
def mp : MvPFunctor n where
  A := P.last.M
  B := M.Path P

/-- `n`-ary M-type for `P` -/
/-
**MvPFunctor.M** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：M (α : TypeVec n) : Type _
参数：α : TypeVec n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n`-ary M-type for `P`
-/
def M (α : TypeVec n) : Type _ :=
  P.mp α
/-
**MvPFunctor.mvfunctorM** 是 Mathlib 中的一个实例，位于命名空间 `MvPFunctor`。
形式化陈述：mvfunctorM : MvFunctor P.M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mvfunctorM : MvFunctor P.M := by delta M; infer_instance
/-
**MvPFunctor.inhabitedM** 是 Mathlib 中的一个实例，位于命名空间 `MvPFunctor`。
形式化陈述：inhabitedM {α : TypeVec _} [I : Inhabited P.A] [forall i : Fin2 n, Inhabit
ed (α i)] : Inhabited (P.M α)
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedM {α : TypeVec _} [I : Inhabited P.A] [∀ i : Fin2 n, Inhabited (α i)] :
    Inhabited (P.M α) :=
  @Obj.inhabited _ (mp P) _ (@PFunctor.M.inhabited P.last I) _

/-- construct through corecursion the shape of an M-type
without its contents -/
/-
**MvPFunctor.M.corecShape** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.M`。
形式化陈述：{n : ℕ} → (P : MvPFunctor.{u} (n + 1)) → {β : Type v} → (g₀ : β → P.A) → (
(b : β) → P.last.B (g₀ b) → β) → β → P.last.M
参数：P : MvPFunctor.{u} (n + 1)；g₀ : β → P.A；(b : β) → P.last.B (g₀ b) → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
construct through corecursion the shape of an M-type
without its contents
-/
def M.corecShape {β : Type v} (g₀ : β → P.A) (g₂ : ∀ b : β, P.last.B (g₀ b) → β) :
    β → P.last.M :=
  PFunctor.M.corec fun b => ⟨g₀ b, g₂ b⟩

/-- Proof of type equality as an arrow -/
/-
**MvPFunctor.castDropB** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：castDropB {a a' : P.A} (h : a = a') : P.drop.B a ⟹ P.drop.B a'
参数：h : a = a'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Proof of type equality as an arrow
-/
def castDropB {a a' : P.A} (h : a = a') : P.drop.B a ⟹ P.drop.B a' := fun _i b => Eq.recOn h b

/-- Proof of type equality as a function -/
/-
**MvPFunctor.castLastB** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：castLastB {a a' : P.A} (h : a = a') : P.last.B a -> P.last.B a'
参数：h : a = a'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Proof of type equality as a function
-/
def castLastB {a a' : P.A} (h : a = a') : P.last.B a → P.last.B a' := fun b => Eq.recOn h b

set_option backward.isDefEq.respectTransparency false in
/-- Using corecursion, construct the contents of an M-type -/
/-
**MvPFunctor.M.corecContents** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.M`。
形式化陈述：{n : ℕ} →   (P : MvPFunctor.{u} (n + 1)) →     {α : TypeVec.{u} n} →      
 {β : Type v} →         (g₀ : β → P.A) →           ((b : β) → (P.drop.B (g₀ b)).
Arrow α) →             (g₂ : (b : β) → P.last.B (g₀ b) → β) →               (x :
 P.last.M) → (b : β) → x = MvPFunctor.M.corecShape P g₀ g₂ b → TypeVec.Arrow (Mv
PFunctor.M.Path P x) α
参数：P : MvPFunctor.{u} (n + 1)；g₀ : β → P.A；(b : β) → (P.drop.B (g₀ b)).Arrow α；g
₂ : (b : β) → P.last.B (g₀ b) → β；x : P.last.M；b : β；MvPFunctor.M.Path P x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Using corecursion, construct the contents of an M-type
-/
def M.corecContents {α : TypeVec.{u} n}
    {β : Type v}
    (g₀ : β → P.A)
    (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : ∀ b : β, P.last.B (g₀ b) → β)
    (x : _)
    (b : β)
    (h : x = M.corecShape P g₀ g₂ b) :
    M.Path P x ⟹ α
  | _, M.Path.root x a f h' i c =>
    have : a = g₀ b := by
      rw [h, M.corecShape, PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    g₁ b i (P.castDropB this i c)
  | _, M.Path.child x a f h' j i c =>
    have h₀ : a = g₀ b := by
      rw [h, M.corecShape, PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    have h₁ : f j = M.corecShape P g₀ g₂ (g₂ b (castLastB P h₀ j)) := by
      rw [h, M.corecShape, PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    M.corecContents g₀ g₁ g₂ (f j) (g₂ b (P.castLastB h₀ j)) h₁ i c

/-- Corecursor for M-type of `P` -/
/-
**MvPFunctor.M.corec'** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.M`。
形式化陈述：{n : ℕ} →   (P : MvPFunctor.{u} (n + 1)) →     {α : TypeVec.{u} n} →      
 {β : Type v} →         (g₀ : β → P.A) → ((b : β) → (P.drop.B (g₀ b)).Arrow α) →
 ((b : β) → P.last.B (g₀ b) → β) → β → P.M α
参数：P : MvPFunctor.{u} (n + 1)；g₀ : β → P.A；(b : β) → (P.drop.B (g₀ b)).Arrow α；(
b : β) → P.last.B (g₀ b) → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Corecursor for M-type of `P`
-/
def M.corec' {α : TypeVec n} {β : Type v} (g₀ : β → P.A) (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : ∀ b : β, P.last.B (g₀ b) → β) : β → P.M α := fun b =>
  ⟨M.corecShape P g₀ g₂ b, M.corecContents P g₀ g₁ g₂ _ _ rfl⟩

/-- Corecursor for M-type of `P` -/
/-
**MvPFunctor.M.corec** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.M`。
形式化陈述：{n : ℕ} → (P : MvPFunctor.{u} (n + 1)) → {α : TypeVec.{u} n} → {β : Type u
} → (β → ↑P (α ::: β)) → β → P.M α
参数：P : MvPFunctor.{u} (n + 1)；β → ↑P (α ::: β)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Corecursor for M-type of `P`
-/
def M.corec {α : TypeVec n} {β : Type u} (g : β → P (α.append1 β)) : β → P.M α :=
  M.corec' P (fun b => (g b).fst) (fun b => dropFun (g b).snd) fun b => lastFun (g b).snd

/-- Implementation of destructor for M-type of `P` -/
/-
**MvPFunctor.M.pathDestLeft** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.M`。
形式化陈述：{n : ℕ} →   (P : MvPFunctor.{u} (n + 1)) →     {α : TypeVec.{u_1} n} →    
   {x : P.last.M} →         {a : P.A} →           {f : P.last.B a → P.last.M} → 
x.dest = ⟨a, f⟩ → TypeVec.Arrow (MvPFunctor.M.Path P x) α → (P.drop.B a).Arrow α
参数：P : MvPFunctor.{u} (n + 1)；MvPFunctor.M.Path P x；P.drop.B a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of destructor for M-type of `P`
-/
def M.pathDestLeft {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P.drop.B a ⟹ α := fun i c =>
  f' i (M.Path.root x a f h i c)

/-- Implementation of destructor for M-type of `P` -/
/-
**MvPFunctor.M.pathDestRight** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.M`。
形式化陈述：{n : ℕ} →   (P : MvPFunctor.{u} (n + 1)) →     {α : TypeVec.{u_1} n} →    
   {x : P.last.M} →         {a : P.A} →           {f : P.last.B a → P.last.M} → 
            x.dest = ⟨a, f⟩ →               TypeVec.Arrow (MvPFunctor.M.Path P x
) α → (j : P.last.B a) → TypeVec.Arrow (MvPFunctor.M.Path P (f j)) α
参数：P : MvPFunctor.{u} (n + 1)；MvPFunctor.M.Path P x；j : P.last.B a；MvPFunctor.M.
Path P (f j)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of destructor for M-type of `P`
-/
def M.pathDestRight {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) :
    ∀ j : P.last.B a, M.Path P (f j) ⟹ α := fun j i c => f' i (M.Path.child x a f h j i c)

/-- Destructor for M-type of `P` -/
/-
**MvPFunctor.M.dest'** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.M`。
形式化陈述：{n : ℕ} →   (P : MvPFunctor.{u} (n + 1)) →     {α : TypeVec.{u} n} →      
 {x : P.last.M} →         {a : P.A} →           {f : P.last.B a → P.last.M} → x.
dest = ⟨a, f⟩ → TypeVec.Arrow (MvPFunctor.M.Path P x) α → ↑P (α ::: P.M α)
参数：P : MvPFunctor.{u} (n + 1)；MvPFunctor.M.Path P x；α ::: P.M α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Destructor for M-type of `P`
-/
def M.dest' {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P (α.append1 (P.M α)) :=
  ⟨a, splitFun (M.pathDestLeft P h f') fun x => ⟨f x, M.pathDestRight P h f' x⟩⟩

/-- Destructor for M-types -/
/-
**MvPFunctor.M.dest** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.M`。
形式化陈述：{n : ℕ} → (P : MvPFunctor.{u} (n + 1)) → {α : TypeVec.{u} n} → P.M α → ↑P 
(α ::: P.M α)
参数：P : MvPFunctor.{u} (n + 1)；α ::: P.M α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Destructor for M-types
-/
def M.dest {α : TypeVec n} (x : P.M α) : P (α ::: P.M α) :=
  M.dest' P (Sigma.eta <| PFunctor.M.dest x.fst).symm x.snd

/-- Constructor for M-types -/
/-
**MvPFunctor.M.mk** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.M`。
形式化陈述：{n : ℕ} → (P : MvPFunctor.{u} (n + 1)) → {α : TypeVec.{u} n} → ↑P (α ::: P
.M α) → P.M α
参数：P : MvPFunctor.{u} (n + 1)；α ::: P.M α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for M-types
-/
def M.mk {α : TypeVec n} : P (α.append1 (P.M α)) → P.M α :=
  M.corec _ fun i => appendFun id (M.dest P) <$$> i
/-
**MvPFunctor.M.dest'_eq_dest'** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.M`。
形式化陈述：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n} {x : P.last.M} 
{a₁ : P.A} {f₁ : P.last.B a₁ → P.last.M}   (h₁ : x.dest = ⟨a₁, f₁⟩) {a₂ : P.A} {
f₂ : P.last.B a₂ → P.last.M} (h₂ : x.dest = ⟨a₂, f₂⟩)   (f' : TypeVec.Arrow (MvP
Functor.M.Path P x) α), MvPFunctor.M.dest' P h₁ f' = MvPFunctor.M.dest' P h₂ f'
参数：P : MvPFunctor.{u} (n + 1)；h₁ : x.dest = ⟨a₁, f₁⟩；h₂ : x.dest = ⟨a₂, f₂⟩；f' :
 TypeVec.Arrow (MvPFunctor.M.Path P x) α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem M.dest'_eq_dest' {α : TypeVec n} {x : P.last.M} {a₁ : P.A}
    {f₁ : P.last.B a₁ → P.last.M} (h₁ : PFunctor.M.dest x = ⟨a₁, f₁⟩) {a₂ : P.A}
    {f₂ : P.last.B a₂ → P.last.M} (h₂ : PFunctor.M.dest x = ⟨a₂, f₂⟩) (f' : M.Path P x ⟹ α) :
    M.dest' P h₁ f' = M.dest' P h₂ f' := by cases h₁.symm.trans h₂; rfl
/-
**MvPFunctor.M.dest_eq_dest'** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.M`。
形式化陈述：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n} {x : P.last.M} 
{a : P.A} {f : P.last.B a → P.last.M}   (h : x.dest = ⟨a, f⟩) (f' : TypeVec.Arro
w (MvPFunctor.M.Path P x) α),   MvPFunctor.M.dest P ⟨x, f'⟩ = MvPFunctor.M.dest'
 P h f'
参数：P : MvPFunctor.{u} (n + 1)；h : x.dest = ⟨a, f⟩；f' : TypeVec.Arrow (MvPFunctor
.M.Path P x) α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPFunctor.M.dest'_eq_dest'`：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α :
 TypeVec.{u} n} {x : P.last.M} {a₁ : P.A} {f₁ : P.last.B a₁ → P.last.M}   (h₁ : 
x.dest = ⟨a₁, f₁⟩…
-/
theorem M.dest_eq_dest' {α : TypeVec n} {x : P.last.M} {a : P.A}
    {f : P.last.B a → P.last.M} (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) :
    M.dest P ⟨x, f'⟩ = M.dest' P h f' :=
  M.dest'_eq_dest' _ _ _ _
/-
**MvPFunctor.M.dest_corec'** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.M`。
形式化陈述：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n} {β : Type v} (g
₀ : β → P.A)   (g₁ : (b : β) → (P.drop.B (g₀ b)).Arrow α) (g₂ : (b : β) → P.last
.B (g₀ b) → β) (x : β),   MvPFunctor.M.dest P (MvPFunctor.M.corec' P g₀ g₁ g₂ x)
 =     ⟨g₀ x, TypeVec.splitFun (g₁ x) (MvPFunctor.M.corec' P g₀ g₁ g₂ ∘ g₂ x)⟩
参数：P : MvPFunctor.{u} (n + 1)；g₀ : β → P.A；g₁ : (b : β) → (P.drop.B (g₀ b)).Arro
w α；g₂ : (b : β) → P.last.B (g₀ b) → β；x : β；MvPFunctor.M.corec' P g₀ g₁ g₂ x；g₁
 x；MvPFunctor.M.corec' P g₀ g₁ g₂ ∘ g₂ x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem M.dest_corec' {α : TypeVec.{u} n} {β : Type v} (g₀ : β → P.A)
    (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α) (g₂ : ∀ b : β, P.last.B (g₀ b) → β) (x : β) :
    M.dest P (M.corec' P g₀ g₁ g₂ x) = ⟨g₀ x, splitFun (g₁ x) (M.corec' P g₀ g₁ g₂ ∘ g₂ x)⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**MvPFunctor.M.dest_corec** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.M`。
形式化陈述：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n} {β : Type u} (g
 : β → ↑P (α ::: β)) (x : β),   MvPFunctor.M.dest P (MvPFunctor.M.corec P g x) =
 MvFunctor.map (TypeVec.id ::: MvPFunctor.M.corec P g) (g x)
参数：P : MvPFunctor.{u} (n + 1)；g : β → ↑P (α ::: β)；x : β；MvPFunctor.M.corec P g 
x；TypeVec.id ::: MvPFunctor.M.corec P g；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPFunctor.M.dest_corec'`：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : Ty
peVec.{u} n} {β : Type v} (g₀ : β → P.A)   (g₁ : (b : β) → (P.drop.B (g₀ b)).Arr
ow α) (g₂ : (b…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPFunctor.map_eq`：map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P
.B a ⟹ α) : @MvFunctor.map _ P.Obj _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TypeVec.split_dropFun_lastFun`：split_dropFun_lastFun {α α' : TypeVec (n 
+ 1)} (f : α ⟹ α') : splitFun (dropFun f) (lastFun f) = f
· 使用定理 `TypeVec.appendFun_comp_splitFun`：appendFun_comp_splitFun {α γ : TypeVec 
n} {β δ : Type*} {ε : TypeVec (n + 1)} (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ) (g₀ : last
 ε -> β) (g₁ : β -> δ…
-/
theorem M.dest_corec {α : TypeVec n} {β : Type u} (g : β → P (α.append1 β)) (x : β) :
    M.dest P (M.corec P g x) = appendFun id (M.corec P g) <$$> g x := by
  trans
  · apply M.dest_corec'
  obtain ⟨a, f⟩ := g x; dsimp
  rw [MvPFunctor.map_eq]; congr
  conv_rhs => rw [← split_dropFun_lastFun f, appendFun_comp_splitFun]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**MvPFunctor.M.bisim_lemma** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.M`。
形式化陈述：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n} {a₁ : P.mp.A} {
f₁ : (P.mp.B a₁).Arrow α} {a' : P.A}   {f' : (P.B a').drop.Arrow α} {f₁' : (P.B 
a').last → P.M α},   MvPFunctor.M.dest P ⟨a₁, f₁⟩ = ⟨a', TypeVec.splitFun f' f₁'
⟩ →     ∃ g₁',       ∃ (e₁' : PFunctor.M.dest a₁ = ⟨a', g₁'⟩),         f' = MvPF
unctor.M.pathDestLeft P e₁' f₁ ∧ f₁' = fun x => ⟨g₁' x, MvPFunctor.M.pathDestRig
ht P e₁' f₁ x⟩
参数：P : MvPFunctor.{u} (n + 1)；P.mp.B a₁；P.B a'；P.B a'；e₁' : PFunctor.M.dest a₁ =
 ⟨a', g₁'⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPFunctor.M.dest_eq_dest'`：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : 
TypeVec.{u} n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}   (h : x.des
t = ⟨a, f⟩) (f' …
· 使用定理 `TypeVec.splitFun_inj`：splitFun_inj {α α' : TypeVec (n + 1)} {f f' : drop
 α ⟹ drop α'} {g g' : last α -> last α'} (H : splitFun f g = splitFun f' g') : f
 = f' ∧ g …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem M.bisim_lemma {α : TypeVec n} {a₁ : (mp P).A} {f₁ : (mp P).B a₁ ⟹ α} {a' : P.A}
    {f' : (P.B a').drop ⟹ α} {f₁' : (P.B a').last → M P α}
    (e₁ : M.dest P ⟨a₁, f₁⟩ = ⟨a', splitFun f' f₁'⟩) :
    ∃ (g₁' : _) (e₁' : PFunctor.M.dest a₁ = ⟨a', g₁'⟩),
      f' = M.pathDestLeft P e₁' f₁ ∧
        f₁' = fun x : (last P).B a' => ⟨g₁' x, M.pathDestRight P e₁' f₁ x⟩ := by
  generalize ef : @splitFun n _ (append1 α (M P α)) f' f₁' = ff at e₁
  let he₁' := PFunctor.M.dest a₁
  rcases e₁' : he₁' with ⟨a₁', g₁'⟩
  rw [M.dest_eq_dest' _ e₁'] at e₁
  cases e₁; exact ⟨_, e₁', splitFun_inj ef⟩
/-
**MvPFunctor.M.bisim** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.M`。
形式化陈述：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n} (R : P.M α → P.
M α → Prop),   (∀ (x y : P.M α),       R x y →         ∃ a f f₁ f₂,           Mv
PFunctor.M.dest P x = ⟨a, TypeVec.splitFun f f₁⟩ ∧             MvPFunctor.M.dest
 P y = ⟨a, TypeVec.splitFun f f₂⟩ ∧ ∀ (i : (P.B a).last), R (f₁ i) (f₂ i)) →    
 ∀ (x y : P.M α), R x y → x = y
参数：P : MvPFunctor.{u} (n + 1)；R : P.M α → P.M α → Prop；∀ (x y : P.M α),       R 
x y →         ∃ a f f₁ f₂,           MvPFunctor.M.dest P x = ⟨a, TypeVec.splitFu
n f f₁⟩ ∧             MvPFunctor.M.dest P y = ⟨a, TypeVec.splitFun f f₂⟩ ∧ ∀ (i 
: (P.B a).last), R (f₁ i) (f₂ i)；x y : P.M α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.M.bisim`：bisim (R : M P -> M P -> Prop) (h : forall x y, R x y 
-> exists a f f', M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ forall i, R (f i) (f'
 i)) :…
· 使用定理 `MvPFunctor.M.bisim_lemma`：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : Ty
peVec.{u} n} {a₁ : P.mp.A} {f₁ : (P.mp.B a₁).Arrow α} {a' : P.A}   {f' : (P.B a'
).drop.Arrow α…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem M.bisim {α : TypeVec n} (R : P.M α → P.M α → Prop)
    (h :
      ∀ x y,
        R x y →
          ∃ a f f₁ f₂,
            M.dest P x = ⟨a, splitFun f f₁⟩ ∧
              M.dest P y = ⟨a, splitFun f f₂⟩ ∧ ∀ i, R (f₁ i) (f₂ i))
    (x y) (r : R x y) : x = y := by
  obtain ⟨a₁, f₁⟩ := x
  obtain ⟨a₂, f₂⟩ := y
  dsimp [mp] at *
  have : a₁ = a₂ := by
    refine
      PFunctor.M.bisim (fun a₁ a₂ => ∃ x y, R x y ∧ x.1 = a₁ ∧ y.1 = a₂) ?_ _ _
        ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
    rintro _ _ ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
    rcases h _ _ r with ⟨a', f', f₁', f₂', e₁, e₂, h'⟩
    rcases M.bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩
    rcases M.bisim_lemma P e₂ with ⟨g₂', e₂', _, rfl⟩
    rw [e₁', e₂']
    exact ⟨_, _, _, rfl, rfl, fun b => ⟨_, _, h' b, rfl, rfl⟩⟩
  subst this
  congr with (i p)
  induction p with (
    obtain ⟨a', f', f₁', f₂', e₁, e₂, h''⟩ := h _ _ r
    obtain ⟨g₁', e₁', rfl, rfl⟩ := M.bisim_lemma P e₁
    obtain ⟨g₂', e₂', e₃, rfl⟩ := M.bisim_lemma P e₂
    cases h'.symm.trans e₁'
    cases h'.symm.trans e₂')
  | root x a f h' i c =>
    exact congr_fun (congr_fun e₃ i) c
  | child x a f h' i c p IH =>
    exact IH _ _ (h'' _)

set_option backward.isDefEq.respectTransparency false in
/-
**MvPFunctor.M.bisim** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.M`。
形式化陈述：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n} (R : P.M α → P.
M α → Prop),   (∀ (x y : P.M α),       R x y →         ∃ a f f₁ f₂,           Mv
PFunctor.M.dest P x = ⟨a, TypeVec.splitFun f f₁⟩ ∧             MvPFunctor.M.dest
 P y = ⟨a, TypeVec.splitFun f f₂⟩ ∧ ∀ (i : (P.B a).last), R (f₁ i) (f₂ i)) →    
 ∀ (x y : P.M α), R x y → x = y
参数：P : MvPFunctor.{u} (n + 1)；R : P.M α → P.M α → Prop；∀ (x y : P.M α),       R 
x y →         ∃ a f f₁ f₂,           MvPFunctor.M.dest P x = ⟨a, TypeVec.splitFu
n f f₁⟩ ∧             MvPFunctor.M.dest P y = ⟨a, TypeVec.splitFun f f₂⟩ ∧ ∀ (i 
: (P.B a).last), R (f₁ i) (f₂ i)；x y : P.M α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFunctor.M.bisim`：bisim (R : M P -> M P -> Prop) (h : forall x y, R x y 
-> exists a f f', M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ forall i, R (f i) (f'
 i)) :…
· 使用定理 `MvPFunctor.M.bisim_lemma`：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : Ty
peVec.{u} n} {a₁ : P.mp.A} {f₁ : (P.mp.B a₁).Arrow α} {a' : P.A}   {f' : (P.B a'
).drop.Arrow α…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem M.bisim₀ {α : TypeVec n} (R : P.M α → P.M α → Prop) (h₀ : Equivalence R)
    (h : ∀ x y, R x y → (id ::: Quot.mk R) <$$> M.dest _ x = (id ::: Quot.mk R) <$$> M.dest _ y)
    (x y) (r : R x y) : x = y := by
  apply M.bisim P R _ _ _ r
  clear r x y
  introv Hr
  specialize h _ _ Hr
  clear Hr
  revert h
  rcases M.dest P x with ⟨ax, fx⟩
  rcases M.dest P y with ⟨ay, fy⟩
  intro h
  rw [map_eq, map_eq] at h
  injection h with h₀ h₁
  subst ay
  simp only [heq_eq_eq] at h₁
  have Hdrop : dropFun fx = dropFun fy := by
    replace h₁ := congr_arg dropFun h₁
    simpa using! h₁
  exists ax, dropFun fx, lastFun fx, lastFun fy
  rw [split_dropFun_lastFun, Hdrop, split_dropFun_lastFun]
  simp only [true_and]
  intro i
  replace h₁ := congr_fun (congr_fun h₁ Fin2.fz) i
  simp only [TypeVec.comp, appendFun, splitFun] at h₁
  replace h₁ := Quot.eqvGen_exact h₁
  rw [h₀.eqvGen_iff] at h₁
  exact h₁
/-
**MvPFunctor.M.bisim'** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.M`。
形式化陈述：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n} (R : P.M α → P.
M α → Prop),   (∀ (x y : P.M α),       R x y →         MvFunctor.map (TypeVec.id
 ::: Quot.mk R) (MvPFunctor.M.dest P x) =           MvFunctor.map (TypeVec.id ::
: Quot.mk R) (MvPFunctor.M.dest P y)) →     ∀ (x y : P.M α), R x y → x = y
参数：P : MvPFunctor.{u} (n + 1)；R : P.M α → P.M α → Prop；∀ (x y : P.M α),       R 
x y →         MvFunctor.map (TypeVec.id ::: Quot.mk R) (MvPFunctor.M.dest P x) =
           MvFunctor.map (TypeVec.id ::: Quot.mk R) (MvPFunctor.M.dest P y)；x y 
: P.M α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPFunctor.M.bisim₀`：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec
.{u} n} (R : P.M α → P.M α → Prop),   Equivalence R →     (∀ (x y : P.M α),     
    R x y…
· 使用定理 `Relation.EqvGen.is_equivalence`：is_equivalence : Equivalence (@EqvGen α 
r)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quot.factor_mk_eq`：factor_mk_eq {α : Type*} (r s : α -> α -> Prop) (h : 
forall x y, r x y -> s x y) : factor r s h ∘ Quot.mk _ = Quot.mk _
· 使用定理 `TypeVec.appendFun_comp_id`：appendFun_comp_id {α : TypeVec n} {β₀ β₁ β₂ :
 Type u} (g₀ : β₀ -> β₁) (g₁ : β₁ -> β₂) : (@id _ α ::: g₁ ∘ g₀) = (id ::: g₁) ⊚
 (id ::: g₀)
· 使用定理 `MvFunctor.map_map`：map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) : h < > g <
 > x = (h ⊚ g) < > x
· 使用定理 `MvPFunctor.instLawfulMvFunctorObj`：∀ {n : ℕ} (P : MvPFunctor.{u} n), Law
fulMvFunctor ↑P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem M.bisim' {α : TypeVec n} (R : P.M α → P.M α → Prop)
    (h : ∀ x y, R x y → (id ::: Quot.mk R) <$$> M.dest _ x = (id ::: Quot.mk R) <$$> M.dest _ y)
    (x y) (r : R x y) : x = y := by
  have := M.bisim₀ P (Relation.EqvGen R) ?_ ?_
  · solve_by_elim [Relation.EqvGen.rel]
  · apply Relation.EqvGen.is_equivalence
  · clear r x y
    introv Hr
    have : ∀ x y, R x y → Relation.EqvGen R x y := @Relation.EqvGen.rel _ R
    induction Hr
    · rw [← Quot.factor_mk_eq R (Relation.EqvGen R) this]
      rwa [appendFun_comp_id, ← MvFunctor.map_map, ← MvFunctor.map_map, h]
    all_goals simp_all

set_option backward.isDefEq.respectTransparency false in
/-
**MvPFunctor.M.dest_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.M`。
形式化陈述：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α β : TypeVec.{u} n} (g : α.Arrow 
β) (x : P.M α),   MvPFunctor.M.dest P (MvFunctor.map g x) = MvFunctor.map (g :::
 fun x => MvFunctor.map g x) (MvPFunctor.M.dest P x)
参数：P : MvPFunctor.{u} (n + 1)；g : α.Arrow β；x : P.M α；MvFunctor.map g x；g ::: fu
n x => MvFunctor.map g x；MvPFunctor.M.dest P x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPFunctor.map_eq`：map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P
.B a ⟹ α) : @MvFunctor.map _ P.Obj _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPFunctor.M.dest.eq_1`：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : Type
Vec.{u} n} (x : P.M α),   MvPFunctor.M.dest P x = MvPFunctor.M.dest' P ⋯ x.snd
· 使用定理 `MvPFunctor.M.dest'.eq_1`：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : Typ
eVec.{u} n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}   (h : x.dest =
 ⟨a, f⟩) (f' …
· 使用定理 `TypeVec.appendFun_comp_splitFun`：appendFun_comp_splitFun {α γ : TypeVec 
n} {β δ : Type*} {ε : TypeVec (n + 1)} (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ) (g₀ : last
 ε -> β) (g₁ : β -> δ…
-/
theorem M.dest_map {α β : TypeVec n} (g : α ⟹ β) (x : P.M α) :
    M.dest P (g <$$> x) = (appendFun g fun x => g <$$> x) <$$> M.dest P x := by
  obtain ⟨a, f⟩ := x
  rw [map_eq]
  conv =>
    rhs
    rw [M.dest, M.dest', map_eq, appendFun_comp_splitFun]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**MvPFunctor.M.map_dest** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.M`。
形式化陈述：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α β : TypeVec.{u} n} (g : (α ::: P
.M α).Arrow (β ::: P.M β)) (x : P.M α),   (∀ (x : P.M α), TypeVec.lastFun g x = 
MvFunctor.map (TypeVec.dropFun g) x) →     MvFunctor.map g (MvPFunctor.M.dest P 
x) = MvPFunctor.M.dest P (MvFunctor.map (TypeVec.dropFun g) x)
参数：P : MvPFunctor.{u} (n + 1)；g : (α ::: P.M α).Arrow (β ::: P.M β)；x : P.M α；∀ 
(x : P.M α), TypeVec.lastFun g x = MvFunctor.map (TypeVec.dropFun g) x；MvPFuncto
r.M.dest P x；MvFunctor.map (TypeVec.dropFun g) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPFunctor.M.dest_map`：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α β : Typ
eVec.{u} n} (g : α.Arrow β) (x : P.M α),   MvPFunctor.M.dest P (MvFunctor.map g 
x) = MvFunc…
· 使用定理 `TypeVec.eq_of_drop_last_eq`：eq_of_drop_last_eq {α β : TypeVec (n + 1)} {
f g : α ⟹ β} (h₀ : dropFun f = dropFun g) (h₁ : lastFun f = lastFun g) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem M.map_dest {α β : TypeVec n} (g : (α ::: P.M α) ⟹ (β ::: P.M β)) (x : P.M α)
    (h : ∀ x : P.M α, lastFun g x = (dropFun g <$$> x : P.M β)) :
    g <$$> M.dest P x = M.dest P (dropFun g <$$> x) := by
  rw [M.dest_map]; congr
  apply eq_of_drop_last_eq (by simp)
  simp only [lastFun_appendFun]
  ext1; apply h

end MvPFunctor

