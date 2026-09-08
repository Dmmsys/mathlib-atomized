/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
module

public import Mathlib.Util.AtomM.Recurse
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.TryThis
public meta import Mathlib.Util.AtomM.Recurse

/-!
# The `abel` tactic

Evaluate expressions in the language of additive, commutative monoids and groups.

## Future work

* In mathlib 3, `abel` accepted additional optional arguments:
  ```
  syntax "abel" (&" raw" <|> &" term")? (location)? : tactic
  ```
  It is undecided whether these features should be restored eventually.

-/

public section

-- TODO: assert_not_exists NonUnitalNonAssociativeSemiring
assert_not_exists IsOrderedMonoid TopologicalSpace PseudoMetricSpace

namespace Mathlib.Tactic.Abel

/-- A type synonym used by `abel` to represent `n • x + a` in an additive commutative monoid. -/
/-
**Mathlib.Tactic.Abel.term** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：{α : Type u_1} → [AddCommMonoid α] → ℕ → α → α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym used by `abel` to represent `n • x + a` in an additive commutativ
e monoid.
-/
@[expose] def term {α} [AddCommMonoid α] (n : ℕ) (x a : α) : α := n • x + a
/-- A type synonym used by `abel` to represent `n • x + a` in an additive commutative group. -/
/-
**Mathlib.Tactic.Abel.termg** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：{α : Type u_1} → [AddCommGroup α] → ℤ → α → α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym used by `abel` to represent `n • x + a` in an additive commutativ
e group.
-/
@[expose] def termg {α} [AddCommGroup α] (n : ℤ) (x a : α) : α := n • x + a

/-- A synonym for `•`, used internally in `abel`. -/
/-
**Mathlib.Tactic.Abel.smul** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：{α : Type u_1} → [AddCommMonoid α] → ℕ → α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A synonym for `•`, used internally in `abel`.
-/
@[expose] def smul {α} [AddCommMonoid α] (n : ℕ) (x : α) : α := n • x
/-- A synonym for `•`, used internally in `abel`. -/
/-
**Mathlib.Tactic.Abel.smulg** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：{α : Type u_1} → [AddCommGroup α] → ℤ → α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A synonym for `•`, used internally in `abel`.
-/
@[expose] def smulg {α} [AddCommGroup α] (n : ℤ) (x : α) : α := n • x

meta section

open Lean Elab Meta Tactic Qq

initialize registerTraceClass `abel
initialize registerTraceClass `abel.detail

/--
`abel` solves equations in the language of *additive*, commutative monoids and groups.

`abel` and its variants work as both tactics and conv tactics.

* `abel1` fails if the target is not an equality that is provable by the axioms of
  commutative monoids/groups.
* `abel_nf` rewrites all group expressions into a normal form.
  * `abel_nf at h` rewrites in a hypothesis.
  * `abel_nf (config := cfg)` allows for additional configuration:
    * `red`: the reducibility setting (overridden by `!`).
    * `zetaDelta`: if true, local `let` variables can be unfolded (overridden by `!`).
    * `recursive`: if true, `abel_nf` also recurses into atoms.
* `abel!`, `abel1!`, `abel_nf!` use a more aggressive reducibility setting to identify atoms.

Examples:
```
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```
-/
syntax (name := abel) "abel" "!"? : tactic

/-- The `Context` for a call to `abel`.

Stores a few options for this call, and caches some common subexpressions
such as typeclass instances and `0 : α`.
-/
/-
**Mathlib.Tactic.Abel.Context** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Context` for a call to `abel`.

Stores a few options for this call, and caches some common subexpressions
such as typeclass instances and `0 : α`.
-/
structure Context where
  /-- The type of the ambient additive commutative group or monoid. -/
  α : Expr
  /-- The universe level for `α`. -/
  univ : Level
  /-- The expression representing `0 : α`. -/
  α0 : Expr
  /-- Specify whether we are in an additive commutative group or an additive commutative monoid. -/
  isGroup : Bool
  /-- The `AddCommGroup α` or `AddCommMonoid α` expression. -/
  inst : Expr

/-- Populate a `context` object for evaluating `e`. -/
/-
**Mathlib.Tactic.Abel.mkContext** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：mkContext (e : Expr) : MetaM Context
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Populate a `context` object for evaluating `e`.
-/
def mkContext (e : Expr) : MetaM Context := do
  let α ← inferType e
  let c ← synthInstance (← mkAppM ``AddCommMonoid #[α])
  let cg ← synthInstance? (← mkAppM ``AddCommGroup #[α])
  let u ← mkFreshLevelMVar
  _ ← isDefEq (.sort (.succ u)) (← inferType α)
  let α0 ← Expr.ofNat α 0
  match cg with
  | some cg => return ⟨α, u, α0, true, cg⟩
  | _ => return ⟨α, u, α0, false, c⟩

/-- The monad for `Abel` contains, in addition to the `AtomM` state,
some information about the current type we are working over, so that we can consistently
use group lemmas or monoid lemmas as appropriate. -/
/-
**Mathlib.Tactic.Abel.M** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monad for `Abel` contains, in addition to the `AtomM` state,
some information about the current type we are working over, so that we can cons
istently
use group lemmas or monoid lemmas as appropriate.
-/
abbrev M := ReaderT Context AtomM

/-- Apply the function `n : ∀ {α} [inst : AddWhatever α], _` to the
implicit parameters in the context, and the given list of arguments. -/
/-
**Mathlib.Tactic.Abel.Context.app** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel
.Context`。
形式化陈述：Mathlib.Tactic.Abel.Context → Name → Expr → Array Expr → Expr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply the function `n : ∀ {α} [inst : AddWhatever α], _` to the
implicit parameters in the context, and the given list of arguments.
-/
def Context.app (c : Context) (n : Name) (inst : Expr) : Array Expr → Expr :=
  mkAppN (((@Expr.const n [c.univ]).app c.α).app inst)

/-- Apply the function `n : ∀ {α} [inst α], _` to the implicit parameters in the
context, and the given list of arguments.

Compared to `context.app`, this takes the name of the typeclass, rather than an
inferred typeclass instance.
-/
/-
**Mathlib.Tactic.Abel.Context.mkApp** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Ab
el.Context`。
形式化陈述：Mathlib.Tactic.Abel.Context → Name → Name → Array Expr → MetaM Expr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply the function `n : ∀ {α} [inst α], _` to the implicit parameters in the
context, and the given list of arguments.

Compared to `context.app`, this takes the name of the typeclass, rather than an
inferred typeclass instance.
-/
def Context.mkApp (c : Context) (n inst : Name) (l : Array Expr) : MetaM Expr := do
  return c.app n (← synthInstance ((Expr.const inst [c.univ]).app c.α)) l

/-- Add the letter "g" to the end of the name, e.g. turning `term` into `termg`.

This is used to choose between declarations taking `AddCommMonoid` and those
taking `AddCommGroup` instances.
-/
/-
**Mathlib.Tactic.Abel.addG** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：Name → Name
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Add the letter "g" to the end of the name, e.g. turning `term` into `termg`.

This is used to choose between declarations taking `AddCommMonoid` and those
taking `AddCommGroup` instances.
-/
def addG : Name → Name
  | .str p s => .str p (s ++ "g")
  | n => n

/-- Apply the function `n : ∀ {α} [AddComm{Monoid,Group} α]` to the given list of arguments.

Will use the `AddComm{Monoid,Group}` instance that has been cached in the context.
-/
/-
**Mathlib.Tactic.Abel.iapp** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：iapp (n : Name) (xs : Array Expr) : M Expr
参数：n : Name；xs : Array Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply the function `n : ∀ {α} [AddComm{Monoid,Group} α]` to the given list of ar
guments.

Will use the `AddComm{Monoid,Group}` instance that has been cached in the contex
t.
-/
def iapp (n : Name) (xs : Array Expr) : M Expr := do
  let c ← read
  return c.app (if c.isGroup then addG n else n) c.inst xs

/-- Evaluate a term with coefficient `n`, atom `x` and successor terms `a`. -/
/-
**Mathlib.Tactic.Abel.mkTerm** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：mkTerm (n x a : Expr) : M Expr
参数：n x a : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate a term with coefficient `n`, atom `x` and successor terms `a`.
-/
def mkTerm (n x a : Expr) : M Expr := iapp ``term #[n, x, a]

/-- Interpret an integer as a coefficient to a term. -/
/-
**Mathlib.Tactic.Abel.intToExpr** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：intToExpr (n : Int) : M Expr
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret an integer as a coefficient to a term.
-/
def intToExpr (n : ℤ) : M Expr := do
  Expr.ofInt (mkConst (if (← read).isGroup then ``Int else ``Nat) []) n

/-- A normal form for `abel`.
Expressions are represented as a list of terms of the form `e = n • x`,
where `n : ℤ` and `x` is an arbitrary element of the additive commutative monoid or group.
We explicitly track the `Expr` forms of `e` and `n`, even though they could be reconstructed,
for efficiency. -/
/-
**Mathlib.Tactic.Abel.NormalExpr** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.Abe
l`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normal form for `abel`.
Expressions are represented as a list of terms of the form `e = n • x`,
where `n : ℤ` and `x` is an arbitrary element of the additive commutative monoid
 or group.
We explicitly track the `Expr` forms of `e` and `n`, even though they could be r
econstructed,
for efficiency.
-/
inductive NormalExpr : Type
  | zero (e : Expr) : NormalExpr
  | nterm (e : Expr) (n : Expr × ℤ) (x : ℕ × Expr) (a : NormalExpr) : NormalExpr
  deriving Inhabited

/-- Extract the expression from a normal form. -/
/-
**Mathlib.Tactic.Abel.NormalExpr.e** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abe
l.NormalExpr`。
形式化陈述：Mathlib.Tactic.Abel.NormalExpr → Expr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the expression from a normal form.
-/
def NormalExpr.e : NormalExpr → Expr
  | .zero e => e
  | .nterm e .. => e
/-
**Mathlib.Tactic.Abel.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Abel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe NormalExpr Expr where coe := NormalExpr.e

/-- Construct the normal form representing a single term. -/
/-
**Mathlib.Tactic.Abel.NormalExpr.term'** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic
.Abel.NormalExpr`。
形式化陈述：Expr × ℤ → ℕ × Expr → Mathlib.Tactic.Abel.NormalExpr → Mathlib.Tactic.Abel
.M Mathlib.Tactic.Abel.NormalExpr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the normal form representing a single term.
-/
def NormalExpr.term' (n : Expr × ℤ) (x : ℕ × Expr) (a : NormalExpr) : M NormalExpr :=
  return .nterm (← mkTerm n.1 x.2 a) n x a

/-- Construct the normal form representing zero. -/
/-
**Mathlib.Tactic.Abel.NormalExpr.zero'** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic
.Abel.NormalExpr`。
形式化陈述：Mathlib.Tactic.Abel.M Mathlib.Tactic.Abel.NormalExpr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the normal form representing zero.
-/
def NormalExpr.zero' : M NormalExpr := return NormalExpr.zero (← read).α0

open NormalExpr
/-
**Mathlib.Tactic.Abel.const_add_term** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.A
bel`。
形式化陈述：const_add_term {α} [AddCommMonoid α] (k n x a a') (h : k + a = a') : k + @
term α _ n x a = term n x a'
参数：k n x a a'；h : k + a = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem const_add_term {α} [AddCommMonoid α] (k n x a a') (h : k + a = a') :
    k + @term α _ n x a = term n x a' := by
  simp [h.symm, term, add_comm, add_assoc]
/-
**Mathlib.Tactic.Abel.const_add_termg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Abel`。
形式化陈述：const_add_termg {α} [AddCommGroup α] (k n x a a') (h : k + a = a') : k + @
termg α _ n x a = termg n x a'
参数：k n x a a'；h : k + a = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem const_add_termg {α} [AddCommGroup α] (k n x a a') (h : k + a = a') :
    k + @termg α _ n x a = termg n x a' := by
  simp [h.symm, termg, add_comm, add_assoc]
/-
**Mathlib.Tactic.Abel.term_add_const** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.A
bel`。
形式化陈述：term_add_const {α} [AddCommMonoid α] (n x a k a') (h : a + k = a') : @term
 α _ n x a + k = term n x a'
参数：n x a k a'；h : a + k = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem term_add_const {α} [AddCommMonoid α] (n x a k a') (h : a + k = a') :
    @term α _ n x a + k = term n x a' := by
  simp [h.symm, term, add_assoc]
/-
**Mathlib.Tactic.Abel.term_add_constg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Abel`。
形式化陈述：term_add_constg {α} [AddCommGroup α] (n x a k a') (h : a + k = a') : @term
g α _ n x a + k = termg n x a'
参数：n x a k a'；h : a + k = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem term_add_constg {α} [AddCommGroup α] (n x a k a') (h : a + k = a') :
    @termg α _ n x a + k = termg n x a' := by
  simp [h.symm, termg, add_assoc]
/-
**Mathlib.Tactic.Abel.term_add_term** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ab
el`。
形式化陈述：term_add_term {α} [AddCommMonoid α] (n₁ x a₁ n₂ a₂ n' a') (h₁ : n₁ + n₂ = 
n') (h₂ : a₁ + a₂ = a') : @term α _ n₁ x a₁ + @term α _ n₂ x a₂ = term n' x a'
参数：n₁ x a₁ n₂ a₂ n' a'；h₁ : n₁ + n₂ = n'；h₂ : a₁ + a₂ = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m +
 n) • a = m • a + n • a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem term_add_term {α} [AddCommMonoid α] (n₁ x a₁ n₂ a₂ n' a') (h₁ : n₁ + n₂ = n')
    (h₂ : a₁ + a₂ = a') : @term α _ n₁ x a₁ + @term α _ n₂ x a₂ = term n' x a' := by
  simp [h₁.symm, h₂.symm, term, add_nsmul, add_assoc, add_left_comm]
/-
**Mathlib.Tactic.Abel.term_add_termg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.A
bel`。
形式化陈述：term_add_termg {α} [AddCommGroup α] (n₁ x a₁ n₂ a₂ n' a') (h₁ : n₁ + n₂ = 
n') (h₂ : a₁ + a₂ = a') : @termg α _ n₁ x a₁ + @termg α _ n₂ x a₂ = termg n' x a
'
参数：n₁ x a₁ n₂ a₂ n' a'；h₁ : n₁ + n₂ = n'；h₂ : a₁ + a₂ = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (m n : ℤ), (m + 
n) • a = m • a + n • a
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
-/
theorem term_add_termg {α} [AddCommGroup α] (n₁ x a₁ n₂ a₂ n' a')
    (h₁ : n₁ + n₂ = n') (h₂ : a₁ + a₂ = a') :
    @termg α _ n₁ x a₁ + @termg α _ n₂ x a₂ = termg n' x a' := by
  simp only [termg, h₁.symm, add_zsmul, h₂.symm]
  exact add_add_add_comm (n₁ • x) a₁ (n₂ • x) a₂
/-
**Mathlib.Tactic.Abel.zero_term** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：zero_term {α} [AddCommMonoid α] (x a) : @term α _ 0 x a = a
参数：x a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_term {α} [AddCommMonoid α] (x a) : @term α _ 0 x a = a := by
  simp [term, zero_nsmul]
/-
**Mathlib.Tactic.Abel.zero_termg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abel`
。
形式化陈述：zero_termg {α} [AddCommGroup α] (x a) : @termg α _ 0 x a = a
参数：x a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 • a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_termg {α} [AddCommGroup α] (x a) : @termg α _ 0 x a = a := by
  simp [termg, zero_zsmul]

/--
Interpret the sum of two expressions in `abel`'s normal form.
-/
/-
**Mathlib.Tactic.Abel.evalAdd** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Tactic.Abel`
。
形式化陈述：Mathlib.Tactic.Abel.NormalExpr →   Mathlib.Tactic.Abel.NormalExpr → Mathli
b.Tactic.Abel.M (Mathlib.Tactic.Abel.NormalExpr × Expr)
参数：Mathlib.Tactic.Abel.NormalExpr × Expr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret the sum of two expressions in `abel`'s normal form.
-/
partial def evalAdd : NormalExpr → NormalExpr → M (NormalExpr × Expr)
  | zero _, e₂ => do
    let p ← mkAppM ``zero_add #[e₂]
    return (e₂, p)
  | e₁, zero _ => do
    let p ← mkAppM ``add_zero #[e₁]
    return (e₁, p)
  | he₁@(nterm e₁ n₁ x₁ a₁), he₂@(nterm e₂ n₂ x₂ a₂) => do
    if x₁.1 = x₂.1 then
      let n' ← Mathlib.Meta.NormNum.eval (← mkAppM ``HAdd.hAdd #[n₁.1, n₂.1])
      let (a', h₂) ← evalAdd a₁ a₂
      let k := n₁.2 + n₂.2
      let p₁ ← iapp ``term_add_term
        #[n₁.1, x₁.2, a₁, n₂.1, a₂, n'.expr, a', ← n'.getProof, h₂]
      if k = 0 then do
        let p ← mkEqTrans p₁ (← iapp ``zero_term #[x₁.2, a'])
        return (a', p)
      else return (← term' (n'.expr, k) x₁ a', p₁)
    else if x₁.1 < x₂.1 then do
      let (a', h) ← evalAdd a₁ he₂
      return (← term' n₁ x₁ a', ← iapp ``term_add_const #[n₁.1, x₁.2, a₁, e₂, a', h])
    else do
      let (a', h) ← evalAdd he₁ a₂
      return (← term' n₂ x₂ a', ← iapp ``const_add_term #[e₁, n₂.1, x₂.2, a₂, a', h])
/-
**Mathlib.Tactic.Abel.term_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：term_neg {α} [AddCommGroup α] (n x a n' a') (h₁ : -n = n') (h₂ : -a = a') 
: -@termg α _ n x a = termg n' x a'
参数：n x a n' a'；h₁ : -n = n'；h₂ : -a = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ)
, -n • a = -(n • a)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem term_neg {α} [AddCommGroup α] (n x a n' a')
    (h₁ : -n = n') (h₂ : -a = a') : -@termg α _ n x a = termg n' x a' := by
  simpa [h₂.symm, h₁.symm, termg] using add_comm _ _

/--
Interpret a negated expression in `abel`'s normal form.
-/
/-
**Mathlib.Tactic.Abel.evalNeg** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：Mathlib.Tactic.Abel.NormalExpr → Mathlib.Tactic.Abel.M (Mathlib.Tactic.Abe
l.NormalExpr × Expr)
参数：Mathlib.Tactic.Abel.NormalExpr × Expr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a negated expression in `abel`'s normal form.
-/
def evalNeg : NormalExpr → M (NormalExpr × Expr)
  | (zero _) => do
    let p ← (← read).mkApp ``neg_zero ``NegZeroClass #[]
    return (← zero', p)
  | (nterm _ n x a) => do
    let n' ← Mathlib.Meta.NormNum.eval (← mkAppM ``Neg.neg #[n.1])
    let (a', h₂) ← evalNeg a
    return (← term' (n'.expr, -n.2) x a',
      (← read).app ``term_neg (← read).inst #[n.1, x.2, a, n'.expr, a', ← n'.getProof, h₂])
/-
**Mathlib.Tactic.Abel.zero_smul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：zero_smul {α} [AddCommMonoid α] (c) : smul c (0 : α) = 0
参数：c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_smul {α} [AddCommMonoid α] (c) : smul c (0 : α) = 0 := by
  simp [smul, nsmul_zero]
/-
**Mathlib.Tactic.Abel.zero_smulg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abel`
。
形式化陈述：zero_smulg {α} [AddCommGroup α] (c) : smulg c (0 : α) = 0
参数：c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (n : ℤ), n • 0
 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_smulg {α} [AddCommGroup α] (c) : smulg c (0 : α) = 0 := by
  simp [smulg, zsmul_zero]
/-
**Mathlib.Tactic.Abel.term_smul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：term_smul {α} [AddCommMonoid α] (c n x a n' a') (h₁ : c * n = n') (h₂ : sm
ul c a = a') : smul c (@term α _ n x a) = term n' x a'
参数：c n x a n' a'；h₁ : c * n = n'；h₂ : smul c a = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_add`：∀ {M : Type u_4} [inst : AddCommMonoid M] (a b : M) (n : ℕ), 
n • (a + b) = n • a + n • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_nsmul'`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m 
* n) • a = m • n • a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem term_smul {α} [AddCommMonoid α] (c n x a n' a')
    (h₁ : c * n = n') (h₂ : smul c a = a') :
    smul c (@term α _ n x a) = term n' x a' := by
  simp [h₂.symm, h₁.symm, term, smul, nsmul_add, mul_nsmul']
/-
**Mathlib.Tactic.Abel.term_smulg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abel`
。
形式化陈述：term_smulg {α} [AddCommGroup α] (c n x a n' a') (h₁ : c * n = n') (h₂ : sm
ulg c a = a') : smulg c (@termg α _ n x a) = termg n' x a'
参数：c n x a n' a'；h₁ : c * n = n'；h₂ : smulg c a = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α) (
n : ℤ), n • (a + b) = n • a + n • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (m n : 
ℤ), (m * n) • a = m • n • a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem term_smulg {α} [AddCommGroup α] (c n x a n' a')
    (h₁ : c * n = n') (h₂ : smulg c a = a') :
    smulg c (@termg α _ n x a) = termg n' x a' := by
  simp [h₂.symm, h₁.symm, termg, smulg, zsmul_add, mul_zsmul]

/--
Auxiliary function for `evalSMul'`.
-/
/-
**Mathlib.Tactic.Abel.evalSMul** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：Expr × ℤ → Mathlib.Tactic.Abel.NormalExpr → Mathlib.Tactic.Abel.M (Mathlib
.Tactic.Abel.NormalExpr × Expr)
参数：Mathlib.Tactic.Abel.NormalExpr × Expr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function for `evalSMul'`.
-/
def evalSMul (k : Expr × ℤ) : NormalExpr → M (NormalExpr × Expr)
  | zero _ => return (← zero', ← iapp ``zero_smul #[k.1])
  | nterm _ n x a => do
    let n' ← Mathlib.Meta.NormNum.eval (← mkAppM ``HMul.hMul #[k.1, n.1])
    let (a', h₂) ← evalSMul k a
    return (← term' (n'.expr, k.2 * n.2) x a',
      ← iapp ``term_smul #[k.1, n.1, x.2, a, n'.expr, a', ← n'.getProof, h₂])
/-
**Mathlib.Tactic.Abel.term_atom** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：term_atom {α} [AddCommMonoid α] (x : α) : x = term 1 x 0
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 1 • a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem term_atom {α} [AddCommMonoid α] (x : α) : x = term 1 x 0 := by simp [term, one_nsmul]
/-
**Mathlib.Tactic.Abel.term_atomg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abel`
。
形式化陈述：term_atomg {α} [AddCommGroup α] (x : α) : x = termg 1 x 0
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem term_atomg {α} [AddCommGroup α] (x : α) : x = termg 1 x 0 := by simp [termg]
/-
**Mathlib.Tactic.Abel.term_atom_pf** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abe
l`。
形式化陈述：term_atom_pf {α} [AddCommMonoid α] (x x' : α) (h : x = x') : x = term 1 x'
 0
参数：x x' : α；h : x = x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 1 • a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem term_atom_pf {α} [AddCommMonoid α] (x x' : α) (h : x = x') : x = term 1 x' 0 := by
  simp [term, h, one_nsmul]
/-
**Mathlib.Tactic.Abel.term_atom_pfg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ab
el`。
形式化陈述：term_atom_pfg {α} [AddCommGroup α] (x x' : α) (h : x = x') : x = termg 1 x
' 0
参数：x x' : α；h : x = x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem term_atom_pfg {α} [AddCommGroup α] (x x' : α) (h : x = x') : x = termg 1 x' 0 := by
  simp [termg, h]

/-- Interpret an expression as an atom for `abel`'s normal form. -/
/-
**Mathlib.Tactic.Abel.evalAtom** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：evalAtom (e : Expr) : M (NormalExpr × Expr)
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret an expression as an atom for `abel`'s normal form.
-/
def evalAtom (e : Expr) : M (NormalExpr × Expr) := do
  let { expr := e', proof?, .. } ← (← readThe AtomM.Context).evalAtom e
  let (i, a) ← AtomM.addAtom e'
  let p ← match proof? with
  | none => iapp ``term_atom #[e]
  | some p => iapp ``term_atom_pf #[e, a, p]
  return (← term' (← intToExpr 1, 1) (i, a) (← zero'), p)
/-
**Mathlib.Tactic.Abel.unfold_sub** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abel`
。
形式化陈述：unfold_sub {α} [SubtractionMonoid α] (a b c : α) (h : a + -b = c) : a - b 
= c
参数：a b c : α；h : a + -b = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem unfold_sub {α} [SubtractionMonoid α] (a b c : α) (h : a + -b = c) : a - b = c := by
  rw [sub_eq_add_neg, h]
/-
**Mathlib.Tactic.Abel.unfold_smul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abel
`。
形式化陈述：unfold_smul {α} [AddCommMonoid α] (n) (x y : α) (h : smul n x = y) : n • x
 = y
参数：n；x y : α；h : smul n x = y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unfold_smul {α} [AddCommMonoid α] (n) (x y : α)
    (h : smul n x = y) : n • x = y := h
/-
**Mathlib.Tactic.Abel.unfold_smulg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abe
l`。
形式化陈述：unfold_smulg {α} [AddCommGroup α] (n : Nat) (x y : α) (h : smulg (Int.ofNa
t n) x = y) : (n : Int) • x = y
参数：n : Nat；x y : α；h : smulg (Int.ofNat n) x = y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unfold_smulg {α} [AddCommGroup α] (n : ℕ) (x y : α)
    (h : smulg (Int.ofNat n) x = y) : (n : ℤ) • x = y := h
/-
**Mathlib.Tactic.Abel.unfold_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abe
l`。
形式化陈述：unfold_zsmul {α} [AddCommGroup α] (n : Int) (x y : α) (h : smulg n x = y) 
: n • x = y
参数：n : Int；x y : α；h : smulg n x = y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unfold_zsmul {α} [AddCommGroup α] (n : ℤ) (x y : α)
    (h : smulg n x = y) : n • x = y := h
/-
**Mathlib.Tactic.Abel.subst_into_smul** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.
Abel`。
形式化陈述：subst_into_smul {α} [AddCommMonoid α] (l r tl tr t) (prl : l = tl) (prr : 
r = tr) (prt : @smul α _ tl tr = t) : smul l r = t
参数：l r tl tr t；prl : l = tl；prr : r = tr；prt : @smul α _ tl tr = t。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma subst_into_smul {α} [AddCommMonoid α]
    (l r tl tr t) (prl : l = tl) (prr : r = tr)
    (prt : @smul α _ tl tr = t) : smul l r = t := by simp [prl, prr, prt]
/-
**Mathlib.Tactic.Abel.subst_into_smulg** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic
.Abel`。
形式化陈述：subst_into_smulg {α} [AddCommGroup α] (l r tl tr t) (prl : l = tl) (prr : 
r = tr) (prt : @smulg α _ tl tr = t) : smulg l r = t
参数：l r tl tr t；prl : l = tl；prr : r = tr；prt : @smulg α _ tl tr = t。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma subst_into_smulg {α} [AddCommGroup α]
    (l r tl tr t) (prl : l = tl) (prr : r = tr)
    (prt : @smulg α _ tl tr = t) : smulg l r = t := by simp [prl, prr, prt]
/-
**Mathlib.Tactic.Abel.subst_into_smul_upcast** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.
Tactic.Abel`。
形式化陈述：subst_into_smul_upcast {α} [AddCommGroup α] (l r tl zl tr t) (prl₁ : l = t
l) (prl₂ : ↑tl = zl) (prr : r = tr) (prt : @smulg α _ zl tr = t) : smul l r = t
参数：l r tl zl tr t；prl₁ : l = tl；prl₂ : ↑tl = zl；prr : r = tr；prt : @smulg α _ zl
 tr = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma subst_into_smul_upcast {α} [AddCommGroup α]
    (l r tl zl tr t) (prl₁ : l = tl) (prl₂ : ↑tl = zl) (prr : r = tr)
    (prt : @smulg α _ zl tr = t) : smul l r = t := by
  simp [← prt, prl₁, ← prl₂, prr, smul, smulg, natCast_zsmul]
/-
**Mathlib.Tactic.Abel.subst_into_add** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.A
bel`。
形式化陈述：subst_into_add {α} [AddCommMonoid α] (l r tl tr t) (prl : (l : α) = tl) (p
rr : r = tr) (prt : tl + tr = t) : l + r = t
参数：l r tl tr t；prl : (l : α) = tl；prr : r = tr；prt : tl + tr = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma subst_into_add {α} [AddCommMonoid α] (l r tl tr t)
    (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t := by
  rw [prl, prr, prt]
/-
**Mathlib.Tactic.Abel.subst_into_addg** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.
Abel`。
形式化陈述：subst_into_addg {α} [AddCommGroup α] (l r tl tr t) (prl : (l : α) = tl) (p
rr : r = tr) (prt : tl + tr = t) : l + r = t
参数：l r tl tr t；prl : (l : α) = tl；prr : r = tr；prt : tl + tr = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma subst_into_addg {α} [AddCommGroup α] (l r tl tr t)
    (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t := by
  rw [prl, prr, prt]
/-
**Mathlib.Tactic.Abel.subst_into_negg** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.
Abel`。
形式化陈述：subst_into_negg {α} [AddCommGroup α] (a ta t : α) (pra : a = ta) (prt : -t
a = t) : -a = t
参数：a ta t : α；pra : a = ta；prt : -ta = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma subst_into_negg {α} [AddCommGroup α] (a ta t : α)
    (pra : a = ta) (prt : -ta = t) : -a = t := by
  simp [pra, prt]

/-- Normalize a term `orig` of the form `smul e₁ e₂` or `smulg e₁ e₂`.
  Normalized terms use `smul` for monoids and `smulg` for groups,
  so there are actually four cases to handle:
  * Using `smul` in a monoid just simplifies the pieces using `subst_into_smul`
  * Using `smulg` in a group just simplifies the pieces using `subst_into_smulg`
  * Using `smul a b` in a group requires converting `a` from a nat to an int and
    then simplifying `smulg ↑a b` using `subst_into_smul_upcast`
  * Using `smulg` in a monoid is impossible (or at least out of scope),
    because you need a group argument to write a `smulg` term -/
/-
**Mathlib.Tactic.Abel.evalSMul'** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：evalSMul' (eval : Expr -> M (NormalExpr × Expr)) (is_smulg : Bool) (orig e
₁ e₂ : Expr) : M (NormalExpr × Expr)
参数：eval : Expr -> M (NormalExpr × Expr)；is_smulg : Bool；orig e₁ e₂ : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normalize a term `orig` of the form `smul e₁ e₂` or `smulg e₁ e₂`.
  Normalized terms use `smul` for monoids and `smulg` for groups,
  so there are actually four cases to handle:
  * Using `smul` in a monoid just simplifies the pieces using `subst_into_smul`
  * Using `smulg` in a group just simplifies the pieces using `subst_into_smulg`
  * Using `smul a b` in a group requires converting `a` from a nat to an int and
    then simplifying `smulg ↑a b` using `subst_into_smul_upcast`
  * Using `smulg` in a monoid is impossible (or at least out of scope),
    because you need a group argument to write a `smulg` term
-/
def evalSMul' (eval : Expr → M (NormalExpr × Expr))
    (is_smulg : Bool) (orig e₁ e₂ : Expr) : M (NormalExpr × Expr) := do
  trace[abel] "Calling NormNum on {e₁}"
  let ⟨e₁', p₁, _⟩ ← try Meta.NormNum.eval e₁ catch _ => pure { expr := e₁ }
  let p₁ ← p₁.getDM (mkEqRefl e₁')
  match e₁'.int? with
  | some n => do
    let c ← read
    let (e₂', p₂) ← eval e₂
    if c.isGroup = is_smulg then do
      let (e', p) ← evalSMul (e₁', n) e₂'
      return (e', ← iapp ``subst_into_smul #[e₁, e₂, e₁', e₂', e', p₁, p₂, p])
    else do
      if ¬ c.isGroup then throwError "Doesn't make sense to us `smulg` in a monoid. "
      -- We are multiplying by a natural number in an additive group.
      let zl ← Expr.ofInt q(ℤ) n
      let p₁' ← mkEqRefl zl
      let (e', p) ← evalSMul (zl, n) e₂'
      return (e', c.app ``subst_into_smul_upcast c.inst #[e₁, e₂, e₁', zl, e₂', e', p₁, p₁', p₂, p])
  | none => evalAtom orig

/-- Evaluate an expression into its `abel` normal form, by recursing into subexpressions. -/
/-
**Mathlib.Tactic.Abel.eval** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：Expr → Mathlib.Tactic.Abel.M (Mathlib.Tactic.Abel.NormalExpr × Expr)
参数：Mathlib.Tactic.Abel.NormalExpr × Expr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate an expression into its `abel` normal form, by recursing into subexpress
ions.
-/
partial def eval (e : Expr) : M (NormalExpr × Expr) := do
  trace[abel.detail] "running eval on {e}"
  trace[abel.detail] "getAppFnArgs: {e.getAppFnArgs}"
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← evalAdd e₁' e₂'
    return (e', ← iapp ``subst_into_add #[e₁, e₂, e₁', e₂', e', p₁, p₂, p'])
  | (``HSub.hSub, #[_, _, _, _, e₁, e₂]) => do
    let e₂' ← mkAppM ``Neg.neg #[e₂]
    let e ← mkAppM ``HAdd.hAdd #[e₁, e₂']
    let (e', p) ← eval e
    let p' ← (← read).mkApp ``unfold_sub ``SubtractionMonoid #[e₁, e₂, e', p]
    return (e', p')
  | (``Neg.neg, #[_, _, e]) => do
    let (e₁, p₁) ← eval e
    let (e₂, p₂) ← evalNeg e₁
    return (e₂, ← iapp `Mathlib.Tactic.Abel.subst_into_neg #[e, e₁, e₂, p₁, p₂])
  | (``NSMul.nsmul, #[_, _, e₁, e₂]) => do
    let n ← if (← read).isGroup then mkAppM ``Int.ofNat #[e₁] else pure e₁
    let (e', p) ← eval <| ← iapp ``smul #[n, e₂]
    return (e', ← iapp ``unfold_smul #[e₁, e₂, e', p])
  | (``ZSMul.zsmul, #[_, _, e₁, e₂]) => do
      if ¬ (← read).isGroup then failure
      let (e', p) ← eval <| ← iapp ``smul #[e₁, e₂]
      return (e', (← read).app ``unfold_zsmul (← read).inst #[e₁, e₂, e', p])
  | (``SMul.smul, #[.const ``Int _, _, _, e₁, e₂]) =>
    evalSMul' eval true e e₁ e₂
  | (``SMul.smul, #[.const ``Nat _, _, _, e₁, e₂]) =>
    evalSMul' eval false e e₁ e₂
  | (``HSMul.hSMul, #[.const ``Int _, _, _, _, e₁, e₂]) =>
    evalSMul' eval true e e₁ e₂
  | (``HSMul.hSMul, #[.const ``Nat _, _, _, _, e₁, e₂]) =>
    evalSMul' eval false e e₁ e₂
  | (``smul, #[_, _, e₁, e₂]) => evalSMul' eval false e e₁ e₂
  | (``smulg, #[_, _, e₁, e₂]) => evalSMul' eval true e e₁ e₂
  | (``OfNat.ofNat, #[_, .lit (.natVal 0), _])
  | (``Zero.zero, #[_, _]) =>
    if ← isDefEq e (← read).α0 then
      pure (← zero', ← mkEqRefl (← read).α0)
    else
      evalAtom e
  | _ => evalAtom e

/-- Determine whether `e` will be handled as an atom by the `abel` tactic. The `match` in this
function should be preserved to be parallel in case-matching to that in the
`Mathlib.Tactic.Abel.eval` metaprogram. -/
/-
**Mathlib.Tactic.Abel.isAtom** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：isAtom (e : Expr) : Bool
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Determine whether `e` will be handled as an atom by the `abel` tactic. The `matc
h` in this
function should be preserved to be parallel in case-matching to that in the
`Mathlib.Tactic.Abel.eval` metaprogram.
-/
def isAtom (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, _, _])
  | (``HSub.hSub, #[_, _, _, _, _, _])
  | (``Neg.neg, #[_, _, _])
  | (``NSMul.nsmul, #[_, _, _, _])
  | (``ZSMul.zsmul, #[_, _, _, _])
  | (``SMul.smul, #[.const ``Int _, _, _, _, _])
  | (``SMul.smul, #[.const ``Nat _, _, _, _, _])
  | (``HSMul.hSMul, #[.const ``Int _, _, _, _, _, _])
  | (``HSMul.hSMul, #[.const ``Nat _, _, _, _, _, _])
  | (``smul, #[_, _, _, _])
  | (``smulg, #[_, _, _, _]) => false
  /- The `OfNat.ofNat` and `Zero.zero` cases are deliberately omitted here: these two cases are not
  strictly atoms for `abel`, but they are atom-like in that their handling by
  `Mathlib.Tactic.Abel.eval` contains no recursive call. -/
  -- | (``OfNat.ofNat, #[_, .lit (.natVal 0), _])
  -- | (``Zero.zero, #[_, _])
  | _ => true

@[tactic_alt abel]
elab (name := abel1) "abel1" tk:"!"? : tactic => withMainContext do
  let tm := if tk.isSome then .default else .reducible
  let some (_, e₁, e₂) := (← whnfR <| ← getMainTarget).eq?
    | throwError "`abel1` requires an equality goal"
  trace[abel] "running on an equality `{e₁} = {e₂}`."
  let c ← mkContext e₁
  let proof ← AtomM.run tm <| ReaderT.run (r := c) do
    let (e₁', p₁) ← eval e₁
    trace[abel] "found `{p₁}`, a proof that `{e₁} = {e₁'.e}`"
    let (e₂', p₂) ← eval e₂
    trace[abel] "found `{p₂}`, a proof that `{e₂} = {e₂'.e}`"
    unless ← isDefEq e₁' e₂' do
      throwError "`abel1` found that the two sides were not equal"
    trace[abel] "verified that the simplified forms are identical"
    mkEqTrans p₁ (← mkEqSymm p₂)
  let type ← getMainTarget
  let proof ← Lean.Meta.mkAuxTheorem type proof (zetaDelta := true) (kind? := `_abel)
  closeMainGoal `abel1 proof

@[tactic_alt abel]
macro (name := abel1!) "abel1!" : tactic => `(tactic| abel1 !)
/-
**Mathlib.Tactic.Abel.term_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：term_eq {α : Type*} [AddCommMonoid α] (n : Nat) (x a : α) : term n x a = n
 • x + a
参数：n : Nat；x a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem term_eq {α : Type*} [AddCommMonoid α] (n : ℕ) (x a : α) : term n x a = n • x + a := (rfl)
/-- A type synonym used by `abel` to represent `n • x + a` in an additive commutative group. -/
/-
**Mathlib.Tactic.Abel.termg_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：termg_eq {α : Type*} [AddCommGroup α] (n : Int) (x a : α) : termg n x a = 
n • x + a
参数：n : Int；x a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym used by `abel` to represent `n • x + a` in an additive commutativ
e group.
-/
theorem termg_eq {α : Type*} [AddCommGroup α] (n : ℤ) (x a : α) : termg n x a = n • x + a := (rfl)

/-- True if this represents an atomic expression. -/
/-
**Mathlib.Tactic.Abel.NormalExpr.isAtom** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tacti
c.Abel.NormalExpr`。
形式化陈述：Mathlib.Tactic.Abel.NormalExpr → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
True if this represents an atomic expression.
-/
def NormalExpr.isAtom : NormalExpr → Bool
  | .nterm _ (_, 1) _ (.zero _) => true
  | _ => false

/-- The normalization style for `abel_nf`. -/
/-
**Mathlib.Tactic.Abel.AbelMode** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.Abel`
。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normalization style for `abel_nf`.
-/
inductive AbelMode where
  /-- The default form -/
  | term
  /-- Raw form: the representation `abel` uses internally. -/
  | raw

/-- Configuration for `abel_nf`. -/
/-
**Mathlib.Tactic.Abel.AbelNF.Config** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.
Abel.AbelNF`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Configuration for `abel_nf`.
-/
structure AbelNF.Config extends AtomM.Recurse.Config where
  /-- The normalization style. -/
  mode := AbelMode.term

/-- Function elaborating `AbelNF.Config`. -/
declare_config_elab elabAbelNFConfig AbelNF.Config

/-- A cleanup routine, which simplifies expressions in `abel` normal form to a more human-friendly
format. -/
/-
**Mathlib.Tactic.Abel.cleanup** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：cleanup (cfg : AbelNF.Config) (r : Simp.Result) : MetaM Simp.Result
参数：cfg : AbelNF.Config；r : Simp.Result。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cleanup routine, which simplifies expressions in `abel` normal form to a more 
human-friendly
format.
-/
def cleanup (cfg : AbelNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  match cfg.mode with
  | .raw => pure r
  | .term =>
    let thms := [``term_eq, ``termg_eq, ``add_zero, ``one_nsmul, ``one_zsmul, ``zsmul_zero]
    let ctx ← Simp.mkContext (config := { zetaDelta := cfg.zetaDelta })
      (simpTheorems := #[← thms.foldlM (·.addConst ·) {}])
      (congrTheorems := ← getSimpCongrTheorems)
    pure <| ←
      r.mkEqTrans (← Simp.main r.expr ctx (methods := ← Lean.Meta.Simp.mkDefaultMethods)).1

/--
Evaluate an expression into its `abel` normal form.

This is a variant of `Mathlib.Tactic.Abel.eval`, the main driver of the `abel` tactic.
It differs in
* outputting a `Simp.Result`, rather than a `NormalExpr × Expr`;
* throwing an error if the expression `e` is an atom for the `abel` tactic.
-/
/-
**Mathlib.Tactic.Abel.evalExpr** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Abel`。
形式化陈述：evalExpr (e : Expr) : AtomM Simp.Result
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate an expression into its `abel` normal form.

This is a variant of `Mathlib.Tactic.Abel.eval`, the main driver of the `abel` t
actic.
It differs in
* outputting a `Simp.Result`, rather than a `NormalExpr × Expr`;
* throwing an error if the expression `e` is an atom for the `abel` tactic.
-/
def evalExpr (e : Expr) : AtomM Simp.Result := do
  let e ← withReducible <| whnf e
  guard !(isAtom e)
  let (a, pa) ← eval e (← mkContext e)
  return { expr := a, proof? := pa }

open Parser.Tactic

@[tactic_alt abel]
elab (name := abelNF) "abel_nf" tk:"!"? cfg:optConfig loc:(location)? : tactic => do
  let mut cfg ← elabAbelNFConfig cfg
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  let m := AtomM.recurse s cfg.toConfig (wellBehavedDischarge := true) evalExpr (cleanup cfg)
  transformAtLocation (m ·) "abel_nf" loc (ifUnchanged := .error) false

@[tactic_alt abel]
macro "abel_nf!" cfg:optConfig loc:(location)? : tactic =>
  `(tactic| abel_nf ! $cfg:optConfig $(loc)?)

@[inherit_doc abel]
syntax (name := abelNFConv) "abel_nf" "!"? optConfig : conv

/-- Elaborator for the `abel_nf` tactic. -/
@[tactic abelNFConv]
/-
**Mathlib.Tactic.Abel.elabAbelNFConv** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.A
bel`。
形式化陈述：elabAbelNFConv : Tactic
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Elaborator for the `abel_nf` tactic.
-/
def elabAbelNFConv : Tactic := fun stx ↦ match stx with
  | `(conv| abel_nf $[!%$tk]? $cfg:optConfig) => withMainContext do
    let mut cfg ← elabAbelNFConfig cfg
    if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
    let s ← IO.mkRef {}
    Conv.applySimpResult
      (← AtomM.recurse s cfg.toConfig (wellBehavedDischarge := true) evalExpr (cleanup cfg)
        (← instantiateMVars (← Conv.getLhs)))
  | _ => Elab.throwUnsupportedSyntax

@[inherit_doc abel]
macro "abel_nf!" cfg:optConfig : conv => `(conv| abel_nf ! $cfg:optConfig)

macro_rules
  | `(tactic| abel !) => `(tactic| first | abel1! | try_this abel_nf!)
  | `(tactic| abel) => `(tactic| first | abel1 | try_this abel_nf)

@[tactic_alt abel]
macro "abel!" : tactic => `(tactic| abel !)

@[inherit_doc abel]
macro (name := abelConv) "abel" : conv =>
  `(conv| first | discharge => abel1 | try_this abel_nf)

@[inherit_doc abelConv] macro "abel!" : conv =>
  `(conv| first | discharge => abel1! | try_this abel_nf!)

end

end Mathlib.Tactic.Abel

/-!
We register `abel` with the `hint` tactic.
-/

register_hint 950 abel

