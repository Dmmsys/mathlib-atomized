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

/--
Definition of `term` / `term` 的定义

English:
definition term
  signature: {α} [AddCommMonoid α] (n : Nat) (x a : α)
  body: n • x + a

中文:
定义 term
  签名: {α} [加法交换幺半群 α] (n : 自然数) (x a : α)
  定义体: n • x + a
-/
@[expose] def term {α} [AddCommMonoid α] (n : Nat) (x a : α) : α := n • x + a
/--
Definition of `termg` / `termg` 的定义

English:
definition termg
  signature: {α} [AddCommGroup α] (n : Int) (x a : α)
  body: n • x + a

中文:
定义 termg
  签名: {α} [加法交换群 α] (n : 整数) (x a : α)
  定义体: n • x + a
-/
@[expose] def termg {α} [AddCommGroup α] (n : Int) (x a : α) : α := n • x + a

/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: {α} [AddCommMonoid α] (n : Nat) (x : α)
  body: n • x

中文:
定义 smul
  签名: {α} [加法交换幺半群 α] (n : 自然数) (x : α)
  定义体: n • x
-/
@[expose] def smul {α} [AddCommMonoid α] (n : Nat) (x : α) : α := n • x
/--
Definition of `smulg` / `smulg` 的定义

English:
definition smulg
  signature: {α} [AddCommGroup α] (n : Int) (x : α)
  body: n • x

meta section

中文:
定义 smulg
  签名: {α} [加法交换群 α] (n : 整数) (x : α)
  定义体: n • x

meta section
-/
@[expose] def smulg {α} [AddCommGroup α] (n : Int) (x : α) : α := n • x

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

/--
Definition of `Context` / `Context` 的定义

English:
structure Context
  parameters: where
  axioms and operations (5):
    - α : Expr
    - univ : Level
    - α0 : Expr
    - isGroup : Bool
    - inst : Expr

中文:
结构 余ntext
  参数: where
  公理与运算 (5 个):
    - α : Expr
    - univ : Level
    - α0 : Expr
    - isGroup : 布尔值
    - inst : Expr
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

/--
Definition of `mkContext` / `mkContext` 的定义

English:
definition mkContext
  signature: (e : Expr)
  body: do
  let α ← inferType e
  let c ← synthInstance (← mkAppM ``AddCommMonoid #[α])
  let cg ← synthInstance? (← mkAppM ``AddCommGroup #[α])
  let u ← mkFreshLevelMVar
  _ ← isDefEq (.sort (.succ u)) (← inferType α)
  let α0 ← Expr.ofNat α 0
  match cg with
  | some cg => return ⟨α, u, α0, true, cg⟩
  

中文:
定义 mkContext
  签名: (e : Expr)
  定义体: do
  let α ← inferType e
  let c ← synthInstance (← mkAppM ``AddCommMonoid #[α])
  let cg ← synthInstance? (← mkAppM ``AddCommGroup #[α])
  let u ← mkFreshLevelMVar
  _ ← isDefEq (.sort (.succ u)) (← inferType α)
  let α0 ← Expr.ofNat α 0
  match cg with
  | some cg => return ⟨α, u, α0, true, cg⟩
  
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

/--
Definition of `M` / `M` 的定义

English:
abbreviation M
  body: ReaderT Context AtomM

中文:
缩写 M
  定义体: ReaderT Context AtomM

Depends on / 依赖: Context, ReaderT
-/
abbrev M := ReaderT Context AtomM

/--
Definition of `Context.app` / `Context.app` 的定义

English:
definition Context.app
  signature: (c : Context) (n : Name) (inst : Expr)
  body: mkAppN (((@Expr.const n [c.univ]).app c.α).app inst)

中文:
定义 余ntext.app
  签名: (c : 余ntext) (n : Name) (inst : Expr)
  定义体: mkAppN (((@Expr.const n [c.univ]).app c.α).app inst)

Depends on / 依赖: Expr.const, c.univ, mkAppN
-/
def Context.app (c : Context) (n : Name) (inst : Expr) : Array Expr -> Expr :=
  mkAppN (((@Expr.const n [c.univ]).app c.α).app inst)

/--
Definition of `Context.mkApp` / `Context.mkApp` 的定义

English:
definition Context.mkApp
  signature: (c : Context) (n inst : Name) (l : Array Expr)
  body: do
  return c.app n (← synthInstance ((Expr.const inst [c.univ]).app c.α)) l

中文:
定义 余ntext.mkApp
  签名: (c : 余ntext) (n inst : Name) (l : 数组 Expr)
  定义体: do
  return c.app n (← synthInstance ((Expr.const inst [c.univ]).app c.α)) l
-/
def Context.mkApp (c : Context) (n inst : Name) (l : Array Expr) : MetaM Expr := do
  return c.app n (← synthInstance ((Expr.const inst [c.univ]).app c.α)) l

/--
Definition of `addG` / `addG` 的定义

English:
definition addG
  signature: : Name -> Name

中文:
定义 addG
  签名: : Name -> Name
-/
def addG : Name -> Name
  | .str p s => .str p (s ++ "g")
  | n => n

/--
Definition of `iapp` / `iapp` 的定义

English:
definition iapp
  signature: (n : Name) (xs : Array Expr)
  body: do
  let c ← read
  return c.app (if c.isGroup then addG n else n) c.inst xs

中文:
定义 iapp
  签名: (n : Name) (xs : 数组 Expr)
  定义体: do
  let c ← read
  return c.app (if c.isGroup then addG n else n) c.inst xs
-/
def iapp (n : Name) (xs : Array Expr) : M Expr := do
  let c ← read
  return c.app (if c.isGroup then addG n else n) c.inst xs

/--
Definition of `mkTerm` / `mkTerm` 的定义

English:
definition mkTerm
  signature: (n x a : Expr)
  body: iapp ``term #[n, x, a]

中文:
定义 mkTerm
  签名: (n x a : Expr)
  定义体: iapp ``term #[n, x, a]
-/
def mkTerm (n x a : Expr) : M Expr := iapp ``term #[n, x, a]

/--
Definition of `intToExpr` / `intToExpr` 的定义

English:
definition intToExpr
  signature: (n : Int)
  body: do
  Expr.ofInt (mkConst (if (← read).isGroup then ``Int else ``Nat) []) n

中文:
定义 intToExpr
  签名: (n : 整数)
  定义体: do
  Expr.ofInt (mkConst (if (← read).isGroup then ``Int else ``Nat) []) n
-/
def intToExpr (n : Int) : M Expr := do
  Expr.ofInt (mkConst (if (← read).isGroup then ``Int else ``Nat) []) n

/--
Inductive type `NormalExpr` / 归纳类型 `NormalExpr`

English:
inductive NormalExpr
  parameters: : Type
  constructors (2):
    - zero: (e : Expr) : NormalExpr
    - nterm: (e : Expr) (n : Expr × Int) (x : Nat × Expr) (a : NormalExpr) : NormalExpr

中文:
归纳类型 NormalExpr
  参数: : 类型
  构造子 (2 个):
    - zero: (e : Expr) : NormalExpr
    - nterm: (e : Expr) (n : Expr × 整数) (x : 自然数 × Expr) (a : NormalExpr) : NormalExpr
-/
inductive NormalExpr : Type
  | zero (e : Expr) : NormalExpr
  | nterm (e : Expr) (n : Expr × Int) (x : Nat × Expr) (a : NormalExpr) : NormalExpr
  deriving Inhabited

/--
Definition of `NormalExpr.e` / `NormalExpr.e` 的定义

English:
definition NormalExpr.e
  signature: : NormalExpr -> Expr

中文:
定义 NormalExpr.e
  签名: : NormalExpr -> Expr
-/
def NormalExpr.e : NormalExpr -> Expr
  | .zero e => e
  | .nterm e .. => e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe NormalExpr Expr
  body: NormalExpr.e

中文:
实例 :
  签名: Coe NormalExpr Expr
  定义体: NormalExpr.e

Depends on / 依赖: NormalExpr, NormalExpr.e
-/
instance : Coe NormalExpr Expr where coe := NormalExpr.e

/--
Definition of `NormalExpr.term'` / `NormalExpr.term'` 的定义

English:
definition NormalExpr.term'
  signature: (n : Expr × Int) (x : Nat × Expr) (a : NormalExpr)
  body: return .nterm (← mkTerm n.1 x.2 a) n x a

中文:
定义 NormalExpr.term'
  签名: (n : Expr × 整数) (x : 自然数 × Expr) (a : NormalExpr)
  定义体: return .nterm (← mkTerm n.1 x.2 a) n x a

Depends on / 依赖: mkTerm, return
-/
def NormalExpr.term' (n : Expr × Int) (x : Nat × Expr) (a : NormalExpr) : M NormalExpr :=
  return .nterm (← mkTerm n.1 x.2 a) n x a

/--
Definition of `NormalExpr.zero'` / `NormalExpr.zero'` 的定义

English:
definition NormalExpr.zero'
  signature: : M NormalExpr
  body: return NormalExpr.zero (← read).α0

中文:
定义 NormalExpr.zero'
  签名: : M NormalExpr
  定义体: return NormalExpr.zero (← read).α0

Depends on / 依赖: IsUltrametricDist, IsUltrametricDist.isClopen_ball, NormalExpr, NormalExpr.zero, Set.mem_compl, dist_comm, dist_pos, dist_pos.mpr, dist_self, exists_between, isClopen_ball, mem_ball, mem_compl, not_lt, return, totallySeparatedSpace_iff_exists_isClopen, totallySeparatedSpace_iff_exists_isClopen.mpr
-/
def NormalExpr.zero' : M NormalExpr := return NormalExpr.zero (← read).α0

open NormalExpr

/--
theorem `const_add_term` / 定理 `const_add_term`

English:
theorem const_add_term
  given: {α} [AddCommMonoid α] (k n x a a') (h : k + a = a')
  proof: by
  simp [h.symm, term, add_comm, add_assoc]

中文:
定理 const_add_term
  条件: {α} [加法交换幺半群 α] (k n x a a') (h : k + a = a')
  证明: by
  simp [h.symm, term, add_comm, add_assoc]

Depends on / 依赖: UniformSpace, _root_, _root_.UniformSpace.pseudoMetrizableSpace, add_assoc, add_comm, h.symm, pseudoMetrizableSpace
-/
theorem const_add_term {α} [AddCommMonoid α] (k n x a a') (h : k + a = a') :
    k + @term α _ n x a = term n x a' := by
  simp [h.symm, term, add_comm, add_assoc]

/--
theorem `const_add_termg` / 定理 `const_add_termg`

English:
theorem const_add_termg
  given: {α} [AddCommGroup α] (k n x a a') (h : k + a = a')
  proof: by
  simp [h.symm, termg, add_comm, add_assoc]

中文:
定理 const_add_termg
  条件: {α} [加法交换群 α] (k n x a a') (h : k + a = a')
  证明: by
  simp [h.symm, termg, add_comm, add_assoc]

Depends on / 依赖: add_assoc, add_comm, h.symm
-/
theorem const_add_termg {α} [AddCommGroup α] (k n x a a') (h : k + a = a') :
    k + @termg α _ n x a = termg n x a' := by
  simp [h.symm, termg, add_comm, add_assoc]

/--
theorem `term_add_const` / 定理 `term_add_const`

English:
theorem term_add_const
  given: {α} [AddCommMonoid α] (n x a k a') (h : a + k = a')
  proof: by
  simp [h.symm, term, add_assoc]

中文:
定理 term_add_const
  条件: {α} [加法交换幺半群 α] (n x a k a') (h : a + k = a')
  证明: by
  simp [h.symm, term, add_assoc]

Depends on / 依赖: add_assoc, h.symm
-/
theorem term_add_const {α} [AddCommMonoid α] (n x a k a') (h : a + k = a') :
    @term α _ n x a + k = term n x a' := by
  simp [h.symm, term, add_assoc]

/--
theorem `term_add_constg` / 定理 `term_add_constg`

English:
theorem term_add_constg
  given: {α} [AddCommGroup α] (n x a k a') (h : a + k = a')
  proof: by
  simp [h.symm, termg, add_assoc]

中文:
定理 term_add_constg
  条件: {α} [加法交换群 α] (n x a k a') (h : a + k = a')
  证明: by
  simp [h.symm, termg, add_assoc]

Depends on / 依赖: add_assoc, h.symm
-/
theorem term_add_constg {α} [AddCommGroup α] (n x a k a') (h : a + k = a') :
    @termg α _ n x a + k = termg n x a' := by
  simp [h.symm, termg, add_assoc]

/--
theorem `term_add_term` / 定理 `term_add_term`

English:
theorem term_add_term
  statement: {α} [AddCommMonoid α] (n₁ x a₁ n₂ a₂ n' a') (h₁ : n₁ + n₂ = n')
  proof: by
  simp [h₁.symm, h₂.symm, term, add_nsmul, add_assoc, add_left_comm]

中文:
定理 term_add_term
  结论: {α} [加法交换幺半群 α] (n₁ x a₁ n₂ a₂ n' a') (h₁ : n₁ + n₂ = n')
  证明: by
  simp [h₁.symm, h₂.symm, term, add_nsmul, add_assoc, add_left_comm]

Depends on / 依赖: add_assoc, add_left_comm, add_nsmul
-/
theorem term_add_term {α} [AddCommMonoid α] (n₁ x a₁ n₂ a₂ n' a') (h₁ : n₁ + n₂ = n')
    (h₂ : a₁ + a₂ = a') : @term α _ n₁ x a₁ + @term α _ n₂ x a₂ = term n' x a' := by
  simp [h₁.symm, h₂.symm, term, add_nsmul, add_assoc, add_left_comm]

/--
theorem `term_add_termg` / 定理 `term_add_termg`

English:
theorem term_add_termg
  statement: {α} [AddCommGroup α] (n₁ x a₁ n₂ a₂ n' a')
  proof: by
  simp only [termg, h₁.symm, add_zsmul, h₂.symm]
  exact add_add_add_comm (n₁ • x) a₁ (n₂ • x) a₂

中文:
定理 term_add_termg
  结论: {α} [加法交换群 α] (n₁ x a₁ n₂ a₂ n' a')
  证明: by
  simp only [termg, h₁.symm, add_zsmul, h₂.symm]
  exact add_add_add_comm (n₁ • x) a₁ (n₂ • x) a₂

Depends on / 依赖: PseudoMetrizableSpace, PseudoMetrizableSpace.firstCountableTopology, add_add_add_comm, add_zsmul, firstCountableTopology
-/
theorem term_add_termg {α} [AddCommGroup α] (n₁ x a₁ n₂ a₂ n' a')
    (h₁ : n₁ + n₂ = n') (h₂ : a₁ + a₂ = a') :
    @termg α _ n₁ x a₁ + @termg α _ n₂ x a₂ = termg n' x a' := by
  simp only [termg, h₁.symm, add_zsmul, h₂.symm]
  exact add_add_add_comm (n₁ • x) a₁ (n₂ • x) a₂

/--
theorem `zero_term` / 定理 `zero_term`

English:
theorem zero_term
  given: {α} [AddCommMonoid α] (x a)
  statement: @term α _ 0 x a = a
  proof: by
  simp [term, zero_nsmul]

中文:
定理 zero_term
  条件: {α} [加法交换幺半群 α] (x a)
  结论: @term α _ 0 x a = a
  证明: by
  simp [term, zero_nsmul]

Depends on / 依赖: zero_nsmul
-/
theorem zero_term {α} [AddCommMonoid α] (x a) : @term α _ 0 x a = a := by
  simp [term, zero_nsmul]

/--
theorem `zero_termg` / 定理 `zero_termg`

English:
theorem zero_termg
  given: {α} [AddCommGroup α] (x a)
  statement: @termg α _ 0 x a = a
  proof: by
  simp [termg, zero_zsmul]

中文:
定理 zero_termg
  条件: {α} [加法交换群 α] (x a)
  结论: @termg α _ 0 x a = a
  证明: by
  simp [termg, zero_zsmul]

Depends on / 依赖: zero_zsmul
-/
theorem zero_termg {α} [AddCommGroup α] (x a) : @termg α _ 0 x a = a := by
  simp [termg, zero_zsmul]

/--
Definition of `evalAdd` / `evalAdd` 的定义

English:
definition evalAdd
  signature: : NormalExpr -> NormalExpr -> M (NormalExpr × Expr)
  body: n₁.2 + n₂.2
      let p₁ ← iapp ``term_add_term
        #[n₁.1, x₁.2, a₁, n₂.1, a₂, n'.expr, a', ← n'.getProof, h₂]
      if k = 0 then do
        let p ← mkEqTrans p₁ (← iapp ``zero_term #[x₁.2, a'])
        return (a', p)
      else return (← term' (n'.expr, k) x₁ a', p₁)
    else if x₁.1 < x₂.1 t

中文:
定义 evalAdd
  签名: : NormalExpr -> NormalExpr -> M (NormalExpr × Expr)
  定义体: n₁.2 + n₂.2
      let p₁ ← iapp ``term_add_term
        #[n₁.1, x₁.2, a₁, n₂.1, a₂, n'.expr, a', ← n'.getProof, h₂]
      if k = 0 then do
        let p ← mkEqTrans p₁ (← iapp ``zero_term #[x₁.2, a'])
        return (a', p)
      else return (← term' (n'.expr, k) x₁ a', p₁)
    else if x₁.1 < x₂.1 t
-/
partial def evalAdd : NormalExpr -> NormalExpr -> M (NormalExpr × Expr)
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

/--
theorem `term_neg` / 定理 `term_neg`

English:
theorem term_neg
  statement: {α} [AddCommGroup α] (n x a n' a')
  proof: by
  simpa [h₂.symm, h₁.symm, termg] using add_comm _ _

中文:
定理 term_neg
  结论: {α} [加法交换群 α] (n x a n' a')
  证明: by
  simpa [h₂.symm, h₁.symm, termg] using add_comm _ _

Depends on / 依赖: IndiscreteTopology, IndiscreteTopology.pseudoMetrizableSpace, add_comm, pseudoMetrizableSpace
-/
theorem term_neg {α} [AddCommGroup α] (n x a n' a')
    (h₁ : -n = n') (h₂ : -a = a') : -@termg α _ n x a = termg n' x a' := by
  simpa [h₂.symm, h₁.symm, termg] using add_comm _ _

/--
Definition of `evalNeg` / `evalNeg` 的定义

English:
definition evalNeg
  signature: : NormalExpr -> M (NormalExpr × Expr)

中文:
定义 evalNeg
  签名: : NormalExpr -> M (NormalExpr × Expr)

Depends on / 依赖: PseudoMetrizableSpace, PseudoMetrizableSpace.toMetrizableSpace, toMetrizableSpace
-/
def evalNeg : NormalExpr -> M (NormalExpr × Expr)
  | (zero _) => do
    let p ← (← read).mkApp ``neg_zero ``NegZeroClass #[]
    return (← zero', p)
  | (nterm _ n x a) => do
    let n' ← Mathlib.Meta.NormNum.eval (← mkAppM ``Neg.neg #[n.1])
    let (a', h₂) ← evalNeg a
    return (← term' (n'.expr, -n.2) x a',
      (← read).app ``term_neg (← read).inst #[n.1, x.2, a, n'.expr, a', ← n'.getProof, h₂])

/--
theorem `zero_smul` / 定理 `zero_smul`

English:
theorem zero_smul
  given: {α} [AddCommMonoid α] (c)
  statement: smul c (0 : α) = 0
  proof: by
  simp [smul, nsmul_zero]

中文:
定理 zero_smul
  条件: {α} [加法交换幺半群 α] (c)
  结论: smul c (0 : α) = 0
  证明: by
  simp [smul, nsmul_zero]

Depends on / 依赖: MetrizableSpace, T2Space, nsmul_zero, t2Space_of_metrizableSpace
-/
theorem zero_smul {α} [AddCommMonoid α] (c) : smul c (0 : α) = 0 := by
  simp [smul, nsmul_zero]

/--
theorem `zero_smulg` / 定理 `zero_smulg`

English:
theorem zero_smulg
  given: {α} [AddCommGroup α] (c)
  statement: smulg c (0 : α) = 0
  proof: by
  simp [smulg, zsmul_zero]

中文:
定理 zero_smulg
  条件: {α} [加法交换群 α] (c)
  结论: smulg c (0 : α) = 0
  证明: by
  simp [smulg, zsmul_zero]

Depends on / 依赖: zsmul_zero
-/
theorem zero_smulg {α} [AddCommGroup α] (c) : smulg c (0 : α) = 0 := by
  simp [smulg, zsmul_zero]

/--
theorem `term_smul` / 定理 `term_smul`

English:
theorem term_smul
  statement: {α} [AddCommMonoid α] (c n x a n' a')
  proof: by
  simp [h₂.symm, h₁.symm, term, smul, nsmul_add, mul_nsmul']

中文:
定理 term_smul
  结论: {α} [加法交换幺半群 α] (c n x a n' a')
  证明: by
  simp [h₂.symm, h₁.symm, term, smul, nsmul_add, mul_nsmul']

Depends on / 依赖: mul_nsmul, nsmul_add
-/
theorem term_smul {α} [AddCommMonoid α] (c n x a n' a')
    (h₁ : c * n = n') (h₂ : smul c a = a') :
    smul c (@term α _ n x a) = term n' x a' := by
  simp [h₂.symm, h₁.symm, term, smul, nsmul_add, mul_nsmul']

/--
theorem `term_smulg` / 定理 `term_smulg`

English:
theorem term_smulg
  statement: {α} [AddCommGroup α] (c n x a n' a')
  proof: by
  simp [h₂.symm, h₁.symm, termg, smulg, zsmul_add, mul_zsmul]

中文:
定理 term_smulg
  结论: {α} [加法交换群 α] (c n x a n' a')
  证明: by
  simp [h₂.symm, h₁.symm, termg, smulg, zsmul_add, mul_zsmul]

Depends on / 依赖: mul_zsmul, zsmul_add
-/
theorem term_smulg {α} [AddCommGroup α] (c n x a n' a')
    (h₁ : c * n = n') (h₂ : smulg c a = a') :
    smulg c (@termg α _ n x a) = termg n' x a' := by
  simp [h₂.symm, h₁.symm, termg, smulg, zsmul_add, mul_zsmul]

/--
Definition of `evalSMul` / `evalSMul` 的定义

English:
definition evalSMul
  signature: (k : Expr × Int)

中文:
定义 evalSMul
  签名: (k : Expr × 整数)

Depends on / 依赖: LindelofSpace, LindelofSpace.elim_nhds_subcover, SeparableSpace, Set.countable_iUnion, Set.iUnion, ball_mem_nhds, countable_iUnion, elim_nhds_subcover, frequently_comap, hVb.freq, hVb.mem, has_seq_basis, iUnion, mem_closure_iff_frequently, nhds_eq_comap_uniformity, pseudoMetrizableSpaceUniformity, pseudoMetrizableSpaceUniformity_countably_generated, secondCountable_of_separable
-/
def evalSMul (k : Expr × Int) : NormalExpr -> M (NormalExpr × Expr)
  | zero _ => return (← zero', ← iapp ``zero_smul #[k.1])
  | nterm _ n x a => do
    let n' ← Mathlib.Meta.NormNum.eval (← mkAppM ``HMul.hMul #[k.1, n.1])
    let (a', h₂) ← evalSMul k a
    return (← term' (n'.expr, k.2 * n.2) x a',
      ← iapp ``term_smul #[k.1, n.1, x.2, a, n'.expr, a', ← n'.getProof, h₂])

/--
theorem `term_atom` / 定理 `term_atom`

English:
theorem term_atom
  given: {α} [AddCommMonoid α] (x : α)
  statement: x = term 1 x 0
  proof: by simp [term, one_nsmul]

中文:
定理 term_atom
  条件: {α} [加法交换幺半群 α] (x : α)
  结论: x = term 1 x 0
  证明: by simp [term, one_nsmul]

Depends on / 依赖: one_nsmul
-/
theorem term_atom {α} [AddCommMonoid α] (x : α) : x = term 1 x 0 := by simp [term, one_nsmul]
/--
theorem `term_atomg` / 定理 `term_atomg`

English:
theorem term_atomg
  given: {α} [AddCommGroup α] (x : α)
  statement: x = termg 1 x 0
  proof: by simp [termg]

中文:
定理 term_atomg
  条件: {α} [加法交换群 α] (x : α)
  结论: x = termg 1 x 0
  证明: by simp [termg]
-/
theorem term_atomg {α} [AddCommGroup α] (x : α) : x = termg 1 x 0 := by simp [termg]
/--
theorem `term_atom_pf` / 定理 `term_atom_pf`

English:
theorem term_atom_pf
  given: {α} [AddCommMonoid α] (x x' : α) (h : x = x')
  statement: x = term 1 x' 0
  proof: by
  simp [term, h, one_nsmul]

中文:
定理 term_atom_pf
  条件: {α} [加法交换幺半群 α] (x x' : α) (h : x = x')
  结论: x = term 1 x' 0
  证明: by
  simp [term, h, one_nsmul]

Depends on / 依赖: DiscreteTopology, DiscreteTopology.metrizableSpace, metrizableSpace, one_nsmul
-/
theorem term_atom_pf {α} [AddCommMonoid α] (x x' : α) (h : x = x') : x = term 1 x' 0 := by
  simp [term, h, one_nsmul]
/--
theorem `term_atom_pfg` / 定理 `term_atom_pfg`

English:
theorem term_atom_pfg
  given: {α} [AddCommGroup α] (x x' : α) (h : x = x')
  statement: x = termg 1 x' 0
  proof: by
  simp [termg, h]

中文:
定理 term_atom_pfg
  条件: {α} [加法交换群 α] (x x' : α) (h : x = x')
  结论: x = termg 1 x' 0
  证明: by
  simp [termg, h]

Depends on / 依赖: upgradeIsCompletelyPseudoMetrizable
-/
theorem term_atom_pfg {α} [AddCommGroup α] (x x' : α) (h : x = x') : x = termg 1 x' 0 := by
  simp [termg, h]

/--
Definition of `evalAtom` / `evalAtom` 的定义

English:
definition evalAtom
  signature: (e : Expr)
  body: do
  let { expr := e', proof?, .. } ← (← readThe AtomM.Context).evalAtom e
  let (i, a) ← AtomM.addAtom e'
  let p ← match proof? with
  | none => iapp ``term_atom #[e]
  | some p => iapp ``term_atom_pf #[e, a, p]
  return (← term' (← intToExpr 1, 1) (i, a) (← zero'), p)

中文:
定义 evalAtom
  签名: (e : Expr)
  定义体: do
  let { expr := e', proof?, .. } ← (← readThe AtomM.Context).evalAtom e
  let (i, a) ← AtomM.addAtom e'
  let p ← match proof? with
  | none => iapp ``term_atom #[e]
  | some p => iapp ``term_atom_pf #[e, a, p]
  return (← term' (← intToExpr 1, 1) (i, a) (← zero'), p)

Depends on / 依赖: PseudoMetricSpace, _root_, _root_.PseudoMetricSpace.toIsCompletelPseudoMetrizableSpace, toIsCompletelPseudoMetrizableSpace
-/
def evalAtom (e : Expr) : M (NormalExpr × Expr) := do
  let { expr := e', proof?, .. } ← (← readThe AtomM.Context).evalAtom e
  let (i, a) ← AtomM.addAtom e'
  let p ← match proof? with
  | none => iapp ``term_atom #[e]
  | some p => iapp ``term_atom_pf #[e, a, p]
  return (← term' (← intToExpr 1, 1) (i, a) (← zero'), p)

/--
theorem `unfold_sub` / 定理 `unfold_sub`

English:
theorem unfold_sub
  given: {α} [SubtractionMonoid α] (a b c : α) (h : a + -b = c)
  statement: a - b = c
  proof: by
  rw [sub_eq_add_neg]; rw [h]

中文:
定理 unfold_sub
  条件: {α} [Subtraction幺半群 α] (a b c : α) (h : a + -b = c)
  结论: a - b = c
  证明: by
  rw [sub_eq_add_neg]; rw [h]

Depends on / 依赖: IsCompletelyPseudoMetrizableSpace, IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable, of_completeSpace_pseudometrizable, sub_eq_add_neg
-/
theorem unfold_sub {α} [SubtractionMonoid α] (a b c : α) (h : a + -b = c) : a - b = c := by
  rw [sub_eq_add_neg]; rw [h]

/--
theorem `unfold_smul` / 定理 `unfold_smul`

English:
theorem unfold_smul
  statement: {α} [AddCommMonoid α] (n) (x y : α)
  proof: h

中文:
定理 unfold_smul
  结论: {α} [加法交换幺半群 α] (n) (x y : α)
  证明: h
-/
theorem unfold_smul {α} [AddCommMonoid α] (n) (x y : α)
    (h : smul n x = y) : n • x = y := h

/--
theorem `unfold_smulg` / 定理 `unfold_smulg`

English:
theorem unfold_smulg
  statement: {α} [AddCommGroup α] (n : Nat) (x y : α)
  proof: h

中文:
定理 unfold_smulg
  结论: {α} [加法交换群 α] (n : 自然数) (x y : α)
  证明: h
-/
theorem unfold_smulg {α} [AddCommGroup α] (n : Nat) (x y : α)
    (h : smulg (Int.ofNat n) x = y) : (n : Int) • x = y := h

/--
theorem `unfold_zsmul` / 定理 `unfold_zsmul`

English:
theorem unfold_zsmul
  statement: {α} [AddCommGroup α] (n : Int) (x y : α)
  proof: h

中文:
定理 unfold_zsmul
  结论: {α} [加法交换群 α] (n : 整数) (x y : α)
  证明: h
-/
theorem unfold_zsmul {α} [AddCommGroup α] (n : Int) (x y : α)
    (h : smulg n x = y) : n • x = y := h

/--
lemma `subst_into_smul` / 引理 `subst_into_smul`

English:
lemma subst_into_smul
  statement: {α} [AddCommMonoid α]
  proof: by simp [prl, prr, prt]

中文:
引理 subst_into_smul
  结论: {α} [加法交换幺半群 α]
  证明: by simp [prl, prr, prt]

Depends on / 依赖: PseudoMetrizableSpace, TopologicalSpace
-/
lemma subst_into_smul {α} [AddCommMonoid α]
    (l r tl tr t) (prl : l = tl) (prr : r = tr)
    (prt : @smul α _ tl tr = t) : smul l r = t := by simp [prl, prr, prt]

/--
lemma `subst_into_smulg` / 引理 `subst_into_smulg`

English:
lemma subst_into_smulg
  statement: {α} [AddCommGroup α]
  proof: by simp [prl, prr, prt]

中文:
引理 subst_into_smulg
  结论: {α} [加法交换群 α]
  证明: by simp [prl, prr, prt]
-/
lemma subst_into_smulg {α} [AddCommGroup α]
    (l r tl tr t) (prl : l = tl) (prr : r = tr)
    (prt : @smulg α _ tl tr = t) : smulg l r = t := by simp [prl, prr, prt]

/--
lemma `subst_into_smul_upcast` / 引理 `subst_into_smul_upcast`

English:
lemma subst_into_smul_upcast
  statement: {α} [AddCommGroup α]
  proof: by
  simp [← prt, prl₁, ← prl₂, prr, smul, smulg, natCast_zsmul]

中文:
引理 subst_into_smul_upcast
  结论: {α} [加法交换群 α]
  证明: by
  simp [← prt, prl₁, ← prl₂, prr, smul, smulg, natCast_zsmul]

Depends on / 依赖: natCast_zsmul
-/
lemma subst_into_smul_upcast {α} [AddCommGroup α]
    (l r tl zl tr t) (prl₁ : l = tl) (prl₂ : ↑tl = zl) (prr : r = tr)
    (prt : @smulg α _ zl tr = t) : smul l r = t := by
  simp [← prt, prl₁, ← prl₂, prr, smul, smulg, natCast_zsmul]

/--
lemma `subst_into_add` / 引理 `subst_into_add`

English:
lemma subst_into_add
  statement: {α} [AddCommMonoid α] (l r tl tr t)
  proof: by
  rw [prl]; rw [prr]; rw [prt]

中文:
引理 subst_into_add
  结论: {α} [加法交换幺半群 α] (l r tl tr t)
  证明: by
  rw [prl]; rw [prr]; rw [prt]
-/
lemma subst_into_add {α} [AddCommMonoid α] (l r tl tr t)
    (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t := by
  rw [prl]; rw [prr]; rw [prt]

/--
lemma `subst_into_addg` / 引理 `subst_into_addg`

English:
lemma subst_into_addg
  statement: {α} [AddCommGroup α] (l r tl tr t)
  proof: by
  rw [prl]; rw [prr]; rw [prt]

中文:
引理 subst_into_addg
  结论: {α} [加法交换群 α] (l r tl tr t)
  证明: by
  rw [prl]; rw [prr]; rw [prt]
-/
lemma subst_into_addg {α} [AddCommGroup α] (l r tl tr t)
    (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t := by
  rw [prl]; rw [prr]; rw [prt]

/--
lemma `subst_into_negg` / 引理 `subst_into_negg`

English:
lemma subst_into_negg
  statement: {α} [AddCommGroup α] (a ta t : α)
  proof: by
  simp [pra, prt]

中文:
引理 subst_into_negg
  结论: {α} [加法交换群 α] (a ta t : α)
  证明: by
  simp [pra, prt]
-/
lemma subst_into_negg {α} [AddCommGroup α] (a ta t : α)
    (pra : a = ta) (prt : -ta = t) : -a = t := by
  simp [pra, prt]

/--
Definition of `evalSMul'` / `evalSMul'` 的定义

English:
definition evalSMul'
  signature: (eval : Expr -> M (NormalExpr × Expr))
  body: do
  trace[abel] "Calling NormNum on {e₁}"
  let ⟨e₁', p₁, _⟩ ← try Meta.NormNum.eval e₁ catch _ => pure { expr := e₁ }
  let p₁ ← p₁.getDM (mkEqRefl e₁')
  match e₁'.int? with
  | some n => do
    let c ← read
    let (e₂', p₂) ← eval e₂
    if c.isGroup = is_smulg then do
      let (e', p) ← evalS

中文:
定义 evalSMul'
  签名: (eval : Expr -> M (NormalExpr × Expr))
  定义体: do
  trace[abel] "Calling NormNum on {e₁}"
  let ⟨e₁', p₁, _⟩ ← try Meta.NormNum.eval e₁ catch _ => pure { expr := e₁ }
  let p₁ ← p₁.getDM (mkEqRefl e₁')
  match e₁'.int? with
  | some n => do
    let c ← read
    let (e₂', p₂) ← eval e₂
    if c.isGroup = is_smulg then do
      let (e', p) ← evalS
-/
def evalSMul' (eval : Expr -> M (NormalExpr × Expr))
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
      let zl ← Expr.ofInt q(Int) n
      let p₁' ← mkEqRefl zl
      let (e', p) ← evalSMul (zl, n) e₂'
      return (e', c.app ``subst_into_smul_upcast c.inst #[e₁, e₂, e₁', zl, e₂', e', p₁, p₁', p₂, p])
  | none => evalAtom orig

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (e : Expr)
  body: do
  trace[abel.detail] "running eval on {e}"
  trace[abel.detail] "getAppFnArgs: {e.getAppFnArgs}"
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← evalAdd e₁' e₂'
    return (e', ← iapp ``subst_int

中文:
定义 eval
  签名: (e : Expr)
  定义体: do
  trace[abel.detail] "running eval on {e}"
  trace[abel.detail] "getAppFnArgs: {e.getAppFnArgs}"
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← evalAdd e₁' e₂'
    return (e', ← iapp ``subst_int
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
let (e', p) ← eval ← iapp ``smul #[n, e₂]
    return (e', ← iapp ``unfold_smul #[e₁, e₂, e', p])
  | (``ZSMul.zsmul, #[_, _, e₁, e₂]) => do
      if ¬ (← read).isGroup then failure
let (e', p) ← eval ← iapp ``smul #[e₁, e₂]
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

/--
Definition of `isAtom` / `isAtom` 的定义

English:
definition isAtom
  signature: (e : Expr)
  body: match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, _, _])
  | (``HSub.hSub, #[_, _, _, _, _, _])
  | (``Neg.neg, #[_, _, _])
  | (``NSMul.nsmul, #[_, _, _, _])
  | (``ZSMul.zsmul, #[_, _, _, _])
  | (``SMul.smul, #[.const ``Int _, _, _, _, _])
  | (``SMul.smul, #[.const ``Nat _, _, _, _, _])


中文:
定义 isAtom
  签名: (e : Expr)
  定义体: match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, _, _])
  | (``HSub.hSub, #[_, _, _, _, _, _])
  | (``Neg.neg, #[_, _, _])
  | (``NSMul.nsmul, #[_, _, _, _])
  | (``ZSMul.zsmul, #[_, _, _, _])
  | (``SMul.smul, #[.const ``Int _, _, _, _, _])
  | (``SMul.smul, #[.const ``Nat _, _, _, _, _])


Depends on / 依赖: HAdd.hAdd, HSMul.hSMul, HSub.hSub, MetricSpace, NSMul.nsmul, Neg.neg, SMul.smul, ZSMul.zsmul, _root_, _root_.MetricSpace.toIsCompletelyMetrizableSpace, e.getAppFnArgs, getAppFnArgs, toIsCompletelyMetrizableSpace
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
let proof ← AtomM.run tm ReaderT.run (r := c) do
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

/--
theorem `term_eq` / 定理 `term_eq`

English:
theorem term_eq
  given: {α : Type*} [AddCommMonoid α] (n : Nat) (x a : α)
  statement: term n x a = n • x + a
  proof: (rfl)

中文:
定理 term_eq
  条件: {α : 类型} [加法交换幺半群 α] (n : 自然数) (x a : α)
  结论: term n x a = n • x + a
  证明: (rfl)

Depends on / 依赖: IsCompletelyMetrizableSpace, IsCompletelyMetrizableSpace.of_completeSpace_metrizable, UniformSpace, of_completeSpace_metrizable
-/
theorem term_eq {α : Type*} [AddCommMonoid α] (n : Nat) (x a : α) : term n x a = n • x + a := (rfl)
/--
theorem `termg_eq` / 定理 `termg_eq`

English:
theorem termg_eq
  given: {α : Type*} [AddCommGroup α] (n : Int) (x a : α)
  statement: termg n x a = n • x + a
  proof: (rfl)

中文:
定理 termg_eq
  条件: {α : 类型} [加法交换群 α] (n : 整数) (x a : α)
  结论: termg n x a = n • x + a
  证明: (rfl)
-/
theorem termg_eq {α : Type*} [AddCommGroup α] (n : Int) (x a : α) : termg n x a = n • x + a := (rfl)

/--
Definition of `NormalExpr.isAtom` / `NormalExpr.isAtom` 的定义

English:
definition NormalExpr.isAtom
  signature: : NormalExpr -> Bool

中文:
定义 NormalExpr.isAtom
  签名: : NormalExpr -> 布尔值
-/
def NormalExpr.isAtom : NormalExpr -> Bool
  | .nterm _ (_, 1) _ (.zero _) => true
  | _ => false

/--
Inductive type `AbelMode` / 归纳类型 `AbelMode`

English:
inductive AbelMode
  parameters: where
  constructors (2):
    - term: 
    - raw: 

中文:
归纳类型 AbelMode
  参数: where
  构造子 (2 个):
    - term: 
    - raw: 
-/
inductive AbelMode where
  /-- The default form -/
  | term
  /-- Raw form: the representation `abel` uses internally. -/
  | raw

/--
Definition of `AbelNF.Config` / `AbelNF.Config` 的定义

English:
structure AbelNF.Config
  parameters: extends AtomM.Recurse.Config
  extends: AtomM.Recurse.Config
  axioms and operations (1):
    - mode : = AbelMode.term

中文:
结构 AbelNF.余nfig
  参数: extends AtomM.Recurse.余nfig
  继承: AtomM.Recurse.余nfig
  公理与运算 (1 个):
    - mode : = AbelMode.term

Depends on / 依赖: AbelMode, AbelMode.term, IsCompletelyMetrizableSpace, MetrizableSpace, TopologicalSpace
-/
structure AbelNF.Config extends AtomM.Recurse.Config where
  /-- The normalization style. -/
  mode := AbelMode.term

/-- Function elaborating `AbelNF.Config`. -/
declare_config_elab elabAbelNFConfig AbelNF.Config

/--
Definition of `cleanup` / `cleanup` 的定义

English:
definition cleanup
  signature: (cfg : AbelNF.Config) (r : Simp.Result)
  body: do
  match cfg.mode with
  | .raw => pure r
  | .term =>
    let thms := [``term_eq, ``termg_eq, ``add_zero, ``one_nsmul, ``one_zsmul, ``zsmul_zero]
    let ctx ← Simp.mkContext (config := { zetaDelta := cfg.zetaDelta })
      (simpTheorems := #[← thms.foldlM (·.addConst ·) {}])
      (congrTheorems

中文:
定义 cleanup
  签名: (cfg : AbelNF.余nfig) (r : Simp.Result)
  定义体: do
  match cfg.mode with
  | .raw => pure r
  | .term =>
    let thms := [``term_eq, ``termg_eq, ``add_zero, ``one_nsmul, ``one_zsmul, ``zsmul_zero]
    let ctx ← Simp.mkContext (config := { zetaDelta := cfg.zetaDelta })
      (simpTheorems := #[← thms.foldlM (·.addConst ·) {}])
      (congrTheorems
-/
def cleanup (cfg : AbelNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  match cfg.mode with
  | .raw => pure r
  | .term =>
    let thms := [``term_eq, ``termg_eq, ``add_zero, ``one_nsmul, ``one_zsmul, ``zsmul_zero]
    let ctx ← Simp.mkContext (config := { zetaDelta := cfg.zetaDelta })
      (simpTheorems := #[← thms.foldlM (·.addConst ·) {}])
      (congrTheorems := ← getSimpCongrTheorems)
pure ←
      r.mkEqTrans (← Simp.main r.expr ctx (methods := ← Lean.Meta.Simp.mkDefaultMethods)).1

/--
Definition of `evalExpr` / `evalExpr` 的定义

English:
definition evalExpr
  signature: (e : Expr)
  body: do
let e ← withReducible whnf e
  guard !(isAtom e)
  let (a, pa) ← eval e (← mkContext e)
  return { expr := a, proof? := pa }

中文:
定义 evalExpr
  签名: (e : Expr)
  定义体: do
let e ← withReducible whnf e
  guard !(isAtom e)
  let (a, pa) ← eval e (← mkContext e)
  return { expr := a, proof? := pa }
-/
def evalExpr (e : Expr) : AtomM Simp.Result := do
let e ← withReducible whnf e
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
/--
Definition of `elabAbelNFConv` / `elabAbelNFConv` 的定义

English:
definition elabAbelNFConv
  signature: : Tactic
  body: fun stx => match stx with
  | `(conv| abel_nf $[!%$tk]? $cfg:optConfig) => withMainContext do
    let mut cfg ← elabAbelNFConfig cfg
    if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
    let s ← IO.mkRef {}
    Conv.applySimpResult
      (← AtomM.recurse s cfg.toConfig (we

中文:
定义 elabAbelNFConv
  签名: : Tactic
  定义体: fun stx => match stx with
  | `(conv| abel_nf $[!%$tk]? $cfg:optConfig) => withMainContext do
    let mut cfg ← elabAbelNFConfig cfg
    if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
    let s ← IO.mkRef {}
    Conv.applySimpResult
      (← AtomM.recurse s cfg.toConfig (we
-/
def elabAbelNFConv : Tactic := fun stx => match stx with
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
