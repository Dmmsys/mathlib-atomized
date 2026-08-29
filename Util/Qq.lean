/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.Init
public import Qq
public import Qq.Typ

/-!
# Extra `Qq` helpers

This file contains some additional functions for using the quote4 library more conveniently.
-/

public section

open Lean Elab Tactic Meta

namespace Qq

/--
Definition of `getLevelQ` / `getLevelQ` 的定义

English:
definition getLevelQ
  signature: (e : Expr)
  body: do
  return ⟨← getLevel e, e⟩

中文:
定义 getLevelQ
  签名: (e : Expr)
  定义体: do
  return ⟨← getLevel e, e⟩
-/
def getLevelQ (e : Expr) : MetaM (Σ u : Lean.Level, Q(Sort u)) := do
  return ⟨← getLevel e, e⟩

/--
Definition of `getLevelQ'` / `getLevelQ'` 的定义

English:
definition getLevelQ'
  signature: (e : Expr)
  body: do
  let u ← getLevel e
  let some v := (← instantiateLevelMVars u).dec | throwError "not a Type{indentExpr e}"
  return ⟨v, e⟩

中文:
定义 getLevelQ'
  签名: (e : Expr)
  定义体: do
  let u ← getLevel e
  let some v := (← instantiateLevelMVars u).dec | throwError "not a Type{indentExpr e}"
  return ⟨v, e⟩
-/
def getLevelQ' (e : Expr) : MetaM (Σ u : Lean.Level, Q(Type u)) := do
  let u ← getLevel e
  let some v := (← instantiateLevelMVars u).dec | throwError "not a Type{indentExpr e}"
  return ⟨v, e⟩

-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Using.20.60QQ.60.20when.20you.20only.20have.20an.20.60Expr.60/near/303349037
/--
Definition of `inferTypeQ'` / `inferTypeQ'` 的定义

English:
definition inferTypeQ'
  signature: (e : Expr)
  body: do
  let α ← inferType e
  let ⟨v, α⟩ ← getLevelQ' α
  pure ⟨v, α, e⟩

中文:
定义 inferTypeQ'
  签名: (e : Expr)
  定义体: do
  let α ← inferType e
  let ⟨v, α⟩ ← getLevelQ' α
  pure ⟨v, α, e⟩
-/
def inferTypeQ' (e : Expr) : MetaM ((u : Level) × (α : Q(Type $u)) × Q($α)) := do
  let α ← inferType e
  let ⟨v, α⟩ ← getLevelQ' α
  pure ⟨v, α, e⟩

/--
theorem `QuotedDefEq.rfl` / 定理 `QuotedDefEq.rfl`

English:
theorem QuotedDefEq.rfl
  given: {u : Level} {α : Q(Sort u)} {a : Q($α)}
  statement: @QuotedDefEq u α a a
  proof: ⟨⟩

中文:
定理 QuotedDefEq.rfl
  条件: {u : Level} {α : Q(类型层 u)} {a : Q($α)}
  结论: @QuotedDefEq u α a a
  证明: ⟨⟩
-/
theorem QuotedDefEq.rfl {u : Level} {α : Q(Sort u)} {a : Q($α)} : @QuotedDefEq u α a a := ⟨⟩

/--
Definition of `findLocalDeclWithTypeQ?` / `findLocalDeclWithTypeQ?` 的定义

English:
definition findLocalDeclWithTypeQ?
  signature: {u : Level} (sort : Q(Sort u))
  body: do
  let some fvarId ← findLocalDeclWithType? q($sort) | return none
return some .fvar fvarId

中文:
定义 findLocalDeclWithTypeQ?
  签名: {u : Level} (sort : Q(类型层 u))
  定义体: do
  let some fvarId ← findLocalDeclWithType? q($sort) | return none
return some .fvar fvarId
-/
def findLocalDeclWithTypeQ? {u : Level} (sort : Q(Sort u)) : MetaM (Option Q($sort)) := do
  let some fvarId ← findLocalDeclWithType? q($sort) | return none
return some .fvar fvarId

/--
Definition of `mkDecideProofQ` / `mkDecideProofQ` 的定义

English:
definition mkDecideProofQ
  signature: (p : Q(Prop))
  body: mkDecideProof p

中文:
定义 mkDecideProofQ
  签名: (p : Q(命题))
  定义体: mkDecideProof p

Depends on / 依赖: mkDecideProof
-/
def mkDecideProofQ (p : Q(Prop)) : MetaM Q($p) := mkDecideProof p

/--
Definition of `mkSetLiteralQ` / `mkSetLiteralQ` 的定义

English:
definition mkSetLiteralQ
  signature: {u v : Level} {α : Q(Type u)} (β : Q(Type v))
  body: match elems with
  | [] => q(∅)
  | [x] => q({$x})
  | x :: xs => q(Insert.insert $x $(mkSetLiteralQ β xs))

中文:
定义 mkSetLiteralQ
  签名: {u v : Level} {α : Q(类型u)} (β : Q(类型v))
  定义体: match elems with
  | [] => q(∅)
  | [x] => q({$x})
  | x :: xs => q(Insert.insert $x $(mkSetLiteralQ β xs))

Depends on / 依赖: Insert, Insert.insert, Singleton, insert, mkSetLiteralQ
-/
def mkSetLiteralQ {u v : Level} {α : Q(Type u)} (β : Q(Type v))
    (elems : List Q($α))
    (_ : Q(EmptyCollection $β) := by exact q(inferInstance))
    (_ : Q(Singleton $α $β) := by exact q(inferInstance))
    (_ : Q(Insert $α $β) := by exact q(inferInstance)) :
    Q($β) :=
  match elems with
  | [] => q(∅)
  | [x] => q({$x})
  | x :: xs => q(Insert.insert $x $(mkSetLiteralQ β xs))

/--
Definition of `mkNatLitQ` / `mkNatLitQ` 的定义

English:
definition mkNatLitQ
  signature: (n : Nat)
  body: mkNatLit n

中文:
定义 mk自然数LitQ
  签名: (n : 自然数)
  定义体: mkNatLit n

Depends on / 依赖: mkNatLit
-/
def mkNatLitQ (n : Nat) : Q(Nat) := mkNatLit n

/--
Definition of `mkIntLitQ` / `mkIntLitQ` 的定义

English:
definition mkIntLitQ
  signature: (n : Int)
  body: mkIntLit n

中文:
定义 mk整数LitQ
  签名: (n : 整数)
  定义体: mkIntLit n

Depends on / 依赖: mkIntLit
-/
def mkIntLitQ (n : Int) : Q(Int) := mkIntLit n

end Qq
