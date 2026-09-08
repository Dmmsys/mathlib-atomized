/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Init
public meta import Lean.CoreM
public meta import Lean.Util.FoldConsts

/-!
A rudimentary export format, adapted from
<https://github.com/leanprover-community/lean/blob/master/doc/export_format.md>
with support for Lean 4 kernel primitives.
-/

public meta section

open Lean
open Std (HashMap HashSet)

namespace Lean

namespace Export

/-! References -/

/-
**Lean.Export.MethodsRefPointed** 是 Mathlib 中的一个不透明定义，位于命名空间 `Lean.Export`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
References
-/
private opaque MethodsRefPointed : NonemptyType.{0}
/-
**Lean.Export.MethodsRef** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Export`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def MethodsRef : Type := MethodsRefPointed.type
/-
**Lean.Export.Entry** 是 Mathlib 中的一个归纳类型，位于命名空间 `Lean.Export`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
inductive Entry
  | name (n : Name)
  | level (n : Level)
  | expr (n : Expr)
  | defn (n : Name)
deriving Inhabited
/-
**Lean.Export.** 是 Mathlib 中的一个实例，位于命名空间 `Lean.Export`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe Name Entry := ⟨Entry.name⟩
/-
**Lean.Export.** 是 Mathlib 中的一个实例，位于命名空间 `Lean.Export`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe Level Entry := ⟨Entry.level⟩
/-
**Lean.Export.** 是 Mathlib 中的一个实例，位于命名空间 `Lean.Export`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe Expr Entry := ⟨Entry.expr⟩
/-
**Lean.Export.Alloc** 是 Mathlib 中的一个归纳类型，位于命名空间 `Lean.Export`。
形式化陈述：(α : Type u_1) → [BEq α] → [Hashable α] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure Alloc (α) [BEq α] [Hashable α] where
  map : Std.HashMap α Nat
  next : Nat
deriving Inhabited
/-
**Lean.Export.State** 是 Mathlib 中的一个结构，位于命名空间 `Lean.Export`。
形式化陈述：State where names : Alloc Name
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure State where
  names : Alloc Name := ⟨(∅ : Std.HashMap Name Nat).insert Name.anonymous 0, 1⟩
  levels : Alloc Level := ⟨(∅ : Std.HashMap Level Nat).insert .zero 0, 1⟩
  exprs : Alloc Expr
  defs : Std.HashSet Name
  stk : Array (Bool × Entry)
deriving Inhabited
/-
**Lean.Export.OfState** 是 Mathlib 中的一个归纳类型，位于命名空间 `Lean.Export`。
形式化陈述：(α : Type) → [BEq α] → [Hashable α] → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class OfState (α : Type) [BEq α] [Hashable α] where
  get : State → Alloc α
  modify : (Alloc α → Alloc α) → State → State
/-
**Lean.Export.** 是 Mathlib 中的一个实例，位于命名空间 `Lean.Export`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OfState Name where
  get s := s.names
  modify f s := { s with names := f s.names }
/-
**Lean.Export.** 是 Mathlib 中的一个实例，位于命名空间 `Lean.Export`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OfState Level where
  get s := s.levels
  modify f s := { s with levels := f s.levels }
/-
**Lean.Export.** 是 Mathlib 中的一个实例，位于命名空间 `Lean.Export`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OfState Expr where
  get s := s.exprs
  modify f s := { s with exprs := f s.exprs }

end Export

/-
**Lean.ExportM** 是 Mathlib 中的一个缩写定义，位于命名空间 `Lean`。
形式化陈述：ExportM
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev ExportM := StateT Export.State CoreM

namespace Export

/-
**Lean.Export.alloc** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Export`。
形式化陈述：alloc {α} [BEq α] [Hashable α] [OfState α] (a : α) : ExportM Nat
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def alloc {α} [BEq α] [Hashable α] [OfState α] (a : α) : ExportM Nat := do
  let n := (OfState.get (α := α) (← get)).next
  modify <| OfState.modify (α := α) fun s ↦ {map := s.map.insert a n, next := n + 1}
  pure n
/-
**Lean.Export.exportName** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Export`。
形式化陈述：exportName (n : Name) : ExportM Nat
参数：n : Name。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def exportName (n : Name) : ExportM Nat := do
  match (← get).names.map[n]? with
  | some i => pure i
  | none => match n with
    | .anonymous => pure 0
    | .num p a => let i ← alloc n; IO.println s!"{i} #NI {← exportName p} {a}"; pure i
    | .str p s => let i ← alloc n; IO.println s!"{i} #NS {← exportName p} {s}"; pure i
/-
**Lean.Export.exportLevel** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Export`。
形式化陈述：exportLevel (L : Level) : ExportM Nat
参数：L : Level。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def exportLevel (L : Level) : ExportM Nat := do
  match (← get).levels.map[L]? with
  | some i => pure i
  | none => match L with
    | .zero => pure 0
    | .succ l =>
      let i ← alloc L; IO.println s!"{i} #US {← exportLevel l}"; pure i
    | .max l₁ l₂ =>
      let i ← alloc L; IO.println s!"{i} #UM {← exportLevel l₁} {← exportLevel l₂}"; pure i
    | .imax l₁ l₂ =>
      let i ← alloc L; IO.println s!"{i} #UIM {← exportLevel l₁} {← exportLevel l₂}"; pure i
    | .param n =>
      let i ← alloc L; IO.println s!"{i} #UP {← exportName n}"; pure i
    | .mvar _ => unreachable!
/-
**Lean.Export.biStr** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Export`。
形式化陈述：biStr : BinderInfo -> String | BinderInfo.default => "#BD" | BinderInfo.im
plicit => "#BI" | BinderInfo.strictImplicit => "#BS" | BinderInfo.instImplicit =
> "#BC"  open ConstantInfo in mutual  partial def exportExpr (E : Expr) : Export
M Nat
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def biStr : BinderInfo → String
  | BinderInfo.default        => "#BD"
  | BinderInfo.implicit       => "#BI"
  | BinderInfo.strictImplicit => "#BS"
  | BinderInfo.instImplicit   => "#BC"

open ConstantInfo in
mutual
/-
**Lean.Export.exportExpr** 是 Mathlib 中的一个不透明定义，位于命名空间 `Lean.Export`。
形式化陈述：Expr → ExportM ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
partial def exportExpr (E : Expr) : ExportM Nat := do
  match (← get).exprs.map[E]? with
  | some i => pure i
  | none => match E with
    | .bvar n => let i ← alloc E; IO.println s!"{i} #EV {n}"; pure i
    | .fvar _ => unreachable!
    | .mvar _ => unreachable!
    | .sort l => let i ← alloc E; IO.println s!"{i} #ES {← exportLevel l}"; pure i
    | .const n ls =>
      exportDef n
      let i ← alloc E
      let mut s := s!"{i} #EC {← exportName n}"
      for l in ls do s := s ++ s!" {← exportLevel l}"
      IO.println s; pure i
    | .app e₁ e₂ =>
      let i ← alloc E; IO.println s!"{i} #EA {← exportExpr e₁} {← exportExpr e₂}"; pure i
    | .lam _ e₁ e₂ d =>
      let i ← alloc E
      IO.println s!"{i} #EL {biStr d} {← exportExpr e₁} {← exportExpr e₂}"; pure i
    | .forallE _ e₁ e₂ d =>
      let i ← alloc E
      IO.println s!"{i} #EP {biStr d} {← exportExpr e₁} {← exportExpr e₂}"; pure i
    | .letE _ e₁ e₂ e₃ _ =>
      let i ← alloc E
      IO.println s!"{i} #EP {← exportExpr e₁} {← exportExpr e₂} {← exportExpr e₃}"; pure i
    | .lit (.natVal n) => let i ← alloc E; IO.println s!"{i} #EN {n}"; pure i
    | .lit (.strVal s) => let i ← alloc E; IO.println s!"{i} #ET {s}"; pure i
    | .mdata _ _ => unreachable!
    | .proj n k e =>
      let i ← alloc E; IO.println s!"{i} #EJ {← exportName n} {k} {← exportExpr e}"; pure i
/-
**Lean.Export.exportDef** 是 Mathlib 中的一个不透明定义，位于命名空间 `Lean.Export`。
形式化陈述：Name → ExportM Unit
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
partial def exportDef (n : Name) : ExportM Unit := do
  if (← get).defs.contains n then return
  let ci ← getConstInfo n
  for c in ci.value!.getUsedConstants do
    unless (← get).defs.contains c do
      exportDef c
  match ci with
  | axiomInfo   val => axdef "#AX" val.name val.type val.levelParams
  | defnInfo    val => defn "#DEF" val.name val.type val.value val.levelParams
  | thmInfo     val => defn "#THM" val.name val.type val.value val.levelParams
  | opaqueInfo  val => defn "#CN" val.name val.type val.value val.levelParams
  | quotInfo    _ =>
    IO.println "#QUOT"
    for n in [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
      insert n
  | inductInfo  val => ind val.all
  | ctorInfo    val => ind (← getConstInfoInduct val.induct).all
  | recInfo     val => ind val.all
where
  insert (n : Name) : ExportM Unit :=
    modify fun s ↦ { s with defs := s.defs.insert n }
  defn (ty : String) (n : Name) (t e : Expr) (ls : List Name) : ExportM Unit := do
    let mut s := s!"{ty} {← exportName n} {← exportExpr t} {← exportExpr e}"
    for l in ls do s := s ++ s!" {← exportName l}"
    IO.println s
    insert n
  axdef (ty : String) (n : Name) (t : Expr) (ls : List Name) : ExportM Unit := do
    let mut s := s!"{ty} {← exportName n} {← exportExpr t}"
    for l in ls do s := s ++ s!" {← exportName l}"
    IO.println s
    insert n
  ind : List Name → ExportM Unit
  | [] => unreachable!
  | is@(i::_) => do
    let val ← getConstInfoInduct i
    let mut s := match is.length with
    | 1 => s!"#IND {val.numParams}"
    | n => s!"#MUT {val.numParams} {n}"
    for j in is do insert j; insert (mkRecName j)
    for j in is do
      let val ← getConstInfoInduct j
      s := s ++ s!" {← exportName val.name} {← exportExpr val.type} {val.ctors.length}"
      for c in val.ctors do
        insert c
        s := s ++ s!" {← exportName c} {← exportExpr (← getConstInfoCtor c).type}"
    for j in is do s ← indbody j s
    for l in val.levelParams do s := s ++ s!" {← exportName l}"
    IO.println s
  indbody (ind : Name) (s : String) : ExportM String := do
    let val ← getConstInfoInduct ind
    let mut s := s ++ s!" {← exportName ind} {← exportExpr val.type} {val.ctors.length}"
    for c in val.ctors do
      s := s ++ s!" {← exportName c} {← exportExpr (← getConstInfoCtor c).type}"
    pure s

end

/-
**Lean.Export.runExportM** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Export`。
形式化陈述：{α : Type} → ExportM α → CoreM α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def runExportM {α : Type} (m : ExportM α) : CoreM α := m.run' default

-- #eval runExportM (exportDef `Lean.Expr)
end Export

end Lean

