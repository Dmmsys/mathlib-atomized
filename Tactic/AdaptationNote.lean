/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public meta import Lean.Meta.Tactic.TryThis
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# Adaptation notes

This file defines a `#adaptation_note` command.
Adaptation notes are comments that are used to indicate that a piece of code
has been changed to accommodate a change in Lean core.
They typically require further action/maintenance to be taken in the future.
-/

public meta section

open Lean

initialize registerTraceClass `adaptationNote

/-- General function implementing adaptation notes. -/
/-
**reportAdaptationNote** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：reportAdaptationNote (f : Syntax -> Meta.Tactic.TryThis.Suggestion) : Meta
M Unit
参数：f : Syntax -> Meta.Tactic.TryThis.Suggestion。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
General function implementing adaptation notes.
-/
def reportAdaptationNote (f : Syntax → Meta.Tactic.TryThis.Suggestion) : MetaM Unit := do
  let stx ← getRef
  if let some doc := stx[1].getOptional? then
    trace[adaptationNote] (Lean.TSyntax.getDocString ⟨doc⟩)
  else
    logError "Adaptation notes must be followed by a /-- comment -/"
    let trailing := if let .original (trailing := s) .. := stx[0].getTailInfo then s else default
    let doc : Syntax :=
      Syntax.node2 .none ``Parser.Command.docComment (mkAtom "/--") (mkAtom "comment -/")
    -- Optional: copy the original whitespace after the `#adaptation_note` token
    -- to after the docstring comment
    let doc := doc.updateTrailing trailing
    let stx' := (← getRef)
    let stx' := stx'.setArg 0 stx'[0].unsetTrailing
    let stx' := stx'.setArg 1 (mkNullNode #[doc])
    Meta.Tactic.TryThis.addSuggestion (← getRef) (f stx') (origSpan? := ← getRef)

/-- `#adaptation_note /-- comment -/` adds an adaptation note to the current file.
Adaptation notes are comments that are used to indicate that a piece of code
has been changed to accommodate a change in Lean core.
They typically require further action/maintenance to be taken in the future.

This syntax works as a command, or inline in tactic or term mode.
-/
elab (name := adaptationNoteCmd) "#adaptation_note " (docComment)? : command => do
  Elab.Command.liftTermElabM <| reportAdaptationNote (fun s => (⟨s⟩ : TSyntax `tactic))

@[inherit_doc adaptationNoteCmd]
elab "#adaptation_note " (docComment)? : tactic =>
  reportAdaptationNote (fun s => (⟨s⟩ : TSyntax `tactic))

@[inherit_doc adaptationNoteCmd]
syntax (name := adaptationNoteTermStx) "#adaptation_note " (docComment)? term : term

/-- Elaborator for adaptation notes. -/
@[term_elab adaptationNoteTermStx]
/-
**adaptationNoteTermElab** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：adaptationNoteTermElab : Elab.Term.TermElab | `(#adaptation_note $[$_]? $t
) => fun expectedType? => do reportAdaptationNote (fun s => (⟨s⟩ : Term)) Elab.T
erm.elabTerm t expectedType? | _ => fun _ => Elab.throwUnsupportedSyntax   #adap
tation_note /-- This is a test -/  example : True
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Elaborator for adaptation notes.
-/
def adaptationNoteTermElab : Elab.Term.TermElab
  | `(#adaptation_note $[$_]? $t) => fun expectedType? => do
    reportAdaptationNote (fun s => (⟨s⟩ : Term))
    Elab.Term.elabTerm t expectedType?
  | _ => fun _ => Elab.throwUnsupportedSyntax


#adaptation_note /-- This is a test -/
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a test
-/
example : True := by
  #adaptation_note /-- This is a test -/
  trivial
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : True :=
  #adaptation_note /-- This is a test -/
  trivial
