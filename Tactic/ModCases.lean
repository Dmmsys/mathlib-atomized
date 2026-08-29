/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.HaveI

/-! # `mod_cases` tactic

The `mod_cases` tactic does case disjunction on `e % n`, where `e : ℤ` or `e : ℕ`,
to yield `n` new subgoals corresponding to the possible values of `e` modulo `n`.
-/

public section

namespace Mathlib.Tactic.ModCases
open Lean Meta Elab Tactic Term Qq

namespace IntMod
open Int

/--
Definition of `OnModCases` / `OnModCases` 的定义

English:
definition OnModCases
  signature: (n : Nat) (a : Int) (lb : Nat) (p : Sort*)
  body: forall z, lb <= z ∧ z < n ∧ a ≡ ↑z [ZMOD ↑n] -> p

中文:
定义 OnModCases
  签名: (n : 自然数) (a : 整数) (lb : 自然数) (p : Sort*)
  定义体: forall z, lb <= z ∧ z < n ∧ a ≡ ↑z [ZMOD ↑n] -> p
-/
@[expose] def OnModCases (n : Nat) (a : Int) (lb : Nat) (p : Sort*) :=
  forall z, lb <= z ∧ z < n ∧ a ≡ ↑z [ZMOD ↑n] -> p

/--
Definition of `onModCases_start` / `onModCases_start` 的定义

English:
definition onModCases_start
  signature: (p : Sort*) (a : Int) (n : Nat) (hn : Nat.ble 1 n = true)
  body: H (a % ↑n).toNat by
have := natCast_pos.2 Nat.le_of_ble_eq_true hn
have nonneg := emod_nonneg a Int.ne_of_gt this
    refine ⟨Nat.zero_le _, ?_, ?_⟩
    · rw [Int.toNat_lt nonneg]; exact Int.emod_lt_of_pos _ this
    · rw [Int.ModEq, Int.toNat_of_nonneg nonneg, emod_emod]

中文:
定义 onModCases_start
  签名: (p : Sort*) (a : 整数) (n : 自然数) (hn : 自然数.ble 1 n = true)
  定义体: H (a % ↑n).toNat by
have := natCast_pos.2 Nat.le_of_ble_eq_true hn
have nonneg := emod_nonneg a Int.ne_of_gt this
    refine ⟨Nat.zero_le _, ?_, ?_⟩
    · rw [Int.toNat_lt nonneg]; exact Int.emod_lt_of_pos _ this
    · rw [Int.ModEq, Int.toNat_of_nonneg nonneg, emod_emod]
-/
@[inline] def onModCases_start (p : Sort*) (a : Int) (n : Nat) (hn : Nat.ble 1 n = true)
    (H : OnModCases n a (nat_lit 0) p) : p :=
H (a % ↑n).toNat by
have := natCast_pos.2 Nat.le_of_ble_eq_true hn
have nonneg := emod_nonneg a Int.ne_of_gt this
    refine ⟨Nat.zero_le _, ?_, ?_⟩
    · rw [Int.toNat_lt nonneg]; exact Int.emod_lt_of_pos _ this
    · rw [Int.ModEq, Int.toNat_of_nonneg nonneg, emod_emod]

/--
Definition of `onModCases_stop` / `onModCases_stop` 的定义

English:
definition onModCases_stop
  signature: (p : Sort*) (n : Nat) (a : Int)
  body: fun _ h => (Nat.not_lt.2 h.1 h.2.1).elim

中文:
定义 onModCases_stop
  签名: (p : Sort*) (n : 自然数) (a : 整数)
  定义体: fun _ h => (Nat.not_lt.2 h.1 h.2.1).elim
-/
@[inline] def onModCases_stop (p : Sort*) (n : Nat) (a : Int) : OnModCases n a n p :=
  fun _ h => (Nat.not_lt.2 h.1 h.2.1).elim

/--
Definition of `onModCases_succ` / `onModCases_succ` 的定义

English:
definition onModCases_succ
  signature: {p : Sort*} {n : Nat} {a : Int} (b : Nat)
  body: fun z ⟨h₁, h₂⟩ => if e : b = z then h (e ▸ h₂.2) else H _ ⟨Nat.lt_of_le_of_ne h₁ e, h₂⟩

中文:
定义 onModCases_succ
  签名: {p : Sort*} {n : 自然数} {a : 整数} (b : 自然数)
  定义体: fun z ⟨h₁, h₂⟩ => if e : b = z then h (e ▸ h₂.2) else H _ ⟨Nat.lt_of_le_of_ne h₁ e, h₂⟩
-/
@[inline] def onModCases_succ {p : Sort*} {n : Nat} {a : Int} (b : Nat)
    (h : a ≡ OfNat.ofNat b [ZMOD OfNat.ofNat n] -> p) (H : OnModCases n a (Nat.add b 1) p) :
    OnModCases n a b p :=
  fun z ⟨h₁, h₂⟩ => if e : b = z then h (e ▸ h₂.2) else H _ ⟨Nat.lt_of_le_of_ne h₁ e, h₂⟩

/--
Proves an expression of the form `OnModCases n a b p` where `n` and `b` are raw nat literals
and `b ≤ n`. Returns the list of subgoals `?gi : a ≡ i [ZMOD n] → p`.
-/
meta partial def proveOnModCases {u : Level} (n : Q(Nat)) (a : Q(Int)) (b : Q(Nat)) (p : Q(Sort u)) :
    MetaM (Q(OnModCases $n $a $b $p) × List MVarId) := do
  if n.natLit! <= b.natLit! then
haveI' : b =Q n := ⟨⟩
    pure (q(onModCases_stop $p $n $a), [])
  else
    let ty := q($a ≡ OfNat.ofNat $b [ZMOD OfNat.ofNat $n] -> $p)
    let g ← mkFreshExprMVarQ ty
    have b1 : Q(Nat) := mkRawNatLit (b.natLit! + 1)
haveI' : b1 =Q ($b).succ := ⟨⟩
    let (pr, acc) ← proveOnModCases n a b1 p
    pure (q(onModCases_succ $b $g $pr), g.mvarId! :: acc)

/--
Int case of `mod_cases h : e % n`.
-/
meta def modCases (h : TSyntax `Lean.binderIdent) (e : Q(Int)) (n : Nat) : TacticM Unit := do
  let ⟨u, p, g⟩ ← inferTypeQ (.mvar (← getMainGoal))
  have lit : Q(Nat) := mkRawNatLit n
have p₁ : Nat.ble 1 lit =Q true := ⟨⟩
  let (p₂, gs) ← proveOnModCases lit e q(nat_lit 0) p
  let gs ← gs.mapM fun g => do
    let (fvar, g) ← match h with
    | `(binderIdent| $n:ident) => g.intro n.getId
    | _ => g.intro `H
g.withContext (Expr.fvar fvar).addLocalVarInfoForBinderIdent h
    pure g
  g.mvarId!.assign q(onModCases_start $p $e $lit $p₁ $p₂)
  replaceMainGoal gs

end IntMod

namespace NatMod

/--
Definition of `OnModCases` / `OnModCases` 的定义

English:
definition OnModCases
  signature: (n : Nat) (a : Nat) (lb : Nat) (p : Sort _)
  body: forall m, lb <= m ∧ m < n ∧ a ≡ m [MOD n] -> p

中文:
定义 OnModCases
  签名: (n : 自然数) (a : 自然数) (lb : 自然数) (p : Sort _)
  定义体: forall m, lb <= m ∧ m < n ∧ a ≡ m [MOD n] -> p
-/
@[expose] def OnModCases (n : Nat) (a : Nat) (lb : Nat) (p : Sort _) :=
  forall m, lb <= m ∧ m < n ∧ a ≡ m [MOD n] -> p

/--
Definition of `onModCases_start` / `onModCases_start` 的定义

English:
definition onModCases_start
  signature: (p : Sort _) (a : Nat) (n : Nat) (hn : Nat.ble 1 n = true)
  body: H (a % n) by
    refine ⟨Nat.zero_le _, ?_, ?_⟩
    · exact Nat.mod_lt _ (Nat.le_of_ble_eq_true hn)
    · rw [Nat.ModEq, Nat.mod_mod]

中文:
定义 onModCases_start
  签名: (p : Sort _) (a : 自然数) (n : 自然数) (hn : 自然数.ble 1 n = true)
  定义体: H (a % n) by
    refine ⟨Nat.zero_le _, ?_, ?_⟩
    · exact Nat.mod_lt _ (Nat.le_of_ble_eq_true hn)
    · rw [Nat.ModEq, Nat.mod_mod]
-/
@[inline] def onModCases_start (p : Sort _) (a : Nat) (n : Nat) (hn : Nat.ble 1 n = true)
    (H : OnModCases n a (nat_lit 0) p) : p :=
H (a % n) by
    refine ⟨Nat.zero_le _, ?_, ?_⟩
    · exact Nat.mod_lt _ (Nat.le_of_ble_eq_true hn)
    · rw [Nat.ModEq, Nat.mod_mod]


/--
Definition of `onModCases_stop` / `onModCases_stop` 的定义

English:
definition onModCases_stop
  signature: (p : Sort _) (n : Nat) (a : Nat)
  body: fun _ h => (Nat.not_lt.2 h.1 h.2.1).elim

中文:
定义 onModCases_stop
  签名: (p : Sort _) (n : 自然数) (a : 自然数)
  定义体: fun _ h => (Nat.not_lt.2 h.1 h.2.1).elim
-/
@[inline] def onModCases_stop (p : Sort _) (n : Nat) (a : Nat) : OnModCases n a n p :=
  fun _ h => (Nat.not_lt.2 h.1 h.2.1).elim

/--
Definition of `onModCases_succ` / `onModCases_succ` 的定义

English:
definition onModCases_succ
  signature: {p : Sort _} {n : Nat} {a : Nat} (b : Nat)
  body: fun z ⟨h₁, h₂⟩ => if e : b = z then h (e ▸ h₂.2) else H _ ⟨Nat.lt_of_le_of_ne h₁ e, h₂⟩

中文:
定义 onModCases_succ
  签名: {p : Sort _} {n : 自然数} {a : 自然数} (b : 自然数)
  定义体: fun z ⟨h₁, h₂⟩ => if e : b = z then h (e ▸ h₂.2) else H _ ⟨Nat.lt_of_le_of_ne h₁ e, h₂⟩
-/
@[inline] def onModCases_succ {p : Sort _} {n : Nat} {a : Nat} (b : Nat)
    (h : a ≡ b [MOD n] -> p) (H : OnModCases n a (Nat.add b 1) p) :
    OnModCases n a b p :=
  fun z ⟨h₁, h₂⟩ => if e : b = z then h (e ▸ h₂.2) else H _ ⟨Nat.lt_of_le_of_ne h₁ e, h₂⟩

/--
Proves an expression of the form `OnModCases n a b p` where `n` and `b` are raw nat literals
and `b ≤ n`. Returns the list of subgoals `?gi : a ≡ i [MOD n] → p`.
-/
meta partial def proveOnModCases {u : Level} (n : Q(Nat)) (a : Q(Nat)) (b : Q(Nat)) (p : Q(Sort u)) :
    MetaM (Q(OnModCases $n $a $b $p) × List MVarId) := do
  if n.natLit! <= b.natLit! then
have : b =Q n := ⟨⟩
    pure (q(onModCases_stop $p $n $a), [])
  else
    let ty := q($a ≡ $b [MOD $n] -> $p)
    let g ← mkFreshExprMVarQ ty
    let ((pr : Q(OnModCases $n $a (Nat.add $b 1) $p)), acc) ←
      proveOnModCases n a (mkRawNatLit (b.natLit! + 1)) p
    pure (q(onModCases_succ $b $g $pr), g.mvarId! :: acc)

/--
Nat case of `mod_cases h : e % n`.
-/
meta def modCases (h : TSyntax `Lean.binderIdent) (e : Q(Nat)) (n : Nat) : TacticM Unit := do
  let ⟨u, p, g⟩ ← inferTypeQ (.mvar (← getMainGoal))
  have lit : Q(Nat) := mkRawNatLit n
  let p₁ : Q(Nat.ble 1 $lit = true) := (q(Eq.refl true) : Expr)
  let (p₂, gs) ← proveOnModCases lit e q(nat_lit 0) p
  let gs ← gs.mapM fun g => do
    let (fvar, g) ← match h with
    | `(binderIdent| $n:ident) => g.intro n.getId
    | _ => g.intro `H
g.withContext (Expr.fvar fvar).addLocalVarInfoForBinderIdent h
    pure g
  g.mvarId!.assign q(onModCases_start $p $e $lit $p₁ $p₂)
  replaceMainGoal gs

end NatMod

/--
`mod_cases h : e % n`, where `n` is a positive numeral and `e` is an expression of type `ℕ` or `ℤ`,
performs a case disjunction on the value of `e` modulo `n`. If `e : ℤ`, the goal is split into
`n` subgoals containing the new hypotheses `h : e ≡ 0 [ZMOD n]`, ..., `h : e ≡ n-1 [ZMOD n]`
respectively. If `e : ℕ` instead, then the hypotheses contain `[MOD n]` instead of `[ZMOD n]`.

* `mod_cases e % n`, with `h` omitted, gives the default name `H` to the new hypotheses.
-/
syntax "mod_cases " (atomic(binderIdent ":"))? term:71 " % " num : tactic

elab_rules : tactic
  | `(tactic| mod_cases $[$h :]? $e % $n) => do
    let n := n.getNat
    if n == 0 then Elab.throwUnsupportedSyntax
    let h := h.getD (← `(binderIdent| _))
    withMainContext do
    let e ← Tactic.elabTerm e none
    let α : Q(Type) ← inferType e
    match α with
    | ~q(Int) => IntMod.modCases h e n
    | ~q(Nat) => NatMod.modCases h e n
    | _ => throwError "mod_cases only works with Int and Nat"

end Mathlib.Tactic.ModCases
