/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public meta import Mathlib.Util.Qq
public meta import Mathlib.Tactic.Linarith.Datatypes
public import Mathlib.Tactic.Linarith.Parsing

/-!
# Deriving a proof of false

`linarith` uses an untrusted oracle to produce a certificate of unsatisfiability.
It needs to do some proof reconstruction work to turn this into a proof term.
This file implements the reconstruction.

## Main declarations

The public facing declaration in this file is `proveFalseByLinarith`.
-/

public meta section

open Lean Elab Tactic Meta

namespace Qq

variable {u : Level}

/--
Definition of `ofNatQ` / `ofNatQ` 的定义

English:
definition ofNatQ
  signature: (α : Q(Type $u)) (_ : Q(Semiring $α)) (n : Nat)
  body: match n with
  | 0 => q(0 : $α)
  | 1 => q(1 : $α)
  | k+2 =>
    have lit : Q(Nat) := mkRawNatLit n
    have k : Q(Nat) := mkRawNatLit k
haveI : lit =Q k + 2 := ⟨⟩
    q(OfNat.ofNat $lit)

中文:
定义 ofNatQ
  签名: (α : Q(Type $u)) (_ : Q(Semiring $α)) (n : 自然数)
  定义体: match n with
  | 0 => q(0 : $α)
  | 1 => q(1 : $α)
  | k+2 =>
    have lit : Q(Nat) := mkRawNatLit n
    have k : Q(Nat) := mkRawNatLit k
haveI : lit =Q k + 2 := ⟨⟩
    q(OfNat.ofNat $lit)

Depends on / 依赖: OfNat.ofNat, mkRawNatLit
-/
def ofNatQ (α : Q(Type $u)) (_ : Q(Semiring $α)) (n : Nat) : Q($α) :=
  match n with
  | 0 => q(0 : $α)
  | 1 => q(1 : $α)
  | k+2 =>
    have lit : Q(Nat) := mkRawNatLit n
    have k : Q(Nat) := mkRawNatLit k
haveI : lit =Q k + 2 := ⟨⟩
    q(OfNat.ofNat $lit)

end Qq

namespace Mathlib.Tactic.Linarith

open Ineq
open Qq

/-! ### Auxiliary functions for assembling proofs -/

/--
Definition of `mulExpr'` / `mulExpr'` 的定义

English:
definition mulExpr'
  signature: {u : Level} (n : Nat) {α : Q(Type $u)} (inst : Q(Semiring $α)) (e : Q($α))
  body: if n = 1 then e else
    let n := ofNatQ α inst n
    q($n * $e)

中文:
定义 mulExpr'
  签名: {u : Level} (n : 自然数) {α : Q(Type $u)} (inst : Q(Semiring $α)) (e : Q($α))
  定义体: if n = 1 then e else
    let n := ofNatQ α inst n
    q($n * $e)

Depends on / 依赖: ofNatQ
-/
def mulExpr' {u : Level} (n : Nat) {α : Q(Type $u)} (inst : Q(Semiring $α)) (e : Q($α)) : Q($α) :=
  if n = 1 then e else
    let n := ofNatQ α inst n
    q($n * $e)

/--
Definition of `mulExpr` / `mulExpr` 的定义

English:
definition mulExpr
  signature: (n : Nat) (e : Expr)
  body: do
  let ⟨_, α, e⟩ ← inferTypeQ' e
  let inst : Q(Semiring $α) ← synthInstanceQ q(Semiring $α)
  return mulExpr' n inst e

中文:
定义 mulExpr
  签名: (n : 自然数) (e : Expr)
  定义体: do
  let ⟨_, α, e⟩ ← inferTypeQ' e
  let inst : Q(Semiring $α) ← synthInstanceQ q(Semiring $α)
  return mulExpr' n inst e
-/
def mulExpr (n : Nat) (e : Expr) : MetaM Expr := do
  let ⟨_, α, e⟩ ← inferTypeQ' e
  let inst : Q(Semiring $α) ← synthInstanceQ q(Semiring $α)
  return mulExpr' n inst e

/--
Definition of `addExprs'` / `addExprs'` 的定义

English:
definition addExprs'
  signature: {u : Level} {α : Q(Type $u)} (_inst : Q(AddMonoid $α))

中文:
定义 addExprs'
  签名: {u : Level} {α : Q(Type $u)} (_inst : Q(AddMonoid $α))
-/
def addExprs' {u : Level} {α : Q(Type $u)} (_inst : Q(AddMonoid $α)) : List Q($α) -> Q($α)
  | [] => q(0)
  | h::t => go h t
where
  /-- Inner loop for `addExprs'`. -/
  go (p : Q($α)) : List Q($α) -> Q($α)
  | [] => p
  | [q] => q($p + $q)
  | q::t => go q($p + $q) t

/--
Definition of `addExprs` / `addExprs` 的定义

English:
definition addExprs
  signature: : List Expr -> MetaM Expr

中文:
定义 addExprs
  签名: : List Expr -> MetaM Expr
-/
def addExprs : List Expr -> MetaM Expr
  | [] => return q(0) -- This may not be of the intended type; use with caution.
  | L@(h::_) => do
    let ⟨_, α, _⟩ ← inferTypeQ' h
    let inst : Q(AddMonoid $α) ← synthInstanceQ q(AddMonoid $α)
    -- This is not type safe; we just assume all the `Expr`s in the tail have the same type:
    return addExprs' inst L

/--
Definition of `addIneq` / `addIneq` 的定义

English:
definition addIneq
  signature: : Ineq -> Ineq -> (Name × Ineq)

中文:
定义 addIneq
  签名: : Ineq -> Ineq -> (Name × Ineq)
-/
def addIneq : Ineq -> Ineq -> (Name × Ineq)
  | eq, eq => (``Linarith.eq_of_eq_of_eq, eq)
  | eq, le => (``Linarith.le_of_eq_of_le, le)
  | eq, lt => (``Linarith.lt_of_eq_of_lt, lt)
  | le, eq => (``Linarith.le_of_le_of_eq, le)
  | le, le => (``Linarith.add_nonpos, le)
  | le, lt => (``Linarith.add_lt_of_le_of_neg, lt)
  | lt, eq => (``Linarith.lt_of_lt_of_eq, lt)
  | lt, le => (``Linarith.add_lt_of_neg_of_le, lt)
  | lt, lt => (``Linarith.add_neg, lt)

/--
Definition of `mkLTZeroProof` / `mkLTZeroProof` 的定义

English:
definition mkLTZeroProof
  signature: : List (Expr × Nat) -> MetaM Expr

中文:
定义 mkLTZeroProof
  签名: : List (Expr × 自然数) -> MetaM Expr
-/
def mkLTZeroProof : List (Expr × Nat) -> MetaM Expr
  | [] => throwError "no linear hypotheses found"
  | [(h, c)] => do
      let (_, t) ← mkSingleCompZeroOf c h
      return t
  | ((h, c)::t) => do
      let (iq, h') ← mkSingleCompZeroOf c h
      let (_, t) ← t.foldlM (fun pr ce => step pr.1 pr.2 ce.1 ce.2) (iq, h')
      return t
where
  /--
  `step c pf npf coeff` assumes that `pf` is a proof of `t1 R1 0` and `npf` is a proof
  of `t2 R2 0`. It uses `mkSingleCompZeroOf` to prove `t1 + coeff*t2 R 0`, and returns `R`
  along with this proof.
  -/
  step (c : Ineq) (pf npf : Expr) (coeff : Nat) : MetaM (Ineq × Expr) := do
    let (iq, h') ← mkSingleCompZeroOf coeff npf
    let (nm, niq) := addIneq c iq
    return (niq, ← mkAppM nm #[pf, h'])

/--
Definition of `leftOfIneqProof` / `leftOfIneqProof` 的定义

English:
definition leftOfIneqProof
  signature: (prf : Expr)
  body: do
  let (_, _, t, _) ← (← inferType prf).ineq?
  return t

中文:
定义 leftOfIneqProof
  签名: (prf : Expr)
  定义体: do
  let (_, _, t, _) ← (← inferType prf).ineq?
  return t
-/
def leftOfIneqProof (prf : Expr) : MetaM Expr := do
  let (_, _, t, _) ← (← inferType prf).ineq?
  return t

/--
Definition of `typeOfIneqProof` / `typeOfIneqProof` 的定义

English:
definition typeOfIneqProof
  signature: (prf : Expr)
  body: do
  let (_, ty, _) ← (← inferType prf).ineq?
  return ty

中文:
定义 typeOfIneqProof
  签名: (prf : Expr)
  定义体: do
  let (_, ty, _) ← (← inferType prf).ineq?
  return ty
-/
def typeOfIneqProof (prf : Expr) : MetaM Expr := do
  let (_, ty, _) ← (← inferType prf).ineq?
  return ty

/--
Definition of `mkNegOneLtZeroProof` / `mkNegOneLtZeroProof` 的定义

English:
definition mkNegOneLtZeroProof
  signature: (tp : Expr)
  body: do
  let zero_lt_one ← mkAppOptM ``Linarith.zero_lt_one #[tp, none, none, none]
  mkAppM `neg_neg_of_pos #[zero_lt_one]

中文:
定义 mkNegOneLtZeroProof
  签名: (tp : Expr)
  定义体: do
  let zero_lt_one ← mkAppOptM ``Linarith.zero_lt_one #[tp, none, none, none]
  mkAppM `neg_neg_of_pos #[zero_lt_one]
-/
def mkNegOneLtZeroProof (tp : Expr) : MetaM Expr := do
  let zero_lt_one ← mkAppOptM ``Linarith.zero_lt_one #[tp, none, none, none]
  mkAppM `neg_neg_of_pos #[zero_lt_one]

/--
Definition of `addNegEqProofsIdx` / `addNegEqProofsIdx` 的定义

English:
definition addNegEqProofsIdx
  signature: : List (Expr × Nat) -> MetaM (List (Expr × Nat))
  body: mkAppN (← mkAppM `Iff.mpr #[← mkAppOptM ``neg_eq_zero #[none, none, t]]) #[h]
      let tl ← addNegEqProofsIdx tl
      return (h, i)::(nep, i)::tl
    | _ => return (h, i) :: (← addNegEqProofsIdx tl)

中文:
定义 addNegEqProofsIdx
  签名: : List (Expr × 自然数) -> MetaM (List (Expr × 自然数))
  定义体: mkAppN (← mkAppM `Iff.mpr #[← mkAppOptM ``neg_eq_zero #[none, none, t]]) #[h]
      let tl ← addNegEqProofsIdx tl
      return (h, i)::(nep, i)::tl
    | _ => return (h, i) :: (← addNegEqProofsIdx tl)

Depends on / 依赖: Iff.mpr, addNegEqProofsIdx, mkAppM, mkAppN, mkAppOptM, neg_eq_zero, return
-/
def addNegEqProofsIdx : List (Expr × Nat) -> MetaM (List (Expr × Nat))
  | [] => return []
  | (⟨h, i⟩::tl) => do
    let (iq, t) ← parseCompAndExpr (← inferType h)
    match iq with
    | Ineq.eq => do
      let nep :=
        mkAppN (← mkAppM `Iff.mpr #[← mkAppOptM ``neg_eq_zero #[none, none, t]]) #[h]
      let tl ← addNegEqProofsIdx tl
      return (h, i)::(nep, i)::tl
    | _ => return (h, i) :: (← addNegEqProofsIdx tl)

/--
Definition of `proveEqZeroUsing` / `proveEqZeroUsing` 的定义

English:
definition proveEqZeroUsing
  signature: (tac : TacticM Unit) (e : Expr)
  body: do
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let _h : Q(Zero $α) ← synthInstanceQ q(Zero $α)
  synthesizeUsing' q($e = 0) tac

中文:
定义 proveEqZeroUsing
  签名: (tac : TacticM Unit) (e : Expr)
  定义体: do
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let _h : Q(Zero $α) ← synthInstanceQ q(Zero $α)
  synthesizeUsing' q($e = 0) tac
-/
def proveEqZeroUsing (tac : TacticM Unit) (e : Expr) : MetaM Expr := do
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let _h : Q(Zero $α) ← synthInstanceQ q(Zero $α)
  synthesizeUsing' q($e = 0) tac

/-! #### The main method -/

/--
Definition of `proveFalseByLinarith` / `proveFalseByLinarith` 的定义

English:
definition proveFalseByLinarith
  signature: (transparency : TransparencyMode) (oracle : CertificateOracle)
  body: l.zipIdx
let l' ← detailTrace "addNegEqProofs" addNegEqProofsIdx lidx
      let inputsTagged : List (Expr × Option Nat) ←
detailTrace "mkNegOneLtZeroProof"
          return ((← mkNegOneLtZeroProof (← typeOfIneqProof h)), none) ::
            (l'.reverse.map fun ⟨e, i⟩ => (e, some i))
      let input

中文:
定义 proveFalseByLinarith
  签名: (transparency : TransparencyMode) (oracle : CertificateOracle)
  定义体: l.zipIdx
let l' ← detailTrace "addNegEqProofs" addNegEqProofsIdx lidx
      let inputsTagged : List (Expr × Option Nat) ←
detailTrace "mkNegOneLtZeroProof"
          return ((← mkNegOneLtZeroProof (← typeOfIneqProof h)), none) ::
            (l'.reverse.map fun ⟨e, i⟩ => (e, some i))
      let input

Depends on / 依赖: l.zipIdx, zipIdx
-/
def proveFalseByLinarith (transparency : TransparencyMode) (oracle : CertificateOracle)
    (discharger : TacticM Unit) : MVarId -> List Expr -> MetaM (Expr × List Nat)
  | _, [] => throwError "no args to linarith"
  | g, l@(h::_) => do
      Lean.Core.checkSystem decl_name%.toString
      -- for the elimination to work properly, we must add a proof of `-1 < 0` to the list,
      -- along with negated equality proofs.
      let lidx := l.zipIdx
let l' ← detailTrace "addNegEqProofs" addNegEqProofsIdx lidx
      let inputsTagged : List (Expr × Option Nat) ←
detailTrace "mkNegOneLtZeroProof"
          return ((← mkNegOneLtZeroProof (← typeOfIneqProof h)), none) ::
            (l'.reverse.map fun ⟨e, i⟩ => (e, some i))
      let inputs := inputsTagged.map Prod.fst
      trace[linarith.detail] "inputs:{indentD <| toMessageData (← inputs.mapM inferType)}"
let (comps, max_var) ← detailTrace "linearFormsAndMaxVar"
        linearFormsAndMaxVar transparency inputs
      trace[linarith.detail] "comps:{indentD <| toMessageData comps}"
      -- perform the elimination and fail if no contradiction is found.
      let certificate : Std.HashMap Nat Nat ←
        withTraceNode `linarith (fun _ => return m!" Invoking oracle") do
          let certificate ←
            try
              oracle.produceCertificate comps max_var
            catch e =>
              trace[linarith] e.toMessageData
              throwError "linarith failed to find a contradiction"
          trace[linarith] "found a contradiction: {certificate.toList}"
          return certificate
      let (sm, zip, idxs) ←
        withTraceNode `linarith (fun _ => return m!" Building final expression") do
          let enum_inputs := inputsTagged.zipIdx
          -- construct a list pairing nonzero coeffs with the proof of their corresponding
          -- comparison and track the original index
          let used := enum_inputs.filterMap fun ⟨⟨e, orig?⟩, n⟩ =>
            (certificate[n]?).map fun c => (e, c, orig?)
          let zip := used.map fun ⟨e, c, _⟩ => (e, c)
          let mls ← used.mapM fun ⟨e, c, _⟩ => do mulExpr c (← leftOfIneqProof e)
          -- `sm` is the sum of input terms, scaled to cancel out all variables.
          let sm ← addExprs mls
          -- let sm ← instantiateMVars sm
          trace[linarith] "{indentD sm}\nshould be both 0 and negative"
          let idxs :=
            (used.foldl (fun acc (_, _, orig?) =>
                match orig? with
                | some i => i :: acc
                | none => acc) []).eraseDups
          return (sm, zip, idxs)
      -- we prove that `sm = 0`, typically with `ring`.
let sm_eq_zero ← detailTrace "proveEqZeroUsing" proveEqZeroUsing discharger sm
      -- we also prove that `sm < 0`
let sm_lt_zero ← detailTrace "mkLTZeroProof" mkLTZeroProof zip
      let pf ← detailTrace "Linarith.lt_irrefl" do
        -- this is a contradiction.
        let pftp ← inferType sm_lt_zero
        let ⟨_, nep, _⟩ ← g.rewrite pftp sm_eq_zero
        let pf' ← mkAppM ``Eq.mp #[nep, sm_lt_zero]
        mkAppM ``Linarith.lt_irrefl #[pf']
      return (pf, idxs)
where
  /-- Log `f` under `linarith.detail`, with the provided name. -/
  detailTrace {α} (s : String) (f : MetaM α) : MetaM α :=
    withTraceNode `linarith.detail (fun _ => return m!"{s}") f

end Mathlib.Tactic.Linarith
