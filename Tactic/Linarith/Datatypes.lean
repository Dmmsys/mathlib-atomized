/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Util.SynthesizeUsing

/-!
# Datatypes for `linarith`

Some of the data structures here are used in multiple parts of the tactic.
We split them into their own file.

This file also contains a few convenient auxiliary functions.
-/

public meta section

open Lean Elab Tactic Meta Qq

initialize registerTraceClass `linarith
initialize registerTraceClass `linarith.detail

namespace Mathlib.Tactic.Linarith

/--
Definition of `linarithGetProofsMessage` / `linarithGetProofsMessage` 的定义

English:
definition linarithGetProofsMessage
  signature: (l : List Expr)
  body: do
  return m!"{← l.mapM fun e => do instantiateMVars (← inferType e)}"

中文:
定义 linarithGetProofsMessage
  签名: (l : 列表 Expr)
  定义体: do
  return m!"{← l.mapM fun e => do instantiateMVars (← inferType e)}"
-/
def linarithGetProofsMessage (l : List Expr) : MetaM MessageData := do
  return m!"{← l.mapM fun e => do instantiateMVars (← inferType e)}"

/--
Definition of `linarithTraceProofs` / `linarithTraceProofs` 的定义

English:
definition linarithTraceProofs
  signature: {α} [ToMessageData α] (s : α) (l : List Expr)
  body: do
  if ← isTracingEnabledFor `linarith then
addRawTrace .trace { cls := `linarith } (toMessageData s) #[← linarithGetProofsMessage l]

中文:
定义 linarithTraceProofs
  签名: {α} [ToMessageData α] (s : α) (l : 列表 Expr)
  定义体: do
  if ← isTracingEnabledFor `linarith then
addRawTrace .trace { cls := `linarith } (toMessageData s) #[← linarithGetProofsMessage l]
-/
def linarithTraceProofs {α} [ToMessageData α] (s : α) (l : List Expr) : MetaM Unit := do
  if ← isTracingEnabledFor `linarith then
addRawTrace .trace { cls := `linarith } (toMessageData s) #[← linarithGetProofsMessage l]

/-! ### Linear expressions -/

/--
Definition of `Linexp` / `Linexp` 的定义

English:
abbreviation Linexp
  signature: : Type
  body: List (Nat × Int)

中文:
缩写 Linexp
  签名: : 类型
  定义体: List (Nat × Int)
-/
abbrev Linexp : Type := List (Nat × Int)

namespace Linexp
/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: : Linexp -> Linexp -> Linexp
  body: z1 + z2
    if sum = 0 then add t1 t2 else (n1, sum)::add t1 t2

中文:
定义 add
  签名: : Linexp -> Linexp -> Linexp
  定义体: z1 + z2
    if sum = 0 then add t1 t2 else (n1, sum)::add t1 t2
-/
partial def add : Linexp -> Linexp -> Linexp
| [], a => a
| a, [] => a
| (a@(n1,z1)::t1), (b@(n2,z2)::t2) =>
  if n1 < n2 then b::add (a::t1) t2
  else if n2 < n1 then a::add t1 (b::t2)
  else
    let sum := z1 + z2
    if sum = 0 then add t1 t2 else (n1, sum)::add t1 t2

/--
Definition of `scale` / `scale` 的定义

English:
definition scale
  signature: (c : Int) (l : Linexp)
  body: if c = 0 then []
  else if c = 1 then l
  else l.map fun ⟨n, z⟩ => (n, z*c)

中文:
定义 scale
  签名: (c : 整数) (l : Linexp)
  定义体: if c = 0 then []
  else if c = 1 then l
  else l.map fun ⟨n, z⟩ => (n, z*c)

Depends on / 依赖: l.map
-/
def scale (c : Int) (l : Linexp) : Linexp :=
  if c = 0 then []
  else if c = 1 then l
  else l.map fun ⟨n, z⟩ => (n, z*c)

/--
Definition of `get` / `get` 的定义

English:
definition get
  signature: (n : Nat)

中文:
定义 get
  签名: (n : 自然数)

Depends on / 依赖: OrderTop, PartialOrder, PseudoEpimorphismClass, PseudoEpimorphismClass.toTopHomClass, toTopHomClass
-/
def get (n : Nat) : Linexp -> Option Int
  | [] => none
  | ((a, b)::t) =>
    if a < n then none
    else if a = n then some b
    else get n t

/--
Definition of `contains` / `contains` 的定义

English:
definition contains
  signature: (n : Nat)
  body: Option.isSome ∘ get n

中文:
定义 contains
  签名: (n : 自然数)
  定义体: Option.isSome ∘ get n

Depends on / 依赖: EsakiaHomClass, EsakiaHomClass.toPseudoEpimorphismClass, Option.isSome, Preorder, TopologicalSpace, isSome, toPseudoEpimorphismClass
-/
def contains (n : Nat) : Linexp -> Bool := Option.isSome ∘ get n

/--
Definition of `zfind` / `zfind` 的定义

English:
definition zfind
  signature: (n : Nat) (l : Linexp)
  body: match l.get n with
  | none => 0
  | some v => v

中文:
定义 zfind
  签名: (n : 自然数) (l : Linexp)
  定义体: match l.get n with
  | none => 0
  | some v => v

Depends on / 依赖: l.get
-/
def zfind (n : Nat) (l : Linexp) : Int :=
  match l.get n with
  | none => 0
  | some v => v

/--
Definition of `vars` / `vars` 的定义

English:
definition vars
  signature: (l : Linexp)
  body: l.map Prod.fst

中文:
定义 vars
  签名: (l : Linexp)
  定义体: l.map Prod.fst

Depends on / 依赖: Prod.fst, l.map
-/
def vars (l : Linexp) : List Nat :=
  l.map Prod.fst

/--
Definition of `cmp` / `cmp` 的定义

English:
definition cmp
  signature: : Linexp -> Linexp -> Ordering

中文:
定义 cmp
  签名: : Linexp -> Linexp -> Ordering

Depends on / 依赖: OrderIsoClass, OrderIsoClass.toPseudoEpimorphismClass, Preorder, toPseudoEpimorphismClass
-/
def cmp : Linexp -> Linexp -> Ordering
  | [], [] => Ordering.eq
  | [], _ => Ordering.lt
  | _, [] => Ordering.gt
  | ((n1,z1)::t1), ((n2,z2)::t2) =>
    if n1 < n2 then Ordering.lt
    else if n2 < n1 then Ordering.gt
    else if z1 < z2 then Ordering.lt
    else if z2 < z1 then Ordering.gt
    else cmp t1 t2

end Linexp

/-! ### Comparisons with 0 -/

/--
Definition of `Comp` / `Comp` 的定义

English:
structure Comp
  parameters: : Type where
  axioms and operations (2):
    - str : Ineq
    - coeffs : Linexp

中文:
结构 复合
  参数: : 类型 where
  公理与运算 (2 个):
    - str : Ineq
    - coeffs : Linexp
-/
structure Comp : Type where
  /-- The strength of the comparison, `<`, `≤`, or `=`. -/
  str : Ineq
  /-- The coefficients of the comparison, stored as list of pairs `(i, a)`,
  where `i` is the index of a recorded atom, and `a` is the coefficient. -/
  coeffs : Linexp
deriving Inhabited, Repr

-- See https://github.com/leanprover/lean4/issues/10295
attribute [nolint unusedArguments] Mathlib.Tactic.Linarith.instReprComp.repr

/--
Definition of `Comp.vars` / `Comp.vars` 的定义

English:
definition Comp.vars
  signature: : Comp -> List Nat
  body: Linexp.vars ∘ Comp.coeffs

中文:
定义 复合.vars
  签名: : 复合 -> 列表 自然数
  定义体: Linexp.vars ∘ Comp.coeffs

Depends on / 依赖: Comp.coeffs, Linexp, Linexp.vars, coeffs
-/
def Comp.vars : Comp -> List Nat := Linexp.vars ∘ Comp.coeffs

/--
Definition of `Comp.coeffOf` / `Comp.coeffOf` 的定义

English:
definition Comp.coeffOf
  signature: (c : Comp) (a : Nat)
  body: c.coeffs.zfind a

中文:
定义 复合.coeffOf
  签名: (c : 复合) (a : 自然数)
  定义体: c.coeffs.zfind a

Depends on / 依赖: c.coeffs.zfind, coeffs
-/
def Comp.coeffOf (c : Comp) (a : Nat) : Int :=
  c.coeffs.zfind a

/--
Definition of `Comp.scale` / `Comp.scale` 的定义

English:
definition Comp.scale
  signature: (c : Comp) (n : Nat)
  body: { c with coeffs := c.coeffs.scale n }

中文:
定义 复合.scale
  签名: (c : 复合) (n : 自然数)
  定义体: { c with coeffs := c.coeffs.scale n }

Depends on / 依赖: c.coeffs.scale, coeffs
-/
def Comp.scale (c : Comp) (n : Nat) : Comp :=
  { c with coeffs := c.coeffs.scale n }

/--
Definition of `Comp.add` / `Comp.add` 的定义

English:
definition Comp.add
  signature: (c1 c2 : Comp)
  body: ⟨c1.str.max c2.str, c1.coeffs.add c2.coeffs⟩

中文:
定义 复合.add
  签名: (c1 c2 : 复合)
  定义体: ⟨c1.str.max c2.str, c1.coeffs.add c2.coeffs⟩

Depends on / 依赖: c1.coeffs.add, c1.str.max, c2.coeffs, c2.str, coeffs
-/
def Comp.add (c1 c2 : Comp) : Comp :=
  ⟨c1.str.max c2.str, c1.coeffs.add c2.coeffs⟩

/--
Definition of `Comp.cmp` / `Comp.cmp` 的定义

English:
definition Comp.cmp
  signature: : Comp -> Comp -> Ordering

中文:
定义 复合.cmp
  签名: : 复合 -> 复合 -> Ordering
-/
def Comp.cmp : Comp -> Comp -> Ordering
  | ⟨str1, coeffs1⟩, ⟨str2, coeffs2⟩ =>
    match str1.cmp str2 with
    | Ordering.lt => Ordering.lt
    | Ordering.gt => Ordering.gt
    | Ordering.eq => coeffs1.cmp coeffs2

/--
Definition of `Comp.isContr` / `Comp.isContr` 的定义

English:
definition Comp.isContr
  signature: (c : Comp)
  body: c.coeffs.isEmpty && c.str = Ineq.lt

中文:
定义 复合.isContr
  签名: (c : 复合)
  定义体: c.coeffs.isEmpty && c.str = Ineq.lt

Depends on / 依赖: Ineq.lt, c.coeffs.isEmpty, c.str, coeffs, isEmpty
-/
def Comp.isContr (c : Comp) : Bool := c.coeffs.isEmpty && c.str = Ineq.lt

/--
Instance `Comp.ToFormat` / 实例 `Comp.ToFormat`

English:
instance Comp.ToFormat
  signature: : ToFormat Comp
  body: ⟨fun p => format p.coeffs ++ toString p.str ++ "0"⟩

中文:
实例 复合.ToFormat
  签名: : ToFormat 复合
  定义体: ⟨fun p => format p.coeffs ++ toString p.str ++ "0"⟩

Depends on / 依赖: coeffs, format, p.coeffs, p.str, toString
-/
instance Comp.ToFormat : ToFormat Comp :=
  ⟨fun p => format p.coeffs ++ toString p.str ++ "0"⟩

/-! ### Parsing into linear form -/


/-! ### Control -/

/--
Definition of `PreprocessorBase` / `PreprocessorBase` 的定义

English:
structure PreprocessorBase
  parameters: : Type where
  axioms and operations (2):
    - name : Name  [default: by exact decl_name%]
    - description : String

中文:
结构 PreprocessorBase
  参数: : 类型 where
  公理与运算 (2 个):
    - name : Name  [默认: by exact decl_name%]
    - description : String

Depends on / 依赖: decl_name
-/
structure PreprocessorBase : Type where
  /-- The name of the preprocessor, populated automatically, to create linkable trace messages. -/
  name : Name := by exact decl_name%
  /-- The description of the preprocessor. -/
  description : String

/--
Definition of `Preprocessor` / `Preprocessor` 的定义

English:
structure Preprocessor
  parameters: : Type extends PreprocessorBase where
  extends: PreprocessorBase
  axioms and operations (1):
    - transform : Expr -> MetaM (List Expr)

中文:
结构 Preprocessor
  参数: : 类型 extends PreprocessorBase where
  继承: PreprocessorBase
  公理与运算 (1 个):
    - transform : Expr -> MetaM (列表 Expr)
-/
structure Preprocessor : Type extends PreprocessorBase where
  /-- Replace a hypothesis by a list of hypotheses. These expressions are the proof terms. -/
  transform : Expr -> MetaM (List Expr)

/--
Definition of `GlobalPreprocessor` / `GlobalPreprocessor` 的定义

English:
structure GlobalPreprocessor
  parameters: : Type extends PreprocessorBase where
  extends: PreprocessorBase
  axioms and operations (1):
    - transform : List Expr -> MetaM (List Expr)

中文:
结构 GlobalPreprocessor
  参数: : 类型 extends PreprocessorBase where
  继承: PreprocessorBase
  公理与运算 (1 个):
    - transform : 列表 Expr -> MetaM (列表 Expr)
-/
structure GlobalPreprocessor : Type extends PreprocessorBase where
  /-- Replace the collection of all hypotheses with new hypotheses.
  These expressions are proof terms. -/
  transform : List Expr -> MetaM (List Expr)

/--
Definition of `Branch` / `Branch` 的定义

English:
definition Branch
  signature: : Type
  body: MVarId × List Expr

中文:
定义 Branch
  签名: : 类型
  定义体: MVarId × List Expr
-/
@[expose] def Branch : Type := MVarId × List Expr

/--
Definition of `GlobalBranchingPreprocessor` / `GlobalBranchingPreprocessor` 的定义

English:
structure GlobalBranchingPreprocessor
  parameters: : Type extends PreprocessorBase where
  extends: PreprocessorBase
  axioms and operations (1):
    - transform : MVarId -> List Expr -> MetaM (List Branch)

中文:
结构 GlobalBranchingPreprocessor
  参数: : 类型 extends PreprocessorBase where
  继承: PreprocessorBase
  公理与运算 (1 个):
    - transform : MVarId -> 列表 Expr -> MetaM (列表 Branch)
-/
structure GlobalBranchingPreprocessor : Type extends PreprocessorBase where
  /-- Given a goal, and a list of hypotheses,
  produce a list of pairs (consisting of a goal and list of hypotheses). -/
  transform : MVarId -> List Expr -> MetaM (List Branch)

/--
Definition of `Preprocessor.globalize` / `Preprocessor.globalize` 的定义

English:
definition Preprocessor.globalize
  signature: (pp : Preprocessor)
  body: pp
  transform := List.foldrM (fun e ret => do return (← pp.transform e) ++ ret) []

中文:
定义 Preprocessor.globalize
  签名: (pp : Preprocessor)
  定义体: pp
  transform := List.foldrM (fun e ret => do return (← pp.transform e) ++ ret) []
-/
def Preprocessor.globalize (pp : Preprocessor) : GlobalPreprocessor where
  __ := pp
  transform := List.foldrM (fun e ret => do return (← pp.transform e) ++ ret) []

/--
Definition of `GlobalPreprocessor.branching` / `GlobalPreprocessor.branching` 的定义

English:
definition GlobalPreprocessor.branching
  signature: (pp : GlobalPreprocessor)
  body: pp
  transform := fun g l => do return [⟨g, ← pp.transform l⟩]

中文:
定义 GlobalPreprocessor.branching
  签名: (pp : GlobalPreprocessor)
  定义体: pp
  transform := fun g l => do return [⟨g, ← pp.transform l⟩]
-/
def GlobalPreprocessor.branching (pp : GlobalPreprocessor) : GlobalBranchingPreprocessor where
  __ := pp
  transform := fun g l => do return [⟨g, ← pp.transform l⟩]

/--
Definition of `GlobalBranchingPreprocessor.process` / `GlobalBranchingPreprocessor.process` 的定义

English:
definition GlobalBranchingPreprocessor.process
  signature: (pp : GlobalBranchingPreprocessor)
  body: g.withContext do
  withTraceNode `linarith (fun _ =>
      return m!"{.ofConstName pp.name}: {pp.description}") do
    let branches ← pp.transform g l
    if branches.length > 1 then
      trace[linarith] "Preprocessing: {pp.name} has branched, with branches:"
    for ⟨goal, hyps⟩ in branches do
   

中文:
定义 GlobalBranchingPreprocessor.process
  签名: (pp : GlobalBranchingPreprocessor)
  定义体: g.withContext do
  withTraceNode `linarith (fun _ =>
      return m!"{.ofConstName pp.name}: {pp.description}") do
    let branches ← pp.transform g l
    if branches.length > 1 then
      trace[linarith] "Preprocessing: {pp.name} has branched, with branches:"
    for ⟨goal, hyps⟩ in branches do
   

Depends on / 依赖: g.withContext, withContext
-/
def GlobalBranchingPreprocessor.process (pp : GlobalBranchingPreprocessor)
    (g : MVarId) (l : List Expr) : MetaM (List Branch) := g.withContext do
  withTraceNode `linarith (fun _ =>
      return m!"{.ofConstName pp.name}: {pp.description}") do
    let branches ← pp.transform g l
    if branches.length > 1 then
      trace[linarith] "Preprocessing: {pp.name} has branched, with branches:"
    for ⟨goal, hyps⟩ in branches do
      trace[linarith] (← goal.withContext <| linarithGetProofsMessage hyps)
    return branches

/--
Instance `PreprocessorToGlobalBranchingPreprocessor` / 实例 `PreprocessorToGlobalBranchingPreprocessor`

English:
instance PreprocessorToGlobalBranchingPreprocessor
  signature: :
  body: ⟨GlobalPreprocessor.branching ∘ Preprocessor.globalize⟩

中文:
实例 PreprocessorToGlobalBranchingPreprocessor
  签名: :
  定义体: ⟨GlobalPreprocessor.branching ∘ Preprocessor.globalize⟩

Depends on / 依赖: GlobalPreprocessor, GlobalPreprocessor.branching, Preprocessor, Preprocessor.globalize, branching, globalize
-/
instance PreprocessorToGlobalBranchingPreprocessor :
    Coe Preprocessor GlobalBranchingPreprocessor :=
  ⟨GlobalPreprocessor.branching ∘ Preprocessor.globalize⟩

/--
Instance `GlobalPreprocessorToGlobalBranchingPreprocessor` / 实例 `GlobalPreprocessorToGlobalBranchingPreprocessor`

English:
instance GlobalPreprocessorToGlobalBranchingPreprocessor
  signature: :
  body: ⟨GlobalPreprocessor.branching⟩

中文:
实例 GlobalPreprocessorToGlobalBranchingPreprocessor
  签名: :
  定义体: ⟨GlobalPreprocessor.branching⟩

Depends on / 依赖: GlobalPreprocessor, GlobalPreprocessor.branching, branching
-/
instance GlobalPreprocessorToGlobalBranchingPreprocessor :
    Coe GlobalPreprocessor GlobalBranchingPreprocessor :=
  ⟨GlobalPreprocessor.branching⟩

/--
Definition of `CertificateOracle` / `CertificateOracle` 的定义

English:
structure CertificateOracle
  parameters: : Type where
  axioms and operations (1):
    - produceCertificate((hyps : List Comp) (max_var : Nat)) : MetaM (Std.HashMap Nat Nat)

中文:
结构 CertificateOracle
  参数: : 类型 where
  公理与运算 (1 个):
    - produceCertificate((hyps : 列表 复合) (max_var : 自然数)) : MetaM (Std.HashMap 自然数 自然数)
-/
structure CertificateOracle : Type where
  /-- `produceCertificate hyps max_var` tries to derive a contradiction from the comparisons in
  `hyps` by eliminating all variables ≤ `max_var`.
  If successful, it returns a map `coeff : Nat → Nat` as a certificate.
  This map represents that we can find a contradiction by taking the sum `∑ (coeff i) * hyps[i]`. -/
  produceCertificate (hyps : List Comp) (max_var : Nat) : MetaM (Std.HashMap Nat Nat)

/-!
### Auxiliary functions

These functions are used by multiple modules, so we put them here for accessibility.
-/

/--
Definition of `parseCompAndExpr` / `parseCompAndExpr` 的定义

English:
definition parseCompAndExpr
  signature: (e : Expr)
  body: do
  let (rel, _, e, z) ← e.ineq?
  if z.zero? then return (rel, e) else throwError "invalid comparison, rhs not zero: {z}"

中文:
定义 parseCompAndExpr
  签名: (e : Expr)
  定义体: do
  let (rel, _, e, z) ← e.ineq?
  if z.zero? then return (rel, e) else throwError "invalid comparison, rhs not zero: {z}"
-/
def parseCompAndExpr (e : Expr) : MetaM (Ineq × Expr) := do
  let (rel, _, e, z) ← e.ineq?
  if z.zero? then return (rel, e) else throwError "invalid comparison, rhs not zero: {z}"

/--
Definition of `mkSingleCompZeroOf` / `mkSingleCompZeroOf` 的定义

English:
definition mkSingleCompZeroOf
  signature: (c : Nat) (h : Expr)
  body: do
  let tp ← inferType h
  let (iq, e) ← parseCompAndExpr tp
  if c = 0 then do
    let e' ← mkAppM ``zero_mul #[e]
    return (Ineq.eq, e')
  else if c = 1 then return (iq, h)
  else do
    let (_, tp, _) ← tp.ineq?
    let cpos : Q(Prop) ← mkAppM ``GT.gt #[(← tp.ofNat c), (← tp.ofNat 0)]
    let 

中文:
定义 mkSingleCompZeroOf
  签名: (c : 自然数) (h : Expr)
  定义体: do
  let tp ← inferType h
  let (iq, e) ← parseCompAndExpr tp
  if c = 0 then do
    let e' ← mkAppM ``zero_mul #[e]
    return (Ineq.eq, e')
  else if c = 1 then return (iq, h)
  else do
    let (_, tp, _) ← tp.ineq?
    let cpos : Q(Prop) ← mkAppM ``GT.gt #[(← tp.ofNat c), (← tp.ofNat 0)]
    let 
-/
def mkSingleCompZeroOf (c : Nat) (h : Expr) : MetaM (Ineq × Expr) := do
  let tp ← inferType h
  let (iq, e) ← parseCompAndExpr tp
  if c = 0 then do
    let e' ← mkAppM ``zero_mul #[e]
    return (Ineq.eq, e')
  else if c = 1 then return (iq, h)
  else do
    let (_, tp, _) ← tp.ineq?
    let cpos : Q(Prop) ← mkAppM ``GT.gt #[(← tp.ofNat c), (← tp.ofNat 0)]
    let ex ← synthesizeUsingTactic' cpos (← `(tactic| norm_num))
    let e' ← mkAppM iq.toConstMulName #[h, ex]
    return (iq, e')

end Mathlib.Tactic.Linarith
