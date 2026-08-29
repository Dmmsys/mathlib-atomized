/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Anne Baanen
-/
module

public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.TryThis
public import Mathlib.Util.AtomM.Recurse
public meta import Mathlib.Util.AtomM.Recurse

/-!
# `ring_nf` tactic

A tactic which uses `ring` to rewrite expressions. This can be used non-terminally to normalize
ring expressions in the goal such as `⊢ P (x + x + x)` ~> `⊢ P (x * 3)`, as well as being able to
prove some equations that `ring` cannot because they involve ring reasoning inside a subterm,
such as `sin (x + y) + sin (y + x) = 2 * sin (x + y)`.

-/

public meta section

namespace Mathlib.Tactic
open Lean Meta Qq

namespace RingNF
open Mathlib.Tactic.Ring

/--
Inductive type `RingMode` / 归纳类型 `RingMode`

English:
inductive RingMode
  parameters: where
  constructors (2):
    - SOP: 
    - raw: 

中文:
归纳类型 RingMode
  参数: where
  构造子 (2 个):
    - SOP: 
    - raw: 
-/
inductive RingMode where
  /-- Sum-of-products form, like `x + x * y * 2 + z ^ 2`. -/
  | SOP
  /-- Raw form: the representation `ring` uses internally. -/
  | raw
  deriving Inhabited, BEq, Repr

/--
Definition of `Config` / `Config` 的定义

English:
structure Config
  parameters: extends AtomM.Recurse.Config
  extends: AtomM.Recurse.Config
  axioms and operations (2):
    - ifUnchanged : = BehaviorIfUnchanged.error
    - mode : = RingMode.SOP

中文:
结构 余nfig
  参数: extends AtomM.Recurse.余nfig
  继承: AtomM.Recurse.余nfig
  公理与运算 (2 个):
    - ifUnchanged : = BehaviorIfUnchanged.error
    - mode : = RingMode.SOP

Depends on / 依赖: BehaviorIfUnchanged, BehaviorIfUnchanged.error
-/
structure Config extends AtomM.Recurse.Config where
  /-- How to behave if no progress is made: warn, error or keep silent. Default to error -/
  ifUnchanged := BehaviorIfUnchanged.error
  /-- The normalization style. -/
  mode := RingMode.SOP
  deriving Inhabited, BEq, Repr

-- See https://github.com/leanprover/lean4/issues/10295
attribute [nolint unusedArguments] Mathlib.Tactic.RingNF.instReprConfig.repr

/-- Function elaborating `RingNF.Config`. -/
declare_config_elab elabConfig Config

/--
Definition of `evalExpr` / `evalExpr` 的定义

English:
definition evalExpr
  signature: (e : Expr)
  body: do
let e ← withReducible whnf e
  guard e.isApp -- all interesting ring expressions are applications
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let sα ← synthInstanceQ q(CommSemiring $α)
  let c ← Common.mkCache sα
  let ⟨a, _, pa⟩ ← match
    (← Common.isAtomOrDerivable (ringCompute c) c q($e)) with
  | non

中文:
定义 evalExpr
  签名: (e : Expr)
  定义体: do
let e ← withReducible whnf e
  guard e.isApp -- all interesting ring expressions are applications
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let sα ← synthInstanceQ q(CommSemiring $α)
  let c ← Common.mkCache sα
  let ⟨a, _, pa⟩ ← match
    (← Common.isAtomOrDerivable (ringCompute c) c q($e)) with
  | non
-/
def evalExpr (e : Expr) : AtomM Simp.Result := do
let e ← withReducible whnf e
  guard e.isApp -- all interesting ring expressions are applications
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let sα ← synthInstanceQ q(CommSemiring $α)
  let c ← Common.mkCache sα
  let ⟨a, _, pa⟩ ← match
    (← Common.isAtomOrDerivable (ringCompute c) c q($e)) with
  | none => Common.eval rcNat (ringCompute c) c e
    -- `none` indicates that `eval` will find something algebraic.
  | some none => failure -- No point rewriting atoms
  | some (some r) => pure r -- Nothing algebraic for `eval` to use, but `norm_num` simplifies.
  pure { expr := a, proof? := pa }

variable {R : Type*} [CommSemiring R] {n d : Nat}

/--
theorem `add_assoc_rev` / 定理 `add_assoc_rev`

English:
theorem add_assoc_rev
  given: (a b c : R)
  statement: a + (b + c) = a + b + c
  proof: (add_assoc ..).symm

中文:
定理 add_assoc_rev
  条件: (a b c : R)
  结论: a + (b + c) = a + b + c
  证明: (add_assoc ..).symm

Depends on / 依赖: add_assoc
-/
theorem add_assoc_rev (a b c : R) : a + (b + c) = a + b + c := (add_assoc ..).symm
/--
theorem `mul_assoc_rev` / 定理 `mul_assoc_rev`

English:
theorem mul_assoc_rev
  given: (a b c : R)
  statement: a * (b * c) = a * b * c
  proof: (mul_assoc ..).symm

中文:
定理 mul_assoc_rev
  条件: (a b c : R)
  结论: a * (b * c) = a * b * c
  证明: (mul_assoc ..).symm

Depends on / 依赖: mul_assoc
-/
theorem mul_assoc_rev (a b c : R) : a * (b * c) = a * b * c := (mul_assoc ..).symm
/--
theorem `mul_neg` / 定理 `mul_neg`

English:
theorem mul_neg
  given: {R} [Ring R] (a b : R)
  statement: a * -b = -(a * b)
  proof: by simp

中文:
定理 mul_neg
  条件: {R} [环 R] (a b : R)
  结论: a * -b = -(a * b)
  证明: by simp
-/
theorem mul_neg {R} [Ring R] (a b : R) : a * -b = -(a * b) := by simp
/--
theorem `add_neg` / 定理 `add_neg`

English:
theorem add_neg
  given: {R} [Ring R] (a b : R)
  statement: a + -b = a - b
  proof: (sub_eq_add_neg ..).symm

中文:
定理 add_neg
  条件: {R} [环 R] (a b : R)
  结论: a + -b = a - b
  证明: (sub_eq_add_neg ..).symm

Depends on / 依赖: sub_eq_add_neg
-/
theorem add_neg {R} [Ring R] (a b : R) : a + -b = a - b := (sub_eq_add_neg ..).symm
/--
theorem `nat_rawCast_0` / 定理 `nat_rawCast_0`

English:
theorem nat_rawCast_0
  statement: (Nat.rawCast 0 : R) = 0
  proof: by simp

中文:
定理 nat_rawCast_0
  结论: (自然数.rawCast 0 : R) = 0
  证明: by simp
-/
theorem nat_rawCast_0 : (Nat.rawCast 0 : R) = 0 := by simp
/--
theorem `nat_rawCast_1` / 定理 `nat_rawCast_1`

English:
theorem nat_rawCast_1
  statement: (Nat.rawCast 1 : R) = 1
  proof: by simp

中文:
定理 nat_rawCast_1
  结论: (自然数.rawCast 1 : R) = 1
  证明: by simp
-/
theorem nat_rawCast_1 : (Nat.rawCast 1 : R) = 1 := by simp
/--
theorem `nat_rawCast_2` / 定理 `nat_rawCast_2`

English:
theorem nat_rawCast_2
  given: [Nat.AtLeastTwo n]
  statement: (Nat.rawCast n : R) = OfNat.ofNat n
  proof: rfl

中文:
定理 nat_rawCast_2
  条件: [自然数.AtLeastTwo n]
  结论: (自然数.rawCast n : R) = Of自然数.of自然数 n
  证明: rfl
-/
theorem nat_rawCast_2 [Nat.AtLeastTwo n] : (Nat.rawCast n : R) = OfNat.ofNat n := rfl
/--
theorem `int_rawCast_neg` / 定理 `int_rawCast_neg`

English:
theorem int_rawCast_neg
  given: {R} [Ring R]
  statement: (Int.rawCast (.negOfNat n) : R) = -Nat.rawCast n
  proof: by simp

中文:
定理 int_rawCast_neg
  条件: {R} [环 R]
  结论: (整数.rawCast (.negOf自然数 n) : R) = -自然数.rawCast n
  证明: by simp
-/
theorem int_rawCast_neg {R} [Ring R] : (Int.rawCast (.negOfNat n) : R) = -Nat.rawCast n := by simp
/--
theorem `nnrat_rawCast` / 定理 `nnrat_rawCast`

English:
theorem nnrat_rawCast
  given: {R} [DivisionSemiring R]
  proof: by simp

中文:
定理 nnrat_rawCast
  条件: {R} [除半环 R]
  证明: by simp
-/
theorem nnrat_rawCast {R} [DivisionSemiring R] :
    (NNRat.rawCast n d : R) = Nat.rawCast n / Nat.rawCast d := by simp
/--
theorem `rat_rawCast_neg` / 定理 `rat_rawCast_neg`

English:
theorem rat_rawCast_neg
  given: {R} [DivisionRing R]
  proof: by simp

中文:
定理 rat_rawCast_neg
  条件: {R} [除环 R]
  证明: by simp
-/
theorem rat_rawCast_neg {R} [DivisionRing R] :
    (Rat.rawCast (.negOfNat n) d : R) = Int.rawCast (.negOfNat n) / Nat.rawCast d := by simp

/--
Definition of `cleanup` / `cleanup` 的定义

English:
definition cleanup
  signature: (cfg : RingNF.Config) (r : Simp.Result)
  body: do
  match cfg.mode with
  | .raw => pure r
  | .SOP => do
    let thms : SimpTheorems := {}
    let thms ← [``add_zero, ``_root_.mul_one, ``_root_.pow_one, ``mul_neg, ``add_neg
      ].foldlM (·.addConst ·) thms
    let thms ← [``nat_rawCast_0, ``nat_rawCast_1, ``nat_rawCast_2, ``int_rawCast_neg,
 

中文:
定义 cleanup
  签名: (cfg : RingNF.余nfig) (r : Simp.Result)
  定义体: do
  match cfg.mode with
  | .raw => pure r
  | .SOP => do
    let thms : SimpTheorems := {}
    let thms ← [``add_zero, ``_root_.mul_one, ``_root_.pow_one, ``mul_neg, ``add_neg
      ].foldlM (·.addConst ·) thms
    let thms ← [``nat_rawCast_0, ``nat_rawCast_1, ``nat_rawCast_2, ``int_rawCast_neg,
 
-/
def cleanup (cfg : RingNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  match cfg.mode with
  | .raw => pure r
  | .SOP => do
    let thms : SimpTheorems := {}
    let thms ← [``add_zero, ``_root_.mul_one, ``_root_.pow_one, ``mul_neg, ``add_neg
      ].foldlM (·.addConst ·) thms
    let thms ← [``nat_rawCast_0, ``nat_rawCast_1, ``nat_rawCast_2, ``int_rawCast_neg,
      ``nnrat_rawCast, ``rat_rawCast_neg, ``add_assoc_rev, ``mul_assoc_rev
      ].foldlM (·.addConst · (post := false)) thms
    let ctx ← Simp.mkContext { zetaDelta := cfg.zetaDelta }
      (simpTheorems := #[thms])
      (congrTheorems := ← getSimpCongrTheorems)
pure ←
      r.mkEqTrans (← Simp.main r.expr ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1

/-- Overrides the default error message in `ring1` to use a prettified version of the goal. -/
initialize ringCleanupRef.set fun e => do
  return (← cleanup {} { expr := e }).expr

open Elab.Tactic Parser.Tactic

/--
`ring_nf` simplifies expressions in the language of commutative (semi)rings,
which rewrites all ring expressions into a normal form, allowing variables in the exponents.

`ring_nf` works as both a tactic and a conv tactic.

See also the `ring` tactic for solving a goal which is an equation in the language
of commutative (semi)rings.

* `ring_nf!` will use a more aggressive reducibility setting to identify atoms.
* `ring_nf (config := cfg)` allows for additional configuration (see `RingNF.Config`):
  * `red`: the reducibility setting (overridden by `!`)
  * `zetaDelta`: if true, local let variables can be unfolded (overridden by `!`)
  * `recursive`: if true, `ring_nf` will also recurse into atoms
* `ring_nf at l1 l2 ...` can be used to rewrite at the given locations.

Examples:
This can be used non-terminally to normalize ring expressions in the goal such as
`⊢ P (x + x + x)` ~> `⊢ P (x * 3)`, as well as being able to prove some equations that
`ring` cannot because they involve ring reasoning inside a subterm, such as
`sin (x + y) + sin (y + x) = 2 * sin (x + y)`.
-/
elab (name := ringNF) "ring_nf" tk:"!"? cfg:optConfig loc:(location)? : tactic => do
  let mut cfg ← elabConfig cfg
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  let m := AtomM.recurse s cfg.toConfig (wellBehavedDischarge := true) evalExpr (cleanup cfg)
  transformAtLocation (m ·) "ring_nf" loc cfg.ifUnchanged false

@[tactic_alt ringNF] macro "ring_nf!" cfg:optConfig loc:(location)? : tactic =>
  `(tactic| ring_nf ! $cfg:optConfig $(loc)?)

@[inherit_doc ringNF] syntax (name := ringNFConv) "ring_nf" "!"? optConfig : conv

/--
* `ring1_nf` additionally uses `ring_nf` to simplify in atoms.
* `ring1_nf!` will use a more aggressive reducibility setting
  to determine equality of atoms.
-/
tactic_extension ring1

@[tactic_alt ring1]
elab (name := ring1NF) "ring1_nf" tk:"!"? cfg:optConfig : tactic => do
  let mut cfg ← elabConfig cfg
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let s ← IO.mkRef {}
  liftMetaMAtMain fun g => AtomM.RecurseM.run s cfg.toConfig
(wellBehavedDischarge := true) evalExpr (cleanup cfg) proveEq g

@[tactic_alt ring1]
macro "ring1_nf!" cfg:optConfig : tactic =>
  `(tactic| ring1_nf ! $cfg:optConfig)

/--
Definition of `elabRingNFConv` / `elabRingNFConv` 的定义

English:
definition elabRingNFConv
  signature: : Tactic
  body: fun stx => match stx with
  | `(conv| ring_nf $[!%$tk]? $cfg:optConfig) => withMainContext do
    let mut cfg ← elabConfig cfg
    if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
    let s ← IO.mkRef {}
    Conv.applySimpResult
      (← AtomM.recurse s cfg.toConfig (wellBeha

中文:
定义 elabRingNFConv
  签名: : Tactic
  定义体: fun stx => match stx with
  | `(conv| ring_nf $[!%$tk]? $cfg:optConfig) => withMainContext do
    let mut cfg ← elabConfig cfg
    if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
    let s ← IO.mkRef {}
    Conv.applySimpResult
      (← AtomM.recurse s cfg.toConfig (wellBeha
-/
@[tactic ringNFConv] def elabRingNFConv : Tactic := fun stx => match stx with
  | `(conv| ring_nf $[!%$tk]? $cfg:optConfig) => withMainContext do
    let mut cfg ← elabConfig cfg
    if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
    let s ← IO.mkRef {}
    Conv.applySimpResult
      (← AtomM.recurse s cfg.toConfig (wellBehavedDischarge := true) evalExpr (cleanup cfg)
        (← instantiateMVars (← Conv.getLhs)))
  | _ => Elab.throwUnsupportedSyntax

@[inherit_doc ringNF] macro "ring_nf!" cfg:optConfig : conv =>
  `(conv| ring_nf ! $cfg:optConfig)

/--
`ring` solves equations in *commutative* (semi)rings, allowing for variables in the
exponent. If the goal is not appropriate for `ring` (e.g. not an equality) `ring_nf` will be
suggested. See also `ring1`, which fails if the goal is not an equality.

* `ring!` will use a more aggressive reducibility setting to determine equality of atoms.

Examples:
```
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
example (x : ℕ) (h : x * 2 > 5): x + x > 5 := by ring; assumption -- suggests ring_nf
```
-/
macro (name := ring) "ring" : tactic =>
  `(tactic| first | ring1 | try_this ring_nf
  "\n\nThe `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
  \nNote that `ring` works primarily in *commutative* rings. \
  If you have a noncommutative ring, abelian group or module, consider using \
  `noncomm_ring`, `abel` or `module` instead.")
@[tactic_alt ring] macro "ring!" : tactic =>
  `(tactic| first | ring1! | try_this ring_nf!
  "\n\nThe `ring!` tactic failed to close the goal. Use `ring_nf!` to obtain a normal form.
  \nNote that `ring!` works primarily in *commutative* rings. \
  If you have a noncommutative ring, abelian group or module, consider using \
  `noncomm_ring`, `abel` or `module` instead.")

/--
The tactic `ring` evaluates expressions in *commutative* (semi)rings.
This is the conv tactic version, which rewrites a target which is a ring equality to `True`.

See also the `ring` tactic.
-/
macro (name := ringConv) "ring" : conv =>
  `(conv| first | discharge => ring1 | try_this ring_nf
  "\n\nThe `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
  \nNote that `ring` works primarily in *commutative* rings. \
  If you have a noncommutative ring, abelian group or module, consider using \
  `noncomm_ring`, `abel` or `module` instead.")
@[inherit_doc ringConv] macro "ring!" : conv =>
  `(conv| first | discharge => ring1! | try_this ring_nf!
  "\n\nThe `ring!` tactic failed to close the goal. Use `ring_nf!` to obtain a normal form.
  \nNote that `ring!` works primarily in *commutative* rings. \
  If you have a noncommutative ring, abelian group or module, consider using \
  `noncomm_ring`, `abel` or `module` instead.")

end RingNF

end Mathlib.Tactic

/-!
We register `ring` with the `hint` tactic.
-/

register_hint 1000 ring
