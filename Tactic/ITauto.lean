/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.Basic -- shake: keep (Qq output dependency)
public meta import Mathlib.Util.AtomM
public meta import Qq
public import Batteries.Tactic.Exact
public import Batteries.Tactic.Init
public import Mathlib.Util.AtomM

/-!

# Intuitionistic tautology (`itauto`) decision procedure

The `itauto` tactic will prove any intuitionistic tautology. It implements the well-known
`G4ip` algorithm:
[Dyckhoff, *Contraction-free sequent calculi for intuitionistic logic*][dyckhoff_1992].

All built in propositional connectives are supported: `True`, `False`, `And`, `Or`, `→`,
`Not`, `Iff`, `Xor`, as well as `Eq` and `Ne` on propositions. Anything else, including definitions
and predicate logical connectives (`∀` and `∃`), are not supported, and will have to be
simplified or instantiated before calling this tactic.

The resulting proofs will never use any axioms except possibly `propext`, and `propext` is only
used if the input formula contains an equality of propositions `p = q`. Using `itauto!`, one can
enable the selective use of LEM for case splitting on specified propositions.

## Implementation notes

The core logic of the prover is in three functions:

* `prove : Context → IProp → StateM Nat (Bool × Proof)`: The main entry point.
  Gets a context and a goal, and returns a `proof` object or fails, using `StateM Nat` for the name
  generator.
* `search : Context → IProp → StateM Nat (Bool × Proof)`: Same meaning as `proof`, called during the
  search phase (see below).
* `Context.add : IProp → Proof → Context → Except (IProp → Proof) Context`: Adds a proposition with
  its proof into the context, but it also does some simplifications on the spot while doing so.
  It will either return the new context, or if it happens to notice a proof of false, it will
  return a function to compute a proof of any proposition in the original context.

The intuitionistic logic rules are separated into three groups:

* level 1: No splitting, validity preserving: apply whenever you can.
  Left rules in `Context.add`, right rules in `prove`.
  * `Context.add`:
    * simplify `Γ, ⊤ ⊢ B` to `Γ ⊢ B`
    * `Γ, ⊥ ⊢ B` is true
    * simplify `Γ, A ∧ B ⊢ C` to `Γ, A, B ⊢ C`
    * simplify `Γ, ⊥ → A ⊢ B` to `Γ ⊢ B`
    * simplify `Γ, ⊤ → A ⊢ B` to `Γ, A ⊢ B`
    * simplify `Γ, A ∧ B → C ⊢ D` to `Γ, A → B → C ⊢ D`
    * simplify `Γ, A ∨ B → C ⊢ D` to `Γ, A → C, B → C ⊢ D`
  * `prove`:
    * `Γ ⊢ ⊤` is true
    * simplify `Γ ⊢ A → B` to `Γ, A ⊢ B`
  * `search`:
    * `Γ, P ⊢ P` is true
    * simplify `Γ, P, P → A ⊢ B` to `Γ, P, A ⊢ B`
* level 2: Splitting rules, validity preserving: apply after level 1 rules. Done in `prove`
  * simplify `Γ ⊢ A ∧ B` to `Γ ⊢ A` and `Γ ⊢ B`
  * simplify `Γ, A ∨ B ⊢ C` to `Γ, A ⊢ C` and `Γ, B ⊢ C`
* level 3: Splitting rules, not validity preserving: apply only if nothing else applies.
  Done in `search`
  * `Γ ⊢ A ∨ B` follows from `Γ ⊢ A`
  * `Γ ⊢ A ∨ B` follows from `Γ ⊢ B`
  * `Γ, (A₁ → A₂) → C ⊢ B` follows from `Γ, A₂ → C, A₁ ⊢ A₂` and `Γ, C ⊢ B`

This covers the core algorithm, which only handles `True`, `False`, `And`, `Or`, and `→`.
For `Iff` and `Eq`, we treat them essentially the same as `(p → q) ∧ (q → p)`, although we use
a different `IProp` representation because we have to remember to apply different theorems during
replay. For definitions like `Not` and `Xor`, we just eagerly unfold them. (This could potentially
cause a blowup issue for `Xor`, but it isn't used very often anyway. We could add it to the `IProp`
grammar if it matters.)

## Tags

propositional logic, intuitionistic logic, decision procedure
-/

public meta section


open Std (TreeMap TreeSet)

namespace Mathlib.Tactic.ITauto

/--
Inductive type `AndKind` / 归纳类型 `AndKind`

English:
inductive AndKind
  parameters: | and | iff | eq

中文:
归纳类型 AndKind
  参数: | and | iff | eq
-/
inductive AndKind | and | iff | eq
  deriving Lean.ToExpr, DecidableEq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited AndKind
  body: ⟨AndKind.and⟩

中文:
实例 :
  签名: 可居 AndKind
  定义体: ⟨AndKind.and⟩

Depends on / 依赖: AndKind, AndKind.and
-/
instance : Inhabited AndKind := ⟨AndKind.and⟩

/--
Inductive type `IProp` / 归纳类型 `IProp`

English:
inductive IProp
  parameters: : Type
  constructors (6):
    - var: Nat -> IProp -- propositional atoms P_i
    - true: IProp -- ⊤
    - false: IProp -- ⊥
    - and': AndKind -> IProp -> IProp -> IProp -- p ∧ q, p ↔ q, p = q
    - or: IProp -> IProp -> IProp -- p ∨ q
    - imp: IProp -> IProp -> IProp -- p → q

中文:
归纳类型 IProp
  参数: : 类型
  构造子 (6 个):
    - var: 自然数 -> IProp -- propositional atoms P_i
    - true: IProp -- ⊤
    - false: IProp -- ⊥
    - and': AndKind -> IProp -> IProp -> IProp -- p ∧ q, p ↔ q, p = q
    - or: IProp -> IProp -> IProp -- p ∨ q
    - imp: IProp -> IProp -> IProp -- p → q
-/
inductive IProp : Type
  | var : Nat -> IProp -- propositional atoms P_i
  | true : IProp -- ⊤
  | false : IProp -- ⊥
  | and' : AndKind -> IProp -> IProp -> IProp -- p ∧ q, p ↔ q, p = q
  | or : IProp -> IProp -> IProp -- p ∨ q
  | imp : IProp -> IProp -> IProp -- p → q
  deriving Lean.ToExpr

/--
Definition of `IProp.and` / `IProp.and` 的定义

English:
definition IProp.and
  signature: : IProp -> IProp -> IProp
  body: .and' .and

中文:
定义 IProp.and
  签名: : IProp -> IProp -> IProp
  定义体: .and' .and
-/
@[match_pattern, expose] def IProp.and : IProp -> IProp -> IProp := .and' .and

/--
Definition of `IProp.iff` / `IProp.iff` 的定义

English:
definition IProp.iff
  signature: : IProp -> IProp -> IProp
  body: .and' .iff

中文:
定义 IProp.iff
  签名: : IProp -> IProp -> IProp
  定义体: .and' .iff
-/
@[match_pattern, expose] def IProp.iff : IProp -> IProp -> IProp := .and' .iff

/--
Definition of `IProp.eq` / `IProp.eq` 的定义

English:
definition IProp.eq
  signature: : IProp -> IProp -> IProp
  body: .and' .eq

中文:
定义 IProp.eq
  签名: : IProp -> IProp -> IProp
  定义体: .and' .eq
-/
@[match_pattern, expose] def IProp.eq : IProp -> IProp -> IProp := .and' .eq

/--
Definition of `IProp.not` / `IProp.not` 的定义

English:
definition IProp.not
  signature: (a : IProp)
  body: a.imp .false

中文:
定义 IProp.not
  签名: (a : IProp)
  定义体: a.imp .false
-/
@[match_pattern, expose] def IProp.not (a : IProp) : IProp := a.imp .false

/--
Definition of `IProp.xor` / `IProp.xor` 的定义

English:
definition IProp.xor
  signature: (a b : IProp)
  body: (a.and b.not).or (b.and a.not)

中文:
定义 IProp.xor
  签名: (a b : IProp)
  定义体: (a.and b.not).or (b.and a.not)
-/
@[match_pattern, expose] def IProp.xor (a b : IProp) : IProp := (a.and b.not).or (b.and a.not)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited IProp
  body: ⟨IProp.true⟩

中文:
实例 :
  签名: 可居 IProp
  定义体: ⟨IProp.true⟩

Depends on / 依赖: IProp.true
-/
instance : Inhabited IProp := ⟨IProp.true⟩

/--
Definition of `AndKind.sides` / `AndKind.sides` 的定义

English:
definition AndKind.sides
  signature: : AndKind -> IProp -> IProp -> IProp × IProp

中文:
定义 AndKind.sides
  签名: : AndKind -> IProp -> IProp -> IProp × IProp
-/
def AndKind.sides : AndKind -> IProp -> IProp -> IProp × IProp
  | .and, A, B => (A, B)
  | _, A, B => (A.imp B, B.imp A)

/--
Definition of `IProp.format` / `IProp.format` 的定义

English:
definition IProp.format
  signature: : IProp -> Std.Format

中文:
定义 IProp.format
  签名: : IProp -> Std.Format
-/
def IProp.format : IProp -> Std.Format
  | .var i => f!"v{i}"
  | .true => f!"⊤"
  | .false => f!"⊥"
  | .and p q => f!"({p.format} ∧ {q.format})"
  | .iff p q => f!"({p.format} ↔ {q.format})"
  | .eq p q => f!"({p.format} = {q.format})"
  | .or p q => f!"({p.format} ∨ {q.format})"
  | .imp p q => f!"({p.format} -> {q.format})"

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.ToFormat IProp
  body: ⟨IProp.format⟩

中文:
实例 :
  签名: Std.ToFormat IProp
  定义体: ⟨IProp.format⟩

Depends on / 依赖: IProp.format, format
-/
instance : Std.ToFormat IProp := ⟨IProp.format⟩

/--
Definition of `AndKind.cmp` / `AndKind.cmp` 的定义

English:
definition AndKind.cmp
  signature: (p q : AndKind)
  body: by
  cases p <;> cases q
  exacts [.eq, .lt, .lt, .gt, .eq, .lt, .gt, .gt, .eq]

中文:
定义 AndKind.cmp
  签名: (p q : AndKind)
  定义体: by
  cases p <;> cases q
  exacts [.eq, .lt, .lt, .gt, .eq, .lt, .gt, .gt, .eq]

Depends on / 依赖: exacts
-/
def AndKind.cmp (p q : AndKind) : Ordering := by
  cases p <;> cases q
  exacts [.eq, .lt, .lt, .gt, .eq, .lt, .gt, .gt, .eq]

/--
Definition of `IProp.cmp` / `IProp.cmp` 的定义

English:
definition IProp.cmp
  signature: (p q : IProp)
  body: by
  cases p <;> cases q
  case var.var p q => exact compare p q
  case true.true => exact .eq
  case false.false => exact .eq
case and'.and' ap p₁ p₂ aq q₁ q₂ => exact (ap.cmp aq).then (p₁.cmp q₁).then (p₂.cmp q₂)
  case or.or p₁ p₂ q₁ q₂ => exact (p₁.cmp q₁).then (p₂.cmp q₂)
  case imp.imp p₁ p₂ q

中文:
定义 IProp.cmp
  签名: (p q : IProp)
  定义体: by
  cases p <;> cases q
  case var.var p q => exact compare p q
  case true.true => exact .eq
  case false.false => exact .eq
case and'.and' ap p₁ p₂ aq q₁ q₂ => exact (ap.cmp aq).then (p₁.cmp q₁).then (p₂.cmp q₂)
  case or.or p₁ p₂ q₁ q₂ => exact (p₁.cmp q₁).then (p₂.cmp q₂)
  case imp.imp p₁ p₂ q

Depends on / 依赖: ap.cmp, compare, exacts, false.false, imp.imp, or.or, true.true, var.var
-/
def IProp.cmp (p q : IProp) : Ordering := by
  cases p <;> cases q
  case var.var p q => exact compare p q
  case true.true => exact .eq
  case false.false => exact .eq
case and'.and' ap p₁ p₂ aq q₁ q₂ => exact (ap.cmp aq).then (p₁.cmp q₁).then (p₂.cmp q₂)
  case or.or p₁ p₂ q₁ q₂ => exact (p₁.cmp q₁).then (p₂.cmp q₂)
  case imp.imp p₁ p₂ q₁ q₂ => exact (p₁.cmp q₁).then (p₂.cmp q₂)
  exacts [.lt, .lt, .lt, .lt, .lt,
          .gt, .lt, .lt, .lt, .lt,
          .gt, .gt, .lt, .lt, .lt,
          .gt, .gt, .gt, .lt, .lt,
          .gt, .gt, .gt, .gt, .lt,
          .gt, .gt, .gt, .gt, .gt]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LT IProp
  body: ⟨fun p q => p.cmp q = .lt⟩

中文:
实例 :
  签名: LT IProp
  定义体: ⟨fun p q => p.cmp q = .lt⟩

Depends on / 依赖: p.cmp
-/
instance : LT IProp := ⟨fun p q => p.cmp q = .lt⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableLT IProp
  body: fun _ _ => inferInstanceAs (Decidable (_ = _))

中文:
实例 :
  签名: DecidableLT IProp
  定义体: fun _ _ => inferInstanceAs (Decidable (_ = _))

Depends on / 依赖: Decidable
-/
instance : DecidableLT IProp := fun _ _ => inferInstanceAs (Decidable (_ = _))

open Lean (Name)

/--
Inductive type `Proof` / 归纳类型 `Proof`

English:
inductive Proof
  constructors (19):
    - sorry: Proof
    - hyp: (n : Name) : Proof
    - triv: Proof
    - exfalso': (p : Proof) : Proof
    - intro: (x : Name) (p : Proof) : Proof
    - andLeft: (ak : AndKind) (p : Proof) : Proof
    - andRight: (ak : AndKind) (p : Proof) : Proof
    - andIntro: (ak : AndKind) (p₁ p₂ : Proof) : Proof
    - curry: (ak : AndKind) (p : Proof) : Proof
    - curry₂: (ak : AndKind) (p q : Proof) : Proof
    - app': Proof -> Proof -> Proof
    - orImpL: (p : Proof) : Proof
    - orImpR: (p : Proof) : Proof
    - orInL: (p : Proof) : Proof
    - orInR: (p : Proof) : Proof
    - orElim': (p₁ : Proof) (x : Name) (p₂ p₃ : Proof) : Proof
    - decidableElim: (classical : Bool) (p₁ x : Name) (p₂ p₃ : Proof) : Proof
    - em: (classical : Bool) (p : Name) : Proof
    - impImpSimp: (x : Name) (p : Proof) : Proof

中文:
归纳类型 证明
  构造子 (19 个):
    - sorry: 证明
    - hyp: (n : Name) : 证明
    - triv: 证明
    - exfalso': (p : 证明) : 证明
    - intro: (x : Name) (p : 证明) : 证明
    - andLeft: (ak : AndKind) (p : 证明) : 证明
    - andRight: (ak : AndKind) (p : 证明) : 证明
    - andIntro: (ak : AndKind) (p₁ p₂ : 证明) : 证明
    - curry: (ak : AndKind) (p : 证明) : 证明
    - curry₂: (ak : AndKind) (p q : 证明) : 证明
    - app': 证明 -> 证明 -> 证明
    - orImpL: (p : 证明) : 证明
    - orImpR: (p : 证明) : 证明
    - orInL: (p : 证明) : 证明
    - orInR: (p : 证明) : 证明
    - orElim': (p₁ : 证明) (x : Name) (p₂ p₃ : 证明) : 证明
    - decidableElim: (classical : 布尔值) (p₁ x : Name) (p₂ p₃ : 证明) : 证明
    - em: (classical : 布尔值) (p : Name) : 证明
    - impImpSimp: (x : Name) (p : 证明) : 证明
-/
inductive Proof
  /-- `⊢ A`, causes failure during reconstruction -/
  | sorry : Proof
  /-- `(n: A) ⊢ A` -/
  | hyp (n : Name) : Proof
  /-- `⊢ ⊤` -/
  | triv : Proof
  /-- `(p: ⊥) ⊢ A` -/
  | exfalso' (p : Proof) : Proof
  /-- `(p: (x: A) ⊢ B) ⊢ A → B` -/
  | intro (x : Name) (p : Proof) : Proof
  /--
  * `ak = .and`: `(p: A ∧ B) ⊢ A`
  * `ak = .iff`: `(p: A ↔ B) ⊢ A → B`
  * `ak = .eq`: `(p: A = B) ⊢ A → B`
  -/
  | andLeft (ak : AndKind) (p : Proof) : Proof
  /--
  * `ak = .and`: `(p: A ∧ B) ⊢ B`
  * `ak = .iff`: `(p: A ↔ B) ⊢ B → A`
  * `ak = .eq`: `(p: A = B) ⊢ B → A`
  -/
  | andRight (ak : AndKind) (p : Proof) : Proof
  /--
  * `ak = .and`: `(p₁: A) (p₂: B) ⊢ A ∧ B`
  * `ak = .iff`: `(p₁: A → B) (p₁: B → A) ⊢ A ↔ B`
  * `ak = .eq`: `(p₁: A → B) (p₁: B → A) ⊢ A = B`
  -/
  | andIntro (ak : AndKind) (p₁ p₂ : Proof) : Proof
  /--
  * `ak = .and`: `(p: A ∧ B → C) ⊢ A → B → C`
  * `ak = .iff`: `(p: (A ↔ B) → C) ⊢ (A → B) → (B → A) → C`
  * `ak = .eq`: `(p: (A = B) → C) ⊢ (A → B) → (B → A) → C`
  -/
  | curry (ak : AndKind) (p : Proof) : Proof
  /-- This is a partial application of curry.
  * `ak = .and`: `(p: A ∧ B → C) (q : A) ⊢ B → C`
  * `ak = .iff`: `(p: (A ↔ B) → C) (q: A → B) ⊢ (B → A) → C`
  * `ak = .eq`: `(p: (A ↔ B) → C) (q: A → B) ⊢ (B → A) → C`
  -/
  | curry₂ (ak : AndKind) (p q : Proof) : Proof
  /-- `(p: A → B) (q: A) ⊢ B` -/
  | app' : Proof -> Proof -> Proof
  /-- `(p: A ∨ B → C) ⊢ A → C` -/
  | orImpL (p : Proof) : Proof
  /-- `(p: A ∨ B → C) ⊢ B → C` -/
  | orImpR (p : Proof) : Proof
  /-- `(p: A) ⊢ A ∨ B` -/
  | orInL (p : Proof) : Proof
  /-- `(p: B) ⊢ A ∨ B` -/
  | orInR (p : Proof) : Proof
  /-- `(p₁: A ∨ B) (p₂: (x: A) ⊢ C) (p₃: (x: B) ⊢ C) ⊢ C` -/
  | orElim' (p₁ : Proof) (x : Name) (p₂ p₃ : Proof) : Proof
  /-- `(p₁: Decidable A) (p₂: (x: A) ⊢ C) (p₃: (x: ¬ A) ⊢ C) ⊢ C` -/
  | decidableElim (classical : Bool) (p₁ x : Name) (p₂ p₃ : Proof) : Proof
  /--
  * `classical = false`: `(p: Decidable A) ⊢ A ∨ ¬A`
  * `classical = true`: `(p: Prop) ⊢ p ∨ ¬p`
  -/
  | em (classical : Bool) (p : Name) : Proof
  /-- The variable `x` here names the variable that will be used in the elaborated proof.
  * `(p: ((x:A) → B) → C) ⊢ B → C`
  -/
  | impImpSimp (x : Name) (p : Proof) : Proof
  deriving Lean.ToExpr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Proof
  body: ⟨Proof.triv⟩

中文:
实例 :
  签名: 可居 证明
  定义体: ⟨Proof.triv⟩

Depends on / 依赖: Proof.triv
-/
instance : Inhabited Proof := ⟨Proof.triv⟩

/--
Definition of `Proof.format` / `Proof.format` 的定义

English:
definition Proof.format
  signature: : Proof -> Std.Format

中文:
定义 证明.format
  签名: : 证明 -> Std.Format
-/
def Proof.format : Proof -> Std.Format
  | .sorry => "sorry"
  | .hyp i => Std.format i
  | .triv => "triv"
  | .exfalso' p => f!"(exfalso {p.format})"
  | .intro x p => f!"(fun {x} => {p.format})"
  | .andLeft _ p => f!"{p.format} .1"
  | .andRight _ p => f!"{p.format} .2"
  | .andIntro _ p q => f!"⟨{p.format}, {q.format}⟩"
  | .curry _ p => f!"(curry {p.format})"
  | .curry₂ _ p q => f!"(curry {p.format} {q.format})"
  | .app' p q => f!"({p.format} {q.format})"
  | .orImpL p => f!"(orImpL {p.format})"
  | .orImpR p => f!"(orImpR {p.format})"
  | .orInL p => f!"(Or.inl {p.format})"
  | .orInR p => f!"(Or.inr {p.format})"
  | .orElim' p x q r => f!"({p.format}.elim (fun {x} => {q.format}) (fun {x} => {r.format})"
  | .em false p => f!"(Decidable.em {p})"
  | .em true p => f!"(Classical.em {p})"
  | .decidableElim _ p x q r => f!"({p}.elim (fun {x} => {q.format}) (fun {x} => {r.format})"
  | .impImpSimp _ p => f!"(impImpSimp {p.format})"

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.ToFormat Proof
  body: ⟨Proof.format⟩

中文:
实例 :
  签名: Std.ToFormat 证明
  定义体: ⟨Proof.format⟩

Depends on / 依赖: Proof.format, format
-/
instance : Std.ToFormat Proof := ⟨Proof.format⟩

/--
Definition of `Proof.exfalso` / `Proof.exfalso` 的定义

English:
definition Proof.exfalso
  signature: : IProp -> Proof -> Proof

中文:
定义 证明.exfalso
  签名: : IProp -> 证明 -> 证明
-/
def Proof.exfalso : IProp -> Proof -> Proof
  | .false, p => p
  | _, p => .exfalso' p

/--
Definition of `Proof.orElim` / `Proof.orElim` 的定义

English:
definition Proof.orElim
  signature: : Proof -> Name -> Proof -> Proof -> Proof

中文:
定义 证明.orElim
  签名: : 证明 -> Name -> 证明 -> 证明 -> 证明

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, ContinuousMap
-/
def Proof.orElim : Proof -> Name -> Proof -> Proof -> Proof
  | .em cl p, x, q, r => .decidableElim cl p x q r
  | p, x, q, r => .orElim' p x q r

/--
Definition of `Proof.app` / `Proof.app` 的定义

English:
definition Proof.app
  signature: : Proof -> Proof -> Proof

中文:
定义 证明.app
  签名: : 证明 -> 证明 -> 证明
-/
def Proof.app : Proof -> Proof -> Proof
  | .curry ak p, q => .curry₂ ak p q
  | .curry₂ ak p q, r => p.app (q.andIntro ak r)
  | .orImpL p, q => p.app q.orInL
  | .orImpR p, q => p.app q.orInR
  | .impImpSimp x p, q => p.app (.intro x q)
  | p, q => p.app' q

-- Note(Mario): the typechecker is disabled because it requires proofs to carry around additional
-- props. These can be retrieved from the git history (rev 6c96d2ff7) if you want to re-enable this.
/-
/--
Definition of `Proof.check` / `Proof.check` 的定义

English:
definition Proof.check
  signature: : Lean.NameMap IProp -> Proof -> Option IProp
  body: ak.sides A B
    guard (ak = ak') *> pure (A'.imp $ B'.imp C)
  | Γ, .curry₂ ak p q => do
    let .imp (.and' ak' A B) C ← p.check Γ | none
    let A₂ ← q.check Γ
    let (A', B') := ak.sides A B
    guard (ak = ak' ∧ A₂ = A') *> pure (B'.imp C)
  | Γ, .app' p q => do
    let .imp A B ← p.check Γ | 

中文:
定义 证明.check
  签名: : Lean.NameMap IProp -> 证明 -> 选项类型 IProp
  定义体: ak.sides A B
    guard (ak = ak') *> pure (A'.imp $ B'.imp C)
  | Γ, .curry₂ ak p q => do
    let .imp (.and' ak' A B) C ← p.check Γ | none
    let A₂ ← q.check Γ
    let (A', B') := ak.sides A B
    guard (ak = ak' ∧ A₂ = A') *> pure (B'.imp C)
  | Γ, .app' p q => do
    let .imp A B ← p.check Γ | 

Depends on / 依赖: ak.sides
-/
def Proof.check : Lean.NameMap IProp -> Proof -> Option IProp
  | _, .sorry A => some A
  | Γ, .hyp i => Γ.find? i
  | _, triv => some .true
  | Γ, .exfalso' A p => guard (p.check Γ = some .false) *> pure A
  | Γ, .intro x A p => do let B ← p.check (Γ.insert x A); pure (.imp A B)
  | Γ, .andLeft ak p => do
    let .and' ak' A B ← p.check Γ | none
    guard (ak = ak') *> pure (ak.sides A B).1
  | Γ, .andRight ak p => do
    let .and' ak' A B ← p.check Γ | none
    guard (ak = ak') *> pure (ak.sides A B).2
  | Γ, .andIntro .and p q => do
    let A ← p.check Γ; let B ← q.check Γ
    pure (A.and B)
  | Γ, .andIntro ak p q => do
    let .imp A B ← p.check Γ | none
    let C ← q.check Γ; guard (C = .imp B A) *> pure (A.and' ak B)
  | Γ, .curry ak p => do
    let .imp (.and' ak' A B) C ← p.check Γ | none
    let (A', B') := ak.sides A B
    guard (ak = ak') *> pure (A'.imp $ B'.imp C)
  | Γ, .curry₂ ak p q => do
    let .imp (.and' ak' A B) C ← p.check Γ | none
    let A₂ ← q.check Γ
    let (A', B') := ak.sides A B
    guard (ak = ak' ∧ A₂ = A') *> pure (B'.imp C)
  | Γ, .app' p q => do
    let .imp A B ← p.check Γ | none
    let A' ← q.check Γ
    guard (A = A') *> pure B
  | Γ, .orImpL B p => do
    let .imp (.or A B') C ← p.check Γ | none
    guard (B = B') *> pure (A.imp C)
  | Γ, .orImpR A p => do
    let .imp (.or A' B) C ← p.check Γ | none
    guard (A = A') *> pure (B.imp C)
  | Γ, .orInL B p => do let A ← p.check Γ; pure (A.or B)
  | Γ, .orInR A p => do let B ← p.check Γ; pure (A.or B)
  | Γ, .orElim' p x q r => do
    let .or A B ← p.check Γ | none
    let C ← q.check (Γ.insert x A)
    let C' ← r.check (Γ.insert x B)
    guard (C = C') *> pure C
  | _, .em _ _ A => pure (A.or A.not)
  | Γ, .decidableElim _ A _ x p₂ p₃ => do
    let C ← p₂.check (Γ.insert x A)
    let C' ← p₃.check (Γ.insert x A.not)
    guard (C = C') *> pure C
  | Γ, .impImpSimp _ A p => do
    let .imp (.imp A' B) C ← p.check Γ | none
    guard (A = A') *> pure (B.imp C)
-/

/--
Definition of `freshName` / `freshName` 的定义

English:
definition freshName
  signature: : StateM Nat Name
  body: fun n => (Name.mkSimple s!"h{n}", n + 1)

中文:
定义 freshName
  签名: : StateM 自然数 Name
  定义体: fun n => (Name.mkSimple s!"h{n}", n + 1)
-/
@[inline] def freshName : StateM Nat Name := fun n => (Name.mkSimple s!"h{n}", n + 1)

/--
Definition of `Context` / `Context` 的定义

English:
abbreviation Context
  body: TreeMap IProp Proof IProp.cmp

中文:
缩写 余ntext
  定义体: TreeMap IProp Proof IProp.cmp

Depends on / 依赖: IProp.cmp, TreeMap
-/
abbrev Context := TreeMap IProp Proof IProp.cmp

/--
Definition of `Context.format` / `Context.format` 的定义

English:
definition Context.format
  signature: (Γ : Context)
  body: Γ.foldl (init := "") fun f P p => P.format ++ " := " ++ p.format ++ ",\n" ++ f

中文:
定义 余ntext.format
  签名: (Γ : 余ntext)
  定义体: Γ.foldl (init := "") fun f P p => P.format ++ " := " ++ p.format ++ ",\n" ++ f

Depends on / 依赖: P.format, format, p.format
-/
def Context.format (Γ : Context) : Std.Format :=
  Γ.foldl (init := "") fun f P p => P.format ++ " := " ++ p.format ++ ",\n" ++ f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.ToFormat Context
  body: ⟨Context.format⟩

中文:
实例 :
  签名: Std.ToFormat 余ntext
  定义体: ⟨Context.format⟩

Depends on / 依赖: Context, Context.format, format
-/
instance : Std.ToFormat Context := ⟨Context.format⟩

/--
Definition of `Context.add` / `Context.add` 的定义

English:
definition Context.add
  signature: : IProp -> Proof -> Context -> Except (IProp -> Proof) Context
  body: ak.sides A B
    let Γ ← Γ.add A (p.andLeft ak)
    Γ.add B (p.andRight ak)
  | .imp .false _, _, Γ => pure Γ
  | .imp .true A, p, Γ => Γ.add A (p.app .triv)
  | .imp (.and' ak A B) C, p, Γ =>
    let (A, B) := ak.sides A B
    Γ.add (A.imp (B.imp C)) (p.curry ak)
  | .imp (.or A B) C, p, Γ => do
  

中文:
定义 余ntext.add
  签名: : IProp -> 证明 -> 余ntext -> Except (IProp -> 证明) 余ntext
  定义体: ak.sides A B
    let Γ ← Γ.add A (p.andLeft ak)
    Γ.add B (p.andRight ak)
  | .imp .false _, _, Γ => pure Γ
  | .imp .true A, p, Γ => Γ.add A (p.app .triv)
  | .imp (.and' ak A B) C, p, Γ =>
    let (A, B) := ak.sides A B
    Γ.add (A.imp (B.imp C)) (p.curry ak)
  | .imp (.or A B) C, p, Γ => do
  
-/
partial def Context.add : IProp -> Proof -> Context -> Except (IProp -> Proof) Context
  | .true, _, Γ => pure Γ
  | .false, p, _ => throw fun A => .exfalso A p
  | .and' ak A B, p, Γ => do
    let (A, B) := ak.sides A B
    let Γ ← Γ.add A (p.andLeft ak)
    Γ.add B (p.andRight ak)
  | .imp .false _, _, Γ => pure Γ
  | .imp .true A, p, Γ => Γ.add A (p.app .triv)
  | .imp (.and' ak A B) C, p, Γ =>
    let (A, B) := ak.sides A B
    Γ.add (A.imp (B.imp C)) (p.curry ak)
  | .imp (.or A B) C, p, Γ => do
    let Γ ← Γ.add (A.imp C) p.orImpL
    Γ.add (B.imp C) p.orImpR
  | .imp _ .true, _, Γ => pure Γ
  | A, p, Γ => pure (Γ.insert A p)

/--
Definition of `Context.withAdd` / `Context.withAdd` 的定义

English:
definition Context.withAdd
  signature: (Γ : Context) (A : IProp) (p : Proof) (B : IProp)
  body: match Γ.add A p with
  | .ok Γ_A => f Γ_A B
  | .error p => pure (true, p B)

中文:
定义 余ntext.withAdd
  签名: (Γ : 余ntext) (A : IProp) (p : 证明) (B : IProp)
  定义体: match Γ.add A p with
  | .ok Γ_A => f Γ_A B
  | .error p => pure (true, p B)
-/
@[inline] def Context.withAdd (Γ : Context) (A : IProp) (p : Proof) (B : IProp)
    (f : Context -> IProp -> StateM Nat (Bool × Proof)) : StateM Nat (Bool × Proof) :=
  match Γ.add A p with
  | .ok Γ_A => f Γ_A B
  | .error p => pure (true, p B)

/--
Definition of `mapProof` / `mapProof` 的定义

English:
definition mapProof
  signature: (f : Proof -> Proof)

中文:
定义 mapProof
  签名: (f : 证明 -> 证明)
-/
def mapProof (f : Proof -> Proof) : Bool × Proof -> Bool × Proof
  | (b, p) => (b, f p)

/--
Definition of `isOk` / `isOk` 的定义

English:
definition isOk
  signature: : (Bool × Proof) × Nat -> Option (Proof × Nat)

中文:
定义 isOk
  签名: : (布尔值 × 证明) × 自然数 -> 选项类型 (证明 × 自然数)

Depends on / 依赖: toOrderHomClass
-/
def isOk : (Bool × Proof) × Nat -> Option (Proof × Nat)
  | ((false, _), _) => none
  | ((true, p), n) => some (p, n)

/--
Definition of `whenOk` / `whenOk` 的定义

English:
definition whenOk
  signature: : Bool -> IProp -> StateM Nat (Bool × Proof) -> StateM Nat (Bool × Proof)

中文:
定义 whenOk
  签名: : 布尔值 -> IProp -> StateM 自然数 (布尔值 × 证明) -> StateM 自然数 (布尔值 × 证明)
-/
def whenOk : Bool -> IProp -> StateM Nat (Bool × Proof) -> StateM Nat (Bool × Proof)
  | false, _, _ => pure (false, .sorry)
  | true, _, f => f

mutual

/--
Definition of `search` / `search` 的定义

English:
definition search
  signature: (Γ : Context) (B : IProp)
  body: do
  if let some p := Γ[B]? then return (true, p)
  fun n =>
  let search₁ := Γ.foldl (init := none) fun r A p => do
    if let some r := r then return r
    let .imp A' C := A | none
    if let some q := Γ[A']? then
isOk Context.withAdd (Γ.erase A) C (p.app q) B prove n
    else
      let .imp A₁ A

中文:
定义 search
  签名: (Γ : 余ntext) (B : IProp)
  定义体: do
  if let some p := Γ[B]? then return (true, p)
  fun n =>
  let search₁ := Γ.foldl (init := none) fun r A p => do
    if let some r := r then return r
    let .imp A' C := A | none
    if let some q := Γ[A']? then
isOk Context.withAdd (Γ.erase A) C (p.app q) B prove n
    else
      let .imp A₁ A
-/
partial def search (Γ : Context) (B : IProp) : StateM Nat (Bool × Proof) := do
  if let some p := Γ[B]? then return (true, p)
  fun n =>
  let search₁ := Γ.foldl (init := none) fun r A p => do
    if let some r := r then return r
    let .imp A' C := A | none
    if let some q := Γ[A']? then
isOk Context.withAdd (Γ.erase A) C (p.app q) B prove n
    else
      let .imp A₁ A₂ := A' | none
      let Γ : Context := Γ.erase A
      let (a, n) := freshName n
let (p₁, n) ← isOk Γ.withAdd A₁ (.hyp a) A₂ (fun Γ_A₁ A₂ =>
        Γ_A₁.withAdd (IProp.imp A₂ C) (.impImpSimp a p) A₂ prove) n
isOk Γ.withAdd C (p.app (.intro a p₁)) B prove n
  if let some (r, n) := search₁ then
    ((true, r), n)
  else if let .or B₁ B₂ := B then
    match (mapProof .orInL <$> prove Γ B₁) n with
    | ((false, _), _) => (mapProof .orInR <$> prove Γ B₂) n
    | r => r
  else ((false, .sorry), n)

/--
Definition of `prove` / `prove` 的定义

English:
definition prove
  signature: (Γ : Context) (B : IProp)
  body: match B with
  | .true => pure (true, .triv)
  | .imp A B => do
    let a ← freshName
mapProof (.intro a) < > Γ.withAdd A (.hyp a) B prove
  | .and' ak A B => do
    let (A, B) := ak.sides A B
    let (ok, p) ← prove Γ A
mapProof (p.andIntro ak) < > whenOk ok B (prove Γ B)
  | B =>
    Γ.foldl
     

中文:
定义 prove
  签名: (Γ : 余ntext) (B : IProp)
  定义体: match B with
  | .true => pure (true, .triv)
  | .imp A B => do
    let a ← freshName
mapProof (.intro a) < > Γ.withAdd A (.hyp a) B prove
  | .and' ak A B => do
    let (A, B) := ak.sides A B
    let (ok, p) ← prove Γ A
mapProof (p.andIntro ak) < > whenOk ok B (prove Γ B)
  | B =>
    Γ.foldl
     
-/
partial def prove (Γ : Context) (B : IProp) : StateM Nat (Bool × Proof) :=
  match B with
  | .true => pure (true, .triv)
  | .imp A B => do
    let a ← freshName
mapProof (.intro a) < > Γ.withAdd A (.hyp a) B prove
  | .and' ak A B => do
    let (A, B) := ak.sides A B
    let (ok, p) ← prove Γ A
mapProof (p.andIntro ak) < > whenOk ok B (prove Γ B)
  | B =>
    Γ.foldl
      (init := fun found Γ => bif found then prove Γ B else search Γ B)
      (f := fun IH A p found Γ => do
        if let .or A₁ A₂ := A then
          let Γ : Context := Γ.erase A
          let a ← freshName
          let (ok, p₁) ← Γ.withAdd A₁ (.hyp a) B fun Γ _ => IH true Γ
mapProof (.orElim p a p₁) < >
            whenOk ok B (Γ.withAdd A₂ (.hyp a) B fun Γ _ => IH true Γ)
        else IH found Γ)
      (found := false) (Γ := Γ)

end

open Lean Qq Meta

/--
Definition of `reify` / `reify` 的定义

English:
definition reify
  signature: (e : Q(Prop))
  body: match e with
  | ~q(True) => return .true
  | ~q(False) => return .false
  | ~q(¬ $a) => return .not (← reify a)
  | ~q($a ∧ $b) => return .and (← reify a) (← reify b)
  | ~q($a ∨ $b) => return .or (← reify a) (← reify b)
  | ~q($a ↔ $b) => return .iff (← reify a) (← reify b)
  | ~q(Xor $a $b) => re

中文:
定义 reify
  签名: (e : Q(命题))
  定义体: match e with
  | ~q(True) => return .true
  | ~q(False) => return .false
  | ~q(¬ $a) => return .not (← reify a)
  | ~q($a ∧ $b) => return .and (← reify a) (← reify b)
  | ~q($a ∨ $b) => return .or (← reify a) (← reify b)
  | ~q($a ↔ $b) => return .iff (← reify a) (← reify b)
  | ~q(Xor $a $b) => re
-/
partial def reify (e : Q(Prop)) : AtomM IProp :=
  match e with
  | ~q(True) => return .true
  | ~q(False) => return .false
  | ~q(¬ $a) => return .not (← reify a)
  | ~q($a ∧ $b) => return .and (← reify a) (← reify b)
  | ~q($a ∨ $b) => return .or (← reify a) (← reify b)
  | ~q($a ↔ $b) => return .iff (← reify a) (← reify b)
  | ~q(Xor $a $b) => return .xor (← reify a) (← reify b)
  | ~q(@Eq Prop $a $b) => return .eq (← reify a) (← reify b)
  | ~q(@Ne Prop $a $b) => return .not (.eq (← reify a) (← reify b))
  | e =>
    if e.isArrow then return .imp (← reify e.bindingDomain!) (← reify e.bindingBody!)
    else return .var (← AtomM.addAtom e).1

/--
Definition of `applyProof` / `applyProof` 的定义

English:
definition applyProof
  signature: (g : MVarId) (Γ : NameMap Expr) (p : Proof)
  body: match p with
  | .sorry => throwError "itauto failed\n{g}"
  | .hyp n => do g.assignIfDefEq (← liftOption (Γ.find? n))
  | .triv => g.assignIfDefEq q(trivial)
  | .exfalso' p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q(False)
    g.assignIfDefEq q(@False.elim $A $t)
   

中文:
定义 applyProof
  签名: (g : MVarId) (Γ : NameMap Expr) (p : 证明)
  定义体: match p with
  | .sorry => throwError "itauto failed\n{g}"
  | .hyp n => do g.assignIfDefEq (← liftOption (Γ.find? n))
  | .triv => g.assignIfDefEq q(trivial)
  | .exfalso' p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q(False)
    g.assignIfDefEq q(@False.elim $A $t)
   
-/
partial def applyProof (g : MVarId) (Γ : NameMap Expr) (p : Proof) : MetaM Unit :=
  match p with
  | .sorry => throwError "itauto failed\n{g}"
  | .hyp n => do g.assignIfDefEq (← liftOption (Γ.find? n))
  | .triv => g.assignIfDefEq q(trivial)
  | .exfalso' p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q(False)
    g.assignIfDefEq q(@False.elim $A $t)
    applyProof t.mvarId! Γ p
  | .intro x p => do
    let (e, g) ← g.intro x; g.withContext do
      applyProof g (Γ.insert x (.fvar e)) p
  | .andLeft .and p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ∧ $B)
    g.assignIfDefEq q(And.left $t)
    applyProof t.mvarId! Γ p
  | .andLeft .iff p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ↔ $B)
    g.assignIfDefEq q(Iff.mp $t)
    applyProof t.mvarId! Γ p
  | .andLeft .eq p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A = $B)
    g.assignIfDefEq q(cast $t)
    applyProof t.mvarId! Γ p
  | .andRight .and p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ∧ $B)
    g.assignIfDefEq q(And.right $t)
    applyProof t.mvarId! Γ p
  | .andRight .iff p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ↔ $B)
    g.assignIfDefEq q(Iff.mpr $t)
    applyProof t.mvarId! Γ p
  | .andRight .eq p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A = $B)
    g.assignIfDefEq q(cast (Eq.symm $t))
    applyProof t.mvarId! Γ p
  | .andIntro .and p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A)
    let t₂ ← mkFreshExprMVarQ q($B)
    g.assignIfDefEq q(And.intro $t₁ $t₂)
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | .andIntro .iff p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A -> $B)
    let t₂ ← mkFreshExprMVarQ q($B -> $A)
    g.assignIfDefEq q(Iff.intro $t₁ $t₂)
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | .andIntro .eq p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A -> $B)
    let t₂ ← mkFreshExprMVarQ q($B -> $A)
    g.assignIfDefEq q(propext (Iff.intro $t₁ $t₂))
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | .app' p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A -> $B)
    let t₂ ← mkFreshExprMVarQ q($A)
    g.assignIfDefEq q($t₁ $t₂)
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | .orInL p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A)
    g.assignIfDefEq q(@Or.inl $A $B $t)
    applyProof t.mvarId! Γ p
  | .orInR p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($B)
    g.assignIfDefEq q(@Or.inr $A $B $t)
    applyProof t.mvarId! Γ p
  | .orElim' p x p₁ p₂ => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let C ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A ∨ $B)
    let t₂ ← mkFreshExprMVarQ q($A -> $C)
    let t₃ ← mkFreshExprMVarQ q($B -> $C)
    g.assignIfDefEq q(Or.elim $t₁ $t₂ $t₃)
    applyProof t₁.mvarId! Γ p
    let (e, t₂) ← t₂.mvarId!.intro x; t₂.withContext do
      applyProof t₂ (Γ.insert x (.fvar e)) p₁
    let (e, t₃) ← t₃.mvarId!.intro x; t₃.withContext do
      applyProof t₃ (Γ.insert x (.fvar e)) p₂
  | .em false n => do
    let A ← mkFreshExprMVarQ q(Prop)
    let e : Q(Decidable $A) ← liftOption (Γ.find? n)
    let .true ← Meta.isDefEq (← Meta.inferType e) q(Decidable $A) | failure
    g.assignIfDefEq q(@Decidable.em $A $e)
  | .em true n => do
    let A : Q(Prop) ← liftOption (Γ.find? n)
    g.assignIfDefEq q(@Classical.em $A)
  | .decidableElim false n x p₁ p₂ => do
    let A ← mkFreshExprMVarQ q(Prop)
    let e : Q(Decidable $A) ← liftOption (Γ.find? n)
    let .true ← Meta.isDefEq (← Meta.inferType e) q(Decidable $A) | failure
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A -> $B)
    let t₂ ← mkFreshExprMVarQ q(¬$A -> $B)
    g.assignIfDefEq q(@dite $B $A $e $t₁ $t₂)
    let (e, t₁) ← t₁.mvarId!.intro x; t₁.withContext do
      applyProof t₁ (Γ.insert x (.fvar e)) p₁
    let (e, t₂) ← t₂.mvarId!.intro x; t₂.withContext do
      applyProof t₂ (Γ.insert x (.fvar e)) p₂
  | .decidableElim true n x p₁ p₂ => do
    let A : Q(Prop) ← liftOption (Γ.find? n)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A -> $B)
    let t₂ ← mkFreshExprMVarQ q(¬$A -> $B)
    g.assignIfDefEq q(@Classical.byCases $A $B $t₁ $t₂)
    let (e, t₁) ← t₁.mvarId!.intro x; t₁.withContext do
      applyProof t₁ (Γ.insert x (.fvar e)) p₁
    let (e, t₂) ← t₂.mvarId!.intro x; t₂.withContext do
      applyProof t₂ (Γ.insert x (.fvar e)) p₂
  | .curry .. | .curry₂ .. | .orImpL .. | .orImpR .. | .impImpSimp .. => do
    let (e, g) ← g.intro1; g.withContext do
      applyProof g (Γ.insert e.name (.fvar e)) (p.app (.hyp e.name))

/--
Definition of `itautoCore` / `itautoCore` 的定义

English:
definition itautoCore
  signature: (g : MVarId)
  body: do
  AtomM.run (← getTransparency) do
    let mut hs := mkNameMap Expr
    let t ← g.getType
    let (g, t) ← if ← isProp t then pure (g, ← reify t) else pure (← g.exfalso, .false)
    let mut Γ : Except (IProp -> Proof) ITauto.Context := .ok TreeMap.empty
    let mut decs := TreeMap.empty
    for l

中文:
定义 itautoCore
  签名: (g : MVarId)
  定义体: do
  AtomM.run (← getTransparency) do
    let mut hs := mkNameMap Expr
    let t ← g.getType
    let (g, t) ← if ← isProp t then pure (g, ← reify t) else pure (← g.exfalso, .false)
    let mut Γ : Except (IProp -> Proof) ITauto.Context := .ok TreeMap.empty
    let mut decs := TreeMap.empty
    for l
-/
def itautoCore (g : MVarId)
    (useDec useClassical : Bool) (extraDec : Array Expr) : MetaM Unit := do
  AtomM.run (← getTransparency) do
    let mut hs := mkNameMap Expr
    let t ← g.getType
    let (g, t) ← if ← isProp t then pure (g, ← reify t) else pure (← g.exfalso, .false)
    let mut Γ : Except (IProp -> Proof) ITauto.Context := .ok TreeMap.empty
    let mut decs := TreeMap.empty
    for ldecl in ← getLCtx do
      if !ldecl.isImplementationDetail then
        let e := ldecl.type
        if ← isProp e then
          let A ← reify e
          let n := ldecl.fvarId.name
          hs := hs.insert n (Expr.fvar ldecl.fvarId)
          Γ := do (← Γ).add A (.hyp n)
        else
          if let .const ``Decidable _ := e.getAppFn then
            let p : Q(Prop) := e.appArg!
            if useDec then
              let A ← reify p
              decs := decs.insert A (false, Expr.fvar ldecl.fvarId)
    let addDec (force : Bool) (decs : TreeMap IProp (Bool × Expr) IProp.cmp) (e : Q(Prop)) := do
      let A ← reify e
      let dec_e := q(Decidable $e)
      let res ← trySynthInstance q(Decidable $e)
      if !(res matches .some _) && !useClassical then
        if force then _ ← synthInstance dec_e
        pure decs
      else
        pure (decs.insert A (match res with | .some e => (false, e) | _ => (true, e)))
    decs ← extraDec.foldlM (addDec true) decs
    if useDec then
      let mut decided := TreeSet.empty (cmp := compare)
      if let .ok Γ' := Γ then
        decided := Γ'.foldl (init := decided) fun m p _ =>
          match p with
          | .var i => m.insert i
          | .not (.var i) => m.insert i
          | _ => m
      let ats := (← get).atoms
      for e in ats, i in [0:ats.size] do
        if !decided.contains i then
          decs ← addDec false decs e
    for (A, cl, pf) in decs do
      let n ← mkFreshId
      hs := hs.insert n pf
      Γ := return (← Γ).insert (A.or A.not) (.em cl n)
    let p : Proof :=
      match Γ with
      | .ok Γ => (prove Γ t 0).1.2
      | .error p => p t
    applyProof g hs p

open Elab Tactic

/-- `itauto` solves the main goal when it is a tautology of intuitionistic propositional logic.
Unlike `grind` and `tauto!` this tactic never uses the law of excluded middle (without the `!`
option), and the proof search is tailored for this use case. `itauto` is complete for intuitionistic
propositional logic: it will solve any goal that is provable in this logic.

* `itauto [a, b]` will additionally attempt case analysis on `a` and `b` assuming that it can derive
  `Decidable a` and `Decidable b`.
* `itauto *` will case on all decidable propositions that it can find among the atomic propositions.
* `itauto!` will work as a classical SAT solver, but the algorithm is not very good in this
  situation.
* `itauto! *` will case on all propositional atoms. *Warning:* This can blow up the proof search, so
  it should be used sparingly.

Example:
```lean
example (p : Prop) : ¬ (p ↔ ¬ p) := by itauto
```
-/
syntax (name := itauto) "itauto" "!"? (" *" <|> (" [" term,* "]"))? : tactic

elab_rules : tactic
  | `(tactic| itauto $[!%$cl]?) => liftMetaTactic (itautoCore · false cl.isSome #[] *> pure [])
  | `(tactic| itauto $[!%$cl]? *) => liftMetaTactic (itautoCore · true cl.isSome #[] *> pure [])
  | `(tactic| itauto $[!%$cl]? [$hs,*]) => withMainContext do
    let hs ← hs.getElems.mapM (Term.elabTermAndSynthesize · none)
    liftMetaTactic (itautoCore · true cl.isSome hs *> pure [])

@[tactic_alt itauto] syntax (name := itauto!) "itauto!" (" *" <|> (" [" term,* "]"))? : tactic

macro_rules
  | `(tactic| itauto!) => `(tactic| itauto !)
  | `(tactic| itauto! *) => `(tactic| itauto ! *)
  | `(tactic| itauto! [$hs,*]) => `(tactic| itauto ! [$hs,*])

-- add_hint_tactic itauto

-- add_tactic_doc
-- { Name := "itauto"
-- category := DocCategory.tactic
-- declNames := [`tactic.interactive.itauto]
-- tags := ["logic", "propositional logic", "intuitionistic logic", "decision procedure"] }

end Mathlib.Tactic.ITauto
