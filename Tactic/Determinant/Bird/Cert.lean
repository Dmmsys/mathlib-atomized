/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public meta import Mathlib.Tactic.Determinant.Bird.Meta
public meta import Mathlib.Tactic.Ring

/-!

# Certificate-chain evaluator for `BirdDet.birdDet`

This file contains an evaluator that computes the ring tactic normal form of
`Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs.birdDet` via iteratively
unfolding its definition, using the ring tactic for ring operations, and caching
intermediate certificates.

The structure `Cert rα` carries the proof certificate and the evaluator builds
larger certificates as `birdDet` is unfolded.

The entrypoint of the evaluator `certBirdDet` follows the two branches (n=0,
n=k+1) of the `birdDet` function:

```
certBirdDet (birdDet n A)
  n = 0:
    birdDet n A
      = 1 -- via BirdDet.birdDet_zero
      = ring normal form of 1 -- via certEval
  n = k + 1:
    birdDet n A
      = (-1)^k * (stepEntry n A)^[k] (get n A) 0 0 -- via BirdDet.birdDet_eq
      = ring normal form of the product -- certMul (certBirdSign k) (certIterStepEntry k 0 0)
```

The `(stepEntry n A)^[k] (get n A) i j` expression branches on `k`, so
`certIterStepEntry` has two branches:

```
certIterStepEntry k i j
  k = 0:
    (stepEntry n A)^[0] F i j
      = F i j -- via Function.iterate_zero_apply
      = ring normal form of A[i][j] -- via certEntry i j
  k = t + 1:
    (stepEntry n A)^[t + 1] F i j
      = -(sumFrom n (i + 1) fun k => (stepEntry n A)^[t] F k k) * get n A i j
          + sumFrom n (i + 1) fun k => (stepEntry n A)^[t] F i k * get n A k j
        -- via Function.iterate_succ_apply'
      = normal form of the first summand + normal form of the second summand
        -- via certAdd
                 (certMul (certNeg (certDiag t (i + 1))) (certEntry i j))
                 (certTail t i j (i + 1))
```

Then the `certDiag` and `certTail` functions certify the two kinds of `sumFrom`
expressions.

The evaluator also memoizes `certIterStepEntry`, `certDiag` and `certEntry` to
improve performance.

## Main definitions

- `certEntry` certifies `BirdDet.get`.
- `certSumFromStop` and `certSumFromStep` certify `BirdDet.sumFrom_stop` and
  `BirdDet.sumFrom_step`.
- `certIterStepEntry` certifies entries of
  `(BirdDet.stepEntry n A)^[t] (BirdDet.get n A)`.
- `certBirdDet` certifies `BirdDet.birdDet_zero` and `BirdDet.birdDet_eq`.
-/

public meta section

open Lean Meta Qq
open Mathlib.Tactic.Ring

variable {u : Level} {α : Q(Type u)} {rα : Q(CommRing $α)}

namespace Mathlib.Tactic.Determinant

/--
Definition of `CertVal` / `CertVal` 的定义

English:
abbreviation CertVal
  signature: {u : Level} {α : Q(Type u)}
  body: Common.ExSum RatCoeff (commSemiringOfCommRing rα) e

中文:
缩写 CertVal
  签名: {u : Level} {α : Q(类型u)}
  定义体: Common.ExSum RatCoeff (commSemiringOfCommRing rα) e

Depends on / 依赖: Common, Common.ExSum, RatCoeff, commSemiringOfCommRing
-/
abbrev CertVal {u : Level} {α : Q(Type u)}
    (rα : Q(CommRing $α)) (e : Q($α)) :=
  Common.ExSum RatCoeff (commSemiringOfCommRing rα) e

/--
Definition of `CertResult` / `CertResult` 的定义

English:
abbreviation CertResult
  signature: {u : Level} {α : Q(Type u)}
  body: Common.Result (CertVal rα) subject

中文:
缩写 CertResult
  签名: {u : Level} {α : Q(类型u)}
  定义体: Common.Result (CertVal rα) subject

Depends on / 依赖: CertVal, Common, Common.Result, Result, subject
-/
abbrev CertResult {u : Level} {α : Q(Type u)}
    (rα : Q(CommRing $α)) (subject : Q($α)) :=
  Common.Result (CertVal rα) subject

namespace Ctx

/--
Definition of `iterStepEntry` / `iterStepEntry` 的定义

English:
definition iterStepEntry
  signature: (ctx : Ctx rα) (t : Nat)
  body: let dim : Q(Nat) := ctx.dimensionLit
  let A : Q(Array $α) := ctx.arrayExpr
  q((BirdDet.stepEntry $dim $A)^[$t] (BirdDet.get $dim $A))

中文:
定义 iterStepEntry
  签名: (ctx : Ctx rα) (t : 自然数)
  定义体: let dim : Q(Nat) := ctx.dimensionLit
  let A : Q(Array $α) := ctx.arrayExpr
  q((BirdDet.stepEntry $dim $A)^[$t] (BirdDet.get $dim $A))

Depends on / 依赖: BirdDet, BirdDet.get, BirdDet.stepEntry, arrayExpr, ctx.arrayExpr, ctx.dimensionLit, dimensionLit, stepEntry
-/
def iterStepEntry (ctx : Ctx rα) (t : Nat) : Q(Nat -> Nat -> $α) :=
  let dim : Q(Nat) := ctx.dimensionLit
  let A : Q(Array $α) := ctx.arrayExpr
  q((BirdDet.stepEntry $dim $A)^[$t] (BirdDet.get $dim $A))

/--
Definition of `sumFrom` / `sumFrom` 的定义

English:
definition sumFrom
  signature: (ctx : Ctx rα) (lo : Nat) (f : Q(Nat -> $α))
  body: let dim : Q(Nat) := ctx.dimensionLit
  q(BirdDet.sumFrom $dim $lo $f)

中文:
定义 sumFrom
  签名: (ctx : Ctx rα) (lo : 自然数) (f : Q(自然数 -> $α))
  定义体: let dim : Q(Nat) := ctx.dimensionLit
  q(BirdDet.sumFrom $dim $lo $f)

Depends on / 依赖: BirdDet, BirdDet.sumFrom, ctx.dimensionLit, dimensionLit, sumFrom
-/
def sumFrom (ctx : Ctx rα) (lo : Nat) (f : Q(Nat -> $α)) : Q($α) :=
  let dim : Q(Nat) := ctx.dimensionLit
  q(BirdDet.sumFrom $dim $lo $f)

end Ctx

/--
Definition of `Cert` / `Cert` 的定义

English:
structure Cert
  parameters: {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α))
  axioms and operations (3):
    - {subject : Q($α)}
    - result : CertResult rα subject
    - isZero : Bool

中文:
结构 Cert
  参数: {u : Level} {α : Q(类型u)} (rα : Q(交换环 $α))
  公理与运算 (3 个):
    - {subject : Q($α)}
    - result : CertResult rα subject
    - isZero : 布尔值
-/
structure Cert {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) where
  /-- The expression being certified. -/
  {subject : Q($α)}
  /-- The result of evaluating `subject` using the ring tactic. -/
  result : CertResult rα subject
  /-- `true` when `norm` is zero, used as a hint to the evaluator. -/
  isZero : Bool

namespace Cert

variable
  {u : Level}
  {α : Q(Type u)}
  {rα : Q(CommRing $α)}

/--
Definition of `norm` / `norm` 的定义

English:
definition norm
  signature: (c : Cert rα)
  body: c.result.expr

中文:
定义 norm
  签名: (c : Cert rα)
  定义体: c.result.expr

Depends on / 依赖: c.result.expr, result
-/
def norm (c : Cert rα) : Q($α) :=
  c.result.expr

/--
Definition of `val` / `val` 的定义

English:
definition val
  signature: (c : Cert rα)
  body: c.result.val

中文:
定义 val
  签名: (c : Cert rα)
  定义体: c.result.val

Depends on / 依赖: c.result.val, result
-/
def val (c : Cert rα) : CertVal rα c.norm :=
  c.result.val

/--
Definition of `proof` / `proof` 的定义

English:
definition proof
  signature: (c : Cert rα)
  body: c.result.proof

中文:
定义 proof
  签名: (c : Cert rα)
  定义体: c.result.proof

Depends on / 依赖: c.result.proof, result
-/
def proof (c : Cert rα) : Q($c.subject = $c.norm) :=
  c.result.proof

/--
Definition of `chainProof` / `chainProof` 的定义

English:
definition chainProof
  signature: {lhs rhs : Q($α)} (c : Cert rα) (h : Q($lhs = $rhs))
  body: have : rhs =Q c.subject := ⟨⟩
  let hProof : Q($lhs = $c.subject) := h
  let proof : Q($lhs = $c.norm) := q(Eq.trans $hProof $c.proof)
  { c with
    subject := lhs
    result.proof := proof
  }

中文:
定义 chainProof
  签名: {lhs rhs : Q($α)} (c : Cert rα) (h : Q($lhs = $rhs))
  定义体: have : rhs =Q c.subject := ⟨⟩
  let hProof : Q($lhs = $c.subject) := h
  let proof : Q($lhs = $c.norm) := q(Eq.trans $hProof $c.proof)
  { c with
    subject := lhs
    result.proof := proof
  }

Depends on / 依赖: Eq.trans, c.norm, c.proof, c.subject, hProof, result, result.proof, subject
-/
def chainProof {lhs rhs : Q($α)} (c : Cert rα) (h : Q($lhs = $rhs)) : Cert rα :=
have : rhs =Q c.subject := ⟨⟩
  let hProof : Q($lhs = $c.subject) := h
  let proof : Q($lhs = $c.norm) := q(Eq.trans $hProof $c.proof)
  { c with
    subject := lhs
    result.proof := proof
  }

end Cert

/--
Definition of `CertCache` / `CertCache` 的定义

English:
structure CertCache
  parameters: {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α))
  axioms and operations (3):
    - entryCache : Std.HashMap (Nat × Nat) (Cert rα)  [default: {}]
    - iterStepEntryCache : Std.HashMap (Nat × Nat × Nat) (Cert rα)  [default: {}]
    - diagCache : Std.HashMap (Nat × Nat) (Cert rα)  [default: {}]

中文:
结构 CertCache
  参数: {u : Level} {α : Q(类型u)} (rα : Q(交换环 $α))
  公理与运算 (3 个):
    - entryCache : Std.HashMap (自然数 × 自然数) (Cert rα)  [默认: {}]
    - iterStepEntryCache : Std.HashMap (自然数 × 自然数 × 自然数) (Cert rα)  [默认: {}]
    - diagCache : Std.HashMap (自然数 × 自然数) (Cert rα)  [默认: {}]
-/
structure CertCache {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) where
  /-- Cache for entry certificates, keyed by matrix indices. -/
  entryCache : Std.HashMap (Nat × Nat) (Cert rα) := {}
  /-- Cache for iterated `stepEntry` certificates, keyed by step and matrix indices. -/
  iterStepEntryCache : Std.HashMap (Nat × Nat × Nat) (Cert rα) := {}
  /-- Cache for diagonal-tail certificates, keyed by recursion index and lower bound. -/
  diagCache : Std.HashMap (Nat × Nat) (Cert rα) := {}

/--
Definition of `CertM` / `CertM` 的定义

English:
abbreviation CertM
  signature: {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α))
  body: StateT (CertCache rα) (ReaderT (Ctx rα) AtomM)

中文:
缩写 CertM
  签名: {u : Level} {α : Q(类型u)} (rα : Q(交换环 $α))
  定义体: StateT (CertCache rα) (ReaderT (Ctx rα) AtomM)

Depends on / 依赖: CertCache, ReaderT, StateT
-/
abbrev CertM {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) :=
  StateT (CertCache rα) (ReaderT (Ctx rα) AtomM)

/--
Definition of `isZeroVal` / `isZeroVal` 的定义

English:
definition isZeroVal
  signature: {e : Q($α)} (val : CertVal rα e)
  body: match val with
  | .zero => true
  | .add .. => false

中文:
定义 isZeroVal
  签名: {e : Q($α)} (val : CertVal rα e)
  定义体: match val with
  | .zero => true
  | .add .. => false
-/
def isZeroVal {e : Q($α)} (val : CertVal rα e) : Bool :=
  match val with
  | .zero => true
  | .add .. => false

/--
Definition of `toCert` / `toCert` 的定义

English:
definition toCert
  signature: {e : Q($α)} (res : Common.Result (CertVal rα) e)
  body: { result := res
    isZero := isZeroVal res.val }

中文:
定义 toCert
  签名: {e : Q($α)} (res : Common.Result (CertVal rα) e)
  定义体: { result := res
    isZero := isZeroVal res.val }

Depends on / 依赖: isZero, isZeroVal, res.val, result
-/
def toCert {e : Q($α)} (res : Common.Result (CertVal rα) e) : Cert rα :=
  { result := res
    isZero := isZeroVal res.val }

/--
Definition of `zeroCertOfProof` / `zeroCertOfProof` 的定义

English:
definition zeroCertOfProof
  signature: {lhs : Q($α)} (h : Q($lhs = 0))
  body: q(0)
  result.val := .zero
  result.proof := h
  isZero := true

中文:
定义 zeroCertOfProof
  签名: {lhs : Q($α)} (h : Q($lhs = 0))
  定义体: q(0)
  result.val := .zero
  result.proof := h
  isZero := true
-/
def zeroCertOfProof {lhs : Q($α)} (h : Q($lhs = 0)) : Cert rα where
  result.expr := q(0)
  result.val := .zero
  result.proof := h
  isZero := true

/--
Definition of `zeroProdCert` / `zeroProdCert` 的定义

English:
definition zeroProdCert
  signature: (x : Q($α)) (c : Cert rα)
  body: do
  let zero : Q($α) := q(0)
have : c.norm =Q zero := ⟨⟩
  let h : Q($x * $c.subject = $x * $zero) :=
    q(congrArg (fun y => $x * y) $c.proof)
  return zeroCertOfProof q(Eq.trans $h (mul_zero $x))

中文:
定义 zeroProdCert
  签名: (x : Q($α)) (c : Cert rα)
  定义体: do
  let zero : Q($α) := q(0)
have : c.norm =Q zero := ⟨⟩
  let h : Q($x * $c.subject = $x * $zero) :=
    q(congrArg (fun y => $x * y) $c.proof)
  return zeroCertOfProof q(Eq.trans $h (mul_zero $x))
-/
def zeroProdCert (x : Q($α)) (c : Cert rα) :
    MetaM (Cert rα) := do
  let zero : Q($α) := q(0)
have : c.norm =Q zero := ⟨⟩
  let h : Q($x * $c.subject = $x * $zero) :=
    q(congrArg (fun y => $x * y) $c.proof)
  return zeroCertOfProof q(Eq.trans $h (mul_zero $x))

/--
Definition of `certEval` / `certEval` 的定义

English:
definition certEval
  signature: (e : Q($α))
  body: do
  let ctx ← read
  let res ← Common.eval rcNat ctx.rc ctx.cα e
  return toCert res

中文:
定义 certEval
  签名: (e : Q($α))
  定义体: do
  let ctx ← read
  let res ← Common.eval rcNat ctx.rc ctx.cα e
  return toCert res
-/
def certEval (e : Q($α)) : CertM rα (Cert rα) := do
  let ctx ← read
  let res ← Common.eval rcNat ctx.rc ctx.cα e
  return toCert res

/--
Definition of `certAdd` / `certAdd` 的定义

English:
definition certAdd
  signature: (a b : Cert rα)
  body: do
  let ctx ← read
let c ← toCert < > Common.evalAdd ctx.rc rcNat a.val b.val
  let h : Q($a.subject + $b.subject = $a.norm + $b.norm) :=
    q(congr (congrArg (fun x y => x + y) $a.proof) $b.proof)
  return c.chainProof h

中文:
定义 certAdd
  签名: (a b : Cert rα)
  定义体: do
  let ctx ← read
let c ← toCert < > Common.evalAdd ctx.rc rcNat a.val b.val
  let h : Q($a.subject + $b.subject = $a.norm + $b.norm) :=
    q(congr (congrArg (fun x y => x + y) $a.proof) $b.proof)
  return c.chainProof h
-/
def certAdd (a b : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
let c ← toCert < > Common.evalAdd ctx.rc rcNat a.val b.val
  let h : Q($a.subject + $b.subject = $a.norm + $b.norm) :=
    q(congr (congrArg (fun x y => x + y) $a.proof) $b.proof)
  return c.chainProof h

/--
Definition of `certMul` / `certMul` 的定义

English:
definition certMul
  signature: (a b : Cert rα)
  body: do
  let ctx ← read
let c ← toCert < > Common.evalMul ctx.rc rcNat a.val b.val
  let h : Q($a.subject * $b.subject = $a.norm * $b.norm) :=
    q(congr (congrArg (fun x y => x * y) $a.proof) $b.proof)
  return c.chainProof h

中文:
定义 certMul
  签名: (a b : Cert rα)
  定义体: do
  let ctx ← read
let c ← toCert < > Common.evalMul ctx.rc rcNat a.val b.val
  let h : Q($a.subject * $b.subject = $a.norm * $b.norm) :=
    q(congr (congrArg (fun x y => x * y) $a.proof) $b.proof)
  return c.chainProof h
-/
def certMul (a b : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
let c ← toCert < > Common.evalMul ctx.rc rcNat a.val b.val
  let h : Q($a.subject * $b.subject = $a.norm * $b.norm) :=
    q(congr (congrArg (fun x y => x * y) $a.proof) $b.proof)
  return c.chainProof h

/--
Definition of `certNeg` / `certNeg` 的定义

English:
definition certNeg
  signature: (a : Cert rα)
  body: do
  let ctx ← read
let c ← toCert < > Common.evalNeg ctx.rc rα a.val
  let h : Q(-$a.subject = -$a.norm) :=
    q(congrArg (fun x => -x) $a.proof)
  return c.chainProof h

中文:
定义 certNeg
  签名: (a : Cert rα)
  定义体: do
  let ctx ← read
let c ← toCert < > Common.evalNeg ctx.rc rα a.val
  let h : Q(-$a.subject = -$a.norm) :=
    q(congrArg (fun x => -x) $a.proof)
  return c.chainProof h
-/
def certNeg (a : Cert rα) : CertM rα (Cert rα) := do
  let ctx ← read
let c ← toCert < > Common.evalNeg ctx.rc rα a.val
  let h : Q(-$a.subject = -$a.norm) :=
    q(congrArg (fun x => -x) $a.proof)
  return c.chainProof h

/--
Definition of `certBirdSign` / `certBirdSign` 的定义

English:
definition certBirdSign
  signature: (k : Nat)
  body: do
  certEval q((-1 : $α) ^ $k)

中文:
定义 certBirdSign
  签名: (k : 自然数)
  定义体: do
  certEval q((-1 : $α) ^ $k)
-/
def certBirdSign (k : Nat) : CertM rα (Cert rα) := do
  certEval q((-1 : $α) ^ $k)

/--
Definition of `certEntry` / `certEntry` 的定义

English:
definition certEntry
  signature: (i j : Nat)
  body: do
  if let some c := (← get).entryCache[(i, j)]? then
    return c
  let ctx ← read
  let {dimension := dim, dimensionLit := dimLit, arrayExpr := A, arrayEntries, ..} := ctx
  let lhs : Q($α) := q(BirdDet.get $dimLit $A $i $j)
  -- The index of the matrix entry (i, j) in arrayEntries
  let idx := d

中文:
定义 certEntry
  签名: (i j : 自然数)
  定义体: do
  if let some c := (← get).entryCache[(i, j)]? then
    return c
  let ctx ← read
  let {dimension := dim, dimensionLit := dimLit, arrayExpr := A, arrayEntries, ..} := ctx
  let lhs : Q($α) := q(BirdDet.get $dimLit $A $i $j)
  -- The index of the matrix entry (i, j) in arrayEntries
  let idx := d
-/
def certEntry (i j : Nat) : CertM rα (Cert rα) := do
  if let some c := (← get).entryCache[(i, j)]? then
    return c
  let ctx ← read
  let {dimension := dim, dimensionLit := dimLit, arrayExpr := A, arrayEntries, ..} := ctx
  let lhs : Q($α) := q(BirdDet.get $dimLit $A $i $j)
  -- The index of the matrix entry (i, j) in arrayEntries
  let idx := dim * i + j
  let entry := arrayEntries.getD idx q(0)
  let ce ← certEval entry
  let getD : Q($α) := q(Array.getD $A ($dimLit * $i + $j) 0)
  let hGet : Q($lhs = $getD) := q(BirdDet.get_eq $dimLit $A $i $j)
have : getD =Q entry := ⟨⟩
  let hGetD : Q($getD = $entry) := q(rfl)
  let cert := ce.chainProof q(Eq.trans $hGet $hGetD)
  modify fun s => {s with entryCache := s.entryCache.insert (i, j) cert}
  return cert

/--
Definition of `certSumFromStop` / `certSumFromStop` 的定义

English:
definition certSumFromStop
  signature: (lo : Nat) (f : Q(Nat -> $α))
  body: do
  let ctx ← read
  if lo < ctx.dimension then
    throwError "certSumFromStop called with {lo} such that {lo} < {ctx.dimension}"
  have dimLit : Q(Nat) := ctx.dimensionLit
  let hNot : Q(¬ $lo < $dimLit) ← mkDecideProofQ q(¬ $lo < $dimLit)
  return zeroCertOfProof q(BirdDet.sumFrom_stop $dimLit $

中文:
定义 certSumFromStop
  签名: (lo : 自然数) (f : Q(自然数 -> $α))
  定义体: do
  let ctx ← read
  if lo < ctx.dimension then
    throwError "certSumFromStop called with {lo} such that {lo} < {ctx.dimension}"
  have dimLit : Q(Nat) := ctx.dimensionLit
  let hNot : Q(¬ $lo < $dimLit) ← mkDecideProofQ q(¬ $lo < $dimLit)
  return zeroCertOfProof q(BirdDet.sumFrom_stop $dimLit $
-/
def certSumFromStop (lo : Nat) (f : Q(Nat -> $α)) : CertM rα (Cert rα) := do
  let ctx ← read
  if lo < ctx.dimension then
    throwError "certSumFromStop called with {lo} such that {lo} < {ctx.dimension}"
  have dimLit : Q(Nat) := ctx.dimensionLit
  let hNot : Q(¬ $lo < $dimLit) ← mkDecideProofQ q(¬ $lo < $dimLit)
  return zeroCertOfProof q(BirdDet.sumFrom_stop $dimLit $lo $f $hNot)

/--
Definition of `certSumFromStep` / `certSumFromStep` 的定义

English:
definition certSumFromStep
  body: do
  let ctx ← read
  unless lo < ctx.dimension do
    throwError "certSumFromStep called with {lo} such that ¬ {lo} < {ctx.dimension}"
  have dim : Q(Nat) := ctx.dimensionLit
  let hLt : Q($lo < $dim) ← mkDecideProofQ q($lo < $dim)
  let sumCert ← certAdd (← headCert) (← tailCert)
  return sumCert.

中文:
定义 certSumFromStep
  定义体: do
  let ctx ← read
  unless lo < ctx.dimension do
    throwError "certSumFromStep called with {lo} such that ¬ {lo} < {ctx.dimension}"
  have dim : Q(Nat) := ctx.dimensionLit
  let hLt : Q($lo < $dim) ← mkDecideProofQ q($lo < $dim)
  let sumCert ← certAdd (← headCert) (← tailCert)
  return sumCert.
-/
def certSumFromStep
    (lo : Nat) (f : Q(Nat -> $α))
    (headCert tailCert : CertM rα (Cert rα)) : CertM rα (Cert rα) := do
  let ctx ← read
  unless lo < ctx.dimension do
    throwError "certSumFromStep called with {lo} such that ¬ {lo} < {ctx.dimension}"
  have dim : Q(Nat) := ctx.dimensionLit
  let hLt : Q($lo < $dim) ← mkDecideProofQ q($lo < $dim)
  let sumCert ← certAdd (← headCert) (← tailCert)
  return sumCert.chainProof q(BirdDet.sumFrom_step $dim $lo $f $hLt)

mutual

/--
Definition of `certIterStepEntry` / `certIterStepEntry` 的定义

English:
definition certIterStepEntry
  signature: (t i j : Nat)
  body: do
  if let some c := (← get).iterStepEntryCache[(t, i, j)]? then
    return c
  let ctx ← read
  let {dimensionLit := dimLit, arrayExpr := A, ..} := ctx
  let cert ← match t with
    -- The `t = 0` branch of `Function.iterate`.
    | 0 => do
      let ce ← certEntry i j
      let hIter := q(Functio

中文:
定义 certIterStepEntry
  签名: (t i j : 自然数)
  定义体: do
  if let some c := (← get).iterStepEntryCache[(t, i, j)]? then
    return c
  let ctx ← read
  let {dimensionLit := dimLit, arrayExpr := A, ..} := ctx
  let cert ← match t with
    -- The `t = 0` branch of `Function.iterate`.
    | 0 => do
      let ce ← certEntry i j
      let hIter := q(Functio
-/
partial def certIterStepEntry (t i j : Nat) : CertM rα (Cert rα) := do
  if let some c := (← get).iterStepEntryCache[(t, i, j)]? then
    return c
  let ctx ← read
  let {dimensionLit := dimLit, arrayExpr := A, ..} := ctx
  let cert ← match t with
    -- The `t = 0` branch of `Function.iterate`.
    | 0 => do
      let ce ← certEntry i j
      let hIter := q(Function.iterate_zero_apply
        (BirdDet.stepEntry $dimLit $A) (BirdDet.get $dimLit $A))
      let h := q(congrArg (fun F : Nat -> Nat -> $α => F $i $j) $hIter)
      pure (ce.chainProof h)
    -- The `t = t' + 1` branch of `Function.iterate`.
    | t' + 1 => do
      -- First summand in one `BirdDet.stepEntry` application:
      -- -(sumFrom n (i + 1) fun k => F_t k k) * get n A i j
      let diagSummand := q(fun k => $(ctx.iterStepEntry t') k k)
      let negDiagSum := q(-$(ctx.sumFrom (i + 1) diagSummand))
      let entryCert ← certEntry i j
      let diagProdCert ←
        -- If `get n A i j = 0` then we can skip computation of
        -- `-(sumFrom n (i + 1) fun k => F_t k k)`
        if entryCert.isZero then
          zeroProdCert negDiagSum entryCert
        else do
          let diagSumCert ← certDiag t' (i + 1)
          let negDiagSumCert ← certNeg diagSumCert
          certMul negDiagSumCert entryCert
      -- Second summand in one `BirdDet.stepEntry` application:
      -- sumFrom n (i + 1) fun k => F_t i k * get n A k j
      let tailSumCert ← certTail t' i j (i + 1)
      let rhsCert ← certAdd diagProdCert tailSumCert
      let hStep := q(BirdDet.stepEntry_eq $dimLit $A $(ctx.iterStepEntry t') $i $j)
      let stepCert := rhsCert.chainProof hStep
      let hIter := q(Function.iterate_succ_apply'
(BirdDet.stepEntry $dimLit $A) t' (BirdDet.get $dimLit $A))
      let h := q(congrArg (fun F : Nat -> Nat -> $α => F $i $j) $hIter)
      pure (stepCert.chainProof h)
  modify fun s =>
    {s with iterStepEntryCache := s.iterStepEntryCache.insert (t, i, j) cert}
  return cert


/--
Definition of `certDiag` / `certDiag` 的定义

English:
definition certDiag
  signature: (t lo : Nat)
  body: do
  if let some c := (← get).diagCache[(t, lo)]? then
    return c
  let ctx ← read
  let diagonalSummand := q(fun k => $(ctx.iterStepEntry t) k k)
  let cert ←
    if lo < ctx.dimension
    then do
      let headCert := certIterStepEntry t lo lo
      let tailCert := certDiag t (lo + 1)
      cert

中文:
定义 certDiag
  签名: (t lo : 自然数)
  定义体: do
  if let some c := (← get).diagCache[(t, lo)]? then
    return c
  let ctx ← read
  let diagonalSummand := q(fun k => $(ctx.iterStepEntry t) k k)
  let cert ←
    if lo < ctx.dimension
    then do
      let headCert := certIterStepEntry t lo lo
      let tailCert := certDiag t (lo + 1)
      cert
-/
partial def certDiag (t lo : Nat) : CertM rα (Cert rα) := do
  if let some c := (← get).diagCache[(t, lo)]? then
    return c
  let ctx ← read
  let diagonalSummand := q(fun k => $(ctx.iterStepEntry t) k k)
  let cert ←
    if lo < ctx.dimension
    then do
      let headCert := certIterStepEntry t lo lo
      let tailCert := certDiag t (lo + 1)
      certSumFromStep
        lo
        diagonalSummand
        headCert
        tailCert
    else
      certSumFromStop lo diagonalSummand
  modify fun s => {s with diagCache := s.diagCache.insert (t, lo) cert}
  return cert

/--
Definition of `certTail` / `certTail` 的定义

English:
definition certTail
  signature: (t i j lo : Nat)
  body: do
  let ctx ← read
  let {dimensionLit := dimLit, arrayExpr := A, ..} := ctx
  let tailSummand :=
    q(fun k =>
 (ctx.iterStepEntry t) i k *
BirdDet.get dimLit A k j)
  if lo < ctx.dimension
  then do
    -- headCert certifies `(stepEntry n A)^[t] F i lo * get n A lo j`
    let headCert := do
    

中文:
定义 certTail
  签名: (t i j lo : 自然数)
  定义体: do
  let ctx ← read
  let {dimensionLit := dimLit, arrayExpr := A, ..} := ctx
  let tailSummand :=
    q(fun k =>
 (ctx.iterStepEntry t) i k *
BirdDet.get dimLit A k j)
  if lo < ctx.dimension
  then do
    -- headCert certifies `(stepEntry n A)^[t] F i lo * get n A lo j`
    let headCert := do
    
-/
partial def certTail (t i j lo : Nat) : CertM rα (Cert rα) := do
  let ctx ← read
  let {dimensionLit := dimLit, arrayExpr := A, ..} := ctx
  let tailSummand :=
    q(fun k =>
 (ctx.iterStepEntry t) i k *
BirdDet.get dimLit A k j)
  if lo < ctx.dimension
  then do
    -- headCert certifies `(stepEntry n A)^[t] F i lo * get n A lo j`
    let headCert := do
      let entryCert ← certEntry lo j
      -- If `get n A lo j = 0` then we can skip computation of
      -- `(stepEntry n A)^[t] F i lo`
      if entryCert.isZero
      then
        zeroProdCert
          q($(ctx.iterStepEntry t) $i $lo)
          entryCert
      else do
        let iterateCert ← certIterStepEntry t i lo
        certMul iterateCert entryCert
    let tailCert := certTail t i j (lo + 1)
    certSumFromStep
      lo
      tailSummand
      headCert
      tailCert
  else
    certSumFromStop lo tailSummand

end

/--
Definition of `certBirdDet` / `certBirdDet` 的定义

English:
definition certBirdDet
  signature: : CertM rα (Cert rα)
  body: do
  let ctx ← read
  let {dimension := dim, dimensionLit := dimLit, arrayExpr, ..} := ctx
  if dim == 0
  then
    let ce ← certEval q(1 : $α)
have : dimLit =Q 0 := ⟨⟩
    have A : Q(Array $α) := arrayExpr
    let h := q(BirdDet.birdDet_zero $A)
    return ce.chainProof h
  else
    -- The non-zero

中文:
定义 certBirdDet
  签名: : CertM rα (Cert rα)
  定义体: do
  let ctx ← read
  let {dimension := dim, dimensionLit := dimLit, arrayExpr, ..} := ctx
  if dim == 0
  then
    let ce ← certEval q(1 : $α)
have : dimLit =Q 0 := ⟨⟩
    have A : Q(Array $α) := arrayExpr
    let h := q(BirdDet.birdDet_zero $A)
    return ce.chainProof h
  else
    -- The non-zero
-/
def certBirdDet : CertM rα (Cert rα) := do
  let ctx ← read
  let {dimension := dim, dimensionLit := dimLit, arrayExpr, ..} := ctx
  if dim == 0
  then
    let ce ← certEval q(1 : $α)
have : dimLit =Q 0 := ⟨⟩
    have A : Q(Array $α) := arrayExpr
    let h := q(BirdDet.birdDet_zero $A)
    return ce.chainProof h
  else
    -- The non-zero `BirdDet.birdDet_eq` branch matches `k + 1`
    -- so we set k := `ctx.dimension - 1`.
    let k := dim - 1
    let cs ← certBirdSign k
    let ci ← certIterStepEntry k 0 0
    let cm ← certMul cs ci
    have kLit := mkNatLitQ k
have : dimLit =Q kLit + 1 := ⟨⟩
    let hn : Q($dimLit = $kLit + 1) := q(rfl)
    let h := q(BirdDet.birdDet_eq $dimLit $kLit $arrayExpr $hn)
    return cm.chainProof h

end Mathlib.Tactic.Determinant

end
