/-
Copyright (c) 2024 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

import all Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring.Basic

/-!
# Automation for proving inequalities in commutative (semi)rings

This file provides automation for proving certain kinds of inequalities in commutative semirings:
goals of the form `A ≤ B` and `A < B` for which the ring-normal forms of `A` and `B` differ by a
nonnegative (resp. positive) constant.

For example, `⊢ x + 3 + y < y + x + 4` is in scope because the normal forms of the LHS and RHS are,
respectively, `3 + (x + y)` and `4 + (x + y)`, which differ by an additive constant.

## Main declarations

* `Mathlib.Tactic.Ring.proveLE`: prove goals of the form `A ≤ B` (subject to the scope constraints
  described)
* `Mathlib.Tactic.Ring.proveLT`: prove goals of the form `A < B` (subject to the scope constraints
  described)

## Implementation notes

The automation is provided in the `MetaM` monad; that is, these functions are not user-facing. It
would not be hard to provide user-facing versions (see the test file), but the scope of this
automation is rather specialized and might be confusing to users.

However, this automation serves as the discharger for the `linear_combination` tactic on inequality
goals, so it is available to the user indirectly as the "degenerate" case of that tactic -- that is,
by calling `linear_combination` without arguments.
-/

public meta section

namespace Mathlib.Tactic.Ring

open Lean Qq Meta

/-! Rather than having the metaprograms `Mathlib.Tactic.Ring.evalLE.lean` and
`Mathlib.Tactic.Ring.evalLT.lean` perform all type class inference at the point of use, we record in
advance, as `abbrev`s, a few type class deductions which will certainly be necessary. They add no
new information (they can already be proved by `inferInstance`).

This helps in speeding up the metaprograms in this file substantially -- about a 50% reduction in
heartbeat count in representative test cases -- since otherwise a substantial fraction of their
runtime is devoted to type class inference. -/

section Typeclass

/--
Definition of `addMonoidWithOneOfCommSemiring` / `addMonoidWithOneOfCommSemiring` 的定义

English:
abbreviation addMonoidWithOneOfCommSemiring
  signature: (α : Type*) [CommSemiring α]
  body: inferInstance

中文:
缩写 addMonoidWithOneOfCommSemiring
  签名: (α : 类型) [交换半环 α]
  定义体: inferInstance
-/
abbrev addMonoidWithOneOfCommSemiring (α : Type*) [CommSemiring α] : AddMonoidWithOne α :=
  inferInstance

/--
Definition of `leOfPartialOrder` / `leOfPartialOrder` 的定义

English:
abbreviation leOfPartialOrder
  signature: (α : Type*) [PartialOrder α]
  body: inferInstance

中文:
缩写 leOfPartialOrder
  签名: (α : 类型) [偏序 α]
  定义体: inferInstance
-/
abbrev leOfPartialOrder (α : Type*) [PartialOrder α] : LE α := inferInstance

/--
Definition of `ltOfPartialOrder` / `ltOfPartialOrder` 的定义

English:
abbreviation ltOfPartialOrder
  signature: (α : Type*) [PartialOrder α]
  body: inferInstance

@[deprecated (since := "2026-05-27")] alias amwo_of_cs := addMonoidWithOneOfCommSemiring
@[deprecated (since := "2026-05-27")] alias le_of_po := leOfPartialOrder
@[deprecated (since := "2026-05-27")] alias lt_of_po := ltOfPartialOrder

中文:
缩写 ltOfPartialOrder
  签名: (α : 类型) [偏序 α]
  定义体: inferInstance

@[deprecated (since := "2026-05-27")] alias amwo_of_cs := addMonoidWithOneOfCommSemiring
@[deprecated (since := "2026-05-27")] alias le_of_po := leOfPartialOrder
@[deprecated (since := "2026-05-27")] alias lt_of_po := ltOfPartialOrder
-/
abbrev ltOfPartialOrder (α : Type*) [PartialOrder α] : LT α := inferInstance

@[deprecated (since := "2026-05-27")] alias amwo_of_cs := addMonoidWithOneOfCommSemiring
@[deprecated (since := "2026-05-27")] alias le_of_po := leOfPartialOrder
@[deprecated (since := "2026-05-27")] alias lt_of_po := ltOfPartialOrder

end Typeclass

/-! The lemmas like `add_le_add_right` in the root namespace are stated under minimal type classes,
typically just `[AddRightMono α]` or similar. Here we restate these
lemmas under stronger type class assumptions (`[OrderedCommSemiring α]` or similar), which helps in
speeding up the metaprograms in this file (`Mathlib.Tactic.Ring.proveLT.lean` and
`Mathlib.Tactic.Ring.proveLE.lean`) substantially -- about a 50% reduction in heartbeat count in
representative test cases -- since otherwise a substantial fraction of their runtime is devoted to
type class inference.

These metaprograms at least require `CommSemiring`, `LE`/`LT`, and all
`CovariantClass`/`ContravariantClass` permutations for addition, and in their main use case (in
`linear_combination`) the `Preorder` type class is also required, so it is rather little loss of
generality simply to require `OrderedCommSemiring`/`StrictOrderedCommSemiring`. -/

section Lemma

/--
theorem `add_le_add_left` / 定理 `add_le_add_left`

English:
theorem add_le_add_left
  statement: {α : Type*} [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
  proof: _root_.add_le_add_left bc a

中文:
定理 add_le_add_left
  结论: {α : 类型} [交换半环 α] [偏序 α] [是Ordered环 α]
  证明: _root_.add_le_add_left bc a

Depends on / 依赖: _root_, _root_.add_le_add_left, add_le_add_left
-/
theorem add_le_add_left {α : Type*} [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
    {b c : α} (bc : b <= c) (a : α) :
    b + a <= c + a :=
  _root_.add_le_add_left bc a

/--
theorem `add_le_of_nonpos_left` / 定理 `add_le_of_nonpos_left`

English:
theorem add_le_of_nonpos_left
  statement: {α : Type*} [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
  proof: _root_.add_le_of_nonpos_left h

中文:
定理 add_le_of_nonpos_left
  结论: {α : 类型} [交换半环 α] [偏序 α] [是Ordered环 α]
  证明: _root_.add_le_of_nonpos_left h

Depends on / 依赖: _root_, _root_.add_le_of_nonpos_left, add_le_of_nonpos_left
-/
theorem add_le_of_nonpos_left {α : Type*} [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
    (a : α) {b : α} (h : b <= 0) :
    b + a <= a :=
  _root_.add_le_of_nonpos_left h

/--
theorem `le_add_of_nonneg_left` / 定理 `le_add_of_nonneg_left`

English:
theorem le_add_of_nonneg_left
  statement: {α : Type*} [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
  proof: _root_.le_add_of_nonneg_left h

中文:
定理 le_add_of_nonneg_left
  结论: {α : 类型} [交换半环 α] [偏序 α] [是Ordered环 α]
  证明: _root_.le_add_of_nonneg_left h

Depends on / 依赖: _root_, _root_.le_add_of_nonneg_left, le_add_of_nonneg_left
-/
theorem le_add_of_nonneg_left {α : Type*} [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
    (a : α) {b : α} (h : 0 <= b) :
    a <= b + a :=
  _root_.le_add_of_nonneg_left h

/--
theorem `add_lt_add_left` / 定理 `add_lt_add_left`

English:
theorem add_lt_add_left
  statement: {α : Type*} [CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α]
  proof: _root_.add_lt_add_left bc a

中文:
定理 add_lt_add_left
  结论: {α : 类型} [交换半环 α] [偏序 α] [是StrictOrdered环 α]
  证明: _root_.add_lt_add_left bc a

Depends on / 依赖: _root_, _root_.add_lt_add_left, add_lt_add_left
-/
theorem add_lt_add_left {α : Type*} [CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α]
    {b c : α} (bc : b < c) (a : α) :
    b + a < c + a :=
  _root_.add_lt_add_left bc a

/--
theorem `add_lt_of_neg_left` / 定理 `add_lt_of_neg_left`

English:
theorem add_lt_of_neg_left
  statement: {α : Type*} [CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α]
  proof: _root_.add_lt_of_neg_left a h

中文:
定理 add_lt_of_neg_left
  结论: {α : 类型} [交换半环 α] [偏序 α] [是StrictOrdered环 α]
  证明: _root_.add_lt_of_neg_left a h

Depends on / 依赖: _root_, _root_.add_lt_of_neg_left, add_lt_of_neg_left
-/
theorem add_lt_of_neg_left {α : Type*} [CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α]
    (a : α) {b : α} (h : b < 0) :
    b + a < a :=
  _root_.add_lt_of_neg_left a h

/--
theorem `lt_add_of_pos_left` / 定理 `lt_add_of_pos_left`

English:
theorem lt_add_of_pos_left
  statement: {α : Type*} [CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α]
  proof: _root_.lt_add_of_pos_left a h

中文:
定理 lt_add_of_pos_left
  结论: {α : 类型} [交换半环 α] [偏序 α] [是StrictOrdered环 α]
  证明: _root_.lt_add_of_pos_left a h

Depends on / 依赖: _root_, _root_.lt_add_of_pos_left, lt_add_of_pos_left
-/
theorem lt_add_of_pos_left {α : Type*} [CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α]
    (a : α) {b : α} (h : 0 < b) :
    a < b + a :=
  _root_.lt_add_of_pos_left a h

end Lemma

/--
Inductive type `ExceptType` / 归纳类型 `ExceptType`

English:
inductive ExceptType
  parameters: | tooSmall | notComparable

中文:
归纳类型 ExceptType
  参数: | tooSmall | notComparable
-/
inductive ExceptType | tooSmall | notComparable
export ExceptType (tooSmall notComparable)

/--
Definition of `evalLE` / `evalLE` 的定义

English:
definition evalLE
  signature: {v : Level} {α : Q(Type v)}
  body: do
  let lα : Q(LE $α) := q(leOfPartialOrder $α)
  assumeInstancesCommute
  let ⟨_, pz⟩ ← NormNum.mkOfNat α q(addMonoidWithOneOfCommSemiring $α) q(nat_lit 0)
  let rz : NormNum.Result q((0:$α)) :=
    NormNum.Result.isNat q(addMonoidWithOneOfCommSemiring $α) q(nat_lit 0)
                        (q(N

中文:
定义 evalLE
  签名: {v : Level} {α : Q(类型v)}
  定义体: do
  let lα : Q(LE $α) := q(leOfPartialOrder $α)
  assumeInstancesCommute
  let ⟨_, pz⟩ ← NormNum.mkOfNat α q(addMonoidWithOneOfCommSemiring $α) q(nat_lit 0)
  let rz : NormNum.Result q((0:$α)) :=
    NormNum.Result.isNat q(addMonoidWithOneOfCommSemiring $α) q(nat_lit 0)
                        (q(N
-/
def evalLE {v : Level} {α : Q(Type v)}
    (ics : Q(CommSemiring $α)) (_ : Q(PartialOrder $α)) (_ : Q(IsOrderedRing $α))
    {a b : Q($α)} (va : Ring.ExSum q($ics) a) (vb : Ring.ExSum q($ics) b) :
    MetaM (Except ExceptType Q($a <= $b)) := do
  let lα : Q(LE $α) := q(leOfPartialOrder $α)
  assumeInstancesCommute
  let ⟨_, pz⟩ ← NormNum.mkOfNat α q(addMonoidWithOneOfCommSemiring $α) q(nat_lit 0)
  let rz : NormNum.Result q((0:$α)) :=
    NormNum.Result.isNat q(addMonoidWithOneOfCommSemiring $α) q(nat_lit 0)
                        (q(NormNum.isNat_ofNat $α $pz):)
  match (dependent := true) va, vb with
  /- `0 ≤ 0` -/
| .zero, .zero => pure .ok (q(le_refl (0:$α)):)
  /- For numerals `ca` and `cb`, `ca + x ≤ cb + x` if `ca ≤ cb` -/
  | .add (b := a') (.const (e := xa) ⟨ca, hypa⟩) va', .add (.const (e := xb) ⟨cb, hypb⟩) vb' => do
    unless va'.eq rcNat ringCompare vb' do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLE.core lα rxa rxb | return .error tooSmall
pure .ok (q(add_le_add_left (a := $a') $pf):)
  /- For a numeral `ca ≤ 0`, `ca + x ≤ x` -/
  | .add (.const (e := xa) ⟨ca, hypa⟩) va', _ => do
    unless va'.eq rcNat ringCompare vb do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let NormNum.Result.isTrue pf ← NormNum.evalLE.core lα rxa rz | return .error tooSmall
pure .ok (q(add_le_of_nonpos_left (a := $b) $pf):)
  /- For a numeral `0 ≤ cb`, `x ≤ cb + x` -/
  | _, .add (.const (e := xb) ⟨cb, hypb⟩) vb' => do
    unless va.eq rcNat ringCompare vb' do return .error notComparable
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLE.core lα rz rxb | return .error tooSmall
pure .ok (q(le_add_of_nonneg_left (a := $a) $pf):)
  | _, _ =>
    unless va.eq rcNat ringCompare vb do return .error notComparable
pure .ok (q(le_refl $a):)
--[CommSemiring α] [PartialOrder α] [IsStrictOrderedRing α]
/--
Definition of `evalLT` / `evalLT` 的定义

English:
definition evalLT
  signature: {v : Level} {α : Q(Type v)}
  body: do
  let lα : Q(LT $α) := q(ltOfPartialOrder $α)
  assumeInstancesCommute
  let ⟨_, pz⟩ ← NormNum.mkOfNat α q(addMonoidWithOneOfCommSemiring $α) q(nat_lit 0)
  let rz : NormNum.Result q((0:$α)) :=
    NormNum.Result.isNat q(addMonoidWithOneOfCommSemiring $α) q(nat_lit 0)
                        (q(N

中文:
定义 evalLT
  签名: {v : Level} {α : Q(类型v)}
  定义体: do
  let lα : Q(LT $α) := q(ltOfPartialOrder $α)
  assumeInstancesCommute
  let ⟨_, pz⟩ ← NormNum.mkOfNat α q(addMonoidWithOneOfCommSemiring $α) q(nat_lit 0)
  let rz : NormNum.Result q((0:$α)) :=
    NormNum.Result.isNat q(addMonoidWithOneOfCommSemiring $α) q(nat_lit 0)
                        (q(N
-/
def evalLT {v : Level} {α : Q(Type v)}
    (ics : Q(CommSemiring $α)) (_ : Q(PartialOrder $α)) (_ : Q(IsStrictOrderedRing $α))
    {a b : Q($α)} (va : Ring.ExSum q($ics) a) (vb : Ring.ExSum q($ics) b) :
    MetaM (Except ExceptType Q($a < $b)) := do
  let lα : Q(LT $α) := q(ltOfPartialOrder $α)
  assumeInstancesCommute
  let ⟨_, pz⟩ ← NormNum.mkOfNat α q(addMonoidWithOneOfCommSemiring $α) q(nat_lit 0)
  let rz : NormNum.Result q((0:$α)) :=
    NormNum.Result.isNat q(addMonoidWithOneOfCommSemiring $α) q(nat_lit 0)
                        (q(NormNum.isNat_ofNat $α $pz):)
  match (dependent := true) va, vb with
  /- `0 < 0` -/
  | .zero, .zero => return .error tooSmall
  /- For numerals `ca` and `cb`, `ca + x < cb + x` if `ca < cb` -/
  | .add (b := a') (.const (e := xa) ⟨ca, hypa⟩) va', .add (.const (e := xb) ⟨cb, hypb⟩) vb' => do
    unless va'.eq rcNat ringCompare vb' do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLT.core lα rxa rxb | return .error tooSmall
pure .ok (q(add_lt_add_left $pf $a'):)
  /- For a numeral `ca < 0`, `ca + x < x` -/
  | .add (.const (e := xa) ⟨ca, hypa⟩) va', _ => do
    unless va'.eq rcNat ringCompare vb do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let NormNum.Result.isTrue pf ← NormNum.evalLT.core lα rxa rz | return .error tooSmall
    have pf : Q($xa < 0) := pf
pure .ok (q(add_lt_of_neg_left $b $pf):)
  /- For a numeral `0 < cb`, `x < cb + x` -/
  | _, .add (.const (e := xb) ⟨cb, hypb⟩) vb' => do
    unless va.eq rcNat ringCompare vb' do return .error notComparable
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLT.core lα rz rxb | return .error tooSmall
pure .ok (q(lt_add_of_pos_left $a $pf):)
  | _, _ => return .error notComparable

/--
theorem `le_congr` / 定理 `le_congr`

English:
theorem le_congr
  given: {α : Type*} [LE α] {a b c d : α} (h1 : a = b) (h2 : b <= c) (h3 : d = c)
  proof: by
  rwa [h1, h3]

中文:
定理 le_congr
  条件: {α : 类型} [LE α] {a b c d : α} (h1 : a = b) (h2 : b <= c) (h3 : d = c)
  证明: by
  rwa [h1, h3]
-/
theorem le_congr {α : Type*} [LE α] {a b c d : α} (h1 : a = b) (h2 : b <= c) (h3 : d = c) :
    a <= d := by
  rwa [h1, h3]

/--
theorem `lt_congr` / 定理 `lt_congr`

English:
theorem lt_congr
  given: {α : Type*} [LT α] {a b c d : α} (h1 : a = b) (h2 : b < c) (h3 : d = c)
  proof: by
  rwa [h1, h3]

中文:
定理 lt_congr
  条件: {α : 类型} [LT α] {a b c d : α} (h1 : a = b) (h2 : b < c) (h3 : d = c)
  证明: by
  rwa [h1, h3]
-/
theorem lt_congr {α : Type*} [LT α] {a b c d : α} (h1 : a = b) (h2 : b < c) (h3 : d = c) :
    a < d := by
  rwa [h1, h3]

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `proveLE` / `proveLE` 的定义

English:
definition proveLE
  signature: (g : MVarId)
  body: do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).le?
    | throwError "ring failed: not of the form `A <= B`"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let ics ← synthI

中文:
定义 proveLE
  签名: (g : MVarId)
  定义体: do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).le?
    | throwError "ring failed: not of the form `A <= B`"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let ics ← synthI
-/
def proveLE (g : MVarId) : MetaM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).le?
    | throwError "ring failed: not of the form `A <= B`"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let ics ← synthInstanceQ q(CommSemiring $α)
  let ipo ← synthInstanceQ q(PartialOrder $α)
  let sα ← synthInstanceQ q(IsOrderedRing $α)
  assumeInstancesCommute
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let c ← Common.mkCache q($ics)
  let (⟨a, va, pa⟩, ⟨b, vb, pb⟩)
    ← AtomM.run .instances do
      pure (← Common.eval rcNat (ringCompute c) c e₁,
            ← Common.eval rcNat (ringCompute c) c e₂)
  match ← evalLE ics ipo sα va vb with
  | .ok p => g.assign q(le_congr $pa $p $pb)
  | .error e =>
    let g' ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a <= $b))
    match e with
    | notComparable =>
      throwError "ring failed, ring expressions not equal up to an additive constant\n{g'.mvarId!}"
    | tooSmall => throwError "comparison failed, LHS is larger\n{g'.mvarId!}"

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `proveLT` / `proveLT` 的定义

English:
definition proveLT
  signature: (g : MVarId)
  body: do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).lt?
    | throwError "ring failed: not of the form `A < B`"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let ics ← synthIn

中文:
定义 proveLT
  签名: (g : MVarId)
  定义体: do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).lt?
    | throwError "ring failed: not of the form `A < B`"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let ics ← synthIn
-/
def proveLT (g : MVarId) : MetaM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).lt?
    | throwError "ring failed: not of the form `A < B`"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let ics ← synthInstanceQ q(CommSemiring $α)
  let ipo ← synthInstanceQ q(PartialOrder $α)
  let sα ← synthInstanceQ q(IsStrictOrderedRing $α)
  assumeInstancesCommute
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let c ← Common.mkCache q($ics)
  let (⟨a, va, pa⟩, ⟨b, vb, pb⟩)
    ← AtomM.run .instances do
      pure (← Common.eval rcNat (ringCompute c) c e₁,
            ← Common.eval rcNat (ringCompute c) c e₂)
  match ← evalLT ics ipo sα va vb with
  | .ok p => g.assign q(lt_congr $pa $p $pb)
  | .error e =>
    let g' ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a < $b))
    match e with
    | notComparable =>
      throwError "ring failed, ring expressions not equal up to an additive constant\n{g'.mvarId!}"
    | tooSmall => throwError "comparison failed, LHS is at least as large\n{g'.mvarId!}"

end Mathlib.Tactic.Ring
