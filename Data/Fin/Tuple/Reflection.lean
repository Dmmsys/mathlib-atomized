/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Lemmas for tuples `Fin m → α`

This file contains alternative definitions of common operators on vectors which expand
definitionally to the expected expression when evaluated on `![]` notation.

This allows "proof by reflection", where we prove `f = ![f 0, f 1]` by defining
`FinVec.etaExpand f` to be equal to the RHS definitionally, and then prove that
`f = etaExpand f`.

The definitions in this file should normally not be used directly; the intent is for the
corresponding `*_eq` lemmas to be used in a place where they are definitionally unfolded.

## Main definitions

* `FinVec.seq`
* `FinVec.map`
* `FinVec.sum`
* `FinVec.etaExpand`
-/

@[expose] public section

assert_not_exists Field

namespace FinVec

variable {m : Nat} {α β : Type*}

/--
Definition of `seq` / `seq` 的定义

English:
definition seq
  signature: : forall {m}, (Fin m -> α -> β) -> (Fin m -> α) -> Fin m -> β

中文:
定义 seq
  签名: : 对任意 {m}, (Fin m -> α -> β) -> (Fin m -> α) -> Fin m -> β
-/
def seq : forall {m}, (Fin m -> α -> β) -> (Fin m -> α) -> Fin m -> β
  | 0, _, _ => ![]
  | _ + 1, f, v => Matrix.vecCons (f 0 (v 0)) (seq (Matrix.vecTail f) (Matrix.vecTail v))

@[simp]
/--
theorem `seq_eq` / 定理 `seq_eq`

English:
theorem seq_eq
  statement: forall {m} (f : Fin m -> α -> β) (v : Fin m -> α), seq f v = fun i => f i (v i)
  proof: rfl

中文:
定理 seq_eq
  结论: 对任意 {m} (f : Fin m -> α -> β) (v : Fin m -> α), seq f v = fun i => f i (v i)
  证明: rfl
-/
theorem seq_eq : forall {m} (f : Fin m -> α -> β) (v : Fin m -> α), seq f v = fun i => f i (v i)
  | 0, _, _ => Subsingleton.elim _ _
  | n + 1, f, v =>
    funext fun i => by
      simp_rw [seq, seq_eq]
      refine i.cases ?_ fun i => ?_
      · rfl
      · rw [Matrix.cons_val_succ]
        rfl

example {f₁ f₂ : α -> β} (a₁ a₂ : α) : seq ![f₁, f₂] ![a₁, a₂] = ![f₁ a₁, f₂ a₂] := rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) {m}
  body: seq fun _ => f

中文:
定义 map
  签名: (f : α -> β) {m}
  定义体: seq fun _ => f
-/
def map (f : α -> β) {m} : (Fin m -> α) -> Fin m -> β :=
  seq fun _ => f

/-- This can be used to prove
```lean
example {f : α → β} (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] :=
  (map_eq _ _).symm
```
-/
@[simp]
/--
theorem `map_eq` / 定理 `map_eq`

English:
theorem map_eq
  given: (f : α -> β) {m} (v : Fin m -> α)
  statement: map f v = f ∘ v
  proof: seq_eq _ _

example {f : α -> β} (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] :=
  (map_eq _ _).symm

中文:
定理 map_eq
  条件: (f : α -> β) {m} (v : Fin m -> α)
  结论: map f v = f ∘ v
  证明: seq_eq _ _

example {f : α -> β} (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] :=
  (map_eq _ _).symm

Depends on / 依赖: seq_eq
-/
theorem map_eq (f : α -> β) {m} (v : Fin m -> α) : map f v = f ∘ v :=
  seq_eq _ _

example {f : α -> β} (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] :=
  (map_eq _ _).symm

/--
Definition of `etaExpand` / `etaExpand` 的定义

English:
definition etaExpand
  signature: {m} (v : Fin m -> α)
  body: map id v

中文:
定义 etaExpand
  签名: {m} (v : Fin m -> α)
  定义体: map id v
-/
def etaExpand {m} (v : Fin m -> α) : Fin m -> α :=
  map id v

/-- This can be used to prove
```lean
example (a : Fin 2 → α) : a = ![a 0, a 1] :=
  (etaExpand_eq _).symm
```
-/
@[simp]
/--
theorem `etaExpand_eq` / 定理 `etaExpand_eq`

English:
theorem etaExpand_eq
  given: {m} (v : Fin m -> α)
  statement: etaExpand v = v
  proof: map_eq id v

example (a : Fin 2 -> α) : a = ![a 0, a 1] :=
  (etaExpand_eq _).symm

中文:
定理 etaExpand_eq
  条件: {m} (v : Fin m -> α)
  结论: etaExpand v = v
  证明: map_eq id v

example (a : Fin 2 -> α) : a = ![a 0, a 1] :=
  (etaExpand_eq _).symm

Depends on / 依赖: map_eq
-/
theorem etaExpand_eq {m} (v : Fin m -> α) : etaExpand v = v :=
  map_eq id v

example (a : Fin 2 -> α) : a = ![a 0, a 1] :=
  (etaExpand_eq _).symm

/--
Definition of `Forall` / `Forall` 的定义

English:
definition Forall
  signature: : forall {m} (_ : (Fin m -> α) -> Prop), Prop

中文:
定义 Forall
  签名: : 对任意 {m} (_ : (Fin m -> α) -> 命题), 命题

Depends on / 依赖: forall_iff
-/
def Forall : forall {m} (_ : (Fin m -> α) -> Prop), Prop
  | 0, P => P ![]
  | _ + 1, P => forall x : α, Forall fun v => P (Matrix.vecCons x v)

/-- This can be used to prove
```lean
example (P : (Fin 2 → α) → Prop) : (∀ f, P f) ↔ ∀ a₀ a₁, P ![a₀, a₁] :=
  (forall_iff _).symm
```
-/
@[simp]
/--
theorem `forall_iff` / 定理 `forall_iff`

English:
theorem forall_iff
  statement: forall {m} (P : (Fin m -> α) -> Prop), Forall P ↔ forall x, P x
  proof: (forall_iff _).symm

中文:
定理 forall_iff
  结论: 对任意 {m} (P : (Fin m -> α) -> 命题), Forall P ↔ 对任意 x, P x
  证明: (forall_iff _).symm

Depends on / 依赖: forall_iff
-/
theorem forall_iff : forall {m} (P : (Fin m -> α) -> Prop), Forall P ↔ forall x, P x
  | 0, P => by
    simp only [Forall, Fin.forall_fin_zero_pi]
    rfl
  | .succ n, P => by simp only [Forall, forall_iff, Fin.forall_fin_succ_pi, Matrix.vecCons]

example (P : (Fin 2 -> α) -> Prop) : (forall f, P f) ↔ forall a₀ a₁, P ![a₀, a₁] :=
  (forall_iff _).symm

/--
Definition of `Exists` / `Exists` 的定义

English:
definition Exists
  signature: : forall {m} (_ : (Fin m -> α) -> Prop), Prop

中文:
定义 Exists
  签名: : 对任意 {m} (_ : (Fin m -> α) -> 命题), 命题

Depends on / 依赖: exists_iff
-/
def Exists : forall {m} (_ : (Fin m -> α) -> Prop), Prop
  | 0, P => P ![]
  | _ + 1, P => exists x : α, Exists fun v => P (Matrix.vecCons x v)

/--
theorem `exists_iff` / 定理 `exists_iff`

English:
theorem exists_iff
  statement: forall {m} (P : (Fin m -> α) -> Prop), Exists P ↔ exists x, P x
  proof: (exists_iff _).symm

中文:
定理 exists_iff
  结论: 对任意 {m} (P : (Fin m -> α) -> 命题), Exists P ↔ 存在 x, P x
  证明: (exists_iff _).symm

Depends on / 依赖: exists_iff
-/
theorem exists_iff : forall {m} (P : (Fin m -> α) -> Prop), Exists P ↔ exists x, P x
  | 0, P => by
    simp only [Exists, Fin.exists_fin_zero_pi, Matrix.vecEmpty]
    rfl
  | .succ n, P => by simp only [Exists, exists_iff, Fin.exists_fin_succ_pi, Matrix.vecCons]

example (P : (Fin 2 -> α) -> Prop) : (exists f, P f) ↔ exists a₀ a₁, P ![a₀, a₁] :=
  (exists_iff _).symm

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: [Add α] [Zero α]

中文:
定义 sum
  签名: [Add α] [Zero α]
-/
def sum [Add α] [Zero α] : forall {m} (_ : Fin m -> α), α
  | 0, _ => 0
  | 1, v => v 0
  | _ + 2, v => sum (fun i => v (Fin.castSucc i)) + v (Fin.last _)

-- `to_additive` without `existing` fails, see
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/to_additive.20complains.20about.20equation.20lemmas/near/508910537
/-- `Finset.univ.prod` with better defeq for `Fin`. -/
@[to_additive existing]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: [Mul α] [One α]

中文:
定义 prod
  签名: [Mul α] [One α]

Depends on / 依赖: prod_eq, to_additive
-/
def prod [Mul α] [One α] : forall {m} (_ : Fin m -> α), α
  | 0, _ => 1
  | 1, v => v 0
  | _ + 2, v => prod (fun i => v (Fin.castSucc i)) * v (Fin.last _)

/-- This can be used to prove
```lean
example [CommMonoid α] (a : Fin 3 → α) : ∏ i, a i = a 0 * a 1 * a 2 :=
  (prod_eq _).symm
```
-/
@[to_additive (attr := simp)
/-- This can be used to prove
```lean
example [AddCommMonoid α] (a : Fin 3 → α) : ∑ i, a i = a 0 + a 1 + a 2 :=
  (sum_eq _).symm
``` -/]
/--
theorem `prod_eq` / 定理 `prod_eq`

English:
theorem prod_eq
  given: [CommMonoid α]
  statement: forall {m} (a : Fin m -> α), prod a = ∏ i, a i
  proof: (prod_eq _).symm

example [AddCommMonoid α] (a : Fin 3 -> α) : ∑ i, a i = a 0 + a 1 + a 2 :=
  (sum_eq _).symm

中文:
定理 prod_eq
  条件: [CommMonoid α]
  结论: 对任意 {m} (a : Fin m -> α), prod a = ∏ i, a i
  证明: (prod_eq _).symm

example [AddCommMonoid α] (a : Fin 3 -> α) : ∑ i, a i = a 0 + a 1 + a 2 :=
  (sum_eq _).symm

Depends on / 依赖: prod_eq
-/
theorem prod_eq [CommMonoid α] : forall {m} (a : Fin m -> α), prod a = ∏ i, a i
  | 0, _ => rfl
  | 1, a => (Fintype.prod_unique a).symm
  | n + 2, a => by rw [Fin.prod_univ_castSucc, prod, prod_eq]

example [CommMonoid α] (a : Fin 3 -> α) : ∏ i, a i = a 0 * a 1 * a 2 :=
  (prod_eq _).symm

example [AddCommMonoid α] (a : Fin 3 -> α) : ∑ i, a i = a 0 + a 1 + a 2 :=
  (sum_eq _).symm

section Meta
open Lean Meta Qq

/-- Produce a term of the form `f 0 * f 1 * ... * f (n - 1)` and an application of `FinVec.prod_eq`
that shows it is equal to `∏ i, f i`. -/
meta def mkProdEqQ {u : Level} {α : Q(Type u)}
    (inst : Q(CommMonoid $α)) (n : Nat) (f : Q(Fin $n -> $α)) :
MetaM (val : Q($α)) × Q(∏ i, $f i = $val) :=
  match n with
  | 0 => do return ⟨q((1 : $α)), q(Fin.prod_univ_zero $f)⟩
  | m + 1 => do
    let nezero : Q(NeZero ($m + 1)) := q(⟨Nat.succ_ne_zero _⟩)
    let val ← makeRHS (m + 1) f nezero (m + 1)
let _ : val =Q FinVec.prod f := ⟨⟩
    return ⟨q($val), q(FinVec.prod_eq $f |>.symm)⟩
where
  /-- Creates the expression `f 0 * f 1 * ... * f (n - 1)`. -/
  makeRHS (n : Nat) (f : Q(Fin $n -> $α)) (nezero : Q(NeZero $n)) (k : Nat) : MetaM Q($α) := do
  match k with
  | 0 => failure
  | 1 => pure q($f 0)
  | m + 1 =>
    let pre ← makeRHS n f nezero m
    let mRaw : Q(Nat) := mkRawNatLit m
    pure q($pre * $f (OfNat.ofNat $mRaw))

/-- Produce a term of the form `f 0 + f 1 + ... + f (n - 1)` and an application of `FinVec.sum_eq`
that shows it is equal to `∑ i, f i`. -/
meta def mkSumEqQ {u : Level} {α : Q(Type u)}
    (inst : Q(AddCommMonoid $α)) (n : Nat) (f : Q(Fin $n -> $α)) :
MetaM (val : Q($α)) × Q(∑ i, $f i = $val) :=
  match n with
  | 0 => return ⟨q((0 : $α)), q(Fin.sum_univ_zero $f)⟩
  | m + 1 => do
    let nezero : Q(NeZero ($m + 1)) := q(⟨Nat.succ_ne_zero _⟩)
    let val ← makeRHS (m + 1) f nezero (m + 1)
let _ : val =Q FinVec.sum f := ⟨⟩
    return ⟨q($val), q(FinVec.sum_eq $f |>.symm)⟩
where
  /-- Creates the expression `f 0 + f 1 + ... + f (n - 1)`. -/
  makeRHS (n : Nat) (f : Q(Fin $n -> $α)) (nezero : Q(NeZero $n)) (k : Nat) : MetaM Q($α) := do
  match k with
  | 0 => failure
  | 1 => pure q($f 0)
  | m + 1 =>
    let pre ← makeRHS n f nezero m
    let mRaw : Q(Nat) := mkRawNatLit m
    pure q($pre + $f (OfNat.ofNat $mRaw))

end Meta

end FinVec

namespace Fin
open Qq Lean FinVec

/-- Rewrites `∏ i : Fin n, f i` as `f 0 * f 1 * ... * f (n - 1)` when `n` is a numeral. -/
simproc_decl prod_univ_ofNat (∏ _ : Fin _, _) := .ofQ fun u _ e => do
  match u, e with
  | .succ _, ~q(@Finset.prod (Fin $n) _ $inst (@Finset.univ _ $instF) $f) => do
    match n.nat? with
    | none =>
      return .continue
    | some nVal =>
      let ⟨res, pf⟩ ← mkProdEqQ inst nVal f
      let ⟨_⟩ ← assertDefEqQ q($instF) q(Fin.fintype _)
have _ : n =Q nVal := ⟨⟩
return .visit .mk q($res) some q($pf)
  | _, _ => return .continue

/-- Rewrites `∑ i : Fin n, f i` as `f 0 + f 1 + ... + f (n - 1)` when `n` is a numeral. -/
simproc_decl sum_univ_ofNat (∑ _ : Fin _, _) := .ofQ fun u _ e => do
  match u, e with
  | .succ _, ~q(@Finset.sum (Fin $n) _ $inst (@Finset.univ _ $instF) $f) => do
    match n.nat? with
    | none =>
      return .continue
    | some nVal =>
      let ⟨res, pf⟩ ← mkSumEqQ inst nVal f
      let ⟨_⟩ ← assertDefEqQ q($instF) q(Fin.fintype _)
have _ : n =Q nVal := ⟨⟩
return .visit .mk q($res) some q($pf)
  | _, _ => return .continue

end Fin
