/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Multiset.Bind
public meta import Mathlib.Tactic.ToDual

/-!
# Big operators

In this file we define products and sums indexed by finite sets (specifically, `Finset`).

## Notation

We introduce the following notation.

Let `s` be a `Finset ι`, and `f : ι → β` a function.

* `∏ x ∈ s, f x` is notation for `Finset.prod s f` (assuming `β` is a `CommMonoid`)
* `∑ x ∈ s, f x` is notation for `Finset.sum s f` (assuming `β` is an `AddCommMonoid`)
* `∏ x, f x` is notation for `Finset.prod Finset.univ f`
  (assuming `ι` is a `Fintype` and `β` is a `CommMonoid`)
* `∑ x, f x` is notation for `Finset.sum Finset.univ f`
  (assuming `ι` is a `Fintype` and `β` is an `AddCommMonoid`)
* `∏ x ∈ s with p x, f x` is notation for `Finset.prod (Finset.filter p s) f`.
* `∑ x ∈ s with p x, f x` is notation for `Finset.sum (Finset.filter p s) f`.
* `∏ (x ∈ s) (y ∈ t), f x y` is notation for `Finset.prod (s ×ˢ t) (fun ⟨x, y⟩ ↦ f x y)`.
* `∑ (x ∈ s) (y ∈ t), f x y` is notation for `Finset.sum (s ×ˢ t) (fun ⟨x, y⟩ ↦ f x y)`.
* Other supported binders: `x < n`, `x > n`, `x ≤ n`, `x ≥ n`, `x ≠ n`, `x ∉ s`, `x + y = n`

## Implementation Notes

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

-/

@[expose] public section

assert_not_exists AddCommMonoidWithOne
assert_not_exists MonoidWithZero
assert_not_exists MulAction
assert_not_exists IsOrderedMonoid

variable {ι κ M N G α : Type*}

open Fin Function

namespace Finset

/-- `∏ x ∈ s, f x` is the product of `f x` as `x` ranges over the elements of the finite set `s`.

When the index type is a `Fintype`, the notation `∏ x, f x`, is a shorthand for
`∏ x ∈ Finset.univ, f x`. -/
@[to_additive /-- `∑ x ∈ s, f x` is the sum of `f x` as `x` ranges over the elements
of the finite set `s`.

When the index type is a `Fintype`, the notation `∑ x, f x`, is a shorthand for
`∑ x ∈ Finset.univ, f x`. -/]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: [CommMonoid M] (s : Finset ι) (f : ι -> M)
  body: (s.1.map f).prod

@[to_additive (attr := simp)]

中文:
定义 prod
  签名: [CommMonoid M] (s : Finset ι) (f : ι -> M)
  定义体: (s.1.map f).prod

@[to_additive (attr := simp)]
-/
protected def prod [CommMonoid M] (s : Finset ι) (f : ι -> M) : M :=
  (s.1.map f).prod

@[to_additive (attr := simp)]
/--
theorem `prod_mk` / 定理 `prod_mk`

English:
theorem prod_mk
  given: [CommMonoid M] (s : Multiset ι) (hs : s.Nodup) (f : ι -> M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 prod_mk
  条件: [CommMonoid M] (s : Multiset ι) (hs : s.Nodup) (f : ι -> M)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem prod_mk [CommMonoid M] (s : Multiset ι) (hs : s.Nodup) (f : ι -> M) :
    (⟨s, hs⟩ : Finset ι).prod f = (s.map f).prod :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `prod_val` / 定理 `prod_val`

English:
theorem prod_val
  given: [CommMonoid M] (s : Finset M)
  statement: s.1.prod = s.prod id
  proof: by
  rw [Finset.prod]; rw [Multiset.map_id]

中文:
定理 prod_val
  条件: [CommMonoid M] (s : Finset M)
  结论: s.1.prod = s.prod id
  证明: by
  rw [Finset.prod]; rw [Multiset.map_id]

Depends on / 依赖: Finset, Finset.prod, Multiset, Multiset.map_id, map_id
-/
theorem prod_val [CommMonoid M] (s : Finset M) : s.1.prod = s.prod id := by
  rw [Finset.prod]; rw [Multiset.map_id]

end Finset

library_note «operator precedence of big operators» /--
There is no established mathematical convention
for the operator precedence of big operators like `∏` and `∑`.
We will have to make a choice.

Online discussions, such as https://math.stackexchange.com/q/185538/30839
seem to suggest that `∏` and `∑` should have the same precedence,
and that this should be somewhere between `*` and `+`.
The latter have precedence levels `70` and `65` respectively,
and we therefore choose the level `67`.

In practice, this means that parentheses should be placed as follows:
```lean
∑ k ∈ K, (a k + b k) = ∑ k ∈ K, a k + ∑ k ∈ K, b k →
  ∏ k ∈ K, a k * b k = (∏ k ∈ K, a k) * (∏ k ∈ K, b k)
```
(Example taken from page 490 of Knuth's *Concrete Mathematics*.)
-/

namespace BigOperators
open Batteries.ExtendedBinder Lean Meta

-- TODO: contribute this modification back to `extBinder`

/-- A `bigOpBinder` is like an `extBinder` and has the form `x`, `x : ty`, or `x pred`
where `pred` is a `binderPred` like `< 2`.
Unlike `extBinder`, `x` is a term. -/
syntax bigOpBinder := term:max((" : "term) <|> binderPred)?
/-- A BigOperator binder in parentheses -/
syntax bigOpBinderParenthesized := " ("bigOpBinder")"
/-- A list of parenthesized binders -/
syntax bigOpBinderCollection := bigOpBinderParenthesized+
/-- A single (unparenthesized) binder, or a list of parenthesized binders -/
syntax bigOpBinders := bigOpBinderCollection > (ppSpace bigOpBinder)

/-- Collects additional binder/Finset pairs for the given `bigOpBinder`.

Note: this is not extensible at the moment, unlike the usual `bigOpBinder` expansions. -/
meta def processBigOpBinder (processed : (Array (Term × Term))) (binder : TSyntax ``bigOpBinder) :
    MacroM (Array (Term × Term)) :=
  set_option hygiene false in
  withRef binder do
    match binder with
    | `(bigOpBinder| $x:term) =>
      match x with
      | `(($a + $b = $n)) => -- Maybe this is too cute.
.push (← `(⟨$a, $b⟩), ← `(Finset.Nat.antidiagonal $n)) return processed
.push (x, ← ``(Finset.univ)) | _ => return processed
.push (x, ← ``((Finset.univ : Finset $t))) | `(bigOpBinder| $x : $t) => return processed
.push (x, ← `(finset% $s)) | `(bigOpBinder| $x in $s) => return processed
.push (x, ← `(finset% $sᶜ)) | `(bigOpBinder| $x ∉ $s) => return processed
.push (x, ← `(Finset.univ.erase $n)) | `(bigOpBinder| $x != $n) => return processed
.push (x, ← `(Finset.Iio $n)) | `(bigOpBinder| $x < $n) => return processed
.push (x, ← `(Finset.Iic $n)) | `(bigOpBinder| $x <= $n) => return processed
.push (x, ← `(Finset.Ioi $n)) | `(bigOpBinder| $x > $n) => return processed
.push (x, ← `(Finset.Ici $n)) | `(bigOpBinder| $x >= $n) => return processed
    | _ => Macro.throwUnsupported

/-- Collects the binder/Finset pairs for the given `bigOpBinders`. -/
meta def processBigOpBinders (binders : TSyntax ``bigOpBinders) :
    MacroM (Array (Term × Term)) :=
  match binders with
  | `(bigOpBinders| $b:bigOpBinder) => processBigOpBinder #[] b
  | `(bigOpBinders| $[($bs:bigOpBinder)]*) => bs.foldlM processBigOpBinder #[]
  | _ => Macro.throwUnsupported

/-- Collects the binderIdents into a `⟨...⟩` expression. -/
meta def bigOpBindersPattern (processed : Array (Term × Term)) : MacroM Term := do
  let ts := processed.map Prod.fst
  if h : ts.size = 1 then
    return ts[0]
  else
    `(⟨$ts,*⟩)

/-- Collects the terms into a product of sets. -/
meta def bigOpBindersProd (processed : Array (Term × Term)) : MacroM Term := do
  if h₀ : processed.size = 0 then
    `((Finset.univ : Finset Unit))
  else if h₁ : processed.size = 1 then
    return processed[0].2
  else
    processed.foldrM (fun s p => `(SProd.sprod $(s.2) $p)) processed.back.2
      (start := processed.size - 1)

/-- A `with`-clause in a big operator. Example usage: `∑ i < 100 with Even i, f i`. -/
syntax BigOpWith := " with " atomic(binderIdent " : ")? term

/--
- `∑ x, f x` is notation for `Finset.sum Finset.univ f`. It is the sum of `f x`,
  where `x` ranges over the finite domain of `f`.
- `∑ x ∈ s, f x` is notation for `Finset.sum s f`. It is the sum of `f x`,
  where `x` ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
- `∑ x ∈ s with p x, f x` is notation for `Finset.sum (Finset.filter p s) f`.
- `∑ x ∈ s with h : p x, f x h` is notation for `Finset.sum s fun x ↦ if h : p x then f x h else 0`.
- `∑ (x ∈ s) (y ∈ t), f x y` is notation for `Finset.sum (s ×ˢ t) (fun ⟨x, y⟩ ↦ f x y)`.

These support destructuring, for example `∑ ⟨x, y⟩ ∈ s ×ˢ t, f x y`.

Notation: `"∑" bigOpBinders* (" with" (ident ":")? term)? "," term` -/
syntax (name := bigsum) "∑ " bigOpBinders BigOpWith ? ", " term:67 : term

/--
- `∏ x, f x` is notation for `Finset.prod Finset.univ f`. It is the product of `f x`,
  where `x` ranges over the finite domain of `f`.
- `∏ x ∈ s, f x` is notation for `Finset.prod s f`. It is the product of `f x`,
  where `x` ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
- `∏ x ∈ s with p x, f x` is notation for `Finset.prod (Finset.filter p s) f`.
- `∏ x ∈ s with h : p x, f x h` is notation for
  `Finset.prod s fun x ↦ if h : p x then f x h else 1`.
- `∏ (x ∈ s) (y ∈ t), f x y` is notation for `Finset.prod (s ×ˢ t) (fun ⟨x, y⟩ ↦ f x y)`.

These support destructuring, for example `∏ ⟨x, y⟩ ∈ s ×ˢ t, f x y`.

Notation: `"∏" bigOpBinders* ("with" (ident ":")? term)? "," term` -/
syntax (name := bigprod) "∏ " bigOpBinders BigOpWith ? ", " term:67 : term

macro_rules (kind := bigsum)
  | `(∑ $bs:bigOpBinders $[with $[$hx??:binderIdent :]? $p?:term]?, $v) => do
    let processed ← processBigOpBinders bs
    let x ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    -- `a` is interpreted as the filtering proposition, unless `b` exists, in which case `a` is the
    -- proof and `b` is the filtering proposition
    match hx??, p? with
    | some (some hx), some p =>
      `(Finset.sum $s fun $x => if $hx : $p then $v else 0)
    | _, some p => `(Finset.sum (Finset.filter (fun $x => $p) $s) (fun $x => $v))
    | _, none => `(Finset.sum $s (fun $x => $v))

macro_rules (kind := bigprod)
  | `(∏ $bs:bigOpBinders $[with $[$hx??:binderIdent :]? $p?:term]?, $v) => do
    let processed ← processBigOpBinders bs
    let x ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    -- `a` is interpreted as the filtering proposition, unless `b` exists, in which case `a` is the
    -- proof and `b` is the filtering proposition
    match hx??, p? with
    | some (some hx), some p =>
      `(Finset.prod $s fun $x => if $hx : $p then $v else 1)
    | _, some p => `(Finset.prod (Finset.filter (fun $x => $p) $s) (fun $x => $v))
    | _, none => `(Finset.prod $s (fun $x => $v))

open PrettyPrinter.Delaborator SubExpr
open scoped Batteries.ExtendedBinder

/--
Inductive type `FinsetResult` / 归纳类型 `FinsetResult`

English:
inductive FinsetResult
  parameters: where
  constructors (6):
    - finset: (s : Term)
    - univ: 
    - Iio: (n : Term)
    - Iic: (n : Term)
    - Ioi: (n : Term)
    - Ici: (n : Term)

中文:
归纳类型 FinsetResult
  参数: where
  构造子 (6 个):
    - finset: (s : Term)
    - univ: 
    - Iio: (n : Term)
    - Iic: (n : Term)
    - Ioi: (n : Term)
    - Ici: (n : Term)
-/
private inductive FinsetResult where
  | finset (s : Term)
  | univ
  | Iio (n : Term)
  | Iic (n : Term)
  | Ioi (n : Term)
  | Ici (n : Term)

/--
Definition of `FinsetFilterResult` / `FinsetFilterResult` 的定义

English:
structure FinsetFilterResult
  parameters: where
  axioms and operations (2):
    - finset : FinsetResult
    - filter : Option Term

中文:
结构 FinsetFilterResult
  参数: where
  公理与运算 (2 个):
    - finset : FinsetResult
    - filter : Option Term
-/
private structure FinsetFilterResult where
  finset : FinsetResult
  filter : Option Term

/-- Delaborates a finset indexing a big operator. -/
private meta def delabFinsetResult : DelabM FinsetResult := do
  let s ← getExpr
  if s.isAppOfArity ``Finset.univ 2 then
    return .univ
  else if s.isAppOfArity `Finset.Iio 4 then
    let ss ← withNaryArg 3 delab
    return .Iio ss
  else if s.isAppOfArity `Finset.Iic 4 then
    let ss ← withNaryArg 3 delab
    return .Iic ss
  else if s.isAppOfArity `Finset.Ioi 4 then
    let ss ← withNaryArg 3 delab
    return .Ioi ss
  else if s.isAppOfArity `Finset.Ici 4 then
    let ss ← withNaryArg 3 delab
    return .Ici ss
  else
    let ss ← delab
    return .finset ss

/-- Delaborates a finset indexing a big operator. In case the finset involves a filter,
`i` is used for the binder name. -/
private meta def delabFinsetArg (i : Ident) : DelabM FinsetFilterResult := do
  let s ← getExpr
  if s.isAppOfArity ``Finset.filter 4 then
    let p ←
      withNaryArg 1 do
        if (← getExpr).isLambda then
          withBindingBody i.getId delab
        else
          let p ← delab
          return (← `($p $i))
    let r ← withNaryArg 3 delabFinsetResult
    return ⟨r, some p⟩
  else
    let r ← delabFinsetResult
    return ⟨r, none⟩

/-- Delaborator for `Finset.prod`. The `pp.funBinderTypes` option controls whether
to show the domain type when the product is over `Finset.univ`. -/
@[app_delab Finset.prod] meta def delabFinsetProd : Delab :=
whenPPOption getPPNotation withOverApp 5 do
  let #[_, _, _, _, f] := (← getExpr).getAppArgs | failure
  guard f.isLambda
let ppDomain ← withAppArg getPPOption getPPFunBinderTypes
let (i, body) ← withAppArg withBindingBodyUnusedName fun i => do
    return ((⟨i⟩ : Ident), ← delab)
let ⟨res, p⟩ ← withNaryArg 3 delabFinsetArg i
  let withClause? : Option (TSyntax `BigOperators.BigOpWith) ← (match p with
    | .some pp => return some (← `(BigOpWith|with $pp:term))
    | .none => return none)
  match res with
  | .finset ss => `(∏ $i:ident in $ss $[$withClause?]?, $body)
  | .univ =>
    let binder ←
    if ppDomain then
      let ty ← withNaryArg 0 delab
      `(bigOpBinder| $i:ident : $ty)
    else
      `(bigOpBinder| $i:ident)
    `(∏ $binder:bigOpBinder $[$withClause?]?, $body)
  | .Iio ss => `(∏ $i:ident < $ss $[$withClause?]?, $body)
  | .Iic ss => `(∏ $i:ident <= $ss $[$withClause?]?, $body)
  | .Ioi ss => `(∏ $i:ident > $ss $[$withClause?]?, $body)
  | .Ici ss => `(∏ $i:ident >= $ss $[$withClause?]?, $body)

/-- Delaborator for `Finset.sum`. The `pp.funBinderTypes` option controls whether
to show the domain type when the sum is over `Finset.univ`. -/
@[app_delab Finset.sum] meta def delabFinsetSum : Delab :=
whenPPOption getPPNotation withOverApp 5 do
  let #[_, _, _, _, f] := (← getExpr).getAppArgs | failure
  guard f.isLambda
let ppDomain ← withAppArg getPPOption getPPFunBinderTypes
let (i, body) ← withAppArg withBindingBodyUnusedName fun i => do
    return ((⟨i⟩ : Ident), ← delab)
let ⟨res, p⟩ ← withNaryArg 3 delabFinsetArg i
  let withClause? : Option (TSyntax `BigOperators.BigOpWith) ← (match p with
    | .some pp => return some (← `(BigOpWith|with $pp:term))
    | .none => return none)
  match res with
  | .finset ss => `(∑ $i:ident in $ss $[$withClause?]?, $body)
  | .univ =>
    let binder ←
    if ppDomain then
      let ty ← withNaryArg 0 delab
      `(bigOpBinder| $i:ident : $ty)
    else
      `(bigOpBinder| $i:ident)
    `(∑ $binder:bigOpBinder $[$withClause?]?, $body)
  | .Iio ss => `(∑ $i:ident < $ss $[$withClause?]?, $body)
  | .Iic ss => `(∑ $i:ident <= $ss $[$withClause?]?, $body)
  | .Ioi ss => `(∑ $i:ident > $ss $[$withClause?]?, $body)
  | .Ici ss => `(∑ $i:ident >= $ss $[$withClause?]?, $body)

end BigOperators

namespace Finset

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι -> M}

@[to_additive]
/--
theorem `prod_eq_multiset_prod` / 定理 `prod_eq_multiset_prod`

English:
theorem prod_eq_multiset_prod
  given: [CommMonoid M] (s : Finset ι) (f : ι -> M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 prod_eq_multiset_prod
  条件: [CommMonoid M] (s : Finset ι) (f : ι -> M)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem prod_eq_multiset_prod [CommMonoid M] (s : Finset ι) (f : ι -> M) :
    ∏ x in s, f x = (s.1.map f).prod :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `prod_map_val` / 引理 `prod_map_val`

English:
lemma prod_map_val
  given: [CommMonoid M] (s : Finset ι) (f : ι -> M)
  statement: (s.1.map f).prod = ∏ a in s, f a
  proof: rfl

@[simp]

中文:
引理 prod_map_val
  条件: [CommMonoid M] (s : Finset ι) (f : ι -> M)
  结论: (s.1.map f).prod = ∏ a in s, f a
  证明: rfl

@[simp]
-/
lemma prod_map_val [CommMonoid M] (s : Finset ι) (f : ι -> M) : (s.1.map f).prod = ∏ a in s, f a :=
  rfl

@[simp]
/--
theorem `sum_multiset_singleton` / 定理 `sum_multiset_singleton`

English:
theorem sum_multiset_singleton
  given: (s : Finset ι)
  statement: ∑ a in s, {a} = s.val
  proof: by
  simp only [sum_eq_multiset_sum, Multiset.sum_map_singleton]

中文:
定理 sum_multiset_singleton
  条件: (s : Finset ι)
  结论: ∑ a in s, {a} = s.val
  证明: by
  simp only [sum_eq_multiset_sum, Multiset.sum_map_singleton]

Depends on / 依赖: Multiset, Multiset.sum_map_singleton, sum_eq_multiset_sum, sum_map_singleton
-/
theorem sum_multiset_singleton (s : Finset ι) : ∑ a in s, {a} = s.val := by
  simp only [sum_eq_multiset_sum, Multiset.sum_map_singleton]

end Finset

@[to_additive (attr := simp)]
/--
theorem `map_prod` / 定理 `map_prod`

English:
theorem map_prod
  statement: [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G M N] [MonoidHomClass G M N]
  proof: by
  simp only [Finset.prod_eq_multiset_prod, map_multiset_prod, Multiset.map_map]; rfl

中文:
定理 map_prod
  结论: [CommMonoid M] [CommMonoid N] {G : 类型} [FunLike G M N] [MonoidHomClass G M N]
  证明: by
  simp only [Finset.prod_eq_multiset_prod, map_multiset_prod, Multiset.map_map]; rfl

Depends on / 依赖: Finset, Finset.prod_eq_multiset_prod, Multiset, Multiset.map_map, map_map, map_multiset_prod, prod_eq_multiset_prod
-/
theorem map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G M N] [MonoidHomClass G M N]
    (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s, f x) = ∏ x in s, g (f x) := by
  simp only [Finset.prod_eq_multiset_prod, map_multiset_prod, Multiset.map_map]; rfl

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι -> M}

namespace Finset

section CommMonoid

variable [CommMonoid M]

@[to_additive (attr := simp)]
/--
theorem `prod_empty` / 定理 `prod_empty`

English:
theorem prod_empty
  statement: ∏ x in ∅, f x = 1
  proof: rfl

中文:
定理 prod_empty
  结论: ∏ x in ∅, f x = 1
  证明: rfl
-/
theorem prod_empty : ∏ x in ∅, f x = 1 :=
  rfl

/-- Variant of `prod_empty` not applied to a function. -/
@[to_additive (attr := grind =)]
/--
theorem `prod_empty'` / 定理 `prod_empty'`

English:
theorem prod_empty'
  statement: Finset.prod (∅ : Finset ι) = fun (_ : ι -> M) => 1
  proof: rfl

@[to_additive]

中文:
定理 prod_empty'
  结论: Finset.prod (∅ : Finset ι) = fun (_ : ι -> M) => 1
  证明: rfl

@[to_additive]
-/
theorem prod_empty' : Finset.prod (∅ : Finset ι) = fun (_ : ι -> M) => 1 :=
  rfl

@[to_additive]
/--
theorem `prod_of_isEmpty` / 定理 `prod_of_isEmpty`

English:
theorem prod_of_isEmpty
  given: [IsEmpty ι] (s : Finset ι)
  statement: ∏ i in s, f i = 1
  proof: by
  rw [eq_empty_of_isEmpty s]; rw [prod_empty]

@[to_additive (attr := simp)]

中文:
定理 prod_of_isEmpty
  条件: [IsEmpty ι] (s : Finset ι)
  结论: ∏ i in s, f i = 1
  证明: by
  rw [eq_empty_of_isEmpty s]; rw [prod_empty]

@[to_additive (attr := simp)]

Depends on / 依赖: eq_empty_of_isEmpty, prod_empty
-/
theorem prod_of_isEmpty [IsEmpty ι] (s : Finset ι) : ∏ i in s, f i = 1 := by
  rw [eq_empty_of_isEmpty s]; rw [prod_empty]

@[to_additive (attr := simp)]
/--
theorem `prod_const_one` / 定理 `prod_const_one`

English:
theorem prod_const_one
  statement: (∏ _x in s, (1 : M)) = 1
  proof: by
  simp only [Finset.prod, Multiset.map_const', Multiset.prod_replicate, one_pow]

@[to_additive (attr := simp)]

中文:
定理 prod_const_one
  结论: (∏ _x in s, (1 : M)) = 1
  证明: by
  simp only [Finset.prod, Multiset.map_const', Multiset.prod_replicate, one_pow]

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod, Multiset, Multiset.map_const, Multiset.prod_replicate, map_const, one_pow, prod_replicate
-/
theorem prod_const_one : (∏ _x in s, (1 : M)) = 1 := by
  simp only [Finset.prod, Multiset.map_const', Multiset.prod_replicate, one_pow]

@[to_additive (attr := simp)]
/--
theorem `prod_map` / 定理 `prod_map`

English:
theorem prod_map
  given: (s : Finset ι) (e : ι ↪ κ) (f : κ -> M)
  proof: by
  rw [Finset.prod]; rw [Finset.map_val]; rw [Multiset.map_map]; rfl

中文:
定理 prod_map
  条件: (s : Finset ι) (e : ι ↪ κ) (f : κ -> M)
  证明: by
  rw [Finset.prod]; rw [Finset.map_val]; rw [Multiset.map_map]; rfl

Depends on / 依赖: Finset, Finset.map_val, Finset.prod, Multiset, Multiset.map_map, map_map, map_val
-/
theorem prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) :
    ∏ x in s.map e, f x = ∏ x in s, f (e x) := by
  rw [Finset.prod]; rw [Finset.map_val]; rw [Multiset.map_map]; rfl

/-- Variant of `prod_map` not applied to a function. -/
@[to_additive (attr := grind =)]
/--
theorem `prod_map'` / 定理 `prod_map'`

English:
theorem prod_map'
  given: (s : Finset ι) (e : ι ↪ κ)
  proof: by
  funext f
  simp

中文:
定理 prod_map'
  条件: (s : Finset ι) (e : ι ↪ κ)
  证明: by
  funext f
  simp
-/
theorem prod_map' (s : Finset ι) (e : ι ↪ κ) :
    Finset.prod (s.map e) = fun (f : κ -> M) => ∏ x in s, f (e x) := by
  funext f
  simp

section ToList

@[to_additive (attr := simp, grind =)]
/--
theorem `prod_map_toList` / 定理 `prod_map_toList`

English:
theorem prod_map_toList
  given: (s : Finset ι) (f : ι -> M)
  statement: (s.toList.map f).prod = s.prod f
  proof: by
  rw [Finset.prod]; rw [← Multiset.prod_coe]; rw [← Multiset.map_coe]; rw [Finset.coe_toList]

@[to_additive (attr := simp, grind =)]

中文:
定理 prod_map_toList
  条件: (s : Finset ι) (f : ι -> M)
  结论: (s.toList.map f).prod = s.prod f
  证明: by
  rw [Finset.prod]; rw [← Multiset.prod_coe]; rw [← Multiset.map_coe]; rw [Finset.coe_toList]

@[to_additive (attr := simp, grind =)]

Depends on / 依赖: Finset, Finset.coe_toList, Finset.prod, Multiset, Multiset.map_coe, Multiset.prod_coe, coe_toList, map_coe, prod_coe
-/
theorem prod_map_toList (s : Finset ι) (f : ι -> M) : (s.toList.map f).prod = s.prod f := by
  rw [Finset.prod]; rw [← Multiset.prod_coe]; rw [← Multiset.map_coe]; rw [Finset.coe_toList]

@[to_additive (attr := simp, grind =)]
/--
theorem `prod_toList` / 定理 `prod_toList`

English:
theorem prod_toList
  given: {M : Type*} [CommMonoid M] (s : Finset M)
  proof: by
  simpa using! s.prod_map_toList id

中文:
定理 prod_toList
  条件: {M : 类型} [CommMonoid M] (s : Finset M)
  证明: by
  simpa using! s.prod_map_toList id

Depends on / 依赖: prod_map_toList, s.prod_map_toList
-/
theorem prod_toList {M : Type*} [CommMonoid M] (s : Finset M) :
    s.toList.prod = ∏ x in s, x := by
  simpa using! s.prod_map_toList id

end ToList

@[to_additive]
/--
theorem `_root_.Equiv.Perm.prod_comp` / 定理 `_root_.Equiv.Perm.prod_comp`

English:
theorem _root_.Equiv.Perm.prod_comp
  statement: (σ : Equiv.Perm ι) (s : Finset ι) (f : ι -> M)
  proof: by
  convert! (prod_map s σ.toEmbedding f).symm
  exact (map_perm hs).symm

@[to_additive]

中文:
定理 _root_.Equiv.Perm.prod_comp
  结论: (σ : Equiv.Perm ι) (s : Finset ι) (f : ι -> M)
  证明: by
  convert! (prod_map s σ.toEmbedding f).symm
  exact (map_perm hs).symm

@[to_additive]

Depends on / 依赖: convert, map_perm, prod_map, toEmbedding
-/
theorem _root_.Equiv.Perm.prod_comp (σ : Equiv.Perm ι) (s : Finset ι) (f : ι -> M)
    (hs : { a | σ a != a } subseteq s) : (∏ x in s, f (σ x)) = ∏ x in s, f x := by
  convert! (prod_map s σ.toEmbedding f).symm
  exact (map_perm hs).symm

@[to_additive]
/--
theorem `_root_.Equiv.Perm.prod_comp'` / 定理 `_root_.Equiv.Perm.prod_comp'`

English:
theorem _root_.Equiv.Perm.prod_comp'
  statement: (σ : Equiv.Perm ι) (s : Finset ι) (f : ι -> ι -> M)
  proof: by
  convert! σ.prod_comp s (fun x => f x (σ.symm x)) hs
  rw [Equiv.symm_apply_apply]

中文:
定理 _root_.Equiv.Perm.prod_comp'
  结论: (σ : Equiv.Perm ι) (s : Finset ι) (f : ι -> ι -> M)
  证明: by
  convert! σ.prod_comp s (fun x => f x (σ.symm x)) hs
  rw [Equiv.symm_apply_apply]

Depends on / 依赖: Equiv.symm_apply_apply, convert, prod_comp, symm_apply_apply
-/
theorem _root_.Equiv.Perm.prod_comp' (σ : Equiv.Perm ι) (s : Finset ι) (f : ι -> ι -> M)
    (hs : { a | σ a != a } subseteq s) : (∏ x in s, f (σ x) x) = ∏ x in s, f x (σ.symm x) := by
  convert! σ.prod_comp s (fun x => f x (σ.symm x)) hs
  rw [Equiv.symm_apply_apply]

end CommMonoid

end Finset

namespace Finset

section CommMonoid

variable [CommMonoid M]

section bij
variable {s : Finset ι} {t : Finset κ} {f : ι -> M} {g : κ -> M}

/-- Reorder a product.

The difference with `Finset.prod_bij'` is that the bijection is specified as a surjective injection,
rather than by an inverse function.

The difference with `Finset.prod_nbij` is that the bijection is allowed to use membership of the
domain of the product, rather than being a non-dependent function. -/
@[to_additive /-- Reorder a sum.

The difference with `Finset.sum_bij'` is that the bijection is specified as a surjective injection,
rather than by an inverse function.

The difference with `Finset.sum_nbij` is that the bijection is allowed to use membership of the
domain of the sum, rather than being a non-dependent function. -/]
/--
theorem `prod_bij` / 定理 `prod_bij`

English:
theorem prod_bij
  statement: (i : forall a in s, κ) (hi : forall a ha, i a ha in t)
  proof: congr_arg Multiset.prod (Multiset.map_eq_map_of_bij_of_nodup f g s.2 t.2 i hi i_inj i_surj h)

中文:
定理 prod_bij
  结论: (i : 对任意 a in s, κ) (hi : 对任意 a ha, i a ha in t)
  证明: congr_arg Multiset.prod (Multiset.map_eq_map_of_bij_of_nodup f g s.2 t.2 i hi i_inj i_surj h)

Depends on / 依赖: Multiset, Multiset.map_eq_map_of_bij_of_nodup, Multiset.prod, congr_arg, i_inj, i_surj, map_eq_map_of_bij_of_nodup
-/
theorem prod_bij (i : forall a in s, κ) (hi : forall a ha, i a ha in t)
    (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂)
    (i_surj : forall b in t, exists a ha, i a ha = b) (h : forall a ha, f a = g (i a ha)) :
    ∏ x in s, f x = ∏ x in t, g x :=
  congr_arg Multiset.prod (Multiset.map_eq_map_of_bij_of_nodup f g s.2 t.2 i hi i_inj i_surj h)

/-- Reorder a product.

The difference with `Finset.prod_bij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.prod_nbij'` is that the bijection and its inverse are allowed to use
membership of the domains of the products, rather than being non-dependent functions. -/
@[to_additive /-- Reorder a sum.

The difference with `Finset.sum_bij` is that the bijection is specified with an inverse, rather than
as a surjective injection.

The difference with `Finset.sum_nbij'` is that the bijection and its inverse are allowed to use
membership of the domains of the sums, rather than being non-dependent functions. -/]
/--
theorem `prod_bij'` / 定理 `prod_bij'`

English:
theorem prod_bij'
  statement: (i : forall a in s, κ) (j : forall a in t, ι) (hi : forall a ha, i a ha in t)
  proof: by
  refine prod_bij i hi (fun a1 h1 a2 h2 eq => ?_) (fun b hb => ⟨_, hj b hb, right_inv b hb⟩) h
  rw [← left_inv a1 h1]; rw [← left_inv a2 h2]
  simp only [eq]

中文:
定理 prod_bij'
  结论: (i : 对任意 a in s, κ) (j : 对任意 a in t, ι) (hi : 对任意 a ha, i a ha in t)
  证明: by
  refine prod_bij i hi (fun a1 h1 a2 h2 eq => ?_) (fun b hb => ⟨_, hj b hb, right_inv b hb⟩) h
  rw [← left_inv a1 h1]; rw [← left_inv a2 h2]
  simp only [eq]

Depends on / 依赖: left_inv, prod_bij, right_inv
-/
theorem prod_bij' (i : forall a in s, κ) (j : forall a in t, ι) (hi : forall a ha, i a ha in t)
    (hj : forall a ha, j a ha in s) (left_inv : forall a ha, j (i a ha) (hi a ha) = a)
    (right_inv : forall a ha, i (j a ha) (hj a ha) = a) (h : forall a ha, f a = g (i a ha)) :
    ∏ x in s, f x = ∏ x in t, g x := by
  refine prod_bij i hi (fun a1 h1 a2 h2 eq => ?_) (fun b hb => ⟨_, hj b hb, right_inv b hb⟩) h
  rw [← left_inv a1 h1]; rw [← left_inv a2 h2]
  simp only [eq]

/-- Reorder a product.

The difference with `Finset.prod_nbij'` is that the bijection is specified as a surjective
injection, rather than by an inverse function.

The difference with `Finset.prod_bij` is that the bijection is a non-dependent function, rather than
being allowed to use membership of the domain of the product. -/
@[to_additive /-- Reorder a sum.

The difference with `Finset.sum_nbij'` is that the bijection is specified as a surjective injection,
rather than by an inverse function.

The difference with `Finset.sum_bij` is that the bijection is a non-dependent function, rather than
being allowed to use membership of the domain of the sum. -/]
/--
lemma `prod_nbij` / 引理 `prod_nbij`

English:
lemma prod_nbij
  statement: (i : ι -> κ) (hi : forall a in s, i a in t) (i_inj : (s : Set ι).InjOn i)
  proof: prod_bij (fun a _ => i a) hi i_inj (by simpa using! i_surj) h

中文:
引理 prod_nbij
  结论: (i : ι -> κ) (hi : 对任意 a in s, i a in t) (i_inj : (s : Set ι).InjOn i)
  证明: prod_bij (fun a _ => i a) hi i_inj (by simpa using! i_surj) h

Depends on / 依赖: i_inj, i_surj, prod_bij
-/
lemma prod_nbij (i : ι -> κ) (hi : forall a in s, i a in t) (i_inj : (s : Set ι).InjOn i)
    (i_surj : (s : Set ι).SurjOn i t) (h : forall a in s, f a = g (i a)) :
    ∏ x in s, f x = ∏ x in t, g x :=
  prod_bij (fun a _ => i a) hi i_inj (by simpa using! i_surj) h

/-- Reorder a product.

The difference with `Finset.prod_nbij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.prod_bij'` is that the bijection and its inverse are non-dependent
functions, rather than being allowed to use membership of the domains of the products.

The difference with `Finset.prod_equiv` is that bijectivity is only required to hold on the domains
of the products, rather than on the entire types.
-/
@[to_additive /-- Reorder a sum.

The difference with `Finset.sum_nbij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.sum_bij'` is that the bijection and its inverse are non-dependent
functions, rather than being allowed to use membership of the domains of the sums.

The difference with `Finset.sum_equiv` is that bijectivity is only required to hold on the domains
of the sums, rather than on the entire types. -/]
/--
lemma `prod_nbij'` / 引理 `prod_nbij'`

English:
lemma prod_nbij'
  statement: (i : ι -> κ) (j : κ -> ι) (hi : forall a in s, i a in t) (hj : forall a in t, j a in s)
  proof: prod_bij' (fun a _ => i a) (fun b _ => j b) hi hj left_inv right_inv h

中文:
引理 prod_nbij'
  结论: (i : ι -> κ) (j : κ -> ι) (hi : 对任意 a in s, i a in t) (hj : 对任意 a in t, j a in s)
  证明: prod_bij' (fun a _ => i a) (fun b _ => j b) hi hj left_inv right_inv h

Depends on / 依赖: left_inv, prod_bij, right_inv
-/
lemma prod_nbij' (i : ι -> κ) (j : κ -> ι) (hi : forall a in s, i a in t) (hj : forall a in t, j a in s)
    (left_inv : forall a in s, j (i a) = a) (right_inv : forall a in t, i (j a) = a)
    (h : forall a in s, f a = g (i a)) : ∏ x in s, f x = ∏ x in t, g x :=
  prod_bij' (fun a _ => i a) (fun b _ => j b) hi hj left_inv right_inv h

/-- Specialization of `Finset.prod_nbij'` that automatically fills in most arguments.

See `Fintype.prod_equiv` for the version where `s` and `t` are `univ`. -/
@[to_additive /-- Specialization of `Finset.sum_nbij'` that automatically fills in most arguments.

See `Fintype.sum_equiv` for the version where `s` and `t` are `univ`. -/]
/--
lemma `prod_equiv` / 引理 `prod_equiv`

English:
lemma prod_equiv
  given: (e : ι ≃ κ) (hst : forall i, i in s ↔ e i in t) (hfg : forall i in s, f i = g (e i))
  proof: by refine prod_nbij' e e.symm ?_ ?_ ?_ ?_ hfg <;> simp [hst]

中文:
引理 prod_equiv
  条件: (e : ι ≃ κ) (hst : 对任意 i, i in s ↔ e i in t) (hfg : 对任意 i in s, f i = g (e i))
  证明: by refine prod_nbij' e e.symm ?_ ?_ ?_ ?_ hfg <;> simp [hst]

Depends on / 依赖: e.symm, prod_nbij
-/
lemma prod_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i in t) (hfg : forall i in s, f i = g (e i)) :
    ∏ i in s, f i = ∏ i in t, g i := by refine prod_nbij' e e.symm ?_ ?_ ?_ ?_ hfg <;> simp [hst]

/-- Specialization of `Finset.prod_bij` that automatically fills in most arguments.

See `Fintype.prod_bijective` for the version where `s` and `t` are `univ`. -/
@[to_additive /-- Specialization of `Finset.sum_bij` that automatically fills in most arguments.

See `Fintype.sum_bijective` for the version where `s` and `t` are `univ`. -/]
/--
lemma `prod_bijective` / 引理 `prod_bijective`

English:
lemma prod_bijective
  statement: (e : ι -> κ) (he : e.Bijective) (hst : forall i, i in s ↔ e i in t)
  proof: prod_equiv (.ofBijective e he) hst hfg

中文:
引理 prod_bijective
  结论: (e : ι -> κ) (he : e.Bijective) (hst : 对任意 i, i in s ↔ e i in t)
  证明: prod_equiv (.ofBijective e he) hst hfg

Depends on / 依赖: ofBijective, prod_equiv
-/
lemma prod_bijective (e : ι -> κ) (he : e.Bijective) (hst : forall i, i in s ↔ e i in t)
    (hfg : forall i in s, f i = g (e i)) :
    ∏ i in s, f i = ∏ i in t, g i := prod_equiv (.ofBijective e he) hst hfg

end bij

@[to_additive]
/--
theorem `prod_hom_rel` / 定理 `prod_hom_rel`

English:
theorem prod_hom_rel
  statement: [CommMonoid N] {r : M -> N -> Prop} {f : ι -> M} {g : ι -> N} {s : Finset ι}
  proof: by
  delta Finset.prod
  apply Multiset.prod_hom_rel <;> assumption

中文:
定理 prod_hom_rel
  结论: [CommMonoid N] {r : M -> N -> 命题} {f : ι -> M} {g : ι -> N} {s : Finset ι}
  证明: by
  delta Finset.prod
  apply Multiset.prod_hom_rel <;> assumption

Depends on / 依赖: Finset, Finset.prod, Multiset, Multiset.prod_hom_rel, prod_hom_rel
-/
theorem prod_hom_rel [CommMonoid N] {r : M -> N -> Prop} {f : ι -> M} {g : ι -> N} {s : Finset ι}
    (h₁ : r 1 1) (h₂ : forall a b c, r b c -> r (f a * b) (g a * c)) :
    r (∏ x in s, f x) (∏ x in s, g x) := by
  delta Finset.prod
  apply Multiset.prod_hom_rel <;> assumption

variable (f s)

@[to_additive]
/--
theorem `prod_coe_sort_eq_attach` / 定理 `prod_coe_sort_eq_attach`

English:
theorem prod_coe_sort_eq_attach
  given: (f : s -> M)
  statement: ∏ i : s, f i = ∏ i in s.attach, f i
  proof: rfl

中文:
定理 prod_coe_sort_eq_attach
  条件: (f : s -> M)
  结论: ∏ i : s, f i = ∏ i in s.attach, f i
  证明: rfl
-/
theorem prod_coe_sort_eq_attach (f : s -> M) : ∏ i : s, f i = ∏ i in s.attach, f i :=
  rfl

variable {f s}

@[to_additive]
/--
theorem `prod_ite_index` / 定理 `prod_ite_index`

English:
theorem prod_ite_index
  given: (p : Prop) [Decidable p] (s t : Finset ι) (f : ι -> M)
  proof: apply_ite (fun s => ∏ x in s, f x) _ _ _

@[to_additive (attr := simp)]

中文:
定理 prod_ite_index
  条件: (p : 命题) [Decidable p] (s t : Finset ι) (f : ι -> M)
  证明: apply_ite (fun s => ∏ x in s, f x) _ _ _

@[to_additive (attr := simp)]

Depends on / 依赖: apply_ite
-/
theorem prod_ite_index (p : Prop) [Decidable p] (s t : Finset ι) (f : ι -> M) :
    ∏ x in if p then s else t, f x = if p then ∏ x in s, f x else ∏ x in t, f x :=
  apply_ite (fun s => ∏ x in s, f x) _ _ _

@[to_additive (attr := simp)]
/--
theorem `prod_ite_irrel` / 定理 `prod_ite_irrel`

English:
theorem prod_ite_irrel
  given: (p : Prop) [Decidable p] (s : Finset ι) (f g : ι -> M)
  proof: by
  split_ifs with h <;> rfl

@[to_additive (attr := simp)]

中文:
定理 prod_ite_irrel
  条件: (p : 命题) [Decidable p] (s : Finset ι) (f g : ι -> M)
  证明: by
  split_ifs with h <;> rfl

@[to_additive (attr := simp)]

Depends on / 依赖: split_ifs
-/
theorem prod_ite_irrel (p : Prop) [Decidable p] (s : Finset ι) (f g : ι -> M) :
    ∏ x in s, (if p then f x else g x) = if p then ∏ x in s, f x else ∏ x in s, g x := by
  split_ifs with h <;> rfl

@[to_additive (attr := simp)]
/--
theorem `prod_dite_irrel` / 定理 `prod_dite_irrel`

English:
theorem prod_dite_irrel
  given: (p : Prop) [Decidable p] (s : Finset ι) (f : p -> ι -> M) (g : ¬p -> ι -> M)
  proof: by
  split_ifs with h <;> rfl

@[to_additive]

中文:
定理 prod_dite_irrel
  条件: (p : 命题) [Decidable p] (s : Finset ι) (f : p -> ι -> M) (g : ¬p -> ι -> M)
  证明: by
  split_ifs with h <;> rfl

@[to_additive]

Depends on / 依赖: split_ifs
-/
theorem prod_dite_irrel (p : Prop) [Decidable p] (s : Finset ι) (f : p -> ι -> M) (g : ¬p -> ι -> M) :
    ∏ x in s, (if h : p then f h x else g h x) =
      if h : p then ∏ x in s, f h x else ∏ x in s, g h x := by
  split_ifs with h <;> rfl

@[to_additive]
/--
theorem `ite_prod_one` / 定理 `ite_prod_one`

English:
theorem ite_prod_one
  given: (p : Prop) [Decidable p] (s : Finset ι) (f : ι -> M)
  proof: by
  simp only [prod_ite_irrel, prod_const_one]

@[to_additive]

中文:
定理 ite_prod_one
  条件: (p : 命题) [Decidable p] (s : Finset ι) (f : ι -> M)
  证明: by
  simp only [prod_ite_irrel, prod_const_one]

@[to_additive]

Depends on / 依赖: prod_const_one, prod_ite_irrel
-/
theorem ite_prod_one (p : Prop) [Decidable p] (s : Finset ι) (f : ι -> M) :
    (if p then (∏ x in s, f x) else 1) = ∏ x in s, if p then f x else 1 := by
  simp only [prod_ite_irrel, prod_const_one]

@[to_additive]
/--
theorem `ite_one_prod` / 定理 `ite_one_prod`

English:
theorem ite_one_prod
  given: (p : Prop) [Decidable p] (s : Finset ι) (f : ι -> M)
  proof: by
  simp only [prod_ite_irrel, prod_const_one]

@[to_additive]

中文:
定理 ite_one_prod
  条件: (p : 命题) [Decidable p] (s : Finset ι) (f : ι -> M)
  证明: by
  simp only [prod_ite_irrel, prod_const_one]

@[to_additive]

Depends on / 依赖: prod_const_one, prod_ite_irrel
-/
theorem ite_one_prod (p : Prop) [Decidable p] (s : Finset ι) (f : ι -> M) :
    (if p then 1 else (∏ x in s, f x)) = ∏ x in s, if p then 1 else f x := by
  simp only [prod_ite_irrel, prod_const_one]

@[to_additive]
/--
theorem `nonempty_of_prod_ne_one` / 定理 `nonempty_of_prod_ne_one`

English:
theorem nonempty_of_prod_ne_one
  given: (h : ∏ x in s, f x != 1)
  statement: s.Nonempty
  proof: s.eq_empty_or_nonempty.elim (fun H => False.elim <| h <| H.symm ▸ prod_empty) id

@[to_additive]

中文:
定理 nonempty_of_prod_ne_one
  条件: (h : ∏ x in s, f x != 1)
  结论: s.Nonempty
  证明: s.eq_empty_or_nonempty.elim (fun H => False.elim <| h <| H.symm ▸ prod_empty) id

@[to_additive]

Depends on / 依赖: False.elim, H.symm, eq_empty_or_nonempty, prod_empty, s.eq_empty_or_nonempty.elim
-/
theorem nonempty_of_prod_ne_one (h : ∏ x in s, f x != 1) : s.Nonempty :=
  s.eq_empty_or_nonempty.elim (fun H => False.elim <| h <| H.symm ▸ prod_empty) id

@[to_additive]
/--
theorem `prod_range_zero` / 定理 `prod_range_zero`

English:
theorem prod_range_zero
  given: (f : Nat -> M)
  statement: ∏ k in range 0, f k = 1
  proof: by rw [range_zero, prod_empty]

中文:
定理 prod_range_zero
  条件: (f : 自然数 -> M)
  结论: ∏ k in range 0, f k = 1
  证明: by rw [range_zero, prod_empty]

Depends on / 依赖: prod_empty, range_zero
-/
theorem prod_range_zero (f : Nat -> M) : ∏ k in range 0, f k = 1 := by rw [range_zero, prod_empty]

open List

/--
theorem `sum_filter_count_eq_countP` / 定理 `sum_filter_count_eq_countP`

English:
theorem sum_filter_count_eq_countP
  given: [DecidableEq ι] (p : ι -> Prop) [DecidablePred p] (l : List ι)
  proof: by
  simp [Finset.sum, sum_map_count_dedup_filter_eq_countP p l]

中文:
定理 sum_filter_count_eq_countP
  条件: [DecidableEq ι] (p : ι -> 命题) [DecidablePred p] (l : List ι)
  证明: by
  simp [Finset.sum, sum_map_count_dedup_filter_eq_countP p l]

Depends on / 依赖: Finset, Finset.sum, sum_map_count_dedup_filter_eq_countP
-/
theorem sum_filter_count_eq_countP [DecidableEq ι] (p : ι -> Prop) [DecidablePred p] (l : List ι) :
    ∑ x in l.toFinset with p x, l.count x = l.countP p := by
  simp [Finset.sum, sum_map_count_dedup_filter_eq_countP p l]

open Multiset


@[to_additive]
/--
theorem `prod_mem_multiset` / 定理 `prod_mem_multiset`

English:
theorem prod_mem_multiset
  statement: [DecidableEq ι] (m : Multiset ι) (f : { x // x in m } -> M) (g : ι -> M)
  proof: by
  refine prod_bij' (fun x _ => x) (fun x hx => ⟨x, Multiset.mem_toFinset.1 hx⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp [hfg]

中文:
定理 prod_mem_multiset
  结论: [DecidableEq ι] (m : Multiset ι) (f : { x // x in m } -> M) (g : ι -> M)
  证明: by
  refine prod_bij' (fun x _ => x) (fun x hx => ⟨x, Multiset.mem_toFinset.1 hx⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp [hfg]

Depends on / 依赖: Multiset, Multiset.mem_toFinset, mem_toFinset, prod_bij
-/
theorem prod_mem_multiset [DecidableEq ι] (m : Multiset ι) (f : { x // x in m } -> M) (g : ι -> M)
    (hfg : forall x, f x = g x) : ∏ x : { x // x in m }, f x = ∏ x in m.toFinset, g x := by
  refine prod_bij' (fun x _ => x) (fun x hx => ⟨x, Multiset.mem_toFinset.1 hx⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp [hfg]

/-- To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors. -/
@[to_additive /-- To prove a property of a sum, it suffices to prove that
the property is additive and holds on summands. -/]
/--
theorem `prod_induction` / 定理 `prod_induction`

English:
theorem prod_induction
  statement: {M : Type*} [CommMonoid M] (f : ι -> M) (p : M -> Prop)
  proof: Multiset.prod_induction _ _ hom unit (Multiset.forall_mem_map_iff.mpr base)

中文:
定理 prod_induction
  结论: {M : 类型} [CommMonoid M] (f : ι -> M) (p : M -> 命题)
  证明: Multiset.prod_induction _ _ hom unit (Multiset.forall_mem_map_iff.mpr base)

Depends on / 依赖: Multiset, Multiset.forall_mem_map_iff.mpr, Multiset.prod_induction, forall_mem_map_iff, prod_induction
-/
theorem prod_induction {M : Type*} [CommMonoid M] (f : ι -> M) (p : M -> Prop)
    (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (base : forall x in s, p <| f x) :
p ∏ x in s, f x :=
  Multiset.prod_induction _ _ hom unit (Multiset.forall_mem_map_iff.mpr base)

/-- To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors. -/
@[to_additive /-- To prove a property of a sum, it suffices to prove that
the property is additive and holds on summands. -/]
/--
theorem `prod_induction_nonempty` / 定理 `prod_induction_nonempty`

English:
theorem prod_induction_nonempty
  statement: {M : Type*} [CommMonoid M] (f : ι -> M) (p : M -> Prop)
  proof: Multiset.prod_induction_nonempty p hom (by simp [nonempty_iff_ne_empty.mp nonempty])
    (Multiset.forall_mem_map_iff.mpr base)

@[to_additive]

中文:
定理 prod_induction_nonempty
  结论: {M : 类型} [CommMonoid M] (f : ι -> M) (p : M -> 命题)
  证明: Multiset.prod_induction_nonempty p hom (by simp [nonempty_iff_ne_empty.mp nonempty])
    (Multiset.forall_mem_map_iff.mpr base)

@[to_additive]

Depends on / 依赖: Multiset, Multiset.forall_mem_map_iff.mpr, Multiset.prod_induction_nonempty, forall_mem_map_iff, nonempty, nonempty_iff_ne_empty, nonempty_iff_ne_empty.mp, prod_induction_nonempty
-/
theorem prod_induction_nonempty {M : Type*} [CommMonoid M] (f : ι -> M) (p : M -> Prop)
    (hom : forall a b, p a -> p b -> p (a * b)) (nonempty : s.Nonempty) (base : forall x in s, p <| f x) :
p ∏ x in s, f x :=
  Multiset.prod_induction_nonempty p hom (by simp [nonempty_iff_ne_empty.mp nonempty])
    (Multiset.forall_mem_map_iff.mpr base)

@[to_additive]
/--
theorem `prod_pow` / 定理 `prod_pow`

English:
theorem prod_pow
  given: (s : Finset ι) (n : Nat) (f : ι -> M)
  statement: ∏ x in s, f x ^ n = (∏ x in s, f x) ^ n
  proof: Multiset.prod_map_pow

中文:
定理 prod_pow
  条件: (s : Finset ι) (n : 自然数) (f : ι -> M)
  结论: ∏ x in s, f x ^ n = (∏ x in s, f x) ^ n
  证明: Multiset.prod_map_pow

Depends on / 依赖: Multiset, Multiset.prod_map_pow, prod_map_pow
-/
theorem prod_pow (s : Finset ι) (n : Nat) (f : ι -> M) : ∏ x in s, f x ^ n = (∏ x in s, f x) ^ n :=
  Multiset.prod_map_pow

/--
theorem `prod_dvd_prod_of_subset` / 定理 `prod_dvd_prod_of_subset`

English:
theorem prod_dvd_prod_of_subset
  statement: {ι M : Type*} [CommMonoid M] (s t : Finset ι) (f : ι -> M)
  proof: Multiset.prod_dvd_prod_of_le Multiset.map_le_map by simpa

中文:
定理 prod_dvd_prod_of_subset
  结论: {ι M : 类型} [CommMonoid M] (s t : Finset ι) (f : ι -> M)
  证明: Multiset.prod_dvd_prod_of_le Multiset.map_le_map by simpa

Depends on / 依赖: Multiset, Multiset.map_le_map, Multiset.prod_dvd_prod_of_le, map_le_map, prod_dvd_prod_of_le
-/
theorem prod_dvd_prod_of_subset {ι M : Type*} [CommMonoid M] (s t : Finset ι) (f : ι -> M)
    (h : s subseteq t) : (∏ i in s, f i) ∣ ∏ i in t, f i :=
Multiset.prod_dvd_prod_of_le Multiset.map_le_map by simpa

end CommMonoid

section MulOpposite
variable [AddCommMonoid M] (s : Finset ι)

open MulOpposite

/--
lemma `op_sum` / 引理 `op_sum`

English:
lemma op_sum
  given: (f : ι -> M)
  statement: op (∑ x in s, f x) = ∑ x in s, op (f x)
  proof: map_sum opAddEquiv ..

中文:
引理 op_sum
  条件: (f : ι -> M)
  结论: op (∑ x in s, f x) = ∑ x in s, op (f x)
  证明: map_sum opAddEquiv ..
-/
@[simp] lemma op_sum (f : ι -> M) : op (∑ x in s, f x) = ∑ x in s, op (f x) := map_sum opAddEquiv ..

/--
lemma `unop_sum` / 引理 `unop_sum`

English:
lemma unop_sum
  given: (f : ι -> Mᵐᵒᵖ)
  statement: unop (∑ x in s, f x) = ∑ x in s, unop (f x)
  proof: map_sum opAddEquiv.symm ..

中文:
引理 unop_sum
  条件: (f : ι -> Mᵐᵒᵖ)
  结论: unop (∑ x in s, f x) = ∑ x in s, unop (f x)
  证明: map_sum opAddEquiv.symm ..
-/
@[simp] lemma unop_sum (f : ι -> Mᵐᵒᵖ) : unop (∑ x in s, f x) = ∑ x in s, unop (f x) :=
  map_sum opAddEquiv.symm ..

end MulOpposite

section AddOpposite
variable [CommMonoid M] (s : Finset ι)

open AddOpposite

/--
lemma `op_prod` / 引理 `op_prod`

English:
lemma op_prod
  given: (f : ι -> M)
  statement: op (∏ i in s, f i) = ∏ i in s, op (f i)
  proof: map_prod opMulEquiv ..

中文:
引理 op_prod
  条件: (f : ι -> M)
  结论: op (∏ i in s, f i) = ∏ i in s, op (f i)
  证明: map_prod opMulEquiv ..
-/
@[simp] lemma op_prod (f : ι -> M) : op (∏ i in s, f i) = ∏ i in s, op (f i) := map_prod opMulEquiv ..

/--
lemma `unop_prod` / 引理 `unop_prod`

English:
lemma unop_prod
  given: (f : ι -> Mᵐᵒᵖ)
  statement: unop (∏ i in s, f i) = ∏ i in s, unop (f i)
  proof: map_prod opMulEquiv.symm ..

中文:
引理 unop_prod
  条件: (f : ι -> Mᵐᵒᵖ)
  结论: unop (∏ i in s, f i) = ∏ i in s, unop (f i)
  证明: map_prod opMulEquiv.symm ..
-/
@[simp] lemma unop_prod (f : ι -> Mᵐᵒᵖ) : unop (∏ i in s, f i) = ∏ i in s, unop (f i) :=
  map_prod opMulEquiv.symm ..

end AddOpposite

section DivisionCommMonoid

variable [DivisionCommMonoid G]

@[to_additive (attr := simp)]
/--
theorem `prod_inv_distrib` / 定理 `prod_inv_distrib`

English:
theorem prod_inv_distrib
  given: (f : ι -> G)
  statement: (∏ x in s, (f x)⁻¹) = (∏ x in s, f x)⁻¹
  proof: Multiset.prod_map_inv

@[to_additive (attr := simp)]

中文:
定理 prod_inv_distrib
  条件: (f : ι -> G)
  结论: (∏ x in s, (f x)⁻¹) = (∏ x in s, f x)⁻¹
  证明: Multiset.prod_map_inv

@[to_additive (attr := simp)]

Depends on / 依赖: Multiset, Multiset.prod_map_inv, prod_map_inv
-/
theorem prod_inv_distrib (f : ι -> G) : (∏ x in s, (f x)⁻¹) = (∏ x in s, f x)⁻¹ :=
  Multiset.prod_map_inv

@[to_additive (attr := simp)]
/--
theorem `prod_div_distrib` / 定理 `prod_div_distrib`

English:
theorem prod_div_distrib
  given: (f g : ι -> G)
  statement: ∏ x in s, f x / g x = (∏ x in s, f x) / ∏ x in s, g x
  proof: Multiset.prod_map_div

@[to_additive]

中文:
定理 prod_div_distrib
  条件: (f g : ι -> G)
  结论: ∏ x in s, f x / g x = (∏ x in s, f x) / ∏ x in s, g x
  证明: Multiset.prod_map_div

@[to_additive]

Depends on / 依赖: Multiset, Multiset.prod_map_div, prod_map_div
-/
theorem prod_div_distrib (f g : ι -> G) : ∏ x in s, f x / g x = (∏ x in s, f x) / ∏ x in s, g x :=
  Multiset.prod_map_div

@[to_additive]
/--
theorem `prod_zpow` / 定理 `prod_zpow`

English:
theorem prod_zpow
  given: (f : ι -> G) (s : Finset ι) (n : Int)
  statement: ∏ a in s, f a ^ n = (∏ a in s, f a) ^ n
  proof: Multiset.prod_map_zpow

中文:
定理 prod_zpow
  条件: (f : ι -> G) (s : Finset ι) (n : 整数)
  结论: ∏ a in s, f a ^ n = (∏ a in s, f a) ^ n
  证明: Multiset.prod_map_zpow

Depends on / 依赖: Multiset, Multiset.prod_map_zpow, prod_map_zpow
-/
theorem prod_zpow (f : ι -> G) (s : Finset ι) (n : Int) : ∏ a in s, f a ^ n = (∏ a in s, f a) ^ n :=
  Multiset.prod_map_zpow

end DivisionCommMonoid

/--
theorem `sum_nat_mod` / 定理 `sum_nat_mod`

English:
theorem sum_nat_mod
  given: (s : Finset ι) (n : Nat) (f : ι -> Nat)
  proof: (Multiset.sum_nat_mod _ _).trans by rw [Finset.sum, Multiset.map_map]; rfl

中文:
定理 sum_nat_mod
  条件: (s : Finset ι) (n : 自然数) (f : ι -> 自然数)
  证明: (Multiset.sum_nat_mod _ _).trans by rw [Finset.sum, Multiset.map_map]; rfl

Depends on / 依赖: Finset, Finset.sum, Multiset, Multiset.map_map, Multiset.sum_nat_mod, map_map, sum_nat_mod
-/
theorem sum_nat_mod (s : Finset ι) (n : Nat) (f : ι -> Nat) :
    (∑ i in s, f i) % n = (∑ i in s, f i % n) % n :=
(Multiset.sum_nat_mod _ _).trans by rw [Finset.sum, Multiset.map_map]; rfl

/--
theorem `prod_nat_mod` / 定理 `prod_nat_mod`

English:
theorem prod_nat_mod
  given: (s : Finset ι) (n : Nat) (f : ι -> Nat)
  proof: (Multiset.prod_nat_mod _ _).trans by rw [Finset.prod, Multiset.map_map]; rfl

中文:
定理 prod_nat_mod
  条件: (s : Finset ι) (n : 自然数) (f : ι -> 自然数)
  证明: (Multiset.prod_nat_mod _ _).trans by rw [Finset.prod, Multiset.map_map]; rfl

Depends on / 依赖: Finset, Finset.prod, Multiset, Multiset.map_map, Multiset.prod_nat_mod, map_map, prod_nat_mod
-/
theorem prod_nat_mod (s : Finset ι) (n : Nat) (f : ι -> Nat) :
    (∏ i in s, f i) % n = (∏ i in s, f i % n) % n :=
(Multiset.prod_nat_mod _ _).trans by rw [Finset.prod, Multiset.map_map]; rfl

/--
theorem `sum_int_mod` / 定理 `sum_int_mod`

English:
theorem sum_int_mod
  given: (s : Finset ι) (n : Int) (f : ι -> Int)
  proof: (Multiset.sum_int_mod _ _).trans by rw [Finset.sum, Multiset.map_map]; rfl

中文:
定理 sum_int_mod
  条件: (s : Finset ι) (n : 整数) (f : ι -> 整数)
  证明: (Multiset.sum_int_mod _ _).trans by rw [Finset.sum, Multiset.map_map]; rfl

Depends on / 依赖: Finset, Finset.sum, Multiset, Multiset.map_map, Multiset.sum_int_mod, map_map, sum_int_mod
-/
theorem sum_int_mod (s : Finset ι) (n : Int) (f : ι -> Int) :
    (∑ i in s, f i) % n = (∑ i in s, f i % n) % n :=
(Multiset.sum_int_mod _ _).trans by rw [Finset.sum, Multiset.map_map]; rfl

/--
theorem `prod_int_mod` / 定理 `prod_int_mod`

English:
theorem prod_int_mod
  given: (s : Finset ι) (n : Int) (f : ι -> Int)
  proof: (Multiset.prod_int_mod _ _).trans by rw [Finset.prod, Multiset.map_map]; rfl

中文:
定理 prod_int_mod
  条件: (s : Finset ι) (n : 整数) (f : ι -> 整数)
  证明: (Multiset.prod_int_mod _ _).trans by rw [Finset.prod, Multiset.map_map]; rfl

Depends on / 依赖: Finset, Finset.prod, Multiset, Multiset.map_map, Multiset.prod_int_mod, map_map, prod_int_mod
-/
theorem prod_int_mod (s : Finset ι) (n : Int) (f : ι -> Int) :
    (∏ i in s, f i) % n = (∏ i in s, f i % n) % n :=
(Multiset.prod_int_mod _ _).trans by rw [Finset.prod, Multiset.map_map]; rfl

end Finset

namespace Fintype
variable [Fintype ι] [Fintype κ]

open Finset

section CommMonoid
variable [CommMonoid M]

/-- `Fintype.prod_bijective` is a variant of `Finset.prod_bij` that accepts `Function.Bijective`.

See `Function.Bijective.prod_comp` for a version without `h`. -/
@[to_additive /-- `Fintype.sum_bijective` is a variant of `Finset.sum_bij` that accepts
`Function.Bijective`.

See `Function.Bijective.sum_comp` for a version without `h`. -/]
/--
lemma `prod_bijective` / 引理 `prod_bijective`

English:
lemma prod_bijective
  statement: (e : ι -> κ) (he : e.Bijective) (f : ι -> M) (g : κ -> M)
  proof: prod_equiv (.ofBijective e he) (by simp) (by simp [h])

@[to_additive] alias _root_.Function.Bijective.finsetProd := prod_bijective

@[deprecated (since := "2026-04-08")]
alias _root_.Function.Bijective.finset_sum := _root_.Function.Bijective.finsetSum

@[to_additive existing, deprecated (since := "

中文:
引理 prod_bijective
  结论: (e : ι -> κ) (he : e.Bijective) (f : ι -> M) (g : κ -> M)
  证明: prod_equiv (.ofBijective e he) (by simp) (by simp [h])

@[to_additive] alias _root_.Function.Bijective.finsetProd := prod_bijective

@[deprecated (since := "2026-04-08")]
alias _root_.Function.Bijective.finset_sum := _root_.Function.Bijective.finsetSum

@[to_additive existing, deprecated (since := "

Depends on / 依赖: ofBijective, prod_equiv
-/
lemma prod_bijective (e : ι -> κ) (he : e.Bijective) (f : ι -> M) (g : κ -> M)
    (h : forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x :=
  prod_equiv (.ofBijective e he) (by simp) (by simp [h])

@[to_additive] alias _root_.Function.Bijective.finsetProd := prod_bijective

@[deprecated (since := "2026-04-08")]
alias _root_.Function.Bijective.finset_sum := _root_.Function.Bijective.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias _root_.Function.Bijective.finset_prod := _root_.Function.Bijective.finsetProd

/-- `Fintype.prod_equiv` is a specialization of `Finset.prod_bij` that
automatically fills in most arguments.

See `Equiv.prod_comp` for a version without `h`.
-/
@[to_additive /-- `Fintype.sum_equiv` is a specialization of `Finset.sum_bij` that
automatically fills in most arguments.

See `Equiv.sum_comp` for a version without `h`. -/]
/--
lemma `prod_equiv` / 引理 `prod_equiv`

English:
lemma prod_equiv
  given: (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h : forall x, f x = g (e x))
  proof: prod_bijective _ e.bijective _ _ h

@[to_additive]

中文:
引理 prod_equiv
  条件: (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h : 对任意 x, f x = g (e x))
  证明: prod_bijective _ e.bijective _ _ h

@[to_additive]

Depends on / 依赖: bijective, e.bijective, prod_bijective
-/
lemma prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h : forall x, f x = g (e x)) :
    ∏ x, f x = ∏ x, g x := prod_bijective _ e.bijective _ _ h

@[to_additive]
/--
lemma `_root_.Function.Bijective.prod_comp` / 引理 `_root_.Function.Bijective.prod_comp`

English:
lemma _root_.Function.Bijective.prod_comp
  given: {e : ι -> κ} (he : e.Bijective) (g : κ -> M)
  proof: prod_bijective _ he _ _ fun _ => rfl

@[to_additive]

中文:
引理 _root_.Function.Bijective.prod_comp
  条件: {e : ι -> κ} (he : e.Bijective) (g : κ -> M)
  证明: prod_bijective _ he _ _ fun _ => rfl

@[to_additive]

Depends on / 依赖: prod_bijective
-/
lemma _root_.Function.Bijective.prod_comp {e : ι -> κ} (he : e.Bijective) (g : κ -> M) :
    ∏ i, g (e i) = ∏ i, g i := prod_bijective _ he _ _ fun _ => rfl

@[to_additive]
/--
lemma `_root_.Equiv.prod_comp` / 引理 `_root_.Equiv.prod_comp`

English:
lemma _root_.Equiv.prod_comp
  given: (e : ι ≃ κ) (g : κ -> M)
  statement: ∏ i, g (e i) = ∏ i, g i
  proof: prod_equiv e _ _ fun _ => rfl

@[to_additive]

中文:
引理 _root_.Equiv.prod_comp
  条件: (e : ι ≃ κ) (g : κ -> M)
  结论: ∏ i, g (e i) = ∏ i, g i
  证明: prod_equiv e _ _ fun _ => rfl

@[to_additive]

Depends on / 依赖: prod_equiv
-/
lemma _root_.Equiv.prod_comp (e : ι ≃ κ) (g : κ -> M) : ∏ i, g (e i) = ∏ i, g i :=
  prod_equiv e _ _ fun _ => rfl

@[to_additive]
/--
theorem `prod_empty` / 定理 `prod_empty`

English:
theorem prod_empty
  given: [IsEmpty ι] (f : ι -> M)
  statement: ∏ x : ι, f x = 1
  proof: prod_of_isEmpty _

中文:
定理 prod_empty
  条件: [IsEmpty ι] (f : ι -> M)
  结论: ∏ x : ι, f x = 1
  证明: prod_of_isEmpty _

Depends on / 依赖: prod_of_isEmpty
-/
theorem prod_empty [IsEmpty ι] (f : ι -> M) : ∏ x : ι, f x = 1 := prod_of_isEmpty _

end CommMonoid
end Fintype

namespace Finset
variable [CommMonoid M]

@[to_additive (attr := simp)]
/--
lemma `prod_attach_univ` / 引理 `prod_attach_univ`

English:
lemma prod_attach_univ
  given: [Fintype ι] (f : {i // i in @univ ι _} -> M)
  proof: Fintype.prod_equiv (Equiv.subtypeUnivEquiv mem_univ) _ _ by simp

@[to_additive]

中文:
引理 prod_attach_univ
  条件: [Fintype ι] (f : {i // i in @univ ι _} -> M)
  证明: Fintype.prod_equiv (Equiv.subtypeUnivEquiv mem_univ) _ _ by simp

@[to_additive]

Depends on / 依赖: Equiv.subtypeUnivEquiv, Fintype, Fintype.prod_equiv, mem_univ, prod_equiv, subtypeUnivEquiv
-/
lemma prod_attach_univ [Fintype ι] (f : {i // i in @univ ι _} -> M) :
    ∏ i in univ.attach, f i = ∏ i, f ⟨i, mem_univ _⟩ :=
Fintype.prod_equiv (Equiv.subtypeUnivEquiv mem_univ) _ _ by simp

@[to_additive]
/--
theorem `prod_erase_attach` / 定理 `prod_erase_attach`

English:
theorem prod_erase_attach
  given: [DecidableEq ι] {s : Finset ι} (f : ι -> M) (i : ↑s)
  proof: by
  rw [← Function.Embedding.coe_subtype]; rw [← prod_map]
  simp [attach_map_val]

中文:
定理 prod_erase_attach
  条件: [DecidableEq ι] {s : Finset ι} (f : ι -> M) (i : ↑s)
  证明: by
  rw [← Function.Embedding.coe_subtype]; rw [← prod_map]
  simp [attach_map_val]

Depends on / 依赖: Embedding, Function, Function.Embedding.coe_subtype, attach_map_val, coe_subtype, prod_map
-/
theorem prod_erase_attach [DecidableEq ι] {s : Finset ι} (f : ι -> M) (i : ↑s) :
    ∏ j in s.attach.erase i, f ↑j = ∏ j in s.erase ↑i, f j := by
  rw [← Function.Embedding.coe_subtype]; rw [← prod_map]
  simp [attach_map_val]

end Finset

namespace Multiset

@[simp]
/--
lemma `card_sum` / 引理 `card_sum`

English:
lemma card_sum
  given: (s : Finset ι) (f : ι -> Multiset α)
  statement: card (∑ i in s, f i) = ∑ i in s, card (f i)
  proof: map_sum cardHom ..

中文:
引理 card_sum
  条件: (s : Finset ι) (f : ι -> Multiset α)
  结论: card (∑ i in s, f i) = ∑ i in s, card (f i)
  证明: map_sum cardHom ..

Depends on / 依赖: cardHom, map_sum
-/
lemma card_sum (s : Finset ι) (f : ι -> Multiset α) : card (∑ i in s, f i) = ∑ i in s, card (f i) :=
  map_sum cardHom ..

/--
theorem `disjoint_list_sum_left` / 定理 `disjoint_list_sum_left`

English:
theorem disjoint_list_sum_left
  given: {a : Multiset α} {l : List (Multiset α)}
  proof: by
  induction l with
  | nil =>
    simp only [zero_disjoint, List.not_mem_nil, IsEmpty.forall_iff, forall_const, List.sum_nil]
  | cons b bs ih =>
    simp [ih]

中文:
定理 disjoint_list_sum_left
  条件: {a : Multiset α} {l : List (Multiset α)}
  证明: by
  induction l with
  | nil =>
    simp only [zero_disjoint, List.not_mem_nil, IsEmpty.forall_iff, forall_const, List.sum_nil]
  | cons b bs ih =>
    simp [ih]

Depends on / 依赖: IsEmpty, IsEmpty.forall_iff, List.not_mem_nil, List.sum_nil, forall_const, forall_iff, not_mem_nil, sum_nil, zero_disjoint
-/
theorem disjoint_list_sum_left {a : Multiset α} {l : List (Multiset α)} :
    Disjoint l.sum a ↔ forall b in l, Disjoint b a := by
  induction l with
  | nil =>
    simp only [zero_disjoint, List.not_mem_nil, IsEmpty.forall_iff, forall_const, List.sum_nil]
  | cons b bs ih =>
    simp [ih]

/--
theorem `disjoint_list_sum_right` / 定理 `disjoint_list_sum_right`

English:
theorem disjoint_list_sum_right
  given: {a : Multiset α} {l : List (Multiset α)}
  proof: by
  simpa only [disjoint_comm (a := a)] using disjoint_list_sum_left

中文:
定理 disjoint_list_sum_right
  条件: {a : Multiset α} {l : List (Multiset α)}
  证明: by
  simpa only [disjoint_comm (a := a)] using disjoint_list_sum_left

Depends on / 依赖: disjoint_comm, disjoint_list_sum_left
-/
theorem disjoint_list_sum_right {a : Multiset α} {l : List (Multiset α)} :
    Disjoint a l.sum ↔ forall b in l, Disjoint a b := by
  simpa only [disjoint_comm (a := a)] using disjoint_list_sum_left

/--
theorem `disjoint_sum_left` / 定理 `disjoint_sum_left`

English:
theorem disjoint_sum_left
  given: {a : Multiset α} {i : Multiset (Multiset α)}
  proof: Quotient.inductionOn i fun l => by
    rw [quot_mk_to_coe]; rw [Multiset.sum_coe]
    exact disjoint_list_sum_left

中文:
定理 disjoint_sum_left
  条件: {a : Multiset α} {i : Multiset (Multiset α)}
  证明: Quotient.inductionOn i fun l => by
    rw [quot_mk_to_coe]; rw [Multiset.sum_coe]
    exact disjoint_list_sum_left

Depends on / 依赖: Multiset, Multiset.sum_coe, Quotient, Quotient.inductionOn, disjoint_list_sum_left, inductionOn, quot_mk_to_coe, sum_coe
-/
theorem disjoint_sum_left {a : Multiset α} {i : Multiset (Multiset α)} :
    Disjoint i.sum a ↔ forall b in i, Disjoint b a :=
  Quotient.inductionOn i fun l => by
    rw [quot_mk_to_coe]; rw [Multiset.sum_coe]
    exact disjoint_list_sum_left

/--
theorem `disjoint_sum_right` / 定理 `disjoint_sum_right`

English:
theorem disjoint_sum_right
  given: {a : Multiset α} {i : Multiset (Multiset α)}
  proof: by
  simpa only [disjoint_comm (a := a)] using disjoint_sum_left

中文:
定理 disjoint_sum_right
  条件: {a : Multiset α} {i : Multiset (Multiset α)}
  证明: by
  simpa only [disjoint_comm (a := a)] using disjoint_sum_left

Depends on / 依赖: disjoint_comm, disjoint_sum_left
-/
theorem disjoint_sum_right {a : Multiset α} {i : Multiset (Multiset α)} :
    Disjoint a i.sum ↔ forall b in i, Disjoint a b := by
  simpa only [disjoint_comm (a := a)] using disjoint_sum_left

/--
theorem `disjoint_finsetSum_left` / 定理 `disjoint_finsetSum_left`

English:
theorem disjoint_finsetSum_left
  given: {i : Finset ι} {f : ι -> Multiset α} {a : Multiset α}
  proof: by
  convert! @disjoint_sum_left _ a (map f i.val)
  simp

@[deprecated (since := "2026-04-08")] alias disjoint_finset_sum_left := disjoint_finsetSum_left

中文:
定理 disjoint_finsetSum_left
  条件: {i : Finset ι} {f : ι -> Multiset α} {a : Multiset α}
  证明: by
  convert! @disjoint_sum_left _ a (map f i.val)
  simp

@[deprecated (since := "2026-04-08")] alias disjoint_finset_sum_left := disjoint_finsetSum_left

Depends on / 依赖: convert, disjoint_sum_left, i.val
-/
theorem disjoint_finsetSum_left {i : Finset ι} {f : ι -> Multiset α} {a : Multiset α} :
    Disjoint (i.sum f) a ↔ forall b in i, Disjoint (f b) a := by
  convert! @disjoint_sum_left _ a (map f i.val)
  simp

@[deprecated (since := "2026-04-08")] alias disjoint_finset_sum_left := disjoint_finsetSum_left

/--
theorem `disjoint_finsetSum_right` / 定理 `disjoint_finsetSum_right`

English:
theorem disjoint_finsetSum_right
  statement: {i : Finset ι} {f : ι -> Multiset α}
  proof: by
  simpa only [disjoint_comm] using disjoint_finsetSum_left

@[deprecated (since := "2026-04-08")] alias disjoint_finset_sum_right := disjoint_finsetSum_right

中文:
定理 disjoint_finsetSum_right
  结论: {i : Finset ι} {f : ι -> Multiset α}
  证明: by
  simpa only [disjoint_comm] using disjoint_finsetSum_left

@[deprecated (since := "2026-04-08")] alias disjoint_finset_sum_right := disjoint_finsetSum_right

Depends on / 依赖: disjoint_comm, disjoint_finsetSum_left
-/
theorem disjoint_finsetSum_right {i : Finset ι} {f : ι -> Multiset α}
    {a : Multiset α} : Disjoint a (i.sum f) ↔ forall b in i, Disjoint a (f b) := by
  simpa only [disjoint_comm] using disjoint_finsetSum_left

@[deprecated (since := "2026-04-08")] alias disjoint_finset_sum_right := disjoint_finsetSum_right

variable [DecidableEq α]

/--
theorem `count_sum'` / 定理 `count_sum'`

English:
theorem count_sum'
  given: {s : Finset ι} {a : α} {f : ι -> Multiset α}
  proof: by
  dsimp only [Finset.sum]
  rw [count_sum]

中文:
定理 count_sum'
  条件: {s : Finset ι} {a : α} {f : ι -> Multiset α}
  证明: by
  dsimp only [Finset.sum]
  rw [count_sum]

Depends on / 依赖: Finset, Finset.sum, count_sum
-/
theorem count_sum' {s : Finset ι} {a : α} {f : ι -> Multiset α} :
    count a (∑ x in s, f x) = ∑ x in s, count a (f x) := by
  dsimp only [Finset.sum]
  rw [count_sum]

/--
theorem `toFinset_prod_dvd_prod` / 定理 `toFinset_prod_dvd_prod`

English:
theorem toFinset_prod_dvd_prod
  given: [DecidableEq M] [CommMonoid M] (S : Multiset M)
  proof: by
  rw [Finset.prod_eq_multiset_prod]
  refine Multiset.prod_dvd_prod_of_le ?_
  simp [Multiset.dedup_le S]

中文:
定理 toFinset_prod_dvd_prod
  条件: [DecidableEq M] [CommMonoid M] (S : Multiset M)
  证明: by
  rw [Finset.prod_eq_multiset_prod]
  refine Multiset.prod_dvd_prod_of_le ?_
  simp [Multiset.dedup_le S]

Depends on / 依赖: Finset, Finset.prod_eq_multiset_prod, Multiset, Multiset.dedup_le, Multiset.prod_dvd_prod_of_le, dedup_le, prod_dvd_prod_of_le, prod_eq_multiset_prod
-/
theorem toFinset_prod_dvd_prod [DecidableEq M] [CommMonoid M] (S : Multiset M) :
    S.toFinset.prod id ∣ S.prod := by
  rw [Finset.prod_eq_multiset_prod]
  refine Multiset.prod_dvd_prod_of_le ?_
  simp [Multiset.dedup_le S]

end Multiset

@[simp, norm_cast]
/--
theorem `Units.coe_prod` / 定理 `Units.coe_prod`

English:
theorem Units.coe_prod
  given: [CommMonoid M] (f : α -> Mˣ) (s : Finset α)
  proof: map_prod (Units.coeHom M) _ _

中文:
定理 Units.coe_prod
  条件: [CommMonoid M] (f : α -> Mˣ) (s : Finset α)
  证明: map_prod (Units.coeHom M) _ _

Depends on / 依赖: Units.coeHom, coeHom, map_prod
-/
theorem Units.coe_prod [CommMonoid M] (f : α -> Mˣ) (s : Finset α) :
    (↑(∏ i in s, f i) : M) = ∏ i in s, (f i : M) :=
  map_prod (Units.coeHom M) _ _


/-! ### `Additive`, `Multiplicative` -/


open Additive Multiplicative

section Monoid

variable [Monoid M]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ofMul_list_prod` / 定理 `ofMul_list_prod`

English:
theorem ofMul_list_prod
  given: (s : List M)
  statement: ofMul s.prod = (s.map ofMul).sum
  proof: by simp [ofMul]; rfl

中文:
定理 ofMul_list_prod
  条件: (s : List M)
  结论: ofMul s.prod = (s.map ofMul).sum
  证明: by simp [ofMul]; rfl
-/
theorem ofMul_list_prod (s : List M) : ofMul s.prod = (s.map ofMul).sum := by simp [ofMul]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toMul_list_sum` / 定理 `toMul_list_sum`

English:
theorem toMul_list_sum
  given: (s : List (Additive M))
  statement: s.sum.toMul = (s.map toMul).prod
  proof: by
  simp [toMul, ofMul]; rfl

中文:
定理 toMul_list_sum
  条件: (s : List (Additive M))
  结论: s.sum.toMul = (s.map toMul).prod
  证明: by
  simp [toMul, ofMul]; rfl
-/
theorem toMul_list_sum (s : List (Additive M)) : s.sum.toMul = (s.map toMul).prod := by
  simp [toMul, ofMul]; rfl

end Monoid

section AddMonoid

variable [AddMonoid M]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ofAdd_list_prod` / 定理 `ofAdd_list_prod`

English:
theorem ofAdd_list_prod
  given: (s : List M)
  statement: ofAdd s.sum = (s.map ofAdd).prod
  proof: by simp [ofAdd]; rfl

中文:
定理 ofAdd_list_prod
  条件: (s : List M)
  结论: ofAdd s.sum = (s.map ofAdd).prod
  证明: by simp [ofAdd]; rfl
-/
theorem ofAdd_list_prod (s : List M) : ofAdd s.sum = (s.map ofAdd).prod := by simp [ofAdd]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toAdd_list_sum` / 定理 `toAdd_list_sum`

English:
theorem toAdd_list_sum
  given: (s : List (Multiplicative M))
  statement: s.prod.toAdd = (s.map toAdd).sum
  proof: by
  simp [toAdd, ofAdd]; rfl

中文:
定理 toAdd_list_sum
  条件: (s : List (Multiplicative M))
  结论: s.prod.toAdd = (s.map toAdd).sum
  证明: by
  simp [toAdd, ofAdd]; rfl
-/
theorem toAdd_list_sum (s : List (Multiplicative M)) : s.prod.toAdd = (s.map toAdd).sum := by
  simp [toAdd, ofAdd]; rfl

end AddMonoid

section CommMonoid

variable [CommMonoid M]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ofMul_multiset_prod` / 定理 `ofMul_multiset_prod`

English:
theorem ofMul_multiset_prod
  given: (s : Multiset M)
  statement: ofMul s.prod = (s.map ofMul).sum
  proof: by
  simp [ofMul]; rfl

中文:
定理 ofMul_multiset_prod
  条件: (s : Multiset M)
  结论: ofMul s.prod = (s.map ofMul).sum
  证明: by
  simp [ofMul]; rfl
-/
theorem ofMul_multiset_prod (s : Multiset M) : ofMul s.prod = (s.map ofMul).sum := by
  simp [ofMul]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toMul_multiset_sum` / 定理 `toMul_multiset_sum`

English:
theorem toMul_multiset_sum
  given: (s : Multiset (Additive M))
  statement: s.sum.toMul = (s.map toMul).prod
  proof: by
  simp [toMul, ofMul]; rfl

@[simp]

中文:
定理 toMul_multiset_sum
  条件: (s : Multiset (Additive M))
  结论: s.sum.toMul = (s.map toMul).prod
  证明: by
  simp [toMul, ofMul]; rfl

@[simp]
-/
theorem toMul_multiset_sum (s : Multiset (Additive M)) : s.sum.toMul = (s.map toMul).prod := by
  simp [toMul, ofMul]; rfl

@[simp]
/--
theorem `ofMul_prod` / 定理 `ofMul_prod`

English:
theorem ofMul_prod
  given: (s : Finset ι) (f : ι -> M)
  statement: ofMul (∏ i in s, f i) = ∑ i in s, ofMul (f i)
  proof: rfl

@[simp]

中文:
定理 ofMul_prod
  条件: (s : Finset ι) (f : ι -> M)
  结论: ofMul (∏ i in s, f i) = ∑ i in s, ofMul (f i)
  证明: rfl

@[simp]
-/
theorem ofMul_prod (s : Finset ι) (f : ι -> M) : ofMul (∏ i in s, f i) = ∑ i in s, ofMul (f i) :=
  rfl

@[simp]
/--
theorem `toMul_sum` / 定理 `toMul_sum`

English:
theorem toMul_sum
  given: (s : Finset ι) (f : ι -> Additive M)
  proof: rfl

中文:
定理 toMul_sum
  条件: (s : Finset ι) (f : ι -> Additive M)
  证明: rfl
-/
theorem toMul_sum (s : Finset ι) (f : ι -> Additive M) :
    (∑ i in s, f i).toMul = ∏ i in s, (f i).toMul :=
  rfl

end CommMonoid

section AddCommMonoid

variable [AddCommMonoid M]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ofAdd_multiset_prod` / 定理 `ofAdd_multiset_prod`

English:
theorem ofAdd_multiset_prod
  given: (s : Multiset M)
  statement: ofAdd s.sum = (s.map ofAdd).prod
  proof: by
  simp [ofAdd]; rfl

中文:
定理 ofAdd_multiset_prod
  条件: (s : Multiset M)
  结论: ofAdd s.sum = (s.map ofAdd).prod
  证明: by
  simp [ofAdd]; rfl
-/
theorem ofAdd_multiset_prod (s : Multiset M) : ofAdd s.sum = (s.map ofAdd).prod := by
  simp [ofAdd]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toAdd_multiset_sum` / 定理 `toAdd_multiset_sum`

English:
theorem toAdd_multiset_sum
  given: (s : Multiset (Multiplicative M))
  proof: by
  simp [toAdd, ofAdd]; rfl

@[simp]

中文:
定理 toAdd_multiset_sum
  条件: (s : Multiset (Multiplicative M))
  证明: by
  simp [toAdd, ofAdd]; rfl

@[simp]
-/
theorem toAdd_multiset_sum (s : Multiset (Multiplicative M)) :
    s.prod.toAdd = (s.map toAdd).sum := by
  simp [toAdd, ofAdd]; rfl

@[simp]
/--
theorem `ofAdd_sum` / 定理 `ofAdd_sum`

English:
theorem ofAdd_sum
  given: (s : Finset ι) (f : ι -> M)
  statement: ofAdd (∑ i in s, f i) = ∏ i in s, ofAdd (f i)
  proof: rfl

@[simp]

中文:
定理 ofAdd_sum
  条件: (s : Finset ι) (f : ι -> M)
  结论: ofAdd (∑ i in s, f i) = ∏ i in s, ofAdd (f i)
  证明: rfl

@[simp]
-/
theorem ofAdd_sum (s : Finset ι) (f : ι -> M) : ofAdd (∑ i in s, f i) = ∏ i in s, ofAdd (f i) :=
  rfl

@[simp]
/--
theorem `toAdd_prod` / 定理 `toAdd_prod`

English:
theorem toAdd_prod
  given: (s : Finset ι) (f : ι -> Multiplicative M)
  proof: rfl

中文:
定理 toAdd_prod
  条件: (s : Finset ι) (f : ι -> Multiplicative M)
  证明: rfl
-/
theorem toAdd_prod (s : Finset ι) (f : ι -> Multiplicative M) :
    (∏ i in s, f i).toAdd = ∑ i in s, (f i).toAdd :=
  rfl

end AddCommMonoid
