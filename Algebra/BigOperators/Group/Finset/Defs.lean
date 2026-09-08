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
/-
**Finset.prod** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{ι : Type u_1} → {M : Type u_3} → [CommMonoid M] → Finset ι → (ι → M) → M
参数：ι → M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def prod [CommMonoid M] (s : Finset ι) (f : ι → M) : M :=
  (s.1.map f).prod

@[to_additive (attr := simp)]
/-
**Finset.prod_mk** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_mk [CommMonoid M] (s : Multiset ι) (hs : s.Nodup) (f : ι -> M) : (⟨s,
 hs⟩ : Finset ι).prod f = (s.map f).prod
参数：s : Multiset ι；hs : s.Nodup；f : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_mk [CommMonoid M] (s : Multiset ι) (hs : s.Nodup) (f : ι → M) :
    (⟨s, hs⟩ : Finset ι).prod f = (s.map f).prod :=
  rfl

@[to_additive (attr := simp)]
/-
**Finset.prod_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_val [CommMonoid M] (s : Finset M) : s.1.prod = s.prod id
参数：s : Finset M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod.eq_1`：∀ {ι : Type u_1} {M : Type u_3} [inst : CommMonoid M] 
(s : Finset ι) (f : ι → M), s.prod f = (Multiset.map f s.val).prod
· 使用定理 `Multiset.map_id`：map_id (s : Multiset α) : map id s = s
-/
theorem prod_val [CommMonoid M] (s : Finset M) : s.1.prod = s.prod id := by
  rw [Finset.prod, Multiset.map_id]

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
syntax bigOpBinders := bigOpBinderCollection <|> (ppSpace bigOpBinder)

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
        return processed |>.push (← `(⟨$a, $b⟩), ← `(Finset.Nat.antidiagonal $n))
      | _ => return processed |>.push (x, ← ``(Finset.univ))
    | `(bigOpBinder| $x : $t) => return processed |>.push (x, ← ``((Finset.univ : Finset $t)))
    | `(bigOpBinder| $x ∈ $s) => return processed |>.push (x, ← `(finset% $s))
    | `(bigOpBinder| $x ∉ $s) => return processed |>.push (x, ← `(finset% $sᶜ))
    | `(bigOpBinder| $x ≠ $n) => return processed |>.push (x, ← `(Finset.univ.erase $n))
    | `(bigOpBinder| $x < $n) => return processed |>.push (x, ← `(Finset.Iio $n))
    | `(bigOpBinder| $x ≤ $n) => return processed |>.push (x, ← `(Finset.Iic $n))
    | `(bigOpBinder| $x > $n) => return processed |>.push (x, ← `(Finset.Ioi $n))
    | `(bigOpBinder| $x ≥ $n) => return processed |>.push (x, ← `(Finset.Ici $n))
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
      `(Finset.sum $s fun $x ↦ if $hx : $p then $v else 0)
    | _, some p => `(Finset.sum (Finset.filter (fun $x ↦ $p) $s) (fun $x ↦ $v))
    | _, none => `(Finset.sum $s (fun $x ↦ $v))

macro_rules (kind := bigprod)
  | `(∏ $bs:bigOpBinders $[with $[$hx??:binderIdent :]? $p?:term]?, $v) => do
    let processed ← processBigOpBinders bs
    let x ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    -- `a` is interpreted as the filtering proposition, unless `b` exists, in which case `a` is the
    -- proof and `b` is the filtering proposition
    match hx??, p? with
    | some (some hx), some p =>
      `(Finset.prod $s fun $x ↦ if $hx : $p then $v else 1)
    | _, some p => `(Finset.prod (Finset.filter (fun $x ↦ $p) $s) (fun $x ↦ $v))
    | _, none => `(Finset.prod $s (fun $x ↦ $v))

open PrettyPrinter.Delaborator SubExpr
open scoped Batteries.ExtendedBinder

/-- The possibilities we distinguish to delaborate the finset indexing a big operator:
* `finset s` corresponds to `∑ x ∈ s, f x`
* `univ` corresponds to `∑ x, f x`
* `Iio n`/`Iic n`/`Ioi n`/`Ici n` corresponds to the intervals that are elaborated by sums.
-/
/-
**BigOperators.FinsetResult** 是 Mathlib 中的一个归纳类型，位于命名空间 `BigOperators`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The possibilities we distinguish to delaborate the finset indexing a big operato
r:
* `finset s` corresponds to `∑ x ∈ s, f x`
* `univ` corresponds to `∑ x, f x`
* `Iio n`/`Iic n`/`Ioi n`/`Ici n` corresponds to the intervals that are elaborat
ed by sums.
-/
private inductive FinsetResult where
  | finset (s : Term)
  | univ
  | Iio (n : Term)
  | Iic (n : Term)
  | Ioi (n : Term)
  | Ici (n : Term)

/-- The possibilities we distinguish to delaborate the finset indexing a big operator, including
filters.
* `{finset := s, filter = none}` represents `∑ x ∈ s, f x`;
* `{finset := s, filter = some p}` represents `∑ x ∈ s with p, f x`.
-/
/-
**BigOperators.FinsetFilterResult** 是 Mathlib 中的一个结构，位于命名空间 `BigOperators`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The possibilities we distinguish to delaborate the finset indexing a big operato
r, including
filters.
* `{finset := s, filter = none}` represents `∑ x ∈ s, f x`;
* `{finset := s, filter = some p}` represents `∑ x ∈ s with p, f x`.
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
  whenPPOption getPPNotation <| withOverApp 5 do
  let #[_, _, _, _, f] := (← getExpr).getAppArgs | failure
  guard f.isLambda
  let ppDomain ← withAppArg <| getPPOption getPPFunBinderTypes
  let (i, body) ← withAppArg <| withBindingBodyUnusedName fun i => do
    return ((⟨i⟩ : Ident), ← delab)
  let ⟨res, p⟩ ← withNaryArg 3 <| delabFinsetArg i
  let withClause? : Option (TSyntax `BigOperators.BigOpWith) ← (match p with
    | .some pp => return some (← `(BigOpWith|with $pp:term))
    | .none => return none)
  match res with
  | .finset ss => `(∏ $i:ident ∈ $ss $[$withClause?]?, $body)
  | .univ =>
    let binder ←
    if ppDomain then
      let ty ← withNaryArg 0 delab
      `(bigOpBinder| $i:ident : $ty)
    else
      `(bigOpBinder| $i:ident)
    `(∏ $binder:bigOpBinder $[$withClause?]?, $body)
  | .Iio ss => `(∏ $i:ident < $ss $[$withClause?]?, $body)
  | .Iic ss => `(∏ $i:ident ≤ $ss $[$withClause?]?, $body)
  | .Ioi ss => `(∏ $i:ident > $ss $[$withClause?]?, $body)
  | .Ici ss => `(∏ $i:ident ≥ $ss $[$withClause?]?, $body)

/-- Delaborator for `Finset.sum`. The `pp.funBinderTypes` option controls whether
to show the domain type when the sum is over `Finset.univ`. -/
@[app_delab Finset.sum] meta def delabFinsetSum : Delab :=
  whenPPOption getPPNotation <| withOverApp 5 do
  let #[_, _, _, _, f] := (← getExpr).getAppArgs | failure
  guard f.isLambda
  let ppDomain ← withAppArg <| getPPOption getPPFunBinderTypes
  let (i, body) ← withAppArg <| withBindingBodyUnusedName fun i => do
    return ((⟨i⟩ : Ident), ← delab)
  let ⟨res, p⟩ ← withNaryArg 3 <| delabFinsetArg i
  let withClause? : Option (TSyntax `BigOperators.BigOpWith) ← (match p with
    | .some pp => return some (← `(BigOpWith|with $pp:term))
    | .none => return none)
  match res with
  | .finset ss => `(∑ $i:ident ∈ $ss $[$withClause?]?, $body)
  | .univ =>
    let binder ←
    if ppDomain then
      let ty ← withNaryArg 0 delab
      `(bigOpBinder| $i:ident : $ty)
    else
      `(bigOpBinder| $i:ident)
    `(∑ $binder:bigOpBinder $[$withClause?]?, $body)
  | .Iio ss => `(∑ $i:ident < $ss $[$withClause?]?, $body)
  | .Iic ss => `(∑ $i:ident ≤ $ss $[$withClause?]?, $body)
  | .Ioi ss => `(∑ $i:ident > $ss $[$withClause?]?, $body)
  | .Ici ss => `(∑ $i:ident ≥ $ss $[$withClause?]?, $body)

end BigOperators

namespace Finset

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

@[to_additive]
/-
**Finset.prod_eq_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eq_multiset_prod [CommMonoid M] (s : Finset ι) (f : ι -> M) : ∏ x in 
s, f x = (s.1.map f).prod
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_eq_multiset_prod [CommMonoid M] (s : Finset ι) (f : ι → M) :
    ∏ x ∈ s, f x = (s.1.map f).prod :=
  rfl

@[to_additive (attr := simp)]
/-
**Finset.prod_map_val** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_map_val [CommMonoid M] (s : Finset ι) (f : ι -> M) : (s.1.map f).prod
 = ∏ a in s, f a
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prod_map_val [CommMonoid M] (s : Finset ι) (f : ι → M) : (s.1.map f).prod = ∏ a ∈ s, f a :=
  rfl

@[simp]
/-
**Finset.sum_multiset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_multiset_singleton (s : Finset ι) : ∑ a in s, {a} = s.val
参数：s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sum_map_singleton`：sum_map_singleton (s : Multiset M) : (s.map 
fun a => ({a} : Multiset M)).sum = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_multiset_singleton (s : Finset ι) : ∑ a ∈ s, {a} = s.val := by
  simp only [sum_eq_multiset_sum, Multiset.sum_map_singleton]

end Finset

@[to_additive (attr := simp)]
/-
**map_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G M N] [Monoid
HomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s, f x) = ∏ x in
 s, g (f x)
参数：g : G；f : ι -> M；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_multiset_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst 
: CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MonoidHomCla
ss F M …
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
-/
theorem map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G M N] [MonoidHomClass G M N]
    (g : G) (f : ι → M) (s : Finset ι) : g (∏ x ∈ s, f x) = ∏ x ∈ s, g (f x) := by
  simp only [Finset.prod_eq_multiset_prod, map_multiset_prod, Multiset.map_map]; rfl

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

namespace Finset

section CommMonoid

variable [CommMonoid M]

@[to_additive (attr := simp)]
/-
**Finset.prod_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_empty : ∏ x in ∅, f x = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_empty : ∏ x ∈ ∅, f x = 1 :=
  rfl

/-- Variant of `prod_empty` not applied to a function. -/
@[to_additive (attr := grind =)]
/-
**Finset.prod_empty'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_empty' : Finset.prod (∅ : Finset ι) = fun (_ : ι -> M) => 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Variant of `prod_empty` not applied to a function.
-/
theorem prod_empty' : Finset.prod (∅ : Finset ι) = fun (_ : ι → M) => 1 :=
  rfl

@[to_additive]
/-
**Finset.prod_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_of_isEmpty [IsEmpty ι] (s : Finset ι) : ∏ i in s, f i = 1
参数：s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.eq_empty_of_isEmpty`：eq_empty_of_isEmpty [IsEmpty α] (s : Finset 
α) : s = ∅
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
-/
theorem prod_of_isEmpty [IsEmpty ι] (s : Finset ι) : ∏ i ∈ s, f i = 1 := by
  rw [eq_empty_of_isEmpty s, prod_empty]

@[to_additive (attr := simp)]
/-
**Finset.prod_const_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_const_one : (∏ _x in s, (1 : M)) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_const_one : (∏ _x ∈ s, (1 : M)) = 1 := by
  simp only [Finset.prod, Multiset.map_const', Multiset.prod_replicate, one_pow]

@[to_additive (attr := simp)]
/-
**Finset.prod_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x in s.map e, f x = ∏
 x in s, f (e x)
参数：s : Finset ι；e : ι ↪ κ；f : κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod.eq_1`：∀ {ι : Type u_1} {M : Type u_3} [inst : CommMonoid M] 
(s : Finset ι) (f : ι → M), s.prod f = (Multiset.map f s.val).prod
· 使用定理 `Finset.map_val`：map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.m
ap f
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
-/
theorem prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ → M) :
    ∏ x ∈ s.map e, f x = ∏ x ∈ s, f (e x) := by
  rw [Finset.prod, Finset.map_val, Multiset.map_map]; rfl

/-- Variant of `prod_map` not applied to a function. -/
@[to_additive (attr := grind =)]
/-
**Finset.prod_map'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_map' (s : Finset ι) (e : ι ↪ κ) : Finset.prod (s.map e) = fun (f : κ 
-> M) => ∏ x in s, f (e x)
参数：s : Finset ι；e : ι ↪ κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Variant of `prod_map` not applied to a function.
-/
theorem prod_map' (s : Finset ι) (e : ι ↪ κ) :
    Finset.prod (s.map e) = fun (f : κ → M) => ∏ x ∈ s, f (e x) := by
  funext f
  simp

section ToList

@[to_additive (attr := simp, grind =)]
/-
**Finset.prod_map_toList** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_map_toList (s : Finset ι) (f : ι -> M) : (s.toList.map f).prod = s.pr
od f
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod.eq_1`：∀ {ι : Type u_1} {M : Type u_3} [inst : CommMonoid M] 
(s : Finset ι) (f : ι → M), s.prod f = (Multiset.map f s.val).prod
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_coe`：prod_coe (l : List M) : prod ↑l = l.prod
· 使用定理 `Multiset.map_coe`：∀ {α : Type u_1} {β : Type v} (f : α → β) (l : List α)
, Multiset.map f ↑l = ↑(List.map f l)
· 使用定理 `Finset.coe_toList`：coe_toList (s : Finset α) : (s.toList : Multiset α) =
 s.val
-/
theorem prod_map_toList (s : Finset ι) (f : ι → M) : (s.toList.map f).prod = s.prod f := by
  rw [Finset.prod, ← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]

@[to_additive (attr := simp, grind =)]
/-
**Finset.prod_toList** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_toList {M : Type*} [CommMonoid M] (s : Finset M) : s.toList.prod = ∏ 
x in s, x
参数：s : Finset M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `Finset.prod_map_toList`：prod_map_toList (s : Finset ι) (f : ι -> M) : (s
.toList.map f).prod = s.prod f
-/
theorem prod_toList {M : Type*} [CommMonoid M] (s : Finset M) :
    s.toList.prod = ∏ x ∈ s, x := by
  simpa using! s.prod_map_toList id

end ToList

@[to_additive]
/-
**Finset._root_.Equiv.Perm.prod_comp** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Equiv.Perm.prod_comp (σ : Equiv.Perm ι) (s : Finset ι) (f : ι → M)
    (hs : { a | σ a ≠ a } ⊆ s) : (∏ x ∈ s, f (σ x)) = ∏ x ∈ s, f x := by
  convert! (prod_map s σ.toEmbedding f).symm
  exact (map_perm hs).symm

@[to_additive]
/-
**Finset._root_.Equiv.Perm.prod_comp'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Equiv.Perm.prod_comp' (σ : Equiv.Perm ι) (s : Finset ι) (f : ι → ι → M)
    (hs : { a | σ a ≠ a } ⊆ s) : (∏ x ∈ s, f (σ x) x) = ∏ x ∈ s, f x (σ.symm x) := by
  convert! σ.prod_comp s (fun x => f x (σ.symm x)) hs
  rw [Equiv.symm_apply_apply]

end CommMonoid

end Finset

namespace Finset

section CommMonoid

variable [CommMonoid M]

section bij
variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}

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
/-
**Finset.prod_bij** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_bij (i : forall a in s, κ) (hi : forall a ha, i a ha in t) (i_inj : f
orall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj : forall b in t, ex
ists a ha, i a ha = b) (h : forall a ha, f a = g (i a ha)) : ∏ x in s, f x = ∏ x
 in t, g x
参数：i : forall a in s, κ；hi : forall a ha, i a ha in t；i_inj : forall a₁ ha₁ a₂ h
a₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂；i_surj : forall b in t, exists a ha, i a ha =
 b；h : forall a ha, f a = g (i a ha)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Multiset.map_eq_map_of_bij_of_nodup`：map_eq_map_of_bij_of_nodup (f : α -
> γ) (g : β -> γ) {s : Multiset α} {t : Multiset β} (hs : s.Nodup) (ht : t.Nodup
) (i : forall a in s, β) …
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem prod_bij (i : ∀ a ∈ s, κ) (hi : ∀ a ha, i a ha ∈ t)
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) (h : ∀ a ha, f a = g (i a ha)) :
    ∏ x ∈ s, f x = ∏ x ∈ t, g x :=
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
/-
**Finset.prod_bij'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_bij' (i : forall a in s, κ) (j : forall a in t, ι) (hi : forall a ha,
 i a ha in t) (hj : forall a ha, j a ha in s) (left_inv : forall a ha, j (i a ha
) (hi a ha) = a) (right_inv : forall a ha, i (j a ha) (hj a ha) = a) (h : forall
 a ha, f a = g (i a ha)) : ∏ x in s, f x = ∏ x in t, g x
参数：i : forall a in s, κ；j : forall a in t, ι；hi : forall a ha, i a ha in t；hj : 
forall a ha, j a ha in s；left_inv : forall a ha, j (i a ha) (hi a ha) = a；right_
inv : forall a ha, i (j a ha) (hj a ha) = a；h : forall a ha, f a = g (i a ha)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_bij`：prod_bij (i : forall a in s, κ) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_bij' (i : ∀ a ∈ s, κ) (j : ∀ a ∈ t, ι) (hi : ∀ a ha, i a ha ∈ t)
    (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) (h : ∀ a ha, f a = g (i a ha)) :
    ∏ x ∈ s, f x = ∏ x ∈ t, g x := by
  refine prod_bij i hi (fun a1 h1 a2 h2 eq ↦ ?_) (fun b hb ↦ ⟨_, hj b hb, right_inv b hb⟩) h
  rw [← left_inv a1 h1, ← left_inv a2 h2]
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
/-
**Finset.prod_nbij** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_nbij (i : ι -> κ) (hi : forall a in s, i a in t) (i_inj : (s : Set ι)
.InjOn i) (i_surj : (s : Set ι).SurjOn i t) (h : forall a in s, f a = g (i a)) :
 ∏ x in s, f x = ∏ x in t, g x
参数：i : ι -> κ；hi : forall a in s, i a in t；i_inj : (s : Set ι).InjOn i；i_surj : 
(s : Set ι).SurjOn i t；h : forall a in s, f a = g (i a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_bij`：prod_bij (i : forall a in s, κ) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma prod_nbij (i : ι → κ) (hi : ∀ a ∈ s, i a ∈ t) (i_inj : (s : Set ι).InjOn i)
    (i_surj : (s : Set ι).SurjOn i t) (h : ∀ a ∈ s, f a = g (i a)) :
    ∏ x ∈ s, f x = ∏ x ∈ t, g x :=
  prod_bij (fun a _ ↦ i a) hi i_inj (by simpa using! i_surj) h

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
/-
**Finset.prod_nbij'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_nbij' (i : ι -> κ) (j : κ -> ι) (hi : forall a in s, i a in t) (hj : 
forall a in t, j a in s) (left_inv : forall a in s, j (i a) = a) (right_inv : fo
rall a in t, i (j a) = a) (h : forall a in s, f a = g (i a)) : ∏ x in s, f x = ∏
 x in t, g x
参数：i : ι -> κ；j : κ -> ι；hi : forall a in s, i a in t；hj : forall a in t, j a in
 s；left_inv : forall a in s, j (i a) = a；right_inv : forall a in t, i (j a) = a；
h : forall a in s, f a = g (i a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_bij'`：prod_bij' (i : forall a in s, κ) (j : forall a in t, ι
) (hi : forall a ha, i a ha in t) (hj : forall a ha, j a ha in s) (left_inv : fo
rall a…
-/
lemma prod_nbij' (i : ι → κ) (j : κ → ι) (hi : ∀ a ∈ s, i a ∈ t) (hj : ∀ a ∈ t, j a ∈ s)
    (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a)
    (h : ∀ a ∈ s, f a = g (i a)) : ∏ x ∈ s, f x = ∏ x ∈ t, g x :=
  prod_bij' (fun a _ ↦ i a) (fun b _ ↦ j b) hi hj left_inv right_inv h

/-- Specialization of `Finset.prod_nbij'` that automatically fills in most arguments.

See `Fintype.prod_equiv` for the version where `s` and `t` are `univ`. -/
@[to_additive /-- Specialization of `Finset.sum_nbij'` that automatically fills in most arguments.

See `Fintype.sum_equiv` for the version where `s` and `t` are `univ`. -/]
/-
**Finset.prod_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i in t) (hfg : forall i
 in s, f i = g (e i)) : ∏ i in s, f i = ∏ i in t, g i
参数：e : ι ≃ κ；hst : forall i, i in s ↔ e i in t；hfg : forall i in s, f i = g (e i
)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_nbij'`：prod_nbij' (i : ι -> κ) (j : κ -> ι) (hi : forall a i
n s, i a in t) (hj : forall a in t, j a in s) (left_inv : forall a in s, j (i a)
 = a) (…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_equiv (e : ι ≃ κ) (hst : ∀ i, i ∈ s ↔ e i ∈ t) (hfg : ∀ i ∈ s, f i = g (e i)) :
    ∏ i ∈ s, f i = ∏ i ∈ t, g i := by refine prod_nbij' e e.symm ?_ ?_ ?_ ?_ hfg <;> simp [hst]

/-- Specialization of `Finset.prod_bij` that automatically fills in most arguments.

See `Fintype.prod_bijective` for the version where `s` and `t` are `univ`. -/
@[to_additive /-- Specialization of `Finset.sum_bij` that automatically fills in most arguments.

See `Fintype.sum_bijective` for the version where `s` and `t` are `univ`. -/]
/-
**Finset.prod_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_bijective (e : ι -> κ) (he : e.Bijective) (hst : forall i, i in s ↔ e
 i in t) (hfg : forall i in s, f i = g (e i)) : ∏ i in s, f i = ∏ i in t, g i
参数：e : ι -> κ；he : e.Bijective；hst : forall i, i in s ↔ e i in t；hfg : forall i 
in s, f i = g (e i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_equiv`：prod_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i 
in t) (hfg : forall i in s, f i = g (e i)) : ∏ i in s, f i = ∏ i in t, g i
-/
lemma prod_bijective (e : ι → κ) (he : e.Bijective) (hst : ∀ i, i ∈ s ↔ e i ∈ t)
    (hfg : ∀ i ∈ s, f i = g (e i)) :
    ∏ i ∈ s, f i = ∏ i ∈ t, g i := prod_equiv (.ofBijective e he) hst hfg

end bij

@[to_additive]
/-
**Finset.prod_hom_rel** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_hom_rel [CommMonoid N] {r : M -> N -> Prop} {f : ι -> M} {g : ι -> N}
 {s : Finset ι} (h₁ : r 1 1) (h₂ : forall a b c, r b c -> r (f a * b) (g a * c))
 : r (∏ x in s, f x) (∏ x in s, g x)
参数：h₁ : r 1 1；h₂ : forall a b c, r b c -> r (f a * b) (g a * c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_hom_rel`：prod_hom_rel (s : Multiset ι) {r : M -> N -> Prop
} {f : ι -> M} {g : ι -> N} (h₁ : r 1 1) (h₂ : forall ⦃a b c⦄, r b c -> r (f a *
 b) (g a * …
-/
theorem prod_hom_rel [CommMonoid N] {r : M → N → Prop} {f : ι → M} {g : ι → N} {s : Finset ι}
    (h₁ : r 1 1) (h₂ : ∀ a b c, r b c → r (f a * b) (g a * c)) :
    r (∏ x ∈ s, f x) (∏ x ∈ s, g x) := by
  delta Finset.prod
  apply Multiset.prod_hom_rel <;> assumption

variable (f s)

@[to_additive]
/-
**Finset.prod_coe_sort_eq_attach** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_coe_sort_eq_attach (f : s -> M) : ∏ i : s, f i = ∏ i in s.attach, f i
参数：f : s -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_coe_sort_eq_attach (f : s → M) : ∏ i : s, f i = ∏ i ∈ s.attach, f i :=
  rfl

variable {f s}

@[to_additive]
/-
**Finset.prod_ite_index** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_ite_index (p : Prop) [Decidable p] (s t : Finset ι) (f : ι -> M) : ∏ 
x in if p then s else t, f x = if p then ∏ x in s, f x else ∏ x in t, f x
参数：p : Prop；s t : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
-/
theorem prod_ite_index (p : Prop) [Decidable p] (s t : Finset ι) (f : ι → M) :
    ∏ x ∈ if p then s else t, f x = if p then ∏ x ∈ s, f x else ∏ x ∈ t, f x :=
  apply_ite (fun s => ∏ x ∈ s, f x) _ _ _

@[to_additive (attr := simp)]
/-
**Finset.prod_ite_irrel** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_ite_irrel (p : Prop) [Decidable p] (s : Finset ι) (f g : ι -> M) : ∏ 
x in s, (if p then f x else g x) = if p then ∏ x in s, f x else ∏ x in s, g x
参数：p : Prop；s : Finset ι；f g : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem prod_ite_irrel (p : Prop) [Decidable p] (s : Finset ι) (f g : ι → M) :
    ∏ x ∈ s, (if p then f x else g x) = if p then ∏ x ∈ s, f x else ∏ x ∈ s, g x := by
  split_ifs with h <;> rfl

@[to_additive (attr := simp)]
/-
**Finset.prod_dite_irrel** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_dite_irrel (p : Prop) [Decidable p] (s : Finset ι) (f : p -> ι -> M) 
(g : ¬p -> ι -> M) : ∏ x in s, (if h : p then f h x else g h x) = if h : p then 
∏ x in s, f h x else ∏ x in s, g h x
参数：p : Prop；s : Finset ι；f : p -> ι -> M；g : ¬p -> ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem prod_dite_irrel (p : Prop) [Decidable p] (s : Finset ι) (f : p → ι → M) (g : ¬p → ι → M) :
    ∏ x ∈ s, (if h : p then f h x else g h x) =
      if h : p then ∏ x ∈ s, f h x else ∏ x ∈ s, g h x := by
  split_ifs with h <;> rfl

@[to_additive]
/-
**Finset.ite_prod_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ite_prod_one (p : Prop) [Decidable p] (s : Finset ι) (f : ι -> M) : (if p 
then (∏ x in s, f x) else 1) = ∏ x in s, if p then f x else 1
参数：p : Prop；s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_ite_irrel`：prod_ite_irrel (p : Prop) [Decidable p] (s : Fins
et ι) (f g : ι -> M) : ∏ x in s, (if p then f x else g x) = if p then ∏ x in s, 
f x else ∏ …
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ite_prod_one (p : Prop) [Decidable p] (s : Finset ι) (f : ι → M) :
    (if p then (∏ x ∈ s, f x) else 1) = ∏ x ∈ s, if p then f x else 1 := by
  simp only [prod_ite_irrel, prod_const_one]

@[to_additive]
/-
**Finset.ite_one_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ite_one_prod (p : Prop) [Decidable p] (s : Finset ι) (f : ι -> M) : (if p 
then 1 else (∏ x in s, f x)) = ∏ x in s, if p then 1 else f x
参数：p : Prop；s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_ite_irrel`：prod_ite_irrel (p : Prop) [Decidable p] (s : Fins
et ι) (f g : ι -> M) : ∏ x in s, (if p then f x else g x) = if p then ∏ x in s, 
f x else ∏ …
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ite_one_prod (p : Prop) [Decidable p] (s : Finset ι) (f : ι → M) :
    (if p then 1 else (∏ x ∈ s, f x)) = ∏ x ∈ s, if p then 1 else f x := by
  simp only [prod_ite_irrel, prod_const_one]

@[to_additive]
/-
**Finset.nonempty_of_prod_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_of_prod_ne_one (h : ∏ x in s, f x != 1) : s.Nonempty
参数：h : ∏ x in s, f x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonempty_of_prod_ne_one (h : ∏ x ∈ s, f x ≠ 1) : s.Nonempty :=
  s.eq_empty_or_nonempty.elim (fun H => False.elim <| h <| H.symm ▸ prod_empty) id

@[to_additive]
/-
**Finset.prod_range_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_range_zero (f : Nat -> M) : ∏ k in range 0, f k = 1
参数：f : Nat -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.range_zero`：range_zero : range 0 = ∅
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
-/
theorem prod_range_zero (f : ℕ → M) : ∏ k ∈ range 0, f k = 1 := by rw [range_zero, prod_empty]

open List
/-
**Finset.sum_filter_count_eq_countP** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_filter_count_eq_countP [DecidableEq ι] (p : ι -> Prop) [DecidablePred 
p] (l : List ι) : ∑ x in l.toFinset with p x, l.count x = l.countP p
参数：p : ι -> Prop；l : List ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sum_map_count_dedup_filter_eq_countP`：sum_map_count_dedup_filter_eq
_countP (p : α -> Bool) (l : List α) : ((l.dedup.filter p).map fun x => l.count 
x).sum = l.countP p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_filter_count_eq_countP [DecidableEq ι] (p : ι → Prop) [DecidablePred p] (l : List ι) :
    ∑ x ∈ l.toFinset with p x, l.count x = l.countP p := by
  simp [Finset.sum, sum_map_count_dedup_filter_eq_countP p l]

open Multiset


@[to_additive]
/-
**Finset.prod_mem_multiset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_mem_multiset [DecidableEq ι] (m : Multiset ι) (f : { x // x in m } ->
 M) (g : ι -> M) (hfg : forall x, f x = g x) : ∏ x : { x // x in m }, f x = ∏ x 
in m.toFinset, g x
参数：m : Multiset ι；f : { x // x in m } -> M；g : ι -> M；hfg : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_bij'`：prod_bij' (i : forall a in s, κ) (j : forall a in t, ι
) (hi : forall a ha, i a ha in t) (hj : forall a ha, j a ha in s) (left_inv : fo
rall a…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_mem_multiset [DecidableEq ι] (m : Multiset ι) (f : { x // x ∈ m } → M) (g : ι → M)
    (hfg : ∀ x, f x = g x) : ∏ x : { x // x ∈ m }, f x = ∏ x ∈ m.toFinset, g x := by
  refine prod_bij' (fun x _ ↦ x) (fun x hx ↦ ⟨x, Multiset.mem_toFinset.1 hx⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp [hfg]

/-- To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors. -/
@[to_additive /-- To prove a property of a sum, it suffices to prove that
the property is additive and holds on summands. -/]
/-
**Finset.prod_induction** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_induction {M : Type*} [CommMonoid M] (f : ι -> M) (p : M -> Prop) (ho
m : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (base : forall x in s, p <
| f x) : p ∏ x in s, f x
参数：f : ι -> M；p : M -> Prop；hom : forall a b, p a -> p b -> p (a * b)；unit : p 1
；base : forall x in s, p <| f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_induction`：prod_induction (p : M -> Prop) (s : Multiset M)
 (p_mul : forall a b, p a -> p b -> p (a * b)) (p_one : p 1) (p_s : forall a in 
s, p a) : p s…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.forall_mem_map_iff`：forall_mem_map_iff {f : α -> β} {p : β -> P
rop} {s : Multiset α} : (forall y in s.map f, p y) ↔ forall x in s, p (f x)
-/
theorem prod_induction {M : Type*} [CommMonoid M] (f : ι → M) (p : M → Prop)
    (hom : ∀ a b, p a → p b → p (a * b)) (unit : p 1) (base : ∀ x ∈ s, p <| f x) :
    p <| ∏ x ∈ s, f x :=
  Multiset.prod_induction _ _ hom unit (Multiset.forall_mem_map_iff.mpr base)

/-- To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors. -/
@[to_additive /-- To prove a property of a sum, it suffices to prove that
the property is additive and holds on summands. -/]
/-
**Finset.prod_induction_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_induction_nonempty {M : Type*} [CommMonoid M] (f : ι -> M) (p : M -> 
Prop) (hom : forall a b, p a -> p b -> p (a * b)) (nonempty : s.Nonempty) (base 
: forall x in s, p <| f x) : p ∏ x in s, f x
参数：f : ι -> M；p : M -> Prop；hom : forall a b, p a -> p b -> p (a * b)；nonempty :
 s.Nonempty；base : forall x in s, p <| f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_induction_nonempty`：prod_induction_nonempty (p : M -> Prop
) (p_mul : forall a b, p a -> p b -> p (a * b)) (hs : s != ∅) (p_s : forall a in
 s, p a) : p s.prod
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.forall_mem_map_iff`：forall_mem_map_iff {f : α -> β} {p : β -> P
rop} {s : Multiset α} : (forall y in s.map f, p y) ↔ forall x in s, p (f x)
-/
theorem prod_induction_nonempty {M : Type*} [CommMonoid M] (f : ι → M) (p : M → Prop)
    (hom : ∀ a b, p a → p b → p (a * b)) (nonempty : s.Nonempty) (base : ∀ x ∈ s, p <| f x) :
    p <| ∏ x ∈ s, f x :=
  Multiset.prod_induction_nonempty p hom (by simp [nonempty_iff_ne_empty.mp nonempty])
    (Multiset.forall_mem_map_iff.mpr base)

@[to_additive]
/-
**Finset.prod_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_pow (s : Finset ι) (n : Nat) (f : ι -> M) : ∏ x in s, f x ^ n = (∏ x 
in s, f x) ^ n
参数：s : Finset ι；n : Nat；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_map_pow`：prod_map_pow {n : Nat} : (m.map fun i => f i ^ n)
.prod = (m.map f).prod ^ n
-/
theorem prod_pow (s : Finset ι) (n : ℕ) (f : ι → M) : ∏ x ∈ s, f x ^ n = (∏ x ∈ s, f x) ^ n :=
  Multiset.prod_map_pow
/-
**Finset.prod_dvd_prod_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_dvd_prod_of_subset {ι M : Type*} [CommMonoid M] (s t : Finset ι) (f :
 ι -> M) (h : s subseteq t) : (∏ i in s, f i) ∣ ∏ i in t, f i
参数：s t : Finset ι；f : ι -> M；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_dvd_prod_of_le`：prod_dvd_prod_of_le (h : s <= t) : s.prod 
∣ t.prod
· 使用定理 `Multiset.map_le_map`：map_le_map {f : α -> β} {s t : Multiset α} (h : s <
= t) : map f s <= map f t
-/
theorem prod_dvd_prod_of_subset {ι M : Type*} [CommMonoid M] (s t : Finset ι) (f : ι → M)
    (h : s ⊆ t) : (∏ i ∈ s, f i) ∣ ∏ i ∈ t, f i :=
  Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| by simpa

end CommMonoid

section MulOpposite
variable [AddCommMonoid M] (s : Finset ι)

open MulOpposite

/-- Moving to the opposite additive commutative monoid commutes with summing. -/
/-
**Finset.op_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M] (s : Finset ι) (f
 : ι → M),   MulOpposite.op (∑ x ∈ s, f x) = ∑ x ∈ s, MulOpposite.op (f x)
参数：s : Finset ι；f : ι → M；∑ x ∈ s, f x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N

--- 原说明 ---
Moving to the opposite additive commutative monoid commutes with summing.
-/
@[simp] lemma op_sum (f : ι → M) : op (∑ x ∈ s, f x) = ∑ x ∈ s, op (f x) := map_sum opAddEquiv ..
/-
**Finset.unop_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M] (s : Finset ι) (f
 : ι → Mᵐᵒᵖ),   MulOpposite.unop (∑ x ∈ s, f x) = ∑ x ∈ s, MulOpposite.unop (f x
)
参数：s : Finset ι；f : ι → Mᵐᵒᵖ；∑ x ∈ s, f x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N

--- 原说明 ---
Moving to the opposite additive commutative monoid commutes with summing.
-/
@[simp] lemma unop_sum (f : ι → Mᵐᵒᵖ) : unop (∑ x ∈ s, f x) = ∑ x ∈ s, unop (f x) :=
  map_sum opAddEquiv.symm ..

end MulOpposite

section AddOpposite
variable [CommMonoid M] (s : Finset ι)

open AddOpposite

/-
**Finset.op_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : CommMonoid M] (s : Finset ι) (f : 
ι → M),   AddOpposite.op (∏ i ∈ s, f i) = ∏ i ∈ s, AddOpposite.op (f i)
参数：s : Finset ι；f : ι → M；∏ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
@[simp] lemma op_prod (f : ι → M) : op (∏ i ∈ s, f i) = ∏ i ∈ s, op (f i) := map_prod opMulEquiv ..
/-
**Finset.unop_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : CommMonoid M] (s : Finset ι) (f : 
ι → Mᵐᵒᵖ),   AddOpposite.unop (∏ i ∈ s, f i) = ∏ i ∈ s, AddOpposite.unop (f i)
参数：s : Finset ι；f : ι → Mᵐᵒᵖ；∏ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
@[simp] lemma unop_prod (f : ι → Mᵐᵒᵖ) : unop (∏ i ∈ s, f i) = ∏ i ∈ s, unop (f i) :=
  map_prod opMulEquiv.symm ..

end AddOpposite

section DivisionCommMonoid

variable [DivisionCommMonoid G]

@[to_additive (attr := simp)]
/-
**Finset.prod_inv_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_inv_distrib (f : ι -> G) : (∏ x in s, (f x)⁻¹) = (∏ x in s, f x)⁻¹
参数：f : ι -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_map_inv`：prod_map_inv : (m.map fun i => (f i)⁻¹).prod = (m
.map f).prod⁻¹
-/
theorem prod_inv_distrib (f : ι → G) : (∏ x ∈ s, (f x)⁻¹) = (∏ x ∈ s, f x)⁻¹ :=
  Multiset.prod_map_inv

@[to_additive (attr := simp)]
/-
**Finset.prod_div_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_div_distrib (f g : ι -> G) : ∏ x in s, f x / g x = (∏ x in s, f x) / 
∏ x in s, g x
参数：f g : ι -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_map_div`：prod_map_div : (m.map fun i => f i / g i).prod = 
(m.map f).prod / (m.map g).prod
-/
theorem prod_div_distrib (f g : ι → G) : ∏ x ∈ s, f x / g x = (∏ x ∈ s, f x) / ∏ x ∈ s, g x :=
  Multiset.prod_map_div

@[to_additive]
/-
**Finset.prod_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_zpow (f : ι -> G) (s : Finset ι) (n : Int) : ∏ a in s, f a ^ n = (∏ a
 in s, f a) ^ n
参数：f : ι -> G；s : Finset ι；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_map_zpow`：prod_map_zpow {n : Int} : (m.map fun i => f i ^ 
n).prod = (m.map f).prod ^ n
-/
theorem prod_zpow (f : ι → G) (s : Finset ι) (n : ℤ) : ∏ a ∈ s, f a ^ n = (∏ a ∈ s, f a) ^ n :=
  Multiset.prod_map_zpow

end DivisionCommMonoid

/-
**Finset.sum_nat_mod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_nat_mod (s : Finset ι) (n : Nat) (f : ι -> Nat) : (∑ i in s, f i) % n 
= (∑ i in s, f i % n) % n
参数：s : Finset ι；n : Nat；f : ι -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.sum_nat_mod`：sum_nat_mod (s : Multiset Nat) (n : Nat) : s.sum %
 n = (s.map (· % n)).sum % n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum.eq_1`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M
] (s : Finset ι) (f : ι → M),   s.sum f = (Multiset.map f s.val).sum
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
-/
theorem sum_nat_mod (s : Finset ι) (n : ℕ) (f : ι → ℕ) :
    (∑ i ∈ s, f i) % n = (∑ i ∈ s, f i % n) % n :=
  (Multiset.sum_nat_mod _ _).trans <| by rw [Finset.sum, Multiset.map_map]; rfl
/-
**Finset.prod_nat_mod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_nat_mod (s : Finset ι) (n : Nat) (f : ι -> Nat) : (∏ i in s, f i) % n
 = (∏ i in s, f i % n) % n
参数：s : Finset ι；n : Nat；f : ι -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.prod_nat_mod`：prod_nat_mod (s : Multiset Nat) (n : Nat) : s.pro
d % n = (s.map (· % n)).prod % n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod.eq_1`：∀ {ι : Type u_1} {M : Type u_3} [inst : CommMonoid M] 
(s : Finset ι) (f : ι → M), s.prod f = (Multiset.map f s.val).prod
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
-/
theorem prod_nat_mod (s : Finset ι) (n : ℕ) (f : ι → ℕ) :
    (∏ i ∈ s, f i) % n = (∏ i ∈ s, f i % n) % n :=
  (Multiset.prod_nat_mod _ _).trans <| by rw [Finset.prod, Multiset.map_map]; rfl
/-
**Finset.sum_int_mod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_int_mod (s : Finset ι) (n : Int) (f : ι -> Int) : (∑ i in s, f i) % n 
= (∑ i in s, f i % n) % n
参数：s : Finset ι；n : Int；f : ι -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.sum_int_mod`：sum_int_mod (s : Multiset Int) (n : Int) : s.sum %
 n = (s.map (· % n)).sum % n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum.eq_1`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M
] (s : Finset ι) (f : ι → M),   s.sum f = (Multiset.map f s.val).sum
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
-/
theorem sum_int_mod (s : Finset ι) (n : ℤ) (f : ι → ℤ) :
    (∑ i ∈ s, f i) % n = (∑ i ∈ s, f i % n) % n :=
  (Multiset.sum_int_mod _ _).trans <| by rw [Finset.sum, Multiset.map_map]; rfl
/-
**Finset.prod_int_mod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_int_mod (s : Finset ι) (n : Int) (f : ι -> Int) : (∏ i in s, f i) % n
 = (∏ i in s, f i % n) % n
参数：s : Finset ι；n : Int；f : ι -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.prod_int_mod`：prod_int_mod (s : Multiset Int) (n : Int) : s.pro
d % n = (s.map (· % n)).prod % n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod.eq_1`：∀ {ι : Type u_1} {M : Type u_3} [inst : CommMonoid M] 
(s : Finset ι) (f : ι → M), s.prod f = (Multiset.map f s.val).prod
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
-/
theorem prod_int_mod (s : Finset ι) (n : ℤ) (f : ι → ℤ) :
    (∏ i ∈ s, f i) % n = (∏ i ∈ s, f i % n) % n :=
  (Multiset.prod_int_mod _ _).trans <| by rw [Finset.prod, Multiset.map_map]; rfl

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
/-
**Fintype.prod_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_bijective (e : ι -> κ) (he : e.Bijective) (f : ι -> M) (g : κ -> M) (
h : forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
参数：e : ι -> κ；he : e.Bijective；f : ι -> M；g : κ -> M；h : forall x, f x = g (e x)
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_equiv`：prod_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i 
in t) (hfg : forall i in s, f i = g (e i)) : ∏ i in s, f i = ∏ i in t, g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.ofBijective_apply`：∀ {α : Sort u} {β : Sort v} (f : α → β) (hf : F
unction.Bijective f) (a : α), (Equiv.ofBijective f hf) a = f a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_bijective (e : ι → κ) (he : e.Bijective) (f : ι → M) (g : κ → M)
    (h : ∀ x, f x = g (e x)) : ∏ x, f x = ∏ x, g x :=
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
/-
**Fintype.prod_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h : forall x, f x = g (e
 x)) : ∏ x, f x = ∏ x, g x
参数：e : ι ≃ κ；f : ι -> M；g : κ -> M；h : forall x, f x = g (e x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fintype.prod_bijective`：prod_bijective (e : ι -> κ) (he : e.Bijective) (
f : ι -> M) (g : κ -> M) (h : forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma prod_equiv (e : ι ≃ κ) (f : ι → M) (g : κ → M) (h : ∀ x, f x = g (e x)) :
    ∏ x, f x = ∏ x, g x := prod_bijective _ e.bijective _ _ h

@[to_additive]
/-
**Fintype._root_.Function.Bijective.prod_comp** 是 Mathlib 中的一个引理，位于命名空间 `Fintype
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Function.Bijective.prod_comp {e : ι → κ} (he : e.Bijective) (g : κ → M) :
    ∏ i, g (e i) = ∏ i, g i := prod_bijective _ he _ _ fun _ ↦ rfl

@[to_additive]
/-
**Fintype._root_.Equiv.prod_comp** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Equiv.prod_comp (e : ι ≃ κ) (g : κ → M) : ∏ i, g (e i) = ∏ i, g i :=
  prod_equiv e _ _ fun _ ↦ rfl

@[to_additive]
/-
**Fintype.prod_empty** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：prod_empty [IsEmpty ι] (f : ι -> M) : ∏ x : ι, f x = 1
参数：f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_of_isEmpty`：prod_of_isEmpty [IsEmpty ι] (s : Finset ι) : ∏ i
 in s, f i = 1
-/
theorem prod_empty [IsEmpty ι] (f : ι → M) : ∏ x : ι, f x = 1 := prod_of_isEmpty _

end CommMonoid
end Fintype

namespace Finset
variable [CommMonoid M]

@[to_additive (attr := simp)]
/-
**Finset.prod_attach_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_attach_univ [Fintype ι] (f : {i // i in @univ ι _} -> M) : ∏ i in uni
v.attach, f i = ∏ i, f ⟨i, mem_univ _⟩
参数：f : {i // i in @univ ι _} -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.subtypeUnivEquiv_apply`：∀ {α : Sort u_9} {p : α → Prop} (h : ∀ (x 
: α), p x) (x : Subtype p), (Equiv.subtypeUnivEquiv h) x = ↑x
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma prod_attach_univ [Fintype ι] (f : {i // i ∈ @univ ι _} → M) :
    ∏ i ∈ univ.attach, f i = ∏ i, f ⟨i, mem_univ _⟩ :=
  Fintype.prod_equiv (Equiv.subtypeUnivEquiv mem_univ) _ _ <| by simp

@[to_additive]
/-
**Finset.prod_erase_attach** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_erase_attach [DecidableEq ι] {s : Finset ι} (f : ι -> M) (i : ↑s) : ∏
 j in s.attach.erase i, f ↑j = ∏ j in s.erase ↑i, f j
参数：f : ι -> M；i : ↑s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Embedding.coe_subtype`：coe_subtype {α} (p : α -> Prop) : ↑(subt
ype p) = Subtype.val
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.map_erase`：map_erase [DecidableEq α] (f : α ↪ β) (s : Finset α) (
a : α) : (s.erase a).map f = (s.map f).erase (f a)
· 使用定理 `Finset.attach_map_val`：attach_map_val {s : Finset α} : s.attach.map (Emb
edding.subtype _) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_erase_attach [DecidableEq ι] {s : Finset ι} (f : ι → M) (i : ↑s) :
    ∏ j ∈ s.attach.erase i, f ↑j = ∏ j ∈ s.erase ↑i, f j := by
  rw [← Function.Embedding.coe_subtype, ← prod_map]
  simp [attach_map_val]

end Finset

namespace Multiset

@[simp]
/-
**Multiset.card_sum** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：card_sum (s : Finset ι) (f : ι -> Multiset α) : card (∑ i in s, f i) = ∑ i
 in s, card (f i)
参数：s : Finset ι；f : ι -> Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma card_sum (s : Finset ι) (f : ι → Multiset α) : card (∑ i ∈ s, f i) = ∑ i ∈ s, card (f i) :=
  map_sum cardHom ..
/-
**Multiset.disjoint_list_sum_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_list_sum_left {a : Multiset α} {l : List (Multiset α)} : Disjoint
 l.sum a ↔ forall b in l, Disjoint b a
参数：Multiset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_list_sum_left {a : Multiset α} {l : List (Multiset α)} :
    Disjoint l.sum a ↔ ∀ b ∈ l, Disjoint b a := by
  induction l with
  | nil =>
    simp only [zero_disjoint, List.not_mem_nil, IsEmpty.forall_iff, forall_const, List.sum_nil]
  | cons b bs ih =>
    simp [ih]
/-
**Multiset.disjoint_list_sum_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_list_sum_right {a : Multiset α} {l : List (Multiset α)} : Disjoin
t a l.sum ↔ forall b in l, Disjoint a b
参数：Multiset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Multiset.disjoint_list_sum_left`：disjoint_list_sum_left {a : Multiset α}
 {l : List (Multiset α)} : Disjoint l.sum a ↔ forall b in l, Disjoint b a
-/
theorem disjoint_list_sum_right {a : Multiset α} {l : List (Multiset α)} :
    Disjoint a l.sum ↔ ∀ b ∈ l, Disjoint a b := by
  simpa only [disjoint_comm (a := a)] using disjoint_list_sum_left
/-
**Multiset.disjoint_sum_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_sum_left {a : Multiset α} {i : Multiset (Multiset α)} : Disjoint 
i.sum a ↔ forall b in i, Disjoint b a
参数：Multiset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.quot_mk_to_coe`：quot_mk_to_coe (l : List α) : @Eq (Multiset α) 
⟦l⟧ l
· 使用定理 `Multiset.sum_coe`：∀ {M : Type u_3} [inst : AddCommMonoid M] (l : List M)
, (↑l).sum = l.sum
· 使用定理 `Multiset.disjoint_list_sum_left`：disjoint_list_sum_left {a : Multiset α}
 {l : List (Multiset α)} : Disjoint l.sum a ↔ forall b in l, Disjoint b a
-/
theorem disjoint_sum_left {a : Multiset α} {i : Multiset (Multiset α)} :
    Disjoint i.sum a ↔ ∀ b ∈ i, Disjoint b a :=
  Quotient.inductionOn i fun l => by
    rw [quot_mk_to_coe, Multiset.sum_coe]
    exact disjoint_list_sum_left
/-
**Multiset.disjoint_sum_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_sum_right {a : Multiset α} {i : Multiset (Multiset α)} : Disjoint
 a i.sum ↔ forall b in i, Disjoint a b
参数：Multiset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Multiset.disjoint_sum_left`：disjoint_sum_left {a : Multiset α} {i : Mult
iset (Multiset α)} : Disjoint i.sum a ↔ forall b in i, Disjoint b a
-/
theorem disjoint_sum_right {a : Multiset α} {i : Multiset (Multiset α)} :
    Disjoint a i.sum ↔ ∀ b ∈ i, Disjoint a b := by
  simpa only [disjoint_comm (a := a)] using disjoint_sum_left
/-
**Multiset.disjoint_finsetSum_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_finsetSum_left {i : Finset ι} {f : ι -> Multiset α} {a : Multiset
 α} : Disjoint (i.sum f) a ↔ forall b in i, Disjoint (f b) a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Multiset.disjoint_sum_left`：disjoint_sum_left {a : Multiset α} {i : Mult
iset (Multiset α)} : Disjoint i.sum a ↔ forall b in i, Disjoint b a
-/
theorem disjoint_finsetSum_left {i : Finset ι} {f : ι → Multiset α} {a : Multiset α} :
    Disjoint (i.sum f) a ↔ ∀ b ∈ i, Disjoint (f b) a := by
  convert! @disjoint_sum_left _ a (map f i.val)
  simp

@[deprecated (since := "2026-04-08")] alias disjoint_finset_sum_left := disjoint_finsetSum_left
/-
**Multiset.disjoint_finsetSum_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_finsetSum_right {i : Finset ι} {f : ι -> Multiset α} {a : Multise
t α} : Disjoint a (i.sum f) ↔ forall b in i, Disjoint a (f b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Multiset.disjoint_finsetSum_left`：disjoint_finsetSum_left {i : Finset ι}
 {f : ι -> Multiset α} {a : Multiset α} : Disjoint (i.sum f) a ↔ forall b in i, 
Disjoint (f b) a
-/
theorem disjoint_finsetSum_right {i : Finset ι} {f : ι → Multiset α}
    {a : Multiset α} : Disjoint a (i.sum f) ↔ ∀ b ∈ i, Disjoint a (f b) := by
  simpa only [disjoint_comm] using disjoint_finsetSum_left

@[deprecated (since := "2026-04-08")] alias disjoint_finset_sum_right := disjoint_finsetSum_right

variable [DecidableEq α]
/-
**Multiset.count_sum'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_sum' {s : Finset ι} {a : α} {f : ι -> Multiset α} : count a (∑ x in 
s, f x) = ∑ x in s, count a (f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_sum`：count_sum [DecidableEq α] {m : Multiset β} {f : β ->
 Multiset α} {a : α} : count a (map f m).sum = sum (m.map fun b => count a <| f 
b)
-/
theorem count_sum' {s : Finset ι} {a : α} {f : ι → Multiset α} :
    count a (∑ x ∈ s, f x) = ∑ x ∈ s, count a (f x) := by
  dsimp only [Finset.sum]
  rw [count_sum]
/-
**Multiset.toFinset_prod_dvd_prod** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_prod_dvd_prod [DecidableEq M] [CommMonoid M] (S : Multiset M) : S
.toFinset.prod id ∣ S.prod
参数：S : Multiset M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_eq_multiset_prod`：prod_eq_multiset_prod [CommMonoid M] (s : 
Finset ι) (f : ι -> M) : ∏ x in s, f x = (s.1.map f).prod
· 使用定理 `Multiset.prod_dvd_prod_of_le`：prod_dvd_prod_of_le (h : s <= t) : s.prod 
∣ t.prod
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Multiset.dedup_le`：dedup_le (s : Multiset α) : dedup s <= s
-/
theorem toFinset_prod_dvd_prod [DecidableEq M] [CommMonoid M] (S : Multiset M) :
    S.toFinset.prod id ∣ S.prod := by
  rw [Finset.prod_eq_multiset_prod]
  refine Multiset.prod_dvd_prod_of_le ?_
  simp [Multiset.dedup_le S]

end Multiset

@[simp, norm_cast]
/-
**Units.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.coe_prod [CommMonoid M] (f : α -> Mˣ) (s : Finset α) : (↑(∏ i in s, 
f i) : M) = ∏ i in s, (f i : M)
参数：f : α -> Mˣ；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem Units.coe_prod [CommMonoid M] (f : α → Mˣ) (s : Finset α) :
    (↑(∏ i ∈ s, f i) : M) = ∏ i ∈ s, (f i : M) :=
  map_prod (Units.coeHom M) _ _


/-! ### `Additive`, `Multiplicative` -/


open Additive Multiplicative

section Monoid

variable [Monoid M]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ofMul_list_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofMul_list_prod (s : List M) : ofMul s.prod = (s.map ofMul).sum
参数：s : List M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
-/
theorem ofMul_list_prod (s : List M) : ofMul s.prod = (s.map ofMul).sum := by simp [ofMul]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**toMul_list_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMul_list_sum (s : List (Additive M)) : s.sum.toMul = (s.map toMul).prod
参数：s : List (Additive M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
-/
theorem toMul_list_sum (s : List (Additive M)) : s.sum.toMul = (s.map toMul).prod := by
  simp [toMul, ofMul]; rfl

end Monoid

section AddMonoid

variable [AddMonoid M]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ofAdd_list_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofAdd_list_prod (s : List M) : ofAdd s.sum = (s.map ofAdd).prod
参数：s : List M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
-/
theorem ofAdd_list_prod (s : List M) : ofAdd s.sum = (s.map ofAdd).prod := by simp [ofAdd]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**toAdd_list_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAdd_list_sum (s : List (Multiplicative M)) : s.prod.toAdd = (s.map toAdd
).sum
参数：s : List (Multiplicative M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
-/
theorem toAdd_list_sum (s : List (Multiplicative M)) : s.prod.toAdd = (s.map toAdd).sum := by
  simp [toAdd, ofAdd]; rfl

end AddMonoid

section CommMonoid

variable [CommMonoid M]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ofMul_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofMul_multiset_prod (s : Multiset M) : ofMul s.prod = (s.map ofMul).sum
参数：s : Multiset M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
-/
theorem ofMul_multiset_prod (s : Multiset M) : ofMul s.prod = (s.map ofMul).sum := by
  simp [ofMul]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**toMul_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMul_multiset_sum (s : Multiset (Additive M)) : s.sum.toMul = (s.map toMu
l).prod
参数：s : Multiset (Additive M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
-/
theorem toMul_multiset_sum (s : Multiset (Additive M)) : s.sum.toMul = (s.map toMul).prod := by
  simp [toMul, ofMul]; rfl

@[simp]
/-
**ofMul_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofMul_prod (s : Finset ι) (f : ι -> M) : ofMul (∏ i in s, f i) = ∑ i in s,
 ofMul (f i)
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMul_prod (s : Finset ι) (f : ι → M) : ofMul (∏ i ∈ s, f i) = ∑ i ∈ s, ofMul (f i) :=
  rfl

@[simp]
/-
**toMul_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMul_sum (s : Finset ι) (f : ι -> Additive M) : (∑ i in s, f i).toMul = ∏
 i in s, (f i).toMul
参数：s : Finset ι；f : ι -> Additive M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMul_sum (s : Finset ι) (f : ι → Additive M) :
    (∑ i ∈ s, f i).toMul = ∏ i ∈ s, (f i).toMul :=
  rfl

end CommMonoid

section AddCommMonoid

variable [AddCommMonoid M]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ofAdd_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofAdd_multiset_prod (s : Multiset M) : ofAdd s.sum = (s.map ofAdd).prod
参数：s : Multiset M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
-/
theorem ofAdd_multiset_prod (s : Multiset M) : ofAdd s.sum = (s.map ofAdd).prod := by
  simp [ofAdd]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**toAdd_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAdd_multiset_sum (s : Multiset (Multiplicative M)) : s.prod.toAdd = (s.m
ap toAdd).sum
参数：s : Multiset (Multiplicative M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
-/
theorem toAdd_multiset_sum (s : Multiset (Multiplicative M)) :
    s.prod.toAdd = (s.map toAdd).sum := by
  simp [toAdd, ofAdd]; rfl

@[simp]
/-
**ofAdd_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofAdd_sum (s : Finset ι) (f : ι -> M) : ofAdd (∑ i in s, f i) = ∏ i in s, 
ofAdd (f i)
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofAdd_sum (s : Finset ι) (f : ι → M) : ofAdd (∑ i ∈ s, f i) = ∏ i ∈ s, ofAdd (f i) :=
  rfl

@[simp]
/-
**toAdd_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAdd_prod (s : Finset ι) (f : ι -> Multiplicative M) : (∏ i in s, f i).to
Add = ∑ i in s, (f i).toAdd
参数：s : Finset ι；f : ι -> Multiplicative M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAdd_prod (s : Finset ι) (f : ι → Multiplicative M) :
    (∏ i ∈ s, f i).toAdd = ∑ i ∈ s, (f i).toAdd :=
  rfl

end AddCommMonoid

