/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
module

public import Mathlib.Data.Set.Prod
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.ModelTheory.LanguageMap
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Basics on First-Order Syntax

This file defines first-order terms, formulas, sentences, and theories in a style inspired by the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions

- A `FirstOrder.Language.Term` is defined so that `L.Term α` is the type of `L`-terms with free
  variables indexed by `α`.
- A `FirstOrder.Language.Formula` is defined so that `L.Formula α` is the type of `L`-formulas with
  free variables indexed by `α`.
- A `FirstOrder.Language.Sentence` is a formula with no free variables.
- A `FirstOrder.Language.Theory` is a set of sentences.
- The variables of terms and formulas can be relabelled with `FirstOrder.Language.Term.relabel`,
  `FirstOrder.Language.BoundedFormula.relabel`, and `FirstOrder.Language.Formula.relabel`.
- Given an operation on terms and an operation on relations,
  `FirstOrder.Language.BoundedFormula.mapTermRel` gives an operation on formulas.
- `FirstOrder.Language.BoundedFormula.castLE` adds more bound variables.
- `FirstOrder.Language.BoundedFormula.liftAt` raises the indexes of the bound variables above a
  particular index.
- `FirstOrder.Language.Term.subst` and `FirstOrder.Language.BoundedFormula.subst` substitute
  variables with given terms.
- `FirstOrder.Language.Term.substFunc` instead substitutes function definitions with given terms.
- Language maps can act on syntactic objects with functions such as
  `FirstOrder.Language.LHom.onFormula`.
- `FirstOrder.Language.Term.constantsVarsEquiv` and
  `FirstOrder.Language.BoundedFormula.constantsVarsEquiv` switch terms and formulas between having
  constants in the language and having extra free variables indexed by the same type.

## Implementation Notes

- `BoundedFormula` uses a locally nameless representation with bound variables as well-scoped de
  Bruijn levels (the variable bounded by the outermost quantifier is indexed by `0`). Specifically,
  a `L.BoundedFormula α n` is a formula with free variables indexed by a type `α`, which cannot be
  quantified over, and bound variables indexed by `Fin n`, which can. For any
  `φ : L.BoundedFormula α (n + 1)`, we define the formula `∀' φ : L.BoundedFormula α n` by
  universally quantifying over the variable indexed by `n : Fin (n + 1)`.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum
  hypothesis*][flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]
-/

@[expose] public section


universe u v w u' v'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) {L' : Language}
variable {M : Type w} {α : Type u'} {β : Type v'} {γ : Type*}

open FirstOrder

open Structure Fin

/--
Inductive type `Term` / 归纳类型 `Term`

English:
inductive Term
  parameters: (α : Type u')
  constructors (2):
    - var: α -> Term α
    - func: forall {l : Nat} (_f : L.Functions l) (_ts : Fin l -> Term α), Term α

中文:
归纳类型 Term
  参数: (α : 类型u')
  构造子 (2 个):
    - var: α -> Term α
    - func: 对任意 {l : 自然数} (_f : L.Functions l) (_ts : Fin l -> Term α), Term α
-/
inductive Term (α : Type u') : Type max u u'
  | var : α -> Term α
  | func : forall {l : Nat} (_f : L.Functions l) (_ts : Fin l -> Term α), Term α
export Term (var func)

variable {L}

namespace Term

/--
Instance `instDecidableEq` / 实例 `instDecidableEq`

English:
instance instDecidableEq
  signature: [DecidableEq α] [forall n, DecidableEq (L.Functions n)]
  body: instDecidableEq
decidable_of_iff (f = h ▸ g ∧ forall i : Fin m, xs i = ys (Fin.cast h i)) by
          subst h
          simp [funext_iff]
      else
.isFalse by simp [h]
| .var _, .func _ _ | .func _ _, .var _ => .isFalse by simp

中文:
实例 instDecidableEq
  签名: [DecidableEq α] [对任意 n, DecidableEq (L.Functions n)]
  定义体: instDecidableEq
decidable_of_iff (f = h ▸ g ∧ forall i : Fin m, xs i = ys (Fin.cast h i)) by
          subst h
          simp [funext_iff]
      else
.isFalse by simp [h]
| .var _, .func _ _ | .func _ _, .var _ => .isFalse by simp

Depends on / 依赖: instDecidableEq
-/
instance instDecidableEq [DecidableEq α] [forall n, DecidableEq (L.Functions n)] : DecidableEq (L.Term α)
| .var a, .var b => decidable_of_iff (a = b) by simp
  | @Term.func _ _ m f xs, @Term.func _ _ n g ys =>
      if h : m = n then
        letI : DecidableEq (L.Term α) := instDecidableEq
decidable_of_iff (f = h ▸ g ∧ forall i : Fin m, xs i = ys (Fin.cast h i)) by
          subst h
          simp [funext_iff]
      else
.isFalse by simp [h]
| .var _, .func _ _ | .func _ _, .var _ => .isFalse by simp

open Finset

/-- The `Finset` of variables used in a given term. -/
@[simp]
/--
Definition of `varFinset` / `varFinset` 的定义

English:
definition varFinset
  signature: [DecidableEq α]

中文:
定义 varFinset
  签名: [DecidableEq α]
-/
def varFinset [DecidableEq α] : L.Term α -> Finset α
  | var i => {i}
  | func _f ts => univ.biUnion fun i => (ts i).varFinset

/-- The `Finset` of variables from the left side of a sum used in a given term. -/
@[simp]
/--
Definition of `varFinsetLeft` / `varFinsetLeft` 的定义

English:
definition varFinsetLeft
  signature: [DecidableEq α]

中文:
定义 varFinsetLeft
  签名: [DecidableEq α]
-/
def varFinsetLeft [DecidableEq α] : L.Term (α oplus β) -> Finset α
  | var (Sum.inl i) => {i}
  | var (Sum.inr _i) => ∅
  | func _f ts => univ.biUnion fun i => (ts i).varFinsetLeft

/-- Relabels a term's variables along a particular function. -/
@[simp]
/--
Definition of `relabel` / `relabel` 的定义

English:
definition relabel
  signature: (g : α -> β)

中文:
定义 relabel
  签名: (g : α -> β)
-/
def relabel (g : α -> β) : L.Term α -> L.Term β
  | var i => var (g i)
  | func f ts => func f fun {i} => (ts i).relabel g

/--
theorem `relabel_id` / 定理 `relabel_id`

English:
theorem relabel_id
  given: (t : L.Term α)
  statement: t.relabel id = t
  proof: by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

@[simp]

中文:
定理 relabel_id
  条件: (t : L.Term α)
  结论: t.relabel id = t
  证明: by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

@[simp]
-/
theorem relabel_id (t : L.Term α) : t.relabel id = t := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

@[simp]
/--
theorem `relabel_id_eq_id` / 定理 `relabel_id_eq_id`

English:
theorem relabel_id_eq_id
  statement: (Term.relabel id : L.Term α -> L.Term α) = id
  proof: funext relabel_id

@[simp]

中文:
定理 relabel_id_eq_id
  结论: (Term.relabel id : L.Term α -> L.Term α) = id
  证明: funext relabel_id

@[simp]

Depends on / 依赖: relabel_id
-/
theorem relabel_id_eq_id : (Term.relabel id : L.Term α -> L.Term α) = id :=
  funext relabel_id

@[simp]
/--
theorem `relabel_relabel` / 定理 `relabel_relabel`

English:
theorem relabel_relabel
  given: (f : α -> β) (g : β -> γ) (t : L.Term α)
  proof: by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

@[simp]

中文:
定理 relabel_relabel
  条件: (f : α -> β) (g : β -> γ) (t : L.Term α)
  证明: by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

@[simp]
-/
theorem relabel_relabel (f : α -> β) (g : β -> γ) (t : L.Term α) :
    (t.relabel f).relabel g = t.relabel (g ∘ f) := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

@[simp]
/--
theorem `relabel_comp_relabel` / 定理 `relabel_comp_relabel`

English:
theorem relabel_comp_relabel
  given: (f : α -> β) (g : β -> γ)
  proof: funext (relabel_relabel f g)

中文:
定理 relabel_comp_relabel
  条件: (f : α -> β) (g : β -> γ)
  证明: funext (relabel_relabel f g)

Depends on / 依赖: relabel_relabel
-/
theorem relabel_comp_relabel (f : α -> β) (g : β -> γ) :
    (Term.relabel g ∘ Term.relabel f : L.Term α -> L.Term γ) = Term.relabel (g ∘ f) :=
  funext (relabel_relabel f g)

/-- Relabels a term's variables along a bijection. -/
@[simps]
/--
Definition of `relabelEquiv` / `relabelEquiv` 的定义

English:
definition relabelEquiv
  signature: (g : α ≃ β)
  body: ⟨relabel g, relabel g.symm, fun t => by simp, fun t => by simp⟩

中文:
定义 relabelEquiv
  签名: (g : α ≃ β)
  定义体: ⟨relabel g, relabel g.symm, fun t => by simp, fun t => by simp⟩

Depends on / 依赖: g.symm, relabel
-/
def relabelEquiv (g : α ≃ β) : L.Term α ≃ L.Term β :=
  ⟨relabel g, relabel g.symm, fun t => by simp, fun t => by simp⟩

/--
Definition of `restrictVar` / `restrictVar` 的定义

English:
definition restrictVar
  signature: [DecidableEq α]

中文:
定义 restrictVar
  签名: [DecidableEq α]
-/
def restrictVar [DecidableEq α] : forall (t : L.Term α) (_f : t.varFinset -> β), L.Term β
  | var a, f => var (f ⟨a, mem_singleton_self a⟩)
  | func F ts, f =>
    func F fun i => (ts i).restrictVar (f ∘ Set.inclusion
      (subset_biUnion_of_mem (fun i => varFinset (ts i)) (mem_univ i)))

/--
Definition of `restrictVarLeft` / `restrictVarLeft` 的定义

English:
definition restrictVarLeft
  signature: [DecidableEq α] {γ : Type*}

中文:
定义 restrictVarLeft
  签名: [DecidableEq α] {γ : 类型}
-/
def restrictVarLeft [DecidableEq α] {γ : Type*} :
    forall (t : L.Term (α oplus γ)) (_f : t.varFinsetLeft -> β), L.Term (β oplus γ)
  | var (Sum.inl a), f => var (Sum.inl (f ⟨a, mem_singleton_self a⟩))
  | var (Sum.inr a), _f => var (Sum.inr a)
  | func F ts, f =>
    func F fun i =>
      (ts i).restrictVarLeft (f ∘ Set.inclusion (subset_biUnion_of_mem
        (fun i => varFinsetLeft (ts i)) (mem_univ i)))

end Term

/--
Definition of `Constants.term` / `Constants.term` 的定义

English:
definition Constants.term
  signature: (c : L.Constants)
  body: func c default

中文:
定义 Constants.term
  签名: (c : L.Constants)
  定义体: func c default
-/
def Constants.term (c : L.Constants) : L.Term α :=
  func c default

/--
Definition of `Functions.apply₁` / `Functions.apply₁` 的定义

English:
definition Functions.apply₁
  signature: (f : L.Functions 1) (t : L.Term α)
  body: func f ![t]

中文:
定义 Functions.apply₁
  签名: (f : L.Functions 1) (t : L.Term α)
  定义体: func f ![t]
-/
def Functions.apply₁ (f : L.Functions 1) (t : L.Term α) : L.Term α :=
  func f ![t]

/--
Definition of `Functions.apply₂` / `Functions.apply₂` 的定义

English:
definition Functions.apply₂
  signature: (f : L.Functions 2) (t₁ t₂ : L.Term α)
  body: func f ![t₁, t₂]

中文:
定义 Functions.apply₂
  签名: (f : L.Functions 2) (t₁ t₂ : L.Term α)
  定义体: func f ![t₁, t₂]
-/
def Functions.apply₂ (f : L.Functions 2) (t₁ t₂ : L.Term α) : L.Term α :=
  func f ![t₁, t₂]

/--
Definition of `Functions.term` / `Functions.term` 的定义

English:
definition Functions.term
  signature: {n : Nat} (f : L.Functions n)
  body: func f Term.var

中文:
定义 Functions.term
  签名: {n : 自然数} (f : L.Functions n)
  定义体: func f Term.var

Depends on / 依赖: Term.var
-/
def Functions.term {n : Nat} (f : L.Functions n) : L.Term (Fin n) :=
  func f Term.var

namespace Term

/-- Sends a term with constants to a term with extra variables. -/
@[simp]
/--
Definition of `constantsToVars` / `constantsToVars` 的定义

English:
definition constantsToVars
  signature: : L[[γ]].Term α -> L.Term (γ oplus α)

中文:
定义 constantsToVars
  签名: : L[[γ]].Term α -> L.Term (γ oplus α)
-/
def constantsToVars : L[[γ]].Term α -> L.Term (γ oplus α)
  | var a => var (Sum.inr a)
  | @func _ _ 0 f ts =>
    Sum.casesOn f (fun f => func f fun i => (ts i).constantsToVars) fun c => var (Sum.inl c)
  | @func _ _ (_n + 1) f ts =>
    Sum.casesOn f (fun f => func f fun i => (ts i).constantsToVars) fun c => isEmptyElim c

/-- Sends a term with extra variables to a term with constants. -/
@[simp]
/--
Definition of `varsToConstants` / `varsToConstants` 的定义

English:
definition varsToConstants
  signature: : L.Term (γ oplus α) -> L[[γ]].Term α

中文:
定义 varsToConstants
  签名: : L.Term (γ oplus α) -> L[[γ]].Term α
-/
def varsToConstants : L.Term (γ oplus α) -> L[[γ]].Term α
  | var (Sum.inr a) => var a
  | var (Sum.inl c) => Constants.term (Sum.inr c)
  | func f ts => func (Sum.inl f) fun i => (ts i).varsToConstants

set_option backward.isDefEq.respectTransparency false in
/-- A bijection between terms with constants and terms with extra variables. -/
@[simps]
/--
Definition of `constantsVarsEquiv` / `constantsVarsEquiv` 的定义

English:
definition constantsVarsEquiv
  signature: : L[[γ]].Term α ≃ L.Term (γ oplus α)
  body: ⟨constantsToVars, varsToConstants, by
    intro t
    induction t with
    | var => rfl
    | @func n f _ ih =>
      cases n
      · cases f
        · simp [constantsToVars, varsToConstants, ih]
        · simp [constantsToVars, varsToConstants, Constants.term, eq_iff_true_of_subsingleton]
      · o

中文:
定义 constantsVarsEquiv
  签名: : L[[γ]].Term α ≃ L.Term (γ oplus α)
  定义体: ⟨constantsToVars, varsToConstants, by
    intro t
    induction t with
    | var => rfl
    | @func n f _ ih =>
      cases n
      · cases f
        · simp [constantsToVars, varsToConstants, ih]
        · simp [constantsToVars, varsToConstants, Constants.term, eq_iff_true_of_subsingleton]
      · o

Depends on / 依赖: Constants, Constants.term, constantsToVars, eq_iff_true_of_subsingleton, isEmptyElim, varsToConstants
-/
def constantsVarsEquiv : L[[γ]].Term α ≃ L.Term (γ oplus α) :=
  ⟨constantsToVars, varsToConstants, by
    intro t
    induction t with
    | var => rfl
    | @func n f _ ih =>
      cases n
      · cases f
        · simp [constantsToVars, varsToConstants, ih]
        · simp [constantsToVars, varsToConstants, Constants.term, eq_iff_true_of_subsingleton]
      · obtain - | f := f
        · simp [constantsToVars, varsToConstants, ih]
        · exact isEmptyElim f, by
    intro t
    induction t with
    | var x => cases x <;> rfl
    | @func n f _ ih => cases n <;> · simp [varsToConstants, constantsToVars, ih]⟩

/--
Definition of `constantsVarsEquivLeft` / `constantsVarsEquivLeft` 的定义

English:
definition constantsVarsEquivLeft
  signature: : L[[γ]].Term (α oplus β) ≃ L.Term ((γ oplus α) oplus β)
  body: constantsVarsEquiv.trans (relabelEquiv (Equiv.sumAssoc _ _ _)).symm

@[simp]

中文:
定义 constantsVarsEquivLeft
  签名: : L[[γ]].Term (α oplus β) ≃ L.Term ((γ oplus α) oplus β)
  定义体: constantsVarsEquiv.trans (relabelEquiv (Equiv.sumAssoc _ _ _)).symm

@[simp]

Depends on / 依赖: Equiv.sumAssoc, constantsVarsEquiv, constantsVarsEquiv.trans, relabelEquiv, sumAssoc
-/
def constantsVarsEquivLeft : L[[γ]].Term (α oplus β) ≃ L.Term ((γ oplus α) oplus β) :=
  constantsVarsEquiv.trans (relabelEquiv (Equiv.sumAssoc _ _ _)).symm

@[simp]
/--
theorem `constantsVarsEquivLeft_apply` / 定理 `constantsVarsEquivLeft_apply`

English:
theorem constantsVarsEquivLeft_apply
  given: (t : L[[γ]].Term (α oplus β))
  proof: rfl

@[simp]

中文:
定理 constantsVarsEquivLeft_apply
  条件: (t : L[[γ]].Term (α oplus β))
  证明: rfl

@[simp]
-/
theorem constantsVarsEquivLeft_apply (t : L[[γ]].Term (α oplus β)) :
    constantsVarsEquivLeft t = (constantsToVars t).relabel (Equiv.sumAssoc _ _ _).symm :=
  rfl

@[simp]
/--
theorem `constantsVarsEquivLeft_symm_apply` / 定理 `constantsVarsEquivLeft_symm_apply`

English:
theorem constantsVarsEquivLeft_symm_apply
  given: (t : L.Term ((γ oplus α) oplus β))
  proof: rfl

中文:
定理 constantsVarsEquivLeft_symm_apply
  条件: (t : L.Term ((γ oplus α) oplus β))
  证明: rfl
-/
theorem constantsVarsEquivLeft_symm_apply (t : L.Term ((γ oplus α) oplus β)) :
    constantsVarsEquivLeft.symm t = varsToConstants (t.relabel (Equiv.sumAssoc _ _ _)) :=
  rfl

/--
Instance `inhabitedOfVar` / 实例 `inhabitedOfVar`

English:
instance inhabitedOfVar
  signature: [Inhabited α]
  body: ⟨var default⟩

中文:
实例 inhabitedOfVar
  签名: [Inhabited α]
  定义体: ⟨var default⟩
-/
instance inhabitedOfVar [Inhabited α] : Inhabited (L.Term α) :=
  ⟨var default⟩

/--
Instance `inhabitedOfConstant` / 实例 `inhabitedOfConstant`

English:
instance inhabitedOfConstant
  signature: [Inhabited L.Constants]
  body: ⟨(default : L.Constants).term⟩

中文:
实例 inhabitedOfConstant
  签名: [Inhabited L.Constants]
  定义体: ⟨(default : L.Constants).term⟩

Depends on / 依赖: Constants, L.Constants
-/
instance inhabitedOfConstant [Inhabited L.Constants] : Inhabited (L.Term α) :=
  ⟨(default : L.Constants).term⟩

/--
Definition of `liftAt` / `liftAt` 的定义

English:
definition liftAt
  signature: {n : Nat} (n' m : Nat)
  body: relabel (Sum.map id fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n')

中文:
定义 liftAt
  签名: {n : 自然数} (n' m : 自然数)
  定义体: relabel (Sum.map id fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n')

Depends on / 依赖: Fin.addNat, Fin.castAdd, Sum.map, addNat, castAdd, relabel
-/
def liftAt {n : Nat} (n' m : Nat) : L.Term (α oplus (Fin n)) -> L.Term (α oplus (Fin (n + n'))) :=
  relabel (Sum.map id fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n')

/-- Substitutes the variables in a given term with terms. -/
@[simp]
/--
Definition of `subst` / `subst` 的定义

English:
definition subst
  signature: : L.Term α -> (α -> L.Term β) -> L.Term β

中文:
定义 subst
  签名: : L.Term α -> (α -> L.Term β) -> L.Term β
-/
def subst : L.Term α -> (α -> L.Term β) -> L.Term β
  | var a, tf => tf a
  | func f ts, tf => func f fun i => (ts i).subst tf

/-- Substitutes the functions in a given term with expressions. -/
@[simp]
/--
Definition of `substFunc` / `substFunc` 的定义

English:
definition substFunc
  signature: : L.Term α -> (forall {n : Nat}, L.Functions n -> L'.Term (Fin n)) -> L'.Term α

中文:
定义 substFunc
  签名: : L.Term α -> (对任意 {n : 自然数}, L.Functions n -> L'.Term (Fin n)) -> L'.Term α
-/
def substFunc : L.Term α -> (forall {n : Nat}, L.Functions n -> L'.Term (Fin n)) -> L'.Term α
  | var a, _ => var a
  | func f ts, tf => (tf f).subst fun i => (ts i).substFunc tf

@[simp]
/--
theorem `substFunc_term` / 定理 `substFunc_term`

English:
theorem substFunc_term
  given: (t : L.Term α)
  statement: t.substFunc Functions.term = t
  proof: by
  induction t
  · rfl
  · simp only [substFunc, Functions.term, subst, ‹forall _, _›]

中文:
定理 substFunc_term
  条件: (t : L.Term α)
  结论: t.substFunc Functions.term = t
  证明: by
  induction t
  · rfl
  · simp only [substFunc, Functions.term, subst, ‹forall _, _›]

Depends on / 依赖: Functions, Functions.term, substFunc
-/
theorem substFunc_term (t : L.Term α) : t.substFunc Functions.term = t := by
  induction t
  · rfl
  · simp only [substFunc, Functions.term, subst, ‹forall _, _›]

end Term

/-- `&n` is notation for the bound variable indexed by `n` in a bounded formula. -/
scoped[FirstOrder] prefix:arg "&" => FirstOrder.Language.Term.var ∘ Sum.inr

namespace LHom

open Term

/-- Maps a term's symbols along a language map. -/
@[simp]
/--
Definition of `onTerm` / `onTerm` 的定义

English:
definition onTerm
  signature: (φ : L ->ᴸ L')

中文:
定义 onTerm
  签名: (φ : L ->ᴸ L')
-/
def onTerm (φ : L ->ᴸ L') : L.Term α -> L'.Term α
  | var i => var i
  | func f ts => func (φ.onFunction f) fun i => onTerm φ (ts i)

@[simp]
/--
theorem `id_onTerm` / 定理 `id_onTerm`

English:
theorem id_onTerm
  statement: ((LHom.id L).onTerm : L.Term α -> L.Term α) = id
  proof: by
  ext t
  induction t with
  | var => rfl
  | func _ _ ih => simp_rw [onTerm, ih]; rfl

@[simp]

中文:
定理 id_onTerm
  结论: ((LHom.id L).onTerm : L.Term α -> L.Term α) = id
  证明: by
  ext t
  induction t with
  | var => rfl
  | func _ _ ih => simp_rw [onTerm, ih]; rfl

@[simp]

Depends on / 依赖: onTerm, simp_rw
-/
theorem id_onTerm : ((LHom.id L).onTerm : L.Term α -> L.Term α) = id := by
  ext t
  induction t with
  | var => rfl
  | func _ _ ih => simp_rw [onTerm, ih]; rfl

@[simp]
/--
theorem `comp_onTerm` / 定理 `comp_onTerm`

English:
theorem comp_onTerm
  given: {L'' : Language} (φ : L' ->ᴸ L'') (ψ : L ->ᴸ L')
  proof: by
  ext t
  induction t with
  | var => rfl
  | func _ _ ih => simp_rw [onTerm, ih]; rfl

中文:
定理 comp_onTerm
  条件: {L'' : Language} (φ : L' ->ᴸ L'') (ψ : L ->ᴸ L')
  证明: by
  ext t
  induction t with
  | var => rfl
  | func _ _ ih => simp_rw [onTerm, ih]; rfl

Depends on / 依赖: onTerm, simp_rw
-/
theorem comp_onTerm {L'' : Language} (φ : L' ->ᴸ L'') (ψ : L ->ᴸ L') :
    ((φ.comp ψ).onTerm : L.Term α -> L''.Term α) = φ.onTerm ∘ ψ.onTerm := by
  ext t
  induction t with
  | var => rfl
  | func _ _ ih => simp_rw [onTerm, ih]; rfl

end LHom

/-- Maps a term's symbols along a language equivalence. -/
@[simps]
/--
Definition of `LEquiv.onTerm` / `LEquiv.onTerm` 的定义

English:
definition LEquiv.onTerm
  signature: (φ : L ≃ᴸ L')
  body: φ.toLHom.onTerm
  invFun := φ.invLHom.onTerm
  left_inv := by
    rw [Function.leftInverse_iff_comp]; rw [← LHom.comp_onTerm]; rw [φ.left_inv]; rw [LHom.id_onTerm]
  right_inv := by
    rw [Function.rightInverse_iff_comp]; rw [← LHom.comp_onTerm]; rw [φ.right_inv]; rw [LHom.id_onTerm]

中文:
定义 LEquiv.onTerm
  签名: (φ : L ≃ᴸ L')
  定义体: φ.toLHom.onTerm
  invFun := φ.invLHom.onTerm
  left_inv := by
    rw [Function.leftInverse_iff_comp]; rw [← LHom.comp_onTerm]; rw [φ.left_inv]; rw [LHom.id_onTerm]
  right_inv := by
    rw [Function.rightInverse_iff_comp]; rw [← LHom.comp_onTerm]; rw [φ.right_inv]; rw [LHom.id_onTerm]

Depends on / 依赖: B.sets, onTerm, toLHom, toLHom.onTerm
-/
def LEquiv.onTerm (φ : L ≃ᴸ L') : L.Term α ≃ L'.Term α where
  toFun := φ.toLHom.onTerm
  invFun := φ.invLHom.onTerm
  left_inv := by
    rw [Function.leftInverse_iff_comp]; rw [← LHom.comp_onTerm]; rw [φ.left_inv]; rw [LHom.id_onTerm]
  right_inv := by
    rw [Function.rightInverse_iff_comp]; rw [← LHom.comp_onTerm]; rw [φ.right_inv]; rw [LHom.id_onTerm]

variable (L) (α)

/--
Inductive type `BoundedFormula` / 归纳类型 `BoundedFormula`

English:
inductive BoundedFormula
  parameters: : Nat -> Type max u v u'
  constructors (5):
    - falsum: {n} : BoundedFormula n
    - equal: {n} (t₁ t₂ : L.Term (α oplus (Fin n))) : BoundedFormula n
    - rel: {n l : Nat} (R : L.Relations l) (ts : Fin l -> L.Term (α oplus (Fin n))) : BoundedFormula n
    - imp: {n} (f₁ f₂ : BoundedFormula n) : BoundedFormula n
    - all: {n} (f : BoundedFormula (n + 1)) : BoundedFormula n

中文:
归纳类型 BoundedFormula
  参数: : 自然数 -> Type max u v u'
  构造子 (5 个):
    - falsum: {n} : BoundedFormula n
    - equal: {n} (t₁ t₂ : L.Term (α oplus (Fin n))) : BoundedFormula n
    - rel: {n l : 自然数} (R : L.Relations l) (ts : Fin l -> L.Term (α oplus (Fin n))) : BoundedFormula n
    - imp: {n} (f₁ f₂ : BoundedFormula n) : BoundedFormula n
    - all: {n} (f : BoundedFormula (n + 1)) : BoundedFormula n
-/
inductive BoundedFormula : Nat -> Type max u v u'
  | falsum {n} : BoundedFormula n
  | equal {n} (t₁ t₂ : L.Term (α oplus (Fin n))) : BoundedFormula n
  | rel {n l : Nat} (R : L.Relations l) (ts : Fin l -> L.Term (α oplus (Fin n))) : BoundedFormula n
  /-- The implication between two bounded formulas. -/
  | imp {n} (f₁ f₂ : BoundedFormula n) : BoundedFormula n
  /-- The universal quantifier over bounded formulas. -/
  | all {n} (f : BoundedFormula (n + 1)) : BoundedFormula n

/--
Definition of `Formula` / `Formula` 的定义

English:
abbreviation Formula
  body: L.BoundedFormula α 0

中文:
缩写 Formula
  定义体: L.BoundedFormula α 0

Depends on / 依赖: BoundedFormula, L.BoundedFormula
-/
abbrev Formula :=
  L.BoundedFormula α 0

/--
Definition of `Sentence` / `Sentence` 的定义

English:
abbreviation Sentence
  body: L.Formula Empty

中文:
缩写 Sentence
  定义体: L.Formula Empty

Depends on / 依赖: Formula, L.Formula
-/
abbrev Sentence :=
  L.Formula Empty

/--
Definition of `Theory` / `Theory` 的定义

English:
abbreviation Theory
  body: Set L.Sentence

中文:
缩写 Theory
  定义体: Set L.Sentence

Depends on / 依赖: L.Sentence, Sentence
-/
abbrev Theory :=
  Set L.Sentence

variable {L} {α} {n : Nat}

/--
Definition of `Relations.boundedFormula` / `Relations.boundedFormula` 的定义

English:
definition Relations.boundedFormula
  signature: {l : Nat} (R : L.Relations n) (ts : Fin n -> L.Term (α oplus (Fin l)))
  body: BoundedFormula.rel R ts

中文:
定义 Relations.boundedFormula
  签名: {l : 自然数} (R : L.Relations n) (ts : Fin n -> L.Term (α oplus (Fin l)))
  定义体: BoundedFormula.rel R ts

Depends on / 依赖: BoundedFormula, BoundedFormula.rel
-/
def Relations.boundedFormula {l : Nat} (R : L.Relations n) (ts : Fin n -> L.Term (α oplus (Fin l))) :
    L.BoundedFormula α l :=
  BoundedFormula.rel R ts

/--
Definition of `Relations.boundedFormula₁` / `Relations.boundedFormula₁` 的定义

English:
definition Relations.boundedFormula₁
  signature: (r : L.Relations 1) (t : L.Term (α oplus (Fin n)))
  body: r.boundedFormula ![t]

中文:
定义 Relations.boundedFormula₁
  签名: (r : L.Relations 1) (t : L.Term (α oplus (Fin n)))
  定义体: r.boundedFormula ![t]

Depends on / 依赖: boundedFormula, r.boundedFormula
-/
def Relations.boundedFormula₁ (r : L.Relations 1) (t : L.Term (α oplus (Fin n))) :
    L.BoundedFormula α n :=
  r.boundedFormula ![t]

/--
Definition of `Relations.boundedFormula₂` / `Relations.boundedFormula₂` 的定义

English:
definition Relations.boundedFormula₂
  signature: (r : L.Relations 2) (t₁ t₂ : L.Term (α oplus (Fin n)))
  body: r.boundedFormula ![t₁, t₂]

中文:
定义 Relations.boundedFormula₂
  签名: (r : L.Relations 2) (t₁ t₂ : L.Term (α oplus (Fin n)))
  定义体: r.boundedFormula ![t₁, t₂]

Depends on / 依赖: boundedFormula, r.boundedFormula
-/
def Relations.boundedFormula₂ (r : L.Relations 2) (t₁ t₂ : L.Term (α oplus (Fin n))) :
    L.BoundedFormula α n :=
  r.boundedFormula ![t₁, t₂]

/--
Definition of `Term.bdEqual` / `Term.bdEqual` 的定义

English:
definition Term.bdEqual
  signature: (t₁ t₂ : L.Term (α oplus (Fin n)))
  body: BoundedFormula.equal t₁ t₂

中文:
定义 Term.bdEqual
  签名: (t₁ t₂ : L.Term (α oplus (Fin n)))
  定义体: BoundedFormula.equal t₁ t₂

Depends on / 依赖: BoundedFormula, BoundedFormula.equal
-/
def Term.bdEqual (t₁ t₂ : L.Term (α oplus (Fin n))) : L.BoundedFormula α n :=
  BoundedFormula.equal t₁ t₂

/--
Definition of `Relations.formula` / `Relations.formula` 的定义

English:
definition Relations.formula
  signature: (R : L.Relations n) (ts : Fin n -> L.Term α)
  body: R.boundedFormula fun i => (ts i).relabel Sum.inl

中文:
定义 Relations.formula
  签名: (R : L.Relations n) (ts : Fin n -> L.Term α)
  定义体: R.boundedFormula fun i => (ts i).relabel Sum.inl

Depends on / 依赖: R.boundedFormula, Sum.inl, boundedFormula, relabel
-/
def Relations.formula (R : L.Relations n) (ts : Fin n -> L.Term α) : L.Formula α :=
  R.boundedFormula fun i => (ts i).relabel Sum.inl

/--
Definition of `Relations.formula₁` / `Relations.formula₁` 的定义

English:
definition Relations.formula₁
  signature: (r : L.Relations 1) (t : L.Term α)
  body: r.formula ![t]

中文:
定义 Relations.formula₁
  签名: (r : L.Relations 1) (t : L.Term α)
  定义体: r.formula ![t]

Depends on / 依赖: formula, r.formula
-/
def Relations.formula₁ (r : L.Relations 1) (t : L.Term α) : L.Formula α :=
  r.formula ![t]

/--
Definition of `Relations.formula₂` / `Relations.formula₂` 的定义

English:
definition Relations.formula₂
  signature: (r : L.Relations 2) (t₁ t₂ : L.Term α)
  body: r.formula ![t₁, t₂]

中文:
定义 Relations.formula₂
  签名: (r : L.Relations 2) (t₁ t₂ : L.Term α)
  定义体: r.formula ![t₁, t₂]

Depends on / 依赖: formula, r.formula
-/
def Relations.formula₂ (r : L.Relations 2) (t₁ t₂ : L.Term α) : L.Formula α :=
  r.formula ![t₁, t₂]

/--
Definition of `Term.equal` / `Term.equal` 的定义

English:
definition Term.equal
  signature: (t₁ t₂ : L.Term α)
  body: (t₁.relabel Sum.inl).bdEqual (t₂.relabel Sum.inl)

中文:
定义 Term.equal
  签名: (t₁ t₂ : L.Term α)
  定义体: (t₁.relabel Sum.inl).bdEqual (t₂.relabel Sum.inl)

Depends on / 依赖: Sum.inl, bdEqual, relabel
-/
def Term.equal (t₁ t₂ : L.Term α) : L.Formula α :=
  (t₁.relabel Sum.inl).bdEqual (t₂.relabel Sum.inl)

namespace BoundedFormula

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (L.BoundedFormula α n)
  body: ⟨falsum⟩

中文:
实例 :
  签名: Inhabited (L.BoundedFormula α n)
  定义体: ⟨falsum⟩

Depends on / 依赖: falsum
-/
instance : Inhabited (L.BoundedFormula α n) :=
  ⟨falsum⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (L.BoundedFormula α n)
  body: ⟨falsum⟩

中文:
实例 :
  签名: Bot (L.BoundedFormula α n)
  定义体: ⟨falsum⟩

Depends on / 依赖: falsum
-/
instance : Bot (L.BoundedFormula α n) :=
  ⟨falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[match_pattern]
/--
Definition of `not` / `not` 的定义

English:
definition not
  signature: (φ : L.BoundedFormula α n)
  body: φ.imp ⊥

中文:
定义 not
  签名: (φ : L.BoundedFormula α n)
  定义体: φ.imp ⊥
-/
protected def not (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
@[match_pattern]
/--
Definition of `ex` / `ex` 的定义

English:
definition ex
  signature: (φ : L.BoundedFormula α (n + 1))
  body: φ.not.all.not

中文:
定义 ex
  签名: (φ : L.BoundedFormula α (n + 1))
  定义体: φ.not.all.not
-/
protected def ex (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  φ.not.all.not

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (L.BoundedFormula α n)
  body: ⟨BoundedFormula.not ⊥⟩

中文:
实例 :
  签名: Top (L.BoundedFormula α n)
  定义体: ⟨BoundedFormula.not ⊥⟩

Depends on / 依赖: BoundedFormula, BoundedFormula.not
-/
instance : Top (L.BoundedFormula α n) :=
  ⟨BoundedFormula.not ⊥⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (L.BoundedFormula α n)
  body: ⟨fun f g => (f.imp g.not).not⟩

中文:
实例 :
  签名: Min (L.BoundedFormula α n)
  定义体: ⟨fun f g => (f.imp g.not).not⟩

Depends on / 依赖: f.imp, g.not
-/
instance : Min (L.BoundedFormula α n) :=
  ⟨fun f g => (f.imp g.not).not⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (L.BoundedFormula α n)
  body: ⟨fun f g => f.not.imp g⟩

中文:
实例 :
  签名: Max (L.BoundedFormula α n)
  定义体: ⟨fun f g => f.not.imp g⟩

Depends on / 依赖: f.not.imp
-/
instance : Max (L.BoundedFormula α n) :=
  ⟨fun f g => f.not.imp g⟩

/--
Definition of `iff` / `iff` 的定义

English:
definition iff
  signature: (φ ψ : L.BoundedFormula α n)
  body: φ.imp ψ ⊓ ψ.imp φ

中文:
定义 iff
  签名: (φ ψ : L.BoundedFormula α n)
  定义体: φ.imp ψ ⊓ ψ.imp φ
-/
protected def iff (φ ψ : L.BoundedFormula α n) :=
  φ.imp ψ ⊓ ψ.imp φ

open Finset

/-- The `Finset` of free variables used in a given formula. -/
@[simp]
/--
Definition of `freeVarFinset` / `freeVarFinset` 的定义

English:
definition freeVarFinset
  signature: [DecidableEq α]

中文:
定义 freeVarFinset
  签名: [DecidableEq α]
-/
def freeVarFinset [DecidableEq α] : forall {n}, L.BoundedFormula α n -> Finset α
  | _n, falsum => ∅
  | _n, equal t₁ t₂ => t₁.varFinsetLeft union t₂.varFinsetLeft
  | _n, rel _R ts => univ.biUnion fun i => (ts i).varFinsetLeft
  | _n, imp f₁ f₂ => f₁.freeVarFinset union f₂.freeVarFinset
  | _n, all f => f.freeVarFinset

/-- Casts `L.BoundedFormula α m` as `L.BoundedFormula α n`, where `m ≤ n`. -/
@[simp]
/--
Definition of `castLE` / `castLE` 的定义

English:
definition castLE
  signature: : forall {m n : Nat} (_h : m <= n), L.BoundedFormula α m -> L.BoundedFormula α n

中文:
定义 castLE
  签名: : 对任意 {m n : 自然数} (_h : m <= n), L.BoundedFormula α m -> L.BoundedFormula α n
-/
def castLE : forall {m n : Nat} (_h : m <= n), L.BoundedFormula α m -> L.BoundedFormula α n
  | _m, _n, _h, falsum => falsum
  | _m, _n, h, equal t₁ t₂ =>
    equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
  | _m, _n, h, rel R ts => rel R (Term.relabel (Sum.map id (Fin.castLE h)) ∘ ts)
  | _m, _n, h, imp f₁ f₂ => (f₁.castLE h).imp (f₂.castLE h)
  | _m, _n, h, all f => (f.castLE (by gcongr)).all

@[simp]
/--
theorem `castLE_rfl` / 定理 `castLE_rfl`

English:
theorem castLE_rfl
  given: {n} (h : n <= n) (φ : L.BoundedFormula α n)
  statement: φ.castLE h = φ
  proof: by
  induction φ with
  | falsum => rfl
  | equal => simp
  | rel => simp
  | imp _ _ ih1 ih2 => simp [ih1, ih2]
  | all _ ih3 => simp [ih3]

@[simp]

中文:
定理 castLE_rfl
  条件: {n} (h : n <= n) (φ : L.BoundedFormula α n)
  结论: φ.castLE h = φ
  证明: by
  induction φ with
  | falsum => rfl
  | equal => simp
  | rel => simp
  | imp _ _ ih1 ih2 => simp [ih1, ih2]
  | all _ ih3 => simp [ih3]

@[simp]

Depends on / 依赖: falsum
-/
theorem castLE_rfl {n} (h : n <= n) (φ : L.BoundedFormula α n) : φ.castLE h = φ := by
  induction φ with
  | falsum => rfl
  | equal => simp
  | rel => simp
  | imp _ _ ih1 ih2 => simp [ih1, ih2]
  | all _ ih3 => simp [ih3]

@[simp]
/--
theorem `castLE_castLE` / 定理 `castLE_castLE`

English:
theorem castLE_castLE
  given: {k m n} (km : k <= m) (mn : m <= n) (φ : L.BoundedFormula α k)
  proof: by
  revert m n
  induction φ with
  | falsum => intros; rfl
  | equal => simp
  | rel =>
    intros
    simp only [castLE]
    rw [← Function.comp_assoc]; rw [Term.relabel_comp_relabel]
    simp
  | imp _ _ ih1 ih2 => simp [ih1, ih2]
  | all _ ih3 => intros; simp only [castLE, ih3]

@[simp]

中文:
定理 castLE_castLE
  条件: {k m n} (km : k <= m) (mn : m <= n) (φ : L.BoundedFormula α k)
  证明: by
  revert m n
  induction φ with
  | falsum => intros; rfl
  | equal => simp
  | rel =>
    intros
    simp only [castLE]
    rw [← Function.comp_assoc]; rw [Term.relabel_comp_relabel]
    simp
  | imp _ _ ih1 ih2 => simp [ih1, ih2]
  | all _ ih3 => intros; simp only [castLE, ih3]

@[simp]

Depends on / 依赖: Function, Function.comp_assoc, Term.relabel_comp_relabel, castLE, comp_assoc, falsum, intros, relabel_comp_relabel, revert
-/
theorem castLE_castLE {k m n} (km : k <= m) (mn : m <= n) (φ : L.BoundedFormula α k) :
    (φ.castLE km).castLE mn = φ.castLE (km.trans mn) := by
  revert m n
  induction φ with
  | falsum => intros; rfl
  | equal => simp
  | rel =>
    intros
    simp only [castLE]
    rw [← Function.comp_assoc]; rw [Term.relabel_comp_relabel]
    simp
  | imp _ _ ih1 ih2 => simp [ih1, ih2]
  | all _ ih3 => intros; simp only [castLE, ih3]

@[simp]
/--
theorem `castLE_comp_castLE` / 定理 `castLE_comp_castLE`

English:
theorem castLE_comp_castLE
  given: {k m n} (km : k <= m) (mn : m <= n)
  proof: funext (castLE_castLE km mn)

中文:
定理 castLE_comp_castLE
  条件: {k m n} (km : k <= m) (mn : m <= n)
  证明: funext (castLE_castLE km mn)

Depends on / 依赖: castLE_castLE
-/
theorem castLE_comp_castLE {k m n} (km : k <= m) (mn : m <= n) :
    (BoundedFormula.castLE mn ∘ BoundedFormula.castLE km :
        L.BoundedFormula α k -> L.BoundedFormula α n) =
      BoundedFormula.castLE (km.trans mn) :=
  funext (castLE_castLE km mn)

/--
Definition of `restrictFreeVar` / `restrictFreeVar` 的定义

English:
definition restrictFreeVar
  signature: [DecidableEq α]

中文:
定义 restrictFreeVar
  签名: [DecidableEq α]
-/
def restrictFreeVar [DecidableEq α] :
    forall {n : Nat} (φ : L.BoundedFormula α n) (_f : φ.freeVarFinset -> β), L.BoundedFormula β n
  | _n, falsum, _f => falsum
  | _n, equal t₁ t₂, f =>
    equal (t₁.restrictVarLeft (f ∘ Set.inclusion subset_union_left))
      (t₂.restrictVarLeft (f ∘ Set.inclusion subset_union_right))
  | _n, rel R ts, f =>
    rel R fun i => (ts i).restrictVarLeft (f ∘ Set.inclusion
      (subset_biUnion_of_mem (fun i => Term.varFinsetLeft (ts i)) (mem_univ i)))
  | _n, imp φ₁ φ₂, f =>
    (φ₁.restrictFreeVar (f ∘ Set.inclusion subset_union_left)).imp
      (φ₂.restrictFreeVar (f ∘ Set.inclusion subset_union_right))
  | _n, all φ, f => (φ.restrictFreeVar f).all

/--
Definition of `alls` / `alls` 的定义

English:
definition alls
  signature: : forall {n}, L.BoundedFormula α n -> L.Formula α

中文:
定义 alls
  签名: : 对任意 {n}, L.BoundedFormula α n -> L.Formula α
-/
def alls : forall {n}, L.BoundedFormula α n -> L.Formula α
  | 0, φ => φ
  | _n + 1, φ => φ.all.alls

/--
Definition of `exs` / `exs` 的定义

English:
definition exs
  signature: : forall {n}, L.BoundedFormula α n -> L.Formula α

中文:
定义 exs
  签名: : 对任意 {n}, L.BoundedFormula α n -> L.Formula α
-/
def exs : forall {n}, L.BoundedFormula α n -> L.Formula α
  | 0, φ => φ
  | _n + 1, φ => φ.ex.exs

/--
Definition of `mapTermRel` / `mapTermRel` 的定义

English:
definition mapTermRel
  signature: {g : Nat -> Nat} (ft : forall n, L.Term (α oplus (Fin n)) -> L'.Term (β oplus (Fin (g n))))

中文:
定义 mapTermRel
  签名: {g : 自然数 -> 自然数} (ft : 对任意 n, L.Term (α oplus (Fin n)) -> L'.Term (β oplus (Fin (g n))))
-/
def mapTermRel {g : Nat -> Nat} (ft : forall n, L.Term (α oplus (Fin n)) -> L'.Term (β oplus (Fin (g n))))
    (fr : forall n, L.Relations n -> L'.Relations n)
    (h : forall n, L'.BoundedFormula β (g (n + 1)) -> L'.BoundedFormula β (g n + 1)) :
    forall {n}, L.BoundedFormula α n -> L'.BoundedFormula β (g n)
  | _n, falsum => falsum
  | _n, equal t₁ t₂ => equal (ft _ t₁) (ft _ t₂)
  | _n, rel R ts => rel (fr _ R) fun i => ft _ (ts i)
  | _n, imp φ₁ φ₂ => (φ₁.mapTermRel ft fr h).imp (φ₂.mapTermRel ft fr h)
  | n, all φ => (h n (φ.mapTermRel ft fr h)).all

/--
Definition of `liftAt` / `liftAt` 的定义

English:
definition liftAt
  signature: : forall {n : Nat} (n' _m : Nat), L.BoundedFormula α n -> L.BoundedFormula α (n + n')
  body: fun {_} n' m φ =>
  φ.mapTermRel (fun _ t => t.liftAt n' m) (fun _ => id) fun _ =>
    castLE (by rw [add_assoc, add_comm 1, add_assoc])

@[simp]

中文:
定义 liftAt
  签名: : 对任意 {n : 自然数} (n' _m : 自然数), L.BoundedFormula α n -> L.BoundedFormula α (n + n')
  定义体: fun {_} n' m φ =>
  φ.mapTermRel (fun _ t => t.liftAt n' m) (fun _ => id) fun _ =>
    castLE (by rw [add_assoc, add_comm 1, add_assoc])

@[simp]

Depends on / 依赖: add_assoc, add_comm, castLE, liftAt, mapTermRel, t.liftAt
-/
def liftAt : forall {n : Nat} (n' _m : Nat), L.BoundedFormula α n -> L.BoundedFormula α (n + n') :=
  fun {_} n' m φ =>
  φ.mapTermRel (fun _ t => t.liftAt n' m) (fun _ => id) fun _ =>
    castLE (by rw [add_assoc, add_comm 1, add_assoc])

@[simp]
/--
theorem `mapTermRel_mapTermRel` / 定理 `mapTermRel_mapTermRel`

English:
theorem mapTermRel_mapTermRel
  statement: {L'' : Language}
  proof: by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ ih3 => simp [mapTermRel, ih3]

@[simp]

中文:
定理 mapTermRel_mapTermRel
  结论: {L'' : Language}
  证明: by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ ih3 => simp [mapTermRel, ih3]

@[simp]

Depends on / 依赖: falsum, mapTermRel
-/
theorem mapTermRel_mapTermRel {L'' : Language}
    (ft : forall n, L.Term (α oplus (Fin n)) -> L'.Term (β oplus (Fin n)))
    (fr : forall n, L.Relations n -> L'.Relations n)
    (ft' : forall n, L'.Term (β oplus Fin n) -> L''.Term (γ oplus (Fin n)))
    (fr' : forall n, L'.Relations n -> L''.Relations n) {n} (φ : L.BoundedFormula α n) :
    ((φ.mapTermRel ft fr fun _ => id).mapTermRel ft' fr' fun _ => id) =
      φ.mapTermRel (fun _ => ft' _ ∘ ft _) (fun _ => fr' _ ∘ fr _) fun _ => id := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ ih3 => simp [mapTermRel, ih3]

@[simp]
/--
theorem `mapTermRel_id_id_id` / 定理 `mapTermRel_id_id_id`

English:
theorem mapTermRel_id_id_id
  given: {n} (φ : L.BoundedFormula α n)
  proof: by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ ih3 => simp [mapTermRel, ih3]

中文:
定理 mapTermRel_id_id_id
  条件: {n} (φ : L.BoundedFormula α n)
  证明: by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ ih3 => simp [mapTermRel, ih3]

Depends on / 依赖: falsum, mapTermRel
-/
theorem mapTermRel_id_id_id {n} (φ : L.BoundedFormula α n) :
    (φ.mapTermRel (fun _ => id) (fun _ => id) fun _ => id) = φ := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ ih3 => simp [mapTermRel, ih3]

/-- An equivalence of bounded formulas given by an equivalence of terms and an equivalence of
relations. -/
@[simps]
/--
Definition of `mapTermRelEquiv` / `mapTermRelEquiv` 的定义

English:
definition mapTermRelEquiv
  signature: (ft : forall n, L.Term (α oplus (Fin n)) ≃ L'.Term (β oplus (Fin n)))
  body: ⟨mapTermRel (fun n => ft n) (fun n => fr n) fun _ => id,
    mapTermRel (fun n => (ft n).symm) (fun n => (fr n).symm) fun _ => id, fun φ => by simp, fun φ =>
    by simp⟩

中文:
定义 mapTermRelEquiv
  签名: (ft : 对任意 n, L.Term (α oplus (Fin n)) ≃ L'.Term (β oplus (Fin n)))
  定义体: ⟨mapTermRel (fun n => ft n) (fun n => fr n) fun _ => id,
    mapTermRel (fun n => (ft n).symm) (fun n => (fr n).symm) fun _ => id, fun φ => by simp, fun φ =>
    by simp⟩

Depends on / 依赖: mapTermRel
-/
def mapTermRelEquiv (ft : forall n, L.Term (α oplus (Fin n)) ≃ L'.Term (β oplus (Fin n)))
    (fr : forall n, L.Relations n ≃ L'.Relations n) {n} : L.BoundedFormula α n ≃ L'.BoundedFormula β n :=
  ⟨mapTermRel (fun n => ft n) (fun n => fr n) fun _ => id,
    mapTermRel (fun n => (ft n).symm) (fun n => (fr n).symm) fun _ => id, fun φ => by simp, fun φ =>
    by simp⟩

/--
Definition of `relabelAux` / `relabelAux` 的定义

English:
definition relabelAux
  signature: (g : α -> β oplus (Fin n)) (k : Nat)
  body: Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id

@[simp]

中文:
定义 relabelAux
  签名: (g : α -> β oplus (Fin n)) (k : 自然数)
  定义体: Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id

@[simp]

Depends on / 依赖: Equiv.sumAssoc, Sum.map, finSumFinEquiv, sumAssoc
-/
def relabelAux (g : α -> β oplus (Fin n)) (k : Nat) : α oplus (Fin k) -> β oplus (Fin (n + k)) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id

@[simp]
/--
theorem `sumElim_comp_relabelAux` / 定理 `sumElim_comp_relabelAux`

English:
theorem sumElim_comp_relabelAux
  statement: {m : Nat} {g : α -> β oplus (Fin n)} {v : β -> M}
  proof: by
  ext x
  rcases x with x | x
  · simp only [BoundedFormula.relabelAux, Function.comp_apply, Sum.map_inl, Sum.elim_inl]
    rcases g x with l | r <;> simp
  · simp [BoundedFormula.relabelAux]

@[simp]

中文:
定理 sumElim_comp_relabelAux
  结论: {m : 自然数} {g : α -> β oplus (Fin n)} {v : β -> M}
  证明: by
  ext x
  rcases x with x | x
  · simp only [BoundedFormula.relabelAux, Function.comp_apply, Sum.map_inl, Sum.elim_inl]
    rcases g x with l | r <;> simp
  · simp [BoundedFormula.relabelAux]

@[simp]

Depends on / 依赖: BoundedFormula, BoundedFormula.relabelAux, Function, Function.comp_apply, Sum.elim_inl, Sum.map_inl, comp_apply, elim_inl, map_inl, relabelAux
-/
theorem sumElim_comp_relabelAux {m : Nat} {g : α -> β oplus (Fin n)} {v : β -> M}
    {xs : Fin (n + m) -> M} : Sum.elim v xs ∘ relabelAux g m =
    Sum.elim (Sum.elim v (xs ∘ castAdd m) ∘ g) (xs ∘ natAdd n) := by
  ext x
  rcases x with x | x
  · simp only [BoundedFormula.relabelAux, Function.comp_apply, Sum.map_inl, Sum.elim_inl]
    rcases g x with l | r <;> simp
  · simp [BoundedFormula.relabelAux]

@[simp]
/--
theorem `relabelAux_sumInl` / 定理 `relabelAux_sumInl`

English:
theorem relabelAux_sumInl
  given: (k : Nat)
  proof: by
  ext x
  cases x <;> · simp [relabelAux]

中文:
定理 relabelAux_sumInl
  条件: (k : 自然数)
  证明: by
  ext x
  cases x <;> · simp [relabelAux]

Depends on / 依赖: relabelAux
-/
theorem relabelAux_sumInl (k : Nat) :
    relabelAux (Sum.inl : α -> α oplus (Fin n)) k = Sum.map id (natAdd n) := by
  ext x
  cases x <;> · simp [relabelAux]

/--
Definition of `relabel` / `relabel` 的定义

English:
definition relabel
  signature: (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α k)
  body: φ.mapTermRel (fun _ t => t.relabel (relabelAux g _)) (fun _ => id) fun _ =>
    castLE (ge_of_eq (add_assoc _ _ _))

中文:
定义 relabel
  签名: (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α k)
  定义体: φ.mapTermRel (fun _ t => t.relabel (relabelAux g _)) (fun _ => id) fun _ =>
    castLE (ge_of_eq (add_assoc _ _ _))

Depends on / 依赖: add_assoc, castLE, ge_of_eq, mapTermRel, relabel, relabelAux, t.relabel
-/
def relabel (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α k) : L.BoundedFormula β (n + k) :=
  φ.mapTermRel (fun _ t => t.relabel (relabelAux g _)) (fun _ => id) fun _ =>
    castLE (ge_of_eq (add_assoc _ _ _))

/--
Definition of `relabelEquiv` / `relabelEquiv` 的定义

English:
definition relabelEquiv
  signature: (g : α ≃ β) {k}
  body: mapTermRelEquiv (fun _n => Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
    fun _n => _root_.Equiv.refl _

@[simp]

中文:
定义 relabelEquiv
  签名: (g : α ≃ β) {k}
  定义体: mapTermRelEquiv (fun _n => Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
    fun _n => _root_.Equiv.refl _

@[simp]

Depends on / 依赖: Term.relabelEquiv, _root_, _root_.Equiv.refl, g.sumCongr, mapTermRelEquiv, relabelEquiv, sumCongr
-/
def relabelEquiv (g : α ≃ β) {k} : L.BoundedFormula α k ≃ L.BoundedFormula β k :=
  mapTermRelEquiv (fun _n => Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
    fun _n => _root_.Equiv.refl _

@[simp]
/--
theorem `relabel_falsum` / 定理 `relabel_falsum`

English:
theorem relabel_falsum
  given: (g : α -> β oplus (Fin n)) {k}
  proof: rfl

@[simp]

中文:
定理 relabel_falsum
  条件: (g : α -> β oplus (Fin n)) {k}
  证明: rfl

@[simp]
-/
theorem relabel_falsum (g : α -> β oplus (Fin n)) {k} :
    (falsum : L.BoundedFormula α k).relabel g = falsum :=
  rfl

@[simp]
/--
theorem `relabel_bot` / 定理 `relabel_bot`

English:
theorem relabel_bot
  given: (g : α -> β oplus (Fin n)) {k}
  statement: (⊥ : L.BoundedFormula α k).relabel g = ⊥
  proof: rfl

@[simp]

中文:
定理 relabel_bot
  条件: (g : α -> β oplus (Fin n)) {k}
  结论: (⊥ : L.BoundedFormula α k).relabel g = ⊥
  证明: rfl

@[simp]
-/
theorem relabel_bot (g : α -> β oplus (Fin n)) {k} : (⊥ : L.BoundedFormula α k).relabel g = ⊥ :=
  rfl

@[simp]
/--
theorem `relabel_imp` / 定理 `relabel_imp`

English:
theorem relabel_imp
  given: (g : α -> β oplus (Fin n)) {k} (φ ψ : L.BoundedFormula α k)
  proof: rfl

@[simp]

中文:
定理 relabel_imp
  条件: (g : α -> β oplus (Fin n)) {k} (φ ψ : L.BoundedFormula α k)
  证明: rfl

@[simp]
-/
theorem relabel_imp (g : α -> β oplus (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ.imp ψ).relabel g = (φ.relabel g).imp (ψ.relabel g) :=
  rfl

@[simp]
/--
theorem `relabel_not` / 定理 `relabel_not`

English:
theorem relabel_not
  given: (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α k)
  proof: by simp [BoundedFormula.not]

@[simp]

中文:
定理 relabel_not
  条件: (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α k)
  证明: by simp [BoundedFormula.not]

@[simp]

Depends on / 依赖: BoundedFormula, BoundedFormula.not
-/
theorem relabel_not (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α k) :
    φ.not.relabel g = (φ.relabel g).not := by simp [BoundedFormula.not]

@[simp]
/--
theorem `relabel_all` / 定理 `relabel_all`

English:
theorem relabel_all
  given: (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α (k + 1))
  proof: by
  rw [relabel]; rw [mapTermRel]; rw [relabel]
  simp

@[simp]

中文:
定理 relabel_all
  条件: (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α (k + 1))
  证明: by
  rw [relabel]; rw [mapTermRel]; rw [relabel]
  simp

@[simp]

Depends on / 依赖: mapTermRel, relabel
-/
theorem relabel_all (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.all.relabel g = (φ.relabel g).all := by
  rw [relabel]; rw [mapTermRel]; rw [relabel]
  simp

@[simp]
/--
theorem `relabel_ex` / 定理 `relabel_ex`

English:
theorem relabel_ex
  given: (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α (k + 1))
  proof: by simp [BoundedFormula.ex]

@[simp]

中文:
定理 relabel_ex
  条件: (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α (k + 1))
  证明: by simp [BoundedFormula.ex]

@[simp]

Depends on / 依赖: BoundedFormula, BoundedFormula.ex
-/
theorem relabel_ex (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.ex.relabel g = (φ.relabel g).ex := by simp [BoundedFormula.ex]

@[simp]
/--
theorem `relabel_sumInl` / 定理 `relabel_sumInl`

English:
theorem relabel_sumInl
  given: (φ : L.BoundedFormula α n)
  proof: by
  simp only [relabel, relabelAux_sumInl]
  induction φ with
  | falsum => rfl
  | equal => simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]
  | rel => simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]; rfl
  | imp _ _ ih1 ih2 => simp_all [mapTermRel]
  | all _ ih3 => simp_all [mapTermRel]

中文:
定理 relabel_sumInl
  条件: (φ : L.BoundedFormula α n)
  证明: by
  simp only [relabel, relabelAux_sumInl]
  induction φ with
  | falsum => rfl
  | equal => simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]
  | rel => simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]; rfl
  | imp _ _ ih1 ih2 => simp_all [mapTermRel]
  | all _ ih3 => simp_all [mapTermRel]

Depends on / 依赖: Fin.natAdd_zero, castLE_of_eq, falsum, mapTermRel, natAdd_zero, relabel, relabelAux_sumInl
-/
theorem relabel_sumInl (φ : L.BoundedFormula α n) :
    (φ.relabel Sum.inl : L.BoundedFormula α (0 + n)) = φ.castLE (ge_of_eq (zero_add n)) := by
  simp only [relabel, relabelAux_sumInl]
  induction φ with
  | falsum => rfl
  | equal => simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]
  | rel => simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]; rfl
  | imp _ _ ih1 ih2 => simp_all [mapTermRel]
  | all _ ih3 => simp_all [mapTermRel]

/--
Definition of `subst` / `subst` 的定义

English:
definition subst
  signature: {n : Nat} (φ : L.BoundedFormula α n) (f : α -> L.Term β)
  body: φ.mapTermRel (fun _ t => t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr)))
    (fun _ => id) fun _ => id

中文:
定义 subst
  签名: {n : 自然数} (φ : L.BoundedFormula α n) (f : α -> L.Term β)
  定义体: φ.mapTermRel (fun _ t => t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr)))
    (fun _ => id) fun _ => id

Depends on / 依赖: Sum.elim, Sum.inl, Sum.inr, Term.relabel, mapTermRel, relabel, t.subst
-/
def subst {n : Nat} (φ : L.BoundedFormula α n) (f : α -> L.Term β) : L.BoundedFormula β n :=
  φ.mapTermRel (fun _ t => t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr)))
    (fun _ => id) fun _ => id

/--
Definition of `constantsVarsEquiv` / `constantsVarsEquiv` 的定义

English:
definition constantsVarsEquiv
  signature: : L[[γ]].BoundedFormula α n ≃ L.BoundedFormula (γ oplus α) n
  body: mapTermRelEquiv (fun _ => Term.constantsVarsEquivLeft) fun _ => Equiv.sumEmpty _ _

中文:
定义 constantsVarsEquiv
  签名: : L[[γ]].BoundedFormula α n ≃ L.BoundedFormula (γ oplus α) n
  定义体: mapTermRelEquiv (fun _ => Term.constantsVarsEquivLeft) fun _ => Equiv.sumEmpty _ _

Depends on / 依赖: Equiv.sumEmpty, Term.constantsVarsEquivLeft, constantsVarsEquivLeft, mapTermRelEquiv, sumEmpty
-/
def constantsVarsEquiv : L[[γ]].BoundedFormula α n ≃ L.BoundedFormula (γ oplus α) n :=
  mapTermRelEquiv (fun _ => Term.constantsVarsEquivLeft) fun _ => Equiv.sumEmpty _ _

/-- Turns all the in-scope bound variables into free variables. -/
@[simp]
/--
Definition of `toFormula` / `toFormula` 的定义

English:
definition toFormula
  signature: : forall {n : Nat}, L.BoundedFormula α n -> L.Formula (α oplus (Fin n))

中文:
定义 toFormula
  签名: : 对任意 {n : 自然数}, L.BoundedFormula α n -> L.Formula (α oplus (Fin n))
-/
def toFormula : forall {n : Nat}, L.BoundedFormula α n -> L.Formula (α oplus (Fin n))
  | _n, falsum => falsum
  | _n, equal t₁ t₂ => t₁.equal t₂
  | _n, rel R ts => R.formula ts
  | _n, imp φ₁ φ₂ => φ₁.toFormula.imp φ₂.toFormula
  | _n, all φ =>
    (φ.toFormula.relabel
        (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm))).all

/--
Definition of `iSup` / `iSup` 的定义

English:
definition iSup
  signature: [Finite β] (f : β -> L.BoundedFormula α n)
  body: let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊔ ·) ⊥

中文:
定义 iSup
  签名: [Finite β] (f : β -> L.BoundedFormula α n)
  定义体: let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊔ ·) ⊥

Depends on / 依赖: Finset, Finset.univ, Fintype, Fintype.ofFinite, ofFinite, toList, toList.map
-/
noncomputable def iSup [Finite β] (f : β -> L.BoundedFormula α n) : L.BoundedFormula α n :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊔ ·) ⊥

/--
Definition of `iInf` / `iInf` 的定义

English:
definition iInf
  signature: [Finite β] (f : β -> L.BoundedFormula α n)
  body: let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊓ ·) ⊤

中文:
定义 iInf
  签名: [Finite β] (f : β -> L.BoundedFormula α n)
  定义体: let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊓ ·) ⊤

Depends on / 依赖: Finset, Finset.univ, Fintype, Fintype.ofFinite, ofFinite, toList, toList.map
-/
noncomputable def iInf [Finite β] (f : β -> L.BoundedFormula α n) : L.BoundedFormula α n :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊓ ·) ⊤

end BoundedFormula

namespace LHom

open BoundedFormula

/-- Maps a bounded formula's symbols along a language map. -/
@[simp]
/--
Definition of `onBoundedFormula` / `onBoundedFormula` 的定义

English:
definition onBoundedFormula
  signature: (g : L ->ᴸ L')

中文:
定义 onBoundedFormula
  签名: (g : L ->ᴸ L')
-/
def onBoundedFormula (g : L ->ᴸ L') : forall {k : Nat}, L.BoundedFormula α k -> L'.BoundedFormula α k
  | _k, falsum => falsum
  | _k, equal t₁ t₂ => (g.onTerm t₁).bdEqual (g.onTerm t₂)
  | _k, rel R ts => (g.onRelation R).boundedFormula (g.onTerm ∘ ts)
  | _k, imp f₁ f₂ => (onBoundedFormula g f₁).imp (onBoundedFormula g f₂)
  | _k, all f => (onBoundedFormula g f).all

@[simp]
/--
theorem `id_onBoundedFormula` / 定理 `id_onBoundedFormula`

English:
theorem id_onBoundedFormula
  proof: by
  ext f
  induction f with
  | falsum => rfl
  | equal => rw [onBoundedFormula, LHom.id_onTerm, id, id, id, Term.bdEqual]
  | rel => rw [onBoundedFormula, LHom.id_onTerm]; rfl
  | imp _ _ ih1 ih2 => rw [onBoundedFormula, ih1, ih2, id, id, id]
  | all _ ih3 => rw [onBoundedFormula, ih3, id, id]

@

中文:
定理 id_onBoundedFormula
  证明: by
  ext f
  induction f with
  | falsum => rfl
  | equal => rw [onBoundedFormula, LHom.id_onTerm, id, id, id, Term.bdEqual]
  | rel => rw [onBoundedFormula, LHom.id_onTerm]; rfl
  | imp _ _ ih1 ih2 => rw [onBoundedFormula, ih1, ih2, id, id, id]
  | all _ ih3 => rw [onBoundedFormula, ih3, id, id]

@

Depends on / 依赖: LHom.id_onTerm, Term.bdEqual, bdEqual, falsum, id_onTerm, onBoundedFormula
-/
theorem id_onBoundedFormula :
    ((LHom.id L).onBoundedFormula : L.BoundedFormula α n -> L.BoundedFormula α n) = id := by
  ext f
  induction f with
  | falsum => rfl
  | equal => rw [onBoundedFormula, LHom.id_onTerm, id, id, id, Term.bdEqual]
  | rel => rw [onBoundedFormula, LHom.id_onTerm]; rfl
  | imp _ _ ih1 ih2 => rw [onBoundedFormula, ih1, ih2, id, id, id]
  | all _ ih3 => rw [onBoundedFormula, ih3, id, id]

@[simp]
/--
theorem `comp_onBoundedFormula` / 定理 `comp_onBoundedFormula`

English:
theorem comp_onBoundedFormula
  given: {L'' : Language} (φ : L' ->ᴸ L'') (ψ : L ->ᴸ L')
  proof: by
  ext f
  induction f with
  | falsum => rfl
  | equal => simp [Term.bdEqual]
  | rel => simp only [onBoundedFormula, comp_onRelation, comp_onTerm, Function.comp_apply]; rfl
  | imp _ _ ih1 ih2 =>
    simp only [onBoundedFormula, Function.comp_apply, ih1, ih2]
  | all _ ih3 => simp only [ih3, onB

中文:
定理 comp_onBoundedFormula
  条件: {L'' : Language} (φ : L' ->ᴸ L'') (ψ : L ->ᴸ L')
  证明: by
  ext f
  induction f with
  | falsum => rfl
  | equal => simp [Term.bdEqual]
  | rel => simp only [onBoundedFormula, comp_onRelation, comp_onTerm, Function.comp_apply]; rfl
  | imp _ _ ih1 ih2 =>
    simp only [onBoundedFormula, Function.comp_apply, ih1, ih2]
  | all _ ih3 => simp only [ih3, onB

Depends on / 依赖: Function, Function.comp_apply, Term.bdEqual, bdEqual, comp_apply, comp_onRelation, comp_onTerm, falsum, onBoundedFormula
-/
theorem comp_onBoundedFormula {L'' : Language} (φ : L' ->ᴸ L'') (ψ : L ->ᴸ L') :
    ((φ.comp ψ).onBoundedFormula : L.BoundedFormula α n -> L''.BoundedFormula α n) =
      φ.onBoundedFormula ∘ ψ.onBoundedFormula := by
  ext f
  induction f with
  | falsum => rfl
  | equal => simp [Term.bdEqual]
  | rel => simp only [onBoundedFormula, comp_onRelation, comp_onTerm, Function.comp_apply]; rfl
  | imp _ _ ih1 ih2 =>
    simp only [onBoundedFormula, Function.comp_apply, ih1, ih2]
  | all _ ih3 => simp only [ih3, onBoundedFormula, Function.comp_apply]

/--
Definition of `onFormula` / `onFormula` 的定义

English:
definition onFormula
  signature: (g : L ->ᴸ L')
  body: g.onBoundedFormula

中文:
定义 onFormula
  签名: (g : L ->ᴸ L')
  定义体: g.onBoundedFormula

Depends on / 依赖: g.onBoundedFormula, onBoundedFormula
-/
def onFormula (g : L ->ᴸ L') : L.Formula α -> L'.Formula α :=
  g.onBoundedFormula

/--
Definition of `onSentence` / `onSentence` 的定义

English:
definition onSentence
  signature: (g : L ->ᴸ L')
  body: g.onFormula

中文:
定义 onSentence
  签名: (g : L ->ᴸ L')
  定义体: g.onFormula

Depends on / 依赖: g.onFormula, onFormula
-/
def onSentence (g : L ->ᴸ L') : L.Sentence -> L'.Sentence :=
  g.onFormula

/--
Definition of `onTheory` / `onTheory` 的定义

English:
definition onTheory
  signature: (g : L ->ᴸ L') (T : L.Theory)
  body: g.onSentence '' T

@[simp]

中文:
定义 onTheory
  签名: (g : L ->ᴸ L') (T : L.Theory)
  定义体: g.onSentence '' T

@[simp]

Depends on / 依赖: g.onSentence, onSentence
-/
def onTheory (g : L ->ᴸ L') (T : L.Theory) : L'.Theory :=
  g.onSentence '' T

@[simp]
/--
theorem `mem_onTheory` / 定理 `mem_onTheory`

English:
theorem mem_onTheory
  given: {g : L ->ᴸ L'} {T : L.Theory} {φ : L'.Sentence}
  proof: Set.mem_image _ _ _

中文:
定理 mem_onTheory
  条件: {g : L ->ᴸ L'} {T : L.Theory} {φ : L'.Sentence}
  证明: Set.mem_image _ _ _

Depends on / 依赖: Set.mem_image, mem_image
-/
theorem mem_onTheory {g : L ->ᴸ L'} {T : L.Theory} {φ : L'.Sentence} :
    φ in g.onTheory T ↔ exists φ₀, φ₀ in T ∧ g.onSentence φ₀ = φ :=
  Set.mem_image _ _ _

end LHom

namespace LEquiv

/-- Maps a bounded formula's symbols along a language equivalence. -/
@[simps]
/--
Definition of `onBoundedFormula` / `onBoundedFormula` 的定义

English:
definition onBoundedFormula
  signature: (φ : L ≃ᴸ L')
  body: φ.toLHom.onBoundedFormula
  invFun := φ.invLHom.onBoundedFormula
  left_inv := by
    rw [Function.leftInverse_iff_comp]; rw [← LHom.comp_onBoundedFormula]; rw [φ.left_inv]; rw [LHom.id_onBoundedFormula]
  right_inv := by
    rw [Function.rightInverse_iff_comp]; rw [← LHom.comp_onBoundedFormula]; rw

中文:
定义 onBoundedFormula
  签名: (φ : L ≃ᴸ L')
  定义体: φ.toLHom.onBoundedFormula
  invFun := φ.invLHom.onBoundedFormula
  left_inv := by
    rw [Function.leftInverse_iff_comp]; rw [← LHom.comp_onBoundedFormula]; rw [φ.left_inv]; rw [LHom.id_onBoundedFormula]
  right_inv := by
    rw [Function.rightInverse_iff_comp]; rw [← LHom.comp_onBoundedFormula]; rw

Depends on / 依赖: onBoundedFormula, toLHom, toLHom.onBoundedFormula
-/
def onBoundedFormula (φ : L ≃ᴸ L') : L.BoundedFormula α n ≃ L'.BoundedFormula α n where
  toFun := φ.toLHom.onBoundedFormula
  invFun := φ.invLHom.onBoundedFormula
  left_inv := by
    rw [Function.leftInverse_iff_comp]; rw [← LHom.comp_onBoundedFormula]; rw [φ.left_inv]; rw [LHom.id_onBoundedFormula]
  right_inv := by
    rw [Function.rightInverse_iff_comp]; rw [← LHom.comp_onBoundedFormula]; rw [φ.right_inv]; rw [LHom.id_onBoundedFormula]

/--
theorem `onBoundedFormula_symm` / 定理 `onBoundedFormula_symm`

English:
theorem onBoundedFormula_symm
  given: (φ : L ≃ᴸ L')
  proof: rfl

中文:
定理 onBoundedFormula_symm
  条件: (φ : L ≃ᴸ L')
  证明: rfl
-/
theorem onBoundedFormula_symm (φ : L ≃ᴸ L') :
    (φ.onBoundedFormula.symm : L'.BoundedFormula α n ≃ L.BoundedFormula α n) =
      φ.symm.onBoundedFormula :=
  rfl

/--
Definition of `onFormula` / `onFormula` 的定义

English:
definition onFormula
  signature: (φ : L ≃ᴸ L')
  body: φ.onBoundedFormula

@[simp]

中文:
定义 onFormula
  签名: (φ : L ≃ᴸ L')
  定义体: φ.onBoundedFormula

@[simp]

Depends on / 依赖: onBoundedFormula
-/
def onFormula (φ : L ≃ᴸ L') : L.Formula α ≃ L'.Formula α :=
  φ.onBoundedFormula

@[simp]
/--
theorem `onFormula_apply` / 定理 `onFormula_apply`

English:
theorem onFormula_apply
  given: (φ : L ≃ᴸ L')
  proof: rfl

@[simp]

中文:
定理 onFormula_apply
  条件: (φ : L ≃ᴸ L')
  证明: rfl

@[simp]
-/
theorem onFormula_apply (φ : L ≃ᴸ L') :
    (φ.onFormula : L.Formula α -> L'.Formula α) = φ.toLHom.onFormula :=
  rfl

@[simp]
/--
theorem `onFormula_symm` / 定理 `onFormula_symm`

English:
theorem onFormula_symm
  given: (φ : L ≃ᴸ L')
  proof: rfl

中文:
定理 onFormula_symm
  条件: (φ : L ≃ᴸ L')
  证明: rfl
-/
theorem onFormula_symm (φ : L ≃ᴸ L') :
    (φ.onFormula.symm : L'.Formula α ≃ L.Formula α) = φ.symm.onFormula :=
  rfl

/-- Maps a sentence's symbols along a language equivalence. -/
@[simps!]
/--
Definition of `onSentence` / `onSentence` 的定义

English:
definition onSentence
  signature: (φ : L ≃ᴸ L')
  body: φ.onFormula

中文:
定义 onSentence
  签名: (φ : L ≃ᴸ L')
  定义体: φ.onFormula

Depends on / 依赖: onFormula
-/
def onSentence (φ : L ≃ᴸ L') : L.Sentence ≃ L'.Sentence :=
  φ.onFormula

end LEquiv

@[inherit_doc] scoped[FirstOrder] infixl:88 " =' " => FirstOrder.Language.Term.bdEqual
-- input \~- or \simeq

@[inherit_doc] scoped[FirstOrder] infixr:62 " ⟹ " => FirstOrder.Language.BoundedFormula.imp
-- input \==>

@[inherit_doc] scoped[FirstOrder] prefix:110 "forall' " => FirstOrder.Language.BoundedFormula.all

@[inherit_doc] scoped[FirstOrder] prefix:arg "∼" => FirstOrder.Language.BoundedFormula.not
-- input \~, the ASCII character ~ has too low precedence

@[inherit_doc] scoped[FirstOrder] infixl:61 " ⇔ " => FirstOrder.Language.BoundedFormula.iff
-- input \<=>

@[inherit_doc] scoped[FirstOrder] prefix:110 "exists' " => FirstOrder.Language.BoundedFormula.ex
-- input \ex

namespace Formula

/--
Definition of `relabel` / `relabel` 的定义

English:
definition relabel
  signature: (g : α -> β)
  body: @BoundedFormula.relabel _ _ _ 0 (Sum.inl ∘ g) 0

中文:
定义 relabel
  签名: (g : α -> β)
  定义体: @BoundedFormula.relabel _ _ _ 0 (Sum.inl ∘ g) 0

Depends on / 依赖: BoundedFormula, BoundedFormula.relabel, Sum.inl, relabel
-/
def relabel (g : α -> β) : L.Formula α -> L.Formula β :=
  @BoundedFormula.relabel _ _ _ 0 (Sum.inl ∘ g) 0

/--
Definition of `graph` / `graph` 的定义

English:
definition graph
  signature: (f : L.Functions n)
  body: Term.equal (var 0) (func f fun i => var i.succ)

中文:
定义 graph
  签名: (f : L.Functions n)
  定义体: Term.equal (var 0) (func f fun i => var i.succ)

Depends on / 依赖: Term.equal, i.succ
-/
def graph (f : L.Functions n) : L.Formula (Fin (n + 1)) :=
  Term.equal (var 0) (func f fun i => var i.succ)

/-- The negation of a formula. -/
protected nonrec abbrev not (φ : L.Formula α) : L.Formula α :=
  φ.not

/--
Definition of `imp` / `imp` 的定义

English:
abbreviation imp
  signature: : L.Formula α -> L.Formula α -> L.Formula α
  body: BoundedFormula.imp

中文:
缩写 imp
  签名: : L.Formula α -> L.Formula α -> L.Formula α
  定义体: BoundedFormula.imp
-/
protected abbrev imp : L.Formula α -> L.Formula α -> L.Formula α :=
  BoundedFormula.imp

variable (β) in
/--
Definition of `iAlls` / `iAlls` 的定义

English:
definition iAlls
  signature: [Finite β] (φ : L.Formula (α oplus β))
  body: let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).alls

中文:
定义 iAlls
  签名: [Finite β] (φ : L.Formula (α oplus β))
  定义体: let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).alls

Depends on / 依赖: BoundedFormula, BoundedFormula.relabel, Classical, Classical.choice, Classical.choose_spec, Finite, Finite.exists_equiv_fin, Sum.map, choice, choose_spec, exists_equiv_fin, relabel
-/
noncomputable def iAlls [Finite β] (φ : L.Formula (α oplus β)) : L.Formula α :=
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).alls

variable (β) in
/--
Definition of `iExs` / `iExs` 的定义

English:
definition iExs
  signature: [Finite β] (φ : L.Formula (α oplus β))
  body: let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).exs

中文:
定义 iExs
  签名: [Finite β] (φ : L.Formula (α oplus β))
  定义体: let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).exs

Depends on / 依赖: BoundedFormula, BoundedFormula.relabel, Classical, Classical.choice, Classical.choose_spec, Finite, Finite.exists_equiv_fin, Sum.map, choice, choose_spec, exists_equiv_fin, relabel
-/
noncomputable def iExs [Finite β] (φ : L.Formula (α oplus β)) : L.Formula α :=
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).exs

variable (β) in
/--
Definition of `iExsUnique` / `iExsUnique` 的定义

English:
definition iExsUnique
  signature: [Finite β] (φ : L.Formula (α oplus β))
  body: iExs β φ ⊓ iAlls β
    ((φ.relabel (fun a => Sum.elim (.inl ∘ .inl) .inr a)).imp <|
      .iInf fun g => Term.equal (var (.inr g)) (var (.inl (.inr g))))

中文:
定义 iExsUnique
  签名: [Finite β] (φ : L.Formula (α oplus β))
  定义体: iExs β φ ⊓ iAlls β
    ((φ.relabel (fun a => Sum.elim (.inl ∘ .inl) .inr a)).imp <|
      .iInf fun g => Term.equal (var (.inr g)) (var (.inl (.inr g))))

Depends on / 依赖: Sum.elim, Term.equal, relabel
-/
noncomputable def iExsUnique [Finite β] (φ : L.Formula (α oplus β)) : L.Formula α :=
iExs β φ ⊓ iAlls β
    ((φ.relabel (fun a => Sum.elim (.inl ∘ .inl) .inr a)).imp <|
      .iInf fun g => Term.equal (var (.inr g)) (var (.inl (.inr g))))

variable [DecidableEq α] in
/--
Definition of `exClosure` / `exClosure` 的定义

English:
definition exClosure
  signature: (φ : L.Formula α)
  body: iExs φ.freeVarFinset (Formula.relabel Sum.inr (φ.restrictFreeVar id))

中文:
定义 exClosure
  签名: (φ : L.Formula α)
  定义体: iExs φ.freeVarFinset (Formula.relabel Sum.inr (φ.restrictFreeVar id))

Depends on / 依赖: Formula, Formula.relabel, Sum.inr, freeVarFinset, relabel, restrictFreeVar
-/
noncomputable def exClosure (φ : L.Formula α) : L.Sentence :=
  iExs φ.freeVarFinset (Formula.relabel Sum.inr (φ.restrictFreeVar id))

/-- The biimplication between formulas, as a formula. -/
protected nonrec abbrev iff (φ ψ : L.Formula α) : L.Formula α :=
  φ.iff ψ

/--
Definition of `iSup` / `iSup` 的定义

English:
definition iSup
  signature: [Finite α] (f : α -> L.Formula β)
  body: BoundedFormula.iSup f

中文:
定义 iSup
  签名: [Finite α] (f : α -> L.Formula β)
  定义体: BoundedFormula.iSup f

Depends on / 依赖: BoundedFormula, BoundedFormula.iSup
-/
noncomputable def iSup [Finite α] (f : α -> L.Formula β) : L.Formula β :=
  BoundedFormula.iSup f

/--
Definition of `iInf` / `iInf` 的定义

English:
definition iInf
  signature: [Finite α] (f : α -> L.Formula β)
  body: BoundedFormula.iInf f

中文:
定义 iInf
  签名: [Finite α] (f : α -> L.Formula β)
  定义体: BoundedFormula.iInf f

Depends on / 依赖: BoundedFormula, BoundedFormula.iInf
-/
noncomputable def iInf [Finite α] (f : α -> L.Formula β) : L.Formula β :=
  BoundedFormula.iInf f

/--
Definition of `equivSentence` / `equivSentence` 的定义

English:
definition equivSentence
  signature: : L.Formula α ≃ L[[α]].Sentence
  body: (BoundedFormula.constantsVarsEquiv.trans (BoundedFormula.relabelEquiv (Equiv.sumEmpty _ _))).symm

中文:
定义 equivSentence
  签名: : L.Formula α ≃ L[[α]].Sentence
  定义体: (BoundedFormula.constantsVarsEquiv.trans (BoundedFormula.relabelEquiv (Equiv.sumEmpty _ _))).symm

Depends on / 依赖: BoundedFormula, BoundedFormula.constantsVarsEquiv.trans, BoundedFormula.relabelEquiv, Equiv.sumEmpty, constantsVarsEquiv, relabelEquiv, sumEmpty
-/
def equivSentence : L.Formula α ≃ L[[α]].Sentence :=
  (BoundedFormula.constantsVarsEquiv.trans (BoundedFormula.relabelEquiv (Equiv.sumEmpty _ _))).symm

/--
theorem `equivSentence_not` / 定理 `equivSentence_not`

English:
theorem equivSentence_not
  given: (φ : L.Formula α)
  statement: equivSentence φ.not = (equivSentence φ).not
  proof: rfl

中文:
定理 equivSentence_not
  条件: (φ : L.Formula α)
  结论: equivSentence φ.not = (equivSentence φ).not
  证明: rfl
-/
theorem equivSentence_not (φ : L.Formula α) : equivSentence φ.not = (equivSentence φ).not :=
  rfl

/--
theorem `equivSentence_inf` / 定理 `equivSentence_inf`

English:
theorem equivSentence_inf
  given: (φ ψ : L.Formula α)
  proof: rfl

中文:
定理 equivSentence_inf
  条件: (φ ψ : L.Formula α)
  证明: rfl
-/
theorem equivSentence_inf (φ ψ : L.Formula α) :
    equivSentence (φ ⊓ ψ) = equivSentence φ ⊓ equivSentence ψ :=
  rfl

end Formula

namespace Relations

variable (r : L.Relations 2)

/--
Definition of `reflexive` / `reflexive` 的定义

English:
definition reflexive
  signature: : L.Sentence
  body: forall' r.boundedFormula₂ (&0) &0

中文:
定义 reflexive
  签名: : L.Sentence
  定义体: forall' r.boundedFormula₂ (&0) &0
-/
protected def reflexive : L.Sentence :=
  forall' r.boundedFormula₂ (&0) &0

/--
Definition of `irreflexive` / `irreflexive` 的定义

English:
definition irreflexive
  signature: : L.Sentence
  body: forall' ∼(r.boundedFormula₂ (&0) &0)

中文:
定义 irreflexive
  签名: : L.Sentence
  定义体: forall' ∼(r.boundedFormula₂ (&0) &0)
-/
protected def irreflexive : L.Sentence :=
  forall' ∼(r.boundedFormula₂ (&0) &0)

/--
Definition of `symmetric` / `symmetric` 的定义

English:
definition symmetric
  signature: : L.Sentence
  body: forall' forall' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0)

中文:
定义 symmetric
  签名: : L.Sentence
  定义体: forall' forall' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0)
-/
protected def symmetric : L.Sentence :=
  forall' forall' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0)

/--
Definition of `antisymmetric` / `antisymmetric` 的定义

English:
definition antisymmetric
  signature: : L.Sentence
  body: forall' forall' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0 ⟹ Term.bdEqual (&0) &1)

中文:
定义 antisymmetric
  签名: : L.Sentence
  定义体: forall' forall' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0 ⟹ Term.bdEqual (&0) &1)
-/
protected def antisymmetric : L.Sentence :=
  forall' forall' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0 ⟹ Term.bdEqual (&0) &1)

/--
Definition of `transitive` / `transitive` 的定义

English:
definition transitive
  signature: : L.Sentence
  body: forall' forall' forall' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &2 ⟹ r.boundedFormula₂ (&0) &2)

中文:
定义 transitive
  签名: : L.Sentence
  定义体: forall' forall' forall' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &2 ⟹ r.boundedFormula₂ (&0) &2)
-/
protected def transitive : L.Sentence :=
  forall' forall' forall' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &2 ⟹ r.boundedFormula₂ (&0) &2)

/--
Definition of `total` / `total` 的定义

English:
definition total
  signature: : L.Sentence
  body: forall' forall' (r.boundedFormula₂ (&0) &1 ⊔ r.boundedFormula₂ (&1) &0)

中文:
定义 total
  签名: : L.Sentence
  定义体: forall' forall' (r.boundedFormula₂ (&0) &1 ⊔ r.boundedFormula₂ (&1) &0)
-/
protected def total : L.Sentence :=
  forall' forall' (r.boundedFormula₂ (&0) &1 ⊔ r.boundedFormula₂ (&1) &0)

end Relations

section Cardinality

variable (L)

/--
Definition of `Sentence.cardGe` / `Sentence.cardGe` 的定义

English:
definition Sentence.cardGe
  signature: (n : Nat)
  body: ((((List.finRange n ×ˢ List.finRange n).filter fun ij : _ × _ => ij.1 != ij.2).map
          fun ij : _ × _ => ∼((&ij.1).bdEqual &ij.2)).foldr
      (· ⊓ ·) ⊤).exs

中文:
定义 Sentence.cardGe
  签名: (n : 自然数)
  定义体: ((((List.finRange n ×ˢ List.finRange n).filter fun ij : _ × _ => ij.1 != ij.2).map
          fun ij : _ × _ => ∼((&ij.1).bdEqual &ij.2)).foldr
      (· ⊓ ·) ⊤).exs
-/
protected def Sentence.cardGe (n : Nat) : L.Sentence :=
  ((((List.finRange n ×ˢ List.finRange n).filter fun ij : _ × _ => ij.1 != ij.2).map
          fun ij : _ × _ => ∼((&ij.1).bdEqual &ij.2)).foldr
      (· ⊓ ·) ⊤).exs

/--
Definition of `infiniteTheory` / `infiniteTheory` 的定义

English:
definition infiniteTheory
  signature: : L.Theory
  body: Set.range (Sentence.cardGe L)

中文:
定义 infiniteTheory
  签名: : L.Theory
  定义体: Set.range (Sentence.cardGe L)

Depends on / 依赖: Sentence, Sentence.cardGe, Set.range, cardGe
-/
def infiniteTheory : L.Theory :=
  Set.range (Sentence.cardGe L)

/--
Definition of `nonemptyTheory` / `nonemptyTheory` 的定义

English:
definition nonemptyTheory
  signature: : L.Theory
  body: {Sentence.cardGe L 1}

中文:
定义 nonemptyTheory
  签名: : L.Theory
  定义体: {Sentence.cardGe L 1}

Depends on / 依赖: Sentence, Sentence.cardGe, cardGe
-/
def nonemptyTheory : L.Theory :=
  {Sentence.cardGe L 1}

/--
Definition of `distinctConstantsTheory` / `distinctConstantsTheory` 的定义

English:
definition distinctConstantsTheory
  signature: (s : Set α)
  body: (fun ab : α × α => ((L.con ab.1).term.equal (L.con ab.2).term).not) ''
  (s ×ˢ s inter (Set.diagonal α)ᶜ)

中文:
定义 distinctConstantsTheory
  签名: (s : Set α)
  定义体: (fun ab : α × α => ((L.con ab.1).term.equal (L.con ab.2).term).not) ''
  (s ×ˢ s inter (Set.diagonal α)ᶜ)

Depends on / 依赖: L.con, Set.diagonal, diagonal, term.equal
-/
def distinctConstantsTheory (s : Set α) : L[[α]].Theory :=
  (fun ab : α × α => ((L.con ab.1).term.equal (L.con ab.2).term).not) ''
  (s ×ˢ s inter (Set.diagonal α)ᶜ)

variable {L}

open Set

/--
theorem `distinctConstantsTheory_mono` / 定理 `distinctConstantsTheory_mono`

English:
theorem distinctConstantsTheory_mono
  given: {s t : Set α} (h : s subseteq t)
  proof: by
  unfold distinctConstantsTheory; gcongr

中文:
定理 distinctConstantsTheory_mono
  条件: {s t : Set α} (h : s subseteq t)
  证明: by
  unfold distinctConstantsTheory; gcongr

Depends on / 依赖: distinctConstantsTheory
-/
theorem distinctConstantsTheory_mono {s t : Set α} (h : s subseteq t) :
    L.distinctConstantsTheory s subseteq L.distinctConstantsTheory t := by
  unfold distinctConstantsTheory; gcongr

/--
theorem `monotone_distinctConstantsTheory` / 定理 `monotone_distinctConstantsTheory`

English:
theorem monotone_distinctConstantsTheory
  proof: fun _s _t st =>
  L.distinctConstantsTheory_mono st

中文:
定理 monotone_distinctConstantsTheory
  证明: fun _s _t st =>
  L.distinctConstantsTheory_mono st
-/
theorem monotone_distinctConstantsTheory :
    Monotone (L.distinctConstantsTheory : Set α -> L[[α]].Theory) := fun _s _t st =>
  L.distinctConstantsTheory_mono st

/--
theorem `directed_distinctConstantsTheory` / 定理 `directed_distinctConstantsTheory`

English:
theorem directed_distinctConstantsTheory
  proof: Monotone.directed_le monotone_distinctConstantsTheory

中文:
定理 directed_distinctConstantsTheory
  证明: Monotone.directed_le monotone_distinctConstantsTheory

Depends on / 依赖: Monotone, Monotone.directed_le, directed_le, monotone_distinctConstantsTheory
-/
theorem directed_distinctConstantsTheory :
    Directed (· subseteq ·) (L.distinctConstantsTheory : Set α -> L[[α]].Theory) :=
  Monotone.directed_le monotone_distinctConstantsTheory

/--
theorem `distinctConstantsTheory_eq_iUnion` / 定理 `distinctConstantsTheory_eq_iUnion`

English:
theorem distinctConstantsTheory_eq_iUnion
  given: (s : Set α)
  proof: by
  classical
    simp only [distinctConstantsTheory]
    rw [← image_iUnion]; rw [← iUnion_inter]
    refine congr(_ '' ($(?_) inter _))
    ext ⟨i, j⟩
    simp only [prodMk_mem_set_prod_eq, Finset.coe_map, Function.Embedding.coe_subtype, mem_iUnion,
      mem_image, Finset.mem_coe, Subtype.exists

中文:
定理 distinctConstantsTheory_eq_iUnion
  条件: (s : Set α)
  证明: by
  classical
    simp only [distinctConstantsTheory]
    rw [← image_iUnion]; rw [← iUnion_inter]
    refine congr(_ '' ($(?_) inter _))
    ext ⟨i, j⟩
    simp only [prodMk_mem_set_prod_eq, Finset.coe_map, Function.Embedding.coe_subtype, mem_iUnion,
      mem_image, Finset.mem_coe, Subtype.exists

Depends on / 依赖: Embedding, Finset, Finset.coe_map, Finset.mem_coe, Function, Function.Embedding.coe_subtype, Subtype, Subtype.exists, classical, coe_map, coe_subtype, distinctConstantsTheory, exists_and_right, exists_eq_right, iUnion_inter, image_iUnion, mem_coe, mem_iUnion, mem_image, prodMk_mem_set_prod_eq
-/
theorem distinctConstantsTheory_eq_iUnion (s : Set α) :
    L.distinctConstantsTheory s =
      ⋃ t : Finset s,
        L.distinctConstantsTheory (t.map (Function.Embedding.subtype fun x => x in s)) := by
  classical
    simp only [distinctConstantsTheory]
    rw [← image_iUnion]; rw [← iUnion_inter]
    refine congr(_ '' ($(?_) inter _))
    ext ⟨i, j⟩
    simp only [prodMk_mem_set_prod_eq, Finset.coe_map, Function.Embedding.coe_subtype, mem_iUnion,
      mem_image, Finset.mem_coe, Subtype.exists, exists_and_right, exists_eq_right]
    refine ⟨fun h => ⟨{⟨i, h.1⟩, ⟨j, h.2⟩}, ⟨h.1, ?_⟩, ⟨h.2, ?_⟩⟩, ?_⟩
    · simp
    · simp
    · rintro ⟨t, ⟨is, _⟩, ⟨js, _⟩⟩
      exact ⟨is, js⟩

end Cardinality

end Language

end FirstOrder
