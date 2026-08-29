/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.ModelTheory.Syntax
public import Mathlib.Data.List.ProdSigma

/-!
# Basics on First-Order Semantics

This file defines the interpretations of first-order terms, formulas, sentences, and theories
in a style inspired by the [Flypitch project](https://flypitch.github.io/).

## Main Definitions

- `FirstOrder.Language.Term.realize` is defined so that `t.realize v` is the term `t` evaluated at
  variables `v`.
- `FirstOrder.Language.BoundedFormula.Realize` is defined so that `φ.Realize v xs` is the bounded
  formula `φ` evaluated at tuples of variables `v` and `xs`.
- `FirstOrder.Language.Formula.Realize` is defined so that `φ.Realize v` is the formula `φ`
  evaluated at variables `v`.
- `FirstOrder.Language.Sentence.Realize` is defined so that `φ.Realize M` is the sentence `φ`
  evaluated in the structure `M`. Also denoted `M ⊨ φ`.
- `FirstOrder.Language.Theory.Model` is defined so that `T.Model M` is true if and only if every
  sentence of `T` is realized in `M`. Also denoted `T ⊨ φ`.

## Main Results

- Several results in this file show that syntactic constructions such as `relabel`, `castLE`,
  `liftAt`, `subst`, and the actions of language maps commute with realization of terms, formulas,
  sentences, and theories.

## Implementation Notes

- `BoundedFormula` uses a locally nameless representation with bound variables as well-scoped de
  Bruijn levels. See the implementation note in `Syntax.lean` for details.

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

variable {L : Language.{u, v}} {L' : Language}
variable {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variable {α : Type u'} {β : Type v'} {γ : Type*}

open FirstOrder Cardinal

open Structure Fin

namespace Term

/--
Definition of `realize` / `realize` 的定义

English:
definition realize
  signature: (v : α -> M)

中文:
定义 realize
  签名: (v : α -> M)
-/
def realize (v : α -> M) : forall _t : L.Term α, M
  | var k => v k
  | func f ts => funMap f fun i => (ts i).realize v

@[simp]
/--
theorem `realize_var` / 定理 `realize_var`

English:
theorem realize_var
  given: (v : α -> M) (k)
  statement: realize v (var k : L.Term α) = v k
  proof: rfl

@[simp]

中文:
定理 realize_var
  条件: (v : α -> M) (k)
  结论: realize v (var k : L.Term α) = v k
  证明: rfl

@[simp]
-/
theorem realize_var (v : α -> M) (k) : realize v (var k : L.Term α) = v k := rfl

@[simp]
/--
theorem `realize_func` / 定理 `realize_func`

English:
theorem realize_func
  given: (v : α -> M) {n} (f : L.Functions n) (ts)
  proof: rfl

@[simp]

中文:
定理 realize_func
  条件: (v : α -> M) {n} (f : L.Functions n) (ts)
  证明: rfl

@[simp]
-/
theorem realize_func (v : α -> M) {n} (f : L.Functions n) (ts) :
    realize v (func f ts : L.Term α) = funMap f fun i => (ts i).realize v := rfl

@[simp]
/--
theorem `realize_function_term` / 定理 `realize_function_term`

English:
theorem realize_function_term
  given: {n} (v : Fin n -> M) (f : L.Functions n)
  proof: by
  rfl

@[simp]

中文:
定理 realize_function_term
  条件: {n} (v : Fin n -> M) (f : L.Functions n)
  证明: by
  rfl

@[simp]
-/
theorem realize_function_term {n} (v : Fin n -> M) (f : L.Functions n) :
    f.term.realize v = funMap f v := by
  rfl

@[simp]
/--
theorem `realize_relabel` / 定理 `realize_relabel`

English:
theorem realize_relabel
  given: {t : L.Term α} {g : α -> β} {v : β -> M}
  proof: by
  induction t with
  | var => rfl
  | func f ts ih => simp [ih]

@[simp]

中文:
定理 realize_relabel
  条件: {t : L.Term α} {g : α -> β} {v : β -> M}
  证明: by
  induction t with
  | var => rfl
  | func f ts ih => simp [ih]

@[simp]
-/
theorem realize_relabel {t : L.Term α} {g : α -> β} {v : β -> M} :
    (t.relabel g).realize v = t.realize (v ∘ g) := by
  induction t with
  | var => rfl
  | func f ts ih => simp [ih]

@[simp]
/--
theorem `realize_liftAt` / 定理 `realize_liftAt`

English:
theorem realize_liftAt
  given: {n n' m : Nat} {t : L.Term (α oplus (Fin n))} {v : α oplus (Fin (n + n')) -> M}
  proof: realize_relabel

@[simp]

中文:
定理 realize_liftAt
  条件: {n n' m : 自然数} {t : L.Term (α oplus (Fin n))} {v : α oplus (Fin (n + n')) -> M}
  证明: realize_relabel

@[simp]

Depends on / 依赖: realize_relabel
-/
theorem realize_liftAt {n n' m : Nat} {t : L.Term (α oplus (Fin n))} {v : α oplus (Fin (n + n')) -> M} :
    (t.liftAt n' m).realize v =
      t.realize (v ∘ Sum.map id fun i : Fin _ =>
        if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') :=
  realize_relabel

@[simp]
/--
theorem `realize_constants` / 定理 `realize_constants`

English:
theorem realize_constants
  given: {c : L.Constants} {v : α -> M}
  statement: c.term.realize v = c
  proof: funMap_eq_coe_constants

@[simp]

中文:
定理 realize_constants
  条件: {c : L.Constants} {v : α -> M}
  结论: c.term.realize v = c
  证明: funMap_eq_coe_constants

@[simp]

Depends on / 依赖: funMap_eq_coe_constants
-/
theorem realize_constants {c : L.Constants} {v : α -> M} : c.term.realize v = c :=
  funMap_eq_coe_constants

@[simp]
/--
theorem `realize_functions_apply₁` / 定理 `realize_functions_apply₁`

English:
theorem realize_functions_apply₁
  given: {f : L.Functions 1} {t : L.Term α} {v : α -> M}
  proof: by
  rw [Functions.apply₁]; rw [Term.realize]
  refine congr rfl (funext fun i => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]

中文:
定理 realize_functions_apply₁
  条件: {f : L.Functions 1} {t : L.Term α} {v : α -> M}
  证明: by
  rw [Functions.apply₁]; rw [Term.realize]
  refine congr rfl (funext fun i => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]

Depends on / 依赖: Functions, Functions.apply, Matrix, Matrix.cons_val_fin_one, Term.realize, cons_val_fin_one, realize
-/
theorem realize_functions_apply₁ {f : L.Functions 1} {t : L.Term α} {v : α -> M} :
    (f.apply₁ t).realize v = funMap f ![t.realize v] := by
  rw [Functions.apply₁]; rw [Term.realize]
  refine congr rfl (funext fun i => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]
/--
theorem `realize_functions_apply₂` / 定理 `realize_functions_apply₂`

English:
theorem realize_functions_apply₂
  given: {f : L.Functions 2} {t₁ t₂ : L.Term α} {v : α -> M}
  proof: by
  rw [Functions.apply₂]; rw [Term.realize]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

中文:
定理 realize_functions_apply₂
  条件: {f : L.Functions 2} {t₁ t₂ : L.Term α} {v : α -> M}
  证明: by
  rw [Functions.apply₂]; rw [Term.realize]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

Depends on / 依赖: Fin.cases, Functions, Functions.apply, Matrix, Matrix.cons_val_fin_one, Matrix.cons_val_succ, Matrix.cons_val_zero, Term.realize, cons_val_fin_one, cons_val_succ, cons_val_zero, forall_const, realize
-/
theorem realize_functions_apply₂ {f : L.Functions 2} {t₁ t₂ : L.Term α} {v : α -> M} :
    (f.apply₂ t₁ t₂).realize v = funMap f ![t₁.realize v, t₂.realize v] := by
  rw [Functions.apply₂]; rw [Term.realize]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

/--
theorem `realize_con` / 定理 `realize_con`

English:
theorem realize_con
  given: {A : Set M} {a : A} {v : α -> M}
  statement: (L.con a).term.realize v = a
  proof: rfl

@[simp]

中文:
定理 realize_con
  条件: {A : Set M} {a : A} {v : α -> M}
  结论: (L.con a).term.realize v = a
  证明: rfl

@[simp]
-/
theorem realize_con {A : Set M} {a : A} {v : α -> M} : (L.con a).term.realize v = a :=
  rfl

@[simp]
/--
theorem `realize_subst` / 定理 `realize_subst`

English:
theorem realize_subst
  given: {t : L.Term α} {tf : α -> L.Term β} {v : β -> M}
  proof: by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

中文:
定理 realize_subst
  条件: {t : L.Term α} {tf : α -> L.Term β} {v : β -> M}
  证明: by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]
-/
theorem realize_subst {t : L.Term α} {tf : α -> L.Term β} {v : β -> M} :
    (t.subst tf).realize v = t.realize fun a => (tf a).realize v := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

/--
theorem `realize_substFunc` / 定理 `realize_substFunc`

English:
theorem realize_substFunc
  statement: [L'.Structure M] {c : {n : Nat} -> L.Functions n -> L'.Term (Fin n)}
  proof: by
  induction x with
  | var => simp
  | func f ts ih => simp [← ih, ← hc]

中文:
定理 realize_substFunc
  结论: [L'.Structure M] {c : {n : 自然数} -> L.Functions n -> L'.Term (Fin n)}
  证明: by
  induction x with
  | var => simp
  | func f ts ih => simp [← ih, ← hc]
-/
theorem realize_substFunc [L'.Structure M] {c : {n : Nat} -> L.Functions n -> L'.Term (Fin n)}
    (hc : forall {n : Nat} (g) (y : Fin n -> M), g.term.realize y = (c g).realize y)
    (v : β -> M) (x : L.Term β) :
    (x.substFunc c).realize v = x.realize v := by
  induction x with
  | var => simp
  | func f ts ih => simp [← ih, ← hc]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `realize_restrictVar` / 定理 `realize_restrictVar`

English:
theorem realize_restrictVar
  statement: [DecidableEq α] {t : L.Term α} {f : t.varFinset -> β}
  proof: by
  induction t with
  | var => simp [restrictVar, hv']
  | func _ _ ih =>
    exact congr rfl (funext fun i => ih i ((by simp [Function.comp_apply, hv'])))

中文:
定理 realize_restrictVar
  结论: [DecidableEq α] {t : L.Term α} {f : t.varFinset -> β}
  证明: by
  induction t with
  | var => simp [restrictVar, hv']
  | func _ _ ih =>
    exact congr rfl (funext fun i => ih i ((by simp [Function.comp_apply, hv'])))

Depends on / 依赖: Function, Function.comp_apply, comp_apply, restrictVar
-/
theorem realize_restrictVar [DecidableEq α] {t : L.Term α} {f : t.varFinset -> β}
    {v : β -> M} (v' : α -> M) (hv' : forall a, v (f a) = v' a) :
    (t.restrictVar f).realize v = t.realize v' := by
  induction t with
  | var => simp [restrictVar, hv']
  | func _ _ ih =>
    exact congr rfl (funext fun i => ih i ((by simp [Function.comp_apply, hv'])))

/-- A special case of `realize_restrictVar`, included because we can add the `simp` attribute
to it -/
@[simp]
/--
theorem `realize_restrictVar'` / 定理 `realize_restrictVar'`

English:
theorem realize_restrictVar'
  statement: [DecidableEq α] {t : L.Term α} {s : Set α} (h : ↑t.varFinset subseteq s)
  proof: realize_restrictVar _ (by simp)

中文:
定理 realize_restrictVar'
  结论: [DecidableEq α] {t : L.Term α} {s : Set α} (h : ↑t.varFinset subseteq s)
  证明: realize_restrictVar _ (by simp)

Depends on / 依赖: realize_restrictVar
-/
theorem realize_restrictVar' [DecidableEq α] {t : L.Term α} {s : Set α} (h : ↑t.varFinset subseteq s)
    {v : α -> M} : (t.restrictVar (Set.inclusion h)).realize (v ∘ (↑)) = t.realize v :=
  realize_restrictVar _ (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `realize_restrictVarLeft` / 定理 `realize_restrictVarLeft`

English:
theorem realize_restrictVarLeft
  statement: [DecidableEq α] {γ : Type*} {t : L.Term (α oplus γ)}
  proof: by
  induction t with
  | var a => cases a <;> simp [restrictVarLeft, hxs']
  | func _ _ ih =>
    exact congr rfl (funext fun i => ih i (by simp [hxs']))

中文:
定理 realize_restrictVarLeft
  结论: [DecidableEq α] {γ : 类型} {t : L.Term (α oplus γ)}
  证明: by
  induction t with
  | var a => cases a <;> simp [restrictVarLeft, hxs']
  | func _ _ ih =>
    exact congr rfl (funext fun i => ih i (by simp [hxs']))

Depends on / 依赖: restrictVarLeft
-/
theorem realize_restrictVarLeft [DecidableEq α] {γ : Type*} {t : L.Term (α oplus γ)}
    {f : t.varFinsetLeft -> β}
    {xs : β oplus γ -> M} (xs' : α -> M) (hxs' : forall a, xs (Sum.inl (f a)) = xs' a) :
    (t.restrictVarLeft f).realize xs = t.realize (Sum.elim xs' (xs ∘ Sum.inr)) := by
  induction t with
  | var a => cases a <;> simp [restrictVarLeft, hxs']
  | func _ _ ih =>
    exact congr rfl (funext fun i => ih i (by simp [hxs']))

/-- A special case of `realize_restrictVarLeft`, included because we can add the `simp` attribute
to it -/
@[simp]
/--
theorem `realize_restrictVarLeft'` / 定理 `realize_restrictVarLeft'`

English:
theorem realize_restrictVarLeft'
  statement: [DecidableEq α] {γ : Type*} {t : L.Term (α oplus γ)} {s : Set α}
  proof: realize_restrictVarLeft _ (by simp)

中文:
定理 realize_restrictVarLeft'
  结论: [DecidableEq α] {γ : 类型} {t : L.Term (α oplus γ)} {s : Set α}
  证明: realize_restrictVarLeft _ (by simp)

Depends on / 依赖: realize_restrictVarLeft
-/
theorem realize_restrictVarLeft' [DecidableEq α] {γ : Type*} {t : L.Term (α oplus γ)} {s : Set α}
    (h : ↑t.varFinsetLeft subseteq s) {v : α -> M} {xs : γ -> M} :
    (t.restrictVarLeft (Set.inclusion h)).realize (Sum.elim (v ∘ (↑)) xs) =
      t.realize (Sum.elim v xs) :=
  realize_restrictVarLeft _ (by simp)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `realize_constantsToVars` / 定理 `realize_constantsToVars`

English:
theorem realize_constantsToVars
  statement: [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
  proof: by
  induction t with
  | var => simp
  | @func n f ts ih =>
    cases n
    · cases f
      · simp only [realize, ih, constantsOn, constantsOnFunc, constantsToVars]
        -- Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sumInl]
      · simp onl

中文:
定理 realize_constantsToVars
  结论: [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
  证明: by
  induction t with
  | var => simp
  | @func n f ts ih =>
    cases n
    · cases f
      · simp only [realize, ih, constantsOn, constantsOnFunc, constantsToVars]
        -- Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sumInl]
      · simp onl

Depends on / 依赖: constantsOn, constantsOnFunc, constantsToVars, realize
-/
theorem realize_constantsToVars [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L[[α]].Term β} {v : β -> M} :
    t.constantsToVars.realize (Sum.elim (fun a => ↑(L.con a)) v) = t.realize v := by
  induction t with
  | var => simp
  | @func n f ts ih =>
    cases n
    · cases f
      · simp only [realize, ih, constantsOn, constantsOnFunc, constantsToVars]
        -- Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sumInl]
      · simp only [realize, constantsToVars, Sum.elim_inl, funMap_eq_coe_constants]
        rfl
    · obtain - | f := f
      · simp only [realize, ih, constantsOn, constantsOnFunc, constantsToVars]
        -- Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sumInl]
      · exact isEmptyElim f

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `realize_varsToConstants` / 定理 `realize_varsToConstants`

English:
theorem realize_varsToConstants
  statement: [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
  proof: by
  induction t with
  | var ab => rcases ab with a | b <;> simp [Language.con]
  | func f ts ih =>
    simp only [realize, constantsOn, constantsOnFunc, ih, varsToConstants]
    -- Porting note: below lemma does not work with simp for some reason
    rw [withConstants_funMap_sumInl]

中文:
定理 realize_varsToConstants
  结论: [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
  证明: by
  induction t with
  | var ab => rcases ab with a | b <;> simp [Language.con]
  | func f ts ih =>
    simp only [realize, constantsOn, constantsOnFunc, ih, varsToConstants]
    -- Porting note: below lemma does not work with simp for some reason
    rw [withConstants_funMap_sumInl]

Depends on / 依赖: Language, Language.con, constantsOn, constantsOnFunc, realize, varsToConstants
-/
theorem realize_varsToConstants [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L.Term (α oplus β)} {v : β -> M} :
    t.varsToConstants.realize v = t.realize (Sum.elim (fun a => ↑(L.con a)) v) := by
  induction t with
  | var ab => rcases ab with a | b <;> simp [Language.con]
  | func f ts ih =>
    simp only [realize, constantsOn, constantsOnFunc, ih, varsToConstants]
    -- Porting note: below lemma does not work with simp for some reason
    rw [withConstants_funMap_sumInl]

/--
theorem `realize_constantsVarsEquivLeft` / 定理 `realize_constantsVarsEquivLeft`

English:
theorem realize_constantsVarsEquivLeft
  statement: [L[[α]].Structure M]
  proof: by
  simp only [constantsVarsEquivLeft, realize_relabel, Equiv.coe_trans, Function.comp_apply,
    constantsVarsEquiv_apply, relabelEquiv_symm_apply]
  refine _root_.trans ?_ realize_constantsToVars
  congr 1; funext x -- Note: was previously rcongr x
  rcases x with (a | (b | i)) <;> simp

中文:
定理 realize_constantsVarsEquivLeft
  结论: [L[[α]].Structure M]
  证明: by
  simp only [constantsVarsEquivLeft, realize_relabel, Equiv.coe_trans, Function.comp_apply,
    constantsVarsEquiv_apply, relabelEquiv_symm_apply]
  refine _root_.trans ?_ realize_constantsToVars
  congr 1; funext x -- Note: was previously rcongr x
  rcases x with (a | (b | i)) <;> simp

Depends on / 依赖: Equiv.coe_trans, Function, Function.comp_apply, _root_, _root_.trans, coe_trans, comp_apply, constantsVarsEquivLeft, constantsVarsEquiv_apply, previously, rcongr, realize_constantsToVars, realize_relabel, relabelEquiv_symm_apply
-/
theorem realize_constantsVarsEquivLeft [L[[α]].Structure M]
    [(lhomWithConstants L α).IsExpansionOn M] {n} {t : L[[α]].Term (β oplus (Fin n))} {v : β -> M}
    {xs : Fin n -> M} :
    (constantsVarsEquivLeft t).realize (Sum.elim (Sum.elim (fun a => ↑(L.con a)) v) xs) =
      t.realize (Sum.elim v xs) := by
  simp only [constantsVarsEquivLeft, realize_relabel, Equiv.coe_trans, Function.comp_apply,
    constantsVarsEquiv_apply, relabelEquiv_symm_apply]
  refine _root_.trans ?_ realize_constantsToVars
  congr 1; funext x -- Note: was previously rcongr x
  rcases x with (a | (b | i)) <;> simp

end Term

namespace LHom

@[simp]
/--
theorem `realize_onTerm` / 定理 `realize_onTerm`

English:
theorem realize_onTerm
  statement: [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] (t : L.Term α)
  proof: by
  induction t with
  | var => rfl
  | func f ts ih => simp only [Term.realize, LHom.onTerm, LHom.map_onFunction, ih]

中文:
定理 realize_onTerm
  结论: [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] (t : L.Term α)
  证明: by
  induction t with
  | var => rfl
  | func f ts ih => simp only [Term.realize, LHom.onTerm, LHom.map_onFunction, ih]

Depends on / 依赖: LHom.map_onFunction, LHom.onTerm, Term.realize, map_onFunction, onTerm, realize
-/
theorem realize_onTerm [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] (t : L.Term α)
    (v : α -> M) : (φ.onTerm t).realize v = t.realize v := by
  induction t with
  | var => rfl
  | func f ts ih => simp only [Term.realize, LHom.onTerm, LHom.map_onFunction, ih]

end LHom

@[simp]
/--
theorem `HomClass.realize_term` / 定理 `HomClass.realize_term`

English:
theorem HomClass.realize_term
  statement: {F : Type*} [FunLike F M N] [HomClass L F M N]
  proof: by
  induction t
  · rfl
  · rw [Term.realize, Term.realize, HomClass.map_fun]
    refine congr rfl ?_
    ext x
    simp [*]

中文:
定理 HomClass.realize_term
  结论: {F : 类型} [FunLike F M N] [HomClass L F M N]
  证明: by
  induction t
  · rfl
  · rw [Term.realize, Term.realize, HomClass.map_fun]
    refine congr rfl ?_
    ext x
    simp [*]

Depends on / 依赖: HomClass, HomClass.map_fun, Term.realize, map_fun, realize
-/
theorem HomClass.realize_term {F : Type*} [FunLike F M N] [HomClass L F M N]
    (g : F) {t : L.Term α} {v : α -> M} :
    t.realize (g ∘ v) = g (t.realize v) := by
  induction t
  · rfl
  · rw [Term.realize, Term.realize, HomClass.map_fun]
    refine congr rfl ?_
    ext x
    simp [*]

variable {n : Nat}

namespace BoundedFormula

open Term

/--
Definition of `Realize` / `Realize` 的定义

English:
definition Realize
  signature: : forall {l} (_f : L.BoundedFormula α l) (_v : α -> M) (_xs : Fin l -> M), Prop

中文:
定义 Realize
  签名: : 对任意 {l} (_f : L.BoundedFormula α l) (_v : α -> M) (_xs : Fin l -> M), 命题

Depends on / 依赖: atTop_isCountablyGenerated_of_archimedean
-/
def Realize : forall {l} (_f : L.BoundedFormula α l) (_v : α -> M) (_xs : Fin l -> M), Prop
  | _, falsum, _v, _xs => False
  | _, equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, rel R ts, v, xs => RelMap R fun i => (ts i).realize (Sum.elim v xs)
  | _, imp f₁ f₂, v, xs => Realize f₁ v xs -> Realize f₂ v xs
  | _, all f, v, xs => forall x : M, Realize f v (snoc xs x)

variable {l : Nat} {φ ψ : L.BoundedFormula α l} {θ : L.BoundedFormula α l.succ}
variable {v : α -> M} {xs : Fin l -> M}

@[simp]
/--
theorem `realize_bot` / 定理 `realize_bot`

English:
theorem realize_bot
  statement: (⊥ : L.BoundedFormula α l).Realize v xs ↔ False
  proof: Iff.rfl

@[simp]

中文:
定理 realize_bot
  结论: (⊥ : L.BoundedFormula α l).实数ize v xs ↔ False
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl, atBot_isCountablyGenerated_of_archimedean
-/
theorem realize_bot : (⊥ : L.BoundedFormula α l).Realize v xs ↔ False :=
  Iff.rfl

@[simp]
/--
theorem `realize_not` / 定理 `realize_not`

English:
theorem realize_not
  statement: φ.not.Realize v xs ↔ ¬φ.Realize v xs
  proof: Iff.rfl

@[simp]

中文:
定理 realize_not
  结论: φ.not.实数ize v xs ↔ ¬φ.实数ize v xs
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem realize_not : φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  Iff.rfl

@[simp]
/--
theorem `realize_bdEqual` / 定理 `realize_bdEqual`

English:
theorem realize_bdEqual
  given: (t₁ t₂ : L.Term (α oplus (Fin l)))
  proof: Iff.rfl

@[simp]

中文:
定理 realize_bdEqual
  条件: (t₁ t₂ : L.Term (α oplus (Fin l)))
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem realize_bdEqual (t₁ t₂ : L.Term (α oplus (Fin l))) :
    (t₁.bdEqual t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
/--
theorem `realize_top` / 定理 `realize_top`

English:
theorem realize_top
  statement: (⊤ : L.BoundedFormula α l).Realize v xs ↔ True
  proof: by simp [Top.top]

@[simp]

中文:
定理 realize_top
  结论: (⊤ : L.BoundedFormula α l).实数ize v xs ↔ True
  证明: by simp [Top.top]

@[simp]

Depends on / 依赖: Top.top
-/
theorem realize_top : (⊤ : L.BoundedFormula α l).Realize v xs ↔ True := by simp [Top.top]

@[simp]
/--
theorem `realize_inf` / 定理 `realize_inf`

English:
theorem realize_inf
  statement: (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs
  proof: by
  simp [Realize, Min.min]

@[simp]

中文:
定理 realize_inf
  结论: (φ ⊓ ψ).实数ize v xs ↔ φ.实数ize v xs ∧ ψ.实数ize v xs
  证明: by
  simp [Realize, Min.min]

@[simp]

Depends on / 依赖: Min.min, Realize
-/
theorem realize_inf : (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp [Realize, Min.min]

@[simp]
/--
theorem `realize_foldr_inf` / 定理 `realize_foldr_inf`

English:
theorem realize_foldr_inf
  given: (l : List (L.BoundedFormula α n)) (v : α -> M) (xs : Fin n -> M)
  proof: by
  induction l with
  | nil => simp
  | cons φ l ih => simp [ih]

@[simp]

中文:
定理 realize_foldr_inf
  条件: (l : List (L.BoundedFormula α n)) (v : α -> M) (xs : Fin n -> M)
  证明: by
  induction l with
  | nil => simp
  | cons φ l ih => simp [ih]

@[simp]
-/
theorem realize_foldr_inf (l : List (L.BoundedFormula α n)) (v : α -> M) (xs : Fin n -> M) :
    (l.foldr (· ⊓ ·) ⊤).Realize v xs ↔ forall φ in l, BoundedFormula.Realize φ v xs := by
  induction l with
  | nil => simp
  | cons φ l ih => simp [ih]

@[simp]
/--
theorem `realize_imp` / 定理 `realize_imp`

English:
theorem realize_imp
  statement: (φ.imp ψ).Realize v xs ↔ φ.Realize v xs -> ψ.Realize v xs
  proof: by
  simp only [Realize]

中文:
定理 realize_imp
  结论: (φ.imp ψ).实数ize v xs ↔ φ.实数ize v xs -> ψ.实数ize v xs
  证明: by
  simp only [Realize]

Depends on / 依赖: Realize
-/
theorem realize_imp : (φ.imp ψ).Realize v xs ↔ φ.Realize v xs -> ψ.Realize v xs := by
  simp only [Realize]

/--
theorem `realize_foldr_imp` / 定理 `realize_foldr_imp`

English:
theorem realize_foldr_imp
  statement: {k : Nat} (l : List (L.BoundedFormula α k))
  proof: by
  intro v xs
  induction l
  next => simp
  next f' _ _ => by_cases f'.Realize v xs <;> simp [*]

@[simp]

中文:
定理 realize_foldr_imp
  结论: {k : 自然数} (l : List (L.BoundedFormula α k))
  证明: by
  intro v xs
  induction l
  next => simp
  next f' _ _ => by_cases f'.Realize v xs <;> simp [*]

@[simp]

Depends on / 依赖: Realize
-/
theorem realize_foldr_imp {k : Nat} (l : List (L.BoundedFormula α k))
    (f : L.BoundedFormula α k) :
    forall (v : α -> M) xs,
      (l.foldr BoundedFormula.imp f).Realize v xs =
      ((forall i in l, i.Realize v xs) -> f.Realize v xs) := by
  intro v xs
  induction l
  next => simp
  next f' _ _ => by_cases f'.Realize v xs <;> simp [*]

@[simp]
/--
theorem `realize_rel` / 定理 `realize_rel`

English:
theorem realize_rel
  given: {k : Nat} {R : L.Relations k} {ts : Fin k -> L.Term _}
  proof: Iff.rfl

@[simp]

中文:
定理 realize_rel
  条件: {k : 自然数} {R : L.Relations k} {ts : Fin k -> L.Term _}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem realize_rel {k : Nat} {R : L.Relations k} {ts : Fin k -> L.Term _} :
    (R.boundedFormula ts).Realize v xs ↔ RelMap R fun i => (ts i).realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
/--
theorem `realize_rel₁` / 定理 `realize_rel₁`

English:
theorem realize_rel₁
  given: {R : L.Relations 1} {t : L.Term _}
  proof: by
  rw [Relations.boundedFormula₁]; rw [realize_rel]; rw [iff_eq_eq]
  refine congr rfl (funext fun _ => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]

中文:
定理 realize_rel₁
  条件: {R : L.Relations 1} {t : L.Term _}
  证明: by
  rw [Relations.boundedFormula₁]; rw [realize_rel]; rw [iff_eq_eq]
  refine congr rfl (funext fun _ => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]

Depends on / 依赖: Matrix, Matrix.cons_val_fin_one, Relations, Relations.boundedFormula, cons_val_fin_one, iff_eq_eq, realize_rel
-/
theorem realize_rel₁ {R : L.Relations 1} {t : L.Term _} :
    (R.boundedFormula₁ t).Realize v xs ↔ RelMap R ![t.realize (Sum.elim v xs)] := by
  rw [Relations.boundedFormula₁]; rw [realize_rel]; rw [iff_eq_eq]
  refine congr rfl (funext fun _ => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]
/--
theorem `realize_rel₂` / 定理 `realize_rel₂`

English:
theorem realize_rel₂
  given: {R : L.Relations 2} {t₁ t₂ : L.Term _}
  proof: by
  rw [Relations.boundedFormula₂]; rw [realize_rel]; rw [iff_eq_eq]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

@[simp]

中文:
定理 realize_rel₂
  条件: {R : L.Relations 2} {t₁ t₂ : L.Term _}
  证明: by
  rw [Relations.boundedFormula₂]; rw [realize_rel]; rw [iff_eq_eq]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

@[simp]

Depends on / 依赖: Fin.cases, Matrix, Matrix.cons_val_fin_one, Matrix.cons_val_succ, Matrix.cons_val_zero, Relations, Relations.boundedFormula, cons_val_fin_one, cons_val_succ, cons_val_zero, forall_const, iff_eq_eq, realize_rel
-/
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
    (R.boundedFormula₂ t₁ t₂).Realize v xs ↔
      RelMap R ![t₁.realize (Sum.elim v xs), t₂.realize (Sum.elim v xs)] := by
  rw [Relations.boundedFormula₂]; rw [realize_rel]; rw [iff_eq_eq]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

@[simp]
/--
theorem `realize_sup` / 定理 `realize_sup`

English:
theorem realize_sup
  statement: (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs
  proof: by
  simp only [max]
  tauto

@[simp]

中文:
定理 realize_sup
  结论: (φ ⊔ ψ).实数ize v xs ↔ φ.实数ize v xs ∨ ψ.实数ize v xs
  证明: by
  simp only [max]
  tauto

@[simp]
-/
theorem realize_sup : (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  simp only [max]
  tauto

@[simp]
/--
theorem `realize_foldr_sup` / 定理 `realize_foldr_sup`

English:
theorem realize_foldr_sup
  given: (l : List (L.BoundedFormula α n)) (v : α -> M) (xs : Fin n -> M)
  proof: by
  induction l with
  | nil => simp
  | cons φ l ih =>
    simp_rw [List.foldr_cons, realize_sup, ih, List.mem_cons, or_and_right, exists_or,
      exists_eq_left]

@[simp]

中文:
定理 realize_foldr_sup
  条件: (l : List (L.BoundedFormula α n)) (v : α -> M) (xs : Fin n -> M)
  证明: by
  induction l with
  | nil => simp
  | cons φ l ih =>
    simp_rw [List.foldr_cons, realize_sup, ih, List.mem_cons, or_and_right, exists_or,
      exists_eq_left]

@[simp]

Depends on / 依赖: List.foldr_cons, List.mem_cons, exists_eq_left, exists_or, foldr_cons, mem_cons, or_and_right, realize_sup, simp_rw
-/
theorem realize_foldr_sup (l : List (L.BoundedFormula α n)) (v : α -> M) (xs : Fin n -> M) :
    (l.foldr (· ⊔ ·) ⊥).Realize v xs ↔ exists φ in l, BoundedFormula.Realize φ v xs := by
  induction l with
  | nil => simp
  | cons φ l ih =>
    simp_rw [List.foldr_cons, realize_sup, ih, List.mem_cons, or_and_right, exists_or,
      exists_eq_left]

@[simp]
/--
theorem `realize_all` / 定理 `realize_all`

English:
theorem realize_all
  statement: (all θ).Realize v xs ↔ forall a : M, θ.Realize v (Fin.snoc xs a)
  proof: Iff.rfl

@[simp]

中文:
定理 realize_all
  结论: (all θ).实数ize v xs ↔ 对任意 a : M, θ.实数ize v (Fin.snoc xs a)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem realize_all : (all θ).Realize v xs ↔ forall a : M, θ.Realize v (Fin.snoc xs a) :=
  Iff.rfl

@[simp]
/--
theorem `realize_ex` / 定理 `realize_ex`

English:
theorem realize_ex
  statement: θ.ex.Realize v xs ↔ exists a : M, θ.Realize v (Fin.snoc xs a)
  proof: by
  rw [BoundedFormula.ex]; rw [realize_not]; rw [realize_all]; rw [not_forall]
  simp_rw [realize_not, Classical.not_not]

@[simp]

中文:
定理 realize_ex
  结论: θ.ex.实数ize v xs ↔ 存在 a : M, θ.实数ize v (Fin.snoc xs a)
  证明: by
  rw [BoundedFormula.ex]; rw [realize_not]; rw [realize_all]; rw [not_forall]
  simp_rw [realize_not, Classical.not_not]

@[simp]

Depends on / 依赖: BoundedFormula, BoundedFormula.ex, Classical, Classical.not_not, not_forall, not_not, realize_all, realize_not, simp_rw
-/
theorem realize_ex : θ.ex.Realize v xs ↔ exists a : M, θ.Realize v (Fin.snoc xs a) := by
  rw [BoundedFormula.ex]; rw [realize_not]; rw [realize_all]; rw [not_forall]
  simp_rw [realize_not, Classical.not_not]

@[simp]
/--
theorem `realize_iff` / 定理 `realize_iff`

English:
theorem realize_iff
  statement: (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs)
  proof: by
  simp only [BoundedFormula.iff, realize_inf, realize_imp, ← iff_def]

中文:
定理 realize_iff
  结论: (φ.iff ψ).实数ize v xs ↔ (φ.实数ize v xs ↔ ψ.实数ize v xs)
  证明: by
  simp only [BoundedFormula.iff, realize_inf, realize_imp, ← iff_def]

Depends on / 依赖: BoundedFormula, BoundedFormula.iff, iff_def, realize_imp, realize_inf
-/
theorem realize_iff : (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs) := by
  simp only [BoundedFormula.iff, realize_inf, realize_imp, ← iff_def]

/--
theorem `realize_castLE_of_eq` / 定理 `realize_castLE_of_eq`

English:
theorem realize_castLE_of_eq
  statement: {m n : Nat} (h : m = n) {h' : m <= n} {φ : L.BoundedFormula α m}
  proof: by
  subst h
  simp only [castLE_rfl, cast_refl, Function.comp_id]

中文:
定理 realize_castLE_of_eq
  结论: {m n : 自然数} (h : m = n) {h' : m <= n} {φ : L.BoundedFormula α m}
  证明: by
  subst h
  simp only [castLE_rfl, cast_refl, Function.comp_id]

Depends on / 依赖: Function, Function.comp_id, castLE_rfl, cast_refl, comp_id
-/
theorem realize_castLE_of_eq {m n : Nat} (h : m = n) {h' : m <= n} {φ : L.BoundedFormula α m}
    {v : α -> M} {xs : Fin n -> M} : (φ.castLE h').Realize v xs ↔ φ.Realize v (xs ∘ Fin.cast h) := by
  subst h
  simp only [castLE_rfl, cast_refl, Function.comp_id]

/--
theorem `realize_mapTermRel_id` / 定理 `realize_mapTermRel_id`

English:
theorem realize_mapTermRel_id
  statement: [L'.Structure M]
  proof: by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel, Realize, h1]
  | rel => simp [mapTermRel, Realize, h1, h2]
  | imp _ _ ih1 ih2 => simp [mapTermRel, Realize, ih1, ih2]
  | all _ ih => simp only [mapTermRel, Realize, ih, id]

中文:
定理 realize_mapTermRel_id
  结论: [L'.Structure M]
  证明: by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel, Realize, h1]
  | rel => simp [mapTermRel, Realize, h1, h2]
  | imp _ _ ih1 ih2 => simp [mapTermRel, Realize, ih1, ih2]
  | all _ ih => simp only [mapTermRel, Realize, ih, id]

Depends on / 依赖: Realize, falsum, mapTermRel
-/
theorem realize_mapTermRel_id [L'.Structure M]
    {ft : forall n, L.Term (α oplus (Fin n)) -> L'.Term (β oplus (Fin n))}
    {fr : forall n, L.Relations n -> L'.Relations n} {n} {φ : L.BoundedFormula α n} {v : α -> M}
    {v' : β -> M} {xs : Fin n -> M}
    (h1 :
      forall (n) (t : L.Term (α oplus (Fin n))) (xs : Fin n -> M),
        (ft n t).realize (Sum.elim v' xs) = t.realize (Sum.elim v xs))
    (h2 : forall (n) (R : L.Relations n) (x : Fin n -> M), RelMap (fr n R) x = RelMap R x) :
    (φ.mapTermRel ft fr fun _ => id).Realize v' xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel, Realize, h1]
  | rel => simp [mapTermRel, Realize, h1, h2]
  | imp _ _ ih1 ih2 => simp [mapTermRel, Realize, ih1, ih2]
  | all _ ih => simp only [mapTermRel, Realize, ih, id]

/--
theorem `realize_mapTermRel_add_castLe` / 定理 `realize_mapTermRel_add_castLe`

English:
theorem realize_mapTermRel_add_castLe
  statement: [L'.Structure M] {k : Nat}
  proof: by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel, Realize, h1]
  | rel => simp [mapTermRel, Realize, h1, h2]
  | imp _ _ ih1 ih2 => simp [mapTermRel, Realize, ih1, ih2]
  | all _ ih => simp [mapTermRel, Realize, ih, hv]

@[simp]

中文:
定理 realize_mapTermRel_add_castLe
  结论: [L'.Structure M] {k : 自然数}
  证明: by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel, Realize, h1]
  | rel => simp [mapTermRel, Realize, h1, h2]
  | imp _ _ ih1 ih2 => simp [mapTermRel, Realize, ih1, ih2]
  | all _ ih => simp [mapTermRel, Realize, ih, hv]

@[simp]

Depends on / 依赖: Realize, falsum, mapTermRel
-/
theorem realize_mapTermRel_add_castLe [L'.Structure M] {k : Nat}
    {ft : forall n, L.Term (α oplus (Fin n)) -> L'.Term (β oplus (Fin (k + n)))}
    {fr : forall n, L.Relations n -> L'.Relations n} {n} {φ : L.BoundedFormula α n}
    (v : forall {n}, (Fin (k + n) -> M) -> α -> M) {v' : β -> M} (xs : Fin (k + n) -> M)
    (h1 :
      forall (n) (t : L.Term (α oplus (Fin n))) (xs' : Fin (k + n) -> M),
        (ft n t).realize (Sum.elim v' xs') = t.realize (Sum.elim (v xs') (xs' ∘ Fin.natAdd _)))
    (h2 : forall (n) (R : L.Relations n) (x : Fin n -> M), RelMap (fr n R) x = RelMap R x)
    (hv : forall (n) (xs : Fin (k + n) -> M) (x : M), @v (n + 1) (snoc xs x : Fin _ -> M) = v xs) :
    (φ.mapTermRel ft fr fun _ => castLE (add_assoc _ _ _).symm.le).Realize v' xs ↔
      φ.Realize (v xs) (xs ∘ Fin.natAdd _) := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel, Realize, h1]
  | rel => simp [mapTermRel, Realize, h1, h2]
  | imp _ _ ih1 ih2 => simp [mapTermRel, Realize, ih1, ih2]
  | all _ ih => simp [mapTermRel, Realize, ih, hv]

@[simp]
/--
theorem `realize_relabel` / 定理 `realize_relabel`

English:
theorem realize_relabel
  statement: {m n : Nat} {φ : L.BoundedFormula α n} {g : α -> β oplus (Fin m)} {v : β -> M}
  proof: by
  apply realize_mapTermRel_add_castLe <;> simp

中文:
定理 realize_relabel
  结论: {m n : 自然数} {φ : L.BoundedFormula α n} {g : α -> β oplus (Fin m)} {v : β -> M}
  证明: by
  apply realize_mapTermRel_add_castLe <;> simp

Depends on / 依赖: realize_mapTermRel_add_castLe
-/
theorem realize_relabel {m n : Nat} {φ : L.BoundedFormula α n} {g : α -> β oplus (Fin m)} {v : β -> M}
    {xs : Fin (m + n) -> M} :
    (φ.relabel g).Realize v xs ↔
      φ.Realize (Sum.elim v (xs ∘ Fin.castAdd n) ∘ g) (xs ∘ Fin.natAdd m) := by
  apply realize_mapTermRel_add_castLe <;> simp

/--
theorem `realize_liftAt` / 定理 `realize_liftAt`

English:
theorem realize_liftAt
  statement: {n n' m : Nat} {φ : L.BoundedFormula α n} {v : α -> M} {xs : Fin (n + n') -> M}
  proof: by
  rw [liftAt]
  induction φ with
  | falsum => simp [mapTermRel, Realize]
  | equal => simp [mapTermRel, Realize, Sum.elim_comp_map]
  | rel => simp [mapTermRel, Realize, Sum.elim_comp_map]
  | imp _ _ ih1 ih2 => simp only [mapTermRel, Realize, ih1 hmn, ih2 hmn]
  | @all k _ ih3 =>
    have h : k

中文:
定理 realize_liftAt
  结论: {n n' m : 自然数} {φ : L.BoundedFormula α n} {v : α -> M} {xs : Fin (n + n') -> M}
  证明: by
  rw [liftAt]
  induction φ with
  | falsum => simp [mapTermRel, Realize]
  | equal => simp [mapTermRel, Realize, Sum.elim_comp_map]
  | rel => simp [mapTermRel, Realize, Sum.elim_comp_map]
  | imp _ _ ih1 ih2 => simp only [mapTermRel, Realize, ih1 hmn, ih2 hmn]
  | @all k _ ih3 =>
    have h : k

Depends on / 依赖: Realize, Sum.elim_comp_map, add_assoc, add_comm, elim_comp_map, falsum, forall_congr, hmn.trans, iff_eq_eq, iff_eq_eq.mpr, k.le_succ, le_succ, liftAt, mapTermRel, realize_castLE_of_eq
-/
theorem realize_liftAt {n n' m : Nat} {φ : L.BoundedFormula α n} {v : α -> M} {xs : Fin (n + n') -> M}
    (hmn : m <= n) :
    (φ.liftAt n' m).Realize v xs ↔
      φ.Realize v (xs ∘ fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') := by
  rw [liftAt]
  induction φ with
  | falsum => simp [mapTermRel, Realize]
  | equal => simp [mapTermRel, Realize, Sum.elim_comp_map]
  | rel => simp [mapTermRel, Realize, Sum.elim_comp_map]
  | imp _ _ ih1 ih2 => simp only [mapTermRel, Realize, ih1 hmn, ih2 hmn]
  | @all k _ ih3 =>
    have h : k + 1 + n' = k + n' + 1 := by rw [add_assoc, add_comm 1 n', ← add_assoc]
    simp only [mapTermRel, Realize, realize_castLE_of_eq h, ih3 (hmn.trans k.le_succ)]
    refine forall_congr' fun x => iff_eq_eq.mpr (congr rfl (funext (Fin.lastCases ?_ fun i => ?_)))
    · simp only [Function.comp_apply, val_last, snoc_last]
      refine (congr rfl (Fin.ext ?_)).trans (snoc_last _ _)
      split_ifs <;> dsimp; lia
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      refine (congr rfl (Fin.ext ?_)).trans (snoc_castSucc _ _ _)
      simp only [val_castSucc, val_cast]
      split_ifs <;> simp

/--
theorem `realize_liftAt_one` / 定理 `realize_liftAt_one`

English:
theorem realize_liftAt_one
  statement: {n m : Nat} {φ : L.BoundedFormula α n} {v : α -> M} {xs : Fin (n + 1) -> M}
  proof: by
  simp [realize_liftAt, hmn, castSucc]

@[simp]

中文:
定理 realize_liftAt_one
  结论: {n m : 自然数} {φ : L.BoundedFormula α n} {v : α -> M} {xs : Fin (n + 1) -> M}
  证明: by
  simp [realize_liftAt, hmn, castSucc]

@[simp]

Depends on / 依赖: castSucc, realize_liftAt
-/
theorem realize_liftAt_one {n m : Nat} {φ : L.BoundedFormula α n} {v : α -> M} {xs : Fin (n + 1) -> M}
    (hmn : m <= n) :
    (φ.liftAt 1 m).Realize v xs ↔
      φ.Realize v (xs ∘ fun i => if ↑i < m then castSucc i else i.succ) := by
  simp [realize_liftAt, hmn, castSucc]

@[simp]
/--
theorem `realize_liftAt_one_self` / 定理 `realize_liftAt_one_self`

English:
theorem realize_liftAt_one_self
  statement: {n : Nat} {φ : L.BoundedFormula α n} {v : α -> M}
  proof: by
  rw [realize_liftAt_one (refl n)]; rw [iff_eq_eq]
  refine congr rfl (congr rfl (funext fun i => ?_))
  rw [if_pos i.is_lt]

@[simp]

中文:
定理 realize_liftAt_one_self
  结论: {n : 自然数} {φ : L.BoundedFormula α n} {v : α -> M}
  证明: by
  rw [realize_liftAt_one (refl n)]; rw [iff_eq_eq]
  refine congr rfl (congr rfl (funext fun i => ?_))
  rw [if_pos i.is_lt]

@[simp]

Depends on / 依赖: i.is_lt, if_pos, iff_eq_eq, is_lt, realize_liftAt_one
-/
theorem realize_liftAt_one_self {n : Nat} {φ : L.BoundedFormula α n} {v : α -> M}
    {xs : Fin (n + 1) -> M} : (φ.liftAt 1 n).Realize v xs ↔ φ.Realize v (xs ∘ castSucc) := by
  rw [realize_liftAt_one (refl n)]; rw [iff_eq_eq]
  refine congr rfl (congr rfl (funext fun i => ?_))
  rw [if_pos i.is_lt]

@[simp]
/--
theorem `realize_subst` / 定理 `realize_subst`

English:
theorem realize_subst
  given: {φ : L.BoundedFormula α n} {tf : α -> L.Term β} {v : β -> M} {xs : Fin n -> M}
  proof: realize_mapTermRel_id
    (fun n t x => by
      rw [Term.realize_subst]
      rcongr a
      cases a
      · simp only [Sum.elim_inl, Function.comp_apply, Term.realize_relabel, Sum.elim_comp_inl]
      · rfl)
    (by simp)

中文:
定理 realize_subst
  条件: {φ : L.BoundedFormula α n} {tf : α -> L.Term β} {v : β -> M} {xs : Fin n -> M}
  证明: realize_mapTermRel_id
    (fun n t x => by
      rw [Term.realize_subst]
      rcongr a
      cases a
      · simp only [Sum.elim_inl, Function.comp_apply, Term.realize_relabel, Sum.elim_comp_inl]
      · rfl)
    (by simp)

Depends on / 依赖: Function, Function.comp_apply, Sum.elim_comp_inl, Sum.elim_inl, Term.realize_relabel, Term.realize_subst, comp_apply, elim_comp_inl, elim_inl, rcongr, realize_mapTermRel_id, realize_relabel, realize_subst
-/
theorem realize_subst {φ : L.BoundedFormula α n} {tf : α -> L.Term β} {v : β -> M} {xs : Fin n -> M} :
    (φ.subst tf).Realize v xs ↔ φ.Realize (fun a => (tf a).realize v) xs :=
  realize_mapTermRel_id
    (fun n t x => by
      rw [Term.realize_subst]
      rcongr a
      cases a
      · simp only [Sum.elim_inl, Function.comp_apply, Term.realize_relabel, Sum.elim_comp_inl]
      · rfl)
    (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `realize_restrictFreeVar` / 定理 `realize_restrictFreeVar`

English:
theorem realize_restrictFreeVar
  statement: [DecidableEq α] {n : Nat} {φ : L.BoundedFormula α n}
  proof: by
  induction φ with
  | falsum => rfl
  | equal =>
    simp only [Realize, restrictFreeVar]
    rw [realize_restrictVarLeft v' (by simp [hv']), realize_restrictVarLeft v' (by simp [hv'])]
    simp
  | rel =>
    simp only [Realize, restrictFreeVar]
    congr!
    rw [realize_restrictVarLeft v' (by

中文:
定理 realize_restrictFreeVar
  结论: [DecidableEq α] {n : 自然数} {φ : L.BoundedFormula α n}
  证明: by
  induction φ with
  | falsum => rfl
  | equal =>
    simp only [Realize, restrictFreeVar]
    rw [realize_restrictVarLeft v' (by simp [hv']), realize_restrictVarLeft v' (by simp [hv'])]
    simp
  | rel =>
    simp only [Realize, restrictFreeVar]
    congr!
    rw [realize_restrictVarLeft v' (by

Depends on / 依赖: Realize, falsum, forall_congr, realize_restrictVarLeft, restrictFreeVar
-/
theorem realize_restrictFreeVar [DecidableEq α] {n : Nat} {φ : L.BoundedFormula α n}
    {f : φ.freeVarFinset -> β} {v : β -> M} {xs : Fin n -> M}
    (v' : α -> M) (hv' : forall a, v (f a) = v' a) :
    (φ.restrictFreeVar f).Realize v xs ↔ φ.Realize v' xs := by
  induction φ with
  | falsum => rfl
  | equal =>
    simp only [Realize, restrictFreeVar]
    rw [realize_restrictVarLeft v' (by simp [hv']), realize_restrictVarLeft v' (by simp [hv'])]
    simp
  | rel =>
    simp only [Realize, restrictFreeVar]
    congr!
    rw [realize_restrictVarLeft v' (by simp [hv'])]
    simp
  | imp _ _ ih1 ih2 =>
    simp only [Realize, restrictFreeVar]
    rw [ih1]; rw [ih2] <;> simp [hv']
  | all _ ih3 =>
    simp only [restrictFreeVar, Realize]
    refine forall_congr' (fun _ => ?_)
    rw [ih3]; simp [hv']

/-- A special case of `realize_restrictFreeVar`, included because we can add the `simp` attribute
to it -/
@[simp]
/--
theorem `realize_restrictFreeVar'` / 定理 `realize_restrictFreeVar'`

English:
theorem realize_restrictFreeVar'
  statement: [DecidableEq α] {n : Nat} {φ : L.BoundedFormula α n} {s : Set α}
  proof: realize_restrictFreeVar _ (by simp)

中文:
定理 realize_restrictFreeVar'
  结论: [DecidableEq α] {n : 自然数} {φ : L.BoundedFormula α n} {s : Set α}
  证明: realize_restrictFreeVar _ (by simp)

Depends on / 依赖: realize_restrictFreeVar
-/
theorem realize_restrictFreeVar' [DecidableEq α] {n : Nat} {φ : L.BoundedFormula α n} {s : Set α}
    (h : ↑φ.freeVarFinset subseteq s) {v : α -> M} {xs : Fin n -> M} :
    (φ.restrictFreeVar (Set.inclusion h)).Realize (v ∘ (↑)) xs ↔ φ.Realize v xs :=
  realize_restrictFreeVar _ (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `realize_constantsVarsEquiv` / 定理 `realize_constantsVarsEquiv`

English:
theorem realize_constantsVarsEquiv
  statement: [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
  proof: by
  refine realize_mapTermRel_id (fun n t xs => realize_constantsVarsEquivLeft) fun n R xs => ?_
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [← (lhomWithConstants L α).map_onRelation
      (Equiv.sumEmpty (L.Relations n) ((constantsOn α).Re

中文:
定理 realize_constantsVarsEquiv
  结论: [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
  证明: by
  refine realize_mapTermRel_id (fun n t xs => realize_constantsVarsEquivLeft) fun n R xs => ?_
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [← (lhomWithConstants L α).map_onRelation
      (Equiv.sumEmpty (L.Relations n) ((constantsOn α).Re

Depends on / 依赖: realize_constantsVarsEquivLeft, realize_mapTermRel_id
-/
theorem realize_constantsVarsEquiv [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {φ : L[[α]].BoundedFormula β n} {v : β -> M} {xs : Fin n -> M} :
    (constantsVarsEquiv φ).Realize (Sum.elim (fun a => ↑(L.con a)) v) xs ↔ φ.Realize v xs := by
  refine realize_mapTermRel_id (fun n t xs => realize_constantsVarsEquivLeft) fun n R xs => ?_
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [← (lhomWithConstants L α).map_onRelation
      (Equiv.sumEmpty (L.Relations n) ((constantsOn α).Relations n) R) xs]
  rcongr
  obtain - | R := R
  · simp
  · exact isEmptyElim R

@[simp]
/--
theorem `realize_relabelEquiv` / 定理 `realize_relabelEquiv`

English:
theorem realize_relabelEquiv
  statement: {g : α ≃ β} {k} {φ : L.BoundedFormula α k} {v : β -> M}
  proof: by
  simp only [relabelEquiv, mapTermRelEquiv_apply, Equiv.coe_refl]
  refine realize_mapTermRel_id (fun n t xs => ?_) fun _ _ _ => rfl
  simp only [relabelEquiv_apply, Term.realize_relabel]
  refine congr (congr rfl ?_) rfl
  ext (i | i) <;> rfl

中文:
定理 realize_relabelEquiv
  结论: {g : α ≃ β} {k} {φ : L.BoundedFormula α k} {v : β -> M}
  证明: by
  simp only [relabelEquiv, mapTermRelEquiv_apply, Equiv.coe_refl]
  refine realize_mapTermRel_id (fun n t xs => ?_) fun _ _ _ => rfl
  simp only [relabelEquiv_apply, Term.realize_relabel]
  refine congr (congr rfl ?_) rfl
  ext (i | i) <;> rfl

Depends on / 依赖: Equiv.coe_refl, Term.realize_relabel, coe_refl, mapTermRelEquiv_apply, realize_mapTermRel_id, realize_relabel, relabelEquiv, relabelEquiv_apply
-/
theorem realize_relabelEquiv {g : α ≃ β} {k} {φ : L.BoundedFormula α k} {v : β -> M}
    {xs : Fin k -> M} : (relabelEquiv g φ).Realize v xs ↔ φ.Realize (v ∘ g) xs := by
  simp only [relabelEquiv, mapTermRelEquiv_apply, Equiv.coe_refl]
  refine realize_mapTermRel_id (fun n t xs => ?_) fun _ _ _ => rfl
  simp only [relabelEquiv_apply, Term.realize_relabel]
  refine congr (congr rfl ?_) rfl
  ext (i | i) <;> rfl

variable [Nonempty M]

/--
theorem `realize_all_liftAt_one_self` / 定理 `realize_all_liftAt_one_self`

English:
theorem realize_all_liftAt_one_self
  statement: {n : Nat} {φ : L.BoundedFormula α n} {v : α -> M}
  proof: by
  simp

中文:
定理 realize_all_liftAt_one_self
  结论: {n : 自然数} {φ : L.BoundedFormula α n} {v : α -> M}
  证明: by
  simp
-/
theorem realize_all_liftAt_one_self {n : Nat} {φ : L.BoundedFormula α n} {v : α -> M}
    {xs : Fin n -> M} : (φ.liftAt 1 n).all.Realize v xs ↔ φ.Realize v xs := by
  simp

end BoundedFormula

namespace LHom

open BoundedFormula

@[simp]
/--
theorem `realize_onBoundedFormula` / 定理 `realize_onBoundedFormula`

English:
theorem realize_onBoundedFormula
  statement: [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] {n : Nat}
  proof: by
  induction ψ with
  | falsum => rfl
  | equal => simp only [onBoundedFormula, realize_bdEqual, realize_onTerm]; rfl
  | rel =>
    simp only [onBoundedFormula, realize_rel, LHom.map_onRelation,
      Function.comp_apply, realize_onTerm]
    rfl
  | imp _ _ ih1 ih2 => simp only [onBoundedFormula,

中文:
定理 realize_onBoundedFormula
  结论: [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] {n : 自然数}
  证明: by
  induction ψ with
  | falsum => rfl
  | equal => simp only [onBoundedFormula, realize_bdEqual, realize_onTerm]; rfl
  | rel =>
    simp only [onBoundedFormula, realize_rel, LHom.map_onRelation,
      Function.comp_apply, realize_onTerm]
    rfl
  | imp _ _ ih1 ih2 => simp only [onBoundedFormula,

Depends on / 依赖: Function, Function.comp_apply, LHom.map_onRelation, comp_apply, falsum, map_onRelation, onBoundedFormula, realize_all, realize_bdEqual, realize_imp, realize_onTerm, realize_rel
-/
theorem realize_onBoundedFormula [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] {n : Nat}
    (ψ : L.BoundedFormula α n) {v : α -> M} {xs : Fin n -> M} :
    (φ.onBoundedFormula ψ).Realize v xs ↔ ψ.Realize v xs := by
  induction ψ with
  | falsum => rfl
  | equal => simp only [onBoundedFormula, realize_bdEqual, realize_onTerm]; rfl
  | rel =>
    simp only [onBoundedFormula, realize_rel, LHom.map_onRelation,
      Function.comp_apply, realize_onTerm]
    rfl
  | imp _ _ ih1 ih2 => simp only [onBoundedFormula, ih1, ih2, realize_imp]
  | all _ ih3 => simp only [onBoundedFormula, ih3, realize_all]

end LHom

namespace Formula

/-- A formula can be evaluated as true or false by giving values to each free variable. -/
nonrec def Realize (φ : L.Formula α) (v : α -> M) : Prop :=
  φ.Realize v default

variable {φ ψ : L.Formula α} {v : α -> M}

@[simp]
/--
theorem `realize_not` / 定理 `realize_not`

English:
theorem realize_not
  statement: φ.not.Realize v ↔ ¬φ.Realize v
  proof: Iff.rfl

@[simp]

中文:
定理 realize_not
  结论: φ.not.实数ize v ↔ ¬φ.实数ize v
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem realize_not : φ.not.Realize v ↔ ¬φ.Realize v :=
  Iff.rfl

@[simp]
/--
theorem `realize_bot` / 定理 `realize_bot`

English:
theorem realize_bot
  statement: (⊥ : L.Formula α).Realize v ↔ False
  proof: Iff.rfl

@[simp]

中文:
定理 realize_bot
  结论: (⊥ : L.Formula α).实数ize v ↔ False
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem realize_bot : (⊥ : L.Formula α).Realize v ↔ False :=
  Iff.rfl

@[simp]
/--
theorem `realize_top` / 定理 `realize_top`

English:
theorem realize_top
  statement: (⊤ : L.Formula α).Realize v ↔ True
  proof: BoundedFormula.realize_top

@[simp]

中文:
定理 realize_top
  结论: (⊤ : L.Formula α).实数ize v ↔ True
  证明: BoundedFormula.realize_top

@[simp]

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_top, realize_top
-/
theorem realize_top : (⊤ : L.Formula α).Realize v ↔ True :=
  BoundedFormula.realize_top

@[simp]
/--
theorem `realize_inf` / 定理 `realize_inf`

English:
theorem realize_inf
  statement: (φ ⊓ ψ).Realize v ↔ φ.Realize v ∧ ψ.Realize v
  proof: BoundedFormula.realize_inf

@[simp]

中文:
定理 realize_inf
  结论: (φ ⊓ ψ).实数ize v ↔ φ.实数ize v ∧ ψ.实数ize v
  证明: BoundedFormula.realize_inf

@[simp]

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_inf, realize_inf
-/
theorem realize_inf : (φ ⊓ ψ).Realize v ↔ φ.Realize v ∧ ψ.Realize v :=
  BoundedFormula.realize_inf

@[simp]
/--
theorem `realize_imp` / 定理 `realize_imp`

English:
theorem realize_imp
  statement: (φ.imp ψ).Realize v ↔ φ.Realize v -> ψ.Realize v
  proof: BoundedFormula.realize_imp

@[simp]

中文:
定理 realize_imp
  结论: (φ.imp ψ).实数ize v ↔ φ.实数ize v -> ψ.实数ize v
  证明: BoundedFormula.realize_imp

@[simp]

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_imp, realize_imp
-/
theorem realize_imp : (φ.imp ψ).Realize v ↔ φ.Realize v -> ψ.Realize v :=
  BoundedFormula.realize_imp

@[simp]
/--
theorem `realize_rel` / 定理 `realize_rel`

English:
theorem realize_rel
  given: {k : Nat} {R : L.Relations k} {ts : Fin k -> L.Term α}
  proof: BoundedFormula.realize_rel.trans (by simp)

@[simp]

中文:
定理 realize_rel
  条件: {k : 自然数} {R : L.Relations k} {ts : Fin k -> L.Term α}
  证明: BoundedFormula.realize_rel.trans (by simp)

@[simp]

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_rel.trans, realize_rel
-/
theorem realize_rel {k : Nat} {R : L.Relations k} {ts : Fin k -> L.Term α} :
    (R.formula ts).Realize v ↔ RelMap R fun i => (ts i).realize v :=
  BoundedFormula.realize_rel.trans (by simp)

@[simp]
/--
theorem `realize_rel₁` / 定理 `realize_rel₁`

English:
theorem realize_rel₁
  given: {R : L.Relations 1} {t : L.Term _}
  proof: by
  rw [Relations.formula₁]; rw [realize_rel]; rw [iff_eq_eq]
  refine congr rfl (funext fun _ => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]

中文:
定理 realize_rel₁
  条件: {R : L.Relations 1} {t : L.Term _}
  证明: by
  rw [Relations.formula₁]; rw [realize_rel]; rw [iff_eq_eq]
  refine congr rfl (funext fun _ => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]

Depends on / 依赖: Matrix, Matrix.cons_val_fin_one, Relations, Relations.formula, cons_val_fin_one, iff_eq_eq, realize_rel
-/
theorem realize_rel₁ {R : L.Relations 1} {t : L.Term _} :
    (R.formula₁ t).Realize v ↔ RelMap R ![t.realize v] := by
  rw [Relations.formula₁]; rw [realize_rel]; rw [iff_eq_eq]
  refine congr rfl (funext fun _ => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]
/--
theorem `realize_rel₂` / 定理 `realize_rel₂`

English:
theorem realize_rel₂
  given: {R : L.Relations 2} {t₁ t₂ : L.Term _}
  proof: by
  rw [Relations.formula₂]; rw [realize_rel]; rw [iff_eq_eq]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

@[simp]

中文:
定理 realize_rel₂
  条件: {R : L.Relations 2} {t₁ t₂ : L.Term _}
  证明: by
  rw [Relations.formula₂]; rw [realize_rel]; rw [iff_eq_eq]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

@[simp]

Depends on / 依赖: Fin.cases, Matrix, Matrix.cons_val_fin_one, Matrix.cons_val_succ, Matrix.cons_val_zero, Relations, Relations.formula, cons_val_fin_one, cons_val_succ, cons_val_zero, forall_const, iff_eq_eq, realize_rel
-/
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
    (R.formula₂ t₁ t₂).Realize v ↔ RelMap R ![t₁.realize v, t₂.realize v] := by
  rw [Relations.formula₂]; rw [realize_rel]; rw [iff_eq_eq]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

@[simp]
/--
theorem `realize_sup` / 定理 `realize_sup`

English:
theorem realize_sup
  statement: (φ ⊔ ψ).Realize v ↔ φ.Realize v ∨ ψ.Realize v
  proof: BoundedFormula.realize_sup

@[simp]

中文:
定理 realize_sup
  结论: (φ ⊔ ψ).实数ize v ↔ φ.实数ize v ∨ ψ.实数ize v
  证明: BoundedFormula.realize_sup

@[simp]

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_sup, realize_sup
-/
theorem realize_sup : (φ ⊔ ψ).Realize v ↔ φ.Realize v ∨ ψ.Realize v :=
  BoundedFormula.realize_sup

@[simp]
/--
theorem `realize_iff` / 定理 `realize_iff`

English:
theorem realize_iff
  statement: (φ.iff ψ).Realize v ↔ (φ.Realize v ↔ ψ.Realize v)
  proof: BoundedFormula.realize_iff

@[simp]

中文:
定理 realize_iff
  结论: (φ.iff ψ).实数ize v ↔ (φ.实数ize v ↔ ψ.实数ize v)
  证明: BoundedFormula.realize_iff

@[simp]

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_iff, realize_iff
-/
theorem realize_iff : (φ.iff ψ).Realize v ↔ (φ.Realize v ↔ ψ.Realize v) :=
  BoundedFormula.realize_iff

@[simp]
/--
theorem `realize_relabel` / 定理 `realize_relabel`

English:
theorem realize_relabel
  given: {φ : L.Formula α} {g : α -> β} {v : β -> M}
  proof: by
  rw [Realize]; rw [Realize]; rw [relabel]; rw [BoundedFormula.realize_relabel]; rw [iff_eq_eq]; rw [Fin.castAdd_zero]
  exact congr rfl (funext finZeroElim)

中文:
定理 realize_relabel
  条件: {φ : L.Formula α} {g : α -> β} {v : β -> M}
  证明: by
  rw [Realize]; rw [Realize]; rw [relabel]; rw [BoundedFormula.realize_relabel]; rw [iff_eq_eq]; rw [Fin.castAdd_zero]
  exact congr rfl (funext finZeroElim)

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_relabel, Fin.castAdd_zero, Realize, castAdd_zero, finZeroElim, iff_eq_eq, realize_relabel, relabel
-/
theorem realize_relabel {φ : L.Formula α} {g : α -> β} {v : β -> M} :
    (φ.relabel g).Realize v ↔ φ.Realize (v ∘ g) := by
  rw [Realize]; rw [Realize]; rw [relabel]; rw [BoundedFormula.realize_relabel]; rw [iff_eq_eq]; rw [Fin.castAdd_zero]
  exact congr rfl (funext finZeroElim)

/--
theorem `realize_relabel_sumInr` / 定理 `realize_relabel_sumInr`

English:
theorem realize_relabel_sumInr
  given: (φ : L.Formula (Fin n)) {v : Empty -> M} {x : Fin n -> M}
  proof: by
  rw [BoundedFormula.realize_relabel]; rw [Formula.Realize]; rw [Sum.elim_comp_inr]; rw [Fin.castAdd_zero]; rw [cast_refl]; rw [Function.comp_id]; rw [Subsingleton.elim (x ∘ (natAdd n : Fin 0 -> Fin n)) default]

@[simp]

中文:
定理 realize_relabel_sumInr
  条件: (φ : L.Formula (Fin n)) {v : Empty -> M} {x : Fin n -> M}
  证明: by
  rw [BoundedFormula.realize_relabel]; rw [Formula.Realize]; rw [Sum.elim_comp_inr]; rw [Fin.castAdd_zero]; rw [cast_refl]; rw [Function.comp_id]; rw [Subsingleton.elim (x ∘ (natAdd n : Fin 0 -> Fin n)) default]

@[simp]

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_relabel, Fin.castAdd_zero, Formula, Formula.Realize, Function, Function.comp_id, Realize, Subsingleton, Subsingleton.elim, Sum.elim_comp_inr, castAdd_zero, cast_refl, comp_id, elim_comp_inr, natAdd, realize_relabel
-/
theorem realize_relabel_sumInr (φ : L.Formula (Fin n)) {v : Empty -> M} {x : Fin n -> M} :
    (BoundedFormula.relabel Sum.inr φ).Realize v x ↔ φ.Realize x := by
  rw [BoundedFormula.realize_relabel]; rw [Formula.Realize]; rw [Sum.elim_comp_inr]; rw [Fin.castAdd_zero]; rw [cast_refl]; rw [Function.comp_id]; rw [Subsingleton.elim (x ∘ (natAdd n : Fin 0 -> Fin n)) default]

@[simp]
/--
theorem `realize_equal` / 定理 `realize_equal`

English:
theorem realize_equal
  given: {t₁ t₂ : L.Term α} {x : α -> M}
  proof: by simp [Term.equal, Realize]

@[simp]

中文:
定理 realize_equal
  条件: {t₁ t₂ : L.Term α} {x : α -> M}
  证明: by simp [Term.equal, Realize]

@[simp]

Depends on / 依赖: Realize, Term.equal
-/
theorem realize_equal {t₁ t₂ : L.Term α} {x : α -> M} :
    (t₁.equal t₂).Realize x ↔ t₁.realize x = t₂.realize x := by simp [Term.equal, Realize]

@[simp]
/--
theorem `realize_graph` / 定理 `realize_graph`

English:
theorem realize_graph
  given: {f : L.Functions n} {x : Fin n -> M} {y : M}
  proof: by
  simp only [Formula.graph, Term.realize, realize_equal, Fin.cons_zero, Fin.cons_succ]
  rw [eq_comm]

中文:
定理 realize_graph
  条件: {f : L.Functions n} {x : Fin n -> M} {y : M}
  证明: by
  simp only [Formula.graph, Term.realize, realize_equal, Fin.cons_zero, Fin.cons_succ]
  rw [eq_comm]

Depends on / 依赖: Fin.cons_succ, Fin.cons_zero, Formula, Formula.graph, Term.realize, cons_succ, cons_zero, eq_comm, realize, realize_equal
-/
theorem realize_graph {f : L.Functions n} {x : Fin n -> M} {y : M} :
    (Formula.graph f).Realize (Fin.cons y x : _ -> M) ↔ funMap f x = y := by
  simp only [Formula.graph, Term.realize, realize_equal, Fin.cons_zero, Fin.cons_succ]
  rw [eq_comm]

/--
theorem `boundedFormula_realize_eq_realize` / 定理 `boundedFormula_realize_eq_realize`

English:
theorem boundedFormula_realize_eq_realize
  given: (φ : L.Formula α) (x : α -> M) (y : Fin 0 -> M)
  proof: by
  rw [Formula.Realize]; rw [iff_iff_eq]
  congr
  ext i; exact Fin.elim0 i

中文:
定理 boundedFormula_realize_eq_realize
  条件: (φ : L.Formula α) (x : α -> M) (y : Fin 0 -> M)
  证明: by
  rw [Formula.Realize]; rw [iff_iff_eq]
  congr
  ext i; exact Fin.elim0 i

Depends on / 依赖: Fin.elim0, Formula, Formula.Realize, Realize, iff_iff_eq
-/
theorem boundedFormula_realize_eq_realize (φ : L.Formula α) (x : α -> M) (y : Fin 0 -> M) :
    BoundedFormula.Realize φ x y ↔ φ.Realize x := by
  rw [Formula.Realize]; rw [iff_iff_eq]
  congr
  ext i; exact Fin.elim0 i

end Formula

@[simp]
/--
theorem `LHom.realize_onFormula` / 定理 `LHom.realize_onFormula`

English:
theorem LHom.realize_onFormula
  statement: [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] (ψ : L.Formula α)
  proof: φ.realize_onBoundedFormula ψ

@[simp]

中文:
定理 LHom.realize_onFormula
  结论: [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] (ψ : L.Formula α)
  证明: φ.realize_onBoundedFormula ψ

@[simp]

Depends on / 依赖: realize_onBoundedFormula
-/
theorem LHom.realize_onFormula [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] (ψ : L.Formula α)
    {v : α -> M} : (φ.onFormula ψ).Realize v ↔ ψ.Realize v :=
  φ.realize_onBoundedFormula ψ

@[simp]
/--
theorem `LHom.setOfPred_realize_onFormula` / 定理 `LHom.setOfPred_realize_onFormula`

English:
theorem LHom.setOfPred_realize_onFormula
  statement: [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M]
  proof: by
  ext
  simp

@[deprecated (since := "2026-07-09")]
alias LHom.setOf_realize_onFormula := LHom.setOfPred_realize_onFormula

中文:
定理 LHom.setOfPred_realize_onFormula
  结论: [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M]
  证明: by
  ext
  simp

@[deprecated (since := "2026-07-09")]
alias LHom.setOf_realize_onFormula := LHom.setOfPred_realize_onFormula
-/
theorem LHom.setOfPred_realize_onFormula [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M]
    (ψ : L.Formula α) :
    (Set.ofPred (φ.onFormula ψ).Realize : Set (α -> M)) = Set.ofPred ψ.Realize := by
  ext
  simp

@[deprecated (since := "2026-07-09")]
alias LHom.setOf_realize_onFormula := LHom.setOfPred_realize_onFormula

variable (M)

/-- A sentence can be evaluated as true or false in a structure. -/
nonrec def Sentence.Realize (φ : L.Sentence) : Prop :=
  φ.Realize (default : _ -> M)

-- input using \|= or \vDash, but not using \models
@[inherit_doc Sentence.Realize]
infixl:51 " ⊨ " => Sentence.Realize

namespace Sentence

variable {φ ψ : L.Sentence}

@[simp]
/--
theorem `realize_not` / 定理 `realize_not`

English:
theorem realize_not
  statement: M ⊨ φ.not ↔ ¬M ⊨ φ
  proof: Iff.rfl

@[simp]

中文:
定理 realize_not
  结论: M ⊨ φ.not ↔ ¬M ⊨ φ
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem realize_not : M ⊨ φ.not ↔ ¬M ⊨ φ :=
  Iff.rfl

@[simp]
/--
theorem `not_realize_bot` / 定理 `not_realize_bot`

English:
theorem not_realize_bot
  statement: ¬(M ⊨ (⊥ : L.Sentence))
  proof: False.elim

@[simp]

中文:
定理 not_realize_bot
  结论: ¬(M ⊨ (⊥ : L.Sentence))
  证明: False.elim

@[simp]

Depends on / 依赖: False.elim
-/
theorem not_realize_bot : ¬(M ⊨ (⊥ : L.Sentence)) :=
  False.elim

@[simp]
/--
theorem `realize_top` / 定理 `realize_top`

English:
theorem realize_top
  statement: M ⊨ (⊤ : L.Sentence)
  proof: False.elim

@[simp]

中文:
定理 realize_top
  结论: M ⊨ (⊤ : L.Sentence)
  证明: False.elim

@[simp]

Depends on / 依赖: False.elim
-/
theorem realize_top : M ⊨ (⊤ : L.Sentence) :=
  False.elim

@[simp]
/--
theorem `realize_inf` / 定理 `realize_inf`

English:
theorem realize_inf
  statement: M ⊨ φ ⊓ ψ ↔ M ⊨ φ ∧ M ⊨ ψ
  proof: Formula.realize_inf

@[simp]

中文:
定理 realize_inf
  结论: M ⊨ φ ⊓ ψ ↔ M ⊨ φ ∧ M ⊨ ψ
  证明: Formula.realize_inf

@[simp]

Depends on / 依赖: Formula, Formula.realize_inf, realize_inf
-/
theorem realize_inf : M ⊨ φ ⊓ ψ ↔ M ⊨ φ ∧ M ⊨ ψ :=
  Formula.realize_inf

@[simp]
/--
theorem `realize_sup` / 定理 `realize_sup`

English:
theorem realize_sup
  statement: M ⊨ φ ⊔ ψ ↔ M ⊨ φ ∨ M ⊨ ψ
  proof: Formula.realize_sup

@[simp]

中文:
定理 realize_sup
  结论: M ⊨ φ ⊔ ψ ↔ M ⊨ φ ∨ M ⊨ ψ
  证明: Formula.realize_sup

@[simp]

Depends on / 依赖: Formula, Formula.realize_sup, realize_sup
-/
theorem realize_sup : M ⊨ φ ⊔ ψ ↔ M ⊨ φ ∨ M ⊨ ψ :=
  Formula.realize_sup

@[simp]
/--
theorem `realize_imp` / 定理 `realize_imp`

English:
theorem realize_imp
  statement: M ⊨ φ.imp ψ ↔ M ⊨ φ -> M ⊨ ψ
  proof: Formula.realize_imp

@[simp]

中文:
定理 realize_imp
  结论: M ⊨ φ.imp ψ ↔ M ⊨ φ -> M ⊨ ψ
  证明: Formula.realize_imp

@[simp]

Depends on / 依赖: Formula, Formula.realize_imp, realize_imp
-/
theorem realize_imp : M ⊨ φ.imp ψ ↔ M ⊨ φ -> M ⊨ ψ :=
  Formula.realize_imp

@[simp]
/--
theorem `realize_iff` / 定理 `realize_iff`

English:
theorem realize_iff
  statement: M ⊨ φ.iff ψ ↔ (M ⊨ φ ↔ M ⊨ ψ)
  proof: Formula.realize_iff

中文:
定理 realize_iff
  结论: M ⊨ φ.iff ψ ↔ (M ⊨ φ ↔ M ⊨ ψ)
  证明: Formula.realize_iff

Depends on / 依赖: Formula, Formula.realize_iff, realize_iff
-/
theorem realize_iff : M ⊨ φ.iff ψ ↔ (M ⊨ φ ↔ M ⊨ ψ) :=
  Formula.realize_iff

end Sentence

namespace Formula

@[simp]
/--
theorem `realize_equivSentence_symm_con` / 定理 `realize_equivSentence_symm_con`

English:
theorem realize_equivSentence_symm_con
  statement: [L[[α]].Structure M]
  proof: by
  simp only [equivSentence, _root_.Equiv.symm_symm, Equiv.coe_trans, Realize,
    BoundedFormula.realize_relabelEquiv, Function.comp]
  refine _root_.trans ?_ BoundedFormula.realize_constantsVarsEquiv
  rw [iff_iff_eq]
  congr 1 with (_ | a)
  · simp
  · cases a

@[simp]

中文:
定理 realize_equivSentence_symm_con
  结论: [L[[α]].Structure M]
  证明: by
  simp only [equivSentence, _root_.Equiv.symm_symm, Equiv.coe_trans, Realize,
    BoundedFormula.realize_relabelEquiv, Function.comp]
  refine _root_.trans ?_ BoundedFormula.realize_constantsVarsEquiv
  rw [iff_iff_eq]
  congr 1 with (_ | a)
  · simp
  · cases a

@[simp]

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_constantsVarsEquiv, BoundedFormula.realize_relabelEquiv, Equiv.coe_trans, Function, Function.comp, Realize, _root_, _root_.Equiv.symm_symm, _root_.trans, coe_trans, equivSentence, iff_iff_eq, realize_constantsVarsEquiv, realize_relabelEquiv, symm_symm
-/
theorem realize_equivSentence_symm_con [L[[α]].Structure M]
    [(L.lhomWithConstants α).IsExpansionOn M] (φ : L[[α]].Sentence) :
    ((equivSentence.symm φ).Realize fun a => (L.con a : M)) ↔ φ.Realize M := by
  simp only [equivSentence, _root_.Equiv.symm_symm, Equiv.coe_trans, Realize,
    BoundedFormula.realize_relabelEquiv, Function.comp]
  refine _root_.trans ?_ BoundedFormula.realize_constantsVarsEquiv
  rw [iff_iff_eq]
  congr 1 with (_ | a)
  · simp
  · cases a

@[simp]
/--
theorem `realize_equivSentence` / 定理 `realize_equivSentence`

English:
theorem realize_equivSentence
  statement: [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M]
  proof: by
  rw [← realize_equivSentence_symm_con M (equivSentence φ)]; rw [_root_.Equiv.symm_apply_apply]

中文:
定理 realize_equivSentence
  结论: [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M]
  证明: by
  rw [← realize_equivSentence_symm_con M (equivSentence φ)]; rw [_root_.Equiv.symm_apply_apply]

Depends on / 依赖: _root_, _root_.Equiv.symm_apply_apply, equivSentence, realize_equivSentence_symm_con, symm_apply_apply
-/
theorem realize_equivSentence [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M]
    (φ : L.Formula α) : (equivSentence φ).Realize M ↔ φ.Realize fun a => (L.con a : M) := by
  rw [← realize_equivSentence_symm_con M (equivSentence φ)]; rw [_root_.Equiv.symm_apply_apply]

/--
theorem `realize_equivSentence_symm` / 定理 `realize_equivSentence_symm`

English:
theorem realize_equivSentence_symm
  given: (φ : L[[α]].Sentence) (v : α -> M)
  proof: letI := constantsOn.structure v
  realize_equivSentence_symm_con M φ

中文:
定理 realize_equivSentence_symm
  条件: (φ : L[[α]].Sentence) (v : α -> M)
  证明: letI := constantsOn.structure v
  realize_equivSentence_symm_con M φ

Depends on / 依赖: constantsOn, constantsOn.structure, realize_equivSentence_symm_con, structure
-/
theorem realize_equivSentence_symm (φ : L[[α]].Sentence) (v : α -> M) :
    (equivSentence.symm φ).Realize v ↔
      @Sentence.Realize _ M (@Language.withConstantsStructure L M _ α (constantsOn.structure v))
        φ :=
  letI := constantsOn.structure v
  realize_equivSentence_symm_con M φ

end Formula

@[simp]
/--
theorem `LHom.realize_onSentence` / 定理 `LHom.realize_onSentence`

English:
theorem LHom.realize_onSentence
  statement: [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M]
  proof: φ.realize_onFormula ψ

中文:
定理 LHom.realize_onSentence
  结论: [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M]
  证明: φ.realize_onFormula ψ

Depends on / 依赖: realize_onFormula
-/
theorem LHom.realize_onSentence [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M]
    (ψ : L.Sentence) : M ⊨ φ.onSentence ψ ↔ M ⊨ ψ :=
  φ.realize_onFormula ψ

variable (L)

/--
Definition of `completeTheory` / `completeTheory` 的定义

English:
definition completeTheory
  signature: : L.Theory
  body: { φ | M ⊨ φ }

中文:
定义 completeTheory
  签名: : L.Theory
  定义体: { φ | M ⊨ φ }
-/
def completeTheory : L.Theory :=
  { φ | M ⊨ φ }

variable (N)

/--
Definition of `ElementarilyEquivalent` / `ElementarilyEquivalent` 的定义

English:
definition ElementarilyEquivalent
  signature: : Prop
  body: L.completeTheory M = L.completeTheory N

@[inherit_doc FirstOrder.Language.ElementarilyEquivalent]
scoped[FirstOrder]
  notation:25 A " ≅[" L "] " B:50 => FirstOrder.Language.ElementarilyEquivalent L A B

中文:
定义 ElementarilyEquivalent
  签名: : 命题
  定义体: L.completeTheory M = L.completeTheory N

@[inherit_doc FirstOrder.Language.ElementarilyEquivalent]
scoped[FirstOrder]
  notation:25 A " ≅[" L "] " B:50 => FirstOrder.Language.ElementarilyEquivalent L A B

Depends on / 依赖: L.completeTheory, completeTheory
-/
def ElementarilyEquivalent : Prop :=
  L.completeTheory M = L.completeTheory N

@[inherit_doc FirstOrder.Language.ElementarilyEquivalent]
scoped[FirstOrder]
  notation:25 A " ≅[" L "] " B:50 => FirstOrder.Language.ElementarilyEquivalent L A B

variable {L} {M} {N}

@[simp]
/--
theorem `mem_completeTheory` / 定理 `mem_completeTheory`

English:
theorem mem_completeTheory
  given: {φ : Sentence L}
  statement: φ in L.completeTheory M ↔ M ⊨ φ
  proof: Iff.rfl

中文:
定理 mem_completeTheory
  条件: {φ : Sentence L}
  结论: φ in L.completeTheory M ↔ M ⊨ φ
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_completeTheory {φ : Sentence L} : φ in L.completeTheory M ↔ M ⊨ φ :=
  Iff.rfl

/--
theorem `elementarilyEquivalent_iff` / 定理 `elementarilyEquivalent_iff`

English:
theorem elementarilyEquivalent_iff
  statement: M ≅[L] N ↔ forall φ : L.Sentence, M ⊨ φ ↔ N ⊨ φ
  proof: by
  simp only [ElementarilyEquivalent, Set.ext_iff, completeTheory, Set.mem_ofPred_eq]

中文:
定理 elementarilyEquivalent_iff
  结论: M ≅[L] N ↔ 对任意 φ : L.Sentence, M ⊨ φ ↔ N ⊨ φ
  证明: by
  simp only [ElementarilyEquivalent, Set.ext_iff, completeTheory, Set.mem_ofPred_eq]

Depends on / 依赖: ElementarilyEquivalent, Set.ext_iff, Set.mem_ofPred_eq, completeTheory, ext_iff, mem_ofPred_eq
-/
theorem elementarilyEquivalent_iff : M ≅[L] N ↔ forall φ : L.Sentence, M ⊨ φ ↔ N ⊨ φ := by
  simp only [ElementarilyEquivalent, Set.ext_iff, completeTheory, Set.mem_ofPred_eq]

variable (M)

/--
Definition of `Theory.Model` / `Theory.Model` 的定义

English:
class Theory.Model
  parameters: (T : L.Theory)
  axioms and operations (1):
    - realize_of_mem : forall φ in T, M ⊨ φ

中文:
类 Theory.Model
  参数: (T : L.Theory)
  公理与运算 (1 个):
    - realize_of_mem : 对任意 φ in T, M ⊨ φ
-/
class Theory.Model (T : L.Theory) : Prop where
  realize_of_mem : forall φ in T, M ⊨ φ

-- input using \|= or \vDash, but not using \models
@[inherit_doc Theory.Model]
infixl:51 " ⊨ " => Theory.Model

variable {M} (T : L.Theory)

@[simp default - 10]
/--
theorem `Theory.model_iff` / 定理 `Theory.model_iff`

English:
theorem Theory.model_iff
  statement: M ⊨ T ↔ forall φ in T, M ⊨ φ
  proof: ⟨fun h => h.realize_of_mem, fun h => ⟨h⟩⟩

中文:
定理 Theory.model_iff
  结论: M ⊨ T ↔ 对任意 φ in T, M ⊨ φ
  证明: ⟨fun h => h.realize_of_mem, fun h => ⟨h⟩⟩

Depends on / 依赖: h.realize_of_mem, realize_of_mem
-/
theorem Theory.model_iff : M ⊨ T ↔ forall φ in T, M ⊨ φ :=
  ⟨fun h => h.realize_of_mem, fun h => ⟨h⟩⟩

/--
theorem `Theory.realize_sentence_of_mem` / 定理 `Theory.realize_sentence_of_mem`

English:
theorem Theory.realize_sentence_of_mem
  given: [M ⊨ T] {φ : L.Sentence} (h : φ in T)
  statement: M ⊨ φ
  proof: Theory.Model.realize_of_mem φ h

@[simp]

中文:
定理 Theory.realize_sentence_of_mem
  条件: [M ⊨ T] {φ : L.Sentence} (h : φ in T)
  结论: M ⊨ φ
  证明: Theory.Model.realize_of_mem φ h

@[simp]

Depends on / 依赖: Theory, Theory.Model.realize_of_mem, realize_of_mem
-/
theorem Theory.realize_sentence_of_mem [M ⊨ T] {φ : L.Sentence} (h : φ in T) : M ⊨ φ :=
  Theory.Model.realize_of_mem φ h

@[simp]
/--
theorem `LHom.onTheory_model` / 定理 `LHom.onTheory_model`

English:
theorem LHom.onTheory_model
  given: [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] (T : L.Theory)
  proof: by simp [Theory.model_iff, LHom.onTheory]

中文:
定理 LHom.onTheory_model
  条件: [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] (T : L.Theory)
  证明: by simp [Theory.model_iff, LHom.onTheory]

Depends on / 依赖: LHom.onTheory, Theory, Theory.model_iff, model_iff, onTheory
-/
theorem LHom.onTheory_model [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] (T : L.Theory) :
    M ⊨ φ.onTheory T ↔ M ⊨ T := by simp [Theory.model_iff, LHom.onTheory]

variable {T}

/--
Instance `model_empty` / 实例 `model_empty`

English:
instance model_empty
  signature: : M ⊨ (∅ : L.Theory)
  body: ⟨fun φ hφ => (Set.notMem_empty φ hφ).elim⟩

中文:
实例 model_empty
  签名: : M ⊨ (∅ : L.Theory)
  定义体: ⟨fun φ hφ => (Set.notMem_empty φ hφ).elim⟩

Depends on / 依赖: Set.notMem_empty, notMem_empty
-/
instance model_empty : M ⊨ (∅ : L.Theory) :=
  ⟨fun φ hφ => (Set.notMem_empty φ hφ).elim⟩

namespace Theory

/--
theorem `Model.mono` / 定理 `Model.mono`

English:
theorem Model.mono
  given: {T' : L.Theory} (_h : M ⊨ T') (hs : T subseteq T')
  statement: M ⊨ T
  proof: ⟨fun _φ hφ => T'.realize_sentence_of_mem (hs hφ)⟩

中文:
定理 Model.mono
  条件: {T' : L.Theory} (_h : M ⊨ T') (hs : T subseteq T')
  结论: M ⊨ T
  证明: ⟨fun _φ hφ => T'.realize_sentence_of_mem (hs hφ)⟩

Depends on / 依赖: realize_sentence_of_mem
-/
theorem Model.mono {T' : L.Theory} (_h : M ⊨ T') (hs : T subseteq T') : M ⊨ T :=
  ⟨fun _φ hφ => T'.realize_sentence_of_mem (hs hφ)⟩

/--
theorem `Model.union` / 定理 `Model.union`

English:
theorem Model.union
  given: {T' : L.Theory} (h : M ⊨ T) (h' : M ⊨ T')
  statement: M ⊨ T union T'
  proof: by
  simp only [model_iff, Set.mem_union] at *
  exact fun φ hφ => hφ.elim (h _) (h' _)

@[simp]

中文:
定理 Model.union
  条件: {T' : L.Theory} (h : M ⊨ T) (h' : M ⊨ T')
  结论: M ⊨ T union T'
  证明: by
  simp only [model_iff, Set.mem_union] at *
  exact fun φ hφ => hφ.elim (h _) (h' _)

@[simp]

Depends on / 依赖: Set.mem_union, mem_union, model_iff
-/
theorem Model.union {T' : L.Theory} (h : M ⊨ T) (h' : M ⊨ T') : M ⊨ T union T' := by
  simp only [model_iff, Set.mem_union] at *
  exact fun φ hφ => hφ.elim (h _) (h' _)

@[simp]
/--
theorem `model_union_iff` / 定理 `model_union_iff`

English:
theorem model_union_iff
  given: {T' : L.Theory}
  statement: M ⊨ T union T' ↔ M ⊨ T ∧ M ⊨ T'
  proof: ⟨fun h => ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩, fun h =>
    h.1.union h.2⟩

@[simp]

中文:
定理 model_union_iff
  条件: {T' : L.Theory}
  结论: M ⊨ T union T' ↔ M ⊨ T ∧ M ⊨ T'
  证明: ⟨fun h => ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩, fun h =>
    h.1.union h.2⟩

@[simp]

Depends on / 依赖: Set.subset_union_left, Set.subset_union_right, h.mono, subset_union_left, subset_union_right
-/
theorem model_union_iff {T' : L.Theory} : M ⊨ T union T' ↔ M ⊨ T ∧ M ⊨ T' :=
  ⟨fun h => ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩, fun h =>
    h.1.union h.2⟩

@[simp]
/--
theorem `model_singleton_iff` / 定理 `model_singleton_iff`

English:
theorem model_singleton_iff
  given: {φ : L.Sentence}
  statement: M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ
  proof: by simp

中文:
定理 model_singleton_iff
  条件: {φ : L.Sentence}
  结论: M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ
  证明: by simp
-/
theorem model_singleton_iff {φ : L.Sentence} : M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ := by simp

/--
theorem `model_insert_iff` / 定理 `model_insert_iff`

English:
theorem model_insert_iff
  given: {φ : L.Sentence}
  statement: M ⊨ insert φ T ↔ M ⊨ φ ∧ M ⊨ T
  proof: by
  rw [Set.insert_eq]; rw [model_union_iff]; rw [model_singleton_iff]

中文:
定理 model_insert_iff
  条件: {φ : L.Sentence}
  结论: M ⊨ insert φ T ↔ M ⊨ φ ∧ M ⊨ T
  证明: by
  rw [Set.insert_eq]; rw [model_union_iff]; rw [model_singleton_iff]

Depends on / 依赖: Set.insert_eq, insert_eq, model_singleton_iff, model_union_iff
-/
theorem model_insert_iff {φ : L.Sentence} : M ⊨ insert φ T ↔ M ⊨ φ ∧ M ⊨ T := by
  rw [Set.insert_eq]; rw [model_union_iff]; rw [model_singleton_iff]

/--
theorem `model_iff_subset_completeTheory` / 定理 `model_iff_subset_completeTheory`

English:
theorem model_iff_subset_completeTheory
  statement: M ⊨ T ↔ T subseteq L.completeTheory M
  proof: T.model_iff

中文:
定理 model_iff_subset_completeTheory
  结论: M ⊨ T ↔ T subseteq L.completeTheory M
  证明: T.model_iff

Depends on / 依赖: T.model_iff, model_iff
-/
theorem model_iff_subset_completeTheory : M ⊨ T ↔ T subseteq L.completeTheory M :=
  T.model_iff

/--
theorem `completeTheory.subset` / 定理 `completeTheory.subset`

English:
theorem completeTheory.subset
  given: [MT : M ⊨ T]
  statement: T subseteq L.completeTheory M
  proof: model_iff_subset_completeTheory.1 MT

中文:
定理 completeTheory.subset
  条件: [MT : M ⊨ T]
  结论: T subseteq L.completeTheory M
  证明: model_iff_subset_completeTheory.1 MT

Depends on / 依赖: model_iff_subset_completeTheory
-/
theorem completeTheory.subset [MT : M ⊨ T] : T subseteq L.completeTheory M :=
  model_iff_subset_completeTheory.1 MT

end Theory

/--
Instance `model_completeTheory` / 实例 `model_completeTheory`

English:
instance model_completeTheory
  signature: : M ⊨ L.completeTheory M
  body: Theory.model_iff_subset_completeTheory.2 subset_rfl

中文:
实例 model_completeTheory
  签名: : M ⊨ L.completeTheory M
  定义体: Theory.model_iff_subset_completeTheory.2 subset_rfl

Depends on / 依赖: Theory, Theory.model_iff_subset_completeTheory, model_iff_subset_completeTheory, subset_rfl
-/
instance model_completeTheory : M ⊨ L.completeTheory M :=
  Theory.model_iff_subset_completeTheory.2 subset_rfl

variable (M N)

/--
theorem `realize_iff_of_model_completeTheory` / 定理 `realize_iff_of_model_completeTheory`

English:
theorem realize_iff_of_model_completeTheory
  given: [N ⊨ L.completeTheory M] (φ : L.Sentence)
  proof: by
  refine ⟨fun h => ?_, (L.completeTheory M).realize_sentence_of_mem⟩
  contrapose h
  rw [← Sentence.realize_not] at *
  exact (L.completeTheory M).realize_sentence_of_mem (mem_completeTheory.2 h)

中文:
定理 realize_iff_of_model_completeTheory
  条件: [N ⊨ L.completeTheory M] (φ : L.Sentence)
  证明: by
  refine ⟨fun h => ?_, (L.completeTheory M).realize_sentence_of_mem⟩
  contrapose h
  rw [← Sentence.realize_not] at *
  exact (L.completeTheory M).realize_sentence_of_mem (mem_completeTheory.2 h)

Depends on / 依赖: L.completeTheory, Sentence, Sentence.realize_not, completeTheory, contrapose, mem_completeTheory, realize_not, realize_sentence_of_mem
-/
theorem realize_iff_of_model_completeTheory [N ⊨ L.completeTheory M] (φ : L.Sentence) :
    N ⊨ φ ↔ M ⊨ φ := by
  refine ⟨fun h => ?_, (L.completeTheory M).realize_sentence_of_mem⟩
  contrapose h
  rw [← Sentence.realize_not] at *
  exact (L.completeTheory M).realize_sentence_of_mem (mem_completeTheory.2 h)

variable {M N}

namespace BoundedFormula

@[simp]
/--
theorem `realize_alls` / 定理 `realize_alls`

English:
theorem realize_alls
  given: {φ : L.BoundedFormula α n} {v : α -> M}
  proof: by
  induction n with
  | zero => exact Unique.forall_iff.symm
  | succ n ih =>
    simp only [alls, ih, Realize]
    exact ⟨fun h xs => Fin.snoc_init_self xs ▸ h _ _, fun h xs x => h (Fin.snoc xs x)⟩

@[simp]

中文:
定理 realize_alls
  条件: {φ : L.BoundedFormula α n} {v : α -> M}
  证明: by
  induction n with
  | zero => exact Unique.forall_iff.symm
  | succ n ih =>
    simp only [alls, ih, Realize]
    exact ⟨fun h xs => Fin.snoc_init_self xs ▸ h _ _, fun h xs x => h (Fin.snoc xs x)⟩

@[simp]

Depends on / 依赖: Fin.snoc, Fin.snoc_init_self, Realize, Unique, Unique.forall_iff.symm, forall_iff, snoc_init_self
-/
theorem realize_alls {φ : L.BoundedFormula α n} {v : α -> M} :
    φ.alls.Realize v ↔ forall xs : Fin n -> M, φ.Realize v xs := by
  induction n with
  | zero => exact Unique.forall_iff.symm
  | succ n ih =>
    simp only [alls, ih, Realize]
    exact ⟨fun h xs => Fin.snoc_init_self xs ▸ h _ _, fun h xs x => h (Fin.snoc xs x)⟩

@[simp]
/--
theorem `realize_exs` / 定理 `realize_exs`

English:
theorem realize_exs
  given: {φ : L.BoundedFormula α n} {v : α -> M}
  proof: by
  induction n with
  | zero => exact Unique.exists_iff.symm
  | succ n ih =>
    simp only [BoundedFormula.exs, ih, realize_ex]
    constructor
    · rintro ⟨xs, x, h⟩
      exact ⟨_, h⟩
    · rintro ⟨xs, h⟩
      rw [← Fin.snoc_init_self xs] at h
      exact ⟨_, _, h⟩

@[simp]

中文:
定理 realize_exs
  条件: {φ : L.BoundedFormula α n} {v : α -> M}
  证明: by
  induction n with
  | zero => exact Unique.exists_iff.symm
  | succ n ih =>
    simp only [BoundedFormula.exs, ih, realize_ex]
    constructor
    · rintro ⟨xs, x, h⟩
      exact ⟨_, h⟩
    · rintro ⟨xs, h⟩
      rw [← Fin.snoc_init_self xs] at h
      exact ⟨_, _, h⟩

@[simp]

Depends on / 依赖: BoundedFormula, BoundedFormula.exs, Fin.snoc_init_self, Unique, Unique.exists_iff.symm, exists_iff, realize_ex, snoc_init_self
-/
theorem realize_exs {φ : L.BoundedFormula α n} {v : α -> M} :
    φ.exs.Realize v ↔ exists xs : Fin n -> M, φ.Realize v xs := by
  induction n with
  | zero => exact Unique.exists_iff.symm
  | succ n ih =>
    simp only [BoundedFormula.exs, ih, realize_ex]
    constructor
    · rintro ⟨xs, x, h⟩
      exact ⟨_, h⟩
    · rintro ⟨xs, h⟩
      rw [← Fin.snoc_init_self xs] at h
      exact ⟨_, _, h⟩

@[simp]
/--
theorem `_root_.FirstOrder.Language.Formula.realize_iAlls` / 定理 `_root_.FirstOrder.Language.Formula.realize_iAlls`

English:
theorem _root_.FirstOrder.Language.Formula.realize_iAlls
  proof: by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  rw [Formula.iAlls]
  simp only [Nat.add_zero, realize_alls, realize_relabel, Function.comp_def,
    castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.forall_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm

中文:
定理 _root_.FirstOrder.Language.Formula.realize_iAlls
  证明: by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  rw [Formula.iAlls]
  simp only [Nat.add_zero, realize_alls, realize_relabel, Function.comp_def,
    castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.forall_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm

Depends on / 依赖: Classical, Classical.choice, Classical.choose_spec, Equiv.forall_congr, Finite, Finite.exists_equiv_fin, Formula, Formula.Realize, Formula.iAlls, Function, Function.comp_def, Nat.add_zero, Realize, Sum.elim_map, add_zero, castAdd_zero, choice, choose_spec, comp_def, e.symm
-/
theorem _root_.FirstOrder.Language.Formula.realize_iAlls
    [Finite β] {φ : L.Formula (α oplus β)} {v : α -> M} : (φ.iAlls β).Realize v ↔
      forall (i : β -> M), φ.Realize (fun a => Sum.elim v i a) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  rw [Formula.iAlls]
  simp only [Nat.add_zero, realize_alls, realize_relabel, Function.comp_def,
    castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.forall_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,
      fun _ => by simp [Function.comp_def],
      fun _ => by simp [Function.comp_def]⟩
  · intro x
    rw [Formula.Realize]; rw [iff_iff_eq]
    congr
    funext i
    exact i.elim0

@[simp]
/--
theorem `realize_iAlls` / 定理 `realize_iAlls`

English:
theorem realize_iAlls
  given: [Finite β] {φ : L.Formula (α oplus β)} {v : α -> M} {v' : Fin 0 -> M}
  proof: by
  rw [← Formula.realize_iAlls]; rw [iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]

中文:
定理 realize_iAlls
  条件: [Finite β] {φ : L.Formula (α oplus β)} {v : α -> M} {v' : Fin 0 -> M}
  证明: by
  rw [← Formula.realize_iAlls]; rw [iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]

Depends on / 依赖: Formula, Formula.realize_iAlls, eq_iff_true_of_subsingleton, iff_iff_eq, realize_iAlls
-/
theorem realize_iAlls [Finite β] {φ : L.Formula (α oplus β)} {v : α -> M} {v' : Fin 0 -> M} :
    BoundedFormula.Realize (φ.iAlls β) v v' ↔
      forall (i : β -> M), φ.Realize (fun a => Sum.elim v i a) := by
  rw [← Formula.realize_iAlls]; rw [iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]
/--
theorem `_root_.FirstOrder.Language.Formula.realize_iExs` / 定理 `_root_.FirstOrder.Language.Formula.realize_iExs`

English:
theorem _root_.FirstOrder.Language.Formula.realize_iExs
  proof: by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  rw [Formula.iExs]
  simp only [Nat.add_zero, realize_exs, realize_relabel, Function.comp_def,
    castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.exists_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,


中文:
定理 _root_.FirstOrder.Language.Formula.realize_iExs
  证明: by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  rw [Formula.iExs]
  simp only [Nat.add_zero, realize_exs, realize_relabel, Function.comp_def,
    castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.exists_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,


Depends on / 依赖: Classical, Classical.choice, Classical.choose_spec, Equiv.exists_congr, Finite, Finite.exists_equiv_fin, Formula, Formula.Realize, Formula.iExs, Function, Function.comp_def, Nat.add_zero, Realize, Sum.elim_map, add_zero, castAdd_zero, choice, choose_spec, comp_def, e.symm
-/
theorem _root_.FirstOrder.Language.Formula.realize_iExs
    [Finite γ] {φ : L.Formula (α oplus γ)} {v : α -> M} : (φ.iExs γ).Realize v ↔
      exists (i : γ -> M), φ.Realize (Sum.elim v i) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  rw [Formula.iExs]
  simp only [Nat.add_zero, realize_exs, realize_relabel, Function.comp_def,
    castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.exists_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,
      fun _ => by simp [Function.comp_def],
      fun _ => by simp [Function.comp_def]⟩
  · intro x
    rw [Formula.Realize]; rw [iff_iff_eq]
    congr
    funext i
    exact i.elim0

@[simp]
/--
theorem `realize_iExs` / 定理 `realize_iExs`

English:
theorem realize_iExs
  given: [Finite γ] {φ : L.Formula (α oplus γ)} {v : α -> M} {v' : Fin 0 -> M}
  proof: by
  rw [← Formula.realize_iExs]; rw [iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]

中文:
定理 realize_iExs
  条件: [Finite γ] {φ : L.Formula (α oplus γ)} {v : α -> M} {v' : Fin 0 -> M}
  证明: by
  rw [← Formula.realize_iExs]; rw [iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]

Depends on / 依赖: Formula, Formula.realize_iExs, eq_iff_true_of_subsingleton, iff_iff_eq, realize_iExs
-/
theorem realize_iExs [Finite γ] {φ : L.Formula (α oplus γ)} {v : α -> M} {v' : Fin 0 -> M} :
    BoundedFormula.Realize (φ.iExs γ) v v' ↔
      exists (i : γ -> M), φ.Realize (Sum.elim v i) := by
  rw [← Formula.realize_iExs]; rw [iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]
/--
theorem `realize_toFormula` / 定理 `realize_toFormula`

English:
theorem realize_toFormula
  given: (φ : L.BoundedFormula α n) (v : α oplus (Fin n) -> M)
  proof: by
  induction φ with
  | falsum => rfl
  | equal => simp [BoundedFormula.Realize]
  | rel => simp [BoundedFormula.Realize]
  | imp _ _ ih1 ih2 =>
    rw [toFormula]; rw [Formula.Realize]; rw [realize_imp]; rw [← Formula.Realize]; rw [ih1]; rw [← Formula.Realize]; rw [ih2]; rw [realize_imp]
  | all 

中文:
定理 realize_toFormula
  条件: (φ : L.BoundedFormula α n) (v : α oplus (Fin n) -> M)
  证明: by
  induction φ with
  | falsum => rfl
  | equal => simp [BoundedFormula.Realize]
  | rel => simp [BoundedFormula.Realize]
  | imp _ _ ih1 ih2 =>
    rw [toFormula]; rw [Formula.Realize]; rw [realize_imp]; rw [← Formula.Realize]; rw [ih1]; rw [← Formula.Realize]; rw [ih2]; rw [realize_imp]
  | all 

Depends on / 依赖: BoundedFormula, BoundedFormula.Realize, Formula, Formula.Realize, Realize, Sum.elim, Sum.elim_, Sum.elim_comp_inl, Sum.inl, Sum.inr, elim_, elim_comp_inl, falsum, forall_congr, realize_all, realize_imp, toFormula
-/
theorem realize_toFormula (φ : L.BoundedFormula α n) (v : α oplus (Fin n) -> M) :
    φ.toFormula.Realize v ↔ φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr) := by
  induction φ with
  | falsum => rfl
  | equal => simp [BoundedFormula.Realize]
  | rel => simp [BoundedFormula.Realize]
  | imp _ _ ih1 ih2 =>
    rw [toFormula]; rw [Formula.Realize]; rw [realize_imp]; rw [← Formula.Realize]; rw [ih1]; rw [← Formula.Realize]; rw [ih2]; rw [realize_imp]
  | all _ ih3 =>
    rw [toFormula]; rw [Formula.Realize]; rw [realize_all]; rw [realize_all]
    refine forall_congr' fun a => ?_
    have h := ih3 (Sum.elim (v ∘ Sum.inl) (snoc (v ∘ Sum.inr) a))
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
    rw [← h]; rw [realize_relabel]; rw [Formula.Realize]; rw [iff_iff_eq]
    simp only [Function.comp_def]
    congr with x
    · rcases x with _ | x
      · simp
      · refine Fin.lastCases ?_ ?_ x
        · simp [Fin.snoc]
        · simp only [castSucc, Sum.elim_inr,
            finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, Sum.elim_inl]
          rw [← castSucc]
          simp
    · exact Fin.elim0 x

@[simp]
/--
theorem `realize_iSup` / 定理 `realize_iSup`

English:
theorem realize_iSup
  statement: [Finite β] {f : β -> L.BoundedFormula α n}
  proof: by
  simp only [iSup, realize_foldr_sup, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    exists_exists_eq_and]

@[simp]

中文:
定理 realize_iSup
  结论: [Finite β] {f : β -> L.BoundedFormula α n}
  证明: by
  simp only [iSup, realize_foldr_sup, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    exists_exists_eq_and]

@[simp]

Depends on / 依赖: Finset, Finset.mem_toList, Finset.mem_univ, List.mem_map, exists_exists_eq_and, mem_map, mem_toList, mem_univ, realize_foldr_sup, true_and
-/
theorem realize_iSup [Finite β] {f : β -> L.BoundedFormula α n}
    {v : α -> M} {v' : Fin n -> M} :
    (iSup f).Realize v v' ↔ exists b, (f b).Realize v v' := by
  simp only [iSup, realize_foldr_sup, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    exists_exists_eq_and]

@[simp]
/--
theorem `realize_iInf` / 定理 `realize_iInf`

English:
theorem realize_iInf
  statement: [Finite β] {f : β -> L.BoundedFormula α n}
  proof: by
  simp only [iInf, realize_foldr_inf, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]

@[simp]

中文:
定理 realize_iInf
  结论: [Finite β] {f : β -> L.BoundedFormula α n}
  证明: by
  simp only [iInf, realize_foldr_inf, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]

@[simp]

Depends on / 依赖: Finset, Finset.mem_toList, Finset.mem_univ, List.mem_map, forall_apply_eq_imp_iff, forall_exists_index, mem_map, mem_toList, mem_univ, realize_foldr_inf, true_and
-/
theorem realize_iInf [Finite β] {f : β -> L.BoundedFormula α n}
    {v : α -> M} {v' : Fin n -> M} :
    (iInf f).Realize v v' ↔ forall b, (f b).Realize v v' := by
  simp only [iInf, realize_foldr_inf, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]

@[simp]
/--
theorem `_root_.FirstOrder.Language.Formula.realize_iSup` / 定理 `_root_.FirstOrder.Language.Formula.realize_iSup`

English:
theorem _root_.FirstOrder.Language.Formula.realize_iSup
  statement: [Finite β] {f : β -> L.Formula α}
  proof: by
  simp [Formula.iSup, Formula.Realize]

@[simp]

中文:
定理 _root_.FirstOrder.Language.Formula.realize_iSup
  结论: [Finite β] {f : β -> L.Formula α}
  证明: by
  simp [Formula.iSup, Formula.Realize]

@[simp]

Depends on / 依赖: Formula, Formula.Realize, Formula.iSup, Realize
-/
theorem _root_.FirstOrder.Language.Formula.realize_iSup [Finite β] {f : β -> L.Formula α}
    {v : α -> M} : (Formula.iSup f).Realize v ↔ exists b, (f b).Realize v := by
  simp [Formula.iSup, Formula.Realize]

@[simp]
/--
theorem `_root_.FirstOrder.Language.Formula.realize_iInf` / 定理 `_root_.FirstOrder.Language.Formula.realize_iInf`

English:
theorem _root_.FirstOrder.Language.Formula.realize_iInf
  statement: [Finite β] {f : β -> L.Formula α}
  proof: by
  simp [Formula.iInf, Formula.Realize]

中文:
定理 _root_.FirstOrder.Language.Formula.realize_iInf
  结论: [Finite β] {f : β -> L.Formula α}
  证明: by
  simp [Formula.iInf, Formula.Realize]

Depends on / 依赖: Formula, Formula.Realize, Formula.iInf, Realize
-/
theorem _root_.FirstOrder.Language.Formula.realize_iInf [Finite β] {f : β -> L.Formula α}
    {v : α -> M} : (Formula.iInf f).Realize v ↔ forall b, (f b).Realize v := by
  simp [Formula.iInf, Formula.Realize]

/--
theorem `_root_.FirstOrder.Language.Formula.realize_iExsUnique` / 定理 `_root_.FirstOrder.Language.Formula.realize_iExsUnique`

English:
theorem _root_.FirstOrder.Language.Formula.realize_iExsUnique
  statement: [Finite γ]
  proof: by
  rw [Formula.iExsUnique]; rw [ExistsUnique]
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_relabel]
  simp only [Formula.Realize, Function.comp_def, Term.equal, Term.relabel, realize_iInf,
    realize_bdEqual, Term.realize_

中文:
定理 _root_.FirstOrder.Language.Formula.realize_iExsUnique
  结论: [Finite γ]
  证明: by
  rw [Formula.iExsUnique]; rw [ExistsUnique]
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_relabel]
  simp only [Formula.Realize, Function.comp_def, Term.equal, Term.relabel, realize_iInf,
    realize_bdEqual, Term.realize_

Depends on / 依赖: ExistsUnique, Formula, Formula.Realize, Formula.iExsUnique, Formula.realize_iAlls, Formula.realize_iExs, Formula.realize_imp, Formula.realize_inf, Formula.realize_relabel, Function, Function.comp_def, Realize, Sum.elim_inl, Sum.elim_inr, Term.equal, Term.realize_var, Term.relabel, and_congr_right, comp_def, elim_inl
-/
theorem _root_.FirstOrder.Language.Formula.realize_iExsUnique [Finite γ]
    {φ : L.Formula (α oplus γ)} {v : α -> M} : (φ.iExsUnique γ).Realize v ↔
      exists! (i : γ -> M), φ.Realize (Sum.elim v i) := by
  rw [Formula.iExsUnique]; rw [ExistsUnique]
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_relabel]
  simp only [Formula.Realize, Function.comp_def, Term.equal, Term.relabel, realize_iInf,
    realize_bdEqual, Term.realize_var, Sum.elim_inl, Sum.elim_inr, funext_iff]
  refine exists_congr (fun i => and_congr_right' (forall_congr' (fun y => ?_)))
  rw [iff_iff_eq]; congr with x
  cases x <;> simp

@[simp]
/--
theorem `realize_iExsUnique` / 定理 `realize_iExsUnique`

English:
theorem realize_iExsUnique
  given: [Finite γ] {φ : L.Formula (α oplus γ)} {v : α -> M} {v' : Fin 0 -> M}
  proof: by
  rw [← Formula.realize_iExsUnique]; rw [iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

中文:
定理 realize_iExsUnique
  条件: [Finite γ] {φ : L.Formula (α oplus γ)} {v : α -> M} {v' : Fin 0 -> M}
  证明: by
  rw [← Formula.realize_iExsUnique]; rw [iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

Depends on / 依赖: Formula, Formula.realize_iExsUnique, eq_iff_true_of_subsingleton, iff_iff_eq, realize_iExsUnique
-/
theorem realize_iExsUnique [Finite γ] {φ : L.Formula (α oplus γ)} {v : α -> M} {v' : Fin 0 -> M} :
    BoundedFormula.Realize (φ.iExsUnique γ) v v' ↔
      exists! (i : γ -> M), φ.Realize (Sum.elim v i) := by
  rw [← Formula.realize_iExsUnique]; rw [iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

end BoundedFormula

namespace Formula

@[simp]
/--
theorem `realize_exClosure` / 定理 `realize_exClosure`

English:
theorem realize_exClosure
  given: [DecidableEq α] (φ : L.Formula α)
  proof: by
  simp [Sentence.Realize, Formula.exClosure, Formula.realize_iExs]

中文:
定理 realize_exClosure
  条件: [DecidableEq α] (φ : L.Formula α)
  证明: by
  simp [Sentence.Realize, Formula.exClosure, Formula.realize_iExs]

Depends on / 依赖: Countable, Formula, Formula.exClosure, Formula.realize_iExs, Preorder, Realize, Sentence, Sentence.Realize, atTop.isCountablyGenerated, exClosure, isCountablyGenerated, realize_iExs
-/
theorem realize_exClosure [DecidableEq α] (φ : L.Formula α) :
    φ.exClosure.Realize M ↔
      exists v : φ.freeVarFinset -> M, Formula.Realize (φ.restrictFreeVar id) v := by
  simp [Sentence.Realize, Formula.exClosure, Formula.realize_iExs]

/--
theorem `realize_exClosure_of_realize_equivSentence` / 定理 `realize_exClosure_of_realize_equivSentence`

English:
theorem realize_exClosure_of_realize_equivSentence
  statement: [DecidableEq α] [L[[α]].Structure M]
  proof: by
  rw [Formula.realize_exClosure]
  exists fun a => (L.con (a : α) : M)
  simpa [Formula.Realize, BoundedFormula.realize_restrictFreeVar] using h

中文:
定理 realize_exClosure_of_realize_equivSentence
  结论: [DecidableEq α] [L[[α]].Structure M]
  证明: by
  rw [Formula.realize_exClosure]
  exists fun a => (L.con (a : α) : M)
  simpa [Formula.Realize, BoundedFormula.realize_restrictFreeVar] using h

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_restrictFreeVar, Countable, Formula, Formula.Realize, Formula.realize_exClosure, L.con, Preorder, Realize, atBot.isCountablyGenerated, isCountablyGenerated, realize_exClosure, realize_restrictFreeVar
-/
theorem realize_exClosure_of_realize_equivSentence [DecidableEq α] [L[[α]].Structure M]
    [(L.lhomWithConstants α).IsExpansionOn M] {φ : L.Formula α}
    (h : (Formula.equivSentence φ).Realize M) : φ.exClosure.Realize M := by
  rw [Formula.realize_exClosure]
  exists fun a => (L.con (a : α) : M)
  simpa [Formula.Realize, BoundedFormula.realize_restrictFreeVar] using h

/--
theorem `exists_realize_equivSentence_iff_realize_exClosure` / 定理 `exists_realize_equivSentence_iff_realize_exClosure`

English:
theorem exists_realize_equivSentence_iff_realize_exClosure
  proof: by
  constructor
  · rintro ⟨v, hv⟩
    exact (Formula.realize_exClosure φ).mpr ⟨fun a => v a,
      (BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id) (v := fun a => v a) (v' := v)
        (fun _ => rfl)).2
        (by simpa [Formula.Realize]
          using (realize_equivSentence_symm M (F

中文:
定理 exists_realize_equivSentence_iff_realize_exClosure
  证明: by
  constructor
  · rintro ⟨v, hv⟩
    exact (Formula.realize_exClosure φ).mpr ⟨fun a => v a,
      (BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id) (v := fun a => v a) (v' := v)
        (fun _ => rfl)).2
        (by simpa [Formula.Realize]
          using (realize_equivSentence_symm M (F

Depends on / 依赖: constantsOn, constantsOn.structure, structure
-/
theorem exists_realize_equivSentence_iff_realize_exClosure
    [DecidableEq α] [Nonempty M] {φ : L.Formula α} :
    (exists v : α -> M,
      letI := (constantsOn.structure v);
      (Formula.equivSentence φ).Realize M) ↔ (φ.exClosure.Realize M) := by
  constructor
  · rintro ⟨v, hv⟩
    exact (Formula.realize_exClosure φ).mpr ⟨fun a => v a,
      (BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id) (v := fun a => v a) (v' := v)
        (fun _ => rfl)).2
        (by simpa [Formula.Realize]
          using (realize_equivSentence_symm M (Formula.equivSentence φ) v).2 hv)⟩
  · intro h
    obtain ⟨v, hv⟩ := (Formula.realize_exClosure φ).1 h
    let v' := fun a => if hmem : a in φ.freeVarFinset
      then v ⟨a, hmem⟩ else Classical.choice inferInstance
    exists v'
    refine (Formula.realize_equivSentence_symm M (Formula.equivSentence φ) v').mp ?_
    simpa [Equiv.symm_apply_apply, Formula.Realize] using
      (BoundedFormula.realize_restrictFreeVar v' (by grind)).1 hv

end Formula

namespace StrongHomClass

variable {F : Type*} [EquivLike F M N] [StrongHomClass L F M N] (g : F)

@[simp]
/--
theorem `realize_boundedFormula` / 定理 `realize_boundedFormula`

English:
theorem realize_boundedFormula
  statement: (φ : L.BoundedFormula α n) {v : α -> M}
  proof: by
  induction φ with
  | falsum => rfl
  | equal =>
    simp only [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term,
      EmbeddingLike.apply_eq_iff_eq g]
  | rel =>
    simp only [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
    exact StrongHomClass.map_rel g _ _


中文:
定理 realize_boundedFormula
  结论: (φ : L.BoundedFormula α n) {v : α -> M}
  证明: by
  induction φ with
  | falsum => rfl
  | equal =>
    simp only [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term,
      EmbeddingLike.apply_eq_iff_eq g]
  | rel =>
    simp only [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
    exact StrongHomClass.map_rel g _ _


Depends on / 依赖: BoundedFormula, BoundedFormula.Realize, EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Fin.comp_snoc, HomClass, HomClass.realize_term, Realize, StrongHomClass, StrongHomClass.map_rel, Sum.comp_elim, apply_eq_iff_eq, comp_elim, comp_snoc, falsum, map_rel, realize_term
-/
theorem realize_boundedFormula (φ : L.BoundedFormula α n) {v : α -> M}
    {xs : Fin n -> M} : φ.Realize (g ∘ v) (g ∘ xs) ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal =>
    simp only [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term,
      EmbeddingLike.apply_eq_iff_eq g]
  | rel =>
    simp only [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
    exact StrongHomClass.map_rel g _ _
  | imp _ _ ih1 ih2 => rw [BoundedFormula.Realize, ih1, ih2, BoundedFormula.Realize]
  | all _ ih3 =>
    rw [BoundedFormula.Realize]; rw [BoundedFormula.Realize]
    constructor
    · intro h a
      have h' := h (g a)
      rw [← Fin.comp_snoc]; rw [ih3] at h'
      exact h'
    · intro h a
      have h' := h (EquivLike.inv g a)
      rw [← ih3]; rw [Fin.comp_snoc]; rw [EquivLike.apply_inv_apply g] at h'
      exact h'

@[simp]
/--
theorem `realize_formula` / 定理 `realize_formula`

English:
theorem realize_formula
  given: (φ : L.Formula α) {v : α -> M}
  proof: by
  rw [Formula.Realize]; rw [Formula.Realize]; rw [← realize_boundedFormula g φ]; rw [iff_eq_eq]; rw [Unique.eq_default (g ∘ default)]

include g

中文:
定理 realize_formula
  条件: (φ : L.Formula α) {v : α -> M}
  证明: by
  rw [Formula.Realize]; rw [Formula.Realize]; rw [← realize_boundedFormula g φ]; rw [iff_eq_eq]; rw [Unique.eq_default (g ∘ default)]

include g

Depends on / 依赖: Formula, Formula.Realize, Realize, Unique, Unique.eq_default, eq_default, iff_eq_eq, realize_boundedFormula
-/
theorem realize_formula (φ : L.Formula α) {v : α -> M} :
    φ.Realize (g ∘ v) ↔ φ.Realize v := by
  rw [Formula.Realize]; rw [Formula.Realize]; rw [← realize_boundedFormula g φ]; rw [iff_eq_eq]; rw [Unique.eq_default (g ∘ default)]

include g

/--
theorem `realize_sentence` / 定理 `realize_sentence`

English:
theorem realize_sentence
  given: (φ : L.Sentence)
  statement: M ⊨ φ ↔ N ⊨ φ
  proof: by
  rw [Sentence.Realize]; rw [Sentence.Realize]; rw [← realize_formula g]; rw [Unique.eq_default (g ∘ default)]

中文:
定理 realize_sentence
  条件: (φ : L.Sentence)
  结论: M ⊨ φ ↔ N ⊨ φ
  证明: by
  rw [Sentence.Realize]; rw [Sentence.Realize]; rw [← realize_formula g]; rw [Unique.eq_default (g ∘ default)]

Depends on / 依赖: Realize, Sentence, Sentence.Realize, Unique, Unique.eq_default, eq_default, realize_formula
-/
theorem realize_sentence (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  rw [Sentence.Realize]; rw [Sentence.Realize]; rw [← realize_formula g]; rw [Unique.eq_default (g ∘ default)]

/--
theorem `theory_model` / 定理 `theory_model`

English:
theorem theory_model
  given: [M ⊨ T]
  statement: N ⊨ T
  proof: ⟨fun φ hφ => (realize_sentence g φ).1 (Theory.realize_sentence_of_mem T hφ)⟩

中文:
定理 theory_model
  条件: [M ⊨ T]
  结论: N ⊨ T
  证明: ⟨fun φ hφ => (realize_sentence g φ).1 (Theory.realize_sentence_of_mem T hφ)⟩

Depends on / 依赖: Theory, Theory.realize_sentence_of_mem, realize_sentence, realize_sentence_of_mem
-/
theorem theory_model [M ⊨ T] : N ⊨ T :=
  ⟨fun φ hφ => (realize_sentence g φ).1 (Theory.realize_sentence_of_mem T hφ)⟩

/--
theorem `elementarilyEquivalent` / 定理 `elementarilyEquivalent`

English:
theorem elementarilyEquivalent
  statement: M ≅[L] N
  proof: elementarilyEquivalent_iff.2 (realize_sentence g)

中文:
定理 elementarilyEquivalent
  结论: M ≅[L] N
  证明: elementarilyEquivalent_iff.2 (realize_sentence g)

Depends on / 依赖: elementarilyEquivalent_iff, realize_sentence
-/
theorem elementarilyEquivalent : M ≅[L] N :=
  elementarilyEquivalent_iff.2 (realize_sentence g)

end StrongHomClass

namespace Relations

open BoundedFormula

variable {r : L.Relations 2}

@[simp]
/--
theorem `realize_reflexive` / 定理 `realize_reflexive`

English:
theorem realize_reflexive
  statement: M ⊨ r.reflexive ↔ Std.Refl fun x y : M => RelMap r ![x, y]
  proof: by
  rw [refl_def]
  exact forall_congr' fun _ => realize_rel₂

@[simp]

中文:
定理 realize_reflexive
  结论: M ⊨ r.reflexive ↔ Std.Refl fun x y : M => RelMap r ![x, y]
  证明: by
  rw [refl_def]
  exact forall_congr' fun _ => realize_rel₂

@[simp]

Depends on / 依赖: forall_congr, refl_def
-/
theorem realize_reflexive : M ⊨ r.reflexive ↔ Std.Refl fun x y : M => RelMap r ![x, y] := by
  rw [refl_def]
  exact forall_congr' fun _ => realize_rel₂

@[simp]
/--
theorem `realize_irreflexive` / 定理 `realize_irreflexive`

English:
theorem realize_irreflexive
  statement: M ⊨ r.irreflexive ↔ Std.Irrefl fun x y : M => RelMap r ![x, y]
  proof: by
  rw [irrefl_def]
  exact forall_congr' fun _ => not_congr realize_rel₂

@[simp]

中文:
定理 realize_irreflexive
  结论: M ⊨ r.irreflexive ↔ Std.Irrefl fun x y : M => RelMap r ![x, y]
  证明: by
  rw [irrefl_def]
  exact forall_congr' fun _ => not_congr realize_rel₂

@[simp]

Depends on / 依赖: forall_congr, irrefl_def, not_congr
-/
theorem realize_irreflexive : M ⊨ r.irreflexive ↔ Std.Irrefl fun x y : M => RelMap r ![x, y] := by
  rw [irrefl_def]
  exact forall_congr' fun _ => not_congr realize_rel₂

@[simp]
/--
theorem `realize_symmetric` / 定理 `realize_symmetric`

English:
theorem realize_symmetric
  statement: M ⊨ r.symmetric ↔ Std.Symm fun x y : M => RelMap r ![x, y]
  proof: by
  rw [symm_def]
  exact forall₂_congr fun _ _ => imp_congr realize_rel₂ realize_rel₂

@[simp]

中文:
定理 realize_symmetric
  结论: M ⊨ r.symmetric ↔ Std.Symm fun x y : M => RelMap r ![x, y]
  证明: by
  rw [symm_def]
  exact forall₂_congr fun _ _ => imp_congr realize_rel₂ realize_rel₂

@[simp]

Depends on / 依赖: imp_congr, symm_def
-/
theorem realize_symmetric : M ⊨ r.symmetric ↔ Std.Symm fun x y : M => RelMap r ![x, y] := by
  rw [symm_def]
  exact forall₂_congr fun _ _ => imp_congr realize_rel₂ realize_rel₂

@[simp]
/--
theorem `realize_antisymmetric` / 定理 `realize_antisymmetric`

English:
theorem realize_antisymmetric
  proof: by
  rw [antisymm_def]
exact forall₂_congr fun _ _ => imp_congr realize_rel₂ imp_congr realize_rel₂ .rfl

@[simp]

中文:
定理 realize_antisymmetric
  证明: by
  rw [antisymm_def]
exact forall₂_congr fun _ _ => imp_congr realize_rel₂ imp_congr realize_rel₂ .rfl

@[simp]

Depends on / 依赖: antisymm_def, imp_congr
-/
theorem realize_antisymmetric :
    M ⊨ r.antisymmetric ↔ Std.Antisymm fun x y : M => RelMap r ![x, y] := by
  rw [antisymm_def]
exact forall₂_congr fun _ _ => imp_congr realize_rel₂ imp_congr realize_rel₂ .rfl

@[simp]
/--
theorem `realize_transitive` / 定理 `realize_transitive`

English:
theorem realize_transitive
  statement: M ⊨ r.transitive ↔ IsTrans M fun x y => RelMap r ![x, y]
  proof: by
  rw [isTrans_def]
exact forall₃_congr fun _ _ _ => imp_congr realize_rel₂ imp_congr realize_rel₂ realize_rel₂

@[simp]

中文:
定理 realize_transitive
  结论: M ⊨ r.transitive ↔ IsTrans M fun x y => RelMap r ![x, y]
  证明: by
  rw [isTrans_def]
exact forall₃_congr fun _ _ _ => imp_congr realize_rel₂ imp_congr realize_rel₂ realize_rel₂

@[simp]

Depends on / 依赖: imp_congr, isTrans_def
-/
theorem realize_transitive : M ⊨ r.transitive ↔ IsTrans M fun x y => RelMap r ![x, y] := by
  rw [isTrans_def]
exact forall₃_congr fun _ _ _ => imp_congr realize_rel₂ imp_congr realize_rel₂ realize_rel₂

@[simp]
/--
theorem `realize_total` / 定理 `realize_total`

English:
theorem realize_total
  statement: M ⊨ r.total ↔ Std.Total fun x y : M => RelMap r ![x, y]
  proof: by
  rw [total_def]
exact forall₂_congr fun _ _ => realize_sup.trans or_congr realize_rel₂ realize_rel₂

中文:
定理 realize_total
  结论: M ⊨ r.total ↔ Std.Total fun x y : M => RelMap r ![x, y]
  证明: by
  rw [total_def]
exact forall₂_congr fun _ _ => realize_sup.trans or_congr realize_rel₂ realize_rel₂

Depends on / 依赖: or_congr, realize_sup, realize_sup.trans, total_def
-/
theorem realize_total : M ⊨ r.total ↔ Std.Total fun x y : M => RelMap r ![x, y] := by
  rw [total_def]
exact forall₂_congr fun _ _ => realize_sup.trans or_congr realize_rel₂ realize_rel₂

end Relations

section Cardinality

variable (L)
@[simp]
/--
theorem `Sentence.realize_cardGe` / 定理 `Sentence.realize_cardGe`

English:
theorem Sentence.realize_cardGe
  given: (n)
  statement: M ⊨ Sentence.cardGe L n ↔ ↑n <= #M
  proof: by
  rw [← lift_mk_fin]; rw [← lift_le.{0}]; rw [lift_lift]; rw [lift_mk_le]; rw [Sentence.cardGe]; rw [Sentence.Realize]; rw [BoundedFormula.realize_exs]
  simp_rw [BoundedFormula.realize_foldr_inf]
  simp only [Function.comp_apply, List.mem_map, Prod.exists, Ne, List.mem_product,
    List.mem_finR

中文:
定理 Sentence.realize_cardGe
  条件: (n)
  结论: M ⊨ Sentence.cardGe L n ↔ ↑n <= #M
  证明: by
  rw [← lift_mk_fin]; rw [← lift_le.{0}]; rw [lift_lift]; rw [lift_mk_le]; rw [Sentence.cardGe]; rw [Sentence.Realize]; rw [BoundedFormula.realize_exs]
  simp_rw [BoundedFormula.realize_foldr_inf]
  simp only [Function.comp_apply, List.mem_map, Prod.exists, Ne, List.mem_product,
    List.mem_finR

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_exs, BoundedFormula.realize_foldr_inf, Function, Function.comp_apply, List.mem_filter, List.mem_finRange, List.mem_map, List.mem_product, Prod.exists, Realize, Sentence, Sentence.Realize, Sentence.cardGe, and_imp, cardGe, comp_apply, contrapose, forall_exists_index, lift_le
-/
theorem Sentence.realize_cardGe (n) : M ⊨ Sentence.cardGe L n ↔ ↑n <= #M := by
  rw [← lift_mk_fin]; rw [← lift_le.{0}]; rw [lift_lift]; rw [lift_mk_le]; rw [Sentence.cardGe]; rw [Sentence.Realize]; rw [BoundedFormula.realize_exs]
  simp_rw [BoundedFormula.realize_foldr_inf]
  simp only [Function.comp_apply, List.mem_map, Prod.exists, Ne, List.mem_product,
    List.mem_finRange, forall_exists_index, and_imp, List.mem_filter, true_and]
  refine ⟨?_, fun xs => ⟨xs.some, ?_⟩⟩
  · rintro ⟨xs, h⟩
    refine ⟨⟨xs, fun i j ij => ?_⟩⟩
    contrapose! ij
    exact h _ i j (by simpa using ij) rfl
  · rintro _ i j ij rfl
    simpa using ij

@[simp]
/--
theorem `model_infiniteTheory_iff` / 定理 `model_infiniteTheory_iff`

English:
theorem model_infiniteTheory_iff
  statement: M ⊨ L.infiniteTheory ↔ Infinite M
  proof: by
  simp [infiniteTheory, infinite_iff, aleph0_le]

中文:
定理 model_infiniteTheory_iff
  结论: M ⊨ L.infiniteTheory ↔ Infinite M
  证明: by
  simp [infiniteTheory, infinite_iff, aleph0_le]

Depends on / 依赖: aleph0_le, infiniteTheory, infinite_iff
-/
theorem model_infiniteTheory_iff : M ⊨ L.infiniteTheory ↔ Infinite M := by
  simp [infiniteTheory, infinite_iff, aleph0_le]

/--
Instance `model_infiniteTheory` / 实例 `model_infiniteTheory`

English:
instance model_infiniteTheory
  signature: [h : Infinite M]
  body: L.model_infiniteTheory_iff.2 h

@[simp]

中文:
实例 model_infiniteTheory
  签名: [h : Infinite M]
  定义体: L.model_infiniteTheory_iff.2 h

@[simp]

Depends on / 依赖: L.model_infiniteTheory_iff, model_infiniteTheory_iff
-/
instance model_infiniteTheory [h : Infinite M] : M ⊨ L.infiniteTheory :=
  L.model_infiniteTheory_iff.2 h

@[simp]
/--
theorem `model_nonemptyTheory_iff` / 定理 `model_nonemptyTheory_iff`

English:
theorem model_nonemptyTheory_iff
  statement: M ⊨ L.nonemptyTheory ↔ Nonempty M
  proof: by
  simp only [nonemptyTheory, Theory.model_iff, Set.mem_singleton_iff, forall_eq,
    Sentence.realize_cardGe, Nat.cast_one, Cardinal.one_le_iff_ne_zero, mk_ne_zero_iff]

中文:
定理 model_nonemptyTheory_iff
  结论: M ⊨ L.nonemptyTheory ↔ Nonempty M
  证明: by
  simp only [nonemptyTheory, Theory.model_iff, Set.mem_singleton_iff, forall_eq,
    Sentence.realize_cardGe, Nat.cast_one, Cardinal.one_le_iff_ne_zero, mk_ne_zero_iff]

Depends on / 依赖: Cardinal, Cardinal.one_le_iff_ne_zero, Nat.cast_one, Sentence, Sentence.realize_cardGe, Set.mem_singleton_iff, Theory, Theory.model_iff, cast_one, forall_eq, mem_singleton_iff, mk_ne_zero_iff, model_iff, nonemptyTheory, one_le_iff_ne_zero, realize_cardGe
-/
theorem model_nonemptyTheory_iff : M ⊨ L.nonemptyTheory ↔ Nonempty M := by
  simp only [nonemptyTheory, Theory.model_iff, Set.mem_singleton_iff, forall_eq,
    Sentence.realize_cardGe, Nat.cast_one, Cardinal.one_le_iff_ne_zero, mk_ne_zero_iff]

/--
Instance `model_nonempty` / 实例 `model_nonempty`

English:
instance model_nonempty
  signature: [h : Nonempty M]
  body: L.model_nonemptyTheory_iff.2 h

中文:
实例 model_nonempty
  签名: [h : Nonempty M]
  定义体: L.model_nonemptyTheory_iff.2 h

Depends on / 依赖: L.model_nonemptyTheory_iff, model_nonemptyTheory_iff
-/
instance model_nonempty [h : Nonempty M] : M ⊨ L.nonemptyTheory :=
  L.model_nonemptyTheory_iff.2 h

/--
theorem `model_distinctConstantsTheory` / 定理 `model_distinctConstantsTheory`

English:
theorem model_distinctConstantsTheory
  given: {M : Type w} [L[[α]].Structure M] (s : Set α)
  proof: by
  simp only [distinctConstantsTheory, Theory.model_iff, Set.mem_image,
    Prod.exists, forall_exists_index, and_imp]
  refine ⟨fun h a as b bs ab => ?_, ?_⟩
  · contrapose! ab
    have h' := h _ a b ⟨⟨as, bs⟩, ab⟩ rfl
    simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal,
 

中文:
定理 model_distinctConstantsTheory
  条件: {M : Type w} [L[[α]].Structure M] (s : Set α)
  证明: by
  simp only [distinctConstantsTheory, Theory.model_iff, Set.mem_image,
    Prod.exists, forall_exists_index, and_imp]
  refine ⟨fun h a as b bs ab => ?_, ?_⟩
  · contrapose! ab
    have h' := h _ a b ⟨⟨as, bs⟩, ab⟩ rfl
    simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal,
 

Depends on / 依赖: Formula, Formula.realize_equal, Formula.realize_not, Prod.exists, Realize, Sentence, Sentence.Realize, Set.mem_image, Term.realize_constants, Theory, Theory.model_iff, and_imp, contra, contrapose, distinctConstantsTheory, forall_exists_index, mem_image, model_iff, realize_constants, realize_equal
-/
theorem model_distinctConstantsTheory {M : Type w} [L[[α]].Structure M] (s : Set α) :
    M ⊨ L.distinctConstantsTheory s ↔ Set.InjOn (fun i : α => (L.con i : M)) s := by
  simp only [distinctConstantsTheory, Theory.model_iff, Set.mem_image,
    Prod.exists, forall_exists_index, and_imp]
  refine ⟨fun h a as b bs ab => ?_, ?_⟩
  · contrapose! ab
    have h' := h _ a b ⟨⟨as, bs⟩, ab⟩ rfl
    simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal,
      Term.realize_constants] at h'
    exact h'
  · rintro h φ a b ⟨⟨as, bs⟩, ab⟩ rfl
    simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal, Term.realize_constants]
    exact fun contra => ab (h as bs contra)

/--
theorem `card_le_of_model_distinctConstantsTheory` / 定理 `card_le_of_model_distinctConstantsTheory`

English:
theorem card_le_of_model_distinctConstantsTheory
  statement: (s : Set α) (M : Type w) [L[[α]].Structure M]
  proof: lift_mk_le'.2 ⟨⟨_, Set.injOn_iff_injective.1 ((L.model_distinctConstantsTheory s).1 h)⟩⟩

中文:
定理 card_le_of_model_distinctConstantsTheory
  结论: (s : Set α) (M : Type w) [L[[α]].Structure M]
  证明: lift_mk_le'.2 ⟨⟨_, Set.injOn_iff_injective.1 ((L.model_distinctConstantsTheory s).1 h)⟩⟩

Depends on / 依赖: L.model_distinctConstantsTheory, Set.injOn_iff_injective, injOn_iff_injective, lift_mk_le, model_distinctConstantsTheory
-/
theorem card_le_of_model_distinctConstantsTheory (s : Set α) (M : Type w) [L[[α]].Structure M]
    [h : M ⊨ L.distinctConstantsTheory s] : Cardinal.lift.{w} #s <= Cardinal.lift.{u'} #M :=
  lift_mk_le'.2 ⟨⟨_, Set.injOn_iff_injective.1 ((L.model_distinctConstantsTheory s).1 h)⟩⟩

end Cardinality

namespace ElementarilyEquivalent

@[symm]
nonrec theorem symm (h : M ≅[L] N) : N ≅[L] M :=
  h.symm

@[trans]
nonrec theorem trans (MN : M ≅[L] N) (NP : N ≅[L] P) : M ≅[L] P :=
  MN.trans NP

/--
theorem `completeTheory_eq` / 定理 `completeTheory_eq`

English:
theorem completeTheory_eq
  given: (h : M ≅[L] N)
  statement: L.completeTheory M = L.completeTheory N
  proof: h

中文:
定理 completeTheory_eq
  条件: (h : M ≅[L] N)
  结论: L.completeTheory M = L.completeTheory N
  证明: h
-/
theorem completeTheory_eq (h : M ≅[L] N) : L.completeTheory M = L.completeTheory N :=
  h

/--
theorem `realize_sentence` / 定理 `realize_sentence`

English:
theorem realize_sentence
  given: (h : M ≅[L] N) (φ : L.Sentence)
  statement: M ⊨ φ ↔ N ⊨ φ
  proof: (elementarilyEquivalent_iff.1 h) φ

中文:
定理 realize_sentence
  条件: (h : M ≅[L] N) (φ : L.Sentence)
  结论: M ⊨ φ ↔ N ⊨ φ
  证明: (elementarilyEquivalent_iff.1 h) φ

Depends on / 依赖: elementarilyEquivalent_iff
-/
theorem realize_sentence (h : M ≅[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ :=
  (elementarilyEquivalent_iff.1 h) φ

/--
theorem `theory_model_iff` / 定理 `theory_model_iff`

English:
theorem theory_model_iff
  given: (h : M ≅[L] N)
  statement: M ⊨ T ↔ N ⊨ T
  proof: by
  rw [Theory.model_iff_subset_completeTheory]; rw [Theory.model_iff_subset_completeTheory]; rw [h.completeTheory_eq]

中文:
定理 theory_model_iff
  条件: (h : M ≅[L] N)
  结论: M ⊨ T ↔ N ⊨ T
  证明: by
  rw [Theory.model_iff_subset_completeTheory]; rw [Theory.model_iff_subset_completeTheory]; rw [h.completeTheory_eq]

Depends on / 依赖: Theory, Theory.model_iff_subset_completeTheory, completeTheory_eq, h.completeTheory_eq, model_iff_subset_completeTheory
-/
theorem theory_model_iff (h : M ≅[L] N) : M ⊨ T ↔ N ⊨ T := by
  rw [Theory.model_iff_subset_completeTheory]; rw [Theory.model_iff_subset_completeTheory]; rw [h.completeTheory_eq]

/--
theorem `theory_model` / 定理 `theory_model`

English:
theorem theory_model
  given: [MT : M ⊨ T] (h : M ≅[L] N)
  statement: N ⊨ T
  proof: h.theory_model_iff.1 MT

中文:
定理 theory_model
  条件: [MT : M ⊨ T] (h : M ≅[L] N)
  结论: N ⊨ T
  证明: h.theory_model_iff.1 MT

Depends on / 依赖: h.theory_model_iff, theory_model_iff
-/
theorem theory_model [MT : M ⊨ T] (h : M ≅[L] N) : N ⊨ T :=
  h.theory_model_iff.1 MT

/--
theorem `nonempty_iff` / 定理 `nonempty_iff`

English:
theorem nonempty_iff
  given: (h : M ≅[L] N)
  statement: Nonempty M ↔ Nonempty N
  proof: (model_nonemptyTheory_iff L).symm.trans (h.theory_model_iff.trans (model_nonemptyTheory_iff L))

中文:
定理 nonempty_iff
  条件: (h : M ≅[L] N)
  结论: Nonempty M ↔ Nonempty N
  证明: (model_nonemptyTheory_iff L).symm.trans (h.theory_model_iff.trans (model_nonemptyTheory_iff L))

Depends on / 依赖: h.theory_model_iff.trans, model_nonemptyTheory_iff, symm.trans, theory_model_iff
-/
theorem nonempty_iff (h : M ≅[L] N) : Nonempty M ↔ Nonempty N :=
  (model_nonemptyTheory_iff L).symm.trans (h.theory_model_iff.trans (model_nonemptyTheory_iff L))

/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  given: [Mn : Nonempty M] (h : M ≅[L] N)
  statement: Nonempty N
  proof: h.nonempty_iff.1 Mn

中文:
定理 nonempty
  条件: [Mn : Nonempty M] (h : M ≅[L] N)
  结论: Nonempty N
  证明: h.nonempty_iff.1 Mn

Depends on / 依赖: h.nonempty_iff, nonempty_iff
-/
theorem nonempty [Mn : Nonempty M] (h : M ≅[L] N) : Nonempty N :=
  h.nonempty_iff.1 Mn

/--
theorem `infinite_iff` / 定理 `infinite_iff`

English:
theorem infinite_iff
  given: (h : M ≅[L] N)
  statement: Infinite M ↔ Infinite N
  proof: (model_infiniteTheory_iff L).symm.trans (h.theory_model_iff.trans (model_infiniteTheory_iff L))

中文:
定理 infinite_iff
  条件: (h : M ≅[L] N)
  结论: Infinite M ↔ Infinite N
  证明: (model_infiniteTheory_iff L).symm.trans (h.theory_model_iff.trans (model_infiniteTheory_iff L))

Depends on / 依赖: h.theory_model_iff.trans, model_infiniteTheory_iff, symm.trans, theory_model_iff
-/
theorem infinite_iff (h : M ≅[L] N) : Infinite M ↔ Infinite N :=
  (model_infiniteTheory_iff L).symm.trans (h.theory_model_iff.trans (model_infiniteTheory_iff L))

/--
theorem `infinite` / 定理 `infinite`

English:
theorem infinite
  given: [Mi : Infinite M] (h : M ≅[L] N)
  statement: Infinite N
  proof: h.infinite_iff.1 Mi

中文:
定理 infinite
  条件: [Mi : Infinite M] (h : M ≅[L] N)
  结论: Infinite N
  证明: h.infinite_iff.1 Mi

Depends on / 依赖: h.infinite_iff, infinite_iff
-/
theorem infinite [Mi : Infinite M] (h : M ≅[L] N) : Infinite N :=
  h.infinite_iff.1 Mi

end ElementarilyEquivalent

end Language

end FirstOrder
