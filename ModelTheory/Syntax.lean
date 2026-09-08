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

/-- A term on `α` is either a variable indexed by an element of `α` or a function symbol applied to
simpler terms. -/
/-
**FirstOrder.Language.Term** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Language`。
形式化陈述：FirstOrder.Language → Type u' → Type (max u u')
参数：max u u'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A term on `α` is either a variable indexed by an element of `α` or a function sy
mbol applied to
simpler terms.
-/
inductive Term (α : Type u') : Type max u u'
  | var : α → Term α
  | func : ∀ {l : ℕ} (_f : L.Functions l) (_ts : Fin l → Term α), Term α
export Term (var func)

variable {L}

namespace Term

/-
**FirstOrder.Language.Term.instDecidableEq** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder
.Language.Term`。
形式化陈述：instDecidableEq [DecidableEq α] [forall n, DecidableEq (L.Functions n)] : 
DecidableEq (L.Term α) | .var a, .var b => decidable_of_iff (a = b) by simp | @T
erm.func _ _ m f xs, @Term.func _ _ n g ys => if h : m = n then letI : Decidable
Eq (L.Term α)
参数：L.Functions n。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableEq [DecidableEq α] [∀ n, DecidableEq (L.Functions n)] : DecidableEq (L.Term α)
  | .var a, .var b => decidable_of_iff (a = b) <| by simp
  | @Term.func _ _ m f xs, @Term.func _ _ n g ys =>
      if h : m = n then
        letI : DecidableEq (L.Term α) := instDecidableEq
        decidable_of_iff (f = h ▸ g ∧ ∀ i : Fin m, xs i = ys (Fin.cast h i)) <| by
          subst h
          simp [funext_iff]
      else
        .isFalse <| by simp [h]
  | .var _, .func _ _ | .func _ _, .var _ => .isFalse <| by simp

open Finset

/-- The `Finset` of variables used in a given term. -/
@[simp]
/-
**FirstOrder.Language.Term.varFinset** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age.Term`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → [DecidableEq α] → L.Term α → F
inset α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Finset` of variables used in a given term.
-/
def varFinset [DecidableEq α] : L.Term α → Finset α
  | var i => {i}
  | func _f ts => univ.biUnion fun i => (ts i).varFinset

/-- The `Finset` of variables from the left side of a sum used in a given term. -/
@[simp]
/-
**FirstOrder.Language.Term.varFinsetLeft** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.L
anguage.Term`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {β : Type v'} → [DecidableEq α
] → L.Term (α ⊕ β) → Finset α
参数：α ⊕ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Finset` of variables from the left side of a sum used in a given term.
-/
def varFinsetLeft [DecidableEq α] : L.Term (α ⊕ β) → Finset α
  | var (Sum.inl i) => {i}
  | var (Sum.inr _i) => ∅
  | func _f ts => univ.biUnion fun i => (ts i).varFinsetLeft

/-- Relabels a term's variables along a particular function. -/
@[simp]
/-
**FirstOrder.Language.Term.relabel** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Languag
e.Term`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {β : Type v'} → (α → β) → L.Te
rm α → L.Term β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Relabels a term's variables along a particular function.
-/
def relabel (g : α → β) : L.Term α → L.Term β
  | var i => var (g i)
  | func f ts => func f fun {i} => (ts i).relabel g
/-
**FirstOrder.Language.Term.relabel_id** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Term`。
形式化陈述：relabel_id (t : L.Term α) : t.relabel id = t
参数：t : L.Term α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem relabel_id (t : L.Term α) : t.relabel id = t := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

@[simp]
/-
**FirstOrder.Language.Term.relabel_id_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.Term`。
形式化陈述：relabel_id_eq_id : (Term.relabel id : L.Term α -> L.Term α) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.Term.relabel_id`：relabel_id (t : L.Term α) : t.relab
el id = t
-/
theorem relabel_id_eq_id : (Term.relabel id : L.Term α → L.Term α) = id :=
  funext relabel_id

@[simp]
/-
**FirstOrder.Language.Term.relabel_relabel** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Term`。
形式化陈述：relabel_relabel (f : α -> β) (g : β -> γ) (t : L.Term α) : (t.relabel f).r
elabel g = t.relabel (g ∘ f)
参数：f : α -> β；g : β -> γ；t : L.Term α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Term.relabel.eq_2`：∀ {L : FirstOrder.Language} {α : 
Type u'} {β : Type v'} (g : α → β) (l : ℕ) (_f : L.Functions l)   (ts : Fin l → 
L.Term α),   FirstOrder.Lan…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem relabel_relabel (f : α → β) (g : β → γ) (t : L.Term α) :
    (t.relabel f).relabel g = t.relabel (g ∘ f) := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

@[simp]
/-
**FirstOrder.Language.Term.relabel_comp_relabel** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Term`。
形式化陈述：relabel_comp_relabel (f : α -> β) (g : β -> γ) : (Term.relabel g ∘ Term.re
label f : L.Term α -> L.Term γ) = Term.relabel (g ∘ f)
参数：f : α -> β；g : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.Term.relabel_relabel`：relabel_relabel (f : α -> β) (
g : β -> γ) (t : L.Term α) : (t.relabel f).relabel g = t.relabel (g ∘ f)
-/
theorem relabel_comp_relabel (f : α → β) (g : β → γ) :
    (Term.relabel g ∘ Term.relabel f : L.Term α → L.Term γ) = Term.relabel (g ∘ f) :=
  funext (relabel_relabel f g)

/-- Relabels a term's variables along a bijection. -/
@[simps]
/-
**FirstOrder.Language.Term.relabelEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage.Term`。
形式化陈述：relabelEquiv (g : α ≃ β) : L.Term α ≃ L.Term β
参数：g : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Relabels a term's variables along a bijection.
-/
def relabelEquiv (g : α ≃ β) : L.Term α ≃ L.Term β :=
  ⟨relabel g, relabel g.symm, fun t => by simp, fun t => by simp⟩

/-- Restricts a term to use only a set of the given variables. -/
/-
**FirstOrder.Language.Term.restrictVar** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lan
guage.Term`。
形式化陈述：{L : FirstOrder.Language} →   {α : Type u'} → {β : Type v'} → [inst : Deci
dableEq α] → (t : L.Term α) → (↥t.varFinset → β) → L.Term β
参数：t : L.Term α；↥t.varFinset → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricts a term to use only a set of the given variables.
-/
def restrictVar [DecidableEq α] : ∀ (t : L.Term α) (_f : t.varFinset → β), L.Term β
  | var a, f => var (f ⟨a, mem_singleton_self a⟩)
  | func F ts, f =>
    func F fun i => (ts i).restrictVar (f ∘ Set.inclusion
      (subset_biUnion_of_mem (fun i => varFinset (ts i)) (mem_univ i)))

/-- Restricts a term to use only a set of the given variables on the left side of a sum. -/
/-
**FirstOrder.Language.Term.restrictVarLeft** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder
.Language.Term`。
形式化陈述：{L : FirstOrder.Language} →   {α : Type u'} →     {β : Type v'} →       [i
nst : DecidableEq α] → {γ : Type u_2} → (t : L.Term (α ⊕ γ)) → (↥t.varFinsetLeft
 → β) → L.Term (β ⊕ γ)
参数：t : L.Term (α ⊕ γ)；↥t.varFinsetLeft → β；β ⊕ γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricts a term to use only a set of the given variables on the left side of a 
sum.
-/
def restrictVarLeft [DecidableEq α] {γ : Type*} :
    ∀ (t : L.Term (α ⊕ γ)) (_f : t.varFinsetLeft → β), L.Term (β ⊕ γ)
  | var (Sum.inl a), f => var (Sum.inl (f ⟨a, mem_singleton_self a⟩))
  | var (Sum.inr a), _f => var (Sum.inr a)
  | func F ts, f =>
    func F fun i =>
      (ts i).restrictVarLeft (f ∘ Set.inclusion (subset_biUnion_of_mem
        (fun i => varFinsetLeft (ts i)) (mem_univ i)))

end Term

/-- The representation of a constant symbol as a term. -/
/-
**FirstOrder.Language.Constants.term** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age.Constants`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → L.Constants → L.Term α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representation of a constant symbol as a term.
-/
def Constants.term (c : L.Constants) : L.Term α :=
  func c default

/-- Applies a unary function to a term. -/
/-
**FirstOrder.Language.Functions.apply** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies a unary function to a term.
-/
def Functions.apply₁ (f : L.Functions 1) (t : L.Term α) : L.Term α :=
  func f ![t]

/-- Applies a binary function to two terms. -/
/-
**FirstOrder.Language.Functions.apply** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies a binary function to two terms.
-/
def Functions.apply₂ (f : L.Functions 2) (t₁ t₂ : L.Term α) : L.Term α :=
  func f ![t₁, t₂]

/-- The representation of a function symbol as a term, on fresh variables indexed by Fin. -/
/-
**FirstOrder.Language.Functions.term** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age.Functions`。
形式化陈述：{L : FirstOrder.Language} → {n : ℕ} → L.Functions n → L.Term (Fin n)
参数：Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representation of a function symbol as a term, on fresh variables indexed by
 Fin.
-/
def Functions.term {n : ℕ} (f : L.Functions n) : L.Term (Fin n) :=
  func f Term.var

namespace Term

/-- Sends a term with constants to a term with extra variables. -/
@[simp]
/-
**FirstOrder.Language.Term.constantsToVars** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder
.Language.Term`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {γ : Type u_1} → (L.withConsta
nts γ).Term α → L.Term (γ ⊕ α)
参数：L.withConstants γ；γ ⊕ α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sends a term with constants to a term with extra variables.
-/
def constantsToVars : L[[γ]].Term α → L.Term (γ ⊕ α)
  | var a => var (Sum.inr a)
  | @func _ _ 0 f ts =>
    Sum.casesOn f (fun f => func f fun i => (ts i).constantsToVars) fun c => var (Sum.inl c)
  | @func _ _ (_n + 1) f ts =>
    Sum.casesOn f (fun f => func f fun i => (ts i).constantsToVars) fun c => isEmptyElim c

/-- Sends a term with extra variables to a term with constants. -/
@[simp]
/-
**FirstOrder.Language.Term.varsToConstants** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder
.Language.Term`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {γ : Type u_1} → L.Term (γ ⊕ α
) → (L.withConstants γ).Term α
参数：γ ⊕ α；L.withConstants γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sends a term with extra variables to a term with constants.
-/
def varsToConstants : L.Term (γ ⊕ α) → L[[γ]].Term α
  | var (Sum.inr a) => var a
  | var (Sum.inl c) => Constants.term (Sum.inr c)
  | func f ts => func (Sum.inl f) fun i => (ts i).varsToConstants

set_option backward.isDefEq.respectTransparency false in
/-- A bijection between terms with constants and terms with extra variables. -/
@[simps]
/-
**FirstOrder.Language.Term.constantsVarsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FirstOr
der.Language.Term`。
形式化陈述：constantsVarsEquiv : L[[γ]].Term α ≃ L.Term (γ oplus α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bijection between terms with constants and terms with extra variables.
-/
def constantsVarsEquiv : L[[γ]].Term α ≃ L.Term (γ ⊕ α) :=
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

/-- A bijection between terms with constants and terms with extra variables. -/
/-
**FirstOrder.Language.Term.constantsVarsEquivLeft** 是 Mathlib 中的一个定义，位于命名空间 `Fir
stOrder.Language.Term`。
形式化陈述：constantsVarsEquivLeft : L[[γ]].Term (α oplus β) ≃ L.Term ((γ oplus α) opl
us β)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A bijection between terms with constants and terms with extra variables.
-/
def constantsVarsEquivLeft : L[[γ]].Term (α ⊕ β) ≃ L.Term ((γ ⊕ α) ⊕ β) :=
  constantsVarsEquiv.trans (relabelEquiv (Equiv.sumAssoc _ _ _)).symm

@[simp]
/-
**FirstOrder.Language.Term.constantsVarsEquivLeft_apply** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.Term`。
形式化陈述：constantsVarsEquivLeft_apply (t : L[[γ]].Term (α oplus β)) : constantsVars
EquivLeft t = (constantsToVars t).relabel (Equiv.sumAssoc _ _ _).symm
参数：t : L[[γ]].Term (α oplus β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantsVarsEquivLeft_apply (t : L[[γ]].Term (α ⊕ β)) :
    constantsVarsEquivLeft t = (constantsToVars t).relabel (Equiv.sumAssoc _ _ _).symm :=
  rfl

@[simp]
/-
**FirstOrder.Language.Term.constantsVarsEquivLeft_symm_apply** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.Term`。
形式化陈述：constantsVarsEquivLeft_symm_apply (t : L.Term ((γ oplus α) oplus β)) : con
stantsVarsEquivLeft.symm t = varsToConstants (t.relabel (Equiv.sumAssoc _ _ _))
参数：t : L.Term ((γ oplus α) oplus β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem constantsVarsEquivLeft_symm_apply (t : L.Term ((γ ⊕ α) ⊕ β)) :
    constantsVarsEquivLeft.symm t = varsToConstants (t.relabel (Equiv.sumAssoc _ _ _)) :=
  rfl
/-
**FirstOrder.Language.Term.inhabitedOfVar** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.
Language.Term`。
形式化陈述：inhabitedOfVar [Inhabited α] : Inhabited (L.Term α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedOfVar [Inhabited α] : Inhabited (L.Term α) :=
  ⟨var default⟩
/-
**FirstOrder.Language.Term.inhabitedOfConstant** 是 Mathlib 中的一个实例，位于命名空间 `FirstO
rder.Language.Term`。
形式化陈述：inhabitedOfConstant [Inhabited L.Constants] : Inhabited (L.Term α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedOfConstant [Inhabited L.Constants] : Inhabited (L.Term α) :=
  ⟨(default : L.Constants).term⟩

/-- Raises all of the `Fin`-indexed variables of a term greater than or equal to `m` by `n'`. -/
/-
**FirstOrder.Language.Term.liftAt** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
.Term`。
形式化陈述：liftAt {n : Nat} (n' m : Nat) : L.Term (α oplus (Fin n)) -> L.Term (α oplu
s (Fin (n + n')))
参数：n' m : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Raises all of the `Fin`-indexed variables of a term greater than or equal to `m`
 by `n'`.
-/
def liftAt {n : ℕ} (n' m : ℕ) : L.Term (α ⊕ (Fin n)) → L.Term (α ⊕ (Fin (n + n'))) :=
  relabel (Sum.map id fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n')

/-- Substitutes the variables in a given term with terms. -/
@[simp]
/-
**FirstOrder.Language.Term.subst** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language.
Term`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {β : Type v'} → L.Term α → (α 
→ L.Term β) → L.Term β
参数：α → L.Term β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Substitutes the variables in a given term with terms.
-/
def subst : L.Term α → (α → L.Term β) → L.Term β
  | var a, tf => tf a
  | func f ts, tf => func f fun i => (ts i).subst tf

/-- Substitutes the functions in a given term with expressions. -/
@[simp]
/-
**FirstOrder.Language.Term.substFunc** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age.Term`。
形式化陈述：{L : FirstOrder.Language} →   {L' : FirstOrder.Language} → {α : Type u'} →
 L.Term α → ({n : ℕ} → L.Functions n → L'.Term (Fin n)) → L'.Term α
参数：{n : ℕ} → L.Functions n → L'.Term (Fin n)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Substitutes the functions in a given term with expressions.
-/
def substFunc : L.Term α → (∀ {n : ℕ}, L.Functions n → L'.Term (Fin n)) → L'.Term α
  | var a, _ => var a
  | func f ts, tf => (tf f).subst fun i ↦ (ts i).substFunc tf

@[simp]
/-
**FirstOrder.Language.Term.substFunc_term** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Term`。
形式化陈述：substFunc_term (t : L.Term α) : t.substFunc Functions.term = t
参数：t : L.Term α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.Term.subst.eq_2`：∀ {L : FirstOrder.Language} {α : Ty
pe u'} {β : Type v'} (x : α → L.Term β) (l : ℕ) (f : L.Functions l)   (ts : Fin 
l → L.Term α), (FirstOrde…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem substFunc_term (t : L.Term α) : t.substFunc Functions.term = t := by
  induction t
  · rfl
  · simp only [substFunc, Functions.term, subst, ‹∀ _, _›]

end Term

/-- `&n` is notation for the bound variable indexed by `n` in a bounded formula. -/
scoped[FirstOrder] prefix:arg "&" => FirstOrder.Language.Term.var ∘ Sum.inr

namespace LHom

open Term

/-- Maps a term's symbols along a language map. -/
@[simp]
/-
**FirstOrder.Language.LHom.onTerm** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
.LHom`。
形式化陈述：{L : FirstOrder.Language} → {L' : FirstOrder.Language} → {α : Type u'} → (
L →ᴸ L') → L.Term α → L'.Term α
参数：L →ᴸ L'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps a term's symbols along a language map.
-/
def onTerm (φ : L →ᴸ L') : L.Term α → L'.Term α
  | var i => var i
  | func f ts => func (φ.onFunction f) fun i => onTerm φ (ts i)

@[simp]
/-
**FirstOrder.Language.LHom.id_onTerm** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langu
age.LHom`。
形式化陈述：id_onTerm : ((LHom.id L).onTerm : L.Term α -> L.Term α) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem id_onTerm : ((LHom.id L).onTerm : L.Term α → L.Term α) = id := by
  ext t
  induction t with
  | var => rfl
  | func _ _ ih => simp_rw [onTerm, ih]; rfl

@[simp]
/-
**FirstOrder.Language.LHom.comp_onTerm** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.LHom`。
形式化陈述：comp_onTerm {L'' : Language} (φ : L' ->ᴸ L'') (ψ : L ->ᴸ L') : ((φ.comp ψ)
.onTerm : L.Term α -> L''.Term α) = φ.onTerm ∘ ψ.onTerm
参数：φ : L' ->ᴸ L''；ψ : L ->ᴸ L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem comp_onTerm {L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onTerm : L.Term α → L''.Term α) = φ.onTerm ∘ ψ.onTerm := by
  ext t
  induction t with
  | var => rfl
  | func _ _ ih => simp_rw [onTerm, ih]; rfl

end LHom

/-- Maps a term's symbols along a language equivalence. -/
@[simps]
/-
**FirstOrder.Language.LEquiv.onTerm** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langua
ge.LEquiv`。
形式化陈述：{L : FirstOrder.Language} → {L' : FirstOrder.Language} → {α : Type u'} → (
L ≃ᴸ L') → L.Term α ≃ L'.Term α
参数：L ≃ᴸ L'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps a term's symbols along a language equivalence.
-/
def LEquiv.onTerm (φ : L ≃ᴸ L') : L.Term α ≃ L'.Term α where
  toFun := φ.toLHom.onTerm
  invFun := φ.invLHom.onTerm
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LHom.comp_onTerm, φ.left_inv, LHom.id_onTerm]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LHom.comp_onTerm, φ.right_inv, LHom.id_onTerm]

variable (L) (α)

/-- `BoundedFormula α n` is the type of formulas with free variables indexed by `α` and `n` in-scope
bound variables indexed by `Fin n`. -/
/-
**FirstOrder.Language.BoundedFormula** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Lan
guage`。
形式化陈述：FirstOrder.Language → Type u' → ℕ → Type (max u v u')
参数：max u v u'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BoundedFormula α n` is the type of formulas with free variables indexed by `α` 
and `n` in-scope
bound variables indexed by `Fin n`.
-/
inductive BoundedFormula : ℕ → Type max u v u'
  | falsum {n} : BoundedFormula n
  | equal {n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : BoundedFormula n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : BoundedFormula n
  /-- The implication between two bounded formulas. -/
  | imp {n} (f₁ f₂ : BoundedFormula n) : BoundedFormula n
  /-- The universal quantifier over bounded formulas. -/
  | all {n} (f : BoundedFormula (n + 1)) : BoundedFormula n

/-- `Formula α` is the type of formulas with free variables indexed by `α` and no bound variables in
scope. -/
/-
**FirstOrder.Language.Formula** 是 Mathlib 中的一个缩写定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：Formula
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Formula α` is the type of formulas with free variables indexed by `α` and no bo
und variables in
scope.
-/
abbrev Formula :=
  L.BoundedFormula α 0

/-- A sentence is a formula with no free variables. -/
/-
**FirstOrder.Language.Sentence** 是 Mathlib 中的一个缩写定义，位于命名空间 `FirstOrder.Language`
。
形式化陈述：Sentence
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sentence is a formula with no free variables.
-/
abbrev Sentence :=
  L.Formula Empty

/-- A theory is a set of sentences. -/
/-
**FirstOrder.Language.Theory** 是 Mathlib 中的一个缩写定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：Theory
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A theory is a set of sentences.
-/
abbrev Theory :=
  Set L.Sentence

variable {L} {α} {n : ℕ}

/-- Applies a relation to terms as a bounded formula. -/
/-
**FirstOrder.Language.Relations.boundedFormula** 是 Mathlib 中的一个定义，位于命名空间 `FirstO
rder.Language.Relations`。
形式化陈述：{L : FirstOrder.Language} →   {α : Type u'} → {n l : ℕ} → L.Relations n → 
(Fin n → L.Term (α ⊕ Fin l)) → L.BoundedFormula α l
参数：Fin n → L.Term (α ⊕ Fin l)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies a relation to terms as a bounded formula.
-/
def Relations.boundedFormula {l : ℕ} (R : L.Relations n) (ts : Fin n → L.Term (α ⊕ (Fin l))) :
    L.BoundedFormula α l :=
  BoundedFormula.rel R ts

/-- Applies a unary relation to a term as a bounded formula. -/
/-
**FirstOrder.Language.Relations.boundedFormula** 是 Mathlib 中的一个定义，位于命名空间 `FirstO
rder.Language.Relations`。
形式化陈述：{L : FirstOrder.Language} →   {α : Type u'} → {n l : ℕ} → L.Relations n → 
(Fin n → L.Term (α ⊕ Fin l)) → L.BoundedFormula α l
参数：Fin n → L.Term (α ⊕ Fin l)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies a unary relation to a term as a bounded formula.
-/
def Relations.boundedFormula₁ (r : L.Relations 1) (t : L.Term (α ⊕ (Fin n))) :
    L.BoundedFormula α n :=
  r.boundedFormula ![t]

/-- Applies a binary relation to two terms as a bounded formula. -/
/-
**FirstOrder.Language.Relations.boundedFormula** 是 Mathlib 中的一个定义，位于命名空间 `FirstO
rder.Language.Relations`。
形式化陈述：{L : FirstOrder.Language} →   {α : Type u'} → {n l : ℕ} → L.Relations n → 
(Fin n → L.Term (α ⊕ Fin l)) → L.BoundedFormula α l
参数：Fin n → L.Term (α ⊕ Fin l)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies a binary relation to two terms as a bounded formula.
-/
def Relations.boundedFormula₂ (r : L.Relations 2) (t₁ t₂ : L.Term (α ⊕ (Fin n))) :
    L.BoundedFormula α n :=
  r.boundedFormula ![t₁, t₂]

/-- The equality of two terms as a bounded formula. -/
/-
**FirstOrder.Language.Term.bdEqual** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Languag
e.Term`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.Term (α ⊕ Fin n) →
 L.Term (α ⊕ Fin n) → L.BoundedFormula α n
参数：α ⊕ Fin n；α ⊕ Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equality of two terms as a bounded formula.
-/
def Term.bdEqual (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  BoundedFormula.equal t₁ t₂

/-- Applies a relation to terms as a formula. -/
/-
**FirstOrder.Language.Relations.formula** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage.Relations`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.Relations n → (Fin
 n → L.Term α) → L.Formula α
参数：Fin n → L.Term α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies a relation to terms as a formula.
-/
def Relations.formula (R : L.Relations n) (ts : Fin n → L.Term α) : L.Formula α :=
  R.boundedFormula fun i => (ts i).relabel Sum.inl

/-- Applies a unary relation to a term as a formula. -/
/-
**FirstOrder.Language.Relations.formula** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage.Relations`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.Relations n → (Fin
 n → L.Term α) → L.Formula α
参数：Fin n → L.Term α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies a unary relation to a term as a formula.
-/
def Relations.formula₁ (r : L.Relations 1) (t : L.Term α) : L.Formula α :=
  r.formula ![t]

/-- Applies a binary relation to two terms as a formula. -/
/-
**FirstOrder.Language.Relations.formula** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage.Relations`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.Relations n → (Fin
 n → L.Term α) → L.Formula α
参数：Fin n → L.Term α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies a binary relation to two terms as a formula.
-/
def Relations.formula₂ (r : L.Relations 2) (t₁ t₂ : L.Term α) : L.Formula α :=
  r.formula ![t₁, t₂]

/-- The equality of two terms as a first-order formula. -/
/-
**FirstOrder.Language.Term.equal** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language.
Term`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → L.Term α → L.Term α → L.Formul
a α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equality of two terms as a first-order formula.
-/
def Term.equal (t₁ t₂ : L.Term α) : L.Formula α :=
  (t₁.relabel Sum.inl).bdEqual (t₂.relabel Sum.inl)

namespace BoundedFormula

/-
**FirstOrder.Language.BoundedFormula.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Lang
uage.BoundedFormula`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (L.BoundedFormula α n) :=
  ⟨falsum⟩
/-
**FirstOrder.Language.BoundedFormula.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Lang
uage.BoundedFormula`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (L.BoundedFormula α n) :=
  ⟨falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[match_pattern]
/-
**FirstOrder.Language.BoundedFormula.not** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.L
anguage.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.BoundedFormula α n
 → L.BoundedFormula α n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The negation of a bounded formula is also a bounded formula.
-/
protected def not (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
@[match_pattern]
/-
**FirstOrder.Language.BoundedFormula.ex** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.BoundedFormula α (
n + 1) → L.BoundedFormula α n
参数：n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Puts an `∃` quantifier on a bounded formula.
-/
protected def ex (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  φ.not.all.not
/-
**FirstOrder.Language.BoundedFormula.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Lang
uage.BoundedFormula`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (L.BoundedFormula α n) :=
  ⟨BoundedFormula.not ⊥⟩
/-
**FirstOrder.Language.BoundedFormula.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Lang
uage.BoundedFormula`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (L.BoundedFormula α n) :=
  ⟨fun f g => (f.imp g.not).not⟩
/-
**FirstOrder.Language.BoundedFormula.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Lang
uage.BoundedFormula`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (L.BoundedFormula α n) :=
  ⟨fun f g => f.not.imp g⟩

/-- The biimplication between two bounded formulas. -/
/-
**FirstOrder.Language.BoundedFormula.iff** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.L
anguage.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.BoundedFormula α n
 → L.BoundedFormula α n → L.BoundedFormula α n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The biimplication between two bounded formulas.
-/
protected def iff (φ ψ : L.BoundedFormula α n) :=
  φ.imp ψ ⊓ ψ.imp φ

open Finset

/-- The `Finset` of free variables used in a given formula. -/
@[simp]
/-
**FirstOrder.Language.BoundedFormula.freeVarFinset** 是 Mathlib 中的一个定义，位于命名空间 `Fi
rstOrder.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → [DecidableEq α] → {n : ℕ} → L.
BoundedFormula α n → Finset α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Finset` of free variables used in a given formula.
-/
def freeVarFinset [DecidableEq α] : ∀ {n}, L.BoundedFormula α n → Finset α
  | _n, falsum => ∅
  | _n, equal t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | _n, rel _R ts => univ.biUnion fun i => (ts i).varFinsetLeft
  | _n, imp f₁ f₂ => f₁.freeVarFinset ∪ f₂.freeVarFinset
  | _n, all f => f.freeVarFinset

/-- Casts `L.BoundedFormula α m` as `L.BoundedFormula α n`, where `m ≤ n`. -/
@[simp]
/-
**FirstOrder.Language.BoundedFormula.castLE** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrde
r.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {m n : ℕ} → m ≤ n → L.BoundedF
ormula α m → L.BoundedFormula α n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Casts `L.BoundedFormula α m` as `L.BoundedFormula α n`, where `m ≤ n`.
-/
def castLE : ∀ {m n : ℕ} (_h : m ≤ n), L.BoundedFormula α m → L.BoundedFormula α n
  | _m, _n, _h, falsum => falsum
  | _m, _n, h, equal t₁ t₂ =>
    equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
  | _m, _n, h, rel R ts => rel R (Term.relabel (Sum.map id (Fin.castLE h)) ∘ ts)
  | _m, _n, h, imp f₁ f₂ => (f₁.castLE h).imp (f₂.castLE h)
  | _m, _n, h, all f => (f.castLE (by gcongr)).all

@[simp]
/-
**FirstOrder.Language.BoundedFormula.castLE_rfl** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.BoundedFormula`。
形式化陈述：castLE_rfl {n} (h : n <= n) (φ : L.BoundedFormula α n) : φ.castLE h = φ
参数：h : n <= n；φ : L.BoundedFormula α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Sum.map_id_id`：∀ {α : Type u_1} {β : Type u_2}, Sum.map id id = id
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FirstOrder.Language.Term.relabel_id_eq_id`：relabel_id_eq_id : (Term.rela
bel id : L.Term α -> L.Term α) = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem castLE_rfl {n} (h : n ≤ n) (φ : L.BoundedFormula α n) : φ.castLE h = φ := by
  induction φ with
  | falsum => rfl
  | equal => simp
  | rel => simp
  | imp _ _ ih1 ih2 => simp [ih1, ih2]
  | all _ ih3 => simp [ih3]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.castLE_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.BoundedFormula`。
形式化陈述：castLE_castLE {k m n} (km : k <= m) (mn : m <= n) (φ : L.BoundedFormula α 
k) : (φ.castLE km).castLE mn = φ.castLE (km.trans mn)
参数：km : k <= m；mn : m <= n；φ : L.BoundedFormula α k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.castLE.eq_2`：∀ {L : FirstOrder.Langua
ge} {α : Type u'} (x x_1 : ℕ) (x_2 : x ≤ x_1) (t₁ t₂ : L.Term (α ⊕ Fin x)),   Fi
rstOrder.Language.BoundedFormula.cas…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Language.Term.relabel_relabel`：relabel_relabel (f : α -> β) (
g : β -> γ) (t : L.Term α) : (t.relabel f).relabel g = t.relabel (g ∘ f)
· 使用定理 `Sum.map_comp_map`：∀ {α' : Type u_1} {α'' : Type u_2} {β' : Type u_3} {β'
' : Type u_4} {α : Type u_5} {β : Type u_6} (f' : α' → α'')   (g' : β' → β'') (f
 : α →…
· 使用定理 `Fin.castLE_comp_castLE`：∀ {k m n : ℕ} (km : k ≤ m) (mn : m ≤ n), Fin.cas
tLE mn ∘ Fin.castLE km = Fin.castLE ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `FirstOrder.Language.BoundedFormula.castLE.eq_3`：∀ {L : FirstOrder.Langua
ge} {α : Type u'} (x x_1 : ℕ) (x_2 : x ≤ x_1) (l : ℕ) (R : L.Relations l)   (ts 
: Fin l → L.Term (α ⊕ Fin x)),   Fir…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `FirstOrder.Language.Term.relabel_comp_relabel`：relabel_comp_relabel (f :
 α -> β) (g : β -> γ) : (Term.relabel g ∘ Term.relabel f : L.Term α -> L.Term γ)
 = Term.relabel (g ∘ f)
· 使用定理 `FirstOrder.Language.BoundedFormula.castLE.eq_4`：∀ {L : FirstOrder.Langua
ge} {α : Type u'} (x x_1 : ℕ) (x_2 : x ≤ x_1) (f₁ f₂ : L.BoundedFormula α x),   
FirstOrder.Language.BoundedFormula.c…
· 使用定理 `FirstOrder.Language.BoundedFormula.castLE.eq_5`：∀ {L : FirstOrder.Langua
ge} {α : Type u'} (x x_1 : ℕ) (x_2 : x ≤ x_1) (f : L.BoundedFormula α (x + 1)), 
  FirstOrder.Language.BoundedFormula…
-/
theorem castLE_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) (φ : L.BoundedFormula α k) :
    (φ.castLE km).castLE mn = φ.castLE (km.trans mn) := by
  revert m n
  induction φ with
  | falsum => intros; rfl
  | equal => simp
  | rel =>
    intros
    simp only [castLE]
    rw [← Function.comp_assoc, Term.relabel_comp_relabel]
    simp
  | imp _ _ ih1 ih2 => simp [ih1, ih2]
  | all _ ih3 => intros; simp only [castLE, ih3]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.castLE_comp_castLE** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：castLE_comp_castLE {k m n} (km : k <= m) (mn : m <= n) : (BoundedFormula.c
astLE mn ∘ BoundedFormula.castLE km : L.BoundedFormula α k -> L.BoundedFormula α
 n) = BoundedFormula.castLE (km.trans mn)
参数：km : k <= m；mn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `FirstOrder.Language.BoundedFormula.castLE_castLE`：castLE_castLE {k m n} 
(km : k <= m) (mn : m <= n) (φ : L.BoundedFormula α k) : (φ.castLE km).castLE mn
 = φ.castLE (km.trans mn)
-/
theorem castLE_comp_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) :
    (BoundedFormula.castLE mn ∘ BoundedFormula.castLE km :
        L.BoundedFormula α k → L.BoundedFormula α n) =
      BoundedFormula.castLE (km.trans mn) :=
  funext (castLE_castLE km mn)

/-- Restricts a bounded formula to only use a particular set of free variables. -/
/-
**FirstOrder.Language.BoundedFormula.restrictFreeVar** 是 Mathlib 中的一个定义，位于命名空间 `
FirstOrder.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} →   {α : Type u'} →     {β : Type v'} →       [i
nst : DecidableEq α] → {n : ℕ} → (φ : L.BoundedFormula α n) → (↥φ.freeVarFinset 
→ β) → L.BoundedFormula β n
参数：φ : L.BoundedFormula α n；↥φ.freeVarFinset → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricts a bounded formula to only use a particular set of free variables.
-/
def restrictFreeVar [DecidableEq α] :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (_f : φ.freeVarFinset → β), L.BoundedFormula β n
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

/-- Places universal quantifiers on all in-scope bound variables of a bounded formula. -/
/-
**FirstOrder.Language.BoundedFormula.alls** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.
Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.BoundedFormula α n
 → L.Formula α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Places universal quantifiers on all in-scope bound variables of a bounded formul
a.
-/
def alls : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | _n + 1, φ => φ.all.alls

/-- Places existential quantifiers on all in-scope bound variables of a bounded formula. -/
/-
**FirstOrder.Language.BoundedFormula.exs** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.L
anguage.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.BoundedFormula α n
 → L.Formula α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Places existential quantifiers on all in-scope bound variables of a bounded form
ula.
-/
def exs : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | _n + 1, φ => φ.ex.exs

/-- Maps bounded formulas along a map of terms and a map of relations. -/
/-
**FirstOrder.Language.BoundedFormula.mapTermRel** 是 Mathlib 中的一个定义，位于命名空间 `First
Order.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} →   {L' : FirstOrder.Language} →     {α : Type u
'} →       {β : Type v'} →         {g : ℕ → ℕ} →           ((n : ℕ) → L.Term (α 
⊕ Fin n) → L'.Term (β ⊕ Fin (g n))) →             ((n : ℕ) → L.Relations n → L'.
Relations n) →               ((n : ℕ) → L'.BoundedFormula β (g (n + 1)) → L'.Bou
ndedFormula β (g n + 1)) →                 {n : ℕ} → L.BoundedFormula α n → L'.B
oundedFormula β (g n)
参数：(n : ℕ) → L.Term (α ⊕ Fin n) → L'.Term (β ⊕ Fin (g n))；(n : ℕ) → L.Relations 
n → L'.Relations n；(n : ℕ) → L'.BoundedFormula β (g (n + 1)) → L'.BoundedFormula
 β (g n + 1)；g n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps bounded formulas along a map of terms and a map of relations.
-/
def mapTermRel {g : ℕ → ℕ} (ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin (g n))))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (h : ∀ n, L'.BoundedFormula β (g (n + 1)) → L'.BoundedFormula β (g n + 1)) :
    ∀ {n}, L.BoundedFormula α n → L'.BoundedFormula β (g n)
  | _n, falsum => falsum
  | _n, equal t₁ t₂ => equal (ft _ t₁) (ft _ t₂)
  | _n, rel R ts => rel (fr _ R) fun i => ft _ (ts i)
  | _n, imp φ₁ φ₂ => (φ₁.mapTermRel ft fr h).imp (φ₂.mapTermRel ft fr h)
  | n, all φ => (h n (φ.mapTermRel ft fr h)).all

/-- Raises all of the bound variables of a formula greater than or equal to `m` by `n'`. -/
/-
**FirstOrder.Language.BoundedFormula.liftAt** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrde
r.Language.BoundedFormula`。
形式化陈述：liftAt : forall {n : Nat} (n' _m : Nat), L.BoundedFormula α n -> L.Bounded
Formula α (n + n')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Raises all of the bound variables of a formula greater than or equal to `m` by `
n'`.
-/
def liftAt : ∀ {n : ℕ} (n' _m : ℕ), L.BoundedFormula α n → L.BoundedFormula α (n + n') :=
  fun {_} n' m φ =>
  φ.mapTermRel (fun _ t => t.liftAt n' m) (fun _ => id) fun _ =>
    castLE (by rw [add_assoc, add_comm 1, add_assoc])

@[simp]
/-
**FirstOrder.Language.BoundedFormula.mapTermRel_mapTermRel** 是 Mathlib 中的一个定理，位于
命名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：mapTermRel_mapTermRel {L'' : Language} (ft : forall n, L.Term (α oplus (Fi
n n)) -> L'.Term (β oplus (Fin n))) (fr : forall n, L.Relations n -> L'.Relation
s n) (ft' : forall n, L'.Term (β oplus Fin n) -> L''.Term (γ oplus (Fin n))) (fr
' : forall n, L'.Relations n -> L''.Relations n) {n} (φ : L.BoundedFormula α n) 
: ((φ.mapTermRel ft fr fun _ => id).mapTermRel ft' fr' fun _ => id) = φ.mapTermR
el (fun _ => ft' _ ∘ ft _) (fun _ => fr' _ ∘ fr _) fun _ => id
参数：ft : forall n, L.Term (α oplus (Fin n)) -> L'.Term (β oplus (Fin n))；fr : for
all n, L.Relations n -> L'.Relations n；ft' : forall n, L'.Term (β oplus Fin n) -
> L''.Term (γ oplus (Fin n))；fr' : forall n, L'.Relations n -> L''.Relations n；φ
 : L.BoundedFormula α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.mapTermRel.eq_2`：∀ {L : FirstOrder.La
nguage} {L' : FirstOrder.Language} {α : Type u'} {β : Type v'} {g : ℕ → ℕ}   (ft
 : (n : ℕ) → L.Term (α ⊕ Fin n) → L'.Ter…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FirstOrder.Language.BoundedFormula.mapTermRel.eq_3`：∀ {L : FirstOrder.La
nguage} {L' : FirstOrder.Language} {α : Type u'} {β : Type v'} {g : ℕ → ℕ}   (ft
 : (n : ℕ) → L.Term (α ⊕ Fin n) → L'.Ter…
· 使用定理 `FirstOrder.Language.BoundedFormula.mapTermRel.eq_4`：∀ {L : FirstOrder.La
nguage} {L' : FirstOrder.Language} {α : Type u'} {β : Type v'} {g : ℕ → ℕ}   (ft
 : (n : ℕ) → L.Term (α ⊕ Fin n) → L'.Ter…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.mapTermRel.eq_5`：∀ {L : FirstOrder.La
nguage} {L' : FirstOrder.Language} {α : Type u'} {β : Type v'} {g : ℕ → ℕ}   (ft
 : (n : ℕ) → L.Term (α ⊕ Fin n) → L'.Ter…
-/
theorem mapTermRel_mapTermRel {L'' : Language}
    (ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin n)))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (ft' : ∀ n, L'.Term (β ⊕ Fin n) → L''.Term (γ ⊕ (Fin n)))
    (fr' : ∀ n, L'.Relations n → L''.Relations n) {n} (φ : L.BoundedFormula α n) :
    ((φ.mapTermRel ft fr fun _ => id).mapTermRel ft' fr' fun _ => id) =
      φ.mapTermRel (fun _ => ft' _ ∘ ft _) (fun _ => fr' _ ∘ fr _) fun _ => id := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ ih3 => simp [mapTermRel, ih3]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.mapTermRel_id_id_id** 是 Mathlib 中的一个定理，位于命名
空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：mapTermRel_id_id_id {n} (φ : L.BoundedFormula α n) : (φ.mapTermRel (fun _ 
=> id) (fun _ => id) fun _ => id) = φ
参数：φ : L.BoundedFormula α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
/-
**FirstOrder.Language.BoundedFormula.mapTermRelEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
FirstOrder.Language.BoundedFormula`。
形式化陈述：mapTermRelEquiv (ft : forall n, L.Term (α oplus (Fin n)) ≃ L'.Term (β oplu
s (Fin n))) (fr : forall n, L.Relations n ≃ L'.Relations n) {n} : L.BoundedFormu
la α n ≃ L'.BoundedFormula β n
参数：ft : forall n, L.Term (α oplus (Fin n)) ≃ L'.Term (β oplus (Fin n))；fr : fora
ll n, L.Relations n ≃ L'.Relations n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An equivalence of bounded formulas given by an equivalence of terms and an equiv
alence of
relations.
-/
def mapTermRelEquiv (ft : ∀ n, L.Term (α ⊕ (Fin n)) ≃ L'.Term (β ⊕ (Fin n)))
    (fr : ∀ n, L.Relations n ≃ L'.Relations n) {n} : L.BoundedFormula α n ≃ L'.BoundedFormula β n :=
  ⟨mapTermRel (fun n => ft n) (fun n => fr n) fun _ => id,
    mapTermRel (fun n => (ft n).symm) (fun n => (fr n).symm) fun _ => id, fun φ => by simp, fun φ =>
    by simp⟩

/-- A function to help relabel the variables in bounded formulas. -/
/-
**FirstOrder.Language.BoundedFormula.relabelAux** 是 Mathlib 中的一个定义，位于命名空间 `First
Order.Language.BoundedFormula`。
形式化陈述：relabelAux (g : α -> β oplus (Fin n)) (k : Nat) : α oplus (Fin k) -> β opl
us (Fin (n + k))
参数：g : α -> β oplus (Fin n)；k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function to help relabel the variables in bounded formulas.
-/
def relabelAux (g : α → β ⊕ (Fin n)) (k : ℕ) : α ⊕ (Fin k) → β ⊕ (Fin (n + k)) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id

@[simp]
/-
**FirstOrder.Language.BoundedFormula.sumElim_comp_relabelAux** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：sumElim_comp_relabelAux {m : Nat} {g : α -> β oplus (Fin n)} {v : β -> M} 
{xs : Fin (n + m) -> M} : Sum.elim v xs ∘ relabelAux g m = Sum.elim (Sum.elim v 
(xs ∘ castAdd m) ∘ g) (xs ∘ natAdd n)
参数：Fin n；n + m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumElim_comp_relabelAux {m : ℕ} {g : α → β ⊕ (Fin n)} {v : β → M}
    {xs : Fin (n + m) → M} : Sum.elim v xs ∘ relabelAux g m =
    Sum.elim (Sum.elim v (xs ∘ castAdd m) ∘ g) (xs ∘ natAdd n) := by
  ext x
  rcases x with x | x
  · simp only [BoundedFormula.relabelAux, Function.comp_apply, Sum.map_inl, Sum.elim_inl]
    rcases g x with l | r <;> simp
  · simp [BoundedFormula.relabelAux]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.relabelAux_sumInl** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.BoundedFormula`。
形式化陈述：relabelAux_sumInl (k : Nat) : relabelAux (Sum.inl : α -> α oplus (Fin n)) 
k = Sum.map id (natAdd n)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem relabelAux_sumInl (k : ℕ) :
    relabelAux (Sum.inl : α → α ⊕ (Fin n)) k = Sum.map id (natAdd n) := by
  ext x
  cases x <;> · simp [relabelAux]

/-- Relabels a bounded formula's variables along a particular function. -/
/-
**FirstOrder.Language.BoundedFormula.relabel** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrd
er.Language.BoundedFormula`。
形式化陈述：relabel (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α k) : L.Boun
dedFormula β (n + k)
参数：g : α -> β oplus (Fin n)；φ : L.BoundedFormula α k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Relabels a bounded formula's variables along a particular function.
-/
def relabel (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α k) : L.BoundedFormula β (n + k) :=
  φ.mapTermRel (fun _ t => t.relabel (relabelAux g _)) (fun _ => id) fun _ =>
    castLE (ge_of_eq (add_assoc _ _ _))

/-- Relabels a bounded formula's free variables along a bijection. -/
/-
**FirstOrder.Language.BoundedFormula.relabelEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Fir
stOrder.Language.BoundedFormula`。
形式化陈述：relabelEquiv (g : α ≃ β) {k} : L.BoundedFormula α k ≃ L.BoundedFormula β k
参数：g : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Relabels a bounded formula's free variables along a bijection.
-/
def relabelEquiv (g : α ≃ β) {k} : L.BoundedFormula α k ≃ L.BoundedFormula β k :=
  mapTermRelEquiv (fun _n => Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
    fun _n => _root_.Equiv.refl _

@[simp]
/-
**FirstOrder.Language.BoundedFormula.relabel_falsum** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.BoundedFormula`。
形式化陈述：relabel_falsum (g : α -> β oplus (Fin n)) {k} : (falsum : L.BoundedFormula
 α k).relabel g = falsum
参数：g : α -> β oplus (Fin n)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem relabel_falsum (g : α → β ⊕ (Fin n)) {k} :
    (falsum : L.BoundedFormula α k).relabel g = falsum :=
  rfl

@[simp]
/-
**FirstOrder.Language.BoundedFormula.relabel_bot** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：relabel_bot (g : α -> β oplus (Fin n)) {k} : (⊥ : L.BoundedFormula α k).re
label g = ⊥
参数：g : α -> β oplus (Fin n)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem relabel_bot (g : α → β ⊕ (Fin n)) {k} : (⊥ : L.BoundedFormula α k).relabel g = ⊥ :=
  rfl

@[simp]
/-
**FirstOrder.Language.BoundedFormula.relabel_imp** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：relabel_imp (g : α -> β oplus (Fin n)) {k} (φ ψ : L.BoundedFormula α k) : 
(φ.imp ψ).relabel g = (φ.relabel g).imp (ψ.relabel g)
参数：g : α -> β oplus (Fin n)；φ ψ : L.BoundedFormula α k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem relabel_imp (g : α → β ⊕ (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ.imp ψ).relabel g = (φ.relabel g).imp (ψ.relabel g) :=
  rfl

@[simp]
/-
**FirstOrder.Language.BoundedFormula.relabel_not** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：relabel_not (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α k) : φ.
not.relabel g = (φ.relabel g).not
参数：g : α -> β oplus (Fin n)；φ : L.BoundedFormula α k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem relabel_not (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α k) :
    φ.not.relabel g = (φ.relabel g).not := by simp [BoundedFormula.not]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.relabel_all** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：relabel_all (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)
) : φ.all.relabel g = (φ.relabel g).all
参数：g : α -> β oplus (Fin n)；φ : L.BoundedFormula α (k + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.relabel.eq_1`：∀ {L : FirstOrder.Langu
age} {α : Type u'} {β : Type v'} {n : ℕ} (g : α → β ⊕ Fin n) {k : ℕ} (φ : L.Boun
dedFormula α k),   FirstOrder.Languag…
· 使用定理 `FirstOrder.Language.BoundedFormula.mapTermRel.eq_5`：∀ {L : FirstOrder.La
nguage} {L' : FirstOrder.Language} {α : Type u'} {β : Type v'} {g : ℕ → ℕ}   (ft
 : (n : ℕ) → L.Term (α ⊕ Fin n) → L'.Ter…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.BoundedFormula.castLE_rfl`：castLE_rfl {n} (h : n <= 
n) (φ : L.BoundedFormula α n) : φ.castLE h = φ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem relabel_all (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.all.relabel g = (φ.relabel g).all := by
  rw [relabel, mapTermRel, relabel]
  simp

@[simp]
/-
**FirstOrder.Language.BoundedFormula.relabel_ex** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.BoundedFormula`。
形式化陈述：relabel_ex (g : α -> β oplus (Fin n)) {k} (φ : L.BoundedFormula α (k + 1))
 : φ.ex.relabel g = (φ.relabel g).ex
参数：g : α -> β oplus (Fin n)；φ : L.BoundedFormula α (k + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.relabel_not`：relabel_not (g : α -> β 
oplus (Fin n)) {k} (φ : L.BoundedFormula α k) : φ.not.relabel g = (φ.relabel g).
not
· 使用定理 `FirstOrder.Language.BoundedFormula.relabel_all`：relabel_all (g : α -> β 
oplus (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) : φ.all.relabel g = (φ.relab
el g).all
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem relabel_ex (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.ex.relabel g = (φ.relabel g).ex := by simp [BoundedFormula.ex]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.relabel_sumInl** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.BoundedFormula`。
形式化陈述：relabel_sumInl (φ : L.BoundedFormula α n) : (φ.relabel Sum.inl : L.Bounded
Formula α (0 + n)) = φ.castLE (ge_of_eq (zero_add n))
参数：φ : L.BoundedFormula α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.BoundedFormula.relabelAux_sumInl`：relabelAux_sumInl 
(k : Nat) : relabelAux (Sum.inl : α -> α oplus (Fin n)) k = Sum.map id (natAdd n
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.natAdd_zero`：∀ {n : ℕ}, Fin.natAdd 0 = Fin.cast ⋯
· 使用定理 `FirstOrder.Language.BoundedFormula.rel.injEq`：∀ {L : FirstOrder.Language
} {α : Type u'} {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) 
(l_1 : ℕ)   (R_1 : L.Relations l_1…
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `FirstOrder.Language.BoundedFormula.castLE.congr_simp`：∀ {L : FirstOrder.
Language} {α : Type u'} {m n : ℕ} (_h : m ≤ n) (a a_1 : L.BoundedFormula α m),  
 a = a_1 → FirstOrder.Language.BoundedForm…
· 使用定理 `FirstOrder.Language.BoundedFormula.castLE_rfl`：castLE_rfl {n} (h : n <= 
n) (φ : L.BoundedFormula α n) : φ.castLE h = φ
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

/-- Substitutes the free variables in a bounded formula with terms, leaving bound variables
unchanged. -/
/-
**FirstOrder.Language.BoundedFormula.subst** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder
.Language.BoundedFormula`。
形式化陈述：subst {n : Nat} (φ : L.BoundedFormula α n) (f : α -> L.Term β) : L.Bounded
Formula β n
参数：φ : L.BoundedFormula α n；f : α -> L.Term β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Substitutes the free variables in a bounded formula with terms, leaving bound va
riables
unchanged.
-/
def subst {n : ℕ} (φ : L.BoundedFormula α n) (f : α → L.Term β) : L.BoundedFormula β n :=
  φ.mapTermRel (fun _ t => t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr)))
    (fun _ => id) fun _ => id

/-- A bijection sending formulas with constants to formulas with extra free variables. -/
/-
**FirstOrder.Language.BoundedFormula.constantsVarsEquiv** 是 Mathlib 中的一个定义，位于命名空
间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：constantsVarsEquiv : L[[γ]].BoundedFormula α n ≃ L.BoundedFormula (γ oplus
 α) n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.instIsAlgebraicConstantsOn`：∀ (α : Type u_1), (First
Order.Language.constantsOn α).IsAlgebraic

--- 原说明 ---
A bijection sending formulas with constants to formulas with extra free variable
s.
-/
def constantsVarsEquiv : L[[γ]].BoundedFormula α n ≃ L.BoundedFormula (γ ⊕ α) n :=
  mapTermRelEquiv (fun _ => Term.constantsVarsEquivLeft) fun _ => Equiv.sumEmpty _ _

/-- Turns all the in-scope bound variables into free variables. -/
@[simp]
/-
**FirstOrder.Language.BoundedFormula.toFormula** 是 Mathlib 中的一个定义，位于命名空间 `FirstO
rder.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → {n : ℕ} → L.BoundedFormula α n
 → L.Formula (α ⊕ Fin n)
参数：α ⊕ Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns all the in-scope bound variables into free variables.
-/
def toFormula : ∀ {n : ℕ}, L.BoundedFormula α n → L.Formula (α ⊕ (Fin n))
  | _n, falsum => falsum
  | _n, equal t₁ t₂ => t₁.equal t₂
  | _n, rel R ts => R.formula ts
  | _n, imp φ₁ φ₂ => φ₁.toFormula.imp φ₂.toFormula
  | _n, all φ =>
    (φ.toFormula.relabel
        (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm))).all

/-- Take the disjunction of a finite set of formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
/-
**FirstOrder.Language.BoundedFormula.iSup** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.
Language.BoundedFormula`。
形式化陈述：iSup [Finite β] (f : β -> L.BoundedFormula α n) : L.BoundedFormula α n
参数：f : β -> L.BoundedFormula α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take the disjunction of a finite set of formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is 
only well-defined up
to equivalence of formulas.
-/
noncomputable def iSup [Finite β] (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊔ ·) ⊥

/-- Take the conjunction of a finite set of formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
/-
**FirstOrder.Language.BoundedFormula.iInf** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.
Language.BoundedFormula`。
形式化陈述：iInf [Finite β] (f : β -> L.BoundedFormula α n) : L.BoundedFormula α n
参数：f : β -> L.BoundedFormula α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take the conjunction of a finite set of formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is 
only well-defined up
to equivalence of formulas.
-/
noncomputable def iInf [Finite β] (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊓ ·) ⊤

end BoundedFormula

namespace LHom

open BoundedFormula

/-- Maps a bounded formula's symbols along a language map. -/
@[simp]
/-
**FirstOrder.Language.LHom.onBoundedFormula** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrde
r.Language.LHom`。
形式化陈述：{L : FirstOrder.Language} →   {L' : FirstOrder.Language} → {α : Type u'} →
 (L →ᴸ L') → {k : ℕ} → L.BoundedFormula α k → L'.BoundedFormula α k
参数：L →ᴸ L'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps a bounded formula's symbols along a language map.
-/
def onBoundedFormula (g : L →ᴸ L') : ∀ {k : ℕ}, L.BoundedFormula α k → L'.BoundedFormula α k
  | _k, falsum => falsum
  | _k, equal t₁ t₂ => (g.onTerm t₁).bdEqual (g.onTerm t₂)
  | _k, rel R ts => (g.onRelation R).boundedFormula (g.onTerm ∘ ts)
  | _k, imp f₁ f₂ => (onBoundedFormula g f₁).imp (onBoundedFormula g f₂)
  | _k, all f => (onBoundedFormula g f).all

@[simp]
/-
**FirstOrder.Language.LHom.id_onBoundedFormula** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.LHom`。
形式化陈述：id_onBoundedFormula : ((LHom.id L).onBoundedFormula : L.BoundedFormula α n
 -> L.BoundedFormula α n) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.LHom.onBoundedFormula.eq_2`：∀ {L : FirstOrder.Langua
ge} {L' : FirstOrder.Language} {α : Type u'} (g : L →ᴸ L') (x : ℕ) (t₁ t₂ : L.Te
rm (α ⊕ Fin x)),   g.onBoundedFormul…
· 使用定理 `FirstOrder.Language.LHom.id_onTerm`：id_onTerm : ((LHom.id L).onTerm : L.
Term α -> L.Term α) = id
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `FirstOrder.Language.Term.bdEqual.eq_1`：∀ {L : FirstOrder.Language} {α : 
Type u'} {n : ℕ} (t₁ t₂ : L.Term (α ⊕ Fin n)),   t₁.bdEqual t₂ = FirstOrder.Lang
uage.BoundedFormula.equal t…
· 使用定理 `FirstOrder.Language.LHom.onBoundedFormula.eq_3`：∀ {L : FirstOrder.Langua
ge} {L' : FirstOrder.Language} {α : Type u'} (g : L →ᴸ L') (x l : ℕ) (_R : L.Rel
ations l)   (ts : Fin l → L.Term (α …
· 使用定理 `FirstOrder.Language.LHom.onBoundedFormula.eq_4`：∀ {L : FirstOrder.Langua
ge} {L' : FirstOrder.Language} {α : Type u'} (g : L →ᴸ L') (x : ℕ)   (f₁ f₂ : L.
BoundedFormula α x), g.onBoundedForm…
· 使用定理 `FirstOrder.Language.LHom.onBoundedFormula.eq_5`：∀ {L : FirstOrder.Langua
ge} {L' : FirstOrder.Language} {α : Type u'} (g : L →ᴸ L') (x : ℕ)   (f : L.Boun
dedFormula α (x + 1)), g.onBoundedFo…
-/
theorem id_onBoundedFormula :
    ((LHom.id L).onBoundedFormula : L.BoundedFormula α n → L.BoundedFormula α n) = id := by
  ext f
  induction f with
  | falsum => rfl
  | equal => rw [onBoundedFormula, LHom.id_onTerm, id, id, id, Term.bdEqual]
  | rel => rw [onBoundedFormula, LHom.id_onTerm]; rfl
  | imp _ _ ih1 ih2 => rw [onBoundedFormula, ih1, ih2, id, id, id]
  | all _ ih3 => rw [onBoundedFormula, ih3, id, id]

@[simp]
/-
**FirstOrder.Language.LHom.comp_onBoundedFormula** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.LHom`。
形式化陈述：comp_onBoundedFormula {L'' : Language} (φ : L' ->ᴸ L'') (ψ : L ->ᴸ L') : (
(φ.comp ψ).onBoundedFormula : L.BoundedFormula α n -> L''.BoundedFormula α n) = 
φ.onBoundedFormula ∘ ψ.onBoundedFormula
参数：φ : L' ->ᴸ L''；ψ : L ->ᴸ L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FirstOrder.Language.LHom.comp_onTerm`：comp_onTerm {L'' : Language} (φ : 
L' ->ᴸ L'') (ψ : L ->ᴸ L') : ((φ.comp ψ).onTerm : L.Term α -> L''.Term α) = φ.on
Term ∘ ψ.onTerm
· 使用定理 `FirstOrder.Language.LHom.onBoundedFormula.eq_2`：∀ {L : FirstOrder.Langua
ge} {L' : FirstOrder.Language} {α : Type u'} (g : L →ᴸ L') (x : ℕ) (t₁ t₂ : L.Te
rm (α ⊕ Fin x)),   g.onBoundedFormul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.LHom.comp_onRelation`：∀ {L : FirstOrder.Language} {L
' : FirstOrder.Language} {L'' : FirstOrder.Language} (g : L' →ᴸ L'') (f : L →ᴸ L
') (x : ℕ)   (R : L.Relations …
· 使用定理 `FirstOrder.Language.LHom.onBoundedFormula.eq_4`：∀ {L : FirstOrder.Langua
ge} {L' : FirstOrder.Language} {α : Type u'} (g : L →ᴸ L') (x : ℕ)   (f₁ f₂ : L.
BoundedFormula α x), g.onBoundedForm…
· 使用定理 `FirstOrder.Language.LHom.onBoundedFormula.eq_5`：∀ {L : FirstOrder.Langua
ge} {L' : FirstOrder.Language} {α : Type u'} (g : L →ᴸ L') (x : ℕ)   (f : L.Boun
dedFormula α (x + 1)), g.onBoundedFo…
-/
theorem comp_onBoundedFormula {L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onBoundedFormula : L.BoundedFormula α n → L''.BoundedFormula α n) =
      φ.onBoundedFormula ∘ ψ.onBoundedFormula := by
  ext f
  induction f with
  | falsum => rfl
  | equal => simp [Term.bdEqual]
  | rel => simp only [onBoundedFormula, comp_onRelation, comp_onTerm, Function.comp_apply]; rfl
  | imp _ _ ih1 ih2 =>
    simp only [onBoundedFormula, Function.comp_apply, ih1, ih2]
  | all _ ih3 => simp only [ih3, onBoundedFormula, Function.comp_apply]

/-- Maps a formula's symbols along a language map. -/
/-
**FirstOrder.Language.LHom.onFormula** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age.LHom`。
形式化陈述：onFormula (g : L ->ᴸ L') : L.Formula α -> L'.Formula α
参数：g : L ->ᴸ L'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps a formula's symbols along a language map.
-/
def onFormula (g : L →ᴸ L') : L.Formula α → L'.Formula α :=
  g.onBoundedFormula

/-- Maps a sentence's symbols along a language map. -/
/-
**FirstOrder.Language.LHom.onSentence** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage.LHom`。
形式化陈述：onSentence (g : L ->ᴸ L') : L.Sentence -> L'.Sentence
参数：g : L ->ᴸ L'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps a sentence's symbols along a language map.
-/
def onSentence (g : L →ᴸ L') : L.Sentence → L'.Sentence :=
  g.onFormula

/-- Maps a theory's symbols along a language map. -/
/-
**FirstOrder.Language.LHom.onTheory** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langua
ge.LHom`。
形式化陈述：onTheory (g : L ->ᴸ L') (T : L.Theory) : L'.Theory
参数：g : L ->ᴸ L'；T : L.Theory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps a theory's symbols along a language map.
-/
def onTheory (g : L →ᴸ L') (T : L.Theory) : L'.Theory :=
  g.onSentence '' T

@[simp]
/-
**FirstOrder.Language.LHom.mem_onTheory** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.La
nguage.LHom`。
形式化陈述：mem_onTheory {g : L ->ᴸ L'} {T : L.Theory} {φ : L'.Sentence} : φ in g.onTh
eory T ↔ exists φ₀, φ₀ in T ∧ g.onSentence φ₀ = φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
-/
theorem mem_onTheory {g : L →ᴸ L'} {T : L.Theory} {φ : L'.Sentence} :
    φ ∈ g.onTheory T ↔ ∃ φ₀, φ₀ ∈ T ∧ g.onSentence φ₀ = φ :=
  Set.mem_image _ _ _

end LHom

namespace LEquiv

/-- Maps a bounded formula's symbols along a language equivalence. -/
@[simps]
/-
**FirstOrder.Language.LEquiv.onBoundedFormula** 是 Mathlib 中的一个定义，位于命名空间 `FirstOr
der.Language.LEquiv`。
形式化陈述：onBoundedFormula (φ : L ≃ᴸ L') : L.BoundedFormula α n ≃ L'.BoundedFormula 
α n where toFun
参数：φ : L ≃ᴸ L'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps a bounded formula's symbols along a language equivalence.
-/
def onBoundedFormula (φ : L ≃ᴸ L') : L.BoundedFormula α n ≃ L'.BoundedFormula α n where
  toFun := φ.toLHom.onBoundedFormula
  invFun := φ.invLHom.onBoundedFormula
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LHom.comp_onBoundedFormula, φ.left_inv,
      LHom.id_onBoundedFormula]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LHom.comp_onBoundedFormula, φ.right_inv,
      LHom.id_onBoundedFormula]
/-
**FirstOrder.Language.LEquiv.onBoundedFormula_symm** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.LEquiv`。
形式化陈述：onBoundedFormula_symm (φ : L ≃ᴸ L') : (φ.onBoundedFormula.symm : L'.Bounde
dFormula α n ≃ L.BoundedFormula α n) = φ.symm.onBoundedFormula
参数：φ : L ≃ᴸ L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem onBoundedFormula_symm (φ : L ≃ᴸ L') :
    (φ.onBoundedFormula.symm : L'.BoundedFormula α n ≃ L.BoundedFormula α n) =
      φ.symm.onBoundedFormula :=
  rfl

/-- Maps a formula's symbols along a language equivalence. -/
/-
**FirstOrder.Language.LEquiv.onFormula** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lan
guage.LEquiv`。
形式化陈述：onFormula (φ : L ≃ᴸ L') : L.Formula α ≃ L'.Formula α
参数：φ : L ≃ᴸ L'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps a formula's symbols along a language equivalence.
-/
def onFormula (φ : L ≃ᴸ L') : L.Formula α ≃ L'.Formula α :=
  φ.onBoundedFormula

@[simp]
/-
**FirstOrder.Language.LEquiv.onFormula_apply** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.LEquiv`。
形式化陈述：onFormula_apply (φ : L ≃ᴸ L') : (φ.onFormula : L.Formula α -> L'.Formula α
) = φ.toLHom.onFormula
参数：φ : L ≃ᴸ L'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem onFormula_apply (φ : L ≃ᴸ L') :
    (φ.onFormula : L.Formula α → L'.Formula α) = φ.toLHom.onFormula :=
  rfl

@[simp]
/-
**FirstOrder.Language.LEquiv.onFormula_symm** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.LEquiv`。
形式化陈述：onFormula_symm (φ : L ≃ᴸ L') : (φ.onFormula.symm : L'.Formula α ≃ L.Formul
a α) = φ.symm.onFormula
参数：φ : L ≃ᴸ L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem onFormula_symm (φ : L ≃ᴸ L') :
    (φ.onFormula.symm : L'.Formula α ≃ L.Formula α) = φ.symm.onFormula :=
  rfl

/-- Maps a sentence's symbols along a language equivalence. -/
@[simps!]
/-
**FirstOrder.Language.LEquiv.onSentence** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage.LEquiv`。
形式化陈述：onSentence (φ : L ≃ᴸ L') : L.Sentence ≃ L'.Sentence
参数：φ : L ≃ᴸ L'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps a sentence's symbols along a language equivalence.
-/
def onSentence (φ : L ≃ᴸ L') : L.Sentence ≃ L'.Sentence :=
  φ.onFormula

end LEquiv

@[inherit_doc] scoped[FirstOrder] infixl:88 " =' " => FirstOrder.Language.Term.bdEqual
-- input \~- or \simeq

@[inherit_doc] scoped[FirstOrder] infixr:62 " ⟹ " => FirstOrder.Language.BoundedFormula.imp
-- input \==>

@[inherit_doc] scoped[FirstOrder] prefix:110 "∀' " => FirstOrder.Language.BoundedFormula.all

@[inherit_doc] scoped[FirstOrder] prefix:arg "∼" => FirstOrder.Language.BoundedFormula.not
-- input \~, the ASCII character ~ has too low precedence

@[inherit_doc] scoped[FirstOrder] infixl:61 " ⇔ " => FirstOrder.Language.BoundedFormula.iff
-- input \<=>

@[inherit_doc] scoped[FirstOrder] prefix:110 "∃' " => FirstOrder.Language.BoundedFormula.ex
-- input \ex

namespace Formula

/-- Relabels a formula's variables along a particular function. -/
/-
**FirstOrder.Language.Formula.relabel** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage.Formula`。
形式化陈述：relabel (g : α -> β) : L.Formula α -> L.Formula β
参数：g : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Relabels a formula's variables along a particular function.
-/
def relabel (g : α → β) : L.Formula α → L.Formula β :=
  @BoundedFormula.relabel _ _ _ 0 (Sum.inl ∘ g) 0

/-- The graph of a function as a first-order formula. -/
/-
**FirstOrder.Language.Formula.graph** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langua
ge.Formula`。
形式化陈述：graph (f : L.Functions n) : L.Formula (Fin (n + 1))
参数：f : L.Functions n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graph of a function as a first-order formula.
-/
def graph (f : L.Functions n) : L.Formula (Fin (n + 1)) :=
  Term.equal (var 0) (func f fun i => var i.succ)

/-- The negation of a formula. -/
protected nonrec abbrev not (φ : L.Formula α) : L.Formula α :=
  φ.not

/-- The implication between formulas, as a formula. -/
/-
**FirstOrder.Language.Formula.imp** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
.Formula`。
形式化陈述：{L : FirstOrder.Language} → {α : Type u'} → L.Formula α → L.Formula α → L.
Formula α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The implication between formulas, as a formula.
-/
protected abbrev imp : L.Formula α → L.Formula α → L.Formula α :=
  BoundedFormula.imp

variable (β) in
/-- `iAlls f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by universally
quantifying over all variables `Sum.inr _`. -/
/-
**FirstOrder.Language.Formula.iAlls** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langua
ge.Formula`。
形式化陈述：iAlls [Finite β] (φ : L.Formula (α oplus β)) : L.Formula α
参数：φ : L.Formula (α oplus β)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)

--- 原说明 ---
`iAlls f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by universally
quantifying over all variables `Sum.inr _`.
-/
noncomputable def iAlls [Finite β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).alls

variable (β) in
/-- `iExs f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by existentially
quantifying over all variables `Sum.inr _`. -/
/-
**FirstOrder.Language.Formula.iExs** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Languag
e.Formula`。
形式化陈述：iExs [Finite β] (φ : L.Formula (α oplus β)) : L.Formula α
参数：φ : L.Formula (α oplus β)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)

--- 原说明 ---
`iExs f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by existentiall
y
quantifying over all variables `Sum.inr _`.
-/
noncomputable def iExs [Finite β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).exs

variable (β) in
/-- `iExsUnique f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by existentially
quantifying over all variables `Sum.inr _` and asserting that the solution should be unique -/
/-
**FirstOrder.Language.Formula.iExsUnique** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.L
anguage.Formula`。
形式化陈述：iExsUnique [Finite β] (φ : L.Formula (α oplus β)) : L.Formula α
参数：φ : L.Formula (α oplus β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`iExsUnique f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by existe
ntially
quantifying over all variables `Sum.inr _` and asserting that the solution shoul
d be unique
-/
noncomputable def iExsUnique [Finite β] (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  iExs β <| φ ⊓ iAlls β
    ((φ.relabel (fun a => Sum.elim (.inl ∘ .inl) .inr a)).imp <|
      .iInf fun g => Term.equal (var (.inr g)) (var (.inl (.inr g))))

variable [DecidableEq α] in
/-- `exClosure φ` is the sentence asserting that there exist values for all free variables of `φ`
such that `φ` holds. -/
/-
**FirstOrder.Language.Formula.exClosure** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage.Formula`。
形式化陈述：exClosure (φ : L.Formula α) : L.Sentence
参数：φ : L.Formula α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`exClosure φ` is the sentence asserting that there exist values for all free var
iables of `φ`
such that `φ` holds.
-/
noncomputable def exClosure (φ : L.Formula α) : L.Sentence :=
  iExs φ.freeVarFinset (Formula.relabel Sum.inr (φ.restrictFreeVar id))

/-- The biimplication between formulas, as a formula. -/
protected nonrec abbrev iff (φ ψ : L.Formula α) : L.Formula α :=
  φ.iff ψ

/-- Take the disjunction of finitely many formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
/-
**FirstOrder.Language.Formula.iSup** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Languag
e.Formula`。
形式化陈述：iSup [Finite α] (f : α -> L.Formula β) : L.Formula β
参数：f : α -> L.Formula β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take the disjunction of finitely many formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is 
only well-defined up
to equivalence of formulas.
-/
noncomputable def iSup [Finite α] (f : α → L.Formula β) : L.Formula β :=
  BoundedFormula.iSup f

/-- Take the conjunction of finitely many formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
/-
**FirstOrder.Language.Formula.iInf** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Languag
e.Formula`。
形式化陈述：iInf [Finite α] (f : α -> L.Formula β) : L.Formula β
参数：f : α -> L.Formula β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take the conjunction of finitely many formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is 
only well-defined up
to equivalence of formulas.
-/
noncomputable def iInf [Finite α] (f : α → L.Formula β) : L.Formula β :=
  BoundedFormula.iInf f

/-- A bijection sending formulas to sentences with constants. -/
/-
**FirstOrder.Language.Formula.equivSentence** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrde
r.Language.Formula`。
形式化陈述：equivSentence : L.Formula α ≃ L[[α]].Sentence
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
A bijection sending formulas to sentences with constants.
-/
def equivSentence : L.Formula α ≃ L[[α]].Sentence :=
  (BoundedFormula.constantsVarsEquiv.trans (BoundedFormula.relabelEquiv (Equiv.sumEmpty _ _))).symm
/-
**FirstOrder.Language.Formula.equivSentence_not** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Formula`。
形式化陈述：equivSentence_not (φ : L.Formula α) : equivSentence φ.not = (equivSentence
 φ).not
参数：φ : L.Formula α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivSentence_not (φ : L.Formula α) : equivSentence φ.not = (equivSentence φ).not :=
  rfl
/-
**FirstOrder.Language.Formula.equivSentence_inf** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Formula`。
形式化陈述：equivSentence_inf (φ ψ : L.Formula α) : equivSentence (φ ⊓ ψ) = equivSente
nce φ ⊓ equivSentence ψ
参数：φ ψ : L.Formula α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivSentence_inf (φ ψ : L.Formula α) :
    equivSentence (φ ⊓ ψ) = equivSentence φ ⊓ equivSentence ψ :=
  rfl

end Formula

namespace Relations

variable (r : L.Relations 2)

/-- The sentence indicating that a basic relation symbol is reflexive. -/
/-
**FirstOrder.Language.Relations.reflexive** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.
Language.Relations`。
形式化陈述：{L : FirstOrder.Language} → L.Relations 2 → L.Sentence
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sentence indicating that a basic relation symbol is reflexive.
-/
protected def reflexive : L.Sentence :=
  ∀' r.boundedFormula₂ (&0) &0

/-- The sentence indicating that a basic relation symbol is irreflexive. -/
/-
**FirstOrder.Language.Relations.irreflexive** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrde
r.Language.Relations`。
形式化陈述：{L : FirstOrder.Language} → L.Relations 2 → L.Sentence
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sentence indicating that a basic relation symbol is irreflexive.
-/
protected def irreflexive : L.Sentence :=
  ∀' ∼(r.boundedFormula₂ (&0) &0)

/-- The sentence indicating that a basic relation symbol is symmetric. -/
/-
**FirstOrder.Language.Relations.symmetric** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.
Language.Relations`。
形式化陈述：{L : FirstOrder.Language} → L.Relations 2 → L.Sentence
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sentence indicating that a basic relation symbol is symmetric.
-/
protected def symmetric : L.Sentence :=
  ∀' ∀' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0)

/-- The sentence indicating that a basic relation symbol is antisymmetric. -/
/-
**FirstOrder.Language.Relations.antisymmetric** 是 Mathlib 中的一个定义，位于命名空间 `FirstOr
der.Language.Relations`。
形式化陈述：{L : FirstOrder.Language} → L.Relations 2 → L.Sentence
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sentence indicating that a basic relation symbol is antisymmetric.
-/
protected def antisymmetric : L.Sentence :=
  ∀' ∀' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0 ⟹ Term.bdEqual (&0) &1)

/-- The sentence indicating that a basic relation symbol is transitive. -/
/-
**FirstOrder.Language.Relations.transitive** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder
.Language.Relations`。
形式化陈述：{L : FirstOrder.Language} → L.Relations 2 → L.Sentence
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sentence indicating that a basic relation symbol is transitive.
-/
protected def transitive : L.Sentence :=
  ∀' ∀' ∀' (r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &2 ⟹ r.boundedFormula₂ (&0) &2)

/-- The sentence indicating that a basic relation symbol is total. -/
/-
**FirstOrder.Language.Relations.total** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage.Relations`。
形式化陈述：{L : FirstOrder.Language} → L.Relations 2 → L.Sentence
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sentence indicating that a basic relation symbol is total.
-/
protected def total : L.Sentence :=
  ∀' ∀' (r.boundedFormula₂ (&0) &1 ⊔ r.boundedFormula₂ (&1) &0)

end Relations

section Cardinality

variable (L)

/-- A sentence indicating that a structure has `n` distinct elements. -/
/-
**FirstOrder.Language.Sentence.cardGe** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage.Sentence`。
形式化陈述：(L : FirstOrder.Language) → ℕ → L.Sentence
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sentence indicating that a structure has `n` distinct elements.
-/
protected def Sentence.cardGe (n : ℕ) : L.Sentence :=
  ((((List.finRange n ×ˢ List.finRange n).filter fun ij : _ × _ => ij.1 ≠ ij.2).map
          fun ij : _ × _ => ∼((&ij.1).bdEqual &ij.2)).foldr
      (· ⊓ ·) ⊤).exs

/-- A theory indicating that a structure is infinite. -/
/-
**FirstOrder.Language.infiniteTheory** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：infiniteTheory : L.Theory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A theory indicating that a structure is infinite.
-/
def infiniteTheory : L.Theory :=
  Set.range (Sentence.cardGe L)

/-- A theory that indicates a structure is nonempty. -/
/-
**FirstOrder.Language.nonemptyTheory** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：nonemptyTheory : L.Theory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A theory that indicates a structure is nonempty.
-/
def nonemptyTheory : L.Theory :=
  {Sentence.cardGe L 1}

/-- A theory indicating that each of a set of constants is distinct. -/
/-
**FirstOrder.Language.distinctConstantsTheory** 是 Mathlib 中的一个定义，位于命名空间 `FirstOr
der.Language`。
形式化陈述：distinctConstantsTheory (s : Set α) : L[[α]].Theory
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A theory indicating that each of a set of constants is distinct.
-/
def distinctConstantsTheory (s : Set α) : L[[α]].Theory :=
  (fun ab : α × α => ((L.con ab.1).term.equal (L.con ab.2).term).not) ''
  (s ×ˢ s ∩ (Set.diagonal α)ᶜ)

variable {L}

open Set
/-
**FirstOrder.Language.distinctConstantsTheory_mono** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language`。
形式化陈述：distinctConstantsTheory_mono {s t : Set α} (h : s subseteq t) : L.distinct
ConstantsTheory s subseteq L.distinctConstantsTheory t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem distinctConstantsTheory_mono {s t : Set α} (h : s ⊆ t) :
    L.distinctConstantsTheory s ⊆ L.distinctConstantsTheory t := by
  unfold distinctConstantsTheory; gcongr
/-
**FirstOrder.Language.monotone_distinctConstantsTheory** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language`。
形式化陈述：monotone_distinctConstantsTheory : Monotone (L.distinctConstantsTheory : S
et α -> L[[α]].Theory)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.distinctConstantsTheory_mono`：distinctConstantsTheor
y_mono {s t : Set α} (h : s subseteq t) : L.distinctConstantsTheory s subseteq L
.distinctConstantsTheory t
-/
theorem monotone_distinctConstantsTheory :
    Monotone (L.distinctConstantsTheory : Set α → L[[α]].Theory) := fun _s _t st =>
  L.distinctConstantsTheory_mono st
/-
**FirstOrder.Language.directed_distinctConstantsTheory** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language`。
形式化陈述：directed_distinctConstantsTheory : Directed (· subseteq ·) (L.distinctCons
tantsTheory : Set α -> L[[α]].Theory)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `OrderTop.instIsDirectedOrder`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
], IsDirectedOrder α
· 使用定理 `FirstOrder.Language.monotone_distinctConstantsTheory`：monotone_distinctC
onstantsTheory : Monotone (L.distinctConstantsTheory : Set α -> L[[α]].Theory)
-/
theorem directed_distinctConstantsTheory :
    Directed (· ⊆ ·) (L.distinctConstantsTheory : Set α → L[[α]].Theory) :=
  Monotone.directed_le monotone_distinctConstantsTheory
/-
**FirstOrder.Language.distinctConstantsTheory_eq_iUnion** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language`。
形式化陈述：distinctConstantsTheory_eq_iUnion (s : Set α) : L.distinctConstantsTheory 
s = ⋃ t : Finset s, L.distinctConstantsTheory (t.map (Function.Embedding.subtype
 fun x => x in s))
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem distinctConstantsTheory_eq_iUnion (s : Set α) :
    L.distinctConstantsTheory s =
      ⋃ t : Finset s,
        L.distinctConstantsTheory (t.map (Function.Embedding.subtype fun x => x ∈ s)) := by
  classical
    simp only [distinctConstantsTheory]
    rw [← image_iUnion, ← iUnion_inter]
    refine congr(_ '' ($(?_) ∩ _))
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

