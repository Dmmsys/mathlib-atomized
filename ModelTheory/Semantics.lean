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

/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
/-
**FirstOrder.Language.Term.realize** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Languag
e.Term`。
形式化陈述：{L : FirstOrder.Language} → {M : Type w} → [L.Structure M] → {α : Type u'}
 → (α → M) → L.Term α → M
参数：α → M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A term `t` with variables indexed by `α` can be evaluated by giving a value to e
ach variable.
-/
def realize (v : α → M) : ∀ _t : L.Term α, M
  | var k => v k
  | func f ts => funMap f fun i => (ts i).realize v

@[simp]
/-
**FirstOrder.Language.Term.realize_var** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Term`。
形式化陈述：realize_var (v : α -> M) (k) : realize v (var k : L.Term α) = v k
参数：v : α -> M；k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem realize_var (v : α → M) (k) : realize v (var k : L.Term α) = v k := rfl

@[simp]
/-
**FirstOrder.Language.Term.realize_func** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.La
nguage.Term`。
形式化陈述：realize_func (v : α -> M) {n} (f : L.Functions n) (ts) : realize v (func f
 ts : L.Term α) = funMap f fun i => (ts i).realize v
参数：v : α -> M；f : L.Functions n；ts。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem realize_func (v : α → M) {n} (f : L.Functions n) (ts) :
    realize v (func f ts : L.Term α) = funMap f fun i => (ts i).realize v := rfl

@[simp]
/-
**FirstOrder.Language.Term.realize_function_term** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Term`。
形式化陈述：realize_function_term {n} (v : Fin n -> M) (f : L.Functions n) : f.term.re
alize v = funMap f v
参数：v : Fin n -> M；f : L.Functions n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem realize_function_term {n} (v : Fin n → M) (f : L.Functions n) :
    f.term.realize v = funMap f v := by
  rfl

@[simp]
/-
**FirstOrder.Language.Term.realize_relabel** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Term`。
形式化陈述：realize_relabel {t : L.Term α} {g : α -> β} {v : β -> M} : (t.relabel g).r
ealize v = t.realize (v ∘ g)
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
theorem realize_relabel {t : L.Term α} {g : α → β} {v : β → M} :
    (t.relabel g).realize v = t.realize (v ∘ g) := by
  induction t with
  | var => rfl
  | func f ts ih => simp [ih]

@[simp]
/-
**FirstOrder.Language.Term.realize_liftAt** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Term`。
形式化陈述：realize_liftAt {n n' m : Nat} {t : L.Term (α oplus (Fin n))} {v : α oplus 
(Fin (n + n')) -> M} : (t.liftAt n' m).realize v = t.realize (v ∘ Sum.map id fun
 i : Fin _ => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n')
参数：α oplus (Fin n)；Fin (n + n')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
-/
theorem realize_liftAt {n n' m : ℕ} {t : L.Term (α ⊕ (Fin n))} {v : α ⊕ (Fin (n + n')) → M} :
    (t.liftAt n' m).realize v =
      t.realize (v ∘ Sum.map id fun i : Fin _ =>
        if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') :=
  realize_relabel

@[simp]
/-
**FirstOrder.Language.Term.realize_constants** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Term`。
形式化陈述：realize_constants {c : L.Constants} {v : α -> M} : c.term.realize v = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.funMap_eq_coe_constants`：funMap_eq_coe_constants {c 
: L.Constants} {x : Fin 0 -> M} : funMap c x = c
-/
theorem realize_constants {c : L.Constants} {v : α → M} : c.term.realize v = c :=
  funMap_eq_coe_constants

@[simp]
/-
**FirstOrder.Language.Term.realize_functions_apply** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Term`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem realize_functions_apply₁ {f : L.Functions 1} {t : L.Term α} {v : α → M} :
    (f.apply₁ t).realize v = funMap f ![t.realize v] := by
  rw [Functions.apply₁, Term.realize]
  refine congr rfl (funext fun i => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]
/-
**FirstOrder.Language.Term.realize_functions_apply** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Term`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem realize_functions_apply₂ {f : L.Functions 2} {t₁ t₂ : L.Term α} {v : α → M} :
    (f.apply₂ t₁ t₂).realize v = funMap f ![t₁.realize v, t₂.realize v] := by
  rw [Functions.apply₂, Term.realize]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]
/-
**FirstOrder.Language.Term.realize_con** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Term`。
形式化陈述：realize_con {A : Set M} {a : A} {v : α -> M} : (L.con a).term.realize v = 
a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem realize_con {A : Set M} {a : A} {v : α → M} : (L.con a).term.realize v = a :=
  rfl

@[simp]
/-
**FirstOrder.Language.Term.realize_subst** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage.Term`。
形式化陈述：realize_subst {t : L.Term α} {tf : α -> L.Term β} {v : β -> M} : (t.subst 
tf).realize v = t.realize fun a => (tf a).realize v
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
theorem realize_subst {t : L.Term α} {tf : α → L.Term β} {v : β → M} :
    (t.subst tf).realize v = t.realize fun a => (tf a).realize v := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]
/-
**FirstOrder.Language.Term.realize_substFunc** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Term`。
形式化陈述：realize_substFunc [L'.Structure M] {c : {n : Nat} -> L.Functions n -> L'.T
erm (Fin n)} (hc : forall {n : Nat} (g) (y : Fin n -> M), g.term.realize y = (c 
g).realize y) (v : β -> M) (x : L.Term β) : (x.substFunc c).realize v = x.realiz
e v
参数：Fin n；hc : forall {n : Nat} (g) (y : Fin n -> M), g.term.realize y = (c g).re
alize y；v : β -> M；x : L.Term β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Term.realize_subst`：realize_subst {t : L.Term α} {tf
 : α -> L.Term β} {v : β -> M} : (t.subst tf).realize v = t.realize fun a => (tf
 a).realize v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Term.realize_function_term`：realize_function_term {n
} (v : Fin n -> M) (f : L.Functions n) : f.term.realize v = funMap f v
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem realize_substFunc [L'.Structure M] {c : {n : ℕ} → L.Functions n → L'.Term (Fin n)}
    (hc : ∀ {n : ℕ} (g) (y : Fin n → M), g.term.realize y = (c g).realize y)
    (v : β → M) (x : L.Term β) :
    (x.substFunc c).realize v = x.realize v := by
  induction x with
  | var => simp
  | func f ts ih => simp [← ih, ← hc]

set_option backward.isDefEq.respectTransparency false in
/-
**FirstOrder.Language.Term.realize_restrictVar** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.Term`。
形式化陈述：realize_restrictVar [DecidableEq α] {t : L.Term α} {f : t.varFinset -> β} 
{v : β -> M} (v' : α -> M) (hv' : forall a, v (f a) = v' a) : (t.restrictVar f).
realize v = t.realize v'
参数：v' : α -> M；hv' : forall a, v (f a) = v' a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem realize_restrictVar [DecidableEq α] {t : L.Term α} {f : t.varFinset → β}
    {v : β → M} (v' : α → M) (hv' : ∀ a, v (f a) = v' a) :
    (t.restrictVar f).realize v = t.realize v' := by
  induction t with
  | var => simp [restrictVar, hv']
  | func _ _ ih =>
    exact congr rfl (funext fun i => ih i ((by simp [Function.comp_apply, hv'])))

/-- A special case of `realize_restrictVar`, included because we can add the `simp` attribute
to it -/
@[simp]
/-
**FirstOrder.Language.Term.realize_restrictVar'** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Term`。
形式化陈述：realize_restrictVar' [DecidableEq α] {t : L.Term α} {s : Set α} (h : ↑t.va
rFinset subseteq s) {v : α -> M} : (t.restrictVar (Set.inclusion h)).realize (v 
∘ (↑)) = t.realize v
参数：h : ↑t.varFinset subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Term.realize_restrictVar`：realize_restrictVar [Decid
ableEq α] {t : L.Term α} {f : t.varFinset -> β} {v : β -> M} (v' : α -> M) (hv' 
: forall a, v (f a) = v' a) : (t.r…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A special case of `realize_restrictVar`, included because we can add the `simp` 
attribute
to it
-/
theorem realize_restrictVar' [DecidableEq α] {t : L.Term α} {s : Set α} (h : ↑t.varFinset ⊆ s)
    {v : α → M} : (t.restrictVar (Set.inclusion h)).realize (v ∘ (↑)) = t.realize v :=
  realize_restrictVar _ (by simp)

set_option backward.isDefEq.respectTransparency false in
/-
**FirstOrder.Language.Term.realize_restrictVarLeft** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Term`。
形式化陈述：realize_restrictVarLeft [DecidableEq α] {γ : Type*} {t : L.Term (α oplus γ
)} {f : t.varFinsetLeft -> β} {xs : β oplus γ -> M} (xs' : α -> M) (hxs' : foral
l a, xs (Sum.inl (f a)) = xs' a) : (t.restrictVarLeft f).realize xs = t.realize 
(Sum.elim xs' (xs ∘ Sum.inr))
参数：α oplus γ；xs' : α -> M；hxs' : forall a, xs (Sum.inl (f a)) = xs' a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem realize_restrictVarLeft [DecidableEq α] {γ : Type*} {t : L.Term (α ⊕ γ)}
    {f : t.varFinsetLeft → β}
    {xs : β ⊕ γ → M} (xs' : α → M) (hxs' : ∀ a, xs (Sum.inl (f a)) = xs' a) :
    (t.restrictVarLeft f).realize xs = t.realize (Sum.elim xs' (xs ∘ Sum.inr)) := by
  induction t with
  | var a => cases a <;> simp [restrictVarLeft, hxs']
  | func _ _ ih =>
    exact congr rfl (funext fun i => ih i (by simp [hxs']))

/-- A special case of `realize_restrictVarLeft`, included because we can add the `simp` attribute
to it -/
@[simp]
/-
**FirstOrder.Language.Term.realize_restrictVarLeft'** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.Term`。
形式化陈述：realize_restrictVarLeft' [DecidableEq α] {γ : Type*} {t : L.Term (α oplus 
γ)} {s : Set α} (h : ↑t.varFinsetLeft subseteq s) {v : α -> M} {xs : γ -> M} : (
t.restrictVarLeft (Set.inclusion h)).realize (Sum.elim (v ∘ (↑)) xs) = t.realize
 (Sum.elim v xs)
参数：α oplus γ；h : ↑t.varFinsetLeft subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Term.realize_restrictVarLeft`：realize_restrictVarLef
t [DecidableEq α] {γ : Type*} {t : L.Term (α oplus γ)} {f : t.varFinsetLeft -> β
} {xs : β oplus γ -> M} (xs' : α -> M)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A special case of `realize_restrictVarLeft`, included because we can add the `si
mp` attribute
to it
-/
theorem realize_restrictVarLeft' [DecidableEq α] {γ : Type*} {t : L.Term (α ⊕ γ)} {s : Set α}
    (h : ↑t.varFinsetLeft ⊆ s) {v : α → M} {xs : γ → M} :
    (t.restrictVarLeft (Set.inclusion h)).realize (Sum.elim (v ∘ (↑)) xs) =
      t.realize (Sum.elim v xs) :=
  realize_restrictVarLeft _ (by simp)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**FirstOrder.Language.Term.realize_constantsToVars** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Term`。
形式化陈述：realize_constantsToVars [L[[α]].Structure M] [(lhomWithConstants L α).IsEx
pansionOn M] {t : L[[α]].Term β} {v : β -> M} : t.constantsToVars.realize (Sum.e
lim (fun a => ↑(L.con a)) v) = t.realize v
参数：lhomWithConstants L α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FirstOrder.Language.Term.realize.eq_2`：∀ {L : FirstOrder.Language} {M : 
Type w} [inst : L.Structure M] {α : Type u'} (v : α → M) (l : ℕ) (f : L.Function
s l)   (ts : Fin l → L.Term…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.withConstants_funMap_sumInl`：withConstants_funMap_su
mInl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M] {n} {f : L.F
unctions n} {x : Fin n -> M} : @funMa…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Language.Term.realize.eq_1`：∀ {L : FirstOrder.Language} {M : 
Type w} [inst : L.Structure M] {α : Type u'} (v : α → M) (k : α),   FirstOrder.L
anguage.Term.realize v (Fir…
· 使用定理 `FirstOrder.Language.funMap_eq_coe_constants`：funMap_eq_coe_constants {c 
: L.Constants} {x : Fin 0 -> M} : funMap c x = c
-/
theorem realize_constantsToVars [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L[[α]].Term β} {v : β → M} :
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
/-
**FirstOrder.Language.Term.realize_varsToConstants** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Term`。
形式化陈述：realize_varsToConstants [L[[α]].Structure M] [(lhomWithConstants L α).IsEx
pansionOn M] {t : L.Term (α oplus β)} {v : β -> M} : t.varsToConstants.realize v
 = t.realize (Sum.elim (fun a => ↑(L.con a)) v)
参数：lhomWithConstants L α；α oplus β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Term.realize_constants`：realize_constants {c : L.Con
stants} {v : α -> M} : c.term.realize v = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FirstOrder.Language.Term.realize.eq_2`：∀ {L : FirstOrder.Language} {M : 
Type w} [inst : L.Structure M] {α : Type u'} (v : α → M) (l : ℕ) (f : L.Function
s l)   (ts : Fin l → L.Term…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.withConstants_funMap_sumInl`：withConstants_funMap_su
mInl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M] {n} {f : L.F
unctions n} {x : Fin n -> M} : @funMa…
-/
theorem realize_varsToConstants [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L.Term (α ⊕ β)} {v : β → M} :
    t.varsToConstants.realize v = t.realize (Sum.elim (fun a => ↑(L.con a)) v) := by
  induction t with
  | var ab => rcases ab with a | b <;> simp [Language.con]
  | func f ts ih =>
    simp only [realize, constantsOn, constantsOnFunc, ih, varsToConstants]
    -- Porting note: below lemma does not work with simp for some reason
    rw [withConstants_funMap_sumInl]
/-
**FirstOrder.Language.Term.realize_constantsVarsEquivLeft** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.Term`。
形式化陈述：realize_constantsVarsEquivLeft [L[[α]].Structure M] [(lhomWithConstants L 
α).IsExpansionOn M] {n} {t : L[[α]].Term (β oplus (Fin n))} {v : β -> M} {xs : F
in n -> M} : (constantsVarsEquivLeft t).realize (Sum.elim (Sum.elim (fun a => ↑(
L.con a)) v) xs) = t.realize (Sum.elim v xs)
参数：lhomWithConstants L α；β oplus (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FirstOrder.Language.Term.constantsVarsEquiv_apply`：∀ {L : FirstOrder.Lan
guage} {α : Type u'} {γ : Type u_1} (a : (L.withConstants γ).Term α),   FirstOrd
er.Language.Term.constantsVarsEquiv a =…
· 使用定理 `FirstOrder.Language.Term.relabelEquiv_symm_apply`：∀ {L : FirstOrder.Lang
uage} {α : Type u'} {β : Type v'} (g : α ≃ β) (a : L.Term β),   (FirstOrder.Lang
uage.Term.relabelEquiv g).symm a = Fir…
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FirstOrder.Language.Term.realize_constantsToVars`：realize_constantsToVar
s [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M] {t : L[[α]].Ter
m β} {v : β -> M} : t.constantsToVars.…
-/
theorem realize_constantsVarsEquivLeft [L[[α]].Structure M]
    [(lhomWithConstants L α).IsExpansionOn M] {n} {t : L[[α]].Term (β ⊕ (Fin n))} {v : β → M}
    {xs : Fin n → M} :
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
/-
**FirstOrder.Language.LHom.realize_onTerm** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.LHom`。
形式化陈述：realize_onTerm [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] (t : L.
Term α) (v : α -> M) : (φ.onTerm t).realize v = t.realize v
参数：φ : L ->ᴸ L'；t : L.Term α；v : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Term.realize.eq_2`：∀ {L : FirstOrder.Language} {M : 
Type w} [inst : L.Structure M] {α : Type u'} (v : α → M) (l : ℕ) (f : L.Function
s l)   (ts : Fin l → L.Term…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.LHom.map_onFunction`：map_onFunction {M : Type*} [L.S
tructure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n} (f : L.Functions n) (x : Fi
n n -> M) : funMap (ϕ.onFunct…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem realize_onTerm [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (t : L.Term α)
    (v : α → M) : (φ.onTerm t).realize v = t.realize v := by
  induction t with
  | var => rfl
  | func f ts ih => simp only [Term.realize, LHom.onTerm, LHom.map_onFunction, ih]

end LHom

@[simp]
/-
**FirstOrder.Language.HomClass.realize_term** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.HomClass`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} {N : Type u_1} [inst : L.Structur
e M] [inst_1 : L.Structure N] {α : Type u'}   {F : Type u_4} [inst_2 : FunLike F
 M N] [L.HomClass F M N] (g : F) {t : L.Term α} {v : α → M},   FirstOrder.Langua
ge.Term.realize (⇑g ∘ v) t = g (FirstOrder.Language.Term.realize v t)
参数：g : F；⇑g ∘ v；FirstOrder.Language.Term.realize v t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Term.realize.eq_2`：∀ {L : FirstOrder.Language} {M : 
Type w} [inst : L.Structure M] {α : Type u'} (v : α → M) (l : ℕ) (f : L.Function
s l)   (ts : Fin l → L.Term…
· 使用定理 `FirstOrder.Language.HomClass.map_fun`：∀ {L : outParam FirstOrder.Languag
e} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {inst : 
FunLike F M N} {inst_1 : L…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HomClass.realize_term {F : Type*} [FunLike F M N] [HomClass L F M N]
    (g : F) {t : L.Term α} {v : α → M} :
    t.realize (g ∘ v) = g (t.realize v) := by
  induction t
  · rfl
  · rw [Term.realize, Term.realize, HomClass.map_fun]
    refine congr rfl ?_
    ext x
    simp [*]

variable {n : ℕ}

namespace BoundedFormula

open Term

/-- A bounded formula can be evaluated as true or false by giving values to each free and bound
variable. -/
/-
**FirstOrder.Language.BoundedFormula.Realize** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrd
er.Language.BoundedFormula`。
形式化陈述：{L : FirstOrder.Language} →   {M : Type w} → [L.Structure M] → {α : Type u
'} → {l : ℕ} → L.BoundedFormula α l → (α → M) → (Fin l → M) → Prop
参数：α → M；Fin l → M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded formula can be evaluated as true or false by giving values to each fre
e and bound
variable.
-/
def Realize : ∀ {l} (_f : L.BoundedFormula α l) (_v : α → M) (_xs : Fin l → M), Prop
  | _, falsum, _v, _xs => False
  | _, equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, rel R ts, v, xs => RelMap R fun i => (ts i).realize (Sum.elim v xs)
  | _, imp f₁ f₂, v, xs => Realize f₁ v xs → Realize f₂ v xs
  | _, all f, v, xs => ∀ x : M, Realize f v (snoc xs x)

variable {l : ℕ} {φ ψ : L.BoundedFormula α l} {θ : L.BoundedFormula α l.succ}
variable {v : α → M} {xs : Fin l → M}

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_bot** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：realize_bot : (⊥ : L.BoundedFormula α l).Realize v xs ↔ False
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_bot : (⊥ : L.BoundedFormula α l).Realize v xs ↔ False :=
  Iff.rfl

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_not** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：realize_not : φ.not.Realize v xs ↔ ¬φ.Realize v xs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_not : φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  Iff.rfl

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_bdEqual** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_bdEqual (t₁ t₂ : L.Term (α oplus (Fin l))) : (t₁.bdEqual t₂).Reali
ze v xs ↔ t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
参数：t₁ t₂ : L.Term (α oplus (Fin l))。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_bdEqual (t₁ t₂ : L.Term (α ⊕ (Fin l))) :
    (t₁.bdEqual t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_top** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：realize_top : (⊤ : L.BoundedFormula α l).Realize v xs ↔ True
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_top : (⊤ : L.BoundedFormula α l).Realize v xs ↔ True := by simp [Top.top]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_inf** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：realize_inf : (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_inf : (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp [Realize, Min.min]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_foldr_inf** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_foldr_inf (l : List (L.BoundedFormula α n)) (v : α -> M) (xs : Fin
 n -> M) : (l.foldr (· ⊓ ·) ⊤).Realize v xs ↔ forall φ in l, BoundedFormula.Real
ize φ v xs
参数：l : List (L.BoundedFormula α n)；v : α -> M；xs : Fin n -> M。
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
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_foldr_inf (l : List (L.BoundedFormula α n)) (v : α → M) (xs : Fin n → M) :
    (l.foldr (· ⊓ ·) ⊤).Realize v xs ↔ ∀ φ ∈ l, BoundedFormula.Realize φ v xs := by
  induction l with
  | nil => simp
  | cons φ l ih => simp [ih]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_imp** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：realize_imp : (φ.imp ψ).Realize v xs ↔ φ.Realize v xs -> ψ.Realize v xs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_imp : (φ.imp ψ).Realize v xs ↔ φ.Realize v xs → ψ.Realize v xs := by
  simp only [Realize]

/-- List.foldr on BoundedFormula.imp gives a big "And" of input conditions. -/
/-
**FirstOrder.Language.BoundedFormula.realize_foldr_imp** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_foldr_imp {k : Nat} (l : List (L.BoundedFormula α k)) (f : L.Bound
edFormula α k) : forall (v : α -> M) xs, (l.foldr BoundedFormula.imp f).Realize 
v xs = ((forall i in l, i.Realize v xs) -> f.Realize v xs)
参数：l : List (L.BoundedFormula α k)；f : L.BoundedFormula α k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False

--- 原说明 ---
List.foldr on BoundedFormula.imp gives a big "And" of input conditions.
-/
theorem realize_foldr_imp {k : ℕ} (l : List (L.BoundedFormula α k))
    (f : L.BoundedFormula α k) :
    ∀ (v : α → M) xs,
      (l.foldr BoundedFormula.imp f).Realize v xs =
      ((∀ i ∈ l, i.Realize v xs) → f.Realize v xs) := by
  intro v xs
  induction l
  next => simp
  next f' _ _ => by_cases f'.Realize v xs <;> simp [*]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_rel** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：realize_rel {k : Nat} {R : L.Relations k} {ts : Fin k -> L.Term _} : (R.bo
undedFormula ts).Realize v xs ↔ RelMap R fun i => (ts i).realize (Sum.elim v xs)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_rel {k : ℕ} {R : L.Relations k} {ts : Fin k → L.Term _} :
    (R.boundedFormula ts).Realize v xs ↔ RelMap R fun i => (ts i).realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_rel** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：realize_rel {k : Nat} {R : L.Relations k} {ts : Fin k -> L.Term _} : (R.bo
undedFormula ts).Realize v xs ↔ RelMap R fun i => (ts i).realize (Sum.elim v xs)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_rel₁ {R : L.Relations 1} {t : L.Term _} :
    (R.boundedFormula₁ t).Realize v xs ↔ RelMap R ![t.realize (Sum.elim v xs)] := by
  rw [Relations.boundedFormula₁, realize_rel, iff_eq_eq]
  refine congr rfl (funext fun _ => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_rel** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：realize_rel {k : Nat} {R : L.Relations k} {ts : Fin k -> L.Term _} : (R.bo
undedFormula ts).Realize v xs ↔ RelMap R fun i => (ts i).realize (Sum.elim v xs)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
    (R.boundedFormula₂ t₁ t₂).Realize v xs ↔
      RelMap R ![t₁.realize (Sum.elim v xs), t₂.realize (Sum.elim v xs)] := by
  rw [Relations.boundedFormula₂, realize_rel, iff_eq_eq]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_sup** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：realize_sup : (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
theorem realize_sup : (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  simp only [max]
  tauto

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_foldr_sup** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_foldr_sup (l : List (L.BoundedFormula α n)) (v : α -> M) (xs : Fin
 n -> M) : (l.foldr (· ⊔ ·) ⊥).Realize v xs ↔ exists φ in l, BoundedFormula.Real
ize φ v xs
参数：l : List (L.BoundedFormula α n)；v : α -> M；xs : Fin n -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_foldr_sup (l : List (L.BoundedFormula α n)) (v : α → M) (xs : Fin n → M) :
    (l.foldr (· ⊔ ·) ⊥).Realize v xs ↔ ∃ φ ∈ l, BoundedFormula.Realize φ v xs := by
  induction l with
  | nil => simp
  | cons φ l ih =>
    simp_rw [List.foldr_cons, realize_sup, ih, List.mem_cons, or_and_right, exists_or,
      exists_eq_left]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_all** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：realize_all : (all θ).Realize v xs ↔ forall a : M, θ.Realize v (Fin.snoc x
s a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_all : (all θ).Realize v xs ↔ ∀ a : M, θ.Realize v (Fin.snoc xs a) :=
  Iff.rfl

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_ex** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.BoundedFormula`。
形式化陈述：realize_ex : θ.ex.Realize v xs ↔ exists a : M, θ.Realize v (Fin.snoc xs a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.ex.eq_1`：∀ {L : FirstOrder.Language} 
{α : Type u'} {n : ℕ} (φ : L.BoundedFormula α (n + 1)), φ.ex = φ.not.all.not
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_not`：realize_not : φ.not.Real
ize v xs ↔ ¬φ.Realize v xs
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_all`：realize_all : (all θ).Re
alize v xs ↔ forall a : M, θ.Realize v (Fin.snoc xs a)
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_ex : θ.ex.Realize v xs ↔ ∃ a : M, θ.Realize v (Fin.snoc xs a) := by
  rw [BoundedFormula.ex, realize_not, realize_all, not_forall]
  simp_rw [realize_not, Classical.not_not]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_iff** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：realize_iff : (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_iff : (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs) := by
  simp only [BoundedFormula.iff, realize_inf, realize_imp, ← iff_def]
/-
**FirstOrder.Language.BoundedFormula.realize_castLE_of_eq** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_castLE_of_eq {m n : Nat} (h : m = n) {h' : m <= n} {φ : L.BoundedF
ormula α m} {v : α -> M} {xs : Fin n -> M} : (φ.castLE h').Realize v xs ↔ φ.Real
ize v (xs ∘ Fin.cast h)
参数：h : m = n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.BoundedFormula.castLE_rfl`：castLE_rfl {n} (h : n <= 
n) (φ : L.BoundedFormula α n) : φ.castLE h = φ
· 使用定理 `Fin.cast_refl`：∀ (n : ℕ) (h : n = n), Fin.cast h = id
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_castLE_of_eq {m n : ℕ} (h : m = n) {h' : m ≤ n} {φ : L.BoundedFormula α m}
    {v : α → M} {xs : Fin n → M} : (φ.castLE h').Realize v xs ↔ φ.Realize v (xs ∘ Fin.cast h) := by
  subst h
  simp only [castLE_rfl, cast_refl, Function.comp_id]
/-
**FirstOrder.Language.BoundedFormula.realize_mapTermRel_id** 是 Mathlib 中的一个定理，位于
命名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_mapTermRel_id [L'.Structure M] {ft : forall n, L.Term (α oplus (Fi
n n)) -> L'.Term (β oplus (Fin n))} {fr : forall n, L.Relations n -> L'.Relation
s n} {n} {φ : L.BoundedFormula α n} {v : α -> M} {v' : β -> M} {xs : Fin n -> M}
 (h1 : forall (n) (t : L.Term (α oplus (Fin n))) (xs : Fin n -> M), (ft n t).rea
lize (Sum.elim v' xs) = t.realize (Sum.elim v xs)) (h2 : forall (n) (R : L.Relat
ions n) (x : Fin n -> M), RelMap (fr n R) x = RelMap R x) : (φ.mapTermRel ft fr 
fun _ => id).Realize v' xs
参数：α oplus (Fin n)；β oplus (Fin n)；h1 : forall (n) (t : L.Term (α oplus (Fin n))
) (xs : Fin n -> M), (ft n t).realize (Sum.elim v' xs) = t.realize (Sum.elim v x
s)；h2 : forall (n) (R : L.Relations n) (x : Fin n -> M), RelMap (fr n R) x = Rel
Map R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_2`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (t₁ t₂ : L.Term (α ⊕…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_3`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (l : ℕ) (R : L.Relat…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_5`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (f : L.BoundedFormul…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem realize_mapTermRel_id [L'.Structure M]
    {ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin n))}
    {fr : ∀ n, L.Relations n → L'.Relations n} {n} {φ : L.BoundedFormula α n} {v : α → M}
    {v' : β → M} {xs : Fin n → M}
    (h1 :
      ∀ (n) (t : L.Term (α ⊕ (Fin n))) (xs : Fin n → M),
        (ft n t).realize (Sum.elim v' xs) = t.realize (Sum.elim v xs))
    (h2 : ∀ (n) (R : L.Relations n) (x : Fin n → M), RelMap (fr n R) x = RelMap R x) :
    (φ.mapTermRel ft fr fun _ => id).Realize v' xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel, Realize, h1]
  | rel => simp [mapTermRel, Realize, h1, h2]
  | imp _ _ ih1 ih2 => simp [mapTermRel, Realize, ih1, ih2]
  | all _ ih => simp only [mapTermRel, Realize, ih, id]
/-
**FirstOrder.Language.BoundedFormula.realize_mapTermRel_add_castLe** 是 Mathlib 中
的一个定理，位于命名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_mapTermRel_add_castLe [L'.Structure M] {k : Nat} {ft : forall n, L
.Term (α oplus (Fin n)) -> L'.Term (β oplus (Fin (k + n)))} {fr : forall n, L.Re
lations n -> L'.Relations n} {n} {φ : L.BoundedFormula α n} (v : forall {n}, (Fi
n (k + n) -> M) -> α -> M) {v' : β -> M} (xs : Fin (k + n) -> M) (h1 : forall (n
) (t : L.Term (α oplus (Fin n))) (xs' : Fin (k + n) -> M), (ft n t).realize (Sum
.elim v' xs') = t.realize (Sum.elim (v xs') (xs' ∘ Fin.natAdd _))) (h2 : forall 
(n) (R : L.Relations n) (x
参数：α oplus (Fin n)；β oplus (Fin (k + n))；v : forall {n}, (Fin (k + n) -> M) -> α
 -> M；xs : Fin (k + n) -> M；h1 : forall (n) (t : L.Term (α oplus (Fin n))) (xs' 
: Fin (k + n) -> M), (ft n t).realize (Sum.elim v' xs') = t.realize (Sum.elim (v
 xs') (xs' ∘ Fin.natAdd _))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_2`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (t₁ t₂ : L.Term (α ⊕…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_3`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (l : ℕ) (R : L.Relat…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FirstOrder.Language.BoundedFormula.castLE_rfl`：castLE_rfl {n} (h : n <= 
n) (φ : L.BoundedFormula α n) : φ.castLE h = φ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.snoc_comp_natAdd`：snoc_comp_natAdd {n m : Nat} {α : Sort*} (f : Fin 
(m + n) -> α) (a : α) : (snoc f a : Fin _ -> α) ∘ (natAdd m : Fin (n + 1) -> Fin
 (m + n + …
-/
theorem realize_mapTermRel_add_castLe [L'.Structure M] {k : ℕ}
    {ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin (k + n)))}
    {fr : ∀ n, L.Relations n → L'.Relations n} {n} {φ : L.BoundedFormula α n}
    (v : ∀ {n}, (Fin (k + n) → M) → α → M) {v' : β → M} (xs : Fin (k + n) → M)
    (h1 :
      ∀ (n) (t : L.Term (α ⊕ (Fin n))) (xs' : Fin (k + n) → M),
        (ft n t).realize (Sum.elim v' xs') = t.realize (Sum.elim (v xs') (xs' ∘ Fin.natAdd _)))
    (h2 : ∀ (n) (R : L.Relations n) (x : Fin n → M), RelMap (fr n R) x = RelMap R x)
    (hv : ∀ (n) (xs : Fin (k + n) → M) (x : M), @v (n + 1) (snoc xs x : Fin _ → M) = v xs) :
    (φ.mapTermRel ft fr fun _ => castLE (add_assoc _ _ _).symm.le).Realize v' xs ↔
      φ.Realize (v xs) (xs ∘ Fin.natAdd _) := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel, Realize, h1]
  | rel => simp [mapTermRel, Realize, h1, h2]
  | imp _ _ ih1 ih2 => simp [mapTermRel, Realize, ih1, ih2]
  | all _ ih => simp [mapTermRel, Realize, ih, hv]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_relabel** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_relabel {m n : Nat} {φ : L.BoundedFormula α n} {g : α -> β oplus (
Fin m)} {v : β -> M} {xs : Fin (m + n) -> M} : (φ.relabel g).Realize v xs ↔ φ.Re
alize (Sum.elim v (xs ∘ Fin.castAdd n) ∘ g) (xs ∘ Fin.natAdd m)
参数：Fin m；m + n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_mapTermRel_add_castLe`：realiz
e_mapTermRel_add_castLe [L'.Structure M] {k : Nat} {ft : forall n, L.Term (α opl
us (Fin n)) -> L'.Term (β oplus (Fin (k + n)))} {fr : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用定理 `FirstOrder.Language.BoundedFormula.sumElim_comp_relabelAux`：sumElim_comp
_relabelAux {m : Nat} {g : α -> β oplus (Fin n)} {v : β -> M} {xs : Fin (n + m) 
-> M} : Sum.elim v xs ∘ relabelAux g m = Sum.eli…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Fin.snoc_comp_castAdd`：snoc_comp_castAdd {n m : Nat} {α : Sort*} (f : Fi
n (n + m) -> α) (a : α) : (snoc f a : Fin _ -> α) ∘ castAdd (m + 1) = f ∘ castAd
d m
-/
theorem realize_relabel {m n : ℕ} {φ : L.BoundedFormula α n} {g : α → β ⊕ (Fin m)} {v : β → M}
    {xs : Fin (m + n) → M} :
    (φ.relabel g).Realize v xs ↔
      φ.Realize (Sum.elim v (xs ∘ Fin.castAdd n) ∘ g) (xs ∘ Fin.natAdd m) := by
  apply realize_mapTermRel_add_castLe <;> simp
/-
**FirstOrder.Language.BoundedFormula.realize_liftAt** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.BoundedFormula`。
形式化陈述：realize_liftAt {n n' m : Nat} {φ : L.BoundedFormula α n} {v : α -> M} {xs 
: Fin (n + n') -> M} (hmn : m <= n) : (φ.liftAt n' m).Realize v xs ↔ φ.Realize v
 (xs ∘ fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n')
参数：n + n'；hmn : m <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.liftAt.eq_1`：∀ {L : FirstOrder.Langua
ge} {α : Type u'} {x : ℕ} (n' m : ℕ) (φ : L.BoundedFormula α x),   FirstOrder.La
nguage.BoundedFormula.liftAt n' m φ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_1`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M),   FirstOrder.Language…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_2`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (t₁ t₂ : L.Term (α ⊕…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Language.Term.realize_liftAt`：realize_liftAt {n n' m : Nat} {
t : L.Term (α oplus (Fin n))} {v : α oplus (Fin (n + n')) -> M} : (t.liftAt n' m
).realize v = t.realize (v ∘ …
· 使用定理 `Sum.elim_comp_map`：∀ {α : Type u_1} {β : Type u_2} {ε : Sort u_3} {γ : T
ype u_4} {δ : Type u_5} {f₁ : α → β} {f₂ : β → ε} {g₁ : γ → δ}   {g₂ : δ → ε}, S
um.elim…
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_3`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (l : ℕ) (R : L.Relat…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_4`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (f₁ f₂ : L.BoundedFo…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_5`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (f : L.BoundedFormul…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_castLE_of_eq`：realize_castLE_
of_eq {m n : Nat} (h : m = n) {h' : m <= n} {φ : L.BoundedFormula α m} {v : α ->
 M} {xs : Fin n -> M} : (φ.castLE h').Realize…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用引理 `iff_eq_eq`：iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b)
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `Fin.cast.congr_simp`：∀ {n m : ℕ} (eq : n = m) (i i_1 : Fin n), i = i_1 →
 Fin.cast eq i = Fin.cast eq i_1
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
（共 32 条，此处仅展示前 30 条）
-/
theorem realize_liftAt {n n' m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Fin (n + n') → M}
    (hmn : m ≤ n) :
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
/-
**FirstOrder.Language.BoundedFormula.realize_liftAt_one** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_liftAt_one {n m : Nat} {φ : L.BoundedFormula α n} {v : α -> M} {xs
 : Fin (n + 1) -> M} (hmn : m <= n) : (φ.liftAt 1 m).Realize v xs ↔ φ.Realize v 
(xs ∘ fun i => if ↑i < m then castSucc i else i.succ)
参数：n + 1；hmn : m <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_liftAt_one {n m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Fin (n + 1) → M}
    (hmn : m ≤ n) :
    (φ.liftAt 1 m).Realize v xs ↔
      φ.Realize v (xs ∘ fun i => if ↑i < m then castSucc i else i.succ) := by
  simp [realize_liftAt, hmn, castSucc]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_liftAt_one_self** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_liftAt_one_self {n : Nat} {φ : L.BoundedFormula α n} {v : α -> M} 
{xs : Fin (n + 1) -> M} : (φ.liftAt 1 n).Realize v xs ↔ φ.Realize v (xs ∘ castSu
cc)
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_liftAt_one`：realize_liftAt_on
e {n m : Nat} {φ : L.BoundedFormula α n} {v : α -> M} {xs : Fin (n + 1) -> M} (h
mn : m <= n) : (φ.liftAt 1 m).Realize v xs …
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用引理 `iff_eq_eq`：iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
-/
theorem realize_liftAt_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : α → M}
    {xs : Fin (n + 1) → M} : (φ.liftAt 1 n).Realize v xs ↔ φ.Realize v (xs ∘ castSucc) := by
  rw [realize_liftAt_one (refl n), iff_eq_eq]
  refine congr rfl (congr rfl (funext fun i => ?_))
  rw [if_pos i.is_lt]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_subst** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.BoundedFormula`。
形式化陈述：realize_subst {φ : L.BoundedFormula α n} {tf : α -> L.Term β} {v : β -> M}
 {xs : Fin n -> M} : (φ.subst tf).Realize v xs ↔ φ.Realize (fun a => (tf a).real
ize v) xs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_mapTermRel_id`：realize_mapTer
mRel_id [L'.Structure M] {ft : forall n, L.Term (α oplus (Fin n)) -> L'.Term (β 
oplus (Fin n))} {fr : forall n, L.Relations n …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Term.realize_subst`：realize_subst {t : L.Term α} {tf
 : α -> L.Term β} {v : β -> M} : (t.subst tf).realize v = t.realize fun a => (tf
 a).realize v
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem realize_subst {φ : L.BoundedFormula α n} {tf : α → L.Term β} {v : β → M} {xs : Fin n → M} :
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
/-
**FirstOrder.Language.BoundedFormula.realize_restrictFreeVar** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_restrictFreeVar [DecidableEq α] {n : Nat} {φ : L.BoundedFormula α 
n} {f : φ.freeVarFinset -> β} {v : β -> M} {xs : Fin n -> M} (v' : α -> M) (hv' 
: forall a, v (f a) = v' a) : (φ.restrictFreeVar f).Realize v xs ↔ φ.Realize v' 
xs
参数：v' : α -> M；hv' : forall a, v (f a) = v' a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_2`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (t₁ t₂ : L.Term (α ⊕…
· 使用定理 `FirstOrder.Language.Term.realize_restrictVarLeft`：realize_restrictVarLef
t [DecidableEq α] {γ : Type*} {t : L.Term (α oplus γ)} {f : t.varFinsetLeft -> β
} {xs : β oplus γ -> M} (xs' : α -> M)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_3`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (l : ℕ) (R : L.Relat…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_4`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (f₁ f₂ : L.BoundedFo…
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_5`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (f : L.BoundedFormul…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
-/
theorem realize_restrictFreeVar [DecidableEq α] {n : ℕ} {φ : L.BoundedFormula α n}
    {f : φ.freeVarFinset → β} {v : β → M} {xs : Fin n → M}
    (v' : α → M) (hv' : ∀ a, v (f a) = v' a) :
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
    rw [ih1, ih2] <;> simp [hv']
  | all _ ih3 =>
    simp only [restrictFreeVar, Realize]
    refine forall_congr' (fun _ => ?_)
    rw [ih3]; simp [hv']

/-- A special case of `realize_restrictFreeVar`, included because we can add the `simp` attribute
to it -/
@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_restrictFreeVar'** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_restrictFreeVar' [DecidableEq α] {n : Nat} {φ : L.BoundedFormula α
 n} {s : Set α} (h : ↑φ.freeVarFinset subseteq s) {v : α -> M} {xs : Fin n -> M}
 : (φ.restrictFreeVar (Set.inclusion h)).Realize (v ∘ (↑)) xs ↔ φ.Realize v xs
参数：h : ↑φ.freeVarFinset subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_restrictFreeVar`：realize_rest
rictFreeVar [DecidableEq α] {n : Nat} {φ : L.BoundedFormula α n} {f : φ.freeVarF
inset -> β} {v : β -> M} {xs : Fin n -> M} (v' :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A special case of `realize_restrictFreeVar`, included because we can add the `si
mp` attribute
to it
-/
theorem realize_restrictFreeVar' [DecidableEq α] {n : ℕ} {φ : L.BoundedFormula α n} {s : Set α}
    (h : ↑φ.freeVarFinset ⊆ s) {v : α → M} {xs : Fin n → M} :
    (φ.restrictFreeVar (Set.inclusion h)).Realize (v ∘ (↑)) xs ↔ φ.Realize v xs :=
  realize_restrictFreeVar _ (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**FirstOrder.Language.BoundedFormula.realize_constantsVarsEquiv** 是 Mathlib 中的一个
定理，位于命名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_constantsVarsEquiv [L[[α]].Structure M] [(lhomWithConstants L α).I
sExpansionOn M] {n} {φ : L[[α]].BoundedFormula β n} {v : β -> M} {xs : Fin n -> 
M} : (constantsVarsEquiv φ).Realize (Sum.elim (fun a => ↑(L.con a)) v) xs ↔ φ.Re
alize v xs
参数：lhomWithConstants L α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_mapTermRel_id`：realize_mapTer
mRel_id [L'.Structure M] {ft : forall n, L.Term (α oplus (Fin n)) -> L'.Term (β 
oplus (Fin n))} {fr : forall n, L.Relations n …
· 使用定理 `FirstOrder.Language.instIsAlgebraicConstantsOn`：∀ (α : Type u_1), (First
Order.Language.constantsOn α).IsAlgebraic
· 使用定理 `FirstOrder.Language.Term.realize_constantsVarsEquivLeft`：realize_constan
tsVarsEquivLeft [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M] {
n} {t : L[[α]].Term (β oplus (Fin n))} {v : β…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.LHom.map_onRelation`：map_onRelation {M : Type*} [L.S
tructure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n} (R : L.Relations n) (x : Fi
n n -> M) : RelMap (ϕ.onRelat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_constantsVarsEquiv [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {φ : L[[α]].BoundedFormula β n} {v : β → M} {xs : Fin n → M} :
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
/-
**FirstOrder.Language.BoundedFormula.realize_relabelEquiv** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_relabelEquiv {g : α ≃ β} {k} {φ : L.BoundedFormula α k} {v : β -> 
M} {xs : Fin k -> M} : (relabelEquiv g φ).Realize v xs ↔ φ.Realize (v ∘ g) xs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.mapTermRelEquiv_apply`：∀ {L : FirstOr
der.Language} {L' : FirstOrder.Language} {α : Type u'} {β : Type v'}   (ft : (n 
: ℕ) → L.Term (α ⊕ Fin n) ≃ L'.Term (β ⊕ Fin n…
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_mapTermRel_id`：realize_mapTer
mRel_id [L'.Structure M] {ft : forall n, L.Term (α oplus (Fin n)) -> L'.Term (β 
oplus (Fin n))} {fr : forall n, L.Relations n …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FirstOrder.Language.Term.relabelEquiv_apply`：∀ {L : FirstOrder.Language}
 {α : Type u'} {β : Type v'} (g : α ≃ β) (a : L.Term α),   (FirstOrder.Language.
Term.relabelEquiv g) a = FirstOrd…
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem realize_relabelEquiv {g : α ≃ β} {k} {φ : L.BoundedFormula α k} {v : β → M}
    {xs : Fin k → M} : (relabelEquiv g φ).Realize v xs ↔ φ.Realize (v ∘ g) xs := by
  simp only [relabelEquiv, mapTermRelEquiv_apply, Equiv.coe_refl]
  refine realize_mapTermRel_id (fun n t xs => ?_) fun _ _ _ => rfl
  simp only [relabelEquiv_apply, Term.realize_relabel]
  refine congr (congr rfl ?_) rfl
  ext (i | i) <;> rfl

variable [Nonempty M]
/-
**FirstOrder.Language.BoundedFormula.realize_all_liftAt_one_self** 是 Mathlib 中的一
个定理，位于命名空间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_all_liftAt_one_self {n : Nat} {φ : L.BoundedFormula α n} {v : α ->
 M} {xs : Fin n -> M} : (φ.liftAt 1 n).all.Realize v xs ↔ φ.Realize v xs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.snoc_comp_castSucc`：snoc_comp_castSucc {α : Sort*} {a : α} {f : Fin 
n -> α} : (snoc f a : Fin (n + 1) -> α) ∘ castSucc = f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_all_liftAt_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : α → M}
    {xs : Fin n → M} : (φ.liftAt 1 n).all.Realize v xs ↔ φ.Realize v xs := by
  simp

end BoundedFormula

namespace LHom

open BoundedFormula

@[simp]
/-
**FirstOrder.Language.LHom.realize_onBoundedFormula** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.LHom`。
形式化陈述：realize_onBoundedFormula [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn 
M] {n : Nat} (ψ : L.BoundedFormula α n) {v : α -> M} {xs : Fin n -> M} : (φ.onBo
undedFormula ψ).Realize v xs ↔ ψ.Realize v xs
参数：φ : L ->ᴸ L'；ψ : L.BoundedFormula α n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Language.LHom.realize_onTerm`：realize_onTerm [L'.Structure M]
 (φ : L ->ᴸ L') [φ.IsExpansionOn M] (t : L.Term α) (v : α -> M) : (φ.onTerm t).r
ealize v = t.realize v
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.LHom.map_onRelation`：map_onRelation {M : Type*} [L.S
tructure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n} (R : L.Relations n) (x : Fi
n n -> M) : RelMap (ϕ.onRelat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem realize_onBoundedFormula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] {n : ℕ}
    (ψ : L.BoundedFormula α n) {v : α → M} {xs : Fin n → M} :
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
nonrec def Realize (φ : L.Formula α) (v : α → M) : Prop :=
  φ.Realize v default

variable {φ ψ : L.Formula α} {v : α → M}

@[simp]
/-
**FirstOrder.Language.Formula.realize_not** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Formula`。
形式化陈述：realize_not : φ.not.Realize v ↔ ¬φ.Realize v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_not : φ.not.Realize v ↔ ¬φ.Realize v :=
  Iff.rfl

@[simp]
/-
**FirstOrder.Language.Formula.realize_bot** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Formula`。
形式化陈述：realize_bot : (⊥ : L.Formula α).Realize v ↔ False
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_bot : (⊥ : L.Formula α).Realize v ↔ False :=
  Iff.rfl

@[simp]
/-
**FirstOrder.Language.Formula.realize_top** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Formula`。
形式化陈述：realize_top : (⊤ : L.Formula α).Realize v ↔ True
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_top`：realize_top : (⊤ : L.Bou
ndedFormula α l).Realize v xs ↔ True
-/
theorem realize_top : (⊤ : L.Formula α).Realize v ↔ True :=
  BoundedFormula.realize_top

@[simp]
/-
**FirstOrder.Language.Formula.realize_inf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Formula`。
形式化陈述：realize_inf : (φ ⊓ ψ).Realize v ↔ φ.Realize v ∧ ψ.Realize v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_inf`：realize_inf : (φ ⊓ ψ).Re
alize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs
-/
theorem realize_inf : (φ ⊓ ψ).Realize v ↔ φ.Realize v ∧ ψ.Realize v :=
  BoundedFormula.realize_inf

@[simp]
/-
**FirstOrder.Language.Formula.realize_imp** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Formula`。
形式化陈述：realize_imp : (φ.imp ψ).Realize v ↔ φ.Realize v -> ψ.Realize v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_imp`：realize_imp : (φ.imp ψ).
Realize v xs ↔ φ.Realize v xs -> ψ.Realize v xs
-/
theorem realize_imp : (φ.imp ψ).Realize v ↔ φ.Realize v → ψ.Realize v :=
  BoundedFormula.realize_imp

@[simp]
/-
**FirstOrder.Language.Formula.realize_rel** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Formula`。
形式化陈述：realize_rel {k : Nat} {R : L.Relations k} {ts : Fin k -> L.Term α} : (R.fo
rmula ts).Realize v ↔ RelMap R fun i => (ts i).realize v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_rel`：realize_rel {k : Nat} {R
 : L.Relations k} {ts : Fin k -> L.Term _} : (R.boundedFormula ts).Realize v xs 
↔ RelMap R fun i => (ts i).realize (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_rel {k : ℕ} {R : L.Relations k} {ts : Fin k → L.Term α} :
    (R.formula ts).Realize v ↔ RelMap R fun i => (ts i).realize v :=
  BoundedFormula.realize_rel.trans (by simp)

@[simp]
/-
**FirstOrder.Language.Formula.realize_rel** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Formula`。
形式化陈述：realize_rel {k : Nat} {R : L.Relations k} {ts : Fin k -> L.Term α} : (R.fo
rmula ts).Realize v ↔ RelMap R fun i => (ts i).realize v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_rel`：realize_rel {k : Nat} {R
 : L.Relations k} {ts : Fin k -> L.Term _} : (R.boundedFormula ts).Realize v xs 
↔ RelMap R fun i => (ts i).realize (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_rel₁ {R : L.Relations 1} {t : L.Term _} :
    (R.formula₁ t).Realize v ↔ RelMap R ![t.realize v] := by
  rw [Relations.formula₁, realize_rel, iff_eq_eq]
  refine congr rfl (funext fun _ => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]
/-
**FirstOrder.Language.Formula.realize_rel** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Formula`。
形式化陈述：realize_rel {k : Nat} {R : L.Relations k} {ts : Fin k -> L.Term α} : (R.fo
rmula ts).Realize v ↔ RelMap R fun i => (ts i).realize v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_rel`：realize_rel {k : Nat} {R
 : L.Relations k} {ts : Fin k -> L.Term _} : (R.boundedFormula ts).Realize v xs 
↔ RelMap R fun i => (ts i).realize (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
    (R.formula₂ t₁ t₂).Realize v ↔ RelMap R ![t₁.realize v, t₂.realize v] := by
  rw [Relations.formula₂, realize_rel, iff_eq_eq]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

@[simp]
/-
**FirstOrder.Language.Formula.realize_sup** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Formula`。
形式化陈述：realize_sup : (φ ⊔ ψ).Realize v ↔ φ.Realize v ∨ ψ.Realize v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_sup`：realize_sup : (φ ⊔ ψ).Re
alize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs
-/
theorem realize_sup : (φ ⊔ ψ).Realize v ↔ φ.Realize v ∨ ψ.Realize v :=
  BoundedFormula.realize_sup

@[simp]
/-
**FirstOrder.Language.Formula.realize_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Formula`。
形式化陈述：realize_iff : (φ.iff ψ).Realize v ↔ (φ.Realize v ↔ ψ.Realize v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_iff`：realize_iff : (φ.iff ψ).
Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs)
-/
theorem realize_iff : (φ.iff ψ).Realize v ↔ (φ.Realize v ↔ ψ.Realize v) :=
  BoundedFormula.realize_iff

@[simp]
/-
**FirstOrder.Language.Formula.realize_relabel** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Formula`。
形式化陈述：realize_relabel {φ : L.Formula α} {g : α -> β} {v : β -> M} : (φ.relabel g
).Realize v ↔ φ.Realize (v ∘ g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Formula.Realize.eq_1`：∀ {L : FirstOrder.Language} {M
 : Type w} [inst : L.Structure M] {α : Type u'} (φ : L.Formula α) (v : α → M),  
 φ.Realize v = FirstOrder.Lang…
· 使用定理 `FirstOrder.Language.Formula.relabel.eq_1`：∀ {L : FirstOrder.Language} {α
 : Type u'} {β : Type v'} (g : α → β),   FirstOrder.Language.Formula.relabel g =
 FirstOrder.Language.BoundedFo…
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_relabel`：realize_relabel {m n
 : Nat} {φ : L.BoundedFormula α n} {g : α -> β oplus (Fin m)} {v : β -> M} {xs :
 Fin (m + n) -> M} : (φ.relabel g).Reali…
· 使用引理 `iff_eq_eq`：iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b)
· 使用定理 `Fin.castAdd_zero`：∀ {n : ℕ}, Fin.castAdd 0 = Fin.cast ⋯
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem realize_relabel {φ : L.Formula α} {g : α → β} {v : β → M} :
    (φ.relabel g).Realize v ↔ φ.Realize (v ∘ g) := by
  rw [Realize, Realize, relabel, BoundedFormula.realize_relabel, iff_eq_eq, Fin.castAdd_zero]
  exact congr rfl (funext finZeroElim)
/-
**FirstOrder.Language.Formula.realize_relabel_sumInr** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Formula`。
形式化陈述：realize_relabel_sumInr (φ : L.Formula (Fin n)) {v : Empty -> M} {x : Fin n
 -> M} : (BoundedFormula.relabel Sum.inr φ).Realize v x ↔ φ.Realize x
参数：φ : L.Formula (Fin n)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_relabel`：realize_relabel {m n
 : Nat} {φ : L.BoundedFormula α n} {g : α -> β oplus (Fin m)} {v : β -> M} {xs :
 Fin (m + n) -> M} : (φ.relabel g).Reali…
· 使用定理 `FirstOrder.Language.Formula.Realize.eq_1`：∀ {L : FirstOrder.Language} {M
 : Type w} [inst : L.Structure M] {α : Type u'} (φ : L.Formula α) (v : α → M),  
 φ.Realize v = FirstOrder.Lang…
· 使用定理 `Sum.elim_comp_inr`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α
 → γ) (g : β → γ), Sum.elim f g ∘ Sum.inr = g
· 使用定理 `Fin.castAdd_zero`：∀ {n : ℕ}, Fin.castAdd 0 = Fin.cast ⋯
· 使用定理 `Fin.cast_refl`：∀ (n : ℕ) (h : n = n), Fin.cast h = id
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_relabel_sumInr (φ : L.Formula (Fin n)) {v : Empty → M} {x : Fin n → M} :
    (BoundedFormula.relabel Sum.inr φ).Realize v x ↔ φ.Realize x := by
  rw [BoundedFormula.realize_relabel, Formula.Realize, Sum.elim_comp_inr, Fin.castAdd_zero,
    cast_refl, Function.comp_id,
    Subsingleton.elim (x ∘ (natAdd n : Fin 0 → Fin n)) default]

@[simp]
/-
**FirstOrder.Language.Formula.realize_equal** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.Formula`。
形式化陈述：realize_equal {t₁ t₂ : L.Term α} {x : α -> M} : (t₁.equal t₂).Realize x ↔ 
t₁.realize x = t₂.realize x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_equal {t₁ t₂ : L.Term α} {x : α → M} :
    (t₁.equal t₂).Realize x ↔ t₁.realize x = t₂.realize x := by simp [Term.equal, Realize]

@[simp]
/-
**FirstOrder.Language.Formula.realize_graph** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.Formula`。
形式化陈述：realize_graph {f : L.Functions n} {x : Fin n -> M} {y : M} : (Formula.grap
h f).Realize (Fin.cons y x : _ -> M) ↔ funMap f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_graph {f : L.Functions n} {x : Fin n → M} {y : M} :
    (Formula.graph f).Realize (Fin.cons y x : _ → M) ↔ funMap f x = y := by
  simp only [Formula.graph, Term.realize, realize_equal, Fin.cons_zero, Fin.cons_succ]
  rw [eq_comm]
/-
**FirstOrder.Language.Formula.boundedFormula_realize_eq_realize** 是 Mathlib 中的一个
定理，位于命名空间 `FirstOrder.Language.Formula`。
形式化陈述：boundedFormula_realize_eq_realize (φ : L.Formula α) (x : α -> M) (y : Fin 
0 -> M) : BoundedFormula.Realize φ x y ↔ φ.Realize x
参数：φ : L.Formula α；x : α -> M；y : Fin 0 -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Formula.Realize.eq_1`：∀ {L : FirstOrder.Language} {M
 : Type w} [inst : L.Structure M] {α : Type u'} (φ : L.Formula α) (v : α → M),  
 φ.Realize v = FirstOrder.Lang…
· 使用定理 `iff_iff_eq`：∀ {a b : Prop}, (a ↔ b) ↔ a = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem boundedFormula_realize_eq_realize (φ : L.Formula α) (x : α → M) (y : Fin 0 → M) :
    BoundedFormula.Realize φ x y ↔ φ.Realize x := by
  rw [Formula.Realize, iff_iff_eq]
  congr
  ext i; exact Fin.elim0 i

end Formula

@[simp]
/-
**FirstOrder.Language.LHom.realize_onFormula** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.LHom`。
形式化陈述：∀ {L : FirstOrder.Language} {L' : FirstOrder.Language} {M : Type w} [inst 
: L.Structure M] {α : Type u'}   [inst_1 : L'.Structure M] (φ : L →ᴸ L') [φ.IsEx
pansionOn M] (ψ : L.Formula α) {v : α → M},   (φ.onFormula ψ).Realize v ↔ ψ.Real
ize v
参数：φ : L →ᴸ L'；ψ : L.Formula α；φ.onFormula ψ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.realize_onBoundedFormula`：realize_onBoundedForm
ula [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] {n : Nat} (ψ : L.Bounded
Formula α n) {v : α -> M} {xs : Fin n -…
-/
theorem LHom.realize_onFormula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (ψ : L.Formula α)
    {v : α → M} : (φ.onFormula ψ).Realize v ↔ ψ.Realize v :=
  φ.realize_onBoundedFormula ψ

@[simp]
/-
**FirstOrder.Language.LHom.setOfPred_realize_onFormula** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.LHom`。
形式化陈述：∀ {L : FirstOrder.Language} {L' : FirstOrder.Language} {M : Type w} [inst 
: L.Structure M] {α : Type u'}   [inst_1 : L'.Structure M] (φ : L →ᴸ L') [φ.IsEx
pansionOn M] (ψ : L.Formula α),   Set.ofPred (φ.onFormula ψ).Realize = Set.ofPre
d ψ.Realize
参数：φ : L →ᴸ L'；ψ : L.Formula α；φ.onFormula ψ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem LHom.setOfPred_realize_onFormula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (ψ : L.Formula α) :
    (Set.ofPred (φ.onFormula ψ).Realize : Set (α → M)) = Set.ofPred ψ.Realize := by
  ext
  simp

@[deprecated (since := "2026-07-09")]
alias LHom.setOf_realize_onFormula := LHom.setOfPred_realize_onFormula

variable (M)

/-- A sentence can be evaluated as true or false in a structure. -/
nonrec def Sentence.Realize (φ : L.Sentence) : Prop :=
  φ.Realize (default : _ → M)

-- input using \|= or \vDash, but not using \models
@[inherit_doc Sentence.Realize]
infixl:51 " ⊨ " => Sentence.Realize

namespace Sentence

variable {φ ψ : L.Sentence}

@[simp]
/-
**FirstOrder.Language.Sentence.realize_not** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Sentence`。
形式化陈述：realize_not : M ⊨ φ.not ↔ ¬M ⊨ φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_not : M ⊨ φ.not ↔ ¬M ⊨ φ :=
  Iff.rfl

@[simp]
/-
**FirstOrder.Language.Sentence.not_realize_bot** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.Sentence`。
形式化陈述：not_realize_bot : ¬(M ⊨ (⊥ : L.Sentence))
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_realize_bot : ¬(M ⊨ (⊥ : L.Sentence)) :=
  False.elim

@[simp]
/-
**FirstOrder.Language.Sentence.realize_top** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Sentence`。
形式化陈述：realize_top : M ⊨ (⊤ : L.Sentence)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem realize_top : M ⊨ (⊤ : L.Sentence) :=
  False.elim

@[simp]
/-
**FirstOrder.Language.Sentence.realize_inf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Sentence`。
形式化陈述：realize_inf : M ⊨ φ ⊓ ψ ↔ M ⊨ φ ∧ M ⊨ ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Formula.realize_inf`：realize_inf : (φ ⊓ ψ).Realize v
 ↔ φ.Realize v ∧ ψ.Realize v
-/
theorem realize_inf : M ⊨ φ ⊓ ψ ↔ M ⊨ φ ∧ M ⊨ ψ :=
  Formula.realize_inf

@[simp]
/-
**FirstOrder.Language.Sentence.realize_sup** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Sentence`。
形式化陈述：realize_sup : M ⊨ φ ⊔ ψ ↔ M ⊨ φ ∨ M ⊨ ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Formula.realize_sup`：realize_sup : (φ ⊔ ψ).Realize v
 ↔ φ.Realize v ∨ ψ.Realize v
-/
theorem realize_sup : M ⊨ φ ⊔ ψ ↔ M ⊨ φ ∨ M ⊨ ψ :=
  Formula.realize_sup

@[simp]
/-
**FirstOrder.Language.Sentence.realize_imp** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Sentence`。
形式化陈述：realize_imp : M ⊨ φ.imp ψ ↔ M ⊨ φ -> M ⊨ ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Formula.realize_imp`：realize_imp : (φ.imp ψ).Realize
 v ↔ φ.Realize v -> ψ.Realize v
-/
theorem realize_imp : M ⊨ φ.imp ψ ↔ M ⊨ φ → M ⊨ ψ :=
  Formula.realize_imp

@[simp]
/-
**FirstOrder.Language.Sentence.realize_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Sentence`。
形式化陈述：realize_iff : M ⊨ φ.iff ψ ↔ (M ⊨ φ ↔ M ⊨ ψ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Formula.realize_iff`：realize_iff : (φ.iff ψ).Realize
 v ↔ (φ.Realize v ↔ ψ.Realize v)
-/
theorem realize_iff : M ⊨ φ.iff ψ ↔ (M ⊨ φ ↔ M ⊨ ψ) :=
  Formula.realize_iff

end Sentence

namespace Formula

@[simp]
/-
**FirstOrder.Language.Formula.realize_equivSentence_symm_con** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.Formula`。
形式化陈述：realize_equivSentence_symm_con [L[[α]].Structure M] [(L.lhomWithConstants 
α).IsExpansionOn M] (φ : L[[α]].Sentence) : ((equivSentence.symm φ).Realize fun 
a => (L.con a : M)) ↔ φ.Realize M
参数：L.lhomWithConstants α；φ : L[[α]].Sentence。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `iff_iff_eq`：∀ {a b : Prop}, (a ↔ b) ↔ a = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_constantsVarsEquiv`：realize_c
onstantsVarsEquiv [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
 {n} {φ : L[[α]].BoundedFormula β n} {v : β -> M} {…
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
/-
**FirstOrder.Language.Formula.realize_equivSentence** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.Formula`。
形式化陈述：realize_equivSentence [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpa
nsionOn M] (φ : L.Formula α) : (equivSentence φ).Realize M ↔ φ.Realize fun a => 
(L.con a : M)
参数：L.lhomWithConstants α；φ : L.Formula α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Formula.realize_equivSentence_symm_con`：realize_equi
vSentence_symm_con [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M
] (φ : L[[α]].Sentence) : ((equivSentence.symm φ…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_equivSentence [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M]
    (φ : L.Formula α) : (equivSentence φ).Realize M ↔ φ.Realize fun a => (L.con a : M) := by
  rw [← realize_equivSentence_symm_con M (equivSentence φ), _root_.Equiv.symm_apply_apply]
/-
**FirstOrder.Language.Formula.realize_equivSentence_symm** 是 Mathlib 中的一个定理，位于命名
空间 `FirstOrder.Language.Formula`。
形式化陈述：realize_equivSentence_symm (φ : L[[α]].Sentence) (v : α -> M) : (equivSent
ence.symm φ).Realize v ↔ @Sentence.Realize _ M (@Language.withConstantsStructure
 L M _ α (constantsOn.structure v)) φ
参数：φ : L[[α]].Sentence；v : α -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Formula.realize_equivSentence_symm_con`：realize_equi
vSentence_symm_con [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M
] (φ : L[[α]].Sentence) : ((equivSentence.symm φ…
-/
theorem realize_equivSentence_symm (φ : L[[α]].Sentence) (v : α → M) :
    (equivSentence.symm φ).Realize v ↔
      @Sentence.Realize _ M (@Language.withConstantsStructure L M _ α (constantsOn.structure v))
        φ :=
  letI := constantsOn.structure v
  realize_equivSentence_symm_con M φ

end Formula

@[simp]
/-
**FirstOrder.Language.LHom.realize_onSentence** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.LHom`。
形式化陈述：∀ {L : FirstOrder.Language} {L' : FirstOrder.Language} (M : Type w) [inst 
: L.Structure M] [inst_1 : L'.Structure M]   (φ : L →ᴸ L') [φ.IsExpansionOn M] (
ψ : L.Sentence), M ⊨ φ.onSentence ψ ↔ M ⊨ ψ
参数：M : Type w；φ : L →ᴸ L'；ψ : L.Sentence。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.realize_onFormula`：∀ {L : FirstOrder.Language} 
{L' : FirstOrder.Language} {M : Type w} [inst : L.Structure M] {α : Type u'}   [
inst_1 : L'.Structure M] (φ : L …
-/
theorem LHom.realize_onSentence [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (ψ : L.Sentence) : M ⊨ φ.onSentence ψ ↔ M ⊨ ψ :=
  φ.realize_onFormula ψ

variable (L)

/-- The complete theory of a structure `M` is the set of all sentences `M` satisfies. -/
/-
**FirstOrder.Language.completeTheory** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：completeTheory : L.Theory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complete theory of a structure `M` is the set of all sentences `M` satisfies
.
-/
def completeTheory : L.Theory :=
  { φ | M ⊨ φ }

variable (N)

/-- Two structures are elementarily equivalent when they satisfy the same sentences. -/
/-
**FirstOrder.Language.ElementarilyEquivalent** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrd
er.Language`。
形式化陈述：ElementarilyEquivalent : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two structures are elementarily equivalent when they satisfy the same sentences.
-/
def ElementarilyEquivalent : Prop :=
  L.completeTheory M = L.completeTheory N

@[inherit_doc FirstOrder.Language.ElementarilyEquivalent]
scoped[FirstOrder]
  notation:25 A " ≅[" L "] " B:50 => FirstOrder.Language.ElementarilyEquivalent L A B

variable {L} {M} {N}

@[simp]
/-
**FirstOrder.Language.mem_completeTheory** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage`。
形式化陈述：mem_completeTheory {φ : Sentence L} : φ in L.completeTheory M ↔ M ⊨ φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_completeTheory {φ : Sentence L} : φ ∈ L.completeTheory M ↔ M ⊨ φ :=
  Iff.rfl
/-
**FirstOrder.Language.elementarilyEquivalent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language`。
形式化陈述：elementarilyEquivalent_iff : M ≅[L] N ↔ forall φ : L.Sentence, M ⊨ φ ↔ N ⊨
 φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem elementarilyEquivalent_iff : M ≅[L] N ↔ ∀ φ : L.Sentence, M ⊨ φ ↔ N ⊨ φ := by
  simp only [ElementarilyEquivalent, Set.ext_iff, completeTheory, Set.mem_ofPred_eq]

variable (M)

/-- A model of a theory is a structure in which every sentence is realized as true. -/
/-
**FirstOrder.Language.Theory.Model** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Langu
age.Theory`。
形式化陈述：{L : FirstOrder.Language} → (M : Type w) → [L.Structure M] → L.Theory → Pr
op
参数：M : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A model of a theory is a structure in which every sentence is realized as true.
-/
class Theory.Model (T : L.Theory) : Prop where
  realize_of_mem : ∀ φ ∈ T, M ⊨ φ

-- input using \|= or \vDash, but not using \models
@[inherit_doc Theory.Model]
infixl:51 " ⊨ " => Theory.Model

variable {M} (T : L.Theory)

@[simp default - 10]
/-
**FirstOrder.Language.Theory.model_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Theory`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} [inst : L.Structure M] (T : L.The
ory), M ⊨ T ↔ ∀ φ ∈ T, M ⊨ φ
参数：T : L.Theory。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.Model.realize_of_mem`：∀ {L : FirstOrder.Langu
age} {M : Type w} {inst : L.Structure M} {T : L.Theory} [self : M ⊨ T], ∀ φ ∈ T,
 M ⊨ φ
-/
theorem Theory.model_iff : M ⊨ T ↔ ∀ φ ∈ T, M ⊨ φ :=
  ⟨fun h => h.realize_of_mem, fun h => ⟨h⟩⟩
/-
**FirstOrder.Language.Theory.realize_sentence_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Theory`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} [inst : L.Structure M] (T : L.The
ory) [M ⊨ T] {φ : L.Sentence}, φ ∈ T → M ⊨ φ
参数：T : L.Theory。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.Model.realize_of_mem`：∀ {L : FirstOrder.Langu
age} {M : Type w} {inst : L.Structure M} {T : L.Theory} [self : M ⊨ T], ∀ φ ∈ T,
 M ⊨ φ
-/
theorem Theory.realize_sentence_of_mem [M ⊨ T] {φ : L.Sentence} (h : φ ∈ T) : M ⊨ φ :=
  Theory.Model.realize_of_mem φ h

@[simp]
/-
**FirstOrder.Language.LHom.onTheory_model** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.LHom`。
形式化陈述：∀ {L : FirstOrder.Language} {L' : FirstOrder.Language} {M : Type w} [inst 
: L.Structure M] [inst_1 : L'.Structure M]   (φ : L →ᴸ L') [φ.IsExpansionOn M] (
T : L.Theory), M ⊨ φ.onTheory T ↔ M ⊨ T
参数：φ : L →ᴸ L'；T : L.Theory。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem LHom.onTheory_model [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (T : L.Theory) :
    M ⊨ φ.onTheory T ↔ M ⊨ T := by simp [Theory.model_iff, LHom.onTheory]

variable {T}
/-
**FirstOrder.Language.model_empty** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language
`。
形式化陈述：model_empty : M ⊨ (∅ : L.Theory)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
instance model_empty : M ⊨ (∅ : L.Theory) :=
  ⟨fun φ hφ => (Set.notMem_empty φ hφ).elim⟩

namespace Theory

/-
**FirstOrder.Language.Theory.Model.mono** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.La
nguage.Theory.Model`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} [inst : L.Structure M] {T T' : L.
Theory}, M ⊨ T' → T ⊆ T' → M ⊨ T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.realize_sentence_of_mem`：∀ {L : FirstOrder.La
nguage} {M : Type w} [inst : L.Structure M] (T : L.Theory) [M ⊨ T] {φ : L.Senten
ce}, φ ∈ T → M ⊨ φ
-/
theorem Model.mono {T' : L.Theory} (_h : M ⊨ T') (hs : T ⊆ T') : M ⊨ T :=
  ⟨fun _φ hφ => T'.realize_sentence_of_mem (hs hφ)⟩
/-
**FirstOrder.Language.Theory.Model.union** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage.Theory.Model`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} [inst : L.Structure M] {T T' : L.
Theory}, M ⊨ T → M ⊨ T' → M ⊨ T ∪ T'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
theorem Model.union {T' : L.Theory} (h : M ⊨ T) (h' : M ⊨ T') : M ⊨ T ∪ T' := by
  simp only [model_iff, Set.mem_union] at *
  exact fun φ hφ => hφ.elim (h _) (h' _)

@[simp]
/-
**FirstOrder.Language.Theory.model_union_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Theory`。
形式化陈述：model_union_iff {T' : L.Theory} : M ⊨ T union T' ↔ M ⊨ T ∧ M ⊨ T'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.Model.mono`：∀ {L : FirstOrder.Language} {M : 
Type w} [inst : L.Structure M] {T T' : L.Theory}, M ⊨ T' → T ⊆ T' → M ⊨ T
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `FirstOrder.Language.Theory.Model.union`：∀ {L : FirstOrder.Language} {M :
 Type w} [inst : L.Structure M] {T T' : L.Theory}, M ⊨ T → M ⊨ T' → M ⊨ T ∪ T'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem model_union_iff {T' : L.Theory} : M ⊨ T ∪ T' ↔ M ⊨ T ∧ M ⊨ T' :=
  ⟨fun h => ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩, fun h =>
    h.1.union h.2⟩

@[simp]
/-
**FirstOrder.Language.Theory.model_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Theory`。
形式化陈述：model_singleton_iff {φ : L.Sentence} : M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem model_singleton_iff {φ : L.Sentence} : M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ := by simp
/-
**FirstOrder.Language.Theory.model_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Theory`。
形式化陈述：model_insert_iff {φ : L.Sentence} : M ⊨ insert φ T ↔ M ⊨ φ ∧ M ⊨ T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `FirstOrder.Language.Theory.model_union_iff`：model_union_iff {T' : L.Theo
ry} : M ⊨ T union T' ↔ M ⊨ T ∧ M ⊨ T'
· 使用定理 `FirstOrder.Language.Theory.model_singleton_iff`：model_singleton_iff {φ :
 L.Sentence} : M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem model_insert_iff {φ : L.Sentence} : M ⊨ insert φ T ↔ M ⊨ φ ∧ M ⊨ T := by
  rw [Set.insert_eq, model_union_iff, model_singleton_iff]
/-
**FirstOrder.Language.Theory.model_iff_subset_completeTheory** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.Theory`。
形式化陈述：model_iff_subset_completeTheory : M ⊨ T ↔ T subseteq L.completeTheory M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.model_iff`：∀ {L : FirstOrder.Language} {M : T
ype w} [inst : L.Structure M] (T : L.Theory), M ⊨ T ↔ ∀ φ ∈ T, M ⊨ φ
-/
theorem model_iff_subset_completeTheory : M ⊨ T ↔ T ⊆ L.completeTheory M :=
  T.model_iff
/-
**FirstOrder.Language.Theory.completeTheory.subset** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Theory.completeTheory`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} [inst : L.Structure M] {T : L.The
ory} [MT : M ⊨ T], T ⊆ L.completeTheory M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Theory.model_iff_subset_completeTheory`：model_iff_su
bset_completeTheory : M ⊨ T ↔ T subseteq L.completeTheory M
-/
theorem completeTheory.subset [MT : M ⊨ T] : T ⊆ L.completeTheory M :=
  model_iff_subset_completeTheory.1 MT

end Theory

/-
**FirstOrder.Language.model_completeTheory** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder
.Language`。
形式化陈述：model_completeTheory : M ⊨ L.completeTheory M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Theory.model_iff_subset_completeTheory`：model_iff_su
bset_completeTheory : M ⊨ T ↔ T subseteq L.completeTheory M
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
instance model_completeTheory : M ⊨ L.completeTheory M :=
  Theory.model_iff_subset_completeTheory.2 subset_rfl

variable (M N)
/-
**FirstOrder.Language.realize_iff_of_model_completeTheory** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language`。
形式化陈述：realize_iff_of_model_completeTheory [N ⊨ L.completeTheory M] (φ : L.Senten
ce) : N ⊨ φ ↔ M ⊨ φ
参数：φ : L.Sentence。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Sentence.realize_not`：realize_not : M ⊨ φ.not ↔ ¬M ⊨
 φ
· 使用定理 `FirstOrder.Language.Theory.realize_sentence_of_mem`：∀ {L : FirstOrder.La
nguage} {M : Type w} [inst : L.Structure M] (T : L.Theory) [M ⊨ T] {φ : L.Senten
ce}, φ ∈ T → M ⊨ φ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.mem_completeTheory`：mem_completeTheory {φ : Sentence
 L} : φ in L.completeTheory M ↔ M ⊨ φ
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
/-
**FirstOrder.Language.BoundedFormula.realize_alls** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.BoundedFormula`。
形式化陈述：realize_alls {φ : L.BoundedFormula α n} {v : α -> M} : φ.alls.Realize v ↔ 
forall xs : Fin n -> M, φ.Realize v xs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Unique.forall_iff`：forall_iff {p : α -> Prop} : (forall a, p a) ↔ p defa
ult
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.snoc_init_self`：snoc_init_self : snoc (init q) (q (last n)) = q
-/
theorem realize_alls {φ : L.BoundedFormula α n} {v : α → M} :
    φ.alls.Realize v ↔ ∀ xs : Fin n → M, φ.Realize v xs := by
  induction n with
  | zero => exact Unique.forall_iff.symm
  | succ n ih =>
    simp only [alls, ih, Realize]
    exact ⟨fun h xs => Fin.snoc_init_self xs ▸ h _ _, fun h xs x => h (Fin.snoc xs x)⟩

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_exs** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.BoundedFormula`。
形式化陈述：realize_exs {φ : L.BoundedFormula α n} {v : α -> M} : φ.exs.Realize v ↔ ex
ists xs : Fin n -> M, φ.Realize v xs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Unique.exists_iff`：exists_iff {p : α -> Prop} : Exists p ↔ p default
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.snoc_init_self`：snoc_init_self : snoc (init q) (q (last n)) = q
-/
theorem realize_exs {φ : L.BoundedFormula α n} {v : α → M} :
    φ.exs.Realize v ↔ ∃ xs : Fin n → M, φ.Realize v xs := by
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
/-
**FirstOrder.Language.BoundedFormula._root_.FirstOrder.Language.Formula.realize_
iAlls** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.BoundedFormula`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.FirstOrder.Language.Formula.realize_iAlls
    [Finite β] {φ : L.Formula (α ⊕ β)} {v : α → M} : (φ.iAlls β).Realize v ↔
      ∀ (i : β → M), φ.Realize (fun a => Sum.elim v i a) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  rw [Formula.iAlls]
  simp only [Nat.add_zero, realize_alls, realize_relabel, Function.comp_def,
    castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.forall_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,
      fun _ => by simp [Function.comp_def],
      fun _ => by simp [Function.comp_def]⟩
  · intro x
    rw [Formula.Realize, iff_iff_eq]
    congr
    funext i
    exact i.elim0

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_iAlls** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.BoundedFormula`。
形式化陈述：realize_iAlls [Finite β] {φ : L.Formula (α oplus β)} {v : α -> M} {v' : Fi
n 0 -> M} : BoundedFormula.Realize (φ.iAlls β) v v' ↔ forall (i : β -> M), φ.Rea
lize (fun a => Sum.elim v i a)
参数：α oplus β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Formula.realize_iAlls`：∀ {L : FirstOrder.Language} {
M : Type w} [inst : L.Structure M] {α : Type u'} {β : Type v'} [inst_1 : Finite 
β]   {φ : L.Formula (α ⊕ β)} {v…
· 使用定理 `iff_iff_eq`：∀ {a b : Prop}, (a ↔ b) ↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem realize_iAlls [Finite β] {φ : L.Formula (α ⊕ β)} {v : α → M} {v' : Fin 0 → M} :
    BoundedFormula.Realize (φ.iAlls β) v v' ↔
      ∀ (i : β → M), φ.Realize (fun a => Sum.elim v i a) := by
  rw [← Formula.realize_iAlls, iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]
/-
**FirstOrder.Language.BoundedFormula._root_.FirstOrder.Language.Formula.realize_
iExs** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.BoundedFormula`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.FirstOrder.Language.Formula.realize_iExs
    [Finite γ] {φ : L.Formula (α ⊕ γ)} {v : α → M} : (φ.iExs γ).Realize v ↔
      ∃ (i : γ → M), φ.Realize (Sum.elim v i) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  rw [Formula.iExs]
  simp only [Nat.add_zero, realize_exs, realize_relabel, Function.comp_def,
    castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.exists_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,
      fun _ => by simp [Function.comp_def],
      fun _ => by simp [Function.comp_def]⟩
  · intro x
    rw [Formula.Realize, iff_iff_eq]
    congr
    funext i
    exact i.elim0

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_iExs** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.BoundedFormula`。
形式化陈述：realize_iExs [Finite γ] {φ : L.Formula (α oplus γ)} {v : α -> M} {v' : Fin
 0 -> M} : BoundedFormula.Realize (φ.iExs γ) v v' ↔ exists (i : γ -> M), φ.Reali
ze (Sum.elim v i)
参数：α oplus γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Formula.realize_iExs`：∀ {L : FirstOrder.Language} {M
 : Type w} [inst : L.Structure M] {α : Type u'} {γ : Type u_3} [inst_1 : Finite 
γ]   {φ : L.Formula (α ⊕ γ)} {…
· 使用定理 `iff_iff_eq`：∀ {a b : Prop}, (a ↔ b) ↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem realize_iExs [Finite γ] {φ : L.Formula (α ⊕ γ)} {v : α → M} {v' : Fin 0 → M} :
    BoundedFormula.Realize (φ.iExs γ) v v' ↔
      ∃ (i : γ → M), φ.Realize (Sum.elim v i) := by
  rw [← Formula.realize_iExs, iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_toFormula** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_toFormula (φ : L.BoundedFormula α n) (v : α oplus (Fin n) -> M) : 
φ.toFormula.Realize v ↔ φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr)
参数：φ : L.BoundedFormula α n；v : α oplus (Fin n) -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sum.elim_comp_inl_inr`：∀ {α : Type u_1} {β : Type u_2} {γ : Sort u_3} (f
 : α ⊕ β → γ), Sum.elim (f ∘ Sum.inl) (f ∘ Sum.inr) = f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.BoundedFormula.toFormula.eq_4`：∀ {L : FirstOrder.Lan
guage} {α : Type u'} (x : ℕ) (f₁ f₂ : L.BoundedFormula α x),   (f₁.imp f₂).toFor
mula = FirstOrder.Language.BoundedFormu…
· 使用定理 `FirstOrder.Language.Formula.Realize.eq_1`：∀ {L : FirstOrder.Language} {M
 : Type w} [inst : L.Structure M] {α : Type u'} (φ : L.Formula α) (v : α → M),  
 φ.Realize v = FirstOrder.Lang…
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_imp`：realize_imp : (φ.imp ψ).
Realize v xs ↔ φ.Realize v xs -> ψ.Realize v xs
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `FirstOrder.Language.BoundedFormula.toFormula.eq_5`：∀ {L : FirstOrder.Lan
guage} {α : Type u'} (x : ℕ) (f : L.BoundedFormula α (x + 1)),   f.all.toFormula
 =     (FirstOrder.Language.BoundedForm…
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_all`：realize_all : (all θ).Re
alize v xs ↔ forall a : M, θ.Realize v (Fin.snoc xs a)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_relabel`：realize_relabel {m n
 : Nat} {φ : L.BoundedFormula α n} {g : α -> β oplus (Fin m)} {v : β -> M} {xs :
 Fin (m + n) -> M} : (φ.relabel g).Reali…
· 使用定理 `iff_iff_eq`：∀ {a b : Prop}, (a ↔ b) ↔ a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `finSumFinEquiv_symm_last`：finSumFinEquiv_symm_last : finSumFinEquiv.symm
 (Fin.last n) = Sum.inr 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `finSumFinEquiv_symm_apply_castAdd`：finSumFinEquiv_symm_apply_castAdd (x 
: Fin m) : finSumFinEquiv.symm (Fin.castAdd n x) = Sum.inl x
· 使用定理 `Fin.castSucc.eq_1`：∀ {n : ℕ}, Fin.castSucc = Fin.castAdd 1
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem realize_toFormula (φ : L.BoundedFormula α n) (v : α ⊕ (Fin n) → M) :
    φ.toFormula.Realize v ↔ φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr) := by
  induction φ with
  | falsum => rfl
  | equal => simp [BoundedFormula.Realize]
  | rel => simp [BoundedFormula.Realize]
  | imp _ _ ih1 ih2 =>
    rw [toFormula, Formula.Realize, realize_imp, ← Formula.Realize, ih1, ← Formula.Realize, ih2,
      realize_imp]
  | all _ ih3 =>
    rw [toFormula, Formula.Realize, realize_all, realize_all]
    refine forall_congr' fun a => ?_
    have h := ih3 (Sum.elim (v ∘ Sum.inl) (snoc (v ∘ Sum.inr) a))
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
    rw [← h, realize_relabel, Formula.Realize, iff_iff_eq]
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
/-
**FirstOrder.Language.BoundedFormula.realize_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.BoundedFormula`。
形式化陈述：realize_iSup [Finite β] {f : β -> L.BoundedFormula α n} {v : α -> M} {v' :
 Fin n -> M} : (iSup f).Realize v v' ↔ exists b, (f b).Realize v v'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_iSup [Finite β] {f : β → L.BoundedFormula α n}
    {v : α → M} {v' : Fin n → M} :
    (iSup f).Realize v v' ↔ ∃ b, (f b).Realize v v' := by
  simp only [iSup, realize_foldr_sup, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    exists_exists_eq_and]

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.BoundedFormula`。
形式化陈述：realize_iInf [Finite β] {f : β -> L.BoundedFormula α n} {v : α -> M} {v' :
 Fin n -> M} : (iInf f).Realize v v' ↔ forall b, (f b).Realize v v'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_iInf [Finite β] {f : β → L.BoundedFormula α n}
    {v : α → M} {v' : Fin n → M} :
    (iInf f).Realize v v' ↔ ∀ b, (f b).Realize v v' := by
  simp only [iInf, realize_foldr_inf, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]

@[simp]
/-
**FirstOrder.Language.BoundedFormula._root_.FirstOrder.Language.Formula.realize_
iSup** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.BoundedFormula`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.FirstOrder.Language.Formula.realize_iSup [Finite β] {f : β → L.Formula α}
    {v : α → M} : (Formula.iSup f).Realize v ↔ ∃ b, (f b).Realize v := by
  simp [Formula.iSup, Formula.Realize]

@[simp]
/-
**FirstOrder.Language.BoundedFormula._root_.FirstOrder.Language.Formula.realize_
iInf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.BoundedFormula`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.FirstOrder.Language.Formula.realize_iInf [Finite β] {f : β → L.Formula α}
    {v : α → M} : (Formula.iInf f).Realize v ↔ ∀ b, (f b).Realize v := by
  simp [Formula.iInf, Formula.Realize]
/-
**FirstOrder.Language.BoundedFormula._root_.FirstOrder.Language.Formula.realize_
iExsUnique** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.BoundedFormula`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.FirstOrder.Language.Formula.realize_iExsUnique [Finite γ]
    {φ : L.Formula (α ⊕ γ)} {v : α → M} : (φ.iExsUnique γ).Realize v ↔
      ∃! (i : γ → M), φ.Realize (Sum.elim v i) := by
  rw [Formula.iExsUnique, ExistsUnique]
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_relabel]
  simp only [Formula.Realize, Function.comp_def, Term.equal, Term.relabel, realize_iInf,
    realize_bdEqual, Term.realize_var, Sum.elim_inl, Sum.elim_inr, funext_iff]
  refine exists_congr (fun i => and_congr_right' (forall_congr' (fun y => ?_)))
  rw [iff_iff_eq]; congr with x
  cases x <;> simp

@[simp]
/-
**FirstOrder.Language.BoundedFormula.realize_iExsUnique** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.BoundedFormula`。
形式化陈述：realize_iExsUnique [Finite γ] {φ : L.Formula (α oplus γ)} {v : α -> M} {v'
 : Fin 0 -> M} : BoundedFormula.Realize (φ.iExsUnique γ) v v' ↔ exists! (i : γ -
> M), φ.Realize (Sum.elim v i)
参数：α oplus γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Formula.realize_iExsUnique`：∀ {L : FirstOrder.Langua
ge} {M : Type w} [inst : L.Structure M] {α : Type u'} {γ : Type u_3} [inst_1 : F
inite γ]   {φ : L.Formula (α ⊕ γ)} {…
· 使用定理 `iff_iff_eq`：∀ {a b : Prop}, (a ↔ b) ↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem realize_iExsUnique [Finite γ] {φ : L.Formula (α ⊕ γ)} {v : α → M} {v' : Fin 0 → M} :
    BoundedFormula.Realize (φ.iExsUnique γ) v v' ↔
      ∃! (i : γ → M), φ.Realize (Sum.elim v i) := by
  rw [← Formula.realize_iExsUnique, iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

end BoundedFormula

namespace Formula

@[simp]
/-
**FirstOrder.Language.Formula.realize_exClosure** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Formula`。
形式化陈述：realize_exClosure [DecidableEq α] (φ : L.Formula α) : φ.exClosure.Realize 
M ↔ exists v : φ.freeVarFinset -> M, Formula.Realize (φ.restrictFreeVar id) v
参数：φ : L.Formula α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_exClosure [DecidableEq α] (φ : L.Formula α) :
    φ.exClosure.Realize M ↔
      ∃ v : φ.freeVarFinset → M, Formula.Realize (φ.restrictFreeVar id) v := by
  simp [Sentence.Realize, Formula.exClosure, Formula.realize_iExs]
/-
**FirstOrder.Language.Formula.realize_exClosure_of_realize_equivSentence** 是 Mat
hlib 中的一个定理，位于命名空间 `FirstOrder.Language.Formula`。
形式化陈述：realize_exClosure_of_realize_equivSentence [DecidableEq α] [L[[α]].Structu
re M] [(L.lhomWithConstants α).IsExpansionOn M] {φ : L.Formula α} (h : (Formula.
equivSentence φ).Realize M) : φ.exClosure.Realize M
参数：L.lhomWithConstants α；h : (Formula.equivSentence φ).Realize M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Formula.realize_exClosure`：realize_exClosure [Decida
bleEq α] (φ : L.Formula α) : φ.exClosure.Realize M ↔ exists v : φ.freeVarFinset 
-> M, Formula.Realize (φ.restrictFr…
-/
theorem realize_exClosure_of_realize_equivSentence [DecidableEq α] [L[[α]].Structure M]
    [(L.lhomWithConstants α).IsExpansionOn M] {φ : L.Formula α}
    (h : (Formula.equivSentence φ).Realize M) : φ.exClosure.Realize M := by
  rw [Formula.realize_exClosure]
  exists fun a => (L.con (a : α) : M)
  simpa [Formula.Realize, BoundedFormula.realize_restrictFreeVar] using h
/-
**FirstOrder.Language.Formula.exists_realize_equivSentence_iff_realize_exClosure
** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.Formula`。
形式化陈述：exists_realize_equivSentence_iff_realize_exClosure [DecidableEq α] [Nonemp
ty M] {φ : L.Formula α} : (exists v : α -> M, letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Formula.realize_exClosure`：realize_exClosure [Decida
bleEq α] (φ : L.Formula α) : φ.exClosure.Realize M ↔ exists v : φ.freeVarFinset 
-> M, Formula.Realize (φ.restrictFr…
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_restrictFreeVar`：realize_rest
rictFreeVar [DecidableEq α] {n : Nat} {φ : L.BoundedFormula α n} {f : φ.freeVarF
inset -> β} {v : β -> M} {xs : Fin n -> M} (v' :…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `FirstOrder.Language.Formula.realize_equivSentence_symm`：realize_equivSen
tence_symm (φ : L[[α]].Sentence) (v : α -> M) : (equivSentence.symm φ).Realize v
 ↔ @Sentence.Realize _ M (@Language.withCons…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem exists_realize_equivSentence_iff_realize_exClosure
    [DecidableEq α] [Nonempty M] {φ : L.Formula α} :
    (∃ v : α → M,
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
    let v' := fun a => if hmem : a ∈ φ.freeVarFinset
      then v ⟨a, hmem⟩ else Classical.choice inferInstance
    exists v'
    refine (Formula.realize_equivSentence_symm M (Formula.equivSentence φ) v').mp ?_
    simpa [Equiv.symm_apply_apply, Formula.Realize] using
      (BoundedFormula.realize_restrictFreeVar v' (by grind)).1 hv

end Formula

namespace StrongHomClass

variable {F : Type*} [EquivLike F M N] [StrongHomClass L F M N] (g : F)

@[simp]
/-
**FirstOrder.Language.StrongHomClass.realize_boundedFormula** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Language.StrongHomClass`。
形式化陈述：realize_boundedFormula (φ : L.BoundedFormula α n) {v : α -> M} {xs : Fin n
 -> M} : φ.Realize (g ∘ v) (g ∘ xs) ↔ φ.Realize v xs
参数：φ : L.BoundedFormula α n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Language.HomClass.realize_term`：∀ {L : FirstOrder.Language} {
M : Type w} {N : Type u_1} [inst : L.Structure M] [inst_1 : L.Structure N] {α : 
Type u'}   {F : Type u_4} [inst…
· 使用定理 `FirstOrder.Language.StrongHomClass.homClass`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] {F :
 Type u_3}   [inst_2 : FunLike F …
· 使用定理 `EmbeddingLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : F) {x y : α} : f x =
 f y ↔ x = y
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.StrongHomClass.map_rel`：∀ {L : outParam FirstOrder.L
anguage} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {i
nst : FunLike F M N} {inst_1 : L…
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_4`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (f₁ f₂ : L.BoundedFo…
· 使用定理 `FirstOrder.Language.BoundedFormula.Realize.eq_5`：∀ {L : FirstOrder.Langu
age} {M : Type w} [inst : L.Structure M] {α : Type u'} (x : ℕ) (x_1 : α → M) (x_
2 : Fin x → M)   (f : L.BoundedFormul…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.comp_snoc`：comp_snoc {α : Sort*} {β : Sort*} (g : α -> β) (q : Fin n
 -> α) (y : α) : g ∘ snoc q y = snoc (g ∘ q) (g y)
· 使用定理 `EquivLike.apply_inv_apply`：apply_inv_apply (e : E) (b : β) : e (inv e b)
 = b
-/
theorem realize_boundedFormula (φ : L.BoundedFormula α n) {v : α → M}
    {xs : Fin n → M} : φ.Realize (g ∘ v) (g ∘ xs) ↔ φ.Realize v xs := by
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
    rw [BoundedFormula.Realize, BoundedFormula.Realize]
    constructor
    · intro h a
      have h' := h (g a)
      rw [← Fin.comp_snoc, ih3] at h'
      exact h'
    · intro h a
      have h' := h (EquivLike.inv g a)
      rw [← ih3, Fin.comp_snoc, EquivLike.apply_inv_apply g] at h'
      exact h'

@[simp]
/-
**FirstOrder.Language.StrongHomClass.realize_formula** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.StrongHomClass`。
形式化陈述：realize_formula (φ : L.Formula α) {v : α -> M} : φ.Realize (g ∘ v) ↔ φ.Rea
lize v
参数：φ : L.Formula α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Formula.Realize.eq_1`：∀ {L : FirstOrder.Language} {M
 : Type w} [inst : L.Structure M] {α : Type u'} (φ : L.Formula α) (v : α → M),  
 φ.Realize v = FirstOrder.Lang…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.StrongHomClass.realize_boundedFormula`：realize_bound
edFormula (φ : L.BoundedFormula α n) {v : α -> M} {xs : Fin n -> M} : φ.Realize 
(g ∘ v) (g ∘ xs) ↔ φ.Realize v xs
· 使用引理 `iff_eq_eq`：iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b)
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
-/
theorem realize_formula (φ : L.Formula α) {v : α → M} :
    φ.Realize (g ∘ v) ↔ φ.Realize v := by
  rw [Formula.Realize, Formula.Realize, ← realize_boundedFormula g φ, iff_eq_eq,
    Unique.eq_default (g ∘ default)]

include g
/-
**FirstOrder.Language.StrongHomClass.realize_sentence** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.StrongHomClass`。
形式化陈述：realize_sentence (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ
参数：φ : L.Sentence。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Sentence.Realize.eq_1`：∀ {L : FirstOrder.Language} (
M : Type w) [inst : L.Structure M] (φ : L.Sentence),   M ⊨ φ = FirstOrder.Langua
ge.Formula.Realize φ default
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.StrongHomClass.realize_formula`：realize_formula (φ :
 L.Formula α) {v : α -> M} : φ.Realize (g ∘ v) ↔ φ.Realize v
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_sentence (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  rw [Sentence.Realize, Sentence.Realize, ← realize_formula g,
    Unique.eq_default (g ∘ default)]
/-
**FirstOrder.Language.StrongHomClass.theory_model** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.StrongHomClass`。
形式化陈述：theory_model [M ⊨ T] : N ⊨ T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.StrongHomClass.realize_sentence`：realize_sentence (φ
 : L.Sentence) : M ⊨ φ ↔ N ⊨ φ
· 使用定理 `FirstOrder.Language.Theory.realize_sentence_of_mem`：∀ {L : FirstOrder.La
nguage} {M : Type w} [inst : L.Structure M] (T : L.Theory) [M ⊨ T] {φ : L.Senten
ce}, φ ∈ T → M ⊨ φ
-/
theorem theory_model [M ⊨ T] : N ⊨ T :=
  ⟨fun φ hφ => (realize_sentence g φ).1 (Theory.realize_sentence_of_mem T hφ)⟩
/-
**FirstOrder.Language.StrongHomClass.elementarilyEquivalent** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Language.StrongHomClass`。
形式化陈述：elementarilyEquivalent : M ≅[L] N
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.elementarilyEquivalent_iff`：elementarilyEquivalent_i
ff : M ≅[L] N ↔ forall φ : L.Sentence, M ⊨ φ ↔ N ⊨ φ
· 使用定理 `FirstOrder.Language.StrongHomClass.realize_sentence`：realize_sentence (φ
 : L.Sentence) : M ⊨ φ ↔ N ⊨ φ
-/
theorem elementarilyEquivalent : M ≅[L] N :=
  elementarilyEquivalent_iff.2 (realize_sentence g)

end StrongHomClass

namespace Relations

open BoundedFormula

variable {r : L.Relations 2}

@[simp]
/-
**FirstOrder.Language.Relations.realize_reflexive** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Relations`。
形式化陈述：realize_reflexive : M ⊨ r.reflexive ↔ Std.Refl fun x y : M => RelMap r ![x
, y]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `refl_def`：refl_def : Std.Refl r ↔ forall ⦃a⦄, r a a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_rel₂`：realize_rel₂ {R : L.Rel
ations 2} {t₁ t₂ : L.Term _} : (R.boundedFormula₂ t₁ t₂).Realize v xs ↔ RelMap R
 ![t₁.realize (Sum.elim v xs), t₂.rea…
-/
theorem realize_reflexive : M ⊨ r.reflexive ↔ Std.Refl fun x y : M => RelMap r ![x, y] := by
  rw [refl_def]
  exact forall_congr' fun _ ↦ realize_rel₂

@[simp]
/-
**FirstOrder.Language.Relations.realize_irreflexive** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.Relations`。
形式化陈述：realize_irreflexive : M ⊨ r.irreflexive ↔ Std.Irrefl fun x y : M => RelMap
 r ![x, y]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `irrefl_def`：irrefl_def : Std.Irrefl r ↔ forall ⦃a⦄, ¬r a a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_rel₂`：realize_rel₂ {R : L.Rel
ations 2} {t₁ t₂ : L.Term _} : (R.boundedFormula₂ t₁ t₂).Realize v xs ↔ RelMap R
 ![t₁.realize (Sum.elim v xs), t₂.rea…
-/
theorem realize_irreflexive : M ⊨ r.irreflexive ↔ Std.Irrefl fun x y : M => RelMap r ![x, y] := by
  rw [irrefl_def]
  exact forall_congr' fun _ ↦ not_congr realize_rel₂

@[simp]
/-
**FirstOrder.Language.Relations.realize_symmetric** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Relations`。
形式化陈述：realize_symmetric : M ⊨ r.symmetric ↔ Std.Symm fun x y : M => RelMap r ![x
, y]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `symm_def`：symm_def : Std.Symm r ↔ forall ⦃a b⦄, r a b -> r b a
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `imp_congr`：∀ {a b c d : Prop}, (a ↔ c) → (b ↔ d) → (a → b ↔ c → d)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_rel₂`：realize_rel₂ {R : L.Rel
ations 2} {t₁ t₂ : L.Term _} : (R.boundedFormula₂ t₁ t₂).Realize v xs ↔ RelMap R
 ![t₁.realize (Sum.elim v xs), t₂.rea…
-/
theorem realize_symmetric : M ⊨ r.symmetric ↔ Std.Symm fun x y : M => RelMap r ![x, y] := by
  rw [symm_def]
  exact forall₂_congr fun _ _ ↦ imp_congr realize_rel₂ realize_rel₂

@[simp]
/-
**FirstOrder.Language.Relations.realize_antisymmetric** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.Relations`。
形式化陈述：realize_antisymmetric : M ⊨ r.antisymmetric ↔ Std.Antisymm fun x y : M => 
RelMap r ![x, y]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `antisymm_def`：antisymm_def : Std.Antisymm r ↔ forall ⦃a b⦄, r a b -> r b
 a -> a = b
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `imp_congr`：∀ {a b c d : Prop}, (a ↔ c) → (b ↔ d) → (a → b ↔ c → d)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_rel₂`：realize_rel₂ {R : L.Rel
ations 2} {t₁ t₂ : L.Term _} : (R.boundedFormula₂ t₁ t₂).Realize v xs ↔ RelMap R
 ![t₁.realize (Sum.elim v xs), t₂.rea…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem realize_antisymmetric :
    M ⊨ r.antisymmetric ↔ Std.Antisymm fun x y : M => RelMap r ![x, y] := by
  rw [antisymm_def]
  exact forall₂_congr fun _ _ ↦ imp_congr realize_rel₂ <| imp_congr realize_rel₂ .rfl

@[simp]
/-
**FirstOrder.Language.Relations.realize_transitive** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Relations`。
形式化陈述：realize_transitive : M ⊨ r.transitive ↔ IsTrans M fun x y => RelMap r ![x,
 y]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isTrans_def`：isTrans_def {α : Sort*} {r : α -> α -> Prop} : IsTrans α r 
↔ forall ⦃a b c⦄, r a b -> r b c -> r a c
· 使用定理 `forall₃_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {p q : (a : α) → (b : β a) → γ a b → Prop},   (∀ (a : α) (b : β a) (c 
: γ…
· 使用定理 `imp_congr`：∀ {a b c d : Prop}, (a ↔ c) → (b ↔ d) → (a → b ↔ c → d)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_rel₂`：realize_rel₂ {R : L.Rel
ations 2} {t₁ t₂ : L.Term _} : (R.boundedFormula₂ t₁ t₂).Realize v xs ↔ RelMap R
 ![t₁.realize (Sum.elim v xs), t₂.rea…
-/
theorem realize_transitive : M ⊨ r.transitive ↔ IsTrans M fun x y ↦ RelMap r ![x, y] := by
  rw [isTrans_def]
  exact forall₃_congr fun _ _ _ ↦ imp_congr realize_rel₂ <| imp_congr realize_rel₂ realize_rel₂

@[simp]
/-
**FirstOrder.Language.Relations.realize_total** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Relations`。
形式化陈述：realize_total : M ⊨ r.total ↔ Std.Total fun x y : M => RelMap r ![x, y]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `total_def`：total_def : Std.Total r ↔ forall ⦃a b⦄, r a b ∨ r b a
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_sup`：realize_sup : (φ ⊔ ψ).Re
alize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs
· 使用定理 `or_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_rel₂`：realize_rel₂ {R : L.Rel
ations 2} {t₁ t₂ : L.Term _} : (R.boundedFormula₂ t₁ t₂).Realize v xs ↔ RelMap R
 ![t₁.realize (Sum.elim v xs), t₂.rea…
-/
theorem realize_total : M ⊨ r.total ↔ Std.Total fun x y : M ↦ RelMap r ![x, y] := by
  rw [total_def]
  exact forall₂_congr fun _ _ ↦ realize_sup.trans <| or_congr realize_rel₂ realize_rel₂

end Relations

section Cardinality

variable (L)
@[simp]
/-
**FirstOrder.Language.Sentence.realize_cardGe** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Sentence`。
形式化陈述：∀ (L : FirstOrder.Language) {M : Type w} [inst : L.Structure M] (n : ℕ),  
 M ⊨ FirstOrder.Language.Sentence.cardGe L n ↔ ↑n ≤ Cardinal.mk M
参数：L : FirstOrder.Language；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_mk_fin`：lift_mk_fin (n : Nat) : lift #(Fin n) = n
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.lift_mk_le`：lift_mk_le {α : Type v} {β : Type w} : lift.{max u 
w} #α <= lift.{max u v} #β ↔ Nonempty (α ↪ β)
· 使用定理 `FirstOrder.Language.Sentence.cardGe.eq_1`：∀ (L : FirstOrder.Language) (n
 : ℕ),   FirstOrder.Language.Sentence.cardGe L n =     (List.foldr (fun x1 x2 =>
 x1 ⊓ x2) ⊤         (List.map …
· 使用定理 `FirstOrder.Language.Sentence.Realize.eq_1`：∀ {L : FirstOrder.Language} (
M : Type w) [inst : L.Structure M] (φ : L.Sentence),   M ⊨ φ = FirstOrder.Langua
ge.Formula.Realize φ default
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_exs`：realize_exs {φ : L.Bound
edFormula α n} {v : α -> M} : φ.exs.Realize v ↔ exists xs : Fin n -> M, φ.Realiz
e v xs
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
-/
theorem Sentence.realize_cardGe (n) : M ⊨ Sentence.cardGe L n ↔ ↑n ≤ #M := by
  rw [← lift_mk_fin, ← lift_le.{0}, lift_lift, lift_mk_le, Sentence.cardGe, Sentence.Realize,
    BoundedFormula.realize_exs]
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
/-
**FirstOrder.Language.model_infiniteTheory_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language`。
形式化陈述：model_infiniteTheory_iff : M ⊨ L.infiniteTheory ↔ Infinite M
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem model_infiniteTheory_iff : M ⊨ L.infiniteTheory ↔ Infinite M := by
  simp [infiniteTheory, infinite_iff, aleph0_le]
/-
**FirstOrder.Language.model_infiniteTheory** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder
.Language`。
形式化陈述：model_infiniteTheory [h : Infinite M] : M ⊨ L.infiniteTheory
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.model_infiniteTheory_iff`：model_infiniteTheory_iff :
 M ⊨ L.infiniteTheory ↔ Infinite M
-/
instance model_infiniteTheory [h : Infinite M] : M ⊨ L.infiniteTheory :=
  L.model_infiniteTheory_iff.2 h

@[simp]
/-
**FirstOrder.Language.model_nonemptyTheory_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language`。
形式化陈述：model_nonemptyTheory_iff : M ⊨ L.nonemptyTheory ↔ Nonempty M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem model_nonemptyTheory_iff : M ⊨ L.nonemptyTheory ↔ Nonempty M := by
  simp only [nonemptyTheory, Theory.model_iff, Set.mem_singleton_iff, forall_eq,
    Sentence.realize_cardGe, Nat.cast_one, Cardinal.one_le_iff_ne_zero, mk_ne_zero_iff]
/-
**FirstOrder.Language.model_nonempty** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：model_nonempty [h : Nonempty M] : M ⊨ L.nonemptyTheory
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.model_nonemptyTheory_iff`：model_nonemptyTheory_iff :
 M ⊨ L.nonemptyTheory ↔ Nonempty M
-/
instance model_nonempty [h : Nonempty M] : M ⊨ L.nonemptyTheory :=
  L.model_nonemptyTheory_iff.2 h
/-
**FirstOrder.Language.model_distinctConstantsTheory** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language`。
形式化陈述：model_distinctConstantsTheory {M : Type w} [L[[α]].Structure M] (s : Set α
) : M ⊨ L.distinctConstantsTheory s ↔ Set.InjOn (fun i : α => (L.con i : M)) s
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Language.Term.realize_constants`：realize_constants {c : L.Con
stants} {v : α -> M} : c.term.realize v = c
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
/-
**FirstOrder.Language.card_le_of_model_distinctConstantsTheory** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language`。
形式化陈述：card_le_of_model_distinctConstantsTheory (s : Set α) (M : Type w) [L[[α]].
Structure M] [h : M ⊨ L.distinctConstantsTheory s] : Cardinal.lift.{w} #s <= Car
dinal.lift.{u'} #M
参数：s : Set α；M : Type w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `FirstOrder.Language.model_distinctConstantsTheory`：model_distinctConstan
tsTheory {M : Type w} [L[[α]].Structure M] (s : Set α) : M ⊨ L.distinctConstants
Theory s ↔ Set.InjOn (fun i : α => (L.c…
-/
theorem card_le_of_model_distinctConstantsTheory (s : Set α) (M : Type w) [L[[α]].Structure M]
    [h : M ⊨ L.distinctConstantsTheory s] : Cardinal.lift.{w} #s ≤ Cardinal.lift.{u'} #M :=
  lift_mk_le'.2 ⟨⟨_, Set.injOn_iff_injective.1 ((L.model_distinctConstantsTheory s).1 h)⟩⟩

end Cardinality

namespace ElementarilyEquivalent

@[symm]
nonrec theorem symm (h : M ≅[L] N) : N ≅[L] M :=
  h.symm

@[trans]
nonrec theorem trans (MN : M ≅[L] N) (NP : N ≅[L] P) : M ≅[L] P :=
  MN.trans NP

/-
**FirstOrder.Language.ElementarilyEquivalent.completeTheory_eq** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.ElementarilyEquivalent`。
形式化陈述：completeTheory_eq (h : M ≅[L] N) : L.completeTheory M = L.completeTheory N
参数：h : M ≅[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem completeTheory_eq (h : M ≅[L] N) : L.completeTheory M = L.completeTheory N :=
  h
/-
**FirstOrder.Language.ElementarilyEquivalent.realize_sentence** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.ElementarilyEquivalent`。
形式化陈述：realize_sentence (h : M ≅[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ
参数：h : M ≅[L] N；φ : L.Sentence。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.elementarilyEquivalent_iff`：elementarilyEquivalent_i
ff : M ≅[L] N ↔ forall φ : L.Sentence, M ⊨ φ ↔ N ⊨ φ
-/
theorem realize_sentence (h : M ≅[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ :=
  (elementarilyEquivalent_iff.1 h) φ
/-
**FirstOrder.Language.ElementarilyEquivalent.theory_model_iff** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.ElementarilyEquivalent`。
形式化陈述：theory_model_iff (h : M ≅[L] N) : M ⊨ T ↔ N ⊨ T
参数：h : M ≅[L] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Theory.model_iff_subset_completeTheory`：model_iff_su
bset_completeTheory : M ⊨ T ↔ T subseteq L.completeTheory M
· 使用定理 `FirstOrder.Language.ElementarilyEquivalent.completeTheory_eq`：completeTh
eory_eq (h : M ≅[L] N) : L.completeTheory M = L.completeTheory N
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem theory_model_iff (h : M ≅[L] N) : M ⊨ T ↔ N ⊨ T := by
  rw [Theory.model_iff_subset_completeTheory, Theory.model_iff_subset_completeTheory,
    h.completeTheory_eq]
/-
**FirstOrder.Language.ElementarilyEquivalent.theory_model** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.ElementarilyEquivalent`。
形式化陈述：theory_model [MT : M ⊨ T] (h : M ≅[L] N) : N ⊨ T
参数：h : M ≅[L] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.ElementarilyEquivalent.theory_model_iff`：theory_mode
l_iff (h : M ≅[L] N) : M ⊨ T ↔ N ⊨ T
-/
theorem theory_model [MT : M ⊨ T] (h : M ≅[L] N) : N ⊨ T :=
  h.theory_model_iff.1 MT
/-
**FirstOrder.Language.ElementarilyEquivalent.nonempty_iff** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.ElementarilyEquivalent`。
形式化陈述：nonempty_iff (h : M ≅[L] N) : Nonempty M ↔ Nonempty N
参数：h : M ≅[L] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `FirstOrder.Language.model_nonemptyTheory_iff`：model_nonemptyTheory_iff :
 M ⊨ L.nonemptyTheory ↔ Nonempty M
· 使用定理 `FirstOrder.Language.ElementarilyEquivalent.theory_model_iff`：theory_mode
l_iff (h : M ≅[L] N) : M ⊨ T ↔ N ⊨ T
-/
theorem nonempty_iff (h : M ≅[L] N) : Nonempty M ↔ Nonempty N :=
  (model_nonemptyTheory_iff L).symm.trans (h.theory_model_iff.trans (model_nonemptyTheory_iff L))
/-
**FirstOrder.Language.ElementarilyEquivalent.nonempty** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.ElementarilyEquivalent`。
形式化陈述：nonempty [Mn : Nonempty M] (h : M ≅[L] N) : Nonempty N
参数：h : M ≅[L] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.ElementarilyEquivalent.nonempty_iff`：nonempty_iff (h
 : M ≅[L] N) : Nonempty M ↔ Nonempty N
-/
theorem nonempty [Mn : Nonempty M] (h : M ≅[L] N) : Nonempty N :=
  h.nonempty_iff.1 Mn
/-
**FirstOrder.Language.ElementarilyEquivalent.infinite_iff** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.ElementarilyEquivalent`。
形式化陈述：infinite_iff (h : M ≅[L] N) : Infinite M ↔ Infinite N
参数：h : M ≅[L] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `FirstOrder.Language.model_infiniteTheory_iff`：model_infiniteTheory_iff :
 M ⊨ L.infiniteTheory ↔ Infinite M
· 使用定理 `FirstOrder.Language.ElementarilyEquivalent.theory_model_iff`：theory_mode
l_iff (h : M ≅[L] N) : M ⊨ T ↔ N ⊨ T
-/
theorem infinite_iff (h : M ≅[L] N) : Infinite M ↔ Infinite N :=
  (model_infiniteTheory_iff L).symm.trans (h.theory_model_iff.trans (model_infiniteTheory_iff L))
/-
**FirstOrder.Language.ElementarilyEquivalent.infinite** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.ElementarilyEquivalent`。
形式化陈述：infinite [Mi : Infinite M] (h : M ≅[L] N) : Infinite N
参数：h : M ≅[L] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.ElementarilyEquivalent.infinite_iff`：infinite_iff (h
 : M ≅[L] N) : Infinite M ↔ Infinite N
-/
theorem infinite [Mi : Infinite M] (h : M ≅[L] N) : Infinite N :=
  h.infinite_iff.1 Mi

end ElementarilyEquivalent

end Language

end FirstOrder

