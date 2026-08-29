/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Pim Spelier, Daan van Gent
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.PFun
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Defs

/-!
# State Transition Systems

This file contains simple definitions and lemmas for reasoning about state transition systems
defined by a function `σ → Option σ`, where `σ` is the type of states.
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Relation

namespace StateTransition

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: {σ} (f : σ -> Option σ)
  body: PFun.fix fun s => Part.some (f s).elim (Sum.inl s) Sum.inr

中文:
定义 eval
  签名: {σ} (f : σ -> 选项类型 σ)
  定义体: PFun.fix fun s => Part.some (f s).elim (Sum.inl s) Sum.inr

Depends on / 依赖: PFun.fix, Part.some, Sum.inl, Sum.inr
-/
def eval {σ} (f : σ -> Option σ) : σ -> Part σ :=
PFun.fix fun s => Part.some (f s).elim (Sum.inl s) Sum.inr

/--
Definition of `Reaches` / `Reaches` 的定义

English:
definition Reaches
  signature: {σ} (f : σ -> Option σ)
  body: ReflTransGen fun a b => b in f a

中文:
定义 Reaches
  签名: {σ} (f : σ -> 选项类型 σ)
  定义体: ReflTransGen fun a b => b in f a

Depends on / 依赖: ReflTransGen
-/
def Reaches {σ} (f : σ -> Option σ) : σ -> σ -> Prop :=
  ReflTransGen fun a b => b in f a

/--
Definition of `Reaches₁` / `Reaches₁` 的定义

English:
definition Reaches₁
  signature: {σ} (f : σ -> Option σ)
  body: TransGen fun a b => b in f a

中文:
定义 Reaches₁
  签名: {σ} (f : σ -> 选项类型 σ)
  定义体: TransGen fun a b => b in f a

Depends on / 依赖: TransGen
-/
def Reaches₁ {σ} (f : σ -> Option σ) : σ -> σ -> Prop :=
  TransGen fun a b => b in f a

/--
theorem `reaches₁_eq` / 定理 `reaches₁_eq`

English:
theorem reaches₁_eq
  given: {σ} {f : σ -> Option σ} {a b c} (h : f a = f b)
  proof: TransGen.head'_iff.trans (TransGen.head'_iff.trans <| by rw [h]).symm

中文:
定理 reaches₁_eq
  条件: {σ} {f : σ -> 选项类型 σ} {a b c} (h : f a = f b)
  证明: TransGen.head'_iff.trans (TransGen.head'_iff.trans <| by rw [h]).symm

Depends on / 依赖: TransGen, TransGen.head, _iff, _iff.trans
-/
theorem reaches₁_eq {σ} {f : σ -> Option σ} {a b c} (h : f a = f b) :
    Reaches₁ f a c ↔ Reaches₁ f b c :=
  TransGen.head'_iff.trans (TransGen.head'_iff.trans <| by rw [h]).symm

/--
theorem `reaches_total` / 定理 `reaches_total`

English:
theorem reaches_total
  given: {σ} {f : σ -> Option σ} {a b c} (hab : Reaches f a b) (hac : Reaches f a c)
  proof: ReflTransGen.total_of_right_unique (fun _ _ _ => Option.mem_unique) hab hac

中文:
定理 reaches_total
  条件: {σ} {f : σ -> 选项类型 σ} {a b c} (hab : Reaches f a b) (hac : Reaches f a c)
  证明: ReflTransGen.total_of_right_unique (fun _ _ _ => Option.mem_unique) hab hac

Depends on / 依赖: Option.mem_unique, ReflTransGen, ReflTransGen.total_of_right_unique, mem_unique, total_of_right_unique
-/
theorem reaches_total {σ} {f : σ -> Option σ} {a b c} (hab : Reaches f a b) (hac : Reaches f a c) :
    Reaches f b c ∨ Reaches f c b :=
  ReflTransGen.total_of_right_unique (fun _ _ _ => Option.mem_unique) hab hac

/--
theorem `reaches₁_fwd` / 定理 `reaches₁_fwd`

English:
theorem reaches₁_fwd
  given: {σ} {f : σ -> Option σ} {a b c} (h₁ : Reaches₁ f a c) (h₂ : b in f a)
  proof: by
  rcases TransGen.head'_iff.1 h₁ with ⟨b', hab, hbc⟩
  cases Option.mem_unique hab h₂; exact hbc

中文:
定理 reaches₁_fwd
  条件: {σ} {f : σ -> 选项类型 σ} {a b c} (h₁ : Reaches₁ f a c) (h₂ : b in f a)
  证明: by
  rcases TransGen.head'_iff.1 h₁ with ⟨b', hab, hbc⟩
  cases Option.mem_unique hab h₂; exact hbc

Depends on / 依赖: Option.mem_unique, TransGen, TransGen.head, _iff, mem_unique
-/
theorem reaches₁_fwd {σ} {f : σ -> Option σ} {a b c} (h₁ : Reaches₁ f a c) (h₂ : b in f a) :
    Reaches f b c := by
  rcases TransGen.head'_iff.1 h₁ with ⟨b', hab, hbc⟩
  cases Option.mem_unique hab h₂; exact hbc

/--
Definition of `Reaches₀` / `Reaches₀` 的定义

English:
definition Reaches₀
  signature: {σ} (f : σ -> Option σ) (a b : σ)
  body: forall c, Reaches₁ f b c -> Reaches₁ f a c

中文:
定义 Reaches₀
  签名: {σ} (f : σ -> 选项类型 σ) (a b : σ)
  定义体: forall c, Reaches₁ f b c -> Reaches₁ f a c
-/
def Reaches₀ {σ} (f : σ -> Option σ) (a b : σ) : Prop :=
  forall c, Reaches₁ f b c -> Reaches₁ f a c

/--
theorem `Reaches₀.trans` / 定理 `Reaches₀.trans`

English:
theorem Reaches₀.trans
  statement: {σ} {f : σ -> Option σ} {a b c : σ} (h₁ : Reaches₀ f a b)

中文:
定理 Reaches₀.trans
  结论: {σ} {f : σ -> 选项类型 σ} {a b c : σ} (h₁ : Reaches₀ f a b)
-/
theorem Reaches₀.trans {σ} {f : σ -> Option σ} {a b c : σ} (h₁ : Reaches₀ f a b)
    (h₂ : Reaches₀ f b c) : Reaches₀ f a c
  | _, h₃ => h₁ _ (h₂ _ h₃)

@[refl]
/--
theorem `Reaches₀.refl` / 定理 `Reaches₀.refl`

English:
theorem Reaches₀.refl
  given: {σ} {f : σ -> Option σ} (a : σ)
  statement: Reaches₀ f a a

中文:
定理 Reaches₀.refl
  条件: {σ} {f : σ -> 选项类型 σ} (a : σ)
  结论: Reaches₀ f a a
-/
theorem Reaches₀.refl {σ} {f : σ -> Option σ} (a : σ) : Reaches₀ f a a
  | _, h => h

/--
theorem `Reaches₀.single` / 定理 `Reaches₀.single`

English:
theorem Reaches₀.single
  given: {σ} {f : σ -> Option σ} {a b : σ} (h : b in f a)
  statement: Reaches₀ f a b

中文:
定理 Reaches₀.single
  条件: {σ} {f : σ -> 选项类型 σ} {a b : σ} (h : b in f a)
  结论: Reaches₀ f a b
-/
theorem Reaches₀.single {σ} {f : σ -> Option σ} {a b : σ} (h : b in f a) : Reaches₀ f a b
  | _, h₂ => h₂.head h

/--
theorem `Reaches₀.head` / 定理 `Reaches₀.head`

English:
theorem Reaches₀.head
  given: {σ} {f : σ -> Option σ} {a b c : σ} (h : b in f a) (h₂ : Reaches₀ f b c)
  proof: (Reaches₀.single h).trans h₂

中文:
定理 Reaches₀.head
  条件: {σ} {f : σ -> 选项类型 σ} {a b c : σ} (h : b in f a) (h₂ : Reaches₀ f b c)
  证明: (Reaches₀.single h).trans h₂

Depends on / 依赖: single
-/
theorem Reaches₀.head {σ} {f : σ -> Option σ} {a b c : σ} (h : b in f a) (h₂ : Reaches₀ f b c) :
    Reaches₀ f a c :=
  (Reaches₀.single h).trans h₂

/--
theorem `Reaches₀.tail` / 定理 `Reaches₀.tail`

English:
theorem Reaches₀.tail
  given: {σ} {f : σ -> Option σ} {a b c : σ} (h₁ : Reaches₀ f a b) (h : c in f b)
  proof: h₁.trans (Reaches₀.single h)

中文:
定理 Reaches₀.tail
  条件: {σ} {f : σ -> 选项类型 σ} {a b c : σ} (h₁ : Reaches₀ f a b) (h : c in f b)
  证明: h₁.trans (Reaches₀.single h)

Depends on / 依赖: single
-/
theorem Reaches₀.tail {σ} {f : σ -> Option σ} {a b c : σ} (h₁ : Reaches₀ f a b) (h : c in f b) :
    Reaches₀ f a c :=
  h₁.trans (Reaches₀.single h)

/--
theorem `reaches₀_eq` / 定理 `reaches₀_eq`

English:
theorem reaches₀_eq
  given: {σ} {f : σ -> Option σ} {a b} (e : f a = f b)
  statement: Reaches₀ f a b

中文:
定理 reaches₀_eq
  条件: {σ} {f : σ -> 选项类型 σ} {a b} (e : f a = f b)
  结论: Reaches₀ f a b
-/
theorem reaches₀_eq {σ} {f : σ -> Option σ} {a b} (e : f a = f b) : Reaches₀ f a b
  | _, h => (reaches₁_eq e).2 h

/--
theorem `Reaches₁.to₀` / 定理 `Reaches₁.to₀`

English:
theorem Reaches₁.to₀
  given: {σ} {f : σ -> Option σ} {a b : σ} (h : Reaches₁ f a b)
  statement: Reaches₀ f a b

中文:
定理 Reaches₁.to₀
  条件: {σ} {f : σ -> 选项类型 σ} {a b : σ} (h : Reaches₁ f a b)
  结论: Reaches₀ f a b
-/
theorem Reaches₁.to₀ {σ} {f : σ -> Option σ} {a b : σ} (h : Reaches₁ f a b) : Reaches₀ f a b
  | _, h₂ => h.trans h₂

/--
theorem `Reaches.to₀` / 定理 `Reaches.to₀`

English:
theorem Reaches.to₀
  given: {σ} {f : σ -> Option σ} {a b : σ} (h : Reaches f a b)
  statement: Reaches₀ f a b

中文:
定理 Reaches.to₀
  条件: {σ} {f : σ -> 选项类型 σ} {a b : σ} (h : Reaches f a b)
  结论: Reaches₀ f a b
-/
theorem Reaches.to₀ {σ} {f : σ -> Option σ} {a b : σ} (h : Reaches f a b) : Reaches₀ f a b
  | _, h₂ => h₂.trans_right h

/--
theorem `Reaches₀.tail'` / 定理 `Reaches₀.tail'`

English:
theorem Reaches₀.tail'
  given: {σ} {f : σ -> Option σ} {a b c : σ} (h : Reaches₀ f a b) (h₂ : c in f b)
  proof: h _ (TransGen.single h₂)

中文:
定理 Reaches₀.tail'
  条件: {σ} {f : σ -> 选项类型 σ} {a b c : σ} (h : Reaches₀ f a b) (h₂ : c in f b)
  证明: h _ (TransGen.single h₂)

Depends on / 依赖: TransGen, TransGen.single, single
-/
theorem Reaches₀.tail' {σ} {f : σ -> Option σ} {a b c : σ} (h : Reaches₀ f a b) (h₂ : c in f b) :
    Reaches₁ f a c :=
  h _ (TransGen.single h₂)

/-- (co-)Induction principle for `eval`. If a property `C` holds of any point `a` evaluating to `b`
which is either terminal (meaning `a = b`) or where the next point also satisfies `C`, then it
holds of any point where `eval f a` evaluates to `b`. This formalizes the notion that if
`eval f a` evaluates to `b` then it reaches terminal state `b` in finitely many steps. -/
@[elab_as_elim]
/--
Definition of `evalInduction` / `evalInduction` 的定义

English:
definition evalInduction
  signature: {σ} {f : σ -> Option σ} {b : σ} {C : σ -> Sort*} {a : σ}
  body: PFun.fixInduction h fun a' ha' h' =>
H _ ha' fun b' e => h' _ Part.mem_some_iff.2 by rw [e]; rfl

中文:
定义 evalInduction
  签名: {σ} {f : σ -> 选项类型 σ} {b : σ} {C : σ -> 类型层*} {a : σ}
  定义体: PFun.fixInduction h fun a' ha' h' =>
H _ ha' fun b' e => h' _ Part.mem_some_iff.2 by rw [e]; rfl

Depends on / 依赖: PFun.fixInduction, Part.mem_some_iff, fixInduction, mem_some_iff
-/
def evalInduction {σ} {f : σ -> Option σ} {b : σ} {C : σ -> Sort*} {a : σ}
    (h : b in eval f a) (H : forall a, b in eval f a -> (forall a', f a = some a' -> C a') -> C a) : C a :=
  PFun.fixInduction h fun a' ha' h' =>
H _ ha' fun b' e => h' _ Part.mem_some_iff.2 by rw [e]; rfl

/--
theorem `mem_eval` / 定理 `mem_eval`

English:
theorem mem_eval
  given: {σ} {f : σ -> Option σ} {a b}
  statement: b in eval f a ↔ Reaches f a b ∧ f b = none
  proof: by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · refine evalInduction h fun a h IH => ?_
    rcases e : f a with - | a'
    · rw [Part.mem_unique h
          (PFun.mem_fix_iff.2 <| Or.inl <| Part.mem_some_iff.2 <| by rw [e]; rfl)]
      exact ⟨ReflTransGen.refl, e⟩
    · rcases PFun.mem_fix_iff.1 h with (h | ⟨_, h, _⟩) <;> rw [e] at h <;>
        cases Part.mem_some_iff.1 h
      obtain ⟨h₁, h₂⟩ := IH a' e
      exact ⟨ReflTransGen.head e h₁, h₂⟩
  · refine ReflTransGen.head_induction_on h₁ ?_ fun h _ IH => ?_
    · refine PFun.mem_fix_iff.2 (Or.inl ?_)
      rw [h₂]
      apply Part.mem_some
    · refine PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, IH⟩)
      rw [h]
      apply Part.mem_some

中文:
定理 mem_eval
  条件: {σ} {f : σ -> 选项类型 σ} {a b}
  结论: b in eval f a ↔ Reaches f a b ∧ f b = none
  证明: by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · refine evalInduction h fun a h IH => ?_
    rcases e : f a with - | a'
    · rw [Part.mem_unique h
          (PFun.mem_fix_iff.2 <| Or.inl <| Part.mem_some_iff.2 <| by rw [e]; rfl)]
      exact ⟨ReflTransGen.refl, e⟩
    · rcases PFun.mem_fix_iff.1 h with (h | ⟨_, h, _⟩) <;> rw [e] at h <;>
        cases Part.mem_some_iff.1 h
      obtain ⟨h₁, h₂⟩ := IH a' e
      exact ⟨ReflTransGen.head e h₁, h₂⟩
  · refine ReflTransGen.head_induction_on h₁ ?_ fun h _ IH => ?_
    · refine PFun.mem_fix_iff.2 (Or.inl ?_)
      rw [h₂]
      apply Part.mem_some
    · refine PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, IH⟩)
      rw [h]
      apply Part.mem_some

Depends on / 依赖: Or.inl, PFun.mem_fix_iff, Part.mem_some_iff, Part.mem_unique, ReflTransGen, ReflTransGen.head, ReflTransGen.head_induction_on, ReflTransGen.refl, evalInduction, head_induction_on, mem_fix_iff, mem_some_iff, mem_unique
-/
theorem mem_eval {σ} {f : σ -> Option σ} {a b} : b in eval f a ↔ Reaches f a b ∧ f b = none := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · refine evalInduction h fun a h IH => ?_
    rcases e : f a with - | a'
    · rw [Part.mem_unique h
          (PFun.mem_fix_iff.2 <| Or.inl <| Part.mem_some_iff.2 <| by rw [e]; rfl)]
      exact ⟨ReflTransGen.refl, e⟩
    · rcases PFun.mem_fix_iff.1 h with (h | ⟨_, h, _⟩) <;> rw [e] at h <;>
        cases Part.mem_some_iff.1 h
      obtain ⟨h₁, h₂⟩ := IH a' e
      exact ⟨ReflTransGen.head e h₁, h₂⟩
  · refine ReflTransGen.head_induction_on h₁ ?_ fun h _ IH => ?_
    · refine PFun.mem_fix_iff.2 (Or.inl ?_)
      rw [h₂]
      apply Part.mem_some
    · refine PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, IH⟩)
      rw [h]
      apply Part.mem_some

/--
theorem `eval_maximal₁` / 定理 `eval_maximal₁`

English:
theorem eval_maximal₁
  given: {σ} {f : σ -> Option σ} {a b} (h : b in eval f a) (c)
  statement: ¬Reaches₁ f b c
  proof: mem_eval.1 h
    let ⟨b', h', _⟩ := TransGen.head'_iff.1 bc
    cases b0.symm.trans h'

中文:
定理 eval_maximal₁
  条件: {σ} {f : σ -> 选项类型 σ} {a b} (h : b in eval f a) (c)
  结论: ¬Reaches₁ f b c
  证明: mem_eval.1 h
    let ⟨b', h', _⟩ := TransGen.head'_iff.1 bc
    cases b0.symm.trans h'

Depends on / 依赖: mem_eval
-/
theorem eval_maximal₁ {σ} {f : σ -> Option σ} {a b} (h : b in eval f a) (c) : ¬Reaches₁ f b c
  | bc => by
    let ⟨_, b0⟩ := mem_eval.1 h
    let ⟨b', h', _⟩ := TransGen.head'_iff.1 bc
    cases b0.symm.trans h'

/--
theorem `eval_maximal` / 定理 `eval_maximal`

English:
theorem eval_maximal
  given: {σ} {f : σ -> Option σ} {a b} (h : b in eval f a) {c}
  statement: Reaches f b c ↔ c = b
  proof: let ⟨_, b0⟩ := mem_eval.1 h
  reflTransGen_iff_eq fun b' h' => by cases b0.symm.trans h'

中文:
定理 eval_maximal
  条件: {σ} {f : σ -> 选项类型 σ} {a b} (h : b in eval f a) {c}
  结论: Reaches f b c ↔ c = b
  证明: let ⟨_, b0⟩ := mem_eval.1 h
  reflTransGen_iff_eq fun b' h' => by cases b0.symm.trans h'

Depends on / 依赖: b0.symm.trans, mem_eval, reflTransGen_iff_eq
-/
theorem eval_maximal {σ} {f : σ -> Option σ} {a b} (h : b in eval f a) {c} : Reaches f b c ↔ c = b :=
  let ⟨_, b0⟩ := mem_eval.1 h
  reflTransGen_iff_eq fun b' h' => by cases b0.symm.trans h'

/--
theorem `reaches_eval` / 定理 `reaches_eval`

English:
theorem reaches_eval
  given: {σ} {f : σ -> Option σ} {a b} (ab : Reaches f a b)
  statement: eval f a = eval f b
  proof: by
  refine Part.ext fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · have ⟨ac, c0⟩ := mem_eval.1 h
    exact mem_eval.2 ⟨(or_iff_left_of_imp fun cb => (eval_maximal h).1 cb ▸ ReflTransGen.refl).1
      (reaches_total ab ac), c0⟩
  · have ⟨bc, c0⟩ := mem_eval.1 h
    exact mem_eval.2 ⟨ab.trans bc, c0⟩

中文:
定理 reaches_eval
  条件: {σ} {f : σ -> 选项类型 σ} {a b} (ab : Reaches f a b)
  结论: eval f a = eval f b
  证明: by
  refine Part.ext fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · have ⟨ac, c0⟩ := mem_eval.1 h
    exact mem_eval.2 ⟨(or_iff_left_of_imp fun cb => (eval_maximal h).1 cb ▸ ReflTransGen.refl).1
      (reaches_total ab ac), c0⟩
  · have ⟨bc, c0⟩ := mem_eval.1 h
    exact mem_eval.2 ⟨ab.trans bc, c0⟩

Depends on / 依赖: Part.ext, ReflTransGen, ReflTransGen.refl, ab.trans, eval_maximal, mem_eval, or_iff_left_of_imp, reaches_total
-/
theorem reaches_eval {σ} {f : σ -> Option σ} {a b} (ab : Reaches f a b) : eval f a = eval f b := by
  refine Part.ext fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · have ⟨ac, c0⟩ := mem_eval.1 h
    exact mem_eval.2 ⟨(or_iff_left_of_imp fun cb => (eval_maximal h).1 cb ▸ ReflTransGen.refl).1
      (reaches_total ab ac), c0⟩
  · have ⟨bc, c0⟩ := mem_eval.1 h
    exact mem_eval.2 ⟨ab.trans bc, c0⟩

/--
Definition of `Respects` / `Respects` 的定义

English:
definition Respects
  signature: {σ₁ σ₂} (f₁ : σ₁ -> Option σ₁) (f₂ : σ₂ -> Option σ₂) (tr : σ₁ -> σ₂ -> Prop)
  body: forall ⦃a₁ a₂⦄, tr a₁ a₂ -> (match f₁ a₁ with
    | some b₁ => exists b₂, tr b₁ b₂ ∧ Reaches₁ f₂ a₂ b₂
    | none => f₂ a₂ = none : Prop)

中文:
定义 Respects
  签名: {σ₁ σ₂} (f₁ : σ₁ -> 选项类型 σ₁) (f₂ : σ₂ -> 选项类型 σ₂) (tr : σ₁ -> σ₂ -> 命题)
  定义体: forall ⦃a₁ a₂⦄, tr a₁ a₂ -> (match f₁ a₁ with
    | some b₁ => exists b₂, tr b₁ b₂ ∧ Reaches₁ f₂ a₂ b₂
    | none => f₂ a₂ = none : Prop)
-/
def Respects {σ₁ σ₂} (f₁ : σ₁ -> Option σ₁) (f₂ : σ₂ -> Option σ₂) (tr : σ₁ -> σ₂ -> Prop) :=
  forall ⦃a₁ a₂⦄, tr a₁ a₂ -> (match f₁ a₁ with
    | some b₁ => exists b₂, tr b₁ b₂ ∧ Reaches₁ f₂ a₂ b₂
    | none => f₂ a₂ = none : Prop)

/--
theorem `tr_reaches₁` / 定理 `tr_reaches₁`

English:
theorem tr_reaches₁
  statement: {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
  proof: by
  induction ab with
  | single ac =>
    have := H aa
    rwa [show f₁ a₁ = _ from ac] at this
  | @tail c₁ d₁ _ cd IH =>
    rcases IH with ⟨c₂, cc, ac₂⟩
    have := H cc
    rw [show f₁ c₁ = _ from cd] at this
    rcases this with ⟨d₂, dd, cd₂⟩
    exact ⟨_, dd, ac₂.trans cd₂⟩

中文:
定理 tr_reaches₁
  结论: {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> 命题} (H : Respects f₁ f₂ tr) {a₁ a₂}
  证明: by
  induction ab with
  | single ac =>
    have := H aa
    rwa [show f₁ a₁ = _ from ac] at this
  | @tail c₁ d₁ _ cd IH =>
    rcases IH with ⟨c₂, cc, ac₂⟩
    have := H cc
    rw [show f₁ c₁ = _ from cd] at this
    rcases this with ⟨d₂, dd, cd₂⟩
    exact ⟨_, dd, ac₂.trans cd₂⟩

Depends on / 依赖: single
-/
theorem tr_reaches₁ {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₁} (ab : Reaches₁ f₁ a₁ b₁) : exists b₂, tr b₁ b₂ ∧ Reaches₁ f₂ a₂ b₂ := by
  induction ab with
  | single ac =>
    have := H aa
    rwa [show f₁ a₁ = _ from ac] at this
  | @tail c₁ d₁ _ cd IH =>
    rcases IH with ⟨c₂, cc, ac₂⟩
    have := H cc
    rw [show f₁ c₁ = _ from cd] at this
    rcases this with ⟨d₂, dd, cd₂⟩
    exact ⟨_, dd, ac₂.trans cd₂⟩

/--
theorem `tr_reaches` / 定理 `tr_reaches`

English:
theorem tr_reaches
  statement: {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
  proof: by
  rcases reflTransGen_iff_eq_or_transGen.1 ab with (rfl | ab)
  · exact ⟨_, aa, ReflTransGen.refl⟩
  · have ⟨b₂, bb, h⟩ := tr_reaches₁ H aa ab
    exact ⟨b₂, bb, h.to_reflTransGen⟩

中文:
定理 tr_reaches
  结论: {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> 命题} (H : Respects f₁ f₂ tr) {a₁ a₂}
  证明: by
  rcases reflTransGen_iff_eq_or_transGen.1 ab with (rfl | ab)
  · exact ⟨_, aa, ReflTransGen.refl⟩
  · have ⟨b₂, bb, h⟩ := tr_reaches₁ H aa ab
    exact ⟨b₂, bb, h.to_reflTransGen⟩

Depends on / 依赖: ReflTransGen, ReflTransGen.refl, h.to_reflTransGen, reflTransGen_iff_eq_or_transGen, to_reflTransGen
-/
theorem tr_reaches {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₁} (ab : Reaches f₁ a₁ b₁) : exists b₂, tr b₁ b₂ ∧ Reaches f₂ a₂ b₂ := by
  rcases reflTransGen_iff_eq_or_transGen.1 ab with (rfl | ab)
  · exact ⟨_, aa, ReflTransGen.refl⟩
  · have ⟨b₂, bb, h⟩ := tr_reaches₁ H aa ab
    exact ⟨b₂, bb, h.to_reflTransGen⟩

/--
theorem `tr_reaches_rev` / 定理 `tr_reaches_rev`

English:
theorem tr_reaches_rev
  statement: {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
  proof: by
  induction ab with
  | refl => exact ⟨_, _, ReflTransGen.refl, aa, ReflTransGen.refl⟩
  | tail _ cd IH =>
    rcases IH with ⟨e₁, e₂, ce, ee, ae⟩
    rcases ReflTransGen.cases_head ce with (rfl | ⟨d', cd', de⟩)
    · have := H ee
      revert this
      rcases eg : f₁ e₁ with - | g₁ <;> simp only [and_imp, exists_imp]
      · intro c0
        cases cd.symm.trans c0
      · intro g₂ gg cg
        rcases TransGen.head'_iff.1 cg with ⟨d', cd', dg⟩
        cases Option.mem_unique cd cd'
        exact ⟨_, _, dg, gg, ae.tail eg⟩
    · cases Option.mem_unique cd cd'
      exact ⟨_, _, de, ee, ae⟩

中文:
定理 tr_reaches_rev
  结论: {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> 命题} (H : Respects f₁ f₂ tr) {a₁ a₂}
  证明: by
  induction ab with
  | refl => exact ⟨_, _, ReflTransGen.refl, aa, ReflTransGen.refl⟩
  | tail _ cd IH =>
    rcases IH with ⟨e₁, e₂, ce, ee, ae⟩
    rcases ReflTransGen.cases_head ce with (rfl | ⟨d', cd', de⟩)
    · have := H ee
      revert this
      rcases eg : f₁ e₁ with - | g₁ <;> simp only [and_imp, exists_imp]
      · intro c0
        cases cd.symm.trans c0
      · intro g₂ gg cg
        rcases TransGen.head'_iff.1 cg with ⟨d', cd', dg⟩
        cases Option.mem_unique cd cd'
        exact ⟨_, _, dg, gg, ae.tail eg⟩
    · cases Option.mem_unique cd cd'
      exact ⟨_, _, de, ee, ae⟩

Depends on / 依赖: Option.mem_unique, ReflTransGen, ReflTransGen.cases_head, ReflTransGen.refl, TransGen, TransGen.head, _iff, ae.tail, and_imp, cases_head, cd.symm.trans, exists_imp, mem_unique, revert
-/
theorem tr_reaches_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₂} (ab : Reaches f₂ a₂ b₂) :
    exists c₁ c₂, Reaches f₂ b₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁ := by
  induction ab with
  | refl => exact ⟨_, _, ReflTransGen.refl, aa, ReflTransGen.refl⟩
  | tail _ cd IH =>
    rcases IH with ⟨e₁, e₂, ce, ee, ae⟩
    rcases ReflTransGen.cases_head ce with (rfl | ⟨d', cd', de⟩)
    · have := H ee
      revert this
      rcases eg : f₁ e₁ with - | g₁ <;> simp only [and_imp, exists_imp]
      · intro c0
        cases cd.symm.trans c0
      · intro g₂ gg cg
        rcases TransGen.head'_iff.1 cg with ⟨d', cd', dg⟩
        cases Option.mem_unique cd cd'
        exact ⟨_, _, dg, gg, ae.tail eg⟩
    · cases Option.mem_unique cd cd'
      exact ⟨_, _, de, ee, ae⟩

/--
theorem `tr_eval` / 定理 `tr_eval`

English:
theorem tr_eval
  statement: {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {a₁ b₁ a₂}
  proof: by
  obtain ⟨ab, b0⟩ := mem_eval.1 ab
  rcases tr_reaches H aa ab with ⟨b₂, bb, ab⟩
  refine ⟨_, bb, mem_eval.2 ⟨ab, ?_⟩⟩
  have := H bb; rwa [b0] at this

中文:
定理 tr_eval
  结论: {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> 命题} (H : Respects f₁ f₂ tr) {a₁ b₁ a₂}
  证明: by
  obtain ⟨ab, b0⟩ := mem_eval.1 ab
  rcases tr_reaches H aa ab with ⟨b₂, bb, ab⟩
  refine ⟨_, bb, mem_eval.2 ⟨ab, ?_⟩⟩
  have := H bb; rwa [b0] at this

Depends on / 依赖: mem_eval, tr_reaches
-/
theorem tr_eval {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {a₁ b₁ a₂}
    (aa : tr a₁ a₂) (ab : b₁ in eval f₁ a₁) : exists b₂, tr b₁ b₂ ∧ b₂ in eval f₂ a₂ := by
  obtain ⟨ab, b0⟩ := mem_eval.1 ab
  rcases tr_reaches H aa ab with ⟨b₂, bb, ab⟩
  refine ⟨_, bb, mem_eval.2 ⟨ab, ?_⟩⟩
  have := H bb; rwa [b0] at this

/--
theorem `tr_eval_rev` / 定理 `tr_eval_rev`

English:
theorem tr_eval_rev
  statement: {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {a₁ b₂ a₂}
  proof: by
  obtain ⟨ab, b0⟩ := mem_eval.1 ab
  rcases tr_reaches_rev H aa ab with ⟨c₁, c₂, bc, cc, ac⟩
  cases (reflTransGen_iff_eq (Option.eq_none_iff_forall_not_mem.1 b0)).1 bc
  refine ⟨_, cc, mem_eval.2 ⟨ac, ?_⟩⟩
  have := H cc
  rcases hfc : f₁ c₁ with - | d₁
  · rfl
  rw [hfc] at this
  rcases this with ⟨d₂, _, bd⟩
  rcases TransGen.head'_iff.1 bd with ⟨e, h, _⟩
  cases b0.symm.trans h

中文:
定理 tr_eval_rev
  结论: {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> 命题} (H : Respects f₁ f₂ tr) {a₁ b₂ a₂}
  证明: by
  obtain ⟨ab, b0⟩ := mem_eval.1 ab
  rcases tr_reaches_rev H aa ab with ⟨c₁, c₂, bc, cc, ac⟩
  cases (reflTransGen_iff_eq (Option.eq_none_iff_forall_not_mem.1 b0)).1 bc
  refine ⟨_, cc, mem_eval.2 ⟨ac, ?_⟩⟩
  have := H cc
  rcases hfc : f₁ c₁ with - | d₁
  · rfl
  rw [hfc] at this
  rcases this with ⟨d₂, _, bd⟩
  rcases TransGen.head'_iff.1 bd with ⟨e, h, _⟩
  cases b0.symm.trans h

Depends on / 依赖: Option.eq_none_iff_forall_not_mem, TransGen, TransGen.head, _iff, b0.symm.trans, eq_none_iff_forall_not_mem, mem_eval, reflTransGen_iff_eq, tr_reaches_rev
-/
theorem tr_eval_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {a₁ b₂ a₂}
    (aa : tr a₁ a₂) (ab : b₂ in eval f₂ a₂) : exists b₁, tr b₁ b₂ ∧ b₁ in eval f₁ a₁ := by
  obtain ⟨ab, b0⟩ := mem_eval.1 ab
  rcases tr_reaches_rev H aa ab with ⟨c₁, c₂, bc, cc, ac⟩
  cases (reflTransGen_iff_eq (Option.eq_none_iff_forall_not_mem.1 b0)).1 bc
  refine ⟨_, cc, mem_eval.2 ⟨ac, ?_⟩⟩
  have := H cc
  rcases hfc : f₁ c₁ with - | d₁
  · rfl
  rw [hfc] at this
  rcases this with ⟨d₂, _, bd⟩
  rcases TransGen.head'_iff.1 bd with ⟨e, h, _⟩
  cases b0.symm.trans h

/--
theorem `tr_eval_dom` / 定理 `tr_eval_dom`

English:
theorem tr_eval_dom
  statement: {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
  proof: ⟨fun h =>
    let ⟨_, _, h, _⟩ := tr_eval_rev H aa ⟨h, rfl⟩
    h,
    fun h =>
    let ⟨_, _, h, _⟩ := tr_eval H aa ⟨h, rfl⟩
    h⟩

中文:
定理 tr_eval_dom
  结论: {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> 命题} (H : Respects f₁ f₂ tr) {a₁ a₂}
  证明: ⟨fun h =>
    let ⟨_, _, h, _⟩ := tr_eval_rev H aa ⟨h, rfl⟩
    h,
    fun h =>
    let ⟨_, _, h, _⟩ := tr_eval H aa ⟨h, rfl⟩
    h⟩

Depends on / 依赖: tr_eval, tr_eval_rev
-/
theorem tr_eval_dom {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) : (eval f₂ a₂).Dom ↔ (eval f₁ a₁).Dom :=
  ⟨fun h =>
    let ⟨_, _, h, _⟩ := tr_eval_rev H aa ⟨h, rfl⟩
    h,
    fun h =>
    let ⟨_, _, h, _⟩ := tr_eval H aa ⟨h, rfl⟩
    h⟩

/--
Definition of `FRespects` / `FRespects` 的定义

English:
definition FRespects
  signature: {σ₁ σ₂} (f₂ : σ₂ -> Option σ₂) (tr : σ₁ -> σ₂) (a₂ : σ₂)

中文:
定义 FRespects
  签名: {σ₁ σ₂} (f₂ : σ₂ -> 选项类型 σ₂) (tr : σ₁ -> σ₂) (a₂ : σ₂)
-/
def FRespects {σ₁ σ₂} (f₂ : σ₂ -> Option σ₂) (tr : σ₁ -> σ₂) (a₂ : σ₂) : Option σ₁ -> Prop
  | some b₁ => Reaches₁ f₂ a₂ (tr b₁)
  | none => f₂ a₂ = none

/--
theorem `frespects_eq` / 定理 `frespects_eq`

English:
theorem frespects_eq
  given: {σ₁ σ₂} {f₂ : σ₂ -> Option σ₂} {tr : σ₁ -> σ₂} {a₂ b₂} (h : f₂ a₂ = f₂ b₂)

中文:
定理 frespects_eq
  条件: {σ₁ σ₂} {f₂ : σ₂ -> 选项类型 σ₂} {tr : σ₁ -> σ₂} {a₂ b₂} (h : f₂ a₂ = f₂ b₂)
-/
theorem frespects_eq {σ₁ σ₂} {f₂ : σ₂ -> Option σ₂} {tr : σ₁ -> σ₂} {a₂ b₂} (h : f₂ a₂ = f₂ b₂) :
    forall {b₁}, FRespects f₂ tr a₂ b₁ ↔ FRespects f₂ tr b₂ b₁
  | some _ => reaches₁_eq h
  | none => by unfold FRespects; rw [h]

/--
theorem `fun_respects` / 定理 `fun_respects`

English:
theorem fun_respects
  given: {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂}
  proof: forall_congr' fun a₁ => by
    cases f₁ a₁ <;> simp only [FRespects, exists_eq_left', forall_eq']

中文:
定理 fun_respects
  条件: {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂}
  证明: forall_congr' fun a₁ => by
    cases f₁ a₁ <;> simp only [FRespects, exists_eq_left', forall_eq']

Depends on / 依赖: FRespects, exists_eq_left, forall_congr, forall_eq
-/
theorem fun_respects {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂} :
    (Respects f₁ f₂ fun a b => tr a = b) ↔ forall ⦃a₁⦄, FRespects f₂ tr (tr a₁) (f₁ a₁) :=
  forall_congr' fun a₁ => by
    cases f₁ a₁ <;> simp only [FRespects, exists_eq_left', forall_eq']

/--
theorem `tr_eval'` / 定理 `tr_eval'`

English:
theorem tr_eval'
  statement: {σ₁ σ₂} (f₁ : σ₁ -> Option σ₁) (f₂ : σ₂ -> Option σ₂) (tr : σ₁ -> σ₂)
  proof: Part.ext fun b₂ =>
    ⟨fun h =>
      let ⟨b₁, bb, hb⟩ := tr_eval_rev H rfl h
      (Part.mem_map_iff _).2 ⟨b₁, hb, bb⟩,
      fun h => by
      rcases (Part.mem_map_iff _).1 h with ⟨b₁, ab, bb⟩
      rcases tr_eval H rfl ab with ⟨_, rfl, h⟩
      rwa [bb] at h⟩

中文:
定理 tr_eval'
  结论: {σ₁ σ₂} (f₁ : σ₁ -> 选项类型 σ₁) (f₂ : σ₂ -> 选项类型 σ₂) (tr : σ₁ -> σ₂)
  证明: Part.ext fun b₂ =>
    ⟨fun h =>
      let ⟨b₁, bb, hb⟩ := tr_eval_rev H rfl h
      (Part.mem_map_iff _).2 ⟨b₁, hb, bb⟩,
      fun h => by
      rcases (Part.mem_map_iff _).1 h with ⟨b₁, ab, bb⟩
      rcases tr_eval H rfl ab with ⟨_, rfl, h⟩
      rwa [bb] at h⟩

Depends on / 依赖: Part.ext, Part.mem_map_iff, mem_map_iff, tr_eval, tr_eval_rev
-/
theorem tr_eval' {σ₁ σ₂} (f₁ : σ₁ -> Option σ₁) (f₂ : σ₂ -> Option σ₂) (tr : σ₁ -> σ₂)
(H : Respects f₁ f₂ fun a b => tr a = b) (a₁) : eval f₂ (tr a₁) = tr < > eval f₁ a₁ :=
  Part.ext fun b₂ =>
    ⟨fun h =>
      let ⟨b₁, bb, hb⟩ := tr_eval_rev H rfl h
      (Part.mem_map_iff _).2 ⟨b₁, hb, bb⟩,
      fun h => by
      rcases (Part.mem_map_iff _).1 h with ⟨b₁, ab, bb⟩
      rcases tr_eval H rfl ab with ⟨_, rfl, h⟩
      rwa [bb] at h⟩

section EvalsTo

/--
Definition of `EvalsTo` / `EvalsTo` 的定义

English:
structure EvalsTo
  parameters: {σ : Type*} (f : σ -> Option σ) (a : σ) (b : Option σ)
  axioms and operations (2):
    - steps : Nat
    - evals_in_steps : (flip bind f)^[steps] a = b

中文:
结构 EvalsTo
  参数: {σ : 类型} (f : σ -> 选项类型 σ) (a : σ) (b : 选项类型 σ)
  公理与运算 (2 个):
    - steps : 自然数
    - evals_in_steps : (flip bind f)^[steps] a = b
-/
structure EvalsTo {σ : Type*} (f : σ -> Option σ) (a : σ) (b : Option σ) where
  /-- number of steps taken -/
  steps : Nat
  evals_in_steps : (flip bind f)^[steps] a = b

-- note: this cannot currently be used in `calc`, as the last two arguments must be `a` and `b`.
-- If this is desired, this argument order can be changed, but this spelling is I think the most
-- natural, so there is a trade-off that needs to be made here. A notation can get around this.
/--
Definition of `EvalsToInTime` / `EvalsToInTime` 的定义

English:
structure EvalsToInTime
  parameters: {σ : Type*} (f : σ -> Option σ) (a : σ) (b : Option σ) (m : Nat)
  axioms and operations (1):
    - steps_le_m : steps <= m

中文:
结构 EvalsToInTime
  参数: {σ : 类型} (f : σ -> 选项类型 σ) (a : σ) (b : 选项类型 σ) (m : 自然数)
  公理与运算 (1 个):
    - steps_le_m : steps <= m
-/
structure EvalsToInTime {σ : Type*} (f : σ -> Option σ) (a : σ) (b : Option σ) (m : Nat) extends
  EvalsTo f a b where
  steps_le_m : steps <= m

/--
Definition of `EvalsTo.refl` / `EvalsTo.refl` 的定义

English:
definition EvalsTo.refl
  signature: {σ : Type*} (f : σ -> Option σ) (a : σ)
  body: ⟨0, rfl⟩

中文:
定义 EvalsTo.refl
  签名: {σ : 类型} (f : σ -> 选项类型 σ) (a : σ)
  定义体: ⟨0, rfl⟩
-/
def EvalsTo.refl {σ : Type*} (f : σ -> Option σ) (a : σ) : EvalsTo f a (some a) :=
  ⟨0, rfl⟩

/-- Transitivity of `EvalsTo` in the sum of the numbers of steps. -/
@[trans]
/--
Definition of `EvalsTo.trans` / `EvalsTo.trans` 的定义

English:
definition EvalsTo.trans
  signature: {σ : Type*} (f : σ -> Option σ) (a : σ) (b : σ) (c : Option σ)
  body: ⟨h₂.steps + h₁.steps, by rw [Function.iterate_add_apply, h₁.evals_in_steps, h₂.evals_in_steps]⟩

中文:
定义 EvalsTo.trans
  签名: {σ : 类型} (f : σ -> 选项类型 σ) (a : σ) (b : σ) (c : 选项类型 σ)
  定义体: ⟨h₂.steps + h₁.steps, by rw [Function.iterate_add_apply, h₁.evals_in_steps, h₂.evals_in_steps]⟩

Depends on / 依赖: Function, Function.iterate_add_apply, evals_in_steps, iterate_add_apply
-/
def EvalsTo.trans {σ : Type*} (f : σ -> Option σ) (a : σ) (b : σ) (c : Option σ)
    (h₁ : EvalsTo f a b) (h₂ : EvalsTo f b c) : EvalsTo f a c :=
  ⟨h₂.steps + h₁.steps, by rw [Function.iterate_add_apply, h₁.evals_in_steps, h₂.evals_in_steps]⟩

/--
Definition of `EvalsToInTime.refl` / `EvalsToInTime.refl` 的定义

English:
definition EvalsToInTime.refl
  signature: {σ : Type*} (f : σ -> Option σ) (a : σ)
  body: ⟨EvalsTo.refl f a, le_refl 0⟩

中文:
定义 EvalsToInTime.refl
  签名: {σ : 类型} (f : σ -> 选项类型 σ) (a : σ)
  定义体: ⟨EvalsTo.refl f a, le_refl 0⟩

Depends on / 依赖: EvalsTo, EvalsTo.refl, le_refl
-/
def EvalsToInTime.refl {σ : Type*} (f : σ -> Option σ) (a : σ) : EvalsToInTime f a (some a) 0 :=
  ⟨EvalsTo.refl f a, le_refl 0⟩

/-- Transitivity of `EvalsToInTime` in the sum of the numbers of steps. -/
@[trans]
/--
Definition of `EvalsToInTime.trans` / `EvalsToInTime.trans` 的定义

English:
definition EvalsToInTime.trans
  signature: {σ : Type*} (f : σ -> Option σ) (m₁ : Nat) (m₂ : Nat) (a : σ) (b : σ)
  body: ⟨EvalsTo.trans f a b c h₁.toEvalsTo h₂.toEvalsTo, add_le_add h₂.steps_le_m h₁.steps_le_m⟩

中文:
定义 EvalsToInTime.trans
  签名: {σ : 类型} (f : σ -> 选项类型 σ) (m₁ : 自然数) (m₂ : 自然数) (a : σ) (b : σ)
  定义体: ⟨EvalsTo.trans f a b c h₁.toEvalsTo h₂.toEvalsTo, add_le_add h₂.steps_le_m h₁.steps_le_m⟩

Depends on / 依赖: EvalsTo, EvalsTo.trans, add_le_add, steps_le_m, toEvalsTo
-/
def EvalsToInTime.trans {σ : Type*} (f : σ -> Option σ) (m₁ : Nat) (m₂ : Nat) (a : σ) (b : σ)
    (c : Option σ) (h₁ : EvalsToInTime f a b m₁) (h₂ : EvalsToInTime f b c m₂) :
    EvalsToInTime f a c (m₂ + m₁) :=
  ⟨EvalsTo.trans f a b c h₁.toEvalsTo h₂.toEvalsTo, add_le_add h₂.steps_le_m h₁.steps_le_m⟩

end EvalsTo

end StateTransition
