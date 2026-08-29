/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Init

/-!
# Coequalizer of a pair of functions

The coequalizer of two functions `f g : α → β` is the pair (`μ`, `p : β → μ`) that
satisfies the following universal property: Every function `u : β → γ`
with `u ∘ f = u ∘ g` factors uniquely via `p`.

In this file we define the coequalizer and provide the basic API.
-/

@[expose] public section

universe v

namespace Function

/--
Inductive type `Coequalizer.Rel` / 归纳类型 `Coequalizer.Rel`

English:
inductive Coequalizer.Rel
  parameters: {α β : Type*} (f g : α -> β)
  constructors (1):
    - intro: (x : α) : Rel f g (f x) (g x)

中文:
归纳类型 Coequalizer.Rel
  参数: {α β : 类型} (f g : α -> β)
  构造子 (1 个):
    - intro: (x : α) : Rel f g (f x) (g x)
-/
inductive Coequalizer.Rel {α β : Type*} (f g : α -> β) : β -> β -> Prop where
  | intro (x : α) : Rel f g (f x) (g x)

/--
Definition of `Coequalizer` / `Coequalizer` 的定义

English:
definition Coequalizer
  signature: {α : Type*} {β : Type v} (f g : α -> β)
  body: Quot (Function.Coequalizer.Rel f g)

中文:
定义 Coequalizer
  签名: {α : 类型} {β : 类型v} (f g : α -> β)
  定义体: Quot (Function.Coequalizer.Rel f g)

Depends on / 依赖: Coequalizer, Function, Function.Coequalizer.Rel
-/
def Coequalizer {α : Type*} {β : Type v} (f g : α -> β) : Type v :=
  Quot (Function.Coequalizer.Rel f g)

namespace Coequalizer

variable {α β : Type*} (f g : α -> β)

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x : β)
  body: Quot.mk _ x

中文:
定义 mk
  签名: (x : β)
  定义体: Quot.mk _ x

Depends on / 依赖: Quot.mk
-/
def mk (x : β) : Coequalizer f g :=
  Quot.mk _ x

/--
lemma `condition` / 引理 `condition`

English:
lemma condition
  given: (x : α)
  statement: mk f g (f x) = mk f g (g x)
  proof: Quot.sound (.intro x)

中文:
引理 condition
  条件: (x : α)
  结论: mk f g (f x) = mk f g (g x)
  证明: Quot.sound (.intro x)

Depends on / 依赖: Quot.sound
-/
lemma condition (x : α) : mk f g (f x) = mk f g (g x) :=
  Quot.sound (.intro x)

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  statement: Function.Surjective (mk f g)
  proof: Quot.exists_rep

中文:
引理 mk_surjective
  结论: Function.Surjective (mk f g)
  证明: Quot.exists_rep

Depends on / 依赖: Quot.exists_rep, exists_rep
-/
lemma mk_surjective : Function.Surjective (mk f g) :=
  Quot.exists_rep

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: {γ : Type*} (u : β -> γ) (hu : u ∘ f = u ∘ g)
  body: Quot.lift u (fun _ _ (.intro e) => congrFun hu e)

中文:
定义 desc
  签名: {γ : 类型} (u : β -> γ) (hu : u ∘ f = u ∘ g)
  定义体: Quot.lift u (fun _ _ (.intro e) => congrFun hu e)

Depends on / 依赖: Quot.lift
-/
def desc {γ : Type*} (u : β -> γ) (hu : u ∘ f = u ∘ g) : Coequalizer f g -> γ :=
  Quot.lift u (fun _ _ (.intro e) => congrFun hu e)

/--
lemma `desc_mk` / 引理 `desc_mk`

English:
lemma desc_mk
  given: {γ : Type*} (u : β -> γ) (hu : u ∘ f = u ∘ g) (x : β)
  proof: rfl

中文:
引理 desc_mk
  条件: {γ : 类型} (u : β -> γ) (hu : u ∘ f = u ∘ g) (x : β)
  证明: rfl
-/
@[simp] lemma desc_mk {γ : Type*} (u : β -> γ) (hu : u ∘ f = u ∘ g) (x : β) :
    desc f g u hu (mk f g x) = u x :=
  rfl

end Function.Coequalizer
