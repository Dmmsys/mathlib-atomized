/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Init
/-!
# Nonempty types

This file proves a few extra facts about `Nonempty`, which is defined in core Lean.

## Main declarations

* `Nonempty.some`: Extracts a witness of nonemptiness using choice. Takes `Nonempty α` explicitly.
* `Classical.arbitrary`: Extracts a witness of nonemptiness using choice. Takes `Nonempty α` as an
  instance.
-/

@[expose] public section

section
variable {α β : Sort*}

@[simp]
/--
theorem `Nonempty.forall` / 定理 `Nonempty.forall`

English:
theorem Nonempty.forall
  given: {α} {p : Nonempty α -> Prop}
  statement: (forall h : Nonempty α, p h) ↔ forall a, p ⟨a⟩
  proof: Iff.intro (fun h _ => h _) fun h ⟨a⟩ => h a

@[simp]

中文:
定理 Nonempty.forall
  条件: {α} {p : Nonempty α -> 命题}
  结论: (对任意 h : Nonempty α, p h) ↔ 对任意 a, p ⟨a⟩
  证明: Iff.intro (fun h _ => h _) fun h ⟨a⟩ => h a

@[simp]

Depends on / 依赖: Iff.intro
-/
theorem Nonempty.forall {α} {p : Nonempty α -> Prop} : (forall h : Nonempty α, p h) ↔ forall a, p ⟨a⟩ :=
  Iff.intro (fun h _ => h _) fun h ⟨a⟩ => h a

@[simp]
/--
theorem `Nonempty.exists` / 定理 `Nonempty.exists`

English:
theorem Nonempty.exists
  given: {α} {p : Nonempty α -> Prop}
  statement: (exists h : Nonempty α, p h) ↔ exists a, p ⟨a⟩
  proof: Iff.intro (fun ⟨⟨a⟩, h⟩ => ⟨a, h⟩) fun ⟨a, h⟩ => ⟨⟨a⟩, h⟩

中文:
定理 Nonempty.exists
  条件: {α} {p : Nonempty α -> 命题}
  结论: (存在 h : Nonempty α, p h) ↔ 存在 a, p ⟨a⟩
  证明: Iff.intro (fun ⟨⟨a⟩, h⟩ => ⟨a, h⟩) fun ⟨a, h⟩ => ⟨⟨a⟩, h⟩

Depends on / 依赖: Iff.intro
-/
theorem Nonempty.exists {α} {p : Nonempty α -> Prop} : (exists h : Nonempty α, p h) ↔ exists a, p ⟨a⟩ :=
  Iff.intro (fun ⟨⟨a⟩, h⟩ => ⟨a, h⟩) fun ⟨a, h⟩ => ⟨⟨a⟩, h⟩

-- Note: we set low priority here, to ensure it is not applied before `exists_prop`
-- and `exists_const`.
@[simp low]
/--
theorem `exists_const_iff` / 定理 `exists_const_iff`

English:
theorem exists_const_iff
  given: {α : Sort*} {P : Prop}
  statement: (exists _ : α, P) ↔ Nonempty α ∧ P
  proof: Iff.intro (fun ⟨a, h⟩ => ⟨⟨a⟩, h⟩) fun ⟨⟨a⟩, h⟩ => ⟨a, h⟩

中文:
定理 exists_const_iff
  条件: {α : Sort*} {P : 命题}
  结论: (存在 _ : α, P) ↔ Nonempty α ∧ P
  证明: Iff.intro (fun ⟨a, h⟩ => ⟨⟨a⟩, h⟩) fun ⟨⟨a⟩, h⟩ => ⟨a, h⟩

Depends on / 依赖: Iff.intro
-/
theorem exists_const_iff {α : Sort*} {P : Prop} : (exists _ : α, P) ↔ Nonempty α ∧ P :=
  Iff.intro (fun ⟨a, h⟩ => ⟨⟨a⟩, h⟩) fun ⟨⟨a⟩, h⟩ => ⟨a, h⟩

/--
theorem `exists_true_iff_nonempty` / 定理 `exists_true_iff_nonempty`

English:
theorem exists_true_iff_nonempty
  given: {α : Sort*}
  statement: (exists _ : α, True) ↔ Nonempty α
  proof: Iff.intro (fun ⟨a, _⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨a, trivial⟩

中文:
定理 exists_true_iff_nonempty
  条件: {α : Sort*}
  结论: (存在 _ : α, True) ↔ Nonempty α
  证明: Iff.intro (fun ⟨a, _⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨a, trivial⟩

Depends on / 依赖: Iff.intro
-/
theorem exists_true_iff_nonempty {α : Sort*} : (exists _ : α, True) ↔ Nonempty α :=
  Iff.intro (fun ⟨a, _⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨a, trivial⟩

/--
theorem `Nonempty.imp` / 定理 `Nonempty.imp`

English:
theorem Nonempty.imp
  given: {α} {p : Prop}
  statement: (Nonempty α -> p) ↔ (α -> p)
  proof: Nonempty.forall

中文:
定理 Nonempty.imp
  条件: {α} {p : 命题}
  结论: (Nonempty α -> p) ↔ (α -> p)
  证明: Nonempty.forall

Depends on / 依赖: Nonempty, Nonempty.forall
-/
theorem Nonempty.imp {α} {p : Prop} : (Nonempty α -> p) ↔ (α -> p) :=
  Nonempty.forall

/--
theorem `not_nonempty_iff_imp_false` / 定理 `not_nonempty_iff_imp_false`

English:
theorem not_nonempty_iff_imp_false
  given: {α : Sort*}
  statement: ¬Nonempty α ↔ α -> False
  proof: Nonempty.imp

@[simp]

中文:
定理 not_nonempty_iff_imp_false
  条件: {α : Sort*}
  结论: ¬Nonempty α ↔ α -> False
  证明: Nonempty.imp

@[simp]

Depends on / 依赖: Nonempty, Nonempty.imp
-/
theorem not_nonempty_iff_imp_false {α : Sort*} : ¬Nonempty α ↔ α -> False :=
  Nonempty.imp

@[simp]
/--
theorem `nonempty_psigma` / 定理 `nonempty_psigma`

English:
theorem nonempty_psigma
  given: {α} {β : α -> Sort*}
  statement: Nonempty (PSigma β) ↔ exists a : α, Nonempty (β a)
  proof: Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩

@[simp]

中文:
定理 nonempty_psigma
  条件: {α} {β : α -> Sort*}
  结论: Nonempty (PSigma β) ↔ 存在 a : α, Nonempty (β a)
  证明: Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩

@[simp]

Depends on / 依赖: Iff.intro
-/
theorem nonempty_psigma {α} {β : α -> Sort*} : Nonempty (PSigma β) ↔ exists a : α, Nonempty (β a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩

@[simp]
/--
theorem `nonempty_subtype` / 定理 `nonempty_subtype`

English:
theorem nonempty_subtype
  given: {α} {p : α -> Prop}
  statement: Nonempty (Subtype p) ↔ exists a : α, p a
  proof: Iff.intro (fun ⟨⟨a, h⟩⟩ => ⟨a, h⟩) fun ⟨a, h⟩ => ⟨⟨a, h⟩⟩

@[simp]

中文:
定理 nonempty_subtype
  条件: {α} {p : α -> 命题}
  结论: Nonempty (Subtype p) ↔ 存在 a : α, p a
  证明: Iff.intro (fun ⟨⟨a, h⟩⟩ => ⟨a, h⟩) fun ⟨a, h⟩ => ⟨⟨a, h⟩⟩

@[simp]

Depends on / 依赖: Iff.intro
-/
theorem nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subtype p) ↔ exists a : α, p a :=
  Iff.intro (fun ⟨⟨a, h⟩⟩ => ⟨a, h⟩) fun ⟨a, h⟩ => ⟨⟨a, h⟩⟩

@[simp]
/--
theorem `nonempty_pprod` / 定理 `nonempty_pprod`

English:
theorem nonempty_pprod
  given: {α β}
  statement: Nonempty (PProd α β) ↔ Nonempty α ∧ Nonempty β
  proof: Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩

@[simp]

中文:
定理 nonempty_pprod
  条件: {α β}
  结论: Nonempty (PProd α β) ↔ Nonempty α ∧ Nonempty β
  证明: Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩

@[simp]

Depends on / 依赖: Iff.intro
-/
theorem nonempty_pprod {α β} : Nonempty (PProd α β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩

@[simp]
/--
theorem `nonempty_psum` / 定理 `nonempty_psum`

English:
theorem nonempty_psum
  given: {α β}
  statement: Nonempty (α oplus' β) ↔ Nonempty α ∨ Nonempty β
  proof: Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | PSum.inl a => Or.inl ⟨a⟩
      | PSum.inr b => Or.inr ⟨b⟩)
    fun h =>
    match h with
    | Or.inl ⟨a⟩ => ⟨PSum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨PSum.inr b⟩

@[simp]

中文:
定理 nonempty_psum
  条件: {α β}
  结论: Nonempty (α oplus' β) ↔ Nonempty α ∨ Nonempty β
  证明: Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | PSum.inl a => Or.inl ⟨a⟩
      | PSum.inr b => Or.inr ⟨b⟩)
    fun h =>
    match h with
    | Or.inl ⟨a⟩ => ⟨PSum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨PSum.inr b⟩

@[simp]

Depends on / 依赖: Iff.intro, Or.inl, Or.inr, PSum.inl, PSum.inr
-/
theorem nonempty_psum {α β} : Nonempty (α oplus' β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | PSum.inl a => Or.inl ⟨a⟩
      | PSum.inr b => Or.inr ⟨b⟩)
    fun h =>
    match h with
    | Or.inl ⟨a⟩ => ⟨PSum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨PSum.inr b⟩

@[simp]
/--
theorem `nonempty_plift` / 定理 `nonempty_plift`

English:
theorem nonempty_plift
  given: {α}
  statement: Nonempty (PLift α) ↔ Nonempty α
  proof: Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩

中文:
定理 nonempty_plift
  条件: {α}
  结论: Nonempty (PLift α) ↔ Nonempty α
  证明: Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩

Depends on / 依赖: Iff.intro
-/
theorem nonempty_plift {α} : Nonempty (PLift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩

/-- Using `Classical.choice`, lifts a (`Prop`-valued) `Nonempty` instance to a (`Type`-valued)
`Inhabited` instance. `Classical.inhabited_of_nonempty` already exists, in `Init/Classical.lean`,
but the assumption is not a type class argument, which makes it unsuitable for some applications. -/
@[instance_reducible]
/--
Definition of `Classical.inhabited_of_nonempty'` / `Classical.inhabited_of_nonempty'` 的定义

English:
definition Classical.inhabited_of_nonempty'
  signature: {α} [h : Nonempty α]
  body: ⟨Classical.choice h⟩

中文:
定义 Classical.inhabited_of_nonempty'
  签名: {α} [h : Nonempty α]
  定义体: ⟨Classical.choice h⟩

Depends on / 依赖: Classical, Classical.choice, choice
-/
noncomputable def Classical.inhabited_of_nonempty' {α} [h : Nonempty α] : Inhabited α :=
  ⟨Classical.choice h⟩

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev Nonempty.some {α} (h : Nonempty α)
  body: Classical.choice h

中文:
缩写 noncomputable
  签名: abbrev Nonempty.some {α} (h : Nonempty α)
  定义体: Classical.choice h
-/
protected noncomputable abbrev Nonempty.some {α} (h : Nonempty α) : α :=
  Classical.choice h

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev Classical.arbitrary (α) [h : Nonempty α]
  body: Classical.choice h

中文:
缩写 noncomputable
  签名: abbrev Classical.arbitrary (α) [h : Nonempty α]
  定义体: Classical.choice h
-/
protected noncomputable abbrev Classical.arbitrary (α) [h : Nonempty α] : α :=
  Classical.choice h

/--
theorem `Nonempty.map` / 定理 `Nonempty.map`

English:
theorem Nonempty.map
  given: {α β} (f : α -> β)
  statement: Nonempty α -> Nonempty β

中文:
定理 Nonempty.map
  条件: {α β} (f : α -> β)
  结论: Nonempty α -> Nonempty β

Depends on / 依赖: Nonempty, Nonempty.map
-/
theorem Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
  | ⟨h⟩ => ⟨f h⟩

/--
theorem `Nonempty.map2` / 定理 `Nonempty.map2`

English:
theorem Nonempty.map2
  given: {α β γ : Sort*} (f : α -> β -> γ)

中文:
定理 Nonempty.map2
  条件: {α β γ : Sort*} (f : α -> β -> γ)
-/
protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> γ) :
    Nonempty α -> Nonempty β -> Nonempty γ
  | ⟨x⟩, ⟨y⟩ => ⟨f x y⟩

/--
theorem `Nonempty.congr` / 定理 `Nonempty.congr`

English:
theorem Nonempty.congr
  given: {α β} (f : α -> β) (g : β -> α)
  statement: Nonempty α ↔ Nonempty β
  proof: ⟨Nonempty.map f, Nonempty.map g⟩

中文:
定理 Nonempty.congr
  条件: {α β} (f : α -> β) (g : β -> α)
  结论: Nonempty α ↔ Nonempty β
  证明: ⟨Nonempty.map f, Nonempty.map g⟩
-/
protected theorem Nonempty.congr {α β} (f : α -> β) (g : β -> α) : Nonempty α ↔ Nonempty β :=
  ⟨Nonempty.map f, Nonempty.map g⟩

/--
theorem `Nonempty.elim_to_inhabited` / 定理 `Nonempty.elim_to_inhabited`

English:
theorem Nonempty.elim_to_inhabited
  given: {α : Sort*} [h : Nonempty α] {p : Prop} (f : Inhabited α -> p)
  proof: h.elim f ∘ Inhabited.mk

中文:
定理 Nonempty.elim_to_inhabited
  条件: {α : Sort*} [h : Nonempty α] {p : 命题} (f : Inhabited α -> p)
  证明: h.elim f ∘ Inhabited.mk

Depends on / 依赖: Inhabited, Inhabited.mk, h.elim
-/
theorem Nonempty.elim_to_inhabited {α : Sort*} [h : Nonempty α] {p : Prop} (f : Inhabited α -> p) :
    p :=
h.elim f ∘ Inhabited.mk

/--
theorem `Classical.nonempty_pi` / 定理 `Classical.nonempty_pi`

English:
theorem Classical.nonempty_pi
  given: {ι} {α : ι -> Sort*}
  statement: Nonempty (forall i, α i) ↔ forall i, Nonempty (α i)
  proof: ⟨fun ⟨f⟩ a => ⟨f a⟩, @Pi.instNonempty _ _⟩

中文:
定理 Classical.nonempty_pi
  条件: {ι} {α : ι -> Sort*}
  结论: Nonempty (对任意 i, α i) ↔ 对任意 i, Nonempty (α i)
  证明: ⟨fun ⟨f⟩ a => ⟨f a⟩, @Pi.instNonempty _ _⟩

Depends on / 依赖: Pi.instNonempty, instNonempty
-/
theorem Classical.nonempty_pi {ι} {α : ι -> Sort*} : Nonempty (forall i, α i) ↔ forall i, Nonempty (α i) :=
  ⟨fun ⟨f⟩ a => ⟨f a⟩, @Pi.instNonempty _ _⟩

/--
theorem `subsingleton_of_not_nonempty` / 定理 `subsingleton_of_not_nonempty`

English:
theorem subsingleton_of_not_nonempty
  given: {α : Sort*} (h : ¬Nonempty α)
  statement: Subsingleton α
  proof: ⟨fun x => False.elim not_nonempty_iff_imp_false.mp h x⟩

中文:
定理 subsingleton_of_not_nonempty
  条件: {α : Sort*} (h : ¬Nonempty α)
  结论: Subsingleton α
  证明: ⟨fun x => False.elim not_nonempty_iff_imp_false.mp h x⟩

Depends on / 依赖: False.elim, not_nonempty_iff_imp_false, not_nonempty_iff_imp_false.mp
-/
theorem subsingleton_of_not_nonempty {α : Sort*} (h : ¬Nonempty α) : Subsingleton α :=
⟨fun x => False.elim not_nonempty_iff_imp_false.mp h x⟩

/--
theorem `Function.Surjective.nonempty` / 定理 `Function.Surjective.nonempty`

English:
theorem Function.Surjective.nonempty
  given: [h : Nonempty β] {f : α -> β} (hf : Function.Surjective f)
  proof: let ⟨y⟩ := h
  let ⟨x, _⟩ := hf y
  ⟨x⟩

中文:
定理 Function.Surjective.nonempty
  条件: [h : Nonempty β] {f : α -> β} (hf : Function.Surjective f)
  证明: let ⟨y⟩ := h
  let ⟨x, _⟩ := hf y
  ⟨x⟩
-/
theorem Function.Surjective.nonempty [h : Nonempty β] {f : α -> β} (hf : Function.Surjective f) :
    Nonempty α :=
  let ⟨y⟩ := h
  let ⟨x, _⟩ := hf y
  ⟨x⟩

end

section
variable {α β : Type*} {γ : α -> Type*}

@[simp]
/--
theorem `nonempty_sigma` / 定理 `nonempty_sigma`

English:
theorem nonempty_sigma
  statement: Nonempty (Σ a : α, γ a) ↔ exists a : α, Nonempty (γ a)
  proof: Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩

@[simp]

中文:
定理 nonempty_sigma
  结论: Nonempty (Σ a : α, γ a) ↔ 存在 a : α, Nonempty (γ a)
  证明: Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩

@[simp]

Depends on / 依赖: Iff.intro
-/
theorem nonempty_sigma : Nonempty (Σ a : α, γ a) ↔ exists a : α, Nonempty (γ a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩

@[simp]
/--
theorem `nonempty_sum` / 定理 `nonempty_sum`

English:
theorem nonempty_sum
  statement: Nonempty (α oplus β) ↔ Nonempty α ∨ Nonempty β
  proof: Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | Sum.inl a => Or.inl ⟨a⟩
      | Sum.inr b => Or.inr ⟨b⟩)
    fun h =>
    match h with
    | Or.inl ⟨a⟩ => ⟨Sum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨Sum.inr b⟩

@[simp]

中文:
定理 nonempty_sum
  结论: Nonempty (α oplus β) ↔ Nonempty α ∨ Nonempty β
  证明: Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | Sum.inl a => Or.inl ⟨a⟩
      | Sum.inr b => Or.inr ⟨b⟩)
    fun h =>
    match h with
    | Or.inl ⟨a⟩ => ⟨Sum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨Sum.inr b⟩

@[simp]

Depends on / 依赖: Iff.intro, Or.inl, Or.inr, Sum.inl, Sum.inr
-/
theorem nonempty_sum : Nonempty (α oplus β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | Sum.inl a => Or.inl ⟨a⟩
      | Sum.inr b => Or.inr ⟨b⟩)
    fun h =>
    match h with
    | Or.inl ⟨a⟩ => ⟨Sum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨Sum.inr b⟩

@[simp]
/--
theorem `nonempty_prod` / 定理 `nonempty_prod`

English:
theorem nonempty_prod
  statement: Nonempty (α × β) ↔ Nonempty α ∧ Nonempty β
  proof: Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩

@[simp]

中文:
定理 nonempty_prod
  结论: Nonempty (α × β) ↔ Nonempty α ∧ Nonempty β
  证明: Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩

@[simp]

Depends on / 依赖: Iff.intro
-/
theorem nonempty_prod : Nonempty (α × β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩

@[simp]
/--
theorem `nonempty_ulift` / 定理 `nonempty_ulift`

English:
theorem nonempty_ulift
  statement: Nonempty (ULift α) ↔ Nonempty α
  proof: Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩

中文:
定理 nonempty_ulift
  结论: Nonempty (ULift α) ↔ Nonempty α
  证明: Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩

Depends on / 依赖: Iff.intro
-/
theorem nonempty_ulift : Nonempty (ULift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩

end
