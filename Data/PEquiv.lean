/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Option.Basic
public import Batteries.Tactic.Congr
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.Contrapose

/-!

# Partial Equivalences

In this file, we define partial equivalences `PEquiv`, which are a bijection between a subset of `α`
and a subset of `β`. Notationally, a `PEquiv` is denoted by "`≃.`" (note that the full stop is part
of the notation). The way we store these internally is with two functions `f : α → Option β` and
the reverse function `g : β → Option α`, with the condition that if `f a` is `some b`,
then `g b` is `some a`.

## Main results

- `PEquiv.ofSet`: creates a `PEquiv` from a set `s`,
  which sends an element to itself if it is in `s`.
- `PEquiv.single`: given two elements `a : α` and `b : β`, create a `PEquiv` that sends them to
  each other, and ignores all other elements.
- `PEquiv.injective_of_forall_ne_isSome`/`injective_of_forall_isSome`: If the domain of a `PEquiv`
  is all of `α` (except possibly one point), its `toFun` is injective.

## Canonical order

`PEquiv` is canonically ordered by inclusion; that is, if a function `f` defined on a subset `s`
is equal to `g` on that subset, but `g` is also defined on a larger set, then `f ≤ g`. We also have
a definition of `⊥`, which is the empty `PEquiv` (sends all to `none`), which in the end gives us a
`SemilatticeInf` with an `OrderBot` instance.

## Tags

pequiv, partial equivalence

-/

@[expose] public section

assert_not_exists RelIso

universe u v w x

/--
Definition of `PEquiv` / `PEquiv` 的定义

English:
structure PEquiv
  parameters: (α : Type u) (β : Type v)
  axioms and operations (3):
    - toFun : α -> Option β
    - invFun : β -> Option α
    - inv : forall (a : α) (b : β), invFun b = some a ↔ toFun a = some b

中文:
结构 PEquiv
  参数: (α : 类型u) (β : 类型v)
  公理与运算 (3 个):
    - toFun : α -> Option β
    - invFun : β -> Option α
    - inv : 对任意 (a : α) (b : β), invFun b = some a ↔ toFun a = some b
-/
structure PEquiv (α : Type u) (β : Type v) where
  /-- The underlying partial function of a `PEquiv` -/
  toFun : α -> Option β
  /-- The partial inverse of `toFun` -/
  invFun : β -> Option α
  /-- `invFun` is the partial inverse of `toFun` -/
  inv : forall (a : α) (b : β), invFun b = some a ↔ toFun a = some b

/-- A `PEquiv` is a partial equivalence, a representation of a bijection between a subset
  of `α` and a subset of `β`. See also `PartialEquiv` for a version that requires `toFun` and
`invFun` to be globally defined functions and has `source` and `target` sets as extra fields. -/
infixr:25 " ≃. " => PEquiv

namespace PEquiv

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open Function Option

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (α ≃. β) α (Option β)
  body: { coe := toFun
    coe_injective := by
      rintro ⟨f₁, f₂, hf⟩ ⟨g₁, g₂, hg⟩ (rfl : f₁ = g₁)
      congr with y x
      simp only [hf, hg] }

中文:
实例 :
  签名: FunLike (α ≃. β) α (Option β)
  定义体: { coe := toFun
    coe_injective := by
      rintro ⟨f₁, f₂, hf⟩ ⟨g₁, g₂, hg⟩ (rfl : f₁ = g₁)
      congr with y x
      simp only [hf, hg] }

Depends on / 依赖: coe_injective
-/
instance : FunLike (α ≃. β) α (Option β) :=
  { coe := toFun
    coe_injective := by
      rintro ⟨f₁, f₂, hf⟩ ⟨g₁, g₂, hg⟩ (rfl : f₁ = g₁)
      congr with y x
      simp only [hf, hg] }

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f₁ : α -> Option β) (f₂ h)
  statement: (mk f₁ f₂ h : α -> Option β) = f₁
  proof: rfl

中文:
定理 coe_mk
  条件: (f₁ : α -> Option β) (f₂ h)
  结论: (mk f₁ f₂ h : α -> Option β) = f₁
  证明: rfl
-/
@[simp] theorem coe_mk (f₁ : α -> Option β) (f₂ h) : (mk f₁ f₂ h : α -> Option β) = f₁ :=
  rfl

/--
theorem `coe_mk_apply` / 定理 `coe_mk_apply`

English:
theorem coe_mk_apply
  given: (f₁ : α -> Option β) (f₂ : β -> Option α) (h) (x : α)
  proof: rfl

中文:
定理 coe_mk_apply
  条件: (f₁ : α -> Option β) (f₂ : β -> Option α) (h) (x : α)
  证明: rfl
-/
theorem coe_mk_apply (f₁ : α -> Option β) (f₂ : β -> Option α) (h) (x : α) :
    (PEquiv.mk f₁ f₂ h : α -> Option β) x = f₁ x :=
  rfl

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : α ≃. β} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : α ≃. β} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h
-/
@[ext] theorem ext {f g : α ≃. β} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- The identity map as a partial equivalence. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (α : Type*)
  body: some
  invFun := some
  inv _ _ := eq_comm

中文:
定义 refl
  签名: (α : 类型)
  定义体: some
  invFun := some
  inv _ _ := eq_comm
-/
protected def refl (α : Type*) : α ≃. α where
  toFun := some
  invFun := some
  inv _ _ := eq_comm

/-- The inverse partial equivalence. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (f : α ≃. β)
  body: f.2
  invFun := f.1
  inv _ _ := (f.inv _ _).symm

中文:
定义 symm
  签名: (f : α ≃. β)
  定义体: f.2
  invFun := f.1
  inv _ _ := (f.inv _ _).symm
-/
protected def symm (f : α ≃. β) : β ≃. α where
  toFun := f.2
  invFun := f.1
  inv _ _ := (f.inv _ _).symm

/--
theorem `mem_iff_mem` / 定理 `mem_iff_mem`

English:
theorem mem_iff_mem
  given: (f : α ≃. β)
  statement: forall {a : α} {b : β}, a in f.symm b ↔ b in f a
  proof: f.3 _ _

中文:
定理 mem_iff_mem
  条件: (f : α ≃. β)
  结论: 对任意 {a : α} {b : β}, a in f.symm b ↔ b in f a
  证明: f.3 _ _
-/
theorem mem_iff_mem (f : α ≃. β) : forall {a : α} {b : β}, a in f.symm b ↔ b in f a :=
  f.3 _ _

/--
theorem `eq_some_iff` / 定理 `eq_some_iff`

English:
theorem eq_some_iff
  given: (f : α ≃. β)
  statement: forall {a : α} {b : β}, f.symm b = some a ↔ f a = some b
  proof: f.3 _ _

中文:
定理 eq_some_iff
  条件: (f : α ≃. β)
  结论: 对任意 {a : α} {b : β}, f.symm b = some a ↔ f a = some b
  证明: f.3 _ _
-/
theorem eq_some_iff (f : α ≃. β) : forall {a : α} {b : β}, f.symm b = some a ↔ f a = some b :=
  f.3 _ _

/-- Composition of partial equivalences `f : α ≃. β` and `g : β ≃. γ`. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (f : α ≃. β) (g : β ≃. γ)
  body: (f a).bind g
  invFun a := (g.symm a).bind f.symm
  inv a b := by simp_all [and_comm, eq_some_iff f, eq_some_iff g, bind_eq_some_iff]

@[simp]

中文:
定义 trans
  签名: (f : α ≃. β) (g : β ≃. γ)
  定义体: (f a).bind g
  invFun a := (g.symm a).bind f.symm
  inv a b := by simp_all [and_comm, eq_some_iff f, eq_some_iff g, bind_eq_some_iff]

@[simp]
-/
protected def trans (f : α ≃. β) (g : β ≃. γ) :
    α ≃. γ where
  toFun a := (f a).bind g
  invFun a := (g.symm a).bind f.symm
  inv a b := by simp_all [and_comm, eq_some_iff f, eq_some_iff g, bind_eq_some_iff]

@[simp]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (a : α)
  statement: PEquiv.refl α a = some a
  proof: rfl

@[simp]

中文:
定理 refl_apply
  条件: (a : α)
  结论: PEquiv.refl α a = some a
  证明: rfl

@[simp]
-/
theorem refl_apply (a : α) : PEquiv.refl α a = some a :=
  rfl

@[simp]
/--
theorem `symm_refl` / 定理 `symm_refl`

English:
theorem symm_refl
  statement: (PEquiv.refl α).symm = PEquiv.refl α
  proof: rfl

@[simp]

中文:
定理 symm_refl
  结论: (PEquiv.refl α).symm = PEquiv.refl α
  证明: rfl

@[simp]
-/
theorem symm_refl : (PEquiv.refl α).symm = PEquiv.refl α :=
  rfl

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (f : α ≃. β)
  statement: f.symm.symm = f
  proof: rfl

中文:
定理 symm_symm
  条件: (f : α ≃. β)
  结论: f.symm.symm = f
  证明: rfl
-/
theorem symm_symm (f : α ≃. β) : f.symm.symm = f := rfl

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (f : α ≃. β) {x : β} {y : α}
  statement: f.symm x = y ↔ x = f y
  proof: by
  rw [eq_some_iff]; rw [eq_comm]

中文:
定理 symm_apply_eq
  条件: (f : α ≃. β) {x : β} {y : α}
  结论: f.symm x = y ↔ x = f y
  证明: by
  rw [eq_some_iff]; rw [eq_comm]

Depends on / 依赖: eq_comm, eq_some_iff
-/
theorem symm_apply_eq (f : α ≃. β) {x : β} {y : α} : f.symm x = y ↔ x = f y := by
  rw [eq_some_iff]; rw [eq_comm]

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (f : α ≃. β) {x : β} {y : α}
  statement: y = f.symm x ↔ f y = x
  proof: by
  rw [← eq_some_iff]; rw [eq_comm]

中文:
定理 eq_symm_apply
  条件: (f : α ≃. β) {x : β} {y : α}
  结论: y = f.symm x ↔ f y = x
  证明: by
  rw [← eq_some_iff]; rw [eq_comm]

Depends on / 依赖: eq_comm, eq_some_iff
-/
theorem eq_symm_apply (f : α ≃. β) {x : β} {y : α} : y = f.symm x ↔ f y = x := by
  rw [← eq_some_iff]; rw [eq_comm]

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (PEquiv.symm : (α ≃. β) -> β ≃. α)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  结论: Function.Bijective (PEquiv.symm : (α ≃. β) -> β ≃. α)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (PEquiv.symm : (α ≃. β) -> β ≃. α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
theorem `symm_injective` / 定理 `symm_injective`

English:
theorem symm_injective
  statement: Function.Injective (@PEquiv.symm α β)
  proof: symm_bijective.injective

中文:
定理 symm_injective
  结论: Function.Injective (@PEquiv.symm α β)
  证明: symm_bijective.injective

Depends on / 依赖: injective, symm_bijective, symm_bijective.injective
-/
theorem symm_injective : Function.Injective (@PEquiv.symm α β) :=
  symm_bijective.injective

/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  given: (f : α ≃. β) (g : β ≃. γ) (h : γ ≃. δ)
  proof: ext fun _ => Option.bind_assoc _ _ _

中文:
定理 trans_assoc
  条件: (f : α ≃. β) (g : β ≃. γ) (h : γ ≃. δ)
  证明: ext fun _ => Option.bind_assoc _ _ _

Depends on / 依赖: Option.bind_assoc, bind_assoc
-/
theorem trans_assoc (f : α ≃. β) (g : β ≃. γ) (h : γ ≃. δ) :
    (f.trans g).trans h = f.trans (g.trans h) :=
  ext fun _ => Option.bind_assoc _ _ _

/--
theorem `mem_trans` / 定理 `mem_trans`

English:
theorem mem_trans
  given: (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ)
  proof: Option.bind_eq_some_iff

中文:
定理 mem_trans
  条件: (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ)
  证明: Option.bind_eq_some_iff

Depends on / 依赖: Option.bind_eq_some_iff, bind_eq_some_iff
-/
theorem mem_trans (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) :
    c in f.trans g a ↔ exists b, b in f a ∧ c in g b :=
  Option.bind_eq_some_iff

/--
theorem `trans_eq_some` / 定理 `trans_eq_some`

English:
theorem trans_eq_some
  given: (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ)
  proof: Option.bind_eq_some_iff

中文:
定理 trans_eq_some
  条件: (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ)
  证明: Option.bind_eq_some_iff

Depends on / 依赖: Option.bind_eq_some_iff, bind_eq_some_iff
-/
theorem trans_eq_some (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) :
    f.trans g a = some c ↔ exists b, f a = some b ∧ g b = some c :=
  Option.bind_eq_some_iff

/--
theorem `trans_eq_none` / 定理 `trans_eq_none`

English:
theorem trans_eq_none
  given: (f : α ≃. β) (g : β ≃. γ) (a : α)
  proof: by
  simp only [eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm]
  push Not
  exact forall_comm

@[simp]

中文:
定理 trans_eq_none
  条件: (f : α ≃. β) (g : β ≃. γ) (a : α)
  证明: by
  simp only [eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm]
  push Not
  exact forall_comm

@[simp]

Depends on / 依赖: eq_none_iff_forall_not_mem, forall_comm, imp_iff_not_or, imp_iff_not_or.symm, mem_trans
-/
theorem trans_eq_none (f : α ≃. β) (g : β ≃. γ) (a : α) :
    f.trans g a = none ↔ forall b c, b ∉ f a ∨ c ∉ g b := by
  simp only [eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm]
  push Not
  exact forall_comm

@[simp]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  given: (f : α ≃. β)
  statement: (PEquiv.refl α).trans f = f
  proof: by
  ext; dsimp [PEquiv.trans]; rfl

中文:
定理 refl_trans
  条件: (f : α ≃. β)
  结论: (PEquiv.refl α).trans f = f
  证明: by
  ext; dsimp [PEquiv.trans]; rfl

Depends on / 依赖: PEquiv, PEquiv.trans
-/
theorem refl_trans (f : α ≃. β) : (PEquiv.refl α).trans f = f := by
  ext; dsimp [PEquiv.trans]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  given: (f : α ≃. β)
  statement: f.trans (PEquiv.refl β) = f
  proof: by
  ext; dsimp [PEquiv.trans]; simp

中文:
定理 trans_refl
  条件: (f : α ≃. β)
  结论: f.trans (PEquiv.refl β) = f
  证明: by
  ext; dsimp [PEquiv.trans]; simp

Depends on / 依赖: PEquiv, PEquiv.trans
-/
theorem trans_refl (f : α ≃. β) : f.trans (PEquiv.refl β) = f := by
  ext; dsimp [PEquiv.trans]; simp

/--
theorem `inj` / 定理 `inj`

English:
theorem inj
  given: (f : α ≃. β) {a₁ a₂ : α} {b : β} (h₁ : b in f a₁) (h₂ : b in f a₂)
  proof: by rw [← mem_iff_mem] at *; cases h : f.symm b <;> simp_all

中文:
定理 inj
  条件: (f : α ≃. β) {a₁ a₂ : α} {b : β} (h₁ : b in f a₁) (h₂ : b in f a₂)
  证明: by rw [← mem_iff_mem] at *; cases h : f.symm b <;> simp_all
-/
protected theorem inj (f : α ≃. β) {a₁ a₂ : α} {b : β} (h₁ : b in f a₁) (h₂ : b in f a₂) :
    a₁ = a₂ := by rw [← mem_iff_mem] at *; cases h : f.symm b <;> simp_all

/--
theorem `injective_of_forall_ne_isSome` / 定理 `injective_of_forall_ne_isSome`

English:
theorem injective_of_forall_ne_isSome
  statement: (f : α ≃. β) (a₂ : α)
  proof: HasLeftInverse.injective
    ⟨fun b => Option.recOn b a₂ fun b' => Option.recOn (f.symm b') a₂ id, fun x => by
      cases hfx : f x
      · have : x = a₂ := not_imp_comm.1 (h x) (hfx.symm ▸ by simp)
        simp [this]
      · dsimp only
        rw [(eq_some_iff f).2 hfx]
        rfl⟩

中文:
定理 injective_of_forall_ne_isSome
  结论: (f : α ≃. β) (a₂ : α)
  证明: HasLeftInverse.injective
    ⟨fun b => Option.recOn b a₂ fun b' => Option.recOn (f.symm b') a₂ id, fun x => by
      cases hfx : f x
      · have : x = a₂ := not_imp_comm.1 (h x) (hfx.symm ▸ by simp)
        simp [this]
      · dsimp only
        rw [(eq_some_iff f).2 hfx]
        rfl⟩

Depends on / 依赖: HasLeftInverse, HasLeftInverse.injective, Option.recOn, eq_some_iff, f.symm, hfx.symm, injective, not_imp_comm
-/
theorem injective_of_forall_ne_isSome (f : α ≃. β) (a₂ : α)
    (h : forall a₁ : α, a₁ != a₂ -> isSome (f a₁)) : Injective f :=
  HasLeftInverse.injective
    ⟨fun b => Option.recOn b a₂ fun b' => Option.recOn (f.symm b') a₂ id, fun x => by
      cases hfx : f x
      · have : x = a₂ := not_imp_comm.1 (h x) (hfx.symm ▸ by simp)
        simp [this]
      · dsimp only
        rw [(eq_some_iff f).2 hfx]
        rfl⟩

/--
theorem `injective_of_forall_isSome` / 定理 `injective_of_forall_isSome`

English:
theorem injective_of_forall_isSome
  given: {f : α ≃. β} (h : forall a : α, isSome (f a))
  statement: Injective f
  proof: (Classical.em (Nonempty α)).elim
    (fun hn => injective_of_forall_ne_isSome f (Classical.choice hn) fun a _ => h a) fun hn x =>
    (hn ⟨x⟩).elim

中文:
定理 injective_of_forall_isSome
  条件: {f : α ≃. β} (h : 对任意 a : α, isSome (f a))
  结论: Injective f
  证明: (Classical.em (Nonempty α)).elim
    (fun hn => injective_of_forall_ne_isSome f (Classical.choice hn) fun a _ => h a) fun hn x =>
    (hn ⟨x⟩).elim

Depends on / 依赖: Classical, Classical.choice, Classical.em, Nonempty, choice, injective_of_forall_ne_isSome
-/
theorem injective_of_forall_isSome {f : α ≃. β} (h : forall a : α, isSome (f a)) : Injective f :=
  (Classical.em (Nonempty α)).elim
    (fun hn => injective_of_forall_ne_isSome f (Classical.choice hn) fun a _ => h a) fun hn x =>
    (hn ⟨x⟩).elim

section OfSet

variable (s : Set α) [DecidablePred (· in s)]

/--
Definition of `ofSet` / `ofSet` 的定义

English:
definition ofSet
  signature: (s : Set α) [DecidablePred (· in s)]
  body: if a in s then some a else none
  invFun a := if a in s then some a else none
  inv a b := by
    split_ifs with hb ha ha
    · simp [eq_comm]
    · simp [ne_of_mem_of_not_mem hb ha]
    · simp [ne_of_mem_of_not_mem ha hb]
    · simp

中文:
定义 ofSet
  签名: (s : Set α) [DecidablePred (· in s)]
  定义体: if a in s then some a else none
  invFun a := if a in s then some a else none
  inv a b := by
    split_ifs with hb ha ha
    · simp [eq_comm]
    · simp [ne_of_mem_of_not_mem hb ha]
    · simp [ne_of_mem_of_not_mem ha hb]
    · simp
-/
def ofSet (s : Set α) [DecidablePred (· in s)] :
    α ≃. α where
  toFun a := if a in s then some a else none
  invFun a := if a in s then some a else none
  inv a b := by
    split_ifs with hb ha ha
    · simp [eq_comm]
    · simp [ne_of_mem_of_not_mem hb ha]
    · simp [ne_of_mem_of_not_mem ha hb]
    · simp

/--
theorem `mem_ofSet_self_iff` / 定理 `mem_ofSet_self_iff`

English:
theorem mem_ofSet_self_iff
  given: {s : Set α} [DecidablePred (· in s)] {a : α}
  statement: a in ofSet s a ↔ a in s
  proof: by
  dsimp [ofSet]; split_ifs <;> simp [*]

中文:
定理 mem_ofSet_self_iff
  条件: {s : Set α} [DecidablePred (· in s)] {a : α}
  结论: a in ofSet s a ↔ a in s
  证明: by
  dsimp [ofSet]; split_ifs <;> simp [*]

Depends on / 依赖: split_ifs
-/
theorem mem_ofSet_self_iff {s : Set α} [DecidablePred (· in s)] {a : α} : a in ofSet s a ↔ a in s := by
  dsimp [ofSet]; split_ifs <;> simp [*]

/--
theorem `mem_ofSet_iff` / 定理 `mem_ofSet_iff`

English:
theorem mem_ofSet_iff
  given: {s : Set α} [DecidablePred (· in s)] {a b : α}
  proof: by
  dsimp [ofSet]
  grind

@[simp]

中文:
定理 mem_ofSet_iff
  条件: {s : Set α} [DecidablePred (· in s)] {a b : α}
  证明: by
  dsimp [ofSet]
  grind

@[simp]
-/
theorem mem_ofSet_iff {s : Set α} [DecidablePred (· in s)] {a b : α} :
    a in ofSet s b ↔ a = b ∧ a in s := by
  dsimp [ofSet]
  grind

@[simp]
/--
theorem `ofSet_eq_some_iff` / 定理 `ofSet_eq_some_iff`

English:
theorem ofSet_eq_some_iff
  given: {s : Set α} {_ : DecidablePred (· in s)} {a b : α}
  proof: mem_ofSet_iff

中文:
定理 ofSet_eq_some_iff
  条件: {s : Set α} {_ : DecidablePred (· in s)} {a b : α}
  证明: mem_ofSet_iff

Depends on / 依赖: IsFractionRing, IsFractionRing.integerNormalization_eq_zero_iff.not.mpr, integerNormalization_eq_zero_iff, map_ne_zero, mem_ofSet_iff
-/
theorem ofSet_eq_some_iff {s : Set α} {_ : DecidablePred (· in s)} {a b : α} :
    ofSet s b = some a ↔ a = b ∧ a in s :=
  mem_ofSet_iff

/--
theorem `ofSet_eq_some_self_iff` / 定理 `ofSet_eq_some_self_iff`

English:
theorem ofSet_eq_some_self_iff
  given: {s : Set α} {_ : DecidablePred (· in s)} {a : α}
  proof: mem_ofSet_self_iff

@[simp]

中文:
定理 ofSet_eq_some_self_iff
  条件: {s : Set α} {_ : DecidablePred (· in s)} {a : α}
  证明: mem_ofSet_self_iff

@[simp]

Depends on / 依赖: mem_ofSet_self_iff
-/
theorem ofSet_eq_some_self_iff {s : Set α} {_ : DecidablePred (· in s)} {a : α} :
    ofSet s a = some a ↔ a in s :=
  mem_ofSet_self_iff

@[simp]
/--
theorem `ofSet_symm` / 定理 `ofSet_symm`

English:
theorem ofSet_symm
  statement: (ofSet s).symm = ofSet s
  proof: rfl

@[simp]

中文:
定理 ofSet_symm
  结论: (ofSet s).symm = ofSet s
  证明: rfl

@[simp]
-/
theorem ofSet_symm : (ofSet s).symm = ofSet s :=
  rfl

@[simp]
/--
theorem `ofSet_univ` / 定理 `ofSet_univ`

English:
theorem ofSet_univ
  statement: ofSet Set.univ = PEquiv.refl α
  proof: rfl

@[simp]

中文:
定理 ofSet_univ
  结论: ofSet Set.univ = PEquiv.refl α
  证明: rfl

@[simp]

Depends on / 依赖: IsLocalization, IsLocalization.integerNormalization_spec, algebraMap, choose_spec, integerNormalization_spec
-/
theorem ofSet_univ : ofSet Set.univ = PEquiv.refl α :=
  rfl

@[simp]
/--
theorem `ofSet_eq_refl` / 定理 `ofSet_eq_refl`

English:
theorem ofSet_eq_refl
  given: {s : Set α} [DecidablePred (· in s)]
  proof: ⟨fun h => by
    rw [Set.eq_univ_iff_forall]
    intro
    rw [← mem_ofSet_self_iff]; rw [h]
    exact rfl, fun h => by simp only [← ofSet_univ, h]⟩

中文:
定理 ofSet_eq_refl
  条件: {s : Set α} [DecidablePred (· in s)]
  证明: ⟨fun h => by
    rw [Set.eq_univ_iff_forall]
    intro
    rw [← mem_ofSet_self_iff]; rw [h]
    exact rfl, fun h => by simp only [← ofSet_univ, h]⟩

Depends on / 依赖: Set.eq_univ_iff_forall, eq_univ_iff_forall, mem_ofSet_self_iff, ofSet_univ
-/
theorem ofSet_eq_refl {s : Set α} [DecidablePred (· in s)] :
    ofSet s = PEquiv.refl α ↔ s = Set.univ :=
  ⟨fun h => by
    rw [Set.eq_univ_iff_forall]
    intro
    rw [← mem_ofSet_self_iff]; rw [h]
    exact rfl, fun h => by simp only [← ofSet_univ, h]⟩

end OfSet

/--
theorem `symm_trans_rev` / 定理 `symm_trans_rev`

English:
theorem symm_trans_rev
  given: (f : α ≃. β) (g : β ≃. γ)
  statement: (f.trans g).symm = g.symm.trans f.symm
  proof: rfl

中文:
定理 symm_trans_rev
  条件: (f : α ≃. β) (g : β ≃. γ)
  结论: (f.trans g).symm = g.symm.trans f.symm
  证明: rfl
-/
theorem symm_trans_rev (f : α ≃. β) (g : β ≃. γ) : (f.trans g).symm = g.symm.trans f.symm :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (f : α ≃. β)
  statement: f.trans f.symm = ofSet { a | (f a).isSome }
  proof: by
  ext
  dsimp [PEquiv.trans]
  simp only [eq_some_iff f, Option.isSome_iff_exists, bind_eq_some_iff,
    ofSet_eq_some_iff]
  constructor
  · rintro ⟨b, hb₁, hb₂⟩
    exact ⟨PEquiv.inj _ hb₂ hb₁, b, hb₂⟩
  · simp +contextual

中文:
定理 self_trans_symm
  条件: (f : α ≃. β)
  结论: f.trans f.symm = ofSet { a | (f a).isSome }
  证明: by
  ext
  dsimp [PEquiv.trans]
  simp only [eq_some_iff f, Option.isSome_iff_exists, bind_eq_some_iff,
    ofSet_eq_some_iff]
  constructor
  · rintro ⟨b, hb₁, hb₂⟩
    exact ⟨PEquiv.inj _ hb₂ hb₁, b, hb₂⟩
  · simp +contextual

Depends on / 依赖: Option.isSome_iff_exists, PEquiv, PEquiv.inj, PEquiv.trans, bind_eq_some_iff, contextual, eq_some_iff, isSome_iff_exists, ofSet_eq_some_iff
-/
theorem self_trans_symm (f : α ≃. β) : f.trans f.symm = ofSet { a | (f a).isSome } := by
  ext
  dsimp [PEquiv.trans]
  simp only [eq_some_iff f, Option.isSome_iff_exists, bind_eq_some_iff,
    ofSet_eq_some_iff]
  constructor
  · rintro ⟨b, hb₁, hb₂⟩
    exact ⟨PEquiv.inj _ hb₂ hb₁, b, hb₂⟩
  · simp +contextual

/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (f : α ≃. β)
  statement: f.symm.trans f = ofSet { b | (f.symm b).isSome }
  proof: symm_injective by simp [symm_trans_rev, self_trans_symm, -symm_symm]

中文:
定理 symm_trans_self
  条件: (f : α ≃. β)
  结论: f.symm.trans f = ofSet { b | (f.symm b).isSome }
  证明: symm_injective by simp [symm_trans_rev, self_trans_symm, -symm_symm]

Depends on / 依赖: self_trans_symm, symm_injective, symm_symm, symm_trans_rev
-/
theorem symm_trans_self (f : α ≃. β) : f.symm.trans f = ofSet { b | (f.symm b).isSome } :=
symm_injective by simp [symm_trans_rev, self_trans_symm, -symm_symm]

/--
theorem `trans_symm_eq_iff_forall_isSome` / 定理 `trans_symm_eq_iff_forall_isSome`

English:
theorem trans_symm_eq_iff_forall_isSome
  given: {f : α ≃. β}
  proof: by
  rw [self_trans_symm]; rw [ofSet_eq_refl]; rw [Set.eq_univ_iff_forall]; rfl

中文:
定理 trans_symm_eq_iff_forall_isSome
  条件: {f : α ≃. β}
  证明: by
  rw [self_trans_symm]; rw [ofSet_eq_refl]; rw [Set.eq_univ_iff_forall]; rfl

Depends on / 依赖: Set.eq_univ_iff_forall, eq_univ_iff_forall, ofSet_eq_refl, self_trans_symm
-/
theorem trans_symm_eq_iff_forall_isSome {f : α ≃. β} :
    f.trans f.symm = PEquiv.refl α ↔ forall a, isSome (f a) := by
  rw [self_trans_symm]; rw [ofSet_eq_refl]; rw [Set.eq_univ_iff_forall]; rfl

/--
Instance `instBotPEquiv` / 实例 `instBotPEquiv`

English:
instance instBotPEquiv
  signature: : Bot (α ≃. β)
  body: ⟨{ toFun := fun _ => none
      invFun := fun _ => none
      inv := by simp }⟩

中文:
实例 instBotPEquiv
  签名: : Bot (α ≃. β)
  定义体: ⟨{ toFun := fun _ => none
      invFun := fun _ => none
      inv := by simp }⟩

Depends on / 依赖: invFun
-/
instance instBotPEquiv : Bot (α ≃. β) :=
  ⟨{ toFun := fun _ => none
      invFun := fun _ => none
      inv := by simp }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (α ≃. β)
  body: ⟨⊥⟩

@[simp]

中文:
实例 :
  签名: Inhabited (α ≃. β)
  定义体: ⟨⊥⟩

@[simp]
-/
instance : Inhabited (α ≃. β) :=
  ⟨⊥⟩

@[simp]
/--
theorem `bot_apply` / 定理 `bot_apply`

English:
theorem bot_apply
  given: (a : α)
  statement: (⊥ : α ≃. β) a = none
  proof: rfl

@[simp]

中文:
定理 bot_apply
  条件: (a : α)
  结论: (⊥ : α ≃. β) a = none
  证明: rfl

@[simp]
-/
theorem bot_apply (a : α) : (⊥ : α ≃. β) a = none :=
  rfl

@[simp]
/--
theorem `symm_bot` / 定理 `symm_bot`

English:
theorem symm_bot
  statement: (⊥ : α ≃. β).symm = ⊥
  proof: rfl

@[simp]

中文:
定理 symm_bot
  结论: (⊥ : α ≃. β).symm = ⊥
  证明: rfl

@[simp]
-/
theorem symm_bot : (⊥ : α ≃. β).symm = ⊥ :=
  rfl

@[simp]
/--
theorem `trans_bot` / 定理 `trans_bot`

English:
theorem trans_bot
  given: (f : α ≃. β)
  statement: f.trans (⊥ : β ≃. γ) = ⊥
  proof: by
  ext; dsimp [PEquiv.trans]; simp

@[simp]

中文:
定理 trans_bot
  条件: (f : α ≃. β)
  结论: f.trans (⊥ : β ≃. γ) = ⊥
  证明: by
  ext; dsimp [PEquiv.trans]; simp

@[simp]

Depends on / 依赖: PEquiv, PEquiv.trans
-/
theorem trans_bot (f : α ≃. β) : f.trans (⊥ : β ≃. γ) = ⊥ := by
  ext; dsimp [PEquiv.trans]; simp

@[simp]
/--
theorem `bot_trans` / 定理 `bot_trans`

English:
theorem bot_trans
  given: (f : β ≃. γ)
  statement: (⊥ : α ≃. β).trans f = ⊥
  proof: by
  ext; dsimp [PEquiv.trans]; simp

中文:
定理 bot_trans
  条件: (f : β ≃. γ)
  结论: (⊥ : α ≃. β).trans f = ⊥
  证明: by
  ext; dsimp [PEquiv.trans]; simp

Depends on / 依赖: PEquiv, PEquiv.trans
-/
theorem bot_trans (f : β ≃. γ) : (⊥ : α ≃. β).trans f = ⊥ := by
  ext; dsimp [PEquiv.trans]; simp

/--
theorem `isSome_symm_get` / 定理 `isSome_symm_get`

English:
theorem isSome_symm_get
  given: (f : α ≃. β) {a : α} (h : isSome (f a))
  proof: isSome_iff_exists.2 ⟨a, by rw [f.eq_some_iff, some_get]⟩

中文:
定理 isSome_symm_get
  条件: (f : α ≃. β) {a : α} (h : isSome (f a))
  证明: isSome_iff_exists.2 ⟨a, by rw [f.eq_some_iff, some_get]⟩

Depends on / 依赖: eq_some_iff, f.eq_some_iff, isSome_iff_exists, some_get
-/
theorem isSome_symm_get (f : α ≃. β) {a : α} (h : isSome (f a)) :
    isSome (f.symm (Option.get _ h)) :=
  isSome_iff_exists.2 ⟨a, by rw [f.eq_some_iff, some_get]⟩

section Single

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (a : α) (b : β)
  body: if x = a then some b else none
  invFun x := if x = b then some a else none
  inv x y := by
    split_ifs with h1 h2
    · simp [*]
    · simp only [some.injEq, iff_false] at *
      exact Ne.symm h2
    · simp only [some.injEq, false_iff] at *
      exact Ne.symm h1
    · simp

中文:
定义 single
  签名: (a : α) (b : β)
  定义体: if x = a then some b else none
  invFun x := if x = b then some a else none
  inv x y := by
    split_ifs with h1 h2
    · simp [*]
    · simp only [some.injEq, iff_false] at *
      exact Ne.symm h2
    · simp only [some.injEq, false_iff] at *
      exact Ne.symm h1
    · simp
-/
def single (a : α) (b : β) :
    α ≃. β where
  toFun x := if x = a then some b else none
  invFun x := if x = b then some a else none
  inv x y := by
    split_ifs with h1 h2
    · simp [*]
    · simp only [some.injEq, iff_false] at *
      exact Ne.symm h2
    · simp only [some.injEq, false_iff] at *
      exact Ne.symm h1
    · simp

/--
theorem `mem_single` / 定理 `mem_single`

English:
theorem mem_single
  given: (a : α) (b : β)
  statement: b in single a b a
  proof: if_pos rfl

中文:
定理 mem_single
  条件: (a : α) (b : β)
  结论: b in single a b a
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
theorem mem_single (a : α) (b : β) : b in single a b a :=
  if_pos rfl

/--
theorem `mem_single_iff` / 定理 `mem_single_iff`

English:
theorem mem_single_iff
  given: (a₁ a₂ : α) (b₁ b₂ : β)
  statement: b₁ in single a₂ b₂ a₁ ↔ a₁ = a₂ ∧ b₁ = b₂
  proof: by
  dsimp [single]; split_ifs <;> simp [*, eq_comm]

@[simp]

中文:
定理 mem_single_iff
  条件: (a₁ a₂ : α) (b₁ b₂ : β)
  结论: b₁ in single a₂ b₂ a₁ ↔ a₁ = a₂ ∧ b₁ = b₂
  证明: by
  dsimp [single]; split_ifs <;> simp [*, eq_comm]

@[simp]

Depends on / 依赖: eq_comm, single, split_ifs
-/
theorem mem_single_iff (a₁ a₂ : α) (b₁ b₂ : β) : b₁ in single a₂ b₂ a₁ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  dsimp [single]; split_ifs <;> simp [*, eq_comm]

@[simp]
/--
theorem `symm_single` / 定理 `symm_single`

English:
theorem symm_single
  given: (a : α) (b : β)
  statement: (single a b).symm = single b a
  proof: rfl

@[simp]

中文:
定理 symm_single
  条件: (a : α) (b : β)
  结论: (single a b).symm = single b a
  证明: rfl

@[simp]
-/
theorem symm_single (a : α) (b : β) : (single a b).symm = single b a :=
  rfl

@[simp]
/--
theorem `single_apply` / 定理 `single_apply`

English:
theorem single_apply
  given: (a : α) (b : β)
  statement: single a b a = some b
  proof: if_pos rfl

中文:
定理 single_apply
  条件: (a : α) (b : β)
  结论: single a b a = some b
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
theorem single_apply (a : α) (b : β) : single a b a = some b :=
  if_pos rfl

/--
theorem `single_apply_of_ne` / 定理 `single_apply_of_ne`

English:
theorem single_apply_of_ne
  given: {a₁ a₂ : α} (h : a₁ != a₂) (b : β)
  statement: single a₁ b a₂ = none
  proof: if_neg h.symm

中文:
定理 single_apply_of_ne
  条件: {a₁ a₂ : α} (h : a₁ != a₂) (b : β)
  结论: single a₁ b a₂ = none
  证明: if_neg h.symm

Depends on / 依赖: h.symm, if_neg
-/
theorem single_apply_of_ne {a₁ a₂ : α} (h : a₁ != a₂) (b : β) : single a₁ b a₂ = none :=
  if_neg h.symm

/--
theorem `single_trans_of_mem` / 定理 `single_trans_of_mem`

English:
theorem single_trans_of_mem
  given: (a : α) {b : β} {c : γ} {f : β ≃. γ} (h : c in f b)
  proof: by
  ext
  dsimp [single, PEquiv.trans]
  split_ifs <;> simp_all

中文:
定理 single_trans_of_mem
  条件: (a : α) {b : β} {c : γ} {f : β ≃. γ} (h : c in f b)
  证明: by
  ext
  dsimp [single, PEquiv.trans]
  split_ifs <;> simp_all

Depends on / 依赖: PEquiv, PEquiv.trans, single, split_ifs
-/
theorem single_trans_of_mem (a : α) {b : β} {c : γ} {f : β ≃. γ} (h : c in f b) :
    (single a b).trans f = single a c := by
  ext
  dsimp [single, PEquiv.trans]
  split_ifs <;> simp_all

/--
theorem `trans_single_of_mem` / 定理 `trans_single_of_mem`

English:
theorem trans_single_of_mem
  given: {a : α} {b : β} (c : γ) {f : α ≃. β} (h : b in f a)
  proof: symm_injective single_trans_of_mem _ ((mem_iff_mem f).2 h)

@[simp]

中文:
定理 trans_single_of_mem
  条件: {a : α} {b : β} (c : γ) {f : α ≃. β} (h : b in f a)
  证明: symm_injective single_trans_of_mem _ ((mem_iff_mem f).2 h)

@[simp]

Depends on / 依赖: mem_iff_mem, single_trans_of_mem, symm_injective
-/
theorem trans_single_of_mem {a : α} {b : β} (c : γ) {f : α ≃. β} (h : b in f a) :
    f.trans (single b c) = single a c :=
symm_injective single_trans_of_mem _ ((mem_iff_mem f).2 h)

@[simp]
/--
theorem `single_trans_single` / 定理 `single_trans_single`

English:
theorem single_trans_single
  given: (a : α) (b : β) (c : γ)
  proof: single_trans_of_mem _ (mem_single _ _)

@[simp]

中文:
定理 single_trans_single
  条件: (a : α) (b : β) (c : γ)
  证明: single_trans_of_mem _ (mem_single _ _)

@[simp]

Depends on / 依赖: mem_single, single_trans_of_mem
-/
theorem single_trans_single (a : α) (b : β) (c : γ) :
    (single a b).trans (single b c) = single a c :=
  single_trans_of_mem _ (mem_single _ _)

@[simp]
/--
theorem `single_subsingleton_eq_refl` / 定理 `single_subsingleton_eq_refl`

English:
theorem single_subsingleton_eq_refl
  given: [Subsingleton α] (a b : α)
  statement: single a b = PEquiv.refl α
  proof: by
  ext i j
  dsimp [single]
  rw [if_pos (Subsingleton.elim i a)]; rw [Subsingleton.elim i j]; rw [Subsingleton.elim b j]

中文:
定理 single_subsingleton_eq_refl
  条件: [Subsingleton α] (a b : α)
  结论: single a b = PEquiv.refl α
  证明: by
  ext i j
  dsimp [single]
  rw [if_pos (Subsingleton.elim i a)]; rw [Subsingleton.elim i j]; rw [Subsingleton.elim b j]

Depends on / 依赖: Subsingleton, Subsingleton.elim, if_pos, single
-/
theorem single_subsingleton_eq_refl [Subsingleton α] (a b : α) : single a b = PEquiv.refl α := by
  ext i j
  dsimp [single]
  rw [if_pos (Subsingleton.elim i a)]; rw [Subsingleton.elim i j]; rw [Subsingleton.elim b j]

/--
theorem `trans_single_of_eq_none` / 定理 `trans_single_of_eq_none`

English:
theorem trans_single_of_eq_none
  given: {b : β} (c : γ) {f : δ ≃. β} (h : f.symm b = none)
  proof: by
  ext
  simp only [eq_none_iff_forall_not_mem, Option.mem_def, f.eq_some_iff] at h
  dsimp [PEquiv.trans, single]
  simp only [bind_eq_some_iff, iff_false, not_exists, not_and, reduceCtorEq]
  intros
  split_ifs <;> simp_all

中文:
定理 trans_single_of_eq_none
  条件: {b : β} (c : γ) {f : δ ≃. β} (h : f.symm b = none)
  证明: by
  ext
  simp only [eq_none_iff_forall_not_mem, Option.mem_def, f.eq_some_iff] at h
  dsimp [PEquiv.trans, single]
  simp only [bind_eq_some_iff, iff_false, not_exists, not_and, reduceCtorEq]
  intros
  split_ifs <;> simp_all

Depends on / 依赖: Option.mem_def, PEquiv, PEquiv.trans, bind_eq_some_iff, eq_none_iff_forall_not_mem, eq_some_iff, f.eq_some_iff, iff_false, intros, mem_def, not_and, not_exists, reduceCtorEq, single, split_ifs
-/
theorem trans_single_of_eq_none {b : β} (c : γ) {f : δ ≃. β} (h : f.symm b = none) :
    f.trans (single b c) = ⊥ := by
  ext
  simp only [eq_none_iff_forall_not_mem, Option.mem_def, f.eq_some_iff] at h
  dsimp [PEquiv.trans, single]
  simp only [bind_eq_some_iff, iff_false, not_exists, not_and, reduceCtorEq]
  intros
  split_ifs <;> simp_all

/--
theorem `single_trans_of_eq_none` / 定理 `single_trans_of_eq_none`

English:
theorem single_trans_of_eq_none
  given: (a : α) {b : β} {f : β ≃. δ} (h : f b = none)
  proof: symm_injective trans_single_of_eq_none _ h

中文:
定理 single_trans_of_eq_none
  条件: (a : α) {b : β} {f : β ≃. δ} (h : f b = none)
  证明: symm_injective trans_single_of_eq_none _ h

Depends on / 依赖: symm_injective, trans_single_of_eq_none
-/
theorem single_trans_of_eq_none (a : α) {b : β} {f : β ≃. δ} (h : f b = none) :
    (single a b).trans f = ⊥ :=
symm_injective trans_single_of_eq_none _ h

/--
theorem `single_trans_single_of_ne` / 定理 `single_trans_single_of_ne`

English:
theorem single_trans_single_of_ne
  given: {b₁ b₂ : β} (h : b₁ != b₂) (a : α) (c : γ)
  proof: single_trans_of_eq_none _ (single_apply_of_ne h.symm _)

中文:
定理 single_trans_single_of_ne
  条件: {b₁ b₂ : β} (h : b₁ != b₂) (a : α) (c : γ)
  证明: single_trans_of_eq_none _ (single_apply_of_ne h.symm _)

Depends on / 依赖: h.symm, single_apply_of_ne, single_trans_of_eq_none
-/
theorem single_trans_single_of_ne {b₁ b₂ : β} (h : b₁ != b₂) (a : α) (c : γ) :
    (single a b₁).trans (single b₂ c) = ⊥ :=
  single_trans_of_eq_none _ (single_apply_of_ne h.symm _)

end Single

section Order

/--
Instance `instPartialOrderPEquiv` / 实例 `instPartialOrderPEquiv`

English:
instance instPartialOrderPEquiv
  signature: : PartialOrder (α ≃. β) where
  body: forall (a : α) (b : β), b in f a -> b in g a
  le_refl _ _ _ := id
  le_trans _ _ _ fg gh a b := gh a b ∘ fg a b
  le_antisymm f g fg gf :=
    ext
      (by
        intro a
        rcases h : g a with _ | b
· exact eq_none_iff_forall_not_mem.2 fun b hb => Option.not_mem_none b h ▸ fg a b hb
       

中文:
实例 instPartialOrderPEquiv
  签名: : PartialOrder (α ≃. β) where
  定义体: forall (a : α) (b : β), b in f a -> b in g a
  le_refl _ _ _ := id
  le_trans _ _ _ fg gh a b := gh a b ∘ fg a b
  le_antisymm f g fg gf :=
    ext
      (by
        intro a
        rcases h : g a with _ | b
· exact eq_none_iff_forall_not_mem.2 fun b hb => Option.not_mem_none b h ▸ fg a b hb
       
-/
instance instPartialOrderPEquiv : PartialOrder (α ≃. β) where
  le f g := forall (a : α) (b : β), b in f a -> b in g a
  le_refl _ _ _ := id
  le_trans _ _ _ fg gh a b := gh a b ∘ fg a b
  le_antisymm f g fg gf :=
    ext
      (by
        intro a
        rcases h : g a with _ | b
· exact eq_none_iff_forall_not_mem.2 fun b hb => Option.not_mem_none b h ▸ fg a b hb
        · exact gf _ _ h)

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {f g : α ≃. β}
  statement: f <= g ↔ forall (a : α) (b : β), b in f a -> b in g a
  proof: Iff.rfl

中文:
定理 le_def
  条件: {f g : α ≃. β}
  结论: f <= g ↔ 对任意 (a : α) (b : β), b in f a -> b in g a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def {f g : α ≃. β} : f <= g ↔ forall (a : α) (b : β), b in f a -> b in g a :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (α ≃. β)
  body: { instBotPEquiv with bot_le := fun _ _ _ h => (not_mem_none _ h).elim }

中文:
实例 :
  签名: OrderBot (α ≃. β)
  定义体: { instBotPEquiv with bot_le := fun _ _ _ h => (not_mem_none _ h).elim }

Depends on / 依赖: bot_le, instBotPEquiv, not_mem_none
-/
instance : OrderBot (α ≃. β) :=
  { instBotPEquiv with bot_le := fun _ _ _ h => (not_mem_none _ h).elim }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] [DecidableEq β] : SemilatticeInf (α ≃. β)
  body: { instPartialOrderPEquiv with
    inf := fun f g =>
      { toFun := fun a => if f a = g a then f a else none
        invFun := fun b => if f.symm b = g.symm b then f.symm b else none
        inv := fun a b => by
          have hf := @mem_iff_mem _ _ f a b
          have hg := @mem_iff_mem _ _ g a b

中文:
实例 [DecidableEq
  签名: α] [DecidableEq β] : SemilatticeInf (α ≃. β)
  定义体: { instPartialOrderPEquiv with
    inf := fun f g =>
      { toFun := fun a => if f a = g a then f a else none
        invFun := fun b => if f.symm b = g.symm b then f.symm b else none
        inv := fun a b => by
          have hf := @mem_iff_mem _ _ f a b
          have hg := @mem_iff_mem _ _ g a b

Depends on / 依赖: Option.mem_def, coe_mk, f.symm, g.symm, inf_le_left, inf_le_right, instPartialOrderPEquiv, invFun, le_inf, mem_def, mem_iff_mem, split_ifs
-/
instance [DecidableEq α] [DecidableEq β] : SemilatticeInf (α ≃. β) :=
  { instPartialOrderPEquiv with
    inf := fun f g =>
      { toFun := fun a => if f a = g a then f a else none
        invFun := fun b => if f.symm b = g.symm b then f.symm b else none
        inv := fun a b => by
          have hf := @mem_iff_mem _ _ f a b
          have hg := @mem_iff_mem _ _ g a b
          simp only [Option.mem_def] at *
          grind }
    inf_le_left := fun _ _ _ _ => by simp only [coe_mk, mem_def]; split_ifs <;> simp [*]
    inf_le_right := fun _ _ _ _ => by simp only [coe_mk, mem_def]; split_ifs <;> simp [*]
    le_inf := fun f g h fg gh a b => by
      intro H
      have hf := fg a b H
      have hg := gh a b H
      simp only [Option.mem_def, PEquiv.coe_mk_apply] at *
      rw [hf]; rw [hg]; rw [if_pos rfl] }

end Order

end PEquiv

namespace Equiv

variable {α : Type*} {β : Type*} {γ : Type*}

/--
Definition of `toPEquiv` / `toPEquiv` 的定义

English:
definition toPEquiv
  signature: (f : α ≃ β)
  body: some ∘ f
  invFun := some ∘ f.symm
  inv := by simp [Equiv.eq_symm_apply, eq_comm]

@[simp]

中文:
定义 toPEquiv
  签名: (f : α ≃ β)
  定义体: some ∘ f
  invFun := some ∘ f.symm
  inv := by simp [Equiv.eq_symm_apply, eq_comm]

@[simp]
-/
def toPEquiv (f : α ≃ β) : α ≃. β where
  toFun := some ∘ f
  invFun := some ∘ f.symm
  inv := by simp [Equiv.eq_symm_apply, eq_comm]

@[simp]
/--
theorem `toPEquiv_refl` / 定理 `toPEquiv_refl`

English:
theorem toPEquiv_refl
  statement: (Equiv.refl α).toPEquiv = PEquiv.refl α
  proof: rfl

中文:
定理 toPEquiv_refl
  结论: (Equiv.refl α).toPEquiv = PEquiv.refl α
  证明: rfl
-/
theorem toPEquiv_refl : (Equiv.refl α).toPEquiv = PEquiv.refl α :=
  rfl

/--
theorem `toPEquiv_trans` / 定理 `toPEquiv_trans`

English:
theorem toPEquiv_trans
  given: (f : α ≃ β) (g : β ≃ γ)
  proof: rfl

中文:
定理 toPEquiv_trans
  条件: (f : α ≃ β) (g : β ≃ γ)
  证明: rfl
-/
theorem toPEquiv_trans (f : α ≃ β) (g : β ≃ γ) :
    (f.trans g).toPEquiv = f.toPEquiv.trans g.toPEquiv :=
  rfl

/--
theorem `toPEquiv_symm` / 定理 `toPEquiv_symm`

English:
theorem toPEquiv_symm
  given: (f : α ≃ β)
  statement: f.symm.toPEquiv = f.toPEquiv.symm
  proof: rfl

@[simp]

中文:
定理 toPEquiv_symm
  条件: (f : α ≃ β)
  结论: f.symm.toPEquiv = f.toPEquiv.symm
  证明: rfl

@[simp]
-/
theorem toPEquiv_symm (f : α ≃ β) : f.symm.toPEquiv = f.toPEquiv.symm :=
  rfl

@[simp]
/--
theorem `toPEquiv_apply` / 定理 `toPEquiv_apply`

English:
theorem toPEquiv_apply
  given: (f : α ≃ β) (x : α)
  statement: f.toPEquiv x = some (f x)
  proof: rfl

中文:
定理 toPEquiv_apply
  条件: (f : α ≃ β) (x : α)
  结论: f.toPEquiv x = some (f x)
  证明: rfl
-/
theorem toPEquiv_apply (f : α ≃ β) (x : α) : f.toPEquiv x = some (f x) :=
  rfl

end Equiv
