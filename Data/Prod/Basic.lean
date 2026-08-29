/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Lean.PrettyPrinter.Delaborator.Builtins
public import Mathlib.Logic.Function.Defs
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Inhabit
public import Batteries.Tactic.Trans

import Mathlib.Tactic.Attr.Register

/-!
# Extra facts about `Prod`

This file proves various simple lemmas about `Prod`.
It also defines better delaborators for product projections.
-/

@[expose] public section

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

namespace Prod

/--
lemma `swap_eq_iff_eq_swap` / 引理 `swap_eq_iff_eq_swap`

English:
lemma swap_eq_iff_eq_swap
  given: {x : α × β} {y : β × α}
  statement: x.swap = y ↔ x = y.swap
  proof: by grind

中文:
引理 swap_eq_iff_eq_swap
  条件: {x : α × β} {y : β × α}
  结论: x.swap = y ↔ x = y.swap
  证明: by grind
-/
lemma swap_eq_iff_eq_swap {x : α × β} {y : β × α} : x.swap = y ↔ x = y.swap := by grind

/--
Definition of `mk.injArrow` / `mk.injArrow` 的定义

English:
definition mk.injArrow
  signature: {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β}
  body: by
  intros h P w
  cases h
  exact w rfl rfl

@[simp]

中文:
定义 mk.injArrow
  签名: {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β}
  定义体: by
  intros h P w
  cases h
  exact w rfl rfl

@[simp]

Depends on / 依赖: intros
-/
def mk.injArrow {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) -> forall ⦃P : Sort*⦄, (x₁ = x₂ -> y₁ = y₂ -> P) -> P := by
  intros h P w
  cases h
  exact w rfl rfl

@[simp]
/--
theorem `mk.eta` / 定理 `mk.eta`

English:
theorem mk.eta
  statement: forall {p : α × β}, (p.1, p.2) = p

中文:
定理 mk.eta
  结论: 对任意 {p : α × β}, (p.1, p.2) = p
-/
theorem mk.eta : forall {p : α × β}, (p.1, p.2) = p
  | (_, _) => rfl

/--
theorem `forall'` / 定理 `forall'`

English:
theorem forall'
  given: {p : α -> β -> Prop}
  statement: (forall x : α × β, p x.1 x.2) ↔ forall a b, p a b
  proof: Prod.forall

中文:
定理 forall'
  条件: {p : α -> β -> 命题}
  结论: (对任意 x : α × β, p x.1 x.2) ↔ 对任意 a b, p a b
  证明: Prod.forall

Depends on / 依赖: Prod.forall
-/
theorem forall' {p : α -> β -> Prop} : (forall x : α × β, p x.1 x.2) ↔ forall a b, p a b :=
  Prod.forall

/--
theorem `exists'` / 定理 `exists'`

English:
theorem exists'
  given: {p : α -> β -> Prop}
  statement: (exists x : α × β, p x.1 x.2) ↔ exists a b, p a b
  proof: Prod.exists

@[simp]

中文:
定理 exists'
  条件: {p : α -> β -> 命题}
  结论: (存在 x : α × β, p x.1 x.2) ↔ 存在 a b, p a b
  证明: Prod.exists

@[simp]

Depends on / 依赖: Prod.exists
-/
theorem exists' {p : α -> β -> Prop} : (exists x : α × β, p x.1 x.2) ↔ exists a b, p a b :=
  Prod.exists

@[simp]
/--
theorem `snd_comp_mk` / 定理 `snd_comp_mk`

English:
theorem snd_comp_mk
  given: (x : α)
  statement: Prod.snd ∘ (Prod.mk x : β -> α × β) = id
  proof: rfl

@[simp]

中文:
定理 snd_comp_mk
  条件: (x : α)
  结论: Prod.snd ∘ (Prod.mk x : β -> α × β) = id
  证明: rfl

@[simp]
-/
theorem snd_comp_mk (x : α) : Prod.snd ∘ (Prod.mk x : β -> α × β) = id :=
  rfl

@[simp]
/--
theorem `fst_comp_mk` / 定理 `fst_comp_mk`

English:
theorem fst_comp_mk
  given: (x : α)
  statement: Prod.fst ∘ (Prod.mk x : β -> α × β) = Function.const β x
  proof: rfl

中文:
定理 fst_comp_mk
  条件: (x : α)
  结论: Prod.fst ∘ (Prod.mk x : β -> α × β) = Function.const β x
  证明: rfl
-/
theorem fst_comp_mk (x : α) : Prod.fst ∘ (Prod.mk x : β -> α × β) = Function.const β x :=
  rfl

attribute [mfld_simps] map_apply

-- This was previously a `simp` lemma, but no longer is on the basis that it destructures the pair.
-- See `map_apply`, `map_fst`, and `map_snd` for slightly weaker lemmas in the `simp` set.
/--
theorem `map_apply'` / 定理 `map_apply'`

English:
theorem map_apply'
  given: (f : α -> γ) (g : β -> δ) (p : α × β)
  statement: map f g p = (f p.1, g p.2)
  proof: rfl

中文:
定理 map_apply'
  条件: (f : α -> γ) (g : β -> δ) (p : α × β)
  结论: map f g p = (f p.1, g p.2)
  证明: rfl
-/
theorem map_apply' (f : α -> γ) (g : β -> δ) (p : α × β) : map f g p = (f p.1, g p.2) :=
  rfl

/--
theorem `map_fst'` / 定理 `map_fst'`

English:
theorem map_fst'
  given: (f : α -> γ) (g : β -> δ)
  statement: Prod.fst ∘ map f g = f ∘ Prod.fst
  proof: funext map_fst f g

中文:
定理 map_fst'
  条件: (f : α -> γ) (g : β -> δ)
  结论: Prod.fst ∘ map f g = f ∘ Prod.fst
  证明: funext map_fst f g

Depends on / 依赖: map_fst
-/
theorem map_fst' (f : α -> γ) (g : β -> δ) : Prod.fst ∘ map f g = f ∘ Prod.fst :=
funext map_fst f g

/--
theorem `map_snd'` / 定理 `map_snd'`

English:
theorem map_snd'
  given: (f : α -> γ) (g : β -> δ)
  statement: Prod.snd ∘ map f g = g ∘ Prod.snd
  proof: funext map_snd f g

中文:
定理 map_snd'
  条件: (f : α -> γ) (g : β -> δ)
  结论: Prod.snd ∘ map f g = g ∘ Prod.snd
  证明: funext map_snd f g

Depends on / 依赖: map_snd
-/
theorem map_snd' (f : α -> γ) (g : β -> δ) : Prod.snd ∘ map f g = g ∘ Prod.snd :=
funext map_snd f g

/--
theorem `mk_inj` / 定理 `mk_inj`

English:
theorem mk_inj
  given: {a₁ a₂ : α} {b₁ b₂ : β}
  statement: (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂
  proof: by simp

中文:
定理 mk_inj
  条件: {a₁ a₂ : α} {b₁ b₂ : β}
  结论: (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂
  证明: by simp
-/
theorem mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂ := by simp

/--
theorem `mk_right_injective` / 定理 `mk_right_injective`

English:
theorem mk_right_injective
  given: {α β : Type*} (a : α)
  statement: (mk a : β -> α × β).Injective
  proof: by
  intro b₁ b₂ h
  simpa only [true_and, Prod.mk_inj, eq_self_iff_true] using h

中文:
定理 mk_right_injective
  条件: {α β : 类型} (a : α)
  结论: (mk a : β -> α × β).Injective
  证明: by
  intro b₁ b₂ h
  simpa only [true_and, Prod.mk_inj, eq_self_iff_true] using h

Depends on / 依赖: Prod.mk_inj, eq_self_iff_true, mk_inj, true_and
-/
theorem mk_right_injective {α β : Type*} (a : α) : (mk a : β -> α × β).Injective := by
  intro b₁ b₂ h
  simpa only [true_and, Prod.mk_inj, eq_self_iff_true] using h

/--
theorem `mk_left_injective` / 定理 `mk_left_injective`

English:
theorem mk_left_injective
  given: {α β : Type*} (b : β)
  statement: (fun a => mk a b : α -> α × β).Injective
  proof: by
  intro b₁ b₂ h
  simpa only [and_true, eq_self_iff_true, mk_inj] using h

中文:
定理 mk_left_injective
  条件: {α β : 类型} (b : β)
  结论: (fun a => mk a b : α -> α × β).Injective
  证明: by
  intro b₁ b₂ h
  simpa only [and_true, eq_self_iff_true, mk_inj] using h

Depends on / 依赖: and_true, eq_self_iff_true, mk_inj
-/
theorem mk_left_injective {α β : Type*} (b : β) : (fun a => mk a b : α -> α × β).Injective := by
  intro b₁ b₂ h
  simpa only [and_true, eq_self_iff_true, mk_inj] using h

/--
lemma `mk_right_inj` / 引理 `mk_right_inj`

English:
lemma mk_right_inj
  given: {a : α} {b₁ b₂ : β}
  statement: (a, b₁) = (a, b₂) ↔ b₁ = b₂
  proof: (mk_right_injective _).eq_iff

中文:
引理 mk_right_inj
  条件: {a : α} {b₁ b₂ : β}
  结论: (a, b₁) = (a, b₂) ↔ b₁ = b₂
  证明: (mk_right_injective _).eq_iff

Depends on / 依赖: eq_iff, mk_right_injective
-/
lemma mk_right_inj {a : α} {b₁ b₂ : β} : (a, b₁) = (a, b₂) ↔ b₁ = b₂ :=
    (mk_right_injective _).eq_iff

/--
lemma `mk_left_inj` / 引理 `mk_left_inj`

English:
lemma mk_left_inj
  given: {a₁ a₂ : α} {b : β}
  statement: (a₁, b) = (a₂, b) ↔ a₁ = a₂
  proof: (mk_left_injective _).eq_iff

中文:
引理 mk_left_inj
  条件: {a₁ a₂ : α} {b : β}
  结论: (a₁, b) = (a₂, b) ↔ a₁ = a₂
  证明: (mk_left_injective _).eq_iff

Depends on / 依赖: eq_iff, mk_left_injective
-/
lemma mk_left_inj {a₁ a₂ : α} {b : β} : (a₁, b) = (a₂, b) ↔ a₁ = a₂ := (mk_left_injective _).eq_iff

/--
theorem `map_def` / 定理 `map_def`

English:
theorem map_def
  given: {f : α -> γ} {g : β -> δ}
  statement: Prod.map f g = fun p : α × β => (f p.1, g p.2)
  proof: funext fun p => Prod.ext (map_fst f g p) (map_snd f g p)

中文:
定理 map_def
  条件: {f : α -> γ} {g : β -> δ}
  结论: Prod.map f g = fun p : α × β => (f p.1, g p.2)
  证明: funext fun p => Prod.ext (map_fst f g p) (map_snd f g p)

Depends on / 依赖: Prod.ext, map_fst, map_snd
-/
theorem map_def {f : α -> γ} {g : β -> δ} : Prod.map f g = fun p : α × β => (f p.1, g p.2) :=
  funext fun p => Prod.ext (map_fst f g p) (map_snd f g p)

/--
theorem `id_prod` / 定理 `id_prod`

English:
theorem id_prod
  statement: (fun p : α × β => (p.1, p.2)) = id
  proof: rfl

@[simp]

中文:
定理 id_prod
  结论: (fun p : α × β => (p.1, p.2)) = id
  证明: rfl

@[simp]
-/
theorem id_prod : (fun p : α × β => (p.1, p.2)) = id :=
  rfl

@[simp]
/--
theorem `map_iterate` / 定理 `map_iterate`

English:
theorem map_iterate
  given: (f : α -> α) (g : β -> β) (n : Nat)
  proof: by induction n <;> simp [*, Prod.map_comp_map]

中文:
定理 map_iterate
  条件: (f : α -> α) (g : β -> β) (n : 自然数)
  证明: by induction n <;> simp [*, Prod.map_comp_map]

Depends on / 依赖: Prod.map_comp_map, map_comp_map
-/
theorem map_iterate (f : α -> α) (g : β -> β) (n : Nat) :
    (Prod.map f g)^[n] = Prod.map f^[n] g^[n] := by induction n <;> simp [*, Prod.map_comp_map]

/--
theorem `fst_surjective` / 定理 `fst_surjective`

English:
theorem fst_surjective
  given: [h : Nonempty β]
  statement: Function.Surjective (@fst α β)
  proof: fun x => h.elim fun y => ⟨⟨x, y⟩, rfl⟩

中文:
定理 fst_surjective
  条件: [h : Nonempty β]
  结论: Function.Surjective (@fst α β)
  证明: fun x => h.elim fun y => ⟨⟨x, y⟩, rfl⟩

Depends on / 依赖: h.elim
-/
theorem fst_surjective [h : Nonempty β] : Function.Surjective (@fst α β) :=
  fun x => h.elim fun y => ⟨⟨x, y⟩, rfl⟩

/--
theorem `snd_surjective` / 定理 `snd_surjective`

English:
theorem snd_surjective
  given: [h : Nonempty α]
  statement: Function.Surjective (@snd α β)
  proof: fun y => h.elim fun x => ⟨⟨x, y⟩, rfl⟩

中文:
定理 snd_surjective
  条件: [h : Nonempty α]
  结论: Function.Surjective (@snd α β)
  证明: fun y => h.elim fun x => ⟨⟨x, y⟩, rfl⟩

Depends on / 依赖: h.elim
-/
theorem snd_surjective [h : Nonempty α] : Function.Surjective (@snd α β) :=
  fun y => h.elim fun x => ⟨⟨x, y⟩, rfl⟩

/--
theorem `fst_injective` / 定理 `fst_injective`

English:
theorem fst_injective
  given: [Subsingleton β]
  statement: Function.Injective (@fst α β)
  proof: fun _ _ h => Prod.ext h (Subsingleton.elim _ _)

中文:
定理 fst_injective
  条件: [Subsingleton β]
  结论: Function.Injective (@fst α β)
  证明: fun _ _ h => Prod.ext h (Subsingleton.elim _ _)

Depends on / 依赖: Prod.ext, Subsingleton, Subsingleton.elim
-/
theorem fst_injective [Subsingleton β] : Function.Injective (@fst α β) :=
  fun _ _ h => Prod.ext h (Subsingleton.elim _ _)

/--
theorem `snd_injective` / 定理 `snd_injective`

English:
theorem snd_injective
  given: [Subsingleton α]
  statement: Function.Injective (@snd α β)
  proof: fun _ _ h => Prod.ext (Subsingleton.elim _ _) h

@[simp]

中文:
定理 snd_injective
  条件: [Subsingleton α]
  结论: Function.Injective (@snd α β)
  证明: fun _ _ h => Prod.ext (Subsingleton.elim _ _) h

@[simp]

Depends on / 依赖: Prod.ext, Subsingleton, Subsingleton.elim
-/
theorem snd_injective [Subsingleton α] : Function.Injective (@snd α β) :=
  fun _ _ h => Prod.ext (Subsingleton.elim _ _) h

@[simp]
/--
theorem `swap_leftInverse` / 定理 `swap_leftInverse`

English:
theorem swap_leftInverse
  statement: Function.LeftInverse (@swap α β) swap
  proof: swap_swap

@[simp]

中文:
定理 swap_leftInverse
  结论: Function.LeftInverse (@swap α β) swap
  证明: swap_swap

@[simp]

Depends on / 依赖: swap_swap
-/
theorem swap_leftInverse : Function.LeftInverse (@swap α β) swap :=
  swap_swap

@[simp]
/--
theorem `swap_rightInverse` / 定理 `swap_rightInverse`

English:
theorem swap_rightInverse
  statement: Function.RightInverse (@swap α β) swap
  proof: swap_swap

中文:
定理 swap_rightInverse
  结论: Function.RightInverse (@swap α β) swap
  证明: swap_swap

Depends on / 依赖: swap_swap
-/
theorem swap_rightInverse : Function.RightInverse (@swap α β) swap :=
  swap_swap

/--
theorem `swap_injective` / 定理 `swap_injective`

English:
theorem swap_injective
  statement: Function.Injective (@swap α β)
  proof: swap_leftInverse.injective

中文:
定理 swap_injective
  结论: Function.Injective (@swap α β)
  证明: swap_leftInverse.injective

Depends on / 依赖: injective, swap_leftInverse, swap_leftInverse.injective
-/
theorem swap_injective : Function.Injective (@swap α β) :=
  swap_leftInverse.injective

/--
theorem `swap_surjective` / 定理 `swap_surjective`

English:
theorem swap_surjective
  statement: Function.Surjective (@swap α β)
  proof: swap_leftInverse.surjective

中文:
定理 swap_surjective
  结论: Function.Surjective (@swap α β)
  证明: swap_leftInverse.surjective

Depends on / 依赖: surjective, swap_leftInverse, swap_leftInverse.surjective
-/
theorem swap_surjective : Function.Surjective (@swap α β) :=
  swap_leftInverse.surjective

/--
theorem `swap_bijective` / 定理 `swap_bijective`

English:
theorem swap_bijective
  statement: Function.Bijective (@swap α β)
  proof: ⟨swap_injective, swap_surjective⟩

中文:
定理 swap_bijective
  结论: Function.Bijective (@swap α β)
  证明: ⟨swap_injective, swap_surjective⟩

Depends on / 依赖: swap_injective, swap_surjective
-/
theorem swap_bijective : Function.Bijective (@swap α β) :=
  ⟨swap_injective, swap_surjective⟩

/--
theorem `_root_.Function.Semiconj.swap_map` / 定理 `_root_.Function.Semiconj.swap_map`

English:
theorem _root_.Function.Semiconj.swap_map
  given: (f : α -> α) (g : β -> β)
  proof: Function.semiconj_iff_comp_eq.2 (map_comp_swap g f).symm

中文:
定理 _root_.Function.Semiconj.swap_map
  条件: (f : α -> α) (g : β -> β)
  证明: Function.semiconj_iff_comp_eq.2 (map_comp_swap g f).symm

Depends on / 依赖: Function, Function.semiconj_iff_comp_eq, map_comp_swap, semiconj_iff_comp_eq
-/
theorem _root_.Function.Semiconj.swap_map (f : α -> α) (g : β -> β) :
    Function.Semiconj swap (map f g) (map g f) :=
  Function.semiconj_iff_comp_eq.2 (map_comp_swap g f).symm

/--
theorem `eq_iff_fst_eq_snd_eq` / 定理 `eq_iff_fst_eq_snd_eq`

English:
theorem eq_iff_fst_eq_snd_eq
  statement: forall {p q : α × β}, p = q ↔ p.1 = q.1 ∧ p.2 = q.2

中文:
定理 eq_iff_fst_eq_snd_eq
  结论: 对任意 {p q : α × β}, p = q ↔ p.1 = q.1 ∧ p.2 = q.2
-/
theorem eq_iff_fst_eq_snd_eq : forall {p q : α × β}, p = q ↔ p.1 = q.1 ∧ p.2 = q.2
  | ⟨p₁, p₂⟩, ⟨q₁, q₂⟩ => by simp

/--
theorem `fst_eq_iff` / 定理 `fst_eq_iff`

English:
theorem fst_eq_iff
  statement: forall {p : α × β} {x : α}, p.1 = x ↔ p = (x, p.2)

中文:
定理 fst_eq_iff
  结论: 对任意 {p : α × β} {x : α}, p.1 = x ↔ p = (x, p.2)
-/
theorem fst_eq_iff : forall {p : α × β} {x : α}, p.1 = x ↔ p = (x, p.2)
  | ⟨a, b⟩, x => by simp

/--
theorem `snd_eq_iff` / 定理 `snd_eq_iff`

English:
theorem snd_eq_iff
  statement: forall {p : α × β} {x : β}, p.2 = x ↔ p = (p.1, x)

中文:
定理 snd_eq_iff
  结论: 对任意 {p : α × β} {x : β}, p.2 = x ↔ p = (p.1, x)
-/
theorem snd_eq_iff : forall {p : α × β} {x : β}, p.2 = x ↔ p = (p.1, x)
  | ⟨a, b⟩, x => by simp

variable {r : α -> α -> Prop} {s : β -> β -> Prop} {x y : α × β}

/--
lemma `lex_iff` / 引理 `lex_iff`

English:
lemma lex_iff
  statement: Prod.Lex r s x y ↔ r x.1 y.1 ∨ x.1 = y.1 ∧ s x.2 y.2
  proof: lex_def

中文:
引理 lex_iff
  结论: Prod.Lex r s x y ↔ r x.1 y.1 ∨ x.1 = y.1 ∧ s x.2 y.2
  证明: lex_def

Depends on / 依赖: lex_def
-/
lemma lex_iff : Prod.Lex r s x y ↔ r x.1 y.1 ∨ x.1 = y.1 ∧ s x.2 y.2 := lex_def

/--
Instance `Lex.decidable` / 实例 `Lex.decidable`

English:
instance Lex.decidable
  signature: [DecidableEq α]
  body: fun _ _ => decidable_of_decidable_of_iff lex_def.symm

@[refl]

中文:
实例 Lex.decidable
  签名: [DecidableEq α]
  定义体: fun _ _ => decidable_of_decidable_of_iff lex_def.symm

@[refl]

Depends on / 依赖: decidable_of_decidable_of_iff, lex_def, lex_def.symm
-/
instance Lex.decidable [DecidableEq α]
    (r : α -> α -> Prop) (s : β -> β -> Prop) [DecidableRel r] [DecidableRel s] :
    DecidableRel (Prod.Lex r s) :=
  fun _ _ => decidable_of_decidable_of_iff lex_def.symm

@[refl]
/--
theorem `Lex.refl_left` / 定理 `Lex.refl_left`

English:
theorem Lex.refl_left
  given: (r : α -> α -> Prop) (s : β -> β -> Prop) [Std.Refl r]
  statement: forall x, Prod.Lex r s x x

中文:
定理 Lex.refl_left
  条件: (r : α -> α -> 命题) (s : β -> β -> 命题) [Std.Refl r]
  结论: 对任意 x, Prod.Lex r s x x
-/
theorem Lex.refl_left (r : α -> α -> Prop) (s : β -> β -> Prop) [Std.Refl r] : forall x, Prod.Lex r s x x
  | (_, _) => Lex.left _ _ (refl _)

instance {r : α -> α -> Prop} {s : β -> β -> Prop} [Std.Refl r] : Std.Refl (Prod.Lex r s) :=
  ⟨Lex.refl_left _ _⟩

@[refl]
/--
theorem `Lex.refl_right` / 定理 `Lex.refl_right`

English:
theorem Lex.refl_right
  given: (r : α -> α -> Prop) (s : β -> β -> Prop) [Std.Refl s]
  statement: forall x, Prod.Lex r s x x

中文:
定理 Lex.refl_right
  条件: (r : α -> α -> 命题) (s : β -> β -> 命题) [Std.Refl s]
  结论: 对任意 x, Prod.Lex r s x x
-/
theorem Lex.refl_right (r : α -> α -> Prop) (s : β -> β -> Prop) [Std.Refl s] : forall x, Prod.Lex r s x x
  | (_, _) => Lex.right _ (refl _)

instance {r : α -> α -> Prop} {s : β -> β -> Prop} [Std.Refl s] : Std.Refl (Prod.Lex r s) :=
  ⟨Lex.refl_right _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Irrefl
  signature: r] [Std.Irrefl s] : Std.Irrefl (Prod.Lex r s)
  body: ⟨by rintro ⟨i, a⟩ (⟨_, _, h⟩ | ⟨_, h⟩) <;> exact irrefl _ h⟩

中文:
实例 [Std.Irrefl
  签名: r] [Std.Irrefl s] : Std.Irrefl (Prod.Lex r s)
  定义体: ⟨by rintro ⟨i, a⟩ (⟨_, _, h⟩ | ⟨_, h⟩) <;> exact irrefl _ h⟩

Depends on / 依赖: irrefl
-/
instance [Std.Irrefl r] [Std.Irrefl s] : Std.Irrefl (Prod.Lex r s) :=
  ⟨by rintro ⟨i, a⟩ (⟨_, _, h⟩ | ⟨_, h⟩) <;> exact irrefl _ h⟩

set_option linter.style.whitespace false in -- manual alignment is not recognised
@[trans]
/--
theorem `Lex.trans` / 定理 `Lex.trans`

English:
theorem Lex.trans
  given: {r : α -> α -> Prop} {s : β -> β -> Prop} [IsTrans α r] [IsTrans β s]

中文:
定理 Lex.trans
  条件: {r : α -> α -> 命题} {s : β -> β -> 命题} [IsTrans α r] [IsTrans β s]
-/
theorem Lex.trans {r : α -> α -> Prop} {s : β -> β -> Prop} [IsTrans α r] [IsTrans β s] :
    forall {x y z : α × β}, Prod.Lex r s x y -> Prod.Lex r s y z -> Prod.Lex r s x z
  | (_, _), (_, _), (_, _), left _ _ hxy₁, left _ _ hyz₁ => left _ _ (_root_.trans hxy₁ hyz₁)
  | (_, _), (_, _), (_, _), left _ _ hxy₁, right _ _ => left _ _ hxy₁
  | (_, _), (_, _), (_, _), right _ _, left _ _ hyz₁ => left _ _ hyz₁
  | (_, _), (_, _), (_, _), right _ hxy₂, right _ hyz₂ => right _ (_root_.trans hxy₂ hyz₂)

instance {r : α -> α -> Prop} {s : β -> β -> Prop} [IsTrans α r] [IsTrans β s] :
    IsTrans (α × β) (Prod.Lex r s) :=
  ⟨fun _ _ _ => Lex.trans⟩

instance {r : α -> α -> Prop} {s : β -> β -> Prop} [IsStrictOrder α r] [Std.Antisymm s] :
    Std.Antisymm (Prod.Lex r s) :=
  ⟨fun x₁ x₂ h₁₂ h₂₁ =>
    match x₁, x₂, h₁₂, h₂₁ with
    | (a, _), (_, _), .left _ _ hr₁, .left _ _ hr₂ => (irrefl a (_root_.trans hr₁ hr₂)).elim
    | (_, _), (_, _), .left _ _ hr₁, .right _ _ => (irrefl _ hr₁).elim
    | (_, _), (_, _), .right _ _, .left _ _ hr₂ => (irrefl _ hr₂).elim
    | (_, _), (_, _), .right _ hs₁, .right _ hs₂ => antisymm hs₁ hs₂ ▸ rfl⟩

/--
Instance `total_left` / 实例 `total_left`

English:
instance total_left
  signature: {r : α -> α -> Prop} {s : β -> β -> Prop} [Std.Total r]
  body: ⟨fun ⟨a₁, _⟩ ⟨a₂, _⟩ => (Std.Total.total a₁ a₂).imp (Lex.left _ _) (Lex.left _ _)⟩

中文:
实例 total_left
  签名: {r : α -> α -> 命题} {s : β -> β -> 命题} [Std.Total r]
  定义体: ⟨fun ⟨a₁, _⟩ ⟨a₂, _⟩ => (Std.Total.total a₁ a₂).imp (Lex.left _ _) (Lex.left _ _)⟩

Depends on / 依赖: Lex.left, Std.Total.total
-/
instance total_left {r : α -> α -> Prop} {s : β -> β -> Prop} [Std.Total r] :
    Std.Total (Prod.Lex r s) :=
  ⟨fun ⟨a₁, _⟩ ⟨a₂, _⟩ => (Std.Total.total a₁ a₂).imp (Lex.left _ _) (Lex.left _ _)⟩

/--
Instance `total_right` / 实例 `total_right`

English:
instance total_right
  signature: {r : α -> α -> Prop} {s : β -> β -> Prop} [Std.Trichotomous r] [Std.Total s]
  body: ⟨fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (.left _ _ hij)
    · exact (total_of s a b).imp (.right _) (.right _)
    · exact Or.inr (.left _ _ hji) ⟩

中文:
实例 total_right
  签名: {r : α -> α -> 命题} {s : β -> β -> 命题} [Std.Trichotomous r] [Std.Total s]
  定义体: ⟨fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (.left _ _ hij)
    · exact (total_of s a b).imp (.right _) (.right _)
    · exact Or.inr (.left _ _ hji) ⟩

Depends on / 依赖: Or.inl, Or.inr, total_of, trichotomous_of
-/
instance total_right {r : α -> α -> Prop} {s : β -> β -> Prop} [Std.Trichotomous r] [Std.Total s] :
    Std.Total (Prod.Lex r s) :=
  ⟨fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (.left _ _ hij)
    · exact (total_of s a b).imp (.right _) (.right _)
    · exact Or.inr (.left _ _ hji) ⟩

/--
Instance `trichotomous` / 实例 `trichotomous`

English:
instance trichotomous
  signature: [Std.Trichotomous r] [Std.Trichotomous s]
  body: Std.trichotomous_of_rel_or_eq_or_rel_swap by
    intro ⟨i, a⟩ ⟨j, b⟩
    obtain hij | rfl | hji := trichotomous_of r i j
    { exact Or.inl (Lex.left _ _ hij) }
    { exact (trichotomous_of (s) a b).imp3 (Lex.right _) (congr_arg _) (Lex.right _) }
    { exact Or.inr (Or.inr <| Lex.left _ _ hji) }

中文:
实例 trichotomous
  签名: [Std.Trichotomous r] [Std.Trichotomous s]
  定义体: Std.trichotomous_of_rel_or_eq_or_rel_swap by
    intro ⟨i, a⟩ ⟨j, b⟩
    obtain hij | rfl | hji := trichotomous_of r i j
    { exact Or.inl (Lex.left _ _ hij) }
    { exact (trichotomous_of (s) a b).imp3 (Lex.right _) (congr_arg _) (Lex.right _) }
    { exact Or.inr (Or.inr <| Lex.left _ _ hji) }

Depends on / 依赖: Lex.left, Lex.right, Or.inl, Or.inr, Std.trichotomous_of_rel_or_eq_or_rel_swap, congr_arg, trichotomous_of, trichotomous_of_rel_or_eq_or_rel_swap
-/
instance trichotomous [Std.Trichotomous r] [Std.Trichotomous s] :
    Std.Trichotomous (Prod.Lex r s) :=
Std.trichotomous_of_rel_or_eq_or_rel_swap by
    intro ⟨i, a⟩ ⟨j, b⟩
    obtain hij | rfl | hji := trichotomous_of r i j
    { exact Or.inl (Lex.left _ _ hij) }
    { exact (trichotomous_of (s) a b).imp3 (Lex.right _) (congr_arg _) (Lex.right _) }
    { exact Or.inr (Or.inr <| Lex.left _ _ hji) }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Asymm
  signature: r] [Std.Asymm s] :

中文:
实例 [Std.Asymm
  签名: r] [Std.Asymm s] :
-/
instance [Std.Asymm r] [Std.Asymm s] :
    Std.Asymm (Prod.Lex r s) where
  asymm
  | (_a₁, _a₂), (_b₁, _b₂), .left _ _ h₁, .left _ _ h₂ => Std.Asymm.asymm _ _ h₂ h₁
  | (_a₁, _a₂), (_, _b₂), .left _ _ h₁, .right _ _ => Std.Asymm.asymm _ _ h₁ h₁
  | (_a₁, _a₂), (_, _b₂), .right _ _, .left _ _ h₂ => Std.Asymm.asymm _ _ h₂ h₂
  | (_a₁, _a₂), (_, _b₂), .right _ h₁, .right _ h₂ => Std.Asymm.asymm _ _ h₁ h₂

end Prod

open Prod

namespace Function

variable {f : α -> γ} {g : β -> δ} {f₁ : α -> β} {g₁ : γ -> δ} {f₂ : β -> α} {g₂ : δ -> γ}

/--
theorem `Injective.prodMap` / 定理 `Injective.prodMap`

English:
theorem Injective.prodMap
  given: (hf : Injective f) (hg : Injective g)
  statement: Injective (map f g)
  proof: fun _ _ h => Prod.ext (hf <| congr_arg Prod.fst h) (hg <| congr_arg Prod.snd h)

中文:
定理 Injective.prodMap
  条件: (hf : Injective f) (hg : Injective g)
  结论: Injective (map f g)
  证明: fun _ _ h => Prod.ext (hf <| congr_arg Prod.fst h) (hg <| congr_arg Prod.snd h)

Depends on / 依赖: Prod.ext, Prod.fst, Prod.snd, congr_arg
-/
theorem Injective.prodMap (hf : Injective f) (hg : Injective g) : Injective (map f g) :=
  fun _ _ h => Prod.ext (hf <| congr_arg Prod.fst h) (hg <| congr_arg Prod.snd h)

/--
theorem `Surjective.prodMap` / 定理 `Surjective.prodMap`

English:
theorem Surjective.prodMap
  given: (hf : Surjective f) (hg : Surjective g)
  statement: Surjective (map f g)
  proof: fun p =>
  let ⟨x, hx⟩ := hf p.1
  let ⟨y, hy⟩ := hg p.2
  ⟨(x, y), Prod.ext hx hy⟩

中文:
定理 Surjective.prodMap
  条件: (hf : Surjective f) (hg : Surjective g)
  结论: Surjective (map f g)
  证明: fun p =>
  let ⟨x, hx⟩ := hf p.1
  let ⟨y, hy⟩ := hg p.2
  ⟨(x, y), Prod.ext hx hy⟩

Depends on / 依赖: Prod.ext
-/
theorem Surjective.prodMap (hf : Surjective f) (hg : Surjective g) : Surjective (map f g) :=
  fun p =>
  let ⟨x, hx⟩ := hf p.1
  let ⟨y, hy⟩ := hg p.2
  ⟨(x, y), Prod.ext hx hy⟩

/--
theorem `Bijective.prodMap` / 定理 `Bijective.prodMap`

English:
theorem Bijective.prodMap
  given: (hf : Bijective f) (hg : Bijective g)
  statement: Bijective (map f g)
  proof: ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2⟩

中文:
定理 Bijective.prodMap
  条件: (hf : Bijective f) (hg : Bijective g)
  结论: Bijective (map f g)
  证明: ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2⟩

Depends on / 依赖: prodMap
-/
theorem Bijective.prodMap (hf : Bijective f) (hg : Bijective g) : Bijective (map f g) :=
  ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2⟩

/--
theorem `LeftInverse.prodMap` / 定理 `LeftInverse.prodMap`

English:
theorem LeftInverse.prodMap
  given: (hf : LeftInverse f₁ f₂) (hg : LeftInverse g₁ g₂)
  proof: fun a => by rw [Prod.map_map, hf.comp_eq_id, hg.comp_eq_id, map_id, id]

中文:
定理 LeftInverse.prodMap
  条件: (hf : LeftInverse f₁ f₂) (hg : LeftInverse g₁ g₂)
  证明: fun a => by rw [Prod.map_map, hf.comp_eq_id, hg.comp_eq_id, map_id, id]

Depends on / 依赖: Prod.map_map, comp_eq_id, hf.comp_eq_id, hg.comp_eq_id, map_id, map_map
-/
theorem LeftInverse.prodMap (hf : LeftInverse f₁ f₂) (hg : LeftInverse g₁ g₂) :
    LeftInverse (map f₁ g₁) (map f₂ g₂) :=
  fun a => by rw [Prod.map_map, hf.comp_eq_id, hg.comp_eq_id, map_id, id]

/--
theorem `RightInverse.prodMap` / 定理 `RightInverse.prodMap`

English:
theorem RightInverse.prodMap
  proof: LeftInverse.prodMap

中文:
定理 RightInverse.prodMap
  证明: LeftInverse.prodMap

Depends on / 依赖: LeftInverse, LeftInverse.prodMap, prodMap
-/
theorem RightInverse.prodMap :
    RightInverse f₁ f₂ -> RightInverse g₁ g₂ -> RightInverse (map f₁ g₁) (map f₂ g₂) :=
  LeftInverse.prodMap

/--
theorem `Involutive.prodMap` / 定理 `Involutive.prodMap`

English:
theorem Involutive.prodMap
  given: {f : α -> α} {g : β -> β}
  proof: LeftInverse.prodMap

中文:
定理 Involutive.prodMap
  条件: {f : α -> α} {g : β -> β}
  证明: LeftInverse.prodMap

Depends on / 依赖: LeftInverse, LeftInverse.prodMap, prodMap
-/
theorem Involutive.prodMap {f : α -> α} {g : β -> β} :
    Involutive f -> Involutive g -> Involutive (map f g) :=
  LeftInverse.prodMap

end Function

namespace Prod

open Function

@[simp]
/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: [Nonempty α] [Nonempty β] {f : α -> γ} {g : β -> δ}
  proof: ⟨fun h =>
    ⟨fun a₁ a₂ ha => by
      inhabit β
      injection
        @h (a₁, default) (a₂, default) (congr_arg (fun c : γ => Prod.mk c (g default)) ha :),
      fun b₁ b₂ hb => by
      inhabit α
      injection @h (default, b₁) (default, b₂) (congr_arg (Prod.mk (f default)) hb :)⟩,
    fun h =

中文:
定理 map_injective
  条件: [Nonempty α] [Nonempty β] {f : α -> γ} {g : β -> δ}
  证明: ⟨fun h =>
    ⟨fun a₁ a₂ ha => by
      inhabit β
      injection
        @h (a₁, default) (a₂, default) (congr_arg (fun c : γ => Prod.mk c (g default)) ha :),
      fun b₁ b₂ hb => by
      inhabit α
      injection @h (default, b₁) (default, b₂) (congr_arg (Prod.mk (f default)) hb :)⟩,
    fun h =

Depends on / 依赖: Prod.mk, congr_arg, inhabit, injection, prodMap
-/
theorem map_injective [Nonempty α] [Nonempty β] {f : α -> γ} {g : β -> δ} :
    Injective (map f g) ↔ Injective f ∧ Injective g :=
  ⟨fun h =>
    ⟨fun a₁ a₂ ha => by
      inhabit β
      injection
        @h (a₁, default) (a₂, default) (congr_arg (fun c : γ => Prod.mk c (g default)) ha :),
      fun b₁ b₂ hb => by
      inhabit α
      injection @h (default, b₁) (default, b₂) (congr_arg (Prod.mk (f default)) hb :)⟩,
    fun h => h.1.prodMap h.2⟩

@[simp]
/--
theorem `map_surjective` / 定理 `map_surjective`

English:
theorem map_surjective
  given: [Nonempty γ] [Nonempty δ] {f : α -> γ} {g : β -> δ}
  proof: ⟨fun h =>
    ⟨fun c => by
      inhabit δ
      obtain ⟨⟨a, b⟩, h⟩ := h (c, default)
      exact ⟨a, congr_arg Prod.fst h⟩,
      fun d => by
      inhabit γ
      obtain ⟨⟨a, b⟩, h⟩ := h (default, d)
      exact ⟨b, congr_arg Prod.snd h⟩⟩,
    fun h => h.1.prodMap h.2⟩

@[simp]

中文:
定理 map_surjective
  条件: [Nonempty γ] [Nonempty δ] {f : α -> γ} {g : β -> δ}
  证明: ⟨fun h =>
    ⟨fun c => by
      inhabit δ
      obtain ⟨⟨a, b⟩, h⟩ := h (c, default)
      exact ⟨a, congr_arg Prod.fst h⟩,
      fun d => by
      inhabit γ
      obtain ⟨⟨a, b⟩, h⟩ := h (default, d)
      exact ⟨b, congr_arg Prod.snd h⟩⟩,
    fun h => h.1.prodMap h.2⟩

@[simp]

Depends on / 依赖: Prod.fst, Prod.snd, congr_arg, inhabit, prodMap
-/
theorem map_surjective [Nonempty γ] [Nonempty δ] {f : α -> γ} {g : β -> δ} :
    Surjective (map f g) ↔ Surjective f ∧ Surjective g :=
  ⟨fun h =>
    ⟨fun c => by
      inhabit δ
      obtain ⟨⟨a, b⟩, h⟩ := h (c, default)
      exact ⟨a, congr_arg Prod.fst h⟩,
      fun d => by
      inhabit γ
      obtain ⟨⟨a, b⟩, h⟩ := h (default, d)
      exact ⟨b, congr_arg Prod.snd h⟩⟩,
    fun h => h.1.prodMap h.2⟩

@[simp]
/--
theorem `map_bijective` / 定理 `map_bijective`

English:
theorem map_bijective
  given: [Nonempty α] [Nonempty β] {f : α -> γ} {g : β -> δ}
  proof: by
  have := Nonempty.map f ‹_›
  have := Nonempty.map g ‹_›
  exact (map_injective.and map_surjective).trans and_and_and_comm

@[simp]

中文:
定理 map_bijective
  条件: [Nonempty α] [Nonempty β] {f : α -> γ} {g : β -> δ}
  证明: by
  have := Nonempty.map f ‹_›
  have := Nonempty.map g ‹_›
  exact (map_injective.and map_surjective).trans and_and_and_comm

@[simp]

Depends on / 依赖: Nonempty, Nonempty.map, and_and_and_comm, map_injective, map_injective.and, map_surjective
-/
theorem map_bijective [Nonempty α] [Nonempty β] {f : α -> γ} {g : β -> δ} :
    Bijective (map f g) ↔ Bijective f ∧ Bijective g := by
  have := Nonempty.map f ‹_›
  have := Nonempty.map g ‹_›
  exact (map_injective.and map_surjective).trans and_and_and_comm

@[simp]
/--
theorem `map_leftInverse` / 定理 `map_leftInverse`

English:
theorem map_leftInverse
  statement: [Nonempty β] [Nonempty δ] {f₁ : α -> β} {g₁ : γ -> δ} {f₂ : β -> α}
  proof: ⟨fun h =>
    ⟨fun b => by
      inhabit δ
      exact congr_arg Prod.fst (h (b, default)),
      fun d => by
      inhabit β
      exact congr_arg Prod.snd (h (default, d))⟩,
    fun h => h.1.prodMap h.2 ⟩

@[simp]

中文:
定理 map_leftInverse
  结论: [Nonempty β] [Nonempty δ] {f₁ : α -> β} {g₁ : γ -> δ} {f₂ : β -> α}
  证明: ⟨fun h =>
    ⟨fun b => by
      inhabit δ
      exact congr_arg Prod.fst (h (b, default)),
      fun d => by
      inhabit β
      exact congr_arg Prod.snd (h (default, d))⟩,
    fun h => h.1.prodMap h.2 ⟩

@[simp]

Depends on / 依赖: Prod.fst, Prod.snd, congr_arg, inhabit, prodMap
-/
theorem map_leftInverse [Nonempty β] [Nonempty δ] {f₁ : α -> β} {g₁ : γ -> δ} {f₂ : β -> α}
    {g₂ : δ -> γ} : LeftInverse (map f₁ g₁) (map f₂ g₂) ↔ LeftInverse f₁ f₂ ∧ LeftInverse g₁ g₂ :=
  ⟨fun h =>
    ⟨fun b => by
      inhabit δ
      exact congr_arg Prod.fst (h (b, default)),
      fun d => by
      inhabit β
      exact congr_arg Prod.snd (h (default, d))⟩,
    fun h => h.1.prodMap h.2 ⟩

@[simp]
/--
theorem `map_rightInverse` / 定理 `map_rightInverse`

English:
theorem map_rightInverse
  statement: [Nonempty α] [Nonempty γ] {f₁ : α -> β} {g₁ : γ -> δ} {f₂ : β -> α}
  proof: map_leftInverse

@[simp]

中文:
定理 map_rightInverse
  结论: [Nonempty α] [Nonempty γ] {f₁ : α -> β} {g₁ : γ -> δ} {f₂ : β -> α}
  证明: map_leftInverse

@[simp]

Depends on / 依赖: map_leftInverse
-/
theorem map_rightInverse [Nonempty α] [Nonempty γ] {f₁ : α -> β} {g₁ : γ -> δ} {f₂ : β -> α}
    {g₂ : δ -> γ} : RightInverse (map f₁ g₁) (map f₂ g₂) ↔ RightInverse f₁ f₂ ∧ RightInverse g₁ g₂ :=
  map_leftInverse

@[simp]
/--
theorem `map_involutive` / 定理 `map_involutive`

English:
theorem map_involutive
  given: [Nonempty α] [Nonempty β] {f : α -> α} {g : β -> β}
  proof: map_leftInverse

中文:
定理 map_involutive
  条件: [Nonempty α] [Nonempty β] {f : α -> α} {g : β -> β}
  证明: map_leftInverse

Depends on / 依赖: map_leftInverse
-/
theorem map_involutive [Nonempty α] [Nonempty β] {f : α -> α} {g : β -> β} :
    Involutive (map f g) ↔ Involutive f ∧ Involutive g :=
  map_leftInverse

namespace PrettyPrinting
open Lean PrettyPrinter Delaborator

/--
When true, then `Prod.fst x` and `Prod.snd x` pretty print as `x.1` and `x.2`
rather than as `x.fst` and `x.snd`.
-/
meta register_option pp.numericProj.prod : Bool := {
  defValue := true
  descr := "enable pretty printing `Prod.fst x` as `x.1` and `Prod.snd x` as `x.2`."
}

/-- Tell whether pretty-printing should use numeric projection notations `.1`
and `.2` for `Prod.fst` and `Prod.snd`. -/
meta def getPPNumericProjProd (o : Options) : Bool :=
  o.get pp.numericProj.prod.name pp.numericProj.prod.defValue

/-- Delaborator for `Prod.fst x` as `x.1`. -/
@[app_delab Prod.fst]
meta def delabProdFst : Delab :=
whenPPOption getPPNumericProjProd
whenPPOption getPPFieldNotation
whenNotPPOption getPPExplicit
  withOverApp 3 do
    let x ← SubExpr.withAppArg delab
    `($(x).1)

/-- Delaborator for `Prod.snd x` as `x.2`. -/
@[app_delab Prod.snd]
meta def delabProdSnd : Delab :=
whenPPOption getPPNumericProjProd
whenPPOption getPPFieldNotation
whenNotPPOption getPPExplicit
  withOverApp 3 do
    let x ← SubExpr.withAppArg delab
    `($(x).2)

end PrettyPrinting

end Prod
