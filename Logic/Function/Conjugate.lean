/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Logic.Function.Basic

/-!
# Semiconjugate and commuting maps

We define the following predicates:

* `Function.Semiconj`: `f : α → β` semiconjugates `ga : α → α` to `gb : β → β` if `f ∘ ga = gb ∘ f`;
* `Function.Semiconj₂`: `f : α → β` semiconjugates a binary operation `ga : α → α → α`
  to `gb : β → β → β` if `f (ga x y) = gb (f x) (f y)`;
* `Function.Commute`: `f : α → α` commutes with `g : α → α` if `f ∘ g = g ∘ f`,
  or equivalently `Semiconj f g g`.
-/

@[expose] public section

namespace Function

variable {α : Type*} {β : Type*} {γ : Type*}

/--
Definition of `Semiconj` / `Semiconj` 的定义

English:
definition Semiconj
  signature: (f : α -> β) (ga : α -> α) (gb : β -> β)
  body: forall x, f (ga x) = gb (f x)

中文:
定义 Semiconj
  签名: (f : α -> β) (ga : α -> α) (gb : β -> β)
  定义体: forall x, f (ga x) = gb (f x)
-/
def Semiconj (f : α -> β) (ga : α -> α) (gb : β -> β) : Prop :=
  forall x, f (ga x) = gb (f x)

namespace Semiconj

variable {f fab : α -> β} {fbc : β -> γ} {ga ga' : α -> α} {gb gb' : β -> β} {gc : γ -> γ}

/--
lemma `_root_.Function.semiconj_iff_comp_eq` / 引理 `_root_.Function.semiconj_iff_comp_eq`

English:
lemma _root_.Function.semiconj_iff_comp_eq
  statement: Semiconj f ga gb ↔ f ∘ ga = gb ∘ f
  proof: funext_iff.symm

protected alias ⟨comp_eq, _⟩ := semiconj_iff_comp_eq

中文:
引理 _root_.Function.semiconj_iff_comp_eq
  结论: Semiconj f ga gb ↔ f ∘ ga = gb ∘ f
  证明: funext_iff.symm

protected alias ⟨comp_eq, _⟩ := semiconj_iff_comp_eq

Depends on / 依赖: funext_iff, funext_iff.symm
-/
lemma _root_.Function.semiconj_iff_comp_eq : Semiconj f ga gb ↔ f ∘ ga = gb ∘ f := funext_iff.symm

protected alias ⟨comp_eq, _⟩ := semiconj_iff_comp_eq

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: (h : Semiconj f ga gb) (x : α)
  statement: f (ga x) = gb (f x)
  proof: h x

中文:
定理 eq
  条件: (h : Semiconj f ga gb) (x : α)
  结论: f (ga x) = gb (f x)
  证明: h x
-/
protected theorem eq (h : Semiconj f ga gb) (x : α) : f (ga x) = gb (f x) :=
  h x

/--
theorem `comp_right` / 定理 `comp_right`

English:
theorem comp_right
  given: (h : Semiconj f ga gb) (h' : Semiconj f ga' gb')
  proof: fun x => by
  simp only [comp_apply, h.eq, h'.eq]

中文:
定理 comp_right
  条件: (h : Semiconj f ga gb) (h' : Semiconj f ga' gb')
  证明: fun x => by
  simp only [comp_apply, h.eq, h'.eq]

Depends on / 依赖: comp_apply, h.eq
-/
theorem comp_right (h : Semiconj f ga gb) (h' : Semiconj f ga' gb') :
    Semiconj f (ga ∘ ga') (gb ∘ gb') := fun x => by
  simp only [comp_apply, h.eq, h'.eq]

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: (hab : Semiconj fab ga gb) (hbc : Semiconj fbc gb gc)
  proof: fun x => by
  simp only [comp_apply, hab.eq, hbc.eq]

中文:
定理 trans
  条件: (hab : Semiconj fab ga gb) (hbc : Semiconj fbc gb gc)
  证明: fun x => by
  simp only [comp_apply, hab.eq, hbc.eq]
-/
protected theorem trans (hab : Semiconj fab ga gb) (hbc : Semiconj fbc gb gc) :
    Semiconj (fbc ∘ fab) ga gc := fun x => by
  simp only [comp_apply, hab.eq, hbc.eq]

/--
theorem `comp_left` / 定理 `comp_left`

English:
theorem comp_left
  given: (hbc : Semiconj fbc gb gc) (hab : Semiconj fab ga gb)
  proof: hab.trans hbc

中文:
定理 comp_left
  条件: (hbc : Semiconj fbc gb gc) (hab : Semiconj fab ga gb)
  证明: hab.trans hbc

Depends on / 依赖: hab.trans
-/
theorem comp_left (hbc : Semiconj fbc gb gc) (hab : Semiconj fab ga gb) :
    Semiconj (fbc ∘ fab) ga gc :=
  hab.trans hbc

/--
theorem `id_right` / 定理 `id_right`

English:
theorem id_right
  statement: Semiconj f id id
  proof: fun _ => rfl

中文:
定理 id_right
  结论: Semiconj f id id
  证明: fun _ => rfl
-/
theorem id_right : Semiconj f id id := fun _ => rfl

/--
theorem `id_left` / 定理 `id_left`

English:
theorem id_left
  statement: Semiconj id ga ga
  proof: fun _ => rfl

中文:
定理 id_left
  结论: Semiconj id ga ga
  证明: fun _ => rfl
-/
theorem id_left : Semiconj id ga ga := fun _ => rfl

/--
theorem `inverses_right` / 定理 `inverses_right`

English:
theorem inverses_right
  given: (h : Semiconj f ga gb) (ha : RightInverse ga' ga) (hb : LeftInverse gb' gb)
  proof: fun x => by
  rw [← hb (f (ga' x))]; rw [← h.eq]; rw [ha x]

中文:
定理 inverses_right
  条件: (h : Semiconj f ga gb) (ha : RightInverse ga' ga) (hb : LeftInverse gb' gb)
  证明: fun x => by
  rw [← hb (f (ga' x))]; rw [← h.eq]; rw [ha x]

Depends on / 依赖: h.eq
-/
theorem inverses_right (h : Semiconj f ga gb) (ha : RightInverse ga' ga) (hb : LeftInverse gb' gb) :
    Semiconj f ga' gb' := fun x => by
  rw [← hb (f (ga' x))]; rw [← h.eq]; rw [ha x]

/--
lemma `inverse_left` / 引理 `inverse_left`

English:
lemma inverse_left
  statement: {f' : β -> α} (h : Semiconj f ga gb)
  proof: fun x => by
  rw [← hf₁.injective.eq_iff]; rw [h]; rw [hf₂]; rw [hf₂]

中文:
引理 inverse_left
  结论: {f' : β -> α} (h : Semiconj f ga gb)
  证明: fun x => by
  rw [← hf₁.injective.eq_iff]; rw [h]; rw [hf₂]; rw [hf₂]

Depends on / 依赖: eq_iff, injective, injective.eq_iff
-/
lemma inverse_left {f' : β -> α} (h : Semiconj f ga gb)
    (hf₁ : LeftInverse f' f) (hf₂ : RightInverse f' f) : Semiconj f' gb ga := fun x => by
  rw [← hf₁.injective.eq_iff]; rw [h]; rw [hf₂]; rw [hf₂]

/--
theorem `option_map` / 定理 `option_map`

English:
theorem option_map
  given: {f : α -> β} {ga : α -> α} {gb : β -> β} (h : Semiconj f ga gb)

中文:
定理 option_map
  条件: {f : α -> β} {ga : α -> α} {gb : β -> β} (h : Semiconj f ga gb)
-/
theorem option_map {f : α -> β} {ga : α -> α} {gb : β -> β} (h : Semiconj f ga gb) :
    Semiconj (Option.map f) (Option.map ga) (Option.map gb)
  | none => rfl
| some _ => congr_arg some h _

end Semiconj

/--
Definition of `Commute` / `Commute` 的定义

English:
definition Commute
  signature: (f g : α -> α)
  body: Semiconj f g g

中文:
定义 Commute
  签名: (f g : α -> α)
  定义体: Semiconj f g g
-/
protected def Commute (f g : α -> α) : Prop :=
  Semiconj f g g

open Function (Commute)

/--
theorem `Semiconj.commute` / 定理 `Semiconj.commute`

English:
theorem Semiconj.commute
  given: {f g : α -> α} (h : Semiconj f g g)
  statement: Commute f g
  proof: h

中文:
定理 Semiconj.commute
  条件: {f g : α -> α} (h : Semiconj f g g)
  结论: Commute f g
  证明: h
-/
theorem Semiconj.commute {f g : α -> α} (h : Semiconj f g g) : Commute f g := h

namespace Commute

variable {f f' g g' : α -> α}

/--
theorem `semiconj` / 定理 `semiconj`

English:
theorem semiconj
  given: (h : Commute f g)
  statement: Semiconj f g g
  proof: h

@[refl]

中文:
定理 semiconj
  条件: (h : Commute f g)
  结论: Semiconj f g g
  证明: h

@[refl]
-/
theorem semiconj (h : Commute f g) : Semiconj f g g := h

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (f : α -> α)
  statement: Commute f f
  proof: fun _ => Eq.refl _

@[symm]

中文:
定理 refl
  条件: (f : α -> α)
  结论: Commute f f
  证明: fun _ => Eq.refl _

@[symm]

Depends on / 依赖: Eq.refl
-/
theorem refl (f : α -> α) : Commute f f := fun _ => Eq.refl _

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : Commute f g)
  statement: Commute g f
  proof: fun x => (h x).symm

中文:
定理 symm
  条件: (h : Commute f g)
  结论: Commute g f
  证明: fun x => (h x).symm
-/
theorem symm (h : Commute f g) : Commute g f := fun x => (h x).symm

/--
theorem `comp_right` / 定理 `comp_right`

English:
theorem comp_right
  given: (h : Commute f g) (h' : Commute f g')
  statement: Commute f (g ∘ g')
  proof: Semiconj.comp_right h h'

中文:
定理 comp_right
  条件: (h : Commute f g) (h' : Commute f g')
  结论: Commute f (g ∘ g')
  证明: Semiconj.comp_right h h'

Depends on / 依赖: Semiconj, Semiconj.comp_right, comp_right
-/
theorem comp_right (h : Commute f g) (h' : Commute f g') : Commute f (g ∘ g') :=
  Semiconj.comp_right h h'

/-- If `f` and `f'` commute with `g`, then `f ∘ f'` commutes with `g` as well. -/
nonrec theorem comp_left (h : Commute f g) (h' : Commute f' g) : Commute (f ∘ f') g :=
  h.comp_left h'

/--
theorem `id_right` / 定理 `id_right`

English:
theorem id_right
  statement: Commute f id
  proof: Semiconj.id_right

中文:
定理 id_right
  结论: Commute f id
  证明: Semiconj.id_right

Depends on / 依赖: Semiconj, Semiconj.id_right, id_right
-/
theorem id_right : Commute f id := Semiconj.id_right

/--
theorem `id_left` / 定理 `id_left`

English:
theorem id_left
  statement: Commute id f
  proof: Semiconj.id_left

中文:
定理 id_left
  结论: Commute id f
  证明: Semiconj.id_left

Depends on / 依赖: Semiconj, Semiconj.id_left, id_left
-/
theorem id_left : Commute id f :=
  Semiconj.id_left

/-- If `f` commutes with `g`, then `Option.map f` commutes with `Option.map g`. -/
nonrec theorem option_map {f g : α -> α} (h : Commute f g) : Commute (Option.map f) (Option.map g) :=
  h.option_map

end Commute

/--
Definition of `Semiconj₂` / `Semiconj₂` 的定义

English:
definition Semiconj₂
  signature: (f : α -> β) (ga : α -> α -> α) (gb : β -> β -> β)
  body: forall x y, f (ga x y) = gb (f x) (f y)

中文:
定义 Semiconj₂
  签名: (f : α -> β) (ga : α -> α -> α) (gb : β -> β -> β)
  定义体: forall x y, f (ga x y) = gb (f x) (f y)
-/
def Semiconj₂ (f : α -> β) (ga : α -> α -> α) (gb : β -> β -> β) : Prop :=
  forall x y, f (ga x y) = gb (f x) (f y)

namespace Semiconj₂

variable {f : α -> β} {ga : α -> α -> α} {gb : β -> β -> β}

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: (h : Semiconj₂ f ga gb) (x y : α)
  statement: f (ga x y) = gb (f x) (f y)
  proof: h x y

中文:
定理 eq
  条件: (h : Semiconj₂ f ga gb) (x y : α)
  结论: f (ga x y) = gb (f x) (f y)
  证明: h x y
-/
protected theorem eq (h : Semiconj₂ f ga gb) (x y : α) : f (ga x y) = gb (f x) (f y) :=
  h x y

/--
theorem `comp_eq` / 定理 `comp_eq`

English:
theorem comp_eq
  given: (h : Semiconj₂ f ga gb)
  statement: bicompr f ga = bicompl gb f f
  proof: funext fun x => funext h x

中文:
定理 comp_eq
  条件: (h : Semiconj₂ f ga gb)
  结论: bicompr f ga = bicompl gb f f
  证明: funext fun x => funext h x
-/
protected theorem comp_eq (h : Semiconj₂ f ga gb) : bicompr f ga = bicompl gb f f :=
funext fun x => funext h x

/--
theorem `id_left` / 定理 `id_left`

English:
theorem id_left
  given: (op : α -> α -> α)
  statement: Semiconj₂ id op op
  proof: fun _ _ => rfl

中文:
定理 id_left
  条件: (op : α -> α -> α)
  结论: Semiconj₂ id op op
  证明: fun _ _ => rfl
-/
theorem id_left (op : α -> α -> α) : Semiconj₂ id op op := fun _ _ => rfl

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {f' : β -> γ} {gc : γ -> γ -> γ} (hf' : Semiconj₂ f' gb gc) (hf : Semiconj₂ f ga gb)
  proof: fun x y => by simp only [hf'.eq, hf.eq, comp_apply]

中文:
定理 comp
  条件: {f' : β -> γ} {gc : γ -> γ -> γ} (hf' : Semiconj₂ f' gb gc) (hf : Semiconj₂ f ga gb)
  证明: fun x y => by simp only [hf'.eq, hf.eq, comp_apply]

Depends on / 依赖: comp_apply, hf.eq
-/
theorem comp {f' : β -> γ} {gc : γ -> γ -> γ} (hf' : Semiconj₂ f' gb gc) (hf : Semiconj₂ f ga gb) :
    Semiconj₂ (f' ∘ f) ga gc := fun x y => by simp only [hf'.eq, hf.eq, comp_apply]

/--
theorem `isAssociative_right` / 定理 `isAssociative_right`

English:
theorem isAssociative_right
  given: [Std.Associative ga] (h : Semiconj₂ f ga gb) (h_surj : Surjective f)
  proof: ⟨h_surj.forall₃.2 fun x₁ x₂ x₃ => by simp only [← h.eq, Std.Associative.assoc (op := ga)]⟩

中文:
定理 isAssociative_right
  条件: [Std.Associative ga] (h : Semiconj₂ f ga gb) (h_surj : Surjective f)
  证明: ⟨h_surj.forall₃.2 fun x₁ x₂ x₃ => by simp only [← h.eq, Std.Associative.assoc (op := ga)]⟩

Depends on / 依赖: Associative, Std.Associative.assoc, h.eq, h_surj, h_surj.forall
-/
theorem isAssociative_right [Std.Associative ga] (h : Semiconj₂ f ga gb) (h_surj : Surjective f) :
    Std.Associative gb :=
  ⟨h_surj.forall₃.2 fun x₁ x₂ x₃ => by simp only [← h.eq, Std.Associative.assoc (op := ga)]⟩

/--
theorem `isAssociative_left` / 定理 `isAssociative_left`

English:
theorem isAssociative_left
  given: [Std.Associative gb] (h : Semiconj₂ f ga gb) (h_inj : Injective f)
  proof: ⟨fun x₁ x₂ x₃ => h_inj by simp only [h.eq, Std.Associative.assoc (op := gb)]⟩

中文:
定理 isAssociative_left
  条件: [Std.Associative gb] (h : Semiconj₂ f ga gb) (h_inj : Injective f)
  证明: ⟨fun x₁ x₂ x₃ => h_inj by simp only [h.eq, Std.Associative.assoc (op := gb)]⟩

Depends on / 依赖: Associative, Std.Associative.assoc, h.eq, h_inj
-/
theorem isAssociative_left [Std.Associative gb] (h : Semiconj₂ f ga gb) (h_inj : Injective f) :
    Std.Associative ga :=
⟨fun x₁ x₂ x₃ => h_inj by simp only [h.eq, Std.Associative.assoc (op := gb)]⟩

/--
theorem `isIdempotent_right` / 定理 `isIdempotent_right`

English:
theorem isIdempotent_right
  given: [Std.IdempotentOp ga] (h : Semiconj₂ f ga gb) (h_surj : Surjective f)
  proof: ⟨h_surj.forall.2 fun x => by simp only [← h.eq, Std.IdempotentOp.idempotent (op := ga)]⟩

中文:
定理 isIdempotent_right
  条件: [Std.IdempotentOp ga] (h : Semiconj₂ f ga gb) (h_surj : Surjective f)
  证明: ⟨h_surj.forall.2 fun x => by simp only [← h.eq, Std.IdempotentOp.idempotent (op := ga)]⟩

Depends on / 依赖: IdempotentOp, Std.IdempotentOp.idempotent, h.eq, h_surj, h_surj.forall, idempotent
-/
theorem isIdempotent_right [Std.IdempotentOp ga] (h : Semiconj₂ f ga gb) (h_surj : Surjective f) :
    Std.IdempotentOp gb :=
  ⟨h_surj.forall.2 fun x => by simp only [← h.eq, Std.IdempotentOp.idempotent (op := ga)]⟩

/--
theorem `isIdempotent_left` / 定理 `isIdempotent_left`

English:
theorem isIdempotent_left
  given: [Std.IdempotentOp gb] (h : Semiconj₂ f ga gb) (h_inj : Injective f)
  proof: ⟨fun x => h_inj by rw [h.eq, Std.IdempotentOp.idempotent (op := gb)]⟩

中文:
定理 isIdempotent_left
  条件: [Std.IdempotentOp gb] (h : Semiconj₂ f ga gb) (h_inj : Injective f)
  证明: ⟨fun x => h_inj by rw [h.eq, Std.IdempotentOp.idempotent (op := gb)]⟩

Depends on / 依赖: IdempotentOp, Std.IdempotentOp.idempotent, h.eq, h_inj, idempotent
-/
theorem isIdempotent_left [Std.IdempotentOp gb] (h : Semiconj₂ f ga gb) (h_inj : Injective f) :
    Std.IdempotentOp ga :=
⟨fun x => h_inj by rw [h.eq, Std.IdempotentOp.idempotent (op := gb)]⟩

end Semiconj₂

end Function
