/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Logic.Function.Defs
public import Mathlib.Logic.Function.Basic

/-!
# Sigma types

This file proves basic results about sigma types.

A sigma type is a dependent pair type. Like `α × β` but where the type of the second component
depends on the first component. More precisely, given `β : ι → Type*`, `Sigma β` is made of stuff
which is of type `β i` for some `i : ι`, so the sigma type is a disjoint union of types.
For example, the sum type `X ⊕ Y` can be emulated using a sigma type, by taking `ι` with
exactly two elements (see `Equiv.sumEquivSigmaBool`).

`Σ x, A x` is notation for `Sigma A` (note that this is `\Sigma`, not the sum operator `∑`).
`Σ x y z ..., A x y z ...` is notation for `Σ x, Σ y, Σ z, ..., A x y z ...`. Here we have
`α : Type*`, `β : α → Type*`, `γ : Π a : α, β a → Type*`, ...,
`A : Π (a : α) (b : β a) (c : γ a b) ..., Type*` with `x : α` `y : β x`, `z : γ x y`, ...

## Notes

The definition of `Sigma` takes values in `Type*`. This effectively forbids `Prop`-valued sigma
types. To that effect, we have `PSigma`, which takes value in `Sort*` and carries a more
complicated universe signature as a consequence.
-/

@[expose] public section

open Function

section Sigma

variable {α α₁ α₂ : Type*} {β : α -> Type*} {β₁ : α₁ -> Type*} {β₂ : α₂ -> Type*}

namespace Sigma

/--
Instance `instInhabitedSigma` / 实例 `instInhabitedSigma`

English:
instance instInhabitedSigma
  signature: [Inhabited α] [Inhabited (β default)]
  body: ⟨⟨default, default⟩⟩

中文:
实例 instInhabitedSigma
  签名: [Inhabited α] [Inhabited (β default)]
  定义体: ⟨⟨default, default⟩⟩
-/
instance instInhabitedSigma [Inhabited α] [Inhabited (β default)] : Inhabited (Sigma β) :=
  ⟨⟨default, default⟩⟩

/--
Instance `instDecidableEqSigma` / 实例 `instDecidableEqSigma`

English:
instance instDecidableEqSigma
  signature: [h₁ : DecidableEq α] [h₂ : forall a, DecidableEq (β a)]

中文:
实例 instDecidableEqSigma
  签名: [h₁ : DecidableEq α] [h₂ : 对任意 a, DecidableEq (β a)]
-/
instance instDecidableEqSigma [h₁ : DecidableEq α] [h₂ : forall a, DecidableEq (β a)] :
    DecidableEq (Sigma β)
  | ⟨a₁, b₁⟩, ⟨a₂, b₂⟩ =>
    match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
    | _, b₁, _, b₂, isTrue (Eq.refl _) =>
      match b₁, b₂, h₂ _ b₁ b₂ with
      | _, _, isTrue (Eq.refl _) => isTrue rfl
      | _, _, isFalse n => isFalse fun h =>
        Sigma.noConfusion rfl .rfl (heq_of_eq h) fun _ e₂ => n (eq_of_heq e₂)
    | _, _, _, _, isFalse n => isFalse fun h =>
      Sigma.noConfusion rfl .rfl (heq_of_eq h) fun e₁ _ => n (eq_of_heq e₁)

/--
theorem `mk.inj_iff` / 定理 `mk.inj_iff`

English:
theorem mk.inj_iff
  given: {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}
  proof: by simp

@[simp]

中文:
定理 mk.inj_iff
  条件: {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}
  证明: by simp

@[simp]
-/
theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    Sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ b₁ ≍ b₂ := by simp

@[simp]
/--
theorem `eta` / 定理 `eta`

English:
theorem eta
  statement: forall x : Σ a, β a, Sigma.mk x.1 x.2 = x

中文:
定理 eta
  结论: 对任意 x : Σ a, β a, Sigma.mk x.1 x.2 = x
-/
theorem eta : forall x : Σ a, β a, Sigma.mk x.1 x.2 = x
  | ⟨_, _⟩ => rfl

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {α : Type*} {β : α -> Type*}
  statement: forall {p₁ p₂ : Σ a, β a} (h₁ : p₁.1 = p₂.1),

中文:
定理 eq
  条件: {α : 类型} {β : α -> 类型}
  结论: 对任意 {p₁ p₂ : Σ a, β a} (h₁ : p₁.1 = p₂.1),
-/
protected theorem eq {α : Type*} {β : α -> Type*} : forall {p₁ p₂ : Σ a, β a} (h₁ : p₁.1 = p₂.1),
    (Eq.recOn h₁ p₁.2 : β p₂.1) = p₂.2 -> p₁ = p₂
  | ⟨_, _⟩, _, rfl, rfl => rfl

/--
theorem `_root_.Function.eq_of_sigmaMk_comp` / 定理 `_root_.Function.eq_of_sigmaMk_comp`

English:
theorem _root_.Function.eq_of_sigmaMk_comp
  statement: {γ : Type*} [Nonempty γ]
  proof: by
  rcases ‹Nonempty γ› with ⟨i⟩
  obtain rfl : a = b := congr_arg Sigma.fst (congr_fun h i)
  simpa [funext_iff] using h

中文:
定理 _root_.Function.eq_of_sigmaMk_comp
  结论: {γ : 类型} [Nonempty γ]
  证明: by
  rcases ‹Nonempty γ› with ⟨i⟩
  obtain rfl : a = b := congr_arg Sigma.fst (congr_fun h i)
  simpa [funext_iff] using h

Depends on / 依赖: Nonempty, Sigma.fst, congr_arg, congr_fun, funext_iff
-/
theorem _root_.Function.eq_of_sigmaMk_comp {γ : Type*} [Nonempty γ]
    {a b : α} {f : γ -> β a} {g : γ -> β b} (h : Sigma.mk a ∘ f = Sigma.mk b ∘ g) :
    a = b ∧ f ≍ g := by
  rcases ‹Nonempty γ› with ⟨i⟩
  obtain rfl : a = b := congr_arg Sigma.fst (congr_fun h i)
  simpa [funext_iff] using h

/-- A specialized ext lemma for equality of sigma types over an indexed subtype. -/
@[ext]
/--
theorem `subtype_ext` / 定理 `subtype_ext`

English:
theorem subtype_ext
  given: {β : Type*} {p : α -> β -> Prop}

中文:
定理 subtype_ext
  条件: {β : 类型} {p : α -> β -> 命题}
-/
theorem subtype_ext {β : Type*} {p : α -> β -> Prop} :
    forall {x₀ x₁ : Σ a, Subtype (p a)}, x₀.fst = x₁.fst -> (x₀.snd : β) = x₁.snd -> x₀ = x₁
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

-- This is not a good simp lemma, as its discrimination tree key is just an arrow.
/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : (Σ a, β a) -> Prop}
  statement: (forall x, p x) ↔ forall a b, p ⟨a, b⟩
  proof: ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

@[simp]

中文:
定理 «forall»
  条件: {p : (Σ a, β a) -> 命题}
  结论: (对任意 x, p x) ↔ 对任意 a b, p ⟨a, b⟩
  证明: ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

@[simp]
-/
theorem «forall» {p : (Σ a, β a) -> Prop} : (forall x, p x) ↔ forall a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

@[simp]
/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {p : (Σ a, β a) -> Prop}
  statement: (exists x, p x) ↔ exists a b, p ⟨a, b⟩
  proof: ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

中文:
定理 «exists»
  条件: {p : (Σ a, β a) -> 命题}
  结论: (存在 x, p x) ↔ 存在 a b, p ⟨a, b⟩
  证明: ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩
-/
theorem «exists» {p : (Σ a, β a) -> Prop} : (exists x, p x) ↔ exists a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

/--
lemma `exists'` / 引理 `exists'`

English:
lemma exists'
  given: {p : forall a, β a -> Prop}
  statement: (exists a b, p a b) ↔ exists x : Σ a, β a, p x.1 x.2
  proof: (Sigma.exists (p := fun x => p x.1 x.2)).symm

中文:
引理 exists'
  条件: {p : 对任意 a, β a -> 命题}
  结论: (存在 a b, p a b) ↔ 存在 x : Σ a, β a, p x.1 x.2
  证明: (Sigma.exists (p := fun x => p x.1 x.2)).symm

Depends on / 依赖: Sigma.exists
-/
lemma exists' {p : forall a, β a -> Prop} : (exists a b, p a b) ↔ exists x : Σ a, β a, p x.1 x.2 :=
  (Sigma.exists (p := fun x => p x.1 x.2)).symm

/--
lemma `forall'` / 引理 `forall'`

English:
lemma forall'
  given: {p : forall a, β a -> Prop}
  statement: (forall a b, p a b) ↔ forall x : Σ a, β a, p x.1 x.2
  proof: (Sigma.forall (p := fun x => p x.1 x.2)).symm

中文:
引理 forall'
  条件: {p : 对任意 a, β a -> 命题}
  结论: (对任意 a b, p a b) ↔ 对任意 x : Σ a, β a, p x.1 x.2
  证明: (Sigma.forall (p := fun x => p x.1 x.2)).symm

Depends on / 依赖: Sigma.forall
-/
lemma forall' {p : forall a, β a -> Prop} : (forall a b, p a b) ↔ forall x : Σ a, β a, p x.1 x.2 :=
  (Sigma.forall (p := fun x => p x.1 x.2)).symm

/--
theorem `_root_.sigma_mk_injective` / 定理 `_root_.sigma_mk_injective`

English:
theorem _root_.sigma_mk_injective
  given: {i : α}
  statement: Injective (@Sigma.mk α β i)

中文:
定理 _root_.sigma_mk_injective
  条件: {i : α}
  结论: Injective (@Sigma.mk α β i)
-/
theorem _root_.sigma_mk_injective {i : α} : Injective (@Sigma.mk α β i)
  | _, _, rfl => rfl

/--
theorem `fst_surjective` / 定理 `fst_surjective`

English:
theorem fst_surjective
  given: [h : forall a, Nonempty (β a)]
  statement: Surjective (fst : (Σ a, β a) -> α)
  proof: fun a =>
  let ⟨b⟩ := h a; ⟨⟨a, b⟩, rfl⟩

中文:
定理 fst_surjective
  条件: [h : 对任意 a, Nonempty (β a)]
  结论: Surjective (fst : (Σ a, β a) -> α)
  证明: fun a =>
  let ⟨b⟩ := h a; ⟨⟨a, b⟩, rfl⟩
-/
theorem fst_surjective [h : forall a, Nonempty (β a)] : Surjective (fst : (Σ a, β a) -> α) := fun a =>
  let ⟨b⟩ := h a; ⟨⟨a, b⟩, rfl⟩

/--
theorem `fst_surjective_iff` / 定理 `fst_surjective_iff`

English:
theorem fst_surjective_iff
  statement: Surjective (fst : (Σ a, β a) -> α) ↔ forall a, Nonempty (β a)
  proof: ⟨fun h a => let ⟨x, hx⟩ := h a; hx ▸ ⟨x.2⟩, @fst_surjective _ _⟩

中文:
定理 fst_surjective_iff
  结论: Surjective (fst : (Σ a, β a) -> α) ↔ 对任意 a, Nonempty (β a)
  证明: ⟨fun h a => let ⟨x, hx⟩ := h a; hx ▸ ⟨x.2⟩, @fst_surjective _ _⟩

Depends on / 依赖: fst_surjective
-/
theorem fst_surjective_iff : Surjective (fst : (Σ a, β a) -> α) ↔ forall a, Nonempty (β a) :=
  ⟨fun h a => let ⟨x, hx⟩ := h a; hx ▸ ⟨x.2⟩, @fst_surjective _ _⟩

/--
theorem `fst_injective` / 定理 `fst_injective`

English:
theorem fst_injective
  given: [h : forall a, Subsingleton (β a)]
  statement: Injective (fst : (Σ a, β a) -> α)
  proof: by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (rfl : a₁ = a₂)
exact congr_arg (mk a₁) Subsingleton.elim _ _

中文:
定理 fst_injective
  条件: [h : 对任意 a, Subsingleton (β a)]
  结论: Injective (fst : (Σ a, β a) -> α)
  证明: by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (rfl : a₁ = a₂)
exact congr_arg (mk a₁) Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim, congr_arg
-/
theorem fst_injective [h : forall a, Subsingleton (β a)] : Injective (fst : (Σ a, β a) -> α) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (rfl : a₁ = a₂)
exact congr_arg (mk a₁) Subsingleton.elim _ _

/--
theorem `fst_injective_iff` / 定理 `fst_injective_iff`

English:
theorem fst_injective_iff
  statement: Injective (fst : (Σ a, β a) -> α) ↔ forall a, Subsingleton (β a)
  proof: ⟨fun h _ => ⟨fun _ _ => sigma_mk_injective h rfl⟩, @fst_injective _ _⟩

中文:
定理 fst_injective_iff
  结论: Injective (fst : (Σ a, β a) -> α) ↔ 对任意 a, Subsingleton (β a)
  证明: ⟨fun h _ => ⟨fun _ _ => sigma_mk_injective h rfl⟩, @fst_injective _ _⟩

Depends on / 依赖: fst_injective, sigma_mk_injective
-/
theorem fst_injective_iff : Injective (fst : (Σ a, β a) -> α) ↔ forall a, Subsingleton (β a) :=
⟨fun h _ => ⟨fun _ _ => sigma_mk_injective h rfl⟩, @fst_injective _ _⟩

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f₁ : α₁ -> α₂) (f₂ : forall a, β₁ a -> β₂ (f₁ a)) (x : Sigma β₁)
  body: ⟨f₁ x.1, f₂ x.1 x.2⟩

中文:
定义 map
  签名: (f₁ : α₁ -> α₂) (f₂ : 对任意 a, β₁ a -> β₂ (f₁ a)) (x : Sigma β₁)
  定义体: ⟨f₁ x.1, f₂ x.1 x.2⟩
-/
def map (f₁ : α₁ -> α₂) (f₂ : forall a, β₁ a -> β₂ (f₁ a)) (x : Sigma β₁) : Sigma β₂ :=
  ⟨f₁ x.1, f₂ x.1 x.2⟩

/--
lemma `map_mk` / 引理 `map_mk`

English:
lemma map_mk
  given: (f₁ : α₁ -> α₂) (f₂ : forall a, β₁ a -> β₂ (f₁ a)) (x : α₁) (y : β₁ x)
  proof: rfl

中文:
引理 map_mk
  条件: (f₁ : α₁ -> α₂) (f₂ : 对任意 a, β₁ a -> β₂ (f₁ a)) (x : α₁) (y : β₁ x)
  证明: rfl
-/
lemma map_mk (f₁ : α₁ -> α₂) (f₂ : forall a, β₁ a -> β₂ (f₁ a)) (x : α₁) (y : β₁ x) :
    map f₁ f₂ ⟨x, y⟩ = ⟨f₁ x, f₂ x y⟩ := rfl
end Sigma

/--
theorem `Function.Injective.sigma_map` / 定理 `Function.Injective.sigma_map`

English:
theorem Function.Injective.sigma_map
  statement: {f₁ : α₁ -> α₂} {f₂ : forall a, β₁ a -> β₂ (f₁ a)}
  proof: h₁ (Sigma.mk.inj_iff.mp h).1
    obtain rfl : x = y := h₂ i (sigma_mk_injective h)
    rfl

中文:
定理 Function.Injective.sigma_map
  结论: {f₁ : α₁ -> α₂} {f₂ : 对任意 a, β₁ a -> β₂ (f₁ a)}
  证明: h₁ (Sigma.mk.inj_iff.mp h).1
    obtain rfl : x = y := h₂ i (sigma_mk_injective h)
    rfl

Depends on / 依赖: Sigma.mk.inj_iff.mp, inj_iff
-/
theorem Function.Injective.sigma_map {f₁ : α₁ -> α₂} {f₂ : forall a, β₁ a -> β₂ (f₁ a)}
    (h₁ : Injective f₁) (h₂ : forall a, Injective (f₂ a)) : Injective (Sigma.map f₁ f₂)
  | ⟨i, x⟩, ⟨j, y⟩, h => by
    obtain rfl : i = j := h₁ (Sigma.mk.inj_iff.mp h).1
    obtain rfl : x = y := h₂ i (sigma_mk_injective h)
    rfl

/--
theorem `Function.Injective.of_sigma_map` / 定理 `Function.Injective.of_sigma_map`

English:
theorem Function.Injective.of_sigma_map
  statement: {f₁ : α₁ -> α₂} {f₂ : forall a, β₁ a -> β₂ (f₁ a)}
  proof: fun x y hxy =>
sigma_mk_injective @h ⟨a, x⟩ ⟨a, y⟩ (Sigma.ext rfl (heq_of_eq hxy))

中文:
定理 Function.Injective.of_sigma_map
  结论: {f₁ : α₁ -> α₂} {f₂ : 对任意 a, β₁ a -> β₂ (f₁ a)}
  证明: fun x y hxy =>
sigma_mk_injective @h ⟨a, x⟩ ⟨a, y⟩ (Sigma.ext rfl (heq_of_eq hxy))
-/
theorem Function.Injective.of_sigma_map {f₁ : α₁ -> α₂} {f₂ : forall a, β₁ a -> β₂ (f₁ a)}
    (h : Injective (Sigma.map f₁ f₂)) (a : α₁) : Injective (f₂ a) := fun x y hxy =>
sigma_mk_injective @h ⟨a, x⟩ ⟨a, y⟩ (Sigma.ext rfl (heq_of_eq hxy))

/--
theorem `Function.Injective.sigma_map_iff` / 定理 `Function.Injective.sigma_map_iff`

English:
theorem Function.Injective.sigma_map_iff
  statement: {f₁ : α₁ -> α₂} {f₂ : forall a, β₁ a -> β₂ (f₁ a)}
  proof: ⟨fun h => h.of_sigma_map, h₁.sigma_map⟩

中文:
定理 Function.Injective.sigma_map_iff
  结论: {f₁ : α₁ -> α₂} {f₂ : 对任意 a, β₁ a -> β₂ (f₁ a)}
  证明: ⟨fun h => h.of_sigma_map, h₁.sigma_map⟩

Depends on / 依赖: h.of_sigma_map, of_sigma_map, sigma_map
-/
theorem Function.Injective.sigma_map_iff {f₁ : α₁ -> α₂} {f₂ : forall a, β₁ a -> β₂ (f₁ a)}
    (h₁ : Injective f₁) : Injective (Sigma.map f₁ f₂) ↔ forall a, Injective (f₂ a) :=
  ⟨fun h => h.of_sigma_map, h₁.sigma_map⟩

/--
theorem `Function.Surjective.sigma_map` / 定理 `Function.Surjective.sigma_map`

English:
theorem Function.Surjective.sigma_map
  statement: {f₁ : α₁ -> α₂} {f₂ : forall a, β₁ a -> β₂ (f₁ a)}
  proof: by
  simp only [Surjective, Sigma.forall, h₁.forall]
  exact fun i => (h₂ _).forall.2 fun x => ⟨⟨i, x⟩, rfl⟩

中文:
定理 Function.Surjective.sigma_map
  结论: {f₁ : α₁ -> α₂} {f₂ : 对任意 a, β₁ a -> β₂ (f₁ a)}
  证明: by
  simp only [Surjective, Sigma.forall, h₁.forall]
  exact fun i => (h₂ _).forall.2 fun x => ⟨⟨i, x⟩, rfl⟩

Depends on / 依赖: Sigma.forall, Surjective
-/
theorem Function.Surjective.sigma_map {f₁ : α₁ -> α₂} {f₂ : forall a, β₁ a -> β₂ (f₁ a)}
    (h₁ : Surjective f₁) (h₂ : forall a, Surjective (f₂ a)) : Surjective (Sigma.map f₁ f₂) := by
  simp only [Surjective, Sigma.forall, h₁.forall]
  exact fun i => (h₂ _).forall.2 fun x => ⟨⟨i, x⟩, rfl⟩

/--
Definition of `Sigma.curry` / `Sigma.curry` 的定义

English:
definition Sigma.curry
  signature: {γ : forall a, β a -> Type*} (f : forall x : Sigma β, γ x.1 x.2) (x : α) (y : β x)
  body: f ⟨x, y⟩

中文:
定义 Sigma.curry
  签名: {γ : 对任意 a, β a -> 类型} (f : 对任意 x : Sigma β, γ x.1 x.2) (x : α) (y : β x)
  定义体: f ⟨x, y⟩
-/
def Sigma.curry {γ : forall a, β a -> Type*} (f : forall x : Sigma β, γ x.1 x.2) (x : α) (y : β x) : γ x y :=
  f ⟨x, y⟩

/--
Definition of `Sigma.uncurry` / `Sigma.uncurry` 的定义

English:
definition Sigma.uncurry
  signature: {γ : forall a, β a -> Type*} (f : forall (x) (y : β x), γ x y) (x : Sigma β)
  body: f x.1 x.2

@[simp]

中文:
定义 Sigma.uncurry
  签名: {γ : 对任意 a, β a -> 类型} (f : 对任意 (x) (y : β x), γ x y) (x : Sigma β)
  定义体: f x.1 x.2

@[simp]
-/
def Sigma.uncurry {γ : forall a, β a -> Type*} (f : forall (x) (y : β x), γ x y) (x : Sigma β) : γ x.1 x.2 :=
  f x.1 x.2

@[simp]
/--
theorem `Sigma.uncurry_curry` / 定理 `Sigma.uncurry_curry`

English:
theorem Sigma.uncurry_curry
  given: {γ : forall a, β a -> Type*} (f : forall x : Sigma β, γ x.1 x.2)
  proof: funext fun ⟨_, _⟩ => rfl

@[simp]

中文:
定理 Sigma.uncurry_curry
  条件: {γ : 对任意 a, β a -> 类型} (f : 对任意 x : Sigma β, γ x.1 x.2)
  证明: funext fun ⟨_, _⟩ => rfl

@[simp]
-/
theorem Sigma.uncurry_curry {γ : forall a, β a -> Type*} (f : forall x : Sigma β, γ x.1 x.2) :
    Sigma.uncurry (Sigma.curry f) = f :=
  funext fun ⟨_, _⟩ => rfl

@[simp]
/--
theorem `Sigma.curry_uncurry` / 定理 `Sigma.curry_uncurry`

English:
theorem Sigma.curry_uncurry
  given: {γ : forall a, β a -> Type*} (f : forall (x) (y : β x), γ x y)
  proof: rfl

中文:
定理 Sigma.curry_uncurry
  条件: {γ : 对任意 a, β a -> 类型} (f : 对任意 (x) (y : β x), γ x y)
  证明: rfl
-/
theorem Sigma.curry_uncurry {γ : forall a, β a -> Type*} (f : forall (x) (y : β x), γ x y) :
    Sigma.curry (Sigma.uncurry f) = f :=
  rfl

/--
theorem `Sigma.curry_update` / 定理 `Sigma.curry_update`

English:
theorem Sigma.curry_update
  statement: {γ : forall a, β a -> Type*} [DecidableEq α] [forall a, DecidableEq (β a)]
  proof: by
  obtain ⟨ia, ib⟩ := i
  ext ja jb
  unfold Sigma.curry
  obtain rfl | ha := eq_or_ne ia ja
  · simp
    grind
  · rw [Function.update_of_ne (ne_of_apply_ne Sigma.fst _), Function.update_of_ne]
    · exact ha.symm
    · exact ha.symm

中文:
定理 Sigma.curry_update
  结论: {γ : 对任意 a, β a -> 类型} [DecidableEq α] [对任意 a, DecidableEq (β a)]
  证明: by
  obtain ⟨ia, ib⟩ := i
  ext ja jb
  unfold Sigma.curry
  obtain rfl | ha := eq_or_ne ia ja
  · simp
    grind
  · rw [Function.update_of_ne (ne_of_apply_ne Sigma.fst _), Function.update_of_ne]
    · exact ha.symm
    · exact ha.symm

Depends on / 依赖: Function, Function.update_of_ne, Sigma.curry, Sigma.fst, eq_or_ne, ha.symm, ne_of_apply_ne, update_of_ne
-/
theorem Sigma.curry_update {γ : forall a, β a -> Type*} [DecidableEq α] [forall a, DecidableEq (β a)]
    (i : Σ a, β a) (f : (i : Σ a, β a) -> γ i.1 i.2) (x : γ i.1 i.2) :
    Sigma.curry (Function.update f i x) =
      Function.update (Sigma.curry f) i.1 (Function.update (Sigma.curry f i.1) i.2 x) := by
  obtain ⟨ia, ib⟩ := i
  ext ja jb
  unfold Sigma.curry
  obtain rfl | ha := eq_or_ne ia ja
  · simp
    grind
  · rw [Function.update_of_ne (ne_of_apply_ne Sigma.fst _), Function.update_of_ne]
    · exact ha.symm
    · exact ha.symm

/--
Definition of `Prod.toSigma` / `Prod.toSigma` 的定义

English:
definition Prod.toSigma
  signature: {α β} (p : α × β)
  body: ⟨p.1, p.2⟩

@[simp]

中文:
定义 Prod.toSigma
  签名: {α β} (p : α × β)
  定义体: ⟨p.1, p.2⟩

@[simp]
-/
def Prod.toSigma {α β} (p : α × β) : Σ _ : α, β :=
  ⟨p.1, p.2⟩

@[simp]
/--
theorem `Prod.fst_comp_toSigma` / 定理 `Prod.fst_comp_toSigma`

English:
theorem Prod.fst_comp_toSigma
  given: {α β}
  statement: Sigma.fst ∘ @Prod.toSigma α β = Prod.fst
  proof: rfl

@[simp]

中文:
定理 Prod.fst_comp_toSigma
  条件: {α β}
  结论: Sigma.fst ∘ @Prod.toSigma α β = Prod.fst
  证明: rfl

@[simp]
-/
theorem Prod.fst_comp_toSigma {α β} : Sigma.fst ∘ @Prod.toSigma α β = Prod.fst :=
  rfl

@[simp]
/--
theorem `Prod.fst_toSigma` / 定理 `Prod.fst_toSigma`

English:
theorem Prod.fst_toSigma
  given: {α β} (x : α × β)
  statement: (Prod.toSigma x).fst = x.fst
  proof: rfl

@[simp]

中文:
定理 Prod.fst_toSigma
  条件: {α β} (x : α × β)
  结论: (Prod.toSigma x).fst = x.fst
  证明: rfl

@[simp]
-/
theorem Prod.fst_toSigma {α β} (x : α × β) : (Prod.toSigma x).fst = x.fst :=
  rfl

@[simp]
/--
theorem `Prod.snd_toSigma` / 定理 `Prod.snd_toSigma`

English:
theorem Prod.snd_toSigma
  given: {α β} (x : α × β)
  statement: (Prod.toSigma x).snd = x.snd
  proof: rfl

@[simp]

中文:
定理 Prod.snd_toSigma
  条件: {α β} (x : α × β)
  结论: (Prod.toSigma x).snd = x.snd
  证明: rfl

@[simp]
-/
theorem Prod.snd_toSigma {α β} (x : α × β) : (Prod.toSigma x).snd = x.snd :=
  rfl

@[simp]
/--
theorem `Prod.toSigma_mk` / 定理 `Prod.toSigma_mk`

English:
theorem Prod.toSigma_mk
  given: {α β} (x : α) (y : β)
  statement: (x, y).toSigma = ⟨x, y⟩
  proof: rfl

中文:
定理 Prod.toSigma_mk
  条件: {α β} (x : α) (y : β)
  结论: (x, y).toSigma = ⟨x, y⟩
  证明: rfl
-/
theorem Prod.toSigma_mk {α β} (x : α) (y : β) : (x, y).toSigma = ⟨x, y⟩ :=
  rfl

/--
theorem `Prod.toSigma_injective` / 定理 `Prod.toSigma_injective`

English:
theorem Prod.toSigma_injective
  given: {α β}
  statement: Function.Injective (α := α × β) Prod.toSigma
  proof: by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp_all

@[simp]

中文:
定理 Prod.toSigma_injective
  条件: {α β}
  结论: Function.Injective (α := α × β) Prod.toSigma
  证明: by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp_all

@[simp]

Depends on / 依赖: Prod.toSigma, toSigma
-/
theorem Prod.toSigma_injective {α β} : Function.Injective (α := α × β) Prod.toSigma := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp_all

@[simp]
/--
theorem `Prod.toSigma_inj` / 定理 `Prod.toSigma_inj`

English:
theorem Prod.toSigma_inj
  given: {α β} {x y : α × β}
  statement: x.toSigma = y.toSigma ↔ x = y
  proof: Prod.toSigma_injective.eq_iff

中文:
定理 Prod.toSigma_inj
  条件: {α β} {x y : α × β}
  结论: x.toSigma = y.toSigma ↔ x = y
  证明: Prod.toSigma_injective.eq_iff

Depends on / 依赖: Prod.toSigma_injective.eq_iff, eq_iff, toSigma_injective
-/
theorem Prod.toSigma_inj {α β} {x y : α × β} : x.toSigma = y.toSigma ↔ x = y :=
  Prod.toSigma_injective.eq_iff

end Sigma

namespace PSigma

variable {α : Sort*} {β : α -> Sort*}

/--
Definition of `elim` / `elim` 的定义

English:
definition elim
  signature: {γ} (f : forall a, β a -> γ) (a : PSigma β)
  body: PSigma.casesOn a f

@[simp]

中文:
定义 elim
  签名: {γ} (f : 对任意 a, β a -> γ) (a : PSigma β)
  定义体: PSigma.casesOn a f

@[simp]

Depends on / 依赖: PSigma, PSigma.casesOn, casesOn
-/
def elim {γ} (f : forall a, β a -> γ) (a : PSigma β) : γ :=
  PSigma.casesOn a f

@[simp]
/--
theorem `elim_val` / 定理 `elim_val`

English:
theorem elim_val
  given: {γ} (f : forall a, β a -> γ) (a b)
  statement: PSigma.elim f ⟨a, b⟩ = f a b
  proof: rfl

中文:
定理 elim_val
  条件: {γ} (f : 对任意 a, β a -> γ) (a b)
  结论: PSigma.elim f ⟨a, b⟩ = f a b
  证明: rfl
-/
theorem elim_val {γ} (f : forall a, β a -> γ) (a b) : PSigma.elim f ⟨a, b⟩ = f a b :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] [Inhabited (β default)] : Inhabited (PSigma β)
  body: ⟨⟨default, default⟩⟩

中文:
实例 [Inhabited
  签名: α] [Inhabited (β default)] : Inhabited (PSigma β)
  定义体: ⟨⟨default, default⟩⟩
-/
instance [Inhabited α] [Inhabited (β default)] : Inhabited (PSigma β) :=
  ⟨⟨default, default⟩⟩

/--
Instance `decidableEq` / 实例 `decidableEq`

English:
instance decidableEq
  signature: [h₁ : DecidableEq α] [h₂ : forall a, DecidableEq (β a)]

中文:
实例 decidableEq
  签名: [h₁ : DecidableEq α] [h₂ : 对任意 a, DecidableEq (β a)]
-/
instance decidableEq [h₁ : DecidableEq α] [h₂ : forall a, DecidableEq (β a)] : DecidableEq (PSigma β)
  | ⟨a₁, b₁⟩, ⟨a₂, b₂⟩ =>
    match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
    | _, b₁, _, b₂, isTrue (Eq.refl _) =>
      match b₁, b₂, h₂ _ b₁ b₂ with
      | _, _, isTrue (Eq.refl _) => isTrue rfl
      | _, _, isFalse n => isFalse fun h =>
        PSigma.noConfusion rfl .rfl (heq_of_eq h) fun _ e₂ => n (eq_of_heq e₂)
    | _, _, _, _, isFalse n => isFalse fun h =>
      PSigma.noConfusion rfl .rfl (heq_of_eq h) fun e₁ _ => n (eq_of_heq e₁)

/--
theorem `mk.inj_iff` / 定理 `mk.inj_iff`

English:
theorem mk.inj_iff
  given: {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}
  proof: (Iff.intro PSigma.mk.inj) fun ⟨h₁, h₂⟩ =>
    match a₁, a₂, b₁, b₂, h₁, h₂ with
    | _, _, _, _, Eq.refl _, HEq.refl _ => rfl

中文:
定理 mk.inj_iff
  条件: {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}
  证明: (Iff.intro PSigma.mk.inj) fun ⟨h₁, h₂⟩ =>
    match a₁, a₂, b₁, b₂, h₁, h₂ with
    | _, _, _, _, Eq.refl _, HEq.refl _ => rfl
-/
theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    @PSigma.mk α β a₁ b₁ = @PSigma.mk α β a₂ b₂ ↔ a₁ = a₂ ∧ b₁ ≍ b₂ :=
  (Iff.intro PSigma.mk.inj) fun ⟨h₁, h₂⟩ =>
    match a₁, a₂, b₁, b₂, h₁, h₂ with
    | _, _, _, _, Eq.refl _, HEq.refl _ => rfl

-- This should not be a simp lemma, since its discrimination tree key would just be `→`.
/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : (Σ' a, β a) -> Prop}
  statement: (forall x, p x) ↔ forall a b, p ⟨a, b⟩
  proof: ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

中文:
定理 «forall»
  条件: {p : (Σ' a, β a) -> 命题}
  结论: (对任意 x, p x) ↔ 对任意 a b, p ⟨a, b⟩
  证明: ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩
-/
theorem «forall» {p : (Σ' a, β a) -> Prop} : (forall x, p x) ↔ forall a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

/--
lemma `«exists»` / 引理 `«exists»`

English:
lemma «exists»
  given: {p : (Σ' a, β a) -> Prop}
  statement: (exists x, p x) ↔ exists a b, p ⟨a, b⟩
  proof: ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

中文:
引理 «exists»
  条件: {p : (Σ' a, β a) -> 命题}
  结论: (存在 x, p x) ↔ 存在 a b, p ⟨a, b⟩
  证明: ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩
-/
@[simp] lemma «exists» {p : (Σ' a, β a) -> Prop} : (exists x, p x) ↔ exists a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

/-- A specialized ext lemma for equality of `PSigma` types over an indexed subtype. -/
@[ext]
/--
theorem `subtype_ext` / 定理 `subtype_ext`

English:
theorem subtype_ext
  given: {β : Sort*} {p : α -> β -> Prop}

中文:
定理 subtype_ext
  条件: {β : Sort*} {p : α -> β -> 命题}
-/
theorem subtype_ext {β : Sort*} {p : α -> β -> Prop} :
    forall {x₀ x₁ : Σ' a, Subtype (p a)}, x₀.fst = x₁.fst -> (x₀.snd : β) = x₁.snd -> x₀ = x₁
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

variable {α₁ : Sort*} {α₂ : Sort*} {β₁ : α₁ -> Sort*} {β₂ : α₂ -> Sort*}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f₁ : α₁ -> α₂) (f₂ : forall a, β₁ a -> β₂ (f₁ a))

中文:
定义 map
  签名: (f₁ : α₁ -> α₂) (f₂ : 对任意 a, β₁ a -> β₂ (f₁ a))
-/
def map (f₁ : α₁ -> α₂) (f₂ : forall a, β₁ a -> β₂ (f₁ a)) : PSigma β₁ -> PSigma β₂
  | ⟨a, b⟩ => ⟨f₁ a, f₂ a b⟩

end PSigma
