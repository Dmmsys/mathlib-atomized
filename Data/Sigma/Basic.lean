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

variable {α α₁ α₂ : Type*} {β : α → Type*} {β₁ : α₁ → Type*} {β₂ : α₂ → Type*}

namespace Sigma

/-
**Sigma.instInhabitedSigma** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
形式化陈述：instInhabitedSigma [Inhabited α] [Inhabited (β default)] : Inhabited (Sigm
a β)
参数：β default。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabitedSigma [Inhabited α] [Inhabited (β default)] : Inhabited (Sigma β) :=
  ⟨⟨default, default⟩⟩
/-
**Sigma.instDecidableEqSigma** 是 Mathlib 中的一个定义，位于命名空间 `Sigma`。
形式化陈述：{α : Type u_1} → {β : α → Type u_4} → [h₁ : DecidableEq α] → [h₂ : (a : α)
 → DecidableEq (β a)] → DecidableEq (Sigma β)
参数：a : α；β a；Sigma β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableEqSigma [h₁ : DecidableEq α] [h₂ : ∀ a, DecidableEq (β a)] :
    DecidableEq (Sigma β)
  | ⟨a₁, b₁⟩, ⟨a₂, b₂⟩ =>
    match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
    | _, b₁, _, b₂, isTrue (Eq.refl _) =>
      match b₁, b₂, h₂ _ b₁ b₂ with
      | _, _, isTrue (Eq.refl _) => isTrue rfl
      | _, _, isFalse n => isFalse fun h ↦
        Sigma.noConfusion rfl .rfl (heq_of_eq h) fun _ e₂ ↦ n (eq_of_heq e₂)
    | _, _, _, _, isFalse n => isFalse fun h ↦
      Sigma.noConfusion rfl .rfl (heq_of_eq h) fun e₁ _ ↦ n (eq_of_heq e₁)
/-
**Sigma.mk.inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sigma.mk`。
形式化陈述：∀ {α : Type u_1} {β : α → Type u_4} {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}, ⟨
a₁, b₁⟩ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ b₁ ≍ b₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    Sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ b₁ ≍ b₂ := by simp

@[simp]
/-
**Sigma.eta** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.fst, x.snd⟩ = 
x
参数：x : (a : α) × β a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eta : ∀ x : Σ a, β a, Sigma.mk x.1 x.2 = x
  | ⟨_, _⟩ => rfl
/-
**Sigma.eq** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：∀ {α : Type u_7} {β : α → Type u_8} {p₁ p₂ : (a : α) × β a} (h₁ : p₁.fst =
 p₂.fst),   Eq.recOn h₁ p₁.snd = p₂.snd → p₁ = p₂
参数：a : α；h₁ : p₁.fst = p₂.fst。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem eq {α : Type*} {β : α → Type*} : ∀ {p₁ p₂ : Σ a, β a} (h₁ : p₁.1 = p₂.1),
    (Eq.recOn h₁ p₁.2 : β p₂.1) = p₂.2 → p₁ = p₂
  | ⟨_, _⟩, _, rfl, rfl => rfl

/-- A version of `Iff.mp Sigma.ext_iff` for functions from a nonempty type to a sigma type. -/
/-
**Sigma._root_.Function.eq_of_sigmaMk_comp** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Iff.mp Sigma.ext_iff` for functions from a nonempty type to a sigm
a type.
-/
theorem _root_.Function.eq_of_sigmaMk_comp {γ : Type*} [Nonempty γ]
    {a b : α} {f : γ → β a} {g : γ → β b} (h : Sigma.mk a ∘ f = Sigma.mk b ∘ g) :
    a = b ∧ f ≍ g := by
  rcases ‹Nonempty γ› with ⟨i⟩
  obtain rfl : a = b := congr_arg Sigma.fst (congr_fun h i)
  simpa [funext_iff] using h

/-- A specialized ext lemma for equality of sigma types over an indexed subtype. -/
@[ext]
/-
**Sigma.subtype_ext** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：∀ {α : Type u_1} {β : Type u_7} {p : α → β → Prop} {x₀ x₁ : (a : α) × Subt
ype (p a)},   x₀.fst = x₁.fst → ↑x₀.snd = ↑x₁.snd → x₀ = x₁
参数：a : α；p a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A specialized ext lemma for equality of sigma types over an indexed subtype.
-/
theorem subtype_ext {β : Type*} {p : α → β → Prop} :
    ∀ {x₀ x₁ : Σ a, Subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

-- This is not a good simp lemma, as its discrimination tree key is just an arrow.
/-
**Sigma.** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem «forall» {p : (Σ a, β a) → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b ↦ h ⟨a, b⟩, fun h ⟨a, b⟩ ↦ h a b⟩

@[simp]
/-
**Sigma.** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem «exists» {p : (Σ a, β a) → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ ↦ ⟨a, b, h⟩, fun ⟨a, b, h⟩ ↦ ⟨⟨a, b⟩, h⟩⟩
/-
**Sigma.exists'** 是 Mathlib 中的一个引理，位于命名空间 `Sigma`。
形式化陈述：exists' {p : forall a, β a -> Prop} : (exists a b, p a b) ↔ exists x : Σ a
, β a, p x.1 x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Sigma.exists`：∀ {α : Type u_1} {β : α → Type u_4} {p : (a : α) × β a → P
rop}, (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩
-/
lemma exists' {p : ∀ a, β a → Prop} : (∃ a b, p a b) ↔ ∃ x : Σ a, β a, p x.1 x.2 :=
  (Sigma.exists (p := fun x ↦ p x.1 x.2)).symm
/-
**Sigma.forall'** 是 Mathlib 中的一个引理，位于命名空间 `Sigma`。
形式化陈述：forall' {p : forall a, β a -> Prop} : (forall a b, p a b) ↔ forall x : Σ a
, β a, p x.1 x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Sigma.forall`：∀ {α : Type u_1} {β : α → Type u_4} {p : (a : α) × β a → P
rop},   (∀ (x : (a : α) × β a), p x) ↔ ∀ (a : α) (b : β a), p ⟨a, b⟩
-/
lemma forall' {p : ∀ a, β a → Prop} : (∀ a b, p a b) ↔ ∀ x : Σ a, β a, p x.1 x.2 :=
  (Sigma.forall (p := fun x ↦ p x.1 x.2)).symm
/-
**Sigma._root_.sigma_mk_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.sigma_mk_injective {i : α} : Injective (@Sigma.mk α β i)
  | _, _, rfl => rfl
/-
**Sigma.fst_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：fst_surjective [h : forall a, Nonempty (β a)] : Surjective (fst : (Σ a, β 
a) -> α)
参数：β a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_surjective [h : ∀ a, Nonempty (β a)] : Surjective (fst : (Σ a, β a) → α) := fun a ↦
  let ⟨b⟩ := h a; ⟨⟨a, b⟩, rfl⟩
/-
**Sigma.fst_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：fst_surjective_iff : Surjective (fst : (Σ a, β a) -> α) ↔ forall a, Nonemp
ty (β a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.fst_surjective`：fst_surjective [h : forall a, Nonempty (β a)] : Su
rjective (fst : (Σ a, β a) -> α)
-/
theorem fst_surjective_iff : Surjective (fst : (Σ a, β a) → α) ↔ ∀ a, Nonempty (β a) :=
  ⟨fun h a ↦ let ⟨x, hx⟩ := h a; hx ▸ ⟨x.2⟩, @fst_surjective _ _⟩
/-
**Sigma.fst_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：fst_injective [h : forall a, Subsingleton (β a)] : Injective (fst : (Σ a, 
β a) -> α)
参数：β a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem fst_injective [h : ∀ a, Subsingleton (β a)] : Injective (fst : (Σ a, β a) → α) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (rfl : a₁ = a₂)
  exact congr_arg (mk a₁) <| Subsingleton.elim _ _
/-
**Sigma.fst_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：fst_injective_iff : Injective (fst : (Σ a, β a) -> α) ↔ forall a, Subsingl
eton (β a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `Sigma.fst_injective`：fst_injective [h : forall a, Subsingleton (β a)] : 
Injective (fst : (Σ a, β a) -> α)
-/
theorem fst_injective_iff : Injective (fst : (Σ a, β a) → α) ↔ ∀ a, Subsingleton (β a) :=
  ⟨fun h _ ↦ ⟨fun _ _ ↦ sigma_mk_injective <| h rfl⟩, @fst_injective _ _⟩

/-- Map the left and right components of a sigma -/
/-
**Sigma.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：Sigma.map {f g : β -> C} [HasCoproduct f] [HasCoproduct g] (p : forall b, 
f b ⟶ g b) : ∐ f ⟶ ∐ g
参数：p : forall b, f b ⟶ g b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map the left and right components of a sigma
-/
def map (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) (x : Sigma β₁) : Sigma β₂ :=
  ⟨f₁ x.1, f₂ x.1 x.2⟩
/-
**Sigma.map_mk** 是 Mathlib 中的一个引理，位于命名空间 `Sigma`。
形式化陈述：map_mk (f₁ : α₁ -> α₂) (f₂ : forall a, β₁ a -> β₂ (f₁ a)) (x : α₁) (y : β₁
 x) : map f₁ f₂ ⟨x, y⟩ = ⟨f₁ x, f₂ x y⟩
参数：f₁ : α₁ -> α₂；f₂ : forall a, β₁ a -> β₂ (f₁ a)；x : α₁；y : β₁ x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_mk (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) (x : α₁) (y : β₁ x) :
    map f₁ f₂ ⟨x, y⟩ = ⟨f₁ x, f₂ x y⟩ := rfl
end Sigma

/-
**Function.Injective.sigma_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.sigma_map {f₁ : α₁ -> α₂} {f₂ : forall a, β₁ a -> β₂ (f
₁ a)} (h₁ : Injective f₁) (h₂ : forall a, Injective (f₂ a)) : Injective (Sigma.m
ap f₁ f₂) | ⟨i, x⟩, ⟨j, y⟩, h => by obtain rfl : i = j
参数：f₁ a；h₁ : Injective f₁；h₂ : forall a, Injective (f₂ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sigma.mk.inj_iff`：∀ {α : Type u_1} {β : α → Type u_4} {a₁ a₂ : α} {b₁ : 
β a₁} {b₂ : β a₂}, ⟨a₁, b₁⟩ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ b₁ ≍ b₂
-/
theorem Function.Injective.sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h₁ : Injective f₁) (h₂ : ∀ a, Injective (f₂ a)) : Injective (Sigma.map f₁ f₂)
  | ⟨i, x⟩, ⟨j, y⟩, h => by
    obtain rfl : i = j := h₁ (Sigma.mk.inj_iff.mp h).1
    obtain rfl : x = y := h₂ i (sigma_mk_injective h)
    rfl
/-
**Function.Injective.of_sigma_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.of_sigma_map {f₁ : α₁ -> α₂} {f₂ : forall a, β₁ a -> β₂
 (f₁ a)} (h : Injective (Sigma.map f₁ f₂)) (a : α₁) : Injective (f₂ a)
参数：f₁ a；h : Injective (Sigma.map f₁ f₂)；a : α₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `Sigma.ext`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x.fst = y.fs
t → x.snd ≍ y.snd → x = y
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem Function.Injective.of_sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h : Injective (Sigma.map f₁ f₂)) (a : α₁) : Injective (f₂ a) := fun x y hxy ↦
  sigma_mk_injective <| @h ⟨a, x⟩ ⟨a, y⟩ (Sigma.ext rfl (heq_of_eq hxy))
/-
**Function.Injective.sigma_map_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.sigma_map_iff {f₁ : α₁ -> α₂} {f₂ : forall a, β₁ a -> β
₂ (f₁ a)} (h₁ : Injective f₁) : Injective (Sigma.map f₁ f₂) ↔ forall a, Injectiv
e (f₂ a)
参数：f₁ a；h₁ : Injective f₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_sigma_map`：Function.Injective.of_sigma_map {f₁ : α
₁ -> α₂} {f₂ : forall a, β₁ a -> β₂ (f₁ a)} (h : Injective (Sigma.map f₁ f₂)) (a
 : α₁) : Injective (f…
· 使用定理 `Function.Injective.sigma_map`：Function.Injective.sigma_map {f₁ : α₁ -> α
₂} {f₂ : forall a, β₁ a -> β₂ (f₁ a)} (h₁ : Injective f₁) (h₂ : forall a, Inject
ive (f₂ a)) : Inje…
-/
theorem Function.Injective.sigma_map_iff {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h₁ : Injective f₁) : Injective (Sigma.map f₁ f₂) ↔ ∀ a, Injective (f₂ a) :=
  ⟨fun h ↦ h.of_sigma_map, h₁.sigma_map⟩
/-
**Function.Surjective.sigma_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.sigma_map {f₁ : α₁ -> α₂} {f₂ : forall a, β₁ a -> β₂ (
f₁ a)} (h₁ : Surjective f₁) (h₂ : forall a, Surjective (f₂ a)) : Surjective (Sig
ma.map f₁ f₂)
参数：f₁ a；h₁ : Surjective f₁；h₂ : forall a, Surjective (f₂ a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem Function.Surjective.sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h₁ : Surjective f₁) (h₂ : ∀ a, Surjective (f₂ a)) : Surjective (Sigma.map f₁ f₂) := by
  simp only [Surjective, Sigma.forall, h₁.forall]
  exact fun i ↦ (h₂ _).forall.2 fun x ↦ ⟨⟨i, x⟩, rfl⟩

/-- Interpret a function on `Σ x : α, β x` as a dependent function with two arguments.

This also exists as an `Equiv` as `Equiv.piCurry γ`. -/
/-
**Sigma.curry** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Sigma.curry {γ : forall a, β a -> Type*} (f : forall x : Sigma β, γ x.1 x.
2) (x : α) (y : β x) : γ x y
参数：f : forall x : Sigma β, γ x.1 x.2；x : α；y : β x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a function on `Σ x : α, β x` as a dependent function with two argument
s.

This also exists as an `Equiv` as `Equiv.piCurry γ`.
-/
def Sigma.curry {γ : ∀ a, β a → Type*} (f : ∀ x : Sigma β, γ x.1 x.2) (x : α) (y : β x) : γ x y :=
  f ⟨x, y⟩

/-- Interpret a dependent function with two arguments as a function on `Σ x : α, β x`.

This also exists as an `Equiv` as `(Equiv.piCurry γ).symm`. -/
/-
**Sigma.uncurry** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Sigma.uncurry {γ : forall a, β a -> Type*} (f : forall (x) (y : β x), γ x 
y) (x : Sigma β) : γ x.1 x.2
参数：f : forall (x) (y : β x), γ x y；x : Sigma β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a dependent function with two arguments as a function on `Σ x : α, β x
`.

This also exists as an `Equiv` as `(Equiv.piCurry γ).symm`.
-/
def Sigma.uncurry {γ : ∀ a, β a → Type*} (f : ∀ (x) (y : β x), γ x y) (x : Sigma β) : γ x.1 x.2 :=
  f x.1 x.2

@[simp]
/-
**Sigma.uncurry_curry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sigma.uncurry_curry {γ : forall a, β a -> Type*} (f : forall x : Sigma β, 
γ x.1 x.2) : Sigma.uncurry (Sigma.curry f) = f
参数：f : forall x : Sigma β, γ x.1 x.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem Sigma.uncurry_curry {γ : ∀ a, β a → Type*} (f : ∀ x : Sigma β, γ x.1 x.2) :
    Sigma.uncurry (Sigma.curry f) = f :=
  funext fun ⟨_, _⟩ ↦ rfl

@[simp]
/-
**Sigma.curry_uncurry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sigma.curry_uncurry {γ : forall a, β a -> Type*} (f : forall (x) (y : β x)
, γ x y) : Sigma.curry (Sigma.uncurry f) = f
参数：f : forall (x) (y : β x), γ x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sigma.curry_uncurry {γ : ∀ a, β a → Type*} (f : ∀ (x) (y : β x), γ x y) :
    Sigma.curry (Sigma.uncurry f) = f :=
  rfl
/-
**Sigma.curry_update** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sigma.curry_update {γ : forall a, β a -> Type*} [DecidableEq α] [forall a,
 DecidableEq (β a)] (i : Σ a, β a) (f : (i : Σ a, β a) -> γ i.1 i.2) (x : γ i.1 
i.2) : Sigma.curry (Function.update f i x) = Function.update (Sigma.curry f) i.1
 (Function.update (Sigma.curry f i.1) i.2 x)
参数：β a；i : Σ a, β a；f : (i : Σ a, β a) -> γ i.1 i.2；x : γ i.1 i.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem Sigma.curry_update {γ : ∀ a, β a → Type*} [DecidableEq α] [∀ a, DecidableEq (β a)]
    (i : Σ a, β a) (f : (i : Σ a, β a) → γ i.1 i.2) (x : γ i.1 i.2) :
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

/-- Convert a product type to a Σ-type. -/
/-
**Prod.toSigma** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Prod.toSigma {α β} (p : α × β) : Σ _ : α, β
参数：p : α × β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a product type to a Σ-type.
-/
def Prod.toSigma {α β} (p : α × β) : Σ _ : α, β :=
  ⟨p.1, p.2⟩

@[simp]
/-
**Prod.fst_comp_toSigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.fst_comp_toSigma {α β} : Sigma.fst ∘ @Prod.toSigma α β = Prod.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Prod.fst_comp_toSigma {α β} : Sigma.fst ∘ @Prod.toSigma α β = Prod.fst :=
  rfl

@[simp]
/-
**Prod.fst_toSigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.fst_toSigma {α β} (x : α × β) : (Prod.toSigma x).fst = x.fst
参数：x : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Prod.fst_toSigma {α β} (x : α × β) : (Prod.toSigma x).fst = x.fst :=
  rfl

@[simp]
/-
**Prod.snd_toSigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.snd_toSigma {α β} (x : α × β) : (Prod.toSigma x).snd = x.snd
参数：x : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Prod.snd_toSigma {α β} (x : α × β) : (Prod.toSigma x).snd = x.snd :=
  rfl

@[simp]
/-
**Prod.toSigma_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.toSigma_mk {α β} (x : α) (y : β) : (x, y).toSigma = ⟨x, y⟩
参数：x : α；y : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Prod.toSigma_mk {α β} (x : α) (y : β) : (x, y).toSigma = ⟨x, y⟩ :=
  rfl
/-
**Prod.toSigma_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.toSigma_injective {α β} : Function.Injective (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Prod.toSigma_injective {α β} : Function.Injective (α := α × β) Prod.toSigma := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp_all

@[simp]
/-
**Prod.toSigma_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.toSigma_inj {α β} {x y : α × β} : x.toSigma = y.toSigma ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Prod.toSigma_injective`：Prod.toSigma_injective {α β} : Function.Injectiv
e (α
-/
theorem Prod.toSigma_inj {α β} {x y : α × β} : x.toSigma = y.toSigma ↔ x = y :=
  Prod.toSigma_injective.eq_iff

end Sigma

namespace PSigma

variable {α : Sort*} {β : α → Sort*}

/-- Nondependent eliminator for `PSigma`. -/
/-
**PSigma.elim** 是 Mathlib 中的一个定义，位于命名空间 `PSigma`。
形式化陈述：elim {γ} (f : forall a, β a -> γ) (a : PSigma β) : γ
参数：f : forall a, β a -> γ；a : PSigma β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Nondependent eliminator for `PSigma`.
-/
def elim {γ} (f : ∀ a, β a → γ) (a : PSigma β) : γ :=
  PSigma.casesOn a f

@[simp]
/-
**PSigma.elim_val** 是 Mathlib 中的一个定理，位于命名空间 `PSigma`。
形式化陈述：elim_val {γ} (f : forall a, β a -> γ) (a b) : PSigma.elim f ⟨a, b⟩ = f a b
参数：f : forall a, β a -> γ；a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem elim_val {γ} (f : ∀ a, β a → γ) (a b) : PSigma.elim f ⟨a, b⟩ = f a b :=
  rfl
/-
**PSigma.** 是 Mathlib 中的一个实例，位于命名空间 `PSigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] [Inhabited (β default)] : Inhabited (PSigma β) :=
  ⟨⟨default, default⟩⟩
/-
**PSigma.decidableEq** 是 Mathlib 中的一个定义，位于命名空间 `PSigma`。
形式化陈述：{α : Sort u_1} → {β : α → Sort u_2} → [h₁ : DecidableEq α] → [h₂ : (a : α)
 → DecidableEq (β a)] → DecidableEq (PSigma β)
参数：a : α；β a；PSigma β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableEq [h₁ : DecidableEq α] [h₂ : ∀ a, DecidableEq (β a)] : DecidableEq (PSigma β)
  | ⟨a₁, b₁⟩, ⟨a₂, b₂⟩ =>
    match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
    | _, b₁, _, b₂, isTrue (Eq.refl _) =>
      match b₁, b₂, h₂ _ b₁ b₂ with
      | _, _, isTrue (Eq.refl _) => isTrue rfl
      | _, _, isFalse n => isFalse fun h ↦
        PSigma.noConfusion rfl .rfl (heq_of_eq h) fun _ e₂ ↦ n (eq_of_heq e₂)
    | _, _, _, _, isFalse n => isFalse fun h ↦
      PSigma.noConfusion rfl .rfl (heq_of_eq h) fun e₁ _ ↦ n (eq_of_heq e₁)
/-
**PSigma.mk.inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `PSigma.mk`。
形式化陈述：∀ {α : Sort u_1} {β : α → Sort u_2} {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}, ⟨
a₁, b₁⟩ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ b₁ ≍ b₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSigma.mk.inj`：∀ {α : Sort u} {β : α → Sort v} {fst : α} {snd : β fst} {
fst_1 : α} {snd_1 : β fst_1},   ⟨fst, snd⟩ = ⟨fst_1, snd_1⟩ → fst = fst_1 ∧ snd 
≍ s…
-/
theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    @PSigma.mk α β a₁ b₁ = @PSigma.mk α β a₂ b₂ ↔ a₁ = a₂ ∧ b₁ ≍ b₂ :=
  (Iff.intro PSigma.mk.inj) fun ⟨h₁, h₂⟩ ↦
    match a₁, a₂, b₁, b₂, h₁, h₂ with
    | _, _, _, _, Eq.refl _, HEq.refl _ => rfl

-- This should not be a simp lemma, since its discrimination tree key would just be `→`.
/-
**PSigma.** 是 Mathlib 中的一个定理，位于命名空间 `PSigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem «forall» {p : (Σ' a, β a) → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b ↦ h ⟨a, b⟩, fun h ⟨a, b⟩ ↦ h a b⟩
/-
**PSigma.** 是 Mathlib 中的一个引理，位于命名空间 `PSigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma «exists» {p : (Σ' a, β a) → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ ↦ ⟨a, b, h⟩, fun ⟨a, b, h⟩ ↦ ⟨⟨a, b⟩, h⟩⟩

/-- A specialized ext lemma for equality of `PSigma` types over an indexed subtype. -/
@[ext]
/-
**PSigma.subtype_ext** 是 Mathlib 中的一个定理，位于命名空间 `PSigma`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_3} {p : α → β → Prop} {x₀ x₁ : (a : α) ×' Sub
type (p a)},   x₀.fst = x₁.fst → ↑x₀.snd = ↑x₁.snd → x₀ = x₁
参数：a : α；p a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A specialized ext lemma for equality of `PSigma` types over an indexed subtype.
-/
theorem subtype_ext {β : Sort*} {p : α → β → Prop} :
    ∀ {x₀ x₁ : Σ' a, Subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

variable {α₁ : Sort*} {α₂ : Sort*} {β₁ : α₁ → Sort*} {β₂ : α₂ → Sort*}

/-- Map the left and right components of a sigma -/
/-
**PSigma.map** 是 Mathlib 中的一个定义，位于命名空间 `PSigma`。
形式化陈述：{α₁ : Sort u_3} →   {α₂ : Sort u_4} →     {β₁ : α₁ → Sort u_5} → {β₂ : α₂ 
→ Sort u_6} → (f₁ : α₁ → α₂) → ((a : α₁) → β₁ a → β₂ (f₁ a)) → PSigma β₁ → PSigm
a β₂
参数：f₁ : α₁ → α₂；(a : α₁) → β₁ a → β₂ (f₁ a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map the left and right components of a sigma
-/
def map (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) : PSigma β₁ → PSigma β₂
  | ⟨a, b⟩ => ⟨f₁ a, f₂ a b⟩

end PSigma

