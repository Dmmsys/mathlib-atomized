/-
Copyright (c) 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Data.Set.Basic

/-!
# Bundle

Basic data structure to implement fiber bundles, vector bundles (maybe fibrations?), etc. This file
should contain all possible results that do not involve any topology.

We represent a bundle `E` over a base space `B` as a dependent type `E : B → Type*`.

We define `Bundle.TotalSpace F E` to be the type of pairs `⟨b, x⟩`, where `b : B` and `x : E b`.
This type is isomorphic to `Σ x, E x` and uses an extra argument `F` for reasons explained below. In
general, the constructions of fiber bundles we will make will be of this form.

## Main Definitions

* `Bundle.TotalSpace` the total space of a bundle.
* `Bundle.TotalSpace.proj` the projection from the total space to the base space.
* `Bundle.TotalSpace.mk` the constructor for the total space.

## Implementation Notes

- We use a custom structure for the total space of a bundle instead of using a type synonym for the
  canonical disjoint union `Σ x, E x` because the total space usually has a different topology and
  Lean 4 `simp` fails to apply lemmas about `Σ x, E x` to elements of the total space.

- The definition of `Bundle.TotalSpace` has an unused argument `F`. The reason is that in some
  constructions (e.g., the bundle of continuous linear maps) we need access to the atlas of
  trivializations of original fiber bundles to construct the topology on the total space of the new
  fiber bundle.

## References
- https://en.wikipedia.org/wiki/Bundle_(mathematics)
-/

@[expose] public section

assert_not_exists RelIso

open Function Set

namespace Bundle

variable {B F : Type*} (E : B → Type*)

/-- `Bundle.TotalSpace F E` is the total space of the bundle. It consists of pairs
`(proj : B, snd : E proj)`.
-/
@[ext]
/-
**Bundle.TotalSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 `Bundle`。
形式化陈述：{B : Type u_1} → Type u_4 → (B → Type u_5) → Type (max u_1 u_5)
参数：B → Type u_5；max u_1 u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Bundle.TotalSpace F E` is the total space of the bundle. It consists of pairs
`(proj : B, snd : E proj)`.
-/
structure TotalSpace (F : Type*) (E : B → Type*) where
  /-- `Bundle.TotalSpace.proj` is the canonical projection `Bundle.TotalSpace F E → B` from the
  total space to the base space. -/
  proj : B
  snd : E proj
/-
**Bundle.** 是 Mathlib 中的一个实例，位于命名空间 `Bundle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited B] [Inhabited (E default)] : Inhabited (TotalSpace F E) :=
  ⟨⟨default, default⟩⟩

variable {E}

@[inherit_doc]
scoped notation:max "π " F':max E':max => Bundle.TotalSpace.proj (F := F') (E := E')
/-
**Bundle.TotalSpace.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.TotalSpace`。
形式化陈述：{B : Type u_1} → {E : B → Type u_3} → (F : Type u_4) → (x : B) → E x → Bun
dle.TotalSpace F E
参数：F : Type u_4；x : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev TotalSpace.mk' (F : Type*) (x : B) (y : E x) : TotalSpace F E := ⟨x, y⟩
/-
**Bundle.TotalSpace.mk_cast** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.TotalSpace`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} {x x' : B} (h : x = x')
 (b : E x), ⟨x', cast ⋯ b⟩ = ⟨x, b⟩
参数：h : x = x'；b : E x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem TotalSpace.mk_cast {x x' : B} (h : x = x') (b : E x) :
    .mk' F x' (cast (congr_arg E h) b) = TotalSpace.mk x b := by subst h; rfl

@[simp 1001, mfld_simps 1001]
/-
**Bundle.TotalSpace.mk_inj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.TotalSpace`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} {b : B} {y y' : E b}, ⟨
b, y⟩ = ⟨b, y'⟩ ↔ y = y'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem TotalSpace.mk_inj {b : B} {y y' : E b} : mk' F b y = mk' F b y' ↔ y = y' := by
  simp [TotalSpace.ext_iff]
/-
**Bundle.TotalSpace.mk_injective** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.TotalSpace`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} (b : B), Function.Injec
tive (Bundle.TotalSpace.mk b)
参数：b : B；Bundle.TotalSpace.mk b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bundle.TotalSpace.mk_inj`：∀ {B : Type u_1} {F : Type u_2} {E : B → Type 
u_3} {b : B} {y y' : E b}, ⟨b, y⟩ = ⟨b, y'⟩ ↔ y = y'
-/
theorem TotalSpace.mk_injective (b : B) : Injective (mk b : E b → TotalSpace F E) := fun _ _ ↦
  mk_inj.1
/-
**Bundle.** 是 Mathlib 中的一个实例，位于命名空间 `Bundle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {x : B} : CoeTC (E x) (TotalSpace F E) :=
  ⟨TotalSpace.mk x⟩
/-
**Bundle.TotalSpace.eta** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.TotalSpace`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} (z : Bundle.TotalSpace 
F E), ⟨z.proj, z.snd⟩ = z
参数：z : Bundle.TotalSpace F E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem TotalSpace.eta (z : TotalSpace F E) : TotalSpace.mk z.proj z.2 = z := rfl

@[simp]
/-
**Bundle.TotalSpace.exists** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.TotalSpace`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} {p : Bundle.TotalSpace 
F E → Prop}, (∃ x, p x) ↔ ∃ b y, p ⟨b, y⟩
参数：∃ x, p x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem TotalSpace.exists {p : TotalSpace F E → Prop} : (∃ x, p x) ↔ ∃ b y, p ⟨b, y⟩ :=
  ⟨fun ⟨x, hx⟩ ↦ ⟨x.1, x.2, hx⟩, fun ⟨b, y, h⟩ ↦ ⟨⟨b, y⟩, h⟩⟩

@[simp]
/-
**Bundle.TotalSpace.range_mk** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.TotalSpace`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} (b : B),   Set.range (B
undle.TotalSpace.mk b) = Bundle.TotalSpace.proj ⁻¹' {b}
参数：b : B；Bundle.TotalSpace.mk b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
-/
theorem TotalSpace.range_mk (b : B) : range ((↑) : E b → TotalSpace F E) = π F E ⁻¹' {b} := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    rfl
  · rintro ⟨_, x⟩ rfl
    exact ⟨x, rfl⟩

/-- Notation for the direct sum of two bundles over the same base. -/
notation:100 E₁ " ×ᵇ " E₂ => fun x => E₁ x × E₂ x

/-- `Bundle.Trivial B F` is the trivial bundle over `B` of fiber `F`. -/
@[reducible, nolint unusedArguments]
/-
**Bundle.Trivial** 是 Mathlib 中的一个定义，位于命名空间 `Bundle`。
形式化陈述：Trivial (B : Type*) (F : Type*) : B -> Type _
参数：B : Type*；F : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Bundle.Trivial B F` is the trivial bundle over `B` of fiber `F`.
-/
def Trivial (B : Type*) (F : Type*) : B → Type _ := fun _ => F

/-- The trivial bundle, unlike other bundles, has a canonical projection on the fiber. -/
/-
**Bundle.TotalSpace.trivialSnd** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.TotalSpace`。
形式化陈述：(B : Type u_4) → (F : Type u_5) → Bundle.TotalSpace F (Bundle.Trivial B F)
 → F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial bundle, unlike other bundles, has a canonical projection on the fibe
r.
-/
def TotalSpace.trivialSnd (B : Type*) (F : Type*) : TotalSpace F (Bundle.Trivial B F) → F :=
  TotalSpace.snd

/-- A trivial bundle is equivalent to the product `B × F`. -/
@[simps (attr := mfld_simps)]
/-
**Bundle.TotalSpace.toProd** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.TotalSpace`。
形式化陈述：(B : Type u_4) → (F : Type u_5) → (Bundle.TotalSpace F fun x => F) ≃ B × F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A trivial bundle is equivalent to the product `B × F`.
-/
def TotalSpace.toProd (B F : Type*) : (TotalSpace F fun _ : B => F) ≃ B × F where
  toFun x := (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩

section Pullback

variable {B' : Type*}

/-- The pullback of a bundle `E` over a base `B` under a map `f : B' → B`, denoted by
`Bundle.Pullback f E` or `f *ᵖ E`, is the bundle over `B'` whose fiber over `b'` is `E (f b')`. -/
/-
**Bundle.Pullback** 是 Mathlib 中的一个定义，位于命名空间 `Bundle`。
形式化陈述：Pullback (f : B' -> B) (E : B -> Type*) : B' -> Type _
参数：f : B' -> B；E : B -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a bundle `E` over a base `B` under a map `f : B' → B`, denoted b
y
`Bundle.Pullback f E` or `f *ᵖ E`, is the bundle over `B'` whose fiber over `b'`
 is `E (f b')`.
-/
def Pullback (f : B' → B) (E : B → Type*) : B' → Type _ := fun x => E (f x)

@[inherit_doc]
notation f " *ᵖ " E:arg => Pullback f E
/-
**Bundle.** 是 Mathlib 中的一个实例，位于命名空间 `Bundle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : B' → B} {x : B'} [Nonempty (E (f x))] : Nonempty ((f *ᵖ E) x) :=
  ‹Nonempty (E (f x))›

/-- Natural embedding of the total space of `f *ᵖ E` into `B' × TotalSpace F E`. -/
@[simp]
/-
**Bundle.pullbackTotalSpaceEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Bundle`。
形式化陈述：pullbackTotalSpaceEmbedding (f : B' -> B) : TotalSpace F (f *ᵖ E) -> B' × 
TotalSpace F E
参数：f : B' -> B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Natural embedding of the total space of `f *ᵖ E` into `B' × TotalSpace F E`.
-/
def pullbackTotalSpaceEmbedding (f : B' → B) : TotalSpace F (f *ᵖ E) → B' × TotalSpace F E :=
  fun z => (z.proj, TotalSpace.mk (f z.proj) z.2)

/-- The base map `f : B' → B` lifts to a canonical map on the total spaces. -/
@[simps (attr := mfld_simps)]
/-
**Bundle.Pullback.lift** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pullback`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {E : B → Type u_3} → {B' : Type u_
4} → (f : B' → B) → Bundle.TotalSpace F (f *ᵖ E) → Bundle.TotalSpace F E
参数：f : B' → B；f *ᵖ E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base map `f : B' → B` lifts to a canonical map on the total spaces.
-/
def Pullback.lift (f : B' → B) : TotalSpace F (f *ᵖ E) → TotalSpace F E := fun z => ⟨f z.proj, z.2⟩

@[simp, mfld_simps]
/-
**Bundle.Pullback.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pullback`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} {B' : Type u_4} (f : B'
 → B) (x : B') (y : E (f x)),   Bundle.Pullback.lift f ⟨x, y⟩ = ⟨f x, y⟩
参数：f : B' → B；x : B'；y : E (f x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pullback.lift_mk (f : B' → B) (x : B') (y : E (f x)) :
    Pullback.lift f (.mk' F x y) = ⟨f x, y⟩ :=
  rfl

end Pullback

end Bundle

