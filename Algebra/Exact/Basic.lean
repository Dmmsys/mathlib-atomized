/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Exactness of a pair

* For two maps `f : M → N` and `g : N → P`, with `Zero P`,
  `Function.Exact f g` says that `Set.range f = Set.preimage g {0}`

* For two maps `f : M → N` and `g : N → P`, with `One P`,
  `Function.MulExact f g` says that `Set.range f = Set.preimage g {1}`

* For additive maps `f : M →+ N`  and `g : N →+ P`,
  `Exact f g` says that `range f = ker g`

* For multiplicative maps `f : M →* N`  and `g : N →* P`,
  `MulExact f g` says that `range f = ker g`

* For linear maps `f : M →ₗ[R] N`  and `g : N →ₗ[R] P`,
  `Exact f g` says that `range f = ker g`

## TODO :

* generalize to `SemilinearMap`, even `SemilinearMapClass`
-/

@[expose] public section

variable {R M M' N N' P P' : Type*}

namespace Function

variable (f : M → N) (g : N → P) (g' : P → P')

/-- The maps `f` and `g` form an exact pair: `g y = 1` iff `y` belongs to the image of `f`. -/
@[to_additive /-- The maps `f` and `g` form an exact pair:
  `g y = 0` iff `y` belongs to the image of `f`. -/]
/-
**Function.MulExact** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：MulExact [One P] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulExact [One P] : Prop := ∀ y, g y = 1 ↔ y ∈ Set.range f

variable {f g}

namespace MulExact

@[to_additive]
/-
**Function.MulExact.apply_apply_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Function.MulEx
act`。
形式化陈述：apply_apply_eq_one [One P] (h : MulExact f g) (x : M) : g (f x) = 1
参数：h : MulExact f g；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
lemma apply_apply_eq_one [One P] (h : MulExact f g) (x : M) :
    g (f x) = 1 := (h _).mpr <| Set.mem_range_self _

@[to_additive]
/-
**Function.MulExact.comp_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Function.MulExact`。
形式化陈述：comp_eq_one [One P] (h : MulExact f g) : g.comp f = 1
参数：h : MulExact f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Function.MulExact.apply_apply_eq_one`：apply_apply_eq_one [One P] (h : Mu
lExact f g) (x : M) : g (f x) = 1
-/
lemma comp_eq_one [One P] (h : MulExact f g) : g.comp f = 1 :=
  funext h.apply_apply_eq_one

@[to_additive]
/-
**Function.MulExact.of_comp_of_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `Function.Mul
Exact`。
形式化陈述：of_comp_of_mem_range [One P] (h1 : g ∘ f = 1) (h2 : forall x, g x = 1 -> x
 in Set.range f) : MulExact f g
参数：h1 : g ∘ f = 1；h2 : forall x, g x = 1 -> x in Set.range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `forall_apply_eq_imp_iff`：∀ {α : Sort u_2} {β : Sort u_1} {f : α → β} {p 
: β → Prop}, (∀ (b : β) (a : α), f a = b → p b) ↔ ∀ (a : α), p (f a)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma of_comp_of_mem_range [One P] (h1 : g ∘ f = 1)
    (h2 : ∀ x, g x = 1 → x ∈ Set.range f) : MulExact f g :=
  fun y => Iff.intro (h2 y) <|
    Exists.rec ((forall_apply_eq_imp_iff (p := (g · = 1))).mpr (congrFun h1) y)

@[to_additive]
/-
**Function.MulExact.comp_injective** 是 Mathlib 中的一个引理，位于命名空间 `Function.MulExact`
。
形式化陈述：comp_injective [One P] [One P'] (mulExact : MulExact f g) (inj : Function.
Injective g') (h0 : g' 1 = 1) : MulExact f (g' ∘ g)
参数：mulExact : MulExact f g；inj : Function.Injective g'；h0 : g' 1 = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma comp_injective [One P] [One P'] (mulExact : MulExact f g)
    (inj : Function.Injective g') (h0 : g' 1 = 1) :
    MulExact f (g' ∘ g) := by
  intro x
  refine ⟨fun H => mulExact x |>.mp <| inj <| h0 ▸ H, ?_⟩
  intro H
  rw [Function.comp_apply, mulExact x |>.mpr H, h0]

@[to_additive]
/-
**Function.MulExact.of_comp_eq_one_of_ker_in_range** 是 Mathlib 中的一个引理，位于命名空间 `Fu
nction.MulExact`。
形式化陈述：of_comp_eq_one_of_ker_in_range [One P] (hc : g.comp f = 1) (hr : forall y,
 g y = 1 -> y in Set.range f) : MulExact f g
参数：hc : g.comp f = 1；hr : forall y, g y = 1 -> y in Set.range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma of_comp_eq_one_of_ker_in_range [One P] (hc : g.comp f = 1)
    (hr : ∀ y, g y = 1 → y ∈ Set.range f) :
    MulExact f g :=
  fun y ↦ ⟨hr y, fun ⟨x, hx⟩ ↦ hx ▸ congrFun hc x⟩

/-- Two maps `f : M → N` and `g : N → P` are exact if and only if the induced maps
`Set.range f → N → Set.range g` are exact.

Note that if you already have an instance `[One (Set.range g)]` (which is unlikely) this lemma
may not apply if the one of `Set.range g` is not definitionally equal to `⟨1, hg⟩`. -/
@[to_additive /-- Two maps `f : M → N` and `g : N → P` are exact if and only if the induced maps
`Set.range f → N → Set.range g` are exact.

Note that if you already have an instance `[Zero (Set.range g)]` (which is unlikely) this lemma
may not apply if the zero of `Set.range g` is not definitionally equal to `⟨0, hg⟩`. -/]
/-
**Function.MulExact.iff_rangeFactorization** 是 Mathlib 中的一个引理，位于命名空间 `Function.M
ulExact`。
形式化陈述：iff_rangeFactorization [One P] (hg : 1 in Set.range g) : letI : One (Set.r
ange g)
参数：hg : 1 in Set.range g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iff_rangeFactorization [One P] (hg : 1 ∈ Set.range g) :
    letI : One (Set.range g) := ⟨⟨1, hg⟩⟩
    MulExact f g ↔ MulExact ((↑) : Set.range f → N) (Set.rangeFactorization g) := by
  let : One (Set.range g) := ⟨⟨1, hg⟩⟩
  have : ((1 : Set.range g) : P) = 1 := rfl
  simp [MulExact, Subtype.ext_iff, this]

/-- If two maps `f : M → N` and `g : N → P` are exact, then the induced maps
`Set.range f → N → Set.range g` are exact.

Note that if you already have an instance `[One (Set.range g)]` (which is unlikely) this lemma
may not apply if the one of `Set.range g` is not definitionally equal to `⟨1, hg⟩`. -/
@[to_additive /-- If two maps `f : M → N` and `g : N → P` are exact, then the induced maps
`Set.range f → N → Set.range g` are exact.

Note that if you already have an instance `[Zero (Set.range g)]` (which is unlikely) this lemma
may not apply if the zero of `Set.range g` is not definitionally equal to `⟨0, hg⟩`. -/]
/-
**Function.MulExact.rangeFactorization** 是 Mathlib 中的一个引理，位于命名空间 `Function.MulEx
act`。
形式化陈述：rangeFactorization [One P] (h : MulExact f g) (hg : 1 in Set.range g) : le
tI : One (Set.range g)
参数：h : MulExact f g；hg : 1 in Set.range g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Function.MulExact.iff_rangeFactorization`：iff_rangeFactorization [One P]
 (hg : 1 in Set.range g) : letI : One (Set.range g)
-/
lemma rangeFactorization [One P] (h : MulExact f g) (hg : 1 ∈ Set.range g) :
    letI : One (Set.range g) := ⟨⟨1, hg⟩⟩
    MulExact ((↑) : Set.range f → N) (Set.rangeFactorization g) :=
  (iff_rangeFactorization hg).1 h

end MulExact

end Function

section MonoidHom

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

namespace MonoidHom

open Function

@[to_additive]
/-
**MonoidHom.mulExact_iff** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：mulExact_iff : MulExact f g ↔ ker g = range f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
lemma mulExact_iff :
    MulExact f g ↔ ker g = range f :=
  Iff.symm SetLike.ext_iff

@[to_additive]
/-
**MonoidHom.mulExact_of_comp_eq_one_of_ker_le_range** 是 Mathlib 中的一个引理，位于命名空间 `M
onoidHom`。
形式化陈述：mulExact_of_comp_eq_one_of_ker_le_range (h1 : g.comp f = 1) (h2 : ker g <=
 range f) : MulExact f g
参数：h1 : g.comp f = 1；h2 : ker g <= range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.MulExact.of_comp_of_mem_range`：of_comp_of_mem_range [One P] (h1
 : g ∘ f = 1) (h2 : forall x, g x = 1 -> x in Set.range f) : MulExact f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma mulExact_of_comp_eq_one_of_ker_le_range
    (h1 : g.comp f = 1) (h2 : ker g ≤ range f) : MulExact f g :=
  MulExact.of_comp_of_mem_range (congrArg DFunLike.coe h1) h2

@[to_additive]
/-
**MonoidHom.mulExact_of_comp_of_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：mulExact_of_comp_of_mem_range (h1 : g.comp f = 1) (h2 : forall x, g x = 1 
-> x in range f) : MulExact f g
参数：h1 : g.comp f = 1；h2 : forall x, g x = 1 -> x in range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidHom.mulExact_of_comp_eq_one_of_ker_le_range`：mulExact_of_comp_eq_o
ne_of_ker_le_range (h1 : g.comp f = 1) (h2 : ker g <= range f) : MulExact f g
-/
lemma mulExact_of_comp_of_mem_range
    (h1 : g.comp f = 1) (h2 : ∀ x, g x = 1 → x ∈ range f) : MulExact f g :=
  mulExact_of_comp_eq_one_of_ker_le_range h1 h2

/-- When we have a commutative diagram from a sequence of two maps to another,
such that the left vertical map is surjective, the middle vertical map is bijective and the right
vertical map is injective, then the upper row is exact iff the lower row is.
See `ShortComplex.exact_iff_of_epi_of_isIso_of_mono` in the file
`Mathlib/Algebra/Homology/ShortComplex/Exact.lean` for the categorical version of this result. -/
@[to_additive /-- When we have a commutative diagram from a sequence of two maps to another,
such that the left vertical map is surjective, the middle vertical map is bijective and the right
vertical map is injective, then the upper row is exact iff the lower row is.
See `ShortComplex.exact_iff_of_epi_of_isIso_of_mono` in the file
`Mathlib/Algebra/Homology/ShortComplex/Exact.lean` for the categorical version of this result. -/]
/-
**MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective** 是 Mathlib 中的一
个引理，位于命名空间 `MonoidHom`。
形式化陈述：mulExact_iff_of_surjective_of_bijective_of_injective {M₁ M₂ M₃ N₁ N₂ N₃ : 
Type*} [CommMonoid M₁] [CommMonoid M₂] [CommMonoid M₃] [CommMonoid N₁] [CommMono
id N₂] [CommMonoid N₃] (f : M₁ ->* M₂) (g : M₂ ->* M₃) (f' : N₁ ->* N₂) (g' : N₂
 ->* N₃) (τ₁ : M₁ ->* N₁) (τ₂ : M₂ ->* N₂) (τ₃ : M₃ ->* N₃) (comm₁₂ : f'.comp τ₁
 = τ₂.comp f) (comm₂₃ : g'.comp τ₂ = τ₃.comp g) (h₁ : Function.Surjective τ₁) (h
₂ : Function.Bijective τ₂) (h₃ : Function.Injective τ₃) : MulExact f g ↔ MulExac
t f' g'
参数：f : M₁ ->* M₂；g : M₂ ->* M₃；f' : N₁ ->* N₂；g' : N₂ ->* N₃；τ₁ : M₁ ->* N₁；τ₂ :
 M₂ ->* N₂；τ₃ : M₃ ->* N₃；comm₁₂ : f'.comp τ₁ = τ₂.comp f；comm₂₃ : g'.comp τ₂ = 
τ₃.comp g；h₁ : Function.Surjective τ₁；h₂ : Function.Bijective τ₂；h₃ : Function.I
njective τ₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.MulExact.apply_apply_eq_one`：apply_apply_eq_one [One P] (h : Mu
lExact f g) (x : M) : g (f x) = 1
-/
lemma mulExact_iff_of_surjective_of_bijective_of_injective
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [CommMonoid M₁] [CommMonoid M₂] [CommMonoid M₃]
    [CommMonoid N₁] [CommMonoid N₂] [CommMonoid N₃]
    (f : M₁ →* M₂) (g : M₂ →* M₃) (f' : N₁ →* N₂) (g' : N₂ →* N₃)
    (τ₁ : M₁ →* N₁) (τ₂ : M₂ →* N₂) (τ₃ : M₃ →* N₃)
    (comm₁₂ : f'.comp τ₁ = τ₂.comp f)
    (comm₂₃ : g'.comp τ₂ = τ₃.comp g)
    (h₁ : Function.Surjective τ₁) (h₂ : Function.Bijective τ₂) (h₃ : Function.Injective τ₃) :
    MulExact f g ↔ MulExact f' g' := by
  replace comm₁₂ := DFunLike.congr_fun comm₁₂
  replace comm₂₃ := DFunLike.congr_fun comm₂₃
  dsimp at comm₁₂ comm₂₃
  constructor
  · intro h y₂
    obtain ⟨x₂, rfl⟩ := h₂.2 y₂
    constructor
    · intro hx₂
      obtain ⟨x₁, rfl⟩ := (h x₂).1 (h₃ (by simpa only [map_one, comm₂₃] using hx₂))
      exact ⟨τ₁ x₁, by simp only [comm₁₂]⟩
    · rintro ⟨y₁, hy₁⟩
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      rw [comm₂₃, (h x₂).2 _, map_one]
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
  · intro h x₂
    constructor
    · intro hx₂
      obtain ⟨y₁, hy₁⟩ := (h (τ₂ x₂)).1 (by simp only [comm₂₃, hx₂, map_one])
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
    · rintro ⟨x₁, rfl⟩
      apply h₃
      simp only [← comm₁₂, ← comm₂₃, h.apply_apply_eq_one (τ₁ x₁), map_one]

end MonoidHom

namespace Function.MulExact

open MonoidHom

@[to_additive]
/-
**Function.MulExact.monoidHom_ker_eq** 是 Mathlib 中的一个引理，位于命名空间 `Function.MulExac
t`。
形式化陈述：monoidHom_ker_eq (hfg : MulExact f g) : ker g = range f
参数：hfg : MulExact f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
lemma monoidHom_ker_eq (hfg : MulExact f g) :
    ker g = range f :=
  SetLike.ext hfg

@[to_additive]
/-
**Function.MulExact.monoidHom_comp_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Function.M
ulExact`。
形式化陈述：monoidHom_comp_eq_zero (h : MulExact f g) : g.comp f = 1
参数：h : MulExact f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用引理 `Function.MulExact.comp_eq_one`：comp_eq_one [One P] (h : MulExact f g) : 
g.comp f = 1
-/
lemma monoidHom_comp_eq_zero (h : MulExact f g) : g.comp f = 1 :=
  DFunLike.coe_injective h.comp_eq_one

section

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommMonoid X₁] [CommMonoid X₂] [CommMonoid X₃]
  [CommMonoid Y₁] [CommMonoid Y₂] [CommMonoid Y₃]
  (e₁ : X₁ ≃* Y₁) (e₂ : X₂ ≃* Y₂) (e₃ : X₃ ≃* Y₃)
  {f₁₂ : X₁ →* X₂} {f₂₃ : X₂ →* X₃} {g₁₂ : Y₁ →* Y₂} {g₂₃ : Y₂ →* Y₃}

@[to_additive]
/-
**Function.MulExact.iff_of_ladder_mulEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Function.M
ulExact`。
形式化陈述：iff_of_ladder_mulEquiv (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂) (com
m₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) : MulExact g₁₂ g₂₃ ↔ MulExact f₁₂ f₂₃
参数：comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂；comm₂₃ : g₂₃.comp e₂ = MonoidHom
.comp e₃ f₂₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective`：mulExact
_iff_of_surjective_of_bijective_of_injective {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [CommMo
noid M₁] [CommMonoid M₂] [CommMonoid M₃] [CommMonoid…
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `MulEquiv.bijective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Bijective ⇑e
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
-/
lemma iff_of_ladder_mulEquiv (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) : MulExact g₁₂ g₂₃ ↔ MulExact f₁₂ f₂₃ :=
  (mulExact_iff_of_surjective_of_bijective_of_injective _ _ _ _ e₁ e₂ e₃ comm₁₂ comm₂₃
    e₁.surjective e₂.bijective e₃.injective).symm

@[to_additive]
/-
**Function.MulExact.of_ladder_mulEquiv_of_mulExact** 是 Mathlib 中的一个引理，位于命名空间 `Fu
nction.MulExact`。
形式化陈述：of_ladder_mulEquiv_of_mulExact (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f
₁₂) (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) (H : MulExact f₁₂ f₂₃) : MulE
xact g₁₂ g₂₃
参数：comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂；comm₂₃ : g₂₃.comp e₂ = MonoidHom
.comp e₃ f₂₃；H : MulExact f₁₂ f₂₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Function.MulExact.iff_of_ladder_mulEquiv`：iff_of_ladder_mulEquiv (comm₁₂
 : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂) (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e
₃ f₂₃) : MulExact g₁₂ g₂₃ ↔ Mu…
-/
lemma of_ladder_mulEquiv_of_mulExact (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) (H : MulExact f₁₂ f₂₃) : MulExact g₁₂ g₂₃ :=
  (iff_of_ladder_mulEquiv _ _ _ comm₁₂ comm₂₃).2 H

@[to_additive]
/-
**Function.MulExact.of_ladder_mulEquiv_of_mulExact'** 是 Mathlib 中的一个引理，位于命名空间 `F
unction.MulExact`。
形式化陈述：of_ladder_mulEquiv_of_mulExact' (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ 
f₁₂) (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) (H : MulExact g₁₂ g₂₃) : Mul
Exact f₁₂ f₂₃
参数：comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂；comm₂₃ : g₂₃.comp e₂ = MonoidHom
.comp e₃ f₂₃；H : MulExact g₁₂ g₂₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Function.MulExact.iff_of_ladder_mulEquiv`：iff_of_ladder_mulEquiv (comm₁₂
 : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂) (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e
₃ f₂₃) : MulExact g₁₂ g₂₃ ↔ Mu…
-/
lemma of_ladder_mulEquiv_of_mulExact' (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) (H : MulExact g₁₂ g₂₃) : MulExact f₁₂ f₂₃ :=
  (iff_of_ladder_mulEquiv _ _ _ comm₁₂ comm₂₃).1 H

end

/-- Two maps `f : M →* N` and `g : N →* P` are exact if and only if the induced maps
`MonoidHom.range f → N → MonoidHom.range g` are exact. -/
@[to_additive /-- Two maps `f : M →+ N` and `g : N →+ P` are exact if and only if the induced maps
`AddMonoidHom.range f → N → AddMonoidHom.range g` are exact. -/]
/-
**Function.MulExact.iff_monoidHom_rangeRestrict** 是 Mathlib 中的一个引理，位于命名空间 `Funct
ion.MulExact`。
形式化陈述：iff_monoidHom_rangeRestrict : MulExact f g ↔ MulExact f.range.subtype g.ra
ngeRestrict
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.MulExact.iff_rangeFactorization`：iff_rangeFactorization [One P]
 (hg : 1 in Set.range g) : letI : One (Set.range g)
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
lemma iff_monoidHom_rangeRestrict :
    MulExact f g ↔ MulExact f.range.subtype g.rangeRestrict :=
  iff_rangeFactorization (one_mem g.range)

@[to_additive]
alias ⟨monoidHom_rangeRestrict, _⟩ := iff_monoidHom_rangeRestrict

end Function.MulExact

end MonoidHom

section LinearMap

open Function

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

namespace LinearMap

/-
**LinearMap.exact_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap.range f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
lemma exact_iff :
    Exact f g ↔ LinearMap.ker g = LinearMap.range f :=
  Iff.symm SetLike.ext_iff
/-
**LinearMap.exact_of_comp_eq_zero_of_ker_le_range** 是 Mathlib 中的一个引理，位于命名空间 `Lin
earMap`。
形式化陈述：exact_of_comp_eq_zero_of_ker_le_range (h1 : g ∘ₗ f = 0) (h2 : ker g <= ran
ge f) : Exact f g
参数：h1 : g ∘ₗ f = 0；h2 : ker g <= range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Exact.of_comp_of_mem_range`：∀ {M : Type u_2} {N : Type u_4} {P 
: Type u_6} {f : M → N} {g : N → P} [inst : Zero P],   g ∘ f = 0 → (∀ (x : N), g
 x = 0 → x ∈ Set.range f)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma exact_of_comp_eq_zero_of_ker_le_range
    (h1 : g ∘ₗ f = 0) (h2 : ker g ≤ range f) : Exact f g :=
  Exact.of_comp_of_mem_range (congrArg DFunLike.coe h1) h2
/-
**LinearMap.exact_of_comp_of_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：exact_of_comp_of_mem_range (h1 : g ∘ₗ f = 0) (h2 : forall x, g x = 0 -> x 
in range f) : Exact f g
参数：h1 : g ∘ₗ f = 0；h2 : forall x, g x = 0 -> x in range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.exact_of_comp_eq_zero_of_ker_le_range`：exact_of_comp_eq_zero_o
f_ker_le_range (h1 : g ∘ₗ f = 0) (h2 : ker g <= range f) : Exact f g
-/
lemma exact_of_comp_of_mem_range
    (h1 : g ∘ₗ f = 0) (h2 : ∀ x, g x = 0 → x ∈ range f) : Exact f g :=
  exact_of_comp_eq_zero_of_ker_le_range h1 h2

section Ring

variable {R M N P : Type*} [Ring R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]

/-
**LinearMap.exact_subtype_mkQ** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：exact_subtype_mkQ (Q : Submodule R N) : Exact (Submodule.subtype Q) (Submo
dule.mkQ Q)
参数：Q : Submodule R N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
-/
lemma exact_subtype_mkQ (Q : Submodule R N) :
    Exact (Submodule.subtype Q) (Submodule.mkQ Q) := by
  rw [exact_iff, Submodule.ker_mkQ, Submodule.range_subtype Q]
/-
**LinearMap.exact_map_mkQ_range** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：exact_map_mkQ_range (f : M ->ₗ[R] N) : Exact f (Submodule.mkQ (range f))
参数：f : M ->ₗ[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
-/
lemma exact_map_mkQ_range (f : M →ₗ[R] N) :
    Exact f (Submodule.mkQ (range f)) :=
  exact_iff.mpr <| Submodule.ker_mkQ _
/-
**LinearMap.exact_subtype_ker_map** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：exact_subtype_ker_map (g : N ->ₗ[R] P) : Exact (Submodule.subtype (ker g))
 g
参数：g : N ->ₗ[R] P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
-/
lemma exact_subtype_ker_map (g : N →ₗ[R] P) :
    Exact (Submodule.subtype (ker g)) g :=
  exact_iff.mpr <| (Submodule.range_subtype _).symm

@[simp]
/-
**LinearMap.exact_zero_iff_injective** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：exact_zero_iff_injective {M N : Type*} (P : Type*) [AddCommGroup M] [AddCo
mmGroup N] [AddCommMonoid P] [Module R N] [Module R M] [Module R P] (f : M ->ₗ[R
] N) : Function.Exact (0 : P ->ₗ[R] M) f ↔ Function.Injective f
参数：P : Type*；f : M ->ₗ[R] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_zero`：range_zero [RingHomSurjective τ₁₂] : range (0 : M 
->ₛₗ[τ₁₂] M₂) = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma exact_zero_iff_injective {M N : Type*} (P : Type*)
    [AddCommGroup M] [AddCommGroup N] [AddCommMonoid P] [Module R N] [Module R M]
    [Module R P] (f : M →ₗ[R] N) :
    Function.Exact (0 : P →ₗ[R] M) f ↔ Function.Injective f := by
  simp [← ker_eq_bot, exact_iff]

end Ring

@[simp]
/-
**LinearMap.exact_zero_iff_surjective** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：exact_zero_iff_surjective {M N : Type*} (P : Type*) [AddCommGroup M] [AddC
ommGroup N] [AddCommMonoid P] [Module R N] [Module R M] [Module R P] (f : M ->ₗ[
R] N) : Function.Exact f (0 : N ->ₗ[R] P) ↔ Function.Surjective f
参数：P : Type*；f : M ->ₗ[R] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_zero`：ker_zero : ker (0 : M ->ₛₗ[τ₁₂] M₂) = ⊤
· 使用定理 `eq_comm_eq`：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma exact_zero_iff_surjective {M N : Type*} (P : Type*)
    [AddCommGroup M] [AddCommGroup N] [AddCommMonoid P] [Module R N] [Module R M]
    [Module R P] (f : M →ₗ[R] N) :
    Function.Exact f (0 : N →ₗ[R] P) ↔ Function.Surjective f := by
  simp [range_eq_top, exact_iff, eqComm]

end LinearMap

variable (f g) in
/-
**LinearEquiv.conj_exact_iff_exact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearEquiv.conj_exact_iff_exact (e : N ≃ₗ[R] N') : Function.Exact (e ∘ₗ f
) (g ∘ₗ (e.symm : N' ->ₗ[R] N)) ↔ Exact f g
参数：e : N ≃ₗ[R] N'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
lemma LinearEquiv.conj_exact_iff_exact (e : N ≃ₗ[R] N') :
    Function.Exact (e ∘ₗ f) (g ∘ₗ (e.symm : N' →ₗ[R] N)) ↔ Exact f g := by
  simp_rw [LinearMap.exact_iff, LinearMap.ker_comp, ← Submodule.map_equiv_eq_comap_symm,
    LinearMap.range_comp]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff

variable (f g) in
/-
**LinearEquiv.conj_symm_exact_iff_exact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearEquiv.conj_symm_exact_iff_exact (e : N' ≃ₗ[R] N) : Function.Exact (e
.symm ∘ₗ f) (g ∘ₗ (e : N' ->ₗ[R] N)) ↔ Exact f g
参数：e : N' ≃ₗ[R] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearEquiv.conj_exact_iff_exact`：LinearEquiv.conj_exact_iff_exact (e : 
N ≃ₗ[R] N') : Function.Exact (e ∘ₗ f) (g ∘ₗ (e.symm : N' ->ₗ[R] N)) ↔ Exact f g
-/
lemma LinearEquiv.conj_symm_exact_iff_exact (e : N' ≃ₗ[R] N) :
    Function.Exact (e.symm ∘ₗ f) (g ∘ₗ (e : N' →ₗ[R] N)) ↔ Exact f g :=
  LinearEquiv.conj_exact_iff_exact _ _ e.symm

namespace Function

open LinearMap

/-
**Function.Exact.linearMap_ker_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Exact`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_4} {P : Type u_6} [inst : Semi
ring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : AddCom
mMonoid P] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_6 :
 _root_.Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}, Function.Exact ⇑f ⇑g → g.ke
r = f.range
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
lemma Exact.linearMap_ker_eq (hfg : Exact f g) : ker g = range f :=
  SetLike.ext hfg
/-
**Function.Exact.linearMap_comp_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function.Exac
t`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_4} {P : Type u_6} [inst : Semi
ring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : AddCom
mMonoid P] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_6 :
 _root_.Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}, Function.Exact ⇑f ⇑g → g ∘ₗ
 f = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Function.Exact.comp_eq_zero`：∀ {M : Type u_2} {N : Type u_4} {P : Type u
_6} {f : M → N} {g : N → P} [inst : Zero P], Function.Exact f g → g ∘ f = 0
-/
lemma Exact.linearMap_comp_eq_zero (h : Exact f g) : g.comp f = 0 :=
  DFunLike.coe_injective h.comp_eq_zero
/-
**Function.Surjective.comp_exact_iff_exact** 是 Mathlib 中的一个定理，位于命名空间 `Function.S
urjective`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M' : Type u_3} {N : Type u_4} {P : Type u
_6} [inst : Semiring R]   [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M']
 [inst_3 : AddCommMonoid N] [inst_4 : AddCommMonoid P]   [inst_5 : _root_.Module
 R M] [inst_6 : _root_.Module R M'] [inst_7 : _root_.Module R N] [inst_8 : _root
_.Module R P]   {f : M →ₗ[R] N} {g : N →ₗ[R] P} {p : M' →ₗ[R] M},   Function.Sur
jective ⇑p → (Function.Exact ⇑(f ∘ₗ p) ⇑g ↔ Function.Exact ⇑f ⇑g)
参数：Function.Exact ⇑(f ∘ₗ p) ⇑g ↔ Function.Exact ⇑f ⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.range_comp`：∀ {α : Type u_1} {ι : Sort u_3} {ι' : So
rt u_4} {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α), Set.range (g ∘ f
) = Set.range g
-/
lemma Surjective.comp_exact_iff_exact {p : M' →ₗ[R] M} (h : Surjective p) :
    Exact (f ∘ₗ p) g ↔ Exact f g :=
  iff_of_eq <| forall_congr fun x =>
    congrArg (g x = 0 ↔ x ∈ ·) (h.range_comp f)
/-
**Function._root_.LinearEquiv.precomp_exact_iff_exact** 是 Mathlib 中的一个引理，位于命名空间 
`Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearEquiv.precomp_exact_iff_exact {e : M' ≃ₗ[R] M} :
    Exact (f ∘ₗ (e : M' →ₗ[R] M)) g ↔ Exact f g :=
  e.surjective.comp_exact_iff_exact
/-
**Function.Injective.comp_exact_iff_exact** 是 Mathlib 中的一个定理，位于命名空间 `Function.In
jective`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_4} {P : Type u_6} {P' : Type u
_7} [inst : Semiring R]   [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N] 
[inst_3 : AddCommMonoid P] [inst_4 : AddCommMonoid P']   [inst_5 : _root_.Module
 R M] [inst_6 : _root_.Module R N] [inst_7 : _root_.Module R P] [inst_8 : _root_
.Module R P']   {f : M →ₗ[R] N} {g : N →ₗ[R] P} {i : P →ₗ[R] P'},   Function.Inj
ective ⇑i → (Function.Exact ⇑f ⇑(i ∘ₗ g) ↔ Function.Exact ⇑f ⇑g)
参数：Function.Exact ⇑f ⇑(i ∘ₗ g) ↔ Function.Exact ⇑f ⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `iff_congr`：∀ {p₁ p₂ q₁ q₂ : Prop}, (p₁ ↔ p₂) → (q₁ ↔ q₂) → ((p₁ ↔ q₁) ↔ 
(p₂ ↔ q₂))
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Injective.comp_exact_iff_exact {i : P →ₗ[R] P'} (h : Injective i) :
    Exact f (i ∘ₗ g) ↔ Exact f g :=
  forall_congr' fun _ => iff_congr (map_eq_zero_iff _ h) Iff.rfl
/-
**Function._root_.LinearEquiv.postcomp_exact_iff_exact** 是 Mathlib 中的一个引理，位于命名空间
 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearEquiv.postcomp_exact_iff_exact {e : P ≃ₗ[R] P'} :
    Exact f ((e : P →ₗ[R] P') ∘ₗ g) ↔ Exact f g :=
  e.injective.comp_exact_iff_exact

namespace Exact

variable
    {f₁₂ : M →ₗ[R] N} {f₂₃ : N →ₗ[R] P} {g₁₂ : M' →ₗ[R] N'}
    {g₂₃ : N' →ₗ[R] P'} {e₁ : M ≃ₗ[R] M'} {e₂ : N ≃ₗ[R] N'} {e₃ : P ≃ₗ[R] P'}

/-
**Function.Exact.iff_of_ladder_linearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Function.E
xact`。
形式化陈述：iff_of_ladder_linearEquiv (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ =
 e₃ ∘ₗ f₂₃) : Exact g₁₂ g₂₃ ↔ Exact f₁₂ f₂₃
参数：h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂；h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Exact.iff_of_ladder_addEquiv`：∀ {X₁ : Type u_8} {X₂ : Type u_9}
 {X₃ : Type u_10} {Y₁ : Type u_11} {Y₂ : Type u_12} {Y₃ : Type u_13}   [inst : A
ddCommMonoid X₁] [inst_1 : …
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma iff_of_ladder_linearEquiv
    (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃) :
    Exact g₁₂ g₂₃ ↔ Exact f₁₂ f₂₃ :=
  iff_of_ladder_addEquiv e₁.toAddEquiv e₂.toAddEquiv e₃.toAddEquiv
    (f₁₂ := f₁₂) (f₂₃ := f₂₃) (g₁₂ := g₁₂) (g₂₃ := g₂₃)
    (congr_arg LinearMap.toAddMonoidHom h₁₂) (congr_arg LinearMap.toAddMonoidHom h₂₃)
/-
**Function.Exact.of_ladder_linearEquiv_of_exact** 是 Mathlib 中的一个引理，位于命名空间 `Funct
ion.Exact`。
形式化陈述：of_ladder_linearEquiv_of_exact (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ
 e₂ = e₃ ∘ₗ f₂₃) (H : Exact f₁₂ f₂₃) : Exact g₁₂ g₂₃
参数：h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂；h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃；H : Exact f₁₂ f₂₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.Exact.iff_of_ladder_linearEquiv`：iff_of_ladder_linearEquiv (h₁₂
 : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃) : Exact g₁₂ g₂₃ ↔ Exact 
f₁₂ f₂₃
-/
lemma of_ladder_linearEquiv_of_exact
    (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃)
    (H : Exact f₁₂ f₂₃) : Exact g₁₂ g₂₃ := by
  rwa [iff_of_ladder_linearEquiv h₁₂ h₂₃]

/-- Two maps `f : M →ₗ[R] N` and `g : N →ₗ[R] P` are exact if and only if the induced maps
`LinearMap.range f → N → LinearMap.range g` are exact. -/
/-
**Function.Exact.iff_linearMap_rangeRestrict** 是 Mathlib 中的一个引理，位于命名空间 `Function
.Exact`。
形式化陈述：iff_linearMap_rangeRestrict : Exact f g ↔ Exact (LinearMap.range f).subtyp
e g.rangeRestrict
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Exact.iff_rangeFactorization`：∀ {M : Type u_2} {N : Type u_4} {
P : Type u_6} {f : M → N} {g : N → P} [inst : Zero P] (hg : 0 ∈ Set.range g),   
Function.Exact f g ↔ Functi…
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M

--- 原说明 ---
Two maps `f : M →ₗ[R] N` and `g : N →ₗ[R] P` are exact if and only if the induce
d maps
`LinearMap.range f → N → LinearMap.range g` are exact.
-/
lemma iff_linearMap_rangeRestrict :
    Exact f g ↔ Exact (LinearMap.range f).subtype g.rangeRestrict :=
  iff_rangeFactorization (zero_mem (LinearMap.range g))

alias ⟨linearMap_rangeRestrict, _⟩ := iff_linearMap_rangeRestrict

end Exact

end Function

end LinearMap

namespace Function

section split

variable [Semiring R]
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

open LinearMap

set_option backward.isDefEq.respectTransparency.types false in
/-- Given an exact sequence `0 → M → N → P`, giving a section `P → N` is equivalent to giving a
splitting `N ≃ M × P`. -/
noncomputable
/-
**Function.Exact.splitSurjectiveEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Function.Exact`
。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     {N : Type u_4} →       {P : Type u
_6} →         [inst : Semiring R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : AddCommGroup N] →               [inst_3 : AddCommGroup P] →     
            [inst_4 : _root_.Module R M] →                   [inst_5 : _root_.Mo
dule R N] →                     [inst_6 : _root_.Module R P] →                  
     {f : M →ₗ[R] N} →                         {g : N →ₗ[R] P} →                
           Function.Exact ⇑f ⇑g →                             Function.Injective
 ⇑f →                               { l // g ∘ₗ l = LinearMap.id } ≃            
                     { e // f = ↑e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.s
nd R M P ∘ₗ ↑e }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Exact.splitSurjectiveEquiv (h : Function.Exact f g) (hf : Function.Injective f) :
    { l // g ∘ₗ l = .id } ≃
      { e : N ≃ₗ[R] M × P // f = e.symm ∘ₗ inl R M P ∧ g = snd R M P ∘ₗ e } := by
  refine
  { toFun := fun l ↦ ⟨(LinearEquiv.ofBijective (f ∘ₗ fst R M P + l.1 ∘ₗ snd R M P) ?_).symm, ?_⟩
    invFun := fun e ↦ ⟨e.1.symm ∘ₗ inr R M P, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h₁ : ∀ x, g (l.1 x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · intro x y e
      simp only [add_apply, coe_comp, comp_apply, fst_apply, snd_apply] at e
      suffices x.2 = y.2 from Prod.ext (hf (by rwa [this, add_left_inj] at e)) this
      simpa [h₁, h₂] using DFunLike.congr_arg g e
    · intro x
      obtain ⟨y, hy⟩ := (h (x - l.1 (g x))).mp (by simp [h₁, g.map_sub])
      exact ⟨⟨y, g x⟩, by simp [hy]⟩
  · have h₁ : ∀ x, g (l.1 x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · ext; simp
    · rw [LinearEquiv.eq_comp_toLinearMap_symm]
      ext <;> simp [h₁, h₂]
  · rw [← LinearMap.comp_assoc, (LinearEquiv.eq_comp_toLinearMap_symm _ _).mp e.2.2]; rfl
  · intro; ext; simp
  · rintro ⟨e, rfl, rfl⟩
    ext1
    apply LinearEquiv.symm_bijective.injective
    ext
    apply e.injective
    ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Given an exact sequence `M → N → P → 0`, giving a retraction `N → M` is equivalent to giving a
splitting `N ≃ M × P`. -/
noncomputable
/-
**Function.Exact.splitInjectiveEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Function.Exact`。
形式化陈述：{R : Type u_8} →   {M : Type u_9} →     {N : Type u_10} →       {P : Type 
u_11} →         [inst : Semiring R] →           [inst_1 : AddCommGroup M] →     
        [inst_2 : AddCommGroup N] →               [inst_3 : AddCommGroup P] →   
              [inst_4 : _root_.Module R M] →                   [inst_5 : _root_.
Module R N] →                     [inst_6 : _root_.Module R P] →                
       {f : M →ₗ[R] N} →                         {g : N →ₗ[R] P} →              
             Function.Exact ⇑f ⇑g →                             Function.Surject
ive ⇑g →                               { l // l ∘ₗ f = LinearMap.id } ≃         
                        { e // f = ↑e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMa
p.snd R M P ∘ₗ ↑e }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Exact.splitInjectiveEquiv
    {R M N P} [Semiring R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) (hg : Function.Surjective g) :
    { l // l ∘ₗ f = .id } ≃
      { e : N ≃ₗ[R] M × P // f = e.symm ∘ₗ inl R M P ∧ g = snd R M P ∘ₗ e } := by
  refine
  { toFun := fun l ↦ ⟨(LinearEquiv.ofBijective (l.1.prod g) ?_), ?_⟩
    invFun := fun e ↦ ⟨fst R M P ∘ₗ e.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h₁ : ∀ x, l.1 (f x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · intro x y e
      simp only [LinearMap.prod_apply, Function.prod_apply, Prod.mk.injEq] at e
      obtain ⟨z, hz⟩ := (h (x - y)).mp (by simpa [sub_eq_zero] using e.2)
      rw [← sub_eq_zero, ← hz, ← h₁ z, hz, map_sub, e.1, sub_self, map_zero]
    · rintro ⟨x, y⟩
      obtain ⟨y, rfl⟩ := hg y
      refine ⟨f x + y - f (l.1 y), by ext <;> simp [h₁, h₂]⟩
  · have h₁ : ∀ x, l.1 (f x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · rw [LinearEquiv.eq_toLinearMap_symm_comp]
      ext <;> simp [h₁, h₂]
    · ext; simp
  · rw [LinearMap.comp_assoc, (LinearEquiv.eq_toLinearMap_symm_comp _ _).mp e.2.1]; rfl
  · intro; ext; simp
  · rintro ⟨e, rfl, rfl⟩
    ext x <;> simp
/-
**Function.Exact.split_tfae'** 是 Mathlib 中的一个定理，位于命名空间 `Function.Exact`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_4} {P : Type u_6} [inst : Semi
ring R] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGroup N] [inst_3 : AddCommG
roup P] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_6 : _r
oot_.Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P},   Function.Exact ⇑f ⇑g →     [
Function.Injective ⇑f ∧ ∃ l, g ∘ₗ l = LinearMap.id, Function.Surjective ⇑g ∧ ∃ l
, l ∘ₗ f = LinearMap.id,         ∃ e, f = ↑e.symm ∘ₗ LinearMap.inl R M P ∧ g = L
inearMap.snd R M P ∘ₗ ↑e].TFAE
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `LinearMap.inl_injective`：inl_injective : Function.Injective (inl R M M₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
-/
theorem Exact.split_tfae' (h : Function.Exact f g) :
    List.TFAE [
      Function.Injective f ∧ ∃ l, g ∘ₗ l = LinearMap.id,
      Function.Surjective g ∧ ∃ l, l ∘ₗ f = LinearMap.id,
      ∃ e : N ≃ₗ[R] M × P, f = e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e] := by
  tfae_have 1 → 3
  | ⟨hf, l, hl⟩ => ⟨_, (h.splitSurjectiveEquiv hf ⟨l, hl⟩).2⟩
  tfae_have 2 → 3
  | ⟨hg, l, hl⟩ => ⟨_, (h.splitInjectiveEquiv hg ⟨l, hl⟩).2⟩
  tfae_have 3 → 1
  | ⟨e, e₁, e₂⟩ => by
    have : Function.Injective f := e₁ ▸ e.symm.injective.comp LinearMap.inl_injective
    exact ⟨this, ⟨_, ((h.splitSurjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_have 3 → 2
  | ⟨e, e₁, e₂⟩ => by
    have : Function.Surjective g := e₂ ▸ Prod.snd_surjective.comp e.surjective
    exact ⟨this, ⟨_, ((h.splitInjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_finish

/-- Equivalent characterizations of split exact sequences. Also known as the **Splitting lemma**. -/
/-
**Function.Exact.split_tfae** 是 Mathlib 中的一个定理，位于命名空间 `Function.Exact`。
形式化陈述：∀ {R : Type u_8} {M : Type u_9} {N : Type u_10} {P : Type u_11} [inst : Se
miring R] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGroup N] [inst_3 : AddCom
mGroup P] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_6 : 
_root_.Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P},   Function.Exact ⇑f ⇑g →    
 Function.Injective ⇑f →       Function.Surjective ⇑g →         [∃ l, g ∘ₗ l = L
inearMap.id, ∃ l, l ∘ₗ f = LinearMap.id,             ∃ e, f = ↑e.symm ∘ₗ LinearM
ap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ ↑e].TFAE
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
Equivalent characterizations of split exact sequences. Also known as the **Split
ting lemma**.
-/
theorem Exact.split_tfae
    {R M N P} [Semiring R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    List.TFAE [
      ∃ l, g ∘ₗ l = LinearMap.id,
      ∃ l, l ∘ₗ f = LinearMap.id,
      ∃ e : N ≃ₗ[R] M × P, f = e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e] := by
  tfae_have 1 ↔ 3 := by
    simpa using (h.splitSurjectiveEquiv hf).nonempty_congr
  tfae_have 2 ↔ 3 := by
    simpa using (h.splitInjectiveEquiv hg).nonempty_congr
  tfae_finish

end split

section Prod

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-
**Function.Exact.inr_fst** 是 Mathlib 中的一个定理，位于命名空间 `Function.Exact`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_4} [inst : Semiring R] [inst_1
 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [inst_3 : _root_.Module R M] [i
nst_4 : _root_.Module R N],   Function.Exact ⇑(LinearMap.inr R M N) ⇑(LinearMap.
fst R M N)
参数：LinearMap.inr R M N；LinearMap.fst R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Exact.inr_fst : Function.Exact (LinearMap.inr R M N) (LinearMap.fst R M N) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.fst_apply, @eq_comm _ x, LinearMap.coe_inr, Set.mem_range, Prod.mk.injEq,
    exists_eq_right]
/-
**Function.Exact.inl_snd** 是 Mathlib 中的一个定理，位于命名空间 `Function.Exact`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_4} [inst : Semiring R] [inst_1
 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [inst_3 : _root_.Module R M] [i
nst_4 : _root_.Module R N],   Function.Exact ⇑(LinearMap.inl R M N) ⇑(LinearMap.
snd R M N)
参数：LinearMap.inl R M N；LinearMap.snd R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Exact.inl_snd : Function.Exact (LinearMap.inl R M N) (LinearMap.snd R M N) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.snd_apply, @eq_comm _ y, LinearMap.coe_inl, Set.mem_range, Prod.mk.injEq,
    exists_eq_left]

end Prod

end Function

section Ring

open LinearMap Submodule

variable [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}

namespace Function

/-- A necessary and sufficient condition for an exact sequence to descend to a quotient. -/
/-
**Function.Exact.exact_mapQ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.Exact`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_4} {P : Type u_6} [inst : Ring
 R] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGroup N] [inst_3 : AddCommGroup
 P] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_6 : _root_
.Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P},   Function.Exact ⇑f ⇑g →     ∀ {p 
: Submodule R M} {q : Submodule R N} {r : Submodule R P} (hpq : p ≤ Submodule.co
map f q)       (hqr : q ≤ Submodule.comap g r),       Function.Exact ⇑(p.mapQ q 
f hpq) ⇑(q.mapQ r g hqr) ↔ g.range ⊓ r ≤ Submodule.map g q
参数：hpq : p ≤ Submodule.comap f q；hqr : q ≤ Submodule.comap g r；p.mapQ q f hpq；q.
mapQ r g hqr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.comap_injective_of_surjective`：comap_injective_of_surjective :
 Function.Injective (comap f)
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `Submodule.range_liftQ`：range_liftQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ
₁₂] M₂) (h) : range (p.liftQ f h) = range f
· 使用定理 `Submodule.liftQ_mkQ`：liftQ_mkQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : (p.liftQ f h).
comp p.mkQ = f
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `Function.Exact.linearMap_ker_eq`：∀ {R : Type u_1} {M : Type u_2} {N : Ty
pe u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid N] [i…
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `LinearMap.ker_le_comap`：ker_le_comap {p : Submodule R₂ M₂} (f : M ->ₛₗ[τ
₁₂] M₂) : ker f <= p.comap f
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Submodule.map_comap_eq`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} 
{M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A necessary and sufficient condition for an exact sequence to descend to a quoti
ent.
-/
lemma Exact.exact_mapQ_iff
    (hfg : Exact f g) {p q r} (hpq : p ≤ comap f q) (hqr : q ≤ comap g r) :
    Exact (mapQ p q f hpq) (mapQ q r g hqr) ↔ range g ⊓ r ≤ map g q := by
  rw [exact_iff, ← (comap_injective_of_surjective (mkQ_surjective _)).eq_iff]
  dsimp only [mapQ]
  rw [← ker_comp, range_liftQ, liftQ_mkQ, ker_comp, range_comp, comap_map_eq,
    ker_mkQ, ker_mkQ, ← hfg.linearMap_ker_eq, sup_comm,
    ← (sup_le hqr (ker_le_comap g)).ge_iff_eq',
    ← comap_map_eq, ← map_le_iff_le_comap, map_comap_eq]

end Function

namespace LinearMap

/-- When we have a commutative diagram from a sequence of two linear maps to another,
such that the left vertical map is surjective, the middle vertical map is bijective and the right
vertical map is injective, then the upper row is exact iff the lower row is.
See `ShortComplex.exact_iff_of_epi_of_isIso_of_mono` in the file
`Mathlib/Algebra/Homology/ShortComplex/Exact.lean` for the categorical version of this result. -/
/-
**LinearMap.exact_iff_of_surjective_of_bijective_of_injective** 是 Mathlib 中的一个引理
，位于命名空间 `LinearMap`。
形式化陈述：exact_iff_of_surjective_of_bijective_of_injective {M₁ M₂ M₃ N₁ N₂ N₃ : Typ
e*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid N₁] 
[AddCommMonoid N₂] [AddCommMonoid N₃] [Module R M₁] [Module R M₂] [Module R M₃] 
[Module R N₁] [Module R N₂] [Module R N₃] (f : M₁ ->ₗ[R] M₂) (g : M₂ ->ₗ[R] M₃) 
(f' : N₁ ->ₗ[R] N₂) (g' : N₂ ->ₗ[R] N₃) (τ₁ : M₁ ->ₗ[R] N₁) (τ₂ : M₂ ->ₗ[R] N₂) 
(τ₃ : M₃ ->ₗ[R] N₃) (comm₁₂ : f'.comp τ₁ = τ₂.comp f) (comm₂₃ : g'.comp τ₂ = τ₃.
comp g) (h₁ : Function.Sur
参数：f : M₁ ->ₗ[R] M₂；g : M₂ ->ₗ[R] M₃；f' : N₁ ->ₗ[R] N₂；g' : N₂ ->ₗ[R] N₃；τ₁ : M₁
 ->ₗ[R] N₁；τ₂ : M₂ ->ₗ[R] N₂；τ₃ : M₃ ->ₗ[R] N₃；comm₁₂ : f'.comp τ₁ = τ₂.comp f；c
omm₂₃ : g'.comp τ₂ = τ₃.comp g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective`：∀ {M₁ : 
Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} {N₁ : Type u_11} {N₂ : Type u_12} {N₃
 : Type u_13}   [inst : AddCommMonoid M₁] [inst_1 : …
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
When we have a commutative diagram from a sequence of two linear maps to another
,
such that the left vertical map is surjective, the middle vertical map is biject
ive and the right
vertical map is injective, then the upper row is exact iff the lower row is.
See `ShortComplex.exact_iff_of_epi_of_isIso_of_mono` in the file
`Mathlib/Algebra/Homology/ShortComplex/Exact.lean` for the categorical version o
f this result.
-/
lemma exact_iff_of_surjective_of_bijective_of_injective
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    [Module R N₁] [Module R N₂] [Module R N₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (f' : N₁ →ₗ[R] N₂) (g' : N₂ →ₗ[R] N₃)
    (τ₁ : M₁ →ₗ[R] N₁) (τ₂ : M₂ →ₗ[R] N₂) (τ₃ : M₃ →ₗ[R] N₃)
    (comm₁₂ : f'.comp τ₁ = τ₂.comp f) (comm₂₃ : g'.comp τ₂ = τ₃.comp g)
    (h₁ : Function.Surjective τ₁) (h₂ : Function.Bijective τ₂) (h₃ : Function.Injective τ₃) :
    Function.Exact f g ↔ Function.Exact f' g' :=
  AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    f.toAddMonoidHom g.toAddMonoidHom f'.toAddMonoidHom g'.toAddMonoidHom
    τ₁.toAddMonoidHom τ₂.toAddMonoidHom τ₃.toAddMonoidHom
    (by ext; apply DFunLike.congr_fun comm₁₂) (by ext; apply DFunLike.congr_fun comm₂₃) h₁ h₂ h₃
/-
**LinearMap.surjective_range_liftQ** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：surjective_range_liftQ (h : range f <= ker g) (hg : Function.Surjective g)
 : Function.Surjective ((range f).liftQ g h)
参数：h : range f <= ker g；hg : Function.Surjective g。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma surjective_range_liftQ (h : range f ≤ ker g) (hg : Function.Surjective g) :
    Function.Surjective ((range f).liftQ g h) := by
  intro x₃
  obtain ⟨x₂, rfl⟩ := hg x₃
  exact ⟨Submodule.Quotient.mk x₂, rfl⟩
/-
**LinearMap.ker_eq_bot_range_liftQ_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：ker_eq_bot_range_liftQ_iff (h : range f <= ker g) : ker ((range f).liftQ g
 h) = ⊥ ↔ ker g = range f
参数：h : range f <= ker g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Submodule.Quotient.mk_surjective`：mk_surjective : Function.Surjective (@
mk _ _ _ _ _ p)
-/
lemma ker_eq_bot_range_liftQ_iff (h : range f ≤ ker g) :
    ker ((range f).liftQ g h) = ⊥ ↔ ker g = range f := by
  simp only [Submodule.ext_iff, mem_ker, Submodule.mem_bot, mem_range]
  constructor
  · intro hfg x
    simpa using hfg (Submodule.Quotient.mk x)
  · intro hfg x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simpa using hfg x

set_option backward.isDefEq.respectTransparency.types false in
/-
**LinearMap.injective_range_liftQ_of_exact** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`
。
形式化陈述：injective_range_liftQ_of_exact (h : Function.Exact f g) : Function.Injecti
ve ((range f).liftQ g (h · |>.mpr))
参数：h : Function.Exact f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma injective_range_liftQ_of_exact (h : Function.Exact f g) :
    Function.Injective ((range f).liftQ g (h · |>.mpr)) := by
  simpa only [← LinearMap.ker_eq_bot, ker_eq_bot_range_liftQ_iff, exact_iff] using h
/-
**LinearMap.surjective_iff_eq_zero_of_exact** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
`。
形式化陈述：surjective_iff_eq_zero_of_exact (h : Function.Exact f g) : Function.Surjec
tive f ↔ g = 0
参数：h : Function.Exact f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_eq_top`：ker_eq_top {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 
0
· 使用定理 `Function.Exact.linearMap_ker_eq`：∀ {R : Type u_1} {M : Type u_2} {N : Ty
pe u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid N] [i…
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma surjective_iff_eq_zero_of_exact (h : Function.Exact f g) :
    Function.Surjective f ↔ g = 0 := by
  rw [← LinearMap.ker_eq_top, h.linearMap_ker_eq, LinearMap.range_eq_top]
/-
**LinearMap.injective_iff_eq_zero_of_exact** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`
。
形式化陈述：injective_iff_eq_zero_of_exact (h : Function.Exact f g) : Function.Injecti
ve g ↔ f = 0
参数：h : Function.Exact f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Function.Exact.linearMap_ker_eq`：∀ {R : Type u_1} {M : Type u_2} {N : Ty
pe u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid N] [i…
· 使用定理 `LinearMap.range_eq_bot`：range_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : range f = ⊥ 
↔ f = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma injective_iff_eq_zero_of_exact (h : Function.Exact f g) :
    Function.Injective g ↔ f = 0 := by
  rw [← LinearMap.ker_eq_bot, h.linearMap_ker_eq, LinearMap.range_eq_bot]

end LinearMap

/-- The linear equivalence `(N ⧸ LinearMap.range f) ≃ₗ[A] P` associated to
an exact sequence `M → N → P → 0` of `R`-modules. -/
@[simps! apply]
/-
**Function.Exact.linearEquivOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.Exact.linearEquivOfSurjective (h : Function.Exact f g) (hg : Func
tion.Surjective g) : (N ⧸ LinearMap.range f) ≃ₗ[R] P
参数：h : Function.Exact f g；hg : Function.Surjective g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence `(N ⧸ LinearMap.range f) ≃ₗ[A] P` associated to
an exact sequence `M → N → P → 0` of `R`-modules.
-/
noncomputable def Function.Exact.linearEquivOfSurjective (h : Function.Exact f g)
    (hg : Function.Surjective g) : (N ⧸ LinearMap.range f) ≃ₗ[R] P :=
  LinearEquiv.ofBijective ((LinearMap.range f).liftQ g (h · |>.mpr))
    ⟨LinearMap.injective_range_liftQ_of_exact h, LinearMap.surjective_range_liftQ _ hg⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Function.Exact.linearEquivOfSurjective_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：Function.Exact.linearEquivOfSurjective_symm_apply (h : Function.Exact f g)
 (hg : Function.Surjective g) (x : N) : (h.linearEquivOfSurjective hg).symm (g x
) = Submodule.Quotient.mk x
参数：h : Function.Exact f g；hg : Function.Surjective g；x : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Exact.linearEquivOfSurjective_apply`：∀ {R : Type u_1} {M : Type
 u_2} {N : Type u_4} {P : Type u_6} [inst : Ring R] [inst_1 : AddCommGroup M]   
[inst_2 : AddCommGroup N] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Function.Exact.linearEquivOfSurjective_symm_apply (h : Function.Exact f g)
    (hg : Function.Surjective g) (x : N) :
    (h.linearEquivOfSurjective hg).symm (g x) = Submodule.Quotient.mk x := by
  simp [LinearEquiv.symm_apply_eq]

end Ring

