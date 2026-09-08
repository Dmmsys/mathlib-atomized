/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Hom.Ring
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Topology.LocallyConstant.Basic

/-! # Germs of functions between topological spaces

In this file, we prove basic properties of germs of functions between topological spaces,
with respect to the neighbourhood filter `𝓝 x`.

## Main definitions and results

* `Filter.Germ.value φ f`: value associated to the germ `φ` at a point `x`, w.r.t. the
  neighbourhood filter at `x`. This is the common value of all representatives of `φ` at `x`.
* `Filter.Germ.valueOrderRingHom` and friends: the map `Germ (𝓝 x) E → E` is a
  monoid homomorphism, 𝕜-linear map, ring homomorphism, monotone ring homomorphism

* `RestrictGermPredicate`: given a predicate on germs `P : Π x : X, germ (𝓝 x) Y → Prop` and
  `A : set X`, build a new predicate on germs `restrictGermPredicate P A` such that
  `(∀ x, RestrictGermPredicate P A x f) ↔ ∀ᶠ x near A, P x f`;
  `forall_restrictGermPredicate_iff` is this equivalence.

* `Filter.Germ.sliceLeft, sliceRight`: map the germ of functions `X × Y → Z` at `p = (x,y) ∈ X × Y`
  to the corresponding germ of functions `X → Z` at `x ∈ X` resp. `Y → Z` at `y ∈ Y`.
* `eq_of_germ_isConstant`: if each germ of `f : X → Y` is constant and `X` is pre-connected,
  `f` is constant.
-/

@[expose] public section

open scoped Topology

open Filter Set

variable {X Y Z : Type*} [TopologicalSpace X] {f g : X → Y} {A : Set X} {x : X}

namespace Filter.Germ

/-- The value associated to a germ at a point. This is the common value
shared by all representatives at the given point. -/
/-
**Filter.Germ.value** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：value {X α : Type*} [TopologicalSpace X] {x : X} (φ : Germ (𝓝 x) α) : α
参数：φ : Germ (𝓝 x) α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The value associated to a germ at a point. This is the common value
shared by all representatives at the given point.
-/
def value {X α : Type*} [TopologicalSpace X] {x : X} (φ : Germ (𝓝 x) α) : α :=
  Quotient.liftOn' φ (fun f ↦ f x) fun f g h ↦ by rw [Eventually.self_of_nhds h]

@[simp]
/-
**Filter.Germ.value_ofFun** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：value_ofFun (f : X -> Y) (x : X) : value (f : Germ (𝓝 x) Y) = f x
参数：f : X -> Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem value_ofFun (f : X → Y) (x : X) : value (f : Germ (𝓝 x) Y) = f x := rfl

@[simp]
/-
**Filter.Germ.value_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：value_const (c : Y) (x : X) : value (c : Germ (𝓝 x) Y) = c
参数：c : Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem value_const (c : Y) (x : X) : value (c : Germ (𝓝 x) Y) = c := rfl
/-
**Filter.Germ.value_smul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：value_smul {α β : Type*} [SMul α β] (φ : Germ (𝓝 x) α) (ψ : Germ (𝓝 x) β) 
: (φ • ψ).value = φ.value • ψ.value
参数：φ : Germ (𝓝 x) α；ψ : Germ (𝓝 x) β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.inductionOn`：inductionOn (f : Germ l β) {p : Germ l β -> Pro
p} (h : forall f : α -> β, p f) : p f
-/
theorem value_smul {α β : Type*} [SMul α β] (φ : Germ (𝓝 x) α)
    (ψ : Germ (𝓝 x) β) : (φ • ψ).value = φ.value • ψ.value :=
  Germ.inductionOn φ fun _ ↦ Germ.inductionOn ψ fun _ ↦ rfl

/-- The map `Germ (𝓝 x) E → E` into a monoid `E` as a monoid homomorphism -/
@[to_additive /-- The map `Germ (𝓝 x) E → E` as an additive monoid homomorphism -/]
/-
**Filter.Germ.valueMulHom** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：valueMulHom {X E : Type*} [Monoid E] [TopologicalSpace X] {x : X} : Germ (
𝓝 x) E ->* E where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Germ (𝓝 x) E → E` into a monoid `E` as a monoid homomorphism
-/
def valueMulHom {X E : Type*} [Monoid E] [TopologicalSpace X] {x : X} : Germ (𝓝 x) E →* E where
  toFun := Filter.Germ.value
  map_one' := rfl
  map_mul' φ ψ := Germ.inductionOn φ fun _ ↦ Germ.inductionOn ψ fun _ ↦ rfl

/-- The map `Germ (𝓝 x) E → E` into a `𝕜`-module `E` as a `𝕜`-linear map -/
/-
**Filter.Germ.value** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：value {X α : Type*} [TopologicalSpace X] {x : X} (φ : Germ (𝓝 x) α) : α
参数：φ : Germ (𝓝 x) α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Germ (𝓝 x) E → E` into a `𝕜`-module `E` as a `𝕜`-linear map
-/
def valueₗ {X 𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace X]
    {x : X} : Germ (𝓝 x) E →ₗ[𝕜] E where
  __ := Filter.Germ.valueAddHom
  map_smul' := fun _ φ ↦ Germ.inductionOn φ fun _ ↦ rfl

/-- The map `Germ (𝓝 x) E → E` as a ring homomorphism -/
/-
**Filter.Germ.valueRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：valueRingHom {X E : Type*} [Semiring E] [TopologicalSpace X] {x : X} : Ger
m (𝓝 x) E ->+* E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Germ (𝓝 x) E → E` as a ring homomorphism
-/
def valueRingHom {X E : Type*} [Semiring E] [TopologicalSpace X] {x : X} : Germ (𝓝 x) E →+* E :=
  { Filter.Germ.valueMulHom, Filter.Germ.valueAddHom with }

/-- The map `Germ (𝓝 x) E → E` as a monotone ring homomorphism -/
/-
**Filter.Germ.valueOrderRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：valueOrderRingHom {X E : Type*} [Semiring E] [PartialOrder E] [Topological
Space X] {x : X} : Germ (𝓝 x) E ->+*o E where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Germ (𝓝 x) E → E` as a monotone ring homomorphism
-/
def valueOrderRingHom {X E : Type*} [Semiring E] [PartialOrder E] [TopologicalSpace X] {x : X} :
    Germ (𝓝 x) E →+*o E where
  __ := Filter.Germ.valueRingHom
  monotone' := fun φ ψ ↦
  Germ.inductionOn φ fun _ ↦ Germ.inductionOn ψ fun _ h ↦ h.self_of_nhds

end Filter.Germ

section RestrictGermPredicate
/-- Given a predicate on germs `P : Π x : X, germ (𝓝 x) Y → Prop` and `A : set X`,
build a new predicate on germs `RestrictGermPredicate P A` such that
`(∀ x, RestrictGermPredicate P A x f) ↔ ∀ᶠ x near A, P x f`, see
`forall_restrictGermPredicate_iff` for this equivalence. -/
/-
**RestrictGermPredicate** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RestrictGermPredicate (P : forall x : X, Germ (𝓝 x) Y -> Prop) (A : Set X)
 : forall x : X, Germ (𝓝 x) Y -> Prop
参数：P : forall x : X, Germ (𝓝 x) Y -> Prop；A : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a predicate on germs `P : Π x : X, germ (𝓝 x) Y → Prop` and `A : set X`,
build a new predicate on germs `RestrictGermPredicate P A` such that
`(∀ x, RestrictGermPredicate P A x f) ↔ ∀ᶠ x near A, P x f`, see
`forall_restrictGermPredicate_iff` for this equivalence.
-/
def RestrictGermPredicate (P : ∀ x : X, Germ (𝓝 x) Y → Prop)
    (A : Set X) : ∀ x : X, Germ (𝓝 x) Y → Prop := fun x φ ↦
  Germ.liftOn φ (fun f ↦ x ∈ A → ∀ᶠ y in 𝓝 x, P y f)
    haveI : ∀ f f' : X → Y, f =ᶠ[𝓝 x] f' → (∀ᶠ y in 𝓝 x, P y f) → ∀ᶠ y in 𝓝 x, P y f' := by
      intro f f' hff' hf
      apply (hf.and <| Eventually.eventually_nhds hff').mono
      rintro y ⟨hy, hy'⟩
      rwa [Germ.coe_eq.mpr (EventuallyEq.symm hy')]
    fun f f' hff' ↦ propext <| forall_congr' fun _ ↦ ⟨this f f' hff', this f' f hff'.symm⟩
/-
**Filter.Eventually.germ_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.germ_congr_set {P : forall x : X, Germ (𝓝 x) Y -> Prop} 
(hf : forallᶠ x in 𝓝ˢ A, P x f) (h : forallᶠ z in 𝓝ˢ A, g z = f z) : forallᶠ x i
n 𝓝ˢ A, P x g
参数：𝓝 x；hf : forallᶠ x in 𝓝ˢ A, P x f；h : forallᶠ z in 𝓝ˢ A, g z = f z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eventually_nhdsSet_iff_forall`：eventually_nhdsSet_iff_forall {p : X -> P
rop} : (forallᶠ x in 𝓝ˢ s, p x) ↔ forall x, x in s -> forallᶠ y in 𝓝 x, p y
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Eventually.eventually_nhds`：Filter.Eventually.eventually_nhds {p 
: X -> Prop} (h : forallᶠ y in 𝓝 x, p y) : forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p
 x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.Germ.coe_eq`：coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Filter.Eventually.germ_congr_set
    {P : ∀ x : X, Germ (𝓝 x) Y → Prop} (hf : ∀ᶠ x in 𝓝ˢ A, P x f)
    (h : ∀ᶠ z in 𝓝ˢ A, g z = f z) : ∀ᶠ x in 𝓝ˢ A, P x g := by
  rw [eventually_nhdsSet_iff_forall] at *
  intro x hx
  apply ((hf x hx).and (h x hx).eventually_nhds).mono
  intro y hy
  convert! hy.1 using 1
  exact Germ.coe_eq.mpr hy.2
/-
**restrictGermPredicate_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：restrictGermPredicate_congr {P : forall x : X, Germ (𝓝 x) Y -> Prop} (hf :
 RestrictGermPredicate P A x f) (h : forallᶠ z in 𝓝ˢ A, g z = f z) : RestrictGer
mPredicate P A x g
参数：𝓝 x；hf : RestrictGermPredicate P A x f；h : forallᶠ z in 𝓝ˢ A, g z = f z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Eventually.eventually_nhds`：Filter.Eventually.eventually_nhds {p 
: X -> Prop} (h : forallᶠ y in 𝓝 x, p y) : forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p
 x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eventually_nhdsSet_iff_forall`：eventually_nhdsSet_iff_forall {p : X -> P
rop} : (forallᶠ x in 𝓝ˢ s, p x) ↔ forall x, x in s -> forallᶠ y in 𝓝 x, p y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.Germ.coe_eq`：coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g
-/
theorem restrictGermPredicate_congr {P : ∀ x : X, Germ (𝓝 x) Y → Prop}
    (hf : RestrictGermPredicate P A x f) (h : ∀ᶠ z in 𝓝ˢ A, g z = f z) :
    RestrictGermPredicate P A x g := by
  intro hx
  apply ((hf hx).and <| (eventually_nhdsSet_iff_forall.mp h x hx).eventually_nhds).mono
  rintro y ⟨hy, h'y⟩
  rwa [Germ.coe_eq.mpr h'y]
/-
**forall_restrictGermPredicate_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_restrictGermPredicate_iff {P : forall x : X, Germ (𝓝 x) Y -> Prop} 
: (forall x, RestrictGermPredicate P A x f) ↔ forallᶠ x in 𝓝ˢ A, P x f
参数：𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eventually_nhdsSet_iff_forall`：eventually_nhdsSet_iff_forall {p : X -> P
rop} : (forallᶠ x in 𝓝ˢ s, p x) ↔ forall x, x in s -> forallᶠ y in 𝓝 x, p y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem forall_restrictGermPredicate_iff {P : ∀ x : X, Germ (𝓝 x) Y → Prop} :
    (∀ x, RestrictGermPredicate P A x f) ↔ ∀ᶠ x in 𝓝ˢ A, P x f := by
  rw [eventually_nhdsSet_iff_forall]
  rfl
/-
**forall_restrictGermPredicate_of_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_restrictGermPredicate_of_forall {P : forall x : X, Germ (𝓝 x) Y -> 
Prop} (h : forall x, P x f) : forall x, RestrictGermPredicate P A x f
参数：𝓝 x；h : forall x, P x f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `forall_restrictGermPredicate_iff`：forall_restrictGermPredicate_iff {P : 
forall x : X, Germ (𝓝 x) Y -> Prop} : (forall x, RestrictGermPredicate P A x f) 
↔ forallᶠ x in 𝓝ˢ A, P…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem forall_restrictGermPredicate_of_forall
    {P : ∀ x : X, Germ (𝓝 x) Y → Prop} (h : ∀ x, P x f) :
    ∀ x, RestrictGermPredicate P A x f :=
  forall_restrictGermPredicate_iff.mpr (Eventually.of_forall h)
end RestrictGermPredicate

namespace Filter.Germ
/-- Map the germ of functions `X × Y → Z` at `p = (x,y) ∈ X × Y` to the corresponding germ
  of functions `X → Z` at `x ∈ X` -/
/-
**Filter.Germ.sliceLeft** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：sliceLeft [TopologicalSpace Y] {p : X × Y} (P : Germ (𝓝 p) Z) : Germ (𝓝 p.
1) Z
参数：P : Germ (𝓝 p) Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map the germ of functions `X × Y → Z` at `p = (x,y) ∈ X × Y` to the correspondin
g germ
  of functions `X → Z` at `x ∈ X`
-/
def sliceLeft [TopologicalSpace Y] {p : X × Y} (P : Germ (𝓝 p) Z) : Germ (𝓝 p.1) Z :=
  P.compTendsto (Prod.mk · p.2) (Continuous.prodMk_left p.2).continuousAt

@[simp]
/-
**Filter.Germ.sliceLeft_coe** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：sliceLeft_coe [TopologicalSpace Y] {y : Y} (f : X × Y -> Z) : (↑f : Germ (
𝓝 (x, y)) Z).sliceLeft = fun x' => f (x', y)
参数：f : X × Y -> Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sliceLeft_coe [TopologicalSpace Y] {y : Y} (f : X × Y → Z) :
    (↑f : Germ (𝓝 (x, y)) Z).sliceLeft = fun x' ↦ f (x', y) :=
  rfl

/-- Map the germ of functions `X × Y → Z` at `p = (x,y) ∈ X × Y` to the corresponding germ
  of functions `Y → Z` at `y ∈ Y` -/
/-
**Filter.Germ.sliceRight** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：sliceRight [TopologicalSpace Y] {p : X × Y} (P : Germ (𝓝 p) Z) : Germ (𝓝 p
.2) Z
参数：P : Germ (𝓝 p) Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map the germ of functions `X × Y → Z` at `p = (x,y) ∈ X × Y` to the correspondin
g germ
  of functions `Y → Z` at `y ∈ Y`
-/
def sliceRight [TopologicalSpace Y] {p : X × Y} (P : Germ (𝓝 p) Z) : Germ (𝓝 p.2) Z :=
  P.compTendsto (Prod.mk p.1) (Continuous.prodMk_right p.1).continuousAt

@[simp]
/-
**Filter.Germ.sliceRight_coe** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：sliceRight_coe [TopologicalSpace Y] {y : Y} (f : X × Y -> Z) : (↑f : Germ 
(𝓝 (x, y)) Z).sliceRight = fun y' => f (x, y')
参数：f : X × Y -> Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sliceRight_coe [TopologicalSpace Y] {y : Y} (f : X × Y → Z) :
    (↑f : Germ (𝓝 (x, y)) Z).sliceRight = fun y' ↦ f (x, y') :=
  rfl
/-
**Filter.Germ.isConstant_comp_subtype** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Germ`。
形式化陈述：isConstant_comp_subtype {s : Set X} {f : X -> Y} {x : s} (hf : (f : Germ (
𝓝 (x : X)) Y).IsConstant) : ((f ∘ Subtype.val : s -> Y) : Germ (𝓝 x) Y).IsConsta
nt
参数：hf : (f : Germ (𝓝 (x : X)) Y).IsConstant。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Germ.isConstant_comp_tendsto`：isConstant_comp_tendsto {lc : Filte
r γ} {g : γ -> α} (hf : (f : Germ l β).IsConstant) (hg : Tendsto g lc l) : IsCon
stant (f ∘ g : Germ lc β)
· 使用定理 `continuousAt_subtype_val`：continuousAt_subtype_val {p : X -> Prop} {x : 
Subtype p} : ContinuousAt ((↑) : Subtype p -> X) x
-/
lemma isConstant_comp_subtype {s : Set X} {f : X → Y} {x : s}
    (hf : (f : Germ (𝓝 (x : X)) Y).IsConstant) :
    ((f ∘ Subtype.val : s → Y) : Germ (𝓝 x) Y).IsConstant :=
  isConstant_comp_tendsto hf continuousAt_subtype_val

end Filter.Germ

/-- If the germ of `f` w.r.t. each `𝓝 x` is constant, `f` is locally constant. -/
/-
**IsLocallyConstant.of_germ_isConstant** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocallyConstant.of_germ_isConstant (h : forall x : X, (f : Germ (𝓝 x) Y)
.IsConstant) : IsLocallyConstant f
参数：h : forall x : X, (f : Germ (𝓝 x) Y).IsConstant。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s

--- 原说明 ---
If the germ of `f` w.r.t. each `𝓝 x` is constant, `f` is locally constant.
-/
lemma IsLocallyConstant.of_germ_isConstant (h : ∀ x : X, (f : Germ (𝓝 x) Y).IsConstant) :
    IsLocallyConstant f := by
  intro s
  rw [isOpen_iff_mem_nhds]
  intro a ha
  obtain ⟨b, hb⟩ := h a
  apply mem_of_superset hb
  intro x hx
  have : f x = f a := (mem_of_mem_nhds hb) ▸ hx
  rw [mem_preimage, this]
  exact ha
/-
**eq_of_germ_isConstant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_germ_isConstant [i : PreconnectedSpace X] (h : forall x : X, (f : Ge
rm (𝓝 x) Y).IsConstant) (x x' : X) : f x = f x'
参数：h : forall x : X, (f : Germ (𝓝 x) Y).IsConstant；x x' : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.apply_eq_of_isPreconnected`：apply_eq_of_isPreconnected
 {f : X -> Y} (hf : IsLocallyConstant f) {s : Set X} (hs : IsPreconnected s) {x 
y : X} (hx : x in s) (hy : y in s)…
· 使用引理 `IsLocallyConstant.of_germ_isConstant`：IsLocallyConstant.of_germ_isConsta
nt (h : forall x : X, (f : Germ (𝓝 x) Y).IsConstant) : IsLocallyConstant f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `preconnectedSpace_iff_univ`：preconnectedSpace_iff_univ : PreconnectedSpa
ce α ↔ IsPreconnected (univ : Set α)
-/
theorem eq_of_germ_isConstant [i : PreconnectedSpace X]
    (h : ∀ x : X, (f : Germ (𝓝 x) Y).IsConstant) (x x' : X) : f x = f x' :=
  (IsLocallyConstant.of_germ_isConstant h).apply_eq_of_isPreconnected
    (preconnectedSpace_iff_univ.mp i) (by trivial) (by trivial)
/-
**eq_of_germ_isConstant_on** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_of_germ_isConstant_on {s : Set X} (h : forall x in s, (f : Germ (𝓝 x) Y
).IsConstant) (hs : IsPreconnected s) {x' : X} (x_in : x in s) (x'_in : x' in s)
 : f x = f x'
参数：h : forall x in s, (f : Germ (𝓝 x) Y).IsConstant；hs : IsPreconnected s；x_in :
 x in s；x'_in : x' in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.preconnectedSpace`：Subtype.preconnectedSpace {s : Set α} (h : Is
Preconnected s) : PreconnectedSpace s where isPreconnected_univ
· 使用定理 `eq_of_germ_isConstant`：eq_of_germ_isConstant [i : PreconnectedSpace X] (
h : forall x : X, (f : Germ (𝓝 x) Y).IsConstant) (x x' : X) : f x = f x'
· 使用引理 `Filter.Germ.isConstant_comp_subtype`：isConstant_comp_subtype {s : Set X}
 {f : X -> Y} {x : s} (hf : (f : Germ (𝓝 (x : X)) Y).IsConstant) : ((f ∘ Subtype
.val : s -> Y) : Germ (𝓝 …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma eq_of_germ_isConstant_on {s : Set X} (h : ∀ x ∈ s, (f : Germ (𝓝 x) Y).IsConstant)
    (hs : IsPreconnected s) {x' : X} (x_in : x ∈ s) (x'_in : x' ∈ s) : f x = f x' := by
  let i : s → X := fun x ↦ x
  change (f ∘ i) (⟨x, x_in⟩ : s) = (f ∘ i) (⟨x', x'_in⟩ : s)
  have : PreconnectedSpace s := Subtype.preconnectedSpace hs
  exact eq_of_germ_isConstant (fun y ↦ Germ.isConstant_comp_subtype (h y y.2)) _ _

@[to_additive (attr := simp)]
/-
**Germ.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Germ.coe_prod {α : Type*} (l : Filter α) (R : Type*) [CommMonoid R] {ι} (f
 : ι -> α -> R) (s : Finset ι) : ((∏ i in s, f i : α -> R) : Germ l R) = ∏ i in 
s, (f i : Germ l R)
参数：l : Filter α；R : Type*；f : ι -> α -> R；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem Germ.coe_prod {α : Type*} (l : Filter α) (R : Type*) [CommMonoid R] {ι} (f : ι → α → R)
    (s : Finset ι) : ((∏ i ∈ s, f i : α → R) : Germ l R) = ∏ i ∈ s, (f i : Germ l R) :=
  map_prod (Germ.coeMulHom l : (α → R) →* Germ l R) f s
