/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker
-/
module

public import Mathlib.Topology.Separation.Regular

/-!
# Extending a function from a subset

The main definition of this file is `extendFrom A f` where `f : X → Y`
and `A : Set X`. This defines a new function `g : X → Y` which maps any
`x₀ : X` to the limit of `f` as `x` tends to `x₀`, if such a limit exists.

This is analogous to the way `IsDenseInducing.extend` "extends" a function
`f : X → Z` to a function `g : Y → Z` along a dense inducing `i : X → Y`.

The main theorem we prove about this definition is `continuousOn_extendFrom`
which states that, for `extendFrom A f` to be continuous on a set `B ⊆ closure A`,
it suffices that `f` converges within `A` at any point of `B`, provided that
`f` is a function to a T₃ space.

-/

@[expose] public section


noncomputable section

open Topology

open Filter Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Extend a function from a set `A`. The resulting function `g` is such that
at any `x₀`, if `f` converges to some `y` as `x` tends to `x₀` within `A`,
then `g x₀` is defined to be one of these `y`. Else, `g x₀` could be anything. -/
/-
**extendFrom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：extendFrom (A : Set X) (f : X -> Y) : X -> Y
参数：A : Set X；f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a function from a set `A`. The resulting function `g` is such that
at any `x₀`, if `f` converges to some `y` as `x` tends to `x₀` within `A`,
then `g x₀` is defined to be one of these `y`. Else, `g x₀` could be anything.
-/
def extendFrom (A : Set X) (f : X → Y) : X → Y :=
  fun x ↦ @limUnder _ _ _ ⟨f x⟩ (𝓝[A] x) f

/-- If `f` converges to some `y` as `x` tends to `x₀` within `A`,
then `f` tends to `extendFrom A f x` as `x` tends to `x₀`. -/
/-
**tendsto_extendFrom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_extendFrom {A : Set X} {f : X -> Y} {x : X} (h : exists y, Tendsto
 f (𝓝[A] x) (𝓝 y)) : Tendsto f (𝓝[A] x) (𝓝 <| extendFrom A f x)
参数：h : exists y, Tendsto f (𝓝[A] x) (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_limUnder`：tendsto_nhds_limUnder {f : Filter α} {g : α -> X}
 (h : exists x, Tendsto g f (𝓝 x)) : Tendsto g f (𝓝 (@limUnder _ _ _ h.nonempty 
f g))

--- 原说明 ---
If `f` converges to some `y` as `x` tends to `x₀` within `A`,
then `f` tends to `extendFrom A f x` as `x` tends to `x₀`.
-/
theorem tendsto_extendFrom {A : Set X} {f : X → Y} {x : X} (h : ∃ y, Tendsto f (𝓝[A] x) (𝓝 y)) :
    Tendsto f (𝓝[A] x) (𝓝 <| extendFrom A f x) :=
  tendsto_nhds_limUnder h
/-
**extendFrom_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extendFrom_eq [T2Space Y] {A : Set X} {f : X -> Y} {x : X} {y : Y} (hx : x
 in closure A) (hf : Tendsto f (𝓝[A] x) (𝓝 y)) : extendFrom A f x = y
参数：hx : x in closure A；hf : Tendsto f (𝓝[A] x) (𝓝 y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `tendsto_nhds_limUnder`：tendsto_nhds_limUnder {f : Filter α} {g : α -> X}
 (h : exists x, Tendsto g f (𝓝 x)) : Tendsto g f (𝓝 (@limUnder _ _ _ h.nonempty 
f g))
-/
theorem extendFrom_eq [T2Space Y] {A : Set X} {f : X → Y} {x : X} {y : Y} (hx : x ∈ closure A)
    (hf : Tendsto f (𝓝[A] x) (𝓝 y)) : extendFrom A f x = y :=
  haveI := mem_closure_iff_nhdsWithin_neBot.mp hx
  tendsto_nhds_unique (tendsto_nhds_limUnder ⟨y, hf⟩) hf
/-
**extendFrom_extends** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extendFrom_extends [T2Space Y] {f : X -> Y} {A : Set X} (hf : ContinuousOn
 f A) : forall x in A, extendFrom A f x = f x
参数：hf : ContinuousOn f A。
该定理/引理给出了一组等式。
继承自：[T2Space Y] {f : X -> Y} {A : Set X} (hf : ContinuousOn f A) : forall x in A
, extendFrom A f x = f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extendFrom_eq`：extendFrom_eq [T2Space Y] {A : Set X} {f : X -> Y} {x : X
} {y : Y} (hx : x in closure A) (hf : Tendsto f (𝓝[A] x) (𝓝 y)) : extendFrom A f
 x …
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem extendFrom_extends [T2Space Y] {f : X → Y} {A : Set X} (hf : ContinuousOn f A) :
    ∀ x ∈ A, extendFrom A f x = f x :=
  fun x x_in ↦ extendFrom_eq (subset_closure x_in) (hf x x_in)

/-- If `f` is a function to a T₃ space `Y` which has a limit within `A` at any
point of a set `B ⊆ closure A`, then `extendFrom A f` is continuous on `B`. -/
/-
**continuousOn_extendFrom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_extendFrom [RegularSpace Y] {f : X -> Y} {A B : Set X} (hB : 
B subseteq closure A) (hf : forall x in B, exists y, Tendsto f (𝓝[A] x) (𝓝 y)) :
 ContinuousOn (extendFrom A f) B
参数：hB : B subseteq closure A；hf : forall x in B, exists y, Tendsto f (𝓝[A] x) (𝓝
 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_extendFrom`：tendsto_extendFrom {A : Set X} {f : X -> Y} {x : X} 
(h : exists y, Tendsto f (𝓝[A] x) (𝓝 y)) : Tendsto f (𝓝[A] x) (𝓝 <| extendFrom A
 f x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.tendsto_left_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : S
ort u_4} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β}   {f :
 α → β}, la.HasBasis p…
· 使用定理 `nhdsWithin_basis_open`：nhdsWithin_basis_open (a : α) (t : Set α) : (𝓝[t]
 a).HasBasis (fun u => a in u ∧ IsOpen u) fun u => u inter t
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.inter_mem_inf`：inter_mem_inf {α : Type u} {f g : Filter α} {s t :
 Set α} (hs : s in f) (ht : t in g) : s inter t in f ⊓ g
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `closed_nhds_basis`：closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : S
et X => s in 𝓝 x ∧ IsClosed s) id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
If `f` is a function to a T₃ space `Y` which has a limit within `A` at any
point of a set `B ⊆ closure A`, then `extendFrom A f` is continuous on `B`.
-/
theorem continuousOn_extendFrom [RegularSpace Y] {f : X → Y} {A B : Set X} (hB : B ⊆ closure A)
    (hf : ∀ x ∈ B, ∃ y, Tendsto f (𝓝[A] x) (𝓝 y)) : ContinuousOn (extendFrom A f) B := by
  set φ := extendFrom A f
  intro x x_in
  suffices ∀ V' ∈ 𝓝 (φ x), IsClosed V' → φ ⁻¹' V' ∈ 𝓝[B] x by
    simpa [ContinuousWithinAt, (closed_nhds_basis (φ x)).tendsto_right_iff]
  intro V' V'_in V'_closed
  obtain ⟨V, V_in, V_op, hV⟩ : ∃ V ∈ 𝓝 x, IsOpen V ∧ V ∩ A ⊆ f ⁻¹' V' := by
    have := tendsto_extendFrom (hf x x_in)
    rcases (nhdsWithin_basis_open x A).tendsto_left_iff.mp this V' V'_in with ⟨V, ⟨hxV, V_op⟩, hV⟩
    exact ⟨V, IsOpen.mem_nhds V_op hxV, V_op, hV⟩
  suffices ∀ y ∈ V ∩ B, φ y ∈ V' from
    mem_of_superset (inter_mem_inf V_in <| mem_principal_self B) this
  rintro y ⟨hyV, hyB⟩
  have := mem_closure_iff_nhdsWithin_neBot.mp (hB hyB)
  have limy : Tendsto f (𝓝[A] y) (𝓝 <| φ y) := tendsto_extendFrom (hf y hyB)
  have hVy : V ∈ 𝓝 y := IsOpen.mem_nhds V_op hyV
  have : V ∩ A ∈ 𝓝[A] y := by simpa only [inter_comm] using inter_mem_nhdsWithin A hVy
  exact V'_closed.mem_of_tendsto limy (mem_of_superset this hV)

/-- If a function `f` to a T₃ space `Y` has a limit within a
dense set `A` for any `x`, then `extendFrom A f` is continuous. -/
/-
**continuous_extendFrom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_extendFrom [RegularSpace Y] {f : X -> Y} {A : Set X} (hA : Dens
e A) (hf : forall x, exists y, Tendsto f (𝓝[A] x) (𝓝 y)) : Continuous (extendFro
m A f)
参数：hA : Dense A；hf : forall x, exists y, Tendsto f (𝓝[A] x) (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `continuousOn_extendFrom`：continuousOn_extendFrom [RegularSpace Y] {f : X
 -> Y} {A B : Set X} (hB : B subseteq closure A) (hf : forall x in B, exists y, 
Tendsto f (𝓝[…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
If a function `f` to a T₃ space `Y` has a limit within a
dense set `A` for any `x`, then `extendFrom A f` is continuous.
-/
theorem continuous_extendFrom [RegularSpace Y] {f : X → Y} {A : Set X} (hA : Dense A)
    (hf : ∀ x, ∃ y, Tendsto f (𝓝[A] x) (𝓝 y)) : Continuous (extendFrom A f) := by
  rw [← continuousOn_univ]
  exact continuousOn_extendFrom (fun x _ ↦ hA x) (by simpa using hf)
