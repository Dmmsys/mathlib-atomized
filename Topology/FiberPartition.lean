/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Logic.Function.FiberPartition
/-!

This file provides some API surrounding `Function.Fiber` (see
`Mathlib/Logic/Function/FiberPartition.lean`) in the presence of a topology on the domain of the
function.

Note: this API is designed to be useful when defining the counit of the adjunction between
the functor which takes a set to the condensed set corresponding to locally constant maps to that
set, and the forgetful functor from the category of condensed sets to the category of sets
(see PR https://github.com/leanprover-community/mathlib4/pull/14027).
-/

@[expose] public section


open Function

variable {S Y : Type*} (f : S → Y)

namespace TopologicalSpace.Fiber

variable [TopologicalSpace S]

/-- The canonical map from the disjoint union induced by `f` to `S`. -/
@[simps apply]
/-
**TopologicalSpace.Fiber.sigmaIsoHom** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace
.Fiber`。
形式化陈述：sigmaIsoHom : C((x : Fiber f) × x.val, S) where toFun | ⟨a, x⟩ => x.val co
ntinuous_toFun
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the disjoint union induced by `f` to `S`.
-/
def sigmaIsoHom : C((x : Fiber f) × x.val, S) where
  toFun | ⟨a, x⟩ => x.val
  continuous_toFun := continuous_sigma (by fun_prop)

set_option backward.isDefEq.respectTransparency false in
/-
**TopologicalSpace.Fiber.sigmaIsoHom_inj** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalS
pace.Fiber`。
形式化陈述：sigmaIsoHom_inj : Function.Injective (sigmaIsoHom f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.subtype_ext`：∀ {α : Type u_1} {β : Type u_7} {p : α → β → Prop} {x
₀ x₁ : (a : α) × Subtype (p a)},   x₀.fst = x₁.fst → ↑x₀.snd = ↑x₁.snd → x₀ = x₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TopologicalSpace.Fiber.sigmaIsoHom_apply`：∀ {S : Type u_1} {Y : Type u_2
} (f : S → Y) [inst : TopologicalSpace S] (x : (x : Function.Fiber f) × ↑↑x),   
(TopologicalSpace.Fiber.sigmaI…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sigmaIsoHom_inj : Function.Injective (sigmaIsoHom f) := by
  rintro ⟨⟨_, _, rfl⟩, ⟨_, hx⟩⟩ ⟨⟨_, _, rfl⟩, ⟨_, hy⟩⟩ h
  refine Sigma.subtype_ext ?_ h
  simp only [sigmaIsoHom_apply] at h
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx hy
  simp [← hx, ← hy, h]
/-
**TopologicalSpace.Fiber.sigmaIsoHom_surj** 是 Mathlib 中的一个引理，位于命名空间 `Topological
Space.Fiber`。
形式化陈述：sigmaIsoHom_surj : Function.Surjective (sigmaIsoHom f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
lemma sigmaIsoHom_surj : Function.Surjective (sigmaIsoHom f) :=
  fun _ ↦ ⟨⟨⟨_, ⟨⟨_, Set.mem_range_self _⟩, rfl⟩⟩, ⟨_, rfl⟩⟩, rfl⟩

/-- The inclusion map from a component of the disjoint union induced by `f` into `S`. -/
/-
**TopologicalSpace.Fiber.sigmaIncl** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.F
iber`。
形式化陈述：sigmaIncl (a : Fiber f) : C(a.val, S) where toFun x
参数：a : Fiber f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map from a component of the disjoint union induced by `f` into `S`
.
-/
def sigmaIncl (a : Fiber f) : C(a.val, S) where
  toFun x := x.val

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion map from a fiber of a composition into the intermediate fiber. -/
/-
**TopologicalSpace.Fiber.sigmaInclIncl** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpa
ce.Fiber`。
形式化陈述：sigmaInclIncl {X : Type*} (g : Y -> X) (a : Fiber (g ∘ f)) (b : Fiber (f ∘
 (sigmaIncl (g ∘ f) a))) : C(b.val, (Fiber.mk f (b.preimage).val).val) where toF
un x
参数：g : Y -> X；a : Fiber (g ∘ f)；b : Fiber (f ∘ (sigmaIncl (g ∘ f) a))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map from a fiber of a composition into the intermediate fiber.
-/
def sigmaInclIncl {X : Type*} (g : Y → X) (a : Fiber (g ∘ f))
    (b : Fiber (f ∘ (sigmaIncl (g ∘ f) a))) :
    C(b.val, (Fiber.mk f (b.preimage).val).val) where
  toFun x := ⟨x.val.val, by
    have := x.prop
    simp only [sigmaIncl, ContinuousMap.coe_mk, Fiber.mem_iff_eq_image, comp_apply] at this
    rw [Fiber.mem_iff_eq_image, Fiber.mk_image, this, ← Fiber.map_preimage_eq_image]
    simp [sigmaIncl]⟩

variable (l : LocallyConstant S Y) [CompactSpace S]
/-
**TopologicalSpace.Fiber.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Fiber`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : Fiber l) : CompactSpace x.val := by
  obtain ⟨y, hy⟩ := x.prop
  rw [← isCompact_iff_compactSpace, ← hy]
  exact (l.2.isClosed_fiber _).isCompact
/-
**TopologicalSpace.Fiber.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Fiber`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Finite (Fiber l) :=
  have : Finite (Set.range l) := l.range_finite
  Finite.Set.finite_range _

end TopologicalSpace.Fiber

