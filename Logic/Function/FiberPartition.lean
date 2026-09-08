/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Data.Set.Insert
/-!

This file defines the type `f.Fiber` of fibers of a function `f : Y → Z`, and provides some API
to work with and construct terms of this type.

Note: this API is designed to be useful when defining the counit of the adjunction between
the functor which takes a set to the condensed set corresponding to locally constant maps to that
set, and the forgetful functor from the category of condensed sets to the category of sets
(see PR https://github.com/leanprover-community/mathlib4/pull/14027).
-/

@[expose] public section

assert_not_exists RelIso

variable {X Y Z : Type*}

namespace Function

/-- The indexing set of the partition. -/
/-
**Function.Fiber** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：Fiber (f : Y -> Z) : Type _
参数：f : Y -> Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The indexing set of the partition.
-/
def Fiber (f : Y → Z) : Type _ := Set.range (fun (x : Set.range f) ↦ f ⁻¹' {x.val})

namespace Fiber

/--
Any `a : Fiber f` is of the form `f ⁻¹' {x}` for some `x` in the image of `f`. We define `a.image`
as an arbitrary such `x`.
-/
/-
**Function.Fiber.image** 是 Mathlib 中的一个定义，位于命名空间 `Function.Fiber`。
形式化陈述：image (f : Y -> Z) (a : Fiber f) : Z
参数：f : Y -> Z；a : Fiber f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any `a : Fiber f` is of the form `f ⁻¹' {x}` for some `x` in the image of `f`. W
e define `a.image`
as an arbitrary such `x`.
-/
noncomputable def image (f : Y → Z) (a : Fiber f) : Z := a.2.choose.1
/-
**Function.Fiber.eq_fiber_image** 是 Mathlib 中的一个引理，位于命名空间 `Function.Fiber`。
形式化陈述：eq_fiber_image (f : Y -> Z) (a : Fiber f) : a.1 = f ⁻¹' {a.image}
参数：f : Y -> Z；a : Fiber f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma eq_fiber_image (f : Y → Z) (a : Fiber f) : a.1 = f ⁻¹' {a.image} := a.2.choose_spec.symm

/--
Given `y : Y`, `Fiber.mk f y` is the fiber of `f` that `y` belongs to, as an element of `Fiber f`.
-/
/-
**Function.Fiber.mk** 是 Mathlib 中的一个定义，位于命名空间 `Function.Fiber`。
形式化陈述：mk (f : Y -> Z) (y : Y) : Fiber f
参数：f : Y -> Z；y : Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `y : Y`, `Fiber.mk f y` is the fiber of `f` that `y` belongs to, as an ele
ment of `Fiber f`.
-/
def mk (f : Y → Z) (y : Y) : Fiber f := ⟨f ⁻¹' {f y}, by simp⟩

/-- `y : Y` as a term of the type `Fiber.mk f y` -/
/-
**Function.Fiber.mkSelf** 是 Mathlib 中的一个定义，位于命名空间 `Function.Fiber`。
形式化陈述：mkSelf (f : Y -> Z) (y : Y) : (mk f y).val
参数：f : Y -> Z；y : Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`y : Y` as a term of the type `Fiber.mk f y`
-/
def mkSelf (f : Y → Z) (y : Y) : (mk f y).val := ⟨y, rfl⟩
/-
**Function.Fiber.map_eq_image** 是 Mathlib 中的一个引理，位于命名空间 `Function.Fiber`。
形式化陈述：map_eq_image (f : Y -> Z) (a : Fiber f) (x : a.1) : f x = a.image
参数：f : Y -> Z；a : Fiber f；x : a.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma map_eq_image (f : Y → Z) (a : Fiber f) (x : a.1) : f x = a.image := by
  have := a.2.choose_spec
  rw [← Set.mem_singleton_iff, ← Set.mem_preimage]
  convert! x.prop
/-
**Function.Fiber.mk_image** 是 Mathlib 中的一个引理，位于命名空间 `Function.Fiber`。
形式化陈述：mk_image (f : Y -> Z) (y : Y) : (Fiber.mk f y).image = f y
参数：f : Y -> Z；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.Fiber.map_eq_image`：map_eq_image (f : Y -> Z) (a : Fiber f) (x 
: a.1) : f x = a.image
-/
lemma mk_image (f : Y → Z) (y : Y) : (Fiber.mk f y).image = f y :=
  (map_eq_image (x := mkSelf f y)).symm
/-
**Function.Fiber.mem_iff_eq_image** 是 Mathlib 中的一个引理，位于命名空间 `Function.Fiber`。
形式化陈述：mem_iff_eq_image (f : Y -> Z) (y : Y) (a : Fiber f) : y in a.val ↔ f y = a
.image
参数：f : Y -> Z；y : Y；a : Fiber f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Fiber.map_eq_image`：map_eq_image (f : Y -> Z) (a : Fiber f) (x 
: a.1) : f x = a.image
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.Fiber.eq_fiber_image`：eq_fiber_image (f : Y -> Z) (a : Fiber f)
 : a.1 = f ⁻¹' {a.image}
-/
lemma mem_iff_eq_image (f : Y → Z) (y : Y) (a : Fiber f) : y ∈ a.val ↔ f y = a.image :=
  ⟨fun h ↦ a.map_eq_image _ ⟨y, h⟩, fun h ↦ by rw [a.eq_fiber_image]; exact h⟩

/-- An arbitrary element of `a : Fiber f`. -/
/-
**Function.Fiber.preimage** 是 Mathlib 中的一个定义，位于命名空间 `Function.Fiber`。
形式化陈述：preimage (f : Y -> Z) (a : Fiber f) : Y
参数：f : Y -> Z；a : Fiber f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary element of `a : Fiber f`.
-/
noncomputable def preimage (f : Y → Z) (a : Fiber f) : Y := a.2.choose.2.choose
/-
**Function.Fiber.map_preimage_eq_image** 是 Mathlib 中的一个引理，位于命名空间 `Function.Fiber
`。
形式化陈述：map_preimage_eq_image (f : Y -> Z) (a : Fiber f) : f a.preimage = a.image
参数：f : Y -> Z；a : Fiber f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma map_preimage_eq_image (f : Y → Z) (a : Fiber f) : f a.preimage = a.image :=
  a.2.choose.2.choose_spec
/-
**Function.Fiber.fiber_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Function.Fiber`。
形式化陈述：fiber_nonempty (f : Y -> Z) (a : Fiber f) : Set.Nonempty a.val
参数：f : Y -> Z；a : Fiber f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.Fiber.mem_iff_eq_image`：mem_iff_eq_image (f : Y -> Z) (y : Y) (
a : Fiber f) : y in a.val ↔ f y = a.image
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.Fiber.map_preimage_eq_image`：map_preimage_eq_image (f : Y -> Z)
 (a : Fiber f) : f a.preimage = a.image
-/
lemma fiber_nonempty (f : Y → Z) (a : Fiber f) : Set.Nonempty a.val := by
  refine ⟨preimage f a, ?_⟩
  rw [mem_iff_eq_image, ← map_preimage_eq_image]
/-
**Function.Fiber.map_preimage_eq_image_map** 是 Mathlib 中的一个引理，位于命名空间 `Function.F
iber`。
形式化陈述：map_preimage_eq_image_map {W : Type*} (f : Y -> Z) (g : Z -> W) (a : Fiber
 (g ∘ f)) : g (f a.preimage) = a.image
参数：f : Y -> Z；g : Z -> W；a : Fiber (g ∘ f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.Fiber.map_preimage_eq_image`：map_preimage_eq_image (f : Y -> Z)
 (a : Fiber f) : f a.preimage = a.image
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
lemma map_preimage_eq_image_map {W : Type*} (f : Y → Z) (g : Z → W) (a : Fiber (g ∘ f)) :
    g (f a.preimage) = a.image := by rw [← map_preimage_eq_image, comp_apply]
/-
**Function.Fiber.image_eq_image_mk** 是 Mathlib 中的一个引理，位于命名空间 `Function.Fiber`。
形式化陈述：image_eq_image_mk (f : Y -> Z) (g : X -> Y) (a : Fiber (f ∘ g)) : a.image 
= (Fiber.mk f (g (a.preimage _))).image
参数：f : Y -> Z；g : X -> Y；a : Fiber (f ∘ g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.Fiber.map_preimage_eq_image_map`：map_preimage_eq_image_map {W :
 Type*} (f : Y -> Z) (g : Z -> W) (a : Fiber (g ∘ f)) : g (f a.preimage) = a.ima
ge
· 使用引理 `Function.Fiber.mk_image`：mk_image (f : Y -> Z) (y : Y) : (Fiber.mk f y).
image = f y
-/
lemma image_eq_image_mk (f : Y → Z) (g : X → Y) (a : Fiber (f ∘ g)) :
    a.image = (Fiber.mk f (g (a.preimage _))).image := by
  rw [← map_preimage_eq_image_map _ _ a, mk_image]

end Function.Fiber

