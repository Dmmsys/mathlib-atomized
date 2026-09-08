/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison
-/
module

public import Mathlib.Topology.Sheaves.PresheafOfFunctions
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Sheaf conditions for presheaves of (continuous) functions.

We show that
* `Top.Presheaf.toType_isSheaf`: not-necessarily-continuous functions into a type form a sheaf
* `Top.Presheaf.toTypes_isSheaf`: in fact, these may be dependent functions into a type family

For
* `Top.sheafToTop`: continuous functions into a topological space form a sheaf

please see `Mathlib/Topology/Sheaves/LocalPredicate.lean`, where we set up a general framework
for constructing sub(pre)sheaves of the sheaf of dependent functions.

## Future work
Obviously there's more to do:
* sections of a fiber bundle
* various classes of smooth and structure-preserving functions
* functions into spaces with algebraic structure, which the sections inherit
-/

@[expose] public section


open CategoryTheory Limits TopologicalSpace Opens

noncomputable section

variable (X : TopCat)

open TopCat

namespace TopCat.Presheaf

/-- We show that the presheaf of functions to a type `T`
(no continuity assumptions, just plain functions)
form a sheaf.

In fact, the proof is identical when we do this for dependent functions to a type family `T`,
so we do the more general case.
-/
/-
**TopCat.Presheaf.toTypes_isSheaf** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：toTypes_isSheaf (T : X -> Type*) : (presheafToTypes X T).IsSheaf
参数：T : X -> Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types`：isSheaf_of_isSheaf
UniqueGluing_types (Fsh : F.IsSheafUniqueGluing) : F.IsSheaf
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.mem_iSup`：mem_iSup {ι} {x : α} {s : ι -> Opens α}
 : x in iSup s ↔ exists i, x in s i
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
We show that the presheaf of functions to a type `T`
(no continuity assumptions, just plain functions)
form a sheaf.

In fact, the proof is identical when we do this for dependent functions to a typ
e family `T`,
so we do the more general case.
-/
theorem toTypes_isSheaf (T : X → Type*) : (presheafToTypes X T).IsSheaf :=
  isSheaf_of_isSheafUniqueGluing_types _ fun ι U sf hsf => by
  -- We use the sheaf condition in terms of unique gluing
  -- U is a family of open sets, indexed by `ι` and `sf` is a compatible family of sections.
  -- In the informal comments below, I'll just write `U` to represent the union.
    -- Our first goal is to define a function "lifted" to all of `U`.
    -- We do this one point at a time. Using the axiom of choice, we can pick for each
    -- `x : ↑(iSup U)` an index `i : ι` such that `x` lies in `U i`
    choose index index_spec using fun x : ↑(iSup U) => Opens.mem_iSup.mp x.2
    -- Using this data, we can glue our functions together to a single section
    let s : ∀ x : ↑(iSup U), T x := fun x => sf (index x) ⟨x.1, index_spec x⟩
    refine ⟨s, ?_, ?_⟩
    · intro i
      funext x
      -- Now we need to verify that this lifted function restricts correctly to each set `U i`.
      -- Of course, the difficulty is that at any given point `x ∈ U i`,
      -- we may have used the axiom of choice to pick a different `j` with `x ∈ U j`
      -- when defining the function.
      -- Thus we'll need to use the fact that the restrictions are compatible.
      exact congr_fun (hsf (index ⟨x, _⟩) i) ⟨x, ⟨index_spec ⟨x.1, _⟩, x.2⟩⟩
    · -- Now we just need to check that the lift we picked was the only possible one.
      -- So we suppose we had some other gluing `t` of our sections
      intro t ht
      -- and observe that we need to check that it agrees with our choice
      -- for each `x ∈ ↑(iSup U)`.
      funext x
      exact congr_fun (ht (index x)) ⟨x.1, index_spec x⟩

-- We verify that the non-dependent version is an immediate consequence:
/-- The presheaf of not-necessarily-continuous functions to
a target type `T` satisfies the sheaf condition.
-/
/-
**TopCat.Presheaf.toType_isSheaf** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：toType_isSheaf (T : Type*) : (presheafToType X T).IsSheaf
参数：T : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.toTypes_isSheaf`：toTypes_isSheaf (T : X -> Type*) : (pre
sheafToTypes X T).IsSheaf

--- 原说明 ---
The presheaf of not-necessarily-continuous functions to
a target type `T` satisfies the sheaf condition.
-/
theorem toType_isSheaf (T : Type*) : (presheafToType X T).IsSheaf :=
  toTypes_isSheaf X fun _ => T

end TopCat.Presheaf

namespace TopCat

/-- The sheaf of not-necessarily-continuous functions on `X` with values in type family
`T : X → Type u`.
-/
/-
**TopCat.sheafToTypes** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：sheafToTypes (T : X -> Type*) : Sheaf (Type _) X
参数：T : X -> Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.toTypes_isSheaf`：toTypes_isSheaf (T : X -> Type*) : (pre
sheafToTypes X T).IsSheaf

--- 原说明 ---
The sheaf of not-necessarily-continuous functions on `X` with values in type fam
ily
`T : X → Type u`.
-/
def sheafToTypes (T : X → Type*) : Sheaf (Type _) X :=
  ⟨presheafToTypes X T, Presheaf.toTypes_isSheaf _ _⟩

/-- The sheaf of not-necessarily-continuous functions on `X` with values in a type `T`.
-/
/-
**TopCat.sheafToType** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：sheafToType (T : Type*) : Sheaf (Type _) X
参数：T : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.toType_isSheaf`：toType_isSheaf (T : Type*) : (presheafTo
Type X T).IsSheaf

--- 原说明 ---
The sheaf of not-necessarily-continuous functions on `X` with values in a type `
T`.
-/
def sheafToType (T : Type*) : Sheaf (Type _) X :=
  ⟨presheafToType X T, Presheaf.toType_isSheaf _ _⟩

end TopCat

