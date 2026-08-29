/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Support of an element under an action

Given an action of a group `G` on a type `α`, we say that a set `s : Set α` supports an element
`a : α` if, for all `g` that fix `s` pointwise, `g` fixes `a`.

This is crucial in Fourier-Motzkin constructions.
-/

@[expose] public section

assert_not_exists MonoidWithZero

open scoped Pointwise

variable {G H α β : Type*}

namespace MulAction

section SMul

variable (G) [SMul G α] [SMul G β]

/-- A set `s` supports `b` if `g • b = b` whenever `g • a = a` for all `a ∈ s`. -/
@[to_additive /-- A set `s` supports `b` if `g +ᵥ b = b` whenever `g +ᵥ a = a` for all `a ∈ s`. -/]
/--
Definition of `Supports` / `Supports` 的定义

English:
definition Supports
  signature: (s : Set α) (b : β)
  body: forall g : G, (forall ⦃a⦄, a in s -> g • a = a) -> g • b = b

中文:
定义 Supports
  签名: (s : 集合 α) (b : β)
  定义体: forall g : G, (forall ⦃a⦄, a in s -> g • a = a) -> g • b = b
-/
def Supports (s : Set α) (b : β) :=
  forall g : G, (forall ⦃a⦄, a in s -> g • a = a) -> g • b = b

variable {s t : Set α} {a : α} {b : β}

@[to_additive]
/--
theorem `supports_of_mem` / 定理 `supports_of_mem`

English:
theorem supports_of_mem
  given: (ha : a in s)
  statement: Supports G s a
  proof: fun _ h => h ha

中文:
定理 supports_of_mem
  条件: (ha : a in s)
  结论: Supports G s a
  证明: fun _ h => h ha
-/
theorem supports_of_mem (ha : a in s) : Supports G s a := fun _ h => h ha

variable {G}

@[to_additive]
/--
theorem `Supports.mono` / 定理 `Supports.mono`

English:
theorem Supports.mono
  given: (h : s subseteq t) (hs : Supports G s b)
  statement: Supports G t b
  proof: fun _ hg =>
(hs _) fun _ ha => hg h ha

中文:
定理 Supports.mono
  条件: (h : s subseteq t) (hs : Supports G s b)
  结论: Supports G t b
  证明: fun _ hg =>
(hs _) fun _ ha => hg h ha
-/
theorem Supports.mono (h : s subseteq t) (hs : Supports G s b) : Supports G t b := fun _ hg =>
(hs _) fun _ ha => hg h ha

end SMul

variable [Group H] [SMul G α] [SMul G β] [MulAction H α] [SMul H β] [SMulCommClass G H β]
  [SMulCommClass G H α] {s : Set α} {b : β}

-- TODO: This should work without `SMulCommClass`
@[to_additive]
/--
theorem `Supports.smul` / 定理 `Supports.smul`

English:
theorem Supports.smul
  given: (g : H) (h : Supports G s b)
  statement: Supports G (g • s) (g • b)
  proof: by
  rintro g' hg'
  rw [smul_comm]; rw [h]
  rintro a ha
  have := Set.forall_mem_image.1 hg' ha
  rwa [smul_comm, smul_left_cancel_iff] at this

中文:
定理 Supports.smul
  条件: (g : H) (h : Supports G s b)
  结论: Supports G (g • s) (g • b)
  证明: by
  rintro g' hg'
  rw [smul_comm]; rw [h]
  rintro a ha
  have := Set.forall_mem_image.1 hg' ha
  rwa [smul_comm, smul_left_cancel_iff] at this

Depends on / 依赖: Set.forall_mem_image, forall_mem_image, smul_comm, smul_left_cancel_iff
-/
theorem Supports.smul (g : H) (h : Supports G s b) : Supports G (g • s) (g • b) := by
  rintro g' hg'
  rw [smul_comm]; rw [h]
  rintro a ha
  have := Set.forall_mem_image.1 hg' ha
  rwa [smul_comm, smul_left_cancel_iff] at this

end MulAction
