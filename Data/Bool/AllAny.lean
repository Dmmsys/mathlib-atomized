/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Init

/-!
# Boolean quantifiers

This proves a few properties about `List.all` and `List.any`, which are the `Bool` universal and
existential quantifiers. Their definitions are in core Lean.
-/

public section


variable {α : Type*} {p : α -> Prop} [DecidablePred p] {l : List α} {a : α}

namespace List

/--
theorem `all_iff_forall_prop` / 定理 `all_iff_forall_prop`

English:
theorem all_iff_forall_prop
  statement: (all l fun a => p a) ↔ forall a in l, p a
  proof: by
  simp

中文:
定理 all_iff_forall_prop
  结论: (all l fun a => p a) ↔ 对任意 a in l, p a
  证明: by
  simp
-/
theorem all_iff_forall_prop : (all l fun a => p a) ↔ forall a in l, p a := by
  simp

/--
theorem `any_iff_exists_prop` / 定理 `any_iff_exists_prop`

English:
theorem any_iff_exists_prop
  statement: (any l fun a => p a) ↔ exists a in l, p a
  proof: by simp

中文:
定理 any_iff_exists_prop
  结论: (any l fun a => p a) ↔ 存在 a in l, p a
  证明: by simp
-/
theorem any_iff_exists_prop : (any l fun a => p a) ↔ exists a in l, p a := by simp

/--
theorem `any_of_mem` / 定理 `any_of_mem`

English:
theorem any_of_mem
  given: {p : α -> Bool} (h₁ : a in l) (h₂ : p a)
  statement: any l p
  proof: any_eq_true.2 ⟨_, h₁, h₂⟩

中文:
定理 any_of_mem
  条件: {p : α -> 布尔} (h₁ : a in l) (h₂ : p a)
  结论: any l p
  证明: any_eq_true.2 ⟨_, h₁, h₂⟩

Depends on / 依赖: any_eq_true
-/
theorem any_of_mem {p : α -> Bool} (h₁ : a in l) (h₂ : p a) : any l p :=
  any_eq_true.2 ⟨_, h₁, h₂⟩

end List
