/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Logic.Equiv.Option

/-!
# Extending a function from the complement of a singleton

In this file, we define `Function.subtypeNeLift` which allows to
extend a (dependent) function defined on the complement of a singleton.

-/

@[expose] public section

namespace Function

variable {ι : Type*} [DecidableEq ι] {M : ι -> Type*} (i₀ : ι)
  (f : forall (j : { i // i != i₀ }), M j) (x : M i₀)

/--
Definition of `subtypeNeLift` / `subtypeNeLift` 的定义

English:
definition subtypeNeLift
  signature: (i : ι)
  body: if h : i = i₀ then by rw [h]; exact x else f ⟨i, h⟩

@[simp]

中文:
定义 subtypeNeLift
  签名: (i : ι)
  定义体: if h : i = i₀ then by rw [h]; exact x else f ⟨i, h⟩

@[simp]
-/
def subtypeNeLift (i : ι) : M i :=
  if h : i = i₀ then by rw [h]; exact x else f ⟨i, h⟩

@[simp]
/--
lemma `subtypeNeLift_self` / 引理 `subtypeNeLift_self`

English:
lemma subtypeNeLift_self
  statement: subtypeNeLift i₀ f x i₀ = x
  proof: dif_pos rfl

中文:
引理 subtypeNeLift_self
  结论: subtypeNeLift i₀ f x i₀ = x
  证明: dif_pos rfl

Depends on / 依赖: dif_pos
-/
lemma subtypeNeLift_self : subtypeNeLift i₀ f x i₀ = x := dif_pos rfl

/--
lemma `subtypeNeLift_of_neq` / 引理 `subtypeNeLift_of_neq`

English:
lemma subtypeNeLift_of_neq
  given: (i : ι) (h : i != i₀)
  proof: dif_neg h

@[simp]

中文:
引理 subtypeNeLift_of_neq
  条件: (i : ι) (h : i != i₀)
  证明: dif_neg h

@[simp]

Depends on / 依赖: dif_neg
-/
lemma subtypeNeLift_of_neq (i : ι) (h : i != i₀) :
    subtypeNeLift i₀ f x i = f ⟨i, h⟩ := dif_neg h

@[simp]
/--
lemma `subtypeNeLift_restriction` / 引理 `subtypeNeLift_restriction`

English:
lemma subtypeNeLift_restriction
  given: (φ : forall i, M i) (i₀ : ι)
  proof: by
  ext i
  by_cases h : i = i₀
  · subst h
    simp
  · rw [subtypeNeLift_of_neq _ _ _ _ h]

中文:
引理 subtypeNeLift_restriction
  条件: (φ : 对任意 i, M i) (i₀ : ι)
  证明: by
  ext i
  by_cases h : i = i₀
  · subst h
    simp
  · rw [subtypeNeLift_of_neq _ _ _ _ h]

Depends on / 依赖: subtypeNeLift_of_neq
-/
lemma subtypeNeLift_restriction (φ : forall i, M i) (i₀ : ι) :
    subtypeNeLift i₀ (fun i => φ i) (φ i₀) = φ := by
  ext i
  by_cases h : i = i₀
  · subst h
    simp
  · rw [subtypeNeLift_of_neq _ _ _ _ h]

end Function
