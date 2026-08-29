/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.CompleteLattice.Lemmas
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.SetLike

/-!
# Multicoequalizer diagrams in complete lattices

We introduce the notion of bi-Cartesian square (`Lattice.BicartSq`) in a lattice `T`.
This consists of elements `x₁`, `x₂`, `x₃` and `x₄` such that `x₂ ⊔ x₃ = x₄` and
`x₂ ⊓ x₃ = x₁`.

It shall be shown (TODO) that if `T := Set X`, then the image of the
associated commutative square in the category `Type _` is a bi-Cartesian square
in a categorical sense (both pushout and pullback).

More generally, if `T` is a complete lattice, `x : T`, `u : ι → T`, `v : ι → ι → T`,
we introduce a property `MulticoequalizerDiagram x u v` which says that `x` is
the supremum of `u`, and that for all `i` and `j`, `v i j` is the minimum of `u i` and `u j`.
Again, when `T := Set X`, we shall show (TODO) that we obtain a multicoequalizer diagram
in the category of types.

-/

@[expose] public section

universe u

open CategoryTheory Limits

local grind_pattern inf_le_left => a ⊓ b
local grind_pattern inf_le_right => a ⊓ b
local grind_pattern le_sup_left => a ⊔ b
local grind_pattern le_sup_right => a ⊔ b

namespace Lattice

variable {T : Type u} (x₁ x₂ x₃ x₄ : T) [Lattice T]

/--
Definition of `BicartSq` / `BicartSq` 的定义

English:
structure BicartSq
  parameters: : Prop where
  axioms and operations (2):
    - sup_eq : x₂ ⊔ x₃ = x₄
    - inf_eq : x₂ ⊓ x₃ = x₁

中文:
结构 BicartSq
  参数: : 命题 where
  公理与运算 (2 个):
    - sup_eq : x₂ ⊔ x₃ = x₄
    - inf_eq : x₂ ⊓ x₃ = x₁
-/
structure BicartSq : Prop where
  sup_eq : x₂ ⊔ x₃ = x₄
  inf_eq : x₂ ⊓ x₃ = x₁

attribute [grind cases] BicartSq

namespace BicartSq

variable {x₁ x₂ x₃ x₄} (sq : BicartSq x₁ x₂ x₃ x₄)

include sq

/--
lemma `le₁₂` / 引理 `le₁₂`

English:
lemma le₁₂
  statement: x₁ <= x₂
  proof: by grind

中文:
引理 le₁₂
  结论: x₁ <= x₂
  证明: by grind
-/
lemma le₁₂ : x₁ <= x₂ := by grind
/--
lemma `le₁₃` / 引理 `le₁₃`

English:
lemma le₁₃
  statement: x₁ <= x₃
  proof: by grind

中文:
引理 le₁₃
  结论: x₁ <= x₃
  证明: by grind
-/
lemma le₁₃ : x₁ <= x₃ := by grind
/--
lemma `le₂₄` / 引理 `le₂₄`

English:
lemma le₂₄
  statement: x₂ <= x₄
  proof: by grind

中文:
引理 le₂₄
  结论: x₂ <= x₄
  证明: by grind
-/
lemma le₂₄ : x₂ <= x₄ := by grind
/--
lemma `le₃₄` / 引理 `le₃₄`

English:
lemma le₃₄
  statement: x₃ <= x₄
  proof: by grind

中文:
引理 le₃₄
  结论: x₃ <= x₄
  证明: by grind
-/
lemma le₃₄ : x₃ <= x₄ := by grind

/--
lemma `commSq` / 引理 `commSq`

English:
lemma commSq
  statement: CommSq (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
  proof: ⟨rfl⟩

中文:
引理 commSq
  结论: CommSq (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
  证明: ⟨rfl⟩
-/
lemma commSq : CommSq (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
    (homOfLE sq.le₂₄) (homOfLE sq.le₃₄) := ⟨rfl⟩

end BicartSq

end Lattice

namespace CompleteLattice

variable {T : Type u} [CompleteLattice T] {ι : Type*} (x : T) (u : ι -> T) (v : ι -> ι -> T)

/--
Definition of `MulticoequalizerDiagram` / `MulticoequalizerDiagram` 的定义

English:
structure MulticoequalizerDiagram
  parameters: : Prop where
  axioms and operations (2):
    - iSup_eq : ⨆ (i : ι), u i = x
    - eq_inf((i j : ι)) : v i j = u i ⊓ u j

中文:
结构 MulticoequalizerDiagram
  参数: : 命题 where
  公理与运算 (2 个):
    - iSup_eq : ⨆ (i : ι), u i = x
    - eq_inf((i j : ι)) : v i j = u i ⊓ u j
-/
structure MulticoequalizerDiagram : Prop where
  iSup_eq : ⨆ (i : ι), u i = x
  eq_inf (i j : ι) : v i j = u i ⊓ u j

namespace MulticoequalizerDiagram

attribute [local grind] MulticoequalizerDiagram
attribute [local grind =] MultispanShape.prod_fst MultispanShape.prod_snd

variable {x u v} (d : MulticoequalizerDiagram x u v)

/-- The multispan index in the category associated to the complete lattice `T`
given by the objects `u i` and the minima `v i j = u i ⊓ u j`,
when `d : MulticoequalizerDiagram x u v`. -/
@[simps]
/--
Definition of `multispanIndex` / `multispanIndex` 的定义

English:
definition multispanIndex
  signature: : MultispanIndex (.prod ι) T where
  body: fun ⟨i, j⟩ => v i j
  right := u
  fst _ := homOfLE (by grind)
  snd _ := homOfLE (by grind)

中文:
定义 multispanIndex
  签名: : MultispanIndex (.prod ι) T where
  定义体: fun ⟨i, j⟩ => v i j
  right := u
  fst _ := homOfLE (by grind)
  snd _ := homOfLE (by grind)
-/
def multispanIndex : MultispanIndex (.prod ι) T where
  left := fun ⟨i, j⟩ => v i j
  right := u
  fst _ := homOfLE (by grind)
  snd _ := homOfLE (by grind)

/-- The multicofork in the category associated to the complete lattice `T`
associated to `d : MulticoequalizerDiagram x u v` with `x : T`.
(In the case `T := Set X`, this multicofork becomes colimit after the application
of the obvious functor `Set X ⥤ Type _`.) -/
@[simps! pt]
/--
Definition of `multicofork` / `multicofork` 的定义

English:
definition multicofork
  signature: : Multicofork d.multispanIndex
  body: Multicofork.ofπ _ x (fun i => homOfLE (by grind [multispanIndex_right, le_iSup_iff]))
    (fun _ => rfl)

中文:
定义 multicofork
  签名: : Multicofork d.multispanIndex
  定义体: Multicofork.ofπ _ x (fun i => homOfLE (by grind [multispanIndex_right, le_iSup_iff]))
    (fun _ => rfl)

Depends on / 依赖: Multicofork, Multicofork.of, homOfLE, le_iSup_iff, multispanIndex_right
-/
def multicofork : Multicofork d.multispanIndex :=
  Multicofork.ofπ _ x (fun i => homOfLE (by grind [multispanIndex_right, le_iSup_iff]))
    (fun _ => rfl)

end MulticoequalizerDiagram

end CompleteLattice

/--
lemma `Lattice.BicartSq.multicoequalizerDiagram` / 引理 `Lattice.BicartSq.multicoequalizerDiagram`

English:
lemma Lattice.BicartSq.multicoequalizerDiagram
  statement: {T : Type u} [CompleteLattice T]
  proof: by rw [← sq.sup_eq, sup_comm, sup_eq_iSup]
  eq_inf i j := by grind

中文:
引理 Lattice.BicartSq.multicoequalizerDiagram
  结论: {T : 类型u} [CompleteLattice T]
  证明: by rw [← sq.sup_eq, sup_comm, sup_eq_iSup]
  eq_inf i j := by grind
-/
lemma Lattice.BicartSq.multicoequalizerDiagram {T : Type u} [CompleteLattice T]
    {x₁ x₂ x₃ x₄} (sq : BicartSq x₁ x₂ x₃ x₄) :
    CompleteLattice.MulticoequalizerDiagram (T := T) x₄
      (fun i => bif i then x₃ else x₂)
      (fun i j => bif i then bif j then x₃ else x₁
        else bif j then x₁ else x₂) where
  iSup_eq := by rw [← sq.sup_eq, sup_comm, sup_eq_iSup]
  eq_inf i j := by grind
