/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory

/-!
# Homology of complexes in concrete categories

The homology of short complexes in concrete categories was studied in
`Mathlib/Algebra/Homology/ShortComplex/ConcreteCategory.lean`. In this file,
we introduce specific definitions and lemmas for the homology
of homological complexes in concrete categories. In particular,
we give a computation of the connecting homomorphism of
the homology sequence in terms of (co)cycles.

-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {FC : C -> C -> Type*} {CC : C -> Type v}
  [forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC] [HasForget₂ C Ab.{v}]
  [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  {ι : Type*} {c : ComplexShape ι}

namespace HomologicalComplex

variable (K : HomologicalComplex C c)

/--
Definition of `cyclesMk` / `cyclesMk` 的定义

English:
definition cyclesMk
  signature: {i : ι} (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i = j)
  body: (K.sc i).cyclesMk x (by subst hj; exact hx)

@[simp]

中文:
定义 cyclesMk
  签名: {i : ι} (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i = j)
  定义体: (K.sc i).cyclesMk x (by subst hj; exact hx)

@[simp]

Depends on / 依赖: K.sc, cyclesMk
-/
noncomputable def cyclesMk {i : ι} (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i = j)
    (hx : ((forget₂ C Ab).map (K.d i j)) x = 0) :
    (forget₂ C Ab).obj (K.cycles i) :=
  (K.sc i).cyclesMk x (by subst hj; exact hx)

@[simp]
/--
lemma `i_cyclesMk` / 引理 `i_cyclesMk`

English:
lemma i_cyclesMk
  statement: {i : ι} (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i = j)
  proof: by
  subst hj
  apply (K.sc i).i_cyclesMk

中文:
引理 i_cyclesMk
  结论: {i : ι} (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i = j)
  证明: by
  subst hj
  apply (K.sc i).i_cyclesMk

Depends on / 依赖: K.sc, i_cyclesMk
-/
lemma i_cyclesMk {i : ι} (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i = j)
    (hx : ((forget₂ C Ab).map (K.d i j)) x = 0) :
    ((forget₂ C Ab).map (K.iCycles i)) (K.cyclesMk x j hj hx) = x := by
  subst hj
  apply (K.sc i).i_cyclesMk

end HomologicalComplex

namespace CategoryTheory

namespace ShortComplex

namespace ShortExact

variable {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

/--
lemma `δ_apply'` / 引理 `δ_apply'`

English:
lemma δ_apply'
  statement: (x₃ : (forget₂ C Ab).obj (S.X₃.homology i))
  proof: (HomologicalComplex.HomologySequence.snakeInput hS i j hij).δ_apply' x₃ x₂ x₁ h₂ h₁

include hS in

中文:
引理 δ_apply'
  结论: (x₃ : (forget₂ C Ab).obj (S.X₃.homology i))
  证明: (HomologicalComplex.HomologySequence.snakeInput hS i j hij).δ_apply' x₃ x₂ x₁ h₂ h₁

include hS in

Depends on / 依赖: HomologicalComplex, HomologicalComplex.HomologySequence.snakeInput, HomologySequence, snakeInput
-/
lemma δ_apply' (x₃ : (forget₂ C Ab).obj (S.X₃.homology i))
    (x₂ : (forget₂ C Ab).obj (S.X₂.opcycles i))
    (x₁ : (forget₂ C Ab).obj (S.X₁.cycles j))
    (h₂ : (forget₂ C Ab).map (HomologicalComplex.opcyclesMap S.g i) x₂ =
      (forget₂ C Ab).map (S.X₃.homologyι i) x₃)
    (h₁ : (forget₂ C Ab).map (HomologicalComplex.cyclesMap S.f j) x₁ =
      (forget₂ C Ab).map (S.X₂.opcyclesToCycles i j) x₂) :
    (forget₂ C Ab).map (hS.δ i j hij) x₃ = (forget₂ C Ab).map (S.X₁.homologyπ j) x₁ :=
  (HomologicalComplex.HomologySequence.snakeInput hS i j hij).δ_apply' x₃ x₂ x₁ h₂ h₁

include hS in
/--
theorem `d_eq_zero_of_f_eq_d_apply` / 定理 `d_eq_zero_of_f_eq_d_apply`

English:
theorem d_eq_zero_of_f_eq_d_apply
  proof: by
  have := hS.mono_f
  apply (Preadditive.mono_iff_injective (S.f.f k)).1 inferInstance
  rw [← ConcreteCategory.forget₂_comp_apply]; rw [← HomologicalComplex.Hom.comm]; rw [ConcreteCategory.forget₂_comp_apply]; rw [hx₁]; rw [← ConcreteCategory.forget₂_comp_apply]; rw [HomologicalComplex.d_comp_d]

中文:
定理 d_eq_zero_of_f_eq_d_apply
  证明: by
  have := hS.mono_f
  apply (Preadditive.mono_iff_injective (S.f.f k)).1 inferInstance
  rw [← ConcreteCategory.forget₂_comp_apply]; rw [← HomologicalComplex.Hom.comm]; rw [ConcreteCategory.forget₂_comp_apply]; rw [hx₁]; rw [← ConcreteCategory.forget₂_comp_apply]; rw [HomologicalComplex.d_comp_d]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.forget, Functor, Functor.map_zero, HomologicalComplex, HomologicalComplex.Hom.comm, HomologicalComplex.d_comp_d, Preadditive, Preadditive.mono_iff_injective, S.f.f, d_comp_d, hS.mono_f, map_zero, mono_f, mono_iff_injective
-/
theorem d_eq_zero_of_f_eq_d_apply
    (x₂ : ((forget₂ C Ab).obj (S.X₂.X i))) (x₁ : ((forget₂ C Ab).obj (S.X₁.X j)))
    (hx₁ : ((forget₂ C Ab).map (S.f.f j)) x₁ = ((forget₂ C Ab).map (S.X₂.d i j)) x₂) (k : ι) :
    ((forget₂ C Ab).map (S.X₁.d j k)) x₁ = 0 := by
  have := hS.mono_f
  apply (Preadditive.mono_iff_injective (S.f.f k)).1 inferInstance
  rw [← ConcreteCategory.forget₂_comp_apply]; rw [← HomologicalComplex.Hom.comm]; rw [ConcreteCategory.forget₂_comp_apply]; rw [hx₁]; rw [← ConcreteCategory.forget₂_comp_apply]; rw [HomologicalComplex.d_comp_d]; rw [Functor.map_zero]; rw [map_zero]
  rfl

/--
lemma `δ_apply` / 引理 `δ_apply`

English:
lemma δ_apply
  statement: (x₃ : (forget₂ C Ab).obj (S.X₃.X i))
  proof: by
  refine hS.δ_apply' i j hij _ ((forget₂ C Ab).map (S.X₂.pOpcycles i) x₂) _ ?_ ?_
  · rw [← ConcreteCategory.forget₂_comp_apply, ← ConcreteCategory.forget₂_comp_apply,
      HomologicalComplex.p_opcyclesMap, Functor.map_comp, ConcreteCategory.comp_apply,
      HomologicalComplex.homology_π_ι, Con

中文:
引理 δ_apply
  结论: (x₃ : (forget₂ C Ab).obj (S.X₃.X i))
  证明: by
  refine hS.δ_apply' i j hij _ ((forget₂ C Ab).map (S.X₂.pOpcycles i) x₂) _ ?_ ?_
  · rw [← ConcreteCategory.forget₂_comp_apply, ← ConcreteCategory.forget₂_comp_apply,
      HomologicalComplex.p_opcyclesMap, Functor.map_comp, ConcreteCategory.comp_apply,
      HomologicalComplex.homology_π_ι, Con

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, ConcreteCategory.forget, Functor, Functor.map_comp, HomologicalC, HomologicalComplex, HomologicalComplex.homology_, HomologicalComplex.i_cyclesMk, HomologicalComplex.p_opcyclesMap, Preadditive, Preadditive.mono_iff_injective, comp_apply, conv_lhs, iCycles, i_cyclesMk, map_comp, mono_iff_injective, pOpcycles, p_opcyclesMap
-/
lemma δ_apply (x₃ : (forget₂ C Ab).obj (S.X₃.X i))
    (hx₃ : (forget₂ C Ab).map (S.X₃.d i j) x₃ = 0)
    (x₂ : (forget₂ C Ab).obj (S.X₂.X i)) (hx₂ : (forget₂ C Ab).map (S.g.f i) x₂ = x₃)
    (x₁ : (forget₂ C Ab).obj (S.X₁.X j))
    (hx₁ : (forget₂ C Ab).map (S.f.f j) x₁ = (forget₂ C Ab).map (S.X₂.d i j) x₂)
    (k : ι) (hk : c.next j = k) :
    (forget₂ C Ab).map (hS.δ i j hij)
      ((forget₂ C Ab).map (S.X₃.homologyπ i) (S.X₃.cyclesMk x₃ j (c.next_eq' hij) hx₃)) =
        (forget₂ C Ab).map (S.X₁.homologyπ j) (S.X₁.cyclesMk x₁ k hk
          (d_eq_zero_of_f_eq_d_apply hS _ _ x₂ x₁ hx₁ _)) := by
  refine hS.δ_apply' i j hij _ ((forget₂ C Ab).map (S.X₂.pOpcycles i) x₂) _ ?_ ?_
  · rw [← ConcreteCategory.forget₂_comp_apply, ← ConcreteCategory.forget₂_comp_apply,
      HomologicalComplex.p_opcyclesMap, Functor.map_comp, ConcreteCategory.comp_apply,
      HomologicalComplex.homology_π_ι, ConcreteCategory.forget₂_comp_apply, hx₂,
      HomologicalComplex.i_cyclesMk]
  · apply (Preadditive.mono_iff_injective (S.X₂.iCycles j)).1 inferInstance
    conv_lhs =>
      rw [← ConcreteCategory.forget₂_comp_apply]; rw [HomologicalComplex.cyclesMap_i]; rw [ConcreteCategory.forget₂_comp_apply]; rw [HomologicalComplex.i_cyclesMk]; rw [hx₁]
    conv_rhs =>
      rw [← ConcreteCategory.forget₂_comp_apply]; rw [← ConcreteCategory.forget₂_comp_apply]; rw [HomologicalComplex.pOpcycles_opcyclesToCycles_assoc]; rw [HomologicalComplex.toCycles_i]

end ShortExact

end ShortComplex

end CategoryTheory
