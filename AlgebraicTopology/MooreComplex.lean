/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
## Moore complex

We construct the normalized Moore complex, as a functor
`SimplicialObject C ⥤ ChainComplex C ℕ`,
for any abelian category `C`.

The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.

The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.

This functor is one direction of the Dold-Kan equivalence, which we're still working towards.

### References

* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex
-/

@[expose] public section


universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits

open Opposite

open scoped Simplicial

namespace AlgebraicTopology

variable {C : Type*} [Category* C] [Abelian C]

attribute [local instance] Abelian.hasPullbacks

/-! The definitions in this namespace are all auxiliary definitions for `NormalizedMooreComplex`
and should usually only be accessed via that. -/


namespace NormalizedMooreComplex

open CategoryTheory.Subobject

variable (X : SimplicialObject C)

/--
Definition of `objX` / `objX` 的定义

English:
definition objX
  signature: : forall n : Nat, Subobject (X.obj (op ⦋n⦌))

中文:
定义 objX
  签名: : 对任意 n : 自然数, Subobject (X.obj (op ⦋n⦌))
-/
def objX : forall n : Nat, Subobject (X.obj (op ⦋n⦌))
  | 0 => ⊤
  | n + 1 => Finset.univ.inf fun k : Fin (n + 1) => kernelSubobject (X.δ k.succ)

/--
theorem `objX_zero` / 定理 `objX_zero`

English:
theorem objX_zero
  statement: objX X 0 = ⊤
  proof: rfl

中文:
定理 objX_zero
  结论: objX X 0 = ⊤
  证明: rfl
-/
@[simp] theorem objX_zero : objX X 0 = ⊤ :=
  rfl

/--
theorem `objX_add_one` / 定理 `objX_add_one`

English:
theorem objX_add_one
  given: (n)
  proof: rfl

中文:
定理 objX_add_one
  条件: (n)
  证明: rfl
-/
@[simp] theorem objX_add_one (n) :
    objX X (n + 1) = Finset.univ.inf fun k : Fin (n + 1) => kernelSubobject (X.δ k.succ) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The differentials in the normalized Moore complex.
-/
@[simp]
/--
Definition of `objD` / `objD` 的定义

English:
definition objD
  signature: : forall n : Nat, (objX X (n + 1) : C) ⟶ (objX X n : C)

中文:
定义 objD
  签名: : 对任意 n : 自然数, (objX X (n + 1) : C) ⟶ (objX X n : C)
-/
def objD : forall n : Nat, (objX X (n + 1) : C) ⟶ (objX X n : C)
  | 0 => Subobject.arrow _ ≫ X.δ (0 : Fin 2) ≫ inv (⊤ : Subobject _).arrow
  | n + 1 => by
    -- The differential is `Subobject.arrow _ ≫ X.δ (0 : Fin (n+3))`,
    -- factored through the intersection of the kernels.
    refine factorThru _ (arrow _ ≫ X.δ (0 : Fin (n + 3))) ?_
    -- We now need to show that it factors!
    -- A morphism factors through an intersection of subobjects if it factors through each.
    refine (finset_inf_factors _).mpr fun i _ => ?_
    -- A morphism `f` factors through the kernel of `g` exactly if `f ≫ g = 0`.
    apply kernelSubobject_factors
    dsimp [objX]
    -- Use a simplicial identity
    rw [Category.assoc]; rw [← Fin.castSucc_zero]; rw [← X.δ_comp_δ (Fin.zero_le i.succ)]
    -- We can rewrite the arrow out of the intersection of all the kernels as a composition
    -- of a morphism we don't care about with the arrow out of the kernel of `X.δ i.succ.succ`.
    rw [← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ i.succ (by simp))]; rw [Category.assoc]; rw [kernelSubobject_arrow_comp_assoc]; rw [zero_comp]; rw [comp_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `d_squared` / 定理 `d_squared`

English:
theorem d_squared
  given: (n : Nat)
  statement: objD X (n + 1) ≫ objD X n = 0
  proof: by
  -- It's a pity we need to do a case split here;
    -- after the first rw the proofs are almost identical
  rcases n with _ | n <;> dsimp [objD]
  · rw [Subobject.factorThru_arrow_assoc, Category.assoc, ← Fin.castSucc_zero,
      ← X.δ_comp_δ_assoc (Fin.zero_le (0 : Fin 2)),
      ← factorThru_

中文:
定理 d_squared
  条件: (n : 自然数)
  结论: objD X (n + 1) ≫ objD X n = 0
  证明: by
  -- It's a pity we need to do a case split here;
    -- after the first rw the proofs are almost identical
  rcases n with _ | n <;> dsimp [objD]
  · rw [Subobject.factorThru_arrow_assoc, Category.assoc, ← Fin.castSucc_zero,
      ← X.δ_comp_δ_assoc (Fin.zero_le (0 : Fin 2)),
      ← factorThru_
-/
theorem d_squared (n : Nat) : objD X (n + 1) ≫ objD X n = 0 := by
  -- It's a pity we need to do a case split here;
    -- after the first rw the proofs are almost identical
  rcases n with _ | n <;> dsimp [objD]
  · rw [Subobject.factorThru_arrow_assoc, Category.assoc, ← Fin.castSucc_zero,
      ← X.δ_comp_δ_assoc (Fin.zero_le (0 : Fin 2)),
      ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ (0 : Fin 2) (by simp)),
      Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]
  · rw [factorThru_right, factorThru_eq_zero, factorThru_arrow_assoc, Category.assoc,
      ← Fin.castSucc_zero,
      ← X.δ_comp_δ (Fin.zero_le (0 : Fin (n + 3))),
      ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ (0 : Fin (n + 3)) (by simp)),
      Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]

/-- The normalized Moore complex functor, on objects.
-/
@[simps!]
/--
Definition of `obj` / `obj` 的定义

English:
definition obj
  signature: (X : SimplicialObject C)
  body: ChainComplex.of (fun n => (objX X n : C))
    (-- the coercion here picks a representative of the subobject
      objD X) (d_squared X)

中文:
定义 obj
  签名: (X : SimplicialObject C)
  定义体: ChainComplex.of (fun n => (objX X n : C))
    (-- the coercion here picks a representative of the subobject
      objD X) (d_squared X)

Depends on / 依赖: ChainComplex, ChainComplex.of, coercion, d_squared, representative, subobject
-/
def obj (X : SimplicialObject C) : ChainComplex C Nat :=
  ChainComplex.of (fun n => (objX X n : C))
    (-- the coercion here picks a representative of the subobject
      objD X) (d_squared X)

variable {X} {Y : SimplicialObject C} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The normalized Moore complex functor, on morphisms.
-/
@[simps!]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : X ⟶ Y)
  body: ChainComplex.ofHom
    (fun n => factorThru _ (arrow _ ≫ f.app (op ⦋n⦌)) (by
      cases n <;> dsimp
      · apply top_factors
      · refine (finset_inf_factors _).mpr fun i _ => kernelSubobject_factors _ _ ?_
        rw [Category.assoc]; rw [SimplicialObject.δ]; rw [← f.naturality]; rw [← factorTh

中文:
定义 map
  签名: (f : X ⟶ Y)
  定义体: ChainComplex.ofHom
    (fun n => factorThru _ (arrow _ ≫ f.app (op ⦋n⦌)) (by
      cases n <;> dsimp
      · apply top_factors
      · refine (finset_inf_factors _).mpr fun i _ => kernelSubobject_factors _ _ ?_
        rw [Category.assoc]; rw [SimplicialObject.δ]; rw [← f.naturality]; rw [← factorTh

Depends on / 依赖: Category, Category.assoc, ChainComplex, ChainComplex.ofHom, Finset, Finset.univ, SimplicialObject, comp_zero, f.app, f.naturality, factorThru, factorThru_arrow, finset_inf_arrow_factors, finset_inf_factors, kernelSubobject_arrow_comp_assoc, kernelSubobject_factors, naturality, top_factors, zero_comp
-/
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom
    (fun n => factorThru _ (arrow _ ≫ f.app (op ⦋n⦌)) (by
      cases n <;> dsimp
      · apply top_factors
      · refine (finset_inf_factors _).mpr fun i _ => kernelSubobject_factors _ _ ?_
        rw [Category.assoc]; rw [SimplicialObject.δ]; rw [← f.naturality]; rw [← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ i (by simp))]; rw [Category.assoc]
        rw [← SimplicialObject.δ_def]; rw [kernelSubobject_arrow_comp_assoc]; rw [zero_comp]; rw [comp_zero]))
    fun n => by cases n <;> dsimp [objD, objX, ChainComplex.of.d] <;> cat_disch

end NormalizedMooreComplex

open NormalizedMooreComplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-- The (normalized) Moore complex of a simplicial object `X` in an abelian category `C`.

The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.

The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.
-/
@[simps]
/--
Definition of `normalizedMooreComplex` / `normalizedMooreComplex` 的定义

English:
definition normalizedMooreComplex
  signature: : SimplicialObject C ⥤ ChainComplex C Nat where
  body: obj
  map f := map f

中文:
定义 normalizedMooreComplex
  签名: : SimplicialObject C ⥤ 链复形 C 自然数 where
  定义体: obj
  map f := map f
-/
def normalizedMooreComplex : SimplicialObject C ⥤ ChainComplex C Nat where
  obj := obj
  map f := map f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- Not `@[simp]` as `simp` can prove this.
/--
theorem `normalizedMooreComplex_objD` / 定理 `normalizedMooreComplex_objD`

English:
theorem normalizedMooreComplex_objD
  given: (X : SimplicialObject C) (n : Nat)
  proof: by
  simp [-objD, -obj_X]

中文:
定理 normalizedMooreComplex_objD
  条件: (X : SimplicialObject C) (n : 自然数)
  证明: by
  simp [-objD, -obj_X]

Depends on / 依赖: obj_X
-/
theorem normalizedMooreComplex_objD (X : SimplicialObject C) (n : Nat) :
    ((normalizedMooreComplex C).obj X).d (n + 1) n = NormalizedMooreComplex.objD X n := by
  simp [-objD, -obj_X]

end AlgebraicTopology
