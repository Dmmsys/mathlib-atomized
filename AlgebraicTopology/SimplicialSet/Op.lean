/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# The covariant involution of the category of simplicial sets

In this file, we define the covariant involution `opFunctor : SSet ⥤ SSet`
of the category of simplicial sets that is induced by the
covariant involution `SimplexCategory.op : SimplexCategory ⥤ SimplexCategory`.
We use an abbreviation `X.op` for `opFunctor.obj X`.


## TODO

* Show that this involution sends `Δ[n]` to itself, and that via
  this identification, the horn `horn n i` is sent to `horn n i.rev` (@joelriou)
* Construct an isomorphism `nerve Cᵒᵖ ≅ (nerve C).op` (@robin-carlier)
* Show that the topological realization of `X.op` identifies to the
  topological realization of `X` (@joelriou)

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

/--
Definition of `opFunctor` / `opFunctor` 的定义

English:
definition opFunctor
  signature: : SSet.{u} ⥤ SSet.{u}
  body: SimplicialObject.opFunctor

中文:
定义 opFunctor
  签名: : SSet.{u} ⥤ SSet.{u}
  定义体: SimplicialObject.opFunctor

Depends on / 依赖: SimplicialObject, SimplicialObject.opFunctor, opFunctor
-/
def opFunctor : SSet.{u} ⥤ SSet.{u} := SimplicialObject.opFunctor

/--
Definition of `op` / `op` 的定义

English:
abbreviation op
  signature: (X : SSet.{u})
  body: opFunctor.obj X

中文:
缩写 op
  签名: (X : SSet.{u})
  定义体: opFunctor.obj X
-/
protected abbrev op (X : SSet.{u}) : SSet.{u} := opFunctor.obj X

/--
Definition of `opObjEquiv` / `opObjEquiv` 的定义

English:
definition opObjEquiv
  signature: {X : SSet.{u}} {n : SimplexCategoryᵒᵖ}
  body: Equiv.refl _

中文:
定义 opObjEquiv
  签名: {X : SSet.{u}} {n : SimplexCategoryᵒᵖ}
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def opObjEquiv {X : SSet.{u}} {n : SimplexCategoryᵒᵖ} :
    X.op.obj n ≃ X.obj n := Equiv.refl _

/--
lemma `opFunctor_map` / 引理 `opFunctor_map`

English:
lemma opFunctor_map
  given: {X Y : SSet.{u}} (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ} (x : X.op.obj n)
  proof: rfl

中文:
引理 opFunctor_map
  条件: {X Y : SSet.{u}} (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ} (x : X.op.obj n)
  证明: rfl
-/
lemma opFunctor_map {X Y : SSet.{u}} (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ} (x : X.op.obj n) :
    (opFunctor.map f).app n x = opObjEquiv.symm (f.app _ (opObjEquiv x)) :=
  rfl

/--
lemma `op_map` / 引理 `op_map`

English:
lemma op_map
  given: (X : SSet.{u}) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : X.op.obj n)
  proof: rfl

@[simp]

中文:
引理 op_map
  条件: (X : SSet.{u}) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : X.op.obj n)
  证明: rfl

@[simp]
-/
lemma op_map (X : SSet.{u}) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : X.op.obj n) :
    X.op.map f x =
      opObjEquiv.symm (X.map (SimplexCategory.rev.map f.unop).op (opObjEquiv x)) :=
  rfl

@[simp]
/--
lemma `op_δ` / 引理 `op_δ`

English:
lemma op_δ
  given: (X : SSet.{u}) {n : Nat} (i : Fin (n + 2)) (x : X.op _⦋n + 1⦌)
  proof: by
  simp [SimplicialObject.δ, op_map]

@[simp]

中文:
引理 op_δ
  条件: (X : SSet.{u}) {n : 自然数} (i : 有限集 (n + 2)) (x : X.op _⦋n + 1⦌)
  证明: by
  simp [SimplicialObject.δ, op_map]

@[simp]

Depends on / 依赖: SimplicialObject, op_map
-/
lemma op_δ (X : SSet.{u}) {n : Nat} (i : Fin (n + 2)) (x : X.op _⦋n + 1⦌) :
    X.op.δ i x = opObjEquiv.symm (X.δ i.rev (opObjEquiv x)) := by
  simp [SimplicialObject.δ, op_map]

@[simp]
/--
lemma `op_σ` / 引理 `op_σ`

English:
lemma op_σ
  given: (X : SSet.{u}) {n : Nat} (i : Fin (n + 1)) (x : X.op _⦋n⦌)
  proof: by
  simp [SimplicialObject.σ, op_map]

中文:
引理 op_σ
  条件: (X : SSet.{u}) {n : 自然数} (i : 有限集 (n + 1)) (x : X.op _⦋n⦌)
  证明: by
  simp [SimplicialObject.σ, op_map]

Depends on / 依赖: SimplicialObject, op_map
-/
lemma op_σ (X : SSet.{u}) {n : Nat} (i : Fin (n + 1)) (x : X.op _⦋n⦌) :
    X.op.σ i x = opObjEquiv.symm (X.σ i.rev (opObjEquiv x)) := by
  simp [SimplicialObject.σ, op_map]

/--
lemma `δ_opObjEquiv` / 引理 `δ_opObjEquiv`

English:
lemma δ_opObjEquiv
  given: (X : SSet.{u}) {n : Nat} (i : Fin (n + 2)) (x : X.op _⦋n + 1⦌)
  proof: by
  simp

中文:
引理 δ_opObjEquiv
  条件: (X : SSet.{u}) {n : 自然数} (i : 有限集 (n + 2)) (x : X.op _⦋n + 1⦌)
  证明: by
  simp
-/
lemma δ_opObjEquiv (X : SSet.{u}) {n : Nat} (i : Fin (n + 2)) (x : X.op _⦋n + 1⦌) :
    X.δ i (opObjEquiv x) = opObjEquiv (X.op.δ i.rev x) := by
  simp

/--
lemma `σ_opObjEquiv` / 引理 `σ_opObjEquiv`

English:
lemma σ_opObjEquiv
  given: (X : SSet.{u}) {n : Nat} (i : Fin (n + 1)) (x : X.op _⦋n⦌)
  proof: by
  simp

中文:
引理 σ_opObjEquiv
  条件: (X : SSet.{u}) {n : 自然数} (i : 有限集 (n + 1)) (x : X.op _⦋n⦌)
  证明: by
  simp
-/
lemma σ_opObjEquiv (X : SSet.{u}) {n : Nat} (i : Fin (n + 1)) (x : X.op _⦋n⦌) :
    X.σ i (opObjEquiv x) = opObjEquiv (X.op.σ i.rev x) := by
  simp

attribute [local simp] op_map in
/-- The functor `opFunctor : SSet ⥤ SSet` is an involution. -/
@[simps!]
/--
Definition of `opFunctorCompOpFunctorIso` / `opFunctorCompOpFunctorIso` 的定义

English:
definition opFunctorCompOpFunctorIso
  signature: : opFunctor.{u} ⋙ opFunctor ≅ 𝟭 _
  body: dsimp% NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun n => Equiv.toIso (opObjEquiv.trans opObjEquiv)))

中文:
定义 opFunctorCompOpFunctorIso
  签名: : opFunctor.{u} ⋙ opFunctor ≅ 𝟭 _
  定义体: dsimp% NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun n => Equiv.toIso (opObjEquiv.trans opObjEquiv)))

Depends on / 依赖: Equiv.toIso, NatIso, NatIso.ofComponents, ofComponents, opObjEquiv, opObjEquiv.trans
-/
def opFunctorCompOpFunctorIso : opFunctor.{u} ⋙ opFunctor ≅ 𝟭 _ :=
  dsimp% NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun n => Equiv.toIso (opObjEquiv.trans opObjEquiv)))

/-- The covariant involution `opFunctor : SSet ⥤ SSet`,
as an equivalence of categories. -/
@[simps]
/--
Definition of `opEquivalence` / `opEquivalence` 的定义

English:
definition opEquivalence
  signature: : SSet.{u} ≌ SSet.{u} where
  body: opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso

中文:
定义 opEquivalence
  签名: : SSet.{u} ≌ SSet.{u} where
  定义体: opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso

Depends on / 依赖: opFunctor
-/
def opEquivalence : SSet.{u} ≌ SSet.{u} where
  functor := opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso

end SSet
