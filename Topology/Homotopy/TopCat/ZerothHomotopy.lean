/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.TopCat.Path

/-!
# `ZerothHomotopy` and connected components of `TopCat.toSSet.obj X`

In this file, given `X : TopCat`, we define a bijection
`TopCat.zerothHomotopyEquiv` between `ZerothHomotopy X` and
`(TopCat.toSSet.obj X).π₀`.

-/

@[expose] public section

universe u

open Simplicial

namespace TopCat

variable {X : TopCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toSSetObj₁Equiv` / `toSSetObj₁Equiv` 的定义

English:
definition toSSetObj₁Equiv
  signature: :
  body: (toSSetObjEquiv _ _).trans
    { toFun f := ofHom (f.comp (toContinuousMap TopCat.stdSimplexHomeomorphI.symm))
      invFun f := f.hom.comp TopCat.stdSimplexHomeomorphI
      left_inv _ := by simp
      right_inv _ := by simp }

中文:
定义 toSSetObj₁Equiv
  签名: :
  定义体: (toSSetObjEquiv _ _).trans
    { toFun f := ofHom (f.comp (toContinuousMap TopCat.stdSimplexHomeomorphI.symm))
      invFun f := f.hom.comp TopCat.stdSimplexHomeomorphI
      left_inv _ := by simp
      right_inv _ := by simp }

Depends on / 依赖: TopCat, TopCat.stdSimplexHomeomorphI, TopCat.stdSimplexHomeomorphI.symm, f.comp, f.hom.comp, invFun, left_inv, right_inv, stdSimplexHomeomorphI, toContinuousMap, toSSetObjEquiv
-/
noncomputable def toSSetObj₁Equiv :
    toSSet.obj X _⦋1⦌ ≃ (I ⟶ X) :=
  (toSSetObjEquiv _ _).trans
    { toFun f := ofHom (f.comp (toContinuousMap TopCat.stdSimplexHomeomorphI.symm))
      invFun f := f.hom.comp TopCat.stdSimplexHomeomorphI
      left_inv _ := by simp
      right_inv _ := by simp }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `toSSetObj₁Equiv_apply_zero` / 引理 `toSSetObj₁Equiv_apply_zero`

English:
lemma toSSetObj₁Equiv_apply_zero
  given: (s : toSSet.obj X _⦋1⦌)
  proof: by
  simp [toSSetObj₀Equiv, toSSetObj₁Equiv, -ContinuousMap.coe_mk,
    Subsingleton.elim (default : stdSimplex Real (Fin 1)) (stdSimplex.vertex 0)]

中文:
引理 toSSetObj₁Equiv_apply_zero
  条件: (s : toSSet.obj X _⦋1⦌)
  证明: by
  simp [toSSetObj₀Equiv, toSSetObj₁Equiv, -ContinuousMap.coe_mk,
    Subsingleton.elim (default : stdSimplex Real (Fin 1)) (stdSimplex.vertex 0)]

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, Subsingleton, Subsingleton.elim, coe_mk, stdSimplex, stdSimplex.vertex, vertex
-/
lemma toSSetObj₁Equiv_apply_zero (s : toSSet.obj X _⦋1⦌) :
    X.toSSetObj₁Equiv s 0 = toSSetObj₀Equiv ((toSSet.obj X).δ 1 s) := by
  simp [toSSetObj₀Equiv, toSSetObj₁Equiv, -ContinuousMap.coe_mk,
    Subsingleton.elim (default : stdSimplex Real (Fin 1)) (stdSimplex.vertex 0)]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `toSSetObj₁Equiv_apply_one` / 引理 `toSSetObj₁Equiv_apply_one`

English:
lemma toSSetObj₁Equiv_apply_one
  given: (s : toSSet.obj X _⦋1⦌)
  proof: by
  simp [toSSetObj₀Equiv, toSSetObj₁Equiv, -ContinuousMap.coe_mk,
    Subsingleton.elim (default : stdSimplex Real (Fin 1)) (stdSimplex.vertex 0)]

@[simp]

中文:
引理 toSSetObj₁Equiv_apply_one
  条件: (s : toSSet.obj X _⦋1⦌)
  证明: by
  simp [toSSetObj₀Equiv, toSSetObj₁Equiv, -ContinuousMap.coe_mk,
    Subsingleton.elim (default : stdSimplex Real (Fin 1)) (stdSimplex.vertex 0)]

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, Subsingleton, Subsingleton.elim, coe_mk, stdSimplex, stdSimplex.vertex, vertex
-/
lemma toSSetObj₁Equiv_apply_one (s : toSSet.obj X _⦋1⦌) :
    X.toSSetObj₁Equiv s 1 = toSSetObj₀Equiv ((toSSet.obj X).δ 0 s) := by
  simp [toSSetObj₀Equiv, toSSetObj₁Equiv, -ContinuousMap.coe_mk,
    Subsingleton.elim (default : stdSimplex Real (Fin 1)) (stdSimplex.vertex 0)]

@[simp]
/--
lemma `δ_one_toSSetObj₁Equiv.symm` / 引理 `δ_one_toSSetObj₁Equiv.symm`

English:
lemma δ_one_toSSetObj₁Equiv.symm
  given: (f : I ⟶ X)
  proof: toSSetObj₀Equiv.injective (by simp [← toSSetObj₁Equiv_apply_zero])

@[simp]

中文:
引理 δ_one_toSSetObj₁Equiv.symm
  条件: (f : I ⟶ X)
  证明: toSSetObj₀Equiv.injective (by simp [← toSSetObj₁Equiv_apply_zero])

@[simp]

Depends on / 依赖: Equiv.injective, injective
-/
lemma δ_one_toSSetObj₁Equiv.symm (f : I ⟶ X) :
    (toSSet.obj X).δ 1 (toSSetObj₁Equiv.symm f) =
      toSSetObj₀Equiv.symm (f 0) :=
  toSSetObj₀Equiv.injective (by simp [← toSSetObj₁Equiv_apply_zero])

@[simp]
/--
lemma `δ_zero_toSSetObj₁Equiv.symm` / 引理 `δ_zero_toSSetObj₁Equiv.symm`

English:
lemma δ_zero_toSSetObj₁Equiv.symm
  given: (f : I ⟶ X)
  proof: toSSetObj₀Equiv.injective (by simp [← toSSetObj₁Equiv_apply_one])

中文:
引理 δ_zero_toSSetObj₁Equiv.symm
  条件: (f : I ⟶ X)
  证明: toSSetObj₀Equiv.injective (by simp [← toSSetObj₁Equiv_apply_one])

Depends on / 依赖: Equiv.injective, injective
-/
lemma δ_zero_toSSetObj₁Equiv.symm (f : I ⟶ X) :
    (toSSet.obj X).δ 0 (toSSetObj₁Equiv.symm f) =
      toSSetObj₀Equiv.symm (f 1) :=
  toSSetObj₀Equiv.injective (by simp [← toSSetObj₁Equiv_apply_one])

/-- Given two points `x` and `y` of `X : TopCat`, this is the bijection between
edges in the simplicial set `toSSet.obj X` connecting the vertices corresponding
to `x` and `y`, and paths from `x` to `y`. -/
@[simps]
/--
Definition of `toSSetObjEdgeEquiv` / `toSSetObjEdgeEquiv` 的定义

English:
definition toSSetObjEdgeEquiv
  signature: {x y : X}
  body: { hom := toSSetObj₁Equiv e.edge }
  invFun p := SSet.Edge.mk (toSSetObj₁Equiv.symm p.hom)
  left_inv _ := by aesop
  right_inv _ := by aesop

中文:
定义 toSSetObjEdgeEquiv
  签名: {x y : X}
  定义体: { hom := toSSetObj₁Equiv e.edge }
  invFun p := SSet.Edge.mk (toSSetObj₁Equiv.symm p.hom)
  left_inv _ := by aesop
  right_inv _ := by aesop

Depends on / 依赖: e.edge
-/
noncomputable def toSSetObjEdgeEquiv {x y : X} :
    SSet.Edge (toSSetObj₀Equiv.symm x) (toSSetObj₀Equiv.symm y) ≃ X.Path x y where
  toFun e := { hom := toSSetObj₁Equiv e.edge }
  invFun p := SSet.Edge.mk (toSSetObj₁Equiv.symm p.hom)
  left_inv _ := by aesop
  right_inv _ := by aesop

/--
Definition of `zerothHomotopyEquiv` / `zerothHomotopyEquiv` 的定义

English:
definition zerothHomotopyEquiv
  signature: : ZerothHomotopy X ≃ (toSSet.obj X).π₀ where
  body: ZerothHomotopy.lift (SSet.π₀.mk ∘ toSSetObj₀Equiv.symm)
      (fun _ _ p => SSet.π₀.sound (toSSetObjEdgeEquiv.symm (pathEquiv.symm p)))
  invFun := SSet.π₀.lift (ZerothHomotopy.mk ∘ toSSetObj₀Equiv) (fun x y e => by
    obtain ⟨x, rfl⟩ := toSSetObj₀Equiv.symm.surjective x
    obtain ⟨y, rfl⟩ := toSS

中文:
定义 zerothHomotopyEquiv
  签名: : ZerothHomotopy X ≃ (toSSet.obj X).π₀ where
  定义体: ZerothHomotopy.lift (SSet.π₀.mk ∘ toSSetObj₀Equiv.symm)
      (fun _ _ p => SSet.π₀.sound (toSSetObjEdgeEquiv.symm (pathEquiv.symm p)))
  invFun := SSet.π₀.lift (ZerothHomotopy.mk ∘ toSSetObj₀Equiv) (fun x y e => by
    obtain ⟨x, rfl⟩ := toSSetObj₀Equiv.symm.surjective x
    obtain ⟨y, rfl⟩ := toSS

Depends on / 依赖: Equiv.symm, Equiv.symm.surjective, ZerothHomotopy, ZerothHomotopy.lift, ZerothHomotopy.mk, ZerothHomotopy.sound, invFun, left_inv, pathEquiv, pathEquiv.symm, right_inv, surjective, toSSetObjEdgeEquiv, toSSetObjEdgeEquiv.symm
-/
noncomputable def zerothHomotopyEquiv : ZerothHomotopy X ≃ (toSSet.obj X).π₀ where
  toFun :=
    ZerothHomotopy.lift (SSet.π₀.mk ∘ toSSetObj₀Equiv.symm)
      (fun _ _ p => SSet.π₀.sound (toSSetObjEdgeEquiv.symm (pathEquiv.symm p)))
  invFun := SSet.π₀.lift (ZerothHomotopy.mk ∘ toSSetObj₀Equiv) (fun x y e => by
    obtain ⟨x, rfl⟩ := toSSetObj₀Equiv.symm.surjective x
    obtain ⟨y, rfl⟩ := toSSetObj₀Equiv.symm.surjective y
    exact ZerothHomotopy.sound (pathEquiv (toSSetObjEdgeEquiv e)))
  left_inv x := by induction x; simp
  right_inv x := by induction x; simp

@[simp]
/--
lemma `zerothHomotopyEquiv_mk` / 引理 `zerothHomotopyEquiv_mk`

English:
lemma zerothHomotopyEquiv_mk
  given: (x : X)
  proof: rfl

@[simp]

中文:
引理 zerothHomotopyEquiv_mk
  条件: (x : X)
  证明: rfl

@[simp]
-/
lemma zerothHomotopyEquiv_mk (x : X) :
    zerothHomotopyEquiv (.mk x) = .mk (toSSetObj₀Equiv.symm x) := rfl

@[simp]
/--
lemma `zerothHomotopyEquiv_symm_mk` / 引理 `zerothHomotopyEquiv_symm_mk`

English:
lemma zerothHomotopyEquiv_symm_mk
  given: (x : (toSSet.obj X) _⦋0⦌)
  proof: rfl

中文:
引理 zerothHomotopyEquiv_symm_mk
  条件: (x : (toSSet.obj X) _⦋0⦌)
  证明: rfl
-/
lemma zerothHomotopyEquiv_symm_mk (x : (toSSet.obj X) _⦋0⦌) :
    zerothHomotopyEquiv.symm (.mk x) = .mk (toSSetObj₀Equiv x) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PathConnectedSpace
  signature: X] : (toSSet.obj X).IsConnected
  body: by
  let : Unique (ZerothHomotopy X) := Nonempty.some (by
    rw [unique_iff_subsingleton_and_nonempty]
    constructor <;> infer_instance)
  rw [SSet.isConnected_iff_nonempty_unique]
  exact ⟨zerothHomotopyEquiv.symm.unique⟩

中文:
实例 [道路连通空间
  签名: X] : (toSSet.obj X).是连通
  定义体: by
  let : Unique (ZerothHomotopy X) := Nonempty.some (by
    rw [unique_iff_subsingleton_and_nonempty]
    constructor <;> infer_instance)
  rw [SSet.isConnected_iff_nonempty_unique]
  exact ⟨zerothHomotopyEquiv.symm.unique⟩

Depends on / 依赖: Nonempty, Nonempty.some, SSet.isConnected_iff_nonempty_unique, Unique, ZerothHomotopy, infer_instance, isConnected_iff_nonempty_unique, unique, unique_iff_subsingleton_and_nonempty, zerothHomotopyEquiv, zerothHomotopyEquiv.symm.unique
-/
instance [PathConnectedSpace X] : (toSSet.obj X).IsConnected := by
  let : Unique (ZerothHomotopy X) := Nonempty.some (by
    rw [unique_iff_subsingleton_and_nonempty]
    constructor <;> infer_instance)
  rw [SSet.isConnected_iff_nonempty_unique]
  exact ⟨zerothHomotopyEquiv.symm.unique⟩

end TopCat
