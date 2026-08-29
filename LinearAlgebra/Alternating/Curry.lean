/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Currying alternating forms

In this file we define `AlternatingMap.curryLeft`
which interprets an alternating map in `n + 1` variables
as a linear map in the 0th variable taking values in the alternating maps in `n` variables.
-/

@[expose] public section

variable {R : Type*} {M M₂ N N₂ : Type*} [CommSemiring R] [AddCommMonoid M]
  [AddCommMonoid M₂] [AddCommMonoid N] [AddCommMonoid N₂] [Module R M] [Module R M₂]
  [Module R N] [Module R N₂] {n : Nat}

namespace AlternatingMap

/-- Given an alternating map `f` in `n+1` variables, split the first variable to obtain
a linear map into alternating maps in `n` variables, given by `x ↦ (m ↦ f (Matrix.vecCons x m))`.
It can be thought of as a map $Hom(\bigwedge^{n+1} M, N) \to Hom(M, Hom(\bigwedge^n M, N))$.

This is `MultilinearMap.curryLeft` for `AlternatingMap`. See also
`AlternatingMap.curryLeftLinearMap`. -/
@[simps apply_toMultilinearMap]
/--
Definition of `curryLeft` / `curryLeft` 的定义

English:
definition curryLeft
  signature: (f : M [⋀^Fin n.succ]->ₗ[R] N)
  body: { f.toMultilinearMap.curryLeft m with
      map_eq_zero_of_eq' v i j hv hij :=
        f.map_eq_zero_of_eq _ (by simpa) ((Fin.succ_injective _).ne hij) }
  map_add' _ _ := ext fun _ => f.map_vecCons_add _ _ _
  map_smul' _ _ := ext fun _ => f.map_vecCons_smul _ _ _

@[simp]

中文:
定义 curryLeft
  签名: (f : M [⋀^Fin n.succ]->ₗ[R] N)
  定义体: { f.toMultilinearMap.curryLeft m with
      map_eq_zero_of_eq' v i j hv hij :=
        f.map_eq_zero_of_eq _ (by simpa) ((Fin.succ_injective _).ne hij) }
  map_add' _ _ := ext fun _ => f.map_vecCons_add _ _ _
  map_smul' _ _ := ext fun _ => f.map_vecCons_smul _ _ _

@[simp]

Depends on / 依赖: Fin.succ_injective, curryLeft, f.map_eq_zero_of_eq, f.map_vecCons_add, f.map_vecCons_smul, f.toMultilinearMap.curryLeft, map_add, map_eq_zero_of_eq, map_smul, map_vecCons_add, map_vecCons_smul, succ_injective, toMultilinearMap
-/
def curryLeft (f : M [⋀^Fin n.succ]->ₗ[R] N) : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N where
  toFun m :=
    { f.toMultilinearMap.curryLeft m with
      map_eq_zero_of_eq' v i j hv hij :=
        f.map_eq_zero_of_eq _ (by simpa) ((Fin.succ_injective _).ne hij) }
  map_add' _ _ := ext fun _ => f.map_vecCons_add _ _ _
  map_smul' _ _ := ext fun _ => f.map_vecCons_smul _ _ _

@[simp]
/--
theorem `curryLeft_apply_apply` / 定理 `curryLeft_apply_apply`

English:
theorem curryLeft_apply_apply
  given: (f : M [⋀^Fin n.succ]->ₗ[R] N) (x : M) (v : Fin n -> M)
  proof: rfl

@[simp]

中文:
定理 curryLeft_apply_apply
  条件: (f : M [⋀^Fin n.succ]->ₗ[R] N) (x : M) (v : Fin n -> M)
  证明: rfl

@[simp]
-/
theorem curryLeft_apply_apply (f : M [⋀^Fin n.succ]->ₗ[R] N) (x : M) (v : Fin n -> M) :
    curryLeft f x v = f (Matrix.vecCons x v) :=
  rfl

@[simp]
/--
theorem `curryLeft_zero` / 定理 `curryLeft_zero`

English:
theorem curryLeft_zero
  statement: curryLeft (0 : M [⋀^Fin n.succ]->ₗ[R] N) = 0
  proof: rfl

@[simp]

中文:
定理 curryLeft_zero
  结论: curryLeft (0 : M [⋀^Fin n.succ]->ₗ[R] N) = 0
  证明: rfl

@[simp]
-/
theorem curryLeft_zero : curryLeft (0 : M [⋀^Fin n.succ]->ₗ[R] N) = 0 :=
  rfl

@[simp]
/--
theorem `curryLeft_add` / 定理 `curryLeft_add`

English:
theorem curryLeft_add
  given: (f g : M [⋀^Fin n.succ]->ₗ[R] N)
  proof: rfl

@[simp]

中文:
定理 curryLeft_add
  条件: (f g : M [⋀^Fin n.succ]->ₗ[R] N)
  证明: rfl

@[simp]
-/
theorem curryLeft_add (f g : M [⋀^Fin n.succ]->ₗ[R] N) :
    curryLeft (f + g) = curryLeft f + curryLeft g :=
  rfl

@[simp]
/--
theorem `curryLeft_smul` / 定理 `curryLeft_smul`

English:
theorem curryLeft_smul
  given: (r : R) (f : M [⋀^Fin n.succ]->ₗ[R] N)
  proof: rfl

中文:
定理 curryLeft_smul
  条件: (r : R) (f : M [⋀^Fin n.succ]->ₗ[R] N)
  证明: rfl
-/
theorem curryLeft_smul (r : R) (f : M [⋀^Fin n.succ]->ₗ[R] N) :
    curryLeft (r • f) = r • curryLeft f :=
  rfl

/-- `AlternatingMap.curryLeft` as a `LinearMap`. This is a separate definition as dot notation
does not work for this version. -/
@[simps]
/--
Definition of `curryLeftLinearMap` / `curryLeftLinearMap` 的定义

English:
definition curryLeftLinearMap
  signature: :
  body: f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul

中文:
定义 curryLeftLinearMap
  签名: :
  定义体: f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul

Depends on / 依赖: curryLeft, f.curryLeft
-/
def curryLeftLinearMap :
    (M [⋀^Fin n.succ]->ₗ[R] N) ->ₗ[R] M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N where
  toFun f := f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul

/-- Currying with the same element twice gives the zero map. -/
@[simp]
/--
theorem `curryLeft_same` / 定理 `curryLeft_same`

English:
theorem curryLeft_same
  given: (f : M [⋀^Fin n.succ.succ]->ₗ[R] N) (m : M)
  proof: ext fun _ => f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one

@[simp]

中文:
定理 curryLeft_same
  条件: (f : M [⋀^Fin n.succ.succ]->ₗ[R] N) (m : M)
  证明: ext fun _ => f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one

@[simp]

Depends on / 依赖: Fin.zero_ne_one, f.map_eq_zero_of_eq, map_eq_zero_of_eq, zero_ne_one
-/
theorem curryLeft_same (f : M [⋀^Fin n.succ.succ]->ₗ[R] N) (m : M) :
    (f.curryLeft m).curryLeft m = 0 :=
  ext fun _ => f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one

@[simp]
/--
theorem `curryLeft_compAlternatingMap` / 定理 `curryLeft_compAlternatingMap`

English:
theorem curryLeft_compAlternatingMap
  statement: (g : N ->ₗ[R] N₂)
  proof: rfl

@[simp]

中文:
定理 curryLeft_compAlternatingMap
  结论: (g : N ->ₗ[R] N₂)
  证明: rfl

@[simp]
-/
theorem curryLeft_compAlternatingMap (g : N ->ₗ[R] N₂)
    (f : M [⋀^Fin n.succ]->ₗ[R] N) (m : M) :
    (g.compAlternatingMap f).curryLeft m = g.compAlternatingMap (f.curryLeft m) :=
  rfl

@[simp]
/--
theorem `curryLeft_compLinearMap` / 定理 `curryLeft_compLinearMap`

English:
theorem curryLeft_compLinearMap
  given: (g : M₂ ->ₗ[R] M) (f : M [⋀^Fin n.succ]->ₗ[R] N) (m : M₂)
  proof: ext fun v => congr_arg f funext fun i => by cases i using Fin.cases <;> simp

中文:
定理 curryLeft_compLinearMap
  条件: (g : M₂ ->ₗ[R] M) (f : M [⋀^Fin n.succ]->ₗ[R] N) (m : M₂)
  证明: ext fun v => congr_arg f funext fun i => by cases i using Fin.cases <;> simp

Depends on / 依赖: Fin.cases, congr_arg
-/
theorem curryLeft_compLinearMap (g : M₂ ->ₗ[R] M) (f : M [⋀^Fin n.succ]->ₗ[R] N) (m : M₂) :
    (f.compLinearMap g).curryLeft m = (f.curryLeft (g m)).compLinearMap g :=
ext fun v => congr_arg f funext fun i => by cases i using Fin.cases <;> simp

end AlternatingMap
